namespace UglyToad.PdfPig.Writer
{
    using System;
    using System.Collections.Generic;
    using System.Diagnostics;
    using System.IO;
    using System.Linq;
    using Content;
    using Copier;
    using Copier.Page;
    using Core;
    using CrossReference;
    using Encryption;
    using Filters;
    using Logging;
    using Parser;
    using Parser.FileStructure;
    using Parser.Parts;
    using Tokenization.Scanner;
    using Tokens;
    using Exceptions;
    using Util;

    /// <summary>
    /// Merges PDF documents into each other.
    /// </summary>
    public static class PdfMerger
    {
        private static readonly ILog Log = new NoOpLog();

        private static readonly IFilterProvider FilterProvider = DefaultFilterProvider.Instance;

        /// <summary>
        /// Merge two PDF documents together with the pages from <paramref name="file1"/> followed by <paramref name="file2"/>.
        /// </summary>
        public static byte[] Merge(string file1, string file2, IReadOnlyList<int> file1Selection = null, IReadOnlyList<int> file2Selection = null)
        {
            if (file1 == null)
            {
                throw new ArgumentNullException(nameof(file1));
            }

            if (file2 == null)
            {
                throw new ArgumentNullException(nameof(file2));
            }

            return Merge(new[]
            {
                File.ReadAllBytes(file1),
                File.ReadAllBytes(file2)
            }, new [] { file1Selection, file2Selection });
        }

        /// <summary>
        /// Merge multiple PDF documents together with the pages in the order the file paths are provided.
        /// </summary>
        public static byte[] Merge(params string[] filePaths)
        {
            var bytes = new List<byte[]>(filePaths.Length);

            for (var i = 0; i < filePaths.Length; i++)
            {
                var filePath = filePaths[i];

                if (filePath == null)
                {
                    throw new ArgumentNullException(nameof(filePaths), $"Null filepath at index {i}.");
                }

                bytes.Add(File.ReadAllBytes(filePath));
            }

            return Merge(bytes, null);
        }

        /// <summary>
        /// Merge the set of PDF documents.
        /// </summary>
        public static byte[] Merge(IReadOnlyList<byte[]> files, IReadOnlyList<IReadOnlyList<int>> pagesBundle = null)
        {
            if (files == null)
            {
                throw new ArgumentNullException(nameof(files));
            }

            const bool isLenientParsing = false;

            var documentBuilder = new DocumentMerger();

            foreach (var fileIndex in Enumerable.Range(0, files.Count))
            {
                var file = files[fileIndex];

                IReadOnlyList<int> pages = null;
                if (pagesBundle != null && fileIndex < pagesBundle.Count)
                {
                    pages = pagesBundle[fileIndex];
                }

                var inputBytes = new ByteArrayInputBytes(file);
                var coreScanner = new CoreTokenScanner(inputBytes);

                var version = FileHeaderParser.Parse(coreScanner, isLenientParsing, Log);

                var crossReferenceParser = new CrossReferenceParser(Log, new XrefOffsetValidator(Log),
                    new Parser.Parts.CrossReference.CrossReferenceStreamParser(FilterProvider));

                CrossReferenceTable crossReference = null;

                // ReSharper disable once AccessToModifiedClosure
                var locationProvider = new ObjectLocationProvider(() => crossReference, inputBytes);

                var pdfScanner = new PdfTokenScanner(inputBytes, locationProvider, FilterProvider, NoOpEncryptionHandler.Instance);

                var crossReferenceOffset = FileTrailerParser.GetFirstCrossReferenceOffset(inputBytes, coreScanner, isLenientParsing);
                crossReference = crossReferenceParser.Parse(inputBytes, isLenientParsing, crossReferenceOffset, version.OffsetInFile, pdfScanner, coreScanner);

                var catalogDictionaryToken = ParseCatalog(crossReference, pdfScanner, out var encryptionDictionary);
                if (encryptionDictionary != null)
                {
                    throw new PdfDocumentEncryptedException("Unable to merge document with password");
                }

                var documentCatalog = CatalogFactory.Create(crossReference.Trailer.Root, catalogDictionaryToken, pdfScanner, isLenientParsing);

                documentBuilder.AppendDocument(documentCatalog, version.Version, pdfScanner, pages);
            }

            return documentBuilder.Build();
        }

        // This method is a basically a copy of the method UglyToad.PdfPig.Parser.PdfDocumentFactory.ParseTrailer()
        private static DictionaryToken ParseCatalog(CrossReferenceTable crossReferenceTable,
            IPdfTokenScanner pdfTokenScanner,
            out EncryptionDictionary encryptionDictionary)
        {
            encryptionDictionary = null;

            if (crossReferenceTable.Trailer.EncryptionToken != null)
            {
                if (!DirectObjectFinder.TryGet(crossReferenceTable.Trailer.EncryptionToken, pdfTokenScanner,
                    out DictionaryToken encryptionDictionaryToken))
                {
                    throw new PdfDocumentFormatException($"Unrecognized encryption token in trailer: {crossReferenceTable.Trailer.EncryptionToken}.");
                }

                encryptionDictionary = EncryptionDictionaryFactory.Read(encryptionDictionaryToken, pdfTokenScanner);
            }

            var rootDictionary = DirectObjectFinder.Get<DictionaryToken>(crossReferenceTable.Trailer.Root, pdfTokenScanner);

            if (!rootDictionary.ContainsKey(NameToken.Type))
            {
                rootDictionary = rootDictionary.With(NameToken.Type, NameToken.Catalog);
            }

            return rootDictionary;
        }

        private class DocumentMerger
        {
            private const decimal DefaultVersion = 1.2m;

            private const int ARTIFICIAL_NODE_LIMIT = 100;

            private readonly PdfStreamWriter context = new PdfStreamWriter();
            private readonly List<IndirectReferenceToken> pagesTokenReferences = new List<IndirectReferenceToken>();
            private readonly IndirectReferenceToken rootPagesReference;
            private readonly MultiCopier copier;

            private decimal currentVersion = DefaultVersion;
            private int pageCount = 0;

            public DocumentMerger()
            {
                context = new PdfStreamWriter();
                pagesTokenReferences = new List<IndirectReferenceToken>();

                rootPagesReference = context.ReserveNumberToken();

                copier = new MultiCopier(context);
                copier.AddCopier(new PagesCopier(copier, rootPagesReference));
            }

            public void AppendDocument(Catalog catalog, decimal version, IPdfTokenScanner tokenScanner, IReadOnlyList<int> pages)
            {
                IEnumerable<int> pageIndices;
                if (pages == null)
                {
                    var pagesCount = catalog.PagesDictionary.GetIntOrDefault(NameToken.Count);
                    if (pagesCount < 1)
                    {
                        return;
                    }

                    pageIndices = Enumerable.Range(1, pagesCount);
                }
                else if (pages.Count < 1)
                {
                    return;
                }
                else
                {
                    pageIndices = pages;
                }

                currentVersion = Math.Max(version, currentVersion);

                var currentNodeReference = context.ReserveNumberToken();
                var pagesReferences = new List<IndirectReferenceToken>();
                var resources = new Dictionary<string, IToken>();

                bool DoesAEntryCollide(PageTreeNode node)
                {
                    while (node != null)
                    {
                        var dictionary = node.NodeDictionary;
                        if (dictionary.TryGet(NameToken.Resources, tokenScanner, out DictionaryToken resourcesDictionary))
                        {
                            var nonCollidingResources = resourcesDictionary.Data.Keys.Except(resources.Keys);
                            if (nonCollidingResources.Count() != resourcesDictionary.Data.Count)
                            {
                                // This means that at least one of the resources collided
                                return true;
                            }
                        }

                        /* TODO: How to handle?
                         *  `Rotate`
                         *  `CropBox`
                         *  `MediaBox`
                         */

                        // No colliding entry was found, in this node
                        // Keep walking up into the tree
                        node = node.Parent;
                    }

                    return false;
                }


                void CopyEntries(PageTreeNode node)
                {
                    while (node != null)
                    {
                        var dictionary = node.NodeDictionary;
                        if (dictionary.TryGet(NameToken.Resources, tokenScanner, out DictionaryToken resourcesDictionary))
                        {
                            foreach (var pair in resourcesDictionary.Data)
                            {
                                resources.Add(pair.Key, copier.CopyObject(pair.Value, tokenScanner));
                            }
                        }

                        /* TODO: How to handle?
                         *  `Rotate`
                         *  `CropBox`
                         *  `MediaBox`
                         */

                        // Keep walking up into the tree
                        node = node.Parent;
                    }
                }

                void CreateTree()
                {
                    if (pagesReferences.Count < 1)
                    {
                        throw new InvalidOperationException("Pages reference should always be more than 1 when executing this function");
                    }

                    var newPagesNode = new Dictionary<NameToken, IToken>
                    {
                        { NameToken.Type, NameToken.Pages },
                        { NameToken.Kids, new ArrayToken(pagesReferences) },
                        { NameToken.Count, new NumericToken(pagesReferences.Count) },
                        { NameToken.Parent, rootPagesReference }
                    };

                    if (resources.Count > 0)
                    {
                        newPagesNode.Add(NameToken.Resources, DictionaryToken.With(resources));
                    }
                    
                    var pagesDictionary = new DictionaryToken(newPagesNode);
                    pagesTokenReferences.Add(context.WriteToken(pagesDictionary, (int)currentNodeReference.Data.ObjectNumber));

                    pageCount += pagesReferences.Count;
                };

                foreach (var pageIndex in pageIndices)
                {
                    var pageNode = catalog.GetPageNode(pageIndex);
                    if (pagesReferences.Count >= ARTIFICIAL_NODE_LIMIT || DoesAEntryCollide(pageNode))
                    {
                        CreateTree();

                        currentNodeReference = context.ReserveNumberToken();
                        pagesReferences = new List<IndirectReferenceToken>();
                        resources = new Dictionary<string, IToken>();
                    }

                    CopyEntries(pageNode.Parent);
                    pagesReferences.Add(CopyPageNode(pageNode, currentNodeReference, tokenScanner));
                }

                if (pagesReferences.Count < 1)
                {
                    throw new InvalidOperationException("Pages reference couldn't be less than 1 because we have reserved a indirect reference token");
                }

                CreateTree();

                copier.ClearReference();
            }

            public byte[] Build()
            {
                if (pagesTokenReferences.Count < 1)
                {
                    throw new PdfDocumentFormatException("Empty document");
                }

                var pagesDictionary = new DictionaryToken(new Dictionary<NameToken, IToken>
                {
                    { NameToken.Type, NameToken.Pages },
                    { NameToken.Kids, new ArrayToken(pagesTokenReferences) },
                    { NameToken.Count, new NumericToken(pageCount) }
                });

                var pagesRef = context.WriteToken(pagesDictionary, (int)rootPagesReference.Data.ObjectNumber);

                var catalog = new DictionaryToken(new Dictionary<NameToken, IToken>
                {
                    { NameToken.Type, NameToken.Catalog },
                    { NameToken.Pages, pagesRef }
                });

                var catalogRef = context.WriteToken(catalog);

                context.Flush(currentVersion, catalogRef);

                var bytes = context.ToArray();

                Close();

                return bytes;
            }

            private IndirectReferenceToken CopyPageNode(PageTreeNode pageNode, IndirectReferenceToken parentPagesObject, IPdfTokenScanner tokenScanner)
            {
                Debug.Assert(pageNode.IsPage);

                var pageDictionary = new Dictionary<NameToken, IToken>
                {
                    {NameToken.Parent, parentPagesObject},
                };

                foreach (var setPair in pageNode.NodeDictionary.Data)
                {
                    var name = setPair.Key;
                    var token = setPair.Value;

                    if (name == NameToken.Parent)
                    {
                        // Skip Parent token, since we have to reassign it
                        continue;
                    }

                    pageDictionary.Add(NameToken.Create(name), copier.CopyObject(token, tokenScanner));
                }

                return context.WriteToken(new DictionaryToken(pageDictionary));
            }

            private void Close()
            {
                context.Dispose();
            }

        }
    }
}
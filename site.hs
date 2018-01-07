--------------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}

import           Data.Monoid ((<>))
import qualified Data.Map.Strict as M
import           Data.String (fromString)

import           Control.Monad (filterM, (>=>))

import           Hakyll

--------------------------------------------------------------------------------
main :: IO ()
main = hakyll $ do
    match "bib/bib.bib" $ compile biblioCompiler
    -- Taken from https://github.com/citation-style-language/styles
    match "bib/elsevier-harvard.csl" $ compile cslCompiler

    match "images/*" $ do
        route   idRoute
        compile copyFileCompiler

    match "css/*" $ do
        route   idRoute
        compile compressCssCompiler

    match "posts/*" $ do
        route $ setExtension "html"
        compile $ pandocCompiler
            >>= loadAndApplyTemplate "templates/post.html"    postCtx
            >>= loadAndApplyTemplate "templates/default.html" postCtx
            >>= relativizeUrls

    match "example-sheets/*" $ do
        route $ setExtension "html"

        compile $ pandocBiblioCompiler "bib/elsevier-harvard.csl" "bib/bib.bib"
            >>= loadAndApplyTemplate "templates/post.html"    postCtx
            >>= loadAndApplyTemplate "templates/default.html" postCtx
            >>= relativizeUrls

    create ["archive.html"] $ do
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll "posts/*"
            let archiveCtx =
                  partialWith posts postCtx `mappend`
                  defaultContext

            makeItem ""
                >>= loadAndApplyTemplate "templates/archive.html" archiveCtx
                >>= loadAndApplyTemplate "templates/default.html" archiveCtx
                >>= relativizeUrls

    match "teaching.markdown" $ do
      route $ setExtension "html"
      compile $ do
        let indexCtx =
              constField "title" "Teaching" `mappend`
              defaultContext

        pandocCompiler
          >>= loadAndApplyTemplate "templates/default.html" indexCtx
          >>= relativizeUrls

    match "index.html" $ do
        route idRoute
        compile $ do
            let indexCtx =
                    constField "title" "Home"                `mappend`
                    defaultContext

            getResourceBody
                >>= applyAsTemplate indexCtx
                >>= loadAndApplyTemplate "templates/default.html" indexCtx
                >>= relativizeUrls

    match "templates/*" $ compile templateCompiler


--------------------------------------------------------------------------------
partialWith :: [ Item a ] -> Context a -> Context a
partialWith items itemCtx = functionField "partialWith" f
  where
  f [template, var, key, val] _ = fmap itemBody $ do
    filteredItems <- filterM (itemP key val) items
    let ctx = listField var itemCtx (return filteredItems)
           <> boolField (var ++ "NonNull") (const . not . null $ filteredItems)
           <> constField key val
    makeItem "" >>= loadAndApplyTemplate (fromString template) ctx

  itemP key val item = do
    mVal <- flip getMetadataField key . itemIdentifier $ item
    return $ mVal == Just val

postCtx :: Context String
postCtx =
    dateField "date" "%B %e, %Y" `mappend`
    defaultContext


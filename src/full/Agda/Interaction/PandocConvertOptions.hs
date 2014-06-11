module Agda.Interaction.PandocConvertOptions
    ( convertOptions
    ) where

import Agda.Interaction.Options
import qualified Agda.Interaction.PandocOptions as PO

import Data.Maybe

convertOptions :: PO.CommandLineOptions -> CommandLineOptions
convertOptions opts =
    Options { optProgramName          = PO.optProgramName opts
            , optInputFile            = PO.optInputFile opts
            , optIncludeDirs          = PO.optIncludeDirs opts
            , optShowVersion          = PO.optShowVersion opts
            , optShowHelp             = PO.optShowHelp opts
            , optInteractive          = PO.optInteractive opts        
            , optRunTests             = PO.optRunTests opts        
            , optGHCiInteraction      = PO.optGHCiInteraction opts        
            , optCompile              = PO.optCompile opts        
            , optCompileNoMain        = PO.optCompileNoMain opts
            , optEpicCompile          = PO.optEpicCompile opts        
            , optJSCompile            = PO.optJSCompile opts        
            , optCompileDir           = PO.optCompileDir opts        
            , optGenerateVimFile      = PO.optGenerateVimFile opts        
            , optGenerateLaTeX        = PO.optGenerateLaTeX opts        
            , optGenerateHTML         = isJust $ PO.optGenerateHTML opts
            , optDependencyGraph      = PO.optDependencyGraph opts        
            , optLaTeXDir             = PO.optLaTeXDir opts        
            , optHTMLDir              = PO.optHTMLDir opts        
            , optCSSFile              = PO.optCSSFile opts        
            , optIgnoreInterfaces     = PO.optIgnoreInterfaces opts        
            , optForcing              = PO.optForcing opts        
            , optGhcFlags             = PO.optGhcFlags opts
            , optPragmaOptions        = PO.optPragmaOptions opts
            , optEpicFlags            = PO.optEpicFlags opts
            , optSafe                 = PO.optSafe opts        
            }

    



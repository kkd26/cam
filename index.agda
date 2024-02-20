module index where

-- Simply Typed Lambda Calculus with DeBruijn indecies, types, context, terms
import CAM.term

-- Categotrical Cobinators
import CAM.catComb
import CAM.catComb.compile
import CAM.catComb.eval

-- CAM machine instructions
import CAM.inst

-- values - both combinator values and machine values
import CAM.value

-- machine configuration tuples
import CAM.config

-- machine step relation together with transitive closure
import CAM.step

-- various proofs of the machine
import CAM.proof.termination
import CAM.proof.logicalRelation
import CAM.proof.wellTyped

-- some examples of evaluation of the machine
import CAM.runNonTerminating
import CAM.example

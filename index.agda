module index where

-- Context
import CAM.context

-- Machine
import CAM.config
import CAM.machine.eval

-- Simply Typed Lambda Calculus with DeBruijn indecies, types, context, terms
import CAM.stlc.term
import CAM.stlc.type

-- Categotrical Cobinators
import CAM.stlc.catComb
import CAM.stlc.catComb.compile
import CAM.stlc.catComb.eval
import CAM.stlc.catComb.properities

-- CAM machine instructions
import CAM.stlc.inst

-- values - both combinator values and machine values
import CAM.stlc.value

-- step relation
import CAM.stlc.step

-- various proofs of the machine
import CAM.stlc.proof.termination
import CAM.stlc.proof.wellTyped

-- some examples of evaluation of the machine
import CAM.stlc.run
import CAM.stlc.example

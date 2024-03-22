module index where

-- Typing Context
import CAM.context

-- Machine
import CAM.config
import CAM.machine.eval

-- Simply Typed Lambda Calculus with DeBruijn indecies, types, terms
import CAM.stlc.term
import CAM.stlc.type

-- Typed Categotrical Cobinators
import CAM.stlc.catComb
import CAM.stlc.catComb.compile
import CAM.stlc.catComb.eval
import CAM.stlc.catComb.properities

-- CAM machine instructions
import CAM.stlc.inst

-- Values - both combinator values and machine values
import CAM.stlc.value

-- Step relation
import CAM.stlc.step

-- Various proofs of the machine
import CAM.stlc.proof.termination
import CAM.stlc.proof.wellTyped

-- Untyped Lambda Calculus
import CAM.untyped.type
import CAM.untyped.context
import CAM.untyped.term
import CAM.untyped.catComb
import CAM.untyped.inst
import CAM.untyped.value
import CAM.untyped.compile

-- List object and iteration
import CAM.list.type
import CAM.list.term
import CAM.list.catComb
import CAM.list.inst
import CAM.list.value
import CAM.list.compile
import CAM.list.eval

-- some examples of evaluation of the machine
import CAM.stlc.run
import CAM.stlc.example

import CAM.untyped.run
import CAM.untyped.example

import CAM.list.run
import CAM.list.example

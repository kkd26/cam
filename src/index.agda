module index where

-- Typing Context
import context

-- Machine
import config
import machine.eval

-- Simply Typed Lambda Calculus with DeBruijn indecies, types, terms
import stlc.term
import stlc.type

-- Typed Categotrical Cobinators
import stlc.catComb
import stlc.catComb.compile
import stlc.catComb.eval
import stlc.catComb.properities

-- CAM machine instructions
import stlc.inst

-- Values - both combinator values and machine values
import stlc.value

-- Step relation
import stlc.step

-- Various proofs of the machine
import stlc.proof.termination
import stlc.proof.wellTyped

-- Untyped Lambda Calculus
import untyped.type
import untyped.context
import untyped.term
import untyped.catComb
import untyped.inst
import untyped.value
import untyped.compile

-- List object and iteration
import list.type
import list.term
import list.catComb
import list.inst
import list.value
import list.compile
import list.eval

-- some examples of evaluation of the machine
import stlc.run
import stlc.example

import untyped.run
import untyped.example

import list.run
import list.example

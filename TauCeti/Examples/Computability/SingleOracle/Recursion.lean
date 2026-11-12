/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Computability.SingleOracle.Recursion
import TauCeti.Data.PFun.Basic

/-!
# Parameter compilation and genuine self-reference

These examples use only the public compiler API. A program prints its own index, a family
prints each specialized index alongside its parameter, and an oracle program queries its
own index. The latter works for partial oracles as well: an unanswered query remains undefined.
-/

open Encodable Denumerable TauCeti.Oracle.Single Code

-- Specializing an oracle query to the parameter leaves the ordinary input unused.
example (O : ℕ →. ℕ) (a x : ℕ) : eval O (curry (comp oracle left) a) x = O a := by
  simp

-- A program returning its own index, independently of both its input and its oracle.
example (O : ℕ →. ℕ) (x : ℕ) :
    eval O (fixedPoint left) x = Part.some (encode (fixedPoint left)) := by
  simp

-- Each member of this primitive recursive family returns the parameter and its own index.
example (O : ℕ →. ℕ) (a x : ℕ) :
    eval O (fixedPointParam (pair left (comp left right)) a) x =
      Part.some (Nat.pair a (encode (fixedPointParam (pair left (comp left right)) a))) := by
  simp [Seq.seq]

-- Self-reference can also affect an actual oracle query, rather than just a constant output.
example (O : ℕ →. ℕ) (x : ℕ) :
    eval O (fixedPoint (comp oracle left)) x = O (encode (fixedPoint (comp oracle left))) := by
  simp

-- The index map itself is effective, with no dependence on an oracle.
example : Primrec fun a => encode (fixedPointParam (pair left (comp left right)) a) :=
  Primrec.encode.comp (primrec₂_fixedPointParam.comp (Primrec.const _) Primrec.id)

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Alexander.Basic
public import TauCeti.KnotTheory.PDCode.Oriented.DisjointUnion

/-!
# Alexander coefficients of disjoint diagrams

Disjoint union retains the Alexander coefficients of each summand. These identities allow
local changes of an isolated diagram to be checked inside an arbitrary surrounding diagram.
-/

public section

namespace TauCeti.OrientedPDCode

open PDCode

variable {n m : ℕ} (D : OrientedPDCode n) (E : OrientedPDCode m)

/-- A crossing in the first summand retains its Alexander coefficients. -/
@[simp]
theorem alexanderWeight_disjointUnion_castAdd (i : Fin n) (s : Fin 4) :
    (D.disjointUnion E).alexanderWeight (Fin.castAdd m i) s = D.alexanderWeight i s := by
  simp [alexanderWeight_def, PDCode.isOver_def]

/-- A crossing in the second summand retains its Alexander coefficients. -/
@[simp]
theorem alexanderWeight_disjointUnion_natAdd (i : Fin m) (s : Fin 4) :
    (D.disjointUnion E).alexanderWeight (Fin.natAdd n i) s = E.alexanderWeight i s := by
  simp [alexanderWeight_def, PDCode.isOver_def]

end TauCeti.OrientedPDCode

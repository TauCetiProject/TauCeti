/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.MaximalProP

/-!
# The maximal pro-`p` quotient of an absolute Galois group

For a field `K`, `absoluteGaloisGroupProP p K` is the maximal pro-`p` quotient of
Mathlib's `Field.absoluteGaloisGroup K`. Its topology is the quotient topology. The
quotient is again profinite and is pro-`p`, so it is the group on which local
pro-`p` Galois cohomology and presentations are formulated.
-/

public section

namespace TauCeti

variable (p : ℕ) (K : Type*) [Field K]

/-- The maximal pro-`p` quotient of the absolute Galois group of `K`. -/
abbrev absoluteGaloisGroupProP : Type _ :=
  maximalProPQuotient p (Field.absoluteGaloisGroup K)

/-- The canonical continuous quotient map from an absolute Galois group to its maximal pro-`p`
quotient. -/
noncomputable abbrev absoluteGaloisGroupProPQuotientMap :
    Field.absoluteGaloisGroup K →ₜ* absoluteGaloisGroupProP p K :=
  ContinuousMonoidHom.quotientMk (proPKernel p (Field.absoluteGaloisGroup K))

/-- The maximal pro-`p` quotient of an absolute Galois group is pro-`p`. -/
theorem isProP_absoluteGaloisGroupProP : IsProP p (absoluteGaloisGroupProP p K) :=
  isProP_maximalProPQuotient

end TauCeti

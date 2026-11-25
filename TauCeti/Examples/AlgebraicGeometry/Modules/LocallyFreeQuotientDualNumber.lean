/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.LocallyFreeQuotient.Basic
public import TauCeti.AlgebraicGeometry.StructureSheaf.Stalk.BaseAlgebra
public import TauCeti.RingTheory.TrivSqZeroExt
public import TauCeti.RingTheory.Kaehler.DualNumber
public import Mathlib.Algebra.DualNumber

/-!
# Check: the dual numbers in characteristic other than `2`

For a field `k` in which `2 ≠ 0` and `X = Spec k[ε]/(ε²)`, the sheaf `Ω_{X/k}` admits no locally
free quotient of rank `1`, nor of any rank `d ≠ 0`. The Kähler differentials of `k[ε]/(ε²)` are
spanned by `dε`, and `2ε dε = d(ε²) = 0`, so `ε` kills them; a surjection onto `(k[ε]/(ε²))^d`
would then force `ε = 0`
(`TauCeti.DualNumber.not_surjective_kaehlerDifferential_to_pi_of_surjective`).
By the stalk criterion it suffices to see this at the stalk of the closed point, which is
`k[ε]/(ε²)` itself, the ring being local (`StructureSheaf.toStalkAlgHom_closedPoint_bijective`).

In characteristic `2`, by contrast, `a + bε ↦ b` is a derivation and the predicate holds; so the
predicate depends on the characteristic even for a zero-dimensional scheme.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

namespace TauCeti.LocallyFreeQuotientDualNumberExample

universe u

variable {k : Type u} [Field k]

variable (k) in
/-- The dual numbers `k[ε]/(ε²)`, as a commutative ring. -/
abbrev dualNumberRing : CommRingCat.{u} := .of (DualNumber k)

variable (k) in
/-- The closed point of `Spec k[ε]/(ε²)`, its only point. -/
abbrev closedPt : Spec (dualNumberRing k) := IsLocalRing.closedPoint (dualNumberRing k)

/-- **Check.** For a field `k` with `2 ≠ 0`, `Ω_{X/k}` for `X = Spec k[ε]/(ε²)` admits no locally
free quotient of any rank `d ≠ 0`; the Check is the case `d = 1`. -/
theorem not_hasLocallyFreeQuotientOfDifferentials (h2 : (2 : k) ≠ 0) {d : ℕ} (hd : d ≠ 0) :
    ¬ HasLocallyFreeQuotientOfDifferentials k (Spec (dualNumberRing k)) d := fun h ↦ by
  obtain ⟨g, hg⟩ := h.exists_surjective_stalk (closedPt k)
  -- Stated at `closedPt k`, typed as a point of `Spec`, so that the stalk's `k`-algebra
  -- instance `Scheme.stalkBaseAlgebra` is found.
  have hbij : Function.Bijective (StructureSheaf.toStalkAlgHom k _ (closedPt k)) :=
    StructureSheaf.toStalkAlgHom_closedPoint_bijective k _
  refine DualNumber.not_surjective_kaehlerDifferential_to_pi_of_surjective h2 _ hbij.2 ?_ hd g hg
  rw [Ne, ← map_zero (StructureSheaf.toStalkAlgHom k _ _), hbij.1.eq_iff]
  intro h
  simpa using congrArg TrivSqZeroExt.snd h

end TauCeti.LocallyFreeQuotientDualNumberExample

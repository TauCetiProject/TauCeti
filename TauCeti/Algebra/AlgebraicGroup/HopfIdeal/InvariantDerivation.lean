/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.InvariantDerivation
public import TauCeti.RingTheory.Derivation.TaylorExp

/-!
# Invariant derivations of closed subgroups

Let `I` be the defining Hopf ideal of a closed subgroup of an affine group. A tangent
vector at the identity belongs to that subgroup's Lie algebra precisely when its
left-invariant extension preserves `I`. In that case the induced derivation on the
quotient coordinate ring is the invariant extension of the subgroup tangent vector.

The forward implication uses naturality of invariant derivations under the quotient
bialgebra morphism. Conversely, the counit vanishes on `I`, so preservation by the
invariant extension forces its value at the identity to vanish on `I`.

This is the differential-ideal input to restricting polynomial exponential maps to
closed unipotent subgroups. The ideal-preservation results work over arbitrary commutative
base rings, without smoothness, reducedness, finite type, or a characteristic assumption.

Over a `ℚ`-algebra, if the invariant vector field `D` of a subgroup tangent vector is locally
nilpotent, its Taylor exponential `∑ Dⁿ / n!` therefore also preserves `I`. Polynomial subgroup
membership is proved in
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.OneParameter`.

## Main declarations

* `TauCeti.HopfIdeal.mem_lieSubalgebra_iff_leftInvariantDerivation_mem`: a tangent vector lies in
  the subgroup Lie algebra exactly when its invariant vector field preserves the defining ideal.
* `TauCeti.HopfIdeal.taylorExp_leftInvariantDerivation_mem`: the Taylor exponential of the
  invariant vector field of a subgroup tangent vector preserves the defining ideal.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapters 11 and 12.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 10.

The construction uses `TauCeti.Bialgebra.leftInvariantDerivation` and the closed-subgroup
differential `TauCeti.HopfIdeal.quotientLieHom`.
-/

public section

namespace TauCeti.HopfIdeal

open TauCeti.Bialgebra

variable {R H : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]

/-- For an ambient tangent vector in the subgroup Lie algebra, quotienting its invariant
derivation agrees with first descending the tangent vector. -/
@[simp]
theorem mk_leftInvariantDerivation (I : HopfIdeal R H)
    (d : I.lieSubalgebra (B := R)) (x : H) :
    Ideal.Quotient.mkₐ R I.toIdeal (leftInvariantDerivation d.val x) =
      leftInvariantDerivation (I.quotientLieEquiv.symm d)
        (Ideal.Quotient.mkₐ R I.toIdeal x) := by
  have h := (_root_.Bialgebra.Quotient.mkBialgHom I.toIdeal).map_leftInvariantDerivation
    (I.quotientLieEquiv.symm d) x
  rw [← quotientLieHom_apply, ← quotientLieEquiv_apply_coe, LieEquiv.apply_symm_apply] at h
  simpa only [_root_.Bialgebra.Quotient.mkBialgHom_apply,
    Ideal.Quotient.mkₐ_eq_mk] using h

/-- The left-invariant vector field of a subgroup tangent vector preserves the defining
Hopf ideal. -/
theorem leftInvariantDerivation_mem (I : HopfIdeal R H)
    {d : Derivation R H (CounitAlgebra R H R)} (hd : d ∈ I.lieSubalgebra (B := R))
    {x : H} (hx : x ∈ I.toIdeal) : leftInvariantDerivation d x ∈ I.toIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h := I.mk_leftInvariantDerivation ⟨d, hd⟩ x
  have hx0 : Ideal.Quotient.mkₐ R I.toIdeal x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
  rw [hx0, map_zero, Ideal.Quotient.mkₐ_eq_mk] at h
  exact h

/-- A tangent vector belongs to the Lie algebra of a closed subgroup exactly when its
left-invariant extension preserves the subgroup's defining Hopf ideal. -/
theorem mem_lieSubalgebra_iff_leftInvariantDerivation_mem (I : HopfIdeal R H)
    (d : Derivation R H (CounitAlgebra R H R)) :
    d ∈ I.lieSubalgebra (B := R) ↔
      ∀ x ∈ I.toIdeal, leftInvariantDerivation d x ∈ I.toIdeal := by
  constructor
  · exact fun hd _ hx => I.leftInvariantDerivation_mem hd hx
  · intro hd
    rw [mem_lieSubalgebra_iff]
    intro x hx
    apply (CounitAlgebra.algEquivSelf R H R).injective
    rw [← counit_leftInvariantDerivation, map_zero]
    exact I.counit_eq_zero (mem_toIdeal.mp (hd x hx))

section Exponential

variable [Algebra ℚ H]

/-- **The Taylor exponential preserves closed subgroups.** If a tangent vector lies in the Lie
algebra of a closed subgroup and its invariant vector field is locally nilpotent, the Taylor
exponential of that vector field maps the defining Hopf ideal into itself. -/
theorem taylorExp_leftInvariantDerivation_mem (I : HopfIdeal R H)
    {d : Derivation R H (CounitAlgebra R H R)} (hd : d ∈ I.lieSubalgebra (B := R))
    (hD : ∀ h, ∃ n, (leftInvariantDerivation d)^[n] h = 0) {x : H} (hx : x ∈ I.toIdeal) :
    (leftInvariantDerivation d).taylorExp hD x ∈ I.toIdeal :=
  (leftInvariantDerivation d).taylorExp_apply_mem hD
    (fun _ hy => I.leftInvariantDerivation_mem hd hy) hx

end Exponential

end TauCeti.HopfIdeal

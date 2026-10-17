/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# Lattice indices over discrete valuation rings

Over an infinite principal ideal domain, the index of a full-rank submodule of a finite free
module is the absolute ideal norm of the determinant of its inclusion. Over a discrete valuation
ring with residue cardinality `q`, a matrix whose determinant is associated to the `k`-th power
of a uniformizer therefore has image of index `q ^ k`. No completeness assumption is needed.
This is the algebraic index calculation underlying Haar-measure scaling for image lattices.

The determinant comparison follows Mathlib's `Submodule.natAbs_det_equiv`, replacing the integer
absolute value by `Ideal.absNorm`. The quotient decomposition is Mathlib's
`Submodule.quotientEquivPiSpan`; multiplicativity and the prime-power calculation are supplied by
`Ideal.absNorm` and `cardQuot_pow_of_prime`.

## Main results

* `Submodule.absNorm_span_det_equiv`: the determinant-index comparison over an infinite PID.
* `LinearMap.cardQuot_range_eq_absNorm_span_det`: its form for an injective endomorphism.
* `Matrix.cardQuot_range_eq_pow_of_associated_det`: the image-lattice index over a DVR.
* `Matrix.finite_quotient_range_of_associated_det`: finiteness when the residue field is finite.

## References

* J.-P. Serre, *Local Fields*, Chapter I, §§2 and 5.
-/

public section

open Module

namespace TauCeti

section PrincipalIdealDomain

variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Infinite R]
  [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

/-- The norm of the determinant ideal of a lattice inclusion is its index. -/
theorem _root_.Submodule.absNorm_span_det_equiv (N : Submodule R M) (e : M ≃ₗ[R] N) :
    Ideal.absNorm (Ideal.span {LinearMap.det (N.subtype.comp e.toLinearMap)}) =
      Nat.card (M ⧸ N) := by
  classical
  let b := Module.Free.chooseBasis R M
  have h : Module.finrank R N = Module.finrank R M := e.symm.finrank_eq
  let a := N.smithNormalFormCoeffs b h
  let b' := N.smithNormalFormTopBasis b h
  let ab := N.smithNormalFormBotBasis b h
  let e' : M ≃ₗ[R] N := b'.equiv ab (Equiv.refl _)
  let f : M →ₗ[R] M := N.subtype.comp e'.toLinearMap
  have ha (i) : f (b' i) = a i • b' i := by
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, e', Basis.equiv_apply,
      Equiv.refl_apply, Submodule.subtype_apply]
    exact N.smithNormalFormBotBasis_def b h i
  have hmatrix : LinearMap.toMatrix b' b' f = Matrix.diagonal a :=
    (b'.toMatrix_eq_diagonal_iff b' f a).2 ha
  have hdet : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', hmatrix, Matrix.det_diagonal]
  rw [Ideal.span_singleton_eq_span_singleton.mpr
    (LinearMap.associated_det_comp_equiv N.subtype e e'), hdet,
    ← Ideal.prod_span_singleton, map_prod]
  simp_rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact ((Nat.card_congr (N.quotientEquivPiSpan b h).toEquiv).trans Nat.card_pi).symm

/-- An injective endomorphism of a finite free module over an infinite PID has image index equal
to the norm of its determinant ideal. -/
theorem _root_.LinearMap.cardQuot_range_eq_absNorm_span_det (f : M →ₗ[R] M)
    (hf : Function.Injective f) :
    (LinearMap.range f).cardQuot = Ideal.absNorm (Ideal.span {LinearMap.det f}) := by
  have he : (LinearMap.range f).subtype.comp (LinearEquiv.ofInjective f hf).toLinearMap = f := by
    ext x
    simp
  rw [Submodule.cardQuot_apply,
    ← Submodule.absNorm_span_det_equiv (LinearMap.range f) (LinearEquiv.ofInjective f hf), he]

end PrincipalIdealDomain

section DiscreteValuationRing

variable {R ι : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Fintype ι] [DecidableEq ι]

/-- A matrix over a DVR whose determinant is associated to `π ^ k` has image index equal to the
`k`-th power of the residue cardinality. This equality also allows an infinite residue field,
with `Nat.card` taking its usual junk value `0`. -/
theorem _root_.Matrix.cardQuot_range_eq_pow_of_associated_det (A : Matrix ι ι R)
    {π : R} (hπ : Irreducible π) {k : ℕ} (hdet : Associated A.det (π ^ k)) :
    (LinearMap.range A.toLin').cardQuot = Nat.card (IsLocalRing.ResidueField R) ^ k := by
  have : Infinite R := by
    by_contra h
    have : Finite R := not_infinite_iff_finite.mp h
    exact IsDiscreteValuationRing.not_isField R (Finite.isField_of_domain R)
  have hA : Function.Injective A.toLin' :=
    Matrix.mulVec_injective_of_det_ne_zero (hdet.ne_zero_iff.mpr (pow_ne_zero _ hπ.ne_zero))
  rw [LinearMap.cardQuot_range_eq_absNorm_span_det A.toLin' hA,
    LinearMap.det_toLin', Ideal.span_singleton_eq_span_singleton.mpr hdet,
    ← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq, map_pow, Ideal.absNorm_apply,
    Submodule.cardQuot_apply]
  rfl

/-- Such an image lattice has finite index when the residue field is finite. -/
theorem _root_.Matrix.finite_quotient_range_of_associated_det (A : Matrix ι ι R)
    [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π) {k : ℕ}
    (hdet : Associated A.det (π ^ k)) : Finite ((ι → R) ⧸ LinearMap.range A.toLin') := by
  apply Nat.finite_of_card_ne_zero
  rw [← Submodule.cardQuot_apply, A.cardQuot_range_eq_pow_of_associated_det hπ hdet]
  exact pow_ne_zero _ Nat.card_pos.ne'

end DiscreteValuationRing

end TauCeti

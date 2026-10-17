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

Over a principal ideal domain, the index of a full-rank submodule of a finite free module
is the cardinality of the quotient by the determinant ideal of its inclusion. Over a discrete
valuation ring with residue cardinality `q`, a matrix whose determinant is associated to the
`k`-th power of a uniformizer therefore has image of index `q ^ k`. No completeness is needed.
This is the algebraic index calculation underlying Haar-measure scaling for image lattices.

The determinant comparison follows Mathlib's `Submodule.natAbs_det_equiv`, replacing the integer
absolute value by `Ideal.absNorm`. The quotient decomposition is Mathlib's
`Submodule.quotientEquivPiSpan`; multiplicativity over infinite PIDs is supplied by
`Ideal.absNorm`, and the DVR prime-power calculation uses `cardQuot_pow_of_prime`.

## Main results

* `TauCeti.Submodule.natCard_quotient_eq_natCard_quotient_span_det_equiv`: the PID comparison.
* `TauCeti.LinearMap.natCard_quotient_range_eq_natCard_quotient_span_det`: the endomorphism form.
* `TauCeti.Matrix.natCard_quotient_range_toLin'_of_det_ne_zero`: the matrix form over a PID.
* `TauCeti.Matrix.natCard_quotient_range_eq_pow_of_associated_det`: the DVR image-lattice index.
* `TauCeti.Matrix.finite_quotient_range_of_associated_det`: finiteness over a finite residue field.

## References

* J.-P. Serre, *Local Fields*, Chapter I, §§2 and 5.
-/

public section

open Module

namespace TauCeti

section PrincipalIdealDomain

variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

/-- The index of a lattice inclusion over a PID is the cardinality of the quotient by its
determinant ideal. -/
theorem Submodule.natCard_quotient_eq_natCard_quotient_span_det_equiv (N : Submodule R M)
    (e : M ≃ₗ[R] N) :
    Nat.card (M ⧸ N) =
      Nat.card (R ⧸ Ideal.span {LinearMap.det (N.subtype.comp e.toLinearMap)}) := by
  classical
  cases finite_or_infinite R with
  | inl hR =>
    let := (Finite.isField_of_domain R).toField
    have hN : N = ⊤ := _root_.Submodule.eq_top_of_finrank_eq e.symm.finrank_eq
    have hf : Function.Bijective (N.subtype.comp e.toLinearMap) := by
      refine ⟨N.subtype_injective.comp e.injective, ?_⟩
      intro x
      have hx : x ∈ N := by simp [hN]
      obtain ⟨y, hy⟩ := e.surjective ⟨x, hx⟩
      exact ⟨y, congrArg Subtype.val hy⟩
    have hu : IsUnit (LinearMap.det (N.subtype.comp e.toLinearMap)) := by
      convert (LinearEquiv.ofBijective (N.subtype.comp e.toLinearMap) hf).isUnit_det' using 1
      congr 1
    rw [Ideal.span_singleton_eq_top.mpr hu, hN]
    simp
  | inr hR =>
    change Nat.card (M ⧸ N) = Ideal.absNorm (Ideal.span {_})
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
    exact (Nat.card_congr (N.quotientEquivPiSpan b h).toEquiv).trans Nat.card_pi

/-- An injective endomorphism of a finite free module over a PID has image index equal to
the cardinality of the quotient by its determinant ideal. -/
theorem LinearMap.natCard_quotient_range_eq_natCard_quotient_span_det (f : M →ₗ[R] M)
    (hf : Function.Injective f) :
    Nat.card (M ⧸ LinearMap.range f) = Nat.card (R ⧸ Ideal.span {LinearMap.det f}) := by
  have he : (LinearMap.range f).subtype.comp (LinearEquiv.ofInjective f hf).toLinearMap = f := by
    ext x
    simp
  rw [Submodule.natCard_quotient_eq_natCard_quotient_span_det_equiv (LinearMap.range f)
    (LinearEquiv.ofInjective f hf), he]

/-- A square matrix over a PID with nonzero determinant has cokernel cardinality equal to
that of the quotient by its determinant ideal. -/
theorem Matrix.natCard_quotient_range_toLin'_of_det_ne_zero {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R) (hA : A.det ≠ 0) :
    Nat.card ((ι → R) ⧸ LinearMap.range A.toLin') = Nat.card (R ⧸ Ideal.span {A.det}) := by
  rw [LinearMap.natCard_quotient_range_eq_natCard_quotient_span_det A.toLin'
    (Matrix.mulVec_injective_of_det_ne_zero hA), LinearMap.det_toLin']

end PrincipalIdealDomain

section DiscreteValuationRing

variable {R ι : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Fintype ι] [DecidableEq ι]

/-- A matrix over a DVR whose determinant is associated to `π ^ k` has image index equal to the
`k`-th power of the residue cardinality. This equality also allows an infinite residue field,
with `Nat.card` taking its usual junk value `0`. -/
theorem Matrix.natCard_quotient_range_eq_pow_of_associated_det (A : Matrix ι ι R)
    {π : R} (hπ : Irreducible π) {k : ℕ} (hdet : Associated A.det (π ^ k)) :
    Nat.card ((ι → R) ⧸ LinearMap.range A.toLin') =
      Nat.card (IsLocalRing.ResidueField R) ^ k := by
  rw [Matrix.natCard_quotient_range_toLin'_of_det_ne_zero A
    (hdet.ne_zero_iff.mpr (pow_ne_zero _ hπ.ne_zero)),
    Ideal.span_singleton_eq_span_singleton.mpr hdet,
    ← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq,
    ← _root_.Submodule.cardQuot_apply, cardQuot_pow_of_prime
      (by simpa [hπ.maximalIdeal_eq] using hπ.ne_zero), _root_.Submodule.cardQuot_apply]
  -- The residue field is defined as the quotient by the maximal ideal.
  rfl

/-- A square matrix over a DVR with determinant associated to a power of a uniformizer
has finite cokernel when the residue field is finite. -/
theorem Matrix.finite_quotient_range_of_associated_det (A : Matrix ι ι R)
    [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π) {k : ℕ}
    (hdet : Associated A.det (π ^ k)) : Finite ((ι → R) ⧸ LinearMap.range A.toLin') := by
  apply Nat.finite_of_card_ne_zero
  rw [Matrix.natCard_quotient_range_eq_pow_of_associated_det A hπ hdet]
  exact pow_ne_zero _ Nat.card_pos.ne'

end DiscreteValuationRing

end TauCeti

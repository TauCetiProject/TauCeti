/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.SupSeminorm
public import TauCeti.Analysis.Normed.Unbundled.Slope
public import Mathlib.FieldTheory.SplittingField.Construction

/-!
# Numerical slopes over affinoid algebras

For an affinoid algebra `A` over a complete nonarchimedean field `K`, the slope condition
`Polynomial.IsSlopeLE K r Q` can be tested at the classical points: for each maximal ideal `x` of
`A`, whose residue field is finite over `K`, at the roots of `Q mod x` in a splitting field of
`Q mod x` over `A ⧸ x`, which is again finite over `K`. In particular it suffices to test finite
extensions of `K`, and the bound then holds for algebraic extensions in every universe. A root at
an arbitrary algebraic point is conjugate over `K` to one of these roots, and conjugate elements
have the same spectral norm.

## Main results

* `TauCeti.IsAffinoidAlgebra.isSlopeLE_iff_splittingField`: over an affinoid algebra the slope
  condition is tested at the roots of `Q mod x` in a splitting field, for maximal ideals `x`.
* `TauCeti.IsAffinoidAlgebra.isSlopeLE_iff_finiteDimensional`: over an affinoid algebra the slope
  condition is tested in finite extensions of `K`.
* `TauCeti.IsAffinoidAlgebra.le_spectralNorm_of_isSlopeLE`: over an affinoid algebra the slope
  condition applies to algebraic extensions of `K` in every universe.

## References

* E. Urban, *Eigenvarieties for reductive groups*, Ann. of Math. 174 (2011), 1685–1784, §2.3.
-/

public section

open Polynomial

universe v

namespace TauCeti.IsAffinoidAlgebra

section NontriviallyNormedField

variable {K : Type*} [NontriviallyNormedField K] {A : Type v} [CommRing A] [Algebra K A]
  [IsUltrametricDist K] [CompleteSpace K] {r : ℝ} {Q : A[X]}

/-- If `Q` passes the slope test in finite extensions of `K`, then at every maximal ideal `x`, the
reduction `Q mod x` is nonzero and its roots in a splitting field have spectral norm at least
`r`. Both the residue field and the splitting field are finite over `K`. -/
private theorem forall_splittingField_of_finiteDimensional (hA : IsAffinoidAlgebra K A)
    (h : ∀ (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L] (χ : A →ₐ[K] L)
      (α : L), (Q.map (χ : A →+* L)).IsRoot α → r ≤ spectralNorm K L α) (hr : 0 < r)
    (x : MaximalSpectrum A) :
    letI := Ideal.Quotient.field x.asIdeal
    Q.map (Ideal.Quotient.mk x.asIdeal) ≠ 0 ∧
      ∀ β ∈ (Q.map (Ideal.Quotient.mk x.asIdeal)).rootSet
        (Q.map (Ideal.Quotient.mk x.asIdeal)).SplittingField,
        r ≤ spectralNorm K _ β := by
  let := Ideal.Quotient.field x.asIdeal
  have := hA.finite_quotient_of_isMaximal x.asIdeal
  refine ⟨fun h0 ↦ ?_, fun β hβ ↦ ?_⟩
  · -- If `Q mod x` vanished, then `0` would be a root of `Q` at the residue field of `x`.
    have := h (A ⧸ x.asIdeal) (Ideal.Quotient.mkₐ K x.asIdeal) 0
      (by simpa [IsRoot] using congrArg (eval 0) h0)
    rw [spectralNorm_zero] at this
    exact hr.not_ge this
  · let F := A ⧸ x.asIdeal
    let S := (Q.map (Ideal.Quotient.mk x.asIdeal)).SplittingField
    have : FiniteDimensional K S := Module.Finite.trans F S
    refine h S ((IsScalarTower.toAlgHom K F S).comp (Ideal.Quotient.mkₐ K x.asIdeal)) β ?_
    have hmk : (Ideal.Quotient.mkₐ K x.asIdeal : A →+* F) = Ideal.Quotient.mk x.asIdeal :=
      Ideal.Quotient.mkₐ_toRingHom K x.asIdeal
    simpa [IsRoot, aeval_def, eval_map, eval₂_map, AlgHom.comp_toRingHom, hmk] using
      (mem_rootSet.1 hβ).2

/-- **Slope test at residue fields.** Over an affinoid algebra, `Q` has slope at most `r` if and
only if `r > 0` and, at every maximal ideal `x`, the reduction `Q mod x` is nonzero and each of
its roots in a splitting field over the finite residue field `A ⧸ x` has spectral norm at least
`r`. -/
theorem isSlopeLE_iff_splittingField (hA : IsAffinoidAlgebra K A) :
    Q.IsSlopeLE K r ↔ 0 < r ∧ ∀ x : MaximalSpectrum A,
      letI := Ideal.Quotient.field x.asIdeal
      Q.map (Ideal.Quotient.mk x.asIdeal) ≠ 0 ∧
        ∀ β ∈ (Q.map (Ideal.Quotient.mk x.asIdeal)).rootSet
          (Q.map (Ideal.Quotient.mk x.asIdeal)).SplittingField,
          r ≤ spectralNorm K _ β :=
  ⟨fun hQ ↦ ⟨hQ.pos, hA.forall_splittingField_of_finiteDimensional
    (fun _ _ _ _ χ _ hα ↦ hQ.le_spectralNorm χ hα) hQ.pos⟩,
    fun h ↦ isSlopeLE_iff.2
      ⟨h.1, fun _ _ _ _ χ _ hα ↦ le_spectralNorm_of_forall_splittingField h.2 χ hα⟩⟩

/-- **Slope test in finite extensions.** Over an affinoid algebra, `Q` has slope at most `r` if
and only if `r > 0` and every root of `χ(Q)` has spectral norm at least `r`, for every `K`-algebra
map `χ` from `A` to a finite extension of `K`. -/
theorem isSlopeLE_iff_finiteDimensional (hA : IsAffinoidAlgebra K A) :
    Q.IsSlopeLE K r ↔ 0 < r ∧ ∀ (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]
      (χ : A →ₐ[K] L) (α : L), (Q.map (χ : A →+* L)).IsRoot α → r ≤ spectralNorm K L α :=
  ⟨fun hQ ↦ ⟨hQ.pos, fun _ _ _ _ χ _ hα ↦ hQ.le_spectralNorm χ hα⟩,
    fun h ↦ isSlopeLE_iff.2 ⟨h.1, fun _ _ _ _ χ _ hα ↦ le_spectralNorm_of_forall_splittingField
      (hA.forall_splittingField_of_finiteDimensional h.2 h.1) χ hα⟩⟩

/-- Over an affinoid algebra, the slope condition bounds the roots of `χ(Q)` below by `r` for
algebraic extensions `L` of `K` in every universe, not only in the universe of `A` used in the
definition of `Polynomial.IsSlopeLE`. -/
theorem le_spectralNorm_of_isSlopeLE (hA : IsAffinoidAlgebra K A) (hQ : Q.IsSlopeLE K r)
    {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] (χ : A →ₐ[K] L) {α : L}
    (hα : (Q.map (χ : A →+* L)).IsRoot α) : r ≤ spectralNorm K L α :=
  le_spectralNorm_of_forall_splittingField ((hA.isSlopeLE_iff_splittingField).1 hQ).2 χ hα

end NontriviallyNormedField

section NormedField

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A] {r : ℝ}

/-- Over a nonzero affinoid algebra, `X - c` has slope at most `r` exactly when `0 < r ≤ |c|`. In
particular `X - c` with `0 < |c| < 1` fails the test at `r = 1`. -/
theorem isSlopeLE_X_sub_C_algebraMap_iff [Nontrivial A] (hA : IsAffinoidAlgebra K A) {c : K} :
    (X - C (algebraMap K A c)).IsSlopeLE K r ↔ 0 < r ∧ r ≤ ‖c‖ := by
  refine ⟨fun h ↦ ⟨h.pos, ?_⟩, fun h ↦ isSlopeLE_X_sub_C_algebraMap h.1 h.2⟩
  obtain ⟨x, hx⟩ := Ideal.exists_maximal A
  let := Ideal.Quotient.field x
  have := hA.finite_quotient_of_isMaximal x
  have := h.le_spectralNorm (L := A ⧸ x) (Ideal.Quotient.mkₐ K x)
    (α := algebraMap K (A ⧸ x) c) (by simp)
  rwa [spectralNorm_extends] at this

end NormedField

end TauCeti.IsAffinoidAlgebra

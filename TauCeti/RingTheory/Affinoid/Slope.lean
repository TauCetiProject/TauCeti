/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.SupSeminorm
public import TauCeti.Analysis.Normed.Unbundled.Slope
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.RingTheory.AdjoinRoot

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
  {r : ℝ} {Q : A[X]}

/-- If, at every maximal ideal `x`, the reduction `Q mod x` is nonzero and its roots in a
splitting field over `A ⧸ x` have spectral norm at least `r`, then so does every root `α` of
`χ(Q)` in an algebraic extension `L` of `K`, in any universe. Indeed `α` lies over the maximal
ideal `ker χ`, and its minimal polynomial over `A ⧸ ker χ` has a root `β` in the splitting field;
`α` and `β` are then conjugate over `K`. -/
private theorem le_spectralNorm_of_forall_splittingField
    (h : ∀ x : MaximalSpectrum A,
      letI := Ideal.Quotient.field x.asIdeal
      Q.map (Ideal.Quotient.mk x.asIdeal) ≠ 0 ∧
        ∀ β ∈ (Q.map (Ideal.Quotient.mk x.asIdeal)).rootSet
          (Q.map (Ideal.Quotient.mk x.asIdeal)).SplittingField,
          r ≤ spectralNorm K _ β)
    {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] (χ : A →ₐ[K] L) {α : L}
    (hα : (Q.map (χ : A →+* L)).IsRoot α) : r ≤ spectralNorm K L α := by
  -- `L` is integral over `A` along `χ`, so the kernel of `χ` is maximal.
  let : Algebra A L := (χ : A →+* L).toAlgebra
  have : IsScalarTower K A L := .of_algebraMap_eq fun c ↦ (χ.commutes c).symm
  have : Algebra.IsIntegral A L := .tower_top K
  set I := RingHom.ker χ
  have hI : I.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (χ : A →+* L)
    (fun y ↦ Algebra.IsIntegral.isIntegral (R := A) y) ⊥
  let := Ideal.Quotient.field I
  let F := A ⧸ I
  let Q' : F[X] := Q.map (Ideal.Quotient.mk I)
  obtain ⟨hQ', hroots⟩ := h ⟨I, hI⟩
  -- Make `L` an algebra over the residue field `F` through the injection `F → L` induced by `χ`.
  let : Algebra F L := (Ideal.kerLiftAlg χ : F →+* L).toAlgebra
  have : IsScalarTower K F L :=
    .of_algebraMap_eq fun c ↦ ((Ideal.kerLiftAlg χ).commutes c).symm
  have hmk : (algebraMap F L).comp (Ideal.Quotient.mk I) = (χ : A →+* L) :=
    RingHom.ext (Ideal.kerLiftAlg_mk χ)
  have hint : IsIntegral F α := (Algebra.IsIntegral.isIntegral (R := K) α).tower_top
  have hQα : aeval α Q' = 0 := by
    rwa [aeval_def, eval₂_map, hmk, ← eval_map]
  -- The minimal polynomial of `α` over `F` divides `Q mod x`, so it has a root in the splitting
  -- field of `Q mod x`.
  let S := Q'.SplittingField
  let q := minpoly F α
  have hdvd : q ∣ Q' := minpoly.dvd F α hQα
  obtain ⟨β, hβ⟩ := (SplittingField.splits Q').of_dvd (Polynomial.map_ne_zero hQ')
    (Polynomial.map_dvd _ hdvd) |>.exists_eval_eq_zero
      (by rw [degree_map]; exact (minpoly.degree_pos hint).ne')
  rw [eval_map_algebraMap] at hβ
  have hβQ : β ∈ Q'.rootSet S :=
    (mem_rootSet' (S := S)).2
      ⟨Polynomial.map_ne_zero hQ', aeval_eq_zero_of_dvd_aeval_eq_zero hdvd hβ⟩
  -- `α` and `β` are both images of the root of `q` under `K`-algebra maps of fields.
  have : Fact (Irreducible q) := ⟨minpoly.irreducible hint⟩
  let ψL : AdjoinRoot q →ₐ[K] L :=
    AdjoinRoot.liftAlgHom q (IsScalarTower.toAlgHom K F L) α (minpoly.aeval F α)
  let ψS : AdjoinRoot q →ₐ[K] S := AdjoinRoot.liftAlgHom q (IsScalarTower.toAlgHom K F S) β hβ
  calc r ≤ spectralNorm K S β := hroots β hβQ
    _ = spectralNorm K S (ψS (AdjoinRoot.root q)) :=
      congrArg _ (AdjoinRoot.liftAlgHom_root q _ β hβ).symm
    _ = spectralNorm K L (ψL (AdjoinRoot.root q)) := by
      rw [ψS.spectralNorm_map, ψL.spectralNorm_map]
    _ = spectralNorm K L α := congrArg _ (AdjoinRoot.liftAlgHom_root q _ α _)

variable [IsUltrametricDist K] [CompleteSpace K]

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
    rw [mem_rootSet] at hβ
    rw [IsRoot, ← hβ.2, aeval_def, eval₂_map, ← eval_map, AlgHom.comp_toRingHom,
      IsScalarTower.coe_toAlgHom, ← AlgHom.toRingHom_eq_coe, Ideal.Quotient.mkₐ_toRingHom]

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

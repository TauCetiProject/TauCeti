/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.Length
public import TauCeti.RingTheory.FittingIdeal.Basic
import TauCeti.Algebra.Group.Action.Pow
import TauCeti.RingTheory.FittingIdeal.Span
import TauCeti.RingTheory.Length

/-!
# Minors ideals and lengths over a discrete valuation ring

Let `O` be a discrete valuation ring with valuation `v` and uniformizer `ϖ`, and `R` an
`O`-algebra. This file compares the minors ideals (`Submodule.minorsIdeal`) of `R`-submodules with
`O`-lengths.

* Adjoining to an `R`-submodule `N ⊆ F` the `R`-span of an `O`-submodule `P` whose image in
  `F ⧸ N` has length at most `n` costs at most `ϖ ^ n`: `ϖ ^ n` multiplies the minors of
  `N ⊔ span R P` into those of `N`. Indeed, a nonzero image of finite length contains a nonzero
  element killed by `ϖ`, and adjoining it costs the colon ideal of `N` at it
  (`Submodule.colon_mul_minorsIdeal_sup_span_singleton_le`), which contains `ϖ`.
* For an `O`-algebra map `π : R → O` and an `R`-submodule `N ⊆ R^ι`, some maximal minor `F` of
  `N` has `v(π F)` equal to the colength of the image `π(N) ⊆ O^ι`: the image is spanned by the rows
  of a square matrix whose determinant has that valuation
  (`Matrix.length_quotient_span_range_eq_addVal_det`), and the rows lift to `N`.

## Main results

* `Submodule.pow_mul_mem_minorsIdeal_of_length_map_mkQ_le`: if the image of `P` in `F ⧸ N` has
  length at most `n`, then `ϖ ^ n` multiplies the minors of `N ⊔ span R P` into those of `N`.
* `Submodule.exists_mem_minorsIdeal_addVal_eq_length`: some maximal minor `F` of `N ⊆ R^ι` has
  `v(π F)` equal to the colength of `π(N)`.

## References

* [Stacks Project, Tag 07Z6](https://stacks.math.columbia.edu/tag/07Z6), for Fitting ideals.
-/

public section

open IsDiscreteValuationRing Module

namespace Submodule

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- In a torsion module over a discrete valuation ring, every element is killed by a power of a
uniformizer. -/
private theorem exists_pow_smul_eq_zero {Y : Type*} [AddCommGroup Y] [Module O Y] {ϖ : O}
    (hϖ : Irreducible ϖ) (hY : Module.IsTorsion O Y) (y : Y) : ∃ k : ℕ, ϖ ^ k • y = 0 := by
  obtain ⟨r, hr⟩ := @hY y
  obtain ⟨m, u, hu⟩ := eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero r.property) hϖ
  refine ⟨m, ?_⟩
  have h : (u : O) • ϖ ^ m • y = 0 := by
    rw [smul_smul, ← hu]
    exact hr
  simpa [smul_smul] using congr_arg ((↑u⁻¹ : O) • ·) h

variable {R F : Type*} [CommRing R] [Algebra O R] [AddCommGroup F] [Module R F] [Module O F]
  [IsScalarTower O R F]

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- Adjoining to `N` an element `u` of `P` outside `N` lowers by one the length of the image
of `P`. -/
private theorem length_map_mkQ_sup_span_singleton_le {N : Submodule R F} {P : Submodule O F}
    {n : ℕ} (hP : length O (P.map (N.restrictScalars O).mkQ) ≤ n + 1) {u : F} (huP : u ∈ P)
    (huN : u ∉ N) :
    length O (P.map ((N ⊔ R ∙ u).restrictScalars O).mkQ) ≤ n := by
  rw [TauCeti.length_map_mkQ] at hP ⊢
  have hle : (N.restrictScalars O).comap P.subtype ≤ ((N ⊔ R ∙ u).restrictScalars O).comap
      P.subtype := fun x hx ↦ by
    simp only [mem_comap, subtype_apply, restrictScalars_mem] at hx ⊢
    exact mem_sup_left hx
  rw [TauCeti.length_quotient_eq_length_quotient_comap_subtype_add hle] at hP
  -- The class of `u` is a nonzero element of the first factor.
  have hpos : 1 ≤ length O (↥(((N ⊔ R ∙ u).restrictScalars O).comap P.subtype) ⧸
      ((N.restrictScalars O).comap P.subtype).comap
        (((N ⊔ R ∙ u).restrictScalars O).comap P.subtype).subtype) := by
    rw [Order.one_le_iff_ne_zero, ← pos_iff_ne_zero, length_pos_iff]
    refine nontrivial_of_ne (Quotient.mk ⟨⟨u, huP⟩, ?_⟩) 0 ?_
    · exact (restrictScalars_mem O _ _).2 (mem_sup_right (mem_span_singleton_self u))
    · rw [ne_eq, Quotient.mk_eq_zero]
      simpa using huN
  have h := (add_le_add_left hpos _).trans hP
  rw [add_comm (n : ℕ∞)] at h
  exact (WithTop.add_le_add_iff_left ENat.one_ne_top).1 h

/-- **Adjoining relations of finite length.** Let `O` be a discrete valuation ring with uniformizer
`ϖ`, `R` an `O`-algebra and `N` an `R`-submodule of `F`. If the image of an `O`-submodule `P` of
`F` in `F ⧸ N` has length at most `n`, then `ϖ ^ n` multiplies the minors of `N ⊔ span R P` into
those of `N`. -/
theorem pow_mul_mem_minorsIdeal_of_length_map_mkQ_le {ϖ : O} (hϖ : Irreducible ϖ)
    {N : Submodule R F} {P : Submodule O F} {n : ℕ}
    (hP : length O (P.map (N.restrictScalars O).mkQ) ≤ n) {k : ℕ} {d : R}
    (hd : d ∈ (N ⊔ span R (P : Set F)).minorsIdeal k) :
    algebraMap O R (ϖ ^ n) * d ∈ N.minorsIdeal k := by
  induction n generalizing N d with
  | zero =>
    have hPN : span R (P : Set F) ≤ N := span_le.2 fun x hx ↦ by
      have : Subsingleton (P.map (N.restrictScalars O).mkQ) :=
        length_eq_zero_iff.1 (nonpos_iff_eq_zero.1 hP)
      have h : (N.restrictScalars O).mkQ x = 0 := congrArg Subtype.val
        (Subsingleton.elim (⟨_, mem_map_of_mem hx⟩ : P.map (N.restrictScalars O).mkQ) 0)
      simpa [Quotient.mk_eq_zero] using h
    rw [sup_eq_left.2 hPN] at hd
    simpa using hd
  | succ n ih =>
    by_cases hPN : P ≤ N.restrictScalars O
    · rw [sup_eq_left.2 (span_le.2 fun x hx ↦ by simpa using hPN hx)] at hd
      exact Ideal.mul_mem_left _ _ hd
    -- A nonzero class of the image of `P` killed by `ϖ`, lifted to `u ∈ P`.
    obtain ⟨u₀, hu₀P, hu₀N⟩ := IsConcreteLE.not_le_iff_exists.1 hPN
    have htors : Module.IsTorsion O (P.map (N.restrictScalars O).mkQ) :=
      isTorsion_of_length_ne_top (ne_top_of_le_ne_top (by simp) hP)
    obtain ⟨m, hy0, hϖy⟩ := TauCeti.exists_pow_smul_ne_zero_and_smul_eq_zero
      (w := (⟨_, mem_map_of_mem hu₀P⟩ : P.map (N.restrictScalars O).mkQ))
      (fun h ↦ hu₀N <| by simpa [Quotient.mk_eq_zero] using congrArg Subtype.val h)
      (exists_pow_smul_eq_zero hϖ htors _)
    generalize ϖ ^ m • (⟨_, mem_map_of_mem hu₀P⟩ : P.map (N.restrictScalars O).mkQ) = y
      at hy0 hϖy
    obtain ⟨y, hyP⟩ := y
    obtain ⟨u, huP, rfl⟩ := mem_map.1 hyP
    have huN : u ∉ N := fun h ↦ hy0 <| Subtype.ext <| by
      simpa [Quotient.mk_eq_zero] using h
    have hϖu : ϖ • u ∈ N := by
      have h := congrArg Subtype.val hϖy
      rw [SetLike.val_smul, ← map_smul, ZeroMemClass.coe_zero, mkQ_apply,
        Quotient.mk_eq_zero] at h
      simpa using h
    -- Adjoin `u`, at the cost of one factor `ϖ`.
    have hu : R ∙ u ≤ span R (P : Set F) := (span_singleton_le_iff_mem _ _).2 (subset_span huP)
    have hsup : N ⊔ R ∙ u ⊔ span R (P : Set F) = N ⊔ span R (P : Set F) := by
      rw [sup_assoc, sup_eq_right.2 hu]
    have h₁ := ih (length_map_mkQ_sup_span_singleton_le hP huP huN) (hsup ▸ hd)
    have hcolon : algebraMap O R ϖ ∈ N.colon {u} := mem_colon_singleton.2 (by
      rwa [algebraMap_smul])
    have h₂ := colon_mul_minorsIdeal_sup_span_singleton_le N u k (Ideal.mul_mem_mul hcolon h₁)
    rwa [← mul_assoc, ← map_mul, ← pow_succ'] at h₂

/-- **A minors ideal read along an `O`-algebra map.** Let `π : R → O` be an `O`-algebra map to a
discrete valuation ring and `N` an `R`-submodule of `R^ι`. Some `F` in the ideal of `#ι × #ι`
minors of `N` has `v(π F)` equal to the colength of the image of `N` in `O^ι`. -/
theorem exists_mem_minorsIdeal_addVal_eq_length {ι : Type*} [Fintype ι] (π : R →ₐ[O] O)
    (N : Submodule R (ι → R)) :
    ∃ F ∈ N.minorsIdeal (Fintype.card ι), addVal O (π F) =
      length O ((ι → O) ⧸ (N.restrictScalars O).map (π.toLinearMap.compLeft ι)) := by
  classical
  by_cases hN : length O ((ι → O) ⧸ (N.restrictScalars O).map (π.toLinearMap.compLeft ι)) = ⊤
  · exact ⟨0, zero_mem _, by rw [map_zero, AddValuation.map_zero, hN]⟩
  set U := (N.restrictScalars O).map (π.toLinearMap.compLeft ι)
  obtain ⟨B, hB⟩ := exists_matrix_span_range_row_eq U hN
  have hrow (i : ι) : B.row i ∈ U := hB ▸ subset_span ⟨i, rfl⟩
  choose n hn hnB using fun i ↦ mem_map.1 (hrow i)
  let e := Fintype.equivFin ι
  refine ⟨(Matrix.of fun i j ↦ n i j).det, ?_, ?_⟩
  · have h := det_mem_minorsIdeal (N := N) (fun k ↦ LinearMap.proj (e.symm k))
      (v := fun k ↦ n (e.symm k)) fun k ↦ (restrictScalars_mem O _ _).1 (hn _)
    rw [← Matrix.det_reindex_self e (Matrix.of fun i j ↦ n i j)]
    convert h using 2
    ext i j
    simp
  · rw [← hB, Matrix.length_quotient_span_range_eq_addVal_det, ← AlgHom.coe_toRingHom,
      RingHom.map_det]
    congr 2
    ext i j
    simpa using congr_fun (hnB i) j

end Submodule

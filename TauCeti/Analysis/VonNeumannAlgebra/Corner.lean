/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.Compression
public import TauCeti.Analysis.InnerProductSpace.Projection.ExtendByZero
public import TauCeti.Analysis.InnerProductSpace.UltraweakTopology
public import TauCeti.Analysis.InnerProductSpace.WeakOperatorTopology
public import TauCeti.Analysis.VonNeumannAlgebra.Bicommutant
public import TauCeti.Analysis.VonNeumannAlgebra.Lattice

import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Algebra.Star.Subalgebra
import TauCeti.Analysis.InnerProductSpace.Amplification
import TauCeti.Analysis.InnerProductSpace.Modulus

/-!
# Spatial corners and reduced von Neumann algebras

For a concrete von Neumann algebra `M` on a complex Hilbert space `H` and a closed subspace `U` of
`H` with orthogonal projection `p = U.starProjection`, if either `p ∈ M` (compression to a
projection in `M`, often written `pMp`) or `p ∈ M.commutant` (induction to a reducing subspace of
`M`, often written `Mp`), the compressions `x.compression U.subtypeL : U →L[ℂ] U` of operators
`x ∈ M` form a von Neumann algebra `M.corner U hU : VonNeumannAlgebra U` on `U`, and taking
commutants commutes with passing to the corner (`VonNeumannAlgebra.commutant_corner`,
`(pMp)' = pM'p`).

Unifying compression (`p ∈ M`) and induction (`p ∈ M.commutant`) in a single construction makes
`commutant_corner` swap the two regimes: localizing `M` to a projection `p ∈ M` simultaneously
restricts `M.commutant` to the reducing subspace `U = pH`. This duality underpins projection
comparison, Murray–von Neumann type classification, and subfactor Jones basic constructions, and
immediately yields preservation of scalar center (`corner_inf_commutant_eq_bot`), faithfulness of
induction (`cornerStarAlgEquiv`), and the commutant restriction isomorphism
(`commutantCornerStarAlgEquiv`) for factors.

## Main declarations and results

* `VonNeumannAlgebra.corner`: the spatial corner / induced von Neumann algebra `M.corner U hU` on
  `U` for `hU : U.starProjection ∈ M ∨ U.starProjection ∈ M.commutant`, with underlying set
  `(·.compression U.subtypeL) '' (M : Set (H →L[ℂ] H))`.
* `VonNeumannAlgebra.commutant_corner`: `(M.corner U hU).commutant = M.commutant.corner U _`,
  proved via finite amplification and the operator modulus (`ContinuousLinearMap.modulus`).
* `VonNeumannAlgebra.corner_inf_commutant` and `VonNeumannAlgebra.corner_inf_commutant_eq_bot`:
  `(M.corner U hU) ⊓ (M.corner U hU).commutant = (M ⊓ M.commutant).corner U _`; in particular,
  corners preserve having scalar center (`M ⊓ M.commutant = ⊥`), so nontrivial corners
  (`Nontrivial U`, i.e. `U.starProjection ≠ 0`) of factors are factors.
* `VonNeumannAlgebra.compressionStarAlgHom`, `VonNeumannAlgebra.cornerStarAlgEquiv`, and
  `VonNeumannAlgebra.commutantCornerStarAlgEquiv`: when `U.starProjection ∈ M.commutant`,
  compression to `U` is an ultraweakly and WOT-continuous unital `⋆`-homomorphism into `U →L[ℂ] U`
  with range the induced algebra `M.corner U (.inr hp)`, which is injective (giving
  `M ≃⋆ₐ[ℂ] M.corner U (.inr hp)`) whenever `M ⊓ M.commutant = ⊥` and `Nontrivial U`. Dually, when
  `M ⊓ M.commutant = ⊥`, `U.starProjection ∈ M`, and `Nontrivial U`, compression gives a unital
  `⋆`-algebra isomorphism `M.commutant ≃⋆ₐ[ℂ] (M.corner U (.inl hp)).commutant` (whose forward map
  `M.commutant.compressionStarAlgHom` into `U →L[ℂ] U` is ultraweakly and WOT-continuous).
* `VonNeumannAlgebra.adjoin_image_compression_of_mem_commutant` and
  `VonNeumannAlgebra.adjoin_image_compression_of_mul_mem`: generating sets of corners. When `s` is
  self-adjoint and multiplicatively closed and
  `U.starProjection ∈ adjoin s ∨ U.starProjection ∈ (adjoin s).commutant`,
  `(·.compression U.subtypeL) '' s` generates `(adjoin s).corner U hU`. See
  `TauCeti.Examples.Analysis.VonNeumannAlgebra.CornerAdjoin` for a counterexample when
  multiplicative closure is dropped.

## References

* J. Dixmier, *Von Neumann Algebras*, Part I, Chapter 2, §1, Propositions 1 and 2.
* R. V. Kadison and J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras I*,
  Proposition 5.5.6.
* V. F. R. Jones and V. S. Sunder, *Introduction to Subfactors*, Proposition 1.2.4.
-/

public section

open scoped InnerProductSpace Pointwise
open ContinuousLinearMap TauCeti

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Private commutant-induction helpers -/

section Private

/-- When `U.starProjection ∈ M`, an operator on `U` is the compression of an element of `M` if and
only if its extension by zero belongs to `M`. -/
private theorem mem_image_compression_iff_extendByZero_mem {M : VonNeumannAlgebra H}
    {U : Submodule ℂ H} [CompleteSpace U] (hp : U.starProjection ∈ M) {T : U →L[ℂ] U} :
    T ∈ (·.compression U.subtypeL) '' (M : Set (H →L[ℂ] H)) ↔ U.extendByZero T ∈ M := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [U.extendByZero_compression_subtypeL]
    exact mul_mem (mul_mem hp hx) hp
  · intro hT
    exact ⟨U.extendByZero T, hT, U.compression_extendByZero_subtypeL T⟩

/-- Step A of Dixmier's corner theorem: when `U.starProjection ∈ M`, the centralizer of the
compressed commutant `(·.compression U.subtypeL) '' M.commutant` is the compressed algebra
`(·.compression U.subtypeL) '' M`. -/
private theorem centralizer_image_compression_commutant_of_mem {M : VonNeumannAlgebra H}
    {U : Submodule ℂ H} [CompleteSpace U] (hp : U.starProjection ∈ M) :
    ((·.compression U.subtypeL) '' (M.commutant : Set (H →L[ℂ] H))).centralizer =
      (·.compression U.subtypeL) '' (M : Set (H →L[ℂ] H)) := by
  ext T
  rw [U.mem_centralizer_image_compression_subtypeL_iff_of_commute
      (fun y hy ↦ mem_commutant_iff.mp hy U.starProjection hp),
    ← coe_commutant, SetLike.mem_coe, M.commutant_commutant,
    mem_image_compression_iff_extendByZero_mem hp]

/-- Norm bound in Dixmier's commutant-induction proof: if `S` commutes with all compressions to `U`
of operators in `N.commutant`, then `‖∑ i, x i (S (u i))‖ ≤ ‖S‖ * ‖∑ i, x i (u i)‖` for every
finite tuple `x : Fin n → H →L[ℂ] H` in `N.commutant` and `u : Fin n → U`. -/
private theorem norm_sum_apply_le_of_mem_centralizer {N : VonNeumannAlgebra H}
    {U : Submodule ℂ H} [CompleteSpace U] {S : U →L[ℂ] U}
    (hS : S ∈ ((·.compression U.subtypeL) '' (N.commutant : Set (H →L[ℂ] H))).centralizer)
    {n : ℕ} (x : Fin n → H →L[ℂ] H) (hx : ∀ i, x i ∈ N.commutant) (u : Fin n → U) :
    ‖∑ i : Fin n, x i (S (u i))‖ ≤ ‖S‖ * ‖∑ i : Fin n, x i (u i)‖ := by
  -- Express `∑ i, x i (u i)` as `X η` on the `L²` direct sum `U^n`.
  let X : PiLp 2 (fun _ : Fin n ↦ U) →L[ℂ] H :=
    ∑ i : Fin n, x i ∘L U.subtypeL ∘L PiLp.proj 2 (fun _ : Fin n ↦ U) i
  have hX_apply (η : PiLp 2 (fun _ : Fin n ↦ U)) : X η = ∑ i : Fin n, x i (η i) := by
    simp only [X, sum_apply, comp_apply, U.coe_subtypeL, Submodule.coe_subtype, PiLp.proj_apply]
  have hX_single (j : Fin n) (w : U) : X (PiLp.single 2 j w) = x j w := by
    rw [hX_apply, Finset.sum_eq_single j (fun i _ hij ↦ by simp [hij])
      (fun hj ↦ absurd (Finset.mem_univ j) hj)]
    simp
  -- Every matrix entry of `X† ∘L X` is a compression from `N.commutant`, so `X† ∘L X` commutes
  -- with the diagonal amplification `Sₙ`.
  let A : PiLp 2 (fun _ : Fin n ↦ U) →L[ℂ] PiLp 2 (fun _ : Fin n ↦ U) := X.adjoint ∘L X
  have hA_entry (i j : Fin n) :
      A.piLpEntry i j = (star (x i) * x j).compression U.subtypeL := by
    refine ContinuousLinearMap.ext fun w ↦ ext_inner_left ℂ fun v ↦ ?_
    have hsingle (ξ : PiLp 2 (fun _ : Fin n ↦ U)) : ⟪v, ξ i⟫_ℂ = ⟪PiLp.single 2 i v, ξ⟫_ℂ := by
      rw [PiLp.inner_apply, Finset.sum_eq_single i (fun k _ hki ↦ by simp [hki])
        (fun hi ↦ absurd (Finset.mem_univ i) hi)]
      simp
    rw [piLpEntry_apply, hsingle, comp_apply, adjoint_inner_right, hX_single, hX_single,
      inner_compression_apply, mul_def, comp_apply, star_eq_adjoint, adjoint_inner_right,
      U.coe_subtypeL, Submodule.coe_subtype]
  let Sₙ := PiLp.diagStarAlgHom ℂ U (Fin n) S
  have hAS : Commute A Sₙ :=
    (A.commute_diagStarAlgHom_iff S).mpr fun i j ↦ by
      rw [hA_entry, commute_iff_eq]
      exact Set.mem_centralizer_iff.mp hS _
        ⟨star (x i) * x j, mul_mem (star_mem (hx i)) (hx j), rfl⟩
  -- Conclude from the modulus norm inequality for `X` and contractivity of `diagStarAlgHom`.
  let η : PiLp 2 (fun _ : Fin n ↦ U) := WithLp.toLp 2 u
  have hSₙ_η : X (Sₙ η) = ∑ i : Fin n, x i (S (u i)) := by
    simp only [hX_apply, Sₙ, PiLp.diagStarAlgHom_apply, η]
  calc
    ‖∑ i : Fin n, x i (S (u i))‖ = ‖X (Sₙ η)‖ := by rw [hSₙ_η]
    _ ≤ ‖Sₙ‖ * ‖X η‖ := X.norm_apply_le_of_commute_adjoint_comp_self hAS η
    _ ≤ ‖S‖ * ‖X η‖ :=
      mul_le_mul_of_nonneg_right
        (NonUnitalStarAlgHom.norm_apply_le (PiLp.diagStarAlgHom ℂ U (Fin n)) S) (norm_nonneg _)
    _ = ‖S‖ * ‖∑ i : Fin n, x i (u i)‖ := by simp only [hX_apply, η]

/-- Linear combination map `d ↦ ∑ x, x (d x)` from finitely supported `U`-valued tuples on
`N.commutant` to `H`. -/
private noncomputable def commutantOrbitMap (N : VonNeumannAlgebra H) (U : Submodule ℂ H) :
    (N.commutant →₀ U) →ₗ[ℂ] H :=
  Finsupp.lsum ℂ fun x : N.commutant ↦ (x : H →L[ℂ] H).toLinearMap.comp U.subtype

private theorem commutantOrbitMap_apply (N : VonNeumannAlgebra H) (U : Submodule ℂ H)
    (d : N.commutant →₀ U) :
    commutantOrbitMap N U d = ∑ x ∈ d.support, (x : H →L[ℂ] H) (d x) := by
  simp [commutantOrbitMap, Finsupp.lsum_apply, Finsupp.sum]

private theorem commutantOrbitMap_mapRange (N : VonNeumannAlgebra H) {U : Submodule ℂ H}
    (S : U →L[ℂ] U) (d : N.commutant →₀ U) :
    commutantOrbitMap N U (d.mapRange S S.map_zero) =
      ∑ x ∈ d.support, (x : H →L[ℂ] H) (S (d x)) := by
  rw [commutantOrbitMap, Finsupp.lsum_apply, Finsupp.sum_mapRange_index (fun _ ↦ by simp),
    Finsupp.sum]
  simp [LinearMap.comp_apply]

private theorem commutantOrbitMap_mapDomain_mul {N : VonNeumannAlgebra H} {U : Submodule ℂ H}
    {z : H →L[ℂ] H} (hz : z ∈ N.commutant) (d : N.commutant →₀ U) :
    commutantOrbitMap N U
        (Finsupp.mapDomain (fun x : N.commutant ↦ ⟨z * x, mul_mem hz x.property⟩) d) =
      z (commutantOrbitMap N U d) := by
  rw [commutantOrbitMap, Finsupp.lsum_apply, Finsupp.lsum_apply,
    Finsupp.sum_mapDomain_index (fun _ ↦ by simp) (fun _ _ _ ↦ by simp [map_add]),
    Finsupp.sum, Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by simp [LinearMap.comp_apply]

/-- Closed subspace of `H` spanned by the `N.commutant`-orbit of `U`. -/
private noncomputable abbrev commutantOrbitClosure (N : VonNeumannAlgebra H) (U : Submodule ℂ H) :
    Submodule ℂ H :=
  (LinearMap.range (commutantOrbitMap N U)).topologicalClosure

/-- Codomain restriction of `commutantOrbitMap N U` to `commutantOrbitClosure N U`. -/
private noncomputable def commutantOrbitCodRestrict (N : VonNeumannAlgebra H) (U : Submodule ℂ H) :
    (N.commutant →₀ U) →ₗ[ℂ] commutantOrbitClosure N U :=
  (commutantOrbitMap N U).codRestrict (commutantOrbitClosure N U) fun d ↦
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ d)

private theorem denseRange_commutantOrbitCodRestrict (N : VonNeumannAlgebra H)
    (U : Submodule ℂ H) :
    DenseRange (commutantOrbitCodRestrict N U) := by
  rw [DenseRange, Subtype.dense_iff, ← Set.range_comp]
  exact (Submodule.topologicalClosure_coe _).subset

private theorem starProjection_commutantOrbitClosure_mem (N : VonNeumannAlgebra H)
    (U : Submodule ℂ H) :
    (commutantOrbitClosure N U).starProjection ∈ N := by
  have hrange : LinearMap.range (commutantOrbitMap N U) =
      Submodule.span ℂ {w : H | ∃ x ∈ N.commutant, ∃ v ∈ (U : Set H), x v = w} := by
    refine le_antisymm (by
        rintro _ ⟨d, rfl⟩; rw [commutantOrbitMap_apply]
        exact sum_mem fun x _ ↦ Submodule.subset_span ⟨x.val, x.property, d x, (d x).property, rfl⟩)
      (Submodule.span_le.mpr ?_)
    rintro _ ⟨x, hx, v, hv, rfl⟩
    exact ⟨Finsupp.single ⟨x, hx⟩ ⟨v, hv⟩, by simp [commutantOrbitMap]⟩
  unfold commutantOrbitClosure
  rw [hrange]
  simpa only [N.commutant_commutant] using
    N.commutant.starProjection_topologicalClosure_span_mem_commutant (U : Set H)

/-- Bounded extension of `∑ x, x (d x) ↦ ∑ x, x (S (d x))` to `commutantOrbitClosure N U`. -/
private theorem exists_apply_commutantOrbitCodRestrict_eq_of_mem_centralizer
    {N : VonNeumannAlgebra H} {U : Submodule ℂ H} [CompleteSpace U] {S : U →L[ℂ] U}
    (hS : S ∈ ((·.compression U.subtypeL) '' (N.commutant : Set (H →L[ℂ] H))).centralizer) :
    ∃ Y : commutantOrbitClosure N U →L[ℂ] commutantOrbitClosure N U,
      ∀ d : N.commutant →₀ U,
        Y (commutantOrbitCodRestrict N U d) =
          commutantOrbitCodRestrict N U (d.mapRange S S.map_zero) := by
  let eK := commutantOrbitCodRestrict N U
  let fK : (N.commutant →₀ U) →ₗ[ℂ] commutantOrbitClosure N U :=
    eK.comp (Finsupp.mapRange.linearMap S.toLinearMap)
  have h_norm (d : N.commutant →₀ U) : ‖fK d‖ ≤ ‖S‖ * ‖eK d‖ := by
    let e : Fin d.support.card ≃ d.support := d.support.equivFin.symm
    have hΦ : commutantOrbitMap N U d = ∑ k, ((e k).val : H →L[ℂ] H) (d (e k).val) := by
      rw [commutantOrbitMap_apply, ← Finset.sum_coe_sort, ← e.sum_comp]
    have hΨ : commutantOrbitMap N U (d.mapRange S S.map_zero) =
        ∑ k, ((e k).val : H →L[ℂ] H) (S (d (e k).val)) := by
      rw [commutantOrbitMap_mapRange, ← Finset.sum_coe_sort, ← e.sum_comp]
    rw [← Submodule.norm_coe (fK d), ← Submodule.norm_coe (eK d)]
    simpa only [eK, fK, commutantOrbitCodRestrict, LinearMap.comp_apply,
      Finsupp.mapRange.linearMap_apply, ContinuousLinearMap.coe_coe, LinearMap.codRestrict_apply,
      hΨ, hΦ] using
      norm_sum_apply_le_of_mem_centralizer hS (fun k ↦ ((e k).val : H →L[ℂ] H))
        (fun k ↦ (e k).val.property) (fun k ↦ d (e k).val)
  exact ⟨fK.extendOfNorm eK, fun d ↦
    LinearMap.extendOfNorm_eq (denseRange_commutantOrbitCodRestrict N U) ⟨‖S‖, h_norm⟩ d⟩

/-- The dense extension `Y` on `commutantOrbitClosure N U` commutes with the compression of every
operator in `N.commutant`. -/
private theorem commute_compression_of_forall_apply_commutantOrbitCodRestrict
    {N : VonNeumannAlgebra H} {U : Submodule ℂ H} {S : U →L[ℂ] U}
    {Y : commutantOrbitClosure N U →L[ℂ] commutantOrbitClosure N U}
    (hY : ∀ d : N.commutant →₀ U,
      Y (commutantOrbitCodRestrict N U d) =
        commutantOrbitCodRestrict N U (d.mapRange S S.map_zero))
    {z : H →L[ℂ] H} (hz : z ∈ N.commutant) :
    Commute (z.compression (commutantOrbitClosure N U).subtypeL) Y := by
  set K := commutantOrbitClosure N U
  have hzK (q : K) : (z.compression K.subtypeL q : H) = z (q : H) := by
    simpa [K.coe_subtypeL] using DFunLike.congr_fun
      (K.subtypeL_comp_compression_of_commute
        (mem_commutant_iff.mp hz K.starProjection
          (starProjection_commutantOrbitClosure_mem N U))) q
  rw [Commute, SemiconjBy]
  refine ContinuousLinearMap.ext fun w ↦ ?_
  refine (denseRange_commutantOrbitCodRestrict N U).induction
    (fun v hv ↦ ?_) (isClosed_eq (by fun_prop) (by fun_prop)) w
  obtain ⟨d, rfl⟩ := hv
  apply Subtype.ext
  simp only [mul_apply_eq_comp]
  let mulDom : N.commutant → N.commutant := fun x ↦ ⟨z * x, mul_mem hz x.property⟩
  have heK_zd : z.compression K.subtypeL (commutantOrbitCodRestrict N U d) =
      commutantOrbitCodRestrict N U (Finsupp.mapDomain mulDom d) := by
    apply Subtype.ext
    rw [hzK, commutantOrbitCodRestrict, LinearMap.codRestrict_apply, LinearMap.codRestrict_apply,
      commutantOrbitMap_mapDomain_mul hz d]
  rw [hY d, hzK, heK_zd, hY, ← Finsupp.mapDomain_mapRange mulDom d S S.map_zero S.map_add,
    commutantOrbitCodRestrict, LinearMap.codRestrict_apply, LinearMap.codRestrict_apply,
    commutantOrbitMap_mapDomain_mul hz]

/-- Step B of Dixmier's corner theorem: when `U.starProjection ∈ N.commutant`, the centralizer of
the compressed commutant `(·.compression U.subtypeL) '' N.commutant` is the compressed algebra
`(·.compression U.subtypeL) '' N`. -/
private theorem centralizer_image_compression_commutant_of_mem_commutant {N : VonNeumannAlgebra H}
    {U : Submodule ℂ H} [CompleteSpace U] (hp : U.starProjection ∈ N.commutant) :
    ((·.compression U.subtypeL) '' (N.commutant : Set (H →L[ℂ] H))).centralizer =
      (·.compression U.subtypeL) '' (N : Set (H →L[ℂ] H)) := by
  refine Set.Subset.antisymm (fun S hS ↦ ?_) ?_
  · -- Extend `∑ x, x (d x) ↦ ∑ x, x (S (d x))` to a bounded operator `Y` on the closed orbit `K`.
    set K := commutantOrbitClosure N U
    obtain ⟨Y, hY⟩ := exists_apply_commutantOrbitCodRestrict_eq_of_mem_centralizer hS
    -- Extend `Y` by zero to `y ∈ N'' = N` on `H`.
    let y : H →L[ℂ] H := K.extendByZero Y
    have hyN : y ∈ N := by
      rw [← N.commutant_commutant, mem_commutant_iff]
      intro z hz
      exact ((K.commute_extendByZero_iff_of_commute
        (mem_commutant_iff.mp hz K.starProjection (starProjection_commutantOrbitClosure_mem N U))
        Y).mpr (by
          rw [← compression_subtypeL]
          exact (commute_compression_of_forall_apply_commutantOrbitCodRestrict hY hz).symm)).symm.eq
    -- On `U ⊆ K` (`x = 1`), `y` agrees with `S`, so `y.compression U.subtypeL = S`.
    refine ⟨y, hyN, compression_eq_of_isometry_of_forall_apply_eq U.subtypeₗᵢ.isometry fun u ↦ ?_⟩
    let d₀ : N.commutant →₀ U := Finsupp.single ⟨1, N.commutant.one_mem⟩ u
    have h₀ : y (U.subtypeL u) = y (commutantOrbitCodRestrict N U d₀) := by
      simp [commutantOrbitCodRestrict, commutantOrbitMap, d₀]
    rw [h₀, K.extendByZero_apply_coe, hY]
    simp [commutantOrbitCodRestrict, commutantOrbitMap, d₀]
  · -- Conversely, compressing any `y ∈ N` commutes with compressing `N.commutant` since `U`
    -- reduces `N`.
    rintro _ ⟨y, hy, rfl⟩
    rw [Set.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hpy : Commute U.starProjection y := (mem_commutant_iff.mp hp y hy).symm
    rw [← U.compression_subtypeL_mul_of_commute_right x hpy,
      (mem_commutant_iff.mp hx y hy).symm, U.compression_subtypeL_mul_of_commute_left x hpy]

private theorem centralizer_image_compression_commutant {M : VonNeumannAlgebra H}
    {U : Submodule ℂ H} [CompleteSpace U]
    (hU : U.starProjection ∈ M ∨ U.starProjection ∈ M.commutant) :
    ((·.compression U.subtypeL) '' (M.commutant : Set (H →L[ℂ] H))).centralizer =
      (·.compression U.subtypeL) '' (M : Set (H →L[ℂ] H)) :=
  hU.elim centralizer_image_compression_commutant_of_mem
    centralizer_image_compression_commutant_of_mem_commutant

end Private

/-! ### The spatial corner / reduced von Neumann algebra -/

/-- **The spatial corner (reduced von Neumann algebra) `pMp` on `U = pH`.** When the orthogonal
projection `U.starProjection` onto a closed subspace `U` lies either in `M` or in `M.commutant`,
the compressions `x.compression U.subtypeL` of elements `x ∈ M` form a von Neumann algebra on `U`.
-/
noncomputable def corner (M : VonNeumannAlgebra H) (U : Submodule ℂ H) [CompleteSpace U]
    (hU : U.starProjection ∈ M ∨ U.starProjection ∈ M.commutant) :
    VonNeumannAlgebra U :=
  ((adjoin ((·.compression U.subtypeL) '' (M.commutant : Set (H →L[ℂ] H)))).commutant).copy
    ((·.compression U.subtypeL) '' (M : Set (H →L[ℂ] H))) <| by
      rw [coe_commutant_adjoin, star_image_compression, StarMemClass.star_coe_eq, Set.union_self,
        centralizer_image_compression_commutant hU]

/-- The carrier set of `M.corner U hU` is the image of `M` under compression along `U.subtypeL`. -/
@[simp, norm_cast]
theorem coe_corner (M : VonNeumannAlgebra H) (U : Submodule ℂ H) [CompleteSpace U]
    (hU : U.starProjection ∈ M ∨ U.starProjection ∈ M.commutant) :
    (M.corner U hU : Set (U →L[ℂ] U)) = (·.compression U.subtypeL) '' (M : Set (H →L[ℂ] H)) :=
  coe_copy _ _ _

/-- An operator on `U` belongs to `M.corner U hU` if and only if it is the compression of an
operator in `M`. -/
@[simp]
theorem mem_corner_iff {M : VonNeumannAlgebra H} {U : Submodule ℂ H} [CompleteSpace U]
    {hU : U.starProjection ∈ M ∨ U.starProjection ∈ M.commutant} {T : U →L[ℂ] U} :
    T ∈ M.corner U hU ↔ ∃ x ∈ M, x.compression U.subtypeL = T := by
  simp only [← SetLike.mem_coe, coe_corner, Set.mem_image]

/-- `M.corner U hU` depends only on `M` and `U`, and is independent of the proof witness `hU`. -/
theorem corner_congr {M N : VonNeumannAlgebra H} {U : Submodule ℂ H} [CompleteSpace U]
    {hM : U.starProjection ∈ M ∨ U.starProjection ∈ M.commutant}
    {hN : U.starProjection ∈ N ∨ U.starProjection ∈ N.commutant} (hMN : M = N) :
    M.corner U hM = N.corner U hN := by
  subst hMN
  rfl

/-- The compression to `U` of any element of `M` belongs to `M.corner U hU`. -/
theorem compression_mem_corner {M : VonNeumannAlgebra H} {U : Submodule ℂ H} [CompleteSpace U]
    (hU : U.starProjection ∈ M ∨ U.starProjection ∈ M.commutant) {x : H →L[ℂ] H} (hx : x ∈ M) :
    x.compression U.subtypeL ∈ M.corner U hU :=
  mem_corner_iff.mpr ⟨x, hx, rfl⟩

/-- When `U.starProjection ∈ M`, an operator `T : U →L[ℂ] U` belongs to `M.corner U (.inl hp)` if
and only if its extension by zero `U.extendByZero T` belongs to `M`. -/
theorem mem_corner_iff_extendByZero_mem {M : VonNeumannAlgebra H} {U : Submodule ℂ H}
    [CompleteSpace U] (hp : U.starProjection ∈ M) {T : U →L[ℂ] U} :
    T ∈ M.corner U (.inl hp) ↔ U.extendByZero T ∈ M := by
  rw [← SetLike.mem_coe, coe_corner]
  exact mem_image_compression_iff_extendByZero_mem hp

/-- **Dixmier's commutant-induction theorem (`(pMp)' = pM'p`).** For any closed subspace `U` whose
orthogonal projection lies in `M` or in `M.commutant`, the commutant of `M.corner U hU` is the
corner of `M.commutant` on `U`. -/
theorem commutant_corner (M : VonNeumannAlgebra H) (U : Submodule ℂ H) [CompleteSpace U]
    (hU : U.starProjection ∈ M ∨ U.starProjection ∈ M.commutant) :
    (M.corner U hU).commutant =
      M.commutant.corner U (hU.elim (fun hp ↦ .inr (by simpa using hp)) .inl) := by
  have hU' : U.starProjection ∈ M.commutant ∨ U.starProjection ∈ M.commutant.commutant :=
    hU.elim (fun hp ↦ .inr (by simpa using hp)) .inl
  apply SetLike.coe_injective
  rw [coe_commutant, coe_corner, coe_corner, ← M.commutant_commutant]
  have h := centralizer_image_compression_commutant (M := M.commutant) hU'
  simpa [M.commutant_commutant] using h

/-- The corner of the scalar algebra `⊥` on `U` is the scalar algebra `⊥` on `U`. -/
@[simp]
theorem corner_bot (U : Submodule ℂ H) [CompleteSpace U]
    (hU : U.starProjection ∈ (⊥ : VonNeumannAlgebra H) ∨
      U.starProjection ∈ (⊥ : VonNeumannAlgebra H).commutant) :
    (⊥ : VonNeumannAlgebra H).corner U hU = ⊥ := by
  apply SetLike.coe_injective
  rw [coe_corner, coe_bot, coe_bot]
  ext T
  simp only [Set.mem_image, Set.mem_range, Algebra.algebraMap_eq_smul_one]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩; exact ⟨c, by rw [compression_smul, compression_one_subtypeL]⟩
  · rintro ⟨c, rfl⟩; exact ⟨c • 1, ⟨c, rfl⟩, by rw [compression_smul, compression_one_subtypeL]⟩

/-- The corner of `⊤ = B(H)` on `U` is `⊤ = B(U)`. -/
@[simp]
theorem corner_top (U : Submodule ℂ H) [CompleteSpace U]
    (hU : U.starProjection ∈ (⊤ : VonNeumannAlgebra H) ∨
      U.starProjection ∈ (⊤ : VonNeumannAlgebra H).commutant) :
    (⊤ : VonNeumannAlgebra H).corner U hU = ⊤ :=
  eq_top_iff.mpr fun T _ ↦
    mem_corner_iff.mpr ⟨U.extendByZero T, mem_top, U.compression_extendByZero_subtypeL T⟩

/-- Passing to a corner on `U` is monotone in the von Neumann algebra. -/
theorem corner_mono {M N : VonNeumannAlgebra H} {U : Submodule ℂ H} [CompleteSpace U]
    {hM : U.starProjection ∈ M ∨ U.starProjection ∈ M.commutant}
    {hN : U.starProjection ∈ N ∨ U.starProjection ∈ N.commutant} (hMN : M ≤ N) :
    M.corner U hM ≤ N.corner U hN :=
  fun _ hT ↦ let ⟨x, hx, hTx⟩ := mem_corner_iff.mp hT; mem_corner_iff.mpr ⟨x, hMN hx, hTx⟩

/-- Auxiliary witness that `U.starProjection ∈ (M ⊓ M.commutant).commutant` whenever
`U.starProjection ∈ M ∨ U.starProjection ∈ M.commutant`. -/
theorem starProjection_mem_commutant_inf_commutant {M : VonNeumannAlgebra H} {U : Submodule ℂ H}
    [U.HasOrthogonalProjection] (hU : U.starProjection ∈ M ∨ U.starProjection ∈ M.commutant) :
    U.starProjection ∈ (M ⊓ M.commutant).commutant := by
  rcases hU with hp | hp
  · exact commutant_le_commutant inf_le_right (M.commutant_commutant.symm ▸ hp)
  · exact commutant_le_commutant inf_le_left hp

/-- If `b, y ∈ M.commutant` preserve `U` (`hp : U.starProjection ∈ M`) and their compressions to
`U` commute, then `b * y` and `y * b` agree on the closed `M`-orbit of `U`. -/
private theorem mul_eqOn_topologicalClosure_span_of_commute_compression {M : VonNeumannAlgebra H}
    {U : Submodule ℂ H} [CompleteSpace U] (hp : U.starProjection ∈ M)
    {b y : H →L[ℂ] H} (hb : b ∈ M.commutant) (hy : y ∈ M.commutant)
    (hcomm : Commute (b.compression U.subtypeL) (y.compression U.subtypeL)) :
    ∀ w ∈ (Submodule.span ℂ {v : H | ∃ a ∈ M, ∃ u ∈ (U : Set H), a u = v}).topologicalClosure,
      (b * y) w = (y * b) w := by
  set L₀ : Submodule ℂ H := Submodule.span ℂ {v : H | ∃ a ∈ M, ∃ u ∈ (U : Set H), a u = v}
  let eqSub : Submodule ℂ H := LinearMap.eqLocus (b * y).toLinearMap (y * b).toLinearMap
  have hclosed : IsClosed (eqSub : Set H) := isClosed_eq (b * y).continuous (y * b).continuous
  have hbyU := U.mul_comp_subtypeL_eq_of_commute_compression
    (mem_commutant_iff.mp hb U.starProjection hp)
    (mem_commutant_iff.mp hy U.starProjection hp) hcomm
  have hL₀ : L₀ ≤ eqSub := by
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, u, hu, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_eqLocus, coe_coe, coe_coe]
    have hya (w : H) : y (a w) = a (y w) :=
      DFunLike.congr_fun (mem_commutant_iff.mp hy a ha).symm w
    have hba (w : H) : b (a w) = a (b w) :=
      DFunLike.congr_fun (mem_commutant_iff.mp hb a ha).symm w
    have hbyu : b (y u) = y (b u) := by
      simpa [comp_apply, U.coe_subtypeL] using DFunLike.congr_fun hbyU ⟨u, hu⟩
    simp only [mul_apply_eq_comp, hya, hba, hbyu]
  exact fun w hw ↦ Submodule.topologicalClosure_minimal _ hL₀ hclosed hw

private theorem corner_inf_commutant_of_mem {M : VonNeumannAlgebra H} {U : Submodule ℂ H}
    [CompleteSpace U] (hp : U.starProjection ∈ M) :
    M.corner U (.inl hp) ⊓ (M.corner U (.inl hp)).commutant =
      (M ⊓ M.commutant).corner U (.inr (starProjection_mem_commutant_inf_commutant (.inl hp))) := by
  refine le_antisymm (fun T hT ↦ ?_) ?_
  · obtain ⟨hTM, hTM'⟩ : T ∈ M.corner U (.inl hp) ∧ T ∈ (M.corner U (.inl hp)).commutant :=
      mem_inf.mp hT
    rw [commutant_corner] at hTM'
    obtain ⟨y, hy, rfl⟩ := mem_corner_iff.mp hTM'
    -- The closed `M`-orbit `L` of `U` has central projection `L.starProjection ∈ M ⊓ M.commutant`.
    set L : Submodule ℂ H :=
      (Submodule.span ℂ {v : H | ∃ a ∈ M, ∃ u ∈ (U : Set H), a u = v}).topologicalClosure
    have hL_M : L.starProjection ∈ M.commutant :=
      M.starProjection_topologicalClosure_span_mem_commutant (U : Set H)
    have hL_M' : L.starProjection ∈ M :=
      M.starProjection_topologicalClosure_span_mem fun b hb _ hu ↦
        (starProjection_mem_iff_mem_invtSubmodule U).mp hp b hb hu
    -- Cut `y ∈ M.commutant` down to `L` to obtain a central preimage `z = L.starProjection * y`.
    set z : H →L[ℂ] H := L.starProjection * y with hz_def
    have hzM' : z ∈ M.commutant := mul_mem hL_M hy
    have hzM : z ∈ M := by
      rw [← M.commutant_commutant, mem_commutant_iff]
      intro b hb
      have hbL : b * L.starProjection = L.starProjection * b :=
        (mem_commutant_iff.mp hb L.starProjection hL_M').symm
      have hyL : y * L.starProjection = L.starProjection * y :=
        (mem_commutant_iff.mp hy L.starProjection hL_M').symm
      have hcomm_comp : Commute (b.compression U.subtypeL) (y.compression U.subtypeL) := by
        rw [commute_iff_eq]
        exact (mem_commutant_iff.mp (commutant_corner M U (.inl hp) ▸ compression_mem_corner _ hb)
          _ hTM).symm
      have eqOnL := mul_eqOn_topologicalClosure_span_of_commute_compression hp hb hy hcomm_comp
      refine ContinuousLinearMap.ext fun ξ ↦ ?_
      rw [show (b * z) ξ = (b * y) (L.starProjection ξ) by
          rw [hz_def, ← hyL, ← mul_assoc, mul_apply_eq_comp],
        show (z * b) ξ = (y * b) (L.starProjection ξ) by
          rw [hz_def, ← hyL, mul_assoc, ← hbL, ← mul_assoc, mul_apply_eq_comp],
        eqOnL _ (L.starProjection_apply_mem ξ)]
    -- Since `U ⊆ L`, `z` and `y` have the same compression to `U`.
    rw [mem_corner_iff]
    refine ⟨z, mem_inf.mpr ⟨hzM, hzM'⟩, compression_eq_of_forall_apply_eq fun u ↦ ?_⟩
    have huL : (u : H) ∈ L := Submodule.le_topologicalClosure _
      (Submodule.subset_span ⟨1, M.one_mem, u, u.property, one_apply_eq_self _⟩)
    rw [U.coe_subtypeL, Submodule.coe_subtype, hz_def,
      mem_commutant_iff.mp hy L.starProjection hL_M', mul_apply_eq_comp,
      L.starProjection_eq_self_iff.mpr huL]
  · exact le_inf (corner_mono inf_le_left)
      (commutant_corner M U (.inl hp) ▸ corner_mono inf_le_right)

/-- **The center of a corner is the corner of the center.** -/
theorem corner_inf_commutant (M : VonNeumannAlgebra H) (U : Submodule ℂ H) [CompleteSpace U]
    (hU : U.starProjection ∈ M ∨ U.starProjection ∈ M.commutant) :
    M.corner U hU ⊓ (M.corner U hU).commutant =
      (M ⊓ M.commutant).corner U (.inr (starProjection_mem_commutant_inf_commutant hU)) := by
  rcases hU with hp | hp
  · exact corner_inf_commutant_of_mem hp
  · have hcomm : (M.corner U (.inr hp)).commutant = M.commutant.corner U (.inl hp) := by
      simpa using commutant_corner M U (.inr hp)
    have h1 := corner_inf_commutant_of_mem (M := M.commutant) hp
    rw [show (M.commutant.corner U (.inl hp)).commutant = M.corner U (.inr hp) by
      rw [← hcomm, commutant_commutant], inf_comm] at h1
    exact (congrArg (M.corner U (.inr hp) ⊓ ·) hcomm).trans <|
      h1.trans <| corner_congr (by rw [M.commutant_commutant, inf_comm])

/-- **Corners preserve having scalar center:** if `M ⊓ M.commutant = ⊥`, then any corner
`M.corner U hU` also has scalar center `M.corner U hU ⊓ (M.corner U hU).commutant = ⊥` (so
nontrivial corners of factors are factors). -/
theorem corner_inf_commutant_eq_bot {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    (U : Submodule ℂ H) [CompleteSpace U]
    (hU : U.starProjection ∈ M ∨ U.starProjection ∈ M.commutant) :
    M.corner U hU ⊓ (M.corner U hU).commutant = ⊥ := by
  rw [corner_inf_commutant]
  exact (corner_congr (hN := .inr (by simp)) hM).trans (corner_bot U _)

/-! ### Induction `⋆`-homomorphisms and factor commutant restriction isomorphisms -/

/-- When `U.starProjection ∈ M.commutant`, compression along `U.subtypeL` defines a unital
`⋆`-algebra homomorphism `M →⋆ₐ[ℂ] (U →L[ℂ] U)` into `U →L[ℂ] U`, with range the induced algebra
`M.corner U (.inr hp)`. -/
noncomputable def compressionStarAlgHom (M : VonNeumannAlgebra H) (U : Submodule ℂ H)
    [CompleteSpace U] (hp : U.starProjection ∈ M.commutant) :
    M.toStarSubalgebra →⋆ₐ[ℂ] (U →L[ℂ] U) where
  toFun x := (x : H →L[ℂ] H).compression U.subtypeL
  map_one' := compression_one_subtypeL U
  map_mul' x y :=
    U.compression_subtypeL_mul_of_commute_left (y : H →L[ℂ] H)
      (mem_commutant_iff.mp hp x x.property).symm
  map_zero' := compression_zero U.subtypeL
  map_add' x y := compression_add (x : H →L[ℂ] H) U.subtypeL (y : H →L[ℂ] H)
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, SetLike.val_smul, OneMemClass.coe_one,
      compression_smul, compression_one_subtypeL]
  map_star' x := compression_star (x : H →L[ℂ] H) U.subtypeL

/-- `M.compressionStarAlgHom U hp` acts by compressing along `U.subtypeL`. -/
@[simp]
theorem compressionStarAlgHom_apply (M : VonNeumannAlgebra H) (U : Submodule ℂ H) [CompleteSpace U]
    (hp : U.starProjection ∈ M.commutant) (x : M.toStarSubalgebra) :
    M.compressionStarAlgHom U hp x = (x : H →L[ℂ] H).compression U.subtypeL :=
  (rfl)

/-- The range of `M.compressionStarAlgHom U hp` is the induced algebra `M.corner U (.inr hp)`. -/
@[simp]
theorem compressionStarAlgHom_range (M : VonNeumannAlgebra H) (U : Submodule ℂ H) [CompleteSpace U]
    (hp : U.starProjection ∈ M.commutant) :
    (M.compressionStarAlgHom U hp).range = (M.corner U (.inr hp)).toStarSubalgebra := by
  ext T
  rw [mem_carrier, SetLike.mem_coe, mem_corner_iff]
  exact ⟨fun ⟨x, hx⟩ ↦ ⟨x.val, x.property, by simpa using hx⟩,
    fun ⟨x, hx, hTx⟩ ↦ ⟨⟨x, hx⟩, by simpa using hTx⟩⟩

/-- `compressionStarAlgHom` is continuous with respect to the ultraweak operator topologies on `M`
and `U →L[ℂ] U`. -/
@[fun_prop]
theorem continuous_ultraweak_compressionStarAlgHom (M : VonNeumannAlgebra H) (U : Submodule ℂ H)
    [CompleteSpace U] (hp : U.starProjection ∈ M.commutant) :
    Continuous fun A : {A : ContinuousLinearMapUltraweak ℂ H H // A.toCLM ∈ M} ↦
      ContinuousLinearMapUltraweak.ofCLM
        (M.compressionStarAlgHom U hp ⟨A.val.toCLM, A.property⟩) := by
  simp only [compressionStarAlgHom_apply]
  exact (ContinuousLinearMapUltraweak.continuous_compression U.subtypeL).comp continuous_subtypeVal

/-- `compressionStarAlgHom` is continuous with respect to the weak operator topologies on `M` and
`U →L[ℂ] U`. -/
@[fun_prop]
theorem continuous_wot_compressionStarAlgHom (M : VonNeumannAlgebra H) (U : Submodule ℂ H)
    [CompleteSpace U] (hp : U.starProjection ∈ M.commutant) :
    Continuous fun A : {A : H →WOT[ℂ] H // A.toCLM ∈ M} ↦
      ContinuousLinearMapWOT.ofCLM (M.compressionStarAlgHom U hp ⟨A.val.toCLM, A.property⟩) := by
  simp only [compressionStarAlgHom_apply]
  exact (ContinuousLinearMapWOT.continuous_compression U.subtypeL).comp continuous_subtypeVal

/-- **Faithfulness of induction for factors.** If `M ⊓ M.commutant = ⊥`, `U` is a nontrivial closed
subspace, and `U.starProjection ∈ M.commutant`, then `M.compressionStarAlgHom U hp` is injective. -/
theorem compressionStarAlgHom_injective {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    (U : Submodule ℂ H) [CompleteSpace U] [Nontrivial U] (hp : U.starProjection ∈ M.commutant) :
    Function.Injective (M.compressionStarAlgHom U hp) := by
  refine injective_iff_map_eq_zero _ |>.mpr fun x hx ↦ ?_
  rw [compressionStarAlgHom_apply] at hx
  have hp0 : U.starProjection ≠ 0 := U.starProjection_ne_zero_iff.mpr ‹_›
  have hprod : (x : H →L[ℂ] H) * U.starProjection = 0 := by
    have hpx : Commute U.starProjection (x : H →L[ℂ] H) :=
      (mem_commutant_iff.mp hp x x.property).symm
    have hce := U.extendByZero_compression_subtypeL (x : H →L[ℂ] H)
    rw [hx, map_zero, hpx.eq, mul_assoc, U.isIdempotentElem_starProjection.eq] at hce
    exact hce.symm
  exact Subtype.ext
    ((eq_zero_or_eq_zero_of_mul_eq_zero_of_mem_commutant hM x.property hp hprod).resolve_right hp0)

/-- When `M ⊓ M.commutant = ⊥`, `U` is nontrivial, and `U.starProjection ∈ M.commutant`, compression
gives a unital `⋆`-algebra isomorphism `M ≃⋆ₐ[ℂ] M.corner U (.inr hp)`. -/
noncomputable def cornerStarAlgEquiv {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    (U : Submodule ℂ H) [CompleteSpace U] [Nontrivial U] (hp : U.starProjection ∈ M.commutant) :
    M.toStarSubalgebra ≃⋆ₐ[ℂ] (M.corner U (.inr hp)).toStarSubalgebra :=
  (StarAlgEquiv.ofInjective (M.compressionStarAlgHom U hp)
    (compressionStarAlgHom_injective hM U hp)).trans
    (StarSubalgebra.equivOfEq _ _ (M.compressionStarAlgHom_range U hp))

/-- `cornerStarAlgEquiv` acts by compressing along `U.subtypeL`. -/
@[simp]
theorem coe_cornerStarAlgEquiv_apply {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    (U : Submodule ℂ H) [CompleteSpace U] [Nontrivial U] (hp : U.starProjection ∈ M.commutant)
    (x : M.toStarSubalgebra) :
    (cornerStarAlgEquiv hM U hp x : U →L[ℂ] U) = (x : H →L[ℂ] H).compression U.subtypeL := by
  rw [cornerStarAlgEquiv, StarAlgEquiv.trans_apply, StarSubalgebra.equivOfEq_apply,
    Subtype.coe_mk, StarAlgEquiv.ofInjective_apply, StarAlgHom.coe_rangeRestrict,
    compressionStarAlgHom_apply]

/-- **Commutant restriction isomorphism for factor corners.** If `M ⊓ M.commutant = ⊥` and `U` is a
nontrivial closed subspace with `U.starProjection ∈ M`, then compression along `U.subtypeL` gives a
unital `⋆`-algebra isomorphism `M.commutant ≃⋆ₐ[ℂ] (M.corner U (.inl hp)).commutant` (whose forward
compression map `M.commutant.compressionStarAlgHom` into `U →L[ℂ] U` is ultraweakly and
WOT-continuous by `continuous_ultraweak_compressionStarAlgHom` and
`continuous_wot_compressionStarAlgHom`). -/
noncomputable def commutantCornerStarAlgEquiv {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    (U : Submodule ℂ H) [CompleteSpace U] [Nontrivial U] (hp : U.starProjection ∈ M) :
    M.commutant.toStarSubalgebra ≃⋆ₐ[ℂ] (M.corner U (.inl hp)).commutant.toStarSubalgebra :=
  (cornerStarAlgEquiv (M := M.commutant) (by rw [M.commutant_commutant, inf_comm, hM]) U
    (M.commutant_commutant.symm ▸ hp)).trans
    (StarSubalgebra.equivOfEq _ _
      (congrArg toStarSubalgebra (commutant_corner M U (.inl hp)).symm))

/-- `commutantCornerStarAlgEquiv` acts by compressing along `U.subtypeL`. -/
@[simp]
theorem coe_commutantCornerStarAlgEquiv_apply {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    (U : Submodule ℂ H) [CompleteSpace U] [Nontrivial U] (hp : U.starProjection ∈ M)
    (y : M.commutant.toStarSubalgebra) :
    (commutantCornerStarAlgEquiv hM U hp y : U →L[ℂ] U) =
      (y : H →L[ℂ] H).compression U.subtypeL := by
  rw [commutantCornerStarAlgEquiv, StarAlgEquiv.trans_apply, StarSubalgebra.equivOfEq_apply,
    Subtype.coe_mk, coe_cornerStarAlgEquiv_apply]

/-! ### Generating sets of corners -/

/-- When `U.starProjection ∈ (adjoin s).commutant`, the compressed set
`(·.compression U.subtypeL) '' s` generates `(adjoin s).corner U (.inr hp)` with no algebraic
closure assumptions on `s`. -/
theorem adjoin_image_compression_of_mem_commutant {s : Set (H →L[ℂ] H)} {U : Submodule ℂ H}
    [CompleteSpace U] (hp : U.starProjection ∈ (adjoin s).commutant) :
    adjoin ((·.compression U.subtypeL) '' s) = (adjoin s).corner U (.inr hp) := by
  apply commutant_involutive.injective
  rw [commutant_corner]
  apply SetLike.coe_injective
  have hp' : U.starProjection ∈ (s ∪ star s).centralizer := coe_commutant_adjoin s ▸ hp
  ext T
  rw [coe_commutant_adjoin, star_image_compression, ← Set.image_union,
    U.mem_centralizer_image_compression_subtypeL_iff_of_commute (fun y hy ↦ (hp' y hy).symm),
    ← coe_commutant_adjoin, SetLike.mem_coe, SetLike.mem_coe,
    mem_corner_iff_extendByZero_mem (by simpa using hp)]

/-- **Generating sets of spatial corners.** If `s` is closed under adjoints and multiplication and
`U.starProjection` lies in `adjoin s` or in `(adjoin s).commutant`, then the compressed set
`(·.compression U.subtypeL) '' s` generates `(adjoin s).corner U hU`.

Multiplicative closure cannot be dropped when `U.starProjection ∈ adjoin s`; see
`TauCeti.Examples.Analysis.VonNeumannAlgebra.CornerAdjoin`. -/
theorem adjoin_image_compression_of_mul_mem {s : Set (H →L[ℂ] H)} (hstar : star s ⊆ s)
    (hmul : ∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) {U : Submodule ℂ H} [CompleteSpace U]
    (hU : U.starProjection ∈ adjoin s ∨ U.starProjection ∈ (adjoin s).commutant) :
    adjoin ((·.compression U.subtypeL) '' s) = (adjoin s).corner U hU := by
  let W : VonNeumannAlgebra U := adjoin ((·.compression U.subtypeL) '' s)
  refine le_antisymm (adjoin_le_iff.mpr fun _ ⟨x, hx, hTx⟩ ↦
    hTx ▸ compression_mem_corner hU (subset_adjoin s hx)) fun T hT ↦ ?_
  obtain ⟨x, hx, rfl⟩ := mem_corner_iff.mp hT
  have hx_cl : ContinuousLinearMapWOT.ofCLM x ∈
      closure (ContinuousLinearMapWOT.ofCLM '' (StarAlgebra.adjoin ℂ s : Set (H →L[ℂ] H))) :=
    image_ofCLM_adjoin_eq_closure s ▸ ⟨x, hx, rfl⟩
  let f : (H →WOT[ℂ] H) → (U →WOT[ℂ] U) :=
    fun A ↦ ContinuousLinearMapWOT.ofCLM (A.toCLM.compression U.subtypeL)
  have hclosed : IsClosed (f ⁻¹' (ContinuousLinearMapWOT.ofCLM '' (W : Set (U →L[ℂ] U)))) :=
    W.isClosed_image_ofCLM.preimage (ContinuousLinearMapWOT.continuous_compression U.subtypeL)
  have hspan : (StarAlgebra.adjoin ℂ s : Set (H →L[ℂ] H)) =
      (Submodule.span ℂ (insert 1 s) : Set (H →L[ℂ] H)) :=
    congrArg SetLike.coe (StarAlgebra.adjoin_eq_span_of_mul_mem hstar hmul)
  have hsub : ContinuousLinearMapWOT.ofCLM '' (StarAlgebra.adjoin ℂ s : Set (H →L[ℂ] H)) ⊆
      f ⁻¹' (ContinuousLinearMapWOT.ofCLM '' (W : Set (U →L[ℂ] U))) := by
    rw [hspan]
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y.compression U.subtypeL, ?_, rfl⟩
    induction hy using Submodule.span_induction with
    | mem a ha =>
      exact ha.elim (fun h ↦ h ▸ compression_one_subtypeL U ▸ W.one_mem)
        (fun ha ↦ subset_adjoin _ ⟨a, ha, rfl⟩)
    | zero => simp
    | add _ _ _ _ iha ihb => rw [SetLike.mem_coe, compression_add]; exact W.add_mem iha ihb
    | smul c _ _ iha => rw [SetLike.mem_coe, compression_smul]; exact SMulMemClass.smul_mem c iha
  obtain ⟨T, hTW, hTf⟩ := closure_minimal hsub hclosed hx_cl
  have hTx : T = x.compression U.subtypeL := ContinuousLinearMapWOT.ofCLM_injective hTf
  exact hTx ▸ hTW

end VonNeumannAlgebra

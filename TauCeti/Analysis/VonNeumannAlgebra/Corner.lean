/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.Compression
public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import TauCeti.Analysis.InnerProductSpace.UltraweakTopology
public import TauCeti.Analysis.InnerProductSpace.WeakOperatorTopology
public import TauCeti.Analysis.VonNeumannAlgebra.AlgebraicTensor
public import TauCeti.Analysis.VonNeumannAlgebra.Bicommutant

import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Algebra.Star.Subalgebra
import TauCeti.Analysis.InnerProductSpace.Amplification
import TauCeti.Analysis.InnerProductSpace.Modulus
import TauCeti.Analysis.InnerProductSpace.Projection.Basic

/-!
# Spatial corners and reduced von Neumann algebras

For a concrete von Neumann algebra `M` on a complex Hilbert space `H` and a closed subspace `U` of
`H` with orthogonal projection `p = U.starProjection`, if either `p ∈ M` (compression to a
projection in `M`, often written `pMp`) or `p ∈ M.commutant` (induction to a reducing subspace of
`M`, often written `Mp`), the compressions `x.compression U.subtypeL : U →L[ℂ] U` of operators
`x ∈ M` form a von Neumann algebra `M.corner U hU : VonNeumannAlgebra U` on `U`, and taking
commutants commutes with passing to the corner (`VonNeumannAlgebra.commutant_corner`,
`(pMp)' = pM'p`).

## Main declarations and results

* **Reducing-subspace correspondence:** `VonNeumannAlgebra.starProjection_mem_iff_isReducing` and
  `VonNeumannAlgebra.starProjection_mem_commutant_iff_isReducing` identify projections in `M` and
  in `M.commutant` with closed subspaces reducing `M.commutant` and `M`, respectively.
* `VonNeumannAlgebra.corner`: the spatial corner / reduced von Neumann algebra `M.corner U hU` on
  `U` for `hU : U.starProjection ∈ M ∨ U.starProjection ∈ M.commutant`, with underlying set
  `(·.compression U.subtypeL) '' (M : Set (H →L[ℂ] H))`.
* `VonNeumannAlgebra.commutant_corner`: `(M.corner U hU).commutant = M.commutant.corner U _`,
  proved via finite amplification and the operator modulus (`ContinuousLinearMap.modulus`).
* `VonNeumannAlgebra.corner_inf_commutant` and `VonNeumannAlgebra.corner_inf_commutant_eq_bot`:
  `(M.corner U hU) ⊓ (M.corner U hU).commutant = (M ⊓ M.commutant).corner U _`; in particular,
  corners of factors are factors.
* `VonNeumannAlgebra.compressionStarAlgHom`, `VonNeumannAlgebra.cornerStarAlgEquiv`, and
  `VonNeumannAlgebra.commutantCornerStarAlgEquiv`: when `U.starProjection ∈ M.commutant`,
  compression to `U` is an ultraweakly and WOT-continuous unital `⋆`-homomorphism onto
  `M.corner U (.inr hp)`, which is injective whenever `M ⊓ M.commutant = ⊥` and `Nontrivial U`.
  Dually, when `M ⊓ M.commutant = ⊥`, `U.starProjection ∈ M`, and `Nontrivial U`, restriction from
  `M.commutant` to `(M.corner U (.inl hp)).commutant` is a faithful ultraweakly continuous unital
  `⋆`-isomorphism.
* `VonNeumannAlgebra.adjoin_image_compression_of_mem_commutant` and
  `VonNeumannAlgebra.adjoin_image_compression`: generating sets of corners. When `s` is self-adjoint
  and multiplicatively closed and
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

/-! ### Reducing-subspace correspondence -/

section Reducing

/-- The orthogonal projection onto `U` lies in `M` if and only if `U` is invariant under every
operator in `M.commutant`. -/
theorem starProjection_mem_iff_mem_invtSubmodule {M : VonNeumannAlgebra H}
    (U : Submodule ℂ H) [U.HasOrthogonalProjection] :
    U.starProjection ∈ M ↔
      ∀ y ∈ M.commutant, U ∈ Module.End.invtSubmodule (y : Module.End ℂ H) := by
  simpa [U.range_starProjection] using
    IsStarProjection.mem_iff (isStarProjection_starProjection (U := U)) M

/-- **Reducing-subspace correspondence (`M`).** The orthogonal projection onto `U` lies in `M` if
and only if `U` reduces every operator in `M.commutant`. -/
theorem starProjection_mem_iff_isReducing {M : VonNeumannAlgebra H}
    (U : Submodule ℂ H) [U.HasOrthogonalProjection] :
    U.starProjection ∈ M ↔ ∀ y ∈ M.commutant, U.IsReducing (y : Module.End ℂ H) := by
  simp_rw [U.isReducing_coe_iff_commute_starProjection,
    Commute.symm_iff (a := U.starProjection), commute_iff_eq]
  rw [← mem_commutant_iff, M.commutant_commutant]

/-- The orthogonal projection onto `U` lies in `M.commutant` if and only if `U` is invariant under
every operator in `M`. -/
theorem starProjection_mem_commutant_iff_mem_invtSubmodule {M : VonNeumannAlgebra H}
    (U : Submodule ℂ H) [U.HasOrthogonalProjection] :
    U.starProjection ∈ M.commutant ↔
      ∀ x ∈ M, U ∈ Module.End.invtSubmodule (x : Module.End ℂ H) := by
  simpa using starProjection_mem_iff_mem_invtSubmodule (M := M.commutant) U

/-- **Reducing-subspace correspondence (`M'`).** The orthogonal projection onto `U` lies in
`M.commutant` if and only if `U` reduces every operator in `M`. -/
theorem starProjection_mem_commutant_iff_isReducing {M : VonNeumannAlgebra H}
    (U : Submodule ℂ H) [U.HasOrthogonalProjection] :
    U.starProjection ∈ M.commutant ↔ ∀ x ∈ M, U.IsReducing (x : Module.End ℂ H) := by
  simpa using starProjection_mem_iff_isReducing (M := M.commutant) U

/-- Projections onto orthogonal complements belong to `M` simultaneously. -/
@[simp]
theorem starProjection_orthogonal_mem_iff {M : VonNeumannAlgebra H}
    (U : Submodule ℂ H) [U.HasOrthogonalProjection] :
    Uᗮ.starProjection ∈ M ↔ U.starProjection ∈ M := by
  simp_rw [starProjection_mem_iff_isReducing, U.isReducing_orthogonal_iff]

end Reducing

/-! ### Private commutant-induction helpers -/

section Private

/-- When `U.starProjection ∈ M`, an operator on `U` is the compression of an element of `M` if and
only if its extension by zero belongs to `M`. -/
private theorem mem_image_compression_iff_cornerEmbedding_mem {M : VonNeumannAlgebra H}
    {U : Submodule ℂ H} [CompleteSpace U] (hp : U.starProjection ∈ M) {T : U →L[ℂ] U} :
    T ∈ (·.compression U.subtypeL) '' (M : Set (H →L[ℂ] H)) ↔
      U.subtypeₗᵢ.cornerEmbedding T ∈ M := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [U.cornerEmbedding_subtype_compression]
    exact mul_mem (mul_mem hp hx) hp
  · intro hT
    refine ⟨U.subtypeₗᵢ.cornerEmbedding T, hT, ?_⟩
    simpa [U.subtypeₗᵢ_toContinuousLinearMap] using U.subtypeₗᵢ.compression_cornerEmbedding T

/-- When every operator in `s` commutes with `U.starProjection`, `T` commutes with the compressions
of `s` to `U` if and only if `U.subtypeₗᵢ.cornerEmbedding T` commutes with `s`. -/
private theorem mem_centralizer_image_compression_iff {s : Set (H →L[ℂ] H)}
    {U : Submodule ℂ H} [CompleteSpace U] (hs : ∀ y ∈ s, Commute U.starProjection y)
    {T : U →L[ℂ] U} :
    T ∈ ((·.compression U.subtypeL) '' s).centralizer ↔
      U.subtypeₗᵢ.cornerEmbedding T ∈ s.centralizer := by
  have hproj : U.subtypeₗᵢ.toContinuousLinearMap ∘L
      U.subtypeₗᵢ.toContinuousLinearMap.adjoint = U.starProjection := by
    rw [U.subtypeₗᵢ_toContinuousLinearMap, U.subtypeL_comp_adjoint_subtypeL]
  rw [Set.mem_centralizer_iff, Set.mem_centralizer_iff]
  constructor
  · intro hT y hy
    have hpy : Commute (U.subtypeₗᵢ.toContinuousLinearMap ∘L
        U.subtypeₗᵢ.toContinuousLinearMap.adjoint) y := hproj.symm ▸ hs y hy
    have hTy : Commute (y.compression U.subtypeₗᵢ.toContinuousLinearMap) T := by
      rw [U.subtypeₗᵢ_toContinuousLinearMap, commute_iff_eq]
      exact hT _ ⟨y, hy, rfl⟩
    exact ((U.subtypeₗᵢ.commute_cornerEmbedding_iff T hpy).mpr hTy).eq
  · rintro hT _ ⟨y, hy, rfl⟩
    have hpy : Commute (U.subtypeₗᵢ.toContinuousLinearMap ∘L
        U.subtypeₗᵢ.toContinuousLinearMap.adjoint) y := hproj.symm ▸ hs y hy
    have hcomm : Commute y (U.subtypeₗᵢ.cornerEmbedding T) := by
      rw [commute_iff_eq]
      exact hT y hy
    simpa [U.subtypeₗᵢ_toContinuousLinearMap, commute_iff_eq] using
      (U.subtypeₗᵢ.commute_cornerEmbedding_iff T hpy).mp hcomm

/-- Step A of Dixmier's corner theorem: when `U.starProjection ∈ M`, the centralizer of the
compressed commutant `(·.compression U.subtypeL) '' M.commutant` is the compressed algebra
`(·.compression U.subtypeL) '' M`. -/
private theorem centralizer_image_compression_commutant_of_mem {M : VonNeumannAlgebra H}
    {U : Submodule ℂ H} [CompleteSpace U] (hp : U.starProjection ∈ M) :
    ((·.compression U.subtypeL) '' (M.commutant : Set (H →L[ℂ] H))).centralizer =
      (·.compression U.subtypeL) '' (M : Set (H →L[ℂ] H)) := by
  ext T
  rw [mem_centralizer_image_compression_iff
      (fun y hy ↦ mem_commutant_iff.mp hy U.starProjection hp),
    ← coe_commutant, SetLike.mem_coe, M.commutant_commutant,
    mem_image_compression_iff_cornerEmbedding_mem hp]

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
    rw [hX_apply, Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · intro hj
      exact False.elim (hj (Finset.mem_univ j))
  -- Every matrix entry of `X† ∘L X` is a compression from `N.commutant`, so `X† ∘L X` commutes
  -- with the diagonal amplification `Sₙ`.
  let A : PiLp 2 (fun _ : Fin n ↦ U) →L[ℂ] PiLp 2 (fun _ : Fin n ↦ U) := X.adjoint ∘L X
  have hA_entry (i j : Fin n) :
      A.piLpEntry i j = (star (x i) * x j).compression U.subtypeL := by
    refine ContinuousLinearMap.ext fun w ↦ ext_inner_left ℂ fun v ↦ ?_
    have hsingle (ξ : PiLp 2 (fun _ : Fin n ↦ U)) : ⟪v, ξ i⟫_ℂ = ⟪PiLp.single 2 i v, ξ⟫_ℂ := by
      rw [PiLp.inner_apply, Finset.sum_eq_single i]
      · simp
      · intro k _ hki
        simp [hki]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    rw [piLpEntry_apply, hsingle, comp_apply, adjoint_inner_right, hX_single, hX_single,
      inner_compression_apply, mul_def, comp_apply, star_eq_adjoint, adjoint_inner_right,
      U.coe_subtypeL, Submodule.coe_subtype]
  let Sₙ := PiLp.diagStarAlgHom ℂ U (Fin n) S
  have hAS : Commute A Sₙ := by
    rw [Commute, SemiconjBy]
    refine ContinuousLinearMap.ext fun η ↦ PiLp.ext fun i ↦ ?_
    simp only [mul_apply_eq_comp]
    rw [apply_eq_sum_piLpEntry, PiLp.diagStarAlgHom_apply, apply_eq_sum_piLpEntry, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [PiLp.diagStarAlgHom_apply]
    have hcomm : A.piLpEntry i j * S = S * A.piLpEntry i j := by
      rw [hA_entry]
      exact Set.mem_centralizer_iff.mp hS _
        ⟨star (x i) * x j, mul_mem (star_mem (hx i)) (hx j), rfl⟩
    exact DFunLike.congr_fun hcomm (η j)
  -- Conclude from the modulus norm inequality for `X` and contractivity of `diagStarAlgHom`.
  let η : PiLp 2 (fun _ : Fin n ↦ U) := WithLp.toLp 2 u
  have hSₙ_η : X (Sₙ η) = ∑ i : Fin n, x i (S (u i)) := by
    rw [hX_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [PiLp.diagStarAlgHom_apply]
  calc
    ‖∑ i : Fin n, x i (S (u i))‖ = ‖X (Sₙ η)‖ := by rw [hSₙ_η]
    _ ≤ ‖Sₙ‖ * ‖X η‖ := X.norm_apply_comp_le_of_commute_adjoint_comp_self hAS η
    _ ≤ ‖S‖ * ‖X η‖ := mul_le_mul_of_nonneg_right (PiLp.norm_diagStarAlgHom_le S) (norm_nonneg _)
    _ = ‖S‖ * ‖∑ i : Fin n, x i (u i)‖ := by rw [hX_apply]

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
    commutantOrbitMap N U (Finsupp.mapDomain (fun x : N.commutant ↦ ⟨z * x, mul_mem hz x.2⟩) d) =
      z (commutantOrbitMap N U d) := by
  rw [commutantOrbitMap, Finsupp.lsum_apply, Finsupp.lsum_apply,
    Finsupp.sum_mapDomain_index (fun _ ↦ by simp) (fun _ _ _ ↦ by simp [map_add]),
    Finsupp.sum, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp [LinearMap.comp_apply]

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
  rw [DenseRange, dense_iff_closure_eq,
    Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have himg : Subtype.val '' Set.range (commutantOrbitCodRestrict N U) =
      (LinearMap.range (commutantOrbitMap N U) : Set H) := by
    ext v
    exact ⟨fun ⟨_, ⟨d, rfl⟩, hdv⟩ ↦ ⟨d, hdv⟩,
      fun ⟨d, hdv⟩ ↦ ⟨commutantOrbitCodRestrict N U d, ⟨d, rfl⟩, hdv⟩⟩
  rw [himg]
  ext w
  exact ⟨fun _ ↦ trivial, fun _ ↦ w.2⟩

private theorem starProjection_commutantOrbitClosure_mem (N : VonNeumannAlgebra H)
    (U : Submodule ℂ H) :
    (commutantOrbitClosure N U).starProjection ∈ N := by
  have hrange : LinearMap.range (commutantOrbitMap N U) =
      Submodule.span ℂ {w : H | ∃ x ∈ N.commutant, ∃ v ∈ (U : Set H), x v = w} := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨d, rfl⟩
      rw [commutantOrbitMap_apply]
      exact sum_mem fun x _ ↦ Submodule.subset_span ⟨x.1, x.2, d x, (d x).2, rfl⟩
    · rw [Submodule.span_le]
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
    have hΦ_fin : commutantOrbitMap N U d =
        ∑ k : Fin d.support.card, ((e k).1 : H →L[ℂ] H) (d (e k).1) := by
      rw [commutantOrbitMap_apply, ← Finset.sum_coe_sort d.support]
      exact (e.sum_comp fun x : d.support ↦ (x.1 : H →L[ℂ] H) (d x.1)).symm
    have hΨ_fin : commutantOrbitMap N U (d.mapRange S S.map_zero) =
        ∑ k : Fin d.support.card, ((e k).1 : H →L[ℂ] H) (S (d (e k).1)) := by
      rw [commutantOrbitMap_mapRange, ← Finset.sum_coe_sort d.support]
      exact (e.sum_comp fun x : d.support ↦ (x.1 : H →L[ℂ] H) (S (d x.1))).symm
    rw [← Submodule.norm_coe (fK d), ← Submodule.norm_coe (eK d)]
    simpa only [eK, fK, commutantOrbitCodRestrict, LinearMap.comp_apply,
      Finsupp.mapRange.linearMap_apply, ContinuousLinearMap.coe_coe, LinearMap.codRestrict_apply,
      hΨ_fin, hΦ_fin] using
      norm_sum_apply_le_of_mem_centralizer hS (fun k ↦ ((e k).1 : H →L[ℂ] H))
        (fun k ↦ (e k).1.2) (fun k ↦ d (e k).1)
  refine ⟨fK.extendOfNorm eK, fun d ↦ ?_⟩
  exact LinearMap.extendOfNorm_eq (denseRange_commutantOrbitCodRestrict N U) ⟨‖S‖, h_norm⟩ d

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
  have hKz : Commute (K.subtypeL ∘L K.subtypeL.adjoint) z := by
    rw [K.subtypeL_comp_adjoint_subtypeL]
    exact mem_commutant_iff.mp hz K.starProjection (starProjection_commutantOrbitClosure_mem N U)
  have hzK (q : K) : (z.compression K.subtypeL q : H) = z (q : H) := by
    simpa [K.coe_subtypeL] using
      DFunLike.congr_fun (comp_compression_of_commute K.subtypeₗᵢ.isometry hKz) q
  rw [Commute, SemiconjBy]
  refine ContinuousLinearMap.ext fun w ↦ ?_
  refine (denseRange_commutantOrbitCodRestrict N U).induction
    (fun v hv ↦ ?_) (isClosed_eq (by fun_prop) (by fun_prop)) w
  obtain ⟨d, rfl⟩ := hv
  apply Subtype.ext
  simp only [mul_apply_eq_comp]
  let mulDom : N.commutant → N.commutant := fun x ↦ ⟨z * x, mul_mem hz x.2⟩
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
    let y : H →L[ℂ] H := K.subtypeₗᵢ.cornerEmbedding Y
    have hyN : y ∈ N := by
      rw [← N.commutant_commutant, mem_commutant_iff]
      intro z hz
      have hKz : Commute (K.subtypeₗᵢ.toContinuousLinearMap ∘L
          K.subtypeₗᵢ.toContinuousLinearMap.adjoint) z := by
        rw [K.subtypeₗᵢ_toContinuousLinearMap, K.subtypeL_comp_adjoint_subtypeL]
        exact mem_commutant_iff.mp hz K.starProjection
          (starProjection_commutantOrbitClosure_mem N U)
      refine (K.subtypeₗᵢ.commute_cornerEmbedding_iff Y hKz).mpr ?_
      simpa [K.subtypeₗᵢ_toContinuousLinearMap] using
        commute_compression_of_forall_apply_commutantOrbitCodRestrict hY hz
    -- On `U ⊆ K` (`x = 1`), `y` agrees with `S`, so `y.compression U.subtypeL = S`.
    refine ⟨y, hyN, ?_⟩
    dsimp only
    refine ContinuousLinearMap.ext fun u ↦ ext_inner_left ℂ fun v ↦ ?_
    let d₀ : N.commutant →₀ U := Finsupp.single ⟨1, N.commutant.one_mem⟩ u
    have hΦ₀ : commutantOrbitMap N U d₀ = u := by simp [commutantOrbitMap, d₀]
    have hΨ₀ : commutantOrbitMap N U (d₀.mapRange S S.map_zero) = S u := by
      simp [commutantOrbitMap, d₀]
    have hyu : y u = S u := by
      have huK : (u : H) ∈ K := hΦ₀ ▸ (commutantOrbitCodRestrict N U d₀).2
      have heK₀ : K.subtypeL.adjoint (u : H) = commutantOrbitCodRestrict N U d₀ := by
        rw [K.adjoint_subtypeL]
        apply Subtype.ext
        rw [K.coe_orthogonalProjectionOnto_apply, K.starProjection_eq_self_iff.mpr huK,
          commutantOrbitCodRestrict, LinearMap.codRestrict_apply, hΦ₀]
      rw [LinearIsometry.cornerEmbedding_apply_apply, K.subtypeₗᵢ_toContinuousLinearMap,
        heK₀, hY, K.coe_subtypeₗᵢ, Submodule.coe_subtype, commutantOrbitCodRestrict,
        LinearMap.codRestrict_apply, hΨ₀]
    rw [inner_compression_apply, U.coe_subtypeL, Submodule.coe_subtype, hyu, Submodule.coe_inner]
  · -- Conversely, compressing any `y ∈ N` commutes with compressing `N.commutant` since `U`
    -- reduces `N`.
    rintro _ ⟨y, hy, rfl⟩
    rw [Set.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hpy : Commute (U.subtypeL ∘L U.subtypeL.adjoint) y := by
      rw [U.subtypeL_comp_adjoint_subtypeL]
      exact (mem_commutant_iff.mp hp y hy).symm
    have hxy : x * y = y * x := (mem_commutant_iff.mp hx y hy).symm
    rw [← compression_mul_of_commute_right x U.subtypeₗᵢ.isometry hpy, hxy,
      compression_mul_of_commute_left x U.subtypeₗᵢ.isometry hpy]

private theorem centralizer_image_compression_commutant {M : VonNeumannAlgebra H}
    {U : Submodule ℂ H} [CompleteSpace U]
    (hU : U.starProjection ∈ M ∨ U.starProjection ∈ M.commutant) :
    ((·.compression U.subtypeL) '' (M.commutant : Set (H →L[ℂ] H))).centralizer =
      (·.compression U.subtypeL) '' (M : Set (H →L[ℂ] H)) :=
  hU.elim centralizer_image_compression_commutant_of_mem
    centralizer_image_compression_commutant_of_mem_commutant

private theorem star_image_compression (S : VonNeumannAlgebra H) (U : Submodule ℂ H)
    [CompleteSpace U] :
    star ((·.compression U.subtypeL) '' (S : Set (H →L[ℂ] H))) ⊆
      (·.compression U.subtypeL) '' (S : Set (H →L[ℂ] H)) := by
  intro T hT
  obtain ⟨x, hx, hTx⟩ := Set.mem_star.mp hT
  refine ⟨star x, star_mem hx, ?_⟩
  dsimp only at hTx ⊢
  rw [compression_star, hTx, star_star]

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
      rw [coe_commutant_adjoin, Set.union_eq_left.2 (star_image_compression M.commutant U),
        centralizer_image_compression_commutant hU]

/-- The carrier set of `M.corner U hU` is the image of `M` under compression along `U.subtypeL`. -/
@[simp, norm_cast]
theorem coe_corner (M : VonNeumannAlgebra H) (U : Submodule ℂ H) [CompleteSpace U]
    (hU : U.starProjection ∈ M ∨ U.starProjection ∈ M.commutant) :
    (M.corner U hU : Set (U →L[ℂ] U)) = (·.compression U.subtypeL) '' (M : Set (H →L[ℂ] H)) :=
  coe_copy _ _ _

/-- An operator on `U` belongs to `M.corner U hU` if and only if it is the compression of an
operator in `M`. -/
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
and only if its extension by zero `U.subtypeₗᵢ.cornerEmbedding T` belongs to `M`. -/
theorem mem_corner_iff_cornerEmbedding_mem {M : VonNeumannAlgebra H} {U : Submodule ℂ H}
    [CompleteSpace U] (hp : U.starProjection ∈ M) {T : U →L[ℂ] U} :
    T ∈ M.corner U (.inl hp) ↔ U.subtypeₗᵢ.cornerEmbedding T ∈ M := by
  rw [← SetLike.mem_coe, coe_corner]
  exact mem_image_compression_iff_cornerEmbedding_mem hp

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
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, by rw [compression_smul, compression_one_subtypeL]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c • 1, ⟨c, rfl⟩, by rw [compression_smul, compression_one_subtypeL]⟩

/-- The corner of `⊤ = B(H)` on `U` is `⊤ = B(U)`. -/
@[simp]
theorem corner_top (U : Submodule ℂ H) [CompleteSpace U]
    (hU : U.starProjection ∈ (⊤ : VonNeumannAlgebra H) ∨
      U.starProjection ∈ (⊤ : VonNeumannAlgebra H).commutant) :
    (⊤ : VonNeumannAlgebra H).corner U hU = ⊤ := by
  apply SetLike.coe_injective
  rw [coe_corner, coe_top, coe_top]
  ext T
  simp only [Set.mem_image, Set.mem_univ, true_and, iff_true]
  refine ⟨U.subtypeₗᵢ.cornerEmbedding T, ?_⟩
  simpa [U.subtypeₗᵢ_toContinuousLinearMap] using U.subtypeₗᵢ.compression_cornerEmbedding T

/-- Passing to a corner on `U` is monotone in the von Neumann algebra. -/
theorem corner_mono {M N : VonNeumannAlgebra H} {U : Submodule ℂ H} [CompleteSpace U]
    {hM : U.starProjection ∈ M ∨ U.starProjection ∈ M.commutant}
    {hN : U.starProjection ∈ N ∨ U.starProjection ∈ N.commutant} (hMN : M ≤ N) :
    M.corner U hM ≤ N.corner U hN := by
  intro T hT
  obtain ⟨x, hx, rfl⟩ := mem_corner_iff.mp hT
  exact mem_corner_iff.mpr ⟨x, hMN hx, rfl⟩

/-- Auxiliary witness that `U.starProjection ∈ (M ⊓ M.commutant).commutant` whenever
`U.starProjection ∈ M ∨ U.starProjection ∈ M.commutant`. -/
theorem starProjection_mem_commutant_center {M : VonNeumannAlgebra H} {U : Submodule ℂ H}
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
  have hpb : Commute (U.subtypeL ∘L U.subtypeL.adjoint) b := by
    rw [U.subtypeL_comp_adjoint_subtypeL]
    exact mem_commutant_iff.mp hb U.starProjection hp
  have hpy : Commute (U.subtypeL ∘L U.subtypeL.adjoint) y := by
    rw [U.subtypeL_comp_adjoint_subtypeL]
    exact mem_commutant_iff.mp hy U.starProjection hp
  have hbyU := mul_comp_eq_of_commute_compression U.subtypeₗᵢ.isometry hpb hpy hcomm
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
      (M ⊓ M.commutant).corner U (.inr (starProjection_mem_commutant_center (.inl hp))) := by
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
        have hb_mem : b.compression U.subtypeL ∈ (M.corner U (.inl hp)).commutant := by
          rw [commutant_corner]
          exact compression_mem_corner _ hb
        rw [commute_iff_eq]
        exact (mem_commutant_iff.mp hb_mem _ hTM).symm
      have eqOnL := mul_eqOn_topologicalClosure_span_of_commute_compression hp hb hy hcomm_comp
      refine ContinuousLinearMap.ext fun ξ ↦ ?_
      have hb_z : (b * z) ξ = (b * y) (L.starProjection ξ) := by
        rw [hz_def, ← hyL, ← mul_assoc, mul_apply_eq_comp]
      have hz_b : (z * b) ξ = (y * b) (L.starProjection ξ) := by
        rw [hz_def, ← hyL, mul_assoc, ← hbL, ← mul_assoc, mul_apply_eq_comp]
      rw [hb_z, hz_b, eqOnL _ (L.starProjection_apply_mem ξ)]
    -- Since `U ⊆ L`, `z` and `y` have the same compression to `U`.
    rw [mem_corner_iff]
    refine ⟨z, mem_inf.mpr ⟨hzM, hzM'⟩, ?_⟩
    refine ContinuousLinearMap.ext fun u ↦ ext_inner_left ℂ fun v ↦ ?_
    have huL : (u : H) ∈ L := Submodule.le_topologicalClosure _
      (Submodule.subset_span ⟨1, M.one_mem, u, u.2, one_apply_eq_self _⟩)
    have hzu : z u = y u := by
      have hyL : L.starProjection * y = y * L.starProjection :=
        mem_commutant_iff.mp hy L.starProjection hL_M'
      rw [hz_def, hyL, mul_apply_eq_comp, L.starProjection_eq_self_iff.mpr huL]
    rw [inner_compression_apply, inner_compression_apply, U.coe_subtypeL, Submodule.coe_subtype,
      hzu]
  · refine le_inf (corner_mono inf_le_left) ?_
    rw [commutant_corner]
    exact corner_mono inf_le_right

/-- **The center of a corner is the corner of the center.** -/
theorem corner_inf_commutant (M : VonNeumannAlgebra H) (U : Submodule ℂ H) [CompleteSpace U]
    (hU : U.starProjection ∈ M ∨ U.starProjection ∈ M.commutant) :
    M.corner U hU ⊓ (M.corner U hU).commutant =
      (M ⊓ M.commutant).corner U (.inr (starProjection_mem_commutant_center hU)) := by
  rcases hU with hp | hp
  · exact corner_inf_commutant_of_mem hp
  · have h1 := corner_inf_commutant_of_mem (M := M.commutant) hp
    have hcomm : (M.corner U (.inr hp)).commutant = M.commutant.corner U (.inl hp) := by
      simpa using commutant_corner M U (.inr hp)
    have hcomm2 : (M.commutant.corner U (.inl hp)).commutant = M.corner U (.inr hp) := by
      rw [← hcomm, commutant_commutant]
    rw [hcomm2, inf_comm] at h1
    rw [hcomm, h1]
    apply SetLike.coe_injective
    simp [coe_corner, Set.inter_comm]

/-- **Corners of factors are factors:** if `M ⊓ M.commutant = ⊥`, then any corner `M.corner U hU`
also has trivial center `M.corner U hU ⊓ (M.corner U hU).commutant = ⊥`. -/
theorem corner_inf_commutant_eq_bot {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    (U : Submodule ℂ H) [CompleteSpace U]
    (hU : U.starProjection ∈ M ∨ U.starProjection ∈ M.commutant) :
    M.corner U hU ⊓ (M.corner U hU).commutant = ⊥ := by
  rw [corner_inf_commutant]
  exact (corner_congr (hN := .inr (by simp)) hM).trans (corner_bot U _)

/-! ### Induction `⋆`-homomorphisms and factor commutant restriction isomorphisms -/

/-- When `U.starProjection ∈ M.commutant`, compression along `U.subtypeL` defines a unital
`⋆`-algebra homomorphism `M →⋆ₐ[ℂ] (U →L[ℂ] U)` onto the reduced algebra `M.corner U (.inr hp)`. -/
noncomputable def compressionStarAlgHom (M : VonNeumannAlgebra H) (U : Submodule ℂ H)
    [CompleteSpace U] (hp : U.starProjection ∈ M.commutant) :
    M.toStarSubalgebra →⋆ₐ[ℂ] (U →L[ℂ] U) where
  toFun x := (x : H →L[ℂ] H).compression U.subtypeL
  map_one' := compression_one_subtypeL U
  map_mul' x y := by
    have hpx : Commute (U.subtypeL ∘L U.subtypeL.adjoint) (x : H →L[ℂ] H) := by
      rw [U.subtypeL_comp_adjoint_subtypeL]
      exact (mem_commutant_iff.mp hp x x.2).symm
    exact compression_mul_of_commute_left (y : H →L[ℂ] H) U.subtypeₗᵢ.isometry hpx
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

/-- The range of `M.compressionStarAlgHom U hp` is the reduced algebra `M.corner U (.inr hp)`. -/
@[simp]
theorem compressionStarAlgHom_range (M : VonNeumannAlgebra H) (U : Submodule ℂ H) [CompleteSpace U]
    (hp : U.starProjection ∈ M.commutant) :
    (M.compressionStarAlgHom U hp).range = (M.corner U (.inr hp)).toStarSubalgebra := by
  ext T
  rw [mem_carrier, SetLike.mem_coe, mem_corner_iff]
  exact ⟨fun ⟨x, hx⟩ ↦ ⟨x.1, x.2, by simpa using hx⟩,
    fun ⟨x, hx, hTx⟩ ↦ ⟨⟨x, hx⟩, by simpa using hTx⟩⟩

/-- `compressionStarAlgHom` is continuous with respect to the ultraweak operator topologies on `M`
and `U →L[ℂ] U`. -/
@[fun_prop]
theorem continuous_ultraweak_compressionStarAlgHom (M : VonNeumannAlgebra H) (U : Submodule ℂ H)
    [CompleteSpace U] (hp : U.starProjection ∈ M.commutant) :
    Continuous fun A : {A : ContinuousLinearMapUltraweak ℂ H H // A.toCLM ∈ M} ↦
      ContinuousLinearMapUltraweak.ofCLM (M.compressionStarAlgHom U hp ⟨A.1.toCLM, A.2⟩) :=
  (ContinuousLinearMapUltraweak.continuous_compression U.subtypeL).comp continuous_subtype_val

/-- `compressionStarAlgHom` is continuous with respect to the weak operator topologies on `M` and
`U →L[ℂ] U`. -/
@[fun_prop]
theorem continuous_wot_compressionStarAlgHom (M : VonNeumannAlgebra H) (U : Submodule ℂ H)
    [CompleteSpace U] (hp : U.starProjection ∈ M.commutant) :
    Continuous fun A : {A : H →WOT[ℂ] H // A.toCLM ∈ M} ↦
      ContinuousLinearMapWOT.ofCLM (M.compressionStarAlgHom U hp ⟨A.1.toCLM, A.2⟩) :=
  (ContinuousLinearMapWOT.continuous_compression U.subtypeL).comp continuous_subtype_val

/-- **Faithfulness of induction for factors.** If `M ⊓ M.commutant = ⊥`, `U` is a nontrivial closed
subspace, and `U.starProjection ∈ M.commutant`, then `M.compressionStarAlgHom U hp` is injective. -/
theorem compressionStarAlgHom_injective {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    (U : Submodule ℂ H) [CompleteSpace U] [Nontrivial U] (hp : U.starProjection ∈ M.commutant) :
    Function.Injective (M.compressionStarAlgHom U hp) := by
  refine injective_iff_map_eq_zero _ |>.mpr fun x hx ↦ ?_
  have hp0 : U.starProjection ≠ 0 := U.starProjection_ne_zero_iff.mpr ‹_›
  have hprod : (x : H →L[ℂ] H) * U.starProjection = 0 := by
    have hpx : Commute U.starProjection (x : H →L[ℂ] H) :=
      (mem_commutant_iff.mp hp x x.2).symm
    have hce := U.cornerEmbedding_subtype_compression (x : H →L[ℂ] H)
    rw [show (x : H →L[ℂ] H).compression U.subtypeL = 0 from hx, map_zero,
      hpx.eq, mul_assoc, U.isIdempotentElem_starProjection.eq] at hce
    exact hce.symm
  exact Subtype.ext
    ((eq_zero_or_eq_zero_of_mul_eq_zero_of_mem_commutant hM x.2 hp hprod).resolve_right hp0)

/-- When `M ⊓ M.commutant = ⊥`, `U` is nontrivial, and `U.starProjection ∈ M.commutant`, compression
gives a unital `⋆`-algebra isomorphism `M ≃⋆ₐ[ℂ] M.corner U (.inr hp)`. -/
noncomputable def cornerStarAlgEquiv {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    (U : Submodule ℂ H) [CompleteSpace U] [Nontrivial U] (hp : U.starProjection ∈ M.commutant) :
    M.toStarSubalgebra ≃⋆ₐ[ℂ] (M.corner U (.inr hp)).toStarSubalgebra :=
  let φ := (M.compressionStarAlgHom U hp).codRestrict (M.corner U (.inr hp)).toStarSubalgebra
    fun x ↦ by
      rw [mem_carrier, SetLike.mem_coe, compressionStarAlgHom_apply]
      exact compression_mem_corner (.inr hp) x.2
  StarAlgEquiv.ofBijective φ
    (⟨(StarAlgHom.injective_codRestrict _ _ _).mpr (compressionStarAlgHom_injective hM U hp),
      fun ⟨T, hT⟩ ↦ by
        rw [mem_carrier, SetLike.mem_coe, mem_corner_iff] at hT
        obtain ⟨x, hx, hTx⟩ := hT
        exact ⟨⟨x, hx⟩, Subtype.ext (by simpa [φ] using hTx)⟩⟩ : Function.Bijective φ)

/-- `cornerStarAlgEquiv` acts by compressing along `U.subtypeL`. -/
@[simp]
theorem coe_cornerStarAlgEquiv_apply {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    (U : Submodule ℂ H) [CompleteSpace U] [Nontrivial U] (hp : U.starProjection ∈ M.commutant)
    (x : M.toStarSubalgebra) :
    (cornerStarAlgEquiv hM U hp x : U →L[ℂ] U) = (x : H →L[ℂ] H).compression U.subtypeL := by
  rw [cornerStarAlgEquiv]
  exact (congrArg Subtype.val (StarAlgEquiv.ofBijective_apply _ x)).trans (by simp)

/-- **Commutant restriction isomorphism for factor corners.** If `M ⊓ M.commutant = ⊥` and `U` is a
nontrivial closed subspace with `U.starProjection ∈ M`, then compression along `U.subtypeL` gives a
faithful (and ultraweakly continuous, by `continuous_ultraweak_compressionStarAlgHom`) unital
`⋆`-algebra isomorphism from `M.commutant` onto `(M.corner U (.inl hp)).commutant`. -/
noncomputable def commutantCornerStarAlgEquiv {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    (U : Submodule ℂ H) [CompleteSpace U] [Nontrivial U] (hp : U.starProjection ∈ M) :
    M.commutant.toStarSubalgebra ≃⋆ₐ[ℂ] (M.corner U (.inl hp)).commutant.toStarSubalgebra :=
  have hM' : M.commutant ⊓ M.commutant.commutant = ⊥ := by
    rw [M.commutant_commutant, inf_comm, hM]
  have hp' : U.starProjection ∈ M.commutant.commutant := M.commutant_commutant.symm ▸ hp
  have hmem (y : M.commutant.toStarSubalgebra) :
      M.commutant.compressionStarAlgHom U hp' y ∈
        (M.corner U (.inl hp)).commutant.toStarSubalgebra := by
    rw [mem_carrier, SetLike.mem_coe, commutant_corner, compressionStarAlgHom_apply]
    exact compression_mem_corner _ y.2
  let φ := (M.commutant.compressionStarAlgHom U hp').codRestrict
    (M.corner U (.inl hp)).commutant.toStarSubalgebra hmem
  StarAlgEquiv.ofBijective φ
    (⟨(StarAlgHom.injective_codRestrict _ _ _).mpr (compressionStarAlgHom_injective hM' U hp'),
      fun ⟨T, hT⟩ ↦ by
        rw [mem_carrier, SetLike.mem_coe, commutant_corner, mem_corner_iff] at hT
        obtain ⟨y, hy, hTy⟩ := hT
        exact ⟨⟨y, hy⟩, Subtype.ext (by simpa [φ] using hTy)⟩⟩ : Function.Bijective φ)

/-- `commutantCornerStarAlgEquiv` acts by compressing along `U.subtypeL`. -/
@[simp]
theorem coe_commutantCornerStarAlgEquiv_apply {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    (U : Submodule ℂ H) [CompleteSpace U] [Nontrivial U] (hp : U.starProjection ∈ M)
    (y : M.commutant.toStarSubalgebra) :
    (commutantCornerStarAlgEquiv hM U hp y : U →L[ℂ] U) =
      (y : H →L[ℂ] H).compression U.subtypeL := by
  rw [commutantCornerStarAlgEquiv]
  exact (congrArg Subtype.val (StarAlgEquiv.ofBijective_apply _ y)).trans (by simp)

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
  have himg : ((·.compression U.subtypeL) '' s) ∪ star ((·.compression U.subtypeL) '' s) =
      (·.compression U.subtypeL) '' (s ∪ star s) := by
    ext A
    simp only [Set.mem_union, Set.mem_image, Set.mem_star]
    constructor
    · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, hyA⟩)
      · exact ⟨y, Or.inl hy, rfl⟩
      · refine ⟨star y, Or.inr (by rwa [star_star]), ?_⟩
        rw [compression_star, hyA, star_star]
    · rintro ⟨y, hy | hy, rfl⟩
      · exact Or.inl ⟨y, hy, rfl⟩
      · exact Or.inr ⟨star y, hy, compression_star y U.subtypeL⟩
  have hsub : s ∪ star s ⊆ adjoin s :=
    Set.union_subset (subset_adjoin s) fun y hy ↦ by
      rw [SetLike.mem_coe, ← star_star y]
      exact star_mem (subset_adjoin s (Set.mem_star.mp hy))
  ext T
  rw [coe_commutant_adjoin, himg,
    mem_centralizer_image_compression_iff
      (fun y hy ↦ (mem_commutant_iff.mp hp y (hsub hy)).symm),
    ← coe_commutant_adjoin, SetLike.mem_coe, SetLike.mem_coe,
    mem_corner_iff_cornerEmbedding_mem (by simpa using hp)]

/-- **Generating sets of spatial corners.** If `s` is closed under adjoints and multiplication and
`U.starProjection` lies in `adjoin s` or in `(adjoin s).commutant`, then the compressed set
`(·.compression U.subtypeL) '' s` generates `(adjoin s).corner U hU`.

Multiplicative closure cannot be dropped when `U.starProjection ∈ adjoin s`; see
`TauCeti.Examples.Analysis.VonNeumannAlgebra.CornerAdjoin`. -/
theorem adjoin_image_compression {s : Set (H →L[ℂ] H)} (hstar : star s ⊆ s)
    (hmul : ∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) {U : Submodule ℂ H} [CompleteSpace U]
    (hU : U.starProjection ∈ adjoin s ∨ U.starProjection ∈ (adjoin s).commutant) :
    adjoin ((·.compression U.subtypeL) '' s) = (adjoin s).corner U hU := by
  let W : VonNeumannAlgebra U := adjoin ((·.compression U.subtypeL) '' s)
  refine le_antisymm (adjoin_le_iff.mpr ?_) ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact compression_mem_corner hU (subset_adjoin s hx)
  · intro T hT
    obtain ⟨x, hx, rfl⟩ := mem_corner_iff.mp hT
    have hx_cl : ContinuousLinearMapWOT.ofCLM x ∈
        closure (ContinuousLinearMapWOT.ofCLM '' (StarAlgebra.adjoin ℂ s : Set (H →L[ℂ] H))) := by
      rw [← image_ofCLM_adjoin_eq_closure]
      exact ⟨x, hx, rfl⟩
    let f : (H →WOT[ℂ] H) → (U →WOT[ℂ] U) :=
      fun A ↦ ContinuousLinearMapWOT.ofCLM (A.toCLM.compression U.subtypeL)
    have hf : Continuous f := ContinuousLinearMapWOT.continuous_compression U.subtypeL
    have hclosed : IsClosed (f ⁻¹' (ContinuousLinearMapWOT.ofCLM '' (W : Set (U →L[ℂ] U)))) :=
      W.isClosed_image_ofCLM.preimage hf
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
        rcases ha with rfl | ha
        · rw [compression_one_subtypeL]
          exact W.one_mem
        · exact subset_adjoin _ ⟨a, ha, rfl⟩
      | zero =>
        rw [compression_zero]
        exact W.zero_mem
      | add a b _ _ iha ihb =>
        rw [compression_add]
        exact W.add_mem iha ihb
      | smul c a _ iha =>
        rw [compression_smul]
        exact SMulMemClass.smul_mem c iha
    obtain ⟨T, hTW, hTf⟩ := closure_minimal hsub hclosed hx_cl
    have hTx : T = x.compression U.subtypeL := ContinuousLinearMapWOT.ofCLM_injective hTf
    exact hTx ▸ hTW

end VonNeumannAlgebra

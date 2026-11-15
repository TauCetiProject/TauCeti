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

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import TauCeti.Algebra.Star.Subalgebra
import TauCeti.Analysis.InnerProductSpace.Amplification

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
  proved via finite amplification and positive operator square roots (`CFC.sqrt`).
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

open scoped InnerProductSpace Pointwise NNReal
open ContinuousLinearMap TauCeti

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Reducing-subspace correspondence and projection helpers -/

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

omit [CompleteSpace H] in
/-- The orthogonal projection onto `U` is nonzero if and only if `U` is nontrivial. -/
theorem starProjection_ne_zero_iff (U : Submodule ℂ H) [U.HasOrthogonalProjection] :
    U.starProjection ≠ 0 ↔ Nontrivial U := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ : ∃ x : H, U.starProjection x ≠ 0 := by
      by_contra! hall
      exact h (ContinuousLinearMap.ext hall)
    exact nontrivial_of_ne ⟨U.starProjection x, U.starProjection_apply_mem x⟩ 0
      (Subtype.coe_ne_coe.mp hx)
  · intro _
    obtain ⟨u, hu⟩ := exists_ne (0 : U)
    intro h0
    apply hu
    apply Subtype.ext
    have hu' : U.starProjection (u : H) = u := U.starProjection_eq_self_iff.mpr u.2
    simpa [h0] using hu'.symm

/-- Compressing `x` along `U.subtypeL` is `U.orthogonalProjectionOnto ∘L x ∘L U.subtypeL`. -/
theorem compression_subtypeL_eq (U : Submodule ℂ H) [CompleteSpace U] (x : H →L[ℂ] H) :
    x.compression U.subtypeL = U.orthogonalProjectionOnto ∘L x ∘L U.subtypeL := by
  rw [compression_def, U.adjoint_subtypeL]

end Reducing

/-! ### Private corner-embedding and commutant-induction lemmas -/

section Private

private theorem subtypeL_comp_adjoint_subtypeL (U : Submodule ℂ H) [CompleteSpace U] :
    U.subtypeL ∘L U.subtypeL.adjoint = U.starProjection := by
  rw [U.adjoint_subtypeL]
  rfl

private theorem cornerEmbedding_subtype_compression (U : Submodule ℂ H) [CompleteSpace U]
    (x : H →L[ℂ] H) :
    U.subtypeₗᵢ.cornerEmbedding (x.compression U.subtypeL) =
      U.starProjection * x * U.starProjection := by
  have h := U.subtypeₗᵢ.cornerEmbedding_compression x
  rw [U.subtypeₗᵢ_toContinuousLinearMap, subtypeL_comp_adjoint_subtypeL] at h
  rw [h, compression_def, (isSelfAdjoint_starProjection U).adjoint_eq]
  rfl

private theorem subtypeL_comp_compression_of_commute {U : Submodule ℂ H} [CompleteSpace U]
    {y : H →L[ℂ] H} (hy : Commute U.starProjection y) :
    U.subtypeL ∘L y.compression U.subtypeL = y ∘L U.subtypeL := by
  calc
    U.subtypeL ∘L y.compression U.subtypeL
        = (U.subtypeL ∘L U.subtypeL.adjoint) ∘L y ∘L U.subtypeL := by
          simp only [compression_def, comp_assoc]
    _ = (U.starProjection * y) ∘L U.subtypeL := by
          rw [subtypeL_comp_adjoint_subtypeL]; rfl
    _ = (y * U.starProjection) ∘L U.subtypeL := by rw [hy.eq]
    _ = y ∘L (U.starProjection ∘L U.subtypeL) := rfl
    _ = y ∘L U.subtypeL := by
          congr 1
          ext u
          exact U.starProjection_eq_self_iff.mpr u.2

private theorem compression_comp_adjoint_subtypeL_of_commute {U : Submodule ℂ H} [CompleteSpace U]
    {y : H →L[ℂ] H} (hy : Commute U.starProjection y) :
    y.compression U.subtypeL ∘L U.subtypeL.adjoint = U.subtypeL.adjoint ∘L y := by
  have h1 : U.subtypeL.adjoint ∘L U.starProjection = U.subtypeL.adjoint := by
    rw [← subtypeL_comp_adjoint_subtypeL, ← comp_assoc]
    have hiso : U.subtypeL.adjoint ∘L U.subtypeL = ContinuousLinearMap.id ℂ U :=
      (isometry_iff_adjoint_comp_self U.subtypeL).mp U.subtypeₗᵢ.isometry
    rw [hiso, id_comp]
  calc
    y.compression U.subtypeL ∘L U.subtypeL.adjoint
        = U.subtypeL.adjoint ∘L (y * U.starProjection) := by
          rw [compression_def, comp_assoc, comp_assoc, subtypeL_comp_adjoint_subtypeL]; rfl
    _ = U.subtypeL.adjoint ∘L (U.starProjection * y) := by rw [hy.eq]
    _ = (U.subtypeL.adjoint ∘L U.starProjection) ∘L y := rfl
    _ = U.subtypeL.adjoint ∘L y := by rw [h1]

private theorem cornerEmbedding_mul_of_commute {U : Submodule ℂ H} [CompleteSpace U]
    (T : U →L[ℂ] U) {y : H →L[ℂ] H} (hy : Commute U.starProjection y) :
    U.subtypeₗᵢ.cornerEmbedding T * y =
      U.subtypeₗᵢ.cornerEmbedding (T * y.compression U.subtypeL) := by
  calc
    U.subtypeₗᵢ.cornerEmbedding T * y
        = U.subtypeL ∘L T ∘L (U.subtypeL.adjoint ∘L y) := by
          rw [mul_def, LinearIsometry.cornerEmbedding_apply, U.subtypeₗᵢ_toContinuousLinearMap,
            compression_def, adjoint_adjoint]
          simp only [comp_assoc]
    _ = U.subtypeL ∘L T ∘L (y.compression U.subtypeL ∘L U.subtypeL.adjoint) := by
          rw [compression_comp_adjoint_subtypeL_of_commute hy]
    _ = U.subtypeₗᵢ.cornerEmbedding (T * y.compression U.subtypeL) := by
          simp only [LinearIsometry.cornerEmbedding_apply, U.subtypeₗᵢ_toContinuousLinearMap,
            compression_def, adjoint_adjoint, mul_def, comp_assoc]

private theorem mul_cornerEmbedding_of_commute {U : Submodule ℂ H} [CompleteSpace U]
    (T : U →L[ℂ] U) {y : H →L[ℂ] H} (hy : Commute U.starProjection y) :
    y * U.subtypeₗᵢ.cornerEmbedding T =
      U.subtypeₗᵢ.cornerEmbedding (y.compression U.subtypeL * T) := by
  calc
    y * U.subtypeₗᵢ.cornerEmbedding T
        = (y ∘L U.subtypeL) ∘L T ∘L U.subtypeL.adjoint := by
          rw [mul_def, LinearIsometry.cornerEmbedding_apply, U.subtypeₗᵢ_toContinuousLinearMap,
            compression_def, adjoint_adjoint]
          simp only [comp_assoc]
    _ = (U.subtypeL ∘L y.compression U.subtypeL) ∘L T ∘L U.subtypeL.adjoint := by
          rw [subtypeL_comp_compression_of_commute hy]
    _ = U.subtypeₗᵢ.cornerEmbedding (y.compression U.subtypeL * T) := by
          simp only [LinearIsometry.cornerEmbedding_apply, U.subtypeₗᵢ_toContinuousLinearMap,
            compression_def, adjoint_adjoint, mul_def, comp_assoc]

private theorem commute_cornerEmbedding_iff {U : Submodule ℂ H} [CompleteSpace U]
    (T : U →L[ℂ] U) {y : H →L[ℂ] H} (hy : Commute U.starProjection y) :
    Commute y (U.subtypeₗᵢ.cornerEmbedding T) ↔ Commute (y.compression U.subtypeL) T := by
  rw [Commute, SemiconjBy, mul_cornerEmbedding_of_commute T hy,
    cornerEmbedding_mul_of_commute T hy, U.subtypeₗᵢ.cornerEmbedding.injective.eq_iff]
  rfl

/-- Step A of Dixmier's corner theorem: when `U.starProjection ∈ M`, the centralizer of the
compressed commutant `(·.compression U.subtypeL) '' M.commutant` is the compressed algebra
`(·.compression U.subtypeL) '' M`. -/
private theorem centralizer_image_compression_commutant_of_mem {M : VonNeumannAlgebra H}
    {U : Submodule ℂ H} [CompleteSpace U] (hp : U.starProjection ∈ M) :
    ((·.compression U.subtypeL) '' (M.commutant : Set (H →L[ℂ] H))).centralizer =
      (·.compression U.subtypeL) '' (M : Set (H →L[ℂ] H)) := by
  ext T
  have hmem : T ∈ ((·.compression U.subtypeL) '' (M.commutant : Set (H →L[ℂ] H))).centralizer ↔
      U.subtypeₗᵢ.cornerEmbedding T ∈ M := by
    conv_rhs => rw [← M.commutant_commutant, mem_commutant_iff]
    rw [Set.mem_centralizer_iff]
    constructor
    · intro hT y hy
      have hpy : Commute U.starProjection y := mem_commutant_iff.mp hy U.starProjection hp
      exact (commute_cornerEmbedding_iff T hpy).mpr (hT _ ⟨y, hy, rfl⟩)
    · rintro hT _ ⟨y, hy, rfl⟩
      have hpy : Commute U.starProjection y := mem_commutant_iff.mp hy U.starProjection hp
      exact (commute_cornerEmbedding_iff T hpy).mp (hT y hy)
  rw [hmem]
  constructor
  · intro hTM
    refine ⟨U.subtypeₗᵢ.cornerEmbedding T, hTM, ?_⟩
    simpa [U.subtypeₗᵢ_toContinuousLinearMap] using U.subtypeₗᵢ.compression_cornerEmbedding T
  · rintro ⟨x, hx, rfl⟩
    rw [cornerEmbedding_subtype_compression]
    exact mul_mem (mul_mem hp hx) hp

/-- If `T : K →L[ℂ] K` commutes with `X.adjoint ∘L X`, then `T` commutes with `(X^* X)^{1/2}`, so
`‖X (T ξ)‖ ≤ ‖T‖ * ‖X ξ‖`. -/
private theorem norm_apply_comp_le_of_commute_adjoint_comp_self
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (X : K →L[ℂ] H) {T : K →L[ℂ] K} (hT : Commute (X.adjoint ∘L X) T) (ξ : K) :
    ‖X (T ξ)‖ ≤ ‖T‖ * ‖X ξ‖ := by
  let A : K →L[ℂ] K := X.adjoint ∘L X
  have hA : 0 ≤ A := nonneg_iff_isPositive.mpr (isPositive_adjoint_comp_self X)
  let B : K →L[ℂ] K := CFC.sqrt A
  have hBT : Commute B T := hT.cfcₙ_nnreal NNReal.sqrt
  have hB_sa : IsSelfAdjoint B := .of_nonneg (CFC.sqrt_nonneg A)
  have hBB : B.adjoint ∘L B = A := by
    rw [← star_eq_adjoint, hB_sa.star_eq, ← mul_def, CFC.sqrt_mul_sqrt_self A hA]
  have hnorm (η : K) : ‖B η‖ = ‖X η‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← inner_self_eq_norm_sq (𝕜 := ℂ),
      ← inner_self_eq_norm_sq (𝕜 := ℂ), ← adjoint_inner_right B, ← comp_apply B.adjoint B, hBB,
      comp_apply, adjoint_inner_right]
  calc
    ‖X (T ξ)‖ = ‖B (T ξ)‖ := (hnorm (T ξ)).symm
    _ = ‖T (B ξ)‖ := congrArg norm (DFunLike.congr_fun hBT.eq ξ)
    _ ≤ ‖T‖ * ‖B ξ‖ := T.le_opNorm (B ξ)
    _ = ‖T‖ * ‖X ξ‖ := by rw [hnorm ξ]

/-- Norm bound in Dixmier's commutant-induction proof: if `S` commutes with all compressions to `U`
of operators in `N.commutant`, then `‖∑ i, x i (S (u i))‖ ≤ ‖S‖ * ‖∑ i, x i (u i)‖` for every
finite tuple `x : Fin n → H →L[ℂ] H` in `N.commutant` and `u : Fin n → U`. -/
private theorem norm_sum_apply_le_of_mem_centralizer {N : VonNeumannAlgebra H}
    {U : Submodule ℂ H} [CompleteSpace U] {S : U →L[ℂ] U}
    (hS : S ∈ ((·.compression U.subtypeL) '' (N.commutant : Set (H →L[ℂ] H))).centralizer)
    {n : ℕ} (x : Fin n → H →L[ℂ] H) (hx : ∀ i, x i ∈ N.commutant) (u : Fin n → U) :
    ‖∑ i : Fin n, x i (S (u i))‖ ≤ ‖S‖ * ‖∑ i : Fin n, x i (u i)‖ := by
  let X : PiLp 2 (fun _ : Fin n ↦ U) →L[ℂ] H :=
    ∑ i : Fin n, x i ∘L U.subtypeL ∘L PiLp.proj 2 (fun _ : Fin n ↦ U) i
  have hX_apply (η : PiLp 2 (fun _ : Fin n ↦ U)) : X η = ∑ i : Fin n, x i (η i) := by
    simp only [X, sum_apply, comp_apply, U.coe_subtypeL, Submodule.coe_subtype]
    rfl
  have hX_single (j : Fin n) (w : U) : X (PiLp.single 2 j w) = x j w := by
    rw [hX_apply, Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · intro hj
      exact False.elim (hj (Finset.mem_univ j))
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
      inner_compression_apply, mul_def, comp_apply, star_eq_adjoint, adjoint_inner_right]
    rfl
  let Sₙ := PiLp.diagStarAlgHom ℂ U (Fin n) S
  have hAS : Commute A Sₙ := by
    rw [Commute, SemiconjBy]
    refine ContinuousLinearMap.ext fun η ↦ PiLp.ext fun i ↦ ?_
    change A (Sₙ η) i = Sₙ (A η) i
    rw [apply_eq_sum_piLpEntry, PiLp.diagStarAlgHom_apply, apply_eq_sum_piLpEntry, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [PiLp.diagStarAlgHom_apply]
    have hcomm : A.piLpEntry i j * S = S * A.piLpEntry i j := by
      rw [hA_entry]
      exact Set.mem_centralizer_iff.mp hS _
        ⟨star (x i) * x j, mul_mem (star_mem (hx i)) (hx j), rfl⟩
    exact DFunLike.congr_fun hcomm (η j)
  have hSₙ_norm : ‖Sₙ‖ ≤ ‖S‖ := by
    refine opNorm_le_bound _ (norm_nonneg S) fun ξ ↦ ?_
    refine (sq_le_sq₀ (norm_nonneg (Sₙ ξ))
      (mul_nonneg (norm_nonneg S) (norm_nonneg ξ))).mp ?_
    rw [mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    change ‖Sₙ ξ i‖ ^ 2 ≤ _
    rw [PiLp.diagStarAlgHom_apply, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (S.le_opNorm (ξ i)) 2
  let η : PiLp 2 (fun _ : Fin n ↦ U) := WithLp.toLp 2 u
  have hSₙ_η : X (Sₙ η) = ∑ i : Fin n, x i (S (u i)) := by
    rw [hX_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [PiLp.diagStarAlgHom_apply]
  calc
    ‖∑ i : Fin n, x i (S (u i))‖ = ‖X (Sₙ η)‖ := by rw [hSₙ_η]
    _ ≤ ‖Sₙ‖ * ‖X η‖ := norm_apply_comp_le_of_commute_adjoint_comp_self X hAS η
    _ ≤ ‖S‖ * ‖X η‖ := mul_le_mul_of_nonneg_right hSₙ_norm (norm_nonneg _)
    _ = ‖S‖ * ‖∑ i : Fin n, x i (u i)‖ := by rw [hX_apply]

/-- Step B of Dixmier's corner theorem: when `U.starProjection ∈ N.commutant`, the centralizer of
the compressed commutant `(·.compression U.subtypeL) '' N.commutant` is the compressed algebra
`(·.compression U.subtypeL) '' N`. -/
private theorem centralizer_image_compression_commutant_of_mem_commutant {N : VonNeumannAlgebra H}
    {U : Submodule ℂ H} [CompleteSpace U] (hp : U.starProjection ∈ N.commutant) :
    ((·.compression U.subtypeL) '' (N.commutant : Set (H →L[ℂ] H))).centralizer =
      (·.compression U.subtypeL) '' (N : Set (H →L[ℂ] H)) := by
  refine Set.Subset.antisymm (fun S hS ↦ ?_) ?_
  · let Φ : (N.commutant →₀ U) →ₗ[ℂ] H :=
      Finsupp.lsum ℂ fun x : N.commutant ↦ (x : H →L[ℂ] H).toLinearMap.comp U.subtype
    let Ψ : (N.commutant →₀ U) →ₗ[ℂ] H :=
      Finsupp.lsum ℂ fun x : N.commutant ↦
        (x : H →L[ℂ] H).toLinearMap.comp (U.subtype.comp S.toLinearMap)
    have hΦ_apply (d : N.commutant →₀ U) :
        Φ d = ∑ x ∈ d.support, (x : H →L[ℂ] H) (d x) := by
      simp [Φ, Finsupp.lsum_apply, Finsupp.sum]
    have hΨ_apply (d : N.commutant →₀ U) :
        Ψ d = ∑ x ∈ d.support, (x : H →L[ℂ] H) (S (d x)) := by
      simp [Ψ, Finsupp.lsum_apply, Finsupp.sum]
    have hΨ_le (d : N.commutant →₀ U) : ‖Ψ d‖ ≤ ‖S‖ * ‖Φ d‖ := by
      let e : Fin d.support.card ≃ d.support := d.support.equivFin.symm
      have hΦ_fin : Φ d = ∑ k : Fin d.support.card, ((e k).1 : H →L[ℂ] H) (d (e k).1) := by
        rw [hΦ_apply, ← Finset.sum_coe_sort d.support]
        exact (e.sum_comp fun x : d.support ↦ (x.1 : H →L[ℂ] H) (d x.1)).symm
      have hΨ_fin : Ψ d = ∑ k : Fin d.support.card, ((e k).1 : H →L[ℂ] H) (S (d (e k).1)) := by
        rw [hΨ_apply, ← Finset.sum_coe_sort d.support]
        exact (e.sum_comp fun x : d.support ↦ (x.1 : H →L[ℂ] H) (S (d x.1))).symm
      rw [hΨ_fin, hΦ_fin]
      exact norm_sum_apply_le_of_mem_centralizer hS (fun k ↦ ((e k).1 : H →L[ℂ] H))
        (fun k ↦ (e k).1.2) (fun k ↦ d (e k).1)
    let K₀ : Submodule ℂ H := LinearMap.range Φ
    let K : Submodule ℂ H := K₀.topologicalClosure
    have : CompleteSpace K := K₀.isClosed_topologicalClosure.completeSpace_coe
    have hΨ_mem (d : N.commutant →₀ U) : Ψ d ∈ K := by
      rw [hΨ_apply]
      exact sum_mem fun x _ ↦ subset_closure ⟨Finsupp.single x (S (d x)), by simp [Φ]⟩
    let eK : (N.commutant →₀ U) →ₗ[ℂ] K :=
      Φ.codRestrict K fun d ↦ subset_closure (LinearMap.mem_range_self Φ d)
    let fK : (N.commutant →₀ U) →ₗ[ℂ] K := Ψ.codRestrict K hΨ_mem
    have h_dense : DenseRange eK := by
      rw [DenseRange, dense_iff_closure_eq,
        Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
      have himg : Subtype.val '' Set.range eK = (K₀ : Set H) := by
        ext v
        exact ⟨fun ⟨_, ⟨d, rfl⟩, hdv⟩ ↦ ⟨d, hdv⟩, fun ⟨d, hdv⟩ ↦ ⟨eK d, ⟨d, rfl⟩, hdv⟩⟩
      rw [himg]
      ext w
      exact ⟨fun _ ↦ trivial, fun _ ↦ w.2⟩
    have h_norm (d : N.commutant →₀ U) : ‖fK d‖ ≤ ‖S‖ * ‖eK d‖ := hΨ_le d
    let Y : K →L[ℂ] K := fK.extendOfNorm eK
    have hY_eq (d : N.commutant →₀ U) : Y (eK d) = fK d :=
      LinearMap.extendOfNorm_eq h_dense ⟨‖S‖, h_norm⟩ d
    let mulDom (z : H →L[ℂ] H) (hz : z ∈ N.commutant) :
        N.commutant → N.commutant := fun x ↦ ⟨z * x, mul_mem hz x.2⟩
    have hΦ_mulDom (z : H →L[ℂ] H) (hz : z ∈ N.commutant) (d : N.commutant →₀ U) :
        Φ (Finsupp.mapDomain (mulDom z hz) d) = z (Φ d) := by
      change (Finsupp.mapDomain (mulDom z hz) d).sum (fun x u ↦ (x : H →L[ℂ] H) u) = z (Φ d)
      rw [Finsupp.sum_mapDomain_index (fun _ ↦ by simp) (fun _ _ _ ↦ by simp [map_add]),
        hΦ_apply, map_sum]
      rfl
    have hΨ_mulDom (z : H →L[ℂ] H) (hz : z ∈ N.commutant) (d : N.commutant →₀ U) :
        Ψ (Finsupp.mapDomain (mulDom z hz) d) = z (Ψ d) := by
      change (Finsupp.mapDomain (mulDom z hz) d).sum
        (fun x u ↦ (x : H →L[ℂ] H) (S u)) = z (Ψ d)
      rw [Finsupp.sum_mapDomain_index (fun _ ↦ by simp) (fun _ _ _ ↦ by simp [map_add]),
        hΨ_apply, map_sum]
      rfl
    have hK_inv (z : H →L[ℂ] H) (hz : z ∈ N.commutant) :
        K ∈ Module.End.invtSubmodule (z : Module.End ℂ H) := by
      rw [Module.End.mem_invtSubmodule]
      have hK₀ : (K₀ : Set H) ⊆ z ⁻¹' (K : Set H) := by
        rintro _ ⟨d, rfl⟩
        exact subset_closure ⟨Finsupp.mapDomain (mulDom z hz) d, hΦ_mulDom z hz d⟩
      exact closure_minimal hK₀ (K₀.isClosed_topologicalClosure.preimage z.continuous)
    have hK_mem : K.starProjection ∈ N :=
      (starProjection_mem_iff_mem_invtSubmodule K).mpr hK_inv
    let y : H →L[ℂ] H := K.subtypeₗᵢ.cornerEmbedding Y
    have hyN : y ∈ N := by
      rw [← N.commutant_commutant, mem_commutant_iff]
      intro z hz
      have hKz : Commute K.starProjection z := mem_commutant_iff.mp hz K.starProjection hK_mem
      apply (commute_cornerEmbedding_iff Y hKz).mpr
      rw [Commute, SemiconjBy]
      refine ContinuousLinearMap.ext fun w ↦ ?_
      refine h_dense.induction (fun v hv ↦ ?_) (isClosed_eq (by fun_prop) (by fun_prop)) w
      obtain ⟨d, rfl⟩ := hv
      apply Subtype.ext
      have hsub := subtypeL_comp_compression_of_commute hKz
      have hzK (q : K) : (z.compression K.subtypeL q : H) = z (q : H) :=
        DFunLike.congr_fun hsub q
      change (z.compression K.subtypeL (Y (eK d)) : H) =
        (Y (z.compression K.subtypeL (eK d)) : H)
      have heK_zd : z.compression K.subtypeL (eK d) = eK (Finsupp.mapDomain (mulDom z hz) d) := by
        apply Subtype.ext
        rw [hzK]
        exact (hΦ_mulDom z hz d).symm
      rw [hY_eq d, hzK, heK_zd, hY_eq]
      exact (hΨ_mulDom z hz d).symm
    refine ⟨y, hyN, ?_⟩
    dsimp only
    refine ContinuousLinearMap.ext fun u ↦ ext_inner_left ℂ fun v ↦ ?_
    let d₀ : N.commutant →₀ U := Finsupp.single ⟨1, N.commutant.one_mem⟩ u
    have hΦ₀ : Φ d₀ = u := by simp [Φ, d₀]
    have hΨ₀ : Ψ d₀ = S u := by simp [Ψ, d₀]
    have hyu : y u = S u := by
      have huK : (u : H) ∈ K := hΦ₀ ▸ (eK d₀).2
      have heK₀ : K.subtypeL.adjoint (u : H) = eK d₀ := by
        rw [K.adjoint_subtypeL]
        apply Subtype.ext
        rw [K.coe_orthogonalProjectionOnto_apply, K.starProjection_eq_self_iff.mpr huK]
        exact hΦ₀.symm
      simp only [y, LinearIsometry.cornerEmbedding_apply_apply, K.subtypeₗᵢ_toContinuousLinearMap,
        heK₀, hY_eq]
      exact hΨ₀
    rw [inner_compression_apply, U.coe_subtypeL, Submodule.coe_subtype, hyu, Submodule.coe_inner]
  · rintro _ ⟨y, hy, rfl⟩
    rw [Set.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hpy : Commute (U.subtypeL ∘L U.subtypeL.adjoint) y := by
      rw [subtypeL_comp_adjoint_subtypeL]
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
  let s' : Set (U →L[ℂ] U) := (·.compression U.subtypeL) '' (M.commutant : Set (H →L[ℂ] H))
  let s : Set (U →L[ℂ] U) := (·.compression U.subtypeL) '' (M : Set (H →L[ℂ] H))
  have hc : (StarSubalgebra.centralizer ℂ s' : Set (U →L[ℂ] U)) = s := by
    rw [StarSubalgebra.coe_centralizer,
      Set.union_eq_left.2 (star_image_compression M.commutant U),
      centralizer_image_compression_commutant hU]
  { toStarSubalgebra := (StarSubalgebra.centralizer ℂ s').copy s hc.symm
    centralizer_centralizer' := by
      let c := (StarSubalgebra.centralizer ℂ s').copy s hc.symm
      change (c : Set (U →L[ℂ] U)).centralizer.centralizer = (c : Set (U →L[ℂ] U))
      rw [StarSubalgebra.coe_copy]
      simpa only [s, ← centralizer_image_compression_commutant hU] using
        Set.centralizer_centralizer_centralizer s' }

/-- The carrier set of `M.corner U hU` is the image of `M` under compression along `U.subtypeL`. -/
@[simp, norm_cast]
theorem coe_corner (M : VonNeumannAlgebra H) (U : Submodule ℂ H) [CompleteSpace U]
    (hU : U.starProjection ∈ M ∨ U.starProjection ∈ M.commutant) :
    (M.corner U hU : Set (U →L[ℂ] U)) = (·.compression U.subtypeL) '' (M : Set (H →L[ℂ] H)) :=
  (rfl)

/-- An operator on `U` belongs to `M.corner U hU` if and only if it is the compression of an
operator in `M`. -/
theorem mem_corner_iff {M : VonNeumannAlgebra H} {U : Submodule ℂ H} [CompleteSpace U]
    {hU : U.starProjection ∈ M ∨ U.starProjection ∈ M.commutant} {T : U →L[ℂ] U} :
    T ∈ M.corner U hU ↔ ∃ x ∈ M, x.compression U.subtypeL = T :=
  Iff.rfl

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
  ⟨x, hx, rfl⟩

/-- When `U.starProjection ∈ M`, an operator `T : U →L[ℂ] U` belongs to `M.corner U (.inl hp)` if
and only if its extension by zero `U.subtypeₗᵢ.cornerEmbedding T` belongs to `M`. -/
theorem mem_corner_iff_cornerEmbedding_mem {M : VonNeumannAlgebra H} {U : Submodule ℂ H}
    [CompleteSpace U] (hp : U.starProjection ∈ M) {T : U →L[ℂ] U} :
    T ∈ M.corner U (.inl hp) ↔ U.subtypeₗᵢ.cornerEmbedding T ∈ M := by
  rw [mem_corner_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [cornerEmbedding_subtype_compression]
    exact mul_mem (mul_mem hp hx) hp
  · intro hT
    refine ⟨U.subtypeₗᵢ.cornerEmbedding T, hT, ?_⟩
    simpa [U.subtypeₗᵢ_toContinuousLinearMap] using U.subtypeₗᵢ.compression_cornerEmbedding T

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
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hMN hx, rfl⟩

/-- Auxiliary witness that `U.starProjection ∈ (M ⊓ M.commutant).commutant` whenever
`U.starProjection ∈ M ∨ U.starProjection ∈ M.commutant`. -/
theorem starProjection_mem_commutant_center {M : VonNeumannAlgebra H} {U : Submodule ℂ H}
    [U.HasOrthogonalProjection] (hU : U.starProjection ∈ M ∨ U.starProjection ∈ M.commutant) :
    U.starProjection ∈ (M ⊓ M.commutant).commutant := by
  rcases hU with hp | hp
  · exact commutant_le_commutant inf_le_right (M.commutant_commutant.symm ▸ hp)
  · exact commutant_le_commutant inf_le_left hp

private theorem corner_inf_commutant_of_mem {M : VonNeumannAlgebra H} {U : Submodule ℂ H}
    [CompleteSpace U] (hp : U.starProjection ∈ M) :
    M.corner U (.inl hp) ⊓ (M.corner U (.inl hp)).commutant =
      (M ⊓ M.commutant).corner U (.inr (starProjection_mem_commutant_center (.inl hp))) := by
  refine le_antisymm (fun T hT ↦ ?_) ?_
  · obtain ⟨hTM, hTM'⟩ : T ∈ M.corner U (.inl hp) ∧ T ∈ (M.corner U (.inl hp)).commutant :=
      mem_inf.mp hT
    rw [commutant_corner] at hTM'
    obtain ⟨y, hy, rfl⟩ := hTM'
    let L₀ : Submodule ℂ H :=
      Submodule.span ℂ {v : H | ∃ a ∈ M, ∃ u : U, a u = v}
    let L : Submodule ℂ H := L₀.topologicalClosure
    have hL_M : L.starProjection ∈ M.commutant := by
      rw [starProjection_mem_commutant_iff_mem_invtSubmodule]
      intro x hx
      rw [Module.End.mem_invtSubmodule]
      refine closure_minimal ?_ (L₀.isClosed_topologicalClosure.preimage x.continuous)
      change (L₀ : Set H) ⊆ (L.comap (x : Module.End ℂ H) : Set H)
      rw [SetLike.coe_subset_coe, ← Submodule.map_le_iff_le_comap, Submodule.map_span_le]
      rintro _ ⟨a, ha, u, rfl⟩
      exact subset_closure (Submodule.subset_span ⟨x * a, mul_mem hx ha, u, rfl⟩)
    have hL_M' : L.starProjection ∈ M := by
      rw [starProjection_mem_iff_mem_invtSubmodule]
      intro b hb
      rw [Module.End.mem_invtSubmodule]
      refine closure_minimal ?_ (L₀.isClosed_topologicalClosure.preimage b.continuous)
      change (L₀ : Set H) ⊆ (L.comap (b : Module.End ℂ H) : Set H)
      rw [SetLike.coe_subset_coe, ← Submodule.map_le_iff_le_comap, Submodule.map_span_le]
      rintro _ ⟨a, ha, u, rfl⟩
      have hbu : b u ∈ U := (starProjection_mem_iff_mem_invtSubmodule U).mp hp b hb u.2
      have hcomm : b (a u) = a (b u) :=
        DFunLike.congr_fun (mem_commutant_iff.mp hb a ha).symm (u : H)
      exact subset_closure (Submodule.subset_span ⟨a, ha, ⟨b u, hbu⟩, hcomm.symm⟩)
    let z : H →L[ℂ] H := L.starProjection * y
    have hzM' : z ∈ M.commutant := mul_mem hL_M hy
    have hzM : z ∈ M := by
      rw [← M.commutant_commutant, mem_commutant_iff]
      intro b hb
      have hbL : b * L.starProjection = L.starProjection * b :=
        (mem_commutant_iff.mp hb L.starProjection hL_M').symm
      have hyL : y * L.starProjection = L.starProjection * y :=
        (mem_commutant_iff.mp hy L.starProjection hL_M').symm
      have eqOnL : ∀ w ∈ L, (b * y) w = (y * b) w := by
        let eqSub : Submodule ℂ H := LinearMap.eqLocus (b * y).toLinearMap (y * b).toLinearMap
        have hclosed : IsClosed (eqSub : Set H) :=
          isClosed_eq (b * y).continuous (y * b).continuous
        have hL₀ : L₀ ≤ eqSub := by
          rw [Submodule.span_le]
          rintro _ ⟨a, ha, u, rfl⟩
          change (b * y) (a u) = (y * b) (a u)
          have hya : y * a = a * y := (mem_commutant_iff.mp hy a ha).symm
          have hba : b * a = a * b := (mem_commutant_iff.mp hb a ha).symm
          have hpy : Commute U.starProjection y := mem_commutant_iff.mp hy U.starProjection hp
          have hpb : Commute U.starProjection b := mem_commutant_iff.mp hb U.starProjection hp
          have hy_sub := subtypeL_comp_compression_of_commute hpy
          have hb_sub := subtypeL_comp_compression_of_commute hpb
          have hTy : y.compression U.subtypeL * b.compression U.subtypeL =
              b.compression U.subtypeL * y.compression U.subtypeL := by
            have hb_mem : b.compression U.subtypeL ∈ (M.corner U (.inl hp)).commutant := by
              rw [commutant_corner]
              exact ⟨b, hb, rfl⟩
            exact mem_commutant_iff.mp hb_mem _ hTM
          have hbyu : b (y u) = y (b u) := by
            have h1 : b (y u) = U.subtypeL ((b.compression U.subtypeL *
                y.compression U.subtypeL) u) := by
              have hyu := DFunLike.congr_fun hy_sub u
              have hbu := DFunLike.congr_fun hb_sub (y.compression U.subtypeL u)
              simpa only [mul_def, comp_apply, U.coe_subtypeL, Submodule.coe_subtype] using
                (congrArg b hyu.symm).trans hbu.symm
            have h2 : y (b u) = U.subtypeL ((y.compression U.subtypeL *
                b.compression U.subtypeL) u) := by
              have hbu := DFunLike.congr_fun hb_sub u
              have hyu := DFunLike.congr_fun hy_sub (b.compression U.subtypeL u)
              simpa only [mul_def, comp_apply, U.coe_subtypeL, Submodule.coe_subtype] using
                (congrArg y hbu.symm).trans hyu.symm
            rw [h1, h2, hTy]
          have hyaw (w : H) : y (a w) = a (y w) := DFunLike.congr_fun hya w
          have hbaw (w : H) : b (a w) = a (b w) := DFunLike.congr_fun hba w
          simp only [mul_def, comp_apply, hyaw, hbaw, hbyu]
        exact fun w hw ↦ closure_minimal hL₀ hclosed hw
      refine ContinuousLinearMap.ext fun ξ ↦ ?_
      have hb_z : (b * z) ξ = (b * y) (L.starProjection ξ) := by
        change (b * (L.starProjection * y)) ξ = _
        rw [← hyL, ← mul_assoc]
        simp only [mul_def, comp_apply]
      have hz_b : (z * b) ξ = (y * b) (L.starProjection ξ) := by
        change (L.starProjection * y * b) ξ = _
        rw [← hyL, mul_assoc, ← hbL, ← mul_assoc]
        simp only [mul_def, comp_apply]
      rw [hb_z, hz_b, eqOnL _ (L.starProjection_apply_mem ξ)]
    rw [mem_corner_iff]
    refine ⟨z, mem_inf.mpr ⟨hzM, hzM'⟩, ?_⟩
    dsimp only
    refine ContinuousLinearMap.ext fun u ↦ ext_inner_left ℂ fun v ↦ ?_
    have huL : (u : H) ∈ L :=
      subset_closure (Submodule.subset_span ⟨1, M.one_mem, u, by simp⟩)
    have hzu : z u = y u := by
      have hyL : L.starProjection * y = y * L.starProjection :=
        mem_commutant_iff.mp hy L.starProjection hL_M'
      change (L.starProjection * y) u = y u
      rw [hyL, mul_def, comp_apply, L.starProjection_eq_self_iff.mpr huL]
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
      rw [subtypeL_comp_adjoint_subtypeL]
      exact (mem_commutant_iff.mp hp x x.2).symm
    exact compression_mul_of_commute_left (y : H →L[ℂ] H) U.subtypeₗᵢ.isometry hpx
  map_zero' := compression_zero U.subtypeL
  map_add' x y := compression_add (x : H →L[ℂ] H) U.subtypeL (y : H →L[ℂ] H)
  commutes' c := by
    change (algebraMap ℂ (H →L[ℂ] H) c).compression U.subtypeL = algebraMap ℂ (U →L[ℂ] U) c
    simp only [Algebra.algebraMap_eq_smul_one, compression_smul, compression_one_subtypeL]
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
  exact ⟨fun ⟨x, hx⟩ ↦ ⟨x.1, x.2, hx⟩, fun ⟨x, hx, hTx⟩ ↦ ⟨⟨x, hx⟩, hTx⟩⟩

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
  have hp0 : U.starProjection ≠ 0 := (starProjection_ne_zero_iff U).mpr ‹_›
  have hprod : (x : H →L[ℂ] H) * U.starProjection = 0 := by
    have hpx : Commute U.starProjection (x : H →L[ℂ] H) :=
      (mem_commutant_iff.mp hp x x.2).symm
    have hce := cornerEmbedding_subtype_compression U (x : H →L[ℂ] H)
    rw [show (x : H →L[ℂ] H).compression U.subtypeL = 0 from hx, map_zero,
      hpx.eq, mul_assoc, U.isIdempotentElem_starProjection.eq] at hce
    exact hce.symm
  exact Subtype.ext ((eq_zero_or_eq_zero_of_mul_eq_zero hM x.2 hp hprod).resolve_right hp0)

/-- When `M ⊓ M.commutant = ⊥`, `U` is nontrivial, and `U.starProjection ∈ M.commutant`, compression
gives a unital `⋆`-algebra isomorphism `M ≃⋆ₐ[ℂ] M.corner U (.inr hp)`. -/
noncomputable def cornerStarAlgEquiv {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    (U : Submodule ℂ H) [CompleteSpace U] [Nontrivial U] (hp : U.starProjection ∈ M.commutant) :
    M.toStarSubalgebra ≃⋆ₐ[ℂ] (M.corner U (.inr hp)).toStarSubalgebra :=
  let φ : M.toStarSubalgebra →⋆ₐ[ℂ] (M.corner U (.inr hp)).toStarSubalgebra :=
    { toFun := fun x ↦
        ⟨M.compressionStarAlgHom U hp x, compression_mem_corner (.inr hp) x.2⟩
      map_one' := Subtype.ext (map_one (M.compressionStarAlgHom U hp))
      map_mul' := fun x y ↦ Subtype.ext (map_mul (M.compressionStarAlgHom U hp) x y)
      map_zero' := Subtype.ext (map_zero (M.compressionStarAlgHom U hp))
      map_add' := fun x y ↦ Subtype.ext (map_add (M.compressionStarAlgHom U hp) x y)
      commutes' := fun c ↦ Subtype.ext ((M.compressionStarAlgHom U hp).commutes c)
      map_star' := fun x ↦ Subtype.ext (map_star (M.compressionStarAlgHom U hp) x) }
  StarAlgEquiv.ofBijective φ
    ⟨fun _ _ hxy ↦ compressionStarAlgHom_injective hM U hp (congrArg Subtype.val hxy),
      fun ⟨_, x, hx, hTx⟩ ↦ ⟨⟨x, hx⟩, Subtype.ext hTx⟩⟩

/-- `cornerStarAlgEquiv` acts by compressing along `U.subtypeL`. -/
@[simp]
theorem coe_cornerStarAlgEquiv_apply {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    (U : Submodule ℂ H) [CompleteSpace U] [Nontrivial U] (hp : U.starProjection ∈ M.commutant)
    (x : M.toStarSubalgebra) :
    (cornerStarAlgEquiv hM U hp x : U →L[ℂ] U) = (x : H →L[ℂ] H).compression U.subtypeL :=
  (rfl)

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
      M.commutant.compressionStarAlgHom U hp' y ∈ (M.corner U (.inl hp)).commutant := by
    rw [commutant_corner]
    exact compression_mem_corner _ y.2
  let φ : M.commutant.toStarSubalgebra →⋆ₐ[ℂ]
      (M.corner U (.inl hp)).commutant.toStarSubalgebra :=
    { toFun := fun y ↦ ⟨M.commutant.compressionStarAlgHom U hp' y, hmem y⟩
      map_one' := Subtype.ext (map_one (M.commutant.compressionStarAlgHom U hp'))
      map_mul' := fun x y ↦ Subtype.ext (map_mul (M.commutant.compressionStarAlgHom U hp') x y)
      map_zero' := Subtype.ext (map_zero (M.commutant.compressionStarAlgHom U hp'))
      map_add' := fun x y ↦ Subtype.ext (map_add (M.commutant.compressionStarAlgHom U hp') x y)
      commutes' := fun c ↦ Subtype.ext ((M.commutant.compressionStarAlgHom U hp').commutes c)
      map_star' := fun x ↦ Subtype.ext (map_star (M.commutant.compressionStarAlgHom U hp') x) }
  StarAlgEquiv.ofBijective φ
    ⟨fun _ _ hxy ↦ compressionStarAlgHom_injective hM' U hp' (congrArg Subtype.val hxy),
      fun ⟨T, hT⟩ ↦ by
        have hT' : T ∈ M.commutant.corner U (.inr hp') := by
          rwa [commutant_corner] at hT
        obtain ⟨y, hy, hTy⟩ := hT'
        exact ⟨⟨y, hy⟩, Subtype.ext hTy⟩⟩

/-- `commutantCornerStarAlgEquiv` acts by compressing along `U.subtypeL`. -/
@[simp]
theorem coe_commutantCornerStarAlgEquiv_apply {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    (U : Submodule ℂ H) [CompleteSpace U] [Nontrivial U] (hp : U.starProjection ∈ M)
    (y : M.commutant.toStarSubalgebra) :
    (commutantCornerStarAlgEquiv hM U hp y : U →L[ℂ] U) =
      (y : H →L[ℂ] H).compression U.subtypeL :=
  (rfl)

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
  ext T
  rw [coe_commutant_adjoin, himg, SetLike.mem_coe,
    mem_corner_iff_cornerEmbedding_mem (by simpa using hp), ← SetLike.mem_coe,
    coe_commutant_adjoin, Set.mem_centralizer_iff, Set.mem_centralizer_iff]
  have hsub : s ∪ star s ⊆ adjoin s :=
    Set.union_subset (subset_adjoin s) fun y hy ↦ by
      have hy' : star y ∈ adjoin s := subset_adjoin s (Set.mem_star.mp hy)
      have hsy : star (star y) ∈ adjoin s := star_mem hy'
      rwa [star_star] at hsy
  constructor
  · intro hT y hy
    have hpy : Commute U.starProjection y := (mem_commutant_iff.mp hp y (hsub hy)).symm
    exact (commute_cornerEmbedding_iff T hpy).mpr (hT _ ⟨y, hy, rfl⟩)
  · rintro hT _ ⟨y, hy, rfl⟩
    have hpy : Commute U.starProjection y := (mem_commutant_iff.mp hp y (hsub hy)).symm
    exact (commute_cornerEmbedding_iff T hpy).mp (hT y hy)

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
  · rintro _ ⟨x, hx, rfl⟩
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
      congrArg SetLike.coe (StarAlgebra.adjoin_toSubmodule_of_mul_mem hstar hmul)
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
    dsimp only
    exact hTx ▸ hTW

end VonNeumannAlgebra

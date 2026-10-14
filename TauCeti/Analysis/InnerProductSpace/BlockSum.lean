/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.InnerProductSpace.FanDominance
public import TauCeti.Data.Set.Card

/-!
# Unitary-orbit estimates for orthogonal block sums

The orthogonal block sum of `A : E₁ →ₗ[𝕜] F₁` and `B : E₂ →ₗ[𝕜] F₂` is Mathlib's
`(A.prodMap B).withLpMap 2`, acting componentwise on the Hilbert `L²` products. No separate
block-sum construction is needed.

Two-sided unitary orbits and their convex hulls are stable under block sums. Consequently,
Ky Fan domination on each block implies domination of the block sum, both for Ky Fan sums
and for every rectangular unitarily invariant seminorm. These estimates combine independent
bounds on orthogonal pieces without increasing their constants.

The orbit and orbit-hull statements require neither finite dimension nor completeness.
Only the consequences using Fan dominance require finite-dimensional spaces.

On the spectral side, the adjoint and the Gram operator are formed blockwise, so the eigenspaces
of the Gram operator of `A ⊕ B` are products of those of `A` and `B`: every positive singular
value of `A ⊕ B` occurs as often as in `A` and `B` together. In particular the doubled block
`A ⊕ A` repeats each singular value of `A` twice, and its Ky Fan sums are `K₂ₖ(A ⊕ A) = 2 Kₖ(A)`.

## Main results

* `LinearMap.prodMap_withLpMap_mem_twoSidedUnitaryOrbitHull`: stability of orbit hulls.
* `LinearMap.kyFanSum_prodMap_withLpMap_le`: blockwise Ky Fan domination.
* `TauCeti.UnitarilyInvariantSeminorm.map_prodMap_withLpMap_le`: the sharp block-sum
  comparison for all unitarily invariant seminorms.
* `LinearMap.adjoint_prodMap_withLpMap`: `(A ⊕ B)† = A† ⊕ B†`.
* `LinearMap.finrank_eigenspace_prodMap_withLpMap`: the eigenspaces of `T₁ ⊕ T₂` have dimension
  `dim ker(T₁ - μ) + dim ker(T₂ - μ)`.
* `LinearMap.ncard_ofPred_singularValues_prodMap_withLpMap`: a positive value occurs among the
  singular values of `A ⊕ B` as often as among those of `A` and `B` together.
* `LinearMap.singularValues_prodMap_withLpMap_self`: `σᵢ(A ⊕ A) = σ_{⌊i/2⌋}(A)`.
* `LinearMap.kyFanSum_prodMap_withLpMap_self`: `K₂ₖ(A ⊕ A) = 2 Kₖ(A)`.

## References

* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997,
  Sections III.1 and IV.2.
-/

public section

variable {𝕜 E₁ E₂ F₁ F₂ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
  [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]

namespace LinearMap

section Field

variable {K V₁ V₂ : Type*} [Field K] [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁]
  [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂]

open Module Module.End in
/-- The eigenspace of a block sum of endomorphisms is the product of the eigenspaces of the
blocks, so its dimension is the sum of their dimensions. -/
theorem finrank_eigenspace_prodMap_withLpMap (T₁ : V₁ →ₗ[K] V₁) (T₂ : V₂ →ₗ[K] V₂) (μ : K) :
    finrank K (eigenspace ((T₁.prodMap T₂).withLpMap 2) μ) =
      finrank K (eigenspace T₁ μ) + finrank K (eigenspace T₂ μ) := by
  have hmem {x : WithLp 2 (V₁ × V₂)} :
      x ∈ eigenspace ((T₁.prodMap T₂).withLpMap 2) μ ↔
        x.fst ∈ eigenspace T₁ μ ∧ x.snd ∈ eigenspace T₂ μ := by
    simp only [mem_eigenspace_iff, coe_withLpMap]
    constructor
    · intro h
      exact ⟨by simpa [WithLp.map, prodMap_apply] using congrArg WithLp.fst h,
        by simpa [WithLp.map, prodMap_apply] using congrArg WithLp.snd h⟩
    · rintro ⟨h₁, h₂⟩
      simp [WithLp.map, WithLp.ext_iff, Prod.ext_iff, prodMap_apply, h₁, h₂]
  let e : eigenspace ((T₁.prodMap T₂).withLpMap 2) μ ≃ₗ[K] eigenspace T₁ μ × eigenspace T₂ μ :=
    { toFun x := (⟨x.1.fst, (hmem.mp x.2).1⟩, ⟨x.1.snd, (hmem.mp x.2).2⟩)
      invFun y := ⟨WithLp.toLp 2 (y.1.1, y.2.1), hmem.mpr ⟨by simp, by simp⟩⟩
      map_add' x y := rfl
      map_smul' c x := rfl
      left_inv x := Subtype.ext (WithLp.toLp_ofLp 2 x.1)
      right_inv y := rfl }
  rw [e.finrank_eq, finrank_prod]

end Field

/-- Block sums of points in two-sided unitary orbits lie in the orbit of the block sum. -/
theorem prodMap_withLpMap_mem_twoSidedUnitaryOrbit
    {A C : E₁ →ₗ[𝕜] F₁} {B D : E₂ →ₗ[𝕜] F₂}
    (hA : A ∈ C.twoSidedUnitaryOrbit) (hB : B ∈ D.twoSidedUnitaryOrbit) :
    (A.prodMap B).withLpMap 2 ∈ ((C.prodMap D).withLpMap 2).twoSidedUnitaryOrbit := by
  obtain ⟨U, V, rfl⟩ := mem_twoSidedUnitaryOrbit.mp hA
  obtain ⟨U', V', rfl⟩ := mem_twoSidedUnitaryOrbit.mp hB
  refine mem_twoSidedUnitaryOrbit.mpr
    ⟨U.withLpProdCongr 2 U', V.withLpProdCongr 2 V', ?_⟩
  ext x
  simp [LinearIsometryEquiv.withLpProdCongr_apply, WithLp.map, prodMap_apply]

/-- Convex unitary-orbit bounds on two blocks combine into the same bound on their
orthogonal block sum. -/
theorem prodMap_withLpMap_mem_twoSidedUnitaryOrbitHull
    {A C : E₁ →ₗ[𝕜] F₁} {B D : E₂ →ₗ[𝕜] F₂}
    (hA : A ∈ C.twoSidedUnitaryOrbitHull) (hB : B ∈ D.twoSidedUnitaryOrbitHull) :
    (A.prodMap B).withLpMap 2 ∈ ((C.prodMap D).withLpMap 2).twoSidedUnitaryOrbitHull := by
  -- Restrict scalars locally so that Mathlib's convex-hull product theorem applies.
  let := Module.compHom F₁ (algebraMap ℝ 𝕜)
  let := Module.compHom F₂ (algebraMap ℝ 𝕜)
  let : IsScalarTower ℝ 𝕜 F₁ := IsScalarTower.of_compHom ℝ 𝕜 F₁
  let : IsScalarTower ℝ 𝕜 F₂ := IsScalarTower.of_compHom ℝ 𝕜 F₂
  rw [twoSidedUnitaryOrbitHull_eq_convexHull] at hA hB ⊢
  let L := ((LinearEquiv.arrowCongr
    (WithLp.linearEquiv 2 𝕜 (E₁ × E₂)).symm
    (WithLp.linearEquiv 2 𝕜 (F₁ × F₂)).symm).toLinearMap.comp
      (prodMapLinear 𝕜 E₁ E₂ F₁ F₂ (S := 𝕜))).restrictScalars ℝ
  have hL (p : (E₁ →ₗ[𝕜] F₁) × (E₂ →ₗ[𝕜] F₂)) :
      L p = (p.1.prodMap p.2).withLpMap 2 := by
    ext x
    simp [L, WithLp.map, prodMap_apply]
  have hmem : L (A, B) ∈
      convexHull ℝ (L '' (C.twoSidedUnitaryOrbit ×ˢ D.twoSidedUnitaryOrbit)) := by
    rw [← L.image_convexHull]
    exact ⟨(A, B), mk_mem_convexHull_prod hA hB, rfl⟩
  rw [hL] at hmem
  refine convexHull_mono (fun Z hZ ↦ ?_) hmem
  obtain ⟨⟨X, Y⟩, ⟨hX, hY⟩, rfl⟩ := hZ
  rw [hL]
  exact prodMap_withLpMap_mem_twoSidedUnitaryOrbit hX hY

section FiniteDimensional

variable [FiniteDimensional 𝕜 E₁] [FiniteDimensional 𝕜 E₂]
  [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]

/-- Ky Fan domination on each block implies Ky Fan domination on the orthogonal block sum. -/
theorem kyFanSum_prodMap_withLpMap_le
    {A C : E₁ →ₗ[𝕜] F₁} {B D : E₂ →ₗ[𝕜] F₂}
    (hA : ∀ k, A.kyFanSum k ≤ C.kyFanSum k) (hB : ∀ k, B.kyFanSum k ≤ D.kyFanSum k)
    (k : ℕ) :
    ((A.prodMap B).withLpMap 2).kyFanSum k ≤ ((C.prodMap D).withLpMap 2).kyFanSum k :=
  (mem_twoSidedUnitaryOrbitHull_iff_kyFanSum_le.mp
    (prodMap_withLpMap_mem_twoSidedUnitaryOrbitHull
      (mem_twoSidedUnitaryOrbitHull_iff_kyFanSum_le.mpr hA)
      (mem_twoSidedUnitaryOrbitHull_iff_kyFanSum_le.mpr hB))) k

/-- **Adjoint of a block sum.** `(A ⊕ B)† = A† ⊕ B†`. -/
@[simp]
theorem adjoint_prodMap_withLpMap (A : E₁ →ₗ[𝕜] F₁) (B : E₂ →ₗ[𝕜] F₂) :
    adjoint ((A.prodMap B).withLpMap 2) = ((adjoint A).prodMap (adjoint B)).withLpMap 2 := by
  refine ((eq_adjoint_iff _ _).mpr fun x y ↦ ?_).symm
  simp [WithLp.map, prodMap_apply, WithLp.prod_inner_apply, adjoint_inner_left]

/-- A positive value `s` occurs among the singular values of `A ⊕ B` as often as among those of
`A` and of `B` together. -/
theorem ncard_ofPred_singularValues_prodMap_withLpMap (A : E₁ →ₗ[𝕜] F₁) (B : E₂ →ₗ[𝕜] F₂)
    {s : ℝ} (hs : 0 < s) :
    {i | ((A.prodMap B).withLpMap 2).singularValues i = s}.ncard =
      {i | A.singularValues i = s}.ncard + {i | B.singularValues i = s}.ncard := by
  rw [ncard_ofPred_singularValues_eq _ hs, ncard_ofPred_singularValues_eq _ hs,
    ncard_ofPred_singularValues_eq _ hs, adjoint_prodMap_withLpMap, ← withLpMap_comp,
    prodMap_comp, finrank_eigenspace_prodMap_withLpMap]

/-- **Singular values of a doubled block.** The singular values of `A ⊕ A` are those of `A`, each
repeated twice: `σᵢ(A ⊕ A) = σ_{⌊i/2⌋}(A)`. -/
theorem singularValues_prodMap_withLpMap_self (A : E₁ →ₗ[𝕜] F₁) (i : ℕ) :
    ((A.prodMap A).withLpMap 2).singularValues i = A.singularValues (i / 2) := by
  -- The sequence `i ↦ σ_{⌊i/2⌋}(A)` lists every singular value of `A` twice; it vanishes from
  -- `2 * dim E₁` on.
  let d : ℕ →₀ ℝ :=
    Finsupp.ofSupportFinite (fun i ↦ A.singularValues (i / 2))
      ((Set.finite_Iio (2 * Module.finrank 𝕜 E₁)).subset fun i hi ↦ Set.mem_Iio.mpr <| by
        by_contra h
        exact hi (A.singularValues_of_finrank_le (by omega)))
  have hd (i : ℕ) : d i = A.singularValues (i / 2) := congrFun Finsupp.ofSupportFinite_coe i
  suffices ((A.prodMap A).withLpMap 2).singularValues = d by rw [this, hd]
  refine Finsupp.eq_of_antitone_of_ncard_eq (singularValues_antitone _)
    (fun i j hij ↦ by simpa only [hd] using A.singularValues_antitone (Nat.div_le_div_right hij))
    fun s hs ↦ ?_
  rcases (lt_or_gt_of_ne hs) with hs | hs
  · have hempty (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) : {i | f i = s} = ∅ :=
      Set.eq_empty_of_forall_notMem fun i hi ↦ (hf i).not_gt (hi ▸ hs)
    rw [hempty _ (singularValues_nonneg _), hempty d fun i ↦ by
      simpa only [hd] using A.singularValues_nonneg _]
  · rw [ncard_ofPred_singularValues_prodMap_withLpMap A A hs, ← mul_two,
      ← Set.ncard_preimage_div]
    simp only [hd, Set.preimage_ofPred_eq]

/-- **Ky Fan sums of a doubled block.** `K₂ₖ(A ⊕ A) = 2 Kₖ(A)`. -/
theorem kyFanSum_prodMap_withLpMap_self (A : E₁ →ₗ[𝕜] F₁) (k : ℕ) :
    ((A.prodMap A).withLpMap 2).kyFanSum (2 * k) = 2 * A.kyFanSum k := by
  induction k with
  | zero => simp
  | succ k ih =>
    -- Splitting `2 * (k + 1)` as `2 * k + 1 + 1` exposes two steps of the Ky Fan recurrence, which
    -- add `σ_{2k}(A ⊕ A)` and `σ_{2k+1}(A ⊕ A)`; both indices halve to `k`, so each is `σₖ(A)`.
    have hidx : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    have hodd : (2 * k + 1) / 2 = k := by omega
    have heven : 2 * k / 2 = k := by omega
    rw [hidx, kyFanSum_succ, kyFanSum_succ, ih, singularValues_prodMap_withLpMap_self,
      singularValues_prodMap_withLpMap_self, hodd, heven, kyFanSum_succ]
    ring

end FiniteDimensional

end LinearMap

namespace TauCeti.UnitarilyInvariantSeminorm

/-- Blockwise Ky Fan estimates give the sharp comparison for every unitarily invariant
seminorm on the orthogonal block sums. -/
theorem map_prodMap_withLpMap_le
    [FiniteDimensional 𝕜 E₁] [FiniteDimensional 𝕜 E₂]
    [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]
    (N : UnitarilyInvariantSeminorm 𝕜 (WithLp 2 (E₁ × E₂)) (WithLp 2 (F₁ × F₂)))
    {A C : E₁ →ₗ[𝕜] F₁} {B D : E₂ →ₗ[𝕜] F₂}
    (hA : ∀ k, A.kyFanSum k ≤ C.kyFanSum k) (hB : ∀ k, B.kyFanSum k ≤ D.kyFanSum k) :
    N ((A.prodMap B).withLpMap 2) ≤ N ((C.prodMap D).withLpMap 2) :=
  N.map_le_of_kyFanSum_le (LinearMap.kyFanSum_prodMap_withLpMap_le hA hB)

end TauCeti.UnitarilyInvariantSeminorm

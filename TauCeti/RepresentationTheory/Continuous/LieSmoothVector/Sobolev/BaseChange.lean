/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector.BaseChange
public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector.Sobolev.Topology

/-!
# Sobolev seminorms along a basis of the complexified Lie algebra

Let `π` be a continuous representation of a real Lie group `G` on a normed space `V` over a normed
field `𝕜` containing `ℝ` (for instance `𝕜 = ℂ`), and let `𝔤 = 𝕜 ⊗[ℝ] Lie(G)`. The derived action
extends `𝕜`-linearly to `𝔤` (`ContRepresentation.lieSmoothVectorsBaseChangeDerivedAction`). For a
family `Z₁, …, Z_m` of `𝔤`, this file defines the Sobolev seminorms
`Q^Z_k(v) = (∑_{|α| ≤ k} ‖dπ(Z^α) v‖²)^{1/2}` over the ordered monomials
`Z^α = Z₁^{α₁} ⋯ Z_m^{α_m}` (`ContRepresentation.baseChangeSobolevSeminorm`). For `Z = 1 ⊗ X`
they are the real Sobolev seminorms of `X`
(`ContRepresentation.baseChangeSobolevSeminorm_one_tmul`).

They are comparable with the word seminorms `P^Z_k` of
`ContRepresentation.baseChangeWordSeminorm`: `Q^Z_k ≤ P^Z_k`, since every ordered monomial is a
word and the `ℓ²` norm of a finite family is at most its `ℓ¹` norm; and, for a family spanning
`𝔤` over `𝕜`, `P^Z_k ≤ C_k Q^Z_k`, because the spanning half of the Poincaré–Birkhoff–Witt
theorem for `U(𝔤)` (`TauCeti.UniversalEnvelopingAlgebra.span_orderedPBWMonomials_eq_pbwFiltration`)
writes every word of length at most `k` as a `𝕜`-combination of ordered monomials of degree at
most `k`, and words act through `ContRepresentation.lieSmoothVectorsBaseChangeEnvelopingAction`.
With the comparison of word seminorms along a `𝕜`-spanning family of `𝔤` and along a real spanning
family of `Lie(G)`, the Sobolev seminorms along a `𝕜`-spanning family of `𝔤` define the topology of
`ContRepresentation.LieSmoothSpace`.

## Main definitions

* `ContRepresentation.baseChangeWordAction`: the operator `dπ(Z_w)` of a word along a family of
  `𝕜 ⊗[ℝ] Lie(G)`.
* `ContRepresentation.baseChangeSobolevSeminorm`: the Sobolev seminorm `Q^Z_k`.
* `ContRepresentation.LieSmoothSpace.baseChangeSobolevSeminormFamily`: the seminorms `Q^Z_k` on
  `LieSmoothSpace I π X`.

## Main results

* `ContRepresentation.baseChangeSobolevSeminorm_le_baseChangeWordSeminorm`: `Q^Z_k ≤ P^Z_k`.
* `ContRepresentation.exists_baseChangeWordSeminorm_le_mul_baseChangeSobolevSeminorm`:
  `P^Z_k ≤ C_k Q^Z_k` for a family spanning `𝕜 ⊗[ℝ] Lie(G)`.
* `ContRepresentation.LieSmoothSpace.withSeminorms_baseChangeSobolevSeminormFamily`: the Sobolev
  seminorms along a `𝕜`-spanning family of `𝕜 ⊗[ℝ] Lie(G)` define the topology of the smooth
  vectors.

## References

* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*,
  Israel J. Math. 199 (2014), §2.4.2–§2.4.3.
-/

public section

noncomputable section

open scoped ContDiff Manifold TensorProduct

namespace ContRepresentation

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V]
  [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 V]
  {π : ContRepresentation 𝕜 G V} {ι : Type*} {m : ℕ}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-! ### Words along a family of the complexified Lie algebra -/

variable (I π) in
/-- The operator `dπ(Z_w) = dπ(Z_{i₁}) ∘ ⋯ ∘ dπ(Z_{iₙ})` on smooth vectors attached to a word
`w = [i₁, …, iₙ]`, along a family `Z` of `𝕜 ⊗[ℝ] Lie(G)`. -/
def baseChangeWordAction (Z : ι → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) (w : List ι) :
    Module.End 𝕜 (lieSmoothVectors I π) :=
  (w.map fun i ↦ lieSmoothVectorsBaseChangeDerivedAction I π (Z i)).prod

/-- The empty word acts as the identity. -/
@[simp]
theorem baseChangeWordAction_nil (Z : ι → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) :
    baseChangeWordAction I π Z [] = 1 :=
  (rfl)

/-- `dπ(Z_{i w}) = dπ(Z_i) ∘ dπ(Z_w)`. -/
@[simp]
theorem baseChangeWordAction_cons (Z : ι → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) (i : ι)
    (w : List ι) :
    baseChangeWordAction I π Z (i :: w) =
      lieSmoothVectorsBaseChangeDerivedAction I π (Z i) * baseChangeWordAction I π Z w :=
  (rfl)

/-- Along `1 ⊗ X`, the operator of a word is the real operator `dπ(X_w)`. -/
@[simp]
theorem baseChangeWordAction_one_tmul (X : ι → LeftInvariantDerivation I G) (w : List ι) :
    baseChangeWordAction I π (fun i ↦ (1 : 𝕜) ⊗ₜ X i) w = wordAction I π X w := by
  induction w with
  | nil => simp
  | cons i w ih => simp [ih]

/-- **The operator of a word is the action of its PBW monomial** in `U(𝕜 ⊗[ℝ] Lie(G))`. -/
theorem baseChangeWordAction_eq_lieSmoothVectorsBaseChangeEnvelopingAction
    (Z : ι → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) (w : List ι) :
    baseChangeWordAction I π Z w =
      lieSmoothVectorsBaseChangeEnvelopingAction I π
        (UniversalEnvelopingAlgebra.pbwMonomial 𝕜 (𝕜 ⊗[ℝ] LeftInvariantDerivation I G) Z w) := by
  induction w with
  | nil => rw [baseChangeWordAction_nil, UniversalEnvelopingAlgebra.pbwMonomial_nil, map_one]
  | cons i w ih =>
    rw [baseChangeWordAction_cons, ih, UniversalEnvelopingAlgebra.pbwMonomial_cons, map_mul,
      lieSmoothVectorsBaseChangeEnvelopingAction_ι]

/-- The word seminorm along `Z` as an explicit sum over words. -/
theorem baseChangeWordSeminorm_apply [Fintype ι] (Z : ι → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G)
    (k : ℕ) (v : lieSmoothVectors I π) :
    baseChangeWordSeminorm I π Z k v =
      ∑ w : BoundedWord ι k, ‖(baseChangeWordAction I π Z (List.ofFn w.2) v : V)‖ := by
  simp [baseChangeWordSeminorm_eq_endWordSeminorm, Seminorm.endWordSeminorm_apply,
    baseChangeWordAction]

/-! ### The Sobolev seminorms -/

variable (I π) in
/-- The vector `(dπ(Z^α) v)_{|α| ≤ k}` in the `ℓ²` product indexed by `SobolevIndex m k`, along a
family `Z` of `𝕜 ⊗[ℝ] Lie(G)`. -/
def baseChangeSobolevVector (Z : Fin m → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) (k : ℕ) :
    lieSmoothVectors I π →ₗ[𝕜] PiLp 2 (fun _ : SobolevIndex m k ↦ V) :=
  (WithLp.linearEquiv 2 𝕜 _).symm.toLinearMap ∘ₗ
    LinearMap.pi fun α ↦
      (lieSmoothVectors I π).subtype ∘ₗ baseChangeWordAction I π Z (monomialWord α.exponent)

/-- The `α`-component of `baseChangeSobolevVector` is `dπ(Z^α) v`. -/
@[simp]
theorem baseChangeSobolevVector_apply (Z : Fin m → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) (k : ℕ)
    (v : lieSmoothVectors I π) (α : SobolevIndex m k) :
    baseChangeSobolevVector I π Z k v α =
      (baseChangeWordAction I π Z (monomialWord α.exponent) v : V) :=
  (rfl)

variable (I π) in
/-- The Sobolev seminorm `Q^Z_k(v) = (∑_{|α| ≤ k} ‖dπ(Z^α) v‖²)^{1/2}` on smooth vectors, along a
family `Z` of `𝕜 ⊗[ℝ] Lie(G)`, summed over the ordered monomials `Z^α = Z₁^{α₁} ⋯ Z_m^{α_m}`. -/
def baseChangeSobolevSeminorm (Z : Fin m → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) (k : ℕ) :
    Seminorm 𝕜 (lieSmoothVectors I π) :=
  (normSeminorm 𝕜 (PiLp 2 fun _ : SobolevIndex m k ↦ V)).comp (baseChangeSobolevVector I π Z k)

/-- The Sobolev seminorm along `Z` as an explicit square root of a sum of squares. -/
theorem baseChangeSobolevSeminorm_apply (Z : Fin m → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G)
    (k : ℕ) (v : lieSmoothVectors I π) :
    baseChangeSobolevSeminorm I π Z k v =
      √(∑ α : SobolevIndex m k,
        ‖(baseChangeWordAction I π Z (monomialWord α.exponent) v : V)‖ ^ 2) := by
  simp [baseChangeSobolevSeminorm, PiLp.norm_eq_of_L2]

/-- **The Sobolev seminorms of `1 ⊗ X` are the real Sobolev seminorms of `X`.** -/
@[simp]
theorem baseChangeSobolevSeminorm_one_tmul (X : Fin m → LeftInvariantDerivation I G) (k : ℕ) :
    baseChangeSobolevSeminorm I π (fun i ↦ (1 : 𝕜) ⊗ₜ X i) k = sobolevSeminorm I π X k := by
  ext v
  simp [baseChangeSobolevSeminorm_apply, sobolevSeminorm_apply]

/-- The term of an ordered monomial is bounded by the Sobolev seminorm. -/
theorem norm_baseChangeWordAction_monomialWord_le_baseChangeSobolevSeminorm
    (Z : Fin m → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) {k : ℕ} (α : SobolevIndex m k)
    (v : lieSmoothVectors I π) :
    ‖(baseChangeWordAction I π Z (monomialWord α.exponent) v : V)‖ ≤
      baseChangeSobolevSeminorm I π Z k v := by
  rw [← baseChangeSobolevVector_apply]
  refine (PiLp.norm_apply_le (baseChangeSobolevVector I π Z k v) α).trans_eq ?_
  rw [baseChangeSobolevSeminorm_apply, PiLp.norm_eq_of_L2]
  simp only [baseChangeSobolevVector_apply]

/-- **The Sobolev seminorm is bounded by the word seminorm**, `Q^Z_k ≤ P^Z_k`: every ordered
monomial is a word, and the `ℓ²` norm of a finite family is at most its `ℓ¹` norm. -/
theorem baseChangeSobolevSeminorm_le_baseChangeWordSeminorm
    (Z : Fin m → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) (k : ℕ) (v : lieSmoothVectors I π) :
    baseChangeSobolevSeminorm I π Z k v ≤ baseChangeWordSeminorm I π Z k v := by
  classical
  set b : BoundedWord (Fin m) k → ℝ :=
    fun w ↦ ‖(baseChangeWordAction I π Z (List.ofFn w.2) v : V)‖
  have hb : ∀ α : SobolevIndex m k,
      ‖(baseChangeWordAction I π Z (monomialWord α.exponent) v : V)‖ = b α.toBoundedWord :=
    fun α ↦ by simp only [b, SobolevIndex.ofFn_toBoundedWord]
  have hsum : ∑ α : SobolevIndex m k, b α.toBoundedWord ≤ ∑ w, b w :=
    Finset.sum_le_sum_of_injOn SobolevIndex.toBoundedWord
      SobolevIndex.toBoundedWord_injective.injOn (Finset.subset_univ _) (fun _ _ ↦ le_rfl)
      fun _ _ _ ↦ norm_nonneg _
  rw [baseChangeSobolevSeminorm_apply, baseChangeWordSeminorm_apply, Real.sqrt_le_iff]
  refine ⟨Finset.sum_nonneg fun _ _ ↦ norm_nonneg _, ?_⟩
  simp_rw [hb]
  calc ∑ α : SobolevIndex m k, b α.toBoundedWord ^ 2
    _ ≤ (∑ α : SobolevIndex m k, b α.toBoundedWord) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ ↦ norm_nonneg _
    _ ≤ (∑ w, b w) ^ 2 := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) hsum 2

/-- **The word seminorm is bounded by a multiple of the Sobolev seminorm** along a family `Z`
spanning `𝕜 ⊗[ℝ] Lie(G)` over `𝕜`: for every order `k` there is `C_k` with
`P^Z_k ≤ C_k Q^Z_k`. -/
theorem exists_baseChangeWordSeminorm_le_mul_baseChangeSobolevSeminorm
    (Z : Fin m → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) (hZ : Submodule.span 𝕜 (Set.range Z) = ⊤)
    (k : ℕ) :
    ∃ C : ℝ, ∀ v : lieSmoothVectors I π,
      baseChangeWordSeminorm I π Z k v ≤ C * baseChangeSobolevSeminorm I π Z k v := by
  classical
  -- Every word of length at most `k` is a combination of the ordered monomials `Z^α`.
  have hspan : ∀ w : BoundedWord (Fin m) k, ∃ c : SobolevIndex m k → 𝕜,
      ∑ α, c α • UniversalEnvelopingAlgebra.pbwMonomial 𝕜 _ Z (monomialWord α.exponent) =
        UniversalEnvelopingAlgebra.pbwMonomial 𝕜 _ Z (List.ofFn w.2) := by
    intro w
    refine (Submodule.mem_span_range_iff_exists_fun 𝕜).1 ?_
    rw [UniversalEnvelopingAlgebra.range_pbwMonomial_monomialWord_eq_orderedPBWMonomials,
      UniversalEnvelopingAlgebra.span_orderedPBWMonomials_eq_pbwFiltration 𝕜 _ Z hZ]
    refine UniversalEnvelopingAlgebra.pbwFiltration_mono 𝕜 _ ?_
      (UniversalEnvelopingAlgebra.pbwMonomial_mem_pbwFiltration 𝕜 _ Z _)
    rw [List.length_ofFn]
    exact Nat.lt_succ_iff.1 w.1.isLt
  choose c hc using hspan
  refine ⟨∑ w, ∑ α, ‖c w α‖, fun v ↦ ?_⟩
  rw [baseChangeWordSeminorm_apply, Finset.sum_mul]
  refine Finset.sum_le_sum fun w _ ↦ ?_
  rw [baseChangeWordAction_eq_lieSmoothVectorsBaseChangeEnvelopingAction, ← hc w, Finset.sum_mul]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
    Submodule.coe_smul, ← baseChangeWordAction_eq_lieSmoothVectorsBaseChangeEnvelopingAction]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ ↦ ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left
    (norm_baseChangeWordAction_monomialWord_le_baseChangeSobolevSeminorm Z α v) (norm_nonneg _)

/-! ### The topology of the smooth vectors -/

omit [FiniteDimensional ℝ E] [T2Space G] [BoundarylessManifold I G] in
/-- A real spanning family `X` of `Lie(G)` gives the `𝕜`-spanning family `1 ⊗ X` of
`𝕜 ⊗[ℝ] Lie(G)`. -/
theorem span_one_tmul_eq_top {X : ι → LeftInvariantDerivation I G}
    (hX : Submodule.span ℝ (Set.range X) = ⊤) :
    Submodule.span 𝕜 (Set.range fun i ↦ (1 : 𝕜) ⊗ₜ[ℝ] X i) = ⊤ := by
  have h := congrArg (Submodule.baseChange 𝕜) hX
  rwa [Submodule.baseChange_span, Submodule.baseChange_top, ← Set.range_comp] at h

namespace LieSmoothSpace

variable (I π) in
/-- The Sobolev seminorms `Q^Z_k`, `k : ℕ`, along a family `Z` of `𝕜 ⊗[ℝ] Lie(G)`, on
`LieSmoothSpace I π X`. -/
def baseChangeSobolevSeminormFamily (X : ι → LeftInvariantDerivation I G)
    (Z : Fin m → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) :
    SeminormFamily 𝕜 (LieSmoothSpace I π X) ℕ :=
  fun k ↦ (baseChangeSobolevSeminorm I π Z k).comp (linearEquiv I π X).toLinearMap

@[simp]
theorem baseChangeSobolevSeminormFamily_apply (X : ι → LeftInvariantDerivation I G)
    (Z : Fin m → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) (k : ℕ) (v : LieSmoothSpace I π X) :
    baseChangeSobolevSeminormFamily I π X Z k v = baseChangeSobolevSeminorm I π Z k v.toSmooth := by
  rw [baseChangeSobolevSeminormFamily, Seminorm.comp_apply, LinearEquiv.coe_coe, linearEquiv_apply]

/-- **The Sobolev seminorms along a basis of the complexified Lie algebra define the topology of
the smooth vectors.** For a real spanning family `X` of `Lie(G)` and a family `Z` spanning
`𝕜 ⊗[ℝ] Lie(G)` over `𝕜`, the topology of `LieSmoothSpace I π X`, that of the word seminorms of
`X`, is the topology of the Sobolev seminorms `Q^Z_k`. -/
theorem withSeminorms_baseChangeSobolevSeminormFamily [Fintype ι]
    {X : ι → LeftInvariantDerivation I G} (hX : Submodule.span ℝ (Set.range X) = ⊤)
    {Z : Fin m → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G} (hZ : Submodule.span 𝕜 (Set.range Z) = ⊤) :
    WithSeminorms (baseChangeSobolevSeminormFamily I π X Z) := by
  have hX' := span_one_tmul_eq_top (𝕜 := 𝕜) hX
  -- `Z j = ∑ i, c j i • (1 ⊗ X i)` and `1 ⊗ X j = ∑ i, d j i • Z i`.
  choose c hc using fun j ↦ (Submodule.mem_span_range_iff_exists_fun 𝕜).1
    (hX' ▸ Submodule.mem_top (x := Z j))
  choose d hd using fun j ↦ (Submodule.mem_span_range_iff_exists_fun 𝕜).1
    (hZ ▸ Submodule.mem_top (x := (1 : 𝕜) ⊗ₜ[ℝ] X j))
  refine (withSeminorms I π X).congr
    (Seminorm.IsBounded.of_real fun k ↦
      ⟨{k}, (1 + ∑ j, ∑ i, ‖c j i‖) ^ k, fun v ↦ ?_⟩)
    (Seminorm.IsBounded.of_real fun k ↦ ?_)
  · rw [Finset.sup_singleton, LinearMap.id_apply, baseChangeSobolevSeminormFamily_apply,
      seminormFamily_apply, ← baseChangeWordSeminorm_one_tmul (𝕜 := 𝕜)]
    exact (baseChangeSobolevSeminorm_le_baseChangeWordSeminorm Z k v.toSmooth).trans
      (baseChangeWordSeminorm_le_of_eq_sum _ c (fun j ↦ (hc j).symm) k v.toSmooth)
  · obtain ⟨C, hC⟩ := exists_baseChangeWordSeminorm_le_mul_baseChangeSobolevSeminorm
      (π := π) Z hZ k
    refine ⟨{k}, (1 + ∑ j, ∑ i, ‖d j i‖) ^ k * C, fun v ↦ ?_⟩
    rw [Finset.sup_singleton, LinearMap.id_apply, baseChangeSobolevSeminormFamily_apply,
      seminormFamily_apply, ← baseChangeWordSeminorm_one_tmul (𝕜 := 𝕜), mul_assoc]
    exact (baseChangeWordSeminorm_le_of_eq_sum Z d (fun j ↦ (hd j).symm) k v.toSmooth).trans
      (mul_le_mul_of_nonneg_left (hC v.toSmooth) (pow_nonneg (by positivity) _))

end LieSmoothSpace

end ContRepresentation

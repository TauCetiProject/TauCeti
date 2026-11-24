/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyBounded.Basic
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Unitization
import TauCeti.Analysis.InnerProductSpace.GramSchmidtFactor

/-!
# Smith's lemma and completely bounded maps into commutative C⋆-algebras

For a linear map `u : A → M_n(ℂ)` from a C⋆-algebra into the `n × n` matrices (indexed by any
finite type), **Smith's lemma** says that the cb norm is attained at level `n`:
`‖u‖_cb = ‖uₙ‖`. Every bound on the level-`n` amplification `uₙ : M_n(A) → M_n(M_n(ℂ))` bounds
every amplification `uₘ`, so `u` is completely bounded exactly when `uₙ` is bounded.

For a bounded linear map `u : A → B` into a commutative C⋆-algebra, the cb norm equals the norm:
`‖u‖_cb = ‖u‖`.

## Main declarations

* `LinearMap.norm_map_le_of_forall_norm_map_le`: a bound `‖uₙ x‖ ≤ c ‖x‖` at level `n` gives
  `‖uₘ x‖ ≤ c ‖x‖` at every level, for maps `u : A → M_n(ℂ)` (Smith's lemma).
* `LinearMap.isCompletelyBounded_iff_exists_bound_level`,
  `LinearMap.cbNorm_le_iff_level`: complete boundedness and the cb norm of `u : A → M_n(ℂ)` are
  read off at level `n`.
* `LinearMap.cbNorm_eq_opNorm_level`: `‖u‖_cb = ‖uₙ‖`, for `uₙ` given as a continuous linear map.
* `ContinuousLinearMap.isCompletelyBounded_toLinearMap_of_comm`,
  `ContinuousLinearMap.cbNorm_toLinearMap_of_comm`: a bounded map into a commutative C⋆-algebra
  is completely bounded with `‖u‖_cb = ‖u‖`.

## Implementation notes

For Smith's lemma, the norm of `uₘ x ∈ M_m(M_n(ℂ)) ≅ M_{m × n}(ℂ)` is tested against vectors
`v, w ∈ ℂ^{m × n}`. Read `v` as `n` columns `vᵣ ∈ ℂᵐ`; Gram–Schmidt gives `n` pairwise orthogonal
vectors `eₜ ∈ ℂᵐ`, each a unit vector or zero, spanning every `vᵣ`. So `v = e v'` with
`v' ∈ ℂ^{n × n}` of the same norm, and likewise `w = f w'`. The pairing `⟪w, uₘ(x) v⟫` becomes
`⟪w', uₙ(y) v'⟫` for the compression `y = [∑ k l, (eₜ k fₜ' l*) x k l]_{t t'} ∈ M_n(A)`, and
`‖y‖ ≤ ‖x‖` because the maps `a ↦ (∑ t, eₜ k aₜ)ₖ` are contractions of Hilbert `A`-modules.

For a commutative unital target `B`, the Gelfand transform reduces the norm of
`⟪w, uₘ(x) v⟫ ∈ B` to its values under characters `χ`, and `χ ∘ u` is a bounded functional, whose
cb norm is its norm by `ContinuousLinearMap.cbNorm_toLinearMap`. A nonunital target embeds
isometrically in its unitization, which is commutative and unital.

## References

* R. R. Smith, *Completely bounded maps between C⋆-algebras*, J. London Math. Soc. (2) 27
  (1983), Theorem 2.10.
* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Chapters 3 and 8.
-/

public section

open scoped ComplexOrder InnerProductSpace
open WithCStarModule CStarModule

namespace LinearMap

section Smith

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- The pairing of the level-`κ` amplification of `u : A → M_n(ℂ)`, read in `M_{κ × n}(ℂ)`,
with vectors `v, w ∈ ℂ^{κ × n}`. -/
private theorem inner_toCLM_comp_map {κ ι : Type*} [Fintype κ] [Fintype ι]
    (u : A →ₗ[ℂ] CStarMatrix ι ι ℂ) (x : CStarMatrix κ κ A)
    (v w : C⋆ᵐᵒᵈ(ℂ, κ × ι → ℂ)) :
    ⟪w, CStarMatrix.toCLM (CStarMatrix.compStarAlgEquiv ℂ κ ι ℂ (x.map u)) v⟫_ℂ =
      ∑ r, ∑ s, u (∑ k, ∑ l, (v (k, r) * star (w (l, s))) • x k l) r s := by
  simp only [pi_inner, CStarMatrix.toCLM_apply_eq_sum, equiv_symm_pi_apply, inner_def,
    CStarMatrix.compStarAlgEquiv_apply, CStarMatrix.map_apply, map_sum, map_smul,
    CStarMatrix.sum_apply, CStarMatrix.smul_apply, Fintype.sum_prod_type, Finset.sum_mul,
    smul_eq_mul]
  simp only [← Fintype.sum_prod_type']
  -- reindex `(l, s, k, r) ↦ (r, s, k, l)`
  exact Fintype.sum_equiv
    ⟨fun p => (p.2.2.2, p.2.1, p.2.2.1, p.1), fun q => (q.2.2.2, q.2.1, q.2.2.1, q.1),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun _ => by
    dsimp only [Equiv.coe_fn_mk]
    ring

omit [PartialOrder A] [StarOrderedRing A] in
/-- Factoring the test vectors `v = e v'` and `w = f w'` turns the scalar compression of `x` into
the scalar compression of `CStarMatrix.compress e f x`. -/
private theorem sum_smul_eq_sum_smul_compress {κ ι : Type*} [Fintype κ] [Fintype ι]
    {e f : ι → κ → ℂ} {v w : κ → ι → ℂ} {v' w' : ι → ι → ℂ}
    (hv : ∀ k r, v k r = ∑ t, e t k * v' t r) (hw : ∀ l s, w l s = ∑ t, f t l * w' t s)
    (x : CStarMatrix κ κ A) (r s : ι) :
    ∑ k, ∑ l, (v k r * star (w l s)) • x k l =
      ∑ t, ∑ t', (v' t r * star (w' t' s)) • CStarMatrix.compress e f x t t' := by
  simp only [hv, hw, CStarMatrix.compress_apply, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  simp only [← Fintype.sum_prod_type']
  -- reindex `(k, l, t', t) ↦ (t, t', k, l)`
  exact Fintype.sum_equiv
    ⟨fun p => (p.2.2.2, p.2.2.1, p.1, p.2.1), fun q => (q.2.2.1, q.2.2.2, q.2.1, q.1),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun _ => by
    dsimp only [Equiv.coe_fn_mk]
    congr 1
    ring

/-- **Smith's lemma.** For a linear map `u : A → M_n(ℂ)`, a bound `‖uₙ y‖ ≤ c ‖y‖` on the
level-`n` amplification bounds every amplification: `‖uₘ x‖ ≤ c ‖x‖` for `x ∈ M_κ(A)`. -/
theorem norm_map_le_of_forall_norm_map_le {ι : Type*} [Fintype ι] {u : A →ₗ[ℂ] CStarMatrix ι ι ℂ}
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ y : CStarMatrix ι ι A, ‖y.map u‖ ≤ c * ‖y‖)
    {κ : Type*} [Fintype κ] (x : CStarMatrix κ κ A) : ‖x.map u‖ ≤ c * ‖x‖ := by
  rw [← StarAlgEquiv.norm_map (CStarMatrix.compStarAlgEquiv ℂ κ ι ℂ)]
  refine (CStarMatrix.norm_le_of_forall_inner_le
    (M := CStarMatrix.compStarAlgEquiv ℂ κ ι ℂ (x.map u)) (C := c.toNNReal * ‖x‖₊)
    fun v w => ?_).trans_eq (by rw [NNReal.coe_mul, Real.coe_toNNReal _ hc, coe_nnNorm])
  obtain ⟨e, v', hv, he, he₁, hv'⟩ := InnerProductSpace.exists_orthogonal_factor fun k r => v (k, r)
  obtain ⟨f, w', hw, hf, hf₁, hw'⟩ := InnerProductSpace.exists_orthogonal_factor fun l s => w (l, s)
  let V : C⋆ᵐᵒᵈ(ℂ, ι × ι → ℂ) := (equiv ℂ (ι × ι → ℂ)).symm fun p => v' p.1 p.2
  let W : C⋆ᵐᵒᵈ(ℂ, ι × ι → ℂ) := (equiv ℂ (ι × ι → ℂ)).symm fun p => w' p.1 p.2
  have hV : ‖V‖ = ‖v‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq_sum, norm_sq_eq_sum,
      Fintype.sum_prod_type, Fintype.sum_prod_type]
    simpa only [V, equiv_symm_pi_apply] using hv'
  have hW : ‖W‖ = ‖w‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq_sum, norm_sq_eq_sum,
      Fintype.sum_prod_type, Fintype.sum_prod_type]
    simpa only [W, equiv_symm_pi_apply] using hw'
  let Z := CStarMatrix.compStarAlgEquiv ℂ ι ι ℂ ((CStarMatrix.compress e f x).map u)
  have key : ⟪w, CStarMatrix.toCLM (CStarMatrix.compStarAlgEquiv ℂ κ ι ℂ (x.map u)) v⟫_ℂ =
      ⟪W, CStarMatrix.toCLM Z V⟫_ℂ := by
    rw [inner_toCLM_comp_map, inner_toCLM_comp_map]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    simp only [sum_smul_eq_sum_smul_compress hv hw x r s, V, W, equiv_symm_pi_apply]
  have hZ : ‖Z‖ ≤ c * ‖x‖ := by
    rw [StarAlgEquiv.norm_map]
    exact (h _).trans (mul_le_mul_of_nonneg_left (CStarMatrix.norm_compress_le he he₁ hf hf₁ x) hc)
  rw [key]
  calc ‖⟪W, CStarMatrix.toCLM Z V⟫_ℂ‖ ≤ ‖W‖ * ‖CStarMatrix.toCLM Z V‖ := norm_inner_le _
    _ ≤ ‖W‖ * (‖Z‖ * ‖V‖) := by
      gcongr
      exact (CStarMatrix.toCLM Z).le_opNorm V
    _ ≤ ‖W‖ * ((c * ‖x‖) * ‖V‖) := by gcongr
    _ = _ := by rw [hV, hW, NNReal.coe_mul, Real.coe_toNNReal _ hc, coe_nnNorm]; ring

/-- A linear map `u : A → M_n(ℂ)` is completely bounded exactly when its level-`n` amplification
is bounded. -/
theorem isCompletelyBounded_iff_exists_bound_level {ι : Type*} [Fintype ι]
    {u : A →ₗ[ℂ] CStarMatrix ι ι ℂ} :
    IsCompletelyBounded u ↔ ∃ c : ℝ, ∀ y : CStarMatrix ι ι A, ‖y.map u‖ ≤ c * ‖y‖ := by
  refine ⟨fun hu => ⟨cbNorm u, fun y => norm_map_le_cbNorm_mul hu y⟩, fun ⟨c, hc⟩ => ?_⟩
  refine isCompletelyBounded_iff_exists_bound.mpr ⟨max c 0, fun m x =>
    norm_map_le_of_forall_norm_map_le (le_max_right _ _) (fun y => (hc y).trans ?_) x⟩
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

/-- For a completely bounded `u : A → M_n(ℂ)`, `‖u‖_cb ≤ c` exactly when `c` bounds the level-`n`
amplification. -/
theorem cbNorm_le_iff_level {ι : Type*} [Fintype ι] {u : A →ₗ[ℂ] CStarMatrix ι ι ℂ}
    (hu : IsCompletelyBounded u) {c : ℝ} (hc : 0 ≤ c) :
    cbNorm u ≤ c ↔ ∀ y : CStarMatrix ι ι A, ‖y.map u‖ ≤ c * ‖y‖ :=
  ⟨fun h y => (norm_map_le_cbNorm_mul hu y).trans (by gcongr),
    fun h => cbNorm_le_of_bound hc fun _ x => norm_map_le_of_forall_norm_map_le hc h x⟩

/-- **Smith's lemma**, `‖u‖_cb = ‖uₙ‖`: the cb norm of `u : A → M_n(ℂ)` is the operator norm of
its level-`n` amplification `uₙ : M_n(A) → M_n(M_n(ℂ))`. -/
theorem cbNorm_eq_opNorm_level {ι : Type*} [Fintype ι] {u : A →ₗ[ℂ] CStarMatrix ι ι ℂ}
    (uₙ : CStarMatrix ι ι A →L[ℂ] CStarMatrix ι ι (CStarMatrix ι ι ℂ))
    (huₙ : ∀ y, uₙ y = y.map u) : cbNorm u = ‖uₙ‖ := by
  have hu : IsCompletelyBounded u :=
    isCompletelyBounded_iff_exists_bound_level.mpr ⟨‖uₙ‖, fun y => huₙ y ▸ uₙ.le_opNorm y⟩
  refine le_antisymm ((cbNorm_le_iff_level hu (norm_nonneg uₙ)).mpr fun y => ?_) ?_
  · exact huₙ y ▸ uₙ.le_opNorm y
  · exact uₙ.opNorm_le_bound (cbNorm_nonneg u) fun y => huₙ y ▸ norm_map_le_cbNorm_mul hu y

end Smith

end LinearMap

namespace ContinuousLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The amplifications of a bounded map into a commutative unital C⋆-algebra are bounded by its
norm. -/
private theorem norm_map_le_opNorm_mul_of_unital {B : Type*} [CommCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] (u : A →L[ℂ] B) {κ : Type*} [Fintype κ]
    (x : CStarMatrix κ κ A) : ‖x.map (u : A →ₗ[ℂ] B)‖ ≤ ‖u‖ * ‖x‖ := by
  refine (CStarMatrix.norm_le_of_forall_inner_le (M := x.map (u : A →ₗ[ℂ] B))
    (C := ‖u‖₊ * ‖x‖₊) fun v w => ?_).trans_eq (by rw [NNReal.coe_mul, coe_nnNorm, coe_nnNorm])
  rw [← (AddMonoidHomClass.isometry_iff_norm _).mp (gelfandTransform_isometry B),
    ContinuousMap.norm_le _ (by positivity)]
  intro χ
  rw [WeakDual.gelfandTransform_apply_apply]
  let ψ : A →L[ℂ] ℂ := (WeakDual.toStrongDual (χ : WeakDual ℂ B)).comp u
  have hχ (b : B) : ‖χ b‖ ≤ ‖b‖ := by
    simpa using (WeakDual.toStrongDual (χ : WeakDual ℂ B)).le_of_opNorm_le
      (WeakDual.CharacterSpace.norm_toStrongDual_le_one χ) b
  have hψ : ‖ψ‖ ≤ ‖u‖ := (opNorm_comp_le _ _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (WeakDual.CharacterSpace.norm_toStrongDual_le_one χ))
  have hvec (v : C⋆ᵐᵒᵈ(B, κ → B)) : ‖(equiv ℂ (κ → ℂ)).symm fun i => χ (v i)‖ ≤ ‖v‖ := by
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, pi_norm_sq,
      pi_norm_sq]
    simp only [equiv_symm_pi_apply, inner_def, ← map_star χ, ← map_mul, ← map_sum]
    exact hχ _
  have key : χ ⟪w, CStarMatrix.toCLM (x.map (u : A →ₗ[ℂ] B)) v⟫_B =
      ⟪(equiv ℂ (κ → ℂ)).symm fun i => χ (w i),
        CStarMatrix.toCLM (x.map (ψ : A →ₗ[ℂ] ℂ)) ((equiv ℂ (κ → ℂ)).symm fun i => χ (v i))⟫_ℂ := by
    simp [pi_inner, CStarMatrix.toCLM_apply_eq_sum, inner_def, map_sum, map_mul, map_star, ψ]
  rw [key]
  refine (norm_inner_le _).trans ?_
  calc _ ≤ ‖w‖ * (‖x.map (ψ : A →ₗ[ℂ] ℂ)‖ * ‖v‖) := by
        gcongr
        · exact hvec w
        · exact ((CStarMatrix.toCLM (x.map (ψ : A →ₗ[ℂ] ℂ))).le_opNorm _).trans
            (mul_le_mul_of_nonneg_left (hvec v) (norm_nonneg _))
    _ ≤ ‖w‖ * ((‖u‖ * ‖x‖) * ‖v‖) := by
        gcongr
        refine (LinearMap.norm_map_le_cbNorm_mul (isCompletelyBounded_toLinearMap ψ) x).trans ?_
        rw [cbNorm_toLinearMap]
        gcongr
    _ = _ := by rw [NNReal.coe_mul, coe_nnNorm, coe_nnNorm]; ring

variable {B : Type*} [NonUnitalCommCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The amplifications of a bounded map into a commutative C⋆-algebra are bounded by its norm:
compose with the isometric inclusion into the unitization. -/
private theorem norm_map_le_opNorm_mul_of_comm (u : A →L[ℂ] B) {κ : Type*} [Fintype κ]
    (x : CStarMatrix κ κ A) : ‖x.map (u : A →ₗ[ℂ] B)‖ ≤ ‖u‖ * ‖x‖ := by
  let ι := Unitization.inrNonUnitalStarAlgHom ℂ B
  let u' : A →L[ℂ] Unitization ℂ B := ((ι : B →ₗ[ℂ] Unitization ℂ B) ∘ₗ u).mkContinuous ‖u‖
    fun a => by simpa [ι, Unitization.norm_inr] using u.le_opNorm a
  have hι : Function.Injective (CStarMatrix.mapₙₐ (n := κ) ι) := fun M N h => by
    ext i j
    exact Unitization.inr_injective (congr($h i j))
  have hmap : CStarMatrix.mapₙₐ ι (x.map (u : A →ₗ[ℂ] B)) =
      x.map (u' : A →ₗ[ℂ] Unitization ℂ B) := by
    refine CStarMatrix.ext fun i j => ?_
    simp [u', ι, CStarMatrix.mapₙₐ_apply]
  rw [← NonUnitalStarAlgHom.norm_map _ hι, hmap]
  exact (norm_map_le_opNorm_mul_of_unital u' x).trans (by
    gcongr
    exact LinearMap.mkContinuous_norm_le _ (norm_nonneg u) _)

/-- A bounded linear map into a commutative C⋆-algebra is completely bounded. -/
theorem isCompletelyBounded_toLinearMap_of_comm (u : A →L[ℂ] B) :
    (u : A →ₗ[ℂ] B).IsCompletelyBounded :=
  LinearMap.isCompletelyBounded_iff_exists_bound.mpr
    ⟨‖u‖, fun _ x => norm_map_le_opNorm_mul_of_comm u x⟩

/-- **A bounded linear map into a commutative C⋆-algebra has cb norm equal to its norm.** -/
theorem cbNorm_toLinearMap_of_comm (u : A →L[ℂ] B) : (u : A →ₗ[ℂ] B).cbNorm = ‖u‖ :=
  le_antisymm
    (LinearMap.cbNorm_le_of_bound (norm_nonneg u) fun _ x => norm_map_le_opNorm_mul_of_comm u x) <|
    u.opNorm_le_bound (LinearMap.cbNorm_nonneg _) fun a =>
      LinearMap.norm_apply_le_cbNorm_mul (isCompletelyBounded_toLinearMap_of_comm u) a

end ContinuousLinearMap

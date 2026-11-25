/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyBounded.Basic
import Mathlib.Analysis.CStarAlgebra.Hom
import TauCeti.Analysis.InnerProductSpace.GramSchmidt.Factor

/-!
# Smith's lemma

For a linear map `u : A → M_n(ℂ)` from a C⋆-algebra into the `n × n` matrices (indexed by any
finite type), **Smith's lemma** says that the cb norm is attained at level `n`:
`‖u‖_cb = ‖uₙ‖`. Every bound on the level-`n` amplification `uₙ : M_n(A) → M_n(M_n(ℂ))` bounds
every amplification `uₘ`, so `u` is completely bounded exactly when `uₙ` is bounded.

## Main declarations

* `LinearMap.norm_map_le_of_forall_norm_map_le`: a bound `‖uₙ x‖ ≤ c ‖x‖` at level `n` gives
  `‖uₘ x‖ ≤ c ‖x‖` at every level, for maps `u : A → M_n(ℂ)` (Smith's lemma).
* `LinearMap.isCompletelyBounded_iff_exists_bound_level`,
  `LinearMap.cbNorm_le_iff_level`: complete boundedness and the cb norm of `u : A → M_n(ℂ)` are
  read off at level `n`.
* `LinearMap.cbNorm_eq_opNorm_level`: `‖u‖_cb = ‖uₙ‖`, for `uₙ` given as a continuous linear map.

## Implementation notes

For Smith's lemma, the norm of `uₘ x ∈ M_m(M_n(ℂ)) ≅ M_{m × n}(ℂ)` is tested against vectors
`v, w ∈ ℂ^{m × n}`. Read `v` as `n` columns `vᵣ ∈ ℂᵐ`; Gram–Schmidt gives `n` pairwise orthogonal
vectors `eₜ ∈ ℂᵐ`, each a unit vector or zero, spanning every `vᵣ`. So `v = e v'` with
`v' ∈ ℂ^{n × n}` of the same norm, and likewise `w = f w'`. The pairing `⟪w, uₘ(x) v⟫` becomes
`⟪w', uₙ(y) v'⟫` for the compression `y = [∑ k l, (eₜ k fₜ' l*) x k l]_{t t'} ∈ M_n(A)`, and
`‖y‖ ≤ ‖x‖` because the maps `a ↦ (∑ t, eₜ k aₜ)ₖ` are contractions of Hilbert `A`-modules.

## References

* R. R. Smith, *Completely bounded maps between C⋆-algebras*, J. London Math. Soc. (2) 27
  (1983), Theorem 2.10.
* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Chapter 8.
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

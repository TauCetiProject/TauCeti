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
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

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

/-- Gram–Schmidt factorization of `n` vectors `vᵣ = (v k r)ₖ ∈ ℂ^κ`: `v k r = ∑ t, e t k * v' t r`
for pairwise orthogonal vectors `e t` of norm at most `1`, with `‖v'‖ = ‖v‖`. -/
private theorem exists_factor_fin {κ : Type*} [Fintype κ] {n : ℕ} (v : κ → Fin n → ℂ) :
    ∃ (e : Fin n → κ → ℂ) (v' : Fin n → Fin n → ℂ),
      (∀ k r, v k r = ∑ t, e t k * v' t r) ∧
      (∀ t t', t ≠ t' → ∑ k, e t k * star (e t' k) = 0) ∧
      (∀ t, ∑ k, ‖e t k‖ ^ 2 ≤ 1) ∧
      ∑ t, ∑ r, ‖v' t r‖ ^ 2 = ∑ k, ∑ r, ‖v k r‖ ^ 2 := by
  let c : Fin n → EuclideanSpace ℂ κ := fun r => WithLp.toLp 2 fun k => v k r
  let E := InnerProductSpace.gramSchmidtNormed ℂ c
  have horth (t t' : Fin n) (h : t ≠ t') : ⟪E t', E t⟫_ℂ = 0 := by
    simp [E, InnerProductSpace.gramSchmidtNormed,
      InnerProductSpace.gramSchmidt_orthogonal ℂ c h.symm]
  have hnorm (t : Fin n) : ‖E t‖ ^ 2 • E t = E t := by
    by_cases h : E t = 0
    · simp [h]
    · rw [InnerProductSpace.gramSchmidtNormed_unit_length' h, one_pow, one_smul]
  have hrec (r : Fin n) : c r = ∑ t, ⟪E t, c r⟫_ℂ • E t := by
    have hmem : c r ∈ Submodule.span ℂ (Set.range E) := by
      rw [InnerProductSpace.span_gramSchmidtNormed_range, InnerProductSpace.span_gramSchmidt]
      exact Submodule.subset_span ⟨r, rfl⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
    have hcoef (t : Fin n) : ⟪E t, c r⟫_ℂ = a t * (‖E t‖ ^ 2 : ℝ) := by
      rw [← ha, inner_sum, Finset.sum_eq_single t]
      · rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
        norm_cast
      · exact fun t' _ h => by rw [inner_smul_right, horth t' t h, mul_zero]
      · simp
    calc c r = ∑ t, a t • E t := ha.symm
      _ = _ := Finset.sum_congr rfl fun t _ => by rw [hcoef t, mul_smul, Complex.coe_smul, hnorm]
  have hparseval (r : Fin n) : ∑ t, ‖⟪E t, c r⟫_ℂ‖ ^ 2 = ‖c r‖ ^ 2 := by
    have h := congrArg (fun z => ⟪c r, z⟫_ℂ) (hrec r)
    simp only [inner_sum, inner_smul_right, ← inner_conj_symm (c r) (E _),
      RCLike.mul_conj, inner_self_eq_norm_sq_to_K] at h
    exact_mod_cast h.symm
  refine ⟨fun t k => E t k, fun t r => ⟪E t, c r⟫_ℂ, fun k r => ?_, fun t t' h => ?_,
    fun t => ?_, ?_⟩
  · have := congrArg (fun z : EuclideanSpace ℂ κ => z k) (hrec r)
    simpa [c, mul_comm] using this
  · simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct] using horth t t' h
  · rw [← EuclideanSpace.norm_sq_eq]
    by_cases h : E t = 0
    · simp [h]
    · rw [InnerProductSpace.gramSchmidtNormed_unit_length' h, one_pow]
  · rw [Finset.sum_comm]
    simp_rw [hparseval, EuclideanSpace.norm_sq_eq, c]
    exact Finset.sum_comm

/-- Gram–Schmidt factorization of vectors `vᵣ = (v k r)ₖ ∈ ℂ^κ` indexed by a finite type `ι`:
`v k r = ∑ t, e t k * v' t r` for pairwise orthogonal vectors `e t` of norm at most `1`, with
`‖v'‖ = ‖v‖`. -/
private theorem exists_factor {κ ι : Type*} [Fintype κ] [Fintype ι] (v : κ → ι → ℂ) :
    ∃ (e : ι → κ → ℂ) (v' : ι → ι → ℂ),
      (∀ k r, v k r = ∑ t, e t k * v' t r) ∧
      (∀ t t', t ≠ t' → ∑ k, e t k * star (e t' k) = 0) ∧
      (∀ t, ∑ k, ‖e t k‖ ^ 2 ≤ 1) ∧
      ∑ t, ∑ r, ‖v' t r‖ ^ 2 = ∑ k, ∑ r, ‖v k r‖ ^ 2 := by
  classical
  let σ := Fintype.equivFin ι
  obtain ⟨e, v', hv, he, he₁, hv'⟩ := exists_factor_fin fun k i => v k (σ.symm i)
  refine ⟨fun t => e (σ t), fun t r => v' (σ t) (σ r), fun k r => ?_,
    fun t t' h => he _ _ (σ.injective.ne h), fun t => he₁ _, ?_⟩
  · rw [← σ.symm_apply_apply r, hv, ← σ.sum_comp]
    simp
  · calc ∑ t, ∑ r, ‖v' (σ t) (σ r)‖ ^ 2 = ∑ t, ∑ r, ‖v' t r‖ ^ 2 :=
          (Finset.sum_congr rfl fun t _ => σ.sum_comp fun r => ‖v' (σ t) r‖ ^ 2).trans
            (σ.sum_comp fun t => ∑ r, ‖v' t r‖ ^ 2)
      _ = ∑ k, ∑ r, ‖v k (σ.symm r)‖ ^ 2 := hv'
      _ = _ := Finset.sum_congr rfl fun k _ => σ.symm.sum_comp fun r => ‖v k r‖ ^ 2

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The compression `[∑ k l, (e t k * star (f t' l)) • x k l]_{t t'}` of `x ∈ M_κ(A)` to `M_n(A)`
by the vectors `e t, f t' ∈ ℂ^κ`. -/
private def compress {κ ι : Type*} [Fintype κ] (e f : ι → κ → ℂ)
    (x : CStarMatrix κ κ A) : CStarMatrix ι ι A :=
  CStarMatrix.ofMatrix (Matrix.of fun t t' => ∑ k, ∑ l, (e t k * star (f t' l)) • x k l)

omit [PartialOrder A] [StarOrderedRing A] in
private theorem compress_apply {κ ι : Type*} [Fintype κ] (e f : ι → κ → ℂ)
    (x : CStarMatrix κ κ A) (t t' : ι) :
    compress e f x t t' = ∑ k, ∑ l, (e t k * star (f t' l)) • x k l :=
  (rfl)

/-- Compressing by pairwise orthogonal vectors of norm at most `1` does not increase norms. -/
private theorem norm_compress_le {κ ι : Type*} [Fintype κ] [Fintype ι] {e f : ι → κ → ℂ}
    (he : ∀ t t', t ≠ t' → ∑ k, e t k * star (e t' k) = 0) (he₁ : ∀ t, ∑ k, ‖e t k‖ ^ 2 ≤ 1)
    (hf : ∀ t t', t ≠ t' → ∑ k, f t k * star (f t' k) = 0) (hf₁ : ∀ t, ∑ k, ‖f t k‖ ^ 2 ≤ 1)
    (x : CStarMatrix κ κ A) : ‖compress e f x‖ ≤ ‖x‖ := by
  refine CStarMatrix.norm_le_of_forall_inner_le (C := ‖x‖₊) fun a b => ?_
  let a' : C⋆ᵐᵒᵈ(A, κ → A) := (equiv A (κ → A)).symm fun k => ∑ t, e t k • a t
  let b' : C⋆ᵐᵒᵈ(A, κ → A) := (equiv A (κ → A)).symm fun l => ∑ t, f t l • b t
  have h : ⟪b, CStarMatrix.toCLM (compress e f x) a⟫_A = ⟪b', CStarMatrix.toCLM x a'⟫_A := by
    simp only [pi_inner, CStarMatrix.toCLM_apply_eq_sum, equiv_symm_pi_apply, inner_def,
      compress_apply, a', b', star_sum, star_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
      mul_smul_comm, Finset.smul_sum, smul_smul]
    calc _ = ∑ t', ∑ l, ∑ t, ∑ k, (e t k * star (f t' l)) • (a t * x k l * star (b t')) :=
          Finset.sum_congr rfl fun _ _ => (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans
            Finset.sum_comm
      _ = _ := Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl
          fun _ _ => Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl
            fun _ _ => by rw [mul_comm]))
  rw [h]
  calc ‖⟪b', CStarMatrix.toCLM x a'⟫_A‖ ≤ ‖b'‖ * ‖CStarMatrix.toCLM x a'‖ := norm_inner_le _
    _ ≤ ‖b‖ * (‖x‖ * ‖a‖) := by
      gcongr
      · exact norm_equiv_symm_sum_smul_le hf hf₁ b
      · exact ((CStarMatrix.toCLM x).le_opNorm a').trans
          (mul_le_mul_of_nonneg_left (norm_equiv_symm_sum_smul_le he he₁ a) (norm_nonneg _))
    _ = _ := by simp only [coe_nnNorm]; ring

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
  calc _ = ∑ l, ∑ s, ∑ r, ∑ k, v (k, r) * u (x k l) r s * star (w (l, s)) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ l, ∑ r, ∑ s, ∑ k, v (k, r) * u (x k l) r s * star (w (l, s)) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ r, ∑ s, ∑ l, ∑ k, v (k, r) * u (x k l) r s * star (w (l, s)) :=
        Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          by ring)

omit [PartialOrder A] [StarOrderedRing A] in
/-- Factoring the test vectors `v = e v'` and `w = f w'` turns the scalar compression of `x` into
the scalar compression of `compress e f x`. -/
private theorem sum_smul_eq_sum_smul_compress {κ ι : Type*} [Fintype κ] [Fintype ι]
    {e f : ι → κ → ℂ} {v w : κ → ι → ℂ} {v' w' : ι → ι → ℂ}
    (hv : ∀ k r, v k r = ∑ t, e t k * v' t r) (hw : ∀ l s, w l s = ∑ t, f t l * w' t s)
    (x : CStarMatrix κ κ A) (r s : ι) :
    ∑ k, ∑ l, (v k r * star (w l s)) • x k l =
      ∑ t, ∑ t', (v' t r * star (w' t' s)) • compress e f x t t' := by
  simp only [hv, hw, compress_apply, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  calc _ = ∑ k, ∑ t, ∑ l, ∑ t',
        (e t k * v' t r * (star (w' t' s) * star (f t' l))) • x k l :=
        Finset.sum_congr rfl fun _ _ =>
          (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
    _ = ∑ t, ∑ t', ∑ k, ∑ l, (e t k * v' t r * (star (w' t' s) * star (f t' l))) • x k l :=
        Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ =>
          (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm)
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring_nf

/-- **Smith's lemma.** For a linear map `u : A → M_n(ℂ)`, a bound `‖uₙ y‖ ≤ c ‖y‖` on the
level-`n` amplification bounds every amplification: `‖uₘ x‖ ≤ c ‖x‖` for `x ∈ M_κ(A)`. -/
theorem norm_map_le_of_forall_norm_map_le {ι : Type*} [Fintype ι] {u : A →ₗ[ℂ] CStarMatrix ι ι ℂ}
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ y : CStarMatrix ι ι A, ‖y.map u‖ ≤ c * ‖y‖)
    {κ : Type*} [Fintype κ] (x : CStarMatrix κ κ A) : ‖x.map u‖ ≤ c * ‖x‖ := by
  rw [← StarAlgEquiv.norm_map (CStarMatrix.compStarAlgEquiv ℂ κ ι ℂ)]
  refine (CStarMatrix.norm_le_of_forall_inner_le
    (M := CStarMatrix.compStarAlgEquiv ℂ κ ι ℂ (x.map u)) (C := c.toNNReal * ‖x‖₊)
    fun v w => ?_).trans_eq (by rw [NNReal.coe_mul, Real.coe_toNNReal _ hc, coe_nnNorm])
  obtain ⟨e, v', hv, he, he₁, hv'⟩ := exists_factor fun k r => v (k, r)
  obtain ⟨f, w', hw, hf, hf₁, hw'⟩ := exists_factor fun l s => w (l, s)
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
  let Z := CStarMatrix.compStarAlgEquiv ℂ ι ι ℂ ((compress e f x).map u)
  have key : ⟪w, CStarMatrix.toCLM (CStarMatrix.compStarAlgEquiv ℂ κ ι ℂ (x.map u)) v⟫_ℂ =
      ⟪W, CStarMatrix.toCLM Z V⟫_ℂ := by
    rw [inner_toCLM_comp_map, inner_toCLM_comp_map]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    simp only [sum_smul_eq_sum_smul_compress hv hw x r s, V, W, equiv_symm_pi_apply]
  have hZ : ‖Z‖ ≤ c * ‖x‖ := by
    rw [StarAlgEquiv.norm_map]
    exact (h _).trans (mul_le_mul_of_nonneg_left (norm_compress_le he he₁ hf hf₁ x) hc)
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

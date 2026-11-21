/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Orthogonal
public import Mathlib.Analysis.CStarAlgebra.Projection
public import TauCeti.Analysis.CStarAlgebra.Basic
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
import Mathlib.Algebra.Order.Star.Projection
import Mathlib.Algebra.Star.NonUnitalSubalgebra
import TauCeti.Algebra.Star.Projection.Family
import TauCeti.Topology.Algebra.NonUnitalStarAlgebra

/-!
# Norm stability of projections and finite orthogonal projection families in C⋆-algebras

Single star projections and finite pairwise-orthogonal projection families are **uniformly
norm-stable** across all (not necessarily unital) C⋆-algebras: for every `ε > 0` (and finite index
type `ι`), there exists `δ > 0` depending only on `ε` (and `ι`), uniformly across all C⋆-algebras
`A` and closed non-unital `𝕜'`-`⋆`-subalgebras `s` (for any scalar monoid `𝕜'` over `ℝ`), such that
any `δ`-approximate projection (or family) in `s` lies within `ε` of an exact one in `s`. This
feeds lifting projections in quotients and inductive limits for K-theory and stabilizing diagonal
projections in `TauCeti.Analysis.CStarAlgebra.MatrixUnits.Stability`.

## Main results

* `IsStarProjection.eq_of_le_of_norm_sub_lt_one`, `TauCeti.exists_isStarProjection_mem_of_approx`,
  `TauCeti.exists_pos_forall_exists_isStarProjection_mem_norm_sub_lt`,
  `TauCeti.exists_pos_forall_exists_isStarProjection_norm_sub_lt`,
  `TauCeti.exists_pos_forall_exists_pairwise_isStarOrtho_isStarProjection_mem_norm_sub_lt`,
  `TauCeti.exists_pos_forall_exists_pairwise_isStarOrtho_isStarProjection_norm_sub_lt`.

## References

* B. Blackadar, *Operator Algebras*, Springer (2006), Proposition II.8.3.23.
* M. Rørdam, F. Larsen and N. Laustsen, *An Introduction to K-Theory for C*-Algebras*,
  Cambridge Univ. Press (2000), Lemma 2.2.6.
-/

public section

open Function

/-- Star projections `p ≤ q` in a star-ordered C⋆-algebra with `‖p - q‖ < 1` are equal. -/
theorem IsStarProjection.eq_of_le_of_norm_sub_lt_one {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hle : p ≤ q) (h : ‖p - q‖ < 1) : p = q :=
  hp.eq_of_mul_eq_left_of_norm_sub_lt_one hq ((hp.le_iff_mul_eq_left hq).mp hle) h

namespace TauCeti
section
variable {A : Type*} [NonUnitalCStarAlgebra A]
private lemma symmetrize_bounds (e : A) :
    let a : A := (2 : ℝ)⁻¹ • (e + star e)
    IsSelfAdjoint a ∧ ‖a - e‖ = (1 / 2) * ‖e - star e‖ ∧
      ‖a * a - a‖ ≤ ‖e * e - e‖ + (1 / 4) * ‖e - star e‖ ^ 2 := by
  set a : A := (2 : ℝ)⁻¹ • (e + star e)
  have hsub : a - e = (2 : ℝ)⁻¹ • (star e - e) :=
    smul_right_injective A (by norm_num : (2 : ℝ) ≠ 0) <| by
      simp only [a, smul_sub, smul_smul]; norm_num
      simp only [one_smul, ← one_add_one_eq_two, add_smul]; abel
  have hid : a * a - a = (2 : ℝ)⁻¹ • ((e * e - e) + star (e * e - e)) -
      (4 : ℝ)⁻¹ • ((e - star e) * (e - star e)) :=
    smul_right_injective A (by norm_num : (4 : ℝ) ≠ 0) <| by
      simp only [a, smul_mul_smul_comm, smul_sub, smul_smul]; norm_num
      simp only [one_smul, ← one_add_one_eq_two, add_smul, mul_add, add_mul, sub_mul, mul_sub]; abel
  refine ⟨by rw [IsSelfAdjoint, star_smul, star_trivial, star_add, star_star, add_comm],
    by rw [hsub, norm_smul, Real.norm_of_nonneg (by positivity), norm_sub_rev, one_div], ?_⟩
  rw [hid]; refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    linarith [norm_add_le (e * e - e) (star (e * e - e)), norm_star (e * e - e)]
  · rw [norm_smul, Real.norm_of_nonneg (by positivity), one_div, sq]; gcongr; exact norm_mul_le _ _
/-- Every approximate projection with `‖x - star x‖ < 1` and `‖x * x - x‖ < 1` has `‖x‖ < 3`. -/
theorem norm_lt_three_of_approx_projection {x : A} (hsa : ‖x - star x‖ < 1)
    (hidem : ‖x * x - x‖ < 1) : ‖x‖ < 3 := by
  obtain ⟨ha_sa, ha_sub, ha_def⟩ := symmetrize_bounds x; set a : A := (2 : ℝ)⁻¹ • (x + star x)
  have ha_norm : ‖a‖ * ‖a‖ - ‖a‖ ≤ ‖a * a - a‖ := by
    simpa [← CStarRing.norm_star_mul_self, ha_sa.star_eq] using norm_sub_norm_le (a * a) a
  nlinarith [norm_nonneg (x - star x), norm_le_norm_add_norm_sub a x]
/-- **Quantitative norm stability of projections** in a closed non-unital `𝕜'`-`⋆`-subalgebra `s`
(for any scalar monoid `𝕜'` over `ℝ`): if `e ∈ s`, `‖e - star e‖ < δ`, `‖e * e - e‖ < δ` with
`δ ≤ 1 / 5`, there exists a star projection `p ∈ s` with `‖p - e‖ < 3 * δ`. -/
theorem exists_isStarProjection_mem_of_approx {𝕜' S : Type*} [Monoid 𝕜'] [MulAction 𝕜' A]
    [SetLike S A] [NonUnitalSubringClass S A] [SMul ℝ 𝕜'] [IsScalarTower ℝ 𝕜' A]
    [SMulMemClass S 𝕜' A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)] {e : A} (hes : e ∈ s)
    {δ : ℝ} (hδ : δ ≤ 1 / 5) (hsa : ‖e - star e‖ < δ) (hidem : ‖e * e - e‖ < δ) :
    ∃ p ∈ s, IsStarProjection p ∧ ‖p - e‖ < 3 * δ := by
  obtain ⟨ha_sa, ha_sub, ha_def⟩ := symmetrize_bounds e; set a : A := (2 : ℝ)⁻¹ • (e + star e)
  have : SMulMemClass S ℝ A := SMulMemClass.ofIsScalarTower S ℝ 𝕜' A
  have ha_mem : a ∈ s := SMulMemClass.smul_mem (2 : ℝ)⁻¹ (add_mem hes (star_mem hes))
  refine ⟨spectralProjectionIoiHalf a, spectralProjectionIoiHalf_mem (𝕜' := ℝ) ha_mem,
    isStarProjection_spectralProjectionIoiHalf a, ?_⟩
  nlinarith [norm_nonneg (e - star e),
    ha_sa.norm_spectralProjectionIoiHalf_sub_le (by nlinarith [norm_nonneg (e - star e)]),
    norm_sub_le_norm_sub_add_norm_sub (spectralProjectionIoiHalf a) a e]
end

/-- **Uniform norm stability of projections in closed `𝕜'`-`⋆`-subalgebras** (scalar monoid `𝕜'`
over `ℝ`): for `ε > 0`, some `δ > 0` (independent of `A, s`) puts every `δ`-approximate projection
`e ∈ s` within `ε` of a star projection `p ∈ s`. -/
theorem exists_pos_forall_exists_isStarProjection_mem_norm_sub_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A 𝕜' S : Type*} [NonUnitalCStarAlgebra A] [Monoid 𝕜'] [MulAction 𝕜' A]
      [SetLike S A] [NonUnitalSubringClass S A] [SMul ℝ 𝕜'] [IsScalarTower ℝ 𝕜' A]
      [SMulMemClass S 𝕜' A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)] {e : A},
      e ∈ s → ‖e - star e‖ < δ → ‖e * e - e‖ < δ →
      ∃ p ∈ s, IsStarProjection p ∧ ‖p - e‖ < ε :=
  ⟨min (1 / 5) (ε / 3), by positivity, fun {A 𝕜' S} _ _ _ _ _ _ _ _ _ {s} _ {_} hes hsa hidem ↦
    let ⟨p, hps, hp, hpe⟩ :=
      exists_isStarProjection_mem_of_approx (𝕜' := 𝕜') hes (min_le_left _ _) hsa hidem
    ⟨p, hps, hp, hpe.trans_le (by linarith [min_le_right (1 / 5) (ε / 3)])⟩⟩
/-- **Uniform norm stability of projections**: for `ε > 0`, some `δ > 0` (independent of `A`) puts
every `δ`-approximate projection `e : A` within `ε` of a star projection `p : A`. -/
theorem exists_pos_forall_exists_isStarProjection_norm_sub_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A : Type*} [NonUnitalCStarAlgebra A] {e : A},
      ‖e - star e‖ < δ → ‖e * e - e‖ < δ → ∃ p : A, IsStarProjection p ∧ ‖p - e‖ < ε :=
  let ⟨δ, hδ_pos, hδ⟩ := exists_pos_forall_exists_isStarProjection_mem_norm_sub_lt hε
  ⟨δ, hδ_pos, fun {A} _ {_} hsa hidem ↦ by
    have : IsClosed ((⊤ : NonUnitalStarSubalgebra ℝ A) : Set A) := by simp
    obtain ⟨p, -, h⟩ := hδ (𝕜' := ℝ) (s := (⊤ : NonUnitalStarSubalgebra ℝ A))
      NonUnitalStarAlgebra.mem_top hsa hidem; exact ⟨p, h⟩⟩
section
variable {A : Type*} [NonUnitalCStarAlgebra A]
private lemma orthoCorner_compress {s : NonUnitalStarSubalgebra ℝ A} {m : ℕ} {p₀ d₀ : Fin m → A}
    {P : A} (hP_def : P = ∑ j : Fin m, p₀ j) (hP_mem : P ∈ s) (hP_proj : IsStarProjection P)
    {η δ : ℝ} (hp₀_dist : ∀ j, ‖p₀ j - d₀ j‖ < η) {x : A} (hx_mem : x ∈ s) (hx_norm : ‖x‖ ≤ 3)
    (hdx : ∀ j, ‖d₀ j * x‖ < δ) (hxd : ∀ j, ‖x * d₀ j‖ < δ) :
    let y := x - P * x - x * P + P * x * P
    y ∈ s.orthoCorner hP_proj.isSelfAdjoint ∧ ‖y - x‖ ≤ 3 * (m : ℝ) * (3 * η + δ) := by
  dsimp only; set y : A := x - P * x - x * P + P * x * P
  have hPx : ‖P * x‖ ≤ (m : ℝ) * (3 * η + δ) := by
    rw [hP_def, Finset.sum_mul]; refine (norm_sum_le _ _).trans <|
      (Finset.sum_le_card_nsmul _ _ (η * 3 + δ) fun j _ ↦ by
        rw [show p₀ j * x = (p₀ j - d₀ j) * x + d₀ j * x by rw [sub_mul, sub_add_cancel]]
        exact norm_add_le_of_le (norm_mul_le_of_le (hp₀_dist j).le hx_norm) (hdx j).le).trans_eq
        (by simp; ring)
  have hxP : ‖x * P‖ ≤ (m : ℝ) * (3 * η + δ) := by
    rw [hP_def, Finset.mul_sum]; refine (norm_sum_le _ _).trans <|
      (Finset.sum_le_card_nsmul _ _ (3 * η + δ) fun j _ ↦ by
        rw [show x * p₀ j = x * (p₀ j - d₀ j) + x * d₀ j by rw [mul_sub, sub_add_cancel]]
        exact norm_add_le_of_le (norm_mul_le_of_le hx_norm (hp₀_dist j).le) (hxd j).le).trans_eq
        (by simp; ring)
  refine ⟨NonUnitalStarSubalgebra.mem_orthoCorner.mpr
    ⟨add_mem (sub_mem (sub_mem hx_mem (mul_mem hP_mem hx_mem)) (mul_mem hx_mem hP_mem))
        (mul_mem (mul_mem hP_mem hx_mem) hP_mem),
      by dsimp [y]; simp only [mul_add, mul_sub, ← mul_assoc, hP_proj.isIdempotentElem.eq]; abel,
      by dsimp [y]; simp only [add_mul, sub_mul, mul_assoc, hP_proj.isIdempotentElem.eq]; abel⟩, ?_⟩
  rw [show y - x = -(P * x) + -(x * P) + P * x * P by dsimp [y]; abel]
  refine norm_add₃_le.trans ?_; rw [norm_neg, norm_neg]
  linarith [norm_mul_le_of_le hPx (hP_proj.norm_le _)]
private lemma approx_projection_of_close {x y : A} {δ μ δ₁ : ℝ} (hμ_half : μ ≤ 1 / 2)
    (hδ_δ₁ : δ ≤ δ₁ / 5) (hμ_δ₁ : μ ≤ δ₁ / 10) (hx_norm : ‖x‖ < 3) (hx_sa : ‖x - star x‖ < δ)
    (hx_idem : ‖x * x - x‖ < δ) (hy_sub_x : ‖y - x‖ < μ) :
    ‖y - star y‖ < δ₁ ∧ ‖y * y - y‖ < δ₁ := by
  have hy_norm : ‖y‖ ≤ 4 := by linarith [norm_le_norm_add_norm_sub' y x]
  refine ⟨?_, ?_⟩
  · rw [show y - star y = (y - x) + (x - star x) + -star (y - x) by simp [star_sub]]
    exact norm_add₃_le.trans_lt (by rw [norm_neg, norm_star]; linarith [norm_nonneg (y - x)])
  · rw [show y * y - y = (y - x) * y + x * (y - x) + (x * x - x) + -(y - x) by
      simp only [sub_mul, mul_sub]; abel]
    refine norm_add₄_le.trans_lt ?_; rw [norm_neg]
    linarith [norm_mul_le_of_le hy_sub_x.le hy_norm, norm_mul_le_of_le hx_norm.le hy_sub_x.le]
end
private lemma exists_pos_forall_exists_pairwise_isStarOrtho_isStarProjection_fin :
    ∀ (m : ℕ) {ε : ℝ}, 0 < ε →
      ∃ δ > 0, ∀ {A : Type*} [NonUnitalCStarAlgebra A] {s : NonUnitalStarSubalgebra ℝ A},
        [IsClosed (s : Set A)] → ∀ {d : Fin m → A}, (∀ i, d i ∈ s) →
        (∀ i, ‖d i - star (d i)‖ < δ) → (∀ i, ‖d i * d i - d i‖ < δ) →
        (∀ i j, i ≠ j → ‖d i * d j‖ < δ) →
        ∃ p : Fin m → A, (∀ i, p i ∈ s) ∧ (∀ i, IsStarProjection (p i)) ∧
          Pairwise (IsStarOrtho on p) ∧ ∀ i, ‖p i - d i‖ < ε
  | 0, _, _ => ⟨1, zero_lt_one, fun _ _ _ _ ↦
      ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩⟩
  | m + 1, ε, hε => by
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ :=
      exists_pos_forall_exists_isStarProjection_mem_norm_sub_lt (half_pos hε)
    set μ : ℝ := min (1 / 2) (min (ε / 2) (δ₁ / 10)); have : 0 < μ := by positivity
    set η : ℝ := min ε (μ / (12 * (m + 1 : ℝ)))
    obtain ⟨δ_ih, hδ_ih_pos, h_ih⟩ :=
      exists_pos_forall_exists_pairwise_isStarOrtho_isStarProjection_fin m (by positivity : 0 < η)
    set δ : ℝ := min (1 / 2) (min δ_ih (min (δ₁ / 5) η))
    refine ⟨δ, by positivity, fun {A} _ {s} hs {d} hd_mem hd_sa hd_idem hd_ortho ↦ ?_⟩
    have hδ_ih : δ ≤ δ_ih := (min_le_right _ _).trans (min_le_left _ _)
    obtain ⟨p₀, hp₀_mem, hp₀_proj, hp₀_ortho, hp₀_dist⟩ := h_ih (d := fun j ↦ d j.castSucc)
      (fun j ↦ hd_mem j.castSucc) (fun j ↦ (hd_sa _).trans_le hδ_ih)
      (fun j ↦ (hd_idem _).trans_le hδ_ih)
      (fun i j hij ↦ (hd_ortho _ _ (Fin.castSucc_inj.not.mpr hij)).trans_le hδ_ih)
    set P : A := ∑ j : Fin m, p₀ j; set x : A := d (Fin.last m)
    have hP_proj : IsStarProjection P := .sum (fun j _ ↦ hp₀_proj j) (hp₀_ortho.set_pairwise _)
    have hx_norm : ‖x‖ < 3 := norm_lt_three_of_approx_projection
      ((hd_sa _).trans_le ((min_le_left _ _).trans (by norm_num)))
      ((hd_idem _).trans_le ((min_le_left _ _).trans (by norm_num)))
    obtain ⟨hy_mem_corner, hy_dist_le⟩ := orthoCorner_compress rfl (sum_mem fun j _ ↦ hp₀_mem j)
      hP_proj hp₀_dist (hd_mem _) hx_norm.le (fun j ↦ hd_ortho _ _ (Fin.castSucc_lt_last j).ne)
      (fun j ↦ hd_ortho _ _ (Fin.castSucc_lt_last j).ne')
    set y : A := x - P * x - x * P + P * x * P
    have hy_sub_x : ‖y - x‖ < μ := hy_dist_le.trans_lt <| by
      have hη : 12 * (m + 1 : ℝ) * η ≤ μ := (le_div_iff₀' (by positivity)).mp (min_le_right _ _)
      have hδη : δ ≤ η := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
      nlinarith [Nat.cast_nonneg (α := ℝ) m, show (0 : ℝ) < η by positivity]
    obtain ⟨hy_sa, hy_idem⟩ := approx_projection_of_close (min_le_left _ _)
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
      ((min_le_right _ _).trans (min_le_right _ _)) hx_norm (hd_sa _) (hd_idem _) hy_sub_x
    obtain ⟨q, hq_corner, hq_proj, hq_dist⟩ := hδ₁ (𝕜' := ℝ) hy_mem_corner hy_sa hy_idem
    obtain ⟨hq_mem, hPq, -⟩ := NonUnitalStarSubalgebra.mem_orthoCorner.mp hq_corner
    have hortho : ∀ j, IsStarOrtho (p₀ j) q := fun j ↦
      (isStarOrtho_sum_left_iff (fun k _ ↦ hp₀_proj k) (hp₀_ortho.set_pairwise _)).mp
        ((hP_proj.isSelfAdjoint.isStarOrtho_iff_mul_eq_zero hq_proj.isSelfAdjoint).mpr hPq)
        j (Finset.mem_univ j)
    refine ⟨Fin.snoc p₀ q, Fin.lastCases (by simpa) (fun j ↦ by simpa using hp₀_mem j),
      Fin.lastCases (by simpa) (fun j ↦ by simpa using hp₀_proj j), fun i k ↦ ?_,
      Fin.lastCases (by simpa [x] using (show ‖q - x‖ < ε by
        linarith [norm_sub_le_norm_sub_add_norm_sub q y x,
          show μ ≤ ε / 2 from (min_le_right _ _).trans (min_le_left _ _)]))
        (fun j ↦ by simpa using (hp₀_dist j).trans_le (min_le_left _ _))⟩
    refine Fin.lastCases ?_ (fun i' ↦ ?_) i <;> refine Fin.lastCases ?_ (fun k' ↦ ?_) k <;>
      intro hik <;> simp only [onFun, Fin.snoc_last, Fin.snoc_castSucc]
    exacts [(hik rfl).elim, (hortho k').symm, hortho i',
      hp₀_ortho fun h ↦ hik (congrArg Fin.castSucc h)]
/-- **Uniform norm stability of finite pairwise-orthogonal projection families in closed
`𝕜'`-`⋆`-subalgebras** (scalar monoid `𝕜'` over `ℝ`): for finite `ι` and `ε > 0`, some `δ > 0`
(independent of `A, s`) puts `δ`-approx orthogonal families in `s` within `ε` of exact ones. -/
theorem exists_pos_forall_exists_pairwise_isStarOrtho_isStarProjection_mem_norm_sub_lt
    (ι : Type*) [Finite ι] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A 𝕜' S : Type*} [NonUnitalCStarAlgebra A] [Monoid 𝕜'] [MulAction 𝕜' A]
      [SetLike S A] [NonUnitalSubringClass S A] [SMul ℝ 𝕜'] [IsScalarTower ℝ 𝕜' A]
      [SMulMemClass S 𝕜' A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)] {d : ι → A},
      (∀ i, d i ∈ s) → (∀ i, ‖d i - star (d i)‖ < δ) → (∀ i, ‖d i * d i - d i‖ < δ) →
      (∀ i j, i ≠ j → ‖d i * d j‖ < δ) →
      ∃ p : ι → A, (∀ i, p i ∈ s) ∧ (∀ i, IsStarProjection (p i)) ∧
        Pairwise (IsStarOrtho on p) ∧ ∀ i, ‖p i - d i‖ < ε := by
  cases nonempty_fintype ι; let σ := Fintype.equivFin ι
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    exists_pos_forall_exists_pairwise_isStarOrtho_isStarProjection_fin (Fintype.card ι) hε
  refine ⟨δ, hδ_pos, fun {A 𝕜' S} _ _ _ _ _ _ _ _ _ {s} hs {d} hd_mem hd_sa hd_idem hd_ortho ↦ ?_⟩
  have : SMulMemClass S ℝ A := SMulMemClass.ofIsScalarTower S ℝ 𝕜' A
  let s' : NonUnitalStarSubalgebra ℝ A := NonUnitalStarSubalgebra.ofClass s
  have : IsClosed (s' : Set A) := by simpa [s'] using hs
  obtain ⟨p, hp_mem, hp_proj, hp_ortho, hp_dist⟩ := hδ (s := s') (d := fun k ↦ d (σ.symm k))
    (fun _ ↦ NonUnitalStarSubalgebra.mem_ofClass.mpr (hd_mem _))
    (fun _ ↦ hd_sa _) (fun _ ↦ hd_idem _) (fun _ _ hkl ↦ hd_ortho _ _ (σ.symm.injective.ne hkl))
  exact ⟨fun i ↦ p (σ i), fun _ ↦ NonUnitalStarSubalgebra.mem_ofClass.mp (hp_mem _),
    fun _ ↦ hp_proj _, fun _ _ hij ↦ hp_ortho (σ.injective.ne hij),
    fun i ↦ by simpa using hp_dist (σ i)⟩
/-- **Uniform norm stability of finite pairwise-orthogonal projection families**: for finite `ι`
and `ε > 0`, some `δ > 0` (independent of `A`) puts every `δ`-approx family within `ε` of exact. -/
theorem exists_pos_forall_exists_pairwise_isStarOrtho_isStarProjection_norm_sub_lt
    (ι : Type*) [Finite ι] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A : Type*} [NonUnitalCStarAlgebra A] {d : ι → A},
      (∀ i, ‖d i - star (d i)‖ < δ) → (∀ i, ‖d i * d i - d i‖ < δ) →
      (∀ i j, i ≠ j → ‖d i * d j‖ < δ) →
      ∃ p : ι → A, (∀ i, IsStarProjection (p i)) ∧
        Pairwise (IsStarOrtho on p) ∧ ∀ i, ‖p i - d i‖ < ε :=
  let ⟨δ, hδ_pos, hδ⟩ :=
    exists_pos_forall_exists_pairwise_isStarOrtho_isStarProjection_mem_norm_sub_lt ι hε
  ⟨δ, hδ_pos, fun {A} _ {_} hd_sa hd_idem hd_ortho ↦ by
    have : IsClosed ((⊤ : NonUnitalStarSubalgebra ℝ A) : Set A) := by simp
    obtain ⟨p, -, h⟩ := hδ (𝕜' := ℝ) (s := (⊤ : NonUnitalStarSubalgebra ℝ A))
      (fun _ ↦ NonUnitalStarAlgebra.mem_top) hd_sa hd_idem hd_ortho; exact ⟨p, h⟩⟩
end TauCeti

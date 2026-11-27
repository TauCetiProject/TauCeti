/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.MatrixUnits
public import TauCeti.Analysis.CStarAlgebra.PartialIsometry
public import TauCeti.Analysis.CStarAlgebra.Projection.Stability
import Mathlib.Algebra.Star.NonUnitalSubalgebra
import TauCeti.Analysis.Normed.Algebra.Star
import TauCeti.Topology.Algebra.NonUnitalStarAlgebra

/-!
# Norm stability of matrix units in C⋆-algebras

Finite multi-block systems of matrix units (`TauCeti.IsMatrixUnitSystem`) parameterize
`⋆`-homomorphisms from `⨁ᵣ M_{n r}(ℂ)` into a C⋆-algebra `A`. Both non-unital and unital finite
matrix-unit systems are **uniformly norm-stable** across all C⋆-algebras: for every `ε > 0` and
finite index family `n : κ → Type*`, there exists `δ > 0` depending only on `ε` and `n`, uniformly
across all C⋆-algebras `A` and closed non-unital `𝕜'`-`⋆`-subalgebras `s` (for any scalar monoid
`𝕜'` over `ℝ`), such that every `δ`-approximate system in `s` lies entrywise within `ε` of an
exact system in `s` (and unital when `‖matrixUnitSupport x - 1‖ < δ`).

## Main results

* `TauCeti.IsApproxMatrixUnitSystem`,
  `TauCeti.exists_pos_forall_exists_isMatrixUnitSystem_mem_norm_sub_lt`,
  `TauCeti.exists_pos_forall_exists_isMatrixUnitSystem_norm_sub_lt`,
  `TauCeti.exists_pos_forall_exists_isUnitalMatrixUnitSystem_mem_norm_sub_lt`,
  `TauCeti.exists_pos_forall_exists_isUnitalMatrixUnitSystem_norm_sub_lt`.

## References

* B. Blackadar, *Operator Algebras*, Springer (2006), Proposition II.8.3.23.
* K. R. Davidson, *C⋆-Algebras by Example*, Amer. Math. Soc. (1996), Section III.3.
-/

public section
open Function
namespace TauCeti
section
variable {κ A : Type*} {n : κ → Type*}
/-- A multi-block family `x` is a **`δ`-approximate system of matrix units** if the adjoint and
multiplication relations of `IsMatrixUnitSystem` hold up to norm `< δ`. -/
@[mk_iff]
structure IsApproxMatrixUnitSystem [SeminormedAddCommGroup A] [Mul A] [Star A] (δ : ℝ)
    (x : ∀ r : κ, n r → n r → A) : Prop where
  /-- Taking the star approximately transposes indices within each block. -/
  norm_star_sub_lt (r : κ) (i j : n r) : ‖star (x r i j) - x r j i‖ < δ
  /-- Composable entries within a block approximately contract the middle index. -/
  norm_mul_same_sub_lt (r : κ) (i j l : n r) : ‖x r i j * x r j l - x r i l‖ < δ
  /-- Non-composable entries within a block have product of norm `< δ`. -/
  norm_mul_lt_of_ne (r : κ) (i : n r) {j k : n r} (l : n r) : j ≠ k → ‖x r i j * x r k l‖ < δ
  /-- Entries from distinct blocks have product of norm `< δ`. -/
  norm_mul_lt_of_block_ne {r t : κ} : r ≠ t → ∀ (i j : n r) (k l : n t), ‖x r i j * x t k l‖ < δ
/-- Every exact system of matrix units is a `δ`-approximate system for every `δ > 0`. -/
theorem IsMatrixUnitSystem.isApproxMatrixUnitSystem [SeminormedAddCommGroup A] [Mul A] [Star A]
    {e : ∀ r : κ, n r → n r → A} (he : IsMatrixUnitSystem e) {δ : ℝ} (hδ : 0 < δ) :
    IsApproxMatrixUnitSystem δ e where
  norm_star_sub_lt r i j := by simp [he.star_eq, hδ]
  norm_mul_same_sub_lt r i j l := by simp [he.mul_same, hδ]
  norm_mul_lt_of_ne r i {_ _} l hjk := by simp [he.mul_eq_zero_of_ne r i l hjk, hδ]
  norm_mul_lt_of_block_ne hrs i j k l := by simp [he.mul_eq_zero_of_block_ne hrs i j k l, hδ]

namespace IsApproxMatrixUnitSystem
/-- Monotonicity of `IsApproxMatrixUnitSystem` in the tolerance `δ`. -/
theorem mono [SeminormedAddCommGroup A] [Mul A] [Star A] {δ₁ δ₂ : ℝ} {x : ∀ r : κ, n r → n r → A}
    (hx : IsApproxMatrixUnitSystem δ₁ x) (h : δ₁ ≤ δ₂) : IsApproxMatrixUnitSystem δ₂ x :=
  ⟨fun r i j ↦ (hx.norm_star_sub_lt r i j).trans_le h,
   fun r i j l ↦ (hx.norm_mul_same_sub_lt r i j l).trans_le h,
   fun r i {_ _} l hjk ↦ (hx.norm_mul_lt_of_ne r i l hjk).trans_le h,
   fun hrs i j k l ↦ (hx.norm_mul_lt_of_block_ne hrs i j k l).trans_le h⟩
/-- Every entry of a `δ`-approximate system of matrix units with `δ ≤ 1 / 2` has norm `< 3`. -/
theorem norm_lt_three [NonUnitalCStarAlgebra A] {δ : ℝ} {x : ∀ r : κ, n r → n r → A}
    (hx : IsApproxMatrixUnitSystem δ x) (hδ : δ ≤ 1 / 2) (r : κ) (i j : n r) : ‖x r i j‖ < 3 := by
  have hdiag : ‖x r j j‖ < 3 := norm_lt_three_of_approx_projection
    (norm_sub_rev (x r j j) _ ▸ (hx.norm_star_sub_lt r j j).trans_le (by linarith))
    ((hx.norm_mul_same_sub_lt r j j j).trans_le (by linarith))
  have hdiff : ‖star (x r i j) * x r i j - x r j j‖ ≤
      ‖star (x r i j) - x r j i‖ * ‖x r i j‖ + ‖x r j i * x r i j - x r j j‖ :=
    norm_mul_sub_le_right (x r i j) (star (x r i j)) (x r j i) (x r j j)
  have hsq : ‖x r i j‖ ^ 2 < 3 + (1 / 2) * ‖x r i j‖ + 1 / 2 := by
    have hnorm := norm_le_norm_add_norm_sub' (star (x r i j) * x r i j) (x r j j)
    rw [sq, ← CStarRing.norm_star_mul_self]
    nlinarith [(hx.norm_star_sub_lt r i j).le.trans hδ,
      (hx.norm_mul_same_sub_lt r j i j).trans_le hδ, norm_nonneg (x r i j)]
  nlinarith
private lemma norm_proj_mul_sub_lt [NonUnitalCStarAlgebra A] {δ η : ℝ}
    (hδ_η : δ ≤ η / 200) {x : ∀ r : κ, n r → n r → A} (hx : IsApproxMatrixUnitSystem δ x)
    {p : ∀ r : κ, n r → A} (hp_proj : ∀ r i, IsStarProjection (p r i))
    (hp_dist : ∀ r i, ‖p r i - x r i i‖ < η / 200) {r : κ} {i i₀ : n r}
    (hx_le : ‖x r i i₀‖ ≤ 3) :
    ‖p r i * x r i i₀ * p r i₀ - x r i i₀‖ < (8 / 200) * η := by
  have hcomp := norm_mul_mul_sub_le (p r i) (x r i i) (x r i i₀) (x r i₀ i₀) (p r i₀)
  have h1 : ‖p r i - x r i i‖ * ‖x r i i₀‖ < (3 / 200) * η := by
    nlinarith [norm_nonneg (p r i - x r i i), hp_dist r i]
  have h2 : ‖x r i i * x r i i₀ - x r i i₀‖ < (1 / 200) * η :=
    (hx.norm_mul_same_sub_lt r i i i₀).trans_le (hδ_η.trans_eq (by ring))
  have h3 : (‖p r i - x r i i‖ * ‖x r i i₀‖ + ‖x r i i * x r i i₀ - x r i i₀‖) * ‖p r i₀‖ ≤
      (4 / 200) * η := by
    have hp0 := (hp_proj r i₀).norm_le _
    nlinarith [norm_nonneg (p r i₀), norm_nonneg (p r i - x r i i),
      norm_nonneg (x r i i * x r i i₀ - x r i i₀)]
  have h4 : ‖x r i i₀‖ * ‖p r i₀ - x r i₀ i₀‖ < (3 / 200) * η := by
    nlinarith [norm_nonneg (p r i₀ - x r i₀ i₀), hp_dist r i₀]
  have h5 : ‖x r i i₀ * x r i₀ i₀ - x r i i₀‖ < (1 / 200) * η :=
    (hx.norm_mul_same_sub_lt r i i₀ i₀).trans_le (hδ_η.trans_eq (by ring))
  linarith
private lemma exists_column_partialIsometry {𝕜' S : Type*} [NonUnitalCStarAlgebra A] [Monoid 𝕜']
    [MulAction 𝕜' A] [SetLike S A] [NonUnitalSubringClass S A] [SMul ℝ 𝕜']
    [IsScalarTower ℝ 𝕜' A] [SMulMemClass S 𝕜' A] [StarMemClass S A] {s : S}
    [IsClosed (s : Set A)] {δ η : ℝ} (hη_le : η ≤ 1 / 32)
    (hδ_η : δ ≤ η / 200) {x : ∀ r : κ, n r → n r → A} (hx : IsApproxMatrixUnitSystem δ x)
    (hx_mem : ∀ r i j, x r i j ∈ s) {p : ∀ r : κ, n r → A} (hp_mem : ∀ r i, p r i ∈ s)
    (hp_proj : ∀ r i, IsStarProjection (p r i))
    (hp_dist : ∀ r i, ‖p r i - x r i i‖ < η / 200) (r : κ) (i i₀ : n r) :
    ∃ v ∈ s, IsPartialIsometry v ∧ star v * v = p r i₀ ∧ v * star v = p r i ∧
      ‖v - x r i i₀‖ < 11 * η := by
  -- Step 1: Compress `x r i i₀` by `p r i` and `p r i₀`, bounding `‖z‖` and `‖z - x r i i₀‖`.
  have hη_pos : 0 < η := by linarith [hp_dist r i, norm_nonneg (p r i - x r i i)]
  have hδ_half : δ ≤ 1 / 2 := hδ_η.trans (by linarith)
  have hx_le (a b : n r) : ‖x r a b‖ ≤ 3 := (hx.norm_lt_three hδ_half r a b).le
  set z : A := p r i * x r i i₀ * p r i₀
  have hz_norm : ‖z‖ ≤ 3 := (norm_mul_le_of_le (norm_mul_le_of_le ((hp_proj r i).norm_le _)
    (hx_le i i₀)) ((hp_proj r i₀).norm_le _)).trans_eq (by norm_num)
  have hz_sub_x : ‖z - x r i i₀‖ < (8 / 200) * η :=
    norm_proj_mul_sub_lt hδ_η hx hp_proj hp_dist (hx_le i i₀)
  -- Step 2: Estimate the initial and final defects `‖star z * z - p r i₀‖`, `‖z * star z - p r i‖`.
  have hz_init : ‖star z * z - p r i₀‖ < η :=
    (norm_star_mul_self_sub_lt_of_norm_le hz_norm (hx_le i i₀) hz_sub_x.le
      (hx.norm_star_sub_lt r i i₀) (hx.norm_mul_same_sub_lt r i₀ i i₀)
      (hp_dist r i₀)).trans_le (by linarith)
  have hdecomp : star z - x r i₀ i = star (z - x r i i₀) + (star (x r i i₀) - x r i₀ i) := by
    rw [star_sub, sub_add_sub_cancel]
  have hstar_z_sub : ‖star z - x r i₀ i‖ ≤ (9 / 200) * η := by
    rw [hdecomp]
    exact (norm_add_le_of_le ((norm_star _).le.trans hz_sub_x.le)
      ((hx.norm_star_sub_lt r i i₀).le.trans hδ_η)).trans_eq (by ring)
  have hz_fin : ‖z * star z - p r i‖ < η := by
    simpa only [star_star] using (norm_star_mul_self_sub_lt_of_norm_le (z := star z)
      ((norm_star z).le.trans hz_norm) (hx_le i₀ i) hstar_z_sub (hx.norm_star_sub_lt r i₀ i)
      (hx.norm_mul_same_sub_lt r i i₀ i) (hp_dist r i)).trans_le (by linarith)
  -- Step 3: Apply polar perturbation to `z` to obtain the partial isometry `v`.
  obtain ⟨v, hv_mem, hv_pi, hv_init, hv_fin, hv_dist_z⟩ :=
    exists_isPartialIsometry_mem_of_approx (𝕜' := 𝕜') (s := s) (z := z) hη_le (hp_proj r i₀)
      (hp_proj r i) (mul_mem (mul_mem (hp_mem r i) (hx_mem r i i₀)) (hp_mem r i₀))
      (by dsimp [z]; rw [← mul_assoc, ← mul_assoc, (hp_proj r i).isIdempotentElem.eq])
      (by dsimp [z]; rw [mul_assoc, (hp_proj r i₀).isIdempotentElem.eq]) hz_init hz_fin
  exact ⟨v, hv_mem, hv_pi, hv_init, hv_fin,
    by linarith [norm_sub_le_norm_sub_add_norm_sub v z (x r i i₀)]⟩
end IsApproxMatrixUnitSystem
end
private lemma exists_isMatrixUnitSystem_mem_of_diag {κ A 𝕜' S : Type*} [NonUnitalCStarAlgebra A]
    {n : κ → Type*} [Monoid 𝕜'] [MulAction 𝕜' A] [SetLike S A] [NonUnitalSubringClass S A]
    [SMul ℝ 𝕜'] [IsScalarTower ℝ 𝕜' A] [SMulMemClass S 𝕜' A] [StarMemClass S A]
    {s : S} [IsClosed (s : Set A)] {ε η δ : ℝ} (hη_le : η ≤ 1 / 32) (hη_eps : η ≤ ε / 60)
    (hδ_η : δ ≤ η / 200) {x : ∀ r : κ, n r → n r → A} (hx_mem : ∀ r i j, x r i j ∈ s)
    (hx : IsApproxMatrixUnitSystem δ x) {p : (Σ r : κ, n r) → A} (hp_mem : ∀ u, p u ∈ s)
    (hp_proj : ∀ u, IsStarProjection (p u)) (hp_ortho : Pairwise (IsStarOrtho on p))
    (hp_dist : ∀ u, ‖p u - x u.1 u.2 u.2‖ < η / 200) :
    ∃ e : ∀ r : κ, n r → n r → A,
      (∀ r i j, e r i j ∈ s) ∧ IsMatrixUnitSystem e ∧ ∀ r i j, ‖e r i j - x r i j‖ < ε := by
  have hv_blk (r : κ) : ∃ (q : A) (v : n r → A), (∀ i, v i ∈ s) ∧
      (∀ i, IsPartialIsometry (v i)) ∧ (∀ i, star (v i) * v i = q) ∧
      (∀ i, v i * star (v i) = p ⟨r, i⟩) ∧ (∀ i j, ‖v i * star (v j) - x r i j‖ < ε) := by
    by_cases hnr : Nonempty (n r)
    · obtain ⟨i₀⟩ := hnr
      have hcol (i : n r) := hx.exists_column_partialIsometry (𝕜' := 𝕜') (s := s)
        hη_le hδ_η hx_mem (fun r i ↦ hp_mem ⟨r, i⟩) (fun r i ↦ hp_proj ⟨r, i⟩)
        (fun r i ↦ hp_dist ⟨r, i⟩) r i i₀
      choose v hv_mem hv_pi hv_init hv_fin hv_dist using hcol
      refine ⟨p ⟨r, i₀⟩, v, hv_mem, hv_pi, hv_init, hv_fin, fun i j ↦ ?_⟩
      have hη_pos : 0 < η := by linarith [hp_dist ⟨r, i⟩, norm_nonneg (p ⟨r, i⟩ - x r i i)]
      have hδ_half : δ ≤ 1 / 2 := hδ_η.trans (by linarith)
      have hxi : ‖x r i i₀‖ ≤ 3 := (hx.norm_lt_three hδ_half r i i₀).le
      have h1 : ‖v i * star (v j) - x r i i₀ * star (x r j i₀)‖ < 44 * η := by
        have hmul := norm_mul_star_sub_mul_star_le (v i) (v j) (x r i i₀) (x r j i₀)
        have hvj : ‖v j‖ ≤ 1 := (hv_pi j).norm_le_one
        nlinarith [hv_dist i, hv_dist j, norm_nonneg (v i - x r i i₀),
          norm_nonneg (v j - x r j i₀)]
      have h2 : ‖x r i i₀ * star (x r j i₀) - x r i j‖ ≤
          ‖x r i i₀‖ * ‖star (x r j i₀) - x r i₀ j‖ + ‖x r i i₀ * x r i₀ j - x r i j‖ :=
        norm_mul_sub_le_left (x r i i₀) (star (x r j i₀)) (x r i₀ j) (x r i j)
      have htri := norm_sub_le_norm_sub_add_norm_sub (v i * star (v j))
        (x r i i₀ * star (x r j i₀)) (x r i j)
      nlinarith [hx.norm_star_sub_lt r j i₀, hx.norm_mul_same_sub_lt r i i₀ j,
        norm_nonneg (star (x r j i₀) - x r i₀ j)]
    · exact ⟨0, fun i ↦ (hnr ⟨i⟩).elim, fun i ↦ (hnr ⟨i⟩).elim, fun i ↦ (hnr ⟨i⟩).elim,
        fun i ↦ (hnr ⟨i⟩).elim, fun i ↦ (hnr ⟨i⟩).elim, fun i ↦ (hnr ⟨i⟩).elim⟩
  choose q v hv_mem hv_pi hv_init hv_fin hv_dist using hv_blk
  exact ⟨fun r i j ↦ v r i * star (v r j),
    fun r i j ↦ mul_mem (hv_mem r i) (star_mem (hv_mem r j)),
    IsMatrixUnitSystem.of_partialIsometry hv_pi (fun r i j ↦ by rw [hv_init r i, hv_init r j])
      (fun u w huw ↦ by
        rw [onFun, hv_fin, hv_fin]; exact (hp_ortho huw).mul_eq_zero' (hp_proj w).isSelfAdjoint),
    hv_dist⟩
/-- **Uniform norm stability of finite multi-block matrix-unit systems in closed
`𝕜'`-`⋆`-subalgebras** (scalar monoid `𝕜'` over `ℝ`): for `ε > 0` and finite `n : κ → Type*`, some
`δ > 0` (independent of `A, s`) puts every `δ`-approx system in `s` within `ε` of an exact one. -/
theorem exists_pos_forall_exists_isMatrixUnitSystem_mem_norm_sub_lt {κ : Type*} (n : κ → Type*)
    [Finite κ] [∀ r, Finite (n r)] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A 𝕜' S : Type*} [NonUnitalCStarAlgebra A] [Monoid 𝕜'] [MulAction 𝕜' A]
      [SetLike S A] [NonUnitalSubringClass S A] [SMul ℝ 𝕜'] [IsScalarTower ℝ 𝕜' A]
      [SMulMemClass S 𝕜' A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)]
      {x : ∀ r : κ, n r → n r → A}, (∀ r i j, x r i j ∈ s) → IsApproxMatrixUnitSystem δ x →
      ∃ e : ∀ r : κ, n r → n r → A,
        (∀ r i j, e r i j ∈ s) ∧ IsMatrixUnitSystem e ∧ ∀ r i j, ‖e r i j - x r i j‖ < ε := by
  set η : ℝ := min (1 / 32) (ε / 60)
  obtain ⟨δ_diag, hδ_diag_pos, hδ_diag⟩ :=
    exists_pos_forall_exists_pairwise_isStarOrtho_isStarProjection_mem_norm_sub_lt
      (Σ r : κ, n r) (by positivity : 0 < η / 200)
  set δ : ℝ := min (1 / 2) (min δ_diag (η / 200))
  refine ⟨δ, by positivity, fun {A 𝕜' S} _ _ _ _ _ _ _ _ _ {s} _ {x} hx_mem hx ↦ ?_⟩
  have hδ_le : δ ≤ δ_diag := (min_le_right _ _).trans (min_le_left _ _)
  have hδ_le_η : δ ≤ η / 200 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨p, hp_mem, hp_proj, hp_ortho, hp_dist⟩ :=
    hδ_diag (𝕜' := 𝕜') (s := s) (d := fun u : Σ r : κ, n r ↦ x u.1 u.2 u.2)
      (fun u ↦ hx_mem u.1 u.2 u.2)
      (fun u ↦ by rw [norm_sub_rev]; exact (hx.norm_star_sub_lt u.1 u.2 u.2).trans_le hδ_le)
      (fun u ↦ (hx.norm_mul_same_sub_lt u.1 u.2 u.2 u.2).trans_le hδ_le)
      (fun ⟨r, i⟩ ⟨t, j⟩ huw ↦ by
        by_cases hrt : r = t
        · subst hrt; exact (hx.norm_mul_lt_of_ne r i j fun h ↦ huw (congrArg _ h)).trans_le hδ_le
        · exact (hx.norm_mul_lt_of_block_ne hrt i i j j).trans_le hδ_le)
  exact exists_isMatrixUnitSystem_mem_of_diag (min_le_left _ _) (min_le_right _ _)
    hδ_le_η hx_mem hx hp_mem hp_proj hp_ortho hp_dist
/-- **Uniform norm stability of finite multi-block matrix-unit systems**: for `ε > 0` and finite
`n : κ → Type*`, some `δ > 0` (independent of `A`) puts `δ`-approx systems within `ε` of exact. -/
theorem exists_pos_forall_exists_isMatrixUnitSystem_norm_sub_lt {κ : Type*} (n : κ → Type*)
    [Finite κ] [∀ r, Finite (n r)] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A : Type*} [NonUnitalCStarAlgebra A] {x : ∀ r : κ, n r → n r → A},
      IsApproxMatrixUnitSystem δ x →
      ∃ e : ∀ r : κ, n r → n r → A, IsMatrixUnitSystem e ∧ ∀ r i j, ‖e r i j - x r i j‖ < ε :=
  let ⟨δ, hδ_pos, hδ⟩ := exists_pos_forall_exists_isMatrixUnitSystem_mem_norm_sub_lt n hε
  ⟨δ, hδ_pos, fun {A} _ {_} hx ↦
    let ⟨e, _, h⟩ := hδ (𝕜' := ℝ) (s := (⊤ : NonUnitalStarSubalgebra ℝ A))
      (fun _ _ _ ↦ NonUnitalStarAlgebra.mem_top) hx
    ⟨e, h⟩⟩
/-- **Uniform norm stability of unital finite matrix-unit systems in closed `𝕜'`-`⋆`-subalgebras**
(scalar monoid `𝕜'` over `ℝ`): for `ε > 0` and finite `n`, some `δ > 0` (independent of `A, s`)
puts `δ`-approx systems in `s` with `‖matrixUnitSupport x - 1‖ < δ` within `ε` of a unital one. -/
theorem exists_pos_forall_exists_isUnitalMatrixUnitSystem_mem_norm_sub_lt {κ : Type*}
    (n : κ → Type*) [Fintype κ] [∀ r, Fintype (n r)] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A 𝕜' S : Type*} [CStarAlgebra A] [Monoid 𝕜'] [MulAction 𝕜' A] [SetLike S A]
      [NonUnitalSubringClass S A] [SMul ℝ 𝕜'] [IsScalarTower ℝ 𝕜' A] [SMulMemClass S 𝕜' A]
      [StarMemClass S A] {s : S} [IsClosed (s : Set A)] {x : ∀ r : κ, n r → n r → A},
      (∀ r i j, x r i j ∈ s) → IsApproxMatrixUnitSystem δ x → ‖matrixUnitSupport x - 1‖ < δ →
      ∃ e : ∀ r : κ, n r → n r → A,
        (∀ r i j, e r i j ∈ s) ∧ IsUnitalMatrixUnitSystem e ∧ ∀ r i j, ‖e r i j - x r i j‖ < ε := by
  set M : ℕ := ∑ r : κ, Fintype.card (n r); set ε' : ℝ := min ε (1 / (2 * (M + 1 : ℝ)))
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ :=
    exists_pos_forall_exists_isMatrixUnitSystem_mem_norm_sub_lt n (by positivity : 0 < ε')
  refine ⟨min δ₀ (1 / 2), by positivity,
    fun {A 𝕜' S} _ _ _ _ _ _ _ _ _ {s} _ {x} hx_mem hx hsupp_x ↦ ?_⟩
  obtain ⟨e, he_mem, he, he_dist⟩ := hδ₀ (𝕜' := 𝕜') hx_mem (hx.mono (min_le_left _ _))
  refine ⟨e, he_mem,
    ⟨he, he.isStarProjection_support.isIdempotentElem.eq_one_of_norm_sub_one_lt_one ?_⟩,
    fun r i j ↦ (he_dist r i j).trans_le (min_le_left _ _)⟩
  have hsum_le : ‖matrixUnitSupport e - matrixUnitSupport x‖ ≤ (M : ℝ) * ε' := by
    simp only [matrixUnitSupport_def, ← Finset.sum_sub_distrib, M, Nat.cast_sum, Finset.sum_mul]
    exact (norm_sum_le _ _).trans <| Finset.sum_le_sum fun r _ ↦
      (norm_sum_le _ _).trans <| (Finset.sum_le_sum fun i _ ↦ (he_dist r i i).le).trans (by simp)
  have hε'_le : 2 * (M + 1 : ℝ) * ε' ≤ 1 := (le_div_iff₀' (by positivity)).mp (min_le_right _ _)
  have hδ_half : min δ₀ (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hε'_pos : 0 < ε' := by positivity
  nlinarith [norm_sub_le_norm_sub_add_norm_sub (matrixUnitSupport e) (matrixUnitSupport x) 1]
/-- **Uniform norm stability of unital finite matrix-unit systems**: for `ε > 0` and finite
`n : κ → Type*`, some `δ > 0` puts every `δ`-approx unital system within `ε` of an exact one. -/
theorem exists_pos_forall_exists_isUnitalMatrixUnitSystem_norm_sub_lt {κ : Type*} (n : κ → Type*)
    [Fintype κ] [∀ r, Fintype (n r)] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A : Type*} [CStarAlgebra A] {x : ∀ r : κ, n r → n r → A},
      IsApproxMatrixUnitSystem δ x → ‖matrixUnitSupport x - 1‖ < δ →
      ∃ e : ∀ r : κ, n r → n r → A, IsUnitalMatrixUnitSystem e ∧ ∀ r i j, ‖e r i j - x r i j‖ < ε :=
  let ⟨δ, hδ_pos, hδ⟩ := exists_pos_forall_exists_isUnitalMatrixUnitSystem_mem_norm_sub_lt n hε
  ⟨δ, hδ_pos, fun {A} _ {_} hx hsupp ↦
    let ⟨e, _, h⟩ := hδ (𝕜' := ℝ) (s := (⊤ : NonUnitalStarSubalgebra ℝ A))
      (fun _ _ _ ↦ NonUnitalStarAlgebra.mem_top) hx hsupp
    ⟨e, h⟩⟩
end TauCeti

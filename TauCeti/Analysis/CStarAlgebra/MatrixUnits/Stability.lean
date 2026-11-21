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
  have hsq : ‖x r i j‖ ^ 2 < 3 + (1 / 2) * ‖x r i j‖ + 1 / 2 := by
    rw [sq, ← CStarRing.norm_star_mul_self, show star (x r i j) * x r i j =
      x r j j + (star (x r i j) - x r j i) * x r i j + (x r j i * x r i j - x r j j) by
        simp only [sub_mul]; abel]
    refine norm_add₃_le.trans_lt ?_
    linarith [norm_mul_le_of_le ((hx.norm_star_sub_lt r i j).le.trans hδ) (le_refl ‖x r i j‖),
      (hx.norm_mul_same_sub_lt r j i j).trans_le hδ]
  nlinarith
private lemma norm_star_mul_self_sub_lt [NonUnitalCStarAlgebra A] {z y y' d p : A} {α δ β : ℝ}
    (hz : ‖z‖ ≤ 3) (hy : ‖y‖ ≤ 3) (hzy : ‖z - y‖ ≤ α) (hstar : ‖star y - y'‖ < δ)
    (hmul : ‖y' * y - d‖ < δ) (hpd : ‖p - d‖ < β) : ‖star z * z - p‖ < 6 * α + 4 * δ + β := by
  rw [show star z * z - p = (star (z - y) * z + star y * (z - y) + (star y - y') * y +
      (y' * y - d)) + (d - p) by simp only [star_sub, sub_mul, mul_sub]; abel]
  refine (norm_add_le_of_le norm_add₄_le le_rfl).trans_lt ?_; rw [norm_sub_rev d p]
  linarith [norm_mul_le_of_le ((norm_star (z - y)).le.trans hzy) hz,
    norm_mul_le_of_le ((norm_star y).le.trans hy) hzy, norm_mul_le_of_le hstar.le hy]
private lemma exists_column_partialIsometry {𝕜' S : Type*} [NonUnitalCStarAlgebra A] [Monoid 𝕜']
    [MulAction 𝕜' A] [SetLike S A] [NonUnitalSubringClass S A] [SMul ℝ 𝕜']
    [IsScalarTower ℝ 𝕜' A] [SMulMemClass S 𝕜' A] [StarMemClass S A] {s : S}
    [IsClosed (s : Set A)] {δ η : ℝ} (hη_le : η ≤ 1 / 32) (hδ_half : δ ≤ 1 / 2)
    (hδ_η : δ ≤ η / 200) {x : ∀ r : κ, n r → n r → A} (hx : IsApproxMatrixUnitSystem δ x)
    (hx_mem : ∀ r i j, x r i j ∈ s) {p : ∀ r : κ, n r → A} (hp_mem : ∀ r i, p r i ∈ s)
    (hp_proj : ∀ r i, IsStarProjection (p r i))
    (hp_dist : ∀ r i, ‖p r i - x r i i‖ < η / 200) (r : κ) (i i₀ : n r) :
    ∃ v ∈ s, IsPartialIsometry v ∧ star v * v = p r i₀ ∧ v * star v = p r i ∧
      ‖v - x r i i₀‖ < 11 * η := by
  have hη_pos : 0 < η := by linarith [hp_dist r i, norm_nonneg (p r i - x r i i)]
  have hx_le (a b : n r) : ‖x r a b‖ ≤ 3 := (hx.norm_lt_three hδ_half r a b).le
  set z : A := p r i * x r i i₀ * p r i₀
  have hz_norm : ‖z‖ ≤ 3 := (norm_mul_le_of_le (norm_mul_le_of_le ((hp_proj r i).norm_le _)
    (hx_le i i₀)) ((hp_proj r i₀).norm_le _)).trans_eq (by norm_num)
  have hz_sub_x : ‖z - x r i i₀‖ < (16 / 200) * η := by
    rw [show z - x r i i₀ = (p r i - x r i i) * x r i i₀ * p r i₀ +
        x r i i * x r i i₀ * (p r i₀ - x r i₀ i₀) +
        (x r i i * x r i i₀ - x r i i₀) * x r i₀ i₀ + (x r i i₀ * x r i₀ i₀ - x r i i₀) by
      dsimp [z]; simp only [sub_mul, mul_sub]; abel]
    refine norm_add₄_le.trans_lt ?_
    linarith [norm_mul_le_of_le (norm_mul_le_of_le (hp_dist r i).le (hx_le i i₀))
        ((hp_proj r i₀).norm_le _),
      norm_mul_le_of_le (norm_mul_le_of_le (hx_le i i) (hx_le i i₀)) (hp_dist r i₀).le,
      norm_mul_le_of_le (hx.norm_mul_same_sub_lt r i i i₀).le (hx_le i₀ i₀),
      hx.norm_mul_same_sub_lt r i i₀ i₀]
  have hz_init : ‖star z * z - p r i₀‖ < η :=
    (norm_star_mul_self_sub_lt hz_norm (hx_le i i₀) hz_sub_x.le (hx.norm_star_sub_lt r i i₀)
      (hx.norm_mul_same_sub_lt r i₀ i i₀) (hp_dist r i₀)).trans_le (by linarith)
  have hstar_z_sub : ‖star z - x r i₀ i‖ ≤ (17 / 200) * η := by
    rw [show star z - x r i₀ i = star (z - x r i i₀) + (star (x r i i₀) - x r i₀ i) by
      rw [star_sub, sub_add_sub_cancel]]
    exact (norm_add_le_of_le ((norm_star _).le.trans hz_sub_x.le)
      ((hx.norm_star_sub_lt r i i₀).le.trans hδ_η)).trans_eq (by ring)
  have hz_fin : ‖z * star z - p r i‖ < η := by
    simpa only [star_star] using (norm_star_mul_self_sub_lt (z := star z)
      ((norm_star z).le.trans hz_norm) (hx_le i₀ i) hstar_z_sub (hx.norm_star_sub_lt r i₀ i)
      (hx.norm_mul_same_sub_lt r i i₀ i) (hp_dist r i)).trans_le (by linarith)
  obtain ⟨v, hv_mem, hv_pi, hv_init, hv_fin, hv_dist_z⟩ :=
    exists_isPartialIsometry_mem_of_approx (𝕜' := 𝕜') (s := s) (z := z) hη_le (hp_proj r i₀)
      (hp_proj r i) (mul_mem (mul_mem (hp_mem r i) (hx_mem r i i₀)) (hp_mem r i₀))
      (by dsimp [z]; rw [← mul_assoc, ← mul_assoc, (hp_proj r i).isIdempotentElem.eq])
      (by dsimp [z]; rw [mul_assoc, (hp_proj r i₀).isIdempotentElem.eq]) hz_init hz_fin
  exact ⟨v, hv_mem, hv_pi, hv_init, hv_fin,
    by linarith [norm_sub_le_norm_sub_add_norm_sub v z (x r i i₀)]⟩
end IsApproxMatrixUnitSystem
end
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
  obtain ⟨p, hp_mem, hp_proj, hp_ortho, hp_dist⟩ :=
    hδ_diag (𝕜' := 𝕜') (s := s) (d := fun u : Σ r : κ, n r ↦ x u.1 u.2 u.2)
      (fun u ↦ hx_mem u.1 u.2 u.2)
      (fun u ↦ by rw [norm_sub_rev]; exact (hx.norm_star_sub_lt u.1 u.2 u.2).trans_le hδ_le)
      (fun u ↦ (hx.norm_mul_same_sub_lt u.1 u.2 u.2 u.2).trans_le hδ_le)
      (fun ⟨r, i⟩ ⟨t, j⟩ huw ↦ by
        by_cases hrt : r = t
        · subst hrt; exact (hx.norm_mul_lt_of_ne r i j fun h ↦ huw (congrArg _ h)).trans_le hδ_le
        · exact (hx.norm_mul_lt_of_block_ne hrt i i j j).trans_le hδ_le)
  have hv_exists (r : κ) (i : n r) :=
    hx.exists_column_partialIsometry (𝕜' := 𝕜') (s := s) (min_le_left _ _) (min_le_left _ _)
      ((min_le_right _ _).trans (min_le_right _ _)) hx_mem (fun r i ↦ hp_mem ⟨r, i⟩)
      (fun r i ↦ hp_proj ⟨r, i⟩) (fun r i ↦ hp_dist ⟨r, i⟩) r i (Classical.choice ⟨i⟩)
  choose v hv_mem hv_pi hv_init hv_fin hv_dist using hv_exists
  refine ⟨fun r i j ↦ v r i * star (v r j),
    fun r i j ↦ mul_mem (hv_mem r i) (star_mem (hv_mem r j)),
    IsMatrixUnitSystem.of_partialIsometry hv_pi (fun r i j ↦ by rw [hv_init r i, hv_init r j])
      (fun u w huw ↦ by
        rw [onFun, hv_fin, hv_fin]; exact (hp_ortho huw).mul_eq_zero' (hp_proj w).isSelfAdjoint),
    fun r i j ↦ ?_⟩
  let i₀ : n r := Classical.choice ⟨i⟩
  have hx_i_norm : ‖x r i i₀‖ ≤ 3 := (hx.norm_lt_three (min_le_left _ _) r i i₀).le
  rw [show v r i * star (v r j) - x r i j =
      (v r i - x r i i₀) * star (v r j) + x r i i₀ * star (v r j - x r j i₀) +
        x r i i₀ * (star (x r j i₀) - x r i₀ j) + (x r i i₀ * x r i₀ j - x r i j) by
    simp only [star_sub, sub_mul, mul_sub]; abel]
  refine norm_add₄_le.trans_lt ?_
  linarith [norm_mul_le_of_le (hv_dist r i).le ((norm_star _).le.trans (hv_pi r j).norm_le_one),
    norm_mul_le_of_le hx_i_norm ((norm_star (v r j - x r j i₀)).le.trans (hv_dist r j).le),
    norm_mul_le_of_le hx_i_norm (hx.norm_star_sub_lt r j i₀).le,
    hx.norm_mul_same_sub_lt r i i₀ j, show η ≤ ε / 60 from min_le_right _ _,
    show δ ≤ η / 200 from (min_le_right _ _).trans (min_le_right _ _)]
/-- **Uniform norm stability of finite multi-block matrix-unit systems**: for `ε > 0` and finite
`n : κ → Type*`, some `δ > 0` (independent of `A`) puts `δ`-approx systems within `ε` of exact. -/
theorem exists_pos_forall_exists_isMatrixUnitSystem_norm_sub_lt {κ : Type*} (n : κ → Type*)
    [Finite κ] [∀ r, Finite (n r)] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A : Type*} [NonUnitalCStarAlgebra A] {x : ∀ r : κ, n r → n r → A},
      IsApproxMatrixUnitSystem δ x →
      ∃ e : ∀ r : κ, n r → n r → A, IsMatrixUnitSystem e ∧ ∀ r i j, ‖e r i j - x r i j‖ < ε :=
  let ⟨δ, hδ_pos, hδ⟩ := exists_pos_forall_exists_isMatrixUnitSystem_mem_norm_sub_lt n hε
  ⟨δ, hδ_pos, fun {A} _ {_} hx ↦ by
    have : IsClosed ((⊤ : NonUnitalStarSubalgebra ℝ A) : Set A) := by simp
    obtain ⟨e, -, h⟩ := hδ (𝕜' := ℝ) (s := (⊤ : NonUnitalStarSubalgebra ℝ A))
      (fun _ _ _ ↦ NonUnitalStarAlgebra.mem_top) hx; exact ⟨e, h⟩⟩
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
  refine ⟨e, he_mem, ⟨he, he.isStarProjection_support.eq_one_of_norm_sub_one_lt_one ?_⟩,
    fun r i j ↦ (he_dist r i j).trans_le (min_le_left _ _)⟩
  have hsum_le : ‖matrixUnitSupport e - matrixUnitSupport x‖ ≤ (M : ℝ) * ε' := by
    simp only [matrixUnitSupport_def, ← Finset.sum_sub_distrib, M, Nat.cast_sum, Finset.sum_mul]
    exact (norm_sum_le _ _).trans <| Finset.sum_le_sum fun r _ ↦
      (norm_sum_le _ _).trans <| (Finset.sum_le_sum fun i _ ↦ (he_dist r i i).le).trans (by simp)
  have hε'_le : 2 * (M + 1 : ℝ) * ε' ≤ 1 := (le_div_iff₀' (by positivity)).mp (min_le_right _ _)
  nlinarith [norm_sub_le_norm_sub_add_norm_sub (matrixUnitSupport e) (matrixUnitSupport x) 1,
    min_le_right δ₀ (1 / 2), show (0 : ℝ) < ε' by positivity]
/-- **Uniform norm stability of unital finite matrix-unit systems**: for `ε > 0` and finite
`n : κ → Type*`, some `δ > 0` puts every `δ`-approx unital system within `ε` of an exact one. -/
theorem exists_pos_forall_exists_isUnitalMatrixUnitSystem_norm_sub_lt {κ : Type*} (n : κ → Type*)
    [Fintype κ] [∀ r, Fintype (n r)] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A : Type*} [CStarAlgebra A] {x : ∀ r : κ, n r → n r → A},
      IsApproxMatrixUnitSystem δ x → ‖matrixUnitSupport x - 1‖ < δ →
      ∃ e : ∀ r : κ, n r → n r → A, IsUnitalMatrixUnitSystem e ∧ ∀ r i j, ‖e r i j - x r i j‖ < ε :=
  let ⟨δ, hδ_pos, hδ⟩ := exists_pos_forall_exists_isUnitalMatrixUnitSystem_mem_norm_sub_lt n hε
  ⟨δ, hδ_pos, fun {A} _ {_} hx hsupp ↦ by
    have : IsClosed ((⊤ : NonUnitalStarSubalgebra ℝ A) : Set A) := by simp
    obtain ⟨e, -, h⟩ := hδ (𝕜' := ℝ) (s := (⊤ : NonUnitalStarSubalgebra ℝ A))
      (fun _ _ _ ↦ NonUnitalStarAlgebra.mem_top) hx hsupp; exact ⟨e, h⟩⟩
end TauCeti

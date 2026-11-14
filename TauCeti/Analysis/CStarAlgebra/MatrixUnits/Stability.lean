/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import TauCeti.Algebra.Star.MatrixUnits
public import TauCeti.Analysis.CStarAlgebra.PartialIsometry
public import TauCeti.Analysis.CStarAlgebra.Projection.Stability

/-!
# Norm stability of matrix units in C⋆-algebras

Homomorphisms from a finite-dimensional C⋆-algebra `⨁ᵣ M_{n r}(ℂ)` into a C⋆-algebra `A` are
parameterized by finite multi-block systems of matrix units (`TauCeti.IsMatrixUnitSystem`). When
lifting finite-dimensional subalgebras from quotients, passing to inductive limits, or working with
locally finite-dimensional (AF) approximations, one encounters families `x r i j` satisfying the
matrix-unit adjoint and multiplication relations only up to a small norm tolerance `δ`.

This file proves that finite multi-block systems of matrix units—both non-unital and unital—are
**uniformly norm-stable** across all C⋆-algebras: for every `ε > 0` and finite block-index data
`n : κ → Type*`, there exists `δ > 0` depending **only** on `ε` and the cardinalities of `κ` and
each `n r` (independent of the C⋆-algebra `A` and of any closed non-unital `ℂ`-`⋆`-subalgebra `s`)
such that every `δ`-approximate system of matrix units in `s` lies entrywise within `ε` of an exact
system of matrix units in `s` (and, in a unital C⋆-algebra, an exact unital system whenever
`‖matrixUnitSupport x - 1‖ < δ`).

## Main definitions

* `TauCeti.IsApproxMatrixUnitSystem`: multi-block matrix-unit adjoint and multiplication relations
  holding up to norm `< δ`.

## Main results

* `TauCeti.exists_pos_isMatrixUnitSystem_mem`, `TauCeti.exists_pos_isMatrixUnitSystem`: uniform
  norm stability of finite multi-block systems of matrix units (with and without closed
  `ℂ`-`⋆`-subalgebra preservation).
* `TauCeti.exists_pos_isUnitalMatrixUnitSystem_mem`,
  `TauCeti.exists_pos_isUnitalMatrixUnitSystem`: uniform norm stability of unital finite
  multi-block systems of matrix units.

## References

* B. Blackadar, *Operator Algebras*, Springer (2006), Proposition II.8.3.23.
* K. R. Davidson, *C*-Algebras by Example*, Amer. Math. Soc. (1996), Chapter III, §7.
-/

public section

open Function

namespace TauCeti

/-- A multi-block family `x` is a **`δ`-approximate system of matrix units** if the adjoint and
multiplication relations of `IsMatrixUnitSystem` hold up to norm `< δ`. -/
@[mk_iff]
structure IsApproxMatrixUnitSystem {κ A : Type*} {n : κ → Type*} [SeminormedAddCommGroup A] [Mul A]
    [Star A] (δ : ℝ) (x : ∀ r : κ, n r → n r → A) : Prop where
  /-- Taking the star approximately transposes indices within each block. -/
  norm_star_sub_lt (r : κ) (i j : n r) : ‖star (x r i j) - x r j i‖ < δ
  /-- Composable entries within a block approximately contract the middle index. -/
  norm_mul_same_sub_lt (r : κ) (i j l : n r) : ‖x r i j * x r j l - x r i l‖ < δ
  /-- Non-composable entries within a block have product of norm `< δ`. -/
  norm_mul_ne_lt (r : κ) (i : n r) {j k : n r} (l : n r) : j ≠ k → ‖x r i j * x r k l‖ < δ
  /-- Entries from distinct blocks have product of norm `< δ`. -/
  norm_mul_block_ne_lt {r t : κ} : r ≠ t → ∀ (i j : n r) (k l : n t), ‖x r i j * x t k l‖ < δ

namespace IsMatrixUnitSystem

/-- Every exact system of matrix units is a `δ`-approximate system for every `δ > 0`. -/
theorem isApproxMatrixUnitSystem {κ A : Type*} {n : κ → Type*} [NonUnitalSeminormedRing A]
    [Star A] {e : ∀ r : κ, n r → n r → A} (he : IsMatrixUnitSystem e) {δ : ℝ} (hδ : 0 < δ) :
    IsApproxMatrixUnitSystem δ e where
  norm_star_sub_lt r i j := by simp [he.star_eq, hδ]
  norm_mul_same_sub_lt r i j l := by simp [he.mul_same, hδ]
  norm_mul_ne_lt r i {_ _} l hjk := by simp [he.mul_ne r i l hjk, hδ]
  norm_mul_block_ne_lt hrs i j k l := by simp [he.mul_block_ne hrs i j k l, hδ]

end IsMatrixUnitSystem

namespace IsApproxMatrixUnitSystem

/-- Monotonicity of `IsApproxMatrixUnitSystem` in the tolerance `δ`. -/
theorem mono {κ A : Type*} {n : κ → Type*} [SeminormedAddCommGroup A] [Mul A] [Star A] {δ₁ δ₂ : ℝ}
    {x : ∀ r : κ, n r → n r → A} (hx : IsApproxMatrixUnitSystem δ₁ x) (h : δ₁ ≤ δ₂) :
    IsApproxMatrixUnitSystem δ₂ x where
  norm_star_sub_lt r i j := (hx.norm_star_sub_lt r i j).trans_le h
  norm_mul_same_sub_lt r i j l := (hx.norm_mul_same_sub_lt r i j l).trans_le h
  norm_mul_ne_lt r i {_ _} l hjk := (hx.norm_mul_ne_lt r i l hjk).trans_le h
  norm_mul_block_ne_lt hrs i j k l := (hx.norm_mul_block_ne_lt hrs i j k l).trans_le h

/-- Every entry of a `δ`-approximate system of matrix units with `δ ≤ 1 / 2` has norm `< 3`. -/
theorem norm_lt_three {κ A : Type*} {n : κ → Type*} [NonUnitalCStarAlgebra A] {δ : ℝ}
    {x : ∀ r : κ, n r → n r → A} (hx : IsApproxMatrixUnitSystem δ x) (hδ : δ ≤ 1 / 2) (r : κ)
    (i j : n r) : ‖x r i j‖ < 3 := by
  have hdiag : ‖x r j j‖ < 3 := norm_lt_three_of_approx_projection
    (by rw [norm_sub_rev]; exact (hx.norm_star_sub_lt r j j).trans_le (by linarith))
    ((hx.norm_mul_same_sub_lt r j j j).trans_le (by linarith))
  have hsq : ‖x r i j‖ ^ 2 < 3 + (1 / 2) * ‖x r i j‖ + 1 / 2 := by
    rw [sq, ← CStarRing.norm_star_mul_self,
      show star (x r i j) * x r i j =
        x r j j + (star (x r i j) - x r j i) * x r i j + (x r j i * x r i j - x r j j) by
        simp only [sub_mul]; abel]
    refine norm_add₃_le.trans_lt ?_
    linarith [norm_mul_le_of_le ((hx.norm_star_sub_lt r i j).le.trans hδ) (le_refl ‖x r i j‖),
      (hx.norm_mul_same_sub_lt r j i j).trans_le hδ]
  by_contra hge; nlinarith [not_lt.mp hge]

private lemma norm_star_mul_self_sub_lt {A : Type*} [NonUnitalCStarAlgebra A]
    {z y y' d p : A} {α δ β : ℝ} (hz : ‖z‖ ≤ 3) (hy : ‖y‖ ≤ 3)
    (hzy : ‖z - y‖ ≤ α) (hstar : ‖star y - y'‖ < δ) (hmul : ‖y' * y - d‖ < δ)
    (hpd : ‖p - d‖ < β) :
    ‖star z * z - p‖ < 6 * α + 4 * δ + β := by
  rw [show star z * z - p =
      (star (z - y) * z + star y * (z - y) + (star y - y') * y + (y' * y - d)) + (d - p) by
    simp only [star_sub, sub_mul, mul_sub]; abel]
  refine (norm_add_le_of_le norm_add₄_le (le_refl _)).trans_lt ?_
  have hdp : ‖d - p‖ < β := by rwa [norm_sub_rev]
  linarith [norm_mul_le_of_le ((norm_star (z - y)).le.trans hzy) hz,
    norm_mul_le_of_le ((norm_star y).le.trans hy) hzy,
    norm_mul_le_of_le hstar.le hy]

private lemma exists_column_partialIsometry {κ A S : Type*} {n : κ → Type*}
    [NonUnitalCStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A]
    [SMulMemClass S ℂ A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)]
    {δ η : ℝ} (hη_le : η ≤ 1 / 32) (hδ_half : δ ≤ 1 / 2) (hδ_η : δ ≤ η / 200)
    {x : ∀ r : κ, n r → n r → A} (hx : IsApproxMatrixUnitSystem δ x)
    (hx_mem : ∀ r i j, x r i j ∈ s)
    {p : ∀ r : κ, n r → A} (hp_mem : ∀ r i, p r i ∈ s)
    (hp_proj : ∀ r i, IsStarProjection (p r i))
    (hp_dist : ∀ r i, ‖p r i - x r i i‖ < η / 200) (r : κ) (i i₀ : n r) :
    ∃ v ∈ s, IsPartialIsometry v ∧ star v * v = p r i₀ ∧ v * star v = p r i ∧
      ‖v - x r i i₀‖ < 11 * η := by
  have hx_le (a b : n r) : ‖x r a b‖ ≤ 3 := (hx.norm_lt_three hδ_half r a b).le
  set z : A := p r i * x r i i₀ * p r i₀
  have hz_mem : z ∈ s := mul_mem (mul_mem (hp_mem r i) (hx_mem r i i₀)) (hp_mem r i₀)
  have hqz : p r i * z = z := by
    dsimp [z]; rw [← mul_assoc, ← mul_assoc, (hp_proj r i).isIdempotentElem.eq]
  have hzp : z * p r i₀ = z := by dsimp [z]; rw [mul_assoc, (hp_proj r i₀).isIdempotentElem.eq]
  have hpri_norm : ‖p r i‖ ≤ 1 := (hp_proj r i).norm_le _
  have hpri₀_norm : ‖p r i₀‖ ≤ 1 := (hp_proj r i₀).norm_le _
  have hz_norm : ‖z‖ ≤ 3 := by
    simpa using norm_mul_le_of_le (norm_mul_le_of_le hpri_norm (hx_le i i₀)) hpri₀_norm
  have hz_sub_x : ‖z - x r i i₀‖ < (16 / 200) * η := by
    rw [show z - x r i i₀ = (p r i - x r i i) * x r i i₀ * p r i₀ +
        x r i i * x r i i₀ * (p r i₀ - x r i₀ i₀) +
        (x r i i * x r i i₀ - x r i i₀) * x r i₀ i₀ + (x r i i₀ * x r i₀ i₀ - x r i i₀) by
      dsimp [z]; simp only [sub_mul, mul_sub]; abel]
    refine norm_add₄_le.trans_lt ?_
    linarith [
      norm_mul_le_of_le (norm_mul_le_of_le (hp_dist r i).le (hx_le i i₀)) hpri₀_norm,
      norm_mul_le_of_le (norm_mul_le_of_le (hx_le i i) (hx_le i i₀)) (hp_dist r i₀).le,
      norm_mul_le_of_le (hx.norm_mul_same_sub_lt r i i i₀).le (hx_le i₀ i₀),
      hx.norm_mul_same_sub_lt r i i₀ i₀]
  have hz_init : ‖star z * z - p r i₀‖ < η :=
    (norm_star_mul_self_sub_lt hz_norm (hx_le i i₀) hz_sub_x.le
      (hx.norm_star_sub_lt r i i₀) (hx.norm_mul_same_sub_lt r i₀ i i₀) (hp_dist r i₀)).trans_le
      (by linarith [norm_nonneg (z - x r i i₀)])
  have hstar_z_sub : ‖star z - x r i₀ i‖ ≤ (17 / 200) * η := by
    rw [show star z - x r i₀ i = star (z - x r i i₀) + (star (x r i i₀) - x r i₀ i) by
      rw [star_sub, sub_add_sub_cancel]]
    exact (norm_add_le_of_le ((norm_star _).le.trans hz_sub_x.le)
      ((hx.norm_star_sub_lt r i i₀).le.trans hδ_η)).trans_eq (by ring)
  have hz_fin : ‖z * star z - p r i‖ < η := by
    have h := norm_star_mul_self_sub_lt (z := star z) ((norm_star z).le.trans hz_norm)
      (hx_le i₀ i) hstar_z_sub (hx.norm_star_sub_lt r i₀ i) (hx.norm_mul_same_sub_lt r i i₀ i)
      (hp_dist r i)
    rw [star_star] at h
    exact h.trans_le (by linarith [norm_nonneg (z - x r i i₀)])
  obtain ⟨v, hv_mem, hv_pi, hv_init, hv_fin, hv_dist_z⟩ :=
    exists_isPartialIsometry_mem_of_approx (s := s) hη_le (hp_proj r i₀) (hp_proj r i)
      hz_mem hqz hzp hz_init hz_fin
  exact ⟨v, hv_mem, hv_pi, hv_init, hv_fin,
    by linarith [norm_sub_le_norm_sub_add_norm_sub v z (x r i i₀), norm_nonneg (z - x r i i₀)]⟩

end IsApproxMatrixUnitSystem

/-- **Uniform norm stability of finite multi-block systems of matrix units in closed
`ℂ`-`⋆`-subalgebras**: for every `ε > 0` and finite index family `n : κ → Type*`, there exists
`δ > 0` depending only on `ε` and the cardinalities of `κ` and each `n r` (independent of `A` and
`s`) such that every `δ`-approximate system `x` with entries in a closed non-unital
`ℂ`-`⋆`-subalgebra `s` of `A` lies entrywise within `ε` of an exact system `e` of matrix units in
`s`. -/
theorem exists_pos_isMatrixUnitSystem_mem {κ : Type*} (n : κ → Type*) [Finite κ]
    [∀ r, Finite (n r)] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A S : Type*} [NonUnitalCStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A]
      [SMulMemClass S ℂ A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)]
      {x : ∀ r : κ, n r → n r → A}, (∀ r i j, x r i j ∈ s) → IsApproxMatrixUnitSystem δ x →
      ∃ e : ∀ r : κ, n r → n r → A,
        (∀ r i j, e r i j ∈ s) ∧ IsMatrixUnitSystem e ∧ ∀ r i j, ‖e r i j - x r i j‖ < ε := by
  set η : ℝ := min (1 / 32) (ε / 60)
  obtain ⟨δ_diag, hδ_diag_pos, hδ_diag⟩ :=
    exists_pos_pairwise_isStarOrtho_isStarProjection_mem (Σ r : κ, n r)
      (show 0 < η / 200 by positivity)
  set δ : ℝ := min (1 / 2) (min δ_diag (η / 200))
  refine ⟨δ, by positivity, fun {A S} _ _ _ _ _ {s} _ {x} hx_mem hx ↦ ?_⟩
  have hδ_half : δ ≤ 1 / 2 := min_le_left _ _
  have hδ_le_diag : δ ≤ δ_diag := (min_le_right _ _).trans (min_le_left _ _)
  have hδ_le_η : δ ≤ η / 200 := (min_le_right _ _).trans (min_le_right _ _)
  -- Step 1: Jointly stabilize all diagonal approximate projections `x r i i` inside `s`.
  obtain ⟨p_sig, hp_mem, hp_proj, hp_ortho, hp_dist⟩ :=
    hδ_diag (s := s) (d := fun u : Σ r : κ, n r ↦ x u.1 u.2 u.2) (fun u ↦ hx_mem u.1 u.2 u.2)
      (fun u ↦ by rw [norm_sub_rev]; exact (hx.norm_star_sub_lt u.1 u.2 u.2).trans_le hδ_le_diag)
      (fun u ↦ (hx.norm_mul_same_sub_lt u.1 u.2 u.2 u.2).trans_le hδ_le_diag)
      (fun u w huw ↦ by
        rcases u with ⟨r, i⟩; rcases w with ⟨t, j⟩
        by_cases hrt : r = t
        · subst hrt
          exact (hx.norm_mul_ne_lt r i j fun h ↦ huw (congrArg (Sigma.mk r) h)).trans_le hδ_le_diag
        · exact (hx.norm_mul_block_ne_lt hrt i i j j).trans_le hδ_le_diag)
  -- Step 2: Extract a column of partial isometries `v r i` in each block via polar perturbation.
  have hv_exists (r : κ) (i : n r) :=
    hx.exists_column_partialIsometry (s := s) (min_le_left _ _) hδ_half hδ_le_η hx_mem
      (fun r i ↦ hp_mem ⟨r, i⟩) (fun r i ↦ hp_proj ⟨r, i⟩) (fun r i ↦ hp_dist ⟨r, i⟩)
      r i (Classical.choice ⟨i⟩)
  choose v hv_mem hv_pi hv_init hv_fin hv_dist using hv_exists
  -- Step 3: Reconstruct `e r i j = v r i * star (v r j)` and bound `‖e r i j - x r i j‖ < ε`.
  refine ⟨fun r i j ↦ v r i * star (v r j),
    fun r i j ↦ mul_mem (hv_mem r i) (star_mem (hv_mem r j)),
    IsMatrixUnitSystem.of_partialIsometry hv_pi (fun r i j ↦ by rw [hv_init r i, hv_init r j])
      (fun u w huw ↦ by
        dsimp [onFun]; rw [hv_fin u.1 u.2, hv_fin w.1 w.2]
        exact (hp_ortho huw).mul_eq_zero' (hp_proj w).isSelfAdjoint),
    fun r i j ↦ ?_⟩
  let i₀ : n r := Classical.choice ⟨i⟩
  have hx_i_norm : ‖x r i i₀‖ ≤ 3 := (hx.norm_lt_three hδ_half r i i₀).le
  rw [show v r i * star (v r j) - x r i j =
      (v r i - x r i i₀) * star (v r j) + x r i i₀ * star (v r j - x r j i₀) +
        x r i i₀ * (star (x r j i₀) - x r i₀ j) + (x r i i₀ * x r i₀ j - x r i j) by
    simp only [star_sub, sub_mul, mul_sub]; abel]
  refine norm_add₄_le.trans_lt ?_
  linarith [
    norm_mul_le_of_le (hv_dist r i).le ((norm_star (v r j)).le.trans (hv_pi r j).norm_le_one),
    norm_mul_le_of_le hx_i_norm ((norm_star (v r j - x r j i₀)).le.trans (hv_dist r j).le),
    norm_mul_le_of_le hx_i_norm (hx.norm_star_sub_lt r j i₀).le,
    hx.norm_mul_same_sub_lt r i i₀ j, norm_nonneg (v r i - x r i i₀),
    show η ≤ ε / 60 from min_le_right _ _]

/-- **Uniform norm stability of finite multi-block systems of matrix units**: for every `ε > 0` and
finite index family `n : κ → Type*`, there exists `δ > 0` depending only on `ε` and the
cardinalities of `κ` and each `n r` (independent of `A`) such that every `δ`-approximate system `x`
in a C⋆-algebra `A` lies entrywise within `ε` of an exact system `e` of matrix units. -/
theorem exists_pos_isMatrixUnitSystem {κ : Type*} (n : κ → Type*) [Finite κ]
    [∀ r, Finite (n r)] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A : Type*} [NonUnitalCStarAlgebra A] {x : ∀ r : κ, n r → n r → A},
      IsApproxMatrixUnitSystem δ x →
      ∃ e : ∀ r : κ, n r → n r → A, IsMatrixUnitSystem e ∧ ∀ r i j, ‖e r i j - x r i j‖ < ε := by
  obtain ⟨δ, hδ_pos, hδ⟩ := exists_pos_isMatrixUnitSystem_mem n hε
  refine ⟨δ, hδ_pos, fun {A} _ {_} hx ↦ ?_⟩
  have : IsClosed ((⊤ : NonUnitalStarSubalgebra ℂ A) : Set A) := isClosed_univ
  obtain ⟨e, -, he, hdist⟩ := hδ (s := (⊤ : NonUnitalStarSubalgebra ℂ A)) (fun _ _ _ ↦ trivial) hx
  exact ⟨e, he, hdist⟩

/-- **Uniform norm stability of unital finite multi-block systems of matrix units in closed
`ℂ`-`⋆`-subalgebras**: for every `ε > 0` and finite index family `n : κ → Type*`, there exists
`δ > 0` depending only on `ε` and the cardinalities of `κ` and each `n r` (independent of `A` and
`s`) such that every `δ`-approximate system `x` in a closed non-unital `ℂ`-`⋆`-subalgebra `s` of a
unital C⋆-algebra `A` satisfying `‖matrixUnitSupport x - 1‖ < δ` lies entrywise within `ε` of an
exact unital system `e` of matrix units in `s`. -/
theorem exists_pos_isUnitalMatrixUnitSystem_mem {κ : Type*} (n : κ → Type*) [Fintype κ]
    [∀ r, Fintype (n r)] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A S : Type*} [CStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A]
      [SMulMemClass S ℂ A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)]
      {x : ∀ r : κ, n r → n r → A}, (∀ r i j, x r i j ∈ s) → IsApproxMatrixUnitSystem δ x →
      ‖matrixUnitSupport x - 1‖ < δ →
      ∃ e : ∀ r : κ, n r → n r → A,
        (∀ r i j, e r i j ∈ s) ∧ IsUnitalMatrixUnitSystem e ∧
        ∀ r i j, ‖e r i j - x r i j‖ < ε := by
  set M : ℕ := ∑ r : κ, Fintype.card (n r)
  set ε' : ℝ := min ε (1 / (2 * (M + 1 : ℝ)))
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := exists_pos_isMatrixUnitSystem_mem n (show 0 < ε' by positivity)
  set δ : ℝ := min δ₀ (1 / 2)
  refine ⟨δ, by positivity, fun {A S} _ _ _ _ _ {s} _ {x} hx_mem hx hsupp_x ↦ ?_⟩
  obtain ⟨e, he_mem, he, he_dist⟩ := hδ₀ hx_mem (hx.mono (min_le_left _ _))
  refine ⟨e, he_mem, ⟨he, ?_⟩, fun r i j ↦ (he_dist r i j).trans_le (min_le_left _ _)⟩
  apply he.isStarProjection_support.eq_one_of_norm_sub_one_lt_one
  have hsum_le : ‖matrixUnitSupport e - matrixUnitSupport x‖ ≤ (M : ℝ) * ε' := by
    simp only [matrixUnitSupport_def, ← Finset.sum_sub_distrib, M, Nat.cast_sum, Finset.sum_mul]
    exact (norm_sum_le _ _).trans <| Finset.sum_le_sum fun r _ ↦
      (norm_sum_le _ _).trans <| (Finset.sum_le_sum fun i _ ↦ (he_dist r i i).le).trans (by simp)
  have hM_lt : (M : ℝ) * ε' < 1 / 2 :=
    calc (M : ℝ) * ε' ≤ (M : ℝ) * (1 / (2 * (M + 1 : ℝ))) := by gcongr; exact min_le_right _ _
      _ < ((M : ℝ) + 1) * (1 / (2 * (M + 1 : ℝ))) := by gcongr; linarith
      _ = 1 / 2 := by field_simp
  linarith [norm_sub_le_norm_sub_add_norm_sub (matrixUnitSupport e) (matrixUnitSupport x) 1,
    min_le_right δ₀ (1 / 2)]

/-- **Uniform norm stability of unital finite multi-block systems of matrix units**: for every
`ε > 0` and finite index family `n : κ → Type*`, there exists `δ > 0` depending only on `ε` and the
cardinalities of `κ` and each `n r` (independent of `A`) such that every `δ`-approximate system `x`
in a unital C⋆-algebra `A` satisfying `‖matrixUnitSupport x - 1‖ < δ` lies entrywise within `ε` of
an exact unital system `e` of matrix units. -/
theorem exists_pos_isUnitalMatrixUnitSystem {κ : Type*} (n : κ → Type*) [Fintype κ]
    [∀ r, Fintype (n r)] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A : Type*} [CStarAlgebra A] {x : ∀ r : κ, n r → n r → A},
      IsApproxMatrixUnitSystem δ x → ‖matrixUnitSupport x - 1‖ < δ →
      ∃ e : ∀ r : κ, n r → n r → A,
        IsUnitalMatrixUnitSystem e ∧ ∀ r i j, ‖e r i j - x r i j‖ < ε := by
  obtain ⟨δ, hδ_pos, hδ⟩ := exists_pos_isUnitalMatrixUnitSystem_mem n hε
  refine ⟨δ, hδ_pos, fun {A} _ {_} hx hsupp ↦ ?_⟩
  have : IsClosed ((⊤ : NonUnitalStarSubalgebra ℂ A) : Set A) := isClosed_univ
  obtain ⟨e, -, he, hdist⟩ :=
    hδ (s := (⊤ : NonUnitalStarSubalgebra ℂ A)) (fun _ _ _ ↦ trivial) hx hsupp
  exact ⟨e, he, hdist⟩

end TauCeti

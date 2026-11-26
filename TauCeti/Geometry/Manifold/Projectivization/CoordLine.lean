/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import TauCeti.Geometry.Manifold.Projectivization.Map

import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The coordinate line of projective space

The coordinate line `ℓ : ℙ¹ → ℙᵐ⁺¹`, `[v₀ : v₁] ↦ [v₀ : v₁ : 0 : ⋯ : 0]`
(`Projectivization.coordLine`), is induced by the inclusion of the first two coordinates
(`Projectivization.coordLineEmbedding`). It is analytic (`Projectivization.contMDiff_coordLine`),
and this file computes it in the standard affine charts of `ℙᵐ⁺¹` that contain it.

For `a ∈ {0, 1}`, the standard affine chart `a` of `ℙᵐ⁺¹` has the coordinates `vⱼ / vₐ` for
`j ≠ a`, enumerated by `Fin.succAbove a`. Its first coordinate is `v_b / vₐ` for the other index
`b` of the line, and its coordinates `l ≥ 1` are the normal coordinates `v_{l+1} / vₐ`; on the line
these vanish (`Projectivization.affineChart_castLE_coordLine`). Between the charts `a ≠ b` the
change of coordinates is `w ↦ (w₀⁻¹, w₁ / w₀, …, wₘ / w₀)`
(`Projectivization.affineChart_castLE_symm_trans_apply`), so at a point `(z, 0, …, 0)` of the
line its derivative is the diagonal matrix `(-z⁻², z⁻¹, …, z⁻¹)`
(`Projectivization.hasFDerivAt_affineChart_castLE_symm_trans`).

The chart `a` is the preferred chart at the coordinate point `[e_a]`
(`Projectivization.coordLineCenter`, `Projectivization.chartAt_coordLineCenter`), and it contains
the points of the line in the affine open `a` of `ℙ¹`.

## Main declarations

* `Projectivization.coordLineEmbedding`, `Projectivization.coordLine`: the coordinate line in
  `ℙᵐ⁺¹`.
* `Projectivization.contMDiff_coordLine`: the coordinate line is analytic.
* `Projectivization.affineChart_castLE_coordLine`: the coordinate line in the charts `0` and `1`.
* `Projectivization.hasFDerivAt_affineChart_castLE_symm_trans`: the derivative of the changes
  between the charts `0` and `1`, at the points of the line.
* `Projectivization.coordLineCenter`: the coordinate points `[e₀]` and `[e₁]`, whose preferred
  charts are the charts `0` and `1`.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 1, §1
  (the standard affine charts of projective space).
-/

public noncomputable section

open Set
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace Projectivization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] (m : ℕ)

/-! ### The coordinate line -/

section Line

/-- The inclusion `𝕜² → 𝕜ᵐ⁺²` of the first two coordinates, extending by zero. -/
def coordLineEmbedding : (Fin 2 → 𝕜) →ₗ[𝕜] Fin (m + 2) → 𝕜 :=
  Function.ExtendByZero.linearMap 𝕜 𝕜 (Fin.castLE (Nat.le_add_left 2 m))

variable {m}

/-- The coordinate `a ∈ {0, 1}` of `coordLineEmbedding v` is that of `v`. -/
@[simp]
theorem coordLineEmbedding_apply_castLE (v : Fin 2 → 𝕜) (a : Fin 2) :
    coordLineEmbedding m v (Fin.castLE (Nat.le_add_left 2 m) a) = v a :=
  (Fin.castLE_injective _).extend_apply v 0 a

/-- The coordinates `l + 2` of `coordLineEmbedding v` vanish. -/
@[simp]
theorem coordLineEmbedding_apply_succ_succ (v : Fin 2 → 𝕜) (l : Fin m) :
    coordLineEmbedding m v l.succ.succ = 0 := by
  refine Function.extend_apply' _ _ _ fun ⟨a, ha⟩ ↦ ?_
  have h := congrArg Fin.val ha
  simp only [Fin.val_castLE, Fin.val_succ] at h
  omega

variable (m) in
/-- The inclusion of the first two coordinates is injective. -/
theorem coordLineEmbedding_injective : Function.Injective (coordLineEmbedding (𝕜 := 𝕜) m) :=
  Function.extend_injective (Fin.castLE_injective (Nat.le_add_left 2 m)) 0

variable (m) in
/-- **The coordinate line** `[v₀ : v₁] ↦ [v₀ : v₁ : 0 : ⋯ : 0]` from the projective line to
`ℙᵐ⁺¹`. -/
def coordLine : ℙ 𝕜 (Fin 2 → 𝕜) → ℙ 𝕜 (Fin (m + 2) → 𝕜) :=
  map (coordLineEmbedding m) (coordLineEmbedding_injective m)

variable (m) in
/-- The coordinate line is analytic, and so `C^r` for every `r`. -/
theorem contMDiff_coordLine (r : ℕ∞ω) :
    ContMDiff 𝓘(𝕜, Fin 1 → 𝕜) 𝓘(𝕜, Fin (m + 1) → 𝕜) r (coordLine (𝕜 := 𝕜) m) :=
  contMDiff_map _ _ r

@[simp]
theorem coordLine_mk (v : Fin 2 → 𝕜) (hv : v ≠ 0) :
    coordLine m (mk 𝕜 v hv) =
      mk 𝕜 (coordLineEmbedding m v) ((map_ne_zero_iff _ (coordLineEmbedding_injective m)).2 hv) :=
  map_mk _ _ _ _

/-- The point `ℓ x`, in the homogeneous coordinates of the chosen representative of `x`. -/
theorem coordLine_eq_mk (x : ℙ 𝕜 (Fin 2 → 𝕜)) :
    coordLine m x =
      mk 𝕜 (coordLineEmbedding m x.rep) ((map_ne_zero_iff _ (coordLineEmbedding_injective m)).2
        x.rep_ne_zero) := by
  conv_lhs => rw [← mk_rep x]
  exact coordLine_mk _ _

/-- The line meets the affine open `a ∈ {0, 1}` of `ℙᵐ⁺¹` in the affine open `a` of `ℙ¹`. -/
@[simp]
theorem coordLine_mem_affineOpen_castLE_iff (x : ℙ 𝕜 (Fin 2 → 𝕜)) (a : Fin 2) :
    coordLine m x ∈ affineOpen (Fin.castLE (Nat.le_add_left 2 m) a) ↔ x ∈ affineOpen a := by
  rw [coordLine_eq_mk, mk_mem_affineOpen_iff, coordLineEmbedding_apply_castLE, mem_affineOpen_iff]

end Line

/-! ### The charts along the line -/

section Chart

variable {m}

/-- In `ℙᵐ⁺¹`, the first coordinate of the chart `a ∈ {0, 1}` is the homogeneous coordinate `b`,
for the other index `b` of the line. -/
private theorem succAbove_castLE_zero {a b : Fin 2} (hab : a ≠ b) :
    (Fin.castLE (Nat.le_add_left 2 m) a).succAbove 0 = Fin.castLE (Nat.le_add_left 2 m) b := by
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  · ext
    simp [Fin.succAbove]
  · ext
    simp [Fin.succAbove, Fin.lt_def]
  · exact absurd rfl hab

/-- In `ℙᵐ⁺¹`, the coordinate `l + 1` of the chart `a ∈ {0, 1}` is the homogeneous coordinate
`l + 2`, normal to the line. -/
private theorem succAbove_castLE_succ (a : Fin 2) (l : Fin m) :
    (Fin.castLE (Nat.le_add_left 2 m) a).succAbove l.succ = l.succ.succ := by
  rw [Fin.succAbove_of_le_castSucc]
  simp only [Fin.le_def, Fin.val_castLE, Fin.val_castSucc, Fin.val_succ]
  omega

/-- **The line in the chart `a`.** In the chart `a ∈ {0, 1}` of `ℙᵐ⁺¹`, a point of the line has
the coordinates `(v_b / vₐ, 0, …, 0)`, for the other index `b` of the line. -/
theorem affineChart_castLE_coordLine {a b : Fin 2} (hab : a ≠ b) (x : ℙ 𝕜 (Fin 2 → 𝕜)) :
    affineChart (Fin.castLE (Nat.le_add_left 2 m) a) (coordLine m x) =
      Fin.cons (x.rep b / x.rep a) 0 := by
  rw [coordLine_eq_mk, affineChart_mk]
  funext l
  refine Fin.cases ?_ (fun l ↦ ?_) l
  · simp [succAbove_castLE_zero hab]
  · simp [succAbove_castLE_succ]

/-- **The change between the charts of the line.** From the chart `a` to the chart `b ≠ a` of
`ℙᵐ⁺¹`, both containing the line, the coordinates change by `w ↦ (w₀⁻¹, w₁ / w₀, …, wₘ / w₀)`. -/
theorem affineChart_castLE_symm_trans_apply {a b : Fin 2} (hab : a ≠ b) (w : Fin (m + 1) → 𝕜) :
    (affineChart (K := 𝕜) (Fin.castLE (Nat.le_add_left 2 m) a)).symm.trans
        (affineChart (Fin.castLE (Nat.le_add_left 2 m) b)) w =
      Fin.cons (w 0)⁻¹ fun l ↦ w l.succ / w 0 := by
  rw [affineChart_symm_trans_apply]
  funext l
  refine Fin.cases ?_ (fun l ↦ ?_) l
  · rw [Fin.cons_zero, succAbove_castLE_zero hab.symm, ← succAbove_castLE_zero hab,
      Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, one_div]
  · rw [Fin.cons_succ, succAbove_castLE_succ b l, ← succAbove_castLE_succ a l,
      ← succAbove_castLE_zero hab, Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]

/-- **The derivative of the change of charts along the line.** At a point `(z, 0, …, 0)` of the
line in the chart `a`, the derivative of the change to the chart `b ≠ a` is the diagonal matrix
`(-z⁻², z⁻¹, …, z⁻¹)`. -/
theorem hasFDerivAt_affineChart_castLE_symm_trans {a b : Fin 2} (hab : a ≠ b) {z : 𝕜} (hz : z ≠ 0) :
    HasFDerivAt ((affineChart (K := 𝕜) (Fin.castLE (Nat.le_add_left 2 m) a)).symm.trans
        (affineChart (Fin.castLE (Nat.le_add_left 2 m) b)))
      (ContinuousLinearMap.mul 𝕜 (Fin (m + 1) → 𝕜) (Fin.cons (-(z⁻¹ ^ 2)) fun _ ↦ z⁻¹))
      (Fin.cons z 0) := by
  have hfun : ⇑((affineChart (K := 𝕜) (Fin.castLE (Nat.le_add_left 2 m) a)).symm.trans
      (affineChart (Fin.castLE (Nat.le_add_left 2 m) b))) =
        fun w : Fin (m + 1) → 𝕜 ↦ Fin.cons (w 0)⁻¹ fun l ↦ w l.succ / w 0 :=
    funext (affineChart_castLE_symm_trans_apply hab)
  rw [hfun]
  set w₀ : Fin (m + 1) → 𝕜 := Fin.cons z 0
  have hw₀ : w₀ 0 = z := Fin.cons_zero _ _
  have hinv : HasFDerivAt (fun w : Fin (m + 1) → 𝕜 ↦ (w 0)⁻¹)
      ((ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) (-(z ^ 2)⁻¹)).comp
        (ContinuousLinearMap.proj 0)) w₀ := by
    have h := (hasDerivAt_inv (𝕜 := 𝕜) (x := w₀ 0) (by rwa [hw₀])).hasFDerivAt
    rw [hw₀] at h
    exact h.comp w₀ (hasFDerivAt_apply (𝕜 := 𝕜) 0 w₀)
  refine hasFDerivAt_pi'' fun l ↦ ?_
  refine Fin.cases ?_ (fun l ↦ ?_) l
  · refine hinv.congr_fderiv ?_
    ext u
    simp [inv_pow, mul_comm]
  · simp only [Fin.cons_succ, div_eq_mul_inv]
    refine ((hasFDerivAt_apply (𝕜 := 𝕜) l.succ w₀).fun_mul hinv).congr_fderiv ?_
    ext u
    simp [w₀, mul_comm]

end Chart

/-! ### The coordinate points of the coordinate line -/

section CoordinatePoint

variable {m}

/-- The coordinate point `[e_a]` of `ℙᵐ⁺¹`, for `a ∈ {0, 1}`: the center of the chart `a`, whose
preferred chart is the chart `a`. -/
def coordLineCenter (a : Fin 2) : ℙ 𝕜 (Fin (m + 2) → 𝕜) :=
  mk 𝕜 (Pi.single (Fin.castLE (Nat.le_add_left 2 m) a) 1) (by simp)

/-- The preferred chart at `[e_a]` is the chart `a` of `ℙᵐ⁺¹`. -/
theorem chartAt_coordLineCenter (a : Fin 2) :
    chartAt (Fin (m + 1) → 𝕜) (coordLineCenter (𝕜 := 𝕜) (m := m) a) =
      affineOpenPartialHomeomorph (Fin.castLE (Nat.le_add_left 2 m) a) :=
  chartAt_mk_single _

/-- The chart of `[e_a]` contains the points of the line in the affine open `a` of `ℙ¹`. -/
theorem coordLine_mem_chartAt_coordLineCenter_source {x : ℙ 𝕜 (Fin 2 → 𝕜)} {a : Fin 2}
    (hx : x ∈ affineOpen a) :
    coordLine m x ∈ (chartAt (Fin (m + 1) → 𝕜) (coordLineCenter (𝕜 := 𝕜) (m := m) a)).source := by
  rwa [chartAt_coordLineCenter, affineOpenPartialHomeomorph_toPartialEquiv, affineChart_source,
    coordLine_mem_affineOpen_castLE_iff]

end CoordinatePoint

end Projectivization

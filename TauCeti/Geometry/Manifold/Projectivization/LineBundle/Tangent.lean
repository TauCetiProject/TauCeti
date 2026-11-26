/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Projectivization.LineBundle.Canonical
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle.Sum
public import TauCeti.Geometry.Manifold.Projectivization.Map
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The tangent bundle of projective space along a line is `𝒪(2) ⊕ 𝒪(1)ᵐ`

Let `𝕜` be a complete nontrivially normed field and `ℓ : ℙ¹ → ℙᵐ⁺¹` the coordinate line
`[v₀ : v₁] ↦ [v₀ : v₁ : 0 : ⋯ : 0]` (`Projectivization.line`), induced by the inclusion of the first
two coordinates (`Projectivization.lineEmbedding`). This file proves that the pullback `ℓ* Tℙᵐ⁺¹`
of the tangent bundle is the split bundle `𝒪(2) ⊕ 𝒪(1)ᵐ` on `ℙ¹`
(`Projectivization.twistSumCore (lineTwist m)`, the summand `0` being `𝒪(2)` and the others
`𝒪(1)`), as analytic vector bundles (`Projectivization.lineTangentDiffeomorph`). For `𝕜 = ℂ` this
is the holomorphic splitting `ℓ* TℂPⁿ ≅ 𝒪(2) ⊕ 𝒪(1)ⁿ⁻¹`. In every chart, the summand `𝒪(2)` is the
coordinate along the line and the summands `𝒪(1)` are the coordinates normal to it. For `m = 0`
the line is the identity of `ℙ¹`, and the statement is `Tℙ¹ ≅ 𝒪(2)`.

**Coordinates along the line.** For `a ∈ {0, 1}`, the standard affine chart `a` of `ℙᵐ⁺¹` has the
coordinates `vⱼ / vₐ` for `j ≠ a`, enumerated by `Fin.succAbove a`. Its first coordinate is
`v_b / vₐ` for the other index `b` of the line, and its coordinates `l ≥ 1` are the normal
coordinates `v_{l+1} / vₐ`; on the line these vanish
(`Projectivization.affineChart_castLE_line`). Between the charts `a ≠ b` the change of
coordinates is `w ↦ (w₀⁻¹, w₁ / w₀, …, wₘ / w₀)` (`Projectivization.lineChartChange_apply`), so at
a point of the line, where `w₀ = v_b / vₐ` and the other coordinates vanish, its derivative is the
diagonal matrix `(-t², t, …, t)` with `t = vₐ / v_b`
(`Projectivization.hasFDerivAt_lineChartChange`). Up to the sign `-1` on the tangent coordinate,
these are the transitions `t²` of `𝒪(2)` and `t` of `𝒪(1)`.

**The isomorphism.** As for the canonical bundle of `ℙ¹`
(`Projectivization.twistEquivCanonicalBundle`), the sign is absorbed by the signs `εₐ` of the
Euler form (`Projectivization.eulerFormSign`): reading a tangent vector of `ℙᵐ⁺¹` at a point of
the line in the chart `a`, and multiplying its tangent coordinate by `εₐ`, gives a vector of
`𝒪(2) ⊕ 𝒪(1)ᵐ` in the frame of the chart `a`, and this does not depend on `a`
(`Projectivization.twistSumCore_coordChange_lineFrameSign_mul`). These fibrewise isomorphisms
(`Projectivization.lineTangentEquiv`) are analytic in the trivializations
(`Projectivization.contMDiff_lineTangentEquiv`), so they form an analytic diffeomorphism of total
spaces over `ℙ¹`.

The splitting `u* TℂPⁿ ≅ 𝒪(2) ⊕ 𝒪(1)ⁿ⁻¹` is the input for the regularity of the lines of `ℂPⁿ`
as holomorphic spheres: since `H¹(ℂP¹, 𝒪(k)) = 0` for `k ≥ -1`, the linearized Cauchy–Riemann
operator along a line is onto.

## Main declarations

* `Projectivization.lineEmbedding`, `Projectivization.line`: the coordinate line in `ℙᵐ⁺¹`.
* `Projectivization.lineTwist m`: the twists `(2, 1, …, 1)` of `𝒪(2) ⊕ 𝒪(1)ᵐ`.
* `Projectivization.hasFDerivAt_lineChartChange`: the derivative of the changes of the charts of
  the line, at the points of the line.
* `Projectivization.lineTangentEquiv`: the fibrewise isomorphisms `T_{ℓ x}ℙᵐ⁺¹ ≃ (𝒪(2) ⊕ 𝒪(1)ᵐ)ₓ`.
* `Projectivization.lineTangentDiffeomorph`: the analytic diffeomorphism of total spaces
  `ℓ* Tℙᵐ⁺¹ ≃ 𝒪(2) ⊕ 𝒪(1)ᵐ` over `ℙ¹`.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 0, §5 and
  Chapter 1, §1 (the tangent bundle of projective space).
* W. Fulton and R. Pandharipande, *Notes on stable maps and quantum cohomology*, in *Algebraic
  geometry, Santa Cruz 1995*, Proc. Sympos. Pure Math. 62, Part 2, AMS, 1997, Lemma 10 (the
  vanishing of `H¹(C, μ* T_X)` for genus-zero maps to convex targets such as `ℙʳ`, which this
  splitting gives for lines).
-/

public noncomputable section

open Bundle Set
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace Projectivization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] (m : ℕ)

/-! ### The coordinate line -/

section Line

/-- The inclusion `𝕜² → 𝕜ᵐ⁺²` of the first two coordinates, extending by zero. -/
def lineEmbedding : (Fin 2 → 𝕜) →ₗ[𝕜] Fin (m + 2) → 𝕜 :=
  Function.ExtendByZero.linearMap 𝕜 𝕜 (Fin.castLE (Nat.le_add_left 2 m))

variable {m}

/-- The coordinate `a ∈ {0, 1}` of `lineEmbedding v` is that of `v`. -/
@[simp]
theorem lineEmbedding_apply_castLE (v : Fin 2 → 𝕜) (a : Fin 2) :
    lineEmbedding m v (Fin.castLE (Nat.le_add_left 2 m) a) = v a :=
  (Fin.castLE_injective _).extend_apply v 0 a

/-- The coordinates `l + 2` of `lineEmbedding v` vanish. -/
@[simp]
theorem lineEmbedding_apply_succ_succ (v : Fin 2 → 𝕜) (l : Fin m) :
    lineEmbedding m v l.succ.succ = 0 := by
  refine Function.extend_apply' _ _ _ fun ⟨a, ha⟩ ↦ ?_
  have h := congrArg Fin.val ha
  simp only [Fin.val_castLE, Fin.val_succ] at h
  omega

variable (m) in
/-- The inclusion of the first two coordinates is injective. -/
theorem lineEmbedding_injective : Function.Injective (lineEmbedding (𝕜 := 𝕜) m) :=
  fun v w h ↦ funext fun a ↦ by
    simpa using congrFun h (Fin.castLE (Nat.le_add_left 2 m) a)

variable (m) in
/-- **The coordinate line** `[v₀ : v₁] ↦ [v₀ : v₁ : 0 : ⋯ : 0]` from the projective line to
`ℙᵐ⁺¹`. -/
def line : ℙ 𝕜 (Fin 2 → 𝕜) → ℙ 𝕜 (Fin (m + 2) → 𝕜) :=
  map (lineEmbedding m) (lineEmbedding_injective m)

@[simp]
theorem line_mk (v : Fin 2 → 𝕜) (hv : v ≠ 0) :
    line m (mk 𝕜 v hv) =
      mk 𝕜 (lineEmbedding m v) ((map_ne_zero_iff _ (lineEmbedding_injective m)).2 hv) :=
  map_mk _ _ _ _

/-- The point `ℓ x`, in the homogeneous coordinates of the chosen representative of `x`. -/
theorem line_eq_mk (x : ℙ 𝕜 (Fin 2 → 𝕜)) :
    line m x =
      mk 𝕜 (lineEmbedding m x.rep) ((map_ne_zero_iff _ (lineEmbedding_injective m)).2
        x.rep_ne_zero) := by
  conv_lhs => rw [← mk_rep x]
  exact line_mk _ _

/-- The line meets the affine open `a ∈ {0, 1}` of `ℙᵐ⁺¹` in the affine open `a` of `ℙ¹`. -/
@[simp]
theorem line_mem_affineOpen_castLE_iff (x : ℙ 𝕜 (Fin 2 → 𝕜)) (a : Fin 2) :
    line m x ∈ affineOpen (Fin.castLE (Nat.le_add_left 2 m) a) ↔ x ∈ affineOpen a := by
  rw [line_eq_mk, mk_mem_affineOpen_iff, lineEmbedding_apply_castLE, mem_affineOpen_iff]

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
theorem affineChart_castLE_line {a b : Fin 2} (hab : a ≠ b) (x : ℙ 𝕜 (Fin 2 → 𝕜)) :
    affineChart (Fin.castLE (Nat.le_add_left 2 m) a) (line m x) =
      Fin.cons (x.rep b / x.rep a) 0 := by
  rw [line_eq_mk, affineChart_mk]
  funext l
  refine Fin.cases ?_ (fun l ↦ ?_) l
  · simp [succAbove_castLE_zero hab]
  · simp [succAbove_castLE_succ]

/-- **The change between the charts of the line.** From the chart `a` to the chart `b ≠ a` of
`ℙᵐ⁺¹`, both containing the line, the coordinates change by `w ↦ (w₀⁻¹, w₁ / w₀, …, wₘ / w₀)`. -/
theorem lineChartChange_apply {a b : Fin 2} (hab : a ≠ b) (w : Fin (m + 1) → 𝕜) :
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
theorem hasFDerivAt_lineChartChange {a b : Fin 2} (hab : a ≠ b) {z : 𝕜} (hz : z ≠ 0) :
    HasFDerivAt ((affineChart (K := 𝕜) (Fin.castLE (Nat.le_add_left 2 m) a)).symm.trans
        (affineChart (Fin.castLE (Nat.le_add_left 2 m) b)))
      (ContinuousLinearMap.mul 𝕜 (Fin (m + 1) → 𝕜) (Fin.cons (-(z⁻¹ ^ 2)) fun _ ↦ z⁻¹))
      (Fin.cons z 0) := by
  have hfun : ⇑((affineChart (K := 𝕜) (Fin.castLE (Nat.le_add_left 2 m) a)).symm.trans
      (affineChart (Fin.castLE (Nat.le_add_left 2 m) b))) =
        fun w : Fin (m + 1) → 𝕜 ↦ Fin.cons (w 0)⁻¹ fun l ↦ w l.succ / w 0 :=
    funext (lineChartChange_apply hab)
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

/-! ### The coordinate points of the line -/

section CoordinatePoint

variable {m}

/-- The coordinate point `[e_a]` of `ℙᵐ⁺¹`, for `a ∈ {0, 1}`: the centre of the chart `a`, whose
preferred chart is the chart `a`. -/
def lineCentre (a : Fin 2) : ℙ 𝕜 (Fin (m + 2) → 𝕜) :=
  mk 𝕜 (Pi.single (Fin.castLE (Nat.le_add_left 2 m) a) 1) (by simp)

/-- The preferred chart at `[e_a]` is the chart `a` of `ℙᵐ⁺¹`. -/
theorem chartAt_lineCentre (a : Fin 2) :
    chartAt (Fin (m + 1) → 𝕜) (lineCentre (𝕜 := 𝕜) (m := m) a) =
      affineOpenPartialHomeomorph (Fin.castLE (Nat.le_add_left 2 m) a) :=
  chartAt_mk_single _

/-- The chart of `[e_a]` contains the points of the line in the affine open `a` of `ℙ¹`. -/
theorem line_mem_chartAt_lineCentre_source {x : ℙ 𝕜 (Fin 2 → 𝕜)} {a : Fin 2}
    (hx : x ∈ affineOpen a) :
    line m x ∈ (chartAt (Fin (m + 1) → 𝕜) (lineCentre (𝕜 := 𝕜) (m := m) a)).source := by
  rwa [chartAt_lineCentre, affineOpenPartialHomeomorph_toPartialEquiv, affineChart_source,
    line_mem_affineOpen_castLE_iff]

/-- **The tangent coordinate changes along the line.** At a point `x` of the line in the affine
opens `a ≠ b` of `ℙ¹`, the derivative of the change from the chart `a` to the chart `b` of `ℙᵐ⁺¹`
is the diagonal matrix `(-t², t, …, t)`, for the transition `t = xₐ / x_b` of `𝒪(1)`. -/
theorem tangentCoordChange_lineCentre {a b : Fin 2} (hab : a ≠ b) {x : ℙ 𝕜 (Fin 2 → 𝕜)}
    (ha : x ∈ affineOpen a) (hb : x ∈ affineOpen b) :
    tangentCoordChange 𝓘(𝕜, Fin (m + 1) → 𝕜) (lineCentre a) (lineCentre b) (line m x) =
      ContinuousLinearMap.mul 𝕜 (Fin (m + 1) → 𝕜)
        (Fin.cons (-(twistTransition 1 a b x ^ 2)) fun _ ↦ twistTransition 1 a b x) := by
  have hz : x.rep b / x.rep a ≠ 0 :=
    div_ne_zero ((mem_affineOpen_iff b x).1 hb) ((mem_affineOpen_iff a x).1 ha)
  have hd := (hasFDerivAt_lineChartChange (m := m) hab hz).fderiv
  rw [PartialEquiv.coe_trans] at hd
  have hchart : tangentCoordChange 𝓘(𝕜, Fin (m + 1) → 𝕜) (lineCentre a) (lineCentre b)
      (line m x) = fderiv 𝕜 (affineChart (Fin.castLE (Nat.le_add_left 2 m) b) ∘
        (affineChart (Fin.castLE (Nat.le_add_left 2 m) a)).symm)
        (affineChart (Fin.castLE (Nat.le_add_left 2 m) a) (line m x)) := by
    simp [chartAt_lineCentre]
  rw [hchart, affineChart_castLE_line hab, hd, twistTransition_def, zpow_one, inv_div]

end CoordinatePoint

/-! ### The frames of `𝒪(2) ⊕ 𝒪(1)ᵐ` -/

section Frame

variable {m}

variable (m) in
/-- The twists `(2, 1, …, 1)` of the split bundle `𝒪(2) ⊕ 𝒪(1)ᵐ` on `ℙ¹`. -/
def lineTwist : Fin (m + 1) → ℤ :=
  Fin.cons 2 fun _ ↦ 1

@[simp]
theorem lineTwist_zero : lineTwist m 0 = 2 :=
  (rfl)

@[simp]
theorem lineTwist_succ (l : Fin m) : lineTwist m l.succ = 1 :=
  (rfl)

/-- The sign `(εₐ, 1, …, 1)` relating the coordinates of a tangent vector in the chart `a` of
`ℙᵐ⁺¹` to those of the corresponding vector of `𝒪(2) ⊕ 𝒪(1)ᵐ` in the frame of the chart `a`:
the tangent coordinate carries the sign `εₐ = eulerFormSign a` of the Euler form, as in the
isomorphism `𝒪(-2) ≃ K_ℙ¹`. -/
def lineFrameSign (a : Fin 2) : Fin (m + 1) → 𝕜 :=
  Fin.cons (eulerFormSign a) 1

/-- The sign of a frame is an involution. -/
theorem lineFrameSign_mul_self (a : Fin 2) :
    lineFrameSign (𝕜 := 𝕜) (m := m) a * lineFrameSign a = 1 := by
  funext l
  refine Fin.cases ?_ (fun l ↦ ?_) l <;> simp [lineFrameSign, eulerFormSign_mul_self]

/-- **The frames agree.** At a point `x` of the line in the affine opens `a` and `b` of `ℙ¹`,
reading a tangent vector of `ℙᵐ⁺¹` in the chart `a` and multiplying it by the sign of the frame `a`
gives the vector of `𝒪(2) ⊕ 𝒪(1)ᵐ` whose coordinates in the frame `b` are those of the tangent
vector in the chart `b`, multiplied by the sign of the frame `b`. -/
theorem twistSumCore_coordChange_lineFrameSign_mul {a b : Fin 2} {x : ℙ 𝕜 (Fin 2 → 𝕜)}
    (ha : x ∈ affineOpen a) (hb : x ∈ affineOpen b) (w : Fin (m + 1) → 𝕜) :
    (twistSumCore (lineTwist m)).coordChange a b x (lineFrameSign a * w) =
      lineFrameSign b *
        tangentCoordChange 𝓘(𝕜, Fin (m + 1) → 𝕜) (lineCentre a) (lineCentre b) (line m x) w := by
  rcases eq_or_ne a b with rfl | hab
  · rw [tangentCoordChange_self (by rw [extChartAt_source]; exact
        line_mem_chartAt_lineCentre_source ha),
      (twistSumCore (lineTwist m)).coordChange_self _ _ (by rwa [twistSumCore_baseSet])]
  rw [tangentCoordChange_lineCentre hab ha hb]
  funext l
  have hab' := eulerFormSign_mul_of_ne (𝕜 := 𝕜) hab
  have hb' := eulerFormSign_mul_self (𝕜 := 𝕜) b
  refine Fin.cases ?_ (fun l ↦ ?_) l
  · simp only [twistSumCore_coordChange_apply, lineTwist_zero, Pi.mul_apply, lineFrameSign,
      Fin.cons_zero, ContinuousLinearMap.mul_apply']
    rw [show (2 : ℤ) = 1 + 1 from rfl, twistTransition_add 1 1 ha hb]
    linear_combination (twistTransition 1 a b x * twistTransition 1 a b x * w 0) *
      (eulerFormSign b * hab' - eulerFormSign a * hb')
  · simp [lineFrameSign]

end Frame

/-! ### The isomorphism -/

section Equiv

variable {m}

/-- The bundled analytic coordinate line, along which the tangent bundle of `ℙᵐ⁺¹` is pulled
back. -/
def lineContMDiffMap :
    C^ω⟮𝓘(𝕜, Fin 1 → 𝕜), ℙ 𝕜 (Fin 2 → 𝕜); 𝓘(𝕜, Fin (m + 1) → 𝕜), ℙ 𝕜 (Fin (m + 2) → 𝕜)⟯ :=
  ⟨line m, contMDiff_map _ _ ω⟩

/-- The bundled coordinate line is the coordinate line. -/
@[simp]
theorem coe_lineContMDiffMap : ⇑(lineContMDiffMap (𝕜 := 𝕜) (m := m)) = line m :=
  (rfl)

variable (𝕜 m) in
/-- The pullback `ℓ* Tℙᵐ⁺¹` of the tangent bundle of `ℙᵐ⁺¹` along the coordinate line `ℓ`: its
fibre at `x ∈ ℙ¹` is the tangent space of `ℙᵐ⁺¹` at `ℓ x`. -/
abbrev LineTangentSpace : ℙ 𝕜 (Fin 2 → 𝕜) → Type _ :=
  (lineContMDiffMap (𝕜 := 𝕜) (m := m) : ℙ 𝕜 (Fin 2 → 𝕜) → ℙ 𝕜 (Fin (m + 2) → 𝕜)) *ᵖ
    (TangentSpace 𝓘(𝕜, Fin (m + 1) → 𝕜))

/-- The tangent vector of `ℙᵐ⁺¹` at `ℓ x` read in the frame of the preferred chart `a` of `x`:
its coordinates in the chart `a` of `ℙᵐ⁺¹`, with the tangent coordinate multiplied by `εₐ`. -/
private def lineTangentMap (x : ℙ 𝕜 (Fin 2 → 𝕜)) :
    (Fin (m + 1) → 𝕜) →L[𝕜] (Fin (m + 1) → 𝕜) :=
  (ContinuousLinearMap.mul 𝕜 (Fin (m + 1) → 𝕜)
    (lineFrameSign ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x))).comp
    (tangentCoordChange 𝓘(𝕜, Fin (m + 1) → 𝕜) (line m x)
      (lineCentre ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x)) (line m x))

/-- The inverse of `lineTangentMap x`. -/
private def lineTangentMapInv (x : ℙ 𝕜 (Fin 2 → 𝕜)) :
    (Fin (m + 1) → 𝕜) →L[𝕜] (Fin (m + 1) → 𝕜) :=
  (tangentCoordChange 𝓘(𝕜, Fin (m + 1) → 𝕜)
      (lineCentre ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x)) (line m x)
      (line m x)).comp
    (ContinuousLinearMap.mul 𝕜 (Fin (m + 1) → 𝕜)
      (lineFrameSign ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x)))

private theorem line_mem_inter (x : ℙ 𝕜 (Fin 2 → 𝕜)) :
    line m x ∈ (extChartAt 𝓘(𝕜, Fin (m + 1) → 𝕜) (line m x)).source ∩
      (extChartAt 𝓘(𝕜, Fin (m + 1) → 𝕜)
        (lineCentre ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x))).source ∩
      (extChartAt 𝓘(𝕜, Fin (m + 1) → 𝕜) (line m x)).source := by
  have hc := line_mem_chartAt_lineCentre_source (𝕜 := 𝕜) (m := m)
    (mem_affineOpen_twistSumCore_indexAt (lineTwist m) x)
  simp only [extChartAt_source]
  exact ⟨⟨mem_chart_source _ _, hc⟩, mem_chart_source _ _⟩

private theorem line_mem_inter' (x : ℙ 𝕜 (Fin 2 → 𝕜)) :
    line m x ∈ (extChartAt 𝓘(𝕜, Fin (m + 1) → 𝕜)
        (lineCentre ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x))).source ∩
      (extChartAt 𝓘(𝕜, Fin (m + 1) → 𝕜) (line m x)).source ∩
      (extChartAt 𝓘(𝕜, Fin (m + 1) → 𝕜)
        (lineCentre ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x))).source := by
  have h := line_mem_inter (𝕜 := 𝕜) (m := m) x
  exact ⟨⟨h.1.2, h.2⟩, h.1.2⟩

private theorem lineTangentMap_lineTangentMapInv (x : ℙ 𝕜 (Fin 2 → 𝕜)) (v : Fin (m + 1) → 𝕜) :
    lineTangentMap x (lineTangentMapInv x v) = v := by
  simp only [lineTangentMap, lineTangentMapInv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply']
  rw [tangentCoordChange_comp (line_mem_inter' x), tangentCoordChange_self, ← mul_assoc,
    lineFrameSign_mul_self, one_mul]
  rw [extChartAt_source]
  exact line_mem_chartAt_lineCentre_source (mem_affineOpen_twistSumCore_indexAt (lineTwist m) x)

private theorem lineTangentMapInv_lineTangentMap (x : ℙ 𝕜 (Fin 2 → 𝕜)) (v : Fin (m + 1) → 𝕜) :
    lineTangentMapInv x (lineTangentMap x v) = v := by
  simp only [lineTangentMap, lineTangentMapInv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply', ← mul_assoc, lineFrameSign_mul_self, one_mul]
  rw [tangentCoordChange_comp (line_mem_inter x), tangentCoordChange_self]
  rw [extChartAt_source]
  exact mem_chart_source _ _

/-- **The fibres of `ℓ* Tℙᵐ⁺¹ ≅ 𝒪(2) ⊕ 𝒪(1)ᵐ`.** At `x ∈ ℙ¹`, with preferred chart `a`, a tangent
vector of `ℙᵐ⁺¹` at `ℓ x` goes to the vector of `𝒪(2) ⊕ 𝒪(1)ᵐ` whose coordinates in the frame of
the chart `a` are its coordinates in the chart `a` of `ℙᵐ⁺¹`, the tangent coordinate multiplied by
the sign `εₐ` of the Euler form (`Projectivization.lineTangentEquiv_apply`). -/
def lineTangentEquiv (x : ℙ 𝕜 (Fin 2 → 𝕜)) :
    LineTangentSpace 𝕜 m x ≃L[𝕜]
      (twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).Fiber x :=
  -- Both fibres are the model space `Fin (m + 1) → 𝕜`, by definition.
  ContinuousLinearEquiv.ofContinuousLinearMap (lineTangentMap x) (lineTangentMapInv x)
    (ContinuousLinearMap.ext (lineTangentMap_lineTangentMapInv x))
    (ContinuousLinearMap.ext (lineTangentMapInv_lineTangentMap x))

/-- At `x`, with preferred chart `a`, the image of a tangent vector `v` of `ℙᵐ⁺¹` at `ℓ x` has the
coordinates of `v` in the chart `a` of `ℙᵐ⁺¹`, the tangent coordinate multiplied by `εₐ`. -/
theorem lineTangentEquiv_apply (x : ℙ 𝕜 (Fin 2 → 𝕜))
    (v : LineTangentSpace 𝕜 m x) :
    (lineTangentEquiv x v : Fin (m + 1) → 𝕜) =
      lineFrameSign ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x) *
        tangentCoordChange 𝓘(𝕜, Fin (m + 1) → 𝕜) (line m x)
          (lineCentre ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x)) (line m x) v :=
  (rfl)

/-- At `x`, with preferred chart `a`, the tangent vector of `ℙᵐ⁺¹` at `ℓ x` corresponding to a
vector of `𝒪(2) ⊕ 𝒪(1)ᵐ` with coordinates `c` in the frame of the chart `a` has the coordinates `c`
in the chart `a` of `ℙᵐ⁺¹`, the tangent coordinate multiplied by `εₐ`. -/
theorem lineTangentEquiv_symm_apply (x : ℙ 𝕜 (Fin 2 → 𝕜)) (c : Fin (m + 1) → 𝕜) :
    ((lineTangentEquiv x).symm c : Fin (m + 1) → 𝕜) =
      tangentCoordChange 𝓘(𝕜, Fin (m + 1) → 𝕜)
        (lineCentre ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x)) (line m x)
        (line m x) (lineFrameSign ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x) * c) :=
  (rfl)

/-- **The isomorphism in the trivializations of a chart.** Read in the trivialization of
`𝒪(2) ⊕ 𝒪(1)ᵐ` at `x₀`, with preferred chart `a₀`, the image of a tangent vector `v` of `ℙᵐ⁺¹` at
`ℓ x` is its reading in the chart `a₀` of `ℙᵐ⁺¹`, multiplied by the sign of the frame `a₀`. -/
theorem trivializationAt_lineTangentEquiv (x₀ : ℙ 𝕜 (Fin 2 → 𝕜)) {x : ℙ 𝕜 (Fin 2 → 𝕜)}
    (hx : x ∈ affineOpen ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x₀))
    (v : LineTangentSpace 𝕜 m x) :
    (trivializationAt (Fin (m + 1) → 𝕜) (twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).Fiber x₀
        ⟨x, lineTangentEquiv x v⟩).2 =
      lineFrameSign ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x₀) *
        tangentCoordChange 𝓘(𝕜, Fin (m + 1) → 𝕜) (line m x)
          (lineCentre ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x₀))
          (line m x) v := by
  have ha := mem_affineOpen_twistSumCore_indexAt (𝕜 := 𝕜) (lineTwist m) x
  have h : (trivializationAt (Fin (m + 1) → 𝕜)
      (twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).Fiber x₀ ⟨x, lineTangentEquiv x v⟩).2 =
        (twistSumCore (lineTwist m)).coordChange
          ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x)
          ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x₀) x
          (lineTangentEquiv x v) :=
    (rfl)
  rw [h, lineTangentEquiv_apply]
  refine (twistSumCore_coordChange_lineFrameSign_mul ha hx _).trans ?_
  have hsrc : line m x ∈ (extChartAt 𝓘(𝕜, Fin (m + 1) → 𝕜) (line m x)).source ∩
      (extChartAt 𝓘(𝕜, Fin (m + 1) → 𝕜)
        (lineCentre ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x))).source ∩
      (extChartAt 𝓘(𝕜, Fin (m + 1) → 𝕜)
        (lineCentre ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt x₀))).source := by
    simp only [extChartAt_source]
    exact ⟨⟨mem_chart_source _ _, line_mem_chartAt_lineCentre_source ha⟩,
      line_mem_chartAt_lineCentre_source hx⟩
  -- The tangent space at `ℓ x` is the model space `Fin (m + 1) → 𝕜`, by definition.
  let v' : Fin (m + 1) → 𝕜 := v
  exact congrArg (lineFrameSign _ * ·) (tangentCoordChange_comp (v := v') hsrc)

/-- The change from the chart of `ℓ x₀` to the chart `a` of `ℙᵐ⁺¹`, read along the line, is
analytic near `x₀` when `x₀` lies in the affine open `a` of `ℙ¹`. -/
private theorem contMDiffAt_tangentCoordChange_line {x₀ : ℙ 𝕜 (Fin 2 → 𝕜)} {a : Fin 2}
    (ha : x₀ ∈ affineOpen a) :
    ContMDiffAt 𝓘(𝕜, Fin 1 → 𝕜) 𝓘(𝕜, (Fin (m + 1) → 𝕜) →L[𝕜] Fin (m + 1) → 𝕜) ω
      (fun x ↦ tangentCoordChange 𝓘(𝕜, Fin (m + 1) → 𝕜) (line m x₀) (lineCentre a) (line m x))
      x₀ := by
  have hcore : ContMDiffOn 𝓘(𝕜, Fin (m + 1) → 𝕜) 𝓘(𝕜, (Fin (m + 1) → 𝕜) →L[𝕜] Fin (m + 1) → 𝕜) ω
      (tangentCoordChange 𝓘(𝕜, Fin (m + 1) → 𝕜) (line m x₀) (lineCentre a))
      ((chartAt (Fin (m + 1) → 𝕜) (line (𝕜 := 𝕜) m x₀)).source ∩
        (chartAt (Fin (m + 1) → 𝕜) (lineCentre (𝕜 := 𝕜) (m := m) a)).source) :=
    (tangentBundleCore.isContMDiff (I := 𝓘(𝕜, Fin (m + 1) → 𝕜))
      (M := ℙ 𝕜 (Fin (m + 2) → 𝕜)) (n := ω)).contMDiffOn_coordChange _ _
  have hmem : line m x₀ ∈ (chartAt (Fin (m + 1) → 𝕜) (line (𝕜 := 𝕜) m x₀)).source ∩
      (chartAt (Fin (m + 1) → 𝕜) (lineCentre (𝕜 := 𝕜) (m := m) a)).source :=
    ⟨mem_chart_source _ _, line_mem_chartAt_lineCentre_source ha⟩
  exact (hcore.contMDiffAt (((chartAt _ _).open_source.inter
    (chartAt _ _).open_source).mem_nhds hmem)).comp x₀
    ((contMDiff_map (lineEmbedding m) (lineEmbedding_injective m) ω) x₀)

/-- **The isomorphism `ℓ* Tℙᵐ⁺¹ ≃ 𝒪(2) ⊕ 𝒪(1)ᵐ` is analytic.** The map of total spaces given by the
fibrewise isomorphisms `Projectivization.lineTangentEquiv` is analytic; for `𝕜 = ℂ` it is
holomorphic. -/
theorem contMDiff_lineTangentEquiv :
    ContMDiff (𝓘(𝕜, Fin 1 → 𝕜).prod 𝓘(𝕜, Fin (m + 1) → 𝕜))
      (𝓘(𝕜, Fin 1 → 𝕜).prod 𝓘(𝕜, Fin (m + 1) → 𝕜)) ω
      (fun q : TotalSpace (Fin (m + 1) → 𝕜) (LineTangentSpace 𝕜 m) ↦
        TotalSpace.mk' (Fin (m + 1) → 𝕜)
          (E := (twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).Fiber) q.proj
          (lineTangentEquiv q.proj q.snd)) := by
  intro q₀
  have ha₀ := mem_affineOpen_twistSumCore_indexAt (𝕜 := 𝕜) (lineTwist m) q₀.proj
  -- The tangent vector read in the chart of `ℓ x₀` is analytic on the total space.
  have hT := (Bundle.contMDiffAt_totalSpace_iff.1
    (Bundle.Pullback.contMDiff_lift (E := TangentSpace 𝓘(𝕜, Fin (m + 1) → 𝕜))
      (lineContMDiffMap (𝕜 := 𝕜) (m := m)) (lineContMDiffMap (𝕜 := 𝕜) (m := m)).contMDiff q₀)).2
  -- In the trivializations at `x₀`, the isomorphism is this reading followed by the analytic change
  -- to the chart `a₀` and the sign of the frame `a₀`.
  have hfib := (ContinuousLinearMap.mul 𝕜 (Fin (m + 1) → 𝕜)
      (lineFrameSign ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt
        q₀.proj))).contMDiff.contMDiffAt.comp q₀
      (((contMDiffAt_tangentCoordChange_line (m := m) ha₀).comp q₀
        (contMDiffAt_proj _)).clm_apply hT)
  refine Bundle.contMDiffAt_totalSpace_iff.2 ⟨contMDiffAt_proj _, ?_⟩
  have hline : Continuous (line (𝕜 := 𝕜) m) :=
    (lineContMDiffMap (𝕜 := 𝕜) (m := m)).contMDiff.continuous
  have hnhds : ∀ᶠ q : TotalSpace (Fin (m + 1) → 𝕜) (LineTangentSpace 𝕜 m) in nhds q₀,
      q.proj ∈ affineOpen ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt q₀.proj) ∩
        line m ⁻¹' (chartAt (Fin (m + 1) → 𝕜) (line (𝕜 := 𝕜) m q₀.proj)).source :=
    (FiberBundle.continuous_proj (Fin (m + 1) → 𝕜)
      (LineTangentSpace 𝕜 m)).continuousAt.preimage_mem_nhds
        (((isOpen_affineOpen _).inter ((chartAt _ _).open_source.preimage hline)).mem_nhds
          ⟨ha₀, mem_chart_source _ _⟩)
  refine hfib.congr_of_eventuallyEq (hnhds.mono fun ⟨p, v⟩ hq ↦ ?_)
  refine (trivializationAt_lineTangentEquiv q₀.proj hq.1 v).trans ?_
  have hsrc : line m p ∈ (extChartAt 𝓘(𝕜, Fin (m + 1) → 𝕜) (line m p)).source ∩
      (extChartAt 𝓘(𝕜, Fin (m + 1) → 𝕜) (line m q₀.proj)).source ∩
      (extChartAt 𝓘(𝕜, Fin (m + 1) → 𝕜) (lineCentre
        ((twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).indexAt q₀.proj))).source := by
    simp only [extChartAt_source]
    exact ⟨⟨mem_chart_source _ _, hq.2⟩, line_mem_chartAt_lineCentre_source hq.1⟩
  -- The tangent space at `ℓ p` is the model space `Fin (m + 1) → 𝕜`, by definition, and the
  -- trivialization of the tangent bundle at `ℓ x₀` reads a vector at `ℓ p` by the change from the
  -- chart of `ℓ p` to the chart of `ℓ x₀`.
  let v' : Fin (m + 1) → 𝕜 := v
  have htriv : (trivializationAt (Fin (m + 1) → 𝕜) (TangentSpace 𝓘(𝕜, Fin (m + 1) → 𝕜))
      (Pullback.lift (⇑(lineContMDiffMap (𝕜 := 𝕜) (m := m))) q₀).proj
      (Pullback.lift (⇑(lineContMDiffMap (𝕜 := 𝕜) (m := m))) ⟨p, v⟩)).2 =
        tangentCoordChange 𝓘(𝕜, Fin (m + 1) → 𝕜) (line m p) (line m q₀.proj) (line m p) v' :=
    TangentBundle.trivializationAt_snd_eq_tangentCoordChange (x := line m q₀.proj)
      (y := line m p) v'
  simp only [Function.comp_apply, ContinuousLinearMap.mul_apply']
  rw [htriv]
  exact congrArg (lineFrameSign _ * ·) (tangentCoordChange_comp (v := v') hsrc).symm

variable [CompleteSpace 𝕜]

/-- **The tangent bundle of `ℙᵐ⁺¹` along a line is `𝒪(2) ⊕ 𝒪(1)ᵐ`.** The fibrewise isomorphisms
`Projectivization.lineTangentEquiv` form a `C^n` diffeomorphism, for every `n` and hence analytic
at `n = ω`, from the total space of the pullback `ℓ* Tℙᵐ⁺¹` of the tangent bundle along the
coordinate line `ℓ` to the total space of the split bundle `𝒪(2) ⊕ 𝒪(1)ᵐ`, over the identity of
`ℙ¹`. For `𝕜 = ℂ` it is a biholomorphism of total spaces. -/
def lineTangentDiffeomorph (n : ℕ∞ω) :
    TotalSpace (Fin (m + 1) → 𝕜)
        (LineTangentSpace 𝕜 m) ≃ₘ^n⟮𝓘(𝕜, Fin 1 → 𝕜).prod 𝓘(𝕜, Fin (m + 1) → 𝕜),
        𝓘(𝕜, Fin 1 → 𝕜).prod 𝓘(𝕜, Fin (m + 1) → 𝕜)⟯
      TotalSpace (Fin (m + 1) → 𝕜) (twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).Fiber :=
  TauCeti.bundleDiffeomorph lineTangentEquiv (contMDiff_lineTangentEquiv.of_le le_top)

@[simp]
theorem lineTangentDiffeomorph_apply (n : ℕ∞ω)
    (q : TotalSpace (Fin (m + 1) → 𝕜)
      (LineTangentSpace 𝕜 m)) :
    lineTangentDiffeomorph n q = ⟨q.proj, lineTangentEquiv q.proj q.snd⟩ :=
  TauCeti.bundleDiffeomorph_apply _ _ q

@[simp]
theorem lineTangentDiffeomorph_symm_apply (n : ℕ∞ω)
    (q : TotalSpace (Fin (m + 1) → 𝕜) (twistSumCore (𝕜 := 𝕜) (n := 1) (lineTwist m)).Fiber) :
    (lineTangentDiffeomorph n).symm q = ⟨q.proj, (lineTangentEquiv q.proj).symm q.snd⟩ :=
  TauCeti.bundleDiffeomorph_symm_apply _ _ q

/-- The isomorphism `ℓ* Tℙᵐ⁺¹ ≃ 𝒪(2) ⊕ 𝒪(1)ᵐ` lies over the identity of `ℙ¹`. -/
theorem proj_lineTangentDiffeomorph (n : ℕ∞ω)
    (q : TotalSpace (Fin (m + 1) → 𝕜)
      (LineTangentSpace 𝕜 m)) :
    (lineTangentDiffeomorph n q).proj = q.proj := by
  simp

end Equiv

end Projectivization

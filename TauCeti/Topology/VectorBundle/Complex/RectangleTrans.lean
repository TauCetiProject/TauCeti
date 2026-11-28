/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Cylinder
public import TauCeti.Topology.VectorBundle.Complex.TorusClutching
import TauCeti.Topology.VectorBundle.FiberCast

/-!
# Frames over a square glued from two maps

Let `u` and `u'` be maps of the plane into a space `X` that agree on the line `s = 0`. Gluing `u`
run backwards to `u'` along this line gives the map of the unit square
`rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u'`, which is `u` run backwards for `s ≤ 1/2`
and `u'` for `s ≥ 1/2`: the sphere glued from two caps of a loop, or the torus glued from two
cylinders from a loop to a reference loop.

Let `E` be a complex vector bundle over `X`, and let `φ` and `φ'` be continuous frames of `E` along
`u` and `u'` which differ along the line `s = 0` by automorphisms `k t` of the model fibre,
`φ (0, t) = φ' (0, t) ∘ k t`. Then `φ` on the half `s ≤ 1/2` and `φ' ∘ k` on the half `s ≥ 1/2`
form a continuous frame along the glued square (`TauCeti.exists_frame_rectangleTrans`).

When `u` and `u'` are cylinders, with frames periodic on their loops and equal along the edge
`s = 1`, the glued square is a map of the torus and this frame takes the same values on its top and
bottom edges and differs across its vertical edges by `k`. So the torus clutching number of the
glued torus is minus the winding of `det k`
(`TauCeti.torusClutchingNumber_mul_two_pi_eq_of_rectangleTrans`), which computes the first Chern
number of the torus glued from two cylinders from frames over the cylinders.

## Main results

* `TauCeti.exists_frame_rectangleTrans`: the frame along the square glued from two maps.
* `TauCeti.torusClutchingNumber_mul_two_pi_eq_of_rectangleTrans`: the clutching number of the torus
  glued from two cylinders is minus the winding of the change of frame along their common loop.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Appendix C.1 (the first Chern number of a bundle over a closed surface by clutching).
-/

public section

noncomputable section

open Bundle Set

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℂ F E]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)]

omit [TopologicalSpace X] [FiniteDimensional ℂ F] [FiberBundle F E] [VectorBundle ℂ F E]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)] in
/-- **The frame of a square glued from two maps.** Let `u` and `u'` be maps of the plane that
agree on the line `s = 0`, and `p` the map of the unit square
`rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u'`, `u` run backwards followed by `u'`, such as
the sphere glued from two caps or the torus glued from two cylinders. For continuous frames `φ` and
`φ'` along `u` and `u'` with `φ (0, t) = φ' (0, t) ∘ k t`, there is a continuous frame along `p`
that is `φ` on the half `s ≤ 1/2` and `φ' ∘ k` on the half `s ≥ 1/2`. -/
theorem exists_frame_rectangleTrans {u u' : ℝ × ℝ → X}
    (hseam : ∀ t, u (0, t) = u' (0, t)) {p : (Fin 2 → unitInterval) → X}
    (hp : ∀ y, p y = rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u' ((y 0 : ℝ), (y 1 : ℝ)))
    {φ : ∀ z, F ≃L[ℂ] E (u z)} {φ' : ∀ z, F ≃L[ℂ] E (u' z)}
    (hφ : Continuous fun q : (ℝ × ℝ) × F ↦ TotalSpace.mk' F (u q.1) (φ q.1 q.2))
    (hφ' : Continuous fun q : (ℝ × ℝ) × F ↦ TotalSpace.mk' F (u' q.1) (φ' q.1 q.2))
    {k : unitInterval → F ≃L[ℂ] F} (hk : Continuous fun t ↦ (k t : F →L[ℂ] F))
    (hφk : ∀ (t : unitInterval) v, TotalSpace.mk' F (u (0, t)) (φ (0, t) v) =
      TotalSpace.mk' F (u' (0, t)) (φ' (0, t) (k t v))) :
    ∃ ψ : ∀ y, F ≃L[ℂ] E (p y),
      (Continuous fun q : (Fin 2 → unitInterval) × F ↦ TotalSpace.mk' F (p q.1) (ψ q.1 q.2)) ∧
      ∀ y v, TotalSpace.mk' F (p y) (ψ y v) =
        if (y 0 : ℝ) ≤ 1 / 2 then
          TotalSpace.mk' F (u (1 - Real.smoothTransition (3 * y 0), y 1))
            (φ (1 - Real.smoothTransition (3 * y 0), y 1) v)
        else TotalSpace.mk' F (u' (Real.smoothTransition (3 * y 0 - 2), y 1))
          (φ' (Real.smoothTransition (3 * y 0 - 2), y 1) (k (y 1) v)) := by
  set β := Real.smoothTransition
  -- The points of the two caps that the halves `s ≤ 1/2` and `s ≥ 1/2` of the square run through.
  let a : (Fin 2 → unitInterval) → ℝ × ℝ := fun y ↦ (1 - β (3 * (y 0 : ℝ)), (y 1 : ℝ))
  let b : (Fin 2 → unitInterval) → ℝ × ℝ := fun y ↦ (β (3 * (y 0 : ℝ) - 2), (y 1 : ℝ))
  have hseam' : ∀ t, (u ∘ Prod.map (fun s ↦ 1 - s) id) (1, t) = u' (0, t) := fun t ↦ by
    simpa using hseam t
  -- On each half the sphere is the reparametrized cap, by definition of `a` and `b`.
  have hpa (y : Fin 2 → unitInterval) (hy : (y 0 : ℝ) ≤ 1 / 2) : u (a y) = p y := by
    rw [hp, rectangleTrans_eq_left hseam' (by simp only; linarith)]
    rfl
  have hpb (y : Fin 2 → unitInterval) (hy : ¬(y 0 : ℝ) ≤ 1 / 2) : u' (b y) = p y := by
    rw [hp, rectangleTrans_eq_right hseam' (by simp only; linarith)]
    rfl
  let ψ : ∀ y, F ≃L[ℂ] E (p y) := fun y ↦
    if hy : (y 0 : ℝ) ≤ 1 / 2 then (φ (a y)).trans (fiberCast (hpa y hy))
    else ((k (y 1)).trans (φ' (b y))).trans (fiberCast (hpb y hy))
  have hψ (y : Fin 2 → unitInterval) (v : F) : TotalSpace.mk' F (p y) (ψ y v) =
      if (y 0 : ℝ) ≤ 1 / 2 then TotalSpace.mk' F (u (a y)) (φ (a y) v)
      else TotalSpace.mk' F (u' (b y)) (φ' (b y) (k (y 1) v)) := by
    by_cases hy : (y 0 : ℝ) ≤ 1 / 2
    · simp only [ψ, dite_eq_left hy, ite_eq_left hy, ContinuousLinearEquiv.trans_apply,
        mk_fiberCast]
    · simp only [ψ, dite_eq_right hy, ite_eq_right hy, ContinuousLinearEquiv.trans_apply,
        mk_fiberCast]
  refine ⟨ψ, ?_, hψ⟩
  rw [show (fun q : (Fin 2 → unitInterval) × F ↦ TotalSpace.mk' F (p q.1) (ψ q.1 q.2)) = _ from
    funext fun q ↦ hψ q.1 q.2]
  refine Continuous.if_le (hφ.comp (((by fun_prop : Continuous a).comp continuous_fst).prodMk
      continuous_snd))
    (hφ'.comp (((by fun_prop : Continuous b).comp continuous_fst).prodMk
      ((hk.comp ((continuous_apply 1).comp continuous_fst)).clm_apply continuous_snd)))
    (by fun_prop) continuous_const fun q hq ↦ ?_
  -- At `s = 1/2` both halves are at the edge `s = 0` of the caps, where `φ = φ' ∘ k`. The two
  -- branches are compositions with `q`, which `change` evaluates so that `a q.1` can be rewritten.
  have ha : a q.1 = (0, (q.1 1 : ℝ)) := by
    simp only [a, hq]
    norm_num [β, Real.smoothTransition.one_of_one_le]
  have hb : b q.1 = (0, (q.1 1 : ℝ)) := by
    simp only [b, hq]
    norm_num [β, Real.smoothTransition.zero_of_nonpos]
  change TotalSpace.mk' F (u (a q.1)) (φ (a q.1) q.2) =
    TotalSpace.mk' F (u' (b q.1)) (φ' (b q.1) (k (q.1 1) q.2))
  rw [ha, hb]
  exact hφk (q.1 1) q.2

/-- **The clutching number of the torus glued from two cylinders.** Let `u` and `u'` be maps of the
plane that agree on the line `s = 0`, and let `w` be the map of the unit square
`rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u'`, `u` run backwards followed by `u'`. Let `φ`
and `φ'` be continuous frames of `E` along `u` and `u'` that are periodic on the loops of the
cylinders, `φ (s, 1) = φ (s, 0)` for `s ∈ [0, 1]`, and agree along the edge `s = 1`,
`φ (1, t) = φ' (1, t)` for `t ∈ [0, 1]`; then `w` is a map of the torus. Let `k` be a family of
automorphisms of `F` with `φ (0, t) = φ' (0, t) ∘ k t` along the edge `s = 0`. Then for every
continuous lift `θ` of the normalized determinant of `k` through `Circle.exp`, `2π` times the
torus clutching number of `w` is `θ 0 - θ 1`. -/
theorem torusClutchingNumber_mul_two_pi_eq_of_rectangleTrans {u u' : ℝ × ℝ → X}
    (hseam : ∀ t, u (0, t) = u' (0, t)) {w : C(Fin 2 → unitInterval, X)}
    (hw : ∀ y, w y = rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u' ((y 0 : ℝ), (y 1 : ℝ)))
    {φ : ∀ z, F ≃L[ℂ] E (u z)} {φ' : ∀ z, F ≃L[ℂ] E (u' z)}
    (hφ : Continuous fun q : (ℝ × ℝ) × F ↦ TotalSpace.mk' F (u q.1) (φ q.1 q.2))
    (hφ' : Continuous fun q : (ℝ × ℝ) × F ↦ TotalSpace.mk' F (u' q.1) (φ' q.1 q.2))
    (hper : ∀ s ∈ Icc (0 : ℝ) 1, ∀ v,
      TotalSpace.mk' F (u (s, 1)) (φ (s, 1) v) = TotalSpace.mk' F (u (s, 0)) (φ (s, 0) v))
    (hper' : ∀ s ∈ Icc (0 : ℝ) 1, ∀ v,
      TotalSpace.mk' F (u' (s, 1)) (φ' (s, 1) v) = TotalSpace.mk' F (u' (s, 0)) (φ' (s, 0) v))
    (hend : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v,
      TotalSpace.mk' F (u (1, t)) (φ (1, t) v) = TotalSpace.mk' F (u' (1, t)) (φ' (1, t) v))
    {k : unitInterval → F ≃L[ℂ] F}
    (hφk : ∀ (t : unitInterval) v, TotalSpace.mk' F (u (0, t)) (φ (0, t) v) =
      TotalSpace.mk' F (u' (0, t)) (φ' (0, t) (k t v)))
    {θ : unitInterval → ℝ} (hθ : Continuous θ)
    (hθk : ∀ t, Circle.exp (θ t) = (k t).normalizedDet) :
    (torusClutchingNumber F E w : ℝ) * (2 * Real.pi) = θ 0 - θ 1 := by
  -- `k` is the change of frame along the common edge `s = 0`, so it is continuous.
  have hγ : Continuous fun q : unitInterval × F ↦ (((0 : ℝ), (q.1 : ℝ)), q.2) := by fun_prop
  have hk := continuous_transition_of_totalSpaceMk'_eq (f := fun t : unitInterval ↦ u (0, t))
    (g := fun t : unitInterval ↦ u' (0, t)) (φ := fun t ↦ φ (0, t)) (ψ := fun t ↦ φ' (0, t))
    (hφ.comp hγ) (hφ'.comp hγ) hφk
  -- The frame `Ψ` over the square of `w`: `φ` on the left half and `φ' ∘ k` on the right half.
  obtain ⟨Ψ, hΨc, hΨ⟩ := exists_frame_rectangleTrans (p := w) hseam hw hφ hφ' hk hφk
  -- Points of the total space read in `φ` or `φ'` only depend on the point of the plane.
  have hmk {z z' : ℝ × ℝ} (hz : z = z') (v : F) :
      TotalSpace.mk' F (u z) (φ z v) = TotalSpace.mk' F (u z') (φ z' v) := by
    subst hz
    rfl
  have hmk' {z z' : ℝ × ℝ} (hz : z = z') (v : F) :
      TotalSpace.mk' F (u' z) (φ' z v) = TotalSpace.mk' F (u' z') (φ' z' v) := by
    subst hz
    rfl
  -- Along the edges `s = 0` and `s = 1` of the square, `Ψ` reads `φ (1, ·)` and `φ (1, ·) ∘ k`.
  refine torusClutchingNumber_mul_two_pi_eq_of_frame hΨc (k := k) (fun t v ↦ ?_) (fun s v ↦ ?_) hθ
    hθk
  · rw [hΨ, hΨ, ite_eq_right (by norm_num), ite_eq_left (by simp)]
    refine ((hmk' (Prod.ext (by norm_num [Real.smoothTransition.one_of_one_le]) (by simp))
      _).trans (hend t t.property _).symm).trans (hmk (Prod.ext ?_ (by simp)) _)
    simp [Real.smoothTransition.zero_of_nonpos]
  -- `Ψ` takes the same values on the top and bottom edges: the frames are periodic, and so is `k`,
  -- since both frames are periodic along the common loop `u (0, ·)`.
  · have hk₀₁ : k 1 = k 0 := by
      have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
      ext v
      have e₁ := hφk 1 v
      have e₀ := hφk 0 v
      rw [Icc.coe_one] at e₁
      rw [Icc.coe_zero] at e₀
      exact (φ' (0, 0)).injective (TotalSpace.mk_inj.1
        ((((hper' 0 h0 (k 1 v)).symm.trans e₁.symm).trans (hper 0 h0 v)).trans e₀))
    rw [hΨ, hΨ]
    by_cases hs : (s : ℝ) ≤ 1 / 2
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hs, ↓reduceIte, Icc.coe_one,
        Icc.coe_zero]
      exact hper (1 - Real.smoothTransition (3 * (s : ℝ)))
        ⟨by linarith [Real.smoothTransition.le_one (3 * (s : ℝ))],
          by linarith [Real.smoothTransition.nonneg (3 * (s : ℝ))]⟩ v
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hs, ↓reduceIte, Icc.coe_one,
        Icc.coe_zero, hk₀₁]
      exact hper' (Real.smoothTransition (3 * (s : ℝ) - 2))
        ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ _


end TauCeti

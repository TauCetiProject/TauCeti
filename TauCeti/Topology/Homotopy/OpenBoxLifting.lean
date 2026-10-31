/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.GlueHalves
public import TauCeti.Topology.Homotopy.HurewiczFibration.RelativeLifting
public import TauCeti.Topology.Homotopy.Cube.OpenBox

/-!
# Relative homotopy lifting for the open box

A Hurewicz fibration `p : E → B` lifts homotopies relative to the open box: given a homotopy
`H : A × I × I → B` and a lift `g` of `H` on the open box `J = I × {0} ∪ ∂I × I` (the bottom and
the two sides of the square, in coordinates `(u, t)`), there is a lift of `H` on the whole square
that agrees with `g` on `J` (`TauCeti.IsHurewiczFibration.exists_lift_openBox`).  The data on `J`
is passed as a map on the whole square, of which only the values on `J` are used.

This is the form in which families of paths with prescribed end points are lifted: a homotopy of
paths whose end points stay fixed in `B` lifts to a homotopy of paths whose end points follow
prescribed lifts, for instance the constant lifts at a base point for loops
(`TauCeti.IsHurewiczFibration.loopMap`).  No cofibration theory is needed.

## Main results

* `TauCeti.IsHurewiczFibration.exists_lift_openBox`: relative homotopy lifting for the pair
  `(A × I × I, A × J)`.
* `TauCeti.IsHurewiczFibration.exists_homotopy_lifts`: two lifts of the same family of paths from
  the same starting points are homotopic through lifts, relative to the starting points.
* `TauCeti.IsHurewiczFibration.exists_homotopy_endpoints`: two lifts of the same family of paths
  from the same starting points have homotopic end points, fiberwise over the end points of the
  paths.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter I.7.
* A. Strøm, *Note on cofibrations II*, Math. Scand. 22 (1968), 130–142.
-/

public section

open unitInterval Set

universe w u v

namespace TauCeti

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}
  {A : Type w} [TopologicalSpace A]

/-- **Relative homotopy lifting for the open box.** For a Hurewicz fibration `p`, a homotopy
`H : A × I × I → B` with a lift `g` on the open box `I × {0} ∪ ∂I × I` (coordinates `(u, t)`)
lifts to the whole square, agreeing with `g` on the open box.  Only the values of `g` on the
open box matter. -/
theorem IsHurewiczFibration.exists_lift_openBox (hp : IsHurewiczFibration.{w} p)
    (g : C(A × (I × I), E)) (H : C(A × (I × I), B))
    (hg : ∀ a (x : I × I), x.2 = 0 ∨ x.1 = 0 ∨ x.1 = 1 → p (g (a, x)) = H (a, x)) :
    ∃ G : C(A × (I × I), E), p ∘ G = H ∧
      ∀ a (x : I × I), x.2 = 0 ∨ x.1 = 0 ∨ x.1 = 1 → G (a, x) = g (a, x) := by
  -- Identify the square, in coordinates `(u, t)`, with the one-coordinate cube cylinder.
  let e : I × I → I × (Unit → I) := fun x ↦ (x.2, fun _ ↦ x.1)
  let d : I × (Unit → I) → I × I := fun x ↦ (x.2 (), x.1)
  have he : Continuous e := by unfold e; fun_prop
  have hd : Continuous d := by unfold d; fun_prop
  have hbox (x : I × (Unit → I)) :
      x ∈ cylinderExtensionDomain (Cube.boundary Unit) ↔
        (d x).2 = 0 ∨ (d x).1 = 0 ∨ (d x).1 = 1 := by
    simp [mem_cylinderExtensionDomain_iff, Cube.boundary, d, Unique.exists_iff]
  let deform (s : I) (x : I × I) := d (cubeLiftDeform s (e x))
  have continuous_deform : Continuous fun y : I × (I × I) ↦ deform y.1 y.2 :=
    hd.comp (continuous_cubeLiftDeform.comp
      (continuous_fst.prodMk (he.comp continuous_snd)))
  have deform_zero_isBox (x : I × I) :
      (deform 0 x).2 = 0 ∨ (deform 0 x).1 = 0 ∨ (deform 0 x).1 = 1 :=
    (hbox _).1 (cubeLiftDeform_zero_mem (e x))
  let τ : C(I × I, I) :=
    ⟨fun x ↦ ⟨cubeLiftTime (e x), cubeLiftTime_mem (e x)⟩,
      (continuous_cubeLiftTime.comp he).subtype_mk _⟩
  let J : Set (A × (I × I)) := {y | y.2.2 = 0 ∨ y.2.1 = 0 ∨ y.2.1 = 1}
  let r : C(A × (I × I), J) :=
    ⟨fun y ↦ ⟨(y.1, deform 0 y.2), deform_zero_isBox y.2⟩,
      (continuous_fst.prodMk (continuous_deform.comp
        (continuous_const.prodMk continuous_snd))).subtype_mk _⟩
  -- Apply fixed-data relative lifting to the product of the radial retraction with `A`.
  obtain ⟨G, hG, hGJ⟩ := (hp.hasHomotopyLiftingProperty _).zeroSetSDR_liftingInclusion
    (τ.comp ContinuousMap.snd)
    (fun y ↦ (Subtype.ext_iff.trans (cubeLiftTime_eq_zero_iff (e y.2))).trans (hbox (e y.2)))
    r ⟨{
      toFun := fun y ↦ (y.2.1, deform (σ y.1) y.2.2)
      continuous_toFun := (continuous_fst.comp continuous_snd).prodMk
        (continuous_deform.comp ((continuous_symm.comp continuous_fst).prodMk
          (continuous_snd.comp continuous_snd)))
      map_zero_left := fun y ↦ by simp [deform, e, d]
      map_one_left := fun _ ↦ by simp [r]
      prop' := fun s y hy ↦ by
        simp [deform, cubeLiftDeform_of_mem (σ s) ((hbox (e y.2)).2 hy), e, d] }⟩
    (g.restrict J) H (fun y ↦ hg y.1.1 y.1.2 y.2)
  exact ⟨G, hG, fun a x hx ↦ hGJ ⟨(a, x), hx⟩⟩

section Endpoints

/-- The reparametrization `(u, t) ↦ t (1 - 2 u)`, clipped to `I`: on the left half of the square
it runs from the full path at `u = 0` to the constant path at `u = 1/2`. -/
private noncomputable def leftTime : C(I × I, I) :=
  ⟨fun x ↦ projIcc 0 1 zero_le_one ((x.2 : ℝ) * (1 - 2 * x.1)),
    continuous_projIcc.comp (by fun_prop)⟩

/-- The reparametrization `(u, t) ↦ t (2 u - 1)`, clipped to `I`: on the right half of the square
it runs from the constant path at `u = 1/2` to the full path at `u = 1`. -/
private noncomputable def rightTime : C(I × I, I) :=
  ⟨fun x ↦ projIcc 0 1 zero_le_one ((x.2 : ℝ) * (2 * x.1 - 1)),
    continuous_projIcc.comp (by fun_prop)⟩

private theorem leftTime_apply (x : I × I) :
    leftTime x = projIcc 0 1 zero_le_one ((x.2 : ℝ) * (1 - 2 * x.1)) :=
  (rfl) -- the definition of `leftTime`

private theorem rightTime_apply (x : I × I) :
    rightTime x = projIcc 0 1 zero_le_one ((x.2 : ℝ) * (2 * x.1 - 1)) :=
  (rfl) -- the definition of `rightTime`

private theorem leftTime_zero_left (t : I) : leftTime (0, t) = t := by simp [leftTime_apply]

private theorem leftTime_zero_right (u : I) : leftTime (u, 0) = 0 := by simp [leftTime_apply]

private theorem leftTime_half (x : I × I) (hx : (x.1 : ℝ) = 2⁻¹) : leftTime x = 0 := by
  simp [leftTime_apply, hx]

private theorem rightTime_one_left (t : I) : rightTime (1, t) = t := by
  simp [rightTime_apply]; norm_num

private theorem rightTime_zero_right (u : I) : rightTime (u, 0) = 0 := by simp [rightTime_apply]

private theorem rightTime_half (x : I × I) (hx : (x.1 : ℝ) = 2⁻¹) : rightTime x = 0 := by
  simp [rightTime_apply, hx]

variable {Y : Type*} [TopologicalSpace Y]

/-- The lift on the open box of two families of paths with the same starting points: `α` on the
side `u = 0`, `α'` on the side `u = 1`, and the common starting point on the bottom. -/
private noncomputable def openBoxDatum (α α' : C(Y × I, E)) (h₀ : ∀ y, α (y, 0) = α' (y, 0)) :
    C(Y × (I × I), E) :=
  ContinuousMap.glueHalves (ContinuousMap.fst.comp ContinuousMap.snd)
    (α.comp ⟨fun x ↦ (x.1, leftTime x.2), by fun_prop⟩)
    (α'.comp ⟨fun x ↦ (x.1, rightTime x.2), by fun_prop⟩)
    (fun x hx ↦ by
      simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
      rw [leftTime_half x.2 hx, rightTime_half x.2 hx]
      exact h₀ x.1)

variable (α α' : C(Y × I, E)) (h₀ : ∀ y, α (y, 0) = α' (y, 0))

private theorem openBoxDatum_of_le {y : Y} {x : I × I} (hx : (x.1 : ℝ) ≤ 2⁻¹) :
    openBoxDatum α α' h₀ (y, x) = α (y, leftTime x) :=
  ContinuousMap.glueHalves_of_le _ _ _ _ hx

private theorem openBoxDatum_of_not_le {y : Y} {x : I × I} (hx : ¬ (x.1 : ℝ) ≤ 2⁻¹) :
    openBoxDatum α α' h₀ (y, x) = α' (y, rightTime x) :=
  ContinuousMap.glueHalves_of_not_le _ _ _ _ hx

private theorem openBoxDatum_left (y : Y) (t : I) :
    openBoxDatum α α' h₀ (y, (0, t)) = α (y, t) := by
  rw [openBoxDatum_of_le α α' h₀ (by simp), leftTime_zero_left]

private theorem openBoxDatum_right (y : Y) (t : I) :
    openBoxDatum α α' h₀ (y, (1, t)) = α' (y, t) := by
  rw [openBoxDatum_of_not_le α α' h₀ (by norm_num), rightTime_one_left]

private theorem openBoxDatum_bottom (y : Y) (u : I) :
    openBoxDatum α α' h₀ (y, (u, 0)) = α (y, 0) := by
  by_cases hu : (u : ℝ) ≤ 2⁻¹
  · rw [openBoxDatum_of_le α α' h₀ hu, leftTime_zero_right]
  · rw [openBoxDatum_of_not_le α α' h₀ hu, rightTime_zero_right, h₀]

end Endpoints

/-- **Lifts of the same family of paths are vertically homotopic.**  Let `α` and `α'` be two
families of paths in `E`, parametrized by a space `Y`, with the same starting points and lying over
the same family `γ` of paths in `B`.  Then they are homotopic through lifts of `γ`, relative to
their starting points: there is a family of squares `G`, in coordinates `(u, t)`, equal to `α` on
the side `u = 0`, to `α'` on the side `u = 1` and to the common starting point on the bottom
`t = 0`, with `p (G (y, (u, t))) = γ (y, t)` throughout. -/
theorem IsHurewiczFibration.exists_homotopy_lifts {Y : Type w} [TopologicalSpace Y]
    (hp : IsHurewiczFibration.{w} p) (γ : C(Y × I, B)) (α α' : C(Y × I, E))
    (hα : ∀ y t, p (α (y, t)) = γ (y, t))
    (hα' : ∀ y t, p (α' (y, t)) = γ (y, t)) (h₀ : ∀ y, α (y, 0) = α' (y, 0)) :
    ∃ G : C(Y × (I × I), E), (∀ y t, G (y, (0, t)) = α (y, t)) ∧
      (∀ y t, G (y, (1, t)) = α' (y, t)) ∧ (∀ y u, G (y, (u, 0)) = α (y, 0)) ∧
      ∀ y u t, p (G (y, (u, t))) = γ (y, t) := by
  let H : C(Y × (I × I), B) := ⟨fun x ↦ γ (x.1, x.2.2), by fun_prop⟩
  have H_apply : ∀ x, H x = γ (x.1, x.2.2) := fun _ ↦ (rfl) -- the definition of `H`
  -- Lift the square over `γ (y, t)` from the data on the open box.
  obtain ⟨G, hG, hGJ⟩ := hp.exists_lift_openBox (openBoxDatum α α' h₀) H (by
    rintro y ⟨u, t⟩ (h | h | h)
    · obtain rfl : t = 0 := h
      rw [openBoxDatum_bottom, hα, H_apply]
    · obtain rfl : u = 0 := h
      rw [openBoxDatum_left, hα, H_apply]
    · obtain rfl : u = 1 := h
      rw [openBoxDatum_right, hα', H_apply])
  refine ⟨G, fun y t ↦ ?_, fun y t ↦ ?_, fun y u ↦ ?_, fun y u t ↦ ?_⟩
  · rw [hGJ y (0, t) (Or.inr (Or.inl rfl)), openBoxDatum_left]
  · rw [hGJ y (1, t) (Or.inr (Or.inr rfl)), openBoxDatum_right]
  · rw [hGJ y (u, 0) (Or.inl rfl), openBoxDatum_bottom]
  · rw [← H_apply (y, (u, t))]
    exact congr_fun hG (y, (u, t))

/-- **Uniqueness of lifts up to homotopy.**  Let `α` and `α'` be two families of paths in `E`,
parametrized by a space `Y`, with the same starting points and lying over the same family `γ` of
paths in `B`.  Then their end points are homotopic: there is a homotopy `K` from `α (·, 1)` to
`α' (·, 1)` such that, for each `y`, it stays in the fiber over `γ (y, 1)`, the end point of the
path `γ (y, ·)`. -/
theorem IsHurewiczFibration.exists_homotopy_endpoints {Y : Type w} [TopologicalSpace Y]
    (hp : IsHurewiczFibration.{w} p) (γ : C(Y × I, B)) (α α' : C(Y × I, E))
    (hα : ∀ y t, p (α (y, t)) = γ (y, t))
    (hα' : ∀ y t, p (α' (y, t)) = γ (y, t)) (h₀ : ∀ y, α (y, 0) = α' (y, 0)) :
    ∃ K : C(Y × I, E), (∀ y, K (y, 0) = α (y, 1)) ∧ (∀ y, K (y, 1) = α' (y, 1)) ∧
      ∀ y s, p (K (y, s)) = γ (y, 1) := by
  obtain ⟨G, hG₀, hG₁, -, hG⟩ := hp.exists_homotopy_lifts γ α α' hα hα' h₀
  -- The homotopy is the lift on the top edge `t = 1`.
  exact ⟨⟨fun z ↦ G (z.1, (z.2, 1)), by fun_prop⟩, fun y ↦ hG₀ y 1, fun y ↦ hG₁ y 1,
    fun y s ↦ hG y s 1⟩

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Area
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chern

/-!
# The first Chern number of the sphere bounded by two caps

Let `γ` be a loop in a space `X` based at `x`, and let `u` and `u'` be two caps of `γ`: maps of the
unit square that run along `γ` on the edge `s = 0` and stay at `x` on the other three edges
(`s = 1`, the centre of the disc, and `t = 0`, `t = 1`, its seam). Gluing `u` run backwards to
`u'` along `γ` gives a sphere, whose square is
`rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u'`: `u` run backwards for `s ≤ 1/2` and `u'`
for `s ≥ 1/2`. For smooth based caps of a loop in a manifold this sphere represents the class
`D' -ᵥ D ∈ π₂(M, x)` by which the raw caps of `u'` and `u` differ
(`TauCeti.Floer.IsSmoothBasedCap.homotopyClass_vsub_homotopyClass_toMul`).

This file computes the first Chern number of that sphere from frames over the two caps. Let `E` be
a complex vector bundle over `X`, and let `φ` and `φ'` be continuous frames of `E` along `u` and
`u'` that are constant on the three edges at `x`, so that they are frames over the two discs.
Along `γ` they differ by a loop `k` of automorphisms of the model fibre,
`φ (0, t) = φ' (0, t) ∘ k t`. Then the clutching number of the sphere is minus the winding number
of `det k` (`TauCeti.Floer.clutchingNumber_mul_two_pi_eq_of_rectangleTrans`): for every continuous
lift `θ` of `t ↦ det (k t) / |det (k t)|` through `Circle.exp`,

`2π c₁(E)[u' ∪ -u] = θ 0 - θ 1`.

The proof computes the clutching number with the frame of the sphere that is `φ` on the half
`s ≤ 1/2` and `φ' ∘ k` on the half `s ≥ 1/2`, continuous because the two agree along `γ`. Read in
a trivialization near `x`, its clutching function is constant on the bottom, top and left edges of
the square, where the frame is `φ` or `φ'` at `x`, and it is a constant times `det (k t)⁻¹` along
the right edge, where the frame is `φ' ∘ k t` at the centre of `u'`.

For the tangent bundle `(TM, J)` of a manifold with a fiberwise nondegenerate two-form `σ` and an
almost complex structure `J` tamed by `σ`, this computes the first Chern number of the sphere by
which two smooth based caps of a loop differ
(`TauCeti.Floer.IsSmoothBasedCap.firstChernHom_homotopyClass_vsub_homotopyClass_mul_two_pi_eq`).
Real frames `χ`, `χ'` of `TM` along the caps that are complex linear for `J`
(`χ z (i v) = J (χ z v)`) and constant on the three edges at the base point differ along `γ` by a
loop `k` of complex-linear automorphisms of the model `G`, and `2π c₁(D' -ᵥ D) = θ 0 - θ 1` for
every continuous lift `θ` of `det_ℂ k / |det_ℂ k|`. Such frames exist along every smooth based cap
(`TauCeti.Floer.IsSmoothBasedCap.exists_frame_eq_on_edges`): any frame along the cap becomes
constant on the three edges after composing it with the change of frame read through a retraction
of the plane onto these edges.

This is the topological half of the recapping law for the grading of capped orbits. The
Conley–Zehnder index of a capped orbit, read in a symplectic trivialization over the cap, changes
by twice the Maslov index of the change of trivialization
(`TauCeti.SmoothTwoForm.frameConleyZehnderIndex_eq_add_maslovIndex`), and for frames as above that
change of trivialization along the orbit is the loop `k⁻¹`. The comparison of the Maslov index of
a loop of unitary maps with the winding of its complex determinant, which turns the statement here
into the recapping law, is not made in this file.

## Main results

* `TauCeti.Floer.clutchingNumber_mul_two_pi_eq_of_rectangleTrans`: the clutching number of the
  sphere glued from two caps is minus the winding of the change of frame along their common loop.
* `TauCeti.Floer.IsSmoothBasedCap.firstChernHom_homotopyClass_vsub_homotopyClass_mul_two_pi_eq`:
  the first Chern number of the sphere by which two smooth based caps differ, from complex frames
  over the caps.
* `TauCeti.Floer.IsSmoothBasedCap.exists_frame_eq_on_edges`: complex frames of the tangent bundle
  along a smooth based cap, constant on the three edges at the base point, exist.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Appendix C.1 (the first Chern number of a bundle over a surface by clutching) and Section 12.1
  (the grading of capped periodic orbits and its change under recapping).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999, Lecture 2 (trivializations over caps and the recapping law).
-/

public section

noncomputable section

open Bundle Set Module
open scoped Topology.Homotopy Manifold ContDiff

namespace TauCeti.Floer

/-! ### The clutching number of a sphere glued from two caps -/

section Clutching

variable {X : Type*} [TopologicalSpace X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℂ F E]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)]

/-- The identification of the fibres of `E` over two equal points. -/
private def fiberCast {a b : X} (h : a = b) : E a ≃L[ℂ] E b :=
  h ▸ ContinuousLinearEquiv.refl ℂ (E a)

omit [TopologicalSpace X] [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℂ F E]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)] in
private theorem mk_fiberCast {a b : X} (h : a = b) (w : E a) :
    TotalSpace.mk' F b (fiberCast h w) = TotalSpace.mk' F a w := by
  subst h
  rfl

omit [FiniteDimensional ℂ F] [VectorBundle ℂ F E] [∀ x, IsTopologicalAddGroup (E x)]
  [∀ x, ContinuousSMul ℂ (E x)] in
/-- Two frames that agree as families of points of the total space have the same clutching
function. -/
private theorem clutchingFunction_eq_of_mk_eq {B B' : Type*} {f : B → X} {g : B' → X}
    {φ : ∀ y, F ≃L[ℂ] E (f y)} {ψ : ∀ y, F ≃L[ℂ] E (g y)} (e : Trivialization F (π F E))
    [e.IsLinear ℂ] {y : B} {z : B'}
    (h : ∀ v, TotalSpace.mk' F (f y) (φ y v) = TotalSpace.mk' F (g z) (ψ z v)) :
    clutchingFunction f φ e y = clutchingFunction g ψ e z := by
  have hfg : f y = g z := congrArg TotalSpace.proj (h 0)
  -- The trivialization at a point reads the second coordinate of `e` on the total space.
  have key (b : X) (hb : b ∈ e.baseSet) (w : E b) :
      e.continuousLinearEquivAt ℂ b hb w = (e (TotalSpace.mk' F b w)).2 := by
    rw [e.apply_eq_prod_continuousLinearEquivAt ℂ b hb w]
  by_cases hy : f y ∈ e.baseSet
  · have hz : g z ∈ e.baseSet := hfg ▸ hy
    rw [clutchingFunction_of_mem hy, clutchingFunction_of_mem hz]
    refine congrArg (fun A : F ≃L[ℂ] F ↦ A.normalizedDet⁻¹) (ContinuousLinearEquiv.ext ?_)
    funext v
    rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply, key, key, h v]
  · rw [clutchingFunction_of_notMem hy, clutchingFunction_of_notMem (hfg ▸ hy)]

/-- The degree around the boundary of the square of a circle-valued map that is constant, equal
to `c`, on the bottom, top and left edges and equal to `c' * (g t)⁻¹` on the right edge, is minus
the winding of `g`: `2π` times it is `θ 0 - θ 1` for every continuous lift `θ` of `g`. -/
private theorem squareBoundaryDegree_mul_two_pi_eq_of_edges {Γ : (Fin 2 → unitInterval) → Circle}
    (hΓ : ContinuousOn Γ (Cube.boundary (Fin 2))) {c c' : Circle} {g : unitInterval → Circle}
    (hB : ∀ s, Γ ![s, 0] = c) (hT : ∀ s, Γ ![s, 1] = c) (hL : ∀ t, Γ ![0, t] = c)
    (hR : ∀ t, Γ ![1, t] = c' * (g t)⁻¹) {θ : unitInterval → ℝ} (hθ : Continuous θ)
    (hθg : ∀ t, Circle.exp (θ t) = g t) :
    (squareBoundaryDegree Γ : ℝ) * (2 * Real.pi) = θ 0 - θ 1 := by
  obtain ⟨θc, hθc⟩ := Circle.exp_surjective c
  obtain ⟨θc', hθc'⟩ := Circle.exp_surjective c'
  -- Lifts along the edges: constant on three of them, `θc' - θ` on the right edge.
  rw [squareBoundaryDegree_mul_two_pi_eq hΓ continuous_const (continuous_const.sub hθ)
    continuous_const continuous_const (θB := fun _ ↦ θc) (θR := fun t ↦ θc' - θ t)
    (θT := fun _ ↦ θc) (θL := fun _ ↦ θc) (fun s ↦ by rw [hB, hθc])
    (fun t ↦ by rw [hR, Circle.exp_sub, hθc', hθg, div_eq_mul_inv]) (fun s ↦ by rw [hT, hθc])
    (fun t ↦ by rw [hL, hθc])]
  ring

omit [FiniteDimensional ℂ F] [FiberBundle F E] [VectorBundle ℂ F E]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)] in
/-- **The frame of a sphere glued from two caps.** For continuous frames `φ` and `φ'` along `u` and
`u'` with `φ (0, t) = φ' (0, t) ∘ k t`, there is a continuous frame along the sphere
`rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u'` that is `φ` on the half `s ≤ 1/2` and
`φ' ∘ k` on the half `s ≥ 1/2`. -/
private theorem exists_frame_rectangleTrans {x : X} {u u' : ℝ × ℝ → X}
    (hseam : ∀ t, u (0, t) = u' (0, t)) {p : Ω^ (Fin 2) X x}
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

omit [FiniteDimensional ℂ F] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle ℂ F E] [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)] in
/-- On the boundary of the square, the frame of `exists_frame_rectangleTrans` is `φ₀` on the half
`s ≤ 1/2` and `φ₀' ∘ k` on the half `s ≥ 1/2`, when `φ` and `φ'` are constant, equal to `φ₀` and
`φ₀'`, on the edges `s = 1`, `t = 0`, `t = 1` of the unit square. -/
private theorem mk_frame_rectangleTrans_of_boundary {x : X} {u u' : ℝ × ℝ → X}
    {p : Ω^ (Fin 2) X x} {φ : ∀ z, F ≃L[ℂ] E (u z)} {φ' : ∀ z, F ≃L[ℂ] E (u' z)}
    {φ₀ φ₀' : F ≃L[ℂ] E x}
    (hφ₀ : ∀ s t : ℝ, s ∈ Icc 0 1 → t ∈ Icc 0 1 → (s = 1 ∨ t = 0 ∨ t = 1) → ∀ v,
      TotalSpace.mk' F (u (s, t)) (φ (s, t) v) = TotalSpace.mk' F x (φ₀ v))
    (hφ₀' : ∀ s t : ℝ, s ∈ Icc 0 1 → t ∈ Icc 0 1 → (s = 1 ∨ t = 0 ∨ t = 1) → ∀ v,
      TotalSpace.mk' F (u' (s, t)) (φ' (s, t) v) = TotalSpace.mk' F x (φ₀' v))
    {k : unitInterval → F ≃L[ℂ] F} {ψ : ∀ y, F ≃L[ℂ] E (p y)}
    (hψ : ∀ y v, TotalSpace.mk' F (p y) (ψ y v) =
        if (y 0 : ℝ) ≤ 1 / 2 then
          TotalSpace.mk' F (u (1 - Real.smoothTransition (3 * y 0), y 1))
            (φ (1 - Real.smoothTransition (3 * y 0), y 1) v)
        else TotalSpace.mk' F (u' (Real.smoothTransition (3 * y 0 - 2), y 1))
          (φ' (Real.smoothTransition (3 * y 0 - 2), y 1) (k (y 1) v))) :
    (∀ y, (y 0 : ℝ) ≤ 1 / 2 → ((y 0 : ℝ) = 0 ∨ (y 1 : ℝ) = 0 ∨ (y 1 : ℝ) = 1) → ∀ v,
      TotalSpace.mk' F (p y) (ψ y v) = TotalSpace.mk' F x (φ₀ v)) ∧
    (∀ y, ¬(y 0 : ℝ) ≤ 1 / 2 → ((y 0 : ℝ) = 1 ∨ (y 1 : ℝ) = 0 ∨ (y 1 : ℝ) = 1) → ∀ v,
      TotalSpace.mk' F (p y) (ψ y v) = TotalSpace.mk' F x (φ₀' (k (y 1) v))) := by
  refine ⟨fun y hy hy' v ↦ ?_, fun y hy hy' v ↦ ?_⟩
  · rw [hψ, ite_eq_left hy]
    refine hφ₀ _ _ ⟨by linarith [Real.smoothTransition.le_one (3 * (y 0 : ℝ))],
      by linarith [Real.smoothTransition.nonneg (3 * (y 0 : ℝ))]⟩ (y 1).property ?_ v
    rcases hy' with h | h | h
    · exact Or.inl (by simp [h])
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rw [hψ, ite_eq_right hy]
    refine hφ₀' _ _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
      (y 1).property ?_ _
    rcases hy' with h | h | h
    · exact Or.inl (by norm_num [h, Real.smoothTransition.one_of_one_le])
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

/-- **The clutching number of a sphere glued from two caps.** Let `u` and `u'` be continuous maps
of the plane that agree on the line `s = 0`, and let `p` be the sphere at `x` whose square is
`rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u'`, `u` run backwards followed by `u'`. Let `φ`
and `φ'` be continuous frames of `E` along `u` and `u'` that are constant, equal to `φ₀` and `φ₀'`,
on the three edges `s = 1`, `t = 0` and `t = 1` of the unit square, and let `k` be a continuous
family of automorphisms of `F` with `φ (0, t) = φ' (0, t) ∘ k t` along the edge `s = 0`. Then for
every continuous lift `θ` of the normalized determinant of `k` through `Circle.exp`,
`2π` times the clutching number of `p` is `θ 0 - θ 1`. -/
theorem clutchingNumber_mul_two_pi_eq_of_rectangleTrans {x : X} {u u' : ℝ × ℝ → X}
    (hseam : ∀ t, u (0, t) = u' (0, t)) {p : Ω^ (Fin 2) X x}
    (hp : ∀ y, p y = rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u' ((y 0 : ℝ), (y 1 : ℝ)))
    {φ : ∀ z, F ≃L[ℂ] E (u z)} {φ' : ∀ z, F ≃L[ℂ] E (u' z)}
    (hφ : Continuous fun q : (ℝ × ℝ) × F ↦ TotalSpace.mk' F (u q.1) (φ q.1 q.2))
    (hφ' : Continuous fun q : (ℝ × ℝ) × F ↦ TotalSpace.mk' F (u' q.1) (φ' q.1 q.2))
    {φ₀ φ₀' : F ≃L[ℂ] E x}
    (hφ₀ : ∀ s t : ℝ, s ∈ Icc 0 1 → t ∈ Icc 0 1 → (s = 1 ∨ t = 0 ∨ t = 1) → ∀ v,
      TotalSpace.mk' F (u (s, t)) (φ (s, t) v) = TotalSpace.mk' F x (φ₀ v))
    (hφ₀' : ∀ s t : ℝ, s ∈ Icc 0 1 → t ∈ Icc 0 1 → (s = 1 ∨ t = 0 ∨ t = 1) → ∀ v,
      TotalSpace.mk' F (u' (s, t)) (φ' (s, t) v) = TotalSpace.mk' F x (φ₀' v))
    {k : unitInterval → F ≃L[ℂ] F} (hk : Continuous fun t ↦ (k t : F →L[ℂ] F))
    (hφk : ∀ (t : unitInterval) v, TotalSpace.mk' F (u (0, t)) (φ (0, t) v) =
      TotalSpace.mk' F (u' (0, t)) (φ' (0, t) (k t v)))
    {θ : unitInterval → ℝ} (hθ : Continuous θ)
    (hθk : ∀ t, Circle.exp (θ t) = (k t).normalizedDet) :
    (clutchingNumber F E p : ℝ) * (2 * Real.pi) = θ 0 - θ 1 := by
  obtain ⟨ψ, hψc, hψ⟩ := exists_frame_rectangleTrans hseam hp hφ hφ' hk hφk
  obtain ⟨hleft, hright⟩ := mk_frame_rectangleTrans_of_boundary hφ₀ hφ₀' hψ
  set e := trivializationAt F E x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F E x
  rw [clutchingNumber_eq_squareBoundaryDegree p e hx hψc]
  -- The values of the clutching function at the frames `φ₀` and `φ₀' ∘ k t` at `x`.
  set c := clutchingFunction (fun _ : Unit ↦ x) (fun _ ↦ φ₀) e ()
  set c' := (φ₀'.trans (e.continuousLinearEquivAt ℂ x hx)).normalizedDet⁻¹
  have hc' (t : unitInterval) :
      clutchingFunction (fun _ : Unit ↦ x) (fun _ ↦ (k t).trans φ₀') e () =
        c' * (k t).normalizedDet⁻¹ := by
    -- Composition of continuous linear equivalences is associative by definition.
    rw [clutchingFunction_of_mem (f := fun _ : Unit ↦ x) hx,
      show ((k t).trans φ₀').trans (e.continuousLinearEquivAt ℂ x hx) =
        (k t).trans (φ₀'.trans (e.continuousLinearEquivAt ℂ x hx)) from rfl,
      ContinuousLinearEquiv.normalizedDet_trans, mul_inv, mul_comm]
  -- On the right half of the boundary the clutching function is `c' * (det k)⁻¹`, and at the
  -- corners `t = 0`, `t = 1` of the edge `s = 0` this is `c`, as `φ₀ = φ₀' ∘ k t` there.
  have hR (y : Fin 2 → unitInterval) (hy : ¬(y 0 : ℝ) ≤ 1 / 2)
      (hy' : (y 0 : ℝ) = 1 ∨ (y 1 : ℝ) = 0 ∨ (y 1 : ℝ) = 1) :
      clutchingFunction p ψ e y = c' * (k (y 1)).normalizedDet⁻¹ :=
    (clutchingFunction_eq_of_mk_eq e fun v ↦ (hright y hy hy' v).trans rfl).trans (hc' _)
  have hcorner (t : unitInterval) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1) :
      c' * (k t).normalizedDet⁻¹ = c := by
    rw [← hc']
    refine clutchingFunction_eq_of_mk_eq e fun v ↦ ?_
    rw [ContinuousLinearEquiv.trans_apply, ← hφ₀' 0 t ⟨le_rfl, zero_le_one⟩ t.property (Or.inr ht),
      ← hφk t v, hφ₀ 0 t ⟨le_rfl, zero_le_one⟩ t.property (Or.inr ht)]
  have hhor (s t : unitInterval) (ht : t = 0 ∨ t = 1) :
      clutchingFunction p ψ e ![s, t] = c := by
    by_cases hs : (s : ℝ) ≤ 1 / 2
    · exact clutchingFunction_eq_of_mk_eq e
        (hleft _ (by simpa using hs) (Or.inr (by simpa using ht)))
    · rw [hR _ (by simpa using hs) (Or.inr (by simpa using ht))]
      exact hcorner _ (by simpa using ht)
  exact squareBoundaryDegree_mul_two_pi_eq_of_edges
    (continuousOn_clutchingFunction_boundary p hψc e hx) (fun s ↦ hhor s 0 (Or.inl rfl))
    (fun s ↦ hhor s 1 (Or.inr rfl))
    (fun t ↦ clutchingFunction_eq_of_mk_eq e (hleft _ (by norm_num) (Or.inl (by simp))))
    (fun t ↦ by simpa using hR ![1, t] (by norm_num) (Or.inl (by simp))) hθ hθk

end Clutching

/-! ### The first Chern number of the sphere bounded by two smooth caps -/

section Symplectic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {J : SmoothAlmostComplexStructure I M}
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ E = 2 * finrank ℂ G)]

/-- A real frame `χ : G ≃ T_b M` that is complex linear for `J`, as a complex frame of the fibre
at `b` of the complex vector bundle `(TM, J)`. -/
private def complexFrame {b : M} (χ : G ≃L[ℝ] TangentSpace I b)
    (hχ : ∀ v, χ (Complex.I • v) = J b (χ v)) :
    G ≃L[ℂ] (J.toContMDiff 0).toContinuousComplexStructure.Fiber b where
  toFun v := ((J.toContMDiff 0).toContinuousComplexStructure.fiberEquiv b).symm (χ v)
  invFun w := χ.symm ((J.toContMDiff 0).toContinuousComplexStructure.fiberEquiv b w)
  map_add' v w := by simp
  map_smul' c v := by
    apply ((J.toContMDiff 0).toContinuousComplexStructure.fiberEquiv b).injective
    rw [Bundle.ContinuousComplexStructure.fiberEquiv_smul, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply, RingHom.id_apply]
    conv_lhs => rw [← Complex.re_add_im c, add_smul, mul_smul, Complex.coe_smul,
      Complex.coe_smul]
    rw [map_add, map_smul, map_smul, hχ]
    rw [ContMDiffAlmostComplexStructure.toContinuousComplexStructure_apply,
      SmoothAlmostComplexStructure.toContMDiff_apply]
  left_inv v := by simp
  right_inv w := by simp
  continuous_toFun :=
    ((J.toContMDiff 0).toContinuousComplexStructure.fiberEquiv b).symm.continuous.comp
      χ.continuous
  continuous_invFun :=
    χ.symm.continuous.comp ((J.toContMDiff 0).toContinuousComplexStructure.fiberEquiv b).continuous

/-- The complex frame of a real frame `χ` is `χ`, read in the tangent bundle. -/
private theorem totalSpaceHomeomorph_mk_complexFrame {b : M} (χ : G ≃L[ℝ] TangentSpace I b)
    (hχ : ∀ v, χ (Complex.I • v) = J b (χ v)) (v : G) :
    (J.toContMDiff 0).toContinuousComplexStructure.totalSpaceHomeomorph G
      (TotalSpace.mk' G b (complexFrame χ hχ v)) = (⟨b, χ v⟩ : TangentBundle I M) := by
  rw [Bundle.ContinuousComplexStructure.totalSpaceHomeomorph_apply]
  exact congrArg (TotalSpace.mk' E b) (ContinuousLinearEquiv.apply_symm_apply _ _)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- Tangent vectors at equal points with equal underlying vectors are equal in the tangent
bundle. -/
private theorem tangentBundle_mk_eq_of_eq {b b' : M} (hb : b = b') (w : TangentSpace I b) :
    (⟨b, w⟩ : TangentBundle I M) = ⟨b', w⟩ := by
  subst hb
  rfl

variable [T2Space M] [SigmaCompactSpace M] {σ : SmoothTwoForm I M} {x : M} {γ : Ω M x}
  {u u' : ℝ × ℝ → M}

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] in
/-- A smooth based cap is at the base point on the three edges `s = 1`, `t = 0`, `t = 1` of the
unit square. -/
private theorem IsSmoothBasedCap.apply_eq_of_edge (hu : IsSmoothBasedCap I γ u) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hst : s = 1 ∨ t = 0 ∨ t = 1) : u (s, t) = x := by
  rcases hst with rfl | rfl | rfl
  · simpa using hu.apply_one ⟨t, ht⟩
  · simpa using hu.apply_seam ⟨s, hs⟩
  · simpa using hu.apply_seam_one ⟨s, hs⟩

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] in
/-- The sphere by which the raw caps of two smooth based caps `u'` and `u` differ is represented by
the square of `u` run backwards followed by `u'`. -/
private theorem IsSmoothBasedCap.exists_genLoop_homotopyClass_vsub_homotopyClass
    (hu : IsSmoothBasedCap I γ u) (hu' : IsSmoothBasedCap I γ u') :
    ∃ p : Ω^ (Fin 2) M x,
      (∀ y, p y = rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u' ((y 0 : ℝ), (y 1 : ℝ))) ∧
        hu'.homotopyClass -ᵥ hu.homotopyClass = Additive.ofMul ⟦p⟧ := by
  set w := rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u'
  have hw : IsSmoothBasedHomotopy I (Path.refl x) (Path.refl x) w :=
    hu.comp_prodMap_one_sub.rectangleTrans hu'
  let p : Ω^ (Fin 2) M x := ⟨⟨fun y ↦ w ((y 0 : ℝ), (y 1 : ℝ)),
    hw.contMDiff.continuous.comp (by fun_prop)⟩, fun y hy ↦ by
      simp only [Cube.boundary, Set.mem_ofPred_eq, Fin.exists_fin_two] at hy
      -- Evaluate the continuous map built from `w` at `y`.
      change w ((y 0 : ℝ), (y 1 : ℝ)) = x
      rcases hy with (hi | hi) | (hi | hi) <;> rw [hi]
      · simpa using hw.apply_zero (y 1)
      · simpa using hw.apply_one (y 1)
      · simpa using hw.apply_seam (y 0)
      · simpa using hw.apply_seam_one (y 0)⟩
  exact ⟨p, fun y ↦ rfl, hu.homotopyClass_vsub_homotopyClass_toMul hu' fun y ↦ rfl⟩

omit [FiniteDimensional ℂ G] [Fact (finrank ℝ E = 2 * finrank ℂ G)] [T2Space M]
  [SigmaCompactSpace M] in
/-- If two continuous frames along maps agreeing on the line `s = 0` differ there by complex-linear
automorphisms `k t` of the model, `χ (0, t) = χ' (0, t) ∘ k t`, then `k` is continuous. -/
private theorem continuous_of_apply_eq_apply {χ : ∀ z, G ≃L[ℝ] TangentSpace I (u z)}
    {χ' : ∀ z, G ≃L[ℝ] TangentSpace I (u' z)}
    (hχ : Continuous fun q : (ℝ × ℝ) × G ↦ (⟨u q.1, χ q.1 q.2⟩ : TangentBundle I M))
    (hχ' : Continuous fun q : (ℝ × ℝ) × G ↦ (⟨u' q.1, χ' q.1 q.2⟩ : TangentBundle I M))
    (hseam : ∀ t, u (0, t) = u' (0, t)) {k : unitInterval → G ≃L[ℂ] G}
    (hχk : ∀ (t : unitInterval) v, χ (0, t) v = χ' (0, t) (k t v)) :
    Continuous fun t ↦ (k t : G →L[ℂ] G) := by
  have hγc : Continuous fun q : unitInterval × G ↦ (((0 : ℝ), (q.1 : ℝ)), q.2) :=
    (continuous_const.prodMk (continuous_subtypeVal.comp continuous_fst)).prodMk continuous_snd
  -- As real-linear maps, `k t = χ' (0, t)⁻¹ ∘ χ (0, t)` is a change of frame along `u (0, ·)`.
  have hA : Continuous fun t : unitInterval ↦
      (((χ (0, t)).trans (χ' (0, t)).symm : G ≃L[ℝ] G) : G →L[ℝ] G) :=
    continuous_trans_symm_of_continuous_frame (f := fun t : unitInterval ↦ u (0, t))
      (φ := fun t ↦ χ (0, t)) (ψ := fun t ↦ χ' (0, t)) (hχ.comp hγc)
      ((hχ'.comp hγc).congr fun q ↦ (tangentBundle_mk_eq_of_eq (hseam q.1).symm _))
  refine ((ContinuousLinearMap.restrictScalarsIsometry ℂ G G ℝ ℝ).isometry.isEmbedding
    |>.continuous_iff).2 (hA.congr fun t ↦ ?_)
  ext v
  rw [Function.comp_apply, ContinuousLinearMap.coe_restrictScalarsIsometry,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_coe]
  exact ((χ' (0, t)).symm_apply_eq).2 (hχk t v)

/-- **The first Chern number of the sphere bounded by two smooth caps.** Let `u` and `u'` be
smooth based caps of a loop `γ` at `x`, in a manifold with a fiberwise nondegenerate two-form `σ`
taming an almost complex structure `J`. Let `χ` and `χ'` be real frames of the tangent bundle along
`u` and `u'`, continuous into the tangent bundle, complex linear for `J`, and constant on the three
edges `s = 1`, `t = 0`, `t = 1` of the unit square, where the caps are at `x`. Along `γ` they
differ by a continuous loop `k` of complex-linear automorphisms of the model,
`χ (0, t) = χ' (0, t) ∘ k t`. Then for every continuous lift `θ` of the normalized complex
determinant of `k` through `Circle.exp`, `2π` times the first Chern number of the sphere
`D' -ᵥ D` by which the raw caps of `u'` and `u` differ is `θ 0 - θ 1`. -/
theorem IsSmoothBasedCap.firstChernHom_homotopyClass_vsub_homotopyClass_mul_two_pi_eq
    (h : σ.IsNondegenerate) (hJ : σ.Tames J) (hu : IsSmoothBasedCap I γ u)
    (hu' : IsSmoothBasedCap I γ u')
    {χ : ∀ z, G ≃L[ℝ] TangentSpace I (u z)} {χ' : ∀ z, G ≃L[ℝ] TangentSpace I (u' z)}
    (hχ : Continuous fun q : (ℝ × ℝ) × G ↦ (⟨u q.1, χ q.1 q.2⟩ : TangentBundle I M))
    (hχ' : Continuous fun q : (ℝ × ℝ) × G ↦ (⟨u' q.1, χ' q.1 q.2⟩ : TangentBundle I M))
    (hχJ : ∀ z v, χ z (Complex.I • v) = J (u z) (χ z v))
    (hχJ' : ∀ z v, χ' z (Complex.I • v) = J (u' z) (χ' z v))
    (hχ₀ : ∀ s t : ℝ, s ∈ Icc 0 1 → t ∈ Icc 0 1 → (s = 1 ∨ t = 0 ∨ t = 1) → ∀ v,
      χ (s, t) v = χ (1, 0) v)
    (hχ₀' : ∀ s t : ℝ, s ∈ Icc 0 1 → t ∈ Icc 0 1 → (s = 1 ∨ t = 0 ∨ t = 1) → ∀ v,
      χ' (s, t) v = χ' (1, 0) v)
    {k : unitInterval → G ≃L[ℂ] G} (hχk : ∀ (t : unitInterval) v, χ (0, t) v = χ' (0, t) (k t v))
    {θ : unitInterval → ℝ} (hθ : Continuous θ) (hθk : ∀ t, Circle.exp (θ t) = (k t).normalizedDet) :
    (h.firstChernHom x (hu'.homotopyClass -ᵥ hu.homotopyClass) : ℝ) * (2 * Real.pi) =
      θ 0 - θ 1 := by
  obtain ⟨p, hp, hvsub⟩ := hu.exists_genLoop_homotopyClass_vsub_homotopyClass hu'
  rw [(congrArg (h.firstChernHom x) hvsub).trans (h.firstChernHom_apply_mk G hJ 0 p)]
  -- The complex frames of `(TM, J)` along the two caps.
  set Jc := (J.toContMDiff 0).toContinuousComplexStructure
  let φ : ∀ z, G ≃L[ℂ] Jc.Fiber (u z) := fun z ↦ complexFrame (χ z) (hχJ z)
  let φ' : ∀ z, G ≃L[ℂ] Jc.Fiber (u' z) := fun z ↦ complexFrame (χ' z) (hχJ' z)
  have hφ : Continuous fun q : (ℝ × ℝ) × G ↦ TotalSpace.mk' G (u q.1) (φ q.1 q.2) :=
    ((Jc.totalSpaceHomeomorph G).symm.continuous.comp hχ).congr fun q ↦ by
      -- `complexFrame χ` is `χ` followed by the identification of `T M` with the fibre of `Jc`.
      rw [Function.comp_apply, Bundle.ContinuousComplexStructure.totalSpaceHomeomorph_symm_apply]
      rfl
  have hφ' : Continuous fun q : (ℝ × ℝ) × G ↦ TotalSpace.mk' G (u' q.1) (φ' q.1 q.2) :=
    ((Jc.totalSpaceHomeomorph G).symm.continuous.comp hχ').congr fun q ↦ by
      -- `complexFrame χ'` is `χ'` followed by the identification of `T M` with the fibre of `Jc`.
      rw [Function.comp_apply, Bundle.ContinuousComplexStructure.totalSpaceHomeomorph_symm_apply]
      rfl
  have hx₀ : u (1, 0) = x := by simpa using hu.apply_one 0
  have hx₀' : u' (1, 0) = x := by simpa using hu'.apply_one 0
  have hmk (z : ℝ × ℝ) (v : G) : Jc.totalSpaceHomeomorph G (TotalSpace.mk' G (u z) (φ z v)) =
      (⟨u z, χ z v⟩ : TangentBundle I M) :=
    totalSpaceHomeomorph_mk_complexFrame (χ z) (hχJ z) v
  have hmk' (z : ℝ × ℝ) (v : G) :
      Jc.totalSpaceHomeomorph G (TotalSpace.mk' G (u' z) (φ' z v)) =
        (⟨u' z, χ' z v⟩ : TangentBundle I M) :=
    totalSpaceHomeomorph_mk_complexFrame (χ' z) (hχJ' z) v
  have hseam := hu.apply_zero_eq_apply_zero hu'
  exact clutchingNumber_mul_two_pi_eq_of_rectangleTrans hseam hp hφ hφ'
    (φ₀ := (φ (1, 0)).trans (fiberCast (E := Jc.Fiber) hx₀))
    (φ₀' := (φ' (1, 0)).trans (fiberCast (E := Jc.Fiber) hx₀'))
    (fun s t hs ht hst v ↦ by
      rw [ContinuousLinearEquiv.trans_apply, mk_fiberCast]
      refine (Jc.totalSpaceHomeomorph G).injective ?_
      rw [hmk, hmk, hχ₀ s t hs ht hst v]
      exact tangentBundle_mk_eq_of_eq ((hu.apply_eq_of_edge hs ht hst).trans hx₀.symm) _)
    (fun s t hs ht hst v ↦ by
      rw [ContinuousLinearEquiv.trans_apply, mk_fiberCast]
      refine (Jc.totalSpaceHomeomorph G).injective ?_
      rw [hmk', hmk', hχ₀' s t hs ht hst v]
      exact tangentBundle_mk_eq_of_eq ((hu'.apply_eq_of_edge hs ht hst).trans hx₀'.symm) _)
    (continuous_of_apply_eq_apply hχ hχ' hseam hχk) (fun t v ↦
      (Jc.totalSpaceHomeomorph G).injective <| by
      rw [hmk, hmk', hχk t v]
      exact tangentBundle_mk_eq_of_eq (hseam t) _) hθ hθk

/-! ### Frames over a cap that are constant on its edges at the base point -/

/-- A retraction of the plane onto the three edges `s = 1`, `t = 0`, `t = 1` of the unit square:
clamp to the square, then project radially from the point `(-1, 1/2)` onto the three edges, which
form the unit sphere of `d ↦ max (d₁ / 2) (2 |d₂|)` around that point. -/
private def capEdgeRetraction (z : ℝ × ℝ) : ℝ × ℝ :=
  (((max 0 (min z.1 1) + 1) / max ((max 0 (min z.1 1) + 1) / 2) (2 * |max 0 (min z.2 1) - 1 / 2|)
      - 1),
    ((max 0 (min z.2 1) - 1 / 2) / max ((max 0 (min z.1 1) + 1) / 2)
      (2 * |max 0 (min z.2 1) - 1 / 2|) + 1 / 2))

/-- The radial scale of `capEdgeRetraction`: for `a, b ∈ [0, 1]`,
`1/2 ≤ max ((a + 1) / 2) (2 |b - 1/2|) ≤ 1`. -/
private theorem capEdgeRetraction_scale {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) :
    1 / 2 ≤ max ((a + 1) / 2) (2 * |b - 1 / 2|) ∧ max ((a + 1) / 2) (2 * |b - 1 / 2|) ≤ 1 := by
  have hab : |b - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith [hb.1], by linarith [hb.2]⟩
  exact ⟨le_max_of_le_left (by linarith [ha.1]),
    max_le (by linarith [ha.2]) (by linarith)⟩

private theorem clamp_mem (r : ℝ) : max 0 (min r 1) ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

private theorem continuous_capEdgeRetraction : Continuous capEdgeRetraction := by
  have hN (z : ℝ × ℝ) : max ((max 0 (min z.1 1) + 1) / 2) (2 * |max 0 (min z.2 1) - 1 / 2|) ≠ 0 :=
    (lt_of_lt_of_le (by norm_num) (capEdgeRetraction_scale (clamp_mem z.1) (clamp_mem z.2)).1).ne'
  unfold capEdgeRetraction
  exact ((Continuous.div (by fun_prop) (by fun_prop) hN).sub continuous_const).prodMk
    ((Continuous.div (by fun_prop) (by fun_prop) hN).add continuous_const)

/-- The radial projection of `capEdgeRetraction` lands in the three edges: for `a, b ∈ [0, 1]` and
`N = max ((a + 1) / 2) (2 |b - 1/2|)`, the point `((a + 1) / N - 1, (b - 1/2) / N + 1/2)` lies on
the edge `s = 1`, `t = 0` or `t = 1` of the unit square. -/
private theorem capEdge_mem {a b N : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hNdef : N = max ((a + 1) / 2) (2 * |b - 1 / 2|)) :
    (a + 1) / N - 1 ∈ Icc (0 : ℝ) 1 ∧ (b - 1 / 2) / N + 1 / 2 ∈ Icc (0 : ℝ) 1 ∧
      ((a + 1) / N - 1 = 1 ∨ (b - 1 / 2) / N + 1 / 2 = 0 ∨ (b - 1 / 2) / N + 1 / 2 = 1) := by
  obtain ⟨hN₁, hN₂⟩ := capEdgeRetraction_scale ha hb
  rw [← hNdef] at hN₁ hN₂
  have hN : 0 < N := lt_of_lt_of_le (by norm_num) hN₁
  have hNa : (a + 1) / 2 ≤ N := hNdef ▸ le_max_left _ _
  have hNb : 2 * |b - 1 / 2| ≤ N := hNdef ▸ le_max_right _ _
  have hb' := abs_le.1 (show |b - 1 / 2| ≤ N / 2 by linarith)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [sub_nonneg, le_div_iff₀ hN]
    linarith [ha.1]
  · rw [sub_le_iff_le_add, div_le_iff₀ hN]
    linarith
  · have : -(1 / 2) ≤ (b - 1 / 2) / N := by
      rw [le_div_iff₀ hN]
      linarith [hb'.1]
    linarith
  · have : (b - 1 / 2) / N ≤ 1 / 2 := by
      rw [div_le_iff₀ hN]
      linarith [hb'.2]
    linarith
  · have ha1 : a + 1 ≠ 0 := by linarith [ha.1]
    rcases max_choice ((a + 1) / 2) (2 * |b - 1 / 2|) with h | h <;> rw [← hNdef] at h
    · left
      rw [h]
      field_simp
      ring
    · right
      have hc : b - 1 / 2 ≠ 0 := fun hc ↦ by
        rw [hc, abs_zero, mul_zero] at h
        linarith
      rcases le_or_gt 0 (b - 1 / 2) with hs | hs
      · right
        rw [abs_of_nonneg hs] at h
        rw [h, mul_comm, ← div_div, div_self hc]
        norm_num
      · left
        rw [abs_of_neg hs] at h
        rw [h, mul_neg, div_neg, mul_comm, ← div_div, div_self hc]
        norm_num

/-- `capEdgeRetraction` lands in the three edges `s = 1`, `t = 0`, `t = 1` of the unit square. -/
private theorem capEdgeRetraction_mem (z : ℝ × ℝ) :
    (capEdgeRetraction z).1 ∈ Icc (0 : ℝ) 1 ∧ (capEdgeRetraction z).2 ∈ Icc (0 : ℝ) 1 ∧
      ((capEdgeRetraction z).1 = 1 ∨ (capEdgeRetraction z).2 = 0 ∨
        (capEdgeRetraction z).2 = 1) :=
  capEdge_mem (clamp_mem z.1) (clamp_mem z.2) rfl

/-- `capEdgeRetraction` fixes the three edges `s = 1`, `t = 0`, `t = 1` of the unit square. -/
private theorem capEdgeRetraction_eq {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hst : s = 1 ∨ t = 0 ∨ t = 1) : capEdgeRetraction (s, t) = (s, t) := by
  have hs' : max 0 (min s 1) = s := by rw [min_eq_left hs.2, max_eq_right hs.1]
  have ht' : max 0 (min t 1) = t := by rw [min_eq_left ht.2, max_eq_right ht.1]
  have hN : max ((s + 1) / 2) (2 * |t - 1 / 2|) = 1 := by
    have htb : |t - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rcases hst with rfl | rfl | rfl
    · rw [max_eq_left (by linarith)]
      norm_num
    · rw [max_eq_right (by norm_num; linarith [hs.2])]
      norm_num
    · rw [max_eq_right (by norm_num; linarith [hs.2])]
      norm_num
  simp only [capEdgeRetraction, hs', ht', hN, div_one]
  ext <;> simp only <;> ring

omit [T2Space M] [SigmaCompactSpace M] in
/-- **Frames over a cap.** Along every smooth based cap `u` of a loop at `x` there is a real frame
of the tangent bundle, continuous into the tangent bundle and complex linear for an almost complex
structure `J`, that is constant on the three edges `s = 1`, `t = 0`, `t = 1` of the unit square,
where `u` is at `x`: a frame of the tangent bundle over the disc. Such frames are the input of
`TauCeti.Floer.IsSmoothBasedCap.firstChernHom_homotopyClass_vsub_homotopyClass_mul_two_pi_eq`. -/
theorem IsSmoothBasedCap.exists_frame_eq_on_edges (hu : IsSmoothBasedCap I γ u) :
    ∃ χ : ∀ z, G ≃L[ℝ] TangentSpace I (u z),
      Continuous (fun q : (ℝ × ℝ) × G ↦ (⟨u q.1, χ q.1 q.2⟩ : TangentBundle I M)) ∧
      (∀ z v, χ z (Complex.I • v) = J (u z) (χ z v)) ∧
      ∀ s t : ℝ, s ∈ Icc 0 1 → t ∈ Icc 0 1 → (s = 1 ∨ t = 0 ∨ t = 1) → ∀ v,
        χ (s, t) v = χ (1, 0) v := by
  obtain ⟨φ, hφ, hφJ⟩ :=
    (J.toContMDiff 0).exists_continuous_frame (G := G) hu.contMDiff.continuous
  set ρ := capEdgeRetraction
  have hρ : Continuous ρ := continuous_capEdgeRetraction
  have hcorner : (1 : ℝ) ∈ Icc (0 : ℝ) 1 ∧ (0 : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨⟨zero_le_one, le_rfl⟩, ⟨le_rfl, zero_le_one⟩⟩
  have hρx (z : ℝ × ℝ) : u (ρ z) = u (1, 0) := by
    obtain ⟨h₁, h₂, h₃⟩ := capEdgeRetraction_mem z
    exact (hu.apply_eq_of_edge h₁ h₂ h₃).trans
      (hu.apply_eq_of_edge hcorner.1 hcorner.2 (Or.inl rfl)).symm
  -- The change of frame from `φ` at the retraction of `z` back to `φ` at the corner `(1, 0)`.
  let A : ℝ × ℝ → G ≃L[ℝ] G := fun z ↦ (φ (1, 0)).trans (φ (ρ z)).symm
  have hA : Continuous fun z ↦ (A z : G →L[ℝ] G) := by
    refine continuous_trans_symm_of_continuous_frame (f := u ∘ ρ) (φ := fun _ ↦ φ (1, 0))
      (ψ := fun z ↦ φ (ρ z)) ?_ (hφ.comp ((hρ.comp continuous_fst).prodMk continuous_snd))
    refine (hφ.comp ((continuous_const (y := ((1, 0) : ℝ × ℝ))).prodMk
      continuous_snd)).congr fun q ↦ ?_
    exact (tangentBundle_mk_eq_of_eq (hρx q.1) _).symm
  refine ⟨fun z ↦ (A z).trans (φ z),
    hφ.comp (continuous_fst.prodMk ((hA.comp continuous_fst).clm_apply continuous_snd)),
    fun z v ↦ ?_, fun s t hs ht hst v ↦ ?_⟩
  · -- `A z` is complex linear: both frames are complex linear for `J` at the same point `x`.
    have hJ (w : E) : J.toEndomorphism (u (1, 0)) w = J.toEndomorphism (u (ρ z)) w := by
      rw [hρx]
    have hAI : A z (Complex.I • v) = Complex.I • A z v := by
      -- `A z` composes frames at the points `(1, 0)` and `ρ z`, whose tangent spaces are equal
      -- only definitionally, so `ContinuousLinearEquiv.trans_apply` does not rewrite it.
      change (φ (ρ z)).symm (φ (1, 0) (Complex.I • v)) =
        Complex.I • (φ (ρ z)).symm (φ (1, 0) v)
      rw [hφJ, SmoothAlmostComplexStructure.toContMDiff_apply]
      apply (φ (ρ z)).injective
      rw [hφJ, SmoothAlmostComplexStructure.toContMDiff_apply]
      exact ((φ (ρ z)).apply_symm_apply _).trans ((hJ _).trans
        (congrArg (J.toEndomorphism (u (ρ z))) ((φ (ρ z)).apply_symm_apply _).symm))
    rw [ContinuousLinearEquiv.trans_apply, hAI, hφJ, SmoothAlmostComplexStructure.toContMDiff_apply]
    -- Both sides are `J (u z)` applied to `φ z (A z v)`.
    rfl
  · -- On the edges the retraction is the identity, so the frame is `φ (1, 0)`.
    have hfix {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
        (hst : s = 1 ∨ t = 0 ∨ t = 1) (w : G) : (A (s, t)).trans (φ (s, t)) w = φ (1, 0) w := by
      -- As for `hAI`, the composite is unfolded by `change` since its tangent spaces are equal
      -- only definitionally.
      change φ (s, t) ((φ (ρ (s, t))).symm (φ (1, 0) w)) = φ (1, 0) w
      rw [show ρ (s, t) = (s, t) from capEdgeRetraction_eq hs ht hst]
      exact (φ (s, t)).apply_symm_apply _
    -- Evaluate the frame `fun z ↦ (A z).trans (φ z)` at the two points.
    change (A (s, t)).trans (φ (s, t)) v = (A (1, 0)).trans (φ (1, 0)) v
    rw [hfix hs ht hst, hfix hcorner.1 hcorner.2 (Or.inl rfl)]

end Symplectic

end TauCeti.Floer

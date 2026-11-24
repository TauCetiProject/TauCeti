/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Area
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chern
import TauCeti.Topology.Homotopy.Extension.Cube
import TauCeti.Topology.VectorBundle.FiberCast

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
(`TauCeti.SmoothTwoForm.frameConleyZehnderIndex_eq_add_maslovIndex`). That theorem takes symplectic
frames, while the frames here are only complex linear for `J`. When the frames over the two caps
are moreover symplectic for `σ`, hence unitary for `σ` and `J`, along the orbit, the change of
trivialization along the orbit is the loop `k⁻¹` of unitary maps. Turning the statement here into
the recapping law then also needs the comparison of the Maslov index of a loop of unitary maps
with the winding of its complex determinant. Neither the unitary frames nor this comparison are
made in this file.

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

omit [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)] in
/-- If continuous frames `φ` and `φ'` along maps agreeing on the line `s = 0` differ there by
automorphisms `k t` of `F`, `φ (0, t) = φ' (0, t) ∘ k t`, then `k` is continuous. -/
private theorem continuous_of_mk_eq_mk {u u' : ℝ × ℝ → X} (hseam : ∀ t, u (0, t) = u' (0, t))
    {φ : ∀ z, F ≃L[ℂ] E (u z)} {φ' : ∀ z, F ≃L[ℂ] E (u' z)}
    (hφ : Continuous fun q : (ℝ × ℝ) × F ↦ TotalSpace.mk' F (u q.1) (φ q.1 q.2))
    (hφ' : Continuous fun q : (ℝ × ℝ) × F ↦ TotalSpace.mk' F (u' q.1) (φ' q.1 q.2))
    {k : unitInterval → F ≃L[ℂ] F}
    (hφk : ∀ (t : unitInterval) v, TotalSpace.mk' F (u (0, t)) (φ (0, t) v) =
      TotalSpace.mk' F (u' (0, t)) (φ' (0, t) (k t v))) :
    Continuous fun t ↦ (k t : F →L[ℂ] F) := by
  have hγ : Continuous fun q : unitInterval × F ↦ (((0 : ℝ), (q.1 : ℝ)), q.2) := by fun_prop
  -- `φ'` along `u' (0, ·)`, read as a frame along `u (0, ·)`.
  let ψ : ∀ t : unitInterval, F ≃L[ℂ] E (u (0, t)) := fun t ↦
    (φ' (0, t)).trans (fiberCast (hseam t).symm)
  have hψ (t : unitInterval) (v : F) :
      TotalSpace.mk' F (u (0, t)) (ψ t v) = TotalSpace.mk' F (u' (0, t)) (φ' (0, t) v) := by
    rw [ContinuousLinearEquiv.trans_apply, mk_fiberCast]
  -- As maps of `F`, `k t = (ψ t)⁻¹ ∘ φ (0, t)` is a change of frame along `u (0, ·)`.
  refine (continuous_trans_symm_of_continuous_frame (f := fun t : unitInterval ↦ u (0, t))
    (φ := fun t ↦ φ (0, t)) (ψ := ψ) (hφ.comp hγ)
    ((hφ'.comp hγ).congr fun q ↦ (hψ q.1 q.2).symm)).congr fun t ↦ ?_
  ext v
  rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.symm_apply_eq]
  exact TotalSpace.mk_inj.1 ((hφk t v).trans (hψ t (k t v)).symm)

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

/-- **The clutching number of a sphere glued from two caps.** Let `u` and `u'` be maps of the
plane that agree on the line `s = 0`, and let `p` be the sphere at `x` whose square is
`rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u'`, `u` run backwards followed by `u'`. Let `φ`
and `φ'` be continuous frames of `E` along `u` and `u'` that are constant, equal to `φ₀` and `φ₀'`,
on the three edges `s = 1`, `t = 0` and `t = 1` of the unit square, and let `k` be a family of
automorphisms of `F` with `φ (0, t) = φ' (0, t) ∘ k t` along the edge `s = 0` (it is automatically
continuous, since `φ` and `φ'` are). Then for every continuous lift `θ` of the normalized
determinant of `k` through `Circle.exp`, `2π` times the clutching number of `p` is `θ 0 - θ 1`. -/
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
    {k : unitInterval → F ≃L[ℂ] F}
    (hφk : ∀ (t : unitInterval) v, TotalSpace.mk' F (u (0, t)) (φ (0, t) v) =
      TotalSpace.mk' F (u' (0, t)) (φ' (0, t) (k t v)))
    {θ : unitInterval → ℝ} (hθ : Continuous θ)
    (hθk : ∀ t, Circle.exp (θ t) = (k t).normalizedDet) :
    (clutchingNumber F E p : ℝ) * (2 * Real.pi) = θ 0 - θ 1 := by
  obtain ⟨ψ, hψc, hψ⟩ :=
    exists_frame_rectangleTrans hseam hp hφ hφ' (continuous_of_mk_eq_mk hseam hφ hφ' hφk) hφk
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
    (clutchingFunction_eq_of_mk_eq e fun v ↦ by
      rw [ContinuousLinearEquiv.trans_apply]
      exact hright y hy hy' v).trans (hc' _)
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
  -- Along the right edge `θc' - θ` lifts `c' * (det k)⁻¹`.
  obtain ⟨θc', hθc'⟩ := Circle.exp_surjective c'
  rw [squareBoundaryDegree_mul_two_pi_eq_of_edges
    (continuousOn_clutchingFunction_boundary p hψc e hx) (fun s ↦ hhor s 0 (Or.inl rfl))
    (fun s ↦ hhor s 1 (Or.inr rfl))
    (fun t ↦ clutchingFunction_eq_of_mk_eq e (hleft _ (by norm_num) (Or.inl (by simp))))
    (fun t ↦ by simpa using hR ![1, t] (by norm_num) (Or.inl (by simp)))
    (continuous_const.sub hθ) (θ := fun t ↦ θc' - θ t)
    fun t ↦ by rw [Circle.exp_sub, hθc', hθk, div_eq_mul_inv]]
  ring

end Clutching

/-! ### The first Chern number of the sphere bounded by two smooth caps -/

section Symplectic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {J : SmoothAlmostComplexStructure I M}
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ E = 2 * finrank ℂ G)]

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

omit [T2Space M] [SigmaCompactSpace M] in
/-- A continuous real frame `χ` of the tangent bundle along a smooth based cap `u`, complex linear
for `J` and constant on the three edges `s = 1`, `t = 0`, `t = 1` of the unit square, gives a
continuous complex frame of `(TM, J)` along `u` that is constant on these edges, where `u` is at
the base point. -/
private theorem IsSmoothBasedCap.complexFrame_of_eq_on_edges (hu : IsSmoothBasedCap I γ u)
    {χ : ∀ z, G ≃L[ℝ] TangentSpace I (u z)}
    (hχ : Continuous fun q : (ℝ × ℝ) × G ↦ (⟨u q.1, χ q.1 q.2⟩ : TangentBundle I M))
    (hχJ : ∀ z v, χ z (Complex.I • v) = J.toContMDiff 0 (u z) (χ z v))
    (hχ₀ : ∀ s t : ℝ, s ∈ Icc 0 1 → t ∈ Icc 0 1 → (s = 1 ∨ t = 0 ∨ t = 1) → ∀ v,
      χ (s, t) v = χ (1, 0) v) :
    (Continuous fun q : (ℝ × ℝ) × G ↦
      TotalSpace.mk' G (u q.1) ((J.toContMDiff 0).complexFrame (χ q.1) (hχJ q.1) q.2)) ∧
    ∃ φ₀ : G ≃L[ℂ] (J.toContMDiff 0).toContinuousComplexStructure.Fiber x,
      ∀ s t : ℝ, s ∈ Icc 0 1 → t ∈ Icc 0 1 → (s = 1 ∨ t = 0 ∨ t = 1) → ∀ v,
        TotalSpace.mk' G (u (s, t)) ((J.toContMDiff 0).complexFrame (χ (s, t)) (hχJ (s, t)) v) =
          TotalSpace.mk' G x (φ₀ v) := by
  set Jc := (J.toContMDiff 0).toContinuousComplexStructure
  have hx₀ : u (1, 0) = x := by simpa using hu.apply_one 0
  refine ⟨((Jc.totalSpaceHomeomorph G).symm.continuous.comp hχ).congr fun q ↦ ?_,
    ((J.toContMDiff 0).complexFrame (χ (1, 0)) (hχJ (1, 0))).trans (fiberCast hx₀),
    fun s t hs ht hst v ↦ ?_⟩
  · -- The complex frame is `χ` followed by the identification of `TM` with the fibres of `Jc`.
    rw [Function.comp_apply, Bundle.ContinuousComplexStructure.totalSpaceHomeomorph_symm_apply,
      ContMDiffAlmostComplexStructure.complexFrame_apply]
  · rw [ContinuousLinearEquiv.trans_apply, mk_fiberCast]
    refine (Jc.totalSpaceHomeomorph G).injective ?_
    rw [ContMDiffAlmostComplexStructure.totalSpaceHomeomorph_mk_complexFrame,
      ContMDiffAlmostComplexStructure.totalSpaceHomeomorph_mk_complexFrame, hχ₀ s t hs ht hst v]
    -- The tangent spaces are all the model space, so equal points carry the same vectors.
    exact TotalSpace.ext ((hu.apply_eq_of_edge hs ht hst).trans hx₀.symm) HEq.rfl

/-- **The first Chern number of the sphere bounded by two smooth caps.** Let `u` and `u'` be
smooth based caps of a loop `γ` at `x`, in a manifold with a fiberwise nondegenerate two-form `σ`
taming an almost complex structure `J`. Let `χ` and `χ'` be real frames of the tangent bundle along
`u` and `u'`, continuous into the tangent bundle, complex linear for `J`, and constant on the three
edges `s = 1`, `t = 0`, `t = 1` of the unit square, where the caps are at `x`. Along `γ` they
differ by a family `k` of complex-linear automorphisms of the model (necessarily a continuous
loop), `χ (0, t) = χ' (0, t) ∘ k t`. Then for every continuous lift `θ` of the normalized complex
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
  have hJ₀ {b : M} (w : TangentSpace I b) : J b w = J.toContMDiff 0 b w :=
    (J.toContMDiff_apply 0 b w).symm
  have hχJc (z : ℝ × ℝ) (v : G) := (hχJ z v).trans (hJ₀ _)
  have hχJc' (z : ℝ × ℝ) (v : G) := (hχJ' z v).trans (hJ₀ _)
  obtain ⟨hφ, φ₀, hφ₀⟩ := hu.complexFrame_of_eq_on_edges hχ hχJc hχ₀
  obtain ⟨hφ', φ₀', hφ₀'⟩ := hu'.complexFrame_of_eq_on_edges hχ' hχJc' hχ₀'
  have hseam := hu.apply_zero_eq_apply_zero hu'
  refine clutchingNumber_mul_two_pi_eq_of_rectangleTrans hseam hp
    (φ := fun z ↦ (J.toContMDiff 0).complexFrame (χ z) (hχJc z))
    (φ' := fun z ↦ (J.toContMDiff 0).complexFrame (χ' z) (hχJc' z)) hφ hφ' hφ₀ hφ₀' (k := k)
    (fun t v ↦ ?_) hθ hθk
  refine ((J.toContMDiff 0).toContinuousComplexStructure.totalSpaceHomeomorph G).injective ?_
  rw [ContMDiffAlmostComplexStructure.totalSpaceHomeomorph_mk_complexFrame,
    ContMDiffAlmostComplexStructure.totalSpaceHomeomorph_mk_complexFrame, hχk t v]
  exact TotalSpace.ext (hseam t) HEq.rfl

/-! ### Frames over a cap that are constant on its edges at the base point -/

/-- A retraction of the plane onto the three edges `s = 1`, `t = 0`, `t = 1` of the unit square:
clamp to the square, then apply, in the coordinates `(1 - s, t)`, a retraction of the cylinder
`I × I` onto `{0} × I ∪ I × {0, 1}` given by the homotopy extension property of `{0, 1}`. -/
private theorem exists_capEdgeRetraction :
    ∃ ρ : ℝ × ℝ → ℝ × ℝ, Continuous ρ ∧
      (∀ z, (ρ z).1 ∈ Icc (0 : ℝ) 1 ∧ (ρ z).2 ∈ Icc (0 : ℝ) 1 ∧
        ((ρ z).1 = 1 ∨ (ρ z).2 = 0 ∨ (ρ z).2 = 1)) ∧
      ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → (s = 1 ∨ t = 0 ∨ t = 1) →
        ρ (s, t) = (s, t) := by
  obtain ⟨r, hr, hr'⟩ := hasHomotopyExtensionProperty_zero_one.exists_retraction
  -- The point of the cylinder `I × I` with coordinates `(1 - s, t)` after clamping.
  let q : ℝ × ℝ → unitInterval × unitInterval := fun z ↦
    (unitInterval.symm (projIcc 0 1 zero_le_one z.1), projIcc 0 1 zero_le_one z.2)
  have hq : Continuous q := by
    fun_prop (disch := exact zero_le_one)
  refine ⟨fun z ↦ (1 - ((r (q z)).1 : ℝ), ((r (q z)).2 : ℝ)),
    by fun_prop, fun z ↦ ?_, fun s t hs ht hst ↦ ?_⟩
  · refine ⟨⟨by linarith [unitInterval.le_one (r (q z)).1],
      by linarith [unitInterval.nonneg (r (q z)).1]⟩, (r (q z)).2.property, ?_⟩
    obtain h | h | h : (r (q z)).1 = 0 ∨ (r (q z)).2 = 0 ∨ (r (q z)).2 = 1 :=
      mem_cylinderExtensionDomain_iff.1 (hr (q z))
    · exact Or.inl (by simp [h])
    · exact Or.inr (Or.inl (by simp [h]))
    · exact Or.inr (Or.inr (by simp [h]))
  · have hqst : q (s, t) = (unitInterval.symm ⟨s, hs⟩, ⟨t, ht⟩) := by
      simp only [q, projIcc_of_mem _ hs, projIcc_of_mem _ ht]
    beta_reduce
    rw [hqst, hr' _ ?_]
    · simp
    rw [mem_cylinderExtensionDomain_iff]
    rcases hst with rfl | rfl | rfl
    · exact Or.inl (Subtype.ext (by simp))
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

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
  obtain ⟨ρ, hρ, hρmem, hρeq⟩ := exists_capEdgeRetraction
  have hcorner : (1 : ℝ) ∈ Icc (0 : ℝ) 1 ∧ (0 : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨⟨zero_le_one, le_rfl⟩, ⟨le_rfl, zero_le_one⟩⟩
  have hρx (z : ℝ × ℝ) : u (ρ z) = u (1, 0) := by
    obtain ⟨h₁, h₂, h₃⟩ := hρmem z
    exact (hu.apply_eq_of_edge h₁ h₂ h₃).trans
      (hu.apply_eq_of_edge hcorner.1 hcorner.2 (Or.inl rfl)).symm
  -- The change of frame from `φ` at the retraction of `z` back to `φ` at the corner `(1, 0)`.
  let A : ℝ × ℝ → G ≃L[ℝ] G := fun z ↦ (φ (1, 0)).trans (φ (ρ z)).symm
  have hA : Continuous fun z ↦ (A z : G →L[ℝ] G) := by
    refine continuous_trans_symm_of_continuous_frame (f := u ∘ ρ) (φ := fun _ ↦ φ (1, 0))
      (ψ := fun z ↦ φ (ρ z)) ?_ (hφ.comp ((hρ.comp continuous_fst).prodMk continuous_snd))
    refine (hφ.comp ((continuous_const (y := ((1, 0) : ℝ × ℝ))).prodMk
      continuous_snd)).congr fun q ↦ ?_
    exact TotalSpace.ext (hρx q.1).symm HEq.rfl
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
      rw [hρeq s t hs ht hst]
      exact (φ (s, t)).apply_symm_apply _
    -- Evaluate the frame `fun z ↦ (A z).trans (φ z)` at the two points.
    change (A (s, t)).trans (φ (s, t)) v = (A (1, 0)).trans (φ (1, 0)) v
    rw [hfix hs ht hst, hfix hcorner.1 hcorner.2 (Or.inl rfl)]

end Symplectic

end TauCeti.Floer

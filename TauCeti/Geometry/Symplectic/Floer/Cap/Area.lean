/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Sphere
public import TauCeti.Geometry.Symplectic.Floer.Cap.Loop
public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Capped

/-!
# The symplectic area of raw caps

Let `M` be a compact boundaryless manifold, `φ` a closed `C¹` two-form on `M`, for instance the
symplectic form of a closed symplectic manifold, and `γ` a loop in `M` based at `x`. The raw caps
of `γ` (`TauCeti.Floer.RawCap γ`) are homotopy classes of continuous discs bounding `γ`, and they
form a torsor under `π₂(M, x)` (`TauCeti.Floer.RawCap.instAddTorsor`). The integral of `φ` over
the classes of `π₂(M, x)` is the homomorphism `TauCeti.sphereIntegralHom`. This file defines the
integral of `φ` over a raw cap and proves that it obeys the recapping law for this homomorphism.

A **smooth based homotopy** from a loop `γ₀` to a loop `γ₁`
(`TauCeti.Floer.IsSmoothBasedHomotopy`) is a smooth map `u : ℝ × ℝ → M`, `1`-periodic in `t`,
with `u (0, t) = γ₀ t`, `u (1, t) = γ₁ t` and `u (s, 0) = x` for `s, t ∈ [0, 1]`: a cylinder from
`γ₀` to `γ₁` swept out through loops based at `x`. Its homotopy class
`IsSmoothBasedHomotopy.homotopyClass` is the class of the path `s ↦ u (s, ·)` in the loop space.
Periodicity makes the edges of smooth based homotopies along a common loop agree on the whole
line, so that they glue smoothly: the concatenation `TauCeti.rectangleTrans` of two smooth based
homotopies is again one (`TauCeti.Floer.IsSmoothBasedHomotopy.trans`), and its homotopy class is
the composite of their classes (`TauCeti.Floer.IsSmoothBasedHomotopy.homotopyClass_trans`). A
**smooth based cap** of `γ` (`TauCeti.Floer.IsSmoothBasedCap`) is a smooth based homotopy from
`γ` to the constant loop: a disc bounding `γ`, swept out from `γ` at `s = 0` to its centre at
`s = 1`. Its homotopy class is a raw cap of `γ`.

* **Two smooth caps differ by the sphere they bound.** For two smooth based caps `u` and `u'` of
  `γ`, the sphere `u'.homotopyClass -ᵥ u.homotopyClass` is represented by the concatenation of
  `u` run backwards and `u'`
  (`TauCeti.Floer.IsSmoothBasedCap.homotopyClass_vsub_homotopyClass_toMul`), which is smooth
  after the reparametrization of `TauCeti.rectangleTrans`
  (`TauCeti.Floer.IsSmoothBasedCap.contMDiff_rectangleTrans`). So the integral of `φ` over this
  sphere is `∫ u'^* φ - ∫ u^* φ`, the integrals being over the unit square
  (`TauCeti.Floer.IsSmoothBasedCap.sphereIntegral_homotopyClass_vsub_homotopyClass`), by
  `TauCeti.sphereIntegral_mk_of_contMDiff`.
* **The area of a raw cap.** If `γ` has a smooth based cap `u₀` (witnessing `h`), the area of a
  raw cap `D` is `RawCap.area φ h D = ∫ u₀^* φ + ∫_{D -ᵥ [u₀]} φ`. The area is only defined for
  loops with a smooth based cap. It does not depend on `u₀`: the area of the raw cap of every
  smooth based cap `u` is `∫ u^* φ` (`TauCeti.Floer.RawCap.area_homotopyClass`).
* **The recapping law.** Gluing a sphere `a ∈ π₂(M, x)` to a raw cap adds the integral of `φ` over
  `a` to its area, `area (a +ᵥ D) = ∫_a φ + area D` (`TauCeti.Floer.RawCap.area_vadd`), and the
  areas of two raw caps differ by the integral over the sphere by which they differ
  (`TauCeti.Floer.RawCap.area_sub_area`).
* **Gluing a cylinder.** Gluing a smooth based homotopy `w` from `γ₀` to `γ` to a raw cap `D` of
  `γ` gives a raw cap of `γ₀` of area `∫ w^* φ + area D` (`TauCeti.Floer.RawCap.area_comp`).

The recapping law is the hypothesis of `TauCeti.Floer.CapClass.lift`, with the area homomorphism
`TauCeti.sphereIntegralHom` on the group `π₂(M, x)` of spheres. The area is measured with the cap
oriented from `γ` to its centre, as for `TauCeti.capArea`; the capped action
`TauCeti.cappedLoopAction` uses the disc oriented from its centre to `γ`, so for a smooth based cap
`hu : IsSmoothBasedCap I γ u` its area term is `-RawCap.area φ h hu.homotopyClass`
(`TauCeti.Floer.IsSmoothBasedCap.cappedLoopAction_comp_prodMap_one_sub`).

## Main definitions

* `TauCeti.Floer.IsSmoothBasedHomotopy I γ₀ γ₁ u`: `u` is a smooth based homotopy from `γ₀` to
  `γ₁`.
* `TauCeti.Floer.IsSmoothBasedCap I γ u`: `u` is a smooth based cap of `γ`.
* `TauCeti.Floer.IsSmoothBasedHomotopy.homotopyClass`: the homotopy class of a smooth based
  homotopy, the raw cap of a smooth based cap.
* `TauCeti.Floer.RawCap.area φ h D`: the integral of `φ` over a raw cap `D` of a loop with a
  smooth based cap (`h`).

## Main results

* `TauCeti.Floer.IsSmoothBasedHomotopy.trans`,
  `TauCeti.Floer.IsSmoothBasedHomotopy.homotopyClass_trans`: concatenation of smooth based
  homotopies.
* `TauCeti.Floer.IsSmoothBasedCap.homotopyClass_vsub_homotopyClass_toMul`: two smooth based caps
  differ by the sphere represented by their concatenation.
* `TauCeti.Floer.IsSmoothBasedCap.sphereIntegral_homotopyClass_vsub_homotopyClass`: two smooth
  based caps differ by a sphere whose integral is the difference of their integrals.
* `TauCeti.Floer.RawCap.area_homotopyClass`: the area of the raw cap of a smooth based cap is its
  integral.
* `TauCeti.Floer.RawCap.area_vadd`: the recapping law.
* `TauCeti.Floer.RawCap.area_sub_area`: two raw caps have areas differing by the integral over the
  sphere by which they differ.
* `TauCeti.Floer.RawCap.area_comp`: the area of a raw cap with a smooth cylinder glued to it.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, on the action of capped loops and its recapping law.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  Section 11.1 (the symplectic area of spherical classes and capped loops).
-/

public section

noncomputable section

open Set CategoryTheory HomotopyGroup
open scoped Manifold ContDiff Topology Topology.Homotopy

namespace TauCeti.Floer

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {x : M} {γ : Ω M x}

/-! ### Smooth based homotopies and smooth based caps -/

omit [TopologicalSpace M] in
/-- Two `1`-periodic functions that agree on the unit interval agree everywhere. -/
private theorem eq_of_periodic_of_eqOn {f g : ℝ → M} (hf : Function.Periodic f 1)
    (hg : Function.Periodic g 1) (h : ∀ t : unitInterval, f t = g t) (t : ℝ) : f t = g t := by
  have ht : t - ⌊t⌋ * 1 ∈ unitInterval := by
    rw [mul_one, ← Int.fract]
    exact ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  rw [← hf.sub_int_mul_eq ⌊t⌋, ← hg.sub_int_mul_eq ⌊t⌋]
  exact h ⟨_, ht⟩

variable (I) in
/-- A **smooth based homotopy** from a loop `γ₀` to a loop `γ₁`, both based at `x`: a smooth map
`u : ℝ × ℝ → M`, `1`-periodic in its second coordinate, which runs along `γ₀` for `s = 0` and
along `γ₁` for `s = 1`, and sends the edge `t = 0` of the unit square to `x`. The loops
`u (s, ·)` are based at `x`, so `s ↦ u (s, ·)` is a path in the loop space from `γ₀` to `γ₁`: a
cylinder from `γ₀` to `γ₁` whose seam stays at `x`. Periodicity makes `u (0, ·)` and `u (1, ·)`
the periodic extensions of `γ₀` and `γ₁`, which is how the one-periodic orbits of a Hamiltonian
are parametrized. -/
structure IsSmoothBasedHomotopy (γ₀ γ₁ : Ω M x) (u : ℝ × ℝ → M) : Prop where
  /-- A smooth based homotopy is smooth. -/
  contMDiff : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u
  /-- A smooth based homotopy is `1`-periodic in its second coordinate. -/
  apply_add_one : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z
  /-- A smooth based homotopy starts at the first loop. -/
  apply_zero : ∀ t : unitInterval, u (0, t) = γ₀ t
  /-- A smooth based homotopy ends at the second loop. -/
  apply_one : ∀ t : unitInterval, u (1, t) = γ₁ t
  /-- The seam `t = 0` stays at the base point. -/
  apply_seam : ∀ s : unitInterval, u (s, 0) = x

variable (I) in
/-- A **smooth based cap** of a loop `γ` based at `x`: a smooth based homotopy from `γ` to the
constant loop. It is a smooth map `u : ℝ × ℝ → M`, `1`-periodic in its second coordinate, which
starts at `γ` for `s = 0`, ends at `x` for `s = 1`, and sends the edge `t = 0` of the unit square
to `x`, so `s ↦ u (s, ·)` is a disc bounding `γ` with its centre at `s = 1`. -/
abbrev IsSmoothBasedCap (γ : Ω M x) (u : ℝ × ℝ → M) : Prop :=
  IsSmoothBasedHomotopy I γ (Path.refl x) u

/-- The constant map is a smooth based cap of the constant loop. -/
theorem isSmoothBasedCap_refl (x : M) : IsSmoothBasedCap I (Path.refl x) fun _ ↦ x :=
  ⟨contMDiff_const, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- The reparametrization of the unit interval under which the concatenation of two paths in the
loop space given by maps `u₁` and `u₂` becomes the concatenation `TauCeti.rectangleTrans u₁ u₂`. -/
private def concatReparam (s : ℝ) : ℝ :=
  if s ≤ 1 / 2 then Real.smoothTransition (3 * s) / 2
  else (1 + Real.smoothTransition (3 * s - 2)) / 2

private theorem concatReparam_of_le {s : ℝ} (hs : s ≤ 1 / 2) :
    concatReparam s = Real.smoothTransition (3 * s) / 2 := by
  simp only [concatReparam, hs, ↓reduceIte]

private theorem concatReparam_of_lt {s : ℝ} (hs : 1 / 2 < s) :
    concatReparam s = (1 + Real.smoothTransition (3 * s - 2)) / 2 := by
  simp only [concatReparam, hs.not_ge, ↓reduceIte]

private theorem continuous_concatReparam : Continuous concatReparam := by
  refine Continuous.if_le (by fun_prop (disch := exact Real.smoothTransition.continuous))
    (by fun_prop (disch := exact Real.smoothTransition.continuous)) continuous_id
    continuous_const fun s hs ↦ ?_
  rw [hs, Real.smoothTransition.one_of_one_le (by norm_num),
    Real.smoothTransition.zero_of_nonpos (by norm_num)]
  norm_num

private theorem concatReparam_mem (s : ℝ) : concatReparam s ∈ unitInterval := by
  have h₀ := Real.smoothTransition.nonneg (3 * s)
  have h₁ := Real.smoothTransition.le_one (3 * s)
  have h₂ := Real.smoothTransition.nonneg (3 * s - 2)
  have h₃ := Real.smoothTransition.le_one (3 * s - 2)
  rcases le_or_gt s (1 / 2) with hs | hs
  · rw [concatReparam_of_le hs]
    constructor <;> linarith
  · rw [concatReparam_of_lt hs]
    constructor <;> linarith

/-- The reparametrization of the unit interval as a map of the unit interval. -/
private def concatReparamI (s : unitInterval) : unitInterval :=
  ⟨concatReparam s, concatReparam_mem s⟩

private theorem coe_concatReparamI (s : unitInterval) :
    (concatReparamI s : ℝ) = concatReparam s :=
  (rfl)

private theorem continuous_concatReparamI : Continuous concatReparamI :=
  (continuous_concatReparam.comp continuous_subtype_val).subtype_mk _

private theorem concatReparamI_zero : concatReparamI 0 = 0 :=
  Subtype.ext <| by
    rw [coe_concatReparamI, Icc.coe_zero, concatReparam_of_le (by norm_num), mul_zero,
      Real.smoothTransition.zero, zero_div]

private theorem concatReparamI_one : concatReparamI 1 = 1 :=
  Subtype.ext <| by
    rw [coe_concatReparamI, Icc.coe_one, concatReparam_of_lt (by norm_num),
      Real.smoothTransition.one_of_one_le (by norm_num)]
    norm_num

namespace IsSmoothBasedHomotopy

variable {γ₀ γ₁ γ₂ γ₁' : Ω M x} {u u' : ℝ × ℝ → M}

/-- The edge `t = 1` of a smooth based homotopy stays at the base point. -/
theorem apply_seam_one (hu : IsSmoothBasedHomotopy I γ₀ γ₁ u) (s : unitInterval) :
    u (s, 1) = x := by
  simpa using (hu.apply_add_one (s, 0)).trans (hu.apply_seam s)

/-- Two smooth based homotopies from the same loop agree along the whole line `s = 0`, where both
are the periodic extension of the loop. -/
theorem apply_zero_eq_apply_zero (hu : IsSmoothBasedHomotopy I γ₀ γ₁ u)
    (hu' : IsSmoothBasedHomotopy I γ₀ γ₁' u') (t : ℝ) : u (0, t) = u' (0, t) :=
  eq_of_periodic_of_eqOn (f := fun t ↦ u (0, t)) (g := fun t ↦ u' (0, t))
    (fun t ↦ hu.apply_add_one (0, t)) (fun t ↦ hu'.apply_add_one (0, t))
    (fun t ↦ (hu.apply_zero t).trans (hu'.apply_zero t).symm) t

/-- A smooth based homotopy ending at a loop agrees along the whole line `s = 1` with a smooth
based homotopy starting at it, the periodic extension of the loop along which they meet. -/
theorem apply_one_eq_apply_zero (hu : IsSmoothBasedHomotopy I γ₀ γ₁ u)
    (hu' : IsSmoothBasedHomotopy I γ₁ γ₂ u') (t : ℝ) : u (1, t) = u' (0, t) :=
  eq_of_periodic_of_eqOn (f := fun t ↦ u (1, t)) (g := fun t ↦ u' (0, t))
    (fun t ↦ hu.apply_add_one (1, t)) (fun t ↦ hu'.apply_add_one (0, t))
    (fun t ↦ (hu.apply_one t).trans (hu'.apply_zero t).symm) t

/-- The path `s ↦ u (s, ·)` in the loop space of a smooth based homotopy `u` from `γ₀` to
`γ₁`. -/
def toPath (hu : IsSmoothBasedHomotopy I γ₀ γ₁ u) : Path γ₀ γ₁ where
  toFun s := ⟨⟨fun t ↦ u (s, t),
    hu.contMDiff.continuous.comp (continuous_const.prodMk continuous_subtype_val)⟩,
    hu.apply_seam s, hu.apply_seam_one s⟩
  continuous_toFun := Path.continuous_uncurry_iff.1 <|
    hu.contMDiff.continuous.comp (by fun_prop)
  source' := Path.ext <| funext hu.apply_zero
  target' := Path.ext <| funext hu.apply_one

@[simp]
theorem toPath_apply (hu : IsSmoothBasedHomotopy I γ₀ γ₁ u) (s t : unitInterval) :
    hu.toPath s t = u (s, t) :=
  (rfl)

/-- The homotopy class of a smooth based homotopy from `γ₀` to `γ₁`: the class of its path in the
loop space, a morphism of the fundamental groupoid of the loop space. For a smooth based cap of
`γ` it is a raw cap of `γ`. -/
def homotopyClass (hu : IsSmoothBasedHomotopy I γ₀ γ₁ u) :
    (⟨γ₀⟩ : FundamentalGroupoid (Ω M x)) ⟶ ⟨γ₁⟩ :=
  Path.Homotopic.Quotient.mk hu.toPath

theorem homotopyClass_def (hu : IsSmoothBasedHomotopy I γ₀ γ₁ u) :
    hu.homotopyClass = Path.Homotopic.Quotient.mk hu.toPath :=
  (rfl)

/-- The concatenation of two paths `P₁` and `P₂` in the loop space, reparametrized by
`concatReparamI`, is the concatenation `rectangleTrans u₁ u₂` on the unit square of maps `u₁`
and `u₂` representing them there, when `u₁` ends where `u₂` starts. -/
private theorem trans_reparam_apply {γ₀ γ₁ γ₂ : Ω M x} {P₁ : Path γ₀ γ₁} {P₂ : Path γ₁ γ₂}
    {u₁ u₂ : ℝ × ℝ → M} (h₁ : ∀ s t : unitInterval, P₁ s t = u₁ (s, t))
    (h₂ : ∀ s t : unitInterval, P₂ s t = u₂ (s, t)) (h : ∀ t, u₁ (1, t) = u₂ (0, t))
    (s t : unitInterval) :
    (P₁.trans P₂).reparam concatReparamI continuous_concatReparamI concatReparamI_zero
        concatReparamI_one s t = rectangleTrans u₁ u₂ ((s : ℝ), (t : ℝ)) := by
  have hβ₀ := Real.smoothTransition.nonneg (3 * (s : ℝ) - 2)
  have hβ₁ := Real.smoothTransition.le_one (3 * (s : ℝ))
  rw [Path.coe_reparam, Function.comp_apply, Path.trans_apply]
  rcases le_or_gt (s : ℝ) (1 / 2) with hs | hs
  · -- First half: `P₁`.
    have hc : (concatReparamI s : ℝ) ≤ 1 / 2 := by
      rw [coe_concatReparamI, concatReparam_of_le hs]
      linarith
    rw [dite_eq_left hc, rectangleTrans_eq_left h (by simp only; linarith), h₁]
    simp only [coe_concatReparamI, concatReparam_of_le hs, Function.comp_apply, Prod.map_apply,
      id_eq]
    congr 2
    ring
  · rw [rectangleTrans_eq_right h (by simp only; linarith)]
    simp only [Function.comp_apply, Prod.map_apply, id_eq]
    split_ifs with hc
    · -- Second half, while the concatenation rests at `γ₁`.
      rw [coe_concatReparamI, concatReparam_of_lt hs] at hc
      have hz : Real.smoothTransition (3 * (s : ℝ) - 2) = 0 := by linarith
      rw [h₁, hz, ← h]
      simp only [coe_concatReparamI, concatReparam_of_lt hs, hz]
      norm_num
    · -- Second half: `P₂`.
      rw [h₂]
      simp only [coe_concatReparamI, concatReparam_of_lt hs]
      congr 2
      ring

/-- The concatenation `rectangleTrans u u'` of a smooth based homotopy `u` from `γ₀` to `γ₁`
and a smooth based homotopy `u'` from `γ₁` to `γ₂` is a smooth based homotopy from `γ₀` to
`γ₂`. -/
theorem trans (hu : IsSmoothBasedHomotopy I γ₀ γ₁ u) (hu' : IsSmoothBasedHomotopy I γ₁ γ₂ u') :
    IsSmoothBasedHomotopy I γ₀ γ₂ (rectangleTrans u u') where
  contMDiff := contMDiff_rectangleTrans hu.contMDiff hu'.contMDiff (hu.apply_one_eq_apply_zero hu')
  apply_add_one := rectangleTrans_apply_add_snd hu.apply_add_one hu'.apply_add_one
  apply_zero t := by rw [rectangleTrans_apply_zero, hu.apply_zero]
  apply_one t := by rw [rectangleTrans_apply_one, hu'.apply_one]
  apply_seam s := by
    have hβ (r : ℝ) : Real.smoothTransition r ∈ unitInterval :=
      ⟨Real.smoothTransition.nonneg r, Real.smoothTransition.le_one r⟩
    rcases lt_or_ge (s : ℝ) (2 / 3) with hs | hs
    · rw [rectangleTrans_eq_left (hu.apply_one_eq_apply_zero hu') hs]
      exact hu.apply_seam ⟨_, hβ _⟩
    · rw [rectangleTrans_eq_right (hu.apply_one_eq_apply_zero hu') (by simp only; linarith)]
      exact hu'.apply_seam ⟨_, hβ _⟩

/-- The homotopy class of the concatenation of two smooth based homotopies is the composite of
their homotopy classes in the fundamental groupoid of the loop space. -/
theorem homotopyClass_trans (hu : IsSmoothBasedHomotopy I γ₀ γ₁ u)
    (hu' : IsSmoothBasedHomotopy I γ₁ γ₂ u') :
    (hu.trans hu').homotopyClass = hu.homotopyClass ≫ hu'.homotopyClass := by
  have hpath : (hu.trans hu').toPath = (hu.toPath.trans hu'.toPath).reparam concatReparamI
      continuous_concatReparamI concatReparamI_zero concatReparamI_one :=
    Path.ext <| funext fun s ↦ Path.ext <| funext fun t ↦
      (trans_reparam_apply (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (hu.apply_one_eq_apply_zero hu')
        s t).symm
  calc Path.Homotopic.Quotient.mk (hu.trans hu').toPath
      = Path.Homotopic.Quotient.mk (hu.toPath.trans hu'.toPath) := by
        rw [hpath]
        exact Eq.symm (Quotient.sound ⟨Path.Homotopy.reparam _ _ _ _ _⟩)
    _ = hu.homotopyClass ≫ hu'.homotopyClass := rfl

end IsSmoothBasedHomotopy

namespace IsSmoothBasedCap

variable {u u' : ℝ × ℝ → M}

/-- The double loop of two smooth based caps, reparametrized by `concatReparamI`, is their
concatenation `rectangleTrans` on the unit square. -/
private theorem symm_trans_reparam_apply (hu : IsSmoothBasedCap I γ u)
    (hu' : IsSmoothBasedCap I γ u') (s t : unitInterval) :
    (hu.toPath.symm.trans hu'.toPath).reparam concatReparamI continuous_concatReparamI
        concatReparamI_zero concatReparamI_one s t =
      rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u' ((s : ℝ), (t : ℝ)) :=
  IsSmoothBasedHomotopy.trans_reparam_apply
    (fun s t ↦ by simp [Path.symm_apply, unitInterval.coe_symm_eq])
    (fun _ _ ↦ rfl) (fun t ↦ by simpa using hu.apply_zero_eq_apply_zero hu' t) s t

/-- The generalized loop of the reparametrized double loop of two smooth based caps restricts their
concatenation `rectangleTrans` to the unit square. -/
private theorem fromDoubleLoop_trans_reparam_apply (hu : IsSmoothBasedCap I γ u)
    (hu' : IsSmoothBasedCap I γ u') (y : Fin 2 → unitInterval) :
    GenLoop.fromDoubleLoop ((hu.toPath.symm.trans hu'.toPath).reparam concatReparamI
        continuous_concatReparamI concatReparamI_zero concatReparamI_one) y =
      rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u' ((y 0 : ℝ), (y 1 : ℝ)) := by
  rw [GenLoop.fromDoubleLoop_apply, symm_trans_reparam_apply hu hu']

/-- The concatenation `rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u'` of two smooth based
caps `u` and `u'` of the same loop, `u` run backwards followed by `u'`, is smooth. -/
theorem contMDiff_rectangleTrans (hu : IsSmoothBasedCap I γ u) (hu' : IsSmoothBasedCap I γ u') :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u') :=
  _root_.TauCeti.contMDiff_rectangleTrans (n := ⊤)
    (hu.contMDiff.comp ((contDiff_const.sub contDiff_id).prodMap contDiff_id).contMDiff)
    hu'.contMDiff fun t ↦ by simpa using hu.apply_zero_eq_apply_zero hu' t

/-- **The sphere bounded by two smooth caps.** For smooth based caps `u` and `u'` of the same loop,
the sphere by which their raw caps differ is the class of any generalized loop restricting their
concatenation `rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u'`, `u` run backwards followed
by `u'`, to the unit square. This concatenation is smooth (`contMDiff_rectangleTrans`). -/
theorem homotopyClass_vsub_homotopyClass_toMul (hu : IsSmoothBasedCap I γ u)
    (hu' : IsSmoothBasedCap I γ u') {p : Ω^ (Fin 2) M x}
    (hp : ∀ y, p y = rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u' ((y 0 : ℝ), (y 1 : ℝ))) :
    (hu'.homotopyClass -ᵥ hu.homotopyClass).toMul = ⟦p⟧ := by
  set β := hu.toPath.symm.trans hu'.toPath
  -- The sphere is the class of the double loop `β`: `u` run backwards, then `u'`.
  have hβ : hu'.homotopyClass -ᵥ hu.homotopyClass =
      .ofMul (fundamentalGroupLoopSpaceMulEquiv
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk β))) := by
    -- In the fundamental groupoid, `inv ⟦P⟧ ≫ ⟦P'⟧` is `⟦P.symm.trans P'⟧` by definition of
    -- its inverse and composition.
    rw [RawCap.vsub_def]
    rfl
  -- Reparametrizing `β` does not change its class, and makes it the smooth concatenation.
  have hrep : Path.Homotopic.Quotient.mk β = Path.Homotopic.Quotient.mk
      (β.reparam concatReparamI continuous_concatReparamI concatReparamI_zero
        concatReparamI_one) :=
    Quotient.sound ⟨Path.Homotopy.reparam β _ _ _ _⟩
  rw [hβ, toMul_ofMul, hrep, fundamentalGroupLoopSpaceMulEquiv_fromPath_mk]
  exact congrArg _ <| GenLoop.ext _ _ fun y ↦
    (fromDoubleLoop_trans_reparam_apply hu hu' y).trans (hp y).symm

/-- **Two smooth caps differ by the sphere they bound.** For smooth based caps `u` and `u'` of the
same loop, the integral of a closed `C¹` two-form over the sphere by which their raw caps differ
is the difference of their integrals over the unit square. -/
theorem sphereIntegral_homotopyClass_vsub_homotopyClass [FiniteDimensional ℝ E] [I.Boundaryless]
    [IsManifold I ∞ M] [CompactSpace M] [T2Space M] {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) (hu : IsSmoothBasedCap I γ u)
    (hu' : IsSmoothBasedCap I γ u') :
    sphereIntegral φ x (hu'.homotopyClass -ᵥ hu.homotopyClass).toMul =
      rectangleIntegral φ u' (0, 0) (1, 1) - rectangleIntegral φ u (0, 0) (1, 1) := by
  rw [hu.homotopyClass_vsub_homotopyClass_toMul hu' (fromDoubleLoop_trans_reparam_apply hu hu'),
    sphereIntegral_mk_of_contMDiff hφ hdφ (hu.contMDiff_rectangleTrans hu')
      (fromDoubleLoop_trans_reparam_apply hu hu'),
    rectangleIntegral_rectangleTrans_comp_prodMap_one_sub (hφ.of_le (by simp))
      (hu.contMDiff.of_le (by simp)) (hu'.contMDiff.of_le (by simp))
      (hu.apply_zero_eq_apply_zero hu')]

end IsSmoothBasedCap

/-! ### The area of a raw cap -/

section Area

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  {φ : RoughForm I M F 2}

/-- The **area** of a raw cap `D` of a loop `γ` with a smooth based cap `u₀`, for a two-form `φ`:
the integral of `φ` over `u₀` plus its integral over the sphere `D -ᵥ u₀.homotopyClass` by which
`D` differs from the raw cap of `u₀`. It is defined only for loops that have a smooth based cap.
For a closed `C¹` form it is the integral over the raw cap of any smooth based cap
(`TauCeti.Floer.RawCap.area_homotopyClass`), so it does not depend on `u₀`. The cap is oriented
from `γ` to its centre. -/
def RawCap.area (φ : RoughForm I M F 2) (h : ∃ u, IsSmoothBasedCap I γ u) (D : RawCap γ) : F :=
  rectangleIntegral φ h.choose (0, 0) (1, 1) +
    sphereIntegral φ x (D -ᵥ h.choose_spec.homotopyClass).toMul

/-- The defining equation of `TauCeti.Floer.RawCap.area`, for an arbitrary two-form. -/
theorem RawCap.area_def (φ : RoughForm I M F 2) (h : ∃ u, IsSmoothBasedCap I γ u)
    (D : RawCap γ) :
    RawCap.area φ h D = rectangleIntegral φ h.choose (0, 0) (1, 1) +
      sphereIntegral φ x (D -ᵥ h.choose_spec.homotopyClass).toMul :=
  (rfl)

/-- **The area of a smooth cap.** For a closed `C¹` two-form, the area of the raw cap of a smooth
based cap `u` is the integral of the form over `u` on the unit square. -/
theorem RawCap.area_homotopyClass (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0)
    (h : ∃ u, IsSmoothBasedCap I γ u) {u : ℝ × ℝ → M} (hu : IsSmoothBasedCap I γ u) :
    RawCap.area φ h hu.homotopyClass = rectangleIntegral φ u (0, 0) (1, 1) := by
  rw [RawCap.area_def,
    h.choose_spec.sphereIntegral_homotopyClass_vsub_homotopyClass hφ hdφ hu, add_sub_cancel]

/-- **The recapping law.** If `γ` has a smooth based cap, gluing a sphere `a ∈ π₂(M, x)` to a raw
cap of `γ` adds the integral of a closed `C¹` two-form over `a` to the area. -/
theorem RawCap.area_vadd (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0)
    (h : ∃ u, IsSmoothBasedCap I γ u) (a : Additive (π_ 2 M x)) (D : RawCap γ) :
    RawCap.area φ h (a +ᵥ D) = sphereIntegralHom x hφ hdφ a + RawCap.area φ h D := by
  have : Nonempty (RawCap γ) := ⟨D⟩
  rw [RawCap.area_def, RawCap.area_def, vadd_vsub_assoc,
    ← sphereIntegralHom_apply hφ hdφ, ← sphereIntegralHom_apply hφ hdφ, map_add]
  abel

/-- **Two raw caps differ by a sphere.** If `γ` has a smooth based cap, the areas of two raw caps
of `γ` differ by the integral of a closed `C¹` two-form over the sphere by which they differ. -/
theorem RawCap.area_sub_area (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0)
    (h : ∃ u, IsSmoothBasedCap I γ u) (D' D : RawCap γ) :
    RawCap.area φ h D' - RawCap.area φ h D = sphereIntegralHom x hφ hdφ (D' -ᵥ D) := by
  have : Nonempty (RawCap γ) := ⟨D⟩
  conv_lhs => rw [← vsub_vadd D' D, RawCap.area_vadd hφ hdφ h]
  exact add_sub_cancel_right _ _

/-- **Gluing a smooth cylinder to a cap.** Let `w` be a smooth based homotopy from `γ₀` to `γ₁`,
a cylinder whose seam stays at the base point, and suppose that `γ₁` has a smooth based cap.
Gluing `w` to a raw cap `D` of `γ₁` gives the raw cap `[w] ≫ D` of `γ₀`, whose area for a closed
`C¹` two-form is the integral of the form over `w` plus the area of `D`. -/
theorem RawCap.area_comp (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) {γ₀ : Ω M x}
    {w : ℝ × ℝ → M} (hw : IsSmoothBasedHomotopy I γ₀ γ w) (h₀ : ∃ u, IsSmoothBasedCap I γ₀ u)
    (h : ∃ u, IsSmoothBasedCap I γ u) (D : RawCap γ) :
    RawCap.area φ h₀ (hw.homotopyClass ≫ D) =
      rectangleIntegral φ w (0, 0) (1, 1) + RawCap.area φ h D := by
  obtain ⟨u, hu⟩ := id h
  have : Nonempty (RawCap γ) := ⟨D⟩
  rw [← vsub_vadd D hu.homotopyClass, RawCap.comp_vadd, RawCap.area_vadd hφ hdφ,
    RawCap.area_vadd hφ hdφ, ← hw.homotopyClass_trans hu,
    RawCap.area_homotopyClass hφ hdφ h₀ (hw.trans hu), RawCap.area_homotopyClass hφ hdφ h hu,
    rectangleIntegral_rectangleTrans (hφ.of_le (by simp)) (hw.contMDiff.of_le (by simp))
      (hu.contMDiff.of_le (by simp)) (hw.apply_one_eq_apply_zero hu)]
  abel

/-- **The capped action of a smooth cap.** For a smooth based cap `u` of `γ` and a closed real
`C¹` two-form `σ`, the capped action of `γ` with the disc `u` run backwards, from its centre to
`γ`, is minus the area of the raw cap of `u` plus the Hamiltonian term. -/
theorem IsSmoothBasedCap.cappedLoopAction_comp_prodMap_one_sub {σ : RoughForm I M ℝ 2}
    (hσ : IsSmoothForm I 1 σ) (hdσ : mextDeriv σ = 0) (Ham : ℝ → M → ℝ)
    (h : ∃ u, IsSmoothBasedCap I γ u) {u : ℝ × ℝ → M} (hu : IsSmoothBasedCap I γ u) :
    cappedLoopAction σ Ham (fun t ↦ u (0, t)) (u ∘ Prod.map (fun s ↦ 1 - s) id) =
      -RawCap.area σ h hu.homotopyClass + ∫ t in 0..1, Ham t (u (0, t)) := by
  rw [cappedLoopAction_def, rectangleIntegral_comp_prodMap_one_sub (hσ.of_le (by simp))
    (hu.contMDiff.of_le (by simp)), RawCap.area_homotopyClass hσ hdσ h hu]

end Area

end TauCeti.Floer

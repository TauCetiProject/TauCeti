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

A **smooth based cap** of `γ` (`TauCeti.Floer.IsSmoothBasedCap`) is a smooth map
`u : ℝ × ℝ → M`, `1`-periodic in `t`, with `u (0, t) = γ t`, `u (1, t) = x` and `u (s, 0) = x` for
`s, t ∈ [0, 1]`: a disc bounding `γ`, swept out from `γ` at `s = 0` to its centre at `s = 1`
through loops based at `x`. Periodicity makes two smooth based caps of `γ` agree along the whole
line `s = 0`, so that they glue smoothly. A smooth based cap has a raw cap
`IsSmoothBasedCap.rawCap`, the class of the path `s ↦ u (s, ·)` in the loop space.

* **Two smooth caps differ by the sphere they bound.** For two smooth based caps `u` and `u'` of
  `γ`, the integral of `φ` over the sphere `u'.rawCap -ᵥ u.rawCap` is
  `∫ u'^* φ - ∫ u^* φ`, the integrals being over the unit square
  (`TauCeti.Floer.IsSmoothBasedCap.sphereIntegral_rawCap_vsub_rawCap`). The sphere is represented
  by the concatenation of `u` run backwards and `u'`, which is smooth after the reparametrization
  of `TauCeti.rectangleTrans`; its integral is computed by
  `TauCeti.sphereIntegral_mk_of_contMDiff`.
* **The area of a raw cap.** If `γ` has a smooth based cap `u₀` (witnessing `h`), the area of a
  raw cap `D` is `RawCap.area φ h D = ∫ u₀^* φ + ∫_{D -ᵥ u₀.rawCap} φ`. The area is only defined
  for loops with a smooth based cap. It does not depend on `u₀`: the area of the raw cap of every
  smooth based cap `u` is `∫ u^* φ` (`TauCeti.Floer.RawCap.area_rawCap`).
* **The recapping law.** Gluing a sphere `a ∈ π₂(M, x)` to a raw cap adds the integral of `φ` over
  `a` to its area, `area (a +ᵥ D) = ∫_a φ + area D` (`TauCeti.Floer.RawCap.area_vadd`), and the
  areas of two raw caps differ by the integral over the sphere by which they differ
  (`TauCeti.Floer.RawCap.area_sub_area`).

The recapping law is the hypothesis of `TauCeti.Floer.CapClass.lift`, with the area homomorphism
`TauCeti.sphereIntegralHom` on the group `π₂(M, x)` of spheres. The area is measured with the cap
oriented from `γ` to its centre, as for `TauCeti.capArea`; the capped action
`TauCeti.cappedLoopAction` uses the disc oriented from its centre to `γ`, so for a smooth based cap
`hu : IsSmoothBasedCap I γ u` its area term is `-RawCap.area φ ⟨u, hu⟩ hu.rawCap`
(`TauCeti.Floer.IsSmoothBasedCap.cappedLoopAction_comp_prodMap_one_sub`).

## Main definitions

* `TauCeti.Floer.IsSmoothBasedCap I γ u`: `u` is a smooth based cap of `γ`.
* `TauCeti.Floer.IsSmoothBasedCap.rawCap`: the raw cap of a smooth based cap.
* `TauCeti.Floer.RawCap.area φ h D`: the integral of `φ` over a raw cap `D` of a loop with a
  smooth based cap (`h`).

## Main results

* `TauCeti.Floer.IsSmoothBasedCap.sphereIntegral_rawCap_vsub_rawCap`: two smooth based caps differ
  by a sphere whose integral is the difference of their integrals.
* `TauCeti.Floer.RawCap.area_rawCap`: the area of the raw cap of a smooth based cap is its
  integral.
* `TauCeti.Floer.RawCap.area_vadd`: the recapping law.
* `TauCeti.Floer.RawCap.area_sub_area`: two raw caps have areas differing by the integral over the
  sphere by which they differ.

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

/-! ### Smooth based caps -/

variable (I) in
/-- A **smooth based cap** of a loop `γ` based at `x`: a smooth map `u : ℝ × ℝ → M`, `1`-periodic
in its second coordinate, which starts at `γ` for `s = 0`, ends at `x` for `s = 1`, and sends the
edge `t = 0` of the unit square to `x`. The loops `u (s, ·)` are based at `x`, so `s ↦ u (s, ·)`
is a path in the loop space from `γ` to the constant loop, a disc bounding `γ` with its centre at
`s = 1`. Periodicity makes `u (0, ·)` the periodic extension of `γ`, which is how the
one-periodic orbits of a Hamiltonian are parametrized. -/
structure IsSmoothBasedCap (γ : Ω M x) (u : ℝ × ℝ → M) : Prop where
  /-- A smooth based cap is smooth. -/
  contMDiff : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u
  /-- A smooth based cap is `1`-periodic in its second coordinate. -/
  apply_add_one : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z
  /-- A smooth based cap starts at the loop. -/
  apply_zero : ∀ t : unitInterval, u (0, t) = γ t
  /-- A smooth based cap ends at the base point. -/
  apply_one : ∀ t : unitInterval, u (1, t) = x
  /-- The seam `t = 0` stays at the base point. -/
  apply_seam : ∀ s : unitInterval, u (s, 0) = x

/-- The constant map is a smooth based cap of the constant loop. -/
theorem isSmoothBasedCap_refl (x : M) : IsSmoothBasedCap I (Path.refl x) fun _ ↦ x :=
  ⟨contMDiff_const, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩

namespace IsSmoothBasedCap

variable {u u' : ℝ × ℝ → M}

/-- The edge `t = 1` of a smooth based cap stays at the base point. -/
theorem apply_seam_one (hu : IsSmoothBasedCap I γ u) (s : unitInterval) : u (s, 1) = x := by
  simpa using (hu.apply_add_one (s, 0)).trans (hu.apply_seam s)

/-- Two smooth based caps of the same loop agree along the whole line `s = 0`, where both are the
periodic extension of the loop. -/
theorem apply_zero_eq_apply_zero (hu : IsSmoothBasedCap I γ u) (hu' : IsSmoothBasedCap I γ u')
    (t : ℝ) : u (0, t) = u' (0, t) := by
  have hp : Function.Periodic (fun t ↦ u (0, t)) 1 := fun t ↦ hu.apply_add_one (0, t)
  have hp' : Function.Periodic (fun t ↦ u' (0, t)) 1 := fun t ↦ hu'.apply_add_one (0, t)
  have ht : t - ⌊t⌋ * 1 ∈ unitInterval := by
    rw [mul_one, ← Int.fract]
    exact ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  rw [← hp.sub_int_mul_eq ⌊t⌋, ← hp'.sub_int_mul_eq ⌊t⌋]
  exact (hu.apply_zero ⟨_, ht⟩).trans (hu'.apply_zero ⟨_, ht⟩).symm

/-- The path `s ↦ u (s, ·)` in the loop space of a smooth based cap `u`, from `γ` to the constant
loop. -/
def toPath (hu : IsSmoothBasedCap I γ u) : Path γ (Path.refl x) where
  toFun s := ⟨⟨fun t ↦ u (s, t),
    hu.contMDiff.continuous.comp (continuous_const.prodMk continuous_subtype_val)⟩,
    hu.apply_seam s, hu.apply_seam_one s⟩
  continuous_toFun := Path.continuous_uncurry_iff.1 <|
    hu.contMDiff.continuous.comp (by fun_prop)
  source' := Path.ext <| funext hu.apply_zero
  target' := Path.ext <| funext hu.apply_one

@[simp]
theorem toPath_apply (hu : IsSmoothBasedCap I γ u) (s t : unitInterval) :
    hu.toPath s t = u (s, t) :=
  (rfl)

/-- The raw cap of a smooth based cap: the homotopy class of its path in the loop space. -/
def rawCap (hu : IsSmoothBasedCap I γ u) : RawCap γ :=
  Path.Homotopic.Quotient.mk hu.toPath

theorem rawCap_def (hu : IsSmoothBasedCap I γ u) :
    hu.rawCap = Path.Homotopic.Quotient.mk hu.toPath :=
  (rfl)

/-- The reparametrization of the unit interval under which the double loop of two smooth based caps
`u` and `u'`, `u` run backwards followed by `u'`, becomes their concatenation
`TauCeti.rectangleTrans`. -/
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

/-- The double loop of two smooth based caps, reparametrized by `concatReparamI`, is their
concatenation `rectangleTrans` on the unit square. -/
private theorem trans_reparam_apply (hu : IsSmoothBasedCap I γ u)
    (hu' : IsSmoothBasedCap I γ u') (s t : unitInterval) :
    (hu.toPath.symm.trans hu'.toPath).reparam concatReparamI continuous_concatReparamI
        concatReparamI_zero concatReparamI_one s t =
      rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u' ((s : ℝ), (t : ℝ)) := by
  have h (t : ℝ) : (u ∘ Prod.map (fun s ↦ 1 - s) id) (1, t) = u' (0, t) := by
    simpa using hu.apply_zero_eq_apply_zero hu' t
  have hβ₀ := Real.smoothTransition.nonneg (3 * (s : ℝ) - 2)
  have hβ₁ := Real.smoothTransition.le_one (3 * (s : ℝ))
  rw [Path.coe_reparam, Function.comp_apply, Path.trans_apply]
  rcases le_or_gt (s : ℝ) (1 / 2) with hs | hs
  · -- First half: `u` run backwards.
    have hc : (concatReparamI s : ℝ) ≤ 1 / 2 := by
      rw [coe_concatReparamI, concatReparam_of_le hs]
      linarith
    rw [dite_eq_left hc, rectangleTrans_eq_left h (by simp only; linarith)]
    simp only [Path.symm_apply, Function.comp_apply, toPath_apply, unitInterval.coe_symm_eq,
      coe_concatReparamI, concatReparam_of_le hs, Prod.map_apply, id_eq]
    congr 2
    ring
  · rw [rectangleTrans_eq_right h (by simp only; linarith)]
    simp only [Function.comp_apply, Prod.map_apply, id_eq]
    split_ifs with hc
    · -- Second half, while the double loop rests at `γ`.
      rw [coe_concatReparamI, concatReparam_of_lt hs] at hc
      have hz : Real.smoothTransition (3 * (s : ℝ) - 2) = 0 := by linarith
      simp only [Path.symm_apply, Function.comp_apply, toPath_apply, unitInterval.coe_symm_eq,
        coe_concatReparamI, concatReparam_of_lt hs, hz]
      norm_num
      exact hu.apply_zero_eq_apply_zero hu' t
    · -- Second half: `u'`.
      simp only [toPath_apply, coe_concatReparamI, concatReparam_of_lt hs]
      congr 2
      ring

/-- **Two smooth caps differ by the sphere they bound.** For smooth based caps `u` and `u'` of the
same loop, the integral of a closed `C¹` two-form over the sphere by which their raw caps differ
is the difference of their integrals over the unit square. -/
theorem sphereIntegral_rawCap_vsub_rawCap [FiniteDimensional ℝ E] [I.Boundaryless]
    [IsManifold I ∞ M] [CompactSpace M] [T2Space M] {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) (hu : IsSmoothBasedCap I γ u)
    (hu' : IsSmoothBasedCap I γ u') :
    sphereIntegral φ x (hu'.rawCap -ᵥ hu.rawCap).toMul =
      rectangleIntegral φ u' (0, 0) (1, 1) - rectangleIntegral φ u (0, 0) (1, 1) := by
  set β := hu.toPath.symm.trans hu'.toPath
  -- The sphere is the class of the double loop `β`: `u` run backwards, then `u'`.
  have hβ : hu'.rawCap -ᵥ hu.rawCap =
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
  have hsmooth : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞
      (rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u') :=
    contMDiff_rectangleTrans (n := ⊤)
      (hu.contMDiff.comp ((contDiff_const.sub contDiff_id).prodMap contDiff_id).contMDiff)
      hu'.contMDiff fun t ↦ by simpa using hu.apply_zero_eq_apply_zero hu' t
  rw [hβ, toMul_ofMul, hrep, fundamentalGroupLoopSpaceMulEquiv_fromPath_mk,
    sphereIntegral_mk_of_contMDiff hφ hdφ hsmooth fun y ↦ by
      rw [GenLoop.fromDoubleLoop_apply, trans_reparam_apply hu hu'],
    rectangleIntegral_rectangleTrans_comp_prodMap_one_sub (hφ.of_le (by simp))
      (hu.contMDiff.of_le (by simp)) (hu'.contMDiff.of_le (by simp))
      (hu.apply_zero_eq_apply_zero hu')]

end IsSmoothBasedCap

/-! ### The area of a raw cap -/

section Area

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  {φ : RoughForm I M F 2}

/-- The **area** of a raw cap `D` of a loop `γ` with a smooth based cap `u₀`, for a two-form `φ`:
the integral of `φ` over `u₀` plus its integral over the sphere `D -ᵥ u₀.rawCap` by which `D`
differs from the raw cap of `u₀`. It is defined only for loops that have a smooth based cap. For a
closed `C¹` form it is the integral over the raw cap of any smooth based cap
(`TauCeti.Floer.RawCap.area_rawCap`), so it does not depend on `u₀`. The cap is oriented from `γ`
to its centre. -/
def RawCap.area (φ : RoughForm I M F 2) (h : ∃ u, IsSmoothBasedCap I γ u) (D : RawCap γ) : F :=
  rectangleIntegral φ h.choose (0, 0) (1, 1) +
    sphereIntegral φ x (D -ᵥ h.choose_spec.rawCap).toMul

/-- **The area of a smooth cap.** For a closed `C¹` two-form, the area of the raw cap of a smooth
based cap `u` is the integral of the form over `u` on the unit square. -/
theorem RawCap.area_rawCap (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) {u : ℝ × ℝ → M}
    (hu : IsSmoothBasedCap I γ u) :
    RawCap.area φ ⟨u, hu⟩ hu.rawCap = rectangleIntegral φ u (0, 0) (1, 1) := by
  have h : ∃ u, IsSmoothBasedCap I γ u := ⟨u, hu⟩
  rw [RawCap.area, h.choose_spec.sphereIntegral_rawCap_vsub_rawCap hφ hdφ hu, add_sub_cancel]

/-- **The recapping law.** If `γ` has a smooth based cap, gluing a sphere `a ∈ π₂(M, x)` to a raw
cap of `γ` adds the integral of a closed `C¹` two-form over `a` to the area. -/
theorem RawCap.area_vadd (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0)
    (h : ∃ u, IsSmoothBasedCap I γ u) (a : Additive (π_ 2 M x)) (D : RawCap γ) :
    RawCap.area φ h (a +ᵥ D) = sphereIntegralHom x hφ hdφ a + RawCap.area φ h D := by
  have : Nonempty (RawCap γ) := ⟨D⟩
  rw [RawCap.area, RawCap.area, vadd_vsub_assoc,
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

/-- **The capped action of a smooth cap.** For a smooth based cap `u` of `γ` and a closed real
`C¹` two-form `σ`, the capped action of `γ` with the disc `u` run backwards, from its centre to
`γ`, is minus the area of the raw cap of `u` plus the Hamiltonian term. -/
theorem IsSmoothBasedCap.cappedLoopAction_comp_prodMap_one_sub {σ : RoughForm I M ℝ 2}
    (hσ : IsSmoothForm I 1 σ) (hdσ : mextDeriv σ = 0) (Ham : ℝ → M → ℝ) {u : ℝ × ℝ → M}
    (hu : IsSmoothBasedCap I γ u) :
    cappedLoopAction σ Ham (fun t ↦ u (0, t)) (u ∘ Prod.map (fun s ↦ 1 - s) id) =
      -RawCap.area σ ⟨u, hu⟩ hu.rawCap + ∫ t in 0..1, Ham t (u (0, t)) := by
  rw [cappedLoopAction_def, rectangleIntegral_comp_prodMap_one_sub (hσ.of_le (by simp))
    (hu.contMDiff.of_le (by simp)), RawCap.area_rawCap hσ hdσ hu]

end Area

end TauCeti.Floer

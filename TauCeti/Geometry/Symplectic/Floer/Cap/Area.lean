/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Sphere
public import TauCeti.Geometry.Symplectic.Floer.Cap.Loop
public import TauCeti.Geometry.Symplectic.Floer.Cap.PairOfPants
public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Capped
public import TauCeti.Topology.PathSpace.CollaredTrans
import TauCeti.Algebra.Order.ToIntervalMod
import TauCeti.Geometry.Manifold.Instances.Icc
import TauCeti.Topology.Homotopy.Path

/-!
# The symplectic area of raw caps

Let `M` be a compact boundaryless manifold, `φ` a closed `C¹` two-form on `M`, for instance the
symplectic form of a closed symplectic manifold, and `γ` a loop in `M` based at `x`. The raw caps
of `γ` (`TauCeti.Floer.RawCap γ`) are homotopy classes of continuous discs bounding `γ`, and they
form a torsor under `π₂(M, x)` (`TauCeti.Floer.RawCap.instAddTorsor`). The integral of `φ` over
the classes of `π₂(M, x)` is the homomorphism `TauCeti.sphereIntegralHom`. This file defines the
integral of `φ` over a raw cap and proves that it obeys the recapping law for this homomorphism,
and that gluing a smooth cylinder of loops, or a smooth pair of pants, to raw caps adds the
integral of `φ` over the cylinder or the pair of pants.

A **smooth based cap** of `γ` (`TauCeti.Floer.IsSmoothBasedCap`) is a smooth map
`u : ℝ × ℝ → M`, `1`-periodic in `t`, with `u (0, t) = γ t`, `u (1, t) = x` and `u (s, 0) = x` for
`s, t ∈ [0, 1]`: a disc bounding `γ`, swept out from `γ` at `s = 0` to its centre at `s = 1`
through loops based at `x`. Periodicity makes two smooth based caps of `γ` agree along the whole
line `s = 0`, so that they glue smoothly. The raw cap of a smooth based cap `u` is its homotopy
class `IsSmoothBasedHomotopy.homotopyClass`, the class of the path `s ↦ u (s, ·)` in the loop
space.

* **Two smooth caps differ by the sphere they bound.** For two smooth based caps `u` and `u'` of
  `γ`, the sphere `u'.homotopyClass -ᵥ u.homotopyClass` is represented by the concatenation of `u`
  run backwards and `u'`
  (`TauCeti.Floer.IsSmoothBasedCap.homotopyClass_vsub_homotopyClass_toMul`), which is smooth after
  the reparametrization of `TauCeti.rectangleTrans`
  (`TauCeti.Floer.IsSmoothBasedCap.contMDiff_rectangleTrans`). So the integral of `φ` over this
  sphere is `∫ u'^* φ - ∫ u^* φ`, the integrals being over the unit square
  (`TauCeti.Floer.IsSmoothBasedCap.sphereIntegral_homotopyClass_vsub_homotopyClass`), by
  `TauCeti.sphereIntegral_mk_of_contMDiff`.
* **The area of a raw cap.** If `γ` has a smooth based cap `u₀` (witnessing `h`), the area of a
  raw cap `D` is `RawCap.area φ h D = ∫ u₀^* φ + ∫_{D -ᵥ u₀.homotopyClass} φ`. The area is only
  defined for loops with a smooth based cap. It does not depend on `u₀`: the area of the raw cap of
  every smooth based cap `u` is `∫ u^* φ` (`TauCeti.Floer.RawCap.area_homotopyClass`).
* **The recapping law.** Gluing a sphere `a ∈ π₂(M, x)` to a raw cap adds the integral of `φ` over
  `a` to its area, `area (a +ᵥ D) = ∫_a φ + area D` (`TauCeti.Floer.RawCap.area_vadd`), and the
  areas of two raw caps differ by the integral over the sphere by which they differ
  (`TauCeti.Floer.RawCap.area_sub_area`).
* **The gluing law.** A **smooth based homotopy** from a loop `γ₁` to a loop `γ₂`
  (`TauCeti.Floer.IsSmoothBasedHomotopy`) is a smooth cylinder `w`, `1`-periodic in `t`, from `γ₁`
  at `s = 0` to `γ₂` at `s = 1`, whose seam `t = 0` stays at `x`; a smooth based cap is one ending
  at the constant loop. Two smooth based homotopies glue to their concatenation `rectangleTrans`
  (`TauCeti.Floer.IsSmoothBasedHomotopy.rectangleTrans`), whose homotopy class is the composite of
  theirs (`TauCeti.Floer.IsSmoothBasedHomotopy.homotopyClass_rectangleTrans`). The homotopy class
  `IsSmoothBasedHomotopy.homotopyClass` glues to raw caps `D` of `γ₂`, giving the raw caps
  `w.homotopyClass ≫ D` of `γ₁`. On smooth caps `u` of `γ₂` this is the class of the concatenation
  `rectangleTrans w u`, a smooth based cap of `γ₁`, so gluing a cylinder to a cap adds its
  integral to the area, `area (w ≫ D) = ∫ w^* φ + area D`
  (`TauCeti.Floer.RawCap.area_homotopyClass_comp`), and cutting it off subtracts it
  (`TauCeti.Floer.RawCap.area_inv_homotopyClass_comp`). The energy identity of a Floer cylinder has
  the area `∫ w^* ω` as its topological term; when the cylinder is a smooth based homotopy, this
  law rewrites that term as the difference `area (w ≫ D) - area D` of the areas of raw caps of its
  two ends, the form in which actions of capped orbits enter capped Floer theory.
* **The gluing law for pairs of pants.** The concatenation `γ₁ ⬝ γ₂` of two loops is not smooth
  where they meet, so a smooth pair of pants with inputs `γ₁`, `γ₂` and output `γ₀` is taken to
  be a smooth based homotopy `w` from `γ₀` to their collared concatenation `γ₁.collaredTrans γ₂`
  (`Path.collaredTrans`, in `TauCeti.Topology.PathSpace.CollaredTrans`), the concatenation
  reparametrized to rest near its ends and its junction.
  Its class as a pair of pants `γ₀ ⟶ γ₁ ⬝ γ₂` is `w.homotopyClass` followed by the inverse of the
  reparametrization class `Path.collaredTransHom γ₁ γ₂`. Smooth based caps `u₁`, `u₂` of `γ₁`,
  `γ₂` placed side by side (`TauCeti.loopwiseTrans`) form a smooth based cap of
  `γ₁.collaredTrans γ₂` (`TauCeti.Floer.IsSmoothBasedCap.loopwiseTrans`), whose raw cap is the
  product of the raw caps of `u₁` and `u₂` in the H-space `Ω M x`, conjugated by
  `Path.collaredTransHom` (`TauCeti.Floer.IsSmoothBasedCap.homotopyClass_loopwiseTrans`), and
  whose integral is the sum of theirs
  (`TauCeti.Floer.IsSmoothBasedHomotopy.rectangleIntegral_loopwiseTrans`). Hence gluing raw caps
  `D₁`, `D₂` to the pair of pants with `TauCeti.Floer.RawCap.pantsGlue` adds the integral of `φ`
  over `w` to the sum of their areas,
  `area (pantsGlue P D₁ D₂) = ∫ w^* φ + area D₁ + area D₂` (`TauCeti.Floer.RawCap.area_pantsGlue`).
  For a smooth based pair of pants, this is the form the area term `∫ w^* ω` takes in terms of
  the areas of caps of its three ends.

The recapping law is the hypothesis of `TauCeti.Floer.CapClass.lift`, with the area homomorphism
`TauCeti.sphereIntegralHom` on the group `π₂(M, x)` of spheres. The area is measured with the cap
oriented from `γ` to its centre, as for `TauCeti.capArea`; the capped action
`TauCeti.cappedLoopAction` uses the disc oriented from its centre to `γ`, so for a smooth based cap
`hu : IsSmoothBasedCap I γ u` its area term is `-RawCap.area φ ⟨u, hu⟩ hu.homotopyClass`
(`TauCeti.Floer.IsSmoothBasedCap.cappedLoopAction_comp_prodMap_one_sub`).

## Main definitions

* `TauCeti.Floer.IsSmoothBasedCap I γ u`: `u` is a smooth based cap of `γ`.
* `TauCeti.Floer.IsSmoothBasedHomotopy I γ₁ γ₂ w`: `w` is a smooth based homotopy of loops from
  `γ₁` to `γ₂`.
* `TauCeti.Floer.IsSmoothBasedHomotopy.homotopyClass`: its class in the fundamental groupoid of the
  loop space; for a smooth based cap, its raw cap.
* `TauCeti.Floer.RawCap.area φ h D`: the integral of `φ` over a raw cap `D` of a loop with a
  smooth based cap (`h`).

## Main results

* `TauCeti.Floer.IsSmoothBasedCap.homotopyClass_vsub_homotopyClass_toMul`: two smooth based caps
  differ by the sphere represented by their concatenation.
* `TauCeti.Floer.IsSmoothBasedCap.sphereIntegral_homotopyClass_vsub_homotopyClass`: two smooth
  based caps differ by a sphere whose integral is the difference of their integrals.
* `TauCeti.Floer.RawCap.area_homotopyClass`: the area of the raw cap of a smooth based cap is its
  integral.
* `TauCeti.Floer.RawCap.area_vadd`: the recapping law.
* `TauCeti.Floer.RawCap.area_sub_area`: two raw caps have areas differing by the integral over the
  sphere by which they differ.
* `TauCeti.Floer.IsSmoothBasedHomotopy.rectangleTrans`,
  `TauCeti.Floer.IsSmoothBasedHomotopy.homotopyClass_rectangleTrans`: two smooth based homotopies
  glue to a smooth based homotopy, whose homotopy class is the composite of theirs.
* `TauCeti.Floer.RawCap.area_homotopyClass_comp`,
  `TauCeti.Floer.RawCap.area_inv_homotopyClass_comp`: gluing a smooth based homotopy to a raw cap
  adds its integral to the area, and cutting it off subtracts it.
* `TauCeti.Floer.IsSmoothBasedHomotopy.loopwiseTrans`,
  `TauCeti.Floer.IsSmoothBasedHomotopy.homotopyClass_loopwiseTrans`: two smooth based homotopies
  placed side by side form a smooth based homotopy between collared concatenations, whose class is
  the product of theirs in the H-space `Ω M x`, conjugated by `Path.collaredTransHom`;
  `TauCeti.Floer.IsSmoothBasedCap.loopwiseTrans` and
  `TauCeti.Floer.IsSmoothBasedCap.homotopyClass_loopwiseTrans` for caps.
* `TauCeti.Floer.IsSmoothBasedHomotopy.rectangleIntegral_loopwiseTrans`: the integral over smooth
  based homotopies placed side by side is the sum of their integrals.
* `TauCeti.Floer.RawCap.area_pantsGlue`: gluing raw caps to a smooth pair of pants adds its integral
  to the sum of their areas.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, on the action of capped loops and its recapping law.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  Section 11.1 (the symplectic area of spherical classes and capped loops).
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on
  the classes and energy of pairs of pants relative to caps of their boundary orbits.
-/

public section

noncomputable section

open Set CategoryTheory HomotopyGroup
open scoped Manifold ContDiff Topology Topology.Homotopy

namespace TauCeti.Floer

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {x : M} {γ : Ω M x}

/-- The reparametrization of the unit interval under which the concatenation of the paths in the
loop space of two smooth based homotopies becomes the path of their concatenation
`TauCeti.rectangleTrans`: `Path.transReparam id id`, which is `s ↦ β (3 s) / 2` on `[0, 1/2]` and
`s ↦ (1 + β (3 s - 2)) / 2` on `(1/2, 1]`, where `β = Real.smoothTransition`. -/
private def concatReparamI : unitInterval → unitInterval :=
  Path.transReparam id id

private theorem continuous_concatReparamI : Continuous concatReparamI :=
  Path.continuous_transReparam continuous_id continuous_id (fun _ h ↦ h) fun _ h ↦ h

private theorem concatReparamI_zero : concatReparamI 0 = 0 :=
  Path.transReparam_zero le_rfl

private theorem concatReparamI_one : concatReparamI 1 = 1 :=
  Path.transReparam_one le_rfl

/-! ### Smooth based homotopies of loops -/

variable (I) in
/-- A **smooth based homotopy** of loops from `γ₁` to `γ₂`, both based at `x`: a smooth map
`w : ℝ × ℝ → M`, `1`-periodic in its second coordinate, which runs along `γ₁` for `s = 0` and along
`γ₂` for `s = 1`, and sends the edge `t = 0` of the unit square to `x`. The loops `w (s, ·)` are
based at `x`, so `s ↦ w (s, ·)` is a path in the loop space from `γ₁` to `γ₂`: a cylinder whose
seam stays at the base point. A smooth based cap is a smooth based homotopy to the constant loop
(`TauCeti.Floer.IsSmoothBasedCap`). -/
structure IsSmoothBasedHomotopy (γ₁ γ₂ : Ω M x) (w : ℝ × ℝ → M) : Prop where
  /-- A smooth based homotopy is smooth. -/
  contMDiff : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ w
  /-- A smooth based homotopy is `1`-periodic in its second coordinate. -/
  apply_add_one : ∀ z : ℝ × ℝ, w (z.1, z.2 + 1) = w z
  /-- A smooth based homotopy starts at the first loop. -/
  apply_zero : ∀ t : unitInterval, w (0, t) = γ₁ t
  /-- A smooth based homotopy ends at the second loop. -/
  apply_one : ∀ t : unitInterval, w (1, t) = γ₂ t
  /-- The seam `t = 0` stays at the base point. -/
  apply_seam : ∀ s : unitInterval, w (s, 0) = x

namespace IsSmoothBasedHomotopy

variable {γ₁ γ₂ γ₃ : Ω M x} {w v : ℝ × ℝ → M}

/-- The edge `t = 1` of a smooth based homotopy stays at the base point. -/
theorem apply_seam_one (hw : IsSmoothBasedHomotopy I γ₁ γ₂ w) (s : unitInterval) :
    w (s, 1) = x := by
  simpa using (hw.apply_add_one (s, 0)).trans (hw.apply_seam s)

/-- The path `s ↦ w (s, ·)` in the loop space of a smooth based homotopy `w`, from `γ₁` to
`γ₂`. -/
def toPath (hw : IsSmoothBasedHomotopy I γ₁ γ₂ w) : Path γ₁ γ₂ :=
  Path.ofContinuousFamily (fun s t : unitInterval ↦ w (s, t))
    (hw.contMDiff.continuous.comp (by fun_prop)) hw.apply_seam hw.apply_seam_one
    (fun t ↦ by rw [Icc.coe_zero, hw.apply_zero])
    (fun t ↦ by rw [Icc.coe_one, hw.apply_one])

@[simp]
theorem toPath_apply (hw : IsSmoothBasedHomotopy I γ₁ γ₂ w) (s t : unitInterval) :
    hw.toPath s t = w (s, t) :=
  Path.ofContinuousFamily_apply _ _ _ _ _ _ s t

/-- The homotopy class of a smooth based homotopy: the class of its path in the loop space, a
morphism from `γ₁` to `γ₂` in the fundamental groupoid of `Ω M x`. It glues to raw caps of `γ₂`
to give raw caps `hw.homotopyClass ≫ D` of `γ₁`. -/
def homotopyClass (hw : IsSmoothBasedHomotopy I γ₁ γ₂ w) :
    (⟨γ₁⟩ : FundamentalGroupoid (Ω M x)) ⟶ ⟨γ₂⟩ :=
  Path.Homotopic.Quotient.mk hw.toPath

theorem homotopyClass_def (hw : IsSmoothBasedHomotopy I γ₁ γ₂ w) :
    hw.homotopyClass = Path.Homotopic.Quotient.mk hw.toPath :=
  (rfl)

/-- The end `s = 1` of a smooth based homotopy to `γ₂` agrees along the whole line with the start
of a smooth based homotopy from `γ₂`: both are the periodic extension of `γ₂`. -/
theorem apply_one_eq_apply_zero (hw : IsSmoothBasedHomotopy I γ₁ γ₂ w)
    (hv : IsSmoothBasedHomotopy I γ₂ γ₃ v) (t : ℝ) : w (1, t) = v (0, t) :=
  congrFun (Function.Periodic.eq_of_eqOn_Ico (f := fun t ↦ w (1, t)) (g := fun t ↦ v (0, t))
    (fun t ↦ hw.apply_add_one (1, t)) (fun t ↦ hv.apply_add_one (0, t)) one_pos 0 <| by
      rw [zero_add]
      exact fun t ht ↦
        (hw.apply_one ⟨t, ht.1, ht.2.le⟩).trans (hv.apply_zero ⟨t, ht.1, ht.2.le⟩).symm) t

/-- A smooth based homotopy from `γ₁` to `γ₂` run backwards is a smooth based homotopy from `γ₂`
to `γ₁`. -/
theorem comp_prodMap_one_sub (hw : IsSmoothBasedHomotopy I γ₁ γ₂ w) :
    IsSmoothBasedHomotopy I γ₂ γ₁ (w ∘ Prod.map (fun s ↦ 1 - s) id) where
  contMDiff := hw.contMDiff.comp ((contDiff_const.sub contDiff_id).prodMap contDiff_id).contMDiff
  apply_add_one z := hw.apply_add_one (1 - z.1, z.2)
  apply_zero t := by simpa using hw.apply_one t
  apply_one t := by simpa using hw.apply_zero t
  apply_seam s := by simpa using hw.apply_seam (unitInterval.symm s)

/-- The path in the loop space of a smooth based homotopy run backwards is the reverse of its
path. -/
@[simp]
theorem toPath_comp_prodMap_one_sub (hw : IsSmoothBasedHomotopy I γ₁ γ₂ w) :
    hw.comp_prodMap_one_sub.toPath = hw.toPath.symm :=
  Path.ext <| funext fun s ↦ Path.ext <| funext fun t ↦ by
    simp only [toPath_apply, Path.symm_apply, Function.comp_apply, Prod.map_apply, id_eq,
      unitInterval.coe_symm_eq]

/-- The homotopy class of a smooth based homotopy run backwards is the inverse of its homotopy
class. -/
@[simp]
theorem homotopyClass_comp_prodMap_one_sub (hw : IsSmoothBasedHomotopy I γ₁ γ₂ w) :
    hw.comp_prodMap_one_sub.homotopyClass = inv hw.homotopyClass := by
  rw [homotopyClass_def, homotopyClass_def, toPath_comp_prodMap_one_sub, ← Groupoid.inv_eq_inv]
  -- In the fundamental groupoid, `Groupoid.inv ⟦P⟧` is `⟦P.symm⟧` by definition.
  rfl

/-- The concatenation of the paths in the loop space of two smooth based homotopies `w` and `v`,
reparametrized by `concatReparamI`, is the path of their concatenation `rectangleTrans w v`. -/
private theorem trans_reparam_apply (hw : IsSmoothBasedHomotopy I γ₁ γ₂ w)
    (hv : IsSmoothBasedHomotopy I γ₂ γ₃ v) (s t : unitInterval) :
    (hw.toPath.trans hv.toPath).reparam concatReparamI continuous_concatReparamI
        concatReparamI_zero concatReparamI_one s t =
      rectangleTrans w v ((s : ℝ), (t : ℝ)) := by
  have h := hw.apply_one_eq_apply_zero hv
  have hβ₀ := Real.smoothTransition.nonneg (3 * (s : ℝ) - 2)
  have hβ₁ := Real.smoothTransition.le_one (3 * (s : ℝ))
  rw [Path.coe_reparam, Function.comp_apply, Path.trans_apply]
  rcases le_or_gt (s : ℝ) (1 / 2) with hs | hs
  · -- First half: `w`.
    have hc : (concatReparamI s : ℝ) ≤ 1 / 2 := by
      rw [concatReparamI, Path.coe_transReparam_of_le hs, id]
      linarith
    rw [dite_eq_left hc, rectangleTrans_eq_left h (by simp only; linarith)]
    simp only [toPath_apply, concatReparamI, Path.coe_transReparam_of_le hs, Function.comp_apply,
      Prod.map_apply, id_eq]
    congr 2
    ring
  · rw [rectangleTrans_eq_right h (by simp only; linarith)]
    simp only [Function.comp_apply, Prod.map_apply, id_eq]
    split_ifs with hc
    · -- Second half, while the path rests at `γ₂`.
      rw [concatReparamI, Path.coe_transReparam_of_lt hs, id] at hc
      have hz : Real.smoothTransition (3 * (s : ℝ) - 2) = 0 := by linarith
      simp only [toPath_apply, concatReparamI, Path.coe_transReparam_of_lt hs, id_eq, hz]
      norm_num [h]
    · -- Second half: `v`.
      simp only [toPath_apply, concatReparamI, Path.coe_transReparam_of_lt hs, id_eq]
      congr 2
      ring

/-- **Gluing smooth based homotopies.** The concatenation `rectangleTrans w v` of a smooth based
homotopy `w` from `γ₁` to `γ₂` and a smooth based homotopy `v` from `γ₂` to `γ₃` is a smooth based
homotopy from `γ₁` to `γ₃`. -/
theorem rectangleTrans (hw : IsSmoothBasedHomotopy I γ₁ γ₂ w)
    (hv : IsSmoothBasedHomotopy I γ₂ γ₃ v) :
    IsSmoothBasedHomotopy I γ₁ γ₃ (rectangleTrans w v) where
  contMDiff := _root_.TauCeti.contMDiff_rectangleTrans (n := ⊤) hw.contMDiff hv.contMDiff
    (hw.apply_one_eq_apply_zero hv)
  apply_add_one := rectangleTrans_apply_add_snd hw.apply_add_one hv.apply_add_one
  apply_zero t := by rw [rectangleTrans_apply_zero, hw.apply_zero]
  apply_one t := by rw [rectangleTrans_apply_one, hv.apply_one]
  apply_seam s := by
    rcases lt_or_ge (s : ℝ) (2 / 3) with hs | hs
    · rw [rectangleTrans_eq_left (hw.apply_one_eq_apply_zero hv) hs, Function.comp_apply,
        Prod.map_apply, ← unitInterval.coe_smoothTransition]
      exact hw.apply_seam _
    · rw [rectangleTrans_eq_right (hw.apply_one_eq_apply_zero hv) (by simp only; linarith),
        Function.comp_apply, Prod.map_apply, ← unitInterval.coe_smoothTransition]
      exact hv.apply_seam _

/-- **The homotopy class of a glued homotopy.** The homotopy class of the concatenation of two
smooth based homotopies is the composite of their homotopy classes. -/
theorem homotopyClass_rectangleTrans (hw : IsSmoothBasedHomotopy I γ₁ γ₂ w)
    (hv : IsSmoothBasedHomotopy I γ₂ γ₃ v) :
    (hw.rectangleTrans hv).homotopyClass = hw.homotopyClass ≫ hv.homotopyClass := by
  rw [homotopyClass_def, homotopyClass_def, homotopyClass_def, FundamentalGroupoid.comp_eq,
    ← Path.Homotopic.Quotient.mk_trans]
  -- The path of the glued homotopy reparametrizes the concatenation of the two paths.
  have hrep : (hw.rectangleTrans hv).toPath =
      (hw.toPath.trans hv.toPath).reparam concatReparamI continuous_concatReparamI
        concatReparamI_zero concatReparamI_one :=
    Path.ext <| funext fun s ↦ Path.ext <| funext fun t ↦
      (toPath_apply _ s t).trans (trans_reparam_apply hw hv s t).symm
  rw [hrep]
  exact Quotient.sound ⟨(Path.Homotopy.reparam (hw.toPath.trans hv.toPath) _
    continuous_concatReparamI concatReparamI_zero concatReparamI_one).symm⟩

end IsSmoothBasedHomotopy

/-! ### Smooth based caps -/

variable (I) in
/-- A **smooth based cap** of a loop `γ` based at `x`: a smooth based homotopy from `γ` to the
constant loop. It is a smooth map `u : ℝ × ℝ → M`, `1`-periodic in its second coordinate, which
starts at `γ` for `s = 0`, ends at `x` for `s = 1`, and sends the edge `t = 0` of the unit square to
`x`. The loops `u (s, ·)` are based at `x`, so `s ↦ u (s, ·)` is a path in the loop space from `γ`
to the constant loop, a disc bounding `γ` with its centre at `s = 1`. Periodicity makes `u (0, ·)`
the periodic extension of `γ`, which is how the one-periodic orbits of a Hamiltonian are
parametrized. -/
abbrev IsSmoothBasedCap (γ : Ω M x) (u : ℝ × ℝ → M) : Prop :=
  IsSmoothBasedHomotopy I γ (Path.refl x) u

/-- The constant map is a smooth based cap of the constant loop. -/
theorem isSmoothBasedCap_refl (x : M) : IsSmoothBasedCap I (Path.refl x) fun _ ↦ x :=
  ⟨contMDiff_const, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩

namespace IsSmoothBasedCap

variable {u u' : ℝ × ℝ → M}

/-- Two smooth based caps of the same loop agree along the whole line `s = 0`, where both are the
periodic extension of the loop. -/
theorem apply_zero_eq_apply_zero (hu : IsSmoothBasedCap I γ u) (hu' : IsSmoothBasedCap I γ u')
    (t : ℝ) : u (0, t) = u' (0, t) := by
  simpa using hu.comp_prodMap_one_sub.apply_one_eq_apply_zero hu' t

/-- The generalized loop of the reparametrized double loop of two smooth based caps restricts their
concatenation `rectangleTrans` to the unit square. -/
private theorem fromDoubleLoop_trans_reparam_apply (hu : IsSmoothBasedCap I γ u)
    (hu' : IsSmoothBasedCap I γ u') (y : Fin 2 → unitInterval) :
    GenLoop.fromDoubleLoop ((hu.toPath.symm.trans hu'.toPath).reparam concatReparamI
        continuous_concatReparamI concatReparamI_zero concatReparamI_one) y =
      rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u' ((y 0 : ℝ), (y 1 : ℝ)) := by
  rw [GenLoop.fromDoubleLoop_apply, ← hu.toPath_comp_prodMap_one_sub,
    IsSmoothBasedHomotopy.trans_reparam_apply]

/-- The concatenation `rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u'` of two smooth based
caps `u` and `u'` of the same loop, `u` run backwards followed by `u'`, is smooth. -/
theorem contMDiff_rectangleTrans (hu : IsSmoothBasedCap I γ u) (hu' : IsSmoothBasedCap I γ u') :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u') :=
  (hu.comp_prodMap_one_sub.rectangleTrans hu').contMDiff

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

/-! ### Gluing smooth based homotopies to smooth based caps -/

namespace IsSmoothBasedHomotopy

variable {γ₁ γ₂ : Ω M x} {w : ℝ × ℝ → M}

/-- If `w` is a smooth based homotopy from `γ₁` to `γ₂` and `γ₂` has a smooth based cap, then so
has `γ₁`. -/
theorem exists_isSmoothBasedCap (hw : IsSmoothBasedHomotopy I γ₁ γ₂ w)
    (h : ∃ u, IsSmoothBasedCap I γ₂ u) : ∃ u, IsSmoothBasedCap I γ₁ u :=
  let ⟨_, hu⟩ := h
  ⟨_, hw.rectangleTrans hu⟩

end IsSmoothBasedHomotopy

/-! ### Placing smooth based homotopies side by side -/

namespace IsSmoothBasedHomotopy

variable {γ₁ γ₁' γ₂ γ₂' γ γ' γ'' : Ω M x} {w w₁ w₂ : ℝ × ℝ → M}

/-- Reading a smooth based homotopy along `Real.smoothTransition` in its first coordinate, it stays
at the base point along the whole line `t = 0`. -/
private theorem apply_smoothTransition_seam (hw : IsSmoothBasedHomotopy I γ γ' w) (s : ℝ) :
    (w ∘ Prod.map Real.smoothTransition id) (s, 0) = x := by
  rw [Function.comp_apply, Prod.map_apply, id_eq, ← unitInterval.coe_smoothTransition]
  exact hw.apply_seam _

/-- Reading a smooth based homotopy along `Real.smoothTransition` in its first coordinate, it stays
at the base point along the whole line `t = 1`. -/
private theorem apply_smoothTransition_seam_one (hw : IsSmoothBasedHomotopy I γ γ' w) (s : ℝ) :
    (w ∘ Prod.map Real.smoothTransition id) (s, 1) = x := by
  rw [Function.comp_apply, Prod.map_apply, id_eq, ← unitInterval.coe_smoothTransition]
  exact hw.apply_seam_one _

/-- A smooth based homotopy read along `Real.smoothTransition` in its first coordinate is smooth. -/
private theorem contMDiff_comp_smoothTransition (hw : IsSmoothBasedHomotopy I γ γ' w) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (w ∘ Prod.map Real.smoothTransition id) :=
  hw.contMDiff.comp (Real.smoothTransition.contDiff.prodMap contDiff_id).contMDiff

/-- Two smooth based homotopies read along `Real.smoothTransition` in their first coordinate
agree along the seams where they are placed side by side. -/
private theorem loopwiseTrans_seam (hw₁ : IsSmoothBasedHomotopy I γ₁ γ₁' w₁)
    (hw₂ : IsSmoothBasedHomotopy I γ₂ γ₂' w₂) (s : ℝ) :
    (w₁ ∘ Prod.map Real.smoothTransition id) (s, 1) =
      (w₂ ∘ Prod.map Real.smoothTransition id) (s, 0) :=
  (apply_smoothTransition_seam_one hw₁ s).trans (apply_smoothTransition_seam hw₂ s).symm

/-- The loopwise concatenation of two smooth based homotopies, read along
`Real.smoothTransition` in the first coordinate, runs at each `s` along the collared concatenation
of their loops. -/
private theorem loopwiseTrans_apply (hw₁ : IsSmoothBasedHomotopy I γ₁ γ₁' w₁)
    (hw₂ : IsSmoothBasedHomotopy I γ₂ γ₂' w₂) (s : ℝ) (t : unitInterval) :
    TauCeti.loopwiseTrans (w₁ ∘ Prod.map Real.smoothTransition id)
        (w₂ ∘ Prod.map Real.smoothTransition id) (s, t) =
      (hw₁.toPath (unitInterval.smoothTransition s)).collaredTrans
        (hw₂.toPath (unitInterval.smoothTransition s)) t := by
  rcases le_or_gt (t : ℝ) (1 / 2) with ht | ht
  · rw [loopwiseTrans_of_le _ _ t.property.1 ht, Path.collaredTrans_apply_of_le _ _ ht,
      Path.extend_apply _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩,
      toPath_apply, Function.comp_apply, Prod.map_apply, id_eq, unitInterval.coe_smoothTransition]
  rcases lt_or_eq_of_le t.property.2 with ht₁ | ht₁
  · rw [loopwiseTrans_of_lt _ _ ht ht₁, Path.collaredTrans_apply_of_lt _ _ ht,
      Path.extend_apply _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩,
      toPath_apply, Function.comp_apply, Prod.map_apply, id_eq, unitInterval.coe_smoothTransition]
  · -- At `t = 1` both rest at the base point.
    have h := loopwiseTrans_apply_add_one (w₁ ∘ Prod.map Real.smoothTransition id)
      (w₂ ∘ Prod.map Real.smoothTransition id) s 0
    simp only [zero_add] at h
    rw [ht₁, h, loopwiseTrans_of_le _ _ le_rfl (by norm_num), mul_zero, zero_sub,
      Real.smoothTransition.zero_of_nonpos (by norm_num), apply_smoothTransition_seam hw₁,
      show t = 1 from Subtype.ext ht₁, Path.target]

/-- **Placing smooth based homotopies side by side.** For smooth based homotopies `w₁` from `γ₁`
to `γ₁'` and `w₂` from `γ₂` to `γ₂'`, their loopwise concatenation, read along
`Real.smoothTransition` in the first coordinate, is a smooth based homotopy from the collared
concatenation of `γ₁` and `γ₂` to that of `γ₁'` and `γ₂'`. -/
theorem loopwiseTrans (hw₁ : IsSmoothBasedHomotopy I γ₁ γ₁' w₁)
    (hw₂ : IsSmoothBasedHomotopy I γ₂ γ₂' w₂) :
    IsSmoothBasedHomotopy I (γ₁.collaredTrans γ₂) (γ₁'.collaredTrans γ₂')
      (TauCeti.loopwiseTrans (w₁ ∘ Prod.map Real.smoothTransition id)
        (w₂ ∘ Prod.map Real.smoothTransition id)) where
  contMDiff := contMDiff_loopwiseTrans (contMDiff_comp_smoothTransition hw₁)
    (contMDiff_comp_smoothTransition hw₂) (loopwiseTrans_seam hw₁ hw₂) (loopwiseTrans_seam hw₂ hw₁)
  apply_add_one z := loopwiseTrans_apply_add_one _ _ z.1 z.2
  apply_zero t := by
    rw [loopwiseTrans_apply hw₁ hw₂, unitInterval.smoothTransition_zero, Path.source, Path.source]
  apply_one t := by
    rw [loopwiseTrans_apply hw₁ hw₂, unitInterval.smoothTransition_one, Path.target, Path.target]
  apply_seam s := by
    rw [loopwiseTrans_of_le _ _ le_rfl (by norm_num), mul_zero, zero_sub,
      Real.smoothTransition.zero_of_nonpos (by norm_num)]
    exact apply_smoothTransition_seam hw₁ s

/-- The path in the loop space of collared concatenations of the loops of two smooth based
homotopies at equal times: the pointwise concatenation of their paths, followed by
reparametrization of each loop by `Path.collaredTransReparam`. -/
private def collaredTransPath (hw₁ : IsSmoothBasedHomotopy I γ₁ γ₁' w₁)
    (hw₂ : IsSmoothBasedHomotopy I γ₂ γ₂' w₂) :
    Path (γ₁.collaredTrans γ₂) (γ₁'.collaredTrans γ₂') :=
  ((hw₁.toPath.prod hw₂.toPath).map (HSpace.hmul (X := Ω M x)).continuous).map
    (Path.continuous_reparam Path.continuous_collaredTransReparam Path.collaredTransReparam_zero
      Path.collaredTransReparam_one)

private theorem collaredTransPath_apply (hw₁ : IsSmoothBasedHomotopy I γ₁ γ₁' w₁)
    (hw₂ : IsSmoothBasedHomotopy I γ₂ γ₂' w₂) (s : unitInterval) :
    collaredTransPath hw₁ hw₂ s = (hw₁.toPath s).collaredTrans (hw₂.toPath s) :=
  (rfl)

/-- The path in the loop space of the loopwise concatenation of two smooth based homotopies is the
path of collared concatenations of their loops, read along `Real.smoothTransition`. -/
private theorem toPath_loopwiseTrans (hw₁ : IsSmoothBasedHomotopy I γ₁ γ₁' w₁)
    (hw₂ : IsSmoothBasedHomotopy I γ₂ γ₂' w₂) :
    (hw₁.loopwiseTrans hw₂).toPath =
      (collaredTransPath hw₁ hw₂).reparam (fun s ↦ unitInterval.smoothTransition s)
        (unitInterval.continuous_smoothTransition.comp continuous_subtypeVal)
        unitInterval.smoothTransition_zero unitInterval.smoothTransition_one :=
  Path.ext <| funext fun s ↦ Path.ext <| funext fun t ↦ by
    rw [toPath_apply, loopwiseTrans_apply hw₁ hw₂, Path.coe_reparam, Function.comp_apply,
      collaredTransPath_apply]

/-- **The homotopy class of smooth based homotopies placed side by side.** The homotopy class of
the loopwise concatenation of two smooth based homotopies is the product of their homotopy
classes in the H-space `Ω M x`, conjugated by the classes joining concatenations to collared
concatenations. -/
theorem homotopyClass_loopwiseTrans (hw₁ : IsSmoothBasedHomotopy I γ₁ γ₁' w₁)
    (hw₂ : IsSmoothBasedHomotopy I γ₂ γ₂' w₂) :
    (hw₁.loopwiseTrans hw₂).homotopyClass =
      inv (Path.collaredTransHom γ₁ γ₂) ≫ HSpace.pathHmul hw₁.homotopyClass hw₂.homotopyClass ≫
        Path.collaredTransHom γ₁' γ₂' := by
  set R : (⟨γ₁.collaredTrans γ₂⟩ : FundamentalGroupoid (Ω M x)) ⟶ ⟨γ₁'.collaredTrans γ₂'⟩ :=
    Path.Homotopic.Quotient.mk (collaredTransPath hw₁ hw₂) with hR
  -- Reparametrizing the path does not change its class.
  have hrep : (hw₁.loopwiseTrans hw₂).homotopyClass = R := by
    rw [homotopyClass_def, toPath_loopwiseTrans hw₁ hw₂]
    exact Quotient.sound ⟨(Path.Homotopy.reparam _ _ _ _ _).symm⟩
  -- Naturality of the straight-line reparametrization along the path of pointwise concatenations.
  have hnat : HSpace.pathHmul hw₁.homotopyClass hw₂.homotopyClass ≫
      Path.collaredTransHom γ₁' γ₂' = Path.collaredTransHom γ₁ γ₂ ≫ R := by
    rw [homotopyClass_def, homotopyClass_def, HSpace.pathHmul_mk, Path.collaredTransHom_def,
      Path.collaredTransHom_def, hR, collaredTransPath]
    have h := Path.Homotopic.map_trans_evalAt (Path.reparamHomotopy Path.collaredTransReparam
      Path.continuous_collaredTransReparam Path.collaredTransReparam_zero
      Path.collaredTransReparam_one) ((hw₁.toPath.prod hw₂.toPath).map
        (HSpace.hmul (X := Ω M x)).continuous)
    simp only [ContinuousMap.coe_id, Path.map_id] at h
    -- Composition of classes is the class of the concatenation (`FundamentalGroupoid.comp_eq`,
    -- `Path.Homotopic.Quotient.mk_trans`). The middle objects `HSpace.hmul (γ₁', γ₂')` and
    -- `γ₁'.trans γ₂'` agree only by `Path.hmul_eq_trans`, so `exact` applies these two equations
    -- where `rw` cannot.
    exact Path.Homotopic.Quotient.eq.2 h
  rw [hrep, hnat, IsIso.inv_hom_id_assoc]

/-- **The integral over smooth based homotopies placed side by side.** The integral of a continuous
two-form over the loopwise concatenation of two smooth based homotopies, read along
`Real.smoothTransition` in the first coordinate, is the sum of their integrals. -/
theorem rectangleIntegral_loopwiseTrans [IsManifold I 1 M] {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 0 φ) (hw₁ : IsSmoothBasedHomotopy I γ₁ γ₁' w₁)
    (hw₂ : IsSmoothBasedHomotopy I γ₂ γ₂' w₂) :
    rectangleIntegral φ (TauCeti.loopwiseTrans (w₁ ∘ Prod.map Real.smoothTransition id)
        (w₂ ∘ Prod.map Real.smoothTransition id)) (0, 0) (1, 1) =
      rectangleIntegral φ w₁ (0, 0) (1, 1) + rectangleIntegral φ w₂ (0, 0) (1, 1) := by
  have hβ : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff
  rw [TauCeti.rectangleIntegral_loopwiseTrans hφ
      ((contMDiff_comp_smoothTransition hw₁).of_le (by simp))
      ((contMDiff_comp_smoothTransition hw₂).of_le (by simp))
      (loopwiseTrans_seam hw₁ hw₂)
      (loopwiseTrans_seam hw₂ hw₁),
    rectangleIntegral_comp_prodMap_of_contDiff hφ (hw₁.contMDiff.of_le (by simp)) hβ,
    rectangleIntegral_comp_prodMap_of_contDiff hφ (hw₂.contMDiff.of_le (by simp)) hβ,
    Real.smoothTransition.zero, Real.smoothTransition.one]

/-- Changing the end loop of a smooth based homotopy along an equality of loops. -/
private theorem of_eq_target (hw : IsSmoothBasedHomotopy I γ γ' w) (h : γ' = γ'') :
    IsSmoothBasedHomotopy I γ γ'' w :=
  h ▸ hw

private theorem homotopyClass_of_eq_target (hw : IsSmoothBasedHomotopy I γ γ' w) (h : γ' = γ'') :
    (hw.of_eq_target h).homotopyClass = hw.homotopyClass ≫ eqToHom (congrArg _ h) := by
  subst h
  rw [eqToHom_refl, Category.comp_id]

end IsSmoothBasedHomotopy

namespace IsSmoothBasedCap

variable {γ₁ γ₂ : Ω M x} {u₁ u₂ : ℝ × ℝ → M}

/-- **Placing smooth caps side by side.** For smooth based caps `u₁` of `γ₁` and `u₂` of `γ₂`,
their loopwise concatenation, read along `Real.smoothTransition` in the first coordinate, is a
smooth based cap of the collared concatenation of `γ₁` and `γ₂`. -/
theorem loopwiseTrans (hu₁ : IsSmoothBasedCap I γ₁ u₁) (hu₂ : IsSmoothBasedCap I γ₂ u₂) :
    IsSmoothBasedCap I (γ₁.collaredTrans γ₂)
      (TauCeti.loopwiseTrans (u₁ ∘ Prod.map Real.smoothTransition id)
        (u₂ ∘ Prod.map Real.smoothTransition id)) :=
  IsSmoothBasedHomotopy.of_eq_target (IsSmoothBasedHomotopy.loopwiseTrans hu₁ hu₂)
    (Path.collaredTrans_refl x)

/-- **The raw cap of smooth caps placed side by side.** The raw cap of the loopwise concatenation
of smooth based caps `u₁` and `u₂` is obtained from the product of their raw caps in the H-space
`Ω M x` through the class joining the concatenation of `γ₁` and `γ₂` to their collared
concatenation. -/
theorem homotopyClass_loopwiseTrans (hu₁ : IsSmoothBasedCap I γ₁ u₁)
    (hu₂ : IsSmoothBasedCap I γ₂ u₂) :
    (hu₁.loopwiseTrans hu₂).homotopyClass =
      inv (Path.collaredTransHom γ₁ γ₂) ≫ HSpace.pathHmul hu₁.homotopyClass hu₂.homotopyClass ≫
        eqToHom (congrArg FundamentalGroupoid.mk HSpace.hmul_e_e) := by
  refine (IsSmoothBasedHomotopy.homotopyClass_of_eq_target
    (IsSmoothBasedHomotopy.loopwiseTrans hu₁ hu₂) (Path.collaredTrans_refl x)).trans ?_
  rw [IsSmoothBasedHomotopy.homotopyClass_loopwiseTrans hu₁ hu₂, Path.collaredTransHom_refl]
  simp only [Category.assoc, eqToHom_trans]

end IsSmoothBasedCap

/-! ### The area of a raw cap -/

section Area

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  {φ : RoughForm I M F 2}

/-- The **area** of a raw cap `D` of a loop `γ` with a smooth based cap `u₀`, for a two-form `φ`:
the integral of `φ` over `u₀` plus its integral over the sphere `D -ᵥ u₀.homotopyClass` by which
`D` differs from the raw cap of `u₀`. It is defined only for loops that have a smooth based cap. For
a closed `C¹` form it is the integral over the raw cap of any smooth based cap
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
    {u : ℝ × ℝ → M} (hu : IsSmoothBasedCap I γ u) :
    RawCap.area φ ⟨u, hu⟩ hu.homotopyClass = rectangleIntegral φ u (0, 0) (1, 1) := by
  have h : ∃ u, IsSmoothBasedCap I γ u := ⟨u, hu⟩
  rw [RawCap.area_def, h.choose_spec.sphereIntegral_homotopyClass_vsub_homotopyClass hφ hdφ hu,
    add_sub_cancel]

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

/-- **Gluing a cylinder to a cap adds its area.** If `w` is a smooth based homotopy from `γ₁` to
`γ₂`, and `γ₁` and `γ₂` have smooth based caps, then gluing `w` to a raw cap `D` of `γ₂` adds the
integral of a closed `C¹` two-form over `w` to the area. The first cap (`h₁`) exists whenever the
second (`h₂`) does (`TauCeti.Floer.IsSmoothBasedHomotopy.exists_isSmoothBasedCap`). -/
theorem RawCap.area_homotopyClass_comp (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0)
    {γ₁ γ₂ : Ω M x} {w : ℝ × ℝ → M} (hw : IsSmoothBasedHomotopy I γ₁ γ₂ w)
    (h₁ : ∃ u, IsSmoothBasedCap I γ₁ u) (h₂ : ∃ u, IsSmoothBasedCap I γ₂ u) (D : RawCap γ₂) :
    RawCap.area φ h₁ (hw.homotopyClass ≫ D) =
      rectangleIntegral φ w (0, 0) (1, 1) + RawCap.area φ h₂ D := by
  obtain ⟨u, hu⟩ := h₂
  have : Nonempty (RawCap γ₂) := ⟨D⟩
  -- Write `D` as a sphere glued to the raw cap of `u`, and glue `w` to the smooth cap `u`.
  rw [← vsub_vadd D hu.homotopyClass, RawCap.comp_vadd, ← hw.homotopyClass_rectangleTrans hu,
    RawCap.area_vadd hφ hdφ, RawCap.area_vadd hφ hdφ, RawCap.area_homotopyClass hφ hdφ,
    RawCap.area_homotopyClass hφ hdφ, rectangleIntegral_rectangleTrans (hφ.of_le (by simp))
      (hw.contMDiff.of_le (by simp)) (hu.contMDiff.of_le (by simp))
      (hw.apply_one_eq_apply_zero hu)]
  abel

/-- **Cutting a cylinder off a cap subtracts its area.** If `w` is a smooth based homotopy from
`γ₁` to `γ₂`, and `γ₁` and `γ₂` have smooth based caps, then gluing the inverse of `w` to a raw cap
`D` of `γ₁` subtracts the integral of a closed `C¹` two-form over `w` from the area. -/
theorem RawCap.area_inv_homotopyClass_comp (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0)
    {γ₁ γ₂ : Ω M x} {w : ℝ × ℝ → M} (hw : IsSmoothBasedHomotopy I γ₁ γ₂ w)
    (h₁ : ∃ u, IsSmoothBasedCap I γ₁ u) (h₂ : ∃ u, IsSmoothBasedCap I γ₂ u) (D : RawCap γ₁) :
    RawCap.area φ h₂ (inv hw.homotopyClass ≫ D) =
      RawCap.area φ h₁ D - rectangleIntegral φ w (0, 0) (1, 1) := by
  have h := RawCap.area_homotopyClass_comp hφ hdφ hw h₁ h₂ (inv hw.homotopyClass ≫ D)
  rw [IsIso.hom_inv_id_assoc] at h
  exact eq_sub_of_add_eq' h.symm

/-- **The capped action of a smooth cap.** For a smooth based cap `u` of `γ` and a closed real
`C¹` two-form `σ`, the capped action of `γ` with the disc `u` run backwards, from its centre to
`γ`, is minus the area of the raw cap of `u` plus the Hamiltonian term. -/
theorem IsSmoothBasedCap.cappedLoopAction_comp_prodMap_one_sub {σ : RoughForm I M ℝ 2}
    (hσ : IsSmoothForm I 1 σ) (hdσ : mextDeriv σ = 0) (Ham : ℝ → M → ℝ) {u : ℝ × ℝ → M}
    (hu : IsSmoothBasedCap I γ u) :
    cappedLoopAction σ Ham (fun t ↦ u (0, t)) (u ∘ Prod.map (fun s ↦ 1 - s) id) =
      -RawCap.area σ ⟨u, hu⟩ hu.homotopyClass + ∫ t in 0..1, Ham t (u (0, t)) := by
  rw [cappedLoopAction_def, rectangleIntegral_comp_prodMap_one_sub (hσ.of_le (by simp))
    (hu.contMDiff.of_le (by simp)), RawCap.area_homotopyClass hσ hdσ hu]

/-- **Gluing a pair of pants to caps adds its area.** Let `w` be a smooth based homotopy from `γ₀`
to the collared concatenation of `γ₁` and `γ₂`: a smooth pair of pants with output `γ₀` and
inputs `γ₁`, `γ₂`, whose seam `t = 0` stays at the base point. Its class as a pair of pants
`γ₀ ⟶ γ₁ ⬝ γ₂` is `w.homotopyClass ≫ inv (Path.collaredTransHom γ₁ γ₂)`. If `γ₀`, `γ₁` and `γ₂`
have smooth based caps, then gluing raw caps `D₁` of `γ₁` and `D₂` of `γ₂` to this pair of pants
gives a raw cap of `γ₀` whose area, for a closed `C¹` two-form, is the integral of the form over
`w` plus the areas of `D₁` and `D₂`. The first cap (`h₀`) exists whenever the other two do. -/
theorem RawCap.area_pantsGlue (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0)
    {γ₀ γ₁ γ₂ : Ω M x} {w : ℝ × ℝ → M} (hw : IsSmoothBasedHomotopy I γ₀ (γ₁.collaredTrans γ₂) w)
    (h₀ : ∃ u, IsSmoothBasedCap I γ₀ u) (h₁ : ∃ u, IsSmoothBasedCap I γ₁ u)
    (h₂ : ∃ u, IsSmoothBasedCap I γ₂ u) (D₁ : RawCap γ₁) (D₂ : RawCap γ₂) :
    RawCap.area φ h₀ (RawCap.pantsGlue (hw.homotopyClass ≫ inv (Path.collaredTransHom γ₁ γ₂))
        D₁ D₂) =
      rectangleIntegral φ w (0, 0) (1, 1) + RawCap.area φ h₁ D₁ + RawCap.area φ h₂ D₂ := by
  obtain ⟨u₁, hu₁⟩ := h₁
  obtain ⟨u₂, hu₂⟩ := h₂
  have : Nonempty (RawCap γ₁) := ⟨D₁⟩
  have : Nonempty (RawCap γ₂) := ⟨D₂⟩
  -- Reduce to the raw caps of `u₁` and `u₂`, by the equivariance of gluing.
  rw [← vsub_vadd D₁ hu₁.homotopyClass, ← vsub_vadd D₂ hu₂.homotopyClass,
    RawCap.pantsGlue_vadd_left, RawCap.pantsGlue_vadd_right, RawCap.area_vadd hφ hdφ,
    RawCap.area_vadd hφ hdφ, RawCap.area_vadd hφ hdφ, RawCap.area_vadd hφ hdφ]
  -- The caps `u₁` and `u₂` glue to `w` as the smooth cap `v` of the collared concatenation.
  set hv := hu₁.loopwiseTrans hu₂
  have hglue : RawCap.pantsGlue (hw.homotopyClass ≫ inv (Path.collaredTransHom γ₁ γ₂))
      hu₁.homotopyClass hu₂.homotopyClass = hw.homotopyClass ≫ hv.homotopyClass := by
    rw [RawCap.pantsGlue_def, IsSmoothBasedCap.homotopyClass_loopwiseTrans hu₁ hu₂]
    simp only [Category.assoc]
  rw [hglue, RawCap.area_homotopyClass_comp hφ hdφ hw h₀ ⟨_, hv⟩,
    RawCap.area_homotopyClass hφ hdφ hv, RawCap.area_homotopyClass hφ hdφ hu₁,
    RawCap.area_homotopyClass hφ hdφ hu₂,
    IsSmoothBasedHomotopy.rectangleIntegral_loopwiseTrans (hφ.of_le (by simp)) hu₁ hu₂]
  abel

end Area

end TauCeti.Floer

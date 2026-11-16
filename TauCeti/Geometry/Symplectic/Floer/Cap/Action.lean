/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Area

/-!
# The action of capped loops on raw caps and cap classes

Let `M` be a compact boundaryless manifold with a closed `C¹` two-form `σ`, for instance a closed
symplectic manifold, let `Ham : ℝ → M → ℝ` be a time-dependent Hamiltonian, and let `γ` be a loop
in `M` based at `x` that has a smooth based cap (`TauCeti.Floer.IsSmoothBasedCap`). The capped
action of `γ` with a disc `D` running from its centre to `γ` is
`A_H(γ, D) = ∫ D^* σ + ∫₀¹ H(t, γ(t)) dt` (`TauCeti.cappedLoopAction`). This file defines it on
the raw caps of `γ` (`TauCeti.Floer.RawCap γ`), the homotopy classes of discs bounding `γ`, and
descends it to the cap classes `TauCeti.Floer.SphericalCapClass ω c γ` of capped Hamiltonian Floer
theory.

* **The action of a raw cap.** A raw cap `D` is oriented from `γ` to its centre, so the area term
  of the capped action is minus its area (`TauCeti.Floer.RawCap.area`), and
  `RawCap.action σ Ham h D = -RawCap.area σ h D + ∫₀¹ Ham(t, γ(t)) dt`. On the raw cap of a smooth
  based cap `u` it is the capped action of `γ` with the disc `u` run backwards
  (`TauCeti.Floer.RawCap.action_rawCap`).
* **The recapping law.** Gluing a sphere `a ∈ π₂(M, x)` to a raw cap, with the orientation of the
  cap, lowers the action by the integral of `σ` over `a`
  (`TauCeti.Floer.RawCap.action_vadd`), and two raw caps have actions differing by minus the
  integral over the sphere by which they differ (`TauCeti.Floer.RawCap.action_sub_action`). When
  `σ` vanishes on spheres the action does not depend on the cap
  (`TauCeti.Floer.RawCap.action_eq_action_of_vanishesOnSpheres`).
* **Descent to cap classes.** Let `ω` and `c` be homomorphisms on `H₂(M; ℤ)` defining the period
  group `Γ = SphericalPeriodGroup ω c`, and suppose that `ω` is the integral of `σ` on spherical
  classes: `ω` of the Hurewicz class of every sphere `a` is `∫_a σ`. Then the action descends to the
  cap classes of `γ` (`TauCeti.Floer.SphericalCapClass.action`), and recapping a cap class by a
  class `B ∈ Γ` lowers its action by the area of `B`
  (`TauCeti.Floer.SphericalCapClass.action_vadd`). So the cap classes of finitely many orbits,
  with their actions, are generators with an equivariant potential for the periods
  `PeriodGroup.area`, in the sense of `TauCeti.NovikovModule`. When the area is injective on `Γ`,
  for instance when `c` vanishes on spherical classes, a cap class is determined by its action
  (`TauCeti.Floer.SphericalCapClass.action_injective`).

The sign in the recapping law comes from the orientation of the torsor of raw caps:
`a +ᵥ D` glues `a` with the orientation of the cap, from `γ` to its centre, while the capped action
measures the disc from its centre to `γ`. With the orientation of the disc, gluing a sphere `B` to
`D` is `(-B) +ᵥ D`, and the law reads `A_H(γ, B # D) = ω(B) + A_H(γ, D)`.

That the integral of a closed form over spheres factors through their Hurewicz classes in
`H₂(M; ℤ)` is not proved here: the descent takes a homomorphism `ω` on `H₂(M; ℤ)` together with
its agreement with the sphere integral `TauCeti.sphereIntegralHom`.

## Main definitions

* `TauCeti.Floer.RawCap.action`: the capped action of a loop with a raw cap.
* `TauCeti.Floer.SphericalCapClass.action`: the capped action of a loop with a cap class.

## Main results

* `TauCeti.Floer.RawCap.action_rawCap`: the action of a smooth cap is the capped action.
* `TauCeti.Floer.RawCap.action_vadd`, `TauCeti.Floer.SphericalCapClass.action_vadd`: the
  recapping laws.
* `TauCeti.Floer.SphericalCapClass.action_sub_action`: two cap classes have actions differing by
  minus the area of the class by which they differ.
* `TauCeti.Floer.SphericalCapClass.action_injective`: when the area is injective on the period
  group, a cap class is determined by its action.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, on the action of capped loops and its recapping law.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  Section 11.1 (the action functional on the cover of the loop space).
-/

public section

noncomputable section

open Set HomotopyGroup
open scoped Manifold Topology Topology.Homotopy

namespace TauCeti.Floer

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [FiniteDimensional ℝ E] [I.Boundaryless]

/-! ### The action of a raw cap -/

section Raw

open scoped ContDiff

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [T2Space M] {x : M} {γ : Ω M x} {σ : RoughForm I M ℝ 2}

namespace RawCap

/-- The **capped action** of a loop `γ` with a raw cap `D`, for a two-form `σ` and a
time-dependent Hamiltonian `Ham`: minus the area of `D` plus `∫₀¹ Ham(t, γ(t)) dt`. The raw cap is
oriented from `γ` to its centre, so minus its area is the area of the disc from its centre to `γ`,
as in `TauCeti.cappedLoopAction`. It is defined for loops with a smooth based cap (`h`), like
`TauCeti.Floer.RawCap.area`. -/
def action (σ : RoughForm I M ℝ 2) (Ham : ℝ → M → ℝ) (h : ∃ u, IsSmoothBasedCap I γ u)
    (D : RawCap γ) : ℝ :=
  -RawCap.area σ h D + ∫ t in 0..1, Ham t (γ.extend t)

/-- The defining equation of `TauCeti.Floer.RawCap.action`. -/
theorem action_def (σ : RoughForm I M ℝ 2) (Ham : ℝ → M → ℝ) (h : ∃ u, IsSmoothBasedCap I γ u)
    (D : RawCap γ) :
    action σ Ham h D = -RawCap.area σ h D + ∫ t in 0..1, Ham t (γ.extend t) :=
  (rfl)

/-- **The action of a smooth cap.** For a closed `C¹` two-form, the action of the raw cap of a
smooth based cap `u` is the capped action of `γ` with the disc `u` run backwards, from its centre
to `γ`. -/
theorem action_rawCap (hσ : IsSmoothForm I 1 σ) (hdσ : mextDeriv σ = 0) (Ham : ℝ → M → ℝ)
    {u : ℝ × ℝ → M} (hu : IsSmoothBasedCap I γ u) :
    action σ Ham ⟨u, hu⟩ hu.rawCap =
      cappedLoopAction σ Ham (fun t ↦ u (0, t)) (u ∘ Prod.map (fun s ↦ 1 - s) id) := by
  rw [hu.cappedLoopAction_comp_prodMap_one_sub hσ hdσ, action_def]
  congr 1
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le zero_le_one] at ht
  simp only [γ.extend_apply ht, hu.apply_zero ⟨t, ht⟩]

/-- **The recapping law.** Gluing a sphere `a ∈ π₂(M, x)` to a raw cap, with the orientation of
the cap, lowers the action by the integral of a closed `C¹` two-form over `a`. -/
theorem action_vadd (hσ : IsSmoothForm I 1 σ) (hdσ : mextDeriv σ = 0) (Ham : ℝ → M → ℝ)
    (h : ∃ u, IsSmoothBasedCap I γ u) (a : Additive (π_ 2 M x)) (D : RawCap γ) :
    action σ Ham h (a +ᵥ D) = -sphereIntegralHom x hσ hdσ a + action σ Ham h D := by
  rw [action_def, action_def, RawCap.area_vadd hσ hdσ h]
  ring

/-- **Two raw caps differ by a sphere.** The actions of two raw caps of `γ` differ by minus the
integral of a closed `C¹` two-form over the sphere by which they differ. -/
theorem action_sub_action (hσ : IsSmoothForm I 1 σ) (hdσ : mextDeriv σ = 0) (Ham : ℝ → M → ℝ)
    (h : ∃ u, IsSmoothBasedCap I γ u) (D' D : RawCap γ) :
    action σ Ham h D' - action σ Ham h D = -sphereIntegralHom x hσ hdσ (D' -ᵥ D) := by
  rw [action_def, action_def, ← RawCap.area_sub_area hσ hdσ h]
  ring

/-- **The action does not depend on the cap when the form vanishes on spheres**, as for a
symplectically aspherical form. -/
theorem action_eq_action_of_vanishesOnSpheres (hσ : IsSmoothForm I 1 σ) (hdσ : mextDeriv σ = 0)
    (hS : VanishesOnSpheres σ) (Ham : ℝ → M → ℝ) (h : ∃ u, IsSmoothBasedCap I γ u)
    (D' D : RawCap γ) : action σ Ham h D' = action σ Ham h D := by
  rw [← sub_eq_zero, action_sub_action hσ hdσ, sphereIntegralHom_apply,
    hS.sphereIntegral_eq_zero, neg_zero]

/-- **Normalization.** Adding a function `f` of time to the Hamiltonian adds `∫₀¹ f` to the
action, for an integrable `f` and a Hamiltonian that is integrable along `γ`. -/
theorem action_add_const (σ : RoughForm I M ℝ 2) {Ham : ℝ → M → ℝ} {f : ℝ → ℝ}
    (hHam : IntervalIntegrable (fun t ↦ Ham t (γ.extend t)) MeasureTheory.volume 0 1)
    (hf : IntervalIntegrable f MeasureTheory.volume 0 1) (h : ∃ u, IsSmoothBasedCap I γ u)
    (D : RawCap γ) :
    action σ (fun t y ↦ Ham t y + f t) h D = action σ Ham h D + ∫ t in 0..1, f t := by
  rw [action_def, action_def, intervalIntegral.integral_add hHam hf]
  ring

end RawCap

end Raw

/-! ### The action of a cap class -/

namespace SphericalCapClass

open AlgebraicTopology

-- `ω` names the area homomorphism here, so the `ContDiff` scope, whose notation includes `ω`, is
-- not opened, and smoothness `∞` is written out.
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [CompactSpace M] [T2Space M] {x : M} {γ : Ω M x}
  {σ : RoughForm I M ℝ 2} {hσ : IsSmoothForm I 1 σ} {hdσ : mextDeriv σ = 0}
  {ω : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of M) →+ ℝ}
  {c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of M) →+ ℤ}

/-- The **capped action** of a loop `γ` with a cap class, for a closed `C¹` two-form `σ`, a
time-dependent Hamiltonian `Ham` and a homomorphism `ω` on `H₂(M; ℤ)` that agrees with the
integral of `σ` on the Hurewicz classes of spheres (`hω`): the action of any raw cap in the class.
It is well defined because raw caps in the same class differ by a sphere whose Hurewicz class has
zero `ω`, hence zero integral. -/
def action (hσ : IsSmoothForm I 1 σ) (hdσ : mextDeriv σ = 0)
    (hω : ∀ a, ω (hurewiczIntHom M x 1 a) = sphereIntegralHom x hσ hdσ a) (Ham : ℝ → M → ℝ)
    (h : ∃ u, IsSmoothBasedCap I γ u) : SphericalCapClass ω c γ → ℝ :=
  lift (-PeriodGroup.area _ _) (RawCap.action σ Ham h) fun a D ↦ by
    rw [RawCap.action_vadd hσ hdσ, AddMonoidHom.neg_apply,
      SphericalPeriodGroup.area_ofHomotopyGroup, hω]

variable (hω : ∀ a, ω (hurewiczIntHom M x 1 a) = sphereIntegralHom x hσ hdσ a)
  (Ham : ℝ → M → ℝ) (h : ∃ u, IsSmoothBasedCap I γ u)

/-- The action of the cap class of a raw cap is the action of the raw cap. -/
@[simp]
theorem action_mk (D : RawCap γ) : action hσ hdσ hω Ham h (mk ω c D) = RawCap.action σ Ham h D :=
  lift_mk _ _ _ D

/-- **Two cap classes differ by a class of the period group.** The actions of two cap classes of
`γ` differ by minus the area of the class by which they differ. -/
theorem action_sub_action (q' q : SphericalCapClass ω c γ) :
    action hσ hdσ hω Ham h q' - action hσ hdσ hω Ham h q = -PeriodGroup.area _ _ (q' -ᵥ q) := by
  induction q' using induction_on with | h D' =>
  induction q using induction_on with
  | h D => rw [action_mk, action_mk, mk_vsub_mk, SphericalPeriodGroup.area_ofHomotopyGroup, hω,
      RawCap.action_sub_action hσ hdσ]

variable [PathConnectedSpace M]

/-- **The recapping law on cap classes.** Recapping a cap class by a class `B` of the period group
lowers its action by the area of `B`. -/
@[simp]
theorem action_vadd (B : SphericalPeriodGroup ω c) (q : SphericalCapClass ω c γ) :
    action hσ hdσ hω Ham h (B +ᵥ q) = -PeriodGroup.area _ _ B + action hσ hdσ hω Ham h q :=
  lift_vadd _ _ _ B q

/-- **A cap class is determined by its action when the area is injective on the period group**, as
when the first Chern number vanishes on spherical classes
(`TauCeti.Floer.PeriodGroup.area_injective_of_chern_eq_zero`). -/
theorem action_injective
    (hinj : Function.Injective (PeriodGroup.area _ _ : SphericalPeriodGroup ω c →+ ℝ)) :
    Function.Injective (action (c := c) hσ hdσ hω Ham h) := by
  have : Nonempty (RawCap γ) := ⟨h.choose_spec.rawCap⟩
  refine AddTorsor.injective_of_forall_vadd_eq_add (δ := -PeriodGroup.area _ _)
    (action_vadd hω Ham h) fun B B' hB ↦ hinj ?_
  simpa using hB

end SphericalCapClass

end TauCeti.Floer

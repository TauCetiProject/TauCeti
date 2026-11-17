/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Area

/-!
# The area and the capped action of cap classes

Let `M` be a compact boundaryless manifold, `φ` a closed real `C¹` two-form on `M`, for instance
the symplectic form of a closed symplectic manifold, and `γ` a loop in `M` based at `x` with a
smooth based cap. The cap classes of `γ` (`TauCeti.Floer.SphericalCapClass ω c γ`) are its raw caps
modulo spheres whose Hurewicz classes lie in the joint kernel of homomorphisms
`ω : H₂(M; ℤ) → ℝ` and `c : H₂(M; ℤ) → ℤ`, and they form a torsor under the spherical period group
`Γ = TauCeti.Floer.SphericalPeriodGroup ω c`. This file attaches the symplectic area of raw caps
(`TauCeti.Floer.RawCap.area`) to these cap classes, and with it the capped action of
Hamiltonian Floer theory.

The homomorphisms `ω` and `c` are arbitrary, so the area of raw caps descends to cap classes only
when `ω` measures the area of spheres: throughout, `ω` is assumed to take the value
`∫_a φ = TauCeti.sphereIntegral φ x a` on the Hurewicz class of every sphere `a ∈ π₂(M, x)`. This
is the statement that `ω` is the evaluation of the de Rham class of `φ` on spherical classes. On a
simply connected target the Hurewicz map `π₂(M, x) → H₂(M; ℤ)` is an isomorphism, and
`TauCeti.homologySphereIntegralHom` is such an `ω`
(`TauCeti.homologySphereIntegralHom_hurewiczIntHom`).

* **The area of a cap class.** `SphericalCapClass.area ω c φ h q` is the area of any representative
  of `q` (`TauCeti.Floer.SphericalCapClass.area_mk`). For the class of a smooth based cap `u` it is
  the integral of `φ` over `u` (`TauCeti.Floer.SphericalCapClass.area_mk_homotopyClass`).
* **Recapping.** Recapping by `g ∈ Γ` adds the area of `g`,
  `area (g +ᵥ q) = area g + area q` (`TauCeti.Floer.SphericalCapClass.area_vadd`), and the areas
  of two cap classes differ by the area of the class by which they differ
  (`TauCeti.Floer.SphericalCapClass.area_sub_area`).
* **Gluing a cylinder.** Gluing a smooth based homotopy `w` from `γ₀` to `γ` to a cap class of
  `γ` adds the integral of `φ` over `w` (`TauCeti.Floer.SphericalCapClass.area_glue`).

For a Hamiltonian `Ham : ℝ → M → ℝ`, the **capped action** of `γ` with cap class `q` is

`SphericalCapClass.action ω c φ Ham h q = -area q + ∫₀¹ Ham(t, γ(t)) dt`.

The area of a raw cap is measured with the disc oriented from `γ` to its centre, so for the class
of a smooth based cap `u` this is the capped action `TauCeti.cappedLoopAction` of `γ` with the disc
`u` run backwards, from its centre to `γ`
(`TauCeti.Floer.SphericalCapClass.action_mk_homotopyClass`). With the same orientation, gluing a
sphere at the centre of a raw cap (`TauCeti.Floer.RawCap.instAddAction`) subtracts its area from
the action: `action (g +ᵥ q) = -area g + action q`
(`TauCeti.Floer.SphericalCapClass.action_vadd`). So the action obeys the recapping law of
`TauCeti.Geometry.Symplectic.Floer.Cap.Basic` for the homomorphism `-PeriodGroup.area` on `Γ`. In
the notation `A_H(x, D + B) = A_H(x, D) + ω(B)` of capped Floer theory, the sphere `B` is glued to
the disc oriented from its centre, and corresponds to `-g`.

A cap class is determined by its action and the first Chern number of the class by which it
differs from another (`TauCeti.Floer.SphericalCapClass.eq_iff_action_eq_and_chern_eq`). When the
first Chern number vanishes on spheres, as on the spherical-`c₁`-zero targets of capped Floer
theory, the action alone determines the cap class
(`TauCeti.Floer.SphericalCapClass.action_injective`).

## Main definitions

* `TauCeti.Floer.SphericalCapClass.area ω c φ h`: the area of the cap classes of a loop with a
  smooth based cap (`h`).
* `TauCeti.Floer.SphericalCapClass.action ω c φ Ham h`: the capped action of the cap classes of a
  loop with a smooth based cap, for the Hamiltonian `Ham`.

## Main results

* `TauCeti.Floer.SphericalCapClass.area_mk`, `TauCeti.Floer.SphericalCapClass.area_vadd`,
  `TauCeti.Floer.SphericalCapClass.area_sub_area`, `TauCeti.Floer.SphericalCapClass.area_glue`:
  the area of cap classes and its recapping and gluing laws.
* `TauCeti.Floer.SphericalCapClass.action_mk_homotopyClass`: the capped action of the class of a
  smooth based cap is `TauCeti.cappedLoopAction`.
* `TauCeti.Floer.SphericalCapClass.action_vadd`,
  `TauCeti.Floer.SphericalCapClass.action_sub_action`,
  `TauCeti.Floer.SphericalCapClass.action_glue`: the recapping and gluing laws of the capped action.
* `TauCeti.Floer.SphericalCapClass.eq_iff_action_eq_and_chern_eq`,
  `TauCeti.Floer.SphericalCapClass.action_injective`: cap classes are determined by their action
  and Chern numbers.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, on the action of capped loops and its recapping law.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  Section 11.1 (the symplectic area of spherical classes and capped loops).
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology HomotopyGroup
open scoped Manifold Topology Topology.Homotopy

namespace TauCeti.Floer.SphericalCapClass

variable {E H : Type*} {M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I (⊤ : ℕ∞) M] [CompactSpace M]
  [T2Space M]
  {ω : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of M) →+ ℝ}
  {c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of M) →+ ℤ}
  {φ : RoughForm I M ℝ 2} {x : M} {γ γ₀ : Ω M x}

/-! ### The area of a cap class -/

variable (ω c) in
/-- The **area** of a cap class `q` of a loop `γ` with a smooth based cap (`h`), for a two-form
`φ`: the area `TauCeti.Floer.RawCap.area` of a representative of `q`. When `φ` is closed and `ω`
is its area on spheres, it does not depend on the representative
(`TauCeti.Floer.SphericalCapClass.area_mk`). The cap is oriented from `γ` to its centre. -/
def area (φ : RoughForm I M ℝ 2) (h : ∃ u, IsSmoothBasedCap I γ u)
    (q : SphericalCapClass ω c γ) : ℝ :=
  RawCap.area φ h (Quotient.out q)

/-- The area of a cap class is the area of a representative, when `ω` measures the integral of a
closed `C¹` two-form `φ` over spheres. -/
@[simp]
theorem area_mk (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0)
    (hω : ∀ a, ω (hurewiczIntHom M x 1 a) = sphereIntegral φ x a.toMul)
    (h : ∃ u, IsSmoothBasedCap I γ u) (D : RawCap γ) :
    area ω c φ h (mk ω c D) = RawCap.area φ h D := by
  have hD : mk ω c (Quotient.out (mk ω c D)) = mk ω c D := by
    rw [mk_def, mk_def]
    exact Quotient.out_eq' _
  rw [area, ← sub_eq_zero, RawCap.area_sub_area hφ hdφ h, sphereIntegralHom_apply, ← hω]
  exact (mk_eq_mk_iff.1 hD).1

/-- The area of the cap class of a smooth based cap `u` is the integral of a closed `C¹` two-form
over `u` on the unit square. -/
theorem area_mk_homotopyClass (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0)
    (hω : ∀ a, ω (hurewiczIntHom M x 1 a) = sphereIntegral φ x a.toMul)
    (h : ∃ u, IsSmoothBasedCap I γ u) {u : ℝ × ℝ → M} (hu : IsSmoothBasedCap I γ u) :
    area ω c φ h (mk ω c hu.homotopyClass) = rectangleIntegral φ u (0, 0) (1, 1) := by
  rw [area_mk hφ hdφ hω, RawCap.area_homotopyClass hφ hdφ h hu]

/-- **Two cap classes differ by a class of the period group.** The areas of two cap classes differ
by the area of the class of `Γ` by which they differ. -/
theorem area_sub_area (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0)
    (hω : ∀ a, ω (hurewiczIntHom M x 1 a) = sphereIntegral φ x a.toMul)
    (h : ∃ u, IsSmoothBasedCap I γ u) (q' q : SphericalCapClass ω c γ) :
    area ω c φ h q' - area ω c φ h q = PeriodGroup.area _ _ (q' -ᵥ q) := by
  induction q' using induction_on with | h D' =>
  induction q using induction_on with
  | h D => rw [area_mk hφ hdφ hω, area_mk hφ hdφ hω, RawCap.area_sub_area hφ hdφ h, mk_vsub_mk,
      SphericalPeriodGroup.area_ofHomotopyGroup, hω, sphereIntegralHom_apply]

/-- **The recapping law.** Recapping a cap class by a class `g` of the period group adds the area
of `g`. -/
@[simp]
theorem area_vadd [PathConnectedSpace M] (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0)
    (hω : ∀ a, ω (hurewiczIntHom M x 1 a) = sphereIntegral φ x a.toMul)
    (h : ∃ u, IsSmoothBasedCap I γ u) (g : SphericalPeriodGroup ω c)
    (q : SphericalCapClass ω c γ) :
    area ω c φ h (g +ᵥ q) = PeriodGroup.area _ _ g + area ω c φ h q := by
  have : Nonempty (RawCap γ) := ⟨h.choose_spec.homotopyClass⟩
  rw [← sub_eq_iff_eq_add, area_sub_area hφ hdφ hω h, vadd_vsub]

/-- **Gluing a smooth cylinder to a cap class.** Gluing a smooth based homotopy `w` from `γ₀` to
`γ` to a cap class of `γ` adds the integral of a closed `C¹` two-form over `w` to its area. -/
theorem area_glue (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0)
    (hω : ∀ a, ω (hurewiczIntHom M x 1 a) = sphereIntegral φ x a.toMul) {w : ℝ × ℝ → M}
    (hw : IsSmoothBasedHomotopy I γ₀ γ w) (h₀ : ∃ u, IsSmoothBasedCap I γ₀ u)
    (h : ∃ u, IsSmoothBasedCap I γ u) (q : SphericalCapClass ω c γ) :
    area ω c φ h₀ (glue hw.homotopyClass q) =
      rectangleIntegral φ w (0, 0) (1, 1) + area ω c φ h q := by
  induction q using induction_on with
  | h D => rw [glue_mk, area_mk hφ hdφ hω, area_mk hφ hdφ hω, RawCap.area_comp hφ hdφ hw h₀ h]

/-! ### The capped action of a cap class -/

variable (ω c) in
/-- The **capped action** of a loop `γ` with a smooth based cap (`h`) and a cap class `q`, for a
two-form `φ` and a Hamiltonian `Ham`: `-area q + ∫₀¹ Ham(t, γ(t)) dt`. The area is measured with the
disc oriented from `γ` to its centre, so this is the capped action `TauCeti.cappedLoopAction` with
the disc oriented from its centre to `γ`
(`TauCeti.Floer.SphericalCapClass.action_mk_homotopyClass`). -/
def action (φ : RoughForm I M ℝ 2) (Ham : ℝ → M → ℝ) (h : ∃ u, IsSmoothBasedCap I γ u)
    (q : SphericalCapClass ω c γ) : ℝ :=
  -area ω c φ h q + ∫ t in 0..1, Ham t (γ.extend t)

theorem action_def (φ : RoughForm I M ℝ 2) (Ham : ℝ → M → ℝ) (h : ∃ u, IsSmoothBasedCap I γ u)
    (q : SphericalCapClass ω c γ) :
    action ω c φ Ham h q = -area ω c φ h q + ∫ t in 0..1, Ham t (γ.extend t) :=
  (rfl)

/-- **The capped action of a smooth cap.** The capped action of the cap class of a smooth based
cap `u` of `γ` is the capped action `TauCeti.cappedLoopAction` of `γ` with the disc `u` run
backwards, from its centre to `γ`. -/
theorem action_mk_homotopyClass (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0)
    (hω : ∀ a, ω (hurewiczIntHom M x 1 a) = sphereIntegral φ x a.toMul) (Ham : ℝ → M → ℝ)
    (h : ∃ u, IsSmoothBasedCap I γ u) {u : ℝ × ℝ → M} (hu : IsSmoothBasedCap I γ u) :
    action ω c φ Ham h (mk ω c hu.homotopyClass) =
      cappedLoopAction φ Ham (fun t ↦ u (0, t)) (u ∘ Prod.map (fun s ↦ 1 - s) id) := by
  rw [IsSmoothBasedCap.cappedLoopAction_comp_prodMap_one_sub hφ hdφ Ham h hu, action_def,
    area_mk hφ hdφ hω]
  congr 1
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  rw [Path.extend_apply _ ht, ← hu.apply_zero ⟨t, ht⟩]

/-- **The recapping law of the capped action.** Recapping a cap class by a class `g` of the period
group subtracts the area of `g` from its capped action. -/
@[simp]
theorem action_vadd [PathConnectedSpace M] (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0)
    (hω : ∀ a, ω (hurewiczIntHom M x 1 a) = sphereIntegral φ x a.toMul) (Ham : ℝ → M → ℝ)
    (h : ∃ u, IsSmoothBasedCap I γ u) (g : SphericalPeriodGroup ω c)
    (q : SphericalCapClass ω c γ) :
    action ω c φ Ham h (g +ᵥ q) = -PeriodGroup.area _ _ g + action ω c φ Ham h q := by
  rw [action_def, action_def, area_vadd hφ hdφ hω]
  ring

/-- The capped actions of two cap classes differ by minus the area of the class of the period group
by which they differ. -/
theorem action_sub_action (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0)
    (hω : ∀ a, ω (hurewiczIntHom M x 1 a) = sphereIntegral φ x a.toMul) (Ham : ℝ → M → ℝ)
    (h : ∃ u, IsSmoothBasedCap I γ u) (q' q : SphericalCapClass ω c γ) :
    action ω c φ Ham h q' - action ω c φ Ham h q = -PeriodGroup.area _ _ (q' -ᵥ q) := by
  rw [action_def, action_def, ← area_sub_area hφ hdφ hω h]
  ring

/-- **Transport of the capped action along a smooth cylinder.** Gluing a smooth based homotopy `w`
from `γ₀` to `γ` to a cap class of `γ` changes its capped action by minus the integral of `φ` over
`w`, and by the change of the Hamiltonian term from `γ` to `γ₀`. -/
theorem action_glue (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0)
    (hω : ∀ a, ω (hurewiczIntHom M x 1 a) = sphereIntegral φ x a.toMul) (Ham : ℝ → M → ℝ)
    {w : ℝ × ℝ → M} (hw : IsSmoothBasedHomotopy I γ₀ γ w) (h₀ : ∃ u, IsSmoothBasedCap I γ₀ u)
    (h : ∃ u, IsSmoothBasedCap I γ u) (q : SphericalCapClass ω c γ) :
    action ω c φ Ham h₀ (glue hw.homotopyClass q) =
      action ω c φ Ham h q - rectangleIntegral φ w (0, 0) (1, 1) +
        ((∫ t in 0..1, Ham t (γ₀.extend t)) - ∫ t in 0..1, Ham t (γ.extend t)) := by
  rw [action_def, action_def, area_glue hφ hdφ hω hw h₀ h]
  ring

/-- **A cap class is determined by its action and Chern number.** Two cap classes of a loop on a
path-connected manifold are equal exactly when they have the same capped action and the class of
the period group by which they differ has zero first Chern number. -/
theorem eq_iff_action_eq_and_chern_eq [PathConnectedSpace M] (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) (hω : ∀ a, ω (hurewiczIntHom M x 1 a) = sphereIntegral φ x a.toMul)
    (Ham : ℝ → M → ℝ) (h : ∃ u, IsSmoothBasedCap I γ u) {q q' : SphericalCapClass ω c γ} :
    q' = q ↔
      action ω c φ Ham h q' = action ω c φ Ham h q ∧ PeriodGroup.chern _ _ (q' -ᵥ q) = 0 := by
  have : Nonempty (RawCap γ) := ⟨h.choose_spec.homotopyClass⟩
  refine ⟨fun hq ↦ by simp [hq], fun ⟨ha, hc⟩ ↦ ?_⟩
  rw [← sub_eq_zero, action_sub_action hφ hdφ hω, neg_eq_zero] at ha
  rw [← vsub_eq_zero_iff_eq (G := SphericalPeriodGroup ω c)]
  exact PeriodGroup.ext (by rw [ha, map_zero]) (by rw [hc, map_zero])

/-- **When the first Chern number vanishes on spheres, a cap class is determined by its action.**
This is the case of the spherical-`c₁`-zero targets of capped Floer theory. -/
theorem action_injective [PathConnectedSpace M] (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) (hω : ∀ a, ω (hurewiczIntHom M x 1 a) = sphereIntegral φ x a.toMul)
    (hc : ∀ a, c (hurewiczIntHom M x 1 a) = 0) (Ham : ℝ → M → ℝ)
    (h : ∃ u, IsSmoothBasedCap I γ u) :
    Function.Injective (action ω c φ Ham h : SphericalCapClass ω c γ → ℝ) := by
  have : Nonempty (RawCap γ) := ⟨h.choose_spec.homotopyClass⟩
  intro q' q hq
  refine (eq_iff_action_eq_and_chern_eq hφ hdφ hω Ham h).2 ⟨hq, ?_⟩
  obtain ⟨a, ha⟩ := SphericalPeriodGroup.ofHomotopyGroup_surjective (ω := ω) (c := c) x (q' -ᵥ q)
  rw [← ha, SphericalPeriodGroup.chern_ofHomotopyGroup, hc]

end TauCeti.Floer.SphericalCapClass

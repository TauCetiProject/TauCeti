/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.AddBasepoint
public import TauCeti.LowDimTopology.Heegaard.Summand

/-!
# Adding a basepoint and the `ε`-classes

Adding a basepoint doubles the generators, `(x, 0)` and `(x, 1)` for each generator `x`, and these
two lie in the same `ε`-class
(`TauCeti.HeegaardRegionSystem.epsilonClass_addBasepointGenerator_eq_iff`), so adding a basepoint
identifies the `ε`-classes (`TauCeti.HeegaardRegionSystem.EpsilonClass`) of the two diagrams
(`TauCeti.HeegaardRegionSystem.addBasepointEpsilonClassEquiv`).

## Main definitions

* `TauCeti.HeegaardRegionSystem.addBasepointEpsilonClassEquiv`: the identification of the
  `ε`-classes of a diagram with those of the diagram with an added basepoint.

## Main results

* `TauCeti.HeegaardRegionSystem.epsilonClass_addBasepointGenerator_eq_iff`: adding a basepoint
  preserves and reflects lying in the same `ε`-class, whatever the new points.
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  (H : HeegaardRegionSystem n Point Region Basepoint)

section AddBasepoint

variable (r₀ : Region)

/-- Adding a basepoint does not change the `ε`-classes: the generators `(x, i)` and `(y, j)` of
the diagram with an added basepoint lie in the same class exactly when `x` and `y` lie in the same
class, whatever the new points `i` and `j`. -/
@[simp]
theorem epsilonClass_addBasepointGenerator_eq_iff {x y : H.Generator} {i j : Fin 2} :
    (H.addBasepoint r₀).epsilonClass (H.addBasepointGenerator r₀ x i) =
        (H.addBasepoint r₀).epsilonClass (H.addBasepointGenerator r₀ y j) ↔
      H.epsilonClass x = H.epsilonClass y := by
  simp only [epsilonClass_eq_epsilonClass_iff_exists_isDomainBetween,
    isDomainBetween_addBasepoint_iff]
  refine ⟨fun ⟨D, hD, _⟩ => ⟨_, hD⟩, fun ⟨D, hD⟩ => ⟨Sum.elim D ![D r₀ + (j - i), 0, 0], ?_⟩⟩
  simpa using hD

/-- The identification of the `ε`-classes of a diagram with those of the diagram with an added
basepoint, sending the class of `x` to the common class of `(x, 0)` and `(x, 1)`. -/
noncomputable def addBasepointEpsilonClassEquiv :
    H.EpsilonClass ≃ (H.addBasepoint r₀).EpsilonClass :=
  Equiv.ofBijective
    (EpsilonClass.lift
      (fun x => (H.addBasepoint r₀).epsilonClass (H.addBasepointGenerator r₀ x 0))
      fun _ _ => (H.epsilonClass_addBasepointGenerator_eq_iff r₀).mpr)
    ⟨fun c d => by
      induction c using EpsilonClass.ind with
      | h x =>
        induction d using EpsilonClass.ind with
        | h y =>
          rw [EpsilonClass.lift_epsilonClass, EpsilonClass.lift_epsilonClass]
          exact (H.epsilonClass_addBasepointGenerator_eq_iff r₀).mp,
    fun c => by
      induction c using EpsilonClass.ind with
      | h g =>
        obtain ⟨⟨x, k⟩, rfl⟩ := (H.addBasepointGeneratorEquiv r₀).surjective g
        rw [addBasepointGeneratorEquiv_apply]
        exact ⟨H.epsilonClass x, (EpsilonClass.lift_epsilonClass _ _ x).trans
          ((H.epsilonClass_addBasepointGenerator_eq_iff r₀).mpr rfl)⟩⟩

/-- The identification sends the class of `x` to the class of `(x, k)`, for either new point
`k`. -/
theorem addBasepointEpsilonClassEquiv_epsilonClass (x : H.Generator) (k : Fin 2) :
    H.addBasepointEpsilonClassEquiv r₀ (H.epsilonClass x) =
      (H.addBasepoint r₀).epsilonClass (H.addBasepointGenerator r₀ x k) :=
  (EpsilonClass.lift_epsilonClass _ _ x).trans
    ((H.epsilonClass_addBasepointGenerator_eq_iff r₀).mpr rfl)

/-- The identification sends the class of `x` to the class of `(x, 0)`. This is the case `k = 0`
of `addBasepointEpsilonClassEquiv_epsilonClass`, stated for `simp`. -/
@[simp]
theorem addBasepointEpsilonClassEquiv_epsilonClass_zero (x : H.Generator) :
    H.addBasepointEpsilonClassEquiv r₀ (H.epsilonClass x) =
      (H.addBasepoint r₀).epsilonClass (H.addBasepointGenerator r₀ x 0) :=
  H.addBasepointEpsilonClassEquiv_epsilonClass r₀ x 0

end AddBasepoint

end HeegaardRegionSystem

end TauCeti

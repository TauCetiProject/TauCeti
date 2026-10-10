/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.SerreFibration.Basic

/-!
# Hurewicz fibrations

A map `p : E → B` is a **Hurewicz fibration** when it has the homotopy lifting property
(`TauCeti.HasHomotopyLiftingProperty`) with respect to every space.  A proposition cannot quantify
over the spaces of all universes, so `TauCeti.IsHurewiczFibration.{w} p` asks for the homotopy
lifting property with respect to every space in the universe `w`; the property for a universe
implies it for every smaller one (`TauCeti.IsHurewiczFibration.down`), since the homotopy lifting
property depends on the space only up to homeomorphism.

Every Hurewicz fibration is a Serre fibration (`TauCeti.IsHurewiczFibration.mem_serreFibrations`),
since the cubes are test spaces.  Homeomorphisms and product projections are Hurewicz fibrations,
and Hurewicz fibrations are closed under composition and base change.

## Main definitions

* `TauCeti.IsHurewiczFibration.{w} p`: the homotopy lifting property with respect to every space
  in the universe `w`.

## Main results

* `TauCeti.isHurewiczFibration_iff`: the characterization by the homotopy lifting property.
* `TauCeti.IsHurewiczFibration.mem_serreFibrations`: a Hurewicz fibration is a Serre fibration.
* `TauCeti.IsHurewiczFibration.comp`: Hurewicz fibrations are closed under composition.
* `TauCeti.IsHurewiczFibration.pullback`: the base change of a Hurewicz fibration along any map is
  a Hurewicz fibration.
* `Homeomorph.isHurewiczFibration`, `TauCeti.isHurewiczFibration_fst`: homeomorphisms and product
  projections are Hurewicz fibrations.

## References

* W. Hurewicz, *On the concept of fiber space*, Proc. Nat. Acad. Sci. 41 (1955), 956–961.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter I.7.
-/

public section

open unitInterval

universe w w' u v u' v'

namespace TauCeti

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}
  {A : Type w} [TopologicalSpace A]

/-- A map `p : E → B` is a **Hurewicz fibration**, for test spaces in the universe `w`, when it has
the homotopy lifting property with respect to every space in `Type w`. -/
def IsHurewiczFibration.{w₀, u₀, v₀} {E : Type u₀} {B : Type v₀} [TopologicalSpace E]
    [TopologicalSpace B] (p : E → B) : Prop :=
  ∀ (A : Type w₀) [TopologicalSpace A], HasHomotopyLiftingProperty p A

/-- A map is a Hurewicz fibration, for test spaces in the universe `w`, if and only if it has the
homotopy lifting property with respect to every space in `Type w`. -/
theorem isHurewiczFibration_iff :
    IsHurewiczFibration.{w} p ↔
      ∀ (A : Type w) [TopologicalSpace A], HasHomotopyLiftingProperty p A :=
  Iff.rfl

namespace IsHurewiczFibration

/-- A Hurewicz fibration has the homotopy lifting property with respect to each test space. -/
theorem hasHomotopyLiftingProperty (h : IsHurewiczFibration.{w} p) (A : Type w)
    [TopologicalSpace A] : HasHomotopyLiftingProperty p A :=
  h A

/-- A Hurewicz fibration for test spaces in a universe is one for every smaller universe. -/
theorem down (h : IsHurewiczFibration.{max w w'} p) : IsHurewiczFibration.{w} p :=
  fun A _ ↦ (Homeomorph.ulift.{w'} : ULift A ≃ₜ A).hasHomotopyLiftingProperty_iff.1
    (h (ULift.{w'} A))

/-- A Hurewicz fibration is a Serre fibration: the cubes `Iⁿ` are among the test spaces. -/
theorem mem_serreFibrations {E B : _root_.TopCat.{u}} {p : E ⟶ B}
    (h : IsHurewiczFibration.{w} p) : TopCat.serreFibrations p :=
  TopCat.mem_serreFibrations_iff_cube.2 fun n ↦ (h.down : IsHurewiczFibration.{0} p) (Fin n → I)

/-- Hurewicz fibrations are closed under composition. -/
theorem comp {C : Type v'} [TopologicalSpace C] {q : B → C} (hq : IsHurewiczFibration.{w} q)
    (hp : IsHurewiczFibration.{w} p) (hpc : Continuous p) : IsHurewiczFibration.{w} (q ∘ p) :=
  fun A _ ↦ (hq A).comp (hp A) hpc

/-- The base change of a Hurewicz fibration along any continuous map is a Hurewicz fibration. -/
theorem pullback {B' : Type v'} [TopologicalSpace B'] (hp : IsHurewiczFibration.{w} p)
    (g : C(B', B)) :
    IsHurewiczFibration.{w} (fun x : {x : B' × E // g x.1 = p x.2} ↦ x.1.1) :=
  fun A _ ↦ (hp A).pullback g

/-- Precomposing a Hurewicz fibration with a homeomorphism gives a Hurewicz fibration. -/
theorem comp_homeomorph {E' : Type u'} [TopologicalSpace E'] (hp : IsHurewiczFibration.{w} p)
    (e : E' ≃ₜ E) : IsHurewiczFibration.{w} (p ∘ e) :=
  hp.comp (fun A _ ↦ e.hasHomotopyLiftingProperty A) e.continuous

end IsHurewiczFibration

/-- A homeomorphism is a Hurewicz fibration. -/
theorem _root_.Homeomorph.isHurewiczFibration (e : E ≃ₜ B) : IsHurewiczFibration.{w} e :=
  fun A _ ↦ e.hasHomotopyLiftingProperty A

/-- The projection `B × F → B` is a Hurewicz fibration. -/
theorem isHurewiczFibration_fst (F : Type u') [TopologicalSpace F] :
    IsHurewiczFibration.{w} (Prod.fst : B × F → B) :=
  fun A _ ↦ hasHomotopyLiftingProperty_fst F A

end TauCeti

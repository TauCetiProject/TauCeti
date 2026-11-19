/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Maps.OpenQuotient
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Algebra.ConstMulAction
import TauCeti.Topology.Algebra.ProperAction.Basic

/-!
# The orbit space of a representation

For a representation `ρ` of a group `G` on `V`, `Representation.orbitRel ρ` is the equivalence
relation on `V` whose classes are the orbits `{ρ g v | g ∈ G}`. Its quotient
`Quotient ρ.orbitRel` is the orbit space `V / G`, with the quotient topology when `V` is a
topological space.

The action of `G` on `V` through `ρ` is not registered as a `MulAction` instance, since it would
compete with other actions on `V`: for instance the units `kˣ` of the scalars already act on `V` by
scalar multiplication, and a representation of `kˣ` need not be that action. So
`Representation.orbitRel ρ` is defined as Mathlib's `MulAction.orbitRel` for the action
`MulAction.compHom V ρ`, and the results below restate Mathlib's orbit-space topology for that
action with hypotheses on `ρ` itself.

* When every `ρ g` is continuous, the quotient map `V → V / G` is open
  (`Representation.isOpenQuotientMap_orbitRel_mk`), by `MulAction.isOpenQuotientMap_quotientMk`.
* When `G` is a compact space and the action `(g, v) ↦ ρ g v` is jointly continuous, the quotient
  map is also closed (`Representation.isClosedMap_orbitRel_mk`), because the saturation of a closed
  set `A` is the projection to `V` of the closed set `{(g, v) | ρ g v ∈ A}` of `G × V`, and the
  projection `G × V → V` is a closed map. Its fibres are orbits, continuous images of `G`, so the
  quotient map is proper (`Representation.isProperMap_orbitRel_mk`). If moreover `V` is Hausdorff,
  the action is proper, so the orbit space is Hausdorff
  (`Representation.t2Space_quotient_orbitRel`).

These are the facts behind the identification of the adjoint orbit space of a compact Lie group
with the quotient of the Lie algebra of a maximal torus by the Weyl group, in
`TauCeti.Geometry.Lie.Subgroup.Weyl.OrbitSpace`.

## References

* N. Bourbaki, *General Topology*, Chapter III, § 4, for quotients of spaces by compact groups.
-/

public section

open Set

namespace Representation

variable {k G V : Type*} [Semiring k] [Group G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V)

/-! ### The orbit relation -/

/-- **The orbit relation of a representation.** Two vectors are related when some group element
carries the second to the first; the classes are the orbits `{ρ g v | g ∈ G}`. This is
`MulAction.orbitRel` for the action `MulAction.compHom V ρ` of `G` through `ρ`, so as there,
`v ≈ w` means that `v` lies in the orbit of `w`. -/
def orbitRel : Setoid V :=
  letI := MulAction.compHom V ρ
  MulAction.orbitRel G V

theorem orbitRel_apply {v w : V} : ρ.orbitRel v w ↔ ∃ g : G, ρ g w = v :=
  Iff.rfl

/-- Two vectors have the same class in the orbit space exactly when some group element carries
the second to the first. -/
theorem orbitRel_mk_eq_mk_iff {v w : V} :
    Quotient.mk ρ.orbitRel v = Quotient.mk ρ.orbitRel w ↔ ∃ g : G, ρ g w = v :=
  Quotient.eq

/-- The vector `ρ g v` has the class of `v` in the orbit space. -/
@[simp]
theorem orbitRel_mk_apply (g : G) (v : V) :
    Quotient.mk ρ.orbitRel (ρ g v) = Quotient.mk ρ.orbitRel v :=
  ρ.orbitRel_mk_eq_mk_iff.mpr ⟨g, rfl⟩

/-! ### Topology of the orbit space -/

section Topology

variable [TopologicalSpace V]

/-- **The orbit map of a representation by continuous operators is an open quotient map.** -/
theorem isOpenQuotientMap_orbitRel_mk (hρ : ∀ g : G, Continuous (ρ g)) :
    IsOpenQuotientMap (Quotient.mk ρ.orbitRel) :=
  letI := MulAction.compHom V ρ
  haveI : ContinuousConstSMul G V := ⟨hρ⟩
  MulAction.isOpenQuotientMap_quotientMk

variable [TopologicalSpace G] [CompactSpace G]

/-- **The orbit map of a compact group is closed.** For a jointly continuous representation of a
compact group, the saturation of a closed set `A` is the projection to `V` of the closed set
`{(g, v) | ρ g v ∈ A}`, and the projection `G × V → V` is a closed map. -/
theorem isClosedMap_orbitRel_mk (hρ : Continuous fun p : G × V ↦ ρ p.1 p.2) :
    IsClosedMap (Quotient.mk ρ.orbitRel) := fun A hA ↦ by
  rw [← (ρ.isOpenQuotientMap_orbitRel_mk fun g ↦ hρ.comp (Continuous.prodMk_right g))
    |>.isQuotientMap.isClosed_preimage]
  convert isClosedMap_snd_of_compactSpace _ (hA.preimage hρ)
  ext v
  simp only [mem_preimage, mem_image, orbitRel_mk_eq_mk_iff, Prod.exists]
  exact ⟨fun ⟨_, ha, g, hg⟩ ↦ ⟨g, v, hg ▸ ha, rfl⟩, fun ⟨g, _, ha, rfl⟩ ↦ ⟨_, ha, g, rfl⟩⟩

/-- **The orbit map of a compact group is proper.** For a jointly continuous representation of a
compact group, the orbit map is closed, and its fibres are orbits, which are compact as continuous
images of the group. -/
theorem isProperMap_orbitRel_mk (hρ : Continuous fun p : G × V ↦ ρ p.1 p.2) :
    IsProperMap (Quotient.mk ρ.orbitRel) := by
  refine isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨continuous_quotient_mk', ρ.isClosedMap_orbitRel_mk hρ, fun y ↦ ?_⟩
  induction y using Quotient.inductionOn with | h v => ?_
  convert isCompact_range (hρ.comp (Continuous.prodMk_left v))
  ext w
  exact ρ.orbitRel_mk_eq_mk_iff

/-- **The orbit space of a compact group acting on a Hausdorff space is Hausdorff.** A jointly
continuous action of a compact group on a Hausdorff space is proper. -/
theorem t2Space_quotient_orbitRel [T2Space V] (hρ : Continuous fun p : G × V ↦ ρ p.1 p.2) :
    T2Space (Quotient ρ.orbitRel) :=
  letI := MulAction.compHom V ρ
  haveI : ContinuousSMul G V := ⟨hρ⟩
  haveI := TauCeti.properSMul_of_compactSpace G V
  t2Space_quotient_mulAction_of_properSMul

end Topology

end Representation

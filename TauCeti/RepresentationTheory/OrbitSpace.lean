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
`MulAction.compHom V ρ` (`Representation.orbitRel_eq`), and the results below restate Mathlib's
orbit-space topology for that action with hypotheses on `ρ` itself.

* When every `ρ g` is continuous, the quotient map `V → V / G` is open
  (`Representation.isOpenQuotientMap_orbitRel_mk`), by `MulAction.isOpenQuotientMap_quotientMk`.
* When `G` is a compact space and the action `(g, v) ↦ ρ g v` is jointly continuous, the quotient
  map is also closed and proper (`Representation.isClosedMap_orbitRel_mk`,
  `Representation.isProperMap_orbitRel_mk`), by `MulAction.isClosedMap_quotientMk_of_compactSpace`
  and `MulAction.isProperMap_quotientMk_of_compactSpace`. If moreover `V` is Hausdorff, the action
  is proper, so the orbit space is Hausdorff (`Representation.t2Space_quotient_orbitRel`).

These are the facts behind the identification of the adjoint orbit space of a compact Lie group
with the quotient of the Lie algebra of a maximal torus by the Weyl group, in
`TauCeti.Geometry.Lie.Subgroup.Weyl.OrbitSpace`.

## References

* N. Bourbaki, *General Topology*, Chapter III, § 4, for quotients of spaces by compact groups.
-/

public section

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

/-- `Representation.orbitRel ρ` is Mathlib's `MulAction.orbitRel` for the action
`MulAction.compHom V ρ` of `G` through `ρ`. -/
theorem orbitRel_eq :
    letI := MulAction.compHom V ρ
    ρ.orbitRel = MulAction.orbitRel G V :=
  (rfl)

theorem orbitRel_apply {v w : V} : ρ.orbitRel v w ↔ ∃ g : G, ρ g w = v :=
  Iff.rfl

/-- Two vectors have the same class in the orbit space exactly when some group element carries
the second to the first. -/
theorem orbitRel_mk_eq_mk_iff {v w : V} :
    Quotient.mk ρ.orbitRel v = Quotient.mk ρ.orbitRel w ↔ ∃ g : G, ρ g w = v :=
  Quotient.eq.trans ρ.orbitRel_apply

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
compact group, the quotient map `V → V / G` is closed. -/
theorem isClosedMap_orbitRel_mk (hρ : Continuous fun p : G × V ↦ ρ p.1 p.2) :
    IsClosedMap (Quotient.mk ρ.orbitRel) :=
  letI := MulAction.compHom V ρ
  haveI : ContinuousSMul G V := ⟨hρ⟩
  MulAction.isClosedMap_quotientMk_of_compactSpace

/-- **The orbit map of a compact group is proper.** For a jointly continuous representation of a
compact group, the quotient map `V → V / G` is proper. -/
theorem isProperMap_orbitRel_mk (hρ : Continuous fun p : G × V ↦ ρ p.1 p.2) :
    IsProperMap (Quotient.mk ρ.orbitRel) :=
  letI := MulAction.compHom V ρ
  haveI : ContinuousSMul G V := ⟨hρ⟩
  MulAction.isProperMap_quotientMk_of_compactSpace

/-- **The orbit space of a compact group acting on a Hausdorff space is Hausdorff.** For a jointly
continuous representation of a compact group on a Hausdorff space, the orbit space `V / G` is
Hausdorff. -/
theorem t2Space_quotient_orbitRel [T2Space V] (hρ : Continuous fun p : G × V ↦ ρ p.1 p.2) :
    T2Space (Quotient ρ.orbitRel) :=
  letI := MulAction.compHom V ρ
  haveI : ContinuousSMul G V := ⟨hρ⟩
  haveI := TauCeti.properSMul_of_compactSpace G V
  t2Space_quotient_mulAction_of_properSMul

end Topology

end Representation

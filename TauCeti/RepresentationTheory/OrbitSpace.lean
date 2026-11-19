/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Maps.OpenQuotient
public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Maps.Proper.Basic

/-!
# The orbit space of a representation

For a representation `ρ` of a group `G` on `V`, `Representation.orbitRel ρ` is the equivalence
relation on `V` whose classes are the orbits `{ρ g v | g ∈ G}`. Its quotient
`Quotient ρ.orbitRel` is the orbit space `V / G`, with the quotient topology when `V` is a
topological space.

The action of `G` on `V` through `ρ` is not registered as a `MulAction` instance, since it would
compete with other actions on `V`: for instance the units `kˣ` of the scalars already act on `V` by
scalar multiplication, and a representation of `kˣ` need not be that action. So Mathlib's orbit
spaces `MulAction.orbitRel` do not apply directly, and this file proves the basic topology of the
orbit space of `ρ`.

* When every `ρ g` is continuous, the quotient map `V → V / G` is open
  (`Representation.isOpenQuotientMap_orbitRel_mk`): the saturation of an open set `U` is the union
  of its translates.
* When `G` is a compact space and the action `(g, v) ↦ ρ g v` is jointly continuous, the quotient
  map is also closed (`Representation.isClosedMap_orbitRel_mk`), because the saturation of a closed
  set `A` is the projection to `V` of the closed set `{(g, v) | ρ g v ∈ A}` of `G × V`, and the
  projection `G × V → V` is a closed map. If moreover `V` is Hausdorff, so is the orbit space
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
carries the second to the first; the classes are the orbits `{ρ g v | g ∈ G}`. As for
`MulAction.orbitRel`, `v ≈ w` means that `v` lies in the orbit of `w`. -/
def orbitRel : Setoid V where
  r v w := ∃ g : G, ρ g w = v
  iseqv :=
    { refl := fun v ↦ ⟨1, by simp⟩
      symm := fun {v w} ⟨g, h⟩ ↦ ⟨g⁻¹, by rw [← h, inv_self_apply]⟩
      trans := fun {u v w} ⟨g, hg⟩ ⟨h, hh⟩ ↦ ⟨g * h, by rw [map_mul, mul_apply_eq_comp, hh, hg]⟩ }

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

/-- The saturation of a set `A` under the orbit relation consists of the vectors that some group
element carries into `A`. -/
theorem preimage_image_orbitRel_mk (A : Set V) :
    Quotient.mk ρ.orbitRel ⁻¹' (Quotient.mk ρ.orbitRel '' A) = {v | ∃ g : G, ρ g v ∈ A} := by
  ext v
  simp only [mem_preimage, mem_image, mem_ofPred_eq, orbitRel_mk_eq_mk_iff]
  exact ⟨fun ⟨_, ha, g, hg⟩ ↦ ⟨g, hg ▸ ha⟩, fun ⟨g, hg⟩ ↦ ⟨_, hg, g, rfl⟩⟩

/-! ### Topology of the orbit space -/

section Topology

variable [TopologicalSpace V]

/-- **The orbit map of a representation by continuous operators is an open quotient map.** The
saturation of an open set `U` is the union of the open sets `(ρ g)⁻¹(U)`. -/
theorem isOpenQuotientMap_orbitRel_mk (hρ : ∀ g : G, Continuous (ρ g)) :
    IsOpenQuotientMap (Quotient.mk ρ.orbitRel) := by
  refine ⟨Quotient.mk_surjective, continuous_quotient_mk', fun U hU ↦ ?_⟩
  rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
  change IsOpen (Quotient.mk ρ.orbitRel ⁻¹' (Quotient.mk ρ.orbitRel '' U))
  rw [preimage_image_orbitRel_mk, ofPred_exists]
  exact isOpen_iUnion fun g ↦ hU.preimage (hρ g)

variable [TopologicalSpace G] [CompactSpace G]

/-- **The orbit map of a compact group is closed.** For a jointly continuous representation of a
compact group, the saturation of a closed set `A` is the projection to `V` of the closed set
`{(g, v) | ρ g v ∈ A}`, and the projection `G × V → V` is a closed map. -/
theorem isClosedMap_orbitRel_mk (hρ : Continuous fun p : G × V ↦ ρ p.1 p.2) :
    IsClosedMap (Quotient.mk ρ.orbitRel) := fun A hA ↦ by
  rw [← isQuotientMap_quotient_mk'.isClosed_preimage]
  change IsClosed (Quotient.mk ρ.orbitRel ⁻¹' (Quotient.mk ρ.orbitRel '' A))
  rw [preimage_image_orbitRel_mk]
  convert isClosedMap_snd_of_compactSpace _ (hA.preimage hρ)
  simp

/-- **The orbit space of a compact group acting on a Hausdorff space is Hausdorff.** The relation
`{(v, w) | ∃ g, ρ g w = v}` is the projection of the closed set
`{(g, v, w) | ρ g w = v}` of `G × V × V` along the compact factor `G`, so it is closed, and the
orbit map is an open quotient map. -/
theorem t2Space_quotient_orbitRel [T2Space V] (hρ : Continuous fun p : G × V ↦ ρ p.1 p.2) :
    T2Space (Quotient ρ.orbitRel) := by
  have hρg (g : G) : Continuous (ρ g) := hρ.comp (Continuous.prodMk_right g)
  rw [t2Space_iff_of_isOpenQuotientMap (ρ.isOpenQuotientMap_orbitRel_mk hρg)]
  have hclosed : IsClosed {p : G × (V × V) | ρ p.1 p.2.2 = p.2.1} :=
    isClosed_eq (hρ.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
      (continuous_fst.comp continuous_snd)
  convert isClosedMap_snd_of_compactSpace _ hclosed
  simp [orbitRel_mk_eq_mk_iff]

end Topology

end Representation

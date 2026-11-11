/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.IsLocalHomeomorph
public import TauCeti.CategoryTheory.Category.QuiverTotal
public import TauCeti.Topology.Maps.LocalSections

/-!
# Topological groupoids on total arrows

`TauCeti.IsTopologicalGroupoid` records continuity of the structure maps of a categorical
groupoid, with separate topologies on objects and total arrows. Composable pairs have the
subspace topology from the product of total-arrow spaces. There is no topology on individual
hom types and no separation assumption on the arrow space.

Inversion is a homeomorphism, units embed the object space, and openness of source and target
are equivalent, as is their being local homeomorphisms. These facts let smooth groupoids use the
same topology when their smooth structure is forgotten.

When the source is an open map, composition is open: every arrow near a composite `a ≫ b` is a
composite of an arrow near `a` with an arrow near `b` (`TauCeti.eventually_exists_comp_eq`). The
proof factors a nearby arrow through an arrow near `a` with the same source.

Composition follows categorical order: `a.comp b h` first traverses `a`, then `b`.
Thus the product written `gh` in the opposite, geometric order is `h.comp g`.

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.1.
-/

public section

open CategoryTheory Topology

namespace TauCeti

/-- A groupoid with continuous source, target, units, inversion and composition on the
subspace of composable pairs of total arrows. The topology on arrows is supplied separately;
it need not be the disjoint-union topology of the hom types. -/
class IsTopologicalGroupoid (C : Type*) [Category C] [IsGroupoid C] [TopologicalSpace C]
    [TopologicalSpace (Quiver.Total C)] : Prop where
  /-- Source is continuous. -/
  continuous_source : Continuous (Quiver.Total.left : Quiver.Total C → C)
  /-- Target is continuous. -/
  continuous_target : Continuous (Quiver.Total.right : Quiver.Total C → C)
  /-- Units are continuous. -/
  continuous_unit : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)
  /-- Inversion is continuous. -/
  continuous_inverse : Continuous fun a : Quiver.Total C ↦
    (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total C)
  /-- Composition is continuous on the subspace of composable pairs. -/
  continuous_comp : Continuous fun p :
    {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
      p.1.1.comp p.1.2 p.2

attribute [fun_prop] IsTopologicalGroupoid.continuous_source
  IsTopologicalGroupoid.continuous_target IsTopologicalGroupoid.continuous_unit
  IsTopologicalGroupoid.continuous_inverse IsTopologicalGroupoid.continuous_comp

namespace IsTopologicalGroupoid

variable (C : Type*) [Category C] [IsGroupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)]
  [IsTopologicalGroupoid C]

/-- Inversion exchanges source and target without changing the topology of the arrow space. -/
noncomputable def inverseHomeomorph : Quiver.Total C ≃ₜ Quiver.Total C where
  toFun a := ⟨a.right, a.left, inv a.hom⟩
  invFun a := ⟨a.right, a.left, inv a.hom⟩
  left_inv a := by cases a; simp
  right_inv a := by cases a; simp
  continuous_toFun := continuous_inverse
  continuous_invFun := continuous_inverse

@[simp]
theorem inverseHomeomorph_apply (a : Quiver.Total C) :
    inverseHomeomorph C a = ⟨a.right, a.left, inv a.hom⟩ := (rfl)

@[simp]
theorem inverseHomeomorph_symm_apply (a : Quiver.Total C) :
    (inverseHomeomorph C).symm a = ⟨a.right, a.left, inv a.hom⟩ := (rfl)

/-- The object topology is exactly the topology induced by the unit map. -/
theorem isEmbedding_unit :
    Topology.IsEmbedding (fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) :=
  Function.LeftInverse.isEmbedding (fun _ ↦ rfl) continuous_source continuous_unit

/-- Source is open if and only if target is open; neither is required by the definition
of a topological groupoid. -/
theorem isOpenMap_source_iff_target :
    IsOpenMap (Quiver.Total.left : Quiver.Total C → C) ↔
      IsOpenMap (Quiver.Total.right : Quiver.Total C → C) := by
  constructor <;> intro h
  · exact h.comp (inverseHomeomorph C).isOpenMap
  · exact h.comp (inverseHomeomorph C).isOpenMap

/-- Source is a local homeomorphism if and only if target is, since inversion exchanges them. -/
theorem isLocalHomeomorph_source_iff_target :
    IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C) ↔
      IsLocalHomeomorph (Quiver.Total.right : Quiver.Total C → C) := by
  constructor <;> intro h
  · exact h.comp (inverseHomeomorph C).isLocalHomeomorph
  · exact h.comp (inverseHomeomorph C).isLocalHomeomorph

/-- Continuous local source sections through every arrow make target open, by inversion.
Source itself is open by `IsOpenMap.of_local_sections`. For a Lie groupoid these sections
are supplied by the source-submersion charts. -/
theorem isOpenMap_target_of_local_source_sections
    (h : ∀ a : Quiver.Total C, ∃ σ : C → Quiver.Total C,
      ContinuousAt σ a.left ∧ σ a.left = a ∧
        (∀ᶠ x in 𝓝 a.left, (σ x).left = x)) :
    IsOpenMap (Quiver.Total.right : Quiver.Total C → C) :=
  (isOpenMap_source_iff_target C).mp (.of_local_sections h)

end IsTopologicalGroupoid

section OpenSource

variable {C : Type*} [Category C] [IsGroupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)] [IsTopologicalGroupoid C]

/-- **Composition is open when the source is open.** If the source is an open map, then every
arrow near a composite `a ≫ b` is the composite of an arrow near `a` with an arrow near `b`:
for neighbourhoods `A` of `a` and `B` of `b`, the composites of arrows of `A` with arrows of `B`
form a neighbourhood of `a ≫ b`. This applies in particular to étale groupoids. -/
theorem eventually_exists_comp_eq
    (hs : IsOpenMap (Quiver.Total.left : Quiver.Total C → C))
    {a b : Quiver.Total C} (h : a.right = b.left) {A B : Set (Quiver.Total C)} (hA : A ∈ 𝓝 a)
    (hB : B ∈ 𝓝 b) :
    ∀ᶠ c in 𝓝 (a.comp b h), ∃ a' ∈ A, ∃ b' ∈ B, ∃ h' : a'.right = b'.left, a'.comp b' h' = c := by
  -- For arrows `a'` and `c` with the same source, `Ψ` is the inverse of `a'` followed by `c`,
  -- so that `c` is `a'` followed by `Ψ`. It sends `(a, a ≫ b)` to `b`.
  let Ψ : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.left} → Quiver.Total C := fun p ↦
    (⟨p.1.1.right, p.1.1.left, inv p.1.1.hom⟩ : Quiver.Total C).comp p.1.2 p.2
  have hΨ : Continuous Ψ := IsTopologicalGroupoid.continuous_comp.comp
    (((IsTopologicalGroupoid.continuous_inverse.comp
      (continuous_fst.comp continuous_subtype_val)).prodMk
        (continuous_snd.comp continuous_subtype_val)).subtype_mk fun p ↦ p.2)
  let p₀ : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.left} :=
    ⟨(a, a.comp b h), (Quiver.Total.comp_left a b h).symm⟩
  have hΨp₀ : Ψ p₀ = b := Quiver.Total.inv_comp_comp a b h _
  -- Pairs `(a', c)` with `a'` in `A'` and `c` in `C'` are sent into `B` by `Ψ`.
  have hpre : Ψ ⁻¹' B ∈ 𝓝 p₀ := hΨ.continuousAt.preimage_mem_nhds (by rwa [hΨp₀])
  obtain ⟨u, hu, hsub⟩ := Filter.mem_comap.mp (nhds_induced Subtype.val p₀ ▸ hpre)
  obtain ⟨A', hA', C', hC', hprod⟩ := mem_nhds_prod_iff.mp hu
  -- Since the source is open, an arrow near `a ≫ b` has the source of some `a'` in `A ∩ A'`.
  have hL : Quiver.Total.left '' (A ∩ A') ∈ 𝓝 (a.comp b h).left := by
    rw [Quiver.Total.comp_left]
    exact hs.image_mem_nhds (Filter.inter_mem hA hA')
  filter_upwards [hC', IsTopologicalGroupoid.continuous_source.continuousAt.preimage_mem_nhds hL]
    with c hcC ⟨a', ⟨ha'A, ha'A'⟩, ha'c⟩
  exact ⟨a', ha'A, Ψ ⟨(a', c), ha'c⟩, hsub (hprod ⟨ha'A', hcC⟩),
    (Quiver.Total.comp_left (⟨a'.right, a'.left, inv a'.hom⟩ : Quiver.Total C) c ha'c).symm,
    Quiver.Total.comp_inv_comp a' c ha'c _⟩

end OpenSource

end TauCeti

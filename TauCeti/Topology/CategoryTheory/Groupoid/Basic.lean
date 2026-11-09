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

When the source is a local homeomorphism, composition is open: every arrow near a composite
`a ≫ b` is a composite of an arrow near `a` with an arrow near `b`
(`TauCeti.eventually_exists_comp_eq`). The proof factors a nearby arrow through a local section
of the source through `a`.

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

section Etale

variable {C : Type*} [Category C] [IsGroupoid C]

/-- Following `a` by the composite of its inverse with `c` gives back `c`. -/
private theorem comp_inv_comp (a c : Quiver.Total C) (h : a.left = c.left)
    (h' : a.right = ((⟨a.right, a.left, inv a.hom⟩ : Quiver.Total C).comp c h).left) :
    a.comp ((⟨a.right, a.left, inv a.hom⟩ : Quiver.Total C).comp c h) h' = c := by
  obtain ⟨x, y, f⟩ := a
  obtain ⟨x', z, g⟩ := c
  dsimp only at h
  subst h
  simp [Quiver.Total.comp_def]

/-- Following the inverse of `a` by the composite of `a` with `b` gives back `b`. -/
private theorem inv_comp_comp (a b : Quiver.Total C) (h : a.right = b.left)
    (h' : (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total C).right = (a.comp b h).left) :
    (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total C).comp (a.comp b h) h' = b := by
  obtain ⟨x, y, f⟩ := a
  obtain ⟨y', z, g⟩ := b
  dsimp only at h
  subst h
  simp [Quiver.Total.comp_def]

variable [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)] [IsTopologicalGroupoid C]

/-- **Composition is open in an étale groupoid.** If the source is a local homeomorphism, then
every arrow near a composite `a ≫ b` is the composite of an arrow near `a` with an arrow near `b`:
for neighbourhoods `A` of `a` and `B` of `b`, the composites of arrows of `A` with arrows of `B`
form a neighbourhood of `a ≫ b`. -/
theorem eventually_exists_comp_eq
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    {a b : Quiver.Total C} (h : a.right = b.left) {A B : Set (Quiver.Total C)} (hA : A ∈ 𝓝 a)
    (hB : B ∈ 𝓝 b) :
    ∀ᶠ c in 𝓝 (a.comp b h), ∃ a' ∈ A, ∃ b' ∈ B, ∃ h' : a'.right = b'.left, a'.comp b' h' = c := by
  obtain ⟨e, hae, he⟩ := hs a
  -- The inverse `e.symm` of the source near `a` is a continuous local section of the source.
  have hσl (y : C) (hy : y ∈ e.target) : (e.symm y).left = y := by
    rw [he]
    exact e.right_inv hy
  have hea : e a = a.left := by rw [he]
  have hσa : e.symm a.left = a := by
    rw [← hea]
    exact e.left_inv hae
  have hat : a.left ∈ e.target := hea ▸ e.map_source hae
  let D : Set (Quiver.Total C) := Quiver.Total.left ⁻¹' e.target
  have hD : IsOpen D := e.open_target.preimage IsTopologicalGroupoid.continuous_source
  have hcD : a.comp b h ∈ D := by
    simpa only [D, Set.mem_preimage, Quiver.Total.comp_left] using hat
  -- On `D`, an arrow `c` is `τ c` followed by `Ψ c`, the inverse of `τ c` followed by `c`.
  let τ : D → Quiver.Total C := fun c ↦ e.symm c.1.left
  have hτ : Continuous τ := e.continuousOn_symm.comp_continuous
    (IsTopologicalGroupoid.continuous_source.comp continuous_subtype_val) fun c ↦ c.2
  let Ψ : D → Quiver.Total C := fun c ↦
    (⟨(τ c).right, (τ c).left, inv (τ c).hom⟩ : Quiver.Total C).comp c.1 (hσl _ c.2)
  have hΨ : Continuous Ψ := IsTopologicalGroupoid.continuous_comp.comp
    (((IsTopologicalGroupoid.continuous_inverse.comp hτ).prodMk continuous_subtype_val).subtype_mk
      fun c ↦ hσl _ c.2)
  have hτc : τ ⟨_, hcD⟩ = a := by
    simp only [τ, Quiver.Total.comp_left, hσa]
  have hΨc : Ψ ⟨_, hcD⟩ = b :=
    (Quiver.Total.comp_congr (by rw [hτc]) rfl _ (Quiver.Total.comp_left _ _ _).symm).trans
      (inv_comp_comp a b h _)
  have hmap : Filter.map Subtype.val (𝓝 (⟨_, hcD⟩ : D)) = 𝓝 (a.comp b h) :=
    hD.isOpenMap_subtype_val.map_nhds_eq continuous_subtype_val.continuousAt
  rw [← hmap]
  refine Filter.eventually_map.2 ?_
  filter_upwards [hτ.continuousAt.preimage_mem_nhds (by rwa [hτc] : A ∈ 𝓝 (τ ⟨_, hcD⟩)),
    hΨ.continuousAt.preimage_mem_nhds (by rwa [hΨc] : B ∈ 𝓝 (Ψ ⟨_, hcD⟩))] with c hcA hcB
  exact ⟨τ c, hcA, Ψ c, hcB, (Quiver.Total.comp_left
    (⟨(τ c).right, (τ c).left, inv (τ c).hom⟩ : Quiver.Total C) c.1 (hσl _ c.2)).symm,
    comp_inv_comp _ _ (hσl _ c.2) _⟩

end Etale

end TauCeti

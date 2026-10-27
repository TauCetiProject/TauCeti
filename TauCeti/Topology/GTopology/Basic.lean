/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.Spaces

/-!
# G-topologies and their sites

A G-topology specifies admissible covers of a meet-closed family of subsets, without requiring
arbitrary unions to be admissible. Its covers are set-theoretic covers, stable under restriction
and composition. We use an order embedding into the subsets of the underlying space so that the
same construction applies to bundled admissible opens as well as subtypes of sets.

`GTopology.grothendieckTopology` constructs the site on the inclusion preorder of admissible
opens. `GTopology.isSheaf_iff` identifies its sheaves with presheaves satisfying unique gluing
on admissible covers, using Mathlib's matching families and sheaf categories throughout.
`GTopology.topological` recovers ordinary open covers, and its site is the usual open-set site.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §9.1.1.
-/

public section

namespace TauCeti

open CategoryTheory Opposite

universe u v w

/-- Admissible covers on a family of subsets closed under finite intersections and containing
the whole space. The family is represented by an order embedding `ι`, preserving intersections
and the largest open. Covering families are sets, so repetitions and indexing choices carry
no additional data. -/
@[ext]
structure GTopology {X : Type u} {B : Type v} [SemilatticeInf B] [OrderTop B]
    (ι : B ↪o Set X) where
  /-- The largest admissible open is the whole space. -/
  map_top : ι ⊤ = Set.univ
  /-- Meets represent intersections. -/
  map_inf : ∀ U V, ι (U ⊓ V) = ι U ∩ ι V
  /-- The predicate of admissible covering families. -/
  Covers : B → Set B → Prop
  /-- Every member of a cover is contained in its target. -/
  subset : ∀ {U S}, Covers U S → ∀ V ∈ S, V ≤ U
  /-- An admissible cover covers the underlying set. -/
  union_eq : ∀ {U S}, Covers U S → ⋃₀ (ι '' S) = ι U
  /-- Identity covers are admissible. -/
  identity : ∀ U, Covers U {U}
  /-- Restricting an admissible cover by intersection is admissible. -/
  restriction : ∀ {U S}, Covers U S → ∀ V, V ≤ U → Covers V ((fun W ↦ W ⊓ V) '' S)
  /-- Composing admissible covers gives an admissible cover. -/
  transitive : ∀ {U S} {T : B → Set B}, Covers U S → (∀ V ∈ S, Covers V (T V)) →
    Covers U (⋃ V ∈ S, T V)

namespace GTopology

section Presieve

variable {B : Type v} [Preorder B]

/-- The presieve whose arrows are the inclusions of members of `S` into `U`. -/
def coverPresieve (U : B) (S : Set B) : Presieve U := fun V _ ↦ V ∈ S

@[simp]
theorem coverPresieve_apply {U V : B} (S : Set B) (f : V ⟶ U) :
    coverPresieve U S f ↔ V ∈ S := Iff.rfl

end Presieve

variable {X : Type u} {B : Type v} [SemilatticeInf B] [OrderTop B] {ι : B ↪o Set X}
  (G : GTopology ι)

/-- Admissible covers give a coverage on the preorder of admissible opens. -/
def coverage : Coverage B where
  coverings U := {R | ∃ S, G.Covers U S ∧ R = coverPresieve U S}
  pullback := by
    rintro U V f R ⟨S, hS, rfl⟩
    refine ⟨coverPresieve V ((fun W ↦ W ⊓ V) '' S),
      ⟨_, G.restriction hS V (leOfHom f), rfl⟩, ?_⟩
    intro W g hg
    obtain ⟨Z, hZ, hW⟩ := hg
    have hWZ : W ≤ Z := hW ▸ inf_le_left
    refine ⟨Z, homOfLE hWZ, homOfLE (G.subset hS Z hZ), hZ, ?_⟩
    exact Subsingleton.elim _ _

@[simp]
theorem mem_coverage_iff {U : B} {R : Presieve U} :
    R ∈ G.coverage U ↔ ∃ S, G.Covers U S ∧ R = coverPresieve U S := Iff.rfl

/-- The site on admissible opens: a sieve covers if it contains an admissible cover. -/
noncomputable def grothendieckTopology : GrothendieckTopology B where
  sieves U := {R | ∃ S, G.Covers U S ∧ coverPresieve U S ≤ R}
  top_mem' U := ⟨{U}, G.identity U, le_top⟩
  pullback_stable' := by
    rintro U V R f ⟨S, hS, hSR⟩
    refine ⟨_, G.restriction hS V (leOfHom f), ?_⟩
    rintro W g ⟨Z, hZ, hW⟩
    have hWZ : W ≤ Z := hW ▸ inf_le_left
    exact R.downward_closed (hSR Z (homOfLE (G.subset hS Z hZ)) hZ) (homOfLE hWZ)
  transitive' := by
    classical
    rintro U R ⟨S, hS, hSR⟩ Q hQ
    -- Choose one local admissible cover above each member of the first cover.
    choose T hT hTQ using fun V : S ↦ hQ (hSR V.1 (homOfLE (G.subset hS V.1 V.2)) V.2)
    let T' (V : B) : Set B := if hV : V ∈ S then T ⟨V, hV⟩ else ∅
    have hT' (V : B) (hV : V ∈ S) : G.Covers V (T' V) := by
      simpa only [T', dite_eq_left hV] using hT ⟨V, hV⟩
    refine ⟨_, G.transitive hS hT', ?_⟩
    intro W f hW
    simp only [coverPresieve_apply, Set.mem_iUnion] at hW
    obtain ⟨V, hV, hW⟩ := hW
    have hWT : W ∈ T ⟨V, hV⟩ := by simpa only [T', dite_eq_left hV] using hW
    exact hTQ ⟨V, hV⟩ W (homOfLE (G.subset (hT ⟨V, hV⟩) W hWT)) hWT

/-- Covering sieves are exactly those containing an admissible cover. -/
theorem mem_grothendieckTopology_iff {U : B} {R : Sieve U} :
    R ∈ G.grothendieckTopology U ↔ ∃ S, G.Covers U S ∧ coverPresieve U S ≤ R := Iff.rfl

/-- The explicit site is generated by the native coverage of admissible covers. -/
theorem coverage_toGrothendieck : G.coverage.toGrothendieck = G.grothendieckTopology := by
  apply le_antisymm
  · apply ((Coverage.gi _).gc _ _).mpr
    rintro U R ⟨S, hS, rfl⟩
    exact ⟨S, hS, Sieve.le_generate _⟩
  · rintro U R ⟨S, hS, hSR⟩
    exact G.coverage.mem_toGrothendieck_sieves_of_superset hSR ⟨S, hS, rfl⟩

/-- The site sheaf condition is precisely unique gluing of matching families on all admissible
covers. `Presieve.IsSheafFor` is Mathlib's existence-and-uniqueness condition for amalgamations. -/
theorem isSheaf_iff (P : Bᵒᵖ ⥤ Type w) :
    Presieve.IsSheaf G.grothendieckTopology P ↔
      ∀ (U : B) (S : Set B), G.Covers U S → Presieve.IsSheafFor P (coverPresieve U S) := by
  rw [← coverage_toGrothendieck, Presieve.isSheaf_coverage]
  constructor
  · intro h U S hS
    exact h _ ⟨S, hS, rfl⟩
  · rintro h U R ⟨S, hS, rfl⟩
    exact h U S hS

section Topological

open TopologicalSpace

variable (Y : Type u) [TopologicalSpace Y]

/-- The order embedding sending a bundled open subset to its underlying set. -/
def opensEmbedding : Opens Y ↪o Set Y :=
  .ofMapLEIff (↑) (fun _ _ ↦ SetLike.coe_subset_coe)

@[simp]
theorem opensEmbedding_apply (U : Opens Y) : opensEmbedding Y U = (U : Set Y) := (rfl)

/-- The G-topology of all ordinary open covers. -/
def topological : GTopology (opensEmbedding Y) where
  map_top := Opens.coe_top
  map_inf := Opens.coe_inf
  Covers U S := ⋃₀ ((fun V : Opens Y ↦ (V : Set Y)) '' S) = (U : Set Y)
  subset {U S} h V hV := by
    have hVU : (V : Set Y) ⊆ ⋃₀ ((fun W : Opens Y ↦ (W : Set Y)) '' S) :=
      Set.subset_sUnion_of_mem ⟨V, hV, rfl⟩
    exact hVU.trans h.le
  union_eq h := h
  identity U := by simp
  restriction := by
    intro U S hS V hVU
    calc
      _ = (⋃₀ ((fun W : Opens Y ↦ (W : Set Y)) '' S)) ∩ (V : Set Y) := by
        simp only [Set.image_image, Set.sUnion_image, Opens.coe_inf,
          ← Set.iUnion_inter]
      _ = (U : Set Y) ∩ V := congrArg (· ∩ (V : Set Y)) hS
      _ = (V : Set Y) := Set.inter_eq_right.mpr hVU
  transitive := by
    intro U S T hS hT
    calc
      _ = ⋃ V ∈ S, ⋃₀ ((fun W : Opens Y ↦ (W : Set Y)) '' T V) := by
        simp only [Set.image_iUnion, Set.sUnion_iUnion]
      _ = ⋃ V ∈ S, (V : Set Y) :=
        Set.iUnion_congr fun V ↦ Set.iUnion_congr fun hV ↦ hT V hV
      _ = (U : Set Y) := by simpa only [Set.sUnion_image] using hS

@[simp]
theorem topological_covers_iff {U : Opens Y} {S : Set (Opens Y)} :
    (topological Y).Covers U S ↔
      ⋃₀ ((fun V : Opens Y ↦ (V : Set Y)) '' S) = (U : Set Y) := Iff.rfl

/-- The ordinary topological G-site is Mathlib's open-set site, not a new sheaf category. -/
theorem topological_grothendieckTopology :
    (topological Y).grothendieckTopology = Opens.grothendieckTopology Y := by
  apply le_antisymm
  · rintro U R ⟨S, hS, hSR⟩
    intro x hx
    have hx' : x ∈ (U : Set Y) := hx
    rw [← (topological_covers_iff Y).mp hS] at hx'
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV⟩ := hx'
    exact ⟨V, homOfLE ((topological Y).subset hS V hV), hSR _ _ hV, hxV⟩
  · intro U R hR
    let S : Set (Opens Y) := {V | ∃ f : V ⟶ U, R f}
    have hS : (topological Y).Covers U S := by
      rw [topological_covers_iff]
      ext x
      constructor
      · rintro ⟨_, ⟨V, ⟨f, hf⟩, rfl⟩, hxV⟩
        exact leOfHom f hxV
      · intro hx
        obtain ⟨V, f, hf, hxV⟩ := hR x hx
        exact ⟨V, ⟨V, ⟨f, hf⟩, rfl⟩, hxV⟩
    refine ⟨S, hS, ?_⟩
    rintro V f ⟨g, hg⟩
    exact (Subsingleton.elim g f) ▸ hg

end Topological

end GTopology

end TauCeti

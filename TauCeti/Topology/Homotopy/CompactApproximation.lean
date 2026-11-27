/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Homotopy.Basic

/-!
# Homotopy classes of maps into a space approximated on compact sets

Let `F` be a diagram of spaces with a cocone `gⱼ : Fⱼ → X`, for instance the spaces `𝓛ʳQ` of
closed broken geodesics with `r` breaks in a closed Riemannian manifold `Q`, mapped into the free
loop space `X = 𝓛Q` by the broken-geodesic maps `geoʳ`. Suppose that the diagram approximates `X`
on compact sets, up to homotopy, in the two senses of
`TauCeti.isColimitMapCoconeSingularHomologyOfCompactApprox`:

* every compact subset `K` of `X` maps to some `Fⱼ` by a map `e : K → Fⱼ` with `gⱼ ∘ e` homotopic
  to the inclusion of `K`;
* for every compact subset `K` of some `Fⱼ` and every compact subset `L` of `X` containing
  `gⱼ(K)`, there are `f : j ⟶ k` and a map `e : L → Fₖ` with `e ∘ gⱼ` homotopic on `K` to the map
  `F.map f` of the diagram.

Then, for every compact space `T`, the free homotopy classes `[T, X]` of maps `T → X` and the
classes `[T, Fⱼ]` are related in the following two ways. When the index category is filtered, as
for the sequences indexed by `ℕ` of the applications, these are the two halves that make `[T, X]`
the colimit of the sets `[T, Fⱼ]`:

* every map `φ : T → X` is homotopic to `gⱼ ∘ ψ` for some `j` and some `ψ : T → Fⱼ`
  (`TauCeti.exists_ι_app_comp_homotopic`), since the image of `φ` is a compact subset of `X`;
* if `gⱼ ∘ ψ₀` and `gⱼ ∘ ψ₁` are homotopic, then so are `F.map f ∘ ψ₀` and `F.map f ∘ ψ₁` for some
  `f : j ⟶ k` (`TauCeti.exists_map_comp_homotopic_map_comp`): the images of `ψ₀` and `ψ₁` form a
  compact subset `K` of `Fⱼ`, the image of a homotopy between `gⱼ ∘ ψ₀` and `gⱼ ∘ ψ₁` is a
  compact subset `L` of `X` containing `gⱼ(K)`, and `e` carries that homotopy into `Fₖ`.

This is the homotopical form of the compact-family approximation argument, of which
`TauCeti.isColimitMapCoconeSingularHomologyOfCompactApprox` is the homological form. Taking for
`T` the spheres, it says that the approximations see every free homotopy class of spheres in `X`,
and that two spheres in some `Fⱼ` which become freely homotopic in `X` are already freely homotopic
in some `Fₖ`. The homotopies of the two conditions are free, so nothing is said about homotopy
groups at a chosen basepoint, and no topology is put on a colimit of spaces.

## Main results

* `TauCeti.exists_ι_app_comp_homotopic`: every map of a compact space into the apex factors
  through the diagram up to homotopy.
* `TauCeti.exists_map_comp_homotopic_map_comp`: two maps of a compact space into the diagram that
  become homotopic in the apex become homotopic further along the diagram.
* `TauCeti.exists_map_homOfLE_comp_homotopic_map_homOfLE_comp`: the same for a diagram indexed by
  a preorder, with the later index given by an inequality.

## References

* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry
  and topology*, IRMA Lect. Math. Theor. Phys. 24 (2015), §11.2, Proposition 11.2.4.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton, 1963, §16.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.3.
-/

public section

open CategoryTheory Limits Set

universe w

namespace TauCeti

variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

section Category

variable {J : Type*} [Category J] {F : J ⥤ TopCat.{w}} {c : Cocone F}

/-- **Maps of a compact space into an approximated space factor through the approximations up
to homotopy.** Let `c` be a cocone over a diagram of spaces such that every compact subset `K` of
its apex maps to some space `F j` of the diagram by a map `e` whose composite with the leg
`c.ι.app j` is homotopic to the inclusion of `K`. Then every map `φ` of a compact space into the
apex is homotopic to the composite of the leg `c.ι.app j` with a map `ψ` into some `F j`. -/
theorem exists_ι_app_comp_homotopic
    (happrox : ∀ K : Set c.pt, IsCompact K → ∃ (j : J) (e : C(K, F.obj j)),
      ((c.ι.app j).hom.comp e).Homotopic (ContinuousMap.subtypeVal K))
    (φ : C(T, c.pt)) :
    ∃ (j : J) (ψ : C(T, F.obj j)), ((c.ι.app j).hom.comp ψ).Homotopic φ := by
  obtain ⟨j, e, he⟩ := happrox (range φ) (isCompact_range φ.continuous)
  -- `φ` is its corestriction `φ'` to its range followed by the inclusion of the range.
  let φ' : C(T, range φ) := ⟨fun s ↦ ⟨φ s, mem_range_self s⟩, φ.continuous.subtype_mk _⟩
  have hφ : (ContinuousMap.subtypeVal (range φ)).comp φ' = φ := ContinuousMap.ext fun _ ↦ rfl
  have h := he.comp (ContinuousMap.Homotopic.refl φ')
  rw [hφ] at h
  exact ⟨j, e.comp φ', h⟩

/-- **Maps of a compact space into the approximations which become homotopic in the approximated
space are already homotopic in a later approximation.** Let `c` be a cocone over a diagram of
spaces such that, for every compact subset `K` of a space `F j` of the diagram and every compact
subset `L` of the apex containing the image of `K` under the leg `c.ι.app j`, there are a morphism
`f : j ⟶ k` and a map `e : L → F k` with `e ∘ c.ι.app j` homotopic on `K` to `F.map f`. If two maps
`ψ₀` and `ψ₁` of a compact space into `F j` become homotopic after composing with the leg
`c.ι.app j`, then they become homotopic after composing with `F.map f` for some `f : j ⟶ k`. -/
theorem exists_map_comp_homotopic_map_comp
    (hcompat : ∀ (j : J) (K : Set (F.obj j)) (L : Set c.pt), IsCompact K → IsCompact L →
      ∀ hKL : MapsTo (c.ι.app j) K L, ∃ (k : J) (f : j ⟶ k) (e : C(L, F.obj k)),
        (e.comp ⟨hKL.restrict, (c.ι.app j).hom.continuous.restrict hKL⟩).Homotopic
          ((F.map f).hom.comp (ContinuousMap.subtypeVal K)))
    {j : J} {ψ₀ ψ₁ : C(T, F.obj j)}
    (h : ((c.ι.app j).hom.comp ψ₀).Homotopic ((c.ι.app j).hom.comp ψ₁)) :
    ∃ (k : J) (f : j ⟶ k), ((F.map f).hom.comp ψ₀).Homotopic ((F.map f).hom.comp ψ₁) := by
  obtain ⟨H⟩ := h
  -- The images of `ψ₀` and `ψ₁` form a compact set `K`, sent into the compact image `L` of `H`.
  have hKL : MapsTo (c.ι.app j) (range ψ₀ ∪ range ψ₁) (range H) := by
    rintro _ (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · exact ⟨(0, s), H.apply_zero s⟩
    · exact ⟨(1, s), H.apply_one s⟩
  obtain ⟨k, f, e, he⟩ := hcompat j _ _
    ((isCompact_range ψ₀.continuous).union (isCompact_range ψ₁.continuous))
    (isCompact_range (map_continuous H)) hKL
  let r : C(↥(range ψ₀ ∪ range ψ₁), range H) :=
    ⟨hKL.restrict, (c.ι.app j).hom.continuous.restrict hKL⟩
  let ψ₀' : C(T, ↥(range ψ₀ ∪ range ψ₁)) :=
    ⟨fun s ↦ ⟨ψ₀ s, Or.inl ⟨s, rfl⟩⟩, ψ₀.continuous.subtype_mk _⟩
  let ψ₁' : C(T, ↥(range ψ₀ ∪ range ψ₁)) :=
    ⟨fun s ↦ ⟨ψ₁ s, Or.inr ⟨s, rfl⟩⟩, ψ₁.continuous.subtype_mk _⟩
  -- Read in `L`, the homotopy `H` joins `r ∘ ψ₀'` to `r ∘ ψ₁'`.
  have hH : (r.comp ψ₀').Homotopic (r.comp ψ₁') :=
    ⟨{ toFun := fun x ↦ ⟨H x, mem_range_self x⟩
       continuous_toFun := (map_continuous H).subtype_mk _
       map_zero_left := fun s ↦ Subtype.ext (H.apply_zero s)
       map_one_left := fun s ↦ Subtype.ext (H.apply_one s) }⟩
  have hψ₀ : (F.map f).hom.comp ψ₀ = ((F.map f).hom.comp (ContinuousMap.subtypeVal _)).comp ψ₀' :=
    ContinuousMap.ext fun _ ↦ rfl
  have hψ₁ : (F.map f).hom.comp ψ₁ = ((F.map f).hom.comp (ContinuousMap.subtypeVal _)).comp ψ₁' :=
    ContinuousMap.ext fun _ ↦ rfl
  refine ⟨k, f, ?_⟩
  rw [hψ₀, hψ₁]
  -- Compare both maps with `e ∘ r` on the images, and carry the homotopy `H` along `e`.
  exact (he.symm.comp (ContinuousMap.Homotopic.refl ψ₀')).trans
    (((ContinuousMap.Homotopic.refl e).comp hH).trans
      (he.comp (ContinuousMap.Homotopic.refl ψ₁')))

end Category

section Preorder

variable {J : Type*} [Preorder J] {F : J ⥤ TopCat.{w}} {c : Cocone F}

/-- **Maps of a compact space into a diagram indexed by a preorder which become homotopic in the
approximated space are already homotopic at a later index.** This is
`TauCeti.exists_map_comp_homotopic_map_comp` for a diagram indexed by a preorder, such as `ℕ`, with
the morphism `j ⟶ k` of its conclusion given by an inequality `j ≤ k`. -/
theorem exists_map_homOfLE_comp_homotopic_map_homOfLE_comp
    (hcompat : ∀ (j : J) (K : Set (F.obj j)) (L : Set c.pt), IsCompact K → IsCompact L →
      ∀ hKL : MapsTo (c.ι.app j) K L, ∃ (k : J) (f : j ⟶ k) (e : C(L, F.obj k)),
        (e.comp ⟨hKL.restrict, (c.ι.app j).hom.continuous.restrict hKL⟩).Homotopic
          ((F.map f).hom.comp (ContinuousMap.subtypeVal K)))
    {j : J} {ψ₀ ψ₁ : C(T, F.obj j)}
    (h : ((c.ι.app j).hom.comp ψ₀).Homotopic ((c.ι.app j).hom.comp ψ₁)) :
    ∃ (k : J) (hjk : j ≤ k),
      ((F.map (homOfLE hjk)).hom.comp ψ₀).Homotopic ((F.map (homOfLE hjk)).hom.comp ψ₁) := by
  obtain ⟨k, f, hf⟩ := exists_map_comp_homotopic_map_comp hcompat h
  -- Morphisms of a preorder are inequalities: `f` is `homOfLE (leOfHom f)`.
  rw [← homOfLE_leOfHom f] at hf
  exact ⟨k, leOfHom f, hf⟩

end Preorder

end TauCeti

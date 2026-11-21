/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.CompactSupport
public import TauCeti.Algebra.Category.ModuleCat.FilteredColimits
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance

/-!
# Singular homology of a space approximated on compact sets

Let `F` be a diagram of spaces with a cocone `gⱼ : Fⱼ → X`, for instance the spaces `𝓛ʳQ` of
closed broken geodesics with `r` breaks in a closed Riemannian manifold `Q`, mapped into the free
loop space `X = 𝓛Q` by the broken-geodesic maps `geoʳ`. The legs need not be injective, and no
space of the diagram need be a subspace of `X`. Suppose that the diagram approximates `X` on
compact sets, up to homotopy:

* every compact subset `K` of `X` maps to some `Fⱼ` by a map `e : K → Fⱼ` with `gⱼ ∘ e` homotopic
  to the inclusion of `K` (for broken geodesics, `e` samples a loop at `r` equally spaced times,
  and the homotopy straightens its arcs into geodesic segments);
* for every compact subset `K` of some `Fⱼ` and every compact subset `L` of `X` containing
  `gⱼ(K)`, there are `j ⟶ k` and a map `e : L → Fₖ` with `e ∘ gⱼ` homotopic on `K` to the map
  `Fⱼ → Fₖ` of the diagram (for broken geodesics, sampling a broken geodesic again with more
  breaks slides its vertices along it, back to the subdivided tuple).

Then the singular homology of `X` is the colimit of the singular homology of the diagram
(`TauCeti.isColimitMapCoconeSingularHomologyOfCompactApprox`), with coefficients in any module,
when the diagram is filtered. The two conditions give the two halves separately: every class of
`X` comes from some `Fⱼ` (`TauCeti.exists_singularHomologyMap_eq_of_homotopic`), and a class of
`Fⱼ` vanishing in `X` vanishes in some `Fₖ`
(`TauCeti.exists_singularHomologyMap_eq_zero_of_homotopic`).

The proof reads both conditions through the compact supports of singular homology: a class of
`X` comes from a compact subset `K`, where the first condition and homotopy invariance move it
into `Fⱼ`; a class of a compact subset of `Fⱼ` vanishing in `X` already vanishes in a compact
subset `L` of `X`, and the second condition carries this vanishing into `Fₖ`
(`TauCeti.exists_isCompact_singularHomologyMap_subtypeVal_eq`,
`TauCeti.exists_isCompact_singularHomologyMap_inclusion_eq_zero`). This is the homological form
of the compact-family approximation argument which shows that the colimit of the broken-geodesic
approximations is weakly equivalent to the free loop space; no topology is put on a colimit of
spaces.

## Main results

* `TauCeti.exists_singularHomologyMap_eq_of_homotopic`: every class of `X` comes from the
  diagram.
* `TauCeti.exists_singularHomologyMap_eq_zero_of_homotopic`: a class of the diagram vanishing in
  `X` vanishes further along the diagram.
* `TauCeti.isColimitMapCoconeSingularHomologyOfCompactApprox`: for a filtered diagram,
  `Hₙ(X; M)` is the colimit of the `Hₙ(Fⱼ; M)`.

## References

* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry
  and topology*, IRMA Lect. Math. Theor. Phys. 24 (2015), §11.2, Proposition 11.2.4.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton, 1963, §16.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.3.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology TopCat

universe w

namespace TauCeti

variable {A : Type w} [Ring A] (M : ModuleCat.{w} A) (n : ℕ) {J : Type*} [Category J]
  {F : J ⥤ TopCat.{w}} (c : Cocone F)

/-- **Classes of an approximated space come from the approximations.** Let `c` be a cocone over a
diagram of spaces such that every compact subset `K` of its apex maps to some space `F j` of the
diagram by a map `e` whose composite with the leg `c.ι.app j` is homotopic to the inclusion of
`K`. Then every singular homology class of the apex, with coefficients in a module, is the image
of a class of some `F j`. -/
theorem exists_singularHomologyMap_eq_of_homotopic
    (happrox : ∀ K : Set c.pt, IsCompact K → ∃ (j : J) (e : C(K, F.obj j)),
      ((c.ι.app j).hom.comp e).Homotopic (ContinuousMap.subtypeVal K))
    (x : ((singularHomologyFunctor (ModuleCat.{w} A) n).obj M).obj c.pt) :
    ∃ (j : J) (y : ((singularHomologyFunctor (ModuleCat.{w} A) n).obj M).obj (F.obj j)),
      ((singularHomologyFunctor _ n).obj M).map (c.ι.app j) y = x := by
  obtain ⟨K, hK, y, rfl⟩ := exists_isCompact_singularHomologyMap_subtypeVal_eq M n x
  obtain ⟨j, e, he⟩ := happrox K hK
  refine ⟨j, ((singularHomologyFunctor _ n).obj M).map (ofHom e) y, ?_⟩
  have h : ((singularHomologyFunctor (ModuleCat.{w} A) n).obj M).map (ofHom e ≫ c.ι.app j) =
      ((singularHomologyFunctor _ n).obj M).map (ofHom (ContinuousMap.subtypeVal K)) := by
    rw [← ofHom_hom (c.ι.app j), ← ofHom_comp]
    exact ContinuousMap.singularHomologyFunctor_map_eq_of_homotopic M n he
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, h]

/-- **Classes vanishing in an approximated space vanish in the approximations.** Let `c` be a
cocone over a diagram of spaces such that, for every compact subset `K` of a space `F j` of the
diagram and every compact subset `L` of the apex containing the image of `K` under the leg
`c.ι.app j`, there are a morphism `f : j ⟶ k` and a map `e : L → F k` with `e ∘ c.ι.app j`
homotopic on `K` to `F.map f`. Then a singular homology class of `F j`, with coefficients in a
module, which vanishes in the apex already vanishes in some `F k`. -/
theorem exists_singularHomologyMap_eq_zero_of_homotopic
    (hcompat : ∀ (j : J) (K : Set (F.obj j)) (L : Set c.pt), IsCompact K → IsCompact L →
      ∀ hKL : Set.MapsTo (c.ι.app j) K L, ∃ (k : J) (f : j ⟶ k) (e : C(L, F.obj k)),
        (e.comp ⟨hKL.restrict, (c.ι.app j).hom.continuous.restrict hKL⟩).Homotopic
          ((F.map f).hom.comp (ContinuousMap.subtypeVal K)))
    {j : J} (z : ((singularHomologyFunctor (ModuleCat.{w} A) n).obj M).obj (F.obj j))
    (hz : ((singularHomologyFunctor _ n).obj M).map (c.ι.app j) z = 0) :
    ∃ (k : J) (f : j ⟶ k), ((singularHomologyFunctor _ n).obj M).map (F.map f) z = 0 := by
  obtain ⟨K, hK, y, rfl⟩ := exists_isCompact_singularHomologyMap_subtypeVal_eq M n z
  -- Move `y` to the compact image `c.ι.app j '' K`, where it vanishes in the apex.
  have hK₀ : Set.MapsTo (c.ι.app j) K (c.ι.app j '' K) := Set.mapsTo_image _ _
  have hy₀ : ((singularHomologyFunctor _ n).obj M).map
      (ofHom (ContinuousMap.subtypeVal (c.ι.app j '' K)))
        (((singularHomologyFunctor _ n).obj M).map
          (ofHom ⟨hK₀.restrict, (c.ι.app j).hom.continuous.restrict hK₀⟩) y) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← TopCat.ofHom_subtypeVal_comp, Functor.map_comp, ConcreteCategory.comp_apply, hz]
  -- It vanishes already in a compact subset `L` of the apex.
  obtain ⟨L, hL, hKL, hyL⟩ := exists_isCompact_singularHomologyMap_inclusion_eq_zero M n
    (hK.image (c.ι.app j).hom.continuous) _ hy₀
  obtain ⟨k, f, e, he⟩ := hcompat j K L hK hL (hK₀.mono_right hKL)
  refine ⟨k, f, ?_⟩
  have h : ((singularHomologyFunctor (ModuleCat.{w} A) n).obj M).map
      (ofHom ⟨hK₀.restrict, (c.ι.app j).hom.continuous.restrict hK₀⟩ ≫
        ofHom (ContinuousMap.inclusion hKL) ≫ ofHom e) =
      ((singularHomologyFunctor _ n).obj M).map
        (ofHom (ContinuousMap.subtypeVal K) ≫ F.map f) := by
    -- The restriction of the leg to `K → L` is the composite of its restriction to
    -- `K → c.ι.app j '' K` with the inclusion into `L`.
    have hr : (ContinuousMap.inclusion hKL).comp
        ⟨hK₀.restrict, (c.ι.app j).hom.continuous.restrict hK₀⟩ =
          ⟨(hK₀.mono_right hKL).restrict,
            (c.ι.app j).hom.continuous.restrict (hK₀.mono_right hKL)⟩ := rfl
    rw [← ofHom_comp, ← ofHom_comp, ContinuousMap.comp_assoc, hr, ← ofHom_hom (F.map f),
      ← ofHom_comp]
    exact ContinuousMap.singularHomologyFunctor_map_eq_of_homotopic M n he
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← h, Functor.map_comp,
    Functor.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hyL, map_zero]

/-- **Singular homology of a space approximated on compact sets.** Let `c` be a cocone over a
filtered diagram of spaces which approximates its apex on compact sets up to homotopy: every
compact subset of the apex maps to some `F j` by a map whose composite with the leg is homotopic
to the inclusion, and for every compact subset `K` of some `F j` and every compact subset `L` of
the apex containing its image there is a map `e : L → F k`, for some `f : j ⟶ k`, with
`e ∘ c.ι.app j` homotopic on `K` to `F.map f`. Then singular homology of the apex, with
coefficients in a module, is the colimit of singular homology of the diagram. The legs need not
be embeddings. -/
def isColimitMapCoconeSingularHomologyOfCompactApprox [IsFiltered J]
    (happrox : ∀ K : Set c.pt, IsCompact K → ∃ (j : J) (e : C(K, F.obj j)),
      ((c.ι.app j).hom.comp e).Homotopic (ContinuousMap.subtypeVal K))
    (hcompat : ∀ (j : J) (K : Set (F.obj j)) (L : Set c.pt), IsCompact K → IsCompact L →
      ∀ hKL : Set.MapsTo (c.ι.app j) K L, ∃ (k : J) (f : j ⟶ k) (e : C(L, F.obj k)),
        (e.comp ⟨hKL.restrict, (c.ι.app j).hom.continuous.restrict hKL⟩).Homotopic
          ((F.map f).hom.comp (ContinuousMap.subtypeVal K))) :
    IsColimit (((singularHomologyFunctor (ModuleCat.{w} A) n).obj M).mapCocone c) :=
  ModuleCat.isColimitOfJointlySurjective _
    -- The legs of the image cocone are the maps induced by the legs of `c`.
    (fun x ↦ exists_singularHomologyMap_eq_of_homotopic M n c happrox x)
    fun i j xi xj hij ↦ by
      -- Compare the two classes at a common later stage, where their difference vanishes in
      -- the apex.
      simp only [Functor.mapCocone_ι_app] at hij
      let a := IsFiltered.leftToMax i j
      let b := IsFiltered.rightToMax i j
      obtain ⟨k, f, hf⟩ := exists_singularHomologyMap_eq_zero_of_homotopic M n c hcompat
        (((singularHomologyFunctor _ n).obj M).map (F.map a) xi -
          ((singularHomologyFunctor _ n).obj M).map (F.map b) xj) (by
            rw [map_sub, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
              ← Functor.map_comp, ← Functor.map_comp, c.w, c.w, hij, sub_self])
      refine ⟨k, a ≫ f, b ≫ f, ?_⟩
      rw [map_sub, sub_eq_zero] at hf
      simpa only [Functor.comp_map, Functor.map_comp, ConcreteCategory.comp_apply] using hf

end TauCeti

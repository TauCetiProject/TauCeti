/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.CompactSupport.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.Over
public import TauCeti.Algebra.Category.ModuleCat.FilteredColimits
import TauCeti.AlgebraicTopology.Singular.Twisted.Coefficients

/-!
# Twisted homology of a space approximated on compact sets

Let `F` be a diagram of spaces with a cocone `gⱼ : Fⱼ → X`, for instance the spaces `𝓛ʳQ` of closed
broken geodesics with `r` breaks in a closed Riemannian manifold `Q`, mapped into the free loop
space `X = 𝓛Q` by the broken-geodesic maps `geoʳ`, and let `M` be a local coefficient system on
`X`. This file proves that the twisted homology `Hₖ(X; M)` is the colimit of the twisted homology
groups `Hₖ(Fⱼ; gⱼ*M)` when the diagram approximates `X` on compact sets, coherently up to homotopy
(`isColimitWhiskerOverTwistedHomologyCoconeOfCompactApprox`; all declarations of this file are in
the namespace `TauCeti.LocalCoefficientSystem`). It is the local-coefficient form of
`TauCeti.isColimitMapCoconeSingularHomologyOfCompactApprox`.

**Spaces over `X`.** Twisted homology is a functor `overTwistedHomologyFunctor` on the category
`Over X`, with a cocone `overTwistedHomologyCocone` to `Hₖ(X; M)`, both from
`TauCeti.AlgebraicTopology.Singular.Twisted.Over`. The diagram `j ↦ Hₖ(Fⱼ; gⱼ*M)` is this functor
read through `F.toOver X g _ : J ⥤ Over X`.

**The two halves.** As for constant coefficients, a class of `X` lives on a compact set, and so
does a vanishing class:

* if every compact subset `K` of `X` maps to some `Fⱼ` by a map `e` with `gⱼ ∘ e` homotopic to the
  inclusion of `K`, every class of `Hₖ(X; M)` comes from some `Fⱼ`
  (`exists_twistedHomologyMap_eq_of_homotopic`);
* under the coherence condition below, a class of `Fⱼ` vanishing in `X` vanishes in some `Fᵢ`
  (`exists_homologyMap_overTwistedChainComplexMap_eq_zero_of_homotopic`).

With local coefficients a homotopy acts on coefficients by transport along the paths it traces
(`TopCat.Homotopy.twistedHomologyMap_eq_comp`), so the second half needs more than for constant
coefficients. For a compact `K ⊆ Fⱼ` and a compact `K' ⊆ X` containing `gⱼ(K)`, it asks for a map
`e : K' → Fᵢ` with a homotopy `G` from `gᵢ ∘ e` to the inclusion of `K'` and a homotopy `H` on `K`
from `e ∘ gⱼ` to the map `Fⱼ → Fᵢ` of the diagram, which agree over `X` as far as `M` sees: at every
point of `K`, transport in `M` along the image under `gᵢ` of the path traced by `H` equals transport
along the path traced by `G`. This holds when the two paths are homotopic, and for a local system
pulled back along a map `X → Z` as soon as their images in `Z` are homotopic. Transport along `H`
and along `G` then identify the coefficients in the same way. This is the content of
`homologyMap_overTwistedChainComplexMap_eq_comp`: a triangle of spaces over `X` that commutes up to
such coherent homotopies commutes on twisted homology. With constant coefficients transport is
trivial, and `TauCeti.isColimitMapCoconeSingularHomologyOfCompactApprox` needs no such condition.

For broken geodesics, `e` is the sampling of a loop at equally spaced times, `G` straightens its
arcs into geodesic segments, and `H` slides the vertices of a broken geodesic along it. Both keep
the base point of the loops, so the condition holds for local systems pulled back along the
evaluation of free loops at their base point.

## Main results

* `exists_twistedHomologyMap_eq_of_homotopic`: every class of `X` comes from the diagram.
* `exists_homologyMap_overTwistedChainComplexMap_eq_zero_of_homotopic`: a class of the diagram
  vanishing in `X` vanishes further along the diagram.
* `isColimitWhiskerOverTwistedHomologyCoconeOfCompactApprox`: for a filtered diagram, `Hₖ(X; M)` is
  the colimit of the `Hₖ(Fⱼ; gⱼ*M)`.

## References

* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry
  and topology*, IRMA Lect. Math. Theor. Phys. 24 (2015), §11.2, Proposition 11.2.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.3.
* A. Hatcher, *Algebraic Topology*, Section 3.H, for homology with local coefficients.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R]

/-! ### Spaces approximated on compact sets -/

section Approximation

variable {J : Type*} [Category J] {F : J ⥤ TopCat.{v}} (c : Cocone F)
  (M : LocalCoefficientSystem.{u, v, max v w} R c.pt)

/-- **Twisted classes of an approximated space come from the approximations.** Let `c` be a
cocone over a diagram of spaces such that every compact subset `K` of its apex maps to some space
`F j` of the diagram by a map `e` whose composite with the leg `c.ι.app j` is homotopic to the
inclusion of `K`. Then every class of the twisted homology of the apex, with coefficients in a
local system `M`, is the image of a class of some `F j`, with coefficients in the pullback of
`M`. -/
theorem exists_twistedHomologyMap_eq_of_homotopic
    (happrox : ∀ K : Set c.pt, IsCompact K → ∃ (j : J) (e : C(K, F.obj j)),
      ((c.ι.app j).hom.comp e).Homotopic (ContinuousMap.subtypeVal K))
    {k : ℕ} (x : M.twistedHomology k) :
    ∃ (j : J) (y : ((pullback (c.ι.app j).hom).obj M).twistedHomology k),
      twistedHomologyMap (c.ι.app j) M k y = x := by
  obtain ⟨K, hK, y, rfl⟩ := exists_isCompact_twistedHomologyMap_subtypeVal_eq M x
  obtain ⟨j, e, ⟨H⟩⟩ := happrox K hK
  -- Transport `y` along the homotopy to the coefficients of `e ≫ c.ι.app j`, then push it to `F j`.
  refine ⟨j, twistedHomologyMap (TopCat.ofHom e) ((pullback (c.ι.app j).hom).obj M) k
    (twistedHomologyCoefficientMap
      ((pullbackCompIso (TopCat.ofHom e).hom (c.ι.app j).hom).hom.app M) k
      (twistedHomologyCoefficientMap ((pullbackHomotopyIso H).inv.app M) k y)), ?_⟩
  have hH := TopCat.Homotopy.twistedHomologyMap_eq_comp
    (f := TopCat.ofHom e ≫ c.ι.app j) (g := TopCat.ofHom (ContinuousMap.subtypeVal K)) H M k
  rw [twistedHomologyMap_comp] at hH
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    hH, ← Iso.app_inv, ← Iso.app_hom, twistedHomologyCoefficientMap_inv_hom_id_assoc]

/-- **Twisted classes vanishing in an approximated space vanish in the approximations.** Let `c`
be a cocone over a diagram of spaces. Suppose that for every compact subset `K` of a space `F j`
of the diagram and every compact subset `K'` of the apex containing the image of `K` under the leg
`c.ι.app j`, there are a morphism `f : j ⟶ i` and a map `e : K' → F i` with a homotopy `G` from
`c.ι.app i ∘ e` to the inclusion of `K'`, and a homotopy `H` on `K` from `e ∘ c.ι.app j` to
`F.map f`, such that at every point `x` of `K` transport in `M` along the image of the path traced
by `H` in the apex equals transport along the path traced by `G`, as it does when the two paths are
homotopic. Then a class of the twisted homology of `F j`, with
coefficients in the pullback of a local system `M` on the apex, which vanishes in the apex already
vanishes in some `F i`. -/
theorem exists_homologyMap_overTwistedChainComplexMap_eq_zero_of_homotopic
    (hcompat : ∀ (j : J) (K : Set (F.obj j)) (K' : Set c.pt), IsCompact K → IsCompact K' →
      ∀ hKK' : Set.MapsTo (c.ι.app j) K K', ∃ (i : J) (f : j ⟶ i) (e : C(K', F.obj i))
        (G : ((c.ι.app i).hom.comp e).Homotopy (ContinuousMap.subtypeVal K'))
        (H : (e.comp ⟨hKK'.restrict, (c.ι.app j).hom.continuous.restrict hKK'⟩).Homotopy
          ((F.map f).hom.comp (ContinuousMap.subtypeVal K))),
        ∀ x : K, M.map (Path.Homotopic.Quotient.mk ((H.evalAt x).map
            (c.ι.app i).hom.continuous) : FundamentalGroupoid.mk _ ⟶ FundamentalGroupoid.mk _) =
          M.map (Path.Homotopic.Quotient.mk ((G.evalAt ⟨c.ι.app j x, hKK' x.property⟩).cast rfl
            (ConcreteCategory.congr_hom (c.w f) x.val))))
    {k : ℕ} {j : J} (z : ((pullback (c.ι.app j).hom).obj M).twistedHomology k)
    (hz : twistedHomologyMap (c.ι.app j) M k z = 0) :
    ∃ (i : J) (f : j ⟶ i),
      HomologicalComplex.homologyMap (overTwistedChainComplexMap M (F.map f) (c.w f)) k z = 0 := by
  obtain ⟨K, hK, y, rfl⟩ :=
    exists_isCompact_twistedHomologyMap_subtypeVal_eq ((pullback (c.ι.app j).hom).obj M) z
  -- Read `y` as a class of `K` over the apex.
  set y' := twistedHomologyCoefficientMap
    ((pullbackCompIso (TopCat.ofHom (ContinuousMap.subtypeVal K)).hom (c.ι.app j).hom).inv.app M) k
      y
  have hyz : HomologicalComplex.homologyMap
      (overTwistedChainComplexMap M (TopCat.ofHom (ContinuousMap.subtypeVal K)) rfl) k y' =
      twistedHomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal K))
        ((pullback (c.ι.app j).hom).obj M) k y :=
    ConcreteCategory.congr_hom
      (twistedHomologyCoefficientMap_comp_homologyMap_overTwistedChainComplexMap M _ k) y
  -- Its image in the compact set `c.ι.app j '' K` vanishes in the apex.
  have hK₀ : Set.MapsTo (c.ι.app j) K (c.ι.app j '' K) := Set.mapsTo_image _ _
  obtain ⟨K', hK', hK₀K', hw⟩ := exists_isCompact_homologyMap_subsetTwistedChainComplexMap_eq_zero
    M (hK.image (c.ι.app j).hom.continuous)
    (HomologicalComplex.homologyMap (overTwistedChainComplexMap M
      (TopCat.ofHom ⟨hK₀.restrict, (c.ι.app j).hom.continuous.restrict hK₀⟩) rfl) k y')
    (by
      refine (ConcreteCategory.congr_hom
        (homologyMap_overTwistedChainComplexMap_twistedHomologyMap M _ _ k) y').trans ?_
      exact (ConcreteCategory.congr_hom (homologyMap_overTwistedChainComplexMap_twistedHomologyMap M
        (TopCat.ofHom (ContinuousMap.subtypeVal K)) rfl k) y').symm.trans
          ((congrArg _ hyz).trans hz))
  have hKK' : Set.MapsTo (c.ι.app j) K K' := hK₀.mono_right hK₀K'
  obtain ⟨i, f, e, G, H, hGH⟩ := hcompat j K K' hK hK' hKK'
  refine ⟨i, f, ?_⟩
  -- The class `y'` vanishes in `K'`, and the coherent homotopies carry this to `F i`.
  let ρ₀ : TopCat.of K ⟶ TopCat.of ↥(c.ι.app j '' K) :=
    TopCat.ofHom ⟨hK₀.restrict, (c.ι.app j).hom.continuous.restrict hK₀⟩
  let ι₀ : TopCat.of ↥(c.ι.app j '' K) ⟶ TopCat.of K' :=
    TopCat.ofHom (ContinuousMap.inclusion hK₀K')
  have hρ : HomologicalComplex.homologyMap (overTwistedChainComplexMap M
      (a := TopCat.ofHom (ContinuousMap.subtypeVal K) ≫ c.ι.app j)
      (b := TopCat.ofHom (ContinuousMap.subtypeVal K')) (ρ₀ ≫ ι₀) rfl) k y' = 0 := by
    rw [subsetTwistedChainComplexMap_eq_overTwistedChainComplexMap] at hw
    rw [overTwistedChainComplexMap_comp M
      (a := TopCat.ofHom (ContinuousMap.subtypeVal K) ≫ c.ι.app j)
      (b := TopCat.ofHom (ContinuousMap.subtypeVal (c.ι.app j '' K))) ρ₀ ι₀ rfl rfl,
      HomologicalComplex.homologyMap_comp]
    exact hw
  rw [← hyz]
  refine (ConcreteCategory.congr_hom ((HomologicalComplex.homologyMap_comp _ _ k).symm.trans
    (congrArg (HomologicalComplex.homologyMap · k)
      (overTwistedChainComplexMap_comp M (TopCat.ofHom (ContinuousMap.subtypeVal K)) (F.map f)
        rfl (c.w f)).symm)) y').trans ?_
  rw [homologyMap_overTwistedChainComplexMap_eq_comp M
    (a := TopCat.ofHom (ContinuousMap.subtypeVal K) ≫ c.ι.app j)
    (b := TopCat.ofHom (ContinuousMap.subtypeVal K')) (ρ₀ ≫ ι₀) rfl
    (TopCat.ofHom (ContinuousMap.subtypeVal K) ≫ F.map f) _ (TopCat.ofHom e) G H hGH]
  rw [ConcreteCategory.comp_apply, hρ, map_zero]

/-- **Twisted homology of a space approximated on compact sets.** Let `c` be a cocone over a
filtered diagram of spaces which approximates its apex on compact sets, coherently up to homotopy:
the hypotheses of `exists_twistedHomologyMap_eq_of_homotopic` and of
`exists_homologyMap_overTwistedChainComplexMap_eq_zero_of_homotopic`. Then the twisted homology of
the apex, with coefficients in a local system `M`, is the colimit of the twisted homology of the
spaces of the diagram, with coefficients in the pullbacks of `M` along the legs. -/
def isColimitWhiskerOverTwistedHomologyCoconeOfCompactApprox [IsFiltered J]
    (happrox : ∀ K : Set c.pt, IsCompact K → ∃ (j : J) (e : C(K, F.obj j)),
      ((c.ι.app j).hom.comp e).Homotopic (ContinuousMap.subtypeVal K))
    (hcompat : ∀ (j : J) (K : Set (F.obj j)) (K' : Set c.pt), IsCompact K → IsCompact K' →
      ∀ hKK' : Set.MapsTo (c.ι.app j) K K', ∃ (i : J) (f : j ⟶ i) (e : C(K', F.obj i))
        (G : ((c.ι.app i).hom.comp e).Homotopy (ContinuousMap.subtypeVal K'))
        (H : (e.comp ⟨hKK'.restrict, (c.ι.app j).hom.continuous.restrict hKK'⟩).Homotopy
          ((F.map f).hom.comp (ContinuousMap.subtypeVal K))),
        ∀ x : K, M.map (Path.Homotopic.Quotient.mk ((H.evalAt x).map
            (c.ι.app i).hom.continuous) : FundamentalGroupoid.mk _ ⟶ FundamentalGroupoid.mk _) =
          M.map (Path.Homotopic.Quotient.mk ((G.evalAt ⟨c.ι.app j x, hKK' x.property⟩).cast rfl
            (ConcreteCategory.congr_hom (c.w f) x.val))))
    (k : ℕ) :
    IsColimit ((overTwistedHomologyCocone M k).whisker (F.toOver c.pt c.ι.app c.w)) :=
  ModuleCat.isColimitOfJointlySurjective _
    (fun x ↦ exists_twistedHomologyMap_eq_of_homotopic c M happrox x)
    fun i j xi xj hij ↦ by
      -- Compare the two classes at a common later stage, where their difference vanishes in the
      -- apex.
      let a := IsFiltered.leftToMax i j
      let b := IsFiltered.rightToMax i j
      have hab : twistedHomologyMap (c.ι.app (IsFiltered.max i j)) M k
          (HomologicalComplex.homologyMap (overTwistedChainComplexMap M (F.map a) (c.w a)) k xi -
            HomologicalComplex.homologyMap (overTwistedChainComplexMap M (F.map b) (c.w b)) k xj) =
          0 := by
        rw [map_sub, sub_eq_zero]
        refine ((ConcreteCategory.congr_hom
          (homologyMap_overTwistedChainComplexMap_twistedHomologyMap M _ _ k) xi).trans ?_).trans
            (ConcreteCategory.congr_hom
              (homologyMap_overTwistedChainComplexMap_twistedHomologyMap M _ _ k) xj).symm
        exact hij
      obtain ⟨l, f, hf⟩ :=
        exists_homologyMap_overTwistedChainComplexMap_eq_zero_of_homotopic c M hcompat _ hab
      refine ⟨l, a ≫ f, b ≫ f, ?_⟩
      rw [map_sub, sub_eq_zero] at hf
      rw [Functor.map_comp, Functor.map_comp]
      exact hf

end Approximation

end TauCeti.LocalCoefficientSystem

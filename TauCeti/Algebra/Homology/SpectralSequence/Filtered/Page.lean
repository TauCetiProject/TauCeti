/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralObject.Image
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.FirstPage

/-!
# The pages of the spectral sequence of a filtered complex through representatives

Let `G : EInt ⥤ CochainComplex C ℤ` be a functor whose transition maps are monomorphisms, for
instance the functor `CochainComplex.filtrationFunctor F hF` of an increasing filtration `F` of a
cochain complex `K`, and write `G_b/G_a` for the cokernel of `G_a ⟶ G_b`. On page `r ≥ 2` of the
spectral sequence `CochainComplex.spectralSequence G`, the object at `(p, q)` is the image of the
map

`H^{p+q}(G_{q+1}/G_{q-r+2}) ⟶ H^{p+q}(G_{q+r-1}/G_q)`

induced by the inclusions `G_{q-r+2} ⊆ G_q` and `G_{q+1} ⊆ G_{q+r-1}`
(`CochainComplex.spectralSequencePageXIsoImage`). The map factors as the epimorphism
`CochainComplex.toSpectralSequencePageX` onto the page object followed by the monomorphism
`CochainComplex.fromSpectralSequencePageX`
(`CochainComplex.toSpectralSequencePageX_fromSpectralSequencePageX`).
So the elements of `H^{p+q}(G_{q+1}/G_{q-r+2})` represent the elements of the page object, and two
representatives give the same element exactly when they have the same image in
`H^{p+q}(G_{q+r-1}/G_q)`. For a filtration of a complex of modules, these representatives are the
classes of the elements `x ∈ G_{q+1}` with `dx ∈ G_{q-r+2}`.

The differential `d_r` from `(p, q)` to `(p + r, q - r + 1)` is computed on representatives
(`CochainComplex.toSpectralSequencePageX_d`): it sends the element represented by
`x ∈ H^{p+q}(G_{q+1}/G_{q-r+2})` to the element represented by
`δ x ∈ H^{p+q+1}(G_{q-r+2}/G_{q-2r+3})`, where `δ` is the connecting map of the short exact
sequence of quotients `G_{q-r+2}/G_{q-2r+3} ⟶ G_{q+1}/G_{q-2r+3} ⟶ G_{q+1}/G_{q-r+2}`.
Concretely, for a filtration of a complex of modules and a representative given by `x ∈ G_{q+1}`
with `dx ∈ G_{q-r+2}`, the image is represented by the class of `dx`. For `r = 2` the quotients are
the graded pieces and `δ` is the connecting map of
`CochainComplex.spectralSequence_first_page_d_eq`.

The indices of the quotients are given as integers together with equations, so that the
statements apply to any expressions for them.

## Main definitions

* `CochainComplex.toSpectralSequencePageX`: the epimorphism from `H^n(G_{q+1}/G_{q-r+2})` onto the
  object at `(p, q)` of page `r`.
* `CochainComplex.fromSpectralSequencePageX`: the monomorphism from the object at `(p, q)` of
  page `r` to `H^n(G_{q+r-1}/G_q)`.
* `CochainComplex.spectralSequencePageXIsoImage`: the page object is the image of
  `H^n(G_{q+1}/G_{q-r+2}) ⟶ H^n(G_{q+r-1}/G_q)`.

## Main results

* `CochainComplex.toSpectralSequencePageX_fromSpectralSequencePageX`: the two maps compose to the
  map induced by the inclusions.
* `CochainComplex.toSpectralSequencePageX_d`: the differentials on representatives.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge Studies in Advanced
  Mathematics 58, Cambridge University Press, 2001, §2.2, proof of Theorem 2.6.
* C. A. Weibel, *An introduction to homological algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press, 1994, §5.4.
-/

public section

open CategoryTheory Limits ComposableArrows

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] (G : EInt ⥤ CochainComplex C ℤ)
  [∀ {a b : EInt} (f : a ⟶ b), Mono (G.map f)]

/-- The morphism `a ⟶ b` of `EInt` between integers `a ≤ b`. -/
abbrev intHom {a b : ℤ} (h : a ≤ b) : (a : EInt) ⟶ (b : EInt) :=
  homOfLE (WithBotTop.coe_le_coe.mpr h)

/-- The epimorphism from `H^n(G_{i₂}/G_{i₀})` onto the object at `pq = (p, q)` of page `r` of the
spectral sequence of `G`, where `i₀ = q - r + 2`, `i₂ = q + 1` and `n = p + q`. -/
noncomputable def toSpectralSequencePageX (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (i₀ i₂ : ℤ)
    (h₀ : i₀ = pq.2 - r + 2) (h₂ : i₂ = pq.2 + 1) (n : ℤ) (hn : n = pq.1 + pq.2) :
    (cokernel (G.map (intHom (show i₀ ≤ i₂ by lia)))).homology n ⟶
      ((spectralSequence G).page r).X pq :=
  (spectralObjectHIsoCokernel G _ n).inv ≫
    (spectralObject G).toE (intHom (show i₀ ≤ pq.2 by lia)) (intHom (show pq.2 ≤ i₂ by lia))
      (intHom (show i₂ ≤ pq.2 + r - 1 by lia)) (intHom (show i₀ ≤ i₂ by lia)) rfl
      (n - 1) n (n + 1) ≫
    ((spectralObject G).spectralSequencePageXIso Abelian.SpectralObject.coreE₂Cohomological r hr
      pq i₀ pq.2 i₂ (pq.2 + r - 1 : ℤ) (by rw [h₀]; rfl) rfl (by rw [h₂]; rfl) rfl
      (n - 1) n (n + 1) hn).inv

instance (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (i₀ i₂ : ℤ) (h₀ : i₀ = pq.2 - r + 2)
    (h₂ : i₂ = pq.2 + 1) (n : ℤ) (hn : n = pq.1 + pq.2) :
    Epi (toSpectralSequencePageX G r hr pq i₀ i₂ h₀ h₂ n hn) := by
  rw [toSpectralSequencePageX]
  infer_instance

/-- The monomorphism from the object at `pq = (p, q)` of page `r` of the spectral sequence of `G`
to `H^n(G_{i₃}/G_{i₁})`, where `i₁ = q`, `i₃ = q + r - 1` and `n = p + q`. -/
noncomputable def fromSpectralSequencePageX (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (i₁ i₃ : ℤ)
    (h₁ : i₁ = pq.2) (h₃ : i₃ = pq.2 + r - 1) (n : ℤ) (hn : n = pq.1 + pq.2) :
    ((spectralSequence G).page r).X pq ⟶
      (cokernel (G.map (intHom (show i₁ ≤ i₃ by lia)))).homology n :=
  ((spectralObject G).spectralSequencePageXIso Abelian.SpectralObject.coreE₂Cohomological r hr
      pq (pq.2 - r + 2 : ℤ) i₁ (pq.2 + 1 : ℤ) i₃ rfl (by rw [h₁]; rfl) rfl (by rw [h₃]; rfl)
      (n - 1) n (n + 1) hn).hom ≫
    (spectralObject G).fromE (intHom (show pq.2 - r + 2 ≤ i₁ by lia))
      (intHom (show i₁ ≤ pq.2 + 1 by lia)) (intHom (show pq.2 + 1 ≤ i₃ by lia))
      (intHom (show i₁ ≤ i₃ by lia)) rfl (n - 1) n (n + 1) ≫
    (spectralObjectHIsoCokernel G _ n).hom

instance (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (i₁ i₃ : ℤ) (h₁ : i₁ = pq.2)
    (h₃ : i₃ = pq.2 + r - 1) (n : ℤ) (hn : n = pq.1 + pq.2) :
    Mono (fromSpectralSequencePageX G r hr pq i₁ i₃ h₁ h₃ n hn) := by
  rw [fromSpectralSequencePageX]
  infer_instance

/-- The epimorphism `toSpectralSequencePageX` followed by the monomorphism
`fromSpectralSequencePageX` is the map `H^n(G_{i₂}/G_{i₀}) ⟶ H^n(G_{i₃}/G_{i₁})` induced by the
transition maps `G_{i₀} ⟶ G_{i₁}` and `G_{i₂} ⟶ G_{i₃}`. -/
@[reassoc (attr := simp)]
lemma toSpectralSequencePageX_fromSpectralSequencePageX (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    (i₀ i₁ i₂ i₃ : ℤ) (h₀ : i₀ = pq.2 - r + 2) (h₁ : i₁ = pq.2) (h₂ : i₂ = pq.2 + 1)
    (h₃ : i₃ = pq.2 + r - 1) (n : ℤ) (hn : n = pq.1 + pq.2) :
    toSpectralSequencePageX G r hr pq i₀ i₂ h₀ h₂ n hn ≫
        fromSpectralSequencePageX G r hr pq i₁ i₃ h₁ h₃ n hn =
      HomologicalComplex.homologyMap (cokernel.map (G.map (intHom (show i₀ ≤ i₂ by lia)))
        (G.map (intHom (show i₁ ≤ i₃ by lia))) (G.map (intHom (show i₀ ≤ i₁ by lia)))
        (G.map (intHom (show i₂ ≤ i₃ by lia))) (by simp only [← G.map_comp]; rfl)) n := by
  subst h₀ h₁ h₂ h₃
  simp only [toSpectralSequencePageX, fromSpectralSequencePageX, Category.assoc,
    Iso.inv_hom_id_assoc, Abelian.SpectralObject.toE_fromE_assoc,
    spectralObject_H_map_comp_spectralObjectHIsoCokernel_hom, Iso.inv_hom_id_assoc]
  -- Morphisms of `EInt` are unique, so the components of the morphism of arrows are the
  -- inclusions `G_{i₀} ⟶ G_{i₁}` and `G_{i₂} ⟶ G_{i₃}` by definition.
  rfl

/-- **The objects of the pages of the spectral sequence of `G` as images.** On page `r ≥ 2`, the
object at `pq = (p, q)` is the image of the map `H^n(G_{i₂}/G_{i₀}) ⟶ H^n(G_{i₃}/G_{i₁})` induced by
the transition maps, where `i₀ = q - r + 2`, `i₁ = q`, `i₂ = q + 1`, `i₃ = q + r - 1` and
`n = p + q`. -/
noncomputable def spectralSequencePageXIsoImage (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    (i₀ i₁ i₂ i₃ : ℤ) (h₀ : i₀ = pq.2 - r + 2) (h₁ : i₁ = pq.2) (h₂ : i₂ = pq.2 + 1)
    (h₃ : i₃ = pq.2 + r - 1) (n : ℤ) (hn : n = pq.1 + pq.2) :
    ((spectralSequence G).page r).X pq ≅
      image (HomologicalComplex.homologyMap (cokernel.map (G.map (intHom (show i₀ ≤ i₂ by lia)))
        (G.map (intHom (show i₁ ≤ i₃ by lia))) (G.map (intHom (show i₀ ≤ i₁ by lia)))
        (G.map (intHom (show i₂ ≤ i₃ by lia))) (by simp only [← G.map_comp]; rfl)) n) :=
  have := strongEpi_of_epi (toSpectralSequencePageX G r hr pq i₀ i₂ h₀ h₂ n hn)
  image.isoStrongEpiMono _ _
    (toSpectralSequencePageX_fromSpectralSequencePageX G r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n hn)

/-- Through `spectralSequencePageXIsoImage`, the epimorphism `toSpectralSequencePageX` is the
factorization through the image. -/
@[reassoc (attr := simp)]
lemma toSpectralSequencePageX_spectralSequencePageXIsoImage_hom (r : ℤ) (hr : 2 ≤ r)
    (pq : ℤ × ℤ) (i₀ i₁ i₂ i₃ : ℤ) (h₀ : i₀ = pq.2 - r + 2) (h₁ : i₁ = pq.2)
    (h₂ : i₂ = pq.2 + 1) (h₃ : i₃ = pq.2 + r - 1) (n : ℤ) (hn : n = pq.1 + pq.2) :
    toSpectralSequencePageX G r hr pq i₀ i₂ h₀ h₂ n hn ≫
        (spectralSequencePageXIsoImage G r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n hn).hom =
      factorThruImage _ := by
  simp [← cancel_mono (image.ι _), spectralSequencePageXIsoImage]

/-- Through `spectralSequencePageXIsoImage`, the monomorphism `fromSpectralSequencePageX` is the
inclusion of the image. -/
@[reassoc (attr := simp)]
lemma spectralSequencePageXIsoImage_hom_ι (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    (i₀ i₁ i₂ i₃ : ℤ) (h₀ : i₀ = pq.2 - r + 2) (h₁ : i₁ = pq.2) (h₂ : i₂ = pq.2 + 1)
    (h₃ : i₃ = pq.2 + r - 1) (n : ℤ) (hn : n = pq.1 + pq.2) :
    (spectralSequencePageXIsoImage G r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n hn).hom ≫ image.ι _ =
      fromSpectralSequencePageX G r hr pq i₁ i₃ h₁ h₃ n hn :=
  have := strongEpi_of_epi (toSpectralSequencePageX G r hr pq i₀ i₂ h₀ h₂ n hn)
  image.isoStrongEpiMono_hom_comp_ι _ _
    (toSpectralSequencePageX_fromSpectralSequencePageX G r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n hn)

/-- `toSpectralSequencePageX` computed with other expressions `j₁`, `j₃`, `m₀` and `m₂` for the
indices `q` and `q + r - 1` of the page object and for the degrees `n - 1` and `n + 1`. -/
private lemma toSpectralSequencePageX_eq (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (i₀ i₂ : ℤ)
    (h₀ : i₀ = pq.2 - r + 2) (h₂ : i₂ = pq.2 + 1) (n : ℤ) (hn : n = pq.1 + pq.2) (j₁ j₃ : ℤ)
    (h₁ : j₁ = pq.2) (h₃ : j₃ = pq.2 + r - 1) (m₀ m₂ : ℤ) (hm₀ : m₀ = n - 1)
    (hm₂ : m₂ = n + 1) :
    toSpectralSequencePageX G r hr pq i₀ i₂ h₀ h₂ n hn =
      (spectralObjectHIsoCokernel G _ n).inv ≫
        (spectralObject G).toE (intHom (show i₀ ≤ j₁ by lia)) (intHom (show j₁ ≤ i₂ by lia))
          (intHom (show i₂ ≤ j₃ by lia)) (intHom (show i₀ ≤ i₂ by lia)) rfl m₀ n m₂ ≫
        ((spectralObject G).spectralSequencePageXIso Abelian.SpectralObject.coreE₂Cohomological
          r hr pq i₀ j₁ i₂ j₃ (by rw [h₀]; rfl) (by rw [h₁]; rfl) (by rw [h₂]; rfl)
          (by rw [h₃]; rfl) m₀ n m₂ hn).inv := by
  subst h₁ h₃ hm₀ hm₂
  rfl

/-- **The differentials of the spectral sequence of `G` on representatives.** On page `r ≥ 2`, the
differential from `(p, q)` to `(p + r, q - r + 1)` sends the element represented by
`x ∈ H^n(G_c/G_b)` to the element represented by `δ x ∈ H^{n+1}(G_b/G_a)`, where `a = q - 2r + 3`,
`b = q - r + 2`, `c = q + 1`, `n = p + q`, and `δ` is the connecting map of the short exact
sequence `G_b/G_a ⟶ G_c/G_a ⟶ G_c/G_b`. -/
theorem toSpectralSequencePageX_d (r : ℤ) (hr : 2 ≤ r) (p q a b c : ℤ) (ha : a = q - 2 * r + 3)
    (hb : b = q - r + 2) (hc : c = q + 1) (n : ℤ) (hn : n = p + q) :
    toSpectralSequencePageX G r hr (p, q) b c hb hc n hn ≫
        ((spectralSequence G).page r).d (p, q) (p + r, q - r + 1) =
      (TauCeti.kernelCokernelCompSequence_snakeInput_L₃_shortExact
          (G.map (intHom (show a ≤ b by lia))) (G.map (intHom (show b ≤ c by lia)))).δ
          n (n + 1) rfl ≫
        toSpectralSequencePageX G r hr (p + r, q - r + 1) a b (by dsimp; lia) (by dsimp; lia)
          (n + 1) (by dsimp; lia) := by
  subst ha hb hc hn
  -- The connecting map of the spectral object at `G_{q-2r+3} ⟶ G_{q-r+2} ⟶ G_{q+1}`, read through
  -- the identifications with the cohomology of the quotients.
  have key : (spectralObjectHIsoCokernel G (intHom (show q - r + 2 ≤ q + 1 by lia)) (p + q)).inv ≫
      (spectralObject G).δ (intHom (show q - 2 * r + 3 ≤ q - r + 2 by lia))
        (intHom (show q - r + 2 ≤ q + 1 by lia)) (p + q) (p + q + 1) rfl =
      (TauCeti.kernelCokernelCompSequence_snakeInput_L₃_shortExact
          (G.map (intHom (show q - 2 * r + 3 ≤ q - r + 2 by lia)))
          (G.map (intHom (show q - r + 2 ≤ q + 1 by lia)))).δ (p + q) (p + q + 1) rfl ≫
        (spectralObjectHIsoCokernel G (intHom (show q - 2 * r + 3 ≤ q - r + 2 by lia))
          (p + q + 1)).inv :=
    (Iso.inv_comp_eq _).2 (((Iso.eq_comp_inv _).2
      (spectralObject_δ_comp_spectralObjectHIsoCokernel_hom G _ _ _ _ rfl)).trans
        (Category.assoc _ _ _))
  rw [toSpectralSequencePageX_eq G r hr (p + r, q - r + 1) _ _ _ _ _ _ (q - r + 1) q rfl
    (by dsimp; lia) (p + q) (p + q + 2) (by lia) (by lia), toSpectralSequencePageX]
  simp only [Category.assoc]
  refine (congrArg (fun t ↦ (spectralObjectHIsoCokernel G _ _).inv ≫ t)
    ((spectralObject G).toE_spectralSequence_page_d Abelian.SpectralObject.coreE₂Cohomological r
      hr (p, q) (p + r, q - r + 1) (by simp [ComplexShape.up']; lia)
      (intHom (show q - 2 * r + 3 ≤ q - r + 1 by lia)) (intHom (show q - r + 1 ≤ q - r + 2 by lia))
      (intHom (show q - r + 2 ≤ (p, q).2 by dsimp; lia))
      (intHom (show (p, q).2 ≤ q + 1 by dsimp; lia))
      (intHom (show q + 1 ≤ (p, q).2 + r - 1 by dsimp; lia))
      (intHom (show q - 2 * r + 3 ≤ q - r + 2 by lia)) (intHom (show q - r + 2 ≤ q + 1 by lia))
      (by simp; lia) (by simp) (by simp) rfl rfl rfl (p + q - 1) (p + q) (p + q + 1)
      (p + q + 2) rfl)).trans ?_
  rw [← Category.assoc, key]
  exact Category.assoc _ _ _

end CochainComplex

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-!
# The objects and differentials of a spectral object through representatives

Let `X` be a spectral object in an abelian category `C`, indexed by a category `ι`, and let
`f₁ : i₀ ⟶ i₁`, `f₂ : i₁ ⟶ i₂` and `f₃ : i₂ ⟶ i₃` be composable, with composites
`f₁₂ = f₁ ≫ f₂` and `f₂₃ = f₂ ≫ f₃`. The object `E^n(f₁, f₂, f₃)` is defined as the homology of
`H^{n-1}(f₃) ⟶ H^n(f₂) ⟶ H^{n+1}(f₁)`. It is also the image of the map
`H^n(f₁₂) ⟶ H^n(f₂₃)` induced by the morphism of arrows `(f₁, f₃) : f₁₂ ⟶ f₂₃`: this map is the
composite of the epimorphism `X.toE : H^n(f₁₂) ⟶ E^n(f₁, f₂, f₃)` and of the monomorphism
`X.fromE : E^n(f₁, f₂, f₃) ⟶ H^n(f₂₃)` (`X.toE_fromE`), so that
`E^n(f₁, f₂, f₃) ≅ image (H^n(f₁₂) ⟶ H^n(f₂₃))` (`X.EIsoImage`). The elements of `H^n(f₁₂)` are
thus representatives of the elements of `E^n(f₁, f₂, f₃)`, two representatives giving the same
element exactly when they have the same image in `H^n(f₂₃)`.

The differentials are computed on representatives by the connecting maps of `X`: for five
composable morphisms `f₁, …, f₅`, the differential `d : E^n(f₃, f₄, f₅) ⟶ E^{n+1}(f₁, f₂, f₃)`
sends the element represented by `x ∈ H^n(f₃ ≫ f₄)` to the element represented by
`δ x ∈ H^{n+1}(f₁ ≫ f₂)` (`X.toE_d`). Dually, `X.d_fromE` computes `d` followed by
`X.fromE` through `δ : H^n(f₄ ≫ f₅) ⟶ H^{n+1}(f₂ ≫ f₃)`.

The same descriptions hold for the pages of the spectral sequence of `X` attached to any
`SpectralSequenceDataCore` (`X.spectralSequencePageXIsoImage`, `X.toE_spectralSequence_page_d`,
`X.spectralSequence_page_d_fromE`).
For the spectral object of a filtered complex, `H^n(f₁₂)` and `H^n(f₂₃)` are the cohomology of the
quotients `F_{i₂}/F_{i₀}` and `F_{i₃}/F_{i₁}`, and this is the classical description of the page
objects as images and of the differentials as connecting maps on representatives.

## Main definitions

* `CategoryTheory.Abelian.SpectralObject.toE`: the epimorphism `H^n(f₁ ≫ f₂) ⟶ E^n(f₁, f₂, f₃)`.
* `CategoryTheory.Abelian.SpectralObject.fromE`: the monomorphism `E^n(f₁, f₂, f₃) ⟶ H^n(f₂ ≫ f₃)`.
* `CategoryTheory.Abelian.SpectralObject.EIsoImage`: `E^n(f₁, f₂, f₃)` is the image of
  `H^n(f₁ ≫ f₂) ⟶ H^n(f₂ ≫ f₃)`.
* `CategoryTheory.Abelian.SpectralObject.spectralSequencePageXIsoImage`: the same for the objects
  of the pages of the spectral sequence of `X`.

## Main results

* `CategoryTheory.Abelian.SpectralObject.toCycles_πE`,
  `CategoryTheory.Abelian.SpectralObject.ιE_fromOpcycles`: `X.toE` and `X.fromE` through Mathlib's
  `toCycles`, `πE`, `ιE` and `fromOpcycles`.
* `CategoryTheory.Abelian.SpectralObject.toE_descE`,
  `CategoryTheory.Abelian.SpectralObject.liftE_fromE`: Mathlib's `X.descE` and `X.liftE` factor
  through `X.toE` and `X.fromE`.
* `CategoryTheory.Abelian.SpectralObject.toE_fromE`: `X.toE ≫ X.fromE` is the map
  `H^n(f₁ ≫ f₂) ⟶ H^n(f₂ ≫ f₃)`.
* `CategoryTheory.Abelian.SpectralObject.toE_d`, `CategoryTheory.Abelian.SpectralObject.d_fromE`:
  the differentials on representatives.
* `CategoryTheory.Abelian.SpectralObject.toE_spectralSequence_page_d`,
  `CategoryTheory.Abelian.SpectralObject.spectralSequence_page_d_fromE`: the differentials of the
  pages of the spectral sequence on representatives.

## References

* J.-L. Verdier, *Des catégories dérivées des catégories abéliennes*, Astérisque 239 (1996), II.4.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge Studies in Advanced
  Mathematics 58, Cambridge University Press, 2001, §2.2.
-/

public section

namespace CategoryTheory.Abelian.SpectralObject

open Limits ComposableArrows

variable {C : Type*} [Category* C] [Abelian C]

section

variable {ι : Type*} [Category* ι] (X : SpectralObject C ι)
  {i₀ i₁ i₂ i₃ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₁₂ : i₀ ⟶ i₂) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ n₂ : ℤ)

/-- The epimorphism `H^{n₁}(f₁₂) ⟶ E^{n₁}(f₁, f₂, f₃)` for `f₁₂ = f₁ ≫ f₂`: the elements of
`H^{n₁}(f₁₂)` represent the elements of `E^{n₁}(f₁, f₂, f₃)`. It is the second map of Mathlib's
exact sequence `X.cokernelSequenceE`, named here as a morphism in its own right. -/
noncomputable def toE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.H n₁).obj (mk₁ f₁₂) ⟶ X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ :=
  X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂

/-- The composite `X.toCycles ≫ X.πE` of Mathlib's API is the epimorphism `X.toE`. -/
@[reassoc]
lemma toCycles_πE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
      X.toE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂ :=
  (rfl)

instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Epi (X.toE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂) := by
  rw [toE]
  infer_instance

/-- Mathlib's `X.descE` is the factorization of a morphism through the epimorphism `X.toE`. -/
@[reassoc (attr := simp)]
lemma toE_descE {A : C} (x : (X.H n₁).obj (mk₁ f₁₂) ⟶ A)
    (h : (X.H n₁).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂) ≫ x = 0) (hn₁ : n₀ + 1 = n₁)
    (h' : X.δ f₁₂ f₃ n₀ n₁ hn₁ ≫ x = 0) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.toE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂ ≫
      X.descE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ x h hn₁ h' hn₂ = x := by
  simp [toE]

/-- The monomorphism `E^{n₁}(f₁, f₂, f₃) ⟶ H^{n₁}(f₂₃)` for `f₂₃ = f₂ ≫ f₃`. It is the first map
of Mathlib's exact sequence `X.kernelSequenceE`, named here as a morphism in its own right. -/
noncomputable def fromE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶ (X.H n₁).obj (mk₁ f₂₃) :=
  X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₁

/-- The composite `X.ιE ≫ X.fromOpcycles` of Mathlib's API is the monomorphism `X.fromE`. -/
@[reassoc]
lemma ιE_fromOpcycles (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₁ =
      X.fromE f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂ :=
  (rfl)

instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Mono (X.fromE f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂) := by
  rw [fromE]
  infer_instance

/-- Mathlib's `X.liftE` is the factorization of a morphism through the monomorphism `X.fromE`. -/
@[reassoc (attr := simp)]
lemma liftE_fromE {A : C} (x : A ⟶ (X.H n₁).obj (mk₁ f₂₃))
    (h : x ≫ (X.H n₁).map (twoδ₁Toδ₀ f₂ f₃ f₂₃ h₂₃) = 0) (hn₂ : n₁ + 1 = n₂)
    (h' : x ≫ X.δ f₁ f₂₃ n₁ n₂ hn₂ = 0) (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.liftE f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ x h hn₂ h' hn₁ ≫
      X.fromE f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂ = x := by
  simp [fromE]

/-- The epimorphism `X.toE` followed by the monomorphism `X.fromE` is the map
`H^{n₁}(f₁₂) ⟶ H^{n₁}(f₂₃)` induced by the morphism of arrows `(f₁, f₃) : f₁₂ ⟶ f₂₃`. -/
@[reassoc (attr := simp)]
lemma toE_fromE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.toE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂ ≫ X.fromE f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂ =
      (X.H n₁).map (twoδ₁Toδ₀ f₁ f₂ f₁₂ h₁₂ ≫ twoδ₂Toδ₁ f₂ f₃ f₂₃ h₂₃) := by
  simp [toE, fromE]

/-- **`E^{n₁}(f₁, f₂, f₃)` is the image of `H^{n₁}(f₁ ≫ f₂) ⟶ H^{n₁}(f₂ ≫ f₃)`**, the map
induced by the morphism of arrows `(f₁, f₃) : f₁ ≫ f₂ ⟶ f₂ ≫ f₃`. -/
noncomputable def EIsoImage (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≅
      Limits.image ((X.H n₁).map (twoδ₁Toδ₀ f₁ f₂ f₁₂ h₁₂ ≫ twoδ₂Toδ₁ f₂ f₃ f₂₃ h₂₃)) :=
  have := strongEpi_of_epi (X.toE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂)
  image.isoStrongEpiMono _ _ (X.toE_fromE f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂)

/-- Through `X.EIsoImage`, the epimorphism `X.toE` is the factorization through the image. -/
@[reassoc (attr := simp)]
lemma toE_EIsoImage_hom (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.toE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂ ≫
        (X.EIsoImage f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂).hom =
      factorThruImage _ := by
  simp [← cancel_mono (Limits.image.ι _), EIsoImage]

/-- Through `X.EIsoImage`, the monomorphism `X.fromE` is the inclusion of the image. -/
@[reassoc (attr := simp)]
lemma EIsoImage_hom_ι (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.EIsoImage f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂).hom ≫ Limits.image.ι _ =
      X.fromE f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂ :=
  have := strongEpi_of_epi (X.toE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂)
  image.isoStrongEpiMono_hom_comp_ι _ _ (X.toE_fromE f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂)

end

section

variable {ι : Type*} [Category* ι] (X : SpectralObject C ι)
  {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (f₁₂ : i₀ ⟶ i₂) (h₁₂ : f₁ ≫ f₂ = f₁₂)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃) (f₃₄ : i₂ ⟶ i₄) (h₃₄ : f₃ ≫ f₄ = f₃₄)
  (f₄₅ : i₃ ⟶ i₅) (h₄₅ : f₄ ≫ f₅ = f₄₅) (n₀ n₁ n₂ n₃ : ℤ)

/-- **The differentials on representatives.** The differential
`d : E^{n₁}(f₃, f₄, f₅) ⟶ E^{n₂}(f₁, f₂, f₃)` sends the element represented by
`x ∈ H^{n₁}(f₃ ≫ f₄)` to the element represented by the image `δ x ∈ H^{n₂}(f₁ ≫ f₂)` of `x` under
the connecting map of `X`. -/
@[reassoc]
lemma toE_d (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.toE f₃ f₄ f₅ f₃₄ h₃₄ n₀ n₁ n₂ hn₁ hn₂ ≫ X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ =
      X.δ f₁₂ f₃₄ n₁ n₂ hn₂ ≫ X.toE f₁ f₂ f₃ f₁₂ h₁₂ n₁ n₂ n₃ hn₂ hn₃ := by
  simp only [toE, Category.assoc]
  exact X.toCycles_πE_d f₁ f₂ f₃ f₄ f₅ f₁₂ h₁₂ f₃₄ h₃₄ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃

/-- **The differentials, dually.** The differential `d : E^{n₁}(f₃, f₄, f₅) ⟶ E^{n₂}(f₁, f₂, f₃)`
followed by `X.fromE : E^{n₂}(f₁, f₂, f₃) ⟶ H^{n₂}(f₂ ≫ f₃)` is `X.fromE` followed by the
connecting map `δ : H^{n₁}(f₄ ≫ f₅) ⟶ H^{n₂}(f₂ ≫ f₃)` of `X`. -/
@[reassoc]
lemma d_fromE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫ X.fromE f₁ f₂ f₃ f₂₃ h₂₃ n₁ n₂ n₃ hn₂ hn₃ =
      X.fromE f₃ f₄ f₅ f₄₅ h₄₅ n₀ n₁ n₂ hn₁ hn₂ ≫ X.δ f₂₃ f₄₅ n₁ n₂ hn₂ := by
  simp only [fromE, Category.assoc]
  exact X.d_ιE_fromOpcycles f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃ _ rfl f₄₅ h₄₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃

end

section SpectralSequence

variable {ι κ : Type*} [Preorder ι] (X : SpectralObject C ι)
  {c : ℤ → ComplexShape κ} {r₀ : ℤ} (data : SpectralSequenceDataCore ι c r₀)
  [X.HasSpectralSequence data]

/-- **The objects of the pages of the spectral sequence as images.** On page `r`, the object at
`pq` is the image of the map `H^n(i₀ ≤ i₂) ⟶ H^n(i₁ ≤ i₃)`, where `i₀ ≤ i₁ ≤ i₂ ≤ i₃` are the
indices `data.i₀ r pq ≤ data.i₁ pq ≤ data.i₂ pq ≤ data.i₃ r pq` of `pq` and `n = data.deg pq`. -/
noncomputable def spectralSequencePageXIsoImage (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (i₀ i₁ i₂ i₃ : ι) (h₀ : i₀ = data.i₀ r pq) (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ = data.i₂ pq)
    (h₃ : i₃ = data.i₃ r pq) (n : ℤ) (hn : n = data.deg pq) :
    ((X.spectralSequence data).page r).X pq ≅
      Limits.image ((X.H n).map
        (twoδ₁Toδ₀ (homOfLE (data.le₀₁' r hr pq h₀ h₁)) (homOfLE (data.le₁₂' pq h₁ h₂))
            (homOfLE ((data.le₀₁' r hr pq h₀ h₁).trans (data.le₁₂' pq h₁ h₂))) rfl ≫
          twoδ₂Toδ₁ (homOfLE (data.le₁₂' pq h₁ h₂)) (homOfLE (data.le₂₃' r hr pq h₂ h₃))
            (homOfLE ((data.le₁₂' pq h₁ h₂).trans (data.le₂₃' r hr pq h₂ h₃))) rfl)) :=
  X.spectralSequencePageXIso data r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ (n - 1) n (n + 1) hn ≪≫
    X.EIsoImage _ _ _ _ rfl _ rfl (n - 1) n (n + 1)

/-- The isomorphism `spectralSequencePageXIsoImage` is the identification of the page object with
`E^n(i₀ ≤ i₁ ≤ i₂ ≤ i₃)` followed by `EIsoImage`. -/
lemma spectralSequencePageXIsoImage_hom (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (i₀ i₁ i₂ i₃ : ι) (h₀ : i₀ = data.i₀ r pq) (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ = data.i₂ pq)
    (h₃ : i₃ = data.i₃ r pq) (n : ℤ) (hn : n = data.deg pq) :
    (X.spectralSequencePageXIsoImage data r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n hn).hom =
      (X.spectralSequencePageXIso data r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ (n - 1) n (n + 1) hn).hom ≫
        (X.EIsoImage _ _ _ _ rfl _ rfl (n - 1) n (n + 1)).hom :=
  (rfl)

/-- **The differentials of the pages of the spectral sequence on representatives.** Let
`(c r).Rel pq pq'` and let `i₀ ≤ ⋯ ≤ i₅` be the indices with `i₂ ≤ i₃ ≤ i₄ ≤ i₅` those of `pq`
and `i₀ ≤ i₁ ≤ i₂ ≤ i₃` those of `pq'` on page `r`. The differential from `pq` to `pq'` sends the
element represented by `x ∈ H^n(i₂ ≤ i₄)` to the element represented by the image
`δ x ∈ H^{n+1}(i₀ ≤ i₂)` of `x` under the connecting map of `X`. -/
@[reassoc]
lemma toE_spectralSequence_page_d (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) (hpq : (c r).Rel pq pq')
    {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (f₁₂ : i₀ ⟶ i₂) (f₃₄ : i₂ ⟶ i₄)
    (h₀ : i₀ = data.i₀ r pq') (h₁ : i₁ = data.i₁ pq') (h₂ : i₂ = data.i₀ r pq)
    (h₃ : i₃ = data.i₁ pq) (h₄ : i₄ = data.i₂ pq) (h₅ : i₅ = data.i₃ r pq)
    (n₀ n₁ n₂ n₃ : ℤ) (hn₁' : n₁ = data.deg pq) (hn₁ : n₀ + 1 = n₁ := by lia)
    (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.toE f₃ f₄ f₅ f₃₄ (Subsingleton.elim _ _) n₀ n₁ n₂ hn₁ hn₂ ≫
        (X.spectralSequencePageXIso data r hr _ _ _ _ _ h₂ h₃ h₄ h₅ _ _ _ hn₁').inv ≫
        ((X.spectralSequence data).page r).d pq pq' =
      X.δ f₁₂ f₃₄ n₁ n₂ hn₂ ≫ X.toE f₁ f₂ f₃ f₁₂ (Subsingleton.elim _ _) n₁ n₂ n₃ hn₂ hn₃ ≫
        (X.spectralSequencePageXIso data r hr _ _ _ _ _ h₀ h₁
          (by rw [h₂, ← data.hc₀₂ r pq pq' hpq]) (by rw [h₃, data.hc₁₃ r pq pq' hpq]) _ _ _
            (by simpa only [← hn₂, hn₁'] using data.hc r pq pq' hpq)).inv := by
  -- Morphisms in a preorder are unique; we replace `f₃`, `f₄`, `f₅` by the morphisms in the
  -- identification of the page object at `pq`, so that the identification cancels syntactically.
  obtain rfl : f₃ = homOfLE (data.le₀₁' r hr pq h₂ h₃) := Subsingleton.elim _ _
  obtain rfl : f₄ = homOfLE (data.le₁₂' pq h₃ h₄) := Subsingleton.elim _ _
  obtain rfl : f₅ = homOfLE (data.le₂₃' r hr pq h₄ h₅) := Subsingleton.elim _ _
  rw [X.spectralSequence_page_d_eq data r hr pq pq' hpq f₁ f₂
    (homOfLE (data.le₀₁' r hr pq h₂ h₃)) (homOfLE (data.le₁₂' pq h₃ h₄))
    (homOfLE (data.le₂₃' r hr pq h₄ h₅)) h₀ h₁ h₂ h₃ h₄ h₅ n₀ n₁ n₂ n₃ hn₁' hn₁ hn₂ hn₃,
    Iso.inv_hom_id_assoc]
  exact X.toE_d_assoc f₁ f₂ _ _ _ f₁₂ _ f₃₄ _ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ _

/-- **The differentials of the pages of the spectral sequence, dually.** With the indices of
`toE_spectralSequence_page_d`, the differential from `pq` to `pq'` followed by
`X.fromE : E^{n+1}(i₀ ≤ i₁ ≤ i₂ ≤ i₃) ⟶ H^{n+1}(i₁ ≤ i₃)` is `X.fromE` followed by the connecting
map `δ : H^n(i₃ ≤ i₅) ⟶ H^{n+1}(i₁ ≤ i₃)` of `X`. -/
@[reassoc]
lemma spectralSequence_page_d_fromE (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ)
    (hpq : (c r).Rel pq pq') {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂)
    (f₃ : i₂ ⟶ i₃) (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (f₂₃ : i₁ ⟶ i₃) (f₄₅ : i₃ ⟶ i₅)
    (h₀ : i₀ = data.i₀ r pq') (h₁ : i₁ = data.i₁ pq') (h₂ : i₂ = data.i₀ r pq)
    (h₃ : i₃ = data.i₁ pq) (h₄ : i₄ = data.i₂ pq) (h₅ : i₅ = data.i₃ r pq)
    (n₀ n₁ n₂ n₃ : ℤ) (hn₁' : n₁ = data.deg pq) (hn₁ : n₀ + 1 = n₁ := by lia)
    (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    ((X.spectralSequence data).page r).d pq pq' ≫
        (X.spectralSequencePageXIso data r hr _ _ _ _ _ h₀ h₁
          (by rw [h₂, ← data.hc₀₂ r pq pq' hpq]) (by rw [h₃, data.hc₁₃ r pq pq' hpq]) _ _ _
            (by simpa only [← hn₂, hn₁'] using data.hc r pq pq' hpq)).hom ≫
        X.fromE f₁ f₂ f₃ f₂₃ (Subsingleton.elim _ _) n₁ n₂ n₃ hn₂ hn₃ =
      (X.spectralSequencePageXIso data r hr _ _ _ _ _ h₂ h₃ h₄ h₅ _ _ _ hn₁').hom ≫
        X.fromE f₃ f₄ f₅ f₄₅ (Subsingleton.elim _ _) n₀ n₁ n₂ hn₁ hn₂ ≫
          X.δ f₂₃ f₄₅ n₁ n₂ hn₂ := by
  -- As in `toE_spectralSequence_page_d`, we replace `f₁`, …, `f₅` by the morphisms in the
  -- identifications of the page objects at `pq'` and `pq`, so that the identification at `pq'`
  -- cancels syntactically.
  obtain rfl : f₁ = homOfLE (data.le₀₁' r hr pq' h₀ h₁) := Subsingleton.elim _ _
  obtain rfl : f₂ = homOfLE (data.le₁₂' pq' h₁ (by rw [h₂, ← data.hc₀₂ r pq pq' hpq])) :=
    Subsingleton.elim _ _
  obtain rfl : f₃ = homOfLE (data.le₀₁' r hr pq h₂ h₃) := Subsingleton.elim _ _
  obtain rfl : f₄ = homOfLE (data.le₁₂' pq h₃ h₄) := Subsingleton.elim _ _
  obtain rfl : f₅ = homOfLE (data.le₂₃' r hr pq h₄ h₅) := Subsingleton.elim _ _
  rw [X.spectralSequence_page_d_eq data r hr pq pq' hpq _ _
    (homOfLE (data.le₀₁' r hr pq h₂ h₃)) (homOfLE (data.le₁₂' pq h₃ h₄))
    (homOfLE (data.le₂₃' r hr pq h₄ h₅)) h₀ h₁ h₂ h₃ h₄ h₅ n₀ n₁ n₂ n₃ hn₁' hn₁ hn₂ hn₃,
    Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg _ (X.d_fromE _ _ _ _ _ f₂₃ _ f₄₅ _ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃)

end SpectralSequence

end CategoryTheory.Abelian.SpectralObject

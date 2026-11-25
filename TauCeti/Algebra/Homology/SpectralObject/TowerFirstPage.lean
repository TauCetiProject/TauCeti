/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.FirstPage
public import TauCeti.Algebra.Homology.SpectralObject.Image
public import TauCeti.Algebra.Homology.SpectralObject.SpectralSequenceMap
public import TauCeti.Algebra.Homology.SpectralObject.Tower
public import TauCeti.CategoryTheory.Subobject.Image

/-!
# The towers of the spectral sequence of a spectral object through the first page

Let `X` be a spectral object in an abelian category, indexed by a preorder `ι`, and let `data` be a
recipe for spectral sequences starting on the page `r₀`, with `X.HasSpectralSequence data` and
`data.HasFirstPageComputation`. Mathlib's `spectralSequenceFirstPageXIso` identifies the object at
`pq` on the page `r₀` with `H^n(i₁ ≤ i₂)`, where `n = data.deg pq`, `i₁ = data.i₁ pq` and
`i₂ = data.i₂ pq`. Write `i₀ = data.i₀ r pq` and `i₃ = data.i₃ r pq` for the outer indices on the
page `r`. Through this identification, the cycle and boundary towers of
`TauCeti/Algebra/Homology/SpectralObject/Tower.lean` are:

* `Z_r(pq)` is the kernel of the connecting map `δ : H^n(i₁ ≤ i₂) ⟶ H^{n+1}(i₀ ≤ i₁)`
  (`SpectralObject.cyclesSubobject_spectralSequence_eq_kernelSubobject_δ`), equivalently the image
  of `H^n(i₀ ≤ i₂) ⟶ H^n(i₁ ≤ i₂)`
  (`SpectralObject.cyclesSubobject_spectralSequence_eq_imageSubobject`);
* `B_r(pq)` is the image of the connecting map `δ : H^{n-1}(i₂ ≤ i₃) ⟶ H^n(i₁ ≤ i₂)`
  (`SpectralObject.boundariesSubobject_spectralSequence_eq_imageSubobject_δ`), equivalently the
  kernel of `H^n(i₁ ≤ i₂) ⟶ H^n(i₁ ≤ i₃)`
  (`SpectralObject.boundariesSubobject_spectralSequence_eq_kernelSubobject`).

The indices are given by equations, so that the statements specialize to each recipe with its
explicit indices: for `coreE₂Cohomological` at `(p, q)`, `n = p + q`, `i₀ = q - r + 2`, `i₁ = q`,
`i₂ = q + 1` and `i₃ = q + r - 1`; for `coreE₂CohomologicalFin l` the clamped indices
`i₀ = max(0, q - r + 2)` and `i₃ = min(l, q + r - 1)`.

The proof compares the embedding `X.fromE : E^n(i₀ ≤ i₁ ≤ i₂ ≤ i₃) ⟶ H^n(i₁ ≤ i₃)` with the first
page identification (`SpectralObject.spectralSequenceFirstPageXIso_hom_eq`, through
`SpectralObject.EIsoH_hom_eq_fromE`), and then uses the exact sequences
`H^n(i₀ ≤ i₂) ⟶ H^n(i₁ ≤ i₂) ⟶ H^{n+1}(i₀ ≤ i₁)` and
`H^{n-1}(i₂ ≤ i₃) ⟶ H^n(i₁ ≤ i₂) ⟶ H^n(i₁ ≤ i₃)` of the spectral object.

## References

* G. O. Helle and J. Rognes, *Boardman's whole-plane obstruction group for Cartan–Eilenberg
  systems*, Documenta Math. 24 (2019), 1855–1878, Definition 4.5 and Remark 4.6.
-/

public section

namespace CategoryTheory.Abelian.SpectralObject

open ComposableArrows Limits Subobject

variable {C : Type*} [Category* C] [Abelian C]

/-- The identification `X.EIsoH` of `E^n(𝟙, f, 𝟙)` with `H^n(f)` is the embedding `X.fromE`. -/
lemma EIsoH_hom_eq_fromE {ι : Type*} [Category* ι] (X : SpectralObject C ι) {i j : ι}
    (f : i ⟶ j) (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom =
      X.fromE (𝟙 i) f (𝟙 j) f (Category.comp_id f) n₀ n₁ n₂ hn₁ hn₂ := by
  rw [← cancel_mono (X.opcyclesIsoH f n₀ n₁ hn₁).inv, EIsoH_hom_opcyclesIsoH_inv,
    ← X.ιE_fromOpcycles (𝟙 i) f (𝟙 j) f (Category.comp_id f) n₀ n₁ n₂ hn₁ hn₂, Category.assoc,
    X.opcyclesIsoH_hom_inv_id f n₀ n₁ hn₁, Category.comp_id]

variable {ι κ : Type*} [Preorder ι] (X : SpectralObject C ι)

/-- The canonical map `E^{n₁}(i₀ ≤ i₂ ≤ i₃ ≤ i₄) ⟶ E^{n₁}(i₁ ≤ i₂ ≤ i₃ ≤ i₄)` for `i₀ ≤ i₁`
commutes with the embeddings `X.fromE` into `H^{n₁}(i₂ ≤ i₄)`. -/
@[reassoc]
lemma mapFourδ₁Toδ₀'_fromE (i₀ i₁ i₂ i₃ i₄ : ι) (hi₀₁ : i₀ ≤ i₁) (hi₁₂ : i₁ ≤ i₂) (hi₂₃ : i₂ ≤ i₃)
    (hi₃₄ : i₃ ≤ i₄) (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia)
    (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ ≫
        X.fromE (homOfLE hi₁₂) (homOfLE hi₂₃) (homOfLE hi₃₄) (homOfLE (hi₂₃.trans hi₃₄)) rfl
          n₀ n₁ n₂ hn₁ hn₂ =
      X.fromE (homOfLE (hi₀₁.trans hi₁₂)) (homOfLE hi₂₃) (homOfLE hi₃₄)
        (homOfLE (hi₂₃.trans hi₃₄)) rfl n₀ n₁ n₂ hn₁ hn₂ := by
  have h := X.map_fromE (homOfLE (hi₀₁.trans hi₁₂)) (homOfLE hi₂₃) (homOfLE hi₃₄)
    (homOfLE (hi₂₃.trans hi₃₄)) rfl (homOfLE hi₁₂) (homOfLE hi₂₃) (homOfLE hi₃₄)
    (homOfLE (hi₂₃.trans hi₃₄)) rfl (fourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄) n₀ n₁ n₂
    (𝟙 _) (Subsingleton.elim _ _) (Subsingleton.elim _ _) hn₁ hn₂
  rw [Functor.map_id, Category.comp_id] at h
  exact h

variable {c : ℤ → ComplexShape κ} {r₀ : ℤ} (data : SpectralSequenceDataCore ι c r₀)
  [data.HasFirstPageComputation] [X.HasSpectralSequence data] (pq : κ)

/-- **The first page identification through the embedding `X.fromE`.** For any presentation
`i₀ ≤ i₁ ≤ i₂ ≤ i₃` of the indices of `pq` on the page `r₀` (so that `i₀ = i₁` and `i₂ = i₃`), the
isomorphism `spectralSequenceFirstPageXIso` onto `H^n(i₁ ≤ i₂)` is the identification with
`E^n(i₀ ≤ i₁ ≤ i₂ ≤ i₃)`, followed by `X.fromE` into `H^n(i₁ ≤ i₃)` and by any morphism of arrows
`H^n(i₁ ≤ i₃) ⟶ H^n(i₁ ≤ i₂)`. -/
lemma spectralSequenceFirstPageXIso_hom_eq (i₀ i₁ i₂ i₃ : ι) (h₀ : i₀ = data.i₀ r₀ pq)
    (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ = data.i₂ pq) (h₃ : i₃ = data.i₃ r₀ pq) (n : ℤ)
    (hn : n = data.deg pq)
    (ε : mk₁ (homOfLE ((data.le₁₂' pq h₁ h₂).trans (data.le₂₃' r₀ le_rfl pq h₂ h₃))) ⟶
      mk₁ (homOfLE (data.le₁₂' pq h₁ h₂))) :
    (X.spectralSequenceFirstPageXIso data pq i₁ i₂ h₁ h₂ n hn).hom =
      (X.spectralSequencePageXIso data r₀ le_rfl pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃
          (n - 1) n (n + 1) hn).hom ≫
        X.fromE (homOfLE (data.le₀₁' r₀ le_rfl pq h₀ h₁)) (homOfLE (data.le₁₂' pq h₁ h₂))
          (homOfLE (data.le₂₃' r₀ le_rfl pq h₂ h₃))
          (homOfLE ((data.le₁₂' pq h₁ h₂).trans (data.le₂₃' r₀ le_rfl pq h₂ h₃))) rfl
          (n - 1) n (n + 1) ≫
        (X.H n).map ε := by
  obtain rfl : i₀ = i₁ := by rw [h₀, h₁, data.hi₀₁]
  obtain rfl : i₃ = i₂ := by rw [h₃, h₂, data.hi₂₃]
  obtain rfl : ε = 𝟙 _ := hom_ext₁ (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  rw [X.spectralSequenceFirstPageXIso_hom data pq _ _ h₁ h₂ (n - 1) n (n + 1) hn,
    X.EIsoH_hom_eq_fromE _ (n - 1) n (n + 1), Functor.map_id, Category.comp_id]
  rfl

/-- **The cycle tower as an image, through the first page.** Through
`spectralSequenceFirstPageXIso`, the cycles `Z_r(pq)` are the image of the map
`H^n(i₀ ≤ i₂) ⟶ H^n(i₁ ≤ i₂)`, where `i₀ = data.i₀ r pq`, `i₁ = data.i₁ pq`, `i₂ = data.i₂ pq` and
`n = data.deg pq`. -/
theorem cyclesSubobject_spectralSequence_eq_imageSubobject (r : ℤ) (hr : r₀ ≤ r)
    (i₀ i₁ i₂ : ι) (h₀ : i₀ = data.i₀ r pq) (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ = data.i₂ pq)
    (n : ℤ) (hn : n = data.deg pq) :
    (X.spectralSequence data).cyclesSubobject pq r hr =
      imageSubobject ((X.H n).map (twoδ₁Toδ₀' i₀ i₁ i₂ (data.le₀₁' r hr pq h₀ h₁)
          (data.le₁₂' pq h₁ h₂)) ≫
        (X.spectralSequenceFirstPageXIso data pq i₁ i₂ h₁ h₂ n hn).inv) := by
  subst h₀ h₁ h₂ hn
  let ε : mk₁ (homOfLE ((data.le₁₂ pq).trans (data.le₂₃ r₀ pq))) ⟶ mk₁ (homOfLE (data.le₁₂ pq)) :=
    homMk₁ (𝟙 _) (homOfLE (data.hi₂₃ pq).ge) (Subsingleton.elim _ _)
  have hα : X.towerα data pq r hr ≫
      (X.spectralSequenceFirstPageXIso data pq _ _ rfl rfl _ rfl).hom =
        X.fromE (homOfLE ((data.antitone_i₀ r₀ r pq le_rfl hr).trans (data.le₀₁ r₀ pq)))
          (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r₀ pq))
          (homOfLE ((data.le₁₂ pq).trans (data.le₂₃ r₀ pq))) rfl
          (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) ≫ (X.H _).map ε := by
    rw [X.spectralSequenceFirstPageXIso_hom_eq data pq _ _ _ _ rfl rfl rfl rfl _ rfl ε,
      towerα_def, Category.assoc, Iso.inv_hom_id_assoc]
    exact X.mapFourδ₁Toδ₀'_fromE_assoc ..
  rw [cyclesSubobject_spectralSequence, ← Category.comp_id (X.towerα data pq r hr),
    ← Iso.hom_inv_id (X.spectralSequenceFirstPageXIso data pq _ _ rfl rfl _ rfl),
    reassoc_of% hα, ← imageSubobject_comp_eq_of_epi
      (X.toE _ _ _ _ rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)),
    X.toE_fromE_assoc _ _ _ _ _ _ _ (data.deg pq - 1) (data.deg pq) (data.deg pq + 1),
    ← Functor.map_comp_assoc]
  -- Morphisms of arrows in a preorder are unique.
  congr 3

/-- **The cycle tower as a kernel of `δ`, through the first page.** Through
`spectralSequenceFirstPageXIso`, the cycles `Z_r(pq)` are the kernel of the connecting map
`δ : H^n(i₁ ≤ i₂) ⟶ H^{n+1}(i₀ ≤ i₁)`, where `i₀ = data.i₀ r pq`, `i₁ = data.i₁ pq`,
`i₂ = data.i₂ pq` and `n = data.deg pq`. -/
theorem cyclesSubobject_spectralSequence_eq_kernelSubobject_δ (r : ℤ) (hr : r₀ ≤ r)
    (i₀ i₁ i₂ : ι) (h₀ : i₀ = data.i₀ r pq) (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ = data.i₂ pq)
    (n : ℤ) (hn : n = data.deg pq) :
    (X.spectralSequence data).cyclesSubobject pq r hr =
      kernelSubobject ((X.spectralSequenceFirstPageXIso data pq i₁ i₂ h₁ h₂ n hn).hom ≫
        X.δ (homOfLE (data.le₀₁' r hr pq h₀ h₁)) (homOfLE (data.le₁₂' pq h₁ h₂)) n (n + 1)) := by
  rw [X.cyclesSubobject_spectralSequence_eq_imageSubobject data pq r hr i₀ i₁ i₂ h₀ h₁ h₂ n hn]
  set φ := X.spectralSequenceFirstPageXIso data pq i₁ i₂ h₁ h₂ n hn
  have hS := X.exact₃ (homOfLE (data.le₀₁' r hr pq h₀ h₁)) (homOfLE (data.le₁₂' pq h₁ h₂)) _ rfl
    n (n + 1)
  let S : ShortComplex C := ShortComplex.mk
    ((X.H n).map (twoδ₁Toδ₀' i₀ i₁ i₂ (data.le₀₁' r hr pq h₀ h₁) (data.le₁₂' pq h₁ h₂)) ≫ φ.inv)
    (φ.hom ≫ X.δ (homOfLE (data.le₀₁' r hr pq h₀ h₁)) (homOfLE (data.le₁₂' pq h₁ h₂)) n (n + 1))
    (by simp)
  have e : X.sc₃ _ _ _ rfl n (n + 1) ≅ S :=
    ShortComplex.isoMk (Iso.refl _) φ.symm (Iso.refl _) (by simp [S]) (by simp [S])
  exact (ShortComplex.exact_iff_image_eq_kernel S).1 (ShortComplex.exact_of_iso e hS)

/-- **The boundary tower as a kernel, through the first page.** Through
`spectralSequenceFirstPageXIso`, the boundaries `B_r(pq)` are the kernel of the map
`H^n(i₁ ≤ i₂) ⟶ H^n(i₁ ≤ i₃)`, where `i₁ = data.i₁ pq`, `i₂ = data.i₂ pq`, `i₃ = data.i₃ r pq` and
`n = data.deg pq`. -/
theorem boundariesSubobject_spectralSequence_eq_kernelSubobject (r : ℤ) (hr : r₀ ≤ r)
    (i₁ i₂ i₃ : ι) (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ = data.i₂ pq) (h₃ : i₃ = data.i₃ r pq)
    (n : ℤ) (hn : n = data.deg pq) :
    (X.spectralSequence data).boundariesSubobject pq r hr =
      kernelSubobject ((X.spectralSequenceFirstPageXIso data pq i₁ i₂ h₁ h₂ n hn).hom ≫
        (X.H n).map (twoδ₂Toδ₁' i₁ i₂ i₃ (data.le₁₂' pq h₁ h₂) (data.le₂₃' r hr pq h₂ h₃))) := by
  subst h₁ h₂ h₃ hn
  let ε : mk₁ (homOfLE ((data.le₁₂ pq).trans (data.le₂₃ r₀ pq))) ⟶ mk₁ (homOfLE (data.le₁₂ pq)) :=
    homMk₁ (𝟙 _) (homOfLE (data.hi₂₃ pq).ge) (Subsingleton.elim _ _)
  have h : (X.spectralSequenceFirstPageXIso data pq _ _ rfl rfl _ rfl).hom ≫
      (X.H (data.deg pq)).map (twoδ₂Toδ₁' (data.i₁ pq) (data.i₂ pq) (data.i₃ r pq)
        (data.le₁₂ pq) (data.le₂₃ r pq)) =
      X.towerβ data pq r hr ≫
        X.fromE (homOfLE (data.le₀₁ r₀ pq)) (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r pq))
          (homOfLE ((data.le₁₂ pq).trans (data.le₂₃ r pq))) rfl
          (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) := by
    rw [X.spectralSequenceFirstPageXIso_hom_eq data pq _ _ _ _ rfl rfl rfl rfl _ rfl ε,
      towerβ_def, Category.assoc, Category.assoc, Category.assoc, ← Functor.map_comp,
      X.mapFourδ₄Toδ₃'_fromE _ _ _ _ _ _ _ _ _ (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)]
    -- Morphisms of arrows in a preorder are unique.
    congr 3
  simp only [boundariesSubobject_spectralSequence, h, kernelSubobject_comp_mono]

/-- **The boundary tower as an image of `δ`, through the first page.** Through
`spectralSequenceFirstPageXIso`, the boundaries `B_r(pq)` are the image of the connecting map
`δ : H^{n-1}(i₂ ≤ i₃) ⟶ H^n(i₁ ≤ i₂)`, where `i₁ = data.i₁ pq`, `i₂ = data.i₂ pq`,
`i₃ = data.i₃ r pq` and `n = data.deg pq`. -/
theorem boundariesSubobject_spectralSequence_eq_imageSubobject_δ (r : ℤ) (hr : r₀ ≤ r)
    (i₁ i₂ i₃ : ι) (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ = data.i₂ pq) (h₃ : i₃ = data.i₃ r pq)
    (n : ℤ) (hn : n = data.deg pq) :
    (X.spectralSequence data).boundariesSubobject pq r hr =
      imageSubobject (X.δ (homOfLE (data.le₁₂' pq h₁ h₂)) (homOfLE (data.le₂₃' r hr pq h₂ h₃))
          (n - 1) n ≫ (X.spectralSequenceFirstPageXIso data pq i₁ i₂ h₁ h₂ n hn).inv) := by
  rw [X.boundariesSubobject_spectralSequence_eq_kernelSubobject data pq r hr i₁ i₂ i₃ h₁ h₂ h₃ n
    hn]
  set φ := X.spectralSequenceFirstPageXIso data pq i₁ i₂ h₁ h₂ n hn
  have hS := X.exact₁ (homOfLE (data.le₁₂' pq h₁ h₂)) (homOfLE (data.le₂₃' r hr pq h₂ h₃)) _ rfl
    (n - 1) n
  let S : ShortComplex C := ShortComplex.mk
    (X.δ (homOfLE (data.le₁₂' pq h₁ h₂)) (homOfLE (data.le₂₃' r hr pq h₂ h₃)) (n - 1) n ≫ φ.inv)
    (φ.hom ≫ (X.H n).map (twoδ₂Toδ₁' i₁ i₂ i₃ (data.le₁₂' pq h₁ h₂) (data.le₂₃' r hr pq h₂ h₃)))
    (by simp)
  have e : X.sc₁ _ _ _ rfl (n - 1) n ≅ S :=
    ShortComplex.isoMk (Iso.refl _) φ.symm (Iso.refl _) (by simp [S]) (by simp [S])
  exact ((ShortComplex.exact_iff_image_eq_kernel S).1 (ShortComplex.exact_of_iso e hS)).symm

section Naturality

variable {X} {Y : SpectralObject C ι} (φ : X ⟶ Y) [Y.HasSpectralSequence data]

omit [data.HasFirstPageComputation] in
/-- **Naturality of the cycle tower in the spectral object.** The first-page component
`spectralSequencePageXMap data φ r₀` of the morphism of spectral sequences induced by `φ : X ⟶ Y`
maps `Z_r(pq)` of `X` into `Z_r(pq)` of `Y`. Through `spectralSequenceFirstPageXIso` this
component is the component of `φ` on `H^n(i₁ ≤ i₂)`
(`spectralSequencePageXMap_comp_spectralSequenceFirstPageXIso_hom`). -/
theorem cyclesSubobject_spectralSequence_le_pullback (r : ℤ) (hr : r₀ ≤ r) :
    (X.spectralSequence data).cyclesSubobject pq r hr ≤
      (Subobject.pullback (spectralSequencePageXMap data φ r₀ le_rfl pq)).obj
        ((Y.spectralSequence data).cyclesSubobject pq r hr) := by
  simpa using (X.spectralSequence data).cyclesSubobject_le_pullback pq
    (spectralSequenceMap data φ) r hr

omit [data.HasFirstPageComputation] in
/-- **Naturality of the boundary tower in the spectral object.** The first-page component
`spectralSequencePageXMap data φ r₀` of the morphism of spectral sequences induced by `φ : X ⟶ Y`
maps `B_r(pq)` of `X` into `B_r(pq)` of `Y`. -/
theorem boundariesSubobject_spectralSequence_le_pullback (r : ℤ) (hr : r₀ ≤ r) :
    (X.spectralSequence data).boundariesSubobject pq r hr ≤
      (Subobject.pullback (spectralSequencePageXMap data φ r₀ le_rfl pq)).obj
        ((Y.spectralSequence data).boundariesSubobject pq r hr) := by
  simpa using (X.spectralSequence data).boundariesSubobject_le_pullback pq
    (spectralSequenceMap data φ) r hr

end Naturality

end CategoryTheory.Abelian.SpectralObject

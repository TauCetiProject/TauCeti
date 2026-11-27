/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.EpiMono
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-!
# Raising the last index of `E^n(i₀ ≤ i₁ ≤ i₂ ≤ i₃)` along a monomorphism

Let `X` be a spectral object in an abelian category, indexed by a preorder. For
`i₀ ≤ i₁ ≤ i₂ ≤ i₃ ≤ i₄`, the canonical map `E^n(i₀ ≤ i₁ ≤ i₂ ≤ i₃) ⟶ E^n(i₀ ≤ i₁ ≤ i₂ ≤ i₄)`
(Mathlib's `CategoryTheory.Abelian.SpectralObject.mapFourδ₄Toδ₃'`) is always an epimorphism, and
Mathlib shows that it is an isomorphism when `H^{n-1}(i₃ ≤ i₄)` vanishes. This file proves that it
is an isomorphism as soon as the map `H^n(i₀ ≤ i₃) ⟶ H^n(i₀ ≤ i₄)` is a monomorphism
(`CategoryTheory.Abelian.SpectralObject.isIso_mapFourδ₄Toδ₃'_of_mono`), a condition on degree `n`
alone, which follows from the vanishing of `H^{n-1}(i₃ ≤ i₄)` by exactness of
`H^{n-1}(i₃ ≤ i₄) ⟶ H^n(i₀ ≤ i₃) ⟶ H^n(i₀ ≤ i₄)`.

For a spectral object indexed by `EInt`, with `i₀ = ⊥` and `i₄ = ⊤`, this identifies the objects
`E^n(⊥ ≤ q ≤ q + 1 ≤ j)` of the late pages of its spectral sequence with the limit object
`E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)` as soon as `H^n(⊥ ≤ j) ⟶ H^n(⊥ ≤ ⊤)` is a monomorphism, which is what the
convergence of the spectral sequence in a range of degrees needs on the side of `⊤`
(`TauCeti.Algebra.Homology.SpectralObject.ConvergenceBounds`).

The proof compares Mathlib's short exact sequences
`0 ⟶ opZ^n(i₀ ≤ i₁, i₁ ≤ i₃) ⟶ opZ^n(i₀ ≤ i₂, i₂ ≤ i₃) ⟶ E^n(i₀ ≤ i₁ ≤ i₂ ≤ i₃) ⟶ 0`
for `i₃` and `i₄`. The object `opZ^n(i ≤ j, j ≤ k)` is the image of `H^n(i ≤ j) ⟶ H^n(i ≤ k)`, so
raising `k` from `i₃` to `i₄` is an isomorphism on it under the hypothesis
(`CategoryTheory.Abelian.SpectralObject.isIso_opcyclesMap_of_mono`).

## References

* [Stacks, Tag 012Q](https://stacks.math.columbia.edu/tag/012Q), Lemma 24.6, the comparison of the
  boundaries of the pages with the boundaries of the limit, in the filtered-complex form.
-/

public section

namespace CategoryTheory.Abelian.SpectralObject

open ComposableArrows Limits

variable {C ι : Type*} [Category* C] [Abelian C] [Preorder ι] (X : SpectralObject C ι)

/-- For `i ≤ j ≤ k ≤ l`, the map `opZ^n(i ≤ j, j ≤ k) ⟶ opZ^n(i ≤ j, j ≤ l)` is an isomorphism when
`H^n(i ≤ k) ⟶ H^n(i ≤ l)` is a monomorphism: both objects are the images of `H^n(i ≤ j)`, in
`H^n(i ≤ k)` and in `H^n(i ≤ l)`. -/
lemma isIso_opcyclesMap_of_mono {i j k l : ι} (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l)
    (α : mk₂ (homOfLE hij) (homOfLE hjk) ⟶ mk₂ (homOfLE hij) (homOfLE (hjk.trans hkl))) (n : ℤ)
    (h : Mono ((X.H n).map (twoδ₂Toδ₁ (homOfLE (hij.trans hjk)) (homOfLE hkl)
      (homOfLE ((hij.trans hjk).trans hkl)) (Subsingleton.elim _ _)))) :
    IsIso (X.opcyclesMap _ _ _ _ α n) := by
  have : Epi (X.opcyclesMap _ _ _ _ α n) := by
    have := X.p_opcyclesMap _ _ _ _ α (𝟙 _) n (Subsingleton.elim _ _)
    rw [Functor.map_id, Category.id_comp] at this
    exact epi_of_epi_fac this
  have : Mono (X.opcyclesMap _ _ _ _ α n) :=
    mono_of_mono_fac (X.opcyclesMap_fromOpcycles _ _ _ _ (homOfLE (hij.trans hjk))
      (Subsingleton.elim _ _) (homOfLE ((hij.trans hjk).trans hkl)) (Subsingleton.elim _ _) α
      (twoδ₂Toδ₁ _ (homOfLE hkl) _ (Subsingleton.elim _ _)) n (Subsingleton.elim _ _)
      (Subsingleton.elim _ _))
  exact isIso_of_mono_of_epi _

/-- **The last index of `E^n(i₀ ≤ i₁ ≤ i₂ ≤ i₃)` can be raised along a monomorphism.** For
`i₀ ≤ i₁ ≤ i₂ ≤ i₃ ≤ i₄`, the canonical map `E^n(i₀ ≤ i₁ ≤ i₂ ≤ i₃) ⟶ E^n(i₀ ≤ i₁ ≤ i₂ ≤ i₄)` is an
isomorphism when `H^n(i₀ ≤ i₃) ⟶ H^n(i₀ ≤ i₄)` is a monomorphism. -/
lemma isIso_mapFourδ₄Toδ₃'_of_mono (i₀ i₁ i₂ i₃ i₄ : ι) (hi₀₁ : i₀ ≤ i₁) (hi₁₂ : i₁ ≤ i₂)
    (hi₂₃ : i₂ ≤ i₃) (hi₃₄ : i₃ ≤ i₄) (n₀ n₁ n₂ : ℤ)
    (h : Mono ((X.H n₁).map (twoδ₂Toδ₁ (homOfLE (hi₀₁.trans (hi₁₂.trans hi₂₃))) (homOfLE hi₃₄)
      (homOfLE ((hi₀₁.trans (hi₁₂.trans hi₂₃)).trans hi₃₄)) (Subsingleton.elim _ _))))
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂) := by
  -- the short exact sequences `0 ⟶ opZ^n(f₁, f₂ ≫ f₃) ⟶ opZ^n(f₁ ≫ f₂, f₃) ⟶ E^n(f₁, f₂, f₃) ⟶ 0`
  -- for the last index `i₃` and `i₄`
  let S := X.shortComplexOpcyclesThreeδ₂Toδ₁ (homOfLE hi₀₁) (homOfLE hi₁₂) (homOfLE hi₂₃)
    (homOfLE (hi₀₁.trans hi₁₂)) (homOfLE (hi₁₂.trans hi₂₃)) (Subsingleton.elim _ _)
    (Subsingleton.elim _ _) n₀ n₁ n₂ hn₁ hn₂
  let S' := X.shortComplexOpcyclesThreeδ₂Toδ₁ (homOfLE hi₀₁) (homOfLE hi₁₂)
    (homOfLE (hi₂₃.trans hi₃₄)) (homOfLE (hi₀₁.trans hi₁₂))
    (homOfLE (hi₁₂.trans (hi₂₃.trans hi₃₄))) (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    n₀ n₁ n₂ hn₁ hn₂
  let α₁ : mk₂ (homOfLE hi₀₁) (homOfLE (hi₁₂.trans hi₂₃)) ⟶
      mk₂ (homOfLE hi₀₁) (homOfLE (hi₁₂.trans (hi₂₃.trans hi₃₄))) :=
    homMk₂ (𝟙 _) (𝟙 _) (homOfLE hi₃₄) (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  let α₂ : mk₂ (homOfLE (hi₀₁.trans hi₁₂)) (homOfLE hi₂₃) ⟶
      mk₂ (homOfLE (hi₀₁.trans hi₁₂)) (homOfLE (hi₂₃.trans hi₃₄)) :=
    homMk₂ (𝟙 _) (𝟙 _) (homOfLE hi₃₄) (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  let φ : S ⟶ S' :=
    { τ₁ := X.opcyclesMap _ _ _ _ α₁ n₁
      τ₂ := X.opcyclesMap _ _ _ _ α₂ n₁
      τ₃ := X.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂
      comm₁₂ := (X.opcyclesMap_comp _ _ _ _ _ _ _ _ _ n₁ rfl).trans
        (X.opcyclesMap_comp _ _ _ _ _ _ _ _ _ n₁ (Subsingleton.elim _ _)).symm
      comm₂₃ := (X.opcyclesToE_map _ _ _ _ _ _ _ _ _ _ _ _ n₀ n₁ n₂
        (Subsingleton.elim _ _) (Subsingleton.elim _ _)).symm }
  -- `φ` is an isomorphism on the first two terms, hence on the cokernels of the first maps, by
  -- the four lemma
  have : IsIso φ.τ₁ := X.isIso_opcyclesMap_of_mono hi₀₁ (hi₁₂.trans hi₂₃) hi₃₄ α₁ n₁ h
  have : IsIso φ.τ₂ := X.isIso_opcyclesMap_of_mono (hi₀₁.trans hi₁₂) hi₂₃ hi₃₄ α₂ n₁ h
  exact isIso_of_epi_of_isIso (φ := ShortComplex.mapToComposableArrows φ)
    (X.shortComplexOpcyclesThreeδ₂Toδ₁_exact ..).exact_toComposableArrows
    (X.shortComplexOpcyclesThreeδ₂Toδ₁_exact ..).exact_toComposableArrows
    (inferInstanceAs (Epi S.g)) (inferInstanceAs (Epi S'.g)) (inferInstanceAs (Epi φ.τ₁))
    (inferInstanceAs (IsIso φ.τ₂))

end CategoryTheory.Abelian.SpectralObject

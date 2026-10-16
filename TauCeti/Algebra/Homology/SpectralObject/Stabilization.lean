/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.FirstPage

/-!
# Stabilization of the pages of the spectral sequence of a spectral object indexed by `EInt`

Let `X` be a spectral object in an abelian category, indexed by `EInt`. Its spectral sequence
`X.spectralSequence coreE₂Cohomological` has on page `r` at `(p, q)` the object
`E^{p+q}(q - r + 2 ≤ q ≤ q + 1 ≤ q + r - 1)`. We introduce the limit object
`X.EInfty q n = E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)` and show that the page-`r` object at `(p, q)` is
isomorphic to `X.EInfty q (p + q)` as soon as `H^{p+q+1}(⊥ ≤ q - r + 2)` and
`H^{p+q-1}(q + r - 1 ≤ ⊤)` vanish (`spectralSequencePageXIsoEInfty`). The isomorphism is the
composite of the canonical maps `E^n(i₀ ≤ i₁ ≤ i₂ ≤ i₃) ⟶ E^n(i₀' ≤ i₁ ≤ i₂ ≤ i₃')` for
`i₀' ≤ i₀` and `i₃ ≤ i₃'`, which are isomorphisms under these vanishing conditions (Mathlib's
`isoMapFourδ₁Toδ₀'` and `isoMapFourδ₄Toδ₃'`).

## Main definitions

* `CategoryTheory.Abelian.SpectralObject.EInfty X q n`: the object `E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)`.
* `CategoryTheory.Abelian.SpectralObject.spectralSequencePageXIsoEInfty`: the isomorphism of a
  page object with `EInfty` under the vanishing conditions.
-/

public section

namespace CategoryTheory.Abelian.SpectralObject

open ComposableArrows Limits

variable {C : Type*} [Category* C] [Abelian C] (X : SpectralObject C EInt)

/-- The inequality `q ≤ q + 1` in `EInt`. -/
lemma coe_le_coe_add_one (q : ℤ) : (q : EInt) ≤ ((q + 1 : ℤ) : EInt) := by
  simp

/-- The object `E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)` of a spectral object indexed by `EInt`. Under the vanishing
conditions of `spectralSequencePageXIsoEInfty`, it is isomorphic to the object at `(n - q, q)` on
the `r`th page of the spectral sequence. -/
noncomputable abbrev EInfty (q n : ℤ) : C :=
  X.E (homOfLE (bot_le : (⊥ : EInt) ≤ q)) (homOfLE (coe_le_coe_add_one q))
    (homOfLE (le_top : ((q + 1 : ℤ) : EInt) ≤ ⊤)) (n - 1) n (n + 1)

/-- The object at `pq = (p, q)` on page `r ≥ 2` of the spectral sequence of `X` is
`X.EInfty q (p + q)` when `H^{p+q+1}(⊥ ≤ q - r + 2)` and `H^{p+q-1}(q + r - 1 ≤ ⊤)` vanish. -/
noncomputable def spectralSequencePageXIsoEInfty (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (n : ℤ)
    (hn : n = pq.1 + pq.2)
    (h₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt))))))
    (h₃ : IsZero ((X.H (n - 1)).obj
      (mk₁ (homOfLE (le_top : ((pq.2 + r - 1 : ℤ) : EInt) ≤ ⊤))))) :
    ((X.spectralSequence coreE₂Cohomological).page r).X pq ≅ X.EInfty pq.2 n :=
  have h₀₁ : ((pq.2 - r + 2 : ℤ) : EInt) ≤ pq.2 := by simp; lia
  have h₂₃ : ((pq.2 + 1 : ℤ) : EInt) ≤ ((pq.2 + r - 1 : ℤ) : EInt) := by simp; lia
  X.spectralSequencePageXIso coreE₂Cohomological r hr pq ((pq.2 - r + 2 : ℤ) : EInt) pq.2
      ((pq.2 + 1 : ℤ) : EInt) ((pq.2 + r - 1 : ℤ) : EInt) rfl rfl rfl rfl (n - 1) n (n + 1) hn ≪≫
    (X.isoMapFourδ₁Toδ₀' ⊥ _ _ _ _ bot_le h₀₁ (coe_le_coe_add_one pq.2) h₂₃ (n - 1) n (n + 1)
      h₀).symm ≪≫
    X.isoMapFourδ₄Toδ₃' ⊥ _ _ _ ⊤ bot_le (coe_le_coe_add_one pq.2) h₂₃ le_top (n - 1) n (n + 1)
      h₃

/-- The isomorphism `spectralSequencePageXIsoEInfty` is characterized by the canonical maps from
`E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1)` to the page object and to `X.EInfty q n`. -/
@[reassoc]
lemma mapFourδ₁Toδ₀'_comp_spectralSequencePageXIsoEInfty_hom (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    (n : ℤ) (hn : n = pq.1 + pq.2)
    (h₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt))))))
    (h₃ : IsZero ((X.H (n - 1)).obj
      (mk₁ (homOfLE (le_top : ((pq.2 + r - 1 : ℤ) : EInt) ≤ ⊤)))))
    (h₀₁ : ((pq.2 - r + 2 : ℤ) : EInt) ≤ pq.2)
    (h₂₃ : ((pq.2 + 1 : ℤ) : EInt) ≤ ((pq.2 + r - 1 : ℤ) : EInt)) :
    X.mapFourδ₁Toδ₀' ⊥ _ _ _ _ bot_le h₀₁ (coe_le_coe_add_one pq.2) h₂₃ (n - 1) n (n + 1)
        (sub_add_cancel n 1) rfl ≫
      (X.spectralSequencePageXIso coreE₂Cohomological r hr pq ((pq.2 - r + 2 : ℤ) : EInt) pq.2
        ((pq.2 + 1 : ℤ) : EInt) ((pq.2 + r - 1 : ℤ) : EInt) rfl rfl rfl rfl (n - 1) n (n + 1) hn
        (sub_add_cancel n 1) rfl).inv ≫
      (X.spectralSequencePageXIsoEInfty r hr pq n hn h₀ h₃).hom =
    X.mapFourδ₄Toδ₃' ⊥ _ _ _ ⊤ bot_le (coe_le_coe_add_one pq.2) h₂₃ le_top (n - 1) n (n + 1)
      (sub_add_cancel n 1) rfl := by
  rw [spectralSequencePageXIsoEInfty]
  simp

end CategoryTheory.Abelian.SpectralObject

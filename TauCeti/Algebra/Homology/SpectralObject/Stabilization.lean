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

When only `H^{p+q+1}(⊥ ≤ q - r + 2)` vanishes, as for a filtration bounded below with no upper
bound, the page-`r` object is `E^{p+q}(⊥ ≤ q ≤ q + 1 ≤ q + r - 1)`
(`spectralSequencePageXIsoEBot`). It maps onto `X.EInfty q (p + q)`
(`spectralSequencePageXToEInfty`) and to the objects on the later pages
(`spectralSequencePageXToPageX`), compatibly, through the canonical maps
`E^n(i₀ ≤ i₁ ≤ i₂ ≤ i₃) ⟶ E^n(i₀ ≤ i₁ ≤ i₂ ≤ i₃')` for `i₃ ≤ i₃'`. These maps exhibit `X.EInfty`
as a quotient of every page; for filtered complexes of modules whose filtration is moreover
exhaustive in degree `p + q - 1`,
`TauCeti.Algebra.Homology.SpectralSequence.Filtered.BoundedBelow` shows that it is their direct
limit along these maps. The maps `spectralSequencePageXToPageX` are not yet identified with the
spectral sequence's own maps from page `r` to page `r + 1`.

## Main definitions

* `CategoryTheory.Abelian.SpectralObject.EInfty X q n`: the object `E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)`.
* `CategoryTheory.Abelian.SpectralObject.spectralSequencePageXIsoEInfty`: the isomorphism of a
  page object with `EInfty` under the vanishing conditions.
* `CategoryTheory.Abelian.SpectralObject.spectralSequencePageXIsoEBot`: the page object as
  `E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1)` under the vanishing condition at the bottom.
* `CategoryTheory.Abelian.SpectralObject.spectralSequencePageXToEInfty`,
  `CategoryTheory.Abelian.SpectralObject.spectralSequencePageXToPageX`: the epimorphism onto
  `EInfty` and the maps to the later pages under that condition.
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

/-- The object at `pq = (p, q)` on page `r ≥ 2` is `E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1)`, `n = p + q`,
when `H^{n+1}(⊥ ≤ q - r + 2)` vanishes; no condition is put at the top of the filtration. -/
noncomputable def spectralSequencePageXIsoEBot (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (n : ℤ)
    (hn : n = pq.1 + pq.2)
    (h₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt)))))) :
    ((X.spectralSequence coreE₂Cohomological).page r).X pq ≅
      X.E (homOfLE (bot_le : (⊥ : EInt) ≤ pq.2)) (homOfLE (coe_le_coe_add_one pq.2))
        (homOfLE (show ((pq.2 + 1 : ℤ) : EInt) ≤ ((pq.2 + r - 1 : ℤ) : EInt) by simp; lia))
        (n - 1) n (n + 1) :=
  have h₀₁ : ((pq.2 - r + 2 : ℤ) : EInt) ≤ pq.2 := by simp; lia
  have h₂₃ : ((pq.2 + 1 : ℤ) : EInt) ≤ ((pq.2 + r - 1 : ℤ) : EInt) := by simp; lia
  X.spectralSequencePageXIso coreE₂Cohomological r hr pq ((pq.2 - r + 2 : ℤ) : EInt) pq.2
      ((pq.2 + 1 : ℤ) : EInt) ((pq.2 + r - 1 : ℤ) : EInt) rfl rfl rfl rfl (n - 1) n (n + 1) hn ≪≫
    (X.isoMapFourδ₁Toδ₀' ⊥ _ _ _ _ bot_le h₀₁ (coe_le_coe_add_one pq.2) h₂₃ (n - 1) n (n + 1)
      h₀).symm

/-- The inverse of `X.spectralSequencePageXIsoEBot` is the canonical map
`E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1) ⟶ E^n(q - r + 2 ≤ q ≤ q + 1 ≤ q + r - 1)` followed by the
identification of the latter with the page object. -/
@[reassoc]
lemma spectralSequencePageXIsoEBot_inv (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (n : ℤ)
    (hn : n = pq.1 + pq.2)
    (h₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt)))))) :
    (X.spectralSequencePageXIsoEBot r hr pq n hn h₀).inv =
      X.mapFourδ₁Toδ₀' ⊥ ((pq.2 - r + 2 : ℤ) : EInt) pq.2 ((pq.2 + 1 : ℤ) : EInt)
          ((pq.2 + r - 1 : ℤ) : EInt) bot_le (by simp; lia) (coe_le_coe_add_one pq.2)
          (by simp; lia) (n - 1) n (n + 1) ≫
        (X.spectralSequencePageXIso coreE₂Cohomological r hr pq ((pq.2 - r + 2 : ℤ) : EInt) pq.2
          ((pq.2 + 1 : ℤ) : EInt) ((pq.2 + r - 1 : ℤ) : EInt) rfl rfl rfl rfl (n - 1) n (n + 1)
          hn).inv :=
  (rfl)

/-- The object at `pq = (p, q)` on page `r ≥ 2` of the spectral sequence of `X` is
`X.EInfty q (p + q)` when `H^{p+q+1}(⊥ ≤ q - r + 2)` and `H^{p+q-1}(q + r - 1 ≤ ⊤)` vanish. -/
noncomputable def spectralSequencePageXIsoEInfty (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (n : ℤ)
    (hn : n = pq.1 + pq.2)
    (h₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt))))))
    (h₃ : IsZero ((X.H (n - 1)).obj
      (mk₁ (homOfLE (le_top : ((pq.2 + r - 1 : ℤ) : EInt) ≤ ⊤))))) :
    ((X.spectralSequence coreE₂Cohomological).page r).X pq ≅ X.EInfty pq.2 n :=
  X.spectralSequencePageXIsoEBot r hr pq n hn h₀ ≪≫
    X.isoMapFourδ₄Toδ₃' ⊥ _ _ _ ⊤ bot_le (coe_le_coe_add_one pq.2) (by simp; lia) le_top
      (n - 1) n (n + 1) h₃

/-- The isomorphism `spectralSequencePageXIsoEInfty` is characterized by the canonical maps from
`E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1)` to the page object and to `X.EInfty q n`. -/
@[reassoc]
lemma mapFourδ₁Toδ₀'_comp_spectralSequencePageXIsoEInfty_hom (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    (n : ℤ) (hn : n = pq.1 + pq.2)
    (h₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt))))))
    (h₃ : IsZero ((X.H (n - 1)).obj
      (mk₁ (homOfLE (le_top : ((pq.2 + r - 1 : ℤ) : EInt) ≤ ⊤))))) :
    X.mapFourδ₁Toδ₀' ⊥ ((pq.2 - r + 2 : ℤ) : EInt) pq.2 ((pq.2 + 1 : ℤ) : EInt)
        ((pq.2 + r - 1 : ℤ) : EInt) bot_le (by simp; lia) (coe_le_coe_add_one pq.2)
        (by simp; lia) (n - 1) n (n + 1) ≫
      (X.spectralSequencePageXIso coreE₂Cohomological r hr pq ((pq.2 - r + 2 : ℤ) : EInt) pq.2
        ((pq.2 + 1 : ℤ) : EInt) ((pq.2 + r - 1 : ℤ) : EInt) rfl rfl rfl rfl (n - 1) n (n + 1)
        hn).inv ≫
      (X.spectralSequencePageXIsoEInfty r hr pq n hn h₀ h₃).hom =
    X.mapFourδ₄Toδ₃' ⊥ _ _ _ ⊤ bot_le (coe_le_coe_add_one pq.2) (by simp; lia) le_top
      (n - 1) n (n + 1) := by
  rw [← spectralSequencePageXIsoEBot_inv_assoc _ _ _ _ _ _ h₀]
  simp [spectralSequencePageXIsoEInfty]

section DirectLimit

/-- When `H^{n+1}(⊥ ≤ q - r + 2)` vanishes, the epimorphism from the object at `pq = (p, q)` on page
`r ≥ 2` onto `X.EInfty q n`, `n = p + q`: the canonical map
`E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1) ⟶ E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)` through
`X.spectralSequencePageXIsoEBot`. It is an isomorphism when moreover `H^{n-1}(q + r - 1 ≤ ⊤)`
vanishes (`X.spectralSequencePageXIsoEInfty_hom`). -/
noncomputable def spectralSequencePageXToEInfty (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (n : ℤ)
    (hn : n = pq.1 + pq.2)
    (h₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt)))))) :
    ((X.spectralSequence coreE₂Cohomological).page r).X pq ⟶ X.EInfty pq.2 n :=
  (X.spectralSequencePageXIsoEBot r hr pq n hn h₀).hom ≫
    X.mapFourδ₄Toδ₃' ⊥ _ _ _ ⊤ bot_le (coe_le_coe_add_one pq.2) (by simp; lia) le_top
      (n - 1) n (n + 1)

/-- `X.spectralSequencePageXToEInfty` is `X.spectralSequencePageXIsoEBot` followed by the canonical
map `E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1) ⟶ E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)`. -/
lemma spectralSequencePageXToEInfty_def (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (n : ℤ)
    (hn : n = pq.1 + pq.2)
    (h₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt)))))) :
    X.spectralSequencePageXToEInfty r hr pq n hn h₀ =
      (X.spectralSequencePageXIsoEBot r hr pq n hn h₀).hom ≫
        X.mapFourδ₄Toδ₃' ⊥ _ _ _ ⊤ bot_le (coe_le_coe_add_one pq.2) (by simp; lia) le_top
          (n - 1) n (n + 1) :=
  (rfl)

instance (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (n : ℤ) (hn : n = pq.1 + pq.2)
    (h₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt)))))) :
    Epi (X.spectralSequencePageXToEInfty r hr pq n hn h₀) := by
  have := X.epi_map (homOfLE (bot_le : (⊥ : EInt) ≤ pq.2)) (homOfLE (coe_le_coe_add_one pq.2))
    (homOfLE (show ((pq.2 + 1 : ℤ) : EInt) ≤ ((pq.2 + r - 1 : ℤ) : EInt) by simp; lia))
    (homOfLE (le_top : ((pq.2 + 1 : ℤ) : EInt) ≤ ⊤))
    (fourδ₄Toδ₃' ⊥ _ _ _ ⊤ bot_le (coe_le_coe_add_one pq.2) (by simp; lia) le_top) (n - 1) n
    (n + 1)
  rw [spectralSequencePageXToEInfty]
  infer_instance

/-- Under both vanishing conditions, the isomorphism `X.spectralSequencePageXIsoEInfty` is the
epimorphism `X.spectralSequencePageXToEInfty`. -/
lemma spectralSequencePageXIsoEInfty_hom (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (n : ℤ)
    (hn : n = pq.1 + pq.2)
    (h₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt))))))
    (h₃ : IsZero ((X.H (n - 1)).obj
      (mk₁ (homOfLE (le_top : ((pq.2 + r - 1 : ℤ) : EInt) ≤ ⊤))))) :
    (X.spectralSequencePageXIsoEInfty r hr pq n hn h₀ h₃).hom =
      X.spectralSequencePageXToEInfty r hr pq n hn h₀ :=
  (rfl)

/-- When `H^{n+1}(⊥ ≤ q - r + 2)` and `H^{n+1}(⊥ ≤ q - r' + 2)` vanish, the canonical map from the
object at `pq = (p, q)` on page `r` to the object at `pq` on a later page `r' ≥ r`: the map
`E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1) ⟶ E^n(⊥ ≤ q ≤ q + 1 ≤ q + r' - 1)` through
`X.spectralSequencePageXIsoEBot`. These maps are compatible with the maps to `X.EInfty q n`
(`X.spectralSequencePageXToPageX_spectralSequencePageXToEInfty`). -/
noncomputable def spectralSequencePageXToPageX (r r' : ℤ) (hr : 2 ≤ r) (hrr' : r ≤ r') (pq : ℤ × ℤ)
    (n : ℤ) (hn : n = pq.1 + pq.2)
    (h₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt))))))
    (h₀' : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r' + 2 : ℤ) : EInt)))))) :
    ((X.spectralSequence coreE₂Cohomological).page r).X pq ⟶
      ((X.spectralSequence coreE₂Cohomological).page r').X pq :=
  (X.spectralSequencePageXIsoEBot r hr pq n hn h₀).hom ≫
    X.mapFourδ₄Toδ₃' ⊥ _ _ ((pq.2 + r - 1 : ℤ) : EInt) ((pq.2 + r' - 1 : ℤ) : EInt) bot_le
      (coe_le_coe_add_one pq.2) (by simp; lia) (by simp; lia) (n - 1) n (n + 1) ≫
    (X.spectralSequencePageXIsoEBot r' (hr.trans hrr') pq n hn h₀').inv

/-- `X.spectralSequencePageXToPageX` is the canonical map
`E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1) ⟶ E^n(⊥ ≤ q ≤ q + 1 ≤ q + r' - 1)` through
`X.spectralSequencePageXIsoEBot`. -/
lemma spectralSequencePageXToPageX_def (r r' : ℤ) (hr : 2 ≤ r) (hrr' : r ≤ r') (pq : ℤ × ℤ)
    (n : ℤ) (hn : n = pq.1 + pq.2)
    (h₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt))))))
    (h₀' : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r' + 2 : ℤ) : EInt)))))) :
    X.spectralSequencePageXToPageX r r' hr hrr' pq n hn h₀ h₀' =
      (X.spectralSequencePageXIsoEBot r hr pq n hn h₀).hom ≫
        X.mapFourδ₄Toδ₃' ⊥ _ _ ((pq.2 + r - 1 : ℤ) : EInt) ((pq.2 + r' - 1 : ℤ) : EInt) bot_le
          (coe_le_coe_add_one pq.2) (by simp; lia) (by simp; lia) (n - 1) n (n + 1) ≫
        (X.spectralSequencePageXIsoEBot r' (hr.trans hrr') pq n hn h₀').inv :=
  (rfl)

/-- The map from a page to itself is the identity. -/
@[simp]
lemma spectralSequencePageXToPageX_self (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (n : ℤ)
    (hn : n = pq.1 + pq.2)
    (h₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt)))))) :
    X.spectralSequencePageXToPageX r r hr le_rfl pq n hn h₀ h₀ = 𝟙 _ := by
  rw [spectralSequencePageXToPageX_def, mapFourδ₄Toδ₃',
    Subsingleton.elim (fourδ₄Toδ₃' _ _ _ _ _ _ _ _ _) (𝟙 _), X.map_id _ _ _ (n - 1) n (n + 1),
    Category.id_comp, Iso.hom_inv_id]

/-- The maps from a page to later pages are compatible with the maps to `X.EInfty`. -/
@[reassoc]
lemma spectralSequencePageXToPageX_spectralSequencePageXToEInfty (r r' : ℤ) (hr : 2 ≤ r)
    (hrr' : r ≤ r') (pq : ℤ × ℤ) (n : ℤ) (hn : n = pq.1 + pq.2)
    (h₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt))))))
    (h₀' : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r' + 2 : ℤ) : EInt)))))) :
    X.spectralSequencePageXToPageX r r' hr hrr' pq n hn h₀ h₀' ≫
        X.spectralSequencePageXToEInfty r' (hr.trans hrr') pq n hn h₀' =
      X.spectralSequencePageXToEInfty r hr pq n hn h₀ := by
  simp only [spectralSequencePageXToPageX, spectralSequencePageXToEInfty, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [X.mapFourδ₄Toδ₃'_comp (n₀ := n - 1) (n₁ := n) (n₂ := n + 1)]

/-- The maps from a page to later pages compose. -/
@[reassoc (attr := simp)]
lemma spectralSequencePageXToPageX_comp (r r' r'' : ℤ) (hr : 2 ≤ r)
    (hrr' : r ≤ r') (hr'r'' : r' ≤ r'') (pq : ℤ × ℤ) (n : ℤ) (hn : n = pq.1 + pq.2)
    (h₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt))))))
    (h₀' : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r' + 2 : ℤ) : EInt))))))
    (h₀'' : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r'' + 2 : ℤ) : EInt)))))) :
    X.spectralSequencePageXToPageX r r' hr hrr' pq n hn h₀ h₀' ≫
        X.spectralSequencePageXToPageX r' r'' (hr.trans hrr') hr'r'' pq n hn h₀' h₀'' =
      X.spectralSequencePageXToPageX r r'' hr (hrr'.trans hr'r'') pq n hn h₀ h₀'' := by
  simp only [spectralSequencePageXToPageX, Category.assoc, Iso.inv_hom_id_assoc]
  rw [X.mapFourδ₄Toδ₃'_comp_assoc (n₀ := n - 1) (n₁ := n) (n₂ := n + 1)]

end DirectLimit

end CategoryTheory.Abelian.SpectralObject

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralObject.Abutment
public import TauCeti.Algebra.Homology.SpectralObject.SpectralSequenceMap

/-!
# Naturality of the abutment and of the limit objects of spectral objects indexed by `EInt`

Let `φ : X ⟶ Y` be a morphism of spectral objects indexed by `EInt`. On the abutments
`H^n(⊥ ≤ ⊤)` it is the component `(φ.hom n).app` at `⊥ ≤ ⊤`, and on the pieces
`F_q H^n = opZ^n(⊥ ≤ q, q ≤ ⊤)` of their filtrations it is `opcyclesMapOfHom φ`. These maps are
compatible with the embeddings of the pieces and with the inclusions `F_q H^n ⟶ F_{q+1} H^n`
(`abutmentFiltrationι_naturality`, `abutmentFiltrationMap_naturality`), so `φ` induces maps
`abutmentGradedMap φ q n` on the graded pieces `F_{q+1} H^n / F_q H^n`.

The convergence data of the spectral sequence are natural in `φ`, with the morphism of spectral
sequences `spectralSequencePageXMap coreE₂Cohomological φ` on the pages and `EMap φ` on the limit
objects `E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)`:

* the identification of `E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)` with the graded piece
  (`EInftyIsoCokernel_hom_naturality`);
* the identification of a page object with `E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1)` when the filtration
  is bounded below (`spectralSequencePageXIsoEBot_hom_naturality`);
* the epimorphisms from the pages onto `E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)` and the maps to the later pages
  (`spectralSequencePageXToEInfty_naturality`, `spectralSequencePageXToPageX_naturality`).

## Main definitions

* `CategoryTheory.Abelian.SpectralObject.abutmentGradedMap φ q n`: the map
  `F_{q+1} H^n / F_q H^n ⟶ F_{q+1} H^n / F_q H^n` on the graded pieces of the abutments.

## Main results

* `CategoryTheory.Abelian.SpectralObject.EInftyIsoCokernel_hom_naturality`: `E∞` is naturally
  the graded piece of the abutment.
* `CategoryTheory.Abelian.SpectralObject.spectralSequencePageXToEInfty_naturality`: the maps from
  the pages onto `E∞` are natural.
* `spectralSequencePageXToEInfty_comp_EInftyIsoCokernel_hom_naturality`: the maps from the pages
  onto the graded pieces are natural.
* `CategoryTheory.Abelian.SpectralObject.spectralSequencePageXToPageX_naturality`: the maps to
  the later pages are natural.
-/

public section

namespace CategoryTheory.Abelian.SpectralObject

open ComposableArrows Limits

variable {C : Type*} [Category* C] [Abelian C] {X Y Z : SpectralObject C EInt} (φ : X ⟶ Y)
  (ψ : Y ⟶ Z)

section Abutment

/-- The embeddings `F_q H^n ⟶ H^n(⊥ ≤ ⊤)` of the pieces of the filtrations of the abutments are
natural. -/
@[reassoc]
lemma abutmentFiltrationι_naturality (q n : ℤ) :
    opcyclesMapOfHom φ (homOfLE (bot_le : (⊥ : EInt) ≤ q)) (homOfLE (le_top : (q : EInt) ≤ ⊤))
        n ≫ Y.abutmentFiltrationι q n =
      X.abutmentFiltrationι q n ≫ (φ.hom n).app (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) := by
  rw [abutmentFiltrationι_eq, abutmentFiltrationι_eq, opcyclesMapOfHom_fromOpcycles]

/-- The inclusions `F_q H^n ⟶ F_{q+1} H^n` of the pieces of the filtrations of the abutments are
natural. -/
@[reassoc]
lemma abutmentFiltrationMap_naturality (q n : ℤ) :
    X.abutmentFiltrationMap q n ≫
        opcyclesMapOfHom φ (homOfLE (bot_le : (⊥ : EInt) ≤ ((q + 1 : ℤ) : EInt)))
          (homOfLE (le_top : ((q + 1 : ℤ) : EInt) ≤ ⊤)) n =
      opcyclesMapOfHom φ (homOfLE (bot_le : (⊥ : EInt) ≤ q)) (homOfLE (le_top : (q : EInt) ≤ ⊤))
          n ≫ Y.abutmentFiltrationMap q n := by
  rw [← cancel_mono (Y.abutmentFiltrationι (q + 1) n), Category.assoc, Category.assoc,
    abutmentFiltrationι_naturality, abutmentFiltrationMap_ι_assoc, abutmentFiltrationMap_ι,
    abutmentFiltrationι_naturality]

/-- The map `F_{q+1} H^n / F_q H^n ⟶ F_{q+1} H^n / F_q H^n` on the graded pieces of the
filtrations of the abutments induced by a morphism of spectral objects. -/
noncomputable def abutmentGradedMap (q n : ℤ) :
    cokernel (X.abutmentFiltrationMap q n) ⟶ cokernel (Y.abutmentFiltrationMap q n) :=
  cokernel.map _ _ _ _ (abutmentFiltrationMap_naturality φ q n).symm

/-- The map on the graded pieces is induced by the map on the pieces `F_{q+1} H^n`. -/
@[reassoc (attr := simp)]
lemma π_abutmentGradedMap (q n : ℤ) :
    cokernel.π (X.abutmentFiltrationMap q n) ≫ abutmentGradedMap φ q n =
      opcyclesMapOfHom φ (homOfLE (bot_le : (⊥ : EInt) ≤ ((q + 1 : ℤ) : EInt)))
          (homOfLE (le_top : ((q + 1 : ℤ) : EInt) ≤ ⊤)) n ≫
        cokernel.π (Y.abutmentFiltrationMap q n) :=
  cokernel.π_desc _ _ _

/-- The identity induces the identity on the graded pieces. -/
@[simp]
lemma abutmentGradedMap_id (q n : ℤ) : abutmentGradedMap (𝟙 X) q n = 𝟙 _ :=
  coequalizer.hom_ext (by simp)

/-- The map on the graded pieces induced by a composite is the composite of the induced maps. -/
@[reassoc, simp]
lemma abutmentGradedMap_comp (q n : ℤ) :
    abutmentGradedMap (φ ≫ ψ) q n = abutmentGradedMap φ q n ≫ abutmentGradedMap ψ q n :=
  coequalizer.hom_ext (by simp)

/-- **`E∞` is naturally the graded piece of the abutment.** Through `EInftyIsoCokernel`, the map
induced by `φ` on `E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)` is the map on the graded pieces
`F_{q+1} H^n / F_q H^n`. -/
@[reassoc]
lemma EInftyIsoCokernel_hom_naturality (q n : ℤ) :
    EMap φ (homOfLE (bot_le : (⊥ : EInt) ≤ q)) (homOfLE (coe_le_coe_add_one q))
        (homOfLE (le_top : ((q + 1 : ℤ) : EInt) ≤ ⊤)) (n - 1) n (n + 1) (sub_add_cancel n 1)
        rfl ≫ (Y.EInftyIsoCokernel q n).hom =
      (X.EInftyIsoCokernel q n).hom ≫ abutmentGradedMap φ q n := by
  rw [← cancel_epi (X.opcyclesToE (homOfLE (bot_le : (⊥ : EInt) ≤ q))
      (homOfLE (coe_le_coe_add_one q)) (homOfLE (le_top : ((q + 1 : ℤ) : EInt) ≤ ⊤))
      (homOfLE bot_le) (Subsingleton.elim _ _) (n - 1) n (n + 1) (sub_add_cancel n 1) rfl),
    ← opcyclesMapOfHom_opcyclesToE_assoc, opcyclesToE_EInftyIsoCokernel_hom,
    opcyclesToE_EInftyIsoCokernel_hom_assoc, π_abutmentGradedMap]

end Abutment

section Pages

variable (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (n : ℤ) (hn : n = pq.1 + pq.2)

/-- The identification `spectralSequencePageXIsoEBot` of the object at `pq = (p, q)` on page `r`
with `E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1)` is natural. -/
@[reassoc]
lemma spectralSequencePageXIsoEBot_hom_naturality
    (hX₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt))))))
    (hY₀ : IsZero ((Y.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt)))))) :
    spectralSequencePageXMap coreE₂Cohomological φ r hr pq ≫
        (Y.spectralSequencePageXIsoEBot r hr pq n hn hY₀).hom =
      (X.spectralSequencePageXIsoEBot r hr pq n hn hX₀).hom ≫
        EMap φ (homOfLE (bot_le : (⊥ : EInt) ≤ pq.2)) (homOfLE (coe_le_coe_add_one pq.2))
          (homOfLE (show ((pq.2 + 1 : ℤ) : EInt) ≤ ((pq.2 + r - 1 : ℤ) : EInt) by simp; lia))
          (n - 1) n (n + 1) (sub_add_cancel n 1) rfl := by
  -- the indices of the recipe `coreE₂Cohomological`, as hypotheses with their syntactic types
  have e₀ : ((pq.2 - r + 2 : ℤ) : EInt) = coreE₂Cohomological.i₀ r pq hr := rfl
  have e₁ : ((pq.2 : ℤ) : EInt) = coreE₂Cohomological.i₁ pq := rfl
  have e₂ : ((pq.2 + 1 : ℤ) : EInt) = coreE₂Cohomological.i₂ pq := rfl
  have e₃ : ((pq.2 + r - 1 : ℤ) : EInt) = coreE₂Cohomological.i₃ r pq hr := rfl
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv, spectralSequencePageXIsoEBot_inv,
    spectralSequencePageXIsoEBot_inv, Category.assoc,
    spectralSequencePageXMap_eq coreE₂Cohomological φ r hr pq _ _ _ _ e₀ e₁ e₂ e₃ (n - 1) n
      (n + 1) hn (sub_add_cancel n 1) rfl, Iso.inv_hom_id_assoc, map_EMap_assoc]

/-- **The maps from the pages onto `E∞` are natural.** When `H^{n+1}(⊥ ≤ q - r + 2)` vanishes for
`X` and `Y`, the epimorphisms `spectralSequencePageXToEInfty` from the objects at `pq = (p, q)` on
page `r` onto `E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)` commute with the maps induced by `φ`. -/
@[reassoc]
lemma spectralSequencePageXToEInfty_naturality
    (hX₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt))))))
    (hY₀ : IsZero ((Y.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt)))))) :
    spectralSequencePageXMap coreE₂Cohomological φ r hr pq ≫
        Y.spectralSequencePageXToEInfty r hr pq n hn hY₀ =
      X.spectralSequencePageXToEInfty r hr pq n hn hX₀ ≫
        EMap φ (homOfLE (bot_le : (⊥ : EInt) ≤ pq.2)) (homOfLE (coe_le_coe_add_one pq.2))
          (homOfLE (le_top : ((pq.2 + 1 : ℤ) : EInt) ≤ ⊤)) (n - 1) n (n + 1)
          (sub_add_cancel n 1) rfl := by
  rw [spectralSequencePageXToEInfty_def, spectralSequencePageXToEInfty_def,
    spectralSequencePageXIsoEBot_hom_naturality_assoc φ r hr pq n hn hX₀ hY₀, Category.assoc,
    map_EMap]

/-- **The maps from the pages onto the graded pieces are natural.** When `H^{n+1}(⊥ ≤ q - r + 2)`
vanishes for `X` and `Y`, the epimorphisms `spectralSequencePageXToEInfty` followed by
`EInftyIsoCokernel`, from the objects at `pq = (p, q)` on page `r` onto the graded pieces
`F_{q+1} H^n / F_q H^n`, intertwine `spectralSequencePageXMap coreE₂Cohomological φ` with
`abutmentGradedMap φ`. -/
@[reassoc]
lemma spectralSequencePageXToEInfty_comp_EInftyIsoCokernel_hom_naturality
    (hX₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt))))))
    (hY₀ : IsZero ((Y.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt)))))) :
    spectralSequencePageXMap coreE₂Cohomological φ r hr pq ≫
        Y.spectralSequencePageXToEInfty r hr pq n hn hY₀ ≫ (Y.EInftyIsoCokernel pq.2 n).hom =
      X.spectralSequencePageXToEInfty r hr pq n hn hX₀ ≫ (X.EInftyIsoCokernel pq.2 n).hom ≫
        abutmentGradedMap φ pq.2 n := by
  rw [spectralSequencePageXToEInfty_naturality_assoc φ r hr pq n hn hX₀ hY₀,
    EInftyIsoCokernel_hom_naturality]

/-- **The maps to the later pages are natural.** When `H^{n+1}(⊥ ≤ q - r + 2)` and
`H^{n+1}(⊥ ≤ q - r' + 2)` vanish for `X` and `Y`, the maps `spectralSequencePageXToPageX` from
the objects at `pq = (p, q)` on page `r` to those on page `r' ≥ r` commute with the maps induced
by `φ`. -/
@[reassoc]
lemma spectralSequencePageXToPageX_naturality (r' : ℤ) (hrr' : r ≤ r')
    (hX₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt))))))
    (hX₀' : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r' + 2 : ℤ) : EInt))))))
    (hY₀ : IsZero ((Y.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt))))))
    (hY₀' : IsZero ((Y.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r' + 2 : ℤ) : EInt)))))) :
    spectralSequencePageXMap coreE₂Cohomological φ r hr pq ≫
        Y.spectralSequencePageXToPageX r r' hr hrr' pq n hn hY₀ hY₀' =
      X.spectralSequencePageXToPageX r r' hr hrr' pq n hn hX₀ hX₀' ≫
        spectralSequencePageXMap coreE₂Cohomological φ r' (hr.trans hrr') pq := by
  have h := spectralSequencePageXIsoEBot_hom_naturality φ r' (hr.trans hrr') pq n hn hX₀' hY₀'
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv] at h
  rw [spectralSequencePageXToPageX_def, spectralSequencePageXToPageX_def,
    spectralSequencePageXIsoEBot_hom_naturality_assoc φ r hr pq n hn hX₀ hY₀]
  simp only [Category.assoc]
  rw [h, map_EMap_assoc]

end Pages

end CategoryTheory.Abelian.SpectralObject

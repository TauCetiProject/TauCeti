/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralObject.Abutment
public import TauCeti.Algebra.Homology.SpectralObject.PageHomology
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# The edge map of the spectral sequence of a spectral object indexed by `EInt`

Let `X` be a spectral object in an abelian category, indexed by `EInt`, with its `E₂` cohomological
spectral sequence, whose first page (numbered `2`) has at `(p, q)` the object `H^n(q ≤ q + 1)`,
`n = p + q` (Mathlib's `spectralSequenceFirstPageXIso`). When `H^{n+1}(⊥ ≤ q)` vanishes, the
first page at `(p, q)` maps onto the limit object `X.EInfty q n = E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)`
(`CategoryTheory.Abelian.SpectralObject.spectralSequencePageXToEInfty`), which is the graded piece
`F_{q+1} H^n / F_q H^n` of the abutment (`EInftyIsoCokernel`).

This file computes this map on the classes coming from `H^n(⊥ ≤ q + 1)`: the map
`H^n(⊥ ≤ q + 1) ⟶ H^n(q ≤ q + 1)` followed by the map from the first page to `X.EInfty q n` is the
projection of `H^n(⊥ ≤ q + 1)` onto the piece `F_{q+1} H^n = opZ^n(⊥ ≤ q + 1, q + 1 ≤ ⊤)`
followed by the canonical map `opcyclesToE` onto `E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)`
(`H_map_comp_spectralSequencePageXToEInfty`); through `EInftyIsoCokernel`, it is the
projection onto the graded piece (`H_map_comp_spectralSequencePageXToEInfty_EInftyIsoCokernel_hom`).

When the piece `F_q H^n` vanishes, as for the lowest nonzero piece of a filtration bounded below,
`X.EInfty q n` is the piece `F_{q+1} H^n`, embedded in the abutment by the **edge map**
`X.EInftyToAbutment q n h`, and the map from the first page followed by the edge map is the map
`H^n(⊥ ≤ q + 1) ⟶ H^n(⊥ ≤ ⊤)` (`H_map_comp_spectralSequencePageXToEInfty_EInftyToAbutment`).

The stabilization criteria for degeneration, under which the map from the page `r` onto
`X.EInfty q n` is an isomorphism, are in `TauCeti.Algebra.Homology.SpectralObject.PageHomology`
(`isIso_spectralSequencePageXToEInfty_of_d_eq_zero`,
`isIso_spectralSequencePageXToEInfty_of_isZero`). The comparison of the pieces `F_a H^n` and
`F_b H^n` of the filtration when the limit objects vanish between the indices `a` and `b` is in
`TauCeti.Algebra.Homology.SpectralObject.Abutment`
(`isIso_abutmentFiltrationMapOfLE_of_isZero_EInfty`). If `F_q H^n = 0` and
`F_{q+2} H^n` is the whole abutment, the abutment is an extension of `X.EInfty (q + 1) n` by
`X.EInfty q n` (`EInftyToAbutment_shortExact`).

The classes coming from `H^n(⊥ ≤ q + 1)` factor through the canonical map
`H^n(⊥ ≤ q + 1) ⟶ E^n(⊥ ≤ q ≤ q + 1 ≤ q + 1)` (`H_map_comp_spectralSequenceFirstPageXIso_inv`),
so they are always cycles of the first page (`H_map_comp_spectralSequenceFirstPageXIso_inv_d`).
When only `H^{n+1}(⊥ ≤ q - 1)` vanishes, the first page need not map to `X.EInfty q n`, but the
second page does, and the classes on the second page of these cycles, sent to `X.EInfty q n` and
into the abutment, are the map `H^n(⊥ ≤ q + 1) ⟶ H^n(⊥ ≤ ⊤)`
(`liftCycles_H_map_homologyπ_iso_hom_EInftyToAbutment`).

## Main definitions and results

* `CategoryTheory.Abelian.SpectralObject.H_map_comp_spectralSequenceFirstPageXIso_inv` and
  `CategoryTheory.Abelian.SpectralObject.H_map_comp_spectralSequenceFirstPageXIso_inv_d`: the
  classes coming from `H^n(⊥ ≤ q + 1)` on the first page, which are cycles.
* `CategoryTheory.Abelian.SpectralObject.H_map_comp_spectralSequencePageXToEInfty`: the map from
  the first page onto `X.EInfty q n` on classes coming from `H^n(⊥ ≤ q + 1)`.
* `H_map_comp_spectralSequencePageXToEInfty_EInftyIsoCokernel_hom`: the same map, followed by the
  identification of `X.EInfty q n` with the graded piece.
* `CategoryTheory.Abelian.SpectralObject.EInftyToAbutment`: the edge map into the abutment, with
  image `F_{q+1} H^n` (`EInftyToAbutment_eq`), computed on the first page by
  `H_map_comp_spectralSequencePageXToEInfty_EInftyToAbutment`, and on the second page by
  `liftCycles_H_map_homologyπ_iso_hom_EInftyToAbutment`.
* `CategoryTheory.Abelian.SpectralObject.isIso_EInftyToAbutment`: the edge map is onto the
  abutment when `F_{q+1} H^n` is the whole abutment.
* `CategoryTheory.Abelian.SpectralObject.abutmentToEInfty`, characterized by
  `abutmentFiltrationι_abutmentToEInfty`, and
  `CategoryTheory.Abelian.SpectralObject.EInftyToAbutment_shortExact`: the short exact sequence
  of a two-step filtration.
-/

public section

namespace CategoryTheory.Abelian.SpectralObject

open ComposableArrows Limits

variable {C : Type*} [Category* C] [Abelian C] (X : SpectralObject C EInt)

/-- **The classes coming from `H^n(⊥ ≤ q + 1)` on the first page.** The map
`H^n(⊥ ≤ q + 1) ⟶ H^n(q ≤ q + 1)`, followed by the identification of `H^n(q ≤ q + 1)` with the
first page at `pq = (p, q)`, `n = p + q`, is the canonical map
`H^n(⊥ ≤ q + 1) ⟶ E^n(⊥ ≤ q ≤ q + 1 ≤ q + 1)` (the projection of the cycles), followed by the
canonical map to `E^n(q ≤ q ≤ q + 1 ≤ q + 1)`, which is the object of the first page. -/
@[reassoc]
lemma H_map_comp_spectralSequenceFirstPageXIso_inv (pq : ℤ × ℤ) (n : ℤ)
    (hn : n = pq.1 + pq.2) :
    (X.H n).map (twoδ₁Toδ₀ (homOfLE (bot_le : (⊥ : EInt) ≤ pq.2))
        (homOfLE (coe_le_coe_add_one pq.2)) (homOfLE bot_le) (Subsingleton.elim _ _)) ≫
      (X.spectralSequenceFirstPageXIso coreE₂Cohomological pq pq.2 ((pq.2 + 1 : ℤ) : EInt)
        rfl rfl n hn).inv =
    X.toCycles (homOfLE (bot_le : (⊥ : EInt) ≤ pq.2)) (homOfLE (coe_le_coe_add_one pq.2))
        (homOfLE bot_le) (Subsingleton.elim _ _) n ≫
      X.πE (homOfLE (bot_le : (⊥ : EInt) ≤ pq.2)) (homOfLE (coe_le_coe_add_one pq.2))
        (homOfLE (le_refl ((pq.2 + 1 : ℤ) : EInt))) (n - 1) n (n + 1) ≫
      X.mapFourδ₁Toδ₀' ⊥ pq.2 pq.2 ((pq.2 + 1 : ℤ) : EInt) ((pq.2 + 1 : ℤ) : EInt) bot_le le_rfl
        (coe_le_coe_add_one pq.2) le_rfl (n - 1) n (n + 1) ≫
      (X.spectralSequencePageXIso coreE₂Cohomological 2 le_rfl pq pq.2 pq.2
        ((pq.2 + 1 : ℤ) : EInt) ((pq.2 + 1 : ℤ) : EInt) (congrArg _ (by omega)) rfl rfl
        (congrArg _ (by omega)) (n - 1) n (n + 1) hn).inv := by
  rw [X.spectralSequenceFirstPageXIso_inv coreE₂Cohomological (n₀ := n - 1) (n₁ := n)
      (n₂ := n + 1)]
  -- `E^n(q ≤ q ≤ q + 1 ≤ q + 1) ≅ H^n(q ≤ q + 1)` on cycles
  have hE : (X.EIsoH (homOfLE (coe_le_coe_add_one pq.2)) (n - 1) n (n + 1)).inv =
      X.toCycles (𝟙 (pq.2 : EInt)) (homOfLE (coe_le_coe_add_one pq.2))
          (homOfLE (coe_le_coe_add_one pq.2)) (by simp) n ≫
        X.πE (𝟙 (pq.2 : EInt)) (homOfLE (coe_le_coe_add_one pq.2)) (𝟙 ((pq.2 + 1 : ℤ) : EInt))
          (n - 1) n (n + 1) := by
    rw [← cyclesIsoH_inv _ _ n (n + 1), ← cyclesIsoH_hom_EIsoH_inv _ (n - 1) n (n + 1),
      Iso.inv_hom_id_assoc]
  -- the identity of `q` in `EInt` is by definition the morphism `homOfLE le_rfl`
  have hE' : (X.EIsoH (homOfLE (coe_le_coe_add_one pq.2)) (n - 1) n (n + 1)).inv =
      X.toCycles (homOfLE (le_refl (pq.2 : EInt))) (homOfLE (coe_le_coe_add_one pq.2))
          (homOfLE (coe_le_coe_add_one pq.2)) (Subsingleton.elim _ _) n ≫
        X.πE (homOfLE (le_refl (pq.2 : EInt))) (homOfLE (coe_le_coe_add_one pq.2))
          (homOfLE (le_refl ((pq.2 + 1 : ℤ) : EInt))) (n - 1) n (n + 1) :=
    hE
  -- the classes coming from `H^n(⊥ ≤ q + 1)` lift to `E^n(⊥ ≤ q ≤ q + 1 ≤ q + 1)`
  have hA : (X.H n).map (twoδ₁Toδ₀ (homOfLE (bot_le : (⊥ : EInt) ≤ pq.2))
        (homOfLE (coe_le_coe_add_one pq.2)) (homOfLE bot_le) (Subsingleton.elim _ _)) ≫
        (X.EIsoH (homOfLE (coe_le_coe_add_one pq.2)) (n - 1) n (n + 1)).inv =
      X.toCycles (homOfLE (bot_le : (⊥ : EInt) ≤ pq.2)) (homOfLE (coe_le_coe_add_one pq.2))
          (homOfLE bot_le) (Subsingleton.elim _ _) n ≫
        X.πE (homOfLE (bot_le : (⊥ : EInt) ≤ pq.2)) (homOfLE (coe_le_coe_add_one pq.2))
          (homOfLE (le_refl ((pq.2 + 1 : ℤ) : EInt))) (n - 1) n (n + 1) ≫
        X.mapFourδ₁Toδ₀' ⊥ pq.2 pq.2 ((pq.2 + 1 : ℤ) : EInt) ((pq.2 + 1 : ℤ) : EInt) bot_le le_rfl
          (coe_le_coe_add_one pq.2) le_rfl (n - 1) n (n + 1) := by
    rw [hE', mapFourδ₁Toδ₀', X.πE_map (n₀ := n - 1) (n₁ := n) (n₂ := n + 1)
      (β := (homMk₂ (homOfLE bot_le) (𝟙 _) (𝟙 _) (Subsingleton.elim _ _) (Subsingleton.elim _ _) :
        mk₂ (homOfLE (bot_le : (⊥ : EInt) ≤ pq.2)) (homOfLE (coe_le_coe_add_one pq.2)) ⟶
          mk₂ (homOfLE (le_refl (pq.2 : EInt))) (homOfLE (coe_le_coe_add_one pq.2)))),
      X.toCycles_cyclesMap_assoc]
  rw [reassoc_of% hA]

/-- The canonical map `H^n(⊥ ≤ q + 1) ⟶ E^n(⊥ ≤ q ≤ q + 1 ≤ q + 1)`, followed by the canonical map
to `E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤) = X.EInfty q n`, is the projection of `H^n(⊥ ≤ q + 1)` onto the piece
`opZ^n(⊥ ≤ q + 1, q + 1 ≤ ⊤)` of the abutment followed by `opcyclesToE`. -/
@[reassoc]
private lemma toCycles_πE_mapFourδ₄Toδ₃' (q n : ℤ) :
    X.toCycles (homOfLE (bot_le : (⊥ : EInt) ≤ q)) (homOfLE (coe_le_coe_add_one q))
        (homOfLE bot_le) (Subsingleton.elim _ _) n ≫
      X.πE (homOfLE (bot_le : (⊥ : EInt) ≤ q)) (homOfLE (coe_le_coe_add_one q))
        (homOfLE (le_refl ((q + 1 : ℤ) : EInt))) (n - 1) n (n + 1) ≫
      X.mapFourδ₄Toδ₃' ⊥ q ((q + 1 : ℤ) : EInt) ((q + 1 : ℤ) : EInt) ⊤ bot_le
        (coe_le_coe_add_one q) le_rfl le_top (n - 1) n (n + 1) =
    X.pOpcycles (homOfLE (bot_le : (⊥ : EInt) ≤ ((q + 1 : ℤ) : EInt)))
        (homOfLE (le_top : ((q + 1 : ℤ) : EInt) ≤ ⊤)) n ≫
      X.opcyclesToE (homOfLE (bot_le : (⊥ : EInt) ≤ q)) (homOfLE (coe_le_coe_add_one q))
        (homOfLE (le_top : ((q + 1 : ℤ) : EInt) ≤ ⊤)) (homOfLE bot_le)
        (Subsingleton.elim _ _) (n - 1) n (n + 1) := by
  rw [X.p_opcyclesToE _ _ _ _ _ (n - 1) n (n + 1), mapFourδ₄Toδ₃',
    X.πE_map (n₀ := n - 1) (n₁ := n) (n₂ := n + 1) (β := 𝟙 _), cyclesMap_id, Category.id_comp]

/-- The computation of `H_map_comp_spectralSequencePageXToEInfty`, with the bottom index `a` of the
first page and the top index `b` of `E^n(⊥ ≤ q ≤ q + 1 ≤ b)` as variables, so that they can be
substituted by `q` and `q + 1`. -/
private lemma H_map_comp_spectralSequencePageXToEInfty_aux (pq : ℤ × ℤ) (n : ℤ)
    (hn : n = pq.1 + pq.2) (a b : EInt) (ha : a = (pq.2 : EInt)) (hb : b = ((pq.2 + 1 : ℤ) : EInt))
    (h₀ : IsZero ((X.H (n + 1)).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ a))))) :
    (X.H n).map (twoδ₁Toδ₀ (homOfLE (bot_le : (⊥ : EInt) ≤ pq.2))
        (homOfLE (coe_le_coe_add_one pq.2)) (homOfLE bot_le) (Subsingleton.elim _ _)) ≫
      (X.spectralSequenceFirstPageXIso coreE₂Cohomological pq pq.2 ((pq.2 + 1 : ℤ) : EInt)
        rfl rfl n hn).inv ≫
      (X.spectralSequencePageXIso coreE₂Cohomological 2 le_rfl pq a pq.2
        ((pq.2 + 1 : ℤ) : EInt) b (by rw [ha]; exact congrArg _ (by omega)) rfl rfl
        (by rw [hb]; exact congrArg _ (by omega)) (n - 1) n (n + 1) hn).hom ≫
      (X.isoMapFourδ₁Toδ₀' ⊥ a pq.2 ((pq.2 + 1 : ℤ) : EInt) b bot_le (by rw [ha])
        (coe_le_coe_add_one pq.2) (by rw [hb]) (n - 1) n (n + 1) h₀).inv ≫
      X.mapFourδ₄Toδ₃' ⊥ pq.2 ((pq.2 + 1 : ℤ) : EInt) b ⊤ bot_le (coe_le_coe_add_one pq.2)
        (by rw [hb]) le_top (n - 1) n (n + 1) =
    X.pOpcycles (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 + 1 : ℤ) : EInt)))
        (homOfLE (le_top : ((pq.2 + 1 : ℤ) : EInt) ≤ ⊤)) n ≫
      X.opcyclesToE (homOfLE (bot_le : (⊥ : EInt) ≤ pq.2)) (homOfLE (coe_le_coe_add_one pq.2))
        (homOfLE (le_top : ((pq.2 + 1 : ℤ) : EInt) ≤ ⊤)) (homOfLE bot_le)
        (Subsingleton.elim _ _) (n - 1) n (n + 1) := by
  subst ha hb
  rw [X.H_map_comp_spectralSequenceFirstPageXIso_inv_assoc pq n hn, Iso.inv_hom_id_assoc,
    X.isoMapFourδ₁Toδ₀'_hom_inv_id_assoc (n₀ := n - 1) (n₁ := n) (n₂ := n + 1),
    toCycles_πE_mapFourδ₄Toδ₃']

/-- **The edge map from the first page.** Let `pq = (p, q)` and `n = p + q`, and suppose that
`H^{n+1}(⊥ ≤ q)` vanishes. The map `H^n(⊥ ≤ q + 1) ⟶ H^n(q ≤ q + 1)`, followed by the
identification of `H^n(q ≤ q + 1)` with the first page at `pq` and the map
`spectralSequencePageXToEInfty` onto `X.EInfty q n = E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)`, is the projection of
`H^n(⊥ ≤ q + 1)` onto `opZ^n(⊥ ≤ q + 1, q + 1 ≤ ⊤)`, the piece `F_{q+1} H^n` of the abutment,
followed by the canonical map `opcyclesToE`. -/
@[reassoc]
lemma H_map_comp_spectralSequencePageXToEInfty (pq : ℤ × ℤ) (n : ℤ) (hn : n = pq.1 + pq.2)
    (h₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - 2 + 2 : ℤ) : EInt)))))) :
    (X.H n).map (twoδ₁Toδ₀ (homOfLE (bot_le : (⊥ : EInt) ≤ pq.2))
        (homOfLE (coe_le_coe_add_one pq.2)) (homOfLE bot_le) (Subsingleton.elim _ _)) ≫
      (X.spectralSequenceFirstPageXIso coreE₂Cohomological pq pq.2 ((pq.2 + 1 : ℤ) : EInt)
        rfl rfl n hn).inv ≫
      X.spectralSequencePageXToEInfty 2 le_rfl pq n hn h₀ =
    X.pOpcycles (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 + 1 : ℤ) : EInt)))
        (homOfLE (le_top : ((pq.2 + 1 : ℤ) : EInt) ≤ ⊤)) n ≫
      X.opcyclesToE (homOfLE (bot_le : (⊥ : EInt) ≤ pq.2)) (homOfLE (coe_le_coe_add_one pq.2))
        (homOfLE (le_top : ((pq.2 + 1 : ℤ) : EInt) ≤ ⊤)) (homOfLE bot_le)
        (Subsingleton.elim _ _) (n - 1) n (n + 1) := by
  have hEBot : (X.spectralSequencePageXIsoEBot 2 le_rfl pq n hn h₀).hom =
      (X.spectralSequencePageXIso coreE₂Cohomological 2 le_rfl pq ((pq.2 - 2 + 2 : ℤ) : EInt)
        pq.2 ((pq.2 + 1 : ℤ) : EInt) ((pq.2 + 2 - 1 : ℤ) : EInt) rfl rfl rfl rfl
        (n - 1) n (n + 1) hn).hom ≫
      (X.isoMapFourδ₁Toδ₀' ⊥ ((pq.2 - 2 + 2 : ℤ) : EInt) pq.2 ((pq.2 + 1 : ℤ) : EInt)
        ((pq.2 + 2 - 1 : ℤ) : EInt) bot_le (by simp) (coe_le_coe_add_one pq.2) (by simp; omega)
        (n - 1) n (n + 1) h₀).inv := by
    rw [← cancel_mono (X.spectralSequencePageXIsoEBot 2 le_rfl pq n hn h₀).inv, Iso.hom_inv_id,
      spectralSequencePageXIsoEBot_inv, Category.assoc,
      X.isoMapFourδ₁Toδ₀'_inv_hom_id_assoc (n₀ := n - 1) (n₁ := n) (n₂ := n + 1), Iso.hom_inv_id]
  rw [spectralSequencePageXToEInfty_def, hEBot, Category.assoc]
  -- the auxiliary statement is stated for the indices `q - 2 + 2` and `q + 2 - 1` of the page `2`
  exact X.H_map_comp_spectralSequencePageXToEInfty_aux pq n hn _ _ (congrArg _ (by omega))
    (congrArg _ (by omega)) h₀

/-- **The edge map from the first page, on the graded piece.** Through `EInftyIsoCokernel`, the
map of `H_map_comp_spectralSequencePageXToEInfty` is the projection of `H^n(⊥ ≤ q + 1)` onto the
piece `F_{q+1} H^n` of the abutment, followed by the projection onto the graded piece
`F_{q+1} H^n / F_q H^n`. -/
@[reassoc]
lemma H_map_comp_spectralSequencePageXToEInfty_EInftyIsoCokernel_hom (pq : ℤ × ℤ) (n : ℤ)
    (hn : n = pq.1 + pq.2)
    (h₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - 2 + 2 : ℤ) : EInt)))))) :
    (X.H n).map (twoδ₁Toδ₀ (homOfLE (bot_le : (⊥ : EInt) ≤ pq.2))
        (homOfLE (coe_le_coe_add_one pq.2)) (homOfLE bot_le) (Subsingleton.elim _ _)) ≫
      (X.spectralSequenceFirstPageXIso coreE₂Cohomological pq pq.2 ((pq.2 + 1 : ℤ) : EInt)
        rfl rfl n hn).inv ≫
      X.spectralSequencePageXToEInfty 2 le_rfl pq n hn h₀ ≫ (X.EInftyIsoCokernel pq.2 n).hom =
    X.pOpcycles (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 + 1 : ℤ) : EInt)))
        (homOfLE (le_top : ((pq.2 + 1 : ℤ) : EInt) ≤ ⊤)) n ≫
      cokernel.π (X.abutmentFiltrationMap pq.2 n) := by
  rw [X.H_map_comp_spectralSequencePageXToEInfty_assoc pq n hn h₀,
    opcyclesToE_EInftyIsoCokernel_hom]

/-- When the piece `F_q H^n` of the filtration of the abutment vanishes, the projection of
`F_{q+1} H^n` onto the graded piece `F_{q+1} H^n / F_q H^n` is an isomorphism. -/
lemma isIso_cokernel_π_abutmentFiltrationMap_of_isZero {q n : ℤ}
    (h : IsZero (X.abutmentFiltration q n)) : IsIso (cokernel.π (X.abutmentFiltrationMap q n)) := by
  rw [show X.abutmentFiltrationMap q n = 0 from h.eq_of_src _ _]
  infer_instance

/-- **The edge map into the abutment.** When the piece `F_q H^n` of the filtration of the abutment
vanishes, the limit object `X.EInfty q n`, the graded piece `F_{q+1} H^n / F_q H^n`, is the piece
`F_{q+1} H^n`, and this is its embedding into the abutment `H^n(⊥ ≤ ⊤)`, with image
`F_{q+1} H^n`. -/
noncomputable def EInftyToAbutment (q n : ℤ) (h : IsZero (X.abutmentFiltration q n)) :
    X.EInfty q n ⟶ X.abutment n :=
  (X.EInftyIsoCokernel q n).hom ≫
    cokernel.desc _ (X.abutmentFiltrationι (q + 1) n) (h.eq_of_src _ _)

/-- `X.EInftyToAbutment` is the identification `EInftyIsoCokernel` of `X.EInfty q n` with the
graded piece, followed by the embedding of `F_{q+1} H^n`. -/
lemma EInftyToAbutment_def (q n : ℤ) (h : IsZero (X.abutmentFiltration q n)) :
    X.EInftyToAbutment q n h = (X.EInftyIsoCokernel q n).hom ≫
      cokernel.desc _ (X.abutmentFiltrationι (q + 1) n) (h.eq_of_src _ _) :=
  (rfl)

/-- `X.EInftyToAbutment` is the identification `EInftyIsoCokernel` of `X.EInfty q n` with the
graded piece, followed by the inverse of the projection of `F_{q+1} H^n` onto the graded piece,
an isomorphism as `F_q H^n` vanishes, and the embedding of `F_{q+1} H^n`. -/
lemma EInftyToAbutment_eq (q n : ℤ) (h : IsZero (X.abutmentFiltration q n)) :
    haveI := X.isIso_cokernel_π_abutmentFiltrationMap_of_isZero h
    X.EInftyToAbutment q n h = (X.EInftyIsoCokernel q n).hom ≫
      inv (cokernel.π (X.abutmentFiltrationMap q n)) ≫ X.abutmentFiltrationι (q + 1) n := by
  rw [EInftyToAbutment_def]
  congr 1
  rw [IsIso.eq_inv_comp, cokernel.π_desc]

/-- The map `X.EInftyToAbutment` from `X.EInfty q n` to the abutment is a monomorphism. -/
instance (q n : ℤ) (h : IsZero (X.abutmentFiltration q n)) : Mono (X.EInftyToAbutment q n h) := by
  have := X.isIso_cokernel_π_abutmentFiltrationMap_of_isZero h
  rw [EInftyToAbutment_eq]
  infer_instance

/-- On `F_{q+1} H^n = opZ^n(⊥ ≤ q + 1, q + 1 ≤ ⊤)`, the canonical map `opcyclesToE` followed by
`X.EInftyToAbutment` is the embedding of `F_{q+1} H^n` into the abutment. -/
@[reassoc (attr := simp)]
lemma opcyclesToE_EInftyToAbutment (q n : ℤ) (h : IsZero (X.abutmentFiltration q n)) :
    X.opcyclesToE (homOfLE (bot_le : (⊥ : EInt) ≤ q)) (homOfLE (coe_le_coe_add_one q))
        (homOfLE (le_top : ((q + 1 : ℤ) : EInt) ≤ ⊤)) (homOfLE bot_le) (Subsingleton.elim _ _)
        (n - 1) n (n + 1) ≫ X.EInftyToAbutment q n h =
      X.abutmentFiltrationι (q + 1) n := by
  rw [EInftyToAbutment_def, opcyclesToE_EInftyIsoCokernel_hom_assoc, cokernel.π_desc]

/-- **The edge map from the first page into the abutment.** Let `pq = (p, q)` and `n = p + q`, and
suppose that `H^{n+1}(⊥ ≤ q)` and the piece `F_q H^n` of the abutment vanish. The map
`H^n(⊥ ≤ q + 1) ⟶ H^n(q ≤ q + 1)`, followed by the identification of `H^n(q ≤ q + 1)` with the
first page at `pq`, the map `spectralSequencePageXToEInfty` onto `X.EInfty q n` and the edge map
`X.EInftyToAbutment` into the abutment, is the map `H^n(⊥ ≤ q + 1) ⟶ H^n(⊥ ≤ ⊤)`. -/
@[reassoc]
lemma H_map_comp_spectralSequencePageXToEInfty_EInftyToAbutment (pq : ℤ × ℤ) (n : ℤ)
    (hn : n = pq.1 + pq.2)
    (h₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - 2 + 2 : ℤ) : EInt))))))
    (h : IsZero (X.abutmentFiltration pq.2 n)) :
    (X.H n).map (twoδ₁Toδ₀ (homOfLE (bot_le : (⊥ : EInt) ≤ pq.2))
        (homOfLE (coe_le_coe_add_one pq.2)) (homOfLE bot_le) (Subsingleton.elim _ _)) ≫
      (X.spectralSequenceFirstPageXIso coreE₂Cohomological pq pq.2 ((pq.2 + 1 : ℤ) : EInt)
        rfl rfl n hn).inv ≫
      X.spectralSequencePageXToEInfty 2 le_rfl pq n hn h₀ ≫ X.EInftyToAbutment pq.2 n h =
    (X.H n).map (twoδ₂Toδ₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 + 1 : ℤ) : EInt)))
      (homOfLE (le_top : ((pq.2 + 1 : ℤ) : EInt) ≤ ⊤)) (homOfLE bot_le)
      (Subsingleton.elim _ _)) := by
  rw [X.H_map_comp_spectralSequencePageXToEInfty_assoc pq n hn h₀, opcyclesToE_EInftyToAbutment,
    pOpcycles_abutmentFiltrationι]

/-- **The classes coming from `H^n(⊥ ≤ q + 1)` are cycles of the first page.** The map
`H^n(⊥ ≤ q + 1) ⟶ H^n(q ≤ q + 1)`, followed by the identification of `H^n(q ≤ q + 1)` with the
first page at `pq = (p, q)`, `n = p + q`, is killed by the differential of the first page: it
factors through the cycles `E^n(q - 1 ≤ q ≤ q + 1 ≤ q + 1)` of the first page. -/
@[reassoc (attr := simp)]
lemma H_map_comp_spectralSequenceFirstPageXIso_inv_d (pq pq' : ℤ × ℤ) (n : ℤ)
    (hn : n = pq.1 + pq.2) :
    (X.H n).map (twoδ₁Toδ₀ (homOfLE (bot_le : (⊥ : EInt) ≤ pq.2))
        (homOfLE (coe_le_coe_add_one pq.2)) (homOfLE bot_le) (Subsingleton.elim _ _)) ≫
      (X.spectralSequenceFirstPageXIso coreE₂Cohomological pq pq.2 ((pq.2 + 1 : ℤ) : EInt)
        rfl rfl n hn).inv ≫ ((X.spectralSequence coreE₂Cohomological).page 2).d pq pq' = 0 := by
  have hd := X.mapFourδ₁Toδ₀'_spectralSequencePageXIso_inv_d coreE₂Cohomological 2 3 rfl le_rfl
    pq pq' ((pq.2 - 1 : ℤ) : EInt) pq.2 pq.2 ((pq.2 + 1 : ℤ) : EInt) ((pq.2 + 1 : ℤ) : EInt)
    (congrArg _ (by omega)) (congrArg _ (by omega)) rfl rfl (congrArg _ (by omega)) (n - 1) n
    (n + 1) hn
  rw [Category.assoc] at hd
  rw [X.H_map_comp_spectralSequenceFirstPageXIso_inv_assoc pq n hn,
    ← X.mapFourδ₁Toδ₀'_comp_assoc ⊥ ((pq.2 - 1 : ℤ) : EInt) pq.2 pq.2 ((pq.2 + 1 : ℤ) : EInt)
      ((pq.2 + 1 : ℤ) : EInt) bot_le (by simp) le_rfl (coe_le_coe_add_one pq.2) le_rfl (n - 1) n
      (n + 1), hd, comp_zero, comp_zero, comp_zero]

/-- The lift to the cycles of the first page of the classes coming from `H^n(⊥ ≤ q + 1)` factors
through the cycle `E^n(q - 1 ≤ q ≤ q + 1 ≤ q + 1) ⟶ E_2^{p,q}` of
`mapFourδ₁Toδ₀'_spectralSequencePageXIso_inv_d`. -/
private lemma liftCycles_H_map_comp_spectralSequenceFirstPageXIso_inv (pq pq' : ℤ × ℤ)
    (hpq' : (ComplexShape.up' (⟨2, 1 - 2⟩ : ℤ × ℤ)).next pq = pq') (n : ℤ)
    (hn : n = pq.1 + pq.2) :
    ((X.spectralSequence coreE₂Cohomological).page 2).liftCycles
        ((X.H n).map (twoδ₁Toδ₀ (homOfLE (bot_le : (⊥ : EInt) ≤ pq.2))
          (homOfLE (coe_le_coe_add_one pq.2)) (homOfLE bot_le) (Subsingleton.elim _ _)) ≫
        (X.spectralSequenceFirstPageXIso coreE₂Cohomological pq pq.2 ((pq.2 + 1 : ℤ) : EInt)
          rfl rfl n hn).inv) pq' hpq'
        (by rw [Category.assoc, H_map_comp_spectralSequenceFirstPageXIso_inv_d]) =
      X.toCycles (homOfLE (bot_le : (⊥ : EInt) ≤ pq.2)) (homOfLE (coe_le_coe_add_one pq.2))
          (homOfLE bot_le) (Subsingleton.elim _ _) n ≫
        X.πE (homOfLE (bot_le : (⊥ : EInt) ≤ pq.2)) (homOfLE (coe_le_coe_add_one pq.2))
          (homOfLE (le_refl ((pq.2 + 1 : ℤ) : EInt))) (n - 1) n (n + 1) ≫
        X.mapFourδ₁Toδ₀' ⊥ ((pq.2 - 3 + 2 : ℤ) : EInt) pq.2 ((pq.2 + 1 : ℤ) : EInt)
          ((pq.2 + 1 : ℤ) : EInt) bot_le (by simp; omega) (coe_le_coe_add_one pq.2) le_rfl
          (n - 1) n (n + 1) ≫
        ((X.spectralSequence coreE₂Cohomological).page 2).liftCycles
          (X.mapFourδ₁Toδ₀' ((pq.2 - 3 + 2 : ℤ) : EInt) pq.2 pq.2 ((pq.2 + 1 : ℤ) : EInt)
            ((pq.2 + 1 : ℤ) : EInt) (by simp; omega) le_rfl (coe_le_coe_add_one pq.2) le_rfl
            (n - 1) n (n + 1) ≫
            (X.spectralSequencePageXIso coreE₂Cohomological 2 le_rfl pq pq.2 pq.2
              ((pq.2 + 1 : ℤ) : EInt) ((pq.2 + 1 : ℤ) : EInt) (congrArg _ (by omega)) rfl rfl
              (congrArg _ (by omega)) (n - 1) n (n + 1) hn).inv) pq' hpq'
          (X.mapFourδ₁Toδ₀'_spectralSequencePageXIso_inv_d coreE₂Cohomological 2 3 rfl le_rfl
            pq pq' ((pq.2 - 3 + 2 : ℤ) : EInt) pq.2 pq.2 ((pq.2 + 1 : ℤ) : EInt)
            ((pq.2 + 1 : ℤ) : EInt) (congrArg _ (by omega)) (congrArg _ (by omega)) rfl rfl
            (congrArg _ (by omega)) (n - 1) n (n + 1) hn) := by
  rw [← cancel_mono (HomologicalComplex.iCycles _ _)]
  simp only [HomologicalComplex.liftCycles_i, Category.assoc,
    X.H_map_comp_spectralSequenceFirstPageXIso_inv pq n hn]
  rw [X.mapFourδ₁Toδ₀'_comp_assoc (n₀ := n - 1) (n₁ := n) (n₂ := n + 1)]

/-- **The edge map from the second page into the abutment.** Let `pq = (p, q)` and `n = p + q`,
and suppose that `H^{n+1}(⊥ ≤ q - 1)` and the piece `F_q H^n` of the abutment vanish. The map
`H^n(⊥ ≤ q + 1) ⟶ H^n(q ≤ q + 1)`, followed by the identification of `H^n(q ≤ q + 1)` with the
first page at `pq`, lands in the cycles of the first page
(`H_map_comp_spectralSequenceFirstPageXIso_inv_d`); its class in the homology of the first page,
sent to the second page, onto `X.EInfty q n` and into the abutment by the edge map
`X.EInftyToAbutment`, is the map `H^n(⊥ ≤ q + 1) ⟶ H^n(⊥ ≤ ⊤)`.

Unlike `H_map_comp_spectralSequencePageXToEInfty_EInftyToAbutment`, this does not ask
`H^{n+1}(⊥ ≤ q)` to vanish, so the first page need not map to `X.EInfty q n` itself. This happens
for the filtration of a complex by its brutal truncations. -/
@[reassoc]
theorem liftCycles_H_map_homologyπ_iso_hom_EInftyToAbutment
    (pq pq' : ℤ × ℤ) (hpq' : (ComplexShape.up' (⟨2, 1 - 2⟩ : ℤ × ℤ)).next pq = pq') (n : ℤ)
    (hn : n = pq.1 + pq.2)
    (h₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - 3 + 2 : ℤ) : EInt))))))
    (h : IsZero (X.abutmentFiltration pq.2 n)) :
    ((X.spectralSequence coreE₂Cohomological).page 2).liftCycles
        ((X.H n).map (twoδ₁Toδ₀ (homOfLE (bot_le : (⊥ : EInt) ≤ pq.2))
          (homOfLE (coe_le_coe_add_one pq.2)) (homOfLE bot_le) (Subsingleton.elim _ _)) ≫
        (X.spectralSequenceFirstPageXIso coreE₂Cohomological pq pq.2 ((pq.2 + 1 : ℤ) : EInt)
          rfl rfl n hn).inv) pq' hpq'
        (by rw [Category.assoc, H_map_comp_spectralSequenceFirstPageXIso_inv_d]) ≫
      ((X.spectralSequence coreE₂Cohomological).page 2).homologyπ pq ≫
      ((X.spectralSequence coreE₂Cohomological).iso 2 3 pq rfl le_rfl).hom ≫
      X.spectralSequencePageXToEInfty 3 (by omega) pq n hn h₀ ≫ X.EInftyToAbutment pq.2 n h =
    (X.H n).map (twoδ₂Toδ₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 + 1 : ℤ) : EInt)))
      (homOfLE (le_top : ((pq.2 + 1 : ℤ) : EInt) ≤ ⊤)) (homOfLE bot_le)
      (Subsingleton.elim _ _)) := by
  rw [liftCycles_H_map_comp_spectralSequenceFirstPageXIso_inv]
  simp only [Category.assoc]
  rw [X.liftCycles_homologyπ_spectralSequence_iso_hom_assoc coreE₂Cohomological 2 3 rfl le_rfl pq
      pq' hpq' ((pq.2 - 3 + 2 : ℤ) : EInt) pq.2 pq.2 ((pq.2 + 1 : ℤ) : EInt)
      ((pq.2 + 1 : ℤ) : EInt) ((pq.2 + 3 - 1 : ℤ) : EInt) (congrArg _ (by omega))
      (congrArg _ (by omega)) rfl rfl (congrArg _ (by omega)) (congrArg _ (by omega)) (n - 1) n
      (n + 1) hn]
  rw [spectralSequencePageXToEInfty_def, spectralSequencePageXIsoEBot_hom]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc,
    X.mapFourδ₁Toδ₀'_mapFourδ₃Toδ₃'_assoc (n₀ := n - 1) (n₁ := n) (n₂ := n + 1),
    X.isoMapFourδ₁Toδ₀'_hom_inv_id_assoc (n₀ := n - 1) (n₁ := n) (n₂ := n + 1),
    X.mapFourδ₄Toδ₃'_comp_assoc (n₀ := n - 1) (n₁ := n) (n₂ := n + 1),
    toCycles_πE_mapFourδ₄Toδ₃'_assoc, opcyclesToE_EInftyToAbutment,
    pOpcycles_abutmentFiltrationι]

/-- When the piece `F_{q+1} H^n` is the whole abutment, the edge map `X.EInftyToAbutment q n` is an
isomorphism onto the abutment. -/
lemma isIso_EInftyToAbutment (q n : ℤ) (h : IsZero (X.abutmentFiltration q n))
    [IsIso (X.abutmentFiltrationι (q + 1) n)] : IsIso (X.EInftyToAbutment q n h) := by
  have := X.isIso_cokernel_π_abutmentFiltrationMap_of_isZero h
  rw [EInftyToAbutment_eq]
  infer_instance

/-- When the piece `F_{q+2} H^n` is the whole abutment, the projection of the abutment onto the
graded piece `X.EInfty (q + 1) n = F_{q+2} H^n / F_{q+1} H^n`. -/
noncomputable def abutmentToEInfty (q n : ℤ) [IsIso (X.abutmentFiltrationι (q + 1 + 1) n)] :
    X.abutment n ⟶ X.EInfty (q + 1) n :=
  inv (X.abutmentFiltrationι (q + 1 + 1) n) ≫ cokernel.π (X.abutmentFiltrationMap (q + 1) n) ≫
    (X.EInftyIsoCokernel (q + 1) n).inv

/-- `X.abutmentToEInfty` is the inverse of the embedding of `F_{q+2} H^n`, followed by the
projection onto the graded piece and the identification `EInftyIsoCokernel`. -/
lemma abutmentToEInfty_def (q n : ℤ) [IsIso (X.abutmentFiltrationι (q + 1 + 1) n)] :
    X.abutmentToEInfty q n = inv (X.abutmentFiltrationι (q + 1 + 1) n) ≫
      cokernel.π (X.abutmentFiltrationMap (q + 1) n) ≫ (X.EInftyIsoCokernel (q + 1) n).inv :=
  (rfl)

/-- On the piece `F_{q+2} H^n`, the projection `X.abutmentToEInfty q n` is the projection onto
the graded piece `F_{q+2} H^n / F_{q+1} H^n`, followed by the identification `EInftyIsoCokernel`. -/
@[reassoc (attr := simp)]
lemma abutmentFiltrationι_abutmentToEInfty (q n : ℤ)
    [IsIso (X.abutmentFiltrationι (q + 1 + 1) n)] :
    X.abutmentFiltrationι (q + 1 + 1) n ≫ X.abutmentToEInfty q n =
      cokernel.π (X.abutmentFiltrationMap (q + 1) n) ≫ (X.EInftyIsoCokernel (q + 1) n).inv := by
  rw [abutmentToEInfty_def, IsIso.hom_inv_id_assoc]

/-- The projection `X.abutmentToEInfty q n` of the abutment onto the graded piece is an
epimorphism. -/
instance (q n : ℤ) [IsIso (X.abutmentFiltrationι (q + 1 + 1) n)] :
    Epi (X.abutmentToEInfty q n) := by
  rw [abutmentToEInfty_def]
  infer_instance

/-- The edge map `X.EInftyToAbutment q n` followed by `X.abutmentToEInfty q n` vanishes. -/
@[reassoc (attr := simp)]
lemma EInftyToAbutment_abutmentToEInfty (q n : ℤ) (h : IsZero (X.abutmentFiltration q n))
    [IsIso (X.abutmentFiltrationι (q + 1 + 1) n)] :
    X.EInftyToAbutment q n h ≫ X.abutmentToEInfty q n = 0 := by
  rw [← cancel_epi (X.EInftyIsoCokernel q n).inv, ← cancel_epi (cokernel.π _)]
  simp only [EInftyToAbutment_def, abutmentToEInfty_def, Category.assoc, Iso.inv_hom_id_assoc,
    cokernel.π_desc_assoc, comp_zero]
  rw [← X.abutmentFiltrationMap_ι (q + 1) n, Category.assoc, IsIso.hom_inv_id_assoc,
    cokernel.condition_assoc, zero_comp]

/-- **The two-step filtration.** If the pieces `F_q H^n` and `F_{q+2} H^n` of the filtration of the
abutment are zero and everything, the abutment is an extension of the graded piece
`X.EInfty (q + 1) n` by `X.EInfty q n`: the sequence
`0 ⟶ X.EInfty q n ⟶ H^n(⊥ ≤ ⊤) ⟶ X.EInfty (q + 1) n ⟶ 0` is short exact. -/
theorem EInftyToAbutment_shortExact (q n : ℤ) (h : IsZero (X.abutmentFiltration q n))
    [IsIso (X.abutmentFiltrationι (q + 1 + 1) n)] :
    (ShortComplex.mk _ _ (X.EInftyToAbutment_abutmentToEInfty q n h)).ShortExact := by
  have := X.isIso_cokernel_π_abutmentFiltrationMap_of_isZero h
  let e₁ : X.abutmentFiltration (q + 1) n ≅ X.EInfty q n :=
    asIso (cokernel.π (X.abutmentFiltrationMap q n)) ≪≫ (X.EInftyIsoCokernel q n).symm
  let e₂ : X.abutmentFiltration (q + 1 + 1) n ≅ X.abutment n :=
    asIso (X.abutmentFiltrationι (q + 1 + 1) n)
  refine ShortComplex.shortExact_of_iso (ShortComplex.isoMk e₁ e₂
    (X.EInftyIsoCokernel (q + 1) n).symm ?_ ?_)
    (TauCeti.cokernelSequence_shortExact (X.abutmentFiltrationMap (q + 1) n))
  · simp only [e₁, e₂, Iso.trans_hom, asIso_hom, Iso.symm_hom, ShortComplex.cokernelSequence_f,
      EInftyToAbutment_def]
    -- the terms of `ShortComplex.cokernelSequence` are only definitionally those of the cokernel
    exact (Category.assoc _ _ _).trans ((cokernel.π _ ≫= Iso.inv_hom_id_assoc _ _).trans
      ((cokernel.π_desc _ _ _).trans (X.abutmentFiltrationMap_ι (q + 1) n).symm))
  · simp only [e₂, asIso_hom, Iso.symm_hom, ShortComplex.cokernelSequence_g,
      abutmentToEInfty_def]
    -- the terms of `ShortComplex.cokernelSequence` are only definitionally those of the cokernel
    exact IsIso.hom_inv_id_assoc (X.abutmentFiltrationι (q + 1 + 1) n) _

end CategoryTheory.Abelian.SpectralObject

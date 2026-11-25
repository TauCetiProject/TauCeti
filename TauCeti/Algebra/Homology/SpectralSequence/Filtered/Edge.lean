/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralObject.Edge
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Convergence

/-!
# The edge map of the spectral sequence of a filtered complex

Let `F : ℤ → Subobject K` be an increasing filtration of a cochain complex `K`, and `q` an index
such that `H^{n+1}(F_q)` and the piece `F_q H^n` of the induced filtration of `H^n(K)` vanish, as
happens for the lowest nonzero piece `F_{q+1}` of a filtration bounded below. The first page of
the spectral sequence at `(p, q)`, `n = p + q`, is `H^n(F_{q+1}/F_q)`
(`CochainComplex.spectralSequenceFirstPageXIsoCokernel`), and it maps onto the limit object
`E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)`, which is the bottom piece `F_{q+1} H^n` of `H^n(K)`. The resulting edge
map into `H^n(K)` has image this bottom piece `F_{q+1} H^n`. It is computed on the classes coming
from `H^n(F_{q+1})`: composed with the map `H^n(F_{q+1}) ⟶ H^n(F_{q+1}/F_q)`, it is the map
`H^n(F_{q+1}) ⟶ H^n(K)` induced by the inclusion
(`CochainComplex.homologyMap_comp_spectralSequencePageXToEInfty_EInftyToAbutment`).

## Main results

* `CochainComplex.homologyMap_comp_spectralSequencePageXToEInfty_EInftyToAbutment`: the edge map
  from the first page into `H^n(K)`, whose image is the bottom piece `F_{q+1} H^n` of the
  filtration, on the classes coming from `H^n(F_{q+1})`.
-/

public section

open CategoryTheory Limits ComposableArrows

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] {K : CochainComplex C ℤ} (F : ℤ → Subobject K)
  (hF : Monotone F)

/-- The map `H^n(F_{q+1}) ⟶ H^n(F_{q+1}/F_q)`, followed by the identification of
`H^n(F_{q+1}/F_q)` with `H^n(q ≤ q + 1)`, is the map `H^n(⊥ ≤ q + 1) ⟶ H^n(q ≤ q + 1)` of the
spectral object, read on `H^n(F_{q+1}) = H^n(F_{q+1}/F_⊥)`. -/
private lemma homologyMap_cokernel_π_spectralObjectHIsoCokernel_inv (q n : ℤ) :
    HomologicalComplex.homologyMap (eqToHom (filtrationFunctor_obj_coe F hF (q + 1)).symm ≫
        cokernel.π ((filtrationFunctor F hF).map
          (homOfLE (coe_le_coe_of_eq_add_one (rfl : q = q) rfl)))) n ≫
      (spectralObjectHIsoCokernel _ _ n).inv =
    HomologicalComplex.homologyMap (eqToHom (filtrationFunctor_obj_coe F hF (q + 1)).symm ≫
        cokernel.π ((filtrationFunctor F hF).map
          (homOfLE (bot_le : (⊥ : EInt) ≤ ((q + 1 : ℤ) : EInt))))) n ≫
      (spectralObjectHIsoCokernel _ _ n).inv ≫
      ((spectralObject (filtrationFunctor F hF)).H n).map
        (twoδ₁Toδ₀ (homOfLE (bot_le : (⊥ : EInt) ≤ q))
          (homOfLE (Abelian.SpectralObject.coe_le_coe_add_one q)) (homOfLE bot_le)
          (Subsingleton.elim _ _)) := by
  rw [Iso.comp_inv_eq, Category.assoc, Category.assoc,
    spectralObject_H_map_comp_spectralObjectHIsoCokernel_hom, Iso.inv_hom_id_assoc,
    ← HomologicalComplex.homologyMap_comp]
  congr 1
  simp

/-- **The edge map of the spectral sequence of a filtered complex.** Let `pq = (p, q)` and
`n = p + q`, and suppose that `H^{n+1}(F_q)` and the piece `F_q H^n` of the filtration of
`H^n(K)` vanish. The map `H^n(F_{q+1}) ⟶ H^n(F_{q+1}/F_q)`, followed by the identification with
the first page at `pq`, the map onto `E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)`, its embedding into the abutment and
the identification of the abutment with `H^n(K)`, is the map `H^n(F_{q+1}) ⟶ H^n(K)` induced by
the inclusion. -/
@[reassoc]
theorem homologyMap_comp_spectralSequencePageXToEInfty_EInftyToAbutment (pq : ℤ × ℤ) (n : ℤ)
    (hn : n = pq.1 + pq.2) (h₀ : IsZero ((F (pq.2 - 2 + 2) : CochainComplex C ℤ).homology (n + 1)))
    (h : IsZero ((spectralObject (filtrationFunctor F hF)).abutmentFiltration pq.2 n)) :
    HomologicalComplex.homologyMap (eqToHom (filtrationFunctor_obj_coe F hF (pq.2 + 1)).symm ≫
        cokernel.π ((filtrationFunctor F hF).map
          (homOfLE (coe_le_coe_of_eq_add_one (rfl : pq.2 = pq.2) rfl)))) n ≫
      (spectralSequenceFirstPageXIsoCokernel (filtrationFunctor F hF) pq pq.2 (pq.2 + 1) rfl rfl
        n hn).inv ≫
      (spectralObject (filtrationFunctor F hF)).spectralSequencePageXToEInfty 2 le_rfl pq n hn
        (isZero_spectralObject_H_bot F hF _ _ h₀) ≫
      (spectralObject (filtrationFunctor F hF)).EInftyToAbutment pq.2 n h ≫
      (filtrationAbutmentIso F hF n).hom =
    HomologicalComplex.homologyMap (F (pq.2 + 1)).arrow n := by
  rw [spectralSequenceFirstPageXIsoCokernel_eq, Iso.trans_inv, Category.assoc,
    reassoc_of% homologyMap_cokernel_π_spectralObjectHIsoCokernel_inv,
    Abelian.SpectralObject.H_map_comp_spectralSequencePageXToEInfty_EInftyToAbutment_assoc,
    filtrationAbutmentIso_hom, spectralObject_H_map_comp_spectralObjectHIsoCokernel_hom_assoc,
    Iso.inv_hom_id_assoc]
  simp only [← HomologicalComplex.homologyMap_comp]
  congr 1
  simp

end CochainComplex

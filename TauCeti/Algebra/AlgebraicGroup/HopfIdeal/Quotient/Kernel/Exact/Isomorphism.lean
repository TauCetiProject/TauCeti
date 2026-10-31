/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Exact

/-!
# Short exact sequences under coordinate isomorphisms

Replacing the three coordinate Hopf algebras by isomorphic ones preserves and reflects
short exactness of affine group schemes. This allows a sequence to be checked in explicit
coordinates, while retaining its scheme-theoretic kernel.
-/

public section

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

universe u v

variable {R : Type u} [CommRing R]
variable {Q G N Q' G' N' : _root_.CommHopfAlgCat.{v} R}
variable {p : Q ⟶ G} {i : G ⟶ N}

/-- Short exactness is preserved when the three coordinate algebras are replaced by
isomorphic ones. -/
theorem IsShortExact.of_iso (h : IsShortExact p i)
    (eQ : Q ≅ Q') (eG : G ≅ G') (eN : N ≅ N') :
    IsShortExact (eQ.inv ≫ p ≫ eG.hom) (eG.inv ≫ i ≫ eN.hom) := by
  have bQ := ConcreteCategory.bijective_of_isIso eQ.inv
  have bG := ConcreteCategory.bijective_of_isIso eG.hom
  have bGi := ConcreteCategory.bijective_of_isIso eG.inv
  have bN := ConcreteCategory.bijective_of_isIso eN.hom
  refine ⟨?_, ?_, ?_⟩
  · rw [_root_.CommHopfAlgCat.hom_comp, _root_.CommHopfAlgCat.hom_comp,
      BialgHom.comp_toAlgHom, BialgHom.comp_toAlgHom]
    exact RingHom.FaithfullyFlat.stableUnderComposition _ _
      (RingHom.FaithfullyFlat.of_bijective bQ)
      (RingHom.FaithfullyFlat.stableUnderComposition _ _ h.faithfullyFlat
        (RingHom.FaithfullyFlat.of_bijective bG))
  · simpa only [_root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp] using
      (bN.2.comp h.surjective).comp bGi.2
  · rw [kernelHopfIdeal_comp_of_surjective eQ.inv bQ.2,
      kernelHopfIdeal_comp, HopfIdeal.map_toIdeal]
    ext x
    obtain ⟨y, rfl⟩ := bG.2 x
    rw [Ideal.mem_map_iff_of_surjective (eG.hom.hom : G →+* G') bG.2]
    simp only [RingHom.coe_coe, bG.1.eq_iff, exists_eq_right]
    rw [← h.ker_eq, RingHom.mem_ker, RingHom.mem_ker]
    simp only [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_toAlgHom,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, BialgHom.coe_toAlgHom,
      AlgHom.comp_apply, Iso.hom_inv_id_apply, map_eq_zero_iff _ bN.1]

/-- Short exactness can be checked after changing all three coordinate algebras by
isomorphisms. -/
@[simp]
theorem isShortExact_iso_iff (eQ : Q ≅ Q') (eG : G ≅ G') (eN : N ≅ N') :
    IsShortExact (eQ.inv ≫ p ≫ eG.hom) (eG.inv ≫ i ≫ eN.hom) ↔ IsShortExact p i := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.of_iso eQ eG eN⟩
  simpa only [Iso.symm_inv, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id] using h.of_iso eQ.symm eG.symm eN.symm

end TauCeti.CommHopfAlgCat

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.StructureSheaf

/-!
# Independence of the formal spectrum from the ideal of definition

The structure sheaf `O_{Spf A} = lim_n O_{I ^ (n + 1)}` of the formal spectrum is built from a
chosen ideal of definition `I` of `A` (`TauCeti.FormalScheme.Spf.structureSheaf`). Its
underlying space, the set of open primes of `A`, does not depend on this choice. This file shows
that the sheaf does not either: another ideal of definition `J` gives a canonically isomorphic
structure sheaf, so `Spf A` depends only on the topological ring `A` (EGA I, Ch. I, 10.1.1).

The comparison goes through the projections `TauCeti.FormalScheme.Spf.toQuotientSheaf` of the
structure sheaf to the thickenings `O_K` defined by arbitrary ideals of definition `K`. The
structure sheaf built from `J` is the limit of the `O_{J ^ (n + 1)}`, so the projections of
`O_{Spf_I A}` to these thickenings induce a map `O_{Spf_I A} → O_{Spf_J A}`. Its inverse comes
from the same construction with `I` and `J` exchanged, since the powers of either ideal are
cofinal among the powers of the other (EGA I, Ch. 0, 7.1.9).

## Main definitions

* `TauCeti.FormalScheme.Spf.structureSheafIso`: for ideals of definition `I` and `J`, the
  canonical isomorphism between the structure sheaves of `Spf A` built from `I` and from `J`.

## Main results

* `TauCeti.FormalScheme.Spf.structureSheafIso_hom_comp_toQuotientSheaf`: the comparison
  isomorphism commutes with the projections to every thickening `O_K`.
* `TauCeti.FormalScheme.Spf.structureSheafIso_self`,
  `TauCeti.FormalScheme.Spf.structureSheafIso_trans`,
  `TauCeti.FormalScheme.Spf.structureSheafIso_symm`: the comparison isomorphisms form a
  coherent system.
* `TauCeti.FormalScheme.Spf.globalSectionsIso_inv_comp_structureSheafIso_hom`: the comparison
  isomorphism is compatible with the identifications of the global sections with `A`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.1 (7.1.9)
  and Ch. I, §10.1 (10.1.1–10.1.3).
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY).
-/

public section

universe u

open CategoryTheory Opposite

namespace TauCeti.FormalScheme.Spf

variable {A : Type u} [CommRing A] [TopologicalSpace A] {I J K L : Ideal A}

variable [IsTopologicalRing A]

/-- The comparison map `O_{Spf_I A} → O_{Spf_J A}` induced by the projections of the structure
sheaf built from `I` to the thickenings `O_{J ^ (n + 1)}`. -/
private noncomputable def structureSheafHom (hI : IsAdic I) (hJ : IsAdic J) :
    structureSheaf hI ⟶ structureSheaf hJ :=
  structureSheaf.lift hJ (fun _ ↦ toQuotientSheaf hI _) fun _ ↦
    toQuotientSheaf_comp_quotientTransition _ _ _ _

private theorem structureSheafHom_comp_toQuotientSheaf (hI : IsAdic I) (hJ : IsAdic J)
    (hK : IsAdic K) :
    structureSheafHom hI hJ ≫ toQuotientSheaf hJ hK = toQuotientSheaf hI hK := by
  obtain ⟨n, hn⟩ := hJ.exists_pow_succ_le (by simpa using hK.isOpen_pow 1)
  exact (structureSheaf.lift_toQuotientSheaf hJ hK (fun _ ↦ toQuotientSheaf hI _)
    (fun _ ↦ toQuotientSheaf_comp_quotientTransition _ _ _ _) hn).trans
    (toQuotientSheaf_comp_quotientTransition _ _ _ _)

private theorem structureSheafHom_comp_structureSheafHom (hI : IsAdic I) (hJ : IsAdic J) :
    structureSheafHom hI hJ ≫ structureSheafHom hJ hI = 𝟙 _ :=
  structureSheaf.hom_ext hI fun n ↦ by
    rw [Category.assoc, ← toQuotientSheaf_pow_succ, structureSheafHom_comp_toQuotientSheaf,
      structureSheafHom_comp_toQuotientSheaf, Category.id_comp]

/-- For ideals of definition `I` and `J` of `A`, the canonical isomorphism between the structure
sheaves of `Spf A` built from `I` and from `J`. Both are sheaves on the same space, the open primes
of `A`, and the isomorphism commutes with the projections to the thickenings `O_K` for every
ideal of definition `K` (`structureSheafIso_hom_comp_toQuotientSheaf`) and with the
identifications of the global sections with `A`
(`globalSectionsIso_inv_comp_structureSheafIso_hom`). Thus `Spf A` depends only on the topology
of `A` (EGA I, Ch. I, 10.1.1). -/
noncomputable def structureSheafIso (hI : IsAdic I) (hJ : IsAdic J) :
    structureSheaf hI ≅ structureSheaf hJ where
  hom := structureSheafHom hI hJ
  inv := structureSheafHom hJ hI
  hom_inv_id := structureSheafHom_comp_structureSheafHom hI hJ
  inv_hom_id := structureSheafHom_comp_structureSheafHom hJ hI

/-- The comparison isomorphism commutes with the projections to the thickening `O_K`, for every
ideal of definition `K`. -/
@[reassoc (attr := simp)]
theorem structureSheafIso_hom_comp_toQuotientSheaf (hI : IsAdic I) (hJ : IsAdic J)
    (hK : IsAdic K) :
    (structureSheafIso hI hJ).hom ≫ toQuotientSheaf hJ hK = toQuotientSheaf hI hK :=
  structureSheafHom_comp_toQuotientSheaf hI hJ hK

/-- The comparison isomorphism commutes with the projections to the thickenings
`O_{J ^ (n + 1)}`. -/
@[reassoc (attr := simp)]
theorem structureSheafIso_hom_comp_quotientProjection (hI : IsAdic I) (hJ : IsAdic J) (n : ℕ) :
    (structureSheafIso hI hJ).hom ≫ quotientProjection hJ n =
      toQuotientSheaf hI (is_ideal_adic_pow hJ n.succ_pos) := by
  rw [← toQuotientSheaf_pow_succ, structureSheafIso_hom_comp_toQuotientSheaf]

/-- The inverse of the comparison isomorphism from `I` to `J` is the comparison isomorphism from
`J` to `I`. -/
@[simp]
theorem structureSheafIso_symm (hI : IsAdic I) (hJ : IsAdic J) :
    (structureSheafIso hI hJ).symm = structureSheafIso hJ hI :=
  (rfl)

/-- The inverse of the comparison isomorphism from `I` to `J` is the comparison map from `J`
to `I`. -/
@[simp]
theorem structureSheafIso_inv (hI : IsAdic I) (hJ : IsAdic J) :
    (structureSheafIso hI hJ).inv = (structureSheafIso hJ hI).hom :=
  (rfl)

/-- The comparison isomorphism of an ideal of definition with itself is the identity. -/
@[simp]
theorem structureSheafIso_self (hI : IsAdic I) : structureSheafIso hI hI = Iso.refl _ := by
  ext1
  refine structureSheaf.hom_ext hI fun n ↦ ?_
  rw [← toQuotientSheaf_pow_succ, structureSheafIso_hom_comp_toQuotientSheaf, Iso.refl_hom,
    Category.id_comp]

/-- The comparison isomorphisms compose: comparing `I` with `J` and then `J` with `L` is
comparing `I` with `L`. -/
@[simp]
theorem structureSheafIso_trans (hI : IsAdic I) (hJ : IsAdic J) (hL : IsAdic L) :
    structureSheafIso hI hJ ≪≫ structureSheafIso hJ hL = structureSheafIso hI hL := by
  ext1
  refine structureSheaf.hom_ext hL fun n ↦ ?_
  rw [Iso.trans_hom, ← toQuotientSheaf_pow_succ, Category.assoc,
    structureSheafIso_hom_comp_toQuotientSheaf, structureSheafIso_hom_comp_toQuotientSheaf,
    structureSheafIso_hom_comp_toQuotientSheaf]

/-- The comparison isomorphism is compatible with the identifications of the global sections with
`A`: it sends the global section corresponding to `a ∈ A` for `I` to the global section
corresponding to `a` for `J`. By `IsAdic.isAdicComplete_iff_of_isAdic`, `A` is `I`-adically
complete exactly when it is `J`-adically complete. -/
@[reassoc (attr := simp)]
theorem globalSectionsIso_inv_comp_structureSheafIso_hom [IsAdicComplete I A]
    [IsAdicComplete J A] (hI : IsAdic I) (hJ : IsAdic J) :
    (globalSectionsIso hI).inv ≫ (structureSheafIso hI hJ).hom.hom.app (op ⊤) =
      (globalSectionsIso hJ).inv := by
  rw [← cancel_mono (globalSectionsIso hJ).hom, Iso.inv_hom_id]
  refine (IsAdicComplete.isLimitQuotientPowSuccCone J).hom_ext fun n ↦ ?_
  -- Reduce modulo `J ^ (n + 1)`: on global sections, `quotientProjection hJ n` followed by the
  -- identification with `A ⧸ J ^ (n + 1)` is the quotient map.
  have h : (globalSectionsIso hJ).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n.unop + 1))) =
      (quotientProjection hJ n.unop).hom.app (op ⊤) ≫
        (quotientSheafGlobalSectionsIso (is_ideal_adic_pow hJ n.unop.succ_pos)).hom := by
    rw [← cancel_epi (globalSectionsIso hJ).inv, Iso.inv_hom_id_assoc,
      globalSectionsIso_inv_comp_quotientProjection_assoc, Iso.inv_hom_id, Category.comp_id]
  -- The goal composes through the apex `(Ideal.quotientPowSuccCone J).pt`, which is
  -- `CommRingCat.of A` only by unfolding: `@[simps]` gives `_pt_carrier` but no `_pt` lemma, so
  -- rewriting with `Ideal.quotientPowSuccCone_π_app` leaves an ill-typed goal. Restate it.
  change _ ≫ CommRingCat.ofHom (Ideal.Quotient.mk _) =
    𝟙 (CommRingCat.of A) ≫ CommRingCat.ofHom (Ideal.Quotient.mk _)
  rw [Category.assoc, Category.assoc, h, Category.id_comp, ← NatTrans.comp_app_assoc,
    ← ObjectProperty.FullSubcategory.comp_hom, structureSheafIso_hom_comp_quotientProjection,
    globalSectionsIso_inv_comp_toQuotientSheaf_assoc, Iso.inv_hom_id, Category.comp_id]

end TauCeti.FormalScheme.Spf

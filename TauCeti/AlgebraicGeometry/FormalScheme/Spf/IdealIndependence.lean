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

The comparison goes through the thickenings defined by arbitrary ideals of definition. For any
ideal of definition `K`, some power `I ^ (n + 1)` lies in `K`, and composing the projection
`O_{Spf A} → O_{I ^ (n + 1)}` with the reduction map `O_{I ^ (n + 1)} → O_K` gives a projection
`O_{Spf A} → O_K`, independent of `n`. This is the sheaf map of the closed immersion
`Spec (A ⧸ K) → Spf A` (EGA I, Ch. I, 10.3.2). The structure sheaf built from `J` is the limit
of the `O_{J ^ (n + 1)}`, so the projections of `O_{Spf_I A}` to these thickenings induce a map
`O_{Spf_I A} → O_{Spf_J A}`. Its inverse comes from the same construction with `I` and `J`
exchanged, since the powers of either ideal are cofinal among the powers of the other
(EGA I, Ch. 0, 7.1.9).

## Main definitions

* `TauCeti.FormalScheme.Spf.toQuotientSheaf`: for ideals of definition `I` and `K`, the
  projection `O_{Spf A} → O_K` from the structure sheaf built from `I`.
* `TauCeti.FormalScheme.Spf.structureSheafIso`: for ideals of definition `I` and `J`, the
  canonical isomorphism between the structure sheaves of `Spf A` built from `I` and from `J`.

## Main results

* `TauCeti.FormalScheme.Spf.toQuotientSheaf_eq`: the projection to `O_K` factors through the
  projection to `O_{I ^ (n + 1)}` for every `n` with `I ^ (n + 1) ≤ K`.
* `TauCeti.FormalScheme.Spf.toQuotientSheaf_comp_quotientTransition`: the projections are
  compatible with the reduction maps.
* `TauCeti.FormalScheme.Spf.globalSectionsIso_inv_comp_toQuotientSheaf`: the global section
  corresponding to `a ∈ A` projects to the class of `a` in `A ⧸ K`.
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
  and Ch. I, §10.1 (10.1.1–10.1.3) and §10.3 (10.3.2).
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY).
-/

public section

universe u

open CategoryTheory Opposite

namespace TauCeti.FormalScheme.Spf

variable {A : Type u} [CommRing A] [TopologicalSpace A] {I J K L : Ideal A}

variable [IsTopologicalRing A]

/-- For ideals of definition `I` and `K`, the projection `O_{Spf A} → O_K` from the structure
sheaf built from `I` to the structure sheaf of the thickening `Spec (A ⧸ K)`: the projection to
`O_{I ^ (n + 1)}` followed by the reduction map, for any `n` with `I ^ (n + 1) ≤ K`
(`toQuotientSheaf_eq`). It is the sheaf map of the closed immersion `Spec (A ⧸ K) → Spf A`. -/
noncomputable def toQuotientSheaf (hI : IsAdic I) (hK : IsAdic K) :
    structureSheaf hI ⟶ quotientSheaf hK :=
  quotientProjection hI (hI.exists_pow_succ_le hK).choose ≫
    quotientTransition _ hK (hI.exists_pow_succ_le hK).choose_spec

/-- The two-step composites `O_{Spf A} → O_{I ^ (n + 1)} → O_K` agree for all admissible `n`. -/
private theorem quotientProjection_comp_quotientTransition_eq (hI : IsAdic I) (hK : IsAdic K)
    {m n : ℕ} (hm : I ^ (m + 1) ≤ K) (hn : I ^ (n + 1) ≤ K) :
    quotientProjection hI m ≫ quotientTransition _ hK hm =
      quotientProjection hI n ≫ quotientTransition _ hK hn := by
  wlog hmn : m ≤ n generalizing m n
  · exact (this hn hm (le_of_not_ge hmn)).symm
  rw [← quotientProjection_comp_quotientTransition hI hmn, Category.assoc,
    quotientTransition_comp]

/-- The projection to `O_K` is the projection to `O_{I ^ (n + 1)}` followed by the reduction map,
for every `n` with `I ^ (n + 1) ≤ K`. -/
theorem toQuotientSheaf_eq (hI : IsAdic I) (hK : IsAdic K) {n : ℕ} (hn : I ^ (n + 1) ≤ K) :
    toQuotientSheaf hI hK = quotientProjection hI n ≫ quotientTransition _ hK hn :=
  quotientProjection_comp_quotientTransition_eq hI hK _ hn

/-- The projection to the thickening `O_{I ^ (n + 1)}` is `quotientProjection`. -/
@[simp]
theorem toQuotientSheaf_pow_succ (hI : IsAdic I) (n : ℕ) :
    toQuotientSheaf hI (is_ideal_adic_pow hI n.succ_pos) = quotientProjection hI n := by
  rw [toQuotientSheaf_eq hI _ le_rfl, quotientTransition_self, Category.comp_id]

/-- The projections to the thickenings are compatible with the reduction maps `O_K → O_L`. -/
@[reassoc (attr := simp)]
theorem toQuotientSheaf_comp_quotientTransition (hI : IsAdic I) (hK : IsAdic K) (hL : IsAdic L)
    (hKL : K ≤ L) :
    toQuotientSheaf hI hK ≫ quotientTransition hK hL hKL = toQuotientSheaf hI hL := by
  obtain ⟨n, hn⟩ := hI.exists_pow_succ_le hK
  rw [toQuotientSheaf_eq hI hK hn, toQuotientSheaf_eq hI hL (hn.trans hKL), Category.assoc,
    quotientTransition_comp]

/-- The morphism `structureSheaf.lift` projects to every thickening `O_K` through the given
morphism to a thickening `O_{I ^ (n + 1)}` with `I ^ (n + 1) ≤ K`. -/
@[reassoc]
theorem structureSheaf.lift_toQuotientSheaf (hI : IsAdic I) (hK : IsAdic K)
    {F : Sheaf (Opens.grothendieckTopology (TopCat.of (carrier A))) CommRingCat}
    (f : ∀ n : ℕ, F ⟶ quotientSheaf (is_ideal_adic_pow hI n.succ_pos))
    (hf : ∀ {m n : ℕ} (h : m ≤ n),
      f n ≫ quotientTransition _ _ (Ideal.pow_le_pow_right (Nat.succ_le_succ h)) = f m)
    {n : ℕ} (hn : I ^ (n + 1) ≤ K) :
    structureSheaf.lift hI f hf ≫ toQuotientSheaf hI hK = f n ≫ quotientTransition _ hK hn := by
  rw [toQuotientSheaf_eq hI hK hn, structureSheaf.lift_quotientProjection_assoc]

/-- The global section of the structure sheaf of `Spf A` corresponding to `a ∈ A` projects to the
class of `a` in the global sections `A ⧸ K` of the thickening `O_K`. -/
@[reassoc (attr := simp)]
theorem globalSectionsIso_inv_comp_toQuotientSheaf [IsAdicComplete I A] (hI : IsAdic I)
    (hK : IsAdic K) :
    (globalSectionsIso hI).inv ≫ (toQuotientSheaf hI hK).hom.app (op ⊤) =
      CommRingCat.ofHom (Ideal.Quotient.mk K) ≫ (quotientSheafGlobalSectionsIso hK).inv := by
  obtain ⟨n, hn⟩ := hI.exists_pow_succ_le hK
  rw [toQuotientSheaf_eq hI hK hn, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    globalSectionsIso_inv_comp_quotientProjection_assoc,
    quotientSheafGlobalSectionsIso_inv_comp_quotientTransition, ← Category.assoc,
    ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]

/-- The comparison map `O_{Spf_I A} → O_{Spf_J A}` induced by the projections of the structure
sheaf built from `I` to the thickenings `O_{J ^ (n + 1)}`. -/
private noncomputable def structureSheafHom (hI : IsAdic I) (hJ : IsAdic J) :
    structureSheaf hI ⟶ structureSheaf hJ :=
  structureSheaf.lift hJ (fun _ ↦ toQuotientSheaf hI _) fun _ ↦
    toQuotientSheaf_comp_quotientTransition _ _ _ _

private theorem structureSheafHom_comp_toQuotientSheaf (hI : IsAdic I) (hJ : IsAdic J)
    (hK : IsAdic K) :
    structureSheafHom hI hJ ≫ toQuotientSheaf hJ hK = toQuotientSheaf hI hK := by
  obtain ⟨n, hn⟩ := hJ.exists_pow_succ_le hK
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
  -- The apex of `Ideal.quotientPowSuccCone J` is `CommRingCat.of A` only after unfolding the cone,
  -- so the composites are restated with their projections as the quotient maps.
  change _ ≫ CommRingCat.ofHom (Ideal.Quotient.mk _) =
    𝟙 (CommRingCat.of A) ≫ CommRingCat.ofHom (Ideal.Quotient.mk _)
  rw [Category.assoc, Category.assoc, h, Category.id_comp, ← NatTrans.comp_app_assoc,
    ← ObjectProperty.FullSubcategory.comp_hom, structureSheafIso_hom_comp_quotientProjection,
    globalSectionsIso_inv_comp_toQuotientSheaf_assoc, Iso.inv_hom_id, Category.comp_id]

end TauCeti.FormalScheme.Spf

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Pushout.Basic

/-!
# Quotients of affinoid pushouts

Let `B = A⟨X⟩ / I`, `C = A⟨Y⟩ / J`, and `P = A⟨X,Y⟩ / (I,J)`.
For ideals `L ⊆ B` and `M ⊆ C`, the pushout of the quotient factors is

`P / (L P + M P) ≃ A⟨X,Y⟩ / (preimage L, preimage M)`.

The comparison preserves both structure maps and is a homeomorphism for the quotient
topologies. In particular, taking quotients of the factors induces a surjection of affinoid
pushouts, with kernel exactly the sum of the extended ideals. Nilpotents are retained;
no radical is taken. The construction is valid for restricted-series presentations over
any complete ultrametric normed commutative ring, without a coefficient field.

We use Mathlib's third isomorphism theorem rather than constructing new quotient maps.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.1.1.
-/

public section

namespace TauCeti.AffinoidPushout

open _root_.MvPowerSeries TauCeti.MvPowerSeries

variable {A : Type*} [NormedCommRing A] [IsUltrametricDist A] [CompleteSpace A] {m n : ℕ}
  (I : Ideal (IsRestricted.subring (R := A) (fun _ : Fin m ↦ 1)))
  (J : Ideal (IsRestricted.subring (R := A) (fun _ : Fin n ↦ 1)))
  (L : Ideal (IsRestricted.subring (R := A) (fun _ : Fin m ↦ 1) ⧸ I))
  (M : Ideal (IsRestricted.subring (R := A) (fun _ : Fin n ↦ 1) ⧸ J))

/-- The relations defining quotient factors extend to the sum of their images in the pushout. -/
theorem map_pushoutIdeal_comap_quotient :
    (pushoutIdeal (L.comap (Ideal.Quotient.mkₐ A I)) (M.comap (Ideal.Quotient.mkₐ A J))).map
        (Ideal.Quotient.mkₐ A (pushoutIdeal I J)) =
      L.map (inl I J) ⊔ M.map (inr I J) := by
  have hl : (Ideal.Quotient.mkₐ A (pushoutIdeal I J)).comp
      (restrictedRename (Fin.castAdd n)) = (inl I J).comp (Ideal.Quotient.mkₐ A I) := by
    ext f
    simp
  have hr : (Ideal.Quotient.mkₐ A (pushoutIdeal I J)).comp
      (restrictedRename (Fin.natAdd m)) = (inr I J).comp (Ideal.Quotient.mkₐ A J) := by
    ext f
    simp
  simp only [pushoutIdeal_def, Ideal.map_sup, Ideal.map_mapₐ]
  rw [hl, hr]
  simp only [← Ideal.map_mapₐ,
    Ideal.map_comap_of_surjective (Ideal.Quotient.mkₐ A I) (Ideal.Quotient.mkₐ_surjective A I),
    Ideal.map_comap_of_surjective (Ideal.Quotient.mkₐ A J) (Ideal.Quotient.mkₐ_surjective A J)]

/-- Quotienting the factors of an affinoid pushout is the same as quotienting the pushout
by the sum of the extended ideals. The target is the restricted-series presentation of the
pushout of `B / L` and `C / M`. -/
noncomputable def quotientEquiv :
    (AffinoidPushout I J ⧸ (L.map (inl I J) ⊔ M.map (inr I J))) ≃ₐ[A]
      AffinoidPushout (L.comap (Ideal.Quotient.mkₐ A I)) (M.comap (Ideal.Quotient.mkₐ A J)) :=
  (Ideal.quotientEquivAlgOfEq A (map_pushoutIdeal_comap_quotient I J L M).symm).trans
    (DoubleQuot.quotQuotEquivQuotOfLEₐ A (pushoutIdeal_mono
      (I.mk_ker.symm.trans_le (Ideal.ker_le_comap _))
      (J.mk_ker.symm.trans_le (Ideal.ker_le_comap _))))

/-- The comparison sends the class of a restricted series to its class in the new presentation. -/
@[simp]
theorem quotientEquiv_mk_mk
    (f : IsRestricted.subring (R := A) (fun _ : Fin (m + n) ↦ 1)) :
    quotientEquiv I J L M (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ f)) =
      Ideal.Quotient.mk _ f := by
  simp only [quotientEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    DoubleQuot.coe_quotQuotEquivQuotOfLEₐ]
  exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk f _

/-- The inverse comparison sends a series class to its iterated quotient class. -/
@[simp]
theorem quotientEquiv_symm_mk
    (f : IsRestricted.subring (R := A) (fun _ : Fin (m + n) ↦ 1)) :
    (quotientEquiv I J L M).symm (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk _ f) := by
  apply (quotientEquiv I J L M).injective
  simp

/-- The quotient comparison commutes with the left structure map. -/
@[simp]
theorem quotientEquiv_mk_inl (x : IsRestricted.subring (R := A) (fun _ : Fin m ↦ 1) ⧸ I) :
    quotientEquiv I J L M (Ideal.Quotient.mk _ (inl I J x)) =
      inl (L.comap (Ideal.Quotient.mkₐ A I)) (M.comap (Ideal.Quotient.mkₐ A J))
        (Ideal.Quotient.factorₐ A (I.mk_ker.symm.trans_le (Ideal.ker_le_comap _)) x) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [inl_mk, quotientEquiv_mk_mk]
  exact (inl_mk _ _ f).symm

/-- The quotient comparison commutes with the right structure map. -/
@[simp]
theorem quotientEquiv_mk_inr (y : IsRestricted.subring (R := A) (fun _ : Fin n ↦ 1) ⧸ J) :
    quotientEquiv I J L M (Ideal.Quotient.mk _ (inr I J y)) =
      inr (L.comap (Ideal.Quotient.mkₐ A I)) (M.comap (Ideal.Quotient.mkₐ A J))
        (Ideal.Quotient.factorₐ A (J.mk_ker.symm.trans_le (Ideal.ker_le_comap _)) y) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [inr_mk, quotientEquiv_mk_mk]
  exact (inr_mk _ _ f).symm

/-- The quotient comparison is continuous for the quotient topologies. -/
theorem continuous_quotientEquiv : Continuous (quotientEquiv I J L M) := by
  apply (QuotientRing.isOpenQuotientMap_mk _).isQuotientMap.continuous_iff.mpr
  apply (QuotientRing.isOpenQuotientMap_mk _).isQuotientMap.continuous_iff.mpr
  simpa only [Function.comp_def, quotientEquiv_mk_mk] using
    (QuotientRing.isOpenQuotientMap_mk
      (pushoutIdeal (L.comap (Ideal.Quotient.mkₐ A I))
        (M.comap (Ideal.Quotient.mkₐ A J)))).continuous

/-- The inverse quotient comparison is continuous for the quotient topologies. -/
theorem continuous_quotientEquiv_symm : Continuous (quotientEquiv I J L M).symm := by
  apply (QuotientRing.isOpenQuotientMap_mk _).isQuotientMap.continuous_iff.mpr
  simpa only [Function.comp_def, quotientEquiv_symm_mk] using
    (QuotientRing.isOpenQuotientMap_mk (L.map (inl I J) ⊔ M.map (inr I J))).continuous.comp
      (QuotientRing.isOpenQuotientMap_mk (pushoutIdeal I J)).continuous

/-- The algebraic quotient comparison also identifies the quotient topologies. -/
theorem isHomeomorph_quotientEquiv : IsHomeomorph (quotientEquiv I J L M) :=
  ({ toEquiv := (quotientEquiv I J L M).toEquiv
     continuous_toFun := continuous_quotientEquiv I J L M
     continuous_invFun := continuous_quotientEquiv_symm I J L M } : _ ≃ₜ _).isHomeomorph

end TauCeti.AffinoidPushout

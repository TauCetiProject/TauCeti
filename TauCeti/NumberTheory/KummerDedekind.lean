/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.KummerDedekind
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Inertia degrees and ramification indices along the Kummer–Dedekind correspondence

Let `S` be a Dedekind domain that is a torsion-free algebra over an integrally closed domain `R`,
let `x : S` be integral over `R`, and let `I` be a nonzero maximal ideal of `R` coprime to the
conductor of `R[x]`. Mathlib's Kummer–Dedekind theorem
(`KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk`) is a bijection between the
prime factors of `I S` and the monic irreducible factors of `minpoly R x` modulo `I`. This file
identifies the invariants of a prime `J` above `I` with those of its factor `Q`:

* the inertia degree of `J` is the degree of `Q`, because `S / J` is isomorphic over `R / I` to
  `(R / I)[X] / (Q)`;
* the ramification index of `J` is the multiplicity of `Q` in `minpoly R x` modulo `I`, the
  `ramificationIdx` form of Mathlib's `emultiplicity_factors_map_eq_emultiplicity`.

These generalise the statements Mathlib proves for the ring of integers of a number field over
`ℤ` (`NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply` and
`NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply`).

## Main results

* `KummerDedekind.inertiaDeg_normalizedFactorsMapEquivNormalizedFactorsMinPolyMk`: the inertia
  degree of a prime factor of `I S` is the degree of the corresponding factor of `minpoly R x`
  modulo `I` (with `…_symm_apply` the form for the prime attached to a lift of a factor).
* `KummerDedekind.ramificationIdx_normalizedFactorsMapEquivNormalizedFactorsMinPolyMk`: its
  ramification index is the multiplicity of that factor.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, Proposition (8.3).
-/

public section

open Ideal Polynomial UniqueFactorizationMonoid Algebra

namespace KummerDedekind

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {x : S} {I : Ideal R}
variable [IsDomain R] [IsIntegrallyClosed R] [IsDedekindDomain S] [Module.IsTorsionFree R S]

attribute [local instance] Ideal.Quotient.field

omit [IsIntegrallyClosed R] in
/-- A prime factor of `I S` is a prime of `S` lying over `I`. -/
private theorem mem_primesOver_of_mem_normalizedFactors (hI : I.IsMaximal) (hI' : I ≠ ⊥)
    {J : Ideal S} (hJ : J ∈ normalizedFactors (I.map (algebraMap R S))) : J ∈ I.primesOver S :=
  (mem_primesOver_iff_mem_normalizedFactors S hI').mpr hJ

/-- **The ramification index along the Kummer–Dedekind correspondence.** The ramification index
of a prime factor `J` of `I S` is the multiplicity, in `minpoly R x` modulo `I`, of the monic
irreducible factor corresponding to `J`. -/
theorem ramificationIdx_normalizedFactorsMapEquivNormalizedFactorsMinPolyMk (hI : I.IsMaximal)
    (hI' : I ≠ ⊥) (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x)
    {J : Ideal S} (hJ : J ∈ normalizedFactors (I.map (algebraMap R S))) :
    J.ramificationIdx R =
      multiplicity (normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx' ⟨J, hJ⟩).val
        ((minpoly R x).map (Ideal.Quotient.mk I)) := by
  have hmem := mem_primesOver_of_mem_normalizedFactors hI hI' hJ
  have : J.IsPrime := hmem.1
  have : J.LiesOver I := hmem.2
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity I J
    (by rwa [Ne, map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective R S)])]
  exact multiplicity_eq_of_emultiplicity_eq
    (emultiplicity_factors_map_eq_emultiplicity hI hI' hx hx' hJ)

open scoped Classical in
/-- For a lift `Q` of a monic irreducible factor of `minpoly R x` modulo `I`, the quotient
`(R / I)[X] / (Q mod I)` is isomorphic to `S / (I S + (Q(x)))`. This is the general form of
Mathlib's `ZModXQuotSpanEquivQuotSpanPair` for the ring of integers of a number field. -/
private noncomputable def quotSpanPairEquiv (hI : I.IsMaximal)
    (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x) {Q : R[X]}
    (hQ : Q.map (Ideal.Quotient.mk I) ∈
      normalizedFactors ((minpoly R x).map (Ideal.Quotient.mk I))) :
    (R ⧸ I)[X] ⧸ span {Q.map (Ideal.Quotient.mk I)} ≃+*
      S ⧸ (I.map (algebraMap R S) ⊔ span {aeval x Q}) :=
  have h₀ : (minpoly R x).map (Ideal.Quotient.mk I) ≠ 0 :=
    map_monic_ne_zero (minpoly.monic hx')
  have h_eq₁ : span {Q.map (Ideal.Quotient.mk I)} =
      span {(minpoly R x).map (Ideal.Quotient.mk I)} ⊔ span {Q.map (Ideal.Quotient.mk I)} := by
    rw [← span_insert, span_pair_comm, span_pair_eq_span_left_iff_dvd.mpr]
    exact ((Polynomial.mem_normalizedFactors_iff h₀).mp hQ).2.2
  ((Ideal.quotEquivOfEq h_eq₁).trans (DoubleQuot.quotQuotEquivQuotSup _ _).symm).trans <|
    (Ideal.quotientEquiv
      (Ideal.map (Ideal.Quotient.mk _) (span {Q.map (Ideal.Quotient.mk I)}))
      (Ideal.map (Ideal.Quotient.mk _) (span {aeval x Q}))
      (quotMapEquivQuotQuotMap hx hx').symm (by
        simp [Ideal.map_span, quotMapEquivQuotQuotMap_symm_apply])).trans <|
    DoubleQuot.quotQuotEquivQuotSup _ _

open scoped Classical in
/-- **The inertia degree along the Kummer–Dedekind correspondence**, for a lift `Q` of a monic
irreducible factor of `minpoly R x` modulo `I`: the prime of `S` corresponding to `Q mod I` has
inertia degree the degree of `Q mod I`. -/
theorem inertiaDeg_normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply
    (hI : I.IsMaximal) (hI' : I ≠ ⊥) (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
    (hx' : IsIntegral R x) {Q : R[X]}
    (hQ : Q.map (Ideal.Quotient.mk I) ∈
      normalizedFactors ((minpoly R x).map (Ideal.Quotient.mk I))) :
    ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm
      ⟨Q.map (Ideal.Quotient.mk I), hQ⟩ : Ideal S).inertiaDeg R =
        (Q.map (Ideal.Quotient.mk I)).natDegree := by
  set J : Ideal S := ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm
    ⟨Q.map (Ideal.Quotient.mk I), hQ⟩ : Ideal S) with hJdef
  have hJ : J ∈ normalizedFactors (I.map (algebraMap R S)) :=
    ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm
      ⟨Q.map (Ideal.Quotient.mk I), hQ⟩).prop
  have hJspan : J = I.map (algebraMap R S) ⊔ span {aeval x Q} := by
    rw [hJdef, normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span hI hQ hI'
      hx hx', span_union, span_eq]
  have hmem := mem_primesOver_of_mem_normalizedFactors hI hI' hJ
  have : J.IsPrime := hmem.1
  have : J.LiesOver I := hmem.2
  have : J.IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance (fun h => zero_notMem_normalizedFactors _ (h ▸ hJ))
  rw [Ideal.inertiaDeg_eq_of_isMaximal I J, ← finrank_quotient_span_eq_natDegree]
  refine Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl (R ⧸ I))
    ((Ideal.quotEquivOfEq hJspan).trans (quotSpanPairEquiv hI hx hx' hQ).symm) ?_
  ext r
  -- The Kummer–Dedekind isomorphism sends the class of `algebraMap R S r` to that of the constant
  -- `r mod I`, by `quotMapEquivQuotQuotMap_symm_apply` at `C r`.
  have hφ : quotMapEquivQuotQuotMap hx hx' (Ideal.Quotient.mk _ (algebraMap R S r)) =
      Ideal.Quotient.mk _ (C (Ideal.Quotient.mk I r)) := by
    rw [← RingEquiv.eq_symm_apply, ← Polynomial.map_C,
      quotMapEquivQuotQuotMap_symm_apply, aeval_C]
  have h₅ : DoubleQuot.quotQuotEquivQuotSup (span {(minpoly R x).map (Ideal.Quotient.mk I)})
      (span {Q.map (Ideal.Quotient.mk I)})
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (C (Ideal.Quotient.mk I r)))) =
        Ideal.Quotient.mk _ (C (Ideal.Quotient.mk I r)) :=
    DoubleQuot.quotQuotEquivQuotSup_quotQuotMk _ _ _
  -- The structure map `R / I → S / J` sends the class of `r` to the class of its image in `S`.
  have hSJ : algebraMap (R ⧸ I) (S ⧸ J) (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk J (algebraMap R S r) :=
    Ideal.Quotient.algebraMap_mk_of_liesOver J I r
  -- Unfold the composite isomorphism and push the class of `r` through it.
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.refl_apply, quotSpanPairEquiv, RingEquiv.symm_trans_apply, RingEquiv.trans_apply,
    RingEquiv.symm_symm]
  rw [← Ideal.Quotient.mk_algebraMap (R ⧸ I) (span {Q.map (Ideal.Quotient.mk I)})
    (Ideal.Quotient.mk I r)]
  rw [Polynomial.algebraMap_eq]
  rw [hSJ]
  rw [Ideal.quotEquivOfEq_mk]
  rw [DoubleQuot.quotQuotEquivQuotSup_symm_quotQuotMk]
  rw [DoubleQuot.quotQuotMk]
  rw [RingHom.comp_apply]
  rw [Ideal.quotientEquiv_symm_mk]
  rw [RingEquiv.symm_symm]
  rw [hφ]
  rw [h₅]
  rw [RingEquiv.eq_symm_apply]
  rw [Ideal.quotEquivOfEq_mk]

open scoped Classical in
/-- **The inertia degree along the Kummer–Dedekind correspondence.** The inertia degree of a
prime factor `J` of `I S` is the degree of the monic irreducible factor of `minpoly R x` modulo
`I` corresponding to `J`. -/
theorem inertiaDeg_normalizedFactorsMapEquivNormalizedFactorsMinPolyMk (hI : I.IsMaximal)
    (hI' : I ≠ ⊥) (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x)
    {J : Ideal S} (hJ : J ∈ normalizedFactors (I.map (algebraMap R S))) :
    J.inertiaDeg R =
      (normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx'
        ⟨J, hJ⟩).val.natDegree := by
  set e := normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx' with he
  -- Lift the factor corresponding to `J` to `R[X]` and identify `J` with the prime attached to
  -- that lift.
  obtain ⟨Q, hQ⟩ := Polynomial.map_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    (e ⟨J, hJ⟩).val
  have hQmem : Q.map (Ideal.Quotient.mk I) ∈
      normalizedFactors ((minpoly R x).map (Ideal.Quotient.mk I)) := hQ ▸ (e ⟨J, hJ⟩).prop
  have hJ' : (e.symm ⟨Q.map (Ideal.Quotient.mk I), hQmem⟩ : Ideal S) = J := by
    rw [show (⟨Q.map (Ideal.Quotient.mk I), hQmem⟩ : {d // d ∈
      normalizedFactors ((minpoly R x).map (Ideal.Quotient.mk I))}) = e ⟨J, hJ⟩ from
      Subtype.ext hQ, Equiv.symm_apply_apply]
  rw [← hQ, ← hJ']
  exact inertiaDeg_normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply hI hI' hx hx'
    hQmem

end KummerDedekind

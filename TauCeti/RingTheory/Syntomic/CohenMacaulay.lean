/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Syntomic.StandardSyntomic
public import TauCeti.RingTheory.CohenMacaulay.Quotient
public import TauCeti.RingTheory.CohenMacaulay.Localization
import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay
import TauCeti.RingTheory.KrullDimension.Presentation
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Cohen–Macaulay local rings of standard syntomic algebras over fields

A global complete intersection over a field has Cohen–Macaulay local rings. At a closed point,
localize its polynomial presentation: the ambient regular local ring has dimension the number
of variables, and the quotient has dimension the number of variables minus the number of
relations. The equations therefore form a regular sequence. Localization gives the assertion
at arbitrary primes.

This supplies the fibrewise Cohen–Macaulay input for duality of syntomic curves, in particular
nodal curves. No reducedness or smoothness of the complete intersection is assumed.

## References

* The Stacks Project, Section 10.135, *Local complete intersections* (Tag 00S8).
* The Stacks Project, Proposition 10.103.4 (Tag 00N6).
-/

public section

open IsLocalRing
open scoped TensorProduct

namespace Algebra.Presentation

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
variable {ι σ : Type*} [Finite ι] [Finite σ] (P : Presentation k A ι σ)

/-- The local ring at a closed point of a global complete intersection over a field is
Cohen–Macaulay. The dimension condition is an upper bound: the opposite inequality follows
from Krull's height theorem. -/
theorem isCohenMacaulay_localization_atMaximal (hcard : Nat.card σ ≤ Nat.card ι)
    (hdim : ringKrullDim A ≤ P.dimension) (m : Ideal A) [m.IsMaximal] :
    Module.IsCohenMacaulay (Localization.AtPrime m) (Localization.AtPrime m) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype σ := Fintype.ofFinite σ
  have := P.finitePresentation_of_isFinite
  let q := m.comap (algebraMap P.Ring A)
  have : q.IsMaximal := Ideal.comap_isMaximal_of_surjective _ P.algebraMap_surjective
  let Q := Localization.AtPrime q
  let B := Localization.AtPrime m
  have hT : q.primeCompl.map (algebraMap P.Ring A) = m.primeCompl :=
    Ideal.map_primeCompl_comap_of_surjective _ P.algebraMap_surjective m
  have : IsLocalization (q.primeCompl.map (algebraMap P.Ring A)) B := by
    rw [hT]
    infer_instance
  let φ : Q →+* B := IsLocalization.map B (algebraMap P.Ring A)
    (hT.symm ▸ q.primeCompl.le_comap_map)
  let : Algebra Q B := φ.toAlgebra
  have hφ : algebraMap Q B = φ := (rfl)
  have hsurj : Function.Surjective (algebraMap Q B) :=
    IsLocalization.map_surjective_of_surjective _ _ _ P.algebraMap_surjective
  let rs : List Q := Finset.univ.toList.map (algebraMap P.Ring Q ∘ P.relation)
  have hrels : RingHom.ker (algebraMap P.Ring A) = Ideal.span (Set.range P.relation) :=
    P.span_range_relation_eq_ker.symm
  have hker : RingHom.ker (algebraMap Q B) = Ideal.ofList rs := by
    rw [hφ, IsLocalization.ker_map (S := Q) B (algebraMap P.Ring A) hT,
      hrels, Ideal.map_span]
    congr 1
    ext x
    simp [rs]
  have hB : ringKrullDim B = P.dimension := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height m B]
    exact le_antisymm (Ideal.height_le_ringKrullDim_of_isPrime.trans hdim)
      (WithBot.coe_le_coe.mpr (P.dimension_le_height_of_isMaximal m))
  have hQ : ringKrullDim Q = Nat.card ι := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q Q,
      MvPolynomial.height_eq_natCard_of_isMaximal]
    rfl
  apply Module.IsCohenMacaulay.of_surjective_of_ringKrullDim_add_length_eq
    TauCeti.IsRegularLocalRing.isCohenMacaulay hsurj rs hker
  rw [hB, hQ]
  simp only [rs, List.length_map, Finset.length_toList, Finset.card_univ,
    ← Nat.card_eq_fintype_card, dimension]
  norm_cast
  omega

/-- Every local ring of a global complete intersection over a field is Cohen–Macaulay. -/
theorem isCohenMacaulay_localization (hcard : Nat.card σ ≤ Nat.card ι)
    (hdim : ringKrullDim A ≤ P.dimension) (p : Ideal A) [p.IsPrime] :
    Module.IsCohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p) := by
  have := P.finitePresentation_of_isFinite
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p (Ideal.IsPrime.ne_top inferInstance)
  have : m.IsMaximal := hm
  let B := Localization.AtPrime m
  let q := p.map (algebraMap A B)
  have : q.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime m hpm
  have hq : q.comap (algebraMap A B) = p :=
    Ideal.under_map_of_isLocalizationAtPrime m hpm
  have hB := P.isCohenMacaulay_localization_atMaximal hcard hdim m
  have : IsLocalization.AtPrime (Localization.AtPrime q) p := by
    have hloc : IsLocalization.AtPrime (Localization.AtPrime q)
        (q.comap (algebraMap A B)) := inferInstance
    simpa only [hq] using hloc
  exact (IsLocalization.AtPrime.isCohenMacaulay_self_iff p (Localization.AtPrime q)).1
    (hB.localization_atPrime q)

end Algebra.Presentation

namespace TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] {n : ℕ}
    [hA : IsStandardSyntomicOfRelativeDimension n k A]

include hA in
/-- Standard syntomic algebras over a field have Cohen–Macaulay local rings, without a
reducedness assumption. In particular this applies to the algebras of affine charts of
syntomic fibres. -/
theorem isCohenMacaulay_localization (p : Ideal A) [p.IsPrime] :
    Module.IsCohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p) := by
  classical
  obtain ⟨ι, σ, _, _, P, hP⟩ := hA.exists_presentation
  have hdim : P.dimension = n := by
    rw [_root_.Algebra.Presentation.dimension, hP, Nat.add_sub_cancel]
  apply P.isCohenMacaulay_localization (by omega)
  rw [hdim]
  cases subsingleton_or_nontrivial A with
  | inl _ => simp [ringKrullDim_eq_bot_of_subsingleton]
  | inr _ =>
    let e := _root_.Algebra.TensorProduct.lid k A
    have : Nontrivial (k ⊗[k] A) := e.toEquiv.nontrivial
    rw [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv,
      hA.ringKrullDim_tensorProduct_of_field k]

end TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension

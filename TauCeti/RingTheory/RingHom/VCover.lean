/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing

import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import TauCeti.RingTheory.Spectrum.Prime.TensorProduct
import TauCeti.RingTheory.TensorProduct.Maps
import TauCeti.RingTheory.Valuation.ValuationSubring

/-!
# v-covers of rings

A ring homomorphism `f : A →+* B` is a *v-cover* when every homomorphism `A →+* V` to a
valuation domain lifts along `f` after an injective local homomorphism `V →+* W` to another
valuation domain. On spectra this is the v-cover condition of Bhatt–Scholze and Rydh for
`Spec B → Spec A`; the test rings live in the universe of `A` and `B`, and their rank is
unrestricted.

The lifting problem for a single test map `φ : A →+* V` is governed by the prime spectrum of
`V ⊗[A] B`: a lift exists exactly when some prime of `V ⊗[A] B` lying over the generic point of
`Spec V` specializes to a prime lying over its closed point. The construction behind this,
`TauCeti.exists_valuationRing_of_isPrime_le`, is general: in any algebra `T` over a local ring
`V`, such a pair of primes `P ≤ Q` yields a valuation domain `W` and a map `T →+* W` whose
restriction to `V` is injective and local; `W` is a valuation subring of the fraction field of
`T ⧸ P` with the image of `Q` among its nonunits.

Since flat ring maps have going down, faithfully flat ring homomorphisms are v-covers; since
integral ring maps have going up, so are integral ring homomorphisms surjective on spectra.

## Main definitions

* `RingHom.IsVCover`: the valuative lifting property of a ring homomorphism.

## Main results

* `RingHom.IsVCover.id`, `RingHom.IsVCover.comp`, `RingHom.IsVCover.of_comp`: identities are
  v-covers, v-covers compose, and a map through which a v-cover factors is one.
* `RingHom.IsVCover.of_comp_eq_id`, `RingHom.IsVCover.of_bijective`: a homomorphism with a
  retraction, in particular a bijective one, is a v-cover.
* `RingHom.IsVCover.respectsIso`, `RingHom.IsVCover.isStableUnderBaseChange`: v-covers respect
  isomorphisms and are stable under base change.
* `RingHom.IsVCover.comap_surjective`: a v-cover is surjective on prime spectra.
* `RingHom.IsVCover.pi_of_span_eq_top`: a covering by basic opens is a v-cover.
* `TauCeti.exists_lift_iff_exists_isPrime_le`: a single test map `A →+* V` lifts if and only if
  the prime spectrum of `V ⊗[A] B` contains such a pair.
* `RingHom.isVCover_iff_exists_isPrime_le`: `f` is a v-cover if and only if, for every test map
  `A →+* V`, the prime spectrum of `V ⊗[A] B` contains such a pair.
* `RingHom.IsVCover.of_faithfullyFlat`: faithfully flat ring homomorphisms are v-covers.
* `RingHom.IsVCover.of_isIntegral_of_comap_surjective`: integral ring homomorphisms that are
  surjective on prime spectra are v-covers, the affine case of proper surjections.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*, Invent. Math.
  209 (2017), Definition 2.1 and Remark 2.2.
* D. Rydh, *Submersions and effective descent of étale morphisms*, Bull. Soc. Math. France 138
  (2010), Definition 2.2 and Theorem 2.8.
* B. Bhatt and A. Mathew, *The arc-topology*, Forum Math. Pi 9 (2021), Definition 1.1 and
  Lemma 2.3.
-/

public section

universe u

open IsLocalRing TensorProduct

namespace TauCeti

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Let `V` be a valuation domain and `B` an algebra over `A`, with `A →+* V` the structure map.
It lifts along `A →+* B` after an injective local homomorphism `V →+* W` to a valuation domain
if and only if there are primes `P ≤ Q` of `V ⊗[A] B` lying over the zero ideal and over the
maximal ideal of `V`. -/
theorem exists_lift_iff_exists_isPrime_le (V : Type u) [CommRing V] [IsDomain V]
    [ValuationRing V] [Algebra A V] [Algebra A B] :
    (∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : ValuationRing W) (e : V →+* W)
      (ψ : B →+* W), Function.Injective e ∧ IsLocalHom e ∧
        ψ.comp (algebraMap A B) = e.comp (algebraMap A V)) ↔
      ∃ P Q : Ideal (V ⊗[A] B), P.IsPrime ∧ Q.IsPrime ∧ P ≤ Q ∧
        P.comap (algebraMap V (V ⊗[A] B)) = ⊥ ∧
        Q.comap (algebraMap V (V ⊗[A] B)) = maximalIdeal V := by
  constructor
  · rintro ⟨W, _, _, _, e, ψ, he, he', hψ⟩
    let χ := Algebra.TensorProduct.liftRingHom e ψ hψ.symm
    have hχ : χ.comp (algebraMap V (V ⊗[A] B)) = e := by
      ext
      simp [χ]
    refine ⟨RingHom.ker χ, (maximalIdeal W).comap χ, RingHom.ker_isPrime χ, inferInstance,
      Ideal.comap_mono bot_le, ?_, ?_⟩
    · rw [RingHom.comap_ker, hχ, (RingHom.injective_iff_ker_eq_bot e).mp he]
    · rw [Ideal.comap_comap, hχ, maximalIdeal_comap]
  · rintro ⟨P, Q, _, _, hPQ, hP, hQ⟩
    obtain ⟨W, i₁, i₂, i₃, g, hg, hg'⟩ := exists_valuationRing_of_isPrime_le hPQ hP hQ
    refine ⟨W, i₁, i₂, i₃, g.comp (algebraMap V (V ⊗[A] B)),
      g.comp Algebra.TensorProduct.includeRight.toRingHom, hg, hg', ?_⟩
    ext a
    simp

end TauCeti

namespace RingHom

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-- A ring homomorphism `f : A →+* B` is a *v-cover* if every homomorphism `φ : A →+* V` to a
valuation domain `V` lifts along `f` after an injective local homomorphism `e : V →+* W` to a
valuation domain `W`: there is `ψ : B →+* W` with `ψ ∘ f = e ∘ φ`. The test rings live in the
universe of `A` and `B`. -/
def IsVCover (f : A →+* B) : Prop :=
  ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V] (φ : A →+* V),
    ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : ValuationRing W) (e : V →+* W)
      (ψ : B →+* W), Function.Injective e ∧ IsLocalHom e ∧ ψ.comp f = e.comp φ

/-- Unfolding `RingHom.IsVCover`. -/
theorem isVCover_iff (f : A →+* B) :
    f.IsVCover ↔
      ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V] (φ : A →+* V),
        ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : ValuationRing W) (e : V →+* W)
          (ψ : B →+* W), Function.Injective e ∧ IsLocalHom e ∧ ψ.comp f = e.comp φ :=
  Iff.rfl

namespace IsVCover

/-- If every test homomorphism lifts along `f` without enlarging the valuation ring, then `f` is
a v-cover. -/
theorem of_forall_exists_comp_eq {f : A →+* B}
    (h : ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V] (φ : A →+* V),
      ∃ ψ : B →+* V, ψ.comp f = φ) :
    f.IsVCover := by
  intro V _ _ _ φ
  obtain ⟨ψ, hψ⟩ := h V φ
  exact ⟨V, ‹_›, ‹_›, ‹_›, RingHom.id V, ψ, Function.injective_id, inferInstance,
    by simpa using hψ⟩

/-- The identity is a v-cover. -/
protected theorem id : (RingHom.id A).IsVCover :=
  of_forall_exists_comp_eq fun _ _ _ _ φ => ⟨φ, rfl⟩

/-- v-covers compose. -/
protected theorem comp {f : A →+* B} {g : B →+* C} (hf : f.IsVCover) (hg : g.IsVCover) :
    (g.comp f).IsVCover := by
  intro V _ _ _ φ
  obtain ⟨W₁, _, _, _, e₁, ψ₁, he₁, _, hψ₁⟩ := hf V φ
  obtain ⟨W₂, i₁, i₂, i₃, e₂, ψ₂, he₂, _, hψ₂⟩ := hg W₁ ψ₁
  refine ⟨W₂, i₁, i₂, i₃, e₂.comp e₁, ψ₂, he₂.comp he₁, inferInstance, ?_⟩
  rw [← RingHom.comp_assoc, hψ₂, RingHom.comp_assoc, hψ₁, RingHom.comp_assoc]

/-- If a composite `g ∘ f` is a v-cover, then so is `f`. On spectra, if
`Spec C → Spec B → Spec A` is a v-cover then so is `Spec B → Spec A`. -/
theorem of_comp {f : A →+* B} {g : B →+* C} (h : (g.comp f).IsVCover) : f.IsVCover := by
  intro V _ _ _ φ
  obtain ⟨W, i₁, i₂, i₃, e, ψ, he, he', hψ⟩ := h V φ
  exact ⟨W, i₁, i₂, i₃, e, ψ.comp g, he, he', by rw [RingHom.comp_assoc, hψ]⟩

/-- A ring homomorphism with a retraction is a v-cover; on spectra, a morphism with a section is
a v-cover. -/
theorem of_comp_eq_id {f : A →+* B} (g : B →+* A) (h : g.comp f = RingHom.id A) :
    f.IsVCover :=
  of_comp (g := g) (h ▸ IsVCover.id)

/-- Bijective ring homomorphisms are v-covers. -/
theorem of_bijective {f : A →+* B} (hf : Function.Bijective f) : f.IsVCover :=
  of_comp_eq_id (RingEquiv.ofBijective f hf).symm.toRingHom
    (by ext x; simpa using (RingEquiv.ofBijective f hf).symm_apply_apply x)

/-- Identities are v-covers, in the form used by Mathlib's ring-homomorphism properties. -/
theorem containsIdentities : ContainsIdentities IsVCover := fun _ _ => IsVCover.id

/-- v-covers are stable under composition. -/
theorem stableUnderComposition : StableUnderComposition IsVCover := by
  introv R hf hg
  exact hf.comp hg

/-- v-covers respect ring isomorphisms of the source and target. -/
theorem respectsIso : RespectsIso IsVCover :=
  stableUnderComposition.respectsIso fun e => of_bijective e.bijective

/-- v-covers are stable under base change: if `R →+* T` is a v-cover, then so is
`S →+* S ⊗[R] T` for every `R`-algebra `S`. -/
theorem isStableUnderBaseChange : IsStableUnderBaseChange IsVCover := by
  refine IsStableUnderBaseChange.mk respectsIso ?_
  introv h
  intro V _ _ _ φ
  obtain ⟨W, i₁, i₂, i₃, e, ψ, he, he', hψ⟩ := h V (φ.comp (algebraMap R S))
  refine ⟨W, i₁, i₂, i₃, e, Algebra.TensorProduct.liftRingHom (e.comp φ) ψ hψ.symm, he, he', ?_⟩
  ext
  simp

/-- A v-cover is surjective on prime spectra. -/
theorem comap_surjective {f : A →+* B} (h : f.IsVCover) :
    Function.Surjective (PrimeSpectrum.comap f) := by
  intro p
  obtain ⟨W, _, _, _, e, ψ, he, _, hψ⟩ := h p.asIdeal.ResidueField (algebraMap A _)
  refine ⟨⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩, PrimeSpectrum.ext ?_⟩
  simp [RingHom.comap_ker, hψ, RingHom.ker_comp_of_injective _ he]

/-- A family of localizations `A →+* S i` away from elements `s i` generating the unit ideal
gives a v-cover `A →+* ∏ i, S i`; on spectra, a covering of `Spec A` by basic opens is a v-cover.
No enlargement of the valuation ring is needed. -/
theorem pi_of_span_eq_top {ι : Type u} (S : ι → Type u) [∀ i, CommRing (S i)]
    [∀ i, Algebra A (S i)] (s : ι → A) [∀ i, IsLocalization.Away (s i) (S i)]
    (hs : Ideal.span (Set.range s) = ⊤) :
    (RingHom.pi fun i => algebraMap A (S i)).IsVCover := by
  refine of_forall_exists_comp_eq fun V _ _ _ φ => ?_
  -- some `φ (s i)` is a unit: otherwise `φ` sends the unit ideal into the maximal ideal of `V`
  obtain ⟨i, hi⟩ : ∃ i, IsUnit (φ (s i)) := by
    by_contra! h
    have : Ideal.span (Set.range s) ≤ (maximalIdeal V).comap φ :=
      Ideal.span_le.mpr (Set.range_subset_iff.mpr fun i => h i)
    rw [hs, top_le_iff, Ideal.comap_eq_top_iff] at this
    exact (maximalIdeal.isMaximal V).ne_top this
  refine ⟨(IsLocalization.Away.lift (s i) hi).comp (Pi.evalRingHom S i), ?_⟩
  ext a
  simp

end IsVCover

/-- A ring homomorphism `f : A →+* B` is a v-cover if and only if, for every homomorphism
`φ : A →+* V` to a valuation domain, there are primes `P ≤ Q` of `V ⊗[A] B` lying over the zero
ideal and over the maximal ideal of `V`. On spectra: the specialization from the generic to the
closed point of `Spec V` lifts to the base change of `Spec B → Spec A` along `Spec V → Spec A`.
For a single test map with given algebra structures, see
`TauCeti.exists_lift_iff_exists_isPrime_le`. -/
theorem isVCover_iff_exists_isPrime_le (f : A →+* B) :
    f.IsVCover ↔ ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V] (φ : A →+* V),
      letI := φ.toAlgebra
      letI := f.toAlgebra
      ∃ P Q : Ideal (V ⊗[A] B), P.IsPrime ∧ Q.IsPrime ∧ P ≤ Q ∧
        P.comap (algebraMap V (V ⊗[A] B)) = ⊥ ∧
        Q.comap (algebraMap V (V ⊗[A] B)) = maximalIdeal V := by
  -- the structure maps of `φ.toAlgebra` and `f.toAlgebra` are `φ` and `f`
  refine forall_congr' fun V => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun φ => ?_
  let := φ.toAlgebra
  let := f.toAlgebra
  simpa only [RingHom.algebraMap_toAlgebra] using
    TauCeti.exists_lift_iff_exists_isPrime_le (A := A) (B := B) V

namespace IsVCover

/-- Faithfully flat ring homomorphisms are v-covers. -/
theorem of_faithfullyFlat {f : A →+* B} (hf : f.FaithfullyFlat) : f.IsVCover := by
  -- After base change to `V`, the closed point of `Spec V` lifts by faithful flatness, and the
  -- generic point lifts to a generization of that lift by going down for flat maps.
  rw [isVCover_iff_exists_isPrime_le]
  intro V _ _ _ φ
  let := φ.toAlgebra
  let := f.toAlgebra
  have : Module.FaithfullyFlat A B := RingHom.faithfullyFlat_algebraMap_iff.mp hf
  obtain ⟨Q, _, hQ⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := V ⊗[A] B)
    (maximalIdeal V)
  obtain ⟨P, hPQ, _, hP⟩ := Q.exists_ideal_le_liesOver_of_le (p := ⊥) (q := maximalIdeal V)
    bot_le
  exact ⟨P, Q, ‹_›, ‹_›, hPQ, hP.over.symm, hQ.over.symm⟩

/-- An integral ring homomorphism which is surjective on prime spectra is a v-cover. On spectra,
this is the affine case of the fact that proper surjections are v-covers. -/
theorem of_isIntegral_of_comap_surjective {f : A →+* B} (hf : f.IsIntegral)
    (hs : Function.Surjective (PrimeSpectrum.comap f)) : f.IsVCover := by
  -- After base change to `V`, the generic point of `Spec V` lifts because images of spectra
  -- commute with base change, and the closed point lifts to a specialization of that lift by
  -- going up for integral maps.
  rw [isVCover_iff_exists_isPrime_le]
  intro V _ _ _ φ
  let := φ.toAlgebra
  let := f.toAlgebra
  have : Algebra.IsIntegral A B := algebraMap_isIntegral_iff.mp hf
  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) ∈
      Set.range (PrimeSpectrum.comap (algebraMap V (V ⊗[A] B))) := by
    rw [PrimeSpectrum.range_comap_algebraMap_tensorProduct]
    exact hs _
  obtain ⟨P, hP⟩ := hgen
  have hP' : P.asIdeal.comap (algebraMap V (V ⊗[A] B)) = ⊥ := by
    simpa only [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hP
  obtain ⟨Q, hPQ, _, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime
    (maximalIdeal V) P.asIdeal (by rw [Ideal.under, hP']; exact bot_le)
  exact ⟨P.asIdeal, Q, inferInstance, ‹_›, hPQ, hP', hQ⟩

/-- An injective integral ring homomorphism is a v-cover. For instance, the inclusion of a
domain into its integral closure in a finite extension of its fraction field is a v-cover. -/
theorem of_isIntegral_of_injective {f : A →+* B} (hf : f.IsIntegral)
    (hinj : Function.Injective f) : f.IsVCover :=
  of_isIntegral_of_comap_surjective hf (hf.comap_surjective hinj)

end IsVCover

end RingHom

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Units.LocalPowerClass
public import TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension
public import TauCeti.RingTheory.Ideal.PrimesOver

import TauCeti.NumberTheory.ClassFieldTheory.Global.FrobeniusGeneration
import TauCeti.NumberTheory.NumberField.Frobenius.SplitBasis
import TauCeti.NumberTheory.NumberField.Kummer.Unramified

/-!
# Auxiliary places for the Kummer second inequality

Let `K` be a number field containing the `p`-th roots of unity, let `S` be a finite set of
finite places containing the places above the prime `p`, and put `M = K(U_S^{1/p})`. For every
intermediate field `L`, this file chooses a finite set `T` of auxiliary places with the four
properties needed in the counting step of the Kummer proof of the second fundamental inequality:

* `S` and `T` are disjoint;
* `p ^ #T = [M : L]`;
* the `S`-units surject onto the product of the local unit `p`-th power classes at `T`;
* every place in `T` has a place of `L` above it of local degree one.

The Frobenius elements outside `S` generate `Gal(M/L)` by the first fundamental inequality.
The Frobenius-basis theorem extracts `T`; its cardinality identity then makes the Kummer-theoretic
counting bound for local power classes an equality.

## Main result

* `TauCeti.ClassFieldTheory.exists_auxiliaryPlaces_unitLocalPowerClassMap_surjective`: the
  auxiliary set `T`, including its cardinality, local-power-class and local-degree properties.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §6, especially Lemma 6.9 and the
  proof of the second inequality.
-/

public noncomputable section

open IsDedekindDomain NumberField IntermediateField
open TauCeti.NumberField TauCeti.NumberFieldArithmetic
open scoped AdicCompletionExtension NumberField.LiesOver

namespace TauCeti.ClassFieldTheory

variable {K E : Type} [Field K] [NumberField K] [Field E] [Algebra K E]

/-- Every place of `K` has a prime of a number field extension `M` lying over it. -/
private theorem exists_isPrime_liesOver {M : Type} [Field M] [NumberField M] [Algebra K M]
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ Q : Ideal (𝓞 M), Q.IsPrime ∧ Q.LiesOver v.asIdeal := by
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 M) v.asIdeal
  exact ⟨Q, hQ.isPrime, hQv⟩

omit [NumberField K] in
/-- The `p`-th roots of the elements of `Δ` in `E` lie in the Kummer field `K(Δ^{1/p})`. -/
private theorem exists_pow_eq_kummerField {p : ℕ} {Δ : Subgroup Kˣ}
    (hroots : ∀ a ∈ Δ, ∃ x : E, x ^ p = algebraMap K E (a : K)) :
    ∀ a ∈ Δ, ∃ x : kummerField E p Δ, x ^ p = algebraMap K (kummerField E p Δ) (a : K) := by
  intro a ha
  obtain ⟨x, hx⟩ := hroots a ha
  exact ⟨⟨x, mem_kummerField_of_pow_eq ha hx⟩, Subtype.ext (by simpa using hx)⟩

/-- The Kummer field of the `S`-units is unramified at every place outside `S`, when `S`
contains the places above `p`. -/
private theorem isUnramifiedAt_kummerField_of_notMem {p : ℕ} [NeZero p]
    [HasEnoughRootsOfUnity K p] (S : Finset (HeightOneSpectrum (𝓞 K)))
    [(powMonoidHom p : Kˣ →* Kˣ).range.IsFiniteRelIndex
      ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)]
    (hpS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S)
    (Q : Ideal (𝓞 (kummerField E p ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))))
    [Q.IsPrime] [Q.LiesOver v.asIdeal] :
    Algebra.IsUnramifiedAt (𝓞 K) Q :=
  isUnramifiedAway_ramifiedSupport (K := K) (L := kummerField E p _) v
    (fun hvram ↦ hv (ramifiedSupport_kummerField_sUnits_subset S hpS hvram)) Q

/-- **Auxiliary places for the Kummer second inequality.** Let `p` be prime, let `S` contain all
finite places above `p`, and let `M = K(U_S^{1/p})` in an ambient field containing the required
radicals. For every intermediate field `L/K` in `M`, there is a finite set `T`, disjoint from
`S`, such that `p ^ #T = [M : L]`, the `S`-units surject onto the local unit `p`-th power
classes at `T`, and every place in `T` has a place of `L` above it of local degree one. -/
theorem exists_auxiliaryPlaces_unitLocalPowerClassMap_surjective
    {p : ℕ} (hp : p.Prime) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hpS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    (hroots : ∀ a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
      ∃ x : E, x ^ p = algebraMap K E (a : K))
    (L : IntermediateField K
      (kummerField E p ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))) [NumberField L] :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)),
      ∃ hST : Disjoint (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set _),
        p ^ T.card = Module.finrank L
            (kummerField E p ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) ∧
          Function.Surjective
            (Set.unitLocalPowerClassMap (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set _) hST p) ∧
          ∀ v ∈ T, ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
            Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1 := by
  classical
  let _ : NeZero p := ⟨hp.ne_zero⟩
  have hζK : IsPrimitiveRoot (algebraMap (𝓞 K) K ζ) p :=
    hζ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  let _ : HasEnoughRootsOfUnity K p := .of_card_le hζK.card_rootsOfUnity.ge
  let Δ := (S : Set (HeightOneSpectrum (𝓞 K))).unit K
  let M := kummerField E p Δ
  let _ : (powMonoidHom p : Kˣ →* Kˣ).range.IsFiniteRelIndex Δ :=
    ⟨by rw [relIndex_range_powMonoidHom_sUnits_numberField]; exact pow_ne_zero _ hp.ne_zero⟩
  have hur := isUnramifiedAt_kummerField_of_notMem (E := E) (p := p) S hpS
  have hab : ∀ σ τ : M ≃ₐ[K] M, Commute σ τ := fun σ τ ↦
    (commute_iff_eq σ τ).2 (IsMulCommutative.is_comm.comm σ τ)
  have hgen : Subgroup.closure {τ : M ≃ₐ[L] M | ∃ v ∉ S,
      ∃ Q : {Q : HeightOneSpectrum (𝓞 M) // Q.asIdeal.LiesOver v.asIdeal},
        IsArithFrobAt (𝓞 L) τ Q.1.asIdeal} = ⊤ :=
    closure_isArithFrobAt_eq_top_tower (K := K) (L := L) (M := M) S
  obtain ⟨T, hST, hclosure, hcard, hsplit⟩ :=
    exists_finset_closure_artinElementAway_eq_range_restrictScalarsHom hp
      exponent_algEquiv_kummerField_dvd hab S hur hgen
  have hST' : Disjoint (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set _) :=
    Finset.disjoint_coe.mpr hST
  choose Q hQprime hQover using fun v : T ↦ exists_isPrime_liesOver (K := K) (M := M) v.1
  let σ (v : T) : M ≃ₐ[K] M := artinElementAway hab S hur v.1
  have hσ (v : T) : IsArithFrobAt (𝓞 K) (σ v) (Q v) := by
    let _ : (Q v).IsPrime := hQprime v
    let _ : (Q v).LiesOver v.1.asIdeal := hQover v
    exact isArithFrobAt_artinElementAway hab S hur
      (fun hvS ↦ Set.disjoint_left.mp hST' hvS v.2) (Q v)
  have hfix : L.fixingSubgroup = Subgroup.closure (Set.range σ) := by
    rw [show Set.range σ = _ from (Set.image_eq_range (artinElementAway hab S hur) _).symm,
      hclosure, AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom,
      L.restrictNormalHom_ker]
  have havoid (v : T) : (p : 𝓞 K) ∉ v.1.asIdeal := fun hpv ↦
    Set.disjoint_left.mp hST' (hpS v.1 hpv) v.2
  have hrootsM := exists_pow_eq_kummerField hroots
  have hsurj : Function.Surjective
      (Set.unitLocalPowerClassMap (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set _) hST' p) := by
    let _ (v : T) : (Q v).IsPrime := hQprime v
    let _ (v : T) : (Q v).LiesOver v.1.asIdeal := hQover v
    have hM : kummerField M p Δ = ⊤ :=
      kummerField_def.trans adjoin_pow_eq_algebraMap_kummerField_eq_top
    have hbound : p ^ Nat.card (T : Set (HeightOneSpectrum (𝓞 K))) ≤ Module.finrank L M := by
      rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
      exact hcard.le
    exact Set.unitLocalPowerClassMap_surjective
      (K := K) (M := M) (S := (S : Set (HeightOneSpectrum (𝓞 K))))
      (T := (T : Set (HeightOneSpectrum (𝓞 K)))) hST' hp.ne_zero L σ Q hσ hfix hζ
      havoid hrootsM hM hbound
  exact ⟨T, hST', hcard, hsurj, hsplit⟩

end TauCeti.ClassFieldTheory

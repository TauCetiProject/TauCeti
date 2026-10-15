/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Unramified.Kummer
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import TauCeti.RingTheory.DedekindDomain.SelmerGroup
public import TauCeti.RingTheory.DedekindDomain.SInteger.SelmerGroup.NumberField

/-!
# Kummer classes unramified outside `S` and the Selmer group `K(S, n)`

Let `R` be a Dedekind domain with finite residue fields and fraction field `K`, let `n` be a natural
number invertible in `K`, and let `S` be a set of height-one primes of `R` containing every prime
that divides `n`. For each prime `v` fix a `K`-embedding `τ v : Kˢ → K_vˢ` of separable closures,
along which a class of `H¹(G_K, μₙ)` restricts to a class of `H¹(G_{K_v}, μₙ)`. A class is
**unramified outside `S`** when, for every `v ∉ S`, its restriction to `K_v` vanishes on the
inertia subgroup of `K_v` (`TauCeti.unramifiedOutsideKummerCohomology`).

Under the Kummer isomorphism `Kˣ ⧸ (Kˣ)ⁿ ≃ H¹(G_K, μₙ)` these are exactly the classes of the
Selmer group `K(S, n)`, the power classes whose `v`-adic valuation is divisible by `n` at every
`v ∉ S` (`TauCeti.kummerMap_mem_unramifiedOutsideKummerCohomology_iff`). Indeed restriction to
`K_v` carries the Kummer class of `a ∈ Kˣ` to the Kummer class of its image in `K_v`
(`TauCeti.explicitMap1_kummerMap`), which is unramified exactly when `n` divides the normalized
valuation of `a` at `v` (`TauCeti.explicitRes1_kummerMap_eq_zero_iff`, using that `v` does not
divide `n`). In particular, under these hypotheses the condition does not depend on the chosen
embeddings `τ`.

For a number field `K` and a finite `S`, the group `K(S, n)` is finite by the finiteness of the
class group and Dirichlet's unit theorem (`IsDedekindDomain.finite_selmerGroup_of_numberField`), so
the classes of `H¹(G_K, μₙ)` unramified outside `S` form a finite group
(`TauCeti.finite_unramifiedOutsideKummerCohomology`). This is the Kummer-theoretic step in the
finiteness of the Selmer groups of an elliptic curve over a number field: over a field containing
the `n`-torsion, the Weil pairing reduces `H¹(G_K, E[n])` to copies of `H¹(G_K, μₙ)`, and the
Selmer classes land in the classes unramified outside the primes of bad reduction and those
dividing `n`.

## Main definitions

* `TauCeti.unramifiedOutsideKummerCohomology τ S n`: the classes of `H¹(G_K, μₙ)` whose restriction
  to every `K_v` with `v ∉ S` vanishes on inertia.

## Main results

* `TauCeti.kummerMap_mem_unramifiedOutsideKummerCohomology_iff`: the Kummer class of `a ∈ Kˣ` is
  unramified outside `S` exactly when the power class of `a` lies in `K(S, n)`.
* `TauCeti.mem_unramifiedOutsideKummerCohomology_iff_exists`: the classes unramified outside `S`
  are exactly the Kummer classes of the elements of `K(S, n)`.
* `TauCeti.finite_unramifiedOutsideKummerCohomology`: over a number field and for finite `S`, there
  are finitely many classes unramified outside `S`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.1, Proposition VIII.1.6
  and its proof, and X.4.
-/

public section

noncomputable section

namespace TauCeti

open ContCohomology IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (τ : ∀ v : HeightOneSpectrum R,
    SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
  (S : Set (HeightOneSpectrum R)) (n : ℕ)

/-- **The Kummer classes unramified outside `S`**: the classes of `H¹(G_K, μₙ)` whose restriction
to the completion `K_v` along `τ v`, for every prime `v ∉ S`, vanishes on the inertia subgroup of
`K_v`. -/
def unramifiedOutsideKummerCohomology :
    AddSubgroup (H1 (AbsoluteGaloisGroup K) (KummerCoeff K n)) :=
  ⨅ (v : HeightOneSpectrum R) (_ : v ∉ S),
    ((explicitRes1 (AbsoluteGaloisGroup (v.adicCompletion K)) (KummerCoeff (v.adicCompletion K) n)
      ((inertiaSubgroup (v.adicCompletion K)).map
        (absoluteGaloisGroupRestrictEquiv (v.adicCompletion K)).toMonoidHom)).comp
      (explicitMap1 (AbsoluteGaloisGroup K) (KummerCoeff K n)
        (AbsoluteGaloisGroup (v.adicCompletion K)) (KummerCoeff (v.adicCompletion K) n)
        (absoluteGaloisGroupMap (τ v)) (kummerCoeffBaseChange n (τ v))
        continuous_of_discreteTopology (kummerCoeffBaseChange_smul n (τ v)))).ker

variable {τ S n}

/-- A class is unramified outside `S` exactly when, at every `v ∉ S`, its restriction to `K_v`
vanishes on inertia. -/
theorem mem_unramifiedOutsideKummerCohomology_iff
    {c : H1 (AbsoluteGaloisGroup K) (KummerCoeff K n)} :
    c ∈ unramifiedOutsideKummerCohomology τ S n ↔ ∀ v ∉ S,
      explicitRes1 (AbsoluteGaloisGroup (v.adicCompletion K)) (KummerCoeff (v.adicCompletion K) n)
        ((inertiaSubgroup (v.adicCompletion K)).map
          (absoluteGaloisGroupRestrictEquiv (v.adicCompletion K)).toMonoidHom)
        (explicitMap1 (AbsoluteGaloisGroup K) (KummerCoeff K n)
          (AbsoluteGaloisGroup (v.adicCompletion K)) (KummerCoeff (v.adicCompletion K) n)
          (absoluteGaloisGroupMap (τ v)) (kummerCoeffBaseChange n (τ v))
          continuous_of_discreteTopology (kummerCoeffBaseChange_smul n (τ v)) c) = 0 := by
  simp only [unramifiedOutsideKummerCohomology, AddSubgroup.mem_iInf, AddMonoidHom.mem_ker,
    AddMonoidHom.comp_apply]

/-- **Kummer classes unramified outside `S` are the Selmer group `K(S, n)`.** If `n` is invertible
in `K` and no prime outside `S` divides `n`, the Kummer class of `a ∈ Kˣ` is unramified outside
`S` exactly when the power class of `a` lies in `K(S, n)`, that is, when `n` divides the `v`-adic
valuation of `a` at every `v ∉ S`. -/
theorem kummerMap_mem_unramifiedOutsideKummerCohomology_iff (hn : IsUnit (n : K))
    (hS : ∀ v ∉ S, (n : R) ∉ v.asIdeal) (a : Kˣ) :
    (kummerMap K n hn a).toAdd ∈ unramifiedOutsideKummerCohomology τ S n ↔
      (QuotientGroup.mk a : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) ∈
        selmerGroup (R := R) (K := K) (S := S) (n := n) := by
  rw [mem_unramifiedOutsideKummerCohomology_iff]
  refine forall₂_congr fun v hv ↦ ?_
  -- restriction to `K_v` is the Kummer class of the image of `a`, whose normalized valuation is
  -- minus the `v`-adic valuation of `a`
  have hval : (normalizedValuation (v.adicCompletion K)
      (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) a)).toAdd =
        -(v.valuationOfNeZero a).toAdd := by
    have h := v.coe_normalizedValuation_unitsMap_algebraMap (K := K) a
    rw [← HeightOneSpectrum.valuationOfNeZero_eq, ← WithZero.coe_inv, WithZero.coe_inj] at h
    rw [h, toAdd_inv]
  rw [explicitMap1_kummerMap n (τ v) hn a,
    explicitRes1_kummerMap_eq_zero_iff (v.adicCompletion K) _
      (mt v.ringChar_residueField_adicCompletion_dvd_iff.1 (hS v hv)),
    hval, Int.dvd_neg, HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff]

/-- **The classes unramified outside `S` are the Kummer classes of `K(S, n)`.** If `n` is
invertible in `K` and no prime outside `S` divides `n`, a class of `H¹(G_K, μₙ)` is unramified
outside `S` exactly when it is the Kummer class of an element of `Kˣ` whose power class lies in
`K(S, n)`. -/
theorem mem_unramifiedOutsideKummerCohomology_iff_exists (hn : IsUnit (n : K))
    (hS : ∀ v ∉ S, (n : R) ∉ v.asIdeal) {c : H1 (AbsoluteGaloisGroup K) (KummerCoeff K n)} :
    c ∈ unramifiedOutsideKummerCohomology τ S n ↔
      ∃ a : Kˣ, (QuotientGroup.mk a : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) ∈
        selmerGroup (R := R) (K := K) (S := S) (n := n) ∧ (kummerMap K n hn a).toAdd = c := by
  obtain ⟨a, ha⟩ := kummerMap_surjective hn (Multiplicative.ofAdd c)
  obtain rfl : (kummerMap K n hn a).toAdd = c := by rw [ha, toAdd_ofAdd]
  refine ⟨fun h ↦ ⟨a, (kummerMap_mem_unramifiedOutsideKummerCohomology_iff hn hS a).1 h, rfl⟩,
    fun ⟨b, hb, hba⟩ ↦ ?_⟩
  rw [← hba]
  exact (kummerMap_mem_unramifiedOutsideKummerCohomology_iff hn hS b).2 hb

end TauCeti

namespace TauCeti

open ContCohomology IsDedekindDomain NumberField

variable {K : Type*} [Field K] [NumberField K]
  {τ : ∀ v : HeightOneSpectrum (𝓞 K),
    SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)}
  {S : Set (HeightOneSpectrum (𝓞 K))} {n : ℕ}

/-- **Finiteness of the Kummer classes unramified outside `S`.** Over a number field `K`, if `n` is
invertible in `K` and `S` is a finite set of finite places, only finitely many classes of
`H¹(G_K, μₙ)` are unramified outside `S`. This follows by enlarging `S` by the finitely many places
dividing `n`, where the classes are the Kummer classes of the finite group `K(S, n)`. -/
theorem finite_unramifiedOutsideKummerCohomology (hSf : S.Finite) (hn : IsUnit (n : K)) :
    Finite (unramifiedOutsideKummerCohomology τ S n) := by
  have : NeZero n := ⟨fun h ↦ by simp [h] at hn⟩
  let T := S ∪ {v : HeightOneSpectrum (𝓞 K) | (n : 𝓞 K) ∈ v.asIdeal}
  have hdiv : {v : HeightOneSpectrum (𝓞 K) | (n : 𝓞 K) ∈ v.asIdeal}.Finite :=
    (HeightOneSpectrum.finite_setOfPred_valuation_ne_one (R := 𝓞 K) hn.ne_zero).subset <| by
      intro v hv
      exact ne_of_lt ((v.valuation_lt_one_iff_mem (K := K) (n : 𝓞 K)).2 hv)
  have hTf : T.Finite := hSf.union hdiv
  have hT : ∀ v ∉ T, (n : 𝓞 K) ∉ v.asIdeal := by
    intro v hvT hvn
    exact hvT (Set.mem_union_right S hvn)
  have hfinT : Finite (unramifiedOutsideKummerCohomology τ T n) := by
    have := finite_selmerGroup_of_numberField K T n hTf
    -- the Kummer map descends to the power classes, and every class is the image of `K(T, n)`
    let f := (kummerClassMap K n hn).comp
      (QuotientGroup.quotientMulEquivOfEq
        (powerSubgroup_eq_range_powMonoidHom Kˣ n).symm).toMonoidHom
    refine Set.Finite.to_subtype ((Set.finite_range fun x : selmerGroup (R := 𝓞 K) (K := K)
      (S := T) (n := n) ↦ (f x).toAdd).subset fun c hc ↦ ?_)
    obtain ⟨a, ha, rfl⟩ :=
      (mem_unramifiedOutsideKummerCohomology_iff_exists hn hT).1 hc
    exact ⟨⟨_, ha⟩, by
      change (f (QuotientGroup.mk a)).toAdd = _
      dsimp [f]
      rw [kummerClassMap_mk]⟩
  refine @Finite.of_injective _ _ hfinT
    (fun c : unramifiedOutsideKummerCohomology τ S n =>
      (⟨c, ?_⟩ : unramifiedOutsideKummerCohomology τ T n)) ?_
  · rw [mem_unramifiedOutsideKummerCohomology_iff]
    have hc := c.property
    rw [mem_unramifiedOutsideKummerCohomology_iff] at hc
    intro v hvT
    exact hc v fun hvS ↦ hvT (Set.mem_union_left _ hvS)
  · intro a b hab
    apply Subtype.ext
    exact congrArg (fun c : unramifiedOutsideKummerCohomology τ T n =>
      (c : H1 (AbsoluteGaloisGroup K) (KummerCoeff K n))) hab

end TauCeti

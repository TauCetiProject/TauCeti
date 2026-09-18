/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PolynomialGaloisGroup
public import Mathlib.RingTheory.Frobenius
public import TauCeti.GroupTheory.Perm.Partition
public import TauCeti.NumberTheory.NumberField.Index.Exponent
import TauCeti.GroupTheory.GroupAction.OrbitCard
import TauCeti.NumberTheory.NumberField.Frobenius.DecompositionGroup
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.NumberTheory.NumberField.Inertia
import TauCeti.FieldTheory.Galois.FixedField
import TauCeti.FieldTheory.GaloisGroups.Stabilizer
import TauCeti.NumberTheory.NumberField.Minpoly
import TauCeti.NumberTheory.RamificationInertia.DoubleCoset.DecompositionOrbits

/-!
# Dedekind's theorem

Let `θ` be an algebraic integer of a number field `K`, with minimal polynomial
`f = minpoly ℤ θ`, and let `p` be a prime modulo which `f` is squarefree. Let `M` be a Galois
number field in which `minpoly ℚ θ` splits, let `Q` be a prime of `𝓞 M` above `p`, and let `σ`
be an arithmetic Frobenius at `Q`. **Dedekind's theorem** says that the multiset of the degrees of
the monic irreducible factors of `f mod p` is the cycle type of `σ` acting on the roots of
`minpoly ℚ θ` in `M`, with one part `1` added for each fixed root
(`factorizationType_eq_cycleType_isArithFrobAt`); in terms of `Equiv.Perm.fullCycleType`, the
two sides are `fullCycleType_galActionHom_restrict_eq_map_natDegree_monicFactorsMod`.

The proof is a chain of identifications of multisets of natural numbers.

* Every root `β` of `minpoly ℚ θ` in `M` generates a subfield `ℚ(β)`, realised as the fixed field
  of the stabilizer of `β` in `Gal(M/ℚ)`, in which `β` is an integral primitive element with the
  same minimal polynomial over `ℤ` as `θ` (`rootIntegralPrimitiveElement`). Since `f mod p` is
  squarefree, `p` does not divide the conductor exponent of `β` there, so the Kummer–Dedekind
  theorem applies in `ℚ(β)`: the primes above `p` correspond to the irreducible factors of
  `f mod p`, unramified over `ℤ`, with residue degrees the degrees of the factors
  (`ramificationIdx_eq_one_of_liesOver_span`,
  `map_inertiaDeg_primesOver_eq_map_natDegree_monicFactorsMod`).
* Since every root field is unramified at `p`, the inertia subgroup of `Q` fixes every root
  (`inertia_smul_eq_self`), so the orbits of the decomposition group of `Q` on the roots are the
  orbits of the Frobenius `σ` (`Ideal.orbit_stabilizer_eq_orbit_zpowers_of_isArithFrobAt`), whose
  sizes form the full cycle type of `σ` (`Equiv.Perm.fullCycleType_eq_map_card_orbit`).
* The roots are the cosets of the stabilizer of a chosen root
  (`rootSetEquivQuotientStabilizer`), and the orbits of the decomposition group on those cosets
  are the primes of the root field above `p`, with orbit size the local degree `e · f`
  (`Ideal.map_card_orbit_stabilizer_eq_map_ramificationIdx_mul_inertiaDeg`); those local degrees
  are computed over `𝓞 ℚ`, and agree with the ones over `ℤ`
  (`Ideal.inertiaDeg_ringOfIntegers_rat_eq_int`).

No transport between `K` and the subfields of `M` is needed: `K` only enters through `θ`, whose
minimal polynomial is shared by all the roots. In particular no hypothesis that `θ` generates
`K` over `ℚ`, and none on the conductor exponent of `θ`, is needed: every root generates its own
field, and squarefreeness of `minpoly ℤ θ` modulo `p` already keeps `p` away from the conductor
exponent.

## Main results

* `TauCeti.NumberField.factorizationType_eq_cycleType_isArithFrobAt`: Dedekind's theorem.
* `TauCeti.NumberField.fullCycleType_galActionHom_restrict_eq_map_natDegree_monicFactorsMod`: the
  same statement with the full cycle type.
* `TauCeti.NumberField.inertia_smul_eq_self`: the inertia subgroup of a prime above `p` fixes the
  roots of `minpoly ℚ θ` when `minpoly ℤ θ` is squarefree modulo `p`.
* `TauCeti.NumberField.rootIntegralPrimitiveElement`: a root of `minpoly ℚ θ`, as an integral
  primitive element of the field it generates.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §8, Exercises 4 and 5.
* D. A. Marcus, *Number Fields*, Chapter 4.
-/

public section

open IntermediateField MulAction Polynomial

open scoped NumberField Pointwise

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {M : Type*} [Field M] [NumberField M]

/-! ### A root as an integral primitive element of its field -/

section RootField

variable [IsGalois ℚ M] {θ : 𝓞 K} {β : M}

/-- A root `β` of `minpoly ℚ θ`, as an integral primitive element of `ℚ(β)`, the fixed field of
the stabilizer of `β`. -/
noncomputable def rootIntegralPrimitiveElement (hβ : β ∈ (minpoly ℚ (θ : K)).rootSet M) :
    IntegralPrimitiveElement (fixedField (stabilizer (M ≃ₐ[ℚ] M) β)) :=
  ⟨⟨⟨β, mem_fixedField_stabilizer β⟩, by
      rw [mem_integralClosure_iff,
        ← isIntegral_algebraMap_iff (A := fixedField (stabilizer (M ≃ₐ[ℚ] M) β)) (B := M)]
      exact isIntegral_of_mem_rootSet hβ⟩,
    adjoin_eq_top_of_fixedField_stabilizer β⟩

variable (hβ : β ∈ (minpoly ℚ (θ : K)).rootSet M)

/-- The underlying element of `rootIntegralPrimitiveElement hβ` is the root `β`. -/
@[simp]
theorem coe_coe_rootIntegralPrimitiveElement :
    (((rootIntegralPrimitiveElement hβ).1 : fixedField (stabilizer (M ≃ₐ[ℚ] M) β)) : M) = β :=
  (rfl)

/-- The minimal polynomial over `ℤ` of a root, as an integral primitive element of its own field,
is `minpoly ℤ θ`. -/
@[simp]
theorem minpoly_rootIntegralPrimitiveElement :
    minpoly ℤ (rootIntegralPrimitiveElement hβ).1 = minpoly ℤ θ := by
  set E := fixedField (stabilizer (M ≃ₐ[ℚ] M) β)
  have h : minpoly ℚ ((rootIntegralPrimitiveElement hβ).1 : E) = minpoly ℚ (θ : K) := by
    rw [← minpoly.algebraMap_eq (algebraMap E M).injective]
    exact minpoly_rat_eq_of_mem_rootSet hβ
  rw [_root_.NumberField.RingOfIntegers.minpoly_rat_coe,
    _root_.NumberField.RingOfIntegers.minpoly_rat_coe] at h
  exact Polynomial.map_injective _ (algebraMap ℤ ℚ).injective_int h

/-- If `minpoly ℤ θ` is squarefree modulo `p`, then `p` does not divide the conductor exponent
of a root of `minpoly ℚ θ` in its own field. -/
theorem not_dvd_exponent_rootIntegralPrimitiveElement {p : ℕ} [Fact p.Prime]
    (hsq : Squarefree ((minpoly ℤ θ).map (Int.castRingHom (ZMod p)))) :
    ¬ p ∣ RingOfIntegers.exponent (rootIntegralPrimitiveElement hβ).1 := fun h =>
  (rootIntegralPrimitiveElement hβ).not_dvd_index_of_squarefree_map
    (by rwa [minpoly_rootIntegralPrimitiveElement])
    (h.trans (rootIntegralPrimitiveElement hβ).exponent_dvd_index)

/-- The monic irreducible factors modulo `p` of the minimal polynomial of a root are those of
`minpoly ℤ θ`. -/
@[simp]
theorem monicFactorsMod_rootIntegralPrimitiveElement (p : ℕ) [Fact p.Prime] :
    RingOfIntegers.monicFactorsMod (rootIntegralPrimitiveElement hβ).1 p =
      RingOfIntegers.monicFactorsMod θ p := by
  simp only [RingOfIntegers.monicFactorsMod, minpoly_rootIntegralPrimitiveElement]

variable {p : ℕ} [Fact p.Prime]

include hβ in
/-- **Every prime of the root field above `p` is unramified over `ℤ`.** -/
theorem ramificationIdx_eq_one_of_liesOver_span
    (hsq : Squarefree ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))))
    (𝔮 : Ideal (𝓞 (fixedField (stabilizer (M ≃ₐ[ℚ] M) β)))) [𝔮.IsPrime]
    [𝔮.LiesOver (Ideal.span {(p : ℤ)})] : 𝔮.ramificationIdx ℤ = 1 := by
  classical
  have hexp := not_dvd_exponent_rootIntegralPrimitiveElement hβ hsq
  obtain ⟨⟨φ, hφ⟩, hφ'⟩ :=
    (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hexp).symm.surjective
      ⟨𝔮, inferInstance, inferInstance⟩
  have h := NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply' hexp hφ
  rw [hφ'] at h
  rw [h, minpoly_rootIntegralPrimitiveElement]
  rw [monicFactorsMod_rootIntegralPrimitiveElement, RingOfIntegers.monicFactorsMod,
    Multiset.mem_toFinset] at hφ
  have hf0 : (minpoly ℤ θ).map (Int.castRingHom (ZMod p)) ≠ 0 :=
    ((minpoly.monic θ.isIntegral).map _).ne_zero
  rw [UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors
    (UniqueFactorizationMonoid.irreducible_of_normalized_factor _ hφ) hf0,
    UniqueFactorizationMonoid.normalize_normalized_factor _ hφ]
  exact Multiset.count_eq_one_of_mem
    ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hf0).mp hsq) hφ

include hβ in
/-- **The residue degrees of the primes of the root field above `p` are the degrees of the
irreducible factors of `minpoly ℤ θ` modulo `p`.** -/
theorem map_inertiaDeg_primesOver_eq_map_natDegree_monicFactorsMod
    (hexp : ¬ p ∣ RingOfIntegers.exponent (rootIntegralPrimitiveElement hβ).1) :
    (Finset.univ : Finset ((Ideal.span {(p : ℤ)}).primesOver
        (𝓞 (fixedField (stabilizer (M ≃ₐ[ℚ] M) β))))).val.map (fun 𝔮 => 𝔮.1.inertiaDeg ℤ) =
      (RingOfIntegers.monicFactorsMod θ p).val.map natDegree := by
  classical
  set e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hexp
  rw [← monicFactorsMod_rootIntegralPrimitiveElement hβ p]
  refine Multiset.map_eq_map_of_bij_of_nodup _ _ Finset.univ.nodup (Finset.nodup _)
    (fun 𝔮 _ => (e 𝔮).1) (fun 𝔮 _ => (e 𝔮).2) ?_ ?_ ?_
  · intro a _ b _ h
    exact e.injective (Subtype.ext h)
  · intro φ hφ
    exact ⟨e.symm ⟨φ, hφ⟩, Finset.mem_univ _, by rw [e.apply_symm_apply]⟩
  · intro 𝔮 _
    have h := NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hexp
      (e 𝔮).2
    rw [e.symm_apply_apply] at h
    exact h

end RootField

/-! ### Dedekind's theorem -/

section Assembly

variable [IsGalois ℚ M] {θ : 𝓞 K} {p : ℕ} [Fact p.Prime]

omit [IsGalois ℚ M] in
/-- The orbits of the permutation of the roots induced by `σ` are the `⟨σ⟩`-orbits. -/
theorem orbit_zpowers_galActionHom_restrict_eq
    [Fact ((minpoly ℚ (θ : K)).map (algebraMap ℚ M)).Splits] (σ : M ≃ₐ[ℚ] M)
    (x : (minpoly ℚ (θ : K)).rootSet M) :
    orbit (Subgroup.zpowers (Gal.galActionHom (minpoly ℚ (θ : K)) M
      (Gal.restrict (minpoly ℚ (θ : K)) M σ))) x = orbit (Subgroup.zpowers σ) x := by
  have key : ∀ n : ℤ, (Gal.galActionHom (minpoly ℚ (θ : K)) M
      (Gal.restrict (minpoly ℚ (θ : K)) M σ)) ^ n • x = σ ^ n • x := fun n => by
    apply Subtype.ext
    rw [← map_zpow, ← map_zpow, Equiv.Perm.smul_def, Gal.galActionHom_restrict, rootSet.coe_smul]
    rfl
  ext y
  simp only [mem_orbit_iff]
  constructor
  · rintro ⟨⟨_, n, rfl⟩, rfl⟩
    exact ⟨⟨σ ^ n, Subgroup.zpow_mem_zpowers σ n⟩, (key n).symm⟩
  · rintro ⟨⟨_, n, rfl⟩, rfl⟩
    exact ⟨⟨_ ^ n, Subgroup.zpow_mem_zpowers _ n⟩, key n⟩

/-- **Inertia fixes the roots.** If `minpoly ℤ θ` is squarefree modulo `p`, then the inertia
subgroup of any prime `Q` above `p` acts trivially on the roots of `minpoly ℚ θ`. -/
theorem inertia_smul_eq_self (hsq : Squarefree ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))))
    (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver (Ideal.span {(p : ℤ)})]
    {τ : M ≃ₐ[ℚ] M} (hτ : τ ∈ Q.inertia (M ≃ₐ[ℚ] M)) (x : (minpoly ℚ (θ : K)).rootSet M) :
    τ • x = x := by
  obtain ⟨β, hβ⟩ := x
  have : IsGaloisGroup (stabilizer (M ≃ₐ[ℚ] M) β) (fixedField (stabilizer (M ≃ₐ[ℚ] M) β)) M :=
    IsGaloisGroup.subgroup (G := M ≃ₐ[ℚ] M) (K := ℚ) (L := M) _
  have h := (NumberField.ramificationIdx_under_eq_one_iff_inertia_le
    (stabilizer (M ≃ₐ[ℚ] M) β) Q inferInstance).mp
    (ramificationIdx_eq_one_of_liesOver_span hβ hsq _)
  exact Subtype.ext (mem_stabilizer_iff.mp (h hτ))

-- The hypotheses that `θ` generates `K` and that `p` does not divide the conductor exponent of
-- `θ` are not needed: every root generates its own field, and squarefreeness modulo `p` bounds
-- the conductor exponent of each root away from `p`.
open scoped Classical in
/-- **Dedekind's theorem.** Let `θ` be an algebraic integer of a number field `K` whose minimal
polynomial `minpoly ℤ θ` is squarefree modulo a prime `p`. Let `M` be a Galois number field in
which `minpoly ℚ θ` splits, `Q` a prime of `𝓞 M` above `p`, and `σ` an arithmetic Frobenius at
`Q`. Then the full cycle type of `σ` acting on the roots of `minpoly ℚ θ` in `M` is the multiset
of the degrees of the monic irreducible factors of `minpoly ℤ θ` modulo `p`. -/
theorem fullCycleType_galActionHom_restrict_eq_map_natDegree_monicFactorsMod
    (hsq : Squarefree ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))))
    [Fact ((minpoly ℚ (θ : K)).map (algebraMap ℚ M)).Splits]
    (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver (Ideal.span {(p : ℤ)})]
    {σ : M ≃ₐ[ℚ] M} (hσ : IsArithFrobAt ℤ σ Q) :
    Equiv.Perm.fullCycleType
        (Gal.galActionHom (minpoly ℚ (θ : K)) M (Gal.restrict (minpoly ℚ (θ : K)) M σ)) =
      (RingOfIntegers.monicFactorsMod θ p).val.map natDegree := by
  classical
  -- A root of `minpoly ℚ θ` in `M`.
  obtain ⟨α, hα⟩ : ∃ α, α ∈ (minpoly ℚ (θ : K)).rootSet M := by
    obtain ⟨α, hα⟩ :=
      (Fact.out : ((minpoly ℚ (θ : K)).map (algebraMap ℚ M)).Splits).exists_eval_eq_zero
        (by rw [degree_map]; exact (minpoly.degree_pos (IsIntegral.of_finite ℚ _)).ne')
    exact ⟨α, mem_rootSet.mpr ⟨minpoly.ne_zero (IsIntegral.of_finite ℚ _),
      by rwa [aeval_def, ← eval_map]⟩⟩
  have hp0 : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Q
  have hσ' : IsArithFrobAt (𝓞 ℚ) σ Q := (Ideal.isArithFrobAt_ringOfIntegers_rat_iff σ Q).mpr hσ
  have hp' : (Q.under (𝓞 ℚ)).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance (Ideal.under_ne_bot (𝓞 ℚ) hQ0)
  have hirr : Irreducible (minpoly ℚ (θ : K)) := minpoly.irreducible (IsIntegral.of_finite ℚ _)
  -- The chain of identifications.
  refine (Equiv.Perm.fullCycleType_eq_map_card_orbit _).trans ?_
  refine (TauCeti.map_card_orbit_eq_of_orbit_eq (G' := Subgroup.zpowers σ)
    (orbit_zpowers_galActionHom_restrict_eq σ)).trans ?_
  refine (TauCeti.map_card_orbit_eq_of_orbit_eq (G' := stabilizer (M ≃ₐ[ℚ] M) Q) (fun x =>
    (Ideal.orbit_stabilizer_eq_orbit_zpowers_of_isArithFrobAt Q hσ' x
      (fun τ hτ => inertia_smul_eq_self (p := p) hsq Q hτ x)).symm)).trans ?_
  refine (Equiv.map_card_orbit_eq_of_map_smul (G := stabilizer (M ≃ₐ[ℚ] M) Q)
    (rootSetEquivQuotientStabilizer hirr hα) fun d x => by
      rw [MulAction.subgroup_smul_def, MulAction.subgroup_smul_def]
      exact rootSetEquivQuotientStabilizer_smul hirr hα d x).trans
    ?_
  refine (Ideal.map_card_orbit_stabilizer_eq_map_ramificationIdx_mul_inertiaDeg (Q.under (𝓞 ℚ)) Q
    (stabilizer (M ≃ₐ[ℚ] M) α)).trans ?_
  refine Eq.trans ?_ (map_inertiaDeg_primesOver_eq_map_natDegree_monicFactorsMod (p := p) hα
    (not_dvd_exponent_rootIntegralPrimitiveElement hα hsq))
  -- Primes above `Q ∩ 𝓞 ℚ` are primes above `p`, with the same residue degree and trivial
  -- ramification.
  have hset := Ideal.primesOver_under_ringOfIntegers_rat_eq (p := p) Q
    (fixedField (stabilizer (M ≃ₐ[ℚ] M) α))
  refine Multiset.map_eq_map_of_bij_of_nodup _ _ Finset.univ.nodup Finset.univ.nodup
    (fun 𝔮 _ => ⟨𝔮.1, hset ▸ 𝔮.2⟩) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro a _ b _ h
    exact Subtype.ext (Subtype.mk.inj h)
  · intro 𝔮 _
    exact ⟨⟨𝔮.1, hset.symm ▸ 𝔮.2⟩, Finset.mem_univ _, rfl⟩
  · intro 𝔮 _
    have hmem : 𝔮.1 ∈ (Ideal.span {(p : ℤ)}).primesOver
        (𝓞 (fixedField (stabilizer (M ≃ₐ[ℚ] M) α))) := hset ▸ 𝔮.2
    have h1 : 𝔮.1.IsPrime := hmem.1
    have h2 : 𝔮.1.LiesOver (Ideal.span {(p : ℤ)}) := hmem.2
    have hne : 𝔮.1 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 𝔮.1
    rw [Ideal.ramificationIdx_ringOfIntegers_rat_eq_int _ hne,
      Ideal.inertiaDeg_ringOfIntegers_rat_eq_int _ hne,
      ramificationIdx_eq_one_of_liesOver_span (p := p) hα hsq 𝔮.1, one_mul]

open scoped Classical in
/-- **Dedekind's theorem, with the fixed points counted separately.** The multiset of degrees of
the monic irreducible factors of `minpoly ℤ θ` modulo `p` is the cycle type of a Frobenius at a
prime above `p` acting on the roots of `minpoly ℚ θ`, together with one part `1` for each fixed
root. This is the form with the cycle type and the fixed points separated; the full cycle type of
`fullCycleType_galActionHom_restrict_eq_map_natDegree_monicFactorsMod` packages the two
summands. -/
theorem factorizationType_eq_cycleType_isArithFrobAt
    (hsq : Squarefree ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))))
    [Fact ((minpoly ℚ (θ : K)).map (algebraMap ℚ M)).Splits]
    (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver (Ideal.span {(p : ℤ)})]
    {σ : M ≃ₐ[ℚ] M} (hσ : IsArithFrobAt ℤ σ Q) :
    (RingOfIntegers.monicFactorsMod θ p).val.map natDegree =
      (Gal.galActionHom (minpoly ℚ (θ : K)) M
          (Gal.restrict (minpoly ℚ (θ : K)) M σ)).cycleType +
        Multiset.replicate (Nat.card (Function.fixedPoints
          (Gal.galActionHom (minpoly ℚ (θ : K)) M
            (Gal.restrict (minpoly ℚ (θ : K)) M σ)))) 1 := by
  rw [← fullCycleType_galActionHom_restrict_eq_map_natDegree_monicFactorsMod hsq Q hσ,
    Equiv.Perm.fullCycleType_def, Equiv.Perm.parts_partition, Nat.card_eq_fintype_card,
    Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType]

end Assembly

end TauCeti.NumberField

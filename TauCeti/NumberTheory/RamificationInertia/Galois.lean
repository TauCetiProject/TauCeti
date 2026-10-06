/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Sigma
public import Mathlib.Algebra.Group.Action.TransferInstance
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import TauCeti.NumberTheory.NumberField.AutomorphismAction
public import TauCeti.RingTheory.Ideal.PrimesOver
import TauCeti.RingTheory.Unramified.AlgEquiv

/-!
# Ramification and inertia in Galois extensions

This file records Galois consequences of the fundamental identity for primes in finite
extensions of domains. First, in a Galois extension the number of primes above a prime ideal is
maximal exactly when the common ramification index and inertia degree are both `1`, and, by
orbit–stabilizer alone, exactly when the decomposition group of one (equivalently, every) prime
above it is trivial; neither criterion needs separability of the residue extensions. Second, the
cardinality of the inertia subgroup of a prime `P` upstairs is the ramification index of `P`
itself over the base, rather than the `Ideal.ramificationIdxIn` of the prime below it.

The rest of the file is about how unramifiedness and inertia subgroups vary with the prime.
Translating a prime by `σ` preserves unramifiedness and conjugates its inertia subgroup by `σ`.
Because the Galois group acts transitively on the primes above a fixed prime of the base,
unramifiedness at one of them gives it at all of them, and when one of their inertia subgroups is
normal (for instance when the Galois group is commutative) they all share that inertia subgroup.
That uniformity is what lets a statement about ramification in an intermediate field be tested at
a single prime upstairs.

The number-field specialization also compares the `galRestrict` action on primes over a
base ideal with the pointwise ideal action on the ring of integers, including stabilizers and
transitivity.

## Main results

* `TauCeti.coe_galRestrict_eq_toRingHom`: restriction agrees with the canonical action.
* `TauCeti.coe_smul_primesOver_ringOfIntegers` and
  `TauCeti.stabilizer_primesOver_ringOfIntegers`: the primes-over action and its stabilizers
  agree with those on the underlying ideals.
* `TauCeti.isPretransitive_primesOver_ringOfIntegers`: transitivity for Galois extensions.
* `TauCeti.primesAboveRingOfIntegersMulAction` and
  `TauCeti.sigmaPrimesOverEquivPrimesAbove_smul`: the canonical primes-above action and its
  equivariant comparison with the fibre indexing.
* `TauCeti.asIdeal_smul_primesAbove_ringOfIntegers`: the induced action on underlying ideals.

* `Ideal.ncard_primesOver_eq_natCard_iff_of_isGaloisGroup`: the domain/flat Galois counting
  criterion.
* `Ideal.ncard_primesOver_eq_natCard_iff_stabilizer_eq_bot`,
  `Ideal.ncard_primesOver_eq_natCard_iff_forall_stabilizer_eq_bot`: the same count is maximal
  exactly when the decomposition groups above the prime are trivial.
* `Ideal.stabilizer_eq_bot_iff_ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one`: a decomposition
  group is trivial exactly when `e = f = 1`.
* `Ideal.card_inertia_eq_ramificationIdx`: the un-`In` form of the inertia count.
* `Ideal.isUnramifiedAt_pointwise_smul_iff`: unramifiedness is invariant under translation by
  an algebra automorphism.
* `Ideal.isUnramifiedAt_of_isUnramifiedAt_of_isGaloisGroup`: unramifiedness transfers between
  primes above the same base prime in a Galois extension.
* `Ideal.mem_inertia_pointwise_smul_iff`: translation conjugates inertia subgroups.
* `Ideal.inertia_pointwise_smul`: translation leaves a normal inertia subgroup unchanged.
* `Ideal.inertia_eq_of_liesOver`: when one of them is normal, all the primes above a fixed prime of
  the base have the same inertia subgroup.

## Provenance

Built directly on Mathlib's Galois fundamental identity
(`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`), on its description of the
primes above a prime as one orbit (`Algebra.IsInvariant.orbit_eq_primesOver`) together with
orbit–stabilizer (`MulAction.index_stabilizer`), on its inertia count
(`Ideal.card_inertia_eq_ramificationIdxIn`), on its conjugation formula for inertia subgroups
(`Ideal.inertia_smul`) and on its transitivity statement
(`Ideal.exists_smul_eq_of_isGaloisGroup`), together with the transport of unramifiedness along
algebra isomorphisms `AlgEquiv.isUnramifiedAt_of_eq_comap`.
-/

public section

open Module

namespace Ideal

open scoped Pointwise

/-- In a finite flat Galois extension of domains, the number of primes over a prime ideal
equals the order of the Galois group iff the common ramification index and inertia degree are
both `1`. -/
theorem ncard_primesOver_eq_natCard_iff_of_isGaloisGroup {A B : Type*}
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
    [Module.Flat A B] (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] (P : Ideal A) [P.IsPrime] : (primesOver P B).ncard = Nat.card G ↔
      P.ramificationIdxIn B = 1 ∧ P.inertiaDegIn B = 1 := by
  have h := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn P B G
  rw [← mul_eq_one, ← h, left_eq_mul₀ (left_ne_zero_of_mul (h ▸ Nat.card_pos.ne'))]

section Stabilizer

open MulAction

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (G : Type*) [Group G] [Finite G]
  [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G]

/-- **Complete splitting through the decomposition group.** If `G` acts on `B` with invariants
`A`, then the number of primes of `B` over `P` equals the order of `G` exactly when the
decomposition group `stabilizer G Q` of one prime `Q` over `P` is trivial. This is
orbit–stabilizer for the transitive action of `G` on the primes over `P`; no hypothesis on the
residue extensions is needed. -/
theorem ncard_primesOver_eq_natCard_iff_stabilizer_eq_bot (P : Ideal A) (Q : Ideal B)
    [Q.IsPrime] [Q.LiesOver P] :
    (P.primesOver B).ncard = Nat.card G ↔ stabilizer G Q = ⊥ := by
  rw [← Algebra.IsInvariant.orbit_eq_primesOver A B G P Q, ← index_stabilizer]
  refine ⟨fun h ↦ Subgroup.card_eq_one.1 ?_, fun h ↦ by rw [h, Subgroup.index_bot]⟩
  have hmul := (stabilizer G Q).card_mul_index
  rw [h] at hmul
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [hmul, one_mul])

/-- **Complete splitting through all decomposition groups.** If `G` acts on `B` with invariants
`A`, then the number of primes of `B` over a prime `P` of `A` equals the order of `G` exactly when
the decomposition group of every prime over `P` is trivial. -/
theorem ncard_primesOver_eq_natCard_iff_forall_stabilizer_eq_bot [FaithfulSMul A B]
    (P : Ideal A) [P.IsPrime] :
    (P.primesOver B).ncard = Nat.card G ↔ ∀ Q ∈ P.primesOver B, stabilizer G Q = ⊥ := by
  have : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  obtain ⟨⟨Q, _, _⟩⟩ := (inferInstance : Nonempty (P.primesOver B))
  exact ⟨fun h Q' ⟨_, _⟩ ↦ (ncard_primesOver_eq_natCard_iff_stabilizer_eq_bot G P Q').1 h,
    fun h ↦ (ncard_primesOver_eq_natCard_iff_stabilizer_eq_bot G P Q).2 (h Q ⟨‹_›, ‹_›⟩)⟩

end Stabilizer

/-- **The decomposition group is trivial exactly when `e = f = 1`.** In a finite flat Galois
extension of domains, the decomposition group of a prime `Q` over `P` is trivial exactly when the
common ramification index and inertia degree over `P` are both `1`. Unlike
`Ideal.card_stabilizer_eq`, this needs no separability of the residue extension. -/
theorem stabilizer_eq_bot_iff_ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one {A B : Type*}
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
    [Module.Flat A B] (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] (P : Ideal A) [P.IsPrime] (Q : Ideal B) [Q.IsPrime] [Q.LiesOver P] :
    MulAction.stabilizer G Q = ⊥ ↔ P.ramificationIdxIn B = 1 ∧ P.inertiaDegIn B = 1 := by
  rw [← ncard_primesOver_eq_natCard_iff_stabilizer_eq_bot G P Q,
    ncard_primesOver_eq_natCard_iff_of_isGaloisGroup G P]

/-- The cardinality of the inertia subgroup of `P` is the ramification index of `P` over `R`.
This is `Ideal.card_inertia_eq_ramificationIdxIn` stated with the ramification index of `P`
itself rather than with `Ideal.ramificationIdxIn` of the ideal below it. -/
theorem card_inertia_eq_ramificationIdx (R : Type*) {S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsDomain R] [IsDomain S] [Module.Finite R S] [Module.Flat R S] (G : Type*)
    [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S] (P : Ideal S) [P.IsPrime]
    [Algebra.HasSeparableResidueFieldsAt R S (P.under R)] :
    Nat.card (P.inertia G) = P.ramificationIdx R :=
  (card_inertia_eq_ramificationIdxIn (G := G) (P.under R) P).trans
    (ramificationIdxIn_eq_ramificationIdx (P.under R) P G)

section Unramified

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]

/-- **Unramifiedness is invariant under algebra automorphisms.** Translating a prime by an
`R`-algebra action automorphism preserves unramifiedness over `R`. -/
@[simp]
theorem isUnramifiedAt_pointwise_smul_iff (Q : Ideal S) [Q.IsPrime] (g : G) :
    Algebra.IsUnramifiedAt R (g • Q) ↔ Algebra.IsUnramifiedAt R Q := by
  have key (g : G) (Q : Ideal S) [Q.IsPrime] [Algebra.IsUnramifiedAt R Q] :
      Algebra.IsUnramifiedAt R (g • Q) :=
    (MulSemiringAction.toAlgEquiv R S g).symm.isUnramifiedAt_of_eq_comap
      (pointwise_smul_eq_comap Q)
  refine ⟨fun _ ↦ ?_, fun _ ↦ key g Q⟩
  simpa using key g⁻¹ (g • Q)

end Unramified

/-- Unramifiedness at one prime above `p` implies unramifiedness at every prime above `p`
when the Galois group acts transitively on them. -/
theorem isUnramifiedAt_of_isUnramifiedAt_of_isGaloisGroup
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (p : Ideal A) (P Q : Ideal B) [P.IsPrime] [P.LiesOver p]
    [Q.IsPrime] [Q.LiesOver p] (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G B] [IsGaloisGroup G A B]
    [Algebra.IsUnramifiedAt A P] : Algebra.IsUnramifiedAt A Q := by
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup p P Q G
  exact (isUnramifiedAt_pointwise_smul_iff P σ).mpr inferInstance

section Inertia

variable {S : Type*} [Ring S] {G : Type*} [Group G] [MulSemiringAction G S]

/-- **Inertia is conjugated by the Galois action.** An element `τ` lies in the inertia subgroup of
the translated ideal `σ • P` exactly when its conjugate `σ⁻¹ τ σ` lies in the inertia subgroup
of `P`. -/
theorem mem_inertia_pointwise_smul_iff {σ τ : G} {P : Ideal S} :
    τ ∈ (σ • P).inertia G ↔ σ⁻¹ * τ * σ ∈ P.inertia G := by
  simp [inertia_smul, Subgroup.map_equiv_eq_comap_symm]

/-- **Translation leaves a normal inertia subgroup unchanged.** This applies in particular to
every inertia subgroup of a commutative group. -/
@[simp]
theorem inertia_pointwise_smul (σ : G) (P : Ideal S) [(P.inertia G).Normal] :
    (σ • P).inertia G = P.inertia G := by
  rw [inertia_smul, Subgroup.Normal.map_conj_eq]

end Inertia

/-- **The primes over a fixed prime share a normal inertia subgroup.** In a Galois extension, if
the inertia subgroup of one prime `P` above `p` is normal (for instance when the Galois group is
commutative), then every prime `Q` above `p` has the same inertia subgroup. -/
theorem inertia_eq_of_liesOver {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) (P Q : Ideal B) [P.IsPrime] [P.LiesOver p] [Q.IsPrime] [Q.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    [(P.inertia G).Normal] : P.inertia G = Q.inertia G := by
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup p P Q G
  exact (inertia_pointwise_smul σ P).symm

end Ideal

namespace TauCeti

open NumberField
open scoped NumberField Pointwise

section PrimesOver

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

/-- Restriction to rings of integers agrees with the canonical Galois action. -/
theorem coe_galRestrict_eq_toRingHom (σ : L ≃ₐ[K] L) :
    (galRestrict (𝓞 K) K L (𝓞 L) σ : 𝓞 L →+* 𝓞 L) =
      MulSemiringAction.toRingHom (L ≃ₐ[K] L) (𝓞 L) σ := by
  ext1 z
  apply RingOfIntegers.ext
  exact (algebraMap_galRestrict_apply (𝓞 K) σ z).trans
    (algebraMap_smul_eq_apply σ z).symm

/-- The action on primes above a base ideal agrees with the action on their underlying ideals. -/
@[simp]
theorem coe_smul_primesOver_ringOfIntegers {p : Ideal (𝓞 K)}
    (σ : L ≃ₐ[K] L) (P : p.primesOver (𝓞 L)) :
    (σ • P).1 = σ • P.1 := by
  rw [Ideal.coe_smul_primesOver_eq_map_galRestrict, Ideal.pointwise_smul_def,
    ← Ideal.map_coe, coe_galRestrict_eq_toRingHom]

/-- A prime above a base ideal has the same stabilizer as its underlying ideal. -/
@[simp]
theorem stabilizer_primesOver_ringOfIntegers {p : Ideal (𝓞 K)} (P : p.primesOver (𝓞 L)) :
    MulAction.stabilizer (L ≃ₐ[K] L) P =
      MulAction.stabilizer (L ≃ₐ[K] L) (P : Ideal (𝓞 L)) := by
  ext σ
  simp only [MulAction.mem_stabilizer_iff, ← Subtype.val_inj,
    coe_smul_primesOver_ringOfIntegers]

/-- The Galois group acts transitively on primes above any fixed base ideal. -/
instance isPretransitive_primesOver_ringOfIntegers [IsGalois K L] {p : Ideal (𝓞 K)} :
    MulAction.IsPretransitive (L ≃ₐ[K] L) (p.primesOver (𝓞 L)) where
  exists_smul_eq P Q := by
    obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup p P.1 Q.1 (L ≃ₐ[K] L)
    exact ⟨σ, Subtype.ext ((coe_smul_primesOver_ringOfIntegers K L σ P).trans hσ)⟩

/-- The automorphism action on primes above a set, transported from the primes-over fibres. -/
noncomputable instance primesAboveRingOfIntegersMulAction
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    MulAction (L ≃ₐ[K] L)
      ↥(IsDedekindDomain.HeightOneSpectrum.primesAbove (𝓞 K) (𝓞 L) S) :=
  (sigmaPrimesOverEquivPrimesAbove (𝓞 K) (𝓞 L) S).symm.mulAction (L ≃ₐ[K] L)

/-- The canonical primes-above carrier and its fibre reindexing are equivariantly equivalent. -/
@[simp]
theorem sigmaPrimesOverEquivPrimesAbove_smul
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) (σ : L ≃ₐ[K] L)
    (p : Σ v : S, v.1.asIdeal.primesOver (𝓞 L)) :
    sigmaPrimesOverEquivPrimesAbove (𝓞 K) (𝓞 L) S (σ • p) =
      σ • sigmaPrimesOverEquivPrimesAbove (𝓞 K) (𝓞 L) S p := by
  -- The transported action applies the inverse reindexing, the fibre action, then reindexing.
  change _ = sigmaPrimesOverEquivPrimesAbove (𝓞 K) (𝓞 L) S
    (σ • (sigmaPrimesOverEquivPrimesAbove (𝓞 K) (𝓞 L) S).symm
      (sigmaPrimesOverEquivPrimesAbove (𝓞 K) (𝓞 L) S p))
  rw [Equiv.symm_apply_apply]

/-- On underlying ideals, the primes-above action is the canonical pointwise ideal action. -/
@[simp]
theorem asIdeal_smul_primesAbove_ringOfIntegers
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) (σ : L ≃ₐ[K] L)
    (w : ↥(IsDedekindDomain.HeightOneSpectrum.primesAbove (𝓞 K) (𝓞 L) S)) :
    (σ • w).1.asIdeal = σ • w.1.asIdeal := by
  obtain ⟨p, rfl⟩ := (sigmaPrimesOverEquivPrimesAbove (𝓞 K) (𝓞 L) S).surjective w
  rw [← sigmaPrimesOverEquivPrimesAbove_smul]
  rcases p with ⟨v, P⟩
  simp only [sigmaPrimesOverEquivPrimesAbove_apply_asIdeal, Sigma.smul_mk,
    coe_smul_primesOver_ringOfIntegers]

end PrimesOver

end TauCeti

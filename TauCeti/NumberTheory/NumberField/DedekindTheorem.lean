/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PolynomialGaloisGroup
public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import Mathlib.RingTheory.Frobenius
public import TauCeti.GroupTheory.Perm.Partition
public import TauCeti.NumberTheory.NumberField.Index.Discriminant
public import TauCeti.NumberTheory.NumberField.Index.Exponent
import TauCeti.GroupTheory.GroupAction.OrbitCard
import TauCeti.NumberTheory.NumberField.Frobenius.DecompositionGroup
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.NumberTheory.NumberField.Inertia
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
minimal polynomial is shared by all the roots. In particular the hypotheses `ℚ(θ) = K` and
`p ∤ exponent θ` of the roadmap's statement are not needed.

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

/-! ### A root of the minimal polynomial generates its own field -/

section Root

variable {θ : 𝓞 K}

/-- A root in `M` of `minpoly ℚ θ` is a root of `minpoly ℤ θ`. -/
theorem aeval_minpoly_int_eq_zero_of_mem_rootSet {β : M}
    (hβ : β ∈ (minpoly ℚ (θ : K)).rootSet M) : aeval β (minpoly ℤ θ) = 0 := by
  have h := (mem_rootSet.mp hβ).2
  rwa [_root_.NumberField.RingOfIntegers.minpoly_rat_coe, aeval_map_algebraMap] at h

/-- A root in `M` of `minpoly ℚ θ` is an algebraic integer. -/
theorem isIntegral_of_mem_rootSet {β : M} (hβ : β ∈ (minpoly ℚ (θ : K)).rootSet M) :
    IsIntegral ℤ β :=
  ⟨minpoly ℤ θ, minpoly.monic θ.isIntegral, aeval_minpoly_int_eq_zero_of_mem_rootSet hβ⟩

/-- A root in `M` of `minpoly ℚ θ` has that polynomial as its minimal polynomial over `ℚ`. -/
theorem minpoly_rat_eq_of_mem_rootSet {β : M} (hβ : β ∈ (minpoly ℚ (θ : K)).rootSet M) :
    minpoly ℚ β = minpoly ℚ (θ : K) :=
  (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible (IsIntegral.of_finite ℚ _))
    (mem_rootSet.mp hβ).2 (minpoly.monic (IsIntegral.of_finite ℚ _))).symm

/-- An algebraic integer of `M` that is a root of `minpoly ℚ θ` has the same minimal polynomial
over `ℤ` as `θ`. -/
theorem minpoly_int_eq_of_coe_mem_rootSet {β : 𝓞 M}
    (hβ : (β : M) ∈ (minpoly ℚ (θ : K)).rootSet M) : minpoly ℤ β = minpoly ℤ θ := by
  have h := minpoly_rat_eq_of_mem_rootSet hβ
  rw [_root_.NumberField.RingOfIntegers.minpoly_rat_coe,
    _root_.NumberField.RingOfIntegers.minpoly_rat_coe] at h
  exact Polynomial.map_injective _ (algebraMap ℤ ℚ).injective_int h

end Root

/-! ### The fixed field of the stabilizer of a root -/

section FixedField

variable [IsGalois ℚ M]

omit [IsGalois ℚ M] in
/-- The stabilizer of an element `β` of `M` in `Gal(M/ℚ)` is the subgroup fixing `ℚ(β)`. -/
theorem stabilizer_eq_fixingSubgroup_adjoin (β : M) :
    stabilizer (M ≃ₐ[ℚ] M) β = (ℚ⟮β⟯).fixingSubgroup := by
  ext σ
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have : ℚ⟮β⟯ ≤ fixedField (Subgroup.zpowers σ) := by
      rw [adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
      intro f hf
      exact mem_stabilizer_iff.mp (Subgroup.zpowers_le.mpr h hf)
    exact (IntermediateField.mem_fixedField_iff _ x).mp (this hx) σ (Subgroup.mem_zpowers σ)
  · intro h
    exact h β (mem_adjoin_simple_self ℚ β)

/-- The fixed field of the stabilizer of `β` is `ℚ(β)`. -/
theorem fixedField_stabilizer_eq_adjoin (β : M) :
    fixedField (stabilizer (M ≃ₐ[ℚ] M) β) = ℚ⟮β⟯ := by
  rw [stabilizer_eq_fixingSubgroup_adjoin, IsGalois.fixedField_fixingSubgroup]

omit [IsGalois ℚ M] in
/-- `β` lies in the fixed field of its stabilizer. -/
theorem mem_fixedField_stabilizer (β : M) : β ∈ fixedField (stabilizer (M ≃ₐ[ℚ] M) β) :=
  (IntermediateField.mem_fixedField_iff _ β).mpr fun _ hσ => hσ

/-- Inside the fixed field of its stabilizer, `β` generates the whole field over `ℚ`. -/
theorem adjoin_eq_top_of_fixedField_stabilizer (β : M) :
    Algebra.adjoin ℚ {(⟨β, mem_fixedField_stabilizer β⟩ : fixedField (stabilizer (M ≃ₐ[ℚ] M) β))}
      = ⊤ := by
  set E := fixedField (stabilizer (M ≃ₐ[ℚ] M) β) with hE
  set β' : E := ⟨β, mem_fixedField_stabilizer β⟩
  let _ : Algebra ℚ E := E.algebra'
  have hβ' : IsAlgebraic ℚ β' := IsAlgebraic.of_finite ℚ β'
  have htop : ℚ⟮β'⟯ = ⊤ := by
    apply IntermediateField.map_injective E.val
    rw [adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map, fieldRange_val]
    exact (fixedField_stabilizer_eq_adjoin β).symm
  have h := adjoin_simple_toSubalgebra_of_isAlgebraic hβ'
  rw [htop, IntermediateField.top_toSubalgebra] at h
  convert h.symm using 2

end FixedField

/-! ### Multiplicities in a squarefree reduction -/

/-- In a squarefree polynomial over a field, every normalized factor has multiplicity one. -/
theorem _root_.Polynomial.multiplicity_eq_one_of_mem_normalizedFactors_of_squarefree
    {F : Type*} [Field F] [DecidableEq F] {f φ : F[X]} (hsq : Squarefree f)
    (hφ : φ ∈ UniqueFactorizationMonoid.normalizedFactors f) : multiplicity φ f = 1 := by
  have hirr : Irreducible φ := UniqueFactorizationMonoid.irreducible_of_normalized_factor φ hφ
  have hdvd : φ ∣ f := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hφ
  have hle : emultiplicity φ f ≤ 1 :=
    ((squarefree_iff_emultiplicity_le_one f).mp hsq φ).resolve_right hirr.not_isUnit
  have hge : (1 : ℕ∞) ≤ emultiplicity φ f := by
    simpa using (pow_dvd_iff_le_emultiplicity (k := 1)).mp (by simpa using hdvd)
  exact multiplicity_eq_of_emultiplicity_eq_some (by simpa using le_antisymm hle hge)

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

/-- The minimal polynomial over `ℤ` of a root, as an integral primitive element of its own field,
is `minpoly ℤ θ`. -/
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
  exact Polynomial.multiplicity_eq_one_of_mem_normalizedFactors_of_squarefree hsq hφ

include hβ in
/-- **The residue degrees of the primes of the root field above `p` are the degrees of the
irreducible factors of `minpoly ℤ θ` modulo `p`.** -/
theorem map_inertiaDeg_primesOver_eq_map_natDegree_monicFactorsMod
    (hsq : Squarefree ((minpoly ℤ θ).map (Int.castRingHom (ZMod p)))) :
    (Finset.univ : Finset ((Ideal.span {(p : ℤ)}).primesOver
        (𝓞 (fixedField (stabilizer (M ≃ₐ[ℚ] M) β))))).val.map (fun 𝔮 => 𝔮.1.inertiaDeg ℤ) =
      (RingOfIntegers.monicFactorsMod θ p).val.map natDegree := by
  classical
  have hexp := not_dvd_exponent_rootIntegralPrimitiveElement hβ hsq
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

omit [IsGalois ℚ M] in
/-- The root set of `minpoly ℚ θ` in `M` is the Galois orbit of any of its elements. -/
theorem coe_rootSet_eq_orbit [Normal ℚ M] {α : M} (hα : α ∈ (minpoly ℚ (θ : K)).rootSet M) :
    ((minpoly ℚ (θ : K)).rootSet M : Set M) = orbit (M ≃ₐ[ℚ] M) α := by
  ext β
  constructor
  · intro hβ
    rw [← Normal.minpoly_eq_iff_mem_orbit, minpoly_rat_eq_of_mem_rootSet hβ,
      minpoly_rat_eq_of_mem_rootSet hα]
  · rintro ⟨τ, rfl⟩
    exact smul_mem_rootSet τ hα

/-- The roots of `minpoly ℚ θ` in `M`, as the cosets of the stabilizer of a chosen root. -/
noncomputable def rootSetEquivQuotientStabilizer {α : M}
    (hα : α ∈ (minpoly ℚ (θ : K)).rootSet M) :
    (minpoly ℚ (θ : K)).rootSet M ≃ (M ≃ₐ[ℚ] M) ⧸ stabilizer (M ≃ₐ[ℚ] M) α :=
  (Equiv.subtypeEquivRight fun β => Set.ext_iff.mp (coe_rootSet_eq_orbit hα) β).trans
    (orbitEquivQuotientStabilizer _ α)

/-- The identification of the roots with cosets is equivariant. -/
theorem rootSetEquivQuotientStabilizer_smul {α : M} (hα : α ∈ (minpoly ℚ (θ : K)).rootSet M)
    (g : M ≃ₐ[ℚ] M) (x : (minpoly ℚ (θ : K)).rootSet M) :
    rootSetEquivQuotientStabilizer hα (g • x) = g • rootSetEquivQuotientStabilizer hα x := by
  have hsymm : ∀ ρ : M ≃ₐ[ℚ] M,
      (((rootSetEquivQuotientStabilizer hα).symm (ρ : (M ≃ₐ[ℚ] M) ⧸ stabilizer (M ≃ₐ[ℚ] M) α) :
        (minpoly ℚ (θ : K)).rootSet M) : M) = ρ • α := fun ρ =>
    orbitEquivQuotientStabilizer_symm_apply (M ≃ₐ[ℚ] M) α ρ
  apply (rootSetEquivQuotientStabilizer hα).symm.injective
  rw [Equiv.symm_apply_apply]
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (rootSetEquivQuotientStabilizer hα x)
  have hx : (x : M) = τ • α := by
    have := congrArg (fun q => ((rootSetEquivQuotientStabilizer hα).symm q : M)) hτ
    rw [Equiv.symm_apply_apply] at this
    rw [← this, hsymm]
  rw [← hτ, MulAction.Quotient.smul_mk]
  apply Subtype.ext
  rw [hsymm, rootSet.coe_smul, hx, smul_eq_mul, mul_smul]

/-- The subgroup form of `rootSetEquivQuotientStabilizer_smul`, for the decomposition group. -/
theorem rootSetEquivQuotientStabilizer_subgroup_smul {α : M}
    (hα : α ∈ (minpoly ℚ (θ : K)).rootSet M) (D : Subgroup (M ≃ₐ[ℚ] M)) (d : D)
    (x : (minpoly ℚ (θ : K)).rootSet M) :
    rootSetEquivQuotientStabilizer hα (d • x) = d • rootSetEquivQuotientStabilizer hα x := by
  rw [MulAction.subgroup_smul_def, MulAction.subgroup_smul_def]
  exact rootSetEquivQuotientStabilizer_smul hα d x

omit [IsGalois ℚ M] [Fact p.Prime] in
/-- The primes of a subfield above `Q ∩ 𝓞 ℚ` are the primes above `p`. -/
theorem primesOver_under_ringOfIntegers_rat_eq (Q : Ideal (𝓞 M)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span {(p : ℤ)})] (E : IntermediateField ℚ M) :
    (Q.under (𝓞 ℚ)).primesOver (𝓞 E) = (Ideal.span {(p : ℤ)}).primesOver (𝓞 E) := by
  have : IsScalarTower ℤ (𝓞 ℚ) (𝓞 E) :=
    IsScalarTower.of_algebraMap_eq' ((RingHom.eq_intCast' _).trans (RingHom.eq_intCast' _).symm)
  have : IsScalarTower ℤ (𝓞 ℚ) (𝓞 M) :=
    IsScalarTower.of_algebraMap_eq' ((RingHom.eq_intCast' _).trans (RingHom.eq_intCast' _).symm)
  ext 𝔮
  simp only [Ideal.primesOver, Set.mem_ofPred_eq]
  refine and_congr_right fun _ => ⟨fun h => ⟨?_⟩, fun h => ⟨?_⟩⟩
  · rw [Ideal.over_def (P := Q) (p := Ideal.span {(p : ℤ)}),
      ← Ideal.under_under (A := ℤ) (B := 𝓞 ℚ) Q, h.over, Ideal.under_under]
  · rw [Ideal.under_ringOfIntegers_rat_eq_map, Ideal.under_ringOfIntegers_rat_eq_map, ← h.over,
      ← Ideal.over_def (P := Q) (p := Ideal.span {(p : ℤ)})]

-- The statement follows the human-authored specification
-- `TauCetiRoadmap/NumberFieldArithmetic/Suggested.lean`, Layer 3.9, read through
-- `Equiv.Perm.fullCycleType`; the hypotheses `Algebra.adjoin ℚ {θ} = ⊤` and `¬ p ∣ exponent θ`
-- of that specification are not needed, since every root generates its own field and the
-- squarefree reduction already forces `p ∤ exponent` there.
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
  -- The chain of identifications.
  refine (Equiv.Perm.fullCycleType_eq_map_card_orbit _).trans ?_
  refine (TauCeti.map_card_orbit_eq_of_orbit_eq (G' := Subgroup.zpowers σ)
    (orbit_zpowers_galActionHom_restrict_eq σ)).trans ?_
  refine (TauCeti.map_card_orbit_eq_of_orbit_eq (G' := stabilizer (M ≃ₐ[ℚ] M) Q) (fun x =>
    (Ideal.orbit_stabilizer_eq_orbit_zpowers_of_isArithFrobAt Q hσ' x
      (fun τ hτ => inertia_smul_eq_self (p := p) hsq Q hτ x)).symm)).trans ?_
  refine (Equiv.map_card_orbit_eq_of_map_smul (G := stabilizer (M ≃ₐ[ℚ] M) Q)
    (rootSetEquivQuotientStabilizer hα) (rootSetEquivQuotientStabilizer_subgroup_smul hα _)).trans
    ?_
  refine (Ideal.map_card_orbit_stabilizer_eq_map_ramificationIdx_mul_inertiaDeg (Q.under (𝓞 ℚ)) Q
    (stabilizer (M ≃ₐ[ℚ] M) α)).trans ?_
  refine Eq.trans ?_ (map_inertiaDeg_primesOver_eq_map_natDegree_monicFactorsMod (p := p) hα hsq)
  -- Primes above `Q ∩ 𝓞 ℚ` are primes above `p`, with the same residue degree and trivial
  -- ramification.
  have hset := primesOver_under_ringOfIntegers_rat_eq (p := p) Q
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
/-- Dedekind's theorem, stated for any polynomial `g` known to be the minimal polynomial of `θ`
over `ℚ`; this form is convenient when `g` is given first and `θ` is a root of it. -/
theorem fullCycleType_galActionHom_restrict_eq_map_natDegree_monicFactorsMod_of_minpoly_eq
    {g : ℚ[X]} (hg : minpoly ℚ (θ : K) = g)
    (hsq : Squarefree ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))))
    [Fact (g.map (algebraMap ℚ M)).Splits]
    (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver (Ideal.span {(p : ℤ)})]
    {σ : M ≃ₐ[ℚ] M} (hσ : IsArithFrobAt ℤ σ Q) :
    Equiv.Perm.fullCycleType (Gal.galActionHom g M (Gal.restrict g M σ)) =
      (RingOfIntegers.monicFactorsMod θ p).val.map natDegree := by
  subst hg
  exact fullCycleType_galActionHom_restrict_eq_map_natDegree_monicFactorsMod hsq Q hσ

open scoped Classical in
/-- **Dedekind's theorem, with the fixed points counted separately.** The multiset of degrees of
the monic irreducible factors of `minpoly ℤ θ` modulo `p` is the cycle type of a Frobenius at a
prime above `p` acting on the roots of `minpoly ℚ θ`, together with one part `1` for each fixed
root. This is the form of the statement in the roadmap; the full cycle type of
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

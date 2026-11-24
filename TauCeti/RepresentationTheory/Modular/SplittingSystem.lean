/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import TauCeti.RingTheory.Cyclotomic.Basic
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
public import TauCeti.RingTheory.RootsOfUnity.Henselian

/-!
# The splitting modular system of a cyclotomic field

Let `F = ℚ⟮complexRoot e⟯ ⊆ ℂ` (`TauCeti.Cyclotomic.complexField e`), and let `v` be a finite place
of `F` over the prime `p`, that is a height-one prime of `𝓞 F` containing `p`. Write `K = F_v` for
the completion, `O` for its valuation ring and `k` for the residue field of `O`. Then `(K, O, k)` is
a `p`-modular system: `O` is a complete discrete valuation ring (Mathlib's
`IsDiscreteValuationRing` instance and Tau Ceti's `IsAdicComplete` instance) with fraction field
`K`, which has characteristic zero, and `k` has characteristic `p`
(`IsDedekindDomain.HeightOneSpectrum.charP_residueField_adicCompletionIntegers`). It is
splitting for every finite group of exponent dividing `e`, since `K` contains the primitive `e`-th
root of unity `complexRoot e` (`TauCeti.Cyclotomic.isPrimitiveRoot_embedding_zeta`).

Let `e'` be the part of `e` prime to `p`. This file also proves:

* reduction is an isomorphism from the `e'`-th roots of unity of `O` onto those of `k`
  (`IsDedekindDomain.HeightOneSpectrum.rootsOfUnityAdicCompletionIntegersEquiv`, for any order
  prime to `p`, from Hensel's lemma);
* the canonical map `F → K` restricts to an isomorphism from the `e`-th roots of unity of `F` onto
  those of `K` (`TauCeti.Cyclotomic.rootsOfUnityEquivAdicCompletion`);
* `k` is generated over its prime field by the reduction of `complexRoot e'`
  (`TauCeti.Cyclotomic.closure_residue_eq_top_of_coe_eq_complexRoot`). The reduction of
  `complexRoot e` generates `k` because `𝓞 F = ℤ[complexRoot e]`, and `complexRoot e'` is its
  `p ^ a`-th power, where `p ^ a` is the `p`-part of `e`; the `p ^ a`-th power map is an
  automorphism of the finite field `k`.

## Main definitions

* `TauCeti.Cyclotomic.complexField`: the cyclotomic field `ℚ⟮complexRoot e⟯ ⊆ ℂ`, a number field
  and a cyclotomic extension of `ℚ`.
* `TauCeti.Cyclotomic.complexField.zetaInteger`: its generator `complexRoot e`, as an algebraic
  integer.
* `IsDedekindDomain.HeightOneSpectrum.rootsOfUnityAdicCompletionIntegersEquiv`: reduction of
  roots of unity of order prime to `p` at a place over `p`.
* `TauCeti.Cyclotomic.rootsOfUnityEquivAdicCompletion`: the `e`-th roots of unity of `F` and of
  `F_v`.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField IsLocalRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- Every element of the residue field of the completion at `v` is the reduction of an element
of `R`. -/
theorem residue_algebraMap_adicCompletionIntegers_surjective :
    Function.Surjective fun a : R ↦ residue (v.adicCompletionIntegers K)
      (algebraMap R (v.adicCompletionIntegers K) a) := by
  intro y
  obtain ⟨x, hx⟩ := (v.residueFieldEquivAdicCompletionIntegers (K := K)).surjective y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨a, by rw [← hx, residueFieldEquivAdicCompletionIntegers_apply_mk]; rfl⟩

/-- The residue field of the completion at a height-one prime `v` containing the prime `p` has
characteristic `p`. -/
theorem charP_residueField_adicCompletionIntegers (p : ℕ) [Fact p.Prime]
    (hp : (p : R) ∈ v.asIdeal) : CharP (ResidueField (v.adicCompletionIntegers K)) p := by
  rw [CharP.charP_iff_prime_eq_zero Fact.out]
  have : algebraMap R (v.adicCompletionIntegers K) p ∈ maximalIdeal _ := by
    rw [← Ideal.mem_comap, ← Ideal.under_def, under_maximalIdeal_adicCompletionIntegers]
    exact hp
  simpa using (residue_eq_zero_iff _).2 this

/-- At a height-one prime `v` containing the prime `p`, reduction is an isomorphism from the
`n`-th roots of unity of the completed integers onto those of the residue field, for `n` prime
to `p`. -/
def rootsOfUnityAdicCompletionIntegersEquiv (p : ℕ) [Fact p.Prime] (hp : (p : R) ∈ v.asIdeal)
    {n : ℕ} (hn : n.Coprime p) :
    rootsOfUnity n (v.adicCompletionIntegers K) ≃*
      rootsOfUnity n (ResidueField (v.adicCompletionIntegers K)) :=
  have := v.charP_residueField_adicCompletionIntegers (K := K) p hp
  TauCeti.rootsOfUnityEquivResidueField (by
    rw [← residue_ne_zero_iff_isUnit, map_natCast]
    exact fun h ↦ (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hn.symm
      ((CharP.cast_eq_zero_iff _ p n).1 h))

/-- The isomorphism `rootsOfUnityAdicCompletionIntegersEquiv` is reduction modulo the maximal
ideal. -/
@[simp]
theorem coe_rootsOfUnityAdicCompletionIntegersEquiv (p : ℕ) [Fact p.Prime]
    (hp : (p : R) ∈ v.asIdeal) {n : ℕ} (hn : n.Coprime p)
    (ζ : rootsOfUnity n (v.adicCompletionIntegers K)) :
    ((v.rootsOfUnityAdicCompletionIntegersEquiv p hp hn ζ :
        (ResidueField (v.adicCompletionIntegers K))ˣ) : ResidueField (v.adicCompletionIntegers K)) =
      residue _ ((ζ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) :=
  TauCeti.coe_rootsOfUnityEquivResidueField _ ζ

end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti.Cyclotomic

open IntermediateField HeightOneSpectrum

/-- The cyclotomic field `ℚ⟮complexRoot e⟯ ⊆ ℂ`. -/
def complexField (e : ℕ) : IntermediateField ℚ ℂ := ℚ⟮complexRoot e⟯

/-- A power of a distinguished root of unity: `complexRoot (m * n) ^ m = complexRoot n`. -/
theorem complexRoot_mul_pow {m : ℕ} (hm : m ≠ 0) (n : ℕ) :
    complexRoot (m * n) ^ m = complexRoot n := by
  rw [complexRoot_def, complexRoot_def, ← Complex.exp_natCast_mul]
  congr 1
  push_cast
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  field_simp

/-- The power of `complexRoot e` by the `p`-part of `e` is `complexRoot e'`, with `e'` the part
of `e` prime to `p`. -/
theorem complexRoot_pow_ordProj (e : ℕ) [NeZero e] (p : ℕ) :
    complexRoot e ^ ordProj[p] e = complexRoot (ordCompl[p] e) := by
  have he : ordProj[p] e ≠ 0 := by
    intro h
    have := Nat.ordProj_mul_ordCompl_eq_self e p
    rw [h, zero_mul] at this
    exact NeZero.ne e this.symm
  have := complexRoot_mul_pow he (ordCompl[p] e)
  rwa [Nat.ordProj_mul_ordCompl_eq_self] at this

section complexField

variable (e : ℕ)

/-- The generator `complexRoot e` of `complexField e`. -/
def complexField.zeta : complexField e :=
  ⟨complexRoot e, IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩

@[simp]
theorem complexField.coe_zeta : (complexField.zeta e : ℂ) = complexRoot e := rfl

variable [NeZero e]

instance isCyclotomicExtension_complexField : IsCyclotomicExtension {e} ℚ (complexField e) :=
  (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin e ℚ ℂ _
    isPrimitiveRoot_complexRoot).mpr rfl

instance numberField_complexField : NumberField (complexField e) :=
  IsCyclotomicExtension.numberField {e} ℚ _

theorem complexField.isPrimitiveRoot_zeta : IsPrimitiveRoot (complexField.zeta e) e :=
  IsPrimitiveRoot.coe_submonoidClass_iff.mp isPrimitiveRoot_complexRoot

/-- The generator `complexRoot e` of `complexField e`, as an algebraic integer. -/
def complexField.zetaInteger : 𝓞 (complexField e) :=
  (complexField.isPrimitiveRoot_zeta e).toInteger

@[simp]
theorem complexField.coe_zetaInteger :
    ((complexField.zetaInteger e : complexField e) : ℂ) = complexRoot e := rfl

theorem complexField.isPrimitiveRoot_zetaInteger :
    IsPrimitiveRoot (complexField.zetaInteger e) e :=
  (complexField.isPrimitiveRoot_zeta e).toInteger_isPrimitiveRoot

end complexField

section Place

variable {e : ℕ} [NeZero e] (v : HeightOneSpectrum (𝓞 (complexField e)))

local notation "F" => complexField e
local notation "O" => v.adicCompletionIntegers (complexField e)

/-- The reduction of `complexRoot e` at `v`, an element of the residue field of `F_v`. -/
local notation "ρ" => residue O (algebraMap (𝓞 F) O (complexField.zetaInteger e))

/-- The completed integers `O` of `F_v` contain the primitive `e`-th root of unity
`complexRoot e`. -/
theorem isPrimitiveRoot_algebraMap_zetaInteger :
    IsPrimitiveRoot (algebraMap (𝓞 F) O (complexField.zetaInteger e)) e :=
  (complexField.isPrimitiveRoot_zetaInteger e).map_of_injective
    (FaithfulSMul.algebraMap_injective _ _)

/-- The completion `F_v` contains the primitive `e`-th root of unity `complexRoot e`, so it splits
every finite group of exponent dividing `e`. -/
theorem isPrimitiveRoot_embedding_zeta :
    IsPrimitiveRoot (FinitePlace.embedding (K := F) v (complexField.zeta e)) e :=
  (complexField.isPrimitiveRoot_zeta e).map_of_injective
    (FinitePlace.embedding (K := F) v).injective

/-- The canonical map `F → F_v` is a bijection on `e`-th roots of unity. -/
theorem restrictRootsOfUnity_embedding_bijective :
    Function.Bijective (restrictRootsOfUnity (FinitePlace.embedding (K := F) v) e) := by
  have hinj : Function.Injective (restrictRootsOfUnity (FinitePlace.embedding (K := F) v) e) := by
    intro a b h
    ext
    have := congrArg (fun x : rootsOfUnity e (v.adicCompletion F) ↦
      ((x : (v.adicCompletion F)ˣ) : v.adicCompletion F)) h
    simpa using (FinitePlace.embedding v).injective this
  refine hinj.bijective_of_nat_card_le ?_
  rw [(complexField.isPrimitiveRoot_zeta e).card_rootsOfUnity,
    (isPrimitiveRoot_embedding_zeta v).card_rootsOfUnity]

/-- The canonical map `F → F_v` as an isomorphism between the groups of `e`-th roots of unity. -/
def rootsOfUnityEquivAdicCompletion : rootsOfUnity e F ≃* rootsOfUnity e (v.adicCompletion F) :=
  MulEquiv.ofBijective _ (restrictRootsOfUnity_embedding_bijective v)

/-- The isomorphism `rootsOfUnityEquivAdicCompletion` is the canonical map `F → F_v`. -/
@[simp]
theorem coe_rootsOfUnityEquivAdicCompletion (ζ : rootsOfUnity e F) :
    ((rootsOfUnityEquivAdicCompletion v ζ : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      FinitePlace.embedding v ((ζ : Fˣ) : F) :=
  restrictRootsOfUnity_coe_apply _ _

/-- The residue field of `F_v` is generated by the reduction of `complexRoot e`: the ring of
integers of `F` is `ℤ[complexRoot e]`, and it maps onto the residue field. -/
theorem closure_residue_zetaInteger_eq_top : Subring.closure {ρ} = ⊤ := by
  refine eq_top_iff.2 fun y _ ↦ ?_
  obtain ⟨a, rfl⟩ := v.residue_algebraMap_adicCompletionIntegers_surjective (K := F) y
  have ha : a ∈ Subring.closure {complexField.zetaInteger e} := by
    have h := IsCyclotomicExtension.Rat.adjoin_singleton_eq_top
      (complexField.isPrimitiveRoot_zeta e)
    have : a ∈ Algebra.adjoin ℤ {complexField.zetaInteger e} := h ▸ Algebra.mem_top
    rwa [Algebra.adjoin_int] at this
  have : (residue O).comp (algebraMap (𝓞 F) O) a ∈
      (Subring.closure {complexField.zetaInteger e}).map ((residue O).comp (algebraMap (𝓞 F) O)) :=
    Subring.mem_map.2 ⟨a, ha, rfl⟩
  rwa [RingHom.map_closure, Set.image_singleton] at this

/-- The power of `complexRoot e` by the `p`-part of `e` is `complexRoot e'`, with `e'` the part
of `e` prime to `p`. -/
theorem zetaInteger_pow_ordProj (p : ℕ) {x : 𝓞 F}
    (hx : ((x : F) : ℂ) = complexRoot (ordCompl[p] e)) :
    complexField.zetaInteger e ^ (ordProj[p] e) = x := by
  let ψ : 𝓞 F →+* ℂ := (complexField e).val.toRingHom.comp (algebraMap (𝓞 F) F)
  have hψ : Function.Injective ψ :=
    Subtype.val_injective.comp (FaithfulSMul.algebraMap_injective (𝓞 F) F)
  apply hψ
  rw [map_pow]
  change complexRoot e ^ ordProj[p] e = ((x : F) : ℂ)
  rw [hx, complexRoot_pow_ordProj]

/-- **The residue field of `F_v` is generated by the reduction of `complexRoot e'`**, where `v`
lies over the prime `p` and `e'` is the part of `e` prime to `p`. Here `x` is `complexRoot e'`,
written as an algebraic integer of `F`. -/
theorem closure_residue_eq_top_of_coe_eq_complexRoot (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞 F) ∈ v.asIdeal) {x : 𝓞 F} (hx : ((x : F) : ℂ) = complexRoot (ordCompl[p] e)) :
    Subring.closure {residue O (algebraMap (𝓞 F) O x)} = ⊤ := by
  have := v.charP_residueField_adicCompletionIntegers (K := F) p hp
  set φ := iterateFrobenius (ResidueField O) p (e.factorization p)
  have hφ : Function.Surjective φ := Finite.surjective_of_injective φ.injective
  have hx' : residue O (algebraMap (𝓞 F) O x) = φ ρ := by
    rw [← zetaInteger_pow_ordProj p hx, map_pow, map_pow, iterateFrobenius_def]
  rw [hx', ← Set.image_singleton, ← RingHom.map_closure, closure_residue_zetaInteger_eq_top,
    ← RingHom.range_eq_map, RingHom.range_eq_top.2 hφ]

/-- The algebraic integer `complexRoot e'` of `F`, with `e'` the part of `e` prime to `p`, exists:
it is a power of `complexRoot e`. -/
theorem exists_coe_eq_complexRoot_ordCompl (p : ℕ) :
    ∃ x : 𝓞 F, ((x : F) : ℂ) = complexRoot (ordCompl[p] e) := by
  refine ⟨complexField.zetaInteger e ^ (ordProj[p] e), ?_⟩
  change ((complexField e).val.toRingHom.comp (algebraMap (𝓞 F) F))
    (complexField.zetaInteger e ^ (ordProj[p] e)) = _
  rw [map_pow]
  exact complexRoot_pow_ordProj e p

/-- When `e` is a power of `p`, so that `e' = 1`, the residue field of `F_v` at a place over `p`
is the prime field: it has `p` elements. -/
theorem natCard_residueField_of_ordCompl_eq_one (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞 F) ∈ v.asIdeal) (he : ordCompl[p] e = 1) :
    Nat.card (ResidueField O) = p := by
  have := v.charP_residueField_adicCompletionIntegers (K := F) p hp
  obtain ⟨x, hx⟩ := exists_coe_eq_complexRoot_ordCompl (e := e) p
  have hx1 : x = 1 := by
    apply Subtype.val_injective.comp (FaithfulSMul.algebraMap_injective (𝓞 F) F)
    change ((x : F) : ℂ) = 1
    rw [hx, he, complexRoot_def, Nat.cast_one, div_one, Complex.exp_two_pi_mul_I]
  have htop := closure_residue_eq_top_of_coe_eq_complexRoot v p hp hx
  rw [hx1, map_one, map_one] at htop
  let χ := ZMod.castHom (dvd_refl p) (ResidueField O)
  have hχ : Function.Bijective χ := by
    refine ⟨χ.injective, RingHom.range_eq_top.1 (eq_top_iff.2 ?_)⟩
    rw [← htop, Subring.closure_le, Set.singleton_subset_iff]
    exact ⟨1, map_one χ⟩
  rw [← Nat.card_eq_of_bijective χ hχ, Nat.card_zmod]

end Place

end TauCeti.Cyclotomic

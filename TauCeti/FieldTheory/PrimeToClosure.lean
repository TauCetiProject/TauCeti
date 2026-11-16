/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Order.Minimal
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.GroupTheory.Sylow
import Mathlib.Order.Zorn
import TauCeti.FieldTheory.IntermediateField.ScalarTower
import TauCeti.FieldTheory.Normal.FixedField

/-!
# Prime-to-`p` closures of a field

Fix a natural number `p` and a field extension `E / F`. An intermediate field `K` of `E / F` has
*prime-to-`p` degree* (`IntermediateField.IsPrimeToDegree p K`) if every subextension of `K / F`
that is finite over `F` has degree coprime to `p`. A *prime-to-`p` closure* of `F` in `E` is an
intermediate field that is maximal for this property; such fields exist by Zorn's lemma.

The main theorem is that, when `E / F` is normal and `p` is prime, every finite extension of a
prime-to-`p` closure `K` inside `E` has `p`-power degree; when `E` is an algebraic closure of `F`
this holds for every finite field extension of `K`. Together with prime-to-`p` degree this
characterizes the prime-to-`p` closures. Transfer arguments use these fields to reduce statements
about `p`-primary phenomena over `F` to extensions of `p`-power degree, since every finite
subextension of a prime-to-`p` closure has degree prime to `p` over `F`.

## Main definitions

* `IntermediateField.IsPrimeToDegree p K`: every subextension of `K` finite over `F` has degree
  coprime to `p`. A prime-to-`p` closure is a `Maximal (IsPrimeToDegree p)` intermediate field.

## Main results

* `IntermediateField.exists_le_maximal_isPrimeToDegree`: every intermediate field of prime-to-`p`
  degree lies in a prime-to-`p` closure.
* `IntermediateField.IsPrimeToDegree.restrictScalars_adjoin_simple`: adjoining to a field of
  prime-to-`p` degree an algebraic element of relative degree prime to `p` keeps prime-to-`p`
  degree.
* `IntermediateField.exists_finrank_eq_pow_of_maximal_isPrimeToDegree`: if `E / F` is normal and
  `p` is prime, every finite extension of a prime-to-`p` closure inside `E` has `p`-power degree.
* `IntermediateField.maximal_isPrimeToDegree_iff`: the prime-to-`p` closures are exactly the
  intermediate fields of prime-to-`p` degree all of whose finite extensions in `E` have
  `p`-power degree.
* `IntermediateField.exists_finrank_eq_pow_of_isAlgClosure`: inside an algebraic closure, every
  finite field extension of a prime-to-`p` closure has `p`-power degree.

## References

* C. Weibel, *The K-book: an introduction to algebraic K-theory*, Chapter III, the paragraph
  after Theorem 7.6.1 (p. 249), where these fields are used for Milnor K-theory.
-/

public section

open Module Polynomial

namespace IntermediateField

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

section Basic

variable (p : ℕ)

/-- An intermediate field `K` of `E / F` has prime-to-`p` degree if every subextension of `K`
that is finite over `F` has degree over `F` coprime to `p`. -/
def IsPrimeToDegree (K : IntermediateField F E) : Prop :=
  ∀ L : IntermediateField F E, L ≤ K → FiniteDimensional F L → (finrank F L).Coprime p

variable {p} {K L : IntermediateField F E}

/-- Unfolding `IsPrimeToDegree`. -/
theorem isPrimeToDegree_iff : IsPrimeToDegree p K ↔
    ∀ L : IntermediateField F E, L ≤ K → FiniteDimensional F L → (finrank F L).Coprime p :=
  Iff.rfl

/-- A subextension of a field of prime-to-`p` degree that is finite over `F` has degree coprime
to `p`. -/
theorem IsPrimeToDegree.coprime_finrank (hK : IsPrimeToDegree p K) (hL : L ≤ K)
    [FiniteDimensional F L] : (finrank F L).Coprime p :=
  hK L hL inferInstance

/-- A subfield of a field of prime-to-`p` degree has prime-to-`p` degree. -/
theorem IsPrimeToDegree.mono (hL : IsPrimeToDegree p L) (h : K ≤ L) : IsPrimeToDegree p K :=
  fun M hM hfin ↦ hL M (hM.trans h) hfin

/-- A finite subextension has prime-to-`p` degree exactly when its degree is coprime to `p`. -/
theorem isPrimeToDegree_iff_coprime_finrank [FiniteDimensional F K] :
    IsPrimeToDegree p K ↔ (finrank F K).Coprime p :=
  ⟨fun hK ↦ hK.coprime_finrank le_rfl,
    fun hK _ hL _ ↦ Nat.Coprime.coprime_dvd_left (finrank_dvd_of_le_right hL) hK⟩

/-- The base field has prime-to-`p` degree. -/
@[simp]
theorem isPrimeToDegree_bot : IsPrimeToDegree p (⊥ : IntermediateField F E) := by
  rw [isPrimeToDegree_iff_coprime_finrank, IntermediateField.finrank_bot]
  exact Nat.coprime_one_left p

/-- Prime-to-`p` degree is closed under unions of directed families: a finite subextension of
the union lies in one member of the family. -/
theorem isPrimeToDegree_sSup {c : Set (IntermediateField F E)} (hc : DirectedOn (· ≤ ·) c)
    (h : ∀ K ∈ c, IsPrimeToDegree p K) : IsPrimeToDegree p (sSup c) := by
  rcases c.eq_empty_or_nonempty with rfl | hne
  · rw [sSup_empty]
    exact isPrimeToDegree_bot
  intro L hL hfin
  obtain ⟨t, ht, rfl⟩ := fg_def.mp <| fg_of_fg_toSubalgebra L <|
    Subalgebra.fg_of_fg_toSubmodule (Module.Finite.iff_fg.mp hfin)
  obtain ⟨K, hKc, hLK⟩ := (isCompactElement_iff_le_of_directed_sSup_le _).mp
    (adjoin_finite_isCompactElement ht) c hne hc hL
  exact h K hKc _ hLK hfin

/-- Every intermediate field of prime-to-`p` degree is contained in a prime-to-`p` closure. -/
theorem exists_le_maximal_isPrimeToDegree (hK : IsPrimeToDegree p K) :
    ∃ M, K ≤ M ∧ Maximal (IsPrimeToDegree p) M := by
  refine zorn_le_nonempty₀ {M | IsPrimeToDegree p M} (fun c hcs hc _ _ ↦ ?_) K hK
  exact ⟨sSup c, isPrimeToDegree_sSup hc.directedOn hcs, fun _ hz ↦ le_sSup hz⟩

variable (p F E) in
/-- Every field extension contains a prime-to-`p` closure of the base field. -/
theorem exists_maximal_isPrimeToDegree :
    ∃ M : IntermediateField F E, Maximal (IsPrimeToDegree p) M :=
  (exists_le_maximal_isPrimeToDegree isPrimeToDegree_bot).imp fun _ h ↦ h.2

end Basic

section Algebraic

variable [Algebra.IsAlgebraic F E] {p : ℕ} {K : IntermediateField F E}

/-- Every subextension of `K⟮x⟯ / F` that is finite over `F` lies in `K₀⟮x⟯` for a subfield
`K₀ ⊆ K` finite over `F` over which `x` has the same degree as over `K`: take for `K₀` the field
generated by the coefficients of the minimal polynomial of `x` over `K` and of polynomial
expressions in `x` for a basis of the subextension. -/
private theorem exists_finiteDimensional_le_adjoin_simple (K : IntermediateField F E) (x : E)
    (L : IntermediateField F E) [FiniteDimensional F L] (hL : L ≤ K⟮x⟯.restrictScalars F) :
    ∃ K₀ : IntermediateField F E, K₀ ≤ K ∧ FiniteDimensional F K₀ ∧
      finrank K₀ K₀⟮x⟯ = finrank K K⟮x⟯ ∧ L ≤ K₀⟮x⟯.restrictScalars F := by
  classical
  have hx : IsIntegral K x := (Algebra.IsIntegral.isIntegral (R := F) x).tower_top
  have hpoly (y : E) (hy : y ∈ K⟮x⟯) : ∃ q : K[X], aeval x q = y := by
    rwa [← mem_toSubalgebra, adjoin_simple_toSubalgebra_of_isAlgebraic hx.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at hy
  let b := Module.finBasis F L
  choose q hq using fun i ↦ hpoly (b i) (hL (b i).2)
  let T : Finset K := (minpoly K x).coeffs ∪ Finset.univ.biUnion fun i ↦ (q i).coeffs
  let K₀ : IntermediateField F E := adjoin F (((↑) : K → E) '' T)
  have hK₀ : K₀ ≤ K := adjoin_le_iff.2 (by rintro _ ⟨c, -, rfl⟩; exact c.2)
  have hfin : FiniteDimensional F K₀ :=
    finiteDimensional_adjoin fun y _ ↦ Algebra.IsIntegral.isIntegral y
  let : Algebra K₀ K := (inclusion hK₀).toRingHom.toAlgebra
  have : IsScalarTower K₀ K E := .of_algebraMap_eq fun _ ↦ rfl
  -- A polynomial over `K` whose coefficients lie in `T` is defined over `K₀`.
  have hlifts (g : K[X]) (hg : g.coeffs ⊆ T) : g ∈ lifts (algebraMap K₀ K) :=
    (lifts_iff_coeffs_subset_range g).2 fun c hc ↦
      ⟨⟨c, subset_adjoin F _ ⟨c, hg hc, rfl⟩⟩, rfl⟩
  obtain ⟨g₀, hg₀map, hg₀deg, hg₀monic⟩ :=
    lifts_and_natDegree_eq_and_monic (hlifts _ fun c hc ↦ Finset.mem_union_left _ hc)
      (minpoly.monic hx)
  have hg₀ : g₀ = minpoly K₀ x := by
    refine minpoly.eq_of_irreducible_of_monic ?_ ?_ hg₀monic
    · refine Monic.irreducible_of_irreducible_map (algebraMap K₀ K) g₀ hg₀monic ?_
      rw [hg₀map]
      exact minpoly.irreducible hx
    · rw [← aeval_map_algebraMap K, hg₀map, minpoly.aeval]
  have hx₀ : IsIntegral K₀ x := (Algebra.IsIntegral.isIntegral (R := F) x).tower_top
  refine ⟨K₀, hK₀, hfin, ?_, fun y hy ↦ ?_⟩
  · rw [adjoin.finrank hx₀, adjoin.finrank hx, ← hg₀, hg₀deg]
  have hb (i) : (b i : E) ∈ K₀⟮x⟯.restrictScalars F := by
    obtain ⟨g, hg⟩ := hlifts (q i) fun c hc ↦
      Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hc⟩)
    rw [mem_restrictScalars, ← hq i, ← hg, coe_mapRingHom, aeval_map_algebraMap]
    exact algebra_adjoin_le_adjoin K₀ _ (aeval_mem_adjoin_singleton K₀ x)
  rw [show y = ((⟨y, hy⟩ : L) : E) from rfl, ← b.sum_repr ⟨y, hy⟩, coe_sum]
  exact sum_mem fun i _ ↦ smul_mem _ (hb i)

/-- Adjoining to a field of prime-to-`p` degree an element whose degree over it is prime to `p`
gives a field of prime-to-`p` degree. -/
theorem IsPrimeToDegree.restrictScalars_adjoin_simple (hK : IsPrimeToDegree p K) {x : E}
    (hx : (finrank K K⟮x⟯).Coprime p) : IsPrimeToDegree p (K⟮x⟯.restrictScalars F) := by
  intro L hL _
  obtain ⟨K₀, hK₀, _, hdeg, hLK₀⟩ := exists_finiteDimensional_le_adjoin_simple K x L hL
  have := adjoin.finiteDimensional ((Algebra.IsIntegral.isIntegral (R := F) x).tower_top :
    IsIntegral K₀ x)
  refine Nat.Coprime.coprime_dvd_left (finrank_dvd_of_le_right hLK₀) ?_
  rw [(restrictScalarsAlgEquiv F K₀⟮x⟯).toLinearEquiv.finrank_eq,
    ← Module.finrank_mul_finrank F K₀ K₀⟮x⟯]
  exact Nat.Coprime.mul_left (hK.coprime_finrank hK₀) (hdeg ▸ hx)

/-- An element of degree prime to `p` over a prime-to-`p` closure `K` lies in `K`. -/
private theorem mem_of_maximal_isPrimeToDegree (hK : Maximal (IsPrimeToDegree p) K) {x : E}
    (hx : (finrank K K⟮x⟯).Coprime p) : x ∈ K := by
  have hle : K ≤ K⟮x⟯.restrictScalars F := fun y hy ↦
    (mem_restrictScalars F).2 ((K⟮x⟯).algebraMap_mem ⟨y, hy⟩)
  exact (hK.eq_of_le (hK.prop.restrictScalars_adjoin_simple hx) hle).ge
    ((mem_restrictScalars F).2 (mem_adjoin_simple_self K x))

/-- A prime-to-`p` closure `K` has no proper finite extension of degree prime to `p` inside
`E`. -/
theorem eq_bot_of_maximal_isPrimeToDegree (hK : Maximal (IsPrimeToDegree p) K)
    (N : IntermediateField K E) (hN : (finrank K N).Coprime p) : N = ⊥ := by
  refine eq_bot_iff.2 fun x hx ↦ mem_bot.2 ⟨⟨x, mem_of_maximal_isPrimeToDegree hK ?_⟩, rfl⟩
  exact Nat.Coprime.coprime_dvd_left (finrank_dvd_of_le_right (adjoin_simple_le_iff.2 hx)) hN

end Algebraic

section Normal

variable [Normal F E] {p : ℕ} {K : IntermediateField F E}

/-- The Sylow step: a finite separable extension of a prime-to-`p` closure inside a normal
extension has `p`-power degree. The fixed field of a Sylow `p`-subgroup of the Galois group of its
normal closure has degree prime to `p`, so it is trivial. -/
private theorem exists_finrank_eq_pow_of_isSeparable (hp : p.Prime)
    (hK : Maximal (IsPrimeToDegree p) K) (N : IntermediateField K E) [FiniteDimensional K N]
    [Algebra.IsSeparable K N] : ∃ n, finrank K N = p ^ n := by
  have := Fact.mk hp
  have : Normal K E := Normal.tower_top_of_normal F K E
  let M := normalClosure K N E
  obtain ⟨P⟩ : Nonempty (Sylow p Gal(M/K)) := inferInstance
  let H := fixedField (P : Subgroup Gal(M/K))
  have hH : finrank K H * Nat.card P = Nat.card Gal(M/K) := by
    rw [← finrank_fixedField_eq_card, Module.finrank_mul_finrank, IsGalois.card_aut_eq_finrank]
  have hidx : finrank K H = (P : Subgroup Gal(M/K)).index := by
    refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := P)) ?_
    rw [hH, mul_comm, Subgroup.card_mul_index]
  have hbot : lift H = ⊥ := eq_bot_of_maximal_isPrimeToDegree hK (lift H) <| by
    rw [← (liftAlgEquiv H).toLinearEquiv.finrank_eq, hidx]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 P.not_dvd_index)
  have h1 : finrank K H = 1 := by
    rw [(liftAlgEquiv H).toLinearEquiv.finrank_eq, hbot, IntermediateField.finrank_bot]
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 P.isPGroup
  have hdvd : finrank K N ∣ p ^ n := by
    rw [← hn, ← one_mul (Nat.card P), ← h1, hH, IsGalois.card_aut_eq_finrank]
    exact finrank_dvd_of_le_right (le_normalClosure N)
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  exact ⟨m, hm⟩

/-- If the exponential characteristic of a prime-to-`p` closure `K` is not `p`, every finite
extension of `K` inside a normal extension is separable: the purely inseparable part of its
normal closure has degree prime to `p`, so it is trivial. -/
private theorem isSeparable_of_maximal_isPrimeToDegree (hp : p.Prime)
    (hK : Maximal (IsPrimeToDegree p) K) (q : ℕ) [ExpChar K q] (hqp : q ≠ p)
    (L : IntermediateField K E) [FiniteDimensional K L] : Algebra.IsSeparable K L := by
  have : Normal K E := Normal.tower_top_of_normal F K E
  let M := normalClosure K L E
  let I := fixedField (⊤ : Subgroup Gal(M/K))
  have := TauCeti.IntermediateField.isPurelyInseparable_fixedField_top K M
  obtain ⟨n, hn⟩ := IsPurelyInseparable.finrank_eq_pow K I q
  have hqp' : q.Coprime p := (expChar_is_prime_or_one K q).elim
    (fun hq ↦ (Nat.coprime_primes hq hp).2 hqp) fun hq ↦ hq ▸ Nat.coprime_one_left p
  have hbot : lift I = ⊥ := eq_bot_of_maximal_isPrimeToDegree hK (lift I) <| by
    rw [← (liftAlgEquiv I).toLinearEquiv.finrank_eq, hn]
    exact hqp'.pow_left n
  have hI : I = ⊥ := by
    rw [← finrank_eq_one_iff, (liftAlgEquiv I).toLinearEquiv.finrank_eq, hbot,
      IntermediateField.finrank_bot]
  have := IsGalois.of_fixedField_eq_bot K M hI
  exact Algebra.IsSeparable.of_algHom K M (inclusion (le_normalClosure L))

/-- **Finite extensions of a prime-to-`p` closure have `p`-power degree.** If `E / F` is normal,
`p` is prime and `K` is a prime-to-`p` closure of `F` in `E`, then every finite extension of `K`
inside `E` has degree a power of `p`. -/
theorem exists_finrank_eq_pow_of_maximal_isPrimeToDegree (hp : p.Prime)
    (hK : Maximal (IsPrimeToDegree p) K) (L : IntermediateField K E) [FiniteDimensional K L] :
    ∃ n, finrank K L = p ^ n := by
  obtain ⟨q, _⟩ : ∃ q, ExpChar K q := ⟨ringExpChar K, inferInstance⟩
  by_cases hqp : q = p
  · -- The separable part has `p`-power degree, and so does the purely inseparable part.
    subst hqp
    let S := separableClosure K L
    have : FiniteDimensional K (lift S) := (liftAlgEquiv S).toLinearEquiv.finiteDimensional
    have : Algebra.IsSeparable K (lift S) := AlgEquiv.Algebra.isSeparable (liftAlgEquiv S)
    obtain ⟨a, ha⟩ := exists_finrank_eq_pow_of_isSeparable hp hK (lift S)
    obtain ⟨b, hb⟩ := IsPurelyInseparable.finrank_eq_pow S L q
    refine ⟨a + b, ?_⟩
    rw [← Module.finrank_mul_finrank K S L, (liftAlgEquiv S).toLinearEquiv.finrank_eq, ha, hb,
      pow_add]
  · have := isSeparable_of_maximal_isPrimeToDegree hp hK q hqp L
    exact exists_finrank_eq_pow_of_isSeparable hp hK L

/-- **Characterization of prime-to-`p` closures.** In a normal extension `E / F`, an
intermediate field is a prime-to-`p` closure of `F` exactly when it has prime-to-`p` degree and
each of its finite extensions inside `E` has `p`-power degree. -/
theorem maximal_isPrimeToDegree_iff (hp : p.Prime) :
    Maximal (IsPrimeToDegree p) K ↔ IsPrimeToDegree p K ∧
      ∀ L : IntermediateField K E, FiniteDimensional K L → ∃ n, finrank K L = p ^ n := by
  refine ⟨fun hK ↦ ⟨hK.prop, fun L _ ↦ exists_finrank_eq_pow_of_maximal_isPrimeToDegree hp hK L⟩,
    fun ⟨hK, hpow⟩ ↦ ⟨hK, fun K' hK' hle x hx ↦ ?_⟩⟩
  have := adjoin.finiteDimensional ((Algebra.IsIntegral.isIntegral (R := F) x).tower_top :
    IsIntegral K x)
  obtain ⟨n, hn⟩ := hpow K⟮x⟯ inferInstance
  obtain ⟨K₀, hK₀, _, hdeg, -⟩ := exists_finiteDimensional_le_adjoin_simple K x ⊥ bot_le
  have := adjoin.finiteDimensional ((Algebra.IsIntegral.isIntegral (R := F) x).tower_top :
    IsIntegral K₀ x)
  have : FiniteDimensional F K₀⟮x⟯ := FiniteDimensional.trans F K₀ K₀⟮x⟯
  have : FiniteDimensional F (K₀⟮x⟯.restrictScalars F) :=
    (restrictScalarsAlgEquiv F K₀⟮x⟯).symm.toLinearEquiv.finiteDimensional
  have hle' : K₀⟮x⟯.restrictScalars F ≤ K' := by
    rw [restrictScalars_adjoin, adjoin_le_iff, Set.union_subset_iff, Set.singleton_subset_iff]
    exact ⟨fun y hy ↦ hle (hK₀ hy), hx⟩
  -- `K₀⟮x⟯ ⊆ K'` has degree `[K₀ : F] * p ^ n` over `F`, which is prime to `p`, so `n = 0`.
  have hcop := hK'.coprime_finrank hle'
  rw [(restrictScalarsAlgEquiv F K₀⟮x⟯).toLinearEquiv.finrank_eq,
    ← Module.finrank_mul_finrank F K₀ K₀⟮x⟯, hdeg, hn] at hcop
  have hn0 : n = 0 := by
    by_contra h
    have := Nat.Coprime.coprime_dvd_left (dvd_pow_self p h) (Nat.Coprime.coprime_mul_left hcop)
    exact hp.one_lt.ne' ((Nat.coprime_self p).1 this)
  rw [hn0, pow_zero, finrank_eq_one_iff, adjoin_simple_eq_bot_iff] at hn
  obtain ⟨y, rfl⟩ := mem_bot.1 hn
  exact y.2

end Normal

variable {p : ℕ} {K : IntermediateField F E}

/-- **Finite extensions of a prime-to-`p` closure in an algebraic closure.** If `E` is an
algebraic closure of `F`, `p` is prime and `K` is a prime-to-`p` closure of `F` in `E`, then every
finite field extension of `K` has degree a power of `p`. -/
theorem exists_finrank_eq_pow_of_isAlgClosure [IsAlgClosure F E] (hp : p.Prime)
    (hK : Maximal (IsPrimeToDegree p) K) (L : Type*) [Field L] [Algebra K L]
    [FiniteDimensional K L] : ∃ n, finrank K L = p ^ n := by
  have : IsAlgClosed E := IsAlgClosure.isAlgClosed F
  let φ : L →ₐ[K] E := IsAlgClosed.lift
  let e := AlgEquiv.ofInjectiveField φ
  have : FiniteDimensional K φ.fieldRange := e.toLinearEquiv.finiteDimensional
  obtain ⟨n, hn⟩ := exists_finrank_eq_pow_of_maximal_isPrimeToDegree hp hK φ.fieldRange
  exact ⟨n, e.toLinearEquiv.finrank_eq.trans hn⟩

end IntermediateField

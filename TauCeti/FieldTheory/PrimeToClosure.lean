/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.FieldTheory.PExtension
import Mathlib.FieldTheory.Galois.Sylow
import Mathlib.FieldTheory.PurelyInseparable.Basic
import TauCeti.FieldTheory.Normal.FixedField

/-!
# Prime-to-`p` closures of a field

Fix a field extension `E / F` and a set `P` of natural numbers. By Zorn's lemma, every
`P`-subextension of `E / F` (`TauCeti.IsPExtension`: algebraic, and every finite subextension has
a `P`-number as its degree) lies in a maximal one (`TauCeti.exists_le_maximal_isPExtension`), and
a maximal `P`-subextension `K` has no proper `P`-extension inside `E`
(`TauCeti.eq_bot_of_maximal_isPExtension`).

For a prime `p` and `P = {p}ᶜ`, the `P`-numbers are the positive numbers prime to `p`, and a
maximal `{p}ᶜ`-subextension of `E / F` is a *prime-to-`p` closure* of `F` in `E`: a maximal
algebraic extension of `F` inside `E` whose finite subextensions all have degree prime to `p`. The
main theorem is that, when `E / F` is normal, every finite extension of a prime-to-`p` closure `K`
inside `E` has `p`-power degree; when `E` is an algebraic closure of `F` this holds for every
finite field extension of `K`. Together with prime-to-`p` degree this characterizes the
prime-to-`p` closures. Transfer arguments use these fields to reduce statements about
`p`-primary phenomena over `F` to extensions of `p`-power degree, since every finite
subextension of a prime-to-`p` closure has degree prime to `p` over `F`.

## Main results

* `TauCeti.exists_finrank_eq_pow_of_maximal_isPExtension`: if `E / F` is normal, every
  finite extension of a prime-to-`p` closure inside `E` has `p`-power degree.
* `TauCeti.maximal_isPExtension_compl_singleton_iff`: for a prime `p` and `E / F` normal, the
  prime-to-`p` closures are exactly the `{p}ᶜ`-subextensions all of whose finite extensions in `E`
  have `p`-power degree.
* `TauCeti.exists_finrank_eq_pow_of_maximal_isPExtension_of_isAlgClosure`: inside an
  algebraic closure, every finite field extension of a prime-to-`p` closure has `p`-power degree.

## References

* C. Weibel, *The K-book: an introduction to algebraic K-theory*, Chapter III, the paragraph
  after Theorem 7.6.1 (p. 249), where these fields are used for Milnor K-theory.
-/

public section

open Module IntermediateField

namespace TauCeti

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

section Maximal

variable {P : Set ℕ} {K : IntermediateField F E}

/-- Over a maximal `P`-subextension `K`, a subextension `H` of an extension `M / K` inside `E`
whose degree is a `P`-number is trivial. -/
private theorem finrank_eq_one_of_maximal_isPExtension
    (hK : Maximal (fun M : IntermediateField F E ↦ IsPExtension P F M) K)
    {M : IntermediateField K E} (H : IntermediateField K M) (hH : IsPNumber P (finrank K H)) :
    finrank K H = 1 := by
  have : FiniteDimensional K H := Module.finite_of_finrank_pos hH.pos
  have hbot : lift H = ⊥ := eq_bot_of_maximal_isPExtension hK <|
    (isPExtension_congr (liftAlgEquiv H)).1 (isPExtension_iff_isPNumber_finrank.2 hH)
  rw [(liftAlgEquiv H).toLinearEquiv.finrank_eq, hbot, IntermediateField.finrank_bot]

end Maximal

section Normal

variable [Normal F E] {p : ℕ} {K : IntermediateField F E}

/-- The Sylow step: a finite separable extension of a prime-to-`p` closure inside a normal
extension has `p`-power degree. In the Galois closure `M`, a field `O` with `[M : O]` the
`p`-part of `[M : K]` has degree prime to `p` over `K`, so it is `K`. -/
private theorem exists_finrank_eq_pow_of_isSeparable (hp : p.Prime)
    (hK : Maximal (fun M : IntermediateField F E ↦ IsPExtension {p}ᶜ F M) K)
    (N : IntermediateField K E) [FiniteDimensional K N] [Algebra.IsSeparable K N] :
    ∃ n, finrank K N = p ^ n := by
  have : Normal K E := Normal.tower_top_of_normal F K E
  let M := normalClosure K N E
  obtain ⟨O, hO⟩ :=
    IsGalois.exists_intermediateField_finrank_pow_prime hp (Nat.ordProj_dvd (finrank K M) p)
  have hmul := Module.finrank_mul_finrank K O M
  rw [hO] at hmul
  have hO1 : finrank K O = 1 := finrank_eq_one_of_maximal_isPExtension hK O <| by
    rw [isPNumber_compl_singleton_iff hp,
      Nat.eq_div_of_mul_eq_left (pow_pos hp.pos _).ne' hmul]
    exact ⟨Nat.ordCompl_pos p finrank_pos.ne', Nat.not_dvd_ordCompl hp finrank_pos.ne'⟩
  rw [hO1, one_mul] at hmul
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).1 <|
    hmul ▸ finrank_dvd_of_le_right (le_normalClosure N)
  exact ⟨m, hm⟩

/-- If the exponential characteristic of a prime-to-`p` closure `K` is not `p`, every finite
extension of `K` inside a normal extension is separable: the purely inseparable part of its
normal closure has degree prime to `p`, so it is trivial. -/
private theorem isSeparable_of_maximal_isPExtension
    (hK : Maximal (fun M : IntermediateField F E ↦ IsPExtension {p}ᶜ F M) K) (q : ℕ) [ExpChar K q]
    (hqp : q ≠ p) (L : IntermediateField K E) [FiniteDimensional K L] :
    Algebra.IsSeparable K L := by
  have : Normal K E := Normal.tower_top_of_normal F K E
  let M := normalClosure K L E
  let I := fixedField (⊤ : Subgroup Gal(M/K))
  have := IntermediateField.isPurelyInseparable_fixedField_top K M
  obtain ⟨n, hn⟩ := IsPurelyInseparable.finrank_eq_pow K I q
  have hq : IsPNumber {p}ᶜ q := (expChar_is_prime_or_one K q).elim
    (fun hq ↦ (isPNumber_prime_iff hq).2 hqp) fun hq ↦ hq ▸ isPNumber_one
  have hI : I = ⊥ := by
    rw [← IntermediateField.finrank_eq_one_iff]
    exact finrank_eq_one_of_maximal_isPExtension hK I (hn ▸ hq.pow n)
  have := IsGalois.of_fixedField_eq_bot K M hI
  exact Algebra.IsSeparable.of_algHom K M (inclusion (le_normalClosure L))

/-- **Finite extensions of a prime-to-`p` closure have `p`-power degree.** If `E / F` is normal
and `K` is a prime-to-`p` closure of `F` in `E`, then every finite extension of `K` inside `E` has
degree a power of `p`. For `p` not prime, `{p}ᶜ` contains every prime, so `K` has no proper finite
extension inside `E` at all. -/
theorem exists_finrank_eq_pow_of_maximal_isPExtension
    (hK : Maximal (fun M : IntermediateField F E ↦ IsPExtension {p}ᶜ F M) K)
    (L : IntermediateField K E) [FiniteDimensional K L] : ∃ n, finrank K L = p ^ n := by
  by_cases hp : p.Prime
  swap
  · -- Every prime lies in `{p}ᶜ`, so `L` is a `{p}ᶜ`-extension of `K`, hence trivial.
    obtain rfl := eq_bot_of_maximal_isPExtension hK (N := L) <|
      isPExtension_iff_isPNumber_finrank.2 <|
        isPNumber_iff.2 ⟨finrank_pos, fun q hq _ ↦
          Set.mem_compl_singleton_iff.2 fun hqp ↦ hp (hqp ▸ hq)⟩
    exact ⟨0, by simp⟩
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
  · have := isSeparable_of_maximal_isPExtension hK q hqp L
    exact exists_finrank_eq_pow_of_isSeparable hp hK L

/-- **Characterization of prime-to-`p` closures.** In a normal extension `E / F`, an
intermediate field is a prime-to-`p` closure of `F` exactly when it is a `{p}ᶜ`-extension of `F`
each of whose finite extensions inside `E` has `p`-power degree. -/
theorem maximal_isPExtension_compl_singleton_iff (hp : p.Prime) :
    Maximal (fun M : IntermediateField F E ↦ IsPExtension {p}ᶜ F M) K ↔ IsPExtension {p}ᶜ F K ∧
      ∀ L : IntermediateField K E, FiniteDimensional K L → ∃ n, finrank K L = p ^ n := by
  refine ⟨fun hK ↦ ⟨hK.prop, fun L _ ↦ exists_finrank_eq_pow_of_maximal_isPExtension hK L⟩,
    fun ⟨hK, hpow⟩ ↦ ⟨hK, fun K' hK' hle x hx ↦ ?_⟩⟩
  -- `K⟮x⟯ ⊆ K'` is a `{p}ᶜ`-extension of `K` of `p`-power degree, so it is `K`.
  have hle' : K⟮x⟯.restrictScalars F ≤ K' := by
    rw [restrictScalars_adjoin, adjoin_le_iff, Set.union_subset_iff, Set.singleton_subset_iff]
    exact ⟨hle, hx⟩
  have hKx : IsPExtension {p}ᶜ K K⟮x⟯ :=
    ((isPExtension_congr (restrictScalarsAlgEquiv F K⟮x⟯)).1 (hK'.of_le hle')).tower_top
  have := hKx.isAlgebraic
  have := adjoin.finiteDimensional (isIntegral_iff.1 (Algebra.IsIntegral.isIntegral
    (AdjoinSimple.gen K x)))
  obtain ⟨n, hn⟩ := hpow K⟮x⟯ inferInstance
  have hP := isPExtension_iff_isPNumber_finrank.1 hKx
  rw [hn, isPNumber_pow_iff, isPNumber_prime_iff hp] at hP
  rw [hP.resolve_right (Set.notMem_compl_iff.2 (Set.mem_singleton p)), pow_zero,
    IntermediateField.finrank_eq_one_iff, adjoin_simple_eq_bot_iff] at hn
  obtain ⟨y, rfl⟩ := mem_bot.1 hn
  exact y.property

end Normal

variable {p : ℕ} {K : IntermediateField F E}

/-- **Finite extensions of a prime-to-`p` closure in an algebraic closure.** If `E` is an
algebraic closure of `F` and `K` is a prime-to-`p` closure of `F` in `E`, then every finite field
extension of `K` has degree a power of `p`. -/
theorem exists_finrank_eq_pow_of_maximal_isPExtension_of_isAlgClosure [IsAlgClosure F E]
    (hK : Maximal (fun M : IntermediateField F E ↦ IsPExtension {p}ᶜ F M) K)
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] : ∃ n, finrank K L = p ^ n := by
  have : IsAlgClosed E := IsAlgClosure.isAlgClosed F
  let φ : L →ₐ[K] E := IsAlgClosed.lift
  let e := AlgEquiv.ofInjectiveField φ
  have : FiniteDimensional K φ.fieldRange := e.toLinearEquiv.finiteDimensional
  obtain ⟨n, hn⟩ := exists_finrank_eq_pow_of_maximal_isPExtension hK φ.fieldRange
  exact ⟨n, e.toLinearEquiv.finrank_eq.trans hn⟩

end TauCeti

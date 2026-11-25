/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.LinearCombination

/-!
# Threefold stable rings

A commutative ring `A` is *threefold stable* if for every three unimodular pairs `(aᵢ, bᵢ)`,
that is pairs with `aᵢ A + bᵢ A = A` (Mathlib's `IsCoprime (a i) (b i)`), there is a single
`t : A` making all three elements `aᵢ + bᵢ t` units. This is van der Kallen's stability
hypothesis under which `K₂ A` is presented by Dennis–Stein symbols.

The condition is detected by the residue fields. If some residue field `A ⧸ 𝔪` has at most
three elements, the pairs `(-cᵢ, 1)`, with the `cᵢ` lifting all elements of `A ⧸ 𝔪`, exclude
every `t`; so every residue field of a threefold stable ring has at least four elements. Over a
field each unimodular pair excludes at most one value of `t`, so a field with at least four
elements is threefold stable. For a semilocal ring the Chinese remainder theorem glues the
choices made in the finitely many residue fields.

## Main definitions

* `TauCeti.IsThreefoldStable A`: every three unimodular pairs `(aᵢ, bᵢ)` admit a common `t`
  with every `aᵢ + bᵢ t` a unit.

## Main results

* `RingEquiv.isThreefoldStable_iff`: threefold stability is invariant under ring equivalences.
* `TauCeti.IsThreefoldStable.four_le_card_quotient`: every residue field of a threefold stable
  commutative ring has at least four elements.
* `TauCeti.isThreefoldStable_iff_forall_four_le_card`: a semilocal commutative ring is threefold
  stable if and only if each of its residue fields has at least four elements.
* `TauCeti.isThreefoldStable_iff_four_le_card_residueField`: the same for a local ring.
* `TauCeti.isThreefoldStable_iff_four_le_card`: a field is threefold stable if and only if it
  has at least four elements.
* `TauCeti.isThreefoldStable_zmod_iff`: `ZMod p` is threefold stable exactly when `5 ≤ p`.

## References

* W. van der Kallen, *The K₂ of rings with many units*, Ann. Sci. École Norm. Sup. (4) 10
  (1977), 473–515, §5.2 and §5.4(3).
* C. Weibel, *The K-book*, III.5.11.
-/

public section

namespace TauCeti

variable {A B : Type*}

section CommSemiring

variable [CommSemiring A] [CommSemiring B]

variable (A) in
/-- A commutative ring `A` is **threefold stable** if for any three unimodular pairs
`(a i, b i)`, meaning `IsCoprime (a i) (b i)`, there is one `t : A` such that every
`a i + b i * t` is a unit (van der Kallen). -/
def IsThreefoldStable : Prop :=
  ∀ a b : Fin 3 → A, (∀ i, IsCoprime (a i) (b i)) → ∃ t : A, ∀ i, IsUnit (a i + b i * t)

/-- Unfolding `IsThreefoldStable`: every three unimodular pairs `(a i, b i)` admit a common
`t` with every `a i + b i * t` a unit. -/
theorem isThreefoldStable_iff :
    IsThreefoldStable A ↔
      ∀ a b : Fin 3 → A, (∀ i, IsCoprime (a i) (b i)) →
        ∃ t : A, ∀ i, IsUnit (a i + b i * t) :=
  Iff.rfl

/-- In a threefold stable ring, three unimodular pairs `(a i, b i)` admit a common `t` with
every `a i + b i * t` a unit. -/
theorem IsThreefoldStable.exists_isUnit (h : IsThreefoldStable A) {a b : Fin 3 → A}
    (hab : ∀ i, IsCoprime (a i) (b i)) : ∃ t : A, ∀ i, IsUnit (a i + b i * t) :=
  isThreefoldStable_iff.mp h a b hab

/-- Threefold stability is transported along a ring equivalence. -/
theorem IsThreefoldStable.of_ringEquiv (h : IsThreefoldStable A) (e : A ≃+* B) :
    IsThreefoldStable B := by
  refine isThreefoldStable_iff.mpr fun a b hab ↦ ?_
  obtain ⟨t, ht⟩ := h.exists_isUnit (a := fun i ↦ e.symm (a i)) (b := fun i ↦ e.symm (b i))
    fun i ↦ (hab i).map e.symm.toRingHom
  refine ⟨e t, fun i ↦ ?_⟩
  simpa using (ht i).map e

end CommSemiring

end TauCeti

/-- A ring equivalence preserves and reflects threefold stability. -/
theorem RingEquiv.isThreefoldStable_iff {A B : Type*} [CommSemiring A] [CommSemiring B]
    (e : A ≃+* B) : TauCeti.IsThreefoldStable A ↔ TauCeti.IsThreefoldStable B :=
  ⟨fun h ↦ h.of_ringEquiv e, fun h ↦ h.of_ringEquiv e.symm⟩

namespace TauCeti

variable {A : Type*} [CommRing A]

/-- **Residue fields of a threefold stable ring are not too small.** If `A` is threefold
stable then every residue field `A ⧸ m` has at least four elements: otherwise the three
pairs `(-cᵢ, 1)`, where the `cᵢ` lift every element of `A ⧸ m`, exclude every `t`. -/
theorem IsThreefoldStable.four_le_card_quotient (h : IsThreefoldStable A) (m : Ideal A)
    [m.IsMaximal] : 4 ≤ ENat.card (A ⧸ m) := by
  by_contra hlt
  rw [not_le] at hlt
  have : Finite (A ⧸ m) := ENat.card_lt_top.mp (hlt.trans (ENat.natCast_lt_top 4))
  have : Fintype (A ⧸ m) := Fintype.ofFinite _
  -- `A ⧸ m` embeds into `Fin 3`; a left inverse of the embedding lists all its elements
  obtain ⟨g⟩ : Nonempty (A ⧸ m ↪ Fin 3) := Function.Embedding.nonempty_of_card_le <| by
    rw [ENat.card_eq_coe_fintype_card] at hlt
    have : Fintype.card (A ⧸ m) < 4 := by exact_mod_cast hlt
    rw [Fintype.card_fin]
    omega
  have hc : Function.Surjective (Function.invFun g) := Function.invFun_surjective g.injective
  choose c hc' using fun i ↦ Ideal.Quotient.mk_surjective (Function.invFun g i)
  obtain ⟨t, ht⟩ := h.exists_isUnit (a := fun i ↦ -c i) (b := fun _ ↦ 1)
    fun _ ↦ isCoprime_one_right
  obtain ⟨i, hi⟩ := hc (Ideal.Quotient.mk m t)
  have hmem : -c i + 1 * t ∈ m := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp [hc', hi]
  exact Ideal.IsMaximal.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem _ hmem (ht i))

/-- **A field with at least four elements is threefold stable.** Each unimodular pair
`(a, b)` excludes at most one value of `t`, namely the root of `a + b * t`, so three pairs
cannot exclude every element of a field with at least four elements. -/
theorem isThreefoldStable_of_four_le_card {K : Type*} [Field K] (hK : 4 ≤ ENat.card K) :
    IsThreefoldStable K := by
  refine isThreefoldStable_iff.mpr fun a b hab ↦ ?_
  by_contra hbad
  simp only [isUnit_iff_ne_zero, not_exists, not_forall, not_not] at hbad
  -- assign to each `t` a pair `g t` excluding it; distinct `t` need distinct pairs
  choose g hg using hbad
  have hinj : Function.Injective g := fun s t hst ↦ by
    have hs := hg s
    have ht := hg t
    rw [hst] at hs
    have hmul : b (g t) * (s - t) = 0 := by linear_combination hs - ht
    rcases mul_eq_zero.mp hmul with hb | hst'
    · have ha : a (g t) = 0 := by simpa [hb] using ht
      have := hab (g t)
      simp [ha, hb] at this
    · exact sub_eq_zero.mp hst'
  have := ENat.card_le_card_of_injective hinj
  rw [ENat.card_eq_coe_fintype_card (α := Fin 3), Fintype.card_fin] at this
  exact absurd (hK.trans this) (by decide)

/-- A semilocal commutative ring all of whose residue fields have at least four elements is
threefold stable: choose `t` in each residue field and glue by the Chinese remainder theorem. -/
theorem isThreefoldStable_of_forall_four_le_card [Finite (MaximalSpectrum A)]
    (h : ∀ m : Ideal A, m.IsMaximal → 4 ≤ ENat.card (A ⧸ m)) : IsThreefoldStable A := by
  refine isThreefoldStable_iff.mpr fun a b hab ↦ ?_
  -- in every residue field there is a residue class of `s` with all `a i + b i * s` nonzero
  have key (m : MaximalSpectrum A) : ∃ s : A, ∀ i, a i + b i * s ∉ m.asIdeal := by
    let := Ideal.Quotient.field m.asIdeal
    obtain ⟨s, hs⟩ := (isThreefoldStable_of_four_le_card (h m.asIdeal m.isMaximal)).exists_isUnit
      (a := fun i ↦ Ideal.Quotient.mk m.asIdeal (a i))
      (b := fun i ↦ Ideal.Quotient.mk m.asIdeal (b i)) fun i ↦ (hab i).map _
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
    refine ⟨s, fun i hi ↦ not_isUnit_zero (M₀ := A ⧸ m.asIdeal) ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_add, map_mul] at hi
    exact hi ▸ hs i
  choose s hs using key
  obtain ⟨t, ht⟩ := Ideal.exists_forall_sub_mem_ideal (I := fun m : MaximalSpectrum A ↦ m.asIdeal)
    (fun _ _ hne ↦ MaximalSpectrum.isCoprime_of_ne hne) s
  refine ⟨t, fun i ↦ by_contra fun hu ↦ ?_⟩
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hu
  refine hs ⟨m, hm⟩ i ?_
  have heq : a i + b i * s ⟨m, hm⟩ = a i + b i * t - b i * (t - s ⟨m, hm⟩) := by ring
  rw [heq]
  exact m.sub_mem hmem (m.mul_mem_left _ (ht ⟨m, hm⟩))

/-- **Threefold stability of a semilocal ring.** A commutative ring with finitely many maximal
ideals is threefold stable if and only if each of its residue fields has at least four
elements. -/
theorem isThreefoldStable_iff_forall_four_le_card [Finite (MaximalSpectrum A)] :
    IsThreefoldStable A ↔ ∀ m : Ideal A, m.IsMaximal → 4 ≤ ENat.card (A ⧸ m) :=
  ⟨fun h _ _ ↦ h.four_le_card_quotient _, isThreefoldStable_of_forall_four_le_card⟩

/-- A local ring is threefold stable if and only if its residue field has at least four
elements. -/
theorem isThreefoldStable_iff_four_le_card_residueField [IsLocalRing A] :
    IsThreefoldStable A ↔ 4 ≤ ENat.card (IsLocalRing.ResidueField A) := by
  rw [isThreefoldStable_iff_forall_four_le_card]
  -- `ResidueField A` is by definition `A ⧸ maximalIdeal A`
  change _ ↔ 4 ≤ ENat.card (A ⧸ IsLocalRing.maximalIdeal A)
  exact ⟨fun h ↦ h _ inferInstance,
    fun h m hm ↦ IsLocalRing.eq_maximalIdeal hm ▸ h⟩

/-- **Threefold stability of a field.** A field is threefold stable if and only if it has at
least four elements. -/
theorem isThreefoldStable_iff_four_le_card (K : Type*) [Field K] :
    IsThreefoldStable K ↔ 4 ≤ ENat.card K := by
  refine ⟨fun h ↦ ?_, isThreefoldStable_of_four_le_card⟩
  have := Ideal.bot_isMaximal (K := K)
  rw [← ENat.card_congr (RingEquiv.quotientBot K).toEquiv]
  exact h.four_le_card_quotient ⊥

/-- The prime field `ZMod p` is threefold stable exactly when `5 ≤ p`; in particular `𝔽₂` and
`𝔽₃` are not threefold stable, while `𝔽₅` is. -/
theorem isThreefoldStable_zmod_iff (p : ℕ) [Fact p.Prime] :
    IsThreefoldStable (ZMod p) ↔ 5 ≤ p := by
  have hp4 : p ≠ 4 := by
    rintro rfl
    exact absurd (Fact.out : Nat.Prime 4) (by decide)
  refine (isThreefoldStable_iff_four_le_card (ZMod p)).trans ?_
  rw [ENat.card_eq_coe_fintype_card, ZMod.card]
  constructor
  · intro h
    have : 4 ≤ p := by exact_mod_cast h
    omega
  · intro h
    exact_mod_cast (show 4 ≤ p by omega)

end TauCeti

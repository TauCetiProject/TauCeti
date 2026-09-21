/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Values
public import TauCeti.RepresentationTheory.Induction.Ideal
public import TauCeti.RepresentationTheory.Induction.PElementary

/-!
# The `p`-section indicator as a combination of characters

Fix a prime `p`, a finite group `G`, and an algebraically closed field `k` in which `|G|` is
invertible.
Brauer's induction theorem, which writes every character of `G` as an integral combination of
characters induced from elementary subgroups, is proved one prime at a time: for each `p` one
needs a function on `G` with natural-number values, none divisible by `p`, that is a combination
of characters induced from `p`-elementary subgroups. The coefficients of that combination need not
be integers; they lie in any subring `A ≤ k` containing the required roots of unity. The intended
later specialization takes `A` to be a ring of cyclotomic integers, from which descent to `ℤ` is a
separate step. This file constructs that function.

The building block is the `p`-section indicator of a `p`-regular element `s`
(`TauCeti.pSectionIndicator`), a class function on the `p`-elementary subgroup
`H = TauCeti.pElementaryOfSylow s P`. On the cyclic group `⟨s⟩` the indicator of `s` expands as
`|⟨s⟩|⁻¹ ∑ χ, χ(s⁻¹) χ` over the linear characters `χ`, whose values are roots of unity of order
dividing `orderOf s`; the section indicator is its pullback along the projection
`TauCeti.pFreePartHom : H →* ⟨s⟩`. So `orderOf s` times the section indicator is an
`A`-combination of characters of `H`, for every subring `A` of `k` containing those roots of
unity (`TauCeti.orderOf_nsmul_pSectionIndicator_mem_span_virtualCharacters`), and inducing it
gives an `A`-combination of virtual characters induced from `p`-elementary subgroups
(`TauCeti.orderOf_nsmul_indPSectionIndicator_mem_span_indVirtualCharacters`).

Summing these induced functions over the conjugacy classes of `p`-regular elements `s` gives the
function wanted: at `y` only the class of the `p`-free part of `y` contributes, with a value
`orderOf s` times a count of cosets that is prime to `p`
(`TauCeti.exists_mem_span_indVirtualCharacters_isPElementary_not_dvd`).

The scaling by `orderOf s`, rather than by the order of `H`, is what keeps the values prime to
`p`: expanding the section indicator directly on `H` would clear a denominator divisible by the
`p`-part of `|H|`.

## Main statements

* `TauCeti.pSectionIndicator_eq_comp_pFreePartHom`: the `p`-section indicator is the pullback of
  the indicator of `s` along the `p`-free-part homomorphism.
* `TauCeti.orderOf_nsmul_pSectionIndicator_mem_span_virtualCharacters`: `orderOf s` times the
  `p`-section indicator is an `A`-combination of characters of the `p`-elementary subgroup.
* `TauCeti.orderOf_nsmul_indPSectionIndicator_mem_span_indVirtualCharacters`: its induction is an
  `A`-combination of virtual characters induced from `p`-elementary subgroups.
* `TauCeti.exists_mem_span_indVirtualCharacters_isPElementary_not_dvd`: **there is a
  natural-number-valued function with no value divisible by `p` whose cast is such a
  combination.**

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), Part II, §10.3,
  whose construction this follows.
* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Chapter 8.
-/

public section

namespace TauCeti

open _root_.Subgroup

universe u v

variable {k : Type u} {G : Type v} [Group G]

section Section

variable {p : ℕ} [Fact p.Prime] {s : G} {P : Sylow p (centralizer ({s} : Set G))}

/-! ### The section indicator as a pullback -/

section Pullback

variable [Zero k] [One k]

open scoped Classical in
/-- **The `p`-section indicator is a pullback.** It is the indicator of `s` in the cyclic group
`⟨s⟩`, pulled back along the `p`-free-part homomorphism `TauCeti.pFreePartHom`. -/
theorem pSectionIndicator_eq_comp_pFreePartHom (hs : ¬ p ∣ orderOf s) :
    pSectionIndicator k s P =
      Pi.single (⟨s, mem_zpowers s⟩ : zpowers s) (1 : k) ∘ pFreePartHom s P hs := by
  funext x
  simp [Pi.single_apply, Subtype.ext_iff]

end Pullback

/-! ### The scaled section indicator as a combination of characters -/

variable [Field k]
variable [Finite G] [IsAlgClosed k] [Invertible (Nat.card G : k)]

/-- **The `p`-section indicator, scaled by the order of `s`, is an `A`-combination of characters
of the `p`-elementary subgroup**, for every subring `A` of `k` containing the roots of unity of
order dividing `orderOf s`. On `⟨s⟩` the scaled indicator of `s` is `∑ χ, χ(s⁻¹) χ` over the
irreducible characters `χ`, whose values are such roots of unity, and the section indicator is the
pullback of the indicator of `s` along `TauCeti.pFreePartHom`. -/
theorem orderOf_nsmul_pSectionIndicator_mem_span_virtualCharacters (A : Subring k)
    (hA : ∀ x : k, x ^ orderOf s = 1 → x ∈ A) (hs : ¬ p ∣ orderOf s) :
    orderOf s • pSectionIndicator k s P ∈
      Submodule.span A (virtualCharacters k ↥(pElementaryOfSylow s P) : Set _) := by
  classical
  let _ : Invertible (Nat.card ↥(zpowers s) : k) := invertibleOfNonzero
    (ne_zero_of_dvd_ne_zero (Invertible.ne_zero _) (Nat.cast_dvd_cast (card_subgroup_dvd_card _)))
  have h1 : Nat.card ↥(zpowers s) • Pi.single (⟨s, mem_zpowers s⟩ : zpowers s) (1 : k) ∈
      Submodule.span A (irreducibleCharacters k ↥(zpowers s)) := by
    refine natCard_nsmul_mem_span_irreducibleCharacters A
      (ClassFunction.mem_of_isMulCommutative _) (fun g => ?_) fun i g => ?_
    · rw [Pi.single_apply]
      split_ifs <;> simp
    · exact irreducibleCharacter_apply_mem_of_forall_pow_eq_one_mem k
        (by rwa [Nat.card_zpowers]) i g
  have hiv : irreducibleCharacters k ↥(zpowers s) ⊆ virtualCharacters k ↥(zpowers s) :=
    fun f hf => by
      obtain ⟨V, rfl⟩ := irreducibleCharacters_subset_range hf
      exact character_mem_virtualCharacters V
  have h2 := comp_mem_span_virtualCharacters A (pFreePartHom s P hs) (Submodule.span_mono hiv h1)
  rwa [Nat.card_zpowers, Pi.smul_comp, ← pSectionIndicator_eq_comp_pFreePartHom hs] at h2

/-- **The induced `p`-section indicator, scaled by the order of `s`, is an `A`-combination of
virtual characters induced from `p`-elementary subgroups.** -/
theorem orderOf_nsmul_indPSectionIndicator_mem_span_indVirtualCharacters (A : Subring k)
    (hA : ∀ x : k, x ^ orderOf s = 1 → x ∈ A) (hs : ¬ p ∣ orderOf s) :
    orderOf s • indPSectionIndicator k s P ∈
      Submodule.span A
        (ClassFunction.indVirtualCharacters k G (fun S => IsPElementary p S) : Set (G → k)) := by
  rw [indPSectionIndicator, ← indClassFunAddHom_apply, ← map_nsmul, indClassFunAddHom_apply]
  exact ClassFunction.indClassFun_mem_span_indVirtualCharacters A
    (isPElementary_pElementaryOfSylow s P hs)
    (orderOf_nsmul_pSectionIndicator_mem_span_virtualCharacters A hA hs)

end Section

/-! ### A function prime to `p` everywhere -/

variable [Field k]
variable [Finite G] [IsAlgClosed k] [Invertible (Nat.card G : k)]

variable (k) in
/-- **Brauer's local lemma.** For every prime `p` there is a function `ψ : G → ℕ`, none of whose
values is divisible by `p`, whose cast to `k` is an `A`-combination of virtual characters induced
from `p`-elementary subgroups, for every subring `A` of `k` containing the `|G|`-th roots of
unity. It is the sum, over the conjugacy classes of `p`-regular elements `s`, of `orderOf s` times
the induced `p`-section indicator of `s`: at `y` only the class of the `p`-free part of `y`
contributes, and its contribution is prime to `p`. -/
theorem exists_mem_span_indVirtualCharacters_isPElementary_not_dvd (p : ℕ) [Fact p.Prime] :
    ∃ ψ : G → ℕ, (∀ y, ¬ p ∣ ψ y) ∧ ∀ A : Subring k, (∀ x : k, x ^ Nat.card G = 1 → x ∈ A) →
      (fun y => (ψ y : k)) ∈ Submodule.span A
        (ClassFunction.indVirtualCharacters k G (fun S => IsPElementary p S) : Set (G → k)) := by
  classical
  let _ : Fintype (ConjClasses G) := Fintype.ofFinite _
  -- a representative of each conjugacy class, and a Sylow `p`-subgroup of its centraliser
  let rep : ConjClasses G → G := Quotient.out
  let Syl : ∀ C : ConjClasses G, Sylow p (centralizer ({rep C} : Set G)) :=
    fun _ => Classical.arbitrary _
  -- the classes of `p`-regular elements
  let T : Finset (ConjClasses G) := Finset.univ.filter fun C => ¬ p ∣ orderOf (rep C)
  have hT : ∀ C ∈ T, ¬ p ∣ orderOf (rep C) := fun C hC => (Finset.mem_filter.1 hC).2
  have hrep : ∀ C : ConjClasses G, ∀ x : G, IsConj x (rep C) ↔ ConjClasses.mk x = C := fun C x => by
    rw [← ConjClasses.mk_eq_mk_iff_isConj]
    exact ⟨fun h => h.trans (Quotient.out_eq C), fun h => h.trans (Quotient.out_eq C).symm⟩
  refine ⟨fun y => ∑ C ∈ T, orderOf (rep C) * pSectionCosetCard (rep C) (Syl C) y,
    fun y => ?_, fun A hA => ?_⟩
  · -- only the class of the `p`-free part of `y` contributes, and it contributes a number prime
    -- to `p`
    dsimp only
    have hC₀ : IsConj (pFreePart p y) (rep (ConjClasses.mk (pFreePart p y))) := (hrep _ _).2 rfl
    have hmem : ConjClasses.mk (pFreePart p y) ∈ T := by
      obtain ⟨c, hc⟩ := hC₀
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rw [← hc.orderOf_eq]
      exact not_dvd_orderOf_pFreePart Fact.out (orderOf_pos y).ne'
    rw [Finset.sum_eq_single (ConjClasses.mk (pFreePart p y))]
    · intro h
      rcases (Nat.Prime.dvd_mul Fact.out).1 h with h | h
      · exact hT _ hmem h
      · exact not_dvd_pSectionCosetCard_of_isConj hC₀ h
    · intro C _ hC
      rw [pSectionCosetCard_eq_zero_of_not_isConj fun h => hC ((hrep C _).1 h).symm, mul_zero]
    · exact fun h => absurd hmem h
  · -- each summand is an `A`-combination of induced virtual characters
    have hcast : (fun y => ((∑ C ∈ T, orderOf (rep C) * pSectionCosetCard (rep C) (Syl C) y : ℕ) :
        k)) = ∑ C ∈ T, orderOf (rep C) • indPSectionIndicator k (rep C) (Syl C) := by
      funext y
      rw [Finset.sum_apply, Nat.cast_sum]
      refine Finset.sum_congr rfl fun C hC => ?_
      rw [Pi.smul_apply, nsmul_eq_mul, Nat.cast_mul,
        indPSectionIndicator_eq_pSectionCosetCard (hT C hC)]
    rw [hcast]
    refine Submodule.sum_mem _ fun C hC =>
      orderOf_nsmul_indPSectionIndicator_mem_span_indVirtualCharacters A (fun x hx => hA x ?_)
        (hT C hC)
    obtain ⟨m, hm⟩ := orderOf_dvd_natCard (rep C)
    rw [hm, pow_mul, hx, one_pow]

end TauCeti

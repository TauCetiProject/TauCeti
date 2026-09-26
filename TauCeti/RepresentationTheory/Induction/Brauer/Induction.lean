/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Brauer.PSection
import TauCeti.RingTheory.PowerBasis
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Brauer's induction theorem

For a finite group `G` over an algebraically closed field of characteristic zero, every virtual
character is an integral combination of characters induced from elementary subgroups.  In the
canonical lattice API this says

`indVirtualCharacters k G (fun E ↦ IsElementary E) = virtualCharacters k G`.

The local input is `TauCeti.exists_mem_span_indVirtualCharacters_isPElementary_not_dvd`.  For a
prime `p` it supplies a natural-number-valued function `ψ`, none of whose values is divisible by
`p`, in the cyclotomic span of the characters induced from `p`-elementary subgroups.  If `S` is the
finite set of values of `ψ`, then

`           ∏ n in S, (n - ψ) = 0`.

The induced-character span is closed under multiplication.  Expanding the product therefore puts
the constant `∏ n in S, n` in that span, and this constant is prime to `p`.  The prime-by-prime
criterion from `TauCeti.RepresentationTheory.Induction.Ideal` then gives the integral theorem.

## Main results

* `TauCeti.ClassFunction.indVirtualCharacters_eq_virtualCharacters_isElementary`: **Brauer's
  induction theorem**, in virtual-character lattice form.
* `TauCeti.ClassFunction.indVirtualCharacterDirectSumAddHom_isElementary_surjective`: the direct
  sum of induction maps from elementary subgroups is surjective.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), Part II,
  Section 10.3, Theorem 18.
* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Chapter 8.
-/

public section

namespace TauCeti

namespace ClassFunction

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G]

private theorem prod_nsmul_one_sub_mem_span (A : Subring k) (P : Subgroup G → Prop)
    {f : G → k} (hf : f ∈ Submodule.span A (indVirtualCharacters k G P : Set (G → k)))
    (s : Finset ℕ) :
    (∏ n ∈ s, (n • (1 : G → k) - f)) - s.prod id • (1 : G → k) ∈
      Submodule.span A (indVirtualCharacters k G P : Set (G → k)) := by
  let M := Submodule.span A (indVirtualCharacters k G P : Set (G → k))
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, one_nsmul, sub_self] using M.zero_mem
  | @insert n s hn ih =>
      have hmul := mul_mem_span_indVirtualCharacters A P
        (Submodule.span_mono indVirtualCharacters_le_virtualCharacters hf) ih
      have hnsmul : n • ((∏ i ∈ s, (i • (1 : G → k) - f)) -
          s.prod id • (1 : G → k)) ∈ M := M.nsmul_mem ih n
      have hprodsmul : s.prod id • f ∈ M := M.nsmul_mem hf (s.prod id)
      have hmem := M.sub_mem (M.sub_mem hnsmul hmul) hprodsmul
      rw [Finset.prod_insert hn, Finset.prod_insert hn]
      convert hmem using 1
      simp only [id_eq, nsmul_eq_mul, Nat.cast_mul]
      ring

/-- **Brauer's induction theorem.** Over an algebraically closed field of characteristic zero,
every virtual character of a finite group is an integral combination of virtual characters
induced from elementary subgroups. -/
theorem indVirtualCharacters_eq_virtualCharacters_isElementary [CharZero k] [IsAlgClosed k] :
    indVirtualCharacters k G (fun E ↦ IsElementary E) = virtualCharacters k G := by
  classical
  let n := Nat.card G
  have hn : 0 < n := Nat.card_pos
  let _ : NeZero n := ⟨hn.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k n
  have hζint : IsIntegral ℤ ζ := hζ.isIntegral hn
  obtain ⟨A, hroots, t, ht⟩ := exists_subring_retraction_of_primitiveRoot hζ hζint
  let _ : Invertible (Nat.card G : k) := invertibleOfNonzero (Nat.cast_ne_zero.mpr hn.ne')
  rw [indVirtualCharacters_eq_virtualCharacters_iff_forall_prime A t ht]
  intro p hp
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨ψ, hψp, hψspan⟩ := exists_mem_span_indVirtualCharacters_isPElementary_not_dvd
    (k := k) (G := G) p
  let _ : Fintype G := Fintype.ofFinite G
  let values : Finset ℕ := Finset.univ.image ψ
  let m := values.prod id
  have hm : ¬ p ∣ m := by
    apply Prime.not_dvd_finsetProd (M := ℕ) (Nat.prime_iff.mp hp)
    intro a ha
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp ha
    exact hψp g
  refine ⟨m, hm, ?_⟩
  have hpElem : indVirtualCharacters k G (fun E ↦ IsPElementary p E) ≤
      indVirtualCharacters k G (fun E ↦ IsElementary E) :=
    indVirtualCharacters_mono fun _ hE ↦ isElementary_def.mpr ⟨p, hp, hE⟩
  have hψ : (fun g ↦ (ψ g : k)) ∈
      Submodule.span A (indVirtualCharacters k G (fun E ↦ IsElementary E) : Set (G → k)) :=
    Submodule.span_mono hpElem (hψspan A hroots)
  have hrel := prod_nsmul_one_sub_mem_span A (fun E ↦ IsElementary E) hψ values
  have hprod : (∏ a ∈ values, (a • (1 : G → k) - fun g ↦ (ψ g : k))) = 0 := by
    funext g
    simp only [Finset.prod_apply, Pi.sub_apply, Pi.zero_apply]
    have hg : ψ g ∈ values := Finset.mem_image.mpr ⟨g, Finset.mem_univ g, rfl⟩
    apply Finset.prod_eq_zero hg
    simp
  rw [hprod, zero_sub] at hrel
  simpa only [m] using neg_mem_iff.mp hrel

/-- The direct sum of induction maps from elementary subgroups is surjective. This is the
direct-sum formulation of
`TauCeti.ClassFunction.indVirtualCharacters_eq_virtualCharacters_isElementary`. -/
theorem indVirtualCharacterDirectSumAddHom_isElementary_surjective [CharZero k] [IsAlgClosed k] :
    Function.Surjective
      (indVirtualCharacterDirectSumAddHom k G (fun E ↦ IsElementary E)) :=
  indVirtualCharacterDirectSumAddHom_surjective_iff.mpr
    indVirtualCharacters_eq_virtualCharacters_isElementary

end ClassFunction

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import TauCeti.RepresentationTheory.CharacterTable.VirtualCharacter
public import TauCeti.RepresentationTheory.Induction.ClassFunction
import TauCeti.NumberTheory.NumberField.ComplexConjugation.NormOne
import TauCeti.RepresentationTheory.CharacterTable.Coset.Orthogonality
import TauCeti.RepresentationTheory.CharacterTable.Gallagher
import TauCeti.RepresentationTheory.Induction.Clifford.CharacterPackets

/-!
# Virtual characters of norm one on a coset

In prime index, the irreducible characters over stable characters of a normal subgroup come in
packets of quotient twists. The remaining irreducibles are induced and vanish off the subgroup.
On the generator coset, each packet contributes one coefficient in the ring of integers of the
cyclotomic field. Coset orthogonality converts the norm-one condition to a sum of squared
absolute values; arithmetic rigidity then leaves one root-of-unity coefficient.

The split prime-index norm-one statement with a complex scalar is due to Levent Alpöge's Lean
formalization, <https://github.com/leanprover-community/riemann-hypothesis>. Here the normal
subgroup need not admit a complement, and the scalar is a cyclotomic root of unity.
-/

public section

open scoped ComplexConjugate
open Finset

namespace TauCeti

variable {G : Type} [Group G] {N : Subgroup G}

/-- The normalized squared norm of a linear combination of extensions of distinct irreducible
characters, on any coset, is the sum of the squares of its coefficient norms. -/
private theorem extension_sum_normSq {ι : Type*} [Fintype ι] [Finite G] [Fintype N] (x : G)
    (χ : ι → G → ℂ) (hχ : ∀ i, χ i ∈ irreducibleCharacters ℂ G)
    (hN : ∀ i, (fun n : N => χ i n) ∈ irreducibleCharacters ℂ N)
    (hinj : Function.Injective fun i (n : N) => χ i n) (b : ι → ℂ) :
    (Nat.card N : ℂ)⁻¹ * (∑ n : N, (∑ i, b i * χ i (x * n)) *
        conj (∑ i, b i * χ i (x * n))) = ∑ i, (Complex.normSq (b i) : ℂ) := by
  classical
  have hpair (i j : ι) : (∑ n : N, χ i (x * n) * conj (χ j (x * n))) =
      if i = j then (Nat.card N : ℂ) else 0 := by
    have hvirt := irreducibleCharacters_subset_virtualCharacters (hχ j)
    simp only [conj_apply_of_mem_virtualCharacters hvirt]
    obtain ⟨d, ρ, -, hρ⟩ := mem_irreducibleCharacters_iff.mp (hχ i)
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl, ← hρ]
      exact ρ.sum_character_mul_mul_character_mul_inv_eq_card N (hρ ▸ hN i) x
    · rw [ite_eq_right hij]
      obtain ⟨e, σ, -, hσ⟩ := mem_irreducibleCharacters_iff.mp (hχ j)
      exact hρ.symm ▸ hσ.symm ▸
        ρ.sum_character_mul_mul_character_mul_inv_eq_zero σ N (hρ ▸ hN i) (hσ ▸ hN j)
          (by simpa [← hρ, ← hσ] using hinj.ne hij) x
  have hcard : (Nat.card N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  calc
    _ = (Nat.card N : ℂ)⁻¹ * ∑ i, ∑ j, (b i * conj (b j)) *
        ∑ n : N, χ i (x * n) * conj (χ j (x * n)) := by
      congr 1
      simp only [map_sum, map_mul, Finset.sum_mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun i _ => ?_
      rw [sum_comm]
      exact sum_congr rfl fun j _ => by rw [mul_sum]; exact sum_congr rfl fun n _ => by ring
    _ = _ := by
      simp only [hpair, mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true]
      rw [← sum_mul, mul_comm _ (Nat.card N : ℂ), inv_mul_cancel_left₀ hcard]
      simp only [Complex.mul_conj]

variable [N.Normal]

/-- A virtual character of squared norm one on the generator coset of a normal subgroup of prime
index agrees there with a cyclotomic root of unity times an extension of a stable irreducible
character. The extension need not split. -/
theorem exists_rootOfUnity_mul_extension_eq_on_coset (hp : N.index.Prime) {x : G} (hx : x ∉ N)
    [Fintype N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N.index) {X : G → ℂ}
    (hX : X ∈ virtualCharacters ℂ G)
    (hnorm : (Nat.card N : ℂ)⁻¹ * ∑ n : N, X (x * n) * conj (X (x * n)) = 1) :
    ∃ θ ∈ irreducibleCharacters ℂ N, θ ∘ MulAut.conjNormal x = θ ∧
      ∃ χ ∈ irreducibleCharacters ℂ G, (∀ n : N, χ n = θ n) ∧
        ∃ b : IntermediateField.adjoin ℚ ({ζ} : Set ℂ), IsOfFinOrder b ∧
          ∀ n : N, X (x * n) = (b : ℂ) * χ (x * n) := by
  classical
  have : Finite G := (Subgroup.finite_iff_finite_and_finiteIndex N).mpr
    ⟨inferInstance, N.finiteIndex_iff.mpr hp.ne_zero⟩
  let I := {i : Fin (Nat.card (ConjClasses N)) //
    irreducibleCharacter ℂ i ∘ MulAut.conjNormal x = irreducibleCharacter ℂ i}
  let : Fintype I := Fintype.ofFinite I
  obtain ⟨χ, ε, a, Y, hχ, hres, hε, -, hXsum⟩ :=
    exists_sum_quotient_twists_add_indClassFun hp hx hζ hX
  rw [finsum_eq_sum_of_fintype] at hXsum
  let K := IntermediateField.adjoin ℚ ({ζ} : Set ℂ)
  let : NeZero N.index := ⟨hp.ne_zero⟩
  let : IsCyclotomicExtension {N.index} ℚ K := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  let : NumberField K := IsCyclotomicExtension.numberField {N.index} ℚ K
  let : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {N.index} ℚ K
  let z : K := ⟨ζ, IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩
  have hz : IsPrimitiveRoot z N.index := hζ.of_map_of_injective K.val.injective
  let zi : NumberField.RingOfIntegers K := ⟨z, hz.isIntegral hp.pos⟩
  let b (i : I) : NumberField.RingOfIntegers K :=
    ∑ j, (a i j : NumberField.RingOfIntegers K) * zi ^ j.val
  let φ := K.val.toRingHom
  have hb (i : I) : φ (b i) = ∑ j, (a i j : ℂ) * ζ ^ j.val := by
    let f := φ.comp (algebraMap (NumberField.RingOfIntegers K) K)
    have hf : f zi = ζ := rfl
    calc
      φ (b i) = f (b i) := rfl
      _ = _ := by simp only [b, map_sum, map_mul, map_intCast, map_pow, hf]
  have hcoset (n : N) : X (x * n) = ∑ i, φ (b i) * χ i (x * n) := by
    have hn : x * n ∉ N := fun h => hx ((N.mul_mem_cancel_right n.property).mp h)
    have hind : N.indClassFun Y (x * n) = 0 := by
      rw [Subgroup.indClassFun_apply]
      refine sum_eq_zero fun q _ => dite_eq_right fun h => hn ?_
      simpa [mul_assoc] using (inferInstance : N.Normal).conj_mem _ h (Quotient.out q)
    rw [congrFun hXsum (x * n), Pi.add_apply, hind, add_zero, Finset.sum_apply]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.sum_apply, hb, sum_mul]
    have hq : QuotientGroup.mk' N (x * n) = QuotientGroup.mk' N x :=
      QuotientGroup.mk_mul_of_mem x n.property
    simp only [Pi.smul_apply, smul_eq_mul, hq, hε]
    exact sum_congr rfl fun j _ => by ring
  have hpair := extension_sum_normSq x χ hχ (fun i => by simpa only [hres] using
    (irreducibleCharacter_mem ℂ i.val)) (fun i j hij => Subtype.ext
      (irreducibleCharacter_injective (k := ℂ) (funext fun n =>
        (hres i n).symm.trans ((congrFun hij n).trans (hres j n))))) (fun i => φ (b i))
  have hsum : ∑ i, Complex.normSq (φ (b i)) = 1 := by
    rw [← Complex.ofReal_inj, Complex.ofReal_sum, Complex.ofReal_one, ← hpair]
    refine Eq.trans ?_ hnorm
    congr 1
    exact sum_congr rfl fun n _ => by rw [hcoset n]
  obtain ⟨i, -, hi, hzero⟩ := (Finset.sum_normSq_eq_one_iff_of_isAbelianGalois univ b φ).mp hsum
  refine ⟨_, irreducibleCharacter_mem ℂ i.val, i.property, χ i, hχ i, hres i, b i, hi, fun n => ?_⟩
  rw [hcoset, sum_eq_single_of_mem i (mem_univ _) (fun j hj hji => by simp [hzero j hj hji])]
  rfl

end TauCeti

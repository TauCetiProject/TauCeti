/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import TauCeti.RepresentationTheory.CharacterTable.VirtualCharacter
public import TauCeti.RepresentationTheory.Induction.ClassFunction
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import TauCeti.NumberTheory.NumberField.ComplexConjugation.NormOne
import TauCeti.RepresentationTheory.CharacterTable.Coset.Orthogonality
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

variable {G : Type} [Group G] {N : Subgroup G} [N.Normal]

/-- A virtual character of squared norm one on the generator coset of a normal subgroup of prime
index agrees there with a cyclotomic root of unity times an extension of a stable irreducible
character. The group extension `N → G → G ⧸ N` need not split (no complement to `N` is assumed). -/
theorem exists_rootOfUnity_mul_extension_eq_on_coset_of_norm_eq_one
    (hp : N.index.Prime) {x : G} (hx : x ∉ N) [Fintype N]
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N.index) {X : G → ℂ}
    (hX : X ∈ virtualCharacters ℂ G)
    (hnorm : (Nat.card N : ℂ)⁻¹ * ∑ n : N, X (x * n) * conj (X (x * n)) = 1) :
    ∃ θ ∈ irreducibleCharacters ℂ N, θ ∘ MulAut.conjNormal x = θ ∧
      ∃ χ ∈ irreducibleCharacters ℂ G, (∀ n : N, χ n = θ n) ∧
        ∃ b : IntermediateField.adjoin ℚ ({ζ} : Set ℂ), IsOfFinOrder b ∧
          ∀ n : N, X (x * n) = (b : ℂ) * χ (x * n) := by
  classical
  have : Finite G := (Subgroup.finite_iff_finite_and_finiteIndex N).mpr
    ⟨inferInstance, N.finiteIndex_iff.mpr hp.ne_zero⟩
  -- Expand `X` into packets of quotient twists plus an induced virtual character.
  obtain ⟨χ, ε, a, Y, hχ, hres, hε, -, hXsum⟩ :=
    exists_sum_quotient_twists_add_indClassFun hp hx hζ hX
  rw [finsum_eq_sum_of_fintype] at hXsum
  -- Form the packet coefficients in the ring of integers of `K = ℚ(ζ)`.
  let K := IntermediateField.adjoin ℚ ({ζ} : Set ℂ)
  let : NeZero N.index := ⟨hp.ne_zero⟩
  let : IsCyclotomicExtension {N.index} ℚ K := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  let : NumberField K := IsCyclotomicExtension.numberField {N.index} ℚ K
  let : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {N.index} ℚ K
  let z : K := ⟨ζ, IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩
  have hz : IsPrimitiveRoot z N.index := hζ.of_map_of_injective K.val.injective
  let b i : NumberField.RingOfIntegers K := ∑ j, (a i j : NumberField.RingOfIntegers K) *
    hz.toInteger ^ (j : ℕ)
  have hb i : ((b i : K) : ℂ) = ∑ j, (a i j : ℂ) * ζ ^ (j : ℕ) := by
    have hcoe : algebraMap (NumberField.RingOfIntegers K) K hz.toInteger = z := hz.coe_toInteger
    simp [b, hcoe, z]
  let φ := K.val.toRingHom
  have hφ (y : K) : φ y = y := by simp [φ]
  -- Coset evaluation: on `x N` the induced part vanishes and each packet is its coefficient
  -- times `χ i`.
  have hcoset (n : N) : X (x * n) = ∑ i, ((b i : K) : ℂ) * χ i (x * n) := by
    have hn : x * n ∉ N := fun h => hx ((N.mul_mem_cancel_right n.property).mp h)
    rw [congrFun hXsum (x * n), Pi.add_apply, N.indClassFun_apply_eq_zero_of_notMem Y hn,
      add_zero, Finset.sum_apply]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.sum_apply, hb, sum_mul]
    have hq : QuotientGroup.mk' N (x * n) = QuotientGroup.mk' N x :=
      QuotientGroup.mk_mul_of_mem x n.property
    simp only [Pi.smul_apply, smul_eq_mul, hq, hε]
    exact sum_congr rfl fun j _ => by ring
  -- Norm sum: coset orthogonality turns the norm-one condition into `∑ i, |b i|² = 1`.
  have hpair := inv_natCard_mul_sum_mul_conj_eq_sum_normSq x χ hχ
    (fun i => by simpa only [hres] using irreducibleCharacter_mem ℂ i.val)
    (fun i j hij => Subtype.ext (irreducibleCharacter_injective (k := ℂ) (funext fun n =>
        (hres i n).symm.trans ((congrFun hij n).trans (hres j n))))) (fun i => ((b i : K) : ℂ))
  have hsum : ∑ i, Complex.normSq (φ (b i)) = 1 := by
    rw [← Complex.ofReal_inj, Complex.ofReal_sum, Complex.ofReal_one]
    simpa only [hφ, ← hpair, ← hcoset] using hnorm
  -- Rigidity: only one coefficient is nonzero, and it is a root of unity.
  obtain ⟨i, -, hi, hzero⟩ := (Finset.sum_normSq_eq_one_iff_of_isAbelianGalois univ b φ).mp hsum
  refine ⟨_, irreducibleCharacter_mem ℂ i.val, i.property, χ i, hχ i, hres i, b i, hi, fun n => ?_⟩
  rw [hcoset, sum_eq_single_of_mem i (mem_univ _) (fun j hj hji => by simp [hzero j hj hji])]

end TauCeti

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

/-- An integral combination `∑ j ∈ s, a j * z ^ e j` of powers of an algebraic integer `z` of a
subfield `K` of `ℂ` is the image in `ℂ` of an algebraic integer of `K`. -/
private theorem exists_ringOfIntegers_coe_eq_sum {K : IntermediateField ℚ ℂ} {z : K}
    (hz : IsIntegral ℤ z) {ι : Type*} (s : Finset ι) (a : ι → ℤ) (e : ι → ℕ) :
    ∃ b : NumberField.RingOfIntegers K, ((b : K) : ℂ) = ∑ j ∈ s, (a j : ℂ) * (z : ℂ) ^ e j := by
  refine ⟨⟨∑ j ∈ s, (a j : K) * z ^ e j, (mem_integralClosure_iff ℤ K).mpr
    (IsIntegral.sum _ fun j _ => (isIntegral_algebraMap (x := a j)).mul (hz.pow _))⟩, ?_⟩
  simp [NumberField.RingOfIntegers.map_mk]

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
  -- Expansion: `X` is a sum of packets of quotient twists of extensions `χ i` plus an induced
  -- virtual character.
  obtain ⟨χ, ε, a, Y, hχ, hres, hε, -, hXsum⟩ :=
    exists_sum_quotient_twists_add_indClassFun hp hx hζ hX
  rw [finsum_eq_sum_of_fintype] at hXsum
  -- The packet coefficients `∑ j, a i j * ζ ^ j` are algebraic integers of the abelian number
  -- field `K = ℚ(ζ)`.
  let K := IntermediateField.adjoin ℚ ({ζ} : Set ℂ)
  let : NeZero N.index := ⟨hp.ne_zero⟩
  let : IsCyclotomicExtension {N.index} ℚ K := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  let : NumberField K := IsCyclotomicExtension.numberField {N.index} ℚ K
  let : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {N.index} ℚ K
  let z : K := ⟨ζ, IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩
  have hz : IsPrimitiveRoot z N.index := hζ.of_map_of_injective K.val.injective
  choose b hb using fun i =>
    exists_ringOfIntegers_coe_eq_sum (hz.isIntegral hp.pos) univ (a i) Fin.val
  let φ := K.val.toRingHom
  have hφ (y : K) : φ y = y := by simp [φ]
  -- Coset evaluation: on `x N` the induced part vanishes and each packet is its coefficient
  -- times `χ i`.
  have hcoset (n : N) : X (x * n) = ∑ i, ((b i : K) : ℂ) * χ i (x * n) := by
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
  -- Norm sum: coset orthogonality turns the norm-one condition into `∑ i, |b i|² = 1`.
  have hpair := inv_natCard_mul_sum_mul_conj_eq_sum_normSq x χ hχ
    (fun i => by simpa only [hres] using irreducibleCharacter_mem ℂ i.val)
    (fun i j hij => Subtype.ext (irreducibleCharacter_injective (k := ℂ) (funext fun n =>
        (hres i n).symm.trans ((congrFun hij n).trans (hres j n))))) (fun i => ((b i : K) : ℂ))
  have hsum : ∑ i, Complex.normSq (φ (b i)) = 1 := by
    simp only [hφ]
    rw [← Complex.ofReal_inj, Complex.ofReal_sum, Complex.ofReal_one, ← hpair]
    refine Eq.trans ?_ hnorm
    congr 1
    exact sum_congr rfl fun n _ => by rw [hcoset n]
  -- Rigidity: a sum of squared absolute values of algebraic integers of an abelian field equal to
  -- `1` has a single nonzero term, a root of unity.
  obtain ⟨i, -, hi, hzero⟩ := (Finset.sum_normSq_eq_one_iff_of_isAbelianGalois univ b φ).mp hsum
  refine ⟨_, irreducibleCharacter_mem ℂ i.val, i.property, χ i, hχ i, hres i, b i, hi, fun n => ?_⟩
  rw [hcoset, sum_eq_single_of_mem i (mem_univ _) (fun j hj hji => by simp [hzero j hj hji])]

end TauCeti

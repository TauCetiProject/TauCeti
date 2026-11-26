/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra
public import TauCeti.Algebra.Homology.DG.Algebra.Defs
public import TauCeti.Algebra.Module.GradedModule.TensorProduct.Basic
import TauCeti.Algebra.GradedMonoid
import TauCeti.Algebra.Homology.AInfinity.Algebra.CoaugmentedBar
import TauCeti.Data.List.ProdOfFn
import TauCeti.LinearAlgebra.TensorAlgebra.Basic
import TauCeti.LinearAlgebra.TensorAlgebra.Grading
import TauCeti.LinearAlgebra.TensorCoalgebra.Brace
import TauCeti.LinearAlgebra.TensorCoalgebra.Splice
import TauCeti.RingTheory.GradedAlgebra.TensorProduct

/-!
# Tensor products of `A∞` algebras with DG algebras

Let `A` be an `A∞` algebra and `(B, d_B)` a differential graded algebra.  The tensor product
`A ⊗ B`, graded by total degree, is an `A∞` algebra with operations

`m₁ (a ⊗ b) = m₁ a ⊗ b + (-1) ^ |a| • (a ⊗ d_B b)`,

`mₙ (a₀ ⊗ b₀, …, aₙ₋₁ ⊗ bₙ₋₁) = (-1) ^ (∑_{i < j} |bᵢ| |aⱼ|) • (mₙ (a₀, …, aₙ₋₁) ⊗ b₀ ⋯ bₙ₋₁)`
for `n ≥ 2`.

The sign is the Koszul sign of moving every `bᵢ` past every later `aⱼ`.  The tensor product of
two `A∞` algebras needs a diagonal of the associahedra, which involves choices.  When the second
factor is a DG algebra no choice is needed: its operations above arity two vanish, and the
product of the `bᵢ` is defined in every arity.  Examples are matrix algebras `A ⊗ Mₙ(R)` and
extensions of the coefficients of `A` by polynomial or exterior algebras.

The structure lives on the suspended bar construction.  The *signed shuffle*
`Tᶜ(s(A ⊗ B)) ⟶ Tᶜ(sA) ⊗ B` sends a word of letters `aⱼ ⊗ bⱼ` to the word of the `aⱼ` tensored
with the product of the `bⱼ`, with the Koszul sign of the suspended degrees; it is the
multiplicative extension of `a ⊗ b ↦ a ⊗ b` into Mathlib's Koszul-signed tensor product of the
tensor algebra of `sA` with `B`.  The suspended Taylor map of `A ⊗ B` is the single-letter part of
`D_A ⊗ 1 - τ ⊗ d_B` on the shuffled word, with `D_A` the bar differential of `A` and `τ` the
Koszul twist of words; the minus sign appears because the suspension `s (a ⊗ b) = s a ⊗ b` lets
`d_B` cross `s a` rather than `a`.  The shuffle intertwines the bar differential of `A ⊗ B` with
`D_A ⊗ 1 - τ ⊗ d_B`, whose square vanishes, and this gives the square-zero law.

## Main definitions

* `TauCeti.AInfinity.shuffleExp`: the exponent of the Koszul sign of the shuffle.
* `TauCeti.AInfinityAlgebra.tensorDGAlgebra`: the tensor product of an `A∞` algebra with a DG
  algebra.

## Main results

* `TauCeti.AInfinityAlgebra.tensorDGAlgebra_grading`: the grading is by total degree.
* `TauCeti.AInfinityAlgebra.tensorDGAlgebra_taylor_of_tprod`: its suspended Taylor map on words of
  length at least two.
* `TauCeti.AInfinityAlgebra.tensorDGAlgebra_m_one_apply`: its unary operation is
  `m₁ ⊗ 1 + 1 ⊗ d_B` with the Koszul sign.
* `TauCeti.AInfinityAlgebra.tensorDGAlgebra_m_apply`: its higher operations are those of `A`
  tensored with the product of `B`, with the Koszul sign of the shuffle.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Homology, Homotopy and
  Applications 3 (2001), Sections 3.1 and 3.6, for the conventions and the suspended bar
  construction.
* M. Markl and S. Shnider, *Associahedra, cellular W-construction and products of
  `A∞`-algebras*, Transactions of the AMS 358 (2006), for the diagonal needed to tensor two `A∞`
  algebras, which this file avoids.
-/

public section

open scoped TensorProduct DirectSum

namespace TauCeti

universe uR uA uB

namespace AInfinity

/-- The exponent of the Koszul sign of the shuffle `(x₀ ⊗ y₀) ⊗ ⋯ ⊗ (xₙ₋₁ ⊗ yₙ₋₁) ↦
(x₀ ⊗ ⋯ ⊗ xₙ₋₁) ⊗ (y₀ ⋯ yₙ₋₁)` on inputs `xⱼ` of degree `dA j` and `yᵢ` of degree `dB i`: every
`yᵢ` moves past every later `xⱼ`. -/
def shuffleExp (n : ℕ) (dA dB : ℕ → ℤ) : ℤ :=
  ∑ j ∈ Finset.range n, (∑ i ∈ Finset.range j, dB i) * dA j

/-- The defining sum of the shuffle exponent. -/
theorem shuffleExp_def (n : ℕ) (dA dB : ℕ → ℤ) :
    shuffleExp n dA dB = ∑ j ∈ Finset.range n, (∑ i ∈ Finset.range j, dB i) * dA j := (rfl)

/-- The empty string has trivial shuffle sign. -/
@[simp]
theorem shuffleExp_zero (dA dB : ℕ → ℤ) : shuffleExp 0 dA dB = 0 := by
  simp [shuffleExp_def]

/-- Appending a letter moves the earlier `dB i` past its `A`-degree. -/
theorem shuffleExp_succ (n : ℕ) (dA dB : ℕ → ℤ) :
    shuffleExp (n + 1) dA dB = shuffleExp n dA dB + (∑ i ∈ Finset.range n, dB i) * dA n := by
  rw [shuffleExp_def, Finset.sum_range_succ, ← shuffleExp_def]

/-- A single letter has trivial shuffle sign. -/
@[simp]
theorem shuffleExp_one (dA dB : ℕ → ℤ) : shuffleExp 1 dA dB = 0 := by
  simp [shuffleExp_succ]

/-- The shuffle exponent of a concatenation of two strings: the exponents of the two strings and
the sign of moving every `y` of the first string past every `x` of the second. -/
theorem shuffleExp_add (n m : ℕ) (dA dB : ℕ → ℤ) :
    shuffleExp (n + m) dA dB = shuffleExp n dA dB + shuffleExp m (fun j ↦ dA (n + j))
      (fun j ↦ dB (n + j)) + (∑ i ∈ Finset.range n, dB i) * ∑ j ∈ Finset.range m, dA (n + j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, shuffleExp_succ, ih, shuffleExp_succ, Finset.sum_range_add,
      Finset.sum_range_succ]
    ring

/-- The shuffle exponent only reads the degrees below the length of the string. -/
theorem shuffleExp_congr {n : ℕ} {dA dB eA eB : ℕ → ℤ} (hA : ∀ i < n, dA i = eA i)
    (hB : ∀ i < n, dB i = eB i) : shuffleExp n dA dB = shuffleExp n eA eB := by
  rw [shuffleExp_def, shuffleExp_def]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  rw [hA j hj, Finset.sum_congr rfl fun i hi ↦ hB i (by rw [Finset.mem_range] at hi; omega)]

/-- Raising the `B`-degree at `p` by one raises the shuffle exponent by the `A`-degrees of the
letters after `p`. -/
private theorem shuffleExp_replaceBlock_succ (dA dB : ℕ → ℤ) {p n : ℕ} (hp : p < n) :
    shuffleExp n dA (replaceBlock dB p 1 (dB p + 1)) =
      shuffleExp n dA dB + ∑ j ∈ Finset.range n, dA j - ∑ j ∈ Finset.range (p + 1), dA j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [shuffleExp_succ, shuffleExp_succ, sum_range_replaceBlock_one, Finset.sum_range_succ dA n]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hp with h | rfl
    · rw [ih h, ite_eq_left h]
      ring
    · rw [shuffleExp_congr (fun i _ ↦ rfl) fun i hi ↦ replaceBlock_of_lt dB p 1 _ hi,
        ite_eq_right (lt_irrefl p), Finset.sum_range_succ dA p]
      ring

/-- The sign identity matching the terms of the bar differential of a tensor product which apply a
higher operation of `A` to a block: the sign of the twisted prefix, the shuffle sign inside the
block and the shuffle sign of the word with the block collapsed together give the shuffle sign of
the whole word times the prefix sign of the bar differential of `A`. -/
private theorem negOnePow_splice (dA dB : ℕ → ℤ) (p d t : ℕ) :
    (∑ j ∈ Finset.range p, (dA j + dB j) +
        shuffleExp d (fun j ↦ dA (p + j)) (fun j ↦ dB (p + j)) +
        shuffleExp (p + 1 + t) (replaceBlock dA p d (∑ j ∈ Finset.range d, dA (p + j) + 1))
          (replaceBlock dB p d (∑ j ∈ Finset.range d, dB (p + j)))).negOnePow =
      (shuffleExp (p + d + t) dA dB + ∑ j ∈ Finset.range p, dA j).negOnePow := by
  set eA := replaceBlock dA p d (∑ j ∈ Finset.range d, dA (p + j) + 1)
  set eB := replaceBlock dB p d (∑ j ∈ Finset.range d, dB (p + j))
  have hltA : ∀ i < p, eA i = dA i := fun i h ↦ replaceBlock_of_lt _ _ _ _ h
  have hltB : ∀ i < p, eB i = dB i := fun i h ↦ replaceBlock_of_lt _ _ _ _ h
  have hgtA : ∀ i, p < i → eA i = dA (i + d - 1) := fun i h ↦ replaceBlock_of_gt _ _ _ _ h
  have hgtB : ∀ i, p < i → eB i = dB (i + d - 1) := fun i h ↦ replaceBlock_of_gt _ _ _ _ h
  have hA : eA p = ∑ j ∈ Finset.range d, dA (p + j) + 1 := replaceBlock_self _ _ _ _
  have hB : eB p = ∑ j ∈ Finset.range d, dB (p + j) := replaceBlock_self _ _ _ _
  have h₁ := shuffleExp_add p (d + t) dA dB
  have h₂ := shuffleExp_add d t (fun j ↦ dA (p + j)) (fun j ↦ dB (p + j))
  have h₃ := shuffleExp_add p (1 + t) eA eB
  have h₄ := shuffleExp_add 1 t (fun j ↦ eA (p + j)) (fun j ↦ eB (p + j))
  have c₁ : shuffleExp p eA eB = shuffleExp p dA dB := shuffleExp_congr hltA hltB
  have c₂ : ∑ i ∈ Finset.range p, eB i = ∑ i ∈ Finset.range p, dB i :=
    Finset.sum_congr rfl fun i hi ↦ hltB i (Finset.mem_range.1 hi)
  have c₃ : shuffleExp t (fun j ↦ eA (p + (1 + j))) (fun j ↦ eB (p + (1 + j))) =
      shuffleExp t (fun j ↦ dA (p + (d + j))) (fun j ↦ dB (p + (d + j))) :=
    shuffleExp_congr (fun i _ ↦ by rw [hgtA _ (by omega)]; congr 1; omega)
      fun i _ ↦ by rw [hgtB _ (by omega)]; congr 1; omega
  have c₄ : ∑ i ∈ Finset.range 1, eB (p + i) = ∑ j ∈ Finset.range d, dB (p + j) := by
    rw [Finset.sum_range_one, add_zero, hB]
  have c₅ : ∑ j ∈ Finset.range t, eA (p + (1 + j)) = ∑ j ∈ Finset.range t, dA (p + (d + j)) :=
    Finset.sum_congr rfl fun j _ ↦ by rw [hgtA _ (by omega)]; congr 1; omega
  have c₆ : ∑ j ∈ Finset.range (1 + t), eA (p + j) =
      ∑ j ∈ Finset.range d, dA (p + j) + 1 + ∑ j ∈ Finset.range t, dA (p + (d + j)) := by
    rw [Finset.sum_range_add, Finset.sum_range_one, add_zero, hA, c₅]
  have c₇ : ∑ j ∈ Finset.range (d + t), dA (p + j) =
      ∑ j ∈ Finset.range d, dA (p + j) + ∑ j ∈ Finset.range t, dA (p + (d + j)) :=
    Finset.sum_range_add _ _ _
  rw [shuffleExp_one] at h₄
  beta_reduce at h₁ h₂ h₃ h₄
  rw [show p + 1 + t = p + (1 + t) by omega, show p + d + t = p + (d + t) by omega, h₁, h₂, h₃,
    h₄, c₁, c₂, c₃, c₄, c₅, c₆, c₇, Finset.sum_add_distrib, Int.negOnePow_eq_iff]
  exact ⟨∑ i ∈ Finset.range p, dB i, by ring⟩

/-- Suspending the first degrees of a shuffle exponent: every `dB i` moves past one more letter of
degree `-1` for each later letter. -/
private theorem shuffleExp_sub_one (n : ℕ) (dA dB : ℕ → ℤ) :
    shuffleExp n (fun j ↦ dA j - 1) dB =
      shuffleExp n dA dB - ∑ i ∈ Finset.range n, ((n : ℤ) - 1 - i) * dB i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [shuffleExp_succ, shuffleExp_succ, ih, Finset.sum_range_succ, Nat.cast_succ]
    simp only [add_sub_cancel_right, sub_self, zero_mul, add_zero]
    rw [show ∑ i ∈ Finset.range n, ((n : ℤ) - i) * dB i =
        ∑ i ∈ Finset.range n, (((n : ℤ) - 1 - i) * dB i + dB i) from
      Finset.sum_congr rfl fun i _ ↦ by ring, Finset.sum_add_distrib]
    ring

end AInfinity

namespace AInfinityAlgebra

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R] [AddCommGroup A] [Module R A]
  [Ring B] [Algebra R B]

section Shuffle

variable (𝒜 : AInfinityAlgebra R A) (ℬ : ℤ → Submodule R B) [GradedAlgebra ℬ]

/-- The letter map `a ⊗ b ↦ ι a ᵍ⊗ b` into the Koszul-signed tensor product of the tensor algebra
of `A`, graded by suspended degree, with `B`. -/
private noncomputable def shuffleLetter :
    A ⊗[R] B →ₗ[R] tensorAlgebraPiece (𝒜.grading.shift 1) ᵍ⊗[R] ℬ :=
  (GradedTensorProduct.of R (tensorAlgebraPiece (𝒜.grading.shift 1)) ℬ).toLinearMap ∘ₗ
    TensorProduct.map (TensorAlgebra.ι R) LinearMap.id

/-- The letter map on a pure tensor. -/
private theorem shuffleLetter_tmul (a : A) (b : B) :
    shuffleLetter 𝒜 ℬ (a ⊗ₜ b) = TensorAlgebra.ι R a ᵍ⊗ₜ[R] b :=
  (rfl)

/-- The product of the letters `aⱼ ⊗ bⱼ` in the Koszul-signed tensor product: the shuffle sign
times the word of the `aⱼ` tensored with the product of the `bⱼ`. -/
private theorem lift_shuffleLetter_tprod (n : ℕ) (a : ℕ → A) (b : ℕ → B) (dA dB : ℕ → ℤ)
    (ha : ∀ i < n, a i ∈ (𝒜.grading.shift 1).piece (dA i)) (hb : ∀ i < n, b i ∈ ℬ (dB i)) :
    TensorAlgebra.lift R (shuffleLetter 𝒜 ℬ)
        (TensorAlgebra.tprod R (A ⊗[R] B) n fun j ↦ a j ⊗ₜ b j) =
      negOnePowCast R (AInfinity.shuffleExp n dA dB) •
        (TensorAlgebra.tprod R A n (fun j ↦ a j) ᵍ⊗ₜ[R]
          (List.ofFn fun j : Fin n ↦ b j).prod) := by
  induction n with
  | zero =>
    simp only [TensorAlgebra.tprod_apply, List.ofFn_zero, List.prod_nil, map_one,
      AInfinity.shuffleExp_zero, negOnePowCast_zero, one_smul]
    exact (GradedTensorProduct.of_one (tensorAlgebraPiece (𝒜.grading.shift 1)) ℬ).symm
  | succ n ih =>
    simp only [TensorAlgebra.tprod_succ, Fin.val_castSucc, Fin.val_last]
    rw [map_mul, ih (fun i hi ↦ ha i (by omega)) (fun i hi ↦ hb i (by omega)),
      TensorAlgebra.lift_ι_apply, shuffleLetter_tmul, smul_mul_assoc, List.prod_ofFn_val_succ b]
    have hA : TensorAlgebra.ι R (a n) ∈ tensorAlgebraPiece (𝒜.grading.shift 1) (dA n) :=
      ι_mem_tensorAlgebraPiece _ (ha n (by omega))
    have hB := SetLike.list_prod_ofFn_val_mem_graded ℬ (n := n) b dB fun i hi ↦ hb i (by omega)
    have hmul := GradedTensorProduct.tmul_coe_mul_coe_tmul (R := R)
      (𝒜 := tensorAlgebraPiece (𝒜.grading.shift 1)) (ℬ := ℬ)
      (TensorAlgebra.tprod R A n (fun j : Fin n ↦ a j)) ⟨_, hB⟩ ⟨_, hA⟩ (b n)
    dsimp only at hmul
    rw [hmul, ← Int.negOnePow_def, negOnePow_smul_eq_negOnePowCast_smul (R := R), smul_smul,
      ← negOnePowCast_add, AInfinity.shuffleExp_succ]

/-- The signed shuffle `Tᶜ(s(A ⊗ B)) ⟶ Tᶜ(sA) ⊗ B`: a word of letters `aⱼ ⊗ bⱼ` goes to the
word of the `aⱼ` tensored with the product of the `bⱼ`, with the Koszul sign of moving every `bᵢ`
past every later `aⱼ`.  It is the multiplicative extension of `a ⊗ b ↦ a ⊗ b` into the
Koszul-signed tensor product of the tensor algebra of `sA` with `B`. -/
private noncomputable def shuffle : TensorWords R (A ⊗[R] B) →ₗ[R] TensorWords R A ⊗[R] B :=
  TensorProduct.map TensorAlgebra.toDirectSum.toLinearMap LinearMap.id ∘ₗ
    (GradedTensorProduct.of R (tensorAlgebraPiece (𝒜.grading.shift 1)) ℬ).symm.toLinearMap ∘ₗ
      (TensorAlgebra.lift R (shuffleLetter 𝒜 ℬ)).toLinearMap ∘ₗ
        TensorAlgebra.ofDirectSum.toLinearMap

/-- The signed shuffle on a word of pure tensors of homogeneous elements. -/
private theorem shuffle_of_tprod (n : ℕ) (a : ℕ → A) (b : ℕ → B) (dA dB : ℕ → ℤ)
    (ha : ∀ i < n, a i ∈ (𝒜.grading.shift 1).piece (dA i)) (hb : ∀ i < n, b i ∈ ℬ (dB i)) :
    shuffle 𝒜 ℬ
        (TensorWords.of R (A ⊗[R] B) n (PiTensorProduct.tprod R fun j : Fin n ↦ a j ⊗ₜ b j)) =
      negOnePowCast R (AInfinity.shuffleExp n dA dB) •
        (TensorWords.of R A n (PiTensorProduct.tprod R fun j : Fin n ↦ a j) ⊗ₜ
          (List.ofFn fun j : Fin n ↦ b j).prod) := by
  simp only [shuffle, LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe,
    TensorWords.of_def, DirectSum.lof_eq_of, TensorAlgebra.ofDirectSum_of_tprod]
  rw [lift_shuffleLetter_tprod 𝒜 ℬ n a b dA dB ha hb, map_smul, map_smul]
  simp only [GradedTensorProduct.tmul, GradedTensorProduct.of_symm_of, TensorProduct.map_tmul,
    AlgHom.toLinearMap_apply, TensorAlgebra.toDirectSum_tensorPower_tprod, LinearMap.id_apply]

end Shuffle

section Taylor

variable (𝒜 : AInfinityAlgebra R A) (ℬ : ℤ → Submodule R B) [GradedAlgebra ℬ] (dB : B →ₗ[R] B)

/-- The suspended Taylor map of the tensor product: a word of `s(A ⊗ B) = sA ⊗ B` is shuffled into
`Tᶜ(sA) ⊗ B`, the differential `D_A ⊗ 1 + τ ⊗ d_B` is applied, and the single-letter part is
kept. -/
private noncomputable def tensorTaylor : ReducedTensorWords R (A ⊗[R] B) →ₗ[R] A ⊗[R] B :=
  TensorProduct.map (ReducedTensorWords.letter R A ∘ₗ TensorWords.reducedProjection R A)
      LinearMap.id ∘ₗ
    𝒜.leftUnaryDifferential dB ∘ₗ shuffle 𝒜 ℬ ∘ₗ TensorWords.reducedInclusion R (A ⊗[R] B)

/-- The signed shuffle of a word of pure tensors of positive length. -/
private theorem shuffle_reducedInclusion_of_tprod {n : ℕ} (hn : 0 < n) (a : ℕ → A) (b : ℕ → B)
    (dA dB : ℕ → ℤ) (ha : ∀ i < n, a i ∈ (𝒜.grading.shift 1).piece (dA i))
    (hb : ∀ i < n, b i ∈ ℬ (dB i)) :
    shuffle 𝒜 ℬ (TensorWords.reducedInclusion R (A ⊗[R] B)
        (ReducedTensorWords.of R (A ⊗[R] B) ⟨n, hn⟩
          (PiTensorProduct.tprod R fun j : Fin n ↦ a j ⊗ₜ b j))) =
      negOnePowCast R (AInfinity.shuffleExp n dA dB) •
        (TensorWords.reducedInclusion R A
            (ReducedTensorWords.of R A ⟨n, hn⟩ (PiTensorProduct.tprod R fun j : Fin n ↦ a j)) ⊗ₜ
          (List.ofFn fun j : Fin n ↦ b j).prod) := by
  rw [TensorWords.reducedInclusion_of, TensorWords.reducedInclusion_of]
  exact shuffle_of_tprod 𝒜 ℬ n a b dA dB ha hb

/-- The Taylor map of the tensor product on a word of pure tensors of homogeneous elements: the
Taylor map of `A` tensored with the product of the `bⱼ`, plus, on single letters, the twisted letter
tensored with `d_B` of it, all with the shuffle sign. -/
private theorem tensorTaylor_of_tprod {n : ℕ} (hn : 0 < n) (a : ℕ → A) (b : ℕ → B)
    (dA dB' : ℕ → ℤ) (ha : ∀ i < n, a i ∈ (𝒜.grading.shift 1).piece (dA i))
    (hb : ∀ i < n, b i ∈ ℬ (dB' i)) :
    tensorTaylor 𝒜 ℬ dB (ReducedTensorWords.of R (A ⊗[R] B) ⟨n, hn⟩
        (PiTensorProduct.tprod R fun j : Fin n ↦ a j ⊗ₜ b j)) =
      negOnePowCast R (AInfinity.shuffleExp n dA dB') •
        (𝒜.taylor (ReducedTensorWords.of R A ⟨n, hn⟩ (PiTensorProduct.tprod R fun j : Fin n ↦ a j))
            ⊗ₜ (List.ofFn fun j : Fin n ↦ b j).prod +
          negOnePowCast R (∑ i ∈ Finset.range n, dA i) •
            (ReducedTensorWords.letter R A
                (ReducedTensorWords.of R A ⟨n, hn⟩ (PiTensorProduct.tprod R fun j : Fin n ↦ a j)) ⊗ₜ
              dB (List.ofFn fun j : Fin n ↦ b j).prod)) := by
  have hmem := TensorWords.reducedInclusion_of_tprod_mem_gradedPiece _ hn a dA ha
  rw [← TensorWords.grading_piece] at hmem
  rw [tensorTaylor, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    shuffle_reducedInclusion_of_tprod 𝒜 ℬ hn a b dA dB' ha hb, map_smul, map_smul,
    leftUnaryDifferential_tmul, ← TensorWords.koszulTwist_grading,
    InternalGrading.koszulTwist_apply_of_mem _ hmem, one_mul,
    ← LinearMap.comp_apply 𝒜.coaugmentedBarDifferential,
    coaugmentedBarDifferential_comp_reducedInclusion]
  simp only [LinearMap.comp_apply, TensorProduct.smul_tmul', map_add, map_smul,
    TensorProduct.map_tmul, TensorWords.reducedProjection_reducedInclusion, LinearMap.id_apply,
    negOnePowCast_eq_intCast]
  rw [← LinearMap.comp_apply (ReducedTensorWords.letter R A), letter_comp_barDifferential]

/-- The signed shuffle of a word of pure tensors with a block collapsed to a pure tensor. -/
private theorem shuffle_reducedInclusion_splice (a : ℕ → A) (b : ℕ → B) (dA dB' : ℕ → ℤ)
    {p d t : ℕ} (hd : 0 < d) (ha : ∀ i < p + d + t, a i ∈ (𝒜.grading.shift 1).piece (dA i))
    (hb : ∀ i < p + d + t, b i ∈ ℬ (dB' i)) {a' : A} {b' : B} {α β : ℤ}
    (ha' : a' ∈ (𝒜.grading.shift 1).piece α) (hb' : b' ∈ ℬ β) :
    shuffle 𝒜 ℬ (TensorWords.reducedInclusion R (A ⊗[R] B) (ReducedTensorWords.splice R
        (fun j : Fin (p + d + t) ↦ a j ⊗ₜ[R] b j) 0 (p + d + t) p d (a' ⊗ₜ b'))) =
      negOnePowCast R (AInfinity.shuffleExp (p + 1 + t) (replaceBlock dA p d α)
          (replaceBlock dB' p d β)) •
        (TensorWords.reducedInclusion R A
            (ReducedTensorWords.splice R (fun j : Fin (p + d + t) ↦ a j) 0 (p + d + t) p d a') ⊗ₜ
          (List.ofFn fun j : Fin (p + 1 + t) ↦ replaceBlock b p d b' j).prod) := by
  rw [ReducedTensorWords.splice_eq_of_tprod_replaceBlock_add R (fun i ↦ a i ⊗ₜ[R] b i) hd,
    ReducedTensorWords.splice_eq_of_tprod_replaceBlock_add R a hd]
  simp only [← apply₂_replaceBlock (TensorProduct.tmul R) a b]
  exact shuffle_reducedInclusion_of_tprod 𝒜 ℬ _ _ _ _ _
    (fun i hi ↦ replaceBlock_mem _ ha ha' (by omega) (by omega))
    fun i hi ↦ replaceBlock_mem _ hb hb' (by omega) (by omega)

/-- The shuffled `(p, d)` term of the bar differential of the tensor product, for a block that
fits: the shuffled term of the bar differential of `A`, and for `d = 1` also the `d_B` term of
the Leibniz rule at `p`. -/
private theorem shuffle_splice_tensorTaylor_of_fits (hB : IsDGAlgebra ℬ dB) (a : ℕ → A)
    (b : ℕ → B) (dA dB' : ℕ → ℤ) {p d t : ℕ} (hd : 0 < d)
    (ha : ∀ i < p + d + t, a i ∈ (𝒜.grading.shift 1).piece (dA i))
    (hb : ∀ i < p + d + t, b i ∈ ℬ (dB' i)) :
    negOnePowCast R (∑ j ∈ Finset.range p, (dA j + dB' j)) •
      shuffle 𝒜 ℬ (TensorWords.reducedInclusion R (A ⊗[R] B) (ReducedTensorWords.splice R
        (fun j : Fin (p + d + t) ↦ a j ⊗ₜ[R] b j) 0 (p + d + t) p d (tensorTaylor 𝒜 ℬ dB
          (ReducedTensorWords.subword R (fun j : Fin (p + d + t) ↦ a j ⊗ₜ[R] b j) p d)))) =
      negOnePowCast R (AInfinity.shuffleExp (p + d + t) dA dB') •
        (negOnePowCast R (∑ j ∈ Finset.range p, dA j) •
          (TensorWords.reducedInclusion R A (ReducedTensorWords.splice R
            (fun j : Fin (p + d + t) ↦ a j) 0 (p + d + t) p d
              (𝒜.taylor (ReducedTensorWords.subword R (fun j : Fin (p + d + t) ↦ a j) p d))) ⊗ₜ
            (List.ofFn fun j : Fin (p + d + t) ↦ b j).prod) +
        if d = 1 then
          negOnePowCast R (∑ j ∈ Finset.range (p + d + t), dA j + ∑ j ∈ Finset.range p, dB' j) •
            (TensorWords.reducedInclusion R A (ReducedTensorWords.of R A ⟨p + d + t, by omega⟩
              (PiTensorProduct.tprod R fun j : Fin (p + d + t) ↦ a j)) ⊗ₜ
                (List.ofFn fun j : Fin (p + d + t) ↦ Function.update b p (dB (b p)) j).prod)
        else 0) := by
  have hpd : p + d ≤ p + d + t := by omega
  rw [ReducedTensorWords.subword_eq_of_tprod R _ hd hpd,
    ReducedTensorWords.subword_eq_of_tprod R _ hd hpd]
  have hF := tensorTaylor_of_tprod 𝒜 ℬ dB hd (fun j ↦ a (p + j)) (fun j ↦ b (p + j))
    (fun j ↦ dA (p + j)) (fun j ↦ dB' (p + j)) (fun i _ ↦ ha _ (by omega))
    fun i _ ↦ hb _ (by omega)
  have hl := ReducedTensorWords.letter_of_tprod R A hd (fun j ↦ a (p + j))
  beta_reduce at hF hl ⊢
  rw [hF, hl, ReducedTensorWords.splice_smul, ReducedTensorWords.splice_add,
    ReducedTensorWords.splice_smul, map_smul, map_smul, map_add, map_add, map_smul, map_smul,
    shuffle_reducedInclusion_splice 𝒜 ℬ a b dA dB' hd ha hb
      (taylor_of_tprod_mem 𝒜 hd (fun j ↦ a (p + j)) (fun j ↦ dA (p + j)) fun i _ ↦ ha _ (by omega))
      (SetLike.list_prod_ofFn_val_mem_graded ℬ (n := d) (fun j ↦ b (p + j)) (fun j ↦ dB' (p + j))
        fun i _ ↦ hb _ (by omega)),
    prod_ofFn_replaceBlock b p d t]
  have hsplice := AInfinity.negOnePow_splice dA dB' p d t
  by_cases hd1 : d = 1
  · subst hd1
    have hP : (List.ofFn fun j : Fin 1 ↦ b (p + j)).prod = b p := by simp
    rw [ite_eq_left rfl, ite_eq_left rfl, add_zero, hP,
      shuffle_reducedInclusion_splice 𝒜 ℬ a b dA dB' hd ha hb (ha p (by omega))
        (hB.map_mem (hb p (by omega))),
      ReducedTensorWords.splice_eq_of_tprod_replaceBlock_add R a hd (a p), replaceBlock_one_self,
      replaceBlock_one_self, replaceBlock_one b p]
    simp only [AInfinity.shuffleExp_one, Finset.sum_range_one, add_zero, negOnePowCast_zero,
      one_smul] at hsplice ⊢
    simp only [smul_add, smul_smul, ← negOnePowCast_add]
    congr 2
    · exact negOnePowCast_eq_of_even_sub (by convert (Int.negOnePow_eq_iff _ _).1 hsplice using 1)
    · -- Raising the degree of `b p` by one moves `d_B` past the `A`-degrees of the later letters.
      refine negOnePowCast_eq_of_even_sub ⟨0, ?_⟩
      rw [AInfinity.shuffleExp_replaceBlock_succ dA dB' (by omega), Finset.sum_add_distrib,
        Finset.sum_range_succ]
      ring
  · rw [ite_eq_right hd1, ite_eq_right hd1, TensorProduct.zero_tmul,
      ReducedTensorWords.splice_zero, map_zero, map_zero, smul_zero, add_zero, add_zero]
    simp only [smul_smul, ← negOnePowCast_add]
    congr 1
    refine negOnePowCast_eq_of_even_sub ?_
    convert (Int.negOnePow_eq_iff _ _).1 hsplice using 1
    ring

/-- The shuffled `(p, d)` term of the bar differential of the tensor product. -/
private theorem shuffle_splice_tensorTaylor (hB : IsDGAlgebra ℬ dB) (a : ℕ → A) (b : ℕ → B)
    (dA dB' : ℕ → ℤ) {n p d : ℕ} (hn : 0 < n) (hp : p < n)
    (ha : ∀ i < n, a i ∈ (𝒜.grading.shift 1).piece (dA i)) (hb : ∀ i < n, b i ∈ ℬ (dB' i)) :
    negOnePowCast R (∑ j ∈ Finset.range p, (dA j + dB' j)) •
      shuffle 𝒜 ℬ (TensorWords.reducedInclusion R (A ⊗[R] B) (ReducedTensorWords.splice R
        (fun j : Fin n ↦ a j ⊗ₜ[R] b j) 0 n p d (tensorTaylor 𝒜 ℬ dB
          (ReducedTensorWords.subword R (fun j : Fin n ↦ a j ⊗ₜ[R] b j) p d)))) =
      negOnePowCast R (AInfinity.shuffleExp n dA dB') •
        (negOnePowCast R (∑ j ∈ Finset.range p, dA j) •
          (TensorWords.reducedInclusion R A (ReducedTensorWords.splice R (fun j : Fin n ↦ a j) 0 n
            p d (𝒜.taylor (ReducedTensorWords.subword R (fun j : Fin n ↦ a j) p d))) ⊗ₜ
            (List.ofFn fun j : Fin n ↦ b j).prod) +
        if d = 1 then
          negOnePowCast R (∑ j ∈ Finset.range n, dA j + ∑ j ∈ Finset.range p, dB' j) •
            (TensorWords.reducedInclusion R A (ReducedTensorWords.of R A ⟨n, hn⟩
              (PiTensorProduct.tprod R fun j : Fin n ↦ a j)) ⊗ₜ
                (List.ofFn fun j : Fin n ↦ Function.update b p (dB (b p)) j).prod)
        else 0) := by
  by_cases hfit : 0 < d ∧ p + d ≤ n
  · obtain ⟨t, rfl⟩ : ∃ t, n = p + d + t := ⟨n - p - d, by omega⟩
    exact shuffle_splice_tensorTaylor_of_fits 𝒜 ℬ dB hB a b dA dB' hfit.1 ha hb
  · rw [ReducedTensorWords.splice_eq_zero_of_not_fits R _ _ hfit,
      ReducedTensorWords.splice_eq_zero_of_not_fits R _ _ hfit, map_zero, map_zero, map_zero,
      TensorProduct.zero_tmul, smul_zero, smul_zero, zero_add, ite_eq_right (by omega), smul_zero]

/-- **The shuffle intertwines the bar differentials.**  On a word of pure tensors of homogeneous
elements, shuffling the bar differential of the tensor product gives the differential
`D_A ⊗ 1 + τ ⊗ d_B` of the shuffled word. -/
private theorem shuffle_gradedCoderiv_of_tprod (hB : IsDGAlgebra ℬ dB) {n : ℕ} (hn : 0 < n)
    (a : ℕ → A) (b : ℕ → B) (dA dB' : ℕ → ℤ)
    (ha : ∀ i < n, a i ∈ (𝒜.grading.shift 1).piece (dA i)) (hb : ∀ i < n, b i ∈ ℬ (dB' i)) :
    shuffle 𝒜 ℬ (TensorWords.reducedInclusion R (A ⊗[R] B) (ReducedTensorWords.gradedCoderiv
        ((𝒜.grading.tensorProduct (InternalGrading.ofDecomposition ℬ)).shift 1)
        (tensorTaylor 𝒜 ℬ dB) 1 (ReducedTensorWords.of R (A ⊗[R] B) ⟨n, hn⟩
          (PiTensorProduct.tprod R fun j : Fin n ↦ a j ⊗ₜ b j)))) =
      𝒜.leftUnaryDifferential dB (shuffle 𝒜 ℬ (TensorWords.reducedInclusion R (A ⊗[R] B)
        (ReducedTensorWords.of R (A ⊗[R] B) ⟨n, hn⟩
          (PiTensorProduct.tprod R fun j : Fin n ↦ a j ⊗ₜ b j)))) := by
  have hmem := TensorWords.reducedInclusion_of_tprod_mem_gradedPiece _ hn a dA ha
  rw [← TensorWords.grading_piece] at hmem
  rw [ReducedTensorWords.gradedCoderiv_of_tprod_of_homogeneous_nat _ _ 1 hn (fun j ↦ a j ⊗ₜ b j)
      (fun j ↦ dA j + dB' j) fun i hi ↦ by
        rw [← InternalGrading.shift_tensorProduct_piece]
        exact InternalGrading.tmul_mem_tensorProduct _ (InternalGrading.ofDecomposition ℬ)
          (ha i hi) (by rw [InternalGrading.ofDecomposition_piece]; exact hb i hi),
    shuffle_reducedInclusion_of_tprod 𝒜 ℬ hn a b dA dB' ha hb, map_smul,
    leftUnaryDifferential_tmul, ← TensorWords.koszulTwist_grading,
    ← LinearMap.comp_apply 𝒜.coaugmentedBarDifferential,
    coaugmentedBarDifferential_comp_reducedInclusion, LinearMap.comp_apply, barDifferential_def,
    ReducedTensorWords.gradedCoderiv_of_tprod_of_homogeneous_nat _ _ 1 hn a dA ha,
    InternalGrading.koszulTwist_apply_of_mem _ hmem,
    hB.map_list_prod_ofFn b dB' hb]
  simp only [map_sum, map_smul, negOnePow_smul_eq_negOnePowCast_smul (R := R), one_mul]
  rw [Finset.sum_congr rfl fun p hp ↦ Finset.sum_congr rfl fun d _ ↦
    shuffle_splice_tensorTaylor 𝒜 ℬ dB hB a b dA dB' (d := d) hn (Finset.mem_range.1 hp) ha hb]
  simp only [← Finset.smul_sum, smul_add, Finset.sum_add_distrib]
  congr 2
  · simp only [← TensorProduct.smul_tmul', TensorProduct.sum_tmul]
  · rw [Finset.sum_congr rfl fun p _ ↦ Finset.sum_ite_eq' (Finset.range (n + 1)) 1 _]
    simp only [Finset.mem_range, show 1 < n + 1 by omega, ite_true, TensorProduct.tmul_sum,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_smul, ← negOnePowCast_eq_intCast,
      ← negOnePowCast_add]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [add_comm]

/-- **The shuffle intertwines the bar differentials**, as linear maps. -/
private theorem shuffle_comp_gradedCoderiv (hB : IsDGAlgebra ℬ dB) :
    shuffle 𝒜 ℬ ∘ₗ TensorWords.reducedInclusion R (A ⊗[R] B) ∘ₗ
        ReducedTensorWords.gradedCoderiv
          ((𝒜.grading.tensorProduct (InternalGrading.ofDecomposition ℬ)).shift 1)
          (tensorTaylor 𝒜 ℬ dB) 1 =
      𝒜.leftUnaryDifferential dB ∘ₗ shuffle 𝒜 ℬ ∘ₗ TensorWords.reducedInclusion R (A ⊗[R] B) := by
  refine DirectSum.linearMap_ext R fun n ↦ PiTensorProduct.ext_of_span_eq_top
    (g := fun _ (z : Σ pq : ℤ × ℤ, (𝒜.grading.shift 1).piece pq.1 × ℬ pq.2) ↦
      (z.2.1 : A) ⊗ₜ[R] (z.2.2 : B)) (fun _ ↦ by
      have h := InternalGrading.span_range_tmul_piece_eq_top (𝒜.grading.shift 1)
        (InternalGrading.ofDecomposition ℬ)
      rwa [InternalGrading.ofDecomposition_piece] at h)
    fun z ↦ ?_
  let a : ℕ → A := fun i ↦ if h : i < n.val then ((z ⟨i, h⟩).2.1 : A) else 0
  let b : ℕ → B := fun i ↦ if h : i < n.val then ((z ⟨i, h⟩).2.2 : B) else 0
  let dA : ℕ → ℤ := fun i ↦ if h : i < n.val then (z ⟨i, h⟩).1.1 else 0
  let dB' : ℕ → ℤ := fun i ↦ if h : i < n.val then (z ⟨i, h⟩).1.2 else 0
  have hz : (fun i ↦ ((z i).2.1 : A) ⊗ₜ[R] ((z i).2.2 : B)) = fun j : Fin n.val ↦ a j ⊗ₜ b j := by
    funext j
    simp [a, b, j.isLt]
  have h := shuffle_gradedCoderiv_of_tprod 𝒜 ℬ dB hB n.property a b dA dB'
    (fun i hi ↦ by simpa [a, dA, hi] using (z ⟨i, hi⟩).2.1.property)
    fun i hi ↦ by simp [b, dB', hi]
  simp only [LinearMap.comp_apply, hz]
  rwa [ReducedTensorWords.of_def] at h

/-- The signed shuffle preserves the suspended total degree. -/
private theorem isHomogeneous_shuffle :
    LinearMap.IsHomogeneous (shuffle 𝒜 ℬ)
      (TensorWords.gradedPiece
        ((𝒜.grading.tensorProduct (InternalGrading.ofDecomposition ℬ)).shift 1))
      ((TensorWords.grading (𝒜.grading.shift 1)).tensorProduct
        (InternalGrading.ofDecomposition ℬ)).piece 0 := by
  set 𝒯 := tensorAlgebraPiece (𝒜.grading.shift 1)
  have hletter : LinearMap.IsHomogeneous (shuffleLetter 𝒜 ℬ)
      ((𝒜.grading.tensorProduct (InternalGrading.ofDecomposition ℬ)).shift 1).piece
      (gradedTensorGrading 𝒯 ℬ) 0 := by
    rw [← InternalGrading.shift_tensorProduct_piece]
    refine LinearMap.isHomogeneous_def.2 fun d z hz ↦ ?_
    rw [add_zero]
    refine InternalGrading.tensorProduct_piece_le _ _ (C := (gradedTensorGrading 𝒯 ℬ d).comap _)
      (fun p a ha b hb ↦ ?_) hz
    rw [Submodule.mem_comap, shuffleLetter_tmul]
    have h := tmul_mem_gradedTensorGrading 𝒯 ℬ (ι_mem_tensorAlgebraPiece _ ha)
      (by rwa [InternalGrading.ofDecomposition_piece] at hb)
    rwa [add_sub_cancel] at h
  have hofDirectSum : LinearMap.IsHomogeneous TensorAlgebra.ofDirectSum.toLinearMap
      (TensorWords.gradedPiece ((𝒜.grading.tensorProduct
        (InternalGrading.ofDecomposition ℬ)).shift 1))
      (tensorAlgebraPiece ((𝒜.grading.tensorProduct
        (InternalGrading.ofDecomposition ℬ)).shift 1)) 0 :=
    LinearMap.isHomogeneous_def.2 fun d z hz ↦ by
      rwa [add_zero, mem_tensorAlgebraPiece_iff, AlgHom.toLinearMap_apply,
        TensorAlgebra.toDirectSum_ofDirectSum]
  have hsymm : LinearMap.IsHomogeneous
      (GradedTensorProduct.of R 𝒯 ℬ).symm.toLinearMap (gradedTensorGrading 𝒯 ℬ)
      ((InternalGrading.ofDecomposition 𝒯).tensorProduct (InternalGrading.ofDecomposition ℬ)).piece
      0 :=
    LinearMap.isHomogeneous_def.2 fun d z hz ↦ by
      rw [add_zero]
      refine gradedTensorGrading_le 𝒯 ℬ (C := Submodule.comap _ _) (fun p a ha b hb ↦ ?_) hz
      simpa [GradedTensorProduct.tmul, show p + (d - p) = d by ring] using
        InternalGrading.tmul_mem_tensorProduct (InternalGrading.ofDecomposition 𝒯)
          (InternalGrading.ofDecomposition ℬ) (p := p) (q := d - p)
          (by rwa [InternalGrading.ofDecomposition_piece])
          (by rwa [InternalGrading.ofDecomposition_piece])
  have htoDirectSum : LinearMap.IsHomogeneous TensorAlgebra.toDirectSum.toLinearMap
      (InternalGrading.ofDecomposition 𝒯).piece (TensorWords.grading (𝒜.grading.shift 1)).piece
      0 :=
    LinearMap.isHomogeneous_def.2 fun d z hz ↦ by
      rw [add_zero, TensorWords.grading_piece]
      rw [InternalGrading.ofDecomposition_piece] at hz
      exact mem_tensorAlgebraPiece_iff.1 hz
  simpa only [shuffle, add_zero] using
    ((htoDirectSum.tensorProduct (LinearMap.isHomogeneous_id _)).comp
      (hsymm.comp ((isHomogeneous_tensorAlgebraLift _ _ hletter).comp hofDirectSum)))

/-- The Taylor map of the tensor product has degree one for the suspended grading. -/
private theorem isHomogeneous_tensorTaylor (hB : IsDGAlgebra ℬ dB) :
    LinearMap.IsHomogeneous (tensorTaylor 𝒜 ℬ dB)
      (ReducedTensorWords.gradedPiece
        ((𝒜.grading.tensorProduct (InternalGrading.ofDecomposition ℬ)).shift 1))
      ((𝒜.grading.tensorProduct (InternalGrading.ofDecomposition ℬ)).shift 1).piece 1 := by
  have hι : LinearMap.IsHomogeneous (TensorWords.reducedInclusion R (A ⊗[R] B))
      (ReducedTensorWords.gradedPiece
        ((𝒜.grading.tensorProduct (InternalGrading.ofDecomposition ℬ)).shift 1))
      (TensorWords.gradedPiece
        ((𝒜.grading.tensorProduct (InternalGrading.ofDecomposition ℬ)).shift 1)) 0 :=
    LinearMap.isHomogeneous_def.2 fun d w hw ↦ by
      rw [add_zero]
      exact TensorWords.mem_gradedPiece_of_reducedInclusion hw
  have hd : LinearMap.IsHomogeneous dB (InternalGrading.ofDecomposition ℬ).piece
      (InternalGrading.ofDecomposition ℬ).piece 1 :=
    LinearMap.isHomogeneous_def.2 fun d b hb ↦ by
      rw [InternalGrading.ofDecomposition_piece] at hb ⊢
      exact hB.map_mem hb
  have hlet : LinearMap.IsHomogeneous
      (ReducedTensorWords.letter R A ∘ₗ TensorWords.reducedProjection R A)
      (TensorWords.grading (𝒜.grading.shift 1)).piece (𝒜.grading.shift 1).piece 0 := by
    rw [TensorWords.grading_piece]
    simpa only [add_zero] using (ReducedTensorWords.isHomogeneous_letter _).comp
      (TensorWords.isHomogeneous_reducedProjection _)
  have h := (hlet.tensorProduct (LinearMap.isHomogeneous_id _)).comp
    ((𝒜.isHomogeneous_leftUnaryDifferential hd).comp ((isHomogeneous_shuffle 𝒜 ℬ).comp hι))
  rw [InternalGrading.shift_tensorProduct_piece] at h
  simpa only [tensorTaylor, add_zero, zero_add] using h

/-- The bar coderivation of the Taylor map of the tensor product squares to zero. -/
private theorem gradedCoderiv_tensorTaylor_comp_self (hB : IsDGAlgebra ℬ dB) :
    ReducedTensorWords.gradedCoderiv
        ((𝒜.grading.tensorProduct (InternalGrading.ofDecomposition ℬ)).shift 1)
        (tensorTaylor 𝒜 ℬ dB) 1 ∘ₗ
      ReducedTensorWords.gradedCoderiv
        ((𝒜.grading.tensorProduct (InternalGrading.ofDecomposition ℬ)).shift 1)
        (tensorTaylor 𝒜 ℬ dB) 1 = 0 := by
  rw [ReducedTensorWords.gradedCoderiv_comp_self_eq_zero_iff
    (isHomogeneous_tensorTaylor 𝒜 ℬ dB hB) odd_one, ReducedTensorWords.brace_def]
  -- Unfold only the outer Taylor map, keeping the one inside the bar differential folded.
  have h : tensorTaylor 𝒜 ℬ dB ∘ₗ ReducedTensorWords.gradedCoderiv
      ((𝒜.grading.tensorProduct (InternalGrading.ofDecomposition ℬ)).shift 1)
      (tensorTaylor 𝒜 ℬ dB) 1 =
        TensorProduct.map (ReducedTensorWords.letter R A ∘ₗ TensorWords.reducedProjection R A)
          LinearMap.id ∘ₗ 𝒜.leftUnaryDifferential dB ∘ₗ
            (shuffle 𝒜 ℬ ∘ₗ TensorWords.reducedInclusion R (A ⊗[R] B) ∘ₗ
              ReducedTensorWords.gradedCoderiv
                ((𝒜.grading.tensorProduct (InternalGrading.ofDecomposition ℬ)).shift 1)
                (tensorTaylor 𝒜 ℬ dB) 1) :=
    (rfl)
  rw [h, shuffle_comp_gradedCoderiv 𝒜 ℬ dB hB,
    ← LinearMap.comp_assoc _ (𝒜.leftUnaryDifferential dB) (𝒜.leftUnaryDifferential dB),
    𝒜.leftUnaryDifferential_comp_self (LinearMap.ext hB.sq_zero), LinearMap.zero_comp,
    LinearMap.comp_zero]

end Taylor

section TensorDGAlgebra

variable (𝒜 : AInfinityAlgebra R A) {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B}

/-- **The tensor product of an `A∞` algebra with a DG algebra.**  For an `A∞` algebra `A` and a
differential graded algebra `(B, d_B)`, the module `A ⊗ B`, graded by total degree, carries the
`A∞` structure with
`m₁ (a ⊗ b) = m₁ a ⊗ b + (-1) ^ |a| • (a ⊗ d_B b)` and, for `n ≥ 2`,
`mₙ (a₀ ⊗ b₀, …, aₙ₋₁ ⊗ bₙ₋₁) = (-1) ^ (∑_{i < j} |bᵢ| |aⱼ|) • (mₙ (a₀, …, aₙ₋₁) ⊗ b₀ ⋯ bₙ₋₁)`
(`tensorDGAlgebra_m_one_apply` and `tensorDGAlgebra_m_apply`). -/
noncomputable def tensorDGAlgebra (hB : IsDGAlgebra ℬ dB) : AInfinityAlgebra R (A ⊗[R] B) :=
  -- The suspension `s (a ⊗ b) = s a ⊗ b` lets `d_B` cross `s a` rather than `a`, which costs a
  -- sign; the bar construction is therefore assembled from `-d_B`, so that `m₁` carries the
  -- Koszul sign `(-1) ^ |a|` of `1 ⊗ d_B`.
  ofTaylor (𝒜.grading.tensorProduct (InternalGrading.ofDecomposition ℬ))
    (tensorTaylor 𝒜 ℬ (-dB)) (isHomogeneous_tensorTaylor 𝒜 ℬ (-dB) (hB.neg))
    (gradedCoderiv_tensorTaylor_comp_self 𝒜 ℬ (-dB) (hB.neg))

/-- The tensor product is graded by total degree. -/
@[simp]
theorem tensorDGAlgebra_grading (hB : IsDGAlgebra ℬ dB) :
    (𝒜.tensorDGAlgebra hB).grading =
      𝒜.grading.tensorProduct (InternalGrading.ofDecomposition ℬ) := by
  rw [tensorDGAlgebra, ofTaylor_grading]

/-- The suspended Taylor map of the tensor product on a word of length at least two of pure
tensors of homogeneous elements: the shuffle sign of the suspended degrees times the Taylor map of
`A` on the word of the `aⱼ`, tensored with the product of the `bⱼ`. -/
theorem tensorDGAlgebra_taylor_of_tprod (hB : IsDGAlgebra ℬ dB) {n : ℕ} (hn : 2 ≤ n)
    (a : ℕ → A) (b : ℕ → B) (dA dB' : ℕ → ℤ)
    (ha : ∀ i < n, a i ∈ (𝒜.grading.shift 1).piece (dA i)) (hb : ∀ i < n, b i ∈ ℬ (dB' i)) :
    (𝒜.tensorDGAlgebra hB).taylor (ReducedTensorWords.of R (A ⊗[R] B) ⟨n, by omega⟩
        (PiTensorProduct.tprod R fun j : Fin n ↦ a j ⊗ₜ b j)) =
      negOnePowCast R (AInfinity.shuffleExp n dA dB') •
        (𝒜.taylor (ReducedTensorWords.of R A ⟨n, by omega⟩
            (PiTensorProduct.tprod R fun j : Fin n ↦ a j)) ⊗ₜ
          (List.ofFn fun j : Fin n ↦ b j).prod) := by
  rw [tensorDGAlgebra, ofTaylor_taylor, tensorTaylor_of_tprod 𝒜 ℬ (-dB) _ a b dA dB' ha hb,
    ReducedTensorWords.letter_of_tprod R A, ite_eq_right (by omega), TensorProduct.zero_tmul,
    smul_zero, add_zero]

/-- The unary operation of the tensor product on a pure tensor with homogeneous second factor. -/
private theorem tensorDGAlgebra_m_one_apply_of_mem (hB : IsDGAlgebra ℬ dB) {p q : ℤ} {a : A}
    {b : B} (ha : a ∈ 𝒜.grading.piece p) (hb : b ∈ ℬ q) :
    (𝒜.tensorDGAlgebra hB).m 1 ![a ⊗ₜ b] =
      𝒜.m 1 ![a] ⊗ₜ b + negOnePowCast R p • (a ⊗ₜ dB b) := by
  have ha' : ∀ i < 1, (fun _ ↦ a) i ∈ (𝒜.grading.shift 1).piece ((fun _ ↦ p - 1) i) :=
    fun _ _ ↦ by rwa [InternalGrading.shift_piece, sub_add_cancel]
  have h := tensorTaylor_of_tprod 𝒜 ℬ (-dB) Nat.one_pos (fun _ ↦ a) (fun _ ↦ b) (fun _ ↦ p - 1)
    (fun _ ↦ q) ha' fun _ _ ↦ hb
  rw [← taylor_ofLetter, tensorDGAlgebra, ofTaylor_taylor, ReducedTensorWords.ofLetter_eq_of_tprod]
  refine h.trans ?_
  have hl : ReducedTensorWords.of R A ⟨1, Nat.one_pos⟩ (PiTensorProduct.tprod R fun _ ↦ a) =
      ReducedTensorWords.ofLetter R A a :=
    (ReducedTensorWords.ofLetter_eq_of_tprod R A a).symm
  rw [hl, ReducedTensorWords.letter_ofLetter,
    AInfinity.shuffleExp_one, negOnePowCast_zero, one_smul, taylor_ofLetter, Finset.sum_range_one]
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    LinearMap.neg_apply, TensorProduct.tmul_neg, smul_neg, negOnePowCast_eq_intCast,
    Int.negOnePow_sub, Int.negOnePow_one, mul_neg, mul_one, Units.val_neg, Int.cast_neg, neg_smul,
    neg_neg]

/-- **The unary operation of the tensor product** is the tensor product differential
`m₁ ⊗ 1 + 1 ⊗ d_B`, with the Koszul sign of `d_B` crossing `a`. -/
theorem tensorDGAlgebra_m_one_apply (hB : IsDGAlgebra ℬ dB) {p : ℤ} {a : A}
    (ha : a ∈ 𝒜.grading.piece p) (b : B) :
    (𝒜.tensorDGAlgebra hB).m 1 ![a ⊗ₜ b] =
      𝒜.m 1 ![a] ⊗ₜ b + negOnePowCast R p • (a ⊗ₜ dB b) := by
  rw [← differential_apply (𝒜.tensorDGAlgebra hB), ← differential_apply 𝒜]
  induction b using DirectSum.Decomposition.inductionOn ℬ with
  | zero => simp only [TensorProduct.tmul_zero, map_zero, smul_zero, add_zero]
  | homogeneous b =>
    rw [differential_apply, differential_apply]
    exact tensorDGAlgebra_m_one_apply_of_mem 𝒜 hB ha b.property
  | add b b' hb hb' =>
    simp only [TensorProduct.tmul_add, map_add, smul_add] at hb hb' ⊢
    rw [hb, hb']
    abel

/-- **The operations of the tensor product other than the unary one**: on pure tensors of
homogeneous elements, `mₙ (a₀ ⊗ b₀, …, aₙ₋₁ ⊗ bₙ₋₁)` is `mₙ (a₀, …, aₙ₋₁) ⊗ b₀ ⋯ bₙ₋₁` with the
Koszul sign `(-1) ^ (∑_{i < j} |bᵢ| |aⱼ|)` of moving every `bᵢ` past every later `aⱼ`. -/
theorem tensorDGAlgebra_m_apply (hB : IsDGAlgebra ℬ dB) {n : ℕ} (hn : n ≠ 1) (a : ℕ → A)
    (b : ℕ → B) (p q : ℕ → ℤ) (ha : ∀ i < n, a i ∈ 𝒜.grading.piece (p i))
    (hb : ∀ i < n, b i ∈ ℬ (q i)) :
    (𝒜.tensorDGAlgebra hB).m n (fun i : Fin n ↦ a i ⊗ₜ b i) =
      negOnePowCast R (AInfinity.shuffleExp n p q) •
        (𝒜.m n (fun i : Fin n ↦ a i) ⊗ₜ (List.ofFn fun i : Fin n ↦ b i).prod) := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [m_zero, m_zero, _root_.zero_apply, _root_.zero_apply,
      TensorProduct.zero_tmul, smul_zero]
  have h2 : 2 ≤ n := by omega
  have hmem : ∀ i : Fin n, a i ⊗ₜ b i ∈
      (𝒜.grading.tensorProduct (InternalGrading.ofDecomposition ℬ)).piece (p i + q i) :=
    fun i ↦ InternalGrading.tmul_mem_tensorProduct _ _ (ha i i.isLt)
      (by rw [InternalGrading.ofDecomposition_piece]; exact hb i i.isLt)
  have h := (𝒜.tensorDGAlgebra hB).taylor_of_tprod ⟨n, by omega⟩ fun i : Fin n ↦
    (𝒜.grading.tensorProduct (InternalGrading.ofDecomposition ℬ)).koszulTwist
      ((n : ℤ) - 1 - i) (a i ⊗ₜ b i)
  simp only [tensorDGAlgebra_grading, InternalGrading.koszulTwist_koszulTwist] at h
  rw [← h]
  simp only [InternalGrading.koszulTwist_apply_of_mem _ (hmem _), ← negOnePowCast_eq_intCast,
    (PiTensorProduct.tprod R).map_smul_univ, map_smul,
    tensorDGAlgebra_taylor_of_tprod 𝒜 hB h2 a b (fun i ↦ p i - 1) q
      (fun i hi ↦ by rw [InternalGrading.shift_piece, sub_add_cancel]; exact ha i hi) hb,
    𝒜.taylor_of_tprod, InternalGrading.koszulTwist_apply_of_mem _ (ha _ (Fin.isLt _)),
    MultilinearMap.map_smul_univ, ← TensorProduct.smul_tmul', smul_smul]
  congr 1
  simp only [RingHom.id_apply]
  rw [← negOnePowCast_sum, ← negOnePowCast_sum, ← negOnePowCast_add, ← negOnePowCast_add]
  refine negOnePowCast_eq_of_even_sub ⟨∑ i ∈ Finset.range n, ((n : ℤ) - 1 - i) * p i, ?_⟩
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ ((n : ℤ) - 1 - i) * (p i + q i)),
    Fin.sum_univ_eq_sum_range (fun i ↦ ((n : ℤ) - 1 - i) * p i), AInfinity.shuffleExp_sub_one]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

end TensorDGAlgebra

end AInfinityAlgebra

end TauCeti

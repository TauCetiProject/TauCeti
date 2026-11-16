/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Additive.Equivalence
public import TauCeti.InformationTheory.Coding.Binary.Basic

/-!
# Support rigidity for coordinate permutation automorphisms of binary codes

Over `ZMod 2`, two distinct codewords in an additive code `C` of minimum nonzero Hamming weight at
least `d` cannot both be nonzero on a finite coordinate set `s` when the sum of their weights is
strictly less than `d + 2 * s.card` (`TauCeti.eq_of_mem_of_hammingNorm_add_lt`). Applying this to a
codeword `x ∈ C` and its image `x ∘ σ.symm` under a coordinate permutation automorphism
`σ ∈ TauCeti.AdditiveCode.permutationAut C` shows that whenever `σ` fixes all points of `s` inside
the support of `x` and `2 * hammingNorm x < d + 2 * s.card`, the automorphism fixes `x` as a
codeword and preserves the value of `x` along every `σ`-orbit.

In particular, for any binary code of minimum nonzero weight at least eight (such as an extended
binary Golay code), fixing five nonzero coordinates of an octad forces a coordinate permutation
automorphism to preserve that octad.

## Main declarations

* `TauCeti.AdditiveCode.comp_symm_eq_of_mem_permutationAut_of_two_mul_hammingNorm_lt`: a coordinate
  permutation automorphism fixing enough nonzero coordinates of a binary codeword fixes that
  codeword.
* `TauCeti.AdditiveCode.apply_perm_eq_of_mem_permutationAut_of_two_mul_hammingNorm_lt`: under the
  same hypothesis, the codeword is constant on every orbit of the permutation.

## References

* W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University Press,
  2003, §1.6 and Chapter 9.
-/

public section

namespace TauCeti.AdditiveCode

variable {ι : Type*} [Fintype ι]

/-- In a binary additive code whose nonzero codewords have Hamming weight at least `d`, a
coordinate permutation automorphism fixing all points of `s` inside the support of a codeword `x`
fixes `x` whenever `2 * hammingNorm x < d + 2 * s.card`. -/
theorem comp_symm_eq_of_mem_permutationAut_of_two_mul_hammingNorm_lt
    {C : AddSubgroup (ι → ZMod 2)} {d : ℕ} (hd : ∀ z ∈ C, z ≠ 0 → d ≤ hammingNorm z)
    {σ : Equiv.Perm ι} (hσ : σ ∈ permutationAut C) {x : ι → ZMod 2} (hx : x ∈ C)
    {s : Finset ι} (hs : ∀ i ∈ s, x i ≠ 0 ∧ σ i = i)
    (hcard : 2 * hammingNorm x < d + 2 * s.card) : x ∘ σ.symm = x :=
  eq_of_mem_of_hammingNorm_add_lt hd (comp_symm_mem_of_mem_permutationAut hσ hx) hx
    (fun i hi ↦ by
      have hsymm : σ.symm i = i := σ.symm_apply_eq.mpr (hs i hi).2.symm
      exact ⟨by simpa [Function.comp_apply, hsymm] using (hs i hi).1, (hs i hi).1⟩)
    (by
      rw [Equiv.hammingNorm_comp]
      omega)

/-- In a binary additive code whose nonzero codewords have Hamming weight at least `d`, if a
coordinate permutation automorphism `σ` fixes all points of `s` inside the support of a codeword
`x` and `2 * hammingNorm x < d + 2 * s.card`, then `x` is constant on every `σ`-orbit. -/
theorem apply_perm_eq_of_mem_permutationAut_of_two_mul_hammingNorm_lt
    {C : AddSubgroup (ι → ZMod 2)} {d : ℕ} (hd : ∀ z ∈ C, z ≠ 0 → d ≤ hammingNorm z)
    {σ : Equiv.Perm ι} (hσ : σ ∈ permutationAut C) {x : ι → ZMod 2} (hx : x ∈ C)
    {s : Finset ι} (hs : ∀ i ∈ s, x i ≠ 0 ∧ σ i = i)
    (hcard : 2 * hammingNorm x < d + 2 * s.card) (i : ι) : x (σ i) = x i := by
  have h := congrFun
    (comp_symm_eq_of_mem_permutationAut_of_two_mul_hammingNorm_lt hd hσ hx hs hcard) (σ i)
  simpa using h.symm

end TauCeti.AdditiveCode

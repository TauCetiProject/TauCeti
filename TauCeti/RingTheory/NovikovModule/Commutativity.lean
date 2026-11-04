/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Tensor

/-!
# Graded commutativity homotopies of supported kernel products

Let `⋆` and `⋆'` be products of completed combinations given by supported product kernels
(`TauCeti.NovikovModule.kernelProduct`): `a ⋆ b` with a kernel `n(p₁, p₂, p₀)` on
`S₁ × S₂`, and `b ⋆' a` with a kernel `n'(p₂, p₁, p₀)` on `S₂ × S₁`, so that the inputs of the
second product are exchanged. Given degree functions `d₁` and `d₂` on the input generators, the
graded commutator `a ⋆ b - (-1)^(i j) b ⋆' a` of homogeneous `a` and `b` of degrees `i` and `j`
is a kernel map out of the completed tensor product. Its kernel is
`n(p₁, p₂, ·) - (-1)^(d₁ p₁ d₂ p₂) n'(p₂, p₁, ·)`: on the tensor product `a ⊗ b`, the kernel
map of the Koszul-signed exchanged kernel `(-1)^(d₁ p₁ d₂ p₂) n'(p₂, p₁, ·)` is
`(-1)^(i j) b ⋆' a` (`NovikovModule.kernelMap_tensor_eq_negOnePow_smul_kernelProduct`).

For the pair-of-pants product in Floer theory, `n'` counts the pairs of pants whose two input
ends are exchanged, and a one-parameter family of domains rotating one labelling of the inputs
into the other has as its boundary the two products, with the orientation sign `(-1)^(i j)`
of the exchange, and the breakings of a Floer cylinder at one of the three ends. Counting the
boundary of its one-dimensional moduli spaces gives the kernel identity

`n(p₁, p₂, p₀) - (-1)^(d₁ p₁ d₂ p₂) n'(p₂, p₁, p₀) = (k δ₀ + D k)((p₁, p₂), p₀)`

for the kernel `k` counting rigid elements of the family, the output differential `δ₀` and the
differential `D` of the tensor product. This file turns that identity into the chain homotopy

`a ⋆ b - (-1)^(i j) b ⋆' a = δ₀ (K (a ⊗ b)) + K (D (a ⊗ b))`

for the kernel map `K` of `k`, for arbitrary homogeneous completed combinations
(`NovikovModule.kernelProduct_sub_negOnePow_smul_kernelProduct`). When `D` is the Koszul tensor
differential `δ₁ ⊗ 1 + (-1)^(d₁) ⊗ δ₂`, the second term is
`K (δ₁ a ⊗ b) + (-1)^i K (a ⊗ δ₂ b)`
(`NovikovModule.kernelProduct_sub_negOnePow_smul_kernelProduct_of_tensorDifferential`), so for
cycles `a` and `b` the graded commutator is the coboundary `δ₀ (K (a ⊗ b))`
(`NovikovModule.kernelProduct_sub_negOnePow_smul_kernelProduct_of_kernelMap_eq_zero`). Hence,
once both products satisfy the Leibniz rule, the products they induce on homology agree up to
the sign `(-1)^(i j)` of the exchange. The kernel identity and the potential bounds
of the kernels remain hypotheses here: they are the geometric input from the compactified moduli
spaces.

## Main results

* `NovikovModule.kernelMap_tensor_eq_negOnePow_smul_kernelProduct`: the exchanged product as a
  kernel map out of the tensor product, with the Koszul sign.
* `NovikovModule.kernelProduct_sub_negOnePow_smul_kernelProduct`: a kernel homotopy for the
  graded commutator gives a homotopy between the product and the exchanged product.
* `NovikovModule.kernelProduct_sub_negOnePow_smul_kernelProduct_of_tensorDifferential`: the same
  homotopy with the tensor differential expanded by the Leibniz rule.
* `NovikovModule.kernelProduct_sub_negOnePow_smul_kernelProduct_of_kernelMap_eq_zero`: on cycles
  the graded commutator is a coboundary.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the graded commutativity of the pair-of-pants product.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
-/

public section

noncomputable section

namespace TauCeti

namespace NovikovModule

variable {R S₁ S₂ S₀ : Type*} [CommRing R] {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ} {F₀ : S₀ → ℝ}
  {d₁ : S₁ → ℤ} {d₂ : S₂ → ℤ} {C₁ C₂ : ℝ}
  {n : S₁ → S₂ → S₀ → R} {n' : S₂ → S₁ → S₀ → R}
  (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C₁)
  (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)
  (hn' : ∀ p₂ p₁ p₀, n' p₂ p₁ p₀ ≠ 0 → F₀ p₀ ≤ F₂ p₂ + F₁ p₁ + C₂)
  (hfin' : ∀ p₂ p₁, n' p₂ p₁ ∈ NovikovModule R F₀)
  {i j : ℤ} {a : NovikovModule R F₁} {b : NovikovModule R F₂}

/-- **The exchanged product with the Koszul sign.** For a product kernel `n'` on `S₂ × S₁`, the
kernel map of the Koszul-signed exchanged kernel `(-1)^(d₁ p₁ d₂ p₂) n'(p₂, p₁, ·)` on `S₁ × S₂`
sends the tensor product of `a` of degree `i` and `b` of degree `j` to `(-1)^(i j) b ⋆' a`. The
potential bound of the exchanged kernel may have any constant. -/
theorem kernelMap_tensor_eq_negOnePow_smul_kernelProduct {C : ℝ}
    (hN : ∀ (q : S₁ × S₂) p₀, ((d₁ q.1 * d₂ q.2).negOnePow : R) * n' q.2 q.1 p₀ ≠ 0 →
      F₀ p₀ ≤ F₁ q.1 + F₂ q.2 + C)
    (hNfin : ∀ q : S₁ × S₂,
      (fun p₀ => ((d₁ q.1 * d₂ q.2).negOnePow : R) * n' q.2 q.1 p₀) ∈ NovikovModule R F₀)
    (ha : a ∈ gradeBy R F₁ d₁ i) (hb : b ∈ gradeBy R F₂ d₂ j) :
    kernelMap hN hNfin (tensor a b) = ((i * j).negOnePow : R) • kernelProduct hn' hfin' b a := by
  ext p₀
  rw [kernelMap_apply_val, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
    kernelProduct_apply_val, mul_finsum' _ _ (finite_support_mul_kernel hn' b a p₀),
    ← finsum_comp_equiv (Equiv.prodComm S₁ S₂)]
  refine finsum_congr fun q => ?_
  simp only [tensor_apply_val, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  -- Only pairs of support generators contribute, and their degrees are `i` and `j`.
  by_cases h₁ : a.val q.1 = 0
  · simp [h₁]
  by_cases h₂ : b.val q.2 = 0
  · simp [h₂]
  rw [mem_gradeBy_iff.1 ha q.1 h₁, mem_gradeBy_iff.1 hb q.2 h₂]
  ring

variable {Ck C₀ : ℝ} {k : S₁ × S₂ → S₀ → R} {δ₀ : S₀ → S₀ → R}
  (hk : ∀ (q : S₁ × S₂) p₀, k q p₀ ≠ 0 → F₀ p₀ ≤ F₁ q.1 + F₂ q.2 + Ck)
  (hkfin : ∀ q, k q ∈ NovikovModule R F₀)
  (hδ₀ : ∀ p p₀, δ₀ p p₀ ≠ 0 → F₀ p₀ ≤ F₀ p + C₀) (hδ₀fin : ∀ p, δ₀ p ∈ NovikovModule R F₀)

include hn hfin in
/-- **Graded commutativity up to homotopy.** Let `n` and `n'` be the product kernels of `a ⋆ b`
and of the exchanged product `b ⋆' a`, let `δ₀` be a kernel on the output generators, and let `D`
be a kernel on the tensor product. If a kernel `k` from the tensor product to the output is a
kernel homotopy,

`n(p₁, p₂, p₀) - (-1)^(d₁ p₁ d₂ p₂) n'(p₂, p₁, p₀) = (k δ₀ + D k)((p₁, p₂), p₀)`,

then its kernel map `K` is a homotopy between the two products: for `a` of degree `i` and `b` of
degree `j`, `a ⋆ b - (-1)^(i j) b ⋆' a = δ₀ (K (a ⊗ b)) + K (D (a ⊗ b))`. -/
theorem kernelProduct_sub_negOnePow_smul_kernelProduct
    {D : S₁ × S₂ → S₁ × S₂ → R} {CD : ℝ}
    (hD : ∀ q q', D q q' ≠ 0 → F₁ q'.1 + F₂ q'.2 ≤ F₁ q.1 + F₂ q.2 + CD)
    (hDfin : ∀ q, D q ∈ NovikovModule R fun q' : S₁ × S₂ => F₁ q'.1 + F₂ q'.2)
    (hcomm : ∀ (q : S₁ × S₂) p₀,
      n q.1 q.2 p₀ - ((d₁ q.1 * d₂ q.2).negOnePow : R) * n' q.2 q.1 p₀ =
        kernelComp k δ₀ q p₀ + kernelComp D k q p₀)
    (ha : a ∈ gradeBy R F₁ d₁ i) (hb : b ∈ gradeBy R F₂ d₂ j) :
    kernelProduct hn hfin a b - ((i * j).negOnePow : R) • kernelProduct hn' hfin' b a =
      kernelMap hδ₀ hδ₀fin (kernelMap hk hkfin (tensor a b)) +
        kernelMap hk hkfin (kernelMap hD hDfin (tensor a b)) := by
  -- Potential bounds and completed outputs of the product kernel and of the exchanged kernel,
  -- read as one-input kernels on the tensor product.
  have hN (q : S₁ × S₂) (p₀ : S₀) (h : n q.1 q.2 p₀ ≠ 0) : F₀ p₀ ≤ F₁ q.1 + F₂ q.2 + C₁ :=
    hn q.1 q.2 p₀ h
  have hN' (q : S₁ × S₂) (p₀ : S₀) (h : ((d₁ q.1 * d₂ q.2).negOnePow : R) * n' q.2 q.1 p₀ ≠ 0) :
      F₀ p₀ ≤ F₁ q.1 + F₂ q.2 + C₂ := by
    linarith [hn' q.2 q.1 p₀ (right_ne_zero_of_mul h)]
  have hN'fin (q : S₁ × S₂) :
      (fun p₀ => ((d₁ q.1 * d₂ q.2).negOnePow : R) * n' q.2 q.1 p₀) ∈ NovikovModule R F₀ :=
    Submodule.smul_mem _ _ (hfin' q.2 q.1)
  rw [kernelProduct_eq_kernelMap_tensor hn hfin hN (fun q => hfin q.1 q.2),
    ← kernelMap_tensor_eq_negOnePow_smul_kernelProduct hn' hfin' hN' hN'fin ha hb]
  exact kernelMap_sub_kernelMap hN _ hN' hN'fin hk hkfin hD hDfin hδ₀ hδ₀fin hcomm _

variable [DecidableEq S₁] [DecidableEq S₂] {δ₁ : S₁ → S₁ → R} {δ₂ : S₂ → S₂ → R} {E₁ E₂ : ℝ}
  (hδ₁ : ∀ p q, δ₁ p q ≠ 0 → F₁ q ≤ F₁ p + E₁) (hδ₁fin : ∀ p, δ₁ p ∈ NovikovModule R F₁)
  (hδ₂ : ∀ p q, δ₂ p q ≠ 0 → F₂ q ≤ F₂ p + E₂) (hδ₂fin : ∀ p, δ₂ p ∈ NovikovModule R F₂)

include hn hfin in
/-- **Graded commutativity up to homotopy, with the Koszul signs.** Let `δ₁`, `δ₂` be kernels on
the input generators and let `D = δ₁ ⊗ 1 + (-1)^(d₁) ⊗ δ₂` be the tensor differential. If a
kernel `k` is a kernel homotopy,

`n(p₁, p₂, p₀) - (-1)^(d₁ p₁ d₂ p₂) n'(p₂, p₁, p₀) = (k δ₀ + D k)((p₁, p₂), p₀)`,

then for `a` of degree `i` and `b` of degree `j` its kernel map `K` satisfies

`a ⋆ b - (-1)^(i j) b ⋆' a = δ₀ (K (a ⊗ b)) + K (δ₁ a ⊗ b) + (-1)^i K (a ⊗ δ₂ b)`. -/
theorem kernelProduct_sub_negOnePow_smul_kernelProduct_of_tensorDifferential
    (hcomm : ∀ (q : S₁ × S₂) p₀,
      n q.1 q.2 p₀ - ((d₁ q.1 * d₂ q.2).negOnePow : R) * n' q.2 q.1 p₀ =
        kernelComp k δ₀ q p₀ + kernelComp (tensorDifferential d₁ δ₁ δ₂) k q p₀)
    (ha : a ∈ gradeBy R F₁ d₁ i) (hb : b ∈ gradeBy R F₂ d₂ j) :
    kernelProduct hn hfin a b - ((i * j).negOnePow : R) • kernelProduct hn' hfin' b a =
      kernelMap hδ₀ hδ₀fin (kernelMap hk hkfin (tensor a b)) +
        kernelMap hk hkfin (tensor (kernelMap hδ₁ hδ₁fin a) b) +
        (i.negOnePow : R) • kernelMap hk hkfin (tensor a (kernelMap hδ₂ hδ₂fin b)) := by
  have hD (p q : S₁ × S₂) (h : tensorDifferential d₁ δ₁ δ₂ p q ≠ 0) :=
    potential_le_of_tensorDifferential_ne_zero hδ₁ hδ₂ h
  have hDfin := tensorDifferential_mem (d₁ := d₁) hδ₁fin hδ₂fin
  rw [kernelProduct_sub_negOnePow_smul_kernelProduct hn hfin hn' hfin' hk hkfin hδ₀ hδ₀fin hD
      hDfin hcomm ha hb,
    kernelMap_tensorDifferential_tensor hδ₁ hδ₁fin hδ₂ hδ₂fin hD hDfin ha]
  simp only [map_add, map_smul, add_assoc]

include hn hfin in
/-- **Graded commutativity on cycles.** Under the kernel homotopy of
`kernelProduct_sub_negOnePow_smul_kernelProduct_of_tensorDifferential`, if `δ₁ a = 0` and
`δ₂ b = 0`, then the graded commutator `a ⋆ b - (-1)^(i j) b ⋆' a` is the coboundary
`δ₀ (K (a ⊗ b))`. -/
theorem kernelProduct_sub_negOnePow_smul_kernelProduct_of_kernelMap_eq_zero
    (hcomm : ∀ (q : S₁ × S₂) p₀,
      n q.1 q.2 p₀ - ((d₁ q.1 * d₂ q.2).negOnePow : R) * n' q.2 q.1 p₀ =
        kernelComp k δ₀ q p₀ + kernelComp (tensorDifferential d₁ δ₁ δ₂) k q p₀)
    (ha : a ∈ gradeBy R F₁ d₁ i) (hb : b ∈ gradeBy R F₂ d₂ j)
    (hδa : kernelMap hδ₁ hδ₁fin a = 0) (hδb : kernelMap hδ₂ hδ₂fin b = 0) :
    kernelProduct hn hfin a b - ((i * j).negOnePow : R) • kernelProduct hn' hfin' b a =
      kernelMap hδ₀ hδ₀fin (kernelMap hk hkfin (tensor a b)) := by
  rw [kernelProduct_sub_negOnePow_smul_kernelProduct_of_tensorDifferential hn hfin hn' hfin' hk
      hkfin hδ₀ hδ₀fin hδ₁ hδ₁fin hδ₂ hδ₂fin hcomm ha hb, hδa, hδb]
  simp

end NovikovModule

end TauCeti

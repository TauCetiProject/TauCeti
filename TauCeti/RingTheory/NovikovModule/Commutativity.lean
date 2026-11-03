/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Tensor

/-!
# Graded commutativity homotopies of supported kernel products

Let `⋆` denote the product of completed combinations given by a supported product kernel
`n(p₁, p₂, p₀)` (`TauCeti.NovikovModule.kernelProduct`), and let `⋆'` be a product in the
opposite order, with a kernel `n'(p₂, p₁, p₀)` taking its inputs from `S₂` first and from `S₁`
second. Let `d₁` and `d₂` be degree functions on the input generators. Graded commutativity
compares `a ⋆ b` with `(-1)^(i j) b ⋆' a` for `a` of degree `i` and `b` of degree `j`.

Both are kernel maps out of the completed tensor product `a ⊗ b`. The exchanged product
`b ⋆' a` is the kernel map of `n'(q.2, q.1, ·)`
(`NovikovModule.kernelProduct_eq_kernelMap_tensor_swap`), and the Koszul sign can be moved
into the kernel, generator by generator: `(-1)^(i j) b ⋆' a` is the kernel map of
`(-1)^(d₁ p₁ d₂ p₂) n'(p₂, p₁, ·)`
(`NovikovModule.negOnePow_smul_kernelProduct_eq_kernelMap_tensor`). The sign depends on the
bidegree of the pair of generators, not on its total degree, so it is not a scalar on
homogeneous elements of the tensor product; homogeneity of both factors is what makes it one.

For the pair-of-pants product in Floer theory, `n'` counts the pairs of pants with their two
input ends exchanged, and a one-parameter family of pairs of pants rotating one input end around
the other connects the two configurations. The other codimension-one boundary points of its
one-dimensional moduli spaces are breakings of a Floer cylinder at one of the three ends, so the
count of all boundary points gives the kernel identity

`n(p₁, p₂, p₀) - (-1)^(d₁ p₁ d₂ p₂) n'(p₂, p₁, p₀) = (k δ₀ + D k)((p₁, p₂), p₀)`

for the kernel `k` counting rigid elements of the family, the output differential `δ₀` and the
differential `D` of the tensor product. This file turns that identity into the chain homotopy

`a ⋆ b - (-1)^(i j) b ⋆' a = δ₀ (K (a ⊗ b)) + K (D (a ⊗ b))`

between the two products, for the kernel map `K` of `k` and arbitrary homogeneous completed
combinations `a`, `b`
(`NovikovModule.kernelProduct_sub_negOnePow_smul_kernelProduct`). When `D` is the Koszul tensor
differential `δ₁ ⊗ 1 + (-1)^(d₁) ⊗ δ₂`, the second term expands to
`K (δ₁ a ⊗ b) + (-1)^i K (a ⊗ δ₂ b)`
(`NovikovModule.kernelProduct_sub_negOnePow_smul_kernelProduct_of_tensorDifferential`). In
particular, if `δ₁ a` and `δ₂ b` vanish, then `a ⋆ b` and `(-1)^(i j) b ⋆' a` differ by the
coboundary `δ₀ (K (a ⊗ b))`
(`NovikovModule.kernelProduct_sub_negOnePow_smul_kernelProduct_of_kernelMap_eq_zero`). The kernel
identity itself, and the potential bounds of the kernels, which come from the energy estimate,
remain hypotheses here: they are the geometric input from the compactified moduli spaces.

## Main results

* `NovikovModule.negOnePow_smul_kernelProduct_eq_kernelMap_tensor`: a product with exchanged
  inputs and the Koszul sign of the exchange is a kernel map out of the tensor product, for
  homogeneous inputs.
* `NovikovModule.kernelProduct_sub_negOnePow_smul_kernelProduct`: a kernel homotopy between a
  product kernel and the signed exchanged kernel gives a chain homotopy between the products.
* `NovikovModule.kernelProduct_sub_negOnePow_smul_kernelProduct_of_tensorDifferential`: the same
  homotopy for the Koszul differential of the tensor product, with its signs.
* `NovikovModule.kernelProduct_sub_negOnePow_smul_kernelProduct_of_kernelMap_eq_zero`: on cycles,
  the two products differ by a coboundary.

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

variable {R S₁ S₂ S₀ : Type*} {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ} {F₀ : S₀ → ℝ}

section CommRing

variable [CommRing R] {C₁ C₂ Ck C₀ : ℝ} {n : S₁ → S₂ → S₀ → R} {n' : S₂ → S₁ → S₀ → R}
  {k : S₁ × S₂ → S₀ → R} {δ₀ : S₀ → S₀ → R} {d₁ : S₁ → ℤ} {d₂ : S₂ → ℤ}
  (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C₁)
  (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)
  (hn' : ∀ p₂ p₁ p₀, n' p₂ p₁ p₀ ≠ 0 → F₀ p₀ ≤ F₂ p₂ + F₁ p₁ + C₂)
  (hfin' : ∀ p₂ p₁, n' p₂ p₁ ∈ NovikovModule R F₀)
  (hk : ∀ (q : S₁ × S₂) p₀, k q p₀ ≠ 0 → F₀ p₀ ≤ F₁ q.1 + F₂ q.2 + Ck)
  (hkfin : ∀ q, k q ∈ NovikovModule R F₀)
  (hδ₀ : ∀ p p₀, δ₀ p p₀ ≠ 0 → F₀ p₀ ≤ F₀ p + C₀) (hδ₀fin : ∀ p, δ₀ p ∈ NovikovModule R F₀)

/-- **The Koszul sign of the exchange.** For a product kernel `n'` from `S₂ × S₁`, degree
functions `d₁`, `d₂`, and `a` of degree `i` and `b` of degree `j`, the signed product
`(-1)^(i j) b ⋆' a` is the kernel map, out of the tensor product `a ⊗ b`, of the kernel
`(-1)^(d₁ q.1 d₂ q.2) n'(q.2, q.1, ·)`. -/
theorem negOnePow_smul_kernelProduct_eq_kernelMap_tensor {C' : ℝ}
    (hm : ∀ (q : S₁ × S₂) p₀, ((d₁ q.1 * d₂ q.2).negOnePow : R) * n' q.2 q.1 p₀ ≠ 0 →
      F₀ p₀ ≤ F₁ q.1 + F₂ q.2 + C')
    (hmfin : ∀ q : S₁ × S₂,
      (fun p₀ => ((d₁ q.1 * d₂ q.2).negOnePow : R) * n' q.2 q.1 p₀) ∈ NovikovModule R F₀)
    {i j : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ d₁ i)
    {b : NovikovModule R F₂} (hb : b ∈ gradeBy R F₂ d₂ j) :
    ((i * j).negOnePow : R) • kernelProduct hn' hfin' b a = kernelMap hm hmfin (tensor a b) := by
  have hs (q : S₁ × S₂) (p₀ : S₀) (h : n' q.2 q.1 p₀ ≠ 0) :
      F₀ p₀ ≤ F₁ q.1 + F₂ q.2 + C₂ := by
    linarith [hn' q.2 q.1 p₀ h]
  rw [kernelProduct_eq_kernelMap_tensor_swap hn' hfin' hs fun q => hfin' q.2 q.1]
  ext p₀
  rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, kernelMap_apply_val, kernelMap_apply_val,
    mul_finsum' _ _ (finite_support_mul_kernelMap hs _ p₀)]
  refine finsum_congr fun q => ?_
  -- Off the support of `a ⊗ b` both terms vanish; on it, the generator signs are `(-1)^(i j)`.
  rw [tensor_apply_val]
  by_cases h₁ : a.val q.1 = 0
  · simp [h₁]
  by_cases h₂ : b.val q.2 = 0
  · simp [h₂]
  rw [mem_gradeBy_iff.1 ha q.1 h₁, mem_gradeBy_iff.1 hb q.2 h₂]
  ring

/-- **Graded commutativity up to homotopy.** Let `n` and `n'` be the product kernels of `a ⋆ b`
and of the exchanged product `b ⋆' a`, let `d₁`, `d₂` be degree functions on the input
generators, let `δ₀` be a kernel on the output generators, and let `D` be a kernel on the tensor
product. If a kernel `k` from the tensor product to the output is a kernel homotopy,

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
    {i j : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ d₁ i)
    {b : NovikovModule R F₂} (hb : b ∈ gradeBy R F₂ d₂ j) :
    kernelProduct hn hfin a b - ((i * j).negOnePow : R) • kernelProduct hn' hfin' b a =
      kernelMap hδ₀ hδ₀fin (kernelMap hk hkfin (tensor a b)) +
        kernelMap hk hkfin (kernelMap hD hDfin (tensor a b)) := by
  -- Potential bounds and completed outputs of the product kernel and the signed exchanged
  -- kernel, read as kernels on the tensor product.
  have hN (q : S₁ × S₂) (p₀ : S₀) (h : n q.1 q.2 p₀ ≠ 0) : F₀ p₀ ≤ F₁ q.1 + F₂ q.2 + C₁ :=
    hn q.1 q.2 p₀ h
  have hS (q : S₁ × S₂) (p₀ : S₀)
      (h : ((d₁ q.1 * d₂ q.2).negOnePow : R) * n' q.2 q.1 p₀ ≠ 0) :
      F₀ p₀ ≤ F₁ q.1 + F₂ q.2 + C₂ := by
    linarith [hn' q.2 q.1 p₀ (right_ne_zero_of_mul h)]
  have hSfin (q : S₁ × S₂) :
      (fun p₀ => ((d₁ q.1 * d₂ q.2).negOnePow : R) * n' q.2 q.1 p₀) ∈ NovikovModule R F₀ := by
    simpa only [Pi.smul_def, smul_eq_mul] using
      Submodule.smul_mem _ ((d₁ q.1 * d₂ q.2).negOnePow : R) (hfin' q.2 q.1)
  rw [kernelProduct_eq_kernelMap_tensor hn hfin hN (fun q => hfin q.1 q.2),
    negOnePow_smul_kernelProduct_eq_kernelMap_tensor hn' hfin' hS hSfin ha hb]
  exact kernelMap_sub_kernelMap hN _ hS hSfin hk hkfin hD hDfin hδ₀ hδ₀fin hcomm _

/-- **Graded commutativity up to homotopy, with the Koszul signs.** Let `δ₁`, `δ₂` be kernels
on the two input generators and let `D = δ₁ ⊗ 1 + (-1)^(d₁) ⊗ δ₂` be the tensor differential. If
a kernel `k` is a kernel homotopy,

`n(p₁, p₂, p₀) - (-1)^(d₁ p₁ d₂ p₂) n'(p₂, p₁, p₀) = (k δ₀ + D k)((p₁, p₂), p₀)`,

then for `a` of degree `i` and `b` of degree `j` its kernel map `K` satisfies

`a ⋆ b - (-1)^(i j) b ⋆' a = δ₀ (K (a ⊗ b)) + K (δ₁ a ⊗ b) + (-1)^i K (a ⊗ δ₂ b)`. -/
theorem kernelProduct_sub_negOnePow_smul_kernelProduct_of_tensorDifferential
    [DecidableEq S₁] [DecidableEq S₂] {δ₁ : S₁ → S₁ → R} {δ₂ : S₂ → S₂ → R} {E₁ E₂ : ℝ}
    (hδ₁ : ∀ p q, δ₁ p q ≠ 0 → F₁ q ≤ F₁ p + E₁) (hδ₁fin : ∀ p, δ₁ p ∈ NovikovModule R F₁)
    (hδ₂ : ∀ p q, δ₂ p q ≠ 0 → F₂ q ≤ F₂ p + E₂) (hδ₂fin : ∀ p, δ₂ p ∈ NovikovModule R F₂)
    (hcomm : ∀ (q : S₁ × S₂) p₀,
      n q.1 q.2 p₀ - ((d₁ q.1 * d₂ q.2).negOnePow : R) * n' q.2 q.1 p₀ =
        kernelComp k δ₀ q p₀ + kernelComp (tensorDifferential d₁ δ₁ δ₂) k q p₀)
    {i j : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ d₁ i)
    {b : NovikovModule R F₂} (hb : b ∈ gradeBy R F₂ d₂ j) :
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

/-- **Graded commutativity on cycles.** Under the hypotheses of
`NovikovModule.kernelProduct_sub_negOnePow_smul_kernelProduct_of_tensorDifferential`, if
`δ₁ a = 0` and `δ₂ b = 0`, then `a ⋆ b - (-1)^(i j) b ⋆' a = δ₀ (K (a ⊗ b))` is a coboundary. -/
theorem kernelProduct_sub_negOnePow_smul_kernelProduct_of_kernelMap_eq_zero
    [DecidableEq S₁] [DecidableEq S₂] {δ₁ : S₁ → S₁ → R} {δ₂ : S₂ → S₂ → R} {E₁ E₂ : ℝ}
    (hδ₁ : ∀ p q, δ₁ p q ≠ 0 → F₁ q ≤ F₁ p + E₁) (hδ₁fin : ∀ p, δ₁ p ∈ NovikovModule R F₁)
    (hδ₂ : ∀ p q, δ₂ p q ≠ 0 → F₂ q ≤ F₂ p + E₂) (hδ₂fin : ∀ p, δ₂ p ∈ NovikovModule R F₂)
    (hcomm : ∀ (q : S₁ × S₂) p₀,
      n q.1 q.2 p₀ - ((d₁ q.1 * d₂ q.2).negOnePow : R) * n' q.2 q.1 p₀ =
        kernelComp k δ₀ q p₀ + kernelComp (tensorDifferential d₁ δ₁ δ₂) k q p₀)
    {i j : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ d₁ i)
    {b : NovikovModule R F₂} (hb : b ∈ gradeBy R F₂ d₂ j)
    (hδa : kernelMap hδ₁ hδ₁fin a = 0) (hδb : kernelMap hδ₂ hδ₂fin b = 0) :
    kernelProduct hn hfin a b - ((i * j).negOnePow : R) • kernelProduct hn' hfin' b a =
      kernelMap hδ₀ hδ₀fin (kernelMap hk hkfin (tensor a b)) := by
  rw [kernelProduct_sub_negOnePow_smul_kernelProduct_of_tensorDifferential hn hfin hn' hfin' hk
      hkfin hδ₀ hδ₀fin hδ₁ hδ₁fin hδ₂ hδ₂fin hcomm ha hb, hδa, hδb]
  simp

end CommRing

end NovikovModule

end TauCeti

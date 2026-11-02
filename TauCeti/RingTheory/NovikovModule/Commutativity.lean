/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Tensor

/-!
# Graded commutativity homotopies of supported kernel products

Let `⋆` denote products of completed combinations given by supported product kernels
(`TauCeti.NovikovModule.kernelProduct`). A product `a ⋆ b` with kernel `n(p₁, p₂, p₀)` and a
product `b ⋆' a` with the inputs exchanged, with kernel `n'(p₂, p₁, p₀)`, are both kernel maps out
of the completed tensor product `a ⊗ b`: the second has the kernel `n'(p₂, p₁, ·)` at `(p₁, p₂)`
(`NovikovModule.kernelProduct_eq_kernelMap_tensor_swap`).

For the pair-of-pants product in Floer theory the two kernels count the rigid pairs of pants and
the rigid pairs of pants with their two input ends exchanged. A one-parameter family of
thrice-punctured spheres rotating one input puncture to the other gives a kernel `k(q, p₀)`
counting its rigid elements. The ends of its one-dimensional moduli spaces are the two
products, with the Koszul sign `(-1)^(d₁ p₁ d₂ p₂)` of the orientation comparison, and the
breakings of a Floer cylinder at one of the three ends. So the count of all boundary points gives
the kernel identity

`n(p₁, p₂, p₀) - (-1)^(d₁ p₁ d₂ p₂) n'(p₂, p₁, p₀) = (k δ₀ + D k)((p₁, p₂), p₀)`

for the output differential `δ₀` and the differential `D` of the tensor product. This file turns
that identity into the chain homotopy

`a ⋆ b - (-1)^(i j) b ⋆' a = δ₀ (K (a ⊗ b)) + K (D (a ⊗ b))`

for completed combinations `a` of degree `i` and `b` of degree `j`, where `K` is the kernel map
of `k` (of degree `-1` in the Floer setting); both sides are infinite sums
(`NovikovModule.kernelProduct_sub_negOnePow_smul_kernelProduct`). When `D` is the Koszul tensor
differential `δ₁ ⊗ 1 + (-1)^(d₁) ⊗ δ₂`, the second term expands to
`K (δ₁ a ⊗ b) + (-1)^i K (a ⊗ δ₂ b)`
(`NovikovModule.kernelProduct_sub_negOnePow_smul_kernelProduct_of_tensorDifferential`). In
particular, for cocycles `a` and `b` the two products differ by the coboundary
`δ₀ (K (a ⊗ b))`, which is graded commutativity on cohomology
(`NovikovModule.kernelProduct_sub_negOnePow_smul_kernelProduct_of_eq_zero`). The kernel identity
itself and the potential bounds of the kernels, which come from the energy estimate, remain
hypotheses here: they are the geometric input from the compactified moduli spaces.

## Main results

* `NovikovModule.kernelProduct_sub_negOnePow_smul_kernelProduct`: a kernel homotopy between a
  product kernel and the Koszul-signed exchanged kernel gives a chain homotopy between the
  product and the signed exchanged product.
* `NovikovModule.kernelProduct_sub_negOnePow_smul_kernelProduct_of_tensorDifferential`: the same
  homotopy for the Koszul differential of the tensor product, with its signs.
* `NovikovModule.kernelProduct_sub_negOnePow_smul_kernelProduct_of_eq_zero`: on cocycles the
  product and the signed exchanged product differ by a coboundary.

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

variable [CommRing R] {C₁ C₂ Ck C₀ : ℝ}
  {n : S₁ → S₂ → S₀ → R} {n' : S₂ → S₁ → S₀ → R}
  {k : S₁ × S₂ → S₀ → R} {δ₀ : S₀ → S₀ → R} {d₁ : S₁ → ℤ} {d₂ : S₂ → ℤ}
  (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C₁)
  (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)
  (hn' : ∀ p₂ p₁ p₀, n' p₂ p₁ p₀ ≠ 0 → F₀ p₀ ≤ F₂ p₂ + F₁ p₁ + C₂)
  (hfin' : ∀ p₂ p₁, n' p₂ p₁ ∈ NovikovModule R F₀)
  (hk : ∀ (q : S₁ × S₂) p₀, k q p₀ ≠ 0 → F₀ p₀ ≤ F₁ q.1 + F₂ q.2 + Ck)
  (hkfin : ∀ q, k q ∈ NovikovModule R F₀)
  (hδ₀ : ∀ p p₀, δ₀ p p₀ ≠ 0 → F₀ p₀ ≤ F₀ p + C₀) (hδ₀fin : ∀ p, δ₀ p ∈ NovikovModule R F₀)

/-- **Graded commutativity up to homotopy.** Let `n` be the product kernel of `a ⋆ b` and `n'`
that of the product `b ⋆' a` with the inputs exchanged, let `d₁`, `d₂` be degree functions on the
input generators, let `δ₀` be a kernel on the output generators, and let `D` be a kernel on the
tensor product. If a kernel `k` from the tensor product to the output is a kernel homotopy,

`n(p₁, p₂, p₀) - (-1)^(d₁ p₁ d₂ p₂) n'(p₂, p₁, p₀) = (k δ₀ + D k)((p₁, p₂), p₀)`,

then its kernel map `K` is a homotopy between the product and the signed exchanged product: for
`a` of degree `i` and `b` of degree `j`,
`a ⋆ b - (-1)^(i j) b ⋆' a = δ₀ (K (a ⊗ b)) + K (D (a ⊗ b))`. -/
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
  -- Potential bounds of the exchanged kernel and of the two composites with the homotopy kernel.
  have hm (q : S₁ × S₂) (p₀ : S₀) (h : n' q.2 q.1 p₀ ≠ 0) :
      F₀ p₀ ≤ F₁ q.1 + F₂ q.2 + C₂ := by
    linarith [hn' q.2 q.1 p₀ h]
  have hkδ (q : S₁ × S₂) (p₀ : S₀) (h : kernelComp k δ₀ q p₀ ≠ 0) :
      F₀ p₀ ≤ F₁ q.1 + F₂ q.2 + (Ck + C₀) := by
    linarith [potential_le_of_kernelComp_ne_zero (hk q) (hδ₀ · p₀) h]
  have hDk (q : S₁ × S₂) (p₀ : S₀) (h : kernelComp D k q p₀ ≠ 0) :
      F₀ p₀ ≤ F₁ q.1 + F₂ q.2 + (CD + Ck) := by
    linarith [potential_le_of_kernelComp_ne_zero (hD q) (hk · p₀) h]
  rw [kernelProduct_eq_kernelMap_tensor hn hfin (fun q => hn q.1 q.2) (fun q => hfin q.1 q.2),
    kernelProduct_eq_kernelMap_tensor_swap hn' hfin' hm (fun q => hfin' q.2 q.1),
    kernelMap_kernelMap hk hkfin hδ₀ hδ₀fin hkδ fun q => kernelComp_mem hδ₀ hδ₀fin (hkfin q),
    kernelMap_kernelMap hD hDfin hk hkfin hDk fun q => kernelComp_mem hk hkfin (hDfin q)]
  -- All maps are kernel maps on the same completed module. On the support of `a ⊗ b` the
  -- generator degrees are `i` and `j`, so the signed kernels agree there by the hypothesis.
  ext p₀
  simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, Pi.sub_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, kernelMap_apply_val]
  rw [mul_finsum' _ _ (finite_support_mul_kernelMap hm _ p₀),
    ← finsum_sub_distrib (finite_support_mul_kernelMap (fun q => hn q.1 q.2) _ p₀)
      ((finite_support_mul_kernelMap hm _ p₀).subset fun q hq => right_ne_zero_of_mul hq),
    ← finsum_add_distrib (finite_support_mul_kernelMap hkδ _ p₀)
      (finite_support_mul_kernelMap hDk _ p₀)]
  refine finsum_congr fun q => ?_
  by_cases hq : (tensor a b).val q = 0
  · simp [hq]
  rw [tensor_apply_val] at hq
  rw [← mul_add, ← hcomm, mem_gradeBy_iff.1 ha q.1 (left_ne_zero_of_mul hq),
    mem_gradeBy_iff.1 hb q.2 (right_ne_zero_of_mul hq)]
  ring

/-- **Graded commutativity up to homotopy, with the Koszul signs.** Let `δ₁`, `δ₂` be kernels on
the input generators and let `D = δ₁ ⊗ 1 + (-1)^(d₁) ⊗ δ₂` be the tensor differential. If a
kernel `k` is a kernel homotopy,

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
    kernelMap_tensorDifferential_tensor hδ₁ hδ₁fin hδ₂ hδ₂fin hD hDfin ha, map_add, map_smul,
    add_assoc]

/-- **Graded commutativity on cocycles.** Under the hypotheses of
`NovikovModule.kernelProduct_sub_negOnePow_smul_kernelProduct_of_tensorDifferential`, if moreover
`δ₁ a = 0` and `δ₂ b = 0`, then `a ⋆ b - (-1)^(i j) b ⋆' a = δ₀ (K (a ⊗ b))` is a coboundary. -/
theorem kernelProduct_sub_negOnePow_smul_kernelProduct_of_eq_zero
    [DecidableEq S₁] [DecidableEq S₂] {δ₁ : S₁ → S₁ → R} {δ₂ : S₂ → S₂ → R} {E₁ E₂ : ℝ}
    (hδ₁ : ∀ p q, δ₁ p q ≠ 0 → F₁ q ≤ F₁ p + E₁) (hδ₁fin : ∀ p, δ₁ p ∈ NovikovModule R F₁)
    (hδ₂ : ∀ p q, δ₂ p q ≠ 0 → F₂ q ≤ F₂ p + E₂) (hδ₂fin : ∀ p, δ₂ p ∈ NovikovModule R F₂)
    (hcomm : ∀ (q : S₁ × S₂) p₀,
      n q.1 q.2 p₀ - ((d₁ q.1 * d₂ q.2).negOnePow : R) * n' q.2 q.1 p₀ =
        kernelComp k δ₀ q p₀ + kernelComp (tensorDifferential d₁ δ₁ δ₂) k q p₀)
    {i j : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ d₁ i)
    {b : NovikovModule R F₂} (hb : b ∈ gradeBy R F₂ d₂ j)
    (ha₀ : kernelMap hδ₁ hδ₁fin a = 0) (hb₀ : kernelMap hδ₂ hδ₂fin b = 0) :
    kernelProduct hn hfin a b - ((i * j).negOnePow : R) • kernelProduct hn' hfin' b a =
      kernelMap hδ₀ hδ₀fin (kernelMap hk hkfin (tensor a b)) := by
  rw [kernelProduct_sub_negOnePow_smul_kernelProduct_of_tensorDifferential hn hfin hn' hfin' hk
      hkfin hδ₀ hδ₀fin hδ₁ hδ₁fin hδ₂ hδ₂fin hcomm ha hb, ha₀, hb₀]
  simp

end CommRing

end NovikovModule

end TauCeti

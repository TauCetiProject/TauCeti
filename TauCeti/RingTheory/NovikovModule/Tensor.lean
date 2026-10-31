/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Grading
public import Mathlib.Algebra.Ring.NegOnePow

/-!
# Completed tensor products of Novikov modules

Let `F₁ : S₁ → ℝ` and `F₂ : S₂ → ℝ` be potentials. The *completed tensor product* of the
completed combinations `NovikovModule R F₁` and `NovikovModule R F₂` is the module of completed
combinations of pairs of generators, `NovikovModule R (fun q : S₁ × S₂ => F₁ q.1 + F₂ q.2)`, for
the sum of the two potentials. The tensor product of `a` and `b` is the combination
`(p₁, p₂) ↦ a(p₁) b(p₂)` (`NovikovModule.tensor`). It is finite above every threshold of the
summed potential because the potentials are bounded above on the supports of `a` and `b`.

This is not the algebraic tensor product: an element of the completed tensor product is in
general an infinite sum of tensor products. Its universal property concerns supported kernels.
A product kernel `n : S₁ → S₂ → S₀ → R` with potential bound
`F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C` is the same datum as a one-input kernel on pairs of generators with
potential bound `C`. The bilinear product of `n` is the kernel map of that kernel precomposed with
the tensor product (`NovikovModule.kernelProduct_eq_kernelMap_tensor`), and a kernel map out of
the completed tensor product is determined by its values on tensor products
(`NovikovModule.kernelMap_tensor_ext`). Kernel maps act on both factors by the tensor product of
kernels, `m₁(p₁, q₁) m₂(p₂, q₂)` (`NovikovModule.kernelMap_kernelTensor_tensor`).

For differentials `δ₁`, `δ₂` given by kernels and a degree function `d₁` on the generators of the
first factor, the tensor differential has the Koszul kernel
`δ₁ ⊗ 1 + (-1)^(d₁) ⊗ δ₂` (`NovikovModule.tensorDifferential`). On homogeneous combinations it
obeys the Leibniz rule `D (a ⊗ b) = δ₁ a ⊗ b + (-1)^i a ⊗ δ₂ b`
(`NovikovModule.kernelMap_tensorDifferential_tensor`), and if `δ₁` raises degree by one and both
differentials square to zero then so does `D`
(`NovikovModule.kernelMap_tensorDifferential_kernelMap_tensorDifferential_eq_zero`).

Since a bilinear product is a kernel map out of the completed tensor product, a chain-level
identity such as the Leibniz rule `δ₀ (a ⋆ b) = δ₁ a ⋆ b + (-1)^i a ⋆ δ₂ b` of a pair-of-pants
product, or a chain homotopy `f ∘ g - h = δ₀ ∘ K + K ∘ D` for a degree `-1` map `K` out of the
tensor product, is an identity between kernel maps on that module, and so follows from the
corresponding identity between kernels (`NovikovModule.kernelMap_kernelMap`).

## Main definitions

* `TauCeti.NovikovModule.tensor`: the completed tensor product of two completed combinations.
* `TauCeti.NovikovModule.kernelTensor`: the tensor product of two kernels.
* `TauCeti.NovikovModule.tensorDifferential`: the Koszul kernel of the tensor differential.

## Main results

* `TauCeti.NovikovModule.kernelProduct_eq_kernelMap_tensor`,
  `TauCeti.NovikovModule.kernelMap_tensor_ext`: kernel products are the kernel maps out of the
  completed tensor product, composed with the tensor product.
* `TauCeti.NovikovModule.kernelMap_kernelTensor_tensor`: kernel maps act factorwise on tensor
  products.
* `TauCeti.NovikovModule.tensor_mem_gradeBy`,
  `TauCeti.NovikovModule.degree_eq_of_tensorDifferential_ne_zero`: the tensor product adds degrees,
  and the tensor differential raises the total degree by one.
* `TauCeti.NovikovModule.kernelMap_tensorDifferential_tensor`: the Leibniz rule for the tensor
  differential.
* `TauCeti.NovikovModule.kernelMap_tensorDifferential_kernelMap_tensorDifferential_eq_zero`: the
  tensor differential squares to zero.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the pair-of-pants product as a chain map out of the tensor product.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
-/

public section

noncomputable section

open Function

namespace TauCeti

namespace NovikovModule

variable {R S₁ S₂ T₁ T₂ S₀ : Type*}

section CommSemiring

variable [CommSemiring R] {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ} {F₀ : S₀ → ℝ}

/-- The coefficientwise product of two completed combinations is a completed combination of
pairs of generators, for the sum of the two potentials. -/
theorem mul_mem_prod (a : NovikovModule R F₁) (b : NovikovModule R F₂) :
    (fun q : S₁ × S₂ => a.val q.1 * b.val q.2) ∈
      NovikovModule R fun q : S₁ × S₂ => F₁ q.1 + F₂ q.2 :=
  mem_iff_finite_ge.2 fun T => (finite_setOf_le_add a b T).subset fun _ hq =>
    ⟨left_ne_zero_of_mul hq.1, right_ne_zero_of_mul hq.1, hq.2⟩

/-- The completed tensor product of completed combinations: the coefficient of a pair of
generators `(p₁, p₂)` in the tensor product of `a` and `b` is `a(p₁) b(p₂)`. -/
def tensor : NovikovModule R F₁ →ₗ[R] NovikovModule R F₂ →ₗ[R]
    NovikovModule R fun q : S₁ × S₂ => F₁ q.1 + F₂ q.2 :=
  LinearMap.mk₂ R (fun a b => ⟨_, mul_mem_prod a b⟩)
    (fun a a' b => Subtype.ext <| funext fun q => add_mul (a.val q.1) (a'.val q.1) (b.val q.2))
    (fun c a b => Subtype.ext <| funext fun q => mul_assoc c (a.val q.1) (b.val q.2))
    (fun a b b' => Subtype.ext <| funext fun q => mul_add (a.val q.1) (b.val q.2) (b'.val q.2))
    (fun c a b => Subtype.ext <| funext fun q => mul_left_comm (a.val q.1) c (b.val q.2))

/-- The coefficient of a pair of generators in a tensor product is the product of the
coefficients. -/
@[simp]
theorem tensor_apply_val (a : NovikovModule R F₁) (b : NovikovModule R F₂) (q : S₁ × S₂) :
    (tensor a b).val q = a.val q.1 * b.val q.2 :=
  (rfl)

/-- The tensor product of two point masses is the point mass at the pair of generators, with the
product coefficient. -/
theorem tensor_pi_single [DecidableEq S₁] [DecidableEq S₂] (p₁ : S₁) (p₂ : S₂) (r₁ r₂ : R) :
    tensor (⟨Pi.single p₁ r₁, pi_single_mem p₁ r₁⟩ : NovikovModule R F₁)
        (⟨Pi.single p₂ r₂, pi_single_mem p₂ r₂⟩ : NovikovModule R F₂) =
      ⟨Pi.single (p₁, p₂) (r₁ * r₂), pi_single_mem _ _⟩ := by
  ext ⟨q₁, q₂⟩
  by_cases h₁ : q₁ = p₁ <;> by_cases h₂ : q₂ = p₂ <;> simp [h₁, h₂]

/-- Homogeneous tensor factors give a homogeneous tensor product, for the sum of the two degree
functions. -/
theorem tensor_mem_gradeBy {D : Type*} [Add D] {d₁ : S₁ → D} {d₂ : S₂ → D} {i j : D}
    {a : NovikovModule R F₁} {b : NovikovModule R F₂}
    (ha : a ∈ gradeBy R F₁ d₁ i) (hb : b ∈ gradeBy R F₂ d₂ j) :
    tensor a b ∈ gradeBy R _ (fun q : S₁ × S₂ => d₁ q.1 + d₂ q.2) (i + j) := by
  rw [mem_gradeBy_iff] at ha hb ⊢
  intro q hq
  rw [tensor_apply_val] at hq
  rw [ha q.1 (left_ne_zero_of_mul hq), hb q.2 (right_ne_zero_of_mul hq)]

section Universal

variable {C C' : ℝ}

/-- **Kernel products factor through the completed tensor product.** The product of a supported
product kernel `n` is the kernel map of the same kernel, read as a one-input kernel on pairs of
generators, applied to the tensor product. The two potential bounds may have different
constants. -/
theorem kernelProduct_eq_kernelMap_tensor {n : S₁ → S₂ → S₀ → R}
    (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
    (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)
    (hm : ∀ (q : S₁ × S₂) p₀, n q.1 q.2 p₀ ≠ 0 → F₀ p₀ ≤ F₁ q.1 + F₂ q.2 + C')
    (hmfin : ∀ q : S₁ × S₂, n q.1 q.2 ∈ NovikovModule R F₀)
    (a : NovikovModule R F₁) (b : NovikovModule R F₂) :
    kernelProduct hn hfin a b = kernelMap hm hmfin (tensor a b) := by
  ext p₀
  rw [kernelProduct_apply_val, kernelMap_apply_val]
  simp only [tensor_apply_val]

/-- **Kernel maps out of the completed tensor product are determined on tensor products.** Two
kernel maps out of the completed tensor product that agree on all tensor products of completed
combinations coincide. -/
theorem kernelMap_tensor_ext {m m' : S₁ × S₂ → S₀ → R}
    (hm : ∀ (q : S₁ × S₂) p₀, m q p₀ ≠ 0 → F₀ p₀ ≤ F₁ q.1 + F₂ q.2 + C)
    (hmfin : ∀ q, m q ∈ NovikovModule R F₀)
    (hm' : ∀ (q : S₁ × S₂) p₀, m' q p₀ ≠ 0 → F₀ p₀ ≤ F₁ q.1 + F₂ q.2 + C')
    (hmfin' : ∀ q, m' q ∈ NovikovModule R F₀)
    (h : ∀ a b, kernelMap hm hmfin (tensor a b) = kernelMap hm' hmfin' (tensor a b)) :
    kernelMap hm hmfin = kernelMap hm' hmfin' := by
  classical
  refine (kernelMap_inj hm hmfin hm' hmfin').2
    (funext fun q => funext fun p₀ => ?_)
  have hq := congrArg (fun x => x.val p₀)
    (h ⟨Pi.single q.1 1, pi_single_mem q.1 1⟩ ⟨Pi.single q.2 1, pi_single_mem q.2 1⟩)
  simpa only [tensor_pi_single, kernelMap_pi_single_apply_val, one_mul] using hq

end Universal

section KernelTensor

variable {G₁ : T₁ → ℝ} {G₂ : T₂ → ℝ} {C₁ C₂ : ℝ} {m₁ : S₁ → T₁ → R} {m₂ : S₂ → T₂ → R}

/-- The tensor product of a kernel `m₁` from `S₁` to `T₁` and a kernel `m₂` from `S₂` to `T₂`:
the coefficient from `(p₁, p₂)` to `(q₁, q₂)` is `m₁(p₁, q₁) m₂(p₂, q₂)`. -/
def kernelTensor (m₁ : S₁ → T₁ → R) (m₂ : S₂ → T₂ → R) (p : S₁ × S₂) (q : T₁ × T₂) : R :=
  m₁ p.1 q.1 * m₂ p.2 q.2

/-- A coefficient of a tensor product of kernels is the product of the coefficients. -/
@[simp]
theorem kernelTensor_apply (m₁ : S₁ → T₁ → R) (m₂ : S₂ → T₂ → R) (p : S₁ × S₂) (q : T₁ × T₂) :
    kernelTensor m₁ m₂ p q = m₁ p.1 q.1 * m₂ p.2 q.2 :=
  (rfl)

/-- **Potential bound of a tensor product of kernels.** The constants of the two potential bounds
add. -/
theorem potential_le_of_kernelTensor_ne_zero
    (hm₁ : ∀ p₁ q₁, m₁ p₁ q₁ ≠ 0 → G₁ q₁ ≤ F₁ p₁ + C₁)
    (hm₂ : ∀ p₂ q₂, m₂ p₂ q₂ ≠ 0 → G₂ q₂ ≤ F₂ p₂ + C₂) {p : S₁ × S₂} {q : T₁ × T₂}
    (h : kernelTensor m₁ m₂ p q ≠ 0) : G₁ q.1 + G₂ q.2 ≤ F₁ p.1 + F₂ p.2 + (C₁ + C₂) := by
  have h₁ := hm₁ _ _ (left_ne_zero_of_mul h)
  have h₂ := hm₂ _ _ (right_ne_zero_of_mul h)
  linarith

/-- **Completed outputs of a tensor product of kernels.** The output at `(p₁, p₂)` is the tensor
product of the outputs at `p₁` and at `p₂`. -/
theorem kernelTensor_mem (hmfin₁ : ∀ p₁, m₁ p₁ ∈ NovikovModule R G₁)
    (hmfin₂ : ∀ p₂, m₂ p₂ ∈ NovikovModule R G₂) (p : S₁ × S₂) :
    kernelTensor m₁ m₂ p ∈ NovikovModule R fun q : T₁ × T₂ => G₁ q.1 + G₂ q.2 :=
  mul_mem_prod ⟨m₁ p.1, hmfin₁ p.1⟩ ⟨m₂ p.2, hmfin₂ p.2⟩

/-- **Kernel maps act factorwise on tensor products.** The map of the tensor product of two
kernels sends the tensor product of `a` and `b` to the tensor product of their images. The
potential bound of the tensor product kernel may have any constant. -/
theorem kernelMap_kernelTensor_tensor
    (hm₁ : ∀ p₁ q₁, m₁ p₁ q₁ ≠ 0 → G₁ q₁ ≤ F₁ p₁ + C₁) (hmfin₁ : ∀ p₁, m₁ p₁ ∈ NovikovModule R G₁)
    (hm₂ : ∀ p₂ q₂, m₂ p₂ q₂ ≠ 0 → G₂ q₂ ≤ F₂ p₂ + C₂) (hmfin₂ : ∀ p₂, m₂ p₂ ∈ NovikovModule R G₂)
    {C : ℝ} (hm : ∀ p q, kernelTensor m₁ m₂ p q ≠ 0 → G₁ q.1 + G₂ q.2 ≤ F₁ p.1 + F₂ p.2 + C)
    (hmfin : ∀ p, kernelTensor m₁ m₂ p ∈ NovikovModule R fun q : T₁ × T₂ => G₁ q.1 + G₂ q.2)
    (a : NovikovModule R F₁) (b : NovikovModule R F₂) :
    kernelMap hm hmfin (tensor a b) = tensor (kernelMap hm₁ hmfin₁ a) (kernelMap hm₂ hmfin₂ b) := by
  ext ⟨q₁, q₂⟩
  rw [kernelMap_apply_val, finsum_curry _ (finite_support_mul_kernelMap hm (tensor a b) _),
    tensor_apply_val, kernelMap_apply_val, kernelMap_apply_val,
    finsum_mul' _ _ (finite_support_mul_kernelMap hm₁ a q₁)]
  refine finsum_congr fun p₁ => ?_
  rw [mul_finsum' _ _ (finite_support_mul_kernelMap hm₂ b q₂)]
  refine finsum_congr fun p₂ => ?_
  simp only [tensor_apply_val, kernelTensor_apply]
  ring

end KernelTensor

end CommSemiring

section Differential

variable [CommRing R] [DecidableEq S₁] [DecidableEq S₂] {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ}

/-- The kernel of the tensor differential for differentials with kernels `δ₁` and `δ₂` and the
degree function `d₁` on the generators of the first factor: the Koszul kernel
`δ₁ ⊗ 1 + (-1)^(d₁) ⊗ δ₂`, whose second term is `(-1)^(d₁ p₁) δ₂(p₂, q₂)` from `(p₁, p₂)` to
`(p₁, q₂)`. -/
def tensorDifferential (d₁ : S₁ → ℤ) (δ₁ : S₁ → S₁ → R) (δ₂ : S₂ → S₂ → R) :
    S₁ × S₂ → S₁ × S₂ → R :=
  kernelTensor δ₁ (fun p₂ q₂ => if p₂ = q₂ then 1 else 0) +
    kernelTensor (fun p₁ q₁ => if p₁ = q₁ then ((d₁ p₁).negOnePow : R) else 0) δ₂

/-- The tensor differential kernel is the sum of its two Koszul summands. -/
theorem tensorDifferential_eq_add (d₁ : S₁ → ℤ) (δ₁ : S₁ → S₁ → R) (δ₂ : S₂ → S₂ → R) :
    tensorDifferential d₁ δ₁ δ₂ =
      kernelTensor δ₁ (fun p₂ q₂ => if p₂ = q₂ then 1 else 0) +
        kernelTensor (fun p₁ q₁ => if p₁ = q₁ then ((d₁ p₁).negOnePow : R) else 0) δ₂ :=
  (rfl)

/-- A coefficient of the tensor differential kernel. -/
theorem tensorDifferential_apply (d₁ : S₁ → ℤ) (δ₁ : S₁ → S₁ → R) (δ₂ : S₂ → S₂ → R)
    (p q : S₁ × S₂) :
    tensorDifferential d₁ δ₁ δ₂ p q =
      δ₁ p.1 q.1 * (if p.2 = q.2 then 1 else 0) +
        (if p.1 = q.1 then ((d₁ p.1).negOnePow : R) else 0) * δ₂ p.2 q.2 :=
  (rfl)

variable {d₁ : S₁ → ℤ} {δ₁ : S₁ → S₁ → R} {δ₂ : S₂ → S₂ → R} {C₁ C₂ : ℝ}

/-- **The tensor differential has degree one.** If `δ₁` and `δ₂` raise the degrees `d₁` and `d₂`
by one, then the tensor differential raises the total degree `d₁ + d₂` by one. -/
theorem degree_eq_of_tensorDifferential_ne_zero {d₂ : S₂ → ℤ}
    (hd₁ : ∀ p q, δ₁ p q ≠ 0 → d₁ q = d₁ p + 1) (hd₂ : ∀ p q, δ₂ p q ≠ 0 → d₂ q = d₂ p + 1)
    {p q : S₁ × S₂} (h : tensorDifferential d₁ δ₁ δ₂ p q ≠ 0) :
    d₁ q.1 + d₂ q.2 = d₁ p.1 + d₂ p.2 + 1 := by
  rw [tensorDifferential_apply] at h
  by_cases h₁ : δ₁ p.1 q.1 * (if p.2 = q.2 then (1 : R) else 0) = 0
  · rw [h₁, zero_add] at h
    have h₂ : p.1 = q.1 := by
      by_contra hpq
      simp [hpq] at h
    rw [← h₂, hd₂ _ _ (right_ne_zero_of_mul h)]
    ring
  · have h₂ : p.2 = q.2 := by
      by_contra hpq
      simp [hpq] at h₁
    rw [← h₂, hd₁ _ _ (left_ne_zero_of_mul h₁)]
    ring

variable (hδ₁ : ∀ p q, δ₁ p q ≠ 0 → F₁ q ≤ F₁ p + C₁) (hδ₁fin : ∀ p, δ₁ p ∈ NovikovModule R F₁)
  (hδ₂ : ∀ p q, δ₂ p q ≠ 0 → F₂ q ≤ F₂ p + C₂) (hδ₂fin : ∀ p, δ₂ p ∈ NovikovModule R F₂)

omit [DecidableEq S₁] in
include hδ₁ in
/-- The potential bound of the summand `δ₁ ⊗ 1` of the tensor differential. -/
private theorem potential_le_of_kernelTensor_one_ne_zero {p q : S₁ × S₂}
    (h : kernelTensor δ₁ (fun p₂ q₂ => if p₂ = q₂ then (1 : R) else 0) p q ≠ 0) :
    F₁ q.1 + F₂ q.2 ≤ F₁ p.1 + F₂ p.2 + (C₁ + 0) :=
  potential_le_of_kernelTensor_ne_zero hδ₁
    (fun _ _ h => potential_le_of_diagonal_ne_zero (s := fun _ => (1 : R)) h) h

omit [DecidableEq S₂] in
include hδ₂ in
/-- The potential bound of the summand `(-1)^(d₁) ⊗ δ₂` of the tensor differential. -/
private theorem potential_le_of_kernelTensor_sign_ne_zero {p q : S₁ × S₂}
    (h : kernelTensor (fun p₁ q₁ => if p₁ = q₁ then ((d₁ p₁).negOnePow : R) else 0) δ₂ p q ≠ 0) :
    F₁ q.1 + F₂ q.2 ≤ F₁ p.1 + F₂ p.2 + (0 + C₂) :=
  potential_le_of_kernelTensor_ne_zero
    (fun _ _ h => potential_le_of_diagonal_ne_zero (s := fun p => ((d₁ p).negOnePow : R)) h) hδ₂ h

include hδ₁ hδ₂ in
/-- **Potential bound of the tensor differential.** Its constant is the larger of the constants
of the two differentials. -/
theorem potential_le_of_tensorDifferential_ne_zero {p q : S₁ × S₂}
    (h : tensorDifferential d₁ δ₁ δ₂ p q ≠ 0) :
    F₁ q.1 + F₂ q.2 ≤ F₁ p.1 + F₂ p.2 + max C₁ C₂ := by
  rw [tensorDifferential_eq_add, Pi.add_apply, Pi.add_apply] at h
  by_cases h₁ : kernelTensor δ₁ (fun p₂ q₂ => if p₂ = q₂ then (1 : R) else 0) p q = 0
  · rw [h₁, zero_add] at h
    linarith [potential_le_of_kernelTensor_sign_ne_zero (F₁ := F₁) hδ₂ h, le_max_right C₁ C₂]
  · linarith [potential_le_of_kernelTensor_one_ne_zero (F₂ := F₂) hδ₁ h₁, le_max_left C₁ C₂]

include hδ₁fin hδ₂fin in
/-- **Completed outputs of the tensor differential.** -/
theorem tensorDifferential_mem (p : S₁ × S₂) :
    tensorDifferential d₁ δ₁ δ₂ p ∈ NovikovModule R fun q : S₁ × S₂ => F₁ q.1 + F₂ q.2 := by
  rw [tensorDifferential_eq_add]
  exact add_mem (kernelTensor_mem hδ₁fin (diagonal_mem _) p)
    (kernelTensor_mem (diagonal_mem _) hδ₂fin p)

variable {C : ℝ}
  (hD : ∀ p q, tensorDifferential d₁ δ₁ δ₂ p q ≠ 0 → F₁ q.1 + F₂ q.2 ≤ F₁ p.1 + F₂ p.2 + C)
  (hDfin : ∀ p, tensorDifferential d₁ δ₁ δ₂ p ∈ NovikovModule R fun q : S₁ × S₂ => F₁ q.1 + F₂ q.2)

include hδ₁ hδ₂ in
/-- **The Leibniz rule for the tensor differential.** On the tensor product of a combination `a`
of degree `i` with any `b`, the tensor differential is `δ₁ a ⊗ b + (-1)^i a ⊗ δ₂ b`. -/
theorem kernelMap_tensorDifferential_tensor {i : ℤ} {a : NovikovModule R F₁}
    (ha : a ∈ gradeBy R F₁ d₁ i) (b : NovikovModule R F₂) :
    kernelMap hD hDfin (tensor a b) =
      tensor (kernelMap hδ₁ hδ₁fin a) b +
        (i.negOnePow : R) • tensor a (kernelMap hδ₂ hδ₂fin b) := by
  have hι₂ (p₂ q₂ : S₂) (h : (if p₂ = q₂ then (1 : R) else 0) ≠ 0) : F₂ q₂ ≤ F₂ p₂ + 0 :=
    potential_le_of_diagonal_ne_zero (s := fun _ => (1 : R)) h
  have hσ (p₁ q₁ : S₁) (h : (if p₁ = q₁ then ((d₁ p₁).negOnePow : R) else 0) ≠ 0) :
      F₁ q₁ ≤ F₁ p₁ + 0 :=
    potential_le_of_diagonal_ne_zero (s := fun p => ((d₁ p).negOnePow : R)) h
  -- Split the tensor differential kernel into its two summands, via `kernelMap_inj`.
  have hE (p q : S₁ × S₂) (h : (kernelTensor δ₁ (fun p₂ q₂ => if p₂ = q₂ then (1 : R) else 0) +
      kernelTensor (fun p₁ q₁ => if p₁ = q₁ then ((d₁ p₁).negOnePow : R) else 0) δ₂ :
        S₁ × S₂ → S₁ × S₂ → R) p q ≠ 0) :
      F₁ q.1 + F₂ q.2 ≤ F₁ p.1 + F₂ p.2 + C :=
    hD p q (by rwa [tensorDifferential_eq_add])
  have hEfin (p : S₁ × S₂) :=
    add_mem (kernelTensor_mem hδ₁fin (diagonal_mem (fun _ => (1 : R))) p)
      (kernelTensor_mem (diagonal_mem fun p₁ => ((d₁ p₁).negOnePow : R)) hδ₂fin p)
  have hadd : kernelMap hD hDfin =
      kernelMap (fun _ _ => potential_le_of_kernelTensor_one_ne_zero hδ₁)
          (kernelTensor_mem hδ₁fin (diagonal_mem fun _ => (1 : R))) +
        kernelMap (fun _ _ => potential_le_of_kernelTensor_sign_ne_zero (d₁ := d₁) hδ₂)
          (kernelTensor_mem (diagonal_mem fun p₁ => ((d₁ p₁).negOnePow : R)) hδ₂fin) := by
    rw [(kernelMap_inj hD hDfin hE hEfin).2 (tensorDifferential_eq_add d₁ δ₁ δ₂)]
    exact kernelMap_add _ _ _ _ hE hEfin
  rw [hadd, LinearMap.add_apply,
    kernelMap_kernelTensor_tensor hδ₁ hδ₁fin hι₂ (diagonal_mem _),
    kernelMap_kernelTensor_tensor hσ (diagonal_mem _) hδ₂ hδ₂fin, kernelMap_eq_id]
  -- On combinations of degree `i`, the diagonal sign kernel is multiplication by `(-1)^i`.
  have hsign : kernelMap hσ (diagonal_mem _) a = (i.negOnePow : R) • a := by
    ext p₁
    rw [kernelMap_diagonal_apply_val, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hp : a.val p₁ = 0
    · simp [hp]
    · rw [mem_gradeBy_iff.1 ha p₁ hp, mul_comm]
  rw [hsign, LinearMap.map_smul₂, LinearMap.id_apply]

include hδ₁ hδ₂ in
/-- **The tensor differential squares to zero.** If `δ₁` raises the degree `d₁` by one and both
differentials square to zero, then so does the tensor differential. -/
theorem kernelMap_tensorDifferential_kernelMap_tensorDifferential_eq_zero
    (hd : ∀ p q, δ₁ p q ≠ 0 → d₁ q = d₁ p + 1)
    (hδ₁δ₁ : ∀ a, kernelMap hδ₁ hδ₁fin (kernelMap hδ₁ hδ₁fin a) = 0)
    (hδ₂δ₂ : ∀ b, kernelMap hδ₂ hδ₂fin (kernelMap hδ₂ hδ₂fin b) = 0)
    (x : NovikovModule R fun q : S₁ × S₂ => F₁ q.1 + F₂ q.2) :
    kernelMap hD hDfin (kernelMap hD hDfin x) = 0 := by
  -- The composite is the kernel map of the composite kernel, which vanishes: its row at
  -- `(p₁, p₂)` is the image of the point mass there, a tensor product of homogeneous point masses.
  have hE (p r : S₁ × S₂) (h : kernelComp (tensorDifferential d₁ δ₁ δ₂)
      (tensorDifferential d₁ δ₁ δ₂) p r ≠ 0) :
      F₁ r.1 + F₂ r.2 ≤ F₁ p.1 + F₂ p.2 + (C + C) := by
    linarith [potential_le_of_kernelComp_ne_zero (F₀ := fun q : S₁ × S₂ => F₁ q.1 + F₂ q.2)
      (F₂ := fun q : S₁ × S₂ => F₁ q.1 + F₂ q.2) (hD p) (hD · r) h]
  have hEfin (p : S₁ × S₂) := kernelComp_mem hD hDfin (hDfin p)
  rw [kernelMap_kernelMap hD hDfin hD hDfin hE hEfin]
  suffices hz : kernelComp (tensorDifferential d₁ δ₁ δ₂) (tensorDifferential d₁ δ₁ δ₂) = 0 by
    have h0 := (kernelMap_inj hE hEfin (C' := 0) (m' := 0) (fun _ _ h => absurd rfl h)
      fun _ => zero_mem _).2 hz
    rw [h0, kernelMap_zero, LinearMap.zero_apply]
  funext ⟨p₁, p₂⟩ r
  set e₁ : NovikovModule R F₁ := ⟨Pi.single p₁ 1, pi_single_mem p₁ 1⟩
  set e₂ : NovikovModule R F₂ := ⟨Pi.single p₂ 1, pi_single_mem p₂ 1⟩
  have he₁ : e₁ ∈ gradeBy R F₁ d₁ (d₁ p₁) := pi_single_mem_gradeBy d₁ p₁ 1
  have hδe₁ : kernelMap hδ₁ hδ₁fin e₁ ∈ gradeBy R F₁ d₁ (d₁ p₁ + 1) :=
    kernelMap_mem_gradeBy hδ₁ hδ₁fin hd he₁
  have key : (kernelMap hD hDfin (kernelMap hD hDfin (tensor e₁ e₂))).val r =
      kernelComp (tensorDifferential d₁ δ₁ δ₂) (tensorDifferential d₁ δ₁ δ₂) (p₁, p₂) r := by
    rw [tensor_pi_single, kernelMap_kernelMap hD hDfin hD hDfin hE hEfin,
      kernelMap_pi_single_apply_val, one_mul, one_mul]
  rw [kernelMap_tensorDifferential_tensor hδ₁ hδ₁fin hδ₂ hδ₂fin hD hDfin he₁, map_add, map_smul,
    kernelMap_tensorDifferential_tensor hδ₁ hδ₁fin hδ₂ hδ₂fin hD hDfin hδe₁,
    kernelMap_tensorDifferential_tensor hδ₁ hδ₁fin hδ₂ hδ₂fin hD hDfin he₁, hδ₁δ₁, hδ₂δ₂,
    Int.negOnePow_succ, Units.val_neg, Int.cast_neg] at key
  simpa [smul_add, add_comm] using key.symm

end Differential

end NovikovModule

end TauCeti

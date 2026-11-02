/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Tensor
public import TauCeti.Algebra.Homology.SquareZero.Graded

/-!
# Graded commutativity homotopies of supported kernel products

Let `⋆` be the product of completed combinations given by a supported product kernel
`n(p₁, p₂, p₀)` (`TauCeti.NovikovModule.kernelProduct`), and let `⋆'` be a product with the two
inputs exchanged, given by a kernel `n'(p₂, p₁, p₀)`. Both `a ⋆ b` and the exchanged product
`b ⋆' a` are kernel maps out of the completed tensor product `a ⊗ b`
(`NovikovModule.kernelProduct_eq_kernelMap_tensor`,
`NovikovModule.kernelProduct_eq_kernelMap_tensor_swap`). For degree functions `d₁`, `d₂` on the
two inputs and `a`, `b` homogeneous of degrees `i`, `j`, the exchanged product with the Koszul sign
`(-1)^(i j)` is the kernel map of the signed exchanged kernel `(-1)^(d₁ p₁ d₂ p₂) n'(p₂, p₁, ·)`
(`NovikovModule.negOnePowCast_smul_kernelProduct_eq_kernelMap_tensor`).

For the pair-of-pants product in Floer theory, a one-parameter family of three-punctured spheres
rotates the two input ends around each other by a half turn. Its two ends are the product and the
product with exchanged inputs, whose orientation differs from the first by the Koszul sign of
exchanging the input determinant lines. The other codimension-one boundary points of the
one-dimensional moduli spaces are breakings of a Floer cylinder at one of the three ends, so the
count of all boundary points gives the kernel identity

`n(p₁, p₂, p₀) - (-1)^(d₁ p₁ d₂ p₂) n'(p₂, p₁, p₀) = (k δ₀ + D k)((p₁, p₂), p₀)`

for the kernel `k` counting rigid elements of the family, the output differential `δ₀` and the
differential `D` of the tensor product. This file turns that identity into the chain homotopy

`a ⋆ b - (-1)^(i j) b ⋆' a = δ₀ (K (a ⊗ b)) + K (D (a ⊗ b))`

for the kernel map `K` of `k` (`NovikovModule.kernelProduct_sub_smul_kernelProduct`). Both sides
are infinite sums. When `D` is the Koszul tensor differential `δ₁ ⊗ 1 + (-1)^(d₁) ⊗ δ₂`, the
second term is `K (δ₁ a ⊗ b) + (-1)^i K (a ⊗ δ₂ b)`
(`NovikovModule.kernelProduct_sub_smul_kernelProduct_of_tensorDifferential`). If `K` shifts degree
by one less than the products do, then on cocycles the difference is a coboundary
(`NovikovModule.kernelProduct_sub_smul_kernelProduct_mem_coboundaries`), and the products induced
on degree-wise cohomology satisfy `x ⋆ y = (-1)^(i j) y ⋆' x`
(`NovikovModule.cohomologyProduct_kernelProduct_comm`). With `⋆' = ⋆` on a common complex this is
graded commutativity of the product on cohomology. The chain-level product need not be strictly
commutative. The kernel identity and the potential bounds of the kernels remain hypotheses here:
they are the geometric input from the compactified moduli spaces.

## Main results

* `NovikovModule.kernelProduct_eq_kernelMap_tensor_swap`: a product with exchanged inputs is a
  kernel map out of the tensor product of the original inputs.
* `NovikovModule.negOnePowCast_smul_kernelProduct_eq_kernelMap_tensor`: the same, with the Koszul
  sign, on homogeneous inputs.
* `NovikovModule.kernelProduct_sub_smul_kernelProduct`: a kernel homotopy between a product kernel
  and the signed exchanged kernel gives a chain homotopy between the two products.
* `NovikovModule.kernelProduct_sub_smul_kernelProduct_of_tensorDifferential`: the same homotopy
  for the Koszul differential of the tensor product, with its signs.
* `NovikovModule.kernelProduct_sub_smul_kernelProduct_mem_coboundaries`,
  `NovikovModule.cohomologyProduct_kernelProduct_comm`: graded commutativity on cohomology.

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

section CommSemiring

variable [CommSemiring R] {C C' : ℝ}

/-- **Exchanged products factor through the completed tensor product.** For a product kernel `n'`
on `S₂ × S₁`, the product `b ⋆' a` with exchanged inputs is the kernel map, out of the completed
tensor product `a ⊗ b`, of the exchanged kernel `n'(p₂, p₁, ·)`. The two potential bounds may have
different constants. -/
theorem kernelProduct_eq_kernelMap_tensor_swap {n' : S₂ → S₁ → S₀ → R}
    (hn' : ∀ p₂ p₁ p₀, n' p₂ p₁ p₀ ≠ 0 → F₀ p₀ ≤ F₂ p₂ + F₁ p₁ + C)
    (hfin' : ∀ p₂ p₁, n' p₂ p₁ ∈ NovikovModule R F₀)
    (hm : ∀ (q : S₁ × S₂) p₀, n' q.2 q.1 p₀ ≠ 0 → F₀ p₀ ≤ F₁ q.1 + F₂ q.2 + C')
    (hmfin : ∀ q : S₁ × S₂, n' q.2 q.1 ∈ NovikovModule R F₀)
    (a : NovikovModule R F₁) (b : NovikovModule R F₂) :
    kernelProduct hn' hfin' b a = kernelMap hm hmfin (tensor a b) := by
  ext p₀
  -- Reindex the sum over `S₂ × S₁` by the exchange of factors.
  rw [kernelProduct_apply_val, kernelMap_apply_val, ← finsum_comp_equiv (Equiv.prodComm S₁ S₂)]
  refine finsum_congr fun q => ?_
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, tensor_apply_val]
  ring

end CommSemiring

section CommRing

variable [CommRing R] {C C' Ck C₀ : ℝ} {d₁ : S₁ → ℤ} {d₂ : S₂ → ℤ}

/-- **Koszul-signed exchanged products.** For `a` of degree `i` and `b` of degree `j`, the product
`b ⋆' a` with exchanged inputs and the Koszul sign `(-1)^(i j)` is the kernel map, out of the
completed tensor product `a ⊗ b`, of the signed exchanged kernel
`(-1)^(d₁ p₁ d₂ p₂) n'(p₂, p₁, ·)`. -/
theorem negOnePowCast_smul_kernelProduct_eq_kernelMap_tensor {n' : S₂ → S₁ → S₀ → R}
    (hn' : ∀ p₂ p₁ p₀, n' p₂ p₁ p₀ ≠ 0 → F₀ p₀ ≤ F₂ p₂ + F₁ p₁ + C)
    (hfin' : ∀ p₂ p₁, n' p₂ p₁ ∈ NovikovModule R F₀)
    (hm : ∀ (q : S₁ × S₂) p₀, negOnePowCast R (d₁ q.1 * d₂ q.2) * n' q.2 q.1 p₀ ≠ 0 →
      F₀ p₀ ≤ F₁ q.1 + F₂ q.2 + C')
    (hmfin : ∀ q : S₁ × S₂,
      (fun p₀ => negOnePowCast R (d₁ q.1 * d₂ q.2) * n' q.2 q.1 p₀) ∈ NovikovModule R F₀)
    {i j : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ d₁ i)
    {b : NovikovModule R F₂} (hb : b ∈ gradeBy R F₂ d₂ j) :
    negOnePowCast R (i * j) • kernelProduct hn' hfin' b a = kernelMap hm hmfin (tensor a b) := by
  have hm' (q : S₁ × S₂) (p₀ : S₀) (h : n' q.2 q.1 p₀ ≠ 0) : F₀ p₀ ≤ F₁ q.1 + F₂ q.2 + C := by
    linarith [hn' q.2 q.1 p₀ h]
  rw [kernelProduct_eq_kernelMap_tensor_swap hn' hfin' hm' (fun q => hfin' q.2 q.1)]
  ext p₀
  rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, kernelMap_apply_val, kernelMap_apply_val,
    mul_finsum' _ _ (finite_support_mul_kernelMap hm' (tensor a b) p₀)]
  refine finsum_congr fun q => ?_
  rw [tensor_apply_val]
  -- On the support of `a ⊗ b` the degrees are `i` and `j`, so the signs agree.
  by_cases ha' : a.val q.1 = 0
  · simp [ha']
  by_cases hb' : b.val q.2 = 0
  · simp [hb']
  rw [mem_gradeBy_iff.1 ha q.1 ha', mem_gradeBy_iff.1 hb q.2 hb']
  ring

variable {n : S₁ → S₂ → S₀ → R} {n' : S₂ → S₁ → S₀ → R} {k : S₁ × S₂ → S₀ → R}
  {δ₀ : S₀ → S₀ → R}
  (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
  (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)
  (hn' : ∀ p₂ p₁ p₀, n' p₂ p₁ p₀ ≠ 0 → F₀ p₀ ≤ F₂ p₂ + F₁ p₁ + C')
  (hfin' : ∀ p₂ p₁, n' p₂ p₁ ∈ NovikovModule R F₀)
  (hk : ∀ (q : S₁ × S₂) p₀, k q p₀ ≠ 0 → F₀ p₀ ≤ F₁ q.1 + F₂ q.2 + Ck)
  (hkfin : ∀ q, k q ∈ NovikovModule R F₀)
  (hδ₀ : ∀ p q, δ₀ p q ≠ 0 → F₀ q ≤ F₀ p + C₀) (hδ₀fin : ∀ p, δ₀ p ∈ NovikovModule R F₀)

/-- **Graded commutativity up to homotopy.** Let `n` and `n'` be the product kernels of `a ⋆ b` and
of the product `b ⋆' a` with exchanged inputs, let `δ₀` be a kernel on the output generators, and
let `D` be a kernel on the tensor product. If a kernel `k` from the tensor product to the output is
a kernel homotopy,

`n(p₁, p₂, p₀) - (-1)^(d₁ p₁ d₂ p₂) n'(p₂, p₁, p₀) = (k δ₀ + D k)((p₁, p₂), p₀)`,

then for `a` of degree `i` and `b` of degree `j` its kernel map `K` is a homotopy between the two
products: `a ⋆ b - (-1)^(i j) b ⋆' a = δ₀ (K (a ⊗ b)) + K (D (a ⊗ b))`. -/
theorem kernelProduct_sub_smul_kernelProduct
    {D : S₁ × S₂ → S₁ × S₂ → R} {CD : ℝ}
    (hD : ∀ q q', D q q' ≠ 0 → F₁ q'.1 + F₂ q'.2 ≤ F₁ q.1 + F₂ q.2 + CD)
    (hDfin : ∀ q, D q ∈ NovikovModule R fun q' : S₁ × S₂ => F₁ q'.1 + F₂ q'.2)
    (hcomm : ∀ (q : S₁ × S₂) p₀,
      n q.1 q.2 p₀ - negOnePowCast R (d₁ q.1 * d₂ q.2) * n' q.2 q.1 p₀ =
        kernelComp k δ₀ q p₀ + kernelComp D k q p₀)
    {i j : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ d₁ i)
    {b : NovikovModule R F₂} (hb : b ∈ gradeBy R F₂ d₂ j) :
    kernelProduct hn hfin a b - negOnePowCast R (i * j) • kernelProduct hn' hfin' b a =
      kernelMap hδ₀ hδ₀fin (kernelMap hk hkfin (tensor a b)) +
        kernelMap hk hkfin (kernelMap hD hDfin (tensor a b)) := by
  -- Both products are kernel maps out of the tensor product.
  have hm (q : S₁ × S₂) (p₀ : S₀) (h : n q.1 q.2 p₀ ≠ 0) : F₀ p₀ ≤ F₁ q.1 + F₂ q.2 + C :=
    hn q.1 q.2 p₀ h
  have hσ (q : S₁ × S₂) (p₀ : S₀) (h : negOnePowCast R (d₁ q.1 * d₂ q.2) * n' q.2 q.1 p₀ ≠ 0) :
      F₀ p₀ ≤ F₁ q.1 + F₂ q.2 + C' := by
    linarith [hn' q.2 q.1 p₀ (right_ne_zero_of_mul h)]
  have hσfin (q : S₁ × S₂) :
      (fun p₀ => negOnePowCast R (d₁ q.1 * d₂ q.2) * n' q.2 q.1 p₀) ∈ NovikovModule R F₀ :=
    Submodule.smul_mem _ _ (hfin' q.2 q.1)
  rw [kernelProduct_eq_kernelMap_tensor hn hfin hm (fun q => hfin q.1 q.2),
    negOnePowCast_smul_kernelProduct_eq_kernelMap_tensor hn' hfin' hσ hσfin ha hb]
  exact kernelMap_sub_kernelMap hm _ hσ hσfin hk hkfin hD hDfin hδ₀ hδ₀fin hcomm _

section Koszul

variable [DecidableEq S₁] [DecidableEq S₂] {δ₁ : S₁ → S₁ → R} {δ₂ : S₂ → S₂ → R} {E₁ E₂ : ℝ}
  (hδ₁ : ∀ p q, δ₁ p q ≠ 0 → F₁ q ≤ F₁ p + E₁) (hδ₁fin : ∀ p, δ₁ p ∈ NovikovModule R F₁)
  (hδ₂ : ∀ p q, δ₂ p q ≠ 0 → F₂ q ≤ F₂ p + E₂) (hδ₂fin : ∀ p, δ₂ p ∈ NovikovModule R F₂)

/-- **Graded commutativity up to homotopy, with the Koszul signs.** Let `δ₁`, `δ₂` be kernels on
the two input generators and `D = δ₁ ⊗ 1 + (-1)^(d₁) ⊗ δ₂` the tensor differential. If a kernel `k`
is a kernel homotopy,

`n(p₁, p₂, p₀) - (-1)^(d₁ p₁ d₂ p₂) n'(p₂, p₁, p₀) = (k δ₀ + D k)((p₁, p₂), p₀)`,

then for `a` of degree `i` and `b` of degree `j` its kernel map `K` satisfies

`a ⋆ b - (-1)^(i j) b ⋆' a = δ₀ (K (a ⊗ b)) + K (δ₁ a ⊗ b) + (-1)^i K (a ⊗ δ₂ b)`. -/
theorem kernelProduct_sub_smul_kernelProduct_of_tensorDifferential
    (hcomm : ∀ (q : S₁ × S₂) p₀,
      n q.1 q.2 p₀ - negOnePowCast R (d₁ q.1 * d₂ q.2) * n' q.2 q.1 p₀ =
        kernelComp k δ₀ q p₀ + kernelComp (tensorDifferential d₁ δ₁ δ₂) k q p₀)
    {i j : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ d₁ i)
    {b : NovikovModule R F₂} (hb : b ∈ gradeBy R F₂ d₂ j) :
    kernelProduct hn hfin a b - negOnePowCast R (i * j) • kernelProduct hn' hfin' b a =
      kernelMap hδ₀ hδ₀fin (kernelMap hk hkfin (tensor a b)) +
        kernelMap hk hkfin (tensor (kernelMap hδ₁ hδ₁fin a) b) +
        negOnePowCast R i • kernelMap hk hkfin (tensor a (kernelMap hδ₂ hδ₂fin b)) := by
  have hD (p q : S₁ × S₂) (h : tensorDifferential d₁ δ₁ δ₂ p q ≠ 0) :=
    potential_le_of_tensorDifferential_ne_zero hδ₁ hδ₂ h
  rw [kernelProduct_sub_smul_kernelProduct hn hfin hn' hfin' hk hkfin hδ₀ hδ₀fin hD
      (tensorDifferential_mem hδ₁fin hδ₂fin) hcomm ha hb,
    kernelMap_tensorDifferential_tensor hδ₁ hδ₁fin hδ₂ hδ₂fin hD _ ha]
  simp only [map_add, map_smul, add_assoc, negOnePowCast_eq_intCast]

include hk hkfin hδ₁ hδ₂ in
/-- **Graded commutativity on cocycles.** Under the kernel homotopy of
`NovikovModule.kernelProduct_sub_smul_kernelProduct_of_tensorDifferential`, if the homotopy kernel
`k` shifts the total degree by `ε - 1`, then for cocycles `a` of degree `i` and `b` of degree `j`
the difference `a ⋆ b - (-1)^(i j) b ⋆' a` is a coboundary of degree `i + j + ε`. -/
theorem kernelProduct_sub_smul_kernelProduct_mem_coboundaries {d₀ : S₀ → ℤ} {ε : ℤ}
    (hkd : ∀ q p₀, k q p₀ ≠ 0 → d₀ p₀ = d₁ q.1 + d₂ q.2 + ε - 1)
    (hcomm : ∀ (q : S₁ × S₂) p₀,
      n q.1 q.2 p₀ - negOnePowCast R (d₁ q.1 * d₂ q.2) * n' q.2 q.1 p₀ =
        kernelComp k δ₀ q p₀ + kernelComp (tensorDifferential d₁ δ₁ δ₂) k q p₀)
    {i j : ℤ} {a : NovikovModule R F₁}
    (ha : a ∈ (kernelMap hδ₁ hδ₁fin).cocycles (gradeBy R F₁ d₁) i)
    {b : NovikovModule R F₂} (hb : b ∈ (kernelMap hδ₂ hδ₂fin).cocycles (gradeBy R F₂ d₂) j) :
    kernelProduct hn hfin a b - negOnePowCast R (i * j) • kernelProduct hn' hfin' b a ∈
      (kernelMap hδ₀ hδ₀fin).coboundaries (gradeBy R F₀ d₀) (i + j + ε) := by
  rw [LinearMap.mem_cocycles_iff] at ha hb
  rw [kernelProduct_sub_smul_kernelProduct_of_tensorDifferential hn hfin hn' hfin' hk hkfin hδ₀
      hδ₀fin hδ₁ hδ₁fin hδ₂ hδ₂fin hcomm ha.2 hb.2, ha.1, hb.1, map_zero, LinearMap.zero_apply,
    map_zero, map_zero, map_zero, smul_zero, add_zero, add_zero]
  refine LinearMap.mem_coboundaries_iff.2 ⟨_, ?_, rfl⟩
  rw [add_sub_assoc]
  exact kernelMap_mem_gradeBy hk hkfin (fun q p₀ h => by rw [hkd q p₀ h, add_sub_assoc])
    (tensor_mem_gradeBy ha.2 hb.2)

section Cohomology

variable {d₀ : S₀ → ℤ} {ε : ℤ}
  (hdeg : ∀ {i j : ℤ} {a : NovikovModule R F₁} {b : NovikovModule R F₂},
    a ∈ gradeBy R F₁ d₁ i → b ∈ gradeBy R F₂ d₂ j →
      kernelProduct hn hfin a b ∈ gradeBy R F₀ d₀ (i + j + ε))
  (hL : ∀ {i : ℤ} {a : NovikovModule R F₁}, a ∈ gradeBy R F₁ d₁ i → ∀ b,
    kernelMap hδ₀ hδ₀fin (kernelProduct hn hfin a b) =
      kernelProduct hn hfin (kernelMap hδ₁ hδ₁fin a) b +
        negOnePowCast R i • kernelProduct hn hfin a (kernelMap hδ₂ hδ₂fin b))
  (hdeg' : ∀ {j i : ℤ} {b : NovikovModule R F₂} {a : NovikovModule R F₁},
    b ∈ gradeBy R F₂ d₂ j → a ∈ gradeBy R F₁ d₁ i →
      kernelProduct hn' hfin' b a ∈ gradeBy R F₀ d₀ (j + i + ε))
  (hL' : ∀ {j : ℤ} {b : NovikovModule R F₂}, b ∈ gradeBy R F₂ d₂ j → ∀ a,
    kernelMap hδ₀ hδ₀fin (kernelProduct hn' hfin' b a) =
      kernelProduct hn' hfin' (kernelMap hδ₂ hδ₂fin b) a +
        negOnePowCast R j • kernelProduct hn' hfin' b (kernelMap hδ₁ hδ₁fin a))

include hk hkfin hδ₁ hδ₂ in
/-- **Graded commutativity on cohomology.** Let `⋆` and the product `⋆'` with exchanged inputs
obey the Leibniz rule and shift degree by `ε`, so that they induce products on degree-wise
cohomology. Suppose they are related by a kernel homotopy `k` shifting the total degree by `ε - 1`,

`n(p₁, p₂, p₀) - (-1)^(d₁ p₁ d₂ p₂) n'(p₂, p₁, p₀) = (k δ₀ + D k)((p₁, p₂), p₀)`,

for the tensor differential `D`. Then for cohomology classes `x` of degree `i` and `y` of degree
`j`, `x ⋆ y = (-1)^(i j) y ⋆' x`. -/
theorem cohomologyProduct_kernelProduct_comm
    (hkd : ∀ q p₀, k q p₀ ≠ 0 → d₀ p₀ = d₁ q.1 + d₂ q.2 + ε - 1)
    (hcomm : ∀ (q : S₁ × S₂) p₀,
      n q.1 q.2 p₀ - negOnePowCast R (d₁ q.1 * d₂ q.2) * n' q.2 q.1 p₀ =
        kernelComp k δ₀ q p₀ + kernelComp (tensorDifferential d₁ δ₁ δ₂) k q p₀)
    {i j l : ℤ} (hij : i + j + ε = l)
    (x : (kernelMap hδ₁ hδ₁fin).cohomology (gradeBy R F₁ d₁) i)
    (y : (kernelMap hδ₂ hδ₂fin).cohomology (gradeBy R F₂ d₂) j) :
    LinearMap.cohomologyProduct (kernelProduct hn hfin) hdeg hL hij x y =
      negOnePowCast R (i * j) •
        LinearMap.cohomologyProduct (kernelProduct hn' hfin') hdeg' hL'
          ((congrArg (· + ε) (add_comm j i)).trans hij) y x := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  subst hij
  rw [LinearMap.cohomologyProduct_mk, LinearMap.cohomologyProduct_mk,
    ← Submodule.Quotient.mk_smul, LinearMap.cohomology_mk_eq_mk_iff]
  exact kernelProduct_sub_smul_kernelProduct_mem_coboundaries hn hfin hn' hfin' hk hkfin hδ₀
    hδ₀fin hδ₁ hδ₁fin hδ₂ hδ₂fin hkd hcomm a.2 b.2

end Cohomology

end Koszul

end CommRing

end NovikovModule

end TauCeti

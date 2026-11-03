/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Tensor
public import TauCeti.Algebra.Homology.SquareZero.Graded

/-!
# Continuation homotopies of supported kernel products

Let `⋆` be the product of completed combinations given by a supported product kernel
`n(p₁, p₂, p₀)` from generators `S₁ × S₂` to `S₀` (`TauCeti.NovikovModule.kernelProduct`), and
`⋆'` the product given by a second product kernel `n'(t₁, t₂, t₀)` from `T₁ × T₂` to `T₀`. Let
`φ₁`, `φ₂`, `φ₀` be supported kernels from `S₁` to `T₁`, from `S₂` to `T₂` and from `S₀` to
`T₀`, with kernel maps `NovikovModule.kernelMap`. There are two ways of passing from a pair of
completed combinations `a`, `b` to a completed combination of output generators `T₀`: first
multiply and then apply `φ₀`, giving `φ₀ (a ⋆ b)`; or first apply `φ₁` and `φ₂` and then
multiply, giving `φ₁ a ⋆' φ₂ b`. Both are kernel maps out of the completed tensor product
`a ⊗ b`, with the kernels `∑ₚ n(p₁, p₂, p) φ₀(p, ·)` and
`∑_{t₁, t₂} φ₁(p₁, t₁) φ₂(p₂, t₂) n'(t₁, t₂, ·)`, the composites
`NovikovModule.kernelComp` of the product kernel with `φ₀` and of the tensor product of kernels
`NovikovModule.kernelTensor φ₁ φ₂` with `n'`.

For the pair-of-pants product in Floer theory, `⋆` and `⋆'` are the products for two triples of
end Hamiltonians `(H₁, H₂, H₀)` and `(H₁', H₂', H₀')`, and `φᵢ` is the continuation map from the
Floer complex of `Hᵢ` to that of `Hᵢ'`. The two composite kernels count the two broken
configurations at the ends of a one-parameter family of pairs of pants with end-changing data:
a pair of pants for the first triple followed by a continuation cylinder at its output, and
continuation cylinders at both inputs followed by a pair of pants for the second triple. The
other codimension-one boundary points of the one-dimensional moduli spaces are breakings of a
Floer cylinder at one of the three ends, so the count of all boundary points gives the kernel
identity

`∑ₚ n(p₁, p₂, p) φ₀(p, t₀) - ∑_{t₁, t₂} φ₁(p₁, t₁) φ₂(p₂, t₂) n'(t₁, t₂, t₀) =
  (k δ₀ + D k)(q, t₀)`

for the kernel `k(q, t₀)` counting rigid elements of the family, the differential `δ₀` of the
target output complex and the differential `D` of the source tensor product, at every pair
`q = (p₁, p₂)`. This file turns that identity into the chain homotopy

`φ₀ (a ⋆ b) - φ₁ a ⋆' φ₂ b = δ₀ (K (a ⊗ b)) + K (D (a ⊗ b))`

between the two composites, where `K` is the kernel map of `k`, for arbitrary completed
combinations: both sides are infinite sums
(`NovikovModule.kernelMap_kernelProduct_sub_kernelProduct_kernelMap_kernelMap`). When `D` is the
Koszul tensor differential `δ₁ ⊗ 1 + (-1)^(d₁) ⊗ δ₂` and `a` is homogeneous of degree `i`, the
second term expands to `K (δ₁ a ⊗ b) + (-1)^i K (a ⊗ δ₂ b)`
(`NovikovModule.kernelMap_kernelProduct_sub_kernelProduct_kernelMap_kernelMap_of_mem_gradeBy`).
If `k` shifts the total degree by `ε - 1`, where `ε` is the degree shift of the products, then on
cocycles `a`, `b` of degrees `i`, `j` the two composites differ by a coboundary of degree
`i + j + ε`, by
`NovikovModule.kernelMap_kernelProduct_sub_kernelProduct_kernelMap_kernelMap_mem_coboundaries`.
So whenever `φ₀ (a ⋆ b)` and `φ₁ a ⋆' φ₂ b` are cocycles, they have the same cohomology class: on
cohomology, the continuation maps intertwine the two products. The kernel identity itself, and
the potential bounds of the kernels, which come from the energy estimate, remain hypotheses here:
they are the geometric input from the compactified moduli spaces.

## Main results

* `NovikovModule.kernelMap_kernelProduct_sub_kernelProduct_kernelMap_kernelMap`: a kernel
  homotopy between the two composite kernels gives a chain homotopy between applying a map after
  the product and applying maps before it.
* `NovikovModule.kernelMap_kernelProduct_sub_kernelProduct_kernelMap_kernelMap_of_mem_gradeBy`:
  the same homotopy for the Koszul differential of the tensor product, with its sign.
* `NovikovModule.kernelMap_kernelProduct_sub_kernelProduct_kernelMap_kernelMap_mem_coboundaries`:
  on cocycles the two composites differ by a coboundary.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the pair-of-pants product and its compatibility with continuation maps.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
-/

public section

noncomputable section

namespace TauCeti

namespace NovikovModule

variable {R S₁ S₂ S₀ T₁ T₂ T₀ : Type*} [CommRing R]
  {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ} {F₀ : S₀ → ℝ} {G₁ : T₁ → ℝ} {G₂ : T₂ → ℝ} {G₀ : T₀ → ℝ}
  {C C' C₁ C₂ C₀ Ck Cδ : ℝ}
  {n : S₁ → S₂ → S₀ → R} {n' : T₁ → T₂ → T₀ → R}
  {φ₁ : S₁ → T₁ → R} {φ₂ : S₂ → T₂ → R} {φ₀ : S₀ → T₀ → R}
  {k : S₁ × S₂ → T₀ → R} {δ₀ : T₀ → T₀ → R}
  (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
  (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)
  (hn' : ∀ t₁ t₂ t₀, n' t₁ t₂ t₀ ≠ 0 → G₀ t₀ ≤ G₁ t₁ + G₂ t₂ + C')
  (hfin' : ∀ t₁ t₂, n' t₁ t₂ ∈ NovikovModule R G₀)
  (hφ₁ : ∀ p t, φ₁ p t ≠ 0 → G₁ t ≤ F₁ p + C₁) (hφ₁fin : ∀ p, φ₁ p ∈ NovikovModule R G₁)
  (hφ₂ : ∀ p t, φ₂ p t ≠ 0 → G₂ t ≤ F₂ p + C₂) (hφ₂fin : ∀ p, φ₂ p ∈ NovikovModule R G₂)
  (hφ₀ : ∀ p t, φ₀ p t ≠ 0 → G₀ t ≤ F₀ p + C₀) (hφ₀fin : ∀ p, φ₀ p ∈ NovikovModule R G₀)
  (hk : ∀ (q : S₁ × S₂) t₀, k q t₀ ≠ 0 → G₀ t₀ ≤ F₁ q.1 + F₂ q.2 + Ck)
  (hkfin : ∀ q, k q ∈ NovikovModule R G₀)
  (hδ₀ : ∀ t t', δ₀ t t' ≠ 0 → G₀ t' ≤ G₀ t + Cδ) (hδ₀fin : ∀ t, δ₀ t ∈ NovikovModule R G₀)

/-- **Continuation up to homotopy.** Let `n` and `n'` be the product kernels of `⋆` and `⋆'`, let
`φ₁`, `φ₂`, `φ₀` be kernels from the generators of the inputs and output of `⋆` to those of `⋆'`,
let `δ₀` be a kernel on the output generators of `⋆'`, and let `D` be a kernel on the pairs of
input generators of `⋆`. If a kernel `k` is a kernel homotopy,

`∑ₚ n(p₁, p₂, p) φ₀(p, t₀) - ∑_{t₁, t₂} φ₁(p₁, t₁) φ₂(p₂, t₂) n'(t₁, t₂, t₀) =
  (k δ₀ + D k)(q, t₀)`

for `q = (p₁, p₂)`, then its kernel map `K` is a homotopy between the two composites: for
`x = a ⊗ b`, `φ₀ (a ⋆ b) - φ₁ a ⋆' φ₂ b = δ₀ (K x) + K (D x)`. -/
theorem kernelMap_kernelProduct_sub_kernelProduct_kernelMap_kernelMap
    {D : S₁ × S₂ → S₁ × S₂ → R} {CD : ℝ}
    (hD : ∀ q q', D q q' ≠ 0 → F₁ q'.1 + F₂ q'.2 ≤ F₁ q.1 + F₂ q.2 + CD)
    (hDfin : ∀ q, D q ∈ NovikovModule R fun q' : S₁ × S₂ => F₁ q'.1 + F₂ q'.2)
    (hcont : ∀ (q : S₁ × S₂) t₀,
      kernelComp (fun q : S₁ × S₂ => n q.1 q.2) φ₀ q t₀ -
          kernelComp (kernelTensor φ₁ φ₂) (fun t : T₁ × T₂ => n' t.1 t.2) q t₀ =
        kernelComp k δ₀ q t₀ + kernelComp D k q t₀)
    (a : NovikovModule R F₁) (b : NovikovModule R F₂) :
    kernelMap hφ₀ hφ₀fin (kernelProduct hn hfin a b) -
        kernelProduct hn' hfin' (kernelMap hφ₁ hφ₁fin a) (kernelMap hφ₂ hφ₂fin b) =
      kernelMap hδ₀ hδ₀fin (kernelMap hk hkfin (tensor a b)) +
        kernelMap hk hkfin (kernelMap hD hDfin (tensor a b)) := by
  -- The two product kernels, read as one-input kernels on pairs of generators.
  have hN (q : S₁ × S₂) (p₀ : S₀) (h : n q.1 q.2 p₀ ≠ 0) : F₀ p₀ ≤ F₁ q.1 + F₂ q.2 + C :=
    hn q.1 q.2 p₀ h
  have hN' (t : T₁ × T₂) (t₀ : T₀) (h : n' t.1 t.2 t₀ ≠ 0) : G₀ t₀ ≤ G₁ t.1 + G₂ t.2 + C' :=
    hn' t.1 t.2 t₀ h
  -- The tensor product of the input kernels is supported.
  have hΦ (q : S₁ × S₂) (t : T₁ × T₂) (h : kernelTensor φ₁ φ₂ q t ≠ 0) :
      G₁ t.1 + G₂ t.2 ≤ F₁ q.1 + F₂ q.2 + (C₁ + C₂) :=
    potential_le_of_kernelTensor_ne_zero hφ₁ hφ₂ h
  have hΦfin := kernelTensor_mem hφ₁fin hφ₂fin
  -- The two composite kernels are supported.
  have hA (q : S₁ × S₂) (t₀ : T₀)
      (h : kernelComp (fun q : S₁ × S₂ => n q.1 q.2) φ₀ q t₀ ≠ 0) :
      G₀ t₀ ≤ F₁ q.1 + F₂ q.2 + (C + C₀) := by
    linarith [potential_le_of_kernelComp_ne_zero (m := fun q : S₁ × S₂ => n q.1 q.2) (hN q)
      (hφ₀ · t₀) h]
  have hB (q : S₁ × S₂) (t₀ : T₀)
      (h : kernelComp (kernelTensor φ₁ φ₂) (fun t : T₁ × T₂ => n' t.1 t.2) q t₀ ≠ 0) :
      G₀ t₀ ≤ F₁ q.1 + F₂ q.2 + (C₁ + C₂ + C') := by
    linarith [potential_le_of_kernelComp_ne_zero (F₀ := fun t : T₁ × T₂ => G₁ t.1 + G₂ t.2)
      (hΦ q) (hN' · t₀) h]
  -- Both composites are kernel maps out of the completed tensor product.
  rw [kernelProduct_eq_kernelMap_tensor hn hfin hN (fun q => hfin q.1 q.2),
    kernelMap_kernelMap hN (fun q => hfin q.1 q.2) hφ₀ hφ₀fin hA
      (fun q => kernelComp_mem hφ₀ hφ₀fin (hfin q.1 q.2)),
    kernelProduct_eq_kernelMap_tensor hn' hfin' hN' (fun t => hfin' t.1 t.2),
    ← kernelMap_kernelTensor_tensor hφ₁ hφ₁fin hφ₂ hφ₂fin hΦ hΦfin,
    kernelMap_kernelMap hΦ hΦfin hN' (fun t => hfin' t.1 t.2) hB
      (fun q => kernelComp_mem hN' (fun t => hfin' t.1 t.2) (hΦfin q))]
  exact kernelMap_sub_kernelMap hA _ hB _ hk hkfin hD hDfin hδ₀ hδ₀fin hcont _

variable [DecidableEq S₁] [DecidableEq S₂] {d₁ : S₁ → ℤ} {δ₁ : S₁ → S₁ → R} {δ₂ : S₂ → S₂ → R}
  {E₁ E₂ : ℝ}
  (hδ₁ : ∀ p q, δ₁ p q ≠ 0 → F₁ q ≤ F₁ p + E₁) (hδ₁fin : ∀ p, δ₁ p ∈ NovikovModule R F₁)
  (hδ₂ : ∀ p q, δ₂ p q ≠ 0 → F₂ q ≤ F₂ p + E₂) (hδ₂fin : ∀ p, δ₂ p ∈ NovikovModule R F₂)

/-- **Continuation up to homotopy, with the Koszul sign.** Let `δ₁`, `δ₂` be kernels on the input
generators of `⋆`, `d₁` a degree function on the first input, and
`D = δ₁ ⊗ 1 + (-1)^(d₁) ⊗ δ₂` the tensor differential. If a kernel `k` is a kernel homotopy,

`∑ₚ n(p₁, p₂, p) φ₀(p, t₀) - ∑_{t₁, t₂} φ₁(p₁, t₁) φ₂(p₂, t₂) n'(t₁, t₂, t₀) =
  (k δ₀ + D k)(q, t₀)`

for `q = (p₁, p₂)`, then for `a` of degree `i` and any `b`, its kernel map `K` satisfies

`φ₀ (a ⋆ b) - φ₁ a ⋆' φ₂ b = δ₀ (K (a ⊗ b)) + K (δ₁ a ⊗ b) + (-1)^i K (a ⊗ δ₂ b)`. -/
theorem kernelMap_kernelProduct_sub_kernelProduct_kernelMap_kernelMap_of_mem_gradeBy
    (hcont : ∀ (q : S₁ × S₂) t₀,
      kernelComp (fun q : S₁ × S₂ => n q.1 q.2) φ₀ q t₀ -
          kernelComp (kernelTensor φ₁ φ₂) (fun t : T₁ × T₂ => n' t.1 t.2) q t₀ =
        kernelComp k δ₀ q t₀ + kernelComp (tensorDifferential d₁ δ₁ δ₂) k q t₀)
    {i : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ d₁ i) (b : NovikovModule R F₂) :
    kernelMap hφ₀ hφ₀fin (kernelProduct hn hfin a b) -
        kernelProduct hn' hfin' (kernelMap hφ₁ hφ₁fin a) (kernelMap hφ₂ hφ₂fin b) =
      kernelMap hδ₀ hδ₀fin (kernelMap hk hkfin (tensor a b)) +
        kernelMap hk hkfin (tensor (kernelMap hδ₁ hδ₁fin a) b) +
        (i.negOnePow : R) • kernelMap hk hkfin (tensor a (kernelMap hδ₂ hδ₂fin b)) := by
  -- The tensor differential is supported.
  have hD (q q' : S₁ × S₂) (h : tensorDifferential d₁ δ₁ δ₂ q q' ≠ 0) :=
    potential_le_of_tensorDifferential_ne_zero hδ₁ hδ₂ h
  have hDfin := tensorDifferential_mem (d₁ := d₁) hδ₁fin hδ₂fin
  rw [kernelMap_kernelProduct_sub_kernelProduct_kernelMap_kernelMap hn hfin hn' hfin' hφ₁ hφ₁fin
      hφ₂ hφ₂fin hφ₀ hφ₀fin hk hkfin hδ₀ hδ₀fin hD hDfin hcont,
    kernelMap_tensorDifferential_tensor hδ₁ hδ₁fin hδ₂ hδ₂fin hD hDfin ha]
  simp only [map_add, map_smul, add_assoc]

include hk hkfin in
/-- **Continuation on cocycles.** Under the kernel homotopy of
`NovikovModule.kernelMap_kernelProduct_sub_kernelProduct_kernelMap_kernelMap_of_mem_gradeBy`, if
the homotopy kernel `k` shifts the total degree by `ε - 1`, then for cocycles `a` of degree `i`
and `b` of degree `j` the difference `φ₀ (a ⋆ b) - φ₁ a ⋆' φ₂ b` is a coboundary of degree
`i + j + ε`. -/
theorem kernelMap_kernelProduct_sub_kernelProduct_kernelMap_kernelMap_mem_coboundaries
    {d₂ : S₂ → ℤ} {e₀ : T₀ → ℤ} {ε : ℤ}
    (hkd : ∀ (q : S₁ × S₂) t₀, k q t₀ ≠ 0 → e₀ t₀ = d₁ q.1 + d₂ q.2 + ε - 1)
    (hcont : ∀ (q : S₁ × S₂) t₀,
      kernelComp (fun q : S₁ × S₂ => n q.1 q.2) φ₀ q t₀ -
          kernelComp (kernelTensor φ₁ φ₂) (fun t : T₁ × T₂ => n' t.1 t.2) q t₀ =
        kernelComp k δ₀ q t₀ + kernelComp (tensorDifferential d₁ δ₁ δ₂) k q t₀)
    {i j : ℤ} {a : NovikovModule R F₁}
    (ha : a ∈ (kernelMap hδ₁ hδ₁fin).cocycles (gradeBy R F₁ d₁) i)
    {b : NovikovModule R F₂} (hb : b ∈ (kernelMap hδ₂ hδ₂fin).cocycles (gradeBy R F₂ d₂) j) :
    kernelMap hφ₀ hφ₀fin (kernelProduct hn hfin a b) -
        kernelProduct hn' hfin' (kernelMap hφ₁ hφ₁fin a) (kernelMap hφ₂ hφ₂fin b) ∈
      (kernelMap hδ₀ hδ₀fin).coboundaries (gradeBy R G₀ e₀) (i + j + ε) := by
  rw [LinearMap.mem_cocycles_iff] at ha hb
  rw [kernelMap_kernelProduct_sub_kernelProduct_kernelMap_kernelMap_of_mem_gradeBy hn hfin hn'
      hfin' hφ₁ hφ₁fin hφ₂ hφ₂fin hφ₀ hφ₀fin hk hkfin hδ₀ hδ₀fin hδ₁ hδ₁fin hδ₂ hδ₂fin hcont ha.2,
    ha.1, hb.1]
  simp only [map_zero, LinearMap.zero_apply, smul_zero, add_zero]
  refine LinearMap.mem_coboundaries_iff.2 ⟨_, ?_, rfl⟩
  have hdeg := kernelMap_mem_gradeBy hk hkfin (d₀ := e₀) (ε := ε - 1)
    (fun q t₀ h => by rw [hkd q t₀ h, add_sub_assoc]) (tensor_mem_gradeBy ha.2 hb.2)
  rwa [← add_sub_assoc] at hdeg

end NovikovModule

end TauCeti

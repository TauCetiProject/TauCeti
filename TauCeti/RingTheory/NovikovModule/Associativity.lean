/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Tensor

/-!
# Associativity homotopies of supported kernel products

Let `⋆` denote products of completed combinations given by supported product kernels
(`TauCeti.NovikovModule.kernelProduct`). There are two ways of multiplying three completed
combinations `a`, `b` and `c`: first `a ⋆ b`, through intermediate generators `t` with a kernel
`n(p₁, p₂, t)`, and then `(a ⋆ b) ⋆' c` with a kernel `n'(t, p₃, p₀)`; or first `b ⋆'' c`,
through intermediate generators `u` with a kernel `m(p₂, p₃, u)`, and then `a ⋆''' (b ⋆'' c)`
with a kernel `m'(p₁, u, p₀)`. Both are kernel maps out of the completed triple tensor product
`(a ⊗ b) ⊗ c`, with the kernels `∑ₜ n(p₁, p₂, t) n'(t, p₃, ·)` and
`∑ᵤ m(p₂, p₃, u) m'(p₁, u, ·)` (`NovikovModule.kernelProduct_kernelProduct_left`,
`NovikovModule.kernelProduct_kernelProduct_right`).

For the pair-of-pants product in Floer theory these two kernels count the two kinds of broken
configurations at the ends of a one-parameter family of four-punctured spheres. The other
codimension-one boundary points of the one-dimensional moduli spaces are breakings of a Floer
cylinder at one of the four ends, so the count of all boundary points gives the kernel identity

`∑ₜ n(p₁, p₂, t) n'(t, p₃, p₀) - ∑ᵤ m(p₂, p₃, u) m'(p₁, u, p₀) = (k δ₀ + D k)(q, p₀)`

for the kernel `k(q, p₀)` counting rigid elements of the family, the output differential `δ₀`
and the differential `D` of the triple tensor product, at every triple `q = ((p₁, p₂), p₃)`.
This file turns that identity into the chain homotopy

`(a ⋆ b) ⋆' c - a ⋆''' (b ⋆'' c) = δ₀ (K x) + K (D x)`,  `x = (a ⊗ b) ⊗ c`,

between the two products, where `K` is the kernel map of `k` (of degree `-1` in the Floer
setting), for arbitrary completed combinations: both sides are infinite sums
(`NovikovModule.kernelProduct_kernelProduct_sub_kernelProduct_kernelProduct`). When `D` is the
Koszul tensor differential `(δ₁ ⊗ 1 + (-1)^(d₁) ⊗ δ₂) ⊗ 1 + (-1)^(d₁ + d₂) ⊗ δ₃` and `a`, `b`
are homogeneous of degrees `i`, `j`, the second term expands to

`K ((δ₁ a ⊗ b) ⊗ c) + (-1)^i K ((a ⊗ δ₂ b) ⊗ c) + (-1)^(i + j) K ((a ⊗ b) ⊗ δ₃ c)`

(`NovikovModule.kernelProduct_kernelProduct_sub_kernelProduct_kernelProduct_of_mem_gradeBy`).
In particular, if `δ₁ a`, `δ₂ b` and `δ₃ c` vanish, the two products differ by the coboundary
`δ₀ (K ((a ⊗ b) ⊗ c))`. The kernel identity itself, and the potential
bounds of the kernels, which come from the energy estimate, remain hypotheses here: they are
the geometric input from the compactified moduli spaces.

## Main results

* `NovikovModule.kernelProduct_kernelProduct_left`,
  `NovikovModule.kernelProduct_kernelProduct_right`: the two nested products are kernel
  maps out of the triple tensor product.
* `NovikovModule.kernelProduct_kernelProduct_sub_kernelProduct_kernelProduct`: a kernel homotopy
  between the two nested product kernels gives a chain homotopy between the products.
* `NovikovModule.kernelProduct_kernelProduct_sub_kernelProduct_kernelProduct_of_mem_gradeBy`: the
  same homotopy for the Koszul differential of the triple tensor product, with its signs.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the associativity of the pair-of-pants product.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
-/

public section

noncomputable section

namespace TauCeti

namespace NovikovModule

variable {R S₁ S₂ S₃ S₀ S₁₂ S₂₃ : Type*}
  {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ} {F₃ : S₃ → ℝ} {F₀ : S₀ → ℝ} {F₁₂ : S₁₂ → ℝ} {F₂₃ : S₂₃ → ℝ}

section CommSemiring

variable [CommSemiring R] {C C' C'' : ℝ}

/-- **A product with a product in its first input.** For product kernels `n` from `S₁ × S₂` to
`S₁₂` and `n'` from `S₁₂ × S₃` to `S₀`, the product `(a ⋆ b) ⋆' c` is the kernel map, out of the
triple tensor product, of the kernel `∑ₜ n(p₁, p₂, t) n'(t, p₃, ·)`. The potential bound of this
kernel may have any constant. -/
theorem kernelProduct_kernelProduct_left {n : S₁ → S₂ → S₁₂ → R} {n' : S₁₂ → S₃ → S₀ → R}
    (hn : ∀ p₁ p₂ t, n p₁ p₂ t ≠ 0 → F₁₂ t ≤ F₁ p₁ + F₂ p₂ + C)
    (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₁₂)
    (hn' : ∀ t p₃ p₀, n' t p₃ p₀ ≠ 0 → F₀ p₀ ≤ F₁₂ t + F₃ p₃ + C')
    (hfin' : ∀ t p₃, n' t p₃ ∈ NovikovModule R F₀)
    (hN : ∀ (q : (S₁ × S₂) × S₃) p₀, ∑ᶠ t, n q.1.1 q.1.2 t * n' t q.2 p₀ ≠ 0 →
      F₀ p₀ ≤ F₁ q.1.1 + F₂ q.1.2 + F₃ q.2 + C'')
    (hNfin : ∀ q : (S₁ × S₂) × S₃,
      (fun p₀ => ∑ᶠ t, n q.1.1 q.1.2 t * n' t q.2 p₀) ∈ NovikovModule R F₀)
    (a : NovikovModule R F₁) (b : NovikovModule R F₂) (c : NovikovModule R F₃) :
    kernelProduct hn' hfin' (kernelProduct hn hfin a b) c =
      kernelMap hN hNfin (tensor (tensor a b) c) := by
  have hn₁₂ (q : S₁ × S₂) (t : S₁₂) (h : n q.1 q.2 t ≠ 0) : F₁₂ t ≤ F₁ q.1 + F₂ q.2 + C :=
    hn q.1 q.2 t h
  have hn'₃ (p₃ : S₃) (t : S₁₂) (p₀ : S₀) (h : n' t p₃ p₀ ≠ 0) : F₀ p₀ ≤ F₁₂ t + (F₃ p₃ + C') := by
    linarith [hn' t p₃ p₀ h]
  rw [kernelProduct_eq_kernelMap_tensor hn hfin hn₁₂ (fun q => hfin q.1 q.2),
    kernelProduct_kernelMap_left hn' hfin' hn₁₂ (fun q => hfin q.1 q.2) (C'' := C'')
      (fun q p₃ p₀ h => hN (q, p₃) p₀ (by rwa [kernelComp_apply] at h))
      (fun q p₃ => kernelComp_mem (hn'₃ p₃) (hfin' · p₃) (hfin q.1 q.2))]
  ext p₀
  simp only [kernelProduct_apply_val, kernelMap_apply_val, tensor_apply_val, kernelComp_apply]

/-- **A product with a product in its second input.** For product kernels `m` from `S₂ × S₃` to
`S₂₃` and `m'` from `S₁ × S₂₃` to `S₀`, the product `a ⋆' (b ⋆ c)` is the kernel map, out of the
triple tensor product `(a ⊗ b) ⊗ c`, of the kernel `∑ᵤ m(p₂, p₃, u) m'(p₁, u, ·)`. The potential
bound of this kernel may have any constant. -/
theorem kernelProduct_kernelProduct_right {m : S₂ → S₃ → S₂₃ → R} {m' : S₁ → S₂₃ → S₀ → R}
    (hm : ∀ p₂ p₃ u, m p₂ p₃ u ≠ 0 → F₂₃ u ≤ F₂ p₂ + F₃ p₃ + C)
    (hfin : ∀ p₂ p₃, m p₂ p₃ ∈ NovikovModule R F₂₃)
    (hm' : ∀ p₁ u p₀, m' p₁ u p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂₃ u + C')
    (hfin' : ∀ p₁ u, m' p₁ u ∈ NovikovModule R F₀)
    (hM : ∀ (q : (S₁ × S₂) × S₃) p₀, ∑ᶠ u, m q.1.2 q.2 u * m' q.1.1 u p₀ ≠ 0 →
      F₀ p₀ ≤ F₁ q.1.1 + F₂ q.1.2 + F₃ q.2 + C'')
    (hMfin : ∀ q : (S₁ × S₂) × S₃,
      (fun p₀ => ∑ᶠ u, m q.1.2 q.2 u * m' q.1.1 u p₀) ∈ NovikovModule R F₀)
    (a : NovikovModule R F₁) (b : NovikovModule R F₂) (c : NovikovModule R F₃) :
    kernelProduct hm' hfin' a (kernelProduct hm hfin b c) =
      kernelMap hM hMfin (tensor (tensor a b) c) := by
  have hm₂₃ (q : S₂ × S₃) (u : S₂₃) (h : m q.1 q.2 u ≠ 0) : F₂₃ u ≤ F₂ q.1 + F₃ q.2 + C :=
    hm q.1 q.2 u h
  have hm'₁ (p₁ : S₁) (u : S₂₃) (p₀ : S₀) (h : m' p₁ u p₀ ≠ 0) :
      F₀ p₀ ≤ F₂₃ u + (F₁ p₁ + C') := by
    linarith [hm' p₁ u p₀ h]
  rw [kernelProduct_eq_kernelMap_tensor hm hfin hm₂₃ (fun q => hfin q.1 q.2),
    kernelProduct_kernelMap_right hm' hfin' hm₂₃ (fun q => hfin q.1 q.2) (C'' := C'')
      (fun p₁ q p₀ h => by
        linarith [hM ((p₁, q.1), q.2) p₀ (by rwa [kernelComp_apply] at h)])
      (fun p₁ q => kernelComp_mem (hm'₁ p₁) (hfin' p₁) (hfin q.1 q.2))]
  ext p₀
  -- Reindex the sum over `S₁ × (S₂ × S₃)` by the associator of the triple product.
  rw [kernelProduct_apply_val, kernelMap_apply_val,
    ← finsum_comp_equiv (Equiv.prodAssoc S₁ S₂ S₃)]
  refine finsum_congr fun q => ?_
  simp only [Equiv.prodAssoc_apply, tensor_apply_val, kernelComp_apply]
  ring

end CommSemiring

section CommRing

variable [CommRing R] {C₁ C₂ C₃ C₄ Ck C₀ : ℝ}
  {n : S₁ → S₂ → S₁₂ → R} {n' : S₁₂ → S₃ → S₀ → R}
  {m : S₂ → S₃ → S₂₃ → R} {m' : S₁ → S₂₃ → S₀ → R}
  {k : (S₁ × S₂) × S₃ → S₀ → R} {δ₀ : S₀ → S₀ → R}
  (hn : ∀ p₁ p₂ t, n p₁ p₂ t ≠ 0 → F₁₂ t ≤ F₁ p₁ + F₂ p₂ + C₁)
  (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₁₂)
  (hn' : ∀ t p₃ p₀, n' t p₃ p₀ ≠ 0 → F₀ p₀ ≤ F₁₂ t + F₃ p₃ + C₂)
  (hfin' : ∀ t p₃, n' t p₃ ∈ NovikovModule R F₀)
  (hm : ∀ p₂ p₃ u, m p₂ p₃ u ≠ 0 → F₂₃ u ≤ F₂ p₂ + F₃ p₃ + C₃)
  (hmfin : ∀ p₂ p₃, m p₂ p₃ ∈ NovikovModule R F₂₃)
  (hm' : ∀ p₁ u p₀, m' p₁ u p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂₃ u + C₄)
  (hmfin' : ∀ p₁ u, m' p₁ u ∈ NovikovModule R F₀)
  (hk : ∀ (q : (S₁ × S₂) × S₃) p₀, k q p₀ ≠ 0 → F₀ p₀ ≤ F₁ q.1.1 + F₂ q.1.2 + F₃ q.2 + Ck)
  (hkfin : ∀ q, k q ∈ NovikovModule R F₀)
  (hδ₀ : ∀ p p₀, δ₀ p p₀ ≠ 0 → F₀ p₀ ≤ F₀ p + C₀) (hδ₀fin : ∀ p, δ₀ p ∈ NovikovModule R F₀)

/-- **Associativity up to homotopy.** Let `n`, `n'` and `m`, `m'` be the product kernels of the
two nested products `(a ⋆ b) ⋆' c` and `a ⋆''' (b ⋆'' c)`, let `δ₀` be a kernel on the output
generators, and let `D` be a kernel on the triple tensor product. If a kernel `k` from the triple
tensor product to the output is a kernel homotopy,

`∑ₜ n(p₁, p₂, t) n'(t, p₃, p₀) - ∑ᵤ m(p₂, p₃, u) m'(p₁, u, p₀) = (k δ₀ + D k)(q, p₀)`

for `q = ((p₁, p₂), p₃)`, then its kernel map `K` is a homotopy between the two products: for
`x = (a ⊗ b) ⊗ c`, `(a ⋆ b) ⋆' c - a ⋆''' (b ⋆'' c) = δ₀ (K x) + K (D x)`. -/
theorem kernelProduct_kernelProduct_sub_kernelProduct_kernelProduct
    {D : (S₁ × S₂) × S₃ → (S₁ × S₂) × S₃ → R} {CD : ℝ}
    (hD : ∀ q q', D q q' ≠ 0 →
      F₁ q'.1.1 + F₂ q'.1.2 + F₃ q'.2 ≤ F₁ q.1.1 + F₂ q.1.2 + F₃ q.2 + CD)
    (hDfin : ∀ q, D q ∈ NovikovModule R fun q' : (S₁ × S₂) × S₃ => F₁ q'.1.1 + F₂ q'.1.2 + F₃ q'.2)
    (hassoc : ∀ (q : (S₁ × S₂) × S₃) p₀,
      ∑ᶠ t, n q.1.1 q.1.2 t * n' t q.2 p₀ - ∑ᶠ u, m q.1.2 q.2 u * m' q.1.1 u p₀ =
        kernelComp k δ₀ q p₀ + kernelComp D k q p₀)
    (a : NovikovModule R F₁) (b : NovikovModule R F₂) (c : NovikovModule R F₃) :
    kernelProduct hn' hfin' (kernelProduct hn hfin a b) c -
        kernelProduct hm' hmfin' a (kernelProduct hm hmfin b c) =
      kernelMap hδ₀ hδ₀fin (kernelMap hk hkfin (tensor (tensor a b) c)) +
        kernelMap hk hkfin (kernelMap hD hDfin (tensor (tensor a b) c)) := by
  -- Potential bounds and completed outputs of the two nested product kernels.
  have hN (q : (S₁ × S₂) × S₃) (p₀ : S₀) (h : ∑ᶠ t, n q.1.1 q.1.2 t * n' t q.2 p₀ ≠ 0) :
      F₀ p₀ ≤ F₁ q.1.1 + F₂ q.1.2 + F₃ q.2 + (C₁ + C₂) := by
    linarith [potential_le_of_kernelComp_ne_zero (m := fun q : (S₁ × S₂) × S₃ => n q.1.1 q.1.2)
      (m' := (n' · q.2)) (C' := F₃ q.2 + C₂) (hn q.1.1 q.1.2)
      (fun t h => by linarith [hn' t q.2 p₀ h]) (by rwa [kernelComp_apply])]
  have hNfin (q : (S₁ × S₂) × S₃) :
      (fun p₀ => ∑ᶠ t, n q.1.1 q.1.2 t * n' t q.2 p₀) ∈ NovikovModule R F₀ := by
    convert kernelComp_mem (m := fun q : (S₁ × S₂) × S₃ => n q.1.1 q.1.2) (C' := F₃ q.2 + C₂)
      (fun t p₀ h => by linarith [hn' t q.2 p₀ h]) (hfin' · q.2) (hfin q.1.1 q.1.2) using 1
    ext p₀
    rw [kernelComp_apply]
  have hM (q : (S₁ × S₂) × S₃) (p₀ : S₀) (h : ∑ᶠ u, m q.1.2 q.2 u * m' q.1.1 u p₀ ≠ 0) :
      F₀ p₀ ≤ F₁ q.1.1 + F₂ q.1.2 + F₃ q.2 + (C₃ + C₄) := by
    linarith [potential_le_of_kernelComp_ne_zero (m := fun q : (S₁ × S₂) × S₃ => m q.1.2 q.2)
      (m' := m' q.1.1) (C' := F₁ q.1.1 + C₄) (hm q.1.2 q.2)
      (fun u h => by linarith [hm' q.1.1 u p₀ h]) (by rwa [kernelComp_apply])]
  have hMfin (q : (S₁ × S₂) × S₃) :
      (fun p₀ => ∑ᶠ u, m q.1.2 q.2 u * m' q.1.1 u p₀) ∈ NovikovModule R F₀ := by
    convert kernelComp_mem (m := fun q : (S₁ × S₂) × S₃ => m q.1.2 q.2) (C' := F₁ q.1.1 + C₄)
      (fun u p₀ h => by linarith [hm' q.1.1 u p₀ h]) (hmfin' q.1.1) (hmfin q.1.2 q.2) using 1
    ext p₀
    rw [kernelComp_apply]
  rw [kernelProduct_kernelProduct_left hn hfin hn' hfin' hN hNfin,
    kernelProduct_kernelProduct_right hm hmfin hm' hmfin' hM hMfin]
  exact kernelMap_sub_kernelMap hN hNfin hM hMfin hk hkfin hD hDfin hδ₀ hδ₀fin hassoc _

/-- **Associativity up to homotopy, with the Koszul signs.** Let `δ₁`, `δ₂`, `δ₃` be kernels on
the three input generators and `d₁`, `d₂` degree functions on the first two, and let
`D = (δ₁ ⊗ 1 + (-1)^(d₁) ⊗ δ₂) ⊗ 1 + (-1)^(d₁ + d₂) ⊗ δ₃` be the tensor differential of the
triple tensor product. If a kernel `k` is a kernel homotopy,

`∑ₜ n(p₁, p₂, t) n'(t, p₃, p₀) - ∑ᵤ m(p₂, p₃, u) m'(p₁, u, p₀) = (k δ₀ + D k)(q, p₀)`

for `q = ((p₁, p₂), p₃)`, then for `a` of degree `i`, `b` of degree `j` and any `c`, its kernel
map `K` satisfies

`(a ⋆ b) ⋆' c - a ⋆''' (b ⋆'' c) = δ₀ (K ((a ⊗ b) ⊗ c)) + K ((δ₁ a ⊗ b) ⊗ c) +
  (-1)^i K ((a ⊗ δ₂ b) ⊗ c) + (-1)^(i + j) K ((a ⊗ b) ⊗ δ₃ c)`. -/
theorem kernelProduct_kernelProduct_sub_kernelProduct_kernelProduct_of_mem_gradeBy
    [DecidableEq S₁] [DecidableEq S₂] [DecidableEq S₃]
    {d₁ : S₁ → ℤ} {d₂ : S₂ → ℤ} {δ₁ : S₁ → S₁ → R} {δ₂ : S₂ → S₂ → R} {δ₃ : S₃ → S₃ → R}
    {E₁ E₂ E₃ : ℝ}
    (hδ₁ : ∀ p q, δ₁ p q ≠ 0 → F₁ q ≤ F₁ p + E₁) (hδ₁fin : ∀ p, δ₁ p ∈ NovikovModule R F₁)
    (hδ₂ : ∀ p q, δ₂ p q ≠ 0 → F₂ q ≤ F₂ p + E₂) (hδ₂fin : ∀ p, δ₂ p ∈ NovikovModule R F₂)
    (hδ₃ : ∀ p q, δ₃ p q ≠ 0 → F₃ q ≤ F₃ p + E₃) (hδ₃fin : ∀ p, δ₃ p ∈ NovikovModule R F₃)
    (hassoc : ∀ (q : (S₁ × S₂) × S₃) p₀,
      ∑ᶠ t, n q.1.1 q.1.2 t * n' t q.2 p₀ - ∑ᶠ u, m q.1.2 q.2 u * m' q.1.1 u p₀ =
        kernelComp k δ₀ q p₀ +
          kernelComp (tensorDifferential (fun q : S₁ × S₂ => d₁ q.1 + d₂ q.2)
            (tensorDifferential d₁ δ₁ δ₂) δ₃) k q p₀)
    {i j : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ d₁ i)
    {b : NovikovModule R F₂} (hb : b ∈ gradeBy R F₂ d₂ j) (c : NovikovModule R F₃) :
    kernelProduct hn' hfin' (kernelProduct hn hfin a b) c -
        kernelProduct hm' hmfin' a (kernelProduct hm hmfin b c) =
      kernelMap hδ₀ hδ₀fin (kernelMap hk hkfin (tensor (tensor a b) c)) +
        kernelMap hk hkfin (tensor (tensor (kernelMap hδ₁ hδ₁fin a) b) c) +
        (i.negOnePow : R) • kernelMap hk hkfin (tensor (tensor a (kernelMap hδ₂ hδ₂fin b)) c) +
        ((i + j).negOnePow : R) •
          kernelMap hk hkfin (tensor (tensor a b) (kernelMap hδ₃ hδ₃fin c)) := by
  -- The tensor differentials of the double and of the triple tensor product are supported.
  have hD₁₂ (p q : S₁ × S₂) (h : tensorDifferential d₁ δ₁ δ₂ p q ≠ 0) :=
    potential_le_of_tensorDifferential_ne_zero hδ₁ hδ₂ h
  have hD₁₂fin := tensorDifferential_mem (d₁ := d₁) hδ₁fin hδ₂fin
  have hD (p q : (S₁ × S₂) × S₃) (h : tensorDifferential (fun q : S₁ × S₂ => d₁ q.1 + d₂ q.2)
      (tensorDifferential d₁ δ₁ δ₂) δ₃ p q ≠ 0) :=
    potential_le_of_tensorDifferential_ne_zero hD₁₂ hδ₃ h
  have hDfin := tensorDifferential_mem (d₁ := fun q : S₁ × S₂ => d₁ q.1 + d₂ q.2) hD₁₂fin hδ₃fin
  rw [kernelProduct_kernelProduct_sub_kernelProduct_kernelProduct hn hfin hn' hfin' hm hmfin hm'
      hmfin' hk hkfin hδ₀ hδ₀fin hD hDfin hassoc,
    kernelMap_tensorDifferential_tensor hD₁₂ hD₁₂fin hδ₃ hδ₃fin hD hDfin (tensor_mem_gradeBy ha hb),
    kernelMap_tensorDifferential_tensor hδ₁ hδ₁fin hδ₂ hδ₂fin hD₁₂ hD₁₂fin ha]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, add_assoc]

end CommRing

end NovikovModule

end TauCeti

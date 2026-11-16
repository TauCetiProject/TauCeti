/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Tensor
public import TauCeti.RingTheory.NovikovModule.Leibniz
public import TauCeti.RingTheory.NovikovModule.Trilinear
public import TauCeti.Algebra.Homology.SquareZero.Graded
import Mathlib.Tactic.LinearCombination

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
`δ₀ (K ((a ⊗ b) ⊗ c))`; when `K` lowers degree by one relative to the two products, this is a
coboundary in the degree of the output
(`NovikovModule.kernelProduct_kernelProduct_sub_kernelProduct_kernelProduct_mem_coboundaries`).
Hence, once the four products obey the Leibniz rule, the products they induce on degree-wise
cohomology (`LinearMap.cohomologyProduct`) are associative,
`([a] ⋆ [b]) ⋆' [c] = [a] ⋆''' ([b] ⋆'' [c])`
(`NovikovModule.cohomologyProduct_kernelProduct_assoc`).
The kernel identity itself, and the potential bounds of the kernels, which come from the energy
estimate, remain hypotheses here: they are the geometric input from the compactified moduli
spaces.

On finite unions of torsors with invariant kernels, products are given by matrices of Novikov
series relative to reference generators (`NovikovModule.novikovProductOfMatrix`), and so is the
homotopy: a family `K` of Novikov series indexed by three input orbits and one output orbit
defines a trilinear map over the Novikov ring (`NovikovModule.novikovTrilinearOfMatrix`), given
in the reference coordinates by `K(a, b, c)ₗ = ∑ᵢ ∑ⱼ ∑ₖ aᵢ bⱼ cₖ Kᵢⱼₖₗ`. For the matrices `Q`,
`Q'` of `(a ⋆ b) ⋆' c`, the matrices `T`, `T'` of `a ⋆''' (b ⋆'' c)`, and matrices `D₁`, `D₂`,
`D₃`, `D₀` of maps on the three inputs and the output, the kernel identity becomes the identity

`∑ₜ Qᵢⱼₜ Q'ₜₖₗ - ∑ᵤ Tⱼₖᵤ T'ᵢᵤₗ = ∑ₘ Kᵢⱼₖₘ D₀ₘₗ + ∑ₘ D₁ᵢₘ Kₘⱼₖₗ + (-1)^(d₁ (r₁ i)) ∑ₘ D₂ⱼₘ Kᵢₘₖₗ +
  (-1)^(d₁ (r₁ i) + d₂ (r₂ j)) ∑ₘ D₃ₖₘ Kᵢⱼₘₗ`

between finite sums of Novikov series. It implies the chain homotopy
`(a ⋆ b) ⋆' c - a ⋆''' (b ⋆'' c) = D₀ K(a, b, c) + K(D₁ a, b, c) + (-1)^i K(a, D₂ b, c) +
(-1)^(i + j) K(a, b, D₃ c)` for `a` of degree `i` and `b` of degree `j`
(`NovikovModule.novikovProductOfMatrix_assoc_sub_eq_add`), provided degrees change by even
amounts within each orbit, so that the signs only depend on the orbits. This is the form in which
counts indexed by classes of a period group enter.

## Main results

* `NovikovModule.kernelProduct_kernelProduct_left`,
  `NovikovModule.kernelProduct_kernelProduct_right`: the two nested products are kernel
  maps out of the triple tensor product.
* `NovikovModule.kernelProduct_kernelProduct_sub_kernelProduct_kernelProduct`: a kernel homotopy
  between the two nested product kernels gives a chain homotopy between the products.
* `NovikovModule.kernelProduct_kernelProduct_sub_kernelProduct_kernelProduct_of_mem_gradeBy`: the
  same homotopy for the Koszul differential of the triple tensor product, with its signs.
* `NovikovModule.kernelProduct_kernelProduct_sub_kernelProduct_kernelProduct_mem_coboundaries`: on
  cocycles the two products differ by a coboundary.
* `NovikovModule.cohomologyProduct_kernelProduct_assoc`: the induced products on cohomology are
  associative.
* `NovikovModule.novikovProductOfMatrix_assoc_sub_eq_add`: the associativity homotopy for
  products of matrices, from the associativity identity between matrices.

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

section Cohomology

variable [DecidableEq S₁] [DecidableEq S₂] [DecidableEq S₃]
  {d₁ : S₁ → ℤ} {d₂ : S₂ → ℤ} {d₃ : S₃ → ℤ} {d₀ : S₀ → ℤ}
  {δ₁ : S₁ → S₁ → R} {δ₂ : S₂ → S₂ → R} {δ₃ : S₃ → S₃ → R} {E₁ E₂ E₃ : ℝ}
  (hδ₁ : ∀ p q, δ₁ p q ≠ 0 → F₁ q ≤ F₁ p + E₁) (hδ₁fin : ∀ p, δ₁ p ∈ NovikovModule R F₁)
  (hδ₂ : ∀ p q, δ₂ p q ≠ 0 → F₂ q ≤ F₂ p + E₂) (hδ₂fin : ∀ p, δ₂ p ∈ NovikovModule R F₂)
  (hδ₃ : ∀ p q, δ₃ p q ≠ 0 → F₃ q ≤ F₃ p + E₃) (hδ₃fin : ∀ p, δ₃ p ∈ NovikovModule R F₃)

include hk hkfin in
/-- **Associativity on cocycles.** Under the kernel homotopy of
`NovikovModule.kernelProduct_kernelProduct_sub_kernelProduct_kernelProduct_of_mem_gradeBy`, if the
homotopy kernel `k` shifts degree by `ε - 1`, then for cocycles `a`, `b`, `c` of degrees `i`, `j`,
`l` the difference `(a ⋆ b) ⋆' c - a ⋆''' (b ⋆'' c)` is a coboundary of degree `i + j + l + ε`. -/
theorem kernelProduct_kernelProduct_sub_kernelProduct_kernelProduct_mem_coboundaries {ε : ℤ}
    (hkd : ∀ q p₀, k q p₀ ≠ 0 → d₀ p₀ = d₁ q.1.1 + d₂ q.1.2 + d₃ q.2 + (ε - 1))
    (hassoc : ∀ (q : (S₁ × S₂) × S₃) p₀,
      ∑ᶠ t, n q.1.1 q.1.2 t * n' t q.2 p₀ - ∑ᶠ u, m q.1.2 q.2 u * m' q.1.1 u p₀ =
        kernelComp k δ₀ q p₀ +
          kernelComp (tensorDifferential (fun q : S₁ × S₂ => d₁ q.1 + d₂ q.2)
            (tensorDifferential d₁ δ₁ δ₂) δ₃) k q p₀)
    {i j l : ℤ} {a : NovikovModule R F₁}
    (ha : a ∈ (kernelMap hδ₁ hδ₁fin).cocycles (gradeBy R F₁ d₁) i)
    {b : NovikovModule R F₂} (hb : b ∈ (kernelMap hδ₂ hδ₂fin).cocycles (gradeBy R F₂ d₂) j)
    {c : NovikovModule R F₃} (hc : c ∈ (kernelMap hδ₃ hδ₃fin).cocycles (gradeBy R F₃ d₃) l) :
    kernelProduct hn' hfin' (kernelProduct hn hfin a b) c -
        kernelProduct hm' hmfin' a (kernelProduct hm hmfin b c) ∈
      (kernelMap hδ₀ hδ₀fin).coboundaries (gradeBy R F₀ d₀) (i + j + l + ε) := by
  rw [LinearMap.mem_cocycles_iff] at ha hb hc
  rw [kernelProduct_kernelProduct_sub_kernelProduct_kernelProduct_of_mem_gradeBy hn hfin hn' hfin'
      hm hmfin hm' hmfin' hk hkfin hδ₀ hδ₀fin hδ₁ hδ₁fin hδ₂ hδ₂fin hδ₃ hδ₃fin hassoc ha.2 hb.2 c,
    ha.1, hb.1, hc.1]
  simp only [map_zero, LinearMap.zero_apply, smul_zero, add_zero]
  refine LinearMap.mem_coboundaries_iff.2 ⟨_, ?_, rfl⟩
  have he : i + j + l + (ε - 1) = i + j + l + ε - 1 := by ring
  exact he ▸ kernelMap_mem_gradeBy hk hkfin hkd
    (tensor_mem_gradeBy (tensor_mem_gradeBy ha.2 hb.2) hc.2)

variable {d₁₂ : S₁₂ → ℤ} {d₂₃ : S₂₃ → ℤ} {δ₁₂ : S₁₂ → S₁₂ → R} {δ₂₃ : S₂₃ → S₂₃ → R}
  {E₁₂ E₂₃ : ℝ} {hδ₁₂ : ∀ p q, δ₁₂ p q ≠ 0 → F₁₂ q ≤ F₁₂ p + E₁₂}
  {hδ₁₂fin : ∀ p, δ₁₂ p ∈ NovikovModule R F₁₂} {hδ₂₃ : ∀ p q, δ₂₃ p q ≠ 0 → F₂₃ q ≤ F₂₃ p + E₂₃}
  {hδ₂₃fin : ∀ p, δ₂₃ p ∈ NovikovModule R F₂₃} {ε₁ ε₂ ε₃ ε₄ : ℤ}
  {hndeg : ∀ {i j : ℤ} {a : NovikovModule R F₁} {b : NovikovModule R F₂},
    a ∈ gradeBy R F₁ d₁ i → b ∈ gradeBy R F₂ d₂ j →
      kernelProduct hn hfin a b ∈ gradeBy R F₁₂ d₁₂ (i + j + ε₁)}
  {hnL : ∀ {i : ℤ} {a : NovikovModule R F₁}, a ∈ gradeBy R F₁ d₁ i → ∀ b,
    kernelMap hδ₁₂ hδ₁₂fin (kernelProduct hn hfin a b) =
      kernelProduct hn hfin (kernelMap hδ₁ hδ₁fin a) b +
        negOnePowCast R i • kernelProduct hn hfin a (kernelMap hδ₂ hδ₂fin b)}
  {hn'deg : ∀ {i j : ℤ} {a : NovikovModule R F₁₂} {b : NovikovModule R F₃},
    a ∈ gradeBy R F₁₂ d₁₂ i → b ∈ gradeBy R F₃ d₃ j →
      kernelProduct hn' hfin' a b ∈ gradeBy R F₀ d₀ (i + j + ε₂)}
  {hn'L : ∀ {i : ℤ} {a : NovikovModule R F₁₂}, a ∈ gradeBy R F₁₂ d₁₂ i → ∀ b,
    kernelMap hδ₀ hδ₀fin (kernelProduct hn' hfin' a b) =
      kernelProduct hn' hfin' (kernelMap hδ₁₂ hδ₁₂fin a) b +
        negOnePowCast R i • kernelProduct hn' hfin' a (kernelMap hδ₃ hδ₃fin b)}
  {hmdeg : ∀ {i j : ℤ} {a : NovikovModule R F₂} {b : NovikovModule R F₃},
    a ∈ gradeBy R F₂ d₂ i → b ∈ gradeBy R F₃ d₃ j →
      kernelProduct hm hmfin a b ∈ gradeBy R F₂₃ d₂₃ (i + j + ε₃)}
  {hmL : ∀ {i : ℤ} {a : NovikovModule R F₂}, a ∈ gradeBy R F₂ d₂ i → ∀ b,
    kernelMap hδ₂₃ hδ₂₃fin (kernelProduct hm hmfin a b) =
      kernelProduct hm hmfin (kernelMap hδ₂ hδ₂fin a) b +
        negOnePowCast R i • kernelProduct hm hmfin a (kernelMap hδ₃ hδ₃fin b)}
  {hm'deg : ∀ {i j : ℤ} {a : NovikovModule R F₁} {b : NovikovModule R F₂₃},
    a ∈ gradeBy R F₁ d₁ i → b ∈ gradeBy R F₂₃ d₂₃ j →
      kernelProduct hm' hmfin' a b ∈ gradeBy R F₀ d₀ (i + j + ε₄)}
  {hm'L : ∀ {i : ℤ} {a : NovikovModule R F₁}, a ∈ gradeBy R F₁ d₁ i → ∀ b,
    kernelMap hδ₀ hδ₀fin (kernelProduct hm' hmfin' a b) =
      kernelProduct hm' hmfin' (kernelMap hδ₁ hδ₁fin a) b +
        negOnePowCast R i • kernelProduct hm' hmfin' a (kernelMap hδ₂₃ hδ₂₃fin b)}

include hk hkfin in
/-- **Associativity on cohomology.** Let the four products `⋆`, `⋆'`, `⋆''`, `⋆'''` obey the
Leibniz rule and shift degrees by `ε₁`, `ε₂`, `ε₃`, `ε₄`, so that they induce products on
degree-wise cohomology. Under the kernel homotopy of
`NovikovModule.kernelProduct_kernelProduct_sub_kernelProduct_kernelProduct_of_mem_gradeBy`, with
the homotopy kernel `k` shifting degree by `ε₁ + ε₂ - 1`, the induced products are associative:
`([a] ⋆ [b]) ⋆' [c] = [a] ⋆''' ([b] ⋆'' [c])` for classes of degrees `i`, `j`, `l`. -/
theorem cohomologyProduct_kernelProduct_assoc
    (hkd : ∀ q p₀, k q p₀ ≠ 0 → d₀ p₀ = d₁ q.1.1 + d₂ q.1.2 + d₃ q.2 + (ε₁ + ε₂ - 1))
    (hassoc : ∀ (q : (S₁ × S₂) × S₃) p₀,
      ∑ᶠ t, n q.1.1 q.1.2 t * n' t q.2 p₀ - ∑ᶠ u, m q.1.2 q.2 u * m' q.1.1 u p₀ =
        kernelComp k δ₀ q p₀ +
          kernelComp (tensorDifferential (fun q : S₁ × S₂ => d₁ q.1 + d₂ q.2)
            (tensorDifferential d₁ δ₁ δ₂) δ₃) k q p₀)
    {i j l i₁₂ i₂₃ i₀ : ℤ} (h₁₂ : i + j + ε₁ = i₁₂) (h₀ : i₁₂ + l + ε₂ = i₀)
    (h₂₃ : j + l + ε₃ = i₂₃) (h₀' : i + i₂₃ + ε₄ = i₀)
    (x : (kernelMap hδ₁ hδ₁fin).cohomology (gradeBy R F₁ d₁) i)
    (y : (kernelMap hδ₂ hδ₂fin).cohomology (gradeBy R F₂ d₂) j)
    (z : (kernelMap hδ₃ hδ₃fin).cohomology (gradeBy R F₃ d₃) l) :
    LinearMap.cohomologyProduct (kernelProduct hn' hfin') hn'deg hn'L h₀
        (LinearMap.cohomologyProduct (kernelProduct hn hfin) hndeg hnL h₁₂ x y) z =
      LinearMap.cohomologyProduct (kernelProduct hm' hmfin') hm'deg hm'L h₀' x
        (LinearMap.cohomologyProduct (kernelProduct hm hmfin) hmdeg hmL h₂₃ y z) := by
  refine LinearMap.cohomologyProduct_assoc h₁₂ h₀ h₂₃ h₀' (fun ha hb hc => ?_) x y z
  have he : i + j + l + (ε₁ + ε₂) = i₀ := by omega
  exact he ▸ kernelProduct_kernelProduct_sub_kernelProduct_kernelProduct_mem_coboundaries hn hfin
    hn' hfin' hm hmfin hm' hmfin' hk hkfin hδ₀ hδ₀fin hδ₁ hδ₁fin hδ₂ hδ₂fin hδ₃ hδ₃fin hkd hassoc
    ha hb hc

end Cohomology

end CommRing

end NovikovModule

namespace NovikovModule

section AssociativityOfMatrix

variable {R H ι₁ ι₂ ι₃ ι₀ ι₁₂ ι₂₃ : Type*} [CommRing R] [AddCommGroup H] {N : H →+ ℝ}
  {P₁ : ι₁ → Type*} {P₂ : ι₂ → Type*} {P₃ : ι₃ → Type*} {P₀ : ι₀ → Type*}
  {P₁₂ : ι₁₂ → Type*} {P₂₃ : ι₂₃ → Type*}
  [∀ i, AddTorsor H (P₁ i)] [∀ j, AddTorsor H (P₂ j)] [∀ k, AddTorsor H (P₃ k)]
  [∀ l, AddTorsor H (P₀ l)] [∀ t, AddTorsor H (P₁₂ t)] [∀ u, AddTorsor H (P₂₃ u)]
  {F₁ : (Σ i, P₁ i) → ℝ} {F₂ : (Σ j, P₂ j) → ℝ} {F₃ : (Σ k, P₃ k) → ℝ} {F₀ : (Σ l, P₀ l) → ℝ}
  {F₁₂ : (Σ t, P₁₂ t) → ℝ} {F₂₃ : (Σ u, P₂₃ u) → ℝ}
  (hF₁ : ∀ i h (p : P₁ i), F₁ ⟨i, h +ᵥ p⟩ = F₁ ⟨i, p⟩ - N h)
  (hF₂ : ∀ j h (p : P₂ j), F₂ ⟨j, h +ᵥ p⟩ = F₂ ⟨j, p⟩ - N h)
  (hF₃ : ∀ k h (p : P₃ k), F₃ ⟨k, h +ᵥ p⟩ = F₃ ⟨k, p⟩ - N h)
  (hF₀ : ∀ l h (p : P₀ l), F₀ ⟨l, h +ᵥ p⟩ = F₀ ⟨l, p⟩ - N h)
  (hF₁₂ : ∀ t h (p : P₁₂ t), F₁₂ ⟨t, h +ᵥ p⟩ = F₁₂ ⟨t, p⟩ - N h)
  (hF₂₃ : ∀ u h (p : P₂₃ u), F₂₃ ⟨u, h +ᵥ p⟩ = F₂₃ ⟨u, p⟩ - N h)
  (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₃ : ∀ k, P₃ k) (r₀ : ∀ l, P₀ l)
  (r₁₂ : ∀ t, P₁₂ t) (r₂₃ : ∀ u, P₂₃ u)
  [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] [Fintype ι₀] [Fintype ι₁₂] [Fintype ι₂₃]

/-- **The associativity homotopy for matrices of Novikov series.** Let `Q`, `Q'` be the matrices
of the products in `(a ⋆ b) ⋆' c` and `T`, `T'` those of the products in `a ⋆''' (b ⋆'' c)`, let
`D₁`, `D₂`, `D₃`, `D₀` be the matrices of maps on the three inputs and the output, and let `K` be a
family of Novikov series indexed by three input orbits and an output orbit, all relative to
reference generators. Grade the first two inputs by `d₁` and `d₂`, with even changes of degree
within each orbit. If the matrices obey the associativity identity

`∑ₜ Qᵢⱼₜ Q'ₜₖₗ - ∑ᵤ Tⱼₖᵤ T'ᵢᵤₗ = ∑ₘ Kᵢⱼₖₘ D₀ₘₗ + ∑ₘ D₁ᵢₘ Kₘⱼₖₗ + (-1)^(d₁ (r₁ i)) ∑ₘ D₂ⱼₘ Kᵢₘₖₗ +
  (-1)^(d₁ (r₁ i) + d₂ (r₂ j)) ∑ₘ D₃ₖₘ Kᵢⱼₘₗ`,

which in Floer theory is the count of the ends of one-dimensional moduli spaces of
four-punctured spheres between reference generators, class by class, then for a completed
combination `a` of degree `e₁`, a completed combination `b` of degree `e₂` and any completed
combination `c`, the trilinear map of `K` is a homotopy between the two products:
`(a ⋆ b) ⋆' c - a ⋆''' (b ⋆'' c) = D₀ K(a, b, c) + K(D₁ a, b, c) + (-1)^e₁ K(a, D₂ b, c) +
(-1)^(e₁ + e₂) K(a, b, D₃ c)`. -/
theorem novikovProductOfMatrix_assoc_sub_eq_add
    (Q : ι₁ → ι₂ → ι₁₂ → NovikovSeries R H N) (Q' : ι₁₂ → ι₃ → ι₀ → NovikovSeries R H N)
    (T : ι₂ → ι₃ → ι₂₃ → NovikovSeries R H N) (T' : ι₁ → ι₂₃ → ι₀ → NovikovSeries R H N)
    (K : ι₁ → ι₂ → ι₃ → ι₀ → NovikovSeries R H N)
    (D₁ : Matrix ι₁ ι₁ (NovikovSeries R H N)) (D₂ : Matrix ι₂ ι₂ (NovikovSeries R H N))
    (D₃ : Matrix ι₃ ι₃ (NovikovSeries R H N)) (D₀ : Matrix ι₀ ι₀ (NovikovSeries R H N))
    {d₁ : (Σ i, P₁ i) → ℤ} {d₂ : (Σ j, P₂ j) → ℤ}
    (hd₁ : ∀ i (h : H) (p : P₁ i), Even (d₁ ⟨i, h +ᵥ p⟩ - d₁ ⟨i, p⟩))
    (hd₂ : ∀ j (h : H) (p : P₂ j), Even (d₂ ⟨j, h +ᵥ p⟩ - d₂ ⟨j, p⟩))
    (hA : ∀ i j k l, ∑ t, Q i j t * Q' t k l - ∑ u, T j k u * T' i u l =
      ∑ m, K i j k m * D₀ m l + ∑ m, D₁ i m * K m j k l +
        negOnePowCast R (d₁ ⟨i, r₁ i⟩) • ∑ m, D₂ j m * K i m k l +
        negOnePowCast R (d₁ ⟨i, r₁ i⟩ + d₂ ⟨j, r₂ j⟩) • ∑ m, D₃ k m * K i j m l)
    {e₁ e₂ : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ d₁ e₁)
    {b : NovikovModule R F₂} (hb : b ∈ gradeBy R F₂ d₂ e₂) (c : NovikovModule R F₃) :
    novikovProductOfMatrix hF₁₂ hF₃ hF₀ r₁₂ r₃ r₀ Q'
        (novikovProductOfMatrix hF₁ hF₂ hF₁₂ r₁ r₂ r₁₂ Q a b) c -
      novikovProductOfMatrix hF₁ hF₂₃ hF₀ r₁ r₂₃ r₀ T' a
        (novikovProductOfMatrix hF₂ hF₃ hF₂₃ r₂ r₃ r₂₃ T b c) =
      novikovMapOfMatrix hF₀ hF₀ r₀ r₀ D₀
          (novikovTrilinearOfMatrix hF₁ hF₂ hF₃ hF₀ r₁ r₂ r₃ r₀ K a b c) +
        novikovTrilinearOfMatrix hF₁ hF₂ hF₃ hF₀ r₁ r₂ r₃ r₀ K
          (novikovMapOfMatrix hF₁ hF₁ r₁ r₁ D₁ a) b c +
        negOnePowCast R e₁ • novikovTrilinearOfMatrix hF₁ hF₂ hF₃ hF₀ r₁ r₂ r₃ r₀ K a
          (novikovMapOfMatrix hF₂ hF₂ r₂ r₂ D₂ b) c +
        negOnePowCast R (e₁ + e₂) • novikovTrilinearOfMatrix hF₁ hF₂ hF₃ hF₀ r₁ r₂ r₃ r₀ K a b
          (novikovMapOfMatrix hF₃ hF₃ r₃ r₃ D₃ c) := by
  refine (coordinates hF₀ r₀).injective (funext fun l => ?_)
  simp only [map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    coordinates_novikovMapOfMatrix, coordinates_novikovProductOfMatrix,
    coordinates_novikovTrilinearOfMatrix]
  have hs₁ := negOnePowCast_smul_coordinates_of_mem_gradeBy hF₁ r₁ hd₁ ha
  have hs₂ := negOnePowCast_smul_coordinates_of_mem_gradeBy hF₂ r₂ hd₂ hb
  set x := coordinates hF₁ r₁ a
  set y := coordinates hF₂ r₂ b
  set z := coordinates hF₃ r₃ c
  -- Each of the six sums is regrouped as `∑ᵢ ∑ⱼ ∑ₖ xᵢ yⱼ zₖ c(i, j, k)`, with `c(i, j, k)`
  -- one of the six sums of the associativity identity, by expanding the products and
  -- interchanging the sums.
  have h₁ : ∑ t, ∑ k, (∑ i, ∑ j, x i * y j * Q i j t) * z k * Q' t k l =
      ∑ i, ∑ j, ∑ k, x i * y j * z k * ∑ t, Q i j t * Q' t k l := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset ι₃)),
      Finset.sum_comm (s := (Finset.univ : Finset ι₁₂))]
    ac_rfl
  have h₂ : ∑ i, ∑ u, (x i * ∑ j, ∑ k, y j * z k * T j k u) * T' i u l =
      ∑ i, ∑ j, ∑ k, x i * y j * z k * ∑ u, T j k u * T' i u l := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset ι₂₃))]
    ac_rfl
  have h₃ : ∑ m, (∑ i, ∑ j, ∑ k, x i * y j * z k * K i j k m) * D₀ m l =
      ∑ i, ∑ j, ∑ k, x i * y j * z k * ∑ m, K i j k m * D₀ m l := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset ι₀))]
    ac_rfl
  have h₄ : ∑ m, ∑ j, ∑ k, (∑ i, x i * D₁ i m) * y j * z k * K m j k l =
      ∑ i, ∑ j, ∑ k, x i * y j * z k * ∑ m, D₁ i m * K m j k l := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset ι₂)),
      Finset.sum_comm (s := (Finset.univ : Finset ι₃))]
    rw [Finset.sum_comm]
    ac_rfl
  have h₅ : ∑ i, ∑ m, ∑ k, (x i * ∑ j, y j * D₂ j m) * z k * K i m k l =
      ∑ i, ∑ j, ∑ k, x i * y j * z k * ∑ m, D₂ j m * K i m k l := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset ι₃))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    ac_rfl
  have h₆ : ∑ i, ∑ j, ∑ m, (x i * y j * ∑ k, z k * D₃ k m) * K i j m l =
      ∑ i, ∑ j, ∑ k, x i * y j * z k * ∑ m, D₃ k m * K i j m l := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    ac_rfl
  -- Termwise, this is the associativity identity, with the signs of the orbits of `i` and `j`
  -- replaced by the signs of the degrees of `a` and `b` on their nonzero coordinates.
  rw [h₁, h₂, h₃, h₄, h₅, h₆]
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  have h := hA i j k l
  simp only [← negOnePow_smul_eq_negOnePowCast_smul, Units.smul_def, zsmul_eq_mul,
    Int.negOnePow_add, Units.val_mul, Int.cast_mul] at h hs₁ hs₂ ⊢
  linear_combination (x i * y j * z k) * h + (y j * z k * ∑ m, D₂ j m * K i m k l) * hs₁ i +
    (((d₂ ⟨j, r₂ j⟩).negOnePow : ℤ) * y j * z k * ∑ m, D₃ k m * K i j m l) * hs₁ i +
    ((e₁.negOnePow : ℤ) * x i * z k * ∑ m, D₃ k m * K i j m l) * hs₂ j

end AssociativityOfMatrix

end NovikovModule

end TauCeti

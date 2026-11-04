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

Let `⋆` and `⋆'` be products of completed combinations given by supported product kernels
`n(p₁, p₂, p₀)` and `n'(t₁, t₂, t₀)` (`TauCeti.NovikovModule.kernelProduct`), and let `φ₁`, `φ₂`,
`φ₀` be kernels from the generators of each input and of the output of `⋆` to those of `⋆'`.
There are two ways to pass from a pair of inputs of `⋆` to an output of `⋆'`: multiply first and
then apply `φ₀`, or apply `φ₁` and `φ₂` first and then multiply. Both are kernel maps out of the
completed tensor product `a ⊗ b`, with the kernels `∑ₚ n(p₁, p₂, p) φ₀(p, ·)` and
`∑ₜ φ₁(p₁, t₁) φ₂(p₂, t₂) n'(t₁, t₂, ·)`.

In Floer theory `⋆` and `⋆'` are pair-of-pants products for two choices of end Hamiltonians, and
`φ₁`, `φ₂`, `φ₀` count continuation cylinders between them. Gluing the continuation cylinders to
the ends of a pair of pants gives a one-parameter family of pairs of pants whose perturbation
data interpolate between the two choices. Its broken ends are the two configurations above; the
remaining codimension-one boundary points of the one-dimensional moduli spaces are breakings of
Floer cylinders at the three ends. Counting all boundary points gives the kernel identity

`∑ₚ n(p₁, p₂, p) φ₀(p, t₀) - ∑ₜ φ₁(p₁, t₁) φ₂(p₂, t₂) n'(t₁, t₂, t₀) = (k η₀ + D k)(q, t₀)`

for the kernel `k(q, t₀)` counting rigid elements of the family, the differential `η₀` of the
output of `⋆'` and the differential `D` of the tensor product of the inputs of `⋆`, at every pair
`q = (p₁, p₂)`. This file turns that identity into the chain homotopy

`φ₀ (a ⋆ b) - φ₁ a ⋆' φ₂ b = η₀ (K (a ⊗ b)) + K (D (a ⊗ b))`

for arbitrary completed combinations, where `K` is the kernel map of `k`
(`NovikovModule.kernelMap_kernelProduct_sub_kernelProduct_kernelMap`). Both sides are infinite
sums. For the Koszul tensor differential `D = δ₁ ⊗ 1 + (-1)^(d₁) ⊗ δ₂` and `a` of degree `i` the
second term expands to `K (δ₁ a ⊗ b) + (-1)^i K (a ⊗ δ₂ b)`
(`NovikovModule.kernelMap_kernelProduct_sub_kernelProduct_kernelMap_of_mem_gradeBy`), so on
cocycles the difference is the coboundary `η₀ (K (a ⊗ b))`
(`NovikovModule.kernelMap_kernelProduct_sub_kernelProduct_kernelMap_mem_coboundaries`). Hence the
maps induced on degree-wise cohomology by `φ₁`, `φ₂`, `φ₀` intertwine the two products on
cohomology (`NovikovModule.cohomologyMap_cohomologyProduct_kernelProduct`): continuation maps are
multiplicative on cohomology. The kernel identity and the potential bounds, which come from the
energy estimate, remain hypotheses: they are the geometric input from the compactified moduli
spaces.

## Main results

* `NovikovModule.kernelMap_kernelProduct_sub_kernelProduct_kernelMap`: a kernel homotopy between
  the two composite kernels gives a chain homotopy between `φ₀ (a ⋆ b)` and `φ₁ a ⋆' φ₂ b`.
* `NovikovModule.kernelMap_kernelProduct_sub_kernelProduct_kernelMap_of_mem_gradeBy`: the same
  homotopy for the Koszul tensor differential, with its sign.
* `NovikovModule.kernelMap_kernelProduct_sub_kernelProduct_kernelMap_mem_coboundaries`: on
  cocycles the two composites differ by a coboundary.
* `NovikovModule.cohomologyMap_cohomologyProduct_kernelProduct`: the maps induced on cohomology
  intertwine the two products.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  compatibility of the pair-of-pants product with continuation maps.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995).
-/

public section

noncomputable section

namespace TauCeti

namespace NovikovModule

variable {R S₁ S₂ S₀ T₁ T₂ T₀ : Type*} [CommRing R]
  {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ} {F₀ : S₀ → ℝ} {G₁ : T₁ → ℝ} {G₂ : T₂ → ℝ} {G₀ : T₀ → ℝ}
  {C C' C₁ C₂ C₀ Ck Cη : ℝ}
  {n : S₁ → S₂ → S₀ → R} {n' : T₁ → T₂ → T₀ → R}
  {φ₁ : S₁ → T₁ → R} {φ₂ : S₂ → T₂ → R} {φ₀ : S₀ → T₀ → R}
  {k : S₁ × S₂ → T₀ → R} {η₀ : T₀ → T₀ → R}
  (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
  (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)
  (hn' : ∀ t₁ t₂ t₀, n' t₁ t₂ t₀ ≠ 0 → G₀ t₀ ≤ G₁ t₁ + G₂ t₂ + C')
  (hfin' : ∀ t₁ t₂, n' t₁ t₂ ∈ NovikovModule R G₀)
  (hφ₁ : ∀ p t, φ₁ p t ≠ 0 → G₁ t ≤ F₁ p + C₁) (hφ₁fin : ∀ p, φ₁ p ∈ NovikovModule R G₁)
  (hφ₂ : ∀ p t, φ₂ p t ≠ 0 → G₂ t ≤ F₂ p + C₂) (hφ₂fin : ∀ p, φ₂ p ∈ NovikovModule R G₂)
  (hφ₀ : ∀ p t, φ₀ p t ≠ 0 → G₀ t ≤ F₀ p + C₀) (hφ₀fin : ∀ p, φ₀ p ∈ NovikovModule R G₀)
  (hk : ∀ (q : S₁ × S₂) t₀, k q t₀ ≠ 0 → G₀ t₀ ≤ F₁ q.1 + F₂ q.2 + Ck)
  (hkfin : ∀ q, k q ∈ NovikovModule R G₀)
  (hη₀ : ∀ t t', η₀ t t' ≠ 0 → G₀ t' ≤ G₀ t + Cη) (hη₀fin : ∀ t, η₀ t ∈ NovikovModule R G₀)

section Homotopy

/-- **Compatibility with continuation maps up to homotopy.** Let `n` and `n'` be product kernels,
let `φ₁`, `φ₂`, `φ₀` be kernels from the generators of each input and of the output of the first
product to those of the second, let `η₀` be a kernel on the output generators of the second
product, and let `D` be a kernel on pairs of input generators of the first. If a kernel `k` from
pairs of input generators of the first product to output generators of the second is a kernel
homotopy,

`∑ₚ n(p₁, p₂, p) φ₀(p, t₀) - ∑ₜ φ₁(p₁, t₁) φ₂(p₂, t₂) n'(t₁, t₂, t₀) = (k η₀ + D k)(q, t₀)`

for `q = (p₁, p₂)`, then its kernel map `K` is a homotopy between the two composites: for
`x = a ⊗ b`, `φ₀ (a ⋆ b) - φ₁ a ⋆' φ₂ b = η₀ (K x) + K (D x)`. -/
theorem kernelMap_kernelProduct_sub_kernelProduct_kernelMap
    {D : S₁ × S₂ → S₁ × S₂ → R} {CD : ℝ}
    (hD : ∀ q q', D q q' ≠ 0 → F₁ q'.1 + F₂ q'.2 ≤ F₁ q.1 + F₂ q.2 + CD)
    (hDfin : ∀ q, D q ∈ NovikovModule R fun q' : S₁ × S₂ => F₁ q'.1 + F₂ q'.2)
    (hcont : ∀ (q : S₁ × S₂) t₀,
      kernelComp (fun q : S₁ × S₂ => n q.1 q.2) φ₀ q t₀ -
          kernelComp (kernelTensor φ₁ φ₂) (fun t : T₁ × T₂ => n' t.1 t.2) q t₀ =
        kernelComp k η₀ q t₀ + kernelComp D k q t₀)
    (a : NovikovModule R F₁) (b : NovikovModule R F₂) :
    kernelMap hφ₀ hφ₀fin (kernelProduct hn hfin a b) -
        kernelProduct hn' hfin' (kernelMap hφ₁ hφ₁fin a) (kernelMap hφ₂ hφ₂fin b) =
      kernelMap hη₀ hη₀fin (kernelMap hk hkfin (tensor a b)) +
        kernelMap hk hkfin (kernelMap hD hDfin (tensor a b)) := by
  -- Both composites are kernel maps out of the tensor product, of the two composite kernels.
  have hn₂ (q : S₁ × S₂) (p₀ : S₀) (h : n q.1 q.2 p₀ ≠ 0) : F₀ p₀ ≤ F₁ q.1 + F₂ q.2 + C :=
    hn q.1 q.2 p₀ h
  have hn'₂ (t : T₁ × T₂) (t₀ : T₀) (h : n' t.1 t.2 t₀ ≠ 0) : G₀ t₀ ≤ G₁ t.1 + G₂ t.2 + C' :=
    hn' t.1 t.2 t₀ h
  have hT (q : S₁ × S₂) (t : T₁ × T₂) (h : kernelTensor φ₁ φ₂ q t ≠ 0) :
      G₁ t.1 + G₂ t.2 ≤ F₁ q.1 + F₂ q.2 + (C₁ + C₂) :=
    potential_le_of_kernelTensor_ne_zero hφ₁ hφ₂ h
  have hTfin := kernelTensor_mem hφ₁fin hφ₂fin
  have hN (q : S₁ × S₂) (t₀ : T₀) (h : kernelComp (fun q : S₁ × S₂ => n q.1 q.2) φ₀ q t₀ ≠ 0) :
      G₀ t₀ ≤ F₁ q.1 + F₂ q.2 + (C + C₀) := by
    linarith [potential_le_of_kernelComp_ne_zero (m := fun q : S₁ × S₂ => n q.1 q.2) (hn₂ q)
      (hφ₀ · t₀) h]
  have hM (q : S₁ × S₂) (t₀ : T₀)
      (h : kernelComp (kernelTensor φ₁ φ₂) (fun t : T₁ × T₂ => n' t.1 t.2) q t₀ ≠ 0) :
      G₀ t₀ ≤ F₁ q.1 + F₂ q.2 + (C₁ + C₂ + C') := by
    linarith [potential_le_of_kernelComp_ne_zero (hT q) (hn'₂ · t₀) h]
  rw [kernelProduct_eq_kernelMap_tensor hn hfin hn₂ (fun q => hfin q.1 q.2),
    kernelMap_kernelMap hn₂ (fun q => hfin q.1 q.2) hφ₀ hφ₀fin hN
      (fun q => kernelComp_mem hφ₀ hφ₀fin (hfin q.1 q.2)),
    kernelProduct_eq_kernelMap_tensor hn' hfin' hn'₂ (fun t => hfin' t.1 t.2),
    ← kernelMap_kernelTensor_tensor hφ₁ hφ₁fin hφ₂ hφ₂fin hT hTfin,
    kernelMap_kernelMap hT hTfin hn'₂ (fun t => hfin' t.1 t.2) hM
      (fun q => kernelComp_mem hn'₂ (fun t => hfin' t.1 t.2) (hTfin q))]
  exact kernelMap_sub_kernelMap _ _ _ _ hk hkfin hD hDfin hη₀ hη₀fin hcont _

/-- **Compatibility with continuation maps up to homotopy, with the Koszul sign.** Let `δ₁`,
`δ₂` be kernels on the input generators of the first product and `d₁` a degree function on the
first input, and let `D = δ₁ ⊗ 1 + (-1)^(d₁) ⊗ δ₂` be the tensor differential. If a kernel `k` is
a kernel homotopy,

`∑ₚ n(p₁, p₂, p) φ₀(p, t₀) - ∑ₜ φ₁(p₁, t₁) φ₂(p₂, t₂) n'(t₁, t₂, t₀) = (k η₀ + D k)(q, t₀)`

for `q = (p₁, p₂)`, then for `a` of degree `i` and any `b` its kernel map `K` satisfies

`φ₀ (a ⋆ b) - φ₁ a ⋆' φ₂ b = η₀ (K (a ⊗ b)) + K (δ₁ a ⊗ b) + (-1)^i K (a ⊗ δ₂ b)`. -/
theorem kernelMap_kernelProduct_sub_kernelProduct_kernelMap_of_mem_gradeBy
    [DecidableEq S₁] [DecidableEq S₂] {d₁ : S₁ → ℤ} {δ₁ : S₁ → S₁ → R} {δ₂ : S₂ → S₂ → R}
    {E₁ E₂ : ℝ}
    (hδ₁ : ∀ p q, δ₁ p q ≠ 0 → F₁ q ≤ F₁ p + E₁) (hδ₁fin : ∀ p, δ₁ p ∈ NovikovModule R F₁)
    (hδ₂ : ∀ p q, δ₂ p q ≠ 0 → F₂ q ≤ F₂ p + E₂) (hδ₂fin : ∀ p, δ₂ p ∈ NovikovModule R F₂)
    (hcont : ∀ (q : S₁ × S₂) t₀,
      kernelComp (fun q : S₁ × S₂ => n q.1 q.2) φ₀ q t₀ -
          kernelComp (kernelTensor φ₁ φ₂) (fun t : T₁ × T₂ => n' t.1 t.2) q t₀ =
        kernelComp k η₀ q t₀ + kernelComp (tensorDifferential d₁ δ₁ δ₂) k q t₀)
    {i : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ d₁ i) (b : NovikovModule R F₂) :
    kernelMap hφ₀ hφ₀fin (kernelProduct hn hfin a b) -
        kernelProduct hn' hfin' (kernelMap hφ₁ hφ₁fin a) (kernelMap hφ₂ hφ₂fin b) =
      kernelMap hη₀ hη₀fin (kernelMap hk hkfin (tensor a b)) +
        kernelMap hk hkfin (tensor (kernelMap hδ₁ hδ₁fin a) b) +
        (i.negOnePow : R) • kernelMap hk hkfin (tensor a (kernelMap hδ₂ hδ₂fin b)) := by
  have hD (p q : S₁ × S₂) (h : tensorDifferential d₁ δ₁ δ₂ p q ≠ 0) :=
    potential_le_of_tensorDifferential_ne_zero hδ₁ hδ₂ h
  have hDfin := tensorDifferential_mem (d₁ := d₁) hδ₁fin hδ₂fin
  rw [kernelMap_kernelProduct_sub_kernelProduct_kernelMap hn hfin hn' hfin' hφ₁ hφ₁fin hφ₂ hφ₂fin
      hφ₀ hφ₀fin hk hkfin hη₀ hη₀fin hD hDfin hcont,
    kernelMap_tensorDifferential_tensor hδ₁ hδ₁fin hδ₂ hδ₂fin hD hDfin ha]
  simp only [map_add, map_smul, add_assoc]

include hk hkfin in
/-- **Compatibility with continuation maps on cocycles.** Under the kernel homotopy of
`NovikovModule.kernelMap_kernelProduct_sub_kernelProduct_kernelMap_of_mem_gradeBy`, suppose that
`k` has degree `ε - 1` for degree functions `d₁`, `d₂` on the inputs of the first product and
`e₀` on the output of the second. Then for cocycles `a` and `b` of degrees `i` and `j`, the
difference `φ₀ (a ⋆ b) - φ₁ a ⋆' φ₂ b` is a coboundary of degree `i + j + ε`. -/
theorem kernelMap_kernelProduct_sub_kernelProduct_kernelMap_mem_coboundaries
    [DecidableEq S₁] [DecidableEq S₂] {d₁ : S₁ → ℤ} {d₂ : S₂ → ℤ} {e₀ : T₀ → ℤ} {ε : ℤ}
    {δ₁ : S₁ → S₁ → R} {δ₂ : S₂ → S₂ → R} {E₁ E₂ : ℝ}
    (hδ₁ : ∀ p q, δ₁ p q ≠ 0 → F₁ q ≤ F₁ p + E₁) (hδ₁fin : ∀ p, δ₁ p ∈ NovikovModule R F₁)
    (hδ₂ : ∀ p q, δ₂ p q ≠ 0 → F₂ q ≤ F₂ p + E₂) (hδ₂fin : ∀ p, δ₂ p ∈ NovikovModule R F₂)
    (hkd : ∀ (q : S₁ × S₂) t₀, k q t₀ ≠ 0 → e₀ t₀ = d₁ q.1 + d₂ q.2 + (ε - 1))
    (hcont : ∀ (q : S₁ × S₂) t₀,
      kernelComp (fun q : S₁ × S₂ => n q.1 q.2) φ₀ q t₀ -
          kernelComp (kernelTensor φ₁ φ₂) (fun t : T₁ × T₂ => n' t.1 t.2) q t₀ =
        kernelComp k η₀ q t₀ + kernelComp (tensorDifferential d₁ δ₁ δ₂) k q t₀)
    {i j : ℤ} {a : NovikovModule R F₁}
    (ha : a ∈ (kernelMap hδ₁ hδ₁fin).cocycles (gradeBy R F₁ d₁) i)
    {b : NovikovModule R F₂} (hb : b ∈ (kernelMap hδ₂ hδ₂fin).cocycles (gradeBy R F₂ d₂) j) :
    kernelMap hφ₀ hφ₀fin (kernelProduct hn hfin a b) -
        kernelProduct hn' hfin' (kernelMap hφ₁ hφ₁fin a) (kernelMap hφ₂ hφ₂fin b) ∈
      (kernelMap hη₀ hη₀fin).coboundaries (gradeBy R G₀ e₀) (i + j + ε) := by
  rw [LinearMap.mem_cocycles_iff] at ha hb
  rw [kernelMap_kernelProduct_sub_kernelProduct_kernelMap_of_mem_gradeBy hn hfin hn' hfin' hφ₁
      hφ₁fin hφ₂ hφ₂fin hφ₀ hφ₀fin hk hkfin hη₀ hη₀fin hδ₁ hδ₁fin hδ₂ hδ₂fin hcont ha.2,
    ha.1, hb.1]
  simp only [map_zero, LinearMap.zero_apply, smul_zero, add_zero]
  refine LinearMap.mem_coboundaries_iff.2 ⟨_, ?_, rfl⟩
  have hdeg : i + j + (ε - 1) = i + j + ε - 1 := by ring
  exact hdeg ▸ kernelMap_mem_gradeBy hk hkfin (d₁ := fun q : S₁ × S₂ => d₁ q.1 + d₂ q.2) hkd
    (tensor_mem_gradeBy ha.2 hb.2)

end Homotopy

section Cohomology

variable [DecidableEq S₁] [DecidableEq S₂]
  {d₁ : S₁ → ℤ} {d₂ : S₂ → ℤ} {d₀ : S₀ → ℤ} {e₁ : T₁ → ℤ} {e₂ : T₂ → ℤ} {e₀ : T₀ → ℤ} {ε : ℤ}
  {δ₁ : S₁ → S₁ → R} {δ₂ : S₂ → S₂ → R} {δ₀ : S₀ → S₀ → R}
  {η₁ : T₁ → T₁ → R} {η₂ : T₂ → T₂ → R} {E₁ E₂ E₀ E₁' E₂' : ℝ}
  (hδ₁ : ∀ p q, δ₁ p q ≠ 0 → F₁ q ≤ F₁ p + E₁) (hδ₁fin : ∀ p, δ₁ p ∈ NovikovModule R F₁)
  (hδ₂ : ∀ p q, δ₂ p q ≠ 0 → F₂ q ≤ F₂ p + E₂) (hδ₂fin : ∀ p, δ₂ p ∈ NovikovModule R F₂)
  (hδ₀ : ∀ p q, δ₀ p q ≠ 0 → F₀ q ≤ F₀ p + E₀) (hδ₀fin : ∀ p, δ₀ p ∈ NovikovModule R F₀)
  (hη₁ : ∀ p q, η₁ p q ≠ 0 → G₁ q ≤ G₁ p + E₁') (hη₁fin : ∀ p, η₁ p ∈ NovikovModule R G₁)
  (hη₂ : ∀ p q, η₂ p q ≠ 0 → G₂ q ≤ G₂ p + E₂') (hη₂fin : ∀ p, η₂ p ∈ NovikovModule R G₂)
  {hndeg : ∀ {i j : ℤ} {a : NovikovModule R F₁} {b : NovikovModule R F₂},
    a ∈ gradeBy R F₁ d₁ i → b ∈ gradeBy R F₂ d₂ j →
      kernelProduct hn hfin a b ∈ gradeBy R F₀ d₀ (i + j + ε)}
  {hnL : ∀ {i : ℤ} {a : NovikovModule R F₁}, a ∈ gradeBy R F₁ d₁ i → ∀ b,
    kernelMap hδ₀ hδ₀fin (kernelProduct hn hfin a b) =
      kernelProduct hn hfin (kernelMap hδ₁ hδ₁fin a) b +
        negOnePowCast R i • kernelProduct hn hfin a (kernelMap hδ₂ hδ₂fin b)}
  {hn'deg : ∀ {i j : ℤ} {a : NovikovModule R G₁} {b : NovikovModule R G₂},
    a ∈ gradeBy R G₁ e₁ i → b ∈ gradeBy R G₂ e₂ j →
      kernelProduct hn' hfin' a b ∈ gradeBy R G₀ e₀ (i + j + ε)}
  {hn'L : ∀ {i : ℤ} {a : NovikovModule R G₁}, a ∈ gradeBy R G₁ e₁ i → ∀ b,
    kernelMap hη₀ hη₀fin (kernelProduct hn' hfin' a b) =
      kernelProduct hn' hfin' (kernelMap hη₁ hη₁fin a) b +
        negOnePowCast R i • kernelProduct hn' hfin' a (kernelMap hη₂ hη₂fin b)}
  {hφ₁deg : ∀ {i : ℤ} {a : NovikovModule R F₁}, a ∈ gradeBy R F₁ d₁ i →
    kernelMap hφ₁ hφ₁fin a ∈ gradeBy R G₁ e₁ i}
  {hφ₁D : ∀ {i : ℤ} {a : NovikovModule R F₁}, a ∈ gradeBy R F₁ d₁ i →
    kernelMap hη₁ hη₁fin (kernelMap hφ₁ hφ₁fin a) = kernelMap hφ₁ hφ₁fin (kernelMap hδ₁ hδ₁fin a)}
  {hφ₂deg : ∀ {i : ℤ} {a : NovikovModule R F₂}, a ∈ gradeBy R F₂ d₂ i →
    kernelMap hφ₂ hφ₂fin a ∈ gradeBy R G₂ e₂ i}
  {hφ₂D : ∀ {i : ℤ} {a : NovikovModule R F₂}, a ∈ gradeBy R F₂ d₂ i →
    kernelMap hη₂ hη₂fin (kernelMap hφ₂ hφ₂fin a) = kernelMap hφ₂ hφ₂fin (kernelMap hδ₂ hδ₂fin a)}
  {hφ₀deg : ∀ {i : ℤ} {a : NovikovModule R F₀}, a ∈ gradeBy R F₀ d₀ i →
    kernelMap hφ₀ hφ₀fin a ∈ gradeBy R G₀ e₀ i}
  {hφ₀D : ∀ {i : ℤ} {a : NovikovModule R F₀}, a ∈ gradeBy R F₀ d₀ i →
    kernelMap hη₀ hη₀fin (kernelMap hφ₀ hφ₀fin a) =
      kernelMap hφ₀ hφ₀fin (kernelMap hδ₀ hδ₀fin a)}

include hk hkfin in
/-- **Continuation maps are multiplicative on cohomology.** Let `⋆` and `⋆'` be products obeying
the Leibniz rule and shifting degree by `ε`, so that they induce products on degree-wise
cohomology, and let `φ₁`, `φ₂`, `φ₀` be degree-preserving kernel maps commuting with the
differentials, so that they induce maps on cohomology. If a kernel `k` of degree `ε - 1` is a
kernel homotopy,

`∑ₚ n(p₁, p₂, p) φ₀(p, t₀) - ∑ₜ φ₁(p₁, t₁) φ₂(p₂, t₂) n'(t₁, t₂, t₀) = (k η₀ + D k)(q, t₀)`

for the tensor differential `D = δ₁ ⊗ 1 + (-1)^(d₁) ⊗ δ₂`, then the induced maps intertwine the
products on cohomology: `φ₀ (x ⋆ y) = φ₁ x ⋆' φ₂ y` for all classes `x` of degree `i` and `y` of
degree `j`. -/
theorem cohomologyMap_cohomologyProduct_kernelProduct
    (hkd : ∀ (q : S₁ × S₂) t₀, k q t₀ ≠ 0 → e₀ t₀ = d₁ q.1 + d₂ q.2 + (ε - 1))
    (hcont : ∀ (q : S₁ × S₂) t₀,
      kernelComp (fun q : S₁ × S₂ => n q.1 q.2) φ₀ q t₀ -
          kernelComp (kernelTensor φ₁ φ₂) (fun t : T₁ × T₂ => n' t.1 t.2) q t₀ =
        kernelComp k η₀ q t₀ + kernelComp (tensorDifferential d₁ δ₁ δ₂) k q t₀)
    {i j l : ℤ} (hl : i + j + ε = l)
    (x : (kernelMap hδ₁ hδ₁fin).cohomology (gradeBy R F₁ d₁) i)
    (y : (kernelMap hδ₂ hδ₂fin).cohomology (gradeBy R F₂ d₂) j) :
    LinearMap.cohomologyMap (kernelMap hφ₀ hφ₀fin) hφ₀deg hφ₀D l
        (LinearMap.cohomologyProduct (kernelProduct hn hfin) hndeg hnL hl x y) =
      LinearMap.cohomologyProduct (kernelProduct hn' hfin') hn'deg hn'L hl
        (LinearMap.cohomologyMap (kernelMap hφ₁ hφ₁fin) hφ₁deg hφ₁D i x)
        (LinearMap.cohomologyMap (kernelMap hφ₂ hφ₂fin) hφ₂deg hφ₂D j y) := by
  subst hl
  exact LinearMap.cohomologyMap_cohomologyProduct rfl (fun ha hb =>
    kernelMap_kernelProduct_sub_kernelProduct_kernelMap_mem_coboundaries hn hfin hn' hfin' hφ₁
      hφ₁fin hφ₂ hφ₂fin hφ₀ hφ₀fin hk hkfin hη₀ hη₀fin hδ₁ hδ₁fin hδ₂ hδ₂fin hkd hcont ha hb) x y

end Cohomology

end NovikovModule

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Grading
public import TauCeti.Algebra.Homology.SquareZero.Graded

/-!
# Unit homotopies of supported kernel products

Let `⋆` be the product of completed combinations given by a supported product kernel
`n(p₁, p₂, p₀)` (`TauCeti.NovikovModule.kernelProduct`), and let `e` be a completed combination
of generators of the first input. Multiplying by `e` on the left is the kernel map of the
one-input kernel `p₂ ↦ ∑ₜ e(t) n(t, p₂, ·)` (`NovikovModule.kernelProduct_eq_kernelMap_right`).

In Floer theory `e` is the unit cycle, the count of PSS planes constrained by the fundamental
cycle, and gluing such a plane into the first input of a pair of pants gives a one-parameter
family whose other end is a Floer cylinder: a continuation cylinder `φ` between the two end
Hamiltonians, or the stationary cylinder, with the identity kernel, when they coincide. The
remaining codimension-one boundary points of its one-dimensional moduli spaces are breakings of
Floer cylinders at the two other ends, together with breakings at the constraint, which cancel
because the fundamental cycle is closed. Counting all boundary points gives the kernel identity

`∑ₜ e(t) n(t, p₂, p₀) - φ(p₂, p₀) = (k δ₀ + δ₂ k)(p₂, p₀)`

for the kernel `k` counting rigid elements of the family. This file turns that identity into the
chain homotopy `e ⋆ b - φ b = δ₀ (K b) + K (δ₂ b)` for every completed combination `b`, where
`K` is the kernel map of `k` (`NovikovModule.kernelProduct_sub_kernelMap_right`), and likewise
for a unit in the second input (`NovikovModule.kernelProduct_sub_kernelMap_left`). Both sides are
infinite sums. The proofs reduce to the chain homotopy of a kernel homotopy between one-input
kernels (`NovikovModule.kernelMap_sub_kernelMap`).

If `K` lowers degree by one, then on a cocycle `b` the difference `e ⋆ b - φ b` is the coboundary
`δ₀ (K b)` (`NovikovModule.kernelProduct_sub_kernelMap_mem_coboundaries_right`). On a common
complex, with `φ` the identity kernel, the class of a cocycle `e` is therefore a two-sided unit for
the product on degree-wise cohomology (`LinearMap.cohomologyProduct`) induced by `⋆`
(`NovikovModule.cohomologyProduct_kernelProduct_unit_mk`,
`NovikovModule.cohomologyProduct_kernelProduct_mk_unit`). The kernel identities and potential
bounds remain hypotheses: they are the geometric input from the compactified moduli spaces.

## Main results

* `NovikovModule.kernelProduct_sub_kernelMap_right`,
  `NovikovModule.kernelProduct_sub_kernelMap_left`: a unit kernel homotopy gives a chain homotopy
  between multiplication by the unit and the kernel map of the cylinder kernel.
* `NovikovModule.kernelProduct_sub_kernelMap_mem_coboundaries_right`,
  `NovikovModule.kernelProduct_sub_kernelMap_mem_coboundaries_left`: on cocycles the two differ by
  a coboundary.
* `NovikovModule.cohomologyProduct_kernelProduct_unit_mk`,
  `NovikovModule.cohomologyProduct_kernelProduct_mk_unit`: on a common complex the class of the
  unit is a left and a right identity for the product on cohomology.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  unit of the pair-of-pants product.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995).
-/

public section

noncomputable section

namespace TauCeti

namespace NovikovModule

variable {R S₁ S₂ S₀ : Type*} [CommRing R] {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ} {F₀ : S₀ → ℝ}
  {C Cφ Ck Cδ C₀ : ℝ}

section Homotopy

variable {n : S₁ → S₂ → S₀ → R}
  (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
  (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)
  {δ₀ : S₀ → S₀ → R} (hδ₀ : ∀ p q, δ₀ p q ≠ 0 → F₀ q ≤ F₀ p + C₀)
  (hδ₀fin : ∀ p, δ₀ p ∈ NovikovModule R F₀)

section Right

variable {φ k : S₂ → S₀ → R} (hφ : ∀ p₂ p₀, φ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₂ p₂ + Cφ)
  (hφfin : ∀ p₂, φ p₂ ∈ NovikovModule R F₀)
  (hk : ∀ p₂ p₀, k p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₂ p₂ + Ck) (hkfin : ∀ p₂, k p₂ ∈ NovikovModule R F₀)
  {δ₂ : S₂ → S₂ → R} (hδ₂ : ∀ p q, δ₂ p q ≠ 0 → F₂ q ≤ F₂ p + Cδ)
  (hδ₂fin : ∀ p, δ₂ p ∈ NovikovModule R F₂)

/-- **A unit in the first input, up to homotopy.** Let `e` be a completed combination of
generators of the first input, `φ` a kernel between the second input and the output, and `δ₂`,
`δ₀` kernels on the generators of the second input and of the output. If a kernel `k` is a kernel
homotopy,

`∑ₜ e(t) n(t, p₂, p₀) - φ(p₂, p₀) = (k δ₀ + δ₂ k)(p₂, p₀)`,

then its kernel map `K` is a homotopy between multiplication by `e` and the map of `φ`:
`e ⋆ b - φ b = δ₀ (K b) + K (δ₂ b)` for every completed combination `b`. -/
theorem kernelProduct_sub_kernelMap_right (e : NovikovModule R F₁)
    (hunit : ∀ p₂ p₀, ∑ᶠ t, e.val t * n t p₂ p₀ - φ p₂ p₀ =
      kernelComp k δ₀ p₂ p₀ + kernelComp δ₂ k p₂ p₀)
    (b : NovikovModule R F₂) :
    kernelProduct hn hfin e b - kernelMap hφ hφfin b =
      kernelMap hδ₀ hδ₀fin (kernelMap hk hkfin b) +
        kernelMap hk hkfin (kernelMap hδ₂ hδ₂fin b) := by
  obtain ⟨D, hm⟩ := kernelProduct_exists_potential_le_right hn e
  rw [kernelProduct_eq_kernelMap_right hn hfin e hm (kernelProduct_finsum_mul_mem_right hn hfin e)]
  exact kernelMap_sub_kernelMap hm _ hφ hφfin hk hkfin hδ₂ hδ₂fin hδ₀ hδ₀fin hunit b

include hk hkfin in
/-- **A unit in the first input, on cocycles.** Under the kernel homotopy of
`NovikovModule.kernelProduct_sub_kernelMap_right`, if the homotopy kernel `k` lowers degree by
one, then for every cocycle `b` of degree `j` the difference `e ⋆ b - φ b` is a coboundary of
degree `j`. -/
theorem kernelProduct_sub_kernelMap_mem_coboundaries_right {d₂ : S₂ → ℤ} {d₀ : S₀ → ℤ}
    (hkd : ∀ p₂ p₀, k p₂ p₀ ≠ 0 → d₀ p₀ = d₂ p₂ - 1) (e : NovikovModule R F₁)
    (hunit : ∀ p₂ p₀, ∑ᶠ t, e.val t * n t p₂ p₀ - φ p₂ p₀ =
      kernelComp k δ₀ p₂ p₀ + kernelComp δ₂ k p₂ p₀)
    {j : ℤ} {b : NovikovModule R F₂}
    (hb : b ∈ (kernelMap hδ₂ hδ₂fin).cocycles (gradeBy R F₂ d₂) j) :
    kernelProduct hn hfin e b - kernelMap hφ hφfin b ∈
      (kernelMap hδ₀ hδ₀fin).coboundaries (gradeBy R F₀ d₀) j := by
  rw [LinearMap.mem_cocycles_iff] at hb
  rw [kernelProduct_sub_kernelMap_right hn hfin hδ₀ hδ₀fin hφ hφfin hk hkfin hδ₂ hδ₂fin e hunit,
    hb.1, map_zero, add_zero]
  refine LinearMap.mem_coboundaries_iff.2 ⟨_, ?_, rfl⟩
  simpa only [sub_eq_add_neg] using kernelMap_mem_gradeBy hk hkfin
    (fun p₂ p₀ h => by rw [hkd p₂ p₀ h, sub_eq_add_neg]) hb.2

end Right

section Left

variable {φ k : S₁ → S₀ → R} (hφ : ∀ p₁ p₀, φ p₁ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + Cφ)
  (hφfin : ∀ p₁, φ p₁ ∈ NovikovModule R F₀)
  (hk : ∀ p₁ p₀, k p₁ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + Ck) (hkfin : ∀ p₁, k p₁ ∈ NovikovModule R F₀)
  {δ₁ : S₁ → S₁ → R} (hδ₁ : ∀ p q, δ₁ p q ≠ 0 → F₁ q ≤ F₁ p + Cδ)
  (hδ₁fin : ∀ p, δ₁ p ∈ NovikovModule R F₁)

/-- **A unit in the second input, up to homotopy.** Let `e` be a completed combination of
generators of the second input, `φ` a kernel between the first input and the output, and `δ₁`,
`δ₀` kernels on the generators of the first input and of the output. If a kernel `k` is a kernel
homotopy,

`∑ₜ e(t) n(p₁, t, p₀) - φ(p₁, p₀) = (k δ₀ + δ₁ k)(p₁, p₀)`,

then its kernel map `K` is a homotopy between multiplication by `e` and the map of `φ`:
`a ⋆ e - φ a = δ₀ (K a) + K (δ₁ a)` for every completed combination `a`. -/
theorem kernelProduct_sub_kernelMap_left (e : NovikovModule R F₂)
    (hunit : ∀ p₁ p₀, ∑ᶠ t, e.val t * n p₁ t p₀ - φ p₁ p₀ =
      kernelComp k δ₀ p₁ p₀ + kernelComp δ₁ k p₁ p₀)
    (a : NovikovModule R F₁) :
    kernelProduct hn hfin a e - kernelMap hφ hφfin a =
      kernelMap hδ₀ hδ₀fin (kernelMap hk hkfin a) +
        kernelMap hk hkfin (kernelMap hδ₁ hδ₁fin a) := by
  obtain ⟨D, hm⟩ := kernelProduct_exists_potential_le_left hn e
  rw [kernelProduct_eq_kernelMap_left hn hfin e hm (kernelProduct_finsum_mul_mem_left hn hfin e)]
  exact kernelMap_sub_kernelMap hm _ hφ hφfin hk hkfin hδ₁ hδ₁fin hδ₀ hδ₀fin hunit a

include hk hkfin in
/-- **A unit in the second input, on cocycles.** Under the kernel homotopy of
`NovikovModule.kernelProduct_sub_kernelMap_left`, if the homotopy kernel `k` lowers degree by
one, then for every cocycle `a` of degree `i` the difference `a ⋆ e - φ a` is a coboundary of
degree `i`. -/
theorem kernelProduct_sub_kernelMap_mem_coboundaries_left {d₁ : S₁ → ℤ} {d₀ : S₀ → ℤ}
    (hkd : ∀ p₁ p₀, k p₁ p₀ ≠ 0 → d₀ p₀ = d₁ p₁ - 1) (e : NovikovModule R F₂)
    (hunit : ∀ p₁ p₀, ∑ᶠ t, e.val t * n p₁ t p₀ - φ p₁ p₀ =
      kernelComp k δ₀ p₁ p₀ + kernelComp δ₁ k p₁ p₀)
    {i : ℤ} {a : NovikovModule R F₁}
    (ha : a ∈ (kernelMap hδ₁ hδ₁fin).cocycles (gradeBy R F₁ d₁) i) :
    kernelProduct hn hfin a e - kernelMap hφ hφfin a ∈
      (kernelMap hδ₀ hδ₀fin).coboundaries (gradeBy R F₀ d₀) i := by
  rw [LinearMap.mem_cocycles_iff] at ha
  rw [kernelProduct_sub_kernelMap_left hn hfin hδ₀ hδ₀fin hφ hφfin hk hkfin hδ₁ hδ₁fin e hunit,
    ha.1, map_zero, add_zero]
  refine LinearMap.mem_coboundaries_iff.2 ⟨_, ?_, rfl⟩
  simpa only [sub_eq_add_neg] using kernelMap_mem_gradeBy hk hkfin
    (fun p₁ p₀ h => by rw [hkd p₁ p₀ h, sub_eq_add_neg]) ha.2

end Left

end Homotopy

section Cohomology

variable {S : Type*} [DecidableEq S] {F : S → ℝ} {d : S → ℤ} {ε : ℤ}
  {δ : S → S → R} (hδ : ∀ p q, δ p q ≠ 0 → F q ≤ F p + C₀)
  (hδfin : ∀ p, δ p ∈ NovikovModule R F)
  {k : S → S → R} (hk : ∀ p q, k p q ≠ 0 → F q ≤ F p + Ck) (hkfin : ∀ p, k p ∈ NovikovModule R F)
  (hkd : ∀ p q, k p q ≠ 0 → d q = d p - 1)

section UnitMk

variable {d₁ : S₁ → ℤ} {n : S₁ → S → S → R}
  (hn : ∀ p₁ p p₀, n p₁ p p₀ ≠ 0 → F p₀ ≤ F₁ p₁ + F p + C)
  (hfin : ∀ p₁ p, n p₁ p ∈ NovikovModule R F)
  {δ₁ : S₁ → S₁ → R} (hδ₁ : ∀ p q, δ₁ p q ≠ 0 → F₁ q ≤ F₁ p + Cδ)
  (hδ₁fin : ∀ p, δ₁ p ∈ NovikovModule R F₁)
  (hdeg : ∀ {i j : ℤ} {a : NovikovModule R F₁} {b : NovikovModule R F},
    a ∈ gradeBy R F₁ d₁ i → b ∈ gradeBy R F d j →
      kernelProduct hn hfin a b ∈ gradeBy R F d (i + j + ε))
  (hL : ∀ {i : ℤ} {a : NovikovModule R F₁}, a ∈ gradeBy R F₁ d₁ i → ∀ b,
    kernelMap hδ hδfin (kernelProduct hn hfin a b) =
      kernelProduct hn hfin (kernelMap hδ₁ hδ₁fin a) b +
        negOnePowCast R i • kernelProduct hn hfin a (kernelMap hδ hδfin b))

include hk hkfin hkd in
/-- **The unit on cohomology, on the left.** Let `⋆` be a product with a common complex as its
second input and its output, obeying the Leibniz rule and shifting degree by `ε`, so that it
induces a product on degree-wise cohomology. Suppose that a cocycle `e` of degree `i` of the first
input is a unit up to a kernel homotopy `k` lowering degree by one,

`∑ₜ e(t) n(t, p, p₀) - [p = p₀] = (k δ + δ k)(p, p₀)`.

Then the class of `e` is a left identity for the product on cohomology: `[e] ⋆ [b] = [b]` for
every cocycle `b` of degree `j`, where `i + j + ε = j`. -/
theorem cohomologyProduct_kernelProduct_unit_mk {i j : ℤ} (hij : i + j + ε = j)
    (e : (kernelMap hδ₁ hδ₁fin).cocycles (gradeBy R F₁ d₁) i)
    (hunit : ∀ p p₀, ∑ᶠ t, (e : NovikovModule R F₁).val t * n t p p₀ - (if p = p₀ then 1 else 0) =
      kernelComp k δ p p₀ + kernelComp δ k p p₀)
    (b : (kernelMap hδ hδfin).cocycles (gradeBy R F d) j) :
    LinearMap.cohomologyProduct (kernelProduct hn hfin) hdeg hL hij (Submodule.Quotient.mk e)
      (Submodule.Quotient.mk b) = Submodule.Quotient.mk b := by
  have h := kernelProduct_sub_kernelMap_mem_coboundaries_right hn hfin hδ hδfin
    (fun p q h => potential_le_of_diagonal_ne_zero (s := fun _ => (1 : R)) h)
    (diagonal_mem fun _ => 1) hk hkfin hδ hδfin
    hkd e hunit b.2
  rw [kernelMap_eq_id, LinearMap.id_apply] at h
  rw [LinearMap.cohomologyProduct_mk, LinearMap.cohomology_mk_eq_mk_iff]
  exact h

end UnitMk

section MkUnit

variable {d₂ : S₂ → ℤ} {n : S → S₂ → S → R}
  (hn : ∀ p p₂ p₀, n p p₂ p₀ ≠ 0 → F p₀ ≤ F p + F₂ p₂ + C)
  (hfin : ∀ p p₂, n p p₂ ∈ NovikovModule R F)
  {δ₂ : S₂ → S₂ → R} (hδ₂ : ∀ p q, δ₂ p q ≠ 0 → F₂ q ≤ F₂ p + Cδ)
  (hδ₂fin : ∀ p, δ₂ p ∈ NovikovModule R F₂)
  (hdeg : ∀ {i j : ℤ} {a : NovikovModule R F} {b : NovikovModule R F₂},
    a ∈ gradeBy R F d i → b ∈ gradeBy R F₂ d₂ j →
      kernelProduct hn hfin a b ∈ gradeBy R F d (i + j + ε))
  (hL : ∀ {i : ℤ} {a : NovikovModule R F}, a ∈ gradeBy R F d i → ∀ b,
    kernelMap hδ hδfin (kernelProduct hn hfin a b) =
      kernelProduct hn hfin (kernelMap hδ hδfin a) b +
        negOnePowCast R i • kernelProduct hn hfin a (kernelMap hδ₂ hδ₂fin b))

include hk hkfin hkd in
/-- **The unit on cohomology, on the right.** Let `⋆` be a product with a common complex as its
first input and its output, obeying the Leibniz rule and shifting degree by `ε`, so that it
induces a product on degree-wise cohomology. Suppose that a cocycle `e` of degree `j` of the
second input is a unit up to a kernel homotopy `k` lowering degree by one,

`∑ₜ e(t) n(p, t, p₀) - [p = p₀] = (k δ + δ k)(p, p₀)`.

Then the class of `e` is a right identity for the product on cohomology: `[a] ⋆ [e] = [a]` for
every cocycle `a` of degree `i`, where `i + j + ε = i`. -/
theorem cohomologyProduct_kernelProduct_mk_unit {i j : ℤ} (hij : i + j + ε = i)
    (a : (kernelMap hδ hδfin).cocycles (gradeBy R F d) i)
    (e : (kernelMap hδ₂ hδ₂fin).cocycles (gradeBy R F₂ d₂) j)
    (hunit : ∀ p p₀, ∑ᶠ t, (e : NovikovModule R F₂).val t * n p t p₀ - (if p = p₀ then 1 else 0) =
      kernelComp k δ p p₀ + kernelComp δ k p p₀) :
    LinearMap.cohomologyProduct (kernelProduct hn hfin) hdeg hL hij (Submodule.Quotient.mk a)
      (Submodule.Quotient.mk e) = Submodule.Quotient.mk a := by
  have h := kernelProduct_sub_kernelMap_mem_coboundaries_left hn hfin hδ hδfin
    (fun p q h => potential_le_of_diagonal_ne_zero (s := fun _ => (1 : R)) h)
    (diagonal_mem fun _ => 1) hk hkfin hδ hδfin
    hkd e hunit a.2
  rw [kernelMap_eq_id, LinearMap.id_apply] at h
  rw [LinearMap.cohomologyProduct_mk, LinearMap.cohomology_mk_eq_mk_iff]
  exact h

end MkUnit

end Cohomology

end NovikovModule

end TauCeti

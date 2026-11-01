/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Grading
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# The Leibniz rule for supported products and the product on cohomology

Let `n : S₁ → S₂ → S₀ → R` be a supported product kernel and let `δ₁`, `δ₂`, `δ₀` be supported
kernels on the generators of the two inputs and the output, with linear maps
`NovikovModule.kernelMap` on completed combinations. Grade the first input by `d₁ : S₁ → ℤ`.
Counting the ends of one-dimensional moduli spaces of a product operation gives, for all
generators `p₁`, `p₂`, `p₀`, the identity between kernels

`∑ n(p₁, p₂, p) δ₀(p, p₀) = ∑ δ₁(p₁, p) n(p, p₂, p₀) + (-1)^(d₁ p₁) ∑ δ₂(p₂, p) n(p₁, p, p₀)`.

This file shows that it implies the Leibniz rule

`δ₀ (a ⋆ b) = δ₁ a ⋆ b + (-1)^i a ⋆ δ₂ b`

for every completed combination `a` of degree `i` and every completed combination `b`
(`NovikovModule.kernelMap_kernelProduct_eq_add`). Both sides are completed, not finite, sums, and
the identity uses the composite kernels of `TauCeti.RingTheory.NovikovModule.Bilinear`.

For an endomorphism `D` of a completed module graded by `d : S → ℤ`, the degree-`i` cocycles are
the homogeneous combinations of degree `i` killed by `D`, the degree-`i` coboundaries are the
images of homogeneous combinations of degree `i - 1`, and the degree-`i` cohomology is the
quotient of the first by the second (`NovikovModule.cohomology`). This is the cohomology of the
cochain convention, in which the differential raises degree by one. It is formed degree by
degree: a completed combination need not be a sum of homogeneous ones.

If the product kernel has degree shift `ε`, the Leibniz rule shows that the product of two
cocycles is a cocycle, and that the product of a cocycle with a coboundary, in either order, is a
coboundary. Hence the product descends to a bilinear map on cohomology
`H^i ⊗ H^j → H^(i + j + ε)` (`NovikovModule.cohomologyProduct`). For the pair-of-pants product
on Hamiltonian Floer cochains regraded by `n - μ`, the shift is `ε = 0`.

## Main definitions

* `TauCeti.NovikovModule.cocycles`, `TauCeti.NovikovModule.coboundaries`: the degree-`i`
  cocycles and coboundaries of an endomorphism of a graded completed module.
* `TauCeti.NovikovModule.cohomology`: the degree-`i` cohomology.
* `TauCeti.NovikovModule.cohomologyProduct`: the product on cohomology induced by a supported
  product kernel obeying the Leibniz identity.

## Main results

* `TauCeti.NovikovModule.kernelMap_kernelProduct_eq_add`: the Leibniz rule on completed
  combinations, from the Leibniz identity between kernels.
* `TauCeti.NovikovModule.coboundaries_le_cocycles`: coboundaries are cocycles for a differential
  of degree one.
* `TauCeti.NovikovModule.kernelProduct_mem_cocycles`,
  `TauCeti.NovikovModule.kernelProduct_mem_coboundaries_of_left`,
  `TauCeti.NovikovModule.kernelProduct_mem_coboundaries_of_right`: products of cocycles are
  cocycles, and products with a coboundary are coboundaries.
* `TauCeti.NovikovModule.cohomologyProduct_mk`: the product on cohomology is computed on
  representing cocycles.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the pair-of-pants product and its chain-map property.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
-/

public section

noncomputable section

open Function

namespace TauCeti

namespace NovikovModule

section Cohomology

variable {R S : Type*} [Ring R] {F : S → ℝ}
  (D : NovikovModule R F →ₗ[R] NovikovModule R F) (d : S → ℤ) (i : ℤ)

/-- The degree-`i` cocycles of an endomorphism `D` of a graded completed module: the
homogeneous completed combinations of degree `i` which `D` sends to zero. -/
def cocycles : Submodule R (NovikovModule R F) :=
  LinearMap.ker D ⊓ gradeBy R F d i

/-- The degree-`i` coboundaries of an endomorphism `D` of a graded completed module: the images
under `D` of the homogeneous completed combinations of degree `i - 1`. -/
def coboundaries : Submodule R (NovikovModule R F) :=
  (gradeBy R F d (i - 1)).map D

/-- The degree-`i` cohomology of an endomorphism `D` of a graded completed module: its degree-`i`
cocycles modulo those which are degree-`i` coboundaries. -/
abbrev cohomology : Type _ :=
  cocycles D d i ⧸ (coboundaries D d i).comap (cocycles D d i).subtype

variable {D d i}

/-- A cocycle of degree `i` is a homogeneous combination of degree `i` killed by `D`. -/
@[simp]
theorem mem_cocycles_iff {a : NovikovModule R F} :
    a ∈ cocycles D d i ↔ D a = 0 ∧ a ∈ gradeBy R F d i :=
  Iff.rfl

/-- A coboundary of degree `i` is the image of a homogeneous combination of degree `i - 1`. -/
@[simp]
theorem mem_coboundaries_iff {a : NovikovModule R F} :
    a ∈ coboundaries D d i ↔ ∃ x ∈ gradeBy R F d (i - 1), D x = a :=
  Iff.rfl

/-- If `D` squares to zero and raises degrees by one on homogeneous combinations of degree
`i - 1`, as a differential of degree one does, then every degree-`i` coboundary is a cocycle. -/
theorem coboundaries_le_cocycles (hD : ∀ x ∈ gradeBy R F d (i - 1), D (D x) = 0)
    (hdeg : ∀ x ∈ gradeBy R F d (i - 1), D x ∈ gradeBy R F d i) :
    coboundaries D d i ≤ cocycles D d i := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨hD x hx, hdeg x hx⟩

end Cohomology

section Product

variable {R S₁ S₂ S₀ : Type*} [CommRing R] {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ} {F₀ : S₀ → ℝ}
  {C C₁ C₂ C₀ : ℝ} {n : S₁ → S₂ → S₀ → R}
  (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
  (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)
  {δ₁ : S₁ → S₁ → R} (hδ₁ : ∀ p q, δ₁ p q ≠ 0 → F₁ q ≤ F₁ p + C₁)
  (hδ₁fin : ∀ p, δ₁ p ∈ NovikovModule R F₁)
  {δ₂ : S₂ → S₂ → R} (hδ₂ : ∀ p q, δ₂ p q ≠ 0 → F₂ q ≤ F₂ p + C₂)
  (hδ₂fin : ∀ p, δ₂ p ∈ NovikovModule R F₂)
  {δ₀ : S₀ → S₀ → R} (hδ₀ : ∀ p q, δ₀ p q ≠ 0 → F₀ q ≤ F₀ p + C₀)
  (hδ₀fin : ∀ p, δ₀ p ∈ NovikovModule R F₀)
  {d₁ : S₁ → ℤ}

/-- On a homogeneous first input of degree `i`, the product only depends on the kernel at
generators of degree `i`: if there the kernel `k` is `k₁ + c k₂`, then so is the product. -/
private theorem kernelProduct_eq_add_smul_of_mem_gradeBy {C' C'' C''' : ℝ}
    {k k₁ k₂ : S₁ → S₂ → S₀ → R}
    (hk : ∀ p₁ p₂ p₀, k p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C')
    (hkfin : ∀ p₁ p₂, k p₁ p₂ ∈ NovikovModule R F₀)
    (hk₁ : ∀ p₁ p₂ p₀, k₁ p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C'')
    (hk₁fin : ∀ p₁ p₂, k₁ p₁ p₂ ∈ NovikovModule R F₀)
    (hk₂ : ∀ p₁ p₂ p₀, k₂ p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C''')
    (hk₂fin : ∀ p₁ p₂, k₂ p₁ p₂ ∈ NovikovModule R F₀) {i : ℤ} {c : R}
    (h : ∀ p₁, d₁ p₁ = i → ∀ p₂ p₀, k p₁ p₂ p₀ = k₁ p₁ p₂ p₀ + c * k₂ p₁ p₂ p₀)
    {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ d₁ i) (b : NovikovModule R F₂) :
    kernelProduct hk hkfin a b =
      kernelProduct hk₁ hk₁fin a b + c • kernelProduct hk₂ hk₂fin a b := by
  ext p₀
  simp only [kernelProduct_apply_val, Submodule.coe_add, Pi.add_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [mul_finsum' _ c (finite_support_mul_kernel hk₂ a b p₀),
    ← finsum_add_distrib (finite_support_mul_kernel hk₁ a b p₀)
      ((finite_support_mul_kernel hk₂ a b p₀).subset (support_mul_subset_right _ _))]
  refine finsum_congr fun q => ?_
  by_cases hq : a.val q.1 = 0
  · simp [hq]
  · rw [h q.1 (mem_gradeBy_iff.1 ha q.1 hq)]
    ring

/-- **The Leibniz rule.** Suppose the product kernel `n` and the kernels `δ₁`, `δ₂`, `δ₀` obey
the Leibniz identity `n ∘ δ₀ = δ₁ ∘ n + (-1)^(d₁) (δ₂ ∘ n)` between composite kernels, which in
Floer theory is the count of the ends of one-dimensional product moduli spaces. Then for a
completed combination `a` of degree `i` and any completed combination `b`,
`δ₀ (a ⋆ b) = δ₁ a ⋆ b + (-1)^i a ⋆ δ₂ b`. -/
theorem kernelMap_kernelProduct_eq_add
    (hL : ∀ p₁ p₂ p₀, kernelComp (n p₁) δ₀ p₂ p₀ =
      kernelComp δ₁ (fun p => n p p₂) p₁ p₀ +
        ((d₁ p₁).negOnePow : R) * kernelComp δ₂ (n p₁) p₂ p₀)
    {i : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ d₁ i) (b : NovikovModule R F₂) :
    kernelMap hδ₀ hδ₀fin (kernelProduct hn hfin a b) =
      kernelProduct hn hfin (kernelMap hδ₁ hδ₁fin a) b +
        (i.negOnePow : R) • kernelProduct hn hfin a (kernelMap hδ₂ hδ₂fin b) := by
  -- The three composite kernels are supported, so each side is a product of composite kernels.
  have h₀ (p₁ : S₁) (p₂ : S₂) (p₀ : S₀) (h : kernelComp (n p₁) δ₀ p₂ p₀ ≠ 0) :
      F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + (C + C₀) := by
    linarith [potential_le_of_kernelComp_ne_zero (hn p₁ p₂) (hδ₀ · p₀) h]
  have h₁ (p₃ : S₁) (p₂ : S₂) (p₀ : S₀) (h : kernelComp δ₁ (fun p => n p p₂) p₃ p₀ ≠ 0) :
      F₀ p₀ ≤ F₁ p₃ + F₂ p₂ + (C₁ + C) := by
    linarith [potential_le_of_kernelComp_ne_zero (C' := F₂ p₂ + C) (hδ₁ p₃)
      (fun p hp => by linarith [hn p p₂ p₀ hp]) h]
  have h₂ (p₁ : S₁) (p₃ : S₂) (p₀ : S₀) (h : kernelComp δ₂ (n p₁) p₃ p₀ ≠ 0) :
      F₀ p₀ ≤ F₁ p₁ + F₂ p₃ + (C₂ + C) := by
    linarith [potential_le_of_kernelComp_ne_zero (C' := F₁ p₁ + C) (hδ₂ p₃)
      (fun p hp => by linarith [hn p₁ p p₀ hp]) h]
  rw [kernelMap_kernelProduct hn hfin hδ₀ hδ₀fin h₀
      (fun p₁ p₂ => kernelComp_mem hδ₀ hδ₀fin (hfin p₁ p₂)),
    kernelProduct_kernelMap_left hn hfin hδ₁ hδ₁fin h₁
      (fun p₃ p₂ => kernelComp_mem (C' := F₂ p₂ + C)
        (fun p p₀ hp => by linarith [hn p p₂ p₀ hp]) (hfin · p₂) (hδ₁fin p₃)),
    kernelProduct_kernelMap_right hn hfin hδ₂ hδ₂fin h₂
      (fun p₁ p₃ => kernelComp_mem (C' := F₁ p₁ + C)
        (fun p p₀ hp => by linarith [hn p₁ p p₀ hp]) (hfin p₁) (hδ₂fin p₃))]
  exact kernelProduct_eq_add_smul_of_mem_gradeBy _ _ _ _ _ _
    (fun p₁ hp₁ p₂ p₀ => by rw [hL, hp₁]) ha b

variable {d₂ : S₂ → ℤ} {d₀ : S₀ → ℤ} {ε : ℤ}
  (hL : ∀ p₁ p₂ p₀, kernelComp (n p₁) δ₀ p₂ p₀ =
    kernelComp δ₁ (fun p => n p p₂) p₁ p₀ +
      ((d₁ p₁).negOnePow : R) * kernelComp δ₂ (n p₁) p₂ p₀)
  (hd : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → d₀ p₀ = d₁ p₁ + d₂ p₂ + ε)

include hL hd

/-- The product of two cocycles is a cocycle, of the sum of their degrees and the degree shift
of the product kernel. -/
theorem kernelProduct_mem_cocycles {i j : ℤ} {a : NovikovModule R F₁} {b : NovikovModule R F₂}
    (ha : a ∈ cocycles (kernelMap hδ₁ hδ₁fin) d₁ i)
    (hb : b ∈ cocycles (kernelMap hδ₂ hδ₂fin) d₂ j) :
    kernelProduct hn hfin a b ∈ cocycles (kernelMap hδ₀ hδ₀fin) d₀ (i + j + ε) := by
  rw [mem_cocycles_iff] at ha hb ⊢
  refine ⟨?_, kernelProduct_mem_gradeBy hn hfin hd ha.2 hb.2⟩
  rw [kernelMap_kernelProduct_eq_add hn hfin hδ₁ hδ₁fin hδ₂ hδ₂fin hδ₀ hδ₀fin hL ha.2, ha.1,
    hb.1]
  simp

/-- The product of a coboundary with a cocycle is a coboundary. -/
theorem kernelProduct_mem_coboundaries_of_left {i j : ℤ} {a : NovikovModule R F₁}
    {b : NovikovModule R F₂} (ha : a ∈ coboundaries (kernelMap hδ₁ hδ₁fin) d₁ i)
    (hb : b ∈ cocycles (kernelMap hδ₂ hδ₂fin) d₂ j) :
    kernelProduct hn hfin a b ∈ coboundaries (kernelMap hδ₀ hδ₀fin) d₀ (i + j + ε) := by
  obtain ⟨x, hx, rfl⟩ := mem_coboundaries_iff.1 ha
  rw [mem_cocycles_iff] at hb
  refine mem_coboundaries_iff.2 ⟨kernelProduct hn hfin x b, ?_, ?_⟩
  · have he : i - 1 + j + ε = i + j + ε - 1 := by ring
    simpa only [he] using kernelProduct_mem_gradeBy hn hfin hd hx hb.2
  · rw [kernelMap_kernelProduct_eq_add hn hfin hδ₁ hδ₁fin hδ₂ hδ₂fin hδ₀ hδ₀fin hL hx, hb.1]
    simp

/-- The product of a cocycle with a coboundary is a coboundary. -/
theorem kernelProduct_mem_coboundaries_of_right {i j : ℤ} {a : NovikovModule R F₁}
    {b : NovikovModule R F₂} (ha : a ∈ cocycles (kernelMap hδ₁ hδ₁fin) d₁ i)
    (hb : b ∈ coboundaries (kernelMap hδ₂ hδ₂fin) d₂ j) :
    kernelProduct hn hfin a b ∈ coboundaries (kernelMap hδ₀ hδ₀fin) d₀ (i + j + ε) := by
  obtain ⟨y, hy, rfl⟩ := mem_coboundaries_iff.1 hb
  rw [mem_cocycles_iff] at ha
  have hs : (i.negOnePow : R) * (i.negOnePow : R) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  refine mem_coboundaries_iff.2 ⟨(i.negOnePow : R) • kernelProduct hn hfin a y, ?_, ?_⟩
  · have he : i + (j - 1) + ε = i + j + ε - 1 := by ring
    exact Submodule.smul_mem _ _
      (by simpa only [he] using kernelProduct_mem_gradeBy hn hfin hd ha.2 hy)
  · rw [map_smul, kernelMap_kernelProduct_eq_add hn hfin hδ₁ hδ₁fin hδ₂ hδ₂fin hδ₀ hδ₀fin hL ha.2,
      ha.1, smul_add, smul_smul, hs, one_smul]
    simp

/-- **The product on cohomology.** A supported product kernel of degree shift `ε` obeying the
Leibniz identity with the differentials induces a bilinear map from degree-`i` and degree-`j`
cohomology to degree-`(i + j + ε)` cohomology. -/
def cohomologyProduct (i j : ℤ) :
    cohomology (kernelMap hδ₁ hδ₁fin) d₁ i →ₗ[R] cohomology (kernelMap hδ₂ hδ₂fin) d₂ j →ₗ[R]
      cohomology (kernelMap hδ₀ hδ₀fin) d₀ (i + j + ε) :=
  LinearMap.liftQ₂ _ _
    (LinearMap.mk₂ R
      (fun a b => Submodule.Quotient.mk
        ⟨kernelProduct hn hfin a b,
          kernelProduct_mem_cocycles hn hfin hδ₁ hδ₁fin hδ₂ hδ₂fin hδ₀ hδ₀fin hL hd a.2 b.2⟩)
      (fun a a' b => by
        rw [← Submodule.Quotient.mk_add]
        exact congrArg _ (Subtype.ext (by simp)))
      (fun c a b => by
        rw [← Submodule.Quotient.mk_smul]
        exact congrArg _ (Subtype.ext (by simp)))
      (fun a b b' => by
        rw [← Submodule.Quotient.mk_add]
        exact congrArg _ (Subtype.ext (by simp)))
      (fun c a b => by
        rw [← Submodule.Quotient.mk_smul]
        exact congrArg _ (Subtype.ext (by simp))))
    (fun a ha => LinearMap.ext fun b => (Submodule.Quotient.mk_eq_zero _).2
      (kernelProduct_mem_coboundaries_of_left hn hfin hδ₁ hδ₁fin hδ₂ hδ₂fin hδ₀ hδ₀fin hL hd ha
        b.2))
    (fun b hb => LinearMap.ext fun a => (Submodule.Quotient.mk_eq_zero _).2
      (kernelProduct_mem_coboundaries_of_right hn hfin hδ₁ hδ₁fin hδ₂ hδ₂fin hδ₀ hδ₀fin hL hd a.2
        hb))

/-- The product on cohomology of the classes of two cocycles is the class of their product. -/
@[simp]
theorem cohomologyProduct_mk {i j : ℤ} (a : cocycles (kernelMap hδ₁ hδ₁fin) d₁ i)
    (b : cocycles (kernelMap hδ₂ hδ₂fin) d₂ j) :
    cohomologyProduct hn hfin hδ₁ hδ₁fin hδ₂ hδ₂fin hδ₀ hδ₀fin hL hd i j
        (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk ⟨kernelProduct hn hfin a b,
        kernelProduct_mem_cocycles hn hfin hδ₁ hδ₁fin hδ₂ hδ₂fin hδ₀ hδ₀fin hL hd a.2 b.2⟩ :=
  (rfl)

end Product

end NovikovModule

end TauCeti

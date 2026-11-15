/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Grading
public import TauCeti.RingTheory.NovikovModule.MapOfMatrix
public import TauCeti.Algebra.Ring.NegOnePow

/-!
# The Leibniz rule for supported products

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

If the product kernel also has degree shift `ε` (`NovikovModule.kernelProduct_mem_gradeBy`), the
Leibniz rule is exactly the hypothesis under which `LinearMap.cohomologyProduct` descends the
product to a bilinear map `H^i × H^j → H^k`, for `k = i + j + ε`, on the degree-wise cohomology of
the three kernel maps graded by `NovikovModule.gradeBy`. For the pair-of-pants product, whose
kernel has raw Floer degree minus the half-dimension, the product preserves degree on combinations
regraded by the half-dimension minus the raw degree
(`TauCeti.Floer.kernelProduct_mem_cochain_gradeBy`).

On finite unions of torsors with invariant kernels, products and maps are given by matrices of
Novikov series relative to reference generators (`NovikovModule.novikovProductOfMatrix`,
`NovikovModule.novikovMapOfMatrix`). For matrices `Q`, `D₁`, `D₂`, `D₀` the Leibniz identity
becomes the identity `∑ₖ Qᵢⱼₖ D₀ₖₗ = ∑ₖ D₁ᵢₖ Qₖⱼₗ + (-1)^(d₁ (r₁ i)) ∑ₖ D₂ⱼₖ Qᵢₖₗ` between finite
sums of Novikov series, and it implies the Leibniz rule for the product and maps of the matrices
(`NovikovModule.novikovMapOfMatrix_novikovProductOfMatrix_eq_add`), provided degrees change by
even amounts within each orbit, so that the sign only depends on the orbit. This is the form in
which counts indexed by classes of a period group enter.

## Main results

* `TauCeti.NovikovModule.kernelMap_kernelProduct_eq_add`: the Leibniz rule on completed
  combinations, from the Leibniz identity between kernels.
* `TauCeti.NovikovModule.novikovMapOfMatrix_novikovProductOfMatrix_eq_add`: the Leibniz rule for
  matrices of Novikov series, from the Leibniz identity between matrices.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the pair-of-pants product and its chain-map property.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
-/

public section

noncomputable section

namespace TauCeti

namespace NovikovModule

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

/-- **The Leibniz rule.** Suppose the product kernel `n` and the kernels `δ₁`, `δ₂`, `δ₀` obey
the Leibniz identity `n ∘ δ₀ = δ₁ ∘ n + (-1)^(d₁) (δ₂ ∘ n)` between composite kernels, which in
Floer theory is the count of the ends of one-dimensional product moduli spaces. Then for a
completed combination `a` of degree `i` and any completed combination `b`,
`δ₀ (a ⋆ b) = δ₁ a ⋆ b + (-1)^i a ⋆ δ₂ b`. -/
theorem kernelMap_kernelProduct_eq_add
    (hL : ∀ p₁ p₂ p₀, kernelComp (n p₁) δ₀ p₂ p₀ =
      kernelComp δ₁ (fun p => n p p₂) p₁ p₀ +
        negOnePowCast R (d₁ p₁) * kernelComp δ₂ (n p₁) p₂ p₀)
    {i : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ d₁ i) (b : NovikovModule R F₂) :
    kernelMap hδ₀ hδ₀fin (kernelProduct hn hfin a b) =
      kernelProduct hn hfin (kernelMap hδ₁ hδ₁fin a) b +
        negOnePowCast R i • kernelProduct hn hfin a (kernelMap hδ₂ hδ₂fin b) := by
  -- The potential bound of `n`, regrouped with one input generator fixed.
  have hn₁ (p₂ : S₂) (p : S₁) (p₀ : S₀) (hp : n p p₂ p₀ ≠ 0) : F₀ p₀ ≤ F₁ p + (F₂ p₂ + C) := by
    linarith [hn p p₂ p₀ hp]
  have hn₂ (p₁ : S₁) (p : S₂) (p₀ : S₀) (hp : n p₁ p p₀ ≠ 0) : F₀ p₀ ≤ F₂ p + (F₁ p₁ + C) := by
    linarith [hn p₁ p p₀ hp]
  -- The three composite kernels are supported, so each side is a product of composite kernels.
  have h₀ (p₁ : S₁) (p₂ : S₂) (p₀ : S₀) (h : kernelComp (n p₁) δ₀ p₂ p₀ ≠ 0) :
      F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + (C + C₀) := by
    linarith [potential_le_of_kernelComp_ne_zero (hn p₁ p₂) (hδ₀ · p₀) h]
  have h₁ (p₃ : S₁) (p₂ : S₂) (p₀ : S₀) (h : kernelComp δ₁ (fun p => n p p₂) p₃ p₀ ≠ 0) :
      F₀ p₀ ≤ F₁ p₃ + F₂ p₂ + (C₁ + C) := by
    linarith [potential_le_of_kernelComp_ne_zero (hδ₁ p₃) (fun p hp => hn₁ p₂ p p₀ hp) h]
  have h₂ (p₁ : S₁) (p₃ : S₂) (p₀ : S₀) (h : kernelComp δ₂ (n p₁) p₃ p₀ ≠ 0) :
      F₀ p₀ ≤ F₁ p₁ + F₂ p₃ + (C₂ + C) := by
    linarith [potential_le_of_kernelComp_ne_zero (hδ₂ p₃) (fun p hp => hn₂ p₁ p p₀ hp) h]
  have h₁fin (p₃ : S₁) (p₂ : S₂) : kernelComp δ₁ (fun p => n p p₂) p₃ ∈ NovikovModule R F₀ :=
    kernelComp_mem (hn₁ p₂) (hfin · p₂) (hδ₁fin p₃)
  have h₂fin (p₁ : S₁) (p₃ : S₂) : kernelComp δ₂ (n p₁) p₃ ∈ NovikovModule R F₀ :=
    kernelComp_mem (hn₂ p₁) (hfin p₁) (hδ₂fin p₃)
  -- On generators of degree `i`, the left composite is a combination of the right ones.
  set k₁ : S₁ → S₂ → S₀ → R := fun p₁ p₂ => kernelComp δ₁ (fun p => n p p₂) p₁
  set k₂ : S₁ → S₂ → S₀ → R := fun p₁ => kernelComp δ₂ (n p₁)
  have hk₂ (p₁ : S₁) (p₂ : S₂) (p₀ : S₀) (h : (negOnePowCast R i • k₂) p₁ p₂ p₀ ≠ 0) :
      F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + (C₂ + C) :=
    h₂ p₁ p₂ p₀ (right_ne_zero_of_mul h)
  have hk (p₁ : S₁) (p₂ : S₂) (p₀ : S₀) (h : (k₁ + negOnePowCast R i • k₂) p₁ p₂ p₀ ≠ 0) :
      F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + max (C₁ + C) (C₂ + C) := by
    by_cases h' : k₁ p₁ p₂ p₀ = 0
    · have h'' : (negOnePowCast R i • k₂) p₁ p₂ p₀ ≠ 0 := by simpa [h'] using h
      linarith [hk₂ p₁ p₂ p₀ h'', le_max_right (C₁ + C) (C₂ + C)]
    · linarith [h₁ p₁ p₂ p₀ h', le_max_left (C₁ + C) (C₂ + C)]
  have hk₂fin (p₁ : S₁) (p₂ : S₂) : (negOnePowCast R i • k₂) p₁ p₂ ∈ NovikovModule R F₀ :=
    Submodule.smul_mem _ _ (h₂fin p₁ p₂)
  have hkfin (p₁ : S₁) (p₂ : S₂) :
      (k₁ + negOnePowCast R i • k₂) p₁ p₂ ∈ NovikovModule R F₀ :=
    add_mem (h₁fin p₁ p₂) (hk₂fin p₁ p₂)
  rw [kernelMap_kernelProduct hn hfin hδ₀ hδ₀fin h₀
      (fun p₁ p₂ => kernelComp_mem hδ₀ hδ₀fin (hfin p₁ p₂)),
    kernelProduct_kernelMap_left hn hfin hδ₁ hδ₁fin h₁ h₁fin,
    kernelProduct_kernelMap_right hn hfin hδ₂ hδ₂fin h₂ h₂fin,
    kernelProduct_congr_of_mem_gradeBy _ _ hk hkfin
      (fun p₁ hp₁ => funext₂ fun p₂ p₀ => by simp [k₁, k₂, hL, hp₁]) ha b,
    kernelProduct_add h₁ h₁fin hk₂ hk₂fin hk hkfin, kernelProduct_smul h₂ h₂fin _ hk₂ hk₂fin,
    LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]

section Matrix

variable {R H ι₁ ι₂ ι₀ : Type*} [CommRing R] [AddCommGroup H] {N : H →+ ℝ}
  {P₁ : ι₁ → Type*} {P₂ : ι₂ → Type*} {P₀ : ι₀ → Type*}
  [∀ i, AddTorsor H (P₁ i)] [∀ j, AddTorsor H (P₂ j)] [∀ k, AddTorsor H (P₀ k)]
  {F₁ : (Σ i, P₁ i) → ℝ} {F₂ : (Σ j, P₂ j) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  (hF₁ : ∀ i h (p : P₁ i), F₁ ⟨i, h +ᵥ p⟩ = F₁ ⟨i, p⟩ - N h)
  (hF₂ : ∀ j h (p : P₂ j), F₂ ⟨j, h +ᵥ p⟩ = F₂ ⟨j, p⟩ - N h)
  (hF₀ : ∀ k h (p : P₀ k), F₀ ⟨k, h +ᵥ p⟩ = F₀ ⟨k, p⟩ - N h)
  (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₀ : ∀ k, P₀ k)

variable [Fintype ι₁] [Fintype ι₂] [Fintype ι₀]

/-- **The Leibniz rule for matrices of Novikov series.** Let `Q` be the matrix of a product and
`D₁`, `D₂`, `D₀` the matrices of maps on the two inputs and the output, relative to reference
generators. Grade the first input by `d₁`, with even changes of degree within each orbit. If the
matrices obey the Leibniz identity

`∑ₖ Qᵢⱼₖ D₀ₖₗ = ∑ₖ D₁ᵢₖ Qₖⱼₗ + (-1)^(d₁ (r₁ i)) ∑ₖ D₂ⱼₖ Qᵢₖₗ`,

which in Floer theory is the count of the ends of one-dimensional product moduli spaces between
reference generators, class by class, then for a completed combination `a` of degree `e` and any
completed combination `b`, `D₀ (a ⋆ b) = D₁ a ⋆ b + (-1)^e a ⋆ D₂ b`. -/
theorem novikovMapOfMatrix_novikovProductOfMatrix_eq_add
    (Q : ι₁ → ι₂ → ι₀ → NovikovSeries R H N) (D₁ : Matrix ι₁ ι₁ (NovikovSeries R H N))
    (D₂ : Matrix ι₂ ι₂ (NovikovSeries R H N)) (D₀ : Matrix ι₀ ι₀ (NovikovSeries R H N))
    {d₁ : (Σ i, P₁ i) → ℤ} (hd₁ : ∀ i (h : H) (p : P₁ i), Even (d₁ ⟨i, h +ᵥ p⟩ - d₁ ⟨i, p⟩))
    (hL : ∀ i j l, ∑ k, Q i j k * D₀ k l =
      ∑ k, D₁ i k * Q k j l + negOnePowCast R (d₁ ⟨i, r₁ i⟩) • ∑ k, D₂ j k * Q i k l)
    {e : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ d₁ e) (b : NovikovModule R F₂) :
    novikovMapOfMatrix hF₀ hF₀ r₀ r₀ D₀ (novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀ Q a b) =
      novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀ Q (novikovMapOfMatrix hF₁ hF₁ r₁ r₁ D₁ a) b +
        negOnePowCast R e • novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀ Q a
          (novikovMapOfMatrix hF₂ hF₂ r₂ r₂ D₂ b) := by
  refine (coordinates hF₀ r₀).injective (funext fun l => ?_)
  rw [map_add, map_smul, Pi.add_apply, Pi.smul_apply,
    coordinates_novikovMapOfMatrix_novikovProductOfMatrix,
    coordinates_novikovProductOfMatrix_novikovMapOfMatrix_left,
    coordinates_novikovProductOfMatrix_novikovMapOfMatrix_right]
  have hs := negOnePowCast_smul_coordinates_of_mem_gradeBy hF₁ r₁ hd₁ ha
  -- Termwise, this is the Leibniz identity, with the sign of the orbit of `i` replaced by the
  -- sign of the degree of `a` on its nonzero coordinates.
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hL, mul_add, mul_smul_comm, ← smul_mul_assoc, ← smul_mul_assoc, hs, smul_mul_assoc,
    smul_mul_assoc]

end Matrix

end NovikovModule

end TauCeti

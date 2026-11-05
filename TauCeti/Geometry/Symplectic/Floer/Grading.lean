/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Grading
public import TauCeti.Geometry.Symplectic.Floer.PeriodGroup

/-!
# Cochain degrees of supported Floer products

For a raw grading `μ` and half-dimension `n`, the cochain degree of a capped generator is
`n - μ`. The corresponding homogeneous completed combinations are exactly those of raw degree
`n - k`. A supported kernel of raw degree `-n` therefore gives a degree-zero product in the
cochain grading. This is a statement about the completed kernel product itself, including its
finite coefficient sums, rather than just about its expected index.

The same holds for any additive image of the cochain degree
(`TauCeti.Floer.kernelProduct_mem_map_cochain_gradeBy`), and the image that matters is the
*residue* of the cochain degree modulo the degrees `2 c₁(γ)` of the period group `Γ`. Recapping a
generator by `γ` shifts its grading by `2 c₁(γ)`, so an orbit meets infinitely many integer
degrees as soon as `c₁` is nonzero on spheres; a completed combination may then meet infinitely
many degrees and is not a finite sum of integer-homogeneous combinations. The residue, by
contrast, is constant on orbits (`TauCeti.Floer.quotientMk_sub_vadd`). By
`TauCeti.NovikovModule.isInternal_novikovGradeBy`, the completed module over finitely many orbits
is therefore the internal direct sum of its residue pieces, as a module over the Floer Novikov
ring, and the supported product is additive in residues. When `c₁` vanishes on spheres the
grading itself is constant on orbits (`TauCeti.Floer.vadd_eq_of_chern_eq_zero`), which gives the
completed integer grading of that case. Residues still determine parity, since every degree of
`Γ` is even (`TauCeti.Floer.PeriodGroup.negOnePow_eq_negOnePow_of_quotientMk_eq`); thus Koszul
signs `(-1)^(ab)` are defined on residue pieces.

The kernel's grading and support hypotheses remain explicit: establishing them for geometric
counts requires the index and compactness theorems of the chosen Floer problem. No complex,
orientation line, differential or geometric count is constructed here.

The product is `TauCeti.NovikovModule.kernelProduct`, and its homogeneity follows from
`TauCeti.NovikovModule.kernelProduct_mem_gradeBy`.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
-/

public section

namespace TauCeti.Floer

open NovikovModule

section Product

variable {R S₁ S₂ S₀ : Type*} [CommSemiring R]
  {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ} {F₀ : S₀ → ℝ}
  {C : ℝ} {κ : S₁ → S₂ → S₀ → R}
  (hκ : ∀ p₁ p₂ p₀, κ p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
  (hfin : ∀ p₁ p₂, κ p₁ p₂ ∈ NovikovModule R F₀)
  {μ₁ : S₁ → ℤ} {μ₂ : S₂ → ℤ} {μ₀ : S₀ → ℤ} {n : ℤ}
  (hμ : ∀ p₁ p₂ p₀, κ p₁ p₂ p₀ ≠ 0 → μ₀ p₀ = μ₁ p₁ + μ₂ p₂ - n)

include hμ

/-- A supported product kernel of raw Floer degree `-n` is additive in any additive image `f` of
the cochain degree `k = n - μ`; for `f` the quotient map modulo the degrees of the period group
this is the residue grading. The degree hypothesis concerns nonzero kernel coefficients, and the
conclusion concerns the actual extended bilinear product. -/
theorem kernelProduct_mem_map_cochain_gradeBy {D : Type*} [AddMonoid D] (f : ℤ →+ D)
    {i j : D} {a : NovikovModule R F₁} {b : NovikovModule R F₂}
    (ha : a ∈ gradeBy R F₁ (fun p => f (n - μ₁ p)) i)
    (hb : b ∈ gradeBy R F₂ (fun p => f (n - μ₂ p)) j) :
    kernelProduct hκ hfin a b ∈ gradeBy R F₀ (fun p => f (n - μ₀ p)) (i + j) := by
  have hm := kernelProduct_mem_gradeBy hκ hfin (d₀ := fun p => f (n - μ₀ p)) (ε := 0)
    (fun p₁ p₂ p₀ h => by
      rw [hμ p₁ p₂ p₀ h, add_zero, ← map_add]
      congr 1
      ring) ha hb
  rwa [add_zero] at hm

/-- A supported product kernel of raw Floer degree `-n` has degree zero on completed
combinations regraded by `k = n - μ`. The degree hypothesis concerns nonzero kernel
coefficients, and the conclusion concerns the actual extended bilinear product. -/
theorem kernelProduct_mem_cochain_gradeBy {i j : ℤ} {a : NovikovModule R F₁}
    {b : NovikovModule R F₂}
    (ha : a ∈ gradeBy R F₁ (fun p => n - μ₁ p) i)
    (hb : b ∈ gradeBy R F₂ (fun p => n - μ₂ p) j) :
    kernelProduct hκ hfin a b ∈ gradeBy R F₀ (fun p => n - μ₀ p) (i + j) :=
  kernelProduct_mem_map_cochain_gradeBy hκ hfin hμ (AddMonoidHom.id ℤ) ha hb

end Product

section Residue

variable {S : Type*} [AddGroup S] {ω : S →+ ℝ} {c : S →+ ℤ}

variable {ι : Type*} {P : ι → Type*} [∀ i, AddTorsor (PeriodGroup ω c) (P i)]
  {μ : (Σ i, P i) → ℤ}
  (hμ : ∀ i γ (D : P i), μ ⟨i, γ +ᵥ D⟩ = PeriodGroup.degree ω c γ + μ ⟨i, D⟩)

include hμ

/-- If recapping a generator by `γ` shifts its grading by the degree `2 c₁(γ)`, then the residue
of the cochain degree `n - μ` modulo the degrees of the period group does not depend on the cap.
Hence it is constant on each orbit, and the completed module over finitely many orbits is the
direct sum of its residue pieces as a module over the Floer Novikov ring
(`TauCeti.NovikovModule.isInternal_novikovGradeBy`). -/
theorem quotientMk_sub_vadd (n : ℤ) (i : ι) (γ : PeriodGroup ω c) (D : P i) :
    ((n - μ ⟨i, γ +ᵥ D⟩ : ℤ) : ℤ ⧸ (PeriodGroup.degree ω c).range) =
      ((n - μ ⟨i, D⟩ : ℤ) : ℤ ⧸ (PeriodGroup.degree ω c).range) :=
  QuotientAddGroup.eq_iff_sub_mem.2 ⟨-γ, by rw [hμ, map_neg]; ring⟩

/-- If the first Chern number vanishes on spherical classes, recapping does not change the
grading of a generator. Hence the integer grading is constant on each orbit, and the completed
module over finitely many orbits is the direct sum of its integer-homogeneous pieces as a module
over the Floer Novikov ring (`TauCeti.NovikovModule.isInternal_novikovGradeBy`). -/
theorem vadd_eq_of_chern_eq_zero (hc : ∀ s, c s = 0) (i : ι) (γ : PeriodGroup ω c) (D : P i) :
    μ ⟨i, γ +ᵥ D⟩ = μ ⟨i, D⟩ := by
  rw [hμ, PeriodGroup.degree_apply, PeriodGroup.chern_eq_zero hc, mul_zero, zero_add]

end Residue

end TauCeti.Floer

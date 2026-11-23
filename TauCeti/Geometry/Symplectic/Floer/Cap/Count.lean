/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Product
public import TauCeti.RingTheory.NovikovSeries.Count

/-!
# Count matrices of the pair-of-pants product from rigid solutions

The pair-of-pants product of `TauCeti.Geometry.Symplectic.Floer.Cap.Product` is built from a
matrix of Novikov series `Q i j k = ∑_A N_A q^A`, one for each triple of orbits at the ends, and
takes as hypotheses that each `Q i j k` lies in the period filtration given by the energy bound
and that its support satisfies the index condition. This file produces such a matrix from the
rigid solutions themselves and derives both hypotheses from properties of individual solutions.

For each triple `(i, j, k)` let `M i j k` be the rigid solutions with input orbits `i`, `j` and
output orbit `k`, let `A u` be the class of `u` relative to the reference caps and `w u` its
orientation sign. The matrix entry is the generating series `TauCeti.NovikovSeries.countSeries`
of the family, whose coefficient at `A` is the signed count of the solutions of class `A`.

* **Energy cutoff.** The energy of a solution `u` with reference caps is
  `E u = F₁(r₁) + F₂(r₂) - F₀(r₀) + ω(A u) - ρ u`, where `ρ u = ∫ R_K(u)` is the curvature term
  of the perturbation. If `ρ u ≥ -C`, a solution of area below `L` has energy below
  `F₁(r₁) + F₂(r₂) - F₀(r₀) + L + C`. So compactness below each energy level, finitely many
  rigid solutions there, gives finitely many below each area level, which is what the generating
  series needs (`TauCeti.Floer.finite_setOf_area_lt_of_energy`).
* **Lower support bound.** Since `E u ≥ 0`, the same bound `ρ u ≥ -C` gives
  `ω(A u) ≥ F₀(r₀) - F₁(r₁) - F₂(r₂) - C`, so the generating series lies in the period filtration
  at this level (`TauCeti.Floer.countSeries_mem_periodFiltration_of_energy`), and the product of
  the count matrix shifts action cutoffs by `C`
  (`novikovProductOfMatrix_coefficientComparison_countSeries_mem_potentialFiltration`).
* **Degree.** If every solution of nonzero sign satisfies the index condition
  `μ₀(r₀) - 2 c₁(A u) = μ₁(r₁) + μ₂(r₂) - n - ε`, so does every class counted by the generating
  series, and the product of the count matrix shifts the cochain degree `n - μ` and its residues
  by `ε`
  (`novikovProductOfMatrix_coefficientComparison_countSeries_mem_map_cochain_gradeBy_add`).

The moduli spaces, their compactness and the orientation signs are the geometric input; they are
not constructed here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the chapter on
  Floer homology and the pair-of-pants product.
-/

public section

noncomputable section

namespace TauCeti.Floer

open NovikovModule NovikovSeries PeriodGroup

section Energy

variable {R G M : Type*} [AddZeroClass G] {ωG : G →+ ℝ} {A : M → G} {E ρ : M → ℝ} {T C : ℝ}

/-- **Energy cutoff.** If each solution `u` of class `A u` has energy
`E u = T + ω(A u) - ρ u` with curvature term `ρ u ≥ -C`, and only finitely many solutions have
energy at most each level, then only finitely many solutions have area below each level. -/
theorem finite_setOf_area_lt_of_energy (hE : ∀ u, E u = T + ωG (A u) - ρ u)
    (hρ : ∀ u, -C ≤ ρ u) (hfin : ∀ L, {u | E u ≤ L}.Finite) (L : ℝ) :
    {u | ωG (A u) < L}.Finite :=
  (hfin (T + L + C)).subset fun u hu => by
    rw [Set.mem_ofPred_eq] at hu ⊢
    linarith [hE u, hρ u]

/-- **Lower support bound from the energy.** If each solution `u` of class `A u` has nonnegative
energy `E u = T + ω(A u) - ρ u` with curvature term `ρ u ≥ -C`, then every solution has area at
least `-T - C`, so the generating series of the solutions lies in the period filtration at
`-T - C`. -/
theorem countSeries_mem_periodFiltration_of_energy [AddCommGroup R] {w : M → R}
    {hfin : ∀ L : ℝ, {u | w u ≠ 0 ∧ ωG (A u) < L}.Finite} (hE₀ : ∀ u, 0 ≤ E u)
    (hE : ∀ u, E u = T + ωG (A u) - ρ u) (hρ : ∀ u, -C ≤ ρ u) :
    countSeries A w hfin ∈ periodFiltration R ωG (-T - C) :=
  countSeries_mem_periodFiltration fun u _ => by linarith [hE₀ u, hE u, hρ u]

end Energy

variable {R S : Type*} [AddCommGroup S] {ω : S →+ ℝ} {c : S →+ ℤ}
  {ι₁ ι₂ ι₀ : Type*} {P₁ : ι₁ → Type*} {P₂ : ι₂ → Type*} {P₀ : ι₀ → Type*}
  [∀ i, AddTorsor (PeriodGroup ω c) (P₁ i)] [∀ j, AddTorsor (PeriodGroup ω c) (P₂ j)]
  [∀ k, AddTorsor (PeriodGroup ω c) (P₀ k)]
  (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₀ : ∀ k, P₀ k)
  {G : Type*} [AddMonoid G] {ωG : G →+ ℝ} (q : G →+ PeriodGroup ω c)
  (hq : ∀ A, area ω c (q A) = ωG A)
  [Finite ι₁] [Finite ι₂] [Finite ι₀] {F₁ : (Σ i, P₁ i) → ℝ}
  {F₂ : (Σ j, P₂ j) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
  (hF₂ : ∀ j γ (D : P₂ j), F₂ ⟨j, γ +ᵥ D⟩ = F₂ ⟨j, D⟩ - (-area ω c) γ)
  (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)
  {M : ι₁ → ι₂ → ι₀ → Type*} (A : ∀ i j k, M i j k → G)

/-- **The product of the count matrix shifts action cutoffs by the curvature bound.** Let the
solutions of each triple `(i, j, k)` have nonnegative energies
`E u = F₁(r₁ i) + F₂(r₂ j) - F₀(r₀ k) + ω(A u) - ρ u` relative to the reference caps, with
curvature terms `ρ u ≥ -C`. Then the product given by the generating series of the solutions sends
combinations vanishing above the actions `D₁` and `D₂` to one vanishing above `D₁ + D₂ + C`. -/
theorem novikovProductOfMatrix_coefficientComparison_countSeries_mem_potentialFiltration
    [CommRing R]
    (w : ∀ i j k, M i j k → R)
    (hfin : ∀ i j k, ∀ L : ℝ, {u | w i j k u ≠ 0 ∧ ωG (A i j k u) < L}.Finite)
    {E ρ : ∀ i j k, M i j k → ℝ} {C : ℝ} (hE₀ : ∀ i j k u, 0 ≤ E i j k u)
    (hE : ∀ i j k u, E i j k u =
      F₁ ⟨i, r₁ i⟩ + F₂ ⟨j, r₂ j⟩ - F₀ ⟨k, r₀ k⟩ + ωG (A i j k u) - ρ i j k u)
    (hρ : ∀ i j k u, -C ≤ ρ i j k u) {D₁ D₂ : ℝ} {a : NovikovModule R F₁}
    {b : NovikovModule R F₂} (ha : a ∈ potentialFiltration R F₁ D₁)
    (hb : b ∈ potentialFiltration R F₂ D₂) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
        (fun i j k => coefficientComparison q hq (countSeries (A i j k) (w i j k) (hfin i j k)))
        a b ∈
      potentialFiltration R F₀ (D₁ + D₂ + C) :=
  novikovProductOfMatrix_coefficientComparison_mem_potentialFiltration r₁ r₂ r₀ q hq hF₁ hF₂ hF₀
    (fun i j k => by
      convert countSeries_mem_periodFiltration_of_energy (hE₀ i j k) (hE i j k) (hρ i j k)
        using 2
      ring) ha hb

/-- **The degree of the product of the count matrix from the index of each solution.** If the
gradings obey the recapping law and every solution of nonzero sign satisfies the index condition
`μ₀(r₀ k) - 2 c₁(A u) = μ₁(r₁ i) + μ₂(r₂ j) - n - ε`, then the product given by the generating
series of the solutions sends combinations of degrees `i'` and `j'` in an additive image `f` of the
cochain degree `n - μ` to one of degree `i' + j' + f ε`. Rigid pairs of pants have `ε = 0`. -/
theorem novikovProductOfMatrix_coefficientComparison_countSeries_mem_map_cochain_gradeBy_add
    [CommSemiring R]
    {μ₁ : (Σ i, P₁ i) → ℤ} {μ₂ : (Σ j, P₂ j) → ℤ} {μ₀ : (Σ k, P₀ k) → ℤ}
    (hμ₁ : ∀ i γ (D : P₁ i), μ₁ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ₁ ⟨i, D⟩)
    (hμ₂ : ∀ j γ (D : P₂ j), μ₂ ⟨j, γ +ᵥ D⟩ = degree ω c γ + μ₂ ⟨j, D⟩)
    (hμ₀ : ∀ k γ (D : P₀ k), μ₀ ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₀ ⟨k, D⟩)
    (w : ∀ i j k, M i j k → R)
    (hfin : ∀ i j k, ∀ L : ℝ, {u | w i j k u ≠ 0 ∧ ωG (A i j k u) < L}.Finite) {n ε : ℤ}
    (hA : ∀ i j k u, w i j k u ≠ 0 →
      μ₀ ⟨k, r₀ k⟩ - degree ω c (q (A i j k u)) = μ₁ ⟨i, r₁ i⟩ + μ₂ ⟨j, r₂ j⟩ - n - ε)
    {D : Type*} [AddMonoid D] (f : ℤ →+ D) {i' j' : D} {a : NovikovModule R F₁}
    {b : NovikovModule R F₂} (ha : a ∈ gradeBy R F₁ (fun p => f (n - μ₁ p)) i')
    (hb : b ∈ gradeBy R F₂ (fun p => f (n - μ₂ p)) j') :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
        (fun i j k => coefficientComparison q hq (countSeries (A i j k) (w i j k) (hfin i j k)))
        a b ∈
      gradeBy R F₀ (fun p => f (n - μ₀ p)) (i' + j' + f ε) :=
  novikovProductOfMatrix_coefficientComparison_mem_map_cochain_gradeBy_add r₁ r₂ r₀ q hq hF₁ hF₂
    hF₀ hμ₁ hμ₂ hμ₀ _ (fun i j k _ hB => by
      obtain ⟨u, hu, rfl⟩ := support_countSeries_subset hB
      exact hA i j k u hu) f ha hb

end TauCeti.Floer

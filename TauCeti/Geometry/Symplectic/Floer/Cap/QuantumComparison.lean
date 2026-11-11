/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.CoefficientComparison
public import TauCeti.RingTheory.NovikovModule.Comparison

/-!
# Comparing the capped product of class-indexed counts with the quantum product

The Piunikhin–Salamon–Schwarz (PSS) map is multiplicative: it intertwines the Morse quantum
product with the pair-of-pants product. This file states that comparison for products and maps
given by class-indexed counts on capped generators, in the form in which the counts of the
comparison family enter.

On the Floer side, the capped orbits of the two inputs and the output of the pair of pants have
reference caps `r₁`, `r₂`, `r₀`, and `Q` is the generating series of rigid pairs of pants, as in
`TauCeti.Geometry.Symplectic.Floer.Cap.Product`. On the quantum side, the generators are critical
points of Morse functions with Novikov coefficients, organized in the same way as torsors under
the period group `Γ = PeriodGroup ω c` with reference generators `s₁`, `s₂`, `s₀`, and `M` is the
generating series of the rigid three-pointed genus-zero configurations of the Morse quantum
product. Further generating series, all indexed by a common class group `G` mapping to `Γ` by an
area-preserving homomorphism `q`, count:

* `Φ₁`, `Φ₂`, `Φ₀`: PSS half-cylinders from the Morse generators of each end to the capped
  orbits, and `Ψ₀`: PSS half-cylinders in the opposite direction at the output;
* `E₁`, `E₂`, `E₀`: Morse trajectories, the differentials on the quantum side, and `D₀`: Floer
  cylinders, the differential at the output of the pair of pants;
* `K`: rigid members of the comparison family, obtained by attaching PSS planes to the three ends
  of a pair of pants and deforming the Hamiltonian perturbation to zero, which interpolates
  between the broken configurations counted by `Ψ₀ (Φ₁ a ⋆ Φ₂ b)` and those counted by `M`;
* `H₀`: rigid members of the family giving the homotopy `Ψ₀ Φ₀ - 1 = H₀ D₀ + D₀ H₀`, which a
  module inverse of the PSS map supplies.

Every series is sent to the Floer Novikov ring by the coefficient comparison `q^A ↦ e^(-q A)`
(`TauCeti.Floer.coefficientComparison`), and gives a map or a product on the completed capped
modules (`TauCeti.NovikovModule.novikovMapOfMatrix`,
`TauCeti.NovikovModule.novikovProductOfMatrix`). If the ends of the one-dimensional moduli spaces
of the comparison family give the identity

`∑ᵢ' ∑ⱼ' Φ₁ᵢᵢ' Φ₂ⱼⱼ' ∑ₖ Qᵢ'ⱼ'ₖ Ψ₀ₖₗ - Mᵢⱼₗ =`
`  ∑ₖ Kᵢⱼₖ E₀ₖₗ + ∑ₖ E₁ᵢₖ Kₖⱼₗ + (-1)^(n - μ₁(s₁ i)) ∑ₖ E₂ⱼₖ Kᵢₖₗ`

in `G`-indexed series, then:

* `Ψ₀ (Φ₁ a ⋆ Φ₂ b) - a ⋆_M b = E₀ K(a, b) + K(E₁ a, b) + (-1)^e K(a, E₂ b)` for `a` of cochain
  degree `e`
  (`novikovMapOfMatrix_novikovProductOfMatrix_novikovMapOfMatrix_coefficientComparison_sub`);
* if moreover `Φ₀` is a chain map, `E₀ Φ₀ = Φ₀ D₀`, and `H₀` is a homotopy
  `Ψ₀ Φ₀ - 1 = H₀ D₀ + D₀ H₀`, all class by class, then with `T = Φ₁ a ⋆ Φ₂ b`,
  `T - Φ₀ (a ⋆_M b) = D₀ (Φ₀ K(a, b) - H₀ T) + (Φ₀ (K(E₁ a, b) + (-1)^e K(a, E₂ b)) - H₀ (D₀ T))`
  (`novikovProductOfMatrix_novikovMapOfMatrix_coefficientComparison_sub`).

The second identity is the chain-level form of the multiplicativity of the PSS map: when `a`, `b`
and `T` are cocycles, the last summand vanishes and `T - Φ₀ (a ⋆_M b)` is the coboundary
`D₀ (Φ₀ K(a, b) - H₀ T)`. Neither product is defined by transporting the
other: `Q` and `M` are independent counts. The sign `(-1)^(n - μ₁(s₁ i))` only depends on the
orbit, because recapping changes the grading by the even number `2 c₁(γ)`. The count identities
are the geometric input from the compactified moduli spaces; no moduli space, orientation or
count is constructed here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the chapter on Floer
  homology and the Piunikhin–Salamon–Schwarz isomorphism.
-/

public section

noncomputable section

namespace TauCeti.Floer

open NovikovModule NovikovSeries PeriodGroup

variable {R S : Type*} [AddCommGroup S] {ω : S →+ ℝ} {c : S →+ ℤ}
  {ι₁ ι₂ ι₀ κ₁ κ₂ κ₀ : Type*} {P₁ : ι₁ → Type*} {P₂ : ι₂ → Type*} {P₀ : ι₀ → Type*}
  {T₁ : κ₁ → Type*} {T₂ : κ₂ → Type*} {T₀ : κ₀ → Type*}
  [∀ i, AddTorsor (PeriodGroup ω c) (P₁ i)] [∀ j, AddTorsor (PeriodGroup ω c) (P₂ j)]
  [∀ k, AddTorsor (PeriodGroup ω c) (P₀ k)]
  [∀ i, AddTorsor (PeriodGroup ω c) (T₁ i)] [∀ j, AddTorsor (PeriodGroup ω c) (T₂ j)]
  [∀ k, AddTorsor (PeriodGroup ω c) (T₀ k)]
  (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₀ : ∀ k, P₀ k)
  (s₁ : ∀ i, T₁ i) (s₂ : ∀ j, T₂ j) (s₀ : ∀ k, T₀ k)
  {μ₁ : (Σ i, T₁ i) → ℤ} (hμ₁ : ∀ i γ (t : T₁ i), μ₁ ⟨i, γ +ᵥ t⟩ = degree ω c γ + μ₁ ⟨i, t⟩)
  (n : ℤ)

include hμ₁ in
/-- Recapping a Morse generator changes its cochain degree `n - μ₁` by the even number
`-2 c₁(γ)`. -/
private theorem even_cochain_sub (i : κ₁) (γ : PeriodGroup ω c) (t : T₁ i) :
    Even (n - μ₁ ⟨i, γ +ᵥ t⟩ - (n - μ₁ ⟨i, t⟩)) := by
  rw [hμ₁]
  convert (even_degree ω c γ).neg using 1
  ring

variable {G : Type*} [AddMonoid G] {ωG : G →+ ℝ} (q : G →+ PeriodGroup ω c)
  (hq : ∀ A, area ω c (q A) = ωG A)
  [CommRing R] [Fintype ι₁] [Fintype ι₂] [Fintype ι₀] [Fintype κ₁] [Fintype κ₂] [Fintype κ₀]
  {F₁ : (Σ i, P₁ i) → ℝ} {F₂ : (Σ j, P₂ j) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  {F₁' : (Σ i, T₁ i) → ℝ} {F₂' : (Σ j, T₂ j) → ℝ} {F₀' : (Σ k, T₀ k) → ℝ}
  (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
  (hF₂ : ∀ j γ (D : P₂ j), F₂ ⟨j, γ +ᵥ D⟩ = F₂ ⟨j, D⟩ - (-area ω c) γ)
  (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)
  (hF₁' : ∀ i γ (t : T₁ i), F₁' ⟨i, γ +ᵥ t⟩ = F₁' ⟨i, t⟩ - (-area ω c) γ)
  (hF₂' : ∀ j γ (t : T₂ j), F₂' ⟨j, γ +ᵥ t⟩ = F₂' ⟨j, t⟩ - (-area ω c) γ)
  (hF₀' : ∀ k γ (t : T₀ k), F₀' ⟨k, γ +ᵥ t⟩ = F₀' ⟨k, t⟩ - (-area ω c) γ)
  (Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (M : κ₁ → κ₂ → κ₀ → NovikovSeries R G ωG)
  (Φ₁ : κ₁ → ι₁ → NovikovSeries R G ωG) (Φ₂ : κ₂ → ι₂ → NovikovSeries R G ωG)
  (Ψ₀ : ι₀ → κ₀ → NovikovSeries R G ωG) (K : κ₁ → κ₂ → κ₀ → NovikovSeries R G ωG)
  (E₁ : κ₁ → κ₁ → NovikovSeries R G ωG) (E₂ : κ₂ → κ₂ → NovikovSeries R G ωG)
  (E₀ : κ₀ → κ₀ → NovikovSeries R G ωG)

omit [∀ i, AddTorsor (PeriodGroup ω c) (T₁ i)] in
/-- The comparison identity of class-indexed counts, sent to the Floer Novikov ring by the
coefficient comparison. -/
private theorem coefficientComparison_comparison_identity
    (hcomp : ∀ i j l, ∑ i', ∑ j', Φ₁ i i' * Φ₂ j j' * ∑ k, Q i' j' k * Ψ₀ k l - M i j l =
      ∑ k, K i j k * E₀ k l + ∑ k, E₁ i k * K k j l +
        negOnePowCast R (n - μ₁ ⟨i, s₁ i⟩) • ∑ k, E₂ j k * K i k l) (i : κ₁) (j : κ₂) (l : κ₀) :
    ∑ i', ∑ j', coefficientComparison q hq (Φ₁ i i') * coefficientComparison q hq (Φ₂ j j') *
        ∑ k, coefficientComparison q hq (Q i' j' k) * coefficientComparison q hq (Ψ₀ k l) -
      coefficientComparison q hq (M i j l) =
    ∑ k, coefficientComparison q hq (K i j k) * coefficientComparison q hq (E₀ k l) +
      ∑ k, coefficientComparison q hq (E₁ i k) * coefficientComparison q hq (K k j l) +
      negOnePowCast R (n - μ₁ ⟨i, s₁ i⟩) •
        ∑ k, coefficientComparison q hq (E₂ j k) * coefficientComparison q hq (K i k l) := by
  have h := congrArg (coefficientComparison q hq) (hcomp i j l)
  simp only [map_sum, map_sub, map_add, _root_.map_mul, ← negOnePow_smul_eq_negOnePowCast_smul,
    Units.smul_def, map_zsmul] at h ⊢
  exact h

include hμ₁ in
/-- **Comparison through the inverse PSS map, for class-indexed counts.** Let `Q` be the
generating series of rigid pairs of pants between reference capped orbits, `M` those of the Morse
quantum product between reference Morse generators, `Φ₁`, `Φ₂` those of PSS half-cylinders from
the Morse generators of the inputs to the capped orbits, `Ψ₀` those of PSS half-cylinders from the
capped orbits of the output back to its Morse generators, and `E₁`, `E₂`, `E₀` those of Morse
trajectories, all indexed by a common class group `G`. Suppose the generating series `K` of the
rigid members of the comparison family obey the identity

`∑ᵢ' ∑ⱼ' Φ₁ᵢᵢ' Φ₂ⱼⱼ' ∑ₖ Qᵢ'ⱼ'ₖ Ψ₀ₖₗ - Mᵢⱼₗ =`
`  ∑ₖ Kᵢⱼₖ E₀ₖₗ + ∑ₖ E₁ᵢₖ Kₖⱼₗ + (-1)^(n - μ₁(s₁ i)) ∑ₖ E₂ⱼₖ Kᵢₖₗ`

in `G`-indexed series, the count, class by class, of the ends of its one-dimensional moduli spaces.
Then on the completed modules, with the first Morse input graded by the cochain degree
`n - μ₁`, `Ψ₀ (Φ₁ a ⋆ Φ₂ b) - a ⋆_M b = E₀ K(a, b) + K(E₁ a, b) + (-1)^e K(a, E₂ b)` for every
`a` of degree `e`. -/
theorem novikovMapOfMatrix_novikovProductOfMatrix_novikovMapOfMatrix_coefficientComparison_sub
    (hcomp : ∀ i j l, ∑ i', ∑ j', Φ₁ i i' * Φ₂ j j' * ∑ k, Q i' j' k * Ψ₀ k l - M i j l =
      ∑ k, K i j k * E₀ k l + ∑ k, E₁ i k * K k j l +
        negOnePowCast R (n - μ₁ ⟨i, s₁ i⟩) • ∑ k, E₂ j k * K i k l)
    {e : ℤ} {a : NovikovModule R F₁'} (ha : a ∈ gradeBy R F₁' (fun p => n - μ₁ p) e)
    (b : NovikovModule R F₂') :
    novikovMapOfMatrix hF₀ hF₀' r₀ s₀ (fun k l => coefficientComparison q hq (Ψ₀ k l))
          (novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
            (fun i j k => coefficientComparison q hq (Q i j k))
            (novikovMapOfMatrix hF₁' hF₁ s₁ r₁ (fun i k => coefficientComparison q hq (Φ₁ i k)) a)
            (novikovMapOfMatrix hF₂' hF₂ s₂ r₂ (fun j k => coefficientComparison q hq (Φ₂ j k))
              b)) -
        novikovProductOfMatrix hF₁' hF₂' hF₀' s₁ s₂ s₀
          (fun i j k => coefficientComparison q hq (M i j k)) a b =
      novikovMapOfMatrix hF₀' hF₀' s₀ s₀ (fun k l => coefficientComparison q hq (E₀ k l))
          (novikovProductOfMatrix hF₁' hF₂' hF₀' s₁ s₂ s₀
            (fun i j k => coefficientComparison q hq (K i j k)) a b) +
        novikovProductOfMatrix hF₁' hF₂' hF₀' s₁ s₂ s₀
          (fun i j k => coefficientComparison q hq (K i j k))
          (novikovMapOfMatrix hF₁' hF₁' s₁ s₁ (fun i k => coefficientComparison q hq (E₁ i k)) a)
          b +
        negOnePowCast R e • novikovProductOfMatrix hF₁' hF₂' hF₀' s₁ s₂ s₀
          (fun i j k => coefficientComparison q hq (K i j k)) a
          (novikovMapOfMatrix hF₂' hF₂' s₂ s₂ (fun j k => coefficientComparison q hq (E₂ j k))
            b) :=
  novikovMapOfMatrix_novikovProductOfMatrix_novikovMapOfMatrix_sub_novikovProductOfMatrix hF₁ hF₂
    hF₀ hF₁' hF₂' hF₀' r₁ r₂ r₀ s₁ s₂ s₀ _ _ _ _ _ _ _ _ _ (even_cochain_sub hμ₁ n)
    (coefficientComparison_comparison_identity s₁ n q hq Q M Φ₁ Φ₂ Ψ₀ K E₁ E₂ E₀ hcomp) ha b

include hμ₁ in
/-- **The multiplicativity homotopy of the PSS map, for class-indexed counts.** Under the
comparison identity of class-indexed counts through the inverse PSS map, let `Φ₀` be the
generating series of PSS half-cylinders from the Morse generators of the output to
its capped orbits, `D₀` those of rigid Floer cylinders at the output, and `H₀` those of the rigid
members of a homotopy between `Ψ₀ Φ₀` and the identity. Suppose that, in `G`-indexed series,

`∑ₘ E₀ₖₘ Φ₀ₘₗ = ∑ₘ Φ₀ₖₘ D₀ₘₗ` and `∑ₘ Ψ₀ₖₘ Φ₀ₘₗ - [k = l] = ∑ₘ H₀ₖₘ D₀ₘₗ + ∑ₘ D₀ₖₘ H₀ₘₗ`,

that is, `Φ₀` is a chain map and `H₀` a homotopy `Φ₀ ∘ Ψ₀ - 1 = D₀ ∘ H₀ + H₀ ∘ D₀`. Then on the
completed modules, for `a` of cochain degree `e` and with `T = Φ₁ a ⋆ Φ₂ b`,

`T - Φ₀ (a ⋆_M b) = D₀ (Φ₀ K(a, b) - H₀ T) + (Φ₀ (K(E₁ a, b) + (-1)^e K(a, E₂ b)) - H₀ (D₀ T))`.

When `a`, `b` and `T` are cocycles, `T - Φ₀ (a ⋆_M b)` is therefore the coboundary
`D₀ (Φ₀ K(a, b) - H₀ T)`. -/
theorem novikovProductOfMatrix_novikovMapOfMatrix_coefficientComparison_sub [DecidableEq ι₀]
    (Φ₀ : κ₀ → ι₀ → NovikovSeries R G ωG) (H₀ D₀ : ι₀ → ι₀ → NovikovSeries R G ωG)
    (hΦ₀ : ∀ k l, ∑ m, E₀ k m * Φ₀ m l = ∑ m, Φ₀ k m * D₀ m l)
    (hinv : ∀ k l, ∑ m, Ψ₀ k m * Φ₀ m l - (if k = l then 1 else 0) =
      ∑ m, H₀ k m * D₀ m l + ∑ m, D₀ k m * H₀ m l)
    (hcomp : ∀ i j l, ∑ i', ∑ j', Φ₁ i i' * Φ₂ j j' * ∑ k, Q i' j' k * Ψ₀ k l - M i j l =
      ∑ k, K i j k * E₀ k l + ∑ k, E₁ i k * K k j l +
        negOnePowCast R (n - μ₁ ⟨i, s₁ i⟩) • ∑ k, E₂ j k * K i k l)
    {e : ℤ} {a : NovikovModule R F₁'} (ha : a ∈ gradeBy R F₁' (fun p => n - μ₁ p) e)
    (b : NovikovModule R F₂') :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀ (fun i j k => coefficientComparison q hq (Q i j k))
          (novikovMapOfMatrix hF₁' hF₁ s₁ r₁ (fun i k => coefficientComparison q hq (Φ₁ i k)) a)
          (novikovMapOfMatrix hF₂' hF₂ s₂ r₂ (fun j k => coefficientComparison q hq (Φ₂ j k)) b) -
        novikovMapOfMatrix hF₀' hF₀ s₀ r₀ (fun k l => coefficientComparison q hq (Φ₀ k l))
          (novikovProductOfMatrix hF₁' hF₂' hF₀' s₁ s₂ s₀
            (fun i j k => coefficientComparison q hq (M i j k)) a b) =
      novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun k l => coefficientComparison q hq (D₀ k l))
          (novikovMapOfMatrix hF₀' hF₀ s₀ r₀ (fun k l => coefficientComparison q hq (Φ₀ k l))
              (novikovProductOfMatrix hF₁' hF₂' hF₀' s₁ s₂ s₀
                (fun i j k => coefficientComparison q hq (K i j k)) a b) -
            novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun k l => coefficientComparison q hq (H₀ k l))
              (novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
                (fun i j k => coefficientComparison q hq (Q i j k))
                (novikovMapOfMatrix hF₁' hF₁ s₁ r₁
                  (fun i k => coefficientComparison q hq (Φ₁ i k)) a)
                (novikovMapOfMatrix hF₂' hF₂ s₂ r₂
                  (fun j k => coefficientComparison q hq (Φ₂ j k)) b))) +
        (novikovMapOfMatrix hF₀' hF₀ s₀ r₀ (fun k l => coefficientComparison q hq (Φ₀ k l))
            (novikovProductOfMatrix hF₁' hF₂' hF₀' s₁ s₂ s₀
                (fun i j k => coefficientComparison q hq (K i j k))
                (novikovMapOfMatrix hF₁' hF₁' s₁ s₁
                  (fun i k => coefficientComparison q hq (E₁ i k)) a) b +
              negOnePowCast R e • novikovProductOfMatrix hF₁' hF₂' hF₀' s₁ s₂ s₀
                (fun i j k => coefficientComparison q hq (K i j k)) a
                (novikovMapOfMatrix hF₂' hF₂' s₂ s₂
                  (fun j k => coefficientComparison q hq (E₂ j k)) b)) -
          novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun k l => coefficientComparison q hq (H₀ k l))
            (novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun k l => coefficientComparison q hq (D₀ k l))
              (novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
                (fun i j k => coefficientComparison q hq (Q i j k))
                (novikovMapOfMatrix hF₁' hF₁ s₁ r₁
                  (fun i k => coefficientComparison q hq (Φ₁ i k)) a)
                (novikovMapOfMatrix hF₂' hF₂ s₂ r₂
                  (fun j k => coefficientComparison q hq (Φ₂ j k)) b)))) := by
  -- The output matrices are passed as `Matrix.of` of their entries, so that the matrix identities
  -- they must satisfy can be read entrywise with `Matrix.mul_apply`.
  refine novikovProductOfMatrix_novikovMapOfMatrix_sub_novikovMapOfMatrix_novikovProductOfMatrix
    hF₁ hF₂ hF₀ hF₁' hF₂' hF₀' r₁ r₂ r₀ s₁ s₂ s₀ _ _ _ _ (Matrix.of fun k l =>
      coefficientComparison q hq (Ψ₀ k l)) _ _ _ (Matrix.of fun k l =>
      coefficientComparison q hq (E₀ k l)) (Matrix.of fun k l =>
      coefficientComparison q hq (Φ₀ k l)) (Matrix.of fun k l =>
      coefficientComparison q hq (H₀ k l)) (Matrix.of fun k l =>
      coefficientComparison q hq (D₀ k l)) ?_ ?_ (even_cochain_sub hμ₁ n)
    (coefficientComparison_comparison_identity s₁ n q hq Q M Φ₁ Φ₂ Ψ₀ K E₁ E₂ E₀ hcomp) ha b
  · refine Matrix.ext fun k l => ?_
    simpa only [Matrix.mul_apply, Matrix.of_apply, map_sum, _root_.map_mul] using
      congrArg (coefficientComparison q hq) (hΦ₀ k l)
  · refine Matrix.ext fun k l => ?_
    simpa only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply,
      Matrix.of_apply, map_sum, map_sub, map_add, _root_.map_mul,
      apply_ite (coefficientComparison q hq), _root_.map_one, map_zero] using
      congrArg (coefficientComparison q hq) (hinv k l)

end TauCeti.Floer

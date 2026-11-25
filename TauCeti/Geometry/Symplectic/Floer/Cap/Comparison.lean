/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Map
public import TauCeti.Geometry.Symplectic.Floer.Cap.Product
public import TauCeti.RingTheory.NovikovModule.Comparison
import TauCeti.Geometry.Symplectic.Floer.Grading

/-!
# The multiplicative PSS comparison for class-indexed counts on capped generators

Fix finitely many orbits for each end of the pair of pants, with capped generators `Pₗ` and
reference caps `rₗ`, and finitely many critical points for each of three Morse functions, with
capped generators `Tₗ` and reference generators `sₗ`. Both families are torsors under the period
group `Γ = PeriodGroup ω c`. Every count is recorded by a generating series in a common class
group `G` mapping to `Γ` by an area-preserving homomorphism `q`, and enters the completed capped
modules through the coefficient comparison `q^A ↦ e^(-q A)` of
`TauCeti.Floer.coefficientComparison`, as in `TauCeti.Geometry.Symplectic.Floer.Cap.Product`:

* `Qᵢⱼₖ` counts rigid pairs of pants, giving the pair-of-pants product `⋆`;
* `Mₛₜₗ` counts the rigid three-pointed genus-zero configurations with Morse incidence conditions,
  giving the Morse quantum product `⋆_M`;
* `Φₗ` count PSS half-cylinders from critical points to orbits, and `Ψ₀` counts them in the
  opposite direction;
* `Kₛₜₗ` counts the rigid members of the comparison family obtained by attaching PSS planes to the
  three ends of a pair of pants and deforming the Hamiltonian perturbation to zero;
* `Eₗ` and `Dₗ` count the rigid Morse trajectories and Floer cylinders, giving the differentials;
* `Y₀` counts the rigid members of the family giving the module homotopy `Φ₀ Ψ₀ ≃ 1`.

The ends of the one-dimensional moduli spaces of the comparison family give, class by class, the
comparison identity

`∑ᵢ ∑ⱼ Φ₁ₛᵢ Φ₂ₜⱼ ∑ₖ Qᵢⱼₖ Ψ₀ₖₗ - Mₛₜₗ = ∑ₘ Kₛₜₘ E₀ₘₗ + ∑ₘ E₁ₛₘ Kₘₜₗ + (-1)^e₁ ∑ₘ E₂ₜₘ Kₛₘₗ`

with `e₁ = n - ν₁(s₁ s)` the cochain degree of the reference generator. This file proves that it
gives the homotopy `Ψ₀ (Φ₁ a ⋆ Φ₂ b) - a ⋆_M b = E₀ K(a, b) + K(E₁ a, b) + (-1)^e K(a, E₂ b)`
(`novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_novikovProductOfMatrix`)
and, together with the module homotopy, the homotopy between `Φ₁ a ⋆ Φ₂ b` and `Φ₀ (a ⋆_M b)`
(`novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_novikovProductOfMatrix`).
Under the index conditions of rigid counts, the PSS maps preserve the cochain degree `n - μ` and
the homotopies lower it by one
(`TauCeti.Floer.novikovMapOfMatrix_coefficientComparison_mem_cochain_gradeBy`), so on cocycles of
the Morse differentials the two differ by a coboundary of the Floer differential
(`novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_mem_coboundaries`).
This is the multiplicativity of the PSS map on capped generators, with the Novikov exponents of
both sides compared through `q^A ↦ e^(-q A)`. Neither product is defined by transporting the
other.

On cohomology, graded by the cochain degrees, the maps induced by the PSS counts therefore
intertwine the Morse quantum product with the pair-of-pants product,
`Φ₀ ([a] ⋆_M [b]) = Φ₁ [a] ⋆ Φ₂ [b]`
(`cohomologyMap_cohomologyProduct_kernelProduct_coefficientComparison`). A module inverse of the
PSS maps makes them isomorphisms of cohomology (`LinearMap.cohomologyEquiv`) once both composite
homotopies `ΨΦ ≃ id` and `ΦΨ ≃ id` hold, each obtained from
`TauCeti.Floer.novikovMapOfMatrix_novikovMapOfMatrix_coefficientComparison_sub_mem_coboundaries`.
The inverse maps are multiplicative too: `g₀ (x ⋆ y) = g₁ x ⋆_M g₂ y` for one-sided inverses `g₁`,
`g₂` of the input maps and `g₀` of the output map
(`cohomologyMap_cohomologyProduct_kernelProduct_coefficientComparison_of_inverse`, an instance of
`LinearMap.cohomologyMap_cohomologyProduct_of_leftInverse`). So the PSS maps
are isomorphisms of the products on cohomology, in both directions, once the comparison identity
and the module homotopies hold.

The kernel-level forms of these statements are
`TauCeti.NovikovModule.kernelMap_kernelProduct_kernelMap_sub_kernelProduct`,
`TauCeti.NovikovModule.kernelProduct_kernelMap_sub_kernelMap_kernelProduct` and
`TauCeti.NovikovModule.kernelProduct_kernelMap_sub_kernelMap_kernelProduct_mem_coboundaries`; the
downstream statement on cohomology is
`TauCeti.NovikovModule.cohomologyMap_cohomologyProduct_kernelProduct_of_homotopy_inverse`. The
count identities, index conditions and potential bounds are the hypotheses the compactified moduli
spaces are to supply; no moduli space, orientation or count is constructed here.

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
  [∀ k, AddTorsor (PeriodGroup ω c) (P₀ k)] [∀ s, AddTorsor (PeriodGroup ω c) (T₁ s)]
  [∀ t, AddTorsor (PeriodGroup ω c) (T₂ t)] [∀ l, AddTorsor (PeriodGroup ω c) (T₀ l)]
  (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₀ : ∀ k, P₀ k)
  (s₁ : ∀ s, T₁ s) (s₂ : ∀ t, T₂ t) (s₀ : ∀ l, T₀ l)
  {G : Type*} [AddMonoid G] {ωG : G →+ ℝ} (q : G →+ PeriodGroup ω c)
  (hq : ∀ A, area ω c (q A) = ωG A)

section Homotopy

variable [CommRing R] [Fintype ι₁] [Fintype ι₂] [Fintype ι₀] [Fintype κ₁] [Fintype κ₂]
  [Fintype κ₀] {F₁ : (Σ i, P₁ i) → ℝ} {F₂ : (Σ j, P₂ j) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  {G₁ : (Σ s, T₁ s) → ℝ} {G₂ : (Σ t, T₂ t) → ℝ} {G₀ : (Σ l, T₀ l) → ℝ}
  (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
  (hF₂ : ∀ j γ (D : P₂ j), F₂ ⟨j, γ +ᵥ D⟩ = F₂ ⟨j, D⟩ - (-area ω c) γ)
  (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)
  (hG₁ : ∀ s γ (D : T₁ s), G₁ ⟨s, γ +ᵥ D⟩ = G₁ ⟨s, D⟩ - (-area ω c) γ)
  (hG₂ : ∀ t γ (D : T₂ t), G₂ ⟨t, γ +ᵥ D⟩ = G₂ ⟨t, D⟩ - (-area ω c) γ)
  (hG₀ : ∀ l γ (D : T₀ l), G₀ ⟨l, γ +ᵥ D⟩ = G₀ ⟨l, D⟩ - (-area ω c) γ)
  {ν₁ : (Σ s, T₁ s) → ℤ} (hν₁ : ∀ s γ (D : T₁ s), ν₁ ⟨s, γ +ᵥ D⟩ = degree ω c γ + ν₁ ⟨s, D⟩)
  (Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (M : κ₁ → κ₂ → κ₀ → NovikovSeries R G ωG)
  (Φ₁ : κ₁ → ι₁ → NovikovSeries R G ωG) (Φ₂ : κ₂ → ι₂ → NovikovSeries R G ωG)
  (Ψ₀ : ι₀ → κ₀ → NovikovSeries R G ωG) (K : κ₁ → κ₂ → κ₀ → NovikovSeries R G ωG)
  (E₁ : κ₁ → κ₁ → NovikovSeries R G ωG) (E₂ : κ₂ → κ₂ → NovikovSeries R G ωG)
  (E₀ : κ₀ → κ₀ → NovikovSeries R G ωG) (n : ℤ)

include hν₁ in
/-- **Comparison of class-indexed counts through the inverse PSS map.** Let `Q` be the generating
series of rigid pairs of pants, `M` those of the rigid configurations of the Morse quantum product,
`Φ₁`, `Φ₂` those of PSS half-cylinders from the input critical points to the input orbits, `Ψ₀`
those from the output orbits to the output critical points, `K` those of the rigid members of the
comparison family, and `E₁`, `E₂`, `E₀` those of rigid Morse trajectories, all between reference
generators and indexed by a common class group `G`. Suppose the series obey the identity

`∑ᵢ ∑ⱼ Φ₁ₛᵢ Φ₂ₜⱼ ∑ₖ Qᵢⱼₖ Ψ₀ₖₗ - Mₛₜₗ =
  ∑ₘ Kₛₜₘ E₀ₘₗ + ∑ₘ E₁ₛₘ Kₘₜₗ + (-1)^(n - ν₁(s₁ s)) ∑ₘ E₂ₜₘ Kₛₘₗ`

in `G`-indexed series, which is the count, class by class, of the ends of the one-dimensional
moduli spaces of the comparison family. Then on the completed capped modules, with the first Morse
input graded by the cochain degree `n - ν₁`,
`Ψ₀ (Φ₁ a ⋆ Φ₂ b) - a ⋆_M b = E₀ K(a, b) + K(E₁ a, b) + (-1)^e K(a, E₂ b)` for every `a` of degree
`e`. -/
theorem novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_novikovProductOfMatrix
    (hC : ∀ s t l, ∑ i, ∑ j, Φ₁ s i * Φ₂ t j * ∑ k, Q i j k * Ψ₀ k l - M s t l =
      ∑ m, K s t m * E₀ m l + ∑ m, E₁ s m * K m t l +
        negOnePowCast R (n - ν₁ ⟨s, s₁ s⟩) • ∑ m, E₂ t m * K s m l)
    {e : ℤ} {a : NovikovModule R G₁} (ha : a ∈ gradeBy R G₁ (fun p => n - ν₁ p) e)
    (b : NovikovModule R G₂) :
    novikovMapOfMatrix hF₀ hG₀ r₀ s₀ (fun k l => coefficientComparison q hq (Ψ₀ k l))
          (novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
            (fun i j k => coefficientComparison q hq (Q i j k))
            (novikovMapOfMatrix hG₁ hF₁ s₁ r₁ (fun s i => coefficientComparison q hq (Φ₁ s i)) a)
            (novikovMapOfMatrix hG₂ hF₂ s₂ r₂ (fun t j => coefficientComparison q hq (Φ₂ t j))
              b)) -
        novikovProductOfMatrix hG₁ hG₂ hG₀ s₁ s₂ s₀
          (fun s t l => coefficientComparison q hq (M s t l)) a b =
      novikovMapOfMatrix hG₀ hG₀ s₀ s₀ (fun l m => coefficientComparison q hq (E₀ l m))
          (novikovProductOfMatrix hG₁ hG₂ hG₀ s₁ s₂ s₀
            (fun s t l => coefficientComparison q hq (K s t l)) a b) +
        novikovProductOfMatrix hG₁ hG₂ hG₀ s₁ s₂ s₀
          (fun s t l => coefficientComparison q hq (K s t l))
          (novikovMapOfMatrix hG₁ hG₁ s₁ s₁ (fun s m => coefficientComparison q hq (E₁ s m)) a)
          b +
        negOnePowCast R e • novikovProductOfMatrix hG₁ hG₂ hG₀ s₁ s₂ s₀
          (fun s t l => coefficientComparison q hq (K s t l)) a
          (novikovMapOfMatrix hG₂ hG₂ s₂ s₂ (fun t m => coefficientComparison q hq (E₂ t m))
            b) := by
  refine novikovMapOfMatrix_novikovProductOfMatrix_novikovMapOfMatrix_sub_novikovProductOfMatrix
    hF₁ hF₂ hF₀ hG₁ hG₂ hG₀ r₁ r₂ r₀ s₁ s₂ s₀ _ _ _ _ _ _ _ _ _
    (even_cochain_vadd_sub hν₁ n) (fun s t l => ?_) ha b
  simpa only [map_sum, map_add, map_sub, _root_.map_mul,
    map_negOnePowCast_smul] using
    congrArg (coefficientComparison q hq) (hC s t l)

include hν₁ in
/-- **Multiplicativity of the PSS maps of class-indexed counts up to homotopy.** Under the
comparison identity of
`novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_novikovProductOfMatrix`, let
`Φ₀` be the generating series of PSS half-cylinders from the output critical points to the output
orbits, `D₀` those of rigid Floer cylinders of the output, and `Y₀` those of the rigid members of
the family giving the module homotopy. Suppose that the series obey the identities

`∑ₘ E₀ₗₘ Φ₀ₘₖ = ∑ₘ Φ₀ₗₘ D₀ₘₖ`,  `∑ₗ Ψ₀ₖₗ Φ₀ₗₖ' - [k = k'] = ∑ₘ Y₀ₖₘ D₀ₘₖ' + ∑ₘ D₀ₖₘ Y₀ₘₖ'`

in `G`-indexed series, the counts of the ends of the one-dimensional moduli spaces saying that
`Φ₀` is a chain map and that `Y₀` is a homotopy between `Φ₀ Ψ₀` and the identity. Then for `a` of
degree `e`, with `T = Φ₁ a ⋆ Φ₂ b`,

`T - Φ₀ (a ⋆_M b) = D₀ (Φ₀ K(a, b) - Y₀ T) + (Φ₀ (K(E₁ a, b) + (-1)^e K(a, E₂ b)) - Y₀ (D₀ T))`. -/
theorem
    novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_novikovProductOfMatrix
    [DecidableEq ι₀] (Φ₀ : κ₀ → ι₀ → NovikovSeries R G ωG)
    (D₀ Y₀ : ι₀ → ι₀ → NovikovSeries R G ωG)
    (hC : ∀ s t l, ∑ i, ∑ j, Φ₁ s i * Φ₂ t j * ∑ k, Q i j k * Ψ₀ k l - M s t l =
      ∑ m, K s t m * E₀ m l + ∑ m, E₁ s m * K m t l +
        negOnePowCast R (n - ν₁ ⟨s, s₁ s⟩) • ∑ m, E₂ t m * K s m l)
    (hΦ₀ : ∀ l k, ∑ m, E₀ l m * Φ₀ m k = ∑ m, Φ₀ l m * D₀ m k)
    (hinv : ∀ k k', ∑ l, Ψ₀ k l * Φ₀ l k' - (if k = k' then 1 else 0) =
      ∑ m, Y₀ k m * D₀ m k' + ∑ m, D₀ k m * Y₀ m k')
    {e : ℤ} {a : NovikovModule R G₁} (ha : a ∈ gradeBy R G₁ (fun p => n - ν₁ p) e)
    (b : NovikovModule R G₂) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀ (fun i j k => coefficientComparison q hq (Q i j k))
          (novikovMapOfMatrix hG₁ hF₁ s₁ r₁ (fun s i => coefficientComparison q hq (Φ₁ s i)) a)
          (novikovMapOfMatrix hG₂ hF₂ s₂ r₂ (fun t j => coefficientComparison q hq (Φ₂ t j)) b) -
        novikovMapOfMatrix hG₀ hF₀ s₀ r₀ (fun l k => coefficientComparison q hq (Φ₀ l k))
          (novikovProductOfMatrix hG₁ hG₂ hG₀ s₁ s₂ s₀
            (fun s t l => coefficientComparison q hq (M s t l)) a b) =
      novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun k k' => coefficientComparison q hq (D₀ k k'))
          (novikovMapOfMatrix hG₀ hF₀ s₀ r₀ (fun l k => coefficientComparison q hq (Φ₀ l k))
              (novikovProductOfMatrix hG₁ hG₂ hG₀ s₁ s₂ s₀
                (fun s t l => coefficientComparison q hq (K s t l)) a b) -
            novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun k k' => coefficientComparison q hq (Y₀ k k'))
              (novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
                (fun i j k => coefficientComparison q hq (Q i j k))
                (novikovMapOfMatrix hG₁ hF₁ s₁ r₁ (fun s i => coefficientComparison q hq (Φ₁ s i))
                  a)
                (novikovMapOfMatrix hG₂ hF₂ s₂ r₂ (fun t j => coefficientComparison q hq (Φ₂ t j))
                  b))) +
        (novikovMapOfMatrix hG₀ hF₀ s₀ r₀ (fun l k => coefficientComparison q hq (Φ₀ l k))
            (novikovProductOfMatrix hG₁ hG₂ hG₀ s₁ s₂ s₀
                (fun s t l => coefficientComparison q hq (K s t l))
                (novikovMapOfMatrix hG₁ hG₁ s₁ s₁ (fun s m => coefficientComparison q hq (E₁ s m))
                  a) b +
              negOnePowCast R e • novikovProductOfMatrix hG₁ hG₂ hG₀ s₁ s₂ s₀
                (fun s t l => coefficientComparison q hq (K s t l)) a
                (novikovMapOfMatrix hG₂ hG₂ s₂ s₂ (fun t m => coefficientComparison q hq (E₂ t m))
                  b)) -
          novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun k k' => coefficientComparison q hq (Y₀ k k'))
            (novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun k k' => coefficientComparison q hq (D₀ k k'))
              (novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
                (fun i j k => coefficientComparison q hq (Q i j k))
                (novikovMapOfMatrix hG₁ hF₁ s₁ r₁ (fun s i => coefficientComparison q hq (Φ₁ s i))
                  a)
                (novikovMapOfMatrix hG₂ hF₂ s₂ r₂ (fun t j => coefficientComparison q hq (Φ₂ t j))
                  b)))) := by
  refine novikovProductOfMatrix_novikovMapOfMatrix_sub_novikovMapOfMatrix_novikovProductOfMatrix
    hF₁ hF₂ hF₀ hG₁ hG₂ hG₀ r₁ r₂ r₀ s₁ s₂ s₀ _ _ _ _
    (fun k l => coefficientComparison q hq (Ψ₀ k l))
    _ _ _ (fun l m => coefficientComparison q hq (E₀ l m)) _ _ _
    (even_cochain_vadd_sub hν₁ n) (fun s t l => ?_) ?_ ?_ ha b
  · simpa only [map_sum, map_add, map_sub, _root_.map_mul,
      map_negOnePowCast_smul] using
      congrArg (coefficientComparison q hq) (hC s t l)
  -- The count identities are matrix identities, which the ring homomorphism
  -- `coefficientComparison` carries to the matrices of comparisons.
  · have h := congrArg (Matrix.map · (coefficientComparison q hq))
      (Matrix.ext hΦ₀ : Matrix.of E₀ * Matrix.of Φ₀ = Matrix.of Φ₀ * Matrix.of D₀)
    rwa [Matrix.map_mul, Matrix.map_mul] at h
  · have h := congrArg (Matrix.map · (coefficientComparison q hq))
      (Matrix.ext hinv : Matrix.of Ψ₀ * Matrix.of Φ₀ - 1 =
        Matrix.of Y₀ * Matrix.of D₀ + Matrix.of D₀ * Matrix.of Y₀)
    rwa [Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _), Matrix.map_mul,
      Matrix.map_mul, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h

include hν₁ in
/-- **Multiplicativity of the PSS maps of class-indexed counts on cocycles.** Under the identities
of
`novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_novikovProductOfMatrix`,
suppose that the rigid pairs of pants obey the Leibniz identity with the Floer cylinders `D₁`, `D₂`,
`D₀` of `novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_eq_add`, that `Φ₁` and
`Φ₂` are chain maps, `∑ᵢ Φ₁ₛᵢ D₁ᵢᵢ' = ∑ₛ' E₁ₛₛ' Φ₁ₛ'ᵢ'` and likewise for `Φ₂`, and that every
counted class satisfies the index condition of its moduli space, relative to the reference
generators:

* `μ₀(r₀) - 2 c₁(A) = μ₁(r₁) + μ₂(r₂) - n` for the pairs of pants `Q`;
* `μ(r) - 2 c₁(A) = ν(s)` for the PSS maps `Φ₁`, `Φ₂`, `Φ₀`, which preserve the cochain degree;
* `μ₀(r₀ k') - 2 c₁(A) = μ₀(r₀ k) + 1` for the homotopy `Y₀`, which lowers it by one;
* `ν₀(s₀) - 2 c₁(A) = ν₁(s₁) + ν₂(s₂) - n + 1` for the comparison family `K`, whose rigid members
  have Fredholm index `-1` at a fixed parameter, so that `K` lowers the cochain degree by one.

Then for cocycles `a` and `b` of the Morse differentials, of cochain degrees `e` and `f`, the
difference `Φ₁ a ⋆ Φ₂ b - Φ₀ (a ⋆_M b)` is a coboundary of the Floer differential in cochain degree
`e + f`. The differentials are the ground-ring linear maps of the trajectory and cylinder counts,
for any potential bounds of their kernels. -/
theorem novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_mem_coboundaries
    [DecidableEq ι₀] (Φ₀ : κ₀ → ι₀ → NovikovSeries R G ωG)
    (D₀ Y₀ : ι₀ → ι₀ → NovikovSeries R G ωG) (D₁ : ι₁ → ι₁ → NovikovSeries R G ωG)
    (D₂ : ι₂ → ι₂ → NovikovSeries R G ωG)
    {μ₁ : (Σ i, P₁ i) → ℤ} (hμ₁ : ∀ i γ (D : P₁ i), μ₁ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ₁ ⟨i, D⟩)
    {μ₂ : (Σ j, P₂ j) → ℤ} (hμ₂ : ∀ j γ (D : P₂ j), μ₂ ⟨j, γ +ᵥ D⟩ = degree ω c γ + μ₂ ⟨j, D⟩)
    {μ₀ : (Σ k, P₀ k) → ℤ} (hμ₀ : ∀ k γ (D : P₀ k), μ₀ ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₀ ⟨k, D⟩)
    {ν₂ : (Σ t, T₂ t) → ℤ} (hν₂ : ∀ t γ (D : T₂ t), ν₂ ⟨t, γ +ᵥ D⟩ = degree ω c γ + ν₂ ⟨t, D⟩)
    {ν₀ : (Σ l, T₀ l) → ℤ} (hν₀ : ∀ l γ (D : T₀ l), ν₀ ⟨l, γ +ᵥ D⟩ = degree ω c γ + ν₀ ⟨l, D⟩)
    (hQ : ∀ i j k, ∀ A ∈ (Q i j k).support,
      μ₀ ⟨k, r₀ k⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + μ₂ ⟨j, r₂ j⟩ - n)
    (hΦ₁ : ∀ s i, ∀ A ∈ (Φ₁ s i).support, μ₁ ⟨i, r₁ i⟩ - degree ω c (q A) = ν₁ ⟨s, s₁ s⟩)
    (hΦ₂ : ∀ t j, ∀ A ∈ (Φ₂ t j).support, μ₂ ⟨j, r₂ j⟩ - degree ω c (q A) = ν₂ ⟨t, s₂ t⟩)
    (hΦ₀deg : ∀ l k, ∀ A ∈ (Φ₀ l k).support, μ₀ ⟨k, r₀ k⟩ - degree ω c (q A) = ν₀ ⟨l, s₀ l⟩)
    (hY₀ : ∀ k k', ∀ A ∈ (Y₀ k k').support,
      μ₀ ⟨k', r₀ k'⟩ - degree ω c (q A) = μ₀ ⟨k, r₀ k⟩ + 1)
    (hK : ∀ s t l, ∀ A ∈ (K s t l).support,
      ν₀ ⟨l, s₀ l⟩ - degree ω c (q A) = ν₁ ⟨s, s₁ s⟩ + ν₂ ⟨t, s₂ t⟩ - n + 1)
    (hL : ∀ i j l, ∑ k, Q i j k * D₀ k l =
      ∑ k, D₁ i k * Q k j l + negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ k, D₂ j k * Q i k l)
    (hΦ₁D : ∀ s i', ∑ i, Φ₁ s i * D₁ i i' = ∑ s', E₁ s s' * Φ₁ s' i')
    (hΦ₂D : ∀ t j', ∑ j, Φ₂ t j * D₂ j j' = ∑ t', E₂ t t' * Φ₂ t' j')
    (hC : ∀ s t l, ∑ i, ∑ j, Φ₁ s i * Φ₂ t j * ∑ k, Q i j k * Ψ₀ k l - M s t l =
      ∑ m, K s t m * E₀ m l + ∑ m, E₁ s m * K m t l +
        negOnePowCast R (n - ν₁ ⟨s, s₁ s⟩) • ∑ m, E₂ t m * K s m l)
    (hΦ₀ : ∀ l k, ∑ m, E₀ l m * Φ₀ m k = ∑ m, Φ₀ l m * D₀ m k)
    (hinv : ∀ k k', ∑ l, Ψ₀ k l * Φ₀ l k' - (if k = k' then 1 else 0) =
      ∑ m, Y₀ k m * D₀ m k' + ∑ m, D₀ k m * Y₀ m k')
    {C₁ C₂ C₀ : ℝ}
    (hη₁ : ∀ p p',
      mapKernelOfMatrix s₁ s₁ (fun s m => coefficientComparison q hq (E₁ s m)) p p' ≠ 0 →
        G₁ p' ≤ G₁ p + C₁)
    (hη₂ : ∀ p p',
      mapKernelOfMatrix s₂ s₂ (fun t m => coefficientComparison q hq (E₂ t m)) p p' ≠ 0 →
        G₂ p' ≤ G₂ p + C₂)
    (hδ₀ : ∀ p p',
      mapKernelOfMatrix r₀ r₀ (fun k k' => coefficientComparison q hq (D₀ k k')) p p' ≠ 0 →
        F₀ p' ≤ F₀ p + C₀)
    {e f : ℤ} {a : NovikovModule R G₁} {b : NovikovModule R G₂}
    (ha : a ∈ (kernelMap hη₁ (mapKernelOfMatrix_mem hG₁ s₁ s₁ _)).cocycles
      (gradeBy R G₁ fun p => n - ν₁ p) e)
    (hb : b ∈ (kernelMap hη₂ (mapKernelOfMatrix_mem hG₂ s₂ s₂ _)).cocycles
      (gradeBy R G₂ fun p => n - ν₂ p) f) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀ (fun i j k => coefficientComparison q hq (Q i j k))
          (novikovMapOfMatrix hG₁ hF₁ s₁ r₁ (fun s i => coefficientComparison q hq (Φ₁ s i)) a)
          (novikovMapOfMatrix hG₂ hF₂ s₂ r₂ (fun t j => coefficientComparison q hq (Φ₂ t j)) b) -
        novikovMapOfMatrix hG₀ hF₀ s₀ r₀ (fun l k => coefficientComparison q hq (Φ₀ l k))
          (novikovProductOfMatrix hG₁ hG₂ hG₀ s₁ s₂ s₀
            (fun s t l => coefficientComparison q hq (M s t l)) a b) ∈
      (kernelMap hδ₀ (mapKernelOfMatrix_mem hF₀ r₀ r₀ _)).coboundaries
        (gradeBy R F₀ fun p => n - μ₀ p) (e + f) := by
  rw [LinearMap.mem_cocycles_iff] at ha hb
  have hEa : novikovMapOfMatrix hG₁ hG₁ s₁ s₁ (fun s m => coefficientComparison q hq (E₁ s m)) a =
      0 := by
    rw [novikovMapOfMatrix_eq_kernelMap hG₁ hG₁ s₁ s₁ _ hη₁]
    exact ha.1
  have hEb : novikovMapOfMatrix hG₂ hG₂ s₂ s₂ (fun t m => coefficientComparison q hq (E₂ t m)) b =
      0 := by
    rw [novikovMapOfMatrix_eq_kernelMap hG₂ hG₂ s₂ s₂ _ hη₂]
    exact hb.1
  -- The PSS maps preserve the cochain degree.
  have hΦa := novikovMapOfMatrix_coefficientComparison_mem_cochain_gradeBy_of_eq s₁ r₁ q hq hν₁
    hμ₁ hG₁ hF₁ hΦ₁ ha.2
  have hΦb := novikovMapOfMatrix_coefficientComparison_mem_cochain_gradeBy_of_eq s₂ r₂ q hq hν₂
    hμ₂ hG₂ hF₂ hΦ₂ hb.2
  -- The PSS maps send the cocycles `a` and `b` to cocycles of the cylinder differentials.
  have hDΦa := novikovMapOfMatrix_novikovMapOfMatrix_coefficientComparison_comm s₁ r₁ q hq hG₁ hF₁
    Φ₁ D₁ E₁ hΦ₁D a
  have hDΦb := novikovMapOfMatrix_novikovMapOfMatrix_coefficientComparison_comm s₂ r₂ q hq hG₂ hF₂
    Φ₂ D₂ E₂ hΦ₂D b
  rw [hEa, map_zero] at hDΦa
  rw [hEb, map_zero] at hDΦb
  -- The Novikov module structures, for the vanishing of maps and products at zero.
  let := module (R := R) hF₁
  let := module (R := R) hF₂
  let := module (R := R) hF₀
  let := module (R := R) hG₁
  let := module (R := R) hG₂
  let := module (R := R) hG₀
  -- So the product `T = Φ₁ a ⋆ Φ₂ b` is a cocycle, by the Leibniz rule.
  have hT := novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_eq_add r₁ r₂ r₀ q hq
    hF₁ hF₂ hF₀ hμ₁ Q D₁ D₂ D₀ n hL hΦa
    (novikovMapOfMatrix hG₂ hF₂ s₂ r₂ (fun t j => coefficientComparison q hq (Φ₂ t j)) b)
  rw [hDΦa, hDΦb, map_zero, LinearMap.zero_apply, map_zero, smul_zero, add_zero] at hT
  -- The homotopy, whose second term vanishes on cocycles.
  rw [novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_novikovProductOfMatrix
      r₁ r₂ r₀ s₁ s₂ s₀ q hq hF₁ hF₂ hF₀ hG₁ hG₂ hG₀ hν₁ Q M Φ₁ Φ₂ Ψ₀ K E₁ E₂ E₀ n Φ₀ D₀ Y₀ hC hΦ₀
      hinv ha.2 b, hEa, hEb, hT]
  simp only [map_zero, LinearMap.zero_apply, smul_zero, add_zero, sub_zero]
  refine LinearMap.mem_coboundaries_iff.2 ⟨_, Submodule.sub_mem _ ?_ ?_,
    (novikovMapOfMatrix_eq_kernelMap hF₀ hF₀ r₀ r₀ _ hδ₀ _).symm⟩
  · -- `K` lowers the cochain degree by one, so `K(a, b)` has cochain degree `e + f - 1`, which
    -- `Φ₀` preserves.
    have hKab' := novikovProductOfMatrix_coefficientComparison_mem_cochain_gradeBy_add s₁ s₂ s₀ q
      hq hG₁ hG₂ hG₀ hν₁ hν₂ hν₀ K (ε := -1) (fun s t l A hA => by rw [hK s t l A hA]; ring)
      ha.2 hb.2
    rw [← sub_eq_add_neg] at hKab'
    exact novikovMapOfMatrix_coefficientComparison_mem_cochain_gradeBy_of_eq s₀ r₀ q hq hν₀ hμ₀
      hG₀ hF₀ hΦ₀deg hKab'
  · -- `T` has cochain degree `e + f`, and `Y₀` lowers it by one.
    have hTdeg := novikovProductOfMatrix_coefficientComparison_mem_cochain_gradeBy r₁ r₂ r₀ q hq
      hF₁ hF₂ hF₀ hμ₁ hμ₂ hμ₀ Q hQ hΦa hΦb
    simpa only [← sub_eq_add_neg] using
      novikovMapOfMatrix_coefficientComparison_mem_cochain_gradeBy r₀ r₀ q hq hμ₀ hμ₀ hF₀ hF₀
        (ε := -1) (fun k k' A hA => by rw [sub_neg_eq_add]; exact hY₀ k k' A hA) hTdeg

end Homotopy

section Cohomology

variable [CommRing R] [Fintype ι₁] [Fintype ι₂] [Fintype ι₀] [Fintype κ₁] [Fintype κ₂]
  [Fintype κ₀] [DecidableEq ι₀] {F₁ : (Σ i, P₁ i) → ℝ} {F₂ : (Σ j, P₂ j) → ℝ}
  {F₀ : (Σ k, P₀ k) → ℝ} {G₁ : (Σ s, T₁ s) → ℝ} {G₂ : (Σ t, T₂ t) → ℝ} {G₀ : (Σ l, T₀ l) → ℝ}
  (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
  (hF₂ : ∀ j γ (D : P₂ j), F₂ ⟨j, γ +ᵥ D⟩ = F₂ ⟨j, D⟩ - (-area ω c) γ)
  (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)
  (hG₁ : ∀ s γ (D : T₁ s), G₁ ⟨s, γ +ᵥ D⟩ = G₁ ⟨s, D⟩ - (-area ω c) γ)
  (hG₂ : ∀ t γ (D : T₂ t), G₂ ⟨t, γ +ᵥ D⟩ = G₂ ⟨t, D⟩ - (-area ω c) γ)
  (hG₀ : ∀ l γ (D : T₀ l), G₀ ⟨l, γ +ᵥ D⟩ = G₀ ⟨l, D⟩ - (-area ω c) γ)
  {μ₁ : (Σ i, P₁ i) → ℤ} (hμ₁ : ∀ i γ (D : P₁ i), μ₁ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ₁ ⟨i, D⟩)
  {μ₂ : (Σ j, P₂ j) → ℤ} (hμ₂ : ∀ j γ (D : P₂ j), μ₂ ⟨j, γ +ᵥ D⟩ = degree ω c γ + μ₂ ⟨j, D⟩)
  {μ₀ : (Σ k, P₀ k) → ℤ} (hμ₀ : ∀ k γ (D : P₀ k), μ₀ ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₀ ⟨k, D⟩)
  {ν₁ : (Σ s, T₁ s) → ℤ} (hν₁ : ∀ s γ (D : T₁ s), ν₁ ⟨s, γ +ᵥ D⟩ = degree ω c γ + ν₁ ⟨s, D⟩)
  {ν₂ : (Σ t, T₂ t) → ℤ} (hν₂ : ∀ t γ (D : T₂ t), ν₂ ⟨t, γ +ᵥ D⟩ = degree ω c γ + ν₂ ⟨t, D⟩)
  {ν₀ : (Σ l, T₀ l) → ℤ} (hν₀ : ∀ l γ (D : T₀ l), ν₀ ⟨l, γ +ᵥ D⟩ = degree ω c γ + ν₀ ⟨l, D⟩)
  (Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (M : κ₁ → κ₂ → κ₀ → NovikovSeries R G ωG)
  (Φ₁ : κ₁ → ι₁ → NovikovSeries R G ωG) (Φ₂ : κ₂ → ι₂ → NovikovSeries R G ωG)
  (Φ₀ : κ₀ → ι₀ → NovikovSeries R G ωG) (Ψ₀ : ι₀ → κ₀ → NovikovSeries R G ωG)
  (K : κ₁ → κ₂ → κ₀ → NovikovSeries R G ωG)
  (E₁ : κ₁ → κ₁ → NovikovSeries R G ωG) (E₂ : κ₂ → κ₂ → NovikovSeries R G ωG)
  (E₀ : κ₀ → κ₀ → NovikovSeries R G ωG) (D₁ : ι₁ → ι₁ → NovikovSeries R G ωG)
  (D₂ : ι₂ → ι₂ → NovikovSeries R G ωG) (D₀ Y₀ : ι₀ → ι₀ → NovikovSeries R G ωG) (n : ℤ)
  {C₁ C₂ C₀ C₁' C₂' C₀' Cφ₁ Cφ₂ Cφ₀ CQ CM : ℝ}
  (hδ₁ : ∀ p p',
    mapKernelOfMatrix r₁ r₁ (fun i i' => coefficientComparison q hq (D₁ i i')) p p' ≠ 0 →
      F₁ p' ≤ F₁ p + C₁)
  (hδ₂ : ∀ p p',
    mapKernelOfMatrix r₂ r₂ (fun j j' => coefficientComparison q hq (D₂ j j')) p p' ≠ 0 →
      F₂ p' ≤ F₂ p + C₂)
  (hδ₀ : ∀ p p',
    mapKernelOfMatrix r₀ r₀ (fun k k' => coefficientComparison q hq (D₀ k k')) p p' ≠ 0 →
      F₀ p' ≤ F₀ p + C₀)
  (hη₁ : ∀ p p',
    mapKernelOfMatrix s₁ s₁ (fun s m => coefficientComparison q hq (E₁ s m)) p p' ≠ 0 →
      G₁ p' ≤ G₁ p + C₁')
  (hη₂ : ∀ p p',
    mapKernelOfMatrix s₂ s₂ (fun t m => coefficientComparison q hq (E₂ t m)) p p' ≠ 0 →
      G₂ p' ≤ G₂ p + C₂')
  (hη₀ : ∀ p p',
    mapKernelOfMatrix s₀ s₀ (fun l m => coefficientComparison q hq (E₀ l m)) p p' ≠ 0 →
      G₀ p' ≤ G₀ p + C₀')
  (hφ₁ : ∀ p p',
    mapKernelOfMatrix s₁ r₁ (fun s i => coefficientComparison q hq (Φ₁ s i)) p p' ≠ 0 →
      F₁ p' ≤ G₁ p + Cφ₁)
  (hφ₂ : ∀ p p',
    mapKernelOfMatrix s₂ r₂ (fun t j => coefficientComparison q hq (Φ₂ t j)) p p' ≠ 0 →
      F₂ p' ≤ G₂ p + Cφ₂)
  (hφ₀ : ∀ p p',
    mapKernelOfMatrix s₀ r₀ (fun l k => coefficientComparison q hq (Φ₀ l k)) p p' ≠ 0 →
      F₀ p' ≤ G₀ p + Cφ₀)
  (hnQ : ∀ p₁ p₂ p₀,
    kernelOfMatrix r₁ r₂ r₀ (fun i j k => coefficientComparison q hq (Q i j k)) p₁ p₂ p₀ ≠ 0 →
      F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + CQ)
  (hnM : ∀ p₁ p₂ p₀,
    kernelOfMatrix s₁ s₂ s₀ (fun s t l => coefficientComparison q hq (M s t l)) p₁ p₂ p₀ ≠ 0 →
      G₀ p₀ ≤ G₁ p₁ + G₂ p₂ + CM)
  {hQdeg : ∀ {i j : ℤ} {a : NovikovModule R F₁} {b : NovikovModule R F₂},
    a ∈ gradeBy R F₁ (fun p => n - μ₁ p) i → b ∈ gradeBy R F₂ (fun p => n - μ₂ p) j →
      kernelProduct hnQ (kernelOfMatrix_mem hF₀ r₁ r₂ r₀ _) a b ∈
        gradeBy R F₀ (fun p => n - μ₀ p) (i + j + 0)}
  {hQL : ∀ {i : ℤ} {a : NovikovModule R F₁}, a ∈ gradeBy R F₁ (fun p => n - μ₁ p) i → ∀ b,
    kernelMap hδ₀ (mapKernelOfMatrix_mem hF₀ r₀ r₀ _)
        (kernelProduct hnQ (kernelOfMatrix_mem hF₀ r₁ r₂ r₀ _) a b) =
      kernelProduct hnQ (kernelOfMatrix_mem hF₀ r₁ r₂ r₀ _)
          (kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _) a) b +
        negOnePowCast R i • kernelProduct hnQ (kernelOfMatrix_mem hF₀ r₁ r₂ r₀ _) a
          (kernelMap hδ₂ (mapKernelOfMatrix_mem hF₂ r₂ r₂ _) b)}
  {hMdeg : ∀ {i j : ℤ} {a : NovikovModule R G₁} {b : NovikovModule R G₂},
    a ∈ gradeBy R G₁ (fun p => n - ν₁ p) i → b ∈ gradeBy R G₂ (fun p => n - ν₂ p) j →
      kernelProduct hnM (kernelOfMatrix_mem hG₀ s₁ s₂ s₀ _) a b ∈
        gradeBy R G₀ (fun p => n - ν₀ p) (i + j + 0)}
  {hML : ∀ {i : ℤ} {a : NovikovModule R G₁}, a ∈ gradeBy R G₁ (fun p => n - ν₁ p) i → ∀ b,
    kernelMap hη₀ (mapKernelOfMatrix_mem hG₀ s₀ s₀ _)
        (kernelProduct hnM (kernelOfMatrix_mem hG₀ s₁ s₂ s₀ _) a b) =
      kernelProduct hnM (kernelOfMatrix_mem hG₀ s₁ s₂ s₀ _)
          (kernelMap hη₁ (mapKernelOfMatrix_mem hG₁ s₁ s₁ _) a) b +
        negOnePowCast R i • kernelProduct hnM (kernelOfMatrix_mem hG₀ s₁ s₂ s₀ _) a
          (kernelMap hη₂ (mapKernelOfMatrix_mem hG₂ s₂ s₂ _) b)}
  {hφ₁deg : ∀ {i : ℤ} {a : NovikovModule R G₁}, a ∈ gradeBy R G₁ (fun p => n - ν₁ p) i →
    kernelMap hφ₁ (mapKernelOfMatrix_mem hF₁ s₁ r₁ _) a ∈ gradeBy R F₁ (fun p => n - μ₁ p) i}
  {hφ₁D : ∀ {i : ℤ} {a : NovikovModule R G₁}, a ∈ gradeBy R G₁ (fun p => n - ν₁ p) i →
    kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _)
        (kernelMap hφ₁ (mapKernelOfMatrix_mem hF₁ s₁ r₁ _) a) =
      kernelMap hφ₁ (mapKernelOfMatrix_mem hF₁ s₁ r₁ _)
        (kernelMap hη₁ (mapKernelOfMatrix_mem hG₁ s₁ s₁ _) a)}
  {hφ₂deg : ∀ {i : ℤ} {a : NovikovModule R G₂}, a ∈ gradeBy R G₂ (fun p => n - ν₂ p) i →
    kernelMap hφ₂ (mapKernelOfMatrix_mem hF₂ s₂ r₂ _) a ∈ gradeBy R F₂ (fun p => n - μ₂ p) i}
  {hφ₂D : ∀ {i : ℤ} {a : NovikovModule R G₂}, a ∈ gradeBy R G₂ (fun p => n - ν₂ p) i →
    kernelMap hδ₂ (mapKernelOfMatrix_mem hF₂ r₂ r₂ _)
        (kernelMap hφ₂ (mapKernelOfMatrix_mem hF₂ s₂ r₂ _) a) =
      kernelMap hφ₂ (mapKernelOfMatrix_mem hF₂ s₂ r₂ _)
        (kernelMap hη₂ (mapKernelOfMatrix_mem hG₂ s₂ s₂ _) a)}
  {hφ₀deg : ∀ {i : ℤ} {a : NovikovModule R G₀}, a ∈ gradeBy R G₀ (fun p => n - ν₀ p) i →
    kernelMap hφ₀ (mapKernelOfMatrix_mem hF₀ s₀ r₀ _) a ∈ gradeBy R F₀ (fun p => n - μ₀ p) i}
  {hφ₀D : ∀ {i : ℤ} {a : NovikovModule R G₀}, a ∈ gradeBy R G₀ (fun p => n - ν₀ p) i →
    kernelMap hδ₀ (mapKernelOfMatrix_mem hF₀ r₀ r₀ _)
        (kernelMap hφ₀ (mapKernelOfMatrix_mem hF₀ s₀ r₀ _) a) =
      kernelMap hφ₀ (mapKernelOfMatrix_mem hF₀ s₀ r₀ _)
        (kernelMap hη₀ (mapKernelOfMatrix_mem hG₀ s₀ s₀ _) a)}

include hμ₁ hμ₂ hμ₀ hν₁ hν₂ hν₀ in
/-- **Multiplicativity of the PSS maps of class-indexed counts on cohomology.** Let the
pair-of-pants counts `Q` and the Morse quantum counts `M`, as ground-ring bilinear maps for any
potential bounds of their kernels, induce products of cochain degree zero on the cohomology of the
Floer and Morse differentials, graded by the cochain degrees `n - μ` and `n - ν`, and let the PSS
counts `Φ₁`, `Φ₂`, `Φ₀` induce maps on cohomology. Under the identities and index conditions of
`novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_mem_coboundaries`, which
include the comparison family `K` and the module homotopy `Y₀` between `Φ₀ Ψ₀` and the identity,
the maps induced on cohomology intertwine the products: `Φ₀ ([a] ⋆_M [b]) = Φ₁ [a] ⋆ Φ₂ [b]`. -/
theorem cohomologyMap_cohomologyProduct_kernelProduct_coefficientComparison
    (hQ : ∀ i j k, ∀ A ∈ (Q i j k).support,
      μ₀ ⟨k, r₀ k⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + μ₂ ⟨j, r₂ j⟩ - n)
    (hΦ₁ : ∀ s i, ∀ A ∈ (Φ₁ s i).support, μ₁ ⟨i, r₁ i⟩ - degree ω c (q A) = ν₁ ⟨s, s₁ s⟩)
    (hΦ₂ : ∀ t j, ∀ A ∈ (Φ₂ t j).support, μ₂ ⟨j, r₂ j⟩ - degree ω c (q A) = ν₂ ⟨t, s₂ t⟩)
    (hΦ₀deg : ∀ l k, ∀ A ∈ (Φ₀ l k).support, μ₀ ⟨k, r₀ k⟩ - degree ω c (q A) = ν₀ ⟨l, s₀ l⟩)
    (hY₀ : ∀ k k', ∀ A ∈ (Y₀ k k').support,
      μ₀ ⟨k', r₀ k'⟩ - degree ω c (q A) = μ₀ ⟨k, r₀ k⟩ + 1)
    (hK : ∀ s t l, ∀ A ∈ (K s t l).support,
      ν₀ ⟨l, s₀ l⟩ - degree ω c (q A) = ν₁ ⟨s, s₁ s⟩ + ν₂ ⟨t, s₂ t⟩ - n + 1)
    (hL : ∀ i j l, ∑ k, Q i j k * D₀ k l =
      ∑ k, D₁ i k * Q k j l + negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ k, D₂ j k * Q i k l)
    (hΦ₁D : ∀ s i', ∑ i, Φ₁ s i * D₁ i i' = ∑ s', E₁ s s' * Φ₁ s' i')
    (hΦ₂D : ∀ t j', ∑ j, Φ₂ t j * D₂ j j' = ∑ t', E₂ t t' * Φ₂ t' j')
    (hC : ∀ s t l, ∑ i, ∑ j, Φ₁ s i * Φ₂ t j * ∑ k, Q i j k * Ψ₀ k l - M s t l =
      ∑ m, K s t m * E₀ m l + ∑ m, E₁ s m * K m t l +
        negOnePowCast R (n - ν₁ ⟨s, s₁ s⟩) • ∑ m, E₂ t m * K s m l)
    (hΦ₀ : ∀ l k, ∑ m, E₀ l m * Φ₀ m k = ∑ m, Φ₀ l m * D₀ m k)
    (hinv : ∀ k k', ∑ l, Ψ₀ k l * Φ₀ l k' - (if k = k' then 1 else 0) =
      ∑ m, Y₀ k m * D₀ m k' + ∑ m, D₀ k m * Y₀ m k')
    {e f l : ℤ} (hl : e + f + 0 = l)
    (x : (kernelMap hη₁ (mapKernelOfMatrix_mem hG₁ s₁ s₁ _)).cohomology
      (gradeBy R G₁ fun p => n - ν₁ p) e)
    (y : (kernelMap hη₂ (mapKernelOfMatrix_mem hG₂ s₂ s₂ _)).cohomology
      (gradeBy R G₂ fun p => n - ν₂ p) f) :
    LinearMap.cohomologyMap (kernelMap hφ₀ (mapKernelOfMatrix_mem hF₀ s₀ r₀ _)) hφ₀deg hφ₀D l
        (LinearMap.cohomologyProduct (kernelProduct hnM (kernelOfMatrix_mem hG₀ s₁ s₂ s₀ _))
          hMdeg hML hl x y) =
      LinearMap.cohomologyProduct (kernelProduct hnQ (kernelOfMatrix_mem hF₀ r₁ r₂ r₀ _)) hQdeg hQL
        hl (LinearMap.cohomologyMap (kernelMap hφ₁ (mapKernelOfMatrix_mem hF₁ s₁ r₁ _)) hφ₁deg
          hφ₁D e x)
        (LinearMap.cohomologyMap (kernelMap hφ₂ (mapKernelOfMatrix_mem hF₂ s₂ r₂ _)) hφ₂deg hφ₂D f
          y) := by
  refine LinearMap.cohomologyMap_cohomologyProduct hl (fun ha hb => ?_) x y
  have h := novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_mem_coboundaries
    r₁ r₂ r₀ s₁ s₂ s₀ q hq hF₁ hF₂ hF₀ hG₁ hG₂ hG₀ hν₁ Q M Φ₁ Φ₂ Ψ₀ K E₁ E₂ E₀ n Φ₀ D₀ Y₀ D₁ D₂
    hμ₁ hμ₂ hμ₀ hν₂ hν₀ hQ hΦ₁ hΦ₂ hΦ₀deg hY₀ hK hL hΦ₁D hΦ₂D hC hΦ₀ hinv hη₁ hη₂ hδ₀ ha hb
  rw [novikovProductOfMatrix_eq_kernelProduct hF₁ hF₂ hF₀ r₁ r₂ r₀ _ hnQ,
    novikovMapOfMatrix_eq_kernelMap hG₁ hF₁ s₁ r₁ _ hφ₁,
    novikovMapOfMatrix_eq_kernelMap hG₂ hF₂ s₂ r₂ _ hφ₂,
    novikovMapOfMatrix_eq_kernelMap hG₀ hF₀ s₀ r₀ _ hφ₀,
    novikovProductOfMatrix_eq_kernelProduct hG₁ hG₂ hG₀ s₁ s₂ s₀ _ hnM] at h
  rw [← neg_sub, ← hl, add_zero]
  exact Submodule.neg_mem _ h

variable {g₁ : NovikovModule R F₁ →ₗ[R] NovikovModule R G₁}
  {g₂ : NovikovModule R F₂ →ₗ[R] NovikovModule R G₂}
  {g₀ : NovikovModule R F₀ →ₗ[R] NovikovModule R G₀}
  {hg₁ : ∀ {i : ℤ} {a : NovikovModule R F₁}, a ∈ gradeBy R F₁ (fun p => n - μ₁ p) i →
    g₁ a ∈ gradeBy R G₁ (fun p => n - ν₁ p) i}
  {hg₁D : ∀ {i : ℤ} {a : NovikovModule R F₁}, a ∈ gradeBy R F₁ (fun p => n - μ₁ p) i →
    kernelMap hη₁ (mapKernelOfMatrix_mem hG₁ s₁ s₁ _) (g₁ a) =
      g₁ (kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _) a)}
  {hg₂ : ∀ {i : ℤ} {a : NovikovModule R F₂}, a ∈ gradeBy R F₂ (fun p => n - μ₂ p) i →
    g₂ a ∈ gradeBy R G₂ (fun p => n - ν₂ p) i}
  {hg₂D : ∀ {i : ℤ} {a : NovikovModule R F₂}, a ∈ gradeBy R F₂ (fun p => n - μ₂ p) i →
    kernelMap hη₂ (mapKernelOfMatrix_mem hG₂ s₂ s₂ _) (g₂ a) =
      g₂ (kernelMap hδ₂ (mapKernelOfMatrix_mem hF₂ r₂ r₂ _) a)}
  {hg₀ : ∀ {i : ℤ} {a : NovikovModule R F₀}, a ∈ gradeBy R F₀ (fun p => n - μ₀ p) i →
    g₀ a ∈ gradeBy R G₀ (fun p => n - ν₀ p) i}
  {hg₀D : ∀ {i : ℤ} {a : NovikovModule R F₀}, a ∈ gradeBy R F₀ (fun p => n - μ₀ p) i →
    kernelMap hη₀ (mapKernelOfMatrix_mem hG₀ s₀ s₀ _) (g₀ a) =
      g₀ (kernelMap hδ₀ (mapKernelOfMatrix_mem hF₀ r₀ r₀ _) a)}
  {e f l : ℤ}
  {hfg₁ : ∀ {a : NovikovModule R F₁},
    a ∈ (kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _)).cocycles
      (gradeBy R F₁ fun p => n - μ₁ p) e →
    kernelMap hφ₁ (mapKernelOfMatrix_mem hF₁ s₁ r₁ _) (g₁ a) - a ∈
      (kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _)).coboundaries
        (gradeBy R F₁ fun p => n - μ₁ p) e}
  {hfg₂ : ∀ {a : NovikovModule R F₂},
    a ∈ (kernelMap hδ₂ (mapKernelOfMatrix_mem hF₂ r₂ r₂ _)).cocycles
      (gradeBy R F₂ fun p => n - μ₂ p) f →
    kernelMap hφ₂ (mapKernelOfMatrix_mem hF₂ s₂ r₂ _) (g₂ a) - a ∈
      (kernelMap hδ₂ (mapKernelOfMatrix_mem hF₂ r₂ r₂ _)).coboundaries
        (gradeBy R F₂ fun p => n - μ₂ p) f}
  {hgf₀ : ∀ {a : NovikovModule R G₀},
    a ∈ (kernelMap hη₀ (mapKernelOfMatrix_mem hG₀ s₀ s₀ _)).cocycles
      (gradeBy R G₀ fun p => n - ν₀ p) l →
    g₀ (kernelMap hφ₀ (mapKernelOfMatrix_mem hF₀ s₀ r₀ _) a) - a ∈
      (kernelMap hη₀ (mapKernelOfMatrix_mem hG₀ s₀ s₀ _)).coboundaries
        (gradeBy R G₀ fun p => n - ν₀ p) l}

variable (hφ₁deg hφ₁D hφ₂deg hφ₂D hφ₀deg hφ₀D hfg₁ hfg₂ hgf₀) in
include hμ₁ hμ₂ hμ₀ hν₁ hν₂ hν₀ hφ₁deg hφ₁D hφ₂deg hφ₂D hφ₀deg hφ₀D hfg₁ hfg₂ hgf₀ in
/-- **The inverses of the PSS maps of class-indexed counts are multiplicative on cohomology.**
Under the hypotheses of `cohomologyMap_cohomologyProduct_kernelProduct_coefficientComparison`, let
`g₁` and `g₂` be right inverses of the PSS maps `Φ₁` and `Φ₂` on the cohomology of the Floer inputs,
and `g₀` a left inverse of `Φ₀` on the cohomology of the Morse output, in the sense that `Φ₁ g₁`,
`Φ₂ g₂` and `g₀ Φ₀` are the identity up to coboundaries on cocycles. The module inverses of the PSS
maps are such, through the module homotopies of
`novikovMapOfMatrix_novikovMapOfMatrix_coefficientComparison_sub_mem_coboundaries`. Then the maps
they induce on cohomology intertwine the products: `g₀ (x ⋆ y) = g₁ x ⋆_M g₂ y` for Floer classes
`x` and `y`. Together with `LinearMap.cohomologyEquiv`, which makes a PSS map with a homotopy
inverse an isomorphism of cohomology, this says that the PSS isomorphisms are isomorphisms of
the products in both directions. -/
theorem cohomologyMap_cohomologyProduct_kernelProduct_coefficientComparison_of_inverse
    (hQ : ∀ i j k, ∀ A ∈ (Q i j k).support,
      μ₀ ⟨k, r₀ k⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + μ₂ ⟨j, r₂ j⟩ - n)
    (hΦ₁ : ∀ s i, ∀ A ∈ (Φ₁ s i).support, μ₁ ⟨i, r₁ i⟩ - degree ω c (q A) = ν₁ ⟨s, s₁ s⟩)
    (hΦ₂ : ∀ t j, ∀ A ∈ (Φ₂ t j).support, μ₂ ⟨j, r₂ j⟩ - degree ω c (q A) = ν₂ ⟨t, s₂ t⟩)
    (hΦ₀deg : ∀ l k, ∀ A ∈ (Φ₀ l k).support, μ₀ ⟨k, r₀ k⟩ - degree ω c (q A) = ν₀ ⟨l, s₀ l⟩)
    (hY₀ : ∀ k k', ∀ A ∈ (Y₀ k k').support,
      μ₀ ⟨k', r₀ k'⟩ - degree ω c (q A) = μ₀ ⟨k, r₀ k⟩ + 1)
    (hK : ∀ s t l, ∀ A ∈ (K s t l).support,
      ν₀ ⟨l, s₀ l⟩ - degree ω c (q A) = ν₁ ⟨s, s₁ s⟩ + ν₂ ⟨t, s₂ t⟩ - n + 1)
    (hL : ∀ i j l, ∑ k, Q i j k * D₀ k l =
      ∑ k, D₁ i k * Q k j l + negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ k, D₂ j k * Q i k l)
    (hΦ₁D : ∀ s i', ∑ i, Φ₁ s i * D₁ i i' = ∑ s', E₁ s s' * Φ₁ s' i')
    (hΦ₂D : ∀ t j', ∑ j, Φ₂ t j * D₂ j j' = ∑ t', E₂ t t' * Φ₂ t' j')
    (hC : ∀ s t l, ∑ i, ∑ j, Φ₁ s i * Φ₂ t j * ∑ k, Q i j k * Ψ₀ k l - M s t l =
      ∑ m, K s t m * E₀ m l + ∑ m, E₁ s m * K m t l +
        negOnePowCast R (n - ν₁ ⟨s, s₁ s⟩) • ∑ m, E₂ t m * K s m l)
    (hΦ₀ : ∀ l k, ∑ m, E₀ l m * Φ₀ m k = ∑ m, Φ₀ l m * D₀ m k)
    (hinv : ∀ k k', ∑ l, Ψ₀ k l * Φ₀ l k' - (if k = k' then 1 else 0) =
      ∑ m, Y₀ k m * D₀ m k' + ∑ m, D₀ k m * Y₀ m k')
    (hl : e + f + 0 = l)
    (x : (kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _)).cohomology
      (gradeBy R F₁ fun p => n - μ₁ p) e)
    (y : (kernelMap hδ₂ (mapKernelOfMatrix_mem hF₂ r₂ r₂ _)).cohomology
      (gradeBy R F₂ fun p => n - μ₂ p) f) :
    LinearMap.cohomologyMap g₀ hg₀ hg₀D l
        (LinearMap.cohomologyProduct (kernelProduct hnQ (kernelOfMatrix_mem hF₀ r₁ r₂ r₀ _)) hQdeg
          hQL hl x y) =
      LinearMap.cohomologyProduct (kernelProduct hnM (kernelOfMatrix_mem hG₀ s₁ s₂ s₀ _)) hMdeg hML
        hl (LinearMap.cohomologyMap g₁ hg₁ hg₁D e x) (LinearMap.cohomologyMap g₂ hg₂ hg₂D f y) :=
  LinearMap.cohomologyMap_cohomologyProduct_of_leftInverse hl
    (LinearMap.leftInverse_cohomologyMap g₁ (kernelMap hφ₁ (mapKernelOfMatrix_mem hF₁ s₁ r₁ _)) hg₁
      hg₁D hφ₁deg hφ₁D hfg₁)
    (LinearMap.leftInverse_cohomologyMap g₂ (kernelMap hφ₂ (mapKernelOfMatrix_mem hF₂ s₂ r₂ _)) hg₂
      hg₂D hφ₂deg hφ₂D hfg₂)
    (LinearMap.leftInverse_cohomologyMap (kernelMap hφ₀ (mapKernelOfMatrix_mem hF₀ s₀ r₀ _)) g₀
      hφ₀deg hφ₀D hg₀ hg₀D hgf₀)
    (cohomologyMap_cohomologyProduct_kernelProduct_coefficientComparison r₁ r₂ r₀ s₁ s₂ s₀ q hq
      hF₁ hF₂ hF₀ hG₁ hG₂ hG₀ hμ₁ hμ₂ hμ₀ hν₁ hν₂ hν₀ Q M Φ₁ Φ₂ Φ₀ Ψ₀ K E₁ E₂ E₀ D₁ D₂ D₀ Y₀ n hδ₁
      hδ₂ hδ₀ hη₁ hη₂ hη₀ hφ₁ hφ₂ hφ₀ hnQ hnM hQ hΦ₁ hΦ₂ hΦ₀deg hY₀ hK hL hΦ₁D hΦ₂D hC hΦ₀ hinv hl)
    x y

end Cohomology

end TauCeti.Floer

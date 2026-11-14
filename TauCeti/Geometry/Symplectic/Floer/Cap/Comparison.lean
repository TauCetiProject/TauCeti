/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Map
public import TauCeti.Geometry.Symplectic.Floer.Cap.Product
public import TauCeti.RingTheory.NovikovModule.Comparison

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
  have hΦa := novikovMapOfMatrix_coefficientComparison_mem_cochain_gradeBy s₁ r₁ q hq hν₁ hμ₁
    hG₁ hF₁ (ε := 0) (fun s i A hA => by rw [sub_zero]; exact hΦ₁ s i A hA) ha.2
  have hΦb := novikovMapOfMatrix_coefficientComparison_mem_cochain_gradeBy s₂ r₂ q hq hν₂ hμ₂
    hG₂ hF₂ (ε := 0) (fun t j A hA => by rw [sub_zero]; exact hΦ₂ t j A hA) hb.2
  rw [add_zero] at hΦa hΦb
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
    simpa only [add_zero] using novikovMapOfMatrix_coefficientComparison_mem_cochain_gradeBy s₀ r₀
      q hq hν₀ hμ₀ hG₀ hF₀ (ε := 0) (fun l k A hA => by rw [sub_zero]; exact hΦ₀deg l k A hA)
      hKab'
  · -- `T` has cochain degree `e + f`, and `Y₀` lowers it by one.
    have hTdeg := novikovProductOfMatrix_coefficientComparison_mem_cochain_gradeBy r₁ r₂ r₀ q hq
      hF₁ hF₂ hF₀ hμ₁ hμ₂ hμ₀ Q hQ hΦa hΦb
    simpa only [← sub_eq_add_neg] using
      novikovMapOfMatrix_coefficientComparison_mem_cochain_gradeBy r₀ r₀ q hq hμ₀ hμ₀ hF₀ hF₀
        (ε := -1) (fun k k' A hA => by rw [sub_neg_eq_add]; exact hY₀ k k' A hA) hTdeg

end Homotopy

end TauCeti.Floer

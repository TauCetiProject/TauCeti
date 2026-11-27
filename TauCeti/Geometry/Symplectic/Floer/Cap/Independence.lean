/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Ring

/-!
# The product of class-indexed counts does not depend on the auxiliary data

The pair-of-pants product counts solutions of a Floer equation on the pair of pants, which depends
on auxiliary data: the Hamiltonian perturbation and the domain-dependent almost complex structure
on the compact core, which agree with the Floer data of the three complexes on the cylindrical
ends. Two choices of these data with the same ends are joined by a path of data with fixed ends.
The rigid members of the one-parameter family of pairs of pants along such a path are counted, for
reference capped orbits `i`, `j`, `l` of the two inputs and the output, by generating series
`K i j l` in a class group `G` mapping to the period group by an area-preserving homomorphism `q`,
as in `TauCeti.Geometry.Symplectic.Floer.Cap.Product`. If `Q` and `Q'` count the rigid pairs of
pants for the two choices, the ends of the one-dimensional moduli spaces of the family give, class
by class, the identity

`Qᵢⱼₗ - Q'ᵢⱼₗ = ∑ₘ Kᵢⱼₘ D₀ₘₗ + ∑ₘ D₁ᵢₘ Kₘⱼₗ + (-1)^(n - μ₁(r₁ i)) ∑ₘ D₂ⱼₘ Kᵢₘₗ`,

where `D₁`, `D₂`, `D₀` count the rigid Floer cylinders of the three ends: the left side counts the
two ends of the parameter interval, the right side the breaking of a Floer cylinder at one of the
three ends. This is the
identity of the continuation family of pairs of pants
(`novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_eq_add`) for the identity
continuation maps, since the ends of the path do not move. This file proves:

* **The homotopy of products.** Under this identity the two products satisfy
  `a ⋆ b - a ⋆' b = d₀ K(a, b) + K(d₁ a, b) + (-1)^e K(a, d₂ b)` for `a` of cochain degree `e`
  (`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_sub_eq_add`). If the classes counted
  by `K` satisfy the index condition of rigid members of a one-parameter family, then for cocycles
  `a` and `b` the difference is the coboundary of `K(a, b)`
  (`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_sub_mem_coboundaries`), so the two
  products induce the same product on cohomology
  (`TauCeti.Floer.cohomologyProduct_kernelProduct_coefficientComparison_eq`).
* **The unit.** On a single complex, if the combination `e` of the counts `E` of rigid PSS planes
  for the first choice is a left unit of `⋆` up to coboundaries, and the combination `e'` of the
  counts `E'` for the second choice is a right unit of `⋆'`, then `e - e'` is a coboundary
  (`coordinates_symm_coefficientComparison_sub_mem_coboundaries`):
  `[e] = [e] ⋆' [e'] = [e] ⋆ [e'] = [e']`. No family joining the two PSS data is needed. With
  `Q = Q'` and `K = 0` this says that the unit class does not depend on the PSS data, or on the
  cycle representing the fundamental class that constrains the planes.
* **The cohomology ring.** When both choices satisfy the hypotheses of
  `TauCeti.Floer.cohomologyGRingOfCounts`, the two graded ring structures on the degree-wise
  cohomology are equal (`TauCeti.Floer.cohomologyGRingOfCounts_eq`): the cohomology ring does not
  depend on the auxiliary data.

The count identity, index conditions and potential bounds are the hypotheses the compactified
moduli spaces of the family are to supply; no moduli space, orientation or count is constructed
here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 12.1, on the pair-of-pants product.
-/

public section

noncomputable section

namespace TauCeti.Floer

open _root_.DirectSum NovikovModule NovikovSeries PeriodGroup

variable {R S : Type*} [AddCommGroup S] {ω : S →+ ℝ} {c : S →+ ℤ}
  {G : Type*} [AddMonoid G] {ωG : G →+ ℝ} (q : G →+ PeriodGroup ω c)
  (hq : ∀ A, area ω c (q A) = ωG A)

section Product

variable {ι₁ ι₂ ι₀ : Type*} {P₁ : ι₁ → Type*} {P₂ : ι₂ → Type*} {P₀ : ι₀ → Type*}
  [∀ i, AddTorsor (PeriodGroup ω c) (P₁ i)] [∀ j, AddTorsor (PeriodGroup ω c) (P₂ j)]
  [∀ k, AddTorsor (PeriodGroup ω c) (P₀ k)]
  (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₀ : ∀ k, P₀ k)
  [CommRing R] [Fintype ι₁] [Fintype ι₂] [Fintype ι₀]
  {F₁ : (Σ i, P₁ i) → ℝ} {F₂ : (Σ j, P₂ j) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
  (hF₂ : ∀ j γ (D : P₂ j), F₂ ⟨j, γ +ᵥ D⟩ = F₂ ⟨j, D⟩ - (-area ω c) γ)
  (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)
  {μ₁ : (Σ i, P₁ i) → ℤ} (hμ₁ : ∀ i γ (D : P₁ i), μ₁ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ₁ ⟨i, D⟩)
  (Q Q' K : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (D₁ : ι₁ → ι₁ → NovikovSeries R G ωG)
  (D₂ : ι₂ → ι₂ → NovikovSeries R G ωG) (D₀ : ι₀ → ι₀ → NovikovSeries R G ωG) (n : ℤ)

/-- For identity continuation matrices, the left side `∑ₖ Qᵢⱼₖ Φ₀ₖₗ - ∑ₛ ∑ₜ Φ₁ᵢₛ Φ₂ⱼₜ Q'ₛₜₗ` of
the continuation identity is `Qᵢⱼₗ - Q'ᵢⱼₗ`. -/
private theorem sum_mul_one_sub_sum_sum_one_mul_one_mul [DecidableEq ι₁] [DecidableEq ι₂]
    [DecidableEq ι₀] (i : ι₁) (j : ι₂) (l : ι₀) :
    ∑ k, Q i j k * (1 : Matrix ι₀ ι₀ (NovikovSeries R G ωG)) k l -
        ∑ s, ∑ t, (1 : Matrix ι₁ ι₁ (NovikovSeries R G ωG)) i s *
          (1 : Matrix ι₂ ι₂ (NovikovSeries R G ωG)) j t * Q' s t l =
      Q i j l - Q' i j l := by
  simp only [Matrix.one_apply, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

include hμ₁

/-- **The homotopy of products along a path of auxiliary data.** Let `Q` and `Q'` be the
generating series of rigid pairs of pants between reference capped orbits for two choices of
auxiliary data with the same ends, `K` those of the rigid members of the family of pairs of pants
along a path between them, and `D₁`, `D₂`, `D₀` those of rigid Floer cylinders of the two inputs
and the output, all indexed by a common class group `G`. Suppose the series obey the identity

`Qᵢⱼₗ - Q'ᵢⱼₗ = ∑ₘ Kᵢⱼₘ D₀ₘₗ + ∑ₘ D₁ᵢₘ Kₘⱼₗ + (-1)^(n - μ₁(r₁ i)) ∑ₘ D₂ⱼₘ Kᵢₘₗ`

given by the ends of the one-dimensional moduli spaces of the family. Then on the completed capped
modules, with the first input graded by the cochain degree `n - μ₁`, the operation of `K` is a
homotopy between the two products:
`a ⋆ b - a ⋆' b = d₀ K(a, b) + K(d₁ a, b) + (-1)^e K(a, d₂ b)` for `a` of degree `e`. -/
theorem novikovProductOfMatrix_coefficientComparison_sub_eq_add
    (hpath : ∀ i j l, Q i j l - Q' i j l =
      ∑ m, K i j m * D₀ m l + ∑ m, D₁ i m * K m j l +
        negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ m, D₂ j m * K i m l)
    {e : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ (fun p => n - μ₁ p) e)
    (b : NovikovModule R F₂) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (Q i j k)) a b -
        novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (Q' i j k)) a b =
      novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun m l => coefficientComparison q hq (D₀ m l))
          (novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
            (fun i j m => coefficientComparison q hq (K i j m)) a b) +
        novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j m => coefficientComparison q hq (K i j m))
          (novikovMapOfMatrix hF₁ hF₁ r₁ r₁ (fun i m => coefficientComparison q hq (D₁ i m)) a) b +
        negOnePowCast R e • novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j m => coefficientComparison q hq (K i j m)) a
          (novikovMapOfMatrix hF₂ hF₂ r₂ r₂ (fun j m => coefficientComparison q hq (D₂ j m))
            b) := by
  classical
  -- This is the homotopy of the continuation family for the identity continuation maps.
  have h := novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_eq_add r₁ r₂ r₀ q
    hq r₁ r₂ r₀ hF₁ hF₂ hF₀ hF₁ hF₂ hF₀ hμ₁ Q Q' (1 : Matrix ι₁ ι₁ (NovikovSeries R G ωG))
    (1 : Matrix ι₂ ι₂ (NovikovSeries R G ωG)) (1 : Matrix ι₀ ι₀ (NovikovSeries R G ωG)) K D₁ D₂ D₀
    n (fun i j l => (sum_mul_one_sub_sum_sum_one_mul_one_mul Q Q' i j l).trans (hpath i j l))
    ha b
  simpa only [novikovMapOfMatrix_coefficientComparison_one_apply] using h

/-- **Products along a path of auxiliary data agree on cocycles.** Under the identity of
`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_sub_eq_add`, suppose that every class
counted by `K` satisfies the index condition `μ₀(r₀) - 2 c₁(A) = μ₁(r₁) + μ₂(r₂) - n + 1` of
rigid members of a one-parameter family, whose Fredholm index at a fixed parameter is `-1`, so
that `K` lowers the cochain degree by one. Then for cocycles `a` and `b` of the cylinder
differentials, of cochain degrees `e` and `f`, the difference `a ⋆ b - a ⋆' b` is the coboundary of
`K(a, b)` in cochain degree `e + f`. The differentials are the ground-ring linear maps of the
cylinder counts, for any potential bounds of their kernels. -/
theorem novikovProductOfMatrix_coefficientComparison_sub_mem_coboundaries
    {μ₂ : (Σ j, P₂ j) → ℤ} (hμ₂ : ∀ j γ (D : P₂ j), μ₂ ⟨j, γ +ᵥ D⟩ = degree ω c γ + μ₂ ⟨j, D⟩)
    {μ₀ : (Σ k, P₀ k) → ℤ} (hμ₀ : ∀ k γ (D : P₀ k), μ₀ ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₀ ⟨k, D⟩)
    (hK : ∀ i j l, ∀ A ∈ (K i j l).support,
      μ₀ ⟨l, r₀ l⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + μ₂ ⟨j, r₂ j⟩ - n + 1)
    (hpath : ∀ i j l, Q i j l - Q' i j l =
      ∑ m, K i j m * D₀ m l + ∑ m, D₁ i m * K m j l +
        negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ m, D₂ j m * K i m l)
    {C₁ C₂ C₀ : ℝ}
    (hδ₁ : ∀ p p',
      mapKernelOfMatrix r₁ r₁ (fun i k => coefficientComparison q hq (D₁ i k)) p p' ≠ 0 →
        F₁ p' ≤ F₁ p + C₁)
    (hδ₂ : ∀ p p',
      mapKernelOfMatrix r₂ r₂ (fun j k => coefficientComparison q hq (D₂ j k)) p p' ≠ 0 →
        F₂ p' ≤ F₂ p + C₂)
    (hδ₀ : ∀ p p',
      mapKernelOfMatrix r₀ r₀ (fun k l => coefficientComparison q hq (D₀ k l)) p p' ≠ 0 →
        F₀ p' ≤ F₀ p + C₀)
    {e f : ℤ} {a : NovikovModule R F₁} {b : NovikovModule R F₂}
    (ha : a ∈ (kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _)).cocycles
      (gradeBy R F₁ fun p => n - μ₁ p) e)
    (hb : b ∈ (kernelMap hδ₂ (mapKernelOfMatrix_mem hF₂ r₂ r₂ _)).cocycles
      (gradeBy R F₂ fun p => n - μ₂ p) f) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (Q i j k)) a b -
        novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (Q' i j k)) a b ∈
      (kernelMap hδ₀ (mapKernelOfMatrix_mem hF₀ r₀ r₀ _)).coboundaries
        (gradeBy R F₀ fun p => n - μ₀ p) (e + f) := by
  classical
  -- This is the continuation statement on cocycles for the identity continuation maps.
  have h := novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_mem_coboundaries
    r₁ r₂ r₀ q hq r₁ r₂ r₀ hF₁ hF₂ hF₀ hF₁ hF₂ hF₀ hμ₁ Q Q'
    (1 : Matrix ι₁ ι₁ (NovikovSeries R G ωG)) (1 : Matrix ι₂ ι₂ (NovikovSeries R G ωG))
    (1 : Matrix ι₀ ι₀ (NovikovSeries R G ωG)) K D₁ D₂ D₀ n hμ₂ hμ₀ hK
    (fun i j l => (sum_mul_one_sub_sum_sum_one_mul_one_mul Q Q' i j l).trans (hpath i j l))
    hδ₁ hδ₂ hδ₀ ha hb
  simpa only [novikovMapOfMatrix_coefficientComparison_one_apply] using h

section Cohomology

variable {μ₂ : (Σ j, P₂ j) → ℤ} {μ₀ : (Σ k, P₀ k) → ℤ} {C₁ C₂ C₀ : ℝ}
  (hδ₁ : ∀ p p',
    mapKernelOfMatrix r₁ r₁ (fun i k => coefficientComparison q hq (D₁ i k)) p p' ≠ 0 →
      F₁ p' ≤ F₁ p + C₁)
  (hδ₂ : ∀ p p',
    mapKernelOfMatrix r₂ r₂ (fun j k => coefficientComparison q hq (D₂ j k)) p p' ≠ 0 →
      F₂ p' ≤ F₂ p + C₂)
  (hδ₀ : ∀ p p',
    mapKernelOfMatrix r₀ r₀ (fun k l => coefficientComparison q hq (D₀ k l)) p p' ≠ 0 →
      F₀ p' ≤ F₀ p + C₀)
  {CQ CQ' : ℝ}
  (hnQ : ∀ p₁ p₂ p₀,
    kernelOfMatrix r₁ r₂ r₀ (fun i j k => coefficientComparison q hq (Q i j k)) p₁ p₂ p₀ ≠ 0 →
      F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + CQ)
  (hnQ' : ∀ p₁ p₂ p₀,
    kernelOfMatrix r₁ r₂ r₀ (fun i j k => coefficientComparison q hq (Q' i j k)) p₁ p₂ p₀ ≠ 0 →
      F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + CQ')
  {ε ε' : ℤ}
  {hQdeg : ∀ {i j : ℤ} {a : NovikovModule R F₁} {b : NovikovModule R F₂},
    a ∈ gradeBy R F₁ (fun p => n - μ₁ p) i → b ∈ gradeBy R F₂ (fun p => n - μ₂ p) j →
      kernelProduct hnQ (kernelOfMatrix_mem hF₀ r₁ r₂ r₀ _) a b ∈
        gradeBy R F₀ (fun p => n - μ₀ p) (i + j + ε)}
  {hQL : ∀ {i : ℤ} {a : NovikovModule R F₁}, a ∈ gradeBy R F₁ (fun p => n - μ₁ p) i → ∀ b,
    kernelMap hδ₀ (mapKernelOfMatrix_mem hF₀ r₀ r₀ _)
        (kernelProduct hnQ (kernelOfMatrix_mem hF₀ r₁ r₂ r₀ _) a b) =
      kernelProduct hnQ (kernelOfMatrix_mem hF₀ r₁ r₂ r₀ _)
          (kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _) a) b +
        negOnePowCast R i • kernelProduct hnQ (kernelOfMatrix_mem hF₀ r₁ r₂ r₀ _) a
          (kernelMap hδ₂ (mapKernelOfMatrix_mem hF₂ r₂ r₂ _) b)}
  {hQ'deg : ∀ {i j : ℤ} {a : NovikovModule R F₁} {b : NovikovModule R F₂},
    a ∈ gradeBy R F₁ (fun p => n - μ₁ p) i → b ∈ gradeBy R F₂ (fun p => n - μ₂ p) j →
      kernelProduct hnQ' (kernelOfMatrix_mem hF₀ r₁ r₂ r₀ _) a b ∈
        gradeBy R F₀ (fun p => n - μ₀ p) (i + j + ε')}
  {hQ'L : ∀ {i : ℤ} {a : NovikovModule R F₁}, a ∈ gradeBy R F₁ (fun p => n - μ₁ p) i → ∀ b,
    kernelMap hδ₀ (mapKernelOfMatrix_mem hF₀ r₀ r₀ _)
        (kernelProduct hnQ' (kernelOfMatrix_mem hF₀ r₁ r₂ r₀ _) a b) =
      kernelProduct hnQ' (kernelOfMatrix_mem hF₀ r₁ r₂ r₀ _)
          (kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _) a) b +
        negOnePowCast R i • kernelProduct hnQ' (kernelOfMatrix_mem hF₀ r₁ r₂ r₀ _) a
          (kernelMap hδ₂ (mapKernelOfMatrix_mem hF₂ r₂ r₂ _) b)}

/-- **Products along a path of auxiliary data agree on cohomology.** Let the products `⋆` and
`⋆'` of the class-indexed counts `Q` and `Q'`, as ground-ring bilinear maps for any potential
bounds of their kernels, induce products on the cohomology of the cylinder differentials, graded by
the cochain degrees `n - μ`. The degree shift `ε` of `⋆` must be zero, as the shift of the product
of rigid counts is. Under the identity and the index condition of
`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_sub_mem_coboundaries`, the two induced
products on cohomology are equal. -/
theorem cohomologyProduct_kernelProduct_coefficientComparison_eq
    (hμ₂ : ∀ j γ (D : P₂ j), μ₂ ⟨j, γ +ᵥ D⟩ = degree ω c γ + μ₂ ⟨j, D⟩)
    (hμ₀ : ∀ k γ (D : P₀ k), μ₀ ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₀ ⟨k, D⟩)
    (hK : ∀ i j l, ∀ A ∈ (K i j l).support,
      μ₀ ⟨l, r₀ l⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + μ₂ ⟨j, r₂ j⟩ - n + 1)
    (hpath : ∀ i j l, Q i j l - Q' i j l =
      ∑ m, K i j m * D₀ m l + ∑ m, D₁ i m * K m j l +
        negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ m, D₂ j m * K i m l)
    (hε : ε = 0) {e f e₀ : ℤ} (h₀ : e + f + ε = e₀) (h₀' : e + f + ε' = e₀) :
    LinearMap.cohomologyProduct (kernelProduct hnQ (kernelOfMatrix_mem hF₀ r₁ r₂ r₀ _)) hQdeg hQL
        h₀ =
      LinearMap.cohomologyProduct (kernelProduct hnQ' (kernelOfMatrix_mem hF₀ r₁ r₂ r₀ _)) hQ'deg
        hQ'L h₀' := by
  refine LinearMap.cohomologyProduct_eq_of_sub_mem_coboundaries h₀ h₀' fun ha hb => ?_
  have h := novikovProductOfMatrix_coefficientComparison_sub_mem_coboundaries q hq r₁ r₂ r₀ hF₁
    hF₂ hF₀ hμ₁ Q Q' K D₁ D₂ D₀ n hμ₂ hμ₀ hK hpath hδ₁ hδ₂ hδ₀ ha hb
  rw [novikovProductOfMatrix_eq_kernelProduct hF₁ hF₂ hF₀ r₁ r₂ r₀ _ hnQ,
    novikovProductOfMatrix_eq_kernelProduct hF₁ hF₂ hF₀ r₁ r₂ r₀ _ hnQ'] at h
  rwa [← h₀, hε, add_zero]

end Cohomology

end Product

section Ring

variable [CommRing R] {ι : Type*} [Fintype ι] {P : ι → Type*}
  [∀ i, AddTorsor (PeriodGroup ω c) (P i)] (r : ∀ i, P i) {F : (Σ i, P i) → ℝ}
  (hF : ∀ i γ (D : P i), F ⟨i, γ +ᵥ D⟩ = F ⟨i, D⟩ - (-area ω c) γ)
  {μ : (Σ i, P i) → ℤ} (hμ : ∀ i γ (D : P i), μ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ ⟨i, D⟩)
  (n : ℤ) (D : ι → ι → NovikovSeries R G ωG) {C : ℝ}
  (hδ : ∀ p p', mapKernelOfMatrix r r (fun i k => coefficientComparison q hq (D i k)) p p' ≠ 0 →
    F p' ≤ F p + C)
  (Q Q' : ι → ι → ι → NovikovSeries R G ωG) {CQ CQ' : ℝ}
  (hnQ : ∀ p₁ p₂ p₀,
    kernelOfMatrix r r r (fun i j k => coefficientComparison q hq (Q i j k)) p₁ p₂ p₀ ≠ 0 →
      F p₀ ≤ F p₁ + F p₂ + CQ)
  (hnQ' : ∀ p₁ p₂ p₀,
    kernelOfMatrix r r r (fun i j k => coefficientComparison q hq (Q' i j k)) p₁ p₂ p₀ ≠ 0 →
      F p₀ ≤ F p₁ + F p₂ + CQ')
  (hpath : ∃ K : ι → ι → ι → NovikovSeries R G ωG,
    (∀ i j l, ∀ A ∈ (K i j l).support,
      μ ⟨l, r l⟩ - degree ω c (q A) = μ ⟨i, r i⟩ + μ ⟨j, r j⟩ - n + 1) ∧
    ∀ i j l, Q i j l - Q' i j l =
      ∑ m, K i j m * D m l + ∑ m, D i m * K m j l +
        negOnePowCast R (n - μ ⟨i, r i⟩) • ∑ m, D j m * K i m l)

include hμ hpath in
/-- On a single complex, products of counts joined by a path of auxiliary data differ by a
coboundary on cocycles. -/
private theorem kernelProduct_sub_kernelProduct_mem_coboundaries {e f : ℤ}
    {a b : NovikovModule R F}
    (ha : a ∈ (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cocycles
      (gradeBy R F fun p => n - μ p) e)
    (hb : b ∈ (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cocycles
      (gradeBy R F fun p => n - μ p) f) :
    kernelProduct hnQ (kernelOfMatrix_mem hF r r r _) a b -
        kernelProduct hnQ' (kernelOfMatrix_mem hF r r r _) a b ∈
      (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).coboundaries
        (gradeBy R F fun p => n - μ p) (e + f) := by
  obtain ⟨K, hK, hKid⟩ := hpath
  rw [← novikovProductOfMatrix_eq_kernelProduct hF hF hF r r r _ hnQ,
    ← novikovProductOfMatrix_eq_kernelProduct hF hF hF r r r _ hnQ']
  exact novikovProductOfMatrix_coefficientComparison_sub_mem_coboundaries q hq r r r hF hF hF hμ
    Q Q' K D D D n hμ hμ hK hKid hδ hδ hδ ha hb

variable
  (hQ : ∀ i j k, ∀ A ∈ (Q i j k).support,
    μ ⟨k, r k⟩ - degree ω c (q A) = μ ⟨i, r i⟩ + μ ⟨j, r j⟩ - n)
  (hQ' : ∀ i j k, ∀ A ∈ (Q' i j k).support,
    μ ⟨k, r k⟩ - degree ω c (q A) = μ ⟨i, r i⟩ + μ ⟨j, r j⟩ - n)
  (hL : ∀ i j l, ∑ k, Q i j k * D k l =
    ∑ k, D i k * Q k j l + negOnePowCast R (n - μ ⟨i, r i⟩) • ∑ k, D j k * Q i k l)
  (hL' : ∀ i j l, ∑ k, Q' i j k * D k l =
    ∑ k, D i k * Q' k j l + negOnePowCast R (n - μ ⟨i, r i⟩) • ∑ k, D j k * Q' i k l)
  (E E' : ι → NovikovSeries R G ωG)
  (hE : ∀ i, ∀ A ∈ (E i).support, μ ⟨i, r i⟩ - degree ω c (q A) = n)
  (hE' : ∀ i, ∀ A ∈ (E' i).support, μ ⟨i, r i⟩ - degree ω c (q A) = n)
  (hED : ∀ l, ∑ i, E i * D i l = 0) (hED' : ∀ l, ∑ i, E' i * D i l = 0)
  [DecidableEq ι]
  (hone_mul : ∃ K : ι → ι → NovikovSeries R G ωG,
    (∀ j l, ∀ A ∈ (K j l).support, μ ⟨l, r l⟩ - degree ω c (q A) = μ ⟨j, r j⟩ + 1) ∧
    ∀ j l, ∑ i, E i * Q i j l - (1 : Matrix ι ι (NovikovSeries R G ωG)) j l =
      ∑ m, K j m * D m l + ∑ m, D j m * K m l)
  (hone_mul' : ∃ K : ι → ι → NovikovSeries R G ωG,
    (∀ j l, ∀ A ∈ (K j l).support, μ ⟨l, r l⟩ - degree ω c (q A) = μ ⟨j, r j⟩ + 1) ∧
    ∀ j l, ∑ i, E' i * Q' i j l - (1 : Matrix ι ι (NovikovSeries R G ωG)) j l =
      ∑ m, K j m * D m l + ∑ m, D j m * K m l)
  (hmul_one : ∃ K : ι → ι → NovikovSeries R G ωG,
    (∀ i l, ∀ A ∈ (K i l).support, μ ⟨l, r l⟩ - degree ω c (q A) = μ ⟨i, r i⟩ + 1) ∧
    ∀ i l, ∑ j, E j * Q i j l - (1 : Matrix ι ι (NovikovSeries R G ωG)) i l =
      ∑ m, K i m * D m l + ∑ m, D i m * K m l)
  (hmul_one' : ∃ K : ι → ι → NovikovSeries R G ωG,
    (∀ i l, ∀ A ∈ (K i l).support, μ ⟨l, r l⟩ - degree ω c (q A) = μ ⟨i, r i⟩ + 1) ∧
    ∀ i l, ∑ j, E' j * Q' i j l - (1 : Matrix ι ι (NovikovSeries R G ωG)) i l =
      ∑ m, K i m * D m l + ∑ m, D i m * K m l)

include hμ hnQ hnQ' hpath hE hED hQ' hL' hE' hED' hone_mul hmul_one' in
/-- **The unit does not depend on the auxiliary data.** Let `e` and `e'` be the combinations of
the counts `E` and `E'` of rigid PSS planes for two choices of auxiliary data, with products `⋆`
and `⋆'` of the counts `Q` and `Q'` joined by a path of auxiliary data as in
`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_sub_mem_coboundaries`. If `e` is a left
unit of `⋆` up to coboundaries (`hone_mul`) and `e'` a right unit of `⋆'` (`hmul_one'`), each
through the family gluing a PSS plane into an input, then `e - e'` is a coboundary:
`[e] = [e] ⋆' [e'] = [e] ⋆ [e'] = [e']`. -/
theorem coordinates_symm_coefficientComparison_sub_mem_coboundaries :
    ((coordinates hF r).symm fun i => coefficientComparison q hq (E i)) -
        ((coordinates hF r).symm fun i => coefficientComparison q hq (E' i)) ∈
      (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).coboundaries
        (gradeBy R F fun p => n - μ p) 0 :=
  LinearMap.sub_mem_coboundaries_of_mul_sub_mem_coboundaries
    (kernelProduct hnQ (kernelOfMatrix_mem hF r r r _)) _
    (coordinates_symm_coefficientComparison_mem_cocycles_zero q hq r hF hμ n D hδ E hE hED)
    (kernelProduct_coordinates_symm_sub_mem_coboundaries_right r q hq hF r hF hμ D hδ Q hnQ E
      hone_mul)
    (kernelProduct hnQ' (kernelOfMatrix_mem hF r r r _))
    (kernelProduct_coefficientComparison_mem_cochain_gradeBy q hq r hF hμ n Q' hnQ' hQ')
    (kernelMap_kernelProduct_coefficientComparison_self_eq_add q hq r hF hμ n D hδ Q' hnQ' hL')
    _ (coordinates_symm_coefficientComparison_mem_cocycles_zero q hq r hF hμ n D hδ E' hE' hED')
    (kernelProduct_coordinates_symm_sub_mem_coboundaries_left r q hq hF r hF hμ D hδ Q' hnQ' E'
      hmul_one')
    (fun ha hb => kernelProduct_sub_kernelProduct_mem_coboundaries q hq r hF hμ n D hδ Q Q' hnQ
      hnQ' hpath ha hb)

variable
  (hassoc : ∃ K : ι → ι → ι → ι → NovikovSeries R G ωG,
    (∀ i j k l, ∀ A ∈ (K i j k l).support,
      μ ⟨l, r l⟩ - degree ω c (q A) = μ ⟨i, r i⟩ + μ ⟨j, r j⟩ + μ ⟨k, r k⟩ - 2 * n + 1) ∧
    ∀ i j k l, ∑ t, Q i j t * Q t k l - ∑ u, Q j k u * Q i u l =
      ∑ m, K i j k m * D m l + ∑ m, D i m * K m j k l +
        negOnePowCast R (n - μ ⟨i, r i⟩) • ∑ m, D j m * K i m k l +
        negOnePowCast R (n - μ ⟨i, r i⟩ + (n - μ ⟨j, r j⟩)) • ∑ m, D k m * K i j m l)
  (hassoc' : ∃ K : ι → ι → ι → ι → NovikovSeries R G ωG,
    (∀ i j k l, ∀ A ∈ (K i j k l).support,
      μ ⟨l, r l⟩ - degree ω c (q A) = μ ⟨i, r i⟩ + μ ⟨j, r j⟩ + μ ⟨k, r k⟩ - 2 * n + 1) ∧
    ∀ i j k l, ∑ t, Q' i j t * Q' t k l - ∑ u, Q' j k u * Q' i u l =
      ∑ m, K i j k m * D m l + ∑ m, D i m * K m j k l +
        negOnePowCast R (n - μ ⟨i, r i⟩) • ∑ m, D j m * K i m k l +
        negOnePowCast R (n - μ ⟨i, r i⟩ + (n - μ ⟨j, r j⟩)) • ∑ m, D k m * K i j m l)

include hpath in
/-- **The cohomology ring does not depend on the auxiliary data.** Let two choices of auxiliary
data with the same ends give counts `Q`, `E` and `Q'`, `E'` of rigid pairs of pants and PSS planes
on the same complex, each satisfying the hypotheses of `TauCeti.Floer.cohomologyGRingOfCounts`. If
the products are joined by a path of auxiliary data, whose rigid members `K` lower the cochain
degree by one and satisfy the identity of
`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_sub_eq_add` (`hpath`), then the two
graded ring structures on the degree-wise cohomology of the cylinder differential are equal: the
products and the units on cohomology coincide. -/
theorem cohomologyGRingOfCounts_eq :
    cohomologyGRingOfCounts q hq r hF hμ n D hδ Q hnQ hQ hL E hE hED hone_mul hmul_one hassoc =
      cohomologyGRingOfCounts q hq r hF hμ n D hδ Q' hnQ' hQ' hL' E' hE' hED' hone_mul' hmul_one'
        hassoc' :=
  LinearMap.cohomologyGRing_eq_of_sub_mem_coboundaries
    (kernelProduct hnQ (kernelOfMatrix_mem hF r r r _))
    (kernelProduct_coefficientComparison_mem_cochain_gradeBy q hq r hF hμ n Q hnQ hQ)
    (kernelMap_kernelProduct_coefficientComparison_self_eq_add q hq r hF hμ n D hδ Q hnQ hL)
    _ (coordinates_symm_coefficientComparison_mem_cocycles_zero q hq r hF hμ n D hδ E hE hED)
    (kernelProduct_coordinates_symm_sub_mem_coboundaries_right r q hq hF r hF hμ D hδ Q hnQ E
      hone_mul)
    (kernelProduct_coordinates_symm_sub_mem_coboundaries_left r q hq hF r hF hμ D hδ Q hnQ E
      hmul_one)
    (kernelProduct_kernelProduct_coefficientComparison_sub_mem_coboundaries q hq r hF hμ n D hδ Q
      hnQ hassoc)
    (kernelProduct hnQ' (kernelOfMatrix_mem hF r r r _))
    (kernelProduct_coefficientComparison_mem_cochain_gradeBy q hq r hF hμ n Q' hnQ' hQ')
    (kernelMap_kernelProduct_coefficientComparison_self_eq_add q hq r hF hμ n D hδ Q' hnQ' hL')
    _ (coordinates_symm_coefficientComparison_mem_cocycles_zero q hq r hF hμ n D hδ E' hE' hED')
    (kernelProduct_coordinates_symm_sub_mem_coboundaries_right r q hq hF r hF hμ D hδ Q' hnQ' E'
      hone_mul')
    (kernelProduct_coordinates_symm_sub_mem_coboundaries_left r q hq hF r hF hμ D hδ Q' hnQ' E'
      hmul_one')
    (kernelProduct_kernelProduct_coefficientComparison_sub_mem_coboundaries q hq r hF hμ n D hδ Q'
      hnQ' hassoc')
    fun ha hb => kernelProduct_sub_kernelProduct_mem_coboundaries q hq r hF hμ n D hδ Q Q' hnQ hnQ'
      hpath ha hb

end Ring

end TauCeti.Floer

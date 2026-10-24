/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Basic
public import TauCeti.RingTheory.NovikovSeries.Topology
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Bilinear products of completed combinations given by supported kernels

Let `F₁ : S₁ → ℝ`, `F₂ : S₂ → ℝ` and `F₀ : S₀ → ℝ` be potentials, and let
`n : S₁ → S₂ → S₀ → R` be a *product kernel*: `n p₁ p₂ p₀` is the coefficient of the output
generator `p₀` in the product of the input generators `p₁` and `p₂`. Suppose that

* `n p₁ p₂ p₀ ≠ 0` implies `F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C` for a fixed constant `C`, and
* each output function `n p₁ p₂` is itself a completed combination, that is, it has only finitely
  many nonzero coefficients above every threshold of `F₀`.

Then for completed combinations `a` and `b` the sum `∑ a(p₁) b(p₂) n(p₁, p₂, p₀)` has finitely many
nonzero terms, and it defines a bilinear map
`NovikovModule R F₁ → NovikovModule R F₂ → NovikovModule R F₀` (`NovikovModule.kernelProduct`). The
product shifts potential cutoffs by `C`: if `a` and `b` vanish above `D₁` and `D₂`, then their
product vanishes above `D₁ + D₂ + C`.

This is the algebraic form of the pair-of-pants product on capped Hamiltonian Floer complexes.
The generators are capped orbits, the potentials are the action functionals, `n` counts rigid
pairs of pants whose glued cap is the output cap, and the potential bound is the energy estimate
`0 ≤ E = A₁ + A₂ - A₀ - ∫ R_K`, with `C` bounding `-∫ R_K` for the curvature `R_K` of the
perturbation. Finiteness of each `n p₁ p₂` above an action level is compactness of the moduli
spaces below an energy level.

Suppose next that each `Sₗ` is a finite disjoint union of torsors under a group `H`, that the
potentials satisfy `F (h +ᵥ p) = F p - N h`, and that the kernel is unchanged when one input and
the output are translated by the same element (recapping both by the same sphere). Choosing one
reference generator in each orbit turns the kernel into a finite matrix of Novikov series
(`NovikovModule.kernelMatrix`). The `(i, j, k)` entry lies in the period filtration at level
`F₀(r₀ k) - F₁(r₁ i) - F₂(r₂ j) - C`; this is the lower valuation bound of the output monomials.
In the lift coordinates of `TauCeti.RingTheory.NovikovModule.Basic` the product is given by the
matrix formula `(a ⋆ b)ₖ = ∑ᵢ ∑ⱼ aᵢ bⱼ Mᵢⱼₖ` (`NovikovModule.coordinates_kernelProduct`), even
for a noncommutative group `H`. Hence the product is linear over the Novikov ring in its first
argument, and for a commutative group also in its second, so that it is a Novikov-bilinear map
(`NovikovModule.novikovKernelProduct`). No discreteness or injectivity of the periods `N` is
assumed.

## Main definitions

* `TauCeti.NovikovModule.kernelProduct`: the bilinear product given by a supported kernel.
* `TauCeti.NovikovModule.kernelMatrix`: the matrix of Novikov series of an invariant kernel in
  chosen reference generators.
* `TauCeti.NovikovModule.novikovKernelProduct`: the product of an invariant kernel, as a bilinear
  map over the Novikov ring.

## Main results

* `TauCeti.NovikovModule.kernelProduct_apply_val_eq_zero`: the product shifts potential cutoffs
  by the constant of the potential bound.
* `TauCeti.NovikovModule.kernelMatrix_mem_periodFiltration`: the uniform lower period bound on
  the matrix entries.
* `TauCeti.NovikovModule.coordinates_kernelProduct`: the matrix formula for the product in lift
  coordinates.
* `TauCeti.NovikovModule.kernelProduct_smul_left`, `TauCeti.NovikovModule.kernelProduct_smul_right`:
  linearity over the Novikov ring.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the pair-of-pants product.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2, on completed modules over Novikov rings.
-/

public section

noncomputable section

open Function

namespace TauCeti

namespace NovikovModule

section Product

variable {R S₁ S₂ S₀ : Type*} {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ} {F₀ : S₀ → ℝ}

section Semiring

variable [Semiring R]

/-- Only finitely many pairs of support generators of two completed combinations have total
potential at least a given threshold. -/
theorem finite_setOf_le_add (a : NovikovModule R F₁) (b : NovikovModule R F₂) (T : ℝ) :
    {q : S₁ × S₂ | a.val q.1 ≠ 0 ∧ b.val q.2 ≠ 0 ∧ T ≤ F₁ q.1 + F₂ q.2}.Finite := by
  obtain ⟨M₁, hM₁⟩ := bddAbove_image_support a
  obtain ⟨M₂, hM₂⟩ := bddAbove_image_support b
  refine ((finite_ge a (T - M₂)).prod (finite_ge b (T - M₁))).subset ?_
  rintro ⟨s₁, s₂⟩ ⟨h₁, h₂, hT⟩
  have e₁ : F₁ s₁ ≤ M₁ := hM₁ ⟨s₁, h₁, rfl⟩
  have e₂ : F₂ s₂ ≤ M₂ := hM₂ ⟨s₂, h₂, rfl⟩
  exact ⟨⟨h₁, by linarith⟩, ⟨h₂, by linarith⟩⟩

variable {C : ℝ} {n : S₁ → S₂ → S₀ → R}

/-- For a kernel obeying a potential bound, each coefficient of the product is a sum with
finitely many nonzero terms. -/
theorem finite_support_mul_kernel
    (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
    (a : NovikovModule R F₁) (b : NovikovModule R F₂) (p₀ : S₀) :
    (support fun q : S₁ × S₂ => a.val q.1 * b.val q.2 * n q.1 q.2 p₀).Finite :=
  (finite_setOf_le_add a b (F₀ p₀ - C)).subset fun q hq => by
    have h₀ := hn _ _ _ (right_ne_zero_of_mul hq)
    exact ⟨left_ne_zero_of_mul (left_ne_zero_of_mul hq),
      right_ne_zero_of_mul (left_ne_zero_of_mul hq), by linarith⟩

/-- The product of two completed combinations by a supported kernel is a completed
combination. -/
private theorem kernel_mem (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
    (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)
    (a : NovikovModule R F₁) (b : NovikovModule R F₂) :
    (fun p₀ => ∑ᶠ q : S₁ × S₂, a.val q.1 * b.val q.2 * n q.1 q.2 p₀) ∈ NovikovModule R F₀ := by
  refine mem_iff.2 fun T => ((finite_setOf_le_add a b (T - C)).biUnion
    fun q _ => mem_iff.1 (hfin q.1 q.2) T).subset ?_
  rintro p₀ ⟨hp, hT⟩
  obtain ⟨q, hq⟩ : ∃ q : S₁ × S₂, a.val q.1 * b.val q.2 * n q.1 q.2 p₀ ≠ 0 := by
    by_contra! h
    exact hp (finsum_eq_zero_of_forall_eq_zero h)
  have h₀ := hn _ _ _ (right_ne_zero_of_mul hq)
  exact Set.mem_biUnion (x := q) ⟨left_ne_zero_of_mul (left_ne_zero_of_mul hq),
    right_ne_zero_of_mul (left_ne_zero_of_mul hq), by linarith⟩ ⟨right_ne_zero_of_mul hq, hT⟩

end Semiring

variable [CommSemiring R] {C : ℝ} {n : S₁ → S₂ → S₀ → R}
  (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
  (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)

/-- The bilinear product of completed combinations given by a kernel `n` with potential bound `C`
and completed outputs: the coefficient of `p₀` in the product of `a` and `b` is the finite sum
`∑ a(p₁) b(p₂) n(p₁, p₂, p₀)` over all pairs of generators. -/
def kernelProduct : NovikovModule R F₁ →ₗ[R] NovikovModule R F₂ →ₗ[R] NovikovModule R F₀ :=
  LinearMap.mk₂ R (fun a b => ⟨_, kernel_mem hn hfin a b⟩)
    (fun a a' b => Subtype.ext <| funext fun p₀ => by
      simp only [Submodule.coe_add, Pi.add_apply, add_mul]
      exact finsum_add_distrib (finite_support_mul_kernel hn a b p₀)
        (finite_support_mul_kernel hn a' b p₀))
    (fun c a b => Subtype.ext <| funext fun p₀ => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [mul_finsum' _ c (finite_support_mul_kernel hn a b p₀)]
      exact finsum_congr fun q => by ring)
    (fun a b b' => Subtype.ext <| funext fun p₀ => by
      simp only [Submodule.coe_add, Pi.add_apply, mul_add, add_mul]
      exact finsum_add_distrib (finite_support_mul_kernel hn a b p₀)
        (finite_support_mul_kernel hn a b' p₀))
    (fun c a b => Subtype.ext <| funext fun p₀ => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [mul_finsum' _ c (finite_support_mul_kernel hn a b p₀)]
      exact finsum_congr fun q => by ring)

/-- The coefficient of a generator in a product is the sum, over all pairs of input generators,
of the product of their coefficients with the kernel. -/
@[simp]
theorem kernelProduct_apply_val (a : NovikovModule R F₁) (b : NovikovModule R F₂) (p₀ : S₀) :
    (kernelProduct hn hfin a b).val p₀ = ∑ᶠ q : S₁ × S₂, a.val q.1 * b.val q.2 * n q.1 q.2 p₀ :=
  (rfl)

/-- A coefficient of a product is a sum over any finite set of pairs containing every pair of
support generators with nonzero kernel coefficient. -/
theorem kernelProduct_apply_val_eq_sum (a : NovikovModule R F₁) (b : NovikovModule R F₂)
    (p₀ : S₀) {s : Finset (S₁ × S₂)}
    (hs : ∀ q : S₁ × S₂, a.val q.1 ≠ 0 → b.val q.2 ≠ 0 → n q.1 q.2 p₀ ≠ 0 → q ∈ s) :
    (kernelProduct hn hfin a b).val p₀ = ∑ q ∈ s, a.val q.1 * b.val q.2 * n q.1 q.2 p₀ := by
  rw [kernelProduct_apply_val]
  exact finsum_eq_sum_of_support_subset _ fun q hq =>
    hs q (left_ne_zero_of_mul (left_ne_zero_of_mul hq))
      (right_ne_zero_of_mul (left_ne_zero_of_mul hq)) (right_ne_zero_of_mul hq)

/-- The product shifts potential cutoffs by the constant of the potential bound: if `a` vanishes
above `D₁` and `b` vanishes above `D₂`, then their product vanishes above `D₁ + D₂ + C`. -/
theorem kernelProduct_apply_val_eq_zero {a : NovikovModule R F₁} {b : NovikovModule R F₂}
    {D₁ D₂ : ℝ} (ha : ∀ s, D₁ < F₁ s → a.val s = 0) (hb : ∀ s, D₂ < F₂ s → b.val s = 0)
    {p₀ : S₀} (hp : D₁ + D₂ + C < F₀ p₀) : (kernelProduct hn hfin a b).val p₀ = 0 := by
  rw [kernelProduct_apply_val]
  refine finsum_eq_zero_of_forall_eq_zero fun q => ?_
  by_contra hq
  have h₁ : F₁ q.1 ≤ D₁ :=
    not_lt.1 fun h => left_ne_zero_of_mul (left_ne_zero_of_mul hq) (ha _ h)
  have h₂ : F₂ q.2 ≤ D₂ :=
    not_lt.1 fun h => right_ne_zero_of_mul (left_ne_zero_of_mul hq) (hb _ h)
  have h₀ := hn _ _ _ (right_ne_zero_of_mul hq)
  linarith

end Product

section Torsor

variable {R H ι₁ ι₂ ι₀ : Type*} [AddGroup H] {N : H →+ ℝ}
  {P₁ : ι₁ → Type*} {P₂ : ι₂ → Type*} {P₀ : ι₀ → Type*}
  [∀ i, AddTorsor H (P₁ i)] [∀ j, AddTorsor H (P₂ j)] [∀ k, AddTorsor H (P₀ k)]
  {F₁ : (Σ i, P₁ i) → ℝ} {F₂ : (Σ j, P₂ j) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  {C : ℝ} {n : (Σ i, P₁ i) → (Σ j, P₂ j) → (Σ k, P₀ k) → R}

/-- Translating both inputs of an invariant kernel is the same as translating its output by the
negatives, in reverse order. -/
theorem kernel_vadd_vadd
    (hn₁ : ∀ (g : H) i (p₁ : P₁ i) p₂ k (p₀ : P₀ k),
      n ⟨i, g +ᵥ p₁⟩ p₂ ⟨k, g +ᵥ p₀⟩ = n ⟨i, p₁⟩ p₂ ⟨k, p₀⟩)
    (hn₂ : ∀ (g : H) p₁ j (p₂ : P₂ j) k (p₀ : P₀ k),
      n p₁ ⟨j, g +ᵥ p₂⟩ ⟨k, g +ᵥ p₀⟩ = n p₁ ⟨j, p₂⟩ ⟨k, p₀⟩)
    (u v : H) {i : ι₁} {j : ι₂} {k : ι₀} (p₁ : P₁ i) (p₂ : P₂ j) (p₀ : P₀ k) :
    n ⟨i, u +ᵥ p₁⟩ ⟨j, v +ᵥ p₂⟩ ⟨k, p₀⟩ = n ⟨i, p₁⟩ ⟨j, p₂⟩ ⟨k, -v +ᵥ (-u +ᵥ p₀)⟩ := by
  have h₁ := hn₁ u i p₁ ⟨j, v +ᵥ p₂⟩ k (-u +ᵥ p₀)
  have h₂ := hn₂ v ⟨i, p₁⟩ j p₂ k (-v +ᵥ (-u +ᵥ p₀))
  rw [vadd_neg_vadd] at h₁ h₂
  exact h₁.trans h₂

section Matrix

variable [Semiring R] [Finite ι₀] (hF₀ : ∀ k h (p : P₀ k), F₀ ⟨k, h +ᵥ p⟩ = F₀ ⟨k, p⟩ - N h)
  (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)

/-- The matrix of a kernel relative to reference generators `r₁`, `r₂` and `r₀`: the coefficient
of its `(i, j, k)` entry at `h` is the coefficient of the output generator `h +ᵥ r₀ k` in the
product of the reference inputs `r₁ i` and `r₂ j`. -/
def kernelMatrix (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₀ : ∀ k, P₀ k) (i : ι₁) (j : ι₂) (k : ι₀) :
    NovikovSeries R H N :=
  coordinates hF₀ r₀ ⟨n ⟨i, r₁ i⟩ ⟨j, r₂ j⟩, hfin _ _⟩ k

omit [∀ i, AddTorsor H (P₁ i)] [∀ j, AddTorsor H (P₂ j)] in
/-- The coefficient at `h` of a kernel matrix entry is the kernel coefficient of the reference
inputs and the output generator `h +ᵥ r₀ k`. -/
@[simp]
theorem kernelMatrix_coeff (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₀ : ∀ k, P₀ k) (i : ι₁) (j : ι₂)
    (k : ι₀) (h : H) :
    (kernelMatrix hF₀ hfin r₁ r₂ r₀ i j k).coeff h = n ⟨i, r₁ i⟩ ⟨j, r₂ j⟩ ⟨k, h +ᵥ r₀ k⟩ := by
  rw [kernelMatrix, coordinates_coeff]

end Matrix

omit [∀ i, AddTorsor H (P₁ i)] [∀ j, AddTorsor H (P₂ j)] in
/-- Under a potential bound with constant `C`, the `(i, j, k)` entry of the kernel matrix lies in
the period filtration at level `F₀(r₀ k) - F₁(r₁ i) - F₂(r₂ j) - C`. -/
theorem kernelMatrix_mem_periodFiltration [Ring R] [Finite ι₀]
    (hF₀ : ∀ k h (p : P₀ k), F₀ ⟨k, h +ᵥ p⟩ = F₀ ⟨k, p⟩ - N h)
    (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
    (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)
    (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₀ : ∀ k, P₀ k) (i : ι₁) (j : ι₂) (k : ι₀) :
    kernelMatrix hF₀ hfin r₁ r₂ r₀ i j k ∈
      NovikovSeries.periodFiltration R N (F₀ ⟨k, r₀ k⟩ - F₁ ⟨i, r₁ i⟩ - F₂ ⟨j, r₂ j⟩ - C) := by
  refine NovikovSeries.mem_periodFiltration.2 fun h hh => ?_
  by_contra hne
  rw [kernelMatrix_coeff] at hne
  have h₀ := hn _ _ _ hne
  rw [hF₀] at h₀
  linarith

section Coordinates

variable [CommSemiring R] [Fintype ι₁] [Fintype ι₂] [Finite ι₀]
  (hF₁ : ∀ i h (p : P₁ i), F₁ ⟨i, h +ᵥ p⟩ = F₁ ⟨i, p⟩ - N h)
  (hF₂ : ∀ j h (p : P₂ j), F₂ ⟨j, h +ᵥ p⟩ = F₂ ⟨j, p⟩ - N h)
  (hF₀ : ∀ k h (p : P₀ k), F₀ ⟨k, h +ᵥ p⟩ = F₀ ⟨k, p⟩ - N h)
  (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
  (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)
  (hn₁ : ∀ (g : H) i (p₁ : P₁ i) p₂ k (p₀ : P₀ k),
    n ⟨i, g +ᵥ p₁⟩ p₂ ⟨k, g +ᵥ p₀⟩ = n ⟨i, p₁⟩ p₂ ⟨k, p₀⟩)
  (hn₂ : ∀ (g : H) p₁ j (p₂ : P₂ j) k (p₀ : P₀ k),
    n p₁ ⟨j, g +ᵥ p₂⟩ ⟨k, g +ᵥ p₀⟩ = n p₁ ⟨j, p₂⟩ ⟨k, p₀⟩)

include hn₁ hn₂ in
/-- In lift coordinates, the product of an invariant kernel is given by its kernel matrix:
`(a ⋆ b)ₖ = ∑ᵢ ∑ⱼ aᵢ bⱼ Mᵢⱼₖ`. -/
theorem coordinates_kernelProduct (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₀ : ∀ k, P₀ k)
    (a : NovikovModule R F₁) (b : NovikovModule R F₂) (k : ι₀) :
    coordinates hF₀ r₀ (kernelProduct hn hfin a b) k =
      ∑ i, ∑ j, coordinates hF₁ r₁ a i * coordinates hF₂ r₂ b j *
        kernelMatrix hF₀ hfin r₁ r₂ r₀ i j k := by
  classical
  -- Both sides are sums over the pairs of input generators contributing to the coefficient at
  -- `h`: on the right these are parametrized by orbit indices and exponent triples `(u, v, w)`
  -- with `u + v + w = h`, which `g` sends injectively onto pairs of input generators covering
  -- the support of the left side. Invariance of the kernel matches the summands.
  ext h
  set x := coordinates hF₁ r₁ a
  set y := coordinates hF₂ r₂ b
  set M := kernelMatrix hF₀ hfin r₁ r₂ r₀
  -- The exponent triples contributing to the coefficient at `h` of each term of the sum.
  let T : ι₁ × ι₂ → Finset (H × H × H) := fun ij =>
    (NovikovSeries.finite_setOf_add_add_eq (x ij.1) (y ij.2) (M ij.1 ij.2 k) h).toFinset
  have hT (ij : ι₁ × ι₂) (t : H × H × H) : t ∈ T ij ↔ t.1 + t.2.1 + t.2.2 = h ∧
      (x ij.1).coeff t.1 ≠ 0 ∧ (y ij.2).coeff t.2.1 ≠ 0 ∧ (M ij.1 ij.2 k).coeff t.2.2 ≠ 0 :=
    Set.Finite.mem_toFinset _
  -- Each contributing triple gives the pair of input generators it translates the references to.
  let g : (Σ _ : ι₁ × ι₂, H × H × H) → (Σ i, P₁ i) × (Σ j, P₂ j) :=
    fun u => (⟨u.1.1, u.2.1 +ᵥ r₁ u.1.1⟩, ⟨u.1.2, u.2.2.1 +ᵥ r₂ u.1.2⟩)
  have hR : (∑ i, ∑ j, x i * y j * M i j k).coeff h = ∑ u ∈ Finset.univ.sigma T,
      (x u.1.1).coeff u.2.1 * (y u.1.2).coeff u.2.2.1 * (M u.1.1 u.1.2 k).coeff u.2.2.2 := by
    rw [Finset.sum_sigma, Fintype.sum_prod_type]
    simp only [NovikovSeries.coeff_sum, NovikovSeries.coeff_mul_mul_eq_sum, T]
  have hs : ∀ q : (Σ i, P₁ i) × (Σ j, P₂ j), a.val q.1 ≠ 0 → b.val q.2 ≠ 0 →
      n q.1 q.2 ⟨k, h +ᵥ r₀ k⟩ ≠ 0 → q ∈ (Finset.univ.sigma T).image g := by
    rintro ⟨⟨i, p₁⟩, ⟨j, p₂⟩⟩ h₁ h₂ h₀
    refine Finset.mem_image.2 ⟨⟨(i, j), (p₁ -ᵥ r₁ i, p₂ -ᵥ r₂ j,
      -(p₂ -ᵥ r₂ j) + (-(p₁ -ᵥ r₁ i) + h))⟩,
      Finset.mem_sigma.2 ⟨Finset.mem_univ _, (hT _ _).2 ⟨?_, ?_, ?_, ?_⟩⟩, ?_⟩
    · simp only [add_assoc, add_neg_cancel_left]
    · simpa [x] using h₁
    · simpa [y] using h₂
    · rw [kernelMatrix_coeff, add_vadd, add_vadd, ← kernel_vadd_vadd hn₁ hn₂, vsub_vadd,
        vsub_vadd]
      exact h₀
    · simp [g]
  have hinj : Set.InjOn g (Finset.univ.sigma T) := by
    rintro ⟨⟨i, j⟩, ⟨u, v, w⟩⟩ hu ⟨⟨i', j'⟩, ⟨u', v', w'⟩⟩ hu' he
    simp only [g, Prod.mk.injEq, Sigma.mk.inj_iff] at he
    obtain ⟨⟨rfl, e₁⟩, ⟨rfl, e₂⟩⟩ := he
    obtain rfl := vadd_right_injective _ (eq_of_heq e₁)
    obtain rfl := vadd_right_injective _ (eq_of_heq e₂)
    have s := ((hT _ _).1 (Finset.mem_sigma.1 hu).2).1
    have s' := ((hT _ _).1 (Finset.mem_sigma.1 hu').2).1
    obtain rfl : w = w' := add_left_cancel (s.trans s'.symm)
    rfl
  rw [coordinates_coeff, kernelProduct_apply_val_eq_sum hn hfin a b _ hs,
    Finset.sum_image hinj, hR]
  refine Finset.sum_congr rfl fun u hu => ?_
  obtain ⟨⟨i, j⟩, ⟨u, v, w⟩⟩ := u
  have s := ((hT _ _).1 (Finset.mem_sigma.1 hu).2).1
  simp only [g, x, y, M, coordinates_coeff, kernelMatrix_coeff]
  rw [kernel_vadd_vadd hn₁ hn₂, ← add_vadd, ← add_vadd, ← s]
  simp [add_assoc]

end Coordinates

section Novikov

variable [CommSemiring R] [Finite ι₁] [Finite ι₂] [Finite ι₀]
  (hF₁ : ∀ i h (p : P₁ i), F₁ ⟨i, h +ᵥ p⟩ = F₁ ⟨i, p⟩ - N h)
  (hF₂ : ∀ j h (p : P₂ j), F₂ ⟨j, h +ᵥ p⟩ = F₂ ⟨j, p⟩ - N h)
  (hF₀ : ∀ k h (p : P₀ k), F₀ ⟨k, h +ᵥ p⟩ = F₀ ⟨k, p⟩ - N h)
  (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
  (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)
  (hn₁ : ∀ (g : H) i (p₁ : P₁ i) p₂ k (p₀ : P₀ k),
    n ⟨i, g +ᵥ p₁⟩ p₂ ⟨k, g +ᵥ p₀⟩ = n ⟨i, p₁⟩ p₂ ⟨k, p₀⟩)
  (hn₂ : ∀ (g : H) p₁ j (p₂ : P₂ j) k (p₀ : P₀ k),
    n p₁ ⟨j, g +ᵥ p₂⟩ ⟨k, g +ᵥ p₀⟩ = n p₁ ⟨j, p₂⟩ ⟨k, p₀⟩)

include hF₂ hn₁ hn₂ in
/-- The product of an invariant kernel is linear over the Novikov ring in its first argument. -/
theorem kernelProduct_smul_left (β : NovikovSeries R H N) (a : NovikovModule R F₁)
    (b : NovikovModule R F₂) :
    letI := module (R := R) hF₁
    letI := module (R := R) hF₀
    kernelProduct hn hfin (β • a) b = β • kernelProduct hn hfin a b := by
  let := module (R := R) hF₁
  let := module (R := R) hF₀
  have := Fintype.ofFinite ι₁
  have := Fintype.ofFinite ι₂
  let r₁ := fun i => Classical.arbitrary (P₁ i)
  let r₂ := fun j => Classical.arbitrary (P₂ j)
  let r₀ := fun k => Classical.arbitrary (P₀ k)
  refine (coordinates hF₀ r₀).injective (funext fun k => ?_)
  rw [coordinates_smul, Pi.smul_apply,
    coordinates_kernelProduct hF₁ hF₂ hF₀ hn hfin hn₁ hn₂ r₁ r₂,
    coordinates_kernelProduct hF₁ hF₂ hF₀ hn hfin hn₁ hn₂ r₁ r₂, coordinates_smul]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

end Novikov

end Torsor

section NovikovBilinear

variable {R H ι₁ ι₂ ι₀ : Type*} [CommSemiring R] [AddCommGroup H] {N : H →+ ℝ}
  {P₁ : ι₁ → Type*} {P₂ : ι₂ → Type*} {P₀ : ι₀ → Type*}
  [∀ i, AddTorsor H (P₁ i)] [∀ j, AddTorsor H (P₂ j)] [∀ k, AddTorsor H (P₀ k)]
  [Finite ι₁] [Finite ι₂] [Finite ι₀]
  {F₁ : (Σ i, P₁ i) → ℝ} {F₂ : (Σ j, P₂ j) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  {C : ℝ} {n : (Σ i, P₁ i) → (Σ j, P₂ j) → (Σ k, P₀ k) → R}
  (hF₁ : ∀ i h (p : P₁ i), F₁ ⟨i, h +ᵥ p⟩ = F₁ ⟨i, p⟩ - N h)
  (hF₂ : ∀ j h (p : P₂ j), F₂ ⟨j, h +ᵥ p⟩ = F₂ ⟨j, p⟩ - N h)
  (hF₀ : ∀ k h (p : P₀ k), F₀ ⟨k, h +ᵥ p⟩ = F₀ ⟨k, p⟩ - N h)
  (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
  (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)
  (hn₁ : ∀ (g : H) i (p₁ : P₁ i) p₂ k (p₀ : P₀ k),
    n ⟨i, g +ᵥ p₁⟩ p₂ ⟨k, g +ᵥ p₀⟩ = n ⟨i, p₁⟩ p₂ ⟨k, p₀⟩)
  (hn₂ : ∀ (g : H) p₁ j (p₂ : P₂ j) k (p₀ : P₀ k),
    n p₁ ⟨j, g +ᵥ p₂⟩ ⟨k, g +ᵥ p₀⟩ = n p₁ ⟨j, p₂⟩ ⟨k, p₀⟩)

include hF₁ hn₁ hn₂ in
/-- For a commutative group of periods, the product of an invariant kernel is linear over the
Novikov ring in its second argument. -/
theorem kernelProduct_smul_right (β : NovikovSeries R H N) (a : NovikovModule R F₁)
    (b : NovikovModule R F₂) :
    letI := module (R := R) hF₂
    letI := module (R := R) hF₀
    kernelProduct hn hfin a (β • b) = β • kernelProduct hn hfin a b := by
  let := module (R := R) hF₂
  let := module (R := R) hF₀
  have := Fintype.ofFinite ι₁
  have := Fintype.ofFinite ι₂
  let r₁ := fun i => Classical.arbitrary (P₁ i)
  let r₂ := fun j => Classical.arbitrary (P₂ j)
  let r₀ := fun k => Classical.arbitrary (P₀ k)
  refine (coordinates hF₀ r₀).injective (funext fun k => ?_)
  rw [coordinates_smul, Pi.smul_apply,
    coordinates_kernelProduct hF₁ hF₂ hF₀ hn hfin hn₁ hn₂ r₁ r₂,
    coordinates_kernelProduct hF₁ hF₂ hF₀ hn hfin hn₁ hn₂ r₁ r₂, coordinates_smul]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc, mul_left_comm β]

/-- The product of an invariant kernel, as a bilinear map over the Novikov ring, for the Novikov
module structures of `TauCeti.NovikovModule.module`. -/
def novikovKernelProduct :
    letI := module (R := R) hF₁
    letI := module (R := R) hF₂
    letI := module (R := R) hF₀
    NovikovModule R F₁ →ₗ[NovikovSeries R H N] NovikovModule R F₂ →ₗ[NovikovSeries R H N]
      NovikovModule R F₀ :=
  letI := module (R := R) hF₁
  letI := module (R := R) hF₂
  letI := module (R := R) hF₀
  LinearMap.mk₂ _ (fun a b => kernelProduct hn hfin a b)
    (fun a a' b => by rw [map_add, LinearMap.add_apply])
    (kernelProduct_smul_left hF₁ hF₂ hF₀ hn hfin hn₁ hn₂)
    (fun a b b' => map_add _ b b')
    (kernelProduct_smul_right hF₁ hF₂ hF₀ hn hfin hn₁ hn₂)

/-- The Novikov-bilinear product evaluates to the product of the kernel. -/
@[simp]
theorem novikovKernelProduct_apply (a : NovikovModule R F₁) (b : NovikovModule R F₂) :
    novikovKernelProduct hF₁ hF₂ hF₀ hn hfin hn₁ hn₂ a b = kernelProduct hn hfin a b :=
  (rfl)

end NovikovBilinear

end NovikovModule

end TauCeti

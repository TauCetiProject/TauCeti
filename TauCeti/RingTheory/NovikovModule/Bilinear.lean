/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.KernelMap
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
for a noncommutative group `H`. Fixing one input turns the product into a one-input invariant
kernel map of `TauCeti.RingTheory.NovikovModule.KernelMap`, whose coordinates are given by its own
matrix (`NovikovModule.coordinates_eq_sum_mul`). Hence the product is linear over the Novikov ring
in each argument, using only the invariance and equivariance on that side, and for a commutative
group it is a Novikov-bilinear map (`NovikovModule.novikovKernelProduct`). No discreteness or
injectivity of the periods `N` is assumed.

Conversely, for a commutative group `H` every matrix `M` of Novikov series is the matrix of an
invariant kernel (`NovikovModule.kernelOfMatrix`): the coefficient on generators in the orbits
`i`, `j` and `k` is the coefficient of `M i j k` at the displacement of the output from its
reference generator minus the displacements of the two inputs. The two constructions are inverse
to each other (`NovikovModule.kernelMatrix_kernelOfMatrix`,
`NovikovModule.kernelOfMatrix_kernelMatrix`). The kernel of a matrix whose entries obey the lower
period bounds above obeys the potential bound with the same constant, and with finitely many
orbits the kernel of every matrix obeys a potential bound for some constant. Hence every finite
matrix of Novikov series has a Novikov-bilinear product (`NovikovModule.novikovProductOfMatrix`),
given in reference coordinates by the matrix formula, and every Novikov-bilinear map of these
finitely generated modules is the product of the matrix of its values on the reference basis
(`NovikovModule.eq_novikovProductOfMatrix`). In Floer theory, the entries are the count series
`∑_A #M(x₁, x₂, x₀; A) e^(-A)` of the reference generator triples, with `A` measured against the
reference caps, and the product of this matrix is the pair-of-pants product on the completed
complexes.

Composing a product with kernel maps, on either input or on the output, gives the product of the
composite kernel (`NovikovModule.kernelMap_kernelProduct`,
`NovikovModule.kernelProduct_kernelMap_left`, `NovikovModule.kernelProduct_kernelMap_right`), and
the product is linear in the kernel (`NovikovModule.kernelProduct_add`,
`NovikovModule.kernelProduct_smul`). Hence a Leibniz rule
`d (a ⋆ b) = d a ⋆ b ± a ⋆ d b` for differentials given by kernels follows from the corresponding
identity between kernels, which is what counting the ends of one-dimensional moduli spaces gives.

## Main definitions

* `TauCeti.NovikovModule.kernelProduct`: the bilinear product given by a supported kernel.
* `TauCeti.NovikovModule.toProductKernel`: the coefficients of a bilinear map.
* `TauCeti.NovikovModule.kernelMatrix`: the matrix of Novikov series of an invariant kernel in
  chosen reference generators.
* `TauCeti.NovikovModule.novikovKernelProduct`: the product of an invariant kernel, as a bilinear
  map over the Novikov ring.
* `TauCeti.NovikovModule.kernelOfMatrix`: the invariant kernel with a given matrix of Novikov
  series.
* `TauCeti.NovikovModule.novikovProductOfMatrix`: the Novikov-bilinear product of a finite matrix
  of Novikov series.

## Main results

* `TauCeti.NovikovModule.kernelProduct_apply_val_eq_zero`: the product shifts potential cutoffs
  by the constant of the potential bound.
* `TauCeti.NovikovModule.kernelMatrix_mem_periodFiltration`: the uniform lower period bound on
  the matrix entries.
* `TauCeti.NovikovModule.coordinates_kernelProduct`: the matrix formula for the product in lift
  coordinates.
* `TauCeti.NovikovModule.kernelProduct_eq_kernelMap_left`,
  `TauCeti.NovikovModule.kernelProduct_eq_kernelMap_right`: for one input fixed, the product is
  the map of a one-input kernel.
* `TauCeti.NovikovModule.kernelMap_kernelProduct`,
  `TauCeti.NovikovModule.kernelProduct_kernelMap_left`,
  `TauCeti.NovikovModule.kernelProduct_kernelMap_right`: composites of products and kernel maps are
  products of composite kernels.
* `TauCeti.NovikovModule.kernelProduct_smul_left`, `TauCeti.NovikovModule.kernelProduct_smul_right`:
  linearity over the Novikov ring.
* `TauCeti.NovikovModule.kernelMatrix_kernelOfMatrix`,
  `TauCeti.NovikovModule.kernelOfMatrix_kernelMatrix`: invariant kernels and matrices of Novikov
  series determine each other.
* `TauCeti.NovikovModule.exists_potential_le_of_kernelOfMatrix_ne_zero`,
  `TauCeti.NovikovModule.potential_le_of_kernelOfMatrix_ne_zero`: potential bounds for the kernel
  of a matrix.
* `TauCeti.NovikovModule.coordinates_novikovProductOfMatrix`: the matrix formula for the product of
  a matrix.
* `TauCeti.NovikovModule.eq_novikovProductOfMatrix`: every Novikov-bilinear map is the product of a
  matrix.

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

/-- A coefficient of a product, summed first over the second input generator. -/
private theorem kernelProduct_apply_val_eq_finsum_left (a : NovikovModule R F₁)
    (b : NovikovModule R F₂) (p₀ : S₀) :
    (kernelProduct hn hfin a b).val p₀ = ∑ᶠ p₁, a.val p₁ * ∑ᶠ p₂, b.val p₂ * n p₁ p₂ p₀ := by
  rw [kernelProduct_apply_val, finsum_curry _ (finite_support_mul_kernel hn a b p₀)]
  refine finsum_congr fun p₁ => ?_
  rw [mul_finsum' _ _ (finite_support_mul (T := F₀ p₀ - F₁ p₁ - C) (fun p₂ h => ?_) b)]
  · exact finsum_congr fun p₂ => mul_assoc _ _ _
  · linarith [hn _ _ _ h]

/-- A coefficient of a product, summed first over the first input generator. -/
private theorem kernelProduct_apply_val_eq_finsum_right (a : NovikovModule R F₁)
    (b : NovikovModule R F₂) (p₀ : S₀) :
    (kernelProduct hn hfin a b).val p₀ = ∑ᶠ p₂, b.val p₂ * ∑ᶠ p₁, a.val p₁ * n p₁ p₂ p₀ := by
  have hf := (finite_support_mul_kernel hn a b p₀).preimage
    (Equiv.prodComm S₂ S₁).injective.injOn
  rw [kernelProduct_apply_val, ← finsum_comp_equiv (Equiv.prodComm S₂ S₁), finsum_curry _ hf]
  refine finsum_congr fun p₂ => ?_
  rw [mul_finsum' _ _ (finite_support_mul (T := F₀ p₀ - F₂ p₂ - C) (fun p₁ h => ?_) a)]
  · exact finsum_congr fun p₁ => by
      simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
      ring
  · linarith [hn _ _ _ h]

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

/-- A kernel product sends a pair of generators to the corresponding entry of the kernel. -/
@[simp]
theorem kernelProduct_ofFinsupp_single_val (p₁ : S₁) (p₂ : S₂) :
    (kernelProduct hn hfin (ofFinsupp F₁ (Finsupp.single p₁ 1))
      (ofFinsupp F₂ (Finsupp.single p₂ 1))).val = n p₁ p₂ := by
  classical
  ext p₀
  rw [kernelProduct_apply_val, finsum_eq_single _ (p₁, p₂) fun q hq => by
    obtain ⟨q₁, q₂⟩ := q
    by_cases h₁ : q₁ = p₁
    · have h₂ : q₂ ≠ p₂ := fun h₂ => hq (by rw [h₁, h₂])
      simp [Finsupp.single_apply, Ne.symm h₂]
    · simp [Finsupp.single_apply, Ne.symm h₁]]
  simp

/-- A product kernel whose outputs have finitely many nonzero coefficients maps pairs of finite
combinations to finite combinations. -/
theorem kernelProduct_ofFinsupp_mem_range (hn' : ∀ p₁ p₂, (support (n p₁ p₂)).Finite)
    (a : S₁ →₀ R) (b : S₂ →₀ R) :
    kernelProduct hn hfin (ofFinsupp F₁ a) (ofFinsupp F₂ b) ∈ LinearMap.range (ofFinsupp F₀) := by
  refine mem_range_ofFinsupp_iff.2 (((a.hasFiniteSupport.prod b.hasFiniteSupport).biUnion
    fun q _ => hn' q.1 q.2).subset ?_)
  intro p₀ hp₀
  obtain ⟨q, hq⟩ : ∃ q : S₁ × S₂, a q.1 * b q.2 * n q.1 q.2 p₀ ≠ 0 := by
    by_contra! h
    exact hp₀ (by simp [h])
  exact Set.mem_biUnion (x := q)
    ⟨left_ne_zero_of_mul (left_ne_zero_of_mul hq), right_ne_zero_of_mul (left_ne_zero_of_mul hq)⟩
    (right_ne_zero_of_mul hq)

section ProductKernel

/-- The coefficients of a bilinear map of completed combinations: the coefficient of the output
generator `p₀` in the image of the pair of input generators `p₁` and `p₂`. -/
def toProductKernel
    (B : NovikovModule R F₁ →ₗ[R] NovikovModule R F₂ →ₗ[R] NovikovModule R F₀)
    (p₁ : S₁) (p₂ : S₂) (p₀ : S₀) : R :=
  (B (ofFinsupp F₁ (Finsupp.single p₁ 1)) (ofFinsupp F₂ (Finsupp.single p₂ 1))).val p₀

variable {B : NovikovModule R F₁ →ₗ[R] NovikovModule R F₂ →ₗ[R] NovikovModule R F₀}

@[simp]
theorem toProductKernel_apply (p₁ : S₁) (p₂ : S₂) (p₀ : S₀) :
    toProductKernel B p₁ p₂ p₀ =
      (B (ofFinsupp F₁ (Finsupp.single p₁ 1)) (ofFinsupp F₂ (Finsupp.single p₂ 1))).val p₀ :=
  (rfl)

/-- Each output of the coefficients of a bilinear map is a completed combination. -/
theorem toProductKernel_mem
    (B : NovikovModule R F₁ →ₗ[R] NovikovModule R F₂ →ₗ[R] NovikovModule R F₀)
    (p₁ : S₁) (p₂ : S₂) : toProductKernel B p₁ p₂ ∈ NovikovModule R F₀ :=
  (B _ _).property

/-- The coefficients of a kernel product are its kernel. -/
@[simp]
theorem toProductKernel_kernelProduct : toProductKernel (kernelProduct hn hfin) = n := by
  ext p₁ p₂ p₀
  rw [toProductKernel_apply, kernelProduct_ofFinsupp_single_val]

end ProductKernel

section Comp

variable {S₃ : Type*} {F₃ : S₃ → ℝ} {C' C'' : ℝ}

/-- The product of a sum of kernels is the sum of their products. The three potential bounds may
have different constants. -/
theorem kernelProduct_add {n' : S₁ → S₂ → S₀ → R}
    (hn' : ∀ p₁ p₂ p₀, n' p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C')
    (hfin' : ∀ p₁ p₂, n' p₁ p₂ ∈ NovikovModule R F₀)
    (hnn' : ∀ p₁ p₂ p₀, (n + n') p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C'')
    (hfinn' : ∀ p₁ p₂, (n + n') p₁ p₂ ∈ NovikovModule R F₀) :
    kernelProduct hnn' hfinn' = kernelProduct hn hfin + kernelProduct hn' hfin' := by
  ext a b p₀
  simp only [kernelProduct_apply_val, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply,
    mul_add]
  exact finsum_add_distrib (finite_support_mul_kernel hn a b p₀)
    (finite_support_mul_kernel hn' a b p₀)

/-- The product of a scalar multiple of a kernel is the scalar multiple of its product. The two
potential bounds may have different constants. -/
theorem kernelProduct_smul (c : R)
    (hcn : ∀ p₁ p₂ p₀, (c • n) p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C')
    (hcfin : ∀ p₁ p₂, (c • n) p₁ p₂ ∈ NovikovModule R F₀) :
    kernelProduct hcn hcfin = c • kernelProduct hn hfin := by
  ext a b p₀
  simp only [kernelProduct_apply_val, LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul]
  rw [mul_finsum' _ c (finite_support_mul_kernel hn a b p₀)]
  exact finsum_congr fun q => by ring

include hn in
/-- Fixing the second input `b` of a supported product kernel gives the one-input kernel
`p₁ ↦ ∑ b(p₂) n(p₁, p₂, ·)`, which obeys a potential bound: its constant uses an upper bound of
the potential on the support of `b`. -/
theorem kernelProduct_exists_potential_le_left (b : NovikovModule R F₂) :
    ∃ D, ∀ p₁ p₀, ∑ᶠ p₂, b.val p₂ * n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + D := by
  obtain ⟨M, hM⟩ := bddAbove_image_support b
  refine ⟨M + C, fun p₁ p₀ h => ?_⟩
  obtain ⟨p₂, hp₂⟩ : ∃ p₂, b.val p₂ * n p₁ p₂ p₀ ≠ 0 := by
    by_contra! h'
    exact h (finsum_eq_zero_of_forall_eq_zero h')
  have h₂ : F₂ p₂ ≤ M := hM ⟨p₂, left_ne_zero_of_mul hp₂, rfl⟩
  linarith [hn _ _ _ (right_ne_zero_of_mul hp₂)]

include hn in
/-- Fixing the first input `a` of a supported product kernel gives the one-input kernel
`p₂ ↦ ∑ a(p₁) n(p₁, p₂, ·)`, which obeys a potential bound: its constant uses an upper bound of
the potential on the support of `a`. -/
theorem kernelProduct_exists_potential_le_right (a : NovikovModule R F₁) :
    ∃ D, ∀ p₂ p₀, ∑ᶠ p₁, a.val p₁ * n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₂ p₂ + D := by
  obtain ⟨M, hM⟩ := bddAbove_image_support a
  refine ⟨M + C, fun p₂ p₀ h => ?_⟩
  obtain ⟨p₁, hp₁⟩ : ∃ p₁, a.val p₁ * n p₁ p₂ p₀ ≠ 0 := by
    by_contra! h'
    exact h (finsum_eq_zero_of_forall_eq_zero h')
  have h₁ : F₁ p₁ ≤ M := hM ⟨p₁, left_ne_zero_of_mul hp₁, rfl⟩
  linarith [hn _ _ _ (right_ne_zero_of_mul hp₁)]

include hn hfin in
/-- The one-input kernel obtained by fixing the second input of a supported product kernel has
completed outputs. -/
theorem kernelProduct_finsum_mul_mem_left (b : NovikovModule R F₂) (p₁ : S₁) :
    (fun p₀ => ∑ᶠ p₂, b.val p₂ * n p₁ p₂ p₀) ∈ NovikovModule R F₀ :=
  finsum_mul_mem (D := F₁ p₁ + C) (fun p₂ p₀ h => by linarith [hn p₁ p₂ p₀ h]) (hfin p₁) b

include hn hfin in
/-- The one-input kernel obtained by fixing the first input of a supported product kernel has
completed outputs. -/
theorem kernelProduct_finsum_mul_mem_right (a : NovikovModule R F₁) (p₂ : S₂) :
    (fun p₀ => ∑ᶠ p₁, a.val p₁ * n p₁ p₂ p₀) ∈ NovikovModule R F₀ :=
  finsum_mul_mem (κ := fun p₁ => n p₁ p₂) (D := F₂ p₂ + C)
    (fun p₁ p₀ h => by linarith [hn p₁ p₂ p₀ h]) (hfin · p₂) a

/-- **A product as a kernel map in its first input.** For fixed `b`, the product of `a` and `b`
is the image of `a` under the one-input kernel `p₁ ↦ ∑ b(p₂) n(p₁, p₂, ·)`, for any potential
bound of that kernel. -/
theorem kernelProduct_eq_kernelMap_left {D : ℝ} (b : NovikovModule R F₂)
    (hm : ∀ p₁ p₀, ∑ᶠ p₂, b.val p₂ * n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + D)
    (hmfin : ∀ p₁, (fun p₀ => ∑ᶠ p₂, b.val p₂ * n p₁ p₂ p₀) ∈ NovikovModule R F₀)
    (a : NovikovModule R F₁) :
    kernelProduct hn hfin a b = kernelMap hm hmfin a :=
  Subtype.ext <| funext fun p₀ => by
    rw [kernelProduct_apply_val_eq_finsum_left, kernelMap_apply_val]

/-- **A product as a kernel map in its second input.** For fixed `a`, the product of `a` and `b`
is the image of `b` under the one-input kernel `p₂ ↦ ∑ a(p₁) n(p₁, p₂, ·)`, for any potential
bound of that kernel. -/
theorem kernelProduct_eq_kernelMap_right {D : ℝ} (a : NovikovModule R F₁)
    (hm : ∀ p₂ p₀, ∑ᶠ p₁, a.val p₁ * n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₂ p₂ + D)
    (hmfin : ∀ p₂, (fun p₀ => ∑ᶠ p₁, a.val p₁ * n p₁ p₂ p₀) ∈ NovikovModule R F₀)
    (b : NovikovModule R F₂) :
    kernelProduct hn hfin a b = kernelMap hm hmfin b :=
  Subtype.ext <| funext fun p₀ => by
    rw [kernelProduct_apply_val_eq_finsum_right, kernelMap_apply_val]

/-- **A kernel map applied to a product.** Applying the map of a kernel `m` to the product of
`a` and `b` is the product of `a` and `b` for the kernel obtained by composing each output of `n`
with `m`. The potential bound of the composite may have any constant. -/
theorem kernelMap_kernelProduct {m : S₀ → S₃ → R}
    (hm : ∀ p₀ p₃, m p₀ p₃ ≠ 0 → F₃ p₃ ≤ F₀ p₀ + C') (hmfin : ∀ p₀, m p₀ ∈ NovikovModule R F₃)
    (hnm : ∀ p₁ p₂ p₃, kernelComp (n p₁) m p₂ p₃ ≠ 0 → F₃ p₃ ≤ F₁ p₁ + F₂ p₂ + C'')
    (hnmfin : ∀ p₁ p₂, kernelComp (n p₁) m p₂ ∈ NovikovModule R F₃)
    (a : NovikovModule R F₁) (b : NovikovModule R F₂) :
    kernelMap hm hmfin (kernelProduct hn hfin a b) = kernelProduct hnm hnmfin a b := by
  -- For fixed `b`, the product is the map of the one-input kernel `p₁ ↦ ∑ b(p₂) n(p₁, p₂, ·)`.
  obtain ⟨D, hY⟩ := kernelProduct_exists_potential_le_left hn b
  have hYfin := kernelProduct_finsum_mul_mem_left hn hfin b
  have hYm (p₁ : S₁) (p₃ : S₃)
      (h : kernelComp (fun p₁ p₀ => ∑ᶠ p₂, b.val p₂ * n p₁ p₂ p₀) m p₁ p₃ ≠ 0) :
      F₃ p₃ ≤ F₁ p₁ + (D + C') := by
    linarith [potential_le_of_kernelComp_ne_zero (hY p₁) (hm · p₃) h]
  rw [kernelProduct_eq_kernelMap_left hn hfin b hY hYfin,
    kernelMap_kernelMap hY hYfin hm hmfin hYm fun p₁ => kernelComp_mem hm hmfin (hYfin p₁)]
  ext p₃
  rw [kernelMap_apply_val, kernelProduct_apply_val_eq_finsum_left]
  refine finsum_congr fun p₁ => congrArg (a.val p₁ * ·) ?_
  -- The composite of the kernel at `p₁` with `m` is the image of `b` under the composite of
  -- `n p₁` with `m`.
  have hn₁ (p₂ : S₂) (p₀ : S₀) (h : n p₁ p₂ p₀ ≠ 0) : F₀ p₀ ≤ F₂ p₂ + (F₁ p₁ + C) := by
    linarith [hn p₁ p₂ p₀ h]
  have hn₁m (p₂ : S₂) (p₃ : S₃) (h : kernelComp (n p₁) m p₂ p₃ ≠ 0) :
      F₃ p₃ ≤ F₂ p₂ + (F₁ p₁ + C'') := by
    linarith [hnm p₁ p₂ p₃ h]
  simpa only [kernelMap_apply_val, kernelComp_apply] using congrFun (congrArg Subtype.val
    (kernelMap_kernelMap hn₁ (hfin p₁) hm hmfin hn₁m (hnmfin p₁) b)) p₃

/-- **A product with a kernel map applied to its first input.** The product of the image of `a`
under the map of a kernel `m` with `b` is the product of `a` and `b` for the kernel obtained by
composing `m` with `n`. The potential bound of the composite may have any constant. -/
theorem kernelProduct_kernelMap_left {m : S₃ → S₁ → R}
    (hm : ∀ p₃ p₁, m p₃ p₁ ≠ 0 → F₁ p₁ ≤ F₃ p₃ + C') (hmfin : ∀ p₃, m p₃ ∈ NovikovModule R F₁)
    (hmn : ∀ p₃ p₂ p₀, kernelComp m (fun p₁ => n p₁ p₂) p₃ p₀ ≠ 0 →
      F₀ p₀ ≤ F₃ p₃ + F₂ p₂ + C'')
    (hmnfin : ∀ p₃ p₂, kernelComp m (fun p₁ => n p₁ p₂) p₃ ∈ NovikovModule R F₀)
    (a : NovikovModule R F₃) (b : NovikovModule R F₂) :
    kernelProduct hn hfin (kernelMap hm hmfin a) b = kernelProduct hmn hmnfin a b := by
  ext p₀
  rw [kernelProduct_apply_val_eq_finsum_right, kernelProduct_apply_val_eq_finsum_right]
  refine finsum_congr fun p₂ => congrArg (b.val p₂ * ·) ?_
  -- For fixed `p₂`, both sides are images under one-input kernels, composed on the left.
  have hn₂ (p₁ : S₁) (p₀ : S₀) (h : n p₁ p₂ p₀ ≠ 0) : F₀ p₀ ≤ F₁ p₁ + (F₂ p₂ + C) := by
    linarith [hn p₁ p₂ p₀ h]
  have hmn₂ (p₃ : S₃) (p₀ : S₀) (h : kernelComp m (fun p₁ => n p₁ p₂) p₃ p₀ ≠ 0) :
      F₀ p₀ ≤ F₃ p₃ + (F₂ p₂ + C'') := by
    linarith [hmn p₃ p₂ p₀ h]
  simpa only [kernelMap_apply_val] using congrFun (congrArg Subtype.val
    (kernelMap_kernelMap hm hmfin hn₂ (hfin · p₂) hmn₂ (hmnfin · p₂) a)) p₀

/-- **A product with a kernel map applied to its second input.** The product of `a` with the
image of `b` under the map of a kernel `m` is the product of `a` and `b` for the kernel obtained
by composing `m` with `n`. The potential bound of the composite may have any constant. -/
theorem kernelProduct_kernelMap_right {m : S₃ → S₂ → R}
    (hm : ∀ p₃ p₂, m p₃ p₂ ≠ 0 → F₂ p₂ ≤ F₃ p₃ + C') (hmfin : ∀ p₃, m p₃ ∈ NovikovModule R F₂)
    (hnm : ∀ p₁ p₃ p₀, kernelComp m (n p₁) p₃ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₃ p₃ + C'')
    (hnmfin : ∀ p₁ p₃, kernelComp m (n p₁) p₃ ∈ NovikovModule R F₀)
    (a : NovikovModule R F₁) (b : NovikovModule R F₃) :
    kernelProduct hn hfin a (kernelMap hm hmfin b) = kernelProduct hnm hnmfin a b := by
  ext p₀
  rw [kernelProduct_apply_val_eq_finsum_left, kernelProduct_apply_val_eq_finsum_left]
  refine finsum_congr fun p₁ => congrArg (a.val p₁ * ·) ?_
  -- For fixed `p₁`, both sides are images under one-input kernels, composed on the left.
  have hn₁ (p₂ : S₂) (p₀ : S₀) (h : n p₁ p₂ p₀ ≠ 0) : F₀ p₀ ≤ F₂ p₂ + (F₁ p₁ + C) := by
    linarith [hn p₁ p₂ p₀ h]
  have hnm₁ (p₃ : S₃) (p₀ : S₀) (h : kernelComp m (n p₁) p₃ p₀ ≠ 0) :
      F₀ p₀ ≤ F₃ p₃ + (F₁ p₁ + C'') := by
    linarith [hnm p₁ p₃ p₀ h]
  simpa only [kernelMap_apply_val] using congrFun (congrArg Subtype.val
    (kernelMap_kernelMap hm hmfin hn₁ (hfin p₁) hnm₁ (hnmfin p₁) b)) p₀

end Comp

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

variable [CommSemiring R] [Finite ι₀]
  (hF₁ : ∀ i h (p : P₁ i), F₁ ⟨i, h +ᵥ p⟩ = F₁ ⟨i, p⟩ - N h)
  (hF₂ : ∀ j h (p : P₂ j), F₂ ⟨j, h +ᵥ p⟩ = F₂ ⟨j, p⟩ - N h)
  (hF₀ : ∀ k h (p : P₀ k), F₀ ⟨k, h +ᵥ p⟩ = F₀ ⟨k, p⟩ - N h)
  (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
  (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)
  (hn₁ : ∀ (g : H) i (p₁ : P₁ i) p₂ k (p₀ : P₀ k),
    n ⟨i, g +ᵥ p₁⟩ p₂ ⟨k, g +ᵥ p₀⟩ = n ⟨i, p₁⟩ p₂ ⟨k, p₀⟩)
  (hn₂ : ∀ (g : H) p₁ j (p₂ : P₂ j) k (p₀ : P₀ k),
    n p₁ ⟨j, g +ᵥ p₂⟩ ⟨k, g +ᵥ p₀⟩ = n p₁ ⟨j, p₂⟩ ⟨k, p₀⟩)

omit [∀ j, AddTorsor H (P₂ j)] in
include hn₁ in
/-- The product of a kernel invariant in its first input is linear over the Novikov ring in its
first argument. -/
theorem kernelProduct_smul_left [Finite ι₁] (β : NovikovSeries R H N) (a : NovikovModule R F₁)
    (b : NovikovModule R F₂) :
    letI := module (R := R) hF₁
    letI := module (R := R) hF₀
    kernelProduct hn hfin (β • a) b = β • kernelProduct hn hfin a b := by
  -- For fixed `b`, the product is the map of the one-input kernel `∑ b(p₂) n(p₁, p₂, p₀)`.
  obtain ⟨D, hm⟩ := kernelProduct_exists_potential_le_left hn b
  have hinv (g : H) i (p₁ : P₁ i) k (p₀ : P₀ k) :
      ∑ᶠ p₂, b.val p₂ * n ⟨i, g +ᵥ p₁⟩ p₂ ⟨k, g +ᵥ p₀⟩ = ∑ᶠ p₂, b.val p₂ * n ⟨i, p₁⟩ p₂ ⟨k, p₀⟩ :=
    finsum_congr fun p₂ => by rw [hn₁]
  have hmfin := kernelProduct_finsum_mul_mem_left hn hfin b
  rw [kernelProduct_eq_kernelMap_left hn hfin b hm hmfin,
    kernelProduct_eq_kernelMap_left hn hfin b hm hmfin]
  exact kernelMap_smul hF₁ hF₀ hm hmfin hinv β a

omit [∀ i, AddTorsor H (P₁ i)] in
include hn₂ in
/-- The product of a kernel invariant in its second input is linear over the Novikov ring in its
second argument. -/
theorem kernelProduct_smul_right [Finite ι₂] (β : NovikovSeries R H N) (a : NovikovModule R F₁)
    (b : NovikovModule R F₂) :
    letI := module (R := R) hF₂
    letI := module (R := R) hF₀
    kernelProduct hn hfin a (β • b) = β • kernelProduct hn hfin a b := by
  -- For fixed `a`, the product is the map of the one-input kernel `∑ a(p₁) n(p₁, p₂, p₀)`.
  obtain ⟨D, hm⟩ := kernelProduct_exists_potential_le_right hn a
  have hinv (g : H) j (p₂ : P₂ j) k (p₀ : P₀ k) :
      ∑ᶠ p₁, a.val p₁ * n p₁ ⟨j, g +ᵥ p₂⟩ ⟨k, g +ᵥ p₀⟩ = ∑ᶠ p₁, a.val p₁ * n p₁ ⟨j, p₂⟩ ⟨k, p₀⟩ :=
    finsum_congr fun p₁ => by rw [hn₂]
  have hmfin := kernelProduct_finsum_mul_mem_right hn hfin a
  rw [kernelProduct_eq_kernelMap_right hn hfin a hm hmfin,
    kernelProduct_eq_kernelMap_right hn hfin a hm hmfin]
  exact kernelMap_smul hF₂ hF₀ hm hmfin hinv β b

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
    (kernelProduct_smul_left hF₁ hF₀ hn hfin hn₁)
    (fun a b b' => map_add _ b b')
    (kernelProduct_smul_right hF₂ hF₀ hn hfin hn₂)

/-- The Novikov-bilinear product evaluates to the product of the kernel. -/
@[simp]
theorem novikovKernelProduct_apply (a : NovikovModule R F₁) (b : NovikovModule R F₂) :
    novikovKernelProduct hF₁ hF₂ hF₀ hn hfin hn₁ hn₂ a b = kernelProduct hn hfin a b :=
  (rfl)

end NovikovBilinear

section OfMatrix

variable {R H ι₁ ι₂ ι₀ : Type*} [AddCommGroup H] {N : H →+ ℝ}
  {P₁ : ι₁ → Type*} {P₂ : ι₂ → Type*} {P₀ : ι₀ → Type*}
  [∀ i, AddTorsor H (P₁ i)] [∀ j, AddTorsor H (P₂ j)] [∀ k, AddTorsor H (P₀ k)]
  {F₁ : (Σ i, P₁ i) → ℝ} {F₂ : (Σ j, P₂ j) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  (hF₁ : ∀ i h (p : P₁ i), F₁ ⟨i, h +ᵥ p⟩ = F₁ ⟨i, p⟩ - N h)
  (hF₂ : ∀ j h (p : P₂ j), F₂ ⟨j, h +ᵥ p⟩ = F₂ ⟨j, p⟩ - N h)
  (hF₀ : ∀ k h (p : P₀ k), F₀ ⟨k, h +ᵥ p⟩ = F₀ ⟨k, p⟩ - N h)
  (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₀ : ∀ k, P₀ k)

section Zero

variable [Zero R] (M : ι₁ → ι₂ → ι₀ → NovikovSeries R H N)

/-- The product kernel with a given matrix `M` of Novikov series relative to reference generators
`r₁`, `r₂` and `r₀`. Its coefficient on generators `p₁`, `p₂` and `p₀` in the orbits `i`, `j` and
`k` is the coefficient of `M i j k` at the displacement of `p₀` from `r₀ k`, minus the
displacements of `p₁` and `p₂` from `r₁ i` and `r₂ j`. On invariant kernels it is the inverse of
`NovikovModule.kernelMatrix`. -/
def kernelOfMatrix (p₁ : Σ i, P₁ i) (p₂ : Σ j, P₂ j) (p₀ : Σ k, P₀ k) : R :=
  (M p₁.1 p₂.1 p₀.1).coeff (p₀.2 -ᵥ r₀ p₀.1 - (p₁.2 -ᵥ r₁ p₁.1) - (p₂.2 -ᵥ r₂ p₂.1))

/-- The coefficient of the kernel of a matrix on generators in the orbits `i`, `j` and `k` is a
coefficient of the `(i, j, k)` entry. -/
@[simp]
theorem kernelOfMatrix_apply {i : ι₁} {j : ι₂} {k : ι₀} (p₁ : P₁ i) (p₂ : P₂ j) (p₀ : P₀ k) :
    kernelOfMatrix r₁ r₂ r₀ M ⟨i, p₁⟩ ⟨j, p₂⟩ ⟨k, p₀⟩ =
      (M i j k).coeff (p₀ -ᵥ r₀ k - (p₁ -ᵥ r₁ i) - (p₂ -ᵥ r₂ j)) :=
  (rfl)

/-- The kernel of a matrix is unchanged when its first input and its output are translated by the
same element. -/
theorem kernelOfMatrix_vadd_fst (g : H) (i : ι₁) (p₁ : P₁ i) (p₂ : Σ j, P₂ j) (k : ι₀)
    (p₀ : P₀ k) :
    kernelOfMatrix r₁ r₂ r₀ M ⟨i, g +ᵥ p₁⟩ p₂ ⟨k, g +ᵥ p₀⟩ =
      kernelOfMatrix r₁ r₂ r₀ M ⟨i, p₁⟩ p₂ ⟨k, p₀⟩ := by
  simp only [kernelOfMatrix, vadd_vsub_assoc]
  congr 1
  abel

/-- The kernel of a matrix is unchanged when its second input and its output are translated by
the same element. -/
theorem kernelOfMatrix_vadd_snd (g : H) (p₁ : Σ i, P₁ i) (j : ι₂) (p₂ : P₂ j) (k : ι₀)
    (p₀ : P₀ k) :
    kernelOfMatrix r₁ r₂ r₀ M p₁ ⟨j, g +ᵥ p₂⟩ ⟨k, g +ᵥ p₀⟩ =
      kernelOfMatrix r₁ r₂ r₀ M p₁ ⟨j, p₂⟩ ⟨k, p₀⟩ := by
  simp only [kernelOfMatrix, vadd_vsub_assoc]
  congr 1
  abel

include hF₁ hF₂ hF₀ in
/-- **Every finite matrix of Novikov series has a supported kernel.** With finitely many orbits,
the kernel of any matrix of Novikov series obeys a potential bound with some constant `C`, since
the periods of the support of each of the finitely many entries are bounded below. -/
theorem exists_potential_le_of_kernelOfMatrix_ne_zero [Finite ι₁] [Finite ι₂] [Finite ι₀] :
    ∃ C, ∀ p₁ p₂ p₀, kernelOfMatrix r₁ r₂ r₀ M p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C := by
  choose b hb using fun q : ι₁ × ι₂ × ι₀ => (M q.1 q.2.1 q.2.2).bddBelow_image_support
  obtain ⟨C, hC⟩ := (Set.finite_range fun q : ι₁ × ι₂ × ι₀ =>
    F₀ ⟨q.2.2, r₀ q.2.2⟩ - F₁ ⟨q.1, r₁ q.1⟩ - F₂ ⟨q.2.1, r₂ q.2.1⟩ - b q).bddAbove
  refine ⟨C, fun ⟨i, p₁⟩ ⟨j, p₂⟩ ⟨k, p₀⟩ h => ?_⟩
  have h₁ := hb (i, j, k) ⟨_, NovikovSeries.mem_support.2 h, rfl⟩
  have h₂ := hC ⟨(i, j, k), rfl⟩
  simp only [map_sub] at h₁ h₂
  rw [potential_eq_sub_vsub hF₁ r₁ i p₁, potential_eq_sub_vsub hF₂ r₂ j p₂,
    potential_eq_sub_vsub hF₀ r₀ k p₀]
  linarith

end Zero

section Semiring

variable [Semiring R] (M : ι₁ → ι₂ → ι₀ → NovikovSeries R H N)

include hF₀ in
/-- The outputs of the kernel of a matrix are completed combinations: in the output coordinates
relative to `r₀`, the output at `p₁` and `p₂` is the family `M i j · e^(u + v)`, where `u` and `v`
are the displacements of `p₁` and `p₂` from their reference generators. -/
theorem kernelOfMatrix_mem [Finite ι₀] (p₁ : Σ i, P₁ i) (p₂ : Σ j, P₂ j) :
    kernelOfMatrix r₁ r₂ r₀ M p₁ p₂ ∈ NovikovModule R F₀ := by
  have h : kernelOfMatrix r₁ r₂ r₀ M p₁ p₂ = ((coordinates hF₀ r₀).symm fun k =>
      M p₁.1 p₂.1 k * NovikovSeries.single ((p₁.2 -ᵥ r₁ p₁.1) + (p₂.2 -ᵥ r₂ p₂.1)) 1).val := by
    funext ⟨k, p₀⟩
    simp only [kernelOfMatrix, coordinates_symm_apply, NovikovSeries.coeff_mul_single, mul_one,
      sub_sub]
  rw [h]
  exact Subtype.property _

include hF₀ in
/-- The matrix of the kernel of a matrix, relative to the same reference generators, is the
matrix itself. -/
@[simp]
theorem kernelMatrix_kernelOfMatrix [Finite ι₀] :
    kernelMatrix hF₀ (kernelOfMatrix_mem hF₀ r₁ r₂ r₀ M) r₁ r₂ r₀ = M := by
  funext i j k
  ext h
  simp

include hF₀ in
/-- An invariant kernel is the kernel of its matrix: kernels invariant under translating either
input together with the output are determined by their matrices. -/
theorem kernelOfMatrix_kernelMatrix [Finite ι₀]
    {n : (Σ i, P₁ i) → (Σ j, P₂ j) → (Σ k, P₀ k) → R}
    (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)
    (hn₁ : ∀ (g : H) i (p₁ : P₁ i) p₂ k (p₀ : P₀ k),
      n ⟨i, g +ᵥ p₁⟩ p₂ ⟨k, g +ᵥ p₀⟩ = n ⟨i, p₁⟩ p₂ ⟨k, p₀⟩)
    (hn₂ : ∀ (g : H) p₁ j (p₂ : P₂ j) k (p₀ : P₀ k),
      n p₁ ⟨j, g +ᵥ p₂⟩ ⟨k, g +ᵥ p₀⟩ = n p₁ ⟨j, p₂⟩ ⟨k, p₀⟩) :
    kernelOfMatrix r₁ r₂ r₀ (kernelMatrix hF₀ hfin r₁ r₂ r₀) = n := by
  funext ⟨i, p₁⟩ ⟨j, p₂⟩ ⟨k, p₀⟩
  have e := kernel_vadd_vadd hn₁ hn₂ (p₁ -ᵥ r₁ i) (p₂ -ᵥ r₂ j) (r₁ i) (r₂ j) p₀
  rw [vsub_vadd, vsub_vadd] at e
  have hp : (p₀ -ᵥ r₀ k - (p₁ -ᵥ r₁ i) - (p₂ -ᵥ r₂ j)) +ᵥ r₀ k =
      -(p₂ -ᵥ r₂ j) +ᵥ (-(p₁ -ᵥ r₁ i) +ᵥ p₀) := by
    rw [← add_vadd, vadd_eq_vadd_iff_neg_add_eq_vsub, ← neg_vsub_eq_vsub_rev]
    abel
  rw [kernelOfMatrix_apply, kernelMatrix_coeff, e, hp]

end Semiring

section AddGroup

variable [AddGroup R]

include hF₁ hF₂ hF₀ in
/-- **The potential bound of the kernel of a matrix.** If the `(i, j, k)` entry of the matrix lies
in the period filtration at level `F₀(r₀ k) - F₁(r₁ i) - F₂(r₂ j) - C`, then the kernel obeys the
potential bound with constant `C`. This is the converse of
`NovikovModule.kernelMatrix_mem_periodFiltration`. -/
theorem potential_le_of_kernelOfMatrix_ne_zero {M : ι₁ → ι₂ → ι₀ → NovikovSeries R H N} {C : ℝ}
    (hM : ∀ i j k, M i j k ∈
      NovikovSeries.periodFiltration R N (F₀ ⟨k, r₀ k⟩ - F₁ ⟨i, r₁ i⟩ - F₂ ⟨j, r₂ j⟩ - C))
    (p₁ : Σ i, P₁ i) (p₂ : Σ j, P₂ j) (p₀ : Σ k, P₀ k)
    (h : kernelOfMatrix r₁ r₂ r₀ M p₁ p₂ p₀ ≠ 0) : F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C := by
  obtain ⟨i, p₁⟩ := p₁
  obtain ⟨j, p₂⟩ := p₂
  obtain ⟨k, p₀⟩ := p₀
  have hN := not_lt.1 fun hlt => h (NovikovSeries.mem_periodFiltration.1 (hM i j k) _ hlt)
  rw [map_sub, map_sub] at hN
  rw [potential_eq_sub_vsub hF₁ r₁ i p₁, potential_eq_sub_vsub hF₂ r₂ j p₂,
    potential_eq_sub_vsub hF₀ r₀ k p₀]
  linarith

end AddGroup

section Product

variable [CommSemiring R] [Finite ι₁] [Finite ι₂] [Finite ι₀]
  (M : ι₁ → ι₂ → ι₀ → NovikovSeries R H N)

/-- **The Novikov-bilinear product of a matrix of Novikov series.** For finitely many orbits and
reference generators `r₁`, `r₂` and `r₀`, every matrix `M` of Novikov series defines the product
of its kernel `NovikovModule.kernelOfMatrix`, a bilinear map over the Novikov ring for the module
structures of `TauCeti.NovikovModule.module`. In the reference coordinates it is
`(a ⋆ b)ₖ = ∑ᵢ ∑ⱼ aᵢ bⱼ Mᵢⱼₖ` (`NovikovModule.coordinates_novikovProductOfMatrix`). -/
def novikovProductOfMatrix :
    letI := module (R := R) hF₁
    letI := module (R := R) hF₂
    letI := module (R := R) hF₀
    NovikovModule R F₁ →ₗ[NovikovSeries R H N] NovikovModule R F₂ →ₗ[NovikovSeries R H N]
      NovikovModule R F₀ :=
  novikovKernelProduct hF₁ hF₂ hF₀
    (exists_potential_le_of_kernelOfMatrix_ne_zero hF₁ hF₂ hF₀ r₁ r₂ r₀ M).choose_spec
    (kernelOfMatrix_mem hF₀ r₁ r₂ r₀ M) (kernelOfMatrix_vadd_fst r₁ r₂ r₀ M)
    (kernelOfMatrix_vadd_snd r₁ r₂ r₀ M)

/-- The coefficient of a generator in the product of a matrix is the finite sum, over all pairs of
input generators, of the product of their coefficients with the kernel of the matrix. -/
@[simp]
theorem novikovProductOfMatrix_apply_val (a : NovikovModule R F₁) (b : NovikovModule R F₂)
    (p₀ : Σ k, P₀ k) :
    (novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀ M a b).val p₀ =
      ∑ᶠ q : (Σ i, P₁ i) × (Σ j, P₂ j),
        a.val q.1 * b.val q.2 * kernelOfMatrix r₁ r₂ r₀ M q.1 q.2 p₀ :=
  (rfl)

/-- The product of a matrix is the kernel product of its kernel, for any potential bound of that
kernel. Thus the results on kernel products, such as the shift of potential cutoffs by `C` and
continuity, apply to it. -/
theorem novikovProductOfMatrix_eq_kernelProduct {C : ℝ}
    (hn : ∀ p₁ p₂ p₀, kernelOfMatrix r₁ r₂ r₀ M p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
    (a : NovikovModule R F₁) (b : NovikovModule R F₂) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀ M a b =
      kernelProduct hn (kernelOfMatrix_mem hF₀ r₁ r₂ r₀ M) a b := by
  ext p₀
  rw [novikovProductOfMatrix_apply_val, kernelProduct_apply_val]

/-- **The matrix formula for the product of a matrix.** In the coordinates relative to the
reference generators, the product of `a` and `b` is `(a ⋆ b)ₖ = ∑ᵢ ∑ⱼ aᵢ bⱼ Mᵢⱼₖ`. -/
theorem coordinates_novikovProductOfMatrix [Fintype ι₁] [Fintype ι₂] (a : NovikovModule R F₁)
    (b : NovikovModule R F₂) (k : ι₀) :
    coordinates hF₀ r₀ (novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀ M a b) k =
      ∑ i, ∑ j, coordinates hF₁ r₁ a i * coordinates hF₂ r₂ b j * M i j k := by
  rw [novikovProductOfMatrix_eq_kernelProduct hF₁ hF₂ hF₀ r₁ r₂ r₀ M
      (exists_potential_le_of_kernelOfMatrix_ne_zero hF₁ hF₂ hF₀ r₁ r₂ r₀ M).choose_spec,
    coordinates_kernelProduct hF₁ hF₂ hF₀ _ _ (kernelOfMatrix_vadd_fst r₁ r₂ r₀ M)
      (kernelOfMatrix_vadd_snd r₁ r₂ r₀ M), kernelMatrix_kernelOfMatrix]

/-- The product of two reference basis vectors has the `(i, j)` entries of the matrix as its
coordinates: `eᵢ ⋆ eⱼ = ∑ₖ Mᵢⱼₖ eₖ`. -/
@[simp]
theorem coordinates_novikovProductOfMatrix_basis (i : ι₁) (j : ι₂) (k : ι₀) :
    coordinates hF₀ r₀
      (novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀ M (basis hF₁ r₁ i) (basis hF₂ r₂ j)) k =
      M i j k := by
  classical
  have := Fintype.ofFinite ι₁
  have := Fintype.ofFinite ι₂
  simp [coordinates_novikovProductOfMatrix, Pi.single_apply]

/-- **Every Novikov-bilinear map is the product of a matrix.** A bilinear map over the Novikov ring
between finitely generated completed modules is the product of the matrix of coordinates of its
values on the reference basis vectors. -/
theorem eq_novikovProductOfMatrix (B :
    letI := module (R := R) hF₁
    letI := module (R := R) hF₂
    letI := module (R := R) hF₀
    NovikovModule R F₁ →ₗ[NovikovSeries R H N] NovikovModule R F₂ →ₗ[NovikovSeries R H N]
      NovikovModule R F₀) :
    B = novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
      (fun i j k => coordinates hF₀ r₀ (B (basis hF₁ r₁ i) (basis hF₂ r₂ j)) k) := by
  let := module (R := R) hF₁
  let := module (R := R) hF₂
  let := module (R := R) hF₀
  refine (basis hF₁ r₁).ext fun i => (basis hF₂ r₂).ext fun j => ?_
  refine (coordinates hF₀ r₀).injective (funext fun k => ?_)
  rw [coordinates_novikovProductOfMatrix_basis]

end Product

end OfMatrix

end NovikovModule

end TauCeti

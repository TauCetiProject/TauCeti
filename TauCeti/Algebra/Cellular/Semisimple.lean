/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import TauCeti.Algebra.Cellular.Simple
public import TauCeti.RingTheory.Semisimple.Wedderburn.Presentation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.Order.Preorder.Finite
import TauCeti.Algebra.Cellular.Matrix
import TauCeti.RingTheory.Semisimple.Wedderburn.Split

/-!
# Semisimplicity and Wedderburn decomposition of cellular algebras

This file formalizes the ring-general split Wedderburn decomposition of cellular algebras whose
Gram determinants are units, Graham and Lehrer's semisimplicity criterion over a field, and a
sharpness counterexample over `ℤ`.

Over an arbitrary commutative ring `R`, the cell representations `c.cellRep μ` assemble into an
`R`-algebra homomorphism

`c.cellRepPiAlgHom : A →ₐ[R] ∀ μ : Λ, Matrix (M μ) (M μ) R`.

Whenever every cell radical vanishes (in particular, whenever every `(c.gramMatrix μ).det` is a
non-zero-divisor in `R`), `c.cellRepPiAlgHom` is injective
(`TauCeti.CellularBasis.cellRepPiAlgHom_injective`,
`TauCeti.CellularBasis.cellRepPiAlgHom_injective_of_forall_det_gramMatrix_mem_nonZeroDivisors`),
without any finiteness hypothesis on `Λ`. Moreover, when `Λ` is finite and every
`(c.gramMatrix μ).det` is a unit in `R`, triangular induction along `<` upgrades
`c.cellRepPiAlgHom` to an explicit `R`-algebra isomorphism
(`TauCeti.CellularBasis.cellRepPiAlgEquiv`)

`A ≃ₐ[R] ∀ μ : Λ, Matrix (M μ) (M μ) R`,

implying `IsSemisimpleRing A` over any commutative semisimple base ring `R`
(`TauCeti.CellularBasis.isSemisimpleRing_of_forall_isUnit_det_gramMatrix`). Conversely, when `A` is
semisimple and `R` is nontrivial, every nonempty cell has nonzero bilinear form
(`TauCeti.CellularBasis.cellForm_ne_zero_of_isSemisimpleRing`).

Over a field `K`, when `B` is semisimple every cell radical vanishes, so a cell module
`d.CellModule μ` is simple if and only if `M μ` is nonempty
(`TauCeti.CellularBasis.isSimpleModule_cellModule_iff_nonempty_of_isSemisimpleRing`), and (when
`<` on `Λ` is well-founded) the nonempty cell modules classify all simple `B`-modules up to
isomorphism
(`TauCeti.CellularBasis.existsUnique_nonempty_and_nonempty_linearEquiv_of_isSemisimpleRing`).
With a finite preorder `Λ` of cells, `d.cellRepPiAlgEquiv` specializes to the split
Artin–Wedderburn isomorphism `B ≃ₐ[K] ∀ μ : Λ, Matrix (M μ) (M μ) K`, yielding **Graham–Lehrer
Theorem 3.8**: the following are equivalent:
1. `B` is a semisimple ring (`IsSemisimpleRing B`);
2. every cell radical is trivial (`∀ μ, d.cellRadical μ = ⊥`);
3. every cell bilinear form is nondegenerate (`∀ μ, (d.cellForm μ).Nondegenerate`);
4. every Gram determinant is nonzero (`∀ μ, (d.gramMatrix μ).det ≠ 0`);
5. `d.cellRepPiAlgHom` is bijective.

Moreover, any semisimple cellular `K`-algebra with well-founded cell order is automatically split
over `K` (`TauCeti.CellularBasis.nonempty_splitWedderburnAlgebraPresentation`), with no
algebraic-closure assumption on `K`. Finally, `CellularBasis.matrix ℤ Unit` witnesses that the
field hypothesis in Theorem 3.8 is sharp
(`TauCeti.CellularBasis.exists_cellularBasis_int_nondegenerate_and_not_isSemisimpleRing`).

## Main definitions

* `TauCeti.CellularBasis.cellRepPiAlgHom`: the product of all cell representations
  `A →ₐ[R] ∀ μ : Λ, Matrix (M μ) (M μ) R`.
* `TauCeti.CellularBasis.cellRepPiAlgEquiv`: the ring-general split Wedderburn `R`-algebra
  isomorphism `A ≃ₐ[R] ∀ μ : Λ, Matrix (M μ) (M μ) R` when `∀ μ, IsUnit (c.gramMatrix μ).det` and
  `[Finite Λ]`.

## Main results

* `TauCeti.CellularBasis.cellRepPiAlgHom_injective`,
  `TauCeti.CellularBasis.cellRepPiAlgHom_injective_of_forall_det_gramMatrix_mem_nonZeroDivisors`,
  `TauCeti.CellularBasis.cellRepPiAlgHom_surjective_of_forall_isUnit_det_gramMatrix`: injectivity
  when all cell radicals vanish (or all Gram determinants are non-zero-divisors) and surjectivity
  when `Λ` is finite and all Gram determinants are units.
* `TauCeti.CellularBasis.isSemisimpleRing_of_forall_isUnit_det_gramMatrix`: unit Gram determinants
  over a commutative semisimple ring imply `IsSemisimpleRing A`.
* `TauCeti.CellularBasis.isSimpleModule_cellModule_of_isSemisimpleRing`,
  `TauCeti.CellularBasis.isSimpleModule_cellModule_iff_nonempty_of_isSemisimpleRing`,
  `TauCeti.CellularBasis.nonempty_cellModule_linearEquiv_iff_of_isSemisimpleRing`,
  `TauCeti.CellularBasis.existsUnique_nonempty_and_nonempty_linearEquiv_of_isSemisimpleRing`:
  simplicity and classification of simple modules directly by nonempty cell modules `d.CellModule μ`
  when `[IsSemisimpleRing B]`.
* `TauCeti.CellularBasis.isSemisimpleRing_iff_forall_cellRadical_eq_bot`,
  `TauCeti.CellularBasis.isSemisimpleRing_iff_forall_nondegenerate_cellForm`,
  `TauCeti.CellularBasis.isSemisimpleRing_iff_forall_det_gramMatrix_ne_zero`: Graham–Lehrer
  Theorem 3.8.
* `TauCeti.CellularBasis.nonempty_splitWedderburnAlgebraPresentation`: every semisimple cellular
  `K`-algebra (with well-founded cell order) admits a `SplitWedderburnAlgebraPresentation K B`.

## References

* J. J. Graham and G. I. Lehrer, *Cellular algebras*, Invent. Math. 123 (1996), 1–34,
  Theorem 3.8.
-/

public section

open Module Submodule
open scoped Matrix

namespace TauCeti.CellularBasis

section CommRing

variable {R A Λ : Type*} [CommRing R] [Ring A] [Algebra R A] [Preorder Λ]
  {M : Λ → Type*} [∀ μ, Fintype (M μ)] [∀ μ, DecidableEq (M μ)]
  (c : CellularBasis R A M)

/-- The `R`-algebra homomorphism assembling all cell representations of `c` into a product of
matrix algebras indexed by the cells `μ : Λ`. -/
noncomputable def cellRepPiAlgHom : A →ₐ[R] ∀ μ : Λ, Matrix (M μ) (M μ) R :=
  AlgHom.pi c.cellRep

/-- Evaluating `cellRepPiAlgHom` at a cell `μ` gives `c.cellRep μ`. -/
@[simp]
theorem cellRepPiAlgHom_apply (a : A) (μ : Λ) :
    c.cellRepPiAlgHom a μ = c.cellRep μ a :=
  (rfl)

omit [∀ μ, DecidableEq (M μ)] in
/-- Decompose `x : A` along `c.basis` into its `μ`-cell part and the remaining support terms in
cells `ν ≠ μ`. -/
private theorem eq_sum_cell_add_sum_support_ne [DecidableEq Λ] (x : A) (μ : Λ) :
    x = (∑ s, ∑ t, c.basis.repr x ⟨μ, s, t⟩ • c.basis ⟨μ, s, t⟩) +
      ∑ j ∈ (c.basis.repr x).support with j.1 ≠ μ, c.basis.repr x j • c.basis j := by
  classical
  have hcell : ∑ s, ∑ t, c.basis.repr x ⟨μ, s, t⟩ • c.basis ⟨μ, s, t⟩ =
      ∑ j ∈ (c.basis.repr x).support with j.1 = μ, c.basis.repr x j • c.basis j := by
    let T : Finset (Σ ν, M ν × M ν) := Finset.univ.image (Sigma.mk μ)
    have himg : ∑ j ∈ T, c.basis.repr x j • c.basis j =
        ∑ p : M μ × M μ, c.basis.repr x ⟨μ, p⟩ • c.basis ⟨μ, p⟩ := by
      rw [Finset.sum_image (fun _ _ _ _ hp ↦ sigma_mk_injective hp)]
    rw [← Fintype.sum_prod_type (f := fun p : M μ × M μ ↦ c.basis.repr x ⟨μ, p⟩ • c.basis ⟨μ, p⟩),
      ← himg]
    symm
    refine Finset.sum_subset (fun j hj ↦ ?_) (fun j hj_img hj ↦ ?_)
    · obtain ⟨_, rfl⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_image_of_mem _ (Finset.mem_univ j.2)
    · rw [Finset.mem_filter, not_and_or, Finsupp.notMem_support_iff] at hj
      rcases hj with h0 | hne
      · rw [h0, zero_smul]
      · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hj_img
        exact (hne rfl).elim
  conv_lhs => rw [← c.basis.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [hcell, Finset.sum_filter_add_sum_filter_not]

/-- If `x : A` acts trivially on `c.CellModule μ` and has no nonzero cellular coordinate in any
cell strictly above `μ`, then for each row `s₀ : M μ` the vector
`∑ t, c.basis.repr x ⟨μ, s₀, t⟩ • c.cellBasis μ t` lies in `c.cellRadical μ`. -/
theorem sum_repr_cellBasis_mem_cellRadical {x : A} {μ : Λ} (hx0 : c.cellRep μ x = 0)
    (hmax : ∀ j ∈ (c.basis.repr x).support, ¬ μ < j.1) (s₀ : M μ) :
    ∑ t, c.basis.repr x ⟨μ, s₀, t⟩ • c.cellBasis μ t ∈ c.cellRadical μ := by
  classical
  rw [mem_cellRadical]
  intro w
  -- First, `x` annihilates `w` because `c.cellRep μ x = 0`.
  have hxw : x • w = 0 := by
    apply (c.cellModuleEquiv μ).injective
    rw [cellModuleEquiv_smul, hx0, Matrix.zero_mulVec, map_zero]
  -- Split `x` into its `μ`-cell part and support terms in cells `ν ≠ μ`; the latter annihilate `w`
  -- by `hmax` and `basis_smul_eq_zero_of_ne_of_not_lt`.
  have hrest :
      (∑ j ∈ (c.basis.repr x).support with j.1 ≠ μ, c.basis.repr x j • c.basis j) • w = 0 := by
    rw [Finset.sum_smul]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    obtain ⟨hj_supp, hne⟩ := Finset.mem_filter.mp hj
    rw [smul_assoc, c.basis_smul_eq_zero_of_ne_of_not_lt hne.symm (hmax j hj_supp), smul_zero]
  rw [c.eq_sum_cell_add_sum_support_ne x μ, add_smul, hrest, add_zero] at hxw
  -- Evaluate the `μ`-cell part on `w` via `basis_smul` and read off the `s₀`-coordinate.
  have hsum_eq : (∑ s, ∑ t, c.basis.repr x ⟨μ, s, t⟩ • c.basis ⟨μ, s, t⟩) • w =
      ∑ s, (∑ t, c.basis.repr x ⟨μ, s, t⟩ * c.cellForm μ (c.cellBasis μ t) w) •
        c.cellBasis μ s := by
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [Finset.sum_smul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [smul_assoc, c.basis_smul, smul_smul]
  rw [hsum_eq] at hxw
  have hcoord := congrFun (congrArg (fun v : c.CellModule μ ↦ ⇑((c.cellBasis μ).repr v)) hxw) s₀
  rw [(c.cellBasis μ).repr_sum_self, map_zero, Finsupp.coe_zero, Pi.zero_apply] at hcoord
  simpa [map_sum, map_smul, smul_eq_mul] using hcoord

/-- Over any commutative ring, if every cell radical vanishes, the product of cell representations
`c.cellRepPiAlgHom` is injective. -/
theorem cellRepPiAlgHom_injective (h : ∀ μ, c.cellRadical μ = ⊥) :
    Function.Injective c.cellRepPiAlgHom := by
  classical
  rw [injective_iff_map_eq_zero]
  intro x hx0
  by_contra hx
  have hrepr : c.basis.repr x ≠ 0 := mt (LinearEquiv.map_eq_zero_iff c.basis.repr).mp hx
  obtain ⟨⟨μ, s₀, t₀⟩, hmax⟩ :=
    (c.basis.repr x).support.exists_maximalFor Sigma.fst (Finsupp.support_nonempty_iff.mpr hrepr)
  have hi₀ : c.basis.repr x ⟨μ, s₀, t₀⟩ ≠ 0 := Finsupp.mem_support_iff.mp hmax.prop
  have hxμ : c.cellRep μ x = 0 := by
    rw [← cellRepPiAlgHom_apply, hx0, Pi.zero_apply]
  have hv_rad := c.sum_repr_cellBasis_mem_cellRadical hxμ (fun _ hj ↦ hmax.not_gt hj) s₀
  have hv0 : ∑ t, c.basis.repr x ⟨μ, s₀, t⟩ • c.cellBasis μ t = 0 :=
    (Submodule.eq_bot_iff _).mp (h μ) _ hv_rad
  have hcoord := congrFun (congrArg (fun v : c.CellModule μ ↦ ⇑((c.cellBasis μ).repr v)) hv0) t₀
  rw [(c.cellBasis μ).repr_sum_self, map_zero, Finsupp.coe_zero, Pi.zero_apply] at hcoord
  exact hi₀ hcoord

/-- Over any commutative ring, if every Gram determinant is a non-zero-divisor,
`c.cellRepPiAlgHom` is injective (with no finiteness hypothesis on `Λ`). -/
theorem cellRepPiAlgHom_injective_of_forall_det_gramMatrix_mem_nonZeroDivisors
    (h : ∀ μ, (c.gramMatrix μ).det ∈ nonZeroDivisors R) : Function.Injective c.cellRepPiAlgHom :=
  c.cellRepPiAlgHom_injective fun μ ↦
    c.cellRadical_eq_bot_of_det_gramMatrix_mem_nonZeroDivisors (h μ)

/-- When `(c.gramMatrix μ).det` is a unit, any matrix `N : Matrix (M μ) (M μ) R` is realized at
cell `μ` by an element `x : A` that annihilates all cells `τ ≠ μ` with `¬ τ < μ`. -/
private theorem exists_cellRep_eq_of_isUnit_det_gramMatrix {μ : Λ}
    (hμ : IsUnit (c.gramMatrix μ).det) (N : Matrix (M μ) (M μ) R) :
    ∃ x : A, c.cellRep μ x = N ∧ ∀ ⦃τ : Λ⦄, τ ≠ μ → ¬ τ < μ → c.cellRep τ x = 0 := by
  refine ⟨∑ w : M μ, ∑ t : M μ, (N * (c.gramMatrix μ)⁻¹) w t • c.basis ⟨μ, w, t⟩, ?_,
    fun τ hne hnlt ↦ ?_⟩
  · ext u s
    have hmul : (N * (c.gramMatrix μ)⁻¹ * c.gramMatrix μ) u s = N u s := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hμ, Matrix.mul_one]
    rw [← hmul, Matrix.mul_apply]
    simp [Matrix.sum_apply, Matrix.smul_apply, mul_ite, mul_zero]
  · simp [c.cellRep_basis_of_ne_of_not_lt hne hnlt]

/-- Over any commutative ring, when `Λ` is finite and every Gram determinant is a unit,
`c.cellRepPiAlgHom` is surjective. -/
theorem cellRepPiAlgHom_surjective_of_forall_isUnit_det_gramMatrix [Finite Λ]
    (h : ∀ μ, IsUnit (c.gramMatrix μ).det) : Function.Surjective c.cellRepPiAlgHom := by
  classical
  cases nonempty_fintype Λ
  have : WellFoundedLT Λ := Finite.to_wellFoundedLT
  have hsingle (μ : Λ) : ∀ N : Matrix (M μ) (M μ) R,
      Pi.single μ N ∈ c.cellRepPiAlgHom.range := by
    induction μ using WellFoundedLT.induction with
    | ind μ ih =>
      intro N
      obtain ⟨x, hx_diag, hx_other⟩ := c.exists_cellRep_eq_of_isUnit_det_gramMatrix (h μ) N
      have hdiff : c.cellRepPiAlgHom x - Pi.single μ N =
          ∑ ν ∈ Finset.univ.filter (· < μ), Pi.single ν (c.cellRep ν x) := by
        funext τ
        rw [Pi.sub_apply, cellRepPiAlgHom_apply, Finset.sum_apply]
        by_cases hτμ : τ = μ
        · subst hτμ
          rw [hx_diag, Pi.single_eq_same, sub_self]
          exact (Finset.sum_eq_zero fun ν hν ↦
            Pi.single_eq_of_ne (ne_of_gt (Finset.mem_filter.mp hν).2) _).symm
        · rw [Pi.single_eq_of_ne hτμ, sub_zero]
          by_cases hlt : τ < μ
          · rw [Finset.sum_eq_single τ
              (fun ν _ hν ↦ Pi.single_eq_of_ne (Ne.symm hν) _)
              (fun h ↦ (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)).elim),
              Pi.single_eq_same]
          · rw [hx_other hτμ hlt]
            exact (Finset.sum_eq_zero fun ν hν ↦
              Pi.single_eq_of_ne
                (fun hEq : τ = ν ↦ hlt (hEq ▸ (Finset.mem_filter.mp hν).2)) _).symm
      have hlow_mem : c.cellRepPiAlgHom x - Pi.single μ N ∈ c.cellRepPiAlgHom.range :=
        hdiff ▸ sum_mem fun ν hν ↦ ih ν (Finset.mem_filter.mp hν).2 _
      simpa using sub_mem (AlgHom.mem_range_self c.cellRepPiAlgHom x) hlow_mem
  intro F
  have hF : F = ∑ μ : Λ, Pi.single μ (F μ) := by
    funext μ
    rw [Finset.sum_apply,
      Fintype.sum_eq_single μ (fun ν hν ↦ Pi.single_eq_of_ne (Ne.symm hν) _), Pi.single_eq_same]
  exact hF ▸ sum_mem fun μ _ ↦ hsingle μ (F μ)

/-- Over any commutative ring, when `Λ` is finite and every Gram determinant is a unit,
`c.cellRepPiAlgHom` is bijective. -/
theorem cellRepPiAlgHom_bijective_of_forall_isUnit_det_gramMatrix [Finite Λ]
    (h : ∀ μ, IsUnit (c.gramMatrix μ).det) : Function.Bijective c.cellRepPiAlgHom :=
  ⟨c.cellRepPiAlgHom_injective_of_forall_det_gramMatrix_mem_nonZeroDivisors fun μ ↦
      (h μ).mem_nonZeroDivisors,
    c.cellRepPiAlgHom_surjective_of_forall_isUnit_det_gramMatrix h⟩

/-- **Ring-general split Wedderburn decomposition of a cellular algebra**: over any commutative
ring `R`, when `Λ` is finite and every Gram determinant is a unit in `R`, `c.cellRepPiAlgHom`
upgrades to an `R`-algebra isomorphism `A ≃ₐ[R] ∀ μ : Λ, Matrix (M μ) (M μ) R`. -/
noncomputable def cellRepPiAlgEquiv [Finite Λ] (h : ∀ μ, IsUnit (c.gramMatrix μ).det) :
    A ≃ₐ[R] ∀ μ : Λ, Matrix (M μ) (M μ) R :=
  AlgEquiv.ofBijective c.cellRepPiAlgHom
    (c.cellRepPiAlgHom_bijective_of_forall_isUnit_det_gramMatrix h)

/-- Evaluating `c.cellRepPiAlgEquiv h a` at `μ` yields `c.cellRep μ a`. -/
@[simp]
theorem cellRepPiAlgEquiv_apply [Finite Λ] (h : ∀ μ, IsUnit (c.gramMatrix μ).det) (a : A)
    (μ : Λ) : c.cellRepPiAlgEquiv h a μ = c.cellRep μ a :=
  (rfl)

/-- Coercing `cellRepPiAlgEquiv` to an algebra homomorphism recovers `c.cellRepPiAlgHom`. -/
@[simp, norm_cast]
theorem toAlgHom_cellRepPiAlgEquiv [Finite Λ] (h : ∀ μ, IsUnit (c.gramMatrix μ).det) :
    (c.cellRepPiAlgEquiv h : A →ₐ[R] ∀ μ : Λ, Matrix (M μ) (M μ) R) = c.cellRepPiAlgHom :=
  (rfl)

/-- `c.cellRepPiAlgHom` is a right inverse to `(c.cellRepPiAlgEquiv h).symm`. -/
@[simp]
theorem cellRepPiAlgHom_cellRepPiAlgEquiv_symm [Finite Λ] (h : ∀ μ, IsUnit (c.gramMatrix μ).det)
    (m : ∀ μ : Λ, Matrix (M μ) (M μ) R) :
    c.cellRepPiAlgHom ((c.cellRepPiAlgEquiv h).symm m) = m :=
  (c.cellRepPiAlgEquiv h).apply_symm_apply m

/-- The cell representation at `μ` of `(c.cellRepPiAlgEquiv h).symm m` is `m μ`. -/
@[simp]
theorem cellRep_cellRepPiAlgEquiv_symm [Finite Λ] (h : ∀ μ, IsUnit (c.gramMatrix μ).det)
    (m : ∀ μ : Λ, Matrix (M μ) (M μ) R) (μ : Λ) :
    c.cellRep μ ((c.cellRepPiAlgEquiv h).symm m) = m μ :=
  congrFun (c.cellRepPiAlgHom_cellRepPiAlgEquiv_symm h m) μ

/-- `(c.cellRepPiAlgEquiv h).symm` is a left inverse to `c.cellRepPiAlgHom`. -/
@[simp]
theorem cellRepPiAlgEquiv_symm_cellRepPiAlgHom [Finite Λ] (h : ∀ μ, IsUnit (c.gramMatrix μ).det)
    (a : A) : (c.cellRepPiAlgEquiv h).symm (c.cellRepPiAlgHom a) = a :=
  (c.cellRepPiAlgEquiv h).symm_apply_apply a

/-- Over a commutative semisimple base ring `R`, if `Λ` is finite and every Gram determinant is a
unit, then `A` is a semisimple ring. -/
theorem isSemisimpleRing_of_forall_isUnit_det_gramMatrix [IsSemisimpleRing R] [Finite Λ]
    (h : ∀ μ, IsUnit (c.gramMatrix μ).det) : IsSemisimpleRing A :=
  (c.cellRepPiAlgEquiv h).toRingEquiv.symm.isSemisimpleRing

/-- When `c.gramMatrix μ = 0`, the `R`-span of cellular basis vectors in cells `ν < μ` or `ν = μ`
is a left ideal `I` of `A` containing every `c.basis ⟨μ, s, t⟩` whose products land inside
`c.lowerSpan μ`. -/
private theorem exists_ideal_basis_mem_and_mul_mem_lowerSpan {μ : Λ}
    (hgram : c.gramMatrix μ = 0) :
    ∃ I : Ideal A, (∀ s t : M μ, c.basis ⟨μ, s, t⟩ ∈ I) ∧
      ∀ x ∈ I, ∀ y ∈ I, x * y ∈ c.lowerSpan μ := by
  let L : Submodule R A := span R (c.basis '' {i | i.1 < μ ∨ i.1 = μ})
  have hlow_le : c.lowerSpan μ ≤ L := by
    rw [lowerSpan_def]
    exact span_mono (Set.image_mono fun _ hi ↦ Or.inl hi)
  have hbasis_le (s t : M μ) : c.basis ⟨μ, s, t⟩ ∈ L :=
    subset_span ⟨⟨μ, s, t⟩, Or.inr rfl, rfl⟩
  have hmul_L (a : A) {x : A} (hx : x ∈ L) : a * x ∈ L := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨ν, s, t⟩, hν | hν, rfl⟩ := hy
      · exact hlow_le (c.mul_mem_lowerSpan a (c.basis_mem_lowerSpan hν s t))
      · dsimp only at hν; subst ν
        have hsub := hlow_le (c.mul_basis_sub_sum_mem a μ s t)
        have hsum : ∑ u, c.cellRep μ a u s • c.basis ⟨μ, u, t⟩ ∈ L :=
          sum_mem fun u _ ↦ L.smul_mem _ (hbasis_le u t)
        simpa using L.add_mem hsub hsum
    | zero => simp
    | add x y _ _ ihx ihy => rw [mul_add]; exact L.add_mem ihx ihy
    | smul r x _ ih => rw [mul_smul_comm]; exact L.smul_mem r ih
  have hprod_low {x y : A} (hx : x ∈ L) (hy : y ∈ L) : x * y ∈ c.lowerSpan μ := by
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨ν, s, t⟩, hν | hν, rfl⟩ := hz
      · exact c.mem_lowerSpan_mul y (c.basis_mem_lowerSpan hν s t)
      · dsimp only at hν; subst ν
        induction hy using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨⟨ξ, u, v⟩, hξ | hξ, rfl⟩ := hw
          · exact c.mul_mem_lowerSpan _ (c.basis_mem_lowerSpan hξ u v)
          · dsimp only at hξ; subst ξ
            simpa [hgram] using c.basis_mul_basis_sub_mem μ s t u v
        | zero => simp
        | add w₁ w₂ _ _ ih₁ ih₂ => rw [mul_add]; exact add_mem ih₁ ih₂
        | smul r w _ ih => rw [mul_smul_comm]; exact smul_mem _ r ih
    | zero => simp
    | add z₁ z₂ _ _ ih₁ ih₂ => rw [add_mul]; exact add_mem ih₁ ih₂
    | smul r z _ ih => rw [smul_mul_assoc]; exact smul_mem _ r ih
  exact ⟨{ carrier := L, add_mem' := L.add_mem, zero_mem' := L.zero_mem,
           smul_mem' := fun a {_} hx ↦ hmul_L a hx },
    hbasis_le, fun _ hx _ hy ↦ hprod_low hx hy⟩

/-- Over a nontrivial coefficient ring `R`, if `A` is a semisimple ring, every cell `μ` with
nonempty index set `M μ` has nonzero bilinear form `c.cellForm μ ≠ 0`. -/
theorem cellForm_ne_zero_of_isSemisimpleRing [Nontrivial R] [IsSemisimpleRing A] (μ : Λ)
    [Nonempty (M μ)] : c.cellForm μ ≠ 0 := by
  intro hform
  obtain ⟨I, hbasis_I, hprod_low⟩ :=
    c.exists_ideal_basis_mem_and_mul_mem_lowerSpan ((c.cellForm_eq_zero_iff μ).mp hform)
  obtain ⟨e, he_idem, he_span⟩ := IsSemisimpleRing.ideal_eq_span_idempotent I
  have he_I : e ∈ I := he_span ▸ Ideal.subset_span (Set.mem_singleton e)
  have he_low : e ∈ c.lowerSpan μ := he_idem.eq ▸ hprod_low e he_I e he_I
  obtain ⟨s₀⟩ := ‹Nonempty (M μ)›
  have hb_I : c.basis ⟨μ, s₀, s₀⟩ ∈ I := hbasis_I s₀ s₀
  rw [he_span, Ideal.mem_span_singleton'] at hb_I
  obtain ⟨a, ha⟩ := hb_I
  have hb_low : c.basis ⟨μ, s₀, s₀⟩ ∈ c.lowerSpan μ := ha ▸ c.mul_mem_lowerSpan a he_low
  have h0 := c.mem_lowerSpan_iff.mp hb_low ⟨μ, s₀, s₀⟩ (lt_irrefl μ)
  simp at h0

end CommRing

section Field

variable {K B Λ : Type*} [Field K] [Ring B] [Algebra K B] [Preorder Λ]
  {M : Λ → Type*} [∀ μ, Fintype (M μ)] [∀ μ, DecidableEq (M μ)]
  (d : CellularBasis K B M)

/-- Over a field `K`, if `B` is semisimple, every cell radical `d.cellRadical μ` is trivial. -/
theorem cellRadical_eq_bot_of_isSemisimpleRing [IsSemisimpleRing B] (μ : Λ) :
    d.cellRadical μ = ⊥ := by
  rcases isEmpty_or_nonempty (M μ) with hEmpty | hNonempty
  · rw [Submodule.eq_bot_iff]
    intro x _
    apply (d.cellModuleEquiv μ).injective
    ext s
    exact hEmpty.elim s
  · obtain ⟨C, hC⟩ := exists_isCompl (d.cellRadical μ)
    have hC_top : C = ⊤ := by
      by_contra hne
      have htop : d.cellRadical μ = ⊤ :=
        (sup_eq_left.mpr (d.le_cellRadical_of_ne_top μ C hne)).symm.trans hC.sup_eq_top
      exact d.cellForm_ne_zero_of_isSemisimpleRing μ ((d.cellRadical_eq_top_iff μ).mp htop)
    simpa [hC_top] using hC.inf_eq_bot

/-- Over a field `K`, if `B` is semisimple, every cell bilinear form is nondegenerate. -/
theorem nondegenerate_cellForm_of_isSemisimpleRing [IsSemisimpleRing B] (μ : Λ) :
    (d.cellForm μ).Nondegenerate :=
  (d.nondegenerate_cellForm_iff_cellRadical_eq_bot μ).mpr
    (d.cellRadical_eq_bot_of_isSemisimpleRing μ)

/-- Over a field `K`, if `B` is semisimple, every Gram determinant `(d.gramMatrix μ).det` is
nonzero. -/
theorem det_gramMatrix_ne_zero_of_isSemisimpleRing [IsSemisimpleRing B] (μ : Λ) :
    (d.gramMatrix μ).det ≠ 0 :=
  (d.cellRadical_eq_bot_iff_det_gramMatrix_ne_zero μ).mp
    (d.cellRadical_eq_bot_of_isSemisimpleRing μ)

/-- Over a field `K`, if `B` is semisimple, every nonempty cell module `d.CellModule μ` is
simple. -/
theorem isSimpleModule_cellModule_of_isSemisimpleRing [IsSemisimpleRing B] (μ : Λ)
    [Nonempty (M μ)] : IsSimpleModule B (d.CellModule μ) :=
  d.isSimpleModule_cellModule_of_cellRadical_eq_bot (d.cellRadical_eq_bot_of_isSemisimpleRing μ)

/-- Over a field `K`, if `B` is semisimple, a cell module `d.CellModule μ` is simple if and only if
its index set `M μ` is nonempty. -/
theorem isSimpleModule_cellModule_iff_nonempty_of_isSemisimpleRing [IsSemisimpleRing B] (μ : Λ) :
    IsSimpleModule B (d.CellModule μ) ↔ Nonempty (M μ) := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ d.isSimpleModule_cellModule_of_isSemisimpleRing μ⟩
  obtain ⟨x, y, hxy⟩ := IsSimpleModule.nontrivial B (d.CellModule μ)
  by_contra h
  exact hxy ((d.cellModuleEquiv μ).injective (funext fun s ↦ (h ⟨s⟩).elim))

/-- Over a field `K`, if `B` is semisimple and `M μ` is nonempty, `d.CellModule μ` is `B`-linearly
equivalent to `d.CellModule ν` if and only if `μ = ν`. -/
theorem nonempty_cellModule_linearEquiv_iff_of_isSemisimpleRing [IsSemisimpleRing B] {μ ν : Λ}
    [Nonempty (M μ)] : Nonempty (d.CellModule μ ≃ₗ[B] d.CellModule ν) ↔ μ = ν := by
  have eμ := (d.cellRadical μ).quotEquivOfEqBot (d.cellRadical_eq_bot_of_isSemisimpleRing μ)
  have eν := (d.cellRadical ν).quotEquivOfEqBot (d.cellRadical_eq_bot_of_isSemisimpleRing ν)
  refine ⟨fun ⟨e⟩ ↦ (d.nonempty_cellModule_quotient_linearEquiv_iff
    (d.cellForm_ne_zero_of_isSemisimpleRing μ)).mp ⟨eμ.trans (e.trans eν.symm)⟩, ?_⟩
  rintro rfl
  exact ⟨LinearEquiv.refl B _⟩

section Finite

variable [Finite Λ]

/-- **Graham–Lehrer Theorem 3.8 (radical form).** Over a field `K` with finitely many cells, `B` is
a semisimple ring if and only if every cell radical `d.cellRadical μ` is trivial. -/
theorem isSemisimpleRing_iff_forall_cellRadical_eq_bot :
    IsSemisimpleRing B ↔ ∀ μ, d.cellRadical μ = ⊥ :=
  ⟨fun _ ↦ d.cellRadical_eq_bot_of_isSemisimpleRing,
    fun h ↦ d.isSemisimpleRing_of_forall_isUnit_det_gramMatrix fun μ ↦
      isUnit_iff_ne_zero.mpr ((d.cellRadical_eq_bot_iff_det_gramMatrix_ne_zero μ).mp (h μ))⟩

/-- **Graham–Lehrer Theorem 3.8 (bilinear-form criterion).** Over a field `K` with finitely many
cells, `B` is semisimple if and only if every cell bilinear form `d.cellForm μ` is nondegenerate. -/
theorem isSemisimpleRing_iff_forall_nondegenerate_cellForm :
    IsSemisimpleRing B ↔ ∀ μ, (d.cellForm μ).Nondegenerate := by
  simp_rw [d.isSemisimpleRing_iff_forall_cellRadical_eq_bot,
    d.nondegenerate_cellForm_iff_cellRadical_eq_bot]

/-- **Graham–Lehrer Theorem 3.8 (Gram-determinant criterion).** Over a field `K` with finitely many
cells, `B` is semisimple if and only if `(d.gramMatrix μ).det ≠ 0` for every cell `μ`. -/
theorem isSemisimpleRing_iff_forall_det_gramMatrix_ne_zero :
    IsSemisimpleRing B ↔ ∀ μ, (d.gramMatrix μ).det ≠ 0 := by
  simp_rw [d.isSemisimpleRing_iff_forall_cellRadical_eq_bot,
    d.cellRadical_eq_bot_iff_det_gramMatrix_ne_zero]

/-- Over a field `K` with finitely many cells, `d.cellRepPiAlgHom` is bijective if and only if `B`
is semisimple. -/
theorem cellRepPiAlgHom_bijective_iff_isSemisimpleRing :
    Function.Bijective d.cellRepPiAlgHom ↔ IsSemisimpleRing B :=
  ⟨fun hbij ↦ (AlgEquiv.ofBijective d.cellRepPiAlgHom hbij).symm.toRingEquiv.isSemisimpleRing,
    fun _ ↦ d.cellRepPiAlgHom_bijective_of_forall_isUnit_det_gramMatrix fun μ ↦
      isUnit_iff_ne_zero.mpr (d.det_gramMatrix_ne_zero_of_isSemisimpleRing μ)⟩

end Finite

/-- Over a field `K` with well-founded cell order, when `B` is semisimple every simple `B`-module is
`B`-linearly equivalent to `d.CellModule μ` for a unique nonempty cell `μ`. -/
theorem existsUnique_nonempty_and_nonempty_linearEquiv_of_isSemisimpleRing
    [WellFoundedLT Λ] [IsSemisimpleRing B] (S : Type*) [AddCommGroup S] [Module B S]
    [IsSimpleModule B S] :
    ∃! μ : Λ, Nonempty (M μ) ∧ Nonempty (d.CellModule μ ≃ₗ[B] S) := by
  obtain ⟨μ, ⟨hμ, ⟨e⟩⟩, huniq⟩ := d.existsUnique_cellForm_ne_zero_and_nonempty_linearEquiv S
  obtain ⟨s, -, -⟩ := d.exists_gramMatrix_ne_zero hμ
  have eμ := (d.cellRadical μ).quotEquivOfEqBot (d.cellRadical_eq_bot_of_isSemisimpleRing μ)
  refine ⟨μ, ⟨⟨s⟩, ⟨eμ.symm.trans e⟩⟩, fun ν ⟨hneν, ⟨e'⟩⟩ ↦ huniq ν ⟨?_, ⟨?_⟩⟩⟩
  · exact d.cellForm_ne_zero_of_isSemisimpleRing ν
  · exact ((d.cellRadical ν).quotEquivOfEqBot
      (d.cellRadical_eq_bot_of_isSemisimpleRing ν)).trans e'

omit [∀ μ, DecidableEq (M μ)] in
/-- Every semisimple cellular `K`-algebra with well-founded cell order (in particular, with
finitely many cells) is split over `K`, admitting a `SplitWedderburnAlgebraPresentation K B` with no
algebraic-closure assumption on `K`. -/
theorem nonempty_splitWedderburnAlgebraPresentation [WellFoundedLT Λ] [IsSemisimpleRing B]
    (d : CellularBasis K B M) :
    Nonempty (SplitWedderburnAlgebraPresentation K B) :=
  IsSemisimpleRing.nonempty_splitWedderburnAlgebraPresentation_of_finrank_end_eq_one K B
    fun S _ ↦ d.finrank_end_eq_one_of_isSimpleModule S

end Field

/-- **Sharpness of the field hypothesis in Theorem 3.8.** Over `ℤ`, there exists a cellular algebra
(`Matrix Unit Unit ℤ` with `CellularBasis.matrix ℤ Unit`, isomorphic as a ring to `ℤ`) whose cell
form is nondegenerate, yet which is not a semisimple ring. -/
theorem exists_cellularBasis_int_nondegenerate_and_not_isSemisimpleRing :
    ∃ (A : Type) (_ : Ring A) (_ : Algebra ℤ A) (c : CellularBasis ℤ A (fun _ : Unit ↦ Unit)),
      (∀ μ, (c.cellForm μ).Nondegenerate) ∧ ¬ IsSemisimpleRing A := by
  refine ⟨Matrix Unit Unit ℤ, inferInstance, inferInstance, CellularBasis.matrix ℤ Unit,
    fun ⟨⟩ ↦ nondegenerate_cellForm_matrix, fun hss ↦ ?_⟩
  have : IsSemisimpleRing ℤ := (Matrix.uniqueRingEquiv (m := Unit) (A := ℤ)).isSemisimpleRing
  have hunit : IsUnit (2 : ℤ) :=
    IsArtinianRing.isUnit_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero two_ne_zero)
  rcases Int.isUnit_iff.mp hunit with h | h <;> omega

end TauCeti.CellularBasis

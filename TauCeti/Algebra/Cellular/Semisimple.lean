/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import TauCeti.Algebra.Cellular.Simple
public import TauCeti.RingTheory.Semisimple.Wedderburn.Presentation
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.Order.Preorder.Finite
import TauCeti.RingTheory.Semisimple.Wedderburn.Split

/-!
# Semisimplicity and Wedderburn decomposition of cellular algebras

This file formalizes Graham and Lehrer's semisimplicity criterion for cellular algebras over a
field and their canonical split Artin–Wedderburn decomposition into matrix algebras indexed by the
cells.

Over an arbitrary commutative ring `R`, the cell representations `c.cellRep μ` assemble into an
`R`-algebra homomorphism

`c.cellRepPiAlgHom : A →ₐ[R] ∀ μ : Λ, Matrix (M μ) (M μ) R`.

Because `c.cellForm μ` is symmetric, its nondegeneracy (`LinearMap.BilinForm.Nondegenerate`) is
equivalent to triviality of `c.cellRadical μ` over any commutative ring, and further equivalent to
`(c.gramMatrix μ).det ≠ 0` when `R` is an integral domain. Whenever every cell radical vanishes,
`c.cellRepPiAlgHom` is injective (`TauCeti.CellularBasis.cellRepPiAlgHom_injective`), without any
finiteness hypothesis on `Λ`. Conversely, when `A` is semisimple and `R` is nontrivial, every
nonempty cell has nonzero bilinear form
(`TauCeti.CellularBasis.cellForm_ne_zero_of_isSemisimpleRing`).

Over a field `K` with a finite preorder `Λ` of cells, dimension counting upgrades injectivity of
`d.cellRepPiAlgHom` to an explicit `K`-algebra isomorphism
(`TauCeti.CellularBasis.wedderburnAlgEquiv`)

`B ≃ₐ[K] ∀ μ : Λ, Matrix (M μ) (M μ) K`,

yielding **Graham–Lehrer Theorem 3.8**: the following are equivalent:
1. `B` is a semisimple ring (`IsSemisimpleRing B`);
2. every cell radical is trivial (`∀ μ, d.cellRadical μ = ⊥`);
3. every cell bilinear form is nondegenerate (`∀ μ, (d.cellForm μ).Nondegenerate`);
4. every Gram determinant is nonzero (`∀ μ, (d.gramMatrix μ).det ≠ 0`);
5. `d.cellRepPiAlgHom` is bijective.

Moreover, any semisimple cellular `K`-algebra with well-founded cell order is automatically split
over `K` (`TauCeti.CellularBasis.nonempty_splitWedderburnAlgebraPresentation`), with no
algebraic-closure assumption on `K`.

The field hypothesis in Theorem 3.8 is sharp: `Matrix Unit Unit ℤ` (isomorphic to `ℤ`) has one cell
with nondegenerate bilinear form and Gram determinant `1`, yet is not a semisimple ring
(`TauCeti.CellularBasis.exists_cellularBasis_int_nondegenerate_and_not_isSemisimpleRing`).

## Main definitions

* `TauCeti.CellularBasis.cellRepPiAlgHom`: the product of all cell representations
  `A →ₐ[R] ∀ μ : Λ, Matrix (M μ) (M μ) R`.
* `TauCeti.CellularBasis.wedderburnAlgEquiv`: the `K`-algebra isomorphism
  `B ≃ₐ[K] ∀ μ : Λ, Matrix (M μ) (M μ) K` when `∀ μ, d.cellRadical μ = ⊥` and `[Finite Λ]`.

## Main results

* `TauCeti.CellularBasis.cellRepPiAlgHom_injective`: `c.cellRepPiAlgHom` is injective whenever
  `∀ μ, c.cellRadical μ = ⊥`.
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
/-- Coordinates of a linear combination of standard cell basis vectors. -/
private theorem cellModuleEquiv_sum_smul_cellBasis (μ : Λ) (r : M μ → R) (u : M μ) :
    c.cellModuleEquiv μ (∑ s, r s • c.cellBasis μ s) u = r u := by
  classical
  simp [Pi.single_apply]

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
  -- by `hmax` and `basis_smul_eq_zero_of_ne`.
  have hrest :
      (∑ j ∈ (c.basis.repr x).support with j.1 ≠ μ, c.basis.repr x j • c.basis j) • w = 0 := by
    rw [Finset.sum_smul]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    obtain ⟨hj_supp, hne⟩ := Finset.mem_filter.mp hj
    rw [smul_assoc, c.basis_smul_eq_zero_of_ne hne (hmax j hj_supp), smul_zero]
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
  have hcoord : ∑ t, c.basis.repr x ⟨μ, s₀, t⟩ * c.cellForm μ (c.cellBasis μ t) w = 0 := by
    simpa [cellModuleEquiv_sum_smul_cellBasis] using
      congrFun (congrArg (c.cellModuleEquiv μ) hxw) s₀
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
  have hcoord := congrFun (congrArg (c.cellModuleEquiv μ) hv0) t₀
  exact hi₀ (by simpa [cellModuleEquiv_sum_smul_cellBasis] using hcoord)

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

section Finite

variable [Finite Λ]

/-- Over a field `K` with a finite preorder `Λ` of cells, if every cell radical vanishes,
`d.cellRepPiAlgHom` is bijective. -/
theorem cellRepPiAlgHom_bijective_of_forall_cellRadical_eq_bot (h : ∀ μ, d.cellRadical μ = ⊥) :
    Function.Bijective d.cellRepPiAlgHom := by
  have hinj : Function.Injective d.cellRepPiAlgHom := d.cellRepPiAlgHom_injective h
  cases nonempty_fintype Λ
  have : FiniteDimensional K B := Module.Finite.of_basis d.basis
  have hdim : Module.finrank K B = Module.finrank K (∀ μ : Λ, Matrix (M μ) (M μ) K) := by
    rw [Module.finrank_eq_card_basis d.basis, Fintype.card_sigma, Module.finrank_pi_fintype K]
    refine Finset.sum_congr rfl fun μ _ ↦ ?_
    rw [Fintype.card_prod, Module.finrank_matrix, Module.finrank_self, mul_one]
  exact ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := d.cellRepPiAlgHom.toLinearMap)
      hdim).mp hinj⟩

/-- The canonical split Artin–Wedderburn `K`-algebra isomorphism
`B ≃ₐ[K] ∀ μ : Λ, Matrix (M μ) (M μ) K` induced by the cell representations when every cell radical
vanishes. -/
noncomputable def wedderburnAlgEquiv (h : ∀ μ, d.cellRadical μ = ⊥) :
    B ≃ₐ[K] ∀ μ : Λ, Matrix (M μ) (M μ) K :=
  AlgEquiv.ofBijective d.cellRepPiAlgHom
    (d.cellRepPiAlgHom_bijective_of_forall_cellRadical_eq_bot h)

/-- `wedderburnAlgEquiv` evaluates at each cell `μ` to `d.cellRep μ`. -/
@[simp]
theorem wedderburnAlgEquiv_apply (h : ∀ μ, d.cellRadical μ = ⊥) (b : B) (μ : Λ) :
    d.wedderburnAlgEquiv h b μ = d.cellRep μ b :=
  (rfl)

/-- **Graham–Lehrer Theorem 3.8 (radical form).** Over a field `K` with finitely many cells, `B` is
a semisimple ring if and only if every cell radical `d.cellRadical μ` is trivial. -/
theorem isSemisimpleRing_iff_forall_cellRadical_eq_bot :
    IsSemisimpleRing B ↔ ∀ μ, d.cellRadical μ = ⊥ :=
  ⟨fun _ ↦ d.cellRadical_eq_bot_of_isSemisimpleRing,
    fun h ↦ (d.wedderburnAlgEquiv h).symm.toRingEquiv.isSemisimpleRing⟩

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
    fun _ ↦ d.cellRepPiAlgHom_bijective_of_forall_cellRadical_eq_bot
      d.cellRadical_eq_bot_of_isSemisimpleRing⟩

end Finite

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

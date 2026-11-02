/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Submanifold.Polynomial
public import TauCeti.Geometry.RealAlgebraic.Projection.McCallum.Basic
public import TauCeti.Geometry.RealAlgebraic.Projection.McCallum.FamilyOrder
public import TauCeti.Geometry.RealAlgebraic.Stack.Chart
public import TauCeti.Geometry.RealAlgebraic.Stack.Discriminant.Global
public import TauCeti.Geometry.RealAlgebraic.Stack.Sectors

/-!
# McCallum lifting over an order-invariant base

A squarefree polynomial basis, in particular an irreducible basis, is analytically delineable
over a connected analytic submanifold when none of its fibers is nullified and the McCallum
projection is order-invariant there. Every input polynomial reconstructed from the basis then
has constant ambient order, and hence constant sign, on every section and sector of the
resulting stack.

This is the non-nullified lifting step of McCallum's projection-correctness argument, used at
each positive-dimensional cell whose base is already order-invariant for the projection.
Nullified fibers over zero-dimensional cells are not covered; they require refinement by
delineating polynomials.

## References

S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
Springer (1998), Sections 2–3.
-/

public section

open Filter Metric MvPolynomial Polynomial Set Topology

namespace TauCeti

variable {n d : ℕ} [NormalizedGCDMonoid (MvPolynomial (Fin n) ℝ)]
  {F B : Finset (Polynomial (MvPolynomial (Fin n) ℝ))} {S : Set (Fin n → ℝ)}

/-- Any nonnullified subfamily of a squarefree basis has a common delineation over a
preconnected analytic submanifold on which the original McCallum projection is
order-invariant. The product of the subfamily has constant ambient order along each section.
Nullified members outside the subfamily cause no obstruction. -/
theorem exists_delineation_orderAt_prod_eq_of_mcCallumProjection
    (hB : F.IsSquarefreeBasis B) {A : Finset (Polynomial (MvPolynomial (Fin n) ℝ))}
    (hAB : A ⊆ B) (hS : IsAnalyticSubmanifold d S) (hconn : IsPreconnected S)
    (hfiber : ∀ b ∈ A, ∀ x ∈ S, b.map (MvPolynomial.eval x) ≠ 0)
    (hproj : ∀ q ∈ F.mcCallumProjection B, ∀ x ∈ S, ∀ y ∈ S,
      q.orderAt x = q.orderAt y) :
    ∃ D : Delineation fun (b : A) (x : S) ↦ b.1.map (MvPolynomial.eval x.1),
      ∀ i, ∀ x y : S,
        ((finSuccEquiv ℝ n).symm (∏ b : A, b.1)).orderAt (Fin.cons (D.root i x) x.1) =
          ((finSuccEquiv ℝ n).symm (∏ b : A, b.1)).orderAt (Fin.cons (D.root i y) y.1) := by
  classical
  have hdegree (b : A) (x : Fin n → ℝ) (hx : x ∈ S) (y : Fin n → ℝ) (hy : y ∈ S) :
      (b.1.map (MvPolynomial.eval x)).natDegree =
        (b.1.map (MvPolynomial.eval y)).natDegree :=
    Finset.natDegree_map_eq_of_mcCallumProjection
      (fun q hq ↦ eval_eq_zero_iff_of_orderAt_eq (hproj q hq x hx y hy)) (hAB b.2)
  let p : Polynomial (MvPolynomial (Fin n) ℝ) := ∏ b : A, b.1
  have hp_eq : p = ∏ b ∈ A, b := Finset.prod_coe_sort A fun b ↦ b
  have hp_discr_ne : p.discr ≠ 0 := by
    rw [hp_eq]
    exact hB.discr_prod_ne_zero hAB
  have hp_discr (x : Fin n → ℝ) (hx : x ∈ S) (y : Fin n → ℝ) (hy : y ∈ S) :
      p.discr.orderAt x = p.discr.orderAt y := by
    rw [hp_eq]
    exact hB.orderAt_discr_prod_eq_of_mcCallumProjection hAB x y
      (fun q hq ↦ hproj q hq x hx y hy)
  apply exists_delineation_of_locally_chart
    (d := d) (P := fun (b : A) x ↦ b.1.map (MvPolynomial.eval x))
    (q := fun x t ↦ ((finSuccEquiv ℝ n).symm p).orderAt (Fin.cons t x)) hconn
  intro x hx
  obtain ⟨e, hxe, he⟩ := hS.exists_isAnalyticChart x hx
  exact ⟨e, he, hxe, he.exists_delineation_orderAt_prod_eq (P := fun b : A ↦ b.1) hxe hx
    (fun b ↦ hfiber b b.2) hdegree hp_discr_ne hp_discr⟩

end TauCeti

namespace Finset.IsSquarefreeBasis

variable {n d : ℕ} [NormalizedGCDMonoid (MvPolynomial (Fin n) ℝ)]
  {F B : Finset (Polynomial (MvPolynomial (Fin n) ℝ))}
  {S : Set (Fin n → ℝ)}

/-- **McCallum lifting over an order-invariant base.** If a squarefree basis has no
nullified fiber over a connected analytic submanifold and every member of its McCallum
projection has constant ambient order there, then the basis has a common delineation.
Every stack cell is an analytic submanifold, and every original input has constant ambient
order and sign on that cell. -/
theorem exists_delineation_orderAt_eq_of_mcCallumProjection
    (hB : F.IsSquarefreeBasis B) (hS : TauCeti.IsAnalyticSubmanifold d S)
    (hconn : IsPreconnected S)
    (hfiber : ∀ b ∈ B, ∀ x ∈ S, b.map (MvPolynomial.eval x) ≠ 0)
    (hproj : ∀ q ∈ F.mcCallumProjection B, ∀ x ∈ S, ∀ y ∈ S,
      q.orderAt x = q.orderAt y) :
    ∃ D : TauCeti.Delineation fun (b : B) (x : S) ↦ b.1.map (MvPolynomial.eval x.1),
      ∀ E ∈ TauCeti.stackCells S D.root,
        (∃ e, (e = d ∨ e = d + 1) ∧ TauCeti.IsAnalyticSubmanifold e E) ∧
        ∀ f ∈ F,
          (∀ y ∈ E, ∀ y' ∈ E, ((finSuccEquiv ℝ n).symm f).orderAt y =
            ((finSuccEquiv ℝ n).symm f).orderAt y') ∧
          TauCeti.SignInvariant
            (fun y ↦ MvPolynomial.eval y ((finSuccEquiv ℝ n).symm f)) E := by
  classical
  obtain ⟨D, hprod⟩ := TauCeti.exists_delineation_orderAt_prod_eq_of_mcCallumProjection
    hB Subset.rfl hS hconn hfiber hproj
  let p : Polynomial (MvPolynomial (Fin n) ℝ) := ∏ b : B, b.1
  have hp_eq : p = ∏ b ∈ B, b := Finset.prod_coe_sort B fun b ↦ b
  have hcontent (f : Polynomial (MvPolynomial (Fin n) ℝ)) (hf : f ∈ F)
      (x : Fin n → ℝ) (hx : x ∈ S) (y : Fin n → ℝ) (hy : y ∈ S) :
      f.content.orderAt x = f.content.orderAt y :=
    hproj f.content (content_mem_mcCallumProjection hf) x hx y hy
  refine ⟨D, fun E hE ↦ ⟨D.exists_isAnalyticSubmanifold_of_mem_stackCells hS
    (fun (b : B) j ↦ hS.analyticOnSubmanifold_coeff_map_eval b.1 j) hE, ?_⟩⟩
  have hp_mv_eq : (finSuccEquiv ℝ n).symm p =
      ∏ b ∈ B, (finSuccEquiv ℝ n).symm b := by
    rw [hp_eq, map_prod]
  exact hB.orderAt_eq_of_prod_delineation hconn D hfiber hcontent
    (by
      rw [← hp_mv_eq]
      intro i a ha a' ha'
      obtain ⟨haS, hai⟩ := TauCeti.mem_image_cylinder.mp ha
      obtain ⟨haS', hai'⟩ := TauCeti.mem_image_cylinder.mp ha'
      simp only [TauCeti.mem_sectionSet] at hai hai'
      have h := hprod i ⟨Fin.tail a, haS⟩ ⟨Fin.tail a', haS'⟩
      rw [hai, hai', Fin.cons_self_tail, Fin.cons_self_tail] at h
      exact h) E hE

end Finset.IsSquarefreeBasis

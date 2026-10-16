/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Lazard.Basic
import TauCeti.Topology.Algebra.MvPolynomial.Lazard

/-!
# Recovering a Lazard delineation from a product

A Lazard delineation of a nonzero finite product over a preconnected base induces a Lazard
delineation of its factors with exactly the same ordered root functions. No preservation of
ordinary fiber degrees or nonnullification is needed. Factors may share roots and have
repeated roots; the empty family is included.

Constant product valuation passes to each divisor along continuous sections. On each product
root section this fixes the factor's root multiplicity. On a continuous graph in a sector it
fixes the factor's removed base exponents. Multiplicativity of Lazard evaluation supplies root
coverage and ensures that each section is used by a factor.

This is the product-to-family step in Lazard lifting: a single-polynomial delineability theorem
applied to a basis product provides the common stack for the basis, even over nullified ordinary
fibers. Its section and sector valuations follow from the existing `LazardDelineation` API.

## Main declarations

* `TauCeti.LazardDelineation.ofProd`: recover the factors' common Lazard delineation.
* `TauCeti.LazardDelineation.ofProd_count`, `TauCeti.LazardDelineation.ofProd_root`:
  the number and ordered list of root sections are preserved.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), Proposition 3.4 and Section 5.3.
-/

public section

open MvPolynomial Set

namespace TauCeti.LazardDelineation

variable {ι : Type*} [Fintype ι] {n : ℕ}
  {F : ι → MvPolynomial (Fin (n + 1)) ℝ} {S : Set (Fin n → ℝ)}
  (D : LazardDelineation (fun _ : Unit ↦ ∏ k, F k) S)

/-- Recover a common Lazard delineation of the factors from a delineation of their nonzero
product over a preconnected base. The root list is unchanged. Ordinary fibers may be nullified,
and neither their degrees nor the degrees of Lazard evaluations need to be constant. -/
noncomputable def ofProd (hS : IsPreconnected S) (hprod : ∏ k, F k ≠ 0) :
    LazardDelineation F S := by
  classical
  have : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.1 hS
  let x₀ : S := ⟨D.nonempty.some, D.nonempty.some_mem⟩
  let g (f : MvPolynomial (Fin (n + 1)) ℝ) :=
    optionEquivRight ℝ (Fin n) (rename finSuccEquivLast f)
  have hn (k : ι) : F k ≠ 0 := Finset.prod_ne_zero_iff.1 hprod k (Finset.mem_univ k)
  have hgn (k : ι) : g (F k) ≠ 0 :=
    (map_ne_zero_iff _ (optionEquivRight ℝ (Fin n)).injective).2
      ((map_ne_zero_iff _ (rename_injective _ finSuccEquivLast.injective)).2 (hn k))
  have heval (x : S) :
      (g (∏ k, F k)).lazardEval (Polynomial.C ∘ x.1) =
        ∏ k, (g (F k)).lazardEval (Polynomial.C ∘ x.1) := by
    simp only [g, map_prod, ← lazardEvalHom_apply]
  -- Product valuation constancy on any continuous graph passes to every factor.
  have hfactor (r : S → ℝ) (hr : Continuous r)
      (hv : ∀ x y : S,
        (∏ k, F k).lazardValuation (Fin.snoc x.1 (r x)) =
          (∏ k, F k).lazardValuation (Fin.snoc y.1 (r y)))
      (k : ι) (x y : S) :
      (F k).lazardValuation (Fin.snoc x.1 (r x)) =
        (F k).lazardValuation (Fin.snoc y.1 (r y)) :=
    (F k).lazardValuation_eq_of_dvd hprod
      (Finset.dvd_prod_of_mem F (Finset.mem_univ k)) isPreconnected_univ
      (continuous_subtype_val.finSnoc (A := fun _ ↦ ℝ) hr).continuousOn
      (fun x _ y _ ↦ hv x y) (mem_univ x) (mem_univ y)
  -- The existing stack API supplies a continuous graph in a sector, also for an empty root list.
  let hgraph := exists_continuous_forall_mem_sectorSet
    D.continuous_root D.strictMono_root (0 : Fin (D.count + 1))
  let r := hgraph.choose
  have hr := hgraph.choose_spec.1
  have hrmem := hgraph.choose_spec.2
  have hsector (k : ι) (x y : S) := hfactor r hr
    (fun x y ↦ D.lazardValuation_snoc_eq_of_mem_sectorSet () (hrmem x) (hrmem y)) k x y
  have hexp (k : ι) (x : S) :
      (g (F k)).lazardExponent (Polynomial.C ∘ x.1) =
        (g (F k)).lazardExponent (Polynomial.C ∘ x₀.1) := by
    have h := hsector k x x₀
    simp only [lazardValuation_snoc (hn k), WithTop.coe_inj, toLex_inj,
      Finsupp.snoc_inj] at h
    exact h.1
  have hmult (k : ι) (i : Fin D.count) (x : S) :
      ((g (F k)).lazardEval (Polynomial.C ∘ x.1)).rootMultiplicity (D.root i x) =
        ((g (F k)).lazardEval (Polynomial.C ∘ x₀.1)).rootMultiplicity (D.root i x₀) := by
    have h := hfactor (D.root i) (D.continuous_root i)
      (fun x y ↦ D.lazardValuation_snoc_eq_of_mem_sectionSet ()
        (z := (x, D.root i x)) (z' := (y, D.root i y))
        (mem_sectionSet.2 rfl) (mem_sectionSet.2 rfl)) k x x₀
    simp only [lazardValuation_snoc (hn k), WithTop.coe_inj, toLex_inj,
      Finsupp.snoc_inj] at h
    exact h.2
  refine
    { nonempty := D.nonempty
      count := D.count
      root := D.root
      continuous_root := D.continuous_root
      strictMono_root := D.strictMono_root
      exponent := fun k ↦ (g (F k)).lazardExponent (Polynomial.C ∘ x₀.1)
      lazardExponent_eq := hexp
      multiplicity := fun k i ↦
        ((g (F k)).lazardEval (Polynomial.C ∘ x₀.1)).rootMultiplicity (D.root i x₀)
      rootMultiplicity_root := hmult
      exists_root_eq := ?_
      exists_multiplicity_pos := ?_ }
  · intro k x _ t ht
    apply D.exists_root_eq () x hprod t
    rw [heval]
    exact (Polynomial.isRoot_prod _ _ _).2 ⟨k, Finset.mem_univ k, ht⟩
  · intro i
    obtain ⟨⟨⟩, hu⟩ := D.exists_multiplicity_pos i
    rw [← D.rootMultiplicity_root () i x₀] at hu
    have hroot : ((g (∏ k, F k)).lazardEval (Polynomial.C ∘ x₀.1)).IsRoot
        (D.root i x₀) := (Polynomial.rootMultiplicity_pos'.1 hu).2
    rw [heval] at hroot
    obtain ⟨k, _, hk⟩ := (Polynomial.isRoot_prod _ _ _).1 hroot
    exact ⟨k, (Polynomial.rootMultiplicity_pos (lazardEval_ne_zero (hgn k) _)).2 hk⟩

variable (hS : IsPreconnected S) (hprod : ∏ k, F k ≠ 0)

/-- Recovering the factors' Lazard delineation preserves the number of root sections. -/
@[simp]
theorem ofProd_count : (D.ofProd hS hprod).count = D.count := (rfl)

/-- Recovering the factors' Lazard delineation preserves the ordered root functions. -/
@[simp]
theorem ofProd_root (i : Fin (D.ofProd hS hprod).count) (x : S) :
    (D.ofProd hS hprod).root i x = D.root (Fin.cast (D.ofProd_count hS hprod) i) x := (rfl)

end TauCeti.LazardDelineation

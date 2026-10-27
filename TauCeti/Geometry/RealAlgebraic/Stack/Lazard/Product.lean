/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Lazard.Basic
import TauCeti.Topology.Algebra.MvPolynomial.Lazard

/-!
# Lazard delineations of products

A Lazard delineation of a nonzero finite product over a preconnected base induces a Lazard
delineation of its factors with exactly the same ordered root functions. Conversely, a Lazard
delineation of a finite family with nonzero product is one of the product, over any base. No
preservation of ordinary fiber degrees or nonnullification is needed. Factors may share roots
and have repeated roots; the empty family is included.

Constant product valuation passes to each divisor along continuous sections. On each product
root section this fixes the factor's root multiplicity. On a continuous graph in a sector it
fixes the factor's removed base exponents. Multiplicativity of Lazard evaluation supplies root
coverage and ensures that each section is used by a factor.

This is the product-to-family step in Lazard lifting: a single-polynomial delineability theorem
applied to a basis product provides the common stack for the basis, even over nullified ordinary
fibers. Its section and sector valuations follow from the existing `LazardDelineation` API.
The converse direction is a direct consequence of multiplicativity: removed base exponents and
root multiplicities of the product are the sums of those of its factors. It lifts a polynomial
divisible by the distinguished variable from the lifting of its cofactor.

## Main declarations

* `TauCeti.LazardDelineation.ofProd`: recover the factors' common Lazard delineation.
* `TauCeti.LazardDelineation.ofProd_count`, `TauCeti.LazardDelineation.ofProd_root`:
  the number and ordered list of root sections are preserved.
* `TauCeti.LazardDelineation.prod`: the Lazard delineation of the product of a delineated
  family, with `TauCeti.LazardDelineation.prod_count`, `TauCeti.LazardDelineation.prod_root`,
  `TauCeti.LazardDelineation.prod_exponent` and `TauCeti.LazardDelineation.prod_multiplicity`.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), Proposition 3.4 and Section 5.3.
-/

public section

open MvPolynomial Set

namespace TauCeti.LazardDelineation

section OfProd

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

end OfProd

section Prod

variable {ι : Type*} [Fintype ι] {n : ℕ}
  {F : ι → MvPolynomial (Fin (n + 1)) ℝ} {S : Set (Fin n → ℝ)} (D : LazardDelineation F S)

/-- A Lazard delineation of a finite family with nonzero product is a Lazard delineation of the
product, with the same ordered root functions. Its removed base exponents and its root
multiplicities are the sums of those of the factors. No connectedness of the base is needed. -/
noncomputable def prod (hprod : ∏ k, F k ≠ 0) :
    LazardDelineation (fun _ : Unit ↦ ∏ k, F k) S := by
  classical
  have hn (k : ι) : F k ≠ 0 := Finset.prod_ne_zero_iff.1 hprod k (Finset.mem_univ k)
  have hgn (k : ι) : optionEquivRight ℝ (Fin n) (rename finSuccEquivLast (F k)) ≠ 0 :=
    (map_ne_zero_iff _ (optionEquivRight ℝ (Fin n)).injective).2
      ((map_ne_zero_iff _ (rename_injective _ finSuccEquivLast.injective)).2 (hn k))
  have heval (x : S) :
      (optionEquivRight ℝ (Fin n) (rename finSuccEquivLast (∏ k, F k))).lazardEval
          (Polynomial.C ∘ x.1) =
        ∏ k, (optionEquivRight ℝ (Fin n) (rename finSuccEquivLast (F k))).lazardEval
          (Polynomial.C ∘ x.1) := by
    simp only [map_prod, ← lazardEvalHom_apply]
  exact
    { nonempty := D.nonempty
      count := D.count
      root := D.root
      continuous_root := D.continuous_root
      strictMono_root := D.strictMono_root
      exponent := fun _ ↦ ∑ k, D.exponent k
      lazardExponent_eq := fun _ x ↦ by
        rw [map_prod, map_prod, lazardExponent_prod _ _ fun k _ ↦ hgn k]
        exact Finset.sum_congr rfl fun k _ ↦ D.lazardExponent_eq k x
      multiplicity := fun _ i ↦ ∑ k, D.multiplicity k i
      rootMultiplicity_root := fun _ i x ↦ by
        -- Root multiplicities in a nonzero product add up.
        rw [heval, ← Polynomial.count_roots, Polynomial.roots_prod _ _
          (Finset.prod_ne_zero_iff.2 fun k _ ↦ lazardEval_ne_zero (hgn k) _), Multiset.count_bind]
        exact Finset.sum_congr rfl fun k _ ↦
          (Polynomial.count_roots _).trans (D.rootMultiplicity_root k i x)
      exists_root_eq := fun _ x _ t ht ↦ by
        rw [heval] at ht
        obtain ⟨k, -, hk⟩ := (Polynomial.isRoot_prod _ _ _).1 ht
        exact D.exists_root_eq k x (hn k) t hk
      exists_multiplicity_pos := fun i ↦ by
        obtain ⟨k, hk⟩ := D.exists_multiplicity_pos i
        exact ⟨(), hk.trans_le (Finset.single_le_sum (f := fun k ↦ D.multiplicity k i)
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ k))⟩ }

variable (hprod : ∏ k, F k ≠ 0)

/-- Passing to the product preserves the number of root sections. -/
@[simp]
theorem prod_count : (D.prod hprod).count = D.count := (rfl)

/-- Passing to the product preserves the ordered root functions. -/
@[simp]
theorem prod_root (i : Fin (D.prod hprod).count) (x : S) :
    (D.prod hprod).root i x = D.root (Fin.cast (D.prod_count hprod) i) x := (rfl)

/-- The removed base exponents of the product are the sum of those of the factors. -/
@[simp]
theorem prod_exponent (u : Unit) : (D.prod hprod).exponent u = ∑ k, D.exponent k := (rfl)

/-- The multiplicity of a root function in the product is the sum of its multiplicities in the
factors. -/
@[simp]
theorem prod_multiplicity (u : Unit) (i : Fin (D.prod hprod).count) :
    (D.prod hprod).multiplicity u i =
      ∑ k, D.multiplicity k (Fin.cast (D.prod_count hprod) i) := (rfl)

end Prod

end TauCeti.LazardDelineation

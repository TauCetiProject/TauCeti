/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Delineation
import TauCeti.Topology.Algebra.Polynomial.RootMultiplicity
import TauCeti.RingTheory.Polynomial.Roots

/-!
# Recovering a family delineation from its product

A delineation of the product of a finite family of nowhere-zero real polynomial fibers
induces a delineation of the family, with exactly the same ordered root functions.
The factors must have continuous coefficients and constant degrees, and the base must
be nonempty and preconnected. Factors may share roots and have repeated roots.

The key point is that every factor multiplicity is locally bounded above, while their
sum, the product multiplicity, is constant. Thus every factor multiplicity is locally
constant, and preconnectedness makes it constant on the whole base. Sign-invariance
then follows from the root coverage and connectedness of sections and sectors.

This allows a discriminant theorem applied to a single basis product to supply the
common stack of its factors, without requiring pairwise coprimality of the fibers or
nonvanishing specialized discriminants. The empty factor family is included: its
product is one and the stack has no sections.

## References

S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
Springer (1998), Sections 2–3 (delineability of a polynomial basis).
-/

public section

open Filter Polynomial Set Topology

namespace TauCeti.Delineation

variable {X ι : Type*} [TopologicalSpace X] [PreconnectedSpace X] [Fintype ι]
  {P : ι → X → ℝ[X]}
  (D : Delineation fun (_ : Unit) x ↦ ∏ k, P k x)

/-- Along each root section of a delineated product, the multiplicity in every
nowhere-zero factor is constant on a preconnected base. No coprimality of factors
is required. -/
theorem rootMultiplicity_eq_of_prod
    (hc : ∀ k j, Continuous fun x ↦ (P k x).coeff j)
    (hn : ∀ k x, P k x ≠ 0)
    (hd : ∀ k x y, (P k x).natDegree = (P k y).natDegree)
    (k : ι) (i : Fin D.count) (x y : X) :
    (P k x).rootMultiplicity (D.root i x) =
      (P k y).rootMultiplicity (D.root i y) := by
  have hl : IsLocallyConstant fun x ↦ (P k x).rootMultiplicity (D.root i x) := by
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x₀ ↦ ?_
    exact (eventually_rootMultiplicity_eq_of_prod Finset.univ
      (d := fun k ↦ (P k x₀).natDegree)
      (fun k _ j _ ↦ (hc k j).continuousAt)
      (fun k _ ↦ .of_forall fun x ↦ (hd k x x₀).le)
      (D.continuous_root i).continuousAt (fun k _ ↦ hn k x₀)
      (.of_forall fun x ↦ (D.rootMultiplicity_root () i x).trans
        (D.rootMultiplicity_root () i x₀).symm)).mono fun x hx ↦ hx k (Finset.mem_univ k)
  exact hl.apply_eq_of_preconnectedSpace x y

variable [Nonempty X]

/-- Recover the common delineation of a finite family from a delineation of its
product. The root list is unchanged, and each factor acquires its own constant
multiplicities and signs. The base is nonempty so that the product's root list
really enumerates roots, including when the factor family is empty. -/
noncomputable def ofProd
    (hc : ∀ k j, Continuous fun x ↦ (P k x).coeff j)
    (hn : ∀ k x, P k x ≠ 0)
    (hd : ∀ k x y, (P k x).natDegree = (P k y).natDegree) : Delineation P := by
  classical
  let x₀ : X := Classical.choice ‹Nonempty X›
  let m (k : ι) (i : Fin D.count) := (P k x₀).rootMultiplicity (D.root i x₀)
  have hm (k : ι) (i : Fin D.count) (x : X) :
      (P k x).rootMultiplicity (D.root i x) = m k i :=
    D.rootMultiplicity_eq_of_prod hc hn hd k i x x₀
  have hroots (k : ι) (x : X) (t : ℝ) (ht : (P k x).IsRoot t) :
      ∃ i, D.root i x = t := by
    apply D.exists_root_eq () x (Finset.prod_ne_zero_iff.mpr fun k _ ↦ hn k x) t
    exact (Polynomial.isRoot_prod _ _ t).mpr ⟨k, Finset.mem_univ k, ht⟩
  have hP (k : ι) : Continuous fun z : X × ℝ ↦ (P k z.1).eval z.2 :=
    continuous_eval_of_continuous_coeff (fun j _ ↦ hc k j) fun x ↦ (hd k x x₀).le
  refine {
    count := D.count
    root := D.root
    continuous_root := D.continuous_root
    strictMono_root := D.strictMono_root
    multiplicity := m
    rootMultiplicity_root := hm
    exists_root_eq := fun k x _ ↦ hroots k x
    exists_multiplicity_pos := fun i ↦ ?_
    eq_zero_or_ne_zero := fun k ↦ .inr (hn k)
    natDegree_eq := hd
    signInvariant_sectionSet := fun k i ↦ ?_
    signInvariant_sectorSet := fun k j ↦ ?_ }
  · -- A product root belongs to at least one factor, even if several factors share it.
    obtain ⟨u, hu⟩ := D.exists_multiplicity_pos i
    obtain ⟨k, _, hk⟩ := (Polynomial.isRoot_prod _ _ _).mp
      ((D.multiplicity_pos_iff x₀).mp hu).2
    exact ⟨k, (rootMultiplicity_pos (hn k x₀)).mpr hk⟩
  · exact signInvariant_eval_sectionSet (I := {i | 0 < m k i}) (hP k)
      (D.continuous_root i) (fun x ↦ (D.strictMono_root x).injective) (.inr (hn k))
      fun x _ t ↦ (isRoot_iff_of_rootMultiplicity (fun i ↦ hm k i x)
        (hroots k x) (hn k x) t).trans (by simp only [mem_ofPred_eq, and_comm])
  · exact signInvariant_eval_sectorSet (hP k) D.continuous_root D.strictMono_root
      (.inr (hn k)) fun x _ ↦ hroots k x

variable (hc : ∀ k j, Continuous fun x ↦ (P k x).coeff j)
  (hn : ∀ k x, P k x ≠ 0)
  (hd : ∀ k x y, (P k x).natDegree = (P k y).natDegree)

/-- Passing from a product to its factors preserves the number of root sections. -/
@[simp]
theorem ofProd_count : (D.ofProd hc hn hd).count = D.count := (rfl)

/-- Passing from a product to its factors preserves the ordered root functions. -/
@[simp]
theorem ofProd_root (i : Fin (D.ofProd hc hn hd).count) (x : X) :
    (D.ofProd hc hn hd).root i x = D.root (Fin.cast (D.ofProd_count hc hn hd) i) x := (rfl)

end TauCeti.Delineation

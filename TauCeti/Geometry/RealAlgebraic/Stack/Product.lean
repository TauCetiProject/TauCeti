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
factor is constant on a preconnected base. Only degree bounds and continuity of
coefficients through those bounds are needed; nonvanishing follows from the positive
product multiplicity on the section, and no coprimality of factors is required. -/
theorem rootMultiplicity_eq_of_prod {d : ι → ℕ}
    (hc : ∀ k, ∀ j ≤ d k, Continuous fun x ↦ (P k x).coeff j)
    (hd : ∀ k x, (P k x).natDegree ≤ d k)
    (k : ι) (i : Fin D.count) (x y : X) :
    (P k x).rootMultiplicity (D.root i x) =
      (P k y).rootMultiplicity (D.root i y) := by
  obtain ⟨u, hu⟩ := D.exists_multiplicity_pos i
  have hn (k : ι) (x : X) : P k x ≠ 0 :=
    Finset.prod_ne_zero_iff.mp ((D.multiplicity_pos_iff x).mp hu).1 k (Finset.mem_univ k)
  exact TauCeti.Polynomial.rootMultiplicity_eq_of_prod Finset.univ
    (fun k _ ↦ hc k) (fun k _ ↦ hd k) (D.continuous_root i) (fun k _ ↦ hn k)
    (fun x y ↦ (D.rootMultiplicity_root () i x).trans
      (D.rootMultiplicity_root () i y).symm) k (Finset.mem_univ k) x y

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
    D.rootMultiplicity_eq_of_prod (d := fun k ↦ (P k x₀).natDegree)
      (fun k j _ ↦ hc k j) (fun k x ↦ (hd k x x₀).le) k i x x₀
  have hroots (k : ι) (x : X) (t : ℝ) (ht : (P k x).IsRoot t) :
      ∃ i, D.root i x = t := by
    apply D.exists_root_eq () x (Finset.prod_ne_zero_iff.mpr fun k _ ↦ hn k x) t
    exact (Polynomial.isRoot_prod _ _ t).mpr ⟨k, Finset.mem_univ k, ht⟩
  refine Delineation.ofRoots hc (fun k ↦ .inr (hn k)) hd D.continuous_root
    D.strictMono_root hm (fun k x _ ↦ hroots k x) fun i ↦ ?_
  -- A product root belongs to at least one factor, even if several factors share it.
  obtain ⟨u, hu⟩ := D.exists_multiplicity_pos i
  obtain ⟨k, _, hk⟩ := (Polynomial.isRoot_prod _ _ _).mp
    ((D.multiplicity_pos_iff x₀).mp hu).2
  exact ⟨k, (rootMultiplicity_pos (hn k x₀)).mpr hk⟩

variable (hc : ∀ k j, Continuous fun x ↦ (P k x).coeff j)
  (hn : ∀ k x, P k x ≠ 0)
  (hd : ∀ k x y, (P k x).natDegree = (P k y).natDegree)

/-- Passing from a product to its factors preserves the number of root sections. -/
@[simp]
theorem ofProd_count : (D.ofProd hc hn hd).count = D.count := by
  simp only [ofProd, ofRoots_count]

/-- Passing from a product to its factors preserves the ordered root functions. -/
@[simp]
theorem ofProd_root (i : Fin (D.ofProd hc hn hd).count) (x : X) :
    (D.ofProd hc hn hd).root i x = D.root (Fin.cast (D.ofProd_count hc hn hd) i) x := by
  unfold ofProd at i ⊢
  exact ofRoots_root _ _ _ _ _ _ _ _ i x

/-- A factor's multiplicity in the recovered delineation is its root multiplicity
along the corresponding product section, at any point of the base.
Supply the point `x` explicitly when using this equality as a rewrite rule:
the multiplicity projection does not determine a point of the base. -/
theorem ofProd_multiplicity (k : ι) (i : Fin (D.ofProd hc hn hd).count) (x : X) :
    (D.ofProd hc hn hd).multiplicity k i =
      (P k x).rootMultiplicity (D.root (Fin.cast (D.ofProd_count hc hn hd) i) x) := by
  rw [← (D.ofProd hc hn hd).rootMultiplicity_root k i x, D.ofProd_root hc hn hd]

/-- The multiplicity of a product section is the sum of the multiplicities of that
section in the factors, including when factors share roots. -/
theorem multiplicity_eq_sum_ofProd (i : Fin D.count) :
    D.multiplicity () i = ∑ k, (D.ofProd hc hn hd).multiplicity k
      (Fin.cast (D.ofProd_count hc hn hd).symm i) := by
  let x : X := Classical.choice ‹Nonempty X›
  rw [← D.rootMultiplicity_root () i x, ← count_roots,
    roots_prod _ _ (Finset.prod_ne_zero_iff.mpr fun k _ ↦ hn k x), Multiset.count_bind]
  simp only [count_roots, Finset.sum_map_val]
  apply Finset.sum_congr rfl
  intro k _
  simpa only [Fin.cast_cast, Fin.cast_refl, id_eq] using
    (D.ofProd_multiplicity hc hn hd k (Fin.cast (D.ofProd_count hc hn hd).symm i) x).symm

end TauCeti.Delineation

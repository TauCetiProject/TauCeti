/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Delineation
public import TauCeti.Topology.Algebra.Polynomial.RootMultiplicity
import TauCeti.RingTheory.Polynomial.Roots

/-!
# Transferring a product delineation to its factors

Over a nonempty preconnected base, a delineation of the product of a finite family of
nonzero polynomials induces a delineation of the family itself. The sections are unchanged.
Continuous coefficients and constant factor degrees suffice; no pairwise coprimality or
separate invariance of factor multiplicities is required.

The product multiplicity is the sum of the factor multiplicities. Each summand is locally
bounded above by its central value, so constancy of their sum makes every summand locally
constant, and preconnectedness makes it globally constant. The resulting fixed membership
of each factor in each section gives sign-invariance on sections and sectors.

This allows analytic delineability of an active basis product to supply the common stack
for all its members. Nullified members must be removed before forming that product.

## References

S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
Springer (1998), Section 2 (the passage from a basis product to its members).
-/

public section

open Filter Function Polynomial Set Topology

namespace TauCeti.Delineation

variable {X ι : Type*} [TopologicalSpace X] [PreconnectedSpace X] [Fintype ι]
  {P : ι → X → ℝ[X]} (D : Delineation fun (_ : Unit) x ↦ ∏ k, P k x)
  (hcoeff : ∀ k j, Continuous fun x ↦ (P k x).coeff j)
  (hdeg : ∀ k x y, (P k x).natDegree = (P k y).natDegree)
  (hne : ∀ k x, P k x ≠ 0)

include hcoeff hne

/-- The multiplicity in each factor along a root section of a product delineation
is constant on a preconnected base. Shared roots and repeated factors are allowed. -/
theorem rootMultiplicity_factor_eq
    (hbound : ∀ k x₀, ∃ d : ℕ, ∀ᶠ x in 𝓝 x₀, (P k x).natDegree ≤ d)
    (k : ι) (i : Fin D.count) (x y : X) :
    (P k x).rootMultiplicity (D.root i x) = (P k y).rootMultiplicity (D.root i y) := by
  classical
  have hlc : IsLocallyConstant fun x ↦ (P k x).rootMultiplicity (D.root i x) := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x₀ ↦ ?_
    choose d hd using fun k ↦ hbound k x₀
    have hm : ∀ᶠ x in 𝓝 x₀,
        (∏ k, P k x).rootMultiplicity (D.root i x) =
          (∏ k, P k x₀).rootMultiplicity (D.root i x₀) :=
      .of_forall fun x ↦ (D.rootMultiplicity_root () i x).trans
        (D.rootMultiplicity_root () i x₀).symm
    exact (eventually_rootMultiplicity_eq_of_prod
      (d := d)
      (fun k j _ ↦ (hcoeff k j).continuousAt)
      hd
      (D.continuous_root i).continuousAt (fun k ↦ hne k x₀) hm).mono
        fun _ hx ↦ hx k
  exact hlc.apply_eq_of_preconnectedSpace x y

include hdeg

variable [Nonempty X]

/-- A delineation of a product induces a common delineation of its nonzero factors,
with exactly the same ordered root sections. -/
noncomputable def factors : Delineation P := by
  classical
  let x₀ : X := Classical.choice ‹Nonempty X›
  let m (k : ι) (i : Fin D.count) := (P k x₀).rootMultiplicity (D.root i x₀)
  have hm (k : ι) (i : Fin D.count) (x : X) :
      (P k x).rootMultiplicity (D.root i x) = m k i :=
    D.rootMultiplicity_factor_eq hcoeff hne
      (fun k y ↦ ⟨(P k y).natDegree, .of_forall fun x ↦ (hdeg k x y).le⟩) k i x x₀
  have hpne (x : X) : ∏ k, P k x ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ ↦ hne k x
  -- Every factor root is a product root, hence one of the original sections.
  have hsub (k : ι) (x : X) (t : ℝ) (ht : (P k x).IsRoot t) :
      ∃ i, D.root i x = t := by
    apply D.exists_root_eq () x (hpne x) t
    simp only [IsRoot.def, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) ht.eq_zero
  have hcont (k : ι) : Continuous fun z : X × ℝ ↦ (P k z.1).eval z.2 :=
    continuous_eval_of_continuous_coeff (d := (P k x₀).natDegree)
      (fun j _ ↦ hcoeff k j) (fun x ↦ (hdeg k x x₀).le)
  refine {
    count := D.count
    root := D.root
    continuous_root := D.continuous_root
    strictMono_root := D.strictMono_root
    multiplicity := m
    rootMultiplicity_root := hm
    exists_root_eq := fun k x _ ↦ hsub k x
    exists_multiplicity_pos := ?_
    eq_zero_or_ne_zero := fun k ↦ .inr (hne k)
    natDegree_eq := hdeg
    signInvariant_sectionSet := ?_
    signInvariant_sectorSet := ?_ }
  · -- Each product section is used by at least one factor.
    intro i
    obtain ⟨_, hi⟩ := D.exists_multiplicity_pos i
    have ht := (D.multiplicity_pos_iff x₀).1 hi
    have hroot : ∃ k, (P k x₀).IsRoot (D.root i x₀) := by
      simpa only [IsRoot.def, eval_prod, Finset.prod_eq_zero_iff, Finset.mem_univ,
        true_and] using ht.2
    obtain ⟨k, hk⟩ := hroot
    exact ⟨k, (rootMultiplicity_pos (hne k x₀)).2 hk⟩
  · intro k i
    exact signInvariant_eval_sectionSet (I := {i | 0 < m k i}) (hcont k)
      (D.continuous_root i) (fun x ↦ (D.strictMono_root x).injective) (.inr (hne k))
      fun x _ t ↦ (isRoot_iff_of_rootMultiplicity (fun i ↦ hm k i x)
        (hsub k x) (hne k x) t).trans (by simp only [mem_ofPred_eq, and_comm])
  · intro k j
    exact signInvariant_eval_sectorSet (hcont k) D.continuous_root D.strictMono_root
      (.inr (hne k)) fun x _ ↦ hsub k x

/-- Transferring a product delineation preserves the number of sections. -/
@[simp]
theorem factors_count : (D.factors hcoeff hdeg hne).count = D.count := (rfl)

/-- The root functions of the transferred delineation are the original root functions. -/
@[simp]
theorem factors_root (i : Fin (D.factors hcoeff hdeg hne).count) (x : X) :
    (D.factors hcoeff hdeg hne).root i x =
      D.root (Fin.cast (D.factors_count hcoeff hdeg hne) i) x := (rfl)

end TauCeti.Delineation

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# Finite products of ideal sheaves

The support of a finite product of ideal sheaves is the union of their supports.
When the supports of finitely many ideal sheaves are pairwise disjoint, their
product equals their intersection.
This identifies the sum of section divisors with their set-theoretic union, and of disjoint
section divisors with their scheme-theoretic union.
-/

public section

open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The support of a finite product of ideal sheaves is the supremum of their supports. -/
@[simp]
theorem support_finset_prod {X : Scheme} {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData) :
    (∏ i ∈ s, I i).support = s.sup fun i ↦ (I i).support := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.prod_insert ha, ih]

/-- The support of a product of ideal sheaves indexed by a finite type, as a set, is the union of
their supports. -/
theorem coe_support_prod {X : Scheme} {ι : Type*} [Fintype ι] (I : ι → X.IdealSheafData) :
    ((∏ i, I i).support : Set X) = ⋃ i, (I i).support := by
  simp

/-- Ideal sheaves with disjoint supports generate the unit ideal sheaf together. -/
theorem sup_eq_top_of_disjoint_support
    {X : Scheme} {I J : X.IdealSheafData} (h : Disjoint I.support J.support) :
    I ⊔ J = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_sup]
  exact h.eq_bot

/-- A finite product of ideal sheaves with pairwise disjoint supports equals their intersection. -/
theorem prod_eq_iInf_of_pairwise_disjoint_support
    {X : Scheme} {ι : Type*} [Fintype ι] (I : ι → X.IdealSheafData)
    (h : Pairwise fun i j ↦ Disjoint (I i).support (I j).support) :
    ∏ i, I i = ⨅ i, I i := by
  classical
  ext U : 2
  have hcop : Pairwise fun i j ↦ IsCoprime ((I i).ideal U) ((I j).ideal U) := by
    intro i j hij
    have hs := Scheme.IdealSheafData.sup_eq_top_of_disjoint_support (h hij)
    have he := congrArg (fun J : X.IdealSheafData ↦ J.ideal U) hs
    exact Ideal.isCoprime_iff_sup_eq.mpr he
  let e : X.IdealSheafData →* Ideal Γ(X, U) :=
    { toFun := fun J ↦ J.ideal U
      map_one' := by simp [Scheme.IdealSheafData.one_eq_top]
      map_mul' := fun _ _ ↦ rfl }
  have he (J : X.IdealSheafData) : e J = J.ideal U := rfl
  refine (map_prod e I Finset.univ).trans ?_
  simpa [he, Scheme.IdealSheafData.ideal_iInf] using
    (Ideal.prod_eq_iInf_of_pairwise_isCoprime
      (s := Finset.univ) (J := fun i ↦ (I i).ideal U)
      (fun i _ j _ hij ↦ hcop hij))

end AlgebraicGeometry.Scheme.IdealSheafData

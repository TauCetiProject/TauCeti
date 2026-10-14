/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.Sum

/-!
# Ranks of finite sums of relative effective Cartier divisors

On a proper relative curve, the rank of the closed subscheme of a finite sum of
relative effective Cartier divisors is the sum of their ranks. In particular, a
sum of section divisors has rank equal to the number of sections, even when they coincide.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.1.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- Ranks add for a finite sum of relative effective Cartier divisors on a proper relative curve. -/
theorem finrank_prod_subschemeι_comp
    {X S : Scheme} {f : X ⟶ S} [IsProper f] [TauCeti.AlgebraicGeometry.RelativeDimensionLE 1 f]
    {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData)
    (hI : ∀ i ∈ s, (I i).IsRelativeEffectiveCartier f) :
    ((∏ i ∈ s, I i).subschemeι ≫ f).finrank = ∑ i ∈ s, ((I i).subschemeι ≫ f).finrank := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    have hrel : (1 : X.IdealSheafData).IsRelativeEffectiveCartier f := by simp
    have := hrel.isFinite
    have := hrel.flat
    funext t
    rw [Pi.zero_apply, Scheme.Hom.finrank_eq_zero_iff_notMem_range]
    rintro ⟨z, -⟩
    exact isEmptyElim (α := (⊤ : X.IdealSheafData).subscheme) z
  | insert a s ha ih =>
    have hrel := TauCeti.isRelativeEffectiveCartier_prod
      (fun i hi ↦ hI i (Finset.mem_insert_of_mem hi))
    have hrel' := TauCeti.isRelativeEffectiveCartier_mul (hI a (Finset.mem_insert_self _ _)) hrel
    have := hrel'.isFinite
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      (hI a (Finset.mem_insert_self _ _)).finrank_mul_subschemeι_comp hrel,
      ih (fun i hi ↦ hI i (Finset.mem_insert_of_mem hi))]

end AlgebraicGeometry.Scheme.IdealSheafData

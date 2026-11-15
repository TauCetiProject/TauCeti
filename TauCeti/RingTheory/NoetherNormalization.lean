/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Localization.Free

/-!
# Noether normalization with a free principal localization

A nontrivial finite-type algebra over a field is finite over a polynomial subalgebra.
After inverting one nonzero polynomial it is free over the corresponding polynomial
localization. Injectivity ensures that this localization of the algebra remains nontrivial.

## References

* The Stacks Project, Tags 00OW and 051R.
-/

public noncomputable section

/-- Noether normalization can be chosen with a nonzero polynomial whose localization
makes the finite algebra free. Its image generates a submonoid avoiding zero. -/
theorem Algebra.FiniteType.exists_injective_finite_free_localizedModule_powers
    (k A : Type*) [Field k] [CommRing A] [Nontrivial A] [Algebra k A]
    [Algebra.FiniteType k A] :
    ∃ (n : ℕ) (g : MvPolynomial (Fin n) k →ₐ[k] A), Function.Injective g ∧
      ∃ r : MvPolynomial (Fin n) k, r ≠ 0 ∧
        letI := g.toRingHom.toAlgebra
        Module.Finite (MvPolynomial (Fin n) k) A ∧
        Module.Free (Localization.Away r) (LocalizedModule (.powers r) A) ∧
        (0 : A) ∉ Algebra.algebraMapSubmonoid A (.powers r) := by
  obtain ⟨n, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let := g.toRingHom.toAlgebra
  have : Module.Finite (MvPolynomial (Fin n) k) A := hfin
  have : Module.FinitePresentation (MvPolynomial (Fin n) k) A :=
    Module.finitePresentation_of_finite _ _
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors (MvPolynomial (Fin n) k))
    (LocalizedModule.mkLinearMap (nonZeroDivisors (MvPolynomial (Fin n) k)) A)
    (FractionRing (MvPolynomial (Fin n) k))
  have hr : r ≠ 0 := nonZeroDivisors.ne_zero hr
  refine ⟨n, g, hg, r, hr, hfin, hfree, ?_⟩
  rintro ⟨_, ⟨m, rfl⟩, hp⟩
  rw [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    map_eq_zero_iff g hg] at hp
  exact pow_ne_zero m hr hp

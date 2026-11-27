/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Complex.TateTwist

import TauCeti.NumberTheory.Padics.UnitsCharacter

/-!
# Equivariant maps between distinct Tate twists of `ℂ_p`

For a finite extension `K/ℚ_p` in `PadicAlgCl p`, every continuous `ℚ_p`-linear equivariant
map `ℂ_p(i) → ℂ_p(j)` is zero when `i ≠ j`. On an algebraic element `x`, restrict to the
Galois group of `K(x)`: the image of `x` is an invariant in the nonzero twist `j - i`, so
Tate's theorem makes it zero. Density of the algebraic closure then finishes the proof.

The Tate twists and their characteristic action equations are defined in
`TauCeti.NumberTheory.Padics.Complex.TateTwist` for arbitrary intermediate fields `K`.

## Main results

* `TauCeti.PadicComplex.continuousLinearMap_eq_zero_of_tateTwist_equivariant`: vanishing of
  continuous linear equivariant maps between distinct twists for finite `K/ℚ_p`.
* `TauCeti.padicComplexTateTwist_hom_eq_zero`: the corresponding vanishing of morphisms of
  bundled Banach representations.

## References

* P. Colmez and W. Nizioł, *On the cohomology of p-adic analytic spaces, II: The
  C_st-conjecture* (2025), Proposition 2.14(i), off-diagonal case.
* J. Tate, *p-divisible groups*, Proceedings of a Conference on Local Fields (1967),
  §3.3, Theorem 2.
-/

public section

open UniformSpace.Completion IntermediateField CategoryTheory

namespace TauCeti.PadicComplex

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

/-- Let `K` be a finite extension of `ℚ_p` inside `PadicAlgCl p`. A continuous `ℚ_p`-linear
map between distinct Tate twists of `ℂ_p` which intertwines the `G_K`-actions is zero. -/
theorem continuousLinearMap_eq_zero_of_tateTwist_equivariant [FiniteDimensional ℚ_[p] K]
    {i j : ℤ} (hij : i ≠ j) (f : ℂ_[p] →L[ℚ_[p]] ℂ_[p])
    (hf : ∀ (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (x : ℂ_[p]),
      f ((((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv ^ i : ℤ_[p]ˣ) : ℤ_[p]) :
        ℚ_[p]) • (σ • x)) =
      (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv ^ j : ℤ_[p]ˣ) : ℤ_[p]) :
        ℚ_[p]) • (σ • f x)) : f = 0 := by
  have h_alg (x : PadicAlgCl p) : f (x : ℂ_[p]) = 0 := by
    let L := K⟮x⟯
    let : FiniteDimensional K L := adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral x)
    let : FiniteDimensional ℚ_[p] L := FiniteDimensional.trans ℚ_[p] K L
    let L' : IntermediateField ℚ_[p] (PadicAlgCl p) := L.restrictScalars ℚ_[p]
    let : FiniteDimensional ℚ_[p] L' := inferInstanceAs (FiniteDimensional ℚ_[p] L)
    apply _root_.PadicComplex.eq_zero_of_forall_cyclotomicCharacter_zpow_mul_smul_eq
      (K := L') (i := j - i) (sub_ne_zero.mpr (Ne.symm hij))
    intro σ
    let τ := σ.restrictScalars K
    have hx : τ • (x : ℂ_[p]) = x := by
      rw [algEquiv_restrictScalars_smul, algEquiv_smul_coe]
      exact congrArg ((↑) : PadicAlgCl p → ℂ_[p])
        (σ.commutes (⟨x, mem_adjoin_simple_self K x⟩ : L))
    have h := hf τ x
    rw [hx, f.map_smul, algEquiv_restrictScalars_smul] at h
    let u := padicIntUnitsInclusion p (cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv)
    have hu (n : ℤ) : ((u ^ n : ℚ_[p]ˣ) : ℚ_[p]) =
        (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv ^ n : ℤ_[p]ˣ) : ℤ_[p]) :
          ℚ_[p]) := by
      rw [← map_zpow, coe_padicIntUnitsInclusion_apply]
    have h' : (u ^ i) • f (x : ℂ_[p]) = (u ^ j) • (σ • f (x : ℂ_[p])) := by
      simpa only [Units.smul_def, hu, τ, AlgEquiv.toRingEquiv_restrictScalars] using h
    -- Cancel the unit `u ^ i` using the ordinary group action on `ℂ_p`.
    have h_cancel : (u ^ (j - i)) • (σ • f (x : ℂ_[p])) = f (x : ℂ_[p]) := by
      rw [zpow_sub, mul_comm, mul_smul, inv_smul_eq_iff]
      exact h'.symm
    simpa only [Units.smul_def, hu, Algebra.smul_def] using h_cancel
  ext x
  exact induction_on x (isClosed_eq f.continuous continuous_const) h_alg

end TauCeti.PadicComplex

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- Let `K` be a finite extension of `ℚ_p` inside `PadicAlgCl p`. There are no nonzero morphisms
between distinct Tate twists of `ℂ_p` in the category of Banach representations of `G_K`. -/
theorem padicComplexTateTwist_hom_eq_zero [FiniteDimensional ℚ_[p] K] {i j : ℤ}
    (hij : i ≠ j) (f : padicComplexTateTwist p K i ⟶ padicComplexTateTwist p K j) :
    f = 0 := by
  apply BanachRep.hom_ext
  apply PadicComplex.continuousLinearMap_eq_zero_of_tateTwist_equivariant (K := K) hij
  intro σ x
  -- The `.ρ` projection through `BanachRep.of` reduces to the fixed-carrier representation.
  simpa only [padicComplexTateTwistContinuousRep_apply] using f.hom_comm_apply σ x

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import TauCeti.NumberTheory.Padics.Complex.GaloisAction
public import TauCeti.RepresentationTheory.Continuous.BanachRep.Basic
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Operations

import TauCeti.NumberTheory.Padics.Complex.TateTwist

/-!
# Equivariant maps between distinct Tate twists of `ℂ_p`

For a finite extension `K/ℚ_p` in `PadicAlgCl p`, every continuous `ℚ_p`-linear equivariant
map `ℂ_p(i) → ℂ_p(j)` is zero when `i ≠ j`. On an algebraic element `x`, restrict to the
Galois group of `K(x)`: the image of `x` is an invariant in the nonzero twist `j - i`, so
Tate's theorem makes it zero. Density of the algebraic closure then finishes the proof.

The main result `TauCeti.padicComplexTateTwist_hom_eq_zero` computes the morphisms between
the bundled Banach representations `TauCeti.padicComplexTateTwist` at distinct integer twists.

## References

* P. Colmez and W. Nizioł, *On the cohomology of p-adic analytic spaces, II: The
  C_st-conjecture* (2025), Proposition 2.14(i), off-diagonal case.
* J. Tate, *p-divisible groups*, Proceedings of a Conference on Local Fields (1967),
  §3.3, Theorem 2.
-/

public section

open UniformSpace.Completion IntermediateField CategoryTheory

namespace PadicComplex

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

/-- A continuous `ℚ_p`-linear map between distinct Tate twists of `ℂ_p` which intertwines the
`G_K`-actions is zero. -/
private theorem continuousLinearMap_eq_zero_of_tateTwist_equivariant [FiniteDimensional ℚ_[p] K]
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
    apply eq_zero_of_forall_cyclotomicCharacter_zpow_mul_smul_eq
      (K := L') (i := j - i) (sub_ne_zero.mpr (Ne.symm hij))
    intro σ
    -- The two actions on the completion come from the same ring automorphism.
    let τ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p :=
      { σ.toRingEquiv with
        commutes' := fun a => σ.commutes
          (⟨a, L.algebraMap_mem a⟩ : L') }
    have hx : τ • (x : ℂ_[p]) = x := by
      rw [algEquiv_smul_coe]
      exact congrArg ((↑) : PadicAlgCl p → ℂ_[p])
        (σ.commutes (⟨x, mem_adjoin_simple_self K x⟩ : L))
    have hτ : τ.toRingEquiv = σ.toRingEquiv := RingEquiv.ext fun _ => rfl
    have hτ_smul (y : ℂ_[p]) : τ • y = σ • y := rfl
    have h := hf τ x
    rw [hx, f.map_smul] at h
    rw [← algebraMap_smul ℂ_[p] _ (f (x : ℂ_[p])),
      ← algebraMap_smul ℂ_[p] _ (τ • f (x : ℂ_[p])), smul_eq_mul, smul_eq_mul] at h
    let c : ℂ_[p]ˣ := Units.map (algebraMap ℚ_[p] ℂ_[p]).toMonoidHom
      (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom
        (cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv))
    have hc (n : ℤ) : (c ^ n : ℂ_[p]ˣ).val =
        algebraMap ℚ_[p] ℂ_[p]
          (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv ^ n : ℤ_[p]ˣ) : ℤ_[p]) :
            ℚ_[p]) := by
      dsimp [c]
      rw [← map_zpow, ← map_zpow]
      rfl
    have h' : (c ^ i : ℂ_[p]ˣ) * f x = (c ^ j : ℂ_[p]ˣ) * σ • f x := by
      simpa only [hc, hτ, hτ_smul] using h
    have h'' := congrArg (fun z : ℂ_[p] => (↑(c ^ (-i)) : ℂ_[p]) * z) h'
    have hji : -i + j = j - i := by omega
    rw [← hc]
    simpa only [← mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero,
      Units.val_one, one_mul, hji] using h''.symm
  ext x
  exact induction_on x (isClosed_eq f.continuous continuous_const) h_alg

end PadicComplex

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- The Tate twist `ℂ_p(i)` as a Banach representation of `G_K` over `ℚ_p`. -/
noncomputable abbrev padicComplexTateTwist (i : ℤ) :
    BanachRep.{0} ℚ_[p] (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) :=
  let χ : (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) →ₜ* ℤ_[p]ˣ :=
    ⟨(cyclotomicCharacter (PadicAlgCl p) p).comp
      (MulSemiringAction.toRingAut (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (PadicAlgCl p)),
      cyclotomicCharacter.continuous p K (PadicAlgCl p)⟩
  let incl : ℤ_[p] →ₜ* ℚ_[p] := ⟨PadicInt.Coe.ringHom.toMonoidHom, continuous_subtypeVal⟩
  BanachRep.of ((ContinuousRep.ofDistribMulAction _ ℚ_[p] ℂ_[p]).twist (incl.unitsMap.comp (χ ^ i)))

/-- The action in the Tate twist is the Galois action multiplied by `χ(σ)^i`. -/
theorem padicComplexTateTwist_ρ_apply (i : ℤ)
    (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (x : ℂ_[p]) :
    (padicComplexTateTwist p K i).ρ σ x =
      (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv ^ i : ℤ_[p]ˣ) : ℤ_[p]) :
        ℚ_[p]) • (σ • x) := by
  unfold padicComplexTateTwist
  erw [ContinuousRep.twist_apply, ContinuousRep.ofDistribMulAction_apply]
  erw [ContinuousMonoidHom.comp_toFun, ContinuousMonoidHom.coe_unitsMap_apply,
    ContinuousMonoidHom.zpow_apply]
  rfl

/-- There are no nonzero morphisms between distinct Tate twists of `ℂ_p` in the category of
Banach representations of `G_K`. -/
theorem padicComplexTateTwist_hom_eq_zero [FiniteDimensional ℚ_[p] K] {i j : ℤ}
    (hij : i ≠ j) (f : padicComplexTateTwist p K i ⟶ padicComplexTateTwist p K j) :
    f = 0 := by
  apply BanachRep.hom_ext
  apply PadicComplex.continuousLinearMap_eq_zero_of_tateTwist_equivariant (K := K) hij
  intro σ x
  have h := f.hom_comm_apply σ x
  -- Present the actions on the native `ℂ_p` carrier before rewriting.
  change f.hom ((padicComplexTateTwist p K i).ρ σ x) =
    (padicComplexTateTwist p K j).ρ σ (f.hom x) at h
  erw [padicComplexTateTwist_ρ_apply, padicComplexTateTwist_ρ_apply] at h
  exact h

end TauCeti

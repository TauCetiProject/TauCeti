/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.WashnitzerAlgebra
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Subst

/-!
# Substitutions in the Monsky–Washnitzer algebra

Let `R` be an ultrametric normed commutative ring with `‖1‖ = 1`, and let `a s` be polynomials
in the variables `τ`, indexed by finitely many `s : σ`, without constant term and with all
coefficients of norm at most `1`. Formal substitution `X s ↦ a s` then carries overconvergent
series to overconvergent series: if `f` is restricted at a radius `ρ > 1` and the `a s` have total
degree at most `A`, the substitution is restricted at `ρ ^ (1 / (A + 1)) > 1`. It is therefore an
`R`-algebra homomorphism `R⟨X⟩† → R⟨Y⟩†` of Monsky–Washnitzer algebras, compatible with the
corresponding homomorphism of Tate algebras, and two mutually inverse substitutions give an
isomorphism.

## Main definitions

* `TauCeti.Dagger.washnitzerAlgebra.subst`: substitution of unit-ball polynomials without
  constant term, as an `R`-algebra homomorphism of Monsky–Washnitzer algebras.
* `TauCeti.Dagger.washnitzerAlgebra.substEquiv`: the isomorphism given by two mutually inverse
  substitutions.

## Main results

* `TauCeti.Dagger.subst_mem_washnitzerAlgebra`: substitution of unit-ball polynomials without
  constant term preserves overconvergence.
* `TauCeti.Dagger.washnitzerAlgebra.subst_X` and
  `TauCeti.Dagger.washnitzerAlgebra.subst_ofMvPolynomial`: the substitution on variables and on
  polynomials.
* `TauCeti.Dagger.washnitzerAlgebra.toTate_subst`: compatibility with the substitutions of the
  Tate algebra.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.3 (iv).
-/

public section

namespace TauCeti.Dagger

open _root_.MvPowerSeries

variable {σ τ R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R]

/-- **Substitution preserves overconvergence.** Substituting finitely many polynomials without
constant term, whose coefficients have norm at most `1`, into an overconvergent series gives an
overconvergent series. -/
theorem subst_mem_washnitzerAlgebra [Finite σ] {a : σ → MvPolynomial τ R}
    (ha₀ : ∀ s, (a s).constantCoeff = 0) (ha₁ : ∀ s t, ‖(a s).coeff t‖ ≤ 1)
    {f : MvPowerSeries σ R} (hf : f ∈ washnitzerAlgebra σ R) :
    f.subst (fun s ↦ (a s : MvPowerSeries τ R)) ∈ washnitzerAlgebra τ R := by
  obtain ⟨ρ, hρ, hf⟩ := mem_washnitzerAlgebra.mp hf
  obtain ⟨A, hA⟩ := (Set.finite_range fun s ↦ (a s).totalDegree).bddAbove
  -- The radius `ρ' = ρ ^ (1 / (A + 1)) > 1` satisfies `ρ' ^ A ≤ ρ' ^ (A + 1) = ρ`.
  have hρ' : 1 < ρ ^ (((A + 1 : ℕ) : ℝ)⁻¹) := Real.one_lt_rpow hρ (by positivity)
  refine mem_washnitzerAlgebra.mpr
    ⟨_, hρ', hf.subst_of_totalDegree_le ha₀ ha₁ (fun s ↦ hA ⟨s, rfl⟩) hρ'.le ?_⟩
  calc (ρ ^ (((A + 1 : ℕ) : ℝ)⁻¹)) ^ A ≤ (ρ ^ (((A + 1 : ℕ) : ℝ)⁻¹)) ^ (A + 1) :=
        pow_le_pow_right₀ hρ'.le A.le_succ
    _ = ρ := Real.rpow_inv_natCast_pow (by linarith) A.succ_ne_zero

namespace washnitzerAlgebra

section Subst

variable [Finite σ] (a : σ → MvPolynomial τ R) (ha₀ : ∀ s, (a s).constantCoeff = 0)
  (ha₁ : ∀ s t, ‖(a s).coeff t‖ ≤ 1)

/-- **Substitution of unit-ball polynomials as a map of Monsky–Washnitzer algebras.**
Substituting polynomials without constant term whose coefficients have norm at most `1` is an
`R`-algebra homomorphism `R⟨X⟩† → R⟨Y⟩†`. -/
noncomputable def subst : washnitzerAlgebra σ R →ₐ[R] washnitzerAlgebra τ R :=
  ((substAlgHom (hasSubst_coe ha₀)).comp (washnitzerAlgebra σ R).val).codRestrict _ fun f ↦ by
    simpa [coe_substAlgHom] using subst_mem_washnitzerAlgebra ha₀ ha₁ f.2

/-- The map of Monsky–Washnitzer algebras is Mathlib's formal substitution. -/
@[simp]
theorem coe_subst (f : washnitzerAlgebra σ R) :
    (subst a ha₀ ha₁ f : MvPowerSeries τ R) =
      (f : MvPowerSeries σ R).subst fun s ↦ (a s : MvPowerSeries τ R) := by
  simp [subst, coe_substAlgHom]

/-- Substitution sends the variable `Xₛ` to the polynomial `a s`. -/
@[simp]
theorem subst_X (s : σ) : subst a ha₀ ha₁ (X σ R s) = ofMvPolynomial τ R (a s) :=
  Subtype.ext <| by simp [_root_.MvPowerSeries.subst_X (hasSubst_coe ha₀)]

/-- Substitution sends a polynomial `p` to the polynomial `p(a)`. -/
@[simp]
theorem subst_ofMvPolynomial (p : MvPolynomial σ R) :
    subst a ha₀ ha₁ (ofMvPolynomial σ R p) = ofMvPolynomial τ R (MvPolynomial.aeval a p) := by
  have h : (subst a ha₀ ha₁).comp (ofMvPolynomial σ R) =
      (ofMvPolynomial τ R).comp (MvPolynomial.aeval a) :=
    MvPolynomial.algHom_ext fun s ↦ by simp
  exact DFunLike.congr_fun h p

/-- Substitution commutes with the inclusions into the Tate algebras. -/
@[simp]
theorem toTate_subst (f : washnitzerAlgebra σ R) :
    toTate τ R (subst a ha₀ ha₁ f) = MvPowerSeries.restrictedSubst a ha₀ ha₁ (toTate σ R f) :=
  Subtype.ext (by simp)

variable [Finite τ] (b : τ → MvPolynomial σ R) (hb₀ : ∀ t, (b t).constantCoeff = 0)
  (hb₁ : ∀ t u, ‖(b t).coeff u‖ ≤ 1)

/-- Substituting `b` after `a` is the identity when `b` inverts `a` under substitution. -/
private theorem subst_subst (hab : ∀ s, MvPolynomial.aeval b (a s) = MvPolynomial.X s)
    (hba : ∀ t, MvPolynomial.aeval a (b t) = MvPolynomial.X t) (f : washnitzerAlgebra σ R) :
    subst b hb₀ hb₁ (subst a ha₀ ha₁ f) = f :=
  toTate_injective <| Subtype.ext <| by
    have h := congrArg Subtype.val
      ((MvPowerSeries.restrictedSubstEquiv a ha₀ ha₁ b hb₀ hb₁ hab hba).symm_apply_apply
        (toTate σ R f))
    simp only [MvPowerSeries.coe_restrictedSubstEquiv_symm,
      MvPowerSeries.coe_restrictedSubstEquiv, coe_toTate] at h
    simpa using h

/-- **Isomorphisms of Monsky–Washnitzer algebras from inverse substitutions.** If two families of
unit-ball polynomials without constant term are inverse to each other under substitution, the
substitutions are mutually inverse `R`-algebra isomorphisms `R⟨X⟩† ≃ R⟨Y⟩†`. -/
noncomputable def substEquiv (hab : ∀ s, MvPolynomial.aeval b (a s) = MvPolynomial.X s)
    (hba : ∀ t, MvPolynomial.aeval a (b t) = MvPolynomial.X t) :
    washnitzerAlgebra σ R ≃ₐ[R] washnitzerAlgebra τ R :=
  AlgEquiv.ofAlgHom (subst a ha₀ ha₁) (subst b hb₀ hb₁)
    (AlgHom.ext <| subst_subst b hb₀ hb₁ a ha₀ ha₁ hba hab)
    (AlgHom.ext <| subst_subst a ha₀ ha₁ b hb₀ hb₁ hab hba)

/-- The isomorphism of Monsky–Washnitzer algebras is the substitution of `a`. -/
@[simp]
theorem coe_substEquiv (hab : ∀ s, MvPolynomial.aeval b (a s) = MvPolynomial.X s)
    (hba : ∀ t, MvPolynomial.aeval a (b t) = MvPolynomial.X t) (f : washnitzerAlgebra σ R) :
    (substEquiv a ha₀ ha₁ b hb₀ hb₁ hab hba f : MvPowerSeries τ R) =
      (f : MvPowerSeries σ R).subst fun s ↦ (a s : MvPowerSeries τ R) :=
  coe_subst a ha₀ ha₁ f

/-- The inverse isomorphism of Monsky–Washnitzer algebras is the substitution of `b`. -/
@[simp]
theorem coe_substEquiv_symm (hab : ∀ s, MvPolynomial.aeval b (a s) = MvPolynomial.X s)
    (hba : ∀ t, MvPolynomial.aeval a (b t) = MvPolynomial.X t) (f : washnitzerAlgebra τ R) :
    ((substEquiv a ha₀ ha₁ b hb₀ hb₁ hab hba).symm f : MvPowerSeries σ R) =
      (f : MvPowerSeries τ R).subst fun t ↦ (b t : MvPowerSeries σ R) :=
  coe_subst b hb₀ hb₁ f

/-- The isomorphism of Monsky–Washnitzer algebras sends the variable `Xₛ` to `a s`. -/
@[simp]
theorem substEquiv_X (hab : ∀ s, MvPolynomial.aeval b (a s) = MvPolynomial.X s)
    (hba : ∀ t, MvPolynomial.aeval a (b t) = MvPolynomial.X t) (s : σ) :
    substEquiv a ha₀ ha₁ b hb₀ hb₁ hab hba (X σ R s) = ofMvPolynomial τ R (a s) :=
  subst_X a ha₀ ha₁ s

/-- The inverse isomorphism of Monsky–Washnitzer algebras sends the variable `Xₜ` to `b t`. -/
@[simp]
theorem substEquiv_symm_X (hab : ∀ s, MvPolynomial.aeval b (a s) = MvPolynomial.X s)
    (hba : ∀ t, MvPolynomial.aeval a (b t) = MvPolynomial.X t) (t : τ) :
    (substEquiv a ha₀ ha₁ b hb₀ hb₁ hab hba).symm (X τ R t) = ofMvPolynomial σ R (b t) :=
  subst_X b hb₀ hb₁ t

/-- The isomorphism of Monsky–Washnitzer algebras is the restriction of the isomorphism of Tate
algebras given by the same substitutions. -/
@[simp]
theorem toTate_substEquiv (hab : ∀ s, MvPolynomial.aeval b (a s) = MvPolynomial.X s)
    (hba : ∀ t, MvPolynomial.aeval a (b t) = MvPolynomial.X t) (f : washnitzerAlgebra σ R) :
    toTate τ R (substEquiv a ha₀ ha₁ b hb₀ hb₁ hab hba f) =
      MvPowerSeries.restrictedSubstEquiv a ha₀ ha₁ b hb₀ hb₁ hab hba (toTate σ R f) :=
  Subtype.ext (by simp)

end Subst

end washnitzerAlgebra

end TauCeti.Dagger

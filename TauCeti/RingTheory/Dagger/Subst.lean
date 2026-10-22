/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.WashnitzerAlgebra
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Distinguished

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

The main example is the triangular automorphism `Y ↦ Y`, `Xᵢ ↦ Xᵢ + Y ^ α i` of `R⟨X, Y⟩†`, with
`Y = X none`. Over a complete nonarchimedean field `K`, a suitable such automorphism makes any
nonzero overconvergent series `f` distinguished in `Y`: written as a series in `Y` over the Tate
algebra in the remaining variables, its image is distinguished of some degree `s` at radius `1`,
and its coefficient in degree `s` is a unit. This is the change of variables that precedes
Weierstrass division and preparation in `K⟨X, Y⟩†`. The automorphism is the restriction of the
corresponding automorphism of the Tate algebra, so the statement follows from the Tate algebra
case `TauCeti.MvPowerSeries.exists_restrictedTriangularEquiv_isDistinguished_isUnit`.

## Main definitions

* `TauCeti.Dagger.washnitzerAlgebra.subst`: substitution of unit-ball polynomials without
  constant term, as an `R`-algebra homomorphism of Monsky–Washnitzer algebras.
* `TauCeti.Dagger.washnitzerAlgebra.substEquiv`: the isomorphism given by two mutually inverse
  substitutions.
* `TauCeti.Dagger.washnitzerAlgebra.triangularEquiv`: the triangular automorphism
  `Y ↦ Y`, `Xᵢ ↦ Xᵢ + Y ^ α i` of `R⟨X, Y⟩†`.

## Main results

* `TauCeti.Dagger.subst_mem_washnitzerAlgebra`: substitution of unit-ball polynomials without
  constant term preserves overconvergence.
* `TauCeti.Dagger.washnitzerAlgebra.toTate_subst` and
  `TauCeti.Dagger.washnitzerAlgebra.toTate_triangularEquiv`: compatibility with the
  substitutions of the Tate algebra.
* `TauCeti.Dagger.washnitzerAlgebra.exists_triangularEquiv_isDistinguished_isUnit`: over a
  complete nonarchimedean field, a triangular automorphism makes every nonzero overconvergent
  series distinguished in `Y`, with a unit coefficient in the distinguished degree.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.3 (iv).
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.4.
-/

public section

namespace TauCeti.Dagger

open _root_.MvPowerSeries
open TauCeti.MvPowerSeries (triangularFamily constantCoeff_triangularFamily
  norm_coeff_triangularFamily_le aeval_triangularFamily restrictedTriangularEquiv)

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

/-- The isomorphism of Monsky–Washnitzer algebras is the restriction of the isomorphism of Tate
algebras given by the same substitutions. -/
@[simp]
theorem toTate_substEquiv (hab : ∀ s, MvPolynomial.aeval b (a s) = MvPolynomial.X s)
    (hba : ∀ t, MvPolynomial.aeval a (b t) = MvPolynomial.X t) (f : washnitzerAlgebra σ R) :
    toTate τ R (substEquiv a ha₀ ha₁ b hb₀ hb₁ hab hba f) =
      MvPowerSeries.restrictedSubstEquiv a ha₀ ha₁ b hb₀ hb₁ hab hba (toTate σ R f) :=
  Subtype.ext (by simp)

end Subst

section Triangular

variable [Finite σ]

/-- The triangular automorphism `Y ↦ Y`, `Xᵢ ↦ Xᵢ + Y ^ α i` of the Monsky–Washnitzer algebra
in the variables `Option σ`, where `Y` is the variable `none` and the exponents `α` are
positive. Its inverse is `Xᵢ ↦ Xᵢ - Y ^ α i`. -/
noncomputable def triangularEquiv (α : σ → ℕ) (hα : ∀ i, α i ≠ 0) :
    washnitzerAlgebra (Option σ) R ≃ₐ[R] washnitzerAlgebra (Option σ) R :=
  substEquiv (triangularFamily α 1) (constantCoeff_triangularFamily hα 1)
    (norm_coeff_triangularFamily_le norm_one.le α) (triangularFamily α (-1))
    (constantCoeff_triangularFamily hα (-1))
    (norm_coeff_triangularFamily_le (by simp : ‖(-1 : R)‖ ≤ 1) α)
    (aeval_triangularFamily α (neg_add_cancel 1)) (aeval_triangularFamily α (add_neg_cancel 1))

/-- The triangular automorphism fixes the variable `Y`. -/
@[simp]
theorem triangularEquiv_X_none (α : σ → ℕ) (hα : ∀ i, α i ≠ 0) :
    triangularEquiv α hα (X (Option σ) R none) = X (Option σ) R none :=
  Subtype.ext <| by
    simp [triangularEquiv, subst_X (MvPowerSeries.hasSubst_coe (constantCoeff_triangularFamily
      (R := R) hα 1))]

/-- The triangular automorphism sends `Xᵢ` to `Xᵢ + Y ^ α i`. -/
@[simp]
theorem triangularEquiv_X_some (α : σ → ℕ) (hα : ∀ i, α i ≠ 0) (i : σ) :
    triangularEquiv α hα (X (Option σ) R (some i)) =
      X (Option σ) R (some i) + X (Option σ) R none ^ α i :=
  Subtype.ext <| by
    simp [triangularEquiv, subst_X (MvPowerSeries.hasSubst_coe (constantCoeff_triangularFamily
      (R := R) hα 1))]

/-- The triangular automorphism of the Monsky–Washnitzer algebra is the restriction of the
triangular automorphism of the Tate algebra. -/
@[simp]
theorem toTate_triangularEquiv (α : σ → ℕ) (hα : ∀ i, α i ≠ 0)
    (f : washnitzerAlgebra (Option σ) R) :
    toTate (Option σ) R (triangularEquiv α hα f) =
      restrictedTriangularEquiv α hα (toTate (Option σ) R f) :=
  Subtype.ext (by simp [triangularEquiv])

end Triangular

/-- **Distinguishing automorphisms of Monsky–Washnitzer algebras.** Over a complete
nonarchimedean field `K`, every nonzero overconvergent series `f` in the variables `Option σ`,
for finite `σ`, is carried by a triangular automorphism `Y ↦ Y`, `Xᵢ ↦ Xᵢ + Y ^ α i` of
`K⟨X, Y⟩†` to a series which, as a restricted series in the variable `Y = none` over the Tate
algebra in the variables `σ`, is distinguished of some degree `s` at radius `1` with a unit
coefficient in degree `s`. -/
theorem exists_triangularEquiv_isDistinguished_isUnit {K : Type*} [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [Finite σ] (f : washnitzerAlgebra (Option σ) K)
    (hf : f ≠ 0) :
    ∃ (α : σ → ℕ) (hα : ∀ i, α i ≠ 0) (s : ℕ),
      PowerSeries.IsDistinguished 1 s (Huber.restrictedOptionEquiv
        (toTate (Option σ) K (triangularEquiv α hα f)) :
          PowerSeries (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))) ∧
      IsUnit (PowerSeries.coeff s (Huber.restrictedOptionEquiv
        (toTate (Option σ) K (triangularEquiv α hα f)) :
          PowerSeries (IsRestricted.subring (R := K) (fun _ : σ ↦ 1)))) := by
  have hf' : toTate (Option σ) K f ≠ 0 := fun h ↦ hf (toTate_injective (h.trans (map_zero _).symm))
  obtain ⟨α, hα, s, hd, hu⟩ :=
    MvPowerSeries.exists_restrictedTriangularEquiv_isDistinguished_isUnit _ hf'
  exact ⟨α, hα, s, by simpa using hd, by simpa using hu⟩

end washnitzerAlgebra

end TauCeti.Dagger

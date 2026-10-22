/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Subst
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Distinguished

/-!
# Making an overconvergent series distinguished in one variable

Let `R` be an ultrametric normed commutative ring with `‖1‖ = 1`. The triangular substitution
`Y ↦ Y`, `Xᵢ ↦ Xᵢ + Y ^ α i`, with `Y = X none`, is an automorphism of the Monsky–Washnitzer
algebra `R⟨X, Y⟩†`. Over a complete nonarchimedean field `K`, a suitable such automorphism makes
any nonzero overconvergent series `f` distinguished in `Y`: written as a series in `Y` over the
Tate algebra in the remaining variables, its image is distinguished of some degree `s` at radius
`1`, and its coefficient in degree `s` is a unit. This is the change of variables that precedes
Weierstrass division and preparation in `K⟨X, Y⟩†`. The automorphism is the restriction of the
corresponding automorphism of the Tate algebra, so the statement follows from the Tate algebra
case `TauCeti.MvPowerSeries.exists_restrictedTriangularEquiv_isDistinguished_isUnit`.

## Main definitions

* `TauCeti.Dagger.washnitzerAlgebra.triangularEquiv`: the triangular automorphism
  `Y ↦ Y`, `Xᵢ ↦ Xᵢ + Y ^ α i` of `R⟨X, Y⟩†`.

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.toTate_triangularEquiv`: compatibility with the triangular
  automorphism of the Tate algebra.
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

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R]

namespace washnitzerAlgebra

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
    triangularEquiv α hα (X (Option σ) R none) = X (Option σ) R none := by
  simp [triangularEquiv]

/-- The triangular automorphism sends `Xᵢ` to `Xᵢ + Y ^ α i`. -/
@[simp]
theorem triangularEquiv_X_some (α : σ → ℕ) (hα : ∀ i, α i ≠ 0) (i : σ) :
    triangularEquiv α hα (X (Option σ) R (some i)) =
      X (Option σ) R (some i) + X (Option σ) R none ^ α i := by
  simp [triangularEquiv]

/-- The inverse triangular automorphism fixes the variable `Y`. -/
@[simp]
theorem triangularEquiv_symm_X_none (α : σ → ℕ) (hα : ∀ i, α i ≠ 0) :
    (triangularEquiv α hα).symm (X (Option σ) R none) = X (Option σ) R none := by
  simp [triangularEquiv]

/-- The inverse triangular automorphism sends `Xᵢ` to `Xᵢ - Y ^ α i`. -/
@[simp]
theorem triangularEquiv_symm_X_some (α : σ → ℕ) (hα : ∀ i, α i ≠ 0) (i : σ) :
    (triangularEquiv α hα).symm (X (Option σ) R (some i)) =
      X (Option σ) R (some i) - X (Option σ) R none ^ α i := by
  simp [triangularEquiv, sub_eq_add_neg]

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

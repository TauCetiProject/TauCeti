/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.AnalyticSubst
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Rescale

/-!
# Affine changes of coordinates on restricted power series

Let `R` be a complete ultrametric normed commutative ring and let `r`, `s` be positive
polyradii for variables `X₁, …, X_k` and `Y₁, …, Y_k`. For constants `aᵢ, uᵢ ∈ R` with
`‖aᵢ‖ ≤ rᵢ` and `‖uᵢ‖ sᵢ ≤ rᵢ`, the affine map `Yᵢ ↦ aᵢ + uᵢ Yᵢ` sends the closed polydisc of
radii `s` into the closed polydisc of radii `r`. Pulling back along it is the analytic
substitution

```text
R{X/r} → R{Y/s},   f(X) ↦ f(a + u Y),
```

an `R`-algebra homomorphism that does not increase Gauss norms. Affine substitutions compose as
affine maps do, and evaluating `f(a + u Y)` at `b` is evaluating `f` at `a + u b`. They contain
both translation `Xᵢ ↦ Xᵢ + aᵢ` (`uᵢ = 1`) and rescaling by units `Xᵢ ↦ uᵢ Xᵢ` (`aᵢ = 0`).

When each `uᵢ` is a unit with `‖uᵢ⁻¹‖ rᵢ ≤ sᵢ`, the inverse affine map
`Xᵢ ↦ uᵢ⁻¹ (Xᵢ - aᵢ)` satisfies the same bounds in the opposite direction, so the affine
substitution is an isometric `R`-algebra isomorphism `R{X/r} ≃ R{Y/s}`. Both bounds hold, for
instance, when `uᵢ` is a multiplicative unit with `‖uᵢ‖ sᵢ = rᵢ`, since then
`‖uᵢ⁻¹‖ = ‖uᵢ‖⁻¹`. These isomorphisms are the changes of coordinates between closed polydiscs,
of arbitrary positive real radii, centred at points of `R`.

## Main definitions

* `TauCeti.MvPowerSeries.restrictedAffine`: the substitution `f ↦ f(a + u Y)` as an `R`-algebra
  homomorphism `R{X/r} →ₐ[R] R{Y/s}`.
* `TauCeti.MvPowerSeries.restrictedAffineEquiv`: the affine substitution by units, as an
  `R`-algebra isomorphism with inverse the substitution of the inverse affine map.

## Main results

* `TauCeti.MvPowerSeries.norm_restrictedAffine_le`: affine substitution is contractive.
* `TauCeti.MvPowerSeries.restrictedAffine_comp`: the composition law.
* `TauCeti.MvPowerSeries.restrictedEval₂_restrictedAffine`: the evaluation law.
* `TauCeti.MvPowerSeries.restrictedAffine_one`: the case `u = 1` is translation.
* `TauCeti.MvPowerSeries.restrictedAffine_zero`: the case `a = 0` is rescaling.
* `TauCeti.MvPowerSeries.norm_restrictedAffineEquiv`: affine isomorphisms are isometries.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, §5.1, for
  Tate algebras and their homomorphisms.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {k : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  {r s t : Fin k → ℝ}

section AffineHom

variable [∀ i, Fact (0 < s i)]

omit [CompleteSpace R] in
/-- The affine series `a + u Yᵢ` has Gauss norm at most `ρ` at the radii `s` when `‖a‖ ≤ ρ` and
`‖u‖ sᵢ ≤ ρ`. -/
theorem norm_algebraMap_add_algebraMap_mul_X_le {i : Fin k} {a u : R} {ρ : ℝ} (ha : ‖a‖ ≤ ρ)
    (hu : ‖u‖ * s i ≤ ρ) :
    ‖(algebraMap R _ a + algebraMap R _ u * ⟨X i, isRestricted_monomial s (Finsupp.single i 1) 1⟩ :
      IsRestricted.subring (R := R) s)‖ ≤ ρ := by
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rwa [norm_algebraMap_isRestrictedSubring]
  · -- `u Yᵢ` is the monomial of exponent `single i 1` and coefficient `u`
    have h : (algebraMap R _ u * ⟨X i, isRestricted_monomial s (Finsupp.single i 1) 1⟩ :
        IsRestricted.subring (R := R) s) =
          ⟨monomial (Finsupp.single i 1) u, isRestricted_monomial s _ u⟩ :=
      by rw [mk_monomial_eq_algebraMap_mul_prod, Finsupp.prod_single_index (by simp), pow_one]
    rw [h, norm_monomial]
    simpa using hu

variable (a u : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ r i) (hu : ∀ i, ‖u i‖ * s i ≤ r i)

/-- **Affine substitution** `Xᵢ ↦ aᵢ + uᵢ Yᵢ`, from the polyradius `r` to the polyradius `s`,
for constants with `‖aᵢ‖ ≤ rᵢ` and `‖uᵢ‖ sᵢ ≤ rᵢ`. -/
noncomputable def restrictedAffine :
    IsRestricted.subring (R := R) r →ₐ[R] IsRestricted.subring (R := R) s :=
  restrictedAnalyticSubst
    (fun i ↦ (algebraMap R _ (a i) + algebraMap R _ (u i) *
      ⟨X i, isRestricted_monomial s (Finsupp.single i 1) 1⟩ : IsRestricted.subring (R := R) s))
    -- the bound is elaborated after the series it bounds; as a term, unification times out
    fun i ↦ by exact norm_algebraMap_add_algebraMap_mul_X_le (ha i) (hu i)

/-- Affine substitution is the analytic substitution `Xᵢ ↦ aᵢ + uᵢ Yᵢ`, so the substitution
API (coefficient formula, coefficient maps, comparison with formal substitution) applies to
it. -/
theorem restrictedAffine_def :
    restrictedAffine a u ha hu = restrictedAnalyticSubst
      (fun i ↦ (algebraMap R _ (a i) + algebraMap R _ (u i) *
        ⟨X i, isRestricted_monomial s (Finsupp.single i 1) 1⟩ : IsRestricted.subring (R := R) s))
      (fun i ↦ by exact norm_algebraMap_add_algebraMap_mul_X_le (ha i) (hu i)) := (rfl)

/-- Affine substitution sends `Xᵢ` to `aᵢ + uᵢ Yᵢ`. -/
@[simp]
theorem restrictedAffine_X (i : Fin k) :
    restrictedAffine a u ha hu ⟨X i, isRestricted_monomial r (Finsupp.single i 1) 1⟩ =
      (algebraMap R _ (a i) + algebraMap R _ (u i) *
        ⟨X i, isRestricted_monomial s (Finsupp.single i 1) 1⟩ : IsRestricted.subring (R := R) s) :=
  restrictedAnalyticSubst_X _ _ i

variable [∀ i, Fact (0 < r i)]

/-- **Affine substitution does not increase the Gauss norm**: `‖f(a + u Y)‖_s ≤ ‖f‖_r`. -/
theorem norm_restrictedAffine_le (f : IsRestricted.subring (R := R) r) :
    ‖restrictedAffine a u ha hu f‖ ≤ ‖f‖ :=
  norm_restrictedAnalyticSubst_le _ _ f

/-- Affine substitution is continuous for the Gauss norms. -/
theorem continuous_restrictedAffine : Continuous (restrictedAffine a u ha hu) :=
  continuous_restrictedAnalyticSubst _ _

/-- **Uniqueness of affine substitution**: a continuous `R`-algebra homomorphism
`R{X/r} → R{Y/s}` sending each `Xᵢ` to `aᵢ + uᵢ Yᵢ` is the affine substitution. -/
theorem eq_restrictedAffine
    (ψ : IsRestricted.subring (R := R) r →ₐ[R] IsRestricted.subring (R := R) s)
    (hψ : Continuous ψ)
    (hX : ∀ i, ψ ⟨X i, isRestricted_monomial r (Finsupp.single i 1) 1⟩ =
      (algebraMap R _ (a i) + algebraMap R _ (u i) *
        ⟨X i, isRestricted_monomial s (Finsupp.single i 1) 1⟩ : IsRestricted.subring (R := R) s)) :
    ψ = restrictedAffine a u ha hu :=
  eq_restrictedAnalyticSubst _ _ ψ hψ hX

/-- **Affine substitutions compose as affine maps**: substituting `Yᵢ ↦ bᵢ + vᵢ Zᵢ` into
`f(a + u Y)` gives `f((a + u b) + (u v) Z)`. -/
theorem restrictedAffine_comp [∀ i, Fact (0 < t i)] (b v : Fin k → R) (hb : ∀ i, ‖b i‖ ≤ s i)
    (hv : ∀ i, ‖v i‖ * t i ≤ s i) :
    (restrictedAffine b v hb hv).comp (restrictedAffine a u ha hu) =
      restrictedAffine (a + u * b) (u * v)
        (fun i ↦ (IsUltrametricDist.norm_add_le_max _ _).trans <| max_le (ha i) <|
          (norm_mul_le _ _).trans <| (mul_le_mul_of_nonneg_left (hb i) (norm_nonneg _)).trans
            (hu i))
        (fun i ↦ ((mul_le_mul_of_nonneg_right (norm_mul_le _ _) (Fact.out : 0 < t i).le).trans
          (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hv i) (norm_nonneg _))).trans
            (hu i)) :=
  eq_restrictedAffine _ _ _ _ _
    ((continuous_restrictedAffine b v hb hv).comp (continuous_restrictedAffine a u ha hu))
    fun i ↦ by
      simp only [AlgHom.comp_apply, restrictedAffine_X, map_add, map_mul, AlgHom.commutes,
        Pi.add_apply, Pi.mul_apply]
      ring

/-- **Evaluation of an affine substitution**: for `b` in a complete ultrametric ring with
`‖bᵢ‖ ≤ sᵢ`, evaluating `f(a + u Y)` at `b` is evaluating `f` at `φ(a) + φ(u) b`. -/
theorem restrictedEval₂_restrictedAffine {S : Type*} [NormedCommRing S] [IsUltrametricDist S]
    [CompleteSpace S] (φ : R →+* S) (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) (b : Fin k → S)
    (hb : ∀ i, ‖b i‖ ≤ s i) (f : IsRestricted.subring (R := R) r) :
    restrictedEval₂ φ b hφ hb (restrictedAffine a u ha hu f) =
      restrictedEval₂ φ (fun i ↦ φ (a i) + φ (u i) * b i) hφ
        (fun i ↦ (IsUltrametricDist.norm_add_le_max _ _).trans <| max_le ((hφ _).trans (ha i)) <|
          (norm_mul_le _ _).trans <| (mul_le_mul (hφ _) (hb i) (norm_nonneg _)
            (norm_nonneg _)).trans (hu i)) f := by
  rw [restrictedAffine_def, restrictedEval₂_restrictedAnalyticSubst]
  congr 1
  ext i
  simp

end AffineHom

section Special

variable [NormOneClass R] [∀ i, Fact (0 < r i)]

/-- **The case `u = 1` is translation**: substituting `Xᵢ ↦ aᵢ + Xᵢ` is
`TauCeti.MvPowerSeries.restrictedTranslate`. -/
theorem restrictedAffine_one (a : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ r i) :
    restrictedAffine a 1 ha (fun i ↦ by simp) = restrictedTranslate a ha :=
  (eq_restrictedAffine _ _ _ _ _ (continuous_restrictedTranslate a ha) fun i ↦ by
    simp [add_comm]).symm

/-- **The identity is an affine substitution**: substituting `Xᵢ ↦ 0 + 1 · Xᵢ` is the identity. -/
@[simp]
theorem restrictedAffine_zero_one :
    restrictedAffine (r := r) 0 1 (fun i ↦ by simpa using (Fact.out : 0 < r i).le)
      (fun i ↦ by simp) = AlgHom.id R _ :=
  (eq_restrictedAffine _ _ _ _ _ continuous_id fun i ↦ by simp).symm

end Special

section Rescale

variable [∀ i, Fact (0 < r i)] [∀ i, Fact (0 < s i)]

/-- **The case `a = 0` is rescaling**: for multiplicative units with `‖uᵢ‖ sᵢ = rᵢ`, substituting
`Xᵢ ↦ uᵢ Yᵢ` is `TauCeti.MvPowerSeries.restrictedRescaleEquiv`. -/
theorem restrictedAffine_zero (u : Fin k → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hrs : ∀ i, ‖(u i : R)‖ * s i = r i) :
    restrictedAffine 0 (fun i ↦ (u i : R)) (fun i ↦ by simpa using (Fact.out : 0 < r i).le)
        (fun i ↦ (hrs i).le) =
      (restrictedRescaleEquiv u hu hrs : IsRestricted.subring (R := R) r →ₐ[R] _) :=
  (eq_restrictedAffine _ _ _ _ _ (isometry_restrictedRescaleEquiv u hu hrs).continuous
    fun i ↦ by simp).symm

end Rescale

section AffineEquiv

variable [∀ i, Fact (0 < r i)] [∀ i, Fact (0 < s i)]
  (a : Fin k → R) (u : Fin k → Rˣ) (ha : ∀ i, ‖a i‖ ≤ r i) (hu : ∀ i, ‖(u i : R)‖ * s i ≤ r i)
  (hu' : ∀ i, ‖(((u i)⁻¹ : Rˣ) : R)‖ * r i ≤ s i)

/-- **Affine substitution by units is an isomorphism**: if each `uᵢ` is a unit with
`‖uᵢ‖ sᵢ ≤ rᵢ` and `‖uᵢ⁻¹‖ rᵢ ≤ sᵢ`, substituting `Xᵢ ↦ aᵢ + uᵢ Yᵢ` is an `R`-algebra
isomorphism `R{X/r} ≃ R{Y/s}`, with inverse the substitution `Yᵢ ↦ uᵢ⁻¹ (Xᵢ - aᵢ)`. -/
noncomputable def restrictedAffineEquiv :
    IsRestricted.subring (R := R) r ≃ₐ[R] IsRestricted.subring (R := R) s :=
  AlgEquiv.ofAlgHom (restrictedAffine a (fun i ↦ (u i : R)) ha hu)
    (restrictedAffine (fun i ↦ -((((u i)⁻¹ : Rˣ) : R) * a i)) (fun i ↦ (((u i)⁻¹ : Rˣ) : R))
      (fun i ↦ (norm_neg _).trans_le <| (norm_mul_le _ _).trans <|
        (mul_le_mul_of_nonneg_left (ha i) (norm_nonneg _)).trans (hu' i)) hu')
    (by
      rw [restrictedAffine_comp]
      exact (eq_restrictedAffine _ _ _ _ (AlgHom.id R _) continuous_id fun i ↦ by simp).symm)
    (by
      rw [restrictedAffine_comp]
      exact (eq_restrictedAffine _ _ _ _ (AlgHom.id R _) continuous_id fun i ↦ by simp).symm)

/-- The isomorphism `restrictedAffineEquiv a u` is the affine substitution `Xᵢ ↦ aᵢ + uᵢ Yᵢ`. -/
@[simp]
theorem coe_restrictedAffineEquiv :
    ⇑(restrictedAffineEquiv a u ha hu hu') = restrictedAffine a (fun i ↦ (u i : R)) ha hu := (rfl)

/-- The inverse of the affine isomorphism is the substitution `Yᵢ ↦ uᵢ⁻¹ (Xᵢ - aᵢ)`. -/
@[simp]
theorem restrictedAffineEquiv_symm :
    ⇑(restrictedAffineEquiv a u ha hu hu').symm =
      restrictedAffine (fun i ↦ -((((u i)⁻¹ : Rˣ) : R) * a i)) (fun i ↦ (((u i)⁻¹ : Rˣ) : R))
        (fun i ↦ (norm_neg _).trans_le <| (norm_mul_le _ _).trans <|
          (mul_le_mul_of_nonneg_left (ha i) (norm_nonneg _)).trans (hu' i)) hu' := (rfl)

/-- **Affine isomorphisms are isometries** for the Gauss norms at the radii `r` and `s`. -/
theorem norm_restrictedAffineEquiv (f : IsRestricted.subring (R := R) r) :
    ‖restrictedAffineEquiv a u ha hu hu' f‖ = ‖f‖ := by
  refine le_antisymm (norm_restrictedAffine_le _ _ _ _ f) ?_
  calc ‖f‖ = ‖(restrictedAffineEquiv a u ha hu hu').symm (restrictedAffineEquiv a u ha hu hu' f)‖ :=
        by rw [AlgEquiv.symm_apply_apply]
    _ ≤ ‖restrictedAffineEquiv a u ha hu hu' f‖ := by
        rw [restrictedAffineEquiv_symm]
        exact norm_restrictedAffine_le _ _ _ _ _

/-- Affine isomorphisms are isometries for the Gauss norms. -/
theorem isometry_restrictedAffineEquiv : Isometry (restrictedAffineEquiv a u ha hu hu') :=
  AddMonoidHomClass.isometry_iff_norm _ |>.mpr (norm_restrictedAffineEquiv a u ha hu hu')

end AffineEquiv

end TauCeti.MvPowerSeries

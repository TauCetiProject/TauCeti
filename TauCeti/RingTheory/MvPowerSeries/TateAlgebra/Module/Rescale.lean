/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Coefficients
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Coefficients
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Rescale

/-!
# Rescaling module-valued restricted series

Let `E` be a seminormed module over a commutative seminormed ring `R`, and let `u : σ → Rˣ` be
scalars such that each `u i` scales norms in `E` by `r i / s i`:

```text
‖u i • e‖ * s i = ‖e‖ * r i    for all e : E.
```

Then multiplying the coefficient at `t` by `uᵗ = ∏ᵢ u i ^ t i` identifies restricted families at
the polyradius `r` with restricted families at the polyradius `s`, isometrically for the Gauss
norms. For `E = R` and multiplicative units `u i` with `‖u i‖ * s i = r i`, this is the
substitution `X i ↦ u i * X i` of `TauCeti.MvPowerSeries.restrictedRescaleEquiv`.

Taking `s = 1` gives the unweighted coefficient model at a general polyradius: if each `u i`
scales norms in `E` by `r i`, then `a ↦ (t ↦ uᵗ • a t)` is a linear isometry from restricted
families at `r` onto `C₀(WithDiscreteTopology (σ →₀ ℕ), E)`, extending the unit-radius comparison
`TauCeti.MvPowerSeries.IsRestrictedFamily.Gauss.coeffLinearIsometryEquiv`. No such isometry is
constructed without this hypothesis: at an arbitrary real radius no scalar need realise the
weight, and the restricted families then keep their weighted Gauss norm. For ring-valued
coefficients the comparison is `TauCeti.MvPowerSeries.restrictedRescaleCoeffLinearIsometryEquiv`,
defined whenever the radii are norms of multiplicative units.

## Main definitions

* `TauCeti.MvPowerSeries.IsRestrictedFamily.Gauss.rescaleLinearIsometryEquiv`: the isometric
  change of polyradius `Gauss r E ≃ₗᵢ[R] Gauss s E` given by `a ↦ (t ↦ uᵗ • a t)`.
* `TauCeti.MvPowerSeries.IsRestrictedFamily.Gauss.rescaleCoeffLinearIsometryEquiv`: the resulting
  unweighted coefficient model `Gauss r E ≃ₗᵢ[R] C₀(WithDiscreteTopology (σ →₀ ℕ), E)`.
* `TauCeti.MvPowerSeries.restrictedRescaleCoeffLinearIsometryEquiv`: its scalar form for
  restricted power series at radii `r i = ‖u i‖` of multiplicative units.

## Main results

* `TauCeti.MvPowerSeries.isRestrictedFamily_prod_pow_smul_iff`: rescaling converts restrictedness
  at `r` into restrictedness at `s`, by the weighted norm identity
  `TauCeti.MvPowerSeries.norm_prod_pow_smul_mul_prod`.
* `TauCeti.MvPowerSeries.IsRestrictedFamily.Gauss.rescaleLinearIsometryEquiv_one`,
  `TauCeti.MvPowerSeries.IsRestrictedFamily.Gauss.rescaleLinearIsometryEquiv_trans` and
  `TauCeti.MvPowerSeries.IsRestrictedFamily.Gauss.rescaleLinearIsometryEquiv_symm`: the identity,
  composition and inverse laws.
* `TauCeti.MvPowerSeries.ofAddSubgroup_subringLinearEquiv_restrictedRescaleEquiv`: for
  ring-valued coefficients the rescaling is the substitution `X i ↦ u i * X i`.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §5.1.1.
-/

public section

noncomputable section

open scoped ZeroAtInfty

namespace TauCeti.MvPowerSeries

section Family

variable {σ R E : Type*} [SeminormedCommRing R] [SeminormedAddCommGroup E] [Module R E]
  {r s : σ → ℝ}

/-- Multiplying the coefficient at `t` by `uᵗ` converts restrictedness at `r` into restrictedness
at `s`, when each `u i` scales norms in `E` by `r i / s i`. -/
theorem isRestrictedFamily_prod_pow_smul_iff (u : σ → R)
    (hu : ∀ i (e : E), ‖u i • e‖ * s i = ‖e‖ * r i) (a : (σ →₀ ℕ) → E) :
    IsRestrictedFamily s (fun t ↦ (t.prod fun i m ↦ u i ^ m) • a t) ↔ IsRestrictedFamily r a := by
  simp only [isRestrictedFamily_iff]
  exact Filter.tendsto_congr fun t ↦ norm_prod_pow_smul_mul_prod u hu t (a t)

/-- If `u i` scales norms in `E` by `r i / s i`, then its inverse scales them by `s i / r i`. -/
theorem norm_units_inv_smul_mul (u : σ → Rˣ)
    (hu : ∀ i (e : E), ‖(u i : R) • e‖ * s i = ‖e‖ * r i) (i : σ) (e : E) :
    ‖(((u i)⁻¹ : Rˣ) : R) • e‖ * r i = ‖e‖ * s i := by
  simpa [smul_smul] using (hu i ((((u i)⁻¹ : Rˣ) : R) • e)).symm

namespace IsRestrictedFamily.Gauss

variable [IsBoundedSMul R E]

/-- Multiplying the coefficient at `t` by `uᵗ = ∏ᵢ u i ^ t i` changes the polyradius from `r` to
`s`, when each `u i` scales norms in `E` by `r i / s i`. The inverse multiplies by `u⁻ᵗ`. -/
private def rescaleLinearEquiv (u : σ → Rˣ)
    (hu : ∀ i (e : E), ‖(u i : R) • e‖ * s i = ‖e‖ * r i) :
    Gauss r E ≃ₗ[R] Gauss s E where
  toFun a := ofAddSubgroup ⟨fun t ↦ (t.prod fun i m ↦ (u i : R) ^ m) • a t,
    mem_addSubgroup.mpr <| (isRestrictedFamily_prod_pow_smul_iff _ hu _).mpr
      (mem_addSubgroup.mp a.toAddSubgroup.2)⟩
  invFun a := ofAddSubgroup ⟨fun t ↦ (t.prod fun i m ↦ (((u i)⁻¹ : Rˣ) : R) ^ m) • a t,
    mem_addSubgroup.mpr <| (isRestrictedFamily_prod_pow_smul_iff _
      (norm_units_inv_smul_mul u hu) _).mpr (mem_addSubgroup.mp a.toAddSubgroup.2)⟩
  left_inv a := by
    ext t
    simp [smul_smul, ← Finsupp.prod_mul, ← mul_pow]
  right_inv a := by
    ext t
    simp [smul_smul, ← Finsupp.prod_mul, ← mul_pow]
  map_add' a b := by
    ext t
    simp [smul_add]
  map_smul' c a := by
    ext t
    simp [smul_comm c]

/-- The rescaling equivalence multiplies the coefficient at `t` by `uᵗ`. -/
private theorem rescaleLinearEquiv_apply (u : σ → Rˣ)
    (hu : ∀ i (e : E), ‖(u i : R) • e‖ * s i = ‖e‖ * r i) (a : Gauss r E) (t : σ →₀ ℕ) :
    rescaleLinearEquiv u hu a t = (t.prod fun i m ↦ (u i : R) ^ m) • a t := (rfl)

variable [∀ i, Fact (0 < r i)] [∀ i, Fact (0 < s i)]

/-- Rescaling coefficients by `uᵗ` is a linear isometry from restricted families at `r` onto
restricted families at `s`, when each `u i` scales norms in `E` by `r i / s i`. -/
def rescaleLinearIsometryEquiv (u : σ → Rˣ)
    (hu : ∀ i (e : E), ‖(u i : R) • e‖ * s i = ‖e‖ * r i) :
    Gauss r E ≃ₗᵢ[R] Gauss s E where
  toLinearEquiv := rescaleLinearEquiv u hu
  norm_map' a := by
    simp only [norm_eq_iSup]
    congr 1
    funext t
    rw [rescaleLinearEquiv_apply]
    exact norm_prod_pow_smul_mul_prod _ hu t (a t)

/-- The rescaling isometry multiplies the coefficient at `t` by `uᵗ`. -/
@[simp]
theorem rescaleLinearIsometryEquiv_apply (u : σ → Rˣ)
    (hu : ∀ i (e : E), ‖(u i : R) • e‖ * s i = ‖e‖ * r i) (a : Gauss r E) (t : σ →₀ ℕ) :
    rescaleLinearIsometryEquiv u hu a t = (t.prod fun i m ↦ (u i : R) ^ m) • a t := (rfl)

/-- The inverse rescaling isometry multiplies the coefficient at `t` by `u⁻ᵗ`. -/
@[simp]
theorem rescaleLinearIsometryEquiv_symm_apply (u : σ → Rˣ)
    (hu : ∀ i (e : E), ‖(u i : R) • e‖ * s i = ‖e‖ * r i) (a : Gauss s E) (t : σ →₀ ℕ) :
    (rescaleLinearIsometryEquiv u hu).symm a t =
      (t.prod fun i m ↦ (((u i)⁻¹ : Rˣ) : R) ^ m) • a t := (rfl)

/-- Rescaling by the unit scalars is the identity. -/
@[simp]
theorem rescaleLinearIsometryEquiv_one :
    rescaleLinearIsometryEquiv (1 : σ → Rˣ) (fun _ _ ↦ by simp) =
      LinearIsometryEquiv.refl R (Gauss r E) := by
  ext a t
  simp

/-- The inverse of rescaling by `u` is rescaling by the inverse units `(u i)⁻¹`. -/
theorem rescaleLinearIsometryEquiv_symm (u : σ → Rˣ)
    (hu : ∀ i (e : E), ‖(u i : R) • e‖ * s i = ‖e‖ * r i) :
    (rescaleLinearIsometryEquiv u hu).symm =
      rescaleLinearIsometryEquiv u⁻¹ (norm_units_inv_smul_mul u hu) := by
  ext a t
  simp

/-- Rescaling by `u` and then by `v` is rescaling by the products `v i * u i`. -/
theorem rescaleLinearIsometryEquiv_trans {q : σ → ℝ} [∀ i, Fact (0 < q i)] (u v : σ → Rˣ)
    (hu : ∀ i (e : E), ‖(u i : R) • e‖ * s i = ‖e‖ * r i)
    (hv : ∀ i (e : E), ‖(v i : R) • e‖ * q i = ‖e‖ * s i) :
    (rescaleLinearIsometryEquiv u hu).trans (rescaleLinearIsometryEquiv v hv) =
      rescaleLinearIsometryEquiv (v * u) (fun i e ↦ by
        rw [Pi.mul_apply, Units.val_mul, mul_smul, hv, hu]) := by
  ext a t
  simp [smul_smul, ← Finsupp.prod_mul, mul_pow]

/-- Rescaling sends a single coefficient `e` at `t` to the single coefficient `uᵗ • e`. -/
@[simp]
theorem rescaleLinearIsometryEquiv_ofFinsupp_single (u : σ → Rˣ)
    (hu : ∀ i (e : E), ‖(u i : R) • e‖ * s i = ‖e‖ * r i) (t : σ →₀ ℕ) (e : E) :
    rescaleLinearIsometryEquiv u hu (ofFinsupp R r (Finsupp.single t e)) =
      ofFinsupp R s (Finsupp.single t ((t.prod fun i m ↦ (u i : R) ^ m) • e)) := by
  classical
  ext t'
  by_cases h : t = t'
  · subst h
    simp
  · simp [h]

/-- **The unweighted coefficient model at a general polyradius.** If each `u i` scales norms in
`E` by `r i`, then `a ↦ (t ↦ uᵗ • a t)` is a linear isometry from restricted families at `r` onto
the null families on the discrete exponent set. -/
def rescaleCoeffLinearIsometryEquiv (u : σ → Rˣ)
    (hu : ∀ i (e : E), ‖(u i : R) • e‖ = ‖e‖ * r i) :
    Gauss r E ≃ₗᵢ[R] C₀(WithDiscreteTopology (σ →₀ ℕ), E) :=
  (rescaleLinearIsometryEquiv (s := fun _ ↦ 1) u (by simpa using hu)).trans
    (coeffLinearIsometryEquiv R)

/-- The unweighted coefficient model sends a family to its rescaled coefficients `uᵗ • a t`. -/
@[simp]
theorem rescaleCoeffLinearIsometryEquiv_apply (u : σ → Rˣ)
    (hu : ∀ i (e : E), ‖(u i : R) • e‖ = ‖e‖ * r i) (a : Gauss r E) (t : σ →₀ ℕ) :
    rescaleCoeffLinearIsometryEquiv u hu a (.toTopology ⊥ t) =
      (t.prod fun i m ↦ (u i : R) ^ m) • a t := by
  simp [rescaleCoeffLinearIsometryEquiv]

/-- The inverse of the unweighted coefficient model multiplies the coordinate at `t` by `u⁻ᵗ`. -/
@[simp]
theorem rescaleCoeffLinearIsometryEquiv_symm_apply (u : σ → Rˣ)
    (hu : ∀ i (e : E), ‖(u i : R) • e‖ = ‖e‖ * r i) (f : C₀(WithDiscreteTopology (σ →₀ ℕ), E))
    (t : σ →₀ ℕ) :
    (rescaleCoeffLinearIsometryEquiv u hu).symm f t =
      (t.prod fun i m ↦ (((u i)⁻¹ : Rˣ) : R) ^ m) • f (.toTopology ⊥ t) := by
  simp [rescaleCoeffLinearIsometryEquiv]

/-- The unweighted coefficient model sends a single coefficient `e` at `t` to the coordinate
vector at `t` with value `uᵗ • e`. The equality decision is a parameter because the coordinate
vector occurs in the statement. -/
@[simp]
theorem rescaleCoeffLinearIsometryEquiv_ofFinsupp_single
    [DecidableEq (WithDiscreteTopology (σ →₀ ℕ))] (u : σ → Rˣ)
    (hu : ∀ i (e : E), ‖(u i : R) • e‖ = ‖e‖ * r i) (t : σ →₀ ℕ) (e : E) :
    rescaleCoeffLinearIsometryEquiv u hu (ofFinsupp R r (Finsupp.single t e)) =
      ZeroAtInftyContinuousMap.single (.toTopology ⊥ t)
        ((t.prod fun i m ↦ (u i : R) ^ m) • e) := by
  simp [rescaleCoeffLinearIsometryEquiv]

end IsRestrictedFamily.Gauss

end Family

section Scalar

open _root_.MvPowerSeries

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R] {r s : σ → ℝ}
  [∀ i, Fact (0 < r i)]

/-- For ring-valued coefficients, rescaling restricted families is the substitution
`X i ↦ u i * X i` of `TauCeti.MvPowerSeries.restrictedRescaleEquiv`. -/
theorem ofAddSubgroup_subringLinearEquiv_restrictedRescaleEquiv [∀ i, Fact (0 < s i)]
    (u : σ → Rˣ) (hu : ∀ i, IsNormMulUnit (u i : R)) (hrs : ∀ i, ‖(u i : R)‖ * s i = r i)
    (f : IsRestricted.subring (R := R) r) :
    IsRestrictedFamily.Gauss.ofAddSubgroup
        (IsRestrictedFamily.subringLinearEquiv (restrictedRescaleEquiv u hu hrs f)) =
      IsRestrictedFamily.Gauss.rescaleLinearIsometryEquiv u
        (norm_smul_mul_of_isNormMulUnit (fun i ↦ (u i : R)) hu hrs)
        (IsRestrictedFamily.Gauss.ofAddSubgroup (IsRestrictedFamily.subringLinearEquiv f)) := by
  ext t
  simp

/-- **The unweighted coefficient model of restricted series at a general polyradius.** If the
radii `r i = ‖u i‖` are norms of multiplicative units, then `f ↦ (t ↦ uᵗ * coeff t f)` is a linear
isometry from restricted series at `r` onto the null families on the discrete exponent set. It is
the rescaling `TauCeti.MvPowerSeries.restrictedRescaleEquiv` to unit radius followed by the
unit-radius coefficient model `TauCeti.MvPowerSeries.restrictedCoeffLinearIsometryEquiv`. -/
def restrictedRescaleCoeffLinearIsometryEquiv (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hr : ∀ i, ‖(u i : R)‖ = r i) :
    IsRestricted.subring (R := R) r ≃ₗᵢ[R] C₀(WithDiscreteTopology (σ →₀ ℕ), R) :=
  LinearIsometryEquiv.trans
    ⟨(restrictedRescaleEquiv (s := fun _ ↦ 1) u hu (by simpa using hr)).toLinearEquiv,
      fun f ↦ by
        rw [AlgEquiv.toLinearEquiv_apply]
        exact norm_restrictedRescaleEquiv u hu _ f⟩
    restrictedCoeffLinearIsometryEquiv

/-- The unweighted coefficient model of restricted series takes the coefficient at `t` of the
rescaled series, `uᵗ * coeff t f`. -/
@[simp]
theorem restrictedRescaleCoeffLinearIsometryEquiv_apply (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hr : ∀ i, ‖(u i : R)‖ = r i)
    (f : IsRestricted.subring (R := R) r) (t : σ →₀ ℕ) :
    restrictedRescaleCoeffLinearIsometryEquiv u hu hr f (.toTopology ⊥ t) =
      (t.prod fun i m ↦ (u i : R) ^ m) * coeff t (f : _root_.MvPowerSeries σ R) := by
  simp [restrictedRescaleCoeffLinearIsometryEquiv, coeff_rescale]

/-- The inverse unweighted coefficient model builds the restricted series whose coefficient at `t`
is `u⁻ᵗ` times the coordinate at `t`. -/
@[simp]
theorem restrictedRescaleCoeffLinearIsometryEquiv_symm_apply (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hr : ∀ i, ‖(u i : R)‖ = r i)
    (a : C₀(WithDiscreteTopology (σ →₀ ℕ), R)) (t : σ →₀ ℕ) :
    coeff t (((restrictedRescaleCoeffLinearIsometryEquiv u hu hr).symm a :
      IsRestricted.subring (R := R) r) : _root_.MvPowerSeries σ R) =
      (t.prod fun i m ↦ (((u i)⁻¹ : Rˣ) : R) ^ m) * a (.toTopology ⊥ t) := by
  have h := restrictedRescaleCoeffLinearIsometryEquiv_apply u hu hr
    ((restrictedRescaleCoeffLinearIsometryEquiv u hu hr).symm a) t
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  rw [h, ← mul_assoc, ← Finsupp.prod_mul]
  simp [← mul_pow]

/-- The unweighted coefficient model sends the monomial `a Xᵗ` to the coordinate vector at `t`
with value `uᵗ * a`. The equality decision is a parameter because the coordinate vector occurs
in the statement. -/
@[simp]
theorem restrictedRescaleCoeffLinearIsometryEquiv_monomial
    [DecidableEq (WithDiscreteTopology (σ →₀ ℕ))] (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hr : ∀ i, ‖(u i : R)‖ = r i) (t : σ →₀ ℕ) (a : R) :
    restrictedRescaleCoeffLinearIsometryEquiv u hu hr
        (⟨monomial t a, isRestricted_monomial _ t a⟩ : IsRestricted.subring (R := R) r) =
      ZeroAtInftyContinuousMap.single (.toTopology ⊥ t) ((t.prod fun i m ↦ (u i : R) ^ m) * a) := by
  classical
  ext s
  rcases s with ⟨s⟩
  by_cases h : s = t
  · subst s
    simp [ZeroAtInftyContinuousMap.single_apply]
  · simp [coeff_monomial, ZeroAtInftyContinuousMap.single_apply, h]

end Scalar

end TauCeti.MvPowerSeries

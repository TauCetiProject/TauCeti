/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic
public import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.Algebra.Order.Antidiag.Tendsto

/-!
# Restricted series with coefficients in a normed module

Let `E` be a seminormed additive group and `c : σ → ℝ` a polyradius. A family of coefficients
`a : (σ →₀ ℕ) → E` is *restricted* at `c` when its weighted norms tend to zero,

```text
‖a t‖ * ∏ i ∈ t.support, c i ^ t i → 0   along the cofinite filter on σ →₀ ℕ.
```

This is Mathlib's condition `MvPowerSeries.IsRestricted` with coefficients in a group rather than
a ring, and for `E = R` the two agree (`MvPowerSeries.isRestrictedFamily_coeff_iff`).
Restricted families are the coefficients of the module-valued restricted series `∑ₜ a t Xᵗ`,
such as analytic functions on a closed polydisc with values in a Banach module.

The restricted families form an additive subgroup of the coefficient families, and an
`R`-submodule when `E` is a module over a seminormed ring `R` with `‖r • e‖ ≤ ‖r‖ * ‖e‖`. This file
gives their coefficient maps and extensionality, the inclusion of finitely supported families,
and the maps induced coefficientwise by bounded linear maps `‖φ e‖ ≤ C * ‖e‖`. When `E` is
ultrametric, restricted series over `R` act on restricted families by convolution,

```text
(f • a) t = ∑_{p + q = t} f_p • a_q,
```

making the restricted families a module over the ring of restricted series. The convolution
`MvPowerSeries.convSMul` is defined for all formal series and all coefficient families,
and its module laws hold there without any norm.

The variables may be arbitrary, the coefficient ring need not be commutative, and no
completeness is assumed. Without variables, the restricted families are the module `E` itself
(`TauCeti.MvPowerSeries.IsRestrictedFamily.isEmptyLinearEquiv`); with `E = R`, they are the ring
of restricted series as a module over itself
(`TauCeti.MvPowerSeries.IsRestrictedFamily.subringLinearEquiv`).
-/

public section

open Finset

namespace MvPowerSeries

variable {σ R E : Type*}

section Convolution

variable [Semiring R] [AddCommMonoid E] [Module R E]

/-- The convolution action of a formal power series `f` on a coefficient family `a`: the
coefficient of `f • a` at `t` is `∑_{p + q = t} f_p • a_q`. For `E = R` this is the coefficient
family of the product (`MvPowerSeries.convSMul_coeff`). -/
noncomputable def convSMul (f : MvPowerSeries σ R) (a : (σ →₀ ℕ) → E) : (σ →₀ ℕ) → E :=
  letI := Classical.decEq σ
  fun t ↦ ∑ p ∈ antidiagonal t, coeff p.1 f • a p.2

theorem convSMul_apply [DecidableEq σ] (f : MvPowerSeries σ R) (a : (σ →₀ ℕ) → E)
    (t : σ →₀ ℕ) : convSMul f a t = ∑ p ∈ antidiagonal t, coeff p.1 f • a p.2 := by
  rw [convSMul, Subsingleton.elim (Classical.decEq σ) ‹DecidableEq σ›]

@[simp]
theorem zero_convSMul (a : (σ →₀ ℕ) → E) : convSMul (0 : MvPowerSeries σ R) a = 0 := by
  classical
  ext t
  simp [convSMul_apply]

@[simp]
theorem convSMul_zero (f : MvPowerSeries σ R) : convSMul f (0 : (σ →₀ ℕ) → E) = 0 := by
  classical
  ext t
  simp [convSMul_apply]

theorem add_convSMul (f g : MvPowerSeries σ R) (a : (σ →₀ ℕ) → E) :
    convSMul (f + g) a = convSMul f a + convSMul g a := by
  classical
  ext t
  simp [convSMul_apply, add_smul, Finset.sum_add_distrib]

theorem convSMul_add (f : MvPowerSeries σ R) (a b : (σ →₀ ℕ) → E) :
    convSMul f (a + b) = convSMul f a + convSMul f b := by
  classical
  ext t
  simp [convSMul_apply, smul_add, Finset.sum_add_distrib]

/-- A constant series acts on coefficient families through its constant. -/
@[simp]
theorem C_convSMul (r : R) (a : (σ →₀ ℕ) → E) : convSMul (C r : MvPowerSeries σ R) a = r • a := by
  classical
  ext t
  rw [convSMul_apply, Finset.sum_eq_single_of_mem (0, t) (by simp)]
  · simp
  · rintro ⟨p, q⟩ hpq hne
    have hp : p ≠ 0 := by
      rintro rfl
      exact hne (by simpa using hpq)
    simp [coeff_C, hp]

@[simp]
theorem one_convSMul (a : (σ →₀ ℕ) → E) : convSMul (1 : MvPowerSeries σ R) a = a := by
  simpa using C_convSMul (σ := σ) (1 : R) a

theorem mul_convSMul (f g : MvPowerSeries σ R) (a : (σ →₀ ℕ) → E) :
    convSMul (f * g) a = convSMul f (convSMul g a) := by
  classical
  ext t
  simp only [convSMul_apply, coeff_mul, Finset.sum_smul, Finset.smul_sum, mul_smul,
    Finset.sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ ↦ ⟨(k, l + j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ ↦ ⟨(i + k, l), (i, k)⟩) <;> aesop (add simp [add_assoc])

/-- For coefficients in the ring itself, convolution with the coefficients of `g` gives the
coefficients of the product `f * g`. -/
theorem convSMul_coeff (f g : MvPowerSeries σ R) :
    convSMul f (fun t ↦ coeff t g) = fun t ↦ coeff t (f * g) := by
  classical
  ext t
  simp [convSMul_apply, coeff_mul]

end Convolution

end MvPowerSeries

namespace TauCeti.MvPowerSeries

open Filter Finset _root_.MvPowerSeries
open scoped Topology

variable {σ R E F G : Type*}

section Predicate

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] {c : σ → ℝ}

/-- A family of coefficients `a : (σ →₀ ℕ) → E` in a seminormed group is restricted at the
polyradius `c` if `‖a t‖ * ∏ i ∈ t.support, c i ^ t i → 0` along the cofinite filter. These are
the coefficient families of restricted power series with coefficients in `E`. -/
def IsRestrictedFamily (c : σ → ℝ) (a : (σ →₀ ℕ) → E) : Prop :=
  Tendsto (fun t : σ →₀ ℕ ↦ ‖a t‖ * t.prod (c · ^ ·)) cofinite (𝓝 0)

/-- Restrictedness only depends on the absolute values of the radii. -/
@[simp]
theorem isRestrictedFamily_abs_iff (c : σ → ℝ) (a : (σ →₀ ℕ) → E) :
    IsRestrictedFamily |c| a ↔ IsRestrictedFamily c a := by
  simp [IsRestrictedFamily, NormedAddGroup.tendsto_nhds_zero, Finsupp.prod]

/-- A family whose coefficient norms are bounded by a constant multiple of those of a restricted
family is restricted. -/
theorem IsRestrictedFamily.of_norm_le {a : (σ →₀ ℕ) → E} (ha : IsRestrictedFamily c a)
    {b : (σ →₀ ℕ) → F} {C : ℝ} (hb : ∀ t, ‖b t‖ ≤ C * ‖a t‖) : IsRestrictedFamily c b := by
  rw [← isRestrictedFamily_abs_iff, IsRestrictedFamily] at *
  refine tendsto_const_nhds.squeeze (mul_zero C ▸ ha.const_mul C)
    (fun t ↦ mul_nonneg (norm_nonneg _) (prod_abs_pow_nonneg t)) fun t ↦ ?_
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hb t) (prod_abs_pow_nonneg t)

/-- Mapping the coefficients of a restricted family by a function bounded by a constant multiple
of the norm gives a restricted family. -/
theorem IsRestrictedFamily.map {a : (σ →₀ ℕ) → E} (ha : IsRestrictedFamily c a) (φ : E → F)
    {C : ℝ} (hφ : ∀ e, ‖φ e‖ ≤ C * ‖e‖) : IsRestrictedFamily c (φ ∘ a) :=
  ha.of_norm_le fun t ↦ hφ (a t)

theorem isRestrictedFamily_zero (c : σ → ℝ) : IsRestrictedFamily c (0 : (σ →₀ ℕ) → E) := by
  simpa [IsRestrictedFamily] using tendsto_const_nhds

/-- A family with finitely many nonzero coefficients is restricted at every polyradius. -/
theorem isRestrictedFamily_of_finite_support (c : σ → ℝ) {a : (σ →₀ ℕ) → E}
    (ha : (Function.support a).Finite) : IsRestrictedFamily c a :=
  tendsto_nhds_of_eventually_eq <| eventually_cofinite.mpr <| ha.subset fun t ht ↦
    Function.mem_support.mpr fun h0 ↦ ht (by simp [h0])

/-- A family with a single nonzero coefficient is restricted at every polyradius. -/
theorem isRestrictedFamily_single [DecidableEq σ] (c : σ → ℝ) (t : σ →₀ ℕ) (e : E) :
    IsRestrictedFamily c (Pi.single t e) :=
  isRestrictedFamily_of_finite_support c <| (Set.finite_singleton t).subset
    Pi.support_single_subset

theorem IsRestrictedFamily.add {a b : (σ →₀ ℕ) → E} (ha : IsRestrictedFamily c a)
    (hb : IsRestrictedFamily c b) : IsRestrictedFamily c (a + b) := by
  rw [← isRestrictedFamily_abs_iff, IsRestrictedFamily] at *
  refine tendsto_const_nhds.squeeze (add_zero (0 : ℝ) ▸ ha.add hb)
    (fun t ↦ mul_nonneg (norm_nonneg _) (prod_abs_pow_nonneg t)) fun t ↦ ?_
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (prod_abs_pow_nonneg t)

theorem IsRestrictedFamily.neg {a : (σ →₀ ℕ) → E} (ha : IsRestrictedFamily c a) :
    IsRestrictedFamily c (-a) :=
  ha.of_norm_le (C := 1) fun t ↦ by simp

/-- Scalar multiples of restricted families are restricted. -/
theorem IsRestrictedFamily.smul [SeminormedRing R] [Module R E] [IsBoundedSMul R E] (r : R)
    {a : (σ →₀ ℕ) → E} (ha : IsRestrictedFamily c a) : IsRestrictedFamily c (r • a) :=
  ha.of_norm_le fun t ↦ norm_smul_le r (a t)

end Predicate

section Submodule

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
  {c : σ → ℝ}

namespace IsRestrictedFamily

variable (E) in
/-- The restricted families at the polyradius `c`, as an additive subgroup of all coefficient
families. -/
protected def addSubgroup (c : σ → ℝ) : AddSubgroup ((σ →₀ ℕ) → E) where
  carrier := {a | IsRestrictedFamily c a}
  zero_mem' := isRestrictedFamily_zero c
  add_mem' := IsRestrictedFamily.add
  neg_mem' := IsRestrictedFamily.neg

@[simp]
theorem mem_addSubgroup {a : (σ →₀ ℕ) → E} :
    a ∈ IsRestrictedFamily.addSubgroup E c ↔ IsRestrictedFamily c a :=
  Iff.rfl

/-- Two restricted families with the same coefficients are equal. -/
@[ext]
theorem ext {a b : IsRestrictedFamily.addSubgroup E c}
    (h : ∀ t, (a : (σ →₀ ℕ) → E) t = (b : (σ →₀ ℕ) → E) t) : a = b :=
  Subtype.ext (funext h)

variable [SeminormedRing R] [Module R E] [IsBoundedSMul R E] [Module R F] [IsBoundedSMul R F]
  [Module R G] [IsBoundedSMul R G]

variable (R E) in
/-- The restricted families at the polyradius `c`, as an `R`-submodule of all coefficient
families. Its underlying additive subgroup is
`TauCeti.MvPowerSeries.IsRestrictedFamily.addSubgroup`, which carries the resulting module
structure. -/
protected def submodule (c : σ → ℝ) : Submodule R ((σ →₀ ℕ) → E) :=
  { IsRestrictedFamily.addSubgroup E c with smul_mem' := fun r _ ha ↦ ha.smul r }

@[simp]
theorem toAddSubgroup_submodule :
    (IsRestrictedFamily.submodule R E c).toAddSubgroup = IsRestrictedFamily.addSubgroup E c :=
  (rfl)

instance : Module R (IsRestrictedFamily.addSubgroup E c) :=
  inferInstanceAs <| Module R (IsRestrictedFamily.submodule R E c)

@[simp]
theorem coe_smul (r : R) (a : IsRestrictedFamily.addSubgroup E c) :
    ((r • a : IsRestrictedFamily.addSubgroup E c) : (σ →₀ ℕ) → E) = r • (a : (σ →₀ ℕ) → E) :=
  (rfl)

variable (R) in
/-- The coefficient of a restricted family at the exponent `t`, as an `R`-linear map. -/
def coeff (t : σ →₀ ℕ) : IsRestrictedFamily.addSubgroup E c →ₗ[R] E where
  toFun a := (a : (σ →₀ ℕ) → E) t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coeff_apply (t : σ →₀ ℕ) (a : IsRestrictedFamily.addSubgroup E c) :
    coeff R t a = (a : (σ →₀ ℕ) → E) t :=
  (rfl)

variable (R c) in
/-- The inclusion of the finitely supported coefficient families into the restricted families. -/
noncomputable def ofFinsupp : ((σ →₀ ℕ) →₀ E) →ₗ[R] IsRestrictedFamily.addSubgroup E c :=
  LinearMap.codRestrict (IsRestrictedFamily.submodule R E c) (Finsupp.lcoeFun)
    fun a ↦ isRestrictedFamily_of_finite_support c a.hasFiniteSupport

@[simp]
theorem coe_ofFinsupp (a : (σ →₀ ℕ) →₀ E) :
    (ofFinsupp R c a : (σ →₀ ℕ) → E) = a :=
  (rfl)

theorem ofFinsupp_injective : Function.Injective (ofFinsupp (σ := σ) (E := E) R c) :=
  fun _ _ h ↦ DFunLike.coe_injective (congrArg Subtype.val h)

/-- The family with the single coefficient `e` at `t` is the image of `Finsupp.single t e`. -/
theorem coe_ofFinsupp_single [DecidableEq σ] (t : σ →₀ ℕ) (e : E) :
    (ofFinsupp R c (Finsupp.single t e) : (σ →₀ ℕ) → E) = Pi.single t e := by
  simp [Finsupp.single_eq_pi_single]

/-- A bounded `R`-linear map `φ : E → F`, `‖φ e‖ ≤ C * ‖e‖`, maps restricted families to
restricted families coefficientwise. -/
def mapLinearMap (φ : E →ₗ[R] F) {C : ℝ} (hφ : ∀ e, ‖φ e‖ ≤ C * ‖e‖) :
    IsRestrictedFamily.addSubgroup E c →ₗ[R] IsRestrictedFamily.addSubgroup F c :=
  LinearMap.codRestrict (IsRestrictedFamily.submodule R F c)
    ((LinearMap.compLeft φ (σ →₀ ℕ)).comp (IsRestrictedFamily.submodule R E c).subtype)
    fun a ↦ a.2.map φ hφ

@[simp]
theorem coe_mapLinearMap (φ : E →ₗ[R] F) {C : ℝ} (hφ : ∀ e, ‖φ e‖ ≤ C * ‖e‖)
    (a : IsRestrictedFamily.addSubgroup E c) :
    (mapLinearMap φ hφ a : (σ →₀ ℕ) → F) = φ ∘ (a : (σ →₀ ℕ) → E) :=
  (rfl)

theorem coeff_mapLinearMap (φ : E →ₗ[R] F) {C : ℝ} (hφ : ∀ e, ‖φ e‖ ≤ C * ‖e‖) (t : σ →₀ ℕ)
    (a : IsRestrictedFamily.addSubgroup E c) :
    coeff R t (mapLinearMap φ hφ a) = φ (coeff R t a) :=
  (rfl)

@[simp]
theorem mapLinearMap_id {C : ℝ} (h : ∀ e : E, ‖LinearMap.id (R := R) e‖ ≤ C * ‖e‖) :
    mapLinearMap (c := c) LinearMap.id h = LinearMap.id :=
  (rfl)

theorem mapLinearMap_comp (ψ : F →ₗ[R] G) (φ : E →ₗ[R] F) {C₁ C₂ C₃ : ℝ}
    (hψ : ∀ e, ‖ψ e‖ ≤ C₁ * ‖e‖) (hφ : ∀ e, ‖φ e‖ ≤ C₂ * ‖e‖)
    (hψφ : ∀ e, ‖(ψ ∘ₗ φ) e‖ ≤ C₃ * ‖e‖) :
    mapLinearMap (c := c) (ψ ∘ₗ φ) hψφ = (mapLinearMap ψ hψ).comp (mapLinearMap φ hφ) :=
  (rfl)

theorem mapLinearMap_injective (φ : E →ₗ[R] F) {C : ℝ} (hφ : ∀ e, ‖φ e‖ ≤ C * ‖e‖)
    (hinj : Function.Injective φ) :
    Function.Injective (mapLinearMap (c := c) φ hφ) := fun _ _ h ↦
  ext fun t ↦ hinj (congrFun (congrArg Subtype.val h) t)

theorem mapLinearMap_ofFinsupp (φ : E →ₗ[R] F) {C : ℝ} (hφ : ∀ e, ‖φ e‖ ≤ C * ‖e‖)
    (a : (σ →₀ ℕ) →₀ E) :
    mapLinearMap φ hφ (ofFinsupp R c a) = ofFinsupp R c (Finsupp.mapRange.linearMap φ a) :=
  ext fun _ ↦ rfl

variable (R E c) in
/-- Without variables, a restricted family is determined by its constant coefficient, which can
be arbitrary: the restricted families are the coefficient module itself. -/
def isEmptyLinearEquiv [IsEmpty σ] : IsRestrictedFamily.addSubgroup E c ≃ₗ[R] E where
  toLinearMap := coeff R 0
  invFun e := ⟨fun _ ↦ e, isRestrictedFamily_of_finite_support c (Set.toFinite _)⟩
  left_inv a := ext fun t ↦ by rw [Subsingleton.elim t 0]; rfl
  right_inv _ := rfl

@[simp]
theorem isEmptyLinearEquiv_apply [IsEmpty σ] (a : IsRestrictedFamily.addSubgroup E c) :
    isEmptyLinearEquiv R E c a = (a : (σ →₀ ℕ) → E) 0 :=
  (rfl)

end IsRestrictedFamily

end Submodule

section RestrictedConvolution

variable [NormedRing R] [SeminormedAddCommGroup E] [IsUltrametricDist E] [Module R E]
  [IsBoundedSMul R E] {c : σ → ℝ}

/-- Over an ultrametric coefficient module, the convolution of a restricted series with a
restricted family is restricted. -/
theorem IsRestrictedFamily.convSMul {f : MvPowerSeries σ R} (hf : IsRestricted c f)
    {a : (σ →₀ ℕ) → E} (ha : IsRestrictedFamily c a) :
    IsRestrictedFamily c (MvPowerSeries.convSMul f a) := by
  classical
  rw [← isRestrictedFamily_abs_iff, IsRestrictedFamily] at *
  rw [← isRestricted_abs_iff, IsRestricted] at hf
  refine .squeeze tendsto_const_nhds (HasAntidiagonal.tendsto_sup'_antidiagonal_cofinite
    (tendsto_mul_cofinite_nhds_zero hf ha))
    (fun t ↦ mul_nonneg (norm_nonneg _) (prod_abs_pow_nonneg t)) fun t ↦ ?_
  have ht : 0 ≤ t.prod (|c| · ^ ·) := prod_abs_pow_nonneg t
  rw [convSMul_apply]
  grw [(HasAntidiagonal.nonempty_antidiagonal t).norm_sum_le_sup'_norm, Finset.sup'_mul₀ ht]
  refine Finset.sup'_mono_fun fun p hp ↦ ?_
  rw [← mem_antidiagonal.mp hp, prod_pow_add, mul_mul_mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_smul_le _ _)
    (mul_nonneg (prod_abs_pow_nonneg _) (prod_abs_pow_nonneg _))

namespace IsRestrictedFamily

variable [IsUltrametricDist R]

/-- Restricted series act on restricted families by convolution. -/
noncomputable instance : SMul (IsRestricted.subring (R := R) c)
    (IsRestrictedFamily.addSubgroup E c) where
  smul f a := ⟨MvPowerSeries.convSMul (f : MvPowerSeries σ R) a,
    mem_addSubgroup.mpr (IsRestrictedFamily.convSMul f.2 (mem_addSubgroup.mp a.2))⟩

@[simp]
theorem coe_isRestrictedSubring_smul (f : IsRestricted.subring (R := R) c)
    (a : IsRestrictedFamily.addSubgroup E c) :
    ((f • a : IsRestrictedFamily.addSubgroup E c) : (σ →₀ ℕ) → E) =
      MvPowerSeries.convSMul (f : MvPowerSeries σ R) a :=
  (rfl)

/-- The restricted families form a module over the ring of restricted series. -/
noncomputable instance : Module (IsRestricted.subring (R := R) c)
    (IsRestrictedFamily.addSubgroup E c) where
  one_smul _ := Subtype.ext (one_convSMul _)
  mul_smul _ _ _ := Subtype.ext (mul_convSMul _ _ _)
  smul_zero _ := Subtype.ext (convSMul_zero _)
  smul_add _ _ _ := Subtype.ext (convSMul_add _ _ _)
  add_smul _ _ _ := Subtype.ext (add_convSMul _ _ _)
  zero_smul _ := Subtype.ext (zero_convSMul _)

/-- For coefficients in the ring itself, the restricted families are the ring of restricted
series, regarded as a module over itself. -/
noncomputable def subringLinearEquiv :
    IsRestricted.subring (R := R) c ≃ₗ[IsRestricted.subring (R := R) c]
      IsRestrictedFamily.addSubgroup R c where
  toFun f := ⟨fun t ↦ MvPowerSeries.coeff t (f : MvPowerSeries σ R), f.2⟩
  invFun a := ⟨(a : (σ →₀ ℕ) → R), a.2⟩
  map_add' _ _ := rfl
  map_smul' f g := ext fun t ↦ congrFun (convSMul_coeff (f : MvPowerSeries σ R) g).symm t
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_subringLinearEquiv (f : IsRestricted.subring (R := R) c) :
    (subringLinearEquiv f : (σ →₀ ℕ) → R) =
      fun t ↦ MvPowerSeries.coeff t (f : MvPowerSeries σ R) :=
  (rfl)

end IsRestrictedFamily

end RestrictedConvolution

section CommRing

variable [NormedCommRing R] [IsUltrametricDist R] [SeminormedAddCommGroup E] [IsUltrametricDist E]
  [Module R E] [IsBoundedSMul R E] {c : σ → ℝ}

/-- Over a commutative coefficient ring, the action of a constant series is scalar
multiplication by its constant. -/
instance :
    IsScalarTower R (IsRestricted.subring (R := R) c) (IsRestrictedFamily.addSubgroup E c) where
  smul_assoc r f a := Subtype.ext <| by
    rw [Algebra.smul_def, mul_smul]
    exact C_convSMul r _

end CommRing

end TauCeti.MvPowerSeries

namespace MvPowerSeries

open TauCeti.MvPowerSeries

/-- For coefficients in a normed ring, a family is restricted exactly when the power series with
these coefficients is restricted in Mathlib's sense. -/
theorem isRestrictedFamily_coeff_iff {σ R : Type*} [NormedRing R] {c : σ → ℝ}
    (f : MvPowerSeries σ R) : IsRestrictedFamily c (fun t ↦ coeff t f) ↔ IsRestricted c f :=
  Iff.rfl

end MvPowerSeries

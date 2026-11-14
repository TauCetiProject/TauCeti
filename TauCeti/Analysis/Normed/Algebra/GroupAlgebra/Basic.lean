/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import TauCeti.MeasureTheory.Group.Convolution.Pointwise
public import TauCeti.MeasureTheory.Group.Convolution.Star

/-!
# The `L¹` group convolution Banach `⋆`-algebra

For a topological group `G` equipped with a left-invariant Borel measure `μ` that is locally finite
and inner regular for compact sets of finite measure (in particular, any regular left Haar measure
on a locally compact group, without assuming σ-compactness or second countability) and an `RCLike`
scalar field `𝕜` (such as `ℝ` or `ℂ`), this file equips `Lp 𝕜 1 μ` with its group convolution
algebra structure.

Because `Lp 𝕜 1 μ` already carries the pointwise conjugation `Star` instance, we package elements
of the group algebra in a one-field wrapper `TauCeti.L1GroupAlgebra 𝕜 μ` with projections
`L1GroupAlgebra.toConv` and `L1GroupAlgebra.ofConv`, matching
`TauCeti.CStarAction.ConvolutionAlgebra`:

* **Banach space structure:** `L1GroupAlgebra 𝕜 μ` inherits `NormedAddCommGroup`, `NormedSpace 𝕜`,
  and `CompleteSpace` along `L1GroupAlgebra.linearIsometryEquiv 𝕜 𝕜 μ`.
* **Convolution product (`NonUnitalNormedRing`):** Multiplication is defined via the operator-valued
  Bochner integral `MeasureTheory.Lp.convolutionL μ 1 ENNReal.one_ne_top`, giving associativity,
  submultiplicativity `‖f * g‖ ≤ ‖f‖ * ‖g‖`, and multiplicativity of the Haar integral
  `L1GroupAlgebra.integralNonUnitalAlgHom` without any Fubini or Hausdorff assumption.
* **Pointwise convolution formulas:** When `G` is locally compact Hausdorff and `μ` is a regular
  left Haar measure, `(f * g).ofConv` is represented `μ`-almost everywhere both by the left-hand
  formula `x ↦ ∫ y, f.ofConv y * g.ofConv (y⁻¹ * x) ∂μ` (`L1GroupAlgebra.ofConv_mul_ae_eq`) and by
  the modular right-hand formula
  `x ↦ ∫ z, (Measure.modularCharacter z : ℝ) • (f.ofConv (x * z⁻¹) * g.ofConv z) ∂μ`
  (`L1GroupAlgebra.ofConv_mul_ae_eq_modularCharacter`).
* **Modular involution (`StarRing`, `NormedStarGroup`, `StarModule 𝕜`):** On a locally compact group
  with regular left Haar measure `μ`, `star f` is `Lp.modularInversion μ 1 𝕜 (star f.ofConv)`,
  represented `μ`-almost everywhere by `x ↦ (Measure.modularCharacter x : ℝ) • star (f.ofConv x⁻¹)`.
  It is an isometric conjugate-linear anti-automorphism of `L1GroupAlgebra 𝕜 μ` intertwining left
  and right translations (`L1GroupAlgebra.star_leftTranslation`,
  `L1GroupAlgebra.star_rightTranslation`) and making Haar integration a `⋆`-homomorphism
  (`L1GroupAlgebra.integralStarAlgHom`).
* **Comparison of regular Haar normalizations:** Any two regular left Haar measures `μ` and `ν` on
  `G` yield a canonical isometric `⋆`-algebra isomorphism
  `L1GroupAlgebra.haarStarAlgEquiv 𝕜 μ ν : L1GroupAlgebra 𝕜 μ ≃⋆ₐ[𝕜] L1GroupAlgebra 𝕜 ν`
  preserving norm and Haar integral and intertwining left and right translations.

## References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016), §2.5.
* E. Hewitt and K. A. Ross, *Abstract Harmonic Analysis*, Vol. I, 2nd ed., Springer (1979), §20.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, Clarendon Press (2000), §3.3.
-/

public section

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace TauCeti

/-- The `L¹` group convolution algebra of a group `G` with respect to a measure `μ` and scalars `𝕜`,
whose underlying Banach space is `Lp 𝕜 1 μ` (`G →₁[μ] 𝕜`), equipped with convolution as
multiplication and the modular involution `x ↦ c(x) • star (f x⁻¹)` as `star`. Use
`L1GroupAlgebra.toConv` and `L1GroupAlgebra.ofConv` to pass to and from `Lp 𝕜 1 μ`, whose own `star`
is pointwise conjugation. -/
structure L1GroupAlgebra {G : Type*} [MeasurableSpace G] (𝕜 : Type*) [NormedAddCommGroup 𝕜]
    (μ : Measure G) where
  /-- Regard an `L¹` equivalence class as an element of the group convolution algebra. -/
  toConv ::
  /-- The underlying `L¹` equivalence class of an element of the group convolution algebra. -/
  ofConv : Lp 𝕜 1 μ

namespace L1GroupAlgebra

/-! ### Underlying Banach space structure -/

section BanachSpace

variable {G 𝕜 : Type*} [MeasurableSpace G] [NormedAddCommGroup 𝕜] {μ : Measure G}

@[simp]
theorem ofConv_toConv (f : Lp 𝕜 1 μ) : (toConv f : L1GroupAlgebra 𝕜 μ).ofConv = f :=
  (rfl)

@[simp]
theorem toConv_ofConv (f : L1GroupAlgebra 𝕜 μ) : toConv f.ofConv = f :=
  (rfl)

theorem ofConv_injective : Function.Injective (ofConv : L1GroupAlgebra 𝕜 μ → Lp 𝕜 1 μ) :=
  fun f g h ↦ by rw [← toConv_ofConv f, h, toConv_ofConv]

theorem toConv_injective : Function.Injective (toConv : Lp 𝕜 1 μ → L1GroupAlgebra 𝕜 μ) :=
  fun f g h ↦ by rw [← ofConv_toConv (𝕜 := 𝕜) (μ := μ) f, h, ofConv_toConv]

@[ext]
theorem ext {f g : L1GroupAlgebra 𝕜 μ} (h : f.ofConv = g.ofConv) : f = g :=
  ofConv_injective h

variable (𝕜 μ) in
/-- `L1GroupAlgebra.ofConv` and `L1GroupAlgebra.toConv` as an equivalence with `Lp 𝕜 1 μ`. -/
def equiv : L1GroupAlgebra 𝕜 μ ≃ Lp 𝕜 1 μ where
  toFun := ofConv
  invFun := toConv
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem equiv_apply (f : L1GroupAlgebra 𝕜 μ) : equiv 𝕜 μ f = f.ofConv :=
  (rfl)

@[simp]
theorem equiv_symm_apply (f : Lp 𝕜 1 μ) : (equiv 𝕜 μ).symm f = toConv f :=
  (rfl)

instance : AddCommGroup (L1GroupAlgebra 𝕜 μ) :=
  (equiv 𝕜 μ).addCommGroup

variable (𝕜 μ) in
/-- `L1GroupAlgebra.ofConv` as an additive equivalence with `Lp 𝕜 1 μ`. -/
def addEquiv : L1GroupAlgebra 𝕜 μ ≃+ Lp 𝕜 1 μ where
  __ := equiv 𝕜 μ
  map_add' _ _ := rfl

@[simp]
theorem addEquiv_apply (f : L1GroupAlgebra 𝕜 μ) : addEquiv 𝕜 μ f = f.ofConv :=
  (rfl)

@[simp]
theorem addEquiv_symm_apply (f : Lp 𝕜 1 μ) : (addEquiv 𝕜 μ).symm f = toConv f :=
  (rfl)

instance : NormedAddCommGroup (L1GroupAlgebra 𝕜 μ) :=
  NormedAddCommGroup.induced (L1GroupAlgebra 𝕜 μ) (Lp 𝕜 1 μ) (addEquiv 𝕜 μ)
    (addEquiv 𝕜 μ).injective

theorem norm_def (f : L1GroupAlgebra 𝕜 μ) : ‖f‖ = ‖f.ofConv‖ :=
  (rfl)

@[simp]
theorem norm_ofConv (f : L1GroupAlgebra 𝕜 μ) : ‖f.ofConv‖ = ‖f‖ :=
  (rfl)

@[simp]
theorem norm_toConv (f : Lp 𝕜 1 μ) : ‖(toConv f : L1GroupAlgebra 𝕜 μ)‖ = ‖f‖ :=
  (rfl)

/-- The `L¹` norm of `f : L1GroupAlgebra 𝕜 μ` is the Haar integral of `‖f.ofConv ·‖`. -/
theorem norm_eq_integral_norm (f : L1GroupAlgebra 𝕜 μ) :
    ‖f‖ = ∫ x, ‖f.ofConv x‖ ∂μ :=
  L1.norm_eq_integral_norm f.ofConv

theorem isometry_addEquiv : Isometry (addEquiv 𝕜 μ) :=
  AddMonoidHomClass.isometry_of_norm _ fun _ ↦ rfl

@[fun_prop]
theorem continuous_ofConv : Continuous (ofConv : L1GroupAlgebra 𝕜 μ → Lp 𝕜 1 μ) :=
  isometry_addEquiv.continuous

@[fun_prop]
theorem continuous_toConv : Continuous (toConv : Lp 𝕜 1 μ → L1GroupAlgebra 𝕜 μ) :=
  (AddMonoidHomClass.isometry_of_norm (addEquiv 𝕜 μ).symm fun _ ↦ rfl).continuous

instance [CompleteSpace 𝕜] : CompleteSpace (L1GroupAlgebra 𝕜 μ) :=
  (completeSpace_congr (e := (addEquiv 𝕜 μ).toEquiv)
    isometry_addEquiv.isUniformEmbedding).mpr inferInstance

@[simp]
theorem ofConv_zero : (0 : L1GroupAlgebra 𝕜 μ).ofConv = 0 :=
  (rfl)

@[simp]
theorem ofConv_add (f g : L1GroupAlgebra 𝕜 μ) : (f + g).ofConv = f.ofConv + g.ofConv :=
  (rfl)

@[simp]
theorem ofConv_neg (f : L1GroupAlgebra 𝕜 μ) : (-f).ofConv = -f.ofConv :=
  (rfl)

@[simp]
theorem ofConv_sub (f g : L1GroupAlgebra 𝕜 μ) : (f - g).ofConv = f.ofConv - g.ofConv :=
  (rfl)

@[simp]
theorem toConv_zero : (toConv 0 : L1GroupAlgebra 𝕜 μ) = 0 :=
  (rfl)

@[simp]
theorem toConv_add (f g : Lp 𝕜 1 μ) :
    (toConv (f + g) : L1GroupAlgebra 𝕜 μ) = toConv f + toConv g :=
  (rfl)

@[simp]
theorem toConv_neg (f : Lp 𝕜 1 μ) : (toConv (-f) : L1GroupAlgebra 𝕜 μ) = -toConv f :=
  (rfl)

@[simp]
theorem toConv_sub (f g : Lp 𝕜 1 μ) :
    (toConv (f - g) : L1GroupAlgebra 𝕜 μ) = toConv f - toConv g :=
  (rfl)

/-- Package an integrable function `f : G → 𝕜` as an element of `L1GroupAlgebra 𝕜 μ`. -/
def ofIntegrable {f : G → 𝕜} (hf : Integrable f μ) : L1GroupAlgebra 𝕜 μ :=
  toConv (hf.toL1 f)

@[simp]
theorem ofConv_ofIntegrable {f : G → 𝕜} (hf : Integrable f μ) :
    (ofIntegrable hf).ofConv = hf.toL1 f :=
  (rfl)

theorem coeFn_ofConv_ofIntegrable {f : G → 𝕜} (hf : Integrable f μ) :
    (ofIntegrable hf).ofConv =ᵐ[μ] f :=
  hf.coeFn_toL1

end BanachSpace

section NormedSpace

variable {G R S 𝕜 : Type*} [MeasurableSpace G] {μ : Measure G}

instance [NormedRing R] [NormedAddCommGroup 𝕜] [Module R 𝕜] [IsBoundedSMul R 𝕜] :
    Module R (L1GroupAlgebra 𝕜 μ) :=
  (addEquiv 𝕜 μ).module R

@[simp]
theorem ofConv_smul [NormedRing R] [NormedAddCommGroup 𝕜] [Module R 𝕜] [IsBoundedSMul R 𝕜]
    (c : R) (f : L1GroupAlgebra 𝕜 μ) : (c • f).ofConv = c • f.ofConv :=
  (rfl)

@[simp]
theorem toConv_smul [NormedRing R] [NormedAddCommGroup 𝕜] [Module R 𝕜] [IsBoundedSMul R 𝕜]
    (c : R) (f : Lp 𝕜 1 μ) : (toConv (c • f) : L1GroupAlgebra 𝕜 μ) = c • toConv f :=
  (rfl)

instance [NormedRing R] [NormedRing S] [NormedAddCommGroup 𝕜] [Module R 𝕜] [Module S 𝕜]
    [IsBoundedSMul R 𝕜] [IsBoundedSMul S 𝕜] [SMul R S] [IsScalarTower R S 𝕜] :
    IsScalarTower R S (L1GroupAlgebra 𝕜 μ) where
  smul_assoc r s f := by ext1; exact smul_assoc r s f.ofConv

instance [NormedRing R] [NormedRing S] [NormedAddCommGroup 𝕜] [Module R 𝕜] [Module S 𝕜]
    [IsBoundedSMul R 𝕜] [IsBoundedSMul S 𝕜] [SMulCommClass R S 𝕜] :
    SMulCommClass R S (L1GroupAlgebra 𝕜 μ) where
  smul_comm r s f := by ext1; exact smul_comm r s f.ofConv

variable (R 𝕜 μ) in
/-- `L1GroupAlgebra.ofConv` as a linear isometry equivalence with `Lp 𝕜 1 μ`. -/
def linearIsometryEquiv [NormedField R] [NormedAddCommGroup 𝕜] [NormedSpace R 𝕜] :
    L1GroupAlgebra 𝕜 μ ≃ₗᵢ[R] Lp 𝕜 1 μ where
  __ := addEquiv 𝕜 μ
  map_smul' _ _ := rfl
  norm_map' _ := rfl

@[simp]
theorem linearIsometryEquiv_apply [NormedField R] [NormedAddCommGroup 𝕜] [NormedSpace R 𝕜]
    (f : L1GroupAlgebra 𝕜 μ) : linearIsometryEquiv R 𝕜 μ f = f.ofConv :=
  (rfl)

@[simp]
theorem linearIsometryEquiv_symm_apply [NormedField R] [NormedAddCommGroup 𝕜] [NormedSpace R 𝕜]
    (f : Lp 𝕜 1 μ) : (linearIsometryEquiv R 𝕜 μ).symm f = toConv f :=
  (rfl)

instance [NormedField R] [NormedAddCommGroup 𝕜] [NormedSpace R 𝕜] :
    NormedSpace R (L1GroupAlgebra 𝕜 μ) where
  norm_smul_le r f := by
    rw [norm_def, norm_def, ofConv_smul]
    exact norm_smul_le r f.ofConv

variable (𝕜 μ) in
/-- Integration against `μ` as a continuous `𝕜`-linear functional on `L1GroupAlgebra 𝕜 μ`. -/
def integralCLM [RCLike 𝕜] : L1GroupAlgebra 𝕜 μ →L[𝕜] 𝕜 :=
  (L1.integralCLM' (μ := μ) 𝕜).comp
    (linearIsometryEquiv 𝕜 𝕜 μ).toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem integralCLM_apply [RCLike 𝕜] (f : L1GroupAlgebra 𝕜 μ) :
    integralCLM 𝕜 μ f = ∫ x, f.ofConv x ∂μ := by
  rw [integralCLM, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, linearIsometryEquiv_apply,
    ← L1.integral_eq', L1.integral_eq_integral]

/-- Integration against `μ` on `L1GroupAlgebra 𝕜 μ` has operator norm at most `1`. -/
theorem norm_integralCLM_le [RCLike 𝕜] : ‖integralCLM 𝕜 μ‖ ≤ 1 :=
  (integralCLM 𝕜 μ).opNorm_le_bound zero_le_one fun f ↦ by
    rw [integralCLM_apply, ← L1.integral_eq_integral, one_mul, norm_def]
    exact L1.norm_integral_le f.ofConv

end NormedSpace

/-! ### Convolution multiplication and Banach algebra structure -/

section Convolution

variable {G 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [μ.IsMulLeftInvariant] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [NormedSpace ℝ 𝕜] [SMulCommClass ℝ 𝕜 𝕜]

instance : Mul (L1GroupAlgebra 𝕜 μ) where
  mul f g := toConv (Lp.convolutionL μ 1 ENNReal.one_ne_top f.ofConv g.ofConv)

@[simp]
theorem ofConv_mul (f g : L1GroupAlgebra 𝕜 μ) :
    (f * g).ofConv = Lp.convolutionL μ 1 ENNReal.one_ne_top f.ofConv g.ofConv :=
  (rfl)

@[simp]
theorem toConv_convolutionL (f g : Lp 𝕜 1 μ) :
    (toConv (Lp.convolutionL μ 1 ENNReal.one_ne_top f g) : L1GroupAlgebra 𝕜 μ) =
      toConv f * toConv g :=
  (rfl)

/-- **Submultiplicativity of group convolution** on `L1GroupAlgebra 𝕜 μ`: `‖f * g‖ ≤ ‖f‖ * ‖g‖`. -/
theorem norm_mul_le (f g : L1GroupAlgebra 𝕜 μ) : ‖f * g‖ ≤ ‖f‖ * ‖g‖ :=
  Lp.norm_convolutionL_apply_le f.ofConv g.ofConv

instance : NonUnitalNonAssocRing (L1GroupAlgebra 𝕜 μ) where
  left_distrib f g h := by ext1; simp [map_add]
  right_distrib f g h := by ext1; simp [map_add]
  zero_mul f := by ext1; simp
  mul_zero f := by ext1; simp

instance : IsScalarTower 𝕜 (L1GroupAlgebra 𝕜 μ) (L1GroupAlgebra 𝕜 μ) where
  smul_assoc c f g := by ext1; simp [map_smul]

instance : SMulCommClass 𝕜 (L1GroupAlgebra 𝕜 μ) (L1GroupAlgebra 𝕜 μ) where
  smul_comm c f g := by ext1; simp [map_smul]

end NontriviallyNormedField

section RCLike

variable [RCLike 𝕜]

instance instNonUnitalRing : NonUnitalRing (L1GroupAlgebra 𝕜 μ) where
  mul_assoc f g h := by ext1; exact Lp.convolutionL_assoc f.ofConv g.ofConv h.ofConv

instance instNonUnitalNormedRing : NonUnitalNormedRing (L1GroupAlgebra 𝕜 μ) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le := norm_mul_le

/-- The Haar integral of a convolution product is the product of the Haar integrals. -/
theorem integral_mul (f g : L1GroupAlgebra 𝕜 μ) :
    ∫ x, (f * g).ofConv x ∂μ = (∫ x, f.ofConv x ∂μ) * ∫ x, g.ofConv x ∂μ := by
  simpa only [ofConv_mul, smul_eq_mul] using Lp.integral_convolutionL f.ofConv g.ofConv

variable (𝕜 μ) in
/-- Haar integration as a nonunital `𝕜`-algebra homomorphism `L1GroupAlgebra 𝕜 μ →ₙₐ[𝕜] 𝕜`. -/
def integralNonUnitalAlgHom : L1GroupAlgebra 𝕜 μ →ₙₐ[𝕜] 𝕜 where
  toFun f := integralCLM 𝕜 μ f
  map_mul' f g := by
    simp only [integralCLM_apply]
    exact integral_mul f g
  map_zero' := map_zero (integralCLM 𝕜 μ)
  map_add' := map_add (integralCLM 𝕜 μ)
  map_smul' := map_smul (integralCLM 𝕜 μ)

@[simp]
theorem coe_integralNonUnitalAlgHom :
    ⇑(integralNonUnitalAlgHom 𝕜 μ) = ⇑(integralCLM 𝕜 μ) :=
  (rfl)

theorem integralNonUnitalAlgHom_apply (f : L1GroupAlgebra 𝕜 μ) :
    integralNonUnitalAlgHom 𝕜 μ f = ∫ x, f.ofConv x ∂μ :=
  integralCLM_apply f

end RCLike

end Convolution

/-! ### Pointwise convolution formulas on locally compact Hausdorff groups -/

section PointwiseConvolution

variable {G 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular]
  [NontriviallyNormedField 𝕜] [NormedSpace ℝ 𝕜] [SMulCommClass ℝ 𝕜 𝕜]

/-- **Left-hand pointwise convolution formula.** On a locally compact Hausdorff group `G` with a
regular left Haar measure `μ` (without σ-compactness or second countability), `(f * g).ofConv`
agrees `μ`-almost everywhere with `x ↦ ∫ y, f.ofConv y * g.ofConv (y⁻¹ * x) ∂μ`. -/
theorem ofConv_mul_ae_eq (f g : L1GroupAlgebra 𝕜 μ) :
    (f * g).ofConv =ᵐ[μ] fun x ↦ ∫ y, f.ofConv y * g.ofConv (y⁻¹ * x) ∂μ := by
  simpa only [ofConv_mul, smul_eq_mul] using
    Lp.convolutionL_ae_eq (hp := ENNReal.one_ne_top) f.ofConv g.ofConv

/-- **Right-hand modular pointwise convolution formula.** On a locally compact Hausdorff group `G`
with regular left Haar measure `μ`, `(f * g).ofConv` agrees `μ`-almost everywhere with
`x ↦ ∫ z, (Measure.modularCharacter z : ℝ) • (f.ofConv (x * z⁻¹) * g.ofConv z) ∂μ`. -/
theorem ofConv_mul_ae_eq_modularCharacter (f g : L1GroupAlgebra 𝕜 μ) :
    (f * g).ofConv =ᵐ[μ]
      fun x ↦ ∫ z, (modularCharacter z : ℝ) • (f.ofConv (x * z⁻¹) * g.ofConv z) ∂μ := by
  filter_upwards [ofConv_mul_ae_eq f g] with x hx
  rw [hx, ← integral_mul_left_eq_self (fun y ↦ f.ofConv y * g.ofConv (y⁻¹ * x)) x]
  have hinv := integral_inv_eq_integral_modularCharacter_smul_of_regular (μ := μ)
    fun z ↦ f.ofConv (x * z⁻¹) * g.ofConv z
  simp only [inv_inv] at hinv
  refine Eq.trans ?_ hinv
  refine integral_congr_ae (.of_forall fun z ↦ ?_)
  simp [mul_inv_rev, inv_mul_cancel_right]

end PointwiseConvolution

/-! ### Left and right translations -/

section Translations

variable {G 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G}

section LeftTranslation

variable [μ.IsMulLeftInvariant] [NormedField 𝕜]

variable (𝕜 μ) in
/-- Left translation `g ↦ L_g` on `L1GroupAlgebra 𝕜 μ`, where
`(L_g f).ofConv x = f.ofConv (g⁻¹ * x)` almost everywhere, as a group homomorphism into linear
isometry equivalences. -/
def leftTranslation : G →* (L1GroupAlgebra 𝕜 μ ≃ₗᵢ[𝕜] L1GroupAlgebra 𝕜 μ) where
  toFun g := (linearIsometryEquiv 𝕜 𝕜 μ).trans
    ((Lp.leftTranslation μ 1 𝕜 g).trans (linearIsometryEquiv 𝕜 𝕜 μ).symm)
  map_one' := by ext1 f; ext1; simp
  map_mul' g h := by ext1 f; ext1; simp [map_mul]

@[simp]
theorem ofConv_leftTranslation (g : G) (f : L1GroupAlgebra 𝕜 μ) :
    (leftTranslation 𝕜 μ g f).ofConv = Lp.leftTranslation μ 1 𝕜 g f.ofConv :=
  (rfl)

theorem coeFn_ofConv_leftTranslation (g : G) (f : L1GroupAlgebra 𝕜 μ) :
    (leftTranslation 𝕜 μ g f).ofConv =ᵐ[μ] fun x ↦ f.ofConv (g⁻¹ * x) :=
  Lp.coeFn_leftTranslation g f.ofConv

/-- Left translation preserves Haar integrals on `L1GroupAlgebra 𝕜 μ`. -/
theorem integral_leftTranslation [NormedSpace ℝ 𝕜] (g : G) (f : L1GroupAlgebra 𝕜 μ) :
    ∫ x, (leftTranslation 𝕜 μ g f).ofConv x ∂μ = ∫ x, f.ofConv x ∂μ :=
  Lp.integral_leftTranslation g f.ofConv

/-- Left translation on `L1GroupAlgebra 𝕜 μ` is strongly continuous in the group variable. -/
theorem continuous_leftTranslation_apply [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    (f : L1GroupAlgebra 𝕜 μ) :
    Continuous fun g : G ↦ leftTranslation 𝕜 μ g f :=
  continuous_toConv.comp (Lp.continuous_leftTranslation_apply ENNReal.one_ne_top f.ofConv)

end LeftTranslation

section LeftTranslationMul

variable [μ.IsMulLeftInvariant] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
  [NontriviallyNormedField 𝕜] [NormedSpace ℝ 𝕜] [SMulCommClass ℝ 𝕜 𝕜]

/-- Left translation acts on the left factor of a convolution product:
`L_g (f * h) = L_g f * h`. -/
theorem leftTranslation_mul (g : G) (f h : L1GroupAlgebra 𝕜 μ) :
    leftTranslation 𝕜 μ g (f * h) = leftTranslation 𝕜 μ g f * h := by
  ext1
  exact Lp.leftTranslation_convolutionL g f.ofConv h.ofConv

end LeftTranslationMul

section RightTranslation

variable [LocallyCompactSpace G] [μ.IsHaarMeasure] [μ.Regular]
  [NormedField 𝕜] [NormedSpace ℝ 𝕜] [SMulCommClass ℝ 𝕜 𝕜]

variable (𝕜 μ) in
/-- Weighted right translation `g ↦ R_g` on `L1GroupAlgebra 𝕜 μ`, where
`(R_g f).ofConv x = c(g⁻¹) • f.ofConv (x * g)` almost everywhere, as a group homomorphism into
linear isometry equivalences. -/
def rightTranslation : G →* (L1GroupAlgebra 𝕜 μ ≃ₗᵢ[𝕜] L1GroupAlgebra 𝕜 μ) where
  toFun g := (linearIsometryEquiv 𝕜 𝕜 μ).trans
    ((Lp.rightTranslation μ 1 𝕜 g).trans (linearIsometryEquiv 𝕜 𝕜 μ).symm)
  map_one' := by ext1 f; ext1; simp
  map_mul' g h := by ext1 f; ext1; simp [map_mul]

@[simp]
theorem ofConv_rightTranslation (g : G) (f : L1GroupAlgebra 𝕜 μ) :
    (rightTranslation 𝕜 μ g f).ofConv = Lp.rightTranslation μ 1 𝕜 g f.ofConv :=
  (rfl)

/-- Almost-everywhere formula for weighted right translation on `L1GroupAlgebra 𝕜 μ`. -/
theorem coeFn_ofConv_rightTranslation (g : G) (f : L1GroupAlgebra 𝕜 μ) :
    (rightTranslation 𝕜 μ g f).ofConv =ᵐ[μ]
      fun x ↦ (modularCharacter g⁻¹ : ℝ) • f.ofConv (x * g) := by
  simpa only [ofConv_rightTranslation, ENNReal.toReal_one, inv_one, Real.rpow_one] using
    Lp.coeFn_rightTranslation (𝕜 := 𝕜) g f.ofConv

/-- Weighted right translation preserves Haar integrals on `L1GroupAlgebra 𝕜 μ`. -/
theorem integral_rightTranslation (g : G) (f : L1GroupAlgebra 𝕜 μ) :
    ∫ x, (rightTranslation 𝕜 μ g f).ofConv x ∂μ = ∫ x, f.ofConv x ∂μ :=
  Lp.integral_rightTranslation g f.ofConv

/-- Weighted right translation on `L1GroupAlgebra 𝕜 μ` is strongly continuous in the group
variable. -/
theorem continuous_rightTranslation_apply (f : L1GroupAlgebra 𝕜 μ) :
    Continuous fun g : G ↦ rightTranslation 𝕜 μ g f :=
  continuous_toConv.comp (Lp.continuous_rightTranslation_apply ENNReal.one_ne_top f.ofConv)

/-- Left translation commutes with weighted right translation on `L1GroupAlgebra 𝕜 μ`. -/
theorem leftTranslation_rightTranslation (g h : G) (f : L1GroupAlgebra 𝕜 μ) :
    leftTranslation 𝕜 μ h (rightTranslation 𝕜 μ g f) =
      rightTranslation 𝕜 μ g (leftTranslation 𝕜 μ h f) := by
  ext1
  exact Lp.leftTranslation_rightTranslation g h f.ofConv

end RightTranslation

section RightTranslationMul

variable [LocallyCompactSpace G] [μ.IsHaarMeasure] [μ.Regular]
  [NontriviallyNormedField 𝕜] [NormedSpace ℝ 𝕜] [SMulCommClass ℝ 𝕜 𝕜]

/-- Weighted right translation acts on the right factor of a convolution product:
`R_g (f * h) = f * R_g h`. -/
theorem rightTranslation_mul (g : G) (f h : L1GroupAlgebra 𝕜 μ) :
    rightTranslation 𝕜 μ g (f * h) = f * rightTranslation 𝕜 μ g h := by
  ext1
  exact Lp.rightTranslation_convolutionL g f.ofConv h.ofConv

end RightTranslationMul

end Translations

/-! ### Modular involution (`⋆`-algebra structure) -/

section Star

variable {G 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular]

section StarModule

variable [NormedField 𝕜] [NormedSpace ℝ 𝕜] [SMulCommClass ℝ 𝕜 𝕜]
  [StarRing 𝕜] [NormedStarGroup 𝕜]

/-- The **modular involution** on `L1GroupAlgebra 𝕜 μ`: `star f` corresponds to
`Lp.modularInversion μ 1 𝕜 (star f.ofConv)`, represented almost everywhere by
`x ↦ (Measure.modularCharacter x : ℝ) • star (f.ofConv x⁻¹)`. -/
instance : Star (L1GroupAlgebra 𝕜 μ) where
  star f := toConv (Lp.modularInversion μ 1 𝕜 (star f.ofConv))

@[simp]
theorem ofConv_star (f : L1GroupAlgebra 𝕜 μ) :
    (star f).ofConv = Lp.modularInversion μ 1 𝕜 (star f.ofConv) :=
  (rfl)

/-- Pointwise formula for the modular involution on `L1GroupAlgebra 𝕜 μ`, almost everywhere. -/
theorem coeFn_ofConv_star (f : L1GroupAlgebra 𝕜 μ) :
    (star f).ofConv =ᵐ[μ] fun x ↦ (modularCharacter x : ℝ) • star (f.ofConv x⁻¹) := by
  filter_upwards [Lp.coeFn_modularInversion (𝕜 := 𝕜) (star f.ofConv),
    (quasiMeasurePreserving_inv_of_regular μ).ae (Lp.coeFn_star f.ofConv)] with x h₁ h₂
  rw [ofConv_star, h₁, ENNReal.toReal_one, inv_one, Real.rpow_one, h₂, Pi.star_apply]

/-- Modular involution swaps left translation and weighted right translation on
`L1GroupAlgebra 𝕜 μ`: `star (L_g f) = R_g (star f)`. -/
theorem star_leftTranslation (g : G) (f : L1GroupAlgebra 𝕜 μ) :
    star (leftTranslation 𝕜 μ g f) = rightTranslation 𝕜 μ g (star f) := by
  ext1
  rw [ofConv_star, ofConv_leftTranslation, ← Lp.leftTranslation_star, ofConv_rightTranslation,
    ofConv_star, Lp.rightTranslation_apply, Lp.modularInversion_modularInversion]

variable [StarModule ℝ 𝕜]

instance : InvolutiveStar (L1GroupAlgebra 𝕜 μ) where
  star_involutive f := by
    ext1
    rw [ofConv_star, ofConv_star, ← Lp.modularInversion_star, Lp.modularInversion_modularInversion,
      star_star]

instance : StarAddMonoid (L1GroupAlgebra 𝕜 μ) where
  star_add f g := by ext1; simp [star_add]

instance : StarModule 𝕜 (L1GroupAlgebra 𝕜 μ) where
  star_smul c f := by ext1; simp [star_smul]

instance : NormedStarGroup (L1GroupAlgebra 𝕜 μ) where
  norm_star_le f := by
    rw [norm_def, norm_def, ofConv_star, LinearIsometryEquiv.norm_map, norm_star]

/-- Modular involution swaps weighted right translation and left translation on
`L1GroupAlgebra 𝕜 μ`: `star (R_g f) = L_g (star f)`. -/
theorem star_rightTranslation (g : G) (f : L1GroupAlgebra 𝕜 μ) :
    star (rightTranslation 𝕜 μ g f) = leftTranslation 𝕜 μ g (star f) := by
  apply star_injective
  rw [star_star, star_leftTranslation, star_star]

/-- The Haar integral of `star f` is `star` of the Haar integral of `f`. -/
theorem integral_star (f : L1GroupAlgebra 𝕜 μ) :
    ∫ x, (star f).ofConv x ∂μ = star (∫ x, f.ofConv x ∂μ) := by
  rw [ofConv_star, Lp.integral_modularInversion, integral_congr_ae (Lp.coeFn_star f.ofConv)]
  exact (starL' ℝ (A := 𝕜)).integral_comp_comm _

end StarModule

section RCLike

variable [RCLike 𝕜]

instance instStarRing : StarRing (L1GroupAlgebra 𝕜 μ) where
  star_mul f g := by
    ext1
    exact Lp.modularInversion_star_convolutionL f.ofConv g.ofConv
  star_add := star_add

variable (𝕜 μ) in
/-- Haar integration as a nonunital `⋆`-algebra homomorphism `L1GroupAlgebra 𝕜 μ →⋆ₙₐ[𝕜] 𝕜`
(corresponding to the integrated form of the trivial unitary representation of `G`). -/
def integralStarAlgHom : L1GroupAlgebra 𝕜 μ →⋆ₙₐ[𝕜] 𝕜 where
  __ := integralNonUnitalAlgHom 𝕜 μ
  map_star' f := by
    simp only [NonUnitalAlgHom.toFun_eq_coe, integralNonUnitalAlgHom_apply]
    exact integral_star f

@[simp]
theorem toNonUnitalAlgHom_integralStarAlgHom :
    (integralStarAlgHom 𝕜 μ).toNonUnitalAlgHom = integralNonUnitalAlgHom 𝕜 μ :=
  (rfl)

@[simp]
theorem integralStarAlgHom_apply (f : L1GroupAlgebra 𝕜 μ) :
    integralStarAlgHom 𝕜 μ f = ∫ x, f.ofConv x ∂μ :=
  integralCLM_apply f

end RCLike

end Star

/-! ### Comparison of regular left Haar normalizations -/

section HaarNormalization

variable {G 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ ν ρ : Measure G} [μ.IsHaarMeasure] [μ.Regular] [ν.IsHaarMeasure] [ν.Regular]
  [ρ.IsHaarMeasure] [ρ.Regular]

section LinearIsometry

variable [NormedField 𝕜] [NormedSpace ℝ 𝕜] [SMulCommClass ℝ 𝕜 𝕜]

variable (𝕜 μ ν) in
/-- Canonical linear isometry equivalence `L1GroupAlgebra 𝕜 μ ≃ₗᵢ[𝕜] L1GroupAlgebra 𝕜 ν` relating
any two regular left Haar measures `μ` and `ν` on `G`, multiplying representatives by
`(Measure.haarScalarFactor μ ν : ℝ)`. -/
def haarLinearIsometryEquiv : L1GroupAlgebra 𝕜 μ ≃ₗᵢ[𝕜] L1GroupAlgebra 𝕜 ν :=
  (linearIsometryEquiv 𝕜 𝕜 μ).trans
    ((Lp.haarMeasureCongrₗᵢ μ ν 1 𝕜).trans (linearIsometryEquiv 𝕜 𝕜 ν).symm)

@[simp]
theorem ofConv_haarLinearIsometryEquiv (f : L1GroupAlgebra 𝕜 μ) :
    (haarLinearIsometryEquiv 𝕜 μ ν f).ofConv = Lp.haarMeasureCongrₗᵢ μ ν 1 𝕜 f.ofConv :=
  (rfl)

/-- Almost-everywhere formula for `haarLinearIsometryEquiv 𝕜 μ ν`. -/
theorem coeFn_ofConv_haarLinearIsometryEquiv (f : L1GroupAlgebra 𝕜 μ) :
    (haarLinearIsometryEquiv 𝕜 μ ν f).ofConv =ᵐ[ν]
      fun x ↦ (haarScalarFactor μ ν : ℝ) • f.ofConv x := by
  rw [ofConv_haarLinearIsometryEquiv]
  exact Lp.coeFn_haarMeasureCongrₗᵢ_one (ν := ν) (𝕜 := 𝕜) f.ofConv

@[simp]
theorem haarLinearIsometryEquiv_refl :
    haarLinearIsometryEquiv 𝕜 μ μ = LinearIsometryEquiv.refl 𝕜 (L1GroupAlgebra 𝕜 μ) := by
  ext1 f; ext1; simp

/-- `haarLinearIsometryEquiv` composes functorially across three regular Haar measures. -/
theorem haarLinearIsometryEquiv_trans :
    (haarLinearIsometryEquiv 𝕜 μ ν).trans (haarLinearIsometryEquiv 𝕜 ν ρ) =
      haarLinearIsometryEquiv 𝕜 μ ρ := by
  ext1 f
  ext1
  simpa only [LinearIsometryEquiv.trans_apply, ofConv_haarLinearIsometryEquiv] using
    DFunLike.congr_fun (Lp.haarMeasureCongrₗᵢ_trans (μ := μ) (ν := ν) ρ (p := 1) (𝕜 := 𝕜))
      f.ofConv

@[simp]
theorem haarLinearIsometryEquiv_symm :
    (haarLinearIsometryEquiv 𝕜 μ ν).symm = haarLinearIsometryEquiv 𝕜 ν μ := by
  ext1 f
  rw [LinearIsometryEquiv.symm_apply_eq, ← LinearIsometryEquiv.trans_apply,
    haarLinearIsometryEquiv_trans, haarLinearIsometryEquiv_refl]
  rfl

/-- `haarLinearIsometryEquiv 𝕜 μ ν` preserves Haar integrals. -/
theorem integral_haarLinearIsometryEquiv (f : L1GroupAlgebra 𝕜 μ) :
    ∫ x, (haarLinearIsometryEquiv 𝕜 μ ν f).ofConv x ∂ν = ∫ x, f.ofConv x ∂μ := by
  rw [ofConv_haarLinearIsometryEquiv]
  exact Lp.integral_haarMeasureCongrₗᵢ (ν := ν) (𝕜 := 𝕜) f.ofConv

/-- `haarLinearIsometryEquiv 𝕜 μ ν` intertwines left translations on `L1GroupAlgebra`. -/
theorem haarLinearIsometryEquiv_leftTranslation (g : G) (f : L1GroupAlgebra 𝕜 μ) :
    haarLinearIsometryEquiv 𝕜 μ ν (leftTranslation 𝕜 μ g f) =
      leftTranslation 𝕜 ν g (haarLinearIsometryEquiv 𝕜 μ ν f) := by
  ext1
  rw [ofConv_haarLinearIsometryEquiv, ofConv_leftTranslation,
    Lp.haarMeasureCongrₗᵢ_leftTranslation (ν := ν) (𝕜 := 𝕜),
    ofConv_leftTranslation, ofConv_haarLinearIsometryEquiv]

/-- `haarLinearIsometryEquiv 𝕜 μ ν` intertwines weighted right translations on `L1GroupAlgebra`. -/
theorem haarLinearIsometryEquiv_rightTranslation (g : G) (f : L1GroupAlgebra 𝕜 μ) :
    haarLinearIsometryEquiv 𝕜 μ ν (rightTranslation 𝕜 μ g f) =
      rightTranslation 𝕜 ν g (haarLinearIsometryEquiv 𝕜 μ ν f) := by
  ext1
  rw [ofConv_haarLinearIsometryEquiv, ofConv_rightTranslation,
    Lp.haarMeasureCongrₗᵢ_rightTranslation (ν := ν) (𝕜 := 𝕜),
    ofConv_rightTranslation, ofConv_haarLinearIsometryEquiv]

end LinearIsometry

section StarAlgEquiv

variable [RCLike 𝕜]

variable (𝕜 μ ν) in
/-- **Invariance of the group convolution Banach `⋆`-algebra under Haar rescaling.** Any two regular
left Haar measures `μ` and `ν` on `G` yield a canonical isometric `⋆`-algebra isomorphism
`L1GroupAlgebra 𝕜 μ ≃⋆ₐ[𝕜] L1GroupAlgebra 𝕜 ν`. -/
def haarStarAlgEquiv : L1GroupAlgebra 𝕜 μ ≃⋆ₐ[𝕜] L1GroupAlgebra 𝕜 ν where
  __ := (haarLinearIsometryEquiv 𝕜 μ ν).toLinearEquiv
  map_mul' f g := by
    simp only [LinearEquiv.toFun_eq_coe, LinearIsometryEquiv.coe_toLinearEquiv]
    ext1
    rw [ofConv_haarLinearIsometryEquiv, ofConv_mul, ofConv_mul,
      ofConv_haarLinearIsometryEquiv, ofConv_haarLinearIsometryEquiv]
    exact Lp.haarMeasureCongrₗᵢ_convolutionL (ν := ν) f.ofConv g.ofConv
  map_star' f := by
    simp only [LinearEquiv.toFun_eq_coe, LinearIsometryEquiv.coe_toLinearEquiv]
    ext1
    rw [ofConv_haarLinearIsometryEquiv, ofConv_star,
      Lp.haarMeasureCongrₗᵢ_modularInversion (ν := ν) (𝕜 := 𝕜),
      ← Lp.star_haarMeasureCongrₗᵢ (ν := ν) (𝕜 := 𝕜),
      ofConv_star, ofConv_haarLinearIsometryEquiv]

@[simp]
theorem coe_haarStarAlgEquiv :
    ⇑(haarStarAlgEquiv 𝕜 μ ν) = ⇑(haarLinearIsometryEquiv 𝕜 μ ν) :=
  (rfl)

theorem haarStarAlgEquiv_apply (f : L1GroupAlgebra 𝕜 μ) :
    haarStarAlgEquiv 𝕜 μ ν f = haarLinearIsometryEquiv 𝕜 μ ν f :=
  (rfl)

/-- `haarStarAlgEquiv 𝕜 μ ν` preserves the `L¹` norm. -/
theorem norm_haarStarAlgEquiv (f : L1GroupAlgebra 𝕜 μ) :
    ‖haarStarAlgEquiv 𝕜 μ ν f‖ = ‖f‖ :=
  (haarLinearIsometryEquiv 𝕜 μ ν).norm_map f

/-- `haarStarAlgEquiv 𝕜 μ ν` is an isometry. -/
theorem isometry_haarStarAlgEquiv : Isometry (haarStarAlgEquiv 𝕜 μ ν) :=
  (haarLinearIsometryEquiv 𝕜 μ ν).isometry

/-- `haarStarAlgEquiv 𝕜 μ ν` intertwines the Haar integration `⋆`-homomorphisms. -/
theorem integralStarAlgHom_haarStarAlgEquiv (f : L1GroupAlgebra 𝕜 μ) :
    integralStarAlgHom 𝕜 ν (haarStarAlgEquiv 𝕜 μ ν f) = integralStarAlgHom 𝕜 μ f := by
  rw [integralStarAlgHom_apply, integralStarAlgHom_apply, coe_haarStarAlgEquiv,
    integral_haarLinearIsometryEquiv]

@[simp]
theorem haarStarAlgEquiv_refl :
    haarStarAlgEquiv 𝕜 μ μ = StarAlgEquiv.refl 𝕜 (L1GroupAlgebra 𝕜 μ) :=
  StarAlgEquiv.ext fun f ↦ by simp

@[simp]
theorem haarStarAlgEquiv_symm :
    (haarStarAlgEquiv 𝕜 μ ν).symm = haarStarAlgEquiv 𝕜 ν μ :=
  StarAlgEquiv.ext fun f ↦ by
    rw [StarAlgEquiv.symm_apply_eq, coe_haarStarAlgEquiv, coe_haarStarAlgEquiv,
      ← LinearIsometryEquiv.trans_apply, haarLinearIsometryEquiv_trans,
      haarLinearIsometryEquiv_refl]
    rfl

/-- `haarStarAlgEquiv` composes functorially across three regular Haar measures. -/
theorem haarStarAlgEquiv_trans :
    (haarStarAlgEquiv 𝕜 μ ν).trans (haarStarAlgEquiv 𝕜 ν ρ) =
      haarStarAlgEquiv 𝕜 μ ρ :=
  StarAlgEquiv.ext fun f ↦ by
    have h := DFunLike.congr_fun
      (haarLinearIsometryEquiv_trans (𝕜 := 𝕜) (μ := μ) (ν := ν) (ρ := ρ)) f
    simpa only [StarAlgEquiv.trans_apply, LinearIsometryEquiv.trans_apply, coe_haarStarAlgEquiv]
      using h

end StarAlgEquiv

end HaarNormalization

end L1GroupAlgebra

end TauCeti

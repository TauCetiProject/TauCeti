/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.HahnSeries.TensorProduct
public import TauCeti.RingTheory.LaurentSeries.Substitution.Basic
public import TauCeti.RingTheory.LaurentSeries.ContinuousDual.HahnModule

/-!
# Coordinate changes on module-valued Laurent series

For a finite-dimensional coefficient space `V`, substitution on `V((t))` is scalar
substitution on `K((t)) ⊗[K] V`, transported through the canonical comparison with
`HahnModule ℤ K V`. Thus the construction is independent of a coefficient basis.

The residue pairing with `V*((t)) dt` is coordinate invariant: both Laurent series are
substituted, and the dual series is multiplied by the derivative of the new parameter.
This Jacobian factor is essential to the interpretation of the continuous dual as one-forms.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.2.
-/

public section

noncomputable section

open HahnSeries TensorProduct TauCeti
open scoped LaurentSeries PowerSeries

namespace HahnModule

open TauCeti.HahnModule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)

/-- Substitute a nonzero parameter of positive order into module-valued Laurent series,
using the basis-independent scalar-extension comparison. -/
def subst : HahnModule ℤ K V →ₗ[K] HahnModule ℤ K V :=
  (tensorProductEquiv ℤ K V).toLinearMap.restrictScalars K ∘ₗ
    TensorProduct.map
      { toFun := LaurentSeries.substAlgHom hφ hφ₀
        map_add' := map_add _
        -- The tensor comparison uses coefficientwise scalars, while the Laurent algebra
        -- is obtained through the power-series tower. Identify these actions explicitly.
        map_smul' := fun r f ↦ by
          rw [← laurentSeries_algebraMap_mul_eq_smul, map_mul, AlgHom.commutes,
            laurentSeries_algebraMap_mul_eq_smul]
          rfl } LinearMap.id ∘ₗ
      (tensorProductEquiv ℤ K V).symm.toLinearMap.restrictScalars K

/-- On a scalar series times a constant vector, substitution acts only on the scalar series. -/
theorem subst_smul_single_zero (f : K⸨X⸩) (v : V) :
    subst hφ hφ₀ (f • of K (single 0 v)) =
      LaurentSeries.substAlgHom hφ hφ₀ f • of K (single (0 : ℤ) v) := by
  have ht : (tensorProductEquiv ℤ K V).symm (f • of K (single 0 v)) = f ⊗ₜ[K] v :=
    (tensorProductEquiv ℤ K V).symm_apply_eq.mpr (by simp)
  simp [subst, ht]

/-- A vector-valued monomial is evaluated at the new parameter. -/
@[simp]
theorem subst_single (n : ℤ) (v : V) :
    subst hφ hφ₀ (of K (single n v)) =
      (φ : K⸨X⸩) ^ n • of K (single (0 : ℤ) v) := by
  have hs := single_smul_single_zero n (1 : K) v
  simp only [one_smul] at hs
  rw [← hs, subst_smul_single_zero, LaurentSeries.substAlgHom_single]
  simp

/-- In any finite coefficient basis, substitution applies scalar substitution to each
coordinate Laurent series. -/
theorem subst_eq_sum {ι : Type*} [Fintype ι] (b : Module.Basis ι K V)
    (x : HahnModule ℤ K V) :
    subst hφ hφ₀ x = ∑ i, LaurentSeries.substAlgHom hφ hφ₀
      (((of K).symm x).map (b.coord i)) • of K (single (0 : ℤ) (b i)) := by
  conv_lhs => rw [← sum_map_coord_smul_single b x]
  simp only [map_sum, subst_smul_single_zero]

/-- The coefficient formula for module-valued substitution in any finite coefficient basis. -/
theorem coeff_subst {ι : Type*} [Fintype ι] (b : Module.Basis ι K V)
    (x : HahnModule ℤ K V) (n : ℤ) :
    ((of K).symm (subst hφ hφ₀ x)).coeff n = ∑ i,
      (LaurentSeries.substAlgHom hφ hφ₀ (((of K).symm x).map (b.coord i))).coeff n • b i := by
  rw [subst_eq_sum hφ hφ₀ b, ← ofLinearEquiv_symm_apply]
  simp

/-- Substituting `X` is the identity on module-valued Laurent series. -/
@[simp]
theorem subst_X (x : HahnModule ℤ K V) :
    subst PowerSeries.constantCoeff_X PowerSeries.X_ne_zero x = x := by
  have heq : subst (V := V) PowerSeries.constantCoeff_X PowerSeries.X_ne_zero = LinearMap.id :=
    linearMap_ext_smul_single_zero (R := K) fun f v ↦ by simp [subst_smul_single_zero]
  exact DFunLike.congr_fun heq x

private theorem subst_eq_self_of_eq_X (h : φ = PowerSeries.X) (x : HahnModule ℤ K V) :
    subst hφ hφ₀ x = x := by
  subst φ
  exact subst_X x

/-- Substitution is semilinear for the substitution of scalar Laurent series. -/
@[simp]
theorem subst_smul (f : K⸨X⸩) (x : HahnModule ℤ K V) :
    subst hφ hφ₀ (f • x) = LaurentSeries.substAlgHom hφ hφ₀ f • subst hφ hφ₀ x := by
  obtain ⟨z, rfl⟩ := (tensorProductEquiv ℤ K V).surjective x
  induction z using TensorProduct.inductionOn with
  | tmul a v => simp [← mul_smul, subst_smul_single_zero]
  | add z w hz hw => simp only [map_add, _root_.smul_add, hz, hw]

/-- Successive substitutions on module-valued series agree with substitution by the
composite parameter. -/
theorem subst_subst {ψ : K⟦X⟧} (hψ : PowerSeries.constantCoeff ψ = 0) (hψ₀ : ψ ≠ 0)
    (x : HahnModule ℤ K V) :
    subst hψ hψ₀ (subst hφ hφ₀ x) =
      subst (φ := φ.subst ψ) (by
        simpa only [PowerSeries.constantCoeff_eq] using
          PowerSeries.constantCoeff_subst_eq_zero hψ φ hφ)
        ((PowerSeries.subst_eq_zero_iff hψ hψ₀).not.mpr hφ₀) x := by
  have heq : (subst (V := V) hψ hψ₀).comp (subst hφ hφ₀) =
      subst (φ := φ.subst ψ) (by
        simpa only [PowerSeries.constantCoeff_eq] using
          PowerSeries.constantCoeff_subst_eq_zero hψ φ hφ)
        ((PowerSeries.subst_eq_zero_iff hψ hψ₀).not.mpr hφ₀) := by
    apply linearMap_ext_smul_single_zero (R := K)
    intro f v
    rw [LinearMap.comp_apply, subst_smul_single_zero, subst_smul_single_zero,
      subst_smul_single_zero, LaurentSeries.substAlgHom_comp_substAlgHom_apply]
  exact DFunLike.congr_fun heq x

/-- Substitution commutes with linear maps on the coefficient spaces. -/
theorem subst_map {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ℓ : V →ₗ[K] W) (x : HahnModule ℤ K V) :
    subst hφ hφ₀ (of K (((of K).symm x).map ℓ)) =
      of K (((of K).symm (subst hφ hφ₀ x)).map ℓ) := by
  obtain ⟨z, rfl⟩ := (tensorProductEquiv ℤ K V).surjective x
  induction z using TensorProduct.inductionOn with
  | tmul a v =>
    have hmap (f : K⸨X⸩) : of K (((of K).symm (f • of K (single (0 : ℤ) v))).map ℓ) =
        f • of K (single (0 : ℤ) (ℓ v)) := by
      ext n
      simp
    simp only [tensorProductEquiv_apply, tensorProductToHahnModule_tmul, hmap,
      subst_smul_single_zero]
  | add z w hz hw =>
    -- `HahnSeries.map_add` takes an additive homomorphism, not a linear map.
    have hmap (u w : HahnSeries ℤ V) : (u + w).map ℓ = u.map ℓ + w.map ℓ :=
      HahnSeries.map_add ℓ.toAddMonoidHom
    simp only [map_add, of_symm_add, hmap, of_add, hz, hw]

/-- A coordinate substitution followed by its inverse fixes every module-valued series. -/
@[simp]
theorem subst_inv_subst (φ : FormalCoordinate K) (x : HahnModule ℤ K V) :
    subst φ⁻¹.constantCoeff_toPowerSeries φ⁻¹.toPowerSeries_ne_zero
      (subst φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero x) = x := by
  rw [subst_subst]
  exact subst_eq_self_of_eq_X _ _ (by
    simpa only [FormalCoordinate.toPowerSeries_mul] using φ.toPowerSeries_mul_inv) x

/-- A formal coordinate acts invertibly on finite-dimensional module-valued Laurent series.
The action is linear over the coefficient field and semilinear over the Laurent field. -/
def substEquiv (φ : FormalCoordinate K) : HahnModule ℤ K V ≃ₗ[K] HahnModule ℤ K V where
  toLinearMap := subst φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero
  invFun := subst φ⁻¹.constantCoeff_toPowerSeries φ⁻¹.toPowerSeries_ne_zero
  left_inv := subst_inv_subst φ
  right_inv x := by simpa using subst_inv_subst φ⁻¹ x

@[simp]
theorem substEquiv_apply (φ : FormalCoordinate K) (x : HahnModule ℤ K V) :
    substEquiv φ x = subst φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero x := (rfl)

@[simp]
theorem substEquiv_symm (φ : FormalCoordinate K) :
    (substEquiv (V := V) φ).symm = substEquiv φ⁻¹ := by
  ext x
  rfl

/-- Coordinate composition reverses the order of the induced substitutions. -/
@[simp]
theorem substEquiv_mul (φ ψ : FormalCoordinate K) :
    substEquiv (V := V) (φ * ψ) = (substEquiv φ).trans (substEquiv ψ) := by
  apply LinearEquiv.ext
  intro x
  simpa only [LinearEquiv.trans_apply, substEquiv_apply, FormalCoordinate.toPowerSeries_mul]
    using (subst_subst φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero
      ψ.constantCoeff_toPowerSeries ψ.toPowerSeries_ne_zero x).symm

/-- The identity coordinate acts trivially. -/
@[simp]
theorem substEquiv_one : substEquiv (V := V) (1 : FormalCoordinate K) = LinearEquiv.refl K _ := by
  apply LinearEquiv.ext
  intro x
  rw [substEquiv_apply]
  exact subst_eq_self_of_eq_X _ _ FormalCoordinate.toPowerSeries_one x

/-- A substitution of order `e` maps the lattice `U_a(V)` into `U_(e a)(V)`. -/
theorem subst_mem_lattice {a : ℤ} {x : HahnModule ℤ K V}
    (hx : x ∈ TauCeti.HahnModule.lattice K V a) :
    subst hφ hφ₀ x ∈ TauCeti.HahnModule.lattice K V (φ.order.toNat * a) := by
  classical
  let b := Module.Free.chooseBasis K V
  let := Fintype.ofFinite (Module.Free.ChooseBasisIndex K V)
  rw [TauCeti.HahnModule.mem_lattice_iff]
  intro n hn
  rw [coeff_subst hφ hφ₀ b]
  apply Finset.sum_eq_zero
  intro i _
  have hc : (a : WithTop ℤ) ≤ (((of K).symm x).map (b.coord i)).orderTop := by
    apply le_orderTop_iff_forall.mpr
    intro m hm
    rw [map_coeff, (TauCeti.HahnModule.mem_lattice_iff K V).mp hx m
      (WithTop.coe_lt_coe.mp hm), map_zero]
  have hs := nsmul_le_nsmul_right hc φ.order.toNat
  rw [← LaurentSeries.orderTop_substAlgHom hφ hφ₀, ← WithTop.coe_nsmul,
    nsmul_eq_mul] at hs
  rw [coeff_eq_zero_of_lt_orderTop ((WithTop.coe_lt_coe.mpr hn).trans_le hs), zero_smul]

/-- Module-valued substitution is continuous for the lattice topology. -/
theorem continuous_subst : Continuous (subst (V := V) hφ hφ₀) := by
  apply continuous_of_continuousAt_zero
  rw [ContinuousAt, map_zero]
  apply ((TauCeti.HahnModule.hasBasis_nhds_zero_lattice K V).tendsto_iff
    (TauCeti.HahnModule.hasBasis_nhds_zero_lattice K V)).mpr
  intro a _
  refine ⟨max a 0, trivial, fun x hx ↦ ?_⟩
  apply TauCeti.HahnModule.lattice_antitone K V (a := a) ?_ (subst_mem_lattice hφ hφ₀ hx)
  have he : 0 < (φ.order.toNat : ℤ) := by
    exact_mod_cast Nat.pos_of_ne_zero (PowerSeries.toNat_order_ne_zero hφ hφ₀)
  have hmax : 0 ≤ max a 0 := le_max_right _ _
  nlinarith [le_max_left a 0]

/-- The action of a formal coordinate is a homeomorphism for the lattice topology. -/
theorem isHomeomorph_substEquiv (φ : FormalCoordinate K) :
    IsHomeomorph (substEquiv (V := V) φ) :=
  Homeomorph.isHomeomorph
    { toEquiv := (substEquiv φ).toEquiv
      continuous_toFun := continuous_subst _ _
      continuous_invFun := continuous_subst _ _ }

section Residue

variable [TopologicalSpace K] [DiscreteTopology K]

/-- Under a parameter substitution of order `e`, the contraction-residue pairing on
module-valued series, with the Jacobian on the dual series, is multiplied by `e`.
This holds in every characteristic, including when `e` vanishes in `K`. -/
theorem residueDual_derivative_smul_subst_eq_nsmul
    (g : HahnModule ℤ K (Module.Dual K V)) (x : HahnModule ℤ K V) :
    residueDual (_root_.LaurentSeries.derivative K (φ : K⸨X⸩) • subst hφ hφ₀ g)
      (subst hφ hφ₀ x) = φ.order.toNat • residueDual g x := by
  obtain ⟨z, rfl⟩ := (tensorProductEquiv ℤ K (Module.Dual K V)).surjective g
  induction z using TensorProduct.inductionOn with
  | tmul a ℓ =>
    obtain ⟨w, rfl⟩ := (tensorProductEquiv ℤ K V).surjective x
    induction w using TensorProduct.inductionOn with
    | tmul b v =>
      simp only [tensorProductEquiv_apply, tensorProductToHahnModule_tmul,
        subst_smul_single_zero, ← mul_smul,
        _root_.LaurentSeries.residueDual_smul_single_zero_smul_single_zero]
      have hres := LaurentSeries.coeff_neg_one_substAlgHom_mul_derivative_eq_nsmul
        hφ hφ₀ (a * b)
      rw [map_mul] at hres
      convert congrArg (fun c : K ↦ c * ℓ v) hres using 1
      · congr 2
        ring
      · simp [nsmul_eq_mul, mul_assoc]
    | add u w hu hw =>
      simp only [map_add, hu, hw, nsmul_add]
  | add z w hz hw =>
    simp only [map_add, _root_.smul_add, residueDual_add, add_apply,
      hz, hw]

/-- Formal coordinate changes preserve module-valued residue duality, when the dual
series transforms as a one-form rather than a scalar series. -/
theorem residueDual_derivative_smul_subst_coordinate (φ : FormalCoordinate K)
    (g : HahnModule ℤ K (Module.Dual K V)) (x : HahnModule ℤ K V) :
    residueDual (_root_.LaurentSeries.derivative K (φ.toPowerSeries : K⸨X⸩) •
      subst φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero g)
      (subst φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero x) = residueDual g x := by
  simpa using residueDual_derivative_smul_subst_eq_nsmul
    φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero g x

end Residue

end HahnModule

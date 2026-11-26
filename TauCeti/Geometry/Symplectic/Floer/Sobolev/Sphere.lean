/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.SemiFredholm.Sphere
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Conformal
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# The linearized Floer operator on `W^{1,2}` of the Riemann sphere

Some Floer problems live on a closed domain: the comparison between the pair-of-pants product and
the quantum product deforms Floer data on the sphere with three poles, read in the coordinate
`w ∈ ℂ ≅ ℝ × ℝ` in which the poles are `0`, `1` and `∞`, and the data are unperturbed near `∞`.
This file realizes the linearized Floer operator `D_u` of such data on the Sobolev space of the
round metric of the sphere and proves that the realization has finite-dimensional kernel and
closed range.

In the coordinate `w` the round metric is `4 ρ |dw|²` for the conformal weight

`ρ(w) = (1 + |w|²)⁻²` (`TauCeti.Floer.sphereWeight`),

a conformal weight on the whole plane (`TauCeti.Floer.isWeight_sphereWeight`). The Sobolev space
`TauCeti.ConformalSobolev.H1 V univ ρ` of `TauCeti.Analysis.Sobolev.Conformal` is the completion
of the compactly supported sections of the plane in the norm `∫ (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)`,
the squared `W^{1,2}` norm of the sphere up to the constant `4` in front of `ρ`, since the
Dirichlet energy is conformally invariant. The weight is integrable
(`TauCeti.Floer.integrable_sphereWeight`): the round sphere has finite area.

* **The point at infinity has capacity zero.** The space is not smaller than `W^{1,2}` of the
  sphere near the point at infinity: the jet of every `C²` section that is bounded and has finite
  Dirichlet energy lies in it (`TauCeti.ConformalSobolev.toLp_jet_mem_H1_of_integrable`), although
  such a section need not have compact support in the plane. In particular the constant sections
  lie in it (`TauCeti.SymplecticForm.toLp_jet_const_mem_H1_sphereWeight`).

* **The coefficient field.** Suppose that on `‖w‖ ≥ T` the almost complex structures are a fixed
  `J₀` and the Hamiltonian perturbation vanishes. There the zeroth-order part of `D_u` vanishes,
  so the coefficient field of `D_u` on the conformal jets `(√ρ ξ, ∂s ξ, ∂t ξ)` is that of the
  Cauchy–Riemann operator `∂s + J₀ ∂t`; on the compact square `‖w‖ ≤ T` it is continuous. Hence
  it is essentially bounded on the plane, as for every conformal weight on the plane
  (`TauCeti.SymplecticForm.memLp_floerConformalJetCoeff_of_eq_base`), and
  `TauCeti.SymplecticForm.floerConformalSobolevOperator` realizes `D_u` from `W^{1,2}` to `L²`.
* **Finite-dimensional kernel and closed range.** If moreover `J(w, u w)` is compatible with `ω`,
  the semi-Fredholm estimate on the sphere,
  `exists_forall_integral_le_mul_integral_floerLinearization_add_of_eq_base` in the namespace
  `TauCeti.SymplecticForm`, bounds the norm of `W^{1,2}` by `‖D_u ξ‖_{L²}` and an `L²` norm on a
  compact square, and Peetre's argument gives finite-dimensional kernel
  (`finiteDimensional_ker_floerConformalSobolevOperator_sphereWeight_of_eq_base`) and closed range
  (`isClosed_range_floerConformalSobolevOperator_sphereWeight_of_eq_base`), both in the namespace
  `TauCeti.SymplecticForm`.

* **Constant sections.** For unperturbed data, a fixed `J₀` and zero Hamiltonian perturbation,
  the realization is the Cauchy–Riemann operator `∂s + J₀ ∂t` and vanishes on the constant
  sections (`floerConformalSobolevOperator_sphereWeight_const_apply_const`). For compatible `J₀`
  its finite-dimensional kernel therefore has dimension at least `dim V`
  (`finrank_le_finrank_ker_floerConformalSobolevOperator_sphereWeight_const`), both in the
  namespace `TauCeti.SymplecticForm`. These are the deformations of a constant sphere along the
  target.

The target is a symplectic vector space. The finiteness of the cokernel and the index are not
treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on the Sobolev realization and the semi-Fredholm estimate of real
  Cauchy–Riemann operators on closed surfaces.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  Floer problems on the sphere comparing the pair-of-pants and quantum products.
-/

public section

noncomputable section

open Set Function Filter MeasureTheory Metric TauCeti.ConformalSobolev
open scoped ENNReal

namespace TauCeti

namespace Floer

/-- The **conformal weight of the Riemann sphere** in the real coordinates `ℝ × ℝ ≃ ℂ`:
`ρ(w) = (1 + |w|²)⁻²`. The round metric of the sphere, of area `4π`, is `4 ρ |dw|²` in the
coordinate `w`. -/
def sphereWeight (z : ℝ × ℝ) : ℝ :=
  ((1 + z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹

theorem sphereWeight_apply (z : ℝ × ℝ) : sphereWeight z = ((1 + z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ :=
  (rfl)

/-- The conformal weight of the Riemann sphere is a conformal weight on the whole plane: it is
continuous and positive. -/
theorem isWeight_sphereWeight : IsWeight univ sphereWeight where
  isOpen := isOpen_univ
  continuousOn := by
    refine Continuous.continuousOn ?_
    unfold sphereWeight
    exact (by fun_prop : Continuous fun z : ℝ × ℝ ↦ (1 + z.1 ^ 2 + z.2 ^ 2) ^ 2).inv₀
      fun z ↦ by positivity
  pos z _ := by
    rw [sphereWeight_apply]
    positivity

/-- The conformal weight of the Riemann sphere is integrable on the plane: the round sphere has
finite area. It is at most `4 (1 + ‖w‖)⁻⁴`. -/
theorem integrable_sphereWeight : Integrable sphereWeight := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have h := (integrable_one_add_norm (E := ℝ × ℝ) (μ := volume) (r := 4)
    (by simp; norm_num)).const_mul 4
  refine h.mono' (continuousOn_univ.1 isWeight_sphereWeight.continuousOn).aestronglyMeasurable
    (.of_forall fun z ↦ ?_)
  have hm : ‖z‖ ^ 2 ≤ z.1 ^ 2 + z.2 ^ 2 := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    rcases max_choice |z.1| |z.2| with h | h <;> rw [h, sq_abs] <;> nlinarith [sq_nonneg z.1,
      sq_nonneg z.2]
  have hq : (1 + ‖z‖) ^ 4 / 4 ≤ (1 + z.1 ^ 2 + z.2 ^ 2) ^ 2 := by
    have h₁ : (1 + ‖z‖) ^ 2 ≤ 2 * (1 + z.1 ^ 2 + z.2 ^ 2) := by
      nlinarith [sq_nonneg (1 - ‖z‖)]
    have h₂ := pow_le_pow_left₀ (by positivity) h₁ 2
    nlinarith
  have hρ : 0 ≤ sphereWeight z := (isWeight_sphereWeight.pos z (mem_univ z)).le
  rw [Real.norm_of_nonneg hρ, sphereWeight_apply, Real.rpow_neg (by positivity),
    show (1 + ‖z‖) ^ (4 : ℝ) = (1 + ‖z‖) ^ (4 : ℕ) by norm_cast]
  calc ((1 + z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ ≤ ((1 + ‖z‖) ^ 4 / 4)⁻¹ := inv_anti₀ (by positivity) hq
    _ = 4 * ((1 + ‖z‖) ^ 4)⁻¹ := by rw [inv_div, div_eq_mul_inv]

end Floer

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {J : ℝ × ℝ → V → AlmostComplexStructure V}
  {J₀ : AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {T : ℝ}

/-- **Peetre's estimate on the sphere.** Under the hypotheses of the semi-Fredholm estimate on the
sphere, `exists_forall_integral_le_mul_integral_floerLinearization_add_of_eq_base`, the realization
of `D_u` on `W^{1,2}` of the sphere satisfies `‖x‖ ≤ A (‖D_u x‖ + ‖√ρ ξ‖_{L²(K)})` on the jets `x`
of test sections, for a compact square `K`. -/
private theorem exists_norm_le_floerConformalSobolevOperator_sphereWeight_of_eq_base
    (ω : SymplecticForm V) (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ContDiff ℝ 1 u) (hc : ∀ z, ω.Compatible (J z (u z))) :
    ∃ R A, ∀ x : H1 V univ sphereWeight,
      (x : Lp (V × V × V) 2 (volume.restrict univ)) ∈ jetSubmodule V univ sphereWeight →
        ‖x‖ ≤ A * (‖ω.floerConformalSobolevOperator univ sphereWeight
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u x‖ +
          ‖restrictWeightedValue V univ (closedBall 0 R) x‖) := by
  obtain ⟨R, C, -, hest⟩ :=
    exists_forall_integral_le_mul_integral_floerLinearization_add_of_eq_base hJ₀ hKs₀ hKt₀ hJ hKs
      hKt hu hc
  obtain ⟨A, hA⟩ :=
    ω.exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add_of_integral_le
      isWeight_sphereWeight
      (ω.memLp_floerConformalJetCoeff_of_eq_base isWeight_sphereWeight
        (J := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
        (fun z hz y ↦ by rw [hJ₀ z hz y]) hKs₀ hKt₀ hJ hKs hKt hu)
      (isCompact_closedBall 0 R) (subset_univ _) (C := C) fun ξ hξ ↦ by
        obtain ⟨hξs, hξc, -⟩ := mem_testSection_iff.1 hξ
        simpa only [setIntegral_univ, sphereWeight_apply, stdComplexLineReal_eq,
          stdComplexLineImag_eq] using hest hξs hξc
  exact ⟨R, A, hA⟩

/-- **The linearized operator on the sphere has finite-dimensional kernel on `W^{1,2}`.** Let the
Floer data `J`, `K_s`, `K_t` on the plane `ℝ × ℝ ≅ ℂ` be the fixed structure `J₀` and the zero
perturbation on `‖w‖ ≥ T`, a neighbourhood of the point at infinity of the sphere. Let `J` be `C¹`
and `K_s`, `K_t` be `C²` along a `C¹` map `u`, with `J(w, u w)` compatible. Then the realization of
`D_u` from `W^{1,2}` of the sphere to `L²` has finite-dimensional kernel. -/
theorem finiteDimensional_ker_floerConformalSobolevOperator_sphereWeight_of_eq_base
    (ω : SymplecticForm V)
    (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ContDiff ℝ 1 u) (hc : ∀ z, ω.Compatible (J z (u z))) :
    FiniteDimensional ℝ (ω.floerConformalSobolevOperator univ sphereWeight
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u).ker := by
  obtain ⟨R, A, hA⟩ := exists_norm_le_floerConformalSobolevOperator_sphereWeight_of_eq_base ω
    hJ₀ hKs₀ hKt₀ hJ hKs hKt hu hc
  exact finiteDimensional_ker_of_estimate isWeight_sphereWeight (isCompact_closedBall 0 R)
    (subset_univ _) _ hA

/-- **The linearized operator on the sphere has closed range on `W^{1,2}`.** Under the hypotheses
of `finiteDimensional_ker_floerConformalSobolevOperator_sphereWeight_of_eq_base`, the realization
of `D_u` from `W^{1,2}` of the sphere to `L²` has closed range. -/
theorem isClosed_range_floerConformalSobolevOperator_sphereWeight_of_eq_base
    (ω : SymplecticForm V)
    (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ContDiff ℝ 1 u) (hc : ∀ z, ω.Compatible (J z (u z))) :
    IsClosed (Set.range (ω.floerConformalSobolevOperator univ sphereWeight
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u)) := by
  obtain ⟨R, A, hA⟩ := exists_norm_le_floerConformalSobolevOperator_sphereWeight_of_eq_base ω
    hJ₀ hKs₀ hKt₀ hJ hKs hKt hu hc
  simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using
    isClosed_range_of_estimate isWeight_sphereWeight (isCompact_closedBall 0 R) (subset_univ _) _ hA

omit [FiniteDimensional ℝ V] in
/-- **Constant sections lie in `W^{1,2}` of the sphere.** The jet `(√ρ v, 0, 0)` of the constant
section `v` lies in the Sobolev space of the sphere, the closure of the jets of sections with
compact support in the plane: the point at infinity has capacity zero
(`TauCeti.ConformalSobolev.toLp_jet_mem_H1_of_integrable`). -/
theorem toLp_jet_const_mem_H1_sphereWeight (v : V) :
    (memLp_jet_of_integrable isWeight_sphereWeight integrable_sphereWeight contDiff_const
        (M := ‖v‖) (fun _ ↦ le_rfl) (by simp)).toLp (jet sphereWeight fun _ ↦ v) ∈
      H1 V univ sphereWeight :=
  toLp_jet_mem_H1_of_integrable isWeight_sphereWeight integrable_sphereWeight contDiff_const
    (fun _ ↦ le_rfl) (by simp)

omit [FiniteDimensional ℝ V] in
/-- The class of the jet of the constant section `v` is represented by `(√ρ v, 0, 0)`. -/
private theorem coeFn_toLp_jet_const (v : V) :
    ((⟨_, toLp_jet_const_mem_H1_sphereWeight v⟩ : H1 V univ sphereWeight) :
      Lp (V × V × V) 2 (volume.restrict univ)) =ᵐ[volume.restrict univ]
        fun z ↦ (√(sphereWeight z) • v, 0, 0) :=
  (memLp_jet_of_integrable isWeight_sphereWeight integrable_sphereWeight contDiff_const
    (M := ‖v‖) (fun _ ↦ le_rfl) (by simp)).coeFn_toLp.trans
      (.of_forall fun z ↦ by simp [jet_apply])

/-- For unperturbed data, a fixed `J₀` and zero Hamiltonian perturbation on the whole plane, the
coefficient field of the linearized operator on conformal jets is that of `∂s + J₀ ∂t`. -/
private theorem floerConformalJetCoeff_const (ω : SymplecticForm V) (ρ : ℝ × ℝ → ℝ)
    (J₀ : V →L[ℝ] V) (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerConformalJetCoeff ρ (fun _ _ ↦ J₀) (fun _ _ ↦ 0) (fun _ _ ↦ 0) u z =
      firstOrderJetCoeff J₀ 0 := by
  rw [floerConformalJetCoeff_def,
    ω.floerLinearizationCoeff_eq_zero_of_eq_base u (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl),
    smul_zero]

/-- **Constant sections are in the kernel of the unperturbed operator on the sphere.** For the
unperturbed Floer data on the sphere, a fixed `J₀` and zero Hamiltonian perturbation, the
realization of the linearized operator from `W^{1,2}` of the sphere is the Cauchy–Riemann operator
`∂s + J₀ ∂t` along every map `u`, and it vanishes on the constant sections. -/
theorem floerConformalSobolevOperator_sphereWeight_const_apply_const (ω : SymplecticForm V)
    (J₀ : V →L[ℝ] V) (u : ℝ × ℝ → V) (v : V) :
    ω.floerConformalSobolevOperator univ sphereWeight (fun _ _ ↦ J₀) (fun _ _ ↦ 0)
      (fun _ _ ↦ 0) u ⟨_, toLp_jet_const_mem_H1_sphereWeight v⟩ = 0 := by
  have hM : MemLp (ω.floerConformalJetCoeff sphereWeight (fun _ _ ↦ J₀) (fun _ _ ↦ 0)
      (fun _ _ ↦ 0) u) ∞ (volume.restrict univ) := by
    rw [funext (floerConformalJetCoeff_const ω sphereWeight J₀ u)]
    exact memLp_top_const _
  refine Lp.ext ?_
  filter_upwards [coeFn_floerConformalSobolevOperator ω hM _, coeFn_toLp_jet_const v,
    Lp.coeFn_zero V 2 (volume.restrict univ)] with z h₁ h₂ h₃
  rw [h₁, h₃, Pi.zero_apply, floerConformalJetCoeff_const, firstOrderJetCoeff_apply, h₂]
  simp

/-- The constant sections give an injective linear map from `V` to the kernel of the unperturbed
operator on the sphere. -/
private theorem exists_injective_linearMap_ker_floerConformalSobolevOperator_sphereWeight_const
    (ω : SymplecticForm V) (J₀ : V →L[ℝ] V) (u : ℝ × ℝ → V) :
    ∃ L : V →ₗ[ℝ] (ω.floerConformalSobolevOperator univ sphereWeight (fun _ _ ↦ J₀)
      (fun _ _ ↦ 0) (fun _ _ ↦ 0) u).ker, Function.Injective L := by
  let c : V → H1 V univ sphereWeight := fun v ↦ ⟨_, toLp_jet_const_mem_H1_sphereWeight v⟩
  let L : V →ₗ[ℝ] (ω.floerConformalSobolevOperator univ sphereWeight (fun _ _ ↦ J₀)
      (fun _ _ ↦ 0) (fun _ _ ↦ 0) u).ker :=
    { toFun := fun v ↦ ⟨c v, floerConformalSobolevOperator_sphereWeight_const_apply_const ω J₀
        u v⟩
      map_add' := fun v w ↦ by
        refine Subtype.ext (Subtype.ext (Lp.ext ?_))
        filter_upwards [coeFn_toLp_jet_const (v + w), coeFn_toLp_jet_const v,
          coeFn_toLp_jet_const w, Lp.coeFn_add (c v).val (c w).val] with z h₁ h₂ h₃ h₄
        simp only [Submodule.coe_add] at h₄ ⊢
        rw [h₁, h₄, Pi.add_apply, h₂, h₃]
        simp [smul_add]
      map_smul' := fun a v ↦ by
        refine Subtype.ext (Subtype.ext (Lp.ext ?_))
        filter_upwards [coeFn_toLp_jet_const (a • v), coeFn_toLp_jet_const v,
          Lp.coeFn_smul a (c v).val] with z h₁ h₂ h₃
        simp only [Submodule.coe_smul, RingHom.id_apply] at h₃ ⊢
        rw [h₁, h₃, Pi.smul_apply, h₂, Prod.smul_mk, Prod.smul_mk, smul_zero, smul_comm] }
  refine ⟨L, (injective_iff_map_eq_zero L).2 fun v hv ↦ ?_⟩
  have h0 : (c v).val = 0 := by simpa [L] using congrArg (fun x ↦ x.val.val) hv
  -- The weighted value `√ρ v` vanishes almost everywhere, and `ρ > 0`.
  have hae : (fun z ↦ (√(sphereWeight z) • v, (0 : V), (0 : V))) =ᵐ[volume] 0 := by
    rw [← Measure.restrict_univ (μ := volume)]
    refine (coeFn_toLp_jet_const v).symm.trans ?_
    have h0' : (⟨_, toLp_jet_const_mem_H1_sphereWeight v⟩ : H1 V univ sphereWeight).val = 0 := h0
    rw [h0']
    exact Lp.coeFn_zero _ _ _
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have : (ae (volume : Measure (ℝ × ℝ))).NeBot := ae_neBot.2 (NeZero.ne _)
  obtain ⟨z, hz⟩ := hae.exists
  have hρ : √(sphereWeight z) ≠ 0 :=
    (Real.sqrt_pos.2 (isWeight_sphereWeight.pos z (mem_univ z))).ne'
  simpa [hρ] using congrArg Prod.fst hz

/-- **The unperturbed operator on the sphere has kernel of dimension at least `dim V`.** For a
fixed `ω`-compatible `J₀` and zero Hamiltonian perturbation, the realization of the linearized
operator from `W^{1,2}` of the sphere has finite-dimensional kernel, which contains the constant
sections, a copy of `V`: the infinitesimal deformations of a constant sphere along the
target. -/
theorem finrank_le_finrank_ker_floerConformalSobolevOperator_sphereWeight_const
    (ω : SymplecticForm V) {J₀ : AlmostComplexStructure V} (hc : ω.Compatible J₀)
    (u : ℝ × ℝ → V) :
    Module.finrank ℝ V ≤ Module.finrank ℝ (ω.floerConformalSobolevOperator univ sphereWeight
      (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun _ _ ↦ 0) u).ker := by
  set J₁ : V →L[ℝ] V := J₀.toLinearMap.toContinuousLinearMap
  -- The operator does not depend on `u`, and along `u = 0` its kernel is finite-dimensional.
  have hu : ω.floerConformalSobolevOperator univ sphereWeight (fun _ _ ↦ J₁) (fun _ _ ↦ 0)
      (fun _ _ ↦ 0) u = ω.floerConformalSobolevOperator univ sphereWeight (fun _ _ ↦ J₁)
        (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 := by
    rw [floerConformalSobolevOperator_def, floerConformalSobolevOperator_def,
      funext (floerConformalJetCoeff_const ω sphereWeight J₁ u),
      funext (floerConformalJetCoeff_const ω sphereWeight J₁ 0)]
  have : FiniteDimensional ℝ (ω.floerConformalSobolevOperator univ sphereWeight
      (fun _ _ ↦ J₁) (fun _ _ ↦ 0) (fun _ _ ↦ 0) u).ker := by
    rw [hu]
    exact finiteDimensional_ker_floerConformalSobolevOperator_sphereWeight_of_eq_base ω
      (J := fun _ _ ↦ J₀) (T := 0) (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl)
      (fun _ ↦ contDiffAt_const) (fun _ ↦ contDiffAt_const) (fun _ ↦ contDiffAt_const)
      contDiff_const fun _ ↦ hc
  obtain ⟨L, hL⟩ :=
    exists_injective_linearMap_ker_floerConformalSobolevOperator_sphereWeight_const ω J₁ u
  exact LinearMap.finrank_le_finrank_of_injective hL

end SymplecticForm

end TauCeti

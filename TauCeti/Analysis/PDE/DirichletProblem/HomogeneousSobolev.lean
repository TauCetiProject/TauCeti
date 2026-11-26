/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Ellipticity.Basic
public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
public import TauCeti.Analysis.Sobolev.D1p0.Basic
import TauCeti.Analysis.InnerProductSpace.LaxMilgram
import TauCeti.Analysis.PDE.EnergyForm.Measurability
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.BilinearMap

/-!
# Weak solutions of finite energy in `D^{1,2}_0(Ω)`

Let `Ω ⊆ ℝⁿ` be open, let `a` be a measurable coefficient matrix on `Ω`, uniformly elliptic with
constants `0 < λ ≤ Λ` and not necessarily symmetric, and let `G ∈ L²(Ω; ℝⁿ)`. This file solves the
divergence-form problem

`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` in `Ω`, `u = 0` on `∂Ω`,

in the homogeneous Sobolev space `D^{1,2}_0(Ω)` (`TauCeti.D1p0`), the closure of the gradients of
test functions in `L²(Ω; ℝⁿ)`: there is exactly one `u ∈ D^{1,2}_0(Ω)`, recorded by its gradient
field, with `∫_Ω ⟨a ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩` for every test function `φ`
(`TauCeti.PDE.existsUnique_forall_integral_matrixBilinearForm_eq_integral_inner`), and its energy
is bounded by `λ ‖∇u‖_{L²} ≤ ‖G‖_{L²}`
(`TauCeti.PDE.mul_norm_le_of_forall_integral_matrixBilinearForm_eq_integral_inner`).

No boundedness of `Ω` is assumed, and no Poincaré inequality is needed, because the norm of
`D^{1,2}_0(Ω)` is the `L²` norm of the gradient alone and ellipticity makes the energy form
coercive for it. On the whole space this is the solution concept of the problem: for
`Ω = ℝⁿ` the solution need not be square integrable, so it does not lie in `H¹(ℝⁿ)` in general,
while its gradient does lie in `L²`. For `Ω = ℝⁿ`, the a priori `W^{1,p}` estimate for
coefficients of small mean oscillation holds for those solutions whose gradient lies in `Lᵖ`
(`TauCeti.PDE.exists_eLpNorm_le_of_forall_integral_matrixBilinearForm_eq_of_setAverage_le`).

The weak equation, stated against test functions, extends by density to every element of
`D^{1,2}_0(Ω)` in the place of `∇φ`
(`TauCeti.PDE.integral_matrixBilinearForm_eq_integral_inner_of_forall`): both sides are continuous
in the test field, the left one because the coefficients are essentially bounded.

On an open set `U ⊆ Ω`, a function in `H¹(U)` whose gradient agrees there with a solution
`u ∈ D^{1,2}_0(Ω)` solves the same equation weakly on `U`
(`TauCeti.PDE.energyFormH1_ofTestFunctionₗ_eq_integral_inner_of_gradient_ae_eq`).

## The argument

Integrating the bounded field of bilinear forms `a(x)` against two `L²` fields gives a continuous
bilinear form on `D^{1,2}_0(Ω)`, `B(u, w) = ∫_Ω ⟨a u, w⟩`, coercive with constant `λ` by
ellipticity. The datum defines the continuous functional `w ↦ ∫_Ω ⟨G, w⟩`. The Lax–Milgram theorem
(`IsCoercive.existsUnique_forall_eq`) gives the unique `u` with `B(u, ·) = ⟨G, ·⟩` on all of
`D^{1,2}_0(Ω)`, and by density this is the weak equation against test functions.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 5.8 (the Lax–Milgram theorem) and Section 8.2.
* M. Struwe, *Variational Methods*, 4th ed., Springer (2008), for `D^{1,2}_0(Ω)` as the completion
  of the test functions in the Dirichlet norm.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped Distributions ENNReal Gradient InnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {Lam : ℝ}

/-- The energy form `(u, w) ↦ ∫_Ω ⟨a u, w⟩` on `D^{1,2}_0(Ω)`, for an essentially bounded field of
bilinear forms. -/
private def energyFormD1p0
    (ha : AEStronglyMeasurable a (volume.restrict (Omega : Set (EuclideanSpace ℝ ι))))
    (hbd : ∀ x ∈ Omega, ‖matrixBilinearForm (a x)‖ ≤ Lam) :
    D1p0 volume Omega 2 →L[ℝ] D1p0 volume Omega 2 →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp
    (lpBilinearMap (𝕜 := ℝ) (E := EuclideanSpace ℝ ι) (F := EuclideanSpace ℝ ι) (G := ℝ)
      (p := 2) (q := 2) (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))
      ((memLp_top_matrixBilinearForm ha (ae_restrict_of_forall_mem Omega.isOpen.measurableSet
        hbd)).toLp fun x => matrixBilinearForm (a x))).flip
    (D1p0 volume Omega 2).subtypeL (D1p0 volume Omega 2).subtypeL

private theorem energyFormD1p0_apply
    (ha : AEStronglyMeasurable a (volume.restrict (Omega : Set (EuclideanSpace ℝ ι))))
    (hbd : ∀ x ∈ Omega, ‖matrixBilinearForm (a x)‖ ≤ Lam) (u w : D1p0 volume Omega 2) :
    energyFormD1p0 ha hbd u w = ∫ x in Omega, matrixBilinearForm (a x)
      ((w : Lp (EuclideanSpace ℝ ι) 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) x)
      ((u : Lp (EuclideanSpace ℝ ι) 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) x) := by
  rw [energyFormD1p0, ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.flip_apply,
    lpBilinearMap_apply]
  have hcoe : ((memLp_top_matrixBilinearForm ha (ae_restrict_of_forall_mem
      Omega.isOpen.measurableSet hbd)).toLp (fun x => matrixBilinearForm (a x)) :
      EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) =ᵐ[volume.restrict
        (Omega : Set (EuclideanSpace ℝ ι))] fun x => matrixBilinearForm (a x) :=
    MemLp.coeFn_toLp _
  refine integral_congr_ae ?_
  filter_upwards [hcoe] with x hx
  simp only [Submodule.subtypeL_apply, hx]

/-- The pairing `w ↦ ∫_Ω ⟨G, w⟩` of `D^{1,2}_0(Ω)` with a datum `G ∈ L²(Ω; ℝⁿ)`, as a continuous
linear functional. -/
private def datumD1p0 {G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hG : MemLp G 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) :
    StrongDual ℝ (D1p0 volume Omega 2) :=
  (innerSL ℝ (hG.toLp G)).comp (D1p0 volume Omega 2).subtypeL

private theorem datumD1p0_apply {G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hG : MemLp G 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι))))
    (w : D1p0 volume Omega 2) :
    datumD1p0 hG w = ∫ x in Omega, ⟪G x, (w : Lp (EuclideanSpace ℝ ι) 2
      (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) x⟫_ℝ := by
  rw [datumD1p0, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    Submodule.subtypeL_apply]
  exact L2.toLp_inner_of_ae_eq hG Filter.EventuallyEq.rfl

/-- An integral over `Ω` against the test field of `φ` in `D^{1,2}_0(Ω)` is the integral against
the gradient of `φ`. -/
private theorem integral_coe_ofTestFunctionₗ
    (F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι → ℝ) (φ : 𝓓(Omega, ℝ)) :
    ∫ x in Omega, F x ((D1p0.ofTestFunctionₗ volume Omega 2 φ : Lp (EuclideanSpace ℝ ι) 2
        (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) x) =
      ∫ x in Omega, F x (∇ (φ : EuclideanSpace ℝ ι → ℝ) x) := by
  rw [D1p0.coe_ofTestFunctionₗ]
  refine integral_congr_ae ?_
  filter_upwards [gradientTestFunctionLp_apply_ae (mu := volume) 2 φ] with x hx
  rw [hx]

/-- **The weak equation against every finite-energy test field.** Let `a` be a.e. strongly
measurable and bounded by `Λ` on `Ω`, let `G ∈ L²(Ω; ℝⁿ)`, and let `u ∈ D^{1,2}_0(Ω)` satisfy
`∫_Ω ⟨a ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩` for every test function `φ`. Then
`∫_Ω ⟨a ∇u, w⟩ = ∫_Ω ⟨G, w⟩` for every `w ∈ D^{1,2}_0(Ω)`. -/
theorem integral_matrixBilinearForm_eq_integral_inner_of_forall
    (ha : AEStronglyMeasurable a (volume.restrict (Omega : Set (EuclideanSpace ℝ ι))))
    (hbd : ∀ x ∈ Omega, ‖matrixBilinearForm (a x)‖ ≤ Lam)
    {G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hG : MemLp G 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι))))
    {u : D1p0 volume Omega 2}
    (hu : ∀ φ : 𝓓(Omega, ℝ), ∫ x in Omega, matrixBilinearForm (a x)
        (∇ (φ : EuclideanSpace ℝ ι → ℝ) x)
        ((u : Lp (EuclideanSpace ℝ ι) 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) x) =
      ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ)
    (w : D1p0 volume Omega 2) :
    ∫ x in Omega, matrixBilinearForm (a x)
        ((w : Lp (EuclideanSpace ℝ ι) 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) x)
        ((u : Lp (EuclideanSpace ℝ ι) 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) x) =
      ∫ x in Omega, ⟪G x,
        (w : Lp (EuclideanSpace ℝ ι) 2
            (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) x⟫_ℝ := by
  refine (D1p0.denseRange_ofTestFunctionₗ (mu := volume) (Omega := Omega) (p := 2)).induction_on w
    (isClosed_eq ?_ ((datumD1p0 hG).continuous.congr (datumD1p0_apply hG))) fun φ => ?_
  · exact (energyFormD1p0 ha hbd u).continuous.congr fun w => energyFormD1p0_apply ha hbd u w
  · exact (integral_coe_ofTestFunctionₗ (fun x v => matrixBilinearForm (a x) v
        ((u : Lp (EuclideanSpace ℝ ι) 2
          (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) x)) φ).trans
      ((hu φ).trans (integral_coe_ofTestFunctionₗ (fun x v => ⟪G x, v⟫_ℝ) φ).symm)

/-- **A local potential of a finite-energy solution solves the equation.** Let
`u ∈ D^{1,2}_0(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly on `Ω`, that is
`∫_Ω ⟨a ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩` for every test function `φ` on `Ω`, and let `v ∈ H¹(U)` on an open
set `U ⊆ Ω` have gradient `u` almost everywhere on `U`. Then `v` solves the same equation weakly
on `U`. -/
theorem energyFormH1_ofTestFunctionₗ_eq_integral_inner_of_gradient_ae_eq
    {U : Opens (EuclideanSpace ℝ ι)} (hU : U ≤ Omega) {G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {u : D1p0 volume Omega 2}
    (hu : ∀ φ : 𝓓(Omega, ℝ), ∫ x in Omega, matrixBilinearForm (a x)
        (∇ (φ : EuclideanSpace ℝ ι → ℝ) x)
        ((u : Lp (EuclideanSpace ℝ ι) 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) x) =
      ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ)
    {v : W1p volume U 2}
    (hv : W1p.gradient v =ᵐ[volume.restrict (U : Set (EuclideanSpace ℝ ι))]
      (u : Lp (EuclideanSpace ℝ ι) 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))))
    (φ : 𝓓(U, ℝ)) :
    energyFormH1 a 0 0 v (W1p.ofTestFunctionₗ volume U 2 φ) =
      ∫ x in U, ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ := by
  -- A test function on `U` is one on `Ω`, and its gradient vanishes off `U`.
  set ψ : 𝓓(Omega, ℝ) := TestFunction.monoCLM ℝ φ
  have hψ : (ψ : EuclideanSpace ℝ ι → ℝ) = φ := TestFunction.coe_monoCLM_of_le le_rfl hU φ
  have hsupp : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)) \ U,
      ∇ (φ : EuclideanSpace ℝ ι → ℝ) x = 0 := fun x hx =>
    Function.notMem_support.1 fun h => hx.2 (support_gradient_testFunction_subset φ h)
  have hφU : ∀ᵐ x ∂volume.restrict (U : Set (EuclideanSpace ℝ ι)),
      W1p.gradient (W1p.ofTestFunctionₗ volume U 2 φ) x = ∇ (φ : EuclideanSpace ℝ ι → ℝ) x := by
    rw [W1p.gradient_ofTestFunctionₗ]
    exact gradientTestFunctionLp_apply_ae 2 φ
  rw [energyFormH1_zero_zero_eq_setIntegral]
  calc _ = ∫ x in U, matrixBilinearForm (a x) (∇ (φ : EuclideanSpace ℝ ι → ℝ) x)
            ((u : Lp (EuclideanSpace ℝ ι) 2
              (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) x) := by
        refine integral_congr_ae ?_
        filter_upwards [hv, hφU] with x hvx hφx
        rw [hvx, hφx]
    _ = ∫ x in U, ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ := by
        rw [← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Omega.isOpen.measurableSet
            (SetLike.coe_subset_coe.mpr hU) fun x hx => by simp [hsupp x hx],
          ← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Omega.isOpen.measurableSet
            (SetLike.coe_subset_coe.mpr hU) fun x hx => by simp [hsupp x hx], ← hψ]
        exact hu ψ

variable [DecidableEq ι] {lam : ℝ}

/-- The energy form on `D^{1,2}_0(Ω)` of a uniformly elliptic coefficient is coercive with the
ellipticity constant `λ`. -/
private theorem mul_norm_mul_norm_le_energyFormD1p0 (hell : UniformlyEllipticOn Omega a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Omega : Set (EuclideanSpace ℝ ι))))
    (u : D1p0 volume Omega 2) :
    lam * ‖u‖ * ‖u‖ ≤
      energyFormD1p0 ha (fun _ hx => hell.opNorm_matrixBilinearForm_le hx) u u := by
  set U : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι :=
    ⇑(u : Lp (EuclideanSpace ℝ ι) 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι))))
  have hU : MemLp U 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι))) := Lp.memLp _
  have hsq : Integrable (fun x => ‖U x‖ ^ 2) (volume.restrict (Omega : Set (EuclideanSpace ℝ ι))) :=
    hU.integrable_norm_pow two_ne_zero
  have hnorm : ‖u‖ * ‖u‖ = ∫ x in Omega, ‖U x‖ ^ 2 := by
    rw [← sq, ← real_inner_self_eq_norm_sq, D1p0.inner_def]
    simp only [real_inner_self_eq_norm_sq, U]
  have hint : Integrable (fun x => matrixBilinearForm (a x) (U x) (U x))
      (volume.restrict (Omega : Set (EuclideanSpace ℝ ι))) :=
    (memLp_top_matrixBilinearForm ha (ae_restrict_of_forall_mem Omega.isOpen.measurableSet
      fun _ hx => hell.opNorm_matrixBilinearForm_le hx)).integrable_bilinear_apply hU hU
  rw [mul_assoc, hnorm, ← integral_const_mul, energyFormD1p0_apply]
  refine integral_mono_ae (hsq.const_mul lam) hint ?_
  filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with x hx
  rw [matrixBilinearForm_self]
  exact hell.lower_bound hx (U x)

private theorem isCoercive_energyFormD1p0 (hell : UniformlyEllipticOn Omega a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) :
    IsCoercive (energyFormD1p0 ha fun _ hx => hell.opNorm_matrixBilinearForm_le hx) :=
  ⟨lam, hell.pos, mul_norm_mul_norm_le_energyFormD1p0 hell ha⟩

/-- **Existence and uniqueness of finite-energy weak solutions.** Let `a` be a.e. strongly
measurable on an open set `Ω ⊆ ℝⁿ` and uniformly elliptic there with constants `0 < λ ≤ Λ`, not
necessarily symmetric, and let `G ∈ L²(Ω; ℝⁿ)`. Then exactly one `u ∈ D^{1,2}_0(Ω)` solves
`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly, that is `∫_Ω ⟨a ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩` for every test function
`φ`. The set `Ω` need not be bounded. -/
theorem existsUnique_forall_integral_matrixBilinearForm_eq_integral_inner
    (hell : UniformlyEllipticOn Omega a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Omega : Set (EuclideanSpace ℝ ι))))
    {G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hG : MemLp G 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) :
    ∃! u : D1p0 volume Omega 2, ∀ φ : 𝓓(Omega, ℝ), ∫ x in Omega, matrixBilinearForm (a x)
        (∇ (φ : EuclideanSpace ℝ ι → ℝ) x)
        ((u : Lp (EuclideanSpace ℝ ι) 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) x) =
      ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ := by
  have hbd : ∀ x ∈ Omega, ‖matrixBilinearForm (a x)‖ ≤ Lam :=
    fun _ hx => hell.opNorm_matrixBilinearForm_le hx
  -- On test fields the weak equation is the Lax–Milgram equation, which extends by density.
  have hiff : ∀ u : D1p0 volume Omega 2,
      (∀ w, energyFormD1p0 ha hbd u w = datumD1p0 hG w) ↔ ∀ φ : 𝓓(Omega, ℝ), ∫ x in Omega,
        matrixBilinearForm (a x) (∇ (φ : EuclideanSpace ℝ ι → ℝ) x)
          ((u : Lp (EuclideanSpace ℝ ι) 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) x) =
        ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ := by
    intro u
    constructor
    · intro h φ
      have h' := h (D1p0.ofTestFunctionₗ volume Omega 2 φ)
      rw [energyFormD1p0_apply, datumD1p0_apply] at h'
      exact (integral_coe_ofTestFunctionₗ (fun x v => matrixBilinearForm (a x) v
          ((u : Lp (EuclideanSpace ℝ ι) 2
            (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) x)) φ).symm.trans
        (h'.trans (integral_coe_ofTestFunctionₗ (fun x v => ⟪G x, v⟫_ℝ) φ))
    · intro h w
      rw [energyFormD1p0_apply, datumD1p0_apply]
      exact integral_matrixBilinearForm_eq_integral_inner_of_forall ha hbd hG h w
  obtain ⟨u, hu, huniq⟩ :=
    (isCoercive_energyFormD1p0 hell ha).existsUnique_forall_eq (datumD1p0 hG)
  exact ⟨u, (hiff u).1 hu, fun v hv => huniq v ((hiff v).2 hv)⟩

/-- **The energy estimate for finite-energy weak solutions.** Let `a` be uniformly elliptic on `Ω`
with constants `0 < λ ≤ Λ` and a.e. strongly measurable there, let `G ∈ L²(Ω; ℝⁿ)`, and let
`u ∈ D^{1,2}_0(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly. Then `λ ‖∇u‖_{L²(Ω)} ≤ ‖G‖_{L²(Ω)}`. -/
theorem mul_norm_le_of_forall_integral_matrixBilinearForm_eq_integral_inner
    (hell : UniformlyEllipticOn Omega a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Omega : Set (EuclideanSpace ℝ ι))))
    {G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hG : MemLp G 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι))))
    {u : D1p0 volume Omega 2}
    (hu : ∀ φ : 𝓓(Omega, ℝ), ∫ x in Omega, matrixBilinearForm (a x)
        (∇ (φ : EuclideanSpace ℝ ι → ℝ) x)
        ((u : Lp (EuclideanSpace ℝ ι) 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) x) =
      ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ) :
    lam * ‖u‖ ≤ (eLpNorm G 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))).toReal := by
  have hbd : ∀ x ∈ Omega, ‖matrixBilinearForm (a x)‖ ≤ Lam :=
    fun _ hx => hell.opNorm_matrixBilinearForm_le hx
  -- Testing the equation with `u` itself: `λ ‖u‖² ≤ B(u, u) = ⟪G, u⟫ ≤ ‖G‖ ‖u‖`.
  have hB := mul_norm_mul_norm_le_energyFormD1p0 hell ha u
  rw [energyFormD1p0_apply, integral_matrixBilinearForm_eq_integral_inner_of_forall ha hbd hG hu u,
    ← L2.toLp_inner_of_ae_eq hG Filter.EventuallyEq.rfl] at hB
  have hCS := (real_inner_le_norm (hG.toLp G)
    (u : Lp (EuclideanSpace ℝ ι) 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι))))).trans_eq
    (by rw [Lp.norm_toLp, Submodule.norm_coe])
  rcases (norm_nonneg u).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact ENNReal.toReal_nonneg
  · exact le_of_mul_le_mul_right (hB.trans hCS) hpos

end PDE

end TauCeti

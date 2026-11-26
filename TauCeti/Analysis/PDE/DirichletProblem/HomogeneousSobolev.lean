/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Ellipticity.Basic
public import TauCeti.Analysis.Sobolev.D1p0.Basic
import TauCeti.Analysis.InnerProductSpace.LaxMilgram
import TauCeti.Analysis.PDE.EnergyForm.Measurability
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
while its gradient does lie in `L²`. The `W^{1,p}` estimate for coefficients of
small mean oscillation holds for these solutions
(`TauCeti.PDE.exists_eLpNorm_le_of_forall_integral_matrixBilinearForm_eq_of_setAverage_le`), and
they are the solutions of the adjoint problem that a duality argument pairs with.

The weak equation, stated against test functions, extends by density to every element of
`D^{1,2}_0(Ω)` in the place of `∇φ`
(`TauCeti.PDE.integral_matrixBilinearForm_eq_integral_inner_of_forall`): both sides are continuous
in the test field, the left one because the coefficients are essentially bounded.

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

/-- An a.e. strongly measurable coefficient matrix bounded by `Λ` on `Ω` gives an essentially
bounded field of bilinear forms on `Ω`. -/
private theorem memLp_top_matrixBilinearForm
    (ha : AEStronglyMeasurable a (volume.restrict (Omega : Set (EuclideanSpace ℝ ι))))
    (hbd : ∀ x ∈ Omega, ‖matrixBilinearForm (a x)‖ ≤ Lam) :
    MemLp (fun x => matrixBilinearForm (a x)) ⊤
      (volume.restrict (Omega : Set (EuclideanSpace ℝ ι))) := by
  refine memLp_top_of_bound (f := fun x => matrixBilinearForm (a x)) ?_ Lam ?_
  · simpa only [matrixBilinearFormLinear_apply] using
      (matrixBilinearFormLinear (n := ι)).continuous.comp_aestronglyMeasurable ha
  · filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with x hx
    exact hbd x hx

/-- The energy form `(u, w) ↦ ∫_Ω ⟨a u, w⟩` on `D^{1,2}_0(Ω)`, for an essentially bounded field of
bilinear forms. -/
private def energyFormD1p0
    (ha : AEStronglyMeasurable a (volume.restrict (Omega : Set (EuclideanSpace ℝ ι))))
    (hbd : ∀ x ∈ Omega, ‖matrixBilinearForm (a x)‖ ≤ Lam) :
    D1p0 volume Omega 2 →L[ℝ] D1p0 volume Omega 2 →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp
    (lpBilinearMap (𝕜 := ℝ) (E := EuclideanSpace ℝ ι) (F := EuclideanSpace ℝ ι) (G := ℝ)
      (p := 2) (q := 2) (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))
      ((memLp_top_matrixBilinearForm ha hbd).toLp fun x => matrixBilinearForm (a x))).flip
    (D1p0 volume Omega 2).subtypeL (D1p0 volume Omega 2).subtypeL

private theorem energyFormD1p0_apply
    (ha : AEStronglyMeasurable a (volume.restrict (Omega : Set (EuclideanSpace ℝ ι))))
    (hbd : ∀ x ∈ Omega, ‖matrixBilinearForm (a x)‖ ≤ Lam) (u w : D1p0 volume Omega 2) :
    energyFormD1p0 ha hbd u w = ∫ x in Omega, matrixBilinearForm (a x)
      ((w : Lp (EuclideanSpace ℝ ι) 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) x)
      ((u : Lp (EuclideanSpace ℝ ι) 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) x) := by
  rw [energyFormD1p0, ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.flip_apply,
    lpBilinearMap_apply]
  have hcoe : ((memLp_top_matrixBilinearForm ha hbd).toLp (fun x => matrixBilinearForm (a x)) :
      EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) =ᵐ[volume.restrict
        (Omega : Set (EuclideanSpace ℝ ι))] fun x => matrixBilinearForm (a x) :=
    (memLp_top_matrixBilinearForm ha hbd).coeFn_toLp
  refine integral_congr_ae ?_
  filter_upwards [hcoe] with x hx
  simp only [Submodule.subtypeL_apply, hx]

/-- The pairing `w ↦ ∫_Ω ⟨G, w⟩` of `D^{1,2}_0(Ω)` with a datum `G ∈ L²(Ω; ℝⁿ)` is continuous. -/
private theorem continuous_integral_inner {G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hG : MemLp G 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) :
    Continuous fun w : D1p0 volume Omega 2 => ∫ x in Omega, ⟪G x,
      (w : Lp (EuclideanSpace ℝ ι) 2
          (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) x⟫_ℝ := by
  refine ((innerSL ℝ (hG.toLp G)).comp (D1p0 volume Omega 2).subtypeL).continuous.congr fun w => ?_
  rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, Submodule.subtypeL_apply,
    L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hG.coeFn_toLp] with x hx
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
    (isClosed_eq ?_ (continuous_integral_inner hG)) fun φ => ?_
  · exact (energyFormD1p0 ha hbd u).continuous.congr fun w => energyFormD1p0_apply ha hbd u w
  · have hφ := gradientTestFunctionLp_apply_ae (mu := volume) (Omega := Omega) 2 φ
    rw [D1p0.coe_ofTestFunctionₗ]
    refine (integral_congr_ae ?_).trans ((hu φ).trans (integral_congr_ae ?_))
    · filter_upwards [hφ] with x hx
      rw [hx]
    · filter_upwards [hφ] with x hx
      rw [hx]

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
  have hmeas : AEStronglyMeasurable (fun x => matrixBilinearForm (a x))
      (volume.restrict (Omega : Set (EuclideanSpace ℝ ι))) :=
    (memLp_top_matrixBilinearForm ha fun _ hx =>
      hell.opNorm_matrixBilinearForm_le hx).aestronglyMeasurable
  have hint : Integrable (fun x => matrixBilinearForm (a x) (U x) (U x))
      (volume.restrict (Omega : Set (EuclideanSpace ℝ ι))) := by
    refine (hsq.const_mul Lam).mono'
      (aestronglyMeasurable_matrixBilinearForm_apply hmeas hU.aestronglyMeasurable
        hU.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with x hx
    calc ‖matrixBilinearForm (a x) (U x) (U x)‖
        ≤ ‖matrixBilinearForm (a x)‖ * ‖U x‖ * ‖U x‖ :=
          (matrixBilinearForm (a x)).le_opNorm₂ (U x) (U x)
      _ ≤ Lam * ‖U x‖ * ‖U x‖ := by
          gcongr
          exact hell.opNorm_matrixBilinearForm_le hx
      _ = Lam * ‖U x‖ ^ 2 := by ring
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
  -- The datum as a continuous linear functional on `D^{1,2}_0(Ω)`.
  set ℓ : StrongDual ℝ (D1p0 volume Omega 2) :=
    (innerSL ℝ (hG.toLp G)).comp (D1p0 volume Omega 2).subtypeL
  have hℓ : ∀ w : D1p0 volume Omega 2, ℓ w = ∫ x in Omega, ⟪G x,
      (w : Lp (EuclideanSpace ℝ ι) 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) x⟫_ℝ :=
    fun w => by
      rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, Submodule.subtypeL_apply,
        L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hG.coeFn_toLp] with x hx
      rw [hx]
  -- On test fields the weak equation is the Lax–Milgram equation, which extends by density.
  have hiff : ∀ u : D1p0 volume Omega 2,
      (∀ w, energyFormD1p0 ha hbd u w = ℓ w) ↔ ∀ φ : 𝓓(Omega, ℝ), ∫ x in Omega,
        matrixBilinearForm (a x) (∇ (φ : EuclideanSpace ℝ ι → ℝ) x)
          ((u : Lp (EuclideanSpace ℝ ι) 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) x) =
        ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ := by
    intro u
    have hφ := fun φ : 𝓓(Omega, ℝ) =>
      gradientTestFunctionLp_apply_ae (mu := volume) (Omega := Omega) 2 φ
    constructor
    · intro h φ
      have h' := h (D1p0.ofTestFunctionₗ volume Omega 2 φ)
      rw [energyFormD1p0_apply, hℓ, D1p0.coe_ofTestFunctionₗ] at h'
      refine (integral_congr_ae ?_).trans (h'.trans (integral_congr_ae ?_))
      · filter_upwards [hφ φ] with x hx
        rw [hx]
      · filter_upwards [hφ φ] with x hx
        rw [hx]
    · intro h w
      rw [energyFormD1p0_apply, hℓ]
      exact integral_matrixBilinearForm_eq_integral_inner_of_forall ha hbd hG h w
  obtain ⟨u, hu, huniq⟩ := (isCoercive_energyFormD1p0 hell ha).existsUnique_forall_eq ℓ
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
  have hpair : ∫ x in Omega, ⟪G x,
      (u : Lp (EuclideanSpace ℝ ι) 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) x⟫_ℝ =
      ⟪hG.toLp G,
        (u : Lp (EuclideanSpace ℝ ι) 2
            (volume.restrict (Omega : Set (EuclideanSpace ℝ ι))))⟫_ℝ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hG.coeFn_toLp] with x hx
    rw [hx]
  rw [energyFormD1p0_apply, integral_matrixBilinearForm_eq_integral_inner_of_forall ha hbd hG hu u,
    hpair] at hB
  have hCS := (real_inner_le_norm (hG.toLp G)
    (u : Lp (EuclideanSpace ℝ ι) 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι))))).trans_eq
    (by rw [Lp.norm_toLp, Submodule.norm_coe])
  rcases (norm_nonneg u).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact ENNReal.toReal_nonneg
  · exact le_of_mul_le_mul_right (hB.trans hCS) hpos

end PDE

end TauCeti

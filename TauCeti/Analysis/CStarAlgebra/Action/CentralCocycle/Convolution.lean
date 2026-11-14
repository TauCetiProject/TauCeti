/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CentralCocycle.Basic
public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Basic
public import TauCeti.Analysis.CStarAlgebra.Action.Involution

/-!
# Cocycle-twisted convolution and involution on compactly supported coefficient functions

For a point-norm continuous action `α` of a topological group `G` on a C⋆-algebra `A`, a normalized
continuous central multiplier cocycle `ω : CentralCocycle α`, and a measure `μ` on `G`, the
`ω`-twisted convolution of compactly supported continuous functions `f g : C_c(G, A)` is

`(f *_ω g) s = ∫ r, (ω r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s))) ∂μ`,

and, when `G` is locally compact, the `ω`-twisted involution is

`f^{*_ω} s = c(s) • (star (ω s s⁻¹ : 𝓜(ℂ, A))).fst (α s (star (f s⁻¹)))`,

where `c` is Mathlib's modular character (`Δ(s)⁻¹` in Williams's convention). Because `ω` takes
values in the unitary center of `𝓜(ℂ, A)`, the right action of `ω(r, r⁻¹s)` agrees with its left
action, preserves the norm of coefficients, and at `ω = 1` both operations reduce to the untwisted
`CStarAction.convolution` and `CStarAction.twistedInvolution`.

Neither local compactness, separability, nor σ-finiteness of `μ` is assumed for
`twistedConvolution`, its support bound, associativity, or `L¹` submultiplicativity; local
compactness enters only where `Measure.modularCharacter` appears in `twistedInvolution`.

## Main definitions

* `TauCeti.CStarAction.CentralCocycle.twistedConvolution`: the `ω`-twisted convolution as a
  `ℂ`-bilinear map `C_c(G, A) →ₗ[ℂ] C_c(G, A) →ₗ[ℂ] C_c(G, A)`.
* `TauCeti.CStarAction.CentralCocycle.twistedInvolution`: the `ω`-twisted conjugate-linear
  involution `C_c(G, A) →ₗ⋆[ℂ] C_c(G, A)`.

## Main statements

* `TauCeti.CStarAction.CentralCocycle.one_twistedConvolution` and `one_twistedInvolution`:
  agreement with `α.convolution μ` and `α.twistedInvolution` at `ω = 1`.
* `TauCeti.CStarAction.CentralCocycle.twistedConvolution_assoc`: associativity for left-invariant
  measures, proved via the cocycle identity in `𝓜(ℂ, A)`.
* `TauCeti.CStarAction.CentralCocycle.integral_norm_twistedConvolution_le`: `L¹`
  submultiplicativity.
* `TauCeti.CStarAction.CentralCocycle.twistedInvolution_twistedInvolution`: involutivity, proved
  from `ω s s⁻¹ = α.multiplier s (ω s⁻¹ s)`.
* `TauCeti.CStarAction.CentralCocycle.twistedInvolution_twistedConvolution`:
  `(f *_ω g)^{*_ω} = g^{*_ω} *_ω f^{*_ω}` for left-invariant measures.

## References

* Judith A. Packer and Iain Raeburn, *Twisted crossed products of C*-algebras*, Math. Proc.
  Cambridge Philos. Soc. 106 (1989), 293–311, Section 2.
* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory Function
open scoped CompactlySupported MultiplierAlgebra NNReal Pointwise

namespace TauCeti.CStarAction.CentralCocycle

variable {G A : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]
  {α : CStarAction G A}

/-! ### The cocycle-twisted integrand -/

section Integrand

variable (ω : CentralCocycle α) (f g : C_c(G, A))

private theorem mem_support_of_twistedIntegrand_ne_zero {s r : G}
    (hsr : (ω r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s))) ≠ 0) :
    r ∈ support f ∧ r⁻¹ * s ∈ support g :=
  ⟨mem_support.2 fun hf => hsr (by simp [hf]), mem_support.2 fun hg => hsr (by simp [hg])⟩

private theorem mem_tsupport_of_twistedIntegrand_ne_zero {s r : G}
    (hsr : (ω r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s))) ≠ 0) :
    r ∈ tsupport f ∧ r⁻¹ * s ∈ tsupport g :=
  (mem_support_of_twistedIntegrand_ne_zero ω f g hsr).imp
    (subset_tsupport _ ·) (subset_tsupport _ ·)

private theorem snd_cocycle_assoc (r t s : G) (a b z : A) :
    (ω (r * t) (t⁻¹ * (r⁻¹ * s)) : 𝓜(ℂ, A)).snd
        ((ω r t : 𝓜(ℂ, A)).snd (a * α r b) * α r z) =
      (ω r (r⁻¹ * s) : 𝓜(ℂ, A)).snd
        (a * α r ((ω t (t⁻¹ * (r⁻¹ * s)) : 𝓜(ℂ, A)).snd (b * z))) := by
  apply DoubleCentralizer.coe_injective (𝕜 := ℂ)
  calc (((ω (r * t) (t⁻¹ * (r⁻¹ * s)) : 𝓜(ℂ, A)).snd
        ((ω r t : 𝓜(ℂ, A)).snd (a * α r b) * α r z) : A) : 𝓜(ℂ, A))
      = (a : 𝓜(ℂ, A)) * (α r b : 𝓜(ℂ, A)) *
          ((ω r t : 𝓜(ℂ, A)) * (α r z : 𝓜(ℂ, A))) *
          (ω (r * t) (t⁻¹ * (r⁻¹ * s)) : 𝓜(ℂ, A)) := by
        simp only [← DoubleCentralizer.coe_mul_eq_coe_snd, DoubleCentralizer.coe_mul, mul_assoc]
    _ = (a : 𝓜(ℂ, A)) * (α r b : 𝓜(ℂ, A)) * (α r z : 𝓜(ℂ, A)) *
          ((ω r t : 𝓜(ℂ, A)) * (ω (r * t) (t⁻¹ * (r⁻¹ * s)) : 𝓜(ℂ, A))) := by
        rw [(ω.commute r t _).eq]
        simp only [mul_assoc]
    _ = (a : 𝓜(ℂ, A)) * (α r b : 𝓜(ℂ, A)) * (α r z : 𝓜(ℂ, A)) *
          (α.multiplier r (ω t (t⁻¹ * (r⁻¹ * s)) : 𝓜(ℂ, A)) *
            (ω r (r⁻¹ * s) : 𝓜(ℂ, A))) := by
        have hcoc := ω.mul_cocycle r t (t⁻¹ * (r⁻¹ * s))
        rw [mul_inv_cancel_left] at hcoc
        rw [← hcoc]
    _ = (((ω r (r⁻¹ * s) : 𝓜(ℂ, A)).snd
          (a * α r ((ω t (t⁻¹ * (r⁻¹ * s)) : 𝓜(ℂ, A)).snd (b * z))) : A) : 𝓜(ℂ, A)) := by
        simp only [← DoubleCentralizer.coe_mul_eq_coe_snd, DoubleCentralizer.coe_mul,
          ← α.multiplier_coe, map_mul, mul_assoc]

variable [IsTopologicalGroup G]

private theorem continuous_twistedIntegrand :
    Continuous (uncurry fun s r =>
      (ω r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s)))) := by
  rw [uncurry_def]
  exact ω.continuous_snd_apply _root_.continuous_snd
    (_root_.continuous_snd.inv.mul _root_.continuous_fst) (by fun_prop)

/-- The `ω`-twisted convolution integrand is integrable against any measure finite on compacts. -/
theorem integrable_twistedIntegrand [MeasurableSpace G] [OpensMeasurableSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (s : G) :
    Integrable (fun r => (ω r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s)))) μ :=
  ((continuous_twistedIntegrand ω f g).comp (.prodMk_right s)).integrable_of_hasCompactSupport
    (f.hasCompactSupport.mono' fun _ hr =>
      (mem_tsupport_of_twistedIntegrand_ne_zero ω f g hr).1)

end Integrand

/-! ### Cocycle-twisted convolution -/

section Convolution

variable [IsTopologicalGroup G] [MeasurableSpace G] [OpensMeasurableSpace G]
  (ω : CentralCocycle α) (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (f g h : C_c(G, A))

private def twistedConvolutionAux : C_c(G, A) where
  toFun s := ∫ r, (ω r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s))) ∂μ
  continuous_toFun := continuous_integral_of_compact_support μ f.hasCompactSupport
    (continuous_twistedIntegrand ω f g)
    fun _ _ h => (mem_tsupport_of_twistedIntegrand_ne_zero ω f g h).1
  hasCompactSupport' := hasCompactSupport_integral_of_inv_mul_mem μ f.hasCompactSupport
    g.hasCompactSupport fun _ _ => mem_tsupport_of_twistedIntegrand_ne_zero ω f g

private theorem twistedConvolutionAux_apply (s : G) :
    twistedConvolutionAux ω μ f g s =
      ∫ r, (ω r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s))) ∂μ :=
  rfl

/-- The `ω`-twisted convolution
`(f *_ω g) s = ∫ r, (ω r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s))) ∂μ` on `C_c(G, A)`,
bundled as a `ℂ`-bilinear map. -/
def twistedConvolution : C_c(G, A) →ₗ[ℂ] C_c(G, A) →ₗ[ℂ] C_c(G, A) :=
  LinearMap.mk₂ ℂ (twistedConvolutionAux ω μ)
    (fun f₁ f₂ g => CompactlySupportedContinuousMap.ext fun s => by
      simp only [twistedConvolutionAux_apply, CompactlySupportedContinuousMap.coe_add,
        Pi.add_apply, add_mul, map_add]
      exact integral_add (ω.integrable_twistedIntegrand f₁ g μ s)
        (ω.integrable_twistedIntegrand f₂ g μ s))
    (fun c f g => CompactlySupportedContinuousMap.ext fun s => by
      simp only [twistedConvolutionAux_apply, CompactlySupportedContinuousMap.coe_smul,
        Pi.smul_apply, smul_mul_assoc, map_smul]
      exact integral_smul c _)
    (fun f g₁ g₂ => CompactlySupportedContinuousMap.ext fun s => by
      simp only [twistedConvolutionAux_apply, CompactlySupportedContinuousMap.coe_add,
        Pi.add_apply, map_add, mul_add]
      exact integral_add (ω.integrable_twistedIntegrand f g₁ μ s)
        (ω.integrable_twistedIntegrand f g₂ μ s))
    (fun c f g => CompactlySupportedContinuousMap.ext fun s => by
      simp only [twistedConvolutionAux_apply, CompactlySupportedContinuousMap.coe_smul,
        Pi.smul_apply, map_smul, mul_smul_comm]
      exact integral_smul c _)

@[simp]
theorem twistedConvolution_apply (s : G) :
    ω.twistedConvolution μ f g s =
      ∫ r, (ω r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s))) ∂μ :=
  (rfl)

/-- For the trivial cocycle `1`, `twistedConvolution` agrees with `CStarAction.convolution`. -/
@[simp]
theorem one_twistedConvolution :
    (1 : CentralCocycle α).twistedConvolution μ = α.convolution μ := by
  ext f g s
  simp

/-- The support of an `ω`-twisted convolution lies in the product of the supports. -/
theorem support_twistedConvolution_subset :
    support (ω.twistedConvolution μ f g) ⊆ support f * support g :=
  support_integral_subset_mul μ fun _ _ => mem_support_of_twistedIntegrand_ne_zero ω f g

/-- Left multiplication by a coefficient commutes with `ω`-twisted convolution:
`(a • f) *_ω g = a • (f *_ω g)`. -/
theorem smul_twistedConvolution (a : A) :
    ω.twistedConvolution μ (a • f) g = a • ω.twistedConvolution μ f g := by
  ext s
  simp only [twistedConvolution_apply, CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc, DoubleCentralizer.snd_mul _ a]
  exact integral_const_mul_of_integrable (ω.integrable_twistedIntegrand f g μ s)

section LeftInvariant

variable [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- `ω`-twisted convolution with respect to a left-invariant measure is associative. -/
theorem twistedConvolution_assoc :
    ω.twistedConvolution μ (ω.twistedConvolution μ f g) h =
      ω.twistedConvolution μ f (ω.twistedConvolution μ g h) := by
  ext s
  simp only [twistedConvolution_apply]
  set F : G → G → A := fun t r =>
    (ω t (t⁻¹ * s) : 𝓜(ℂ, A)).snd
      ((ω r (r⁻¹ * t) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * t))) * α t (h (t⁻¹ * s)))
  have hcont : Continuous (uncurry F) := by
    rw [uncurry_def]
    refine ω.continuous_snd_apply _root_.continuous_fst
      (_root_.continuous_fst.inv.mul continuous_const) (Continuous.mul ?_ (by fun_prop))
    exact ω.continuous_snd_apply _root_.continuous_snd
      (_root_.continuous_snd.inv.mul _root_.continuous_fst) (by fun_prop)
  have hsupp : HasCompactSupport (uncurry F) :=
    hasCompactSupport_uncurry_of_inv_mul_mem f.hasCompactSupport g.hasCompactSupport
      fun t r htr => mem_tsupport_of_twistedIntegrand_ne_zero ω f g fun hz =>
        htr (by simp [F, hz])
  calc ∫ t, (ω t (t⁻¹ * s) : 𝓜(ℂ, A)).snd
          ((∫ r, (ω r (r⁻¹ * t) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * t))) ∂μ) *
            α t (h (t⁻¹ * s))) ∂μ
      = ∫ t, ∫ r, F t r ∂μ ∂μ := by
        congr 1 with t
        have hint_mul : Integrable (fun r =>
            (ω r (r⁻¹ * t) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * t))) * α t (h (t⁻¹ * s))) μ := by
          simpa using ((ContinuousLinearMap.mul ℝ A).flip (α t (h (t⁻¹ * s)))).integrable_comp
            (ω.integrable_twistedIntegrand f g μ t)
        rw [← integral_mul_const_of_integrable (ω.integrable_twistedIntegrand f g μ t),
          ← ((ω t (t⁻¹ * s) : 𝓜(ℂ, A)).snd).integral_comp_comm hint_mul]
    _ = ∫ r, ∫ t, F t r ∂μ ∂μ := integral_integral_swap_of_hasCompactSupport hcont hsupp
    _ = ∫ r, (ω r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f r * α r
          (∫ t, (ω t (t⁻¹ * (r⁻¹ * s)) : 𝓜(ℂ, A)).snd
            (g t * α t (h (t⁻¹ * (r⁻¹ * s)))) ∂μ)) ∂μ := by
        congr 1 with r
        have hint : Integrable (fun t =>
            (ω t (t⁻¹ * (r⁻¹ * s)) : 𝓜(ℂ, A)).snd
              (g t * α t (h (t⁻¹ * (r⁻¹ * s))))) μ :=
          ω.integrable_twistedIntegrand g h μ (r⁻¹ * s)
        have hint' : Integrable (fun t =>
            α r ((ω t (t⁻¹ * (r⁻¹ * s)) : 𝓜(ℂ, A)).snd
              (g t * α t (h (t⁻¹ * (r⁻¹ * s)))))) μ := by
          simpa using (α.toContinuousLinearMap r).integrable_comp hint
        have hint'' : Integrable (fun t =>
            f r * α r ((ω t (t⁻¹ * (r⁻¹ * s)) : 𝓜(ℂ, A)).snd
              (g t * α t (h (t⁻¹ * (r⁻¹ * s)))))) μ := by
          simpa using (ContinuousLinearMap.mul ℝ A (f r)).integrable_comp hint'
        have hα : α r (∫ t, (ω t (t⁻¹ * (r⁻¹ * s)) : 𝓜(ℂ, A)).snd
              (g t * α t (h (t⁻¹ * (r⁻¹ * s)))) ∂μ) =
            ∫ t, α r ((ω t (t⁻¹ * (r⁻¹ * s)) : 𝓜(ℂ, A)).snd
              (g t * α t (h (t⁻¹ * (r⁻¹ * s))))) ∂μ := by
          simpa using ((α.toContinuousLinearMap r).integral_comp_comm hint).symm
        rw [hα, ← integral_const_mul_of_integrable hint',
          ← ((ω r (r⁻¹ * s) : 𝓜(ℂ, A)).snd).integral_comp_comm hint'',
          ← integral_mul_left_eq_self (F · r) r]
        congr 1 with t
        simp only [F, inv_mul_cancel_left, mul_inv_rev, mul_assoc, CStarAction.mul_apply]
        exact snd_cocycle_assoc ω r t s (f r) (g t) (α t (h (t⁻¹ * (r⁻¹ * s))))

/-- The `L¹` norm is submultiplicative for `ω`-twisted convolution with respect to a
left-invariant measure. -/
theorem integral_norm_twistedConvolution_le :
    ∫ s, ‖ω.twistedConvolution μ f g s‖ ∂μ ≤ (∫ s, ‖f s‖ ∂μ) * ∫ s, ‖g s‖ ∂μ := by
  have hsupp : ∀ s r, ‖f r‖ * ‖g (r⁻¹ * s)‖ ≠ 0 → r ∈ tsupport f ∧ r⁻¹ * s ∈ tsupport g :=
    fun s r hsr => ⟨subset_tsupport _ (mem_support.2 fun hf => hsr (by simp [hf])),
      subset_tsupport _ (mem_support.2 fun hg => hsr (by simp [hg]))⟩
  have hcont : Continuous (uncurry fun s r => ‖f r‖ * ‖g (r⁻¹ * s)‖) := by
    rw [uncurry_def]
    fun_prop
  have hNcont := continuous_integral_of_compact_support μ f.hasCompactSupport hcont
    fun s r h => (hsupp s r h).1
  have hNsupp := hasCompactSupport_integral_of_inv_mul_mem μ f.hasCompactSupport
    g.hasCompactSupport hsupp
  calc ∫ s, ‖ω.twistedConvolution μ f g s‖ ∂μ
      ≤ ∫ s, ∫ r, ‖f r‖ * ‖g (r⁻¹ * s)‖ ∂μ ∂μ := by
        refine integral_mono
          ((ω.twistedConvolution μ f g).continuous.norm.integrable_of_hasCompactSupport
            (ω.twistedConvolution μ f g).hasCompactSupport.norm)
          (hNcont.integrable_of_hasCompactSupport hNsupp) fun s => ?_
        rw [twistedConvolution_apply]
        refine norm_integral_le_of_norm_le
          ((hcont.comp (.prodMk_right s)).integrable_of_hasCompactSupport
            (f.hasCompactSupport.mono' fun r hr => (hsupp s r hr).1)) (.of_forall fun r => ?_)
        rw [DoubleCentralizer.norm_unitary_snd_apply]
        simpa [StarAlgEquiv.norm_map] using norm_mul_le (f r) (α r (g (r⁻¹ * s)))
    _ = ∫ r, ∫ s, ‖f r‖ * ‖g (r⁻¹ * s)‖ ∂μ ∂μ :=
        integral_integral_swap_of_hasCompactSupport hcont
          (hasCompactSupport_uncurry_of_inv_mul_mem f.hasCompactSupport g.hasCompactSupport hsupp)
    _ = ∫ r, ‖f r‖ * ∫ s, ‖g s‖ ∂μ ∂μ := by
        congr 1 with r
        rw [integral_const_mul]
        congr 1
        exact integral_mul_left_eq_self (fun s => ‖g s‖) r⁻¹
    _ = (∫ s, ‖f s‖ ∂μ) * ∫ s, ‖g s‖ ∂μ := integral_mul_const _ _

end LeftInvariant

end Convolution

/-! ### Cocycle-twisted involution -/

section Involution

variable [IsTopologicalGroup G] [LocallyCompactSpace G] (ω : CentralCocycle α)

/-- The `ω`-twisted, conjugate-linear involution on compactly supported coefficient functions:
`f^{*_ω}(s) = c(s) • (star (ω s s⁻¹ : 𝓜(ℂ, A))).fst (α s (star (f s⁻¹)))`. -/
def twistedInvolution : C_c(G, A) →ₗ⋆[ℂ] C_c(G, A) where
  toFun f :=
    { toFun s :=
        ((Measure.modularCharacter s : ℝ) : ℂ) •
          (star (ω s s⁻¹ : 𝓜(ℂ, A))).fst (α s (star (f s⁻¹)))
      continuous_toFun :=
        (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
          continuous_modularCharacter)).smul
            (ω.continuous_star_fst_apply continuous_id continuous_inv
              (α.continuous_apply continuous_id (f.continuous.comp continuous_inv).star))
      hasCompactSupport' :=
        (f.hasCompactSupport.comp_homeomorph (Homeomorph.inv G)).mono fun s hs => by
          have hz : f s⁻¹ ≠ 0 := fun hz => hs (by simp [hz])
          exact hz }
  map_add' f g := by
    ext s
    simp [map_add, smul_add]
  map_smul' z f := by
    ext s
    simp only [CompactlySupportedContinuousMap.smul_apply, star_smul, map_smul,
      starRingEnd_apply]
    exact smul_comm _ _ _

/-- The pointwise formula for `ω.twistedInvolution`. -/
@[simp]
theorem twistedInvolution_apply (f : C_c(G, A)) (s : G) :
    ω.twistedInvolution f s =
      ((Measure.modularCharacter s : ℝ) : ℂ) •
        (star (ω s s⁻¹ : 𝓜(ℂ, A))).fst (α s (star (f s⁻¹))) :=
  (rfl)

/-- For the trivial cocycle `1`, `twistedInvolution` agrees with `CStarAction.twistedInvolution`. -/
@[simp]
theorem one_twistedInvolution :
    (1 : CentralCocycle α).twistedInvolution = α.twistedInvolution := by
  ext f s
  simp

/-- The norm of an `ω`-involuted coefficient includes precisely the modular weight. -/
@[simp↓]
theorem norm_twistedInvolution_apply (f : C_c(G, A)) (s : G) :
    ‖ω.twistedInvolution f s‖ = (Measure.modularCharacter s : ℝ) * ‖f s⁻¹‖ := by
  rw [twistedInvolution_apply, ← Unitary.coe_star, norm_smul,
    DoubleCentralizer.norm_unitary_fst_apply]
  simp [StarAlgEquiv.norm_map]

/-- `ω`-twisted involution vanishes at `s` iff the original function vanishes at `s⁻¹`. -/
@[simp↓]
theorem twistedInvolution_apply_eq_zero_iff (f : C_c(G, A)) (s : G) :
    ω.twistedInvolution f s = 0 ↔ f s⁻¹ = 0 := by
  rw [← norm_eq_zero, norm_twistedInvolution_apply]
  have hc : (Measure.modularCharacter s : ℝ) ≠ 0 := by
    rw [modularCharacter_apply]
    exact NNReal.coe_ne_zero.mpr (Measure.modularCharacterFun_pos s).ne'
  simp [hc]

/-- The support of `ω.twistedInvolution f` is the inverse support `(support f)⁻¹`. -/
@[simp]
theorem support_twistedInvolution (f : C_c(G, A)) :
    support (ω.twistedInvolution f) = (support f)⁻¹ := by
  ext s
  exact not_congr (ω.twistedInvolution_apply_eq_zero_iff f s)

/-- The topological support of `ω.twistedInvolution f` is `(tsupport f)⁻¹`. -/
@[simp]
theorem tsupport_twistedInvolution (f : C_c(G, A)) :
    tsupport (ω.twistedInvolution f) = (tsupport f)⁻¹ := by
  simp only [tsupport, support_twistedInvolution, ← inv_closure]

/-- Applying `ω.twistedInvolution` twice recovers the original coefficient function. -/
@[simp]
theorem twistedInvolution_twistedInvolution (f : C_c(G, A)) :
    ω.twistedInvolution (ω.twistedInvolution f) = f := by
  ext s
  have hc : Measure.modularCharacter s * Measure.modularCharacter s⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hc' : ((Measure.modularCharacter s : ℝ) : ℂ) *
      ((Measure.modularCharacter s⁻¹ : ℝ) : ℂ) = 1 := by
    exact_mod_cast hc
  simp only [twistedInvolution_apply, inv_inv, star_smul, map_smul, Complex.star_def,
    Complex.conj_ofReal, smul_smul, hc', one_smul]
  apply DoubleCentralizer.coe_injective (𝕜 := ℂ)
  rw [← DoubleCentralizer.mul_coe_eq_coe_fst, ← α.multiplier_coe, DoubleCentralizer.coe_star,
    ← DoubleCentralizer.mul_coe_eq_coe_fst, star_mul, star_star, ← DoubleCentralizer.coe_star,
    map_star, star_star, map_mul, α.multiplier_coe, CStarAction.apply_inv_apply,
    ω.multiplier_apply_inv_mul_self, ← mul_assoc, (ω.commute_star s s⁻¹ (f s : 𝓜(ℂ, A))).eq,
    mul_assoc, (Unitary.mem_iff.mp (ω s s⁻¹).prop).1, mul_one]

omit [IsTopologicalGroup G] [LocallyCompactSpace G] in
private theorem twistedInvolution_integrand_eq (s t : G) (a b : A) :
    (star (ω s s⁻¹ : 𝓜(ℂ, A))).fst
        (α s (star ((ω t (t⁻¹ * s⁻¹) : 𝓜(ℂ, A)).snd (a * α t b)))) =
      (ω (s * t) t⁻¹ : 𝓜(ℂ, A)).snd
        ((star (ω (s * t) (t⁻¹ * s⁻¹) : 𝓜(ℂ, A))).fst (α (s * t) (star b)) *
          α (s * t) ((star (ω t⁻¹ t : 𝓜(ℂ, A))).fst (α t⁻¹ (star a)))) := by
  apply DoubleCentralizer.coe_injective (𝕜 := ℂ)
  have hinv_t : α.multiplier (s * t) (star (ω t⁻¹ t : 𝓜(ℂ, A))) =
      α.multiplier s (star (ω t t⁻¹ : 𝓜(ℂ, A))) := by
    rw [map_mul, StarAlgEquiv.mul_apply, ω.multiplier_star_apply_inv_mul_self]
  have hphase : star (ω s s⁻¹ : 𝓜(ℂ, A)) * α.multiplier s (star (ω t (t⁻¹ * s⁻¹) : 𝓜(ℂ, A))) =
      star (ω (s * t) (t⁻¹ * s⁻¹) : 𝓜(ℂ, A)) *
        α.multiplier s (star (ω t t⁻¹ : 𝓜(ℂ, A))) * (ω (s * t) t⁻¹ : 𝓜(ℂ, A)) := by
    have h1 : α.multiplier s (ω t (t⁻¹ * s⁻¹) : 𝓜(ℂ, A)) * (ω s s⁻¹ : 𝓜(ℂ, A)) =
        (ω s t : 𝓜(ℂ, A)) * (ω (s * t) (t⁻¹ * s⁻¹) : 𝓜(ℂ, A)) := by
      simpa [mul_inv_cancel_left] using ω.mul_cocycle s t (t⁻¹ * s⁻¹)
    have h1' := congrArg star h1
    simp only [star_mul, ← map_star] at h1'
    rw [h1', ω.star_eq_multiplier_star_mul s t, mul_assoc]
  set Y : 𝓜(ℂ, A) := (α (s * t) (star b) : 𝓜(ℂ, A))
  set X : 𝓜(ℂ, A) := (α s (star a) : 𝓜(ℂ, A))
  have hLHS : (((star (ω s s⁻¹ : 𝓜(ℂ, A))).fst
        (α s (star ((ω t (t⁻¹ * s⁻¹) : 𝓜(ℂ, A)).snd (a * α t b)))) : A) : 𝓜(ℂ, A)) =
      (star (ω s s⁻¹ : 𝓜(ℂ, A)) * α.multiplier s (star (ω t (t⁻¹ * s⁻¹) : 𝓜(ℂ, A)))) *
        (Y * X) := by
    rw [← DoubleCentralizer.mul_coe_eq_coe_fst, ← α.multiplier_coe, DoubleCentralizer.coe_star,
      ← DoubleCentralizer.coe_mul_eq_coe_snd, DoubleCentralizer.coe_mul, star_mul, star_mul,
      map_mul, map_mul, ← DoubleCentralizer.coe_star, ← DoubleCentralizer.coe_star,
      α.multiplier_coe, α.multiplier_coe, ← map_star (α t), ← CStarAction.mul_apply]
    simp only [X, Y, mul_assoc]
  have hRHS : (((ω (s * t) t⁻¹ : 𝓜(ℂ, A)).snd
        ((star (ω (s * t) (t⁻¹ * s⁻¹) : 𝓜(ℂ, A))).fst (α (s * t) (star b)) *
          α (s * t) ((star (ω t⁻¹ t : 𝓜(ℂ, A))).fst (α t⁻¹ (star a)))) : A) : 𝓜(ℂ, A)) =
      star (ω (s * t) (t⁻¹ * s⁻¹) : 𝓜(ℂ, A)) * Y *
        (α.multiplier s (star (ω t t⁻¹ : 𝓜(ℂ, A))) * X) * (ω (s * t) t⁻¹ : 𝓜(ℂ, A)) := by
    rw [← DoubleCentralizer.coe_mul_eq_coe_snd, DoubleCentralizer.coe_mul,
      ← DoubleCentralizer.mul_coe_eq_coe_fst,
      ← α.multiplier_coe (s * t) ((star (ω t⁻¹ t : 𝓜(ℂ, A))).fst _),
      ← DoubleCentralizer.mul_coe_eq_coe_fst, map_mul (α.multiplier (s * t)), α.multiplier_coe,
      α.mul_apply s t ((α t⁻¹) _), CStarAction.apply_inv_apply, hinv_t]
  rw [hLHS, hRHS]
  calc (star (ω s s⁻¹ : 𝓜(ℂ, A)) * α.multiplier s (star (ω t (t⁻¹ * s⁻¹) : 𝓜(ℂ, A)))) *
          (Y * X)
      = star (ω (s * t) (t⁻¹ * s⁻¹) : 𝓜(ℂ, A)) *
          (α.multiplier s (star (ω t t⁻¹ : 𝓜(ℂ, A))) *
            ((ω (s * t) t⁻¹ : 𝓜(ℂ, A)) * (Y * X))) := by
        rw [hphase]
        simp only [mul_assoc]
    _ = star (ω (s * t) (t⁻¹ * s⁻¹) : 𝓜(ℂ, A)) *
          (α.multiplier s (star (ω t t⁻¹ : 𝓜(ℂ, A))) *
            (Y * X * (ω (s * t) t⁻¹ : 𝓜(ℂ, A)))) := by
        rw [(ω.commute (s * t) t⁻¹ (Y * X)).eq]
    _ = star (ω (s * t) (t⁻¹ * s⁻¹) : 𝓜(ℂ, A)) * Y *
          (α.multiplier s (star (ω t t⁻¹ : 𝓜(ℂ, A))) * X) * (ω (s * t) t⁻¹ : 𝓜(ℂ, A)) := by
        have hcomm : Commute (α.multiplier s (star (ω t t⁻¹ : 𝓜(ℂ, A)))) Y := by
          rw [Commute, SemiconjBy, ← (α.multiplier s).apply_symm_apply Y, ← map_mul,
            (ω.commute_star t t⁻¹ _).eq, map_mul]
        rw [← mul_assoc (α.multiplier s _), ← mul_assoc (α.multiplier s _), hcomm.eq]
        simp only [mul_assoc]

/-- The `ω`-twisted involution reverses `ω`-twisted convolution for a left-invariant measure:
`(f *_ω g)^{*_ω} = g^{*_ω} *_ω f^{*_ω}`. -/
theorem twistedInvolution_twistedConvolution [MeasurableSpace G] [OpensMeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (f g : C_c(G, A)) :
    ω.twistedInvolution (ω.twistedConvolution μ f g) =
      ω.twistedConvolution μ (ω.twistedInvolution g) (ω.twistedInvolution f) := by
  ext s
  have hint : Integrable (fun t =>
      (ω t (t⁻¹ * s⁻¹) : 𝓜(ℂ, A)).snd (f t * α t (g (t⁻¹ * s⁻¹)))) μ :=
    ω.integrable_twistedIntegrand f g μ s⁻¹
  have hstar : star (∫ t, (ω t (t⁻¹ * s⁻¹) : 𝓜(ℂ, A)).snd (f t * α t (g (t⁻¹ * s⁻¹))) ∂μ) =
      ∫ t, star ((ω t (t⁻¹ * s⁻¹) : 𝓜(ℂ, A)).snd (f t * α t (g (t⁻¹ * s⁻¹)))) ∂μ := by
    simpa using ((starL ℂ : A ≃L⋆[ℂ] A).toContinuousLinearMap.integral_comp_commSL
      (by simp) hint).symm
  have hint_star : Integrable (fun t =>
      star ((ω t (t⁻¹ * s⁻¹) : 𝓜(ℂ, A)).snd (f t * α t (g (t⁻¹ * s⁻¹))))) μ := by
    simpa using (starL ℂ : A ≃L⋆[ℂ] A).toContinuousLinearMap.integrable_comp hint
  have hint_α : Integrable (fun t =>
      α s (star ((ω t (t⁻¹ * s⁻¹) : 𝓜(ℂ, A)).snd (f t * α t (g (t⁻¹ * s⁻¹)))))) μ := by
    simpa using (α.toContinuousLinearMap s).integrable_comp hint_star
  have hα : α s (∫ t, star ((ω t (t⁻¹ * s⁻¹) : 𝓜(ℂ, A)).snd (f t * α t (g (t⁻¹ * s⁻¹)))) ∂μ) =
      ∫ t, α s (star ((ω t (t⁻¹ * s⁻¹) : 𝓜(ℂ, A)).snd (f t * α t (g (t⁻¹ * s⁻¹))))) ∂μ := by
    simpa using ((α.toContinuousLinearMap s).integral_comp_comm hint_star).symm
  have hc (r : G) : ((Measure.modularCharacter r : ℝ) : ℂ) *
      ((Measure.modularCharacter (r⁻¹ * s) : ℝ) : ℂ) = (Measure.modularCharacter s : ℝ) := by
    exact_mod_cast by rw [← map_mul, mul_inv_cancel_left]
  simp only [twistedInvolution_apply, twistedConvolution_apply, map_smul, smul_mul_smul_comm, hc]
  rw [integral_smul, ← integral_mul_left_eq_self
    (fun r => (ω r (r⁻¹ * s) : 𝓜(ℂ, A)).snd
      ((star (ω r r⁻¹ : 𝓜(ℂ, A))).fst (α r (star (g r⁻¹))) *
        α r ((star (ω (r⁻¹ * s) (r⁻¹ * s)⁻¹ : 𝓜(ℂ, A))).fst
          (α (r⁻¹ * s) (star (f (r⁻¹ * s)⁻¹)))))) s]
  congr 1
  rw [hstar, hα, ← ((star (ω s s⁻¹ : 𝓜(ℂ, A))).fst).integral_comp_comm hint_α]
  congr 1 with t
  simp only [mul_inv_rev, inv_mul_cancel_right, inv_inv]
  exact twistedInvolution_integrand_eq ω s t (f t) (g (t⁻¹ * s⁻¹))

end Involution

end TauCeti.CStarAction.CentralCocycle

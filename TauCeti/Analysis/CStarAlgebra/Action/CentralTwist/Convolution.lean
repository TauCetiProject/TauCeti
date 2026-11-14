/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CentralTwist.Basic
public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Algebra

/-!
# Cocycle-twisted convolution and involution on `C_c(G, A)`

Given a point-norm continuous action `α` of a topological group `G` on a possibly nonunital
C⋆-algebra `A` and a normalized continuous central multiplier cocycle `ω : CentralCocycle α`, the
*twisted convolution* against a measure `μ` on `G` is

`twistedConvolution ω μ f g s = ∫ r, (ω.value r (r⁻¹ * s)).snd (f r * α r (g (r⁻¹ * s))) ∂μ`,

and the *twisted involution* on compactly supported continuous coefficient functions is

`ω.involution f s = c(s) • (star (ω.value s s⁻¹)).fst (α s (star (f s⁻¹)))`,

where `c` is Mathlib's modular character (`c(s) = Δ(s)⁻¹`). Because `ω` is central in `𝓜(ℂ, A)`,
the left and right actions of `ω(r, r⁻¹ * s)` on `A` give the same value, and for `ω = 1` both
operations reduce to `α.convolution μ` and `α.twistedInvolution`.

For any measure finite on compacts, `twistedConvolution` preserves continuity and compact support
with `support (f *_ω g) ⊆ support f * support g`, giving a `ℂ`-bilinear map `ω.convolution μ` on
`C_c(G, A)`. When `μ` is left-invariant, the `2`-cocycle identity makes `ω.convolution μ`
associative, unitary norm preservation gives `∫ ‖f *_ω g‖ ≤ (∫ ‖f‖) * ∫ ‖g‖`, and `ω.involution`
is involutive (using `α'_s(ω(s⁻¹, s)) = ω(s, s⁻¹)`), reverses products
`(f *_ω g)^{*_ω} = g^{*_ω} *_ω f^{*_ω}`, and preserves the `L¹` norm of any Haar measure. No
unitality, separability, second countability, or σ-finiteness is assumed.

## Main definitions

* `TauCeti.CStarAction.twistedConvolution`: cocycle-twisted convolution of functions `G → A`.
* `TauCeti.CStarAction.CentralCocycle.convolution`: cocycle-twisted convolution bundled as a
  `ℂ`-bilinear map on `C_c(G, A)`.
* `TauCeti.CStarAction.CentralCocycle.involution`: cocycle-twisted conjugate-linear involution on
  `C_c(G, A)`.

## Main statements

* `TauCeti.CStarAction.CentralCocycle.support_convolution_subset`:
  `support (f *_ω g) ⊆ support f * support g`.
* `TauCeti.CStarAction.CentralCocycle.convolution_assoc`: associativity of `ω.convolution μ` for
  left-invariant `μ`.
* `TauCeti.CStarAction.CentralCocycle.integral_norm_convolution_le`: `L¹` submultiplicativity.
* `TauCeti.CStarAction.CentralCocycle.involution_involution`: involutivity of `ω.involution`.
* `TauCeti.CStarAction.CentralCocycle.integral_norm_involution`: `L¹` isometry of `ω.involution`
  against a Haar measure.
* `TauCeti.CStarAction.CentralCocycle.involution_convolution`:
  `ω.involution (ω.convolution μ f g) = ω.convolution μ (ω.involution g) (ω.involution f)`.

## References

* Judith A. Packer and Iain Raeburn, *Twisted crossed products of C*-algebras*, Math. Proc.
  Cambridge Philos. Soc. 106 (1989), 293–311, Proposition 2.4.
* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2, for the modular character
  convention `c = Δ⁻¹`.
-/

public section

noncomputable section

open MeasureTheory Function
open scoped CompactlySupported Pointwise MultiplierAlgebra NNReal

namespace TauCeti.CStarAction

variable {G A : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]

/-! ### Unbundled twisted convolution -/

/-- The twisted convolution `(f *_ω g)(s) = ∫ r, f(r) α_r(g(r⁻¹s)) ω(r, r⁻¹s) dμ(r)` of a
continuous central multiplier cocycle `ω`, with `ω(r, r⁻¹s)` acting on the right through
`𝓜(ℂ, A)`. -/
def twistedConvolution [MeasurableSpace G] {α : CStarAction G A} (ω : CentralCocycle α)
    (μ : Measure G) (f g : G → A) (s : G) : A :=
  ∫ r, (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s))) ∂μ

/-- By centrality of `ω`, the right multiplier action in `twistedConvolution` agrees with the left
multiplier action. -/
theorem twistedConvolution_eq_integral_fst [MeasurableSpace G] {α : CStarAction G A}
    (ω : CentralCocycle α) (μ : Measure G) (f g : G → A) (s : G) :
    twistedConvolution ω μ f g s =
      ∫ r, (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).fst (f r * α r (g (r⁻¹ * s))) ∂μ := by
  simp_rw [twistedConvolution, ω.fst_eq_snd]

/-- For the trivial cocycle `1`, `twistedConvolution` reduces to the untwisted action convolution
integral. -/
@[simp]
theorem one_twistedConvolution [MeasurableSpace G] {α : CStarAction G A} (μ : Measure G)
    (f g : G → A) (s : G) :
    twistedConvolution (1 : CentralCocycle α) μ f g s =
      ∫ r, f r * α r (g (r⁻¹ * s)) ∂μ := by
  simp [twistedConvolution]

namespace CentralCocycle

variable {α : CStarAction G A} (ω : CentralCocycle α)

/-! ### Continuity, compact support, and bilinearity on `C_c(G, A)` -/

section Convolution

private theorem mem_support_of_integrand_ne_zero (f g : C_c(G, A)) {s r : G}
    (hsr : (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s))) ≠ 0) :
    r ∈ support f ∧ r⁻¹ * s ∈ support g :=
  ⟨mem_support.2 fun hf => hsr (by simp [hf]), mem_support.2 fun hg => hsr (by simp [hg])⟩

private theorem mem_tsupport_of_integrand_ne_zero (f g : C_c(G, A)) {s r : G}
    (hsr : (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s))) ≠ 0) :
    r ∈ tsupport f ∧ r⁻¹ * s ∈ tsupport g :=
  (ω.mem_support_of_integrand_ne_zero f g hsr).imp (subset_tsupport _ ·) (subset_tsupport _ ·)

variable [IsTopologicalGroup G]

private theorem continuous_integrand (f g : C_c(G, A)) :
    Continuous (uncurry fun s r =>
      (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s)))) := by
  rw [uncurry_def]
  fun_prop

variable [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

/-- The cocycle-twisted convolution integrand is integrable against any measure finite on compact
sets. -/
theorem integrable_integrand (f g : C_c(G, A)) (s : G) :
    Integrable (fun r => (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s)))) μ :=
  ((ω.continuous_integrand f g).comp (.prodMk_right s)).integrable_of_hasCompactSupport
    (f.hasCompactSupport.mono' fun _ hr => (ω.mem_tsupport_of_integrand_ne_zero f g hr).1)

private def convolutionAux (f g : C_c(G, A)) : C_c(G, A) where
  toFun := twistedConvolution ω μ f g
  continuous_toFun := continuous_integral_of_compact_support μ f.hasCompactSupport
    (ω.continuous_integrand f g) fun _ _ h => (ω.mem_tsupport_of_integrand_ne_zero f g h).1
  hasCompactSupport' := hasCompactSupport_integral_of_inv_mul_mem μ f.hasCompactSupport
    g.hasCompactSupport fun _ _ => ω.mem_tsupport_of_integrand_ne_zero f g

private theorem convolutionAux_apply (f g : C_c(G, A)) (s : G) :
    ω.convolutionAux μ f g s = twistedConvolution ω μ f g s :=
  rfl

/-- Cocycle-twisted convolution on `C_c(G, A)`, bundled as a `ℂ`-bilinear map. -/
def convolution : C_c(G, A) →ₗ[ℂ] C_c(G, A) →ₗ[ℂ] C_c(G, A) :=
  LinearMap.mk₂ ℂ (ω.convolutionAux μ)
    (fun f₁ f₂ g => CompactlySupportedContinuousMap.ext fun s => by
      simp only [convolutionAux_apply, twistedConvolution,
        CompactlySupportedContinuousMap.coe_add, Pi.add_apply, add_mul, map_add]
      exact integral_add (ω.integrable_integrand μ f₁ g s) (ω.integrable_integrand μ f₂ g s))
    (fun c f g => CompactlySupportedContinuousMap.ext fun s => by
      simp only [convolutionAux_apply, twistedConvolution,
        CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, smul_mul_assoc, map_smul]
      exact integral_smul c _)
    (fun f g₁ g₂ => CompactlySupportedContinuousMap.ext fun s => by
      simp only [convolutionAux_apply, twistedConvolution,
        CompactlySupportedContinuousMap.coe_add, Pi.add_apply, map_add, mul_add]
      exact integral_add (ω.integrable_integrand μ f g₁ s) (ω.integrable_integrand μ f g₂ s))
    (fun c f g => CompactlySupportedContinuousMap.ext fun s => by
      simp only [convolutionAux_apply, twistedConvolution,
        CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, map_smul, mul_smul_comm]
      exact integral_smul c _)

@[simp]
theorem coe_convolution (f g : C_c(G, A)) :
    ⇑(ω.convolution μ f g) = twistedConvolution ω μ f g :=
  (rfl)

@[simp]
theorem convolution_apply (f g : C_c(G, A)) (s : G) :
    ω.convolution μ f g s =
      ∫ r, (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s))) ∂μ :=
  (rfl)

/-- For `ω = 1`, `CentralCocycle.convolution` agrees on `C_c(G, A)` with `CStarAction.convolution`.
-/
@[simp]
theorem one_convolution : (1 : CentralCocycle α).convolution μ = α.convolution μ := by
  ext f g s
  simp

/-- The support of a cocycle-twisted convolution lies in the product of the supports. -/
theorem support_convolution_subset (f g : C_c(G, A)) :
    support (ω.convolution μ f g) ⊆ support f * support g :=
  support_integral_subset_mul μ fun _ _ => ω.mem_support_of_integrand_ne_zero f g

/-- Left multiplication by a coefficient commutes with cocycle-twisted convolution. -/
theorem smul_convolution (a : A) (f g : C_c(G, A)) :
    ω.convolution μ (a • f) g = a • ω.convolution μ f g := by
  ext s
  simp only [convolution_apply, CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, mul_assoc]
  simp_rw [DoubleCentralizer.snd_mul _ a]
  exact integral_const_mul_of_integrable (ω.integrable_integrand μ f g s)

/-! ### Associativity and `L¹` submultiplicativity -/

section LeftInvariant

variable [MeasurableMul G] [μ.IsMulLeftInvariant]

omit [IsTopologicalGroup G] [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G] in
/-- Pointwise algebraic identity behind `convolution_assoc`, proved in `𝓜(ℂ, A)` via centrality
and `ω.multiplier_value_mul_value`. -/
private theorem convolution_assoc_integrand_eq (r u s : G) (a b c : A) :
    (ω.value (r * u) ((r * u)⁻¹ * s) : 𝓜(ℂ, A)).snd
        ((ω.value r u : 𝓜(ℂ, A)).snd (a * α r b) * α (r * u) c) =
      (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd
        (a * α r ((ω.value u (u⁻¹ * (r⁻¹ * s)) : 𝓜(ℂ, A)).snd (b * α u c))) := by
  set w := u⁻¹ * (r⁻¹ * s)
  have hw : (r * u)⁻¹ * s = w := by simp [w, mul_inv_rev, mul_assoc]
  have huw : u * w = r⁻¹ * s := mul_inv_cancel_left u (r⁻¹ * s)
  rw [hw, ← huw, α.mul_apply r u c]
  apply DoubleCentralizer.coe_injective (𝕜 := ℂ)
  have hα :
      (α r ((ω.value u w : 𝓜(ℂ, A)).snd (b * α u c)) : 𝓜(ℂ, A)) =
        (α r b : 𝓜(ℂ, A)) * (α r (α u c) : 𝓜(ℂ, A)) *
          α.multiplier r (ω.value u w : 𝓜(ℂ, A)) := by
    rw [← α.multiplier_coe, ← DoubleCentralizer.coe_mul_eq_coe_snd, map_mul,
      DoubleCentralizer.coe_mul, map_mul, α.multiplier_coe, α.multiplier_coe]
  simp only [← DoubleCentralizer.coe_mul_eq_coe_snd, DoubleCentralizer.coe_mul, hα]
  calc ((a : 𝓜(ℂ, A)) * (α r b : 𝓜(ℂ, A)) * (ω.value r u : 𝓜(ℂ, A))) *
          (α r (α u c) : 𝓜(ℂ, A)) * (ω.value (r * u) w : 𝓜(ℂ, A))
      = (a : 𝓜(ℂ, A)) * (α r b : 𝓜(ℂ, A)) * (α r (α u c) : 𝓜(ℂ, A)) *
          ((ω.value r u : 𝓜(ℂ, A)) * (ω.value (r * u) w : 𝓜(ℂ, A))) := by
        simp only [mul_assoc]
        congr 2
        rw [← mul_assoc, (ω.central r u _).eq, mul_assoc]
    _ = (a : 𝓜(ℂ, A)) * ((α r b : 𝓜(ℂ, A)) * (α r (α u c) : 𝓜(ℂ, A)) *
          α.multiplier r (ω.value u w : 𝓜(ℂ, A))) * (ω.value r (u * w) : 𝓜(ℂ, A)) := by
        rw [← ω.multiplier_value_mul_value]
        simp only [mul_assoc]

/-- Cocycle-twisted convolution with respect to a left-invariant measure is associative. -/
theorem convolution_assoc (f g h : C_c(G, A)) :
    ω.convolution μ (ω.convolution μ f g) h = ω.convolution μ f (ω.convolution μ g h) := by
  ext s
  simp only [convolution_apply]
  calc ∫ t, (ω.value t (t⁻¹ * s) : 𝓜(ℂ, A)).snd
          ((∫ r, (ω.value r (r⁻¹ * t) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * t))) ∂μ) *
            α t (h (t⁻¹ * s))) ∂μ
      = ∫ t, ∫ r, (ω.value t (t⁻¹ * s) : 𝓜(ℂ, A)).snd
          ((ω.value r (r⁻¹ * t) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * t))) *
            α t (h (t⁻¹ * s))) ∂μ ∂μ := by
        congr 1 with t
        have hint_t : Integrable (fun r =>
            (ω.value r (r⁻¹ * t) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * t))) *
              α t (h (t⁻¹ * s))) μ := by
          simpa using ((ContinuousLinearMap.mul ℂ A).flip (α t (h (t⁻¹ * s)))).integrable_comp
            (ω.integrable_integrand μ f g t)
        rw [← integral_mul_const_of_integrable (ω.integrable_integrand μ f g t),
          ← ((ω.value t (t⁻¹ * s) : 𝓜(ℂ, A)).snd).integral_comp_comm hint_t]
    _ = ∫ r, ∫ t, (ω.value t (t⁻¹ * s) : 𝓜(ℂ, A)).snd
          ((ω.value r (r⁻¹ * t) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * t))) *
            α t (h (t⁻¹ * s))) ∂μ ∂μ := by
        refine integral_integral_swap_of_hasCompactSupport ?_
          (hasCompactSupport_uncurry_of_inv_mul_mem f.hasCompactSupport g.hasCompactSupport
            fun t r htr => ω.mem_tsupport_of_integrand_ne_zero f g
              (left_ne_zero_of_mul fun hz => htr (by rw [hz, map_zero])))
        rw [uncurry_def]
        fun_prop
    _ = ∫ r, (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f r *
          α r (∫ u, (ω.value u (u⁻¹ * (r⁻¹ * s)) : 𝓜(ℂ, A)).snd
            (g u * α u (h (u⁻¹ * (r⁻¹ * s)))) ∂μ)) ∂μ := by
        congr 1 with r
        have hint : Integrable (fun u => α r ((ω.value u (u⁻¹ * (r⁻¹ * s)) : 𝓜(ℂ, A)).snd
            (g u * α u (h (u⁻¹ * (r⁻¹ * s)))))) μ := by
          simpa using
            (α.toContinuousLinearMap r).integrable_comp (ω.integrable_integrand μ g h (r⁻¹ * s))
        have hint_mul : Integrable (fun u => f r * α r ((ω.value u (u⁻¹ * (r⁻¹ * s)) : 𝓜(ℂ, A)).snd
            (g u * α u (h (u⁻¹ * (r⁻¹ * s)))))) μ := by
          simpa using (ContinuousLinearMap.mul ℂ A (f r)).integrable_comp hint
        rw [← α.integral_comp_comm, ← integral_const_mul_of_integrable hint,
          ← ((ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd).integral_comp_comm hint_mul,
          ← integral_mul_left_eq_self _ r]
        congr 1 with u
        simpa [mul_assoc] using
          ω.convolution_assoc_integrand_eq r u s (f r) (g u) (h (u⁻¹ * (r⁻¹ * s)))

/-- The `L¹` norm is submultiplicative for cocycle-twisted convolution with respect to a
left-invariant measure. -/
theorem integral_norm_convolution_le (f g : C_c(G, A)) :
    ∫ s, ‖ω.convolution μ f g s‖ ∂μ ≤ (∫ s, ‖f s‖ ∂μ) * ∫ s, ‖g s‖ ∂μ := by
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
  calc ∫ s, ‖ω.convolution μ f g s‖ ∂μ
      ≤ ∫ s, ∫ r, ‖f r‖ * ‖g (r⁻¹ * s)‖ ∂μ ∂μ := by
        refine integral_mono ((ω.convolution μ f g).continuous.norm.integrable_of_hasCompactSupport
          (ω.convolution μ f g).hasCompactSupport.norm)
          (hNcont.integrable_of_hasCompactSupport hNsupp) fun s => ?_
        rw [convolution_apply]
        refine norm_integral_le_of_norm_le
          ((hcont.comp (.prodMk_right s)).integrable_of_hasCompactSupport
            (f.hasCompactSupport.mono' fun r hr => (hsupp s r hr).1)) (.of_forall fun r => ?_)
        simpa [DoubleCentralizer.norm_unitary_snd, StarAlgEquiv.norm_map] using
          norm_mul_le (f r) (α r (g (r⁻¹ * s)))
    _ = ∫ r, ∫ s, ‖f r‖ * ‖g (r⁻¹ * s)‖ ∂μ ∂μ :=
        integral_integral_swap_of_hasCompactSupport hcont
          (hasCompactSupport_uncurry_of_inv_mul_mem f.hasCompactSupport g.hasCompactSupport hsupp)
    _ = ∫ r, ‖f r‖ * ∫ s, ‖g s‖ ∂μ ∂μ := by
        congr 1 with r
        rw [integral_const_mul, integral_mul_left_eq_self (fun s => ‖g s‖) r⁻¹]
    _ = (∫ s, ‖f s‖ ∂μ) * ∫ s, ‖g s‖ ∂μ := integral_mul_const _ _

end LeftInvariant

end Convolution

/-! ### Cocycle-twisted involution -/

section Involution

variable [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- The cocycle-twisted conjugate-linear involution
`f^{*_ω}(s) = c(s) • (star (ω.value s s⁻¹)).fst (α s (star (f s⁻¹)))` on `C_c(G, A)`. -/
def involution : C_c(G, A) →ₗ⋆[ℂ] C_c(G, A) where
  toFun f :=
    { toFun s := ((Measure.modularCharacter s : ℝ) : ℂ) •
        (star (ω.value s s⁻¹ : 𝓜(ℂ, A))).fst (α s (star (f s⁻¹)))
      continuous_toFun := by
        have hω : Continuous fun s : G =>
            (star (ω.value s s⁻¹ : 𝓜(ℂ, A))).fst (α s (star (f s⁻¹))) := by
          simp_rw [← coe_inv_value]
          exact ω⁻¹.continuous_fst_apply continuous_id continuous_inv
            (α.continuous_apply continuous_id (f.continuous.comp continuous_inv).star)
        exact (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
          continuous_modularCharacter)).smul hω
      hasCompactSupport' :=
        (f.hasCompactSupport.comp_homeomorph (Homeomorph.inv G)).mono fun s hs hz => by
          have hfs : f s⁻¹ = 0 := hz
          exact hs (by simp [hfs]) }
  map_add' f g := by
    ext s
    simp [map_add, smul_add]
  map_smul' z f := by
    ext s
    simp only [CompactlySupportedContinuousMap.smul_apply, star_smul, map_smul, starRingEnd_apply]
    exact smul_comm _ _ _

@[simp]
theorem involution_apply (f : C_c(G, A)) (s : G) :
    ω.involution f s = ((Measure.modularCharacter s : ℝ) : ℂ) •
      (star (ω.value s s⁻¹ : 𝓜(ℂ, A))).fst (α s (star (f s⁻¹))) :=
  (rfl)

/-- For `ω = 1`, `CentralCocycle.involution` agrees with `CStarAction.twistedInvolution`. -/
@[simp]
theorem one_involution : (1 : CentralCocycle α).involution = α.twistedInvolution := by
  ext f s
  simp

/-- Applying the cocycle-twisted involution twice recovers `f`, using `α'_s(ω(s⁻¹, s)) = ω(s, s⁻¹)`.
-/
@[simp]
theorem involution_involution (f : C_c(G, A)) : ω.involution (ω.involution f) = f := by
  ext s
  have hc : ((Measure.modularCharacter s : ℝ) : ℂ) *
      ((Measure.modularCharacter s⁻¹ : ℝ) : ℂ) = 1 := by
    exact_mod_cast modularCharacter_mul_inv s
  have hinner :
      (α s (star ((star (ω.value s⁻¹ s : 𝓜(ℂ, A))).fst (α s⁻¹ (star (f s))))) : 𝓜(ℂ, A)) =
        (f s : 𝓜(ℂ, A)) * (ω.value s s⁻¹ : 𝓜(ℂ, A)) := by
    rw [← α.multiplier_coe, DoubleCentralizer.coe_star, ← DoubleCentralizer.mul_coe_eq_coe_fst,
      star_mul, map_mul, ← DoubleCentralizer.coe_star, ← map_star, star_star, star_star,
      α.multiplier_coe, apply_inv_apply, ω.multiplier_value_inv_left]
  apply DoubleCentralizer.coe_injective (𝕜 := ℂ)
  simp only [involution_apply, inv_inv, star_smul, Complex.star_def, Complex.conj_ofReal,
    map_smul, ← DoubleCentralizer.mul_coe_eq_coe_fst, hinner, smul_smul, hc, one_smul]
  rw [← mul_assoc, (ω.commute_star_value s s⁻¹ (f s : 𝓜(ℂ, A))).eq, mul_assoc,
    Unitary.coe_star_mul_self, mul_one]

/-- The norm of `ω.involution f s` equals the modular character times `‖f s⁻¹‖`. -/
@[simp↓]
theorem norm_involution_apply (f : C_c(G, A)) (s : G) :
    ‖ω.involution f s‖ = (Measure.modularCharacter s : ℝ) * ‖f s⁻¹‖ := by
  rw [involution_apply, norm_smul, ← Unitary.coe_star, DoubleCentralizer.norm_unitary_fst]
  simp [StarAlgEquiv.norm_map]

/-- The cocycle-twisted involution vanishes at `s` if and only if `f` vanishes at `s⁻¹`. -/
@[simp↓]
theorem involution_apply_eq_zero_iff (f : C_c(G, A)) (s : G) :
    ω.involution f s = 0 ↔ f s⁻¹ = 0 := by
  rw [← norm_eq_zero, norm_involution_apply]
  have hc : (Measure.modularCharacter s : ℝ) ≠ 0 := by
    rw [modularCharacter_apply]
    exact NNReal.coe_ne_zero.mpr (Measure.modularCharacterFun_pos s).ne'
  simp [hc]

/-- The support of `ω.involution f` is the inverse of `support f`. -/
@[simp]
theorem support_involution (f : C_c(G, A)) :
    support (ω.involution f) = (support f)⁻¹ := by
  ext s
  exact not_congr (ω.involution_apply_eq_zero_iff f s)

/-- The topological support of `ω.involution f` is the inverse of `tsupport f`. -/
@[simp]
theorem tsupport_involution (f : C_c(G, A)) :
    tsupport (ω.involution f) = (tsupport f)⁻¹ := by
  simp only [tsupport, support_involution, ← inv_closure]

/-- Against any Haar measure, `ω.involution` preserves the `L¹` norm. -/
theorem integral_norm_involution [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] (f : C_c(G, A)) :
    ∫ s, ‖ω.involution f s‖ ∂μ = ∫ s, ‖f s‖ ∂μ := by
  simp_rw [norm_involution_apply, ← smul_eq_mul]
  exact integral_modularCharacter_smul_inv_eq_self f.continuous.norm f.hasCompactSupport.norm

section ConvolutionInvolution

omit [IsTopologicalGroup G] [LocallyCompactSpace G] in
/-- Cocycle cancellation identity in `𝓜(ℂ, A)` behind `involution_convolution`. -/
private theorem involution_convolution_cocycle_eq (s r : G) :
    star (ω.value s s⁻¹ : 𝓜(ℂ, A)) * α.multiplier s (star (ω.value r (r⁻¹ * s⁻¹) : 𝓜(ℂ, A))) =
      star (ω.value (s * r) (r⁻¹ * s⁻¹) : 𝓜(ℂ, A)) *
        α.multiplier (s * r) (star (ω.value r⁻¹ r : 𝓜(ℂ, A))) *
          (ω.value (s * r) r⁻¹ : 𝓜(ℂ, A)) := by
  have h₁ : α.multiplier s (ω.value r (r⁻¹ * s⁻¹) : 𝓜(ℂ, A)) * (ω.value s s⁻¹ : 𝓜(ℂ, A)) =
      (ω.value s r : 𝓜(ℂ, A)) * (ω.value (s * r) (r⁻¹ * s⁻¹) : 𝓜(ℂ, A)) := by
    simpa [mul_inv_cancel_left] using ω.multiplier_value_mul_value s r (r⁻¹ * s⁻¹)
  have h₂ : α.multiplier s (ω.value r r⁻¹ : 𝓜(ℂ, A)) =
      (ω.value s r : 𝓜(ℂ, A)) * (ω.value (s * r) r⁻¹ : 𝓜(ℂ, A)) := by
    simpa using ω.multiplier_value_mul_value s r r⁻¹
  have hsr : α.multiplier (s * r) (star (ω.value r⁻¹ r : 𝓜(ℂ, A))) =
      star (α.multiplier s (ω.value r r⁻¹ : 𝓜(ℂ, A))) := by
    rw [map_mul, StarAlgEquiv.mul_apply, map_star, map_star, ω.multiplier_value_inv_left]
  have hstar₁ : star (ω.value s s⁻¹ : 𝓜(ℂ, A)) *
      α.multiplier s (star (ω.value r (r⁻¹ * s⁻¹) : 𝓜(ℂ, A))) =
        star (ω.value (s * r) (r⁻¹ * s⁻¹) : 𝓜(ℂ, A)) * star (ω.value s r : 𝓜(ℂ, A)) := by
    rw [map_star, ← star_mul, h₁, star_mul]
  have hstar₂ : star (α.multiplier s (ω.value r r⁻¹ : 𝓜(ℂ, A))) *
      (ω.value (s * r) r⁻¹ : 𝓜(ℂ, A)) = star (ω.value s r : 𝓜(ℂ, A)) := by
    rw [h₂, star_mul, (ω.commute_star_value (s * r) r⁻¹ _).eq, mul_assoc,
      Unitary.coe_star_mul_self, mul_one]
  rw [hstar₁, hsr, mul_assoc, hstar₂]

/-- Pointwise integrand identity behind `involution_convolution`. -/
private theorem involution_convolution_integrand_eq (f g : C_c(G, A)) (s r : G) :
    ((Measure.modularCharacter s : ℝ) : ℂ) •
        (star (ω.value s s⁻¹ : 𝓜(ℂ, A))).fst
          (α s (star ((ω.value r (r⁻¹ * s⁻¹) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s⁻¹)))))) =
      (ω.value (s * r) ((s * r)⁻¹ * s) : 𝓜(ℂ, A)).snd
        (ω.involution g (s * r) * α (s * r) (ω.involution f ((s * r)⁻¹ * s))) := by
  have hc : ((Measure.modularCharacter (s * r) : ℝ) : ℂ) *
      ((Measure.modularCharacter r⁻¹ : ℝ) : ℂ) = (Measure.modularCharacter s : ℝ) := by
    exact_mod_cast modularCharacter_mul_inv_cancel_right s r
  have hidx : (s * r)⁻¹ * s = r⁻¹ := by simp [mul_inv_rev, mul_assoc]
  rw [hidx]
  set X : 𝓜(ℂ, A) := (α s (α r (star (g (r⁻¹ * s⁻¹)))) : 𝓜(ℂ, A)) * (α s (star (f r)) : 𝓜(ℂ, A))
  have hL :
      (α s (star ((ω.value r (r⁻¹ * s⁻¹) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s⁻¹))))) :
        𝓜(ℂ, A)) = α.multiplier s (star (ω.value r (r⁻¹ * s⁻¹) : 𝓜(ℂ, A))) * X := by
    rw [← α.multiplier_coe, DoubleCentralizer.coe_star, ← DoubleCentralizer.coe_mul_eq_coe_snd,
      DoubleCentralizer.coe_mul, star_mul, star_mul, map_mul, map_mul, ← DoubleCentralizer.coe_star,
      ← DoubleCentralizer.coe_star, ← map_star (α r), α.multiplier_coe, α.multiplier_coe]
  have hRg : (ω.involution g (s * r) : 𝓜(ℂ, A)) = ((Measure.modularCharacter (s * r) : ℝ) : ℂ) •
      (star (ω.value (s * r) (r⁻¹ * s⁻¹) : 𝓜(ℂ, A)) *
        (α s (α r (star (g (r⁻¹ * s⁻¹)))) : 𝓜(ℂ, A))) := by
    rw [involution_apply, mul_inv_rev, α.mul_apply, DoubleCentralizer.coe_smul,
      ← DoubleCentralizer.mul_coe_eq_coe_fst]
  have hRf : (α (s * r) (ω.involution f r⁻¹) : 𝓜(ℂ, A)) =
      ((Measure.modularCharacter r⁻¹ : ℝ) : ℂ) •
        (α.multiplier (s * r) (star (ω.value r⁻¹ r : 𝓜(ℂ, A))) * (α s (star (f r)) : 𝓜(ℂ, A))) := by
    rw [involution_apply, inv_inv, map_smul, DoubleCentralizer.coe_smul, ← α.multiplier_coe,
      ← DoubleCentralizer.mul_coe_eq_coe_fst, map_mul, α.multiplier_coe, α.mul_apply,
      apply_inv_apply]
  apply DoubleCentralizer.coe_injective (𝕜 := ℂ)
  rw [DoubleCentralizer.coe_smul, ← DoubleCentralizer.mul_coe_eq_coe_fst, hL,
    ← DoubleCentralizer.coe_mul_eq_coe_snd, DoubleCentralizer.coe_mul, hRg, hRf,
    smul_mul_smul_comm, hc, smul_mul_assoc]
  congr 1
  rw [← mul_assoc (star (ω.value s s⁻¹ : 𝓜(ℂ, A))), ω.involution_convolution_cocycle_eq,
    mul_assoc (star _ * _), (ω.central (s * r) r⁻¹ X).eq]
  simp only [X, ← mul_assoc]
  congr 2
  rw [mul_assoc, (ω.commute_multiplier_star_value (s * r) r⁻¹ r _).eq, ← mul_assoc]

variable [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G] (μ : Measure G)
  [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]

/-- The cocycle-twisted involution reverses cocycle-twisted convolution:
`(f *_ω g)^{*_ω} = g^{*_ω} *_ω f^{*_ω}`. -/
theorem involution_convolution (f g : C_c(G, A)) :
    ω.involution (ω.convolution μ f g) =
      ω.convolution μ (ω.involution g) (ω.involution f) := by
  ext s
  have hint := ω.integrable_integrand μ f g s⁻¹
  have hstar : star (ω.convolution μ f g s⁻¹) =
      ∫ r, star ((ω.value r (r⁻¹ * s⁻¹) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s⁻¹)))) ∂μ := by
    rw [convolution_apply]
    simpa using ((starL ℂ : A ≃L⋆[ℂ] A).toContinuousLinearMap.integral_comp_commSL
      (by simp) hint).symm
  have hint_star : Integrable (fun r =>
      star ((ω.value r (r⁻¹ * s⁻¹) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s⁻¹))))) μ :=
    (starL ℂ : A ≃L⋆[ℂ] A).toContinuousLinearMap.integrable_comp hint
  have hint_α : Integrable (fun r =>
      α s (star ((ω.value r (r⁻¹ * s⁻¹) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s⁻¹)))))) μ := by
    simpa using (α.toContinuousLinearMap s).integrable_comp hint_star
  rw [involution_apply, hstar, ← α.integral_comp_comm,
    ← ((star (ω.value s s⁻¹ : 𝓜(ℂ, A))).fst).integral_comp_comm hint_α, ← integral_smul,
    convolution_apply, ← integral_mul_left_eq_self
      (fun u => (ω.value u (u⁻¹ * s) : 𝓜(ℂ, A)).snd
        (ω.involution g u * α u (ω.involution f (u⁻¹ * s)))) s]
  congr 1 with r
  exact ω.involution_convolution_integrand_eq f g s r

end ConvolutionInvolution

end Involution

end CentralCocycle

end TauCeti.CStarAction

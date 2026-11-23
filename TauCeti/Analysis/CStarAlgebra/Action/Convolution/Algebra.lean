/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Basic
public import TauCeti.Analysis.CStarAlgebra.Action.Involution
public import TauCeti.Analysis.Normed.Algebra.CompactlySupportedL1

/-!
# The convolution ⋆-algebra of a C⋆-dynamical system

For a point-norm continuous action `α` of a locally compact group `G` on a C⋆-algebra `A` and a
left-invariant measure `μ` on `G`, the compactly supported continuous functions `C_c(G, A)` form
a complex ⋆-algebra under the twisted convolution

`(f ⋆ g) s = ∫ r, f r * α r (g (r⁻¹ * s)) ∂μ`

and the twisted involution `f* s = c(s) • α s (star (f s⁻¹))`, where `c` is Mathlib's modular
character. This is the dense ⋆-algebra whose completions in the universal and regular norms are
the full and reduced crossed products of `(A, G, α)`.

The essential identity is that the twisted involution reverses twisted convolution,
`(f ⋆ g)* = g* ⋆ f*`, `twistedInvolution_convolution`. Its proof uses only left invariance of `μ`
and multiplicativity of `c`, so no relation between `μ` and `c` is needed here. The modular
character is matched with `μ` only when the involution is compared with the `L¹` norm.

The ⋆-algebra is the type `ConvolutionAlgebra α μ`, an abbreviation for
`TauCeti.CompactlySupportedL1 α A μ` wrapping `C_c(G, A)`.
A separate type is needed because `C_c(G, A)` already carries the pointwise product and star,
and because the product and star depend on `α` and `μ`. The maps `ConvolutionAlgebra.toConv` and
`ConvolutionAlgebra.ofConv` pass between the two types, following Mathlib's `WithConv`.
Distributivity and the scalar compatibilities hold for any measure finite on compacts.
Associativity, and hence the `NonUnitalRing` and `StarRing` structures, uses left invariance.
No unit, separability, or σ-finiteness is assumed.

The conventions follow Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.

## Main definitions

* `TauCeti.CStarAction.ConvolutionAlgebra`: the convolution ⋆-algebra on `C_c(G, A)`.

## Main statements

* `TauCeti.CStarAction.twistedInvolution_convolution`: `(f ⋆ g)* = g* ⋆ f*`.
* `TauCeti.CStarAction.ConvolutionAlgebra.instNonUnitalRing`: twisted convolution makes
  `ConvolutionAlgebra α μ` a nonunital ring, and a complex algebra in the sense of
  `IsScalarTower` and `SMulCommClass`.
* `TauCeti.CStarAction.ConvolutionAlgebra.instStarRing`: the twisted involution makes it a ⋆-ring,
  and it is a ⋆-module over `ℂ`.
* `TauCeti.CStarAction.ConvolutionAlgebra.ofConv_mul_smulRight_apply`: the formula for the right
  product `f ⋆ (φ ⊗ e)` with an elementary function, after the substitution `r = s * t⁻¹`.
-/

public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported

namespace TauCeti.CStarAction

variable {G A : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]

/-! ### The involution reverses twisted convolution -/

section Involution

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G]
  [OpensMeasurableSpace G] [MeasurableMul G] (α : CStarAction G A) (μ : Measure G)
  [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]

/-- The twisted involution reverses twisted convolution with respect to a left-invariant measure:
`(f ⋆ g)* = g* ⋆ f*`. -/
theorem twistedInvolution_convolution (f g : C_c(G, A)) :
    α.twistedInvolution (α.convolution μ f g) =
      α.convolution μ (α.twistedInvolution g) (α.twistedInvolution f) := by
  ext s
  have hint : Integrable (fun r => f r * α r (g (r⁻¹ * s⁻¹))) μ :=
    (by fun_prop : Continuous fun r => f r * α r (g (r⁻¹ * s⁻¹))).integrable_of_hasCompactSupport
      f.hasCompactSupport.mul_right
  have hstar : star (∫ r, f r * α r (g (r⁻¹ * s⁻¹)) ∂μ) =
      ∫ r, star (f r * α r (g (r⁻¹ * s⁻¹))) ∂μ := by
    simpa using ((starL ℂ : A ≃L⋆[ℂ] A).toContinuousLinearMap.integral_comp_commSL
      (by simp) hint).symm
  have hc (r : G) : ((Measure.modularCharacter r : ℝ) : ℂ) *
      ((Measure.modularCharacter (r⁻¹ * s) : ℝ) : ℂ) = (Measure.modularCharacter s : ℝ) := by
    exact_mod_cast by rw [← map_mul, mul_inv_cancel_left]
  -- Collect the modular weights into `c(s)` and the automorphisms `α r ∘ α (r⁻¹ * s)` into
  -- `α s` on the right, then substitute `r ↦ s * r` there.
  simp only [twistedInvolution_apply, convolution_apply, map_smul, smul_mul_smul_comm, hc,
    ← mul_apply, mul_inv_cancel_left, mul_inv_rev, inv_inv]
  rw [integral_smul, ← integral_mul_left_eq_self
    (fun r => α r (star (g r⁻¹)) * α s (star (f (s⁻¹ * r)))) s]
  congr 1
  rw [hstar, ← integral_comp_comm]
  congr 1 with t
  simp [star_mul, mul_apply, map_star]

end Involution

/-! ### The convolution algebra -/

variable [MeasurableSpace G]

/-- The convolution ⋆-algebra of the C⋆-dynamical system `(A, G, α)` with respect to `μ`: the
compactly supported continuous functions `G → A`, with twisted convolution as product and the
twisted involution as star. Use `ConvolutionAlgebra.toConv` and `ConvolutionAlgebra.ofConv` to
pass to and from `C_c(G, A)`, whose own product and star are pointwise. -/
abbrev ConvolutionAlgebra (α : CStarAction G A) (μ : Measure G) : Type _ :=
  CompactlySupportedL1 α A μ

namespace ConvolutionAlgebra

variable {α : CStarAction G A} {μ : Measure G}

/-- Regard a compactly supported function as an element of the convolution algebra. -/
abbrev toConv (f : C_c(G, A)) : ConvolutionAlgebra α μ := CompactlySupportedL1.toConv f

/-- The compactly supported function underlying an element of the convolution algebra. -/
abbrev ofConv (f : ConvolutionAlgebra α μ) : C_c(G, A) := CompactlySupportedL1.ofConv f

theorem ofConv_toConv (f : C_c(G, A)) : (toConv f : ConvolutionAlgebra α μ).ofConv = f :=
  CompactlySupportedL1.ofConv_toConv f

theorem toConv_ofConv (f : ConvolutionAlgebra α μ) : toConv f.ofConv = f :=
  CompactlySupportedL1.toConv_ofConv f

theorem ofConv_injective : Function.Injective (ofConv : ConvolutionAlgebra α μ → C_c(G, A)) :=
  CompactlySupportedL1.ofConv_injective

theorem toConv_injective : Function.Injective (toConv : C_c(G, A) → ConvolutionAlgebra α μ) :=
  CompactlySupportedL1.toConv_injective

theorem ext {f g : ConvolutionAlgebra α μ} (h : f.ofConv = g.ofConv) : f = g :=
  ofConv_injective h

variable (α μ) in
/-- `ConvolutionAlgebra.ofConv` and `ConvolutionAlgebra.toConv` as an equivalence. -/
abbrev equiv : ConvolutionAlgebra α μ ≃ C_c(G, A) :=
  CompactlySupportedL1.equiv α A μ

theorem equiv_apply (f : ConvolutionAlgebra α μ) : equiv α μ f = f.ofConv :=
  CompactlySupportedL1.equiv_apply f

theorem equiv_symm_apply (f : C_c(G, A)) : (equiv α μ).symm f = toConv f :=
  CompactlySupportedL1.equiv_symm_apply f

variable (α μ) in
/-- `ConvolutionAlgebra.ofConv` as an additive equivalence with `C_c(G, A)`. -/
abbrev addEquiv : ConvolutionAlgebra α μ ≃+ C_c(G, A) :=
  CompactlySupportedL1.addEquiv α A μ

theorem addEquiv_apply (f : ConvolutionAlgebra α μ) : addEquiv α μ f = f.ofConv :=
  CompactlySupportedL1.addEquiv_apply f

theorem addEquiv_symm_apply (f : C_c(G, A)) : (addEquiv α μ).symm f = toConv f :=
  CompactlySupportedL1.addEquiv_symm_apply f

theorem ofConv_zero : (0 : ConvolutionAlgebra α μ).ofConv = 0 :=
  CompactlySupportedL1.ofConv_zero

theorem ofConv_add (f g : ConvolutionAlgebra α μ) : (f + g).ofConv = f.ofConv + g.ofConv :=
  CompactlySupportedL1.ofConv_add f g

theorem ofConv_neg (f : ConvolutionAlgebra α μ) : (-f).ofConv = -f.ofConv :=
  CompactlySupportedL1.ofConv_neg f

theorem ofConv_sub (f g : ConvolutionAlgebra α μ) : (f - g).ofConv = f.ofConv - g.ofConv :=
  CompactlySupportedL1.ofConv_sub f g

theorem ofConv_smul (c : ℂ) (f : ConvolutionAlgebra α μ) : (c • f).ofConv = c • f.ofConv :=
  CompactlySupportedL1.ofConv_smul c f

theorem toConv_zero : (toConv 0 : ConvolutionAlgebra α μ) = 0 :=
  CompactlySupportedL1.toConv_zero

theorem toConv_add (f g : C_c(G, A)) :
    (toConv (f + g) : ConvolutionAlgebra α μ) = toConv f + toConv g :=
  CompactlySupportedL1.toConv_add f g

theorem toConv_neg (f : C_c(G, A)) : (toConv (-f) : ConvolutionAlgebra α μ) = -toConv f :=
  CompactlySupportedL1.toConv_neg f

theorem toConv_sub (f g : C_c(G, A)) :
    (toConv (f - g) : ConvolutionAlgebra α μ) = toConv f - toConv g :=
  CompactlySupportedL1.toConv_sub f g

theorem toConv_smul (c : ℂ) (f : C_c(G, A)) :
    (toConv (c • f) : ConvolutionAlgebra α μ) = c • toConv f :=
  CompactlySupportedL1.toConv_smul c f

variable (α μ) in
/-- `ConvolutionAlgebra.ofConv` as a complex linear equivalence with `C_c(G, A)`. -/
abbrev linearEquiv : ConvolutionAlgebra α μ ≃ₗ[ℂ] C_c(G, A) :=
  CompactlySupportedL1.linearEquiv α A μ ℂ

theorem linearEquiv_apply (f : ConvolutionAlgebra α μ) : linearEquiv α μ f = f.ofConv :=
  CompactlySupportedL1.linearEquiv_apply f

theorem linearEquiv_symm_apply (f : C_c(G, A)) : (linearEquiv α μ).symm f = toConv f :=
  CompactlySupportedL1.linearEquiv_symm_apply f

/-- The elementary function `s ↦ φ s • e` of a real compactly supported function `φ` and a
coefficient `e`, as an element of the convolution algebra. -/
def smulRight (φ : C_c(G, ℝ)) (e : A) : ConvolutionAlgebra α μ :=
  toConv (φ.compLeft (ContinuousLinearMap.toSpanSingleton ℝ e))

@[simp]
theorem ofConv_smulRight_apply (φ : C_c(G, ℝ)) (e : A) (s : G) :
    (smulRight φ e : ConvolutionAlgebra α μ).ofConv s = φ s • e := by
  simp [smulRight, CompactlySupportedContinuousMap.compLeft_apply]

/-! ### Convolution product -/

section Mul

variable [IsTopologicalGroup G] [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]

instance : Mul (ConvolutionAlgebra α μ) where
  mul f g := toConv (α.convolution μ f.ofConv g.ofConv)

@[simp]
theorem ofConv_mul (f g : ConvolutionAlgebra α μ) :
    (f * g).ofConv = α.convolution μ f.ofConv g.ofConv :=
  (rfl)

@[simp]
theorem toConv_convolution (f g : C_c(G, A)) :
    (toConv (α.convolution μ f g) : ConvolutionAlgebra α μ) = toConv f * toConv g :=
  (rfl)

instance : NonUnitalNonAssocRing (ConvolutionAlgebra α μ) :=
  CompactlySupportedL1.nonUnitalNonAssocRingOf (fun f g => α.convolution μ f g) ofConv_mul
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ => by simp) (fun _ => by simp)

instance : IsScalarTower ℂ (ConvolutionAlgebra α μ) (ConvolutionAlgebra α μ) :=
  CompactlySupportedL1.isScalarTowerOf (fun f g => α.convolution μ f g) ofConv_mul
    fun _ _ _ => by simp

instance : SMulCommClass ℂ (ConvolutionAlgebra α μ) (ConvolutionAlgebra α μ) :=
  CompactlySupportedL1.smulCommClassOf (fun f g => α.convolution μ f g) ofConv_mul
    fun _ _ _ => by simp

variable [MeasurableMul G] [μ.IsMulLeftInvariant]

instance instNonUnitalRing : NonUnitalRing (ConvolutionAlgebra α μ) :=
  CompactlySupportedL1.nonUnitalRingOf (fun f g => α.convolution μ f g) ofConv_mul
    fun _ _ _ => by simp [convolution_assoc]

end Mul

/-! ### Products with elementary functions -/

section SMulRight

/-- The right product with an elementary function, after substituting `r = s * t⁻¹`:
`(f ⋆ (φ ⊗ e)) s = ∫ t, φ t • c(t) • (f (s * t⁻¹) * α (s * t⁻¹) e) ∂μ`. -/
theorem ofConv_mul_smulRight_apply [IsTopologicalGroup G] [LocallyCompactSpace G]
    [BorelSpace G] [μ.IsHaarMeasure] (f : ConvolutionAlgebra α μ)
    (φ : C_c(G, ℝ)) (e : A) (s : G) :
    (f * smulRight φ e).ofConv s = ∫ t, φ t • (Measure.modularCharacter t : ℝ) •
      (f.ofConv (s * t⁻¹) * α (s * t⁻¹) e) ∂μ := by
  set g := f.ofConv
  have hinv := integral_inv_eq_integral_modularCharacter_smul (μ := μ)
    (f := fun t => φ t • (g (s * t⁻¹) * α (s * t⁻¹) e)) (by fun_prop)
    φ.hasCompactSupport.smul_right
  simp only [inv_inv] at hinv
  calc (f * smulRight φ e).ofConv s = ∫ r, φ (r⁻¹ * s) • (g r * α r e) ∂μ := by
        simp only [ofConv_mul, convolution_apply, ofConv_smulRight_apply, g]
        congr 1 with r
        rw [← Complex.coe_smul, map_smul, Complex.coe_smul, mul_smul_comm]
    _ = ∫ t, φ t⁻¹ • (g (s * t) * α (s * t) e) ∂μ := by
        rw [← integral_mul_left_eq_self _ s]
        simp [mul_inv_rev, mul_assoc]
    _ = _ := by rw [hinv]; simp_rw [smul_comm (Measure.modularCharacter _ : ℝ) (φ _)]

end SMulRight

/-! ### Twisted involution -/

section Star

variable [IsTopologicalGroup G] [LocallyCompactSpace G]

instance : Star (ConvolutionAlgebra α μ) where
  star f := toConv (α.twistedInvolution f.ofConv)

@[simp]
theorem ofConv_star (f : ConvolutionAlgebra α μ) :
    (star f).ofConv = α.twistedInvolution f.ofConv :=
  (rfl)

@[simp]
theorem toConv_twistedInvolution (f : C_c(G, A)) :
    (toConv (α.twistedInvolution f) : ConvolutionAlgebra α μ) = star (toConv f) :=
  (rfl)

instance : InvolutiveStar (ConvolutionAlgebra α μ) :=
  CompactlySupportedL1.involutiveStarOf α.twistedInvolution ofConv_star fun _ => by simp

instance : StarModule ℂ (ConvolutionAlgebra α μ) :=
  CompactlySupportedL1.starModuleOf α.twistedInvolution ofConv_star fun _ _ => by simp

variable [OpensMeasurableSpace G] [MeasurableMul G] [IsFiniteMeasureOnCompacts μ]
  [μ.IsMulLeftInvariant]

instance instStarRing : StarRing (ConvolutionAlgebra α μ) :=
  CompactlySupportedL1.starRingOf (fun f g => α.convolution μ f g) α.twistedInvolution ofConv_mul
    ofConv_star ofConv_add (fun _ _ => by simp) fun _ _ => by simp [twistedInvolution_convolution]

end Star

end ConvolutionAlgebra

end TauCeti.CStarAction

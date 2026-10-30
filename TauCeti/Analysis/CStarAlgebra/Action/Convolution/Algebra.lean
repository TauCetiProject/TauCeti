/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Basic
public import TauCeti.Analysis.CStarAlgebra.Action.Involution

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

The ⋆-algebra is the type `ConvolutionAlgebra α μ`, a one-field structure wrapping `C_c(G, A)`.
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
structure ConvolutionAlgebra (α : CStarAction G A) (μ : Measure G) where
  /-- Regard a compactly supported function as an element of the convolution algebra. -/
  toConv ::
  /-- The compactly supported function underlying an element of the convolution algebra. -/
  ofConv : C_c(G, A)

namespace ConvolutionAlgebra

variable {α : CStarAction G A} {μ : Measure G}

@[simp]
theorem ofConv_toConv (f : C_c(G, A)) : (toConv f : ConvolutionAlgebra α μ).ofConv = f :=
  (rfl)

@[simp]
theorem toConv_ofConv (f : ConvolutionAlgebra α μ) : toConv f.ofConv = f :=
  (rfl)

theorem ofConv_injective : Function.Injective (ofConv : ConvolutionAlgebra α μ → C_c(G, A)) :=
  fun f g h => by rw [← toConv_ofConv f, h, toConv_ofConv]

theorem toConv_injective : Function.Injective (toConv : C_c(G, A) → ConvolutionAlgebra α μ) :=
  fun f g h => by rw [← ofConv_toConv (α := α) (μ := μ) f, h, ofConv_toConv]

@[ext]
theorem ext {f g : ConvolutionAlgebra α μ} (h : f.ofConv = g.ofConv) : f = g :=
  ofConv_injective h

variable (α μ) in
/-- `ConvolutionAlgebra.ofConv` and `ConvolutionAlgebra.toConv` as an equivalence. -/
def equiv : ConvolutionAlgebra α μ ≃ C_c(G, A) where
  toFun := ofConv
  invFun := toConv
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem equiv_apply (f : ConvolutionAlgebra α μ) : equiv α μ f = f.ofConv :=
  (rfl)

@[simp]
theorem equiv_symm_apply (f : C_c(G, A)) : (equiv α μ).symm f = toConv f :=
  (rfl)

instance : AddCommGroup (ConvolutionAlgebra α μ) :=
  (equiv α μ).addCommGroup

variable (α μ) in
/-- `ConvolutionAlgebra.ofConv` as an additive equivalence with `C_c(G, A)`. -/
def addEquiv : ConvolutionAlgebra α μ ≃+ C_c(G, A) where
  __ := equiv α μ
  map_add' _ _ := (rfl)

@[simp]
theorem addEquiv_apply (f : ConvolutionAlgebra α μ) : addEquiv α μ f = f.ofConv :=
  (rfl)

@[simp]
theorem addEquiv_symm_apply (f : C_c(G, A)) : (addEquiv α μ).symm f = toConv f :=
  (rfl)

instance : Module ℂ (ConvolutionAlgebra α μ) :=
  (addEquiv α μ).module ℂ

@[simp]
theorem ofConv_zero : (0 : ConvolutionAlgebra α μ).ofConv = 0 :=
  (rfl)

@[simp]
theorem ofConv_add (f g : ConvolutionAlgebra α μ) : (f + g).ofConv = f.ofConv + g.ofConv :=
  (rfl)

@[simp]
theorem ofConv_neg (f : ConvolutionAlgebra α μ) : (-f).ofConv = -f.ofConv :=
  (rfl)

@[simp]
theorem ofConv_sub (f g : ConvolutionAlgebra α μ) : (f - g).ofConv = f.ofConv - g.ofConv :=
  (rfl)

@[simp]
theorem ofConv_smul (c : ℂ) (f : ConvolutionAlgebra α μ) : (c • f).ofConv = c • f.ofConv :=
  (rfl)

@[simp]
theorem toConv_zero : (toConv 0 : ConvolutionAlgebra α μ) = 0 :=
  (rfl)

@[simp]
theorem toConv_add (f g : C_c(G, A)) :
    (toConv (f + g) : ConvolutionAlgebra α μ) = toConv f + toConv g :=
  (rfl)

@[simp]
theorem toConv_neg (f : C_c(G, A)) : (toConv (-f) : ConvolutionAlgebra α μ) = -toConv f :=
  (rfl)

@[simp]
theorem toConv_sub (f g : C_c(G, A)) :
    (toConv (f - g) : ConvolutionAlgebra α μ) = toConv f - toConv g :=
  (rfl)

@[simp]
theorem toConv_smul (c : ℂ) (f : C_c(G, A)) :
    (toConv (c • f) : ConvolutionAlgebra α μ) = c • toConv f :=
  (rfl)

variable (α μ) in
/-- `ConvolutionAlgebra.ofConv` as a complex linear equivalence with `C_c(G, A)`. -/
def linearEquiv : ConvolutionAlgebra α μ ≃ₗ[ℂ] C_c(G, A) where
  __ := equiv α μ
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)

@[simp]
theorem linearEquiv_apply (f : ConvolutionAlgebra α μ) : linearEquiv α μ f = f.ofConv :=
  (rfl)

@[simp]
theorem linearEquiv_symm_apply (f : C_c(G, A)) : (linearEquiv α μ).symm f = toConv f :=
  (rfl)

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

instance : NonUnitalNonAssocRing (ConvolutionAlgebra α μ) where
  left_distrib f g h := by ext1; simp
  right_distrib f g h := by ext1; simp
  zero_mul f := by ext1; simp
  mul_zero f := by ext1; simp

instance : IsScalarTower ℂ (ConvolutionAlgebra α μ) (ConvolutionAlgebra α μ) where
  smul_assoc c f g := by ext1; simp

instance : SMulCommClass ℂ (ConvolutionAlgebra α μ) (ConvolutionAlgebra α μ) where
  smul_comm c f g := by ext1; simp

variable [MeasurableMul G] [μ.IsMulLeftInvariant]

instance instNonUnitalRing : NonUnitalRing (ConvolutionAlgebra α μ) where
  mul_assoc f g h := by ext1; simp [convolution_assoc]

end Mul

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

instance : InvolutiveStar (ConvolutionAlgebra α μ) where
  star_involutive f := by ext1; simp

instance : StarModule ℂ (ConvolutionAlgebra α μ) where
  star_smul c f := by ext1; simp

variable [OpensMeasurableSpace G] [MeasurableMul G] [IsFiniteMeasureOnCompacts μ]
  [μ.IsMulLeftInvariant]

instance instStarRing : StarRing (ConvolutionAlgebra α μ) where
  star_mul f g := by ext1; simp [twistedInvolution_convolution]
  star_add f g := by ext1; simp

end Star

end ConvolutionAlgebra

end TauCeti.CStarAction

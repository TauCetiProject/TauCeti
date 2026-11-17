/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.FullSeminorm
public import TauCeti.Analysis.CStarAlgebra.Completion
import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Nondegenerate

/-!
# The full crossed product of a C⋆-dynamical system

Let `α` be a point-norm continuous action of a locally compact group `G : Type u` on a possibly
nonunital C⋆-algebra `A : Type v`, and let `μ` be a left Haar measure on `G`. The *full crossed
product* `A ⋊_α G` is the completion of the twisted convolution algebra `C_c(G, A)` in the full
C⋆-seminorm `‖f‖ᵤ = sup ‖(π ⋊ U)(f)‖`, the supremum over covariant representations `(π, U)` on
Hilbert spaces in the universe `max u v`.

Bundling the full seminorm as `ConvolutionAlgebra.fullCStarSeminorm α μ : TauCeti.CStarSeminorm`
and taking its C⋆-completion `TauCeti.CStarSeminorm.Completion` yields the nonunital C⋆-algebra
`FullCrossedProduct α μ`. The canonical ⋆-homomorphism `FullCrossedProduct.of` from the twisted
convolution algebra has dense range, and `‖of f‖ = ‖f‖ᵤ`. It is injective whenever `A` has a
faithful representation and `μ` is inner regular for compact sets on sets of finite measure
(`μ.InnerRegularCompactLTTop`).

Every integrated form `π ⋊ U` of a covariant representation, on a Hilbert space in any universe,
extends uniquely to a ⋆-homomorphism `CovariantRepresentation.integratedFull` on the full crossed
product. The norm of `A ⋊_α G` is the supremum of the norms of these extensions,
`FullCrossedProduct.norm_le_iff`. No unit, separability, σ-finiteness or nondegeneracy is
assumed.

## Main definitions

* `TauCeti.CStarAction.ConvolutionAlgebra.fullCStarSeminorm`: the full C⋆-seminorm on the twisted
  convolution algebra, bundled as a `TauCeti.CStarSeminorm`.
* `TauCeti.CStarAction.FullCrossedProduct`: the full crossed product `A ⋊_α G`, a nonunital
  C⋆-algebra.
* `TauCeti.CStarAction.FullCrossedProduct.of`: the canonical ⋆-homomorphism from the twisted
  convolution algebra, with dense range.
* `TauCeti.CStarAction.FullCrossedProduct.lift`: extension of a ⋆-homomorphism bounded by the
  full seminorm to the full crossed product.
* `TauCeti.CStarAction.CovariantRepresentation.integratedFull`: the extension of the integrated
  form of a covariant representation to the full crossed product.

## Main statements

* `TauCeti.CStarAction.FullCrossedProduct.norm_of`: `‖of f‖ = ‖f‖ᵤ`.
* `TauCeti.CStarAction.FullCrossedProduct.of_injective`: given a faithful representation of `A`
  and `μ.InnerRegularCompactLTTop`, the canonical map is injective.
* `TauCeti.CStarAction.FullCrossedProduct.starAlgHom_ext`: ⋆-homomorphisms out of the full
  crossed product are determined on the twisted convolution algebra.
* `TauCeti.CStarAction.FullCrossedProduct.norm_le_iff`: the norm of the full crossed product is
  the least bound for the integrated forms of covariant representations.
* `TauCeti.CStarAction.FullCrossedProduct.of_eq_of_iff`: two elements of the twisted convolution
  algebra have the same image in the full crossed product exactly when all their integrated forms
  agree.
* `TauCeti.CStarAction.CovariantRepresentation.integratedFull_eq_zero_iff`: an extended integrated
  form vanishes precisely when its coefficient representation is zero.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2 (the universal norm and the full
  crossed product).
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti.CStarAction

universe u v w

variable {G : Type u} {A : Type v} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [NonUnitalCStarAlgebra A] {α : CStarAction G A} {μ : Measure G}
  [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure]

variable (α μ) in
/-- The full C⋆-seminorm on the twisted convolution algebra, bundled as a
`TauCeti.CStarSeminorm`. -/
def ConvolutionAlgebra.fullCStarSeminorm : CStarSeminorm (ConvolutionAlgebra α μ) where
  __ := ConvolutionAlgebra.fullSeminorm α μ
  map_mul_le' := ConvolutionAlgebra.fullSeminorm_mul_le
  mul_self_le_star_mul_self' f := (ConvolutionAlgebra.fullSeminorm_star_mul_self f).ge

@[simp]
theorem ConvolutionAlgebra.fullCStarSeminorm_apply (f : ConvolutionAlgebra α μ) :
    ConvolutionAlgebra.fullCStarSeminorm α μ f = ConvolutionAlgebra.fullSeminorm α μ f :=
  (rfl)

variable (α μ) in
/-- The full crossed product `A ⋊_α G` of the C⋆-dynamical system `(A, G, α)`: the completion of
the twisted convolution algebra in the full C⋆-seminorm. It is a nonunital C⋆-algebra, and
the canonical map `FullCrossedProduct.of` from the twisted convolution algebra has dense range. -/
@[expose] def FullCrossedProduct : Type (max u v) :=
  (ConvolutionAlgebra.fullCStarSeminorm α μ).Completion

namespace FullCrossedProduct

/-- The full crossed product is a nonunital C⋆-algebra. -/
instance : NonUnitalCStarAlgebra (FullCrossedProduct α μ) :=
  inferInstanceAs (NonUnitalCStarAlgebra (ConvolutionAlgebra.fullCStarSeminorm α μ).Completion)

variable (α μ) in
/-- The canonical ⋆-homomorphism from the twisted convolution algebra into the full crossed
product. -/
@[expose] def of : ConvolutionAlgebra α μ →⋆ₙₐ[ℂ] FullCrossedProduct α μ :=
  (ConvolutionAlgebra.fullCStarSeminorm α μ).ofNonUnital

/-- The norm of the image of `f` in the full crossed product is its full seminorm `‖f‖ᵤ`. -/
@[simp]
theorem norm_of (f : ConvolutionAlgebra α μ) :
    ‖of α μ f‖ = ConvolutionAlgebra.fullSeminorm α μ f :=
  (ConvolutionAlgebra.fullCStarSeminorm α μ).norm_ofNonUnital f

/-- The image of `f` in the full crossed product has norm at most its L¹ norm. -/
theorem norm_of_le (f : ConvolutionAlgebra α μ) : ‖of α μ f‖ ≤ ‖f‖ :=
  (norm_of f).trans_le (ConvolutionAlgebra.fullSeminorm_le_norm f)

/-- The canonical map is continuous for the L¹ topology on the twisted convolution algebra. -/
theorem continuous_of : Continuous (of α μ) :=
  AddMonoidHomClass.continuous_of_bound (of α μ) 1 fun f => by
    simpa only [one_mul] using norm_of_le f

/-- The twisted convolution algebra is dense in the full crossed product. -/
theorem denseRange_of : DenseRange (of α μ) :=
  (ConvolutionAlgebra.fullCStarSeminorm α μ).denseRange_ofNonUnital

/-- Compactly supported continuous functions `C_c(G, A)` map densely into
`FullCrossedProduct α μ`. -/
theorem denseRange_of_comp_toConv :
    DenseRange ((of α μ) ∘ ConvolutionAlgebra.toConv) := by
  rw [DenseRange, (Function.RightInverse.surjective ConvolutionAlgebra.toConv_ofConv).range_comp]
  exact denseRange_of

/-- To prove a closed property of every element of the full crossed product, it suffices to
prove it on the twisted convolution algebra. -/
@[elab_as_elim]
theorem induction_on {p : FullCrossedProduct α μ → Prop} (x : FullCrossedProduct α μ)
    (hp : IsClosed {x | p x}) (ih : ∀ f, p (of α μ f)) : p x :=
  CStarSeminorm.induction_on x hp ih

/-- If `A` has a faithful representation on a Hilbert space `H` and `μ` is inner regular for compact
sets on sets of finite measure, the canonical map from the twisted convolution algebra into the full
crossed product is injective. -/
theorem of_injective [μ.InnerRegularCompactLTTop] {H : Type w} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hρ : Function.Injective ρ) : Function.Injective (of α μ) :=
  (injective_iff_map_eq_zero (of α μ)).2 fun f hf =>
    (ConvolutionAlgebra.fullSeminorm_eq_zero_iff hρ).1 (by rw [← norm_of, hf, norm_zero])

/-- ⋆-homomorphisms from the full crossed product into a C⋆-algebra are determined by their
values on the twisted convolution algebra. -/
@[ext]
theorem starAlgHom_ext {B : Type*} [NonUnitalCStarAlgebra B]
    {φ ψ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] B} (h : φ.comp (of α μ) = ψ.comp (of α μ)) :
    φ = ψ :=
  CStarSeminorm.nonUnitalStarAlgHom_ext h

/-- Continuous linear maps out of the full crossed product are determined by their values on
the twisted convolution algebra. -/
@[ext]
theorem continuousLinearMap_ext {E : Type*} [TopologicalSpace E] [T2Space E] [AddCommMonoid E]
    [Module ℂ E] {S T : FullCrossedProduct α μ →L[ℂ] E}
    (h : ∀ f, S (of α μ f) = T (of α μ f)) : S = T :=
  CStarSeminorm.continuousLinearMap_ext h

variable {D : Type*} [NonUnitalCStarAlgebra D]
  (ρ : ConvolutionAlgebra α μ →⋆ₙₐ[ℂ] D)
  (hρ : ∀ f, ‖ρ f‖ ≤ ConvolutionAlgebra.fullSeminorm α μ f)

/-- Extend a ⋆-homomorphism bounded by the full seminorm to the full crossed product.
Its values on compactly supported coefficients are given by `lift_of`, and these determine
it uniquely by `starAlgHom_ext`. -/
def lift : FullCrossedProduct α μ →⋆ₙₐ[ℂ] D :=
  (ConvolutionAlgebra.fullCStarSeminorm α μ).liftNonUnital ρ hρ

/-- The extension agrees with the original ⋆-homomorphism on compactly supported coefficients. -/
@[simp]
theorem lift_of (f : ConvolutionAlgebra α μ) : lift ρ hρ (of α μ f) = ρ f :=
  (ConvolutionAlgebra.fullCStarSeminorm α μ).liftNonUnital_ofNonUnital ρ hρ f

/-- Composing the extension with the canonical map recovers the original ⋆-homomorphism. -/
@[simp]
theorem lift_comp_of : (lift ρ hρ).comp (of α μ) = ρ :=
  (ConvolutionAlgebra.fullCStarSeminorm α μ).liftNonUnital_comp_ofNonUnital ρ hρ

end FullCrossedProduct

namespace CovariantRepresentation

open FullCrossedProduct

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (P : CovariantRepresentation α H)

variable (μ) in
/-- The integrated form `π ⋊ U` of a covariant representation on a Hilbert space in any universe,
extended by continuity to a ⋆-homomorphism on the full crossed product. -/
def integratedFull : FullCrossedProduct α μ →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
  lift (P.integratedStarAlgHom μ)
    (ConvolutionAlgebra.norm_integratedStarAlgHom_le_fullSeminorm P)

/-- On the twisted convolution algebra, the extended integrated form is the integrated form. -/
@[simp]
theorem integratedFull_of (f : ConvolutionAlgebra α μ) :
    P.integratedFull μ (of α μ f) = P.integratedStarAlgHom μ f :=
  lift_of _ _ f

/-- The vector formula for the extended integrated form on the twisted convolution algebra:
`(π ⋊ U)(f) ξ = ∫ π(f(s)) U_s ξ dμ(s)`. -/
theorem integratedFull_of_apply (f : ConvolutionAlgebra α μ) (ξ : H) :
    P.integratedFull μ (of α μ f) ξ = ∫ s, P.coefficient (f.ofConv s) (P.group s ξ) ∂μ := by
  rw [integratedFull_of, integratedStarAlgHom_apply, integratedOperator_apply]

@[simp]
theorem integratedFull_comp_of :
    (P.integratedFull μ).comp (of α μ) = P.integratedStarAlgHom μ :=
  NonUnitalStarAlgHom.ext (integratedFull_of P)

/-- The extended integrated form of a covariant pair on the full crossed product vanishes
precisely when the coefficient representation is zero. -/
@[simp]
theorem integratedFull_eq_zero_iff :
    P.integratedFull μ = 0 ↔ P.coefficient = 0 := by
  refine ⟨fun h => (P.forall_integratedOperator_eq_zero_iff μ).1 fun f => ?_, fun h => ?_⟩
  · simpa only [integratedFull_of, integratedStarAlgHom_apply, ConvolutionAlgebra.ofConv_toConv,
      NonUnitalStarAlgHom.zero_apply] using DFunLike.congr_fun h (of α μ (.toConv f))
  · refine starAlgHom_ext (NonUnitalStarAlgHom.ext fun f => ?_)
    simpa only [NonUnitalStarAlgHom.comp_apply, integratedFull_of, integratedStarAlgHom_apply,
      NonUnitalStarAlgHom.zero_apply] using (P.forall_integratedOperator_eq_zero_iff μ).2 h f.ofConv

end CovariantRepresentation

namespace FullCrossedProduct

/-- The norm of the full crossed product is the least bound for the extended
integrated forms of covariant representations on Hilbert spaces in the universe `max u v`. -/
theorem norm_le_iff {x : FullCrossedProduct α μ} {c : ℝ} :
    ‖x‖ ≤ c ↔
      ∀ (H : Type (max u v)) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (P : CovariantRepresentation α H), ‖P.integratedFull μ x‖ ≤ c := by
  refine ⟨fun h _ _ _ _ P => (NonUnitalStarAlgHom.norm_apply_le _ x).trans h, fun h => ?_⟩
  -- Approximate `x` by `of f` within `ε`: every integrated form is then within `ε` at `f`, so the
  -- full seminorm of `f` is at most `c + ε`.
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨f, hf⟩ := (denseRange_of (α := α) (μ := μ)).exists_dist_lt x (half_pos hε)
  have hf' : ‖x - of α μ f‖ < ε / 2 := by rwa [← dist_eq_norm]
  have hfc : ‖of α μ f‖ ≤ c + ε / 2 := by
    rw [norm_of, ConvolutionAlgebra.fullSeminorm_le_iff]
    intro H _ _ _ P
    rw [← P.integratedFull_of]
    calc ‖P.integratedFull μ (of α μ f)‖
        ≤ ‖P.integratedFull μ x‖ + ‖P.integratedFull μ (x - of α μ f)‖ := by
          rw [map_sub, norm_sub_rev]
          exact norm_le_insert' _ _
      _ ≤ c + ε / 2 :=
          add_le_add (h H P) ((NonUnitalStarAlgHom.norm_apply_le _ _).trans hf'.le)
  calc ‖x‖ ≤ ‖of α μ f‖ + ‖x - of α μ f‖ := norm_le_insert' x (of α μ f)
    _ < c + ε := by linarith

/-- Two elements of the twisted convolution algebra have the same image in the full crossed
product exactly when their integrated forms agree for every covariant representation on a
Hilbert space in the universe `max u v`. -/
theorem of_eq_of_iff {f g : ConvolutionAlgebra α μ} :
    of α μ f = of α μ g ↔
      ∀ (H : Type (max u v)) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (P : CovariantRepresentation α H),
          P.integratedStarAlgHom μ f = P.integratedStarAlgHom μ g := by
  refine ⟨fun h H _ _ _ P => by simpa using congr(P.integratedFull μ $h), fun h => ?_⟩
  rw [← sub_eq_zero, ← map_sub, ← norm_eq_zero, norm_of]
  refine le_antisymm (ConvolutionAlgebra.fullSeminorm_le_iff.2 fun H _ _ _ P => ?_)
    (apply_nonneg _ _)
  rw [map_sub, h H P, sub_self, norm_zero]

end FullCrossedProduct

end TauCeti.CStarAction

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Regular
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Star

/-!
# The full C⋆-seminorm of a C⋆-dynamical system

Let `α` be a point-norm continuous action of a locally compact group `G : Type u` on a possibly
nonunital C⋆-algebra `A : Type v`, and let `μ` be a left Haar measure on `G`. The *full* (or
*universal*) seminorm of `f` in the twisted convolution algebra `C_c(G, A)` is

`‖f‖ᵤ = sup ‖(π ⋊ U)(f)‖`,

the supremum over all covariant representations `(π, U)` of `α` of the norms of their integrated
forms. The full crossed product `A ⋊_α G` is the completion of the convolution algebra for this
seminorm.

To avoid quantifying over all universes, the supremum ranges over covariant representations on
Hilbert spaces in the universe `max u v`. This universe contains the regular covariant
representations on `L²(G, H)` induced from representations of `A` on Hilbert spaces `H : Type v`.
It also contains the completions of quotients of `C_c(G, A)`, on which every cyclic representation
of the convolution algebra can be realized.

Every integrated form is bounded by the L¹ norm, so the supremum is finite and dominated by the L¹
norm. Since every integrated form is a ⋆-homomorphism into a C⋆-algebra of bounded operators, the
supremum is a submultiplicative, star-invariant seminorm satisfying the C⋆-identity
`‖f⋆ * f‖ᵤ = ‖f‖ᵤ * ‖f‖ᵤ`. If `A` has a faithful representation `ρ` on a Hilbert space
`H : Type v`, the integrated regular representation induced by `ρ` is injective, so the full
seminorm is a norm.

## Main definitions

* `TauCeti.CStarAction.ConvolutionAlgebra.fullSeminorm`: the full C⋆-seminorm `‖·‖ᵤ` on the
  twisted convolution algebra.

## Main statements

* `TauCeti.CStarAction.ConvolutionAlgebra.norm_integratedStarAlgHom_le_fullSeminorm`: every
  integrated form is bounded by the full seminorm.
* `TauCeti.CStarAction.ConvolutionAlgebra.fullSeminorm_le_iff`: the full seminorm is the least
  such bound.
* `TauCeti.CStarAction.ConvolutionAlgebra.fullSeminorm_le_norm`: the full seminorm is bounded by
  the L¹ norm.
* `TauCeti.CStarAction.ConvolutionAlgebra.fullSeminorm_mul_le`,
  `TauCeti.CStarAction.ConvolutionAlgebra.fullSeminorm_star` and
  `TauCeti.CStarAction.ConvolutionAlgebra.fullSeminorm_star_mul_self`: the full seminorm is a
  C⋆-seminorm.
* `TauCeti.CStarAction.ConvolutionAlgebra.fullSeminorm_eq_zero_iff`: given a faithful
  representation of `A`, the full seminorm is definite.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2 (the universal norm and the full
  crossed product).
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti.CStarAction

universe u v

variable {G : Type u} {A : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  {α : CStarAction G A} {μ : Measure G} [μ.IsHaarMeasure]

namespace ConvolutionAlgebra

variable (α μ) in
/-- The seminorms `f ↦ ‖(π ⋊ U)(f)‖` of the integrated forms of covariant representations on
Hilbert spaces in the universe `max u v`. -/
private def integratedSeminorms : Set (Seminorm ℂ (ConvolutionAlgebra α μ)) :=
  {p | ∃ (H : Type (max u v)) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H) (P : CovariantRepresentation α H),
      p = (normSeminorm ℂ (H →L[ℂ] H)).comp
        (P.integratedStarAlgHom μ : ConvolutionAlgebra α μ →ₗ[ℂ] (H →L[ℂ] H))}

private theorem bddAbove_integratedSeminorms : BddAbove (integratedSeminorms α μ) :=
  ⟨normSeminorm ℂ _, by
    rintro _ ⟨H, _, _, _, P, rfl⟩ f
    exact P.norm_integratedStarAlgHom_le_norm μ f⟩

variable (α μ) in
/-- The full C⋆-seminorm `‖f‖ᵤ = sup ‖(π ⋊ U)(f)‖` on the twisted convolution algebra: the supremum
of the norms of the integrated forms of all covariant representations of `α` on Hilbert spaces in
the universe `max u v`. Its completion is the full crossed product `A ⋊_α G`. -/
def fullSeminorm : Seminorm ℂ (ConvolutionAlgebra α μ) :=
  sSup (integratedSeminorms α μ)

/-- The full seminorm at `f` is the supremum of the norms at `f` of the integrated forms of
covariant representations on Hilbert spaces in the universe `max u v`. -/
theorem fullSeminorm_apply (f : ConvolutionAlgebra α μ) :
    fullSeminorm α μ f =
      sSup {r | ∃ (H : Type (max u v)) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : CompleteSpace H) (P : CovariantRepresentation α H),
          ‖P.integratedStarAlgHom μ f‖ = r} := by
  rw [fullSeminorm, Seminorm.sSup_apply bddAbove_integratedSeminorms, iSup]
  congr 1
  ext r
  simp [integratedSeminorms]

/-- The integrated form of every covariant representation on a Hilbert space in the universe
`max u v` is bounded by the full seminorm. -/
theorem norm_integratedStarAlgHom_le_fullSeminorm {H : Type (max u v)} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (P : CovariantRepresentation α H)
    (f : ConvolutionAlgebra α μ) : ‖P.integratedStarAlgHom μ f‖ ≤ fullSeminorm α μ f :=
  le_csSup bddAbove_integratedSeminorms ⟨H, _, _, _, P, rfl⟩ f

/-- The full seminorm is the least nonnegative bound for the integrated forms of covariant
representations on Hilbert spaces in the universe `max u v`. -/
theorem fullSeminorm_le_iff {f : ConvolutionAlgebra α μ} {c : ℝ} (hc : 0 ≤ c) :
    fullSeminorm α μ f ≤ c ↔
      ∀ (H : Type (max u v)) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (P : CovariantRepresentation α H), ‖P.integratedStarAlgHom μ f‖ ≤ c :=
  ⟨fun h _ _ _ _ P => (norm_integratedStarAlgHom_le_fullSeminorm P f).trans h,
    fun h => by
      rw [fullSeminorm, Seminorm.sSup_apply bddAbove_integratedSeminorms]
      exact Real.iSup_le (fun ⟨_, H, _, _, _, P, hp⟩ => hp ▸ h H P) hc⟩

/-- The full seminorm is bounded by the L¹ norm. -/
theorem fullSeminorm_le_norm (f : ConvolutionAlgebra α μ) : fullSeminorm α μ f ≤ ‖f‖ :=
  (fullSeminorm_le_iff (norm_nonneg f)).2 fun _ _ _ _ P => P.norm_integratedStarAlgHom_le_norm μ f

/-- The full seminorm is submultiplicative for twisted convolution. -/
theorem fullSeminorm_mul_le (f g : ConvolutionAlgebra α μ) :
    fullSeminorm α μ (f * g) ≤ fullSeminorm α μ f * fullSeminorm α μ g := by
  refine (fullSeminorm_le_iff (mul_nonneg (apply_nonneg _ f) (apply_nonneg _ g))).2
    fun _ _ _ _ P => ?_
  rw [map_mul]
  exact (norm_mul_le _ _).trans (mul_le_mul (norm_integratedStarAlgHom_le_fullSeminorm P f)
    (norm_integratedStarAlgHom_le_fullSeminorm P g) (norm_nonneg _) (apply_nonneg _ f))

/-- The full seminorm is invariant under the twisted involution. -/
@[simp]
theorem fullSeminorm_star (f : ConvolutionAlgebra α μ) :
    fullSeminorm α μ (star f) = fullSeminorm α μ f := by
  have key (g : ConvolutionAlgebra α μ) : fullSeminorm α μ (star g) ≤ fullSeminorm α μ g := by
    refine (fullSeminorm_le_iff (apply_nonneg _ g)).2 fun _ _ _ _ P => ?_
    rw [map_star, _root_.norm_star]
    exact norm_integratedStarAlgHom_le_fullSeminorm P g
  exact le_antisymm (key f) (by simpa using key (star f))

/-- The full seminorm satisfies the C⋆-identity `‖f⋆ * f‖ᵤ = ‖f‖ᵤ * ‖f‖ᵤ`. -/
theorem fullSeminorm_star_mul_self (f : ConvolutionAlgebra α μ) :
    fullSeminorm α μ (star f * f) = fullSeminorm α μ f * fullSeminorm α μ f := by
  refine le_antisymm ((fullSeminorm_mul_le _ _).trans_eq (by rw [fullSeminorm_star])) ?_
  -- Each `‖(π ⋊ U)(f)‖` is the square root of `‖(π ⋊ U)(f⋆ * f)‖ ≤ ‖f⋆ * f‖ᵤ`.
  have hsqrt : fullSeminorm α μ f ≤ √(fullSeminorm α μ (star f * f)) := by
    refine (fullSeminorm_le_iff (Real.sqrt_nonneg _)).2 fun _ _ _ _ P => ?_
    refine Real.le_sqrt_of_sq_le ?_
    rw [sq, ← CStarRing.norm_star_mul_self, ← map_star, ← map_mul]
    exact norm_integratedStarAlgHom_le_fullSeminorm P _
  calc fullSeminorm α μ f * fullSeminorm α μ f
      ≤ √(fullSeminorm α μ (star f * f)) * √(fullSeminorm α μ (star f * f)) :=
        mul_le_mul hsqrt hsqrt (apply_nonneg _ f) (Real.sqrt_nonneg _)
    _ = fullSeminorm α μ (star f * f) := Real.mul_self_sqrt (apply_nonneg _ _)

/-- If `A` has a faithful representation `ρ` on a Hilbert space `H : Type v`, the full seminorm is
a norm: the integrated regular representation on `L²(G, H)` induced by `ρ` is injective and
bounded by the full seminorm. -/
theorem fullSeminorm_eq_zero_iff [μ.InnerRegularCompactLTTop] {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hρ : Function.Injective ρ) {f : ConvolutionAlgebra α μ} :
    fullSeminorm α μ f = 0 ↔ f = 0 := by
  refine ⟨fun hf => ext ?_, fun hf => hf ▸ map_zero _⟩
  refine CovariantRepresentation.injective_integratedOperator_regular (α := α) (μ := μ) hρ ?_
  rw [ofConv_zero, map_zero, ← CovariantRepresentation.integratedStarAlgHom_apply,
    ← norm_le_zero_iff, ← hf]
  exact norm_integratedStarAlgHom_le_fullSeminorm (CovariantRepresentation.regular α ρ μ) f

end ConvolutionAlgebra

end TauCeti.CStarAction

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Full

/-!
# Concrete regular crossed products

For a representation `ρ` of a possibly nonunital C⋆-algebra `A`, the regular covariant
representation of `(A, G, α)` acts on `L²(G, H)`. Its integrated image generates a concrete
C⋆-algebra `regularAlgebra α ρ μ`, the operator-norm closure of that image. The canonical map
`RegularCrossedProduct.of` has dense range and is injective when `ρ` is faithful.
Thus this algebra realizes the completion of compactly supported coefficients in the norm
of the chosen regular representation.

The construction keeps `ρ` as a parameter: no independence of the inducing representation
is asserted. For representations in the universe of the coefficient algebra, the extended
integrated form on the full crossed product takes values in this concrete algebra. Its
corestriction `RegularCrossedProduct.fromFull` has dense range and gives the usual regular
norm bound by the full norm. Surjectivity of this map is not asserted here.

No nondegeneracy, separability, second countability or global σ-finiteness is assumed.

## References

Dana Williams, *Crossed Products of C*-Algebras*, Chapter 7, for the concrete regular
realization of reduced crossed products. The construction uses
`CovariantRepresentation.regular` and its vector-integrated form, and Mathlib's topological
closure of a nonunital star subalgebra.
-/

public section

noncomputable section

open MeasureTheory
open scoped CStarAlgebra

namespace TauCeti.CStarAction

universe u v w

variable {G : Type u} {A : Type v} {H : Type w}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (α : CStarAction G A) (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (μ : Measure G)
  [μ.IsHaarMeasure] [μ.InnerRegularCompactLTTop]

/-- The concrete regular crossed-product algebra associated to `ρ`: the norm closure of the
integrated regular representation of compactly supported coefficients on `L²(G, H)`. -/
def regularAlgebra : NonUnitalStarSubalgebra ℂ (Lp H 2 μ →L[ℂ] Lp H 2 μ) :=
  ((CovariantRepresentation.regular α ρ μ).integratedStarAlgHom μ).range.topologicalClosure

instance : IsClosed (regularAlgebra α ρ μ : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ)) :=
  isClosed_closure

/-- An operator belongs to the concrete regular algebra exactly when it can be approximated
in operator norm by integrated compactly supported coefficients. -/
theorem mem_regularAlgebra_iff (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) :
    T ∈ regularAlgebra α ρ μ ↔ ∀ ε > 0, ∃ f : ConvolutionAlgebra α μ,
      dist T ((CovariantRepresentation.regular α ρ μ).integratedStarAlgHom μ f) < ε :=
  Metric.mem_closure_range_iff

namespace RegularCrossedProduct

/-- The canonical map from compactly supported convolution coefficients to the concrete
regular algebra. -/
def of : ConvolutionAlgebra α μ →⋆ₙₐ[ℂ] regularAlgebra α ρ μ :=
  ((CovariantRepresentation.regular α ρ μ).integratedStarAlgHom μ).codRestrict
    (regularAlgebra α ρ μ) fun f =>
      NonUnitalStarSubalgebra.le_topologicalClosure _ ⟨f, rfl⟩

/-- As an operator, the canonical map is the integrated regular representation. -/
@[simp]
theorem coe_of (f : ConvolutionAlgebra α μ) :
    (of α ρ μ f : Lp H 2 μ →L[ℂ] Lp H 2 μ) =
      (CovariantRepresentation.regular α ρ μ).integratedStarAlgHom μ f :=
  (rfl)

/-- The regular norm of a compactly supported coefficient is its integrated operator norm. -/
theorem norm_of (f : ConvolutionAlgebra α μ) :
    ‖of α ρ μ f‖ = ‖(CovariantRepresentation.regular α ρ μ).integratedOperator μ f.ofConv‖ := by
  rw [← (CovariantRepresentation.regular α ρ μ).integratedStarAlgHom_apply]
  rfl

/-- The regular norm is bounded by the L¹ norm. -/
theorem norm_of_le (f : ConvolutionAlgebra α μ) : ‖of α ρ μ f‖ ≤ ‖f‖ := by
  rw [norm_of, ConvolutionAlgebra.norm_eq_integral_norm]
  exact (CovariantRepresentation.regular α ρ μ).norm_integratedOperator_le μ f.ofConv

/-- The compact-support inclusion is continuous for the L¹ topology. -/
@[fun_prop]
theorem continuous_of : Continuous (of α ρ μ) :=
  AddMonoidHomClass.continuous_of_bound (of α ρ μ) 1 fun f => by
    simpa only [one_mul] using norm_of_le α ρ μ f

/-- Compactly supported coefficients are dense in the concrete regular algebra. -/
theorem denseRange_of : DenseRange (of α ρ μ) := by
  let T := (CovariantRepresentation.regular α ρ μ).integratedStarAlgHom μ
  have hd : DenseRange (Set.inclusion (s := Set.range T) subset_closure) :=
    (denseRange_inclusion_iff subset_closure).2 subset_rfl
  exact hd.comp Set.rangeFactorization_surjective.denseRange (continuous_inclusion subset_closure)

/-- Closed properties of the concrete regular algebra can be checked on compactly supported
coefficients. -/
@[elab_as_elim]
theorem induction_on {p : regularAlgebra α ρ μ → Prop} (x : regularAlgebra α ρ μ)
    (hp : IsClosed {x | p x}) (ih : ∀ f, p (of α ρ μ f)) : p x :=
  (denseRange_of α ρ μ).induction (by rintro _ ⟨f, rfl⟩; exact ih f) hp x

/-- A faithful coefficient representation gives a faithful compact-support inclusion. -/
theorem of_injective (hρ : Function.Injective ρ) : Function.Injective (of α ρ μ) := by
  intro f g h
  apply ConvolutionAlgebra.ofConv_injective
  apply (CovariantRepresentation.injective_integratedOperator_regular (α := α) (μ := μ) hρ)
  simpa only [coe_of, CovariantRepresentation.integratedStarAlgHom_apply] using
    congrArg (fun x : regularAlgebra α ρ μ => (x : Lp H 2 μ →L[ℂ] Lp H 2 μ)) h

/-- Homomorphisms out of the concrete regular algebra are determined on compactly supported
coefficients. -/
@[ext]
theorem starAlgHom_ext {B : Type*} [NonUnitalCStarAlgebra B]
    {φ ψ : regularAlgebra α ρ μ →⋆ₙₐ[ℂ] B}
    (h : φ.comp (of α ρ μ) = ψ.comp (of α ρ μ)) : φ = ψ :=
  NonUnitalStarAlgHom.ext fun x => induction_on α ρ μ x
    (isClosed_eq (map_continuous φ) (map_continuous ψ)) fun f => congr($h f)

end RegularCrossedProduct

section Full

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))

namespace RegularCrossedProduct

/-- The regular norm is dominated by the full C⋆-seminorm. -/
theorem norm_of_le_fullSeminorm (f : ConvolutionAlgebra α μ) :
    ‖of α ρ μ f‖ ≤ ConvolutionAlgebra.fullSeminorm α μ f :=
  ConvolutionAlgebra.norm_integratedStarAlgHom_le_fullSeminorm
    (CovariantRepresentation.regular α ρ μ) f

/-- The extended integrated regular representation takes its values in the concrete regular
algebra. -/
private theorem integratedFull_mem (x : FullCrossedProduct α μ) :
    (CovariantRepresentation.regular α ρ μ).integratedFull μ x ∈ regularAlgebra α ρ μ := by
  induction x using FullCrossedProduct.induction_on with
  | hp =>
    have hc : IsClosed (regularAlgebra α ρ μ : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ)) := inferInstance
    exact hc.preimage (map_continuous _)
  | ih f =>
    rw [CovariantRepresentation.integratedFull_of]
    exact (of α ρ μ f).property

/-- The full crossed product maps to the concrete regular algebra by the extended integrated
regular representation. -/
def fromFull : FullCrossedProduct α μ →⋆ₙₐ[ℂ] regularAlgebra α ρ μ :=
  ((CovariantRepresentation.regular α ρ μ).integratedFull μ).codRestrict
    (regularAlgebra α ρ μ) (integratedFull_mem α μ ρ)

/-- The regular comparison map agrees with the compact-support inclusion. -/
@[simp]
theorem fromFull_of (f : ConvolutionAlgebra α μ) :
    fromFull α μ ρ (FullCrossedProduct.of α μ f) = of α ρ μ f := by
  apply Subtype.ext
  exact (CovariantRepresentation.regular α ρ μ).integratedFull_of f

/-- As an operator, the regular comparison map is the extended integrated form. -/
@[simp]
theorem coe_fromFull (x : FullCrossedProduct α μ) :
    (fromFull α μ ρ x : Lp H 2 μ →L[ℂ] Lp H 2 μ) =
      (CovariantRepresentation.regular α ρ μ).integratedFull μ x :=
  (rfl)

/-- The regular comparison map has dense range. -/
theorem denseRange_fromFull : DenseRange (fromFull α μ ρ) := by
  intro x
  apply closure_mono (s := Set.range (of α ρ μ)) ?_ ((denseRange_of α ρ μ) x)
  rintro _ ⟨f, rfl⟩
  exact ⟨FullCrossedProduct.of α μ f, fromFull_of α μ ρ f⟩

end RegularCrossedProduct

end Full

end TauCeti.CStarAction

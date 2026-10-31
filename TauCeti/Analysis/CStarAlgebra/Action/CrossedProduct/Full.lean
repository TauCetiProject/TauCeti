/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Topology.Algebra.LinearMapCompletion
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.FullSeminorm
public import TauCeti.Analysis.CStarAlgebra.Completion

/-!
# The full crossed product of a C⋆-dynamical system

Let `α` be a point-norm continuous action of a locally compact group `G : Type u` on a possibly
nonunital C⋆-algebra `A : Type v`, and let `μ` be a left Haar measure on `G`. The *full crossed
product* `A ⋊_α G` is the completion of the twisted convolution algebra `C_c(G, A)` in the full
C⋆-seminorm `‖f‖ᵤ = sup ‖(π ⋊ U)(f)‖`, the supremum over covariant representations `(π, U)` on
Hilbert spaces in the universe `max u v`.

The twisted convolution algebra already carries its L¹ norm, so the full seminorm lives on the
type synonym `FullConvolutionAlgebra α μ`. Since the full seminorm is a submultiplicative,
star-invariant seminorm satisfying the C⋆-identity, the completion
`FullCrossedProduct α μ` is a nonunital C⋆-algebra. The canonical ⋆-homomorphism
`FullCrossedProduct.of` from the twisted convolution algebra has dense range, and
`‖of f‖ = ‖f‖ᵤ`. It is injective whenever `A` has a faithful representation in its own universe.

Every integrated form `π ⋊ U` of a covariant representation on a Hilbert space in the universe
`max u v` extends uniquely to a ⋆-homomorphism `CovariantRepresentation.integratedFull` on the
full crossed product. The norm of `A ⋊_α G` is the supremum of the norms of these extensions,
`FullCrossedProduct.norm_le_iff`. No unit, separability, σ-finiteness or nondegeneracy is
assumed.

## Main definitions

* `TauCeti.CStarAction.FullConvolutionAlgebra`: the twisted convolution algebra with the full
  C⋆-seminorm.
* `TauCeti.CStarAction.FullCrossedProduct`: the full crossed product `A ⋊_α G`, a nonunital
  C⋆-algebra.
* `TauCeti.CStarAction.FullCrossedProduct.of`: the canonical ⋆-homomorphism from the twisted
  convolution algebra, with dense range.
* `TauCeti.CStarAction.CovariantRepresentation.integratedFull`: the extension of the integrated
  form of a covariant representation to the full crossed product.

## Main statements

* `TauCeti.CStarAction.FullCrossedProduct.norm_of`: `‖of f‖ = ‖f‖ᵤ`.
* `TauCeti.CStarAction.FullCrossedProduct.of_injective`: given a faithful representation of `A`,
  the canonical map is injective.
* `TauCeti.CStarAction.FullCrossedProduct.starAlgHom_ext`: ⋆-homomorphisms out of the full
  crossed product are determined on the twisted convolution algebra.
* `TauCeti.CStarAction.FullCrossedProduct.norm_le_iff`: the norm of the full crossed product is
  the least bound for the integrated forms of covariant representations.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2 (the universal norm and the full
  crossed product).
-/

public section

noncomputable section

open MeasureTheory UniformSpace

namespace TauCeti.CStarAction

universe u v

variable {G : Type u} {A : Type v} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [NonUnitalCStarAlgebra A] {α : CStarAction G A} {μ : Measure G}

variable (α μ) in
/-- The twisted convolution algebra `C_c(G, A)` of `(A, G, α)`, with the full C⋆-seminorm
`ConvolutionAlgebra.fullSeminorm α μ` in place of the L¹ norm. Its completion is the full crossed
product `FullCrossedProduct α μ`. Use `FullConvolutionAlgebra.toFull` and
`FullConvolutionAlgebra.ofFull` to pass to and from `ConvolutionAlgebra α μ`. -/
@[expose] def FullConvolutionAlgebra : Type (max u v) :=
  ConvolutionAlgebra α μ

namespace FullConvolutionAlgebra

/-- Regard an element of the twisted convolution algebra as an element with the full seminorm. -/
def toFull : ConvolutionAlgebra α μ ≃ FullConvolutionAlgebra α μ :=
  Equiv.refl _

/-- The element of the twisted convolution algebra underlying an element with the full
seminorm. -/
def ofFull : FullConvolutionAlgebra α μ ≃ ConvolutionAlgebra α μ :=
  Equiv.refl _

@[simp]
theorem toFull_symm : (toFull (α := α) (μ := μ)).symm = ofFull :=
  (rfl)

@[simp]
theorem ofFull_symm : (ofFull (α := α) (μ := μ)).symm = toFull :=
  (rfl)

@[simp]
theorem ofFull_toFull (f : ConvolutionAlgebra α μ) : ofFull (toFull f) = f :=
  (rfl)

@[simp]
theorem toFull_ofFull (f : FullConvolutionAlgebra α μ) : toFull (ofFull f) = f :=
  (rfl)

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure]

instance : NonUnitalRing (FullConvolutionAlgebra α μ) :=
  inferInstanceAs (NonUnitalRing (ConvolutionAlgebra α μ))

instance : StarRing (FullConvolutionAlgebra α μ) :=
  inferInstanceAs (StarRing (ConvolutionAlgebra α μ))

instance : Module ℂ (FullConvolutionAlgebra α μ) :=
  inferInstanceAs (Module ℂ (ConvolutionAlgebra α μ))

instance : IsScalarTower ℂ (FullConvolutionAlgebra α μ) (FullConvolutionAlgebra α μ) :=
  inferInstanceAs (IsScalarTower ℂ (ConvolutionAlgebra α μ) (ConvolutionAlgebra α μ))

instance : SMulCommClass ℂ (FullConvolutionAlgebra α μ) (FullConvolutionAlgebra α μ) :=
  inferInstanceAs (SMulCommClass ℂ (ConvolutionAlgebra α μ) (ConvolutionAlgebra α μ))

instance : StarModule ℂ (FullConvolutionAlgebra α μ) :=
  inferInstanceAs (StarModule ℂ (ConvolutionAlgebra α μ))

variable (α μ) in
/-- `FullConvolutionAlgebra.toFull` as an isomorphism of ⋆-algebras. -/
def toFullStarAlgEquiv : ConvolutionAlgebra α μ ≃⋆ₐ[ℂ] FullConvolutionAlgebra α μ where
  __ := toFull
  map_mul' _ _ := (rfl)
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)
  map_star' _ := (rfl)

@[simp]
theorem toFullStarAlgEquiv_apply (f : ConvolutionAlgebra α μ) :
    toFullStarAlgEquiv α μ f = toFull f :=
  (rfl)

@[simp]
theorem toFullStarAlgEquiv_symm_apply (f : FullConvolutionAlgebra α μ) :
    (toFullStarAlgEquiv α μ).symm f = ofFull f :=
  (rfl)

/-- The full seminorm makes the twisted convolution algebra a seminormed group. -/
instance : SeminormedAddCommGroup (FullConvolutionAlgebra α μ) :=
  @AddGroupSeminorm.toSeminormedAddCommGroup (FullConvolutionAlgebra α μ) _
    (ConvolutionAlgebra.fullSeminorm α μ).toAddGroupSeminorm

/-- The norm of an element of the full convolution algebra is its full seminorm. -/
@[simp]
theorem norm_toFull (f : ConvolutionAlgebra α μ) :
    ‖toFull f‖ = ConvolutionAlgebra.fullSeminorm α μ f :=
  (rfl)

/-- The norm of an element of the full convolution algebra is the full seminorm of the underlying
element of the twisted convolution algebra. -/
theorem norm_def (f : FullConvolutionAlgebra α μ) :
    ‖f‖ = ConvolutionAlgebra.fullSeminorm α μ (ofFull f) :=
  (rfl)

instance : NormedSpace ℂ (FullConvolutionAlgebra α μ) where
  __ : Module ℂ (FullConvolutionAlgebra α μ) := inferInstance
  norm_smul_le c f := by
    simp only [norm_def, ← toFullStarAlgEquiv_symm_apply, map_smul]
    exact (map_smul_eq_mul _ _ _).le

/-- The full seminorm is submultiplicative, so the twisted convolution algebra is a seminormed
ring for it. -/
instance : NonUnitalSeminormedRing (FullConvolutionAlgebra α μ) where
  __ : SeminormedAddCommGroup (FullConvolutionAlgebra α μ) := inferInstance
  __ : NonUnitalRing (FullConvolutionAlgebra α μ) := inferInstance
  norm_mul_le f g := by
    simpa only [norm_def, ← toFullStarAlgEquiv_symm_apply, map_mul] using
      ConvolutionAlgebra.fullSeminorm_mul_le (ofFull f) (ofFull g)

/-- The twisted involution is isometric for the full seminorm. -/
instance : NormedStarGroup (FullConvolutionAlgebra α μ) where
  norm_star_le f := by
    simp only [norm_def, ← toFullStarAlgEquiv_symm_apply, map_star,
      ConvolutionAlgebra.fullSeminorm_star, le_refl]

/-- The full seminorm satisfies the C⋆-identity on the twisted convolution algebra. -/
theorem norm_star_mul_self (f : FullConvolutionAlgebra α μ) : ‖star f * f‖ = ‖f‖ * ‖f‖ := by
  simpa only [norm_def, ← toFullStarAlgEquiv_symm_apply, map_mul, map_star] using
    ConvolutionAlgebra.fullSeminorm_star_mul_self (ofFull f)

end FullConvolutionAlgebra

open FullConvolutionAlgebra

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure]

variable (α μ) in
/-- The full crossed product `A ⋊_α G` of the C⋆-dynamical system `(A, G, α)`: the completion of
the twisted convolution algebra in the full C⋆-seminorm. It is a nonunital C⋆-algebra, and
`FullCrossedProduct.of` embeds the twisted convolution algebra densely. -/
@[expose] def FullCrossedProduct : Type (max u v) :=
  Completion (FullConvolutionAlgebra α μ)

namespace FullCrossedProduct

/-- The completion of the twisted convolution algebra in the full seminorm is a C⋆-algebra. -/
instance : NonUnitalCStarAlgebra (Completion (FullConvolutionAlgebra α μ)) where
  toCStarRing := Completion.cstarRing fun f => (norm_star_mul_self f).ge

/-- The full crossed product is a nonunital C⋆-algebra. -/
instance : NonUnitalCStarAlgebra (FullCrossedProduct α μ) :=
  inferInstanceAs (NonUnitalCStarAlgebra (Completion (FullConvolutionAlgebra α μ)))

variable (α μ) in
/-- The canonical ⋆-homomorphism from the twisted convolution algebra into the full crossed
product. -/
def of : ConvolutionAlgebra α μ →⋆ₙₐ[ℂ] FullCrossedProduct α μ where
  toFun f := (toFullStarAlgEquiv α μ f : Completion (FullConvolutionAlgebra α μ))
  map_smul' c f := by
    rw [map_smul]
    exact Completion.coe_smul c _
  map_zero' := by
    rw [map_zero]
    exact Completion.coe_zero
  map_add' f g := by
    rw [map_add]
    exact Completion.coe_add _ _
  map_mul' f g := by
    rw [map_mul]
    exact Completion.coe_mul' _ _
  map_star' f := by
    rw [map_star]
    exact Completion.coe_star _

/-- An element of the dense subalgebra of the completion is the image of the underlying element
of the twisted convolution algebra. -/
private theorem coe_eq_of (f : FullConvolutionAlgebra α μ) :
    ((f : Completion (FullConvolutionAlgebra α μ)) : FullCrossedProduct α μ) = of α μ (ofFull f) :=
  (rfl)

/-- The norm of the image of `f` in the full crossed product is its full seminorm `‖f‖ᵤ`. -/
@[simp]
theorem norm_of (f : ConvolutionAlgebra α μ) :
    ‖of α μ f‖ = ConvolutionAlgebra.fullSeminorm α μ f :=
  Completion.norm_coe (toFull f)

/-- The image of `f` in the full crossed product has norm at most its L¹ norm. -/
theorem norm_of_le (f : ConvolutionAlgebra α μ) : ‖of α μ f‖ ≤ ‖f‖ :=
  (norm_of f).trans_le (ConvolutionAlgebra.fullSeminorm_le_norm f)

/-- The canonical map is continuous for the L¹ topology on the twisted convolution algebra. -/
theorem continuous_of : Continuous (of α μ) :=
  AddMonoidHomClass.continuous_of_bound (of α μ) 1 fun f => by
    simpa only [one_mul] using norm_of_le f

/-- The twisted convolution algebra is dense in the full crossed product. -/
theorem denseRange_of : DenseRange (of α μ) :=
  Completion.denseRange_coe.comp toFull.surjective.denseRange (Completion.continuous_coe _)

/-- To prove a closed property of every element of the full crossed product, it suffices to
prove it on the twisted convolution algebra. -/
@[elab_as_elim]
theorem induction_on {p : FullCrossedProduct α μ → Prop} (x : FullCrossedProduct α μ)
    (hp : IsClosed {x | p x}) (ih : ∀ f, p (of α μ f)) : p x :=
  Completion.induction_on (p := p) x hp fun f => coe_eq_of f ▸ ih (ofFull f)

/-- If `A` has a faithful representation on a Hilbert space `H : Type v`, the canonical map from
the twisted convolution algebra into the full crossed product is injective. -/
theorem of_injective [μ.InnerRegularCompactLTTop] {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hρ : Function.Injective ρ) : Function.Injective (of α μ) :=
  (injective_iff_map_eq_zero (of α μ)).2 fun f hf =>
    (ConvolutionAlgebra.fullSeminorm_eq_zero_iff hρ).1 (by rw [← norm_of, hf, norm_zero])

open scoped CStarAlgebra in
/-- ⋆-homomorphisms from the full crossed product into a C⋆-algebra are determined by their
values on the twisted convolution algebra. -/
@[ext]
theorem starAlgHom_ext {B : Type*} [NonUnitalCStarAlgebra B]
    {φ ψ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] B} (h : φ.comp (of α μ) = ψ.comp (of α μ)) :
    φ = ψ :=
  NonUnitalStarAlgHom.ext fun x => induction_on x (isClosed_eq (map_continuous φ)
    (map_continuous ψ)) fun f => congr($h f)

end FullCrossedProduct

namespace CovariantRepresentation

open FullCrossedProduct

variable {H : Type (max u v)} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (P : CovariantRepresentation α H)

variable (μ) in
/-- The integrated form `π ⋊ U` as a continuous linear map on the twisted convolution algebra
with the full seminorm, for which it is a contraction. -/
private def integratedFullCLM : FullConvolutionAlgebra α μ →L[ℂ] (H →L[ℂ] H) :=
  ((P.integratedStarAlgHom μ : ConvolutionAlgebra α μ →ₗ[ℂ] (H →L[ℂ] H)).comp
    ((toFullStarAlgEquiv α μ).symm :
      FullConvolutionAlgebra α μ →ₗ[ℂ] ConvolutionAlgebra α μ)).mkContinuous 1 fun f => by
      simpa [norm_def] using ConvolutionAlgebra.norm_integratedStarAlgHom_le_fullSeminorm P
        (ofFull f)

private theorem fromCompletion_integratedFullCLM_of (f : ConvolutionAlgebra α μ) :
    (integratedFullCLM μ P).fromCompletion (of α μ f) = P.integratedStarAlgHom μ f := by
  have h := ContinuousLinearMap.fromCompletion_apply_coe (integratedFullCLM μ P) (toFull f)
  rw [coe_eq_of, ofFull_toFull] at h
  simpa [integratedFullCLM] using h

variable (μ) in
/-- The integrated form `π ⋊ U` of a covariant representation on a Hilbert space in the universe
`max u v`, extended by continuity to a ⋆-homomorphism on the full crossed product. -/
def integratedFull : FullCrossedProduct α μ →⋆ₙₐ[ℂ] (H →L[ℂ] H) where
  toFun := (integratedFullCLM μ P).fromCompletion
  map_smul' := map_smul _
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' x y := by
    induction x using induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih f =>
      induction y using induction_on with
      | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
      | ih g => simp only [← map_mul, fromCompletion_integratedFullCLM_of]
  map_star' x := by
    induction x using induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih f => simp only [← map_star, fromCompletion_integratedFullCLM_of]

/-- On the twisted convolution algebra, the extended integrated form is the integrated form. -/
@[simp]
theorem integratedFull_of (f : ConvolutionAlgebra α μ) :
    P.integratedFull μ (of α μ f) = P.integratedStarAlgHom μ f :=
  fromCompletion_integratedFullCLM_of P f

@[simp]
theorem integratedFull_comp_of :
    (P.integratedFull μ).comp (of α μ) = P.integratedStarAlgHom μ :=
  NonUnitalStarAlgHom.ext (integratedFull_of P)

end CovariantRepresentation

namespace FullCrossedProduct

/-- The norm of the full crossed product is the least nonnegative bound for the extended
integrated forms of covariant representations on Hilbert spaces in the universe `max u v`. -/
theorem norm_le_iff {x : FullCrossedProduct α μ} {c : ℝ} (hc : 0 ≤ c) :
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
    rw [norm_of, ConvolutionAlgebra.fullSeminorm_le_iff (by positivity)]
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

end FullCrossedProduct

end TauCeti.CStarAction

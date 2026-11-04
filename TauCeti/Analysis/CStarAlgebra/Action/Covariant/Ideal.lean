/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Comap
public import TauCeti.Analysis.CStarAlgebra.Representation.Ideal
public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace

/-!
# Extending covariant representations from closed invariant ideals

For any covariant representation `(π, U)` of a C⋆-dynamical system `(A, G, α)`, the unitary group
operators `U g` leave both the essential subspace `π.essentialSubspace` and its orthogonal
complement invariant, so `π.essentialSubspace` reduces `U g`.

Now let `I` be a closed `α`-invariant two-sided star ideal of `A`, equipped with the restricted
action `hI.restrict : CStarAction G I`. Every covariant representation `P` of `hI.restrict` on a
Hilbert space `H` extends canonically to a covariant representation `P.idealExtension hmul` of `α`
on the *same* Hilbert space `H`, keeping the unitary group representation `P.group` unchanged and
extending `P.coefficient` via `NonUnitalStarAlgHom.idealExtension`. Pulling back along the
equivariant inclusion `hI.subtypeHom` recovers `P`, and when `P.coefficient` is nondegenerate on
`I` this extension is unique among all covariant representations of `α` pulling back to `P`.

Because `I` and `A` live in the same universe, extending covariant representations on Hilbert
spaces in `Type (max u v)` shows that `hI.subtypeHom.convolutionMap μ` preserves the full
C⋆-seminorm `ConvolutionAlgebra.fullSeminorm` identically.

## Main definitions and results

* `TauCeti.CStarAction.CovariantRepresentation.isReducing_essentialSubspace_group`: the essential
  subspace of the coefficient representation reduces every group operator `P.group g`.
* `TauCeti.CStarAction.CovariantRepresentation.idealExtension`: canonical extension of a covariant
  representation from a closed invariant two-sided star ideal `I` to `A` on the same Hilbert space.
* `TauCeti.CStarAction.CovariantRepresentation.comap_idealExtension_subtypeHom`,
  `TauCeti.CStarAction.CovariantRepresentation.eq_idealExtension_iff`, and
  `TauCeti.CStarAction.CovariantRepresentation.eq_idealExtension_of_comap_eq`: pullback recovery
  and uniqueness of the extended covariant pair.
* `IsInvariant.fullSeminorm_convolutionMap_subtypeHom`: the equivariant
  inclusion of a closed invariant two-sided star ideal is isometric for the full C⋆-seminorm on
  compactly supported functions.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Proposition 3.19.
-/

public section

noncomputable section

open MeasureTheory UniformSpace

namespace TauCeti.CStarAction.CovariantRepresentation

section EssentialSubspace

variable {G A H : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)

/-- Every group operator of a covariant representation preserves the essential subspace of the
coefficient representation. -/
theorem group_apply_mem_essentialSubspace (g : G) {ξ : H}
    (hξ : ξ ∈ P.coefficient.essentialSubspace) :
    P.group g ξ ∈ P.coefficient.essentialSubspace := by
  have hle : P.coefficient.essentialSubspace ≤
      P.coefficient.essentialSubspace.comap (P.group g).toLinearMap := by
    refine (P.coefficient.essentialSubspace_le_iff
      (P.coefficient.isClosed_essentialSubspace.preimage (P.group g).continuous)).2 fun a v => ?_
    rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe, P.covariance]
    exact P.coefficient.apply_mem_essentialSubspace (α g a) (P.group g v)
  exact hle hξ

/-- Every group operator of a covariant representation preserves the orthogonal complement of the
essential subspace of the coefficient representation. -/
theorem group_apply_mem_orthogonal_essentialSubspace (g : G) {ξ : H}
    (hξ : ξ ∈ P.coefficient.essentialSubspaceᗮ) :
    P.group g ξ ∈ P.coefficient.essentialSubspaceᗮ := by
  refine P.coefficient.mem_orthogonal_essentialSubspace_iff.2 fun a => ?_
  have hcov := P.covariance g (α g⁻¹ a) ξ
  rw [α.apply_inv_apply] at hcov
  rw [← hcov, P.coefficient.apply_eq_zero_of_mem_orthogonal_essentialSubspace hξ, map_zero]

/-- The essential subspace of the coefficient representation reduces every group operator. -/
theorem isReducing_essentialSubspace_group (g : G) :
    P.coefficient.essentialSubspace.IsReducing (P.group g) :=
  (Submodule.isReducing_iff _ _).2
    ⟨fun _ hξ => P.group_apply_mem_essentialSubspace g hξ,
      fun _ hξ => P.group_apply_mem_orthogonal_essentialSubspace g hξ⟩

/-- The orthogonal projection onto the essential subspace commutes with every group operator. -/
theorem commute_starProjection_essentialSubspace_group (g : G) :
    Commute P.coefficient.essentialSubspace.starProjection (P.group g) :=
  Submodule.isReducing_coe_iff_commute_starProjection.1 (P.isReducing_essentialSubspace_group g)

end EssentialSubspace

section IdealExtension

variable {G A H : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} {I : NonUnitalStarSubalgebra ℂ A} [IsClosed (I : Set A)]
  {hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)}
  (P : CovariantRepresentation hI.restrict H)

/-- Extend a covariant representation of a closed invariant star ideal `I` to a covariant
representation of `A` on the same Hilbert space `H`, keeping the group representation unchanged. -/
def idealExtension (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) : CovariantRepresentation α H where
  coefficient := P.coefficient.idealExtension hmul
  group := P.group
  isUnitary := P.isUnitary
  continuous_orbit := P.continuous_orbit
  covariance g a v := by
    -- Check operator covariance on the essential subspace via ideal multiplication and on its
    -- orthogonal complement via `group`-invariance of `essentialSubspaceᗮ`.
    have hop : P.group g * P.coefficient.idealExtension hmul a =
        P.coefficient.idealExtension hmul (α g a) * P.group g := by
      refine P.coefficient.ext_of_orthogonal_essentialSubspace (fun x => ?_) (fun ξ hξ => ?_)
      · have hact : hI.restrict g ⟨a * x, hmul a x x.2⟩ =
            ⟨α g a * hI.restrict g x, hmul (α g a) _ (hI.restrict g x).2⟩ :=
          Subtype.ext (by simp [map_mul])
        calc (P.group g * P.coefficient.idealExtension hmul a) * P.coefficient x
            = P.group g * (P.coefficient.idealExtension hmul a * P.coefficient x) :=
              mul_assoc _ _ _
          _ = P.group g * P.coefficient ⟨a * x, hmul a x x.2⟩ := by
              rw [P.coefficient.idealExtension_mul_eq]
          _ = P.coefficient (hI.restrict g ⟨a * x, hmul a x x.2⟩) * P.group g :=
              P.group_mul_coefficient g _
          _ = P.coefficient ⟨α g a * hI.restrict g x, hmul (α g a) _ (hI.restrict g x).2⟩ *
                P.group g := by
              rw [hact]
          _ = (P.coefficient.idealExtension hmul (α g a) * P.coefficient (hI.restrict g x)) *
                P.group g := by
              rw [P.coefficient.idealExtension_mul_eq]
          _ = P.coefficient.idealExtension hmul (α g a) * (P.group g * P.coefficient x) := by
              rw [mul_assoc, P.group_mul_coefficient]
          _ = (P.coefficient.idealExtension hmul (α g a) * P.group g) * P.coefficient x :=
              (mul_assoc _ _ _).symm
      · simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
          P.coefficient.idealExtension_apply_eq_zero hmul a hξ, map_zero,
          P.coefficient.idealExtension_apply_eq_zero hmul (α g a)
            (P.group_apply_mem_orthogonal_essentialSubspace g hξ)]
    exact congr($hop v)

@[simp]
theorem idealExtension_coefficient (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) :
    (P.idealExtension hmul).coefficient = P.coefficient.idealExtension hmul :=
  (rfl)

@[simp]
theorem idealExtension_group (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) :
    (P.idealExtension hmul).group = P.group :=
  (rfl)

/-- Pulling back `P.idealExtension hmul` along the equivariant ideal inclusion recovers `P`. -/
@[simp]
theorem comap_idealExtension_subtypeHom (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) :
    (P.idealExtension hmul).comap hI.subtypeHom = P :=
  CovariantRepresentation.ext (NonUnitalStarAlgHom.ext fun x => by simp) (by simp)

/-- Characterization of `P.idealExtension hmul` as the unique covariant representation of `α`
pulling back to `P` whose coefficient operators vanish on `P.coefficient.essentialSubspaceᗮ`. -/
theorem eq_idealExtension_iff (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I)
    {Q : CovariantRepresentation α H} :
    Q = P.idealExtension hmul ↔
      Q.comap hI.subtypeHom = P ∧
        ∀ a, ∀ ξ ∈ P.coefficient.essentialSubspaceᗮ, Q.coefficient a ξ = 0 := by
  refine ⟨fun h => h ▸ ⟨P.comap_idealExtension_subtypeHom hmul,
      fun a _ hξ => P.coefficient.idealExtension_apply_eq_zero hmul a hξ⟩,
    fun ⟨hQ, horth⟩ => ?_⟩
  have hgroup : Q.group = P.group := by simpa using congrArg group hQ
  have hcoef_coe : ∀ x : I, Q.coefficient x = P.coefficient x := fun x => by
    simpa using DFunLike.congr_fun (congrArg coefficient hQ) x
  refine CovariantRepresentation.ext (NonUnitalStarAlgHom.ext fun a => ?_) hgroup
  refine (P.coefficient.eq_idealExtension_iff hmul).2 ⟨fun x => ?_, horth a⟩
  rw [← hcoef_coe x, ← map_mul, ← hcoef_coe ⟨a * x, hmul a x x.2⟩]

/-- When `P.coefficient` is nondegenerate on `I`, `P.idealExtension hmul` is the unique covariant
representation of `α` pulling back to `P`. -/
theorem eq_idealExtension_of_comap_eq (hP : P.coefficient.IsNondegenerate)
    (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) {Q : CovariantRepresentation α H}
    (hQ : Q.comap hI.subtypeHom = P) :
    Q = P.idealExtension hmul := by
  refine (P.eq_idealExtension_iff hmul).2 ⟨hQ, fun a ξ hξ => ?_⟩
  rw [P.coefficient.orthogonal_essentialSubspace_eq_bot_of_isNondegenerate hP,
    Submodule.mem_bot] at hξ
  simp [hξ]

section Integration

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G]
  (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (μ : Measure G)

/-- Integrating `P.idealExtension hmul` against an included compactly supported function agrees
with integrating `P`. -/
@[simp]
theorem integratedOperator_idealExtension_convolutionMap
    [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]
    (f : ConvolutionAlgebra hI.restrict μ) :
    (P.idealExtension hmul).integratedOperator μ (hI.subtypeHom.convolutionMap μ f).ofConv =
      P.integratedOperator μ f.ofConv := by
  rw [← (P.idealExtension hmul).integratedOperator_comap hI.subtypeHom μ f,
    P.comap_idealExtension_subtypeHom hmul]

/-- Integrating `P.idealExtension hmul` on the twisted L¹ completion agrees with integrating `P`
along `hI.subtypeHom.convolutionMapL1 μ`. -/
@[simp]
theorem integratedOperatorL1_idealExtension_convolutionMapL1
    [BorelSpace G] [MeasurableMul G] [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (x : Completion (ConvolutionAlgebra hI.restrict μ)) :
    (P.idealExtension hmul).integratedOperatorL1 μ (hI.subtypeHom.convolutionMapL1 μ x) =
      P.integratedOperatorL1 μ x := by
  rw [← (P.idealExtension hmul).integratedOperatorL1_comap hI.subtypeHom μ x,
    P.comap_idealExtension_subtypeHom hmul]

/-- The integrated ⋆-homomorphism of `P.idealExtension hmul` extends that of `P` along
`hI.subtypeHom.convolutionMap μ`. -/
theorem integratedStarAlgHom_idealExtension_convolutionMap
    [BorelSpace G] [μ.IsHaarMeasure] (f : ConvolutionAlgebra hI.restrict μ) :
    (P.idealExtension hmul).integratedStarAlgHom μ (hI.subtypeHom.convolutionMap μ f) =
      P.integratedStarAlgHom μ f := by
  simp

end Integration

end IdealExtension

end TauCeti.CStarAction.CovariantRepresentation

namespace IsInvariant

open TauCeti CStarAction ConvolutionAlgebra

universe u v

variable {G : Type u} {A : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  {α : CStarAction G A} {I : NonUnitalStarSubalgebra ℂ A} [IsClosed (I : Set A)]
  (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
  (μ : Measure G) [μ.IsHaarMeasure]

/-- The equivariant inclusion of a closed invariant two-sided star ideal preserves the full
C⋆-seminorm identically on compactly supported functions. -/
theorem fullSeminorm_convolutionMap_subtypeHom (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I)
    (f : ConvolutionAlgebra hI.restrict μ) :
    fullSeminorm α μ (hI.subtypeHom.convolutionMap μ f) = fullSeminorm hI.restrict μ f := by
  refine le_antisymm (hI.subtypeHom.fullSeminorm_convolutionMap_le μ f) ?_
  refine (fullSeminorm_le_iff (apply_nonneg _ _)).2 fun H _ _ _ P => ?_
  rw [← P.integratedStarAlgHom_idealExtension_convolutionMap hmul μ f]
  exact norm_integratedStarAlgHom_le_fullSeminorm
    (P.idealExtension hmul) (hI.subtypeHom.convolutionMap μ f)

end IsInvariant

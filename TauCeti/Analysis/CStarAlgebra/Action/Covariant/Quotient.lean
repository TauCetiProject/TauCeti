/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Comap
public import TauCeti.Analysis.CStarAlgebra.Action.Ideal
public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate

/-!
# Quotient descent of covariant representations

A covariant representation `P` of a C⋆-dynamical system `(A, G, α)` whose coefficient
representation vanishes on the kernel of a surjective equivariant homomorphism `q : Hom α β`
descends uniquely to a covariant representation `P.descend q hq hker` of `β` on the same Hilbert
space, keeping the unitary group representation unchanged. Pullback along `q` recovers `P`,
preserves and reflects nondegeneracy of the coefficient representation (in fact, for any
dense-range equivariant homomorphism), and intertwines the integrated forms on both `C_c(G, A)`
and its twisted L¹ completion.

For a closed `α`-invariant two-sided ideal `I : TwoSidedIdeal A`, the same descent is bundled
directly on the concrete quotient action `α.quotient I hI` as `P.quotientLift I hI hker` using
`TwoSidedIdeal.Quotient.liftStarAlgHom`. No unitality, separability, or global σ-finiteness is
assumed, and the algebras and Hilbert space may lie in arbitrary universes.

## Main definitions and results

* `TauCeti.CStarAction.CovariantRepresentation.isNondegenerate_comap_coefficient_iff` and
  `TauCeti.CStarAction.CovariantRepresentation.comap_injective_of_denseRange`: pullback along a
  dense-range equivariant homomorphism preserves and reflects nondegeneracy and is injective.
* `TauCeti.CStarAction.CovariantRepresentation.descend`: descent of a covariant representation
  through a surjective equivariant homomorphism, with pullback recovery `comap_descend`,
  uniqueness `eq_descend_iff`, existence-and-uniqueness `existsUnique_comap_eq_iff`, and
  integration compatibility `integratedOperator_descend` and `integratedOperatorL1_descend`.
* `TauCeti.CStarAction.CovariantRepresentation.quotientLift`: concrete descent to the quotient
  action `α.quotient I hI` by a closed invariant two-sided ideal `I`.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Section 3.3 (Proposition 3.19).
-/

public section

noncomputable section

open MeasureTheory UniformSpace
open scoped CStarAlgebra

namespace TauCeti.CStarAction.CovariantRepresentation

section DenseRange

variable {G A B H : Type*} [Group G] [TopologicalSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} {β : CStarAction G B}

/-- Pulling back a covariant representation along a dense-range equivariant homomorphism preserves
and reflects nondegeneracy of the coefficient representation. -/
theorem isNondegenerate_comap_coefficient_iff (P : CovariantRepresentation β H)
    {φ : Hom α β} (hφ : DenseRange φ) :
    (P.comap φ).coefficient.IsNondegenerate ↔ P.coefficient.IsNondegenerate := by
  rw [comap_coefficient, NonUnitalStarAlgHom.isNondegenerate_iff_dense,
    P.coefficient.isNondegenerate_iff_dense_span_comp hφ]
  rfl

/-- Pullback of covariant representations along a dense-range equivariant homomorphism is
injective. -/
theorem comap_injective_of_denseRange {φ : Hom α β} (hφ : DenseRange φ) :
    Function.Injective (fun Q : CovariantRepresentation β H => Q.comap φ) := by
  intro Q₁ Q₂ hQ
  refine CovariantRepresentation.ext ?_ ?_
  · refine DFunLike.coe_injective <| hφ.equalizer
      (map_continuous Q₁.coefficient) (map_continuous Q₂.coefficient) <| funext fun a => ?_
    simpa only [Function.comp_apply, comap_coefficient, NonUnitalStarAlgHom.comp_apply,
      Hom.coe_toNonUnitalStarAlgHom] using congrArg (fun R => R.coefficient a) hQ
  · simpa only [comap_group] using congrArg CovariantRepresentation.group hQ

end DenseRange

section Descend

variable {G A B H : Type*} [Group G] [TopologicalSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} {β : CStarAction G B}
  (P : CovariantRepresentation α H) (q : Hom α β) (hq : Function.Surjective q)
  (hker : ∀ a, q a = 0 → P.coefficient a = 0)

/-- The descended coefficient representation along a surjective equivariant homomorphism whose
kernel is annihilated by `P.coefficient`. -/
private def descendCoefficient : B →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
  (TwoSidedIdeal.Quotient.liftStarAlgHom (TwoSidedIdeal.ker q.toNonUnitalStarAlgHom)
      P.coefficient fun a ha => hker a ((TwoSidedIdeal.mem_ker _).mp ha)).comp
    (NonUnitalStarAlgHom.quotientKerEquivOfSurjective
      (φ := q.toNonUnitalStarAlgHom) hq).symm.toNonUnitalStarAlgHom

private theorem descendCoefficient_apply (a : A) :
    descendCoefficient P q hq hker (q a) = P.coefficient a := by
  have hsymm :
      (NonUnitalStarAlgHom.quotientKerEquivOfSurjective (φ := q.toNonUnitalStarAlgHom) hq).symm
        (q a) = TwoSidedIdeal.Quotient.mk (TwoSidedIdeal.ker q.toNonUnitalStarAlgHom) a :=
    (NonUnitalStarAlgHom.quotientKerEquivOfSurjective
        (φ := q.toNonUnitalStarAlgHom) hq).symm_apply_eq.mpr
      (NonUnitalStarAlgHom.quotientKerEquivOfSurjective_mk (φ := q.toNonUnitalStarAlgHom) hq a).symm
  exact (congrArg
      (TwoSidedIdeal.Quotient.liftStarAlgHom (TwoSidedIdeal.ker q.toNonUnitalStarAlgHom)
        P.coefficient fun a ha => hker a ((TwoSidedIdeal.mem_ker _).mp ha)) hsymm).trans
    (TwoSidedIdeal.Quotient.liftStarAlgHom_mk _ _ _ a)

/-- Descend a covariant representation of `α` along a surjective equivariant homomorphism
`q : Hom α β` whose kernel is annihilated by `P.coefficient`, keeping the group representation
unchanged. -/
def descend : CovariantRepresentation β H where
  coefficient := descendCoefficient P q hq hker
  group := P.group
  isUnitary := P.isUnitary
  continuous_orbit := P.continuous_orbit
  covariance g b v := by
    obtain ⟨a, rfl⟩ := hq b
    rw [← q.map_action, descendCoefficient_apply, descendCoefficient_apply]
    exact P.covariance g a v

/-- On `q a`, the descended coefficient representation agrees with `P.coefficient a`. -/
@[simp]
theorem descend_coefficient_apply (a : A) :
    (P.descend q hq hker).coefficient (q a) = P.coefficient a :=
  descendCoefficient_apply P q hq hker a

/-- Composing the descended coefficient representation with `q` recovers `P.coefficient`. -/
@[simp]
theorem descend_coefficient_comp :
    (P.descend q hq hker).coefficient.comp q.toNonUnitalStarAlgHom = P.coefficient :=
  NonUnitalStarAlgHom.ext fun a => P.descend_coefficient_apply q hq hker a

/-- Descending along a surjective equivariant homomorphism does not change the group
representation. -/
@[simp]
theorem descend_group : (P.descend q hq hker).group = P.group :=
  (rfl)

/-- Pulling back the descended covariant representation along `q` recovers `P`. -/
@[simp]
theorem comap_descend : (P.descend q hq hker).comap q = P := by
  refine CovariantRepresentation.ext ?_ ?_
  · rw [comap_coefficient, descend_coefficient_comp]
  · rw [comap_group, descend_group]

/-- A covariant representation of `β` equals `P.descend q hq hker` precisely when its pullback
along `q` is `P`. -/
theorem eq_descend_iff {Q : CovariantRepresentation β H} :
    Q = P.descend q hq hker ↔ Q.comap q = P :=
  ⟨fun h => h ▸ P.comap_descend q hq hker,
    fun h => comap_injective_of_denseRange hq.denseRange (h.trans (P.comap_descend q hq hker).symm)⟩

/-- Uniqueness of the descended covariant representation. -/
theorem eq_descend_of_comap_eq {Q : CovariantRepresentation β H} (h : Q.comap q = P) :
    Q = P.descend q hq hker :=
  (P.eq_descend_iff q hq hker).2 h

/-- A covariant representation of `α` descends (uniquely) through a surjective equivariant
homomorphism `q` if and only if its coefficient representation vanishes on the kernel of `q`. -/
theorem existsUnique_comap_eq_iff (P : CovariantRepresentation α H) (q : Hom α β)
    (hq : Function.Surjective q) :
    (∃! Q : CovariantRepresentation β H, Q.comap q = P) ↔
      ∀ a, q a = 0 → P.coefficient a = 0 := by
  refine ⟨?_, fun hker => ⟨P.descend q hq hker, P.comap_descend q hq hker,
    fun _ hQ => P.eq_descend_of_comap_eq q hq hker hQ⟩⟩
  rintro ⟨Q, rfl, -⟩ a ha
  simp only [comap_coefficient, NonUnitalStarAlgHom.comp_apply, Hom.coe_toNonUnitalStarAlgHom, ha,
    map_zero]

/-- The descended coefficient representation is nondegenerate if and only if `P.coefficient` is
nondegenerate. -/
@[simp]
theorem isNondegenerate_descend_coefficient_iff :
    (P.descend q hq hker).coefficient.IsNondegenerate ↔ P.coefficient.IsNondegenerate := by
  rw [← (P.descend q hq hker).isNondegenerate_comap_coefficient_iff hq.denseRange,
    P.comap_descend q hq hker]

/-- Vector integration of the descended covariant representation on `q.convolutionMap μ f` agrees
with integration of `P` on `f`. -/
@[simp]
theorem integratedOperator_descend [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (f : ConvolutionAlgebra α μ) :
    (P.descend q hq hker).integratedOperator μ (q.convolutionMap μ f).ofConv =
      P.integratedOperator μ f.ofConv := by
  rw [← integratedOperator_comap, P.comap_descend q hq hker]

/-- On twisted L¹ completions, integration of the descended covariant representation commutes with
the induced map `q.convolutionMapL1 μ`. -/
@[simp]
theorem integratedOperatorL1_descend [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [BorelSpace G] [MeasurableMul G] [μ.IsMulLeftInvariant]
    (x : Completion (ConvolutionAlgebra α μ)) :
    (P.descend q hq hker).integratedOperatorL1 μ (q.convolutionMapL1 μ x) =
      P.integratedOperatorL1 μ x := by
  rw [← integratedOperatorL1_comap, P.comap_descend q hq hker]

end Descend

section Quotient

variable {G A H : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)
  (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
  (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
  (hker : ∀ a ∈ I, P.coefficient a = 0)

/-- Descend a covariant representation of `α` vanishing on a closed invariant two-sided ideal `I`
to the concrete quotient action `α.quotient I hI`. -/
def quotientLift : CovariantRepresentation (α.quotient I hI) H where
  coefficient := TwoSidedIdeal.Quotient.liftStarAlgHom I P.coefficient hker
  group := P.group
  isUnitary := P.isUnitary
  continuous_orbit := P.continuous_orbit
  covariance g x v := by
    obtain ⟨a, rfl⟩ := TwoSidedIdeal.Quotient.mk_surjective I x
    rw [α.quotient_mk I hI g a, TwoSidedIdeal.Quotient.liftStarAlgHom_mk,
      TwoSidedIdeal.Quotient.liftStarAlgHom_mk]
    exact P.covariance g a v

/-- The coefficient representation of `P.quotientLift I hI hker` is
`TwoSidedIdeal.Quotient.liftStarAlgHom I P.coefficient hker`. -/
@[simp]
theorem quotientLift_coefficient :
    (P.quotientLift I hI hker).coefficient =
      TwoSidedIdeal.Quotient.liftStarAlgHom I P.coefficient hker :=
  (rfl)

/-- On quotient classes, the lifted coefficient representation agrees with `P.coefficient`. -/
theorem quotientLift_coefficient_mk (a : A) :
    (P.quotientLift I hI hker).coefficient (TwoSidedIdeal.Quotient.mk I a) = P.coefficient a :=
  TwoSidedIdeal.Quotient.liftStarAlgHom_mk I P.coefficient hker a

/-- Lifting to a quotient action does not change the group representation. -/
@[simp]
theorem quotientLift_group : (P.quotientLift I hI hker).group = P.group :=
  (rfl)

/-- Pulling back `P.quotientLift I hI hker` along the canonical quotient homomorphism recovers
`P`. -/
@[simp]
theorem comap_quotientLift :
    (P.quotientLift I hI hker).comap (α.quotientMkHom I hI) = P := by
  refine CovariantRepresentation.ext (NonUnitalStarAlgHom.ext fun a => ?_) ?_
  · simpa only [comap_coefficient, NonUnitalStarAlgHom.comp_apply, Hom.coe_toNonUnitalStarAlgHom,
      CStarAction.quotientMkHom_apply] using P.quotientLift_coefficient_mk I hI hker a
  · rw [comap_group, quotientLift_group]

/-- The concrete quotient lift agrees with `CovariantRepresentation.descend` along
`α.quotientMkHom I hI`. -/
theorem quotientLift_eq_descend :
    P.quotientLift I hI hker =
      P.descend (α.quotientMkHom I hI) (α.quotientMkHom_surjective I hI)
        (fun a ha => hker a (TwoSidedIdeal.Quotient.eq_zero_iff_mem.mp
          (by simpa only [CStarAction.quotientMkHom_apply] using ha))) :=
  P.eq_descend_of_comap_eq _ _ _ (P.comap_quotientLift I hI hker)

/-- A covariant representation of `α.quotient I hI` equals `P.quotientLift I hI hker` precisely
when its pullback along `α.quotientMkHom I hI` is `P`. -/
theorem eq_quotientLift_iff {Q : CovariantRepresentation (α.quotient I hI) H} :
    Q = P.quotientLift I hI hker ↔ Q.comap (α.quotientMkHom I hI) = P :=
  ⟨fun h => h ▸ P.comap_quotientLift I hI hker,
    fun h => comap_injective_of_denseRange (α.quotientMkHom_surjective I hI).denseRange
      (h.trans (P.comap_quotientLift I hI hker).symm)⟩

/-- The quotient-lifted coefficient representation is nondegenerate if and only if `P.coefficient`
is nondegenerate. -/
theorem isNondegenerate_quotientLift_coefficient_iff :
    (P.quotientLift I hI hker).coefficient.IsNondegenerate ↔ P.coefficient.IsNondegenerate := by
  rw [P.quotientLift_eq_descend I hI hker, isNondegenerate_descend_coefficient_iff]

/-- Vector integration of `P.quotientLift I hI hker` agrees with integration of `P` along
`α.quotientMkHom I hI`. -/
@[simp]
theorem integratedOperator_quotientLift [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (f : ConvolutionAlgebra α μ) :
    (P.quotientLift I hI hker).integratedOperator μ
        ((α.quotientMkHom I hI).convolutionMap μ f).ofConv =
      P.integratedOperator μ f.ofConv := by
  rw [← integratedOperator_comap, P.comap_quotientLift I hI hker]

/-- On twisted L¹ completions, integration of `P.quotientLift I hI hker` commutes with the
canonical quotient map. -/
@[simp]
theorem integratedOperatorL1_quotientLift [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [BorelSpace G] [MeasurableMul G] [μ.IsMulLeftInvariant]
    (x : Completion (ConvolutionAlgebra α μ)) :
    (P.quotientLift I hI hker).integratedOperatorL1 μ
        ((α.quotientMkHom I hI).convolutionMapL1 μ x) =
      P.integratedOperatorL1 μ x := by
  rw [← integratedOperatorL1_comap, P.comap_quotientLift I hI hker]

end Quotient

end TauCeti.CStarAction.CovariantRepresentation

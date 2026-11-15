/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Comap
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Nondegenerate
public import TauCeti.Analysis.CStarAlgebra.Action.Ideal

/-!
# Descent of covariant representations to quotient actions

Let `q : Hom α β` be a surjective equivariant `⋆`-homomorphism between C⋆-dynamical systems.
Pulling back covariant representations along `q` via `CovariantRepresentation.comap` is injective,
preserves and reflects nondegeneracy of the coefficient representation, and has range consisting
precisely of those covariant pairs `P : CovariantRepresentation α H` whose coefficient
representation vanishes on `ker q`.

Conversely, any covariant representation `P : CovariantRepresentation α H` with
`∀ a, q a = 0 → P.coefficient a = 0` descends uniquely to `P.descend q hq hP :
CovariantRepresentation β H` with the same group representation and with
`(P.descend q hq hP).coefficient (q a) = P.coefficient a`. Specializing `q` to the canonical
quotient projection `α.quotientMkHom I hI` onto `A ⧸ I` for a closed `α`-invariant two-sided ideal
`I` yields `CovariantRepresentation.quotientLift`.

These results provide the quotient-side counterpart to
`TauCeti.Analysis.CStarAlgebra.Action.Covariant.Ideal` and supply the covariant-representation
half of the invariant-ideal exact sequence of full crossed products. No unitality, separability,
or global σ-finiteness is assumed.

## Main definitions and results

* `TauCeti.CStarAction.CovariantRepresentation.comap_injective_of_denseRange` and
  `TauCeti.CStarAction.CovariantRepresentation.comap_injective`: injectivity of `comap` along
  dense-range or surjective equivariant maps.
* `TauCeti.CStarAction.CovariantRepresentation.isNondegenerate_comap_coefficient_iff`: `comap`
  along a dense-range equivariant map preserves and reflects coefficient nondegeneracy.
* `TauCeti.CStarAction.CovariantRepresentation.descend`: descent of a covariant representation along
  a surjective equivariant map annihilated by its coefficient representation, with inverse laws
  `comap_descend`, `descend_comap`, and range characterization `mem_range_comap_iff`.
* `TauCeti.CStarAction.CovariantRepresentation.quotientLift`: specialization of `descend` to the
  concrete C⋆-quotient `A ⧸ I` by a closed invariant two-sided ideal `I`.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Section 2.4 and Proposition 3.19.
-/

public section

noncomputable section

open MeasureTheory UniformSpace
open scoped CStarAlgebra

namespace TauCeti.CStarAction.CovariantRepresentation

section General

variable {G A B H : Type*} [Group G] [TopologicalSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} {β : CStarAction G B}

/-- Pulling back covariant representations along a dense-range equivariant homomorphism is
injective. -/
theorem comap_injective_of_denseRange {φ : Hom α β} (hφ : DenseRange φ) :
    Function.Injective fun Q : CovariantRepresentation β H => Q.comap φ := by
  intro Q₁ Q₂ h
  have hcoeff : ⇑Q₁.coefficient = ⇑Q₂.coefficient :=
    hφ.equalizer (map_continuous Q₁.coefficient) (map_continuous Q₂.coefficient) <|
      funext fun a => by simpa using DFunLike.congr_fun (congrArg coefficient h) a
  have hgroup : Q₁.group = Q₂.group := by
    simpa using congrArg group h
  exact ext (DFunLike.coe_injective hcoeff) hgroup

/-- Pulling back covariant representations along a surjective equivariant homomorphism is
injective. -/
theorem comap_injective {q : Hom α β} (hq : Function.Surjective q) :
    Function.Injective fun Q : CovariantRepresentation β H => Q.comap q :=
  comap_injective_of_denseRange hq.denseRange

/-- Pulling back a covariant representation along a dense-range equivariant homomorphism preserves
and reflects nondegeneracy of the coefficient representation. -/
theorem isNondegenerate_comap_coefficient_iff (Q : CovariantRepresentation β H) {φ : Hom α β}
    (hφ : DenseRange φ) :
    (Q.comap φ).coefficient.IsNondegenerate ↔ Q.coefficient.IsNondegenerate := by
  rw [comap_coefficient]
  exact Q.coefficient.isNondegenerate_comp_iff hφ

/-- Descend a covariant representation `P` of `α` along a surjective equivariant homomorphism
`q : Hom α β` when `P.coefficient` vanishes on `ker q`. -/
def descend (P : CovariantRepresentation α H) (q : Hom α β) (hq : Function.Surjective q)
    (hP : ∀ a, q a = 0 → P.coefficient a = 0) : CovariantRepresentation β H :=
  let hker : TwoSidedIdeal.ker q.toNonUnitalStarAlgHom ≤ TwoSidedIdeal.ker P.coefficient :=
    fun a ha => (TwoSidedIdeal.mem_ker P.coefficient).2
      (hP a ((TwoSidedIdeal.mem_ker q.toNonUnitalStarAlgHom).1 ha))
  let coef := q.toNonUnitalStarAlgHom.liftOfSurjective hq P.coefficient hker
  { coefficient := coef
    group := P.group
    isUnitary := P.isUnitary
    continuous_orbit := P.continuous_orbit
    covariance g b v := by
      obtain ⟨a, rfl⟩ := hq b
      have h1 : coef (q a) = P.coefficient a :=
        q.toNonUnitalStarAlgHom.liftOfSurjective_apply hq P.coefficient hker a
      have h2 : coef (β g (q a)) = P.coefficient (α g a) := by
        rw [← q.map_action]
        exact q.toNonUnitalStarAlgHom.liftOfSurjective_apply hq P.coefficient hker (α g a)
      rw [h1, h2, P.covariance] }

@[simp]
theorem descend_coefficient_apply (P : CovariantRepresentation α H) (q : Hom α β)
    (hq : Function.Surjective q) (hP : ∀ a, q a = 0 → P.coefficient a = 0) (a : A) :
    (P.descend q hq hP).coefficient (q a) = P.coefficient a :=
  q.toNonUnitalStarAlgHom.liftOfSurjective_apply hq P.coefficient _ a

@[simp]
theorem descend_coefficient_comp (P : CovariantRepresentation α H) (q : Hom α β)
    (hq : Function.Surjective q) (hP : ∀ a, q a = 0 → P.coefficient a = 0) :
    (P.descend q hq hP).coefficient.comp q.toNonUnitalStarAlgHom = P.coefficient :=
  q.toNonUnitalStarAlgHom.liftOfSurjective_comp hq P.coefficient _

@[simp]
theorem descend_group (P : CovariantRepresentation α H) (q : Hom α β)
    (hq : Function.Surjective q) (hP : ∀ a, q a = 0 → P.coefficient a = 0) :
    (P.descend q hq hP).group = P.group :=
  (rfl)

@[simp]
theorem comap_descend (P : CovariantRepresentation α H) (q : Hom α β)
    (hq : Function.Surjective q) (hP : ∀ a, q a = 0 → P.coefficient a = 0) :
    (P.descend q hq hP).comap q = P := by
  apply ext
  · rw [comap_coefficient, descend_coefficient_comp]
  · rw [comap_group, descend_group]

@[simp]
theorem descend_comap (Q : CovariantRepresentation β H) (q : Hom α β) (hq : Function.Surjective q)
    (hQ : ∀ a, q a = 0 → (Q.comap q).coefficient a = 0 := fun a ha => by simp [ha]) :
    (Q.comap q).descend q hq hQ = Q :=
  comap_injective hq ((Q.comap q).comap_descend q hq hQ)

/-- A covariant representation `Q` of `β` equals `P.descend q hq hP` if and only if its pullback
along `q` is `P`. -/
theorem eq_descend_iff {P : CovariantRepresentation α H} {q : Hom α β} (hq : Function.Surjective q)
    (hP : ∀ a, q a = 0 → P.coefficient a = 0) {Q : CovariantRepresentation β H} :
    Q = P.descend q hq hP ↔ Q.comap q = P :=
  ⟨fun h => h ▸ P.comap_descend q hq hP,
   fun h => comap_injective hq (h.trans (P.comap_descend q hq hP).symm)⟩

/-- A covariant representation `P` of `α` lies in the range of `comap · q` along a surjective
equivariant homomorphism `q` if and only if `P.coefficient` vanishes on `ker q`. -/
theorem mem_range_comap_iff {q : Hom α β} (hq : Function.Surjective q)
    {P : CovariantRepresentation α H} :
    P ∈ Set.range (fun Q : CovariantRepresentation β H => Q.comap q) ↔
      ∀ a, q a = 0 → P.coefficient a = 0 := by
  refine ⟨?_, fun hP => ⟨P.descend q hq hP, P.comap_descend q hq hP⟩⟩
  rintro ⟨Q, rfl⟩ a ha
  simp [ha]

@[simp]
theorem isNondegenerate_descend_coefficient_iff (P : CovariantRepresentation α H) (q : Hom α β)
    (hq : Function.Surjective q) (hP : ∀ a, q a = 0 → P.coefficient a = 0) :
    (P.descend q hq hP).coefficient.IsNondegenerate ↔ P.coefficient.IsNondegenerate := by
  rw [← isNondegenerate_comap_coefficient_iff _ hq.denseRange, comap_descend]

end General

section Integrated

variable {G A B H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} {β : CStarAction G B}

/-- Integrating a descended covariant representation on `q.convolutionMap μ f` recovers the
integrated operator of `P` on `f`. -/
@[simp]
theorem integratedOperator_descend_convolutionMap (P : CovariantRepresentation α H) (q : Hom α β)
    (hq : Function.Surjective q) (hP : ∀ a, q a = 0 → P.coefficient a = 0)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (f : ConvolutionAlgebra α μ) :
    (P.descend q hq hP).integratedOperator μ (q.convolutionMap μ f).ofConv =
      P.integratedOperator μ f.ofConv := by
  rw [← (P.descend q hq hP).integratedOperator_comap q μ f, comap_descend]

/-- Integrating a descended covariant representation on `q.convolutionMapL1 μ x` recovers the
`L¹`-integrated operator of `P` on `x`. -/
@[simp]
theorem integratedOperatorL1_descend_convolutionMapL1 [BorelSpace G] [MeasurableMul G]
    (P : CovariantRepresentation α H) (q : Hom α β) (hq : Function.Surjective q)
    (hP : ∀ a, q a = 0 → P.coefficient a = 0)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (x : Completion (ConvolutionAlgebra α μ)) :
    (P.descend q hq hP).integratedOperatorL1 μ (q.convolutionMapL1 μ x) =
      P.integratedOperatorL1 μ x := by
  rw [← (P.descend q hq hP).integratedOperatorL1_comap q μ x, comap_descend]

end Integrated

section QuotientIdeal

variable {G A H : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A}

/-- Descend a covariant representation `P` of `α` vanishing on a closed invariant two-sided ideal
`I` to a covariant representation of the quotient action `α.quotient I hI` on `A ⧸ I`. -/
def quotientLift (P : CovariantRepresentation α H) (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (hP : ∀ a ∈ I, P.coefficient a = 0) :
    CovariantRepresentation (α.quotient I hI) H :=
  P.descend (α.quotientMkHom I hI) (α.quotientMkHom_surjective I hI) fun a ha =>
    hP a (TwoSidedIdeal.Quotient.eq_zero_iff_mem.mp ((α.quotientMkHom_apply I hI a).symm.trans ha))

@[simp]
theorem quotientLift_coefficient_mk (P : CovariantRepresentation α H) (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (hP : ∀ a ∈ I, P.coefficient a = 0) (a : A) :
    (P.quotientLift I hI hP).coefficient (TwoSidedIdeal.Quotient.mk I a) = P.coefficient a := by
  simpa only [quotientLift, CStarAction.quotientMkHom_apply] using
    P.descend_coefficient_apply (α.quotientMkHom I hI) (α.quotientMkHom_surjective I hI) _ a

@[simp]
theorem quotientLift_coefficient_comp_mkStarAlgHom (P : CovariantRepresentation α H)
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (hP : ∀ a ∈ I, P.coefficient a = 0) :
    (P.quotientLift I hI hP).coefficient.comp (TwoSidedIdeal.Quotient.mkStarAlgHom I) =
      P.coefficient := by
  rw [quotientLift, ← CStarAction.quotientMkHom_toNonUnitalStarAlgHom α I hI]
  exact P.descend_coefficient_comp (α.quotientMkHom I hI) (α.quotientMkHom_surjective I hI) _

@[simp]
theorem quotientLift_group (P : CovariantRepresentation α H) (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (hP : ∀ a ∈ I, P.coefficient a = 0) :
    (P.quotientLift I hI hP).group = P.group :=
  (rfl)

@[simp]
theorem comap_quotientLift (P : CovariantRepresentation α H) (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (hP : ∀ a ∈ I, P.coefficient a = 0) :
    (P.quotientLift I hI hP).comap (α.quotientMkHom I hI) = P :=
  P.comap_descend (α.quotientMkHom I hI) (α.quotientMkHom_surjective I hI) _

@[simp]
theorem quotientLift_comap (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (Q : CovariantRepresentation (α.quotient I hI) H)
    (hQ : ∀ a ∈ I, (Q.comap (α.quotientMkHom I hI)).coefficient a = 0 := fun a ha => by
      simp [TwoSidedIdeal.Quotient.eq_zero_iff_mem.mpr ha]) :
    (Q.comap (α.quotientMkHom I hI)).quotientLift I hI hQ = Q :=
  Q.descend_comap (α.quotientMkHom I hI) (α.quotientMkHom_surjective I hI) _

/-- A covariant representation `Q` of `α.quotient I hI` equals `P.quotientLift I hI hP` if and only
if its pullback along `α.quotientMkHom I hI` is `P`. -/
theorem eq_quotientLift_iff {P : CovariantRepresentation α H} (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (hP : ∀ a ∈ I, P.coefficient a = 0) {Q : CovariantRepresentation (α.quotient I hI) H} :
    Q = P.quotientLift I hI hP ↔ Q.comap (α.quotientMkHom I hI) = P :=
  eq_descend_iff (α.quotientMkHom_surjective I hI) _

/-- A covariant representation of `α` pulls back from the quotient action `α.quotient I hI` if and
only if its coefficient representation vanishes on `I`. -/
theorem mem_range_comap_quotientMkHom_iff (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    {P : CovariantRepresentation α H} :
    P ∈ Set.range (fun Q : CovariantRepresentation (α.quotient I hI) H =>
        Q.comap (α.quotientMkHom I hI)) ↔
      ∀ a ∈ I, P.coefficient a = 0 := by
  rw [mem_range_comap_iff (α.quotientMkHom_surjective I hI)]
  simp only [CStarAction.quotientMkHom_apply, TwoSidedIdeal.Quotient.eq_zero_iff_mem]

@[simp]
theorem isNondegenerate_quotientLift_coefficient_iff (P : CovariantRepresentation α H)
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (hP : ∀ a ∈ I, P.coefficient a = 0) :
    (P.quotientLift I hI hP).coefficient.IsNondegenerate ↔ P.coefficient.IsNondegenerate :=
  P.isNondegenerate_descend_coefficient_iff (α.quotientMkHom I hI)
    (α.quotientMkHom_surjective I hI) _

end QuotientIdeal

end TauCeti.CStarAction.CovariantRepresentation

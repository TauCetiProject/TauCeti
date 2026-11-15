/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.GroupLike
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.Map

/-!
# Evaluation of the group-like monoid algebra

Every bialgebra `H` over a commutative semiring `R` receives a canonical bialgebra morphism from
the monoid algebra on its group-like elements, Mathlib's `MonoidAlgebra.liftGroupLikeBialgHom`. It
sends each standard basis element to its underlying group-like element. Its linear range is exactly
the span of the group-like elements, and its subcoalgebra image is the subcoalgebra spanned by all
group-like elements. The morphism is injective exactly when the underlying group-like elements are
linearly independent, and it is a bialgebra equivalence when they are also spanning. Over a
commutative domain `R`, linear independence is automatic when `H` is torsion-free as an
`R`-module.

## Main declarations

* `MonoidAlgebra.liftGroupLikeBialgHom_single`: evaluation of Mathlib's
  `MonoidAlgebra.liftGroupLikeBialgHom : R[GroupLike R H] →ₐc[R] H` on a standard basis element.
* `TauCeti.GroupLike.range_liftGroupLikeBialgHom`: its linear range is the span of the group-like
  elements.
* `TauCeti.GroupLike.map_top_liftGroupLikeBialgHom`: its subcoalgebra image is the subcoalgebra
  spanned by all group-like elements.
* `TauCeti.GroupLike.liftGroupLikeBialgHom_injective_iff_linearIndependent`: injectivity is
  equivalent to linear independence of the group-like elements.
* `TauCeti.GroupLike.evaluationBialgEquivOfLinearIndependentOfSpanEqTop`: the equivalence obtained
  from linear independence and spanning.
* `TauCeti.GroupLike.liftGroupLikeBialgHom_injective`: injectivity over a domain when `H` is
  torsion-free as a module.
* `TauCeti.GroupLike.evaluationBialgEquiv`: the specialized equivalence over a domain when the
  group-like elements span `H` and `H` is torsion-free as a module.

## References

The automatic linear independence used in the domain and torsion-free specialization is the
domain-valued form of Milne, *Algebraic Groups*, Proposition 4.23. The reconstruction in the
spanning case is the bialgebra form underlying Definition 12.7 and Theorem 12.8 of the same
reference.
-/

public section

namespace TauCeti

universe u v

namespace GroupLike

variable (R : Type u) (H : Type v)

section Semiring

variable [CommSemiring R] [Semiring H] [Bialgebra R H]

/-- The algebra homomorphism underlying evaluation is the defining monoid-algebra lift. -/
private theorem liftGroupLikeBialgHom_toAlgHom :
    (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H) :
      MonoidAlgebra R (_root_.GroupLike R H) →ₐ[R] H) =
      MonoidAlgebra.lift R H (_root_.GroupLike R H)
        (_root_.GroupLike.valMonoidHom R H) :=
  rfl

/-- Evaluation on a scalar multiple of a standard basis element. -/
theorem _root_.MonoidAlgebra.liftGroupLikeBialgHom_single (g : _root_.GroupLike R H) (r : R) :
    MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H) (MonoidAlgebra.single g r) =
      r • (g : H) := by
  calc
    MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H) (MonoidAlgebra.single g r) =
        (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H) :
          MonoidAlgebra R (_root_.GroupLike R H) →ₐ[R] H)
            (MonoidAlgebra.single g r) := by
      simp only [BialgHom.coe_toAlgHom]
    _ = MonoidAlgebra.lift R H (_root_.GroupLike R H)
          (_root_.GroupLike.valMonoidHom R H) (MonoidAlgebra.single g r) := by
      rw [liftGroupLikeBialgHom_toAlgHom]
    _ = r • (g : H) := by
      rw [MonoidAlgebra.lift_single, _root_.GroupLike.valMonoidHom_apply]

/-- Evaluation of a monoid-algebra element is the finite linear combination of its group-like
indices with its coefficients. -/
theorem liftGroupLikeBialgHom_apply_eq_sum (x : MonoidAlgebra R (_root_.GroupLike R H)) :
    MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H) x =
      x.coeff.sum fun g r => r • (g : H) := by
  calc
    MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H) x =
        (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H) :
          MonoidAlgebra R (_root_.GroupLike R H) →ₐ[R] H) x := by
      simp only [BialgHom.coe_toAlgHom]
    _ = MonoidAlgebra.lift R H (_root_.GroupLike R H)
          (_root_.GroupLike.valMonoidHom R H) x := by
      rw [liftGroupLikeBialgHom_toAlgHom]
    _ = x.coeff.sum fun g r => r • (g : H) := by
      rw [MonoidAlgebra.lift_apply]
      simp only [_root_.GroupLike.valMonoidHom_apply]

/-- Evaluation is finite linear combination of the underlying group-like elements after passing
to the coefficient representation of the monoid algebra. -/
theorem liftGroupLikeBialgHom_toLinearMap :
    (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H) :
      MonoidAlgebra R (_root_.GroupLike R H) →ₗ[R] H) =
      (Finsupp.linearCombination R
          (_root_.GroupLike.val (R := R) (A := H))).comp
        (MonoidAlgebra.coeffLinearEquiv R).toLinearMap := by
  calc
    (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H) :
        MonoidAlgebra R (_root_.GroupLike R H) →ₗ[R] H) =
        ((MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H) :
          MonoidAlgebra R (_root_.GroupLike R H) →ₐ[R] H) :
            MonoidAlgebra R (_root_.GroupLike R H) →ₗ[R] H) :=
      (BialgHom.toAlgHom_toLinearMap (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H))).symm
    _ = (MonoidAlgebra.lift R H (_root_.GroupLike R H)
          (_root_.GroupLike.valMonoidHom R H)).toLinearMap :=
      congrArg (fun f : MonoidAlgebra R (_root_.GroupLike R H) →ₐ[R] H =>
        f.toLinearMap) (liftGroupLikeBialgHom_toAlgHom R H)
    _ = (Finsupp.linearCombination R
          (_root_.GroupLike.val (R := R) (A := H))).comp
        (MonoidAlgebra.coeffLinearEquiv R).toLinearMap := by
      apply LinearMap.ext
      intro x
      rw [AlgHom.toLinearMap_apply, MonoidAlgebra.lift_apply,
        LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        MonoidAlgebra.coeffLinearEquiv_apply, Finsupp.linearCombination_apply]
      simp only [_root_.GroupLike.valMonoidHom_apply]

/-- The linear range of evaluation is the span of the underlying group-like elements. -/
theorem range_liftGroupLikeBialgHom :
    LinearMap.range
        (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H) :
          MonoidAlgebra R (_root_.GroupLike R H) →ₗ[R] H) =
      Submodule.span R
        (Set.range (_root_.GroupLike.val (R := R) (A := H))) := by
  rw [liftGroupLikeBialgHom_toLinearMap]
  calc
    LinearMap.range
        ((Finsupp.linearCombination R
          (_root_.GroupLike.val (R := R) (A := H))).comp
            (MonoidAlgebra.coeffLinearEquiv R).toLinearMap) =
        LinearMap.range (Finsupp.linearCombination R
          (_root_.GroupLike.val (R := R) (A := H))) :=
      LinearMap.range_comp_of_range_eq_top _
        (LinearEquiv.range (MonoidAlgebra.coeffLinearEquiv R))
    _ = Submodule.span R
        (Set.range (_root_.GroupLike.val (R := R) (A := H))) :=
      Finsupp.range_linearCombination (R := R)
        (v := _root_.GroupLike.val (R := R) (A := H))

/-- The linear range of evaluation is the underlying submodule of the subcoalgebra spanned by all
group-like elements. -/
theorem range_liftGroupLikeBialgHom_eq_groupLikeSetSpan_toSubmodule :
    LinearMap.range
        (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H) :
          MonoidAlgebra R (_root_.GroupLike R H) →ₗ[R] H) =
      (Subcoalgebra.groupLikeSetSpan (R := R) (C := H) Set.univ).toSubmodule := by
  rw [range_liftGroupLikeBialgHom, Subcoalgebra.groupLikeSetSpan_toSubmodule]
  congr 1
  simp only [Set.image_univ]

/-- The image of the full source subcoalgebra under evaluation is the subcoalgebra spanned by all
group-like elements. -/
theorem map_top_liftGroupLikeBialgHom :
    (Subcoalgebra.map
        (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H) :
          MonoidAlgebra R (_root_.GroupLike R H) →ₗc[R] H)
        (⊤ : Subcoalgebra R (MonoidAlgebra R (_root_.GroupLike R H)))) =
      Subcoalgebra.groupLikeSetSpan (R := R) (C := H) Set.univ := by
  apply Subcoalgebra.ext
  intro h
  have hmap :
      (Subcoalgebra.map
        (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H) :
          MonoidAlgebra R (_root_.GroupLike R H) →ₗc[R] H)
        (⊤ : Subcoalgebra R (MonoidAlgebra R (_root_.GroupLike R H)))).toSubmodule =
        LinearMap.range
          (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H) :
            MonoidAlgebra R (_root_.GroupLike R H) →ₗ[R] H) :=
    Subcoalgebra.map_top_toSubmodule _
  calc
    h ∈ Subcoalgebra.map
        (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H) :
          MonoidAlgebra R (_root_.GroupLike R H) →ₗc[R] H)
        (⊤ : Subcoalgebra R (MonoidAlgebra R (_root_.GroupLike R H))) ↔
        h ∈ (Subcoalgebra.map
          (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H) :
            MonoidAlgebra R (_root_.GroupLike R H) →ₗc[R] H)
          (⊤ : Subcoalgebra R
            (MonoidAlgebra R (_root_.GroupLike R H)))).toSubmodule :=
      Subcoalgebra.mem_toSubmodule.symm
    _ ↔ h ∈ LinearMap.range
        (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H) :
          MonoidAlgebra R (_root_.GroupLike R H) →ₗ[R] H) := by
      rw [hmap]
    _ ↔ h ∈
        (Subcoalgebra.groupLikeSetSpan (R := R) (C := H) Set.univ).toSubmodule := by
      rw [range_liftGroupLikeBialgHom_eq_groupLikeSetSpan_toSubmodule]
    _ ↔ h ∈ Subcoalgebra.groupLikeSetSpan (R := R) (C := H) Set.univ :=
      Subcoalgebra.mem_toSubmodule

/-- Evaluation is surjective exactly when the group-like elements span the whole bialgebra. -/
theorem liftGroupLikeBialgHom_surjective_iff_span_eq_top :
    Function.Surjective (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H)) ↔
      Submodule.span R
          (Set.range (_root_.GroupLike.val (R := R) (A := H))) = ⊤ := by
  constructor
  · intro h
    rw [← range_liftGroupLikeBialgHom R H]
    apply LinearMap.range_eq_top.2
    simpa only [BialgHom.coe_toLinearMap] using h
  · intro h
    have hsurjective : Function.Surjective
        (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H) :
          MonoidAlgebra R (_root_.GroupLike R H) →ₗ[R] H) := by
      apply LinearMap.range_eq_top.1
      rw [range_liftGroupLikeBialgHom R H]
      exact h
    simpa only [BialgHom.coe_toLinearMap] using hsurjective

/-- Evaluation is surjective exactly when the subcoalgebra spanned by all group-like elements is
the full subcoalgebra. -/
theorem liftGroupLikeBialgHom_surjective_iff_groupLikeSetSpan_eq_top :
    Function.Surjective (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H)) ↔
      Subcoalgebra.groupLikeSetSpan (R := R) (C := H) Set.univ = ⊤ := by
  rw [Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top,
    liftGroupLikeBialgHom_surjective_iff_span_eq_top]

/-- Evaluation is injective exactly when the underlying group-like elements are linearly
independent. -/
theorem liftGroupLikeBialgHom_injective_iff_linearIndependent :
    Function.Injective (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H)) ↔
      LinearIndependent R (_root_.GroupLike.val (R := R) (A := H)) := by
  rw [linearIndependent_iff_injective_finsuppLinearCombination]
  have hevaluation :
      (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H) :
        MonoidAlgebra R (_root_.GroupLike R H) → H) =
        (Finsupp.linearCombination R
          (_root_.GroupLike.val (R := R) (A := H))) ∘
          (MonoidAlgebra.coeffLinearEquiv R) := by
    simpa only [BialgHom.coe_toLinearMap, LinearMap.coe_comp,
      LinearEquiv.coe_toLinearMap] using
      congrArg
        (fun f : MonoidAlgebra R (_root_.GroupLike R H) →ₗ[R] H =>
          (f : MonoidAlgebra R (_root_.GroupLike R H) → H))
        (liftGroupLikeBialgHom_toLinearMap R H)
  rw [hevaluation]
  exact Function.Injective.of_comp_iff'
    (Finsupp.linearCombination R
      (_root_.GroupLike.val (R := R) (A := H)))
    (MonoidAlgebra.coeffLinearEquiv R).bijective

/-- If the underlying group-like elements are linearly independent and span the bialgebra,
evaluation is a bialgebra equivalence. -/
noncomputable def evaluationBialgEquivOfLinearIndependentOfSpanEqTop
    (hlinear : LinearIndependent R
      (_root_.GroupLike.val (R := R) (A := H)))
    (hspan : Submodule.span R
      (Set.range (_root_.GroupLike.val (R := R) (A := H))) = ⊤) :
    MonoidAlgebra R (_root_.GroupLike R H) ≃ₐc[R] H :=
  BialgEquiv.ofBijective (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H))
    ⟨(liftGroupLikeBialgHom_injective_iff_linearIndependent R H).2 hlinear,
      (liftGroupLikeBialgHom_surjective_iff_span_eq_top R H).2 hspan⟩

/-- The general bialgebra equivalence obtained from linear independence and spanning applies as
evaluation. -/
@[simp]
theorem evaluationBialgEquivOfLinearIndependentOfSpanEqTop_apply
    (hlinear : LinearIndependent R
      (_root_.GroupLike.val (R := R) (A := H)))
    (hspan : Submodule.span R
      (Set.range (_root_.GroupLike.val (R := R) (A := H))) = ⊤)
    (x : MonoidAlgebra R (_root_.GroupLike R H)) :
    evaluationBialgEquivOfLinearIndependentOfSpanEqTop R H hlinear hspan x =
      MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H) x := by
  rw [evaluationBialgEquivOfLinearIndependentOfSpanEqTop]
  exact congrFun
    (BialgEquiv.coe_ofBijective (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H)) _) x

/-- The bialgebra morphism underlying the general equivalence from linear independence and
spanning is evaluation. -/
@[simp]
theorem evaluationBialgEquivOfLinearIndependentOfSpanEqTop_toBialgHom
    (hlinear : LinearIndependent R
      (_root_.GroupLike.val (R := R) (A := H)))
    (hspan : Submodule.span R
      (Set.range (_root_.GroupLike.val (R := R) (A := H))) = ⊤) :
    (evaluationBialgEquivOfLinearIndependentOfSpanEqTop R H hlinear hspan :
      MonoidAlgebra R (_root_.GroupLike R H) →ₐc[R] H) =
        MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H) := by
  apply BialgHom.ext
  exact evaluationBialgEquivOfLinearIndependentOfSpanEqTop_apply R H hlinear hspan

end Semiring

section Domain

variable [CommRing R] [IsDomain R] [Ring H] [Bialgebra R H]
variable [Module.IsTorsionFree R H]

/-- Over a commutative domain `R`, evaluation is injective when `H` is torsion-free as an
`R`-module. -/
theorem liftGroupLikeBialgHom_injective :
    Function.Injective (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H)) :=
  (liftGroupLikeBialgHom_injective_iff_linearIndependent R H).2
    (linearIndep_groupLikeVal (R := R) (A := H))

/-- If the group-like elements span a bialgebra `H` over a commutative domain `R`, and `H` is
torsion-free as an `R`-module, evaluation is a bialgebra equivalence. -/
noncomputable def evaluationBialgEquiv
    (hspan : Submodule.span R
      (Set.range (_root_.GroupLike.val (R := R) (A := H))) = ⊤) :
    MonoidAlgebra R (_root_.GroupLike R H) ≃ₐc[R] H :=
  evaluationBialgEquivOfLinearIndependentOfSpanEqTop R H
    (linearIndep_groupLikeVal (R := R) (A := H)) hspan

/-- The bialgebra equivalence obtained from spanning applies as evaluation. -/
@[simp]
theorem evaluationBialgEquiv_apply
    (hspan : Submodule.span R
      (Set.range (_root_.GroupLike.val (R := R) (A := H))) = ⊤)
    (x : MonoidAlgebra R (_root_.GroupLike R H)) :
    evaluationBialgEquiv R H hspan x = MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H) x :=
  evaluationBialgEquivOfLinearIndependentOfSpanEqTop_apply R H
    (linearIndep_groupLikeVal (R := R) (A := H)) hspan x

/-- The bialgebra morphism underlying the spanning equivalence is evaluation. -/
@[simp]
theorem evaluationBialgEquiv_toBialgHom
    (hspan : Submodule.span R
      (Set.range (_root_.GroupLike.val (R := R) (A := H))) = ⊤) :
    (evaluationBialgEquiv R H hspan :
      MonoidAlgebra R (_root_.GroupLike R H) →ₐc[R] H) =
        MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H) :=
  evaluationBialgEquivOfLinearIndependentOfSpanEqTop_toBialgHom R H
    (linearIndep_groupLikeVal (R := R) (A := H)) hspan

end Domain

end GroupLike

end TauCeti

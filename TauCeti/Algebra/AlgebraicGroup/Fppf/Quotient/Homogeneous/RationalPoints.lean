/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Map
public import TauCeti.AlgebraicGeometry.Sites.FppfAlgClosed
import TauCeti.CategoryTheory.Sites.LocallyBijective

/-!
# Rational points of homogeneous quotients over an algebraically closed field

Let `G` be an affine group over an algebraically closed field `k` and `N` a closed subgroup.
The fppf homogeneous quotient `G/N` is the sheafification of the presheaf of left cosets
`A ↦ G(A)/N(A)`, so in general its `A`-points are not cosets. Over `k` itself they are: every
fppf covering of `Spec k` splits, so sheafification changes neither the sections over `k` nor
their equality. Thus

```text
(G/N)(k) = G(k)/N(k).
```

No finiteness, reducedness, smoothness or normality is assumed of `G` or `N`. The comparison is
compatible with the quotient projection from `G` and with the projections `G/P ⟶ G/Q` induced by
inclusions `P ⊆ Q` of closed subgroups.

In particular every `k`-point of `G/N` lifts to a `k`-point of `G`, and two `k`-points of `G`
have the same image in `G/N` exactly when they differ by a `k`-point of `N`.

## Main declarations

* `CommHopfAlgCat.fppfHomogeneousQuotientRationalPointsEquiv`: the bijection
  `G(k)/N(k) ≃ (G/N)(k)`.
* `CommHopfAlgCat.fppfHomogeneousQuotientProjection_app_surjective`: rational points of `G/N`
  lift to rational points of `G`.
* `CommHopfAlgCat.fppfHomogeneousQuotientProjection_app_eq_iff`: the fibres of
  `G(k) → (G/N)(k)` are the left cosets of `N(k)`.
* `CommHopfAlgCat.fppfHomogeneousQuotientMap_app_rationalPointsEquiv`: the comparison commutes
  with the projections induced by inclusions of closed subgroups.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 5, quotient sheaves of affine groups and
  their rational points.
-/

public section

open CategoryTheory Opposite

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

universe u

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k] (H : _root_.CommHopfAlgCat.{u} k)
variable (I : HopfIdeal k H)

/-- **Fibres over rational points.** Two `k`-points of `G` have the same image in `G/N` exactly
when they differ on the right by a `k`-point of `N`. -/
theorem fppfHomogeneousQuotientProjection_app_eq_iff
    (g g' : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    (fppfHomogeneousQuotientProjection H I).app (op (op (CommAlgCat.of k k))) (ULift.up g) =
        (fppfHomogeneousQuotientProjection H I).app (op (op (CommAlgCat.of k k)))
          (ULift.up g') ↔
      g⁻¹ * g' ∈ quotientPointsSubgroup H I (CommAlgCat.of k k) := by
  rw [fppfHomogeneousQuotientProjection_def]
  simp only [NatTrans.comp_app, eqToHom_app, ConcreteCategory.comp_apply]
  -- Sheafification is injective on sections over `k`, since fppf covers of `Spec k` split.
  rw [(ConcreteCategory.bijective_of_isIso _).injective.eq_iff,
    (Presheaf.injective_app_of_isLocallyInjective _ _
      (CommAlgCat.eq_top_of_mem_fppfTopology_of_isAlgClosed k)).eq_iff]
  exact homogeneousQuotientPresheafProjection_eq_iff H I (op (op (CommAlgCat.of k k))) g g'

/-- **Rational points of `G/N` lift to `G`.** Over an algebraically closed field, every
`k`-point of the fppf homogeneous quotient is the image of a `k`-point of the group. -/
theorem fppfHomogeneousQuotientProjection_app_surjective :
    Function.Surjective
      ((fppfHomogeneousQuotientProjection H I).app (op (op (CommAlgCat.of k k)))) :=
  Presheaf.surjective_app_of_isLocallySurjective _ _
    (CommAlgCat.eq_top_of_mem_fppfTopology_of_isAlgClosed k)

/-- **Rational points of a homogeneous quotient.** Over an algebraically closed field `k`, the
`k`-points of the fppf homogeneous quotient `G/N` are the left cosets `G(k)/N(k)`. -/
def fppfHomogeneousQuotientRationalPointsEquiv :
    HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) ⧸
        quotientPointsSubgroup H I (CommAlgCat.of k k) ≃
      (fppfHomogeneousQuotient H I).obj.obj (op (op (CommAlgCat.of k k))) :=
  Equiv.ofBijective
    (Quotient.lift
      (fun g ↦ (fppfHomogeneousQuotientProjection H I).app (op (op (CommAlgCat.of k k)))
        (ULift.up g))
      fun g g' h ↦ (fppfHomogeneousQuotientProjection_app_eq_iff H I g g').mpr
        (QuotientGroup.leftRel_apply.mp h))
    ⟨fun q q' ↦ Quotient.inductionOn₂ q q' fun g g' h ↦
      QuotientGroup.eq.mpr ((fppfHomogeneousQuotientProjection_app_eq_iff H I g g').mp h),
     fun x ↦ by
      obtain ⟨⟨g⟩, rfl⟩ := fppfHomogeneousQuotientProjection_app_surjective H I x
      exact ⟨QuotientGroup.mk g, rfl⟩⟩

/-- The identification of rational points sends the coset of `g` to the image of `g` under
the quotient projection `G ⟶ G/N`. -/
@[simp]
theorem fppfHomogeneousQuotientRationalPointsEquiv_mk
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    fppfHomogeneousQuotientRationalPointsEquiv H I (QuotientGroup.mk g) =
      (fppfHomogeneousQuotientProjection H I).app (op (op (CommAlgCat.of k k))) (ULift.up g) :=
  (rfl)

/-- The inverse identification sends the image of `g` under the quotient projection to the
coset of `g`. -/
theorem fppfHomogeneousQuotientRationalPointsEquiv_symm_projection_app
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    (fppfHomogeneousQuotientRationalPointsEquiv H I).symm
        ((fppfHomogeneousQuotientProjection H I).app (op (op (CommAlgCat.of k k)))
          (ULift.up g)) =
      QuotientGroup.mk g := by
  rw [Equiv.symm_apply_eq, fppfHomogeneousQuotientRationalPointsEquiv_mk]

/-- **Compatibility with subgroup projections.** For closed subgroups `P ⊆ Q`, defined by
`I` and `J` with `J ≤ I`, the projection `G/P ⟶ G/Q` on `k`-points is the map of coset spaces
`G(k)/P(k) → G(k)/Q(k)`. -/
theorem fppfHomogeneousQuotientMap_app_rationalPointsEquiv {J : HopfIdeal k H} (hJI : J ≤ I)
    (q : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) ⧸
      quotientPointsSubgroup H I (CommAlgCat.of k k)) :
    (fppfHomogeneousQuotientMap H hJI).hom.app (op (op (CommAlgCat.of k k)))
        (fppfHomogeneousQuotientRationalPointsEquiv H I q) =
      fppfHomogeneousQuotientRationalPointsEquiv H J
        (Subgroup.quotientMapOfLE (quotientPointsSubgroup_le_of_le H hJI _) q) := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [Subgroup.quotientMapOfLE_apply_mk, fppfHomogeneousQuotientRationalPointsEquiv_mk,
      fppfHomogeneousQuotientRationalPointsEquiv_mk,
      ← fppfHomogeneousQuotientProjection_comp_map H hJI, NatTrans.comp_app,
      ConcreteCategory.comp_apply]

end

end CommHopfAlgCat

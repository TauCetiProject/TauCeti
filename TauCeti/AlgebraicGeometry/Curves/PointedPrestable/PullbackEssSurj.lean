/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.PointedPrestable.Category

/-!
# Base change of pointed prestable families along an isomorphism is essentially surjective

For an isomorphism of bases `g : T ⟶ S`, every pointed prestable family `Q` over `T` is isomorphic
to the base change along `g` of its base change along `g⁻¹`. The isomorphism is the canonical
isomorphism `isoPullback` from a family presented by fibre products to the chosen base change:
on total spaces the presentation is the inverse of the first projection `X ×_T S ⟶ X`, an
isomorphism since `g⁻¹` is one. So base change along an isomorphism is essentially surjective;
together with full faithfulness it is an equivalence of categories.

## Main definitions

* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.pullbackInvLift`: the inverse of the first
  projection `X ×_T S ⟶ X`.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.pullbackInvIso`:
  `(Q.pullback g⁻¹).pullback g ≅ Q` for an isomorphism `g`.

## Main results

* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.essSurj_pullbackFunctor`: base change along an
  isomorphism of bases is essentially surjective on pointed prestable families.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

namespace PointedPrestableFamily

variable {S T : Scheme.{u}} {n : ℕ} (g : T ⟶ S) [IsIso g] (Q : PointedPrestableFamily T n)

/-- The inverse of the first projection `X ×_T S ⟶ X` of the base change of `Q` along `g⁻¹`,
which is an isomorphism since `g⁻¹` is one. -/
def pullbackInvLift : Q.total ⟶ Limits.pullback Q.toBase (inv g) :=
  inv (Limits.pullback.fst Q.toBase (inv g))

@[simp, reassoc]
theorem pullbackInvLift_fst :
    pullbackInvLift g Q ≫ Limits.pullback.fst Q.toBase (inv g) = 𝟙 Q.total :=
  IsIso.inv_hom_id _

@[simp, reassoc]
theorem pullbackInvLift_snd :
    pullbackInvLift g Q ≫ Limits.pullback.snd Q.toBase (inv g) = Q.toBase ≫ g := by
  simp [pullbackInvLift]

@[simp, reassoc]
theorem fst_pullbackInvLift :
    Limits.pullback.fst Q.toBase (inv g) ≫ pullbackInvLift g Q = 𝟙 _ :=
  IsIso.hom_inv_id _

instance isIso_pullbackInvLift : IsIso (pullbackInvLift g Q) :=
  IsIso.of_isIso_fac_right (pullbackInvLift_fst g Q)

/-- `Q.total` with `pullbackInvLift` is a fibre product of the structure morphism of
`Q.pullback g⁻¹` and `g`, both horizontal maps being isomorphisms. -/
theorem isPullback_pullbackInvLift :
    IsPullback (pullbackInvLift g Q) Q.toBase (Limits.pullback.snd Q.toBase (inv g)) g :=
  IsPullback.of_horiz_isIso ⟨pullbackInvLift_snd g Q⟩

theorem marking_comp_pullbackInvLift (i : Fin n) :
    Q.marking i ≫ pullbackInvLift g Q = g ≫ (Q.pullback (inv g)).marking i := by
  dsimp only [pullback]
  apply Limits.pullback.hom_ext <;> simp

/-- For an isomorphism `g`, base change along `g` of the base change along `g⁻¹` is isomorphic to
the original family; on total spaces the isomorphism is the composite of the first projections
`(X ×_T S) ×_S T ⟶ X ×_T S ⟶ X` (`pullbackInvIso_hom_hom`). -/
def pullbackInvIso : (Q.pullback (inv g)).pullback g ≅ Q :=
  ((Q.pullback (inv g)).isoPullback g Q (pullbackInvLift g Q) (isPullback_pullbackInvLift g Q)
    (marking_comp_pullbackInvLift g Q)).symm

@[simp]
theorem pullbackInvIso_hom_hom :
    (pullbackInvIso g Q).hom.hom = Limits.pullback.fst (Limits.pullback.snd Q.toBase (inv g)) g ≫
      Limits.pullback.fst Q.toBase (inv g) := by
  -- The total space of a base change is only definitionally the chosen pullback, so the
  -- component is computed on the chosen pullback and then transported by `Eq.trans`.
  have h : (isPullback_pullbackInvLift g Q).isoPullback.inv =
      Limits.pullback.fst _ g ≫ Limits.pullback.fst Q.toBase (inv g) := by
    rw [← cancel_mono (pullbackInvLift g Q)]
    simp
  exact (isoPullback_inv_hom _ _ _ _ _ _).trans h

@[simp]
theorem pullbackInvIso_inv_hom :
    (pullbackInvIso g Q).inv.hom = Limits.pullback.lift (pullbackInvLift g Q) Q.toBase
      (isPullback_pullbackInvLift g Q).w := by
  have h : (isPullback_pullbackInvLift g Q).isoPullback.hom =
      Limits.pullback.lift (pullbackInvLift g Q) Q.toBase (isPullback_pullbackInvLift g Q).w := by
    apply Limits.pullback.hom_ext <;> simp
  exact (isoPullback_hom_hom _ _ _ _ _ _).trans h

/-- **Base change along an isomorphism of bases is essentially surjective** on pointed prestable
families. -/
instance essSurj_pullbackFunctor : (pullbackFunctor (n := n) g).EssSurj where
  mem_essImage Q := ⟨Q.pullback (inv g), ⟨pullbackInvIso g Q⟩⟩

end PointedPrestableFamily

end TauCeti.AlgebraicGeometry

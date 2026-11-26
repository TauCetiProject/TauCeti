/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.PointedPrestable.PullbackIso

/-!
# Base change of pointed prestable families along an isomorphism is essentially surjective

For an isomorphism of bases `g : T ⟶ S`, every pointed prestable family `Q` over `T` is isomorphic
to the base change along `g` of its base change along `g⁻¹`. The isomorphism is the composite of
the canonical isomorphism `pullbackCompIso` to the base change along `g ≫ g⁻¹ = 𝟙 T` with
`pullbackIdIso`. So base change along an isomorphism is essentially surjective; together with
full faithfulness (`TauCeti.AlgebraicGeometry.PointedPrestableFamily.full_pullbackFunctor` and
`TauCeti.AlgebraicGeometry.PointedPrestableFamily.faithful_pullbackFunctor`) it is an equivalence
of categories.

## Main definitions

* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.pullbackInvIso`:
  `(Q.pullback g⁻¹).pullback g ≅ Q` for an isomorphism `g`.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.pullbackEquivalence`: base change along an
  isomorphism `g`, as an equivalence of categories with inverse the base change along `g⁻¹` and
  counit `pullbackInvIso`.

## Main results

* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.essSurj_pullbackFunctor`: base change along an
  isomorphism of bases is essentially surjective on pointed prestable families.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.isEquivalence_pullbackFunctor`: base change
  along an isomorphism of bases is an equivalence of categories.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

namespace PointedPrestableFamily

variable {S T : Scheme.{u}} {n : ℕ} (g : T ⟶ S) [IsIso g] (Q : PointedPrestableFamily T n)

/-- For an isomorphism `g`, base change along `g` of the base change along `g⁻¹` is isomorphic to
the original family: the composite of `pullbackCompIso`, the identification of the base changes
along `g ≫ g⁻¹` and `𝟙 T`, and `pullbackIdIso`. On total spaces it is the composite of the first
projections `(X ×_T S) ×_S T ⟶ X ×_T S ⟶ X` (`pullbackInvIso_hom_hom`). -/
def pullbackInvIso : (Q.pullback (inv g)).pullback g ≅ Q :=
  Q.pullbackCompIso (inv g) g ≪≫ eqToIso (congrArg Q.pullback (IsIso.hom_inv_id g)) ≪≫
    Q.pullbackIdIso

@[simp]
theorem pullbackInvIso_hom_hom :
    (pullbackInvIso g Q).hom.hom = Limits.pullback.fst (Limits.pullback.snd Q.toBase (inv g)) g ≫
      Limits.pullback.fst Q.toBase (inv g) := by
  -- Transporting along `g ≫ g⁻¹ = 𝟙 T` commutes with the first projection to `Q.total`; this is
  -- checked for an arbitrary endomorphism equal to `𝟙 T`, where the equation can be substituted.
  have h (k : T ⟶ T) (hk : k = 𝟙 T) : (eqToHom (congrArg Q.pullback hk)).hom ≫
      Limits.pullback.fst Q.toBase (𝟙 T) = Limits.pullback.fst Q.toBase k := by
    subst hk
    exact Category.id_comp _
  simp only [pullbackInvIso, Iso.trans_hom, eqToIso.hom, comp_hom, pullbackCompIso_hom_hom,
    pullbackIdIso_hom_hom]
  -- The total space of a base change is only definitionally the chosen pullback.
  dsimp only [pullback] at h ⊢
  rw [h _ (IsIso.hom_inv_id g), pullbackLeftPullbackSndIso_hom_fst]

@[simp]
theorem pullbackInvIso_inv_hom :
    (pullbackInvIso g Q).inv.hom = Limits.pullback.lift (f := Limits.pullback.snd Q.toBase (inv g))
      (inv (Limits.pullback.fst Q.toBase (inv g))) Q.toBase (by simp) := by
  -- Both sides are right inverses of the isomorphism `pullbackInvIso_hom_hom` of total spaces.
  have h := congrArg Hom.hom (pullbackInvIso g Q).inv_hom_id
  simp only [comp_hom, pullbackInvIso_hom_hom, id_hom] at h
  refine (IsIso.eq_inv_of_inv_hom_id (f := Limits.pullback.fst (Limits.pullback.snd Q.toBase
    (inv g)) g ≫ Limits.pullback.fst Q.toBase (inv g)) h).trans
    (IsIso.eq_inv_of_inv_hom_id ?_).symm
  simp

/-- The isomorphism `pullbackInvIso` is natural in the family. -/
@[reassoc]
theorem pullbackInvIso_hom_naturality {Q Q' : PointedPrestableFamily T n} (f : Q ⟶ Q') :
    pullbackMap g (pullbackMap (inv g) f) ≫ (pullbackInvIso g Q').hom =
      (pullbackInvIso g Q).hom ≫ f := by
  refine hom_ext ?_
  simp only [comp_hom, pullbackInvIso_hom_hom]
  -- Paste the commutative squares of the two base changes of `f`; they are applied as terms since
  -- the total space of a base change is only definitionally the chosen pullback.
  exact ((isPullback_pullbackMap_hom g _).w_assoc _).symm.trans
    (congrArg (_ ≫ ·) (isPullback_pullbackMap_hom (inv g) f).w.symm) |>.trans
    (Category.assoc _ _ _).symm

/-- **Base change along an isomorphism of bases is essentially surjective** on pointed prestable
families. -/
instance essSurj_pullbackFunctor : (pullbackFunctor (n := n) g).EssSurj where
  mem_essImage Q := ⟨Q.pullback (inv g), ⟨pullbackInvIso g Q⟩⟩

/-- **Base change along an isomorphism of bases is an equivalence of categories** of pointed
prestable families: it is full, faithful and essentially surjective. -/
instance isEquivalence_pullbackFunctor : (pullbackFunctor (n := n) g).IsEquivalence where

-- The body is exposed because the statement of `pullbackEquivalence_counitIso_app` only
-- typechecks after unfolding it: `pullbackInvIso g Q` has the type of a counit component
-- only up to unfolding the functor and inverse of the equivalence.
/-- Base change along an isomorphism of bases `g : T ⟶ S`, as an equivalence between pointed
prestable families over `S` and over `T`. Its inverse is base change along `g⁻¹` and its counit
is `pullbackInvIso`. -/
@[expose]
def pullbackEquivalence : PointedPrestableFamily S n ≌ PointedPrestableFamily T n :=
  -- The counit is `pullbackInvIso`; the unit is its preimage under the fully faithful base change.
  let ε : pullbackFunctor (inv g) ⋙ pullbackFunctor g ≅ 𝟭 (PointedPrestableFamily T n) :=
    NatIso.ofComponents (pullbackInvIso g) (pullbackInvIso_hom_naturality g)
  .mk (pullbackFunctor g) (pullbackFunctor (inv g))
    (Functor.fullyFaithfulCancelRight (pullbackFunctor g)
      (Functor.isoWhiskerLeft (pullbackFunctor g) ε.symm)) ε

@[simp]
theorem pullbackEquivalence_functor :
    (pullbackEquivalence (n := n) g).functor = pullbackFunctor g :=
  (rfl)

@[simp]
theorem pullbackEquivalence_inverse :
    (pullbackEquivalence (n := n) g).inverse = pullbackFunctor (inv g) :=
  (rfl)

@[simp]
theorem pullbackEquivalence_counitIso_app :
    (pullbackEquivalence g).counitIso.app Q = pullbackInvIso g Q :=
  (rfl)

end PointedPrestableFamily

end TauCeti.AlgebraicGeometry

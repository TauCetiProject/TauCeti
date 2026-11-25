/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableMaps.Category

/-!
# Base change along an isomorphism of bases is essentially surjective

For an isomorphism of bases `g : T ⟶ S`, every pointed prestable family over `T` is isomorphic to
the base change along `g` of its base change along `g⁻¹`, and likewise every prestable map to the
base-changed target `V ×_S T ⟶ T`, after postcomposing the base change along `g⁻¹` with the
canonical projection `(V ×_S T) ×_T S ⟶ V`. Both isomorphisms are main's canonical isomorphisms
`isoPullback` from a family presented by fibre products to the chosen base change: on total spaces
the presentation is the inverse of the first projection `X ×_T S ⟶ X`, an isomorphism since `g⁻¹`
is one. So base change along an isomorphism is essentially surjective.

This is the essential-surjectivity part of StableReduction §10.1's "pullback along an isomorphism
of bases is an equivalence of categories".

## Main definitions

* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.pullbackInvIso`: `(Q.pullback g⁻¹).pullback g
  ≅ Q` for an isomorphism `g`.
* `TauCeti.AlgebraicGeometry.PrestableMap.pullbackInv`: the prestable map to `q` attached to a
  prestable map to `V ×_S T ⟶ T`, and `TauCeti.AlgebraicGeometry.PrestableMap.pullbackInvIso`:
  its base change along `g` is isomorphic to the original map.

## Main results

* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.essSurj_pullbackFunctor`,
  `TauCeti.AlgebraicGeometry.PrestableMap.essSurj_pullbackFunctor`: base change along an
  isomorphism of bases is essentially surjective.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

namespace PointedPrestableFamily

variable {S T : Scheme.{u}} {n : ℕ} (g : T ⟶ S) [IsIso g] (Q : PointedPrestableFamily T n)

/-- The inverse of the first projection `X ×_T S ⟶ X` of the base change of `Q` along `g⁻¹`. -/
def pullbackInvLift : Q.total ⟶ (Q.pullback (inv g)).total :=
  Limits.pullback.lift (𝟙 Q.total) (Q.toBase ≫ g) (by simp)

@[reassoc]
theorem pullbackInvLift_fst :
    pullbackInvLift g Q ≫ Limits.pullback.fst Q.toBase (inv g) = 𝟙 Q.total :=
  Limits.pullback.lift_fst _ _ _

@[reassoc]
theorem pullbackInvLift_snd :
    pullbackInvLift g Q ≫ Limits.pullback.snd Q.toBase (inv g) = Q.toBase ≫ g :=
  Limits.pullback.lift_snd _ _ _

instance isIso_pullbackInvLift : IsIso (pullbackInvLift g Q) :=
  ⟨⟨Limits.pullback.fst Q.toBase (inv g), pullbackInvLift_fst g Q, by
    apply Limits.pullback.hom_ext
    · erw [Category.assoc, Limits.pullback.lift_fst, Category.comp_id]
    · erw [Category.assoc, Limits.pullback.lift_snd, Category.id_comp,
        Limits.pullback.condition_assoc, IsIso.inv_hom_id, Category.comp_id]⟩⟩

/-- `Q.total` with `pullbackInvLift` is a fibre product of the structure morphism of
`Q.pullback g⁻¹` and `g`, both horizontal maps being isomorphisms. -/
theorem isPullback_pullbackInvLift :
    IsPullback (pullbackInvLift g Q) Q.toBase (Q.pullback (inv g)).toBase g :=
  IsPullback.of_horiz_isIso ⟨pullbackInvLift_snd g Q⟩

theorem marking_comp_pullbackInvLift (i : Fin n) :
    Q.marking i ≫ pullbackInvLift g Q = g ≫ (Q.pullback (inv g)).marking i := by
  dsimp only [pullback]
  apply Limits.pullback.hom_ext <;> simp [pullbackInvLift]

/-- For an isomorphism `g`, base change along `g` of the base change along `g⁻¹` is isomorphic to
the original family; on total spaces the isomorphism is the first projection. -/
def pullbackInvIso : (Q.pullback (inv g)).pullback g ≅ Q :=
  ((Q.pullback (inv g)).isoPullback g Q (pullbackInvLift g Q) (isPullback_pullbackInvLift g Q)
    (marking_comp_pullbackInvLift g Q)).symm

/-- **Base change along an isomorphism of bases is essentially surjective** on pointed prestable
families. -/
instance essSurj_pullbackFunctor : (pullbackFunctor (n := n) g).EssSurj where
  mem_essImage Q := ⟨Q.pullback (inv g), ⟨pullbackInvIso g Q⟩⟩

end PointedPrestableFamily

namespace PrestableMap

variable {V S T : Scheme.{u}} {q : V ⟶ S} {n : ℕ} (g : T ⟶ S) [IsIso g]
  (G : PrestableMap (Limits.pullback.snd q g) n)

/-- The projection `(V ×_S T) ×_T S ⟶ V`. -/
abbrev pullbackInvTarget :
    Limits.pullback (Limits.pullback.snd q g) (inv g) ⟶ V :=
  Limits.pullback.fst _ _ ≫ Limits.pullback.fst q g

theorem pullbackInvTarget_comp :
    pullbackInvTarget g ≫ q = Limits.pullback.snd (Limits.pullback.snd q g) (inv g) := by
  rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, Limits.pullback.condition,
    Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- The prestable map to `q` attached to a prestable map `G` to `V ×_S T ⟶ T`: the base change of
`G` along `g⁻¹`, postcomposed with the projection `(V ×_S T) ×_T S ⟶ V`. -/
def pullbackInv : PrestableMap q n :=
  (G.pullback (inv g)).postcomp (pullbackInvTarget g) (pullbackInvTarget_comp g)

theorem pullbackInv_curve : (pullbackInv g G).curve = G.curve.pullback (inv g) :=
  (rfl)

omit [IsIso g] in
/-- The canonical isomorphism `V ×_S T ≅ V ×_S T` of the chosen pullback with itself is the
identity. -/
theorem isoPullback_inv_of_hasPullback :
    (IsPullback.of_hasPullback q g).isoPullback.inv = 𝟙 _ := by
  apply Limits.pullback.hom_ext <;> simp

/-- For an isomorphism `g`, the base change along `g` of `pullbackInv g G` is isomorphic to `G`; on
total spaces the isomorphism is the first projection. -/
def pullbackInvIso : (pullbackInv g G).pullback g ≅ G :=
  isoMk (F := (pullbackInv g G).pullback g)
      (G := ((pullbackInv g G).pullback g).postcomp
        (IsPullback.of_hasPullback q g).isoPullback.inv
        (IsPullback.of_hasPullback q g).isoPullback_inv_snd)
      (Iso.refl _) (by simp [postcomp, isoPullback_inv_of_hasPullback]) ≪≫
    ((pullbackInv g G).isoPullback g (Limits.pullback.fst q g)
      (IsPullback.of_hasPullback q g) G (G.curve.pullbackInvLift g)
      (G.curve.isPullback_pullbackInvLift g) (G.curve.marking_comp_pullbackInvLift g)
      (by
        simp only [pullbackInv, postcomp, pullbackInvTarget,
          PointedPrestableFamily.pullbackInvLift]
        simp only [pullback_map_fst_assoc]
        erw [← Category.assoc, ← Category.assoc, Limits.pullback.lift_fst, Category.id_comp])).symm

/-- **Base change along an isomorphism of bases is essentially surjective** on prestable maps. -/
instance essSurj_pullbackFunctor : (pullbackFunctor (q := q) (n := n) g).EssSurj where
  mem_essImage G := ⟨pullbackInv g G, ⟨pullbackInvIso g G⟩⟩

end PrestableMap

end TauCeti.AlgebraicGeometry

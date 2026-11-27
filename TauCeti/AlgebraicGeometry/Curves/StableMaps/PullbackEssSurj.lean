/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.PointedPrestable.PullbackEssSurj
public import TauCeti.AlgebraicGeometry.Curves.StableMaps.PullbackIso

/-!
# Base change of prestable maps along an isomorphism is essentially surjective

For an isomorphism of bases `g : T ⟶ S`, every prestable map `G` to the base-changed target
`V ×_S T ⟶ T` is isomorphic to the base change along `g` of `pullbackInv g G`: the base change of
`G` along `g⁻¹`, postcomposed with the canonical projection `(V ×_S T) ×_T S ⟶ V`. On source
curves the isomorphism is `TauCeti.AlgebraicGeometry.PointedPrestableFamily.pullbackInvIso`, which
commutes with the maps to `V ×_S T`. So base change along an isomorphism is essentially
surjective; together with full faithfulness
(`TauCeti.AlgebraicGeometry.PrestableMap.full_pullbackFunctor` and
`TauCeti.AlgebraicGeometry.PrestableMap.faithful_pullbackFunctor`) it is an equivalence of
categories.

## Main definitions

* `TauCeti.AlgebraicGeometry.PrestableMap.pullbackInv`: the prestable map to `q` attached to a
  prestable map to `V ×_S T ⟶ T`.
* `TauCeti.AlgebraicGeometry.PrestableMap.pullbackInvIso`: its base change along `g` is
  isomorphic to the original map.
* `TauCeti.AlgebraicGeometry.PrestableMap.pullbackEquivalence`: base change along an isomorphism
  `g`, as an equivalence of categories with inverse `pullbackInv g` and counit `pullbackInvIso`.

## Main results

* `TauCeti.AlgebraicGeometry.PrestableMap.essSurj_pullbackFunctor`: base change along an
  isomorphism of bases is essentially surjective on prestable maps.
* `TauCeti.AlgebraicGeometry.PrestableMap.isEquivalence_pullbackFunctor`: base change along an
  isomorphism of bases is an equivalence of categories.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

namespace PrestableMap

variable {V S T : Scheme.{u}} {q : V ⟶ S} {n : ℕ} (g : T ⟶ S) [IsIso g]
  (G : PrestableMap (Limits.pullback.snd q g) n)

/-- The projection `(V ×_S T) ×_T S ⟶ V`. -/
abbrev pullbackInvTarget :
    Limits.pullback (Limits.pullback.snd q g) (inv g) ⟶ V :=
  Limits.pullback.fst _ _ ≫ Limits.pullback.fst q g

theorem pullbackInvTarget_comp :
    pullbackInvTarget g ≫ q = Limits.pullback.snd (Limits.pullback.snd q g) (inv g) := by
  simp [Limits.pullback.condition, Limits.pullback.condition_assoc]

/-- The prestable map to `q` attached to a prestable map `G` to `V ×_S T ⟶ T`: the base change of
`G` along `g⁻¹`, postcomposed with the projection `(V ×_S T) ×_T S ⟶ V`. -/
@[expose]
def pullbackInv : PrestableMap q n :=
  (G.pullback (inv g)).postcomp (pullbackInvTarget g) (pullbackInvTarget_comp g)

@[simp]
theorem pullbackInv_curve : (pullbackInv g G).curve = G.curve.pullback (inv g) :=
  (rfl)

@[simp]
theorem pullbackInv_map :
    (pullbackInv g G).map = (G.pullback (inv g)).map ≫ pullbackInvTarget g :=
  (rfl)

/-- For an isomorphism `g`, the base change along `g` of `pullbackInv g G` is isomorphic to `G`;
on source curves it is `PointedPrestableFamily.pullbackInvIso`, so on total spaces it is the
composite of the first projections `(C ×_T S) ×_S T ⟶ C ×_T S ⟶ C`. -/
def pullbackInvIso : (pullbackInv g G).pullback g ≅ G :=
  isoMk (G.curve.pullbackInvIso g) (by
    dsimp only [pullbackInv, postcomp, pullback, PointedPrestableFamily.pullback]
    apply Limits.pullback.hom_ext
    · simp
    -- On the second projection it suffices that the isomorphism of curves lies over `T`, so its
    -- formula as a composite of projections is not unfolded.
    · simp [-PointedPrestableFamily.pullbackInvIso_hom_hom])

@[simp]
theorem pullbackInvIso_hom_curve :
    (pullbackInvIso g G).hom.curve = (G.curve.pullbackInvIso g).hom :=
  isoMk_hom_curve _ _

@[simp]
theorem pullbackInvIso_inv_curve :
    (pullbackInvIso g G).inv.curve = (G.curve.pullbackInvIso g).inv :=
  isoMk_inv_curve _ _

/-- **Base change along an isomorphism of bases is essentially surjective** on prestable maps. -/
instance essSurj_pullbackFunctor : (pullbackFunctor (q := q) (n := n) g).EssSurj where
  mem_essImage G := ⟨pullbackInv g G, ⟨pullbackInvIso g G⟩⟩

/-- **Base change along an isomorphism of bases is an equivalence of categories** of prestable
maps: it is full, faithful and essentially surjective. -/
instance isEquivalence_pullbackFunctor : (pullbackFunctor (q := q) (n := n) g).IsEquivalence where

-- The body is exposed because the statement of `pullbackEquivalence_counitIso_app` only
-- typechecks after unfolding it: `pullbackInvIso g G` has the type of a counit component
-- only up to unfolding the functor and inverse of the equivalence.
/-- Base change along an isomorphism of bases `g : T ⟶ S`, as an equivalence between prestable
maps to `q : V ⟶ S` and prestable maps to the base-changed target `V ×_S T ⟶ T`. Its inverse
sends `G` to `pullbackInv g G` and its counit is `pullbackInvIso`. -/
@[expose]
def pullbackEquivalence : PrestableMap q n ≌ PrestableMap (Limits.pullback.snd q g) n :=
  -- The counit is `pullbackInvIso`; the unit is its preimage under the fully faithful base change.
  let ε : (pullbackFunctor (inv g) ⋙ postcompFunctor (pullbackInvTarget g)
      (pullbackInvTarget_comp g)) ⋙ pullbackFunctor g ≅ 𝟭 (PrestableMap (pullback.snd q g) n) :=
    -- The source of `pullbackInvIso` is only definitionally the image under the composite
    -- functor, so `comp_curve` is applied as a term rather than by rewriting.
    NatIso.ofComponents (pullbackInvIso g) fun f ↦ hom_ext <| (comp_curve _ _).trans (by
      simp only [Functor.comp_map, pullbackFunctor_map, pullbackMap_curve,
        pullbackInvIso_hom_curve, Functor.id_map]
      -- Postcomposition does not change the morphism of source curves.
      have h := PointedPrestableFamily.pullbackInvIso_hom_naturality g f.curve
      rw [← pullbackMap_curve (inv g) f] at h
      exact h) |>.trans
      (comp_curve _ _).symm
  .mk (pullbackFunctor g)
    (pullbackFunctor (inv g) ⋙ postcompFunctor (pullbackInvTarget g) (pullbackInvTarget_comp g))
    (Functor.fullyFaithfulCancelRight (pullbackFunctor g)
      (Functor.isoWhiskerLeft (pullbackFunctor g) ε.symm)) ε

@[simp]
theorem pullbackEquivalence_functor :
    (pullbackEquivalence (q := q) (n := n) g).functor = pullbackFunctor g :=
  (rfl)

@[simp]
theorem pullbackEquivalence_inverse :
    (pullbackEquivalence (q := q) (n := n) g).inverse =
      pullbackFunctor (inv g) ⋙ postcompFunctor (pullbackInvTarget g) (pullbackInvTarget_comp g) :=
  (rfl)

@[simp]
theorem pullbackEquivalence_counitIso_app :
    (pullbackEquivalence g).counitIso.app G = pullbackInvIso g G :=
  (rfl)

end PrestableMap

end TauCeti.AlgebraicGeometry

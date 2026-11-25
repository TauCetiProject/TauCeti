/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.PointedPrestable.PullbackIso
public import TauCeti.AlgebraicGeometry.Curves.StableMaps.Category

/-!
# Base change of prestable maps along an isomorphism is fully faithful

Let `g : T ⟶ S` be a morphism of schemes. Base change of prestable maps along `g` is faithful as
soon as the projections `C ×_S T ⟶ C` of total spaces of source curves are epimorphisms
(`TauCeti.AlgebraicGeometry.PrestableMap.pullbackMap_injective_of_epi`), in particular when `g` is
flat and surjective. When `g` is an isomorphism, every morphism of base changes is the base change
of the morphism of prestable maps given on source curves by
`TauCeti.AlgebraicGeometry.PointedPrestableFamily.unpullbackMap`, so base change is also full.

## Main results

* The instances `(PrestableMap.pullbackFunctor g).Faithful` for a flat surjective `g` and
  `(PrestableMap.pullbackFunctor g).Full` for an isomorphism `g`.
* `TauCeti.AlgebraicGeometry.PrestableMap.unpullbackMap`: the preimage of a morphism of base
  changes along an isomorphism, with `pullbackMap_unpullbackMap` and `unpullbackMap_pullbackMap`.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

namespace PrestableMap

variable {V S T : Scheme.{u}} {q : V ⟶ S} {n : ℕ} {F G : PrestableMap q n}

/-- Base change of prestable maps along a flat surjective morphism is faithful: the projections
of total spaces of source curves are then flat and surjective, hence epimorphisms of schemes. -/
instance faithful_pullbackFunctor (g : T ⟶ S) [Flat g] [Surjective g] :
    (pullbackFunctor (q := q) (n := n) g).Faithful where
  map_injective {F _} :=
    have := Flat.epi_of_flat_of_surjective (pullback.fst F.curve.toBase g)
    pullbackMap_injective_of_epi g

variable (g : T ⟶ S) [IsIso g]

/-- For an isomorphism `g`, the conjugate `pr₁ ∘ ψ ∘ pr₁⁻¹` of a morphism `ψ : C ×_S T ⟶ D ×_S T`
commuting with base changes `m`, `m'` of the maps of prestable maps commutes with the maps. -/
private lemma inv_fst_comp_fst_comp_map
    (ψ : Limits.pullback F.curve.toBase g ⟶ Limits.pullback G.curve.toBase g)
    (m : Limits.pullback G.curve.toBase g ⟶ Limits.pullback q g)
    (hm : m ≫ pullback.fst q g = pullback.fst G.curve.toBase g ≫ G.map)
    (m' : Limits.pullback F.curve.toBase g ⟶ Limits.pullback q g)
    (hm' : m' ≫ pullback.fst q g = pullback.fst F.curve.toBase g ≫ F.map) (h : ψ ≫ m = m') :
    (inv (pullback.fst F.curve.toBase g) ≫ ψ ≫ pullback.fst G.curve.toBase g) ≫ G.map =
      F.map := by
  rw [Category.assoc, Category.assoc, ← hm, reassoc_of% h, hm', IsIso.inv_hom_id_assoc]

/-- The morphism of prestable maps `F ⟶ G` whose base change along an isomorphism `g` is a given
morphism `φ`: on source curves it is `PointedPrestableFamily.unpullbackMap`. -/
def unpullbackMap (φ : F.pullback g ⟶ G.pullback g) : F ⟶ G where
  curve := PointedPrestableFamily.unpullbackMap g φ.curve
  hom_comp_map := (congrArg (· ≫ G.map) (PointedPrestableFamily.unpullbackMap_hom g φ.curve)).trans
    (inv_fst_comp_fst_comp_map g φ.curve.hom _ (pullback_map_fst G g) _ (pullback_map_fst F g)
      φ.hom_comp_map)

@[simp]
theorem unpullbackMap_curve (φ : F.pullback g ⟶ G.pullback g) :
    (unpullbackMap g φ).curve = PointedPrestableFamily.unpullbackMap g φ.curve :=
  (rfl)

/-- The base change of `unpullbackMap g φ` is `φ`. -/
@[simp]
theorem pullbackMap_unpullbackMap (φ : F.pullback g ⟶ G.pullback g) :
    pullbackMap g (unpullbackMap g φ) = φ :=
  hom_ext ((pullbackMap_curve g _).trans
    (PointedPrestableFamily.pullbackMap_unpullbackMap g φ.curve))

/-- `unpullbackMap g` recovers a morphism of prestable maps from its base change. -/
@[simp]
theorem unpullbackMap_pullbackMap (f : F ⟶ G) : unpullbackMap g (pullbackMap g f) = f :=
  pullbackMap_injective_of_epi g (pullbackMap_unpullbackMap g _)

/-- Base change of prestable maps along an isomorphism is full. -/
instance full_pullbackFunctor : (pullbackFunctor (q := q) (n := n) g).Full where
  map_surjective φ := ⟨unpullbackMap g φ, pullbackMap_unpullbackMap g φ⟩

end PrestableMap

end TauCeti.AlgebraicGeometry

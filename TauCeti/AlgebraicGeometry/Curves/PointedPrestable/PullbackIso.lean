/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import TauCeti.AlgebraicGeometry.Curves.PointedPrestable.Category

/-!
# Base change of pointed prestable families along an isomorphism is fully faithful

Let `g : T ⟶ S` be a morphism of schemes. Base change of pointed prestable families along `g` is
faithful as soon as the projections `C ×_S T ⟶ C` of total spaces are epimorphisms
(`TauCeti.AlgebraicGeometry.PointedPrestableFamily.pullbackMap_injective_of_epi`), in particular
when `g` is flat and surjective. When `g` is an isomorphism these projections are isomorphisms,
and every morphism `φ : C ×_S T ⟶ D ×_S T` of base changes is the base change of
`pr₁ ∘ φ ∘ pr₁⁻¹ : C ⟶ D`, so base change is also full.

## Main results

* The instances `(PointedPrestableFamily.pullbackFunctor g).Faithful` for a flat surjective `g`
  and `(PointedPrestableFamily.pullbackFunctor g).Full` for an isomorphism `g`.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.unpullbackMap`: the preimage of a morphism of
  base changes along an isomorphism, with `pullbackMap_unpullbackMap` and
  `unpullbackMap_pullbackMap`.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

namespace PointedPrestableFamily

variable {S T : Scheme.{u}} {n : ℕ} {P Q : PointedPrestableFamily S n}

/-- Base change along a flat surjective morphism is faithful: the projections of total spaces are
then flat and surjective, hence epimorphisms of schemes. -/
instance faithful_pullbackFunctor (g : T ⟶ S) [Flat g] [Surjective g] :
    (pullbackFunctor (n := n) g).Faithful where
  map_injective {P _} :=
    have := Flat.epi_of_flat_of_surjective (pullback.fst P.toBase g)
    pullbackMap_injective_of_epi g

variable (g : T ⟶ S) [IsIso g]

/-! The total space of `P.pullback g` is only definitionally, not reducibly, the pullback
`P ×_S T`, so the computations are done for morphisms `ψ : P ×_S T ⟶ Q ×_S T` of chosen pullbacks
and then applied to `φ.hom`. -/

/-- For an isomorphism `g`, the conjugate `pr₁ ∘ ψ ∘ pr₁⁻¹` of a morphism `ψ : P ×_S T ⟶ Q ×_S T`
over `T` lies over `S`. -/
private lemma inv_fst_comp_fst_comp_toBase
    (ψ : Limits.pullback P.toBase g ⟶ Limits.pullback Q.toBase g)
    (h : ψ ≫ pullback.snd Q.toBase g = pullback.snd P.toBase g) :
    (inv (pullback.fst P.toBase g) ≫ ψ ≫ pullback.fst Q.toBase g) ≫ Q.toBase = P.toBase := by
  rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% h, ← pullback.condition,
    IsIso.inv_hom_id_assoc]

/-- For an isomorphism `g`, the conjugate `pr₁ ∘ ψ ∘ pr₁⁻¹` of a morphism `ψ : P ×_S T ⟶ Q ×_S T`
preserving the markings preserves the markings. -/
private lemma marking_comp_inv_fst_comp_fst
    (ψ : Limits.pullback P.toBase g ⟶ Limits.pullback Q.toBase g) (i : Fin n)
    (h : pullback.lift (g ≫ P.marking i) (𝟙 T) (by simp) ≫ ψ =
      pullback.lift (g ≫ Q.marking i) (𝟙 T) (by simp)) :
    P.marking i ≫ inv (pullback.fst P.toBase g) ≫ ψ ≫ pullback.fst Q.toBase g = Q.marking i := by
  -- The `i`th marking of `P` is `g⁻¹` followed by the `i`th marking of `P ×_S T` and `pr₁`.
  have hP : P.marking i ≫ inv (pullback.fst P.toBase g) =
      inv g ≫ pullback.lift (g ≫ P.marking i) (𝟙 T) (by simp) := by
    rw [IsIso.comp_inv_eq, Category.assoc, pullback.lift_fst, IsIso.inv_hom_id_assoc]
  rw [reassoc_of% hP, reassoc_of% h, pullback.lift_fst, IsIso.inv_hom_id_assoc]

private lemma map_unpullback (ψ : Limits.pullback P.toBase g ⟶ Limits.pullback Q.toBase g)
    (h : ψ ≫ pullback.snd Q.toBase g = pullback.snd P.toBase g) :
    pullback.map P.toBase g Q.toBase g
      (inv (pullback.fst P.toBase g) ≫ ψ ≫ pullback.fst Q.toBase g) (𝟙 T) (𝟙 S)
      (by rw [Category.comp_id, inv_fst_comp_fst_comp_toBase g ψ h]) (by simp) = ψ := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst, IsIso.hom_inv_id_assoc]
  · rw [pullback.lift_snd, Category.comp_id, h]

/-- The morphism `P ⟶ Q` whose base change along an isomorphism `g` is a given morphism
`φ : P ×_S T ⟶ Q ×_S T`: on total spaces it is `pr₁ ∘ φ ∘ pr₁⁻¹`. -/
def unpullbackMap (φ : P.pullback g ⟶ Q.pullback g) : P ⟶ Q where
  hom := inv (pullback.fst P.toBase g) ≫ φ.hom ≫ pullback.fst Q.toBase g
  hom_comp_toBase := inv_fst_comp_fst_comp_toBase g φ.hom φ.hom_comp_toBase
  marking_comp_hom i := marking_comp_inv_fst_comp_fst g φ.hom i (φ.marking_comp_hom i)

@[simp]
theorem unpullbackMap_hom (φ : P.pullback g ⟶ Q.pullback g) :
    (unpullbackMap g φ).hom = inv (pullback.fst P.toBase g) ≫ φ.hom ≫ pullback.fst Q.toBase g :=
  (rfl)

/-- The base change of `unpullbackMap g φ` is `φ`. -/
@[simp]
theorem pullbackMap_unpullbackMap (φ : P.pullback g ⟶ Q.pullback g) :
    pullbackMap g (unpullbackMap g φ) = φ :=
  hom_ext ((pullbackMap_hom g _).trans (map_unpullback g φ.hom φ.hom_comp_toBase))

/-- `unpullbackMap g` recovers a morphism from its base change. -/
@[simp]
theorem unpullbackMap_pullbackMap (f : P ⟶ Q) : unpullbackMap g (pullbackMap g f) = f :=
  pullbackMap_injective_of_epi g (pullbackMap_unpullbackMap g _)

/-- Base change along an isomorphism is full. -/
instance full_pullbackFunctor : (pullbackFunctor (n := n) g).Full where
  map_surjective φ := ⟨unpullbackMap g φ, pullbackMap_unpullbackMap g φ⟩

end PointedPrestableFamily

end TauCeti.AlgebraicGeometry

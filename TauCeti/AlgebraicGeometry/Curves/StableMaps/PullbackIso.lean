/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableMaps.Category

/-!
# Base change of prestable maps along an isomorphism is fully faithful

Let `g : T ⟶ S` be a morphism of schemes. Base change of pointed prestable families and of
prestable maps along `g` is faithful as soon as the projections `C ×_S T ⟶ C` of total spaces are
epimorphisms: a morphism `f` is recovered from its base change through
`f ∘ pr₁ = pr₁ ∘ (f ×_S T)`. When `g` is an isomorphism these projections are isomorphisms, and
every morphism `φ : C ×_S T ⟶ D ×_S T` of base changes is the base change of
`pr₁ ∘ φ ∘ pr₁⁻¹ : C ⟶ D`, so base change is also full.

## Main results

* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.pullbackMap_injective_of_epi`,
  `TauCeti.AlgebraicGeometry.PrestableMap.pullbackMap_injective_of_epi`: base change is injective
  on morphisms when the projection of total spaces is an epimorphism.
* The instances `(PointedPrestableFamily.pullbackFunctor g).Faithful`,
  `(PointedPrestableFamily.pullbackFunctor g).Full`, `(PrestableMap.pullbackFunctor g).Faithful`
  and `(PrestableMap.pullbackFunctor g).Full` for an isomorphism `g`.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.pullbackMap_unpullbackMap`,
  `TauCeti.AlgebraicGeometry.PrestableMap.pullbackMap_unpullbackMap`: the preimage of a morphism of
  base changes along an isomorphism.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

namespace PointedPrestableFamily

variable {S T : Scheme.{u}} {n : ℕ} {P Q : PointedPrestableFamily S n}

/-- Base change along `g` is injective on morphisms `P ⟶ Q` when the projection
`P ×_S T ⟶ P` of total spaces is an epimorphism. -/
theorem pullbackMap_injective_of_epi (g : T ⟶ S) [Epi (pullback.fst P.toBase g)] :
    Function.Injective (pullbackMap g : (P ⟶ Q) → (P.pullback g ⟶ Q.pullback g)) := by
  intro f f' hff'
  refine hom_ext ?_
  rw [← cancel_epi (pullback.fst P.toBase g), (isPullback_pullbackMap_hom g f).w,
    (isPullback_pullbackMap_hom g f').w, hff']

/-- Base change along an isomorphism is faithful. -/
instance faithful_pullbackFunctor (g : T ⟶ S) [IsIso g] :
    (pullbackFunctor (n := n) g).Faithful where
  map_injective h := pullbackMap_injective_of_epi g h

variable (g : T ⟶ S) [IsIso g]

/-! The total space of `P.pullback g` is only definitionally, not reducibly, the pullback
`P ×_S T`, so the computations are done for morphisms `ψ : P ×_S T ⟶ Q ×_S T` of chosen pullbacks
and then applied to `φ.hom`. -/

/-- For an isomorphism `g`, the conjugate `pr₁ ∘ ψ ∘ pr₁⁻¹` of a morphism `ψ : P ×_S T ⟶ Q ×_S T`
over `T` lies over `S`. -/
theorem inv_fst_comp_fst_comp_toBase (ψ : Limits.pullback P.toBase g ⟶ Limits.pullback Q.toBase g)
    (h : ψ ≫ pullback.snd Q.toBase g = pullback.snd P.toBase g) :
    (inv (pullback.fst P.toBase g) ≫ ψ ≫ pullback.fst Q.toBase g) ≫ Q.toBase = P.toBase := by
  rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% h, ← pullback.condition,
    IsIso.inv_hom_id_assoc]

/-- For an isomorphism `g`, the conjugate `pr₁ ∘ ψ ∘ pr₁⁻¹` of a morphism `ψ : P ×_S T ⟶ Q ×_S T`
preserving the markings preserves the markings. -/
theorem marking_comp_inv_fst_comp_fst (ψ : Limits.pullback P.toBase g ⟶ Limits.pullback Q.toBase g)
    (i : Fin n)
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
@[expose] def unpullbackMap (φ : P.pullback g ⟶ Q.pullback g) : P ⟶ Q where
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

/-- Base change along an isomorphism is full. -/
instance full_pullbackFunctor : (pullbackFunctor (n := n) g).Full where
  map_surjective φ := ⟨unpullbackMap g φ, pullbackMap_unpullbackMap g φ⟩

end PointedPrestableFamily

namespace PrestableMap

variable {V S T : Scheme.{u}} {q : V ⟶ S} {n : ℕ} {F G : PrestableMap q n}

/-- Base change along `g` is injective on morphisms `F ⟶ G` of prestable maps when the projection
`C ×_S T ⟶ C` of total spaces of source curves is an epimorphism. -/
theorem pullbackMap_injective_of_epi (g : T ⟶ S) [Epi (pullback.fst F.curve.toBase g)] :
    Function.Injective (pullbackMap g : (F ⟶ G) → (F.pullback g ⟶ G.pullback g)) :=
  fun f f' hff' ↦ hom_ext (PointedPrestableFamily.pullbackMap_injective_of_epi g
    ((pullbackMap_curve g f).symm.trans ((congrArg Hom.curve hff').trans (pullbackMap_curve g f'))))

/-- Base change of prestable maps along an isomorphism is faithful. -/
instance faithful_pullbackFunctor (g : T ⟶ S) [IsIso g] :
    (pullbackFunctor (q := q) (n := n) g).Faithful where
  map_injective h := pullbackMap_injective_of_epi g h

variable (g : T ⟶ S) [IsIso g]

/-- For an isomorphism `g`, the conjugate `pr₁ ∘ ψ ∘ pr₁⁻¹` of a morphism `ψ : C ×_S T ⟶ D ×_S T`
commuting with base changes `m`, `m'` of the maps of prestable maps commutes with the maps. -/
theorem inv_fst_comp_fst_comp_map
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
@[expose] def unpullbackMap (φ : F.pullback g ⟶ G.pullback g) : F ⟶ G where
  curve := PointedPrestableFamily.unpullbackMap g φ.curve
  hom_comp_map := inv_fst_comp_fst_comp_map g φ.curve.hom _ (pullback_map_fst G g) _
    (pullback_map_fst F g) φ.hom_comp_map

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

/-- Base change of prestable maps along an isomorphism is full. -/
instance full_pullbackFunctor : (pullbackFunctor (q := q) (n := n) g).Full where
  map_surjective φ := ⟨unpullbackMap g φ, pullbackMap_unpullbackMap g φ⟩

end PrestableMap

end TauCeti.AlgebraicGeometry

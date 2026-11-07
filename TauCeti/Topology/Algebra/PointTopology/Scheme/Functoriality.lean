/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.PointTopology.Scheme.Charts

/-!
# Functoriality of the topology on scheme-valued points

A morphism of schemes over `Spec k` acts on `R`-points by composition. Over a local
topological ring with open units and continuous inversion on the units, this action is
continuous, and open immersions induce open embeddings. Thus an open subscheme carries
exactly the subspace topology on its points. No finiteness or separation assumptions
on the schemes or coefficient ring are needed.

For an open immersion, the image consists of the points whose underlying scheme
morphism lands in the open subscheme. When `R` is local it suffices to test the image
of the closed point of `Spec R`. On affine schemes the action agrees with
precomposition of algebra homomorphisms under `affineHomeomorph`.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Prop. 3.1 and its
  proof, pp. 3–4.
-/

public section

open CategoryTheory AlgebraicGeometry Topology
open scoped TauCeti.PointTopology TauCeti.SchemePointTopology

universe u

namespace TauCeti.SchemePointTopology

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
  {X Y Z : Scheme.{u}} {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)}
  {fZ : Z ⟶ Spec (.of k)}

/-- The map on scheme-valued points induced by a morphism over the base. -/
noncomputable def map (g : X ⟶ Y) (hg : g ≫ fY = fX) (x : Points (R := R) fX) :
    Points (R := R) fY :=
  ⟨x.val ≫ g, by rw [Category.assoc, hg, x.property]⟩

/-- The underlying morphism of the image of a point is its composite with `g`. -/
@[simp]
theorem map_val (g : X ⟶ Y) (hg : g ≫ fY = fX) (x : Points (R := R) fX) :
    (map g hg x).val = x.val ≫ g :=
  (rfl)

/-- The identity morphism acts as the identity on points. -/
@[simp]
theorem map_id (x : Points (R := R) fX) : map (𝟙 X) (Category.id_comp fX) x = x := by
  apply Subtype.ext
  simp

/-- Composition of morphisms acts by composition of the maps on points. -/
@[simp]
theorem map_map (g : X ⟶ Y) (h : Y ⟶ Z) (hg : g ≫ fY = fX) (hh : h ≫ fZ = fY)
    (x : Points (R := R) fX) :
    map h hh (map g hg x) = map (g ≫ h) (by rw [Category.assoc, hh, hg]) x := by
  apply Subtype.ext
  simp

/-- A monomorphism of schemes is injective on points. -/
theorem map_injective (g : X ⟶ Y) (hg : g ≫ fY = fX) [Mono g] :
    Function.Injective (map (R := R) g hg) := by
  intro x y h
  exact Subtype.ext ((cancel_mono g).mp (congrArg Subtype.val h))

/-- Applying a morphism to a chart point composes the chart with that morphism. -/
@[simp]
theorem map_chartPoint (g : X ⟶ Y) (hg : g ≫ fY = fX)
    (A : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X)
    (hi : i ≫ fX = Spec.algebraMap k A) (x : A →ₐ[k] R) :
    map g hg (chartPoint fX A i hi x) =
      chartPoint fY A (i ≫ g) (by rw [Category.assoc, hg, hi]) x := by
  apply Subtype.ext
  simp

/-- The image of an open immersion on points consists exactly of the morphisms whose
image lies in the open subscheme. This algebraic statement needs no locality assumption. -/
theorem mem_range_map_iff (g : X ⟶ Y) (hg : g ≫ fY = fX) [IsOpenImmersion g]
    (y : Points (R := R) fY) :
    y ∈ Set.range (map g hg) ↔ Set.range y.val ⊆ Set.range g := by
  constructor
  · rintro ⟨x, rfl⟩ z ⟨p, rfl⟩
    exact ⟨_, Scheme.Hom.comp_apply _ _ p⟩
  · intro hy
    refine ⟨⟨IsOpenImmersion.lift g y.val hy, ?_⟩, ?_⟩
    · rw [← hg, ← Category.assoc, IsOpenImmersion.lift_fac, y.property]
    · exact Subtype.ext (IsOpenImmersion.lift_fac g y.val hy)

/-- Over a local ring, a point belongs to an open subscheme exactly when the image of
the closed point of its source does. -/
theorem mem_range_map_iff_closedPoint [IsLocalRing R]
    (g : X ⟶ Y) (hg : g ≫ fY = fX) [IsOpenImmersion g] (y : Points (R := R) fY) :
    y ∈ Set.range (map g hg) ↔ y.val (IsLocalRing.closedPoint R) ∈ g.opensRange := by
  rw [mem_range_map_iff]
  constructor
  · exact fun h ↦ h (Set.mem_range_self _)
  · intro hy z hz
    obtain ⟨p, rfl⟩ := hz
    exact ((IsLocalRing.specializes_closedPoint p).map y.val.continuous).mem_open
      g.opensRange.isOpen hy

/-- On affine schemes the induced map on points is precomposition of algebra maps,
under the native equivalence `Spec.homEquivAlgHom`. -/
@[simp]
theorem map_homEquivAlgHom_symm {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (φ : A →ₐ[k] B) (x : B →ₐ[k] R) :
    map (Spec.map (CommRingCat.ofHom (φ : A →+* B)))
      (by rw [← Spec.map_comp]; congr 1; ext a; exact φ.commutes a)
      (Spec.homEquivAlgHom.symm x) = Spec.homEquivAlgHom.symm (x.comp φ) := by
  apply Subtype.ext
  simp only [map_val, Spec.homEquivAlgHom_symm_apply_val, AlgHom.toRingHom_eq_coe,
    AlgHom.comp_toRingHom, CommRingCat.ofHom_comp, Spec.map_comp]

variable [TopologicalSpace R] [ContinuousMul R] [IsLocalRing R] [IsOpenUnits R]

/-- A morphism over the base is continuous on points over a local topological ring
with open units and continuous inversion on the units. -/
@[continuity, fun_prop]
theorem continuous_map (g : X ⟶ Y) (hg : g ≫ fY = fX) :
    Continuous (map (R := R) g hg) := by
  refine (continuous_iff fX _).2 fun A i hi _ ↦ ?_
  have hcomp : map (R := R) g hg ∘ chartPoint fX A i hi =
      chartPoint fY A (i ≫ g) (by rw [Category.assoc, hg, hi]) := by
    funext x
    exact map_chartPoint g hg A i hi x
  rw [hcomp]
  exact continuous_chartPoint_of_isLocalRing fY A (i ≫ g) _

/-- An open immersion over the base induces an open embedding on points. -/
theorem isOpenEmbedding_of_isOpenImmersion (g : X ⟶ Y) (hg : g ≫ fY = fX)
    [IsOpenImmersion g] : IsOpenEmbedding (map (R := R) g hg) := by
  refine .of_continuous_injective_isOpenMap (continuous_map g hg) (map_injective g hg) ?_
  intro s hs
  refine isOpen_iff_forall_mem_open.2 fun y hy ↦ ?_
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨A, i, hi, hiOpen, z, rfl⟩ := exists_mem_range_chartPoint fX x
  have := hiOpen
  let hj : (i ≫ g) ≫ fY = Spec.algebraMap k A := by rw [Category.assoc, hg, hi]
  refine ⟨chartPoint fY A (i ≫ g) hj '' (chartPoint fX A i hi ⁻¹' s), ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨chartPoint fX A i hi a, ha, map_chartPoint g hg A i hi a⟩
  · exact (isOpenEmbedding_chartPoint fY A (i ≫ g) hj).isOpenMap _
      (hs.preimage (continuous_chartPoint fX A i hi))
  · exact ⟨z, hx, (map_chartPoint g hg A i hi z).symm⟩

end TauCeti.SchemePointTopology

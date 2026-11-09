/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.SpecOver
public import TauCeti.Topology.Algebra.PointTopology.Functoriality

/-!
# The chart topology on scheme-valued points

For a scheme `X` over `Spec k`, its `R`-points are morphisms `Spec R → X` over `Spec k`.
Give them the final topology for all affine open charts, whose point spaces carry the
coordinate-evaluation topology. This construction uses no finiteness assumptions.

The topology agrees with the evaluation topology when `X` is affine. If `R` is local,
every point belongs to an affine chart: an affine neighbourhood of the image of the closed
point contains the whole image of `Spec R`. These are the normalization and covering
properties needed to glue affine point spaces. This file does not assert that the charts
are open embeddings; that additional assertion requires open units and continuous inversion
on the units of `R`.

The affine comparison uses Mathlib's `Spec.homEquivAlgHom`, rather than another
algebraic dictionary between affine-scheme points and algebra homomorphisms. Morphisms
over the base act on points by composition; the chart injectivity and range criteria
follow from those for this general action.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Prop. 3.1 and its proof,
  pp. 3–4.
-/

public section

open CategoryTheory AlgebraicGeometry Topology
open scoped TauCeti.PointTopology

universe u

namespace TauCeti.SchemePointTopology

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The `R`-points of a scheme with structure morphism `f`, including the condition of
being a morphism over `Spec k`. -/
abbrev Points :=
  {x : Spec (.of R) ⟶ X // x ≫ f = Spec.algebraMap k R}

section Map

variable {Y Z : Scheme.{u}} {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)}
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

/-- A monomorphism of schemes is injective on points. -/
theorem map_injective (g : X ⟶ Y) (hg : g ≫ fY = fX) [Mono g] :
    Function.Injective (map (R := R) g hg) := by
  intro x y h
  exact Subtype.ext ((cancel_mono g).mp (congrArg Subtype.val h))

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

/-- Apply an affine chart to a point of its coordinate algebra. The equality `hi` says
that the chart is a morphism over the base. -/
noncomputable def chartPoint (A : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X)
    (hi : i ≫ f = Spec.algebraMap k A) (x : A →ₐ[k] R) : Points (R := R) f :=
  ⟨Spec.map (CommRingCat.ofHom x.toRingHom) ≫ i, by
    rw [Category.assoc, hi, ← Spec.map_comp]
    congr 1
    ext a
    exact x.commutes a⟩

/-- The underlying scheme morphism of a chart point is composition with the chart. -/
@[simp]
theorem chartPoint_val (A : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X)
    (hi : i ≫ f = Spec.algebraMap k A) (x : A →ₐ[k] R) :
    (chartPoint f A i hi x).val = Spec.map (CommRingCat.ofHom x.toRingHom) ≫ i :=
  (rfl)

/-- Applying a morphism to a chart point composes the chart with that morphism. -/
@[simp]
theorem map_chartPoint (g : X ⟶ Y) (hg : g ≫ fY = fX)
    (A : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X)
    (hi : i ≫ fX = Spec.algebraMap k A) (x : A →ₐ[k] R) :
    map g hg (chartPoint fX A i hi x) =
      chartPoint fY A (i ≫ g) (by rw [Category.assoc, hg, hi]) x := by
  apply Subtype.ext
  simp

end Map

/-- A chart point is the image of the corresponding affine-scheme point under the chart. -/
theorem chartPoint_eq_map_comp_homEquivAlgHom_symm (A : CommAlgCat.{u} k)
    (i : Spec (.of A) ⟶ X) (hi : i ≫ f = Spec.algebraMap k A) :
    chartPoint (R := R) f A i hi = map i hi ∘ Spec.homEquivAlgHom.symm := by
  funext x
  apply Subtype.ext
  simp only [Function.comp_apply, map_val, Spec.homEquivAlgHom_symm_apply_val, chartPoint_val]

/-- An affine chart is injective on points. -/
theorem chartPoint_injective (A : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X)
    (hi : i ≫ f = Spec.algebraMap k A) [Mono i] :
    Function.Injective (chartPoint (R := R) f A i hi) := by
  rw [chartPoint_eq_map_comp_homEquivAlgHom_symm]
  exact (map_injective i hi).comp Spec.homEquivAlgHom.symm.injective

/-- A scheme-valued point comes from an affine open chart exactly when its underlying
morphism has image in that chart. This criterion does not require a local coefficient ring. -/
theorem mem_range_chartPoint_iff (A : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X)
    (hi : i ≫ f = Spec.algebraMap k A) [IsOpenImmersion i] (x : Points (R := R) f) :
    x ∈ Set.range (chartPoint f A i hi) ↔ Set.range x.val ⊆ Set.range i := by
  rw [chartPoint_eq_map_comp_homEquivAlgHom_symm, EquivLike.range_comp, mem_range_map_iff]

/-- Over a local ring, membership in the points of an affine open chart can be tested
at the closed point of the source spectrum. -/
theorem mem_range_chartPoint_iff_closedPoint [IsLocalRing R]
    (A : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X)
    (hi : i ≫ f = Spec.algebraMap k A) [IsOpenImmersion i] (x : Points (R := R) f) :
    x ∈ Set.range (chartPoint f A i hi) ↔ x.val (IsLocalRing.closedPoint R) ∈ i.opensRange := by
  rw [chartPoint_eq_map_comp_homEquivAlgHom_symm, EquivLike.range_comp,
    mem_range_map_iff_closedPoint]

/-- Every point over a local ring factors through an affine open chart over the base.
In particular the affine chart point spaces cover the entire space of scheme-valued points. -/
theorem exists_mem_range_chartPoint [IsLocalRing R] (x : Points (R := R) f) :
    ∃ (A : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X)
      (hi : i ≫ f = Spec.algebraMap k A) (_ : IsOpenImmersion i),
      x ∈ Set.range (chartPoint f A i hi) := by
  obtain ⟨C, i, hi, p, hp⟩ := X.exists_Spec_apply_eq (x.val (IsLocalRing.closedPoint R))
  let α : k →+* C := (Spec.preimage (i ≫ f)).hom
  let : Algebra k C := α.toAlgebra
  have : IsOpenImmersion i := hi
  have hbase : i ≫ f = Spec.algebraMap k C := (Spec.map_preimage (i ≫ f)).symm
  refine ⟨CommAlgCat.of k C, i, hbase, hi, ?_⟩
  exact (mem_range_chartPoint_iff_closedPoint f (CommAlgCat.of k C) i hbase x).2 ⟨p, hp⟩

variable [TopologicalSpace R]

/-- The finest topology on scheme-valued points for which every affine open chart is
continuous from the coordinate-evaluation topology. No hypotheses on units are imposed
in the construction. -/
@[implicit_reducible]
noncomputable def topology : TopologicalSpace (Points (R := R) f) :=
  ⨆ (A : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X)
    (hi : i ≫ f = Spec.algebraMap k A) (_ : IsOpenImmersion i),
    TopologicalSpace.coinduced (chartPoint f A i hi) PointTopology.topology

attribute [scoped instance] topology

/-- The chart topology is the supremum of the topologies coinduced by affine open charts. -/
theorem topology_def : topology (R := R) f =
    ⨆ (A : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X)
      (hi : i ≫ f = Spec.algebraMap k A) (_ : IsOpenImmersion i),
      TopologicalSpace.coinduced (chartPoint f A i hi) PointTopology.topology :=
  (rfl)

/-- A set of scheme-valued points is open exactly when its preimage in every affine open
chart is open in the coordinate-evaluation topology. -/
theorem isOpen_iff (s : Set (Points (R := R) f)) :
    IsOpen s ↔ ∀ (A : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X)
      (hi : i ≫ f = Spec.algebraMap k A), IsOpenImmersion i →
        IsOpen (chartPoint f A i hi ⁻¹' s) := by
  simp only [isOpen_iSup_iff, isOpen_coinduced]

/-- Each affine open chart is continuous for the chart topology. -/
theorem continuous_chartPoint (A : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X)
    (hi : i ≫ f = Spec.algebraMap k A) [IsOpenImmersion i] :
    Continuous (chartPoint (R := R) f A i hi) :=
  continuous_iff_coinduced_le.2 <|
    le_iSup_of_le A <| le_iSup_of_le i <| le_iSup_of_le hi <| le_iSup_of_le inferInstance le_rfl

/-- Continuity out of the chart topology can be tested on all affine open charts. -/
theorem continuous_iff {Y : Type*} [TopologicalSpace Y] (g : Points (R := R) f → Y) :
    Continuous g ↔ ∀ (A : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X)
      (hi : i ≫ f = Spec.algebraMap k A), IsOpenImmersion i →
        Continuous (g ∘ chartPoint f A i hi) := by
  simp only [continuous_iSup_dom, continuous_coinduced_dom]

/-- On an affine scheme the chart topology is precisely the coordinate-evaluation topology.
The bijection is Mathlib's native equivalence between algebra maps and morphisms over the base. -/
noncomputable def affineHomeomorph (A : Type u) [CommRing A] [Algebra k A] :
    (A →ₐ[k] R) ≃ₜ Points (R := R) (Spec.algebraMap k A) where
  toEquiv := Spec.homEquivAlgHom.symm
  continuous_toFun := by
    have h := continuous_chartPoint (R := R) (Spec.algebraMap k A)
      (CommAlgCat.of k A) (𝟙 _) (by simp)
    convert h using 1
    funext x
    apply Subtype.ext
    simp only [chartPoint_val, Category.comp_id, Equiv.toFun_as_coe,
      Spec.homEquivAlgHom_symm_apply_val]
  continuous_invFun := by
    refine (continuous_iff _ _).2 fun B i hi _ ↦ ?_
    let φ : A →ₐ[k] B := Spec.homEquivAlgHom ⟨i, hi⟩
    have hφ : Spec.map (CommRingCat.ofHom φ.toRingHom) = i := by
      rw [← Spec.homEquivAlgHom_symm_apply_val, Equiv.symm_apply_apply]
    convert PointTopology.continuous_comap (R := R) φ using 1
    funext x
    apply Spec.homEquivAlgHom.symm.injective
    apply Subtype.ext
    dsimp only [Function.comp_apply, Equiv.invFun_as_coe, Equiv.symm_symm]
    simp only [Equiv.symm_apply_apply, chartPoint_val, Spec.homEquivAlgHom_symm_apply_val]
    rw [← hφ, ← Spec.map_comp]
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp]

/-- The affine homeomorphism sends an algebra map to its `Spec` morphism over the base. -/
@[simp]
theorem affineHomeomorph_apply (A : Type u) [CommRing A] [Algebra k A] (x : A →ₐ[k] R) :
    affineHomeomorph (k := k) (R := R) A x = Spec.homEquivAlgHom.symm x :=
  (rfl)

/-- The inverse affine comparison is the native `Spec.homEquivAlgHom`. -/
@[simp]
theorem affineHomeomorph_symm_apply (A : Type u) [CommRing A] [Algebra k A]
    (x : Points (R := R) (Spec.algebraMap k A)) :
    (affineHomeomorph (k := k) (R := R) A).symm x = Spec.homEquivAlgHom x :=
  (rfl)

end TauCeti.SchemePointTopology

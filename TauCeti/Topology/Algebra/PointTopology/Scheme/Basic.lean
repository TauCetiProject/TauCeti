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
algebraic dictionary between affine-scheme points and algebra homomorphisms. The chart
range criterion uses `TauCeti.AlgebraicGeometry.exists_spec_map_comp_eq_of_range_subset`.

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

/-- An affine chart is injective on points. -/
theorem chartPoint_injective (A : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X)
    (hi : i ≫ f = Spec.algebraMap k A) [Mono i] :
    Function.Injective (chartPoint (R := R) f A i hi) := by
  intro x y h
  have hxy := (cancel_mono i).mp (congrArg Subtype.val h)
  exact AlgHom.toRingHom_injective (CommRingCat.hom_ext_iff.mp (Spec.map_injective hxy))

/-- A scheme-valued point comes from an affine open chart exactly when its underlying
morphism has image in that chart. This criterion does not require a local coefficient ring. -/
theorem mem_range_chartPoint_iff (A : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X)
    (hi : i ≫ f = Spec.algebraMap k A) [IsOpenImmersion i] (x : Points (R := R) f) :
    x ∈ Set.range (chartPoint f A i hi) ↔ Set.range x.val ⊆ Set.range i := by
  constructor
  · rintro ⟨y, rfl⟩
    rintro _ ⟨p, rfl⟩
    exact ⟨_, Scheme.Hom.comp_apply _ _ p⟩
  · intro hx
    let : X.Over (Spec (.of k)) := ⟨f⟩
    have : i.IsOver (Spec (.of k)) := ⟨hi⟩
    have : x.val.IsOver (Spec (.of k)) := ⟨x.property⟩
    obtain ⟨φ, hφ⟩ := AlgebraicGeometry.exists_spec_map_comp_eq_of_range_subset (R := k) i x.val hx
    exact ⟨φ, Subtype.ext hφ⟩

/-- Over a local ring, membership in the points of an affine open chart can be tested
at the closed point of the source spectrum. -/
theorem mem_range_chartPoint_iff_closedPoint [IsLocalRing R]
    (A : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X)
    (hi : i ≫ f = Spec.algebraMap k A) [IsOpenImmersion i] (x : Points (R := R) f) :
    x ∈ Set.range (chartPoint f A i hi) ↔ x.val (IsLocalRing.closedPoint R) ∈ i.opensRange := by
  rw [mem_range_chartPoint_iff]
  constructor
  · exact fun h ↦ h (Set.mem_range_self _)
  · intro hx z hz
    obtain ⟨p, rfl⟩ := hz
    exact ((IsLocalRing.specializes_closedPoint p).map x.val.continuous).mem_open
      i.opensRange.isOpen hx

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

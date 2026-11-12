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
precomposition of algebra homomorphisms under the equivalence `Spec.homEquivAlgHom`,
as expressed by `map_homEquivAlgHom_symm`.

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

/-- Applying a morphism to a chart point composes the chart with that morphism. -/
@[simp]
theorem map_chartPoint (g : X ⟶ Y) (hg : g ≫ fY = fX)
    (A : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X)
    (hi : i ≫ fX = Spec.algebraMap k A) (x : A →ₐ[k] R) :
    map g hg (chartPoint fX A i hi x) =
      chartPoint fY A (i ≫ g) (by rw [Category.assoc, hg, hi]) x := by
  apply Subtype.ext
  simp

/-- A point of `X` whose image in `Y` lies in an affine open chart `Spec C ⟶ Y` lies in an affine
open chart `Spec A ⟶ X` mapping to it, through an algebra map `C → A`. -/
theorem exists_chartPoint_over [IsLocalRing R] (g : X ⟶ Y) (hg : g ≫ fY = fX)
    (C : CommAlgCat.{u} k) (iC : Spec (.of C) ⟶ Y) (hiC : iC ≫ fY = Spec.algebraMap k C)
    [IsOpenImmersion iC] (x : Points (R := R) fX)
    (hx : map g hg x ∈ Set.range (chartPoint fY C iC hiC)) :
    ∃ (A : CommAlgCat.{u} k) (iA : Spec (.of A) ⟶ X) (hiA : iA ≫ fX = Spec.algebraMap k A)
      (_ : IsOpenImmersion iA) (φ : C →ₐ[k] A),
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ iC = iA ≫ g ∧
        x ∈ Set.range (chartPoint fX A iA hiA) := by
  -- Work in the open subscheme `U = g⁻¹(Spec C)`, which contains the image of `x`.
  let U : X.Opens := g ⁻¹ᵁ iC.opensRange
  have hxU : x ∈ Set.range (map U.ι (rfl : U.ι ≫ fX = U.ι ≫ fX)) := by
    rw [mem_range_map_iff, Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    have h := (mem_range_chartPoint_iff fY C iC hiC _).1 hx ⟨p, rfl⟩
    simpa [U] using h
  obtain ⟨x', rfl⟩ := hxU
  obtain ⟨A, i, hi, _, a, rfl⟩ := exists_mem_range_chartPoint (U.ι ≫ fX) x'
  have hiA : (i ≫ U.ι) ≫ fX = Spec.algebraMap k A := by rw [Category.assoc, hi]
  have hrange : Set.range (i ≫ U.ι ≫ g) ⊆ Set.range iC := by
    rintro _ ⟨p, rfl⟩
    have h : U.ι (i p) ∈ U := by
      have h' : U.ι (i p) ∈ Set.range U.ι := Set.mem_range_self _
      rwa [Scheme.Opens.range_ι] at h'
    simpa [U] using h
  let : Y.Over (Spec (.of k)) := ⟨fY⟩
  have : iC.IsOver (Spec (.of k)) := ⟨hiC⟩
  have hbase : (i ≫ U.ι ≫ g) ≫ fY = Spec.algebraMap k A := by
    rw [Category.assoc, Category.assoc, hg, hi]
  have : (i ≫ U.ι ≫ g).IsOver (Spec (.of k)) := ⟨hbase⟩
  obtain ⟨φ, hφ, -⟩ :=
    AlgebraicGeometry.existsUnique_spec_map_comp_eq_of_range_subset (R := k) iC _ hrange
  refine ⟨A, i ≫ U.ι, hiA, inferInstance, φ, by rw [hφ, Category.assoc], a, ?_⟩
  rw [map_chartPoint]

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
  obtain ⟨A, i, hi, _, z, rfl⟩ := exists_mem_range_chartPoint fX x
  let hj : (i ≫ g) ≫ fY = Spec.algebraMap k A := by rw [Category.assoc, hg, hi]
  refine ⟨chartPoint fY A (i ≫ g) hj '' (chartPoint fX A i hi ⁻¹' s), ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨chartPoint fX A i hi a, ha, map_chartPoint g hg A i hi a⟩
  · exact (isOpenEmbedding_chartPoint fY A (i ≫ g) hj).isOpenMap _
      (hs.preimage (continuous_chartPoint fX A i hi))
  · exact ⟨z, hx, (map_chartPoint g hg A i hi z).symm⟩

end TauCeti.SchemePointTopology

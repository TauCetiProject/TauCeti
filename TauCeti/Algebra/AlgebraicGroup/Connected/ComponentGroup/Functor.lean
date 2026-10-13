/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Group
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.DominantPoints
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Functoriality of the component group

Over an algebraically closed field, a homomorphism of finite-type affine groups induces a
homomorphism of their component groups. Its underlying function is Mathlib's map on connected
components of the prime spectra. Compatibility with the rational component maps proves
multiplicativity and characterizes the induced homomorphism uniquely.

The construction defines a contravariant functor on finite-type commutative Hopf algebras.
An injective coordinate map induces a surjection on component groups. This gives the
right-surjectivity part of passing an exact sequence of affine groups to component groups;
it does not assert exactness at the middle term or injectivity at the left term.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37 and Section 5.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Sections 6.7 and 14.

The construction uses `Continuous.connectedComponentsMap`, the component-group structure
from `componentGroupPointsMulEquivConnectedComponents`, and the rational point-lifting theorem
`CommHopfAlgCat.mapPointsFunctor_app_surjective_of_injective`.
-/

public section

open CategoryTheory Opposite

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H K L : FiniteTypeCommHopfAlgCat.{u, u} k}

omit [IsAlgClosed k] in
/-- Precomposition of a rational point induces contraction of its prime-spectrum point.
Use with `rw`: simplification already expands `mapDomain` before this formula applies. -/
theorem rationalKernelPoint_mapDomain (f : H ⟶ K)
    (g : HopfAlgebra.points (R := k) (H := K) (CommAlgCat.of k k)) :
    rationalKernelPoint H (AlgHom.mapDomain (A := k) f.hom.hom g) =
      PrimeSpectrum.comap (f.hom.hom.toAlgHom : H →+* K) (rationalKernelPoint K g) := by
  rw [AlgHom.mapDomain_apply]
  exact (AlgHom.comap_kernelPoint g.ofConv f.hom.hom.toAlgHom).symm

/-- The map on connected components induced by an affine group homomorphism is multiplicative.
Coordinate arrows reverse, so `f : H ⟶ K` induces a map from the components of `Spec K` to those
of `Spec H`. -/
noncomputable def mapComponentGroup (f : H ⟶ K) :
    ConnectedComponents (PrimeSpectrum K) →* ConnectedComponents (PrimeSpectrum H) where
  toFun := (PrimeSpectrum.continuous_comap
    (f.hom.hom.toAlgHom : H →+* K)).connectedComponentsMap
  map_one' := by
    rw [← map_one (rationalComponentMap K), rationalComponentMap_apply K,
      Continuous.connectedComponentsMap_mk]
    rw [← rationalKernelPoint_mapDomain f, map_one, rationalKernelPoint_one,
      rationalKernelPoint_one_component]
  map_mul' x y := by
    obtain ⟨g, rfl⟩ := rationalComponentMap_surjective K x
    obtain ⟨h, rfl⟩ := rationalComponentMap_surjective K y
    rw [← map_mul (rationalComponentMap K), rationalComponentMap_apply K,
      rationalComponentMap_apply K g, rationalComponentMap_apply K h]
    simp only [Continuous.connectedComponentsMap_mk, ← rationalKernelPoint_mapDomain f,
      map_mul, rationalKernelPoint_mul_component H]

/-- On a represented component, the component-group map is the map of prime spectra. -/
@[simp]
theorem mapComponentGroup_mk (f : H ⟶ K) (x : PrimeSpectrum K) :
    mapComponentGroup f (ConnectedComponents.mk x) =
      ConnectedComponents.mk (PrimeSpectrum.comap (f.hom.hom.toAlgHom : H →+* K) x) :=
  Continuous.connectedComponentsMap_mk
    (PrimeSpectrum.continuous_comap (f.hom.hom.toAlgHom : H →+* K)) x

/-- The rational component maps commute with an affine group homomorphism. -/
@[simp]
theorem mapComponentGroup_rationalComponentMap (f : H ⟶ K)
    (g : HopfAlgebra.points (R := k) (H := K) (CommAlgCat.of k k)) :
    mapComponentGroup f (rationalComponentMap K g) =
      rationalComponentMap H
        (AlgHom.mapDomain (A := k) f.hom.hom g) := by
  rw [rationalComponentMap_apply K, mapComponentGroup_mk,
    rationalComponentMap_apply H]
  rw [rationalKernelPoint_mapDomain]

/-- The induced component-group homomorphism is uniquely characterized by compatibility
with the rational component maps. -/
theorem mapComponentGroup_unique (f : H ⟶ K)
    (m : ConnectedComponents (PrimeSpectrum K) →* ConnectedComponents (PrimeSpectrum H))
    (hm : ∀ g : HopfAlgebra.points (R := k) (H := K) (CommAlgCat.of k k),
      m (rationalComponentMap K g) = rationalComponentMap H
        (AlgHom.mapDomain (A := k) f.hom.hom g)) :
    m = mapComponentGroup f := by
  ext x
  obtain ⟨g, rfl⟩ := rationalComponentMap_surjective K x
  exact (hm g).trans (mapComponentGroup_rationalComponentMap f g).symm

/-- The identity coordinate morphism induces the identity on component groups. -/
@[simp]
theorem mapComponentGroup_id (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    mapComponentGroup (𝟙 H) = MonoidHom.id (ConnectedComponents (PrimeSpectrum H)) := by
  symm
  apply mapComponentGroup_unique
  intro g
  have hid : (𝟙 H : H ⟶ H).hom.hom = BialgHom.id k H := toBialgHom_id
  rw [MonoidHom.id_apply, hid, AlgHom.mapDomain_id, MonoidHom.id_apply]

/-- Composition of coordinate morphisms induces reverse composition on component groups. -/
@[simp]
theorem mapComponentGroup_comp (f : H ⟶ K) (g : K ⟶ L) :
    mapComponentGroup (f ≫ g) = (mapComponentGroup f).comp (mapComponentGroup g) := by
  symm
  apply mapComponentGroup_unique
  intro p
  rw [MonoidHom.comp_apply, mapComponentGroup_rationalComponentMap g,
    mapComponentGroup_rationalComponentMap f]
  simp only [ObjectProperty.FullSubcategory.comp_hom, _root_.CommHopfAlgCat.hom_comp,
    AlgHom.mapDomain_comp, MonoidHom.comp_apply]

/-- The component group, contravariantly functorial in finite-type coordinate Hopf algebras. -/
noncomputable def componentGroupFunctor :
    (FiniteTypeCommHopfAlgCat.{u, u} k)ᵒᵖ ⥤ GrpCat.{u} where
  obj H := GrpCat.of (ConnectedComponents (PrimeSpectrum H.unop))
  map f := GrpCat.ofHom (mapComponentGroup f.unop)
  map_id H := by
    apply GrpCat.hom_ext
    exact mapComponentGroup_id H.unop
  map_comp f g := by
    apply GrpCat.hom_ext
    exact mapComponentGroup_comp g.unop f.unop

/-- The component-group functor sends a coordinate Hopf algebra to the group of connected
components of its prime spectrum. -/
@[simp]
theorem componentGroupFunctor_obj (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (componentGroupFunctor (k := k)).obj (op H) =
      GrpCat.of (ConnectedComponents (PrimeSpectrum H)) :=
  (rfl)

/-- The component-group functor acts on morphisms by the induced component homomorphism. -/
@[simp]
theorem componentGroupFunctor_map (f : H ⟶ K) :
    (componentGroupFunctor (k := k)).map f.op ≫ eqToHom (componentGroupFunctor_obj H) =
      eqToHom (componentGroupFunctor_obj K) ≫ GrpCat.ofHom (mapComponentGroup f) :=
  (rfl)

/-- An injective coordinate morphism of finite-type affine groups is surjective on component
groups. In particular, this applies to faithfully flat group homomorphisms. Neither group
is required to be smooth or reduced. -/
theorem mapComponentGroup_surjective_of_injective (f : H ⟶ K)
    (hf : Function.Injective f.hom.hom) :
    Function.Surjective (mapComponentGroup f) := by
  intro x
  obtain ⟨p, rfl⟩ := rationalComponentMap_surjective H x
  obtain ⟨q, hq⟩ := CommHopfAlgCat.mapPointsFunctor_app_surjective_of_injective k f.hom hf p
  let q' : HopfAlgebra.points (R := k) (H := K) (CommAlgCat.of k k) := q
  -- `mapPointsFunctor` is constructed with `mapDomain`; specify the rational-point carrier
  -- here because its functor-object spelling does not rewrite at implicit transparency.
  have hq' : AlgHom.mapDomain (A := k) f.hom.hom q' = p := hq
  refine ⟨rationalComponentMap K q', ?_⟩
  rw [mapComponentGroup_rationalComponentMap]
  exact congrArg (rationalComponentMap H) hq'

end TauCeti.FiniteTypeCommHopfAlgCat

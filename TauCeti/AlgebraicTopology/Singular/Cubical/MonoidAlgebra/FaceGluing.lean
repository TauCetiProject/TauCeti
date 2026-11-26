/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Dense
public import TauCeti.AlgebraicTopology.Singular.Cubical.Kunneth.Pair
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Relative.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.RepresentingChainSystem
public import TauCeti.AlgebraicTopology.Singular.Cubical.Relative
public import TauCeti.Topology.ContinuousMap.CodRestrict

/-!
# Representing cycles glued from faces

Let `A` be a compact topological manifold of dimension `m`, such as the boundary of a compact
manifold with corners, and let `(Uᵢ)` be a family of subsets of `A` whose union is dense, such as
the interiors of its faces. A class of the cubical homology `Hₘ(A)` is determined by its images in
the relative groups `Hₘ(A, A ∖ Uᵢ)` (`TauCeti.cubicalHomology_ext_of_dense_iUnion`), the cubical
form of `TauCeti.singularHomology_ext_of_dense_iUnion`.

At the level of chains this gives a criterion for an `m`-cycle `z` of `A` to represent a class
`ν ∈ Hₘ(A)` (`TauCeti.isRepresentingCycle_of_forall_isCubicalRepresentative`). It suffices that for
each `i` some chain `cᵢ`, agreeing with `z` up to a chain of `A ∖ Uᵢ`, is at every point `a` of
`Uᵢ` a relative cycle of `(A, A ∖ {a})` representing the image of `ν` in the local homology: the
relative class of a cycle is that of any chain agreeing with it modulo the subspace
(`TopPair.homologyMap_homologyπ_eq_of_isCubicalRepresentative`), and the classes are compared
point by point, the points of the `Uᵢ` forming a dense set. Nothing is asked of `z` near the
points outside the `Uᵢ`.

When `z` is a finite sum of chains `cᵢ`, each supported in a closed piece `Fᵢ` (a face of `A`),
and `Uᵢ` meets no other piece, the chain agreeing with `z` modulo `A ∖ Uᵢ` is `cᵢ` itself
(`TauCeti.isRepresentingCycle_of_eq_sum`). This is the form of the gluing condition of
representing chain systems (`TauCeti.TwistingChainSystem.exists_isRepresenting`) for fundamental
classes of manifolds with corners. There `A` is the boundary of a compactified trajectory space
`M`, `ν` is the image of the fundamental class of `M` relative to `A` under the connecting
morphism, and `z` is the signed sum of the products of fundamental chains of the
lower-dimensional trajectory spaces, one for each boundary face. The condition is then checked on
the interior of each face separately, comparing the product chain of the face with `ν`; the
corners, where several faces meet, need not be examined.

What remains of the gluing condition is homological and local to the faces
(`TauCeti.TwistingChainSystem.exists_isRepresenting_of_faces`). Suppose that the composition map
`ι x z y : M x z × M z y → M x y` lands in the boundary `A x y`, that it carries the boundary
`A x z × M z y ∪ M x z × A z y` of the product off the interior `U x z y` of its face, and that the
face of every other `z'` misses `U x z y`. A chain representing `μ x z` crossed with one
representing `μ z y` is then, for every point `a` of `U x z y`, a relative cycle of
`(A x y, A x y ∖ {a})`, whose class is the cross product of the two classes pushed forward along
`ι x z y` (`TopPair.IsCubicalRepresentative.crossProduct`). So the gluing condition holds, and a
representing chain system exists, as soon as at each point of the interior of each face this
pushed-forward cross product is `(-1) ^ (ind x - ind z)` times the image of `∂ μ x y` in the local
homology. For the fundamental classes of compactified trajectory spaces this compares the boundary
orientation of each face with its product orientation; when `1` is the only unit of the
coefficients both sides are the unique generator of the local homology, and the condition holds
(`TauCeti.TwistingChainSystem.exists_isRepresenting_of_subsingleton_units`).

The same argument applies to continuation chain systems
(`TauCeti.ContinuationChainSystem.exists_isRepresenting_of_faces`). The boundary of a space
`N x y` of continuation trajectories has two kinds of faces, `M x z × N z y` and
`N x w × M' w y`, and the continuation sum is the sum of their face chains, with the sign
`(-1) ^ (ind x - indQ w - 1)` on the second kind; the twisting chain systems of the two ends are
fixed and represent their own classes.

It applies as well to parametrized chain systems
(`TauCeti.ParametrizedChainSystem.exists_isRepresenting_of_faces`), which join two continuation
chain systems. The boundary of a space `H x y` of trajectories of a one-parameter family of
homotopies has, besides the faces `M x z × H z y` and `H x w × M' w y`, the two ends `N₀ x y` and
`N₁ x y`, the spaces of continuation trajectories of the homotopies at the two ends of the family.
The parametrized sum is the sum of their face chains, with the sign `-1` on the end `N₀ x y` and
the signs `(-1) ^ (ind x - ind z)` and `(-1) ^ (ind x - indQ w)` on the two kinds of faces; the
twisting and continuation chain systems are fixed and represent their own classes.

## Main results

* `TauCeti.isRepresentingCycle_of_forall_isCubicalRepresentative`: a cycle of `A` which, modulo
  `A ∖ Uᵢ`, agrees for each `i` with a chain representing the image of `ν` at every point of `Uᵢ`,
  represents `ν`.
* `TauCeti.isRepresentingCycle_of_eq_sum`: a sum of chains supported in pieces `Fᵢ`, each
  representing the image of `ν` at every point of `Uᵢ`, represents `ν`.
* `TauCeti.TwistingChainSystem.exists_isRepresenting_of_faces`: a twisting chain system
  representing classes `μ` of spaces whose boundaries are compact manifolds glued from faces exists
  when, at each point of the interior of each face, the image of `∂ μ x y` is the signed cross
  product of the classes of the two factors.
* `TauCeti.ContinuationChainSystem.exists_isRepresenting_of_faces`: the same for continuation
  chain systems between two representing twisting chain systems.
* `TauCeti.ParametrizedChainSystem.exists_isRepresenting_of_faces`: the same for parametrized
  chain systems between two representing continuation chain systems.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Annals of
  Mathematics 166 (2007), Appendix A, the representing chain systems of compactified trajectory
  spaces.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 5, the twisting
  cocycle, and Chapter 6, the continuation morphisms between twisting cocycles and the homotopies
  between them.
-/

public section

noncomputable section

open CategoryTheory Limits Module

universe u

namespace TauCeti

variable {k : Type u} [CommRing k] {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {X : TopCat.{u}} {A : Set X}

/-- **A cycle glued from relative cycles over a dense family of pieces represents their class.**
Let `A` be a compact `m`-manifold, `ν` a class of the cubical homology `Hₘ(A)`, and `(Uᵢ)` a family
of subsets of `A` with dense union. Let `z` be an `m`-cycle of `A` such that, for each `i`, some
chain `cᵢ` agreeing with `z` up to a chain supported in `A ∖ Uᵢ` represents the image of `ν` in
the local homology `Hₘ(A, A ∖ {a})` at every point `a` of `Uᵢ`. Then `z`, pushed forward to `X`,
represents `ν`. -/
theorem isRepresentingCycle_of_forall_isCubicalRepresentative [T2Space A] [CompactSpace A]
    [ChartedSpace E A] [FiniteDimensional ℝ E] {m : ℕ} (hm : finrank ℝ E = m)
    (z : ((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).cycles m)
    {ν : ((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).homology m}
    {ι : Type*} {U : ι → Set (TopPair.ofSubset A).snd} (hU : Dense (⋃ i, U i))
    (c : ι → NormalizedCubicalChain (TopPair.ofSubset A).snd k m)
    (hc : ∀ i, ∀ a ∈ U i,
      (TopPair.ofSubset ({a}ᶜ : Set (TopPair.ofSubset A).snd)).IsCubicalRepresentative k (c i)
        ((HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
          (TopPair.ofSubset ({a}ᶜ : Set (TopPair.ofSubset A).snd)).map)) m).hom ν))
    (hzc : ∀ i, normalizedCubicalChainComplexXEquiv _ m
        ((((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).iCycles m).hom z) -
          c i ∈ NormalizedCubicalChain.supportedIn k (U i)ᶜ m) :
    IsRepresentingCycle (cubicalChainLof X k m (NormalizedCubicalChain.map k
      (TopPair.ofSubset A).map.hom m
        ((((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).iCycles m).hom z)))
      ν := by
  -- The space `(TopPair.ofSubset A).snd` is `A`, with the same instances.
  have : T2Space (TopPair.ofSubset A).snd := inferInstanceAs (T2Space A)
  have : CompactSpace (TopPair.ofSubset A).snd := inferInstanceAs (CompactSpace A)
  let : ChartedSpace E (TopPair.ofSubset A).snd := inferInstanceAs (ChartedSpace E A)
  -- The class of `z` is compared with `ν` at each point `a` of each `Uᵢ`, the points `{a}` having
  -- the dense union `⋃ i, Uᵢ`.
  refine (isRepresentingCycle_iff _ ν).2 ⟨z, rfl,
    cubicalHomology_ext_of_dense_iUnion (Y := (TopPair.ofSubset A).snd) (E := E) hm
      (U := fun p : Σ i, U i ↦ {(p.2 : (TopPair.ofSubset A).snd)})
      (by simpa only [Set.iUnion_sigma, Set.iUnion_coe_set, Set.biUnion_of_singleton] using hU)
      fun ⟨i, a, ha⟩ ↦ TopPair.homologyMap_homologyπ_eq_of_isCubicalRepresentative k
        (TopPair.ofSubset {a}ᶜ) z (hc i a ha) ?_⟩
  -- The embedding `(TopPair.ofSubset S).map` of Mathlib's `TopPair.ofSubset` is, by definition,
  -- `TopCat.ofHom` of the subtype inclusion `ContinuousMap.subtypeVal S` through which
  -- `NormalizedCubicalChain.supportedIn` is defined.
  refine (NormalizedCubicalChain.supportedIn_def k _ m).le ?_
  exact NormalizedCubicalChain.supportedIn_mono k
    (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 ha)) m (hzc i)

/-- **A sum of face chains represents the class they represent face by face.** Let `A` be a
compact `m`-manifold, `ν` a class of the cubical homology `Hₘ(A)`, and let `z` be an `m`-cycle of
`A` which is a finite sum of chains `cᵢ`, each supported in a set `Fᵢ` (a face of `A`). Let `Uᵢ` be
sets with dense union (the interiors of the faces) such that `Uᵢ` meets no other face `Fⱼ`,
`j ≠ i`. If each `cᵢ` represents the image of `ν` in the local homology `Hₘ(A, A ∖ {a})` at every
point `a` of `Uᵢ`, then `z`, pushed forward to `X`, represents `ν`.

For the boundary `A` of a compactified trajectory space, with `ν` the image of its fundamental
class relative to `A` and `z` the signed sum of the products of fundamental chains of its faces,
this is the gluing condition of `TauCeti.TwistingChainSystem.exists_isRepresenting`: it is checked
on the interior of each face separately, with nothing to check at the corners. -/
theorem isRepresentingCycle_of_eq_sum [T2Space A] [CompactSpace A] [ChartedSpace E A]
    [FiniteDimensional ℝ E] {m : ℕ} (hm : finrank ℝ E = m)
    (z : ((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).cycles m)
    {ν : ((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).homology m}
    {ι : Type*} [Fintype ι] (c : ι → NormalizedCubicalChain (TopPair.ofSubset A).snd k m)
    (hz : normalizedCubicalChainComplexXEquiv _ m
        ((((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).iCycles m).hom z) =
      ∑ i, c i)
    {F U : ι → Set (TopPair.ofSubset A).snd}
    (hcF : ∀ i, c i ∈ NormalizedCubicalChain.supportedIn k (F i) m)
    (hFU : ∀ i j, j ≠ i → Disjoint (F j) (U i)) (hU : Dense (⋃ i, U i))
    (hc : ∀ i, ∀ a ∈ U i,
      (TopPair.ofSubset ({a}ᶜ : Set (TopPair.ofSubset A).snd)).IsCubicalRepresentative k (c i)
        ((HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
          (TopPair.ofSubset ({a}ᶜ : Set (TopPair.ofSubset A).snd)).map)) m).hom ν)) :
    IsRepresentingCycle (cubicalChainLof X k m (NormalizedCubicalChain.map k
      (TopPair.ofSubset A).map.hom m
        ((((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).iCycles m).hom z)))
      ν := by
  classical
  refine isRepresentingCycle_of_forall_isCubicalRepresentative hm z hU c hc fun i ↦ ?_
  -- Off the face `i`, the cycle is the sum of the other faces, which avoid `Uᵢ`.
  rw [hz, ← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_sub_cancel_right]
  refine Submodule.sum_mem _ fun j hj ↦ ?_
  exact NormalizedCubicalChain.supportedIn_mono k
    (Set.subset_compl_iff_disjoint_right.2 (hFU i j (Finset.ne_of_mem_erase hj))) m (hcF j)

/-- The form of `isRepresentingCycle_of_eq_sum` used by chain systems: a sum of face chains of `A`
whose push-forward to `X` is a cycle there represents the class it represents face by face. -/
private theorem isRepresentingCycle_map_sum [T2Space A] [CompactSpace A] [ChartedSpace E A]
    [FiniteDimensional ℝ E] {m : ℕ} (hm : finrank ℝ E = m)
    {ν : ((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).homology m}
    {ι : Type*} [Fintype ι] (c : ι → NormalizedCubicalChain (TopPair.ofSubset A).snd k m)
    (hcyc : cubicalChainDifferential X k (cubicalChainLof X k m
      (NormalizedCubicalChain.map k (ContinuousMap.subtypeVal A) m (∑ i, c i))) = 0)
    {F U : ι → Set (TopPair.ofSubset A).snd}
    (hcF : ∀ i, c i ∈ NormalizedCubicalChain.supportedIn k (F i) m)
    (hFU : ∀ i j, j ≠ i → Disjoint (F j) (U i)) (hU : Dense (⋃ i, U i))
    (hc : ∀ i, ∀ a ∈ U i,
      (TopPair.ofSubset ({a}ᶜ : Set (TopPair.ofSubset A).snd)).IsCubicalRepresentative k (c i)
        ((HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
          (TopPair.ofSubset ({a}ᶜ : Set (TopPair.ofSubset A).snd)).map)) m).hom ν)) :
    IsRepresentingCycle (cubicalChainLof X k m
      (NormalizedCubicalChain.map k (ContinuousMap.subtypeVal A) m (∑ i, c i))) ν := by
  -- The sum is a cycle of `A`, since the push-forward along the inclusion is injective.
  have h : cubicalChainDifferential A k (cubicalChainLof _ k _ (∑ i, c i)) = 0 := by
    refine cubicalChainSumMap_injective (f := ContinuousMap.subtypeVal A) Subtype.val_injective ?_
    rwa [map_zero, ← cubicalChainDifferential_cubicalChainSumMap, cubicalChainSumMap_lof]
  obtain ⟨z, hz⟩ := exists_iCycles_eq_of_cubicalChainDifferential_lof_eq_zero _ h
  rw [← hz]
  exact isRepresentingCycle_of_eq_sum hm z c hz hcF hFU hU hc

end TauCeti

namespace TauCeti

open MonoidalCategory NormalizedCubicalChain
open scoped TensorProduct

variable {k : Type u} [CommRing k] {P : Type*} [Fintype P] {ind : P → ℤ} {M : P → P → TopCat.{u}}
  {ι : ∀ x y z, C(M x y × M y z, M x z)} {A : ∀ x y, Set (M x y)}
  {μ : ∀ x y, ((TopPair.ofSubset (A x y)).cubicalChainComplex k).homology (ind x - ind y - 1).toNat}

/-- A face chain represents the local class prescribed on its face: if `a` and `b` represent
classes `μ₁` and `μ₂` of the pairs `(X₁, A₁)` and `(X₂, A₂)`, and the face map `g` carries the
boundary of the product pair off the point `z`, then the push-forward along `g` of `a × b`
represents the image of `μ₁ × μ₂` in the local homology at `z`. -/
private theorem isCubicalRepresentative_map_crossProduct {X₁ X₂ : TopCat.{u}} {A₁ : Set X₁}
    {A₂ : Set X₂} {Z : Type u} [TopologicalSpace Z] {p q n : ℕ} (hpq : p + q = n)
    {a : NormalizedCubicalChain X₁ k p}
    {μ₁ : ((TopPair.ofSubset A₁).cubicalChainComplex k).homology p}
    (ha : (TopPair.ofSubset A₁).IsCubicalRepresentative k a μ₁)
    {b : NormalizedCubicalChain X₂ k q}
    {μ₂ : ((TopPair.ofSubset A₂).cubicalChainComplex k).homology q}
    (hb : (TopPair.ofSubset A₂).IsCubicalRepresentative k b μ₂) (g : C(X₁ × X₂, Z)) {z : Z}
    (hg : Set.MapsTo
      (TopCat.ofHom (X := ↑((TopPair.ofSubset A₁).fst ⊗ (TopPair.ofSubset A₂).fst)) g)
      ((TopPair.ofSubset A₁).prodSubspace (TopPair.ofSubset A₂)) ({z}ᶜ : Set Z)) :
    (TopPair.ofSubset (X := TopCat.of Z) {z}ᶜ).IsCubicalRepresentative k
      (map k g n (cast k hpq (crossProduct _ _ k _ _ a b)))
      ((HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
          (TopPair.ofSubsetMap _ hg)) n).hom
        ((HomologicalComplex.homologyMap
          ((TopPair.ofSubset A₁).cubicalChainComplexProdComparison k (TopPair.ofSubset A₂)) n).hom
          ((GradedObject.Monoidal.ιTensorObj _ _ _ _ _ hpq ≫
            cubicalHomologyKunnethPair k _ _ _).hom (μ₁ ⊗ₜ μ₂)))) := by
  obtain ⟨r, hr, hcl⟩ := (TopPair.isCubicalRepresentative_iff _ _).1
    ((ha.crossProduct hpq hb).map (TopPair.ofSubsetMap _ hg))
  rw [TopPair.ofSubsetMap_fst] at hr
  exact (TopPair.isCubicalRepresentative_iff _ _).2 ⟨r, hr, hcl⟩

/-- A signed face chain represents the local class prescribed on its face: if the push-forward of
`μ₁ × μ₂` is `ε • v` for a sign `ε`, then `ε` times the push-forward of `a × b` represents `v`. -/
private theorem isCubicalRepresentative_zsmul_map_crossProduct {X₁ X₂ : TopCat.{u}} {A₁ : Set X₁}
    {A₂ : Set X₂} {Z : Type u} [TopologicalSpace Z] {p q n : ℕ} (hpq : p + q = n)
    {a : NormalizedCubicalChain X₁ k p}
    {μ₁ : ((TopPair.ofSubset A₁).cubicalChainComplex k).homology p}
    (ha : (TopPair.ofSubset A₁).IsCubicalRepresentative k a μ₁)
    {b : NormalizedCubicalChain X₂ k q}
    {μ₂ : ((TopPair.ofSubset A₂).cubicalChainComplex k).homology q}
    (hb : (TopPair.ofSubset A₂).IsCubicalRepresentative k b μ₂) (g : C(X₁ × X₂, Z)) {z : Z}
    (hg : Set.MapsTo
      (TopCat.ofHom (X := ↑((TopPair.ofSubset A₁).fst ⊗ (TopPair.ofSubset A₂).fst)) g)
      ((TopPair.ofSubset A₁).prodSubspace (TopPair.ofSubset A₂)) ({z}ᶜ : Set Z))
    (ε : ℤˣ) {v : ((TopPair.ofSubset (X := TopCat.of Z) {z}ᶜ).cubicalChainComplex k).homology n}
    (hv : (HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
          (TopPair.ofSubsetMap _ hg)) n).hom
        ((HomologicalComplex.homologyMap
          ((TopPair.ofSubset A₁).cubicalChainComplexProdComparison k (TopPair.ofSubset A₂)) n).hom
          ((GradedObject.Monoidal.ιTensorObj _ _ _ _ _ hpq ≫
            cubicalHomologyKunnethPair k _ _ _).hom (μ₁ ⊗ₜ μ₂))) = ε • v) :
    (TopPair.ofSubset (X := TopCat.of Z) {z}ᶜ).IsCubicalRepresentative k
      (ε • map k g n (cast k hpq (crossProduct _ _ k _ _ a b))) v := by
  obtain ⟨r, hr, hcl⟩ := (TopPair.isCubicalRepresentative_iff _ _).1
    ((isCubicalRepresentative_map_crossProduct hpq ha hb g hg).zsmul (ε : ℤ))
  refine (TopPair.isCubicalRepresentative_iff _ _).2 ⟨r, hr, hcl.trans ?_⟩
  rw [hv, ← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]

/-- The pairing along `f` of the homogeneous chains `a` and `b` is the push-forward of `a × b`
through any subspace `B` containing the image of `f`. -/
private theorem cubicalChainSumPairing_lof_lof_eq_subtypeVal {X₁ X₂ Z : Type*}
    [TopologicalSpace X₁] [TopologicalSpace X₂] [TopologicalSpace Z] (f : C(X₁ × X₂, Z))
    (B : Set Z) (hf : ∀ p, f p ∈ B) {p q n : ℕ} (hpq : p + q = n)
    (a : NormalizedCubicalChain X₁ k p) (b : NormalizedCubicalChain X₂ k q) :
    cubicalChainSumPairing k f (cubicalChainLof _ k _ a) (cubicalChainLof _ k _ b) =
      cubicalChainLof Z k n (map k (ContinuousMap.subtypeVal B) n
        (map k (f.codRestrict B hf) n (cast k hpq (crossProduct _ _ k _ _ a b)))) := by
  rw [cubicalChainSumPairing_lof_lof, ← LinearMap.comp_apply (map k (ContinuousMap.subtypeVal B) n),
    ← map_comp, ContinuousMap.subtypeVal_comp_codRestrict, map_cast, cubicalChainLof_cast]

/-- The twisting sum of `(x, y)` of chains `s` with representatives `a z` of `s x z` and `b z` of
`s z y` is the push-forward from the boundary `A x y` of the sum over the faces of the signed cross
products `a z × b z`, carried to `A x y` by the composition maps. -/
private theorem twistingChainSum_eq_sum_face {s : ∀ x y, normalizedCubicalChainAlgebra (M x y) k}
    (hs : ∀ x y, s x y ∈ cubicalChainGrading (M x y) k (ind y - ind x + 1)) {x y : P}
    (hιA : ∀ z : {z // ind y < ind z ∧ ind z < ind x}, ∀ p, ι x z.val y p ∈ A x y)
    (a : ∀ z : {z // ind y < ind z ∧ ind z < ind x},
      NormalizedCubicalChain (M x z.val) k (ind x - ind z.val - 1).toNat)
    (ha : ∀ z, cubicalChainLof _ k _ (a z) = s x z.val)
    (b : ∀ z : {z // ind y < ind z ∧ ind z < ind x},
      NormalizedCubicalChain (M z.val y) k (ind z.val - ind y - 1).toNat)
    (hb : ∀ z, cubicalChainLof _ k _ (b z) = s z.val y) {n : ℕ}
    (hpq : ∀ z : {z // ind y < ind z ∧ ind z < ind x},
      (ind x - ind z.val - 1).toNat + (ind z.val - ind y - 1).toNat = n) :
    twistingChainSum ind ι k s x y = cubicalChainLof (M x y) k n
      (map k (ContinuousMap.subtypeVal (A x y)) n (∑ z, (ind x - ind z.val).negOnePow •
        map k ((ι x z.val y).codRestrict (A x y) (hιA z)) n
          (cast k (hpq z) (crossProduct _ _ k _ _ (a z) (b z))))) := by
  rw [twistingChainSum_eq_sum_subtype hs, map_sum, map_sum]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [← ha z, ← hb z, cubicalChainSumPairing_lof_lof_eq_subtypeVal _ _ (hιA z) (hpq z),
    map_zsmul_unit, map_zsmul_unit]

/-- **Representing chain systems from a face-by-face condition.** Let `μ x y` be classes of the
relative homology `H_{ind x - ind y - 1}(M x y, A x y)`. Suppose that:

* each boundary `A x y` is a compact Hausdorff space charted on a finite-dimensional real normed
  space `E x y`, of dimension `ind x - ind y - 2` whenever `ind x - ind y ≥ 2`, so that `A x y`
  is then a closed topological manifold of that dimension;
* the composition maps `ι x z y : M x z × M z y → M x y` are associative and, for `z` strictly
  between `y` and `x` in index, land in `A x y`;
* the sets `U x z y`, the interiors of the faces, are together dense in `A x y`, the face of every
  other `z'` strictly between `y` and `x` misses `U x z y`, and `ι x z y` carries
  `A x z × M z y ∪ M x z × A z y` off `U x z y`;
* at each point `a` of the interior `U x z y` of each face, the cross product of `μ x z` and
  `μ z y`, pushed forward along `ι x z y` to the local homology `H(A x y, A x y ∖ {a})`, is
  `(-1) ^ (ind x - ind z)` times the image of the boundary `∂ μ x y ∈ H(A x y)`.

Then some twisting chain system represents the classes `μ`. For the fundamental classes rel
boundary of compactified trajectory spaces, the last condition compares the boundary orientation
of each face with its product orientation; no condition is imposed at the corners. -/
theorem TwistingChainSystem.exists_isRepresenting_of_faces
    {E : P → P → Type u} [∀ x y, NormedAddCommGroup (E x y)] [∀ x y, NormedSpace ℝ (E x y)]
    [∀ x y, FiniteDimensional ℝ (E x y)] [∀ x y, T2Space (A x y)] [∀ x y, CompactSpace (A x y)]
    [∀ x y, ChartedSpace (E x y) (A x y)]
    (hE : ∀ x y, ind y + 1 < ind x → Module.finrank ℝ (E x y) = (ind x - ind y - 2).toNat)
    (hι : ∀ x w z y (a : M x w) (b : M w z) (c : M z y),
      ι x z y (ι x w z (a, b), c) = ι x w y (a, ι w z y (b, c)))
    (hιA : ∀ x z y, ind y < ind z → ind z < ind x → ∀ p, ι x z y p ∈ A x y)
    (U : ∀ x, P → ∀ y, Set (M x y))
    (hU : ∀ x y, ind y + 1 < ind x →
      Dense {a : A x y | ∃ z, ind y < ind z ∧ ind z < ind x ∧ (a : M x y) ∈ U x z y})
    (hUι : ∀ x z z' y, ind y < ind z' → ind z' < ind x → z' ≠ z →
      Disjoint (Set.range (ι x z' y)) (U x z y))
    (hUA : ∀ x z y (hyz : ind y < ind z) (hzx : ind z < ind x),
      Set.MapsTo (TopCat.ofHom
          (X := ↑((TopPair.ofSubset (A x z)).fst ⊗ (TopPair.ofSubset (A z y)).fst))
          ((ι x z y).codRestrict (A x y) (hιA x z y hyz hzx)))
        ((TopPair.ofSubset (A x z)).prodSubspace (TopPair.ofSubset (A z y)))
        (Subtype.val ⁻¹' U x z y)ᶜ)
    (hface : ∀ x z y (hyz : ind y < ind z) (hzx : ind z < ind x) (a : A x y)
      (ha : (a : M x y) ∈ U x z y),
      (HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
          (TopPair.ofSubsetMap _ ((hUA x z y hyz hzx).mono_right
            (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 ha)))))
          (ind x - ind y - 2).toNat).hom
        ((HomologicalComplex.homologyMap
          ((TopPair.ofSubset (A x z)).cubicalChainComplexProdComparison k
            (TopPair.ofSubset (A z y))) (ind x - ind y - 2).toNat).hom
          ((GradedObject.Monoidal.ιTensorObj _ _ _ _ _ (by omega) ≫
            cubicalHomologyKunnethPair k _ _ _).hom (μ x z ⊗ₜ μ z y))) =
        (ind x - ind z).negOnePow •
          (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
            (TopPair.ofSubset ({a}ᶜ : Set (A x y))).map)) (ind x - ind y - 2).toNat).hom
            (((TopPair.ofSubset (A x y)).cubicalHomologyδ k _ _).hom (μ x y))) :
    ∃ S : TwistingChainSystem ind ι k, S.IsRepresenting A μ := by
  refine TwistingChainSystem.exists_isRepresenting fun s x y m hm hs hd ↦ ?_
  obtain rfl : m = (ind x - ind y - 2).toNat := by omega
  -- The faces of `A x y` are indexed by the `z` strictly between `y` and `x` in index.
  let T := {z : P // ind y < ind z ∧ ind z < ind x}
  have hpq (z : T) : (ind x - ind z.val - 1).toNat + (ind z.val - ind y - 1).toNat =
      (ind x - ind y - 2).toNat := by omega
  -- Relative cycles representing the classes of the two factors of each face.
  have ha (z : T) := (isRepresentingChain_iff _ _).1 ((hd x z.val (by omega)).2 z.prop.2)
  have hb (z : T) := (isRepresentingChain_iff _ _).1 ((hd z.val y (by omega)).2 z.prop.1)
  choose a ha ha' using ha
  choose b hb hb' using hb
  -- The face maps `M x z × M z y → A x y`.
  let g (z : T) : C(M x z.val × M z.val y, A x y) :=
    (ι x z.val y).codRestrict (A x y) (hιA x z.val y z.prop.1 z.prop.2)
  -- The face chains: the signed cross products of the representatives, carried to `A x y`.
  let c (z : T) : NormalizedCubicalChain (A x y) k (ind x - ind y - 2).toNat :=
    (ind x - ind z.val).negOnePow •
      NormalizedCubicalChain.map k (g z) _ (cast k (hpq z) (crossProduct _ _ k _ _ (a z) (b z)))
  -- The twisting sum is the sum of the face chains, pushed forward from the boundary.
  have hsum := twistingChainSum_eq_sum_face hs (fun z ↦ hιA x z.val y z.prop.1 z.prop.2) a ha b
    hb hpq
  rw [hsum]
  refine isRepresentingCycle_map_sum (hE x y (by omega)) c ?_
    (F := fun z ↦ (Set.range (g z) : Set (A x y)))
    (U := fun z ↦ (Subtype.val ⁻¹' U x z.val y : Set (A x y))) (fun z ↦ ?_)
    (fun z z' hz ↦ Set.disjoint_left.2 ?_) (Dense.mono ?_ (hU x y (by omega)))
    (fun z a ha ↦ ?_)
  · -- The sum of the face chains, pushed forward to `M x y`, is the twisting sum, a cycle.
    rw [← hsum]
    exact cubicalChainDifferential_twistingChainSum hs (hι x · · y) fun z h₁ h₂ ↦
      ⟨(hd x z (by omega)).1, (hd z y (by omega)).1⟩
  · simp only [c, Units.smul_def]
    exact zsmul_mem (map_mem_supportedIn_range k (g z) _) _
  · rintro _ ⟨p, rfl⟩ hp
    exact Set.disjoint_left.1 (hUι x z.val z'.val y z'.prop.1 z'.prop.2 fun h ↦ hz (Subtype.ext h))
      ⟨p, rfl⟩ (by simpa [g] using hp)
  · rintro a ⟨z, hyz, hzx, ha⟩
    exact Set.mem_iUnion.2 ⟨⟨z, hyz, hzx⟩, ha⟩
  · -- The cross product of the representatives of the two factors, carried to the face, represents
    -- the signed image of `∂ μ x y`, and the sign of the face chain cancels that sign. The helper
    -- types the pair of `{a}ᶜ` through `TopCat.of`, which unfolds to the pair in `hface`.
    exact isCubicalRepresentative_zsmul_map_crossProduct (hpq z) (ha' z) (hb' z) (g z) _ _
      (hface x z.val y z.prop.1 z.prop.2 a ha)

section Continuation

variable {Q : Type*} [Fintype Q] {indQ : Q → ℤ} {M' : Q → Q → TopCat.{u}} {N : P → Q → TopCat.{u}}
  {ι' : ∀ x y z, C(M' x y × M' y z, M' x z)} {κ : ∀ x y z, C(M x y × N y z, N x z)}
  {κ' : ∀ x y z, C(N x y × M' y z, N x z)} {S : TwistingChainSystem ind ι k}
  {S' : TwistingChainSystem indQ ι' k} {A' : ∀ x y, Set (M' x y)} {B : ∀ x y, Set (N x y)}
  {μ' : ∀ x y, ((TopPair.ofSubset (A' x y)).cubicalChainComplex k).homology
    (indQ x - indQ y - 1).toNat}
  {ν : ∀ x y, ((TopPair.ofSubset (B x y)).cubicalChainComplex k).homology (ind x - indQ y).toNat}

/-- The continuation sum of `(x, y)` of chains `t` with representatives `a z` of `s x z` and `b z`
of `t z y` on the left faces, and `a' w` of `t x w` and `b' w` of `s' w y` on the right faces, is
the push-forward from the boundary `B x y` of the sum over the faces of the cross products
`a z × b z` and the signed cross products `a' w × b' w`, carried to `B x y` by the composition
maps. -/
private theorem continuationChainSum_eq_sum_face
    {t : ∀ x y, normalizedCubicalChainAlgebra (N x y) k}
    (ht : ∀ x y, t x y ∈ cubicalChainGrading (N x y) k (indQ y - ind x)) {x : P} {y : Q}
    (hκB : ∀ z : {z // indQ y ≤ ind z ∧ ind z < ind x}, ∀ p, κ x z.val y p ∈ B x y)
    (hκ'B : ∀ w : {w // indQ y < indQ w ∧ indQ w ≤ ind x}, ∀ p, κ' x w.val y p ∈ B x y)
    (a : ∀ z : {z // indQ y ≤ ind z ∧ ind z < ind x},
      NormalizedCubicalChain (M x z.val) k (ind x - ind z.val - 1).toNat)
    (ha : ∀ z, cubicalChainLof _ k _ (a z) = S.chain x z.val)
    (b : ∀ z : {z // indQ y ≤ ind z ∧ ind z < ind x},
      NormalizedCubicalChain (N z.val y) k (ind z.val - indQ y).toNat)
    (hb : ∀ z, cubicalChainLof _ k _ (b z) = t z.val y)
    (a' : ∀ w : {w // indQ y < indQ w ∧ indQ w ≤ ind x},
      NormalizedCubicalChain (N x w.val) k (ind x - indQ w.val).toNat)
    (ha' : ∀ w, cubicalChainLof _ k _ (a' w) = t x w.val)
    (b' : ∀ w : {w // indQ y < indQ w ∧ indQ w ≤ ind x},
      NormalizedCubicalChain (M' w.val y) k (indQ w.val - indQ y - 1).toNat)
    (hb' : ∀ w, cubicalChainLof _ k _ (b' w) = S'.chain w.val y) {n : ℕ}
    (hpq : ∀ z : {z // indQ y ≤ ind z ∧ ind z < ind x},
      (ind x - ind z.val - 1).toNat + (ind z.val - indQ y).toNat = n)
    (hpq' : ∀ w : {w // indQ y < indQ w ∧ indQ w ≤ ind x},
      (ind x - indQ w.val).toNat + (indQ w.val - indQ y - 1).toNat = n) :
    continuationChainSum ind indQ κ κ' k S.chain S'.chain t x y = cubicalChainLof (N x y) k n
      (map k (ContinuousMap.subtypeVal (B x y)) n
        (∑ z, map k ((κ x z.val y).codRestrict (B x y) (hκB z)) n
            (cast k (hpq z) (crossProduct _ _ k _ _ (a z) (b z))) +
          ∑ w, (ind x - indQ w.val - 1).negOnePow •
            map k ((κ' x w.val y).codRestrict (B x y) (hκ'B w)) n
              (cast k (hpq' w) (crossProduct _ _ k _ _ (a' w) (b' w))))) := by
  rw [continuationChainSum_eq_sum_subtype S.mem_graded S'.mem_graded ht, map_add, map_add,
    map_sum, map_sum, map_sum, map_sum]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun z _ ↦ ?_) (Finset.sum_congr rfl fun w _ ↦ ?_)
  · rw [← ha z, ← hb z, cubicalChainSumPairing_lof_lof_eq_subtypeVal _ _ (hκB z) (hpq z)]
  · rw [← ha' w, ← hb' w, cubicalChainSumPairing_lof_lof_eq_subtypeVal _ _ (hκ'B w) (hpq' w),
      map_zsmul_unit, map_zsmul_unit]

/-- **Representing continuation chain systems from a face-by-face condition.** Let `S` and `S'` be
twisting chain systems representing classes `μ x y` of `H_{ind x - ind y - 1}(M x y, A x y)` and
`μ' x y` of `H_{indQ x - indQ y - 1}(M' x y, A' x y)`, and let `ν x y` be classes of
`H_{ind x - indQ y}(N x y, B x y)`. Suppose that:

* each boundary `B x y` is a compact Hausdorff space charted on a finite-dimensional real normed
  space `E x y`, of dimension `ind x - indQ y - 1` whenever `indQ y < ind x`, so that `B x y` is
  then a closed topological manifold of that dimension;
* the composition maps `κ x z y : M x z × N z y → N x y` and `κ' x w y : N x w × M' w y → N x y`
  are associative and, for `indQ y ≤ ind z < ind x` and `indQ y < indQ w ≤ ind x`, land in
  `B x y`;
* the sets `U x z y` and `U' x w y`, the interiors of the left and right faces, are together
  dense in `B x y`, the face of every other `z'` or `w'` misses each of them, and `κ x z y`
  carries `A x z × N z y ∪ M x z × B z y` off `U x z y`, while `κ' x w y` carries
  `B x w × M' w y ∪ N x w × A' w y` off `U' x w y`;
* at each point `a` of the interior `U x z y` of a left face, the cross product of `μ x z` and
  `ν z y`, pushed forward along `κ x z y` to the local homology `H(B x y, B x y ∖ {a})`, is the
  image of the boundary `∂ ν x y ∈ H(B x y)`, and at each point of the interior `U' x w y` of a
  right face, the cross product of `ν x w` and `μ' w y`, pushed forward along `κ' x w y`, is
  `(-1) ^ (ind x - indQ w - 1)` times the image of `∂ ν x y`.

Then some continuation chain system from `S` to `S'` represents the classes `ν`. For the
fundamental classes rel boundary of compactified spaces of continuation trajectories, the last
condition compares the boundary orientation of each face with its product orientation; no
condition is imposed at the corners (BDHO, Chapter 6, the continuation morphisms). -/
theorem ContinuationChainSystem.exists_isRepresenting_of_faces (hS : S.IsRepresenting A μ)
    (hS' : S'.IsRepresenting A' μ')
    {E : P → Q → Type u} [∀ x y, NormedAddCommGroup (E x y)] [∀ x y, NormedSpace ℝ (E x y)]
    [∀ x y, FiniteDimensional ℝ (E x y)] [∀ x y, T2Space (B x y)] [∀ x y, CompactSpace (B x y)]
    [∀ x y, ChartedSpace (E x y) (B x y)]
    (hE : ∀ x y, indQ y < ind x → Module.finrank ℝ (E x y) = (ind x - indQ y - 1).toNat)
    (hκ : ∀ x w z y (a : M x w) (b : M w z) (c : N z y),
      κ x z y (ι x w z (a, b), c) = κ x w y (a, κ w z y (b, c)))
    (hκκ' : ∀ x w z y (a : M x w) (b : N w z) (c : M' z y),
      κ' x z y (κ x w z (a, b), c) = κ x w y (a, κ' w z y (b, c)))
    (hκ' : ∀ x w z y (a : N x w) (b : M' w z) (c : M' z y),
      κ' x z y (κ' x w z (a, b), c) = κ' x w y (a, ι' w z y (b, c)))
    (hκB : ∀ x z y, indQ y ≤ ind z → ind z < ind x → ∀ p, κ x z y p ∈ B x y)
    (hκ'B : ∀ x w y, indQ y < indQ w → indQ w ≤ ind x → ∀ p, κ' x w y p ∈ B x y)
    (U : ∀ x, P → ∀ y, Set (N x y)) (U' : ∀ x, Q → ∀ y, Set (N x y))
    (hU : ∀ x y, indQ y < ind x → Dense {a : B x y |
      (∃ z, indQ y ≤ ind z ∧ ind z < ind x ∧ (a : N x y) ∈ U x z y) ∨
        ∃ w, indQ y < indQ w ∧ indQ w ≤ ind x ∧ (a : N x y) ∈ U' x w y})
    (hUκ : ∀ x z z' y, indQ y ≤ ind z' → ind z' < ind x → z' ≠ z →
      Disjoint (Set.range (κ x z' y)) (U x z y))
    (hUκ' : ∀ x z w y, indQ y < indQ w → indQ w ≤ ind x →
      Disjoint (Set.range (κ' x w y)) (U x z y))
    (hU'κ : ∀ x w z y, indQ y ≤ ind z → ind z < ind x →
      Disjoint (Set.range (κ x z y)) (U' x w y))
    (hU'κ' : ∀ x w w' y, indQ y < indQ w' → indQ w' ≤ ind x → w' ≠ w →
      Disjoint (Set.range (κ' x w' y)) (U' x w y))
    (hUB : ∀ x z y (hyz : indQ y ≤ ind z) (hzx : ind z < ind x),
      Set.MapsTo (TopCat.ofHom
          (X := ↑((TopPair.ofSubset (A x z)).fst ⊗ (TopPair.ofSubset (B z y)).fst))
          ((κ x z y).codRestrict (B x y) (hκB x z y hyz hzx)))
        ((TopPair.ofSubset (A x z)).prodSubspace (TopPair.ofSubset (B z y)))
        (Subtype.val ⁻¹' U x z y)ᶜ)
    (hU'B : ∀ x w y (hyw : indQ y < indQ w) (hwx : indQ w ≤ ind x),
      Set.MapsTo (TopCat.ofHom
          (X := ↑((TopPair.ofSubset (B x w)).fst ⊗ (TopPair.ofSubset (A' w y)).fst))
          ((κ' x w y).codRestrict (B x y) (hκ'B x w y hyw hwx)))
        ((TopPair.ofSubset (B x w)).prodSubspace (TopPair.ofSubset (A' w y)))
        (Subtype.val ⁻¹' U' x w y)ᶜ)
    (hface : ∀ x z y (hyz : indQ y ≤ ind z) (hzx : ind z < ind x) (a : B x y)
      (ha : (a : N x y) ∈ U x z y),
      (HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
          (TopPair.ofSubsetMap _ ((hUB x z y hyz hzx).mono_right
            (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 ha)))))
          (ind x - indQ y - 1).toNat).hom
        ((HomologicalComplex.homologyMap
          ((TopPair.ofSubset (A x z)).cubicalChainComplexProdComparison k
            (TopPair.ofSubset (B z y))) (ind x - indQ y - 1).toNat).hom
          ((GradedObject.Monoidal.ιTensorObj _ _ _ _ _ (by omega) ≫
            cubicalHomologyKunnethPair k _ _ _).hom (μ x z ⊗ₜ ν z y))) =
        (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
          (TopPair.ofSubset ({a}ᶜ : Set (B x y))).map)) (ind x - indQ y - 1).toNat).hom
          (((TopPair.ofSubset (B x y)).cubicalHomologyδ k _ _).hom (ν x y)))
    (hface' : ∀ x w y (hyw : indQ y < indQ w) (hwx : indQ w ≤ ind x) (a : B x y)
      (ha : (a : N x y) ∈ U' x w y),
      (HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
          (TopPair.ofSubsetMap _ ((hU'B x w y hyw hwx).mono_right
            (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 ha)))))
          (ind x - indQ y - 1).toNat).hom
        ((HomologicalComplex.homologyMap
          ((TopPair.ofSubset (B x w)).cubicalChainComplexProdComparison k
            (TopPair.ofSubset (A' w y))) (ind x - indQ y - 1).toNat).hom
          ((GradedObject.Monoidal.ιTensorObj _ _ _ _ _ (by omega) ≫
            cubicalHomologyKunnethPair k _ _ _).hom (ν x w ⊗ₜ μ' w y))) =
        (ind x - indQ w - 1).negOnePow •
          (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
            (TopPair.ofSubset ({a}ᶜ : Set (B x y))).map)) (ind x - indQ y - 1).toNat).hom
            (((TopPair.ofSubset (B x y)).cubicalHomologyδ k _ _).hom (ν x y))) :
    ∃ T : ContinuationChainSystem κ κ' S S', T.IsRepresenting B ν := by
  refine ContinuationChainSystem.exists_isRepresenting κ κ' S S' fun t x y m hm ht hd ↦ ?_
  obtain rfl : m = (ind x - indQ y - 1).toNat := by omega
  -- The left faces of `B x y` are indexed by the `z ∈ P` with `indQ y ≤ ind z < ind x`, the right
  -- faces by the `w ∈ Q` with `indQ y < indQ w ≤ ind x`.
  let T := {z : P // indQ y ≤ ind z ∧ ind z < ind x}
  let T' := {w : Q // indQ y < indQ w ∧ indQ w ≤ ind x}
  have hpq (z : T) : (ind x - ind z.val - 1).toNat + (ind z.val - indQ y).toNat =
      (ind x - indQ y - 1).toNat := by omega
  have hpq' (w : T') : (ind x - indQ w.val).toNat + (indQ w.val - indQ y - 1).toNat =
      (ind x - indQ y - 1).toNat := by omega
  -- Relative cycles representing the classes of the two factors of each face.
  choose a ha hra using fun z : T ↦
    (isRepresentingChain_iff _ _).1 ((S.isRepresenting_iff μ).1 hS x z.val z.prop.2)
  choose b hb hrb using fun z : T ↦
    (isRepresentingChain_iff _ _).1 ((hd z.val y (by omega)).2 z.prop.1)
  choose a' ha' hra' using fun w : T' ↦
    (isRepresentingChain_iff _ _).1 ((hd x w.val (by omega)).2 w.prop.2)
  choose b' hb' hrb' using fun w : T' ↦
    (isRepresentingChain_iff _ _).1 ((S'.isRepresenting_iff μ').1 hS' w.val y w.prop.1)
  -- The face maps `M x z × N z y → B x y` and `N x w × M' w y → B x y`.
  let g (z : T) : C(M x z.val × N z.val y, B x y) :=
    (κ x z.val y).codRestrict (B x y) (hκB x z.val y z.prop.1 z.prop.2)
  let g' (w : T') : C(N x w.val × M' w.val y, B x y) :=
    (κ' x w.val y).codRestrict (B x y) (hκ'B x w.val y w.prop.1 w.prop.2)
  have hgκ (z : T) : Set.range (g z) ⊆ Subtype.val ⁻¹' Set.range (κ x z.val y) :=
    Set.range_subset_iff.2 fun p ↦ ⟨p, (ContinuousMap.coe_codRestrict_apply _ _ _ _).symm⟩
  have hgκ' (w : T') : Set.range (g' w) ⊆ Subtype.val ⁻¹' Set.range (κ' x w.val y) :=
    Set.range_subset_iff.2 fun p ↦ ⟨p, (ContinuousMap.coe_codRestrict_apply _ _ _ _).symm⟩
  -- The face chains: the cross products of the representatives, signed on the right faces, carried
  -- to `B x y`.
  let c : T ⊕ T' → NormalizedCubicalChain (B x y) k (ind x - indQ y - 1).toNat :=
    Sum.elim (fun z ↦ map k (g z) _ (cast k (hpq z) (crossProduct _ _ k _ _ (a z) (b z))))
      fun w ↦ (ind x - indQ w.val - 1).negOnePow •
        map k (g' w) _ (cast k (hpq' w) (crossProduct _ _ k _ _ (a' w) (b' w)))
  -- The continuation sum is the sum of the face chains, pushed forward from the boundary.
  have hsum : continuationChainSum ind indQ κ κ' k S.chain S'.chain t x y =
      cubicalChainLof (N x y) k _ (map k (ContinuousMap.subtypeVal (B x y)) _ (∑ i, c i)) := by
    rw [Fintype.sum_sum_type]
    exact continuationChainSum_eq_sum_face ht (fun z ↦ hκB x z.val y z.prop.1 z.prop.2)
      (fun w ↦ hκ'B x w.val y w.prop.1 w.prop.2) a ha b hb a' ha' b' hb' hpq hpq'
  rw [hsum]
  refine isRepresentingCycle_map_sum (hE x y (by omega)) c ?_
    (F := Sum.elim (fun z ↦ (Set.range (g z) : Set (B x y)))
      fun w ↦ (Set.range (g' w) : Set (B x y)))
    (U := Sum.elim (fun z ↦ (Subtype.val ⁻¹' U x z.val y : Set (B x y)))
      fun w ↦ (Subtype.val ⁻¹' U' x w.val y : Set (B x y))) (fun i ↦ ?_) (fun i i' hi ↦ ?_)
    (Dense.mono ?_ (hU x y (by omega))) (fun i a ha ↦ ?_)
  · -- The sum of the face chains, pushed forward to `N x y`, is the continuation sum, a cycle.
    rw [← hsum]
    exact cubicalChainDifferential_continuationChainSum S S' ht (hκ x · · y) (hκκ' x · · y)
      (hκ' x · · y) (fun z _ _ ↦ (hd z y (by omega)).1) fun w _ _ ↦ (hd x w (by omega)).1
  · rcases i with z | w
    · exact map_mem_supportedIn_range k (g z) _
    · simp only [c, Sum.elim_inr, Units.smul_def]
      exact zsmul_mem (map_mem_supportedIn_range k (g' w) _) _
  · -- The face of `i'` misses the interior of the face of `i`.
    rcases i with z | w <;> rcases i' with z' | w'
    · exact ((hUκ x z.val z'.val y z'.prop.1 z'.prop.2 fun h ↦ hi (congrArg Sum.inl
        (Subtype.ext h))).preimage _).mono_left (hgκ z')
    · exact ((hUκ' x z.val w'.val y w'.prop.1 w'.prop.2).preimage _).mono_left (hgκ' w')
    · exact ((hU'κ x w.val z'.val y z'.prop.1 z'.prop.2).preimage _).mono_left (hgκ z')
    · exact ((hU'κ' x w.val w'.val y w'.prop.1 w'.prop.2 fun h ↦ hi (congrArg Sum.inr
        (Subtype.ext h))).preimage _).mono_left (hgκ' w')
  · rintro a (⟨z, hyz, hzx, ha⟩ | ⟨w, hyw, hwx, ha⟩)
    · exact Set.mem_iUnion.2 ⟨Sum.inl ⟨z, hyz, hzx⟩, ha⟩
    · exact Set.mem_iUnion.2 ⟨Sum.inr ⟨w, hyw, hwx⟩, ha⟩
  · rcases i with z | w
    · -- The cross product of the representatives of the two factors, carried to the face,
      -- represents the image of `∂ ν x y`. The helper types the pair of `{a}ᶜ` through
      -- `TopCat.of`, which unfolds to the pair in `hface`.
      have h := isCubicalRepresentative_map_crossProduct (hpq z) (hra z) (hrb z) (g z)
        ((hUB x z.val y z.prop.1 z.prop.2).mono_right
          (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 ha)))
      rwa [hface x z.val y z.prop.1 z.prop.2 a ha] at h
    · -- On a right face the sign of the face chain cancels the sign of the face condition. As on
      -- a left face, the helper's pair of `{a}ᶜ` unfolds to the pair in `hface'`.
      exact isCubicalRepresentative_zsmul_map_crossProduct (hpq' w) (hra' w) (hrb' w) (g' w) _ _
        (hface' x w.val y w.prop.1 w.prop.2 a ha)

end Continuation

section Parametrized

variable {Q : Type*} [Fintype Q] {indQ : Q → ℤ} {M' : Q → Q → TopCat.{u}}
  {N₀ N₁ H : P → Q → TopCat.{u}} {ι' : ∀ x y z, C(M' x y × M' y z, M' x z)}
  {κ₀ : ∀ x y z, C(M x y × N₀ y z, N₀ x z)} {κ₀' : ∀ x y z, C(N₀ x y × M' y z, N₀ x z)}
  {κ₁ : ∀ x y z, C(M x y × N₁ y z, N₁ x z)} {κ₁' : ∀ x y z, C(N₁ x y × M' y z, N₁ x z)}
  {κH : ∀ x y z, C(M x y × H y z, H x z)} {κH' : ∀ x y z, C(H x y × M' y z, H x z)}
  {j₀ : ∀ x y, C(N₀ x y, H x y)} {j₁ : ∀ x y, C(N₁ x y, H x y)}
  {S : TwistingChainSystem ind ι k} {S' : TwistingChainSystem indQ ι' k}
  {T₀ : ContinuationChainSystem κ₀ κ₀' S S'} {T₁ : ContinuationChainSystem κ₁ κ₁' S S'}
  {A' : ∀ x y, Set (M' x y)} {B₀ : ∀ x y, Set (N₀ x y)} {B₁ : ∀ x y, Set (N₁ x y)}
  {C : ∀ x y, Set (H x y)}
  {μ' : ∀ x y, ((TopPair.ofSubset (A' x y)).cubicalChainComplex k).homology
    (indQ x - indQ y - 1).toNat}
  {ν₀ : ∀ x y, ((TopPair.ofSubset (B₀ x y)).cubicalChainComplex k).homology (ind x - indQ y).toNat}
  {ν₁ : ∀ x y, ((TopPair.ofSubset (B₁ x y)).cubicalChainComplex k).homology (ind x - indQ y).toNat}
  {θ : ∀ x y, ((TopPair.ofSubset (C x y)).cubicalChainComplex k).homology
    (ind x - indQ y + 1).toNat}

/-- An end chain represents the local class prescribed on its face: if `a` represents the class
`μ₁` of the pair `(X₁, A₁)` and the map `g` carries `A₁` off the point `z`, then the push-forward
of `a` along `g` represents the image of `μ₁` in the local homology at `z`. -/
private theorem isCubicalRepresentative_map {X₁ : TopCat.{u}} {A₁ : Set X₁} {Z : Type u}
    [TopologicalSpace Z] {n : ℕ} {a : NormalizedCubicalChain X₁ k n}
    {μ₁ : ((TopPair.ofSubset A₁).cubicalChainComplex k).homology n}
    (ha : (TopPair.ofSubset A₁).IsCubicalRepresentative k a μ₁) (g : C(X₁, Z)) {z : Z}
    (hg : Set.MapsTo (TopCat.ofHom (X := X₁) g) A₁ ({z}ᶜ : Set Z)) :
    (TopPair.ofSubset (X := TopCat.of Z) {z}ᶜ).IsCubicalRepresentative k (map k g n a)
      ((HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
        (TopPair.ofSubsetMap _ hg)) n).hom μ₁) := by
  obtain ⟨r, hr, hcl⟩ :=
    (TopPair.isCubicalRepresentative_iff _ _).1 (ha.map (TopPair.ofSubsetMap _ hg))
  rw [TopPair.ofSubsetMap_fst] at hr
  exact (TopPair.isCubicalRepresentative_iff _ _).2 ⟨r, hr, hcl⟩

/-- The push-forward along `f` of the homogeneous chain `a` is its push-forward through any
subspace `B` containing the image of `f`. -/
private theorem cubicalChainSumMap_lof_eq_subtypeVal {X₁ Z : Type*} [TopologicalSpace X₁]
    [TopologicalSpace Z] (f : C(X₁, Z)) (B : Set Z) (hf : ∀ p, f p ∈ B) {n : ℕ}
    (a : NormalizedCubicalChain X₁ k n) :
    cubicalChainSumMap k f (cubicalChainLof _ k _ a) = cubicalChainLof Z k n
      (map k (ContinuousMap.subtypeVal B) n (map k (f.codRestrict B hf) n a)) := by
  rw [cubicalChainSumMap_lof, ← LinearMap.comp_apply (map k (ContinuousMap.subtypeVal B) n),
    ← map_comp, ContinuousMap.subtypeVal_comp_codRestrict]

/-- The parametrized sum of `(x, y)` of chains `h`, with representatives `e₀` of `ν₀ x y` and `e₁`
of `ν₁ x y` on the two ends, `a z` of `s x z` and `b z` of `h z y` on the left faces, and `a' w` of
`h x w` and `b' w` of `s' w y` on the right faces, is the push-forward from the boundary `C x y` of
the sum over the faces of the end chains, with the sign `-1` on the end `j₀`, and of the signed
cross products `a z × b z` and `a' w × b' w`, carried to `C x y` by the face maps. -/
private theorem parametrizedChainSum_eq_sum_face
    {h : ∀ x y, normalizedCubicalChainAlgebra (H x y) k}
    (hh : ∀ x y, h x y ∈ cubicalChainGrading (H x y) k (indQ y - ind x - 1)) {x : P} {y : Q}
    (hj₀C : ∀ p, j₀ x y p ∈ C x y) (hj₁C : ∀ p, j₁ x y p ∈ C x y)
    (hκHC : ∀ z : {z // indQ y ≤ ind z + 1 ∧ ind z < ind x}, ∀ p, κH x z.val y p ∈ C x y)
    (hκH'C : ∀ w : {w // indQ y < indQ w ∧ indQ w ≤ ind x + 1}, ∀ p, κH' x w.val y p ∈ C x y)
    {n : ℕ} (e₀ : NormalizedCubicalChain (N₀ x y) k n)
    (he₀ : cubicalChainLof _ k _ e₀ = T₀.chain x y) (e₁ : NormalizedCubicalChain (N₁ x y) k n)
    (he₁ : cubicalChainLof _ k _ e₁ = T₁.chain x y)
    (a : ∀ z : {z // indQ y ≤ ind z + 1 ∧ ind z < ind x},
      NormalizedCubicalChain (M x z.val) k (ind x - ind z.val - 1).toNat)
    (ha : ∀ z, cubicalChainLof _ k _ (a z) = S.chain x z.val)
    (b : ∀ z : {z // indQ y ≤ ind z + 1 ∧ ind z < ind x},
      NormalizedCubicalChain (H z.val y) k (ind z.val - indQ y + 1).toNat)
    (hb : ∀ z, cubicalChainLof _ k _ (b z) = h z.val y)
    (a' : ∀ w : {w // indQ y < indQ w ∧ indQ w ≤ ind x + 1},
      NormalizedCubicalChain (H x w.val) k (ind x - indQ w.val + 1).toNat)
    (ha' : ∀ w, cubicalChainLof _ k _ (a' w) = h x w.val)
    (b' : ∀ w : {w // indQ y < indQ w ∧ indQ w ≤ ind x + 1},
      NormalizedCubicalChain (M' w.val y) k (indQ w.val - indQ y - 1).toNat)
    (hb' : ∀ w, cubicalChainLof _ k _ (b' w) = S'.chain w.val y)
    (hpq : ∀ z : {z // indQ y ≤ ind z + 1 ∧ ind z < ind x},
      (ind x - ind z.val - 1).toNat + (ind z.val - indQ y + 1).toNat = n)
    (hpq' : ∀ w : {w // indQ y < indQ w ∧ indQ w ≤ ind x + 1},
      (ind x - indQ w.val + 1).toNat + (indQ w.val - indQ y - 1).toNat = n) :
    parametrizedChainSum ind indQ κH κH' j₀ j₁ k S.chain S'.chain T₀.chain T₁.chain h x y =
      cubicalChainLof (H x y) k n (map k (ContinuousMap.subtypeVal (C x y)) n
        (map k ((j₁ x y).codRestrict (C x y) hj₁C) n e₁ -
            map k ((j₀ x y).codRestrict (C x y) hj₀C) n e₀ +
          ∑ z, (ind x - ind z.val).negOnePow •
            map k ((κH x z.val y).codRestrict (C x y) (hκHC z)) n
              (cast k (hpq z) (crossProduct _ _ k _ _ (a z) (b z))) +
          ∑ w, (ind x - indQ w.val).negOnePow •
            map k ((κH' x w.val y).codRestrict (C x y) (hκH'C w)) n
              (cast k (hpq' w) (crossProduct _ _ k _ _ (a' w) (b' w))))) := by
  rw [parametrizedChainSum_eq_sum_subtype S.mem_graded S'.mem_graded hh, ← he₀, ← he₁,
    cubicalChainSumMap_lof_eq_subtypeVal _ _ hj₀C, cubicalChainSumMap_lof_eq_subtypeVal _ _ hj₁C]
  simp only [map_add, map_sub, map_sum, map_zsmul_unit]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun z _ ↦ ?_))
    (Finset.sum_congr rfl fun w _ ↦ ?_)
  · rw [← ha z, ← hb z, cubicalChainSumPairing_lof_lof_eq_subtypeVal _ _ (hκHC z) (hpq z)]
  · rw [← ha' w, ← hb' w, cubicalChainSumPairing_lof_lof_eq_subtypeVal _ _ (hκH'C w) (hpq' w)]

/-- **Representing parametrized chain systems from a face-by-face condition.** Let `S` and `S'`
be twisting chain systems representing classes `μ x y` of `H_{ind x - ind y - 1}(M x y, A x y)` and
`μ' x y` of `H_{indQ x - indQ y - 1}(M' x y, A' x y)`, let `T₀` and `T₁` be continuation chain
systems from `S` to `S'` representing classes `ν₀ x y` of `H_{ind x - indQ y}(N₀ x y, B₀ x y)` and
`ν₁ x y` of `H_{ind x - indQ y}(N₁ x y, B₁ x y)`, and let `θ x y` be classes of
`H_{ind x - indQ y + 1}(H x y, C x y)`. Suppose that:

* each boundary `C x y` is a compact Hausdorff space charted on a finite-dimensional real normed
  space `E x y`, of dimension `ind x - indQ y` whenever `indQ y ≤ ind x`, so that `C x y` is then a
  closed topological manifold of that dimension;
* the composition maps `κH x z y : M x z × H z y → H x y` and `κH' x w y : H x w × M' w y → H x y`
  are associative, the inclusions `j₀ x y : N₀ x y → H x y` and `j₁ x y : N₁ x y → H x y` of the two
  ends are compatible with the composition maps, and for `indQ y ≤ ind x` the ends, the left faces
  with `indQ y ≤ ind z + 1` and `ind z < ind x`, and the right faces with `indQ y < indQ w` and
  `indQ w ≤ ind x + 1` land in `C x y`;
* the sets `V₀ x y`, `V₁ x y`, `U x z y` and `U' x w y`, the interiors of the two ends and of the
  left and right faces, are together dense in `C x y`, each face misses the interior of every
  other face, and each face map carries the boundary of its source (`B₀ x y`, `B₁ x y`,
  `A x z × H z y ∪ M x z × C z y` or `C x w × M' w y ∪ H x w × A' w y`) off the interior of its
  face;
* at each point `a` of the interior of a face, the image of the class of the face in the local
  homology `H(C x y, C x y ∖ {a})` is a signed image of the boundary `∂ θ x y ∈ H(C x y)`: with
  the sign `-1` for `ν₀ x y` on the end `j₀`, `+1` for `ν₁ x y` on the end `j₁`,
  `(-1) ^ (ind x - ind z)` for the cross product of `μ x z` and `θ z y` on a left face, and
  `(-1) ^ (ind x - indQ w)` for the cross product of `θ x w` and `μ' w y` on a right face.

Then some parametrized chain system between `T₀` and `T₁` represents the classes `θ`. For the
fundamental classes rel boundary of the compactified spaces of trajectories of a one-parameter
family of homotopies, the last condition compares the boundary orientation of each face with its
product orientation; no condition is imposed at the corners (BDHO, Chapter 6, the homotopies
between continuation morphisms). -/
theorem ParametrizedChainSystem.exists_isRepresenting_of_faces (hS : S.IsRepresenting A μ)
    (hS' : S'.IsRepresenting A' μ') (hT₀ : T₀.IsRepresenting B₀ ν₀)
    (hT₁ : T₁.IsRepresenting B₁ ν₁)
    {E : P → Q → Type u} [∀ x y, NormedAddCommGroup (E x y)] [∀ x y, NormedSpace ℝ (E x y)]
    [∀ x y, FiniteDimensional ℝ (E x y)] [∀ x y, T2Space (C x y)] [∀ x y, CompactSpace (C x y)]
    [∀ x y, ChartedSpace (E x y) (C x y)]
    (hE : ∀ x y, indQ y ≤ ind x → Module.finrank ℝ (E x y) = (ind x - indQ y).toNat)
    (hκH : ∀ x w z y (a : M x w) (b : M w z) (c : H z y),
      κH x z y (ι x w z (a, b), c) = κH x w y (a, κH w z y (b, c)))
    (hκHκH' : ∀ x w z y (a : M x w) (b : H w z) (c : M' z y),
      κH' x z y (κH x w z (a, b), c) = κH x w y (a, κH' w z y (b, c)))
    (hκH' : ∀ x w z y (a : H x w) (b : M' w z) (c : M' z y),
      κH' x z y (κH' x w z (a, b), c) = κH' x w y (a, ι' w z y (b, c)))
    (hj₀κ : ∀ x z y (u : M x z) (v : N₀ z y), j₀ x y (κ₀ x z y (u, v)) = κH x z y (u, j₀ z y v))
    (hj₀κ' : ∀ x z y (u : N₀ x z) (v : M' z y),
      j₀ x y (κ₀' x z y (u, v)) = κH' x z y (j₀ x z u, v))
    (hj₁κ : ∀ x z y (u : M x z) (v : N₁ z y), j₁ x y (κ₁ x z y (u, v)) = κH x z y (u, j₁ z y v))
    (hj₁κ' : ∀ x z y (u : N₁ x z) (v : M' z y),
      j₁ x y (κ₁' x z y (u, v)) = κH' x z y (j₁ x z u, v))
    (hj₀C : ∀ x y, indQ y ≤ ind x → ∀ p, j₀ x y p ∈ C x y)
    (hj₁C : ∀ x y, indQ y ≤ ind x → ∀ p, j₁ x y p ∈ C x y)
    (hκHC : ∀ x z y, indQ y ≤ ind z + 1 → ind z < ind x → ∀ p, κH x z y p ∈ C x y)
    (hκH'C : ∀ x w y, indQ y < indQ w → indQ w ≤ ind x + 1 → ∀ p, κH' x w y p ∈ C x y)
    (V₀ V₁ : ∀ x y, Set (H x y)) (U : ∀ x, P → ∀ y, Set (H x y))
    (U' : ∀ x, Q → ∀ y, Set (H x y))
    (hU : ∀ x y, indQ y ≤ ind x → Dense {a : C x y |
      (a : H x y) ∈ V₀ x y ∨ (a : H x y) ∈ V₁ x y ∨
        (∃ z, indQ y ≤ ind z + 1 ∧ ind z < ind x ∧ (a : H x y) ∈ U x z y) ∨
          ∃ w, indQ y < indQ w ∧ indQ w ≤ ind x + 1 ∧ (a : H x y) ∈ U' x w y})
    (hV₀j₁ : ∀ x y, indQ y ≤ ind x → Disjoint (Set.range (j₁ x y)) (V₀ x y))
    (hV₀κH : ∀ x z y, indQ y ≤ ind z + 1 → ind z < ind x →
      Disjoint (Set.range (κH x z y)) (V₀ x y))
    (hV₀κH' : ∀ x w y, indQ y < indQ w → indQ w ≤ ind x + 1 →
      Disjoint (Set.range (κH' x w y)) (V₀ x y))
    (hV₁j₀ : ∀ x y, indQ y ≤ ind x → Disjoint (Set.range (j₀ x y)) (V₁ x y))
    (hV₁κH : ∀ x z y, indQ y ≤ ind z + 1 → ind z < ind x →
      Disjoint (Set.range (κH x z y)) (V₁ x y))
    (hV₁κH' : ∀ x w y, indQ y < indQ w → indQ w ≤ ind x + 1 →
      Disjoint (Set.range (κH' x w y)) (V₁ x y))
    (hUj₀ : ∀ x z y, indQ y ≤ ind x → Disjoint (Set.range (j₀ x y)) (U x z y))
    (hUj₁ : ∀ x z y, indQ y ≤ ind x → Disjoint (Set.range (j₁ x y)) (U x z y))
    (hUκH : ∀ x z z' y, indQ y ≤ ind z' + 1 → ind z' < ind x → z' ≠ z →
      Disjoint (Set.range (κH x z' y)) (U x z y))
    (hUκH' : ∀ x z w y, indQ y < indQ w → indQ w ≤ ind x + 1 →
      Disjoint (Set.range (κH' x w y)) (U x z y))
    (hU'j₀ : ∀ x w y, indQ y ≤ ind x → Disjoint (Set.range (j₀ x y)) (U' x w y))
    (hU'j₁ : ∀ x w y, indQ y ≤ ind x → Disjoint (Set.range (j₁ x y)) (U' x w y))
    (hU'κH : ∀ x w z y, indQ y ≤ ind z + 1 → ind z < ind x →
      Disjoint (Set.range (κH x z y)) (U' x w y))
    (hU'κH' : ∀ x w w' y, indQ y < indQ w' → indQ w' ≤ ind x + 1 → w' ≠ w →
      Disjoint (Set.range (κH' x w' y)) (U' x w y))
    (hV₀B : ∀ x y (hxy : indQ y ≤ ind x),
      Set.MapsTo (TopCat.ofHom (X := N₀ x y) ((j₀ x y).codRestrict (C x y) (hj₀C x y hxy)))
        (B₀ x y) (Subtype.val ⁻¹' V₀ x y)ᶜ)
    (hV₁B : ∀ x y (hxy : indQ y ≤ ind x),
      Set.MapsTo (TopCat.ofHom (X := N₁ x y) ((j₁ x y).codRestrict (C x y) (hj₁C x y hxy)))
        (B₁ x y) (Subtype.val ⁻¹' V₁ x y)ᶜ)
    (hUC : ∀ x z y (hyz : indQ y ≤ ind z + 1) (hzx : ind z < ind x),
      Set.MapsTo (TopCat.ofHom
          (X := ↑((TopPair.ofSubset (A x z)).fst ⊗ (TopPair.ofSubset (C z y)).fst))
          ((κH x z y).codRestrict (C x y) (hκHC x z y hyz hzx)))
        ((TopPair.ofSubset (A x z)).prodSubspace (TopPair.ofSubset (C z y)))
        (Subtype.val ⁻¹' U x z y)ᶜ)
    (hU'C : ∀ x w y (hyw : indQ y < indQ w) (hwx : indQ w ≤ ind x + 1),
      Set.MapsTo (TopCat.ofHom
          (X := ↑((TopPair.ofSubset (C x w)).fst ⊗ (TopPair.ofSubset (A' w y)).fst))
          ((κH' x w y).codRestrict (C x y) (hκH'C x w y hyw hwx)))
        ((TopPair.ofSubset (C x w)).prodSubspace (TopPair.ofSubset (A' w y)))
        (Subtype.val ⁻¹' U' x w y)ᶜ)
    (hface₀ : ∀ x y (hxy : indQ y ≤ ind x) (a : C x y) (ha : (a : H x y) ∈ V₀ x y),
      (HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
          (TopPair.ofSubsetMap _ ((hV₀B x y hxy).mono_right
            (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 ha)))))
          (ind x - indQ y).toNat).hom (ν₀ x y) =
        -(HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
          (TopPair.ofSubset ({a}ᶜ : Set (C x y))).map)) (ind x - indQ y).toNat).hom
          (((TopPair.ofSubset (C x y)).cubicalHomologyδ k (ind x - indQ y + 1).toNat
            (ind x - indQ y).toNat (by omega)).hom (θ x y)))
    (hface₁ : ∀ x y (hxy : indQ y ≤ ind x) (a : C x y) (ha : (a : H x y) ∈ V₁ x y),
      (HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
          (TopPair.ofSubsetMap _ ((hV₁B x y hxy).mono_right
            (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 ha)))))
          (ind x - indQ y).toNat).hom (ν₁ x y) =
        (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
          (TopPair.ofSubset ({a}ᶜ : Set (C x y))).map)) (ind x - indQ y).toNat).hom
          (((TopPair.ofSubset (C x y)).cubicalHomologyδ k (ind x - indQ y + 1).toNat
            (ind x - indQ y).toNat (by omega)).hom (θ x y)))
    (hface : ∀ x z y (hyz : indQ y ≤ ind z + 1) (hzx : ind z < ind x) (a : C x y)
      (ha : (a : H x y) ∈ U x z y),
      (HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
          (TopPair.ofSubsetMap _ ((hUC x z y hyz hzx).mono_right
            (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 ha)))))
          (ind x - indQ y).toNat).hom
        ((HomologicalComplex.homologyMap
          ((TopPair.ofSubset (A x z)).cubicalChainComplexProdComparison k
            (TopPair.ofSubset (C z y))) (ind x - indQ y).toNat).hom
          ((GradedObject.Monoidal.ιTensorObj _ _ _ _ _ (by omega) ≫
            cubicalHomologyKunnethPair k _ _ _).hom (μ x z ⊗ₜ θ z y))) =
        (ind x - ind z).negOnePow •
          (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
            (TopPair.ofSubset ({a}ᶜ : Set (C x y))).map)) (ind x - indQ y).toNat).hom
            (((TopPair.ofSubset (C x y)).cubicalHomologyδ k (ind x - indQ y + 1).toNat
            (ind x - indQ y).toNat (by omega)).hom (θ x y)))
    (hface' : ∀ x w y (hyw : indQ y < indQ w) (hwx : indQ w ≤ ind x + 1) (a : C x y)
      (ha : (a : H x y) ∈ U' x w y),
      (HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
          (TopPair.ofSubsetMap _ ((hU'C x w y hyw hwx).mono_right
            (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 ha)))))
          (ind x - indQ y).toNat).hom
        ((HomologicalComplex.homologyMap
          ((TopPair.ofSubset (C x w)).cubicalChainComplexProdComparison k
            (TopPair.ofSubset (A' w y))) (ind x - indQ y).toNat).hom
          ((GradedObject.Monoidal.ιTensorObj _ _ _ _ _ (by omega) ≫
            cubicalHomologyKunnethPair k _ _ _).hom (θ x w ⊗ₜ μ' w y))) =
        (ind x - indQ w).negOnePow •
          (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
            (TopPair.ofSubset ({a}ᶜ : Set (C x y))).map)) (ind x - indQ y).toNat).hom
            (((TopPair.ofSubset (C x y)).cubicalHomologyδ k (ind x - indQ y + 1).toNat
            (ind x - indQ y).toNat (by omega)).hom (θ x y))) :
    ∃ η : ParametrizedChainSystem κH κH' j₀ j₁ T₀ T₁, η.IsRepresenting C θ := by
  refine ParametrizedChainSystem.exists_isRepresenting κH κH' j₀ j₁ T₀ T₁
    fun h x y m hm hh hd ↦ ?_
  obtain rfl : m = (ind x - indQ y).toNat := by omega
  have hxy : indQ y ≤ ind x := by omega
  -- Besides the two ends, the left faces of `C x y` are indexed by the `z ∈ P` with
  -- `indQ y ≤ ind z + 1` and `ind z < ind x`, the right faces by the `w ∈ Q` with
  -- `indQ y < indQ w ≤ ind x + 1`.
  let T := {z : P // indQ y ≤ ind z + 1 ∧ ind z < ind x}
  let T' := {w : Q // indQ y < indQ w ∧ indQ w ≤ ind x + 1}
  have hpq (z : T) : (ind x - ind z.val - 1).toNat + (ind z.val - indQ y + 1).toNat =
      (ind x - indQ y).toNat := by omega
  have hpq' (w : T') : (ind x - indQ w.val + 1).toNat + (indQ w.val - indQ y - 1).toNat =
      (ind x - indQ y).toNat := by omega
  -- Relative cycles representing the classes of the two ends and of the two factors of each face.
  obtain ⟨e₀, he₀, hre₀⟩ :=
    (isRepresentingChain_iff _ _).1 ((T₀.isRepresenting_iff ν₀).1 hT₀ x y hxy)
  obtain ⟨e₁, he₁, hre₁⟩ :=
    (isRepresentingChain_iff _ _).1 ((T₁.isRepresenting_iff ν₁).1 hT₁ x y hxy)
  choose a ha hra using fun z : T ↦
    (isRepresentingChain_iff _ _).1 ((S.isRepresenting_iff μ).1 hS x z.val z.prop.2)
  choose b hb hrb using fun z : T ↦
    (isRepresentingChain_iff _ _).1 ((hd z.val y (by omega)).2 z.prop.1)
  choose a' ha' hra' using fun w : T' ↦
    (isRepresentingChain_iff _ _).1 ((hd x w.val (by omega)).2 w.prop.2)
  choose b' hb' hrb' using fun w : T' ↦
    (isRepresentingChain_iff _ _).1 ((S'.isRepresenting_iff μ').1 hS' w.val y w.prop.1)
  -- The face maps into `C x y`.
  let g₀ : C(N₀ x y, C x y) := (j₀ x y).codRestrict (C x y) (hj₀C x y hxy)
  let g₁ : C(N₁ x y, C x y) := (j₁ x y).codRestrict (C x y) (hj₁C x y hxy)
  let g (z : T) : C(M x z.val × H z.val y, C x y) :=
    (κH x z.val y).codRestrict (C x y) (hκHC x z.val y z.prop.1 z.prop.2)
  let g' (w : T') : C(H x w.val × M' w.val y, C x y) :=
    (κH' x w.val y).codRestrict (C x y) (hκH'C x w.val y w.prop.1 w.prop.2)
  have hg₀ : Set.range g₀ ⊆ Subtype.val ⁻¹' Set.range (j₀ x y) :=
    Set.range_subset_iff.2 fun p ↦ ⟨p, (ContinuousMap.coe_codRestrict_apply _ _ _ _).symm⟩
  have hg₁ : Set.range g₁ ⊆ Subtype.val ⁻¹' Set.range (j₁ x y) :=
    Set.range_subset_iff.2 fun p ↦ ⟨p, (ContinuousMap.coe_codRestrict_apply _ _ _ _).symm⟩
  have hgκ (z : T) : Set.range (g z) ⊆ Subtype.val ⁻¹' Set.range (κH x z.val y) :=
    Set.range_subset_iff.2 fun p ↦ ⟨p, (ContinuousMap.coe_codRestrict_apply _ _ _ _).symm⟩
  have hgκ' (w : T') : Set.range (g' w) ⊆ Subtype.val ⁻¹' Set.range (κH' x w.val y) :=
    Set.range_subset_iff.2 fun p ↦ ⟨p, (ContinuousMap.coe_codRestrict_apply _ _ _ _).symm⟩
  -- The face chains: the end chains, with the sign `-1` on the end `j₀`, and the signed cross
  -- products of the representatives, carried to `C x y`.
  let c : Bool ⊕ (T ⊕ T') → NormalizedCubicalChain (C x y) k (ind x - indQ y).toNat :=
    Sum.elim (fun i ↦ cond i (map k g₁ _ e₁) ((-1 : ℤ) • map k g₀ _ e₀))
      (Sum.elim
        (fun z ↦ (ind x - ind z.val).negOnePow •
          map k (g z) _ (cast k (hpq z) (crossProduct _ _ k _ _ (a z) (b z))))
        fun w ↦ (ind x - indQ w.val).negOnePow •
          map k (g' w) _ (cast k (hpq' w) (crossProduct _ _ k _ _ (a' w) (b' w))))
  -- The parametrized sum is the sum of the face chains, pushed forward from the boundary.
  have hsum : parametrizedChainSum ind indQ κH κH' j₀ j₁ k S.chain S'.chain T₀.chain T₁.chain h
      x y =
        cubicalChainLof (H x y) k _ (map k (ContinuousMap.subtypeVal (C x y)) _ (∑ i, c i)) := by
    rw [parametrizedChainSum_eq_sum_face hh (hj₀C x y hxy) (hj₁C x y hxy)
      (fun z ↦ hκHC x z.val y z.prop.1 z.prop.2) (fun w ↦ hκH'C x w.val y w.prop.1 w.prop.2) e₀
      he₀ e₁ he₁ a ha b hb a' ha' b' hb' hpq hpq', Fintype.sum_sum_type, Fintype.sum_bool,
      Fintype.sum_sum_type]
    simp only [c, Sum.elim_inl, Sum.elim_inr, Bool.cond_true, Bool.cond_false, neg_one_zsmul,
      sub_eq_add_neg, add_assoc]
    -- The two sides differ only by the local definitions of the face maps.
    rfl
  rw [hsum]
  refine isRepresentingCycle_map_sum (hE x y hxy) c ?_
    (F := Sum.elim (fun i ↦ cond i (Set.range g₁) (Set.range g₀))
      (Sum.elim (fun z ↦ (Set.range (g z) : Set (C x y))) fun w ↦ Set.range (g' w)))
    (U := Sum.elim (fun i ↦ cond i (Subtype.val ⁻¹' V₁ x y) (Subtype.val ⁻¹' V₀ x y))
      (Sum.elim (fun z ↦ (Subtype.val ⁻¹' U x z.val y : Set (C x y)))
        fun w ↦ Subtype.val ⁻¹' U' x w.val y)) (fun i ↦ ?_) (fun i i' hi ↦ ?_)
    (Dense.mono ?_ (hU x y hxy)) (fun i a ha ↦ ?_)
  · -- The sum of the face chains, pushed forward to `H x y`, is the parametrized sum, a cycle.
    rw [← hsum]
    exact cubicalChainDifferential_parametrizedChainSum j₀ j₁ T₀ T₁ hh (hκH x · · y)
      (hκHκH' x · · y) (hκH' x · · y) (hj₀κ x · y) (hj₀κ' x · y) (hj₁κ x · y) (hj₁κ' x · y)
      (fun z _ _ ↦ (hd z y (by omega)).1) fun w _ _ ↦ (hd x w (by omega)).1
  · rcases i with (_ | _) | z | w
    · exact zsmul_mem (map_mem_supportedIn_range k g₀ _) _
    · exact map_mem_supportedIn_range k g₁ _
    · simp only [c, Sum.elim_inr, Sum.elim_inl, Units.smul_def]
      exact zsmul_mem (map_mem_supportedIn_range k (g z) _) _
    · simp only [c, Sum.elim_inr, Units.smul_def]
      exact zsmul_mem (map_mem_supportedIn_range k (g' w) _) _
  · -- The face of `i'` misses the interior of the face of `i`.
    rcases i with (_ | _) | z | w <;> rcases i' with (_ | _) | z' | w'
    · exact absurd rfl hi
    · exact ((hV₀j₁ x y hxy).preimage _).mono_left hg₁
    · exact ((hV₀κH x z'.val y z'.prop.1 z'.prop.2).preimage _).mono_left (hgκ z')
    · exact ((hV₀κH' x w'.val y w'.prop.1 w'.prop.2).preimage _).mono_left (hgκ' w')
    · exact ((hV₁j₀ x y hxy).preimage _).mono_left hg₀
    · exact absurd rfl hi
    · exact ((hV₁κH x z'.val y z'.prop.1 z'.prop.2).preimage _).mono_left (hgκ z')
    · exact ((hV₁κH' x w'.val y w'.prop.1 w'.prop.2).preimage _).mono_left (hgκ' w')
    · exact ((hUj₀ x z.val y hxy).preimage _).mono_left hg₀
    · exact ((hUj₁ x z.val y hxy).preimage _).mono_left hg₁
    · exact ((hUκH x z.val z'.val y z'.prop.1 z'.prop.2 fun h ↦ hi (congrArg (Sum.inr ∘ Sum.inl)
        (Subtype.ext h))).preimage _).mono_left (hgκ z')
    · exact ((hUκH' x z.val w'.val y w'.prop.1 w'.prop.2).preimage _).mono_left (hgκ' w')
    · exact ((hU'j₀ x w.val y hxy).preimage _).mono_left hg₀
    · exact ((hU'j₁ x w.val y hxy).preimage _).mono_left hg₁
    · exact ((hU'κH x w.val z'.val y z'.prop.1 z'.prop.2).preimage _).mono_left (hgκ z')
    · exact ((hU'κH' x w.val w'.val y w'.prop.1 w'.prop.2 fun h ↦ hi
        (congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext h))).preimage _).mono_left (hgκ' w')
  · rintro a (ha | ha | ⟨z, hyz, hzx, ha⟩ | ⟨w, hyw, hwx, ha⟩)
    · exact Set.mem_iUnion.2 ⟨Sum.inl false, ha⟩
    · exact Set.mem_iUnion.2 ⟨Sum.inl true, ha⟩
    · exact Set.mem_iUnion.2 ⟨Sum.inr (Sum.inl ⟨z, hyz, hzx⟩), ha⟩
    · exact Set.mem_iUnion.2 ⟨Sum.inr (Sum.inr ⟨w, hyw, hwx⟩), ha⟩
  · rcases i with (_ | _) | z | w
    · -- On the end `j₀` the sign of the face chain cancels the sign of the face condition. The
      -- helper types the pair of `{a}ᶜ` through `TopCat.of`, which unfolds to the pair in
      -- `hface₀`.
      have h := (isCubicalRepresentative_map hre₀ g₀ ((hV₀B x y hxy).mono_right
        (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 ha)))).zsmul (-1)
      rwa [hface₀ x y hxy a ha, neg_one_zsmul, neg_neg] at h
    · have h := isCubicalRepresentative_map hre₁ g₁ ((hV₁B x y hxy).mono_right
        (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 ha)))
      rwa [hface₁ x y hxy a ha] at h
    · -- On a face, the sign of the face chain cancels the sign of the face condition. As on the
      -- ends, the helper's pair of `{a}ᶜ` unfolds to the pair in `hface`.
      exact isCubicalRepresentative_zsmul_map_crossProduct (hpq z) (hra z) (hrb z) (g z) _ _
        (hface x z.val y z.prop.1 z.prop.2 a ha)
    · exact isCubicalRepresentative_zsmul_map_crossProduct (hpq' w) (hra' w) (hrb' w) (g' w) _ _
        (hface' x w.val y w.prop.1 w.prop.2 a ha)

end Parametrized

end TauCeti

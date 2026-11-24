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
each `i` some chain `cᵢ`, agreeing with `z` up to a chain of `A ∖ Uᵢ`, is a relative cycle of
`(A, A ∖ Uᵢ)` representing the image of `ν`: the relative class of a cycle is that of any chain
agreeing with it modulo the subspace
(`TopPair.homologyMap_homologyπ_eq_of_isCubicalRepresentative`). Nothing is asked of `z` near the
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
representing `μ z y` is then a relative cycle of `(A x y, A x y ∖ U x z y)`, whose class is the
cross product of the two classes pushed forward along `ι x z y`
(`TopPair.IsCubicalRepresentative.crossProduct`). So the gluing condition holds, and a
representing chain system exists, as soon as on each face this pushed-forward cross product is
`(-1) ^ (ind x - ind z)` times the image of `∂ μ x y`. For the fundamental classes of
compactified trajectory spaces this compares the boundary orientation of each face with its
product orientation.

## Main results

* `TauCeti.isRepresentingCycle_of_forall_isCubicalRepresentative`: a cycle of `A` which, modulo
  `A ∖ Uᵢ`, agrees with a relative cycle representing the image of `ν` for each `i`, represents
  `ν`.
* `TauCeti.isRepresentingCycle_of_eq_sum`: a sum of chains supported in pieces `Fᵢ`, each a
  relative cycle of `(A, A ∖ Uᵢ)` representing the image of `ν`, represents `ν`.
* `TauCeti.TwistingChainSystem.exists_isRepresenting_of_faces`: a twisting chain system
  representing classes `μ` of spaces whose boundaries are compact manifolds glued from faces exists
  when, on the interior of each face, the image of `∂ μ x y` is the signed cross product of the
  classes of the two factors.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Annals of
  Mathematics 166 (2007), Appendix A, the representing chain systems of compactified trajectory
  spaces.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 5.
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
`Hₘ(A, A ∖ Uᵢ)`. Then `z`, pushed forward to `X`, represents `ν`. -/
theorem isRepresentingCycle_of_forall_isCubicalRepresentative [T2Space A] [CompactSpace A]
    [ChartedSpace E A] [FiniteDimensional ℝ E] {m : ℕ} (hm : finrank ℝ E = m)
    (z : ((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).cycles m)
    {ν : ((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).homology m}
    {ι : Type*} {U : ι → Set (TopPair.ofSubset A).snd} (hU : Dense (⋃ i, U i))
    (c : ι → NormalizedCubicalChain (TopPair.ofSubset A).snd k m)
    (hc : ∀ i, (TopPair.ofSubset (U i)ᶜ).IsCubicalRepresentative k (c i)
      ((HomologicalComplex.homologyMap (cokernel.π
        ((normalizedCubicalChainComplex k).map (TopPair.ofSubset (U i)ᶜ).map)) m).hom ν))
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
  exact (isRepresentingCycle_iff _ ν).2 ⟨z, rfl,
    cubicalHomology_ext_of_dense_iUnion (Y := (TopPair.ofSubset A).snd) (E := E) hm hU
      fun i ↦ TopPair.homologyMap_homologyπ_eq_of_isCubicalRepresentative k
        (TopPair.ofSubset (U i)ᶜ) z (hc i)
          -- The embedding `(TopPair.ofSubset S).map` of Mathlib's `TopPair.ofSubset` is, by
          -- definition, `TopCat.ofHom` of the subtype inclusion `ContinuousMap.subtypeVal S`
          -- through which `NormalizedCubicalChain.supportedIn` is defined.
          ((NormalizedCubicalChain.supportedIn_def k _ m).le (hzc i))⟩

/-- **A sum of face chains represents the class they represent face by face.** Let `A` be a
compact `m`-manifold, `ν` a class of the cubical homology `Hₘ(A)`, and let `z` be an `m`-cycle of
`A` which is a finite sum of chains `cᵢ`, each supported in a set `Fᵢ` (a face of `A`). Let `Uᵢ` be
sets with dense union (the interiors of the faces) such that `Uᵢ` meets no other face `Fⱼ`,
`j ≠ i`. If each `cᵢ` is a relative cycle of `(A, A ∖ Uᵢ)` representing the image of `ν`, then
`z`, pushed forward to `X`, represents `ν`.

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
    (hc : ∀ i, (TopPair.ofSubset (U i)ᶜ).IsCubicalRepresentative k (c i)
      ((HomologicalComplex.homologyMap (cokernel.π
        ((normalizedCubicalChainComplex k).map (TopPair.ofSubset (U i)ᶜ).map)) m).hom ν)) :
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

end TauCeti

namespace TauCeti

open MonoidalCategory NormalizedCubicalChain
open scoped TensorProduct

variable {k : Type u} [CommRing k] {P : Type*} [Fintype P] {ind : P → ℤ} {M : P → P → TopCat.{u}}
  {ι : ∀ x y z, C(M x y × M y z, M x z)} {A : ∀ x y, Set (M x y)}
  {μ : ∀ x y, ((TopPair.ofSubset (A x y)).cubicalChainComplex k).homology (ind x - ind y - 1).toNat}

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
  rw [← ha z, ← hb z, cubicalChainSumPairing_lof_lof, map_zsmul_unit, map_zsmul_unit,
    ← LinearMap.comp_apply (map k (ContinuousMap.subtypeVal (A x y)) n), ← map_comp,
    ContinuousMap.subtypeVal_comp_codRestrict, map_cast, cubicalChainLof_cast]

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
* on each face, the cross product of `μ x z` and `μ z y`, pushed forward along `ι x z y` to the
  relative homology `H(A x y, A x y ∖ U x z y)`, is `(-1) ^ (ind x - ind z)` times the image of the
  boundary `∂ μ x y ∈ H(A x y)`.

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
    (hface : ∀ x z y (hyz : ind y < ind z) (hzx : ind z < ind x),
      (HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
          (TopPair.ofSubsetMap _ (hUA x z y hyz hzx))) (ind x - ind y - 2).toNat).hom
        ((HomologicalComplex.homologyMap
          ((TopPair.ofSubset (A x z)).cubicalChainComplexProdComparison k
            (TopPair.ofSubset (A z y))) (ind x - ind y - 2).toNat).hom
          ((GradedObject.Monoidal.ιTensorObj _ _ _ _ _ (by omega) ≫
            cubicalHomologyKunnethPair k _ _ _).hom (μ x z ⊗ₜ μ z y))) =
        (ind x - ind z).negOnePow •
          (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
            (TopPair.ofSubset (Subtype.val ⁻¹' U x z y : Set (A x y))ᶜ).map))
              (ind x - ind y - 2).toNat).hom
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
      map k (g z) _ (cast k (hpq z) (crossProduct _ _ k _ _ (a z) (b z)))
  -- The twisting sum is the sum of the face chains, pushed forward from the boundary.
  have hsum := twistingChainSum_eq_sum_face hs (fun z ↦ hιA x z.val y z.prop.1 z.prop.2) a ha b
    hb hpq
  -- So the sum of the face chains is a cycle of `A x y`, since the twisting sum is a cycle of
  -- `M x y` and the push-forward along the inclusion is injective.
  have hcyc : cubicalChainDifferential (A x y) k (cubicalChainLof _ k _ (∑ z, c z)) = 0 := by
    refine cubicalChainSumMap_injective (f := ContinuousMap.subtypeVal (A x y))
      Subtype.val_injective ?_
    rw [map_zero, ← cubicalChainDifferential_cubicalChainSumMap, cubicalChainSumMap_lof, ← hsum]
    exact cubicalChainDifferential_twistingChainSum hs (hι x · · y) fun z h₁ h₂ ↦
      ⟨(hd x z (by omega)).1, (hd z y (by omega)).1⟩
  obtain ⟨w, hw⟩ := exists_iCycles_eq_of_cubicalChainDifferential_lof_eq_zero _ hcyc
  rw [hsum, ← hw]
  refine isRepresentingCycle_of_eq_sum (hE x y (by omega)) w c hw
    (F := fun z ↦ (Set.range (g z) : Set (A x y)))
    (U := fun z ↦ (Subtype.val ⁻¹' U x z.val y : Set (A x y))) (fun z ↦ ?_)
    (fun z z' hz ↦ Set.disjoint_left.2 ?_) (Dense.mono ?_ (hU x y (by omega))) (fun z ↦ ?_)
  · simp only [c, Units.smul_def]
    exact zsmul_mem (map_mem_supportedIn_range k (g z) _) _
  · rintro _ ⟨p, rfl⟩ hp
    exact Set.disjoint_left.1 (hUι x z.val z'.val y z'.prop.1 z'.prop.2 fun h ↦ hz (Subtype.ext h))
      ⟨p, rfl⟩ (by simpa [g] using hp)
  · rintro a ⟨z, hyz, hzx, ha⟩
    exact Set.mem_iUnion.2 ⟨⟨z, hyz, hzx⟩, ha⟩
  · -- The cross product of the representatives of the two factors, carried to the face, represents
    -- the signed image of `∂ μ x y`, and the sign of the face chain cancels that sign.
    have h := ((ha' z).crossProduct (hpq z) (hb' z)).map
      (TopPair.ofSubsetMap _ (hUA x z.val y z.prop.1 z.prop.2))
    rw [hface x z.val y z.prop.1 z.prop.2] at h
    obtain ⟨r, hr, hcl⟩ := (TopPair.isCubicalRepresentative_iff _ _).1
      (h.zsmul ((ind x - ind z.val).negOnePow : ℤ))
    rw [TopPair.ofSubsetMap_fst] at hr
    refine (TopPair.isCubicalRepresentative_iff _ _).2 ⟨r, hr, hcl.trans ?_⟩
    rw [← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]
    -- The two sides differ only in how the complement of `U x z y` is typed.
    rfl

end TauCeti

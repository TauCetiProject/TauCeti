/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.FaceGluing
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Cubical

/-!
# The face condition on connected components of the faces

Representing chain systems of classes `μ x y ∈ H(M x y, A x y; k)` exist as soon as, at each point
`a` of the interior `U x z y` of each face of each boundary `A x y`, the cross product of `μ x z`
and `μ z y`, pushed forward to the local homology `H(A x y, A x y ∖ {a}; k)`, is
`(-1) ^ (ind x - ind z)` times the image of the boundary `∂ μ x y`
(`TauCeti.TwistingChainSystem.exists_isRepresenting_of_faces`). For the fundamental classes of
compactified trajectory spaces this compares, at each point of each face, the boundary orientation
of the face with its product orientation. When `1` is the only unit of the coefficients, both sides
are the unique generator of the local homology and the comparison is automatic
(`TauCeti.TwistingChainSystem.exists_isRepresenting_of_subsingleton_units`); over `ℤ` it is not.

This file shows that the comparison need only be made at one point of each connected component of
each face interior, for coefficients in any commutative ring
(`TauCeti.TwistingChainSystem.exists_isRepresenting_of_faces_of_connectedComponentIn`). When the
face interiors are open in the boundary, both sides of the condition at `a` are the images in the
local homology at `a` of two classes of `H(A x y, A x y ∖ U x z y; k)`: the cross product pushed
forward along the composition map, which carries the boundary of the product off `U x z y`, and
the image of `± ∂ μ x y`. The condition at `a` says that the local class of their difference
vanishes at `a`, and the local classes of a class along an open set vanish on whole preconnected
subsets as soon as they vanish at one of their points. So the condition holds on a whole
connected component of the face interior once it holds at one of its points
(`TauCeti.homologyMap_cubicalChainComplexMap_ofSubsetMap_eq_of_isPreconnected`).

The same reduction applies to the face conditions of continuation chain systems
(`TauCeti.ContinuationChainSystem.exists_isRepresenting_of_faces_of_connectedComponentIn`), on the
left faces `M x z × N z y` and the right faces `N x w × M' w y` of the spaces of continuation
trajectories, and of parametrized chain systems
(`TauCeti.ParametrizedChainSystem.exists_isRepresenting_of_faces_of_connectedComponentIn`), on
these two kinds of faces and on the two ends `N₀ x y` and `N₁ x y` of the spaces of trajectories of
a one-parameter family of homotopies. With integral coefficients and oriented interiors, a sign
convention on the orientations of the compactified trajectory spaces, such as that of Barraud,
Damian, Humilière and Oancea, therefore needs to be checked at one point of each component of each
face, for the trajectory spaces of a function, of a homotopy between two functions and of a
family of such homotopies alike.

## Main results

* `TauCeti.TwistingChainSystem.exists_isRepresenting_of_faces_of_connectedComponentIn`: a
  twisting chain system representing classes `μ` of spaces whose boundaries are compact manifolds
  glued from faces with open interiors exists when the face condition holds at one point of each
  connected component of each face interior.
* `TauCeti.ContinuationChainSystem.exists_isRepresenting_of_faces_of_connectedComponentIn`: the
  same for continuation chain systems between two representing twisting chain systems.
* `TauCeti.ParametrizedChainSystem.exists_isRepresenting_of_faces_of_connectedComponentIn`: the
  same for parametrized chain systems between two representing continuation chain systems.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Proposition 5.2.6 and the
  orientation relation (5.11), and Chapter 6, the continuation morphisms and their homotopies.
* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Annals of
  Mathematics 166 (2007), Lemma 2.2 and Appendix A.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set Topology MonoidalCategory
open scoped TensorProduct

universe u

namespace TauCeti

variable {k : Type u} [CommRing k] {P : Type*} [Fintype P] {ind : P → ℤ} {M : P → P → TopCat.{u}}
  {ι : ∀ x y z, C(M x y × M y z, M x z)} {A : ∀ x y, Set (M x y)}
  {μ : ∀ x y, ((TopPair.ofSubset (A x y)).cubicalChainComplex k).homology (ind x - ind y - 1).toNat}

/-- **Representing chain systems from the face condition on one point of each component.** Let
`μ x y` be classes of the relative homology `H_{ind x - ind y - 1}(M x y, A x y)`. Suppose that:

* each boundary `A x y` is a compact Hausdorff space charted on a finite-dimensional real normed
  space `E x y`, of dimension `ind x - ind y - 2` whenever `ind x - ind y ≥ 2`;
* the composition maps `ι x z y : M x z × M z y → M x y` are associative and, for `z` strictly
  between `y` and `x` in index, land in `A x y`;
* the sets `U x z y`, the interiors of the faces, are open in `A x y` and together dense in it, the
  face of every other `z'` strictly between `y` and `x` misses `U x z y`, and `ι x z y` carries
  `A x z × M z y ∪ M x z × A z y` off `U x z y`;
* every connected component of the interior `U x z y` of each face contains a point `b` at which
  the cross product of `μ x z` and `μ z y`, pushed forward along `ι x z y` to the local homology
  `H(A x y, A x y ∖ {b})`, is `(-1) ^ (ind x - ind z)` times the image of the boundary
  `∂ μ x y ∈ H(A x y)`.

Then some twisting chain system represents the classes `μ`. The coefficients are any commutative
ring. -/
theorem TwistingChainSystem.exists_isRepresenting_of_faces_of_connectedComponentIn
    {E : P → P → Type u} [∀ x y, NormedAddCommGroup (E x y)] [∀ x y, NormedSpace ℝ (E x y)]
    [∀ x y, FiniteDimensional ℝ (E x y)] [∀ x y, T2Space (A x y)] [∀ x y, CompactSpace (A x y)]
    [∀ x y, ChartedSpace (E x y) (A x y)]
    (hE : ∀ x y, ind y + 1 < ind x → Module.finrank ℝ (E x y) = (ind x - ind y - 2).toNat)
    (hι : ∀ x w z y (a : M x w) (b : M w z) (c : M z y),
      ι x z y (ι x w z (a, b), c) = ι x w y (a, ι w z y (b, c)))
    (hιA : ∀ x z y, ind y < ind z → ind z < ind x → ∀ p, ι x z y p ∈ A x y)
    (U : ∀ x, P → ∀ y, Set (M x y))
    (hUo : ∀ x z y, IsOpen (Subtype.val ⁻¹' U x z y : Set (A x y)))
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
      (_ : (a : M x y) ∈ U x z y),
      ∃ b ∈ connectedComponentIn (Subtype.val ⁻¹' U x z y) a, ∃ hb : (b : M x y) ∈ U x z y,
      (HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
          (TopPair.ofSubsetMap _ ((hUA x z y hyz hzx).mono_right
            (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 hb)))))
          (ind x - ind y - 2).toNat).hom
        ((HomologicalComplex.homologyMap
          ((TopPair.ofSubset (A x z)).cubicalChainComplexProdComparison k
            (TopPair.ofSubset (A z y))) (ind x - ind y - 2).toNat).hom
          ((GradedObject.Monoidal.ιTensorObj _ _ _ _ _ (by omega) ≫
            cubicalHomologyKunnethPair k _ _ _).hom (μ x z ⊗ₜ μ z y))) =
        (ind x - ind z).negOnePow •
          (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
            (TopPair.ofSubset ({b}ᶜ : Set (A x y))).map)) (ind x - ind y - 2).toNat).hom
            (((TopPair.ofSubset (A x y)).cubicalHomologyδ k _ _).hom (μ x y))) :
    ∃ S : TwistingChainSystem ind ι k, S.IsRepresenting A μ := by
  refine TwistingChainSystem.exists_isRepresenting_of_faces (E := E) hE hι hιA U hU hUι hUA
    fun x z y hyz hzx a ha ↦ ?_
  obtain ⟨b, hbC, _, hcond⟩ := hface x z y hyz hzx a ha
  -- The sign is carried by the absolute class `w = ±∂ μ x y`.
  refine (homologyMap_cubicalChainComplexMap_ofSubsetMap_eq_of_isPreconnected (E := E x y)
    (hUo x z y) isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _)
    (hUA x z y hyz hzx) _ ((ind x - ind z).negOnePow • _) hbC (mem_connectedComponentIn ha)
    (hcond.trans (map_zsmul_unit _ _ _).symm)).trans (map_zsmul_unit _ _ _)


section Continuation

variable {Q : Type*} [Fintype Q] {indQ : Q → ℤ} {M' : Q → Q → TopCat.{u}} {N : P → Q → TopCat.{u}}
  {ι' : ∀ x y z, C(M' x y × M' y z, M' x z)} {κ : ∀ x y z, C(M x y × N y z, N x z)}
  {κ' : ∀ x y z, C(N x y × M' y z, N x z)} {S : TwistingChainSystem ind ι k}
  {S' : TwistingChainSystem indQ ι' k} {A' : ∀ x y, Set (M' x y)} {B : ∀ x y, Set (N x y)}
  {μ' : ∀ x y, ((TopPair.ofSubset (A' x y)).cubicalChainComplex k).homology
    (indQ x - indQ y - 1).toNat}
  {ν : ∀ x y, ((TopPair.ofSubset (B x y)).cubicalChainComplex k).homology (ind x - indQ y).toNat}

/-- **Representing continuation chain systems from the face condition on one point of each
component.** Let `S` and `S'` be twisting chain systems representing classes `μ` and `μ'`, and let
`ν x y` be classes of `H_{ind x - indQ y}(N x y, B x y)`. Suppose that the boundaries `B x y`, the
composition maps `κ` and `κ'` and the interiors `U x z y` and `U' x w y` of the left and right
faces satisfy the hypotheses of `TauCeti.ContinuationChainSystem.exists_isRepresenting_of_faces`,
that the face interiors are open in `B x y`, and that every connected component of each face
interior contains a point `b` at which the face condition holds: on a left face the cross product
of `μ x z` and `ν z y`, pushed forward along `κ x z y` to the local homology
`H(B x y, B x y ∖ {b})`, is the image of the boundary `∂ ν x y`, and on a right face the cross
product of `ν x w` and `μ' w y`, pushed forward along `κ' x w y`, is `(-1) ^ (ind x - indQ w - 1)`
times that image. Then some continuation chain system from `S` to `S'` represents the classes `ν`.
The coefficients are any commutative ring. -/
theorem ContinuationChainSystem.exists_isRepresenting_of_faces_of_connectedComponentIn
    (hS : S.IsRepresenting A μ)
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
    (hUo : ∀ x z y, IsOpen (Subtype.val ⁻¹' U x z y : Set (B x y)))
    (hU'o : ∀ x w y, IsOpen (Subtype.val ⁻¹' U' x w y : Set (B x y)))
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
      (_ : (a : N x y) ∈ U x z y),
      ∃ b ∈ connectedComponentIn (Subtype.val ⁻¹' U x z y) a, ∃ hb : (b : N x y) ∈ U x z y,
      (HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
          (TopPair.ofSubsetMap _ ((hUB x z y hyz hzx).mono_right
            (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 hb)))))
          (ind x - indQ y - 1).toNat).hom
        ((HomologicalComplex.homologyMap
          ((TopPair.ofSubset (A x z)).cubicalChainComplexProdComparison k
            (TopPair.ofSubset (B z y))) (ind x - indQ y - 1).toNat).hom
          ((GradedObject.Monoidal.ιTensorObj _ _ _ _ _ (by omega) ≫
            cubicalHomologyKunnethPair k _ _ _).hom (μ x z ⊗ₜ ν z y))) =
        (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
          (TopPair.ofSubset ({b}ᶜ : Set (B x y))).map)) (ind x - indQ y - 1).toNat).hom
          (((TopPair.ofSubset (B x y)).cubicalHomologyδ k _ _).hom (ν x y)))
    (hface' : ∀ x w y (hyw : indQ y < indQ w) (hwx : indQ w ≤ ind x) (a : B x y)
      (_ : (a : N x y) ∈ U' x w y),
      ∃ b ∈ connectedComponentIn (Subtype.val ⁻¹' U' x w y) a, ∃ hb : (b : N x y) ∈ U' x w y,
      (HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
          (TopPair.ofSubsetMap _ ((hU'B x w y hyw hwx).mono_right
            (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 hb)))))
          (ind x - indQ y - 1).toNat).hom
        ((HomologicalComplex.homologyMap
          ((TopPair.ofSubset (B x w)).cubicalChainComplexProdComparison k
            (TopPair.ofSubset (A' w y))) (ind x - indQ y - 1).toNat).hom
          ((GradedObject.Monoidal.ιTensorObj _ _ _ _ _ (by omega) ≫
            cubicalHomologyKunnethPair k _ _ _).hom (ν x w ⊗ₜ μ' w y))) =
        (ind x - indQ w - 1).negOnePow •
          (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
            (TopPair.ofSubset ({b}ᶜ : Set (B x y))).map)) (ind x - indQ y - 1).toNat).hom
            (((TopPair.ofSubset (B x y)).cubicalHomologyδ k _ _).hom (ν x y))) :
    ∃ T : ContinuationChainSystem κ κ' S S', T.IsRepresenting B ν := by
  refine ContinuationChainSystem.exists_isRepresenting_of_faces hS hS' (E := E) hE hκ hκκ' hκ'
    hκB hκ'B U U' hU hUκ hUκ' hU'κ hU'κ' hUB hU'B (fun x z y hyz hzx a ha ↦ ?_)
    fun x w y hyw hwx a ha ↦ ?_
  · obtain ⟨b, hbC, _, hcond⟩ := hface x z y hyz hzx a ha
    exact homologyMap_cubicalChainComplexMap_ofSubsetMap_eq_of_isPreconnected (E := E x y)
      (hUo x z y) isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _)
      (hUB x z y hyz hzx) _ _ hbC (mem_connectedComponentIn ha) hcond
  · obtain ⟨b, hbC, _, hcond⟩ := hface' x w y hyw hwx a ha
    -- The sign is carried by the absolute class `w = ±∂ ν x y`.
    exact (homologyMap_cubicalChainComplexMap_ofSubsetMap_eq_of_isPreconnected (E := E x y)
      (hU'o x w y) isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _)
      (hU'B x w y hyw hwx) _ ((ind x - indQ w - 1).negOnePow • _) hbC
      (mem_connectedComponentIn ha) (hcond.trans (map_zsmul_unit _ _ _).symm)).trans
      (map_zsmul_unit _ _ _)

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

/-- **Representing parametrized chain systems from the face condition on one point of each
component.** Let `S` and `S'` be twisting chain systems representing classes `μ` and `μ'`, let
`T₀` and `T₁` be continuation chain systems from `S` to `S'` representing classes `ν₀` and `ν₁`,
and let `θ x y` be classes of `H_{ind x - indQ y + 1}(H x y, C x y)`. Suppose that the boundaries
`C x y`, the composition maps `κH` and `κH'`, the inclusions `j₀` and `j₁` of the two ends, and the
interiors `V₀ x y`, `V₁ x y`, `U x z y` and `U' x w y` of the two ends and of the left and right
faces satisfy the hypotheses of `TauCeti.ParametrizedChainSystem.exists_isRepresenting_of_faces`,
that these interiors are open in `C x y`, and that every connected component of each of them
contains a point `b` at which the face condition holds: the image of the class of the face in the
local homology `H(C x y, C x y ∖ {b})` is the image of the boundary `∂ θ x y` with the sign `-1`
for `ν₀ x y` on the end `j₀`, `+1` for `ν₁ x y` on the end `j₁`, `(-1) ^ (ind x - ind z)` for the
cross product of `μ x z` and `θ z y` on a left face, and `(-1) ^ (ind x - indQ w)` for the cross
product of `θ x w` and `μ' w y` on a right face. Then some parametrized chain system between `T₀`
and `T₁` represents the classes `θ`. The coefficients are any commutative ring. -/
theorem ParametrizedChainSystem.exists_isRepresenting_of_faces_of_connectedComponentIn
    (hS : S.IsRepresenting A μ)
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
    (hV₀o : ∀ x y, IsOpen (Subtype.val ⁻¹' V₀ x y : Set (C x y)))
    (hV₁o : ∀ x y, IsOpen (Subtype.val ⁻¹' V₁ x y : Set (C x y)))
    (hUo : ∀ x z y, IsOpen (Subtype.val ⁻¹' U x z y : Set (C x y)))
    (hU'o : ∀ x w y, IsOpen (Subtype.val ⁻¹' U' x w y : Set (C x y)))
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
    (hface₀ : ∀ x y (hxy : indQ y ≤ ind x) (a : C x y) (_ : (a : H x y) ∈ V₀ x y),
      ∃ b ∈ connectedComponentIn (Subtype.val ⁻¹' V₀ x y) a, ∃ hb : (b : H x y) ∈ V₀ x y,
      (HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
          (TopPair.ofSubsetMap _ ((hV₀B x y hxy).mono_right
            (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 hb)))))
          (ind x - indQ y).toNat).hom (ν₀ x y) =
        -(HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
          (TopPair.ofSubset ({b}ᶜ : Set (C x y))).map)) (ind x - indQ y).toNat).hom
          (((TopPair.ofSubset (C x y)).cubicalHomologyδ k (ind x - indQ y + 1).toNat
            (ind x - indQ y).toNat (by omega)).hom (θ x y)))
    (hface₁ : ∀ x y (hxy : indQ y ≤ ind x) (a : C x y) (_ : (a : H x y) ∈ V₁ x y),
      ∃ b ∈ connectedComponentIn (Subtype.val ⁻¹' V₁ x y) a, ∃ hb : (b : H x y) ∈ V₁ x y,
      (HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
          (TopPair.ofSubsetMap _ ((hV₁B x y hxy).mono_right
            (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 hb)))))
          (ind x - indQ y).toNat).hom (ν₁ x y) =
        (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
          (TopPair.ofSubset ({b}ᶜ : Set (C x y))).map)) (ind x - indQ y).toNat).hom
          (((TopPair.ofSubset (C x y)).cubicalHomologyδ k (ind x - indQ y + 1).toNat
            (ind x - indQ y).toNat (by omega)).hom (θ x y)))
    (hface : ∀ x z y (hyz : indQ y ≤ ind z + 1) (hzx : ind z < ind x) (a : C x y)
      (_ : (a : H x y) ∈ U x z y),
      ∃ b ∈ connectedComponentIn (Subtype.val ⁻¹' U x z y) a, ∃ hb : (b : H x y) ∈ U x z y,
      (HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
          (TopPair.ofSubsetMap _ ((hUC x z y hyz hzx).mono_right
            (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 hb)))))
          (ind x - indQ y).toNat).hom
        ((HomologicalComplex.homologyMap
          ((TopPair.ofSubset (A x z)).cubicalChainComplexProdComparison k
            (TopPair.ofSubset (C z y))) (ind x - indQ y).toNat).hom
          ((GradedObject.Monoidal.ιTensorObj _ _ _ _ _ (by omega) ≫
            cubicalHomologyKunnethPair k _ _ _).hom (μ x z ⊗ₜ θ z y))) =
        (ind x - ind z).negOnePow •
          (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
            (TopPair.ofSubset ({b}ᶜ : Set (C x y))).map)) (ind x - indQ y).toNat).hom
            (((TopPair.ofSubset (C x y)).cubicalHomologyδ k (ind x - indQ y + 1).toNat
            (ind x - indQ y).toNat (by omega)).hom (θ x y)))
    (hface' : ∀ x w y (hyw : indQ y < indQ w) (hwx : indQ w ≤ ind x + 1) (a : C x y)
      (_ : (a : H x y) ∈ U' x w y),
      ∃ b ∈ connectedComponentIn (Subtype.val ⁻¹' U' x w y) a, ∃ hb : (b : H x y) ∈ U' x w y,
      (HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
          (TopPair.ofSubsetMap _ ((hU'C x w y hyw hwx).mono_right
            (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 hb)))))
          (ind x - indQ y).toNat).hom
        ((HomologicalComplex.homologyMap
          ((TopPair.ofSubset (C x w)).cubicalChainComplexProdComparison k
            (TopPair.ofSubset (A' w y))) (ind x - indQ y).toNat).hom
          ((GradedObject.Monoidal.ιTensorObj _ _ _ _ _ (by omega) ≫
            cubicalHomologyKunnethPair k _ _ _).hom (θ x w ⊗ₜ μ' w y))) =
        (ind x - indQ w).negOnePow •
          (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
            (TopPair.ofSubset ({b}ᶜ : Set (C x y))).map)) (ind x - indQ y).toNat).hom
            (((TopPair.ofSubset (C x y)).cubicalHomologyδ k (ind x - indQ y + 1).toNat
            (ind x - indQ y).toNat (by omega)).hom (θ x y))) :
    ∃ η : ParametrizedChainSystem κH κH' j₀ j₁ T₀ T₁, η.IsRepresenting C θ := by
  refine ParametrizedChainSystem.exists_isRepresenting_of_faces hS hS' hT₀ hT₁ (E := E) hE hκH
    hκHκH' hκH' hj₀κ hj₀κ' hj₁κ hj₁κ' hj₀C hj₁C hκHC hκH'C V₀ V₁ U U' hU hV₀j₁ hV₀κH hV₀κH'
    hV₁j₀ hV₁κH hV₁κH' hUj₀ hUj₁ hUκH hUκH' hU'j₀ hU'j₁ hU'κH hU'κH' hV₀B hV₁B hUC hU'C
    (fun x y hxy a ha ↦ ?_) (fun x y hxy a ha ↦ ?_) (fun x z y hyz hzx a ha ↦ ?_)
    fun x w y hyw hwx a ha ↦ ?_
  -- On each kind of face, the sign is carried by the absolute class `w = ±∂ θ x y`.
  · obtain ⟨b, hbC, _, hcond⟩ := hface₀ x y hxy a ha
    exact (homologyMap_cubicalChainComplexMap_ofSubsetMap_eq_of_isPreconnected (E := E x y)
      (hV₀o x y) isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _)
      (hV₀B x y hxy) _ (-_) hbC (mem_connectedComponentIn ha)
      (hcond.trans (map_neg _ _).symm)).trans (map_neg _ _)
  · obtain ⟨b, hbC, _, hcond⟩ := hface₁ x y hxy a ha
    exact homologyMap_cubicalChainComplexMap_ofSubsetMap_eq_of_isPreconnected (E := E x y)
      (hV₁o x y) isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _)
      (hV₁B x y hxy) _ _ hbC (mem_connectedComponentIn ha) hcond
  · obtain ⟨b, hbC, _, hcond⟩ := hface x z y hyz hzx a ha
    exact (homologyMap_cubicalChainComplexMap_ofSubsetMap_eq_of_isPreconnected (E := E x y)
      (hUo x z y) isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _)
      (hUC x z y hyz hzx) _ ((ind x - ind z).negOnePow • _) hbC (mem_connectedComponentIn ha)
      (hcond.trans (map_zsmul_unit _ _ _).symm)).trans (map_zsmul_unit _ _ _)
  · obtain ⟨b, hbC, _, hcond⟩ := hface' x w y hyw hwx a ha
    exact (homologyMap_cubicalChainComplexMap_ofSubsetMap_eq_of_isPreconnected (E := E x y)
      (hU'o x w y) isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _)
      (hU'C x w y hyw hwx) _ ((ind x - indQ w).negOnePow • _) hbC (mem_connectedComponentIn ha)
      (hcond.trans (map_zsmul_unit _ _ _).symm)).trans (map_zsmul_unit _ _ _)

end Parametrized

end TauCeti

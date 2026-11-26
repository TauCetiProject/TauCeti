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
the image of `∂ μ x y`. The condition at `a` says that the local class of their difference
vanishes at `a`, and the local classes of a class along an open set vanish on whole preconnected
subsets as soon as they vanish at one of their points
(`TauCeti.homologyMap_cubicalChainComplexMap_eq_zero_of_isPreconnected`). So the condition holds
on a whole connected component of the face interior once it holds at one of its points. With
integral coefficients and oriented interiors, a sign convention on the orientations of the
compactified trajectory spaces, such as that of Barraud, Damian, Humilière and Oancea, therefore
needs to be checked at one point of each component of each face.

## Main results

* `TauCeti.TwistingChainSystem.exists_isRepresenting_of_faces_of_connectedComponentIn`: a
  twisting chain system representing classes `μ` of spaces whose boundaries are compact manifolds
  glued from faces with open interiors exists when the face condition holds at one point of each
  connected component of each face interior.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Proposition 5.2.6 and the
  orientation relation (5.11).
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
  obtain ⟨b, hbC, hb, hcond⟩ := hface x z y hyz hzx a ha
  set m := (ind x - ind y - 2).toNat
  -- The restriction from the local homology along the face interior to that at a point `c` of it.
  let ρ (c : A x y) (hc : (c : M x y) ∈ U x z y) :
      TopPair.ofSubset (X := TopCat.of (A x y)) (Subtype.val ⁻¹' U x z y)ᶜ ⟶
        TopPair.ofSubset (X := TopCat.of (A x y)) {c}ᶜ :=
    TopPair.ofSubsetMap (𝟙 (TopCat.of (A x y)))
      (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 hc))
  -- Both sides of the face condition at `c` factor through the local homology along the face
  -- interior: the composition map carries the boundary of the product off it.
  have hL (c : A x y) (hc : (c : M x y) ∈ U x z y) v :
      (HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
          (TopPair.ofSubsetMap _ ((hUA x z y hyz hzx).mono_right
            (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 hc))))) m).hom v =
      (HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k (ρ c hc)) m).hom
        ((HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
          (TopPair.ofSubsetMap _ (hUA x z y hyz hzx))) m).hom v) :=
    (TopPair.homologyMap_cubicalChainComplexMap_ofSubsetMap_apply_of_comp_eq _ _ _
      (Category.comp_id _) m v).symm
  have hR (c : A x y) (hc : (c : M x y) ∈ U x z y) :
      (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
          (TopPair.ofSubset ({c}ᶜ : Set (A x y))).map)) m).hom
        (((TopPair.ofSubset (A x y)).cubicalHomologyδ k _ _).hom (μ x y)) =
      (HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k (ρ c hc)) m).hom
        ((HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
          (TopPair.ofSubset (X := TopCat.of (A x y)) (Subtype.val ⁻¹' U x z y)ᶜ).map)) m).hom
          (((TopPair.ofSubset (A x y)).cubicalHomologyδ k _ _).hom (μ x y))) := by
    -- Restricting along `ρ c hc` turns the class relative to the face interior into the class
    -- relative to the complement of `c`.
    have e (v) := congr((HomologicalComplex.homologyMap
      $(TopPair.π_cubicalChainComplexMap_ofSubsetMap_id k (X := TopCat.of (A x y))
        (B := (Subtype.val ⁻¹' U x z y)ᶜ) (B' := {c}ᶜ)
        (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 hc))) m).hom v)
    simp only [HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at e
    exact (e _).symm
  -- So the face condition at `c` is the vanishing at `c` of the local class of one class along the
  -- face interior, the difference of the two sides.
  rw [hL a ha, hR a ha]
  rw [hL b hb, hR b hb] at hcond
  rw [Units.smul_def, ← map_zsmul, ← sub_eq_zero, ← map_sub] at hcond ⊢
  exact homologyMap_cubicalChainComplexMap_eq_zero_of_isPreconnected (E := E x y) (hUo x z y)
    isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _) hbC
    (mem_connectedComponentIn ha) hcond

end TauCeti

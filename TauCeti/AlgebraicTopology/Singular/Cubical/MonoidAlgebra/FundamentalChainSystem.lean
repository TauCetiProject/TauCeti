/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.FaceGluing
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Cubical
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Prod
import TauCeti.Algebra.Ring.NegOnePow

/-!
# Representing chain systems of fundamental classes when `1` is the only unit

Let `M x y` be compact Hausdorff spaces, indexed by pairs of elements of a finite set `P` graded by
`ind`, each containing a manifold `O x y` of dimension `ind x - ind y - 1` as an open subset whose
complement `∂ M x y` is collared, such as the compactified trajectory spaces of a Morse function.
With coefficients in a commutative ring `k` whose only unit is `1`, such as `ZMod 2`, let
`μ x y ∈ H(M x y, ∂ M x y; k)` generate the local homology at every interior point, as the mod `2`
fundamental class relative to the boundary does
(`TauCeti.existsUnique_span_localHomologyRestriction_range_eq_top`). Suppose that the boundary is a
closed manifold of dimension `ind x - ind y - 2`, glued along the composition maps
`ι x z y : M x z × M z y → M x y` from faces whose interiors are the images of `O x z × O z y`.
Then some twisting chain system represents the classes `μ`
(`TauCeti.TwistingChainSystem.exists_isRepresenting_of_subsingleton_units`): the fundamental
chains rel boundary can be chosen so that the boundary of each is the sum of the cross products of
the fundamental chains of its faces.

This discharges the face condition of `TauCeti.TwistingChainSystem.exists_isRepresenting_of_faces`
at each interior point `a` of a face. In the local homology `H(∂ M x y, ∂ M x y ∖ {a}; k) ≅ k`:

* the image of the boundary `∂ μ x y` generates
  (`TauCeti.span_homologyMap_cubicalHomologyδ_eq_top`), the cubical form of
  `TauCeti.isFundamentalClass_singularHomologyδ_of_forall_span_eq_top`;
* the image of the cross product `μ x z × μ z y` under the face map generates
  (`TauCeti.span_homologyMap_cubicalChainComplexMap_cubicalHomologyKunnethPair_eq_top`): by the
  Künneth theorem for the local pairs
  (`TauCeti.span_homologyMap_cubicalHomologyKunnethPair_tmul_eq_top`) it generates the local
  homology of the product at the preimage of `a`, and the face map is an open embedding near that
  point
  (`TauCeti.isIso_localHomologyMap_singleton_of_isOpenEmbedding_comp`);
* a module isomorphic to `k` has only one generator when `1` is the only unit of `k`
  (`TauCeti.eq_of_span_cubicalHomology_eq_top`), and the sign `(-1) ^ (ind x - ind z)` acts
  trivially, since `-1 = 1` in `k`.

The same discharge applies to the left faces `M x z × N z y` and the right faces
`N x w × M' w y` of the spaces `N x y` of continuation trajectories, so representing continuation
chain systems of fundamental classes exist between two representing twisting chain systems
(`TauCeti.ContinuationChainSystem.exists_isRepresenting_of_subsingleton_units`). The Künneth step
uses the dimension of the first factor of each face only.

No orientations enter: with integral coefficients the face condition compares the boundary
orientation of each face with its product orientation, which is not done here.

## Main results

* `TauCeti.TwistingChainSystem.exists_isRepresenting_of_subsingleton_units`: representing twisting
  chain systems of fundamental classes exist when `1` is the only unit of the coefficients.
* `TauCeti.ContinuationChainSystem.exists_isRepresenting_of_subsingleton_units`: so do
  representing continuation chain systems.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Annals of
  Mathematics 166 (2007), Lemma 2.2 and Appendix A, the representing chain systems of
  compactified trajectory spaces over `ℤ/2`.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Proposition 5.2.6.
* A. Hatcher, *Algebraic Topology*, Section 3.3, the mod `2` fundamental class.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set Topology MonoidalCategory TopPair HomologicalComplex
open scoped TensorProduct

universe u

namespace TauCeti

variable {k : Type u} [CommRing k]

variable {P : Type*} [Fintype P] {ind : P → ℤ} {M : P → P → TopCat.{u}}
  {ι : ∀ x y z, C(M x y × M y z, M x z)}

/-- **Representing chain systems of fundamental classes when `1` is the only unit.** Let `k` be a
commutative ring whose only unit is `1`, such as `ZMod 2`. Suppose that:

* each `M x y` is a compact Hausdorff space containing an open subset `j x y (N x y)`, a copy of
  `N x y`, whose complement is the boundary `∂ M x y`; when `ind y < ind x`, `N x y` is a manifold
  of dimension `ind x - ind y - 1`, and when `ind y + 1 < ind x`, `∂ M x y` is collared and a
  manifold of dimension `ind x - ind y - 2`;
* when `ind y < ind x`, `μ x y ∈ H(M x y, ∂ M x y; k)` generates the local homology at every
  interior point, as the fundamental class relative to the boundary does;
* the composition maps `ι x z y : M x z × M z y → M x y` are associative, land in `∂ M x y`, and are
  open embeddings into `∂ M x y` on the interiors `N x z × N z y`;
* the images of these interiors, the interiors of the faces, are together dense in `∂ M x y`, the
  face of every other `z'` misses the interior of the face of `z`, and `ι x z y` carries the
  boundary `∂ M x z × M z y ∪ M x z × ∂ M z y` of the product off the interior of its face.

Then some twisting chain system represents the classes `μ`. For the compactified trajectory
spaces of a Morse function this is the existence of representing chain systems over `ℤ/2`
(Barraud–Cornea, Lemma 2.2; BDHO, Proposition 5.2.6). -/
theorem TwistingChainSystem.exists_isRepresenting_of_subsingleton_units [Subsingleton kˣ]
    [∀ x y, T2Space (M x y)] [∀ x y, CompactSpace (M x y)]
    {N : P → P → Type u} [∀ x y, TopologicalSpace (N x y)] {j : ∀ x y, N x y → M x y}
    (hj : ∀ x y, IsOpenEmbedding (j x y))
    {F : P → P → Type u} [∀ x y, NormedAddCommGroup (F x y)] [∀ x y, NormedSpace ℝ (F x y)]
    [∀ x y, FiniteDimensional ℝ (F x y)] [∀ x y, ChartedSpace (F x y) (N x y)]
    (hF : ∀ x y, ind y < ind x → finrank ℝ (F x y) = (ind x - ind y - 1).toNat)
    {E : P → P → Type u} [∀ x y, NormedAddCommGroup (E x y)] [∀ x y, NormedSpace ℝ (E x y)]
    [∀ x y, FiniteDimensional ℝ (E x y)] [∀ x y, ChartedSpace (E x y) ↥(range (j x y))ᶜ]
    (hE : ∀ x y, ind y + 1 < ind x → finrank ℝ (E x y) = (ind x - ind y - 2).toNat)
    (hcol : ∀ x y, ind y + 1 < ind x → IsCollared (Subtype.val : ↥(range (j x y))ᶜ → M x y))
    {μ : ∀ x y, ((TopPair.ofSubset (range (j x y))ᶜ).cubicalChainComplex k).homology
      (ind x - ind y - 1).toNat}
    (hμ : ∀ x y, ind y < ind x → ∀ r : N x y, (k ∙ localHomologyRestriction (ModuleCat.of k k)
      (singleton_subset_iff.2 (mem_range_self r)) _
        ((TopPair.singularCubicalHomologyIso k _ _).inv.hom (μ x y))) = ⊤)
    (hι : ∀ x w z y (a : M x w) (b : M w z) (c : M z y),
      ι x z y (ι x w z (a, b), c) = ι x w y (a, ι w z y (b, c)))
    (hιA : ∀ x z y, ind y < ind z → ind z < ind x → ∀ p, ι x z y p ∈ (range (j x y))ᶜ)
    (hιj : ∀ x z y (hyz : ind y < ind z) (hzx : ind z < ind x),
      IsOpenEmbedding fun r : N x z × N z y ↦
        (ι x z y).codRestrict (range (j x y))ᶜ (hιA x z y hyz hzx) (j x z r.1, j z y r.2))
    (hU : ∀ x y, ind y + 1 < ind x → Dense {a : ↥(range (j x y))ᶜ | ∃ z, ind y < ind z ∧
      ind z < ind x ∧ (a : M x y) ∈ range fun r : N x z × N z y ↦ ι x z y (j x z r.1, j z y r.2)})
    (hUι : ∀ x z z' y, ind y < ind z' → ind z' < ind x → z' ≠ z →
      Disjoint (range (ι x z' y)) (range fun r : N x z × N z y ↦ ι x z y (j x z r.1, j z y r.2)))
    (hUA : ∀ x z y (hyz : ind y < ind z) (hzx : ind z < ind x),
      MapsTo (TopCat.ofHom (X := ↑((TopPair.ofSubset (range (j x z))ᶜ).fst ⊗
          (TopPair.ofSubset (range (j z y))ᶜ).fst))
          ((ι x z y).codRestrict (range (j x y))ᶜ (hιA x z y hyz hzx)))
        ((TopPair.ofSubset (range (j x z))ᶜ).prodSubspace (TopPair.ofSubset (range (j z y))ᶜ))
        (Subtype.val ⁻¹' range fun r : N x z × N z y ↦ ι x z y (j x z r.1, j z y r.2))ᶜ) :
    ∃ S : TwistingChainSystem ind ι k, S.IsRepresenting (fun x y ↦ (range (j x y))ᶜ) μ := by
  have (x y : P) : CompactSpace ↥(range (j x y))ᶜ :=
    isCompact_iff_compactSpace.1 (hj x y).isOpen_range.isClosed_compl.isCompact
  refine TwistingChainSystem.exists_isRepresenting_of_faces (E := E) hE hι hιA
    (fun x z y ↦ range fun r : N x z × N z y ↦ ι x z y (j x z r.1, j z y r.2)) hU hUι hUA
    fun x z y hyz hzx a ha ↦ ?_
  obtain ⟨r, hr⟩ := ha
  obtain rfl : a = (ι x z y).codRestrict (range (j x y))ᶜ (hιA x z y hyz hzx)
      (j x z r.1, j z y r.2) :=
    Subtype.ext (hr.symm.trans (ContinuousMap.coe_codRestrict_apply _ _ _ _).symm)
  -- Both sides generate the local homology of the boundary at `a`, which has a single generator.
  rw [negOnePow_smul_eq_self_of_neg_one_eq_one
    (congrArg Units.val (Subsingleton.elim (-1 : kˣ) 1))]
  exact eq_of_span_cubicalHomology_eq_top (hE x y (by omega)) _
    (span_homologyMap_cubicalChainComplexMap_cubicalHomologyKunnethPair_eq_top (hj x z) (hj z y)
      (hF x z hzx) (by omega) (μ x z) (μ z y) _ (hιj x z y hyz hzx) r (hμ x z hzx r.1)
      (hμ z y hyz r.2) _)
    (span_homologyMap_cubicalHomologyδ_eq_top (hcol x y (by omega)) (by omega) (μ x y)
      (hμ x y (by omega)) _)

section Continuation

variable {Q : Type*} [Fintype Q] {indQ : Q → ℤ} {M' : Q → Q → TopCat.{u}} {N : P → Q → TopCat.{u}}
  {ι' : ∀ x y z, C(M' x y × M' y z, M' x z)} {κ : ∀ x y z, C(M x y × N y z, N x z)}
  {κ' : ∀ x y z, C(N x y × M' y z, N x z)} {S : TwistingChainSystem ind ι k}
  {S' : TwistingChainSystem indQ ι' k}

/-- **Representing continuation chain systems of fundamental classes when `1` is the only unit.**
Let `k` be a commutative ring whose only unit is `1`, such as `ZMod 2`, and let `S` and `S'` be
twisting chain systems representing classes `μ x y ∈ H(M x y, ∂ M x y; k)` and
`μ' x y ∈ H(M' x y, ∂ M' x y; k)`, where `∂ M x y` is the complement of an open subset
`o x y (O x y)` and `∂ M' x y` that of `o' x y (O' x y)`. Suppose that:

* when `ind y < ind x`, `O x y` is a manifold of dimension `ind x - ind y - 1` and `μ x y`
  generates the local homology at every point of `O x y`, and when `indQ y < indQ x`, `μ' x y`
  generates the local homology at every point of `O' x y`, as fundamental classes relative to the
  boundary do;
* each `N x y` is a compact Hausdorff space containing an open subset `j x y (W x y)`, a copy of
  `W x y`, whose complement is the boundary `∂ N x y`; when `indQ y ≤ ind x`, `W x y` is a
  manifold of dimension `ind x - indQ y` and `ν x y ∈ H(N x y, ∂ N x y; k)` generates the local
  homology at every point of `W x y`, and when `indQ y < ind x`, `∂ N x y` is collared and a
  manifold of dimension `ind x - indQ y - 1`;
* the composition maps `κ x z y : M x z × N z y → N x y` and `κ' x w y : N x w × M' w y → N x y`
  are associative, land in `∂ N x y` for `indQ y ≤ ind z < ind x` and `indQ y < indQ w ≤ ind x`,
  and are open embeddings into `∂ N x y` on the interiors `O x z × W z y` and `W x w × O' w y`;
* the images of these interiors, the interiors of the faces, are together dense in `∂ N x y`, the
  face of every other `z'` or `w'` misses the interior of each face, and `κ x z y` and
  `κ' x w y` carry the boundaries `∂ M x z × N z y ∪ M x z × ∂ N z y` and
  `∂ N x w × M' w y ∪ N x w × ∂ M' w y` of the products off the interiors of their faces.

Then some continuation chain system from `S` to `S'` represents the classes `ν`. For the
compactified spaces of continuation trajectories of a homotopy between two Morse functions, this
is the existence over `ℤ/2` of the fundamental chains whose push-forwards form the continuation
cocycle between the Barraud–Cornea cocycles of the two functions. -/
theorem ContinuationChainSystem.exists_isRepresenting_of_subsingleton_units [Subsingleton kˣ]
    [∀ x y, T1Space (M x y)] [∀ x y, T1Space (M' x y)] [∀ x y, T2Space (N x y)]
    [∀ x y, CompactSpace (N x y)]
    {O : P → P → Type u} [∀ x y, TopologicalSpace (O x y)] {o : ∀ x y, O x y → M x y}
    (ho : ∀ x y, IsOpenEmbedding (o x y))
    {F : P → P → Type u} [∀ x y, NormedAddCommGroup (F x y)] [∀ x y, NormedSpace ℝ (F x y)]
    [∀ x y, FiniteDimensional ℝ (F x y)] [∀ x y, ChartedSpace (F x y) (O x y)]
    (hF : ∀ x y, ind y < ind x → finrank ℝ (F x y) = (ind x - ind y - 1).toNat)
    {μ : ∀ x y, ((TopPair.ofSubset (range (o x y))ᶜ).cubicalChainComplex k).homology
      (ind x - ind y - 1).toNat}
    (hμ : ∀ x y, ind y < ind x → ∀ r : O x y, (k ∙ localHomologyRestriction (ModuleCat.of k k)
      (singleton_subset_iff.2 (mem_range_self r)) _
        ((TopPair.singularCubicalHomologyIso k _ _).inv.hom (μ x y))) = ⊤)
    (hS : S.IsRepresenting (fun x y ↦ (range (o x y))ᶜ) μ)
    {O' : Q → Q → Type u} [∀ x y, TopologicalSpace (O' x y)] {o' : ∀ x y, O' x y → M' x y}
    (ho' : ∀ x y, IsOpenEmbedding (o' x y))
    {μ' : ∀ x y, ((TopPair.ofSubset (range (o' x y))ᶜ).cubicalChainComplex k).homology
      (indQ x - indQ y - 1).toNat}
    (hμ' : ∀ x y, indQ y < indQ x → ∀ r : O' x y, (k ∙ localHomologyRestriction (ModuleCat.of k k)
      (singleton_subset_iff.2 (mem_range_self r)) _
        ((TopPair.singularCubicalHomologyIso k _ _).inv.hom (μ' x y))) = ⊤)
    (hS' : S'.IsRepresenting (fun x y ↦ (range (o' x y))ᶜ) μ')
    {W : P → Q → Type u} [∀ x y, TopologicalSpace (W x y)] {j : ∀ x y, W x y → N x y}
    (hj : ∀ x y, IsOpenEmbedding (j x y))
    {G : P → Q → Type u} [∀ x y, NormedAddCommGroup (G x y)] [∀ x y, NormedSpace ℝ (G x y)]
    [∀ x y, FiniteDimensional ℝ (G x y)] [∀ x y, ChartedSpace (G x y) (W x y)]
    (hG : ∀ x y, indQ y ≤ ind x → finrank ℝ (G x y) = (ind x - indQ y).toNat)
    {E : P → Q → Type u} [∀ x y, NormedAddCommGroup (E x y)] [∀ x y, NormedSpace ℝ (E x y)]
    [∀ x y, FiniteDimensional ℝ (E x y)] [∀ x y, ChartedSpace (E x y) ↥(range (j x y))ᶜ]
    (hE : ∀ x y, indQ y < ind x → finrank ℝ (E x y) = (ind x - indQ y - 1).toNat)
    (hcol : ∀ x y, indQ y < ind x → IsCollared (Subtype.val : ↥(range (j x y))ᶜ → N x y))
    {ν : ∀ x y, ((TopPair.ofSubset (range (j x y))ᶜ).cubicalChainComplex k).homology
      (ind x - indQ y).toNat}
    (hν : ∀ x y, indQ y ≤ ind x → ∀ r : W x y, (k ∙ localHomologyRestriction (ModuleCat.of k k)
      (singleton_subset_iff.2 (mem_range_self r)) _
        ((TopPair.singularCubicalHomologyIso k _ _).inv.hom (ν x y))) = ⊤)
    (hκ : ∀ x w z y (a : M x w) (b : M w z) (c : N z y),
      κ x z y (ι x w z (a, b), c) = κ x w y (a, κ w z y (b, c)))
    (hκκ' : ∀ x w z y (a : M x w) (b : N w z) (c : M' z y),
      κ' x z y (κ x w z (a, b), c) = κ x w y (a, κ' w z y (b, c)))
    (hκ' : ∀ x w z y (a : N x w) (b : M' w z) (c : M' z y),
      κ' x z y (κ' x w z (a, b), c) = κ' x w y (a, ι' w z y (b, c)))
    (hκB : ∀ x z y, indQ y ≤ ind z → ind z < ind x → ∀ p, κ x z y p ∈ (range (j x y))ᶜ)
    (hκ'B : ∀ x w y, indQ y < indQ w → indQ w ≤ ind x → ∀ p, κ' x w y p ∈ (range (j x y))ᶜ)
    (hκj : ∀ x z y (hyz : indQ y ≤ ind z) (hzx : ind z < ind x),
      IsOpenEmbedding fun r : O x z × W z y ↦
        (κ x z y).codRestrict (range (j x y))ᶜ (hκB x z y hyz hzx) (o x z r.1, j z y r.2))
    (hκ'j : ∀ x w y (hyw : indQ y < indQ w) (hwx : indQ w ≤ ind x),
      IsOpenEmbedding fun r : W x w × O' w y ↦
        (κ' x w y).codRestrict (range (j x y))ᶜ (hκ'B x w y hyw hwx) (j x w r.1, o' w y r.2))
    (hU : ∀ x y, indQ y < ind x → Dense {a : ↥(range (j x y))ᶜ |
      (∃ z, indQ y ≤ ind z ∧ ind z < ind x ∧
        (a : N x y) ∈ range fun r : O x z × W z y ↦ κ x z y (o x z r.1, j z y r.2)) ∨
      ∃ w, indQ y < indQ w ∧ indQ w ≤ ind x ∧
        (a : N x y) ∈ range fun r : W x w × O' w y ↦ κ' x w y (j x w r.1, o' w y r.2)})
    (hUκ : ∀ x z z' y, indQ y ≤ ind z' → ind z' < ind x → z' ≠ z →
      Disjoint (range (κ x z' y)) (range fun r : O x z × W z y ↦ κ x z y (o x z r.1, j z y r.2)))
    (hUκ' : ∀ x z w y, indQ y < indQ w → indQ w ≤ ind x →
      Disjoint (range (κ' x w y)) (range fun r : O x z × W z y ↦ κ x z y (o x z r.1, j z y r.2)))
    (hU'κ : ∀ x w z y, indQ y ≤ ind z → ind z < ind x →
      Disjoint (range (κ x z y))
        (range fun r : W x w × O' w y ↦ κ' x w y (j x w r.1, o' w y r.2)))
    (hU'κ' : ∀ x w w' y, indQ y < indQ w' → indQ w' ≤ ind x → w' ≠ w →
      Disjoint (range (κ' x w' y))
        (range fun r : W x w × O' w y ↦ κ' x w y (j x w r.1, o' w y r.2)))
    (hUB : ∀ x z y (hyz : indQ y ≤ ind z) (hzx : ind z < ind x),
      MapsTo (TopCat.ofHom (X := ↑((TopPair.ofSubset (range (o x z))ᶜ).fst ⊗
          (TopPair.ofSubset (range (j z y))ᶜ).fst))
          ((κ x z y).codRestrict (range (j x y))ᶜ (hκB x z y hyz hzx)))
        ((TopPair.ofSubset (range (o x z))ᶜ).prodSubspace (TopPair.ofSubset (range (j z y))ᶜ))
        (Subtype.val ⁻¹' range fun r : O x z × W z y ↦ κ x z y (o x z r.1, j z y r.2))ᶜ)
    (hU'B : ∀ x w y (hyw : indQ y < indQ w) (hwx : indQ w ≤ ind x),
      MapsTo (TopCat.ofHom (X := ↑((TopPair.ofSubset (range (j x w))ᶜ).fst ⊗
          (TopPair.ofSubset (range (o' w y))ᶜ).fst))
          ((κ' x w y).codRestrict (range (j x y))ᶜ (hκ'B x w y hyw hwx)))
        ((TopPair.ofSubset (range (j x w))ᶜ).prodSubspace (TopPair.ofSubset (range (o' w y))ᶜ))
        (Subtype.val ⁻¹' range fun r : W x w × O' w y ↦ κ' x w y (j x w r.1, o' w y r.2))ᶜ) :
    ∃ T : ContinuationChainSystem κ κ' S S', T.IsRepresenting (fun x y ↦ (range (j x y))ᶜ) ν := by
  have (x : P) (y : Q) : CompactSpace ↥(range (j x y))ᶜ :=
    isCompact_iff_compactSpace.1 (hj x y).isOpen_range.isClosed_compl.isCompact
  refine ContinuationChainSystem.exists_isRepresenting_of_faces hS hS' (E := E) hE hκ hκκ' hκ'
    hκB hκ'B (fun x z y ↦ range fun r : O x z × W z y ↦ κ x z y (o x z r.1, j z y r.2))
    (fun x w y ↦ range fun r : W x w × O' w y ↦ κ' x w y (j x w r.1, o' w y r.2)) hU hUκ hUκ'
    hU'κ hU'κ' hUB hU'B (fun x z y hyz hzx a ha ↦ ?_) fun x w y hyw hwx a ha ↦ ?_
  · obtain ⟨r, hr⟩ := ha
    obtain rfl : a = (κ x z y).codRestrict (range (j x y))ᶜ (hκB x z y hyz hzx)
        (o x z r.1, j z y r.2) :=
      Subtype.ext (hr.symm.trans (ContinuousMap.coe_codRestrict_apply _ _ _ _).symm)
    -- Both sides generate the local homology of the boundary at `a`, which has a single generator.
    exact eq_of_span_cubicalHomology_eq_top (hE x y (by omega)) _
      (span_homologyMap_cubicalChainComplexMap_cubicalHomologyKunnethPair_eq_top (ho x z) (hj z y)
        (hF x z hzx) (by omega) (μ x z) (ν z y) _ (hκj x z y hyz hzx) r (hμ x z hzx r.1)
        (hν z y hyz r.2) _)
      (span_homologyMap_cubicalHomologyδ_eq_top (hcol x y (by omega)) (by omega) (ν x y)
        (hν x y (by omega)) _)
  · obtain ⟨r, hr⟩ := ha
    obtain rfl : a = (κ' x w y).codRestrict (range (j x y))ᶜ (hκ'B x w y hyw hwx)
        (j x w r.1, o' w y r.2) :=
      Subtype.ext (hr.symm.trans (ContinuousMap.coe_codRestrict_apply _ _ _ _).symm)
    -- The sign acts trivially, and both sides generate the local homology of the boundary at `a`.
    rw [negOnePow_smul_eq_self_of_neg_one_eq_one
      (congrArg Units.val (Subsingleton.elim (-1 : kˣ) 1))]
    exact eq_of_span_cubicalHomology_eq_top (hE x y (by omega)) _
      (span_homologyMap_cubicalChainComplexMap_cubicalHomologyKunnethPair_eq_top (hj x w)
        (ho' w y) (hG x w hwx) (by omega) (ν x w) (μ' w y) _ (hκ'j x w y hyw hwx) r
        (hν x w hwx r.1) (hμ' w y hyw r.2) _)
      (span_homologyMap_cubicalHomologyδ_eq_top (hcol x y (by omega)) (by omega) (ν x y)
        (hν x y (by omega)) _)

end Continuation

end TauCeti

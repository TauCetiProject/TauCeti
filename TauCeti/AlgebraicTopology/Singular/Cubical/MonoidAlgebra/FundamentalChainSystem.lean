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

For the spaces `H x y` of trajectories of a one-parameter family of homotopies, the faces
`M x z × H z y` and `H x w × M' w y` are discharged in the same way, and so are the two ends
`N₀ x y` and `N₁ x y`, the spaces of continuation trajectories of the homotopies at the ends of the
family. On an end there is no cross product: the class of the end, carried along its inclusion,
generates the local homology at every interior point of the end
(`TauCeti.span_homologyMap_cubicalChainComplexMap_eq_top`), so it is again the unique generator, and
the sign `-1` of the end `N₀ x y` acts trivially. So representing parametrized chain systems of
fundamental classes exist between two representing continuation chain systems
(`TauCeti.ParametrizedChainSystem.exists_isRepresenting_of_subsingleton_units`); their
push-forwards are the chain homotopies between the continuation maps of the two ends.

No orientations enter: with integral coefficients the face condition compares the boundary
orientation of each face with its product orientation, which is not done here.

## Main results

* `TauCeti.TwistingChainSystem.exists_isRepresenting_of_subsingleton_units`: representing twisting
  chain systems of fundamental classes exist when `1` is the only unit of the coefficients.
* `TauCeti.ContinuationChainSystem.exists_isRepresenting_of_subsingleton_units`: so do
  representing continuation chain systems.
* `TauCeti.ParametrizedChainSystem.exists_isRepresenting_of_subsingleton_units`: and representing
  parametrized chain systems between two representing continuation chain systems.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Annals of
  Mathematics 166 (2007), Lemma 2.2 and Appendix A, the representing chain systems of
  compactified trajectory spaces over `ℤ/2`.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Proposition 5.2.6, and Chapter 6,
  the fundamental chains of the spaces of continuation trajectories and of their one-parameter
  families.
* A. Hatcher, *Algebraic Topology*, Section 3.3, the mod `2` fundamental class.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set Topology MonoidalCategory TopPair HomologicalComplex
open scoped TensorProduct

universe u

namespace TauCeti

variable {k : Type u} [CommRing k]

/-- **The face condition at an interior point of a face, when `1` is the only unit.** Let
`μ₁ ∈ Hₚ(X₁, ∂ X₁)`, `μ₂ ∈ H_q(X₂, ∂ X₂)` and `μ ∈ Hₙ(X, ∂ X)` generate the local homology at every
interior point, where `∂ X₁`, `∂ X₂` and `∂ X` are the complements of open embeddings `j₁`, `j₂` and
`j`, the interior of `X₁` is a manifold of dimension `p`, and `∂ X` is collared and a manifold of
dimension `p + q = n - 1`. Let the face map `f : X₁ × X₂ → ∂ X` be an open embedding on the
interiors. At a point `a` of the interior of the face, the cross product `μ₁ × μ₂`, carried by `f`
to the local homology of `∂ X` at `a`, is any sign times the image of `∂ μ`: both generate a module
isomorphic to `k`, which has a single generator, and signs act trivially. -/
private theorem face_eq_negOnePow_smul_of_subsingleton_units [Subsingleton kˣ]
    {X₁ X₂ X : TopCat.{u}} [T1Space X₁] [T1Space X₂] [T2Space X] {N₁ N₂ N : Type u}
    [TopologicalSpace N₁] [TopologicalSpace N₂] {j₁ : N₁ → X₁} {j₂ : N₂ → X₂} {j : N → X}
    (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂)
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [ChartedSpace F N₁]
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E ↥(range j)ᶜ] (hcol : IsCollared (Subtype.val : ↥(range j)ᶜ → X))
    {p q m n : ℕ} (hp : finrank ℝ F = p) (hpq : p + q = m) (hE : finrank ℝ E = m)
    (hmn : m + 1 = n)
    {μ₁ : ((TopPair.ofSubset (range j₁)ᶜ).cubicalChainComplex k).homology p}
    {μ₂ : ((TopPair.ofSubset (range j₂)ᶜ).cubicalChainComplex k).homology q}
    {μ : ((TopPair.ofSubset (range j)ᶜ).cubicalChainComplex k).homology n}
    (hμ₁ : ∀ r : N₁, (k ∙ localHomologyRestriction (ModuleCat.of k k)
      (singleton_subset_iff.2 (mem_range_self r)) _
        ((TopPair.singularCubicalHomologyIso k _ _).inv.hom μ₁)) = ⊤)
    (hμ₂ : ∀ r : N₂, (k ∙ localHomologyRestriction (ModuleCat.of k k)
      (singleton_subset_iff.2 (mem_range_self r)) _
        ((TopPair.singularCubicalHomologyIso k _ _).inv.hom μ₂)) = ⊤)
    (hμ : ∀ r : N, (k ∙ localHomologyRestriction (ModuleCat.of k k)
      (singleton_subset_iff.2 (mem_range_self r)) _
        ((TopPair.singularCubicalHomologyIso k _ _).inv.hom μ)) = ⊤)
    (f : C(X₁ × X₂, X)) (hf : ∀ r, f r ∈ (range j)ᶜ)
    (hfj : IsOpenEmbedding fun r : N₁ × N₂ ↦ f.codRestrict (range j)ᶜ hf (j₁ r.1, j₂ r.2))
    {a : ↥(range j)ᶜ} (ha : (a : X) ∈ range fun r : N₁ × N₂ ↦ f (j₁ r.1, j₂ r.2))
    (h : MapsTo (TopCat.ofHom (X := ↑((TopPair.ofSubset (range j₁)ᶜ).fst ⊗
        (TopPair.ofSubset (range j₂)ᶜ).fst)) (f.codRestrict (range j)ᶜ hf))
      ((TopPair.ofSubset (range j₁)ᶜ).prodSubspace (TopPair.ofSubset (range j₂)ᶜ))
      ({a}ᶜ : Set ↥(range j)ᶜ)) (e : ℤ) :
    (homologyMap (TopPair.cubicalChainComplexMap k (TopPair.ofSubsetMap _ h)) m).hom
        ((homologyMap ((TopPair.ofSubset (range j₁)ᶜ).cubicalChainComplexProdComparison k
          (TopPair.ofSubset (range j₂)ᶜ)) m).hom
          ((GradedObject.Monoidal.ιTensorObj _ _ _ _ _ hpq ≫
            cubicalHomologyKunnethPair k _ _ _).hom (μ₁ ⊗ₜ μ₂))) =
      e.negOnePow • (homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
          (TopPair.ofSubset ({a}ᶜ : Set ↥(range j)ᶜ)).map)) m).hom
        (((TopPair.ofSubset (range j)ᶜ).cubicalHomologyδ k _ _ hmn).hom μ) := by
  obtain ⟨r, hr⟩ := ha
  obtain rfl : a = f.codRestrict (range j)ᶜ hf (j₁ r.1, j₂ r.2) :=
    Subtype.ext (hr.symm.trans (ContinuousMap.coe_codRestrict_apply _ _ _ _).symm)
  rw [negOnePow_smul_eq_self_of_neg_one_eq_one
    (congrArg Units.val (Subsingleton.elim (-1 : kˣ) 1))]
  exact eq_of_span_cubicalHomology_eq_top hE _
    (span_homologyMap_cubicalChainComplexMap_cubicalHomologyKunnethPair_eq_top hj₁ hj₂ hp hpq μ₁
      μ₂ _ hfj r (hμ₁ r.1) (hμ₂ r.2) h)
    (span_homologyMap_cubicalHomologyδ_eq_top hcol hmn μ hμ _)

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
    fun x z y hyz hzx a ha ↦ face_eq_negOnePow_smul_of_subsingleton_units (hj x z) (hj z y)
      (hcol x y (by omega)) (hF x z hzx) _ (hE x y (by omega)) _ (hμ x z hzx) (hμ z y hyz)
      (hμ x y (by omega)) _ _ (hιj x z y hyz hzx) ha _ _

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
cocycle between the Barraud–Cornea cocycles of the two functions (BDHO, Chapter 6). -/
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
    hU'κ hU'κ' hUB hU'B (fun x z y hyz hzx a ha ↦ ?_) fun x w y hyw hwx a ha ↦
      face_eq_negOnePow_smul_of_subsingleton_units (hj x w) (ho' w y) (hcol x y (by omega))
        (hG x w hwx) _ (hE x y (by omega)) _ (hν x w hwx) (hμ' w y hyw) (hν x y (by omega)) _ _
        (hκ'j x w y hyw hwx) ha _ _
  -- On a left face there is no sign.
  exact (face_eq_negOnePow_smul_of_subsingleton_units (ho x z) (hj z y) (hcol x y (by omega))
    (hF x z hzx) _ (hE x y (by omega)) _ (hμ x z hzx) (hν z y hyz) (hν x y (by omega)) _ _
    (hκj x z y hyz hzx) ha _ 0).trans (by rw [Int.negOnePow_zero, one_smul])

end Continuation

section Parametrized

/-- **The end condition at an interior point of an end, when `1` is the only unit.** Let
`ν₁ ∈ Hₘ(X₁, ∂ X₁)` and `μ ∈ Hₙ(X, ∂ X)` generate the local homology at every interior point, where
`∂ X₁` and `∂ X` are the complements of open embeddings `j₁` and `j`, and `∂ X` is collared and a
manifold of dimension `m = n - 1`. Let the map `f : X₁ → ∂ X` be an open embedding on the interior
of `X₁`. At a point `a` of the image of that interior, the class `ν₁`, carried by `f` to the local
homology of `∂ X` at `a`, is the image of `∂ μ`: both generate a module isomorphic to `k`, which
has a single generator. -/
private theorem end_eq_of_subsingleton_units [Subsingleton kˣ] {X₁ X : TopCat.{u}} [T1Space X₁]
    [T2Space X] {N₁ N : Type u} [TopologicalSpace N₁] {j₁ : N₁ → X₁}
    {j : N → X} (hj₁ : IsOpenEmbedding j₁)
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E ↥(range j)ᶜ] (hcol : IsCollared (Subtype.val : ↥(range j)ᶜ → X))
    {m n : ℕ} (hE : finrank ℝ E = m) (hmn : m + 1 = n)
    {ν₁ : ((TopPair.ofSubset (range j₁)ᶜ).cubicalChainComplex k).homology m}
    {μ : ((TopPair.ofSubset (range j)ᶜ).cubicalChainComplex k).homology n}
    (hν₁ : ∀ r : N₁, (k ∙ localHomologyRestriction (ModuleCat.of k k)
      (singleton_subset_iff.2 (mem_range_self r)) _
        ((TopPair.singularCubicalHomologyIso k _ _).inv.hom ν₁)) = ⊤)
    (hμ : ∀ r : N, (k ∙ localHomologyRestriction (ModuleCat.of k k)
      (singleton_subset_iff.2 (mem_range_self r)) _
        ((TopPair.singularCubicalHomologyIso k _ _).inv.hom μ)) = ⊤)
    (f : C(X₁, X)) (hf : ∀ r, f r ∈ (range j)ᶜ)
    (hfj : IsOpenEmbedding fun r : N₁ ↦ f.codRestrict (range j)ᶜ hf (j₁ r))
    {a : ↥(range j)ᶜ} (ha : (a : X) ∈ range fun r : N₁ ↦ f (j₁ r))
    (h : MapsTo (TopCat.ofHom (X := X₁) (f.codRestrict (range j)ᶜ hf)) (range j₁)ᶜ
      ({a}ᶜ : Set ↥(range j)ᶜ)) :
    (homologyMap (TopPair.cubicalChainComplexMap k (TopPair.ofSubsetMap _ h)) m).hom ν₁ =
      (homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
          (TopPair.ofSubset ({a}ᶜ : Set ↥(range j)ᶜ)).map)) m).hom
        (((TopPair.ofSubset (range j)ᶜ).cubicalHomologyδ k _ _ hmn).hom μ) := by
  obtain ⟨r, hr⟩ := ha
  obtain rfl : a = f.codRestrict (range j)ᶜ hf (j₁ r) :=
    Subtype.ext (hr.symm.trans (ContinuousMap.coe_codRestrict_apply _ _ _ _).symm)
  exact eq_of_span_cubicalHomology_eq_top hE _
    (span_homologyMap_cubicalChainComplexMap_eq_top hj₁ ν₁ _ hfj r (hν₁ r) h)
    (span_homologyMap_cubicalHomologyδ_eq_top hcol hmn μ hμ _)

variable {Q : Type*} [Fintype Q] {indQ : Q → ℤ} {M' : Q → Q → TopCat.{u}}
  {N₀ N₁ H : P → Q → TopCat.{u}} {ι' : ∀ x y z, C(M' x y × M' y z, M' x z)}
  {κ₀ : ∀ x y z, C(M x y × N₀ y z, N₀ x z)} {κ₀' : ∀ x y z, C(N₀ x y × M' y z, N₀ x z)}
  {κ₁ : ∀ x y z, C(M x y × N₁ y z, N₁ x z)} {κ₁' : ∀ x y z, C(N₁ x y × M' y z, N₁ x z)}
  {κH : ∀ x y z, C(M x y × H y z, H x z)} {κH' : ∀ x y z, C(H x y × M' y z, H x z)}
  {j₀ : ∀ x y, C(N₀ x y, H x y)} {j₁ : ∀ x y, C(N₁ x y, H x y)}
  {S : TwistingChainSystem ind ι k} {S' : TwistingChainSystem indQ ι' k}
  {T₀ : ContinuationChainSystem κ₀ κ₀' S S'} {T₁ : ContinuationChainSystem κ₁ κ₁' S S'}

/-- **Representing parametrized chain systems of fundamental classes when `1` is the only unit.**
Let `k` be a commutative ring whose only unit is `1`, such as `ZMod 2`. Let `S` and `S'` be
twisting chain systems representing classes `μ x y ∈ H(M x y, ∂ M x y; k)` and
`μ' x y ∈ H(M' x y, ∂ M' x y; k)`, and `T₀` and `T₁` continuation chain systems from `S` to `S'`
representing classes `ν₀ x y ∈ H(N₀ x y, ∂ N₀ x y; k)` and `ν₁ x y ∈ H(N₁ x y, ∂ N₁ x y; k)`, where
each boundary is the complement of an open subset, the image of `o x y`, `o' x y`, `o₀ x y` and
`o₁ x y` respectively. Suppose that:

* when `ind y < ind x`, `O x y` is a manifold of dimension `ind x - ind y - 1` and `μ x y`
  generates the local homology at every point of `O x y`; when `indQ y < indQ x`, `μ' x y`
  generates the local homology at every point of `O' x y`; and when `indQ y ≤ ind x`, `ν₀ x y` and
  `ν₁ x y` generate the local homology at every point of `O₀ x y` and `O₁ x y`, as fundamental
  classes relative to the boundary do;
* each `H x y` is a compact Hausdorff space containing an open subset `j x y (W x y)`, a copy of
  `W x y`, whose complement is the boundary `∂ H x y`; when `indQ y ≤ ind x + 1`, `W x y` is a
  manifold of dimension `ind x - indQ y + 1` and `θ x y ∈ H(H x y, ∂ H x y; k)` generates the local
  homology at every point of `W x y`, and when `indQ y ≤ ind x`, `∂ H x y` is collared and a
  manifold of dimension `ind x - indQ y`;
* the composition maps `κH x z y : M x z × H z y → H x y` and `κH' x w y : H x w × M' w y → H x y`
  are associative, the inclusions `j₀ x y : N₀ x y → H x y` and `j₁ x y : N₁ x y → H x y` of the
  two ends are compatible with the composition maps, and for `indQ y ≤ ind x` the ends, the left
  faces with `indQ y ≤ ind z + 1` and `ind z < ind x`, and the right faces with `indQ y < indQ w`
  and `indQ w ≤ ind x + 1` land in `∂ H x y` and are open embeddings into `∂ H x y` on the
  interiors `O₀ x y`, `O₁ x y`, `O x z × W z y` and `W x w × O' w y`;
* the images of these interiors, the interiors of the faces, are together dense in `∂ H x y`,
  each face misses the interior of every other face, and each face map carries the boundary of
  its source off the interior of its face.

Then some parametrized chain system between `T₀` and `T₁` represents the classes `θ`. For the
compactified spaces of trajectories of a one-parameter family of homotopies between two Morse
functions, this is the existence over `ℤ/2` of the fundamental chains whose push-forwards form the
parametrized cocycle, and so the chain homotopy, between the continuation cocycles of the two
homotopies at the ends of the family (BDHO, Chapter 6). -/
theorem ParametrizedChainSystem.exists_isRepresenting_of_subsingleton_units [Subsingleton kˣ]
    [∀ x y, T1Space (M x y)] [∀ x y, T1Space (M' x y)] [∀ x y, T1Space (N₀ x y)]
    [∀ x y, T1Space (N₁ x y)] [∀ x y, T2Space (H x y)] [∀ x y, CompactSpace (H x y)]
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
    {O₀ : P → Q → Type u} [∀ x y, TopologicalSpace (O₀ x y)] {o₀ : ∀ x y, O₀ x y → N₀ x y}
    (ho₀ : ∀ x y, IsOpenEmbedding (o₀ x y))
    {ν₀ : ∀ x y, ((TopPair.ofSubset (range (o₀ x y))ᶜ).cubicalChainComplex k).homology
      (ind x - indQ y).toNat}
    (hν₀ : ∀ x y, indQ y ≤ ind x → ∀ r : O₀ x y, (k ∙ localHomologyRestriction (ModuleCat.of k k)
      (singleton_subset_iff.2 (mem_range_self r)) _
        ((TopPair.singularCubicalHomologyIso k _ _).inv.hom (ν₀ x y))) = ⊤)
    (hT₀ : T₀.IsRepresenting (fun x y ↦ (range (o₀ x y))ᶜ) ν₀)
    {O₁ : P → Q → Type u} [∀ x y, TopologicalSpace (O₁ x y)] {o₁ : ∀ x y, O₁ x y → N₁ x y}
    (ho₁ : ∀ x y, IsOpenEmbedding (o₁ x y))
    {ν₁ : ∀ x y, ((TopPair.ofSubset (range (o₁ x y))ᶜ).cubicalChainComplex k).homology
      (ind x - indQ y).toNat}
    (hν₁ : ∀ x y, indQ y ≤ ind x → ∀ r : O₁ x y, (k ∙ localHomologyRestriction (ModuleCat.of k k)
      (singleton_subset_iff.2 (mem_range_self r)) _
        ((TopPair.singularCubicalHomologyIso k _ _).inv.hom (ν₁ x y))) = ⊤)
    (hT₁ : T₁.IsRepresenting (fun x y ↦ (range (o₁ x y))ᶜ) ν₁)
    {W : P → Q → Type u} [∀ x y, TopologicalSpace (W x y)] {j : ∀ x y, W x y → H x y}
    (hj : ∀ x y, IsOpenEmbedding (j x y))
    {G : P → Q → Type u} [∀ x y, NormedAddCommGroup (G x y)] [∀ x y, NormedSpace ℝ (G x y)]
    [∀ x y, FiniteDimensional ℝ (G x y)] [∀ x y, ChartedSpace (G x y) (W x y)]
    (hG : ∀ x y, indQ y ≤ ind x + 1 → finrank ℝ (G x y) = (ind x - indQ y + 1).toNat)
    {E : P → Q → Type u} [∀ x y, NormedAddCommGroup (E x y)] [∀ x y, NormedSpace ℝ (E x y)]
    [∀ x y, FiniteDimensional ℝ (E x y)] [∀ x y, ChartedSpace (E x y) ↥(range (j x y))ᶜ]
    (hE : ∀ x y, indQ y ≤ ind x → finrank ℝ (E x y) = (ind x - indQ y).toNat)
    (hcol : ∀ x y, indQ y ≤ ind x → IsCollared (Subtype.val : ↥(range (j x y))ᶜ → H x y))
    {θ : ∀ x y, ((TopPair.ofSubset (range (j x y))ᶜ).cubicalChainComplex k).homology
      (ind x - indQ y + 1).toNat}
    (hθ : ∀ x y, indQ y ≤ ind x + 1 → ∀ r : W x y, (k ∙ localHomologyRestriction
      (ModuleCat.of k k) (singleton_subset_iff.2 (mem_range_self r)) _
        ((TopPair.singularCubicalHomologyIso k _ _).inv.hom (θ x y))) = ⊤)
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
    (hj₀C : ∀ x y, indQ y ≤ ind x → ∀ p, j₀ x y p ∈ (range (j x y))ᶜ)
    (hj₁C : ∀ x y, indQ y ≤ ind x → ∀ p, j₁ x y p ∈ (range (j x y))ᶜ)
    (hκHC : ∀ x z y, indQ y ≤ ind z + 1 → ind z < ind x → ∀ p, κH x z y p ∈ (range (j x y))ᶜ)
    (hκH'C : ∀ x w y, indQ y < indQ w → indQ w ≤ ind x + 1 → ∀ p,
      κH' x w y p ∈ (range (j x y))ᶜ)
    (hj₀j : ∀ x y (hxy : indQ y ≤ ind x), IsOpenEmbedding fun r : O₀ x y ↦
      (j₀ x y).codRestrict (range (j x y))ᶜ (hj₀C x y hxy) (o₀ x y r))
    (hj₁j : ∀ x y (hxy : indQ y ≤ ind x), IsOpenEmbedding fun r : O₁ x y ↦
      (j₁ x y).codRestrict (range (j x y))ᶜ (hj₁C x y hxy) (o₁ x y r))
    (hκHj : ∀ x z y (hyz : indQ y ≤ ind z + 1) (hzx : ind z < ind x),
      IsOpenEmbedding fun r : O x z × W z y ↦
        (κH x z y).codRestrict (range (j x y))ᶜ (hκHC x z y hyz hzx) (o x z r.1, j z y r.2))
    (hκH'j : ∀ x w y (hyw : indQ y < indQ w) (hwx : indQ w ≤ ind x + 1),
      IsOpenEmbedding fun r : W x w × O' w y ↦
        (κH' x w y).codRestrict (range (j x y))ᶜ (hκH'C x w y hyw hwx) (j x w r.1, o' w y r.2))
    (hU : ∀ x y, indQ y ≤ ind x → Dense {a : ↥(range (j x y))ᶜ |
      (a : H x y) ∈ (range fun r : O₀ x y ↦ j₀ x y (o₀ x y r)) ∨
        (a : H x y) ∈ (range fun r : O₁ x y ↦ j₁ x y (o₁ x y r)) ∨
        (∃ z, indQ y ≤ ind z + 1 ∧ ind z < ind x ∧
          (a : H x y) ∈ range fun r : O x z × W z y ↦ κH x z y (o x z r.1, j z y r.2)) ∨
        ∃ w, indQ y < indQ w ∧ indQ w ≤ ind x + 1 ∧
          (a : H x y) ∈ range fun r : W x w × O' w y ↦ κH' x w y (j x w r.1, o' w y r.2)})
    (hV₀j₁ : ∀ x y, indQ y ≤ ind x →
      Disjoint (range (j₁ x y)) (range fun r : O₀ x y ↦ j₀ x y (o₀ x y r)))
    (hV₀κH : ∀ x z y, indQ y ≤ ind z + 1 → ind z < ind x →
      Disjoint (range (κH x z y)) (range fun r : O₀ x y ↦ j₀ x y (o₀ x y r)))
    (hV₀κH' : ∀ x w y, indQ y < indQ w → indQ w ≤ ind x + 1 →
      Disjoint (range (κH' x w y)) (range fun r : O₀ x y ↦ j₀ x y (o₀ x y r)))
    (hV₁j₀ : ∀ x y, indQ y ≤ ind x →
      Disjoint (range (j₀ x y)) (range fun r : O₁ x y ↦ j₁ x y (o₁ x y r)))
    (hV₁κH : ∀ x z y, indQ y ≤ ind z + 1 → ind z < ind x →
      Disjoint (range (κH x z y)) (range fun r : O₁ x y ↦ j₁ x y (o₁ x y r)))
    (hV₁κH' : ∀ x w y, indQ y < indQ w → indQ w ≤ ind x + 1 →
      Disjoint (range (κH' x w y)) (range fun r : O₁ x y ↦ j₁ x y (o₁ x y r)))
    (hUj₀ : ∀ x z y, indQ y ≤ ind x → Disjoint (range (j₀ x y))
      (range fun r : O x z × W z y ↦ κH x z y (o x z r.1, j z y r.2)))
    (hUj₁ : ∀ x z y, indQ y ≤ ind x → Disjoint (range (j₁ x y))
      (range fun r : O x z × W z y ↦ κH x z y (o x z r.1, j z y r.2)))
    (hUκH : ∀ x z z' y, indQ y ≤ ind z' + 1 → ind z' < ind x → z' ≠ z →
      Disjoint (range (κH x z' y)) (range fun r : O x z × W z y ↦ κH x z y (o x z r.1, j z y r.2)))
    (hUκH' : ∀ x z w y, indQ y < indQ w → indQ w ≤ ind x + 1 →
      Disjoint (range (κH' x w y))
        (range fun r : O x z × W z y ↦ κH x z y (o x z r.1, j z y r.2)))
    (hU'j₀ : ∀ x w y, indQ y ≤ ind x → Disjoint (range (j₀ x y))
      (range fun r : W x w × O' w y ↦ κH' x w y (j x w r.1, o' w y r.2)))
    (hU'j₁ : ∀ x w y, indQ y ≤ ind x → Disjoint (range (j₁ x y))
      (range fun r : W x w × O' w y ↦ κH' x w y (j x w r.1, o' w y r.2)))
    (hU'κH : ∀ x w z y, indQ y ≤ ind z + 1 → ind z < ind x →
      Disjoint (range (κH x z y))
        (range fun r : W x w × O' w y ↦ κH' x w y (j x w r.1, o' w y r.2)))
    (hU'κH' : ∀ x w w' y, indQ y < indQ w' → indQ w' ≤ ind x + 1 → w' ≠ w →
      Disjoint (range (κH' x w' y))
        (range fun r : W x w × O' w y ↦ κH' x w y (j x w r.1, o' w y r.2)))
    (hV₀B : ∀ x y (hxy : indQ y ≤ ind x),
      MapsTo (TopCat.ofHom (X := N₀ x y)
          ((j₀ x y).codRestrict (range (j x y))ᶜ (hj₀C x y hxy)))
        (range (o₀ x y))ᶜ (Subtype.val ⁻¹' range fun r : O₀ x y ↦ j₀ x y (o₀ x y r))ᶜ)
    (hV₁B : ∀ x y (hxy : indQ y ≤ ind x),
      MapsTo (TopCat.ofHom (X := N₁ x y)
          ((j₁ x y).codRestrict (range (j x y))ᶜ (hj₁C x y hxy)))
        (range (o₁ x y))ᶜ (Subtype.val ⁻¹' range fun r : O₁ x y ↦ j₁ x y (o₁ x y r))ᶜ)
    (hUC : ∀ x z y (hyz : indQ y ≤ ind z + 1) (hzx : ind z < ind x),
      MapsTo (TopCat.ofHom (X := ↑((TopPair.ofSubset (range (o x z))ᶜ).fst ⊗
          (TopPair.ofSubset (range (j z y))ᶜ).fst))
          ((κH x z y).codRestrict (range (j x y))ᶜ (hκHC x z y hyz hzx)))
        ((TopPair.ofSubset (range (o x z))ᶜ).prodSubspace (TopPair.ofSubset (range (j z y))ᶜ))
        (Subtype.val ⁻¹' range fun r : O x z × W z y ↦ κH x z y (o x z r.1, j z y r.2))ᶜ)
    (hU'C : ∀ x w y (hyw : indQ y < indQ w) (hwx : indQ w ≤ ind x + 1),
      MapsTo (TopCat.ofHom (X := ↑((TopPair.ofSubset (range (j x w))ᶜ).fst ⊗
          (TopPair.ofSubset (range (o' w y))ᶜ).fst))
          ((κH' x w y).codRestrict (range (j x y))ᶜ (hκH'C x w y hyw hwx)))
        ((TopPair.ofSubset (range (j x w))ᶜ).prodSubspace (TopPair.ofSubset (range (o' w y))ᶜ))
        (Subtype.val ⁻¹' range fun r : W x w × O' w y ↦ κH' x w y (j x w r.1, o' w y r.2))ᶜ) :
    ∃ η : ParametrizedChainSystem κH κH' j₀ j₁ T₀ T₁,
      η.IsRepresenting (fun x y ↦ (range (j x y))ᶜ) θ := by
  have (x : P) (y : Q) : CompactSpace ↥(range (j x y))ᶜ :=
    isCompact_iff_compactSpace.1 (hj x y).isOpen_range.isClosed_compl.isCompact
  -- Signs act trivially, since `-1 = 1` in `k`.
  have h1 : (-1 : k) = 1 := congrArg Units.val (Subsingleton.elim (-1 : kˣ) 1)
  have hneg {V : Type u} [AddCommGroup V] [Module k V] (v : V) : -v = v := by
    rw [← neg_one_smul k v, h1, one_smul]
  refine ParametrizedChainSystem.exists_isRepresenting_of_faces hS hS' hT₀ hT₁ (E := E) hE hκH
    hκHκH' hκH' hj₀κ hj₀κ' hj₁κ hj₁κ' hj₀C hj₁C hκHC hκH'C
    (fun x y ↦ range fun r : O₀ x y ↦ j₀ x y (o₀ x y r))
    (fun x y ↦ range fun r : O₁ x y ↦ j₁ x y (o₁ x y r))
    (fun x z y ↦ range fun r : O x z × W z y ↦ κH x z y (o x z r.1, j z y r.2))
    (fun x w y ↦ range fun r : W x w × O' w y ↦ κH' x w y (j x w r.1, o' w y r.2)) hU hV₀j₁
    hV₀κH hV₀κH' hV₁j₀ hV₁κH hV₁κH' hUj₀ hUj₁ hUκH hUκH' hU'j₀ hU'j₁ hU'κH hU'κH' hV₀B hV₁B
    hUC hU'C (fun x y hxy a ha ↦ ?_) (fun x y hxy a ha ↦ ?_) (fun x z y hyz hzx a ha ↦ ?_)
    fun x w y hyw hwx a ha ↦
      face_eq_negOnePow_smul_of_subsingleton_units (hj x w) (ho' w y) (hcol x y (by omega))
        (hG x w hwx) _ (hE x y (by omega)) _ (hθ x w hwx) (hμ' w y hyw) (hθ x y (by omega)) _ _
        (hκH'j x w y hyw hwx) ha _ _
  · -- On the end `j₀` the sign of the face condition is `-1`, which acts trivially.
    exact (end_eq_of_subsingleton_units (ho₀ x y) (hcol x y hxy) (hE x y hxy) _
      (hν₀ x y hxy) (hθ x y (by omega)) _ _ (hj₀j x y hxy) ha _).trans (hneg _).symm
  · exact end_eq_of_subsingleton_units (ho₁ x y) (hcol x y hxy) (hE x y hxy) _ (hν₁ x y hxy)
      (hθ x y (by omega)) _ _ (hj₁j x y hxy) ha _
  · exact face_eq_negOnePow_smul_of_subsingleton_units (ho x z) (hj z y) (hcol x y (by omega))
      (hF x z hzx) _ (hE x y (by omega)) _ (hμ x z hzx) (hθ z y hyz) (hθ x y (by omega)) _ _
      (hκHj x z y hyz hzx) ha _ _

end Parametrized

end TauCeti

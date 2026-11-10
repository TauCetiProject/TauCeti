/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.Algebra.Homology.Monoidal.Homology.Connecting
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.Kunneth

/-!
# The relative cubical Eilenberg–Zilber and Künneth theorems

Let `P = (X, A)` be a topological pair and `Y` a space, and let `(X × Y, A × Y)` be their product
pair (`TopPair.prodRight`). The cubical cross product `N(X; k) ⊗ N(Y; k) ⟶ N(X × Y; k)` of
normalized cubical chains carries `N(A; k) ⊗ N(Y; k)` into `N(A × Y; k)`, so it descends to the
**relative cross product**

`N(X, A; k) ⊗ N(Y; k) ⟶ N(X × Y, A × Y; k)`

(`TopPair.cubicalCrossProduct`), which sends `[a] ⊗ b` to `[a × b]`
(`TopPair.π_cubicalCrossProduct`), naturally in the pair and the space. It is a quasi-isomorphism
(`TopPair.quasiIso_cubicalCrossProduct`): this is the **relative Eilenberg–Zilber theorem**.

The sequence `0 ⟶ N(A) ⟶ N(X) ⟶ N(X, A) ⟶ 0` splits in each degree, so it remains short exact
after tensoring on the right with `N(Y)`, with no flatness hypothesis on `N(Y)`
(`HomologicalComplex.shortExact_tensorRightShortComplex`). The three cross products form a
morphism from this tensored sequence to the sequence of the pair `(X × Y, A × Y)`. The two absolute
cross products are quasi-isomorphisms (`TauCeti.quasiIso_cubicalCrossProduct`), so the five lemma,
applied to the long exact homology sequences
(`HomologicalComplex.HomologySequence.quasiIso_τ₃`), shows that the relative one is too.

Composing the algebraic Künneth map with the relative cross product gives the **relative Künneth
map** `⨁_{p + q = n} Hₚ(X, A; k) ⊗ H_q(Y; k) ⟶ Hₙ(X × Y, A × Y; k)`
(`TopPair.cubicalHomologyKunneth`), an isomorphism whenever the algebraic Künneth map of the two
chain complexes is, for instance over a field (`TopPair.isIso_cubicalHomologyKunneth`).

This is the form in which a product of a cell pair with a space enters cellular arguments: the
chains of `(Dⁿ × F, Sⁿ⁻¹ × F)` are quasi-isomorphic to `N(Dⁿ, Sⁿ⁻¹) ⊗ N(F)`, with the cross
product as the comparison.

## Main definitions

* `TopPair.prodRight P Y`: the product pair `(X × Y, A × Y)`, functorial by
  `TopPair.prodRightMap`.
* `TopPair.cubicalCrossProduct k P Y`: the relative cross product
  `N(X, A; k) ⊗ N(Y; k) ⟶ N(X × Y, A × Y; k)`.
* `TopPair.cubicalHomologyKunneth k P Y n`: the relative Künneth map.

## Main results

* `TopPair.π_cubicalCrossProduct`: the relative cross product is induced by the cross product.
* `TopPair.cubicalCrossProduct_naturality`: naturality in the pair and the space.
* `TopPair.quasiIso_cubicalCrossProduct`: the relative Eilenberg–Zilber theorem.
* `TopPair.isIso_cubicalHomologyKunneth`: the relative Künneth theorem.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.B, the relative
  cross product and the Künneth formula.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex TauCeti

universe u

namespace TopPair

/-! ### The product of a pair with a space -/

/-- The product `(X × Y, A × Y)` of a topological pair `P = (X, A)` with a space `Y`. -/
-- Written as a structure instance rather than with `TopPair.of`, whose underlying
-- `MorphismProperty.Arrow.mk` is not reducible: this way the spaces of the product pair are
-- reducibly `X × Y` and `A × Y`, so lemmas about chains of `X × Y` rewrite in its chains.
abbrev prodRight (P : TopPair.{u}) (Y : TopCat.{u}) : TopPair.{u} where
  left := P.snd ⊗ Y
  right := P.fst ⊗ Y
  hom := P.map ▷ Y
  prop := P.isEmbedding_map.prodMap Topology.IsEmbedding.id

/-- The embedding of the product pair `(X × Y, A × Y)` is that of `(X, A)` times the identity. -/
@[simp]
theorem map_prodRight (P : TopPair.{u}) (Y : TopCat.{u}) : (P.prodRight Y).map = P.map ▷ Y :=
  (rfl)

/-- The map of product pairs `(X × Y, A × Y) ⟶ (X' × Y', A' × Y')` induced by a map of pairs
`f : (X, A) ⟶ (X', A')` and a map of spaces `g : Y ⟶ Y'`. -/
def prodRightMap {P P' : TopPair.{u}} (f : P ⟶ P') {Y Y' : TopCat.{u}} (g : Y ⟶ Y') :
    P.prodRight Y ⟶ P'.prodRight Y' :=
  TopPair.ofHom (Hom.fst f ⊗ₘ g) (Hom.snd f ⊗ₘ g) (by
    rw [map_prodRight, map_prodRight, ← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom, Hom.w, Category.comp_id, Category.id_comp])

/-- On the ambient spaces, the map of product pairs is the product map `X × Y ⟶ X' × Y'`. -/
@[simp]
theorem fst_prodRightMap {P P' : TopPair.{u}} (f : P ⟶ P') {Y Y' : TopCat.{u}} (g : Y ⟶ Y') :
    Hom.fst (prodRightMap f g) = Hom.fst f ⊗ₘ g :=
  (rfl)

/-- On the subspaces, the map of product pairs is the product map `A × Y ⟶ A' × Y'`. -/
@[simp]
theorem snd_prodRightMap {P P' : TopPair.{u}} (f : P ⟶ P') {Y Y' : TopCat.{u}} (g : Y ⟶ Y') :
    Hom.snd (prodRightMap f g) = Hom.snd f ⊗ₘ g :=
  (rfl)

/-- The map of product pairs induced by identities is the identity. -/
@[simp]
theorem prodRightMap_id (P : TopPair.{u}) (Y : TopCat.{u}) :
    prodRightMap (𝟙 P) (𝟙 Y) = 𝟙 (P.prodRight Y) := by
  ext : 2 <;> simp
  -- the remaining subspace component holds since `Hom.snd (𝟙 P)` is `𝟙 P.snd` by definition
  rfl

/-- The map of product pairs is compatible with composition. -/
@[simp]
theorem prodRightMap_comp {P P' P'' : TopPair.{u}} (f : P ⟶ P') (f' : P' ⟶ P'')
    {Y Y' Y'' : TopCat.{u}} (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    prodRightMap (f ≫ f') (g ≫ g') = prodRightMap f g ≫ prodRightMap f' g' := by
  ext : 2 <;> simp
  -- the remaining subspace component holds since `Hom.snd (f ≫ f')` is `Hom.snd f ≫ Hom.snd f'`
  -- by definition
  rfl

variable (k : Type u) [CommRing k] (P : TopPair.{u}) (Y : TopCat.{u})

/-! ### The relative cross product -/

/-- The sequence `N(A) ⊗ N(Y) ⟶ N(X) ⊗ N(Y) ⟶ N(X, A) ⊗ N(Y)` is short exact, since the sequence of
the pair splits in each degree. -/
private theorem shortExact_tensorRightShortComplex :
    (tensorRightShortComplex ((normalizedCubicalChainComplex k).obj Y)
      (P.cubicalChainComplexShortComplex k)).ShortExact :=
  HomologicalComplex.shortExact_tensorRightShortComplex _ _
    (P.shortExact_cubicalChainComplexShortComplex k)

/-- The cross product carries `N(A) ⊗ N(Y)` into `N(A × Y)`. -/
private theorem whiskerRight_comp_cubicalCrossProduct :
    (normalizedCubicalChainComplex k).map P.map ▷ (normalizedCubicalChainComplex k).obj Y ≫
        TauCeti.cubicalCrossProduct k P.fst Y =
      TauCeti.cubicalCrossProduct k P.snd Y ≫
        (normalizedCubicalChainComplex k).map (P.prodRight Y).map := by
  simpa using TauCeti.cubicalCrossProduct_naturality (R := k) P.map (𝟙 Y)

/-- The cross product followed by the projection to relative chains kills `N(A) ⊗ N(Y)`. -/
private theorem whiskerRight_comp_cubicalCrossProduct_comp_π :
    (normalizedCubicalChainComplex k).map P.map ▷ (normalizedCubicalChainComplex k).obj Y ≫
      TauCeti.cubicalCrossProduct k P.fst Y ≫
        cokernel.π ((normalizedCubicalChainComplex k).map (P.prodRight Y).map) = 0 := by
  rw [reassoc_of% whiskerRight_comp_cubicalCrossProduct, cokernel.condition, comp_zero]

/-- **The relative cubical cross product** `N(X, A; k) ⊗ N(Y; k) ⟶ N(X × Y, A × Y; k)` of a pair
`P = (X, A)` and a space `Y`, sending `[a] ⊗ b` to `[a × b]` (`TopPair.π_cubicalCrossProduct`). -/
def cubicalCrossProduct :
    P.cubicalChainComplex k ⊗ (normalizedCubicalChainComplex k).obj Y ⟶
      (P.prodRight Y).cubicalChainComplex k :=
  have := (shortExact_tensorRightShortComplex k P Y).epi_g
  (shortExact_tensorRightShortComplex k P Y).exact.desc
    (TauCeti.cubicalCrossProduct k P.fst Y ≫ cokernel.π _)
    (whiskerRight_comp_cubicalCrossProduct_comp_π k P Y)

/-- The projection onto relative chains stays an epimorphism after tensoring with `N(Y)`. -/
instance epi_π_whiskerRight :
    Epi (cokernel.π ((normalizedCubicalChainComplex k).map P.map) ▷
      (normalizedCubicalChainComplex k).obj Y) := by
  rw [← tensorHom_id]
  exact (shortExact_tensorRightShortComplex k P Y).epi_g

/-- The relative cross product is induced by the cross product of normalized chains: it sends the
class `[a] ⊗ b` to the class `[a × b]`. -/
@[reassoc (attr := simp)]
theorem π_cubicalCrossProduct :
    cokernel.π ((normalizedCubicalChainComplex k).map P.map) ▷
        (normalizedCubicalChainComplex k).obj Y ≫ P.cubicalCrossProduct k Y =
      TauCeti.cubicalCrossProduct k P.fst Y ≫
        cokernel.π ((normalizedCubicalChainComplex k).map (P.prodRight Y).map) := by
  have := (shortExact_tensorRightShortComplex k P Y).epi_g
  rw [← tensorHom_id]
  exact (shortExact_tensorRightShortComplex k P Y).exact.g_desc _ _

/-- The cross products of `A × Y`, `X × Y` and the relative one form a morphism from the tensored
sequence of the pair `(X, A)` to the sequence of the pair `(X × Y, A × Y)`. -/
private def cubicalCrossProductShortComplexHom :
    tensorRightShortComplex ((normalizedCubicalChainComplex k).obj Y)
        (P.cubicalChainComplexShortComplex k) ⟶
      (P.prodRight Y).cubicalChainComplexShortComplex k where
  τ₁ := TauCeti.cubicalCrossProduct k P.snd Y
  τ₂ := TauCeti.cubicalCrossProduct k P.fst Y
  τ₃ := P.cubicalCrossProduct k Y
  comm₁₂ := (whiskerRight_comp_cubicalCrossProduct k P Y).symm
  comm₂₃ := by
    have := (shortExact_tensorRightShortComplex k P Y).epi_g
    exact ((shortExact_tensorRightShortComplex k P Y).exact.g_desc _ _).symm

/-- **The relative cubical Eilenberg–Zilber theorem**: the relative cross product
`N(X, A; k) ⊗ N(Y; k) ⟶ N(X × Y, A × Y; k)` is a quasi-isomorphism. -/
instance quasiIso_cubicalCrossProduct : QuasiIso (P.cubicalCrossProduct k Y) :=
  HomologySequence.quasiIso_τ₃ (cubicalCrossProductShortComplexHom k P Y)
    (shortExact_tensorRightShortComplex k P Y)
    ((P.prodRight Y).shortExact_cubicalChainComplexShortComplex k)
    (TauCeti.quasiIso_cubicalCrossProduct k P.snd Y)
    (TauCeti.quasiIso_cubicalCrossProduct k P.fst Y)

/-- The relative cross product induces an isomorphism on homology. -/
instance isIso_homologyMap_cubicalCrossProduct (n : ℕ) :
    IsIso (homologyMap (P.cubicalCrossProduct k Y) n) :=
  (quasiIsoAt_iff_isIso_homologyMap _ _).1 inferInstance

/-- **Naturality** of the relative cross product in the pair and in the space. -/
@[reassoc]
theorem cubicalCrossProduct_naturality {P P' : TopPair.{u}} (f : P ⟶ P') {Y Y' : TopCat.{u}}
    (g : Y ⟶ Y') :
    (cubicalChainComplexMap k f ⊗ₘ (normalizedCubicalChainComplex k).map g) ≫
        P'.cubicalCrossProduct k Y' =
      P.cubicalCrossProduct k Y ≫ cubicalChainComplexMap k (prodRightMap f g) := by
  have hπ : cokernel.π ((normalizedCubicalChainComplex k).map P.map) ▷
        (normalizedCubicalChainComplex k).obj Y ≫
          (cubicalChainComplexMap k f ⊗ₘ (normalizedCubicalChainComplex k).map g) =
      ((normalizedCubicalChainComplex k).map (Hom.fst f) ⊗ₘ
          (normalizedCubicalChainComplex k).map g) ≫
        cokernel.π ((normalizedCubicalChainComplex k).map P'.map) ▷
          (normalizedCubicalChainComplex k).obj Y' := by
    rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      π_cubicalChainComplexMap, Category.id_comp, Category.comp_id]
  rw [← cancel_epi (cokernel.π ((normalizedCubicalChainComplex k).map P.map) ▷
      (normalizedCubicalChainComplex k).obj Y), reassoc_of% hπ, π_cubicalCrossProduct,
    π_cubicalCrossProduct_assoc, TauCeti.cubicalCrossProduct_naturality_assoc,
    π_cubicalChainComplexMap, fst_prodRightMap]

/-! ### The relative Künneth theorem -/

/-- **The relative Künneth map**
`⨁_{p + q = n} Hₚ(X, A; k) ⊗ H_q(Y; k) ⟶ Hₙ(X × Y, A × Y; k)` of cubical homology: the algebraic
Künneth map of the chain complexes `N(X, A; k)` and `N(Y; k)` followed by the map induced by the
relative cross product. -/
def cubicalHomologyKunneth (n : ℕ) :
    GradedObject.Monoidal.tensorObj (fun p ↦ (P.cubicalChainComplex k).homology p)
        (fun q ↦ ((normalizedCubicalChainComplex k).obj Y).homology q) n ⟶
      ((P.prodRight Y).cubicalChainComplex k).homology n :=
  homologyKunneth (P.cubicalChainComplex k) ((normalizedCubicalChainComplex k).obj Y) n ≫
    homologyMap (P.cubicalCrossProduct k Y) n

/-- The relative Künneth map is the algebraic Künneth map of the chain complexes followed by the
map induced by the relative cross product. -/
theorem cubicalHomologyKunneth_def (n : ℕ) :
    P.cubicalHomologyKunneth k Y n =
      homologyKunneth (P.cubicalChainComplex k) ((normalizedCubicalChainComplex k).obj Y) n ≫
        homologyMap (P.cubicalCrossProduct k Y) n :=
  (rfl)

/-- The relative Künneth map restricts to the homology cross product followed by the map induced by
the relative cross product on each summand. -/
@[reassoc (attr := simp)]
theorem ι_cubicalHomologyKunneth (p q n : ℕ) (h : p + q = n) :
    GradedObject.Monoidal.ιTensorObj (fun p ↦ (P.cubicalChainComplex k).homology p)
        (fun q ↦ ((normalizedCubicalChainComplex k).obj Y).homology q) p q n h ≫
      P.cubicalHomologyKunneth k Y n =
      homologyCross (P.cubicalChainComplex k) ((normalizedCubicalChainComplex k).obj Y) p q n h ≫
        homologyMap (P.cubicalCrossProduct k Y) n := by
  rw [cubicalHomologyKunneth_def, ← Category.assoc, ι_homologyKunneth]

/-- **Naturality of the relative Künneth map** in the pair and in the space. -/
@[reassoc]
theorem cubicalHomologyKunneth_naturality {P P' : TopPair.{u}} (f : P ⟶ P') {Y Y' : TopCat.{u}}
    (g : Y ⟶ Y') (n : ℕ) :
    GradedObject.Monoidal.tensorHom (fun p ↦ homologyMap (cubicalChainComplexMap k f) p)
        (fun q ↦ homologyMap ((normalizedCubicalChainComplex k).map g) q) n ≫
      P'.cubicalHomologyKunneth k Y' n =
      P.cubicalHomologyKunneth k Y n ≫
        homologyMap (cubicalChainComplexMap k (prodRightMap f g)) n := by
  rw [cubicalHomologyKunneth_def, cubicalHomologyKunneth_def, ← Category.assoc,
    homologyKunneth_naturality, Category.assoc, ← homologyMap_comp, Category.assoc,
    ← homologyMap_comp, ← cubicalCrossProduct_naturality,
    HomologicalComplex.tensorHom_eq_mapBifunctorMap]

/-- **The relative Künneth theorem for cubical homology**: if the cycles of the relative chains of
`(X, A)` and of the chains of `Y` split off their terms and their homology splits off the cycles,
the relative Künneth map `⨁_{p + q = n} Hₚ(X, A; k) ⊗ H_q(Y; k) ⟶ Hₙ(X × Y, A × Y; k)` is an
isomorphism. -/
theorem isIso_cubicalHomologyKunneth
    [∀ p, IsSplitMono ((P.cubicalChainComplex k).iCycles p)]
    [∀ p, IsSplitEpi ((P.cubicalChainComplex k).homologyπ p)]
    [∀ q, IsSplitMono (((normalizedCubicalChainComplex k).obj Y).iCycles q)]
    [∀ q, IsSplitEpi (((normalizedCubicalChainComplex k).obj Y).homologyπ q)] (n : ℕ) :
    IsIso (P.cubicalHomologyKunneth k Y n) := by
  have := isIso_homologyKunneth_of_isSplitMono_of_isSplitEpi
    (P.cubicalChainComplex k) ((normalizedCubicalChainComplex k).obj Y) n
  rw [cubicalHomologyKunneth_def]
  infer_instance

/-- **The relative Künneth theorem over a semisimple ring**, for instance a field:
`⨁_{p + q = n} Hₚ(X, A; k) ⊗ H_q(Y; k) ≅ Hₙ(X × Y, A × Y; k)` for cubical homology. -/
instance isIso_cubicalHomologyKunneth_of_isSemisimpleRing [IsSemisimpleRing k] (n : ℕ) :
    IsIso (P.cubicalHomologyKunneth k Y n) :=
  P.isIso_cubicalHomologyKunneth k Y n

/-- **The relative Künneth theorem with projective homology**: over a principal ideal domain `k`,
if the relative cubical homology modules of `(X, A)` and the cubical homology modules of `Y` are
projective, for instance free, the relative Künneth map is an isomorphism. The cycles split off the
chains, since the relative and absolute normalized cubical chains are projective. -/
theorem isIso_cubicalHomologyKunneth_of_projective [NoZeroDivisors k] [IsPrincipalIdealRing k]
    [∀ p, CategoryTheory.Projective ((P.cubicalChainComplex k).homology p)]
    [∀ q, CategoryTheory.Projective (((normalizedCubicalChainComplex k).obj Y).homology q)]
    (n : ℕ) : IsIso (P.cubicalHomologyKunneth k Y n) :=
  P.isIso_cubicalHomologyKunneth k Y n

end TopPair

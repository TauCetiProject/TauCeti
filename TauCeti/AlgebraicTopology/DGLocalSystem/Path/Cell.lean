/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth.Projective
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.CubePair
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.FiberHomotopy
public import TauCeti.AlgebraicTopology.Singular.Cubical.Kunneth.Relative
public import TauCeti.Topology.PathSpace.Moore.Pullback

/-!
# The relative chains of the path fibration over a cell

Let `P = (D, A)` be a topological pair, `f : D → X` a map and `b ∈ X`, and let `τ d` be a
continuous family of Moore paths from `b` to `f d`. Appending `τ d` to a loop trivializes the
pulled-back based path fibration `f*P_b X` over `D` up to fibre homotopy
(`TauCeti.MoorePathPullback.fiberHomotopyEquiv`). Written with the loop first,

`Ω_b X × D ⟶ f*P_b X`, `(ω, d) ↦ ω ⋆ τ d` (`TauCeti.MoorePathPullback.loopTrivialization`),

it is strictly equivariant for the left action of the Moore loops at `b` by concatenation in
front, which acts on the loop factor of the product
(`TauCeti.MoorePathPullback.loopTrivialization_mul`). As a map of pairs
`Ω_b X × (D, A) ⟶ (f*P_b X, f*P_b X|_A)` it induces a quasi-isomorphism of relative normalized
cubical chains. Composed with the relative Eilenberg–Zilber quasi-isomorphism
`N(Ω_b X) ⊗ N(D, A) ⟶ N(Ω_b X × D, Ω_b X × A)` this gives the **relative-cell comparison**

`N(Ω_b X) ⊗ N(D, A) ⟶ N(f*P_b X, f*P_b X|_A)`

(`TauCeti.MoorePathPullback.cellChainMap`), a quasi-isomorphism over every commutative ring `k`
(`TauCeti.MoorePathPullback.quasiIso_cellChainMap`).

If the relative chains of the pair receive a quasi-isomorphism `K ⟶ N(D, A)` from a complex of
projective modules with projective homology, then `N(Ω_b X) ⊗ K` computes the relative homology of
the path fibration over the cell
(`TauCeti.MoorePathPullback.quasiIso_whiskerLeft_comp_cellChainMap`). For the cube pair
`(Iᵐ⁺¹, ∂Iᵐ⁺¹)` and `K = k[m + 1]`, with `1` sent to the fundamental cycle `[Iᵐ⁺¹]`
(`TauCeti.cubeBoundaryPairSingleHom`), this is the relative-cell quasi-isomorphism

`N(Ω_b X) ⊗ k[m + 1] ⟶ N(f*P_b X, f*P_b X|_{∂Iᵐ⁺¹})`, `a ⊗ 1 ↦ [ω ⋆ τ] ∘ (a × [Iᵐ⁺¹])`

(`TauCeti.MoorePathPullback.quasiIso_cubeBoundaryPair_cellChainMap`). It is the comparison along
which a free generator over the loop chains `C_*(Ω_b X; k)` is attached for a cell in Brown's
construction of a semi-free resolution of `k`. The loop factor is placed first so that the left
action of the loops, by concatenation in front, only involves the first factor of
`N(Ω_b X) ⊗ N(D, A)`, where it is the Pontryagin product, and the trivialization preserves it. The
loop-module structures of these chain complexes, and the excision that assembles the cells of a
CW complex, are not treated here.

## Main definitions

* `TauCeti.MoorePathPullback.loopTrivialization`: the trivialization `(ω, d) ↦ ω ⋆ τ d`, with the
  loop first.
* `TauCeti.MoorePathPullback.preimagePair`: the pair `(f*P_b X, f*P_b X|_A)` over a pair
  `(D, A)`.
* `TauCeti.MoorePathPullback.loopTrivializationPairHom`: the trivialization as a map of pairs
  `Ω_b X × (D, A) ⟶ (f*P_b X, f*P_b X|_A)`.
* `TauCeti.MoorePathPullback.cellChainMap`: the relative-cell comparison
  `N(Ω_b X) ⊗ N(D, A) ⟶ N(f*P_b X, f*P_b X|_A)`.

## Main results

* `TauCeti.MoorePathPullback.loopTrivialization_mul`: the trivialization is equivariant for
  concatenation of loops in front.
* `TauCeti.MoorePathPullback.quasiIso_cubicalChainComplexMap_loopTrivializationPairHom`: the
  trivialization is a quasi-isomorphism on relative chains.
* `TauCeti.MoorePathPullback.quasiIso_cellChainMap`: the relative-cell comparison is a
  quasi-isomorphism.
* `TauCeti.MoorePathPullback.quasiIso_whiskerLeft_comp_cellChainMap`: so is its composite with
  `N(Ω_b X) ⊗ K ⟶ N(Ω_b X) ⊗ N(D, A)` for a quasi-isomorphism `K ⟶ N(D, A)` of projective
  complexes with projective homology.
* `TauCeti.MoorePathPullback.quasiIso_cubeBoundaryPair_cellChainMap`: the relative-cell
  quasi-isomorphism `N(Ω_b X) ⊗ k[m + 1] ⟶ N(f*P_b X, f*P_b X|_{∂Iᵐ⁺¹})` of a cube.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential
  graded coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
-/

public noncomputable section

open CategoryTheory MonoidalCategory

namespace TauCeti.MoorePathPullback

universe u

/-! ### The trivialization with the loop first -/

section Trivialization

variable {D X : Type*} [TopologicalSpace D] [TopologicalSpace X] {f : C(D, X)} {b : X}
  (τ : C(D, MoorePath X)) (h₀ : ∀ d, (τ d).source = b) (h₁ : ∀ d, (τ d).target = f d)

/-- The trivialization `Ω_b X × D ⟶ f*P_b X`, `(ω, d) ↦ ω ⋆ τ d`, of the pulled-back based path
fibration, with the loop as the first factor. It is `TauCeti.MoorePathPullback.trivializationMap`
with the factors swapped. -/
def loopTrivialization : C(MooreLoopSpace X b × D, MoorePathPullback f b) :=
  (trivializationMap τ h₀ h₁).comp ContinuousMap.prodSwap

@[simp]
theorem loopTrivialization_apply (ω : MooreLoopSpace X b) (d : D) :
    loopTrivialization τ h₀ h₁ (ω, d) = trivializationMap τ h₀ h₁ (d, ω) :=
  (rfl)

/-- The trivialization is equivariant: concatenating a loop in front of the loop factor
concatenates it in front of the path. -/
theorem loopTrivialization_mul (ω η : MooreLoopSpace X b) (d : D) :
    loopTrivialization τ h₀ h₁ (ω * η, d) = ω • loopTrivialization τ h₀ h₁ (η, d) :=
  trivializationMap_mul τ h₀ h₁ d ω η

end Trivialization

/-! ### The trivialization as a map of pairs -/

section Pair

variable (P : TopPair.{u}) {X : Type u} [TopologicalSpace X]

/-- The pair `(f*P_b X, f*P_b X|_A)` formed by the pulled-back based path fibration over the
ambient space of a pair `P = (D, A)` and its part over `A`. -/
abbrev preimagePair (f : C(P.fst, X)) (b : X) : TopPair.{u} :=
  TopPair.ofSubset (X := TopCat.of (MoorePathPullback f b)) (proj f b ⁻¹' Set.range P.map)

variable {f : C(P.fst, X)} {b : X} (τ : C(P.fst, MoorePath X)) (h₀ : ∀ d, (τ d).source = b)
  (h₁ : ∀ d, (τ d).target = f d)

/-- The trivialization `(ω, d) ↦ ω ⋆ τ d` as a map of pairs
`Ω_b X × (D, A) ⟶ (f*P_b X, f*P_b X|_A)`. -/
def loopTrivializationPairHom :
    P.prodLeft (TopCat.of (MooreLoopSpace X b)) ⟶ preimagePair P f b :=
  TopPair.ofHom (TopCat.ofHom (loopTrivialization τ h₀ h₁))
    (TopCat.ofHom ⟨fun z ↦ ⟨loopTrivialization τ h₀ h₁ (z.1, P.map z.2), z.2, by simp [proj_apply]⟩,
      ((loopTrivialization τ h₀ h₁).continuous.comp
        (continuous_fst.prodMk (P.map.hom.continuous.comp continuous_snd))).subtype_mk _⟩)
    (by ext; rfl)

@[simp]
theorem loopTrivializationPairHom_fst :
    TopPair.Hom.fst (loopTrivializationPairHom P τ h₀ h₁) =
      TopCat.ofHom (loopTrivialization τ h₀ h₁) :=
  (rfl)

/-- Swapping the factors identifies `Ω_b X × (D, A)` with the pair `(D × Ω_b X, A × Ω_b X)` of
the preimage of `A`. -/
private def swapPairHom :
    P.prodLeft (TopCat.of (MooreLoopSpace X b)) ⟶
      TopPair.ofSubset (X := TopCat.of (P.fst × MooreLoopSpace X b))
        ((ContinuousMap.fst : C(P.fst × MooreLoopSpace X b, P.fst)) ⁻¹' Set.range P.map) :=
  TopPair.ofHom (TopCat.isoOfHomeo (X := TopCat.of (MooreLoopSpace X b) ⊗ P.fst)
      (Y := TopCat.of (P.fst × MooreLoopSpace X b)) (Homeomorph.prodComm _ _)).hom
    (TopCat.ofHom ⟨fun z ↦ ⟨(P.map z.2, z.1), z.2, rfl⟩,
      ((P.map.hom.continuous.comp continuous_snd).prodMk continuous_fst).subtype_mk _⟩)
    (by ext; rfl)

private instance isIso_swapPairHom : IsIso (swapPairHom P (b := b)) := by
  have : IsIso (TopPair.Hom.fst (swapPairHom P (b := b))) :=
    inferInstanceAs (IsIso (TopCat.isoOfHomeo (X := TopCat.of (MooreLoopSpace X b) ⊗ P.fst)
      (Y := TopCat.of (P.fst × MooreLoopSpace X b)) (Homeomorph.prodComm _ _)).hom)
  refine TopPair.isIso_of_isIso_fst_of_surjective_snd _ ?_
  rintro ⟨⟨d, ω⟩, a, ha⟩
  exact ⟨(ω, a), Subtype.ext (Prod.ext ha rfl)⟩

/-- The loop-first trivialization is the swap followed by the trivialization of
`TauCeti.MoorePathPullback.fiberHomotopyEquiv`. -/
private theorem swapPairHom_comp_preimagePairMap :
    swapPairHom P ≫ (fiberHomotopyEquiv τ h₀ h₁).preimagePairMap (Set.range P.map) =
      loopTrivializationPairHom P τ h₀ h₁ :=
  TopPair.hom_ext_of_fst _ (by
    rw [TopPair.Hom.fst_comp, FiberHomotopyEquiv.preimagePairMap_fst, fiberHomotopyEquiv_toFun]
    rfl)

/-- The trivialization `Ω_b X × (D, A) ⟶ (f*P_b X, f*P_b X|_A)` induces a quasi-isomorphism of
relative normalized cubical chains: it is a homeomorphism of pairs followed by a fibre homotopy
equivalence over `D`. -/
instance quasiIso_cubicalChainComplexMap_loopTrivializationPairHom (R : Type u) [Ring R] :
    QuasiIso (TopPair.cubicalChainComplexMap R (loopTrivializationPairHom P τ h₀ h₁)) := by
  have : IsIso (TopPair.cubicalChainComplexMap R (swapPairHom P (b := b))) :=
    ⟨TopPair.cubicalChainComplexMap R (inv (swapPairHom P)), by
      rw [← TopPair.cubicalChainComplexMap_comp, IsIso.hom_inv_id,
        TopPair.cubicalChainComplexMap_id], by
      rw [← TopPair.cubicalChainComplexMap_comp, IsIso.inv_hom_id,
        TopPair.cubicalChainComplexMap_id]⟩
  have : QuasiIso (TopPair.cubicalChainComplexMap R
      ((fiberHomotopyEquiv τ h₀ h₁).preimagePairMap (Set.range P.map))) := by
    rw [← FiberHomotopyEquiv.relativeCubicalChainHomotopyEquiv_hom]
    infer_instance
  rw [← swapPairHom_comp_preimagePairMap, TopPair.cubicalChainComplexMap_comp]
  infer_instance

end Pair

/-! ### The relative-cell comparison -/

section Chains

variable (P : TopPair.{u}) {X : Type u} [TopologicalSpace X] {f : C(P.fst, X)} {b : X}
  (τ : C(P.fst, MoorePath X)) (h₀ : ∀ d, (τ d).source = b) (h₁ : ∀ d, (τ d).target = f d)
  (k : Type u) [CommRing k]

/-- **The relative-cell comparison** `N(Ω_b X) ⊗ N(D, A) ⟶ N(f*P_b X, f*P_b X|_A)` over a pair
`P = (D, A)`: the relative cross product `N(Ω_b X) ⊗ N(D, A) ⟶ N(Ω_b X × D, Ω_b X × A)` followed
by the loop-first trivialization `(ω, d) ↦ ω ⋆ τ d`. -/
def cellChainMap :
    (normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b)) ⊗
        P.cubicalChainComplex k ⟶ (preimagePair P f b).cubicalChainComplex k :=
  cubicalCrossProductRel k (TopCat.of (MooreLoopSpace X b)) P ≫
    TopPair.cubicalChainComplexMap k (loopTrivializationPairHom P τ h₀ h₁)

/-- On a tensor product of chains, the relative-cell comparison is the relative chain of the
trivialization of their cross product. -/
theorem cellChainMap_f_ιTensorObj_tmul {p q n : ℕ} (h : p + q = n)
    (a : NormalizedCubicalChain (TopCat.of (MooreLoopSpace X b)) k p)
    (c : NormalizedCubicalChain P.fst k q) :
    (cellChainMap P τ h₀ h₁ k).f n
        (HomologicalComplex.ιTensorObj
          ((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b)))
          (P.cubicalChainComplex k) p q n h
          (a ⊗ₜ (Limits.cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f q c)) =
      (TopPair.cubicalChainComplexMap k (loopTrivializationPairHom P τ h₀ h₁)).f n
        ((Limits.cokernel.π ((normalizedCubicalChainComplex k).map
          (P.prodLeft (TopCat.of (MooreLoopSpace X b))).map)).f n
          (NormalizedCubicalChain.cast k h
            (NormalizedCubicalChain.crossProduct (TopCat.of (MooreLoopSpace X b)) P.fst k p q
              a c))) := by
  rw [cellChainMap, HomologicalComplex.comp_f, ModuleCat.comp_apply,
    cubicalCrossProductRel_f_ιTensorObj_tmul]

/-- **The relative-cell comparison is a quasi-isomorphism**: the relative cubical
Eilenberg–Zilber theorem and the fibre homotopy trivialization of the path fibration over `D`. -/
instance quasiIso_cellChainMap : QuasiIso (cellChainMap P τ h₀ h₁ k) := by
  rw [cellChainMap]
  infer_instance

/-- **Relative-cell comparison from a model of the cell.** If `ι : K ⟶ N(D, A)` is a
quasi-isomorphism from a complex of projective modules with projective homology, for instance
`k[n]` mapped to a fundamental cycle of the cell, then
`N(Ω_b X) ⊗ K ⟶ N(Ω_b X) ⊗ N(D, A) ⟶ N(f*P_b X, f*P_b X|_A)` is a quasi-isomorphism. -/
theorem quasiIso_whiskerLeft_comp_cellChainMap {K : ChainComplex (ModuleCat.{u} k) ℕ}
    [∀ p, Module.Projective k (K.X p)] [∀ p, Module.Projective k (K.homology p)]
    (ι : K ⟶ P.cubicalChainComplex k) [QuasiIso ι] :
    QuasiIso ((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b)) ◁ ι ≫
      cellChainMap P τ h₀ h₁ k) := by
  have := HomologicalComplex.quasiIso_whiskerLeft_of_projective
    ((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b))) ι
  infer_instance

end Chains

/-! ### The cube -/

section Cube

variable {X : Type} [TopologicalSpace X] {b : X} (m : ℕ)
  {f : C((cubeBoundaryPair.{0} (m + 1)).fst, X)} (τ : C((cubeBoundaryPair.{0} (m + 1)).fst,
    MoorePath X)) (h₀ : ∀ d, (τ d).source = b) (h₁ : ∀ d, (τ d).target = f d)
  (k : Type) [CommRing k]

/-- **The relative-cell quasi-isomorphism of a cube.** For a map `f : Iᵐ⁺¹ ⟶ X` and paths `τ d`
from `b` to `f d`, the chain map `N(Ω_b X) ⊗ k[m + 1] ⟶ N(f*P_b X, f*P_b X|_{∂Iᵐ⁺¹})` sending
`a ⊗ 1` to the trivialization of the cross product `a × [Iᵐ⁺¹]` is a quasi-isomorphism, over every
commutative ring `k`. -/
theorem quasiIso_cubeBoundaryPair_cellChainMap :
    QuasiIso ((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b)) ◁
      cubeBoundaryPairSingleHom k m ≫ cellChainMap (cubeBoundaryPair.{0} (m + 1)) τ h₀ h₁ k) := by
  have (p : ℕ) : Module.Projective k
      (((HomologicalComplex.single (ModuleCat.{0} k) (ComplexShape.down ℕ) (m + 1)).obj
        (ModuleCat.of k k)).X p) := by
    by_cases hp : p = m + 1
    · subst hp
      exact .of_equiv (R := k) (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) (m + 1)
        (ModuleCat.of k k)).symm.toLinearEquiv
    · have := ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) (m + 1)
          (ModuleCat.of k k) p hp)
      infer_instance
  have (p : ℕ) : Module.Projective k
      (((HomologicalComplex.single (ModuleCat.{0} k) (ComplexShape.down ℕ) (m + 1)).obj
        (ModuleCat.of k k)).homology p) := by
    by_cases hp : p = m + 1
    · subst hp
      exact .of_equiv (R := k) (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ)
        (m + 1) (ModuleCat.of k k)).symm.toLinearEquiv
    · have := ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_homology (ComplexShape.down ℕ) (m + 1)
          (ModuleCat.of k k) p hp)
      infer_instance
  exact quasiIso_whiskerLeft_comp_cellChainMap _ τ h₀ h₁ k (cubeBoundaryPairSingleHom k m)

end Cube

end TauCeti.MoorePathPullback

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Reduced
public import TauCeti.AlgebraicTopology.Singular.Relative
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Singular homology of contractible spaces and the reduced connecting morphism

A contractible space has the singular homology of a point: its homology vanishes in every positive
degree, and its reduced homology vanishes in every degree.

For every topological pair `(X, A)`, the connecting morphism `Hₖ₊₁(X, A) ⟶ Hₖ(A)` of the long
exact sequence lands in the reduced homology `H~ₖ(A)`: in degree zero, it is followed by the map
`H₀(A) ⟶ H₀(X)`, which commutes with the augmentations.  This defines the reduced connecting
morphism `Hₖ₊₁(X, A) ⟶ H~ₖ(A)`, natural in maps of pairs.  When the reduced homology of `X`
vanishes in degrees `k` and `k + 1` it is an isomorphism, and in particular it is an isomorphism
in every degree when `X` is contractible.  For the pair `TauCeti.diskBoundaryPair n` of a disk and
its boundary sphere, whose ambient space is contractible by
`TauCeti.contractibleSpace_diskBoundaryPair_fst`, this identifies `Hₖ₊₁(Dⁿ, Sⁿ⁻¹)` with the
reduced homology `H~ₖ(Sⁿ⁻¹)`, by the connecting morphism itself, so that the relative homology of
a disk modulo its boundary is computed by the reduced homology of spheres.

Coefficients are an object `R` of an abelian category with coproducts, as everywhere in relative
singular homology.

## Main declarations

* `TauCeti.isZero_singularHomologyFunctor_of_contractibleSpace`: the positive-degree singular
  homology of a contractible space vanishes.
* `TauCeti.isZero_reducedSingularHomologyFunctor_of_contractibleSpace`: the reduced singular
  homology of a contractible space vanishes in every degree.
* `TopPair.reducedSingularHomologyδ`: the connecting morphism `Hₖ₊₁(X, A) ⟶ H~ₖ(A)` into the
  reduced homology of the subspace, with `TopPair.reducedSingularHomologyδ_comp_ι` and
  `TopPair.reducedSingularHomologyδ_naturality`.
* `TopPair.isIso_reducedSingularHomologyδ`: it is an isomorphism when the reduced homology of the
  ambient space vanishes in the two adjacent degrees, and in every degree when the ambient space
  is contractible.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1: Corollary 2.11 and the vanishing of the reduced
  homology of contractible spaces, the long exact sequence of reduced homology of a pair, and
  Example 2.23 for the disk and its boundary sphere.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe w v u

namespace TauCeti

section Contractible

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [CategoryWithHomology C] (R : C)

/-- **The positive-degree singular homology of a contractible space vanishes.**  The identity of
a contractible space is homotopic to a map factoring through a point, whose positive-degree
homology vanishes. -/
theorem isZero_singularHomologyFunctor_of_contractibleSpace (X : TopCat.{w})
    [ContractibleSpace X] {n : ℕ} (hn : n ≠ 0) :
    IsZero (((singularHomologyFunctor C n).obj R).obj X) := by
  obtain ⟨x, ⟨H⟩⟩ := id_nullhomotopic X
  let pt : TopCat.{w} := TopCat.of PUnit
  let p : X ⟶ pt := TopCat.ofHom (ContinuousMap.const X PUnit.unit)
  let s : pt ⟶ X := TopCat.ofHom (ContinuousMap.const pt x)
  have hpt : IsZero (((singularHomologyFunctor C n).obj R).obj pt) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n R pt hn
  have hid : ((singularHomologyFunctor C n).obj R).map (p ≫ s) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_id]
    -- The underlying continuous maps of `p ≫ s` and `𝟙 X` are `ContinuousMap.const X x` and
    -- `ContinuousMap.id X` by definition, so `H.symm` is a homotopy between them.
    exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor (f := p ≫ s) (g := 𝟙 X)
      H.symm R n
  rw [IsZero.iff_id_eq_zero, ← hid, CategoryTheory.Functor.map_comp, hpt.eq_of_src
    (((singularHomologyFunctor C n).obj R).map s) 0, comp_zero]

variable [HasKernels C]

/-- **The reduced singular homology of a contractible space vanishes in every degree.** -/
theorem isZero_reducedSingularHomologyFunctor_of_contractibleSpace (X : TopCat.{w})
    [ContractibleSpace X] (n : ℕ) :
    IsZero ((reducedSingularHomologyFunctor R n).obj X) := by
  cases n with
  | zero => exact isZero_reducedSingularHomologyFunctor_zero R X
  | succ n =>
    exact (isZero_singularHomologyFunctor_of_contractibleSpace R X n.succ_ne_zero).of_iso
      ((reducedSingularHomologySuccIso R n).app X)

end Contractible

end TauCeti

namespace TopPair

open TauCeti

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (P : TopPair.{w}) (R : A)

/-- The connecting morphism `Hₖ₊₁(X, A) ⟶ Hₖ(A)` of a topological pair, with its target written as
the singular homology of the subspace, the form in which reduced homology is defined. -/
private abbrev δ (k : ℕ) :
    P.singularHomology R (k + 1) ⟶ ((AlgebraicTopology.singularHomologyFunctor A k).obj R).obj
      P.snd :=
  P.singularHomologyδ R (k + 1) k

/-- The connecting morphism of a topological pair followed by the augmentation of the subspace
vanishes, since the augmentation of the subspace factors through the zeroth homology of the
ambient space. -/
private lemma δ_comp_singularHomology₀ε : δ P R 0 ≫ P.snd.singularHomology₀ε R = 0 := by
  rw [← singularHomologyMap_singularHomology₀ε R P.map, ← Category.assoc]
  exact (P.singularHomologyδ_comp R 1 0 =≫ _).trans zero_comp

/-- The connecting morphism `Hₖ₊₁(X, A) ⟶ H~ₖ(A)` of a topological pair `(X, A)`, into the reduced
singular homology of the subspace.  It lifts the connecting morphism of the long exact sequence
of the pair through the inclusion of reduced into ordinary homology
(`TopPair.reducedSingularHomologyδ_comp_ι`). -/
def reducedSingularHomologyδ : (k : ℕ) →
    P.singularHomology R (k + 1) ⟶ (reducedSingularHomologyFunctor R k).obj P.snd
  | 0 => kernel.lift _ (δ P R 0) (δ_comp_singularHomology₀ε P R) ≫
      eqToHom (reducedSingularHomologyFunctor_zero_obj R P.snd).symm
  | k + 1 => δ P R (k + 1) ≫ (reducedSingularHomologySuccIso R k).inv.app P.snd

/-- The reduced connecting morphism followed by the inclusion of reduced into ordinary homology
is the connecting morphism of the long exact sequence of the pair. -/
@[reassoc (attr := simp)]
lemma reducedSingularHomologyδ_comp_ι (k : ℕ) :
    P.reducedSingularHomologyδ R k ≫ (reducedSingularHomologyι R k).app P.snd =
      P.singularHomologyδ R (k + 1) k := by
  cases k with
  | zero => simp [reducedSingularHomologyδ]
  | succ k => simp [reducedSingularHomologyδ, ← reducedSingularHomologySuccIso_hom]

/-- **Naturality of the reduced connecting morphism** under maps of topological pairs. -/
@[reassoc]
lemma reducedSingularHomologyδ_naturality {P P' : TopPair.{w}} (f : P ⟶ P') (k : ℕ) :
    P.reducedSingularHomologyδ R k ≫ (reducedSingularHomologyFunctor R k).map (Hom.snd f) =
      TopPair.singularHomologyMap f R (k + 1) ≫ P'.reducedSingularHomologyδ R k := by
  rw [← cancel_mono ((reducedSingularHomologyι R k).app P'.snd), Category.assoc,
    (reducedSingularHomologyι R k).naturality, reducedSingularHomologyδ_comp_ι_assoc,
    Category.assoc, reducedSingularHomologyδ_comp_ι]
  exact P.singularHomologyδ_naturality R f (k + 1) k

/-- **The reduced connecting morphism is an isomorphism when the ambient space is acyclic in the
adjacent degrees**: if the reduced homology of `X` vanishes in degrees `k` and `k + 1`, then
`Hₖ₊₁(X, A) ⟶ H~ₖ(A)` is an isomorphism. -/
theorem isIso_reducedSingularHomologyδ {k : ℕ}
    (h₁ : IsZero ((reducedSingularHomologyFunctor R (k + 1)).obj P.fst))
    (h₀ : IsZero ((reducedSingularHomologyFunctor R k).obj P.fst)) :
    IsIso (P.reducedSingularHomologyδ R k) := by
  -- The long exact sequence `Hₖ₊₁(X) ⟶ Hₖ₊₁(X, A) ⟶ Hₖ(A) ⟶ Hₖ(X)` exhibits the connecting
  -- morphism as a monomorphism, and then as a kernel of `Hₖ(A) ⟶ Hₖ(X)`, through which the
  -- inclusion of the reduced homology of `A` factors.
  have hX : IsZero ((toSSetPair.obj P).right.homology R (k + 1)) :=
    h₁.of_iso ((reducedSingularHomologySuccIso R k).app P.fst).symm
  have : Mono (δ P R k) :=
    (P.singularHomology_exact_relative R (k + 1) k).mono_g (hX.eq_of_src _ _)
  have hι : (reducedSingularHomologyι R k).app P.snd ≫
      ((AlgebraicTopology.singularHomologyFunctor A k).obj R).map P.map = 0 := by
    rw [← (reducedSingularHomologyι R k).naturality, h₀.eq_of_tgt
      ((reducedSingularHomologyFunctor R k).map P.map) 0, zero_comp]
  have hS := P.singularHomology_exact_subspace R (k + 1) k
  -- The first map of the short complex `hS` is the connecting morphism, by definition.
  have : Mono (ShortComplex.mk _ _ (P.singularHomologyδ_comp R (k + 1) k)).f := this
  obtain ⟨m, hm⟩ := KernelFork.IsLimit.lift' hS.fIsKernel _ hι
  -- The inclusion of the kernel fork `KernelFork.ofι δ _` is `δ`, by definition.
  replace hm : m ≫ P.singularHomologyδ R (k + 1) k =
      (reducedSingularHomologyι R k).app P.snd := hm
  refine ⟨m, ?_, ?_⟩
  · rw [← cancel_mono (P.singularHomologyδ R (k + 1) k), Category.assoc, hm]
    exact (P.reducedSingularHomologyδ_comp_ι R k).trans (Category.id_comp _).symm
  · rw [← cancel_mono ((reducedSingularHomologyι R k).app P.snd), Category.assoc,
      reducedSingularHomologyδ_comp_ι]
    exact hm.trans (Category.id_comp _).symm

/-- The reduced connecting morphism of a pair with contractible ambient space is an isomorphism
in every degree. -/
instance isIso_reducedSingularHomologyδ_of_contractibleSpace [ContractibleSpace P.fst] (k : ℕ) :
    IsIso (P.reducedSingularHomologyδ R k) :=
  P.isIso_reducedSingularHomologyδ R
    (isZero_reducedSingularHomologyFunctor_of_contractibleSpace R P.fst (k + 1))
    (isZero_reducedSingularHomologyFunctor_of_contractibleSpace R P.fst k)

end TopPair

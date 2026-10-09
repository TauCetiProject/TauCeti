/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Reduced
public import TauCeti.AlgebraicTopology.Singular.Relative

/-!
# Reduced connecting morphism for relative singular homology

For every topological pair `(X, A)`, the connecting morphism `Hₖ₊₁(X, A) ⟶ Hₖ(A)` of the long
exact sequence lands in the reduced homology of `A`. In degree zero, this follows because the
connecting morphism is killed by the map to `H₀(X)`, which commutes with augmentation.
The resulting morphism `TopPair.reducedSingularHomologyδ` is natural in maps of pairs and is an
isomorphism when the reduced homology of `X` vanishes in degrees `k` and `k + 1`.

Coefficients are an object of an abelian category with coproducts.

The construction follows Hatcher, *Algebraic Topology*, Section 2.1, on the reduced long exact
sequence of a pair.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe w v u

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

/-- **Degree-zero relative homology of a path-connected space vanishes** relative to a nonempty
subspace: every point of `X` is homologous to a point of `A`, so `H₀(A) ⟶ H₀(X)` is onto. -/
theorem isZero_singularHomology_zero [PathConnectedSpace P.fst] [Nonempty P.snd] :
    IsZero (P.singularHomology R 0) := by
  -- Through the augmentation `H₀(X) ≅ R`, the map `H₀(A) ⟶ H₀(X)` becomes the augmentation of
  -- `A`, which the class of a point of `A` splits.
  have hε : Epi ((AlgebraicTopology.singularHomologyFunctor A 0 |>.obj R).map P.map ≫
      P.fst.singularHomology₀ε R) := by
    rw [singularHomologyMap_singularHomology₀ε]
    exact (IsSplitEpi.mk' ⟨_, singularHomology₀Section_singularHomology₀ε R
      (Classical.arbitrary P.snd)⟩).epi
  have : Epi ((AlgebraicTopology.singularHomologyFunctor A 0 |>.obj R).map P.map) :=
    (epi_comp_iff_of_isIso _ _).mp hε
  have h0 : P.singularHomologyπ R 0 = 0 := (P.singularHomology_exact_space R 0).epi_f_iff.1 this
  have hπ : Epi (P.singularHomologyπ R 0) := inferInstance
  rw [h0] at hπ
  exact IsZero.of_epi_zero ((toSSetPair.obj P).right.homology R 0) _

end TopPair

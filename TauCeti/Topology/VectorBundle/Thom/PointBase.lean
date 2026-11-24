/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.EulerClass
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Basic

/-!
# Thom-pair homology of vector bundles over subsingleton and point bases

Let `E → B` be a real vector bundle of finite rank `r = finrank ℝ F`. When the base `B` is a
subsingleton, the fibre inclusion `(E_b, E_b ∖ {0}) ⟶ (E, E₀)` is an isomorphism of topological
pairs (`TauCeti.isIso_fiberThomPairMap_of_subsingleton`), so choosing a linear isomorphism between
the fibre `E b` and `ℝʳ` yields an isomorphism of topological pairs from the punctured Euclidean
space `(ℝʳ, ℝʳ ∖ {0})` to the Thom pair `(E, E₀)` (`TauCeti.fiberEuclideanPairIso`).

As a consequence, with arbitrary abelian coefficients `R` (requiring no filtered-colimit
hypotheses):

* `TauCeti.isZero_singularHomology_thomPair_of_subsingleton_of_ne`: `Hₙ(E, E₀; R) = 0` for every
  `n ≠ finrank ℝ F` when `Subsingleton B` (including the empty-base case).
* `TauCeti.singularHomologyThomPairIsoOfUnique`: over a one-point base (`Unique B`),
  `Hᵣ(E, E₀; R) ≅ R` in the rank degree `r = finrank ℝ F`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press (1963),
  §3.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Module Set Topology

universe uF w v u

namespace TauCeti

/-- Over a subsingleton base `B`, choosing a linear equivalence of the fibre `E b` with
`EuclideanSpace ℝ (ULift.{w} (Fin (finrank ℝ F)))` yields an isomorphism of topological pairs
`(ℝʳ, ℝʳ ∖ {0}) ≅ (E, E₀)`, factoring through the fibre inclusion `fiberThomPairMap F E b`.
Because no orientation is assumed on `E`, this isomorphism depends on the choice of coordinates. -/
def fiberEuclideanPairIso
    {B : Type w} [TopologicalSpace B] [Subsingleton B]
    (F : Type uF) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (E : B → Type w) [TopologicalSpace (TotalSpace F E)]
    [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [VectorBundle ℝ F E] (b : B) :
    TopPair.ofSubset (X := TopCat.of (EuclideanSpace ℝ (ULift.{w} (Fin (finrank ℝ F)))))
      ({0}ᶜ : Set _) ≅ thomPair F E :=
  (((trivializationAt F E b).continuousLinearEquivAt ℝ b
      (mem_baseSet_trivializationAt F E b)).trans
    (LinearEquiv.ofFinrankEq F _
      (finrank_euclideanSpace_ulift_fin _).symm).toContinuousLinearEquiv).complZeroPairIso.symm ≪≫
    asIso (fiberThomPairMap F E b)

/-- `fiberEuclideanPairIso` sends the origin of `ℝʳ` to the zero vector of the fibre over `b`. -/
@[simp]
theorem fiberEuclideanPairIso_hom_fst_zero
    {B : Type w} [TopologicalSpace B] [Subsingleton B]
    (F : Type uF) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (E : B → Type w) [TopologicalSpace (TotalSpace F E)]
    [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [VectorBundle ℝ F E] (b : B) :
    TopPair.Hom.fst (fiberEuclideanPairIso F E b).hom
        (0 : EuclideanSpace ℝ (ULift.{w} (Fin (finrank ℝ F)))) =
      TotalSpace.mk b (0 : E b) := by
  let e := ((trivializationAt F E b).continuousLinearEquivAt ℝ b
      (mem_baseSet_trivializationAt F E b)).trans
    (LinearEquiv.ofFinrankEq F (EuclideanSpace ℝ (ULift.{w} (Fin (finrank ℝ F))))
      (finrank_euclideanSpace_ulift_fin _).symm).toContinuousLinearEquiv
  unfold fiberEuclideanPairIso
  rw [Iso.trans_hom, Iso.symm_hom, asIso_hom, TopPair.Hom.fst_comp]
  exact (ConcreteCategory.comp_apply _ _ _).trans <|
    (congrArg (TopPair.Hom.fst (fiberThomPairMap F E b)) <|
      (ContinuousLinearEquiv.complZeroPairIso_inv_fst_apply e 0).trans (map_zero e.symm)).trans
      (fiberThomPairMap_fst_apply F E b 0)

/-- The inverse of `fiberEuclideanPairIso` sends the zero vector of the fibre over `b` to `0`. -/
@[simp]
theorem fiberEuclideanPairIso_inv_fst_zero
    {B : Type w} [TopologicalSpace B] [Subsingleton B]
    (F : Type uF) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (E : B → Type w) [TopologicalSpace (TotalSpace F E)]
    [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [VectorBundle ℝ F E] (b : B) :
    TopPair.Hom.fst (fiberEuclideanPairIso F E b).inv (TotalSpace.mk b (0 : E b)) =
      (0 : EuclideanSpace ℝ (ULift.{w} (Fin (finrank ℝ F)))) := by
  rw [← fiberEuclideanPairIso_hom_fst_zero F E b]
  exact (ConcreteCategory.comp_apply
    (TopPair.Hom.fst (fiberEuclideanPairIso F E b).hom)
    (TopPair.Hom.fst (fiberEuclideanPairIso F E b).inv) _).symm.trans <| by
      rw [← TopPair.Hom.fst_comp, Iso.hom_inv_id, TopPair.Hom.fst_id]
      rfl

/-- Over a subsingleton base, the relative singular homology of the Thom pair `(E, E₀)` vanishes
in every degree `n ≠ finrank ℝ F`, for arbitrary abelian coefficients with coproducts (without
filtered-colimit hypotheses). -/
theorem isZero_singularHomology_thomPair_of_subsingleton_of_ne
    {B : Type w} [TopologicalSpace B] [Subsingleton B]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
    [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [VectorBundle ℝ F E]
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
    (R : C) {n : ℕ} (hn : n ≠ finrank ℝ F) :
    IsZero ((thomPair F E).singularHomology R n) := by
  by_cases hB : Nonempty B
  · obtain ⟨b⟩ := hB
    exact (isZero_singularHomology_complSingleton_of_ne R (OpenPartialHomeomorph.refl _)
      (mem_univ 0) (finrank_euclideanSpace_ulift_fin (finrank ℝ F)) hn).of_iso
        (TopPair.singularHomologyMapIso R (fiberEuclideanPairIso F E b).symm n)
  · have : IsEmpty B := not_nonempty_iff.1 hB
    exact TopPair.isZero_singularHomology_of_surjective_map (thomPair F E) R
      (fun v ↦ isEmptyElim v.proj) n

/-- Over a one-point base (`Unique B`), the relative singular homology of the Thom pair `(E, E₀)`
in the rank degree `finrank ℝ F` is isomorphic to one copy of the coefficients `R`, obtained by
choosing a linear equivalence of the unique fibre with `ℝ^(dim F)` (`LinearEquiv.ofFinrankEq`) and
applying `TauCeti.singularHomologyComplSingletonFinrankIso`. Because no orientation is assumed on
`E`, this isomorphism depends up to sign on that choice of coordinates; invariants such as
`Module.finrank` are independent of the choice. -/
def singularHomologyThomPairIsoOfUnique
    {B : Type w} [TopologicalSpace B] [Unique B]
    (F : Type uF) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (E : B → Type w) [TopologicalSpace (TotalSpace F E)]
    [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [VectorBundle ℝ F E]
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) :
    (thomPair F E).singularHomology R (finrank ℝ F) ≅ R :=
  (TopPair.singularHomologyMapIso R (fiberEuclideanPairIso F E default) (finrank ℝ F)).symm ≪≫
    TopPair.singularHomologyCongrDegreeIso _ R
      (finrank_euclideanSpace_ulift_fin (finrank ℝ F)).symm ≪≫
    singularHomologyComplSingletonFinrankIso R (OpenPartialHomeomorph.refl _) (mem_univ 0)

end TauCeti

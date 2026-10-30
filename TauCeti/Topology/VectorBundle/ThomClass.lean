/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Local.Basic
public import TauCeti.Topology.VectorBundle.EulerClass

/-!
# Thom classes of trivial bundles

The trivial bundle `B × F → B` with finite-dimensional real fibre `F` of rank `r` has Thom pair
`(B × F, B × (F ∖ {0}))`, and the projection to the fibre is a map of pairs
`(B × F, B × (F ∖ {0})) ⟶ (F, F ∖ {0})` (`TauCeti.trivialThomPairMap`). Restricted to the fibre over
any point, it is the identity of `(F, F ∖ {0})`. So the pull-back `p^* u` of a class
`u ∈ Hʳ(F, F ∖ {0})` restricts to `u` on every fibre, and it is a Thom class
(`TauCeti.IsThomClass`) exactly when `u` generates `Hʳ(F, F ∖ {0})`, provided the base is nonempty
(`TauCeti.isThomClass_singularCohomologyMap_trivialThomPairMap_iff`).

With coefficients in a commutative ring `k`, the local cohomology `Hʳ(F, F ∖ {0}; k, k)` is one
copy of `k` (`TauCeti.singularCohomologyComplSingletonFinrankEquivSelf`), so it has a generator,
and every trivial bundle has a Thom class (`TauCeti.exists_isThomClass_trivial`). This is the local
model of the Thom isomorphism: a vector bundle is locally trivial, and an orientation selects a
compatible family of these local Thom classes.

## Main definitions and results

* `TauCeti.trivialThomPairMap`: the projection of the Thom pair of the trivial bundle onto the
  fibre pair `(F, F ∖ {0})`.
* `TauCeti.fiberThomPairMap_comp_trivialThomPairMap`: the projection restricts to the identity on
  every fibre.
* `TauCeti.isThomClass_singularCohomologyMap_trivialThomPairMap_iff`: the pull-back of a class of
  the fibre pair is a Thom class iff that class generates.
* `TauCeti.exists_isThomClass_trivial`: the trivial bundle has a Thom class with coefficients in
  any commutative ring.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (the Thom isomorphism, first for trivial bundles).
* A. Hatcher, *Vector Bundles and K-Theory*, §4.D (Thom classes).
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Module

universe w v u

namespace TauCeti

variable (B : Type w) [TopologicalSpace B] (F : Type w) {C : Type u} [Category.{v} C]
  [HasCoproducts.{w} C] [Abelian C] {R : C} {k : Type*} [Ring k] [Linear k C] {M : C}

section Projection

variable [TopologicalSpace F] [Zero F]

/-- The projection `(B × F, B × (F ∖ {0})) ⟶ (F, F ∖ {0})` of the Thom pair of the trivial bundle
onto its fibre pair. -/
def trivialThomPairMap :
    thomPair F (Bundle.Trivial B F) ⟶ TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F) :=
  TopPair.ofSubsetMap
    (TopCat.ofHom ⟨TotalSpace.trivialSnd B F,
      continuous_snd.comp (Bundle.Trivial.homeomorphProd B F).continuous⟩)
    fun _ hv ↦ mem_zeroSectionCompl.1 hv

@[simp]
theorem trivialThomPairMap_fst_apply (v : TotalSpace F (Bundle.Trivial B F)) :
    TopPair.Hom.fst (trivialThomPairMap B F) v = v.2 := by
  unfold trivialThomPairMap
  exact TopPair.ofSubsetMap_fst_apply _ _ _

/-- The projection of the Thom pair of the trivial bundle onto its fibre pair restricts to the
identity of `(F, F ∖ {0})` on the fibre over every point. -/
theorem fiberThomPairMap_comp_trivialThomPairMap (b : B) :
    fiberThomPairMap F (Bundle.Trivial B F) b ≫ trivialThomPairMap B F = 𝟙 _ := by
  refine TopPair.hom_ext_of_fst _ (TopCat.ext fun v ↦ ?_)
  exact (congrArg _ (fiberThomPairMap_fst_apply F _ b v)).trans (trivialThomPairMap_fst_apply B F _)

/-- The pull-back of a class `u ∈ Hⁿ(F, F ∖ {0})` along the projection of the Thom pair of the
trivial bundle restricts to `u` on the fibre over every point. -/
theorem singularCohomologyMap_fiberThomPairMap_trivialThomPairMap (b : B) {n : ℕ}
    (u : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R k M n) :
    TopPair.singularCohomologyMap (fiberThomPairMap F (Bundle.Trivial B F) b) n
        (TopPair.singularCohomologyMap (trivialThomPairMap B F) n u) = u := by
  rw [← ConcreteCategory.comp_apply, ← TopPair.singularCohomologyMap_comp,
    fiberThomPairMap_comp_trivialThomPairMap, TopPair.singularCohomologyMap_id,
    ConcreteCategory.id_apply]

end Projection

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Thom classes of the trivial bundle**: over a nonempty base, the pull-back of a class
`u ∈ Hʳ(F, F ∖ {0})`, for `r = finrank ℝ F`, along the projection of the Thom pair onto the fibre
pair is a Thom class of the trivial bundle exactly when `u` generates `Hʳ(F, F ∖ {0})` and `F` is
finite-dimensional. -/
theorem isThomClass_singularCohomologyMap_trivialThomPairMap_iff [Nonempty B]
    (u : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R k M
      (finrank ℝ F)) :
    IsThomClass F (Bundle.Trivial B F)
        (TopPair.singularCohomologyMap (trivialThomPairMap B F) _ u) ↔
      FiniteDimensional ℝ F ∧ Submodule.span k {u} = ⊤ := by
  simp only [isThomClass_iff, singularCohomologyMap_fiberThomPairMap_trivialThomPairMap]
  exact and_congr_right fun _ ↦ ⟨fun h ↦ h (Classical.arbitrary B), fun h _ ↦ h⟩

/-- **The trivial bundle has a Thom class** with coefficients in any commutative ring `K`: the
pull-back of a generator of the local cohomology `Hʳ(F, F ∖ {0}; K, K) ≅ K` along the projection
onto the fibre pair. -/
theorem exists_isThomClass_trivial (K : Type w) [CommRing K] [FiniteDimensional ℝ F] :
    ∃ u : (thomPair F (Bundle.Trivial B F)).singularCohomology (ModuleCat.of K K) K
        (ModuleCat.of K K) (finrank ℝ F), IsThomClass F (Bundle.Trivial B F) u := by
  obtain ⟨u, hu⟩ := exists_span_singularCohomology_complSingleton_eq_top (k := K)
    (OpenPartialHomeomorph.refl F) (Set.mem_univ 0)
  exact ⟨TopPair.singularCohomologyMap (trivialThomPairMap B F) _ u,
    isThomClass_iff.2 ⟨inferInstance, fun b ↦ by
      rw [singularCohomologyMap_fiberThomPairMap_trivialThomPairMap B F b u]
      exact hu⟩⟩

end TauCeti

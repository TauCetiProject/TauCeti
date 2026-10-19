/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExactCochains.Basic
public import TauCeti.Algebra.Homology.HomologicalComplex.Homology

/-!
# Short exact sequences of continuous cochains with their topologies

A short exact sequence of discrete coefficients induces a categorical short exact
sequence of homogeneous continuous-cochain complexes in `TopModuleCat ℤ`. The group may be
any locally compact topological group, and only the action on the middle coefficient
module needs to be continuous. The cochains retain their compact-open and subspace
topologies; these need not be discrete when the group is not compact.

The elementwise input is the cochain-lifting and exactness API in `ExactCochains.Basic`.
Mathlib's forgetful functor from topological modules to modules preserves homology
because it has both adjoints. Its faithfulness reflects exactness, so no new model of
homology or topological lifting argument is required.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  (1.3.2), for the cochain sequence underlying the long exact sequence.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology.DiscreteShortExact

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
  {B : Type u} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
  {C : Type u} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C]
  (S : DiscreteShortExact G A B C)

/-- The sequence of canonical continuous-cochain complexes is short exact in the category
of cochain complexes of topological modules, for a locally compact group acting continuously
on the discrete middle coefficient module. -/
theorem continuousCochainsShortExact_shortExact [LocallyCompactSpace G]
    [ContinuousSMul G B] : S.continuousCochainsShortExact.ShortExact := by
  have : (forget₂ (TopModuleCat.{u} ℤ) (ModuleCat.{u} ℤ)).Additive :=
    Functor.additive_of_preserves_binary_products _
  let F := (forget₂ (TopModuleCat.{u} ℤ) (ModuleCat.{u} ℤ)).mapHomologicalComplex
    (ComplexShape.up ℕ)
  have hS := S.continuousCochainsShortExact_shortExact_moduleCat
  exact
    { exact := (S.continuousCochainsShortExact.exact_map_iff_of_faithful F).mp hS.exact
      mono_f := Functor.mono_of_mono_map F hS.mono_f
      epi_g := Functor.epi_of_epi_map F hS.epi_g }

/-- The canonical continuous-cochain sequence is short exact in `TopModuleCat ℤ` in every
degree, for a locally compact group acting continuously on the discrete middle coefficient
module. The compact-open and subspace topologies on the cochains are retained. -/
theorem continuousCochainsShortExact_degreewise_shortExact [LocallyCompactSpace G]
    [ContinuousSMul G B] (n : ℕ) :
    (S.continuousCochainsShortExact.map
      (HomologicalComplex.eval (TopModuleCat.{u} ℤ) (ComplexShape.up ℕ) n)).ShortExact :=
  S.continuousCochainsShortExact_shortExact.map_of_exact
    (HomologicalComplex.eval (TopModuleCat.{u} ℤ) (ComplexShape.up ℕ) n)

end TauCeti.ContCohomology.DiscreteShortExact

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Homology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import TauCeti.Topology.Algebra.Module.Quotient

/-!
# Homology in `TopModuleCat` as a concrete subquotient

Mathlib proves that `TopModuleCat R` is a `CategoryWithHomology` by exhibiting, for a short
complex `S`, the kernel `TopModuleCat.ker S.g` with its subspace topology and the cokernel
`TopModuleCat.coker` with its quotient topology as left and right homology data. On the cycles
side the resulting identification is available generically, as
`ShortComplex.isoCyclesOfIsLimit (TopModuleCat.isLimitKer S.g) : TopModuleCat.ker S.g ≅ S.cycles`;
on the homology side there is no such generic statement, so this file names it:
`ShortComplex.homologyIsoCoker` identifies `S.homology` with the honest cokernel of `S.toCycles`.
Mathlib's `ShortComplex.homologyIsoCokernelLift` is the analogous statement for the *categorical*
`cokernel`, which says nothing about which topology that object carries; the point of the
isomorphism below is that the topology is the quotient topology on a cokernel.

Two consequences are recorded. The first is that the cycles really are a submodule of the middle
term and the homology really is a quotient of the cycles: `ShortComplex.iCycles_injective`,
`ShortComplex.homologyπ_surjective` and `ShortComplex.homologyπ_eq_zero_iff` describe the cycle
inclusion and the class map elementwise. The surjectivity does not follow from
`ShortComplex.homologyπ` being an epimorphism, since an epimorphism of topological modules need
not be surjective.

The second is that homology in `TopModuleCat R` inherits discreteness: a short
complex whose middle term is discrete has discrete cycles and discrete homology, and likewise
degreewise for a homological complex. This is what makes continuous cohomology of a discrete
representation of a compact group an isomorphism problem between *discrete* topological modules
rather than between the quotient topologies the cochain spaces happen to carry.
-/

public section

open CategoryTheory Limits

namespace TopModuleCat

variable {R : Type*} [Ring R] [TopologicalSpace R]

/-- Exactness of a pair of composable maps of topological modules follows from exactness of the
maps of modules they become after forgetting topologies, up to conjugation by isomorphisms. -/
theorem exact_of_forget₂_map_eq {X₁ X₂ X₃ : TopModuleCat R} {f : X₁ ⟶ X₂}
    {g : X₂ ⟶ X₃} {Y₁ Y₂ Y₃ : ModuleCat R} {f' : Y₁ ⟶ Y₂} {g' : Y₂ ⟶ Y₃}
    {e₁ : Y₁ ≅ (forget₂ (TopModuleCat R) (ModuleCat R)).obj X₁}
    {e₂ : Y₂ ≅ (forget₂ (TopModuleCat R) (ModuleCat R)).obj X₂}
    {e₃ : Y₃ ≅ (forget₂ (TopModuleCat R) (ModuleCat R)).obj X₃}
    (hf : (forget₂ (TopModuleCat R) (ModuleCat R)).map f = e₁.inv ≫ f' ≫ e₂.hom)
    (hg : (forget₂ (TopModuleCat R) (ModuleCat R)).map g = e₂.inv ≫ g' ≫ e₃.hom)
    (h : Function.Exact f' g') : Function.Exact f g :=
  Function.Exact.of_ladder_linearEquiv_of_exact (e₁ := e₁.toLinearEquiv) (e₂ := e₂.toLinearEquiv)
    (e₃ := e₃.toLinearEquiv) (g₁₂ := f.hom.toLinearMap) (g₂₃ := g.hom.toLinearMap)
    (congrArg ModuleCat.Hom.hom ((Iso.inv_comp_eq e₁).1 hf.symm).symm)
    (congrArg ModuleCat.Hom.hom ((Iso.inv_comp_eq e₂).1 hg.symm).symm) h

end TopModuleCat

namespace CategoryTheory.ShortComplex

variable {R : Type*} [Ring R] [TopologicalSpace R] (S : ShortComplex (TopModuleCat R))

/-- The homology of a short complex of topological modules is the cokernel of `S.toCycles`,
carrying the quotient topology. -/
noncomputable def homologyIsoCoker : S.homology ≅ TopModuleCat.coker S.toCycles :=
  IsColimit.coconePointUniqueUpToIso S.homologyIsCokernel (TopModuleCat.isColimitCoker S.toCycles)

/-- `homologyIsoCoker` identifies the projection `S.homologyπ` onto homology with the projection
`TopModuleCat.cokerπ` onto the concrete cokernel. -/
@[reassoc (attr := simp)]
theorem homologyπ_comp_homologyIsoCoker_hom :
    S.homologyπ ≫ (homologyIsoCoker S).hom = TopModuleCat.cokerπ S.toCycles :=
  IsColimit.comp_coconePointUniqueUpToIso_hom S.homologyIsCokernel
    (TopModuleCat.isColimitCoker S.toCycles) WalkingParallelPair.one

/-- The form of `homologyπ_comp_homologyIsoCoker_hom` facing the inverse isomorphism: the
projection onto the concrete cokernel, followed back into homology, is `S.homologyπ`. -/
@[reassoc (attr := simp)]
theorem cokerπ_comp_homologyIsoCoker_inv :
    TopModuleCat.cokerπ S.toCycles ≫ (homologyIsoCoker S).inv = S.homologyπ :=
  IsColimit.comp_coconePointUniqueUpToIso_inv S.homologyIsCokernel
    (TopModuleCat.isColimitCoker S.toCycles) WalkingParallelPair.one

/-- The class map onto the homology of a short complex of topological modules is surjective: the
homology is a quotient of the cycles, not merely their receptacle of an epimorphism. In
`TopModuleCat R` an epimorphism need not be surjective, so this does not follow from
`CategoryTheory.ShortComplex.homologyπ` being an epimorphism. -/
theorem homologyπ_surjective : Function.Surjective S.homologyπ.hom := by
  intro x
  obtain ⟨y, hy⟩ := TopModuleCat.cokerπ_surjective S.toCycles ((homologyIsoCoker S).hom x)
  refine ⟨y, ?_⟩
  have h := ConcreteCategory.congr_hom (cokerπ_comp_homologyIsoCoker_inv S) y
  simp only [ConcreteCategory.comp_apply] at h
  -- The categorical equality still displays bundled morphism coercions; expose its equality of
  -- underlying values so that the chosen preimage can be substituted.
  change S.homologyπ y = x
  rw [← h, hy, Iso.hom_inv_id_apply]

/-- A cycle of a short complex of topological modules has trivial homology class exactly when it
is a boundary. -/
theorem homologyπ_eq_zero_iff {x : S.cycles} :
    S.homologyπ x = 0 ↔ x ∈ Set.range S.toCycles.hom := by
  rw [← (homologyIsoCoker S).toContinuousLinearEquiv.map_eq_zero_iff]
  have h := ConcreteCategory.congr_hom (homologyπ_comp_homologyIsoCoker_hom S) x
  simp only [ConcreteCategory.comp_apply] at h
  -- Normalize the bundled composite to its underlying function before using the concrete
  -- quotient's zero criterion.
  change (homologyIsoCoker S).hom (S.homologyπ x) = 0 ↔ _
  rw [h, TopModuleCat.hom_cokerπ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact LinearMap.mem_range

/-- The inclusion of the cycles of a short complex of topological modules into its middle term is
injective: two cycles with the same underlying element of the middle term are equal, so equalities
between cycles can be checked after applying `S.iCycles`. -/
theorem iCycles_injective : Function.Injective S.iCycles.hom :=
  ConcreteCategory.injective_of_mono_of_preservesPullback
    ((forget₂ (TopModuleCat R) TopCat).map S.iCycles)

/-- The cycles of a short complex of topological modules with discrete middle term are discrete. -/
theorem discreteTopology_cycles [DiscreteTopology S.X₂] : DiscreteTopology S.cycles :=
  -- the point of the kernel fork is `TopModuleCat.ker S.g` by definition, but not syntactically,
  -- so the ascription is what lets the subtype topology be found by instance search
  let e : S.cycles ≅ TopModuleCat.ker S.g :=
    (S.isoCyclesOfIsLimit (TopModuleCat.isLimitKer S.g)).symm
  e.toContinuousLinearEquiv.toHomeomorph.isEmbedding.discreteTopology

/-- The homology of a short complex of topological modules with discrete middle term is
discrete. -/
theorem discreteTopology_homology [DiscreteTopology S.X₂] : DiscreteTopology S.homology :=
  have := discreteTopology_cycles S
  (homologyIsoCoker S).toContinuousLinearEquiv.toHomeomorph.isEmbedding.discreteTopology

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {R : Type*} [Ring R] [TopologicalSpace R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (TopModuleCat R) c) (n : ι)

/-- The class map onto the degreewise homology of a homological complex of topological modules is
surjective. -/
theorem homologyπ_surjective [K.HasHomology n] : Function.Surjective (K.homologyπ n).hom :=
  ShortComplex.homologyπ_surjective (K.sc n)

/-- A cycle of a homological complex of topological modules has trivial homology class exactly
when it is a boundary, `m` being the degree preceding `n`. -/
theorem homologyπ_eq_zero_iff [K.HasHomology n] {m : ι} (hm : c.prev n = m)
    {x : K.cycles n} : K.homologyπ n x = 0 ↔ x ∈ Set.range (K.toCycles m n).hom := by
  subst hm
  exact ShortComplex.homologyπ_eq_zero_iff (K.sc n)

/-- The inclusion of the degree-`n` cycles of a homological complex of topological modules into
its degree-`n` term is injective. -/
theorem iCycles_injective : Function.Injective (K.iCycles n).hom :=
  ShortComplex.iCycles_injective (K.sc n)

/-- A homological complex of topological modules that is discrete in degree `n` has discrete
cycles in degree `n`. -/
theorem discreteTopology_cycles [DiscreteTopology (K.X n)] : DiscreteTopology (K.cycles n) :=
  -- `(K.sc n).X₂` is `K.X n` by the definition of `HomologicalComplex.shortComplexFunctor`, but
  -- that is not a syntactic match, so the instance has to be handed over explicitly.
  have : DiscreteTopology (K.sc n).X₂ := ‹DiscreteTopology (K.X n)›
  ShortComplex.discreteTopology_cycles (K.sc n)

/-- A homological complex of topological modules that is discrete in degree `n` has discrete
homology in degree `n`. -/
theorem discreteTopology_homology [DiscreteTopology (K.X n)] : DiscreteTopology (K.homology n) :=
  have : DiscreteTopology (K.sc n).X₂ := ‹DiscreteTopology (K.X n)›
  ShortComplex.discreteTopology_homology (K.sc n)

end HomologicalComplex

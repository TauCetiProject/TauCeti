/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.FilteredColimits
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Subquotients
public import TauCeti.RepresentationTheory.Subrepresentation
public import TauCeti.Topology.Algebra.GroupAction.Discrete

/-!
# Continuous cohomology as a colimit over finitely generated subrepresentations

Let `G` be a compact group and `X` a smooth discrete representation of `G` over a topological ring
`R`, for instance a discrete `G`-module with continuous action over `R = ℤ`. The subrepresentations
of `X` whose underlying `R`-module is finitely generated form a directed family, and `X` is its
union: the `R`-span of the orbit of a vector is stable, and it is finitely generated because the
orbit of a vector is finite, `G` being compact and the stabilizers open. Each such
subrepresentation is fixed pointwise by an open normal subgroup `U` of `G`, so it is a finitely
generated module over the group ring of the finite group `G ⧸ U`.

Continuous cohomology commutes with this colimit, in every degree:

```text
Hⁿ(G, X) = colim_W Hⁿ(G, W),
```

the colimit taken over the finitely generated subrepresentations `W` of `X`, along the coefficient
maps of the inclusions. Thus every class of `Hⁿ(G, X)` comes from a finitely generated
subrepresentation, and a class there that vanishes in `Hⁿ(G, X)` already vanishes in a larger
finitely generated subrepresentation. The diagram is a filtered colimit on underlying sets, so the
statement is an instance of the commutation of `Hⁿ(G, -)` with filtered colimits of smooth discrete
coefficients (`TauCeti.ContinuousCohomology.isColimitMapCoconeOfIsColimitForget`).

The index category is Mathlib's lattice of subrepresentations `Subrepresentation`, cut down to the
finitely generated ones, with the join-semilattice structure
`Subrepresentation.instSemilatticeSupFG`; each subrepresentation is made a representation through
Tau Ceti's `TopRep.subrepresentation`.

## Main definitions

* `TauCeti.SmoothDiscreteTopRep.fgSubrepresentationDiagram`: the finitely generated
  subrepresentations of `X` as a diagram of smooth discrete representations, indexed by the
  join-semilattice `{σ : Subrepresentation X.obj.ρ.toRepresentation // σ.toSubmodule.FG}`.
* `TauCeti.SmoothDiscreteTopRep.fgSubrepresentationCocone`: the cocone of their inclusions into
  `X`.

## Main results

* `TauCeti.SmoothDiscreteTopRep.exists_fg_subrepresentation_mem`: every vector lies in a finitely
  generated subrepresentation.
* `TauCeti.SmoothDiscreteTopRep.exists_openNormalSubgroup_ρ_apply_eq_self`: a finitely generated
  subrepresentation is fixed pointwise by an open normal subgroup.
* `TauCeti.SmoothDiscreteTopRep.isColimitForgetFGSubrepresentationCocone`: the cocone is a colimit
  on underlying sets.
* `TauCeti.SmoothDiscreteTopRep.isColimitContinuousCohomologyFGSubrepresentationCocone`:
  `Hⁿ(G, X)` is the colimit of the `Hⁿ(G, W)`.
* `TauCeti.SmoothDiscreteTopRep.exists_coeffMap_fgSubrepresentationCocone_eq` and
  `TauCeti.SmoothDiscreteTopRep.exists_coeffMap_fgSubrepresentationDiagram_map_eq_zero`: the two
  elementwise halves of the colimit statement.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.5.1).
* J.-P. Serre, *Galois Cohomology*, Ch. I, §2.2, Proposition 8.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace TauCeti.SmoothDiscreteTopRep

open _root_.ContinuousCohomology TauCeti.ContinuousCohomology

attribute [local instance] TopRep.distribMulAction

variable {R : Type v} [Ring R] [TopologicalSpace R]
  {G : Type u} [Group G] [TopologicalSpace G]

/-! ### The diagram of finitely generated subrepresentations -/

section Diagram

variable (X : SmoothDiscreteTopRep.{v, u, w} R G)

/-- The finitely generated subrepresentations of a smooth discrete representation `X`, as a
diagram of smooth discrete representations: a subrepresentation `σ` goes to the representation on
its underlying submodule, with the subspace topology, and an inclusion `σ ≤ τ` goes to the induced
inclusion. The body is exposed so that the object at `σ` is, definitionally, the representation
`TopRep.subrepresentation` on `σ.toSubmodule`, which is what statements about its cohomology are
written against. -/
@[expose] noncomputable def fgSubrepresentationDiagram :
    {σ : Subrepresentation X.obj.ρ.toRepresentation // σ.toSubmodule.FG} ⥤
      SmoothDiscreteTopRep.{v, u, w} R G where
  obj σ := ⟨TopRep.subrepresentation X.obj σ.1.toSubmodule
      σ.1.contRepresentation_apply_mem_toSubmodule, X.property.subrepresentation _ _⟩
  map {σ τ} f := ObjectProperty.homMk <|
    TopRep.subrepresentationLift X.obj τ.1.toSubmodule
      τ.1.contRepresentation_apply_mem_toSubmodule
      (TopRep.subrepresentationι X.obj σ.1.toSubmodule σ.1.contRepresentation_apply_mem_toSubmodule)
      fun y ↦ (congrArg (· ∈ τ.1.toSubmodule) (TopRep.subrepresentationι_apply _ _ _ y)).mpr
        (leOfHom f y.2)
  map_id σ := ObjectProperty.hom_ext _ <| by
    rw [ObjectProperty.homMk_hom, ObjectProperty.FullSubcategory.id_hom]
    exact (TopRep.subrepresentationLift_unique _ _ _ _ _ _ (Category.id_comp _)).symm
  map_comp f g := ObjectProperty.hom_ext _ <| by
    rw [ObjectProperty.homMk_hom, ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.homMk_hom, ObjectProperty.homMk_hom]
    exact (TopRep.subrepresentationLift_unique _ _ _ _ _ _ (by simp)).symm

/-- The cocone of the inclusions of the finitely generated subrepresentations into `X`. The body
is exposed so that its point is, definitionally, `X` itself. -/
@[expose] noncomputable def fgSubrepresentationCocone : Cocone (fgSubrepresentationDiagram X) where
  pt := X
  ι :=
    { app σ := ObjectProperty.homMk <|
        TopRep.subrepresentationι X.obj σ.1.toSubmodule σ.1.contRepresentation_apply_mem_toSubmodule
      naturality _ _ _ := ObjectProperty.hom_ext _ <|
        (TopRep.subrepresentationLift_comp_ι _ _ _ _ _).trans (Category.comp_id _).symm }

-- Not `@[simp]`: the codomain of the leg is written through `Functor.const`, which
-- `Functor.const_obj_obj` rewrites first, so the left-hand side is not in simp normal form.
/-- The leg of `fgSubrepresentationCocone` at `σ` is the inclusion of the subrepresentation. -/
theorem fgSubrepresentationCocone_ι_app_hom_apply
    (σ : {σ : Subrepresentation X.obj.ρ.toRepresentation // σ.toSubmodule.FG})
    (y : ((fgSubrepresentationDiagram X).obj σ).obj.V) :
    ((fgSubrepresentationCocone X).ι.app σ).hom.hom y = y.1 :=
  TopRep.subrepresentationι_apply _ _ _ y

/-- The transition map of `fgSubrepresentationDiagram` along `σ ≤ τ` is the inclusion. -/
@[simp]
theorem coe_fgSubrepresentationDiagram_map_hom_apply
    {σ τ : {σ : Subrepresentation X.obj.ρ.toRepresentation // σ.toSubmodule.FG}} (f : σ ⟶ τ)
    (y : ((fgSubrepresentationDiagram X).obj σ).obj.V) :
    (((fgSubrepresentationDiagram X).map f).hom.hom y).1 = y.1 :=
  (congrArg Subtype.val (TopRep.subrepresentationLift_apply _ _ _ _ _ y)).trans
    (TopRep.subrepresentationι_apply _ _ _ y)

variable [IsTopologicalGroup G] [CompactSpace G]

/-- **Every vector lies in a finitely generated subrepresentation.** In a smooth discrete
representation of a compact group, the orbit of a vector is finite, and its `R`-span is a
finitely generated subrepresentation containing the vector. -/
theorem exists_fg_subrepresentation_mem (x : X.obj.V) :
    ∃ σ : Subrepresentation X.obj.ρ.toRepresentation, σ.toSubmodule.FG ∧ x ∈ σ := by
  have := X.property.discreteTopology
  have := X.property.continuousSMul
  -- the orbit of `x` is the image of the compact group under a continuous map to a discrete space
  have hfin : (Set.range fun g : G ↦ X.obj.ρ g x).Finite :=
    (isCompact_range (continuous_id.smul continuous_const : Continuous fun g : G ↦ g • x))
      |>.finite_of_discrete
  refine ⟨⟨Submodule.span R (Set.range fun g : G ↦ X.obj.ρ g x), fun g y hy ↦ ?_⟩,
    Submodule.fg_span hfin, Submodule.subset_span ⟨1, by simp⟩⟩
  -- `X.ρ g` maps the span of the orbit onto the span of the translated orbit, inside the span
  have h := Submodule.mem_map_of_mem (f := (X.obj.ρ g : X.obj.V →ₗ[R] X.obj.V)) hy
  rw [Submodule.map_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨h', rfl⟩, rfl⟩
  exact ⟨g * h', by simp⟩

/-- **A finitely generated subrepresentation is fixed by an open normal subgroup.** Over a compact
group, a finitely generated subrepresentation of a smooth discrete representation is fixed
pointwise by some open normal subgroup `U`, so it is a module over the group ring of the finite
quotient `G ⧸ U`. -/
theorem exists_openNormalSubgroup_ρ_apply_eq_self
    {σ : Subrepresentation X.obj.ρ.toRepresentation} (hσ : σ.toSubmodule.FG) :
    ∃ U : OpenNormalSubgroup G, ∀ u ∈ U, ∀ x ∈ σ, X.obj.ρ u x = x := by
  have := X.property.discreteTopology
  have := X.property.continuousSMul
  obtain ⟨s, hs⟩ := hσ
  -- an open normal subgroup fixes the finitely many generators, hence their span
  obtain ⟨U, hU⟩ := (s.finite_toSet).exists_openNormalSubgroup_smul_eq_self (G := G)
  refine ⟨U, fun u hu x hx ↦ ?_⟩
  rw [← Subrepresentation.mem_toSubmodule, ← hs] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact hU u hu y hy
  | zero => exact map_zero _
  | add y z _ _ hy hz => rw [map_add, hy, hz]
  | smul r y _ hy => rw [map_smul, hy]

/-- **A smooth discrete representation is the union of its finitely generated
subrepresentations.** Over a compact group, `fgSubrepresentationCocone` is a colimit cocone on
underlying sets. -/
noncomputable def isColimitForgetFGSubrepresentationCocone :
    IsColimit ((smoothDiscreteι R G ⋙ forget (TopRep R G)).mapCocone
      (fgSubrepresentationCocone X)) :=
  Types.FilteredColimit.isColimitOf' _ _
    (fun x ↦ by
      obtain ⟨σ, hσ, hx⟩ := exists_fg_subrepresentation_mem X x
      exact ⟨⟨σ, hσ⟩, ⟨x, hx⟩, (fgSubrepresentationCocone_ι_app_hom_apply X ⟨σ, hσ⟩ ⟨x, hx⟩).symm⟩)
    fun σ x y h ↦ ⟨σ, 𝟙 σ, congrArg _ <| Subtype.ext <|
      (fgSubrepresentationCocone_ι_app_hom_apply X σ x).symm.trans
        (h.trans (fgSubrepresentationCocone_ι_app_hom_apply X σ y))⟩

end Diagram

/-! ### Continuous cohomology as a colimit -/

section Cohomology

variable [IsTopologicalGroup G] [CompactSpace G] (X : SmoothDiscreteTopRep.{v, u, u} R G)

/-- **Continuous cohomology is the colimit over finitely generated subrepresentations.** For a
compact group `G` and a smooth discrete representation `X`, in every degree `n` the coefficient
maps of the inclusions exhibit `Hⁿ(G, X)` as the colimit of the `Hⁿ(G, W)` over the finitely
generated subrepresentations `W` of `X`. -/
noncomputable def isColimitContinuousCohomologyFGSubrepresentationCocone (n : ℕ) :
    IsColimit ((smoothDiscreteι R G ⋙ continuousCohomologyFunctor R G n).mapCocone
      (fgSubrepresentationCocone X)) :=
  isColimitMapCoconeOfIsColimitForget (isColimitForgetFGSubrepresentationCocone X) n

/-- **Every class comes from a finitely generated subrepresentation.** For a compact group `G`
and a smooth discrete representation `X`, every class of `Hⁿ(G, X)` is the image of a class of
`Hⁿ(G, W)` for some finitely generated subrepresentation `W` of `X`. -/
theorem exists_coeffMap_fgSubrepresentationCocone_eq {n : ℕ}
    (x : continuousCohomology n X.obj) :
    ∃ (σ : {σ : Subrepresentation X.obj.ρ.toRepresentation // σ.toSubmodule.FG})
      (y : continuousCohomology n ((fgSubrepresentationDiagram X).obj σ).obj),
      (coeffMap ((fgSubrepresentationCocone X).ι.app σ).hom n).hom y = x :=
  exists_coeffMap_eq_of_isColimit (isColimitForgetFGSubrepresentationCocone X) x

/-- **Vanishing descends to a larger finitely generated subrepresentation.** For a compact group
`G` and a smooth discrete representation `X`, a class of `Hⁿ(G, W)`, for a finitely generated
subrepresentation `W`, that vanishes in `Hⁿ(G, X)` already vanishes in `Hⁿ(G, W')` for some
finitely generated subrepresentation `W' ⊇ W`. -/
theorem exists_coeffMap_fgSubrepresentationDiagram_map_eq_zero {n : ℕ}
    {σ : {σ : Subrepresentation X.obj.ρ.toRepresentation // σ.toSubmodule.FG}}
    (y : continuousCohomology n ((fgSubrepresentationDiagram X).obj σ).obj)
    (hy : (coeffMap ((fgSubrepresentationCocone X).ι.app σ).hom n).hom y = 0) :
    ∃ (τ : {σ : Subrepresentation X.obj.ρ.toRepresentation // σ.toSubmodule.FG}) (f : σ ⟶ τ),
      (coeffMap ((fgSubrepresentationDiagram X).map f).hom n).hom y = 0 :=
  exists_coeffMap_eq_zero_of_isColimit (isColimitForgetFGSubrepresentationCocone X) y hy

end Cohomology

end TauCeti.SmoothDiscreteTopRep

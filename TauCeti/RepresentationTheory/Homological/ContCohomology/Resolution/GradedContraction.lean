/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.TopRep.GradedCochainComplex
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Cohomology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Graded

/-!
# Contractions of graded representations and classes of homogeneous cocycles

Let `M` be a topological representation of `G` with a `ℤ`-grading `ℳ` by invariant submodules
and an equivariant differential `d` of degree one, and let `TopRep.gradedCochainComplex` be the
cochain complex of `TopRep k G` they assemble. A contraction of `M` onto `X` given on the total
module, that is, an equivariant augmentation `ι : X ⟶ M` into degree zero, a retraction
`π : M → X` vanishing in positive degrees and a homotopy `h` of degree `-1` vanishing in degree
zero with

```text
π ∘ ι = 1,        d ∘ h + h ∘ d = 1 - ι ∘ π,
```

where neither `π` nor `h` need be equivariant, restricts degree by degree to a
`TopRep.ResolutionContraction` of that complex onto `X` (`TopRep.ResolutionContraction.ofGraded`).
Through the comparison with the coinduced resolution, a cocycle `z ∈ ℳ n` of `M` fixed by `G`
then has a class in `Hⁿ(G, X)` (`TopRep.ResolutionContraction.gradedCohomologyClass`).

This is how cocycles written on a total module reach continuous cohomology. Tensor constructions
produce their differentials and contractions on a single carrier, and in Evens' multiplicative
transfer the norm of a class is the class of the tensor power of a representing cocycle, an
invariant cocycle of the tensor-induced total resolution.

The total shifted coinduced resolution `X.gradedResolutionTopRep`, with its evaluation-at-`1`
contraction, is the first instance (`TopRep.gradedResolutionContraction`), and there the class of
a homogeneous cocycle is its class in continuous cohomology
(`TopRep.gradedCohomologyClass_gradedResolutionContraction`).

## Main definitions

* `TopRep.ResolutionContraction.ofGraded`: the contraction of `TopRep.gradedCochainComplex`
  obtained from a contraction of the total module.
* `TopRep.ResolutionContraction.gradedCohomologyClass`: the class in `Hⁿ(G, X)` of an invariant
  cocycle of `M` homogeneous of degree `n`.
* `TopRep.gradedResolutionContraction`: the contraction of the complex of the total coinduced
  resolution by evaluation at `1`.

## Main results

* `TopRep.ResolutionContraction.gradedCohomologyClass_eq_of_sub_eq_d`: homogeneous cocycles
  differing by the differential of a homogeneous invariant element have the same class.
* `TopRep.gradedCohomologyClass_gradedResolutionContraction`: on the total coinduced resolution,
  the class of a homogeneous cocycle is its class in continuous cohomology.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer. Math.
  Soc. 108 (1963), §§2–5.
-/

public section

open CategoryTheory

namespace TopRep

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G]
  {M : TopRep.{max v w} k G} {ℳ : ℤ → Submodule k M.V}
  {hρ : ∀ n g x, x ∈ ℳ n → M.ρ g x ∈ ℳ n} {d : M ⟶ M}
  {hd : TauCeti.LinearMap.IsHomogeneous d.hom.toLinearMap ℳ ℳ 1} {hdd : d ≫ d = 0}

namespace ResolutionContraction

/-- Joint continuity of the conjugates `x • φ (x⁻¹ • v)` of a linear map defined on `M` passes to
its restriction to a term of `TopRep.gradedCochainComplex`. -/
private theorem continuous_conj_restrict {Y : TopRep.{max v w} k G} {φ : M.V →ₗ[k] Y.V}
    (hφ : Continuous fun p : M.V × G ↦ Y.ρ p.2 (φ (M.ρ p.2⁻¹ p.1))) (n : ℕ) :
    Continuous fun p : ((M.gradedCochainComplex ℳ hρ d hd hdd).X n).V × G ↦
      Y.ρ p.2 (φ (M.ρ p.2⁻¹ p.1.1)) :=
  hφ.comp (continuous_subtype_val.prodMap continuous_id)

/-- **The contraction of a graded representation**: a contraction of the total module `M` onto
`X` restricts to a contraction of the complex `TopRep.gradedCochainComplex` onto `X`. The data
are an equivariant augmentation `ι` into degree zero, a retraction `π` vanishing in positive
degrees and a homotopy `h` of degree `-1` vanishing in degree zero, with `π ∘ ι = 1` and
`d ∘ h + h ∘ d = 1 - ι ∘ π`; the conjugates of `π` and `h` must be jointly continuous, which holds
automatically between smooth discrete representations (`TauCeti.IsSmoothDiscrete.continuous_conj`).
-/
noncomputable def ofGraded (X : TopRep.{max v w} k G) (ι : X ⟶ M) (hι : ∀ x, ι.hom x ∈ ℳ 0)
    (π : M.V →ₗ[k] X.V) (h : M.V →ₗ[k] M.V) (hh : TauCeti.LinearMap.IsHomogeneous h ℳ ℳ (-1))
    (hπι : ∀ x, π (ι.hom x) = x) (hπ : ∀ (n : ℕ), ∀ v ∈ ℳ (n + 1 : ℕ), π v = 0)
    (hh₀ : ∀ v ∈ ℳ 0, h v = 0) (hdh : ∀ v, d.hom (h v) + h (d.hom v) = v - ι.hom (π v))
    (hπc : Continuous fun p : M.V × G ↦ X.ρ p.2 (π (M.ρ p.2⁻¹ p.1)))
    (hhc : Continuous fun p : M.V × G ↦ M.ρ p.2 (h (M.ρ p.2⁻¹ p.1))) :
    ResolutionContraction X (M.gradedCochainComplex ℳ hρ d hd hdd) where
  ι := M.gradedCochainComplexLift ℳ hρ d hd hdd 0 ι hι
  proj := π ∘ₗ (M.gradedCochainComplexι ℳ hρ d hd hdd 0).hom.toLinearMap
  hom n := M.gradedCochainComplexRestrict ℳ hρ d hd hdd h hh (by push_cast; ring)
  proj_ι x := by
    rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      ContIntertwiningMap.toContinuousLinearMap_apply, gradedCochainComplexι_apply,
      gradedCochainComplexLift_apply, hπι]
  ι_proj_add_hom_d v := by
    apply gradedCochainComplexι_injective M ℳ hρ d hd hdd 0
    have hv := hdh v.1
    rw [hh₀ v.1 v.2, map_zero, zero_add] at hv
    rw [map_add, gradedCochainComplexι_apply, gradedCochainComplexι_apply,
      gradedCochainComplexι_apply, gradedCochainComplexLift_apply, LinearMap.comp_apply,
      ContinuousLinearMap.coe_coe, ContIntertwiningMap.toContinuousLinearMap_apply,
      gradedCochainComplexι_apply, gradedCochainComplexRestrict_apply,
      gradedCochainComplex_d_apply, hv, add_sub_cancel]
  d_hom_add_hom_d n v := by
    apply gradedCochainComplexι_injective M ℳ hρ d hd hdd (n + 1)
    rw [map_add, gradedCochainComplexι_apply, gradedCochainComplexι_apply,
      gradedCochainComplexι_apply, gradedCochainComplex_d_apply,
      gradedCochainComplexRestrict_apply, gradedCochainComplexRestrict_apply,
      gradedCochainComplex_d_apply, hdh, hπ n v.1 v.2, map_zero, sub_zero]
  continuous_proj :=
    (continuous_conj_restrict (hρ := hρ) (hd := hd) (hdd := hdd) hπc 0).congr fun p ↦ by
      rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        ContIntertwiningMap.toContinuousLinearMap_apply, gradedCochainComplexι_apply,
        gradedCochainComplex_ρ_apply]
  continuous_hom n := (continuous_gradedCochainComplex_X_iff M ℳ hρ d hd hdd n _).2 <|
    (continuous_conj_restrict (hρ := hρ) (hd := hd) (hdd := hdd) hhc (n + 1)).congr fun p ↦ by
      rw [gradedCochainComplex_ρ_apply, gradedCochainComplexRestrict_apply,
        gradedCochainComplex_ρ_apply]

variable [IsTopologicalGroup G] {X : TopRep.{max v w} k G}
  (c : ResolutionContraction X (M.gradedCochainComplex ℳ hρ d hd hdd))

/-- **The class of a homogeneous cocycle**: a vector `z ∈ ℳ n` of `M` fixed by `G` and killed by
`d` is an invariant cocycle of `TopRep.gradedCochainComplex`, and this is its class in `Hⁿ(G, X)`
through the contraction `c`. -/
noncomputable def gradedCohomologyClass {n : ℕ} (z : M.V) (hz : z ∈ ℳ n)
    (hinv : ∀ g, M.ρ g z = z) (hdz : d.hom z = 0) : continuousCohomology n X :=
  c.cohomologyClass (M.gradedCochainComplexInvariant ℳ hρ d hd hdd n z hz hinv)
    (gradedCochainComplex_d_invariant M ℳ hρ d hd hdd hz hinv hdz)

/-- The defining equation of `gradedCohomologyClass`: it is the class `cohomologyClass` of the
invariant cocycle given by `z`. -/
theorem gradedCohomologyClass_def {n : ℕ} (z : M.V) (hz : z ∈ ℳ n) (hinv : ∀ g, M.ρ g z = z)
    (hdz : d.hom z = 0) :
    c.gradedCohomologyClass z hz hinv hdz =
      c.cohomologyClass (M.gradedCochainComplexInvariant ℳ hρ d hd hdd n z hz hinv)
        (gradedCochainComplex_d_invariant M ℳ hρ d hd hdd hz hinv hdz) :=
  (rfl)

/-- **Cohomologous homogeneous cocycles have the same class**: if `z - z'` is the differential of
a vector `y ∈ ℳ n` fixed by `G`, then `z` and `z'` have the same class in `Hⁿ⁺¹(G, X)`. -/
theorem gradedCohomologyClass_eq_of_sub_eq_d {n : ℕ} {z z' : M.V} (hz : z ∈ ℳ (n + 1 : ℕ))
    (hz' : z' ∈ ℳ (n + 1 : ℕ)) (hinv : ∀ g, M.ρ g z = z) (hinv' : ∀ g, M.ρ g z' = z')
    (hdz : d.hom z = 0) (hdz' : d.hom z' = 0) {y : M.V} (hy : y ∈ ℳ n)
    (hyinv : ∀ g, M.ρ g y = y) (hzy : z - z' = d.hom y) :
    c.gradedCohomologyClass z hz hinv hdz = c.gradedCohomologyClass z' hz' hinv' hdz' :=
  c.cohomologyClass_eq_of_sub_eq_d _ _ _ _
    (M.gradedCochainComplexInvariant ℳ hρ d hd hdd n y hy hyinv)
    (gradedCochainComplexι_injective M ℳ hρ d hd hdd (n + 1) (by
      rw [map_sub, gradedCochainComplexι_apply, gradedCochainComplexι_apply,
        gradedCochainComplexι_apply, gradedCochainComplex_d_apply,
        gradedCochainComplexInvariant_val, gradedCochainComplexInvariant_val,
        gradedCochainComplexInvariant_val, hzy]))

end ResolutionContraction

section CoinducedResolution

variable [DiscreteTopology k] [IsTopologicalGroup G] (X : TopRep.{max v w} k G)

/-- The cochain complex `TopRep.gradedCochainComplex` of the total shifted coinduced resolution,
whose degree-`n` term is the copy of `C(G, …, C(G, X))` with `n + 1` layers. -/
noncomputable abbrev gradedResolutionCochainComplex : CochainComplex (TopRep.{max v w} k G) ℕ :=
  X.gradedResolutionTopRep.gradedCochainComplex X.gradedResolutionPiece
    X.gradedResolutionTopRep_ρ_mem X.gradedResolutionTopRepDifferential
    X.isHomogeneous_gradedResolutionTopRepDifferential X.gradedResolutionTopRepDifferential_sq

/-- The inclusion of the degree-`n` term of `gradedResolutionCochainComplex X` into the total
resolution. -/
private noncomputable abbrev gradedResolutionι (n : ℕ) :
    (gradedResolutionCochainComplex X).X n ⟶ X.gradedResolutionTopRep :=
  X.gradedResolutionTopRep.gradedCochainComplexι X.gradedResolutionPiece
    X.gradedResolutionTopRep_ρ_mem X.gradedResolutionTopRepDifferential
    X.isHomogeneous_gradedResolutionTopRepDifferential X.gradedResolutionTopRepDifferential_sq n

/-- The inclusions into the total resolution intertwine the differentials. -/
private theorem d_comp_gradedResolutionι (n : ℕ) :
    (gradedResolutionCochainComplex X).d n (n + 1) ≫ gradedResolutionι X (n + 1) =
      gradedResolutionι X n ≫ X.gradedResolutionTopRepDifferential :=
  gradedCochainComplex_d_comp_ι _ _ _ _ _ _ n

/-- Every element of a term of `gradedResolutionCochainComplex X` is an included resolution
term. -/
private theorem exists_lof_eq {n : ℕ} (v : ((gradedResolutionCochainComplex X).X n).V) :
    ∃ F : (resolutionX X (n + 1)).V,
      (gradedResolutionι X n).hom v =
        DirectSum.lof k ℕ (fun n ↦ (resolutionX X (n + 1)).V) n F := by
  classical
  obtain ⟨F, hF⟩ := (SetLike.ext_iff.1 (X.gradedResolutionPiece_natCast n) v.1).1 v.2
  exact ⟨F, (gradedCochainComplexι_apply _ _ _ _ _ _ n v).trans hF.symm⟩

/-- The degree-`n` component of the total resolution, from the degree-`n` term of
`gradedResolutionCochainComplex X` to the degree-`n` term of the coinduced resolution. -/
private noncomputable def gradedResolutionComponent (n : ℕ) :
    (gradedResolutionCochainComplex X).X n ⟶ (resolution' X).X n :=
  haveI : DiscreteTopology ((gradedResolutionCochainComplex X).X n).V :=
    inferInstanceAs
      (DiscreteTopology {x : X.gradedResolutionTopRep.V // x ∈ X.gradedResolutionPiece n})
  { hom' :=
      { toLinearMap := DirectSum.component k ℕ (fun n ↦ (resolutionX X (n + 1)).V) n ∘ₗ
          (gradedResolutionι X n).hom.toLinearMap
        cont := continuous_of_discreteTopology
        isIntertwining' g := by
          classical
          refine ContinuousLinearMap.ext fun v ↦ ?_
          obtain ⟨F, hF⟩ := exists_lof_eq X v
          -- The map just constructed takes the component of the included vector.
          change DirectSum.component k ℕ (fun n ↦ (resolutionX X (n + 1)).V) n
              ((gradedResolutionι X n).hom (((gradedResolutionCochainComplex X).X n).ρ g v)) =
            ((resolution' X).X n).ρ g
              (DirectSum.component k ℕ (fun n ↦ (resolutionX X (n + 1)).V) n
                ((gradedResolutionι X n).hom v))
          rw [hom_comm_apply, hF, gradedResolutionTopRep_ρ_lof, DirectSum.component.lof_self,
            DirectSum.component.lof_self] } }

/-- The component of the total resolution of an element of a term is the resolution term it
includes. -/
private theorem gradedResolutionComponent_apply {n : ℕ}
    (v : ((gradedResolutionCochainComplex X).X n).V) (F : (resolutionX X (n + 1)).V)
    (hF : (gradedResolutionι X n).hom v =
      DirectSum.lof k ℕ (fun n ↦ (resolutionX X (n + 1)).V) n F) :
    (gradedResolutionComponent X n).hom v = F := by
  classical
  -- The underlying function of `gradedResolutionComponent` is the component of the inclusion.
  change DirectSum.component k ℕ (fun n ↦ (resolutionX X (n + 1)).V) n
    ((gradedResolutionι X n).hom v) = F
  rw [hF, DirectSum.component.lof_self]

/-- The components of the total resolution form a chain map from
`gradedResolutionCochainComplex X` to the coinduced resolution. -/
private noncomputable def gradedResolutionToResolution :
    gradedResolutionCochainComplex X ⟶ resolution' X where
  f := gradedResolutionComponent X
  comm' i j hij := by
    classical
    obtain rfl : i + 1 = j := hij
    refine ConcreteCategory.hom_ext _ _ fun v ↦ ?_
    obtain ⟨F, hF⟩ := exists_lof_eq X v
    rw [comp_apply, comp_apply, gradedResolutionComponent_apply X v F hF]
    refine (gradedResolutionComponent_apply X _ _ ?_).symm
    rw [← comp_apply, d_comp_gradedResolutionι, comp_apply, hF,
      gradedResolutionTopRepDifferential_apply, gradedResolutionDifferential_lof]
    simp only [resolution', CochainComplex.of_d, resolution'd_eq]
    -- `TopRep.Hom.hom` is the reducible abbreviation of `ConcreteCategory.hom`.
    rfl

variable [CompactSpace G] {X} (hX : TauCeti.IsSmoothDiscrete k X)

/-- The **contraction of the total coinduced resolution** onto smooth discrete coefficients, by
the evaluation-at-`1` maps `gradedResolutionProjection` and `gradedResolutionHomotopy`. -/
noncomputable def gradedResolutionContraction :
    ResolutionContraction X (gradedResolutionCochainComplex X) :=
  have := hX.discreteTopology
  have hM := X.isSmoothDiscrete_gradedResolutionTopRep hX
  ResolutionContraction.ofGraded X X.gradedResolutionTopRepAugmentation
    (fun x ↦ by
      rw [gradedResolutionTopRepAugmentation_apply]
      exact X.gradedResolutionAugmentation_mem x)
    X.gradedResolutionProjection X.gradedResolutionHomotopy
    X.isHomogeneous_gradedResolutionHomotopy
    (fun x ↦ by
      rw [gradedResolutionTopRepAugmentation_apply]
      exact X.gradedResolutionProjection_augmentation x)
    (fun n v hv ↦ by
      classical
      rw [X.gradedResolutionPiece_natCast] at hv
      obtain ⟨F, rfl⟩ := hv
      exact X.gradedResolutionProjection_lof_succ n F)
    (fun v hv ↦ by
      classical
      rw [← Nat.cast_zero, X.gradedResolutionPiece_natCast] at hv
      obtain ⟨F, rfl⟩ := hv
      exact X.gradedResolutionHomotopy_lof_zero F)
    (fun v ↦ by
      rw [gradedResolutionTopRepDifferential_apply X v, gradedResolutionTopRepAugmentation_apply]
      exact (congrArg (· + _) (gradedResolutionTopRepDifferential_apply X _)).trans
        (X.gradedResolutionDifferential_gradedResolutionHomotopy_add v))
    (hM.continuous_conj hX _) (hM.continuous_conj hM _)

/-- The chain map `gradedResolutionToResolution X` lies over the identity of `X`. -/
private theorem ι_comp_gradedResolutionToResolution_f_zero :
    (gradedResolutionContraction hX).ι ≫ (gradedResolutionToResolution X).f 0 =
      (resolutionContraction X).ι := by
  classical
  have := hX.discreteTopology
  refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
  rw [comp_apply, resolutionContraction_ι]
  refine gradedResolutionComponent_apply X _ _ ?_
  exact (gradedCochainComplexι_apply _ _ _ _ _ _ 0 _).trans
    ((gradedCochainComplexLift_apply _ _ _ _ _ _ 0 _ _ x).trans
      ((gradedResolutionTopRepAugmentation_apply X x).trans
        (gradedResolutionAugmentation_apply X x)))

/-- **On the total coinduced resolution, the class of a homogeneous cocycle is its class in
continuous cohomology**: a homogeneous cocycle `z` of degree `n`, included into the total
resolution, has as class through `gradedResolutionContraction` the class `X.cochainClass n z`. -/
theorem gradedCohomologyClass_gradedResolutionContraction {n : ℕ}
    (z : ((resolution' X).X n).ρ.invariants)
    (hz : ((resolution' X).d n (n + 1)).hom (z : ((resolution' X).X n).V) = 0) :
    (gradedResolutionContraction hX).gradedCohomologyClass
        (DirectSum.lof k ℕ (fun n ↦ (resolutionX X (n + 1)).V) n z)
        (X.lof_mem_gradedResolutionPiece n z)
        (fun g ↦ by
          rw [gradedResolutionTopRep_ρ_lof, (ContRepresentation.mem_invariants _).1 z.2 g])
        (by
          simp only [resolution', CochainComplex.of_d, resolution'd_eq] at hz
          rw [gradedResolutionTopRepDifferential_apply, gradedResolutionDifferential_lof, hz]
          exact map_zero _) =
      X.cochainClass n z (Subtype.ext hz) := by
  refine ((gradedResolutionContraction hX).gradedCohomologyClass_def _ _ _ _).trans ?_
  rw [← (gradedResolutionContraction hX).cohomologyClass_map (resolutionContraction X)
      (gradedResolutionToResolution X) (ι_comp_gradedResolutionToResolution_f_zero hX),
    cohomologyClass_resolutionContraction]
  congr 1
  apply Subtype.ext
  rw [ContIntertwiningMap.mapInvariants_apply]
  exact gradedResolutionComponent_apply X _ _
    ((gradedCochainComplexι_apply _ _ _ _ _ _ n _).trans
      (gradedCochainComplexInvariant_val _ _ _ _ _ _ n _ _ _))

end CoinducedResolution

end TopRep

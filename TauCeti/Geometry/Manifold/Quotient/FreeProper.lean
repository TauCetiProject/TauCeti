/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Geometry.Manifold.GroupAction.Quotient
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.Submersion.Descent

import TauCeti.Geometry.Lie.FundamentalVectorField.OrbitMap
import TauCeti.Geometry.Lie.Interior
import TauCeti.Geometry.Lie.Subgroup.Stabilizer
import TauCeti.Geometry.Manifold.GroupAction.Orbit
import TauCeti.Geometry.Manifold.GroupAction.TransverseSlice
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.Topology.Algebra.ProperAction.TransverseSlice

/-!
# Free proper quotient manifolds: slice tubes, descent, uniqueness, and discrete actions

The smooth manifold structure on the orbit space `MulAction.orbitRel.Quotient G M` of a free proper
smooth action of a finite-dimensional real Lie group `G` (modelled on `(EG, IG)`) on a
finite-dimensional boundaryless smooth manifold `M` (modelled on `(E, I)`) is constructed in
`TauCeti.Geometry.Manifold.GroupAction.Quotient` as `ProperSMul.orbitRelQuotientChartedSpace`,
modelled on `ProperSMul.QuotientModelSpace EG E` (`ℝ^(dim M - dim G)`), together with the smooth
manifold instance `ProperSMul.instIsManifoldOrbitRelQuotient`, the smooth submersion property
`ProperSMul.isSubmersion_quotientMk`, and the vertical kernel identification
`ProperSMul.ker_mfderiv_quotientMk`.

This file complements that core construction with:

1. **Pointwise transverse slice tubes at free points**
   (`TauCeti.exists_injOn_isLocalDiffeomorphOn_smul_slice`): without assuming the entire action is
   free, around any point `x : M` with trivial stabilizer of a proper smooth action there exist a
   smooth transverse slice `σ : ProperSMul.QuotientModelSpace EG E → M` with `σ 0 = x` and an open
   neighbourhood `U` of `0` on which `(g, s) ↦ g • σ s` is both injective on `G × U` and a smooth
   local diffeomorphism at every point of `G × U`.
2. **Explicit submersion complement and existential packaging**
   (`TauCeti.surjective_mfderiv_quotientMk_freeProperQuotient`,
   `TauCeti.isSubmersionOfComplement_quotientMk_freeProperQuotient`,
   `TauCeti.exists_freeProperQuotient_isSubmersion`): strengthens
   `ProperSMul.isSubmersion_quotientMk` to `Manifold.IsSubmersionOfComplement EG` with explicit
   complement `EG`, exposes the surjectivity of `mfderiv` of the orbit projection, and packages the
   quotient manifold theorem into its existential form.
3. **Descent, functoriality, and bundled maps**: `C^m` maps (`m ≤ ∞`), immersions, and submersions
   out of `M ⧸ G` are characterized by composition with the orbit projection; equivariant `C^m`
   maps and smooth submersions descend to orbit spaces; the orbit projection and invariant smooth
   descents are bundled as `TauCeti.smoothFreeProperQuotientMk` and
   `ContMDiffMap.freeProperQuotientLift` with characterizing `apply`, `comp`, and uniqueness
   lemmas matching the discrete-action API in `TauCeti.Geometry.Manifold.Quotient.Descent`.
4. **Uniqueness and discrete specialization**: any surjective smooth submersion out of `M` whose
   fibres are the `G`-orbits is canonically diffeomorphic to `M ⧸ G`
   (`TauCeti.freeProperQuotientDiffeomorph`), and the smooth structure on `M ⧸ G` making the orbit
   projection a smooth submersion has a unique maximal atlas
   (`TauCeti.maximalAtlas_freeProperQuotient_eq`). When `G` carries the discrete topology, the
   orbit projection is a smooth local diffeomorphism
   (`TauCeti.isLocalDiffeomorph_quotientMk_freeProperQuotient_of_discreteTopology`).

No explicit Hausdorff or second-countability hypotheses are needed: `G`, `M`, and `M ⧸ G` are
automatically Hausdorff (`ModelWithCorners.t2Space_of_lieGroup`,
`t2Space_of_properSMul_of_t1Group`, `t2Space_quotient_mulAction_of_properSMul`). An empty manifold
`M` is allowed.

## Main declarations

* `TauCeti.exists_injOn_isLocalDiffeomorphOn_smul_slice`: existence of an injective local
  diffeomorphism slice tube `G × U → M` around any free point of a proper smooth action.
* `TauCeti.surjective_mfderiv_quotientMk_freeProperQuotient`: surjectivity of the differential of
  the orbit projection.
* `TauCeti.isSubmersionOfComplement_quotientMk_freeProperQuotient`: the orbit projection is a smooth
  submersion with explicit complement `EG`.
* `TauCeti.exists_freeProperQuotient_isSubmersion`: existential form of the quotient manifold
  theorem packaging `ProperSMul.orbitRelQuotientChartedSpace`, manifold structure, submersion
  property, and vertical kernel.
* `TauCeti.contMDiffAt_comp_quotientMk_freeProperQuotient_iff`,
  `TauCeti.contMDiff_comp_quotientMk_freeProperQuotient_iff`,
  `TauCeti.contMDiffAt_orbitRelQuotientLift_freeProperQuotient_iff`,
  `TauCeti.contMDiff_orbitRelQuotientLift_freeProperQuotient_iff`,
  `TauCeti.isImmersion_orbitRelQuotientLift_freeProperQuotient_iff`,
  `TauCeti.isSubmersion_orbitRelQuotientLift_freeProperQuotient_iff`,
  `TauCeti.contMDiff_orbitRelQuotientMap_freeProperQuotient`,
  `TauCeti.isSubmersion_orbitRelQuotientMap_freeProperQuotient`,
  `TauCeti.smoothFreeProperQuotientMk`, and `ContMDiffMap.freeProperQuotientLift`: smooth descent
  and functoriality on orbit spaces.
* `TauCeti.freeProperQuotientDiffeomorph` and `TauCeti.maximalAtlas_freeProperQuotient_eq`:
  uniqueness of the quotient manifold up to canonical diffeomorphism and equality of maximal
  atlases.
* `TauCeti.isLocalDiffeomorph_quotientMk_freeProperQuotient_of_discreteTopology`: for a discrete
  Lie group `G`, the orbit projection is a smooth local diffeomorphism.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorems 4.29–4.31 and Theorem 21.10 (the quotient manifold theorem).
* Eckhard Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003,
  Theorem 1.21.
-/

public section

noncomputable section

open Function Set Filter Manifold Topology
open scoped ContDiff Manifold

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-! ### Transverse slice tubes at free points -/

section PointwiseSlice

variable {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace HG G] [LieGroup IG ∞ G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M]

/-- **Transverse slice tubes at free points of proper smooth actions.** Let a finite-dimensional
real Lie group `G` act smoothly and properly on a finite-dimensional boundaryless smooth manifold
`M`, and let `x : M` have trivial stabilizer (the action need not be globally free). Then there
exist a slice `σ : ProperSMul.QuotientModelSpace EG E → M` sending `0` to `x` and an open
neighbourhood `U` of `0` on which `σ` is smooth and such that the slice map `(g, s) ↦ g • σ s` is
injective on `G × U` and a smooth local diffeomorphism at every point of `G × U`. -/
theorem exists_injOn_isLocalDiffeomorphOn_smul_slice {x : M}
    (hx : MulAction.stabilizer G x = ⊥) :
    ∃ (σ : ProperSMul.QuotientModelSpace EG E → M)
      (U : Set (ProperSMul.QuotientModelSpace EG E)),
      σ 0 = x ∧ IsOpen U ∧ 0 ∈ U ∧
      ContMDiffOn 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E) I ∞ σ U ∧
      InjOn (fun p : G × ProperSMul.QuotientModelSpace EG E ↦ p.1 • σ p.2) (univ ×ˢ U) ∧
      IsLocalDiffeomorphOn
        (IG.prod 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E)) I ∞
        (fun p : G × ProperSMul.QuotientModelSpace EG E ↦ p.1 • σ p.2) (univ ×ˢ U) := by
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  have hiso := Lie.isotropy_eq_bot_of_stabilizer_eq_bot (I := IG) (I' := I) hx
  have hdimO := finrank_orbitTangent_fundamental_of_stabilizer_eq_bot (I := IG) (I' := I) hx
  -- Choose a complement `W` of the orbit tangent space in `E` and identify it with
  -- `ProperSMul.QuotientModelSpace EG E`.
  let O : Submodule ℝ E := (InfinitesimalAction.fundamental IG G I M).orbitTangent x
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl O
  have hWW := Submodule.finrank_add_eq_of_isCompl hW
  let S := ProperSMul.QuotientModelSpace EG E
  let K := 𝓘(ℝ, S)
  let e : S ≃L[ℝ] W := ContinuousLinearEquiv.ofFinrankEq (by
    have hdimO' : Module.finrank ℝ O = Module.finrank ℝ EG := hdimO
    dsimp only [S, ProperSMul.QuotientModelSpace]
    rw [finrank_euclideanSpace_fin]
    omega)
  let σ : S → M := fun s ↦ (extChartAt I x).symm (extChartAt I x x + (e s : E))
  have hσ0 : σ 0 = x := by simp [σ]
  have hlocW := isLocalDiffeomorphAt_smul_extChartAt_symm (I := IG) (I' := I) hiso hW
  rw [← e.map_zero] at hlocW
  have hloc0 : IsLocalDiffeomorphAt (IG.prod K) I ∞ (fun p : G × S ↦ p.1 • σ p.2) (1, 0) :=
    IsLocalDiffeomorphAt.comp (hg := hlocW) (hf :=
      ((Diffeomorph.refl IG G ∞).isLocalDiffeomorph 1).prodMap
        (e.toDiffeomorph.isLocalDiffeomorph 0))
  -- Equivariance extends the local diffeomorphism along `G`, and properness shrinks the slice to
  -- make the tube map globally injective on `G × U`.
  have hloc_ev := hloc0.eventually_forall_smul_slice
  obtain ⟨N, hN, hinjN⟩ := hloc0.exists_mem_nhds_injOn
  have hσ_cont : ContinuousAt σ 0 := by
    have h1 : ContinuousAt (fun s : S ↦ (1 : G) • σ s) 0 :=
      hloc0.contMDiffAt.continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt
    simpa only [one_smul] using h1
  obtain ⟨U₀, hU₀, hinjU₀⟩ :=
    ProperSMul.exists_mem_nhds_injOn_smul_slice hσ_cont (hσ0.symm ▸ hx) hN hinjN
  obtain ⟨U, hU_sub, hU_open, h0U⟩ := mem_nhds_iff.1 (inter_mem hU₀ hloc_ev)
  have hlocU : IsLocalDiffeomorphOn (IG.prod K) I ∞ (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U) :=
    fun p ↦ (hU_sub p.2.2).2 p.1.1
  have hσU : ContMDiffOn K I ∞ σ U := by
    have h1 : ContMDiffOn K I ∞ (fun s : S ↦ (1 : G) • σ s) U :=
      hlocU.contMDiffOn.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
        fun s hs ↦ ⟨mem_univ _, hs⟩
    simpa only [one_smul] using h1
  exact ⟨σ, U, hσ0, hU_open, h0U, hσU,
    hinjU₀.mono (prod_mono_right fun _ hu ↦ (hU_sub hu).1), hlocU⟩

end PointwiseSlice

/-! ### Explicit submersion complement and existential packaging -/

section QuotientManifold

variable {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace HG G] [LieGroup IG ∞ G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M] [IsCancelSMul G M]

variable (IG G I) in
/-- At every `x : M`, the orbit tangent space has dimension `dim EG`, hence `dim EG ≤ dim E`. -/
private theorem finrank_orbitTangent_and_le (x : M) :
    Module.finrank ℝ ((InfinitesimalAction.fundamental IG G I M).orbitTangent x) =
      Module.finrank ℝ EG ∧
    Module.finrank ℝ EG ≤ Module.finrank ℝ E := by
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  have h := finrank_orbitTangent_fundamental_of_stabilizer_eq_bot (I := IG) (I' := I)
    (IsCancelSMul.stabilizer_eq_bot (G := G) x)
  exact ⟨h, h ▸ Submodule.finrank_le _⟩

/-- At every point `x : M`, the differential of the orbit projection `M → M ⧸ G` is surjective
for `ProperSMul.orbitRelQuotientChartedSpace`. -/
theorem surjective_mfderiv_quotientMk_freeProperQuotient (x : M) :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
    Surjective (mfderiv I 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E)
      (Quotient.mk (MulAction.orbitRel G M)) x) :=
  letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
  (ProperSMul.isSubmersion_quotientMk (I := IG) (G := G)).surjective_mfderiv (by simp) x

/-- **The orbit projection of a free proper smooth Lie group action is a smooth submersion with
complement `EG`.** This strengthens `ProperSMul.isSubmersion_quotientMk` by fixing the fibre
complement to the Lie-group model space `EG`. -/
theorem isSubmersionOfComplement_quotientMk_freeProperQuotient :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
    Manifold.IsSubmersionOfComplement EG I
      𝓘(ℝ, ProperSMul.QuotientModelSpace EG E) ∞
      (Quotient.mk (MulAction.orbitRel G M)) := by
  let _ := ProperSMul.orbitRelQuotientChartedSpace IG G I M
  have := ProperSMul.instIsManifoldOrbitRelQuotient (I := IG) (G := G) (I' := I) (M := M)
  refine Manifold.isSubmersionOfComplement_iff.2 fun x ↦ ?_
  have hsub :=
    (ProperSMul.contMDiff_quotientMk (I := IG) (G := G) (I' := I) (M := M)).contMDiffOn
      |>.isSubmersionAtOfComplement_of_surjective_mfderiv isOpen_univ (mem_univ x) (by simp)
        (surjective_mfderiv_quotientMk_freeProperQuotient (IG := IG) (G := G) (I := I) (M := M) x)
  obtain ⟨_, hle⟩ := finrank_orbitTangent_and_le IG G I x
  let L : (Fin (Module.finrank ℝ E -
      Module.finrank ℝ (ProperSMul.QuotientModelSpace EG E)) → ℝ) ≃L[ℝ] EG :=
    ContinuousLinearEquiv.ofFinrankEq (by
      rw [Module.finrank_fin_fun]
      dsimp only [ProperSMul.QuotientModelSpace]
      rw [finrank_euclideanSpace_fin]
      omega)
  exact (Manifold.IsSubmersionAtOfComplement.congr_F L).mp hsub

variable (IG G I M) in
/-- **The quotient manifold theorem for free proper Lie group actions.** Existential packaging of
`ProperSMul.orbitRelQuotientChartedSpace`, `ProperSMul.instIsManifoldOrbitRelQuotient`,
`ProperSMul.isSubmersion_quotientMk`, and `ProperSMul.ker_mfderiv_quotientMk`: if a
finite-dimensional real Lie group `G` acts smoothly, freely and properly on a finite-dimensional
boundaryless smooth manifold `M`, then the orbit space `MulAction.orbitRel.Quotient G M` (with its
quotient topology) admits a smooth manifold structure of dimension `dim M - dim G` for which the
orbit projection is a smooth submersion whose differential at each `x : M` has kernel equal to the
orbit tangent space `𝔤 · x`. -/
theorem exists_freeProperQuotient_isSubmersion :
    ∃ cs : ChartedSpace (ProperSMul.QuotientModelSpace EG E)
        (MulAction.orbitRel.Quotient G M),
      letI := cs
      IsManifold 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E) ∞
        (MulAction.orbitRel.Quotient G M) ∧
      Manifold.IsSubmersion I
        𝓘(ℝ, ProperSMul.QuotientModelSpace EG E) ∞
        (Quotient.mk (MulAction.orbitRel G M)) ∧
      ∀ x : M,
        (mfderiv I 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E)
          (Quotient.mk (MulAction.orbitRel G M)) x).ker =
          (InfinitesimalAction.fundamental IG G I M).orbitTangent x :=
  ⟨ProperSMul.orbitRelQuotientChartedSpace IG G I M,
    ProperSMul.instIsManifoldOrbitRelQuotient (I := IG) (G := G) (I' := I) (M := M),
    ProperSMul.isSubmersion_quotientMk (I := IG) (G := G),
    ProperSMul.ker_mfderiv_quotientMk (I := IG) (G := G)⟩

end QuotientManifold

/-! ### Smooth descent, immersions, and equivariant maps -/

section Descent

variable {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace HG G] [LieGroup IG ∞ G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M] [IsCancelSMul G M]
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
  {m : ℕ∞ω}

/-- For `m ≤ ∞`, a map out of the free proper quotient `M ⧸ G` is `C^m` at the orbit of `x`
exactly when its composite with the orbit projection is `C^m` at `x`. -/
theorem contMDiffAt_comp_quotientMk_freeProperQuotient_iff (hm : m ≤ ∞)
    {g : MulAction.orbitRel.Quotient G M → N} {x : M} :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
    ContMDiffAt I J m (g ∘ Quotient.mk (MulAction.orbitRel G M)) x ↔
      ContMDiffAt 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E) J m g
        (Quotient.mk (MulAction.orbitRel G M) x) :=
  letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
  ((ProperSMul.isSubmersion_quotientMk (I := IG) (G := G)).isSubmersionAt
    x).contMDiffAt_comp_iff hm

/-- For `m ≤ ∞`, a map out of the free proper quotient `M ⧸ G` is `C^m` globally exactly when its
composite with the orbit projection is `C^m`. -/
theorem contMDiff_comp_quotientMk_freeProperQuotient_iff (hm : m ≤ ∞)
    {g : MulAction.orbitRel.Quotient G M → N} :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
    ContMDiff I J m (g ∘ Quotient.mk (MulAction.orbitRel G M)) ↔
      ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E) J m g :=
  letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
  (ProperSMul.isSubmersion_quotientMk (I := IG) (G := G)).contMDiff_comp_iff
    Quotient.mk_surjective hm

/-- For `m ≤ ∞`, the descent of a `G`-invariant map `f : M → N` to the free proper quotient `M ⧸ G`
is `C^m` at the orbit of `x` exactly when `f` is `C^m` at `x`. -/
theorem contMDiffAt_orbitRelQuotientLift_freeProperQuotient_iff (hm : m ≤ ∞)
    {f : M → N} {hf : ∀ (g : G) (x : M), f (g • x) = f x} {x : M} :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
    ContMDiffAt 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E) J m
      (MulAction.orbitRelQuotientLift f hf) (Quotient.mk (MulAction.orbitRel G M) x) ↔
      ContMDiffAt I J m f x := by
  let _ := ProperSMul.orbitRelQuotientChartedSpace IG G I M
  rw [← contMDiffAt_comp_quotientMk_freeProperQuotient_iff (IG := IG) hm,
    MulAction.orbitRelQuotientLift_comp_mk]

/-- For `m ≤ ∞`, the descent of a `G`-invariant map `f : M → N` to the free proper quotient `M ⧸ G`
is `C^m` globally exactly when `f` is `C^m`. -/
theorem contMDiff_orbitRelQuotientLift_freeProperQuotient_iff (hm : m ≤ ∞)
    {f : M → N} {hf : ∀ (g : G) (x : M), f (g • x) = f x} :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
    ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E) J m
      (MulAction.orbitRelQuotientLift f hf) ↔ ContMDiff I J m f := by
  let _ := ProperSMul.orbitRelQuotientChartedSpace IG G I M
  rw [← contMDiff_comp_quotientMk_freeProperQuotient_iff (IG := IG) hm,
    MulAction.orbitRelQuotientLift_comp_mk]

/-- **Immersion criterion for maps descended to a free proper quotient.** Into a finite-dimensional
boundaryless smooth manifold `N`, the descent of a `G`-invariant map `f : M → N` is a smooth
immersion exactly when `f` is smooth and at every `x : M` its differential kills precisely the
orbit tangent space `𝔤 · x`. -/
theorem isImmersion_orbitRelQuotientLift_freeProperQuotient_iff
    [FiniteDimensional ℝ EN] [J.Boundaryless] [IsManifold J ∞ N]
    {f : M → N} {hf : ∀ (g : G) (x : M), f (g • x) = f x} :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
    Manifold.IsImmersion 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E) J ∞
      (MulAction.orbitRelQuotientLift f hf) ↔
      ContMDiff I J ∞ f ∧
        ∀ x : M, (mfderiv I J f x).ker =
          (InfinitesimalAction.fundamental IG G I M).orbitTangent x := by
  let _ := ProperSMul.orbitRelQuotientChartedSpace IG G I M
  have := ProperSMul.instIsManifoldOrbitRelQuotient (I := IG) (G := G) (I' := I) (M := M)
  rw [(ProperSMul.isSubmersion_quotientMk (I := IG) (G := G)).isImmersion_iff_ker_mfderiv_comp
    Quotient.mk_surjective (by simp), MulAction.orbitRelQuotientLift_comp_mk]
  exact and_congr_right' (forall_congr' fun x ↦ by
    rw [ProperSMul.ker_mfderiv_quotientMk (I := IG) (G := G) x])

/-- **Submersion criterion for maps descended to a free proper quotient.** Into a finite-dimensional
smooth manifold `N`, the descent of a `G`-invariant map `f : M → N` is a smooth submersion exactly
when `f` is smooth and has surjective differential at every `x : M`. -/
theorem isSubmersion_orbitRelQuotientLift_freeProperQuotient_iff
    [FiniteDimensional ℝ EN] [IsManifold J ∞ N]
    {f : M → N} {hf : ∀ (g : G) (x : M), f (g • x) = f x} :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
    Manifold.IsSubmersion 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E) J ∞
      (MulAction.orbitRelQuotientLift f hf) ↔
      ContMDiff I J ∞ f ∧ ∀ x : M, Surjective (mfderiv I J f x) := by
  let _ := ProperSMul.orbitRelQuotientChartedSpace IG G I M
  have := ProperSMul.instIsManifoldOrbitRelQuotient (I := IG) (G := G) (I' := I) (M := M)
  rw [(ProperSMul.isSubmersion_quotientMk
      (I := IG) (G := G)).isSubmersion_iff_surjective_mfderiv_comp Quotient.mk_surjective (by simp),
    MulAction.orbitRelQuotientLift_comp_mk]

end Descent

section Equivariant

variable {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace HG G] [LieGroup IG ∞ G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M] [IsCancelSMul G M]

/-- **Functoriality of free proper orbit spaces.** For `m ≤ ∞`, an equivariant `C^m` map between
two manifolds carrying free proper smooth Lie group actions induces a `C^m` map between their orbit
spaces. -/
theorem contMDiff_orbitRelQuotientMap_freeProperQuotient
    {EG' : Type*} [NormedAddCommGroup EG'] [NormedSpace ℝ EG'] [FiniteDimensional ℝ EG']
    {HG' : Type*} [TopologicalSpace HG'] {IG' : ModelWithCorners ℝ EG' HG'}
    {G' : Type*} [Group G'] [TopologicalSpace G'] [ChartedSpace HG' G'] [LieGroup IG' ∞ G']
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    [MulAction G' M'] [ContMDiffSMul IG' I' ∞ G' M'] [ProperSMul G' M'] [IsCancelSMul G' M']
    {m : ℕ∞ω} {σ : G → G'} (hm : m ≤ ∞) {φ : M →ₑ[σ] M'} (hφ : ContMDiff I I' m φ) :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
    letI := ProperSMul.orbitRelQuotientChartedSpace IG' G' I' M'
    ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E)
      𝓘(ℝ, ProperSMul.QuotientModelSpace EG' E') m
      (MulActionHom.orbitRelQuotientMap φ) := by
  let _ := ProperSMul.orbitRelQuotientChartedSpace IG G I M
  let _ := ProperSMul.orbitRelQuotientChartedSpace IG' G' I' M'
  rw [← contMDiff_comp_quotientMk_freeProperQuotient_iff (IG := IG) hm,
    MulActionHom.orbitRelQuotientMap_comp_mk]
  exact ((ProperSMul.contMDiff_quotientMk (I := IG') (G := G')).of_le hm).comp hφ

/-- **Equivariant submersions descend to submersions of free proper orbit spaces.** An equivariant
smooth submersion between two manifolds carrying free proper smooth Lie group actions induces a
smooth submersion between their orbit spaces. -/
theorem isSubmersion_orbitRelQuotientMap_freeProperQuotient
    {EG' : Type*} [NormedAddCommGroup EG'] [NormedSpace ℝ EG'] [FiniteDimensional ℝ EG']
    {HG' : Type*} [TopologicalSpace HG'] {IG' : ModelWithCorners ℝ EG' HG'}
    {G' : Type*} [Group G'] [TopologicalSpace G'] [ChartedSpace HG' G'] [LieGroup IG' ∞ G']
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    [MulAction G' M'] [ContMDiffSMul IG' I' ∞ G' M'] [ProperSMul G' M'] [IsCancelSMul G' M']
    {σ : G → G'} {φ : M →ₑ[σ] M'} (hφ : Manifold.IsSubmersion I I' ∞ φ) :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
    letI := ProperSMul.orbitRelQuotientChartedSpace IG' G' I' M'
    Manifold.IsSubmersion 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E)
      𝓘(ℝ, ProperSMul.QuotientModelSpace EG' E') ∞
      (MulActionHom.orbitRelQuotientMap φ) := by
  let _ := ProperSMul.orbitRelQuotientChartedSpace IG G I M
  let _ := ProperSMul.orbitRelQuotientChartedSpace IG' G' I' M'
  have := ProperSMul.instIsManifoldOrbitRelQuotient (I := IG) (G := G) (I' := I) (M := M)
  have := ProperSMul.instIsManifoldOrbitRelQuotient (I := IG') (G := G') (I' := I') (M := M')
  rw [(ProperSMul.isSubmersion_quotientMk
      (I := IG) (G := G)).isSubmersion_iff_surjective_mfderiv_comp Quotient.mk_surjective (by simp),
    MulActionHom.orbitRelQuotientMap_comp_mk]
  refine ⟨(ProperSMul.contMDiff_quotientMk (I := IG') (G := G')).comp hφ.contMDiff, fun x ↦ ?_⟩
  rw [mfderiv_comp x
    ((ProperSMul.contMDiff_quotientMk (I := IG') (G := G') (φ x)).mdifferentiableAt (by simp))
    (hφ.contMDiff.mdifferentiableAt (by simp)), ContinuousLinearMap.coe_comp]
  exact (surjective_mfderiv_quotientMk_freeProperQuotient (IG := IG') (G := G') (I := I')
    (M := M') (φ x)).comp (hφ.surjective_mfderiv (by simp) x)

variable (IG G I M) in
/-- The orbit projection `M → M ⧸ G` of a free proper smooth Lie group action, as a bundled smooth
map for `ProperSMul.orbitRelQuotientChartedSpace`. -/
def smoothFreeProperQuotientMk :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
    C^∞⟮I, M; 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E), MulAction.orbitRel.Quotient G M⟯ :=
  letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
  ⟨Quotient.mk _, ProperSMul.contMDiff_quotientMk (I := IG) (G := G)⟩

/-- The underlying function of `TauCeti.smoothFreeProperQuotientMk` is the orbit projection. -/
theorem coe_smoothFreeProperQuotientMk :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
    ⇑(smoothFreeProperQuotientMk IG G I M) = Quotient.mk (MulAction.orbitRel G M) :=
  (rfl)

/-- `TauCeti.smoothFreeProperQuotientMk` sends each `x : M` to its `G`-orbit. -/
@[simp]
theorem smoothFreeProperQuotientMk_apply (x : M) :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
    smoothFreeProperQuotientMk IG G I M x = Quotient.mk (MulAction.orbitRel G M) x :=
  (rfl)

end Equivariant

/-! ### Uniqueness and discrete specialization -/

section Uniqueness

variable {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace HG G] [LieGroup IG ∞ G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M] [IsCancelSMul G M]

/-- **Uniqueness of the free proper quotient up to diffeomorphism.** Any surjective smooth
submersion `q : M → N` whose fibres are the `G`-orbits induces a canonical smooth diffeomorphism
`M ⧸ G ≃ₘ N` intertwining the orbit projection with `q`. -/
def freeProperQuotientDiffeomorph
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    {HN : Type*} [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN}
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    {q : M → N} (hq : Manifold.IsSubmersion I J ∞ q) (hq_surj : Surjective q)
    (hfib : ∀ x y : M, q x = q y ↔ MulAction.orbitRel G M x y) :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
    MulAction.orbitRel.Quotient G M ≃ₘ⟮𝓘(ℝ, ProperSMul.QuotientModelSpace EG E), J⟯ N :=
  letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
  (ProperSMul.isSubmersion_quotientMk (I := IG) (G := G)).diffeomorphOfSurjective
    Quotient.mk_surjective hq hq_surj fun x y ↦ Quotient.eq.trans (hfib x y).symm

/-- `TauCeti.freeProperQuotientDiffeomorph` sends the orbit of `x` to `q x`. -/
@[simp]
theorem freeProperQuotientDiffeomorph_apply_mk
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    {HN : Type*} [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN}
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    {q : M → N} (hq : Manifold.IsSubmersion I J ∞ q) (hq_surj : Surjective q)
    (hfib : ∀ x y : M, q x = q y ↔ MulAction.orbitRel G M x y) (x : M) :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
    freeProperQuotientDiffeomorph (IG := IG) hq hq_surj hfib
      (Quotient.mk (MulAction.orbitRel G M) x) = q x :=
  letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
  (ProperSMul.isSubmersion_quotientMk (I := IG) (G := G)).diffeomorphOfSurjective_apply
    Quotient.mk_surjective hq hq_surj _ x

/-- Composing `TauCeti.freeProperQuotientDiffeomorph` with the orbit projection recovers `q`. -/
@[simp]
theorem freeProperQuotientDiffeomorph_comp_quotientMk
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    {HN : Type*} [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN}
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    {q : M → N} (hq : Manifold.IsSubmersion I J ∞ q) (hq_surj : Surjective q)
    (hfib : ∀ x y : M, q x = q y ↔ MulAction.orbitRel G M x y) :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
    ⇑(freeProperQuotientDiffeomorph (IG := IG) hq hq_surj hfib) ∘
      Quotient.mk (MulAction.orbitRel G M) = q :=
  letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
  (ProperSMul.isSubmersion_quotientMk (I := IG) (G := G)).diffeomorphOfSurjective_comp
    Quotient.mk_surjective hq hq_surj _

/-- The inverse of `TauCeti.freeProperQuotientDiffeomorph` sends `q x` to the orbit of `x`. -/
@[simp]
theorem freeProperQuotientDiffeomorph_symm_apply
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    {HN : Type*} [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN}
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    {q : M → N} (hq : Manifold.IsSubmersion I J ∞ q) (hq_surj : Surjective q)
    (hfib : ∀ x y : M, q x = q y ↔ MulAction.orbitRel G M x y) (x : M) :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
    (freeProperQuotientDiffeomorph (IG := IG) hq hq_surj hfib).symm (q x) =
      Quotient.mk (MulAction.orbitRel G M) x := by
  let _ := ProperSMul.orbitRelQuotientChartedSpace IG G I M
  rw [← freeProperQuotientDiffeomorph_apply_mk (IG := IG) hq hq_surj hfib x,
    Diffeomorph.symm_apply_apply]

/-- Composing the inverse of `TauCeti.freeProperQuotientDiffeomorph` with `q` recovers the orbit
projection. -/
@[simp]
theorem freeProperQuotientDiffeomorph_symm_comp
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    {HN : Type*} [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN}
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    {q : M → N} (hq : Manifold.IsSubmersion I J ∞ q) (hq_surj : Surjective q)
    (hfib : ∀ x y : M, q x = q y ↔ MulAction.orbitRel G M x y) :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
    ⇑(freeProperQuotientDiffeomorph (IG := IG) hq hq_surj hfib).symm ∘ q =
      Quotient.mk (MulAction.orbitRel G M) :=
  funext (freeProperQuotientDiffeomorph_symm_apply (IG := IG) hq hq_surj hfib)

/-- `TauCeti.freeProperQuotientDiffeomorph` is the unique map `M ⧸ G → N` intertwining the orbit
projection with `q`. -/
theorem eq_freeProperQuotientDiffeomorph_iff
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    {HN : Type*} [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN}
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    {q : M → N} (hq : Manifold.IsSubmersion I J ∞ q) (hq_surj : Surjective q)
    (hfib : ∀ x y : M, q x = q y ↔ MulAction.orbitRel G M x y)
    {e : MulAction.orbitRel.Quotient G M → N} :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
    e = ⇑(freeProperQuotientDiffeomorph (IG := IG) hq hq_surj hfib) ↔
      e ∘ Quotient.mk (MulAction.orbitRel G M) = q :=
  letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
  (ProperSMul.isSubmersion_quotientMk (I := IG) (G := G)).eq_diffeomorphOfSurjective_iff
    Quotient.mk_surjective hq hq_surj _

/-- **Uniqueness of the smooth atlas on `M ⧸ G`.** Any charted-space structure on
`MulAction.orbitRel.Quotient G M` modelled on `ProperSMul.QuotientModelSpace EG E` that makes
`M ⧸ G` a smooth manifold and the orbit projection a smooth submersion has the same maximal atlas
as `ProperSMul.orbitRelQuotientChartedSpace`. -/
theorem maximalAtlas_freeProperQuotient_eq
    {c : ChartedSpace (ProperSMul.QuotientModelSpace EG E) (MulAction.orbitRel.Quotient G M)}
    (hc : letI := c;
      IsManifold 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E) ∞
        (MulAction.orbitRel.Quotient G M))
    (hq : letI := c;
      Manifold.IsSubmersion I 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E) ∞
        (Quotient.mk (MulAction.orbitRel G M))) :
    (letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M;
      IsManifold.maximalAtlas 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E) ∞
        (MulAction.orbitRel.Quotient G M)) =
    (letI := c;
      IsManifold.maximalAtlas 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E) ∞
        (MulAction.orbitRel.Quotient G M)) :=
  Manifold.IsSubmersion.maximalAtlas_eq
    (ProperSMul.instIsManifoldOrbitRelQuotient (I := IG) (G := G) (I' := I) (M := M)) hc
    (ProperSMul.isSubmersion_quotientMk (I := IG) (G := G)) hq Quotient.mk_surjective

/-- **For discrete `G`, the orbit projection is a smooth local diffeomorphism.** When the Lie group
`G` carries the discrete topology, `Quotient.mk (MulAction.orbitRel G M) : M → M ⧸ G` is a smooth
local diffeomorphism for `ProperSMul.orbitRelQuotientChartedSpace`. -/
theorem isLocalDiffeomorph_quotientMk_freeProperQuotient_of_discreteTopology
    [DiscreteTopology G] :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
    IsLocalDiffeomorph I 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E) ∞
      (Quotient.mk (MulAction.orbitRel G M)) := by
  let _ := ProperSMul.orbitRelQuotientChartedSpace IG G I M
  have := ProperSMul.instIsManifoldOrbitRelQuotient (I := IG) (G := G) (I' := I) (M := M)
  let K := 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E)
  intro x
  -- Since `G` is discrete, the orbit map is locally constant at `1`, so `𝔤 · x = 0`.
  have hconst : (fun h : G ↦ h • x) =ᶠ[𝓝 (1 : G)] fun _ : G ↦ (1 : G) • x := by
    filter_upwards [(isOpen_discrete {(1 : G)}).mem_nhds rfl] with h hh
    rw [mem_singleton_iff.1 hh]
  have horb : (InfinitesimalAction.fundamental IG G I M).orbitTangent x = ⊥ := by
    have hr := range_mfderiv_smul_const (I := IG) (I' := I) x (1 : G)
    rw [← one_smul G x, ← hr, hconst.mfderiv_eq, mfderiv_const]
    exact LinearMap.range_zero
  have hdimG : Module.finrank ℝ EG = 0 := by
    rw [← (finrank_orbitTangent_and_le IG G I x).1, horb, finrank_bot]
  have hinj : Injective (mfderiv I K (Quotient.mk (MulAction.orbitRel G M)) x) :=
    LinearMap.ker_eq_bot.1
      ((ProperSMul.ker_mfderiv_quotientMk (I := IG) (G := G) x).trans horb)
  exact isLocalDiffeomorphAt_of_injective_mfderiv
    (ProperSMul.contMDiff_quotientMk (I := IG) (G := G)).contMDiffOn
    isOpen_univ (mem_univ x) BoundarylessManifold.isInteriorPoint (by simp) hinj
    (by
      dsimp only [ProperSMul.QuotientModelSpace]
      rw [finrank_euclideanSpace_fin, hdimG, Nat.sub_zero])

end Uniqueness

end TauCeti

/-! ### Bundled smooth descent -/

namespace ContMDiffMap

open TauCeti

variable {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  {HG : Type*} [TopologicalSpace HG]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MulAction G M] [ProperSMul G M] [IsCancelSMul G M]
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]

/-- A smooth map `f : C^∞⟮I, M; J, N⟯` invariant under a free proper smooth Lie group action
descends to a bundled smooth map on the orbit space `M ⧸ G`. -/
def freeProperQuotientLift (f : C^∞⟮I, M; J, N⟯) (IG : ModelWithCorners ℝ EG HG)
    [LieGroup IG ∞ G] [ContMDiffSMul IG I ∞ G M]
    (hf : ∀ (g : G) (x : M), f (g • x) = f x) :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
    C^∞⟮𝓘(ℝ, ProperSMul.QuotientModelSpace EG E), MulAction.orbitRel.Quotient G M; J, N⟯ :=
  letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
  ⟨MulAction.orbitRelQuotientLift f hf,
    (contMDiff_orbitRelQuotientLift_freeProperQuotient_iff (IG := IG) le_rfl).2 f.contMDiff⟩

/-- The underlying function of `ContMDiffMap.freeProperQuotientLift` is
`TauCeti.MulAction.orbitRelQuotientLift`. -/
theorem coe_freeProperQuotientLift (f : C^∞⟮I, M; J, N⟯) (IG : ModelWithCorners ℝ EG HG)
    [LieGroup IG ∞ G] [ContMDiffSMul IG I ∞ G M]
    (hf : ∀ (g : G) (x : M), f (g • x) = f x) :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
    ⇑(f.freeProperQuotientLift IG hf) = MulAction.orbitRelQuotientLift f hf :=
  (rfl)

/-- `ContMDiffMap.freeProperQuotientLift` evaluates on the orbit of `x` as `f x`. -/
@[simp]
theorem freeProperQuotientLift_apply_mk (f : C^∞⟮I, M; J, N⟯) (IG : ModelWithCorners ℝ EG HG)
    [LieGroup IG ∞ G] [ContMDiffSMul IG I ∞ G M]
    (hf : ∀ (g : G) (x : M), f (g • x) = f x) (x : M) :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
    f.freeProperQuotientLift IG hf (Quotient.mk (MulAction.orbitRel G M) x) = f x :=
  MulAction.orbitRelQuotientLift_mk x

/-- Pulling `ContMDiffMap.freeProperQuotientLift` back along
`TauCeti.smoothFreeProperQuotientMk` recovers `f`. -/
@[simp]
theorem freeProperQuotientLift_comp_smoothFreeProperQuotientMk (f : C^∞⟮I, M; J, N⟯)
    (IG : ModelWithCorners ℝ EG HG) [LieGroup IG ∞ G]
    [ContMDiffSMul IG I ∞ G M] (hf : ∀ (g : G) (x : M), f (g • x) = f x) :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
    (f.freeProperQuotientLift IG hf).comp (smoothFreeProperQuotientMk IG G I M) = f := by
  let _ := ProperSMul.orbitRelQuotientChartedSpace IG G I M
  exact ContMDiffMap.ext fun x ↦ by simp

/-- `ContMDiffMap.freeProperQuotientLift` is the unique bundled smooth map on `M ⧸ G` whose
pullback along the orbit projection is `f`. -/
theorem eq_freeProperQuotientLift_iff (f : C^∞⟮I, M; J, N⟯) (IG : ModelWithCorners ℝ EG HG)
    [LieGroup IG ∞ G] [ContMDiffSMul IG I ∞ G M]
    (hf : ∀ (g : G) (x : M), f (g • x) = f x) :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I M
    ∀ {u : C^∞⟮𝓘(ℝ, ProperSMul.QuotientModelSpace EG E),
        MulAction.orbitRel.Quotient G M; J, N⟯},
      u = f.freeProperQuotientLift IG hf ↔
        u.comp (smoothFreeProperQuotientMk IG G I M) = f := by
  let _ := ProperSMul.orbitRelQuotientChartedSpace IG G I M
  intro u
  refine ⟨fun h ↦ h ▸ freeProperQuotientLift_comp_smoothFreeProperQuotientMk f IG hf,
    fun h ↦ DFunLike.ext' ?_⟩
  rw [coe_freeProperQuotientLift, MulAction.eq_orbitRelQuotientLift_iff]
  exact funext fun x ↦ by simpa using DFunLike.congr_fun h x

end ContMDiffMap

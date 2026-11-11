/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.From
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Support
public import TauCeti.Topology.CWComplex.Classical.CompactSupport
public import TauCeti.Topology.PathSpace.Moore.Pullback

/-!
# The skeletal filtration of the chains on the based path space

Let `B` be a relative CW complex with base `D`, and `b ∈ B`. The end point map `P_b B → B` of the
based path space pulls back the skeleta of `B` to subsets of `P_b B`, and the Moore loops at `b`,
acting by concatenation in front, do not move end points. So the chains on `P_b B` supported over
the `q`-skeleton (`TauCeti.pathFromChainSkeleton`) form a differential graded left submodule of
`C_*(P_b B; R)` over the loop algebra `C_*(Ω_b B; R)`:

* it is stable under the loop algebra and under the boundary, and homogeneous for the grading by
  dimension;
* it increases with `q`, and below degree `0` it is the chains over the base `D`, which is zero for
  an absolute CW complex;
* when `B` is the whole complex, every chain lies in some stage, since the end points of a cube of
  paths form a compact set, which lies in a finite skeleton
  (`TauCeti.iSup_pathFromChainSkeleton_eq_top`).

Over a map `f : E → B` sending a subset `S` into the `q`-skeleton, the projection of the
pulled-back path fibration `f^*P_b B → P_b B` sends the chains over `S` into the `q`-th stage
(`TauCeti.cubicalChainModuleLinearMap_toMoorePathFrom_mem_pathFromChainSkeleton`), and it is linear
over the loop algebra. For the characteristic map of an `n`-cell and the boundary sphere this places
the chains of the pulled-back pair, compared with `D^n × Ω_b B` in
`TauCeti.AlgebraicTopology.DGLocalSystem.Path.Pullback`, inside the `n`-th and `(n - 1)`-th stages.

This is the filtration of the target along which a semi-free model of `C_*(P_b B; R)` over
`C_*(Ω_b B; R)` is built one skeleton at a time, as in Brown's twisted tensor products: free
generators attached for the `n`-cells extend a comparison onto the stage `q = n - 1` to one onto
the stage `q = n`, through
`TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists`, whose submodules `N₀ ≤ N₁` are
homogeneous submodules over the loop algebra.

## Main definitions

* `TauCeti.pathFromChainSkeleton b C H R q`: the chains on `P_b B` supported over the `q`-skeleton,
  as a submodule over `C_*(Ω_b B; R)`.

## Main results

* `TauCeti.monotone_pathFromChainSkeleton`: the stages increase.
* `TauCeti.isHomogeneous_pathFromChainSkeleton`,
  `TauCeti.cubicalChainModuleDifferential_mem_pathFromChainSkeleton`: each stage is a homogeneous
  submodule closed under the boundary.
* `TauCeti.pathFromChainSkeleton_eq_bot_of_neg`: below degree `0`, the stage is zero for an
  absolute CW complex.
* `TauCeti.iSup_pathFromChainSkeleton_eq_top`: the filtration is exhaustive.
* `TauCeti.cubicalChainModuleLinearMap_toMoorePathFrom_mem_pathFromChainSkeleton`: chains of a
  pulled-back path fibration over a subset mapped into a skeleton lie in the corresponding stage.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4 and §7.1.
-/

public section

noncomputable section

open Set Topology Topology.RelCWComplex

namespace TauCeti

universe u

variable {B : Type u} [TopologicalSpace B] [T2Space B] {b : B} {C D : Set B} [RelCWComplex C D]
  {H : Type*} {R : Type*} [CommRing R]

/-- The preimages of the skeleta under the end point map are invariant under concatenation of
loops in front. -/
theorem smul_mem_preimageSkeleton_endpoint {q : ℤ} (ω : MooreLoopSpace B b)
    {γ : MoorePathFrom B b} (hγ : γ ∈ preimageSkeleton C (MoorePathFrom.endpoint B b) q) :
    ω • γ ∈ preimageSkeleton C (MoorePathFrom.endpoint B b) q := by
  simpa only [mem_preimageSkeleton_iff, MoorePathFrom.smul_eq_leftAct,
    MoorePathFrom.endpoint_leftAct] using hγ

variable (b C H R) in
/-- The **chains on the based path space over the `q`-skeleton**: the chains of `P_b B` supported
in the preimage of the `q`-skeleton of `B` under the end point map, as a submodule over the loop
algebra `C_*(Ω_b B; R)`. -/
def pathFromChainSkeleton (q : ℤ) :
    Submodule (loopChainAlgebra B b R) (cubicalChainModule (MoorePathFrom B b) H R) :=
  cubicalChainModuleLeftSupportedIn H R (S := preimageSkeleton C (MoorePathFrom.endpoint B b) q)
    fun ω _ ↦ smul_mem_preimageSkeleton_endpoint ω

/-- Membership in a stage of the skeletal filtration is support over the preimage of the
skeleton. -/
@[simp]
theorem mem_pathFromChainSkeleton {q : ℤ} {x : cubicalChainModule (MoorePathFrom B b) H R} :
    x ∈ pathFromChainSkeleton b C H R q ↔
      x ∈ cubicalChainModuleSupportedIn H R (preimageSkeleton C (MoorePathFrom.endpoint B b) q) :=
  mem_cubicalChainModuleLeftSupportedIn _

variable (b C H R) in
/-- Over the ground ring, a stage of the skeletal filtration is the chains supported over the
preimage of the skeleton. -/
@[simp]
theorem restrictScalars_pathFromChainSkeleton (q : ℤ) :
    (pathFromChainSkeleton b C H R q).restrictScalars R =
      cubicalChainModuleSupportedIn H R (preimageSkeleton C (MoorePathFrom.endpoint B b) q) :=
  restrictScalars_cubicalChainModuleLeftSupportedIn _

/-- The chain of a cube of paths whose end points lie in the `q`-skeleton lies in the `q`-th
stage. -/
theorem cubicalChainModuleLof_ofCube_mem_pathFromChainSkeleton {q : ℤ} {n : ℕ}
    {c : SingularCube (MoorePathFrom B b) n}
    (hc : ∀ t, MoorePathFrom.endpoint B b (c t) ∈ skeletonLT C ((q + 1).toNat : ℕ∞)) :
    cubicalChainModuleLof (MoorePathFrom B b) H R n (NormalizedCubicalChain.ofCube _ R c) ∈
      pathFromChainSkeleton b C H R q :=
  mem_pathFromChainSkeleton.2 <|
    cubicalChainModuleLof_ofCube_mem_cubicalChainModuleSupportedIn <| by
    rintro _ ⟨t, rfl⟩
    simpa using hc t

variable (b C H R) in
/-- The stages of the skeletal filtration increase. -/
theorem monotone_pathFromChainSkeleton : Monotone (pathFromChainSkeleton b C H R) :=
  fun _ _ h _ hx ↦ mem_pathFromChainSkeleton.2 <|
    cubicalChainModuleSupportedIn_mono (fun _ hy ↦ monotone_preimageSkeleton (C := C) _ h hy)
      (mem_pathFromChainSkeleton.1 hx)

variable (b C H R) in
/-- Each stage of the skeletal filtration is a homogeneous submodule. -/
theorem isHomogeneous_pathFromChainSkeleton (q : ℤ) :
    (pathFromChainSkeleton b C H R q).IsHomogeneous
      (cubicalChainModuleGrading (MoorePathFrom B b) H R) := fun i _ hx ↦
  mem_pathFromChainSkeleton.2 <|
    isHomogeneous_cubicalChainModuleSupportedIn _ i (mem_pathFromChainSkeleton.1 hx)

/-- Each stage of the skeletal filtration is closed under the boundary. -/
theorem cubicalChainModuleDifferential_mem_pathFromChainSkeleton {q : ℤ}
    {x : cubicalChainModule (MoorePathFrom B b) H R} (hx : x ∈ pathFromChainSkeleton b C H R q) :
    cubicalChainModuleDifferential (MoorePathFrom B b) H R x ∈ pathFromChainSkeleton b C H R q :=
  mem_pathFromChainSkeleton.2 <|
    cubicalChainModuleDifferential_mem_cubicalChainModuleSupportedIn
      (mem_pathFromChainSkeleton.1 hx)

/-- Below degree `0`, a stage of the skeletal filtration consists of the chains over the base. -/
theorem mem_pathFromChainSkeleton_of_neg {q : ℤ} (hq : q < 0)
    {x : cubicalChainModule (MoorePathFrom B b) H R} :
    x ∈ pathFromChainSkeleton b C H R q ↔
      x ∈ cubicalChainModuleSupportedIn H R (MoorePathFrom.endpoint B b ⁻¹' D) := by
  rw [mem_pathFromChainSkeleton, preimageSkeleton_of_neg _ hq]

/-- For an absolute CW complex, the skeletal filtration is zero below degree `0`. -/
@[simp]
theorem pathFromChainSkeleton_eq_bot_of_neg {C : Set B} [CWComplex C] {q : ℤ} (hq : q < 0) :
    pathFromChainSkeleton b C H R q = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun x hx ↦ ?_
  rwa [mem_pathFromChainSkeleton, preimageSkeleton_eq_empty _ hq,
    cubicalChainModuleSupportedIn_empty, Submodule.mem_bot] at hx

variable (b H R) in
/-- **The skeletal filtration is exhaustive**: if `B` is the whole complex, every chain on the
based path space lies in some stage. The end points of a compact set of paths form a compact
subset of `B`, which lies in a finite skeleton. -/
theorem iSup_pathFromChainSkeleton_eq_top (hC : ∀ x, x ∈ C) :
    ⨆ q, pathFromChainSkeleton b C H R q = ⊤ := by
  have h : ⨆ q, cubicalChainModuleSupportedIn H R
      (preimageSkeleton C (MoorePathFrom.endpoint B b) q) = ⊤ :=
    iSup_cubicalChainModuleSupportedIn_eq_top fun _ hK ↦
      exists_subset_preimageSkeleton_of_isCompact (MoorePathFrom.endpoint B b).continuous
        (range_subset_iff.2 fun _ ↦ hC _) hK
  rw [← Submodule.restrictScalars_eq_top_iff R, Submodule.restrictScalars_iSup]
  simpa only [restrictScalars_pathFromChainSkeleton] using h

/-- **Chains of a pulled-back path fibration lie in the skeletal filtration.** If `f : E → B` sends
`S` into the `q`-skeleton, the projection `f^*P_b B → P_b B` sends the chains supported over `S`
into the `q`-th stage. The projection is linear over the loop algebra
(`TauCeti.cubicalChainModuleLinearMap_smul`, with `MoorePathPullback.toMoorePathFrom_leftAct`). -/
theorem cubicalChainModuleLinearMap_toMoorePathFrom_mem_pathFromChainSkeleton {E : Type u}
    [TopologicalSpace E] {f : C(E, B)} {S : Set E} {q : ℤ}
    (hS : ∀ d ∈ S, f d ∈ skeletonLT C ((q + 1).toNat : ℕ∞))
    {x : cubicalChainModule (MoorePathPullback f b) H R}
    (hx : x ∈ cubicalChainModuleSupportedIn H R (MoorePathPullback.proj f b ⁻¹' S)) :
    cubicalChainModuleLinearMap R MoorePathPullback.toMoorePathFrom x ∈
      pathFromChainSkeleton b C H R q :=
  mem_pathFromChainSkeleton.2 <| cubicalChainModuleLinearMap_mem_cubicalChainModuleSupportedIn
    (fun y hy ↦ by
      simpa only [mem_preimageSkeleton_iff, MoorePathPullback.endpoint_toMoorePathFrom,
        MoorePathPullback.proj_apply] using
        hS _ hy) hx

end TauCeti

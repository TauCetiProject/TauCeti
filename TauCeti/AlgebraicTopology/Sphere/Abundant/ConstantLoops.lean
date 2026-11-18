/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.Abundant.Basic
public import TauCeti.Topology.MappingSpace.Sphere.Moore
public import TauCeti.Topology.PathSpace.Moore.Truncate
import Mathlib.Analysis.Normed.Module.Connected
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Basic

/-!
# Abundance classes killed by the constant loops

Let `Q` be a manifold of dimension `n`, abundant with 2-spheres at `b`
(`TauCeti.IsAbundantWithTwoSpheres`): some class `α ∈ Hₖ(Map(S², Q); ℤ)` lives over the
fundamental class of `Q` for evaluation `ev : Map(S², Q) → Q` at the north pole, and either
`k > n`, or `k = n` and its localization at the fibre over `b` is not that of a class of constant
spheres. Barraud, Damian, Humilière and Oancea prove in their Theorem 6.12 that the
`π₁`-sensitive Hofer–Zehnder capacity of `D*Q` is then finite, through their criterion
Proposition 6.7: a class `α'` of `H_*(Q; i_Q^* F) = H_*(P_{Q→Q} 𝓛₀Q)` with `j_! α' ≠ 0` and
`i_{Q*} α' = 0`, where `i_{Q*}` is induced by the inclusion
`P_{Q→Q} 𝓛₀Q ↪ P_{Q→𝓛₀Q} 𝓛₀Q` of the Moore paths in the contractible loops between constant
loops into those starting at a constant loop.

This file constructs that class from a witness `α` of abundance, as in the source's proof: the
class `α' = α - c_* ev_* α`, where `c : Q → Map(S², Q)` is the section of constant spheres.

* `ev_* α' = 0`, since `ev ∘ c = id` (`TauCeti.homologyMap_sub_homologyMap_section`), and
  therefore `(ev_z)_* α' = 0` for evaluation at every point `z` of `S²`, which is homotopic to
  evaluation at the north pole.
* The localization of `α'` at the fibre over `b` differs from that of `α` by the localization of
  a class of constant spheres (`TauCeti.fiberLocalization_sub_homologyMap_section`). In degree
  `k = n` the second condition of abundance says exactly that this does not make it vanish; in
  degree `k > n` the local homology of `Q` at `b` vanishes, so the localization is unchanged. So
  `α'` still witnesses abundance
  (`TauCeti.IsAbundantWithTwoSpheres.exists_homologyMap_mappingSpaceEval_eq_zero`).

Transported to the Moore model `P_{Q→Q} 𝓛₀Q ≃ Map(S², Q)`
(`TauCeti.sphere2FiberHomotopyEquivMoorePaths`), with the paths reversed so that the fibration
`P_{Q→Q} 𝓛₀Q → Q` is evaluation at the end of the path, as in the source, `α'` lives over the
fundamental class and has zero image in the homology of `P_{Q→𝓛₀Q} 𝓛₀Q`
(`TauCeti.IsAbundantWithTwoSpheres.exists_livesOverFundamentalClass_homologyMap_eq_zero`).
Truncating paths deforms `P_{Q→𝓛₀Q} 𝓛₀Q` onto the constant paths
(`TauCeti.MoorePath.truncateFromHomotopy`), so the image of `α'` there is read off from the
image of `α'` under evaluation at the start of the path, which is evaluation at the south pole.
These are the two hypotheses of the source's Proposition 6.7 for the local system
`F = C_*(P_{Q→⋆} 𝓛₀Q)`, read on the total spaces of the fibrations to which its fibration theorem
identifies `H_*(Q; i_Q^* F)` and `H_*(𝓛₀Q; F)`.

## Main results

* `TauCeti.IsAbundantWithTwoSpheres.exists_homologyMap_mappingSpaceEval_eq_zero`: abundance is
  witnessed by a class with vanishing image under evaluation at every point of `S²`.
* `TauCeti.IsAbundantWithTwoSpheres.exists_livesOverFundamentalClass_homologyMap_eq_zero`:
  a class of `P_{Q→Q} 𝓛₀Q` living over the fundamental class and vanishing in
  `P_{Q→𝓛₀Q} 𝓛₀Q`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 6.11, Proposition 6.7 and the
  proof of Theorem 6.12.
-/

public section

noncomputable section

open CategoryTheory Module Set

namespace TauCeti

variable {Q : Type} [TopologicalSpace Q]

/-- Homotopic maps induce the same map on integral singular homology, read through
`SSet.homologyMap` as in `TauCeti.LivesOverFundamentalClass`: Mathlib's
`TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor` in that form. -/
private lemma homologyMap_eq_of_homotopic {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : f.Homotopic g) (k : ℕ) :
    SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ (ULift.{0} ℤ)) k =
      SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom g)) (ModuleCat.of ℤ (ULift.{0} ℤ)) k :=
  TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor (C := ModuleCat.{0} ℤ)
    (f := TopCat.ofHom f) (g := TopCat.ofHom g) H.some _ k

/-- The induced map of a composite, on integral singular homology. -/
private lemma homologyMap_comp_apply {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) (k : ℕ)
    (x : ((TopCat.toSSet.obj (TopCat.of X)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) k :
      ModuleCat.{0} ℤ)) :
    (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (g.comp f)))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom x =
      (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom g)) (ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom
        ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom f))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom x) := by
  rw [← ModuleCat.comp_apply, ← SSet.homologyMap_comp, ← Functor.map_comp, ← TopCat.ofHom_comp]

/-- **Abundance is witnessed by a class killed by evaluation.** Let `Q` be a `T₁` space with a
chart at `b` to a real normed space of dimension `n`, abundant with 2-spheres at `b` in
dimension `n`. Then abundance is witnessed by a class `α ∈ Hₖ(Map(S², Q); ℤ)` whose image under
evaluation at every point of `S²` vanishes: `α` lives over the fundamental class at `b`, and
either `n < k`, or `k = n` and its localization at the fibre over `b` is not that of a class of
constant spheres. The class is `α₀ - c_* ev_* α₀` for any witness `α₀`, with `c` the constant
spheres (Barraud–Damian–Humilière–Oancea, proof of Theorem 6.12). -/
theorem IsAbundantWithTwoSpheres.exists_homologyMap_mappingSpaceEval_eq_zero [T1Space Q]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : OpenPartialHomeomorph Q E) {n : ℕ} {b : Q} (hb : b ∈ φ.source) (hn : finrank ℝ E = n)
    (h : IsAbundantWithTwoSpheres Q n b) :
    ∃ (k : ℕ) (α : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, Q))).homology
        (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)),
      LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) (mappingSpaceEval Sphere2.north) b
          α ∧
        (n < k ∨ k = n ∧ (fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ))
          (mappingSpaceEval Sphere2.north) b k).hom α ∉
            LinearMap.range (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
              ContinuousMap.const'
                (const'_preimage_mappingSpaceEval_preimage_subset Sphere2.north b) k).hom) ∧
        ∀ z : Sphere2, (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (mappingSpaceEval z)))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom α = 0 := by
  obtain ⟨k, α, hα, hk⟩ := (isAbundantWithTwoSpheres_iff Q n b).1 h
  have hs : (mappingSpaceEval Sphere2.north).comp ContinuousMap.const' = ContinuousMap.id Q :=
    mappingSpaceEval_comp_const' _
  have hloc := fiberLocalization_sub_homologyMap_section (ModuleCat.of ℤ (ULift.{0} ℤ))
    (mappingSpaceEval Sphere2.north) ContinuousMap.const' hs b α
  -- The correction term is the localization of a class of constant spheres.
  set r := (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ContinuousMap.const'
      (const'_preimage_mappingSpaceEval_preimage_subset Sphere2.north b) k).hom
    ((fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ)) id b k).hom
      ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (mappingSpaceEval Sphere2.north)))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom α)) with hr
  have hrange : r ∈ LinearMap.range (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
      ContinuousMap.const' (const'_preimage_mappingSpaceEval_preimage_subset Sphere2.north b)
        k).hom := ⟨_, hr.symm⟩
  refine ⟨k, α - (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ContinuousMap.const'))
    (ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom
      ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (mappingSpaceEval Sphere2.north)))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom α), ?_, ?_, fun z ↦ ?_⟩
  · rw [livesOverFundamentalClass_iff, hloc]
    rcases hk with hk | ⟨rfl, hk⟩
    · -- Above the dimension the local homology of `Q` at `b` vanishes.
      have h0 : fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ)) (id : Q → Q) b k = 0 :=
        (isZero_singularHomology_complSingleton_of_ne _ φ hb hn hk.ne').eq_of_tgt _ _
      rw [hr, h0, ModuleCat.hom_zero, LinearMap.zero_apply, map_zero, sub_zero]
      exact (livesOverFundamentalClass_iff _ _ b α).1 hα
    · intro h0
      rw [← sub_eq_zero.1 h0] at hrange
      exact hk hrange
  · rcases hk with hk | ⟨rfl, hk⟩
    · exact Or.inl hk
    · refine Or.inr ⟨rfl, fun hmem ↦ hk ?_⟩
      rw [hloc] at hmem
      simpa using add_mem hmem hrange
  · -- Evaluation at `z` is homotopic to evaluation at the north pole, since `S²` is path
    -- connected.
    have : PathConnectedSpace Sphere2 :=
      isPathConnected_iff_pathConnectedSpace.1 <| isPathConnected_sphere
        (by rw [← finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num) 0 zero_le_one
    rw [homologyMap_eq_of_homotopic
      ⟨mappingSpaceEvalHomotopy (PathConnectedSpace.somePath z Sphere2.north)⟩ k]
    exact homologyMap_sub_homologyMap_section _ _ ContinuousMap.const' hs α

variable (Q) in
/-- The inclusion `P_{Q→Q} 𝓛₀Q ↪ P_{Q→𝓛₀Q} 𝓛₀Q` of the Moore paths in the contractible loops
between constant loops into the Moore paths starting at a constant loop. -/
def constContractibleMoorePathsInclusion :
    C(ConstContractibleMoorePaths Q,
      MoorePath.pathsBetween (range (constContractibleLoop (Q := Q))) univ) :=
  ⟨inclusion fun _ hγ ↦ MoorePath.mem_pathsBetween.2 ⟨(MoorePath.mem_pathsBetween.1 hγ).1,
    mem_univ _⟩, continuous_inclusion _⟩

@[simp]
theorem coe_constContractibleMoorePathsInclusion (γ : ConstContractibleMoorePaths Q) :
    (constContractibleMoorePathsInclusion Q γ : MoorePath (contractibleLoops Q)) = γ :=
  (rfl)

/-- Reversal of the Moore paths between constant contractible loops. -/
private def constContractibleMoorePathsSymm :
    C(ConstContractibleMoorePaths Q, ConstContractibleMoorePaths Q) :=
  ⟨fun γ ↦ ⟨γ.1.symm, MoorePath.symm_mem_pathsBetween.2 γ.2⟩,
    (continuous_subtype_val.moorePath_symm).subtype_mk _⟩

private lemma constContractibleMoorePathsSymm_comp_self :
    (constContractibleMoorePathsSymm (Q := Q)).comp constContractibleMoorePathsSymm =
      ContinuousMap.id _ :=
  ContinuousMap.ext fun γ ↦ Subtype.ext (MoorePath.symm_symm γ.1)

/-- A constant contractible loop is the constant loop at its base point. -/
private lemma constContractibleLoop_basepointContractibleLoop {ℓ : contractibleLoops Q}
    (hℓ : ℓ ∈ range (constContractibleLoop (Q := Q))) :
    constContractibleLoop (basepointContractibleLoop ℓ) = ℓ := by
  obtain ⟨q, rfl⟩ := hℓ
  rw [basepointContractibleLoop_constContractibleLoop]

/-- **The class of the proof of Theorem 6.12.** Let `Q` be a `T₁` space with a chart at `b` to a
real normed space of dimension `n`, abundant with 2-spheres at `b` in dimension `n`. Then some
class `β ∈ Hₖ(P_{Q→Q} 𝓛₀Q; ℤ)` lives over the fundamental class at `b` for evaluation at the end
of the path, and has zero image in `Hₖ(P_{Q→𝓛₀Q} 𝓛₀Q; ℤ)`. These are the hypotheses
`j_! β ≠ 0` and `i_{Q*} β = 0` of Proposition 6.7 of Barraud–Damian–Humilière–Oancea, for the
local system `C_*(P_{Q→⋆} 𝓛₀Q)`, on the total spaces of the corresponding fibrations. -/
theorem IsAbundantWithTwoSpheres.exists_livesOverFundamentalClass_homologyMap_eq_zero
    [T1Space Q] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : OpenPartialHomeomorph Q E) {n : ℕ} {b : Q} (hb : b ∈ φ.source) (hn : finrank ℝ E = n)
    (h : IsAbundantWithTwoSpheres Q n b) :
    ∃ (k : ℕ) (β : ((TopCat.toSSet.obj (TopCat.of (ConstContractibleMoorePaths Q))).homology
        (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)),
      LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ))
          (ContinuousMap.snd.comp (constContractibleMooreEndpoints Q)) b β ∧
        (SSet.homologyMap
          (TopCat.toSSet.map (TopCat.ofHom (constContractibleMoorePathsInclusion Q)))
            (ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom β = 0 := by
  obtain ⟨k, α, hα, -, hev⟩ := h.exists_homologyMap_mappingSpaceEval_eq_zero φ hb hn
  let e := sphere2FiberHomotopyEquivMoorePaths Q
  let ρ : C(ConstContractibleMoorePaths Q, ConstContractibleMoorePaths Q) :=
    constContractibleMoorePathsSymm
  refine ⟨k, (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ρ.comp e.invFun)))
    (ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom α, ?_, ?_⟩
  · -- Going back to `Map(S², Q)` along `e.toFun ∘ ρ`, which lies over `Q`, recovers `α`.
    refine LivesOverFundamentalClass.of_homologyMap _ (e.toFun.comp ρ)
      (p' := mappingSpaceEval Sphere2.north) (funext fun γ ↦ ?_) ?_
    · have h := congrArg Prod.fst (DFunLike.congr_fun e.comp_toFun (ρ γ))
      simpa [ρ, constContractibleMoorePathsSymm] using h
    · rw [← homologyMap_comp_apply, ContinuousMap.comp_assoc, ← ContinuousMap.comp_assoc ρ,
        constContractibleMoorePathsSymm_comp_self,
        ContinuousMap.id_comp, homologyMap_eq_of_homotopic ⟨e.right_inv.some.toHomotopy⟩ k]
      simpa using hα
  · -- The inclusion is homotopic to the constant paths at the sources, and the source of the
    -- reversed path of a sphere is its value at the south pole.
    let A := range (constContractibleLoop (Q := Q))
    let g : C(Q, ↥(A ∩ univ)) :=
      ⟨fun q ↦ ⟨constContractibleLoop q, mem_range_self q, mem_univ _⟩, by fun_prop⟩
    have hfac : ((MoorePath.sourceFrom A).comp (constContractibleMoorePathsInclusion Q)).comp
        (ρ.comp e.invFun) = g.comp (mappingSpaceEval Sphere2.south) := by
      ext f : 1
      refine Subtype.ext ?_
      have hend := congrArg Prod.snd (DFunLike.congr_fun e.comp_invFun f)
      simp only [ContinuousMap.comp_apply, constContractibleMooreEndpoints_apply,
        sphere2Poles_apply] at hend
      simp only [ContinuousMap.comp_apply, MoorePath.coe_sourceFrom, mappingSpaceEval_apply,
        ContinuousMap.coe_mk, g]
      rw [← hend, constContractibleLoop_basepointContractibleLoop
        (MoorePath.mem_pathsBetween.1 (e.invFun f).2).2]
      exact MoorePath.source_symm _
    have H := (MoorePath.truncateFromHomotopy A).compContinuousMap
      ((constContractibleMoorePathsInclusion Q).comp (ρ.comp e.invFun))
    rw [← homologyMap_comp_apply, ← ContinuousMap.id_comp
        ((constContractibleMoorePathsInclusion Q).comp (ρ.comp e.invFun)),
      ← homologyMap_eq_of_homotopic ⟨H⟩ k, ContinuousMap.comp_assoc,
      ← ContinuousMap.comp_assoc _ (constContractibleMoorePathsInclusion Q), hfac,
      ← ContinuousMap.comp_assoc, homologyMap_comp_apply, hev, map_zero]

end TauCeti

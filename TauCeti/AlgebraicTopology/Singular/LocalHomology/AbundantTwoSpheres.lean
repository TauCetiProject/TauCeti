/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LivesOver
public import TauCeti.Topology.MappingSpace.Evaluation

/-!
# Manifolds abundant with 2-spheres

Let `Q` be an `n`-manifold with a point `b`, and let `ev : Map(S², Q) → Q` be evaluation of
maps of the 2-sphere at a point `s₀`, a fibration whose fibre over `b` is the double loop space
`Ω²Q` and which has the constant spheres `σ : Q → Map(S², Q)` as a section. Barraud, Damian,
Humilière and Oancea call `Q` **abundant with 2-spheres** if some class
`α ∈ H_*(Map(S², Q))` satisfies

1. `α` lives over the fundamental class of `Q`: its shriek map `j_! α ∈ H_{*-n}(Ω²Q)` to the
   fibre over `b` is nonzero;
2. if `α` has degree `n`, then `j_! α ∈ H₀(Ω²Q)` is not a multiple of the class of the constant
   sphere, that is, its image in `H₀(Ω²Q, pt)` is nonzero.

(their Definition 6.11). Their Theorem H states that the cotangent disc bundle of a closed
oriented manifold abundant with 2-spheres has finite `π₁`-sensitive Hofer–Zehnder capacity.

Both conditions are stated here through the localization `Hₖ(Map(S², Q)) → Hₖ(E, E ∖ Ω²Q)`
at the fibre (`TauCeti.fiberLocalization`), which carries the shriek map without a choice of
chart (`TauCeti.LivesOverFundamentalClass`). In degree `n` the constant spheres localize into
the image of the local homology `Hₙ(Q, Q ∖ {b}) ≅ H₀(pt)` under `σ`. The identification of the
localization with `H₀(Ω²Q)` (`TauCeti.TopCat.singularHomologyComplFiberIso`) carries this image
to the span of the class of the constant sphere at `b`, the kernel of `H₀(Ω²Q) → H₀(Ω²Q, pt)`, by
its naturality for the section `σ`; that comparison is not formalized here. The second condition
is therefore stated as: the localization of `α` is not the image under `σ` of a local homology
class of `Q` at `b` (`TauCeti.IsAbundantWithTwoSpheres`).

The proof of Theorem H only uses abundance through a class `α'` that lives over the
fundamental class and is killed by evaluation, `ev_* α' = 0`: in degree `n` it replaces `α` by
`α - σ_* ev_* α`. This file proves that abundance is equivalent to the existence of such a class
(`TauCeti.isAbundantWithTwoSpheres_iff`). The converse direction holds because evaluation sends
the image of `σ` in local homology isomorphically back to the local homology of `Q` at `b`.
Outside degree `n` the local homology of `Q` at `b` vanishes, so there the second condition is
automatic.

## Main definitions

* `TauCeti.IsAbundantWithTwoSpheres R M n s₀ b`: the manifold `M` of dimension `n` is abundant
  with 2-spheres at `b`, for evaluation at `s₀ ∈ S²` and coefficients `R`.

## Main results

* `TauCeti.isAbundantWithTwoSpheres_iff`: abundance holds exactly when some class of
  `Map(S², M)` lives over the fundamental class and is killed by evaluation.
* `TauCeti.IsAbundantWithTwoSpheres.exists_livesOverFundamentalClass`: such a class can be chosen
  killed by evaluation at every point of the sphere.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definitions 1.7 and 6.11 and the proof
  of Theorem 6.12.
-/

public section

noncomputable section

open CategoryTheory Metric Module

universe w

namespace TauCeti

variable {Λ : Type w} [Ring Λ] (R : ModuleCat.{w} Λ) (M : Type w) [TopologicalSpace M]

/-- The manifold `M` of dimension `n` is **abundant with 2-spheres** at `b`, with coefficients
in `R` (Barraud–Damian–Humilière–Oancea, Definition 6.11), if some class
`α ∈ Hₖ(Map(S², M); R)`, for evaluation `ev : Map(S², M) → M` at `s₀ ∈ S²`, satisfies:

1. `α` lives over the fundamental class at `b` for `ev`;
2. if `k = n`, the localization of `α` at the fibre over `b` is not the image of a local homology
   class of `M` at `b` under the section of `ev` by constant spheres.

Read through the identification of the localization at the fibre with `H₀(Ω²M)` in degree `n`,
the second condition is the source's: the shriek image of `α` in `H₀(Ω²M)` is not a multiple of
the class of the constant sphere. In degrees `k ≠ n` the condition would be automatic for a class
living over the fundamental class, since the local homology of `M` at `b` vanishes there. -/
def IsAbundantWithTwoSpheres (n : ℕ) (s₀ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (b : M) :
    Prop :=
  ∃ (k : ℕ) (α : ((TopCat.toSSet.obj
      (TopCat.of C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, M))).homology R k : ModuleCat.{w} Λ)),
    LivesOverFundamentalClass R (mappingSpaceEval s₀) b α ∧
      (k = n → (fiberLocalization R (mappingSpaceEval s₀) b k).hom α ∉ LinearMap.range
        (localHomologyMap R ContinuousMap.const'
          ((leftInverse_mappingSpaceEval_const s₀).preimage_preimage {b}).subset k).hom)

variable {M} [T1Space M] {V : Type w} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [ChartedSpace V M] {n : ℕ}

/-- **Abundance through classes killed by evaluation** (the reduction in the proof of
Barraud–Damian–Humilière–Oancea, Theorem 6.12). A manifold `M` of dimension `n` is abundant
with 2-spheres at `b` exactly when some class of `Map(S², M)` lives over the fundamental class at
`b` and is killed by evaluation `ev : Map(S², M) → M` at `s₀`. Given a class `α` as in the
definition, the class `α - σ_* ev_* α`, for the section `σ` by constant spheres, is such a
class. -/
theorem isAbundantWithTwoSpheres_iff (hn : finrank ℝ V = n)
    (s₀ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (b : M) :
    IsAbundantWithTwoSpheres R M n s₀ b ↔
      ∃ (k : ℕ) (α : ((TopCat.toSSet.obj
          (TopCat.of C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, M))).homology
          R k : ModuleCat.{w} Λ)),
        LivesOverFundamentalClass R (mappingSpaceEval s₀) b α ∧
          (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (mappingSpaceEval s₀))) R k).hom
            α = 0 := by
  have hσ : Function.LeftInverse (mappingSpaceEval (X := M) s₀) ContinuousMap.const' :=
    leftInverse_mappingSpaceEval_const s₀
  constructor
  · rintro ⟨k, α, hα, hn'⟩
    refine ⟨k, _, livesOverFundamentalClass_sub_homologyMap_of_leftInverse R hσ ?_,
      homologyMap_sub_homologyMap_of_leftInverse R hσ α⟩
    by_cases hk : k = n
    · exact hn' hk
    · -- Outside the dimension the local homology of `M` at `b` vanishes.
      rintro ⟨y, hy⟩
      have hy₀ : y = 0 := (ModuleCat.isZero_iff_subsingleton.1
        (isZero_singularHomology_complSingleton_of_ne R (chartAt V b) (mem_chart_source V b) hn
          hk)).elim y 0
      exact (livesOverFundamentalClass_iff R _ b α).1 hα (by rw [← hy, hy₀, map_zero])
  · rintro ⟨k, α, hα, hα₀⟩
    exact ⟨k, α, hα, fun _ ↦ hα.notMem_range_localHomologyMap R hσ hα₀⟩

/-- **Abundance gives a class killed by every evaluation.** If `M` is abundant with 2-spheres at
`b`, some class of `Map(S², M)` lives over the fundamental class at `b` for evaluation at `s₀` and
is killed by evaluation at every point of `S²`: evaluations at two points of the sphere are
homotopic. This is the form in which the proof of Barraud–Damian–Humilière–Oancea,
Theorem 6.12, uses abundance, where `Map(S², M)` is read as a space of paths of free loops and its
evaluations at the initial and the final point are compared. -/
theorem IsAbundantWithTwoSpheres.exists_livesOverFundamentalClass (hn : finrank ℝ V = n)
    {s₀ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1} {b : M}
    (h : IsAbundantWithTwoSpheres R M n s₀ b) :
    ∃ (k : ℕ) (α : ((TopCat.toSSet.obj
        (TopCat.of C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, M))).homology
        R k : ModuleCat.{w} Λ)),
      LivesOverFundamentalClass R (mappingSpaceEval s₀) b α ∧
        ∀ s₁ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
          (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (mappingSpaceEval s₁))) R k).hom
            α = 0 := by
  obtain ⟨k, α, hα, hα₀⟩ := (isAbundantWithTwoSpheres_iff R hn s₀ b).1 h
  refine ⟨k, α, hα, fun s₁ ↦ ?_⟩
  have : PathConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isPathConnected_iff_pathConnectedSpace.1 <| isPathConnected_sphere
      (by simp [← Module.finrank_eq_rank]) 0 zero_le_one
  have heq := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (C := ModuleCat.{w} Λ) (f := TopCat.ofHom (mappingSpaceEval (X := M) s₀))
    (g := TopCat.ofHom (mappingSpaceEval s₁))
    (mappingSpaceEval_homotopic (PathConnectedSpace.joined s₀ s₁)).some R k
  rw [← hα₀]
  exact (ConcreteCategory.congr_hom heq α).symm

end TauCeti

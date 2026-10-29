/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Section
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# The top homology of a compact manifold

Let `M` be a Hausdorff space modelled on a real normed space `E` of finite dimension `n`, that is,
a topological `n`-manifold without boundary. Restricting a class of `Hₖ(M, M ∖ M)` to the
points of `M` gives a cone `TauCeti.localHomologySystemCone` over the local homology system
`x ↦ Hₖ(M, M ∖ {x})`: the restrictions of a global class are compatible with the transport of
local homology along paths
(`TauCeti.localHomologyRestriction_univ_comp_localHomologyTransport`). The cone point
`Hₖ(M, M ∖ M) = Hₖ(M, ∅)` is identified with `Hₖ(M)` by the ordinary-to-relative quotient map.

For `M` compact, with coefficients in a module, this cone is a limit cone in degree `n`
(`TauCeti.isLimitLocalHomologySystemCone`): the top homology `Hₙ(M)` is the module of
transport-invariant families of local homology classes, the global sections of the local homology
system. This is Hatcher's description of `Hₙ(M; R)` by sections of the covering space `M_R`.

If `M` is moreover connected, a transport-invariant family is determined by its value at one point
`x`. So the restriction `Hₙ(M) ⟶ Hₙ(M, M ∖ {x})` is injective, and its image consists of the local
classes fixed by the transport along every loop at `x`
(`TauCeti.mem_range_localHomologySystemCone_π_app_iff`). In particular, for a compact simply
connected manifold the restriction is an isomorphism
(`TauCeti.isIso_localHomologySystemCone_π_app`), so that `Hₙ(M; N) ≅ N` for `n > 0`
(`TauCeti.singularHomologyIsoOfSimplyConnectedSpace`).

No orientability hypothesis is involved: orientability enters only through the action of loops at
`x` on the local homology `Hₙ(M, M ∖ {x})`, which is trivial when `M` is simply connected.

## Main results

* `TauCeti.localHomologySystemCone`: the restrictions `Hₖ(M) ⟶ Hₖ(M, M ∖ {x})`, as a cone over
  the local homology system.
* `TauCeti.isLimitLocalHomologySystemCone`: for compact `M`, the cone is a limit in degree `n`.
* `TauCeti.localHomologySystemCone_π_app_injective` and
  `TauCeti.mem_range_localHomologySystemCone_π_app_iff`: for compact connected `M`, restriction
  to a point is injective in degree `n`, with image the classes invariant under transport along
  loops.
* `TauCeti.isIso_localHomologySystemCone_π_app` and
  `TauCeti.singularHomologyIsoOfSimplyConnectedSpace`: for compact simply connected `M`,
  `Hₙ(M) ≅ Hₙ(M, M ∖ {x}) ≅ N`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Lemma 3.27 and Theorem 3.26.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set

universe w v u

namespace TauCeti

section Cone

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  (M E : Type w) [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]

/-- The restrictions `Hₖ(M, M ∖ M) ⟶ Hₖ(M, M ∖ {x})` to the points of `M`, as a cone over the
local homology system. The cone point `Hₖ(M, M ∖ M) = Hₖ(M, ∅)` is the singular homology of `M`,
through the ordinary-to-relative quotient map. -/
@[expose, simps]
def localHomologySystemCone (k : ℕ) : Cone (localHomologySystem R M E k) where
  pt := localHomology R (univ : Set M) k
  π :=
    { app x := localHomologyRestriction R (subset_univ {x.as}) k
      naturality x y f := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, localHomologySystem_map]
        exact (Category.id_comp _).trans
          (localHomologyRestriction_univ_comp_localHomologyTransport R (E := E) k f).symm }

end Cone

variable {Λ : Type w} [Ring Λ] (N : ModuleCat.{w} Λ)
  (M E : Type w) [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]

/-- **The top homology of a compact manifold is the module of parallel families of local
classes.** For a compact Hausdorff space modelled on a real normed space of finite dimension `n`,
the restrictions `Hₙ(M, M ∖ M; N) ⟶ Hₙ(M, M ∖ {x}; N)` exhibit `Hₙ(M, M ∖ M; N)` as the limit of
the local homology system: every transport-invariant family of local classes is the family of
restrictions of exactly one class. -/
def isLimitLocalHomologySystemCone [CompactSpace M] {n : ℕ} (hn : finrank ℝ E = n) :
    IsLimit (localHomologySystemCone N M E n) := by
  refine isLimitOfReflects (forget (ModuleCat.{w} Λ)) ((Types.isLimit_iff _).2 ?_).some
  intro s hs
  obtain ⟨γ, hγ, huniq⟩ := existsUnique_localHomologyRestriction_eq_of_invariant N hn
    isCompact_univ (fun x ↦ s (FundamentalGroupoid.mk x)) fun f ↦ hs f
  exact ⟨γ, fun x ↦ hγ x.as (mem_univ _), fun δ hδ ↦ huniq δ fun x _ ↦ hδ (.mk x)⟩

variable {M E}

/-- **Restriction to a point is injective on the top homology of a compact connected manifold**:
a class of `Hₙ(M, M ∖ M; N)` is determined by its image in the local homology
`Hₙ(M, M ∖ {x}; N)` at any single point. -/
theorem localHomologySystemCone_π_app_injective [CompactSpace M] [ConnectedSpace M] {n : ℕ}
    (hn : finrank ℝ E = n) (x : FundamentalGroupoid M) :
    Function.Injective ((localHomologySystemCone N M E n).π.app x) := by
  have := ChartedSpace.locallyPathConnectedSpace E M
  have := PathConnectedSpace.of_locallyPathConnectedSpace (X := M)
  intro γ δ h
  refine Concrete.isLimit_ext _ (isLimitLocalHomologySystemCone N M E hn) γ δ fun y ↦ ?_
  -- Transport the equality at `x` along a path from `x` to `y`.
  let f : x ⟶ y := Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x.as y.as)
  rw [← Cone.w _ f, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, h]

/-- **The image of the top homology of a compact connected manifold in local homology.** A local
class at `x` is the restriction of a class of `Hₙ(M, M ∖ M; N)` exactly when it is fixed by the
transport of local homology along every loop at `x`. -/
theorem mem_range_localHomologySystemCone_π_app_iff [CompactSpace M] [ConnectedSpace M] {n : ℕ}
    (hn : finrank ℝ E = n) (x : FundamentalGroupoid M)
    (z : (localHomology N {x.as} n : ModuleCat.{w} Λ)) :
    z ∈ range ((localHomologySystemCone N M E n).π.app x) ↔
      ∀ g : x ⟶ x, localHomologyTransport N M E n g z = z := by
  have := ChartedSpace.locallyPathConnectedSpace E M
  have := PathConnectedSpace.of_locallyPathConnectedSpace (X := M)
  constructor
  · rintro ⟨γ, rfl⟩ g
    exact ConcreteCategory.congr_hom ((localHomologySystemCone N M E n).w g) γ
  · intro hz
    -- Spread `z` over `M` by transport along chosen paths out of `x`.
    let p (y : FundamentalGroupoid M) : x ⟶ y :=
      Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x.as y.as)
    have hp {y y' : FundamentalGroupoid M} (f : y ⟶ y') :
        localHomologyTransport N M E n f (localHomologyTransport N M E n (p y) z) =
          localHomologyTransport N M E n (p y') z := by
      -- `p y ≫ f` is the loop `p y ≫ f ≫ inv (p y')` at `x`, followed by `p y'`.
      have hf : p y ≫ f = (p y ≫ f ≫ inv (p y')) ≫ p y' := by simp
      rw [← ConcreteCategory.comp_apply, ← localHomologyTransport_comp, hf,
        localHomologyTransport_comp, ConcreteCategory.comp_apply, hz]
    obtain ⟨γ, hγ, -⟩ := existsUnique_localHomologyRestriction_eq_of_invariant N hn
      isCompact_univ (fun y ↦ localHomologyTransport N M E n (p (FundamentalGroupoid.mk y)) z)
      fun f ↦ hp f
    exact ⟨γ, (hγ x.as (mem_univ _)).trans (hz (p x))⟩

/-- **The top homology of a compact simply connected manifold is local homology at a point.**
For a compact simply connected Hausdorff space modelled on a real normed space of finite dimension
`n`, the restriction `Hₙ(M, M ∖ M; N) ⟶ Hₙ(M, M ∖ {x}; N)` is an isomorphism. -/
theorem isIso_localHomologySystemCone_π_app [CompactSpace M] [SimplyConnectedSpace M] {n : ℕ}
    (hn : finrank ℝ E = n) (x : FundamentalGroupoid M) :
    IsIso ((localHomologySystemCone N M E n).π.app x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨localHomologySystemCone_π_app_injective N hn x, fun z ↦ ?_⟩
  refine (mem_range_localHomologySystemCone_π_app_iff N hn x z).2 fun g ↦ ?_
  rw [Subsingleton.elim (α := Path.Homotopic.Quotient x.as x.as) g (𝟙 x),
    localHomologyTransport_id]
  exact ConcreteCategory.id_apply z

/-- **The top homology of a compact simply connected manifold.** For a compact simply connected
Hausdorff space modelled on a real normed space of finite dimension `n + 1`, the singular homology
`Hₙ₊₁(M; N)` is a copy of `N`. The isomorphism is the quotient map to `Hₙ₊₁(M, M ∖ M; N)`, followed
by restriction to the local homology at `x` and the chart computation of local homology there. -/
def singularHomologyIsoOfSimplyConnectedSpace [CompactSpace M] [SimplyConnectedSpace M] {n : ℕ}
    (hn : finrank ℝ E = n + 1) (x : M) :
    (TopCat.toSSet.obj (TopCat.of M)).homology N (n + 1) ≅ N := by
  have : IsEmpty (TopPair.ofSubset ((univ : Set M)ᶜ : Set (TopCat.of M))).snd := by
    simp only [compl_univ]
    exact inferInstanceAs (IsEmpty (∅ : Set M))
  have := isIso_localHomologySystemCone_π_app N hn (FundamentalGroupoid.mk x)
  let e := asIso ((TopPair.ofSubset ((univ : Set M)ᶜ : Set (TopCat.of M))).singularHomologyπ N
    (n + 1))
  let e' := asIso ((localHomologySystemCone N M E (n + 1)).π.app (FundamentalGroupoid.mk x))
  exact e ≪≫ e' ≪≫
    singularHomologyComplSingletonIsoOfFinrankEq N (chartAt E x) (mem_chart_source E x) hn

/-- The isomorphism `Hₙ₊₁(M; N) ≅ N` of a compact simply connected manifold is the quotient map to
relative homology, followed by restriction to the local homology at `x` and the chart computation
of local homology. -/
theorem singularHomologyIsoOfSimplyConnectedSpace_hom [CompactSpace M] [SimplyConnectedSpace M]
    {n : ℕ} (hn : finrank ℝ E = n + 1) (x : M) :
    (singularHomologyIsoOfSimplyConnectedSpace N hn x).hom =
      (TopPair.ofSubset ((univ : Set M)ᶜ : Set (TopCat.of M))).singularHomologyπ N (n + 1) ≫
        localHomologyRestriction N (subset_univ {x}) (n + 1) ≫
          (singularHomologyComplSingletonIsoOfFinrankEq N (chartAt E x) (mem_chart_source E x)
            hn).hom :=
  (rfl)

end TauCeti

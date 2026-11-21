/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Section
public import TauCeti.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import TauCeti.Algebra.Module.Equiv.SpanSingleton

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
`x`. So the restriction `Hₙ(M) ⟶ Hₙ(M, M ∖ {x})` is injective
(`TauCeti.localHomologySystemCone_π_app_injective`). Its image consists of the local classes fixed
by the transport along every loop at `x`
(`TauCeti.mem_range_localHomologySystemCone_π_app_iff`), with no connectedness needed. In
particular, for a compact simply connected manifold the restriction is an isomorphism
(`TauCeti.isIso_localHomologySystemCone_π_app`), so that `Hₙ(M; N) ≅ N` for `n > 0`
(`TauCeti.singularHomologyIsoOfSimplyConnectedSpace`). With coefficients `N` free of rank one over
a domain, the restriction is an isomorphism as soon as `Hₙ(M; N)` is nonzero
(`TauCeti.singularHomologyToLocalHomology_bijective_of_ne_zero`): transport along a loop acts on the
local homology, a module free of rank one, by an automorphism fixing the nonzero image of a nonzero
class, hence trivially.

No orientability hypothesis is involved: orientability enters only through the action of loops at
`x` on the local homology `Hₙ(M, M ∖ {x})`, which is trivial when `M` is simply connected.

Without connectedness, a compact manifold has finitely many path components, so finitely many
points detect its top homology (`TauCeti.exists_finset_hom_ext_localHomologySystemCone`), and
`Hₙ(M; N)` embeds into a finite direct sum of copies of `N`. Over a ring over which every module
has projective dimension at most one, such as `ℤ`, with `N` projective, the top homology is
therefore projective (`TauCeti.projective_localHomology_univ`), and so is `Hₘ(M; N)` for every
`m ≥ n` (`TauCeti.projective_singularHomology_of_compactSpace`). This is the input the universal
coefficient theorem needs for the vanishing of the cohomology of `M` above its dimension.

## Main results

* `TauCeti.localHomologySystemCone`: the restrictions `Hₖ(M) ⟶ Hₖ(M, M ∖ {x})`, as a cone over
  the local homology system.
* `TauCeti.isLimitLocalHomologySystemCone`: for compact `M`, the cone is a limit in degree `n`.
* `TauCeti.localHomology_univ_ext_of_localHomologySystemCone`: for compact `M`, classes of
  `Hₙ(M, M ∖ M)` with the same restrictions to the points of a set meeting every path component
  are equal.
* `TauCeti.localHomologySystemCone_π_app_injective` and
  `TauCeti.mem_range_localHomologySystemCone_π_app_iff`: for compact `M`, restriction to a point
  has image the classes invariant under transport along loops in degree `n`, and it is injective
  if `M` is connected.
* `TauCeti.singularHomologyToLocalHomology_injective`: for compact connected `M`, the map
  `Hₙ(M) → Hₙ(M, M ∖ {x})` is injective.
* `TauCeti.singularHomology_ext_of_singularHomologyToLocalHomology`: for compact `M`, classes of
  `Hₙ(M)` with the same images in local homology at the points of a set meeting every path
  component are equal.
* `TauCeti.singularHomologyToLocalHomology_surjective_of_ne_zero` and
  `TauCeti.singularHomologyToLocalHomology_bijective_of_ne_zero`: for compact connected `M`, with
  coefficients free of rank one over a domain, the map `Hₙ(M; N) → Hₙ(M, M ∖ {x}; N)` is surjective,
  hence bijective, as soon as `Hₙ(M; N)` is nonzero.
* `TauCeti.isIso_localHomologySystemCone_π_app` and
  `TauCeti.singularHomologyIsoOfSimplyConnectedSpace`: for compact simply connected `M`,
  `Hₙ(M) ≅ Hₙ(M, M ∖ {x}) ≅ N`.
* `TauCeti.exists_finset_hom_ext_localHomologySystemCone`: for compact `M`, restrictions to
  finitely many points detect the top homology.
* `TauCeti.projective_localHomology_univ` and `TauCeti.projective_singularHomology_of_compactSpace`:
  over a hereditary ring, the homology of a compact manifold is projective from the dimension on.

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

/-- **The top homology of a compact manifold is determined on a set meeting every path
component**: two classes of `Hₙ(M, M ∖ M; N)` are equal as soon as their images in the local
homology `Hₙ(M, M ∖ {x}; N)` agree at every point `x` of a set `D` from which every point of `M`
can be reached by a path. -/
theorem localHomology_univ_ext_of_localHomologySystemCone [CompactSpace M] {n : ℕ}
    (hn : finrank ℝ E = n) {D : Set M} (hD : ∀ y, ∃ x ∈ D, Joined x y)
    {γ δ : (localHomology N (univ : Set M) n : ModuleCat.{w} Λ)}
    (h : ∀ x ∈ D, (localHomologySystemCone N M E n).π.app (.mk x) γ =
      (localHomologySystemCone N M E n).π.app (.mk x) δ) :
    γ = δ := by
  refine Concrete.isLimit_ext _ (isLimitLocalHomologySystemCone N M E hn) γ δ fun y ↦ ?_
  obtain ⟨x, hx, hxy⟩ := hD y.as
  -- Transport the equality at `x` along a path from `x` to `y`.
  let f : FundamentalGroupoid.mk x ⟶ y := Path.Homotopic.Quotient.mk hxy.somePath
  rw [← Cone.w _ f]
  exact congrArg (ConcreteCategory.hom ((localHomologySystem N M E n).map f)) (h x hx)

/-- **Restriction to a point is injective on the top homology of a compact connected manifold**:
a class of `Hₙ(M, M ∖ M; N)` is determined by its image in the local homology
`Hₙ(M, M ∖ {x}; N)` at any single point. -/
theorem localHomologySystemCone_π_app_injective [CompactSpace M] [ConnectedSpace M] {n : ℕ}
    (hn : finrank ℝ E = n) (x : FundamentalGroupoid M) :
    Function.Injective ((localHomologySystemCone N M E n).π.app x) := by
  have := ChartedSpace.locallyPathConnectedSpace E M
  have := PathConnectedSpace.of_locallyPathConnectedSpace (X := M)
  intro γ δ h
  exact localHomology_univ_ext_of_localHomologySystemCone N hn (D := {x.as})
    (fun y ↦ ⟨x.as, rfl, PathConnectedSpace.joined x.as y⟩) (by rintro _ rfl; exact h)

/-- **A top-dimensional class of a compact manifold is determined on a set meeting every path
component**: two classes of `Hₙ(M; N)` are equal as soon as their images in the local homology
`Hₙ(M, M ∖ {x}; N)` agree at every point `x` of a set `D` from which every point of `M` can be
reached by a path. A dense set `D` qualifies, since path components of a manifold are open. -/
theorem singularHomology_ext_of_singularHomologyToLocalHomology [CompactSpace M] {n : ℕ}
    (hn : finrank ℝ E = n) {D : Set M} (hD : ∀ y, ∃ x ∈ D, Joined x y)
    {μ μ' : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} Λ)}
    (h : ∀ x ∈ D,
      singularHomologyToLocalHomology N x n μ = singularHomologyToLocalHomology N x n μ') :
    μ = μ' := by
  refine (singularHomologyπ_compl_univ_bijective M N n).1
    (localHomology_univ_ext_of_localHomologySystemCone N hn hD fun x hx ↦ ?_)
  have hx' := h x hx
  rwa [singularHomologyToLocalHomology_apply, singularHomologyToLocalHomology_apply,
    ← localHomologySystemCone_π_app N M E n (FundamentalGroupoid.mk x)] at hx'

/-- **A top-dimensional class of a compact connected manifold is determined at one point**: the map
`Hₙ(M; N) → Hₙ(M, M ∖ {x}; N)` to the local homology at any point `x` is injective. -/
theorem singularHomologyToLocalHomology_injective [CompactSpace M] [ConnectedSpace M] {n : ℕ}
    (hn : finrank ℝ E = n) (x : M) :
    Function.Injective (singularHomologyToLocalHomology N x n) := by
  have := ChartedSpace.locallyPathConnectedSpace E M
  have := PathConnectedSpace.of_locallyPathConnectedSpace (X := M)
  intro γ δ h
  exact singularHomology_ext_of_singularHomologyToLocalHomology N hn (D := {x})
    (fun y ↦ ⟨x, rfl, PathConnectedSpace.joined x y⟩) (by rintro _ rfl; exact h)

/-- **The image of the top homology of a compact manifold in local homology.** A local
class at `x` is the restriction of a class of `Hₙ(M, M ∖ M; N)` exactly when it is fixed by the
transport of local homology along every loop at `x`. Connectedness is not needed: off the path
component of `x` the family of local classes is extended by zero. -/
theorem mem_range_localHomologySystemCone_π_app_iff [CompactSpace M] {n : ℕ}
    (hn : finrank ℝ E = n) (x : FundamentalGroupoid M)
    (z : (localHomology N {x.as} n : ModuleCat.{w} Λ)) :
    z ∈ range ((localHomologySystemCone N M E n).π.app x) ↔
      ∀ g : x ⟶ x, localHomologyTransport N M E n g z = z := by
  constructor
  · rintro ⟨γ, rfl⟩ g
    exact ConcreteCategory.congr_hom ((localHomologySystemCone N M E n).w g) γ
  · intro hz
    classical
    -- Spread `z` over the path component of `x` by transport along chosen paths out of `x`,
    -- and by zero elsewhere.
    let p {y : FundamentalGroupoid M} (h : Joined x.as y.as) : x ⟶ y :=
      Path.Homotopic.Quotient.mk h.somePath
    have hp {y y' : FundamentalGroupoid M} (h : Joined x.as y.as) (h' : Joined x.as y'.as)
        (f : y ⟶ y') :
        localHomologyTransport N M E n f (localHomologyTransport N M E n (p h) z) =
          localHomologyTransport N M E n (p h') z := by
      -- `p h ≫ f` is the loop `p h ≫ f ≫ inv (p h')` at `x`, followed by `p h'`.
      have hf : p h ≫ f = (p h ≫ f ≫ inv (p h')) ≫ p h' := by simp
      rw [← ConcreteCategory.comp_apply, ← localHomologyTransport_comp, hf,
        localHomologyTransport_comp, ConcreteCategory.comp_apply, hz]
    obtain ⟨γ, hγ, -⟩ := existsUnique_localHomologyRestriction_eq_of_invariant N hn
      isCompact_univ
      (fun y ↦ if h : Joined x.as y then
        localHomologyTransport N M E n (p (y := FundamentalGroupoid.mk y) h) z else 0)
      fun {y y'} f ↦ by
        have hyy' : Joined y.as y'.as := Quotient.inductionOn f fun q ↦ ⟨q⟩
        by_cases h : Joined x.as y.as
        · have h' := h.trans hyy'
          simp only [h, h', dite_true]
          exact hp h h' f
        · have h' : ¬ Joined x.as y'.as := fun h' ↦ h (h'.trans hyy'.symm)
          simp only [h, h', dite_false, map_zero]
    refine ⟨γ, (hγ x.as (mem_univ _)).trans ?_⟩
    simpa only [Joined.refl x.as, dite_true] using hz (p (Joined.refl x.as))

/-- **Nonzero top homology maps onto local homology.** Let `M` be a compact connected manifold of
dimension `n`, and `N` a module free of rank one over a domain `Λ`. If `Hₙ(M; N)` is nonzero, then
the restriction `Hₙ(M; N) → Hₙ(M, M ∖ {x}; N)` to the local homology at any point `x` is surjective,
hence an isomorphism (`TauCeti.singularHomologyToLocalHomology_injective`). Indeed its image is the
set of local classes fixed by transport along loops at `x`, and transport along a loop acts on the
local homology, a module free of rank one, by an automorphism, which fixes the nonzero image of a
nonzero class and is therefore the identity. In other words, `M` is `N`-orientable. -/
theorem singularHomologyToLocalHomology_surjective_of_ne_zero [IsDomain Λ] (eN : N ≃ₗ[Λ] Λ)
    [CompactSpace M] [ConnectedSpace M] {n : ℕ} (hn : finrank ℝ E = n) (x : M)
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} Λ)} (hμ : μ ≠ 0) :
    Function.Surjective (singularHomologyToLocalHomology N x n) := by
  -- The image of `μ` is a nonzero local class fixed by transport along every loop.
  have hμx : singularHomologyToLocalHomology N x n μ ≠ 0 := by
    rw [← map_zero (singularHomologyToLocalHomology N x n)]
    exact (singularHomologyToLocalHomology_injective N hn x).ne hμ
  have hfix (g : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x) :
      localHomologyTransport N M E n g (singularHomologyToLocalHomology N x n μ) =
        singularHomologyToLocalHomology N x n μ :=
    (mem_range_localHomologySystemCone_π_app_iff N hn (FundamentalGroupoid.mk x) _).1
      ⟨((TopPair.ofSubset ((univ : Set (TopCat.of M))ᶜ)).singularHomologyπ N n).hom μ, by
        rw [localHomologySystemCone_π_app]
        exact (singularHomologyToLocalHomology_apply N x μ).symm⟩ g
  -- Hence every local class is fixed by transport along loops, and comes from a global class.
  intro z
  obtain ⟨γ, hγ⟩ := (mem_range_localHomologySystemCone_π_app_iff N hn
    (FundamentalGroupoid.mk x) z).2 fun g ↦
      LinearMap.congr_fun (LinearMap.eq_id_of_apply_eq_self (localHomologyTransport N M E n g).hom
        (localHomologySingletonLinearEquiv N hn eN x) hμx (hfix g)) z
  obtain ⟨γ', rfl⟩ := (singularHomologyπ_compl_univ_bijective M N n).2 γ
  exact ⟨γ', by
    rw [← hγ, localHomologySystemCone_π_app]
    exact singularHomologyToLocalHomology_apply N x γ'⟩

/-- **Nonzero top homology is local homology.** For a compact connected manifold `M` of dimension
`n` and a module `N` free of rank one over a domain, if `Hₙ(M; N)` is nonzero then the restriction
`Hₙ(M; N) → Hₙ(M, M ∖ {x}; N)` is bijective at every point `x`. -/
theorem singularHomologyToLocalHomology_bijective_of_ne_zero [IsDomain Λ] (eN : N ≃ₗ[Λ] Λ)
    [CompactSpace M] [ConnectedSpace M] {n : ℕ} (hn : finrank ℝ E = n) (x : M)
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} Λ)} (hμ : μ ≠ 0) :
    Function.Bijective (singularHomologyToLocalHomology N x n) :=
  ⟨singularHomologyToLocalHomology_injective N hn x,
    singularHomologyToLocalHomology_surjective_of_ne_zero N eN hn x hμ⟩

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

/-- **Finitely many points detect the top homology of a compact manifold.** For a compact
Hausdorff space modelled on a real normed space of finite dimension `n`, there is a finite set `F`
of points, meeting every path component, such that two morphisms into `Hₙ(M, M ∖ M; N)` agree as
soon as their composites with the restrictions `Hₙ(M, M ∖ M; N) ⟶ Hₙ(M, M ∖ {x}; N)` agree for
every `x ∈ F`. -/
theorem exists_finset_hom_ext_localHomologySystemCone [CompactSpace M] {n : ℕ}
    (hn : finrank ℝ E = n) :
    ∃ F : Finset M, ∀ {Z : ModuleCat.{w} Λ} (u v : Z ⟶ localHomology N (univ : Set M) n),
      (∀ x ∈ F, u ≫ (localHomologySystemCone N M E n).π.app (.mk x) =
        v ≫ (localHomologySystemCone N M E n).π.app (.mk x)) → u = v := by
  have := ChartedSpace.locallyPathConnectedSpace E M
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun x : M ↦ pathComponent x)
    (fun x ↦ IsOpen.pathComponent x) fun y _ ↦ mem_iUnion.2 ⟨y, mem_pathComponent_self y⟩
  refine ⟨F, fun u v h ↦ ConcreteCategory.hom_ext _ _ fun z ↦ ?_⟩
  refine localHomology_univ_ext_of_localHomologySystemCone N hn (D := F) (fun y ↦ ?_)
    fun x hx ↦ ?_
  · obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.1 (hF (mem_univ y))
    exact ⟨x, hx, hxy⟩
  · exact ConcreteCategory.congr_hom (h x hx) z

/-- **The top homology of a compact manifold is projective over a hereditary ring.** Let `Λ` be a
ring over which every module has projective dimension at most one, such as `ℤ` or any principal
ideal domain, and let `N` be a projective `Λ`-module. For a compact Hausdorff space modelled on a
real normed space of finite dimension `n`, the top homology `Hₙ(M, M ∖ M; N)` is projective: it
embeds into the finite direct sum of the local homology modules `Hₙ(M, M ∖ {x}; N) ≅ N` at the
points of `TauCeti.exists_finset_hom_ext_localHomologySystemCone`. -/
theorem projective_localHomology_univ [∀ V : ModuleCat.{w} Λ, HasProjectiveDimensionLE V 1]
    [Projective N] [CompactSpace M] {n : ℕ} (hn : finrank ℝ E = n) :
    Projective (localHomology N (univ : Set M) n) := by
  obtain ⟨F, hF⟩ := exists_finset_hom_ext_localHomologySystemCone N (M := M) hn
  have (x : M) : Projective (localHomology N ({x} : Set M) n) := by
    subst hn
    exact Projective.of_iso
      (singularHomologyComplSingletonFinrankIso N (chartAt E x) (mem_chart_source E x)).symm
      inferInstance
  let g : localHomology N (univ : Set M) n ⟶ ⨁ fun x : F ↦ localHomology N ({x.val} : Set M) n :=
    biproduct.lift fun x ↦ localHomologyRestriction N (subset_univ {x.val}) n
  have : Mono g := ⟨fun u v huv ↦ hF u v fun x hx ↦ by
    have h := huv =≫ biproduct.π _ ⟨x, hx⟩
    rw [Category.assoc, Category.assoc, biproduct.lift_π] at h
    exact h⟩
  exact (forall_hasProjectiveDimensionLE_one_iff_projective_of_mono _).1 inferInstance g

/-- **The homology of a compact manifold is projective from the dimension on.** Over a ring `Λ`
over which every module has projective dimension at most one, with a projective coefficient module
`N`, the singular homology `Hₘ(M; N)` of a compact Hausdorff space modelled on a real normed space
of finite dimension `n` is projective for every `m ≥ n`: it is the projective top homology for
`m = n` (`TauCeti.projective_localHomology_univ`) and zero for `m > n`
(`TauCeti.isZero_singularHomology_of_compactSpace`). With `Λ = N = ℤ`, the integral homology of a
compact manifold is free abelian from the dimension on. -/
theorem projective_singularHomology_of_compactSpace
    [∀ V : ModuleCat.{w} Λ, HasProjectiveDimensionLE V 1] [Projective N] [CompactSpace M]
    {n m : ℕ} (hn : finrank ℝ E = n) (hm : n ≤ m) :
    Projective (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) m).obj N).obj
      (TopCat.of M)) := by
  obtain rfl | hm := hm.eq_or_lt
  · exact Projective.of_iso
      (asIso ((TopPair.ofSubset ((univ : Set M)ᶜ : Set (TopCat.of M))).singularHomologyπ N n)).symm
      (projective_localHomology_univ N hn)
  · exact Projective.of_iso (isZero_singularHomology_of_compactSpace N hn hm).isoZero.symm
      inferInstance

end TauCeti

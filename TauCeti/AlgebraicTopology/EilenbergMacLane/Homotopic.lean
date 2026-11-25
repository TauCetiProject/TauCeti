/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import TauCeti.AlgebraicTopology.Homotopy.Relative.Disk
public import TauCeti.AlgebraicTopology.Homotopy.Relative.Exact
public import TauCeti.Topology.CWComplex.Classical.Subcomplex
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
public import TauCeti.Topology.Homotopy.HomotopyGroup.Product
public import TauCeti.Topology.Homotopy.Homotopic.Rel

import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
import TauCeti.Topology.CWComplex.Classical.Zero

/-!
# Maps from a CW complex into a space without higher homotopy

Let `Y` be a space whose homotopy groups `πₙ(Y, y)` vanish for `n ≥ 2` at every point `y`, such as
a `K(H, 1)`. A map from a CW complex into `Y` is determined up to homotopy by what it does on the
`1`-skeleton up to homotopy: two maps `f g : C → Y` out of a relative CW complex `(C, D)` that, on
every path in `C` between points of the `0`-skeleton, agree up to homotopy relative to the
endpoints, are homotopic relative to the `0`-skeleton
(`TauCeti.homotopicRel_skeletonLT_one_of_forall_homotopicRel`). For a complex whose only `0`-cell
is its base point, this says that pointed maps inducing the same homomorphism of fundamental groups
are homotopic relative to the base point (`TauCeti.homotopicRel_singleton_of_mapOfEq_eq`). This is
the uniqueness half of Hatcher's Proposition 1B.9 for complexes with a single `0`-cell, the case
to which Hatcher reduces by collapsing a maximal tree; for the cellular classifying space, the
existence half is `TauCeti.exists_mapOfEq_cellularClassifyingSpace`. For a path-connected CW
complex the base point may be any `0`-cell
(`TauCeti.homotopicRel_singleton_of_mapOfEq_eq_of_mem_skeletonLT`): this is the uniqueness half of
Proposition 1B.9 with a `0`-cell as base point.

The proof reads a homotopy from `f` to `g` relative to a set `A` as a deformation, relative to
`A`, of the map `(f, g) : C → Y × Y` into the diagonal. Since the diagonal `Δ ⊆ Y × Y` is a
retract of `Y × Y` and `πₙ(Y × Y)` vanishes for `n ≥ 2`, the exact sequence of the pair shows that
the relative homotopy sets `πₙ(Y × Y, Δ)` vanish for `n ≥ 2`
(`TauCeti.subsingleton_relHomotopyGroup_diagonal`). So the compression lemma deforms `(f, g)` into
`Δ` relative to `D` as soon as `(C, D)` has no cells of dimension `0` or `1` and `f = g` on `D`
(`TauCeti.homotopicRel_base_of_isEmpty_cell`). In general the hypothesis on paths first lets one
homotope `f`, relative to the `0`-skeleton, to agree with `g` on every `1`-cell, and the
compression lemma then applies to `C` relative to its `1`-skeleton
(`Topology.RelCWComplex.Subcomplex.relCWComplex`), which has no cells of dimension below `2`.

For an arbitrary `0`-cell `x₀`, choose a path `α v` from `x₀` to every `0`-cell `v`, constant
at `x₀`. The paths `(g ∘ α v)⁻¹ · (f ∘ α v)` from `g v` to `f v` form a homotopy on the
`0`-skeleton, which is discrete, and the homotopy extension property of the `0`-skeleton extends
it to a homotopy, stationary at `x₀`, from `g` to a map `f'` that agrees with `f` on the
`0`-skeleton. The square of this homotopy over a path `p` from a `0`-cell `a` to a `0`-cell `b`
shows that `f' ∘ p` is homotopic to `(f ∘ α a)⁻¹ · g ∘ (α a · p · (α b)⁻¹) · (f ∘ α b)`
relative to the endpoints, which is homotopic to `f ∘ p` because `f` and `g` agree on loops at
`x₀`. So the first criterion applies to `f` and `f'`.

Only the vanishing of the higher homotopy groups of `Y` is used, and `Y` need not have the
homotopy type of a CW complex. Neither space needs to be path connected, except that the base
point `x₀` must be joined to every `0`-cell when it is not the only one: maps from two points to
two points agreeing at one of them induce the same homomorphism on fundamental groups at that
point, but they are not homotopic unless they agree at the other point as well.

## Main results

* `TauCeti.subsingleton_relHomotopyGroup_diagonal`: the relative homotopy sets of the diagonal in
  `Y × Y` vanish from degree `2` on.
* `TauCeti.homotopicRel_base_of_isEmpty_cell`: maps agreeing on the base of a relative CW complex
  without cells of dimension `0` and `1` are homotopic relative to the base.
* `TauCeti.homotopicRel_skeletonLT_one_of_forall_homotopicRel`: maps agreeing up to homotopy on
  paths between points of the `0`-skeleton are homotopic relative to the `0`-skeleton.
* `TauCeti.homotopicRel_singleton_of_mapOfEq_eq`: **pointed maps from a CW complex with a single
  `0`-cell into a space without higher homotopy are determined, up to homotopy relative to the
  base point, by the homomorphism they induce on fundamental groups.**
* `TauCeti.homotopicRel_singleton_of_mapOfEq_eq_of_cwComplex`: the same for a CW structure on the
  whole space.
* `TauCeti.homotopicRel_singleton_of_mapOfEq_eq_of_mem_skeletonLT`: **the same for a
  path-connected CW complex based at any of its `0`-cells.**
* `TauCeti.homotopicRel_singleton_of_mapOfEq_eq_of_mem_skeletonLT_of_cwComplex`: the same for a
  CW structure on the whole space.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 1.B, Proposition 1B.9, and Section 4.1, Lemma 4.6 (the compression lemma).
-/

public section

noncomputable section

universe u v

open Metric Set Topology Topology.RelCWComplex
open scoped unitInterval Topology.Homotopy

namespace TauCeti

variable {Y : Type v} [TopologicalSpace Y]

/-- If the homotopy groups of `Y` vanish from degree `2` on, at every point, then so do the
relative homotopy sets `π_{n+2}(Y × Y, Δ, b)` of the diagonal `Δ ⊆ Y × Y`, at every point `b` of
the diagonal. -/
theorem subsingleton_relHomotopyGroup_diagonal
    (hY : ∀ (y : Y) (n : ℕ), Subsingleton (π_ (n + 2) Y y)) (n : ℕ) (b : diagonal Y) :
    Subsingleton (RelHomotopyGroup (Fin (n + 1))
      ⟨TopPair.ofSubset (X := TopCat.of (Y × Y)) (diagonal Y), b⟩) := by
  -- The diagonal is a retract of `Y × Y`, so its inclusion is injective on homotopy groups.
  let r : C(Y × Y, diagonal Y) := ⟨fun p ↦ ⟨(p.1, p.1), rfl⟩, by fun_prop⟩
  have hr : r (b : Y × Y) = b := Subtype.ext (Prod.ext rfl b.property)
  have hrι : r.comp (ContinuousMap.subtypeVal (diagonal Y)) = ContinuousMap.id _ := by
    ext ⟨p, hp⟩
    · simp [r]
    · simpa [r] using hp
  -- `π_{n+2}(Y × Y, b)` is the product of two homotopy groups of `Y`.
  have hY' (y : Y) : Subsingleton (HomotopyGroup (Option (Fin (n + 1))) Y y) :=
    (HomotopyGroup.congrEquiv (finSuccEquiv (n + 1))).subsingleton_congr.1 (hY y n)
  have hYY : Subsingleton (HomotopyGroup (Option (Fin (n + 1))) (Y × Y) (b : Y × Y)) :=
    (HomotopyGroup.prodEquiv (b : Y × Y).1 (b : Y × Y).2).subsingleton_congr.2 inferInstance
  -- The absolute group of the pair is `π_{n+2}(Y × Y, b)` up to unfolding `TopPair.ofSubset`, so
  -- `hYY` is passed explicitly rather than found by instance search.
  exact RelHomotopyGroup.subsingleton_of_injective_of_surjective
    (Function.LeftInverse.injective (g := HomotopyGroup.map r hr)
      (HomotopyGroup.map_map_of_comp_eq_id r _ rfl hr hrι))
    (@Function.surjective_to_subsingleton _ _ _ hYY _)

/-- Two maps `X → Y` inducing the same homomorphism on `π₁(X, x₀)` induce the same homomorphism
on `π₁(univ, x₀)` after composing with `Subtype.val : univ → X`. -/
private theorem mapOfEq_comp_subtypeVal_univ_eq {X : Type u} [TopologicalSpace X]
    {f g : C(X, Y)} {x₀ : X} {y₀ : Y} (hf : f x₀ = y₀) (hg : g x₀ = y₀)
    (hfg : FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg) :
    FundamentalGroup.mapOfEq (f.comp ⟨Subtype.val, continuous_subtypeVal⟩ : C((univ : Set X), Y))
      (x := ⟨x₀, trivial⟩) hf =
      FundamentalGroup.mapOfEq (g.comp ⟨Subtype.val, continuous_subtypeVal⟩) hg := by
  ext p
  rw [← FundamentalGroup.mapOfEq_comp f _ rfl hf, ← FundamentalGroup.mapOfEq_comp g _ rfl hg, hfg]

/-- Two maps `X → Y` whose composites with `Subtype.val : univ → X` are homotopic relative to
`x₀` are homotopic relative to `x₀`. -/
private theorem homotopicRel_singleton_of_comp_subtypeVal_univ {X : Type u} [TopologicalSpace X]
    {f g : C(X, Y)} {x₀ : X}
    (h : (f.comp ⟨Subtype.val, continuous_subtypeVal⟩ : C((univ : Set X), Y)).HomotopicRel
      (g.comp ⟨Subtype.val, continuous_subtypeVal⟩) {⟨x₀, trivial⟩}) :
    f.HomotopicRel g {x₀} := by
  let e' : C(X, univ) := ⟨fun x ↦ ⟨x, mem_univ x⟩, by fun_prop⟩
  have he : (⟨Subtype.val, continuous_subtypeVal⟩ : C((univ : Set X), X)).comp e' =
      ContinuousMap.id X := rfl
  have hpre : e' ⁻¹' {⟨x₀, trivial⟩} = {x₀} := by
    ext
    simp [e', Subtype.ext_iff]
  simpa only [ContinuousMap.comp_assoc, he, ContinuousMap.comp_id, hpre] using h.precomp e'

section RelCWComplex

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]

/-- Let `(C, D)` be a relative CW complex without cells of dimension `0` and `1`, and let `Y` be a
space whose homotopy groups vanish from degree `2` on, at every point. Then two maps `C → Y` that
agree on `D` are homotopic relative to `D`. -/
theorem homotopicRel_base_of_isEmpty_cell (h₀ : IsEmpty (cell C 0)) (h₁ : IsEmpty (cell C 1))
    (hY : ∀ (y : Y) (n : ℕ), Subsingleton (π_ (n + 2) Y y)) {f g : C(C, Y)}
    (hfg : ∀ x : C, (x : X) ∈ D → f x = g x) :
    f.HomotopicRel g {x : C | (x : X) ∈ D} := by
  -- Deform `(f, g)` into the diagonal relative to `D`, and project to either factor.
  obtain ⟨G, hG, hGΔ⟩ := exists_homotopicRel_range_subset_of_relHomotopyGroup
    (Y := TopCat.of (Y × Y)) (B := diagonal Y) (fun h ↦ (h₀.false h.some).elim)
    (fun n hn b ↦ by
      rcases n with _ | n
      · exact (h₁.false hn.some).elim
      · exact subsingleton_relHomotopyGroup_diagonal hY n b)
    (f.prodMk g) fun x hx ↦ hfg x hx
  have hG' : ContinuousMap.fst.comp G = ContinuousMap.snd.comp G := by
    ext x
    exact hGΔ ⟨x, rfl⟩
  have h₁ := hG.comp_continuousMap ContinuousMap.fst
  have h₂ := hG.comp_continuousMap ContinuousMap.snd
  have hf : ContinuousMap.fst.comp (f.prodMk g) = f := by ext; simp
  have hg : ContinuousMap.snd.comp (f.prodMk g) = g := by ext; simp
  rw [hf, hG'] at h₁
  rw [hg] at h₂
  exact h₁.trans h₂.symm

/-- Let `(C, D)` be a relative CW complex, and let `Y` be a space whose homotopy groups vanish from
degree `2` on, at every point. Let `f g : C → Y` be such that, for every path `γ` in `C` between
points of the `0`-skeleton `skeletonLT C 1`, the paths `f ∘ γ` and `g ∘ γ` are homotopic
relative to their endpoints. Then `f` and `g` are homotopic relative to the `0`-skeleton. -/
theorem homotopicRel_skeletonLT_one_of_forall_homotopicRel
    (hY : ∀ (y : Y) (n : ℕ), Subsingleton (π_ (n + 2) Y y)) {f g : C(C, Y)}
    (hfg : ∀ γ : C(I, C), (γ 0 : X) ∈ skeletonLT C 1 → (γ 1 : X) ∈ skeletonLT C 1 →
      (f.comp γ).HomotopicRel (g.comp γ) {0, 1}) :
    f.HomotopicRel g {x : C | (x : X) ∈ skeletonLT C 1} := by
  -- The interval as the closed unit ball of `Fin 1 → ℝ`, by `t ↦ 2 * t - 1`.
  let e : I ≃ₜ closedBall (0 : Fin 1 → ℝ) 1 :=
    (Homeomorph.funUnique (Fin 1) I).symm.trans (cubeHomeomorphClosedBall (Fin 1))
  have he (t : I) : (e t : Fin 1 → ℝ) ∈ sphere 0 1 ↔ t = 0 ∨ t = 1 := by
    rw [mem_sphere_zero_iff_norm, Homeomorph.trans_apply, norm_cubeHomeomorphClosedBall_eq_one_iff]
    simp [Cube.boundary]
  -- Through the characteristic map, each `1`-cell is a path between points of the `0`-skeleton.
  have hcell (j : cell C 1) : (f.comp (cellMap j)).HomotopicRel (g.comp (cellMap j))
      {y | (y : Fin 1 → ℝ) ∈ sphere 0 1} := by
    have hγ (t : I) (ht : t = 0 ∨ t = 1) : ((cellMap j (e t) : C) : X) ∈ skeletonLT C 1 :=
      cellFrontier_subset_skeletonLT 1 j
        ⟨e t, (he t).2 ht, (coe_cellMap_apply j _).symm⟩
    have h := (hfg ((cellMap j).comp e) (hγ 0 (Or.inl rfl)) (hγ 1 (Or.inr rfl))).precomp
      (e.symm : C(closedBall (0 : Fin 1 → ℝ) 1, I))
    have hΦ : ((cellMap j).comp (e : C(I, closedBall (0 : Fin 1 → ℝ) 1))).comp
        (e.symm : C(closedBall (0 : Fin 1 → ℝ) 1, I)) = cellMap j := by
      ext y
      simp
    simp only [ContinuousMap.comp_assoc, hΦ] at h
    refine h.mono fun y hy ↦ (he _).1 ?_
    simpa using hy
  -- Homotope `f`, relative to the `0`-skeleton, to agree with `g` on every `1`-cell.
  obtain ⟨f₁, hff₁, hf₁⟩ := exists_homotopicRel_cellMap 1 f (fun j ↦ g.comp (cellMap j)) hcell
  -- `f₁` agrees with `g` on the `1`-skeleton, and `C` has no cells of dimension `0` or `1`
  -- relative to its `1`-skeleton.
  let E := skeletonLT C 2
  have hf₁g : ∀ x : C, (x : X) ∈ E → f₁ x = g x := by
    have h : MapsTo (f₁.prodMk g) {x : C | (x : X) ∈ skeletonLT C ((1 + 1 : ℕ) : ℕ∞)}
        (diagonal Y) := by
      refine mapsTo_skeletonLT_succ_iff.2 ⟨fun x hx ↦ ?_, fun j y ↦ hf₁ j y⟩
      simp only [mem_diagonal_iff, ContinuousMap.prod_eval]
      rw [← hff₁.fst_eq_snd hx]
      exact (hfg (.const I x) hx hx).fst_eq_snd (Or.inl rfl)
    exact fun x hx ↦ h hx
  have hE (n : ℕ) (hn : n < 2) : IsEmpty (@cell X _ C E E.relCWComplex n) := by
    refine ⟨fun i ↦ (E.relCWComplexCellEquiv n i).property ?_⟩
    simp only [E, skeletonLT_I, mem_ofPred_eq]
    exact_mod_cast hn
  -- The structure relative to `E` is not an instance: `C` already carries one relative to `D`.
  have h := @homotopicRel_base_of_isEmpty_cell Y _ X _ _ C E E.relCWComplex (hE 0 two_pos)
    (hE 1 one_lt_two) hY f₁ g hf₁g
  exact hff₁.trans (h.mono fun x hx ↦ skeletonLT_mono (by norm_num) hx)

/-- **Maps into a space without higher homotopy are determined by their effect on `π₁`.** Let `C`
be a relative CW complex whose `0`-skeleton is a single point `x₀`, such as a CW complex with a
single `0`-cell, and let `Y` be a space whose homotopy groups vanish from degree `2` on, at every
point, such as a `K(H, 1)`. Two maps `C → Y` sending `x₀` to `y₀` and inducing the same
homomorphism `π₁(C, x₀) → π₁(Y, y₀)` are homotopic relative to `x₀`. -/
theorem homotopicRel_singleton_of_mapOfEq_eq
    (hY : ∀ (y : Y) (n : ℕ), Subsingleton (π_ (n + 2) Y y)) {x₀ : C}
    (hx₀ : {x : C | (x : X) ∈ skeletonLT C 1} = {x₀}) {f g : C(C, Y)} {y₀ : Y}
    (hf : f x₀ = y₀) (hg : g x₀ = y₀)
    (hfg : FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg) :
    f.HomotopicRel g {x₀} := by
  rw [← hx₀]
  refine homotopicRel_skeletonLT_one_of_forall_homotopicRel hY fun γ h₀ h₁ ↦ ?_
  -- A path between points of the `0`-skeleton is a loop at `x₀`.
  have h₀' : γ 0 = x₀ := by
    rw [← mem_singleton_iff, ← hx₀]
    exact h₀
  have h₁' : γ 1 = x₀ := by
    rw [← mem_singleton_iff, ← hx₀]
    exact h₁
  let p : Path x₀ x₀ := ⟨γ, h₀', h₁'⟩
  have h := congrArg CategoryTheory.End.asHom <|
    DFunLike.congr_fun hfg (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))
  simp only [FundamentalGroup.mapOfEq_apply] at h
  -- A homotopy of paths is a homotopy relative to `{0, 1}` of the underlying maps `f ∘ γ` and
  -- `g ∘ γ`; the casts along `hf` and `hg` only change the endpoint proofs.
  obtain ⟨H⟩ := Path.Homotopic.Quotient.exact h
  exact ⟨H⟩

/-- **Maps into a space without higher homotopy are determined by their effect on `π₁`**, for a
CW structure on the whole space. Let `X` be a CW complex whose `0`-skeleton is a single point
`x₀`, such as a CW complex with a single `0`-cell, and let `Y` be a space whose homotopy groups
vanish from degree `2` on, at every point. Two maps `X → Y` sending `x₀` to `y₀` and inducing the
same homomorphism `π₁(X, x₀) → π₁(Y, y₀)` are homotopic relative to `x₀`. -/
theorem homotopicRel_singleton_of_mapOfEq_eq_of_cwComplex [CWComplex (univ : Set X)]
    (hY : ∀ (y : Y) (n : ℕ), Subsingleton (π_ (n + 2) Y y)) {x₀ : X}
    (hx₀ : (skeletonLT (univ : Set X) 1 : Set X) = {x₀}) {f g : C(X, Y)} {y₀ : Y}
    (hf : f x₀ = y₀) (hg : g x₀ = y₀)
    (hfg : FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg) :
    f.HomotopicRel g {x₀} :=
  -- Apply `homotopicRel_singleton_of_mapOfEq_eq` to `univ`, through `Subtype.val`.
  homotopicRel_singleton_of_comp_subtypeVal_univ <|
    homotopicRel_singleton_of_mapOfEq_eq (C := (univ : Set X)) hY (x₀ := ⟨x₀, trivial⟩)
      (by ext x; simp [← SetLike.mem_coe, hx₀, Subtype.ext_iff]) hf hg
      (mapOfEq_comp_subtypeVal_univ_eq hf hg hfg)

end RelCWComplex

section Vertex

/-! ### An arbitrary `0`-cell as base point -/

open CategoryTheory

variable {Z : Type*} [TopologicalSpace Z]

/-- Let `α` be a path from `x₀` to `v`, and let `g x₀ = f x₀`. A path `q` from `g v` running
through the points of `(g ∘ α)⁻¹ · (f ∘ α)` has, in the fundamental groupoid, the class of that
composite, read along the equality of its end point with `f v`. -/
private theorem mk_eq_inv_comp_of_apply_eq {f g : C(Z, Y)} {x₀ v : Z} (hg : g x₀ = f x₀)
    (α : Path x₀ v) {y : Y} (q : Path (g v) y) (hy : y = f v)
    (hq : ∀ t, q t = ((α.map g.continuous).symm.trans ((α.map f.continuous).cast hg rfl)) t) :
    (Path.Homotopic.Quotient.mk q : FundamentalGroupoid.mk (g v) ⟶ FundamentalGroupoid.mk y) =
      inv (Path.Homotopic.Quotient.mk (α.map g.continuous) :
        FundamentalGroupoid.mk (g x₀) ⟶ FundamentalGroupoid.mk (g v)) ≫
      eqToHom congr(FundamentalGroupoid.mk $hg) ≫
      (Path.Homotopic.Quotient.mk (α.map f.continuous) :
        FundamentalGroupoid.mk (f x₀) ⟶ FundamentalGroupoid.mk (f v)) ≫
      eqToHom congr(FundamentalGroupoid.mk $(hy.symm)) := by
  subst hy
  obtain rfl := Path.ext (funext hq)
  rw [Path.Homotopic.Quotient.mk_trans, ← FundamentalGroupoid.comp_eq,
    Path.Homotopic.Quotient.mk_cast, ← FundamentalGroupoid.conj_eqToHom,
    Path.Homotopic.Quotient.mk_symm]
  simp only [eqToHom_refl, Category.comp_id, ← Groupoid.inv_eq_inv]
  -- The inverse in Mathlib's fundamental groupoid is defined as the reversal of path classes.
  rfl

/-- Let `G` be a homotopy from `g` to `f'`, and let `f` be a map with `g x₀ = f x₀` inducing the
same homomorphism as `g` on `π₁(Z, x₀)`. If at the two ends `a` and `b` of a path `p` the trace of
`G` is the path `(g ∘ α)⁻¹ · (f ∘ α)` for a path `α` from `x₀`, then `f ∘ p` and `f' ∘ p` are
homotopic relative to their endpoints. -/
private theorem homotopicRel_comp_of_apply_eq_trans {f g f' : C(Z, Y)} {x₀ a b : Z}
    (hg : g x₀ = f x₀) (hfg : FundamentalGroup.mapOfEq f rfl = FundamentalGroup.mapOfEq g hg)
    (G : g.Homotopy f') (α₀ : Path x₀ a) (α₁ : Path x₀ b)
    (h₀ : ∀ t, G (t, a) = ((α₀.map g.continuous).symm.trans ((α₀.map f.continuous).cast hg rfl)) t)
    (h₁ : ∀ t, G (t, b) = ((α₁.map g.continuous).symm.trans ((α₁.map f.continuous).cast hg rfl)) t)
    (p : Path a b) :
    (f.comp p.toContinuousMap).HomotopicRel (f'.comp p.toContinuousMap) {0, 1} := by
  have ha : f' a = f a := by rw [← G.apply_one, h₀, Path.target]
  have hb : f' b = f b := by rw [← G.apply_one, h₁, Path.target]
  -- The square of `G` over `p`, solved for the image of `p` under `f'`.
  have hN := (FundamentalGroupoidFunctor.homotopicMapsNatIso G).naturality
    (Path.Homotopic.Quotient.mk p : FundamentalGroupoid.mk a ⟶ _)
  simp only [FundamentalGroupoidFunctor.homotopicMapsNatIso_app, FundamentalGroupoid.map_map,
    ← Path.Homotopic.Quotient.mk_map] at hN
  have hN' : inv (X := FundamentalGroupoid.mk (g a)) (Y := FundamentalGroupoid.mk (f' a))
        (Path.Homotopic.Quotient.mk (G.evalAt a)) ≫
      (Path.Homotopic.Quotient.mk (p.map g.continuous) :
        FundamentalGroupoid.mk (g a) ⟶ FundamentalGroupoid.mk (g b)) ≫
      (Path.Homotopic.Quotient.mk (G.evalAt b) :
        FundamentalGroupoid.mk (g b) ⟶ FundamentalGroupoid.mk (f' b)) =
      (Path.Homotopic.Quotient.mk (p.map f'.continuous) :
        FundamentalGroupoid.mk (f' a) ⟶ FundamentalGroupoid.mk (f' b)) := by
    rw [IsIso.inv_comp_eq]
    exact hN
  have key : (Path.Homotopic.Quotient.mk (p.map f.continuous) :
        FundamentalGroupoid.mk (f a) ⟶ FundamentalGroupoid.mk (f b)) =
      eqToHom congr(FundamentalGroupoid.mk $(ha.symm)) ≫
      (Path.Homotopic.Quotient.mk (p.map f'.continuous) :
        FundamentalGroupoid.mk (f' a) ⟶ FundamentalGroupoid.mk (f' b)) ≫
      eqToHom congr(FundamentalGroupoid.mk $hb) := by
    have hL := FundamentalGroup.mk_map_comp_eq_of_mapOfEq_eq hg hfg α₀ p α₁
    simp only [Category.assoc] at hL
    rw [← hN', mk_eq_inv_comp_of_apply_eq hg α₀ _ ha h₀, mk_eq_inv_comp_of_apply_eq hg α₁ _ hb h₁]
    simp [← reassoc_of% hL]
  rw [FundamentalGroupoid.conj_eqToHom ha.symm hb.symm, ← Path.Homotopic.Quotient.mk_cast] at key
  -- A homotopy of paths is a homotopy relative to `{0, 1}` of the underlying maps.
  obtain ⟨H⟩ := Path.Homotopic.Quotient.exact key
  exact ⟨H⟩

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

/-- **Maps into a space without higher homotopy are determined by their effect on `π₁`**, at a
`0`-cell. Let `C` be a path-connected CW complex with a base point `x₀` in its `0`-skeleton, and
let `Y` be a space whose homotopy groups vanish from degree `2` on, at every point, such as a
`K(H, 1)`. Two maps `C → Y` sending `x₀` to `y₀` and inducing the same homomorphism
`π₁(C, x₀) → π₁(Y, y₀)` are homotopic relative to `x₀`. -/
theorem homotopicRel_singleton_of_mapOfEq_eq_of_mem_skeletonLT [PathConnectedSpace C]
    (hY : ∀ (y : Y) (n : ℕ), Subsingleton (π_ (n + 2) Y y)) {x₀ : C}
    (hx₀ : (x₀ : X) ∈ skeletonLT C 1) {f g : C(C, Y)} {y₀ : Y}
    (hf : f x₀ = y₀) (hg : g x₀ = y₀)
    (hfg : FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg) :
    f.HomotopicRel g {x₀} := by
  classical
  subst hf
  -- `A` is the `0`-skeleton, a discrete subspace with the homotopy extension property.
  let A : Set C := Subtype.val ⁻¹' (skeletonLT C ((1 : ℕ) : ℕ∞) : Set X)
  have hA : HasHomotopyExtensionProperty A := hasHomotopyExtensionProperty_skeletonLT 1
  have : DiscreteTopology A := by
    let e : A → skeletonLT C ((1 : ℕ) : ℕ∞) := fun v ↦ ⟨v.val.val, v.property⟩
    have h : IsEmbedding ((Subtype.val : C → X) ∘ (Subtype.val : A → C)) :=
      IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
    exact (IsEmbedding.of_comp (f := e) (g := Subtype.val) (by fun_prop) continuous_subtypeVal
      h).discreteTopology
  have hx₀A : x₀ ∈ A := by simpa [A] using hx₀
  -- A path `α v` from `x₀` to every point `v`, constant at `x₀` itself, and the path
  -- `K v = (g ∘ α v)⁻¹ · (f ∘ α v)` from `g v` to `f v`, constant at `x₀`.
  let α (v : C) : Path x₀ v :=
    if h : v = x₀ then (Path.refl x₀).cast rfl h else PathConnectedSpace.somePath x₀ v
  let K (v : C) : Path (g v) (f v) :=
    ((α v).map g.continuous).symm.trans (((α v).map f.continuous).cast hg rfl)
  have hK₀ (t : I) : K x₀ t = g x₀ := by
    simp only [K, α, dite_true, Path.trans_apply]
    split_ifs <;> simp [hg]
  -- Extend the homotopy `v ↦ K v` on the `0`-skeleton to a homotopy `G` from `g` to `f'`; then
  -- `f'` agrees with `f` on the `0`-skeleton, and `G` is stationary at `x₀`.
  let H : (g.restrict A).Homotopy (f.restrict A) :=
    { toFun := fun p ↦ K p.2 p.1
      continuous_toFun := continuous_prod_of_discrete_right.2 fun v ↦ (K v).continuous
      map_zero_left := fun v ↦ (K v).source
      map_one_left := fun v ↦ (K v).target }
  obtain ⟨f', G, hG⟩ := hA.exists_homotopy_of_restrict hA.isClosed g H
  have hGK (v : C) (hv : v ∈ A) (t : I) : G (t, v) = K v t := hG t ⟨v, hv⟩
  have h₁ : g.HomotopicRel f' {x₀} :=
    ⟨{ toHomotopy := G, prop' := fun t x hx ↦ by
        obtain rfl : x = x₀ := hx
        exact (hGK x hx₀A t).trans (hK₀ t) }⟩
  -- On every path between points of the `0`-skeleton, `f` and `f'` agree up to homotopy.
  refine ((homotopicRel_skeletonLT_one_of_forall_homotopicRel hY (g := f')
    fun γ ha hb ↦ ?_).mono ?_).trans h₁.symm
  · exact homotopicRel_comp_of_apply_eq_trans hg hfg G (α _) (α _)
      (hGK _ (by simpa [A] using ha)) (hGK _ (by simpa [A] using hb)) ⟨γ, rfl, rfl⟩
  · simpa [A] using hx₀A

/-- **Maps into a space without higher homotopy are determined by their effect on `π₁`**, at a
`0`-cell, for a CW structure on the whole space. Let `X` be a path-connected CW complex with a base
point `x₀` in its `0`-skeleton, and let `Y` be a space whose homotopy groups vanish from degree `2`
on, at every point. Two maps `X → Y` sending `x₀` to `y₀` and inducing the same homomorphism
`π₁(X, x₀) → π₁(Y, y₀)` are homotopic relative to `x₀`. -/
theorem homotopicRel_singleton_of_mapOfEq_eq_of_mem_skeletonLT_of_cwComplex
    [CWComplex (univ : Set X)] [PathConnectedSpace X]
    (hY : ∀ (y : Y) (n : ℕ), Subsingleton (π_ (n + 2) Y y)) {x₀ : X}
    (hx₀ : x₀ ∈ skeletonLT (univ : Set X) 1) {f g : C(X, Y)} {y₀ : Y}
    (hf : f x₀ = y₀) (hg : g x₀ = y₀)
    (hfg : FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg) :
    f.HomotopicRel g {x₀} := by
  -- Apply `homotopicRel_singleton_of_mapOfEq_eq_of_mem_skeletonLT` to `univ`, through
  -- `Subtype.val`.
  have : PathConnectedSpace (univ : Set X) :=
    isPathConnected_iff_pathConnectedSpace.1 isPathConnected_univ
  exact homotopicRel_singleton_of_comp_subtypeVal_univ <|
    homotopicRel_singleton_of_mapOfEq_eq_of_mem_skeletonLT (C := (univ : Set X)) hY
      (x₀ := ⟨x₀, trivial⟩) hx₀ hf hg (mapOfEq_comp_subtypeVal_univ_eq hf hg hfg)

end Vertex

end TauCeti

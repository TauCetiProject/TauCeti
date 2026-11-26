/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Basic
public import TauCeti.Topology.Instances.AddCircle.UnitInterval
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.UniformSpace.CompactConvergence
import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.On
import TauCeti.Topology.Homotopy.Path

/-!
# Maps from the circle into a simply connected space are null-homotopic

A continuous map `f : AddCircle p → X` (with `0 < p`) is read as the based loop
`t ↦ f (t * p)` on the unit interval. When `X` is simply connected this loop is homotopic to the
constant loop relative to its endpoints, and such a homotopy descends along the quotient map
`I × I → I × AddCircle p`, `(s, t) ↦ (s, t * p)` (built from `AddCircle.ofUnitInterval`),
because it is constant on the two ends `t = 0` and `t = 1`, which are the only points
identified. The descended map is a free null-homotopy of `f`
(`ContinuousMap.nullhomotopic_addCircle_of_simplyConnectedSpace`).

The same descent shows more generally that `f` is null-homotopic exactly when its based loop is
homotopic to the constant loop (`ContinuousMap.nullhomotopic_iff_homotopic_refl`); for the
converse, a free null-homotopy of `f` collapses every loop in the circle, in particular the loop
`t ↦ t * p`. This translates statements about free loops into statements about based loops, to
which the path-homotopy machinery applies.

Mathlib's `SimplyConnectedSpace` is phrased with based paths; this file supplies its consequence
for free loops parametrised by the circle, which is how circles are compared in conditions such as
simple connectivity at infinity.

After rotating the circle, a continuous `p`-periodic curve `γ : ℝ → X` is contractible, as a map
`ℝ ⧸ pℤ → X`, exactly when the loop it traces over a period `[s, s + p]` (`Function.Periodic.loop`)
is null-homotopic (`Function.Periodic.exists_nullhomotopic_iff_loop_homotopic_refl`). Since that
loop only changes by a reparametrization, contractibility of a periodic curve survives a monotone
change of time that carries one period onto another
(`Function.Periodic.exists_nullhomotopic_comp_iff`).

Null-homotopy of a loop does not depend on its constant speed: a null-homotopic loop
`g : AddCircle T → X`, run at speed `a ≠ 0` (backwards when `a < 0`), is the null-homotopic loop
`t ↦ g (t * a)` on `AddCircle (T / |a|)` (`ContinuousMap.Nullhomotopic.exists_addCircle_comp_mul`).

In the other direction, the circle with one point removed contracts in the circle: lifting its
points to the open interval of length `p` above it, they move linearly to its midpoint
(`AddCircle.nullhomotopic_subtypeVal_compl_singleton`). So any subset of a torus on which every
coordinate avoids a point of its circle has nullhomotopic inclusion.

## Main declarations

* `ContinuousMap.toLoop`: a continuous map `f : C(AddCircle p, X)` read as a based loop at `f 0`
  via `AddCircle.ofUnitInterval p`.
* `ContinuousMap.nullhomotopic_iff_homotopic_refl`: a map from a circle `AddCircle p` with
  `0 < p` is null-homotopic exactly when its based loop `t ↦ f (t * p)` is homotopic to the
  constant loop.
* `ContinuousMap.nullhomotopic_addCircle_of_simplyConnectedSpace` and
  `ContinuousMap.isClopen_setOf_nullhomotopic_addCircle`: every continuous map from `AddCircle p`
  (`0 < p`) into a simply connected space is null-homotopic, and into a locally path-connected,
  semilocally simply connected space the null-homotopic maps form a clopen set in
  `C(AddCircle p, X)`.
* `Function.Periodic.loop`: the loop traced by a continuous periodic curve over one period.
* `Function.Periodic.exists_nullhomotopic_iff_loop_homotopic_refl`: a continuous periodic curve is
  contractible exactly when its loop over a period is null-homotopic.
* `Function.Periodic.exists_nullhomotopic_comp_iff`: contractibility of a periodic curve is
  unchanged by a monotone change of time.
* `ContinuousMap.Nullhomotopic.exists_addCircle_comp_mul`: a null-homotopic loop run at constant
  nonzero speed is null-homotopic.
* `IsPathConnected.exists_nullhomotopic_addCircle_of_periodic`: in a continuous family of
  `T`-periodic curves indexed by a path-connected set, if one curve is contractible as a map from
  `AddCircle T`, then every curve in the family is.
* `Function.Periodic.eventually_exists_nullhomotopic_addCircle_iff_of_tendstoUniformly`,
  `Function.Periodic.exists_nullhomotopic_addCircle_of_tendstoUniformly`, and
  `Function.Periodic.exists_nullhomotopic_addCircle_of_tendstoUniformly_Ioi`: uniform convergence
  (through an inducing map) eventually preserves circle null-homotopy of periodic curves, so uniform
  limits of contractible periodic curves are contractible.
* `AddCircle.nullhomotopic_subtypeVal_compl_singleton`: the circle with a point removed contracts
  in the circle.
-/

public section

noncomputable section

open Filter Function Set Topology
open scoped unitInterval

namespace ContinuousMap

variable {p : ℝ} {X : Type*} [TopologicalSpace X]

/-- A continuous map from the circle `AddCircle p` read as a based loop at `f 0` via
`AddCircle.ofUnitInterval p`. -/
def toLoop (f : C(AddCircle p, X)) : Path (f 0) (f 0) where
  toContinuousMap := f.comp (AddCircle.ofUnitInterval p)
  source' := by simp
  target' := by simp [AddCircle.coe_period]

/-- Evaluation of `f.toLoop` at `t ∈ [0, 1]`. -/
@[simp]
theorem toLoop_apply (f : C(AddCircle p, X)) (t : I) :
    f.toLoop t = f (((t : ℝ) * p : ℝ) : AddCircle p) := by
  simp [toLoop]

/-- **A circle map is null-homotopic exactly when its based loop is.** Let `γ` be the based loop
`t ↦ f (t * p)` of `f : AddCircle p → X`, `0 < p`. A homotopy of `γ` to the constant loop relative
to its endpoints descends to a free null-homotopy of `f`; conversely, a free null-homotopy of `f`
collapses the loop `t ↦ t * p` of the circle, and with it `γ`. -/
theorem nullhomotopic_iff_homotopic_refl [Fact (0 < p)] (f : C(AddCircle p, X)) {x : X}
    (γ : Path x x) (hγ : ∀ t : I, γ t = f (AddCircle.ofUnitInterval p t)) :
    f.Nullhomotopic ↔ γ.Homotopic (Path.refl x) := by
  have hx : f 0 = x := by rw [← γ.source, hγ, AddCircle.ofUnitInterval_zero]
  subst hx
  refine ⟨fun hf ↦ ?_, fun ⟨F⟩ ↦ ?_⟩
  · -- The loop `t ↦ t * p` of the circle, mapped by `f`, is `γ`.
    let ℓ : Path (0 : AddCircle p) 0 :=
      ⟨AddCircle.ofUnitInterval p, AddCircle.ofUnitInterval_zero, AddCircle.ofUnitInterval_one⟩
    have hℓ : ℓ.map f.continuous = γ := by
      ext t
      exact (hγ t).symm
    exact hℓ ▸ Path.Homotopic.map_nullhomotopic_of_nullhomotopic hf ℓ
  -- Descend the path homotopy `F` along `(s, t) ↦ (s, t * p)`, which only glues the two ends of
  -- the loop parameter, where `F` takes the value `f 0`.
  let q : C(I × I, I × AddCircle p) := (ContinuousMap.id I).prodMap (AddCircle.ofUnitInterval p)
  have hsurj : Function.Surjective q :=
    Function.surjective_id.prodMap AddCircle.surjective_ofUnitInterval
  have hq : IsQuotientMap q := q.continuous.isClosedMap.isQuotientMap q.continuous hsurj
  have hF : Function.FactorsThrough (F.toContinuousMap : I × I → X) q := by
    rintro ⟨s, t⟩ ⟨s', t'⟩ h
    obtain ⟨rfl, h⟩ := Prod.ext_iff.1 h
    obtain rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := AddCircle.ofUnitInterval_eq_ofUnitInterval_iff.1 h
    · rfl
    · exact (F.source s).trans (F.target s).symm
    · exact (F.target s).trans (F.source s).symm
  have hG (s t : I) : hq.lift F.toContinuousMap hF (s, AddCircle.ofUnitInterval p t) = F (s, t) :=
    DFunLike.congr_fun (hq.lift_comp F.toContinuousMap hF) (s, t)
  refine ⟨f 0, ⟨⟨hq.lift F.toContinuousMap hF, fun θ => ?_, fun θ => ?_⟩⟩⟩ <;>
    obtain ⟨t, rfl⟩ := AddCircle.surjective_ofUnitInterval (p := p) θ
  · exact (hG 0 t).trans ((F.apply_zero t).trans (hγ t))
  · exact (hG 1 t).trans (F.apply_one t)

/-- **Every map from a circle into a simply connected space is null-homotopic.** -/
theorem nullhomotopic_addCircle_of_simplyConnectedSpace [Fact (0 < p)] [SimplyConnectedSpace X]
    (f : C(AddCircle p, X)) : f.Nullhomotopic :=
  (f.nullhomotopic_iff_homotopic_refl (toLoop f) fun _ ↦ rfl).2
    (SimplyConnectedSpace.paths_homotopic _ _)

/-- **Null-homotopic circle maps form a clopen subset of `C(AddCircle p, X)`.** In a locally
path-connected, semilocally simply connected space `X`, the subset of null-homotopic maps in
`C(AddCircle p, X)` (`0 < p`) is both open and closed in the compact-open topology. -/
theorem isClopen_setOf_nullhomotopic_addCircle [Fact (0 < p)] [LocallyPathConnectedSpace X]
    [TauCeti.SemilocallySimplyConnectedSpace X] :
    IsClopen {g : C(AddCircle p, X) | g.Nullhomotopic} := by
  have hEq : {g : C(AddCircle p, X) | g.Nullhomotopic} =
      {g : C(AddCircle p, X) | g.toLoop.Homotopic (Path.refl (g 0))} :=
    Set.ext fun g ↦ g.nullhomotopic_iff_homotopic_refl g.toLoop fun _ ↦ rfl
  rw [hEq]
  exact TauCeti.isClopen_setOf_homotopic_refl toLoop <|
    continuous_eval.comp (continuous_fst.prodMk
      ((AddCircle.ofUnitInterval p).continuous.comp continuous_snd))

/-- **Constant-speed reparametrization of a null-homotopic loop.** If the loop
`g : AddCircle T → X` is null-homotopic and `a ≠ 0`, then `t ↦ g (t * a)`, a loop of period
`T / |a|` run backwards when `a < 0`, is null-homotopic. -/
theorem Nullhomotopic.exists_addCircle_comp_mul {T a : ℝ} (hT : T ≠ 0) (ha : a ≠ 0)
    {g : C(AddCircle T, X)} (hg : g.Nullhomotopic) :
    ∃ g' : C(AddCircle (T / |a|), X), g'.Nullhomotopic ∧
      ∀ t : ℝ, g' t = g ((t * a : ℝ) : AddCircle T) := by
  -- The reparametrization `ℝ/(T/|a|)ℤ → ℝ/Tℤ`, multiplication by `|a|`.
  let e : C(AddCircle (T / |a|), AddCircle T) :=
    ⟨_, (AddCircle.homeomorphAddCircle (T / |a|) T (div_ne_zero hT (abs_ne_zero.2 ha))
      hT).continuous⟩
  have he (t : ℝ) : e t = ((t * |a| : ℝ) : AddCircle T) := by
    rw [coe_mk, AddCircle.homeomorphAddCircle_apply_mk, inv_div,
      div_mul_cancel₀ _ hT]
  rcases ha.lt_or_gt with ha' | ha'
  · -- Backwards: compose further with the reflection of the circle.
    let n : C(AddCircle T, AddCircle T) := ⟨Neg.neg, continuous_neg⟩
    have hn (x : AddCircle T) : n x = -x := rfl
    refine ⟨g.comp (n.comp e), hg.comp_left _, fun t ↦ ?_⟩
    rw [comp_apply, comp_apply, he, hn, ← AddCircle.coe_neg,
      abs_of_neg ha', mul_neg, neg_neg]
  · refine ⟨g.comp e, hg.comp_left _, fun t ↦ ?_⟩
    rw [comp_apply, he, abs_of_pos ha']

end ContinuousMap

namespace Function.Periodic

variable {p : ℝ} {X : Type*} [TopologicalSpace X] {γ : ℝ → X}

/-- The loop at `γ s` traced by a continuous `p`-periodic curve `γ` over the period `[s, s + p]`:
`t ↦ γ (s + t * p)` on the unit interval. -/
def loop (hp : Periodic γ p) (hγ : Continuous γ) (s : ℝ) : Path (γ s) (γ s) where
  toFun t := γ (s + t * p)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp [hp s]

@[simp]
theorem loop_apply (hp : Periodic γ p) (hγ : Continuous γ) (s : ℝ) (t : I) :
    hp.loop hγ s t = γ (s + t * p) :=
  (rfl)

/-- **A periodic curve is contractible exactly when its loop over a period is.** For `0 < p`, the
map `ℝ ⧸ pℤ → X` induced by a continuous `p`-periodic curve `γ` is null-homotopic exactly when
the loop traced by `γ` over the period `[s, s + p]` is null-homotopic relative to its endpoints,
for any initial time `s`. -/
theorem exists_nullhomotopic_iff_loop_homotopic_refl [Fact (0 < p)] (hp : Periodic γ p)
    (hγ : Continuous γ) (s : ℝ) :
    (∃ g : C(AddCircle p, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ t) ↔
      (hp.loop hγ s).Homotopic (Path.refl (γ s)) := by
  -- Rotating the circle by `s` turns `g` into a map whose based loop is `hp.loop hγ s`.
  let r (u : ℝ) : C(AddCircle p, AddCircle p) :=
    ⟨(· + (u : AddCircle p)), continuous_id.add continuous_const⟩
  have hr (u : ℝ) (θ : AddCircle p) : r u θ = θ + u := rfl
  have hrot (g : C(AddCircle p, X)) : (g.comp (r s)).Nullhomotopic → g.Nullhomotopic := by
    intro h
    have hg : (g.comp (r s)).comp (r (-s)) = g := by
      ext θ
      simp [r]
    exact hg ▸ h.comp_left (r (-s))
  have key (g : C(AddCircle p, X)) (hg : ∀ t : ℝ, g t = γ t) :
      (g.comp (r s)).Nullhomotopic ↔ (hp.loop hγ s).Homotopic (Path.refl (γ s)) :=
    (g.comp (r s)).nullhomotopic_iff_homotopic_refl _ fun t ↦ by
      rw [loop_apply, ContinuousMap.comp_apply, hr, AddCircle.ofUnitInterval_apply,
        ← AddCircle.coe_add, hg, add_comm]
  constructor
  · rintro ⟨g, hg, hgγ⟩
    exact (key g hgγ).1 (hg.comp_left (r s))
  · intro h
    let g : C(AddCircle p, X) := ⟨hp.lift, hγ.quotient_liftOn' _⟩
    have hgγ (t : ℝ) : g t = γ t := hp.lift_coe t
    exact ⟨g, hrot g ((key g hgγ).2 h), hgγ⟩

/-- **Contractibility does not depend on a monotone change of time.** Let `γ` be a continuous
`p`-periodic curve, `0 < p`, and let `ψ` be continuous, monotone on `[0, T]`, with `ψ 0 = 0` and
`ψ T = p`, such that `γ ∘ ψ` is `T`-periodic, `0 < T`. Then `γ ∘ ψ` is contractible as a map
`ℝ ⧸ Tℤ → X` exactly when `γ` is contractible as a map `ℝ ⧸ pℤ → X`: over one period, the loop
of `γ ∘ ψ` is a reparametrization of the loop of `γ`. -/
theorem exists_nullhomotopic_comp_iff [Fact (0 < p)] (hp : Periodic γ p) (hγ : Continuous γ)
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) {T : ℝ} [Fact (0 < T)] (hψm : MonotoneOn ψ (Icc 0 T))
    (hψ0 : ψ 0 = 0) (hψT : ψ T = p) (hT : Periodic (γ ∘ ψ) T) :
    (∃ g : C(AddCircle T, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ (ψ t)) ↔
      ∃ g : C(AddCircle p, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ t := by
  have hp₀ : 0 < p := Fact.out
  have hT₀ : 0 < T := Fact.out
  -- The reparametrization `t ↦ ψ (t T) / p` of the unit interval.
  have hmem (t : I) : ψ (t * T) / p ∈ I := by
    have ht : (t : ℝ) * T ∈ Icc 0 T :=
      ⟨mul_nonneg t.property.1 hT₀.le, mul_le_of_le_one_left hT₀.le t.property.2⟩
    refine ⟨div_nonneg ?_ hp₀.le, (div_le_one hp₀).2 ?_⟩
    · exact hψ0 ▸ hψm ⟨le_rfl, hT₀.le⟩ ht ht.1
    · exact hψT ▸ hψm ht ⟨hT₀.le, le_rfl⟩ ht.2
  let f : I → I := fun t ↦ ⟨ψ (t * T) / p, hmem t⟩
  have hf : Continuous f := by fun_prop
  have hf₀ : f 0 = 0 := Subtype.ext (by simp [f, hψ0])
  have hf₁ : f 1 = 1 := Subtype.ext (by simp [f, hψT, hp₀.ne'])
  set ℓ := hp.loop hγ 0
  have hℓ : ℓ.Homotopic (ℓ.reparam f hf hf₀ hf₁) := ⟨Path.Homotopy.reparam ℓ f hf hf₀ hf₁⟩
  -- The reparametrized loop traces `γ ∘ ψ` over `[0, T]`.
  have hrep (g : C(AddCircle T, X)) (hg : ∀ t : ℝ, g t = γ (ψ t)) (t : I) :
      ℓ.reparam f hf hf₀ hf₁ t = g (AddCircle.ofUnitInterval T t) := by
    simp [ℓ, f, AddCircle.ofUnitInterval_apply, hg, div_mul_cancel₀ _ hp₀.ne']
  rw [hp.exists_nullhomotopic_iff_loop_homotopic_refl hγ 0]
  constructor
  · rintro ⟨g, hg, hgγ⟩
    exact hℓ.trans ((g.nullhomotopic_iff_homotopic_refl _ (hrep g hgγ)).1 hg)
  · intro h
    let g : C(AddCircle T, X) := ⟨hT.lift, (hγ.comp hψ).quotient_liftOn' _⟩
    have hgγ (t : ℝ) : g t = γ (ψ t) := hT.lift_coe t
    exact ⟨g, (g.nullhomotopic_iff_homotopic_refl _ (hrep g hgγ)).2 (hℓ.symm.trans h), hgγ⟩

end Function.Periodic

/-- **Null-homotopy of periodic curves propagates along a path-connected parameter set.** Let `U`
be a path-connected subset of `Y`, and let `u : Y × ℝ → X` be continuous on `U × ℝ` such that
`t ↦ u (y, t)` is `T`-periodic for every `y ∈ U`. If at some `y₀ ∈ U` the circle map induced by
`t ↦ u (y₀, t)` is null-homotopic, then so is the circle map induced by `t ↦ u (y, t)` for every
`y ∈ U`. -/
theorem IsPathConnected.exists_nullhomotopic_addCircle_of_periodic {Y X : Type*}
    [TopologicalSpace Y] [TopologicalSpace X] {U : Set Y} (hU : IsPathConnected U)
    {u : Y × ℝ → X} (hu : ContinuousOn u (U ×ˢ univ)) {T : ℝ}
    (hper : ∀ y ∈ U, Function.Periodic (fun t ↦ u (y, t)) T) {y₀ : Y} (hy₀ : y₀ ∈ U)
    (h₀ : ∃ g : C(AddCircle T, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (y₀, t))
    {y : Y} (hy : y ∈ U) :
    ∃ g : C(AddCircle T, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (y, t) := by
  obtain ⟨g₀, ⟨c, hc⟩, hg₀⟩ := h₀
  obtain ⟨γ, hγU⟩ := hU.joinedIn y hy y₀ hy₀
  -- Along the path `γ` in `U`, the `T`-periodic curves descend to a homotopy on `I × AddCircle T`.
  let F : I × AddCircle T → X := fun q ↦ (hper (γ q.1) (hγU q.1)).lift q.2
  have hFc : Continuous F := by
    rw [← (IsOpenQuotientMap.id.prodMap
      (QuotientAddGroup.isOpenQuotientMap_mk (N := AddSubgroup.zmultiples T))).continuous_comp_iff]
    have hcomp : F ∘ Prod.map id QuotientAddGroup.mk = fun q : I × ℝ ↦ u (γ q.1, q.2) :=
      funext fun q ↦ (hper (γ q.1) (hγU q.1)).lift_coe q.2
    rw [hcomp]
    exact hu.comp_continuous ((γ.continuous.comp continuous_fst).prodMk continuous_snd)
      fun q ↦ ⟨hγU q.1, mem_univ _⟩
  let g : C(AddCircle T, X) := ⟨fun θ ↦ F (0, θ), hFc.comp (continuous_const.prodMk continuous_id)⟩
  have hgg₀ : g.Homotopic g₀ := ⟨{
    toContinuousMap := ⟨F, hFc⟩
    map_zero_left := fun _ ↦ rfl
    map_one_left := fun θ ↦ by
      obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
      exact ((hper (γ 1) (hγU 1)).lift_coe t).trans (by rw [γ.target, ← hg₀ t]) }⟩
  refine ⟨g, ⟨c, hgg₀.trans hc⟩, fun t ↦ ?_⟩
  exact ((hper (γ 0) (hγU 0)).lift_coe t).trans (by rw [γ.source])

namespace Function.Periodic

/-- **Uniform convergence through an inducing map eventually preserves circle null-homotopy.** Let
`X` be locally path-connected and semilocally simply connected, and let `e : X → F` restrict to a
topological inducing map on `K ⊆ X` into a uniform space `F`. If `γ` is a continuous `T`-periodic
curve (`0 < T`) in `K` and eventually along `l` each `u i` is a continuous `T`-periodic curve in `K`
with `e ∘ u i → e ∘ γ` uniformly, then eventually `u i` descends to a null-homotopic map
`AddCircle T → X` if and only if `γ` does. -/
theorem eventually_exists_nullhomotopic_addCircle_iff_of_tendstoUniformly {T : ℝ} {X ι F : Type*}
    [TopologicalSpace X] [LocallyPathConnectedSpace X] [TauCeti.SemilocallySimplyConnectedSpace X]
    {l : Filter ι} [UniformSpace F] {K : Set X} {e : X → F} {γ : ℝ → X}
    (hγper : Periodic γ T) (hγc : Continuous γ) (hT : 0 < T)
    (he : IsInducing (K.domRestrict e)) {u : ι → ℝ → X}
    (huc : ∀ᶠ i in l, Continuous (u i)) (huper : ∀ᶠ i in l, Periodic (u i) T)
    (huK : ∀ᶠ i in l, ∀ t, u i t ∈ K) (hγK : ∀ t, γ t ∈ K)
    (hconv : TendstoUniformly (fun i t ↦ e (u i t)) (e ∘ γ) l) :
    ∀ᶠ i in l,
      (∃ g : C(AddCircle T, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u i t) ↔
        ∃ g : C(AddCircle T, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ t := by
  classical
  have : Fact (0 < T) := ⟨hT⟩
  -- On the space `L` of closed curves on `[0, 1]` in `X`, null-homotopy is clopen.
  let L := {f : C(I, X) // f 0 = f 1}
  let loopOf (f : L) : Path (f.val 0) (f.val 0) := ⟨f.val, rfl, f.property.symm⟩
  have hclopen : IsClopen {f : L | (loopOf f).Homotopic (Path.refl (f.val 0))} :=
    TauCeti.isClopen_setOf_homotopic_refl loopOf <|
      continuous_eval.comp ((continuous_subtypeVal.comp continuous_fst).prodMk continuous_snd)
  -- Lift the curves on `[0, T]` to `C(I, K)` so `he` transports uniform convergence from `F`.
  let kγ : C(I, K) := ⟨fun τ ↦ ⟨γ ((τ : ℝ) * T), hγK _⟩,
    Continuous.subtype_mk (hγc.comp (continuous_subtypeVal.mul continuous_const)) _⟩
  let mkKu (i : ι) (hi : Continuous (u i) ∧ Periodic (u i) T ∧ ∀ t, u i t ∈ K) : C(I, K) :=
    ⟨fun τ ↦ ⟨u i ((τ : ℝ) * T), hi.2.2 _⟩,
      Continuous.subtype_mk (hi.1.comp (continuous_subtypeVal.mul continuous_const)) _⟩
  let ku (i : ι) : C(I, K) := if hi : _ then mkKu i hi else kγ
  have hku_pos {i : ι} (hi) : ku i = mkKu i hi := dite_eq_left hi
  let eK : C(K, F) := ⟨K.domRestrict e, he.continuous⟩
  have hku : Tendsto ku l (𝓝 kγ) := by
    rw [(eK.isInducing_postcomp he).tendsto_nhds_iff, ContinuousMap.tendsto_iff_tendstoUniformly]
    refine (tendstoUniformly_congr ?_).1 (hconv.comp fun τ : I ↦ (τ : ℝ) * T)
    filter_upwards [huc, huper, huK] with i hi₁ hi₂ hi₃
    funext τ
    simp [hku_pos ⟨hi₁, hi₂, hi₃⟩, mkKu, eK]
  let inclK : C(K, X) := ⟨Subtype.val, continuous_subtypeVal⟩
  have hfγ01 : (inclK.comp kγ) 0 = (inclK.comp kγ) 1 := by simpa [inclK, kγ] using (hγper 0).symm
  have hfu01 (i : ι) : (inclK.comp (ku i)) 0 = (inclK.comp (ku i)) 1 := by
    by_cases hi : Continuous (u i) ∧ Periodic (u i) T ∧ ∀ t, u i t ∈ K
    · simpa [inclK, hku_pos hi, mkKu] using (hi.2.1 0).symm
    · simpa only [ku, dite_eq_right hi] using hfγ01
  let fγ : L := ⟨inclK.comp kγ, hfγ01⟩
  let fu (i : ι) : L := ⟨inclK.comp (ku i), hfu01 i⟩
  have hfu : Tendsto fu l (𝓝 fγ) :=
    tendsto_subtype_rng.2 ((inclK.continuous_postcomp.tendsto kγ).comp hku)
  have hev : ∀ᶠ i in l,
      (loopOf (fu i)).Homotopic (Path.refl ((fu i).val 0)) ↔
        (loopOf fγ).Homotopic (Path.refl (fγ.val 0)) := by
    by_cases h : fγ ∈ {f : L | (loopOf f).Homotopic (Path.refl (f.val 0))}
    · exact (hfu.eventually (hclopen.isOpen.mem_nhds h)).mono fun _ hi ↦ iff_of_true hi h
    · exact (hfu.eventually (hclopen.compl.isOpen.mem_nhds h)).mono fun _ hi ↦ iff_of_false hi h
  have hiff_loop {δ : ℝ → X} (hδp : Periodic δ T) (hδc : Continuous δ) (f : L)
      (hf : ∀ τ : I, f.val τ = δ ((τ : ℝ) * T)) :
      (∃ g : C(AddCircle T, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = δ t) ↔
        (loopOf f).Homotopic (Path.refl (f.val 0)) := by
    refine ⟨fun ⟨g, hg, hgδ⟩ ↦ (g.nullhomotopic_iff_homotopic_refl (loopOf f) fun τ ↦ by
      simp [loopOf, hf τ, AddCircle.ofUnitInterval_apply, hgδ]).1 hg, fun h ↦ ?_⟩
    let gδ : C(AddCircle T, X) := ⟨hδp.lift, hδc.quotient_liftOn' _⟩
    have hgδ (t : ℝ) : gδ t = δ t := hδp.lift_coe t
    exact ⟨gδ, (gδ.nullhomotopic_iff_homotopic_refl (loopOf f) fun τ ↦ by
      simp [loopOf, hf τ, AddCircle.ofUnitInterval_apply, hgδ]).2 h, hgδ⟩
  filter_upwards [huc, huper, huK, hev] with i hi₁ hi₂ hi₃ h_eq
  exact (hiff_loop hi₂ hi₁ (fu i) fun τ ↦ by simp [fu, hku_pos ⟨hi₁, hi₂, hi₃⟩, mkKu, inclK]).trans
    (h_eq.trans (hiff_loop hγper hγc fγ fun _ ↦ rfl).symm)

/-- **Uniform limits of contractible periodic curves are contractible.** Let `X` be locally
path-connected and semilocally simply connected, and let `e : X → F` restrict to a topological
inducing map on `K ⊆ X` into a uniform space `F`. If `γ` is a continuous `T`-periodic curve
(`0 < T`) in `K`, eventually along `l` each `u i` is a continuous `T`-periodic curve in `K` with
`e ∘ u i → e ∘ γ` uniformly, and frequently the circle map of `u i` is null-homotopic, then the
circle map of `γ` is null-homotopic. -/
theorem exists_nullhomotopic_addCircle_of_tendstoUniformly {T : ℝ} {X ι F : Type*}
    [TopologicalSpace X] [LocallyPathConnectedSpace X] [TauCeti.SemilocallySimplyConnectedSpace X]
    {l : Filter ι} [UniformSpace F] {K : Set X} {e : X → F} {γ : ℝ → X}
    (hγper : Periodic γ T) (hγc : Continuous γ) (hT : 0 < T)
    (he : IsInducing (K.domRestrict e)) {u : ι → ℝ → X}
    (huc : ∀ᶠ i in l, Continuous (u i)) (huper : ∀ᶠ i in l, Periodic (u i) T)
    (huK : ∀ᶠ i in l, ∀ t, u i t ∈ K) (hγK : ∀ t, γ t ∈ K)
    (hconv : TendstoUniformly (fun i t ↦ e (u i t)) (e ∘ γ) l)
    (hnull : ∃ᶠ i in l, ∃ g : C(AddCircle T, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u i t) :
    ∃ g : C(AddCircle T, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ t := by
  obtain ⟨_, hnull_i, hiff⟩ := (hnull.and_eventually
    (hγper.eventually_exists_nullhomotopic_addCircle_iff_of_tendstoUniformly hγc hT he huc huper
      huK hγK hconv)).exists
  exact hiff.1 hnull_i

/-- **Uniform slice limits along a half-cylinder with a contractible slice are contractible.** Let
`X` be locally path-connected and semilocally simply connected, and let `u : ℝ × ℝ → X` be
continuous on `(a, ∞) × ℝ`, with `T`-periodic slices (`0 < T`) in a compact set `K` on which a
continuous map `e : X → F` into a Hausdorff uniform space is injective. If some slice `s > a` is
contractible on `AddCircle T`, then any continuous `T`-periodic curve `γ` in `K` with
`e ∘ u(φ i, ·) → e ∘ γ` uniformly along a nontrivial `l` (`φ i > a` eventually) is contractible. -/
theorem exists_nullhomotopic_addCircle_of_tendstoUniformly_Ioi {T : ℝ} {X ι F : Type*}
    [TopologicalSpace X] [LocallyPathConnectedSpace X] [TauCeti.SemilocallySimplyConnectedSpace X]
    {l : Filter ι} [l.NeBot] [UniformSpace F] [T2Space F] {K : Set X} {e : X → F} {γ : ℝ → X}
    (hγper : Periodic γ T) (hγc : Continuous γ) (hT : 0 < T) (he : Continuous e)
    (hK : IsCompact K) (he_inj : InjOn e K) {a : ℝ} {u : ℝ × ℝ → X}
    (hu : ContinuousOn u (Ioi a ×ˢ univ)) (huper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) T)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (hnull : ∃ s > a, ∃ g : C(AddCircle T, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (s, t))
    {φ : ι → ℝ} (hφ : ∀ᶠ i in l, a < φ i) (hγK : ∀ t, γ t ∈ K)
    (hconv : TendstoUniformly (fun i t ↦ e (u (φ i, t))) (e ∘ γ) l) :
    ∃ g : C(AddCircle T, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ t := by
  obtain ⟨s₀, hs₀, h₀⟩ := hnull
  have := isCompact_iff_compactSpace.1 hK
  have hemb := (he.comp continuous_subtypeVal).isClosedEmbedding he_inj.injective
  exact hγper.exists_nullhomotopic_addCircle_of_tendstoUniformly hγc hT hemb.isInducing
    (hφ.mono fun _ hi ↦ hu.comp_continuous (continuous_const.prodMk continuous_id)
      fun t ↦ ⟨hi, mem_univ t⟩)
    (hφ.mono fun _ hi ↦ huper _ hi) (hφ.mono fun _ hi ↦ huK _ hi) hγK hconv
    (hφ.mono fun _ hi ↦ ((convex_Ioi a).isPathConnected ⟨s₀, hs₀⟩)
      |>.exists_nullhomotopic_addCircle_of_periodic hu huper hs₀ h₀ hi).frequently

end Function.Periodic

namespace AddCircle

variable {p : ℝ} [Fact (0 < p)]

/-- **The circle with a point removed contracts in the circle.** The inclusion of the complement
of a point `c` of `AddCircle p` is nullhomotopic: lifting to the interval `(a, a + p)` above it,
where `a` represents `c`, the points move linearly to the midpoint of that interval. -/
theorem nullhomotopic_subtypeVal_compl_singleton (c : AddCircle p) :
    (ContinuousMap.subtypeVal ({c}ᶜ : Set (AddCircle p))).Nullhomotopic := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
  have hL : Continuous fun x : ({(a : AddCircle p)}ᶜ : Set (AddCircle p)) ↦
      (equivIco p a x : ℝ) :=
    continuous_iff_continuousAt.2 fun x ↦ continuous_subtypeVal.continuousAt.comp
      ((continuousAt_equivIco p a x.property).comp continuous_subtypeVal.continuousAt)
  refine ⟨((a + p / 2 : ℝ) : AddCircle p), ⟨{
    toFun := fun q ↦ ((((1 : ℝ) - q.1) * equivIco p a q.2 + q.1 * (a + p / 2) : ℝ) : AddCircle p)
    continuous_toFun := continuous_quotient_mk'.comp
      (((continuous_const.sub (continuous_subtypeVal.comp continuous_fst)).mul
        (hL.comp continuous_snd)).add
        ((continuous_subtypeVal.comp continuous_fst).mul continuous_const))
    map_zero_left := fun x ↦ by simp
    map_one_left := fun x ↦ by simp }⟩⟩

end AddCircle

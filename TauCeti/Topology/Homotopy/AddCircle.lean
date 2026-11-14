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
is null-homotopic (`Function.Periodic.exists_nullhomotopic_iff_loop_homotopic_refl`). In a locally
path-connected, semilocally simply connected space, null-homotopy of circle maps is clopen in the
compact-open topology (`TauCeti.isClopen_setOf_nullhomotopic_addCircle`), propagates along
continuous families of periodic curves over preconnected parameter sets
(`TauCeti.forall_exists_nullhomotopic_of_isPreconnected`), and is preserved under uniform
convergence along an inducing map (`Function.Periodic.exists_nullhomotopic_of_tendstoUniformly`).

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
* `ContinuousMap.nullhomotopic_addCircle_of_simplyConnectedSpace`: every continuous map from a
  circle `AddCircle p` with `0 < p` into a simply connected space is null-homotopic.
* `Function.Periodic.loop`: the loop traced by a continuous periodic curve over one period.
* `Function.Periodic.exists_nullhomotopic_iff_loop_homotopic_refl`: a continuous periodic curve is
  contractible exactly when its loop over a period is null-homotopic.
* `TauCeti.isClopen_setOf_nullhomotopic_addCircle`: in a locally path-connected, semilocally simply
  connected space, null-homotopic circle maps form a clopen set in `C(AddCircle p, X)`.
* `Function.Periodic.exists_nullhomotopic_of_tendstoUniformly`: a continuous periodic curve that is
  a uniform limit (along an inducing map) of contractible curves is contractible.
* `TauCeti.isClopen_setOf_exists_nullhomotopic` and
  `TauCeti.forall_exists_nullhomotopic_of_isPreconnected`: null-homotopy is locally constant along
  continuous families of periodic curves.
* `ContinuousMap.Nullhomotopic.exists_addCircle_comp_mul`: a null-homotopic loop run at constant
  nonzero speed is null-homotopic.
* `AddCircle.nullhomotopic_subtypeVal_compl_singleton`: the circle with a point removed contracts
  in the circle.
-/

public section

noncomputable section

open Filter Set Topology
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

end Function.Periodic

namespace TauCeti

/-- **Null-homotopy is clopen in `C(AddCircle p, X)`.** In a locally path-connected, semilocally
simply connected space `X`, the null-homotopic maps `AddCircle p → X` (`0 < p`) form a clopen set
in the compact-open topology. -/
theorem isClopen_setOf_nullhomotopic_addCircle {p : ℝ} [Fact (0 < p)] {X : Type*}
    [TopologicalSpace X] [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] :
    IsClopen {f : C(AddCircle p, X) | f.Nullhomotopic} := by
  have h : {f : C(AddCircle p, X) | f.Nullhomotopic} =
      {f : C(AddCircle p, X) | f.toLoop.Homotopic (Path.refl (f 0))} :=
    Set.ext fun f ↦ f.nullhomotopic_iff_homotopic_refl f.toLoop fun _ ↦ rfl
  rw [h]
  refine isClopen_setOf_homotopic_refl ContinuousMap.toLoop ?_
  exact continuous_eval.comp
    (((ContinuousMap.continuous_precomp (AddCircle.ofUnitInterval p)).comp continuous_fst).prodMk
      continuous_snd)

/-- **Null-homotopy of a continuous family of periodic curves is locally constant.** In a locally
path-connected, semilocally simply connected space `X`, if `u y` is `p`-periodic (`0 < p`) and
`(y, t) ↦ u y t` is continuous, then the parameters `y` for which `u y` descends to a
null-homotopic map `AddCircle p → X` form a clopen set. -/
theorem isClopen_setOf_exists_nullhomotopic {Y X : Type*} [TopologicalSpace Y]
    [TopologicalSpace X] [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    {p : ℝ} [Fact (0 < p)] {u : Y → ℝ → X} (hper : ∀ y, Function.Periodic (u y) p)
    (hu : Continuous (Function.uncurry u)) :
    IsClopen {y : Y | ∃ g : C(AddCircle p, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u y t} := by
  have hcont (y : Y) : Continuous (u y) := hu.comp (continuous_const.prodMk continuous_id)
  have heq : {y : Y | ∃ g : C(AddCircle p, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u y t} =
      {y : Y | ((hper y).loop (hcont y) 0).Homotopic (Path.refl (u y 0))} :=
    Set.ext fun y ↦ (hper y).exists_nullhomotopic_iff_loop_homotopic_refl (hcont y) 0
  rw [heq]
  refine isClopen_setOf_homotopic_refl (fun y ↦ (hper y).loop (hcont y) 0) ?_
  exact hu.comp (continuous_fst.prodMk
    (continuous_const.add ((continuous_subtype_val.comp continuous_snd).mul continuous_const)))

/-- **Propagation of contractibility along a preconnected family of periodic curves.** In a
locally path-connected, semilocally simply connected space `X`, if `s ⊆ Y` is preconnected,
`(y, t) ↦ u y t` is continuous on `s ×ˢ univ`, each `u y` (`y ∈ s`) is `p`-periodic (`0 < p`),
and `u y₀` is null-homotopic on `AddCircle p` at one `y₀ ∈ s`, then `u y` is null-homotopic on
`AddCircle p` for every `y ∈ s`. -/
theorem forall_exists_nullhomotopic_of_isPreconnected {Y X : Type*} [TopologicalSpace Y]
    [TopologicalSpace X] [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    {p : ℝ} [Fact (0 < p)] {s : Set Y} (hs : IsPreconnected s) {u : Y → ℝ → X}
    (hu : ContinuousOn (Function.uncurry u) (s ×ˢ univ))
    (hper : ∀ y ∈ s, Function.Periodic (u y) p) {y₀ : Y} (hy₀s : y₀ ∈ s)
    (hy₀ : ∃ g : C(AddCircle p, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u y₀ t) :
    ∀ y ∈ s, ∃ g : C(AddCircle p, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u y t := by
  have : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.1 hs
  have hclopen : IsClopen {y : s | ∃ g : C(AddCircle p, X),
      g.Nullhomotopic ∧ ∀ t : ℝ, g t = u y t} :=
    isClopen_setOf_exists_nullhomotopic (fun y ↦ hper y y.2)
      (hu.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
        fun q ↦ ⟨q.1.2, trivial⟩)
  have heq := hclopen.eq_univ ⟨⟨y₀, hy₀s⟩, hy₀⟩
  intro y hy
  exact eq_univ_iff_forall.1 heq ⟨y, hy⟩

end TauCeti

namespace Function.Periodic

/-- **Uniform limits of contractible curves are contractible.** In a locally path-connected,
semilocally simply connected space `X`, if a continuous `p`-periodic curve `γ` (`0 < p`) takes
values in a set `K` on which `e : X → F` is topologically inducing, `e ∘ u i` converges uniformly
to `e ∘ γ` along a filter `l`, `u i` eventually takes values in `K`, and `u i` frequently descends
to a null-homotopic map `AddCircle p → X`, then `γ` descends to a null-homotopic map
`AddCircle p → X`. -/
theorem exists_nullhomotopic_of_tendstoUniformly {p : ℝ} [Fact (0 < p)] {X : Type*}
    [TopologicalSpace X] [LocallyPathConnectedSpace X] [TauCeti.SemilocallySimplyConnectedSpace X]
    {γ : ℝ → X} (hp : Periodic γ p) (hγ : Continuous γ) {K : Set X} (hγK : ∀ t, γ t ∈ K)
    {F : Type*} [UniformSpace F] {e : X → F} (he : IsInducing fun x : K ↦ e x)
    {ι : Type*} {l : Filter ι} {u : ι → ℝ → X} (huK : ∀ᶠ i in l, ∀ t, u i t ∈ K)
    (hunif : TendstoUniformly (fun i t ↦ e (u i t)) (e ∘ γ) l)
    (hnull : ∃ᶠ i in l, ∃ g : C(AddCircle p, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u i t) :
    ∃ g : C(AddCircle p, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ t := by
  let g₀ : C(AddCircle p, X) := ⟨hp.lift, hγ.quotient_liftOn' _⟩
  have hg₀γ (t : ℝ) : g₀ t = γ t := hp.lift_coe t
  let P (i : ι) : Prop :=
    (∃ g : C(AddCircle p, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u i t) ∧ ∀ t, u i t ∈ K
  let l' : Filter ι := l ⊓ 𝓟 {i | P i}
  have : l'.NeBot := frequently_iff_neBot.1 (hnull.and_eventually huK)
  let g₀K : C(AddCircle p, K) :=
    ⟨fun θ ↦ ⟨g₀ θ, QuotientAddGroup.induction_on θ fun t ↦ (hg₀γ t).symm ▸ hγK t⟩,
      g₀.continuous.subtype_mk _⟩
  let gK (i : ι) : C(AddCircle p, K) := open scoped Classical in
    if hi : P i then
      ⟨fun θ ↦ ⟨hi.1.choose θ,
          QuotientAddGroup.induction_on θ fun t ↦ (hi.1.choose_spec.2 t).symm ▸ hi.2 t⟩,
        hi.1.choose.continuous.subtype_mk _⟩
    else g₀K
  let eK : C(K, F) := ⟨fun x ↦ e x, he.continuous⟩
  have hlim : Tendsto gK l' (𝓝 g₀K) := by
    refine (ContinuousMap.isInducing_postcomp (X := AddCircle p) eK he).tendsto_nhds_iff.2 ?_
    refine ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.2 fun C _ V hV ↦ ?_
    filter_upwards [mem_inf_of_left (hunif V hV),
      mem_inf_of_right (mem_principal_self _)] with i hiV hiP θ _
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    simp only [gK, hiP, dite_true, eK, g₀K, Function.comp_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, hg₀γ, hiP.1.choose_spec.2]
    exact hiV t
  have hg₀eq : (ContinuousMap.subtypeVal K).comp g₀K = g₀ := by ext; rfl
  have hval : Tendsto (fun i ↦ (ContinuousMap.subtypeVal K).comp (gK i)) l' (𝓝 g₀) :=
    hg₀eq ▸ ((ContinuousMap.continuous_postcomp (ContinuousMap.subtypeVal K)).tendsto g₀K).comp hlim
  refine ⟨g₀, TauCeti.isClopen_setOf_nullhomotopic_addCircle.isClosed.mem_of_tendsto hval ?_, hg₀γ⟩
  filter_upwards [mem_inf_of_right (mem_principal_self _)] with i hiP
  have heq : (ContinuousMap.subtypeVal K).comp (gK i) = hiP.1.choose := by
    ext θ
    simp [gK, hiP]
  exact heq ▸ hiP.1.choose_spec.1

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
    continuous_iff_continuousAt.2 fun x ↦ continuous_subtype_val.continuousAt.comp
      ((continuousAt_equivIco p a x.2).comp continuous_subtype_val.continuousAt)
  refine ⟨((a + p / 2 : ℝ) : AddCircle p), ⟨{
    toFun := fun q ↦ ((((1 : ℝ) - q.1) * equivIco p a q.2 + q.1 * (a + p / 2) : ℝ) : AddCircle p)
    continuous_toFun := continuous_quotient_mk'.comp
      (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (hL.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_fst).mul continuous_const))
    map_zero_left := fun x ↦ by simp
    map_one_left := fun x ↦ by simp }⟩⟩

end AddCircle

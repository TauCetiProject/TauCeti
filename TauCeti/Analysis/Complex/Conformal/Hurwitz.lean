/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import TauCeti.Analysis.Complex.Conformal.Rouche
public import TauCeti.Analysis.Complex.IsolatedZero
public import TauCeti.Analysis.Complex.ZeroCount
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Hurwitz's theorem

Hurwitz's theorem describes how the zeros of a locally uniform limit of holomorphic functions
relate to the zeros of the approximants, and it does so in both directions. The limit acquires no
new zeros — a limit of nowhere-vanishing functions is nowhere vanishing or identically zero — and
it loses none either: every zero of the limit is approached by zeros of the approximants. It is
the perturbation backbone for the injectivity step of the Riemann mapping theorem.

Both directions come from one Rouché estimate, isolated here as
`TauCeti.eventually_finsum_analyticOrderNatAt_ball_eq`. Fix a disc whose closure lies in `Ω` and on
whose bounding circle the limit `g` does not vanish. Then `‖g‖` has a positive minimum `δ` on that
circle by compactness, and locally uniform convergence eventually forces `‖g - F i‖ < δ ≤ ‖g‖`
there — exactly Rouché's hypothesis. So *eventually the zero counts of `F i` and of `g` inside the
disc agree*, an equality of natural numbers from which both halves of Hurwitz's theorem are read
off by looking at one side or the other:

* the count of `g` is `0` whenever the `F i` are zero-free, and a function whose count vanishes on
  every such disc has no zeros at all;
* the count of `g` is positive at an isolated zero of `g`, so the count of `F i` is too, and `F i`
  has a zero in a disc that can be taken as small as one likes.

The second reading needs the zero of `g` to be isolated, which is why the *identically zero*
alternative is unavoidable and why `Ω` is assumed connected: it is the identity theorem that turns
"`g` is not constantly `v`" into "`g ≠ v` on a punctured neighbourhood of each point".

Everything is stated for an arbitrary value `v`, not only for `v = 0`: applying the above to
`g - v` costs nothing and gives the statement actually used downstream — a value omitted by the
`F i` is omitted by the limit unless the limit is constantly that value. Specialising to `v = 0`
recovers the classical phrasing `TauCeti.hurwitz`.

Throughout, holomorphy of the family is assumed only *eventually along `l`*: it holds on some
index set belonging to `l`, not on every index. Along a sequence that reads "for all sufficiently
large `i`", the phrasing the docstrings below use; for a general filter it says only that the
indices where the hypothesis fails are excluded by a member of `l`. That is the form limit
arguments produce and consume, and it costs nothing: the conclusions are eventual along `l` as
well, so indices outside a set of `l` never enter. The hypotheses the limit inherits — omitting a
value, injectivity — are needed only *frequently along `l`* (along a sequence: for infinitely many
`i`), since a single such index already contradicts the eventual conclusion.

The corollary usually quoted alongside is the injectivity form: a locally uniform limit of
*injective* holomorphic functions is injective or constant. That is the version the Riemann mapping
theorem consumes. It is proved from the value form: if `g a = g b` for `a ≠ b` and `g` is not
constant, then for all sufficiently large `i` the function `F i` takes the value `g a` in each of
two disjoint balls about `a` and `b`, contradicting injectivity. This avoids applying
`TauCeti.hurwitz` to the differences `F i - F i b` on the punctured domain `Ω \ {b}`, which would
need that set to be connected.

## Main results

* `TauCeti.eventually_finsum_analyticOrderNatAt_ball_eq` — **Hurwitz's theorem, counting form**:
  on a disc whose bounding circle avoids the zeros of the limit, the approximants eventually have
  the same number of zeros as the limit, counted with multiplicity.
* `TauCeti.hurwitz_eventually_exists_eq` — **zeros of the limit are limits of zeros**: if `g` is
  not constantly `v` and `g z₀ = v`, then every neighbourhood of `z₀` eventually contains a point
  where `F i` takes the value `v`.
* `TauCeti.hurwitz_eventually_exists_eq_zero` — the same for `v = 0`.
* `TauCeti.hurwitz_forall_ne` — a value omitted by the `F i` is omitted by a limit that is not
  constantly that value.
* `TauCeti.hurwitz_forall_ne_or_forall_eq` — the dichotomy form of the previous statement.
* `TauCeti.hurwitz` — a locally uniform limit of nowhere-vanishing holomorphic functions on a
  connected open set is nowhere vanishing or identically zero.
* `TauCeti.hurwitz_injOn` — a locally uniform limit of injective holomorphic functions is injective
  or constant.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 5.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. VII.
-/

public section

open Complex Metric Filter Topology

namespace TauCeti

variable {ι : Type*} {l : Filter ι} {Ω : Set ℂ} {F : ι → ℂ → ℂ} {g : ℂ → ℂ}

/-- **Hurwitz's theorem, counting form.** Let `g` and — for all sufficiently large `i` — the `F i`
be analytic on a closed disc `closedBall c r` of positive radius, let `F i → g` uniformly on the
bounding circle `sphere c r`, and let `g` not vanish on that circle. Then for all sufficiently
large `i`, `F i` has exactly as many zeros in `ball c r` as `g` does, counted with multiplicity.

No ambient domain enters: a locally uniform limit on an open `Ω` supplies the uniform convergence
on any circle with `closedBall c r ⊆ Ω`, via
`tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact`. -/
theorem eventually_finsum_analyticOrderNatAt_ball_eq {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : AnalyticOnNhd ℂ g (closedBall c r))
    (hF : ∀ᶠ i in l, AnalyticOnNhd ℂ (F i) (closedBall c r))
    (hconv : TendstoUniformlyOn F g l (sphere c r))
    (hne : ∀ z ∈ sphere c r, g z ≠ 0) :
    ∀ᶠ i in l, (∑ᶠ z ∈ ball c r, analyticOrderNatAt (F i) z)
      = ∑ᶠ z ∈ ball c r, analyticOrderNatAt g z := by
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_norm_of_mem_sphere
    (hg.continuousOn.mono sphere_subset_closedBall) hne
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv _ hδ, hF] with i hi hFi
  exact (rouche hr hg hFi fun z hz =>
    lt_of_lt_of_le (by simpa [dist_eq_norm] using hi z hz) (hδle z hz)).symm

/-- **Hurwitz's theorem: zeros of the limit are limits of zeros.** If `g` is the locally uniform
limit on a connected open `Ω` of functions `F i` that are holomorphic for all sufficiently large
`i`, is not identically zero, and vanishes at `z₀ ∈ Ω`, then every ball about `z₀` contains a zero
of `F i` for all sufficiently large `i`.

The hypothesis that `g` is not identically zero cannot be dropped: for `ι = ℕ` and `l = atTop`,
the constant functions `F n z = 1 / (n + 1 : ℂ)` are holomorphic and nowhere zero and converge
locally uniformly to `g = 0`, which vanishes at every `z₀`, yet no `F n` has a zero anywhere.

Note that the ball is *not* assumed to lie in `Ω`; the zero produced is located in
`Ω ∩ ball z₀ ε`. -/
theorem hurwitz_eventually_exists_eq_zero [l.NeBot] (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) Ω)
    (hconv : TendstoLocallyUniformlyOn F g l Ω)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hgz₀ : g z₀ = 0) (hnc : ¬ ∀ z ∈ Ω, g z = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∃ z ∈ Ω ∩ ball z₀ ε, F i z = 0 := by
  have hgA : AnalyticOnNhd ℂ g Ω :=
    (_root_.TendstoLocallyUniformlyOn.differentiableOn hconv hF hΩ).analyticOnNhd hΩ
  -- by the identity theorem, `z₀` is an isolated zero of `g`; pick a closed disc about `z₀`
  -- inside `Ω ∩ ball z₀ ε` on which `g` vanishes only at the centre
  have hpunct : ∀ᶠ z in 𝓝[≠] z₀, g z ≠ 0 := not_frequently.mp fun h => hnc fun z hz =>
    hgA.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const hconn hz₀ h hz
  obtain ⟨r, hr, hzf⟩ := nhds_basis_closedBall.eventually_iff.mp
    (((hΩ.inter isOpen_ball).eventually_mem ⟨hz₀, mem_ball_self hε⟩).and
      (eventually_nhdsWithin_iff.mp hpunct))
  have hsub : closedBall z₀ r ⊆ Ω ∩ ball z₀ ε := fun z hz => (hzf hz).1
  have hball : closedBall z₀ r ⊆ Ω := hsub.trans Set.inter_subset_left
  have hsphne : ∀ z ∈ sphere z₀ r, g z ≠ 0 := fun z hz =>
    (hzf (sphere_subset_closedBall hz)).2 (ne_of_mem_sphere hz hr.ne')
  have hFA : ∀ᶠ i in l, AnalyticOnNhd ℂ (F i) (closedBall z₀ r) :=
    hF.mono fun i hi => (hi.analyticOnNhd hΩ).mono hball
  have hconvS : TendstoUniformlyOn F g l (sphere z₀ r) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere z₀ r)).mp
      (hconv.mono (sphere_subset_closedBall.trans hball))
  -- `g` vanishes at the centre but not on the bounding circle, so its count is nonzero
  have hcount : (∑ᶠ z ∈ ball z₀ r, analyticOrderNatAt g z) ≠ 0 := fun h =>
    (finsum_analyticOrderNatAt_ball_eq_zero_iff (hgA.mono hball)
        (exists_mem_closedBall_ne_zero_of_forall_mem_sphere_ne_zero hr.le hsphne)).mp h z₀
      (mem_ball_self hr) hgz₀
  filter_upwards [eventually_finsum_analyticOrderNatAt_ball_eq hr (hgA.mono hball) hFA hconvS
    hsphne, hF] with i hi hFi
  by_contra! hcon
  exact hcount (hi ▸ finsum_analyticOrderNatAt_ball_eq_zero_of_forall_ne_zero
    ((hFi.analyticOnNhd hΩ).mono (ball_subset_closedBall.trans hball)) fun z hz =>
      hcon z (hsub (ball_subset_closedBall hz)))

/-- **Hurwitz's theorem: values of the limit are limits of values.** If `g` is the locally uniform
limit on a connected open `Ω` of functions `F i` that are holomorphic for all sufficiently large
`i`, is not constantly `v`, and takes the value `v` at `z₀ ∈ Ω`, then every ball about `z₀`
contains a point where `F i` takes the value `v`, again for all sufficiently large `i`.

This is `TauCeti.hurwitz_eventually_exists_eq_zero` for the translated family `F i - v`, and the
form the injectivity corollary `TauCeti.hurwitz_injOn` consumes. -/
theorem hurwitz_eventually_exists_eq [l.NeBot] (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) Ω)
    (hconv : TendstoLocallyUniformlyOn F g l Ω)
    {v z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hgz₀ : g z₀ = v) (hnc : ¬ ∀ z ∈ Ω, g z = v)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∃ z ∈ Ω ∩ ball z₀ ε, F i z = v := by
  have hconst : TendstoLocallyUniformlyOn (fun (_ : ι) (_ : ℂ) => v) (fun _ => v) l Ω :=
    (tendsto_const_nhds.tendstoUniformlyOn_const Ω).tendstoLocallyUniformlyOn
  have hzero := hurwitz_eventually_exists_eq_zero (F := fun i z => F i z - v)
    (g := fun z => g z - v) hΩ hconn (hF.mono fun i hi => hi.sub_const v) (hconv.sub hconst)
    hz₀ (by simp [hgz₀]) (fun h => hnc fun z hz => sub_eq_zero.mp (h z hz)) hε
  exact hzero.mono fun i ⟨z, hz, hz0⟩ => ⟨z, hz, sub_eq_zero.mp hz0⟩

/-- **Hurwitz's theorem for an omitted value.** If `F i` is holomorphic on `Ω` for all sufficiently
large `i` and avoids the value `v` there for infinitely many `i` (frequently along `l`), and the
locally uniform limit `g` is not constantly `v`, then `g` avoids `v` as well.

Contrapositive of `TauCeti.hurwitz_eventually_exists_eq`: a point where `g` took the value `v`
would force `F i` to take it too. -/
theorem hurwitz_forall_ne (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) Ω)
    (hconv : TendstoLocallyUniformlyOn F g l Ω) {v : ℂ}
    (hne : ∃ᶠ i in l, ∀ z ∈ Ω, F i z ≠ v) (hnc : ¬ ∀ z ∈ Ω, g z = v) :
    ∀ z ∈ Ω, g z ≠ v := by
  have : l.NeBot := (frequently_iff_neBot.mp hne).mono inf_le_left
  intro z₀ hz₀ hgz₀
  obtain ⟨i, ⟨z, hz, hzv⟩, hnei⟩ :=
    ((hurwitz_eventually_exists_eq hΩ hconn hF hconv hz₀ hgz₀ hnc one_pos).and_frequently
      hne).exists
  exact hnei z hz.1 hzv

/-- **Hurwitz's theorem for an omitted value**, dichotomy form. On a connected open set, a locally
uniform limit of functions that are holomorphic for all sufficiently large `i` and avoid the value
`v` for infinitely many `i` either avoids `v` everywhere or is constantly `v`.

The dichotomy is genuine: for `ι = ℕ` and `l = atTop`, the functions `F n z = v + 1 / (n + 1 : ℂ)`
avoid `v` on any `Ω` and converge locally uniformly to the constant `v`. -/
theorem hurwitz_forall_ne_or_forall_eq (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) Ω)
    (hconv : TendstoLocallyUniformlyOn F g l Ω) {v : ℂ}
    (hne : ∃ᶠ i in l, ∀ z ∈ Ω, F i z ≠ v) :
    (∀ z ∈ Ω, g z ≠ v) ∨ (∀ z ∈ Ω, g z = v) :=
  or_iff_not_imp_right.mpr (hurwitz_forall_ne hΩ hconn hF hconv hne)

/-- **Hurwitz's theorem.** On a connected open set, a locally uniform limit of functions that are
holomorphic for all sufficiently large `i` and nowhere zero for infinitely many `i` is itself
either nowhere zero or identically zero.

This is the value `v = 0` of `TauCeti.hurwitz_forall_ne_or_forall_eq`. The dichotomy is genuine:
for `ι = ℕ` and `l = atTop`, the constant functions `F n z = 1 / (n + 1 : ℂ)` on any `Ω` converge
locally uniformly to `0`, so the second alternative cannot be dropped. -/
theorem hurwitz (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) Ω)
    (hconv : TendstoLocallyUniformlyOn F g l Ω)
    (hne : ∃ᶠ i in l, ∀ z ∈ Ω, F i z ≠ 0) :
    (∀ z ∈ Ω, g z ≠ 0) ∨ (∀ z ∈ Ω, g z = 0) :=
  hurwitz_forall_ne_or_forall_eq hΩ hconn hF hconv hne

/-- **Hurwitz's theorem for injectivity.** On a connected open set, a locally uniform limit of
functions that are holomorphic for all sufficiently large `i` and *injective* for infinitely many
`i` is either injective or constant.

This is the form the Riemann mapping theorem consumes: it is what keeps the extremal map injective
in the limit. Both alternatives genuinely occur — for `ι = ℕ` and `l = atTop`, the injective maps
`F n z = z / (n + 1 : ℂ)` converge locally uniformly to the constant `0`. -/
theorem hurwitz_injOn (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) Ω)
    (hconv : TendstoLocallyUniformlyOn F g l Ω)
    (hinj : ∃ᶠ i in l, Set.InjOn (F i) Ω) :
    Set.InjOn g Ω ∨ ∃ v, ∀ z ∈ Ω, g z = v := by
  have : l.NeBot := (frequently_iff_neBot.mp hinj).mono inf_le_left
  refine or_iff_not_imp_right.mpr fun hconst a ha b hb hab => ?_
  by_contra hne
  have hd : 0 < dist a b / 2 := half_pos (dist_pos.mpr hne)
  have hnc : ¬ ∀ z ∈ Ω, g z = g a := fun h => hconst ⟨g a, h⟩
  obtain ⟨i, ⟨⟨z₁, hz₁, hFz₁⟩, ⟨z₂, hz₂, hFz₂⟩⟩, hinji⟩ :=
    (((hurwitz_eventually_exists_eq hΩ hconn hF hconv ha rfl hnc hd).and
      (hurwitz_eventually_exists_eq hΩ hconn hF hconv hb hab.symm hnc hd)).and_frequently
        hinj).exists
  exact (ball_disjoint_ball (add_halves _).le).ne_of_mem hz₁.2 hz₂.2
    (hinji hz₁.1 hz₂.1 (hFz₁.trans hFz₂.symm))

end TauCeti

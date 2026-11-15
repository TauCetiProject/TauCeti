/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Montel.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Vitali's convergence theorem

Vitali's theorem upgrades pointwise convergence on a set with an accumulation point to locally
uniform convergence for a locally bounded sequence of holomorphic maps.

The proof applies `TauCeti.montel` twice. First choose one locally uniform subsequential limit `g`.
For an arbitrary subsequence, Montel supplies a further locally uniform limit `q`. Both limits
agree on the pointwise convergence set, hence on the whole preconnected domain by Mathlib's
analytic identity theorem
`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`. Thus every subsequence has a further
subsequence converging to `g` uniformly on each compact subset, and the sequential convergence
criterion `tendsto_of_subseq_tendsto` gives locally uniform convergence of the original sequence.

When the family already converges pointwise on the *whole* of `Ω`, none of that machinery is
needed. Local boundedness makes the family equicontinuous on `Ω`
(`TauCeti.IsLocallyBoundedOn.equicontinuousOn`, the Cauchy-estimate half of Montel's theorem), and
on an equicontinuous family pointwise convergence *is* uniform convergence on each compact subset,
by Mathlib's Arzelà–Ascoli lemma `Equicontinuous.tendsto_uniformFun_iff_pi`. This is why the
whole-domain statements below are not corollaries of `TauCeti.vitali`: they spend no identity
theorem, hence need neither an accumulation point nor connectivity of `Ω`, and no selection
theorem, hence do not run on `TauCeti.montel` at all.

## Main results

* `TauCeti.vitali` — a locally bounded sequence of holomorphic maps on an open *preconnected*
  `Ω` which converges pointwise on a set with an accumulation point in the domain converges locally
  uniformly to a holomorphic map.
* `TauCeti.vitali_of_tendsto` — the same theorem with a prescribed pointwise limit on the
  convergence set.
* `TauCeti.tendstoLocallyUniformlyOn_of_isLocallyBoundedOn_of_forall_tendsto` — a locally bounded
  family of holomorphic maps converging pointwise on the whole of `Ω` along any filter converges to
  that limit **locally uniformly**: on such a family, pointwise convergence and locally uniform
  convergence are the same thing.
* `TauCeti.exists_differentiableOn_tendstoLocallyUniformlyOn_of_isLocallyBoundedOn` — its
  existential companion, for a consumer who knows the family converges at each point of `Ω`
  without a name for the limit.

Holomorphy of such a pointwise limit, and termwise differentiation along it, are then Mathlib's
`TendstoLocallyUniformlyOn.differentiableOn` and `TendstoLocallyUniformlyOn.deriv` applied to the
third of these.

## The target space

`TauCeti.vitali` runs `TauCeti.montel`, which needs a proper target, so it is stated for a proper
complex normed space `E`; over `ℂ` these are exactly the finite-dimensional ones, `ℂ` itself
included. Vitali's theorem does hold for an arbitrary Banach target (Arendt and Nikolski,
*Vector-valued holomorphic functions revisited*, Math. Z. **234** (2000), §2), but by a different
argument — convergence of the Taylor coefficients at an accumulation point, and a clopen
propagation — so that generality is a separate theorem rather than a weakening of this one. The
whole-domain statements spend no selection theorem, so they hold for an arbitrary complex normed
target, complete where holomorphy of the limit is concluded.

## References

* [Mathlib PR #33505](https://github.com/leanprover-community/mathlib4/pull/33505), the preceding
  human-curated Riemann-mapping development and its local analytic prerequisites.
* L. Ahlfors, *Complex Analysis*, Ch. 5 §5.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. VII §2.
-/

public section

open Complex Filter Set Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {Ω A : Set ℂ}

/-! ### Vitali's theorem -/

section Vitali

variable [ProperSpace E] {F : ℕ → ℂ → E}

/-- **Vitali's convergence theorem.** Let `Ω` be an open preconnected subset of `ℂ`. A locally
bounded sequence of holomorphic maps from `Ω` into a proper complex normed space `E` (for instance
`ℂ`) which converges pointwise on a subset `A ⊆ Ω` having an accumulation point in `Ω` converges
locally uniformly on `Ω` to a holomorphic map.

The pointwise limit on `A` need not be supplied: its existence is enough to determine the
holomorphic limit uniquely. -/
theorem vitali (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hF : ∀ n, DifferentiableOn ℂ (F n) Ω) (hb : IsLocallyBoundedOn F Ω)
    (hAΩ : A ⊆ Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hacc : AccPt z₀ (𝓟 A))
    (hpoint : ∀ z ∈ A, ∃ w, Tendsto (fun n => F n z) atTop (𝓝 w)) :
    ∃ g : ℂ → E, DifferentiableOn ℂ g Ω ∧ TendstoLocallyUniformlyOn F g atTop Ω := by
  -- A first subsequential limit `g`; on `A` the whole sequence converges, necessarily to `g`.
  obtain ⟨φ, g, hφ, hg, hφconv⟩ := montel hΩ hF hb
  have hgA : ∀ z ∈ A, Tendsto (fun n => F n z) atTop (𝓝 (g z)) := fun z hz => by
    obtain ⟨w, hw⟩ := hpoint z hz
    rwa [tendsto_nhds_unique (hφconv.tendsto_at (hAΩ hz)) (hw.comp hφ.tendsto_atTop)]
  refine ⟨g, hg, (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).2 fun K hKΩ hK => ?_⟩
  -- On a compact `K`, every subsequence has a further subsequence converging uniformly to `g`.
  rw [tendstoUniformlyOn_iff_restrict]
  refine (UniformFun.tendsto_iff_tendstoUniformly
    (F := fun n => UniformFun.ofFun (K.domRestrict (F n)))
    (f := UniformFun.ofFun (K.domRestrict g))).1 (tendsto_of_subseq_tendsto fun ψ hψ => ?_)
  obtain ⟨θ, q, hθ, hq, hθconv⟩ := montel hΩ (fun n => hF (ψ n)) (hb.comp ψ)
  -- The further limit `q` agrees with `g` on `A`, hence on `Ω` by the identity theorem.
  have hqg : Ω.EqOn q g :=
    (hq.analyticOnNhd hΩ).eqOn_of_preconnected_of_frequently_eq (hg.analyticOnNhd hΩ) hconn hz₀
      ((accPt_iff_frequently_nhdsNE.mp hacc).mono fun z hz =>
        tendsto_nhds_unique (hθconv.tendsto_at (hAΩ hz))
          ((hgA z hz).comp (hψ.comp hθ.tendsto_atTop)))
  exact ⟨θ, UniformFun.tendsto_iff_tendstoUniformly.2 (tendstoUniformlyOn_iff_restrict.1
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1
      ((hθconv.congr_right hqg).mono hKΩ)))⟩

/-- **Vitali's theorem with prescribed pointwise values.** Under the hypotheses of `vitali`, if
the sequence converges pointwise on `A` to a specified function `g`, its locally uniform
holomorphic limit agrees with `g` throughout `A`.

No regularity of `g` away from `A` is assumed or concluded; when `A` is all of `Ω` the limit is
`g` itself, which is
`TauCeti.tendstoLocallyUniformlyOn_of_isLocallyBoundedOn_of_forall_tendsto`. -/
theorem vitali_of_tendsto (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hF : ∀ n, DifferentiableOn ℂ (F n) Ω) (hb : IsLocallyBoundedOn F Ω)
    (hAΩ : A ⊆ Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hacc : AccPt z₀ (𝓟 A))
    {g : ℂ → E} (hpoint : ∀ z ∈ A, Tendsto (fun n => F n z) atTop (𝓝 (g z))) :
    ∃ q : ℂ → E, DifferentiableOn ℂ q Ω ∧ A.EqOn q g ∧
      TendstoLocallyUniformlyOn F q atTop Ω := by
  obtain ⟨q, hq, hconv⟩ :=
    vitali hΩ hconn hF hb hAΩ hz₀ hacc fun z hz => ⟨g z, hpoint z hz⟩
  exact ⟨q, hq, fun z hz => tendsto_nhds_unique (hconv.tendsto_at (hAΩ hz)) (hpoint z hz), hconv⟩

end Vitali

/-! ### Pointwise convergence on the whole domain -/

section WholeDomain

variable {ι : Type*} {l : Filter ι} {F : ι → ℂ → E}

/-- **On a locally bounded family of holomorphic maps, pointwise convergence is locally uniform
convergence.** If a locally bounded family of holomorphic maps on an open `Ω` converges pointwise
along a filter `l` at every point of `Ω`, it converges locally uniformly along `l` to that
pointwise limit.

This is not a case of `TauCeti.vitali`, which asks `Ω` preconnected in order to propagate an
identification made on a small set `A` to the whole domain: here the identification is available at
every point already, so the identity theorem — and with it the connectivity — is not needed. The
converse implication is immediate, locally uniform convergence being pointwise convergence at each
point of `Ω`.

Neither is it a case of `TauCeti.montel`: only the equicontinuity half of Montel's theorem is
spent, not the selection theorem, so the target need not be proper. On a compact `K ⊆ Ω` local
boundedness makes the restricted family equicontinuous
(`TauCeti.IsLocallyBoundedOn.equicontinuousOn`), and on an equicontinuous family the topology of
uniform convergence and the topology of pointwise convergence have the same convergent filters,
which is Mathlib's Arzelà–Ascoli lemma `Equicontinuous.tendsto_uniformFun_iff_pi`. -/
theorem tendstoLocallyUniformlyOn_of_isLocallyBoundedOn_of_forall_tendsto (hΩ : IsOpen Ω)
    (hF : ∀ i, DifferentiableOn ℂ (F i) Ω) (hb : IsLocallyBoundedOn F Ω) {g : ℂ → E}
    (hpoint : ∀ z ∈ Ω, Tendsto (fun i => F i z) l (𝓝 (g z))) :
    TendstoLocallyUniformlyOn F g l Ω := by
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).2 fun K hKΩ hK => ?_
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have heq : Equicontinuous (K.domRestrict ∘ F) :=
    (equicontinuous_restrict_iff F).2 ((hb.equicontinuousOn hΩ hF).mono hKΩ)
  rw [tendstoUniformlyOn_iff_restrict]
  exact UniformFun.tendsto_iff_tendstoUniformly.1
    ((heq.tendsto_uniformFun_iff_pi l (K.domRestrict g)).2
      (tendsto_pi_nhds.2 fun z => hpoint z (hKΩ z.2)))

/-- **The pointwise limit need not be named.** A locally bounded family of holomorphic maps on an
open `Ω` into a complete complex normed space, which converges along a nontrivial filter `l` at
each point of `Ω`, converges locally uniformly on `Ω` to a holomorphic map — the existential
companion of the statement above, in the shape `TauCeti.vitali` takes on a subset `A`.

The limit is `fun z => limUnder l fun i => F i z`, which the hypothesis identifies as the
pointwise limit on `Ω`; no connectivity of `Ω` and no accumulation point is involved, exactly as
above, and holomorphy of the limit is `TendstoLocallyUniformlyOn.differentiableOn`. -/
theorem exists_differentiableOn_tendstoLocallyUniformlyOn_of_isLocallyBoundedOn [CompleteSpace E]
    [l.NeBot] (hΩ : IsOpen Ω) (hF : ∀ i, DifferentiableOn ℂ (F i) Ω)
    (hb : IsLocallyBoundedOn F Ω) (hpoint : ∀ z ∈ Ω, ∃ w, Tendsto (fun i => F i z) l (𝓝 w)) :
    ∃ g : ℂ → E, DifferentiableOn ℂ g Ω ∧ TendstoLocallyUniformlyOn F g l Ω :=
  have hconv := tendstoLocallyUniformlyOn_of_isLocallyBoundedOn_of_forall_tendsto hΩ hF hb
    (g := fun z => limUnder l fun i => F i z) fun z hz => tendsto_nhds_limUnder (hpoint z hz)
  ⟨_, hconv.differentiableOn (.of_forall hF) hΩ, hconv⟩

end WholeDomain

end TauCeti

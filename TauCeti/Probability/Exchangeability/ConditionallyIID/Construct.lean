/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic
public import TauCeti.Probability.Exchangeability.FiniteMarginals
-- Public: `iIndepFun` appears in the hypothesis of the degeneracy theorem.
public import Mathlib.Probability.Independence.Basic
-- Non-public: the mixture representation and its uniqueness are used only inside the
-- degeneracy proof, and the Layer 0 implications only inside the corollaries.
import TauCeti.Probability.Exchangeability.MixedIID.Mixture
import TauCeti.Probability.Exchangeability.Contractability
import TauCeti.Probability.Exchangeability.IID
import TauCeti.MeasureTheory.Measure.GiryMonad
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# The canonical conditionally i.i.d. process

Every measurable family of probability measures is *realized* as a directing measure. Given a
probability measure `π` on a parameter space `T` and a measurable family
`P : T → ProbabilityMeasure α`, the law

```text
iidMixtureLaw π P = ∫ δ_t ⊗ (P t)^{⊗ℕ} dπ(t)
```

on `T × (ℕ → α)` is the two-stage experiment "draw the parameter `t` from `π`, then sample the
coordinates i.i.d. from `P t`", with the parameter retained as the first coordinate. Its
coordinate process `X n ω = ω.2 n` is **conditionally i.i.d.** with directing measure
`ω ↦ P ω.1`, and the law of that directing measure is the prescribed `π.map P`.

This is the converse direction of the Layer 6 uniqueness statements: `mixedIID_mixingLaw_unique`
and `conditionallyIID_ae_unique` say a directing measure is pinned down by the process, and the
theorems here say every law on `ProbabilityMeasure α` of the form `π.map P` does arise. Before
this file the only `ConditionallyIIDWith` witnesses available were the constant one
(`ConditionallyIIDWith.of_iIndepFun_identDistrib`, i.e. plain i.i.d.) and the one the hard
de Finetti theorem extracts from contractability; nothing produced a *prescribed* nondegenerate
directing measure.

Note that the conclusion is the sharp conditional predicate, not merely the mixture identity: the
generating construction ties the process to `ν` and not just to its law, which is exactly the
difference the roadmap insists on
(`TauCetiRoadmap/Exchangeability/README.md`, "Standing hypotheses").

## Main results

* `iidMixtureLaw` — the canonical two-stage law, with `isProbabilityMeasure_iidMixtureLaw` and the
  marginal `iidMixtureLaw_map_fst`.
* `conditionallyIIDWith_iidMixtureLaw` — the coordinate process is conditionally i.i.d. with
  directing measure `ω ↦ P ω.1`, and the corollaries `mixedIIDWith_iidMixtureLaw`,
  `exchangeable_iidMixtureLaw`, `contractable_iidMixtureLaw`.
* `iidMixtureLaw_map_directing` — the directing measure has the prescribed law `π.map P`, and
  `pathLaw_iidMixtureLaw` reads the path law as the `π.map P`-mixture of infinite powers.
* `map_prod_infinitePi_eq_iidMixtureLaw` — the canonical law is realized by a parameter and
  independent i.i.d. noise pushed through a family of maps carrying the noise law to `P t`.
* `exists_map_eq_dirac_of_iIndepFun_iidMixtureLaw` — the construction is genuinely richer than
  i.i.d.: independent coordinates force the mixing law `π.map P` to be a point mass.

This advances `TauCetiRoadmap/Exchangeability/README.md`, Layer 6 (directing measures), and
supplies the construction the roadmap's coin-flipping worked example instantiates
(`TauCeti/Probability/Exchangeability/ConditionallyIID/CoinFlips.lean`). It needs no material from
`cameronfreer/exchangeability`, whose `ConditionallyIID` names the weaker mixture identity.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {T α : Type*} [MeasurableSpace T] [MeasurableSpace α]

/-- **The canonical conditionally i.i.d. law.** Draw a parameter `t` from `π`, then sample the
coordinates i.i.d. from `P t`, keeping `t` as the first coordinate of the sample space
`T × (ℕ → α)`.

Retaining the parameter is what makes this a *conditional* construction rather than only a mixture
of i.i.d. laws: the sequence and its directing measure live on the same space, so the joint law of
the two can be compared with the disintegration `ConditionallyIIDWith` demands. -/
-- `@[expose]` is forced by the exported `rfl`-unfold `iidMixtureLaw_def` below: a public theorem
-- proved by unfolding the body requires the body to be exposed.
@[expose]
def iidMixtureLaw (π : Measure T) (P : T → ProbabilityMeasure α) : Measure (T × (ℕ → α)) :=
  π.bind fun t => (Measure.dirac t).prod (Measure.infinitePi fun _ : ℕ => (P t : Measure α))

/-- The canonical law unfolded as the `π`-mixture of the parameter-tagged countable powers. -/
@[simp]
theorem iidMixtureLaw_def (π : Measure T) (P : T → ProbabilityMeasure α) :
    iidMixtureLaw π P =
      π.bind fun t => (Measure.dirac t).prod (Measure.infinitePi fun _ : ℕ => (P t : Measure α)) :=
  rfl

variable {π : Measure T} {P : T → ProbabilityMeasure α}

/-- The canonical law is a probability measure. Measurability of `P` is needed, not decorative:
`Measure.bind` against a non-measurable kernel is the zero measure. -/
theorem isProbabilityMeasure_iidMixtureLaw [IsProbabilityMeasure π] (hP : Measurable P) :
    IsProbabilityMeasure (iidMixtureLaw π P) :=
  MeasureTheory.isProbabilityMeasure_bind
    (TauCeti.MeasureTheory.measurable_dirac_prod_infinitePi_const P hP).aemeasurable
    (.of_forall fun _ => inferInstance)

/-- The parameter coordinate of the canonical law is distributed as `π`. -/
theorem iidMixtureLaw_map_fst (hP : Measurable P) :
    (iidMixtureLaw π P).map Prod.fst = π := by
  have hfst : ∀ t : T,
      ((Measure.dirac t).prod (Measure.infinitePi fun _ : ℕ => (P t : Measure α))).map Prod.fst
        = Measure.dirac t := fun _ => Measure.fst_prod
  rw [iidMixtureLaw_def, TauCeti.MeasureTheory.map_bind
    (TauCeti.MeasureTheory.measurable_dirac_prod_infinitePi_const P hP).aemeasurable
    measurable_fst]
  simp_rw [hfst]
  exact Measure.bind_dirac

/-- The directing measure of the canonical law has the prescribed mixing law `π.map P`. -/
theorem iidMixtureLaw_map_directing (hP : Measurable P) :
    (iidMixtureLaw π P).map (fun ω => P ω.1) = π.map P := by
  have hcomp : (fun ω : T × (ℕ → α) => P ω.1) = P ∘ Prod.fst := rfl
  rw [hcomp, ← Measure.map_map hP measurable_fst, iidMixtureLaw_map_fst hP]

/-- **The canonical law from a parameter and i.i.d. noise.** Draw a parameter `t` from `π` and an
independent i.i.d. sequence `r` from `ρ`, and apply a jointly measurable `h t` to each noise
variable. If `h t` pushes `ρ` forward to `P t`, the resulting pair `(t, (h t (r i))ᵢ)` has the
canonical law `iidMixtureLaw π P`: given the parameter, the coordinates are i.i.d. `P t`. -/
theorem map_prod_infinitePi_eq_iidMixtureLaw {R : Type*} [MeasurableSpace R]
    (ρ : Measure R) [IsProbabilityMeasure ρ] {h : T → R → α}
    (hh : Measurable (Function.uncurry h)) (hP : ∀ t, ρ.map (h t) = P t) :
    (π.prod (Measure.infinitePi fun _ : ℕ => ρ)).map (fun q => (q.1, fun i => h q.1 (q.2 i)))
      = iidMixtureLaw π P := by
  have hht (t : T) : Measurable (h t) := hh.comp measurable_prodMk_left
  have hPm : Measurable P := by
    have hPm' : Measurable fun t => (P t : Measure α) := by
      simpa only [hP] using TauCeti.MeasureTheory.measurable_map_of_measurable_uncurry (ν := ρ) hh
    exact hPm'.subtype_mk
  have hG : Measurable fun q : T × (ℕ → R) => (q.1, fun i => h q.1 (q.2 i)) :=
    measurable_fst.prodMk <| Measurable.of_eval fun i =>
      hh.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hpath (t : T) : Measurable fun (r : ℕ → R) i => h t (r i) :=
    Measurable.of_eval fun i => (hht t).comp (measurable_pi_apply i)
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hG hs, Measure.prod_apply (hG hs), iidMixtureLaw_def,
    Measure.bind_apply hs
      (TauCeti.MeasureTheory.measurable_dirac_prod_infinitePi_const P hPm).aemeasurable]
  refine lintegral_congr fun t => ?_
  rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left hs]
  simp_rw [← hP]
  rw [← Measure.infinitePi_map_pi _ fun _ => hht t,
    Measure.map_apply (hpath t) (measurable_prodMk_left hs)]
  -- Both preimages are `{r | (t, fun i => h t (r i)) ∈ s}`.
  rfl

/-- **The canonical process is conditionally i.i.d.** For a measurable family `P`, the coordinate
process of `iidMixtureLaw π P` is conditionally i.i.d. with directing measure `ω ↦ P ω.1`: along
every finite selection of distinct coordinates, the joint law of the directing measure and the
selected block is the disintegration `∫ δ_{P ω.1} ⊗ (P ω.1)^{⊗ Fin m}`.

This is the sharp conditional conclusion — the directing measure is pinned to the process, not
merely to the block laws — which is what makes `iidMixtureLaw` a realization of `P` as a directing
measure rather than only as a mixing representative. -/
theorem conditionallyIIDWith_iidMixtureLaw (hP : Measurable P) :
    ConditionallyIIDWith (iidMixtureLaw π P) (fun n ω => ω.2 n) (fun ω => P ω.1) := by
  -- Both sides of the disintegration collapse to the same `π`-mixture of
  -- `δ_{P t} ⊗ (P t)^{⊗ Fin m}`.
  have hker := TauCeti.MeasureTheory.measurable_dirac_prod_infinitePi_const (ι' := ℕ) P hP
  refine ConditionallyIIDWith.intro
    (fun n => ((measurable_pi_apply n).comp measurable_snd).aemeasurable)
    (hP.comp measurable_fst) fun m k hk => ?_
  -- the joint kernel `Q ↦ δ_Q ⊗ Q^{⊗ Fin m}`, through which both sides factor
  set g : ProbabilityMeasure α → Measure (ProbabilityMeasure α × (Fin m → α)) := fun Q =>
    (Measure.dirac Q).prod (ProbabilityMeasure.pi fun _ : Fin m => Q).toMeasure with hg
  have hgmeas : Measurable g :=
    TauCeti.MeasureTheory.measurable_dirac_prod_probabilityMeasure_pi_const_toMeasure
      (fun Q : ProbabilityMeasure α => Q) measurable_id
  have hsel : Measurable fun ω : T × (ℕ → α) => (P ω.1, fun i : Fin m => ω.2 (k i)) :=
    (hP.comp measurable_fst).prodMk
      (Measurable.of_eval fun i => (measurable_pi_apply (k i)).comp measurable_snd)
  -- Each fibre of the mixture selects its block out of a countable power: `Measure.dirac_prod`
  -- turns the fibre into a pushforward of `(P t)^{⊗ℕ}`, on which the block-selection lemma applies.
  have hfib : ∀ t : T,
      ((Measure.dirac t).prod (Measure.infinitePi fun _ : ℕ => (P t : Measure α))).map
        (fun ω : T × (ℕ → α) => (P ω.1, fun i : Fin m => ω.2 (k i))) = g (P t) := by
    intro t
    rw [Measure.dirac_prod, Measure.map_map hsel measurable_prodMk_left]
    exact TauCeti.MeasureTheory.map_infinitePi_pair_block (P t) (P t) hk
  -- the left-hand side: naturality of `bind` pushes the selection through the mixture, fibre by
  -- fibre
  have hleft : (iidMixtureLaw π P).map (fun ω => (P ω.1, fun i : Fin m => ω.2 (k i)))
      = π.bind fun t => g (P t) := by
    rw [iidMixtureLaw_def, TauCeti.MeasureTheory.map_bind hker.aemeasurable hsel]
    simp_rw [hfib]
  -- the right-hand side: the mixing kernel factors through the parameter, so `bind_map` reindexes
  -- the mixture over `π`
  have hright : ((iidMixtureLaw π P).bind fun ω =>
      (Measure.dirac (P ω.1)).prod (ProbabilityMeasure.pi fun _ : Fin m => P ω.1).toMeasure)
      = π.bind fun t => g (P t) :=
    calc (iidMixtureLaw π P).bind (fun ω => g (P ω.1))
        = ((iidMixtureLaw π P).map fun ω => P ω.1).bind g :=
          (TauCeti.MeasureTheory.bind_map (hP.comp measurable_fst).aemeasurable
            hgmeas.aemeasurable).symm
      _ = (π.map P).bind g := by rw [iidMixtureLaw_map_directing hP]
      _ = π.bind fun t => g (P t) :=
          TauCeti.MeasureTheory.bind_map hP.aemeasurable hgmeas.aemeasurable
  rw [hleft, hright]

/-- The canonical process is conditionally i.i.d. (existential form). -/
theorem conditionallyIID_iidMixtureLaw (hP : Measurable P) :
    ConditionallyIID (iidMixtureLaw π P) fun n ω => ω.2 n :=
  .of_directing (conditionallyIIDWith_iidMixtureLaw hP)

/-- The prescribed family is in particular a mixing representative of the canonical process. -/
theorem mixedIIDWith_iidMixtureLaw (hP : Measurable P) :
    MixedIIDWith (iidMixtureLaw π P) (fun n ω => ω.2 n) fun ω => P ω.1 :=
  mixedIIDWith_of_conditionallyIIDWith (conditionallyIIDWith_iidMixtureLaw hP)

/-- The canonical process is exchangeable. -/
theorem exchangeable_iidMixtureLaw (hP : Measurable P) :
    Exchangeable (iidMixtureLaw π P) fun n ω => ω.2 n :=
  (mixedIIDWith_iidMixtureLaw hP).exchangeable

/-- The canonical process is contractable. -/
theorem contractable_iidMixtureLaw (hP : Measurable P) :
    Contractable (iidMixtureLaw π P) fun n ω => ω.2 n :=
  (mixedIIDWith_iidMixtureLaw hP).contractable

/-- The path law of the canonical process is the `π.map P`-mixture of infinite product measures —
the de Finetti mixture representation, here with the mixing law prescribed in advance. -/
theorem pathLaw_iidMixtureLaw [IsProbabilityMeasure π] (hP : Measurable P) :
    pathLaw (iidMixtureLaw π P) (fun n ω => ω.2 n)
      = (π.map P).bind fun Q => Measure.infinitePi fun _ : ℕ => (Q : Measure α) := by
  have := isProbabilityMeasure_iidMixtureLaw (π := π) hP
  rw [← iidMixtureLaw_map_directing hP]
  exact pathLaw_eq_bind_infinitePi_of_mixedIIDWith (mixedIIDWith_iidMixtureLaw hP)

/-- **The construction is genuinely richer than i.i.d.** If the canonical process happens to have
independent coordinates, then its mixing law `π.map P` is a point mass — so a nondegenerate `π.map
P` produces an exchangeable sequence that is *not* independent, and the directing measure the
construction supplies is genuinely random rather than an a.e. constant. -/
theorem exists_map_eq_dirac_of_iIndepFun_iidMixtureLaw [IsProbabilityMeasure π]
    (hP : Measurable P) (h : iIndepFun (fun n (ω : T × (ℕ → α)) => ω.2 n) (iidMixtureLaw π P)) :
    ∃ Q : ProbabilityMeasure α, π.map P = Measure.dirac Q := by
  have := isProbabilityMeasure_iidMixtureLaw (π := π) hP
  have hX : ∀ n, AEMeasurable (fun ω : T × (ℕ → α) => ω.2 n) (iidMixtureLaw π P) :=
    fun n => ((measurable_pi_apply n).comp measurable_snd).aemeasurable
  -- the coordinates are automatically identically distributed, the process being contractable, so
  -- independence exhibits a constant mixing representative
  have hident : ∀ i, IdentDistrib (fun ω : T × (ℕ → α) => ω.2 i)
      (fun ω : T × (ℕ → α) => ω.2 0) (iidMixtureLaw π P) (iidMixtureLaw π P) :=
    fun i => (contractable_iidMixtureLaw hP).identDistrib_coord (hX i) (hX 0)
  let Q : ProbabilityMeasure α :=
    ⟨(iidMixtureLaw π P).map fun ω => ω.2 0,
      inferInstance⟩
  refine ⟨Q, ?_⟩
  -- uniqueness of the mixing law then identifies `π.map P` with that constant's law
  rw [← iidMixtureLaw_map_directing hP,
    mixedIID_mixingLaw_unique (mixedIIDWith_iidMixtureLaw hP)
      (MixedIIDWith.of_iIndepFun_identDistrib h hident)]
  change Measure.map (fun _ : T × (ℕ → α) => Q) (iidMixtureLaw π P) = Measure.dirac Q
  rw [Measure.map_const, measure_univ, one_smul]

/-- **The prefix pushforward of the canonical mixture law.** Projecting `δ_t ⊗ (P t)^{⊗ℕ}` onto the
first `n` path coordinates leaves `δ_t ⊗ (P t)^{⊗ Fin n}`, fibre by fibre over the mixing law. -/
theorem map_prefixProjPair_iidMixtureLaw {T : Type*} [MeasurableSpace T] {π : Measure T}
    {P : T → ProbabilityMeasure α} (hP : Measurable P) (n : ℕ) :
    (iidMixtureLaw π P).map (prefixProjPair T α n)
      = π.bind fun t =>
          (Measure.dirac t).prod (ProbabilityMeasure.pi fun _ : Fin n => P t).toMeasure := by
  have hker : Measurable fun t : T =>
      (Measure.dirac t).prod (Measure.infinitePi fun _ : ℕ => (P t : Measure α)) :=
    TauCeti.MeasureTheory.measurable_dirac_prod_infinitePi_const P hP
  -- Fibre by fibre, the prefix projection turns the infinite power into the finite one.
  have hstep : ∀ t : T,
      ((Measure.dirac t).prod (Measure.infinitePi fun _ : ℕ => (P t : Measure α))).map
          (prefixProjPair T α n)
        = (Measure.dirac t).prod (ProbabilityMeasure.pi fun _ : Fin n => P t).toMeasure := by
    intro t
    have hcomp : (prefixProjPair T α n) ∘ (Prod.mk t)
        = fun x : ℕ → α => (t, fun i : Fin n => x (i : ℕ)) := by
      funext x; simp [prefixProjPair_apply]
    rw [Measure.dirac_prod,
      Measure.map_map (measurable_prefixProjPair T α n) measurable_prodMk_left, hcomp]
    exact TauCeti.MeasureTheory.map_infinitePi_pair_block t (P t) Fin.val_injective
  rw [iidMixtureLaw_def,
    TauCeti.MeasureTheory.map_bind hker.aemeasurable (measurable_prefixProjPair T α n)]
  simp_rw [hstep]

end Probability

end TauCeti

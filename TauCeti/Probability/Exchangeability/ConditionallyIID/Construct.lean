/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic
public import TauCeti.Probability.Process.IIDMixture
-- Public: `iIndepFun` appears in the hypothesis of the degeneracy theorem.
public import Mathlib.Probability.Independence.Basic
-- Non-public: the mixture representation and its uniqueness are used only inside the
-- degeneracy proof, and the Layer 0 implications only inside the corollaries.
import TauCeti.Probability.Exchangeability.MixedIID.Mixture
import TauCeti.Probability.Exchangeability.Contractability
import TauCeti.Probability.Exchangeability.IID
import TauCeti.MeasureTheory.Measure.GiryMonad

/-!
# The canonical conditionally i.i.d. process

The parameter-retaining mixture `iidMixtureLaw π P`, constructed in
`TauCeti.Probability.Process.IIDMixture`, realizes every measurable family of probability
measures as a directing measure. Its coordinate process `X n ω = ω.2 n` is conditionally
i.i.d. with directing measure `ω ↦ P ω.1`. The joint law of this directing measure and each
finite selection of distinct coordinates is the required conditional-product disintegration.

The process is consequently mixed i.i.d., exchangeable and contractable. Conversely,
independence of its coordinates forces the mixing law `π.map P` to be a point mass, so a
nondegenerate mixing law gives an exchangeable process with dependent coordinates.

## References

* Olav Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005,
  Chapter 1, Theorem 1.1.

No material is adapted from `cameronfreer/exchangeability`, whose `ConditionallyIID` names the
weaker mixture identity.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {T α : Type*} [MeasurableSpace T] [MeasurableSpace α]

variable {π : Measure T} {P : T → ProbabilityMeasure α}

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
    (Measure.dirac Q).prod (ProbabilityMeasure.pi fun _ : Fin m => Q).toMeasure
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

end Probability

end TauCeti

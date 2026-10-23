/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.PathLaw.FiniteMarginals
public import TauCeti.MeasureTheory.Measure.ProductKernel
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# Mixtures of i.i.d. path laws with a retained parameter

For a measure `π` on a parameter space `T` and a measurable family
`P : T → ProbabilityMeasure α`, `iidMixtureLaw π P` is the measure
`∫ δ_t ⊗ (P t)^{⊗ℕ} dπ(t)` on `T × (ℕ → α)`. It describes sampling the parameter first,
then sampling an i.i.d. path from its assigned probability measure.

The parameter marginal is `π`, the random probability measure has law `π.map P`, and the
path marginal is the corresponding mixture of infinite powers. Prefix projections retain
the parameter and replace the infinite power by a finite product. The noise-realization
theorem constructs this joint law by applying a measurable family of maps to independent
i.i.d. noise. These facts require no symmetry assumption on a process and no standard-Borel
hypothesis. Only probability preservation assumes that `π` is a probability measure.

The conditional-independence and exchangeability properties of the coordinate process live
in `TauCeti.Probability.Exchangeability.ConditionallyIID.Construct`.

## References

* Olav Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005,
  Chapter 1, for the conditional-product representation.

-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {T α : Type*} [MeasurableSpace T] [MeasurableSpace α]

/-- **The parameter-retaining mixture of i.i.d. laws.** Draw a parameter `t` from `π`, then sample
the coordinates i.i.d. from `P t`, keeping `t` as the first coordinate of the sample space
`T × (ℕ → α)`.

Retaining the parameter allows joint distribution statements about the sampled path and the
probability measure that generated it. -/
def iidMixtureLaw (π : Measure T) (P : T → ProbabilityMeasure α) : Measure (T × (ℕ → α)) :=
  π.bind fun t => (Measure.dirac t).prod (Measure.infinitePi fun _ : ℕ => (P t : Measure α))

/-- The canonical law unfolded as the `π`-mixture of the parameter-tagged countable powers. -/
@[simp]
theorem iidMixtureLaw_def (π : Measure T) (P : T → ProbabilityMeasure α) :
    iidMixtureLaw π P =
      π.bind fun t => (Measure.dirac t).prod (Measure.infinitePi fun _ : ℕ => (P t : Measure α)) :=
  (rfl)

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
  rw [iidMixtureLaw_def, Measure.map_bind
    (TauCeti.MeasureTheory.measurable_dirac_prod_infinitePi_const P hP).aemeasurable
    measurable_fst.aemeasurable]
  simp_rw [hfst]
  exact Measure.bind_dirac

/-- The directing measure of the canonical law has the prescribed mixing law `π.map P`. -/
theorem iidMixtureLaw_map_directing (hP : Measurable P) :
    (iidMixtureLaw π P).map (fun ω => P ω.1) = π.map P := by
  have hcomp : (fun ω : T × (ℕ → α) => P ω.1) = P ∘ Prod.fst := rfl
  rw [hcomp, ← Measure.map_map hP measurable_fst, iidMixtureLaw_map_fst hP]

/-- **Transport of the canonical law.** If the path map `g` carries each power `(P t)^{⊗ℕ}` to
`(Q (f t))^{⊗ℕ}`, then relabelling the parameter by `f` and the path by `g` carries
`iidMixtureLaw π P` to `iidMixtureLaw (π.map f) Q`. -/
theorem map_prodMap_iidMixtureLaw {T' β : Type*} [MeasurableSpace T'] [MeasurableSpace β]
    {Q : T' → ProbabilityMeasure β} {f : T → T'} {g : (ℕ → α) → ℕ → β}
    (hP : Measurable P) (hQ : Measurable Q) (hf : Measurable f) (hg : Measurable g)
    (hfib : ∀ t, (Measure.infinitePi fun _ : ℕ => (P t : Measure α)).map g =
      Measure.infinitePi fun _ : ℕ => (Q (f t) : Measure β)) :
    (iidMixtureLaw π P).map (Prod.map f g) = iidMixtureLaw (π.map f) Q := by
  rw [iidMixtureLaw_def, iidMixtureLaw_def,
    Measure.map_bind
      (TauCeti.MeasureTheory.measurable_dirac_prod_infinitePi_const P hP).aemeasurable
      (hf.prodMap hg).aemeasurable,
    Measure.bind_map hf.aemeasurable
      (TauCeti.MeasureTheory.measurable_dirac_prod_infinitePi_const Q hQ).aemeasurable]
  refine congrArg π.bind (funext fun t => ?_)
  rw [← Measure.map_prod_map _ _ hf hg, Measure.map_dirac' hf, hfib]

/-- **The canonical law from a parameter and i.i.d. noise.** Draw a parameter `t` from `π` and an
independent i.i.d. sequence `r` from `ρ`, and apply a jointly measurable `h t` to each noise
variable. If `h t` pushes `ρ` forward to `P t`, the resulting pair `(t, (h t (r i))ᵢ)` has the
canonical law `iidMixtureLaw π P`: given the parameter, the coordinates are i.i.d. `P t`. -/
theorem _root_.MeasureTheory.Measure.map_prod_infinitePi_eq_iidMixtureLaw
    {R : Type*} [MeasurableSpace R]
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

/-- The path law of the canonical process is the `π.map P`-mixture of infinite product measures.
The parameter is integrated out, leaving the mixture of the prescribed i.i.d. laws. -/
theorem pathLaw_iidMixtureLaw (hP : Measurable P) :
    pathLaw (iidMixtureLaw π P) (fun n ω => ω.2 n)
      = (π.map P).bind fun Q => Measure.infinitePi fun _ : ℕ => (Q : Measure α) := by
  rw [pathLaw_def, iidMixtureLaw_def, Measure.map_bind
    (TauCeti.MeasureTheory.measurable_dirac_prod_infinitePi_const P hP).aemeasurable
    measurable_snd.aemeasurable]
  simp only [Measure.map_snd_prod, measure_univ, one_smul]
  exact (Measure.bind_map hP.aemeasurable
    TauCeti.MeasureTheory.measurable_infinitePi_const.aemeasurable).symm

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
    Measure.map_bind hker.aemeasurable (measurable_prefixProjPair T α n).aemeasurable]
  simp_rw [hstep]

end Probability

end TauCeti

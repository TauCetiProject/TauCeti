/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Defs
public import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.HomDensity
public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.FiniteGraph.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Closeness
import TauCeti.Combinatorics.DenseGraphLimits.Sampling.Unbiased

/-!
# Empirical mixing measures of an exchangeable graph law

Every exchangeable graph law `L` produces a sequence of candidate mixing measures on the graphon
space over the unit interval: sample an `n`-vertex graph from the level-`n` marginal of `L` and
take the graphon class of its step graphon. This is the *empirical mixing measure*
`empiricalMixing L n`, the pushforward of `L.law n` along `G ↦ ⟦W_G⟧`.

The point of these measures is that they recover the upper masses of `L` in the limit. The
average of `t(F, ·)` against `empiricalMixing L n` is the mean ordinary homomorphism density
`E[t(F, G)]` of an `L`-sample `G` on `n` vertices. Its injective counterpart is exact: by
consistency of `L`, each of the `(n)_k` vertex embeddings of a `k`-vertex pattern `F` sees the
pattern with probability `upperMass F`, so `E[t₀(F, G)] = upperMass F` whenever `k ≤ n`. The two
densities differ by at most the proportion `C(k, 2) / n` of non-injective vertex maps, which gives
the **collision estimate**
`|∫ t(F, ·) d(empiricalMixing L (n + 1)) - upperMass F| ≤ C(k, 2) / (n + 1)`
and hence convergence of the empirical hom-density averages to the upper masses. Any weak limit
point of the empirical mixing measures is therefore a mixing measure with the upper masses of `L`,
which is how the Diaconis–Janson representation of exchangeable graph laws by graphon mixtures is
obtained.

## Main definitions

* `TauCeti.DenseGraphLimits.empiricalMixing` — the graphon class of an `n`-vertex sample from an
  exchangeable graph law, as a probability measure on graphon space.

## Main results

* `TauCeti.DenseGraphLimits.ExchangeableGraphLaw.integral_injHomDensity_law` — the injective
  homomorphism density of a sample from an exchangeable graph law is an unbiased estimator of the
  upper mass;
* `TauCeti.DenseGraphLimits.ExchangeableGraphLaw.abs_integral_homDensityFin_law_sub_upperMass_le` —
  the mean ordinary homomorphism density of a sample is within `C(k, 2) / n` of the upper mass;
* `TauCeti.DenseGraphLimits.integral_homDensityOnSpace_empiricalMixing` — averaging `t(F, ·)`
  against an empirical mixing measure is taking the mean homomorphism density of a sample;
* `TauCeti.DenseGraphLimits.abs_integral_homDensityOnSpace_empiricalMixing_sub_le` — the collision
  estimate;
* `TauCeti.DenseGraphLimits.tendsto_integral_homDensityOnSpace_empiricalMixing` — the empirical
  hom-density averages converge to the upper masses.

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33--61, Section 5.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012),
  Sections 5.2 and 11.3.
* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0, `Graphon/MixtureExistence.lean`. The
  empirical mixing measures and the collision estimate follow its existence argument.
-/

public section

noncomputable section

open MeasureTheory Filter Topology

namespace TauCeti

namespace DenseGraphLimits

namespace ExchangeableGraphLaw

variable (L : ExchangeableGraphLaw) {k m : ℕ}

/-- **Unbiasedness of the injective density.** The injective homomorphism density of a pattern in
a sample from an exchangeable graph law is an unbiased estimator of the pattern's upper mass,
provided the sample has at least as many vertices as the pattern: by consistency of the law, each
vertex embedding of the pattern sees it with probability equal to the upper mass. -/
theorem integral_injHomDensity_law (F : SimpleGraph (Fin k)) (hkm : k ≤ m) :
    ∫ G, injHomDensity F G ∂L.law m = L.upperMass F := by
  have hd : (m.descFactorial k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hkm).ne'
  have hf (f : Fin k ↪ Fin m) : (L.law m).real {G | F.map f ≤ G} = L.upperMass F := by
    rw [measureReal_def, ← upperMass_def, upperMass_map]
  rw [integral_injHomDensity_eq_sum_div, Finset.sum_congr rfl fun f _ => hf f, Finset.sum_const,
    nsmul_eq_mul, Finset.card_univ, Fintype.card_embedding_eq]
  simp only [Fintype.card_fin]
  exact mul_div_cancel_left₀ (L.upperMass F) hd

/-- **Near-unbiasedness of the ordinary density.** The mean ordinary homomorphism density of a
`k`-vertex pattern in an `m`-vertex sample from an exchangeable graph law is within `C(k, 2) / m` of
the pattern's upper mass: the ordinary and injective densities differ by at most the proportion of
non-injective vertex maps. -/
theorem abs_integral_homDensityFin_law_sub_upperMass_le (F : SimpleGraph (Fin k)) (hm : 0 < m) :
    |(∫ G, homDensityFin F G ∂L.law m) - L.upperMass F| ≤ (k.choose 2 : ℝ) / m := by
  rcases le_or_gt k m with hkm | hmk
  · rw [← L.integral_injHomDensity_law F hkm, ← integral_sub Integrable.of_finite
      Integrable.of_finite]
    calc
      |∫ G, homDensityFin F G - injHomDensity F G ∂L.law m|
          ≤ ∫ G, |homDensityFin F G - injHomDensity F G| ∂L.law m :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _G, (k.choose 2 : ℝ) / m ∂L.law m := by
        refine integral_mono Integrable.of_finite (integrable_const _) fun G => ?_
        simpa only [Fintype.card_fin] using homDensityFin_sub_injHomDensity_le F G
      _ = (k.choose 2 : ℝ) / m := by simp
  · -- A pattern with more vertices than the sample: both terms lie in `[0, 1]`, and the bound is
    -- at least `1` because `m ≤ C(m + 1, 2) ≤ C(k, 2)`.
    have hchoose : m ≤ k.choose 2 := by
      calc m ≤ m.choose 1 + m.choose 2 := by simp
        _ = (m + 1).choose 2 := (Nat.choose_succ_succ' m 1).symm
        _ ≤ k.choose 2 := Nat.choose_le_choose 2 hmk
    have hone : (1 : ℝ) ≤ (k.choose 2 : ℝ) / m := by
      rw [one_le_div (by exact_mod_cast hm)]
      exact_mod_cast hchoose
    have h0 : 0 ≤ ∫ G, homDensityFin F G ∂L.law m :=
      integral_nonneg fun G => homDensityFin_nonneg F G
    have h1 : ∫ G, homDensityFin F G ∂L.law m ≤ 1 := by
      calc ∫ G, homDensityFin F G ∂L.law m ≤ ∫ _G, (1 : ℝ) ∂L.law m :=
            integral_mono Integrable.of_finite (integrable_const _) fun G =>
              homDensityFin_le_one F G
        _ = 1 := by simp
    rw [abs_le]
    constructor <;> linarith [L.upperMass_nonneg F, L.upperMass_le_one F]

end ExchangeableGraphLaw

variable (L : ExchangeableGraphLaw)

/-- **Empirical mixing measures.** The graphon class of an `n`-vertex sample from an exchangeable
graph law: the pushforward of the level-`n` marginal along `G ↦ ⟦W_G⟧`, where `W_G` is the step
graphon of `G` on the unit interval. -/
def empiricalMixing (n : ℕ) : ProbabilityMeasure GraphonSpaceI :=
  ⟨(L.law n).map fun G => SeparationQuotient.mk (finiteGraphGraphon G),
    inferInstance⟩

/-- The empirical mixing measure is the pushforward of the level-`n` marginal along the graphon
class of the step graphon. -/
@[simp]
theorem toMeasure_empiricalMixing (n : ℕ) :
    (empiricalMixing L n : Measure GraphonSpaceI) =
      (L.law n).map fun G => SeparationQuotient.mk (finiteGraphGraphon G) := (rfl)

/-- Averaging a homomorphism density against an empirical mixing measure is taking the mean
homomorphism density of a sample from the law. -/
theorem integral_homDensityOnSpace_empiricalMixing {V : Type*} [Fintype V] (F : SimpleGraph V)
    [DecidableRel F.Adj] {n : ℕ} (hn : 0 < n) :
    ∫ x, homDensityOnSpace F x ∂(empiricalMixing L n : Measure GraphonSpaceI) =
      ∫ G, homDensityFin F G ∂L.law n := by
  rw [toMeasure_empiricalMixing, integral_map Measurable.of_discrete.aemeasurable
    (continuous_homDensityOnSpace F).aestronglyMeasurable]
  simp_rw [homDensityOnSpace_mk, homDensity_finiteGraphGraphon F hn]

/-- **The collision estimate.** Averaging `t(F, ·)` against the empirical mixing measure of an
exchangeable graph law at sample size `n + 1` recovers the upper mass of `F` up to
`C(k, 2) / (n + 1)`, where `k` is the number of vertices of `F`. -/
theorem abs_integral_homDensityOnSpace_empiricalMixing_sub_le (n : ℕ) {k : ℕ}
    (F : SimpleGraph (Fin k)) [DecidableRel F.Adj] :
    |(∫ x, homDensityOnSpace F x ∂(empiricalMixing L (n + 1) : Measure GraphonSpaceI)) -
        L.upperMass F| ≤ (k.choose 2 : ℝ) / (n + 1) := by
  rw [integral_homDensityOnSpace_empiricalMixing L F n.succ_pos]
  exact_mod_cast L.abs_integral_homDensityFin_law_sub_upperMass_le F n.succ_pos

/-- The average of `t(F, ·)` against the empirical mixing measures of an exchangeable graph law
converges to the upper mass of `F`. -/
theorem tendsto_integral_homDensityOnSpace_empiricalMixing {k : ℕ} (F : SimpleGraph (Fin k))
    [DecidableRel F.Adj] :
    Tendsto (fun n =>
        ∫ x, homDensityOnSpace F x ∂(empiricalMixing L (n + 1) : Measure GraphonSpaceI))
      atTop (𝓝 (L.upperMass F)) := by
  have hbound : Tendsto (fun n : ℕ => (k.choose 2 : ℝ) / (n + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (k.choose 2 : ℝ)
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _)
    (fun n => ?_) hbound)
  rw [Real.norm_eq_abs]
  exact abs_integral_homDensityOnSpace_empiricalMixing_sub_le L n F

end DenseGraphLimits

end TauCeti

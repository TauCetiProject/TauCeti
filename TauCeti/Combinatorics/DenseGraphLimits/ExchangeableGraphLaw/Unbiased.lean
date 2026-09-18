/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Defs
public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Finite
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Combinatorics.DenseGraphLimits.Sampling.Unbiased

/-!
# Homomorphism densities of samples from an exchangeable graph law

The level-`m` marginal of an exchangeable graph law `L` is a random `m`-vertex graph. This file
compares the mean homomorphism densities of such a sample with the upper masses of `L`. The
injective density is exact: by consistency of `L`, each of the `(m)_k` vertex embeddings of a
`k`-vertex pattern `F` sees the pattern with probability `upperMass F`, so
`E[t₀(F, G)] = upperMass F` whenever `k ≤ m`. The ordinary density differs from it by at most the
proportion `C(k, 2) / m` of non-injective vertex maps.

## Main results

* `TauCeti.DenseGraphLimits.ExchangeableGraphLaw.integral_injHomDensity_law` — the injective
  homomorphism density of a sample from an exchangeable graph law is an unbiased estimator of the
  upper mass;
* `TauCeti.DenseGraphLimits.ExchangeableGraphLaw.abs_integral_homDensityFin_law_sub_upperMass_le` —
  the mean ordinary homomorphism density of a sample is within `C(k, 2) / m` of the upper mass.

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33--61, Section 5.
* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0, `Graphon/MixtureExistence.lean`. The
  collision estimate follows its existence argument.
-/

public section

noncomputable section

open MeasureTheory

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
  refine integral_injHomDensity_eq_of_forall F _ (by simpa using hkm) fun f => ?_
  rw [measureReal_def, ← upperMass_def, upperMass_map]

/-- **Near-unbiasedness of the ordinary density.** The mean ordinary homomorphism density of a
`k`-vertex pattern in an `m`-vertex sample from an exchangeable graph law is within `C(k, 2) / m` of
the pattern's upper mass. The bound holds for every positive sample size, and is informative only
when `k ≤ m`, since `C(k, 2) / m ≥ 1` once `k > m`. -/
theorem abs_integral_homDensityFin_law_sub_upperMass_le (F : SimpleGraph (Fin k)) (hm : 0 < m) :
    |(∫ G, homDensityFin F G ∂L.law m) - L.upperMass F| ≤ (k.choose 2 : ℝ) / m := by
  rcases le_or_gt k m with hkm | hmk
  · rw [← L.integral_injHomDensity_law F hkm]
    simpa using abs_integral_homDensityFin_sub_integral_injHomDensity_le F (L.law m)
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

end DenseGraphLimits

end TauCeti

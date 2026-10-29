/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Contraction.Perturbation
public import TauCeti.LinearAlgebra.Submodule.CompleteFiltration

/-!
# The perturbation lemma for complete filtered contractions

The basic perturbation lemma (`TauCeti.LinearSpecialContraction.perturb`) applies to a special
contraction `(i, p, h)` of `(M, dM)` onto `(N, dN)` and a perturbation `δ` as soon as `1 + δ h`
is invertible.  Its perturbation operator `X = (1 + δ h)⁻¹ δ` is the geometric series
`∑ₙ (-1)ⁿ (δ h)ⁿ δ`, and there are two standard regimes in which that series makes sense:

* it is *pointwise finite* when `δ h` is locally nilpotent, for instance when `δ` lowers an
  exhaustive increasing filtration preserved by `h`; this is
  `Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero`;
* it is *convergent* when `M` carries a complete separated descending filtration
  `M = F 0 ⊇ F 1 ⊇ ⋯` which `h` preserves and `δ` raises, `δ (F n) ⊆ F (n + 1)`.

This file treats the second, complete filtered, regime.  There `1 + δ h` is invertible, the
perturbation operator raises the filtration and is the limit of the partial sums of its geometric
series, and the perturbed homotopy again preserves the filtration, so that the perturbed
contraction satisfies the same hypotheses and perturbations can be iterated.  The typical example
is a contraction of a bar construction completed with respect to tensor length, whose filtration
is complete by `TauCeti.CompletedTensorWords.isCompleteFiltration_filtration`.  Completeness is
only used to invert `1 + δ h`; the other results assume a descending filtration and invertibility.

## Main results

* `TauCeti.LinearSpecialContraction.isUnit_one_add_mul_homotopy_of_isCompleteFiltration`:
  `1 + δ h` is invertible, so the basic perturbation lemma applies.
* `TauCeti.LinearSpecialContraction.perturbationSeries_apply_sub_sum_mem`: the perturbation
  operator is the limit of the partial sums of `∑ₙ (-1)ⁿ (δ h)ⁿ δ`.
* `TauCeti.LinearSpecialContraction.perturbationSeries_apply_mem`: the perturbation operator
  raises the filtration.
* `TauCeti.LinearSpecialContraction.map_perturb_homotopy_le`: the perturbed homotopy
  `h - h X h` preserves the filtration.

## References

* V. K. A. M. Gugenheim, L. A. Lambe, and J. D. Stasheff, *Perturbation theory in differential
  homological algebra II*, Illinois Journal of Mathematics 35 (1991), 357--373.
* M. Crainic, *On the perturbation lemma, and deformations*, Section 2.
-/

public section

namespace TauCeti.LinearSpecialContraction

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {dM : Module.End R M} {dN : Module.End R N} (c : LinearSpecialContraction dM dN)
  (δ : Module.End R M) {F : ℕ → Submodule R M}

/-- If `h` preserves a filtration and `δ` raises it, then `δ h` raises it. -/
private theorem map_mul_homotopy_le (hh : ∀ n, (F n).map c.homotopy ≤ F n)
    (hδ : ∀ n, (F n).map δ ≤ F (n + 1)) (n : ℕ) : (F n).map (δ * c.homotopy) ≤ F (n + 1) := by
  rw [Module.End.mul_eq_comp, Submodule.map_comp]
  exact (Submodule.map_mono (hh n)).trans (hδ n)

variable (hF0 : F 0 = ⊤) (hh : ∀ n, (F n).map c.homotopy ≤ F n)
  (hδ : ∀ n, (F n).map δ ≤ F (n + 1))
include hF0 hh hδ

/-- **Invertibility in the complete filtered regime.**  If `M` carries a complete separated
filtration with `F 0 = ⊤`, preserved by the homotopy `h` and raised by the perturbation `δ`, then
`1 + δ h` is invertible, so the basic perturbation lemma `LinearSpecialContraction.perturb`
applies to `δ`. -/
theorem isUnit_one_add_mul_homotopy_of_isCompleteFiltration (hF : IsCompleteFiltration F) :
    IsUnit (1 + δ * c.homotopy) :=
  hF.isUnit_one_add hF0 (c.map_mul_homotopy_le δ hh hδ)

variable (hanti : Antitone F) (hU : IsUnit (1 + δ * c.homotopy))
include hanti hU

/-- **The perturbation operator is the sum of its geometric series.**  If `1 + δ h` is
invertible (on a complete filtration, by
`isUnit_one_add_mul_homotopy_of_isCompleteFiltration`), then on `z ∈ F m` the perturbation
operator `X = (1 + δ h)⁻¹ δ` differs from the partial sum
`∑_{j < n} (-1)ʲ (δ h)ʲ δ z` by an element of `F (m + 1 + n)`. -/
theorem perturbationSeries_apply_sub_sum_mem {m : ℕ} {z : M} (hz : z ∈ F m) (n : ℕ) :
    c.perturbationSeries δ z - ∑ j ∈ Finset.range n, ((-(δ * c.homotopy)) ^ j) (δ z) ∈
      F (m + 1 + n) := by
  rw [perturbationSeries_def, Module.End.mul_apply]
  exact Module.End.ringInverse_one_add_apply_sub_sum_mem hanti hF0
    (c.map_mul_homotopy_le δ hh hδ) hU (hδ m ⟨z, hz, rfl⟩) n

/-- The perturbation operator `X = (1 + δ h)⁻¹ δ` raises the filtration. -/
theorem perturbationSeries_apply_mem {m : ℕ} {z : M} (hz : z ∈ F m) :
    c.perturbationSeries δ z ∈ F (m + 1) := by
  rw [perturbationSeries_def, Module.End.mul_apply]
  exact Module.End.ringInverse_one_add_apply_mem hanti hF0 (c.map_mul_homotopy_le δ hh hδ) hU
    (hδ m ⟨z, hz, rfl⟩)

/-- The perturbed homotopy `h - h X h` preserves the filtration, so the perturbed contraction again
satisfies the hypotheses of the complete filtered perturbation lemma. -/
theorem map_perturb_homotopy_le (hsq : (dM + δ) ∘ₗ (dM + δ) = dM ∘ₗ dM) (n : ℕ) :
    (F n).map (c.perturb δ hsq hU).homotopy ≤ F n := by
  rintro _ ⟨z, hz, rfl⟩
  have hhz : c.homotopy z ∈ F n := hh n ⟨z, hz, rfl⟩
  have hX : c.perturbationSeries δ (c.homotopy z) ∈ F n :=
    hanti (Nat.le_succ n) (c.perturbationSeries_apply_mem δ hF0 hh hδ hanti hU hhz)
  rw [perturb_homotopy, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  exact sub_mem hhz (hh n ⟨_, hX, rfl⟩)

end TauCeti.LinearSpecialContraction

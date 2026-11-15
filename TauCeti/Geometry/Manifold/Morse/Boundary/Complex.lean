/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import TauCeti.Algebra.Homology.ChainComplex.GradedFinsupp
public import TauCeti.Algebra.Homology.EulerCharacteristic.MorseInequalities
public import TauCeti.Geometry.Manifold.Morse.Boundary.Differential
public import TauCeti.Geometry.Manifold.Morse.EulerCharacteristic

/-!
# The mod-two Morse complex and its homology

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `m`, and `X` a
pseudo-gradient adapted to `f` satisfying the Morse–Smale condition. The mod-two Morse boundary
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary` is an endomorphism of the free
`ZMod 2`-module on the critical points of `f`; it lowers the Morse index by one and squares to
zero (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_comp_morseBoundary`). This file
assembles it into the **mod-two Morse complex**
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseComplex`, a chain complex of `ZMod 2`-vector
spaces indexed by `ℕ` whose term in degree `k` is the space of chains supported on the critical
points of index `k`, built by `ChainComplex.ofGradedFinsupp`. Its homology is the mod-two Morse
homology of `(f, X)`.

The term in degree `k` has dimension the number `cₖ` of critical points of index `k`
(`finrank_morseComplex_X`), and vanishes above the dimension `m` of `M`. The algebraic Morse
inequalities for chain complexes of vector spaces
(`TauCeti.Algebra.Homology.EulerCharacteristic.MorseInequalities`) therefore apply to the Morse
homology, with Betti numbers `bₖ = dim Hₖ`:

* the **weak Morse inequalities** `bₖ ≤ cₖ`
  (`finrank_homology_morseComplex_le`);
* the **strong Morse inequalities** `bₖ - bₖ₋₁ + ⋯ ± b₀ ≤ cₖ - cₖ₋₁ + ⋯ ± c₀`
  (`sum_range_neg_one_pow_mul_finrank_homology_morseComplex_le`);
* the **Euler–Poincaré equality** `∑ᵢ (-1)ⁱ bᵢ = ∑ᵢ (-1)ⁱ cᵢ`
  (`sum_range_neg_one_pow_mul_finrank_homology_morseComplex`).

The signed count `∑ᵢ (-1)ⁱ cᵢ` does not depend on the Morse function, so neither does the Euler
characteristic of the Morse homology, and for `M` of finite CW type it is the Euler characteristic
of `M` (`sum_range_neg_one_pow_mul_finrank_homology_morseComplex_eq_eulerChar`). When the Morse
boundary vanishes, as for the moment function on the real projective plane, the Morse homology is
the space of chains, `bₖ = cₖ` (`finrank_homology_morseComplex_of_morseBoundary_eq_zero`).

These statements concern the Morse homology alone. Its identification with the singular homology
of `M`, of which the Euler characteristic identity is a numerical shadow, is not proved here.

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `morseComplex`: the mod-two Morse complex.
* `coe_morseComplex_d_hom_apply`: its differentials are restrictions of the Morse boundary.
* `finrank_morseComplex_X`: its term in degree `k` has dimension the number of critical points of
  index `k`.
* `finrank_homology_morseComplex_le`, `sum_range_neg_one_pow_mul_finrank_homology_morseComplex_le`:
  the weak and strong Morse inequalities for the Morse homology.
* `sum_range_neg_one_pow_mul_finrank_homology_morseComplex`: the Euler characteristic of the Morse
  homology is the signed count of critical points.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex and its homology).
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2 (the Morse complex).
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5 (the Morse inequalities).
-/

public section

open CategoryTheory Finsupp Module Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)

/-- **The mod-two Morse complex.** The chain complex of `ZMod 2`-vector spaces whose term in
degree `k` is the space of chains supported on the critical points of index `k`, with
differentials the restrictions of the mod-two Morse boundary, which counts the trajectories
between critical points of consecutive index modulo two. Its homology is the mod-two Morse
homology. -/
@[expose] noncomputable def morseComplex : ChainComplex (ModuleCat (ZMod 2)) ℕ :=
  ChainComplex.ofGradedFinsupp
    (fun p : criticalPoints 𝓘(ℝ, E) f ↦ manifoldMorseIndex 𝓘(ℝ, E) f p) (h.morseBoundary hf)
    (fun _ _ ↦ h.morseIndex_eq_add_one_of_morseBoundary_single_apply_ne_zero hf)
    (h.morseBoundary_comp_morseBoundary hf)

/-- The term of degree `k` of the Morse complex is the space of chains supported on the critical
points of index `k`. -/
theorem morseComplex_X (k : ℕ) :
    (h.morseComplex hf).X k = ModuleCat.of (ZMod 2) (supported (ZMod 2) (ZMod 2)
      {p : criticalPoints 𝓘(ℝ, E) f | manifoldMorseIndex 𝓘(ℝ, E) f p = k}) :=
  (rfl)

/-- The differential of the Morse complex from degree `k + 1` to degree `k` is the restriction
of the mod-two Morse boundary. -/
@[simp]
theorem coe_morseComplex_d_hom_apply (k : ℕ)
    (c : supported (ZMod 2) (ZMod 2)
      {p : criticalPoints 𝓘(ℝ, E) f | manifoldMorseIndex 𝓘(ℝ, E) f p = k + 1}) :
    Subtype.val (p := (· ∈ supported (ZMod 2) (ZMod 2)
        {p : criticalPoints 𝓘(ℝ, E) f | manifoldMorseIndex 𝓘(ℝ, E) f p = k}))
      (((h.morseComplex hf).d (k + 1) k).hom c) = h.morseBoundary hf c :=
  ChainComplex.coe_ofGradedFinsupp_d_hom_apply _ _ _ _ k c

/-- **The chain groups of the Morse complex.** Its term in degree `k` has dimension the number of
critical points of index `k`. -/
theorem finrank_morseComplex_X (k : ℕ) :
    finrank (ZMod 2) ((h.morseComplex hf).X k) = (criticalCount 𝓘(ℝ, E) f k).toNat := by
  have := hf.finite_criticalPoints.to_subtype
  rw [morseComplex, ChainComplex.finrank_ofGradedFinsupp_X,
    natCard_preimage_manifoldMorseIndex_eq_toNat_criticalCount]

/-- The terms of the Morse complex are finite-dimensional. -/
instance (k : ℕ) : Module.Finite (ZMod 2) ((h.morseComplex hf).X k) := by
  have := hf.finite_criticalPoints.to_subtype
  unfold morseComplex
  infer_instance

/-- The Morse complex vanishes above the dimension of the manifold, which bounds every Morse
index. -/
theorem isZero_morseComplex_X_of_finrank_lt {k : ℕ} (hk : finrank ℝ E < k) :
    Limits.IsZero ((h.morseComplex hf).X k) :=
  ChainComplex.isZero_ofGradedFinsupp_X _ _ _ _ fun _ hp ↦
    (manifoldMorseIndex_le_finrank.trans_lt hk).ne hp

/-- The differential of the Morse complex out of the degree above the dimension of the manifold
vanishes. -/
theorem morseComplex_d_eq_zero_of_finrank_le {k : ℕ} (hk : finrank ℝ E ≤ k) :
    (h.morseComplex hf).d (k + 1) k = 0 :=
  (h.isZero_morseComplex_X_of_finrank_lt hf (Nat.lt_succ_of_le hk)).eq_of_src _ _

/-- **The weak Morse inequalities.** The `k`-th mod-two Morse homology has dimension at most the
number of critical points of index `k`. -/
theorem finrank_homology_morseComplex_le (k : ℕ) :
    finrank (ZMod 2) ((h.morseComplex hf).homology k) ≤ (criticalCount 𝓘(ℝ, E) f k).toNat :=
  (h.morseComplex hf).finrank_homology_le_finrank_X k |>.trans_eq (h.finrank_morseComplex_X hf k)

/-- **The strong Morse inequalities.** Writing `bᵢ` for the dimension of the `i`-th mod-two Morse
homology and `cᵢ` for the number of critical points of index `i`,
`bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀`. -/
theorem sum_range_neg_one_pow_mul_finrank_homology_morseComplex_le (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ (n - i) * finrank (ZMod 2) ((h.morseComplex hf).homology i) ≤
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) * (criticalCount 𝓘(ℝ, E) f i).toNat := by
  simpa only [h.finrank_morseComplex_X hf] using
    (h.morseComplex hf).sum_range_neg_one_pow_mul_finrank_homology_le n fun _ _ ↦ inferInstance

/-- **The Euler characteristic of the Morse homology.** The alternating sum of the dimensions of
the mod-two Morse homology groups is the signed count `∑ᵢ (-1)ⁱ cᵢ` of the critical points, the
sums running over the indices up to the dimension of the manifold. -/
theorem sum_range_neg_one_pow_mul_finrank_homology_morseComplex :
    ∑ i ∈ Finset.range (finrank ℝ E + 1),
        (-1 : ℤ) ^ i * finrank (ZMod 2) ((h.morseComplex hf).homology i) =
      ∑ i ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ i * (criticalCount 𝓘(ℝ, E) f i).toNat := by
  simpa only [h.finrank_morseComplex_X hf] using
    ((h.morseComplex hf).sum_range_finrank_X_eq_sum_range_finrank_homology
      (fun _ _ ↦ inferInstance) (h.morseComplex_d_eq_zero_of_finrank_le hf le_rfl)).symm

/-- **The Euler characteristic of the Morse homology is that of the manifold.** For a compact
boundaryless manifold `M` of finite CW type, the alternating sum of the dimensions of the
mod-two Morse homology groups of any Morse–Smale pair is the Euler characteristic of `M`. -/
theorem sum_range_neg_one_pow_mul_finrank_homology_morseComplex_eq_eulerChar [FiniteCWType M] :
    ∑ i ∈ Finset.range (finrank ℝ E + 1),
        (-1 : ℤ) ^ i * finrank (ZMod 2) ((h.morseComplex hf).homology i) = eulerChar M := by
  rw [h.sum_range_neg_one_pow_mul_finrank_homology_morseComplex hf,
    hf.sum_range_neg_one_pow_mul_toNat_criticalCount_eq_eulerChar]

/-- **Morse homology with vanishing boundary.** If the mod-two Morse boundary vanishes, the `k`-th
mod-two Morse homology has dimension the number of critical points of index `k`. -/
theorem finrank_homology_morseComplex_of_morseBoundary_eq_zero (h0 : h.morseBoundary hf = 0)
    (k : ℕ) :
    finrank (ZMod 2) ((h.morseComplex hf).homology k) = (criticalCount 𝓘(ℝ, E) f k).toNat := by
  have := hf.finite_criticalPoints.to_subtype
  rw [morseComplex, ChainComplex.finrank_homology_ofGradedFinsupp_of_eq_zero _ _ _ _ h0,
    natCard_preimage_manifoldMorseIndex_eq_toNat_criticalCount]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti

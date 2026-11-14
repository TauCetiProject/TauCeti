/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Differential
public import TauCeti.Algebra.Homology.EulerCharacteristic.ChainComplex
public import TauCeti.Geometry.Manifold.Morse.EulerCharacteristic
public import Mathlib.Algebra.Field.ZMod

/-!
# The mod-two Morse chain complex of a compact manifold

Let `f` be a Morse function on a compact boundaryless manifold `M` and `X` a pseudo-gradient field
adapted to `f` satisfying the Morse–Smale condition. This file packages the mod-two Morse boundary
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary` as a chain complex of
`ZMod 2`-vector spaces graded by the Morse index, whose homology is the mod-two Morse homology of
`(f, X)`.

The term in degree `n` is the free `ZMod 2`-module on the critical points of index `n`, and the
differential from degree `n + 1` to degree `n` counts trajectories modulo two
(`IsMorseSmale.morseBoundaryAt`). Including the graded chains into all chains intertwines this
differential with the total boundary (`IsMorseSmale.mapDomain_morseBoundaryAt`), so the graded
boundary squares to zero because the total one does
(`IsMorseSmale.morseBoundary_comp_morseBoundary`).

The terms are finite-dimensional, of dimension the number `cₙ` of critical points of index `n`
(`IsMorseSmale.finrank_morseComplex_X`), and vanish above the dimension `m` of `M`. Hence the
homology is finite-dimensional, bounded by the critical counts, and vanishes above `m`. Its
Euler characteristic is the signed critical count `∑ᵢ (-1)ⁱ cᵢ`, and so the Euler characteristic
of `M` (`IsMorseSmale.sum_range_neg_one_pow_mul_finrank_homology_morseComplex_eq_eulerChar`).
In terms of Mathlib's Euler characteristics of a complex, both `(h.morseComplex hf).eulerChar` and
`(h.morseComplex hf).homologyEulerChar` are this signed count
(`IsMorseSmale.eulerChar_morseComplex`, `IsMorseSmale.homologyEulerChar_morseComplex`).
When the boundary vanishes, as it does on `ℝℙ²`, every differential of the complex vanishes
(`IsMorseSmale.morseComplex_d_eq_zero_of_morseBoundary_eq_zero`), so the homology in each degree
is the term in that degree and has dimension the number of critical points of that index
(`IsMorseSmale.finrank_homology_morseComplex_of_morseBoundary_eq_zero`).

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `morseBoundaryAt`: the mod-two Morse boundary from index `n + 1` to index `n`.
* `morseBoundaryAt_comp_morseBoundaryAt`: consecutive graded boundaries compose to zero.
* `mapDomain_morseBoundaryAt`: the graded boundary is the restriction of the total boundary.
* `morseComplex`: the mod-two Morse chain complex, indexed by `ℕ`.
* `finrank_morseComplex_X`: its term in degree `n` has dimension the number of critical points of
  index `n`.
* `finite_homology_morseComplex`: the Morse homology is finite-dimensional.
* `isZero_homology_morseComplex_of_finrank_lt`: the Morse homology vanishes above the dimension.
* `sum_range_neg_one_pow_mul_finrank_homology_morseComplex`: the Euler characteristic of the Morse
  homology is the signed count of critical points.
* `sum_range_neg_one_pow_mul_finrank_homology_morseComplex_eq_eulerChar`: it is the Euler
  characteristic of `M`.
* `eulerChar_morseComplex`, `homologyEulerChar_morseComplex`: Mathlib's Euler characteristics of
  the Morse chain complex and of its homology are the signed count of critical points.
* `eulerChar_morseComplex_eq_eulerChar`, `homologyEulerChar_morseComplex_eq_eulerChar`: they are
  the Euler characteristic of `M`.
* `morseComplex_d_eq_zero_of_morseBoundary_eq_zero`: with zero boundary, every differential of the
  Morse chain complex vanishes.
* `finrank_homology_morseComplex_of_morseBoundary_eq_zero`: with zero boundary, the Morse homology
  in degree `n` has dimension the number of critical points of index `n`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex and its homology).
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.
-/

public section

open CategoryTheory Limits Module Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)

/-- **The graded mod-two Morse boundary.** The `ZMod 2`-linear map from the free module on the
critical points of index `n + 1` to the free module on the critical points of index `n` sending
`p` to the sum of the critical points `q` of index `n`, each weighted by the number of
trajectories from `p` to `q` modulo two. -/
noncomputable def morseBoundaryAt (n : ℕ) :
    ({p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n + 1} →₀ ZMod 2) →ₗ[ZMod 2]
      ({q : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f q = n} →₀ ZMod 2) :=
  haveI := hf.finite_criticalPoints.to_subtype
  Finsupp.linearCombination (ZMod 2) fun p ↦
    Finsupp.ofSupportFinite (fun q ↦ h.morseBoundaryCoeff hf p q) (toFinite _)

/-- The coefficient of `q` in the graded Morse boundary of a chain `c` is the sum over the
critical points `p` of index `n + 1` of `c p` times the number of trajectories from `p` to `q`
modulo two. -/
theorem morseBoundaryAt_apply {n : ℕ}
    (c : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n + 1} →₀ ZMod 2)
    (q : {q : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f q = n}) :
    h.morseBoundaryAt hf n c q = c.sum fun p a ↦ a * h.morseBoundaryCoeff hf p q := by
  simp [morseBoundaryAt, Finsupp.linearCombination_apply, Finsupp.ofSupportFinite_coe]

/-- The coefficient of `q` in the graded Morse boundary of `a • p` is `a` times the number of
trajectories from `p` to `q` modulo two. -/
@[simp]
theorem morseBoundaryAt_single_apply {n : ℕ}
    (p : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n + 1}) (a : ZMod 2)
    (q : {q : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f q = n}) :
    h.morseBoundaryAt hf n (Finsupp.single p a) q = a * h.morseBoundaryCoeff hf p q := by
  rw [morseBoundaryAt_apply, Finsupp.sum_single_index (zero_mul _)]

/-- **The graded and total Morse boundaries agree.** Including the chains of index `n + 1` and of
index `n` into all Morse chains intertwines the graded boundary with the total boundary
`morseBoundary`: the boundary of a chain of index `n + 1` is a chain of index `n`. -/
@[simp]
theorem mapDomain_morseBoundaryAt {n : ℕ}
    (c : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n + 1} →₀ ZMod 2) :
    (h.morseBoundaryAt hf n c).mapDomain Subtype.val =
      h.morseBoundary hf (c.mapDomain Subtype.val) := by
  ext r
  rw [morseBoundary_apply, Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) fun _ _ _ ↦ add_mul ..]
  by_cases hr : manifoldMorseIndex 𝓘(ℝ, E) f r = n
  · exact (Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ ⟨r, hr⟩).trans
      (h.morseBoundaryAt_apply hf c ⟨r, hr⟩)
  · -- Outside index `n` both sides vanish: the left side by support, the right side because every
    -- boundary coefficient from index `n + 1` to `r` is zero.
    rw [Finsupp.mapDomain_of_notMem_range _ _ fun ⟨q, hq⟩ ↦ hr (hq ▸ q.2), Finsupp.sum]
    refine (Finset.sum_eq_zero fun p _ ↦ ?_).symm
    rw [h.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hf (by grind), mul_zero]

/-- **The graded mod-two Morse boundary squares to zero.** -/
theorem morseBoundaryAt_comp_morseBoundaryAt (n : ℕ) :
    h.morseBoundaryAt hf n ∘ₗ h.morseBoundaryAt hf (n + 1) = 0 := by
  ext p : 2
  refine Finsupp.mapDomain_injective Subtype.val_injective ?_
  simp [mapDomain_morseBoundaryAt]

/-- **The graded mod-two Morse boundary squares to zero**, applied to a chain. -/
@[simp]
theorem morseBoundaryAt_morseBoundaryAt {n : ℕ}
    (c : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n + 2} →₀ ZMod 2) :
    h.morseBoundaryAt hf n (h.morseBoundaryAt hf (n + 1) c) = 0 :=
  LinearMap.congr_fun (h.morseBoundaryAt_comp_morseBoundaryAt hf n) c

/-- **The mod-two Morse chain complex.** The chain complex of `ZMod 2`-vector spaces whose term in
degree `n` is the free module on the critical points of index `n`, with the differential
`morseBoundaryAt` counting trajectories modulo two. Its homology is the mod-two Morse homology of
`f` and the pseudo-gradient. -/
-- The body is exposed so that the terms of the complex compute to the free modules on the
-- critical points of each index, which the statements of `morseComplex_X` and `morseComplex_d`
-- need.
@[expose]
noncomputable def morseComplex : ChainComplex (ModuleCat (ZMod 2)) ℕ :=
  ChainComplex.of
    (fun n ↦ ModuleCat.of (ZMod 2)
      ({p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ ZMod 2))
    (fun n ↦ ModuleCat.ofHom (h.morseBoundaryAt hf n))
    fun n ↦ by
      rw [← ModuleCat.ofHom_comp, h.morseBoundaryAt_comp_morseBoundaryAt hf, ModuleCat.ofHom_zero]

/-- The term of the Morse chain complex in degree `n` is the free `ZMod 2`-module on the critical
points of index `n`. -/
@[simp]
theorem morseComplex_X (n : ℕ) :
    (h.morseComplex hf).X n = ModuleCat.of (ZMod 2)
      ({p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ ZMod 2) :=
  (rfl)

/-- The differential of the Morse chain complex from degree `n + 1` to degree `n` is the graded
Morse boundary. -/
@[simp]
theorem morseComplex_d (n : ℕ) :
    (h.morseComplex hf).d (n + 1) n = ModuleCat.ofHom (h.morseBoundaryAt hf n) := by
  simp [morseComplex]

/-- The differential of the Morse chain complex from degree `n + 1` to degree `n` applied to a
chain is the graded Morse boundary of that chain. -/
-- Pre-simp lemma, so that it fires before `morseComplex_d` rewrites the differential to a
-- `ModuleCat.ofHom` whose application `simp` can no longer unfold.
@[simp↓]
theorem morseComplex_d_apply (n : ℕ)
    (c : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n + 1} →₀ ZMod 2) :
    (h.morseComplex hf).d (n + 1) n c = h.morseBoundaryAt hf n c := by
  rw [morseComplex_d]
  -- The morphism `ModuleCat.ofHom g` applied to a chain is `g` applied to it, by definition.
  rfl

/-- The terms of the Morse chain complex are finite-dimensional. -/
instance finite_morseComplex_X (n : ℕ) : Module.Finite (ZMod 2) ((h.morseComplex hf).X n) := by
  have := hf.finite_criticalPoints.to_subtype
  rw [morseComplex_X]
  exact Module.Finite.finsupp

/-- **The Morse chains count critical points.** The term of the Morse chain complex in degree `n`
has dimension the number of critical points of index `n`. -/
@[simp]
theorem finrank_morseComplex_X (n : ℕ) :
    finrank (ZMod 2) ((h.morseComplex hf).X n) = (criticalCount 𝓘(ℝ, E) f n).toNat := by
  have := hf.finite_criticalPoints.to_subtype
  let _ := Fintype.ofFinite
    {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n}
  -- The carrier of `ModuleCat.of (ZMod 2) A` is `A` itself; rewriting it with `ModuleCat.coe_of`
  -- is blocked by the module instance depending on it.
  refine (finrank_finsupp_self (R := ZMod 2)).trans ?_
  rw [← Nat.card_eq_fintype_card,
    natCard_criticalPoints_manifoldMorseIndex_eq_toNat_criticalCount]

/-- The Morse chain complex vanishes above the dimension of `M`. -/
theorem isZero_morseComplex_X_of_finrank_lt {n : ℕ} (hn : finrank ℝ E < n) :
    IsZero ((h.morseComplex hf).X n) := by
  rw [morseComplex_X, ModuleCat.isZero_iff_subsingleton]
  have : IsEmpty {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} :=
    ⟨fun p ↦ (manifoldMorseIndex_le_finrank.trans_lt hn).ne p.2⟩
  infer_instance

/-- The mod-two Morse homology is finite-dimensional. -/
instance finite_homology_morseComplex (n : ℕ) :
    Module.Finite (ZMod 2) ((h.morseComplex hf).homology n) :=
  have : Module.Finite (ZMod 2) ((h.morseComplex hf).sc n).X₂ := h.finite_morseComplex_X hf n
  ((h.morseComplex hf).sc n).finite_homology

/-- **The weak Morse inequality for Morse homology.** The mod-two Morse homology in degree `n` has
dimension at most the number of critical points of index `n`. -/
theorem finrank_homology_morseComplex_le (n : ℕ) :
    finrank (ZMod 2) ((h.morseComplex hf).homology n) ≤ (criticalCount 𝓘(ℝ, E) f n).toNat :=
  (h.morseComplex hf).finrank_homology_le_finrank_X n |>.trans_eq (h.finrank_morseComplex_X hf n)

/-- The mod-two Morse homology vanishes above the dimension of `M`. -/
theorem isZero_homology_morseComplex_of_finrank_lt {n : ℕ} (hn : finrank ℝ E < n) :
    IsZero ((h.morseComplex hf).homology n) :=
  (HomologicalComplex.ExactAt.of_isZero
    (h.isZero_morseComplex_X_of_finrank_lt hf hn)).isZero_homology

/-- **The Euler characteristic of Morse homology.** The alternating sum of the dimensions of the
mod-two Morse homology groups is the signed count `∑ᵢ (-1)ⁱ cᵢ` of critical points, where `cᵢ` is
the number of critical points of index `i`. -/
theorem sum_range_neg_one_pow_mul_finrank_homology_morseComplex :
    ∑ i ∈ Finset.range (finrank ℝ E + 1),
        (-1 : ℤ) ^ i * finrank (ZMod 2) ((h.morseComplex hf).homology i) =
      ∑ i ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ i * (criticalCount 𝓘(ℝ, E) f i).toNat := by
  rw [← (h.morseComplex hf).sum_range_finrank_X_eq_sum_range_finrank_homology
    (fun i _ ↦ h.finite_morseComplex_X hf i)
    ((h.isZero_morseComplex_X_of_finrank_lt hf (Nat.lt_succ_self _)).eq_of_src _ _)]
  simp_rw [h.finrank_morseComplex_X hf]

/-- **Morse homology has the Euler characteristic of the manifold.** For a compact boundaryless
manifold `M` of finite CW type, the alternating sum of the dimensions of the mod-two Morse homology
groups is the Euler characteristic of `M`. -/
theorem sum_range_neg_one_pow_mul_finrank_homology_morseComplex_eq_eulerChar [FiniteCWType M] :
    ∑ i ∈ Finset.range (finrank ℝ E + 1),
        (-1 : ℤ) ^ i * finrank (ZMod 2) ((h.morseComplex hf).homology i) = eulerChar M := by
  rw [h.sum_range_neg_one_pow_mul_finrank_homology_morseComplex hf,
    hf.sum_range_neg_one_pow_mul_toNat_criticalCount_eq_eulerChar]

/-- **The Euler characteristic of the Morse chain complex** is the signed count `∑ᵢ (-1)ⁱ cᵢ` of
critical points, where `cᵢ` is the number of critical points of index `i`. -/
theorem eulerChar_morseComplex :
    (h.morseComplex hf).eulerChar =
      ∑ i ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ i * (criticalCount 𝓘(ℝ, E) f i).toNat := by
  rw [HomologicalComplex.eulerChar_eq_sum_finSet_of_finrankSupport_subset _
    (Finset.range (finrank ℝ E + 1)) ((GradedObject.finrankSupport_subset_iff _ _).2 fun i hi ↦
      ModuleCat.finrank_eq_zero_of_isZero
        (h.isZero_morseComplex_X_of_finrank_lt hf (by simpa [Nat.lt_succ_iff] using hi)))]
  simp

/-- **The Euler characteristic of Morse homology**, in terms of Mathlib's homological Euler
characteristic: it is the signed count `∑ᵢ (-1)ⁱ cᵢ` of critical points. -/
theorem homologyEulerChar_morseComplex :
    (h.morseComplex hf).homologyEulerChar =
      ∑ i ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ i * (criticalCount 𝓘(ℝ, E) f i).toNat := by
  rw [← ChainComplex.eulerChar_eq_homologyEulerChar _
      (Filter.eventually_atTop.2 ⟨finrank ℝ E + 1, fun _ hn ↦
        h.isZero_morseComplex_X_of_finrank_lt hf hn⟩),
    h.eulerChar_morseComplex hf]

/-- For a compact boundaryless manifold `M` of finite CW type, the Euler characteristic of the
Morse chain complex is the Euler characteristic of `M`. -/
theorem eulerChar_morseComplex_eq_eulerChar [FiniteCWType M] :
    (h.morseComplex hf).eulerChar = eulerChar M := by
  rw [h.eulerChar_morseComplex hf, hf.sum_range_neg_one_pow_mul_toNat_criticalCount_eq_eulerChar]

/-- For a compact boundaryless manifold `M` of finite CW type, the Euler characteristic of the
mod-two Morse homology is the Euler characteristic of `M`. -/
theorem homologyEulerChar_morseComplex_eq_eulerChar [FiniteCWType M] :
    (h.morseComplex hf).homologyEulerChar = eulerChar M := by
  rw [h.homologyEulerChar_morseComplex hf,
    hf.sum_range_neg_one_pow_mul_toNat_criticalCount_eq_eulerChar]

/-- If the total Morse boundary vanishes, so does every graded Morse boundary. -/
theorem morseBoundaryAt_eq_zero_of_morseBoundary_eq_zero (h0 : h.morseBoundary hf = 0) (n : ℕ) :
    h.morseBoundaryAt hf n = 0 :=
  LinearMap.ext fun c ↦ Finsupp.mapDomain_injective Subtype.val_injective <| by
    simp [mapDomain_morseBoundaryAt, h0]

/-- If the total Morse boundary vanishes, every differential of the Morse chain complex is
zero. -/
theorem morseComplex_d_eq_zero_of_morseBoundary_eq_zero (h0 : h.morseBoundary hf = 0) (i j : ℕ) :
    (h.morseComplex hf).d i j = 0 := by
  by_cases hij : (ComplexShape.down ℕ).Rel i j
  · obtain rfl : j + 1 = i := hij
    rw [morseComplex_d, h.morseBoundaryAt_eq_zero_of_morseBoundary_eq_zero hf h0,
      ModuleCat.ofHom_zero]
    -- Both sides are the zero morphism; they differ only in how the terms are written.
    rfl
  · exact (h.morseComplex hf).shape i j hij

/-- **Morse homology with zero boundary.** If the mod-two Morse boundary vanishes, the mod-two
Morse homology in degree `n` has dimension the number of critical points of index `n`. -/
theorem finrank_homology_morseComplex_of_morseBoundary_eq_zero (h0 : h.morseBoundary hf = 0)
    (n : ℕ) :
    finrank (ZMod 2) ((h.morseComplex hf).homology n) = (criticalCount 𝓘(ℝ, E) f n).toNat := by
  rw [(h.morseComplex hf).finrank_homology_eq_finrank_X_of_d_eq_zero n
      (h.morseComplex_d_eq_zero_of_morseBoundary_eq_zero hf h0 _ _)
      (h.morseComplex_d_eq_zero_of_morseBoundary_eq_zero hf h0 _ _),
    h.finrank_morseComplex_X hf]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti

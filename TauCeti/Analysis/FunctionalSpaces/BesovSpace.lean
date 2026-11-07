/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley
import TauCeti.Analysis.Normed.Lp.Basic

/-!
# Inhomogeneous Besov spaces

Let `φ : E → ℝ` be a smooth bump function on a finite-dimensional real inner product space and let
`Δⱼ` (`j ≥ 0`) be the inhomogeneous Littlewood–Paley blocks built from it
(`TemperedDistribution.littlewoodPaleyBlock`). For `s : ℝ` and `1 ≤ p, q ≤ ∞`, the
**inhomogeneous Besov space** `B^s_{p,q}` consists of the tempered distributions `u` whose blocks
`Δⱼ u` are `Lᵖ` functions with

`‖u‖_{B^s_{p,q}} = ‖(2^{js} ‖Δⱼ u‖_p)ⱼ‖_{ℓ^q} < ∞`.

The parameter `s` measures smoothness, `p` integrability and `q` is a fine index; for
`p = q = ∞` this is the Hölder–Zygmund scale `𝒞^s = B^s_{∞,∞}`. The definition is relative to the
chosen bump function `φ`.

We encode the norm through the sequence of weighted blocks `(2^{js} Δⱼ u)ⱼ`, an element of the
normed space `ℓ^q(ℕ, Lᵖ)`. A tempered distribution is determined by its blocks
(`TemperedDistribution.eq_of_forall_littlewoodPaleyBlock_eq`) and an `Lᵖ` function by its
tempered distribution, so this sequence is an injective linear image of `u`; the Besov norm is the
norm it induces. As in Mathlib's `BesselPotentialSpace`, an element of the bundled space stores
both its tempered distribution and this `Lᵖ` data.

## Main declarations

* `TemperedDistribution.MemBesov φ s p q u`: the unbundled predicate `u ∈ B^s_{p,q}`, and its
  characterisation `TemperedDistribution.memBesov_iff` by `Lᵖ` blocks with weighted `ℓ^q` norms.
* `TauCeti.BesovSpace F φ s p q`: the bundled space, a complex normed space whose elements carry
  their tempered distribution `toDistr` and weighted blocks `weightedBlocks`.
* `TauCeti.BesovSpace.block`: the block `Δⱼ u` as an `Lᵖ` function, with
  `TauCeti.BesovSpace.norm_eq_tsum_rpow` (`q < ∞`) and `TauCeti.BesovSpace.norm_eq_ciSup`
  (`q = ∞`) expressing the norm through the blocks, and the single-block bound
  `TauCeti.BesovSpace.rpow_mul_norm_block_le`.
* `TauCeti.BesovSpace.inclusion`: `B^s_{p,q} ⊆ B^{s'}_{p,q'}` with norm at most `1` for
  `s' ≤ s` and `q ≤ q'`.
* `TauCeti.BesovSpace.inclusionOfLT`: `B^s_{p,q} ⊆ B^{s'}_{p,q'}` for `s' < s` and arbitrary
  `q, q'`, with norm at most `(1 - 2^{s' - s})⁻¹`.
* `TauCeti.BesovSpace.exists_toDistr_eq_and_norm_eq`: a Schwartz function whose Fourier transform
  is carried by the region where `ψⱼ = 1` lies in every Besov space, with norm `2^{js} ‖u‖_p`;
  `TauCeti.BesovSpace.exists_toDistr_eq_and_norm_eq_of_norm_le` is the low-frequency case `j = 0`,
  where the norm is `‖u‖_p` for every `s`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Section 6.2.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Definition 2.68 and Proposition 2.71.
* H. Triebel, *Theory of Function Spaces*, Section 2.3.
-/

public section

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The norm of the Besov weight `2^x`, viewed as a complex scalar. -/
private theorem norm_two_rpow (x : ℝ) : ‖(((2 : ℝ) ^ x : ℝ) : ℂ)‖ = 2 ^ x := by
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg zero_le_two x)]

private theorem two_rpow_ne_zero (x : ℝ) : (((2 : ℝ) ^ x : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos two_pos x).ne'

/-- The complex Besov weights multiply as `2^x 2^y = 2^{x + y}`. -/
private theorem two_rpow_mul_two_rpow (x y : ℝ) :
    (((2 : ℝ) ^ x : ℝ) : ℂ) * (((2 : ℝ) ^ y : ℝ) : ℂ) = (((2 : ℝ) ^ (x + y) : ℝ) : ℂ) := by
  rw [Real.rpow_add two_pos, Complex.ofReal_mul]

namespace TemperedDistribution

section MemBesov

variable (φ : ContDiffBump (0 : E)) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)]

/-- A tempered distribution `u` lies in the **inhomogeneous Besov space** `B^s_{p,q}` built from the
Littlewood–Paley partition of `φ` if its weighted blocks `2^{js} Δⱼ u` are `Lᵖ` functions forming
an `ℓ^q` sequence. See `TemperedDistribution.memBesov_iff` for the formulation with the unweighted
blocks. -/
def MemBesov (u : 𝓢'(E, F)) : Prop :=
  ∃ v : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q,
    ∀ j : ℕ, (v j : 𝓢'(E, F)) = (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) • littlewoodPaleyBlock F φ j u

variable {φ s p q}

/-- `u ∈ B^s_{p,q}` exactly when every Littlewood–Paley block `Δⱼ u` is an `Lᵖ` function `fⱼ` and
the sequence `2^{js} ‖fⱼ‖_p` lies in `ℓ^q`. -/
theorem memBesov_iff {u : 𝓢'(E, F)} :
    u.MemBesov φ s p q ↔ ∃ f : ℕ → Lp F p (volume : Measure E),
      (∀ j, littlewoodPaleyBlock F φ j u = f j) ∧
        Memℓp (fun j : ℕ ↦ (2 : ℝ) ^ (s * j) * ‖f j‖) q := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨fun j ↦ (((2 : ℝ) ^ (-(s * j)) : ℝ) : ℂ) • v j, fun j ↦ ?_,
      (lp.memℓp v).norm.mono fun j ↦ le_of_eq ?_⟩
    · rw [← Lp.toTemperedDistributionCLM_apply, map_smul, Lp.toTemperedDistributionCLM_apply, hv,
        smul_smul, two_rpow_mul_two_rpow, neg_add_cancel, Real.rpow_zero, Complex.ofReal_one,
        one_smul]
    · rw [Real.norm_of_nonneg (by positivity), norm_smul, norm_two_rpow, ← mul_assoc,
        ← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero, one_mul]
  · rintro ⟨f, hf, hmem⟩
    refine ⟨⟨fun j ↦ (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) • f j, hmem.mono fun j ↦ le_of_eq ?_⟩,
      fun j ↦ ?_⟩
    · rw [norm_smul, norm_two_rpow]
    · -- The `j`-th entry of the anonymous `lp` element is `2^{js} • f j` by definition: `lp`
      -- coerces through `Subtype.val` and has no lemma evaluating an anonymous constructor.
      rw [hf j]
      exact map_smul (Lp.toTemperedDistributionCLM F volume p) _ (f j)

theorem MemBesov.zero : (0 : 𝓢'(E, F)).MemBesov φ s p q :=
  ⟨0, fun j ↦ by simp [← Lp.toTemperedDistributionCLM_apply]⟩

theorem MemBesov.add {u v : 𝓢'(E, F)} (hu : u.MemBesov φ s p q) (hv : v.MemBesov φ s p q) :
    (u + v).MemBesov φ s p q := by
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hv
  refine ⟨a + b, fun j ↦ ?_⟩
  rw [lp.coeFn_add, Pi.add_apply, ← Lp.toTemperedDistributionCLM_apply, map_add,
    Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistributionCLM_apply, ha, hb, map_add,
    smul_add]

theorem MemBesov.smul {u : 𝓢'(E, F)} (hu : u.MemBesov φ s p q) (c : ℂ) :
    (c • u).MemBesov φ s p q := by
  obtain ⟨a, ha⟩ := hu
  refine ⟨c • a, fun j ↦ ?_⟩
  rw [lp.coeFn_smul, Pi.smul_apply, ← Lp.toTemperedDistributionCLM_apply, map_smul,
    Lp.toTemperedDistributionCLM_apply, ha, map_smul, smul_comm]

/-- **Monotonicity of the Besov scale.** `B^s_{p,q} ⊆ B^{s'}_{p,q'}` for `s' ≤ s` and `q ≤ q'`. -/
theorem MemBesov.mono {u : 𝓢'(E, F)} {s' : ℝ} {q' : ℝ≥0∞} (hu : u.MemBesov φ s p q)
    (hs : s' ≤ s) (hq : q ≤ q') : u.MemBesov φ s' p q' := by
  obtain ⟨f, hf, hmem⟩ := memBesov_iff.1 hu
  refine memBesov_iff.2 ⟨f, hf, (hmem.of_exponent_ge hq).mono fun j ↦ ?_⟩
  rw [Real.norm_of_nonneg (by positivity)]
  gcongr
  exact one_le_two

theorem MemBesov.neg {u : 𝓢'(E, F)} (hu : u.MemBesov φ s p q) : (-u).MemBesov φ s p q := by
  simpa using hu.smul (-1)

theorem MemBesov.sub {u v : 𝓢'(E, F)} (hu : u.MemBesov φ s p q) (hv : v.MemBesov φ s p q) :
    (u - v).MemBesov φ s p q := by
  simpa [sub_eq_add_neg] using hu.add hv.neg

end MemBesov

end TemperedDistribution

namespace TauCeti

open TemperedDistribution

variable (F) in
/-- The **inhomogeneous Besov space** `B^s_{p,q}` built from the Littlewood–Paley partition of the
bump function `φ`: the tempered distributions `u` whose weighted Littlewood–Paley blocks
`2^{js} Δⱼ u` are `Lᵖ` functions forming an `ℓ^q` sequence. An element stores both `u` and this
sequence, which determine each other. For `1 ≤ q` it is a normed space with
`‖u‖ = ‖(2^{js} ‖Δⱼ u‖_p)ⱼ‖_{ℓ^q}`. -/
structure BesovSpace (φ : ContDiffBump (0 : E)) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] where
  /-- The underlying tempered distribution. -/
  toDistr : 𝓢'(E, F)
  /-- The weighted Littlewood–Paley blocks `(2^{js} Δⱼ u)ⱼ`, an `ℓ^q` sequence of `Lᵖ`
  functions. -/
  weightedBlocks : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q
  /-- The `j`-th weighted block is the `j`-th Littlewood–Paley block of `toDistr`, multiplied
  by `2^{js}`. -/
  coe_weightedBlocks_apply : ∀ j : ℕ, (weightedBlocks j : 𝓢'(E, F)) =
    (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) • littlewoodPaleyBlock F φ j toDistr

namespace BesovSpace

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The tempered distribution of an element of `B^s_{p,q}` lies in `B^s_{p,q}`. -/
theorem memBesov_toDistr (u : BesovSpace F φ s p q) : u.toDistr.MemBesov φ s p q :=
  ⟨u.weightedBlocks, u.coe_weightedBlocks_apply⟩

/-- An element of a Besov space is determined by its tempered distribution. -/
@[ext]
theorem ext {u v : BesovSpace F φ s p q} (h : u.toDistr = v.toDistr) : u = v := by
  obtain ⟨u, a, ha⟩ := u
  obtain ⟨v, b, hb⟩ := v
  obtain rfl : u = v := h
  obtain rfl : a = b := lp.ext <| funext fun j ↦
    LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot <| by
      simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply, ha, hb]
  rfl

/-- An element of a Besov space is determined by its weighted Littlewood–Paley blocks. -/
theorem weightedBlocks_injective :
    Function.Injective (weightedBlocks : BesovSpace F φ s p q → _) := by
  intro u v h
  ext1
  refine eq_of_forall_littlewoodPaleyBlock_eq φ fun j ↦ smul_right_injective _
    (two_rpow_ne_zero (s * j)) ?_
  simp only [← coe_weightedBlocks_apply, h]

instance : Zero (BesovSpace F φ s p q) where
  zero := ⟨0, 0, fun j ↦ by simp [← Lp.toTemperedDistributionCLM_apply]⟩

instance : Add (BesovSpace F φ s p q) where
  add u v := ⟨u.toDistr + v.toDistr, u.weightedBlocks + v.weightedBlocks, fun j ↦ by
    simp [← Lp.toTemperedDistributionCLM_apply, map_add, smul_add,
      ← u.coe_weightedBlocks_apply, ← v.coe_weightedBlocks_apply]⟩

instance : Neg (BesovSpace F φ s p q) where
  neg u := ⟨-u.toDistr, -u.weightedBlocks, fun j ↦ by
    simp [← Lp.toTemperedDistributionCLM_apply, map_neg, ← u.coe_weightedBlocks_apply]⟩

instance : Sub (BesovSpace F φ s p q) where
  sub u v := ⟨u.toDistr - v.toDistr, u.weightedBlocks - v.weightedBlocks, fun j ↦ by
    simp [← Lp.toTemperedDistributionCLM_apply, map_sub, smul_sub,
      ← u.coe_weightedBlocks_apply, ← v.coe_weightedBlocks_apply]⟩

instance : SMul ℂ (BesovSpace F φ s p q) where
  smul c u := ⟨c • u.toDistr, c • u.weightedBlocks, fun j ↦ by
    rw [lp.coeFn_smul, Pi.smul_apply, ← Lp.toTemperedDistributionCLM_apply, map_smul,
      Lp.toTemperedDistributionCLM_apply, u.coe_weightedBlocks_apply, map_smul, smul_comm]⟩

instance : SMul ℕ (BesovSpace F φ s p q) where
  smul n u := (n : ℂ) • u

instance : SMul ℤ (BesovSpace F φ s p q) where
  smul n u := (n : ℂ) • u

@[simp]
theorem toDistr_zero : (0 : BesovSpace F φ s p q).toDistr = 0 := (rfl)

@[simp]
theorem weightedBlocks_zero : (0 : BesovSpace F φ s p q).weightedBlocks = 0 := (rfl)

@[simp]
theorem toDistr_add (u v : BesovSpace F φ s p q) : (u + v).toDistr = u.toDistr + v.toDistr :=
  (rfl)

@[simp]
theorem weightedBlocks_add (u v : BesovSpace F φ s p q) :
    (u + v).weightedBlocks = u.weightedBlocks + v.weightedBlocks := (rfl)

@[simp]
theorem toDistr_neg (u : BesovSpace F φ s p q) : (-u).toDistr = -u.toDistr := (rfl)

@[simp]
theorem weightedBlocks_neg (u : BesovSpace F φ s p q) :
    (-u).weightedBlocks = -u.weightedBlocks := (rfl)

@[simp]
theorem toDistr_sub (u v : BesovSpace F φ s p q) : (u - v).toDistr = u.toDistr - v.toDistr :=
  (rfl)

@[simp]
theorem weightedBlocks_sub (u v : BesovSpace F φ s p q) :
    (u - v).weightedBlocks = u.weightedBlocks - v.weightedBlocks := (rfl)

@[simp]
theorem toDistr_smul (c : ℂ) (u : BesovSpace F φ s p q) : (c • u).toDistr = c • u.toDistr :=
  (rfl)

@[simp]
theorem weightedBlocks_smul (c : ℂ) (u : BesovSpace F φ s p q) :
    (c • u).weightedBlocks = c • u.weightedBlocks := (rfl)

@[simp]
theorem toDistr_nsmul (n : ℕ) (u : BesovSpace F φ s p q) : (n • u).toDistr = n • u.toDistr :=
  Nat.cast_smul_eq_nsmul ℂ n u.toDistr

@[simp]
theorem toDistr_zsmul (n : ℤ) (u : BesovSpace F φ s p q) : (n • u).toDistr = n • u.toDistr :=
  Int.cast_smul_eq_zsmul ℂ n u.toDistr

instance : AddCommGroup (BesovSpace F φ s p q) :=
  fast_instance% Function.Injective.addCommGroup toDistr (fun _ _ ↦ ext) toDistr_zero
    toDistr_add toDistr_neg toDistr_sub (fun u n ↦ toDistr_nsmul n u) fun u n ↦ toDistr_zsmul n u

instance : Module ℂ (BesovSpace F φ s p q) :=
  fast_instance% Function.Injective.module ℂ
    (⟨⟨toDistr, toDistr_zero⟩, toDistr_add⟩ : BesovSpace F φ s p q →+ 𝓢'(E, F))
    (fun _ _ ↦ ext) toDistr_smul

variable (F φ s p q) in
/-- The weighted Littlewood–Paley blocks `u ↦ (2^{js} Δⱼ u)ⱼ`, as an injective linear map into
`ℓ^q(ℕ, Lᵖ)`. -/
def weightedBlocksₗ :
    BesovSpace F φ s p q →ₗ[ℂ] lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q where
  toFun := weightedBlocks
  map_add' := weightedBlocks_add
  map_smul' := weightedBlocks_smul

@[simp]
theorem weightedBlocksₗ_apply (u : BesovSpace F φ s p q) :
    weightedBlocksₗ F φ s p q u = u.weightedBlocks := (rfl)

/-- The Littlewood–Paley block `Δⱼ u` of an element of a Besov space, as an `Lᵖ` function. -/
def block (u : BesovSpace F φ s p q) (j : ℕ) : Lp F p (volume : Measure E) :=
  (((2 : ℝ) ^ (-(s * j)) : ℝ) : ℂ) • u.weightedBlocks j

/-- The `Lᵖ` function `u.block j` is the Littlewood–Paley block `Δⱼ u`. -/
@[simp]
theorem coe_block (u : BesovSpace F φ s p q) (j : ℕ) :
    (u.block j : 𝓢'(E, F)) = littlewoodPaleyBlock F φ j u.toDistr := by
  rw [block, ← Lp.toTemperedDistributionCLM_apply, map_smul, Lp.toTemperedDistributionCLM_apply,
    coe_weightedBlocks_apply, smul_smul, two_rpow_mul_two_rpow, neg_add_cancel, Real.rpow_zero,
    Complex.ofReal_one, one_smul]

theorem weightedBlocks_apply (u : BesovSpace F φ s p q) (j : ℕ) :
    u.weightedBlocks j = (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) • u.block j := by
  rw [block, smul_smul, two_rpow_mul_two_rpow, add_neg_cancel, Real.rpow_zero, Complex.ofReal_one,
    one_smul]

theorem norm_weightedBlocks_apply (u : BesovSpace F φ s p q) (j : ℕ) :
    ‖u.weightedBlocks j‖ = 2 ^ (s * j) * ‖u.block j‖ := by
  rw [weightedBlocks_apply, norm_smul, norm_two_rpow]

/-- A tempered distribution in `B^s_{p,q}`, as an element of the bundled Besov space. -/
def _root_.TemperedDistribution.MemBesov.toBesovSpace {u : 𝓢'(E, F)}
    (hu : u.MemBesov φ s p q) : BesovSpace F φ s p q :=
  ⟨u, hu.choose, hu.choose_spec⟩

@[simp]
theorem _root_.TemperedDistribution.MemBesov.toDistr_toBesovSpace {u : 𝓢'(E, F)}
    (hu : u.MemBesov φ s p q) : hu.toBesovSpace.toDistr = u := (rfl)

section Normed

variable [Fact (1 ≤ q)]

instance : NormedAddCommGroup (BesovSpace F φ s p q) :=
  fast_instance% NormedAddCommGroup.induced _ _ (weightedBlocksₗ F φ s p q)
    (by exact weightedBlocks_injective)

/-- The Besov norm of `u` is the `ℓ^q(ℕ, Lᵖ)` norm of its weighted blocks. -/
@[simp]
theorem norm_weightedBlocks (u : BesovSpace F φ s p q) : ‖u.weightedBlocks‖ = ‖u‖ := by rfl

instance : NormedSpace ℂ (BesovSpace F φ s p q) where
  norm_smul_le c u := by simp [← norm_weightedBlocks, norm_smul]

/-- **The single-block bound.** Each weighted block `2^{js} ‖Δⱼ u‖_p` is at most `‖u‖`. -/
theorem rpow_mul_norm_block_le (u : BesovSpace F φ s p q) (j : ℕ) :
    2 ^ (s * j) * ‖u.block j‖ ≤ ‖u‖ := by
  rw [← norm_weightedBlocks_apply, ← norm_weightedBlocks]
  exact lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' _ j

/-- For `q < ∞` the Besov norm is `(∑ⱼ (2^{js} ‖Δⱼ u‖_p)^q)^{1/q}`. -/
theorem norm_eq_tsum_rpow (hq : q ≠ ∞) (u : BesovSpace F φ s p q) :
    ‖u‖ = (∑' j : ℕ, (2 ^ (s * j) * ‖u.block j‖) ^ q.toReal) ^ (1 / q.toReal) := by
  rw [← norm_weightedBlocks,
    lp.norm_eq_tsum_rpow (ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq)]
  simp_rw [norm_weightedBlocks_apply]

/-- For `q = ∞` the Besov norm is `supⱼ 2^{js} ‖Δⱼ u‖_p`. -/
theorem norm_eq_ciSup (u : BesovSpace F φ s p ∞) :
    ‖u‖ = ⨆ j : ℕ, 2 ^ (s * j) * ‖u.block j‖ := by
  rw [← norm_weightedBlocks, lp.norm_eq_ciSup]
  simp_rw [norm_weightedBlocks_apply]

end Normed

section ChangeOfOrder

variable {s' : ℝ} {q' : ℝ≥0∞}

/-- The element of `B^{s'}_{p,q'}` with the same tempered distribution as `u ∈ B^s_{p,q}`, whose
weighted blocks are those of `u` rescaled by `2^{(s' - s) j}`, assuming they lie in `ℓ^{q'}`. -/
private def changeOrder (u : BesovSpace F φ s p q)
    (h : Memℓp (fun j : ℕ ↦ (((2 : ℝ) ^ ((s' - s) * j) : ℝ) : ℂ) • u.weightedBlocks j) q') :
    BesovSpace F φ s' p q' :=
  -- The `j`-th entry of `⟨_, h⟩` is the rescaled block by definition, as in `memBesov_iff`.
  ⟨u.toDistr, ⟨_, h⟩, fun j ↦ (map_smul (Lp.toTemperedDistributionCLM F volume p) _ _).trans <| by
    rw [Lp.toTemperedDistributionCLM_apply, coe_weightedBlocks_apply, smul_smul,
      two_rpow_mul_two_rpow, ← add_mul, sub_add_cancel]⟩

private theorem changeOrder_apply (u : BesovSpace F φ s p q) (h) (j : ℕ) :
    (changeOrder (s' := s') (q' := q') u h).weightedBlocks j =
      (((2 : ℝ) ^ ((s' - s) * j) : ℝ) : ℂ) • u.weightedBlocks j := (rfl)

omit [CompleteSpace F] in
/-- For `s' ≤ s` the rescaling factor `2^{(s' - s) j}` is at most `1`. -/
private theorem norm_two_rpow_smul_le (hs : s' ≤ s) (j : ℕ) (x : Lp F p (volume : Measure E)) :
    ‖(((2 : ℝ) ^ ((s' - s) * j) : ℝ) : ℂ) • x‖ ≤ ‖x‖ := by
  rw [norm_smul, norm_two_rpow]
  exact mul_le_of_le_one_left (norm_nonneg _) <| Real.rpow_le_one_of_one_le_of_nonpos one_le_two
    (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hs) j.cast_nonneg)

private theorem memℓp_changeOrder_of_le (hs : s' ≤ s) (hq : q ≤ q') (u : BesovSpace F φ s p q) :
    Memℓp (fun j : ℕ ↦ (((2 : ℝ) ^ ((s' - s) * j) : ℝ) : ℂ) • u.weightedBlocks j) q' :=
  ((lp.memℓp u.weightedBlocks).of_exponent_ge hq).mono' fun j ↦ norm_two_rpow_smul_le hs j _

variable [Fact (1 ≤ q)] [Fact (1 ≤ q')]

private theorem norm_changeOrder_of_le (hs : s' ≤ s) (hq : q ≤ q') (u : BesovSpace F φ s p q) :
    ‖changeOrder u (memℓp_changeOrder_of_le hs hq u)‖ ≤ ‖u‖ := by
  rw [← norm_weightedBlocks, ← norm_weightedBlocks]
  set w : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q' :=
    ⟨u.weightedBlocks, (lp.memℓp u.weightedBlocks).of_exponent_ge hq⟩
  calc _ ≤ ‖w‖ := lp.norm_mono (zero_lt_one.trans_le Fact.out).ne' fun j ↦ by
          rw [changeOrder_apply]
          exact norm_two_rpow_smul_le hs j _
    _ ≤ _ := lp.norm_le_norm_of_exponent_le (zero_lt_one.trans_le Fact.out).ne' hq fun _ ↦ rfl

private theorem norm_changeOrder_apply_le (u : BesovSpace F φ s p q) (j : ℕ) :
    ‖(((2 : ℝ) ^ ((s' - s) * j) : ℝ) : ℂ) • u.weightedBlocks j‖ ≤
      ‖u‖ * ((2 : ℝ) ^ (s' - s)) ^ j := by
  rw [norm_smul, norm_two_rpow, Real.rpow_mul_natCast zero_le_two, mul_comm]
  exact mul_le_mul_of_nonneg_right
    ((lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' _ j).trans_eq
      (norm_weightedBlocks u)) (by positivity)

private theorem two_rpow_sub_lt_one (hs : s' < s) : (2 : ℝ) ^ (s' - s) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (sub_neg.2 hs)

private theorem memℓp_changeOrder_of_lt (hs : s' < s) (u : BesovSpace F φ s p q) :
    Memℓp (fun j : ℕ ↦ (((2 : ℝ) ^ ((s' - s) * j) : ℝ) : ℂ) • u.weightedBlocks j) q' := by
  refine Memℓp.of_exponent_ge (q := 1) ?_ Fact.out
  refine Memℓp.mono (memℓp_gen ?_) (norm_changeOrder_apply_le u)
  simpa [abs_of_nonneg (norm_nonneg u), abs_of_pos (Real.rpow_pos_of_pos two_pos (s' - s))] using
    (summable_geometric_of_lt_one (by positivity) (two_rpow_sub_lt_one hs)).mul_left ‖u‖

private theorem norm_changeOrder_of_lt (hs : s' < s) (u : BesovSpace F φ s p q) :
    ‖changeOrder u (memℓp_changeOrder_of_lt (q' := q') hs u)‖ ≤
      (1 - 2 ^ (s' - s))⁻¹ * ‖u‖ := by
  have hr := two_rpow_sub_lt_one hs
  have hC : 0 ≤ (1 - (2 : ℝ) ^ (s' - s))⁻¹ * ‖u‖ :=
    mul_nonneg (inv_nonneg.2 (sub_nonneg.2 hr.le)) (norm_nonneg u)
  rw [← norm_weightedBlocks]
  set w : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) 1 :=
    ⟨_, memℓp_changeOrder_of_lt (q' := 1) hs u⟩
  calc _ ≤ ‖w‖ := lp.norm_le_norm_of_exponent_le (f := w)
        (g := (changeOrder u (memℓp_changeOrder_of_lt (q' := q') hs u)).weightedBlocks)
        one_ne_zero Fact.out fun _ ↦ rfl
    _ ≤ _ := lp.norm_le_of_forall_sum_le (by simp) hC fun t ↦ ?_
  simp only [ENNReal.toReal_one, Real.rpow_one]
  calc ∑ j ∈ t, ‖w j‖ ≤ ∑ j ∈ t, ‖u‖ * ((2 : ℝ) ^ (s' - s)) ^ j :=
        Finset.sum_le_sum fun j _ ↦ norm_changeOrder_apply_le u j
    _ ≤ ∑' j, ‖u‖ * ((2 : ℝ) ^ (s' - s)) ^ j :=
        ((summable_geometric_of_lt_one (by positivity) hr).mul_left ‖u‖).sum_le_tsum t
          fun j _ ↦ by positivity
    _ = (1 - 2 ^ (s' - s))⁻¹ * ‖u‖ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hr, mul_comm]

variable (F φ p) in
/-- **Monotonicity of the Besov scale.** For `s' ≤ s` and `q ≤ q'`, `B^s_{p,q} ⊆ B^{s'}_{p,q'}`
with `‖u‖_{B^{s'}_{p,q'}} ≤ ‖u‖_{B^s_{p,q}}`. -/
def inclusion (hs : s' ≤ s) (hq : q ≤ q') : BesovSpace F φ s p q →L[ℂ] BesovSpace F φ s' p q' :=
  LinearMap.mkContinuous
    { toFun u := changeOrder u (memℓp_changeOrder_of_le hs hq u)
      map_add' _ _ := ext rfl
      map_smul' _ _ := ext rfl }
    1 fun u ↦ by simpa using norm_changeOrder_of_le hs hq u

@[simp]
theorem toDistr_inclusion (hs : s' ≤ s) (hq : q ≤ q') (u : BesovSpace F φ s p q) :
    (inclusion F φ p hs hq u).toDistr = u.toDistr := by rfl

theorem norm_inclusion_le (hs : s' ≤ s) (hq : q ≤ q') (u : BesovSpace F φ s p q) :
    ‖inclusion F φ p hs hq u‖ ≤ ‖u‖ :=
  norm_changeOrder_of_le hs hq u

variable (F φ p q q') in
/-- **Strict monotonicity of the Besov scale.** For `s' < s` and arbitrary fine indices `q, q'`,
`B^s_{p,q} ⊆ B^{s'}_{p,q'}` with `‖u‖_{B^{s'}_{p,q'}} ≤ (1 - 2^{s' - s})⁻¹ ‖u‖_{B^s_{p,q}}`: a
loss of smoothness absorbs every change of the fine index. -/
def inclusionOfLT (hs : s' < s) : BesovSpace F φ s p q →L[ℂ] BesovSpace F φ s' p q' :=
  LinearMap.mkContinuous
    { toFun u := changeOrder u (memℓp_changeOrder_of_lt hs u)
      map_add' _ _ := ext rfl
      map_smul' _ _ := ext rfl }
    (1 - 2 ^ (s' - s))⁻¹ (norm_changeOrder_of_lt hs)

@[simp]
theorem toDistr_inclusionOfLT (hs : s' < s) (u : BesovSpace F φ s p q) :
    (inclusionOfLT F φ p q q' hs u).toDistr = u.toDistr := by rfl

theorem norm_inclusionOfLT_le (hs : s' < s) (u : BesovSpace F φ s p q) :
    ‖inclusionOfLT F φ p q q' hs u‖ ≤ (1 - 2 ^ (s' - s))⁻¹ * ‖u‖ :=
  norm_changeOrder_of_lt hs u

end ChangeOfOrder

section SingleBlock

variable [Fact (1 ≤ q)]

/-- **A Schwartz function carried by one block.** If on the support of the Fourier transform of a
Schwartz function `f` the piece `ψⱼ` equals `1` and every other piece vanishes, then `f` lies in
every Besov space `B^s_{p,q}`, with norm `2^{js} ‖f‖_p`. -/
theorem exists_toDistr_eq_and_norm_eq (j : ℕ) (f : 𝓢(E, F))
    (hf : ∀ k ξ, 𝓕 f ξ ≠ 0 → φ.inhomogeneousLittlewoodPaley k ξ = if k = j then 1 else 0) :
    ∃ v : BesovSpace F φ s p q, v.toDistr = f ∧ ‖v‖ = 2 ^ (s * j) * ‖f.toLp p‖ := by
  refine ⟨⟨f, lp.single q j ((((2 : ℝ) ^ (s * j) : ℝ) : ℂ) • f.toLp p), fun k ↦ ?_⟩, rfl, ?_⟩
  · rw [littlewoodPaleyBlock_toTemperedDistributionCLM_eq_ite φ hf]
    split_ifs with hk
    · subst hk
      rw [lp.single_apply_self, ← Lp.toTemperedDistributionCLM_apply, map_smul,
        Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_toLp_eq]
    · rw [lp.single_apply_ne _ _ _ hk, smul_zero, ← Lp.toTemperedDistributionCLM_apply, map_zero]
  · rw [← norm_weightedBlocks, lp.norm_single (zero_lt_one.trans_le Fact.out), norm_smul,
      norm_two_rpow]

/-- **Low frequencies.** A Schwartz function whose Fourier transform vanishes outside the ball of
radius `φ.rIn`, where `φ = 1`, lies in every Besov space `B^s_{p,q}` with norm `‖f‖_p`,
independently of `s`. -/
theorem exists_toDistr_eq_and_norm_eq_of_norm_le (f : 𝓢(E, F))
    (hf : ∀ ξ, 𝓕 f ξ ≠ 0 → ‖ξ‖ ≤ φ.rIn) :
    ∃ v : BesovSpace F φ s p q, v.toDistr = f ∧ ‖v‖ = ‖f.toLp p‖ := by
  have hf' : ∀ k ξ, 𝓕 f ξ ≠ 0 → φ.inhomogeneousLittlewoodPaley k ξ = if k = 0 then 1 else 0 := by
    rintro (_ | k) ξ hξ
    · simpa using φ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 (hf ξ hξ))
    · simp only [Nat.add_one_ne_zero, ↓reduceIte]
      exact φ.inhomogeneousLittlewoodPaley_succ_eq_zero_of_norm_le <| (hf ξ hξ).trans <|
        le_mul_of_one_le_left φ.rIn_pos.le (one_le_pow₀ one_le_two)
  simpa using exists_toDistr_eq_and_norm_eq (s := s) (q := q) 0 f hf'

end SingleBlock

end BesovSpace

end TauCeti

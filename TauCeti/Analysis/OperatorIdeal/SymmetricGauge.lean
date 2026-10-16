/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Indicator
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Symmetric gauges on sequences

A *symmetric gauge* (a *symmetric norming function* in the terminology of Gohberg and Krein) is a
function `Φ` on finitely supported nonnegative sequences `a : ℕ →₀ ℝ≥0` that is subadditive,
positively homogeneous, invariant under permutations of the indices, monotone in the termwise
order, and normalized by `Φ (single 0 1) = 1`. Applied to the sequence of approximation numbers
of an operator, a symmetric gauge produces the norm of a symmetric operator ideal; the `ℓᵖ`
gauges produce the Schatten classes.

Every symmetric gauge lies between the supremum and the sum of the sequence,
`⨆ n, a n ≤ Φ a ≤ ∑ n, a n`. It extends to arbitrary sequences `a : ℕ → ℝ≥0∞` as the supremum of
`Φ b` over the finitely supported `b` dominated by `a`. The extension is total, lies between the
supremum and the sum of the sequence, and keeps the monotonicity, homogeneity and subadditivity
of `Φ`, as well as its permutation invariance. These laws feed the ideal-norm properties of the
induced gauge on operators; its triangle inequality additionally needs weak majorization of
approximation numbers, which this file does not provide. For a finite-valued sequence the
extension is the supremum of `Φ` along the initial truncations of the sequence, with no
monotonicity hypothesis on the sequence.

The finite counterpart, a permutation- and sign-invariant seminorm on `ι → ℝ`, is
`Seminorm.IsSymmetricGauge` in `TauCeti.Analysis.Convex.Majorization`.

## Main definitions

* `TauCeti.SymmetricGauge`: symmetric gauges on finitely supported nonnegative sequences.
* `TauCeti.SymmetricGauge.extend`: the extension `Φ∞` of a symmetric gauge to `ℕ → ℝ≥0∞`.
* `TauCeti.SymmetricGauge.supGauge`: the supremum `⨆ n, a n`, the least symmetric gauge.

## Main results

* `TauCeti.SymmetricGauge.iSup_le_apply`, `TauCeti.SymmetricGauge.apply_le_sum`:
  `⨆ n, a n ≤ Φ a ≤ ∑ n, a n`.
* `TauCeti.SymmetricGauge.extend_coe`: the extension agrees with `Φ` on finitely supported
  sequences.
* `TauCeti.SymmetricGauge.iSup_le_extend`, `TauCeti.SymmetricGauge.extend_le_tsum`:
  `⨆ n, a n ≤ Φ∞ a ≤ ∑' n, a n`.
* `TauCeti.SymmetricGauge.extend_coe_eq_iSup_indicator`: the truncation formula for finite-valued
  sequences.
* `TauCeti.SymmetricGauge.extend_mono`, `TauCeti.SymmetricGauge.extend_smul`,
  `TauCeti.SymmetricGauge.extend_add_le`, `TauCeti.SymmetricGauge.extend_comp_perm`: the extension
  is monotone, homogeneous, subadditive and permutation invariant.

## References

* I. C. Gohberg, M. G. Krein, *Introduction to the Theory of Linear Nonselfadjoint Operators in
  Hilbert Space*, Translations of Mathematical Monographs 18, AMS (1969), Chapter III.
* B. Simon, *Trace Ideals and Their Applications*, 2nd ed., Mathematical Surveys and Monographs
  120, AMS (2005).
-/

public section

open Finset
open scoped NNReal ENNReal

namespace TauCeti

/-- A **symmetric gauge** (symmetric norming function): a subadditive, positively homogeneous,
permutation-invariant and monotone function on finitely supported nonnegative sequences, normalized
by taking the value `1` on the first basis vector. -/
structure SymmetricGauge where
  /-- The underlying function on finitely supported nonnegative sequences. -/
  toFun : (ℕ →₀ ℝ≥0) → ℝ≥0
  /-- Subadditivity. -/
  map_add_le' : ∀ a b, toFun (a + b) ≤ toFun a + toFun b
  /-- Positive homogeneity. -/
  map_smul' : ∀ (c : ℝ≥0) a, toFun (c • a) = c * toFun a
  /-- Invariance under permutations of the indices. -/
  map_equivMapDomain' : ∀ (σ : Equiv.Perm ℕ) a, toFun (a.equivMapDomain σ) = toFun a
  /-- Monotonicity in the termwise order. -/
  monotone' : Monotone toFun
  /-- Normalization on the first basis vector. -/
  map_single_zero_one' : toFun (Finsupp.single 0 1) = 1

namespace SymmetricGauge

instance : FunLike SymmetricGauge (ℕ →₀ ℝ≥0) ℝ≥0 where
  coe := toFun
  coe_injective Φ Ψ h := by cases Φ; cases Ψ; congr

variable (Φ : SymmetricGauge)

@[ext]
theorem ext {Φ Ψ : SymmetricGauge} (h : ∀ a, Φ a = Ψ a) : Φ = Ψ :=
  DFunLike.ext _ _ h

@[simp]
theorem toFun_eq_coe : Φ.toFun = Φ := rfl

@[simp]
theorem coe_mk (f : (ℕ →₀ ℝ≥0) → ℝ≥0) (h₁ h₂ h₃ h₄ h₅) :
    ⇑(⟨f, h₁, h₂, h₃, h₄, h₅⟩ : SymmetricGauge) = f := rfl

theorem map_add_le (a b : ℕ →₀ ℝ≥0) : Φ (a + b) ≤ Φ a + Φ b :=
  Φ.map_add_le' a b

@[simp]
theorem map_smul (c : ℝ≥0) (a : ℕ →₀ ℝ≥0) : Φ (c • a) = c * Φ a :=
  Φ.map_smul' c a

@[simp]
theorem map_equivMapDomain (σ : Equiv.Perm ℕ) (a : ℕ →₀ ℝ≥0) :
    Φ (a.equivMapDomain σ) = Φ a :=
  Φ.map_equivMapDomain' σ a

theorem monotone : Monotone Φ :=
  Φ.monotone'

@[gcongr]
theorem mono {a b : ℕ →₀ ℝ≥0} (h : a ≤ b) : Φ a ≤ Φ b :=
  Φ.monotone h

theorem map_single_zero_one : Φ (Finsupp.single 0 1) = 1 :=
  Φ.map_single_zero_one'

@[simp]
theorem map_zero : Φ 0 = 0 := by
  simpa using Φ.map_smul 0 0

/-- A symmetric gauge takes the value `c` on every sequence with a single nonzero term `c`. -/
@[simp]
theorem map_single (n : ℕ) (c : ℝ≥0) : Φ (Finsupp.single n c) = c := by
  have : Finsupp.single n c = c • (Finsupp.single 0 1).equivMapDomain (Equiv.swap 0 n) := by
    simp [Finsupp.equivMapDomain_single, Finsupp.smul_single]
  rw [this, map_smul, map_equivMapDomain, map_single_zero_one, mul_one]

/-- The lower end of the scale: a symmetric gauge dominates the supremum of the sequence. -/
theorem iSup_le_apply (a : ℕ →₀ ℝ≥0) : ⨆ n, a n ≤ Φ a :=
  ciSup_le fun n => by
    simpa using Φ.mono (Finsupp.single_le_iff.2 le_rfl : Finsupp.single n (a n) ≤ a)

/-- The upper end of the scale: a symmetric gauge is dominated by the sum of the sequence. -/
theorem apply_le_sum (a : ℕ →₀ ℝ≥0) : Φ a ≤ ∑ n ∈ a.support, a n := by
  conv_lhs => rw [← a.sum_single]
  exact (Finset.le_sum_of_subadditive Φ Φ.map_zero.le Φ.map_add_le _ _).trans (by simp)

/-! ### The extension to arbitrary sequences -/

/-- The extension `Φ∞` of a symmetric gauge to sequences in `ℝ≥0∞`: the supremum of `Φ b` over
the finitely supported sequences `b` dominated termwise by `a`. -/
noncomputable def extend (a : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (b : ℕ →₀ ℝ≥0) (_ : ∀ n, (b n : ℝ≥0∞) ≤ a n), (Φ b : ℝ≥0∞)

theorem extend_def (a : ℕ → ℝ≥0∞) :
    Φ.extend a = ⨆ (b : ℕ →₀ ℝ≥0) (_ : ∀ n, (b n : ℝ≥0∞) ≤ a n), (Φ b : ℝ≥0∞) := (rfl)

theorem apply_le_extend {a : ℕ → ℝ≥0∞} {b : ℕ →₀ ℝ≥0} (hb : ∀ n, (b n : ℝ≥0∞) ≤ a n) :
    (Φ b : ℝ≥0∞) ≤ Φ.extend a :=
  le_iSup₂ (f := fun (b : ℕ →₀ ℝ≥0) (_ : ∀ n, (b n : ℝ≥0∞) ≤ a n) => (Φ b : ℝ≥0∞)) b hb

theorem extend_le_iff {a : ℕ → ℝ≥0∞} {c : ℝ≥0∞} :
    Φ.extend a ≤ c ↔ ∀ b : ℕ →₀ ℝ≥0, (∀ n, (b n : ℝ≥0∞) ≤ a n) → (Φ b : ℝ≥0∞) ≤ c :=
  iSup₂_le_iff

/-- On finitely supported sequences the extension is the gauge itself. -/
@[simp]
theorem extend_coe (a : ℕ →₀ ℝ≥0) : Φ.extend (fun n => a n) = Φ a :=
  le_antisymm
    ((Φ.extend_le_iff).2 fun _ hb => ENNReal.coe_le_coe.2 <| Φ.mono fun n =>
      ENNReal.coe_le_coe.1 (hb n))
    (Φ.apply_le_extend fun _ => le_rfl)

/-- The extension is monotone in the termwise order. -/
theorem extend_mono : Monotone Φ.extend := fun _ _ h =>
  (Φ.extend_le_iff).2 fun _ hb => Φ.apply_le_extend fun n => (hb n).trans (h n)

@[gcongr]
theorem extend_le_extend {a b : ℕ → ℝ≥0∞} (h : a ≤ b) : Φ.extend a ≤ Φ.extend b :=
  Φ.extend_mono h

/-- The extension dominates the supremum of the sequence. -/
theorem iSup_le_extend (a : ℕ → ℝ≥0∞) : ⨆ n, a n ≤ Φ.extend a := by
  refine iSup_le fun n => ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  refine (Φ.map_single n r ▸ Φ.apply_le_extend fun m => ?_)
  rcases eq_or_ne m n with rfl | h
  · simpa using hr.le
  · simp [Finsupp.single_eq_of_ne h]

/-- The extension is dominated by the sum of the sequence. -/
theorem extend_le_tsum (a : ℕ → ℝ≥0∞) : Φ.extend a ≤ ∑' n, a n := by
  refine (Φ.extend_le_iff).2 fun b hb => ?_
  calc (Φ b : ℝ≥0∞) ≤ ∑ n ∈ b.support, (b n : ℝ≥0∞) := by
        exact_mod_cast Φ.apply_le_sum b
    _ ≤ ∑ n ∈ b.support, a n := Finset.sum_le_sum fun n _ => hb n
    _ ≤ ∑' n, a n := ENNReal.sum_le_tsum _

@[simp]
theorem extend_zero : Φ.extend 0 = 0 :=
  nonpos_iff_eq_zero.1 <| by simpa using Φ.extend_le_tsum 0

/-- The extension vanishes exactly on the zero sequence. -/
@[simp]
theorem extend_eq_zero_iff {a : ℕ → ℝ≥0∞} : Φ.extend a = 0 ↔ a = 0 :=
  ⟨fun h => funext fun n => nonpos_iff_eq_zero.1 (h ▸ (le_iSup a n).trans (Φ.iSup_le_extend a)),
    fun h => h ▸ Φ.extend_zero⟩

private theorem extend_comp_perm_le (σ : Equiv.Perm ℕ) (a : ℕ → ℝ≥0∞) :
    Φ.extend (a ∘ σ) ≤ Φ.extend a :=
  (Φ.extend_le_iff).2 fun b hb => Φ.map_equivMapDomain σ b ▸ Φ.apply_le_extend fun n => by
    simpa [Finsupp.equivMapDomain_apply] using hb (σ.symm n)

/-- The extension is invariant under permutations of the indices. -/
@[simp]
theorem extend_comp_perm (σ : Equiv.Perm ℕ) (a : ℕ → ℝ≥0∞) : Φ.extend (a ∘ σ) = Φ.extend a :=
  le_antisymm (Φ.extend_comp_perm_le σ a) <| by
    simpa [Function.comp_assoc] using Φ.extend_comp_perm_le σ.symm (a ∘ σ)

/-- The **truncation formula**: on a finite-valued sequence, the extension is the supremum of the
gauge along the initial truncations `a^{<N}` of the sequence. -/
theorem extend_coe_eq_iSup_indicator (a : ℕ → ℝ≥0) :
    Φ.extend (fun n => a n) =
      ⨆ N, (Φ (Finsupp.indicator (range N) fun n _ => a n) : ℝ≥0∞) := by
  classical
  refine le_antisymm ((Φ.extend_le_iff).2 fun b hb => ?_) (iSup_le fun N => ?_)
  · obtain ⟨N, hN⟩ := b.support.exists_nat_subset_range
    refine le_iSup_of_le N (ENNReal.coe_le_coe.2 <| Φ.mono fun n => ?_)
    rw [Finsupp.indicator_apply]
    split_ifs with hn
    · exact ENNReal.coe_le_coe.1 (hb n)
    · exact (Finsupp.notMem_support_iff.1 fun h => hn (hN h)).le
  · refine Φ.apply_le_extend fun n => ?_
    rw [Finsupp.indicator_apply]
    split_ifs <;> simp

/-- Scaling by a finite constant: `r Φ∞(a) ≤ Φ∞(r a)`. -/
private theorem coe_mul_extend_le (r : ℝ≥0) (a : ℕ → ℝ≥0∞) :
    r * Φ.extend a ≤ Φ.extend ((r : ℝ≥0∞) • a) := by
  rw [extend_def, ENNReal.mul_iSup]
  refine iSup_le fun b => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun hb => ?_
  simpa using Φ.apply_le_extend (a := (r : ℝ≥0∞) • a) (b := r • b) fun n => by
    simpa using mul_le_mul_right (hb n) (r : ℝ≥0∞)

/-- The extension is homogeneous: `Φ∞(c a) = c Φ∞(a)` for every `c : ℝ≥0∞`. -/
@[simp]
theorem extend_smul (c : ℝ≥0∞) (a : ℕ → ℝ≥0∞) : Φ.extend (c • a) = c * Φ.extend a := by
  induction c with
  | top =>
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · obtain ⟨n, hn⟩ := Function.ne_iff.1 ha
      rw [ENNReal.top_mul (Φ.extend_eq_zero_iff.not.2 ha), eq_top_iff]
      calc ⊤ = (⊤ • a) n := by simp [ENNReal.top_mul hn]
        _ ≤ Φ.extend (⊤ • a) := (le_iSup _ n).trans (Φ.iSup_le_extend _)
  | coe r =>
    rcases eq_or_ne r 0 with rfl | hr
    · simp
    have hr' : (r : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hr
    refine le_antisymm ?_ (Φ.coe_mul_extend_le r a)
    -- Undo the scaling with `r⁻¹`.
    have h := Φ.coe_mul_extend_le r⁻¹ ((r : ℝ≥0∞) • a)
    rw [smul_smul, ENNReal.coe_inv hr, ENNReal.inv_mul_cancel hr' ENNReal.coe_ne_top,
      one_smul] at h
    calc Φ.extend ((r : ℝ≥0∞) • a)
        = r * ((r : ℝ≥0∞)⁻¹ * Φ.extend ((r : ℝ≥0∞) • a)) :=
          (ENNReal.mul_inv_cancel_left hr' ENNReal.coe_ne_top).symm
      _ ≤ r * Φ.extend a := by gcongr

/-- The extension is subadditive: `Φ∞(a + b) ≤ Φ∞(a) + Φ∞(b)`. -/
theorem extend_add_le (a b : ℕ → ℝ≥0∞) : Φ.extend (a + b) ≤ Φ.extend a + Φ.extend b := by
  refine (Φ.extend_le_iff).2 fun d hd => ?_
  -- Split `d` as `d₁ + (d - d₁)` with `d₁ = min d a` dominated by `a` and `d - d₁` by `b`.
  let d₁ : ℕ →₀ ℝ≥0 := Finsupp.ofSupportFinite (fun n => (min (d n : ℝ≥0∞) (a n)).toNNReal)
    (d.support.finite_toSet.subset fun n hn =>
      Finsupp.mem_support_iff.2 fun h => hn (by simp [h]))
  have h₁ (n : ℕ) : (d₁ n : ℝ≥0∞) = min (d n : ℝ≥0∞) (a n) :=
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))
  have hle : d₁ ≤ d := fun n => ENNReal.coe_le_coe.1 (h₁ n ▸ min_le_left _ _)
  calc (Φ d : ℝ≥0∞) = Φ (d₁ + (d - d₁)) := by rw [add_tsub_cancel_of_le hle]
    _ ≤ Φ d₁ + Φ (d - d₁) := by exact_mod_cast Φ.map_add_le _ _
    _ ≤ Φ.extend a + Φ.extend b := by
      refine add_le_add (Φ.apply_le_extend fun n => h₁ n ▸ min_le_right _ _)
        (Φ.apply_le_extend fun n => ?_)
      rw [Finsupp.tsub_apply, ENNReal.coe_sub, h₁, tsub_le_iff_left, ← min_add_add_right]
      exact le_min le_self_add (hd n)

/-! ### The supremum gauge -/

/-- The supremum `⨆ n, a n` of a finitely supported sequence, as a symmetric gauge. It is the
least symmetric gauge (`TauCeti.SymmetricGauge.iSup_le_apply`), and its extension is the supremum
of an arbitrary sequence (`TauCeti.SymmetricGauge.extend_supGauge`). -/
noncomputable def supGauge : SymmetricGauge where
  toFun a := ⨆ n, a n
  map_add_le' a b := ciSup_le fun n =>
    add_le_add (le_ciSup a.finite_range.bddAbove n) (le_ciSup b.finite_range.bddAbove n)
  map_smul' c a := by simp [NNReal.mul_iSup]
  map_equivMapDomain' σ a := by
    simpa [Finsupp.equivMapDomain_apply] using σ.symm.iSup_comp (g := fun n => a n)
  monotone' a b h := ciSup_mono b.finite_range.bddAbove h
  map_single_zero_one' := le_antisymm
    (ciSup_le fun n => by rcases eq_or_ne n 0 with rfl | h <;> simp [*])
    (le_ciSup_of_le (Finsupp.finite_range _).bddAbove 0 (by simp))

@[simp]
theorem supGauge_apply (a : ℕ →₀ ℝ≥0) : supGauge a = ⨆ n, a n := (rfl)

/-- The extension of the supremum gauge is the supremum of the sequence. -/
@[simp]
theorem extend_supGauge (a : ℕ → ℝ≥0∞) : supGauge.extend a = ⨆ n, a n := by
  refine le_antisymm ((supGauge.extend_le_iff).2 fun b hb => ?_) (supGauge.iSup_le_extend a)
  rw [supGauge_apply, ENNReal.coe_iSup b.finite_range.bddAbove]
  exact iSup_mono hb

end SymmetricGauge

end TauCeti

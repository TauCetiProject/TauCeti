/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.SimpleFunc.Dense
import TauCeti.MeasureTheory.Function.StronglyMeasurable.SpanningSets

/-!
# Extending an operator from `L² ∩ Lᵖ` to `Lᵖ`

An operator initially defined on `L²` often admits an `Lᵖ` estimate on functions in both spaces.
For `1 < p < ∞`, the intersection is dense in `Lᵖ`: finite-measure simple functions lie in
both spaces. A uniform estimate therefore gives a unique bounded operator on all of `Lᵖ`.
This is the final density step in the Calderón–Zygmund strong-type theorem.

The construction uses Mathlib's `Lp.simpleFunc.dense` and `LinearMap.extendOfNorm`.

When the operator is composed with multiplication by an unbounded function `b`, as in a
commutator `[b, T]`, the dense domain must also keep `b u` in `L^q`. On a σ-finite measure space,
for `p < ∞` and a.e. strongly measurable `b`, the `u ∈ Lᵖ` with `u ∈ L^q` and `b u ∈ L^q`, which
form the submodule `MeasureTheory.memLpSmulSubmodule b q`, are dense in `Lᵖ` for every `q`
(`MeasureTheory.dense_memLpSmulSubmodule`): truncating `u` to the sets of finite measure
where `‖u‖` and `|b|` are bounded gives such functions converging to `u` in `Lᵖ`. An `Lᵖ` bound
for `b T u - T (b u)` on these `u` therefore extends it uniquely to a bounded operator on `Lᵖ`
(`ContinuousLinearMap.exists_continuousLinearMap_apply_ae_eq_smul_sub`).

## Bounds from simple functions

An `Lᵖ → L^q` bound for a bounded operator `T : Lʳ → Lˢ`, `r < ∞`, `1 ≤ p < ∞`, needs only to be
checked on simple functions in `Lʳ`: it then holds for every `f ∈ Lʳ ∩ Lᵖ`
(`ContinuousLinearMap.eLpNorm_apply_le_of_forall_simpleFunc`). The simple approximants of `f`
converge to `f` in `Lʳ` and `Lᵖ` at once, and Fatou's lemma bounds `‖T f‖_q`. The operator norm
bound itself reads `‖T f‖_s ≤ M ‖f‖_r` in `eLpNorm` form
(`ContinuousLinearMap.eLpNorm_apply_le_of_norm_le`).
-/

public section

noncomputable section

namespace MeasureTheory

open scoped ENNReal NNReal

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E] {p : ℝ≥0∞}

variable [NormedSpace ℝ E]

/-- The `Lᵖ` functions which also belong to `L²`. -/
def lpTwoSubmodule : Submodule ℝ (Lp E p μ) where
  carrier := {f | MemLp (f : α → E) 2 μ}
  zero_mem' := by
    -- Unfold submodule membership to the `MemLp` condition on the zero `Lp` class.
    change MemLp ((0 : Lp E p μ) : α → E) 2 μ
    exact (MemLp.zero : MemLp (0 : α → E) 2 μ).ae_eq
      (Lp.coeFn_zero E p μ).symm
  add_mem' := by
    intro f g hf hg
    exact (hf.add hg).ae_eq (Lp.coeFn_add f g).symm
  smul_mem' := by
    intro c f hf
    exact (hf.const_smul c).ae_eq (Lp.coeFn_smul c f).symm

/-- Membership in `Lᵖ ∩ L²` means that the `Lᵖ` representative also has finite `L²` norm. -/
theorem mem_lpTwoSubmodule (f : Lp E p μ) :
    f ∈ lpTwoSubmodule (E := E) (p := p) (μ := μ) ↔ MemLp (f : α → E) 2 μ :=
  Iff.rfl

/-- The `L²` membership proof carried by an element of `Lᵖ ∩ L²`. -/
theorem lpTwoSubmodule.memLp (f : lpTwoSubmodule (E := E) (p := p) (μ := μ)) :
    MemLp (f.val : α → E) 2 μ := f.property

/-- An `Lᵖ ∩ L²` function, read as an element of `L²`. -/
def lpTwoSubmodule.toL2 : lpTwoSubmodule (E := E) (p := p) (μ := μ) →ₗ[ℝ] Lp E 2 μ where
  toFun f := (lpTwoSubmodule.memLp f).toLp (f.val : α → E)
  map_add' := by
    intro f g
    apply Lp.ext
    have hfg := lpTwoSubmodule.memLp (f + g)
    have hf := lpTwoSubmodule.memLp f
    have hg := lpTwoSubmodule.memLp g
    filter_upwards [hfg.coeFn_toLp, hf.coeFn_toLp, hg.coeFn_toLp,
      Lp.coeFn_add (f.val : Lp E p μ) g.val,
      Lp.coeFn_add (hf.toLp (f.val : α → E)) (hg.toLp (g.val : α → E))]
      with x h₁ h₂ h₃ h₄ h₅
    calc
      _ = (f.val : α → E) x + (g.val : α → E) x := h₁.trans h₄
      _ = (hf.toLp (f.val : α → E) : α → E) x +
          (hg.toLp (g.val : α → E) : α → E) x := by rw [h₂, h₃]
      _ = _ := h₅.symm
  map_smul' := by
    intro c f
    apply Lp.ext
    have hcf := lpTwoSubmodule.memLp (c • f)
    have hf := lpTwoSubmodule.memLp f
    filter_upwards [hcf.coeFn_toLp, hf.coeFn_toLp,
      Lp.coeFn_smul c (f.val : Lp E p μ),
      Lp.coeFn_smul c (hf.toLp (f.val : α → E))] with x h₁ h₂ h₃ h₄
    calc
      _ = ((c • f).val : α → E) x := h₁
      _ = c • (f.val : α → E) x := h₃
      _ = c • (hf.toLp (f.val : α → E) : α → E) x := by rw [h₂]
      _ = _ := h₄.symm

/-- The `L²` and `Lᵖ` views of an intersection function agree almost everywhere. -/
theorem lpTwoSubmodule.toL2_ae (f : lpTwoSubmodule (E := E) (p := p) (μ := μ)) :
    (lpTwoSubmodule.toL2 f : α → E) =ᵐ[μ] (f.val : α → E) := by
  have hf := lpTwoSubmodule.memLp f
  exact hf.coeFn_toLp

/-- The `u ∈ Lᵖ` with `u ∈ L^q` and `b u ∈ L^q`. On a σ-finite measure space this subspace is
dense in `Lᵖ` for `p < ∞` and a.e. strongly measurable `b`
(`MeasureTheory.dense_memLpSmulSubmodule`). -/
def memLpSmulSubmodule (b : α → ℝ) (q : ℝ≥0∞) : Submodule ℝ (Lp E p μ) where
  carrier := {u | MemLp u q μ ∧ MemLp (fun x => b x • u x) q μ}
  zero_mem' := by
    refine ⟨MemLp.zero.ae_eq (Lp.coeFn_zero E p μ).symm, MemLp.zero.ae_eq ?_⟩
    filter_upwards [Lp.coeFn_zero E p μ] with x h
    simp only [h, Pi.zero_apply, smul_zero]
  add_mem' {u v} hu hv := by
    refine ⟨(hu.1.add hv.1).ae_eq (Lp.coeFn_add u v).symm, (hu.2.add hv.2).ae_eq ?_⟩
    filter_upwards [Lp.coeFn_add u v] with x h
    simp only [h, Pi.add_apply, smul_add]
  smul_mem' c u hu := by
    refine ⟨(hu.1.const_smul c).ae_eq (Lp.coeFn_smul c u).symm, (hu.2.const_smul c).ae_eq ?_⟩
    filter_upwards [Lp.coeFn_smul c u] with x h
    simp only [h, Pi.smul_apply, smul_comm c (b x)]

/-- Membership in `memLpSmulSubmodule b q` means that `u` and `b u` have finite `L^q` norm. -/
theorem mem_memLpSmulSubmodule {b : α → ℝ} {q : ℝ≥0∞} {u : Lp E p μ} :
    u ∈ memLpSmulSubmodule (μ := μ) b q ↔ MemLp u q μ ∧ MemLp (fun x => b x • u x) q μ :=
  Iff.rfl

/-- An element `u` of `memLpSmulSubmodule b q`, read as the pair `(u, b u)` in `L^q × L^q`. -/
def memLpSmulSubmodule.toLpPair (b : α → ℝ) (q : ℝ≥0∞) :
    memLpSmulSubmodule (E := E) (p := p) (μ := μ) b q →ₗ[ℝ] Lp E q μ × Lp E q μ where
  toFun u := ((mem_memLpSmulSubmodule.1 u.property).1.toLp u,
    (mem_memLpSmulSubmodule.1 u.property).2.toLp fun x => b x • u.val x)
  map_add' u v := by
    rw [Prod.mk_add_mk, ← MemLp.toLp_add, ← MemLp.toLp_add]
    congr 1
    · exact MemLp.toLp_congr _ _ (Lp.coeFn_add u.val v.val)
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [Lp.coeFn_add u.val v.val] with x h
    simp only [Submodule.coe_add, h, Pi.add_apply, smul_add]
  map_smul' c u := by
    rw [RingHom.id_apply, Prod.smul_mk, ← MemLp.toLp_const_smul, ← MemLp.toLp_const_smul]
    congr 1
    · exact MemLp.toLp_congr _ _ (Lp.coeFn_smul c u.val)
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [Lp.coeFn_smul c u.val] with x h
    simp only [Submodule.coe_smul, h, Pi.smul_apply, smul_comm (b x) c]

/-- The first component of `toLpPair b q u` is `u` almost everywhere. -/
theorem memLpSmulSubmodule.toLpPair_fst_ae {b : α → ℝ} {q : ℝ≥0∞}
    (u : memLpSmulSubmodule (E := E) (p := p) (μ := μ) b q) :
    ((toLpPair b q u).1 : α → E) =ᵐ[μ] (u : Lp E p μ) :=
  (mem_memLpSmulSubmodule.1 u.property).1.coeFn_toLp

/-- The second component of `toLpPair b q u` is `b u` almost everywhere. -/
theorem memLpSmulSubmodule.toLpPair_snd_ae {b : α → ℝ} {q : ℝ≥0∞}
    (u : memLpSmulSubmodule (E := E) (p := p) (μ := μ) b q) :
    ((toLpPair b q u).2 : α → E) =ᵐ[μ] fun x => b x • (u : Lp E p μ) x :=
  (mem_memLpSmulSubmodule.1 u.property).2.coeFn_toLp

variable [Fact (1 ≤ p)]

/-- The intersection `Lᵖ ∩ L²` is dense in `Lᵖ` when `p < ∞`. -/
theorem dense_lpTwoSubmodule (hp : p ≠ ∞) :
    Dense (lpTwoSubmodule (E := E) (p := p) (μ := μ) : Set (Lp E p μ)) :=
  Lp.dense_setOf_memLp hp 2

/-- A function `φ`, truncated to `Sₖ = spanningSets μ k ∩ {‖φ‖ ≤ k, |b| ≤ k}`, lies in every
`Lʳ`, and so does its product with `b`: both are bounded and vanish off a set of finite measure.
(The sup norm of `(φ x, b x)` is the larger of `‖φ x‖` and `|b x|`.) -/
private theorem memLp_indicator_and_memLp_smul_indicator [SigmaFinite μ]
    {φ : α → E} (hφ : StronglyMeasurable φ) {b : α → ℝ} (hb : StronglyMeasurable b) (k : ℕ)
    (r : ℝ≥0∞) :
    MemLp ((spanningSets μ k ∩ {x | ‖((φ x, b x) : E × ℝ)‖ ≤ k}).indicator φ) r μ ∧
      MemLp (fun x => b x • (spanningSets μ k ∩ {x | ‖((φ x, b x) : E × ℝ)‖ ≤ k}).indicator
        φ x) r μ := by
  set S := spanningSets μ k ∩ {x | ‖((φ x, b x) : E × ℝ)‖ ≤ k}
  have hS : MeasurableSet S := measurableSet_spanningSets_inter_norm_le (hφ.prodMk hb) k
  have hzero (x : α) (hx : x ∉ spanningSets μ k) : S.indicator φ x = 0 :=
    Set.indicator_of_notMem (s := S) (fun h => hx h.1) _
  have hk := (measure_spanningSets_lt_top μ k).ne
  refine ⟨memLp_of_norm_le_of_measure_support_ne_top (c := k)
      (hφ.indicator hS).aestronglyMeasurable (.of_forall fun x => ?_) hk hzero r,
    memLp_of_norm_le_of_measure_support_ne_top (u := fun x => b x • S.indicator φ x)
      (c := k * k) (hb.aestronglyMeasurable.smul (hφ.indicator hS).aestronglyMeasurable)
      (.of_forall fun x => ?_) hk (fun x hx => by rw [hzero x hx, smul_zero]) r⟩
  · by_cases hx : x ∈ S
    · simpa [hx] using (norm_fst_le ((φ x, b x) : E × ℝ)).trans hx.2
    · simp [hx]
  · by_cases hx : x ∈ S
    · rw [norm_smul, Set.indicator_of_mem hx]
      exact mul_le_mul ((norm_snd_le ((φ x, b x) : E × ℝ)).trans hx.2)
        ((norm_fst_le ((φ x, b x) : E × ℝ)).trans hx.2) (norm_nonneg _) (Nat.cast_nonneg k)
    · simp [hx, mul_nonneg]

/-- On a σ-finite measure space, let `p < ∞` and let `b` be a real a.e. strongly measurable
function. For every exponent `q`, the functions `u ∈ Lᵖ` with `u ∈ L^q` and `b u ∈ L^q` are dense
in `Lᵖ`. This is a dense domain on which an operator given on `L^q` can be composed with
multiplication by an unbounded `b`, as in the commutator `[b, T]` of a singular integral
operator `T` with a function `b` of bounded mean oscillation. -/
theorem dense_memLpSmulSubmodule [SigmaFinite μ] {b : α → ℝ}
    (hb : AEStronglyMeasurable b μ) (hp : p ≠ ∞) (q : ℝ≥0∞) :
    Dense (memLpSmulSubmodule (E := E) (p := p) (μ := μ) b q : Set (Lp E p μ)) := by
  intro φ
  -- Truncate `φ` to `Sₖ = spanningSets μ k ∩ {‖φ‖ ≤ k, |b'| ≤ k}`, where `b' = b` a.e. is
  -- strongly measurable. The truncations converge to `φ` in `Lᵖ` by dominated convergence.
  set b' := hb.mk b
  set S : ℕ → Set α := fun k => spanningSets μ k ∩ {x | ‖((φ x, b' x) : E × ℝ)‖ ≤ k}
  set φs : ℕ → α → E := fun k => (S k).indicator φ
  have hφs (k : ℕ) (r : ℝ≥0∞) : MemLp (φs k) r μ ∧ MemLp (fun x => b' x • φs k x) r μ :=
    memLp_indicator_and_memLp_smul_indicator (Lp.stronglyMeasurable φ)
      hb.stronglyMeasurable_mk k r
  have hmem (k : ℕ) : (hφs k p).1.toLp (φs k) ∈ memLpSmulSubmodule (μ := μ) b q := by
    refine mem_memLpSmulSubmodule.2
      ⟨(hφs k q).1.ae_eq (hφs k p).1.coeFn_toLp.symm, (hφs k q).2.ae_eq ?_⟩
    filter_upwards [hb.ae_eq_mk, (hφs k p).1.coeFn_toLp] with x h₁ h₂
    rw [h₁, h₂]
  refine mem_closure_of_tendsto (TauCeti.tendsto_toLp_of_ae_tendsto_of_norm_le (l := Filter.atTop)
    hp (fun k => (hφs k p).1) Filter.EventuallyEq.rfl
    (fun k => .of_forall fun x => norm_indicator_le_norm_self _ _) (.of_forall fun x => ?_))
    (.of_forall hmem)
  have hlim : Filter.Tendsto (fun k => (S k).indicator (fun x => ((φ x, b' x) : E × ℝ)) x)
      Filter.atTop (nhds (φ x, b' x)) :=
    tendsto_indicator_spanningSets_inter_norm_le _ x
  refine ((continuous_fst.tendsto _).comp hlim).congr fun k => ?_
  by_cases hx : x ∈ S k
  · simp only [Function.comp_apply, φs, Set.indicator_of_mem hx]
  · simp only [Function.comp_apply, φs, Set.indicator_of_notMem hx, Prod.fst_zero]

end MeasureTheory

namespace ContinuousLinearMap

open MeasureTheory
open scoped ENNReal NNReal

variable {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {p : ℝ≥0∞}

/-- A strong-type estimate on `L²` makes the operator's value an `Lᵖ` function whenever its
argument lies in `L² ∩ Lᵖ`. -/
theorem memLp_apply_of_eLpNorm_le (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (C : ℝ≥0)
    (hT : ∀ f : Lp E 2 μ, MemLp f p μ →
      eLpNorm (T f) p μ ≤ C * eLpNorm f p μ)
    (f : Lp E 2 μ) (hf : MemLp f p μ) : MemLp (T f) p μ := by
  exact (hT f hf).trans_lt (ENNReal.mul_lt_top (by finiteness) hf)

/-- The strong-type operator on the dense intersection, with values read in `Lᵖ`. -/
def strongTypeOnIntersection (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (C : ℝ≥0)
    (hT : ∀ f : Lp E 2 μ, MemLp f p μ →
      eLpNorm (T f) p μ ≤ C * eLpNorm f p μ) :
    lpTwoSubmodule (E := E) (p := p) (μ := μ) →ₗ[ℝ] Lp F p μ where
  toFun f := (memLp_apply_of_eLpNorm_le T C hT (lpTwoSubmodule.toL2 f)
    (by
      have hf := lpTwoSubmodule.memLp f
      exact (Lp.memLp f.val).ae_eq hf.coeFn_toLp.symm)).toLp (T (lpTwoSubmodule.toL2 f))
  map_add' := by
    intro f g
    apply Lp.ext
    let hfg := memLp_apply_of_eLpNorm_le T C hT (lpTwoSubmodule.toL2 (f + g))
      (by
        have h := lpTwoSubmodule.memLp (f + g)
        exact (Lp.memLp (f + g).val).ae_eq h.coeFn_toLp.symm)
    let hf := memLp_apply_of_eLpNorm_le T C hT (lpTwoSubmodule.toL2 f)
      (by
        have h := lpTwoSubmodule.memLp f
        exact (Lp.memLp f.val).ae_eq h.coeFn_toLp.symm)
    let hg := memLp_apply_of_eLpNorm_le T C hT (lpTwoSubmodule.toL2 g)
      (by
        have h := lpTwoSubmodule.memLp g
        exact (Lp.memLp g.val).ae_eq h.coeFn_toLp.symm)
    filter_upwards [hfg.coeFn_toLp, hf.coeFn_toLp, hg.coeFn_toLp,
      Lp.coeFn_add (T (lpTwoSubmodule.toL2 f)) (T (lpTwoSubmodule.toL2 g)),
      Lp.coeFn_add (hf.toLp _) (hg.toLp _)] with x h₁ h₂ h₃ h₄ h₅
    calc
      _ = (T (lpTwoSubmodule.toL2 (f + g)) : α → F) x := h₁
      _ = ((T (lpTwoSubmodule.toL2 f) + T (lpTwoSubmodule.toL2 g) : Lp F 2 μ) : α → F) x :=
        by rw [map_add, map_add]
      _ = (T (lpTwoSubmodule.toL2 f) : α → F) x +
          (T (lpTwoSubmodule.toL2 g) : α → F) x := h₄
      _ = (hf.toLp _ : α → F) x + (hg.toLp _ : α → F) x := by rw [h₂, h₃]
      _ = _ := h₅.symm
  map_smul' := by
    intro c f
    apply Lp.ext
    let hcf := memLp_apply_of_eLpNorm_le T C hT (lpTwoSubmodule.toL2 (c • f))
      (by
        have h := lpTwoSubmodule.memLp (c • f)
        exact (Lp.memLp (c • f).val).ae_eq h.coeFn_toLp.symm)
    let hf := memLp_apply_of_eLpNorm_le T C hT (lpTwoSubmodule.toL2 f)
      (by
        have h := lpTwoSubmodule.memLp f
        exact (Lp.memLp f.val).ae_eq h.coeFn_toLp.symm)
    filter_upwards [hcf.coeFn_toLp, hf.coeFn_toLp,
      Lp.coeFn_smul c (T (lpTwoSubmodule.toL2 f)), Lp.coeFn_smul c (hf.toLp _)]
      with x h₁ h₂ h₃ h₄
    calc
      _ = (T (lpTwoSubmodule.toL2 (c • f)) : α → F) x := h₁
      _ = (c • T (lpTwoSubmodule.toL2 f) : Lp F 2 μ) x := by rw [map_smul, map_smul]
      _ = c • (T (lpTwoSubmodule.toL2 f) : α → F) x := h₃
      _ = c • (hf.toLp _ : α → F) x := by rw [h₂]
      _ = _ := h₄.symm

/-- On the intersection, the strong-type map has the same pointwise values almost everywhere
as the given `L²` operator. -/
theorem strongTypeOnIntersection_ae (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (C : ℝ≥0)
    (hT : ∀ f : Lp E 2 μ, MemLp f p μ →
      eLpNorm (T f) p μ ≤ C * eLpNorm f p μ)
    (f : lpTwoSubmodule (E := E) (p := p) (μ := μ)) :
    (strongTypeOnIntersection T C hT f : α → F) =ᵐ[μ] T (lpTwoSubmodule.toL2 f) := by
  have hf : MemLp (lpTwoSubmodule.toL2 f : α → E) p μ :=
    (Lp.memLp f.val).ae_eq (lpTwoSubmodule.toL2_ae f).symm
  exact (memLp_apply_of_eLpNorm_le T C hT (lpTwoSubmodule.toL2 f) hf).coeFn_toLp

variable [Fact (1 ≤ p)]

/-- The `Lᵖ` bound on `L² ∩ Lᵖ`, expressed in ordinary operator norms. -/
theorem norm_strongTypeOnIntersection_le (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (C : ℝ≥0)
    (hT : ∀ f : Lp E 2 μ, MemLp f p μ →
      eLpNorm (T f) p μ ≤ C * eLpNorm f p μ)
    (f : lpTwoSubmodule (E := E) (p := p) (μ := μ)) :
    ‖strongTypeOnIntersection T C hT f‖ ≤ C * ‖f‖ := by
  have hf := lpTwoSubmodule.memLp f
  have hfp : MemLp (lpTwoSubmodule.toL2 f : α → E) p μ :=
    (Lp.memLp f.val).ae_eq hf.coeFn_toLp.symm
  have hTp := memLp_apply_of_eLpNorm_le T C hT (lpTwoSubmodule.toL2 f) hfp
  -- The bundled map applies by turning its `L²` value into the corresponding `Lᵖ` class.
  change ‖hTp.toLp (T (lpTwoSubmodule.toL2 f))‖ ≤ (C : ℝ) * ‖(f : Lp E p μ)‖
  exact hTp.norm_toLp_le_of_eLpNorm_le hf.coeFn_toLp (hT _ hfp)

variable [CompleteSpace F]

/-- The unique continuous `Lᵖ` extension of an `L²` operator satisfying a strong-type
estimate. It agrees with the original operator on `L² ∩ Lᵖ`. -/
def strongTypeExtension (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (C : ℝ≥0)
    (hT : ∀ f : Lp E 2 μ, MemLp f p μ →
      eLpNorm (T f) p μ ≤ C * eLpNorm f p μ) (_hp : p ≠ ∞) :
    Lp E p μ →L[ℝ] Lp F p μ :=
  (strongTypeOnIntersection T C hT).extendOfNorm (lpTwoSubmodule (E := E) (p := p) (μ := μ)).subtype

/-- On the dense intersection the extension equals the original `L²` operator, interpreted in
`Lᵖ`. -/
theorem strongTypeExtension_apply (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (C : ℝ≥0)
    (hT : ∀ f : Lp E 2 μ, MemLp f p μ →
      eLpNorm (T f) p μ ≤ C * eLpNorm f p μ) (hp : p ≠ ∞)
    (f : lpTwoSubmodule (E := E) (p := p) (μ := μ)) :
    strongTypeExtension T C hT hp f.val = strongTypeOnIntersection T C hT f := by
  apply LinearMap.extendOfNorm_eq
  · exact (denseRange_subtypeVal).2 (dense_lpTwoSubmodule (E := E) (p := p) (μ := μ) hp)
  · exact ⟨C, norm_strongTypeOnIntersection_le T C hT⟩

/-- The operator norm of the extended map is bounded by the strong-type constant. -/
theorem norm_strongTypeExtension_le (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (C : ℝ≥0)
    (hT : ∀ f : Lp E 2 μ, MemLp f p μ →
      eLpNorm (T f) p μ ≤ C * eLpNorm f p μ) (hp : p ≠ ∞) :
    ‖strongTypeExtension T C hT hp‖ ≤ C := by
  apply LinearMap.opNorm_extendOfNorm_le
  · exact (denseRange_subtypeVal).2 (dense_lpTwoSubmodule (E := E) (p := p) (μ := μ) hp)
  · exact C.property
  · exact norm_strongTypeOnIntersection_le T C hT

/-- The `Lᵖ` extension agrees almost everywhere with the original `L²` operator on every
function in `L² ∩ Lᵖ`. -/
theorem strongTypeExtension_apply_of_memLp (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (C : ℝ≥0)
    (hT : ∀ f : Lp E 2 μ, MemLp f p μ →
      eLpNorm (T f) p μ ≤ C * eLpNorm f p μ) (hp : p ≠ ∞)
    (f : Lp E 2 μ) (hf : MemLp f p μ) :
    (strongTypeExtension T C hT hp (hf.toLp f) : α → F) =ᵐ[μ] T f := by
  have h2 : MemLp (hf.toLp f : α → E) 2 μ :=
    (Lp.memLp f).ae_eq hf.coeFn_toLp.symm
  let g : lpTwoSubmodule (E := E) (p := p) (μ := μ) := ⟨hf.toLp f, h2⟩
  have hg : lpTwoSubmodule.toL2 g = f :=
    Lp.ext (h2.coeFn_toLp.trans hf.coeFn_toLp)
  rw [strongTypeExtension_apply T C hT hp ⟨hf.toLp f, h2⟩]
  simpa only [hg] using strongTypeOnIntersection_ae T C hT g

/-- A bounded operator on `Lᵖ` agreeing with the strong-type estimate on the dense intersection
is the extension constructed above. -/
theorem strongTypeExtension_unique (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (C : ℝ≥0)
    (hT : ∀ f : Lp E 2 μ, MemLp f p μ →
      eLpNorm (T f) p μ ≤ C * eLpNorm f p μ) (hp : p ≠ ∞)
    (S : Lp E p μ →L[ℝ] Lp F p μ)
    (hS : ∀ f : lpTwoSubmodule (E := E) (p := p) (μ := μ),
      S f.val = strongTypeOnIntersection T C hT f) :
    S = strongTypeExtension T C hT hp := by
  symm
  apply LinearMap.extendOfNorm_unique
    ((denseRange_subtypeVal).2 (dense_lpTwoSubmodule (E := E) (p := p) (μ := μ) hp))
    C (norm_strongTypeOnIntersection_le T C hT)
  apply LinearMap.ext
  intro f
  exact hS f

/-- Agreement almost everywhere on every `L² ∩ Lᵖ` function characterizes the `Lᵖ` extension. -/
theorem strongTypeExtension_unique_of_ae (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (C : ℝ≥0)
    (hT : ∀ f : Lp E 2 μ, MemLp f p μ →
      eLpNorm (T f) p μ ≤ C * eLpNorm f p μ) (hp : p ≠ ∞)
    (S : Lp E p μ →L[ℝ] Lp F p μ)
    (hS : ∀ (f : Lp E 2 μ) (hf : MemLp f p μ),
      (S (hf.toLp f) : α → F) =ᵐ[μ] T f) :
    S = strongTypeExtension T C hT hp := by
  apply strongTypeExtension_unique T C hT hp S
  intro g
  have h₂ := lpTwoSubmodule.memLp g
  have hp' : MemLp (lpTwoSubmodule.toL2 g : α → E) p μ :=
    (Lp.memLp g.val).ae_eq h₂.coeFn_toLp.symm
  have heq : hp'.toLp (lpTwoSubmodule.toL2 g : α → E) = g.val :=
    Lp.ext (hp'.coeFn_toLp.trans h₂.coeFn_toLp)
  have hSg := hS (lpTwoSubmodule.toL2 g) hp'
  rw [heq] at hSg
  have hEg := strongTypeExtension_apply_of_memLp T C hT hp (lpTwoSubmodule.toL2 g) hp'
  rw [heq, strongTypeExtension_apply T C hT hp g] at hEg
  exact Lp.ext (hSg.trans hEg.symm)

end ContinuousLinearMap

/-! ### Extending an operator composed with multiplication

For a bounded operator `T` on `L^q` and an unbounded real function `b`, the expression
`b T f - T (b f)`, as in a commutator `[b, T]`, is defined a priori only for `f ∈ L^q` with
`b f ∈ L^q`. An `Lᵖ` bound for it on the dense set of such `f ∈ Lᵖ` extends it uniquely to a
bounded operator on `Lᵖ` (`ContinuousLinearMap.exists_continuousLinearMap_apply_ae_eq_smul_sub`). -/

namespace ContinuousLinearMap

open MeasureTheory
open scoped ENNReal NNReal

variable {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {p : ℝ≥0∞}

/-- The map `u ↦ b T u - T (b u)` on `memLpSmulSubmodule b q`, with values in `Lᵖ`, given that
it takes values in `Lᵖ`. -/
private def memLpSmulSubmodule.smulSub {q : ℝ≥0∞} [Fact (1 ≤ q)] (T : Lp E q μ →L[ℝ] Lp F q μ)
    {b : α → ℝ} (hmem : ∀ u : memLpSmulSubmodule (E := E) (p := p) (μ := μ) b q,
      MemLp (fun x => b x • T (memLpSmulSubmodule.toLpPair b q u).1 x -
        T (memLpSmulSubmodule.toLpPair b q u).2 x) p μ) :
    memLpSmulSubmodule (E := E) (p := p) (μ := μ) b q →ₗ[ℝ] Lp F p μ where
  toFun u := (hmem u).toLp _
  map_add' u v := by
    refine (MemLp.toLp_congr _ _ ?_).trans (MemLp.toLp_add _ _)
    filter_upwards [Lp.coeFn_add (T (memLpSmulSubmodule.toLpPair b q u).1)
        (T (memLpSmulSubmodule.toLpPair b q v).1),
      Lp.coeFn_add (T (memLpSmulSubmodule.toLpPair b q u).2)
        (T (memLpSmulSubmodule.toLpPair b q v).2)] with x h₁ h₂
    simp only [map_add, Prod.fst_add, Prod.snd_add, Pi.add_apply, h₁, h₂, smul_add]
    abel
  map_smul' a u := by
    refine (MemLp.toLp_congr _ _ ?_).trans (MemLp.toLp_const_smul _ _)
    filter_upwards [Lp.coeFn_smul a (T (memLpSmulSubmodule.toLpPair b q u).1),
      Lp.coeFn_smul a (T (memLpSmulSubmodule.toLpPair b q u).2)] with x h₁ h₂
    simp only [map_smul, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply, h₁, h₂,
      smul_sub, smul_comm (b x) a]

private theorem memLpSmulSubmodule.smulSub_apply {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (T : Lp E q μ →L[ℝ] Lp F q μ) {b : α → ℝ}
    (hmem : ∀ u : memLpSmulSubmodule (E := E) (p := p) (μ := μ) b q,
      MemLp (fun x => b x • T (memLpSmulSubmodule.toLpPair b q u).1 x -
        T (memLpSmulSubmodule.toLpPair b q u).2 x) p μ)
    (u : memLpSmulSubmodule (E := E) (p := p) (μ := μ) b q) :
    memLpSmulSubmodule.smulSub T hmem u = (hmem u).toLp _ :=
  rfl

/-- **Extension of an operator composed with multiplication.** Let `1 ≤ p < ∞`, let `T` be a
bounded operator on `L^q` of a σ-finite measure space, and let `b` be a real a.e. strongly
measurable function. If `‖b T f - T g‖_p ≤ B ‖f‖_p` for all `f, g ∈ L^q` with `g = b f` and
`f ∈ Lᵖ`, as for a commutator `[b, T]`, then there is a bounded operator `S` on `Lᵖ` with
`‖S‖ ≤ B` and `S f = b T f - T g` for all such `f, g`. These `f` are dense in `Lᵖ`
(`MeasureTheory.dense_memLpSmulSubmodule`), so `S` is the only bounded operator with the
latter property. -/
theorem exists_continuousLinearMap_apply_ae_eq_smul_sub [SigmaFinite μ] [Fact (1 ≤ p)]
    [CompleteSpace F] {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (T : Lp E q μ →L[ℝ] Lp F q μ) {b : α → ℝ} (hb : AEStronglyMeasurable b μ) (hp : p ≠ ∞)
    {B : ℝ≥0} (hB : ∀ f g : Lp E q μ, MemLp f p μ → g =ᵐ[μ] (fun x => b x • f x) →
      eLpNorm (fun x => b x • T f x - T g x) p μ ≤ B * eLpNorm f p μ) :
    ∃ S : Lp E p μ →L[ℝ] Lp F p μ, ‖S‖ ≤ B ∧
      (∀ (f g : Lp E q μ) (hf : MemLp f p μ), g =ᵐ[μ] (fun x => b x • f x) →
        S (hf.toLp f) =ᵐ[μ] fun x => b x • T f x - T g x) ∧
      ∀ S' : Lp E p μ →L[ℝ] Lp F p μ,
        (∀ (f g : Lp E q μ) (hf : MemLp f p μ), g =ᵐ[μ] (fun x => b x • f x) →
          S' (hf.toLp f) =ᵐ[μ] fun x => b x • T f x - T g x) → S' = S := by
  set D := memLpSmulSubmodule (E := E) (p := p) (μ := μ) b q
  set j := memLpSmulSubmodule.toLpPair (E := E) (p := p) (μ := μ) b q
  -- `j u = (u, b u)`, read in `L^q × L^q`.
  have hj₁ (u : D) : ((j u).1 : α → E) =ᵐ[μ] u := memLpSmulSubmodule.toLpPair_fst_ae u
  have hj₂ (u : D) : ((j u).2 : α → E) =ᵐ[μ] fun x => b x • (j u).1 x := by
    filter_upwards [memLpSmulSubmodule.toLpPair_snd_ae u, hj₁ u] with x h₁ h₂
    rw [h₂]
    exact h₁
  have hjp (u : D) : MemLp (j u).1 p μ := (Lp.memLp u.val).ae_eq (hj₁ u).symm
  have hmem (u : D) : MemLp (fun x => b x • T (j u).1 x - T (j u).2 x) p μ :=
    (hB _ _ (hjp u) (hj₂ u)).trans_lt (ENNReal.mul_lt_top (by finiteness) (hjp u))
  set c := memLpSmulSubmodule.smulSub T hmem
  have hc (u : D) : c u =ᵐ[μ] fun x => b x • T (j u).1 x - T (j u).2 x := (hmem u).coeFn_toLp
  have hnorm (u : D) : ‖c u‖ ≤ B * ‖D.subtype u‖ := by
    rw [memLpSmulSubmodule.smulSub_apply, Submodule.subtype_apply]
    exact (hmem u).norm_toLp_le_of_eLpNorm_le (hj₁ u) (hB _ _ (hjp u) (hj₂ u))
  have hdense : DenseRange D.subtype :=
    denseRange_subtypeVal.2 (dense_memLpSmulSubmodule hb hp q)
  refine ⟨c.extendOfNorm D.subtype, LinearMap.opNorm_extendOfNorm_le hdense B.property hnorm,
    fun f g hf hg => ?_, fun S' hS' => ?_⟩
  · -- `f`, read in `Lᵖ`, lies in `D`, and `j` sends it back to `(f, g)`.
    have hu : hf.toLp f ∈ D := mem_memLpSmulSubmodule.2
      ⟨(Lp.memLp f).ae_eq hf.coeFn_toLp.symm, (Lp.memLp g).ae_eq (hg.trans
        (by filter_upwards [hf.coeFn_toLp] with x h; rw [h]))⟩
    have hju : j ⟨_, hu⟩ = (f, g) := by
      refine Prod.ext (Lp.ext ((hj₁ _).trans hf.coeFn_toLp)) (Lp.ext ((hj₂ _).trans ?_))
      filter_upwards [hj₁ ⟨_, hu⟩, hf.coeFn_toLp, hg] with x h₁ h₂ h₃
      rw [h₁, h₂, h₃]
    have h := LinearMap.extendOfNorm_eq hdense ⟨B, hnorm⟩ ⟨_, hu⟩
    rw [Submodule.subtype_apply, Submodule.coe_mk] at h
    rw [h]
    simpa only [hju] using hc ⟨_, hu⟩
  · refine (LinearMap.extendOfNorm_unique hdense B hnorm S'
      (LinearMap.ext fun u => Lp.ext ?_)).symm
    have hu : (hjp u).toLp (j u).1 = u.val := Lp.ext ((hjp u).coeFn_toLp.trans (hj₁ u))
    have h := hS' (j u).1 (j u).2 (hjp u) (hj₂ u)
    rw [hu] at h
    exact h.trans (hc u).symm

end ContinuousLinearMap

/-! ### Bounds from simple functions -/

namespace ContinuousLinearMap

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

variable {α β 𝕜 E F : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α}
  {ν : Measure β} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {p q r s : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ s)]

/-- An operator norm bound `‖T‖ ≤ M` for `T : Lʳ → Lˢ` is the bound `‖T f‖_s ≤ M ‖f‖_r` in
`eLpNorm` form. -/
theorem eLpNorm_apply_le_of_norm_le (T : Lp E r μ →L[𝕜] Lp F s ν) {M : ℝ≥0} (hT : ‖T‖ ≤ M)
    (f : Lp E r μ) : eLpNorm (T f) s ν ≤ M * eLpNorm f r μ := by
  rw [← Lp.eNorm_def, ← Lp.eNorm_def]
  refine T.le_of_opENorm_le ?_ f
  rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal hT

/-- A bound for `T : Lʳ → Lˢ`, `r < ∞`, from `Lᵖ` to `L^q`, `1 ≤ p < ∞`, on simple functions in
`Lʳ` passes to every `f ∈ Lʳ ∩ Lᵖ`, for any constant `C`. -/
theorem eLpNorm_apply_le_of_forall_simpleFunc [MeasurableSpace E] [BorelSpace E] (hr : r ≠ ∞)
    (T : Lp E r μ →L[𝕜] Lp F s ν) (hp1 : 1 ≤ p) (hp : p ≠ ∞) {C : ℝ≥0∞}
    (h : ∀ (g : SimpleFunc α E) (hg : MemLp g r μ), eLpNorm (T (hg.toLp g)) q ν ≤
      C * eLpNorm g p μ)
    (f : Lp E r μ) (hf : MemLp f p μ) : eLpNorm (T f) q ν ≤ C * eLpNorm f p μ := by
  have hfm := Lp.aestronglyMeasurable f
  -- If `C = ∞`, the bound is trivial unless `eLpNorm f p μ = 0`, that is `f = 0`.
  by_cases hC : C = ∞
  · rcases eq_or_ne (eLpNorm f p μ) 0 with h0 | h0
    · have hf0 : f = 0 := Lp.ext (((eLpNorm_eq_zero_iff
        (zero_lt_one.trans_le hp1).ne').1 h0).trans (Lp.coeFn_zero E r μ).symm)
      rw [hf0, map_zero, eLpNorm_congr_ae (Lp.coeFn_zero F s ν), eLpNorm_zero]
      exact zero_le
    · rw [hC, ENNReal.top_mul h0]
      exact le_top
  set φ := hfm.mk f
  have hφ : Measurable φ := hfm.stronglyMeasurable_mk.measurable
  have := hfm.stronglyMeasurable_mk.separableSpace_range_union_singleton (b := 0)
  have hfφ : (f : α → E) =ᵐ[μ] φ := hfm.ae_eq_mk
  have hφr : MemLp φ r μ := (Lp.memLp f).ae_eq hfφ
  have hφp : MemLp φ p μ := hf.ae_eq hfφ
  set g : ℕ → SimpleFunc α E := fun n ↦ SimpleFunc.approxOn φ hφ (Set.range φ ∪ {0}) 0
    (by simp) n
  have hgr : ∀ n, MemLp (g n) r μ := SimpleFunc.memLp_approxOn_range hφ hφr
  -- The approximants converge to `f` in `Lʳ`, so their images converge to `T f` in `Lˢ`.
  have hφf : hφr.toLp φ = f := by
    rw [← Lp.toLp_coeFn f (Lp.memLp f), MemLp.toLp_eq_toLp_iff]
    exact hfφ.symm
  have hT : Tendsto (fun n ↦ T ((hgr n).toLp (g n))) atTop (𝓝 (T f)) := by
    have := SimpleFunc.tendsto_approxOn_range_Lp hr hφ hφr
    rw [hφf] at this
    exact (T.continuous.tendsto f).comp this
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hT).exists_seq_tendsto_ae
  -- The approximants also converge to `f` in `Lᵖ`.
  have hgp : Tendsto (fun k ↦ C * (eLpNorm f p μ + eLpNorm (⇑(g (ns k)) - φ) p μ)) atTop
      (𝓝 (C * (eLpNorm f p μ + 0))) :=
    ENNReal.Tendsto.const_mul (tendsto_const_nhds.add
      ((SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm hp hφ hφp.eLpNorm_lt_top).comp
        hns.tendsto_atTop)) (Or.inr hC)
  calc eLpNorm (T f) q ν
      ≤ atTop.liminf fun k ↦ eLpNorm (T ((hgr (ns k)).toLp (g (ns k)))) q ν :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm (fun _ ↦ Lp.aestronglyMeasurable _) _
          (Lp.aestronglyMeasurable _) hae
    _ ≤ atTop.liminf fun k ↦ C * (eLpNorm f p μ + eLpNorm (⇑(g (ns k)) - φ) p μ) := by
        refine liminf_le_liminf (Eventually.of_forall fun k ↦ (h _ _).trans ?_)
        gcongr
        calc eLpNorm (g (ns k)) p μ = eLpNorm (φ + (⇑(g (ns k)) - φ)) p μ := by
              rw [add_sub_cancel]
          _ ≤ eLpNorm φ p μ + eLpNorm (⇑(g (ns k)) - φ) p μ :=
              eLpNorm_add_le hp1
          _ = eLpNorm f p μ + eLpNorm (⇑(g (ns k)) - φ) p μ := by rw [eLpNorm_congr_ae hfφ]
    _ = C * eLpNorm f p μ := by rw [hgp.liminf_eq, add_zero]

end ContinuousLinearMap

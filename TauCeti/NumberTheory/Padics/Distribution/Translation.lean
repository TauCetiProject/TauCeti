/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.LocallyAnalytic
public import TauCeti.Topology.MetricSpace.Ultra.ContinuousMaps
import Mathlib.Algebra.Module.Torsion.Free
import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Matrix.Basic

/-!
# Comultiplication and translation on analytic stages and locally analytic functions

On an analytic stage `LA_h(E) = C₀(ZMod (pʰ) × ℕ, E)`, adding two points `x = a.val + pʰ u` and
`y = b.val + pʰ v` lands in the disc of `a + b` with disc coordinate `q + u + v`, where
`q = ⌊(a.val + b.val) / pʰ⌋` (`PadicInt.discHomeomorph_add_discHomeomorph`). Expanding
`(q + u + v)ᵏ` in powers of `u` and `v` yields a matrix with finitely supported columns and
entries in `ℤ_p`. Combining `Matrix.toZeroAtInftySMulCLM` with currying
`ZeroAtInftyContinuousMap.curryEquiv` defines the linear isometry

`TauCeti.AnalyticStage.comul S : LA_h(E) →ₗᵢ[S] LA_h(LA_h(E))`

satisfying `eval (eval (comul S c) x) y = eval S c (x + y)` (`AnalyticStage.eval_eval_comul`).
It is cocommutative (`AnalyticStage.comul_apply_comm`), coassociative (`AnalyticStage.comul_comul`),
compatible with stage transitions (`AnalyticStage.comul_transition`), and natural under bounded
coefficient maps (`AnalyticStage.comul_compLeft`).

Evaluating the outer stage at a fixed `x : ℤ_p` gives the isometric translation
`TauCeti.AnalyticStage.translate S x : LA_h(E) ≃ₗᵢ[S] LA_h(E)` with
`eval S (translate S x c) y = eval S c (x + y)`. By cocommutativity, evaluating the inner stage at
`x` also recovers `translate S x` (`AnalyticStage.eval_comul_apply`). Translation commutes with
stage transitions (`AnalyticStage.transition_translate`, `AnalyticStage.transitionLE_translate`)
and descends via `Module.DirectLimit.congr` to the linear equivalence
`TauCeti.LocallyAnalytic.translate S x : LA(ℤ_p, E) ≃ₗ[S] LA(ℤ_p, E)`.

Structural identities for `comul` and `translate` are proved first for `E = ℤ_p` using injectivity
of stage evaluation and then transferred to arbitrary complete ultrametric `ℤ_p`-modules `E`
(including torsion and positive-characteristic coefficients) by
`ZeroAtInftyContinuousMap.continuousLinearMap_ext_compLeft_toSpanSingleton`.

## Main definitions

* `TauCeti.AnalyticStage.comul S`: stage comultiplication `LA_h(E) →ₗᵢ[S] LA_h(LA_h(E))`.
* `TauCeti.AnalyticStage.translate S x`: isometric translation `LA_h(E) ≃ₗᵢ[S] LA_h(E)` by `x`.
* `TauCeti.LocallyAnalytic.translate S x`: translation `LA(ℤ_p, E) ≃ₗ[S] LA(ℤ_p, E)` by `x`.

## Main results

* `TauCeti.AnalyticStage.comul_apply_apply`, `TauCeti.AnalyticStage.comul_apply_zero_zero`,
  `TauCeti.AnalyticStage.comul_apply_comm`: coefficient formula, unit slice, and cocommutativity.
* `TauCeti.AnalyticStage.eval_eval_comul`: evaluating `comul S c` at `x` and `y` gives
  `eval S c (x + y)`.
* `TauCeti.AnalyticStage.comul_compLeft`, `TauCeti.AnalyticStage.comul_transition`,
  `TauCeti.AnalyticStage.comul_comul`: naturality, transition compatibility, and coassociativity.
* `TauCeti.AnalyticStage.eval_translate`, `TauCeti.AnalyticStage.eval_comul_apply`,
  `TauCeti.AnalyticStage.translate_zero`, `TauCeti.AnalyticStage.translate_add`,
  `TauCeti.AnalyticStage.translate_symm`, `TauCeti.AnalyticStage.translate_compLeft`,
  `TauCeti.AnalyticStage.transition_translate`, `TauCeti.AnalyticStage.transitionLE_translate`:
  evaluation, group law, naturality, and transition compatibility of stage translation.
* `TauCeti.LocallyAnalytic.translate_ofStage`, `TauCeti.LocallyAnalytic.eval_translate`,
  `TauCeti.LocallyAnalytic.translate_zero`, `TauCeti.LocallyAnalytic.translate_add`,
  `TauCeti.LocallyAnalytic.translate_symm`: corresponding properties on `LA(ℤ_p, E)`.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
* P. Schneider and J. Teitelbaum, *p-adic Fourier theory*, Documenta Math. 6 (2001), 447–481.
-/

public section

open Filter Topology
open scoped ZeroAtInfty

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Comultiplication on analytic stages -/

namespace AnalyticStage

section Comul

variable {h : ℕ} {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]

/-- The scalar `(k choose j) ((k - j) choose m) q^(k - j - m)`, which is the coefficient of
`uᵐ vʲ` in `(q + u + v)ᵏ`. -/
private noncomputable def shiftScalar (q : ℤ_[p]) (m j k : ℕ) : ℤ_[p] :=
  (k.choose j : ℤ_[p]) * ((k - j).choose m : ℤ_[p]) * q ^ (k - j - m)

private theorem shiftScalar_eq_zero_of_lt {q : ℤ_[p]} {m j k : ℕ} (h : k < m + j) :
    shiftScalar q m j k = 0 := by
  by_cases hkj : k < j
  · simp [shiftScalar, Nat.choose_eq_zero_of_lt hkj]
  · have hkm : k - j < m := by omega
    simp [shiftScalar, Nat.choose_eq_zero_of_lt hkm]

private theorem shiftScalar_zero_zero (j k : ℕ) :
    shiftScalar (0 : ℤ_[p]) 0 j k = if k = j then 1 else 0 := by
  by_cases hkj : k = j
  · subst hkj; simp [shiftScalar]
  · simp only [hkj, ↓reduceIte]
    by_cases hlt : k < j
    · simp [shiftScalar, Nat.choose_eq_zero_of_lt hlt]
    · have hsub : k - j ≠ 0 := by omega
      simp [shiftScalar, hsub]

private theorem shiftScalar_comm (q : ℤ_[p]) (m j k : ℕ) :
    shiftScalar q m j k = shiftScalar q j m k := by
  by_cases h : k < m + j
  · rw [shiftScalar_eq_zero_of_lt h, shiftScalar_eq_zero_of_lt (by omega)]
  · have hchoose : k.choose j * (k - j).choose m = k.choose m * (k - m).choose j := by
      rw [← Nat.choose_symm (by omega : j ≤ k),
        Nat.choose_mul (by omega : m ≤ k - j),
        Nat.sub_right_comm k j m, Nat.choose_symm (by omega : j ≤ k - m)]
    simp only [shiftScalar, ← Nat.cast_mul, hchoose, Nat.sub_right_comm k j m]

private theorem add_add_pow_eq_sum_shiftScalar (q u v : ℤ_[p]) (k : ℕ) :
    (q + u + v) ^ k = ∑ m ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      u ^ m * v ^ j * shiftScalar q m j k := by
  rw [add_comm (q + u) v, add_pow, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [add_comm q u, add_pow, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.sum_subset (Finset.range_mono (by omega : k - j + 1 ≤ k + 1))
    fun m _ hm ↦ ?_).trans (Finset.sum_congr rfl fun m _ ↦ ?_)
  · have hlt : k - j < m := by simp only [Finset.mem_range, not_lt] at hm; omega
    simp [Nat.choose_eq_zero_of_lt hlt]
  · rw [shiftScalar]; ring

/-- The comultiplication matrix on `ZMod (p ^ h) × ℕ`: column `(d, k)` records the coefficients of
the expansion of `(q + u + v)ᵏ` across all pairs of discs `(a, b)` summing to `d`. -/
private noncomputable def comulMatrix (h : ℕ) :
    Matrix ((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ)) (ZMod (p ^ h) × ℕ) ℤ_[p] :=
  fun i j ↦
    if i.1.1 + i.2.1 = j.1 then
      shiftScalar (((i.1.1.val + i.2.1.val) / p ^ h : ℕ) : ℤ_[p]) i.1.2 i.2.2 j.2
    else 0

private theorem tendsto_comulMatrix_col (h : ℕ) (j : ZMod (p ^ h) × ℕ) :
    Tendsto (fun i ↦ comulMatrix (p := p) h i j) cofinite (𝓝 0) := by
  have hfin : ((Set.univ ×ˢ Set.Iic j.2) ×ˢ (Set.univ ×ˢ Set.Iic j.2) :
      Set ((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ))).Finite :=
    (Set.finite_univ.prod (Set.finite_Iic j.2)).prod (Set.finite_univ.prod (Set.finite_Iic j.2))
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [hfin.compl_mem_cofinite] with i hi
  simp only [Set.mem_compl_iff, Set.mem_prod, Set.mem_univ, Set.mem_Iic, true_and, not_and_or,
    not_le] at hi
  simp only [comulMatrix]
  split_ifs
  · exact shiftScalar_eq_zero_of_lt (by omega)
  · rfl

private theorem norm_comulMatrix_le_one (h : ℕ)
    (i : (ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ)) (j : ZMod (p ^ h) × ℕ) :
    ‖comulMatrix (p := p) h i j‖ ≤ 1 := by
  simp only [comulMatrix]
  split_ifs
  · exact PadicInt.norm_le_one _
  · simp

variable (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

private noncomputable def comulCLM :
    AnalyticStage p h E →L[S] AnalyticStage p h (AnalyticStage p h E) :=
  (ZeroAtInftyContinuousMap.curryEquiv S E).toLinearIsometry.toContinuousLinearMap.comp
    ((comulMatrix (p := p) h).toZeroAtInftySMulCLM S (tendsto_comulMatrix_col h)
      ⟨1, norm_comulMatrix_le_one h⟩)

private theorem comulCLM_apply_apply (c : AnalyticStage p h E) (i₁ i₂ : ZMod (p ^ h) × ℕ) :
    comulCLM S c i₁ i₂ =
      (comulMatrix (p := p) h).toZeroAtInftySMulCLM S (tendsto_comulMatrix_col h)
        ⟨1, norm_comulMatrix_le_one h⟩ c (i₁, i₂) := by
  simp [comulCLM]

private theorem hasSum_comulCLM_apply_apply (c : AnalyticStage p h E)
    (a b : ZMod (p ^ h)) (m j : ℕ) :
    HasSum (fun k ↦ shiftScalar (((a.val + b.val) / p ^ h : ℕ) : ℤ_[p]) m j k • c (a + b, k))
      (comulCLM S c (a, m) (b, j)) := by
  have hsum : HasSum (fun idx ↦ comulMatrix (p := p) h ((a, m), (b, j)) idx • c idx)
      (comulCLM S c (a, m) (b, j)) := by
    rw [comulCLM_apply_apply]
    exact (comulMatrix (p := p) h).hasSum_toZeroAtInftySMulCLM_apply S
      (tendsto_comulMatrix_col h) ⟨1, norm_comulMatrix_le_one h⟩ c ((a, m), (b, j))
  have hinj : Function.Injective fun k : ℕ ↦ (a + b, k) :=
    fun _ _ hk ↦ (Prod.ext_iff.mp hk).2
  refine ((hinj.hasSum_iff fun idx hidx ↦ ?_).mpr hsum).congr_fun fun k ↦ ?_
  · have hne : a + b ≠ idx.1 := fun he ↦ hidx ⟨idx.2, Prod.ext he rfl⟩
    simp [comulMatrix, hne]
  · simp [comulMatrix]

private theorem comulCLM_zero_zero (c : AnalyticStage p h E) :
    comulCLM S c (0, 0) = c := by
  have : NeZero (p ^ h) := ⟨pow_ne_zero h hp.out.ne_zero⟩
  ext ⟨b, j⟩
  have hsum := hasSum_comulCLM_apply_apply S c 0 b 0 j
  simp only [ZMod.val_zero, zero_add, Nat.div_eq_of_lt (ZMod.val_lt b), Nat.cast_zero,
    shiftScalar_zero_zero] at hsum
  refine hsum.unique ?_
  convert hasSum_single j (f := fun k ↦ (if k = j then (1 : ℤ_[p]) else 0) • c (b, k))
    fun k hk ↦ by simp [hk]
  simp

private theorem norm_comulCLM (c : AnalyticStage p h E) :
    ‖comulCLM S c‖ = ‖c‖ := by
  refine le_antisymm ?_ ?_
  · rw [comulCLM, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.norm_map]
    simpa using (comulMatrix (p := p) h).norm_toZeroAtInftySMulCLM_apply_le S
      (tendsto_comulMatrix_col h) ⟨1, norm_comulMatrix_le_one h⟩ zero_le_one
      (norm_comulMatrix_le_one h) c
  · have h0 := ZeroAtInftyContinuousMap.norm_coe_le_norm (comulCLM S c) (0, 0)
    rwa [comulCLM_zero_zero] at h0

/-- **Comultiplication on an analytic stage.** Expanding `f(x + y)` in the disc coordinates of `x`
and `y` gives a linear isometry `LA_h(E) →ₗᵢ[S] LA_h(LA_h(E))` satisfying
`eval (eval (comul S c) x) y = eval S c (x + y)` (`eval_eval_comul`). -/
noncomputable def comul : AnalyticStage p h E →ₗᵢ[S] AnalyticStage p h (AnalyticStage p h E) where
  toLinearMap := (comulCLM S).toLinearMap
  norm_map' := norm_comulCLM S

private theorem comul_apply_eq_comulCLM (c : AnalyticStage p h E) :
    comul S c = comulCLM S c :=
  (rfl)

/-- The `(0, 0)`-entry of `comul S c` recovers `c`. -/
@[simp]
theorem comul_apply_zero_zero (c : AnalyticStage p h E) :
    comul S c (0, 0) = c :=
  comulCLM_zero_zero S c

/-- The explicit coefficient formula for `comul S c`. -/
theorem comul_apply_apply (c : AnalyticStage p h E) (a b : ZMod (p ^ h)) (m j : ℕ) :
    comul S c (a, m) (b, j) =
      ∑' k, ((k.choose j : ℤ_[p]) * ((k - j).choose m : ℤ_[p]) *
        (((a.val + b.val) / p ^ h : ℕ) : ℤ_[p]) ^ (k - j - m)) • c (a + b, k) := by
  rw [comul_apply_eq_comulCLM, ← (hasSum_comulCLM_apply_apply S c a b m j).tsum_eq]
  rfl

/-- Comultiplication does not depend on the choice of scalar ring. -/
theorem comul_eq_comul {S₁ S₂ : Type*} [Semiring S₁] [Module S₁ E]
    [ContinuousConstSMul S₁ E] [SMulCommClass ℤ_[p] S₁ E] [Semiring S₂] [Module S₂ E]
    [ContinuousConstSMul S₂ E] [SMulCommClass ℤ_[p] S₂ E] (c : AnalyticStage p h E) :
    comul S₁ c = comul S₂ c := by
  ext ⟨a, m⟩ ⟨b, j⟩
  rw [comul_apply_apply, comul_apply_apply]

/-- Comultiplication on an analytic stage is cocommutative: swapping the outer and inner
coordinates leaves `comul S c` unchanged. -/
theorem comul_apply_comm (c : AnalyticStage p h E) (i₁ i₂ : ZMod (p ^ h) × ℕ) :
    comul S c i₁ i₂ = comul S c i₂ i₁ := by
  rcases i₁ with ⟨a, m⟩
  rcases i₂ with ⟨b, j⟩
  rw [comul_apply_eq_comulCLM,
    ← (hasSum_comulCLM_apply_apply S c a b m j).tsum_eq,
    ← (hasSum_comulCLM_apply_apply S c b a j m).tsum_eq]
  refine tsum_congr fun k ↦ ?_
  rw [add_comm a b, Nat.add_comm a.val b.val, shiftScalar_comm]

private theorem comul_single_apply_apply (d : ZMod (p ^ h)) (N : ℕ) (e : E)
    (a b : ZMod (p ^ h)) (m j : ℕ) :
    comul S (ZeroAtInftyContinuousMap.single (d, N) e) (a, m) (b, j) =
      if a + b = d then
        shiftScalar (((a.val + b.val) / p ^ h : ℕ) : ℤ_[p]) m j N • e
      else 0 := by
  rw [comul_apply_eq_comulCLM, comulCLM_apply_apply, Matrix.toZeroAtInftySMulCLM_single_apply,
    comulMatrix]
  split_ifs <;> simp

private theorem comul_single_eq_zero_of_lt (d : ZMod (p ^ h)) {N m : ℕ} (hNm : N < m) (e : E)
    (a : ZMod (p ^ h)) :
    comul S (ZeroAtInftyContinuousMap.single (d, N) e) (a, m) = 0 := by
  ext ⟨b', j⟩
  rw [comul_single_apply_apply]
  split_ifs
  · simp [shiftScalar_eq_zero_of_lt (by omega : N < m + j)]
  · simp

private theorem eval_comul_single_apply (d : ZMod (p ^ h)) (N m : ℕ) (e : E)
    (a b : ZMod (p ^ h)) (u v : ℤ_[p]) :
    u ^ m • eval S (comul S (ZeroAtInftyContinuousMap.single (d, N) e) (a, m))
      ((b.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * v) =
    if a + b = d then
      ∑ j ∈ Finset.range (N + 1),
        (u ^ m * v ^ j * shiftScalar (((a.val + b.val) / p ^ h : ℕ) : ℤ_[p]) m j N) • e
    else 0 := by
  rw [eval_natCast_val_add_mul]
  rw [tsum_eq_sum (s := Finset.range (N + 1)) fun j hj ↦ by
    have hNj : N < j := by simp only [Finset.mem_range, not_lt] at hj; omega
    rw [comul_single_apply_apply]
    split_ifs
    · simp [shiftScalar_eq_zero_of_lt (by omega : N < m + j)]
    · simp]
  by_cases hab : a + b = d
  · simp only [hab, ↓reduceIte, comul_single_apply_apply, Finset.smul_sum, smul_smul, mul_assoc]
  · simp [hab, comul_single_apply_apply]

private theorem eval_eval_comul_single (d : ZMod (p ^ h)) (N : ℕ) (e : E) (x y : ℤ_[p]) :
    eval S (eval S (comul S (ZeroAtInftyContinuousMap.single (d, N) e)) x) y =
      eval S (ZeroAtInftyContinuousMap.single (d, N) e) (x + y) := by
  obtain ⟨⟨a, u⟩, rfl⟩ := (PadicInt.discHomeomorph p h).surjective x
  obtain ⟨⟨b, v⟩, rfl⟩ := (PadicInt.discHomeomorph p h).surjective y
  set q : ℤ_[p] := (((a.val + b.val) / p ^ h : ℕ) : ℤ_[p])
  rw [PadicInt.discHomeomorph_add_discHomeomorph]
  simp only [PadicInt.discHomeomorph_apply]
  rw [eval_natCast_val_add_mul S (comul S (ZeroAtInftyContinuousMap.single (d, N) e)) a u,
    eval_natCast_val_add_mul S (ZeroAtInftyContinuousMap.single (d, N) e) (a + b) (q + u + v)]
  let evY : AnalyticStage p h E →L[ℤ_[p]] E :=
    (ContinuousMap.evalCLM ℤ_[p] ((b.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * v)).comp (eval ℤ_[p])
  have houter : eval S (∑' m, u ^ m • comul S (ZeroAtInftyContinuousMap.single (d, N) e) (a, m))
      ((b.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * v) =
      ∑' m, u ^ m • eval S (comul S (ZeroAtInftyContinuousMap.single (d, N) e) (a, m))
        ((b.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * v) := by
    have hsum := (hasSum_eval_natCast_val_add_mul S
      (comul S (ZeroAtInftyContinuousMap.single (d, N) e)) a u).summable
    simpa only [evY, ContinuousLinearMap.comp_apply, ContinuousMap.evalCLM_apply,
      map_smul, eval_eq_eval (S₁ := ℤ_[p]) (S₂ := S)] using ((hsum.hasSum.mapL evY).tsum_eq).symm
  rw [houter, tsum_eq_sum (s := Finset.range (N + 1)) fun m hm ↦ by
    have hNm : N < m := by simp only [Finset.mem_range, not_lt] at hm; omega
    simp [comul_single_eq_zero_of_lt S d hNm]]
  have hrhs : ∑' k, (q + u + v) ^ k • ZeroAtInftyContinuousMap.single (d, N) e (a + b, k) =
      if a + b = d then (q + u + v) ^ N • e else 0 := by
    rw [tsum_eq_single N]
    · by_cases hab : a + b = d <;> simp [hab]
    · intro k hk
      have hne : (a + b, k) ≠ (d, N) := fun h ↦ hk (Prod.ext_iff.mp h).2
      simp [ZeroAtInftyContinuousMap.single_eq_of_ne hne]
  rw [hrhs]
  simp_rw [eval_comul_single_apply S d N _ e a b u v]
  split_ifs with hab
  · simp_rw [← Finset.sum_smul, ← add_add_pow_eq_sum_shiftScalar, q]
  · simp

/-- Evaluating `comul S c` at `x` and then at `y` equals evaluating `c` at `x + y`. -/
@[simp]
theorem eval_eval_comul (c : AnalyticStage p h E) (x y : ℤ_[p]) :
    eval S (eval S (comul S c) x) y = eval S c (x + y) := by
  let L₁ : AnalyticStage p h E →L[ℤ_[p]] E :=
    ((ContinuousMap.evalCLM ℤ_[p] y).comp (eval ℤ_[p])).comp
      (((ContinuousMap.evalCLM ℤ_[p] x).comp (eval ℤ_[p])).comp
        (comul (p := p) (h := h) (E := E) ℤ_[p]).toContinuousLinearMap)
  let L₂ : AnalyticStage p h E →L[ℤ_[p]] E :=
    (ContinuousMap.evalCLM ℤ_[p] (x + y)).comp (eval ℤ_[p])
  have hEq : L₁ = L₂ := ZeroAtInftyContinuousMap.continuousLinearMap_ext fun ⟨d, N⟩ e ↦ by
    simp only [L₁, L₂, ContinuousLinearMap.comp_apply, ContinuousMap.evalCLM_apply,
      LinearIsometry.coe_toContinuousLinearMap]
    exact eval_eval_comul_single ℤ_[p] d N e x y
  simpa only [L₁, L₂, ContinuousLinearMap.comp_apply, ContinuousMap.evalCLM_apply,
    LinearIsometry.coe_toContinuousLinearMap, comul_eq_comul (S₁ := ℤ_[p]) (S₂ := S),
    eval_eq_eval (S₁ := ℤ_[p]) (S₂ := S)] using DFunLike.congr_fun hEq c

/-- Comultiplication commutes with the coordinatewise action of a bounded continuous linear map
compatible with the `ℤ_p`-action. -/
theorem comul_compLeft {F R : Type*} [NormedAddCommGroup F] [Module ℤ_[p] F] [IsBoundedSMul ℤ_[p] F]
    [IsUltrametricDist F] [CompleteSpace F]
    (S' : Type*) [Semiring S'] [Module S' F] [ContinuousConstSMul S' F] [SMulCommClass ℤ_[p] S' F]
    [Semiring R] [Module R E] [ContinuousConstSMul R E] [Module R F] [ContinuousConstSMul R F]
    [LinearMap.CompatibleSMul E F ℤ_[p] R]
    (u : E →L[R] F) (hu : ∃ C, ∀ e, ‖u e‖ ≤ C * ‖e‖) (c : AnalyticStage p h E) :
    comul S' (ZeroAtInftyContinuousMap.compLeft u hu c) =
      ZeroAtInftyContinuousMap.compLeft
        (ZeroAtInftyContinuousMap.compLeft u hu)
        (ZeroAtInftyContinuousMap.exists_norm_compLeft_apply_le u hu)
        (comul S c) := by
  ext ⟨a, m⟩ ⟨b, j⟩
  rw [ZeroAtInftyContinuousMap.compLeft_apply, ZeroAtInftyContinuousMap.compLeft_apply,
    comul_apply_eq_comulCLM, comul_apply_eq_comulCLM]
  have h1 := hasSum_comulCLM_apply_apply S' (ZeroAtInftyContinuousMap.compLeft u hu c) a b m j
  have h2 := (hasSum_comulCLM_apply_apply S c a b m j).mapL u
  exact h1.unique (h2.congr_fun fun k ↦ by simp [ContinuousLinearMap.map_smul_of_tower])

private theorem comul_transition_padicInt (c : AnalyticStage p h ℤ_[p]) :
    comul ℤ_[p] (transition ℤ_[p] c) =
      ZeroAtInftyContinuousMap.compLeft (transition ℤ_[p]) ⟨1, fun d ↦ by
        simpa using norm_transition_le ℤ_[p] d⟩ (transition ℤ_[p] (comul ℤ_[p] c)) := by
  have hpReg : IsSMulRegular ℤ_[p] (p : ℤ_[p]) :=
    smul_right_injective ℤ_[p] (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  apply eval_injective ℤ_[p] (ZeroAtInftyContinuousMap.isSMulRegular hpReg)
  ext x : 1
  apply eval_injective ℤ_[p] hpReg
  ext y
  rw [eval_eval_comul, eval_transition, eval_compLeft ℤ_[p] ℤ_[p], eval_transition,
    eval_transition, eval_eval_comul]

/-- Comultiplication commutes with stage transitions: refining before comultiplying equals
refining both the outer and inner analytic stages after comultiplying. -/
theorem comul_transition (c : AnalyticStage p h E) :
    comul S (transition S c) =
      ZeroAtInftyContinuousMap.compLeft (transition S) ⟨1, fun d ↦ by
        simpa using norm_transition_le S d⟩ (transition S (comul S c)) := by
  let L₁ : AnalyticStage p h E →L[ℤ_[p]] AnalyticStage p (h + 1) (AnalyticStage p (h + 1) E) :=
    (comul (p := p) (h := h + 1) (E := E) ℤ_[p]).toContinuousLinearMap.comp (transition ℤ_[p])
  let L₂ : AnalyticStage p h E →L[ℤ_[p]] AnalyticStage p (h + 1) (AnalyticStage p (h + 1) E) :=
    (ZeroAtInftyContinuousMap.compLeft (transition ℤ_[p]) ⟨1, fun d ↦ by
      simpa using norm_transition_le ℤ_[p] d⟩).comp
      ((transition ℤ_[p]).comp (comul (p := p) (h := h) (E := E) ℤ_[p]).toContinuousLinearMap)
  have hEq : L₁ = L₂ := ZeroAtInftyContinuousMap.continuousLinearMap_ext_compLeft_toSpanSingleton
    fun e hu i ↦ by
      simp only [L₁, L₂, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
      rw [transition_compLeft ℤ_[p] ℤ_[p], comul_compLeft ℤ_[p] ℤ_[p], comul_transition_padicInt,
        comul_compLeft ℤ_[p] ℤ_[p], transition_compLeft ℤ_[p] ℤ_[p]]
      ext i₁ i₂
      simp only [ZeroAtInftyContinuousMap.compLeft_apply]
      simpa only [ZeroAtInftyContinuousMap.compLeft_apply] using
        DFunLike.congr_fun (transition_compLeft ℤ_[p] ℤ_[p]
          (ContinuousLinearMap.toSpanSingleton ℤ_[p] e) hu _).symm i₂
  have hc := DFunLike.congr_fun hEq c
  simp only [L₁, L₂, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    comul_eq_comul (S₁ := ℤ_[p]) (S₂ := S),
    transition_eq_transition (S₁ := ℤ_[p]) (S₂ := S)] at hc
  rw [hc]
  ext i₁ i₂
  simp only [ZeroAtInftyContinuousMap.compLeft_apply]
  exact DFunLike.congr_fun (transition_eq_transition (S₁ := ℤ_[p]) (S₂ := S) _) i₂

private theorem comul_comul_padicInt (c : AnalyticStage p h ℤ_[p]) :
    comul ℤ_[p] (comul ℤ_[p] c) =
      ZeroAtInftyContinuousMap.compLeft
        (comul (p := p) (h := h) (E := ℤ_[p]) ℤ_[p]).toContinuousLinearMap
        ⟨1, fun d ↦ by simp⟩ (comul ℤ_[p] c) := by
  have hpReg : IsSMulRegular ℤ_[p] (p : ℤ_[p]) :=
    smul_right_injective ℤ_[p] (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hreg1 := ZeroAtInftyContinuousMap.isSMulRegular (α := ZMod (p ^ h) × ℕ) hpReg
  apply eval_injective ℤ_[p] (ZeroAtInftyContinuousMap.isSMulRegular hreg1)
  ext x : 1
  apply eval_injective ℤ_[p] hreg1
  ext y : 1
  apply eval_injective ℤ_[p] hpReg
  ext z
  rw [eval_eval_comul, eval_eval_comul, eval_compLeft ℤ_[p] ℤ_[p],
    LinearIsometry.coe_toContinuousLinearMap, eval_eval_comul, eval_eval_comul, add_assoc]

/-- Comultiplication on an analytic stage is coassociative. -/
theorem comul_comul (c : AnalyticStage p h E) :
    comul S (comul S c) =
      ZeroAtInftyContinuousMap.compLeft
        (comul (p := p) (h := h) (E := E) S).toContinuousLinearMap
        ⟨1, fun d ↦ by simp⟩ (comul S c) := by
  let L₁ : AnalyticStage p h E →L[ℤ_[p]]
      AnalyticStage p h (AnalyticStage p h (AnalyticStage p h E)) :=
    (comul (p := p) (h := h) (E := AnalyticStage p h E) ℤ_[p]).toContinuousLinearMap.comp
      (comul (p := p) (h := h) (E := E) ℤ_[p]).toContinuousLinearMap
  let L₂ : AnalyticStage p h E →L[ℤ_[p]]
      AnalyticStage p h (AnalyticStage p h (AnalyticStage p h E)) :=
    (ZeroAtInftyContinuousMap.compLeft
      (comul (p := p) (h := h) (E := E) ℤ_[p]).toContinuousLinearMap
      ⟨1, fun d ↦ by simp⟩).comp
      (comul (p := p) (h := h) (E := E) ℤ_[p]).toContinuousLinearMap
  have hEq : L₁ = L₂ := ZeroAtInftyContinuousMap.continuousLinearMap_ext_compLeft_toSpanSingleton
    fun e hu i ↦ by
      simp only [L₁, L₂, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
      rw [comul_compLeft ℤ_[p] ℤ_[p], comul_compLeft ℤ_[p] ℤ_[p], comul_comul_padicInt]
      ext i₁ i₂ i₃
      simp only [ZeroAtInftyContinuousMap.compLeft_apply, LinearIsometry.coe_toContinuousLinearMap]
      simpa only [ZeroAtInftyContinuousMap.compLeft_apply] using DFunLike.congr_fun
        (DFunLike.congr_fun (comul_compLeft ℤ_[p] ℤ_[p]
          (ContinuousLinearMap.toSpanSingleton ℤ_[p] e) hu _).symm i₂) i₃
  have hc := DFunLike.congr_fun hEq c
  simp only [L₁, L₂, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    comul_eq_comul (S₁ := ℤ_[p]) (S₂ := S)] at hc
  rw [hc]
  ext i₁ i₂ i₃
  simp only [ZeroAtInftyContinuousMap.compLeft_apply, LinearIsometry.coe_toContinuousLinearMap]
  exact DFunLike.congr_fun
    (DFunLike.congr_fun (comul_eq_comul (S₁ := ℤ_[p]) (S₂ := S) _) i₂) i₃

/-! ### Translation on analytic stages -/

private noncomputable def translateCLM (x : ℤ_[p]) :
    AnalyticStage p h E →L[S] AnalyticStage p h E :=
  (ContinuousMap.evalCLM S x).comp
    ((eval S).comp (comul (p := p) (h := h) (E := E) S).toContinuousLinearMap)

private theorem translateCLM_apply (x : ℤ_[p]) (c : AnalyticStage p h E) :
    translateCLM S x c = eval S (comul S c) x := by
  simp only [translateCLM, ContinuousLinearMap.comp_apply, ContinuousMap.evalCLM_apply,
    LinearIsometry.coe_toContinuousLinearMap]

private theorem translateCLM_eq {S₁ S₂ : Type*} [Semiring S₁] [Module S₁ E]
    [ContinuousConstSMul S₁ E] [SMulCommClass ℤ_[p] S₁ E] [Semiring S₂] [Module S₂ E]
    [ContinuousConstSMul S₂ E] [SMulCommClass ℤ_[p] S₂ E] (x : ℤ_[p]) (c : AnalyticStage p h E) :
    translateCLM S₁ x c = translateCLM S₂ x c := by
  simp only [translateCLM_apply, comul_eq_comul (S₁ := S₁) (S₂ := S₂),
    eval_eq_eval (S₁ := S₁) (S₂ := S₂)]

private theorem eval_translateCLM (x : ℤ_[p]) (c : AnalyticStage p h E) (y : ℤ_[p]) :
    eval S (translateCLM S x c) y = eval S c (x + y) := by
  rw [translateCLM_apply, eval_eval_comul]

private theorem norm_translateCLM_le (x : ℤ_[p]) (c : AnalyticStage p h E) :
    ‖translateCLM S x c‖ ≤ ‖c‖ := by
  rw [translateCLM_apply]
  calc
    ‖eval S (comul S c) x‖ ≤ ‖eval S (comul S c)‖ := ContinuousMap.norm_coe_le_norm _ x
    _ ≤ ‖comul S c‖ := norm_eval_le S (comul S c)
    _ = ‖c‖ := (comul (p := p) (h := h) (E := E) S).norm_map c

private theorem translateCLM_compLeft {F R : Type*} [NormedAddCommGroup F] [Module ℤ_[p] F]
    [IsBoundedSMul ℤ_[p] F] [IsUltrametricDist F] [CompleteSpace F]
    (S' : Type*) [Semiring S'] [Module S' F] [ContinuousConstSMul S' F] [SMulCommClass ℤ_[p] S' F]
    [Semiring R] [Module R E] [ContinuousConstSMul R E] [Module R F] [ContinuousConstSMul R F]
    [LinearMap.CompatibleSMul E F ℤ_[p] R]
    (u : E →L[R] F) (hu : ∃ C, ∀ e, ‖u e‖ ≤ C * ‖e‖) (x : ℤ_[p]) (c : AnalyticStage p h E) :
    translateCLM S' x (ZeroAtInftyContinuousMap.compLeft u hu c) =
      ZeroAtInftyContinuousMap.compLeft u hu (translateCLM S x c) := by
  let u' : E →L[ℤ_[p]] F := u.restrictScalars ℤ_[p]
  have hu' : ∃ C, ∀ e, ‖u' e‖ ≤ C * ‖e‖ := hu
  have hcomp : ∀ d : AnalyticStage p h E,
      ZeroAtInftyContinuousMap.compLeft u hu d = ZeroAtInftyContinuousMap.compLeft u' hu' d :=
    fun d ↦ by
      ext i
      rw [ZeroAtInftyContinuousMap.compLeft_apply, ZeroAtInftyContinuousMap.compLeft_apply]
      rfl
  rw [hcomp, hcomp, translateCLM_apply, translateCLM_apply, comul_compLeft S S' u' hu',
    eval_compLeft S S']

private theorem translateCLM_zero (c : AnalyticStage p h E) : translateCLM S 0 c = c := by
  have hpReg : IsSMulRegular ℤ_[p] (p : ℤ_[p]) :=
    smul_right_injective ℤ_[p] (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hpadic : ∀ d : AnalyticStage p h ℤ_[p], translateCLM ℤ_[p] 0 d = d := fun d ↦ by
    apply eval_injective ℤ_[p] hpReg
    ext y
    rw [eval_translateCLM, zero_add]
  have hEq : translateCLM (p := p) (h := h) (E := E) ℤ_[p] 0 = ContinuousLinearMap.id ℤ_[p] _ :=
    ZeroAtInftyContinuousMap.continuousLinearMap_ext_compLeft_toSpanSingleton fun e hu i ↦ by
      rw [ContinuousLinearMap.id_apply, translateCLM_compLeft ℤ_[p] ℤ_[p], hpadic]
  rw [← translateCLM_eq (S₁ := ℤ_[p]) (S₂ := S)]
  exact DFunLike.congr_fun hEq c

private theorem translateCLM_add (x y : ℤ_[p]) (c : AnalyticStage p h E) :
    translateCLM S (x + y) c = translateCLM S x (translateCLM S y c) := by
  have hpReg : IsSMulRegular ℤ_[p] (p : ℤ_[p]) :=
    smul_right_injective ℤ_[p] (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hpadic : ∀ d : AnalyticStage p h ℤ_[p],
      translateCLM ℤ_[p] (x + y) d = translateCLM ℤ_[p] x (translateCLM ℤ_[p] y d) := fun d ↦ by
    apply eval_injective ℤ_[p] hpReg
    ext z
    rw [eval_translateCLM, eval_translateCLM, eval_translateCLM, add_left_comm, add_assoc]
  have hEq : translateCLM (p := p) (h := h) (E := E) ℤ_[p] (x + y) =
      (translateCLM ℤ_[p] x).comp (translateCLM ℤ_[p] y) :=
    ZeroAtInftyContinuousMap.continuousLinearMap_ext_compLeft_toSpanSingleton fun e hu i ↦ by
      rw [ContinuousLinearMap.comp_apply, translateCLM_compLeft ℤ_[p] ℤ_[p],
        translateCLM_compLeft ℤ_[p] ℤ_[p], translateCLM_compLeft ℤ_[p] ℤ_[p], hpadic]
  rw [← translateCLM_eq (S₁ := ℤ_[p]) (S₂ := S), ← translateCLM_eq (S₁ := ℤ_[p]) (S₂ := S),
    ← translateCLM_eq (S₁ := ℤ_[p]) (S₂ := S)]
  exact DFunLike.congr_fun hEq c

/-- **Translation on an analytic stage.** Translating the argument by `x : ℤ_p` defines a linear
isometry equivalence `LA_h(E) ≃ₗᵢ[S] LA_h(E)` with `eval (translate S x c) y = eval c (x + y)`. -/
noncomputable def translate (x : ℤ_[p]) : AnalyticStage p h E ≃ₗᵢ[S] AnalyticStage p h E where
  toFun := translateCLM S x
  map_add' := map_add (translateCLM S x)
  map_smul' := map_smul (translateCLM S x)
  invFun := translateCLM S (-x)
  left_inv c := by rw [← translateCLM_add, neg_add_cancel, translateCLM_zero]
  right_inv c := by rw [← translateCLM_add, add_neg_cancel, translateCLM_zero]
  norm_map' c := le_antisymm (norm_translateCLM_le S x c) <| by
    have h := norm_translateCLM_le S (-x) (translateCLM S x c)
    rwa [← translateCLM_add, neg_add_cancel, translateCLM_zero] at h

private theorem translate_apply_eq_translateCLM (x : ℤ_[p]) (c : AnalyticStage p h E) :
    translate S x c = translateCLM S x c :=
  (rfl)

/-- Translation of `c` by `x` is the evaluation of `comul S c` at `x`. -/
theorem translate_eq_eval_comul (x : ℤ_[p]) (c : AnalyticStage p h E) :
    translate S x c = eval S (comul S c) x := by
  rw [translate_apply_eq_translateCLM, translateCLM_apply]

/-- Evaluating the `i`-th inner slice `comul S c i` at `x` gives the `i`-th coordinate of
`translate S x c`. -/
theorem eval_comul_apply (c : AnalyticStage p h E) (i : ZMod (p ^ h) × ℕ) (x : ℤ_[p]) :
    eval S (comul S c i) x = translate S x c i := by
  rw [translate_eq_eval_comul]
  have h1 := hasSum_eval_apply S (comul S c i) x
  have h2 := (hasSum_eval_apply S (comul S c) x).mapL (ZeroAtInftyContinuousMap.evalCLM ℤ_[p] i)
  rw [ZeroAtInftyContinuousMap.evalCLM_apply] at h2
  exact h1.unique (h2.congr_fun fun n ↦ by
    simp [ZeroAtInftyContinuousMap.evalCLM_apply, comul_apply_comm])

/-- Evaluating the translate of `c` by `x` at `y` gives `eval S c (x + y)`. -/
@[simp]
theorem eval_translate (x : ℤ_[p]) (c : AnalyticStage p h E) (y : ℤ_[p]) :
    eval S (translate S x c) y = eval S c (x + y) := by
  rw [translate_apply_eq_translateCLM, eval_translateCLM]

/-- Translating by `0` is the identity. -/
@[simp]
theorem translate_zero (c : AnalyticStage p h E) : translate S 0 c = c :=
  translateCLM_zero S c

/-- Translations compose by addition. -/
theorem translate_add (x y : ℤ_[p]) (c : AnalyticStage p h E) :
    translate S (x + y) c = translate S x (translate S y c) :=
  translateCLM_add S x y c

/-- The inverse of translation by `x` is translation by `-x`. -/
@[simp]
theorem translate_symm (x : ℤ_[p]) :
    (translate (p := p) (h := h) (E := E) S x).symm = translate S (-x) := by
  ext c
  rfl

/-- Stage translation does not depend on the choice of scalar ring. -/
theorem translate_eq_translate {S₁ S₂ : Type*} [Semiring S₁] [Module S₁ E]
    [ContinuousConstSMul S₁ E] [SMulCommClass ℤ_[p] S₁ E] [Semiring S₂] [Module S₂ E]
    [ContinuousConstSMul S₂ E] [SMulCommClass ℤ_[p] S₂ E] (x : ℤ_[p]) (c : AnalyticStage p h E) :
    translate S₁ x c = translate S₂ x c :=
  translateCLM_eq x c

/-- Translation commutes with the coordinatewise action of a bounded continuous linear map
compatible with the `ℤ_p`-action. -/
theorem translate_compLeft {F R : Type*} [NormedAddCommGroup F] [Module ℤ_[p] F]
    [IsBoundedSMul ℤ_[p] F] [IsUltrametricDist F] [CompleteSpace F]
    (S' : Type*) [Semiring S'] [Module S' F] [ContinuousConstSMul S' F] [SMulCommClass ℤ_[p] S' F]
    [Semiring R] [Module R E] [ContinuousConstSMul R E] [Module R F] [ContinuousConstSMul R F]
    [LinearMap.CompatibleSMul E F ℤ_[p] R]
    (u : E →L[R] F) (hu : ∃ C, ∀ e, ‖u e‖ ≤ C * ‖e‖) (x : ℤ_[p]) (c : AnalyticStage p h E) :
    translate S' x (ZeroAtInftyContinuousMap.compLeft u hu c) =
      ZeroAtInftyContinuousMap.compLeft u hu (translate S x c) :=
  translateCLM_compLeft S S' u hu x c

/-- Translation commutes with adjacent stage transitions. -/
theorem transition_translate (x : ℤ_[p]) (c : AnalyticStage p h E) :
    transition S (translate S x c) = translate S x (transition S c) := by
  rw [translate_eq_eval_comul, translate_eq_eval_comul, comul_transition]
  have htrans : ∃ C, ∀ d : AnalyticStage p h E, ‖transition ℤ_[p] d‖ ≤ C * ‖d‖ :=
    ⟨1, fun d ↦ by simpa using norm_transition_le ℤ_[p] d⟩
  have hcomp : ZeroAtInftyContinuousMap.compLeft (transition S)
      ⟨1, fun d ↦ by simpa using norm_transition_le S d⟩ (transition S (comul S c)) =
      ZeroAtInftyContinuousMap.compLeft (transition ℤ_[p]) htrans (transition S (comul S c)) := by
    ext i₁ i₂
    simp only [ZeroAtInftyContinuousMap.compLeft_apply]
    exact DFunLike.congr_fun (transition_eq_transition (S₁ := S) (S₂ := ℤ_[p]) _) i₂
  rw [hcomp, eval_compLeft S S, eval_transition, transition_eq_transition (S₁ := ℤ_[p]) (S₂ := S)]

/-- Translation commutes with multi-level stage transitions. -/
theorem transitionLE_translate {k : ℕ} (hhk : h ≤ k) (x : ℤ_[p]) (c : AnalyticStage p h E) :
    transitionLE S hhk (translate S x c) = translate S x (transitionLE S hhk c) := by
  induction k, hhk using Nat.le_induction with
  | base => simp
  | succ k hhk ih =>
    rw [transitionLE_succ S hhk, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ih, transition_translate]

end Comul

end AnalyticStage

/-! ### Translation on locally analytic functions -/

namespace LocallyAnalytic

open AnalyticStage

variable {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-- **Translation on locally analytic functions.** Translating the argument by `x : ℤ_p` defines a
linear equivalence `LA(ℤ_p, E) ≃ₗ[S] LA(ℤ_p, E)` agreeing with `AnalyticStage.translate S x` on
every stage. -/
noncomputable def translate (x : ℤ_[p]) : LocallyAnalytic p S E ≃ₗ[S] LocallyAnalytic p S E :=
  Module.DirectLimit.congr (fun _ ↦ (AnalyticStage.translate S x).toLinearEquiv)
    (fun _ _ hhk ↦ LinearMap.ext fun c ↦ (transitionLE_translate S hhk x c).symm)

/-- Translation restricts to `AnalyticStage.translate` on every analytic stage. -/
@[simp]
theorem translate_ofStage (x : ℤ_[p]) (h : ℕ) (c : AnalyticStage p h E) :
    translate S x (ofStage S h c) = ofStage S h (AnalyticStage.translate S x c) := by
  rw [translate, ofStage_def, Module.DirectLimit.congr_apply_of,
    LinearIsometryEquiv.coe_toLinearEquiv]

/-- Evaluating the translate of `f` by `x` at `y` gives `eval S f (x + y)`. -/
@[simp]
theorem eval_translate (x : ℤ_[p]) (f : LocallyAnalytic p S E) (y : ℤ_[p]) :
    eval S (translate S x f) y = eval S f (x + y) := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, translate_ofStage, eval_ofStage, eval_ofStage, AnalyticStage.eval_translate]

/-- Translating by `0` is the identity. -/
@[simp]
theorem translate_zero (f : LocallyAnalytic p S E) : translate S 0 f = f := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, translate_ofStage, AnalyticStage.translate_zero]

/-- Translations compose by addition. -/
theorem translate_add (x y : ℤ_[p]) (f : LocallyAnalytic p S E) :
    translate S (x + y) f = translate S x (translate S y f) := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, translate_ofStage, translate_ofStage, translate_ofStage,
    AnalyticStage.translate_add]

/-- The inverse of translation by `x` is translation by `-x`. -/
@[simp]
theorem translate_symm (x : ℤ_[p]) :
    (translate (p := p) (E := E) S x).symm = translate S (-x) := by
  ext f
  apply (translate S x).injective
  rw [LinearEquiv.apply_symm_apply, ← translate_add, add_neg_cancel, translate_zero]

end LocallyAnalytic

end TauCeti

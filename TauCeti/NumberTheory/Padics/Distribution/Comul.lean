/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.AnalyticStage
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Bilinear
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Matrix.Basic

/-!
# Two-variable addition re-expansion on analytic stages

Additive convolution of locally analytic distributions on `ℤ_p` dualises addition
`+ : ℤ_p × ℤ_p → ℤ_p` on locally analytic test functions. On a product of level-`h` discs
`(a + pʰℤ_p) × (b + pʰℤ_p)` with local coordinates `(u, v) ∈ ℤ_p × ℤ_p`, addition lands in the
disc `(a + b) + pʰℤ_p` with local coordinate `q + u + v`, where
`q = ⌊(a.val + b.val) / pʰ⌋ ∈ {0, 1}` is the carry from adding the natural representatives of
`a` and `b`. Expanding `(q + u + v)ᵏ` in powers of `u` and `v` turns a single-variable coefficient
vector `c ∈ LA_h(E)` into a null two-variable coefficient family on
`(ZMod (pʰ) × ℕ) × (ZMod (pʰ) × ℕ)`:

`(comul S c)((a, i), (b, j)) =`
`  ∑_{k ≥ i + j} ((i + j) choose i) (k choose (i + j)) q^(k - i - j) • c(a + b, k)`.

Because `ZMod (pʰ)` is finite and `k choose (i + j) = 0` for `i + j > k`, each column of the
defining `ℤ_p`-matrix has finite support and entries of norm at most `1`, so
`Matrix.toZeroAtInftySMulCLM` produces `TauCeti.AnalyticStage.comul` for every complete ultrametric
`ℤ_p`-module `E` with contractive action. Evaluating at `(b, j) = (0, 0)` recovers `c(a, i)`, making
`comul` an exact linear isometry (`norm_comul`).

Currying identifies the codomain with the iterated analytic stage `LA_h(LA_h(E))`
(`TauCeti.AnalyticStage.comulCurried`), on which iterated stage evaluation satisfies
`eval (eval (comulCurried c) x) y = eval c (x + y)` (`eval_eval_comulCurried`). Over `ℤ_p`,
multiplication by `p` is injective, so iterated `eval_injective` transfers compatibility with level
transitions (`transition_compLeft_transition_comulCurried`) and coassociativity
(`comulCurried_comulCurried`) directly from `eval_transition` and `add_assoc`; coefficient
functoriality along `r ↦ r • e` then extends both identities to arbitrary coefficient modules,
including torsion modules.

## Main definitions

* `TauCeti.AnalyticStage.comul`: two-variable addition re-expansion
  `LA_h(E) →L[S] C₀((ZMod (pʰ) × ℕ) × (ZMod (pʰ) × ℕ), E)`.
* `TauCeti.AnalyticStage.comulCurried`: the curried form `LA_h(E) →L[S] LA_h(LA_h(E))`.

## Main results

* `TauCeti.AnalyticStage.comul_apply`: the explicit carry-binomial series for `comul`.
* `TauCeti.AnalyticStage.comul_apply_zero_right`, `TauCeti.AnalyticStage.comul_apply_zero_left`:
  counit identities at `(0, 0)`.
* `TauCeti.AnalyticStage.norm_comul`: `‖comul S c‖ = ‖c‖`.
* `TauCeti.AnalyticStage.congrLeft_prodComm_comul`: cocommutativity under `Homeomorph.prodComm`.
* `TauCeti.AnalyticStage.eval_eval_comulCurried`: compatibility with addition `(x, y) ↦ x + y`.
* `TauCeti.AnalyticStage.eval_curryEquiv_prodMul`: stage evaluation of a curried outer product.
* `TauCeti.AnalyticStage.transition_compLeft_transition_comulCurried`: compatibility with
  `transition`.
* `TauCeti.AnalyticStage.comulCurried_comulCurried`: coassociativity of `comulCurried`.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4 and §II.2.
* P. Schneider and J. Teitelbaum, *p-adic Fourier theory*, Documenta Math. 6 (2001), 447–481.
-/

public section

open Filter Topology ZeroAtInftyContinuousMap
open scoped ZeroAtInfty

variable {p : ℕ} [hp : Fact p.Prime]

namespace TauCeti.AnalyticStage

/-! ### Carry-binomial coefficients and the addition matrix -/

/-- The coefficient of `uⁱ vʲ` in `(q + u + v)ᵏ`. -/
private noncomputable def comulScalar (q : ℤ_[p]) (i j k : ℕ) : ℤ_[p] :=
  ((i + j).choose i : ℤ_[p]) * (k.choose (i + j) : ℤ_[p]) * q ^ (k - (i + j))

private theorem comulScalar_eq_zero_of_lt {q : ℤ_[p]} {i j k : ℕ} (hk : k < i + j) :
    comulScalar q i j k = 0 := by
  simp [comulScalar, Nat.choose_eq_zero_of_lt hk]

/-- Trinomial expansion of `(q + u + v)ᵏ` as a finite double sum in `uⁱ vʲ`. -/
private theorem add_add_pow_eq_sum_comulScalar (q u v : ℤ_[p]) (k : ℕ) :
    (q + u + v) ^ k =
      ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        u ^ i * v ^ j * comulScalar q i j k := by
  have h1 : (q + u + v) ^ k =
      ∑ m ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (k + 1),
        u ^ i * v ^ (m - i) * ((m.choose i : ℤ_[p]) * (k.choose m : ℤ_[p]) * q ^ (k - m)) := by
    have hcomm : q + u + v = (u + v) + q := by ring
    rw [hcomm, add_pow]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [add_pow, Finset.sum_mul, Finset.sum_mul,
      ← Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hmk))]
    · exact Finset.sum_congr rfl fun i _ ↦ by ring
    · intro i _ him
      have hmi : m < i := not_lt.mp (mt Finset.mem_range.mpr him)
      simp [Nat.choose_eq_zero_of_lt hmi]
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  let g : ℕ → ℤ_[p] := fun m ↦
    u ^ i * v ^ (m - i) * ((m.choose i : ℤ_[p]) * (k.choose m : ℤ_[p]) * q ^ (k - m))
  have hlhs : ∑ m ∈ Finset.range (k + 1), g m = ∑ j ∈ Finset.range (k + 1 - i), g (i + j) := by
    rw [← Finset.sum_range_add_sum_Ico g (Nat.le_succ_of_le hik),
      Finset.sum_eq_zero (fun m hm ↦ by
        simp [g, Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hm)]),
      zero_add, Finset.sum_Ico_eq_sum_range]
  have hrhs : ∑ j ∈ Finset.range (k + 1), u ^ i * v ^ j * comulScalar q i j k =
      ∑ j ∈ Finset.range (k + 1 - i), g (i + j) := by
    have hsub : Finset.range (k + 1 - i) ⊆ Finset.range (k + 1) :=
      Finset.range_mono (Nat.sub_le (k + 1) i)
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp [g, comulScalar]
    · intro j _ hj
      have hkj : k < i + j := by
        have := not_lt.mp (mt Finset.mem_range.mpr hj)
        omega
      simp [comulScalar_eq_zero_of_lt hkj]
  exact hlhs.trans hrhs.symm

variable (p) in
/-- The `ℤ_p`-matrix of two-variable addition re-expansion at analytic level `h`. -/
private noncomputable def comulMatrix (h : ℕ) :
    Matrix ((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ)) (ZMod (p ^ h) × ℕ) ℤ_[p] :=
  Matrix.of fun ⟨⟨a, i⟩, ⟨b, j⟩⟩ ⟨d, k⟩ ↦
    if a + b = d then comulScalar (((a.val + b.val) / p ^ h : ℕ) : ℤ_[p]) i j k else 0

private theorem comulMatrix_tendsto_cofinite (h : ℕ) (s : ZMod (p ^ h) × ℕ) :
    Tendsto (fun r ↦ comulMatrix p h r s) cofinite (𝓝 0) := by
  have hfin : {r : (ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ) |
      r.1.2 ≤ s.2 ∧ r.2.2 ≤ s.2}.Finite := by
    let box : Finset ((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ)) :=
      (Finset.univ ×ˢ Finset.range (s.2 + 1)) ×ˢ (Finset.univ ×ˢ Finset.range (s.2 + 1))
    refine box.finite_toSet.subset fun ⟨⟨a, i⟩, ⟨b, j⟩⟩ ⟨hi, hj⟩ ↦ ?_
    simp [box, Nat.lt_succ_of_le hi, Nat.lt_succ_of_le hj]
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [hfin.compl_mem_cofinite] with ⟨⟨a, i⟩, ⟨b, j⟩⟩ hr
  have hlt : s.2 < i + j := by
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_le] at hr
    omega
  simp [comulMatrix, comulScalar_eq_zero_of_lt hlt]

private theorem comulMatrix_norm_le_one (h : ℕ)
    (r : (ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ)) (s : ZMod (p ^ h) × ℕ) :
    ‖comulMatrix p h r s‖ ≤ 1 :=
  PadicInt.norm_le_one _

/-! ### Stage comultiplication -/

section Comul

variable {h : ℕ} {E F : Type*}
  [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]

section Semiring

variable (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-- **Two-variable addition re-expansion on the analytic stage `LA_h(E)`.** Sends a single-variable
coefficient vector `c` on the discs of level `h` to the two-variable coefficient family expanding
`eval c (x + y)` on products `(a + pʰℤ_p) × (b + pʰℤ_p)` of level-`h` discs. -/
noncomputable def comul :
    AnalyticStage p h E →L[S] C₀((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ), E) :=
  (comulMatrix p h).toZeroAtInftySMulCLM S
    (comulMatrix_tendsto_cofinite h) ⟨1, comulMatrix_norm_le_one h⟩

/-- **Curried stage comultiplication** `LA_h(E) →L[S] LA_h(LA_h(E))`, identifying the two-variable
model space with the iterated analytic stage via `ZeroAtInftyContinuousMap.curryEquiv`. -/
noncomputable def comulCurried :
    AnalyticStage p h E →L[S] AnalyticStage p h (AnalyticStage p h E) :=
  (curryEquiv (I := ZMod (p ^ h) × ℕ) (J := ZMod (p ^ h) × ℕ) S E)
    |>.toLinearIsometry.toContinuousLinearMap.comp (comul S)

/-- Currying `comul` gives `comulCurried`. -/
@[simp]
theorem curryEquiv_comul (c : AnalyticStage p h E) :
    curryEquiv S E (comul S c) = comulCurried S c := (rfl)

/-- Curried stage comultiplication applies `curryEquiv` to `comul`. -/
@[simp]
theorem comulCurried_apply_apply (c : AnalyticStage p h E) (x y : ZMod (p ^ h) × ℕ) :
    comulCurried S c x y = comul S c (x, y) := by
  rw [← curryEquiv_comul, curryEquiv_apply_apply]

/-- The carry-binomial coordinate formula for `comul`. -/
theorem comul_apply (c : AnalyticStage p h E) (a b : ZMod (p ^ h)) (i j : ℕ) :
    comul S c ((a, i), (b, j)) =
      ∑' k, (((i + j).choose i : ℤ_[p]) * (k.choose (i + j) : ℤ_[p]) *
        (((a.val + b.val) / p ^ h : ℕ) : ℤ_[p]) ^ (k - (i + j))) • c (a + b, k) := by
  rw [comul, Matrix.toZeroAtInftySMulCLM_apply]
  have hinj : Function.Injective fun k : ℕ ↦ (a + b, k) := fun _ _ h ↦ (Prod.ext_iff.mp h).2
  rw [← hinj.tsum_eq]
  · refine tsum_congr fun k ↦ ?_
    simp [comulMatrix, comulScalar]
  · rintro ⟨d, k⟩ hd
    by_cases hab : a + b = d
    · exact ⟨k, Prod.ext hab rfl⟩
    · exfalso
      exact hd (by simp [comulMatrix, hab])

/-- The underlying family of `comul S c` does not depend on the auxiliary scalar ring `S`. -/
theorem comul_eq_comul_padicInt (c : AnalyticStage p h E) :
    comul S c = comul ℤ_[p] c := by
  ext ⟨⟨a, i⟩, ⟨b, j⟩⟩
  rw [comul_apply, comul_apply]

/-- The underlying family of `comulCurried S c` does not depend on `S`. -/
theorem comulCurried_eq_comulCurried_padicInt (c : AnalyticStage p h E) :
    comulCurried S c = comulCurried ℤ_[p] c := by
  ext x y
  simp [comul_eq_comul_padicInt S c]

/-- **Right counit of `comul`.** Setting the second disc and degree to `(0, 0)` recovers `c`. -/
@[simp]
theorem comul_apply_zero_right (c : AnalyticStage p h E) (x : ZMod (p ^ h) × ℕ) :
    comul S c (x, (0, 0)) = c x := by
  rcases x with ⟨a, i⟩
  rw [comul_apply, tsum_eq_single i]
  · simp [Nat.div_eq_of_lt (ZMod.val_lt a)]
  · intro k hki
    rcases lt_trichotomy k i with hlt | rfl | hgt
    · simp [Nat.choose_eq_zero_of_lt hlt]
    · exact absurd rfl hki
    · have hsub : k - i ≠ 0 := by omega
      simp [Nat.div_eq_of_lt (ZMod.val_lt a), zero_pow hsub]

/-- **Cocommutativity of `comul`.** Swapping the two disc-and-degree factors leaves `comul S c`
unchanged, reflecting commutativity of addition on `ℤ_p`. -/
@[simp]
theorem congrLeft_prodComm_comul (c : AnalyticStage p h E) :
    congrLeft S E (Homeomorph.prodComm (ZMod (p ^ h) × ℕ) (ZMod (p ^ h) × ℕ)) (comul S c) =
      comul S c := by
  ext ⟨⟨a, i⟩, ⟨b, j⟩⟩
  simp only [congrLeft_apply, Homeomorph.prodComm_symm, Homeomorph.coe_prodComm, Prod.swap_prod_mk,
    comul_apply]
  refine tsum_congr fun k ↦ ?_
  rw [add_comm b a, add_comm b.val a.val, add_comm j i, Nat.choose_symm_add]

/-- **Left counit of `comul`.** Setting the first disc and degree to `(0, 0)` recovers `c`. -/
@[simp]
theorem comul_apply_zero_left (c : AnalyticStage p h E) (x : ZMod (p ^ h) × ℕ) :
    comul S c ((0, 0), x) = c x := by
  calc
    comul S c ((0, 0), x) =
        congrLeft S E (Homeomorph.prodComm _ _) (comul S c) ((0, 0), x) :=
      (DFunLike.congr_fun (congrLeft_prodComm_comul S c) ((0, 0), x)).symm
    _ = comul S c (x, (0, 0)) := by
      simp only [congrLeft_apply, Homeomorph.prodComm_symm, Homeomorph.coe_prodComm,
        Prod.swap_prod_mk]
    _ = c x := comul_apply_zero_right S c x

/-- Evaluating `comulCurried S c` at `(0, 0)` recovers `c`. -/
@[simp]
theorem comulCurried_apply_zero (c : AnalyticStage p h E) :
    comulCurried S c (0, 0) = c := by
  ext x
  simp

/-- Stage comultiplication preserves norms: `‖comul S c‖ = ‖c‖`. -/
@[simp]
theorem norm_comul (c : AnalyticStage p h E) : ‖comul S c‖ = ‖c‖ := by
  apply le_antisymm
  · simpa only [comul, one_mul] using
      (comulMatrix p h).norm_toZeroAtInftySMulCLM_apply_le S
        (comulMatrix_tendsto_cofinite h) ⟨1, comulMatrix_norm_le_one h⟩
        zero_le_one (comulMatrix_norm_le_one h) c
  · refine (ZeroAtInftyContinuousMap.norm_le (norm_nonneg (comul S c))).mpr fun x ↦ ?_
    rw [← comul_apply_zero_right S c x]
    exact (comul S c).norm_coe_le_norm (x, (0, 0))

/-- Curried stage comultiplication is also norm-preserving. -/
@[simp]
theorem norm_comulCurried (c : AnalyticStage p h E) : ‖comulCurried S c‖ = ‖c‖ := by
  rw [← curryEquiv_comul S, LinearIsometryEquiv.norm_map, norm_comul]

/-- Curried stage comultiplication is uniformly bounded, in the form required by
`ZeroAtInftyContinuousMap.compLeft`. -/
theorem exists_norm_comulCurried_le :
    ∃ C, ∀ c : AnalyticStage p h E, ‖comulCurried S c‖ ≤ C * ‖c‖ :=
  ⟨1, fun c ↦ by simpa only [one_mul] using (norm_comulCurried S c).le⟩

/-- Over a nontrivially normed field, `comul` has operator norm at most `1`. -/
theorem opNorm_comul_le_one {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℤ_[p] 𝕜 E] : ‖comul (p := p) (h := h) (E := E) 𝕜‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun c ↦ by simp

/-- On a degree-`k` coordinate vector `single (d, k) e`, all rows of `comulCurried` above degree `k`
vanish, truncating the outer stage evaluation to `Finset.range (k + 1)`. -/
private theorem eval_comulCurried_single_eq_sum (d a : ZMod (p ^ h)) (k : ℕ) (e : E) (u : ℤ_[p]) :
    eval ℤ_[p] (comulCurried ℤ_[p] (single (d, k) e)) (PadicInt.discHomeomorph p h (a, u)) =
      ∑ i ∈ Finset.range (k + 1), u ^ i • comulCurried ℤ_[p] (single (d, k) e) (a, i) := by
  rw [PadicInt.discHomeomorph_apply, eval_natCast_val_add_mul]
  refine tsum_eq_sum fun i hi ↦ ?_
  have hki : k < i := not_lt.mp (mt Finset.mem_range.mpr hi)
  have hrow : comulCurried ℤ_[p] (single (d, k) e) (a, i) = 0 := by
    ext ⟨b', j⟩
    rw [comulCurried_apply_apply, comul, Matrix.toZeroAtInftySMulCLM_single_apply]
    have hkij : k < i + j := by omega
    simp [comulMatrix, comulScalar_eq_zero_of_lt hkij]
  simp [hrow]

/-- Each row of `comulCurried ℤ_[p] (single (d, k) e)` vanishes above degree `k`, truncating the
inner stage evaluation to `Finset.range (k + 1)`. -/
private theorem eval_comulCurried_single_apply_eq_sum (d a b : ZMod (p ^ h)) (k i : ℕ) (e : E)
    (v : ℤ_[p]) :
    eval ℤ_[p] (comulCurried ℤ_[p] (single (d, k) e) (a, i))
        (PadicInt.discHomeomorph p h (b, v)) =
      ∑ j ∈ Finset.range (k + 1), v ^ j • comul ℤ_[p] (single (d, k) e) ((a, i), (b, j)) := by
  rw [PadicInt.discHomeomorph_apply, eval_natCast_val_add_mul]
  simp_rw [comulCurried_apply_apply]
  refine tsum_eq_sum fun j hj ↦ ?_
  have hkj : k < j := not_lt.mp (mt Finset.mem_range.mpr hj)
  have hkij : k < i + j := by omega
  rw [comul, Matrix.toZeroAtInftySMulCLM_single_apply]
  simp [comulMatrix, comulScalar_eq_zero_of_lt hkij]

private theorem eval_eval_comulCurried_single (d : ZMod (p ^ h)) (k : ℕ) (e : E) (x y : ℤ_[p]) :
    eval ℤ_[p] (eval ℤ_[p] (comulCurried ℤ_[p] (single (d, k) e)) x) y =
      eval ℤ_[p] (single (d, k) e) (x + y) := by
  -- Write `x` and `y` in level-`h` disc coordinates `(a, u)` and `(b, v)`.
  obtain ⟨⟨a, u⟩, rfl⟩ := (PadicInt.discHomeomorph p h).surjective x
  obtain ⟨⟨b, v⟩, rfl⟩ := (PadicInt.discHomeomorph p h).surjective y
  -- Truncate both the outer and inner series to `range (k + 1)` and match the trinomial sum.
  rw [eval_comulCurried_single_eq_sum, map_sum, ContinuousMap.coe_sum, Finset.sum_apply]
  simp_rw [map_smul, ContinuousMap.smul_apply, eval_comulCurried_single_apply_eq_sum,
    Finset.smul_sum, comul, Matrix.toZeroAtInftySMulCLM_single_apply]
  rw [PadicInt.discHomeomorph_add, PadicInt.discHomeomorph_apply, eval_natCast_val_add_mul,
    tsum_eq_single k (fun n hn ↦ by simp [single_apply, hn])]
  by_cases hab : a + b = d
  · simp only [comulMatrix, Matrix.of_apply, hab, ↓reduceIte, single_apply, smul_smul,
      ← Finset.sum_smul]
    rw [add_add_pow_eq_sum_comulScalar]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  · simp [comulMatrix, hab, single_apply]

/-- **Compatibility of `comulCurried` with addition on `ℤ_p`.** Iterated stage evaluation of
`comulCurried S c` at `(x, y)` equals `eval S c (x + y)`. -/
@[simp]
theorem eval_eval_comulCurried (c : AnalyticStage p h E) (x y : ℤ_[p]) :
    eval S (eval S (comulCurried S c) x) y = eval S c (x + y) := by
  rw [eval_eq_eval_padicInt S (eval S (comulCurried S c) x),
    eval_eq_eval_padicInt S (comulCurried S c), comulCurried_eq_comulCurried_padicInt S c,
    eval_eq_eval_padicInt S c]
  let L₁ : AnalyticStage p h E →L[ℤ_[p]] E :=
    ((ContinuousMap.evalCLM ℤ_[p] y).comp (eval ℤ_[p])).comp
      (((ContinuousMap.evalCLM ℤ_[p] x).comp (eval ℤ_[p])).comp (comulCurried ℤ_[p]))
  let L₂ : AnalyticStage p h E →L[ℤ_[p]] E :=
    (ContinuousMap.evalCLM ℤ_[p] (x + y)).comp (eval ℤ_[p])
  have hL : L₁ = L₂ :=
    continuousLinearMap_ext fun ⟨d, k⟩ e ↦ eval_eval_comulCurried_single d k e x y
  exact DFunLike.congr_fun hL c

end Semiring

/-! ### Functoriality, transition compatibility, and coassociativity -/

section Identities

variable [NormedAddCommGroup F] [Module ℤ_[p] F] [IsBoundedSMul ℤ_[p] F]
  [IsUltrametricDist F] [CompleteSpace F]
  (S : Type*) [Semiring S]
  [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]
  [Module S F] [ContinuousConstSMul S F] [SMulCommClass ℤ_[p] S F]
  [LinearMap.CompatibleSMul E F ℤ_[p] S]

/-- Stage comultiplication commutes with any uniformly bounded coefficient map compatible with
`ℤ_p`. -/
theorem comul_compLeft (φ : E →L[S] F) (hφ : ∃ C, ∀ e, ‖φ e‖ ≤ C * ‖e‖)
    (c : AnalyticStage p h E) :
    comul S (compLeft φ hφ c) = compLeft φ hφ (comul S c) := by
  ext r
  rw [comul, comul, compLeft_apply]
  refine ((comulMatrix p h).hasSum_toZeroAtInftySMulCLM_apply S
    (comulMatrix_tendsto_cofinite h) ⟨1, comulMatrix_norm_le_one h⟩ (compLeft φ hφ c) r).unique ?_
  simpa only [compLeft_apply, ContinuousLinearMap.map_smul_of_tower] using
    ((comulMatrix p h).hasSum_toZeroAtInftySMulCLM_apply S
      (comulMatrix_tendsto_cofinite h) ⟨1, comulMatrix_norm_le_one h⟩ c r).mapL φ

/-- Curried stage comultiplication commutes with any uniformly bounded coefficient map compatible
with `ℤ_p`. -/
theorem comulCurried_compLeft (φ : E →L[S] F) (hφ : ∃ C, ∀ e, ‖φ e‖ ≤ C * ‖e‖)
    (c : AnalyticStage p h E) :
    comulCurried S (compLeft φ hφ c) =
      compLeft (compLeft φ hφ) (exists_norm_compLeft_apply_le φ hφ) (comulCurried S c) := by
  ext x y
  simp only [comulCurried_apply_apply, compLeft_apply]
  rw [comul_compLeft (p := p) S φ hφ c, compLeft_apply]

end Identities

section Structural

variable (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

private theorem comulCurried_transition_padicInt (c : AnalyticStage p h ℤ_[p]) :
    transition ℤ_[p]
        (compLeft (transition ℤ_[p]) (exists_norm_transition_le ℤ_[p]) (comulCurried ℤ_[p] c)) =
      comulCurried ℤ_[p] (transition ℤ_[p] c) := by
  apply eval_injective ℤ_[p] PadicInt.isSMulRegular_natCast_p.zeroAtInftyContinuousMap
  refine ContinuousMap.ext fun x ↦ ?_
  apply eval_injective ℤ_[p] PadicInt.isSMulRegular_natCast_p
  refine ContinuousMap.ext fun y ↦ ?_
  simp [eval_compLeft]

/-- **Curried stage comultiplication commutes with level transitions.** -/
theorem transition_compLeft_transition_comulCurried (c : AnalyticStage p h E) :
    transition S (compLeft (transition S) (exists_norm_transition_le S) (comulCurried S c)) =
      comulCurried S (transition S c) := by
  -- Reduce to `S = ℤ_p` and test on coordinate vectors `single s e`, written as images of
  -- `single s (1 : ℤ_p)` under `r ↦ r • e` so functoriality reduces to the torsion-free `ℤ_p` case.
  have hcomp : (transition (p := p) (h := h) ℤ_[p]).comp
        ((compLeft (transition ℤ_[p]) (exists_norm_transition_le ℤ_[p])).comp
          (comulCurried ℤ_[p])) =
      (comulCurried (p := p) (h := h + 1) (E := E) ℤ_[p]).comp (transition ℤ_[p]) := by
    refine continuousLinearMap_ext fun s e ↦ ?_
    let φ : ℤ_[p] →L[ℤ_[p]] E := ContinuousLinearMap.toSpanSingleton ℤ_[p] e
    let hφ := ContinuousLinearMap.exists_norm_toSpanSingleton_apply_le ℤ_[p] e
    have hs : compLeft φ hφ (single s (1 : ℤ_[p])) = single s e := by simp [φ]
    simp only [ContinuousLinearMap.comp_apply, ← hs]
    have hswap : compLeft (transition ℤ_[p]) (exists_norm_transition_le ℤ_[p])
          (compLeft (compLeft φ hφ) (exists_norm_compLeft_apply_le φ hφ)
            (comulCurried ℤ_[p] (single s (1 : ℤ_[p])))) =
        compLeft (compLeft φ hφ) (exists_norm_compLeft_apply_le φ hφ)
          (compLeft (transition ℤ_[p]) (exists_norm_transition_le ℤ_[p])
            (comulCurried ℤ_[p] (single s (1 : ℤ_[p])))) := by
      ext u
      simp [transition_compLeft]
    rw [comulCurried_compLeft, hswap, transition_compLeft, comulCurried_transition_padicInt,
      ← comulCurried_compLeft, ← transition_compLeft]
  have harg : compLeft (transition S) (exists_norm_transition_le S) (comulCurried S c) =
      compLeft (transition ℤ_[p]) (exists_norm_transition_le ℤ_[p]) (comulCurried ℤ_[p] c) := by
    ext u
    simp [transition_eq_transition_padicInt S, comulCurried_eq_comulCurried_padicInt S]
  rw [transition_eq_transition_padicInt S, harg, comulCurried_eq_comulCurried_padicInt S,
    transition_eq_transition_padicInt S c]
  exact DFunLike.congr_fun hcomp c

private theorem comulCurried_comulCurried_padicInt (c : AnalyticStage p h ℤ_[p]) :
    comulCurried ℤ_[p] (comulCurried ℤ_[p] c) =
      compLeft (comulCurried ℤ_[p]) (exists_norm_comulCurried_le ℤ_[p]) (comulCurried ℤ_[p] c) := by
  apply eval_injective ℤ_[p]
    PadicInt.isSMulRegular_natCast_p.zeroAtInftyContinuousMap.zeroAtInftyContinuousMap
  refine ContinuousMap.ext fun x ↦ ?_
  apply eval_injective ℤ_[p] PadicInt.isSMulRegular_natCast_p.zeroAtInftyContinuousMap
  refine ContinuousMap.ext fun y ↦ ?_
  apply eval_injective ℤ_[p] PadicInt.isSMulRegular_natCast_p
  refine ContinuousMap.ext fun z ↦ ?_
  simp [eval_compLeft, add_assoc]

/-- **Coassociativity of curried stage comultiplication.** Re-expanding twice in the outer slot
equals re-expanding in the inner slot after re-expanding once; holds for every complete ultrametric
`ℤ_p`-module `E`, including torsion modules. -/
theorem comulCurried_comulCurried (c : AnalyticStage p h E) :
    comulCurried S (comulCurried S c) =
      compLeft (comulCurried S) (exists_norm_comulCurried_le S) (comulCurried S c) := by
  have hcomp : (comulCurried (p := p) (h := h) (E := AnalyticStage p h E) ℤ_[p]).comp
        (comulCurried ℤ_[p]) =
      (compLeft (comulCurried ℤ_[p]) (exists_norm_comulCurried_le ℤ_[p])).comp
        (comulCurried ℤ_[p]) := by
    refine continuousLinearMap_ext fun s e ↦ ?_
    let φ : ℤ_[p] →L[ℤ_[p]] E := ContinuousLinearMap.toSpanSingleton ℤ_[p] e
    let hφ := ContinuousLinearMap.exists_norm_toSpanSingleton_apply_le ℤ_[p] e
    have hs : compLeft φ hφ (single s (1 : ℤ_[p])) = single s e := by simp [φ]
    simp only [ContinuousLinearMap.comp_apply, ← hs]
    rw [comulCurried_compLeft, comulCurried_compLeft, comulCurried_comulCurried_padicInt]
    ext u
    simp [comulCurried_compLeft]
  have hpadic := DFunLike.congr_fun hcomp c
  ext u v w
  have huvw := DFunLike.congr_fun
    (DFunLike.congr_fun (DFunLike.congr_fun hpadic u) v) w
  simpa only [ContinuousLinearMap.comp_apply, compLeft_apply,
    comulCurried_eq_comulCurried_padicInt S] using huvw

end Structural

end Comul

/-- Stage evaluation of a curried outer product `curryEquiv R R (prodMul a b)` at `x` scales the
second factor `b` by `eval R a x`. -/
@[simp]
theorem eval_curryEquiv_prodMul {h : ℕ} {R : Type*} [NormedRing R] [Algebra ℤ_[p] R]
    [IsBoundedSMul ℤ_[p] R] [IsUltrametricDist R] [CompleteSpace R]
    (a b : AnalyticStage p h R) (x : ℤ_[p]) :
    eval R (curryEquiv R R (prodMul a b)) x = eval R a x • b := by
  rw [curryEquiv_prodMul_eq_compLeft, eval_compLeft R, ContinuousLinearMap.toSpanSingleton_apply]

end TauCeti.AnalyticStage

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.InnerProductSpace.Variational.FormEigenspace
import TauCeti.Analysis.InnerProductSpace.LinearPMap.ClosedForm.Basic

/-!
# Courant–Fischer on the form domain of a compact form pair

Let `P` be a compact form pair over `𝕜 = ℝ` or `ℂ`: a compact injective inclusion `j : V → H` of
dense range and a bounded Hermitian form `a` on `V` whose energy `q(u) = re a(u, u)` satisfies
`c ‖u‖² ≤ q(u) + ω ‖j u‖²` with `c > 0`. For a submodule `L` of `V` and `n : ℕ`, the
**min–max value** (`TauCeti.CompactFormPair.rayleighMinMax`) is

`inf_{M ≤ L, dim M = n + 1} sup_{u ∈ M, u ≠ 0} q(u) / ‖j u‖²`.

When `L` has no `(n + 1)`-dimensional subspace the infimum is over the empty set and the value is
the junk value `0` (`TauCeti.CompactFormPair.rayleighMinMax_eq_zero`). The Rayleigh quotient is
bounded below by `-ω` on all of `V`, and above on every finite-dimensional `M`, because `j` is
bounded below there; so the infimum and the suprema are genuine.

The main theorem is the **Courant–Fischer min–max principle on the form domain**
(`TauCeti.CompactFormPair.eigenvalue_eq_rayleighMinMax`): if `j u₀, j u₁, …` is a Hilbert basis of
`H` formed by variational eigenvectors, `a(uₖ, v) = λₖ ⟪j uₖ, j v⟫` for every `v`, with
`λ₀ ≤ λ₁ ≤ ⋯`, then `λₙ = rayleighMinMax ⊤ n`. In particular the eigenvalue sequence does not
depend on the choice of the eigenbasis
(`TauCeti.CompactFormPair.eigenvalue_eq_of_hilbertBasis`). The argument:

* on the span of `u₀, …, uₙ` the form is diagonal, so `q(v) ≤ λₙ ‖j v‖²` there, with equality at
  `uₙ` (`TauCeti.CompactFormPair.energy_le_mul_norm_sq_of_mem_span`,
  `TauCeti.CompactFormPair.iSup_rayleigh_span_eq`);
* **Bessel's inequality for the shifted energy**: for every finite set of indices,
  `∑ₖ (λₖ + α) |⟪j uₖ, j v⟫|² ≤ q(v) + α ‖j v‖²` whenever `q + α ‖j ·‖² ≥ 0`
  (`TauCeti.CompactFormPair.sum_mul_norm_inner_sq_le_energy_add`); with Parseval's identity this
  gives `λₙ ‖j v‖² ≤ q(v)` whenever `j v` is orthogonal to `j u₀, …, j uₙ₋₁`
  (`TauCeti.CompactFormPair.mul_norm_sq_le_energy_of_forall_inner_eq_zero`). Since `λₙ + α` may
  be negative for an arbitrary shift, the estimate is made termwise and only the lower bound
  `λₖ ≥ λₙ` for `k ≥ n` is used;
* every subspace of dimension at least `n + 1` contains a nonzero `v` with `j v` orthogonal to the
  `n` vectors `j u₀, …, j uₙ₋₁`
  (`TauCeti.CompactFormPair.exists_mem_ne_zero_mul_norm_sq_le_energy`).

The obstacle count is the first `n` eigenvectors for an `(n + 1)`-dimensional subspace. No
divergence `λₙ → ∞` and no completeness of `V` are used. For a real nonnegative form on a vector
space the same principle, in its least-bound form, is `TauCeti.isLeast_minMax_of_hilbertBasis`;
here the scalars are `ℝ` or `ℂ` and the form is only bounded below after a shift.

## References

* V. Ivrii, *Partial Differential Equations*, Chapter 13, §13.1, Corollary 1. As printed it
  imposes `n` obstacle conditions on an `n`-dimensional subspace, which may leave only `0`; the
  count used here is `n` conditions on an `(n + 1)`-dimensional subspace.
* R. Courant and D. Hilbert, *Methods of Mathematical Physics*, Vol. I, Chapter VI, §1.
-/

public section

open Filter RCLike
open scoped ComplexConjugate InnerProductSpace Topology

namespace TauCeti

namespace CompactFormPair

variable {𝕜 V H : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (P : CompactFormPair 𝕜 V H)

/-! ### The min–max value -/

/-- The **min–max value** of a compact form pair on a submodule `L` of `V`: the infimum, over the
`(n + 1)`-dimensional submodules `M ≤ L`, of the supremum of the Rayleigh quotient
`q(u) / ‖j u‖²` over the nonzero `u ∈ M`. When `L` has no `(n + 1)`-dimensional submodule it is
the junk value `0`. -/
noncomputable def rayleighMinMax (L : Submodule 𝕜 V) (n : ℕ) : ℝ :=
  ⨅ M : {M : Submodule 𝕜 V // M ≤ L ∧ Module.finrank 𝕜 M = n + 1},
    ⨆ u : {u : V // u ∈ M.val ∧ u ≠ 0}, P.energy u / ‖P.inclusion u‖ ^ 2

theorem rayleighMinMax_def (L : Submodule 𝕜 V) (n : ℕ) :
    P.rayleighMinMax L n =
      ⨅ M : {M : Submodule 𝕜 V // M ≤ L ∧ Module.finrank 𝕜 M = n + 1},
        ⨆ u : {u : V // u ∈ M.val ∧ u ≠ 0}, P.energy u / ‖P.inclusion u‖ ^ 2 :=
  (rfl)

/-- The Rayleigh quotient `q(u) / ‖j u‖²` is bounded below on `V`. -/
theorem bddBelow_range_rayleigh :
    BddBelow (Set.range fun u : V ↦ P.energy u / ‖P.inclusion u‖ ^ 2) := by
  obtain ⟨c, hc, ω, h⟩ := P.exists_mul_norm_sq_le_energy_add
  refine ⟨-max ω 0, ?_⟩
  rintro _ ⟨u, rfl⟩
  rcases eq_or_ne (P.inclusion u) 0 with hu | hu
  · simp [hu]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [h u, le_max_left ω 0, le_max_right ω 0, sq_nonneg ‖u‖, sq_nonneg ‖P.inclusion u‖]

/-- On a finite-dimensional submodule `M` of `V` the Rayleigh quotient `q(u) / ‖j u‖²` of the
nonzero `u ∈ M` is bounded above: `j` is injective, hence bounded below on `M`. -/
theorem bddAbove_range_rayleigh (M : Submodule 𝕜 V) [FiniteDimensional 𝕜 M] :
    BddAbove (Set.range fun u : {u : V // u ∈ M ∧ u ≠ 0} ↦
      P.energy u / ‖P.inclusion u‖ ^ 2) := by
  have hinj : Function.Injective ((P.inclusion : V →ₗ[𝕜] H) ∘ₗ M.subtype) :=
    P.injective.comp Subtype.val_injective
  obtain ⟨K, -, hK⟩ := (LinearMap.injective_iff_antilipschitz _).1 hinj
  refine ⟨‖P.form‖ * K ^ 2, ?_⟩
  rintro _ ⟨⟨u, huM, hu0⟩, rfl⟩
  have hju : 0 < ‖P.inclusion u‖ := norm_pos_iff.2 ((map_ne_zero_iff _ P.injective).2 hu0)
  have hnorm : ‖u‖ ≤ K * ‖P.inclusion u‖ :=
    ZeroHomClass.bound_of_antilipschitz _ hK (⟨u, huM⟩ : M)
  have hq : P.energy u ≤ ‖P.form‖ * ‖u‖ ^ 2 := by
    rw [energy_def, sq, ← mul_assoc]
    exact (re_le_norm _).trans (P.form.le_opNorm₂ u u)
  rw [div_le_iff₀ (by positivity)]
  calc P.energy u ≤ ‖P.form‖ * ‖u‖ ^ 2 := hq
    _ ≤ ‖P.form‖ * (K * ‖P.inclusion u‖) ^ 2 := by gcongr
    _ = ‖P.form‖ * K ^ 2 * ‖P.inclusion u‖ ^ 2 := by ring

variable {P}

/-- The supremum of the Rayleigh quotient over the nonzero vectors of a submodule of positive
finite dimension is at least its value at any such vector. -/
private theorem rayleigh_le_iSup {M : Submodule 𝕜 V} [FiniteDimensional 𝕜 M] {u : V}
    (huM : u ∈ M) (hu0 : u ≠ 0) :
    P.energy u / ‖P.inclusion u‖ ^ 2 ≤
      ⨆ w : {w : V // w ∈ M ∧ w ≠ 0}, P.energy w / ‖P.inclusion w‖ ^ 2 :=
  le_ciSup (f := fun w : {w : V // w ∈ M ∧ w ≠ 0} ↦ P.energy w / ‖P.inclusion w‖ ^ 2)
    (P.bddAbove_range_rayleigh M) ⟨u, huM, hu0⟩

/-- The suprema in the definition of `rayleighMinMax` are bounded below uniformly in `M`. -/
private theorem bddBelow_range_iSup_rayleigh (L : Submodule 𝕜 V) (n : ℕ) :
    BddBelow (Set.range fun M : {M : Submodule 𝕜 V // M ≤ L ∧ Module.finrank 𝕜 M = n + 1} ↦
      ⨆ u : {u : V // u ∈ M.val ∧ u ≠ 0}, P.energy u / ‖P.inclusion u‖ ^ 2) := by
  obtain ⟨C, hC⟩ := P.bddBelow_range_rayleigh
  refine ⟨C, ?_⟩
  rintro _ ⟨⟨M, -, hM⟩, rfl⟩
  have : FiniteDimensional 𝕜 M := Module.finite_of_finrank_pos (by omega)
  obtain ⟨u, huM, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.one_le_finrank_iff.1 (by omega) : M ≠ ⊥)
  exact (hC ⟨u, rfl⟩).trans (rayleigh_le_iSup huM hu0)

/-- The min–max value of `L` is at most the supremum of the Rayleigh quotient on any
`(n + 1)`-dimensional submodule `M ≤ L`. -/
theorem rayleighMinMax_le_iSup {L M : Submodule 𝕜 V} {n : ℕ} (hML : M ≤ L)
    (hM : Module.finrank 𝕜 M = n + 1) :
    P.rayleighMinMax L n ≤ ⨆ u : {u : V // u ∈ M ∧ u ≠ 0}, P.energy u / ‖P.inclusion u‖ ^ 2 :=
  ciInf_le (bddBelow_range_iSup_rayleigh L n) ⟨M, hML, hM⟩

/-- A lower bound for the min–max value: if `L` has an `(n + 1)`-dimensional submodule, and every
such submodule contains a nonzero `u` with Rayleigh quotient at least `C`, then
`C ≤ rayleighMinMax L n`. -/
theorem le_rayleighMinMax {L : Submodule 𝕜 V} {n : ℕ} {C : ℝ}
    (hL : ∃ M ≤ L, Module.finrank 𝕜 M = n + 1)
    (h : ∀ M ≤ L, Module.finrank 𝕜 M = n + 1 →
      ∃ u ∈ M, u ≠ 0 ∧ C ≤ P.energy u / ‖P.inclusion u‖ ^ 2) :
    C ≤ P.rayleighMinMax L n := by
  obtain ⟨M₀, hM₀L, hM₀⟩ := hL
  have : Nonempty {M : Submodule 𝕜 V // M ≤ L ∧ Module.finrank 𝕜 M = n + 1} :=
    ⟨⟨M₀, hM₀L, hM₀⟩⟩
  refine le_ciInf fun ⟨M, hML, hM⟩ ↦ ?_
  have : FiniteDimensional 𝕜 M := Module.finite_of_finrank_pos (by omega)
  obtain ⟨u, huM, hu0, hCu⟩ := h M hML hM
  exact hCu.trans (rayleigh_le_iSup huM hu0)

/-- **The junk value.** If `L` has no `(n + 1)`-dimensional submodule, its min–max value is `0`. -/
theorem rayleighMinMax_eq_zero {L : Submodule 𝕜 V} {n : ℕ}
    (h : ∀ M ≤ L, Module.finrank 𝕜 M ≠ n + 1) : P.rayleighMinMax L n = 0 := by
  have : IsEmpty {M : Submodule 𝕜 V // M ≤ L ∧ Module.finrank 𝕜 M = n + 1} :=
    ⟨fun M ↦ h M.val M.property.1 M.property.2⟩
  exact Real.iInf_of_isEmpty _

/-- **Monotonicity in the subspace.** Enlarging `L` can only lower the min–max value, as long as
the smaller subspace has an `(n + 1)`-dimensional submodule. -/
theorem rayleighMinMax_le_rayleighMinMax_of_le {L L' : Submodule 𝕜 V} {n : ℕ} (hLL' : L ≤ L')
    (hL : ∃ M ≤ L, Module.finrank 𝕜 M = n + 1) :
    P.rayleighMinMax L' n ≤ P.rayleighMinMax L n := by
  obtain ⟨M₀, hM₀L, hM₀⟩ := hL
  have : Nonempty {M : Submodule 𝕜 V // M ≤ L ∧ Module.finrank 𝕜 M = n + 1} :=
    ⟨⟨M₀, hM₀L, hM₀⟩⟩
  exact le_ciInf fun ⟨_, hML, hM⟩ ↦ rayleighMinMax_le_iSup (hML.trans hLL') hM

/-! ### Estimates along an orthonormal family of eigenvectors -/

section Eigenvectors

/-- **Bessel's inequality for the shifted energy.** Let `u` be variational eigenvectors,
`a(uₖ, v) = λₖ ⟪j uₖ, j v⟫`, with orthonormal images `j uₖ`, and let `α` be a shift for which
`q + α ‖j ·‖²` is nonnegative. Then for every finite set `s` of indices,
`∑_{k ∈ s} (λₖ + α) |⟪j uₖ, j v⟫|² ≤ q(v) + α ‖j v‖²`. -/
theorem sum_mul_norm_inner_sq_le_energy_add {ι : Type*} {u : ι → V} {lam : ι → ℝ} {α : ℝ}
    (hα : ∀ w, 0 ≤ P.energy w + α * ‖P.inclusion w‖ ^ 2)
    (hu : Orthonormal 𝕜 fun k ↦ P.inclusion (u k)) (heq : ∀ k, u k ∈ P.formEigenspace (lam k))
    (v : V) (s : Finset ι) :
    ∑ k ∈ s, (lam k + α) * ‖⟪P.inclusion (u k), P.inclusion v⟫_𝕜‖ ^ 2 ≤
      P.energy v + α * ‖P.inclusion v‖ ^ 2 := by
  set B := ContinuousLinearMap.shiftedForm P.inclusion P.form α
  set d : ι → 𝕜 := fun k ↦ ⟪P.inclusion (u k), P.inclusion v⟫_𝕜
  set w := ∑ k ∈ s, d k • u k
  -- The shifted form is diagonal along the eigenvectors, with entries `λₖ + α`.
  have hBw (x : V) :
      B w x = ∑ k ∈ s,
        conj (d k) * (((lam k + α : ℝ) : 𝕜) * ⟪P.inclusion (u k), P.inclusion x⟫_𝕜) := by
    simp only [w, B, map_sum, map_smulₛₗ, FunLike.coe_sum, Finset.sum_apply,
      smul_apply, smul_eq_mul, ContinuousLinearMap.shiftedForm_apply,
      mem_formEigenspace.1 (heq _), ofReal_add, add_mul]
  have hsum : B w v = ((∑ k ∈ s, (lam k + α) * ‖d k‖ ^ 2 : ℝ) : 𝕜) := by
    rw [hBw]
    push_cast
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← RCLike.conj_mul]
    ring
  have hww : B w w = B w v := by
    rw [hBw, hBw]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    simp only [w, map_sum, map_smul, hu.inner_right_sum d hk, d]
  have hvw : B v w = star (B w v) :=
    ContinuousLinearMap.shiftedForm_eq_star P.inclusion P.hermitian α v w
  have hnn : 0 ≤ re (B (v - w) (v - w)) := by
    rw [ContinuousLinearMap.re_shiftedForm_self, ← energy_def]
    exact hα _
  have hre : re (B (v - w) (v - w)) = re (B v v) - re (B w v) := by
    simp only [map_sub, sub_apply, hww, hvw, star_def, conj_re]
    ring
  rw [hre, ContinuousLinearMap.re_shiftedForm_self, hsum, ofReal_re] at hnn
  rw [energy_def]
  linarith

/-- **The upper half of Courant–Fischer.** Let `u₀, u₁, …` be variational eigenvectors,
`a(uₖ, v) = λₖ ⟪j uₖ, j v⟫`, with orthonormal images `j uₖ` and `λᵢ ≤ λₙ` for `i ≤ n`. Every `v`
in the span of `u₀, …, uₙ` has `q(v) ≤ λₙ ‖j v‖²`. -/
theorem energy_le_mul_norm_sq_of_mem_span {u : ℕ → V} {lam : ℕ → ℝ} {n : ℕ}
    (hlam : ∀ i ≤ n, lam i ≤ lam n) (hu : Orthonormal 𝕜 fun k ↦ P.inclusion (u k))
    (heq : ∀ k, u k ∈ P.formEigenspace (lam k)) {v : V}
    (hv : v ∈ Submodule.span 𝕜 (Set.range fun i : Fin (n + 1) ↦ u i)) :
    P.energy v ≤ lam n * ‖P.inclusion v‖ ^ 2 := by
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).1 hv
  have he : Orthonormal 𝕜 fun i : Fin (n + 1) ↦ P.inclusion (u i) := hu.comp _ Fin.val_injective
  set v := ∑ i, d i • u i with hv_def
  have hj : P.inclusion v = ∑ i, d i • P.inclusion (u i) := by
    simp only [v, map_sum, map_smul]
  -- The form is diagonal along the eigenvectors, and the coordinates of `j v` are the `d i`.
  have hform : P.form v v = ∑ i : Fin (n + 1), conj (d i) * ((lam i : 𝕜) * d i) := by
    nth_rewrite 1 [hv_def]
    simp only [map_sum, map_smulₛₗ, FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul,
      mem_formEigenspace.1 (heq _), hj, he.inner_right_fintype]
  have hq : P.energy v = ∑ i : Fin (n + 1), lam i * ‖d i‖ ^ 2 := by
    rw [energy_def, hform, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_left_comm, RCLike.conj_mul, ← ofReal_pow, ← ofReal_mul, ofReal_re]
  have hnorm : ‖P.inclusion v‖ ^ 2 = ∑ i, ‖d i‖ ^ 2 := by
    rw [hj, ← ofReal_inj (K := 𝕜)]
    push_cast
    rw [← inner_self_eq_norm_sq_to_K, he.inner_sum]
    exact Finset.sum_congr rfl fun i _ ↦ RCLike.conj_mul _
  rw [hq, hnorm, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦
    mul_le_mul_of_nonneg_right (hlam i (Nat.lt_succ_iff.1 i.isLt)) (sq_nonneg _)

/-- **The lower half of Courant–Fischer.** Let `j u₀, j u₁, …` be a Hilbert basis of `H` formed by
variational eigenvectors, with eigenvalues `λₖ ≥ λₙ` for `k ≥ n`. If `j v` is orthogonal to
`j u₀, …, j uₙ₋₁`, then `λₙ ‖j v‖² ≤ q(v)`. -/
theorem mul_norm_sq_le_energy_of_forall_inner_eq_zero (b : HilbertBasis ℕ 𝕜 H) {u : ℕ → V}
    {lam : ℕ → ℝ} {n : ℕ} (hb : ∀ k, P.inclusion (u k) = b k) (hlam : ∀ k, n ≤ k → lam n ≤ lam k)
    (heq : ∀ k, u k ∈ P.formEigenspace (lam k)) {v : V}
    (hv : ∀ k < n, ⟪b k, P.inclusion v⟫_𝕜 = 0) :
    lam n * ‖P.inclusion v‖ ^ 2 ≤ P.energy v := by
  obtain ⟨c, hc, ω, h⟩ := P.exists_mul_norm_sq_le_energy_add
  have hω (w : V) : 0 ≤ P.energy w + ω * ‖P.inclusion w‖ ^ 2 :=
    (by positivity : 0 ≤ c * ‖w‖ ^ 2).trans (h w)
  have hu : Orthonormal 𝕜 fun k ↦ P.inclusion (u k) := by simpa only [hb] using b.orthonormal
  -- Bessel's inequality for the shifted energy, with `λₖ ≥ λₙ` on the nonzero coefficients.
  have hpartial (N : ℕ) :
      (lam n + ω) * ∑ k ∈ Finset.range N, ‖⟪b k, P.inclusion v⟫_𝕜‖ ^ 2 ≤
        P.energy v + ω * ‖P.inclusion v‖ ^ 2 := by
    refine le_trans ?_ (sum_mul_norm_inner_sq_le_energy_add hω hu heq v (Finset.range N))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ ↦ ?_
    rw [hb]
    rcases lt_or_ge k n with hk | hk
    · simp [hv k hk]
    · gcongr
      exact hlam k hk
  -- Parseval's identity `∑ₖ |⟪b k, j v⟫|² = ‖j v‖²`.
  have hlim := ((b.hasSum_norm_inner_sq (P.inclusion v)).tendsto_sum_nat).const_mul (lam n + ω)
  have := le_of_tendsto' hlim hpartial
  linarith

/-- **The obstacle estimate.** In the setting of
`TauCeti.CompactFormPair.mul_norm_sq_le_energy_of_forall_inner_eq_zero`, every submodule `M` of `V`
of dimension at least `n + 1` contains some `v ≠ 0` with `λₙ ‖j v‖² ≤ q(v)`: the `n` conditions
`⟪j uₖ, j v⟫ = 0`, `k < n`, have a nonzero common solution in `M`. -/
theorem exists_mem_ne_zero_mul_norm_sq_le_energy (b : HilbertBasis ℕ 𝕜 H) {u : ℕ → V}
    {lam : ℕ → ℝ} {n : ℕ} (hb : ∀ k, P.inclusion (u k) = b k) (hlam : ∀ k, n ≤ k → lam n ≤ lam k)
    (heq : ∀ k, u k ∈ P.formEigenspace (lam k)) {M : Submodule 𝕜 V}
    (hM : n + 1 ≤ Module.finrank 𝕜 M) :
    ∃ v ∈ M, v ≠ 0 ∧ lam n * ‖P.inclusion v‖ ^ 2 ≤ P.energy v := by
  have : FiniteDimensional 𝕜 M := Module.finite_of_finrank_pos (by omega)
  let f : M →ₗ[𝕜] Fin n → 𝕜 := LinearMap.pi fun k ↦
    (innerₛₗ 𝕜 (b k)) ∘ₗ (P.inclusion : V →ₗ[𝕜] H) ∘ₗ M.subtype
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := f) (by rw [Module.finrank_fin_fun]; omega))
  refine ⟨x, x.property, fun h ↦ hx0 (Subtype.ext h),
    mul_norm_sq_le_energy_of_forall_inner_eq_zero b hb hlam heq fun k hk ↦ ?_⟩
  simpa [f] using congrFun (LinearMap.mem_ker.1 hx) ⟨k, hk⟩

/-- **Attainment of the min–max value.** For variational eigenvectors `u₀, u₁, …` with orthonormal
images and eigenvalues `λᵢ ≤ λₙ` for `i ≤ n`, the supremum of the Rayleigh quotient over the
nonzero vectors of the span of `u₀, …, uₙ` is `λₙ`, attained at `uₙ`. -/
theorem iSup_rayleigh_span_eq {u : ℕ → V} {lam : ℕ → ℝ} {n : ℕ}
    (hlam : ∀ i ≤ n, lam i ≤ lam n) (hu : Orthonormal 𝕜 fun k ↦ P.inclusion (u k))
    (heq : ∀ k, u k ∈ P.formEigenspace (lam k)) :
    ⨆ v : {v : V // v ∈ Submodule.span 𝕜 (Set.range fun i : Fin (n + 1) ↦ u i) ∧ v ≠ 0},
      P.energy v / ‖P.inclusion v‖ ^ 2 = lam n := by
  have hun : u n ∈ Submodule.span 𝕜 (Set.range fun i : Fin (n + 1) ↦ u i) :=
    Submodule.subset_span ⟨Fin.last n, rfl⟩
  have hjun : ‖P.inclusion (u n)‖ = 1 := hu.1 n
  have hun0 : u n ≠ 0 := fun h ↦ by simp [h] at hjun
  have hle (v : {v : V // v ∈ Submodule.span 𝕜 (Set.range fun i : Fin (n + 1) ↦ u i) ∧ v ≠ 0}) :
      P.energy v / ‖P.inclusion v‖ ^ 2 ≤ lam n := by
    have hjv : 0 < ‖P.inclusion v‖ :=
      norm_pos_iff.2 ((map_ne_zero_iff _ P.injective).2 v.property.2)
    rw [div_le_iff₀ (by positivity)]
    exact energy_le_mul_norm_sq_of_mem_span hlam hu heq v.property.1
  have : Nonempty
      {v : V // v ∈ Submodule.span 𝕜 (Set.range fun i : Fin (n + 1) ↦ u i) ∧ v ≠ 0} :=
    ⟨⟨u n, hun, hun0⟩⟩
  refine le_antisymm (ciSup_le hle) (le_ciSup_of_le ⟨lam n, Set.forall_mem_range.2 hle⟩
    ⟨u n, hun, hun0⟩ ?_)
  simp [hjun, energy_eq_of_mem_formEigenspace (heq n)]

/-- **The Courant–Fischer min–max principle on the form domain.** Let `j u₀, j u₁, …` be a Hilbert
basis of `H` formed by variational eigenvectors, `a(uₖ, v) = λₖ ⟪j uₖ, j v⟫` for every `v`, with
nondecreasing eigenvalues `λₖ`. Then `λₙ` is the min–max value
`inf_{dim M = n + 1} sup_{u ∈ M, u ≠ 0} q(u) / ‖j u‖²` of the whole form domain. The infimum is
attained on the span of `u₀, …, uₙ` (`TauCeti.CompactFormPair.iSup_rayleigh_span_eq`). -/
theorem eigenvalue_eq_rayleighMinMax (b : HilbertBasis ℕ 𝕜 H) {u : ℕ → V} {lam : ℕ → ℝ}
    (hb : ∀ k, P.inclusion (u k) = b k) (hlam : Monotone lam)
    (heq : ∀ k, u k ∈ P.formEigenspace (lam k)) (n : ℕ) :
    lam n = P.rayleighMinMax ⊤ n := by
  have hu : Orthonormal 𝕜 fun k ↦ P.inclusion (u k) := by simpa only [hb] using b.orthonormal
  -- The span of `u₀, …, uₙ` has dimension `n + 1`, since the images `j uᵢ` are orthonormal.
  have hli : LinearIndependent 𝕜 fun i : Fin (n + 1) ↦ u i :=
    ((hu.comp _ Fin.val_injective).linearIndependent).of_comp (P.inclusion : V →ₗ[𝕜] H)
  have hspan : Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range fun i : Fin (n + 1) ↦ u i)) =
      n + 1 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  refine le_antisymm (le_rayleighMinMax ⟨_, le_top, hspan⟩ fun M _ hM ↦ ?_) ?_
  · obtain ⟨v, hvM, hv0, hv⟩ :=
      exists_mem_ne_zero_mul_norm_sq_le_energy b hb (fun _ hk ↦ hlam hk) heq (M := M) hM.ge
    have hjv : 0 < ‖P.inclusion v‖ := norm_pos_iff.2 ((map_ne_zero_iff _ P.injective).2 hv0)
    exact ⟨v, hvM, hv0, (le_div_iff₀ (by positivity)).2 hv⟩
  · exact (rayleighMinMax_le_iSup le_top hspan).trans
      (iSup_rayleigh_span_eq (fun _ hi ↦ hlam hi) hu heq).le

/-- **The eigenvalues do not depend on the eigenbasis.** Two Hilbert bases of `H` formed by
variational eigenvectors with nondecreasing eigenvalues have the same eigenvalue sequence. -/
theorem eigenvalue_eq_of_hilbertBasis (b b' : HilbertBasis ℕ 𝕜 H) {u u' : ℕ → V}
    {lam lam' : ℕ → ℝ} (hb : ∀ k, P.inclusion (u k) = b k) (hb' : ∀ k, P.inclusion (u' k) = b' k)
    (hlam : Monotone lam) (hlam' : Monotone lam') (heq : ∀ k, u k ∈ P.formEigenspace (lam k))
    (heq' : ∀ k, u' k ∈ P.formEigenspace (lam' k)) : lam = lam' :=
  funext fun n ↦ (eigenvalue_eq_rayleighMinMax b hb hlam heq n).trans
    (eigenvalue_eq_rayleighMinMax b' hb' hlam' heq' n).symm

end Eigenvectors

end CompactFormPair

end TauCeti

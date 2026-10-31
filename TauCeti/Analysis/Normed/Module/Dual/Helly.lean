/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Normed.Module.Dual.Goldstine

/-!
# Helly's lemma

**Helly's lemma** solves finitely many linear equations in a normed space with almost optimal
norm. If `φ` is an element of the bidual of a normed space `E` and `f₁, …, fₙ` are continuous
linear functionals on `E`, then for every `ε > 0` there is `x : E` with `‖x‖ < ‖φ‖ + ε` and
`fᵢ x = φ fᵢ` for every `i`. Equivalently, every finite-dimensional subspace `W` of the dual
admits such an `x` interpolating `φ` on all of `W`. The tolerance cannot be removed in general:
for a single functional `f` and a norm-one `φ` with `φ f = ‖f‖`, a solution of norm at most one
would be a point of the closed unit ball where `f` attains its norm.

Classically the lemma is stated without the bidual: prescribed values `cᵢ` of the functionals
`fᵢ` are attained by vectors of norm less than `M + ε` for every `ε > 0` if and only if
`‖∑ aᵢ cᵢ‖ ≤ M ‖∑ aᵢ fᵢ‖` for all scalars `aᵢ`.

These finite interpolation statements are the basic finite-system tool behind the principle of
local reflexivity, which upgrades them to linear maps from finite-dimensional subspaces of the
bidual into `E`. This is unrelated to Helly's intersection theorem for convex sets
(`Convex.helly_theorem` in `Mathlib.Analysis.Convex.Radon`).

## Main results

* `StrongDual.exists_norm_lt_and_forall_apply_eq`: Helly's lemma for a finite family of
  functionals and an element of the bidual.
* `StrongDual.exists_norm_lt_and_forall_mem_apply_eq`: the same for a finite-dimensional
  subspace of the dual.
* `StrongDual.norm_sum_apply_comp_single_le`: a coordinatewise bound for functionals on a finite
  product `κ → E`, paired with bidual vectors of norm at most one.
* `TauCeti.exists_norm_lt_and_forall_apply_eq_iff`: Helly's criterion for prescribed values.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Lemma 3.3.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §12.2 (the principle of local
  reflexivity).
-/

public section

open Metric

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace StrongDual

/-- **Helly's lemma.** For an element `φ` of the bidual of `E`, finitely many continuous linear
functionals `f i` on `E` and `ε > 0`, some `x : E` with `‖x‖ < ‖φ‖ + ε` satisfies
`f i x = φ (f i)` for every `i`. -/
theorem exists_norm_lt_and_forall_apply_eq (φ : StrongDual 𝕜 (StrongDual 𝕜 E)) {ι : Type*}
    [Finite ι] (f : ι → StrongDual 𝕜 E) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : E, ‖x‖ < ‖φ‖ + ε ∧ ∀ i, f i x = φ (f i) := by
  cases nonempty_fintype ι
  let T : E →L[𝕜] ι → 𝕜 := ContinuousLinearMap.pi f
  let c : ι → 𝕜 := fun i ↦ φ (f i)
  -- By Goldstine's theorem, the values of `φ` are approximated by those of vectors of norm at
  -- most `‖φ‖`.
  have happrox : ∀ δ > 0, ∃ x ∈ closedBall (0 : E) ‖φ‖, ‖T x - c‖ < δ := by
    intro δ hδ
    have hφ : toWeakDual φ ∈ closure (NormedSpace.inclusionInDoubleDualWeak 𝕜 E ''
        (toWeakSpace 𝕜 E '' closedBall 0 ‖φ‖)) := by
      rw [NormedSpace.closure_image_inclusionInDoubleDualWeak_closedBall, map_zero,
        Set.mem_preimage, StrongDual.toStrongDual_toWeakDual]
      exact (mem_closedBall_zero_iff (E := StrongDual 𝕜 (StrongDual 𝕜 E))).2 le_rfl
    have hU : IsOpen {ψ : WeakDual 𝕜 (StrongDual 𝕜 E) | ∀ i, ‖ψ (f i) - c i‖ < δ} := by
      simp only [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun i ↦ isOpen_lt
        (((WeakDual.eval_continuous (f i)).sub continuous_const).norm) continuous_const
    obtain ⟨_, hψ, _, ⟨x, hx, rfl⟩, rfl⟩ :=
      mem_closure_iff.1 hφ _ hU fun i ↦ by simpa [c] using hδ
    refine ⟨x, hx, (pi_norm_lt_iff hδ).2 fun i ↦ ?_⟩
    have hψi := hψ i
    rw [NormedSpace.inclusionInDoubleDualWeak_apply, LinearEquiv.symm_apply_apply,
      StrongDual.toWeakDual_apply, NormedSpace.dual_def] at hψi
    simpa [T] using hψi
  -- The vector of values lies in the range of `T`, which is closed in finite dimension.
  let R := LinearMap.range (T : E →ₗ[𝕜] ι → 𝕜)
  have hc : c ∈ R := by
    refine (Submodule.closed_of_finiteDimensional R).closure_subset
      (Metric.mem_closure_iff.2 fun δ hδ ↦ ?_)
    obtain ⟨x, -, hx⟩ := happrox δ hδ
    exact ⟨T x, LinearMap.mem_range_self _ x, by rwa [dist_comm, dist_eq_norm]⟩
  -- Correct an approximate solution by a bounded right inverse of `T` onto its range.
  obtain ⟨S, hS⟩ :=
    T.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict _)
  obtain ⟨x₀, hx₀, hT⟩ := happrox (ε / (‖S‖ + 1)) (by positivity)
  let v : R := ⟨c - T x₀, sub_mem hc (LinearMap.mem_range_self _ x₀)⟩
  have hTS : T (S v) = c - T x₀ := congr(($hS v : ι → 𝕜))
  refine ⟨x₀ + S v, ?_, fun i ↦ ?_⟩
  · have hv : ‖v‖ < ε / (‖S‖ + 1) := (norm_sub_rev _ _).trans_lt hT
    have hSv : ‖S v‖ < ε := by
      calc ‖S v‖ ≤ ‖S‖ * ‖v‖ := S.le_opNorm v
        _ ≤ ‖S‖ * (ε / (‖S‖ + 1)) := by gcongr
        _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg S]
    calc ‖x₀ + S v‖ ≤ ‖x₀‖ + ‖S v‖ := norm_add_le _ _
      _ < ‖φ‖ + ε := add_lt_add_of_le_of_lt (mem_closedBall_zero_iff.1 hx₀) hSv
  · have := congr_fun hTS i
    simp only [T, ContinuousLinearMap.pi_apply, Pi.sub_apply] at this
    simp [map_add, this, c]

/-- **Helly's lemma** for a finite-dimensional subspace `W` of the dual: for an element `φ` of
the bidual of `E` and `ε > 0`, some `x : E` with `‖x‖ < ‖φ‖ + ε` satisfies `f x = φ f` for
every `f ∈ W`. -/
theorem exists_norm_lt_and_forall_mem_apply_eq (φ : StrongDual 𝕜 (StrongDual 𝕜 E))
    (W : Submodule 𝕜 (StrongDual 𝕜 E)) [FiniteDimensional 𝕜 W] {ε : ℝ} (hε : 0 < ε) :
    ∃ x : E, ‖x‖ < ‖φ‖ + ε ∧ ∀ f ∈ W, f x = φ f := by
  -- Interpolate on a finite spanning set of `W`; both sides are linear in the functional.
  obtain ⟨s, rfl⟩ := (Submodule.fg_iff_finiteDimensional W).2 ‹_›
  obtain ⟨x, hx, hs⟩ := φ.exists_norm_lt_and_forall_apply_eq ((↑) : s → StrongDual 𝕜 E) hε
  refine ⟨x, hx, fun f hf ↦ ?_⟩
  exact LinearMap.eqOn_span' (f := (ContinuousLinearMap.apply 𝕜 𝕜 x : StrongDual 𝕜 E →ₗ[𝕜] 𝕜))
    (g := (φ : StrongDual 𝕜 E →ₗ[𝕜] 𝕜)) (fun g hg ↦ hs ⟨g, hg⟩) hf

/-- **Helly's lemma**, coordinatewise: a functional `f` of norm at most one on a finite product
`κ → E` pairs bidual vectors `z i` of norm at most one with its coordinate functionals
`f ∘ single i` to a value of norm at most one. -/
theorem norm_sum_apply_comp_single_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : StrongDual 𝕜 (κ → E)) (hf : ‖f‖ ≤ 1) (z : κ → StrongDual 𝕜 (StrongDual 𝕜 E))
    (hz : ∀ i, ‖z i‖ ≤ 1) :
    ‖∑ i, z i (f.comp (.single 𝕜 (fun _ ↦ E) i))‖ ≤ 1 := by
  refine le_of_forall_pos_le_add fun η hη ↦ ?_
  have he : ∀ i, ∃ e : E, ‖e‖ < 1 + η ∧
      f.comp (.single 𝕜 (fun _ ↦ E) i) e = z i (f.comp (.single 𝕜 (fun _ ↦ E) i)) := by
    intro i
    obtain ⟨e, he, hhe⟩ := StrongDual.exists_norm_lt_and_forall_apply_eq
      (z i) (fun _ : Unit ↦ f.comp (.single 𝕜 (fun _ ↦ E) i)) hη
    exact ⟨e, he.trans_le (by simpa using hz i), hhe ()⟩
  choose e he hhe using he
  calc ‖∑ i, z i (f.comp (.single 𝕜 (fun _ ↦ E) i))‖ = ‖f e‖ := by
        rw [← ContinuousLinearMap.sum_comp_single (L := f) (v := e)]
        simp only [hhe]
    _ ≤ ‖f‖ * ‖e‖ := f.le_opNorm e
    _ ≤ 1 * (1 + η) := by
        gcongr
        exact (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ (he i).le
    _ = 1 + η := one_mul _

end StrongDual

namespace TauCeti

/-- **Helly's criterion.** Let `f i` be finitely many continuous linear functionals on `E`, let
`c i` be scalars and let `0 ≤ M`. For every `ε > 0` some `x : E` with `‖x‖ < M + ε` satisfies
`f i x = c i` for every `i` if and only if `‖∑ i, a i * c i‖ ≤ M * ‖∑ i, a i • f i‖` for all
scalars `a i`. -/
theorem exists_norm_lt_and_forall_apply_eq_iff {ι : Type*} [Fintype ι]
    (f : ι → StrongDual 𝕜 E) (c : ι → 𝕜) {M : ℝ} (hM : 0 ≤ M) :
    (∀ ε > 0, ∃ x : E, ‖x‖ < M + ε ∧ ∀ i, f i x = c i) ↔
      ∀ a : ι → 𝕜, ‖∑ i, a i * c i‖ ≤ M * ‖∑ i, a i • f i‖ := by
  refine ⟨fun h a ↦ le_of_forall_pos_le_add fun ε hε ↦ ?_, fun h ε hε ↦ ?_⟩
  · -- Solutions of norm close to `M` bound the values of the combination `∑ i, a i • f i`.
    set g := ∑ i, a i • f i
    obtain ⟨x, hx, hfx⟩ := h (ε / (‖g‖ + 1)) (by positivity)
    have hgx : g x = ∑ i, a i * c i := by simp [g, hfx]
    rw [← hgx]
    calc ‖g x‖ ≤ ‖g‖ * ‖x‖ := g.le_opNorm x
      _ ≤ ‖g‖ * (M + ε / (‖g‖ + 1)) := by gcongr
      _ ≤ M * ‖g‖ + ε := by
        have : ‖g‖ * (ε / (‖g‖ + 1)) ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith [norm_nonneg g]
        nlinarith
  · classical
    -- The prescribed values define a functional of norm at most `M` on the span of the `f i`,
    -- which Hahn–Banach extends to the bidual; Helly's lemma then applies.
    let L := Fintype.linearCombination 𝕜 f
    let l := Fintype.linearCombination 𝕜 c
    have hl : ∀ a, ‖l a‖ ≤ M * ‖L a‖ := fun a ↦ by
      simpa [L, l, Fintype.linearCombination_apply, smul_eq_mul] using h a
    have hker : LinearMap.ker L ≤ LinearMap.ker l := fun a ha ↦ by
      have := hl a
      rw [LinearMap.mem_ker.1 ha, norm_zero, mul_zero, norm_le_zero_iff] at this
      exact this
    let ψ : LinearMap.range L →ₗ[𝕜] 𝕜 :=
      (LinearMap.ker L).liftQ l hker ∘ₗ L.quotKerEquivRange.symm.toLinearMap
    have hψ : ∀ a, ψ ⟨L a, LinearMap.mem_range_self L a⟩ = l a := fun a ↦ by
      simp [ψ, LinearMap.quotKerEquivRange_symm_apply_image]
    have hψM : ∀ w, ‖ψ w‖ ≤ M * ‖w‖ := by
      rintro ⟨_, a, rfl⟩
      rw [hψ]
      exact hl a
    obtain ⟨φ, hφ, hφn⟩ := exists_extension_norm_eq (LinearMap.range L) (ψ.mkContinuous M hψM)
    obtain ⟨x, hx, hfx⟩ := φ.exists_norm_lt_and_forall_apply_eq f hε
    refine ⟨x, hx.trans_le ?_, fun i ↦ ?_⟩
    · rw [hφn]
      gcongr
      exact ContinuousLinearMap.opNorm_le_bound _ hM hψM
    · have hLi : L (Pi.single i 1) = f i := by
        simp [L, Fintype.linearCombination_apply]
      have := hφ ⟨L (Pi.single i 1), LinearMap.mem_range_self L _⟩
      simp only [LinearMap.mkContinuous_apply, hψ] at this
      rw [hfx, ← hLi]
      simpa [l, Fintype.linearCombination_apply, Pi.single_apply] using this

end TauCeti

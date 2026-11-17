/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.FilledHull
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Units
import TauCeti.Analysis.Complex.Pompeiu.Discretization
import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Geometry.Manifold.Connected

/-!
# Runge approximation by rational functions with prescribed poles

Let `K ⊆ ℂ` be a compact set and `A ⊆ ℂ` a prescribed set of poles.

* **Prescribed finite poles (pole at `∞` allowed)** (`TauCeti.exists_rational_norm_inv_sub_lt`,
  `TauCeti.exists_rational_norm_sub_sum_smul_le`, `TauCeti.exists_rational_norm_sub_lt`): if `A`
  meets every bounded connected component of `Kᶜ`, then every function holomorphic on an open
  neighbourhood of `K` can be uniformly approximated on `K` by rational functions `p / q` whose
  finite poles lie in `A \ K`, via a finite-rank operator with rational kernels depending only on
  `K`, `V`, `A`, and `ε`. The simple-fraction step uses Mathlib's spectral pole-pushing theorem
  (`Subalgebra.spectrum_sUnion_connectedComponentIn` and
  `Subalgebra.spectrum_isBounded_connectedComponentIn`) on the uniform closure of the algebra of
  rational functions on `K` with poles in `A \ K`; the finite-rank operator follows by discretizing
  the Cauchy–Pompeiu formula (`IsCompact.exists_norm_sub_sum_mul_sub_inv_smul_le`).
* **Prescribed poles on the Riemann sphere (no pole at `∞`)**
  (`TauCeti.exists_rational_natDegree_le_norm_sub_lt`): if `A` meets every connected component of
  `Kᶜ`, including the unbounded component, then the rational approximant `p / q` can additionally
  be taken bounded at `∞`, i.e. with `p.natDegree ≤ q.natDegree`. Choosing `a₀ ∈ A \ filledHull K`,
  the Möbius inversion `z ↦ (z - a₀)⁻¹` sends `a₀` to `∞` and `∞` to `0`, keeping `0` in the
  unbounded component of the inverted complement (since removing `{a₀}` from the open unbounded
  component leaves it connected by
  `TauCeti.isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank`), and homogenizing the
  resulting approximant in `(z - a₀)` yields `p.natDegree ≤ q.natDegree`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 11.7, p. 29.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.6.
-/

public section

open Bornology Metric Polynomial Set Topology

universe u

namespace TauCeti

/-! ### Algebra of rational functions with prescribed poles -/

/-- The complex subalgebra of `C(K, ℂ)` consisting of functions represented on `K` by a rational
function `p / q` with `q ≠ 0` and all roots of `q` in `A \ K`. -/
private noncomputable def rationalSubalgebra (K A : Set ℂ) : Subalgebra ℂ C(K, ℂ) where
  carrier := {g : C(K, ℂ) | ∃ p q : ℂ[X], q ≠ 0 ∧ (∀ z, q.eval z = 0 → z ∈ A \ K) ∧
    ∀ z : K, g z = p.eval (z : ℂ) / q.eval (z : ℂ)}
  mul_mem' := by
    rintro _ _ ⟨p₁, q₁, hq₁, hA₁, hg₁⟩ ⟨p₂, q₂, hq₂, hA₂, hg₂⟩
    refine ⟨p₁ * p₂, q₁ * q₂, mul_ne_zero hq₁ hq₂, fun z hz ↦ ?_, fun z ↦ ?_⟩
    · rcases (by simpa [eval_mul] using hz : q₁.eval z = 0 ∨ q₂.eval z = 0) with h | h
      · exact hA₁ z h
      · exact hA₂ z h
    · simp [hg₁ z, hg₂ z, div_mul_div_comm]
  add_mem' := by
    rintro _ _ ⟨p₁, q₁, hq₁, hA₁, hg₁⟩ ⟨p₂, q₂, hq₂, hA₂, hg₂⟩
    refine ⟨p₁ * q₂ + p₂ * q₁, q₁ * q₂, mul_ne_zero hq₁ hq₂, fun z hz ↦ ?_, fun z ↦ ?_⟩
    · rcases (by simpa [eval_mul] using hz : q₁.eval z = 0 ∨ q₂.eval z = 0) with h | h
      · exact hA₁ z h
      · exact hA₂ z h
    · have h1 : q₁.eval (z : ℂ) ≠ 0 := fun h ↦ (hA₁ z h).2 z.2
      have h2 : q₂.eval (z : ℂ) ≠ 0 := fun h ↦ (hA₂ z h).2 z.2
      simp only [ContinuousMap.add_apply, hg₁ z, hg₂ z, eval_add, eval_mul]
      rw [div_add_div _ _ h1 h2, mul_comm (q₁.eval (z : ℂ)) (p₂.eval (z : ℂ))]
  algebraMap_mem' c := ⟨C c, 1, one_ne_zero, fun _ h ↦ by simp at h, fun _ ↦ by simp⟩

/-- The coordinate map `z ↦ z` belongs to `rationalSubalgebra K A`. -/
private theorem mem_rationalSubalgebra_coord (K A : Set ℂ) :
    (⟨Subtype.val, continuous_subtype_val⟩ : C(K, ℂ)) ∈ rationalSubalgebra K A :=
  ⟨X, 1, one_ne_zero, fun _ h ↦ by simp at h, fun _ ↦ by simp⟩

/-- For any `b ∈ A \ K`, the simple fraction `z ↦ (b - z)⁻¹` belongs to `rationalSubalgebra K A`. -/
private theorem mem_rationalSubalgebra_inv_sub {K A : Set ℂ} {b : ℂ} (hb : b ∈ A \ K) :
    ∃ y ∈ rationalSubalgebra K A, ∀ z : K, y z = (b - (z : ℂ))⁻¹ := by
  have hcont : Continuous (fun z : K ↦ (b - (z : ℂ))⁻¹) :=
    (continuous_const.sub continuous_subtype_val).inv₀ fun z h ↦
      hb.2 (sub_eq_zero.mp (by simpa using h) ▸ z.2)
  refine ⟨⟨_, hcont⟩, ⟨1, C b - X, ?_, ?_, fun z ↦ by simp⟩, fun _ ↦ rfl⟩
  · intro h
    have := congrArg (eval (b + 1)) h
    simp at this
  · intro z hz
    have hbz : b = z := sub_eq_zero.mp (by simpa using hz)
    exact hbz ▸ hb

/-! ### Rational Runge approximation with prescribed finite poles -/

/-- **Simple-fraction rational Runge approximation.** If `K ⊆ ℂ` is compact and `A ⊆ ℂ` meets
every bounded connected component of `Kᶜ`, then every simple fraction `(z - a)⁻¹` with `a ∉ K` is
uniformly approximable on `K` by rational functions whose finite poles lie in `A \ K`. -/
theorem exists_rational_norm_inv_sub_lt {K A : Set ℂ} (hK : IsCompact K)
    (hA : ∀ x ∈ filledHull K \ K, (A ∩ connectedComponentIn Kᶜ x).Nonempty)
    {a : ℂ} (ha : a ∉ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ (∀ z, q.eval z = 0 → z ∈ A \ K) ∧
      ∀ z ∈ K, ‖(z - a)⁻¹ - p.eval z / q.eval z‖ < ε := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let R := rationalSubalgebra K A
  let S := R.topologicalClosure
  let : IsClosed (S : Set C(K, ℂ)) := R.isClosed_topologicalClosure
  let x : S := ⟨⟨Subtype.val, continuous_subtype_val⟩,
    R.le_topologicalClosure (mem_rationalSubalgebra_coord K A)⟩
  have hxval (z : K) : (x : C(K, ℂ)) z = z := rfl
  have hx : spectrum ℂ (x : C(K, ℂ)) = K := by
    rw [ContinuousMap.spectrum_eq_range]
    exact Subtype.range_coe
  have houtside (b : ℂ) (hb : b ∈ A \ K) : b ∉ spectrum ℂ x := by
    obtain ⟨y, hyR, hyval⟩ := mem_rationalSubalgebra_inv_sub hb
    rw [spectrum.notMem_iff, isUnit_iff_exists_inv]
    refine ⟨⟨y, R.le_topologicalClosure hyR⟩, Subtype.ext <| ContinuousMap.ext fun z ↦ ?_⟩
    simpa [x, hyval z] using mul_inv_cancel₀ (sub_ne_zero.mpr fun h : b = (z : ℂ) ↦ hb.2 (h ▸ z.2))
  have hspec : a ∉ spectrum ℂ x := by
    intro haspec
    have hbd := Subalgebra.spectrum_isBounded_connectedComponentIn S x haspec
    rw [hx] at hbd
    obtain ⟨b, hbA, hbc⟩ := hA a ⟨mem_filledHull_iff.mpr hbd, ha⟩
    apply houtside b ⟨hbA, connectedComponentIn_subset _ _ hbc⟩
    rw [Subalgebra.spectrum_sUnion_connectedComponentIn S x]
    exact Or.inr <| mem_biUnion ⟨haspec, by rwa [hx]⟩ <| by rwa [hx]
  have hu : IsUnit (x - algebraMap ℂ S a) := by
    simpa only [neg_sub] using (spectrum.notMem_iff.mp hspec).neg
  let v : S := ↑hu.unit⁻¹
  have hv (z : K) : (v : C(K, ℂ)) z = ((z : ℂ) - a)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    have h := congrArg (fun f : S ↦ (f : C(K, ℂ)) z) hu.unit.inv_mul
    simpa only [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one,
      Subalgebra.coe_algebraMap, ContinuousMap.mul_apply, ContinuousMap.sub_apply,
      ContinuousMap.one_apply, _root_.algebraMap_apply, smul_eq_mul, mul_one,
      IsUnit.unit_spec, hxval] using h
  obtain ⟨g, ⟨p, q, hq, hqA, hgval⟩, hdist⟩ := Metric.mem_closure_iff.mp v.property ε hε
  refine ⟨p, q, hq, hqA, fun z hz ↦ ?_⟩
  rw [← hgval ⟨z, hz⟩, ← hv ⟨z, hz⟩]
  exact lt_of_le_of_lt ((v.val - g).norm_coe_le_norm ⟨z, hz⟩) (by simpa [dist_eq_norm] using hdist)

/-- A finite linear combination of rational functions with poles in `A \ K` agrees on `K` with a
single rational function whose poles lie in `A \ K`. -/
private theorem exists_rational_sum_smul_eq {K A : Set ℂ} {N : ℕ} (a : Fin N → ℂ)
    (p_i q_i : Fin N → ℂ[X]) (hq_i : ∀ i, q_i i ≠ 0)
    (hqA_i : ∀ i z, (q_i i).eval z = 0 → z ∈ A \ K) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ (∀ z, q.eval z = 0 → z ∈ A \ K) ∧
      ∀ z ∈ K, p.eval z / q.eval z = ∑ i, a i * ((p_i i).eval z / (q_i i).eval z) := by
  let g_i (i : Fin N) : C(K, ℂ) :=
    ⟨fun z : K ↦ (p_i i).eval (z : ℂ) / (q_i i).eval (z : ℂ),
      ((Polynomial.differentiable (p_i i)).continuous.comp continuous_subtype_val).div
        ((Polynomial.differentiable (q_i i)).continuous.comp continuous_subtype_val)
        fun z h ↦ (hqA_i i z h).2 z.2⟩
  have hg_mem (i : Fin N) : g_i i ∈ rationalSubalgebra K A :=
    ⟨p_i i, q_i i, hq_i i, hqA_i i, fun _ ↦ rfl⟩
  have hG_mem : (∑ i : Fin N, a i • g_i i) ∈ rationalSubalgebra K A :=
    Subalgebra.sum_mem _ fun i _ ↦ Subalgebra.smul_mem _ (hg_mem i) _
  obtain ⟨p, q, hq, hqA, hGval⟩ := hG_mem
  refine ⟨p, q, hq, hqA, fun z hz ↦ ?_⟩
  simpa [g_i, ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply] using
    (hGval ⟨z, hz⟩).symm

/-- **Finite-rank rational Runge approximation operator.** Let `K ⊆ ℂ` be compact, `V ⊆ ℂ` an open
neighbourhood of `K`, and `A ⊆ ℂ` a set meeting every bounded connected component of `Kᶜ`. For
every `ε > 0` there are finitely many points `ζ i ∈ V \ K` and rational kernels `p i / q i` with
poles in `A \ K` such that every `f : ℂ → F` into a complex normed space, holomorphic on `V` and
bounded by `M` there, satisfies `‖f w - ∑ i, ((p i).eval w / (q i).eval w) • f (ζ i)‖ ≤ ε * M` for
all `w ∈ K`. The points and rational kernels depend only on `K`, `V`, `A`, and `ε`. -/
theorem exists_rational_norm_sub_sum_smul_le {K V A : Set ℂ} (hK : IsCompact K) (hV : IsOpen V)
    (hKV : K ⊆ V) (hA : ∀ x ∈ filledHull K \ K, (A ∩ connectedComponentIn Kᶜ x).Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (ζ : Fin N → ℂ) (p q : Fin N → ℂ[X]),
      (∀ i, ζ i ∈ V \ K) ∧ (∀ i, q i ≠ 0) ∧ (∀ i z, (q i).eval z = 0 → z ∈ A \ K) ∧
      ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] (f : ℂ → F) (M : ℝ),
        DifferentiableOn ℂ f V → (∀ z ∈ V, ‖f z‖ ≤ M) →
        ∀ w ∈ K, ‖f w - ∑ i, ((p i).eval w / (q i).eval w) • f (ζ i)‖ ≤ ε * M := by
  obtain ⟨N, ζ, c, hζ, hdisc⟩ :=
    hK.exists_norm_sub_sum_mul_sub_inv_smul_le.{u} hV hKV (half_pos hε)
  set S : ℝ := ∑ i : Fin N, ‖c i‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  set δ : ℝ := ε / (2 * (S + 1))
  have hδ : 0 < δ := by positivity
  choose p_i q_i hq_i hqA_i happrox using fun i : Fin N ↦
    exists_rational_norm_inv_sub_lt hK hA (hζ i).2 hδ
  refine ⟨N, ζ, fun i ↦ C (c i) * p_i i, q_i, hζ, hq_i, hqA_i,
    fun {F} _ _ f M hf hM w hw ↦ ?_⟩
  have hM0 : 0 ≤ M := (norm_nonneg (f w)).trans (hM w (hKV hw))
  have hsplit : f w - ∑ i, ((C (c i) * p_i i).eval w / (q_i i).eval w) • f (ζ i) =
      (f w - ∑ i, (c i * (w - ζ i)⁻¹) • f (ζ i)) +
        ∑ i, (c i * ((w - ζ i)⁻¹ - (p_i i).eval w / (q_i i).eval w)) • f (ζ i) := by
    rw [sub_add, ← Finset.sum_sub_distrib]
    refine congrArg (f w - ·) (Finset.sum_congr rfl fun i _ ↦ ?_)
    rw [← sub_smul, eval_mul, eval_C]
    congr 1; ring
  have htail :
      ‖∑ i, (c i * ((w - ζ i)⁻¹ - (p_i i).eval w / (q_i i).eval w)) • f (ζ i)‖ ≤ ε / 2 * M := by
    calc ‖∑ i, (c i * ((w - ζ i)⁻¹ - (p_i i).eval w / (q_i i).eval w)) • f (ζ i)‖
        ≤ ∑ i, ‖(c i * ((w - ζ i)⁻¹ - (p_i i).eval w / (q_i i).eval w)) • f (ζ i)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i, ‖c i‖ * δ * M := Finset.sum_le_sum fun i _ ↦ by
          rw [norm_smul, norm_mul]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (happrox i w hw).le (norm_nonneg _))
            (hM (ζ i) (hζ i).1) (norm_nonneg _) (by positivity)
      _ = S * δ * M := by simp [S, Finset.sum_mul]
      _ ≤ (S + 1) * δ * M := by gcongr; linarith
      _ = ε / 2 * M := by simp only [δ]; field_simp [show S + 1 ≠ 0 by linarith]
  rw [hsplit]
  calc ‖(f w - ∑ i, (c i * (w - ζ i)⁻¹) • f (ζ i)) +
          ∑ i, (c i * ((w - ζ i)⁻¹ - (p_i i).eval w / (q_i i).eval w)) • f (ζ i)‖
      ≤ ‖f w - ∑ i, (c i * (w - ζ i)⁻¹) • f (ζ i)‖ +
          ‖∑ i, (c i * ((w - ζ i)⁻¹ - (p_i i).eval w / (q_i i).eval w)) • f (ζ i)‖ :=
        norm_add_le _ _
    _ ≤ ε / 2 * M + ε / 2 * M := add_le_add (hdisc f M hf hM w hw) htail
    _ = ε * M := by ring

/-- **Rational Runge approximation with prescribed poles.** Let `K ⊆ ℂ` be compact and `A ⊆ ℂ`
meet every bounded connected component of `Kᶜ`. Then every function holomorphic on an open
neighbourhood `U` of `K` can be uniformly approximated on `K` by rational functions whose finite
poles lie in `A \ K`. -/
theorem exists_rational_norm_sub_lt {K U A : Set ℂ} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hA : ∀ x ∈ filledHull K \ K, (A ∩ connectedComponentIn Kᶜ x).Nonempty)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ (∀ z, q.eval z = 0 → z ∈ A \ K) ∧
      ∀ z ∈ K, ‖f z - p.eval z / q.eval z‖ < ε := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨M₀, hM₀⟩ := hL.bddAbove_image (hf.continuousOn.mono hLU).norm
  set M : ℝ := max M₀ 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ z ∈ interior L, ‖f z‖ ≤ M := fun z hz ↦
    (hM₀ ⟨z, interior_subset hz, rfl⟩).trans (le_max_left _ _)
  obtain ⟨N, ζ, p_i, q_i, -, hq_i, hqA_i, hop⟩ := exists_rational_norm_sub_sum_smul_le hK
    isOpen_interior hKL hA (ε := ε / (2 * (M + 1))) (by positivity)
  obtain ⟨p, q, hq, hqA, hval⟩ := exists_rational_sum_smul_eq (fun i ↦ f (ζ i)) p_i q_i hq_i hqA_i
  refine ⟨p, q, hq, hqA, fun w hw ↦ ?_⟩
  have hsum : p.eval w / q.eval w = ∑ i, ((p_i i).eval w / (q_i i).eval w) • f (ζ i) := by
    rw [hval w hw]
    exact Finset.sum_congr rfl fun i _ ↦ by simp [mul_comm]
  rw [hsum]
  calc ‖f w - ∑ i, ((p_i i).eval w / (q_i i).eval w) • f (ζ i)‖
      ≤ ε / (2 * (M + 1)) * M := hop f M (hf.mono (interior_subset.trans hLU)) hM w hw
    _ < ε := by rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith

/-! ### Homogenization and Riemann-sphere rational Runge approximation -/

/-- The degree-`d` homogenization of `P` in `(X - C a₀)`, satisfying
`(homogShift a₀ d P).eval z = (z - a₀)^d * P.eval (z - a₀)⁻¹` for `z ≠ a₀` and `P.natDegree ≤ d`. -/
private noncomputable def homogShift (a₀ : ℂ) (d : ℕ) (P : ℂ[X]) : ℂ[X] :=
  ∑ k ∈ Finset.range (d + 1), C (P.coeff k) * (X - C a₀) ^ (d - k)

private theorem eval_homogShift {a₀ z : ℂ} {d : ℕ} {P : ℂ[X]} (hP : P.natDegree ≤ d)
    (hz : z ≠ a₀) : (homogShift a₀ d P).eval z = (z - a₀) ^ d * P.eval (z - a₀)⁻¹ := by
  have hu : z - a₀ ≠ 0 := sub_ne_zero.mpr hz
  rw [homogShift, ← coe_evalRingHom, map_sum,
    P.eval_eq_sum_range' (Nat.lt_succ_of_le hP), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simp only [coe_evalRingHom, eval_mul, eval_C, eval_pow, eval_sub, eval_X]
  calc P.coeff k * (z - a₀) ^ (d - k)
      = P.coeff k * ((z - a₀) ^ (d - k) * ((z - a₀) * (z - a₀)⁻¹) ^ k) := by
          rw [mul_inv_cancel₀ hu, one_pow, mul_one]
    _ = (z - a₀) ^ d * (P.coeff k * ((z - a₀)⁻¹) ^ k) := by
          rw [mul_pow, ← mul_assoc ((z - a₀) ^ (d - k)), ← pow_add, Nat.sub_add_cancel hkd]; ring

private theorem natDegree_homogShift_le (a₀ : ℂ) (d : ℕ) (P : ℂ[X]) :
    (homogShift a₀ d P).natDegree ≤ d := by
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun k _ ↦ ?_)
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  exact Nat.sub_le d k

private theorem coeff_homogShift_self (a₀ : ℂ) (d : ℕ) (P : ℂ[X]) :
    (homogShift a₀ d P).coeff d = P.eval 0 := by
  rw [homogShift, ← lcoeff_apply (R := ℂ) d, map_sum, Finset.sum_eq_single 0]
  · simp only [lcoeff_apply, Nat.sub_zero, coeff_C_mul]
    have hmon : ((X - C a₀) ^ d).Monic := (monic_X_sub_C a₀).pow d
    have hdeg : ((X - C a₀) ^ d).natDegree = d := by
      rw [natDegree_pow, natDegree_X_sub_C, mul_one]
    have hcoeff : ((X - C a₀) ^ d).coeff d = 1 :=
      (congrArg ((X - C a₀) ^ d).coeff hdeg).symm.trans hmon.coeff_natDegree
    rw [hcoeff, mul_one, coeff_zero_eq_eval_zero]
  · intro k hk hk0
    have hlt : (C (P.coeff k) * (X - C a₀) ^ (d - k)).natDegree < d := by
      refine (natDegree_C_mul_le _ _).trans_lt ?_
      rw [natDegree_pow, natDegree_X_sub_C, mul_one]
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hd1 : 1 ≤ d := hk1.trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
      omega
    exact coeff_eq_zero_of_natDegree_lt hlt
  · intro h0
    exact (h0 (Finset.mem_range.mpr (Nat.succ_pos d))).elim

/-- For an unbounded set `D ⊆ ℂ`, the image of `D \ {a₀}` under `z ↦ (z - a₀)⁻¹` accumulates at
`0`. -/
private theorem zero_mem_closure_inv_sub_image {D : Set ℂ} {a₀ : ℂ} (hD : ¬ IsBounded D) :
    (0 : ℂ) ∈ closure ((fun z ↦ (z - a₀)⁻¹) '' (D \ {a₀})) := by
  rw [Metric.mem_closure_iff]
  intro r hr
  have hnot : ¬ D ⊆ closedBall a₀ r⁻¹ := fun h ↦ hD (isBounded_closedBall.subset h)
  obtain ⟨z, hzD, hzR⟩ := not_subset.mp hnot
  rw [mem_closedBall, dist_eq_norm, not_le] at hzR
  have hza : z ≠ a₀ := fun h ↦ by
    rw [h, sub_self, norm_zero] at hzR
    exact (inv_pos.mpr hr).not_ge hzR.le
  refine ⟨(z - a₀)⁻¹, ⟨z, ⟨hzD, hza⟩, rfl⟩, ?_⟩
  rw [dist_zero_left, norm_inv]
  exact (inv_lt_comm₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hza)) hr).mpr hzR

/-- If `D` is open around `a₀`, then any set containing `(fun z ↦ (z - a₀)⁻¹) '' (D \ {a₀})` is
unbounded. -/
private theorem not_isBounded_of_inv_sub_image_subset {D S : Set ℂ} {a₀ : ℂ} (hD : IsOpen D)
    (ha₀ : a₀ ∈ D) (hsub : (fun z ↦ (z - a₀)⁻¹) '' (D \ {a₀}) ⊆ S) : ¬ IsBounded S := by
  intro hbd
  obtain ⟨R, hR⟩ := hbd.subset_closedBall 0
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hD a₀ ha₀
  set t : ℝ := min (r / 2) (max R 1 + 1)⁻¹
  have ht : 0 < t := lt_min (half_pos hr) (by positivity)
  set z : ℂ := a₀ + (t : ℂ)
  have hzD : z ∈ D := hball (by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg ht.le]
    exact (min_le_left _ _).trans_lt (half_lt_self hr))
  have hza : z ≠ a₀ := fun h ↦ ht.ne' (Complex.ofReal_eq_zero.mp (by simpa [z] using h))
  have hle := mem_closedBall.mp (hR (hsub ⟨z, ⟨hzD, hza⟩, rfl⟩))
  rw [dist_zero_right, norm_inv, show ‖z - a₀‖ = t by simp [z, Real.norm_of_nonneg ht.le]] at hle
  have hinv : max R 1 + 1 ≤ t⁻¹ := (le_inv_comm₀ (by positivity) ht).mpr (min_le_right _ _)
  linarith [le_max_left R 1]

/-- Under inversion `z ↦ (z - a₀)⁻¹` about a point `a₀` in the unbounded complementary component of
a compact set `K ⊆ ℂ`, the image of `connectedComponentIn Kᶜ a₀ \ {a₀}` lies in the unbounded
component of `(K')ᶜ`, which also contains `0`; hence `0 ∉ filledHull K'`. -/
private theorem notMem_filledHull_inv_sub_image {K : Set ℂ} {a₀ : ℂ} (hK : IsCompact K)
    (ha₀ : a₀ ∉ filledHull K) :
    let φ : ℂ → ℂ := fun z ↦ (z - a₀)⁻¹
    0 ∉ filledHull (φ '' K) ∧
      φ '' (connectedComponentIn Kᶜ a₀ \ {a₀}) ⊆ connectedComponentIn (φ '' K)ᶜ 0 := by
  intro φ
  set K' := φ '' K
  set D := connectedComponentIn Kᶜ a₀
  have ha₀K : a₀ ∉ K := fun h ↦ ha₀ (subset_filledHull h)
  have h0K' : (0 : ℂ) ∉ K' := by
    rintro ⟨z, hzK, h0⟩
    exact inv_ne_zero (sub_ne_zero.mpr fun h : z = a₀ ↦ ha₀K (h ▸ hzK)) h0
  have hD_open : IsOpen D := hK.isClosed.isOpen_compl.connectedComponentIn
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat
  have hD_sdiff_preconn : IsPreconnected (D \ {a₀}) :=
    isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank hrank hD_open
      isPreconnected_connectedComponentIn isClosed_singleton (Set.finite_singleton a₀).isDiscrete
  have hφ_cont : ContinuousOn φ (D \ {a₀}) :=
    (continuousOn_id.sub continuousOn_const).inv₀ fun z hz h ↦
      hz.2 (sub_eq_zero.mp (by simpa using h))
  have hImg_sub : φ '' (D \ {a₀}) ⊆ K'ᶜ := by
    rintro _ ⟨z, ⟨hzD, -⟩, rfl⟩ ⟨w, hwK, hzw⟩
    exact (connectedComponentIn_subset _ _ hzD) (sub_left_injective (inv_injective hzw.symm) ▸ hwK)
  have hS_sub : insert (0 : ℂ) (φ '' (D \ {a₀})) ⊆ connectedComponentIn K'ᶜ 0 :=
    ((hD_sdiff_preconn.image φ hφ_cont).subset_closure (subset_insert _ _)
      (insert_subset (zero_mem_closure_inv_sub_image (mem_filledHull_iff.not.mp ha₀))
        subset_closure)).subset_connectedComponentIn (mem_insert 0 _) (insert_subset h0K' hImg_sub)
  have hD_sub : φ '' (D \ {a₀}) ⊆ connectedComponentIn K'ᶜ 0 := (subset_insert 0 _).trans hS_sub
  exact ⟨mem_filledHull_iff.not.mpr
    (not_isBounded_of_inv_sub_image_subset hD_open (mem_connectedComponentIn ha₀K) hD_sub), hD_sub⟩

/-- If `A` meets every connected component of `Kᶜ` and `a₀ ∈ A \ filledHull K`, then under
`φ z = (z - a₀)⁻¹` the set `φ '' (A \ {a₀})` meets every bounded component of `(φ '' K)ᶜ`. -/
private theorem inv_sub_image_meets_bounded_components {K A : Set ℂ} {a₀ : ℂ} (hK : IsCompact K)
    (ha₀ : a₀ ∉ filledHull K) (hA : ∀ x ∈ Kᶜ, (A ∩ connectedComponentIn Kᶜ x).Nonempty) :
    let φ : ℂ → ℂ := fun z ↦ (z - a₀)⁻¹
    ∀ w ∈ filledHull (φ '' K) \ (φ '' K),
      (φ '' (A \ {a₀}) ∩ connectedComponentIn (φ '' K)ᶜ w).Nonempty := by
  intro φ
  set K' := φ '' K
  obtain ⟨h0_not, hD_sub⟩ := notMem_filledHull_inv_sub_image hK ha₀
  rintro w ⟨hwH, hwK'⟩
  have hw0 : w ≠ 0 := fun h ↦ h0_not (h ▸ hwH)
  set x : ℂ := a₀ + w⁻¹
  have hxa₀ : x ≠ a₀ := fun h ↦ inv_ne_zero hw0 (by simpa [x] using h)
  have hφx : φ x = w := by simp [φ, x]
  have hxK : x ∈ Kᶜ := fun hxK ↦ hwK' ⟨x, hxK, hφx⟩
  have ha₀_not_comp : a₀ ∉ connectedComponentIn Kᶜ x := by
    intro hmem
    have hxD : x ∈ connectedComponentIn Kᶜ a₀ :=
      (connectedComponentIn_eq hmem).symm ▸ mem_connectedComponentIn hxK
    have hw0c : w ∈ connectedComponentIn K'ᶜ 0 := hD_sub ⟨x, ⟨hxD, hxa₀⟩, hφx⟩
    exact h0_not (mem_filledHull_iff.mpr <|
      (connectedComponentIn_eq hw0c).symm ▸ mem_filledHull_iff.mp hwH)
  obtain ⟨b, hbA, hbc⟩ := hA x hxK
  have hba₀ : b ≠ a₀ := fun h ↦ ha₀_not_comp (h ▸ hbc)
  have hcont : ContinuousOn φ (connectedComponentIn Kᶜ x) :=
    (continuousOn_id.sub continuousOn_const).inv₀ fun z hz h ↦
      ha₀_not_comp (sub_eq_zero.mp (by simpa using h) ▸ hz)
  have himg_sub : φ '' connectedComponentIn Kᶜ x ⊆ K'ᶜ := by
    rintro _ ⟨z, hz, rfl⟩ ⟨u, huK, hzu⟩
    exact (connectedComponentIn_subset _ _ hz) (sub_left_injective (inv_injective hzu.symm) ▸ huK)
  have hcomp_sub : φ '' connectedComponentIn Kᶜ x ⊆ connectedComponentIn K'ᶜ w :=
    (isPreconnected_connectedComponentIn.image φ hcont).subset_connectedComponentIn
      ⟨x, mem_connectedComponentIn hxK, hφx⟩ himg_sub
  exact ⟨φ b, ⟨b, ⟨hbA, hba₀⟩, rfl⟩, hcomp_sub ⟨b, hbc, rfl⟩⟩

/-- Pulling back a holomorphic function `f` on `U ⊇ K` along the Möbius inversion
`ψ w = a₀ + w⁻¹` yields a holomorphic function on the open neighbourhood
`{0}ᶜ ∩ ψ ⁻¹' U` of the compact set `(fun z ↦ (z - a₀)⁻¹) '' K`. -/
private theorem inv_sub_pullback_data {K U : Set ℂ} {a₀ : ℂ} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (ha₀K : a₀ ∉ K) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    let φ : ℂ → ℂ := fun z ↦ (z - a₀)⁻¹
    let ψ : ℂ → ℂ := fun w ↦ a₀ + w⁻¹
    let U' : Set ℂ := ({0}ᶜ : Set ℂ) ∩ ψ ⁻¹' U
    IsCompact (φ '' K) ∧ IsOpen U' ∧ φ '' K ⊆ U' ∧ DifferentiableOn ℂ (f ∘ ψ) U' := by
  intro φ ψ U'
  have hφ_cont : ContinuousOn φ K :=
    (continuousOn_id.sub continuousOn_const).inv₀ fun z hz h ↦
      ha₀K (sub_eq_zero.mp (by simpa using h) ▸ hz)
  have hψ_diff : DifferentiableOn ℂ ψ {0}ᶜ :=
    (differentiableOn_const a₀).add (differentiableOn_id.inv fun _ hw ↦ hw)
  refine ⟨hK.image_of_continuousOn hφ_cont, isOpen_iff_mem_nhds.mpr fun w ⟨hw0, hwU⟩ ↦
      Filter.inter_mem (isOpen_compl_singleton.mem_nhds hw0)
        ((hψ_diff.continuousOn.continuousAt
          (isOpen_compl_singleton.mem_nhds hw0)).preimage_mem_nhds (hU.mem_nhds hwU)),
    ?_, hf.comp (hψ_diff.mono inter_subset_left) inter_subset_right⟩
  rintro _ ⟨z, hzK, rfl⟩
  exact ⟨inv_ne_zero (sub_ne_zero.mpr fun h ↦ ha₀K (h ▸ hzK)), by simpa [φ, ψ] using hKU hzK⟩

/-- **Riemann-sphere rational Runge approximation.** Let `K ⊆ ℂ` be compact and `A ⊆ ℂ` meet every
connected component of `Kᶜ`, including the unbounded component. Then every function holomorphic on
an open neighbourhood `U` of `K` can be uniformly approximated on `K` by rational functions `p / q`
with `p.natDegree ≤ q.natDegree` (hence bounded at `∞`) and all finite poles in `A \ K`. -/
theorem exists_rational_natDegree_le_norm_sub_lt {K U A : Set ℂ} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hA : ∀ x ∈ Kᶜ, (A ∩ connectedComponentIn Kᶜ x).Nonempty)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ p.natDegree ≤ q.natDegree ∧ (∀ z, q.eval z = 0 → z ∈ A \ K) ∧
      ∀ z ∈ K, ‖f z - p.eval z / q.eval z‖ < ε := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat
  obtain ⟨x₀, hx₀⟩ := nonempty_compl_filledHull hK.isBounded
  obtain ⟨a₀, ha₀A, ha₀c⟩ := hA x₀ fun hxK ↦ hx₀ (subset_filledHull hxK)
  have ha₀ : a₀ ∉ filledHull K := by
    rwa [← mem_compl_iff, compl_filledHull_eq_connectedComponentIn hrank hK.isBounded hx₀]
  have ha₀K : a₀ ∉ K := fun h ↦ ha₀ (subset_filledHull h)
  set φ : ℂ → ℂ := fun z ↦ (z - a₀)⁻¹
  set ψ : ℂ → ℂ := fun w ↦ a₀ + w⁻¹
  obtain ⟨hK', hU', hK'U', hf'⟩ := inv_sub_pullback_data hK hU hKU ha₀K hf
  obtain ⟨P, Q, -, hQA', happrox⟩ := exists_rational_norm_sub_lt hK' hU' hK'U'
    (inv_sub_image_meets_bounded_components hK ha₀ hA) hf' hε
  have hQ0 : Q.eval 0 ≠ 0 := by
    intro h0
    obtain ⟨b, ⟨-, hba⟩, hb0⟩ := (hQA' 0 h0).1
    exact inv_ne_zero (sub_ne_zero.mpr hba) hb0
  set d := max P.natDegree Q.natDegree
  refine ⟨homogShift a₀ d P, homogShift a₀ d Q, ?_, ?_, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · intro hq0
    exact hQ0 (by rw [← coeff_homogShift_self a₀ d Q, hq0, coeff_zero])
  · exact (natDegree_homogShift_le a₀ d P).trans
      (le_natDegree_of_ne_zero (by rwa [coeff_homogShift_self]))
  · by_cases hza : z = a₀
    · exact hza ▸ ⟨ha₀A, ha₀K⟩
    · rw [eval_homogShift (le_max_right _ _) hza, mul_eq_zero] at hz
      have hQz : Q.eval (φ z) = 0 := hz.resolve_left (pow_ne_zero d (sub_ne_zero.mpr hza))
      obtain ⟨⟨b, ⟨hbA, -⟩, hbz⟩, hzK'⟩ := hQA' (φ z) hQz
      exact ⟨sub_left_injective (inv_injective hbz) ▸ hbA, fun hzK ↦ hzK' ⟨z, hzK, rfl⟩⟩
  · have hza : z ≠ a₀ := fun h ↦ ha₀K (h ▸ hz)
    rw [eval_homogShift (le_max_left _ _) hza, eval_homogShift (le_max_right _ _) hza,
      mul_div_mul_left _ _ (pow_ne_zero d (sub_ne_zero.mpr hza))]
    simpa [φ, ψ] using happrox (φ z) ⟨z, hz, rfl⟩

end TauCeti

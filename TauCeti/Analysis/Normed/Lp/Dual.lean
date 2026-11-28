/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.Mul
import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Dual

/-!
# The continuous dual of `ℓᵖ`

Let `p` and `q` be Hölder conjugate exponents with `q < ∞`. Over real or complex scalars, the
pairing `∑' i, a i * x i` identifies `ℓᵖ` with the continuous dual of `ℓ^q`, isometrically. The
inverse records the values of a functional on the unit coordinate vectors. This covers both the
identification `(ℓ¹)* = ℓ∞` (for `q = 1`) and the reflexive range `(ℓ^q)* = ℓᵖ` for
`1 < q < ∞`. The index type is arbitrary, including empty and uncountable types; no enumeration
is chosen.

`lp.dualEquiv` uses Mathlib's `lp.dualPairing` for the pairing, whose norm bound is Hölder's
inequality, and the coordinate expansion `ContinuousLinearMap.hasSum_smul_lp_single` of
continuous linear maps on `ℓ^q`. The pairing is bilinear, including over complex scalars: the
coefficients of a functional are its values on coordinate vectors, without conjugation.

This identification describes the dual of the sequence spaces `ℓ^q` and makes its norm and the
action of its functionals accessible through coordinates. For `q = 1` the norm of a functional,
and more generally of any continuous linear map from ℓ¹ to a normed space, is the supremum of the
norms of its values on the unit coordinate vectors
(`ContinuousLinearMap.norm_eq_ciSup_norm_lp_single`, in `TauCeti.Analysis.Normed.Lp.Basic`).

More generally, for a family of normed spaces `E i`, the pairing `∑' i, φ i (x i)` identifies the
`ℓᵖ` sum of the duals `E i*` isometrically with the continuous dual of the `ℓ^q` sum of the `E i`
(`lp.strongDualEquiv`), again for `q < ∞`, including `(ℓ¹(ι, E))* = ℓ∞(ι, E*)`. The inverse sends
a functional `Φ` to its coordinate functionals `Φ ∘ eᵢ`, the restrictions of `Φ` along the
coordinate inclusions. For constant fibres `E i = X` this is `(ℓ^q(ι, X))* = ℓᵖ(ι, X*)`, and for
`E i = 𝕜` it agrees with `lp.dualEquiv` (`lp.strongDualEquiv_symm_apply_eq_toSpanSingleton`).
These spaces are the Bochner spaces of a counting measure, and the identification is the atomic
case of the duality of Bochner spaces.

## Main declarations

* `ContinuousLinearMap.sum_norm_lp_single_rpow_le`: for `p < ∞`, the coordinate values of a
  functional on `ℓ^q` have finite partial sums of `p`-th powers of norms bounded by the `p`-th
  power of its norm.
* `ContinuousLinearMap.memℓp_lp_single`: the coordinate values of a functional on `ℓ^q` form an
  `ℓᵖ` family.
* `ContinuousLinearMap.norm_le_opNorm_of_forall_eq_lp_single`: an `ℓᵖ` family of coordinate
  values of a functional on `ℓ^q` has norm at most the norm of the functional.
* `lp.sum_norm_rpow_le_of_forall_norm_sum_mul_le`: for `p < ∞`, finitely many coefficients
  `zᵢ` whose pairing `c ↦ ∑ cᵢ zᵢ` is bounded by `B ‖c‖_q` on `ℓ^q` have
  `∑ ‖zᵢ‖ ^ p ≤ B ^ p`.
* `lp.exists_memℓp_and_norm_le_of_forall_norm_sum_mul_le`: a real family dominated by such
  coefficients, `‖xᵢ‖ ≤ A ‖zᵢ‖`, lies in `ℓᵖ` with norm at most `A B`, also for `p = ∞`.
* `lp.dualEquiv`: the isometric equivalence `ℓᵖ ≃ₗᵢ (ℓ^q)*`.
* `ContinuousLinearMap.norm_rpow_eq_tsum_norm_lp_single_rpow`: for `1 < q < ∞`, the `p`-th
  power of the norm of a functional on `ℓ^q` is the sum of the `p`-th powers of the norms of its
  coordinate values.
* `ContinuousLinearMap.memℓp_comp_singleContinuousLinearMap`: the coordinate functionals of a
  functional on `ℓ^q(ι, E)` form an `ℓᵖ` family.
* `ContinuousLinearMap.norm_le_opNorm_of_forall_eq_comp_singleContinuousLinearMap`: that family
  has norm at most the norm of the functional.
* `lp.strongDualEquiv`: the isometric equivalence `ℓᵖ(ι, E*) ≃ₗᵢ (ℓ^q(ι, E))*`.
* `ContinuousLinearMap.norm_rpow_eq_tsum_norm_comp_singleContinuousLinearMap_rpow`: for
  `1 < q < ∞`, the `p`-th power of the norm of a functional on `ℓ^q(ι, E)` is the sum of the
  `p`-th powers of the norms of its coordinate functionals.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 1.
* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces, Volume I*,
  Springer, 2016, Proposition 1.3.3.
-/

public section

noncomputable section

open scoped ENNReal ComplexConjugate ZeroAtInfty

namespace ContinuousLinearMap

variable {𝕜 ι : Type*} [RCLike 𝕜] [DecidableEq ι] {p q : ℝ≥0∞} [Fact (1 ≤ q)]
  [p.HolderConjugate q]

/-- For `q = ∞` the coordinate values of a continuous linear functional `f` on `ℓ∞` at the unit
coordinate vectors `eᵢ` satisfy `∑ i ∈ s, ‖f eᵢ‖ ≤ ‖f‖` on every finite set `s`: restrict `f` to
`c₀(ι)`. -/
private theorem sum_norm_lp_single_top_le (f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) ∞))
    (s : Finset ι) : ∑ i ∈ s, ‖f (lp.single ∞ i 1)‖ ≤ ‖f‖ := by
  let _ : TopologicalSpace ι := ⊥
  have : DiscreteTopology ι := ⟨rfl⟩
  let J : C₀(ι, 𝕜) →L[𝕜] lp (fun _ : ι ↦ 𝕜) ∞ :=
    (ZeroAtInftyContinuousMap.toLpInfty 𝕜).toContinuousLinearMap
  have hJ (i : ι) : J (ZeroAtInftyContinuousMap.single i 1) = lp.single ∞ i 1 := by
    refine lp.ext (funext fun j ↦ ?_)
    simp only [J, LinearIsometry.coe_toContinuousLinearMap,
      ZeroAtInftyContinuousMap.toLpInfty_apply, ZeroAtInftyContinuousMap.single_apply,
      lp.single_apply, Pi.single_apply]
  have h := ZeroAtInftyContinuousMap.sum_norm_apply_single_one_le (f.comp J) s
  simp only [coe_comp, Function.comp_apply, hJ] at h
  have hJ1 : ‖J‖ ≤ 1 := LinearIsometry.norm_toContinuousLinearMap_le _
  have h2 : ‖f.comp J‖ ≤ ‖f‖ :=
    (f.opNorm_comp_le J).trans (mul_le_of_le_one_right (norm_nonneg f) hJ1)
  exact h.trans h2

/-- For Hölder conjugate exponents `p` and `q` with `p < ∞`, the values of a continuous linear
functional `f` on `ℓ^q` at the unit coordinate vectors `eᵢ` satisfy
`∑ i ∈ s, ‖f eᵢ‖ ^ p ≤ ‖f‖ ^ p` on every finite set `s`. -/
theorem sum_norm_lp_single_rpow_le (hp : p ≠ ∞) (f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) q))
    (s : Finset ι) :
    ∑ i ∈ s, ‖f (lp.single q i 1)‖ ^ p.toReal ≤ ‖f‖ ^ p.toReal := by
  rcases eq_or_ne q ∞ with rfl | hq
  · obtain rfl : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ p).mp rfl
    simpa using sum_norm_lp_single_top_le f s
  have h := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  have hp₀ : 0 < p.toReal := h.pos
  have hq₁ : 1 < q.toReal := h.symm.lt
  -- The real-power identities behind the extremal vector, for `t > 0`.
  have hsq {t : ℝ} (ht : 0 < t) : t ^ 2 * t ^ (p.toReal - 2) = t ^ p.toReal := by
    rw [← Real.rpow_two, ← Real.rpow_add ht, add_sub_cancel]
  have hpow {t : ℝ} (ht : 0 < t) : (t * t ^ (p.toReal - 2)) ^ q.toReal = t ^ p.toReal := by
    rw [← Real.rpow_one_add' ht.le (by linarith [h.lt]), ← Real.rpow_mul ht.le]
    convert congrArg (t ^ ·) h.sub_one_mul_conj using 2
    ring
  set c : ι → 𝕜 := fun i ↦ f (lp.single q i 1)
  -- Test `f` against the extremal vector with coordinates `conj (c i) * ‖c i‖ ^ (p - 2)` on `s`.
  set x : ι → 𝕜 := fun i ↦ conj (c i) * ((‖c i‖ ^ (p.toReal - 2) : ℝ) : 𝕜)
  have hcx (i : ι) : c i * x i = ((‖c i‖ ^ p.toReal : ℝ) : 𝕜) := by
    rcases eq_or_ne (c i) 0 with hc | hc
    · simp [x, hc, Real.zero_rpow hp₀.ne']
    · rw [← mul_assoc, RCLike.mul_conj]
      exact_mod_cast hsq (norm_pos_iff.2 hc)
  have hx (i : ι) : ‖x i‖ ^ q.toReal = ‖c i‖ ^ p.toReal := by
    rcases eq_or_ne (c i) 0 with hc | hc
    · simp [x, hc, Real.zero_rpow hp₀.ne', Real.zero_rpow (zero_lt_one.trans hq₁).ne']
    · have hc' := norm_pos_iff.2 hc
      simpa [x, abs_of_nonneg (Real.rpow_nonneg hc'.le _)] using hpow hc'
  set v : lp (fun _ : ι ↦ 𝕜) q := ∑ i ∈ s, lp.single q i (x i)
  set S := ∑ i ∈ s, ‖c i‖ ^ p.toReal
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ by positivity
  have hv : ‖v‖ ^ q.toReal = S := by
    rw [lp.norm_sum_single (zero_lt_one.trans hq₁)]
    exact Finset.sum_congr rfl fun i _ ↦ hx i
  have hfx (i : ι) : f (lp.single q i (x i)) = c i * x i := by
    rw [f.apply_lp_single, smul_eq_mul, mul_comm]
  have hfv : f v = (S : 𝕜) := by
    simp [v, S, map_sum, hfx, hcx]
  have hSv : ‖v‖ ^ q.toReal ≤ ‖f‖ * ‖v‖ := by
    rw [hv]
    simpa [hfv, abs_of_nonneg hS] using f.le_opNorm v
  -- From `‖v‖ ^ q ≤ ‖f‖ ‖v‖` deduce `‖v‖ ^ (q - 1) ≤ ‖f‖`, then raise to the power `p`.
  rcases (norm_nonneg v).eq_or_lt with hv₀ | hv₀
  · rw [← hv, ← hv₀, Real.zero_rpow (zero_lt_one.trans hq₁).ne']
    positivity
  have hle : ‖v‖ ^ (q.toReal - 1) ≤ ‖f‖ := by
    rw [Real.rpow_sub_one hv₀.ne', div_le_iff₀ hv₀]
    exact hSv
  calc S = (‖v‖ ^ (q.toReal - 1)) ^ p.toReal := by
        rw [← Real.rpow_mul hv₀.le, h.symm.sub_one_mul_conj, hv]
    _ ≤ ‖f‖ ^ p.toReal := Real.rpow_le_rpow (by positivity) hle hp₀.le

/-- For Hölder conjugate exponents `p` and `q`, the coordinate values `f eᵢ` of a continuous linear
functional `f` on `ℓ^q` form an `ℓᵖ` family. -/
theorem memℓp_lp_single (f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) q)) :
    Memℓp (fun i ↦ f (lp.single q i 1)) p := by
  rcases eq_or_ne p ∞ with rfl | hp
  · exact memℓp_infty f.bddAbove_range_norm_apply_lp_single
  · exact memℓp_gen' (f.sum_norm_lp_single_rpow_le hp)

/-- For Hölder conjugate exponents `p` and `q`, an `ℓᵖ` family `a` whose entries are the coordinate
values `f eᵢ` of a continuous linear functional `f` on `ℓ^q` has norm at most `‖f‖`. -/
theorem norm_le_opNorm_of_forall_eq_lp_single (f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) q))
    (a : lp (fun _ : ι ↦ 𝕜) p) (ha : ∀ i, a i = f (lp.single q i 1)) : ‖a‖ ≤ ‖f‖ := by
  rcases eq_or_ne p ∞ with rfl | hp
  · exact lp.norm_le_of_forall_le (norm_nonneg f) fun i ↦ ha i ▸ f.norm_apply_lp_single_le i
  · have hp₀ : 0 < p.toReal := ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero p q) hp
    refine lp.norm_le_of_forall_sum_le hp₀ (norm_nonneg f) fun s ↦ ?_
    simpa only [ha] using f.sum_norm_lp_single_rpow_le hp s

end ContinuousLinearMap

namespace lp

variable {𝕜 ι : Type*} [RCLike 𝕜] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [p.HolderConjugate q]

omit [Fact (1 ≤ p)] in
/-- **Finite sums of coefficients bounded by duality.** For Hölder conjugate exponents `p` and
`q` with `p < ∞`, if the pairing `c ↦ ∑ i ∈ s, cᵢ zᵢ` with finitely many coefficients `zᵢ`
satisfies `‖∑ i ∈ s, cᵢ zᵢ‖ ≤ B ‖c‖_q` for every `c ∈ ℓ^q`, then `∑ i ∈ s, ‖zᵢ‖ ^ p ≤ B ^ p`. -/
theorem sum_norm_rpow_le_of_forall_norm_sum_mul_le (hp : p ≠ ∞) (s : Finset ι)
    (z : ι → 𝕜) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ c : lp (fun _ : ι ↦ 𝕜) q, ‖∑ i ∈ s, c i * z i‖ ≤ B * ‖c‖) :
    ∑ i ∈ s, ‖z i‖ ^ p.toReal ≤ B ^ p.toReal := by
  classical
  -- The pairing is a continuous linear functional on `ℓ^q` of norm at most `B`.
  let f : lp (fun _ : ι ↦ 𝕜) q →ₗ[𝕜] 𝕜 :=
    { toFun c := ∑ i ∈ s, c i * z i
      map_add' c d := by simp only [coeFn_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' a c := by
        simp only [coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum,
          mul_assoc] }
  have hf (i : ι) (hi : i ∈ s) : f.mkContinuous B h (lp.single q i 1) = z i := by
    simp [f, lp.single_apply, Pi.single_apply, hi]
  calc ∑ i ∈ s, ‖z i‖ ^ p.toReal
      = ∑ i ∈ s, ‖f.mkContinuous B h (lp.single q i 1)‖ ^ p.toReal :=
        Finset.sum_congr rfl fun i hi ↦ by rw [hf i hi]
    _ ≤ ‖f.mkContinuous B h‖ ^ p.toReal := (f.mkContinuous B h).sum_norm_lp_single_rpow_le hp s
    _ ≤ B ^ p.toReal := by
        gcongr
        exact LinearMap.mkContinuous_norm_le _ hB _

omit [Fact (1 ≤ p)] in
/-- **Coordinates controlled by a bounded pairing.** For Hölder conjugate exponents `p` and `q`,
let `zᵢ` be coefficients whose finite pairings `c ↦ ∑ i ∈ s, cᵢ zᵢ` are bounded by `B ‖c‖_q` on
`ℓ^q`. Then every real family `x` with `‖xᵢ‖ ≤ A ‖zᵢ‖` lies in `ℓᵖ`, with norm at most `A B`. -/
theorem exists_memℓp_and_norm_le_of_forall_norm_sum_mul_le {x : ι → ℝ} (z : ι → 𝕜) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hxz : ∀ i, ‖x i‖ ≤ A * ‖z i‖)
    (h : ∀ (s : Finset ι) (c : lp (fun _ : ι ↦ 𝕜) q), ‖∑ i ∈ s, c i * z i‖ ≤ B * ‖c‖) :
    ∃ hx : Memℓp x p, ‖(⟨x, hx⟩ : lp (fun _ : ι ↦ ℝ) p)‖ ≤ A * B := by
  classical
  -- Each coefficient is bounded by `B`: pair with a unit coordinate vector.
  have hz (i : ι) : ‖z i‖ ≤ B := by
    simpa [lp.single_apply, lp.norm_single (zero_lt_one.trans_le Fact.out)] using
      h {i} (lp.single q i 1)
  have hle (i : ι) : ‖x i‖ ≤ A * B := (hxz i).trans (by gcongr; exact hz i)
  rcases eq_or_ne p ∞ with rfl | hp
  · exact ⟨memℓp_infty ⟨A * B, by rintro _ ⟨i, rfl⟩; exact hle i⟩,
      lp.norm_le_of_forall_le (by positivity) hle⟩
  · have hp0 : 0 < p.toReal := ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero p q) hp
    have hsum (s : Finset ι) : ∑ i ∈ s, ‖x i‖ ^ p.toReal ≤ (A * B) ^ p.toReal := by
      calc ∑ i ∈ s, ‖x i‖ ^ p.toReal ≤ ∑ i ∈ s, (A * ‖z i‖) ^ p.toReal :=
            Finset.sum_le_sum fun i _ ↦ Real.rpow_le_rpow (norm_nonneg _) (hxz i) hp0.le
        _ = A ^ p.toReal * ∑ i ∈ s, ‖z i‖ ^ p.toReal := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ ↦ Real.mul_rpow hA (norm_nonneg _)
        _ ≤ A ^ p.toReal * B ^ p.toReal := by
            gcongr
            exact sum_norm_rpow_le_of_forall_norm_sum_mul_le hp s z hB (h s)
        _ = (A * B) ^ p.toReal := (Real.mul_rpow hA hB).symm
    exact ⟨memℓp_gen' hsum, lp.norm_le_of_forall_sum_le hp0 (by positivity) hsum⟩

variable (𝕜 ι p q)

/-- The isometric duality between `ℓᵖ` and the continuous dual of `ℓ^q`, for Hölder conjugate
exponents `p` and `q` with `q < ∞`. It sends `a` to the functional `x ↦ ∑' i, a i * x i`. -/
def dualEquiv (hq : q ≠ ∞) :
    lp (fun _ : ι ↦ 𝕜) p ≃ₗᵢ[𝕜] StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) q) := by
  classical
  have hmul : ‖ContinuousLinearMap.mul 𝕜 𝕜‖ ≤ ((1 : NNReal) : ℝ) := by
    simpa only [NNReal.coe_one] using ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜
  let P : lp (fun _ : ι ↦ 𝕜) p →L[𝕜] StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) q) :=
    dualPairing (𝕜 := 𝕜) p q (fun _ : ι ↦ ContinuousLinearMap.mul 𝕜 𝕜) (fun _ ↦ hmul)
  have hP (a : lp (fun _ : ι ↦ 𝕜) p) (i : ι) : P a (lp.single q i 1) = a i := by
    simp only [P, dualPairing_apply, ContinuousLinearMap.mul_apply', lp.single_apply,
      Pi.single_apply, mul_ite, mul_one, mul_zero, tsum_ite_eq]
  have hnorm (a : lp (fun _ : ι ↦ 𝕜) p) : ‖P a‖ = ‖a‖ := by
    refine le_antisymm ((P.le_opNorm a).trans ?_)
      ((P a).norm_le_opNorm_of_forall_eq_lp_single a fun i ↦ (hP a i).symm)
    simpa using mul_le_mul_of_nonneg_right
      (norm_dualPairing (p := p) (q := q) (fun _ : ι ↦ ContinuousLinearMap.mul 𝕜 𝕜)
        (fun _ ↦ hmul)) (norm_nonneg a)
  refine LinearIsometryEquiv.ofSurjective { P.toLinearMap with norm_map' := hnorm } fun f ↦ ?_
  refine ⟨⟨fun i ↦ f (lp.single q i 1), f.memℓp_lp_single⟩, ContinuousLinearMap.ext fun x ↦ ?_⟩
  simp only [LinearIsometry.coe_mk, ContinuousLinearMap.coe_coe, P, dualPairing_apply,
    ContinuousLinearMap.mul_apply']
  simpa only [smul_eq_mul, mul_comm] using (f.hasSum_smul_lp_single hq x).tsum_eq

variable {𝕜 ι p q}

/-- The forward duality map is the scalar series pairing. -/
theorem dualEquiv_apply (hq : q ≠ ∞) (a : lp (fun _ : ι ↦ 𝕜) p) (x : lp (fun _ : ι ↦ 𝕜) q) :
    dualEquiv 𝕜 ι p q hq a x = ∑' i, a i * x i := by
  rfl

variable [DecidableEq ι]

/-- On a coordinate vector, the functional of an `ℓᵖ` family is multiplication by that
coordinate. -/
@[simp]
theorem dualEquiv_apply_single (hq : q ≠ ∞) (a : lp (fun _ : ι ↦ 𝕜) p) (i : ι) (z : 𝕜) :
    dualEquiv 𝕜 ι p q hq a (lp.single q i z) = a i * z := by
  simp [dualEquiv_apply, lp.single_apply, Pi.single_apply]

/-- The inverse duality map records a functional's values on the unit coordinate vectors. -/
@[simp]
theorem dualEquiv_symm_apply (hq : q ≠ ∞) (f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) q))
    (i : ι) : (dualEquiv 𝕜 ι p q hq).symm f i = f (lp.single q i 1) := by
  have h := congrArg (fun g : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) q) ↦
    g (lp.single q i 1)) ((dualEquiv 𝕜 ι p q hq).apply_symm_apply f)
  rwa [dualEquiv_apply_single, mul_one] at h

end lp

namespace ContinuousLinearMap

variable {𝕜 ι : Type*} [RCLike 𝕜] [DecidableEq ι] {p q : ℝ≥0∞} [Fact (1 ≤ q)]
  [p.HolderConjugate q]

/-- For Hölder conjugate exponents `1 < p, q < ∞`, the `p`-th power of the norm of a functional
on `ℓ^q` is the sum of the `p`-th powers of the norms of its coordinate values. -/
theorem norm_rpow_eq_tsum_norm_lp_single_rpow (hp : p ≠ ∞) (hq : q ≠ ∞)
    (f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) q)) :
    ‖f‖ ^ p.toReal = ∑' i, ‖f (lp.single q i 1)‖ ^ p.toReal := by
  have : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  rw [← (lp.dualEquiv 𝕜 ι p q hq).symm.norm_map f,
    lp.norm_rpow_eq_tsum (ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero p q) hp)]
  simp only [lp.dualEquiv_symm_apply]

end ContinuousLinearMap

/-! ### The dual of an `ℓᵖ` sum of normed spaces -/

namespace ContinuousLinearMap

variable {𝕜 ι : Type*} {E : ι → Type*} [RCLike 𝕜] [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace 𝕜 (E i)] [DecidableEq ι] {p q : ℝ≥0∞} [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- Testing a functional `Φ` on `ℓ^q(ι, E)` against the vectors `cᵢ vᵢ`, with `vᵢ` in the closed
unit balls, gives a scalar pairing `c ↦ ∑ i ∈ s, cᵢ Φ(eᵢ vᵢ)` of norm at most `‖Φ‖` on `ℓ^q`. -/
private theorem norm_sum_mul_apply_lp_single_le (Φ : StrongDual 𝕜 (lp E q)) (s : Finset ι)
    {v : ∀ i, E i} (hv : ∀ i, ‖v i‖ ≤ 1) (c : lp (fun _ : ι ↦ 𝕜) q) :
    ‖∑ i ∈ s, c i * Φ (lp.single q i (v i))‖ ≤ ‖Φ‖ * ‖c‖ := by
  have hΦ : ∑ i ∈ s, c i * Φ (lp.single q i (v i)) = Φ (∑ i ∈ s, lp.single q i (c i • v i)) := by
    simp [map_sum, lp.single_smul]
  -- Compare the coordinate norms of the two sequences inside the real sequence space `ℓ^q`.
  have hle : ‖∑ i ∈ s, lp.single q i (c i • v i)‖ ≤ ‖c‖ := by
    rw [← lp.norm_normSeq, ← lp.norm_normSeq c]
    refine lp.norm_le_norm_of_exponent_le (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' le_rfl
      fun j ↦ ?_
    have hcoord : (∑ i ∈ s, lp.single q i (c i • v i)) j = if j ∈ s then c j • v j else 0 := by
      simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single]
      exact Finset.sum_pi_single j (fun i ↦ c i • v i) s
    rw [lp.normSeq_apply, lp.normSeq_apply, norm_norm, norm_norm, hcoord]
    split_ifs
    · exact (norm_smul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hv j))
    · simp
  rw [hΦ]
  exact Φ.le_opNorm_of_le hle

/-- For every `s > 1`, the norms of the coordinate functionals `Φ ∘ eᵢ` of a functional `Φ` on
`ℓ^q(ι, E)` form an `ℓᵖ` family of norm at most `s ‖Φ‖`. -/
private theorem exists_memℓp_norm_comp_singleContinuousLinearMap_le
    (Φ : StrongDual 𝕜 (lp E q)) {s : ℝ} (hs : 1 < s) :
    ∃ h : Memℓp (fun i ↦ ‖Φ.comp (lp.singleContinuousLinearMap 𝕜 E q i)‖) p,
      ‖(⟨_, h⟩ : lp (fun _ : ι ↦ ℝ) p)‖ ≤ s * ‖Φ‖ := by
  set φ := fun i ↦ Φ.comp (lp.singleContinuousLinearMap 𝕜 E q i)
  -- Choose unit-ball vectors `v i` on which `φ i` attains its norm up to the factor `s`.
  have hex (i : ι) : ∃ v : E i, ‖v‖ ≤ 1 ∧ ‖φ i‖ ≤ s * ‖φ i v‖ := by
    rcases (norm_nonneg (φ i)).eq_or_lt with h | h
    · exact ⟨0, by simp, by simp [← h]⟩
    obtain ⟨v, hv, hφv⟩ := (φ i).exists_lt_apply_of_lt_opNorm
      (div_lt_self h hs)
    exact ⟨v, hv.le, (div_lt_iff₀' (zero_lt_one.trans hs)).1 hφv |>.le⟩
  choose v hv hφv using hex
  exact lp.exists_memℓp_and_norm_le_of_forall_norm_sum_mul_le (q := q)
    (fun i ↦ Φ (lp.single q i (v i))) (zero_lt_one.trans hs).le (norm_nonneg Φ)
    (fun i ↦ by simpa [φ] using hφv i) fun t c ↦ Φ.norm_sum_mul_apply_lp_single_le t hv c

/-- For Hölder conjugate exponents `p` and `q`, the coordinate functionals `Φ ∘ eᵢ` of a
continuous linear functional `Φ` on `ℓ^q(ι, E)` form an `ℓᵖ` family. -/
theorem memℓp_comp_singleContinuousLinearMap (Φ : StrongDual 𝕜 (lp E q)) :
    Memℓp (fun i ↦ Φ.comp (lp.singleContinuousLinearMap 𝕜 E q i)) p :=
  memℓp_norm_iff.1 (Φ.exists_memℓp_norm_comp_singleContinuousLinearMap_le one_lt_two).1

/-- For Hölder conjugate exponents `p` and `q`, an `ℓᵖ` family `φ` whose entries are the
coordinate functionals `Φ ∘ eᵢ` of a continuous linear functional `Φ` on `ℓ^q(ι, E)` has norm at
most `‖Φ‖`. -/
theorem norm_le_opNorm_of_forall_eq_comp_singleContinuousLinearMap
    (Φ : StrongDual 𝕜 (lp E q)) (φ : lp (fun i ↦ StrongDual 𝕜 (E i)) p)
    (hφ : ∀ i, φ i = Φ.comp (lp.singleContinuousLinearMap 𝕜 E q i)) : ‖φ‖ ≤ ‖Φ‖ := by
  have hle (s : ℝ) (hs : 1 < s) : ‖φ‖ ≤ s * ‖Φ‖ := by
    obtain ⟨h, hnorm⟩ := Φ.exists_memℓp_norm_comp_singleContinuousLinearMap_le (p := p) hs
    exact (lp.norm_eq_of_forall_norm_eq fun i ↦ by simp [hφ i]).trans_le hnorm
  have hlim : Filter.Tendsto (fun s : ℝ ↦ s * ‖Φ‖) (nhdsWithin 1 (Set.Ioi 1)) (nhds ‖Φ‖) :=
    ((continuous_id.mul continuous_const : Continuous fun s : ℝ ↦ s * ‖Φ‖).tendsto' 1 ‖Φ‖
      (one_mul _)).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall hle)

end ContinuousLinearMap

namespace lp

variable {𝕜 ι : Type*} {E : ι → Type*} [RCLike 𝕜] [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace 𝕜 (E i)] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q] in
/-- Pairing a family of functionals with a vector supported in one coordinate. -/
private theorem tsum_apply_pi_single [DecidableEq ι] (φ : ∀ j, StrongDual 𝕜 (E j)) (i : ι)
    (x : E i) : ∑' j, φ j (Pi.single i x j) = φ i x := by
  rw [tsum_eq_single i fun j hj ↦ by simp [Pi.single_eq_of_ne hj], Pi.single_eq_same]

variable (𝕜 E p q) in
/-- **The dual of an `ℓᵖ` sum of normed spaces.** For Hölder conjugate exponents `p` and `q` with
`q < ∞`, the pairing `(φ, x) ↦ ∑' i, φ i (x i)` identifies the `ℓᵖ` sum of the duals `E i*`
isometrically with the continuous dual of the `ℓ^q` sum of the `E i`. -/
def strongDualEquiv (hq : q ≠ ∞) :
    lp (fun i ↦ StrongDual 𝕜 (E i)) p ≃ₗᵢ[𝕜] StrongDual 𝕜 (lp E q) := by
  classical
  have hid (i : ι) :
      ‖ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 (E i))‖ ≤ ((1 : NNReal) : ℝ) := by
    simpa only [NNReal.coe_one] using ContinuousLinearMap.norm_id_le
  let P : lp (fun i ↦ StrongDual 𝕜 (E i)) p →L[𝕜] StrongDual 𝕜 (lp E q) :=
    dualPairing (𝕜 := 𝕜) p q (fun i ↦ ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 (E i))) hid
  have hP (φ : lp (fun i ↦ StrongDual 𝕜 (E i)) p) (i : ι) :
      (P φ).comp (singleContinuousLinearMap 𝕜 E q i) = φ i := by
    ext x
    simpa [P, dualPairing_apply, lp.coeFn_single] using tsum_apply_pi_single (⇑φ) i x
  have hnorm (φ : lp (fun i ↦ StrongDual 𝕜 (E i)) p) : ‖P φ‖ = ‖φ‖ := by
    refine le_antisymm ((P.le_opNorm φ).trans ?_)
      ((P φ).norm_le_opNorm_of_forall_eq_comp_singleContinuousLinearMap φ fun i ↦ (hP φ i).symm)
    simpa using mul_le_mul_of_nonneg_right (norm_dualPairing (p := p) (q := q) _ hid)
      (norm_nonneg φ)
  refine LinearIsometryEquiv.ofSurjective { P.toLinearMap with norm_map' := hnorm } fun Φ ↦ ?_
  refine ⟨⟨fun i ↦ Φ.comp (singleContinuousLinearMap 𝕜 E q i),
    Φ.memℓp_comp_singleContinuousLinearMap⟩, ext_continuousLinearMap hq fun i ↦ ?_⟩
  exact hP _ i

/-- The forward duality map is the series pairing `∑' i, φ i (x i)`. -/
theorem strongDualEquiv_apply (hq : q ≠ ∞) (φ : lp (fun i ↦ StrongDual 𝕜 (E i)) p)
    (x : lp E q) : strongDualEquiv 𝕜 E p q hq φ x = ∑' i, φ i (x i) :=
  (rfl)

variable [DecidableEq ι]

/-- On a vector supported in one coordinate, the functional of a family `φ` applies `φ i`. -/
@[simp]
theorem strongDualEquiv_apply_single (hq : q ≠ ∞) (φ : lp (fun i ↦ StrongDual 𝕜 (E i)) p)
    (i : ι) (x : E i) : strongDualEquiv 𝕜 E p q hq φ (lp.single q i x) = φ i x := by
  simpa [strongDualEquiv_apply, lp.coeFn_single] using tsum_apply_pi_single (⇑φ) i x

/-- The inverse duality map records the coordinate functionals `Φ ∘ eᵢ`. -/
@[simp]
theorem strongDualEquiv_symm_apply (hq : q ≠ ∞) (Φ : StrongDual 𝕜 (lp E q)) (i : ι) :
    (strongDualEquiv 𝕜 E p q hq).symm Φ i = Φ.comp (singleContinuousLinearMap 𝕜 E q i) := by
  ext x
  have h := congrArg (fun g : StrongDual 𝕜 (lp E q) ↦ g (lp.single q i x))
    ((strongDualEquiv 𝕜 E p q hq).apply_symm_apply Φ)
  simpa only [ContinuousLinearMap.comp_apply, singleContinuousLinearMap_apply,
    strongDualEquiv_apply_single] using h

/-- A family supported in the coordinate `i`, with entry `g`, corresponds to the functional
`g ∘ evalᵢ`. -/
@[simp]
theorem strongDualEquiv_lp_single (hq : q ≠ ∞) (i : ι) (g : StrongDual 𝕜 (E i)) :
    strongDualEquiv 𝕜 E p q hq (lp.single p i g) = g.comp (evalCLM 𝕜 E q i) := by
  refine ext_continuousLinearMap hq fun j ↦ ContinuousLinearMap.ext fun x ↦ ?_
  by_cases hij : j = i
  · subst hij
    simp [evalCLM_apply]
  · simp [evalCLM_apply, Ne.symm hij]

/-- Composing a functional `g` on `E i` with the coordinate evaluation at `i` corresponds to the
family supported in the coordinate `i`, with entry `g`. -/
@[simp]
theorem strongDualEquiv_symm_comp_evalCLM (hq : q ≠ ∞) (i : ι) (g : StrongDual 𝕜 (E i)) :
    (strongDualEquiv 𝕜 E p q hq).symm (g.comp (evalCLM 𝕜 E q i)) = lp.single p i g :=
  (strongDualEquiv 𝕜 E p q hq).symm_apply_eq.2 (strongDualEquiv_lp_single hq i g).symm

omit [DecidableEq ι] in
/-- For the scalar fibres `E i = 𝕜`, the coordinate functionals of `Φ` are the multiplications by
its scalar coordinates under `lp.dualEquiv`. -/
theorem strongDualEquiv_symm_apply_eq_toSpanSingleton (hq : q ≠ ∞)
    (Φ : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) q)) (i : ι) :
    (strongDualEquiv 𝕜 (fun _ : ι ↦ 𝕜) p q hq).symm Φ i =
      ContinuousLinearMap.toSpanSingleton 𝕜 ((dualEquiv 𝕜 ι p q hq).symm Φ i) := by
  classical
  ext
  simp

end lp

namespace ContinuousLinearMap

variable {𝕜 ι : Type*} {E : ι → Type*} [RCLike 𝕜] [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace 𝕜 (E i)] [DecidableEq ι] {p q : ℝ≥0∞} [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- For Hölder conjugate exponents `1 < p, q < ∞`, the `p`-th power of the norm of a functional
`Φ` on `ℓ^q(ι, E)` is the sum of the `p`-th powers of the norms of its coordinate functionals. -/
theorem norm_rpow_eq_tsum_norm_comp_singleContinuousLinearMap_rpow (hp : p ≠ ∞) (hq : q ≠ ∞)
    (Φ : StrongDual 𝕜 (lp E q)) :
    ‖Φ‖ ^ p.toReal = ∑' i, ‖Φ.comp (lp.singleContinuousLinearMap 𝕜 E q i)‖ ^ p.toReal := by
  have : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  rw [← (lp.strongDualEquiv 𝕜 E p q hq).symm.norm_map Φ,
    lp.norm_rpow_eq_tsum (ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero p q) hp)]
  simp only [lp.strongDualEquiv_symm_apply]

end ContinuousLinearMap

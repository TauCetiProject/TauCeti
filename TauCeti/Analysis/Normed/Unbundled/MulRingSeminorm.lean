/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Topology.Algebra.UniformRing
public import TauCeti.Analysis.Normed.Unbundled.SmoothingSeminorm

import Mathlib.Analysis.Normed.Unbundled.SeminormFromConst
import Mathlib.Order.Zorn

/-!
# Pulling back, completing, and bounding multiplicative ring seminorms

The composite `p ∘ f` of a multiplicative seminorm `p` on `S` with a ring homomorphism
`f : R →+* S` is a multiplicative seminorm on `R`, `MulRingSeminorm.comp p f`. This is the
multiplicative analogue of Mathlib's `AddGroupSeminorm.comp`, and it is how a ring homomorphism
acts contravariantly on spaces of multiplicative seminorms such as Berkovich spectra.

A uniformly continuous multiplicative seminorm on a uniform ring extends by continuity to a
multiplicative seminorm on the completion, `MulRingSeminorm.completion`, since the seminorm laws
are closed conditions and the ring is dense in its completion.

Every nonzero power-multiplicative ring seminorm `ρ` on a commutative ring `R` is the pointwise
maximum of the multiplicative ring seminorms `α : MulRingSeminorm R` bounded above by `ρ`
([BGR, §1.3.2, Theorem 3]). Given `x₀ : R` with `ρ x₀ ≠ 0`, `seminormFromConst`
([BGR, Proposition 1.3.2/2]) produces a power-multiplicative seminorm `μ₁ ≤ ρ` agreeing with `ρ`
at `x₀` for which `x₀` is multiplicative. Zorn's lemma applied to descending chains of
power-multiplicative seminorms below `μ₁` that keep `x₀` multiplicative and preserve its value
yields a minimal element; applying `seminormFromConst` again at each element of nonzero seminorm
shows that a minimal element is multiplicative on all of `R`.

Combining this representation with `RingSeminorm.smoothing` expresses `smoothingFun μ x`, for any
ring seminorm `μ` on a commutative ring `R`, as the supremum of `α x` over all multiplicative ring
seminorms `α ≤ μ`, attained whenever `μ ≠ 0`. This is the unbundled core of Berkovich's spectral
formula on the Berkovich spectrum of a normed commutative ring.

## References

* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §1.3.2, Proposition 2 and
  Theorem 3.
* V. G. Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*,
  Mathematical Surveys and Monographs 33, AMS, 1990, Theorem 1.3.1.
-/

public section

open UniformSpace

namespace MulRingSeminorm

section comp

variable {R S T : Type*} [NonAssocRing R] [NonAssocRing S] [NonAssocRing T]

/-- The composite of a multiplicative seminorm on `S` with a ring homomorphism `R →+* S`. -/
def comp (p : MulRingSeminorm S) (f : R →+* S) : MulRingSeminorm R where
  __ := p.toAddGroupSeminorm.comp f.toAddMonoidHom
  map_one' := by simp
  map_mul' x y := by simp

@[simp]
theorem comp_apply (p : MulRingSeminorm S) (f : R →+* S) (x : R) : p.comp f x = p (f x) :=
  (rfl)

@[simp]
theorem comp_id (p : MulRingSeminorm S) : p.comp (RingHom.id S) = p :=
  ext fun _ => rfl

theorem comp_comp (p : MulRingSeminorm T) (g : S →+* T) (f : R →+* S) :
    p.comp (g.comp f) = (p.comp g).comp f :=
  ext fun _ => rfl

end comp

section completion

variable {R : Type*} [Ring R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]

/-- The extension by continuity of a uniformly continuous multiplicative seminorm on a uniform
ring to its completion. -/
noncomputable def completion (p : MulRingSeminorm R) (hp : UniformContinuous p) :
    MulRingSeminorm (Completion R) where
  toFun := Completion.extension p
  map_zero' := by rw [← Completion.coe_zero, Completion.extension_coe hp, map_zero]
  add_le' a b := by
    induction a, b using Completion.induction_on₂ with
    | hp =>
      exact isClosed_le (by fun_prop) (by fun_prop)
    | ih a b =>
      simpa only [← Completion.coe_add, Completion.extension_coe hp] using map_add_le_add p a b
  neg' a := by
    induction a using Completion.induction_on with
    | hp =>
      exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih a => simp only [← Completion.coe_neg, Completion.extension_coe hp, map_neg_eq_map]
  map_one' := by rw [← Completion.coe_one, Completion.extension_coe hp, map_one]
  map_mul' a b := by
    induction a, b using Completion.induction_on₂ with
    | hp =>
      exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih a b => simp only [← Completion.coe_mul, Completion.extension_coe hp, map_mul]

theorem coe_completion (p : MulRingSeminorm R) (hp : UniformContinuous p) :
    ⇑(p.completion hp) = Completion.extension p :=
  (rfl)

@[simp]
theorem completion_coe (p : MulRingSeminorm R) (hp : UniformContinuous p) (a : R) :
    p.completion hp a = p a := by
  rw [coe_completion, Completion.extension_coe hp]

theorem continuous_completion (p : MulRingSeminorm R) (hp : UniformContinuous p) :
    Continuous (p.completion hp) := by
  rw [coe_completion]
  exact Completion.continuous_extension

end completion

section NonAssocRing

variable {R : Type*} [NonAssocRing R]

/-- View a multiplicative ring seminorm as a `RingSeminorm`. -/
def toRingSeminorm (α : MulRingSeminorm R) : RingSeminorm R where
  __ := α.toAddGroupSeminorm
  mul_le' a b := (map_mul α a b).le

/-- Adding an element of seminorm zero leaves a multiplicative ring seminorm unchanged. -/
theorem map_add_eq_left_of_map_eq_zero (α : MulRingSeminorm R) (x : R) {y : R} (hy : α y = 0) :
    α (x + y) = α x :=
  sub_eq_zero.1 <| abs_nonpos_iff.1 <|
    (abs_sub_map_le_sub α (x + y) x).trans_eq (by rw [add_sub_cancel_left, hy])

end NonAssocRing

section Ring

variable {R : Type*} [Ring R]

@[simp]
theorem coe_toRingSeminorm (α : MulRingSeminorm R) : ⇑α.toRingSeminorm = ⇑α :=
  (rfl)

/-- Every multiplicative ring seminorm vanishes on nilpotent elements. -/
theorem eq_zero_of_isNilpotent (α : MulRingSeminorm R) {x : R} (hx : IsNilpotent x) : α x = 0 := by
  obtain ⟨n, hn⟩ := hx
  exact eq_zero_of_pow_eq_zero (by rw [← map_pow, hn, map_zero])

end Ring

section CommRing

variable {R : Type*} [CommRing R]

/-- Over a commutative ring, if `α : MulRingSeminorm R` satisfies `α x ≤ C * μ x` for every `x`,
then `α x ≤ smoothingFun μ x` for every `x`. -/
theorem le_smoothingFun_of_le_mul (α : MulRingSeminorm R) {μ : RingSeminorm R} {C : ℝ}
    (h : ∀ x, α x ≤ C * μ x) (x : R) : α x ≤ smoothingFun μ x :=
  (smoothingFun_of_powMul α.toRingSeminorm (map_one α).le fun n _ ↦ map_pow α x n).symm.trans_le
    ((RingHom.id R).smoothingFun_map_le_of_le_mul (ν := α.toRingSeminorm) h x)

end CommRing

end MulRingSeminorm

/-- The pointwise infimum of a nonempty family of nonnegative power-multiplicative functions is
power-multiplicative. -/
theorem IsPowMul.iInf {R : Type*} {ι : Sort*} [Pow R ℕ] [Nonempty ι] {f : ι → R → ℝ}
    (hf_nonneg : ∀ i a, 0 ≤ f i a) (hf_pm : ∀ i, IsPowMul (f i)) :
    IsPowMul (fun a ↦ ⨅ i, f i a) := by
  intro a k hk
  have hmono : Monotone fun t : ℝ ↦ (max t 0) ^ k := fun x y hxy ↦
    pow_le_pow_left₀ (le_max_right _ _) (max_le_max_right 0 hxy) k
  have hcont : Continuous fun t : ℝ ↦ (max t 0) ^ k :=
    (continuous_id.max continuous_const).pow k
  have hbdd : BddBelow (Set.range fun i ↦ f i a) :=
    ⟨0, by rintro _ ⟨i, rfl⟩; exact hf_nonneg i a⟩
  have hmap := (hmono.map_ciInf_of_continuousAt hcont.continuousAt hbdd).symm
  have hnonneg : 0 ≤ ⨅ i, f i a := le_ciInf fun i ↦ hf_nonneg i a
  simp only [max_eq_left hnonneg, fun i ↦ max_eq_left (hf_nonneg i a),
    fun i ↦ (hf_pm i a hk).symm] at hmap
  exact hmap

namespace RingSeminorm

section NonUnitalRing

variable {R : Type*} [NonUnitalRing R]

/-- The pointwise infimum of a nonempty downward-directed family of ring seminorms is a
`RingSeminorm`. -/
noncomputable def iInfOfDirected {ι : Sort*} [Nonempty ι] (p : ι → RingSeminorm R)
    (hp : Directed (· ≥ ·) (fun i ↦ (p i : R → ℝ))) : RingSeminorm R where
  toFun a := ⨅ i, p i a
  map_zero' := by simp only [map_zero, ciInf_const]
  add_le' a b := by
    have hbdd : BddBelow (Set.range fun i ↦ p i (a + b)) :=
      ⟨0, by rintro _ ⟨i, rfl⟩; exact apply_nonneg (p i) (a + b)⟩
    refine le_ciInf_add_ciInf fun i j ↦ ?_
    obtain ⟨k, hki, hkj⟩ := hp i j
    exact (ciInf_le hbdd k).trans
      ((map_add_le_add (p k) a b).trans (add_le_add (hki a) (hkj b)))
  neg' a := by simp only [map_neg_eq_map]
  mul_le' a b := by
    have hbdd : BddBelow (Set.range fun i ↦ p i (a * b)) :=
      ⟨0, by rintro _ ⟨i, rfl⟩; exact apply_nonneg (p i) (a * b)⟩
    have hpair (i j : ι) : (⨅ k, p k (a * b)) ≤ p i a * p j b := by
      obtain ⟨k, hki, hkj⟩ := hp i j
      exact (ciInf_le hbdd k).trans
        ((map_mul_le_mul (p k) a b).trans (mul_le_mul (hki a) (hkj b)
          (apply_nonneg (p k) b) (apply_nonneg (p i) a)))
    have h1 (i : ι) : (⨅ k, p k (a * b)) ≤ p i a * ⨅ j, p j b := by
      rw [Real.mul_iInf_of_nonneg (apply_nonneg (p i) a)]
      exact le_ciInf fun j ↦ hpair i j
    have hnonneg_b : 0 ≤ ⨅ j, p j b := le_ciInf fun j ↦ apply_nonneg (p j) b
    rw [Real.iInf_mul_of_nonneg hnonneg_b]
    exact le_ciInf h1

/-- Evaluating `iInfOfDirected p hp` at `a` gives `⨅ i, p i a`. -/
@[simp]
theorem iInfOfDirected_apply {ι : Sort*} [Nonempty ι] (p : ι → RingSeminorm R)
    (hp : Directed (· ≥ ·) (fun i ↦ (p i : R → ℝ))) (a : R) :
    iInfOfDirected p hp a = ⨅ i, p i a :=
  (rfl)

/-- The underlying function of `iInfOfDirected p hp` is `fun a ↦ ⨅ i, p i a`. -/
@[simp]
theorem coe_iInfOfDirected {ι : Sort*} [Nonempty ι] (p : ι → RingSeminorm R)
    (hp : Directed (· ≥ ·) (fun i ↦ (p i : R → ℝ))) :
    ⇑(iInfOfDirected p hp) = fun a ↦ ⨅ i, p i a :=
  (rfl)

/-- `iInfOfDirected p hp` is bounded above pointwise by every `p i`. -/
theorem iInfOfDirected_le {ι : Sort*} [Nonempty ι] (p : ι → RingSeminorm R)
    (hp : Directed (· ≥ ·) (fun i ↦ (p i : R → ℝ))) (i : ι) (a : R) :
    iInfOfDirected p hp a ≤ p i a :=
  ciInf_le ⟨0, by rintro _ ⟨j, rfl⟩; exact apply_nonneg (p j) a⟩ i

end NonUnitalRing

section Ring

variable {R : Type*} [Ring R]

/-- The pointwise infimum of a nonempty downward-directed family of power-multiplicative ring
seminorms is power-multiplicative. -/
theorem isPowMul_iInfOfDirected {ι : Sort*} [Nonempty ι] (p : ι → RingSeminorm R)
    (hp : Directed (· ≥ ·) (fun i ↦ (p i : R → ℝ))) (hpm : ∀ i, IsPowMul (p i)) :
    IsPowMul (iInfOfDirected p hp) :=
  IsPowMul.iInf (fun i ↦ apply_nonneg (p i)) hpm

end Ring

section CommRing

variable {R : Type*} [CommRing R]

/-- Predicate characterizing the Zorn poset in BGR Theorem 1.3.2/3: power-multiplicative ring
seminorm functions normalized at `1` that take value `r` at `x₀` and are multiplicative at `x₀`. -/
private structure PowMulSeminormAt (x₀ : R) (r : ℝ) (f : R → ℝ) : Prop where
  map_zero : f 0 = 0
  add_le : ∀ a b, f (a + b) ≤ f a + f b
  neg : ∀ a, f (-a) = f a
  mul_le : ∀ a b, f (a * b) ≤ f a * f b
  isPowMul : IsPowMul f
  map_one : f 1 = 1
  apply_x₀ : f x₀ = r
  const_mul : ∀ y, f (x₀ * y) = f x₀ * f y

/-- Bundle a function satisfying `PowMulSeminormAt` as a `RingSeminorm R`. -/
private def PowMulSeminormAt.toRingSeminorm {x₀ : R} {r : ℝ} {f : R → ℝ}
    (hf : PowMulSeminormAt x₀ r f) : RingSeminorm R where
  toFun := f
  map_zero' := hf.map_zero
  add_le' := hf.add_le
  neg' := hf.neg
  mul_le' := hf.mul_le

private theorem PowMulSeminormAt.toRingSeminorm_apply {x₀ : R} {r : ℝ} {f : R → ℝ}
    (hf : PowMulSeminormAt x₀ r f) (a : R) :
    hf.toRingSeminorm a = f a :=
  rfl

private theorem PowMulSeminormAt.of_ringSeminorm {x₀ : R} {r : ℝ} (ν : RingSeminorm R)
    (hpm : IsPowMul ν) (h1 : ν 1 = 1) (hx₀ : ν x₀ = r)
    (hmul : ∀ y, ν (x₀ * y) = ν x₀ * ν y) :
    PowMulSeminormAt x₀ r ν :=
  ⟨_root_.map_zero ν, map_add_le_add ν, map_neg_eq_map ν, map_mul_le_mul ν,
    hpm, h1, hx₀, hmul⟩

/-- The pointwise infimum of a nonempty descending chain in `{f | PowMulSeminormAt x₀ r f}` again
satisfies `PowMulSeminormAt x₀ r` and bounds the chain from below. -/
private theorem powMulSeminormAt_iInf_of_chain {x₀ : R} {r : ℝ}
    {c : Set (R → ℝ)} (hcs : c ⊆ {f | PowMulSeminormAt x₀ r f})
    (hc : IsChain (· ≥ ·) c) {y₀ : R → ℝ} (hy₀ : y₀ ∈ c) :
    ∃ lb ∈ {f | PowMulSeminormAt x₀ r f}, ∀ z ∈ c, lb ≤ z := by
  have : Nonempty c := ⟨⟨y₀, hy₀⟩⟩
  have hmem (z : c) : PowMulSeminormAt x₀ r z.val := hcs z.property
  let p : c → RingSeminorm R := fun z ↦ (hmem z).toRingSeminorm
  have hr : 0 ≤ r := (hmem ⟨y₀, hy₀⟩).apply_x₀ ▸ apply_nonneg (p ⟨y₀, hy₀⟩) x₀
  have hdir : Directed (· ≥ ·) (fun z : c ↦ (p z : R → ℝ)) := hc.directedOn.directed_val
  let lb : RingSeminorm R := iInfOfDirected p hdir
  have hlb_apply (a : R) : lb a = ⨅ z : c, z.val a := by
    simp only [lb, iInfOfDirected_apply, p, PowMulSeminormAt.toRingSeminorm_apply]
  have hlb_le (z : c) (a : R) : lb a ≤ z.val a := iInfOfDirected_le p hdir z a
  have hlb_pm : IsPowMul lb := isPowMul_iInfOfDirected p hdir (fun z ↦ (hmem z).isPowMul)
  have hlb_one : lb 1 = 1 := by
    simp only [hlb_apply, fun z : c ↦ (hmem z).map_one, ciInf_const]
  have hlb_x₀ : lb x₀ = r := by
    simp only [hlb_apply, fun z : c ↦ (hmem z).apply_x₀, ciInf_const]
  have hlb_x₀_mul (y : R) : lb (x₀ * y) = lb x₀ * lb y := by
    have hz_mul (z : c) : z.val (x₀ * y) = r * z.val y := by
      rw [(hmem z).const_mul y, (hmem z).apply_x₀]
    simp only [hlb_x₀, hlb_apply, hz_mul]
    exact (Real.mul_iInf_of_nonneg hr _).symm
  exact ⟨lb, PowMulSeminormAt.of_ringSeminorm lb hlb_pm hlb_one hlb_x₀ hlb_x₀_mul,
    fun z hz ↦ hlb_le ⟨z, hz⟩⟩

/-- Every minimal element of `{f | PowMulSeminormAt x₀ r f}` is multiplicative on all of `R`. -/
private theorem mul_of_minimal_powMulSeminormAt {x₀ : R} {r : ℝ} {m : R → ℝ}
    (hm_min : Minimal (· ∈ {f | PowMulSeminormAt x₀ r f}) m) (c y : R) :
    m (c * y) = m c * m y := by
  have hm : PowMulSeminormAt x₀ r m := hm_min.prop
  let ν : RingSeminorm R := hm.toRingSeminorm
  have hν_apply (a : R) : ν a = m a := hm.toRingSeminorm_apply a
  have hν_pm : IsPowMul ν := fun a k hk ↦ by
    simp only [hν_apply]
    exact hm.isPowMul a hk
  by_cases hc0 : ν c = 0
  · have hν_mul : ν (c * y) = ν c * ν y :=
      le_antisymm ((map_mul_le_mul ν c y).trans (by simp [hc0])) (by simp [hc0])
    simpa only [hν_apply] using hν_mul
  · let g : RingSeminorm R := seminormFromConst c ν
    have hg_le : (⇑g : R → ℝ) ≤ m := fun a ↦
      (seminormFromConst_le_seminorm c ν a).trans_eq (hν_apply a)
    have hν_x₀_mul (a : R) : ν (x₀ * a) = ν x₀ * ν a := by
      simp only [hν_apply]
      exact hm.const_mul a
    have hg_mem : PowMulSeminormAt x₀ r g :=
      PowMulSeminormAt.of_ringSeminorm g
        (seminormFromConst_isPowMul hν_pm)
        (seminormFromConst_one hc0 hν_pm)
        ((seminormFromConst_apply_of_isMul hc0 hν_pm hν_x₀_mul).trans
          ((hν_apply x₀).trans hm.apply_x₀))
        (seminormFromConst_isMul_of_isMul hc0 hν_pm hν_x₀_mul)
    have hgm : m = ⇑g := (hm_min.eq_of_le hg_mem hg_le).symm
    rw [hgm]
    exact seminormFromConst_const_mul hc0 hν_pm y

/-- Auxiliary step of BGR Theorem 1.3.2/3 when `ρ x₀ ≠ 0`. -/
private theorem exists_mulRingSeminorm_le_of_apply_ne_zero {ρ : RingSeminorm R}
    (hpm : IsPowMul ρ) {x₀ : R} (hx₀ : ρ x₀ ≠ 0) :
    ∃ α : MulRingSeminorm R, (∀ x, α x ≤ ρ x) ∧ α x₀ = ρ x₀ := by
  let μ₁ : RingSeminorm R := seminormFromConst x₀ ρ
  have hμ₁_le (x : R) : μ₁ x ≤ ρ x := seminormFromConst_le_seminorm x₀ ρ x
  have hμ₁_x₀ : μ₁ x₀ = ρ x₀ := seminormFromConst_apply_c hx₀ hpm
  have hμ₁_mem : PowMulSeminormAt x₀ (μ₁ x₀) μ₁ :=
    PowMulSeminormAt.of_ringSeminorm μ₁
      (seminormFromConst_isPowMul hpm)
      (seminormFromConst_one hx₀ hpm)
      rfl
      (seminormFromConst_const_mul hx₀ hpm)
  obtain ⟨m, hm_le, hm_min⟩ :=
    zorn_ge_nonempty₀ {f | PowMulSeminormAt x₀ (μ₁ x₀) f}
      (fun _ hcs hc _ hy₀ ↦ powMulSeminormAt_iInf_of_chain hcs hc hy₀)
      (⇑μ₁) hμ₁_mem
  have hm : PowMulSeminormAt x₀ (μ₁ x₀) m := hm_min.prop
  refine ⟨{ toAddGroupSeminorm := hm.toRingSeminorm.toAddGroupSeminorm
            map_one' := hm.map_one
            map_mul' := mul_of_minimal_powMulSeminormAt hm_min },
    fun x ↦ (hm_le x).trans (hμ₁_le x), hm.apply_x₀.trans hμ₁_x₀⟩

/-- **Bosch–Güntzer–Remmert Theorem 1.3.2/3.** For every nonzero power-multiplicative ring seminorm
`ρ` on a commutative ring `R` and every `x₀ : R`, there exists a multiplicative ring seminorm
`α : MulRingSeminorm R` with `α ≤ ρ` and `α x₀ = ρ x₀` (proved via Zorn's lemma and
`seminormFromConst`, [BGR, Proposition 1.3.2/2]). -/
theorem exists_mulRingSeminorm_le_and_apply_eq {ρ : RingSeminorm R} (hpm : IsPowMul ρ)
    (hρ : ρ ≠ 0) (x₀ : R) :
    ∃ α : MulRingSeminorm R, (∀ x, α x ≤ ρ x) ∧ α x₀ = ρ x₀ := by
  by_cases hx₀ : ρ x₀ = 0
  · have h1 : ρ 1 ≠ 0 := by
      rw [(ρ.seminorm_one_eq_one_iff_ne_zero hpm.map_one_le_one).2 hρ]
      exact one_ne_zero
    obtain ⟨α, hα, -⟩ := exists_mulRingSeminorm_le_of_apply_ne_zero hpm h1
    exact ⟨α, hα, le_antisymm (hα x₀) (by rw [hx₀]; exact apply_nonneg α x₀)⟩
  · exact exists_mulRingSeminorm_le_of_apply_ne_zero hpm hx₀

/-- Every nonzero power-multiplicative ring seminorm on a commutative ring dominates at least one
multiplicative ring seminorm. -/
theorem exists_mulRingSeminorm_le {ρ : RingSeminorm R} (hpm : IsPowMul ρ) (hρ : ρ ≠ 0) :
    ∃ α : MulRingSeminorm R, ∀ x, α x ≤ ρ x := by
  obtain ⟨α, hα, -⟩ := exists_mulRingSeminorm_le_and_apply_eq hpm hρ 1
  exact ⟨α, hα⟩

/-- Every power-multiplicative ring seminorm `ρ` on a commutative ring is the pointwise supremum of
the multiplicative ring seminorms bounded above by `ρ` (including `ρ = 0`, where the set of such
multiplicative seminorms is empty and `sSup ∅ = 0`). -/
theorem eq_sSup_mulRingSeminorm {ρ : RingSeminorm R} (hpm : IsPowMul ρ) (x : R) :
    ρ x = sSup {r : ℝ | ∃ α : MulRingSeminorm R, (∀ y, α y ≤ ρ y) ∧ α x = r} := by
  by_cases hρ : ρ = 0
  · have hρ0 : ∀ y, ρ y = 0 := eq_zero_iff.1 hρ
    have hempty : {r : ℝ | ∃ α : MulRingSeminorm R, (∀ y, α y ≤ ρ y) ∧ α x = r} = ∅ := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro α hα _
      have h1 : (1 : ℝ) ≤ 0 := by simpa [hρ0 1] using hα 1
      linarith
    rw [hempty, Real.sSup_empty, hρ0 x]
  · symm
    refine IsGreatest.csSup_eq ⟨?_, ?_⟩
    · obtain ⟨α, hα, hαx⟩ := exists_mulRingSeminorm_le_and_apply_eq hpm hρ x
      exact ⟨α, hα, hαx⟩
    · rintro _ ⟨α, hα, rfl⟩
      exact hα x

/-- For any ring seminorm `μ` on a commutative ring, `μ.smoothing x` is the supremum of `α x` over
all multiplicative ring seminorms `α ≤ μ`. -/
theorem smoothing_eq_sSup_mulRingSeminorm (μ : RingSeminorm R) (x : R) :
    μ.smoothing x = sSup {r : ℝ | ∃ α : MulRingSeminorm R, (∀ y, α y ≤ μ y) ∧ α x = r} := by
  rw [eq_sSup_mulRingSeminorm μ.isPowMul_smoothing x]
  congr 1
  ext r
  refine exists_congr fun α ↦ and_congr_left fun _ ↦
    ⟨fun h y ↦ (h y).trans (μ.smoothing_le_self y), fun h y ↦ by
      rw [smoothing_apply]
      exact α.le_smoothingFun_of_le_mul (C := 1) (fun z ↦ by simpa only [one_mul] using h z) y⟩

end CommRing

end RingSeminorm

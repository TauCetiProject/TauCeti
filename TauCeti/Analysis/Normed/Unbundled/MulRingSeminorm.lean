/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Unbundled.SmoothingSeminorm

import Mathlib.Analysis.Normed.Unbundled.IsPowMulFaithful
import Mathlib.Analysis.Normed.Unbundled.SeminormFromConst
import Mathlib.Order.Zorn

/-!
# Multiplicative ring seminorms below power-multiplicative seminorms

Every nonzero power-multiplicative ring seminorm `ρ` on a commutative ring `R` is the pointwise
maximum of the multiplicative ring seminorms `α : MulRingSeminorm R` bounded above by `ρ`
([BGR, §1.3.2, Theorem 2]). Given `x₀ : R` with `ρ x₀ ≠ 0`, `seminormFromConst` produces a
power-multiplicative seminorm `μ₁ ≤ ρ` agreeing with `ρ` at `x₀` for which `x₀` is multiplicative.
Zorn's lemma applied to descending chains of power-multiplicative seminorms below `μ₁` that keep
`x₀` multiplicative and preserve its value yields a minimal element; applying `seminormFromConst`
again at each element of nonzero seminorm shows that a minimal element is multiplicative on all of
`R`.

Combining this representation with `RingSeminorm.smoothing` expresses `smoothingFun μ x`, for any
ring seminorm `μ` on a commutative ring `R`, as the supremum of `α x` over all multiplicative ring
seminorms `α ≤ μ`, attained whenever `μ ≠ 0`. This is the unbundled core of Berkovich's spectral
formula on the Gel'fand spectrum of a normed commutative ring.

## Main definitions

* `MulRingSeminorm.toRingSeminorm`: view a multiplicative ring seminorm as a `RingSeminorm`.
* `MulRingSeminorm.comp`: composition of a multiplicative ring seminorm with a ring homomorphism.
* `RingSeminorm.iInfOfDirected`: pointwise infimum of a nonempty downward-directed family of
  ring seminorms.

## Main results

* `MulRingSeminorm.le_smoothingFun_of_le_mul`: over a commutative ring, a multiplicative seminorm
  bounded by `C * μ` is bounded by `smoothingFun μ`.
* `IsPowMul.iInf`: the pointwise infimum of a nonempty family of nonnegative power-multiplicative
  functions is power-multiplicative.
* `RingSeminorm.isPowMul_iInfOfDirected`: the pointwise infimum of a nonempty downward-directed
  family of power-multiplicative ring seminorms is power-multiplicative.
* `RingSeminorm.exists_mulRingSeminorm_le_and_apply_eq`: for a nonzero power-multiplicative ring
  seminorm `ρ` on a commutative ring and any `x₀`, some `α : MulRingSeminorm R` satisfies
  `α ≤ ρ` and `α x₀ = ρ x₀`.
* `RingSeminorm.eq_sSup_mulRingSeminorm`: every power-multiplicative ring seminorm `ρ` on a
  commutative ring is the pointwise supremum of the multiplicative ring seminorms below `ρ`.
* `RingSeminorm.smoothing_eq_sSup_mulRingSeminorm`: `μ.smoothing x` is the supremum of `α x` over
  multiplicative ring seminorms `α ≤ μ`.

## References

* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §1.3.2, Theorem 2.
* V. G. Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*,
  Mathematical Surveys and Monographs 33, AMS, 1990, Theorem 1.3.1.
-/

public section

namespace MulRingSeminorm

section NonAssocRing

variable {R S T : Type*} [NonAssocRing R] [NonAssocRing S] [NonAssocRing T]

/-- Forget multiplicativity and view a `MulRingSeminorm` as a `RingSeminorm`. -/
def toRingSeminorm (α : MulRingSeminorm R) : RingSeminorm R where
  __ := α.toAddGroupSeminorm
  mul_le' x y := (map_mul α x y).le

/-- A ring admitting a multiplicative ring seminorm is nontrivial, since `α 1 = 1 ≠ 0 = α 0`. -/
theorem nontrivial (α : MulRingSeminorm R) : Nontrivial R :=
  ⟨⟨1, 0, fun h ↦ one_ne_zero (by rw [← map_one α, h, map_zero])⟩⟩

/-- Composition of a multiplicative ring seminorm with a ring homomorphism `φ : R →+* S`, as a
multiplicative ring seminorm on `R`. -/
def comp (α : MulRingSeminorm S) (φ : R →+* S) : MulRingSeminorm R where
  __ := α.toAddGroupSeminorm.comp φ.toAddMonoidHom
  map_one' := by simp
  map_mul' x y := by simp

/-- Evaluating `α.comp φ` applies `α` after `φ`. -/
@[simp]
theorem comp_apply (α : MulRingSeminorm S) (φ : R →+* S) (x : R) :
    α.comp φ x = α (φ x) :=
  (rfl)

/-- The underlying function of `α.comp φ` is `α ∘ φ`. -/
@[simp]
theorem coe_comp (α : MulRingSeminorm S) (φ : R →+* S) :
    ⇑(α.comp φ) = α ∘ φ :=
  (rfl)

/-- Composing with the identity ring homomorphism is the identity. -/
@[simp]
theorem comp_id (α : MulRingSeminorm R) :
    α.comp (RingHom.id R) = α :=
  ext fun _ ↦ rfl

/-- Composition of multiplicative ring seminorms with ring homomorphisms is associative. -/
theorem comp_assoc (α : MulRingSeminorm T) (ψ : S →+* T) (φ : R →+* S) :
    α.comp (ψ.comp φ) = (α.comp ψ).comp φ :=
  ext fun _ ↦ rfl

/-- Adding an element of seminorm zero leaves a multiplicative ring seminorm unchanged. -/
theorem map_add_eq_left_of_map_eq_zero (α : MulRingSeminorm R) (x : R) {y : R} (hy : α y = 0) :
    α (x + y) = α x :=
  sub_eq_zero.1 <| abs_nonpos_iff.1 <|
    (abs_sub_map_le_sub α (x + y) x).trans_eq (by rw [add_sub_cancel_left, hy])

end NonAssocRing

section Ring

variable {R : Type*} [Ring R]

/-- The underlying function of `α.toRingSeminorm` is `α` itself. -/
@[simp]
theorem coe_toRingSeminorm (α : MulRingSeminorm R) :
    ⇑α.toRingSeminorm = α :=
  (rfl)

/-- Evaluating `α.toRingSeminorm` agrees with `α`. -/
@[simp]
theorem toRingSeminorm_apply (α : MulRingSeminorm R) (x : R) :
    α.toRingSeminorm x = α x :=
  (rfl)

/-- `α.toRingSeminorm` is nonzero because `α 1 = 1`. -/
theorem toRingSeminorm_ne_zero (α : MulRingSeminorm R) : α.toRingSeminorm ≠ 0 :=
  RingSeminorm.ne_zero_iff.2 ⟨1, by simp⟩

/-- Every multiplicative ring seminorm is power-multiplicative. -/
theorem isPowMul (α : MulRingSeminorm R) : IsPowMul α :=
  fun x n _ ↦ map_pow α x n

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
    (h : ∀ x, α x ≤ C * μ x) (x : R) : α x ≤ smoothingFun μ x := by
  have hle : ∀ y, α y ≤ μ y :=
    contraction_of_isPowMul_of_boundedWrt μ α.isPowMul (f := RingHom.id R)
      ⟨max C 1, zero_lt_one.trans_le (le_max_right _ _),
        fun y ↦ (h y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (apply_nonneg μ _))⟩
  refine le_ciInf fun n ↦ ?_
  calc α x = (α x ^ (n : ℕ)) ^ (1 / (n : ℝ)) := by
        rw [one_div, Real.pow_rpow_inv_natCast (apply_nonneg α x) n.ne_zero]
    _ = α (x ^ (n : ℕ)) ^ (1 / (n : ℝ)) := by rw [map_pow]
    _ ≤ μ (x ^ (n : ℕ)) ^ (1 / (n : ℝ)) := by gcongr; exact hle _

end CommRing

end MulRingSeminorm

/-- The pointwise infimum of a nonempty family of nonnegative power-multiplicative functions is
power-multiplicative. -/
theorem IsPowMul.iInf {R : Type*} {ι : Sort*} [Pow R ℕ] [Nonempty ι] {f : ι → R → ℝ}
    (hf_nonneg : ∀ i a, 0 ≤ f i a) (hf_pm : ∀ i, IsPowMul (f i)) :
    IsPowMul (fun a ↦ ⨅ i, f i a) := by
  intro a k hk
  have hbdd (x : R) : BddBelow (Set.range fun i ↦ f i x) :=
    ⟨0, by rintro _ ⟨i, rfl⟩; exact hf_nonneg i x⟩
  have hle (i : ι) (x : R) : (⨅ j, f j x) ≤ f i x := ciInf_le (hbdd x) i
  have hnonneg (x : R) : 0 ≤ ⨅ j, f j x := le_ciInf fun i ↦ hf_nonneg i x
  refine le_antisymm ?_
    (le_ciInf fun i ↦ (pow_le_pow_left₀ (hnonneg a) (hle i a) k).trans_eq
      ((hf_pm i a hk).symm))
  have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.1 hk
  have hroot : (⨅ j, f j (a ^ k)) ^ (1 / k : ℝ) ≤ ⨅ j, f j a := by
    refine le_ciInf fun i ↦ ?_
    calc (⨅ j, f j (a ^ k)) ^ (1 / k : ℝ)
        ≤ f i (a ^ k) ^ (1 / k : ℝ) := by
          gcongr
          · exact hnonneg _
          · exact hle i (a ^ k)
      _ = (f i a ^ k) ^ (1 / k : ℝ) := by rw [hf_pm i a hk]
      _ = f i a := by rw [one_div, Real.pow_rpow_inv_natCast (hf_nonneg i a) hk0]
  calc ⨅ j, f j (a ^ k)
      = ((⨅ j, f j (a ^ k)) ^ (1 / k : ℝ)) ^ k := by
        rw [one_div, ← Real.rpow_natCast, ← Real.rpow_mul (hnonneg _),
          inv_mul_cancel₀ (Nat.cast_ne_zero.2 hk0), Real.rpow_one]
    _ ≤ (⨅ j, f j a) ^ k := pow_le_pow_left₀ (Real.rpow_nonneg (hnonneg _) _) hroot k

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
    have hbdd (x : R) : BddBelow (Set.range fun i ↦ p i x) :=
      ⟨0, by rintro _ ⟨i, rfl⟩; exact apply_nonneg (p i) x⟩
    have hpair (i j : ι) : (⨅ k, p k (a + b)) ≤ p i a + p j b := by
      obtain ⟨k, hki, hkj⟩ := hp i j
      exact (ciInf_le (hbdd (a + b)) k).trans
        ((map_add_le_add (p k) a b).trans (add_le_add (hki a) (hkj b)))
    have h1 (i : ι) : (⨅ k, p k (a + b)) - p i a ≤ ⨅ j, p j b :=
      le_ciInf fun j ↦ sub_le_iff_le_add'.2 (hpair i j)
    have h2 : (⨅ k, p k (a + b)) - (⨅ j, p j b) ≤ ⨅ i, p i a :=
      le_ciInf fun i ↦ sub_le_iff_le_add.2 (sub_le_iff_le_add'.1 (h1 i))
    exact sub_le_iff_le_add.1 h2
  neg' a := by simp only [map_neg_eq_map]
  mul_le' a b := by
    have hbdd (x : R) : BddBelow (Set.range fun i ↦ p i x) :=
      ⟨0, by rintro _ ⟨i, rfl⟩; exact apply_nonneg (p i) x⟩
    have hpair (i j : ι) : (⨅ k, p k (a * b)) ≤ p i a * p j b := by
      obtain ⟨k, hki, hkj⟩ := hp i j
      exact (ciInf_le (hbdd (a * b)) k).trans
        ((map_mul_le_mul (p k) a b).trans (mul_le_mul (hki a) (hkj b)
          (apply_nonneg (p k) b) (apply_nonneg (p i) a)))
    have h1 (i : ι) : (⨅ k, p k (a * b)) ≤ p i a * (⨅ j, p j b) := by
      rcases (apply_nonneg (p i) a).eq_or_lt with hia | hia
      · simpa [← hia] using hpair i i
      · rw [← div_le_iff₀' hia]
        exact le_ciInf fun j ↦ (div_le_iff₀' hia).2 (hpair i j)
    have hnonneg_b : 0 ≤ ⨅ j, p j b := le_ciInf fun j ↦ apply_nonneg (p j) b
    rcases hnonneg_b.eq_or_lt with hb | hb
    · obtain ⟨i₀⟩ := ‹Nonempty ι›
      simpa [← hb] using h1 i₀
    · rw [← div_le_iff₀ hb]
      exact le_ciInf fun i ↦ (div_le_iff₀ hb).2 (h1 i)

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

/-- A real number bounded above by `p i a` for every `i` is bounded above by
`iInfOfDirected p hp a`. -/
theorem le_iInfOfDirected {ι : Sort*} [Nonempty ι] (p : ι → RingSeminorm R)
    (hp : Directed (· ≥ ·) (fun i ↦ (p i : R → ℝ))) {a : R} {c : ℝ}
    (hc : ∀ i, c ≤ p i a) :
    c ≤ iInfOfDirected p hp a :=
  le_ciInf hc

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

/-- A nonzero power-multiplicative ring seminorm takes value `1` at `1`. -/
theorem map_one_eq_one_of_isPowMul {ρ : RingSeminorm R} (hpm : IsPowMul ρ) (hρ : ρ ≠ 0) :
    ρ 1 = 1 :=
  (ρ.seminorm_one_eq_one_iff_ne_zero hpm.map_one_le_one).2 hρ

/-- Predicate characterizing the Zorn poset in BGR Theorem 1.3.2/2: power-multiplicative ring
seminorm functions normalized at `1` that take value `r` at `x₀` and are multiplicative at `x₀`. -/
private structure PowMulSeminormAt (x₀ : R) (r : ℝ) (f : R → ℝ) : Prop where
  map_zero : f 0 = 0
  nonneg : ∀ a, 0 ≤ f a
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
  ⟨_root_.map_zero ν, apply_nonneg ν, map_add_le_add ν, map_neg_eq_map ν, map_mul_le_mul ν,
    hpm, h1, hx₀, hmul⟩

/-- The pointwise infimum of a nonempty descending chain in `{f | PowMulSeminormAt x₀ r f}`
(for `r > 0`) again satisfies `PowMulSeminormAt x₀ r` and bounds the chain from below. -/
private theorem powMulSeminormAt_iInf_of_chain {x₀ : R} {r : ℝ} (hr : 0 < r)
    {c : Set (R → ℝ)} (hcs : c ⊆ {f | PowMulSeminormAt x₀ r f})
    (hc : IsChain (· ≥ ·) c) {y₀ : R → ℝ} (hy₀ : y₀ ∈ c) :
    ∃ lb ∈ {f | PowMulSeminormAt x₀ r f}, ∀ z ∈ c, lb ≤ z := by
  have : Nonempty c := ⟨⟨y₀, hy₀⟩⟩
  have hmem (z : c) : PowMulSeminormAt x₀ r z.1 := hcs z.2
  let p : c → RingSeminorm R := fun z ↦ (hmem z).toRingSeminorm
  have hdir : Directed (· ≥ ·) (fun z : c ↦ (p z : R → ℝ)) := hc.directedOn.directed_val
  let lb : RingSeminorm R := iInfOfDirected p hdir
  have hlb_le (z : c) (a : R) : lb a ≤ z.1 a := iInfOfDirected_le p hdir z a
  have hlb_pm : IsPowMul lb := isPowMul_iInfOfDirected p hdir (fun z ↦ (hmem z).isPowMul)
  have hlb_one : lb 1 = 1 := by
    dsimp only [lb]
    rw [iInfOfDirected_apply]
    simp only [p, PowMulSeminormAt.toRingSeminorm_apply, fun z : c ↦ (hmem z).map_one, ciInf_const]
  have hlb_x₀ : lb x₀ = r := by
    dsimp only [lb]
    rw [iInfOfDirected_apply]
    simp only [p, PowMulSeminormAt.toRingSeminorm_apply, fun z : c ↦ (hmem z).apply_x₀,
      ciInf_const]
  have hlb_x₀_mul (y : R) : lb (x₀ * y) = lb x₀ * lb y := by
    have hz_mul (z : c) : z.1 (x₀ * y) = r * z.1 y := by
      rw [(hmem z).const_mul y, (hmem z).apply_x₀]
    rw [hlb_x₀]
    refine le_antisymm ?_ (le_iInfOfDirected p hdir fun z ↦ ?_)
    · rw [← div_le_iff₀' hr]
      exact le_ciInf fun z ↦ (div_le_iff₀' hr).2 ((hlb_le z (x₀ * y)).trans_eq (hz_mul z))
    · dsimp only [p]
      rw [PowMulSeminormAt.toRingSeminorm_apply, hz_mul z]
      exact mul_le_mul_of_nonneg_left (hlb_le z y) hr.le
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
  · rw [← hν_apply, ← hν_apply, ← hν_apply]
    exact le_antisymm ((map_mul_le_mul ν c y).trans (by simp [hc0])) (by simp [hc0])
  · let g : RingSeminorm R := seminormFromConst hc0 hν_pm
    have hg_apply (a : R) : g a = seminormFromConst' c ν a := seminormFromConst_def hc0 hν_pm a
    have hg_le : (⇑g : R → ℝ) ≤ m := fun a ↦ by
      rw [hg_apply, ← hν_apply]
      exact seminormFromConst_le_seminorm hc0 hν_pm a
    have hν_x₀_mul (a : R) : ν (x₀ * a) = ν x₀ * ν a := by
      simp only [hν_apply]
      exact hm.const_mul a
    have hg_mem : PowMulSeminormAt x₀ r g :=
      PowMulSeminormAt.of_ringSeminorm g
        (fun a k hk ↦ by simp only [hg_apply]; exact seminormFromConst_isPowMul hc0 hν_pm a hk)
        (by rw [hg_apply]; exact seminormFromConst_one hc0 hν_pm)
        (by
          rw [hg_apply, seminormFromConst_apply_of_isMul hc0 hν_pm hν_x₀_mul, hν_apply]
          exact hm.apply_x₀)
        (fun a ↦ by
          simp only [hg_apply]
          exact seminormFromConst_isMul_of_isMul hc0 hν_pm hν_x₀_mul a)
    have hgm : m = ⇑g := (hm_min.eq_of_le hg_mem hg_le).symm
    rw [hgm, hg_apply, hg_apply, hg_apply]
    exact seminormFromConst_const_mul hc0 hν_pm y

/-- Auxiliary step of BGR Theorem 1.3.2/2 when `ρ x₀ ≠ 0`. -/
private theorem exists_mulRingSeminorm_le_of_apply_ne_zero {ρ : RingSeminorm R}
    (hpm : IsPowMul ρ) {x₀ : R} (hx₀ : ρ x₀ ≠ 0) :
    ∃ α : MulRingSeminorm R, (∀ x, α x ≤ ρ x) ∧ α x₀ = ρ x₀ := by
  let μ₁ : RingSeminorm R := seminormFromConst hx₀ hpm
  have hμ₁_apply (a : R) : μ₁ a = seminormFromConst' x₀ ρ a := seminormFromConst_def hx₀ hpm a
  have hμ₁_le (x : R) : μ₁ x ≤ ρ x := by
    rw [hμ₁_apply]
    exact seminormFromConst_le_seminorm hx₀ hpm x
  have hμ₁_x₀ : μ₁ x₀ = ρ x₀ := by
    rw [hμ₁_apply]
    exact seminormFromConst_apply_c hx₀ hpm
  have hx₀_pos : 0 < μ₁ x₀ :=
    lt_of_le_of_ne (apply_nonneg μ₁ x₀) (hμ₁_x₀ ▸ hx₀.symm)
  have hμ₁_mem : PowMulSeminormAt x₀ (μ₁ x₀) μ₁ :=
    PowMulSeminormAt.of_ringSeminorm μ₁
      (fun a k hk ↦ by simp only [hμ₁_apply]; exact seminormFromConst_isPowMul hx₀ hpm a hk)
      (by rw [hμ₁_apply]; exact seminormFromConst_one hx₀ hpm)
      rfl
      (fun y ↦ by simp only [hμ₁_apply]; exact seminormFromConst_const_mul hx₀ hpm y)
  obtain ⟨m, hm_le, hm_min⟩ :=
    zorn_ge_nonempty₀ {f | PowMulSeminormAt x₀ (μ₁ x₀) f}
      (fun _ hcs hc _ hy₀ ↦ powMulSeminormAt_iInf_of_chain hx₀_pos hcs hc hy₀)
      (⇑μ₁) hμ₁_mem
  have hm : PowMulSeminormAt x₀ (μ₁ x₀) m := hm_min.prop
  refine ⟨{ toAddGroupSeminorm := hm.toRingSeminorm.toAddGroupSeminorm
            map_one' := hm.map_one
            map_mul' := mul_of_minimal_powMulSeminormAt hm_min },
    fun x ↦ (hm_le x).trans (hμ₁_le x), hm.apply_x₀.trans hμ₁_x₀⟩

/-- **Bosch–Güntzer–Remmert Theorem 1.3.2/2.** For every nonzero power-multiplicative ring seminorm
`ρ` on a commutative ring `R` and every `x₀ : R`, there exists a multiplicative ring seminorm
`α : MulRingSeminorm R` with `α ≤ ρ` and `α x₀ = ρ x₀`. -/
theorem exists_mulRingSeminorm_le_and_apply_eq {ρ : RingSeminorm R} (hpm : IsPowMul ρ)
    (hρ : ρ ≠ 0) (x₀ : R) :
    ∃ α : MulRingSeminorm R, (∀ x, α x ≤ ρ x) ∧ α x₀ = ρ x₀ := by
  by_cases hx₀ : ρ x₀ = 0
  · have h1 : ρ 1 ≠ 0 := by rw [map_one_eq_one_of_isPowMul hpm hρ]; exact one_ne_zero
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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Homotopy.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# Pham's retraction of a Fermat fibre onto its skeleton

For a family of exponents `k : Fin n → ℕ`, the *Fermat fibre*
`X = {z ∈ ℂⁿ | ∑ᵢ zᵢ ^ kᵢ = 1}` contains the *Pham skeleton* `S`, the points of `X` all of whose
coordinate powers `zᵢ ^ kᵢ` are real and nonnegative. Pham showed that, when every exponent is
positive, `S` is a strong deformation retract of `X`, equivariantly for the group
`∏ᵢ μ_{kᵢ}` multiplying each coordinate by a `kᵢ`-th root of unity. For `n ≥ 2` the skeleton is
homeomorphic to the join of the finite sets `μ_{kᵢ}`, which is how one sees that `X` has the
homotopy type of a bouquet of `∏ᵢ (kᵢ - 1)` spheres of dimension `n - 1`; that identification is
not part of this file.

## The deformation

Write `uᵢ = zᵢ ^ kᵢ`, so that `∑ᵢ uᵢ = 1`, and let `m = ∑ᵢ max (re uᵢ) 0`, the total positive
part of the real parts; it is at least `∑ᵢ re uᵢ = 1`. The weights `pᵢ = max (re uᵢ) 0 / m` are
nonnegative and sum to `1`. The deformation moves each power along the segment from `uᵢ` to `pᵢ`,
`uᵢ(t) = (1 - t) uᵢ + t pᵢ`, which keeps the sum equal to `1`, and lifts it to the coordinates by
`zᵢ(t) = zᵢ · ρᵢ(t) ^ (1 / kᵢ)` with `ρᵢ(t) = (1 - t) + t pᵢ / uᵢ`. Two estimates make this lift
continuous, including at the branch point `zᵢ = 0`:

* `re ρᵢ(t) ≥ 0`, because `pᵢ · re uᵢ ≥ 0`; the principal power `w ↦ w ^ (1 / kᵢ)` is continuous
  on the closed right half-plane, including at `0`;
* `‖ρᵢ(t)‖ ≤ 1`, because `pᵢ ≤ |re uᵢ| ≤ ‖uᵢ‖` (as `m ≥ 1`), so `‖zᵢ(t)‖ ≤ ‖zᵢ‖` and the lift
  tends to `0` with `zᵢ`.

On the skeleton `m = 1` and `pᵢ = uᵢ`, so `ρᵢ(t) = 1` and the deformation fixes every point. At
`t = 1` the powers are the weights `pᵢ`, so the deformation ends in the skeleton. Since `ρᵢ`
depends on `z` only through the powers `uᵢ`, multiplying `zᵢ` by a `kᵢ`-th root of unity commutes
with the deformation.

## Main definitions

* `TauCeti.fermatFiber k`: the level-one fibre of `z ↦ ∑ᵢ zᵢ ^ kᵢ` on `Fin n → ℂ`.
* `TauCeti.phamSkeleton k`: its subspace of points whose coordinate powers are real and
  nonnegative.
* `TauCeti.phamInclusion k`: the inclusion of the skeleton into the fibre.
* `TauCeti.fermatFiber.mulRoots` and `TauCeti.phamSkeleton.mulRoots`: multiplying each coordinate
  of a point of the fibre or of the skeleton by a root of unity of its exponent.
* `TauCeti.phamRetraction k hk`: the retraction of the fibre onto the skeleton.
* `TauCeti.phamHomotopy k hk`: the homotopy from the identity of the fibre to the retraction
  followed by the inclusion, fixing the skeleton.
* `TauCeti.fermatPositiveLevels k`: the points at which `∑ᵢ zᵢ ^ kᵢ` is real and positive.
* `TauCeti.fermatPositiveLevelsHomeomorph k hk`: the homeomorphism of the positive levels with
  the product of the Fermat fibre and the positive reals.

## Main results

* `TauCeti.fermatFiber.mulRoots_one`, `TauCeti.fermatFiber.mulRoots_mulRoots` and
  `TauCeti.fermatFiber.continuous_mulRoots`, with their skeleton versions: multiplying by roots of
  unity is an action by continuous maps.
* `TauCeti.phamRetraction_coe` and `TauCeti.phamHomotopy_apply_coe`: the retraction and the
  homotopy fix the skeleton.
* `TauCeti.phamRetraction_comp_phamInclusion`: the retraction is a left inverse of the inclusion.
* `TauCeti.phamHomotopy_apply_pow`: the deformation moves each coordinate power along a segment.
* `TauCeti.phamHomotopy_apply_mulRoots` and `TauCeti.phamRetraction_mulRoots`: the homotopy and
  the retraction commute with multiplying the coordinates by roots of unity.
* `TauCeti.phamStrongRetraction`: **Pham's equivariant strong deformation retraction** of the
  Fermat fibre onto its skeleton, for every positive exponent family.

## Positive levels

Positive real scaling `zᵢ ↦ t ^ (1 / kᵢ) zᵢ` multiplies every power `zᵢ ^ kᵢ` by `t`, so it
identifies the Fermat fibre with the level `t` for every `t > 0`. Using the positive real root
of `t`, rather than a complex branch, these identifications assemble into a homeomorphism between
the set where `∑ᵢ zᵢ ^ kᵢ` is real and positive and the product of the Fermat fibre with the
positive reals.

## References

* F. Pham, *Formules de Picard–Lefschetz généralisées et ramification des intégrales*,
  Bull. Soc. Math. France **93** (1965), 333–367, Part I, §§1–2.
-/

public section

open Complex Filter Set Topology
open scoped unitInterval

namespace TauCeti

variable {n : ℕ} (k : Fin n → ℕ)

/-- The **Fermat fibre** `{z ∈ ℂⁿ | ∑ᵢ zᵢ ^ kᵢ = 1}` of an exponent family `k`, with the subspace
topology of `Fin n → ℂ`. -/
abbrev fermatFiber :=
  {z : Fin n → ℂ // ∑ i, z i ^ k i = 1}

/-- The **Pham skeleton** of the Fermat fibre: the points all of whose coordinate powers
`zᵢ ^ kᵢ` are real and nonnegative. -/
abbrev phamSkeleton :=
  {z : fermatFiber k // ∀ i, (z.val i ^ k i).im = 0 ∧ 0 ≤ (z.val i ^ k i).re}

/-- The inclusion of the Pham skeleton into the Fermat fibre. -/
def phamInclusion : C(phamSkeleton k, fermatFiber k) :=
  ⟨Subtype.val, continuous_subtypeVal⟩

@[simp]
theorem phamInclusion_apply (s : phamSkeleton k) : phamInclusion k s = s.val :=
  (rfl)

variable {k} in
/-- Multiplying each coordinate `zᵢ` of a point of the Fermat fibre by a `kᵢ`-th root of unity
`uᵢ`; this leaves every power `zᵢ ^ kᵢ` unchanged. -/
def fermatFiber.mulRoots (z : fermatFiber k) (u : Fin n → ℂ) (hu : ∀ i, u i ^ k i = 1) :
    fermatFiber k :=
  ⟨fun i => u i * z.val i, by simpa [mul_pow, hu] using z.property⟩

variable {k} in
/-- The coordinates of `z.mulRoots u hu` are `uᵢ zᵢ`. -/
@[simp]
theorem fermatFiber.mulRoots_val (z : fermatFiber k) (u : Fin n → ℂ) (hu : ∀ i, u i ^ k i = 1) :
    (z.mulRoots u hu).val = fun i => u i * z.val i :=
  (rfl)

variable {k} in
/-- Multiplying every coordinate by `1` is the identity of the Fermat fibre. -/
@[simp]
theorem fermatFiber.mulRoots_one (z : fermatFiber k) : z.mulRoots 1 (fun _ => one_pow _) = z :=
  Subtype.ext <| funext fun _ => one_mul _

variable {k} in
/-- Multiplying the coordinates by `uᵢ` and then by `vᵢ` is multiplying them by `vᵢ uᵢ`. -/
theorem fermatFiber.mulRoots_mulRoots (z : fermatFiber k) {u v : Fin n → ℂ}
    (hu : ∀ i, u i ^ k i = 1) (hv : ∀ i, v i ^ k i = 1) :
    (z.mulRoots u hu).mulRoots v hv =
      z.mulRoots (v * u) (fun i => by rw [Pi.mul_apply, mul_pow, hu, hv, one_mul]) :=
  Subtype.ext <| funext fun _ => (mul_assoc _ _ _).symm

variable {k} in
/-- Multiplying the coordinates by roots of unity is continuous on the Fermat fibre. -/
theorem fermatFiber.continuous_mulRoots {u : Fin n → ℂ} (hu : ∀ i, u i ^ k i = 1) :
    Continuous fun z : fermatFiber k => z.mulRoots u hu := by
  have h : Continuous fun z : fermatFiber k => fun i => u i * z.val i :=
    continuous_pi fun i => continuous_const.mul ((continuous_apply i).comp continuous_subtypeVal)
  exact h.subtype_mk _

variable {k} in
/-- Multiplying each coordinate `zᵢ` of a point of the Pham skeleton by a `kᵢ`-th root of unity
`uᵢ`; this leaves every power `zᵢ ^ kᵢ` unchanged, so the skeleton is preserved. -/
def phamSkeleton.mulRoots (s : phamSkeleton k) (u : Fin n → ℂ) (hu : ∀ i, u i ^ k i = 1) :
    phamSkeleton k :=
  ⟨s.val.mulRoots u hu, fun i => by simpa [mul_pow, hu] using s.property i⟩

variable {k} in
/-- Multiplying a point of the skeleton by roots of unity is computed in the fibre. -/
@[simp]
theorem phamSkeleton.mulRoots_val (s : phamSkeleton k) (u : Fin n → ℂ)
    (hu : ∀ i, u i ^ k i = 1) : (s.mulRoots u hu).val = s.val.mulRoots u hu :=
  (rfl)

variable {k} in
/-- Multiplying every coordinate by `1` is the identity of the Pham skeleton. -/
@[simp]
theorem phamSkeleton.mulRoots_one (s : phamSkeleton k) : s.mulRoots 1 (fun _ => one_pow _) = s :=
  Subtype.ext s.val.mulRoots_one

variable {k} in
/-- Multiplying the coordinates by `uᵢ` and then by `vᵢ` is multiplying them by `vᵢ uᵢ`. -/
theorem phamSkeleton.mulRoots_mulRoots (s : phamSkeleton k) {u v : Fin n → ℂ}
    (hu : ∀ i, u i ^ k i = 1) (hv : ∀ i, v i ^ k i = 1) :
    (s.mulRoots u hu).mulRoots v hv =
      s.mulRoots (v * u) (fun i => by rw [Pi.mul_apply, mul_pow, hu, hv, one_mul]) :=
  Subtype.ext (s.val.mulRoots_mulRoots hu hv)

variable {k} in
/-- Multiplying the coordinates by roots of unity is continuous on the Pham skeleton. -/
theorem phamSkeleton.continuous_mulRoots {u : Fin n → ℂ} (hu : ∀ i, u i ^ k i = 1) :
    Continuous fun s : phamSkeleton k => s.mulRoots u hu :=
  ((fermatFiber.continuous_mulRoots hu).comp continuous_subtypeVal).subtype_mk _

/-- The inclusion of the skeleton commutes with multiplying the coordinates by roots of unity. -/
theorem phamInclusion_mulRoots (s : phamSkeleton k) {u : Fin n → ℂ} (hu : ∀ i, u i ^ k i = 1) :
    phamInclusion k (s.mulRoots u hu) = (phamInclusion k s).mulRoots u hu :=
  (rfl)

/-! ### The deformation on `Fin n → ℂ` -/

/-- The total positive part `∑ᵢ max (re uᵢ) 0` of a family of complex numbers. -/
private noncomputable def posMass (u : Fin n → ℂ) : ℝ :=
  ∑ i, max (u i).re 0

/-- The endpoint weight `max (re uᵢ) 0 / ∑ⱼ max (re uⱼ) 0`. -/
private noncomputable def weight (u : Fin n → ℂ) (i : Fin n) : ℝ :=
  max (u i).re 0 / posMass u

/-- The factor `ρᵢ(t) = (1 - t) + t pᵢ / uᵢ` by which the deformation scales the `i`-th power. -/
private noncomputable def ratio (t : ℝ) (u : Fin n → ℂ) (i : Fin n) : ℂ :=
  ((1 - t : ℝ) : ℂ) + t * ((weight u i : ℂ) / u i)

/-- The coordinate powers `zᵢ ^ kᵢ`. -/
private def powers (z : Fin n → ℂ) : Fin n → ℂ :=
  fun i => z i ^ k i

/-- Pham's deformation `zᵢ(t) = zᵢ · ρᵢ(t) ^ (1 / kᵢ)`. -/
private noncomputable def deform (t : ℝ) (z : Fin n → ℂ) : Fin n → ℂ :=
  fun i => z i * ratio t (powers k z) i ^ ((k i : ℂ)⁻¹)

private theorem one_le_posMass {u : Fin n → ℂ} (hu : ∑ i, u i = 1) : 1 ≤ posMass u := by
  have h : ∑ i, (u i).re = 1 := by rw [← re_sum, hu, one_re]
  rw [← h]
  exact Finset.sum_le_sum fun i _ => le_max_left _ _

private theorem posMass_pos {u : Fin n → ℂ} (hu : ∑ i, u i = 1) : 0 < posMass u :=
  zero_lt_one.trans_le (one_le_posMass hu)

private theorem weight_nonneg {u : Fin n → ℂ} (hu : ∑ i, u i = 1) (i : Fin n) :
    0 ≤ weight u i :=
  div_nonneg (le_max_right _ _) (posMass_pos hu).le

private theorem sum_weight {u : Fin n → ℂ} (hu : ∑ i, u i = 1) : ∑ i, weight u i = 1 := by
  simp only [weight, ← Finset.sum_div]
  exact div_self (posMass_pos hu).ne'

/-- The weight is at most the norm, since the positive mass is at least one. -/
private theorem weight_le_norm {u : Fin n → ℂ} (hu : ∑ i, u i = 1) (i : Fin n) :
    weight u i ≤ ‖u i‖ := by
  calc weight u i ≤ max (u i).re 0 :=
        div_le_self (le_max_right _ _) (one_le_posMass hu)
    _ ≤ ‖u i‖ := max_le (re_le_norm _) (norm_nonneg _)

private theorem re_ratio_nonneg {u : Fin n → ℂ} (hu : ∑ i, u i = 1) {t : ℝ} (ht : t ∈ I)
    (i : Fin n) : 0 ≤ (ratio t u i).re := by
  have hw : 0 ≤ ((weight u i : ℂ) / u i).re := by
    simp only [div_re, ofReal_re, ofReal_im, zero_mul, zero_div, add_zero]
    refine div_nonneg ?_ (normSq_nonneg _)
    simp only [weight, div_mul_eq_mul_div]
    refine div_nonneg ?_ (posMass_pos hu).le
    rcases le_total 0 (u i).re with h | h
    · rw [max_eq_left h]
      exact mul_self_nonneg _
    · rw [max_eq_right h, zero_mul]
  simp only [ratio, add_re, ofReal_re, mul_re, ofReal_im, zero_mul, sub_zero]
  exact add_nonneg (sub_nonneg.2 ht.2) (mul_nonneg ht.1 hw)

private theorem norm_ratio_le_one {u : Fin n → ℂ} (hu : ∑ i, u i = 1) {t : ℝ} (ht : t ∈ I)
    (i : Fin n) : ‖ratio t u i‖ ≤ 1 := by
  have hw : ‖(weight u i : ℂ) / u i‖ ≤ 1 := by
    rw [norm_div, norm_real, Real.norm_of_nonneg (weight_nonneg hu i)]
    exact div_le_one_of_le₀ (weight_le_norm hu i) (norm_nonneg _)
  calc ‖ratio t u i‖ ≤ ‖((1 - t : ℝ) : ℂ)‖ + ‖(t : ℂ) * ((weight u i : ℂ) / u i)‖ :=
        norm_add_le _ _
    _ ≤ (1 - t) + t * 1 := by
        rw [norm_real, norm_mul, norm_real, Real.norm_of_nonneg (sub_nonneg.2 ht.2),
          Real.norm_of_nonneg ht.1]
        gcongr
        exact ht.1
    _ = 1 := by ring

/-- Scaling the `i`-th power by `ρᵢ(t)` moves it to the point at time `t` of the segment from `uᵢ`
to its weight. -/
private theorem mul_ratio (t : ℝ) (u : Fin n → ℂ) (i : Fin n) :
    u i * ratio t u i = (1 - t) * u i + t * weight u i := by
  by_cases h : u i = 0
  · simp [weight, h]
  · simp only [ratio, ofReal_sub, ofReal_one]
    field_simp

private theorem deform_pow (hk : ∀ i, k i ≠ 0) (t : ℝ) (z : Fin n → ℂ) (i : Fin n) :
    deform k t z i ^ k i = (1 - t) * z i ^ k i + t * weight (powers k z) i := by
  rw [deform, mul_pow, cpow_nat_inv_pow _ (hk i)]
  exact mul_ratio t (powers k z) i

private theorem sum_deform_pow (hk : ∀ i, k i ≠ 0) (t : ℝ) {z : Fin n → ℂ}
    (hz : ∑ i, z i ^ k i = 1) : ∑ i, deform k t z i ^ k i = 1 := by
  have hw : ∑ i, (weight (powers k z) i : ℂ) = 1 := by
    rw [← ofReal_sum, sum_weight (u := powers k z) hz, ofReal_one]
  simp only [deform_pow k hk, Finset.sum_add_distrib, ← Finset.mul_sum, hz, hw]
  ring

private theorem norm_deform_le {t : ℝ} (ht : t ∈ I) {z : Fin n → ℂ}
    (hz : ∑ i, z i ^ k i = 1) (i : Fin n) : ‖deform k t z i‖ ≤ ‖z i‖ := by
  have hpos : (0 : ℝ) ≤ (k i : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
  have hexp : ((k i : ℂ)⁻¹) = (((k i : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [deform, norm_mul, hexp, norm_cpow_real]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (Real.rpow_le_one (norm_nonneg _) (norm_ratio_le_one hz ht i) hpos)

private theorem deform_zero (z : Fin n → ℂ) : deform k 0 z = z := by
  funext i
  simp [deform, ratio]

/-- The deformation fixes every point whose coordinate powers are real and nonnegative. -/
private theorem deform_of_mem_skeleton (t : ℝ) {z : Fin n → ℂ}
    (hz : ∑ i, z i ^ k i = 1) (hS : ∀ i, (z i ^ k i).im = 0 ∧ 0 ≤ (z i ^ k i).re) :
    deform k t z = z := by
  have hmass : posMass (powers k z) = 1 := by
    rw [← one_re, ← hz, re_sum]
    exact Finset.sum_congr rfl fun i _ => max_eq_left (hS i).2
  funext i
  by_cases h : z i = 0
  · simp [deform, h]
  · have hu : z i ^ k i ≠ 0 := pow_ne_zero _ h
    have hre : ((z i ^ k i).re : ℂ) = z i ^ k i := by
      apply Complex.ext <;> simp [(hS i).1]
    have hratio : ratio t (powers k z) i = 1 := by
      simp only [ratio, weight, hmass, div_one, powers, max_eq_left (hS i).2, hre,
        div_self hu]
      push_cast
      ring
    simp [deform, hratio]

/-- At time one the coordinate powers are the weights, which are real and nonnegative. -/
private theorem deform_one_mem_skeleton (hk : ∀ i, k i ≠ 0) {z : Fin n → ℂ}
    (hz : ∑ i, z i ^ k i = 1) (i : Fin n) :
    (deform k 1 z i ^ k i).im = 0 ∧ 0 ≤ (deform k 1 z i ^ k i).re := by
  rw [deform_pow k hk]
  simpa using weight_nonneg (u := powers k z) hz i

/-- The deformation depends on the coordinates only through their powers, so it commutes with
multiplying each coordinate by a root of unity of its exponent. -/
private theorem deform_of_mul {u : Fin n → ℂ} (hu : ∀ i, u i ^ k i = 1) (t : ℝ)
    (z : Fin n → ℂ) (i : Fin n) : deform k t (fun j => u j * z j) i = u i * deform k t z i := by
  have hp : powers k (fun j => u j * z j) = powers k z := by
    funext j
    simp [powers, mul_pow, hu j]
  simp only [deform, hp, mul_assoc]

/-! ### The homotopy on the Fermat fibre -/

/-- Away from the branch point `uᵢ = 0`, the factor `ρᵢ` is continuous on `I × X`. -/
private theorem continuousAt_ratio {t : I} {z : fermatFiber k} {i : Fin n}
    (hu : z.val i ^ k i ≠ 0) :
    ContinuousAt (fun q : I × fermatFiber k => ratio q.1 (powers k q.2.val) i) (t, z) := by
  have hz : ∀ j, Continuous fun q : I × fermatFiber k => q.2.val j := fun j =>
    (continuous_apply j).comp (by fun_prop)
  have hm : posMass (powers k z.val) ≠ 0 := (posMass_pos z.property).ne'
  simp only [ratio, weight, posMass, powers] at hm ⊢
  fun_prop (disch := dsimp only; assumption)

/-- Each coordinate of the deformation is continuous on `I × X`. -/
private theorem continuous_deform_apply (hk : ∀ i, k i ≠ 0) (i : Fin n) :
    Continuous fun q : I × fermatFiber k => deform k q.1 q.2.val i := by
  have hz : Continuous fun q : I × fermatFiber k => q.2.val i :=
    (continuous_apply i).comp (by fun_prop)
  rw [continuous_iff_continuousAt]
  rintro ⟨t, z⟩
  by_cases h : z.val i = 0
  · -- At the branch point the deformation is squeezed to `0` by `‖zᵢ(t)‖ ≤ ‖zᵢ‖`.
    have h0 : deform k t z.val i = 0 := by simp [deform, h]
    rw [ContinuousAt, h0]
    refine squeeze_zero_norm (fun q => norm_deform_le k q.1.property q.2.property i) ?_
    simpa [h] using hz.norm.tendsto (t, z)
  · -- Away from it the factor is continuous, with values in the closed right half-plane, where
    -- the principal power `w ↦ w ^ (1 / kᵢ)` is continuous.
    have hpos : 0 < ((k i : ℂ)⁻¹).re := by
      simpa using Nat.pos_of_ne_zero (hk i)
    have hcpow : ContinuousAt (fun x : ℂ => x ^ ((k i : ℂ)⁻¹)) (ratio t (powers k z.val) i) :=
      continuousAt_cpow_const_of_re_pos (Or.inl (re_ratio_nonneg (u := powers k z.val) z.property
          t.property i))
        hpos
    have hfactor : ContinuousAt
        (fun q : I × fermatFiber k => ratio q.1 (powers k q.2.val) i ^ ((k i : ℂ)⁻¹)) (t, z) :=
      hcpow.comp_of_eq (continuousAt_ratio k (pow_ne_zero _ h)) rfl
    exact hz.continuousAt.mul hfactor

/-- Pham's deformation as a continuous family of self-maps of the Fermat fibre. -/
private noncomputable def deformFiber (hk : ∀ i, k i ≠ 0) : C(I × fermatFiber k, fermatFiber k) :=
  ⟨fun q => ⟨deform k q.1 q.2.val, sum_deform_pow k hk q.1 q.2.property⟩,
    (continuous_pi fun i => continuous_deform_apply k hk i).subtype_mk _⟩

/-- **Pham's retraction** of the Fermat fibre onto its skeleton, the time-one map of the
deformation. -/
noncomputable def phamRetraction (hk : ∀ i, k i ≠ 0) : C(fermatFiber k, phamSkeleton k) :=
  ⟨fun z => ⟨deformFiber k hk (1, z), deform_one_mem_skeleton k hk z.property⟩,
    ((deformFiber k hk).continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩

/-- **Pham's homotopy** from the identity of the Fermat fibre to the retraction onto the skeleton
followed by the inclusion; it fixes the skeleton at all times. -/
noncomputable def phamHomotopy (hk : ∀ i, k i ≠ 0) :
    (ContinuousMap.id (fermatFiber k)).HomotopyRel
      ((phamInclusion k).comp (phamRetraction k hk)) (range (phamInclusion k)) where
  toContinuousMap := deformFiber k hk
  map_zero_left z := Subtype.ext (deform_zero k z.val)
  map_one_left _ := (rfl)
  prop' := by
    rintro t _ ⟨s, rfl⟩
    exact Subtype.ext (deform_of_mem_skeleton k t s.val.property s.property)

private theorem phamHomotopy_apply_val (hk : ∀ i, k i ≠ 0) (t : I) (z : fermatFiber k) :
    (phamHomotopy k hk (t, z)).val = deform k t z.val :=
  (rfl)

private theorem phamRetraction_apply_val (hk : ∀ i, k i ≠ 0) (z : fermatFiber k) :
    (phamRetraction k hk z).val.val = deform k 1 z.val :=
  (rfl)

/-- The retraction fixes the skeleton. -/
@[simp]
theorem phamRetraction_coe (hk : ∀ i, k i ≠ 0) (s : phamSkeleton k) :
    phamRetraction k hk s.val = s :=
  Subtype.ext <| Subtype.ext <| deform_of_mem_skeleton k 1 s.val.property s.property

/-- The retraction is a left inverse of the inclusion. -/
theorem phamRetraction_comp_phamInclusion (hk : ∀ i, k i ≠ 0) :
    (phamRetraction k hk).comp (phamInclusion k) = ContinuousMap.id (phamSkeleton k) :=
  ContinuousMap.ext (phamRetraction_coe k hk)

/-- The homotopy fixes the skeleton at all times. -/
@[simp]
theorem phamHomotopy_apply_coe (hk : ∀ i, k i ≠ 0) (t : I) (s : phamSkeleton k) :
    phamHomotopy k hk (t, s.val) = s.val :=
  (phamHomotopy k hk).eq_fst t (mem_range_self s)

/-- **The deformation moves each coordinate power along a segment**: at time `t`, the power
`zᵢ ^ kᵢ` has moved to `(1 - t) zᵢ ^ kᵢ + t pᵢ`, where `pᵢ = max (re (zᵢ ^ kᵢ)) 0 / m` with
`m = ∑ⱼ max (re (zⱼ ^ kⱼ)) 0`. -/
theorem phamHomotopy_apply_pow (hk : ∀ i, k i ≠ 0) (t : I) (z : fermatFiber k) (i : Fin n) :
    (phamHomotopy k hk (t, z)).val i ^ k i =
      (1 - t) * z.val i ^ k i +
        t * ((max (z.val i ^ k i).re 0 / ∑ j, max (z.val j ^ k j).re 0 : ℝ) : ℂ) :=
  by rw [phamHomotopy_apply_val, deform_pow k hk]; simp [weight, posMass, powers]

/-- The retraction sends the coordinate powers `zᵢ ^ kᵢ` to the weights
`max (re (zᵢ ^ kᵢ)) 0 / ∑ⱼ max (re (zⱼ ^ kⱼ)) 0`. -/
theorem phamRetraction_apply_pow (hk : ∀ i, k i ≠ 0) (z : fermatFiber k) (i : Fin n) :
    (phamRetraction k hk z).val.val i ^ k i =
      ((max (z.val i ^ k i).re 0 / ∑ j, max (z.val j ^ k j).re 0 : ℝ) : ℂ) := by
  rw [phamRetraction_apply_val, deform_pow k hk]
  simp [weight, posMass, powers]

/-- **Equivariance of the homotopy**: multiplying each coordinate by a root of unity of its
exponent commutes with Pham's homotopy at every time. -/
theorem phamHomotopy_apply_mulRoots (hk : ∀ i, k i ≠ 0) {u : Fin n → ℂ}
    (hu : ∀ i, u i ^ k i = 1) (t : I) (z : fermatFiber k) :
    phamHomotopy k hk (t, z.mulRoots u hu) = (phamHomotopy k hk (t, z)).mulRoots u hu :=
  Subtype.ext <| by
    simp only [phamHomotopy_apply_val, fermatFiber.mulRoots_val]
    exact funext (deform_of_mul k hu t z.val)

/-- **Equivariance of the retraction**: multiplying each coordinate by a root of unity of its
exponent commutes with Pham's retraction. -/
theorem phamRetraction_mulRoots (hk : ∀ i, k i ≠ 0) {u : Fin n → ℂ}
    (hu : ∀ i, u i ^ k i = 1) (z : fermatFiber k) :
    phamRetraction k hk (z.mulRoots u hu) = (phamRetraction k hk z).mulRoots u hu :=
  Subtype.ext <| Subtype.ext <| by
    simp only [phamRetraction_apply_val, phamSkeleton.mulRoots_val, fermatFiber.mulRoots_val]
    exact funext (deform_of_mul k hu 1 z.val)

/-- **Pham's equivariant strong deformation retraction.** For every positive exponent family
`k`, the Pham skeleton is a strong deformation retract of the Fermat fibre
`{z ∈ ℂⁿ | ∑ᵢ zᵢ ^ kᵢ = 1}`: there is a retraction `r` with `r ∘ ι = id` and a homotopy from the
identity to `ι ∘ r` fixing the skeleton at all times. The homotopy commutes with multiplying the
coordinates by roots of unity of their exponents. -/
theorem phamStrongRetraction (n : ℕ) (k : Fin n → ℕ) (hk : ∀ i, 1 ≤ k i) :
    ∃ r : C(fermatFiber k, phamSkeleton k),
      r.comp (phamInclusion k) = ContinuousMap.id (phamSkeleton k) ∧
      ∃ H : (ContinuousMap.id (fermatFiber k)).HomotopyRel ((phamInclusion k).comp r)
          (range (phamInclusion k)),
        ∀ u : Fin n → ℂ, (∀ i, u i ^ k i = 1) →
          ∀ (t : I) (z w : fermatFiber k), (∀ i, w.val i = u i * z.val i) →
            ∀ i, (H (t, w)).val i = u i * (H (t, z)).val i := by
  have hk : ∀ i, k i ≠ 0 := fun i => Nat.one_le_iff_ne_zero.1 (hk i)
  refine ⟨phamRetraction k hk, phamRetraction_comp_phamInclusion k hk, phamHomotopy k hk,
    fun u hu t z w hw i => ?_⟩
  obtain rfl : w = z.mulRoots u hu := Subtype.ext <| by
    rw [fermatFiber.mulRoots_val]
    exact funext hw
  simp only [phamHomotopy_apply_mulRoots, fermatFiber.mulRoots_val]

/-! ### Positive levels -/

/-- The points of `ℂⁿ` at which the Fermat polynomial `∑ᵢ zᵢ ^ kᵢ` takes a real positive value,
with the subspace topology of `Fin n → ℂ`. -/
abbrev fermatPositiveLevels :=
  {z : Fin n → ℂ // (∑ i, z i ^ k i).im = 0 ∧ 0 < (∑ i, z i ^ k i).re}

/-- Weighted scaling `zᵢ ↦ s ^ (1 / kᵢ) zᵢ`, which multiplies every power `zᵢ ^ kᵢ` by `s`. -/
private noncomputable def weightedScale (s : ℝ) (z : Fin n → ℂ) : Fin n → ℂ :=
  fun i => ((s ^ ((k i : ℝ)⁻¹) : ℝ) : ℂ) * z i

private theorem sum_weightedScale_pow (hk : ∀ i, k i ≠ 0) {s : ℝ} (hs : 0 ≤ s)
    (z : Fin n → ℂ) : ∑ i, weightedScale k s z i ^ k i = s * ∑ i, z i ^ k i := by
  simp only [weightedScale, mul_pow, ← ofReal_pow, Real.rpow_inv_natCast_pow hs (hk _),
    Finset.mul_sum]

private theorem weightedScale_weightedScale {s s' : ℝ} (hs : 0 ≤ s) (hs' : 0 ≤ s')
    (z : Fin n → ℂ) : weightedScale k s (weightedScale k s' z) = weightedScale k (s * s') z := by
  funext i
  simp only [weightedScale, Real.mul_rpow hs hs', ofReal_mul, mul_assoc]

private theorem weightedScale_one (z : Fin n → ℂ) : weightedScale k 1 z = z := by
  funext i
  simp [weightedScale]

private theorem continuous_weightedScale {X : Type*} [TopologicalSpace X] {s : X → ℝ}
    {z : X → Fin n → ℂ} (hs : Continuous s) (hz : Continuous z) :
    Continuous fun x => weightedScale k (s x) (z x) := by
  unfold weightedScale
  fun_prop

/-- The value `∑ᵢ zᵢ ^ kᵢ` of the Fermat polynomial at a point of a positive level. -/
private theorem sum_pow_eq_ofReal (z : fermatPositiveLevels k) :
    ∑ i, z.val i ^ k i = ((∑ i, z.val i ^ k i).re : ℂ) :=
  Complex.ext (by simp) (by simp [z.property.1])

/-- Rescaling a point of the positive level `t` by `t⁻¹` lands in the Fermat fibre. -/
private theorem sum_weightedScale_inv_pow (hk : ∀ i, k i ≠ 0) (z : fermatPositiveLevels k) :
    ∑ i, weightedScale k (∑ i, z.val i ^ k i).re⁻¹ z.val i ^ k i = 1 := by
  have h := sum_pow_eq_ofReal k z
  have hpos := z.property.2
  generalize (∑ i, z.val i ^ k i).re = t at h hpos ⊢
  rw [sum_weightedScale_pow k hk (inv_nonneg.2 hpos.le), h, ← ofReal_mul,
    inv_mul_cancel₀ hpos.ne', ofReal_one]

/-- Rescaling a point of the Fermat fibre by a positive `t` lands in the positive level `t`. -/
private theorem sum_weightedScale_fiber_pow (hk : ∀ i, k i ≠ 0) {t : ℝ} (ht : 0 ≤ t)
    (x : fermatFiber k) : ∑ i, weightedScale k t x.val i ^ k i = t := by
  rw [sum_weightedScale_pow k hk ht, x.property, mul_one]

/-- The level of a point at a positive level, as a positive real. -/
private noncomputable def positiveLevel (z : fermatPositiveLevels k) : Ioi (0 : ℝ) :=
  ⟨(∑ i, z.val i ^ k i).re, z.property.2⟩

private theorem continuous_positiveLevel : Continuous (positiveLevel k) := by
  have h : Continuous fun z : Fin n → ℂ => (∑ i, z i ^ k i).re := by fun_prop
  exact (h.comp continuous_subtypeVal).subtype_mk _

/-- Rescaling a point at the positive level `t` by `t⁻¹`, a point of the Fermat fibre. -/
private noncomputable def toFermatFiber (hk : ∀ i, k i ≠ 0) (z : fermatPositiveLevels k) :
    fermatFiber k :=
  ⟨weightedScale k (positiveLevel k z : ℝ)⁻¹ z.val, sum_weightedScale_inv_pow k hk z⟩

/-- Rescaling a point of the Fermat fibre by a positive `t`, a point at the level `t`. -/
private noncomputable def ofFermatFiber (hk : ∀ i, k i ≠ 0) (p : fermatFiber k × Ioi (0 : ℝ)) :
    fermatPositiveLevels k :=
  ⟨weightedScale k p.2 p.1.val, by
    rw [sum_weightedScale_fiber_pow k hk (le_of_lt p.2.property) p.1, ofReal_im, ofReal_re]
    exact ⟨rfl, p.2.property⟩⟩

private theorem positiveLevel_ofFermatFiber (hk : ∀ i, k i ≠ 0)
    (p : fermatFiber k × Ioi (0 : ℝ)) : positiveLevel k (ofFermatFiber k hk p) = p.2 :=
  Subtype.ext <| by
    simp only [positiveLevel, ofFermatFiber]
    rw [sum_weightedScale_fiber_pow k hk (le_of_lt p.2.property) p.1, ofReal_re]

/-- **The positive levels of the Fermat polynomial form a product.** For a positive exponent
family, the points where `t = ∑ᵢ zᵢ ^ kᵢ` is real and positive are homeomorphic to the product
of the Fermat fibre with the positive reals, by `z ↦ ((t ^ (-1 / kᵢ) zᵢ)ᵢ, t)` with inverse
`(x, t) ↦ (t ^ (1 / kᵢ) xᵢ)ᵢ`. -/
noncomputable def fermatPositiveLevelsHomeomorph (hk : ∀ i, k i ≠ 0) :
    fermatPositiveLevels k ≃ₜ fermatFiber k × Ioi (0 : ℝ) where
  toFun z := (toFermatFiber k hk z, positiveLevel k z)
  invFun := ofFermatFiber k hk
  left_inv z := Subtype.ext <| by
    have hz := (positiveLevel k z).property
    simp only [ofFermatFiber, toFermatFiber]
    rw [weightedScale_weightedScale k (le_of_lt hz) (inv_nonneg.2 (le_of_lt hz)),
      mul_inv_cancel₀ (ne_of_gt hz), weightedScale_one]
  right_inv p := by
    have hp := p.2.property
    refine Prod.ext (Subtype.ext ?_) (positiveLevel_ofFermatFiber k hk p)
    simp only [toFermatFiber, positiveLevel_ofFermatFiber k hk p]
    rw [ofFermatFiber, weightedScale_weightedScale k (inv_nonneg.2 (le_of_lt hp)) (le_of_lt hp),
      inv_mul_cancel₀ (ne_of_gt hp), weightedScale_one]
  continuous_toFun := by
    refine Continuous.prodMk ?_ (continuous_positiveLevel k)
    have hl : Continuous fun z : fermatPositiveLevels k => (positiveLevel k z : ℝ) :=
      continuous_subtypeVal.comp (continuous_positiveLevel k)
    exact (continuous_weightedScale k (hl.inv₀ fun z => ne_of_gt (positiveLevel k z).property)
      continuous_subtypeVal).subtype_mk _
  continuous_invFun :=
    (continuous_weightedScale k (continuous_subtypeVal.comp continuous_snd)
      (continuous_subtypeVal.comp continuous_fst)).subtype_mk _

/-- The second component of `TauCeti.fermatPositiveLevelsHomeomorph` is the level
`∑ᵢ zᵢ ^ kᵢ`. -/
@[simp]
theorem fermatPositiveLevelsHomeomorph_apply_snd (hk : ∀ i, k i ≠ 0)
    (z : fermatPositiveLevels k) :
    ((fermatPositiveLevelsHomeomorph k hk z).2 : ℝ) = (∑ i, z.val i ^ k i).re :=
  (rfl)

/-- The first component of `TauCeti.fermatPositiveLevelsHomeomorph` rescales the `i`-th
coordinate by `t ^ (-1 / kᵢ)`, where `t = ∑ᵢ zᵢ ^ kᵢ`. -/
@[simp]
theorem fermatPositiveLevelsHomeomorph_apply_fst (hk : ∀ i, k i ≠ 0)
    (z : fermatPositiveLevels k) (i : Fin n) :
    (fermatPositiveLevelsHomeomorph k hk z).1.val i =
      (((∑ j, z.val j ^ k j).re⁻¹ ^ ((k i : ℝ)⁻¹) : ℝ) : ℂ) * z.val i :=
  (rfl)

/-- The inverse of `TauCeti.fermatPositiveLevelsHomeomorph` rescales the `i`-th coordinate of a
fibre point by `t ^ (1 / kᵢ)`. -/
@[simp]
theorem fermatPositiveLevelsHomeomorph_symm_apply (hk : ∀ i, k i ≠ 0)
    (p : fermatFiber k × Ioi (0 : ℝ)) (i : Fin n) :
    ((fermatPositiveLevelsHomeomorph k hk).symm p).val i =
      (((p.2 : ℝ) ^ ((k i : ℝ)⁻¹) : ℝ) : ℂ) * p.1.val i :=
  (rfl)

end TauCeti

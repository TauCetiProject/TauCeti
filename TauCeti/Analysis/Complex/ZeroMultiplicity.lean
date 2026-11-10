/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ContinuousLog.ArgumentPrinciple
public import Mathlib.Algebra.Polynomial.Roots
import TauCeti.Analysis.Complex.Wirtinger.Similarity
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Topology.Algebra.Polynomial

/-!
# Zero multiplicities of functions with local power factorizations

A function `n : ℂ → ℕ` is a **zero multiplicity function** of `f : ℂ → ℂ`
(`TauCeti.IsZeroMultiplicity f n`) if near every point `z` the function factors as

`f w = (w - z) ^ n z * v w`,  with `v` continuous at `z` and `v z ≠ 0`.

No holomorphy is assumed. This is the local form that the similarity principle
(`TauCeti.exists_contDiffAt_pow_mul_of_conjWirtingerDeriv_apply_one_eq_mul`) gives for solutions
of `∂bar f = a f`, for instance for the section of a plane vortex, and it is the hypothesis of the
topological argument principle `TauCeti.finsum_eq_of_tendsto_mul_inv_pow`. The exponent of such a
factorization is unique (`TauCeti.eq_of_eventually_sub_pow_mul_eq`), so `f` has at most one zero
multiplicity function (`TauCeti.IsZeroMultiplicity.unique`); it is positive exactly at the zeros of
`f`.

This file proves how zero multiplicities transform:

* under an affine change of variable `w ↦ c w + a` with `c ≠ 0`, the multiplicity is pulled back
  (`TauCeti.IsZeroMultiplicity.comp_mul_add`);
* under products, multiplicities add (`TauCeti.IsZeroMultiplicity.mul`); the functions with
  multiplicity zero are the continuous functions without zeros
  (`TauCeti.isZeroMultiplicity_zero_iff`), so multiplying by such a function does not change the
  multiplicity;
* a nonzero polynomial has its root multiplicities as zero multiplicity function
  (`TauCeti.isZeroMultiplicity_eval_rootMultiplicity`), in particular `∏ (w - a)` over a multiset
  `D` has multiplicity `count · D` (`TauCeti.isZeroMultiplicity_prod_sub`).

If `f` has no zeros near infinity, its multiplicities are the counts of a multiset of points,
which they determine: the divisor of zeros of `f` (`TauCeti.IsZeroMultiplicity.exists_eq_count`).
When moreover `f(z) (z / |z|)⁻ᵐ → 1` at infinity, that divisor has `m` points
(`TauCeti.IsZeroMultiplicity.card_eq_of_tendsto_mul_inv_pow`).
-/

public section

namespace TauCeti

open Filter Polynomial Topology

/-- `n` is a **zero multiplicity function** of `f`: near every point `z`, `f` factors as
`f w = (w - z) ^ n z * v w` with `v` continuous at `z` and `v z ≠ 0`. -/
def IsZeroMultiplicity (f : ℂ → ℂ) (n : ℂ → ℕ) : Prop :=
  ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧ ∀ᶠ w in 𝓝 z, f w = (w - z) ^ n z * v w

variable {f g : ℂ → ℂ} {n n' : ℂ → ℕ}

/-- The defining local factorizations of a zero multiplicity function. -/
theorem isZeroMultiplicity_iff :
    IsZeroMultiplicity f n ↔
      ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧ ∀ᶠ w in 𝓝 z, f w = (w - z) ^ n z * v w :=
  Iff.rfl

namespace IsZeroMultiplicity

/-- **Uniqueness of zero multiplicities.** A function has at most one zero multiplicity
function. -/
theorem unique (h : IsZeroMultiplicity f n) (h' : IsZeroMultiplicity f n') : n = n' :=
  funext fun z ↦ by
    obtain ⟨v, hv, hv₀, hf⟩ := isZeroMultiplicity_iff.1 h z
    obtain ⟨v', hv', hv₀', hf'⟩ := isZeroMultiplicity_iff.1 h' z
    exact eq_of_eventually_sub_pow_mul_eq hv hv₀ hv' hv₀' <| by
      filter_upwards [hf, hf'] with w hw hw'
      rw [← hw, ← hw']

/-- A function with a zero multiplicity function is continuous. -/
theorem continuous (h : IsZeroMultiplicity f n) : Continuous f :=
  continuous_of_eventually_eq_pow_mul fun z ↦
    (isZeroMultiplicity_iff.1 h z).imp fun _ hv ↦ ⟨hv.1, hv.2.2⟩

/-- The multiplicity vanishes exactly off the zeros of `f`. -/
theorem eq_zero_iff (h : IsZeroMultiplicity f n) {z : ℂ} : n z = 0 ↔ f z ≠ 0 := by
  obtain ⟨v, -, hv₀, hf⟩ := isZeroMultiplicity_iff.1 h z
  rw [hf.self_of_nhds, sub_self]
  rcases eq_or_ne (n z) 0 with hz | hz <;> simp [hz, hv₀]

/-- The multiplicity is positive exactly at the zeros of `f`. -/
theorem pos_iff (h : IsZeroMultiplicity f n) {z : ℂ} : 0 < n z ↔ f z = 0 := by
  rw [Nat.pos_iff_ne_zero, Ne, h.eq_zero_iff, not_not]

/-- **Affine change of variable.** If `c ≠ 0`, the zero multiplicity of `w ↦ f (c w + a)` at `z`
is that of `f` at `c z + a`. -/
theorem comp_mul_add (h : IsZeroMultiplicity f n) {c : ℂ} (hc : c ≠ 0) (a : ℂ) :
    IsZeroMultiplicity (fun w ↦ f (c * w + a)) fun z ↦ n (c * z + a) := by
  refine isZeroMultiplicity_iff.2 fun z ↦ ?_
  obtain ⟨v, hv, hv₀, hf⟩ := isZeroMultiplicity_iff.1 h (c * z + a)
  have hφ : Continuous fun w : ℂ ↦ c * w + a := by fun_prop
  refine ⟨fun w ↦ c ^ n (c * z + a) * v (c * w + a),
    continuousAt_const.mul (hv.comp_of_eq hφ.continuousAt rfl),
    mul_ne_zero (pow_ne_zero _ hc) hv₀, ?_⟩
  filter_upwards [(hφ.tendsto z).eventually hf] with w hw
  rw [hw, show c * w + a - (c * z + a) = c * (w - z) by ring, mul_pow]
  ring

/-- **Multiplicities add under products.** -/
theorem mul (h : IsZeroMultiplicity f n) (h' : IsZeroMultiplicity g n') :
    IsZeroMultiplicity (fun w ↦ f w * g w) (n + n') := by
  refine isZeroMultiplicity_iff.2 fun z ↦ ?_
  obtain ⟨v, hv, hv₀, hf⟩ := isZeroMultiplicity_iff.1 h z
  obtain ⟨v', hv', hv₀', hg⟩ := isZeroMultiplicity_iff.1 h' z
  refine ⟨fun w ↦ v w * v' w, hv.mul hv', mul_ne_zero hv₀ hv₀', ?_⟩
  filter_upwards [hf, hg] with w hw hw'
  rw [hw, hw', Pi.add_apply, pow_add]
  ring

/-- If `f` has no zeros near infinity, its zero multiplicities are the counts of a multiset of
points, the divisor of zeros of `f`. -/
theorem exists_eq_count (h : IsZeroMultiplicity f n) (htail : ∀ᶠ w in cocompact ℂ, f w ≠ 0) :
    ∃ D : Multiset ℂ, n = fun z ↦ D.count z := by
  classical
  have hfin := finite_support_of_eventually_eq_pow_mul (isZeroMultiplicity_iff.1 h) htail
  refine ⟨(Finsupp.ofSupportFinite n hfin).toMultiset, funext fun z ↦ ?_⟩
  simp [Finsupp.ofSupportFinite_coe]

/-- **The degree of the divisor of zeros.** If `f(z) (z / |z|)⁻ᵐ → 1` at infinity and the zero
multiplicities of `f` are the counts of `D`, then `D` has `m` points. -/
theorem card_eq_of_tendsto_mul_inv_pow {D : Multiset ℂ}
    (h : IsZeroMultiplicity f fun z ↦ D.count z) {m : ℕ}
    (hm : Tendsto (fun z ↦ f z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    Multiset.card D = m := by
  classical
  rw [← finsum_eq_of_tendsto_mul_inv_pow (isZeroMultiplicity_iff.1 h) hm,
    finsum_eq_sum_of_support_subset _ (s := D.toFinset) fun z hz ↦ ?_,
    Multiset.toFinset_sum_count_eq]
  simpa [Multiset.count_eq_zero] using hz

end IsZeroMultiplicity

/-- **Zero multiplicity zero.** The functions with zero multiplicity function `0` are the
continuous functions without zeros. -/
theorem isZeroMultiplicity_zero_iff :
    IsZeroMultiplicity g 0 ↔ Continuous g ∧ ∀ z, g z ≠ 0 := by
  refine ⟨fun h ↦ ⟨h.continuous, fun z ↦ h.eq_zero_iff.1 rfl⟩, fun ⟨hg, hg₀⟩ ↦ ?_⟩
  exact isZeroMultiplicity_iff.2 fun z ↦
    ⟨g, hg.continuousAt, hg₀ z, Eventually.of_forall fun w ↦ by simp⟩

/-- Multiplying by a continuous function without zeros does not change the zero
multiplicities. -/
theorem IsZeroMultiplicity.mul_left_of_continuous (h : IsZeroMultiplicity f n)
    (hg : Continuous g) (hg₀ : ∀ z, g z ≠ 0) : IsZeroMultiplicity (fun w ↦ g w * f w) n := by
  simpa using (isZeroMultiplicity_zero_iff.2 ⟨hg, hg₀⟩).mul h

/-- The zero multiplicities of a nonzero complex polynomial are its root multiplicities. -/
theorem isZeroMultiplicity_eval_rootMultiplicity {p : ℂ[X]} (hp : p ≠ 0) :
    IsZeroMultiplicity (fun w ↦ p.eval w) fun z ↦ p.rootMultiplicity z := by
  refine isZeroMultiplicity_iff.2 fun z ↦ ?_
  refine ⟨fun w ↦ (p /ₘ (X - C z) ^ p.rootMultiplicity z).eval w,
    (Polynomial.continuous _).continuousAt, eval_divByMonic_pow_rootMultiplicity_ne_zero z hp,
    Eventually.of_forall fun w ↦ ?_⟩
  conv_lhs => rw [← pow_mul_divByMonic_rootMultiplicity_eq p z]
  simp

/-- The zero multiplicities of `w ↦ ∏_{a ∈ D} (w - a)` are the counts of the multiset `D`. -/
theorem isZeroMultiplicity_prod_sub (D : Multiset ℂ) :
    IsZeroMultiplicity (fun w ↦ (D.map fun a ↦ w - a).prod) fun z ↦ D.count z := by
  classical
  have hmonic : (D.map fun a ↦ X - C a).prod.Monic :=
    monic_multiset_prod_of_monic _ _ fun a _ ↦ monic_X_sub_C a
  convert isZeroMultiplicity_eval_rootMultiplicity hmonic.ne_zero using 1
  · funext w
    simp [eval_multiset_prod, Multiset.map_map]
  · funext z
    rw [← count_roots, roots_multiset_prod_X_sub_C]

end TauCeti

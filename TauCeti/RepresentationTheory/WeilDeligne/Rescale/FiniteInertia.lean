/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.WeilDeligne.Rescale

import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import TauCeti.LinearAlgebra.Eigenspace.ScaledConjugation

/-!
# Rescaling the monodromy of a parameter with finite inertia image

Let `(V, r, N)` be a raw Weil–Deligne parameter over a field `E`, with `V` finite-dimensional,
`q` of infinite multiplicative order in `E` (for instance `q ≥ 2` in characteristic zero), a
degree map that is not trivial, and finite inertia image: the image under `r` of the kernel of the
degree is finite. Then `(r, N) ≅ (r, a N)` for every `a ≠ 0`
(`TauCeti.WeilDeligneParameter.nonempty_iso_rescale`, and
`TauCeti.WeilDeligneParameter.nonempty_iso_rescale_of_two_le` in characteristic zero; Deligne
1973, proof of §8.4.3). No Frobenius-semisimplicity hypothesis is needed.

The proof has two steps.

* **A central Frobenius power.** Choose `Φ` whose degree generates the image of the degree map,
  so that every element of `W` is a power of `Φ` times an element of the inertia `ker deg`.
  Conjugation by the powers of `r(Φ)` permutes the finite inertia image, so two different powers
  induce the same permutation and some `F = r(Φ ^ d)`, `d ≠ 0`, commutes with the inertia image,
  hence with every `r(w)`. The conjugation relation gives `F * N = c • (N * F)` with
  `c = q ^ (d deg Φ)`, of infinite multiplicative order since `q` is.
* **Linear algebra.** `Module.End.exists_mul_eq_smul_mul_of_mul_eq_smul_mul` provides an
  automorphism commuting with everything that commutes with `F`, in particular with the Weil
  action, and conjugating `N` to `a N`: over an algebraic closure it acts on the generalized
  eigenspaces of `F` by suitable powers of `a`, and it descends to `E`.

## Main results

* `TauCeti.WeilDeligneParameter.exists_zpow_commute_of_finite`: some nonzero power of `r(Φ)`
  commutes with the inertia image.
* `TauCeti.WeilDeligneParameter.nonempty_iso_rescale`: `(r, N) ≅ (r, a N)` for `a ≠ 0`.
* `TauCeti.WeilDeligneParameter.nonempty_iso_rescale_of_two_le`: the same in characteristic zero
  for `q ≥ 2`.

## References

* P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*, in *Modular functions
  of one variable II*, Lecture Notes in Math. 349 (1973), §8.4.1, p. 568, and the proof of §8.4.3,
  p. 569.
-/

public section

namespace TauCeti

namespace WeilDeligneParameter

variable {E W V : Type*} [Field E] [Group W] [TopologicalSpace W]
  [AddCommGroup V] [Module E V] {deg : W →* Multiplicative ℤ} {q : ℕ}

omit [TopologicalSpace W] in
/-- If the degree map is not trivial, some `Φ` has nonzero degree generating its image. -/
private theorem exists_deg_generator (hdeg : ∃ w, deg w ≠ 1) :
    ∃ Φ : W, (deg Φ).toAdd ≠ 0 ∧ ∀ w : W, ∃ k : ℤ, deg w = deg Φ ^ k := by
  obtain ⟨⟨x, hx⟩, hsurj⟩ := exists_zpow_surjective deg.range
  obtain ⟨Φ, rfl⟩ := MonoidHom.mem_range.mp hx
  have hgen (w : W) : ∃ k : ℤ, deg w = deg Φ ^ k := by
    obtain ⟨k, hk⟩ := hsurj ⟨deg w, w, rfl⟩
    exact ⟨k, (congrArg Subtype.val hk).symm.trans (by simp)⟩
  refine ⟨Φ, fun h0 ↦ ?_, hgen⟩
  obtain ⟨w₀, hw₀⟩ := hdeg
  obtain ⟨k, hk⟩ := hgen w₀
  have hΦ : deg Φ = 1 := by rw [← ofAdd_toAdd (deg Φ), h0, ofAdd_zero]
  exact hw₀ (by rw [hk, hΦ, one_zpow])

/-- **A power of `r(Φ)` commuting with the inertia image.** If the image under `r` of the kernel
of the degree is finite, then for every `Φ` some nonzero power `r(Φ ^ d)` commutes with every
`r(i)`, `i ∈ ker deg`: conjugation by the powers of `r(Φ)` permutes the finite inertia image, so
two different powers induce the same permutation. -/
theorem exists_zpow_commute_of_finite (D : WeilDeligneParameter E W V deg q)
    (hI : (D.r '' (deg.ker : Set W)).Finite) (Φ : W) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ i ∈ deg.ker, Commute (D.r (Φ ^ d)) (D.r i) := by
  have : Finite (D.r '' (deg.ker : Set W)) := hI.to_subtype
  let f : ℤ → D.r '' (deg.ker : Set W) → D.r '' (deg.ker : Set W) := fun n s ↦
    ⟨D.r (Φ ^ n) * s * D.r (Φ ^ n)⁻¹, by
      obtain ⟨i, hi, hs⟩ := s.property
      refine ⟨Φ ^ n * i * (Φ ^ n)⁻¹, (MonoidHom.normal_ker deg).conj_mem i hi (Φ ^ n), ?_⟩
      rw [map_mul, map_mul, hs]⟩
  obtain ⟨n₁, n₂, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  refine ⟨n₂ - n₁, sub_ne_zero.mpr hne.symm, fun i hi ↦ ?_⟩
  have h := congrArg Subtype.val (congrFun heq ⟨D.r i, i, hi, rfl⟩)
  simp only [f, ← map_mul] at h
  change D.r (Φ ^ (n₂ - n₁)) * D.r i = D.r i * D.r (Φ ^ (n₂ - n₁))
  calc D.r (Φ ^ (n₂ - n₁)) * D.r i
      = D.r (Φ ^ (-n₁)) * D.r (Φ ^ n₂ * i * (Φ ^ n₂)⁻¹) * D.r (Φ ^ n₂) := by
        simp only [← map_mul]
        congr 1
        group
    _ = D.r (Φ ^ (-n₁)) * D.r (Φ ^ n₁ * i * (Φ ^ n₁)⁻¹) * D.r (Φ ^ n₂) := by rw [h]
    _ = D.r i * D.r (Φ ^ (n₂ - n₁)) := by
        simp only [← map_mul]
        congr 1
        group

/-- **`(r, N) ≅ (r, a N)` for finite inertia image.** A raw Weil–Deligne parameter on a
finite-dimensional space with a nontrivial degree map and finite inertia image, and with `q` of
infinite multiplicative order in `E`, is isomorphic to its rescaling by every `a ≠ 0`. No
Frobenius-semisimplicity hypothesis is needed (Deligne 1973, proof of §8.4.3, p. 569). The
hypothesis on `q` cannot be dropped: see `TauCeti.WeilDeligneParameter.eq_one_of_iso_rescale`
for `q = 1`. -/
theorem nonempty_iso_rescale [FiniteDimensional E V] (D : WeilDeligneParameter E W V deg q)
    (hq : ¬IsOfFinOrder (q : E)) (hdeg : ∃ w, deg w ≠ 1)
    (hI : (D.r '' (deg.ker : Set W)).Finite) {a : E} (ha : a ≠ 0) :
    Nonempty (Iso D (D.rescale a)) := by
  obtain ⟨Φ, hΦ, hgen⟩ := exists_deg_generator hdeg
  obtain ⟨d, hd, hcomm⟩ := D.exists_zpow_commute_of_finite hI Φ
  have hFr (w : W) : Commute (D.r (Φ ^ d)) (D.r w) := by
    obtain ⟨k, hk⟩ := hgen w
    have hi : (Φ ^ k)⁻¹ * w ∈ deg.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hk, inv_mul_cancel]
    have hw : D.r w = D.r (Φ ^ k) * D.r ((Φ ^ k)⁻¹ * w) := by
      rw [← map_mul, mul_inv_cancel_left]
    rw [hw]
    exact ((Commute.zpow_zpow_self Φ d k).map D.r).mul_right (hcomm _ hi)
  have hFinj : Function.Injective (D.r (Φ ^ d)) := fun x y h ↦ by
    simpa using congrArg (D.r (Φ ^ d)⁻¹) h
  have ht : (deg (Φ ^ d)).toAdd ≠ 0 := by
    rw [map_zpow, toAdd_zpow, smul_eq_mul]
    exact mul_ne_zero hd hΦ
  have hc : ¬IsOfFinOrder ((q : E) ^ (deg (Φ ^ d)).toAdd) := fun h ↦ by
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_zpow_eq_one.mp h
    rw [← zpow_mul] at hpow
    exact hq (isOfFinOrder_iff_zpow_eq_one.mpr ⟨_, mul_ne_zero ht hn, hpow⟩)
  obtain ⟨g, hgT, hgN⟩ := Module.End.exists_mul_eq_smul_mul_of_mul_eq_smul_mul hFinj hc
    (D.r_mul_N (Φ ^ d)) ha
  refine ⟨⟨.mk (LinearMap.GeneralLinearGroup.toLinearEquiv g) fun w ↦ ?_, ?_⟩⟩
  · rw [rescale_r]
    exact (hgT _ (hFr w)).eq
  · rw [rescale_N]
    change (g : Module.End E V) * D.N = (a • D.N) * g
    rw [hgN, smul_mul_assoc]

/-- **`(r, N) ≅ (r, a N)` in characteristic zero.** Over a field of characteristic zero, a raw
Weil–Deligne parameter on a finite-dimensional space with `q ≥ 2`, a nontrivial degree map and
finite inertia image is isomorphic to its rescaling by every `a ≠ 0` (Deligne 1973, proof of
§8.4.3, p. 569). -/
theorem nonempty_iso_rescale_of_two_le [CharZero E] [FiniteDimensional E V]
    (D : WeilDeligneParameter E W V deg q) (hq : 2 ≤ q) (hdeg : ∃ w, deg w ≠ 1)
    (hI : (D.r '' (deg.ker : Set W)).Finite) {a : E} (ha : a ≠ 0) :
    Nonempty (Iso D (D.rescale a)) := by
  refine D.nonempty_iso_rescale (fun h ↦ ?_) hdeg hI ha
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp h
  have hpow' : q ^ n = 1 := by exact_mod_cast hpow
  rcases Nat.pow_eq_one.mp hpow' with h | h <;> omega

end WeilDeligneParameter

end TauCeti

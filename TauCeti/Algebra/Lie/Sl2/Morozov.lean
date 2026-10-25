/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Sl2
public import TauCeti.Algebra.Lie.Sl2.Associative

/-!
# Morozov's lemma

Let `L` be a Lie algebra over a field `K` of characteristic zero, and let `e, h ∈ L` with `ad e`
nilpotent, `⁅h, e⁆ = 2 • e` and `h ∈ [e, L]`. Morozov's lemma says that `(h, e)` extends to an
`sl₂` triple: there is `f` with `⁅e, f⁆ = h` and `⁅h, f⁆ = -2 • f`. Moreover `f` is unique. No
finite-dimensionality or nondegeneracy assumption on `L` is needed.

This is the second half of the Jacobson–Morozov theorem: the first half produces, for an
`ad`-nilpotent `e` in a finite-dimensional Lie algebra with nondegenerate Killing form, an element
`h ∈ [e, L]` with `⁅h, e⁆ = 2 • e`. The hypotheses here are exactly that output.

The key point is that the eigenvalues of `ad h` on the centralizer `ker (ad e)` are natural
numbers. This is proved at the level of operators: if `E`, `H`, `Z` are endomorphisms of a vector
space with `E` nilpotent, `E * Z - Z * E = H` and `H * E - E * H = 2 • E`, then `H` preserves
`ker E`, and on the decreasing filtration `ker E ⊓ range (E ^ k)` the operator `H - k` maps
the `k`-th step into the `(k + 1)`-st. Since the filtration reaches `0` at the nilpotency index
of `E`, the operator `H - a` is bijective on `ker E` for every `a` that is not a natural number.
For the Lie algebra statement take `E = ad e`, `H = ad h` and `Z = ad z` where `h = ⁅e, z⁆`; the
operator form applies equally to the images of `e`, `h`, `z` in any representation in which the
image of `e` is nilpotent.

The individual filtration-step lemmas only require `k + 1` to be nonzero in `K`, and are stated
over fields of arbitrary characteristic with this assumption.

Mathlib's `IsSl2Triple.HasPrimitiveVectorWith.exists_nat` reaches the same kind of conclusion for
a primitive vector of a complete `sl₂` triple acting on a Noetherian module. Here the third element
`f` is what is being constructed and no finiteness is assumed; the nilpotence of `E` replaces both.

## Main results

* `TauCeti.Sl2.exists_eq_natCast_of_apply_eq_smul`: an eigenvalue of `H` on `ker E` is a natural
  number.
* `TauCeti.Sl2.exists_mem_ker_apply_sub_smul_eq`: for `a` not a natural number, `H - a` maps
  `ker E` onto itself.
* `TauCeti.Sl2.apply_sub_smul_mem_ker_inf_range_pow_succ` and its adjoint form
  `TauCeti.lie_sub_smul_mem_ker_inf_range_pow_succ`: `H - k` maps the `k`-th step of the filtration
  `ker E ⊓ range (E ^ k)` into the next one.
* `TauCeti.exists_eq_natCast_of_lie_eq_smul`: an eigenvalue of `ad h` on the centralizer of `e` is
  a natural number.
* `TauCeti.existsUnique_lie_eq_and_lie_eq_neg_two_nsmul`: Morozov's lemma, with uniqueness of the
  third element, and without assuming `h ≠ 0`.
* `TauCeti.existsUnique_isSl2Triple_of_isNilpotent_ad`: the same statement for Mathlib's
  `IsSl2Triple`, when `h ≠ 0`.

## References

* V. V. Morozov, *On a nilpotent element in a semi-simple Lie algebra*, C. R. (Doklady) Acad.
  Sci. URSS (N.S.) **36** (1942), 83–86.
* N. Jacobson, *Lie Algebras*, Interscience, 1962, Chapter III, §11, Lemma 7.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 7–9, Chapter VIII, §11, no. 2.
-/

public section

namespace TauCeti

namespace Sl2

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {E H Z : Module.End K V}

/-- If `E ^ (k + 1)` kills `y` and `k + 1` is nonzero in `K`, then `H - k` sends `E ^ k y`
into the range of `E ^ (k + 1)`. -/
private theorem apply_pow_apply_sub_smul_mem_range_pow_succ (hEZ : E * Z - Z * E = H)
    (hHE : H * E - E * H = 2 • E) {k : ℕ} [NeZero ((k + 1 : ℕ) : K)] {y : V}
    (hy : (E ^ (k + 1)) y = 0) :
    H ((E ^ k) y) - (k : K) • (E ^ k) y ∈ LinearMap.range (E ^ (k + 1)) := by
  refine ⟨(k + 1 : K)⁻¹ • Z y, ?_⟩
  have h₁ := congr($(f_mul_e_pow_succ hEZ hHE k) y)
  have h₂ : H * E ^ k = E ^ k * (H + ((2 * k : ℕ) : Module.End K V)) := by
    rw [h_mul_e_pow hHE, Nat.cast_mul, Nat.cast_ofNat]
  have h₂ := congr($h₂ y)
  simp only [Module.End.mul_apply, hy, map_zero, LinearMap.sub_apply, LinearMap.smul_apply,
    map_add, LinearMap.add_apply, Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul K,
    map_smul] at h₁ h₂
  have hinv : ((k : K) + 1)⁻¹ * ((k : K) + 1) = 1 := by
    simpa using inv_mul_cancel₀ (NeZero.ne ((k + 1 : ℕ) : K))
  rw [map_smul, eq_of_sub_eq_zero h₁.symm, h₂]
  push_cast
  linear_combination (norm := module) hinv • ((E ^ k) (H y) + (k : K) • (E ^ k) y)

/-- If `k + 1` is nonzero in `K`, then `H - k` maps the `k`-th step
`ker E ⊓ range (E ^ k)` of the filtration into the next one. -/
theorem apply_sub_smul_mem_ker_inf_range_pow_succ (hEZ : E * Z - Z * E = H)
    (hHE : H * E - E * H = 2 • E) {k : ℕ} [NeZero ((k + 1 : ℕ) : K)] {c : V}
    (hc : c ∈ LinearMap.ker E ⊓ LinearMap.range (E ^ k)) :
    H c - (k : K) • c ∈ LinearMap.ker E ⊓ LinearMap.range (E ^ (k + 1)) := by
  obtain ⟨hcE, y, rfl⟩ := hc
  replace hcE := LinearMap.mem_ker.mp hcE
  refine ⟨?_, apply_pow_apply_sub_smul_mem_range_pow_succ hEZ hHE ?_⟩
  · have := congr($hHE ((E ^ k) y))
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hcE, map_zero, LinearMap.smul_apply,
      smul_zero, zero_sub, neg_eq_zero] at this
    simp [this, hcE]
  · rw [pow_succ', Module.End.mul_apply, hcE]

variable [CharZero K]

/-- For `a` not a natural number, `H - a` is injective on, and maps onto, every step of the
filtration `ker E ⊓ range (E ^ k)`. This is proved by descending induction on `k`, starting from
the nilpotency index of `E`, where the filtration step is `0`. -/
private theorem injOn_and_surjOn_ker_inf_range_pow (hE : IsNilpotent E)
    (hEZ : E * Z - Z * E = H) (hHE : H * E - E * H = 2 • E) {a : K} (ha : ∀ n : ℕ, a ≠ n)
    (k : ℕ) :
    (∀ c ∈ LinearMap.ker E ⊓ LinearMap.range (E ^ k), H c = a • c → c = 0) ∧
      ∀ w ∈ LinearMap.ker E ⊓ LinearMap.range (E ^ k),
        ∃ c ∈ LinearMap.ker E ⊓ LinearMap.range (E ^ k), H c - a • c = w := by
  obtain ⟨m, hm⟩ := hE
  suffices ∀ d k, m ≤ k + d →
      (∀ c ∈ LinearMap.ker E ⊓ LinearMap.range (E ^ k), H c = a • c → c = 0) ∧
        ∀ w ∈ LinearMap.ker E ⊓ LinearMap.range (E ^ k),
          ∃ c ∈ LinearMap.ker E ⊓ LinearMap.range (E ^ k), H c - a • c = w from
    this m k (Nat.le_add_left m k)
  intro d
  induction d with
  | zero =>
    intro k hk
    have hzero : ∀ c ∈ LinearMap.ker E ⊓ LinearMap.range (E ^ k), c = 0 := by
      rintro c ⟨-, hc⟩
      rw [pow_eq_zero_of_le (by omega) hm, LinearMap.range_zero] at hc
      exact (Submodule.mem_bot K).mp hc
    exact ⟨fun c hc _ => hzero c hc, fun w hw =>
      ⟨0, zero_mem _, by simp [hzero w hw]⟩⟩
  | succ d ih =>
    intro k hk
    obtain ⟨hinj, hsurj⟩ := ih (k + 1) (by omega)
    have hak : a - k ≠ 0 := sub_ne_zero.mpr (ha k)
    refine ⟨fun c hc hHc => hinj c ?_ hHc, fun w hw => ?_⟩
    · have hmem := apply_sub_smul_mem_ker_inf_range_pow_succ hEZ hHE hc
      rw [hHc, ← sub_smul] at hmem
      simpa [smul_smul, inv_mul_cancel₀ hak] using Submodule.smul_mem _ (a - k)⁻¹ hmem
    · obtain ⟨c, hc, hHc⟩ := hsurj _
        (Submodule.smul_mem _ (a - k)⁻¹ (apply_sub_smul_mem_ker_inf_range_pow_succ hEZ hHE hw))
      refine ⟨c - (a - k)⁻¹ • w, sub_mem ⟨hc.1, E.iterateRange.monotone k.le_succ hc.2⟩
        (Submodule.smul_mem _ _ hw), ?_⟩
      have hinv : (a - k)⁻¹ * (a - k) = 1 := inv_mul_cancel₀ hak
      rw [map_sub, map_smul]
      linear_combination (norm := module) hHc + hinv • w

/-- Let `E` be nilpotent, with `E * Z - Z * E = H` and `H * E - E * H = 2 • E`. Then every
eigenvalue of `H` on `ker E` is a natural number. -/
theorem exists_eq_natCast_of_apply_eq_smul (hE : IsNilpotent E) (hEZ : E * Z - Z * E = H)
    (hHE : H * E - E * H = 2 • E) {c : V} (hc : E c = 0) (hc0 : c ≠ 0) {a : K}
    (hHc : H c = a • c) : ∃ n : ℕ, a = n := by
  by_contra! ha
  exact hc0 ((injOn_and_surjOn_ker_inf_range_pow hE hEZ hHE ha 0).1 c ⟨hc, by simp⟩ hHc)

/-- Let `E` be nilpotent, with `E * Z - Z * E = H` and `H * E - E * H = 2 • E`. If `a` is not a
natural number, then `H - a` maps `ker E` onto `ker E`. -/
theorem exists_mem_ker_apply_sub_smul_eq (hE : IsNilpotent E) (hEZ : E * Z - Z * E = H)
    (hHE : H * E - E * H = 2 • E) {a : K} (ha : ∀ n : ℕ, a ≠ n) {w : V}
    (hw : w ∈ LinearMap.ker E) : ∃ c ∈ LinearMap.ker E, H c - a • c = w := by
  obtain ⟨c, hc, hHc⟩ :=
    (injOn_and_surjOn_ker_inf_range_pow hE hEZ hHE ha 0).2 w ⟨hw, by simp⟩
  exact ⟨c, hc.1, hHc⟩

end Sl2

section LieAlgebra

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The operator relations of `ad e`, `ad h` and `ad z` when `h = ⁅e, z⁆` and
`⁅h, e⁆ = 2 • e`. -/
private theorem ad_relations {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L] {h e : L}
    (hhe : ⁅h, e⁆ = 2 • e) {z : L} (hz : ⁅e, z⁆ = h) :
    ad K L e * ad K L z - ad K L z * ad K L e = ad K L h ∧
      ad K L h * ad K L e - ad K L e * ad K L h = 2 • ad K L e := by
  constructor
  · rw [← hz, LieHom.map_lie, Ring.lie_def]
  · rw [← Ring.lie_def, ← LieHom.map_lie, hhe, map_nsmul]

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] {h e : L}

/-- Let `ad e` be nilpotent, `⁅h, e⁆ = 2 • e` and `h ∈ [e, L]`. Then every eigenvalue of `ad h`
on the centralizer of `e` is a natural number. -/
theorem exists_eq_natCast_of_lie_eq_smul (he : IsNilpotent (ad K L e)) (hhe : ⁅h, e⁆ = 2 • e)
    (hh : h ∈ LinearMap.range (ad K L e)) {c : L} (hc : ⁅e, c⁆ = 0) (hc0 : c ≠ 0) {a : K}
    (hhc : ⁅h, c⁆ = a • c) : ∃ n : ℕ, a = n := by
  obtain ⟨z, hz⟩ := hh
  rw [ad_apply] at hz
  obtain ⟨hEZ, hHE⟩ := ad_relations (K := K) hhe hz
  exact Sl2.exists_eq_natCast_of_apply_eq_smul he hEZ hHE (by simpa using hc) hc0
    (by simpa using hhc)

omit [CharZero K] in
/-- Let `⁅h, e⁆ = 2 • e` and `h ∈ [e, L]`. If `k + 1` is nonzero in `K`, then `ad h - k`
maps the `k`-th step `ker (ad e) ⊓ range ((ad e) ^ k)` of the filtration of the centralizer of `e`
into the next one. -/
theorem lie_sub_smul_mem_ker_inf_range_pow_succ (hhe : ⁅h, e⁆ = 2 • e)
    (hh : h ∈ LinearMap.range (ad K L e)) {k : ℕ} [NeZero ((k + 1 : ℕ) : K)] {c : L}
    (hc : c ∈ LinearMap.ker (ad K L e) ⊓ LinearMap.range (ad K L e ^ k)) :
    ⁅h, c⁆ - (k : K) • c ∈ LinearMap.ker (ad K L e) ⊓ LinearMap.range (ad K L e ^ (k + 1)) := by
  obtain ⟨z, hz⟩ := hh
  rw [ad_apply] at hz
  obtain ⟨hEZ, hHE⟩ := ad_relations (K := K) hhe hz
  simpa using Sl2.apply_sub_smul_mem_ker_inf_range_pow_succ hEZ hHE hc

/-- **Morozov's lemma**. Let `ad e` be nilpotent, `⁅h, e⁆ = 2 • e` and `h ∈ [e, L]`, over a field
of characteristic zero. Then there is a unique `f` with `⁅e, f⁆ = h` and `⁅h, f⁆ = -(2 • f)`.
The case `h = 0` is allowed. -/
theorem existsUnique_lie_eq_and_lie_eq_neg_two_nsmul (he : IsNilpotent (ad K L e))
    (hhe : ⁅h, e⁆ = 2 • e) (hh : h ∈ LinearMap.range (ad K L e)) :
    ∃! f : L, ⁅e, f⁆ = h ∧ ⁅h, f⁆ = -(2 • f) := by
  have ⟨z, hz⟩ := hh
  rw [ad_apply] at hz
  obtain ⟨hEZ, hHE⟩ := ad_relations (K := K) hhe hz
  have hneg (n : ℕ) : (-2 : K) ≠ n := by
    exact_mod_cast (by omega : (-2 : ℤ) ≠ n)
  have hw : ⁅h, z⁆ + 2 • z ∈ LinearMap.ker (ad K L e) := by
    rw [LinearMap.mem_ker, ad_apply, lie_add, leibniz_lie, ← lie_skew e h, hhe]
    simp [hz]
  obtain ⟨c, hc, hhc⟩ :=
    Sl2.exists_mem_ker_apply_sub_smul_eq he hEZ hHE hneg hw
  rw [LinearMap.mem_ker, ad_apply] at hc
  rw [ad_apply] at hhc
  refine ⟨z - c, ⟨by rw [lie_sub, hz, hc, sub_zero], ?_⟩, ?_⟩
  · rw [lie_sub]
    linear_combination (norm := module) -hhc
  · rintro f ⟨hf₁, hf₂⟩
    by_contra hne
    obtain ⟨n, hn⟩ := exists_eq_natCast_of_lie_eq_smul he hhe hh (c := f - (z - c))
      (by rw [lie_sub, hf₁, lie_sub, hz, hc, sub_zero, sub_self]) (sub_ne_zero.mpr hne)
      (a := -2) (by rw [lie_sub, lie_sub, hf₂]; linear_combination (norm := module) hhc)
    exact hneg n hn

/-- **Morozov's lemma** for `sl₂` triples. Let `ad e` be nilpotent, `⁅h, e⁆ = 2 • e`, `h ≠ 0` and
`h ∈ [e, L]`, over a field of characteristic zero. Then there is a unique `f` such that `(h, e, f)`
is an `sl₂` triple. -/
theorem existsUnique_isSl2Triple_of_isNilpotent_ad (he : IsNilpotent (ad K L e))
    (hhe : ⁅h, e⁆ = 2 • e) (hh : h ∈ LinearMap.range (ad K L e)) (h0 : h ≠ 0) :
    ∃! f : L, IsSl2Triple h e f := by
  obtain ⟨f, ⟨hef, hhf⟩, huniq⟩ := existsUnique_lie_eq_and_lie_eq_neg_two_nsmul he hhe hh
  exact ⟨f, ⟨h0, hef, hhe, hhf⟩, fun f' hf' => huniq f' ⟨hf'.lie_e_f, hf'.lie_h_f_nsmul⟩⟩

end LieAlgebra

end TauCeti

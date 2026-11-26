/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import TauCeti.RingTheory.StableRange
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing

/-!
# Relative unimodular vectors and relative stable range

Let `A` be a commutative ring and `I` an ideal of `A`. A **relative unimodular vector at level
`I`** is a unimodular vector `v : ι → A` congruent modulo `I` to a standard basis vector `e_{i₀}`:
`v i₀ ≡ 1` and `v i ≡ 0` modulo `I` for `i ≠ i₀`. These vectors, written `Um(A, I)`, form the set
`Ideal.relUnimodular I i₀`. At the zero ideal the only one is `e_{i₀}`, and at the unit ideal they
are all unimodular vectors.

The congruence subgroup `GL(A, I)`, the kernel of reduction `GL(A) → GL(A ⧸ I)`, acts on column
vectors by `g • v = g *ᵥ v` and preserves `Um(A, I)`. These vectors and their orbits under
congruence and relative elementary matrices control the finite-rank stability theorems for the
relative groups `SLₙ(A, I)` of Bass, Milnor and Serre.

The bound `HasStableRangeLE R s` has a relative form, over any ring `R` and two-sided ideal `I`.
If `(a₀, …, aₘ)` is unimodular, `aₘ ∈ I` and `m ≥ s`, then the shortening `(aᵢ + aₘ cᵢ)ᵢ<ₘ` can
be achieved with all `cᵢ ∈ I`. If `∑ aᵢ bᵢ = 1`, replacing `aₘ` by `aₘ bₘ aₘ` keeps the row
unimodular; shortening that row with some `dᵢ` gives `cᵢ = bₘ aₘ dᵢ ∈ I`. Over a commutative ring
this is the classical device of replacing `aₘ` by a multiple of `aₘ²`. For a vector of `Um(A, I)`
the shortened vector lies again in `Um(A, I)`.

In rank two, `SL₂(A, I)` acts transitively on `Um(A, I)` over every commutative ring: if
`a x + b y = 1` with `a ≡ 1` and `b ≡ 0` modulo `I`, then
`[[a, -y (1 - a)], [b, x + y b]]` has determinant `1`, is congruent to `1` modulo `I`, and has
first column `(a, b)`.

## Main definitions

* `Ideal.relUnimodular I i₀`: the unimodular vectors congruent to `e_{i₀}` modulo `I`.

## Main results

* `Ideal.mem_relUnimodular_iff_comp`: membership through the reduction map `A → A ⧸ I`.
* `Ideal.relUnimodular_bot`, `Ideal.relUnimodular_top`: the levels `0` and `A`.
* `Ideal.smul_mem_relUnimodular_iff`: matrices congruent to `1` modulo `I` preserve `Um(A, I)`.
* `TauCeti.HasStableRangeLE.exists_isUnimodular_add_mul_mem`: relative shortening over any ring,
  with coefficients in a two-sided ideal `I`.
* `TauCeti.HasStableRangeLE.exists_add_mul_mem_relUnimodular`: shortening `Um(A, I)` in rank
  `m + 1` to `Um(A, I)` in rank `m`, for `m ≥ s`.
* `Ideal.exists_specialLinearGroup_mulVec_single_eq`: every vector of `Um(A, I)` of length two is
  the first column of a matrix of `SL₂(A)` congruent to `1` modulo `I`.
* `Ideal.exists_specialLinearGroup_mulVec_eq`: `SL₂(A, I)` acts transitively on `Um(A, I)` in
  rank two.

## References

* H. Bass, J. Milnor, J.-P. Serre, *Solution of the congruence subgroup problem for `SLₙ`
  (`n ≥ 3`) and `Sp₂ₙ` (`n ≥ 2`)*, Publ. Math. IHÉS 33 (1967), §7, Lemma 7.3 and
  Theorems 7.4–7.5.
* H. Bass, *K-theory and stable algebra*, Publ. Math. IHÉS 22 (1964), §4.
-/

public section

open Matrix

namespace Ideal

variable {A ι : Type*} [CommRing A] [DecidableEq ι] (I : Ideal A) (i₀ : ι)

/-- The **relative unimodular vectors** `Um(A, I)` at level `I`: the unimodular vectors
`v : ι → A` congruent modulo `I` to the standard basis vector `e_{i₀}`, that is `v i₀ - 1 ∈ I` and
`v i ∈ I` for `i ≠ i₀`. -/
def relUnimodular : Set (ι → A) :=
  {v | Module.IsUnimodular A v ∧ ∀ i, v i - (Pi.single i₀ 1 : ι → A) i ∈ I}

variable {I i₀}

/-- Membership in `Um(A, I)`: unimodularity and the congruence `v ≡ e_{i₀}` entrywise modulo
`I`. -/
@[simp]
theorem mem_relUnimodular_iff {v : ι → A} :
    v ∈ I.relUnimodular i₀ ↔ Module.IsUnimodular A v ∧ ∀ i, v i - (Pi.single i₀ 1 : ι → A) i ∈ I :=
  Iff.rfl

/-- A vector lies in `Um(A, I)` exactly when it is unimodular and reduces to `e_{i₀}` modulo
`I`. -/
theorem mem_relUnimodular_iff_comp {v : ι → A} :
    v ∈ I.relUnimodular i₀ ↔
      Module.IsUnimodular A v ∧ Ideal.Quotient.mk I ∘ v = Pi.single i₀ 1 := by
  rw [mem_relUnimodular_iff, funext_iff]
  refine and_congr_right fun _ ↦ forall_congr' fun i ↦ ?_
  have hsingle :
      (Pi.single i₀ 1 : ι → A ⧸ I) i = Ideal.Quotient.mk I ((Pi.single i₀ 1 : ι → A) i) := by
    by_cases h : i = i₀ <;> simp [h]
  rw [Function.comp_apply, hsingle, Ideal.Quotient.eq]

/-- The standard basis vector `e_{i₀}` lies in `Um(A, I)` at every level. -/
theorem single_mem_relUnimodular : (Pi.single i₀ 1 : ι → A) ∈ I.relUnimodular i₀ :=
  ⟨IsUnit.isUnimodular_pi (i := i₀) (by simp), fun i ↦ by simp⟩

variable (i₀) in
/-- At the zero ideal the only relative unimodular vector is `e_{i₀}`. -/
@[simp]
theorem relUnimodular_bot : (⊥ : Ideal A).relUnimodular i₀ = {Pi.single i₀ 1} := by
  ext v
  refine ⟨fun hv ↦ funext fun i ↦ sub_eq_zero.mp ((Submodule.mem_bot A).mp (hv.2 i)), ?_⟩
  rintro rfl
  exact single_mem_relUnimodular

variable (i₀) in
/-- At the unit ideal every unimodular vector is relative unimodular. -/
@[simp]
theorem relUnimodular_top : (⊤ : Ideal A).relUnimodular i₀ = {v | Module.IsUnimodular A v} := by
  ext v
  simp [mem_relUnimodular_iff]

/-- Relative unimodular vectors at a smaller level are relative unimodular at a larger one. -/
theorem relUnimodular_mono {J : Ideal A} (h : I ≤ J) : I.relUnimodular i₀ ⊆ J.relUnimodular i₀ :=
  fun _ hv ↦ ⟨hv.1, fun i ↦ h (hv.2 i)⟩

/-- A ring homomorphism carrying `I` into `J` carries `Um(A, I)` into `Um(B, J)`. -/
theorem comp_mem_relUnimodular [Finite ι] {B : Type*} [CommRing B] {J : Ideal B} (f : A →+* B)
    (hf : I.map f ≤ J) {v : ι → A} (hv : v ∈ I.relUnimodular i₀) :
    f ∘ v ∈ J.relUnimodular i₀ := by
  refine ⟨hv.1.ringHom_comp f, fun i ↦ hf ?_⟩
  simpa [Pi.apply_single (fun _ ↦ f), map_sub] using Ideal.mem_map_of_mem f (hv.2 i)

/-- An invertible matrix congruent to `1` modulo `I` preserves `Um(A, I)`. -/
theorem smul_mem_relUnimodular [Fintype ι] {g : GL ι A}
    (hg : GeneralLinearGroup.map (Ideal.Quotient.mk I) g = 1) {v : ι → A}
    (hv : v ∈ I.relUnimodular i₀) : g • v ∈ I.relUnimodular i₀ := by
  rw [mem_relUnimodular_iff_comp] at hv ⊢
  rw [Units.smul_def, smul_eq_mulVec]
  refine ⟨(GeneralLinearGroup.isUnimodular_mulVec_iff g).mpr hv.1, ?_⟩
  have hgm : (g : Matrix ι ι A).map (Ideal.Quotient.mk I) = 1 := by
    simpa using congrArg Units.val hg
  ext i
  rw [Function.comp_apply, RingHom.map_mulVec, hgm, hv.2, one_mulVec]

/-- The congruence subgroup `GL(A, I)` acts on `Um(A, I)`: for `g` congruent to `1` modulo `I`,
`g • v` lies in `Um(A, I)` exactly when `v` does. -/
theorem smul_mem_relUnimodular_iff [Fintype ι] {g : GL ι A}
    (hg : GeneralLinearGroup.map (Ideal.Quotient.mk I) g = 1) {v : ι → A} :
    g • v ∈ I.relUnimodular i₀ ↔ v ∈ I.relUnimodular i₀ := by
  refine ⟨fun h ↦ ?_, smul_mem_relUnimodular hg⟩
  have hg' : GeneralLinearGroup.map (Ideal.Quotient.mk I) g⁻¹ = 1 := by rw [map_inv, hg, inv_one]
  simpa using smul_mem_relUnimodular hg' h

/-! ## Rank two: Bézout completion -/

/-- **Bézout completion at level `I`.** Every vector of `Um(A, I)` of length two is the first column
of a matrix of `SL₂(A)` congruent to `1` modulo `I`: if `a x + b y = 1` with `a ≡ 1` and `b ≡ 0`
modulo `I`, take `[[a, -y (1 - a)], [b, x + y b]]`. -/
theorem exists_specialLinearGroup_mulVec_single_eq {v : Fin 2 → A}
    (hv : v ∈ I.relUnimodular 0) :
    ∃ g : SpecialLinearGroup (Fin 2) A, SpecialLinearGroup.map (Ideal.Quotient.mk I) g = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) A) *ᵥ Pi.single 0 1 = v := by
  obtain ⟨b, hb⟩ := TauCeti.Module.isUnimodular_pi_iff.mp hv.1
  rw [Fin.sum_univ_two] at hb
  have h0 : v 0 - 1 ∈ I := by simpa using hv.2 0
  have h1 : v 1 ∈ I := by simpa using hv.2 1
  let M : Matrix (Fin 2) (Fin 2) A := !![v 0, -(b 1 * (1 - v 0)); v 1, b 0 + b 1 * v 1]
  have hM : M.det = 1 := by
    rw [det_fin_two_of]
    linear_combination hb
  let g : SpecialLinearGroup (Fin 2) A := ⟨M, hM⟩
  have hg : (g : Matrix (Fin 2) (Fin 2) A) = M := rfl
  refine ⟨g, ?_, ?_⟩
  · -- Modulo `I` the matrix is `[[1, 0], [0, x]]`, and `x ≡ 1` because `a x + b y = 1`.
    have hq0 : Ideal.Quotient.mk I (v 0) = 1 := by
      rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
      exact h0
    have hq1 : Ideal.Quotient.mk I (v 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h1
    have hqb : Ideal.Quotient.mk I (b 0) = 1 := by
      simpa [hq0, hq1] using congrArg (Ideal.Quotient.mk I) hb
    ext i j
    rw [SpecialLinearGroup.map_apply_coe, hg]
    fin_cases i <;> fin_cases j <;> simp [M, hq0, hq1, hqb]
  · ext i
    rw [hg]
    fin_cases i <;> simp [M]

/-- **Rank-two transitivity.** `SL₂(A, I)`, hence `GL₂(A, I)`, acts transitively on the vectors of
`Um(A, I)` of length two. -/
theorem exists_specialLinearGroup_mulVec_eq {v w : Fin 2 → A} (hv : v ∈ I.relUnimodular 0)
    (hw : w ∈ I.relUnimodular 0) :
    ∃ g : SpecialLinearGroup (Fin 2) A, SpecialLinearGroup.map (Ideal.Quotient.mk I) g = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) A) *ᵥ v = w := by
  obtain ⟨g, hg, rfl⟩ := exists_specialLinearGroup_mulVec_single_eq hv
  obtain ⟨h, hh, rfl⟩ := exists_specialLinearGroup_mulVec_single_eq hw
  refine ⟨h * g⁻¹, by rw [map_mul, map_inv, hg, hh, inv_one, mul_one], ?_⟩
  rw [mulVec_mulVec, ← SpecialLinearGroup.coe_mul, inv_mul_cancel_right]

end Ideal

/-! ## Relative stable range -/

namespace TauCeti

/-- **Relative shortening.** Over a ring of stable range at most `s`, a unimodular row
`(a₀, …, aₘ)` with `m ≥ s` and last coordinate in a two-sided ideal `I` can be shortened to a
unimodular row `(aᵢ + aₘ cᵢ)ᵢ<ₘ` with all `cᵢ ∈ I`. -/
theorem HasStableRangeLE.exists_isUnimodular_add_mul_mem {R : Type*} [Ring R] {s m : ℕ}
    (hR : HasStableRangeLE R s) (hm : s ≤ m) {I : Ideal R} [I.IsTwoSided]
    {a : Fin (m + 1) → R} (ha : Module.IsUnimodular R a) (hI : a (Fin.last m) ∈ I) :
    ∃ c : Fin m → R, (∀ i, c i ∈ I) ∧
      Module.IsUnimodular R (fun i ↦ a (Fin.castSucc i) + a (Fin.last m) * c i) := by
  obtain ⟨b, hb⟩ := TauCeti.Module.isUnimodular_pi_iff.mp ha
  rw [Fin.sum_univ_castSucc] at hb
  set d := a (Fin.last m)
  set e := b (Fin.last m)
  -- Replacing the last coordinate `d` by `d e d` keeps the row unimodular: if `x + d e = 1`, then
  -- `x (1 + d e) + d e d e = (1 - d e) (1 + d e) + d e d e = 1`.
  have hu : Module.IsUnimodular R
      (Fin.snoc (α := fun _ ↦ R) (fun i ↦ a (Fin.castSucc i)) (d * e * d)) := by
    refine TauCeti.Module.isUnimodular_pi_iff.mpr
      ⟨Fin.snoc (α := fun _ ↦ R) (fun i ↦ b (Fin.castSucc i) * (1 + d * e)) e, ?_⟩
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, ← mul_assoc, ← Finset.sum_mul,
      eq_sub_of_add_eq hb]
    noncomm_ring
  -- Shorten that row: `d e d cᵢ = d (e d cᵢ)` and `e d cᵢ ∈ I`.
  obtain ⟨c, hc⟩ := hasStableRangeLE_iff_forall_le.mp hR hm _ hu
  refine ⟨fun i ↦ e * d * c i, fun i ↦ I.mul_mem_right _ (I.mul_mem_left _ hI), ?_⟩
  simpa [mul_assoc] using hc

variable {A : Type*} [CommRing A]

/-- **Shortening relative unimodular vectors.** Over a commutative ring of stable range at most
`s`, every `v ∈ Um(A, I)` of length `m + 1` with `m ≥ s` shortens to a vector
`(vᵢ + vₘ cᵢ)ᵢ<ₘ` of `Um(A, I)` of length `m`, with all `cᵢ ∈ I`. -/
theorem HasStableRangeLE.exists_add_mul_mem_relUnimodular {s m : ℕ} [NeZero m]
    (hR : HasStableRangeLE A s) (hm : s ≤ m) {I : Ideal A} {v : Fin (m + 1) → A}
    (hv : v ∈ I.relUnimodular 0) :
    ∃ c : Fin m → A, (∀ i, c i ∈ I) ∧
      (fun i ↦ v (Fin.castSucc i) + v (Fin.last m) * c i) ∈ I.relUnimodular 0 := by
  have hlast : v (Fin.last m) ∈ I := by
    simpa [Pi.single_apply, Fin.last_eq_zero_iff, NeZero.ne m] using hv.2 (Fin.last m)
  obtain ⟨c, hcI, hc⟩ := hR.exists_isUnimodular_add_mul_mem hm hv.1 hlast
  refine ⟨c, hcI, hc, fun i ↦ ?_⟩
  have hs :
      (Pi.single 0 1 : Fin (m + 1) → A) (Fin.castSucc i) = (Pi.single 0 1 : Fin m → A) i := by
    rcases eq_or_ne i 0 with rfl | h
    · simp [Fin.castSucc_zero]
    · simp [h]
  rw [← hs, add_sub_right_comm]
  exact I.add_mem (hv.2 _) (I.mul_mem_right _ hlast)

end TauCeti

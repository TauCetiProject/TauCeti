/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.GroupTheory.Torsion
public import TauCeti.Algebra.Group.ElementaryTwoQuotient.Basic

/-!
# Two-power torsion images in `A / A²` and the two-adic power criterion

For a commutative group `A` with maximal elementary-2 quotient `B = A / A²`, this file studies the
increasing filtration `B_t ⊆ B` by the images of the `2 ^ t`-torsion subgroups
`A[2 ^ t] = {a | a ^ 2 ^ t = 1}`, and the **obstruction threshold** `t_A(b)` of an element `b`: the
least `t` with the class of `b` in `B_t`. It answers a concrete question about power equations:
when `A` is torsion and `r ≠ 0`, the equation `h ^ (2 * r) = b ^ r` has a solution `h ∈ A` exactly
when `t_A(b) ≤ v₂(r)`, where `v₂ = multiplicity 2` is the `2`-adic valuation. Equivalently, when
`A` is torsion and `q > 1` is odd, the equation `h ^ (q - 1) = b ^ ((q - 1) / 2)` is solvable
exactly when `t_A(b) < v₂(q - 1)`.

Such equations describe the elements of a fiber of a finite central extension fixed by a `q`-th
power map (Wood, *Nonabelian Cohen–Lenstra moments*, Duke Math. J. 168 (2019), §4.1,
Proposition 4.1 and equation (6)); the criterion turns their solvability into a statement about
the square class of `b` and the `2`-adic valuation of `q - 1`.

The key steps are elementary. The equation `h ^ (2 * r) = b ^ r` is solvable iff `b` is a square
times an `r`-torsion element. For `r = 2 ^ k * m` with `m` odd, an `r`-torsion element `a` has
the same square class as the `2 ^ k`-torsion element `a ^ m`, so the image of `A[r]` in `B` is
`B_{v₂(r)}`. In a torsion group every class lies in some `B_t`, so the threshold is a genuine
minimum.

## Main definitions

* `TauCeti.torsionImageFiltration A t`: the `𝔽₂`-subspace `B_t` of `A / A²`, the image of
  `A[2 ^ t]`.
* `TauCeti.obstructionThreshold b`: the least `t` with the class of `b` in `B_t`.

## Main results

* `TauCeti.exists_pow_two_mul_eq_pow_iff`: `h ^ (2 * r) = b ^ r` is solvable iff `b` is a square
  times an `r`-torsion element.
* `TauCeti.mem_torsionImageFiltration_multiplicity_iff`: the image of `A[r]` is `B_{v₂(r)}`.
* `TauCeti.torsionImageFiltration_zero`, `TauCeti.torsionImageFiltration_mono`,
  `TauCeti.torsionImageFiltration_eq_top`: `B_0 = 0`, the filtration increases, and it exhausts
  `B` once `2 ^ e` kills every element of `2`-power order.
* `TauCeti.obstructionThreshold_le_iff`: in a torsion group, `t_A(b) ≤ t` iff the class of `b`
  lies in `B_t`.
* `TauCeti.obstructionThreshold_eq_zero_of_isSquare`: in any commutative group, squares have
  threshold `0`.
* `TauCeti.exists_pow_two_mul_eq_pow_iff_obstructionThreshold_le` and
  `TauCeti.exists_pow_sub_one_eq_pow_iff_obstructionThreshold_lt`: the two-adic solvability
  criterion.
* `TauCeti.torsionImageFiltration_map_le`,
  `TauCeti.torsionImageFiltration_map_elementaryTwoQuotientCongr`,
  `TauCeti.obstructionThreshold_map_le` and `TauCeti.obstructionThreshold_congr`: the filtration
  and the threshold are compatible with homomorphisms and invariant under isomorphisms.
* `TauCeti.obstructionThreshold_pi`: the threshold of a family is the maximum of the thresholds
  of its coordinates.
* `TauCeti.torsionImageFiltration_eq_top_of_forall_pow_eq_one`,
  `TauCeti.torsionImageFiltration_eq_bot_of_isCyclic` and
  `TauCeti.obstructionThreshold_eq_of_forall_mem_zpowers`: for a cyclic group of order `2 ^ e`,
  `B_t = 0` for `t < e` and `B_t = A / A²` for `t ≥ e`, and a generator has threshold `e`.
-/

public section

namespace TauCeti

section General

variable {A : Type*} [CommGroup A]

/-- **Square times torsion.** For a commutative group `A`, the power equation
`h ^ (2 * r) = b ^ r` has a solution `h` exactly when `b` is a square times an element killed by
`r`. At `r = 0` both sides hold for every `b`. -/
theorem exists_pow_two_mul_eq_pow_iff (b : A) (r : ℕ) :
    (∃ h : A, h ^ (2 * r) = b ^ r) ↔ ∃ s a : A, a ^ r = 1 ∧ b = s ^ 2 * a := by
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h, b / h ^ 2, ?_, by rw [mul_div_cancel]⟩
    rw [div_pow, ← pow_mul, hh, div_self']
  · rintro ⟨s, a, ha, rfl⟩
    exact ⟨s, by rw [mul_pow, ha, mul_one, pow_mul]⟩

variable (A) in
/-- **The torsion-image filtration** `B_t` of the maximal elementary-2 quotient `B = A / A²`: the
image in `B` of the `2 ^ t`-torsion subgroup `A[2 ^ t] = {a | a ^ 2 ^ t = 1}`, as an
`𝔽₂`-subspace. It is `0` at `t = 0` and increases with `t`. -/
def torsionImageFiltration (t : ℕ) : Submodule (ZMod 2) (ElementaryTwoQuotient A) where
  carrier := {x | ∃ a : A, a ^ 2 ^ t = 1 ∧ elementaryTwoQuotientMk a = x}
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, by rw [mul_pow, ha, hb, mul_one], elementaryTwoQuotientMk_mul a b⟩
  zero_mem' := ⟨1, one_pow _, elementaryTwoQuotientMk_one⟩
  smul_mem' := by
    rintro c _ ⟨a, ha, rfl⟩
    refine ⟨a ^ c.val, by rw [← pow_mul, mul_comm, pow_mul, ha, one_pow], ?_⟩
    rw [elementaryTwoQuotientMk_pow, ← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_zmod_val]

/-- Membership in `B_t`: the classes of the elements killed by `2 ^ t`. -/
@[simp] theorem mem_torsionImageFiltration_iff {t : ℕ} {x : ElementaryTwoQuotient A} :
    x ∈ torsionImageFiltration A t ↔ ∃ a : A, a ^ 2 ^ t = 1 ∧ elementaryTwoQuotientMk a = x :=
  Iff.rfl

/-- The class of an element killed by `2 ^ t` lies in `B_t`. -/
theorem elementaryTwoQuotientMk_mem_torsionImageFiltration {t : ℕ} {a : A} (ha : a ^ 2 ^ t = 1) :
    elementaryTwoQuotientMk a ∈ torsionImageFiltration A t :=
  ⟨a, ha, rfl⟩

/-- The first step of the filtration is zero: only `1` is killed by `2 ^ 0 = 1`. -/
@[simp] theorem torsionImageFiltration_zero : torsionImageFiltration A 0 = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 ?_
  rintro _ ⟨a, ha, rfl⟩
  rw [pow_zero, pow_one] at ha
  rw [ha, elementaryTwoQuotientMk_one]

/-- The torsion-image filtration is increasing. -/
theorem torsionImageFiltration_mono : Monotone (torsionImageFiltration A) := by
  intro t u htu _ ⟨a, ha, hx⟩
  refine ⟨a, ?_, hx⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htu
  rw [pow_add, pow_mul, ha, one_pow]

/-- **The image of `A[r]` is `B_{v₂(r)}`.** For `r ≠ 0`, a class of `A / A²` lies in the
filtration step indexed by the `2`-adic valuation of `r` exactly when it is the class of an
element killed by `r`: the odd part of `r` contributes no new square classes. -/
theorem mem_torsionImageFiltration_multiplicity_iff {r : ℕ} (hr : r ≠ 0)
    {x : ElementaryTwoQuotient A} :
    x ∈ torsionImageFiltration A (multiplicity 2 r) ↔
      ∃ a : A, a ^ r = 1 ∧ elementaryTwoQuotientMk a = x := by
  -- Write `r = 2 ^ k * m` with `k = v₂(r)` and `m` odd.
  have hdecomp := Nat.pow_multiplicity_mul_divMaxPow 2 r
  obtain ⟨j, hj⟩ : Odd (r.divMaxPow 2) :=
    Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 (Nat.not_dvd_divMaxPow one_lt_two hr))
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, by rw [← hdecomp, pow_mul, ha, one_pow], rfl⟩
  · rintro ⟨a, ha, rfl⟩
    -- The `2 ^ k`-torsion element `a ^ m` has the square class of `a`.
    refine ⟨a ^ r.divMaxPow 2, by rw [← pow_mul, mul_comm, hdecomp, ha], ?_⟩
    rw [elementaryTwoQuotientMk_eq_iff, hj, pow_succ, mul_div_cancel_right, pow_mul]
    exact IsSquare.pow j (IsSquare.sq a)

/-- **The two-adic form of square times torsion.** For `r ≠ 0`, the power equation
`h ^ (2 * r) = b ^ r` is solvable exactly when the square class of `b` lies in `B_{v₂(r)}`. -/
theorem exists_pow_two_mul_eq_pow_iff_mem_torsionImageFiltration (b : A) {r : ℕ} (hr : r ≠ 0) :
    (∃ h : A, h ^ (2 * r) = b ^ r) ↔
      elementaryTwoQuotientMk b ∈ torsionImageFiltration A (multiplicity 2 r) := by
  rw [exists_pow_two_mul_eq_pow_iff, mem_torsionImageFiltration_multiplicity_iff hr]
  constructor
  · rintro ⟨s, a, ha, rfl⟩
    exact ⟨a, ha, by rw [elementaryTwoQuotientMk_mul,
      (elementaryTwoQuotientMk_eq_zero_iff _).2 (IsSquare.sq s), zero_add]⟩
  · rintro ⟨a, ha, hab⟩
    obtain ⟨s, hs⟩ := (elementaryTwoQuotientMk_eq_iff b a).1 hab.symm
    exact ⟨s, a, ha, by rw [pow_two, ← hs, div_mul_cancel]⟩

/-- **Membership in `B_t` as a power equation.** The square class of `b` lies in `B_t` exactly
when `b ^ 2 ^ t` is a `2 ^ (t + 1)`-th power. -/
theorem elementaryTwoQuotientMk_mem_torsionImageFiltration_iff (b : A) (t : ℕ) :
    elementaryTwoQuotientMk b ∈ torsionImageFiltration A t ↔
      ∃ h : A, h ^ 2 ^ (t + 1) = b ^ 2 ^ t := by
  have h := exists_pow_two_mul_eq_pow_iff_mem_torsionImageFiltration b
    (pow_ne_zero t two_ne_zero)
  rw [multiplicity_base_pow one_lt_two, ← pow_succ'] at h
  exact h.symm

/-- In a torsion group every square class lies in some step of the filtration: the class of `b`
lies in `B_{v₂(n)}` for the order `n` of `b`. -/
theorem exists_elementaryTwoQuotientMk_mem_torsionImageFiltration (hA : IsMulTorsion A) (b : A) :
    ∃ t, elementaryTwoQuotientMk b ∈ torsionImageFiltration A t :=
  ⟨_, (mem_torsionImageFiltration_multiplicity_iff (hA b).orderOf_pos.ne').2
    ⟨b, pow_orderOf_eq_one b, rfl⟩⟩

/-- **Exhaustion.** In a torsion group, if `2 ^ e` kills every element of `2`-power order, then
`B_e` is all of `A / A²`. -/
theorem torsionImageFiltration_eq_top (hA : IsMulTorsion A) {e : ℕ}
    (he : ∀ (a : A) (k : ℕ), a ^ 2 ^ k = 1 → a ^ 2 ^ e = 1) :
    torsionImageFiltration A e = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ ?_
  obtain ⟨b, rfl⟩ := elementaryTwoQuotientMk_surjective x
  obtain ⟨t, a, ha, hab⟩ := exists_elementaryTwoQuotientMk_mem_torsionImageFiltration hA b
  exact ⟨a, he a t ha, hab⟩

/-- **The two-primary obstruction threshold** `t_A(b)` of an element `b` of a commutative group:
the least `t` such that the square class of `b` lies in the torsion-image filtration step `B_t`.
In a torsion group this minimum exists (`obstructionThreshold_le_iff`); if no `B_t` contains the
class of `b`, the value is the junk value `0`. -/
noncomputable def obstructionThreshold (b : A) : ℕ :=
  sInf {t | elementaryTwoQuotientMk b ∈ torsionImageFiltration A t}

/-- If the square class of `b` lies in `B_t`, then `t_A(b) ≤ t`. -/
theorem obstructionThreshold_le_of_mem {b : A} {t : ℕ}
    (h : elementaryTwoQuotientMk b ∈ torsionImageFiltration A t) : obstructionThreshold b ≤ t :=
  Nat.sInf_le h

/-- In a torsion group, `t_A(b) ≤ t` exactly when the square class of `b` lies in `B_t`. -/
theorem obstructionThreshold_le_iff (hA : IsMulTorsion A) {b : A} {t : ℕ} :
    obstructionThreshold b ≤ t ↔ elementaryTwoQuotientMk b ∈ torsionImageFiltration A t := by
  refine ⟨fun h ↦ torsionImageFiltration_mono h ?_, obstructionThreshold_le_of_mem⟩
  have hne : {t | elementaryTwoQuotientMk b ∈ torsionImageFiltration A t}.Nonempty :=
    exists_elementaryTwoQuotientMk_mem_torsionImageFiltration hA b
  exact Nat.sInf_mem hne

/-- In a torsion group, the square class of `b` lies in `B_{t_A(b)}`. -/
theorem elementaryTwoQuotientMk_mem_torsionImageFiltration_obstructionThreshold
    (hA : IsMulTorsion A) (b : A) :
    elementaryTwoQuotientMk b ∈ torsionImageFiltration A (obstructionThreshold b) :=
  (obstructionThreshold_le_iff hA).1 le_rfl

/-- The threshold depends only on the square class. -/
theorem obstructionThreshold_eq_of_elementaryTwoQuotientMk_eq {b c : A}
    (h : elementaryTwoQuotientMk b = elementaryTwoQuotientMk c) :
    obstructionThreshold b = obstructionThreshold c := by
  rw [obstructionThreshold, obstructionThreshold, h]

/-- Squares have threshold `0`: their square class is `0 ∈ B_0`. -/
theorem obstructionThreshold_eq_zero_of_isSquare {b : A} (hb : IsSquare b) :
    obstructionThreshold b = 0 :=
  Nat.le_zero.1 (obstructionThreshold_le_of_mem
    ((elementaryTwoQuotientMk_eq_zero_iff b).2 hb ▸ Submodule.zero_mem _))

/-- The identity has threshold `0`. -/
@[simp] theorem obstructionThreshold_one : obstructionThreshold (1 : A) = 0 :=
  obstructionThreshold_eq_zero_of_isSquare IsSquare.one

/-- In a torsion group, the threshold vanishes exactly on squares. -/
theorem obstructionThreshold_eq_zero_iff (hA : IsMulTorsion A) {b : A} :
    obstructionThreshold b = 0 ↔ IsSquare b := by
  rw [← Nat.le_zero, obstructionThreshold_le_iff hA, torsionImageFiltration_zero,
    Submodule.mem_bot, elementaryTwoQuotientMk_eq_zero_iff]

/-- If `2 ^ e` kills every element of `2`-power order, then every threshold is at most `e`. -/
theorem obstructionThreshold_le {e : ℕ} (he : ∀ (a : A) (k : ℕ), a ^ 2 ^ k = 1 → a ^ 2 ^ e = 1)
    (b : A) : obstructionThreshold b ≤ e := by
  by_cases h : ∃ t, elementaryTwoQuotientMk b ∈ torsionImageFiltration A t
  · obtain ⟨t, a, ha, hab⟩ := h
    exact obstructionThreshold_le_of_mem ⟨a, he a t ha, hab⟩
  · -- The defining set is empty, so the threshold takes its junk value `0`.
    rw [obstructionThreshold, Nat.sInf_eq_zero.2
      (Or.inr (Set.eq_empty_iff_forall_notMem.2 fun t ht ↦ h ⟨t, ht⟩))]
    exact Nat.zero_le e

/-- **The two-adic solvability criterion.** In a torsion commutative group, for `r ≠ 0` the
power equation `h ^ (2 * r) = b ^ r` is solvable exactly when `t_A(b) ≤ v₂(r)`. -/
theorem exists_pow_two_mul_eq_pow_iff_obstructionThreshold_le (hA : IsMulTorsion A) (b : A)
    {r : ℕ} (hr : r ≠ 0) :
    (∃ h : A, h ^ (2 * r) = b ^ r) ↔ obstructionThreshold b ≤ multiplicity 2 r := by
  rw [exists_pow_two_mul_eq_pow_iff_mem_torsionImageFiltration b hr, obstructionThreshold_le_iff hA]

/-- **Two-adic survival.** In a torsion commutative group, for an odd `q > 1` the power equation
`h ^ (q - 1) = b ^ ((q - 1) / 2)` is solvable exactly when `t_A(b) < v₂(q - 1)`, that is,
`v₂(q - 1) ≥ t_A(b) + 1`. -/
theorem exists_pow_sub_one_eq_pow_iff_obstructionThreshold_lt (hA : IsMulTorsion A) (b : A)
    {q : ℕ} (hq : Odd q) (hq1 : 1 < q) :
    (∃ h : A, h ^ (q - 1) = b ^ ((q - 1) / 2)) ↔
      obstructionThreshold b < multiplicity 2 (q - 1) := by
  obtain ⟨r, rfl⟩ := hq
  have hr : r ≠ 0 := by rintro rfl; simp at hq1
  rw [Nat.add_sub_cancel, Nat.mul_div_cancel_left r two_pos,
    multiplicity_base_mul one_lt_two hr, Nat.lt_succ_iff,
    exists_pow_two_mul_eq_pow_iff_obstructionThreshold_le hA b hr]

end General

section Functoriality

variable {G H : Type*} [CommGroup G] [CommGroup H]

/-- A homomorphism maps the filtration step `B_t` of `G` into the step `B_t` of `H`. -/
theorem torsionImageFiltration_map_le (f : G →* H) (t : ℕ) :
    (torsionImageFiltration G t).map (elementaryTwoQuotientMap f) ≤ torsionImageFiltration H t := by
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  exact ⟨f a, by rw [← map_pow, ha, map_one], (elementaryTwoQuotientMap_mk f a).symm⟩

/-- A multiplicative equivalence identifies the torsion-image filtrations. -/
@[simp] theorem torsionImageFiltration_map_elementaryTwoQuotientCongr (e : G ≃* H) (t : ℕ) :
    (torsionImageFiltration G t).map
        (elementaryTwoQuotientCongr e : ElementaryTwoQuotient G →ₗ[ZMod 2] _) =
      torsionImageFiltration H t := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨e a, by rw [← map_pow, ha, map_one],
      by rw [LinearEquiv.coe_coe, elementaryTwoQuotientCongr_mk]⟩
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨_, ⟨e.symm a, by rw [← map_pow, ha, map_one], rfl⟩, ?_⟩
    rw [LinearEquiv.coe_coe, elementaryTwoQuotientCongr_mk, MulEquiv.apply_symm_apply]

/-- In a torsion group, a homomorphism does not increase the obstruction threshold. -/
theorem obstructionThreshold_map_le (hG : IsMulTorsion G) (f : G →* H) (b : G) :
    obstructionThreshold (f b) ≤ obstructionThreshold b := by
  refine obstructionThreshold_le_of_mem (torsionImageFiltration_map_le f _ ?_)
  rw [← elementaryTwoQuotientMap_mk]
  exact Submodule.mem_map_of_mem
    (elementaryTwoQuotientMk_mem_torsionImageFiltration_obstructionThreshold hG b)

/-- A multiplicative equivalence preserves the obstruction threshold. -/
@[simp] theorem obstructionThreshold_congr (e : G ≃* H) (b : G) :
    obstructionThreshold (e b) = obstructionThreshold b := by
  have h (t : ℕ) : elementaryTwoQuotientMk (e b) ∈ torsionImageFiltration H t ↔
      elementaryTwoQuotientMk b ∈ torsionImageFiltration G t := by
    rw [← elementaryTwoQuotientCongr_mk, ← torsionImageFiltration_map_elementaryTwoQuotientCongr e,
      Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
  simp only [obstructionThreshold, h]

end Functoriality

section Pi

variable {ι : Type*} {G : ι → Type*} [∀ i, CommGroup (G i)]

/-- The square class of a family lies in `B_t` exactly when the square class of each coordinate
does. -/
theorem elementaryTwoQuotientMk_mem_torsionImageFiltration_pi_iff (b : ∀ i, G i) (t : ℕ) :
    elementaryTwoQuotientMk b ∈ torsionImageFiltration (∀ i, G i) t ↔
      ∀ i, elementaryTwoQuotientMk (b i) ∈ torsionImageFiltration (G i) t := by
  simp only [elementaryTwoQuotientMk_mem_torsionImageFiltration_iff, funext_iff, Pi.pow_apply]
  exact (Classical.skolem (p := fun i (h : G i) ↦ h ^ 2 ^ (t + 1) = b i ^ 2 ^ t)).symm

/-- **The threshold of a finite family** of elements of torsion groups is the maximum of the
thresholds of its coordinates. On a product of cyclic `2`-groups, each coordinate is either a
generator of its factor `C_{2 ^ e_j}`, of threshold `e_j` by
`obstructionThreshold_eq_of_forall_mem_zpowers`, or a square, of threshold `0`; so the threshold is
the largest `e_j` over the coordinates that generate their factor. -/
theorem obstructionThreshold_pi [Fintype ι] (hG : ∀ i, IsMulTorsion (G i)) (b : ∀ i, G i) :
    obstructionThreshold b = Finset.univ.sup fun i ↦ obstructionThreshold (b i) := by
  have hA : IsMulTorsion (∀ i, G i) := fun b ↦ IsOfFinOrder.pi fun i ↦ hG i (b i)
  refine eq_of_forall_ge_iff fun t ↦ ?_
  simp only [obstructionThreshold_le_iff hA, obstructionThreshold_le_iff (hG _),
    elementaryTwoQuotientMk_mem_torsionImageFiltration_pi_iff, Finset.sup_le_iff, Finset.mem_univ,
    true_implies]

end Pi

section Cyclic

variable {A : Type*} [CommGroup A] {e : ℕ}

/-- **The filtration of a group of exponent dividing `2 ^ e`, from `e` on.** If `2 ^ e` kills
every element of `A` (for instance if `A` has order `2 ^ e`), then `B_t` is all of `A / A²` for
every `t ≥ e`. -/
theorem torsionImageFiltration_eq_top_of_forall_pow_eq_one (h : ∀ a : A, a ^ 2 ^ e = 1) {t : ℕ}
    (ht : e ≤ t) : torsionImageFiltration A t = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ ?_
  obtain ⟨b, rfl⟩ := elementaryTwoQuotientMk_surjective x
  exact torsionImageFiltration_mono ht (elementaryTwoQuotientMk_mem_torsionImageFiltration (h b))

/-- **The filtration of a cyclic group of order `2 ^ e`, below `e`.** In a cyclic group of order
`2 ^ e`, every element killed by `2 ^ t` with `t < e` is a square, so `B_t = 0`. -/
theorem torsionImageFiltration_eq_bot_of_isCyclic [IsCyclic A] (hA : Nat.card A = 2 ^ e) {t : ℕ}
    (ht : t < e) : torsionImageFiltration A t = ⊥ := by
  have : Finite A := Nat.finite_of_card_ne_zero (hA ▸ pow_ne_zero e two_ne_zero)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := A)
  refine (Submodule.eq_bot_iff _).2 ?_
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 (hg a))
  rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one, orderOf_eq_card_of_forall_mem_zpowers hg, hA] at ha
  -- `2 ^ e ∣ k * 2 ^ t` with `t < e` forces `k` to be even.
  have h2 : 2 ^ t * 2 ∣ 2 ^ t * k :=
    (pow_succ 2 t ▸ Nat.pow_dvd_pow 2 ht).trans (mul_comm k (2 ^ t) ▸ ha)
  obtain ⟨j, rfl⟩ := Nat.dvd_of_mul_dvd_mul_left (Nat.two_pow_pos t) h2
  rw [elementaryTwoQuotientMk_eq_zero_iff, pow_mul]
  exact (IsSquare.sq g).pow j

/-- **A generator of a cyclic group of order `2 ^ e` has threshold `e`.** -/
theorem obstructionThreshold_eq_of_forall_mem_zpowers {g : A}
    (hg : ∀ x : A, x ∈ Subgroup.zpowers g) (hA : Nat.card A = 2 ^ e) :
    obstructionThreshold g = e := by
  have : Finite A := Nat.finite_of_card_ne_zero (hA ▸ pow_ne_zero e two_ne_zero)
  have : IsCyclic A := isCyclic_iff_exists_zpowers_eq_top.2 ⟨g, eq_top_iff.2 fun x _ ↦ hg x⟩
  refine le_antisymm ((obstructionThreshold_le_iff isMulTorsion_of_finite).2 ?_)
    (not_lt.1 fun hlt ↦ ?_)
  · rw [torsionImageFiltration_eq_top_of_forall_pow_eq_one (fun a ↦ by rw [← hA, pow_card_eq_one'])
      le_rfl]
    exact Submodule.mem_top
  · -- Below `e` the filtration vanishes, so `g = s ^ 2` for a power `s = g ^ k`, and then
    -- `2 * k ≡ 1` modulo the even order `2 ^ e` of `g`, which is impossible.
    have hmem := elementaryTwoQuotientMk_mem_torsionImageFiltration_obstructionThreshold
      isMulTorsion_of_finite g
    rw [torsionImageFiltration_eq_bot_of_isCyclic hA hlt, Submodule.mem_bot,
      elementaryTwoQuotientMk_eq_zero_iff] at hmem
    obtain ⟨s, hs⟩ := hmem
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 (hg s))
    have h1 : g ^ 1 = g ^ (k + k) := by rw [pow_one, pow_add]; exact hs
    rw [pow_eq_pow_iff_modEq, orderOf_eq_card_of_forall_mem_zpowers hg, hA] at h1
    have h2 := h1.of_dvd (dvd_pow_self 2 (by omega))
    rw [Nat.ModEq] at h2
    omega

end Cyclic

end TauCeti

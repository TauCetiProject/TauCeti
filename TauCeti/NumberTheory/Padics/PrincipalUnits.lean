/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.Index
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.Units
public import TauCeti.NumberTheory.Padics.RingHoms
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Subgroup
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# Principal unit groups `1 + p^f ℤ_p`, their closed subgroups, and pro-`p` subgroups of `ℤ_pˣ`

For a prime `p` and `f : ℕ`, the **principal unit group of level `f`** is
`U^(f) = 1 + p^f ℤ_p ≤ ℤ_pˣ`, the kernel of reduction modulo `p ^ f` on units. The groups
`U^(f)` are open, closed, decreasing, with trivial intersection, and they form a neighbourhood
basis of `1` in `ℤ_pˣ`; the index of `U^(f)` in `ℤ_pˣ` is Euler's totient `φ(p ^ f)`.

The main results are about the structure of these groups as topological groups. Raising to
the `p ^ k`-th power moves an element of exact level `f` (in `U^(f)` but not in `U^(f+1)`) to
exact level `f + k`, provided `f ≥ 1`, and `f ≥ 2` when `p = 2` (the *lifting-the-exponent*
step, read off from Mathlib's expansion `(1 + p^f x)^(p^k) = 1 + p^(f+k) (x + p y)`,
`ZMod.exists_one_add_mul_pow_prime_pow_eq`; for `p = 2` and `f = 1` it fails, since
`(-1)^2 = 1`). Hence an element of exact level `f` generates each finite quotient
`U^(f) / U^(f+k)`, which is cyclic of order `p ^ k`, so the closed subgroup it generates is all
of `U^(f)`: the groups `U^(f)` are **procyclic**.
Consequently every nontrivial closed subgroup of `1 + pℤ_p` (of `1 + 4ℤ_2` when `p = 2`) is
one of the `U^(f)`, and `f` is determined by the subgroup through its index.

The case `p = 2` is the input to the description of all closed subgroups of `ℤ_2ˣ`, which are
sorted by how they sit over `{±1}` inside `ℤ_2ˣ = {±1} × (1 + 4ℤ_2)`.

The filtration also identifies the pro-`p` subgroups of the profinite group `ℤ_pˣ`: they are
exactly the subgroups of `1 + pℤ_p`. Every `U^(f)` with `f ≥ 1` is pro-`p`, because its finite
quotients `U^(f) / U^(f+k)` have order `p ^ k`, and a pro-`p` subgroup has trivial image in the
quotient `ℤ_pˣ / (1 + pℤ_p)` of order `p - 1`. For `p = 2` the principal unit group `1 + 2ℤ_2`
is all of `ℤ_2ˣ`, so every subgroup of `ℤ_2ˣ` is pro-`2`.

## Main declarations

* `TauCeti.unitsPrincipal p f`: the principal unit group `U^(f) = 1 + p^f ℤ_p`, with
  `TauCeti.mem_unitsPrincipal_iff` (`u ∈ U^(f) ↔ p ^ f ∣ u - 1`) and its norm form; at level
  one, `TauCeti.mem_unitsPrincipal_one_iff_toZMod` and `TauCeti.mem_unitsPrincipal_one_iff_residue`
  read the condition in `ℤ/pℤ` and in the residue field, and
  `TauCeti.unitsPrincipal_one_eq_ker_unitsMap_residue` identifies `U^(1)` with the kernel of
  reduction on units.
* `TauCeti.isOpen_unitsPrincipal`, `TauCeti.isClosed_unitsPrincipal`,
  `TauCeti.unitsPrincipal_antitone`, `TauCeti.iInf_unitsPrincipal_eq_bot`,
  `TauCeti.hasBasis_nhds_one_unitsPrincipal`: the topology of the filtration.
* `TauCeti.index_unitsPrincipal`: `[ℤ_pˣ : U^(f)] = φ(p ^ f)`, so `p ^ (f - 1) * (p - 1)`
  for `f ≥ 1`, and `2 ^ (f - 1)` for `p = 2`; `TauCeti.relIndex_unitsPrincipal`:
  `[U^(f) : U^(f+k)] = p ^ k` for `f ≥ 1`.
* `TauCeti.exists_mem_unitsPrincipal_and_notMem_succ`: every unit other than `1` has an exact
  level.
* `TauCeti.neg_one_mem_unitsPrincipal_two_iff`, `TauCeti.neg_mem_unitsPrincipal_two_two_iff`:
  in `ℤ_2ˣ`, `-1 ∉ U^(f)` for `f ≥ 2`, and `u ≡ ±1 mod 4` with exactly one sign;
  `TauCeti.inv_mul_mem_unitsPrincipal_two_succ`: two dyadic units of the same exact level are
  congruent modulo the next level.
* `TauCeti.pow_pow_mem_unitsPrincipal`, `TauCeti.pow_pow_notMem_unitsPrincipal`: the `p ^ k`-th
  power of an element of exact level `f` has exact level `f + k`.
* `TauCeti.topologicalClosure_zpowers_eq_unitsPrincipal`: an element of exact level `f`
  topologically generates `U^(f)`; `TauCeti.exists_topologicalClosure_zpowers_eq_unitsPrincipal`:
  `U^(f)` is procyclic.
* `TauCeti.map_powMonoidHom_unitsPrincipal`: `(U^(f))^p = U^(f+1)`, the subgroup of `p`-th powers
  of `U^(f)`; `TauCeti.relIndex_map_powMonoidHom_unitsPrincipal`: `(U^(f) : (U^(f))^p) = p`.
* `TauCeti.exists_eq_unitsPrincipal_of_isClosed`: a nontrivial closed subgroup of `U^(f₀)` is
  some `U^(f)` with `f ≥ f₀`; `TauCeti.unitsPrincipal_inj`, `TauCeti.unitsPrincipal_injective`:
  the level is unique, at every level when `p` is odd.
* `TauCeti.isProP_unitsPrincipal`: `1 + p^f ℤ_p` is pro-`p` for `f ≥ 1`.
* `TauCeti.IsProP.le_unitsPrincipal_one`, `TauCeti.isProP_iff_le_unitsPrincipal_one`: a subgroup
  of `ℤ_pˣ` is pro-`p` exactly when it lies in `1 + pℤ_p`.
* `TauCeti.isProP_two_subgroup_units`: every subgroup of `ℤ_2ˣ` is pro-`2`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, Proposition 5.7.
* J. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), the remark
  following the corollary to Theorem 4.
-/

public section

open Filter Topology

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]

variable (p) in
/-- The **principal unit group of level `f`**, `U^(f) = 1 + p^f ℤ_p`: the kernel of reduction
modulo `p ^ f` on the units of `ℤ_p`. At `f = 0` it is all of `ℤ_pˣ`. -/
noncomputable def unitsPrincipal (f : ℕ) : Subgroup ℤ_[p]ˣ :=
  (Units.map (PadicInt.toZModPow (p := p) f).toMonoidHom).ker

/-- A unit lies in `U^(f)` iff it reduces to `1` modulo `p ^ f`. -/
@[simp]
theorem mem_unitsPrincipal_iff_toZModPow {f : ℕ} {u : ℤ_[p]ˣ} :
    u ∈ unitsPrincipal p f ↔ PadicInt.toZModPow f (u : ℤ_[p]) = 1 := by
  rw [unitsPrincipal, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, Units.val_one]

/-- `u ∈ U^(f)` iff `u ≡ 1 mod p ^ f`. -/
theorem mem_unitsPrincipal_iff {f : ℕ} {u : ℤ_[p]ˣ} :
    u ∈ unitsPrincipal p f ↔ (p : ℤ_[p]) ^ f ∣ (u : ℤ_[p]) - 1 := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one,
    sub_eq_zero, mem_unitsPrincipal_iff_toZModPow]

/-- `u ∈ U^(f)` iff `‖u - 1‖ ≤ p ^ (-f)`. -/
theorem mem_unitsPrincipal_iff_norm {f : ℕ} {u : ℤ_[p]ˣ} :
    u ∈ unitsPrincipal p f ↔ ‖(u : ℤ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(f : ℤ)) := by
  rw [mem_unitsPrincipal_iff, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]

/-- `u ∈ U^(1)` iff `u ≡ 1 mod p`, read in `ℤ/pℤ`. -/
theorem mem_unitsPrincipal_one_iff_toZMod {u : ℤ_[p]ˣ} :
    u ∈ unitsPrincipal p 1 ↔ PadicInt.toZMod (u : ℤ_[p]) = 1 := by
  rw [mem_unitsPrincipal_iff, pow_one, ← Ideal.mem_span_singleton,
    ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_one,
    sub_eq_zero]

/-- `u ∈ U^(1)` iff `u` reduces to `1` in the residue field of `ℤ_p`. -/
theorem mem_unitsPrincipal_one_iff_residue {u : ℤ_[p]ˣ} :
    u ∈ unitsPrincipal p 1 ↔ IsLocalRing.residue ℤ_[p] (u : ℤ_[p]) = 1 := by
  rw [mem_unitsPrincipal_iff, pow_one, ← Ideal.mem_span_singleton,
    ← PadicInt.maximalIdeal_eq_span_p, ← IsLocalRing.residue_eq_zero_iff, map_sub, map_one,
    sub_eq_zero]

variable (p) in
/-- The principal unit group `1 + pℤ_p` is the kernel of reduction on units. -/
theorem unitsPrincipal_one_eq_ker_unitsMap_residue :
    unitsPrincipal p 1 =
      (Units.map (IsLocalRing.residue ℤ_[p] : ℤ_[p] →* IsLocalRing.ResidueField ℤ_[p])).ker := by
  ext u
  rw [mem_unitsPrincipal_one_iff_residue, MonoidHom.mem_ker, Units.ext_iff]
  simp

variable (p) in
@[simp]
theorem unitsPrincipal_zero : unitsPrincipal p 0 = ⊤ := by
  ext u
  simp only [mem_unitsPrincipal_iff, pow_zero, one_dvd, Subgroup.mem_top]

variable (p) in
/-- The principal unit groups decrease with the level. -/
theorem unitsPrincipal_antitone : Antitone (unitsPrincipal p) := fun _ _ hfg _ hu ↦
  mem_unitsPrincipal_iff.mpr <| (pow_dvd_pow _ hfg).trans (mem_unitsPrincipal_iff.mp hu)

variable (p) in
/-- No principal unit group is trivial: `1 + p ^ max f 1` is an element of `U^(f)` other than
`1`. -/
theorem unitsPrincipal_ne_bot (f : ℕ) : unitsPrincipal p f ≠ ⊥ := by
  intro h
  have hunit : IsUnit (1 + (p : ℤ_[p]) ^ max f 1) :=
    PadicInt.isUnit_one_add_of_dvd (dvd_pow_self _ (by omega))
  have hmem : hunit.unit ∈ unitsPrincipal p f := by
    rw [mem_unitsPrincipal_iff, IsUnit.unit_spec, add_sub_cancel_left]
    exact pow_dvd_pow _ (le_max_left f 1)
  rw [h, Subgroup.mem_bot, Units.ext_iff, IsUnit.unit_spec, Units.val_one, add_eq_left] at hmem
  exact pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero) hmem

variable (p) in
/-- Every principal unit group is open: it is the kernel of a continuous map to a discrete
group. -/
theorem isOpen_unitsPrincipal (f : ℕ) : IsOpen (unitsPrincipal p f : Set ℤ_[p]ˣ) := by
  rw [unitsPrincipal, MonoidHom.coe_ker]
  exact (isOpen_discrete _).preimage ((PadicInt.continuous_toZModPow f).units_map _)

variable (p) in
/-- Every principal unit group is closed: it is the kernel of a continuous map to a discrete
group. -/
theorem isClosed_unitsPrincipal (f : ℕ) : IsClosed (unitsPrincipal p f : Set ℤ_[p]ˣ) := by
  rw [unitsPrincipal, MonoidHom.coe_ker]
  exact isClosed_singleton.preimage ((PadicInt.continuous_toZModPow f).units_map _)

variable (p) in
/-- The principal unit groups have trivial intersection: `U^(∞) = {1}`. -/
@[simp]
theorem iInf_unitsPrincipal_eq_bot : ⨅ f, unitsPrincipal p f = ⊥ := by
  refine (eq_bot_iff).mpr fun u hu ↦ ?_
  rw [Subgroup.mem_iInf] at hu
  rw [Subgroup.mem_bot, Units.ext_iff, Units.val_one, ← sub_eq_zero,
    ← PadicInt.ext_of_toZModPow]
  intro f
  rw [map_zero, ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
  exact mem_unitsPrincipal_iff.mp (hu f)

/-- Every unit `u ≠ 1` has an **exact level**: a `f` with `u ∈ U^(f)` but `u ∉ U^(f+1)`, namely
the `p`-adic valuation of `u - 1`. -/
theorem exists_mem_unitsPrincipal_and_notMem_succ {u : ℤ_[p]ˣ} (hu : u ≠ 1) :
    ∃ f, u ∈ unitsPrincipal p f ∧ u ∉ unitsPrincipal p (f + 1) := by
  classical
  have hex : ∃ f, u ∉ unitsPrincipal p (f + 1) := by
    by_contra! h
    refine hu (Subgroup.mem_bot.mp ?_)
    rw [← iInf_unitsPrincipal_eq_bot p, Subgroup.mem_iInf]
    intro f
    rcases f with - | f
    · simp
    · exact h f
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
  · rw [h0]
    simp
  · have := Nat.find_min hex (Nat.sub_lt h0 one_pos)
    rwa [not_not, Nat.sub_add_cancel (by omega : 1 ≤ Nat.find hex)] at this

variable (p) in
/-- The principal unit groups form a neighbourhood basis of `1` in `ℤ_pˣ`. -/
theorem hasBasis_nhds_one_unitsPrincipal :
    (𝓝 (1 : ℤ_[p]ˣ)).HasBasis (fun _ ↦ True) fun f ↦ (unitsPrincipal p f : Set ℤ_[p]ˣ) := by
  refine hasBasis_iff.mpr fun t ↦ ⟨fun ht ↦ ?_, fun ⟨f, _, hf⟩ ↦
    mem_of_superset ((isOpen_unitsPrincipal p f).mem_nhds (one_mem _)) hf⟩
  rw [Units.isOpenEmbedding_val.isInducing.nhds_eq_comap, mem_comap] at ht
  obtain ⟨s, hs, hst⟩ := ht
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨f, hf⟩ := PadicInt.exists_pow_neg_lt p hε
  refine ⟨f, trivial, fun u hu ↦ hst <| hεs ?_⟩
  rw [Metric.mem_ball, dist_eq_norm]
  exact (mem_unitsPrincipal_iff_norm.mp hu).trans_lt hf

/-! ### Indices -/

variable (p) in
/-- `[ℤ_pˣ : U^(f)] = φ(p ^ f)`: reduction modulo `p ^ f` is surjective on units. -/
@[simp]
theorem index_unitsPrincipal (f : ℕ) : (unitsPrincipal p f).index = Nat.totient (p ^ f) := by
  rw [unitsPrincipal, Subgroup.index_ker,
    MonoidHom.range_eq_top_of_surjective _ (PadicInt.surjective_units_map_toZModPow f),
    Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

variable (p) in
/-- `[ℤ_pˣ : U^(f)] = p ^ (f - 1) * (p - 1)` for `f ≥ 1`. -/
theorem index_unitsPrincipal_of_pos {f : ℕ} (hf : 0 < f) :
    (unitsPrincipal p f).index = p ^ (f - 1) * (p - 1) := by
  rw [index_unitsPrincipal, Nat.totient_prime_pow hp.out hf]

/-- `[ℤ_2ˣ : U^(f)] = 2 ^ (f - 1)`, including the degenerate levels `f = 0, 1` of index `1`. -/
theorem index_unitsPrincipal_two (f : ℕ) : (unitsPrincipal 2 f).index = 2 ^ (f - 1) := by
  rcases f with - | f
  · simp
  · rw [index_unitsPrincipal_of_pos 2 f.succ_pos]
    simp

/-- The dyadic filtration starts at level `2`: `U^(1) = 1 + 2ℤ_2` is all of `ℤ_2ˣ`. -/
@[simp]
theorem unitsPrincipal_two_one : unitsPrincipal 2 1 = ⊤ :=
  Subgroup.index_eq_one.mp ((index_unitsPrincipal_two 1).trans (pow_zero 2))

/-- `-1 ∈ U^(f)` in `ℤ_2ˣ` iff `f ≤ 1`: `-1 ≡ 1 mod 2 ^ f` iff `2 ^ f ∣ 2`. -/
theorem neg_one_mem_unitsPrincipal_two_iff {f : ℕ} :
    (-1 : ℤ_[2]ˣ) ∈ unitsPrincipal 2 f ↔ f ≤ 1 := by
  rw [mem_unitsPrincipal_iff, Units.val_neg, Units.val_one, Nat.cast_ofNat, ← neg_add',
    one_add_one_eq_two, dvd_neg,
    ← pow_dvd_pow_iff (by norm_num : (2 : ℤ_[2]) ≠ 0) PadicInt.p_nonunit (n := f) (m := 1),
    pow_one]

/-- `U^(2) = 1 + 4ℤ_2` has index `2` in `ℤ_2ˣ` and does not contain `-1`, so a dyadic unit `u`
lies outside `1 + 4ℤ_2` iff `-u` lies inside: `u ≡ 1` or `u ≡ -1 mod 4`, and not both. -/
theorem neg_mem_unitsPrincipal_two_two_iff {u : ℤ_[2]ˣ} :
    -u ∈ unitsPrincipal 2 2 ↔ u ∉ unitsPrincipal 2 2 := by
  rw [← neg_one_mul, Subgroup.mul_mem_iff_of_index_two (index_unitsPrincipal_two 2),
    neg_one_mem_unitsPrincipal_two_iff]
  simp

/-- For `f ≥ 2`, a dyadic unit and its negative are never both in `U^(f)`. -/
theorem notMem_unitsPrincipal_two_of_neg_mem {f : ℕ} (hf : 2 ≤ f) {u : ℤ_[2]ˣ}
    (hu : -u ∈ unitsPrincipal 2 f) : u ∉ unitsPrincipal 2 f := fun h ↦
  neg_mem_unitsPrincipal_two_two_iff.mp (unitsPrincipal_antitone 2 hf hu)
    (unitsPrincipal_antitone 2 hf h)

instance (f : ℕ) : (unitsPrincipal p f).FiniteIndex :=
  ⟨by rw [index_unitsPrincipal]; exact (Nat.totient_pos.mpr (pow_pos hp.out.pos f)).ne'⟩

variable (p) in
/-- `[U^(f) : U^(f+k)] = p ^ k` for `f ≥ 1`. -/
theorem relIndex_unitsPrincipal {f : ℕ} (hf : 0 < f) (k : ℕ) :
    (unitsPrincipal p (f + k)).relIndex (unitsPrincipal p f) = p ^ k := by
  have h := Subgroup.relIndex_mul_index (unitsPrincipal_antitone p (Nat.le_add_right f k))
  rw [index_unitsPrincipal_of_pos p hf, index_unitsPrincipal_of_pos p (by omega),
    show f + k - 1 = k + (f - 1) by omega, pow_add, mul_assoc] at h
  exact mul_right_cancel₀ (Nat.mul_ne_zero (pow_pos hp.out.pos _).ne'
    (Nat.sub_ne_zero_of_lt hp.out.one_lt)) h

/-- At `p = 2`, two elements of exact level `f ≥ 1` are congruent modulo `U^(f+1)`: the quotient
`U^(f) / U^(f+1)` has order `2`. -/
theorem inv_mul_mem_unitsPrincipal_two_succ {f : ℕ} (hf : 0 < f) {u x : ℤ_[2]ˣ}
    (hu : u ∈ unitsPrincipal 2 f) (hu' : u ∉ unitsPrincipal 2 (f + 1))
    (hx : x ∈ unitsPrincipal 2 f) (hx' : x ∉ unitsPrincipal 2 (f + 1)) :
    u⁻¹ * x ∈ unitsPrincipal 2 (f + 1) := by
  have h2 : ((unitsPrincipal 2 (f + 1)).subgroupOf (unitsPrincipal 2 f)).index = 2 := by
    rw [← Subgroup.relIndex, relIndex_unitsPrincipal 2 hf 1, pow_one]
  have := (Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨u⁻¹, (unitsPrincipal 2 f).inv_mem hu⟩)
    (b := ⟨x, hx⟩)).mpr (by
      simp only [Subgroup.mem_subgroupOf]
      exact iff_of_false (fun h ↦ hu' ((Subgroup.inv_mem_iff _).mp h)) hx')
  simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mk] using this

/-! ### Lifting the exponent -/

/-- For `u ≡ 1 mod p^f` with `f ≥ 1`, `u ^ (p ^ k) ≡ 1 mod p^(f+k)`. -/
theorem pow_pow_mem_unitsPrincipal {f : ℕ} (hf : 0 < f) {u : ℤ_[p]ˣ}
    (hu : u ∈ unitsPrincipal p f) (k : ℕ) : u ^ p ^ k ∈ unitsPrincipal p (f + k) := by
  rw [mem_unitsPrincipal_iff] at hu ⊢
  obtain ⟨x, hx⟩ := hu
  obtain ⟨y, hy⟩ := ZMod.exists_one_add_mul_pow_prime_pow_eq (R := ℤ_[p]) (u := (p : ℤ_[p]) ^ f)
    (v := 1) hp.out (one_dvd _)
    (by rw [mul_one, ← pow_succ', ← pow_mul]; exact pow_dvd_pow _ (by nlinarith [hp.out.two_le]))
    x k
  rw [Units.val_pow_eq_pow_val, sub_eq_iff_eq_add'.mp hx, hy, add_sub_cancel_left]
  exact Dvd.intro (x + y) (by rw [pow_add]; ring)

/-- For `u` of exact level `f`, that is `u ≡ 1 mod p^f` but `u ≢ 1 mod p^(f+1)`, the power
`u ^ (p ^ k)` is not `≡ 1 mod p^(f+k+1)`, provided `f ≥ 1`, and `f ≥ 2` when `p = 2`; together
with `pow_pow_mem_unitsPrincipal`, it has exact level `f + k`. This is where the level
restriction enters: `(1 + p^f x)^(p^k) = 1 + p^(f+k) (x + p y)` needs `p^(f+2) ∣ p^(fp)`. -/
theorem pow_pow_notMem_unitsPrincipal {f : ℕ} (hf : 0 < f) (hf₂ : p = 2 → 2 ≤ f) {u : ℤ_[p]ˣ}
    (hu : u ∈ unitsPrincipal p f) (hu' : u ∉ unitsPrincipal p (f + 1)) (k : ℕ) :
    u ^ p ^ k ∉ unitsPrincipal p (f + k + 1) := by
  rw [mem_unitsPrincipal_iff] at hu hu' ⊢
  obtain ⟨x, hx⟩ := hu
  have hfp : f + 2 ≤ f * p := by
    rcases Nat.lt_or_ge p 3 with h3 | h3
    · have hp2 : p = 2 := by have := hp.out.two_le; omega
      have := hf₂ hp2
      rw [hp2]
      omega
    · nlinarith
  obtain ⟨y, hy⟩ := ZMod.exists_one_add_mul_pow_prime_pow_eq (R := ℤ_[p]) (u := (p : ℤ_[p]) ^ f)
    (v := p) hp.out (dvd_pow_self _ hf.ne')
    (by rw [← pow_succ', ← pow_succ, ← pow_mul]; exact pow_dvd_pow _ hfp) x k
  have hp0 : (p : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  rw [hx, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ hp0)] at hu'
  rw [Units.val_pow_eq_pow_val, sub_eq_iff_eq_add'.mp hx, hy, add_sub_cancel_left,
    show (p : ℤ_[p]) ^ (f + k + 1) = p ^ k * p ^ f * p by ring,
    mul_dvd_mul_iff_left (mul_ne_zero (pow_ne_zero _ hp0) (pow_ne_zero _ hp0)),
    dvd_add_left (dvd_mul_right _ _)]
  exact hu'

/-! ### Procyclicity -/

/-- An element `u` of exact level `f` generates `U^(f)` modulo every `U^(f+k)`: each
`x ∈ U^(f)` is congruent to a power of `u` modulo `U^(f+k)`. This is the finite-level form of
the procyclicity of `U^(f)`; the quotient `U^(f) / U^(f+k)` is cyclic of order `p ^ k`
generated by the class of `u`. -/
theorem exists_zpow_inv_mul_mem_unitsPrincipal {f : ℕ} (hf : 0 < f) (hf₂ : p = 2 → 2 ≤ f)
    {u : ℤ_[p]ˣ} (hu : u ∈ unitsPrincipal p f) (hu' : u ∉ unitsPrincipal p (f + 1))
    {x : ℤ_[p]ˣ} (hx : x ∈ unitsPrincipal p f) (k : ℕ) :
    ∃ n : ℤ, (u ^ n)⁻¹ * x ∈ unitsPrincipal p (f + k) := by
  rcases k with - | k
  · exact ⟨0, by simpa using hx⟩
  -- the finite quotient `Q = U^(f) / U^(f+k+1)`, of order `p ^ (k + 1)`
  set K := unitsPrincipal p f
  set H := (unitsPrincipal p (f + (k + 1))).subgroupOf K
  have hcard : Nat.card (K ⧸ H) = p ^ (k + 1) := by
    rw [← Subgroup.index_eq_card]
    exact relIndex_unitsPrincipal p hf (k + 1)
  -- the class of `u` has order `p ^ (k + 1)`, so it generates `Q`
  set g : K ⧸ H := QuotientGroup.mk ⟨u, hu⟩
  have hg : orderOf g = p ^ (k + 1) := by
    refine orderOf_eq_prime_pow ?_ ?_
    · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Subgroup.coe_pow]
      exact pow_pow_notMem_unitsPrincipal hf hf₂ hu hu' k
    · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Subgroup.coe_pow]
      exact pow_pow_mem_unitsPrincipal hf hu (k + 1)
  have : Finite (K ⧸ H) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact (pow_pos hp.out.pos _).ne')
  have htop : Subgroup.zpowers g = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hg, hcard])
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
    (htop ▸ Subgroup.mem_top (QuotientGroup.mk ⟨x, hx⟩ : K ⧸ H))
  refine ⟨n, ?_⟩
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hn
  simpa using hn

/-- An element of exact level `f` **topologically generates** `U^(f)`, provided `f ≥ 1`, and
`f ≥ 2` when `p = 2`. -/
theorem topologicalClosure_zpowers_eq_unitsPrincipal {f : ℕ} (hf : 0 < f) (hf₂ : p = 2 → 2 ≤ f)
    {u : ℤ_[p]ˣ} (hu : u ∈ unitsPrincipal p f) (hu' : u ∉ unitsPrincipal p (f + 1)) :
    (Subgroup.zpowers u).topologicalClosure = unitsPrincipal p f := by
  refine le_antisymm (Subgroup.topologicalClosure_minimal _ (Subgroup.zpowers_le.mpr hu)
    (isClosed_unitsPrincipal p f)) fun x hx ↦ ?_
  rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe]
  have hb : (𝓝 x).HasBasis (fun _ ↦ True)
      fun k ↦ (· * x⁻¹) ⁻¹' (unitsPrincipal p k : Set ℤ_[p]ˣ) :=
    nhds_translation_mul_inv x ▸ (hasBasis_nhds_one_unitsPrincipal p).comap _
  refine (mem_closure_iff_nhds_basis hb).mpr fun k _ ↦ ?_
  obtain ⟨n, hn⟩ := exists_zpow_inv_mul_mem_unitsPrincipal hf hf₂ hu hu' hx k
  refine ⟨u ^ n, Subgroup.zpow_mem_zpowers u n, ?_⟩
  have := unitsPrincipal_antitone p (Nat.le_add_left k f) ((unitsPrincipal p (f + k)).inv_mem hn)
  rw [Set.mem_preimage, SetLike.mem_coe, mul_comm]
  simpa using this

variable (p) in
/-- Every positive level `f` is the exact level of some unit, namely `1 + p ^ f`. -/
theorem exists_mem_unitsPrincipal_and_notMem_succ_of_pos {f : ℕ} (hf : 0 < f) :
    ∃ u : ℤ_[p]ˣ, u ∈ unitsPrincipal p f ∧ u ∉ unitsPrincipal p (f + 1) := by
  have hunit : IsUnit (1 + (p : ℤ_[p]) ^ f) :=
    PadicInt.isUnit_one_add_of_dvd (dvd_pow_self _ hf.ne')
  refine ⟨hunit.unit, ?_, ?_⟩
  · rw [mem_unitsPrincipal_iff, IsUnit.unit_spec, add_sub_cancel_left]
  · rw [mem_unitsPrincipal_iff, IsUnit.unit_spec, add_sub_cancel_left,
      pow_dvd_pow_iff (Nat.cast_ne_zero.mpr hp.out.ne_zero) PadicInt.p_nonunit]
    omega

/-- The principal unit group `U^(f)` is **procyclic** for `f ≥ 1`, and `f ≥ 2` when `p = 2`:
it is the closed subgroup generated by `1 + p ^ f`. -/
theorem exists_topologicalClosure_zpowers_eq_unitsPrincipal {f : ℕ} (hf : 0 < f)
    (hf₂ : p = 2 → 2 ≤ f) :
    ∃ u : ℤ_[p]ˣ, (Subgroup.zpowers u).topologicalClosure = unitsPrincipal p f := by
  obtain ⟨u, hu, hu'⟩ := exists_mem_unitsPrincipal_and_notMem_succ_of_pos p hf
  exact ⟨u, topologicalClosure_zpowers_eq_unitsPrincipal hf hf₂ hu hu'⟩

/-! ### The subgroup of `p`-th powers -/

/-- `(U^(f))^p = U^(f+1)`: the `p`-th powers of the principal units of level `f` are exactly the
principal units of level `f + 1`, for `f ≥ 1`, and `f ≥ 2` when `p = 2`. -/
@[simp]
theorem map_powMonoidHom_unitsPrincipal {f : ℕ} (hf : 0 < f) (hf₂ : p = 2 → 2 ≤ f) :
    (unitsPrincipal p f).map (powMonoidHom p) = unitsPrincipal p (f + 1) := by
  obtain ⟨u, hu, hu'⟩ := exists_mem_unitsPrincipal_and_notMem_succ_of_pos p hf
  rw [← topologicalClosure_zpowers_eq_unitsPrincipal hf hf₂ hu hu',
    MonoidHom.map_topologicalClosure (powMonoidHom p : ℤ_[p]ˣ →* ℤ_[p]ˣ) (continuous_pow p)
      (Subgroup.zpowers u) (Subgroup.isClosed_topologicalClosure _).isCompact,
    MonoidHom.map_zpowers, powMonoidHom_apply]
  exact topologicalClosure_zpowers_eq_unitsPrincipal (by omega) (fun _ ↦ by omega)
    (by simpa only [pow_one] using pow_pow_mem_unitsPrincipal hf hu 1)
    (by simpa only [pow_one] using pow_pow_notMem_unitsPrincipal hf hf₂ hu hu' 1)

/-- `(U^(f) : (U^(f))^p) = p`, for `f ≥ 1`, and `f ≥ 2` when `p = 2`. -/
theorem relIndex_map_powMonoidHom_unitsPrincipal {f : ℕ} (hf : 0 < f) (hf₂ : p = 2 → 2 ≤ f) :
    ((unitsPrincipal p f).map (powMonoidHom p)).relIndex (unitsPrincipal p f) = p := by
  rw [map_powMonoidHom_unitsPrincipal hf hf₂]
  simpa only [pow_one] using relIndex_unitsPrincipal p hf 1

/-! ### The closed subgroups of `1 + p ℤ_p` -/

/-- The level of a principal unit group is determined by the group, through its index, once the
level is positive (at `p = 2` the levels `0` and `1` both give all of `ℤ_2ˣ`). -/
theorem unitsPrincipal_inj {f g : ℕ} (hf : 0 < f) (hg : 0 < g) :
    unitsPrincipal p f = unitsPrincipal p g ↔ f = g := by
  refine ⟨fun hfg ↦ ?_, fun h ↦ h ▸ rfl⟩
  have h := congrArg Subgroup.index hfg
  rw [index_unitsPrincipal_of_pos p hf, index_unitsPrincipal_of_pos p hg] at h
  have := Nat.pow_right_injective hp.out.two_le
    (mul_right_cancel₀ (Nat.sub_ne_zero_of_lt hp.out.one_lt) h)
  omega

/-- For odd `p` the level is determined by the group at every level, including `0`: the index
of `U^(f)` is `1` for `f = 0` and `p ^ (f - 1) * (p - 1) ≥ 2` for `f ≥ 1`. -/
theorem unitsPrincipal_injective (hp₂ : p ≠ 2) : Function.Injective (unitsPrincipal p) := by
  have key {f g : ℕ} (hfg : unitsPrincipal p f = unitsPrincipal p g) (hf : f = 0) : g = 0 := by
    by_contra hg
    have h := congrArg Subgroup.index hfg
    rw [hf, unitsPrincipal_zero, Subgroup.index_top,
      index_unitsPrincipal_of_pos p (Nat.pos_of_ne_zero hg)] at h
    have := Nat.eq_one_of_mul_eq_one_left h.symm
    have := hp.out.two_le
    omega
  intro f g hfg
  rcases Nat.eq_zero_or_pos f with hf | hf
  · rw [hf, key hfg hf]
  rcases Nat.eq_zero_or_pos g with hg | hg
  · rw [hg, key hfg.symm hg]
  exact (unitsPrincipal_inj hf hg).mp hfg

/-- Every nontrivial closed subgroup of `U^(f₀)` is a principal unit group `U^(f)` with
`f ≥ f₀`, provided `f₀ ≥ 1`, and `f₀ ≥ 2` when `p = 2`. In particular the nontrivial closed
subgroups of `1 + pℤ_p` for odd `p`, and of `1 + 4ℤ_2`, are exactly the `1 + p^f ℤ_p`. -/
theorem exists_eq_unitsPrincipal_of_isClosed {f₀ : ℕ} (hf₀ : 0 < f₀) (hf₀₂ : p = 2 → 2 ≤ f₀)
    {A : Subgroup ℤ_[p]ˣ} (hA : IsClosed (A : Set ℤ_[p]ˣ)) (hle : A ≤ unitsPrincipal p f₀)
    (hA' : A ≠ ⊥) : ∃ f, f₀ ≤ f ∧ A = unitsPrincipal p f := by
  classical
  obtain ⟨a, haA, ha1⟩ := (A.bot_or_exists_ne_one).resolve_left hA'
  -- `a ≠ 1` lies outside some `U^(m+1)`, since the `U^(f)` have trivial intersection
  have hex : ∃ f, ∃ a ∈ A, a ∉ unitsPrincipal p (f + 1) := by
    by_contra! h
    refine ha1 (Subgroup.mem_bot.mp ?_)
    rw [← iInf_unitsPrincipal_eq_bot p, Subgroup.mem_iInf]
    intro f
    rcases f with - | f
    · simp
    · exact h f a haA
  -- `Nat.find hex` is the least level `f` at which some element of `A` leaves `U^(f+1)`
  obtain ⟨b, hbA, hb⟩ := Nat.find_spec hex
  have hAle : A ≤ unitsPrincipal p (Nat.find hex) := fun c hc ↦ by
    by_contra hcf
    have hpos : 0 < Nat.find hex := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
      · rw [h0, unitsPrincipal_zero] at hcf
        exact (hcf (Subgroup.mem_top c)).elim
      · exact h0
    exact Nat.find_min hex (Nat.sub_lt hpos one_pos)
      ⟨c, hc, by rwa [Nat.sub_add_cancel (by omega : 1 ≤ Nat.find hex)]⟩
  have hf₀f : f₀ ≤ Nat.find hex := by
    by_contra h
    exact hb (unitsPrincipal_antitone p (by omega) (hle hbA))
  refine ⟨Nat.find hex, hf₀f, le_antisymm hAle ?_⟩
  rw [← topologicalClosure_zpowers_eq_unitsPrincipal (by omega)
    (fun h2 ↦ by have := hf₀₂ h2; omega) (hAle hbA) hb]
  exact Subgroup.topologicalClosure_minimal _ (Subgroup.zpowers_le.mpr hbA) hA

/-! ### The pro-`p` subgroups of `ℤ_pˣ` -/

variable (p) in
/-- **The principal unit groups are pro-`p`**: for `f ≥ 1`, `1 + p^f ℤ_p` is a pro-`p` group. -/
theorem isProP_unitsPrincipal {f : ℕ} (hf : 0 < f) : IsProP p (unitsPrincipal p f) := by
  rw [Subgroup.isProP_iff_isPGroup_map_mk']
  intro U g
  -- `U` contains a principal unit group `U^(k)`, and `u ^ (p ^ k) ∈ U^(f + k) ≤ U^(k)` for
  -- `u ∈ U^(f)`.
  obtain ⟨k, -, hk⟩ := (hasBasis_nhds_one_unitsPrincipal p).mem_iff.mp
    (U.isOpen.mem_nhds (one_mem _))
  obtain ⟨u, hu, hgu⟩ := Subgroup.mem_map.mp g.2
  refine ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, OneMemClass.coe_one, ← hgu, ← map_pow, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  exact hk (unitsPrincipal_antitone p (Nat.le_add_left k f) (pow_pow_mem_unitsPrincipal hf hu k))

/-- **A pro-`p` subgroup of `ℤ_pˣ` consists of principal units.** Its image in the quotient
`ℤ_pˣ / (1 + pℤ_p)`, a group of order `p - 1`, is a `p`-group, hence trivial. -/
theorem IsProP.le_unitsPrincipal_one {A : Subgroup ℤ_[p]ˣ} (hA : IsProP p A) :
    A ≤ unitsPrincipal p 1 := by
  have hU : IsPGroup p (A.map (QuotientGroup.mk' (unitsPrincipal p 1))) :=
    A.isProP_iff_isPGroup_map_mk'.mp hA
      ⟨⟨unitsPrincipal p 1, isOpen_unitsPrincipal p 1⟩, inferInstance⟩
  have : Finite (ℤ_[p]ˣ ⧸ unitsPrincipal p 1) :=
    Subgroup.quotient_finite_of_isOpen _ (isOpen_unitsPrincipal p 1)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hU
  have hidx : Nat.card (ℤ_[p]ˣ ⧸ unitsPrincipal p 1) = p - 1 := by
    rw [← Subgroup.index_eq_card, index_unitsPrincipal_of_pos p one_pos]
    simp
  have hdvd := Subgroup.card_subgroup_dvd_card (A.map (QuotientGroup.mk' (unitsPrincipal p 1)))
  rw [hn, hidx] at hdvd
  have hcop : Nat.Coprime p (p - 1) :=
    (Nat.coprime_self_sub_right hp.out.one_lt.le).mpr (Nat.coprime_one_right p)
  rw [(hcop.pow_left n).eq_one_of_dvd hdvd, Subgroup.card_eq_one, Subgroup.map_eq_bot_iff,
    QuotientGroup.ker_mk'] at hn
  exact hn

/-- **The pro-`p` subgroups of `ℤ_pˣ`** are exactly the subgroups of `1 + pℤ_p`. -/
theorem isProP_iff_le_unitsPrincipal_one (A : Subgroup ℤ_[p]ˣ) :
    IsProP p A ↔ A ≤ unitsPrincipal p 1 :=
  ⟨IsProP.le_unitsPrincipal_one, fun h ↦ (isProP_unitsPrincipal p one_pos).mono h⟩

/-- Every subgroup of `ℤ_2ˣ` is pro-`2`, because `1 + 2ℤ_2 = ℤ_2ˣ`. -/
theorem isProP_two_subgroup_units (A : Subgroup ℤ_[2]ˣ) : IsProP 2 A :=
  (isProP_iff_le_unitsPrincipal_one A).mpr (by rw [unitsPrincipal_two_one]; exact le_top)

end TauCeti

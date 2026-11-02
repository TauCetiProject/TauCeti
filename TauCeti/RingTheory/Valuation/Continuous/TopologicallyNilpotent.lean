/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
public import TauCeti.RingTheory.Valuation.CharacteristicGroup
public import TauCeti.RingTheory.Valuation.Continuous.Basic

/-!
# Bounds on a valuation at a topologically nilpotent element

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Theorem 7.10 and Remark 7.11(1), in the
directions that need no Huber-ring hypothesis.**

Topological nilpotence sends the powers of `a` into every neighbourhood of `0`, so as soon as a
ball `{x | v x < γ}` is a neighbourhood of `0`, some power `v a ^ n` drops below `γ` — the shared
step `exists_pow_lt_of_isTopologicallyNilpotent`. Two different hypotheses put a ball in `𝓝 0`
— continuity of `v`, or a full characteristic group together with the unit ball being a
neighbourhood of `0` — and this file records the bounds Theorem 7.10 asks for under each. They
are *not* the same statement and do not need the same hypotheses.

* `v a < 1`, from continuity. The threshold `1 = v 1` is a value `v` attains, so the ball is
  open by the definition of continuity alone: no compatibility between the topology and the ring
  operations is used, and the codomain need only be a `LinearOrderedCommMonoidWithZero`.
* `v a` is **cofinal** in the value group `Γ_v`: for every `γ ∈ Γ_v` some power `v a ^ n` falls
  below `γ`. This is strictly stronger and costs strictly more, for the reason below, and it is
  recorded on both routes: from continuity, and from `Γ_v = cΓ_v` with the unit ball a
  neighbourhood of `0`.

## The value group, not the codomain

Cofinality quantifies over `Γ_v`, the subgroup of the codomain *generated* by the attained
values, so a general `γ` is a **ratio** `v r / v t`, which need not be attained. That is what
`Valuation.IsContinuous.isOpen_lt_div` supplies, and it is why the continuity route reaches for
the ratio form of continuity rather than the attained-value one: `{x | v x < γ}` has to be a
neighbourhood of `0` for the ratios too before topological nilpotence can be applied to it.
Mathlib's `Valuation.exists_div_eq_of_unit` is what puts a general element of `Γ_v` in that
form. The characteristic-group route instead bounds `γ` below by an attained inverse
(`HasFullCharacteristicGroup.exists_inv_le`) and pulls the unit ball back along multiplication
by the attaining element.

## Why `lt_one` is not just the case `γ = 1`

Cofinality does imply `v a < 1`, through `cofinalValueFor_top_iff` and `CofinalValueFor.lt_one`.
But that route pays for the general `γ`: a group codomain, and continuity of right multiplication
for the ratios. Since `Spv (A, I·A)` membership is a condition on all of `Γ_v` while the second
conjunct of Theorem 7.10 is a condition on `1` alone, the two really are separate obligations,
and the second is recorded at its own — much weaker — hypotheses rather than as a corollary of
the first.

## Main results

* `Valuation.exists_pow_lt_of_isTopologicallyNilpotent`
* `Valuation.IsContinuous.lt_one_of_isTopologicallyNilpotent`
* `Valuation.IsContinuous.cofinalValue_of_isTopologicallyNilpotent`
* `Valuation.HasFullCharacteristicGroup.cofinalValue_of_isTopologicallyNilpotent` :
  cofinality again, with continuity replaced by a full characteristic group plus the open unit
  ball being a neighbourhood of `0` — the `Γ_v = cΓ_v` branch of Theorem 7.10's converse.
* `Valuation.exists_pow_lt_of_isIntegral` : on an integral extension `S` of `R`, the powers of
  the value of a topologically nilpotent `ϖ ∈ R` fall below every nonzero value, provided the
  pullback to `R` is continuous and each value is pushed to at most `1` by a power of `v ϖ`.
* `IsTopologicallyNilpotent.valuation_lt_one` : for the canonical valuation of a valuative topology
  (`IsValuativeTopology`), whose open unit ball is a neighbourhood of `0`, a topologically
  nilpotent element has valuation `< 1`.
* `TauCeti.isTopologicallyNilpotent_iff_valuation_lt_one` : when moreover the value group is
  archimedean, the converse holds too, so topological nilpotence is exactly the open unit ball.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Remark 7.11 and Theorem 7.10.
* AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`, `projects/AdicSpaces/Adic spaces/SpvAITopology.lean`,
  was consulted. Its `cont_to_ideal_le_supp_of_mem_defIdeal` proves the `v a < 1` case over a
  `ValuativeRel`-derived valuation, and its general-`γ` counterpart
  `cont_to_ideal_le_supp_microbial` is an explicit `sorry` gated on a microbiality hypothesis.
  Neither result here needs microbiality, and the hypotheses differ; nothing was copied.
-/

public section

namespace Valuation

open MonoidWithZeroHom TauCeti

variable {A : Type*} [Ring A] [TopologicalSpace A]

section Monoid

variable {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] [Nontrivial Γ₀]

omit [Nontrivial Γ₀] in
/-- **The shared step.** If the ball of radius `γ` is a neighbourhood of `0` and `a` is
topologically nilpotent, some power of `v a` falls below `γ`.

Every bound in this file is this lemma at a different threshold, so it is stated once, at the
monoid level, with the neighbourhood supplied rather than derived: nothing here needs a group
codomain or any compatibility between the topology and the ring operations. No positivity of `γ`
is assumed — a neighbourhood of `0` contains `0`, which already places `v 0 = 0` below `γ`. -/
theorem exists_pow_lt_of_isTopologicallyNilpotent {v : Valuation A Γ₀} {γ : Γ₀}
    (hmem : {x : A | v x < γ} ∈ nhds 0) {a : A} (ha : IsTopologicallyNilpotent a) :
    ∃ n : ℕ, v a ^ n < γ := by
  obtain ⟨n, hn⟩ := ha.exists_pow_mem_of_mem_nhds hmem
  exact ⟨n, by rwa [Set.mem_ofPred_eq, map_pow] at hn⟩

/-- **The second conjunct of Wedhorn Theorem 7.10.** A continuous valuation is `< 1` at every
topologically nilpotent element.

The threshold `1` is the attained value `v 1`, so the ball `{x | v x < 1}` is open straight from
the definition of continuity: nothing relates the topology to the ring operations, and the
codomain is only a monoid.

`Nontrivial Γ₀` is not decoration. If `0 = 1` in `Γ₀` then `Γ₀` is trivial, every `{x | v x < v b}`
is empty and so open, and the conclusion `v a < 1` reads `0 < 0`; a group codomain rules this out
by fiat, a monoid one does not. -/
theorem IsContinuous.lt_one_of_isTopologicallyNilpotent {v : Valuation A Γ₀}
    (hv : v.IsContinuous) {a : A} (ha : IsTopologicallyNilpotent a) : v a < 1 := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_isTopologicallyNilpotent (v := v) (γ := 1)
    ((by simpa using isContinuous_def.mp hv 1 : IsOpen _).mem_nhds (by simp)) ha
  exact not_le.mp fun h ↦ absurd hn (not_lt.mpr (one_le_pow₀ h))

end Monoid

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Wedhorn Remark 7.11(1), the direction that holds for any topological ring.** A continuous
valuation has cofinal values at every topologically nilpotent element: the powers of `a` are
eventually inside each ball `{x | v x < γ}`, and continuity is what makes that ball open.

A general `γ ∈ Γ_v` is a ratio `v r / v t` of attained values, which need not be attained, so
the ball is opened by `IsContinuous.isOpen_lt_div` — whence `[ContinuousConstSMul Aᵐᵒᵖ A]`,
which is continuity of right multiplication by a constant and nothing more. -/
theorem IsContinuous.cofinalValue_of_isTopologicallyNilpotent [ContinuousConstSMul Aᵐᵒᵖ A]
    {v : Valuation A Γ₀} (hv : v.IsContinuous) {a : A} (ha : IsTopologicallyNilpotent a) :
    CofinalValue v a := by
  rw [cofinalValue_iff]
  intro γ hγ
  -- a positive element of `Γ_v` is a ratio of attained values (`Valuation.exists_div_eq_of_unit`)
  obtain ⟨r, t, hr, ht, hrt⟩ := v.exists_div_eq_of_unit (Units.mk0 γ hγ.ne')
  simp only [Units.val_mk0] at hrt
  have hemb : ValueGroup₀.embedding γ = v r / v t := by
    rw [← hrt, map_div₀, Valuation.embedding_restrict, Valuation.embedding_restrict]
  obtain ⟨n, hn⟩ := exists_pow_lt_of_isTopologicallyNilpotent (v := v)
    ((hv.isOpen_lt_div r ht.ne').mem_nhds
      (by simpa using zero_lt_iff.mpr (div_ne_zero hr.ne' ht.ne'))) ha
  exact ⟨n, by rw [← map_pow, Valuation.restrict_lt_iff_lt_embedding, hemb, map_pow]; exact hn⟩

/-- **Full characteristic group makes every topologically nilpotent value cofinal**, given that
the open unit ball `{a | v a < 1}` is a neighbourhood of `0`.

This is the sibling of `IsContinuous.cofinalValue_of_isTopologicallyNilpotent` with continuity
replaced by `Γ_v = cΓ_v` plus the one ball it actually uses. It is the `Γ_v = cΓ_v` branch of
Wedhorn's proof of Theorem 7.10, `⊇` direction, stated with no Huber-ring hypothesis. -/
theorem HasFullCharacteristicGroup.cofinalValue_of_isTopologicallyNilpotent
    [ContinuousConstSMul Aᵐᵒᵖ A] {v : Valuation A Γ₀} (hfull : HasFullCharacteristicGroup v)
    (hU : {a : A | v a < 1} ∈ nhds 0) {x : A} (hx : IsTopologicallyNilpotent x) :
    CofinalValue v x := by
  rw [cofinalValue_iff]
  intro γ hγ
  obtain ⟨t, ht0, htle⟩ := hfull.exists_inv_le hγ
  have htne : v t ≠ 0 := fun h ↦ ht0 (v.restrict_eq_zero_iff.mpr (by simpa using h))
  -- the ball of radius `(v t)⁻¹` pulls back from the unit ball along `· * t`, so it is a
  -- neighbourhood of `0` as well, and the shared step applies to it
  have hmem : {a : A | v a < (v t)⁻¹} ∈ nhds (0 : A) := by
    have hmul : Continuous fun a : A ↦ a * t := continuous_const_smul (MulOpposite.op t)
    refine Filter.mem_of_superset
      (hmul.continuousAt.preimage_mem_nhds (by simpa using hU)) fun a ha ↦ ?_
    have hlt : v a * v t < 1 := by rw [← map_mul]; exact ha
    rw [← inv_mul_cancel₀ htne] at hlt
    exact lt_of_mul_lt_mul_right hlt zero_le
  obtain ⟨n, hgoal⟩ := exists_pow_lt_of_isTopologicallyNilpotent hmem hx
  have hemb : v.restrict x ^ n < (v.restrict t)⁻¹ := by
    refine MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.lt_iff_lt.mp ?_
    simpa only [map_pow, map_inv₀, embedding_restrict] using hgoal
  exact ⟨n, hemb.trans_le htle⟩

section Integral

variable {R S : Type*} [CommRing R] [TopologicalSpace R] [CommRing S] [Algebra R S]
  [Algebra.IsIntegral R S]

/-- **Cofinality on an integral extension.** Let `S` be integral over `R`, `v` a valuation on `S`
whose pullback to `R` is continuous, and `ϖ ∈ R` topologically nilpotent with `v ϖ ≠ 0`, such
that every value of `v` is pushed to at most `1` by a power of `v ϖ`. Then the powers of `v ϖ`
fall below every nonzero value of `v`.

Since `S` is integral over `R`, contracting `supp v ⊊ supp v + cS` to `R` stays strict
(`Ideal.under_lt_under_of_integral_mem_sdiff`), so some `a ∈ R` off the support has the form
`a = y + b' c` with `v y = 0`; continuity of the pullback bounds `v ϖ ^ n` below `v a`, and the
power of `v ϖ` absorbing `v b'` finishes. -/
theorem exists_pow_lt_of_isIntegral {v : Valuation S Γ₀}
    (hu : (v.comap (algebraMap R S)).IsContinuous) {ϖ : R} (hϖ : IsTopologicallyNilpotent ϖ)
    (hϖ0 : v (algebraMap R S ϖ) ≠ 0) (habs : ∀ b, ∃ m : ℕ, v (algebraMap R S ϖ) ^ m * v b ≤ 1)
    {c : S} (hc : v c ≠ 0) : ∃ N : ℕ, v (algebraMap R S ϖ) ^ N < v c := by
  set ι := algebraMap R S
  -- contracting `supp v ⊊ supp v + cS` to `R` stays strict, as `S` is integral over `R`
  obtain ⟨a, ha, haq⟩ := IsConcreteLE.exists_of_lt <| Ideal.under_lt_under_of_integral_mem_sdiff
    (R := R) (le_sup_left : v.supp ≤ v.supp ⊔ Ideal.span {c})
    ⟨Ideal.mem_sup_right (Ideal.mem_span_singleton_self c), mt (v.mem_supp_iff c).mp hc⟩
    (Algebra.IsIntegral.isIntegral c)
  -- so `ι a = y + b' c` with `v y = 0` and `v (ι a) ≠ 0`
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (Ideal.mem_comap.mp ha)
  obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton'.mp hz
  have hVa : v (ι a) = v b' * v c := by
    rw [← hyz, add_comm, Valuation.map_add_supp _ _ hy, map_mul]
  have hVa0 : v (ι a) ≠ 0 := by rwa [Ideal.mem_comap, Valuation.mem_supp_iff] at haq
  obtain ⟨m, hm⟩ := habs b'
  -- continuity of the pullback makes `v (ι ϖ) ^ n < v (ι a)` for large `n`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, v (ι ϖ) ^ n < v (ι a) := by
    have h0 : (0 : R) ∈ {x | v.comap ι x < v.comap ι a} := by
      simpa using zero_lt_iff.mpr hVa0
    simpa using exists_pow_lt_of_isTopologicallyNilpotent
      ((isContinuous_def.mp hu a).mem_nhds h0) hϖ
  refine ⟨n + m, ?_⟩
  calc v (ι ϖ) ^ (n + m) = v (ι ϖ) ^ n * v (ι ϖ) ^ m := pow_add _ _ _
    _ < v (ι a) * v (ι ϖ) ^ m := mul_lt_mul_of_pos_right hn (pow_pos (zero_lt_iff.mpr hϖ0) m)
    _ = v c * (v (ι ϖ) ^ m * v b') := by rw [hVa, mul_comm (v b'), mul_assoc, mul_comm (v b')]
    _ ≤ v c * 1 := by gcongr
    _ = v c := mul_one _

end Integral

end Valuation

section ValuativeTopology

open Filter ValuativeRel

variable {R : Type*} [Ring R] [ValuativeRel R] [TopologicalSpace R] [IsValuativeTopology R]

/-- **A topologically nilpotent element has valuation `< 1`** in a valuative topology, since the
open unit ball is a neighbourhood of `0`. -/
theorem IsTopologicallyNilpotent.valuation_lt_one {x : R} (hx : IsTopologicallyNilpotent x) :
    valuation R x < 1 := by
  obtain ⟨n, hn⟩ := Valuation.exists_pow_lt_of_isTopologicallyNilpotent
    ((IsValuativeTopology.mem_nhds_zero_iff _).mpr ⟨1, fun _ hz ↦ hz⟩) hx
  exact not_le.mp fun h ↦ hn.not_ge (one_le_pow₀ h)

namespace TauCeti

/-- **An element of valuation `< 1` is topologically nilpotent** when the value group is
archimedean: its powers enter every ball `{z | v z < γ}` around `0`. -/
theorem isTopologicallyNilpotent_of_valuation_lt_one [MulArchimedean (ValueGroupWithZero R)]
    {x : R} (hx : valuation R x < 1) : IsTopologicallyNilpotent x := by
  refine (IsValuativeTopology.hasBasis_nhds_zero R).tendsto_right_iff.mpr fun γ _ ↦ ?_
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hx γ
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact (pow_le_pow_right_of_le_one' hx.le hm).trans_lt hn

/-- **Topological nilpotence is the open unit ball** of a valuative topology with archimedean
value group. -/
@[simp]
theorem isTopologicallyNilpotent_iff_valuation_lt_one [MulArchimedean (ValueGroupWithZero R)]
    {x : R} : IsTopologicallyNilpotent x ↔ valuation R x < 1 :=
  ⟨IsTopologicallyNilpotent.valuation_lt_one, isTopologicallyNilpotent_of_valuation_lt_one⟩

end TauCeti

end ValuativeTopology

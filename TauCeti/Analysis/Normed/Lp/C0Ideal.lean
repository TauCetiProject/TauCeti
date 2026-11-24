/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import TauCeti.Analysis.Normed.Ring.TwoSidedIdeal
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Separation.Hausdorff
import TauCeti.Analysis.Normed.Module.Ball.Retraction

/-!
# Filter-null ideals and the `c₀` ideal of a bounded product

For a family of normed rings `A i`, the bounded product is `lp A ∞`. Along any filter `l` on `ι`,
the filter-null ideal `lp.nullIdeal A l` consists of the bounded families whose coordinate norms
tend to `0` along `l`; specializing `l` to `cofinite` recovers the `c₀` ideal `lp.c0Ideal A`. It is
a closed two-sided ideal, closed under `star` when the factors are normed star groups, so for
C⋆-algebras `A i` the quotient `lp A ∞ ⧸ lp.nullIdeal A l` is a C⋆-algebra by
`TwoSidedIdeal.Quotient.nonUnitalCStarAlgebra` (unital when the factors are nonzero unital
C⋆-algebras, by `lp.inftyCStarAlgebra` and `TwoSidedIdeal.Quotient.cstarAlgebra`).

The quotient norm of the class of `a` is `limsup_i ‖a i‖` along `l` (`lp.norm_mk_nullIdeal`,
`lp.norm_mk_c0Ideal`), which becomes the ultralimit `lim_ω ‖a i‖` along an ultrafilter `ω`
(`lp.tendsto_norm_mk_nullIdeal`, `lp.norm_mk_nullIdeal_ultrafilter`). Over `ℝ`, radial retraction
produces a representative of the same norm (`lp.exists_mk_nullIdeal_eq_and_norm_eq`).

## Main declarations

* `lp.nullIdeal`, `lp.isClosed_nullIdeal`, `lp.mk_nullIdeal_eq_mk_iff`: the closed filter-null ideal
  in `lp A ∞` along `l` and quotient equality via coordinatewise norm convergence.
* `lp.norm_mk_nullIdeal`, `lp.tendsto_norm_mk_nullIdeal`, `lp.norm_mk_nullIdeal_ultrafilter`,
  `lp.exists_mk_nullIdeal_eq_and_norm_eq`: `limsup` and ultralimit quotient norm formulas, and
  norm-attaining representatives.
* `lp.c0Ideal`: the families in `lp A ∞` whose coordinate norms tend to `0` along `cofinite`.
* `lp.isClosed_c0Ideal`: the `c₀` ideal is closed.
* `lp.star_mem_c0Ideal`: the `c₀` ideal is closed under `star`.
* `lp.norm_mk_c0Ideal`: the quotient norm is the limit superior of the coordinate norms.
* `lp.norm_mk_c0Ideal_eq_one_of_forall_norm_eq_one`: a family of norm-one elements has quotient
  norm `1`.
* `lp.normOneClass_quotient_c0Ideal`: in particular, the unit of the quotient has norm `1`.
* `lp.nontrivial_quotient_c0Ideal`: over an infinite index type the quotient by the `c₀` ideal of
  a bounded product of normed rings with `‖1‖ = 1` is nonzero.

## References

* B. Blackadar, *Operator Algebras*, II.8.1.
* E. Kirchberg and N. C. Phillips, *Embedding of exact C*-algebras in the Cuntz algebra `O₂`*,
  J. Reine Angew. Math. 525 (2000), Lemma 2.2.
-/

public section

open Filter Topology
open scoped ENNReal

noncomputable section

namespace lp

variable {ι : Type*} (A : ι → Type*) [∀ i, NonUnitalNormedRing (A i)]

private theorem norm_mul_apply_le {A : ι → Type*} [∀ i, NonUnitalNormedRing (A i)]
    (a b : lp A ∞) (i : ι) : ‖(a * b) i‖ ≤ ‖a i‖ * ‖b i‖ := by
  rw [infty_coeFn_mul, Pi.mul_apply]; exact norm_mul_le (a i) (b i)

/-- The filter-null ideal of the bounded product `lp A ∞` along a filter `l`: the bounded families
whose coordinate norms tend to `0` along `l`. -/
def nullIdeal (l : Filter ι) : TwoSidedIdeal (lp A ∞) :=
  .mk' {a | Tendsto (fun i ↦ ‖a i‖) l (𝓝 0)}
    (by simpa using tendsto_const_nhds)
    (fun {a b} ha hb ↦ squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun i ↦ by simpa using norm_add_le (a i) (b i)) (by simpa using ha.add hb))
    (fun {a} ha ↦ by simpa using ha)
    (fun {a b} hb ↦ squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun i ↦ (norm_mul_apply_le a b i).trans
        (mul_le_mul_of_nonneg_right (norm_apply_le_norm ENNReal.top_ne_zero a i) (norm_nonneg _)))
      (by simpa using hb.const_mul ‖a‖))
    (fun {a b} ha ↦ squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun i ↦ (norm_mul_apply_le a b i).trans
        (mul_le_mul_of_nonneg_left (norm_apply_le_norm ENNReal.top_ne_zero b i) (norm_nonneg _)))
      (by simpa using ha.mul_const ‖b‖))

variable {A}

/-- A bounded family lies in `lp.nullIdeal A l` when its coordinate norms tend to `0` along `l`. -/
@[simp]
theorem mem_nullIdeal {l : Filter ι} {a : lp A ∞} :
    a ∈ nullIdeal A l ↔ Tendsto (fun i ↦ ‖a i‖) l (𝓝 0) :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ a

/-- Two bounded families define the same class modulo `lp.nullIdeal A l` if and only if the norms of
their coordinatewise differences tend to `0` along `l`. -/
theorem mk_nullIdeal_eq_mk_iff {l : Filter ι} {a b : lp A ∞} :
    TwoSidedIdeal.Quotient.mk (nullIdeal A l) a =
      TwoSidedIdeal.Quotient.mk (nullIdeal A l) b ↔
      Tendsto (fun i ↦ ‖a i - b i‖) l (𝓝 0) := by
  rw [← sub_eq_zero, ← map_sub, TwoSidedIdeal.Quotient.eq_zero_iff_mem, mem_nullIdeal]
  simp only [lp.coeFn_sub, Pi.sub_apply]

/-- Along the bottom filter, every bounded family lies in the filter-null ideal. -/
@[simp]
theorem nullIdeal_bot : nullIdeal A (⊥ : Filter ι) = ⊤ := by ext a; simp

/-- Passing to a finer filter enlarges the filter-null ideal. -/
theorem nullIdeal_antitone : Antitone (nullIdeal A) :=
  fun _ _ hl _ ha ↦ mem_nullIdeal.2 ((mem_nullIdeal.1 ha).mono_left hl)

variable (A) in
/-- The filter-null ideal is closed in `lp A ∞`: a uniform limit of families vanishing along `l`
vanishes along `l`. -/
theorem isClosed_nullIdeal (l : Filter ι) : IsClosed (nullIdeal A l : Set (lp A ∞)) := by
  refine isClosed_of_closure_subset fun a ha ↦ mem_nullIdeal.2 ?_
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨b, hb, hab⟩ := Metric.mem_closure_iff.1 ha (ε / 2) (half_pos hε)
  filter_upwards [Metric.tendsto_nhds.1 (mem_nullIdeal.1 hb) (ε / 2) (half_pos hε)] with i hi
  rw [Real.dist_eq, sub_zero, abs_norm] at hi ⊢
  have hi' : ‖a i - b i‖ ≤ dist a b := by
    simpa [dist_eq_norm] using norm_apply_le_norm ENNReal.top_ne_zero (a - b) i
  calc ‖a i‖ ≤ ‖a i - b i‖ + ‖b i‖ := norm_le_norm_sub_add _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (hi'.trans hab.le) hi
    _ = ε := add_halves ε

/-- Closedness of `lp.nullIdeal A l` as an instance, equipping `lp A ∞ ⧸ lp.nullIdeal A l` with
its quotient norm and C⋆-algebra structure when the factors are C⋆-algebras. -/
instance (l : Filter ι) : IsClosed (nullIdeal A l : Set (lp A ∞)) :=
  isClosed_nullIdeal A l

/-- The filter-null ideal is closed under `star`. -/
theorem star_mem_nullIdeal [∀ i, StarAddMonoid (A i)] [∀ i, NormedStarGroup (A i)] {l : Filter ι}
    {a : lp A ∞} (ha : a ∈ nullIdeal A l) : star a ∈ nullIdeal A l :=
  mem_nullIdeal.2 (by simpa [lp.star_apply] using mem_nullIdeal.1 ha)

private theorem norm_mk_nullIdeal_bot (a : lp A ∞) :
    ‖TwoSidedIdeal.Quotient.mk (nullIdeal A ⊥) a‖ = limsup (fun i ↦ ‖a i‖) ⊥ := by
  rw [TwoSidedIdeal.Quotient.eq_zero_iff_mem.2 (mem_nullIdeal.2 tendsto_bot),
    _root_.norm_zero, limsup, limsSup, map_bot]
  simp only [eventually_bot, Set.ofPred_true]
  exact (Real.sInf_of_not_bddBelow not_bddBelow_univ).symm

/-- **Quotient norm modulo a filter-null ideal.** For any filter `l`, the norm of the class of `a`
in `lp A ∞ ⧸ lp.nullIdeal A l` is `limsup_i ‖a i‖` along `l` (both sides are `0` when `l = ⊥`). -/
theorem norm_mk_nullIdeal {l : Filter ι} (a : lp A ∞) :
    ‖TwoSidedIdeal.Quotient.mk (nullIdeal A l) a‖ = limsup (fun i ↦ ‖a i‖) l := by
  rcases eq_or_neBot l with rfl | hl
  · exact norm_mk_nullIdeal_bot a
  have hbdd : IsBoundedUnder (· ≤ ·) l (fun i ↦ ‖a i‖) :=
    isBoundedUnder_of ⟨‖a‖, fun i ↦ norm_apply_le_norm ENNReal.top_ne_zero a i⟩
  have hcobdd : IsCoboundedUnder (· ≤ ·) l (fun i ↦ ‖a i‖) :=
    (isBoundedUnder_of ⟨0, fun i ↦ norm_nonneg (a i)⟩).isCoboundedUnder_le
  set L := limsup (fun i ↦ ‖a i‖) l
  have hL : 0 ≤ L := le_limsup_of_frequently_le (Frequently.of_forall fun i ↦ norm_nonneg _) hbdd
  refine le_antisymm (le_of_forall_pos_lt_add fun ε hε ↦ ?_) ?_
  · have hev : ∀ᶠ i in l, ‖a i‖ < L + ε / 2 :=
      eventually_lt_of_limsup_lt (by linarith) hbdd
    classical
    let S : Set ι := {i | ‖a i‖ < L + ε / 2}
    let y : lp A ∞ := ⟨fun i ↦ if i ∈ S then 0 else a i, memℓp_infty_iff.2
      ⟨‖a‖, by
        rintro _ ⟨i, rfl⟩
        by_cases hi : i ∈ S <;> simp [hi, norm_apply_le_norm ENNReal.top_ne_zero a i]⟩⟩
    have hy : y ∈ nullIdeal A l := by
      refine mem_nullIdeal.2 (tendsto_const_nhds.congr' ?_)
      filter_upwards [hev] with i hi
      simp [y, show i ∈ S from hi]
    have hbelow : BddBelow ((‖a + ·‖) '' (nullIdeal A l : Set (lp A ∞))) :=
      ⟨0, by rintro _ ⟨z, _, rfl⟩; exact norm_nonneg _⟩
    rw [TwoSidedIdeal.Quotient.norm_mk_eq]
    refine (csInf_le hbelow ⟨-y, (nullIdeal A l).neg_mem hy, rfl⟩).trans_lt
      ((norm_le_of_forall_le (by positivity) fun i ↦ ?_).trans_lt (by linarith : L + ε / 2 < L + ε))
    rw [lp.coeFn_add, lp.coeFn_neg, Pi.add_apply, Pi.neg_apply]
    by_cases hi : i ∈ S
    · simpa [y, hi] using hi.le
    · simpa [y, hi] using (by positivity : (0 : ℝ) ≤ L + ε / 2)
  · -- every representative `a + z`, `z ∈ c₀`, has norm at least `L`
    rw [TwoSidedIdeal.Quotient.norm_mk_eq]
    refine le_csInf ⟨‖a + 0‖, 0, (nullIdeal A l).zero_mem, rfl⟩ ?_
    rintro _ ⟨z, hz, rfl⟩
    refine le_of_forall_pos_le_add fun ε hε ↦ limsup_le_of_le hcobdd ?_
    filter_upwards [Metric.tendsto_nhds.1 (mem_nullIdeal.1 hz) ε hε] with i hi
    rw [Real.dist_eq, sub_zero, abs_norm] at hi
    have h := norm_apply_le_norm ENNReal.top_ne_zero (a + z) i
    calc ‖a i‖ ≤ ‖a i + z i‖ + ‖z i‖ := by simpa using norm_sub_le (a i + z i) (z i)
      _ ≤ ‖a + z‖ + ε := add_le_add (by simpa using h) hi.le

/-- If the quotient norm of `a` modulo `lp.nullIdeal A l` is strictly less than `ε`, then
`‖a i‖ < ε` eventually along `l`. -/
theorem eventually_norm_lt_of_norm_mk_nullIdeal_lt {l : Filter ι} (a : lp A ∞) {ε : ℝ}
    (ha : ‖TwoSidedIdeal.Quotient.mk (nullIdeal A l) a‖ < ε) : ∀ᶠ i in l, ‖a i‖ < ε := by
  rcases eq_or_neBot l with rfl | hl
  · simp
  rw [norm_mk_nullIdeal] at ha
  exact eventually_lt_of_limsup_lt ha
    (isBoundedUnder_of ⟨‖a‖, fun i ↦ norm_apply_le_norm ENNReal.top_ne_zero a i⟩)

/-- **Ultralimit norm convergence.** Along an ultrafilter `ω`, the coordinate norms `‖a i‖` of any
bounded family `a : lp A ∞` converge to the quotient norm of `a` modulo `lp.nullIdeal A ω`. -/
theorem tendsto_norm_mk_nullIdeal (ω : Ultrafilter ι) (a : lp A ∞) :
    Tendsto (fun i ↦ ‖a i‖) ω (𝓝 ‖TwoSidedIdeal.Quotient.mk (nullIdeal A ω) a‖) := by
  have hmem : Set.Icc 0 ‖a‖ ∈ ω.map (fun i ↦ ‖a i‖) :=
    Ultrafilter.mem_map.2 <| Eventually.of_forall fun i ↦
      ⟨norm_nonneg _, norm_apply_le_norm ENNReal.top_ne_zero a i⟩
  obtain ⟨L, _, hL⟩ := isCompact_Icc.ultrafilter_le_nhds (ω.map (fun i ↦ ‖a i‖))
    (le_principal_iff.2 hmem)
  have htend : Tendsto (fun i ↦ ‖a i‖) ω (𝓝 L) := hL
  rwa [norm_mk_nullIdeal (l := (ω : Filter ι)) a, htend.limsup_eq]

/-- **Ultralimit norm formula.** For an ultrafilter `ω`, the quotient norm of the class of `a`
modulo `lp.nullIdeal A ω` is `lim_ω ‖a i‖`. -/
theorem norm_mk_nullIdeal_ultrafilter (ω : Ultrafilter ι) (a : lp A ∞) :
    ‖TwoSidedIdeal.Quotient.mk (nullIdeal A ω) a‖ = limUnder (ω : Filter ι) (fun i ↦ ‖a i‖) :=
  (tendsto_norm_mk_nullIdeal ω a).limUnder_eq.symm

/-- **Norm-attaining bounded representative.** Over `ℝ`, every element `x` of
`lp A ∞ ⧸ lp.nullIdeal A l` admits a representative `a : lp A ∞` with `‖a‖ = ‖x‖`. -/
theorem exists_mk_nullIdeal_eq_and_norm_eq [∀ i, NormedSpace ℝ (A i)] (l : Filter ι)
    (x : lp A ∞ ⧸ nullIdeal A l) :
    ∃ a : lp A ∞, TwoSidedIdeal.Quotient.mk (nullIdeal A l) a = x ∧ ‖a‖ = ‖x‖ := by
  obtain ⟨b, rfl⟩ := TwoSidedIdeal.Quotient.mk_surjective (nullIdeal A l) x
  set r := ‖TwoSidedIdeal.Quotient.mk (nullIdeal A l) b‖
  have hr : 0 ≤ r := norm_nonneg _
  have hrad_le (i : ι) : ‖TauCeti.radialRetraction r (b i)‖ ≤ r :=
    (TauCeti.norm_radialRetraction hr (b i)).trans_le (min_le_right _ _)
  let a : lp A ∞ := ⟨fun i ↦ TauCeti.radialRetraction r (b i),
    memℓp_infty ⟨r, by rintro _ ⟨i, rfl⟩; exact hrad_le i⟩⟩
  have ha_mk : TwoSidedIdeal.Quotient.mk (nullIdeal A l) a =
      TwoSidedIdeal.Quotient.mk (nullIdeal A l) b := by
    rw [mk_nullIdeal_eq_mk_iff]
    refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
    filter_upwards [eventually_norm_lt_of_norm_mk_nullIdeal_lt b (by linarith : r < r + ε)]
      with i hi
    have ha_i : a i = TauCeti.radialRetraction r (b i) := rfl
    rw [Real.dist_eq, sub_zero, abs_norm, ha_i, norm_sub_rev,
      TauCeti.norm_sub_radialRetraction hr (b i)]
    exact max_lt (by linarith) hε
  refine ⟨a, ha_mk, le_antisymm (norm_le_of_forall_le hr hrad_le) ?_⟩
  simpa [ha_mk, r] using TwoSidedIdeal.Quotient.norm_mk_le (nullIdeal A l) a

variable (A) in
/-- The `c₀` ideal of the bounded product `lp A ∞`: the bounded families whose coordinate norms
tend to `0` along the cofinite filter. -/
abbrev c0Ideal : TwoSidedIdeal (lp A ∞) := nullIdeal A cofinite

/-- A bounded family lies in the `c₀` ideal when its coordinate norms tend to `0` along the
cofinite filter. -/
theorem mem_c0Ideal {a : lp A ∞} :
    a ∈ c0Ideal A ↔ Tendsto (fun i ↦ ‖a i‖) cofinite (𝓝 0) := mem_nullIdeal

variable (A) in
/-- The `c₀` ideal is closed in the bounded product: a uniform limit of families vanishing at
infinity vanishes at infinity. -/
theorem isClosed_c0Ideal : IsClosed (c0Ideal A : Set (lp A ∞)) := isClosed_nullIdeal A cofinite

/-- The `c₀` ideal is closed under `star`. -/
theorem star_mem_c0Ideal [∀ i, StarAddMonoid (A i)] [∀ i, NormedStarGroup (A i)] {a : lp A ∞}
    (ha : a ∈ c0Ideal A) : star a ∈ c0Ideal A := star_mem_nullIdeal ha

/-- **The quotient norm of the bounded product by the `c₀` ideal** is the limit superior of the
coordinate norms along the cofinite filter. For a finite index type both sides are `0`. -/
theorem norm_mk_c0Ideal (a : lp A ∞) :
    ‖TwoSidedIdeal.Quotient.mk (c0Ideal A) a‖ = limsup (fun i ↦ ‖a i‖) cofinite :=
  norm_mk_nullIdeal a

/-- A bounded family of norm-one elements has quotient norm one modulo the `c₀` ideal. -/
theorem norm_mk_c0Ideal_eq_one_of_forall_norm_eq_one [Infinite ι] (a : lp A ∞)
    (ha : ∀ i, ‖a i‖ = 1) : ‖TwoSidedIdeal.Quotient.mk (c0Ideal A) a‖ = 1 := by
  simp [norm_mk_c0Ideal, ha]

end lp

namespace lp

variable {ι : Type*} {A : ι → Type*} [∀ i, NormedRing (A i)] [∀ i, NormOneClass (A i)]
  [Infinite ι]

/-- Over an infinite index type, the unit of the quotient of a bounded product of normed rings
with `‖1‖ = 1` by the `c₀` ideal has norm one. -/
instance normOneClass_quotient_c0Ideal : NormOneClass (lp A ∞ ⧸ c0Ideal A) :=
  ⟨by simpa using norm_mk_c0Ideal_eq_one_of_forall_norm_eq_one (A := A) 1 fun _ ↦ by simp⟩

/-- The quotient of a bounded product of normed rings with `‖1‖ = 1`, over an infinite index type,
by the `c₀` ideal is nonzero. -/
instance nontrivial_quotient_c0Ideal : Nontrivial (lp A ∞ ⧸ c0Ideal A) :=
  NormOneClass.nontrivial

end lp

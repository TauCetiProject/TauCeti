/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UnitDisc.Retraction
public import TauCeti.Analysis.Complex.UnitDisc.Subdisc
public import TauCeti.Geometry.Symplectic.Manifold.SectionZeroCharge
public import TauCeti.Geometry.Symplectic.Manifold.ZeroCharge
import TauCeti.Topology.MetricSpace.Pseudo.Lemmas
import TauCeti.Topology.UnitInterval.Contractible

/-!
# Limits of zero charges along a family of functions or sections

Let `α k : Y → ℂ` be a family of continuous functions along a filter `l`, for instance the framing
sections `α` of a sequence of Seiberg–Witten solutions, and let `Z ⊆ Y`. The zero charges
`ContinuousMap.zeroCharge (α k) σ` of discs `σ : 𝔻 → Y` count the zeros of `α k ∘ σ`. In the limit
the zeros of `α k` concentrate on `Z`, and the integers to keep are the eventual values of these
charges. This file constructs those eventual values and proves that they obey the laws of a
positive cohomology assignment to `Z` (`TauCeti.PositiveCohomologyAssignment`) other than
positivity.

Away from `σ⁻¹(Z)` nothing controls the zeros of `α k ∘ σ` near the boundary of `𝔻`, so the charge
is read on a closed subdisc. For `0 ≤ ρ < 1` let `D_ρ : 𝔻 → 𝔻` be the radial retraction onto the
closed disc of radius `ρ` (`TauCeti.Complex.UnitDisc.discRetraction`). If `σ⁻¹(Z)` lies in the open
disc of radius `ρ₀ < ρ`, the disc `σ ∘ D_ρ` has compact image, it agrees with `σ` near `σ⁻¹(Z)`, and
it is what the charge reads.

The family is a **zero-charge limit** with support `Z` (`TauCeti.IsZeroChargeLimit`) if

* **vacuum**: on every compact set missing `Z`, the functions `α k` eventually have no zero; and
* **stabilization**: for every disc `σ` with `σ⁻¹(Z)` in the open disc of radius `ρ₀ < ρ < 1`, the
  zero charges of `σ ∘ D_ρ` are eventually constant.

The **limit zero charge** `TauCeti.limitZeroCharge l α Z σ` is then the eventual value of the
zero charges of `σ ∘ D_ρ`. It does not depend on `ρ`
(`TauCeti.IsZeroChargeLimit.eventually_zeroCharge_eq_limitZeroCharge`): by vacuum, the zeros of
`α k ∘ σ ∘ D_ρ` eventually lie in the disc of radius `ρ₀`, where the retractions do not move
anything. The same localization gives the laws, for discs with compact `σ⁻¹(Z)`:

* **vacuum**: the limit zero charge of a disc missing `Z` is zero
  (`TauCeti.IsZeroChargeLimit.limitZeroCharge_eq_zero`);
* **homotopy**: it is constant along a homotopy with compact total preimage of `Z`
  (`TauCeti.IsZeroChargeLimit.limitZeroCharge_eq_of_homotopy`);
* **degree**: it multiplies by the degree of a proper reparametrization `θ : 𝔻 → 𝔻`
  (`TauCeti.IsZeroChargeLimit.limitZeroCharge_comp`);
* **additivity**: it is the sum of the limit zero charges of finitely many disjoint round subdiscs
  containing `σ⁻¹(Z)`, the empty family included
  (`TauCeti.IsZeroChargeLimit.limitZeroCharge_eq_sum`).

On an almost complex manifold, a zero-charge limit whose limit zero charges are positive on
nonconstant pseudoholomorphic discs meeting `Z` gives a positive cohomology assignment to `Z`
(`TauCeti.PositiveCohomologyAssignment.ofIsZeroChargeLimit`). Positivity is not a consequence of
the limit: it comes from the equations the family solves.

A constant family `α k = f` is a zero-charge limit with support `f⁻¹(0)`
(`TauCeti.isZeroChargeLimit_const`), whose limit zero charge is the zero charge of `f`
(`TauCeti.limitZeroCharge_const`).

**Sections of a line bundle.** On a four-manifold the framing `α` of a Seiberg–Witten solution is
a section of a complex line bundle `L`, not a function. For a family of continuous maps
`s k : Y → L` to its total space, the zero charges of discs are
`ContinuousMap.sectionZeroCharge (s k) σ`, and the same two conditions define a **section
zero-charge limit** (`TauCeti.IsSectionZeroChargeLimit`) and its **limit zero charge**
(`TauCeti.limitSectionZeroCharge`). Its laws are not proved again: along a disc `σ`, or along a
homotopy `F : [0, 1] × 𝔻 → Y`, the bundle has a frame, since the domain is contractible, and in
it `s k` becomes a function `c k`. These functions form a zero-charge limit with support
`σ⁻¹(Z)`, respectively `F⁻¹(Z)`, with the same limit zero charges
(`TauCeti.IsSectionZeroChargeLimit.exists_isZeroChargeLimit`), and each law for `s` is the law for
`c`. So a section zero-charge limit with positive charges on pseudoholomorphic discs also gives a
positive cohomology assignment (`TauCeti.PositiveCohomologyAssignment.ofIsSectionZeroChargeLimit`).

## Main definitions

* `TauCeti.limitZeroCharge l α Z σ`: the eventual zero charge of `σ` along the family `α`.
* `TauCeti.IsZeroChargeLimit l α Z`: the family `α` has vacuum off `Z` and stable zero charges.
* `TauCeti.PositiveCohomologyAssignment.ofIsZeroChargeLimit`: the positive cohomology assignment of
  a zero-charge limit with positive charges on pseudoholomorphic discs.
* `TauCeti.limitSectionZeroCharge l s Z σ`, `TauCeti.IsSectionZeroChargeLimit l s Z`,
  `TauCeti.PositiveCohomologyAssignment.ofIsSectionZeroChargeLimit`: the same for a family of
  sections of a complex line bundle.

## Main results

* `TauCeti.IsZeroChargeLimit.limitZeroCharge_eq_zero`,
  `TauCeti.IsZeroChargeLimit.limitZeroCharge_eq_of_homotopy`,
  `TauCeti.IsZeroChargeLimit.limitZeroCharge_comp`,
  `TauCeti.IsZeroChargeLimit.limitZeroCharge_eq_sum`: the vacuum, homotopy, degree and additivity
  laws of the limit zero charge.
* `TauCeti.IsSectionZeroChargeLimit.exists_isZeroChargeLimit`: along a map from a contractible
  space, a section zero-charge limit is a zero-charge limit of functions.
* `TauCeti.IsSectionZeroChargeLimit.limitSectionZeroCharge_eq_zero`,
  `TauCeti.IsSectionZeroChargeLimit.limitSectionZeroCharge_eq_of_homotopy`,
  `TauCeti.IsSectionZeroChargeLimit.limitSectionZeroCharge_comp`,
  `TauCeti.IsSectionZeroChargeLimit.limitSectionZeroCharge_eq_sum`: the same laws for sections.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Proposition 5.6 and Section 6.
-/

public section

noncomputable section

open Bundle Filter Metric Set Topology
open TauCeti.Complex.UnitDisc
open Complex.UnitDisc (exists_forall_norm_lt_of_isCompact isOpen_setOf_norm_lt)
open scoped Complex.UnitDisc Manifold ContDiff

namespace TauCeti

variable {ι Y : Type*} [TopologicalSpace Y] {l : Filter ι} {α : ι → C(Y, ℂ)} {Z : Set Y}

/-! ### Localization of zeros -/

/-- **Zeros localize near `Z`.** Suppose that on every compact set missing `Z` the functions `α k`
eventually have no zero. Let `σ : X → Y` be continuous, `A ⊆ X` compact and `N ⊆ X` open,
containing every point of `A` that `σ` sends into `Z`. Then eventually every zero of `α k ∘ σ` in
`A` lies in `N`. -/
theorem eventually_forall_mem_of_apply_eq_zero {X : Type*} [TopologicalSpace X]
    (hne : ∀ ⦃K : Set Y⦄, IsCompact K → Disjoint K Z → ∀ᶠ k in l, ∀ y ∈ K, α k y ≠ 0)
    {σ : C(X, Y)} {A N : Set X} (hA : IsCompact A) (hN : IsOpen N)
    (hAN : ∀ x ∈ A, σ x ∈ Z → x ∈ N) :
    ∀ᶠ k in l, ∀ x ∈ A, α k (σ x) = 0 → x ∈ N := by
  have hK : Disjoint (σ '' (A \ N)) Z := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, ⟨hxA, hxN⟩, rfl⟩ hxZ
    exact hxN (hAN x hxA hxZ)
  filter_upwards [hne ((hA.diff hN).image σ.continuous) hK] with k hk x hx hzero
  by_contra hxN
  exact hk _ ⟨x, ⟨hx, hxN⟩, rfl⟩ hzero

/-- **Zeros of a disc cut off at radius `ρ`.** Suppose that on every compact set missing `Z` the
functions `α k` eventually have no zero, and let `N ⊆ 𝔻` be an open set of points of norm less than
`ρ` containing every point that `σ` sends into `Z`. Then eventually every zero of
`α k ∘ σ ∘ D_ρ` lies in `N`, where `D_ρ` is the radial retraction onto the closed disc of
radius `ρ`. -/
theorem eventually_forall_mem_of_apply_discRetraction_eq_zero
    (hne : ∀ ⦃K : Set Y⦄, IsCompact K → Disjoint K Z → ∀ᶠ k in l, ∀ y ∈ K, α k y ≠ 0)
    {σ : C(𝔻, Y)} {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ₁ : ρ < 1) {N : Set 𝔻} (hN : IsOpen N)
    (hNρ : ∀ z ∈ N, ‖(z : ℂ)‖ < ρ) (hσN : ∀ z, σ z ∈ Z → z ∈ N) :
    ∀ᶠ k in l, ∀ z, α k (σ (discRetraction ρ hρ hρ₁ z)) = 0 → z ∈ N := by
  filter_upwards [eventually_forall_mem_of_apply_eq_zero hne (σ := σ)
    (Complex.UnitDisc.isCompact_setOf_norm_le hρ₁) hN fun z _ hz ↦ hσN z hz] with k hk z hz
  have hmem := hk _ (norm_coe_discRetraction_apply_le z) hz
  rwa [(discRetraction_apply_eq_and_norm_lt (hNρ _ hmem) le_rfl).1] at hmem

/-- If every zero of `f ∘ σ` has norm less than `s < 1`, the zeros of `f ∘ σ` form a compact set. -/
private theorem isCompact_preimage_zero_of_forall_norm_lt {f : C(Y, ℂ)} {σ : C(𝔻, Y)} {s : ℝ}
    (hs : s < 1) (h : ∀ z, f (σ z) = 0 → ‖(z : ℂ)‖ < s) : IsCompact (σ ⁻¹' (f ⁻¹' {0})) :=
  (Complex.UnitDisc.isCompact_setOf_norm_le hs).of_isClosed_subset
    ((isClosed_singleton.preimage f.continuous).preimage σ.continuous) fun z hz ↦ (h z hz).le

/-! ### The limit zero charge -/

open scoped Classical in
/-- The **limit zero charge** of a disc `σ : 𝔻 → Y` along a family of continuous functions
`α k : Y → ℂ`, with support `Z`: the eventual value along `l` of the zero charges of
`σ ∘ D_ρ`, where `D_ρ` is the radial retraction onto the closed disc of radius `ρ`, chosen
between `1` and a radius `ρ₀` with `σ⁻¹(Z)` in the open disc of radius `ρ₀`. For a zero-charge
limit this value exists and does not depend on the choice of `ρ`
(`TauCeti.IsZeroChargeLimit.eventually_zeroCharge_eq_limitZeroCharge`). It is `0` when no such
`ρ₀` exists. -/
def limitZeroCharge (l : Filter ι) (α : ι → C(Y, ℂ)) (Z : Set Y) (σ : C(𝔻, Y)) : ℤ :=
  if h : ∃ ρ₀, 0 ≤ ρ₀ ∧ ρ₀ < 1 ∧ ∀ z : 𝔻, σ z ∈ Z → ‖(z : ℂ)‖ < ρ₀ then
    limUnder l fun k ↦ (α k).zeroCharge (σ.comp (discRetraction ((h.choose + 1) / 2)
      (by linarith [h.choose_spec.1]) (by linarith [h.choose_spec.2.1])))
  else 0

/-- A family of continuous functions `α k : Y → ℂ` along a filter `l` is a **zero-charge limit
with support `Z`** if it is eventually nonvanishing on every compact set missing `Z`, and if the
zero charges of every disc cut off at a radius `ρ < 1` are eventually constant, as soon as the
disc sends no point of norm at least `ρ₀ < ρ` into `Z`. -/
structure IsZeroChargeLimit (l : Filter ι) (α : ι → C(Y, ℂ)) (Z : Set Y) : Prop where
  /-- On every compact set missing `Z`, the functions `α k` eventually have no zero. -/
  eventually_ne_zero ⦃K : Set Y⦄ : IsCompact K → Disjoint K Z → ∀ᶠ k in l, ∀ y ∈ K, α k y ≠ 0
  /-- The zero charges of a disc cut off at radius `ρ` are eventually constant, if the disc sends
  no point of norm at least `ρ₀ < ρ` into `Z`. -/
  exists_eventually_zeroCharge_eq (σ : C(𝔻, Y)) {ρ₀ ρ : ℝ} (hρ : 0 ≤ ρ) (hρ₁ : ρ < 1)
    (hρ₀ : ρ₀ < ρ) (hσ : ∀ z : 𝔻, σ z ∈ Z → ‖(z : ℂ)‖ < ρ₀) :
    ∃ n : ℤ, ∀ᶠ k in l, (α k).zeroCharge (σ.comp (discRetraction ρ hρ hρ₁)) = n

/-- Cutting off a disc `σ` at radius `ρ` and then precomposing with a disc map `s`, or precomposing
`σ` with `s` and then cutting off at radius `t`, gives discs with the same zero charge, as long as
the zeros of both lie where neither retraction moves anything. Precisely: `N ⊆ 𝔻` consists of
points of norm less than `ρ`, `s` sends only points of norm less than `t₀ ≤ t` into `N`, and the
zeros of `f ∘ σ ∘ D_ρ`, and those of `f ∘ σ ∘ s` of norm at most `t`, lie in `N`. -/
private theorem zeroCharge_comp_discRetraction_comp_eq {f : C(Y, ℂ)} {σ : C(𝔻, Y)}
    {s : C(𝔻, 𝔻)} {ρ t t₀ : ℝ} (hρ : 0 ≤ ρ) (hρ₁ : ρ < 1) (ht : 0 ≤ t) (ht₁ : t < 1)
    (ht₀ : t₀ ≤ t) {N : Set 𝔻} (hNρ : ∀ z ∈ N, ‖(z : ℂ)‖ < ρ)
    (hsN : ∀ w : 𝔻, s w ∈ N → ‖(w : ℂ)‖ < t₀)
    (hσ : ∀ z, f (σ (discRetraction ρ hρ hρ₁ z)) = 0 → z ∈ N)
    (hσs : ∀ w : 𝔻, ‖(w : ℂ)‖ ≤ t → f (σ (s w)) = 0 → s w ∈ N) :
    f.zeroCharge ((σ.comp (discRetraction ρ hρ hρ₁)).comp s) =
      f.zeroCharge ((σ.comp s).comp (discRetraction t ht ht₁)) := by
  refine ContinuousMap.zeroCharge_congr
    (W := {w : 𝔻 | ‖(s w : ℂ)‖ < ρ} ∩ {w : 𝔻 | ‖(w : ℂ)‖ < t₀})
    (((isOpen_setOf_norm_lt ρ).preimage s.continuous).inter (isOpen_setOf_norm_lt _))
    (fun w hw ↦ ?_) (fun w hw ↦ ?_) fun w hw ↦ ?_
  · simp only [ContinuousMap.comp_apply]
    rw [discRetraction_apply_of_norm_le hw.1.le,
      discRetraction_apply_of_norm_le (hw.2.le.trans ht₀)]
  · have hwN := hσ (s w) hw
    exact ⟨hNρ _ hwN, hsN w hwN⟩
  · have hwN := hσs _ (norm_coe_discRetraction_apply_le w) hw
    obtain ⟨hDw, hw'⟩ := discRetraction_apply_eq_and_norm_lt (hsN _ hwN) ht₀
    rw [hDw] at hwN
    exact ⟨hNρ _ hwN, hw'⟩

namespace IsZeroChargeLimit

variable (h : IsZeroChargeLimit l α Z)
include h

/-- The zero charges of a disc cut off at two radii `ρ` and `ρ'` eventually agree, if the disc
sends no point of norm at least `ρ₀ < ρ, ρ'` into `Z`. -/
private theorem eventually_zeroCharge_comp_discRetraction_eq {σ : C(𝔻, Y)} {ρ₀ ρ ρ' : ℝ}
    (hρ : 0 ≤ ρ) (hρ₁ : ρ < 1) (hρ' : 0 ≤ ρ') (hρ'₁ : ρ' < 1) (hρ₀ : ρ₀ < ρ) (hρ₀' : ρ₀ < ρ')
    (hσ : ∀ z : 𝔻, σ z ∈ Z → ‖(z : ℂ)‖ < ρ₀) :
    ∀ᶠ k in l, (α k).zeroCharge (σ.comp (discRetraction ρ hρ hρ₁)) =
      (α k).zeroCharge (σ.comp (discRetraction ρ' hρ' hρ'₁)) := by
  filter_upwards [eventually_forall_mem_of_apply_discRetraction_eq_zero h.eventually_ne_zero hρ
      hρ₁ (isOpen_setOf_norm_lt ρ₀) (fun z hz ↦ hz.trans hρ₀) hσ,
    eventually_forall_mem_of_apply_discRetraction_eq_zero h.eventually_ne_zero hρ' hρ'₁
      (isOpen_setOf_norm_lt ρ₀) (fun z hz ↦ hz.trans hρ₀') hσ] with k hk hk'
  refine ContinuousMap.zeroCharge_congr (isOpen_setOf_norm_lt ρ₀) (fun z hz ↦ ?_) hk hk'
  simp only [ContinuousMap.comp_apply]
  rw [discRetraction_apply_of_norm_le ((le_of_lt hz).trans hρ₀.le),
    discRetraction_apply_of_norm_le ((le_of_lt hz).trans hρ₀'.le)]

/-- **The limit zero charge is the eventual zero charge.** If the zero charges of `σ` cut off at
radius `ρ < 1` are eventually `n`, and `σ` sends no point of norm at least `ρ₀ < ρ` into `Z`, then
the limit zero charge of `σ` is `n`. -/
theorem limitZeroCharge_eq_of_eventually [l.NeBot] {σ : C(𝔻, Y)} {ρ₀ ρ : ℝ} (hρ : 0 ≤ ρ)
    (hρ₁ : ρ < 1) (hρ₀ : ρ₀ < ρ) (hσ : ∀ z : 𝔻, σ z ∈ Z → ‖(z : ℂ)‖ < ρ₀) {n : ℤ}
    (hn : ∀ᶠ k in l, (α k).zeroCharge (σ.comp (discRetraction ρ hρ hρ₁)) = n) :
    limitZeroCharge l α Z σ = n := by
  have hex : ∃ ρ₀, 0 ≤ ρ₀ ∧ ρ₀ < 1 ∧ ∀ z : 𝔻, σ z ∈ Z → ‖(z : ℂ)‖ < ρ₀ :=
    ⟨ρ, hρ, hρ₁, fun z hz ↦ (hσ z hz).trans hρ₀⟩
  obtain ⟨hc, hc₁, hcσ⟩ := hex.choose_spec
  rw [limitZeroCharge, dite_eq_left hex]
  refine Tendsto.limUnder_eq ((tendsto_pure.2 ?_).mono_right (pure_le_nhds n))
  -- Both cutoff radii lie above `min ρ₀ c`, where `c` is the radius chosen in the definition.
  filter_upwards [hn, h.eventually_zeroCharge_comp_discRetraction_eq (ρ₀ := min ρ₀ hex.choose)
    (ρ := (hex.choose + 1) / 2) (by linarith) (by linarith) hρ hρ₁
    (by linarith [min_le_right ρ₀ hex.choose])
    ((min_le_left _ _).trans_lt hρ₀) fun z hz ↦ lt_min (hσ z hz) (hcσ z hz)] with k hk hk'
  rw [hk', hk]

/-- **The zero charges of a disc converge to its limit zero charge.** If `σ` sends no point of norm
at least `ρ₀ < ρ` into `Z`, then the zero charges of `σ` cut off at radius `ρ < 1` are eventually
the limit zero charge of `σ`. -/
theorem eventually_zeroCharge_eq_limitZeroCharge [l.NeBot] {σ : C(𝔻, Y)} {ρ₀ ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ₁ : ρ < 1) (hρ₀ : ρ₀ < ρ) (hσ : ∀ z : 𝔻, σ z ∈ Z → ‖(z : ℂ)‖ < ρ₀) :
    ∀ᶠ k in l, (α k).zeroCharge (σ.comp (discRetraction ρ hρ hρ₁)) = limitZeroCharge l α Z σ := by
  obtain ⟨n, hn⟩ := h.exists_eventually_zeroCharge_eq σ hρ hρ₁ hρ₀ hσ
  rwa [h.limitZeroCharge_eq_of_eventually hρ hρ₁ hρ₀ hσ hn]

/-! ### The laws of the limit zero charge -/

/-- **Vacuum.** The limit zero charge of a disc missing `Z` vanishes. -/
theorem limitZeroCharge_eq_zero [l.NeBot] {σ : C(𝔻, Y)} (hσ : ∀ z, σ z ∉ Z) :
    limitZeroCharge l α Z σ = 0 := by
  have hρ : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hρ₁ : (1 / 2 : ℝ) < 1 := by norm_num
  refine h.limitZeroCharge_eq_of_eventually hρ hρ₁ (ρ₀ := 0) (by norm_num)
    (fun z hz ↦ absurd hz (hσ z)) ?_
  filter_upwards [eventually_forall_mem_of_apply_discRetraction_eq_zero h.eventually_ne_zero hρ hρ₁
    isOpen_empty (fun _ hz ↦ hz.elim) fun z hz ↦ absurd hz (hσ z)] with k hk
  exact ContinuousMap.zeroCharge_eq_zero_of_forall_ne_zero fun z hz ↦ hk z hz

/-- **Homotopy invariance.** The limit zero charge is constant along a homotopy of discs whose total
preimage of `Z` in `[0, 1] × 𝔻` is compact. -/
theorem limitZeroCharge_eq_of_homotopy [l.NeBot] {σ₀ σ₁ : C(𝔻, Y)} (F : σ₀.Homotopy σ₁)
    (hF : IsCompact ((F : unitInterval × 𝔻 → Y) ⁻¹' Z)) :
    limitZeroCharge l α Z σ₀ = limitZeroCharge l α Z σ₁ := by
  obtain ⟨ρ₀, ρ, hρ₀, hρ₀ρ, hρ₁, hFρ₀⟩ :=
    exists_forall_norm_lt_of_isCompact (hF.image continuous_snd)
  have hρ : 0 ≤ ρ := hρ₀.trans hρ₀ρ.le
  have hFZ (t : unitInterval) (z : 𝔻) (hz : F (t, z) ∈ Z) : ‖(z : ℂ)‖ < ρ₀ :=
    hFρ₀ z ⟨(t, z), hz, rfl⟩
  set D := discRetraction ρ hρ hρ₁
  -- Eventually the zeros of `α k ∘ F` over the closed disc of radius `ρ` have norm less than `ρ₀`.
  have hconf := eventually_forall_mem_of_apply_eq_zero h.eventually_ne_zero
    (σ := F.toContinuousMap) (isCompact_univ.prod (Complex.UnitDisc.isCompact_setOf_norm_le hρ₁))
    (isOpen_univ.prod (isOpen_setOf_norm_lt ρ₀)) fun p _ hp ↦ ⟨mem_univ _, hFZ p.1 p.2 hp⟩
  obtain ⟨k, h₀, h₁, hk⟩ := ((h.eventually_zeroCharge_eq_limitZeroCharge hρ hρ₁ hρ₀ρ
    (σ := σ₀) fun z hz ↦ hFZ 0 z (by simpa using hz)).and
    ((h.eventually_zeroCharge_eq_limitZeroCharge hρ hρ₁ hρ₀ρ (σ := σ₁)
      fun z hz ↦ hFZ 1 z (by simpa using hz)).and hconf)).exists
  rw [← h₀, ← h₁]
  -- The homotopy `F ∘ (id × D)` has compact total preimage of the zeros of `α k`.
  refine ContinuousMap.zeroCharge_eq_of_homotopy (α k) (F.compContinuousMap D) ?_
  refine (isCompact_univ.prod
    (Complex.UnitDisc.isCompact_setOf_norm_le (hρ₀ρ.trans hρ₁))).of_isClosed_subset
    ((isClosed_singleton.preimage (α k).continuous).preimage (F.compContinuousMap D).continuous)
    fun p hp ↦ ⟨mem_univ _, ?_⟩
  have hmem := hk (p.1, D p.2) ⟨mem_univ _, norm_coe_discRetraction_apply_le p.2⟩ hp
  exact (discRetraction_apply_eq_and_norm_lt hmem.2 hρ₀ρ.le).2.le

/-- **The degree law.** For a proper reparametrization `θ : 𝔻 → 𝔻` of a disc `σ` with compact
preimage `σ⁻¹(Z)`, the limit zero charge of `σ ∘ θ` is `deg θ` times that of `σ`, the degree
being taken for any orientation `o` of `𝔻` on both sides. -/
theorem limitZeroCharge_comp [l.NeBot] (o : HomologicalOrientation 𝔻 ℂ 2) {σ : C(𝔻, Y)}
    (hσ : IsCompact (σ ⁻¹' Z)) {θ : C(𝔻, 𝔻)} (hθ : IsProperMap θ) :
    limitZeroCharge l α Z (σ.comp θ) =
      o.degree o Complex.finrank_real_complex θ * limitZeroCharge l α Z σ := by
  obtain ⟨ρ₀, ρ, hρ₀, hρ₀ρ, hρ₁, hσρ₀⟩ := exists_forall_norm_lt_of_isCompact hσ
  have hρ : 0 ≤ ρ := hρ₀.trans hρ₀ρ.le
  -- `θ` sends only a compact set into the closed disc of radius `ρ`; it lies in a disc of radius
  -- `s₀ < s < 1`.
  obtain ⟨s₀, s, hs₀, hs₀s, hs₁, hθs₀⟩ := exists_forall_norm_lt_of_isCompact
    (hθ.isCompact_preimage (Complex.UnitDisc.isCompact_setOf_norm_le hρ₁))
  have hs : 0 ≤ s := hs₀.trans hs₀s.le
  have hθ' (z : 𝔻) (hz : ‖(θ z : ℂ)‖ < ρ₀) : ‖(z : ℂ)‖ < s₀ := hθs₀ z (hz.trans hρ₀ρ).le
  obtain ⟨k, h₁, h₂, h₃, h₄⟩ := ((h.eventually_zeroCharge_eq_limitZeroCharge hρ hρ₁ hρ₀ρ hσρ₀).and
    ((h.eventually_zeroCharge_eq_limitZeroCharge hs hs₁ hs₀s (σ := σ.comp θ)
      fun z hz ↦ hθ' z (hσρ₀ _ hz)).and
    ((eventually_forall_mem_of_apply_discRetraction_eq_zero h.eventually_ne_zero hρ hρ₁
      (isOpen_setOf_norm_lt ρ₀) (fun z hz ↦ hz.trans hρ₀ρ) hσρ₀).and
    (eventually_forall_mem_of_apply_eq_zero h.eventually_ne_zero (σ := σ)
      ((Complex.UnitDisc.isCompact_setOf_norm_le hs₁).image θ.continuous)
      (isOpen_setOf_norm_lt ρ₀) fun z _ hz ↦ hσρ₀ z hz)))).exists
  rw [← h₁, ← h₂, ← ContinuousMap.zeroCharge_comp o
    (isCompact_preimage_zero_of_forall_norm_lt (hρ₀ρ.trans hρ₁) fun z hz ↦ h₃ z hz) hθ]
  -- `σ ∘ θ ∘ D_s` and `σ ∘ D_ρ ∘ θ` agree where `θ` lands in the disc of radius `ρ₀`, inside the
  -- disc of radius `s₀`, which contains the zeros of both.
  exact (zeroCharge_comp_discRetraction_comp_eq (N := {z : 𝔻 | ‖(z : ℂ)‖ < ρ₀}) hρ hρ₁ hs hs₁
    hs₀s.le (fun z hz ↦ hz.trans hρ₀ρ) (fun w hw ↦ hθ' w hw) h₃
    fun w hw hz ↦ h₄ _ ⟨w, hw, rfl⟩ hz).symm

/-- **Additivity.** If finitely many disjoint round discs `B(cᵢ, rᵢ) ⊆ 𝔻` contain the compact
preimage `σ⁻¹(Z)`, the limit zero charge of `σ` is the sum of the limit zero charges of its
restrictions `σ ∘ sᵢ` to them, where `sᵢ = TauCeti.Complex.UnitDisc.subdisc cᵢ rᵢ`. The family may
be empty. -/
theorem limitZeroCharge_eq_sum [l.NeBot] {κ : Type} [Fintype κ] {σ : C(𝔻, Y)}
    (hσ : IsCompact (σ ⁻¹' Z)) (c : κ → ℂ) (r : κ → ℝ) (hc : ∀ i, ‖c i‖ + r i ≤ 1)
    (hr : ∀ i, 0 < r i) (hdisj : Pairwise fun i j ↦ Disjoint (ball (c i) (r i)) (ball (c j) (r j)))
    (hcov : ∀ z, σ z ∈ Z → ∃ i, (z : ℂ) ∈ ball (c i) (r i)) :
    limitZeroCharge l α Z σ =
      ∑ i, limitZeroCharge l α Z (σ.comp (subdisc (c i) (r i) (hc i) (hr i))) := by
  set s := fun i ↦ subdisc (c i) (r i) (hc i) (hr i)
  obtain ⟨ρ₀, ρ, hρ₀, hρ₀ρ, hρ₁, hσρ₀⟩ := exists_forall_norm_lt_of_isCompact hσ
  have hρ : 0 ≤ ρ := hρ₀.trans hρ₀ρ.le
  -- Each restriction `σ ∘ sᵢ` sends no point of norm at least `t₀ᵢ < tᵢ < 1` into `Z`.
  choose t₀ t ht₀ ht₀t ht₁ hσt₀ using fun i ↦ exists_forall_norm_lt_of_isCompact
    (isCompact_subdisc_preimage_of_subset_iUnion hc hr hdisj hσ hcov i)
  have ht (i : κ) : 0 ≤ t i := (ht₀ i).trans (ht₀t i).le
  have ht₀₁ (i : κ) : t₀ i < 1 := (ht₀t i).trans (ht₁ i)
  -- The open set `N` in which the zeros eventually lie: near `σ⁻¹(Z)` in every subdisc.
  set N : Set 𝔻 := {z | ‖(z : ℂ)‖ < ρ₀} ∩ ⋃ i, {z | (z : ℂ) ∈ ball (c i) (r i * t₀ i)}
  have hN : IsOpen N := (isOpen_setOf_norm_lt ρ₀).inter
    (isOpen_iUnion fun i ↦ isOpen_ball.preimage Complex.UnitDisc.continuous_coe)
  have hsN (i : κ) (w : 𝔻) (hw : s i w ∈ N) : ‖(w : ℂ)‖ < t₀ i :=
    (coe_subdisc_mem_ball_mul_iff w (t₀ i)).1 <|
      mem_ball_mul_of_mem_iUnion (fun i ↦ (hr i).le) hdisj (fun i ↦ (ht₀₁ i).le) (by
        obtain ⟨j, hj⟩ := mem_iUnion.1 hw.2
        exact mem_iUnion.2 ⟨j, hj⟩) (mem_range_subdisc.1 ⟨w, rfl⟩)
  have hσN (z : 𝔻) (hz : σ z ∈ Z) : z ∈ N := by
    refine ⟨hσρ₀ z hz, ?_⟩
    obtain ⟨i, hi⟩ := hcov z hz
    obtain ⟨w, rfl⟩ := (mem_range_subdisc (hc := hc i) (hr := hr i)).2 hi
    exact mem_iUnion.2 ⟨i, (coe_subdisc_mem_ball_mul_iff w (t₀ i)).2 (hσt₀ i w hz)⟩
  obtain ⟨k, h₀, hall, hconf, hconf'⟩ := ((h.eventually_zeroCharge_eq_limitZeroCharge hρ hρ₁ hρ₀ρ
    hσρ₀).and ((eventually_all.2 fun i ↦ h.eventually_zeroCharge_eq_limitZeroCharge (ht i) (ht₁ i)
      (ht₀t i) (σ := σ.comp (s i)) (hσt₀ i)).and
    ((eventually_forall_mem_of_apply_discRetraction_eq_zero h.eventually_ne_zero hρ hρ₁ hN
      (fun z hz ↦ hz.1.trans hρ₀ρ) hσN).and
    (eventually_all.2 fun i ↦ eventually_forall_mem_of_apply_eq_zero h.eventually_ne_zero (σ := σ)
      ((Complex.UnitDisc.isCompact_setOf_norm_le (ht₁ i)).image (s i).continuous) hN
      fun z _ hz ↦ hσN z hz)))).exists
  rw [← h₀, ContinuousMap.zeroCharge_eq_sum (isCompact_preimage_zero_of_forall_norm_lt
    (hρ₀ρ.trans hρ₁)
    fun z hz ↦ (hconf z hz).1) c r hc hr hdisj fun z hz ↦ ?_]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← hall i]
    -- On subdisc `i`, the two cut-off discs agree where neither retraction moves anything.
    exact zeroCharge_comp_discRetraction_comp_eq (N := N) hρ hρ₁ (ht i) (ht₁ i) (ht₀t i).le
      (fun z hz ↦ hz.1.trans hρ₀ρ) (hsN i) hconf fun w hw hz ↦ hconf' i _ ⟨w, hw, rfl⟩ hz
  · obtain ⟨j, hj⟩ := mem_iUnion.1 (hconf z hz).2
    exact ⟨j, ball_subset_ball (mul_le_of_le_one_right (hr j).le (ht₀₁ j).le) hj⟩

end IsZeroChargeLimit

/-! ### Constant families -/

/-- A constant family `α k = f` is a zero-charge limit with support the zero set of `f`. -/
theorem isZeroChargeLimit_const (l : Filter ι) (f : C(Y, ℂ)) :
    IsZeroChargeLimit l (fun _ ↦ f) (f ⁻¹' {0}) where
  eventually_ne_zero _ _ hK := Eventually.of_forall fun _ _ hy hfy ↦ Set.disjoint_left.1 hK hy hfy
  exists_eventually_zeroCharge_eq _ _ _ _ _ _ _ := ⟨_, Eventually.of_forall fun _ ↦ rfl⟩

/-- The limit zero charge of a constant family `α k = f` is the zero charge of `f`. -/
theorem limitZeroCharge_const [l.NeBot] {f : C(Y, ℂ)} {σ : C(𝔻, Y)}
    (hσ : IsCompact (σ ⁻¹' (f ⁻¹' {0}))) :
    limitZeroCharge l (fun _ ↦ f) (f ⁻¹' {0}) σ = f.zeroCharge σ := by
  obtain ⟨ρ₀, ρ, hρ₀, hρ₀ρ, hρ₁, hσρ₀⟩ := exists_forall_norm_lt_of_isCompact hσ
  refine (isZeroChargeLimit_const l f).limitZeroCharge_eq_of_eventually (hρ₀.trans hρ₀ρ.le) hρ₁
    hρ₀ρ
    (fun z hz ↦ hσρ₀ z hz) (Eventually.of_forall fun _ ↦ ?_)
  -- `σ ∘ D_ρ` agrees with `σ` on the disc of radius `ρ₀`, which contains the zeros of both.
  refine ContinuousMap.zeroCharge_congr (isOpen_setOf_norm_lt ρ₀) (fun z hz ↦ ?_)
    (fun z hz ↦ ?_) fun z hz ↦ hσρ₀ z hz
  · rw [ContinuousMap.comp_apply, discRetraction_apply_of_norm_le (hz.le.trans hρ₀ρ.le)]
  · exact (discRetraction_apply_eq_and_norm_lt (hσρ₀ _ hz) hρ₀ρ.le).2

/-! ### The positive cohomology assignment of a zero-charge limit -/

section Assignment

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H Y] [IsManifold I ∞ Y]
  {J : SmoothAlmostComplexStructure I Y}

/-- **The positive cohomology assignment of a zero-charge limit.** On an almost complex manifold
`(Y, J)`, the limit zero charges of a zero-charge limit with support `Z` form a positive cohomology
assignment to `Z`, provided they are positive on nonconstant `J`-holomorphic discs meeting `Z`.
The other laws hold for every zero-charge limit; positivity depends on the equations the family
solves. -/
def PositiveCohomologyAssignment.ofIsZeroChargeLimit [l.NeBot] (h : IsZeroChargeLimit l α Z)
    (hpos : ∀ (σ : C(𝔻, Y)), IsCompact (σ ⁻¹' Z) → ∀ u : ℂ → Y, (∀ z : 𝔻, u z = σ z) →
      IsPseudoholomorphicOn (AlmostComplexStructure.ofComplexModule ℂ).constSmooth J u
        (ball 0 1) → (∃ z w, σ z ≠ σ w) → (∃ z, σ z ∈ Z) → 0 < limitZeroCharge l α Z σ) :
    PositiveCohomologyAssignment J Z where
  charge σ _ := limitZeroCharge l α Z σ
  charge_eq_zero _ _ hZ := h.limitZeroCharge_eq_zero hZ
  charge_eq_of_homotopy F hF _ _ := h.limitZeroCharge_eq_of_homotopy F hF
  charge_comp o _ hσ _ hθ _ := h.limitZeroCharge_comp o hσ hθ
  charge_eq_sum _ hσ c r hc hr hdisj hcov _ := h.limitZeroCharge_eq_sum hσ c r hc hr hdisj hcov
  charge_pos σ hσ u hu hhol hnc hZ := hpos σ hσ u hu hhol hnc hZ

/-- The integer of a disc for the positive cohomology assignment of a zero-charge limit is its
limit zero charge. -/
@[simp]
theorem PositiveCohomologyAssignment.charge_ofIsZeroChargeLimit [l.NeBot]
    (h : IsZeroChargeLimit l α Z)
    (hpos : ∀ (σ : C(𝔻, Y)), IsCompact (σ ⁻¹' Z) → ∀ u : ℂ → Y, (∀ z : 𝔻, u z = σ z) →
      IsPseudoholomorphicOn (AlmostComplexStructure.ofComplexModule ℂ).constSmooth J u
        (ball 0 1) → (∃ z w, σ z ≠ σ w) → (∃ z, σ z ∈ Z) → 0 < limitZeroCharge l α Z σ)
    (σ : C(𝔻, Y)) (hσ : IsCompact (σ ⁻¹' Z)) :
    (PositiveCohomologyAssignment.ofIsZeroChargeLimit h hpos).charge σ hσ =
      limitZeroCharge l α Z σ :=
  (rfl)

end Assignment

/-! ### Families of sections of a complex line bundle -/

section Section

variable {L : Y → Type*} [∀ y, AddCommGroup (L y)] [∀ y, Module ℂ (L y)]
  [∀ y, TopologicalSpace (L y)] [TopologicalSpace (TotalSpace ℂ L)] [FiberBundle ℂ L]
  [VectorBundle ℂ ℂ L] [∀ y, IsTopologicalAddGroup (L y)] [∀ y, ContinuousSMul ℂ (L y)]
  {s : ι → C(Y, TotalSpace ℂ L)}

open scoped Classical in
/-- The **limit zero charge** of a disc `σ : 𝔻 → Y` along a family of continuous maps `s k` to the
total space of a complex line bundle `L`, for instance sections, with support `Z`: the eventual
value along `l` of the zero charges `ContinuousMap.sectionZeroCharge (s k)` of `σ ∘ D_ρ`, where
`D_ρ` is the radial retraction onto the closed disc of radius `ρ`, chosen between `1` and a radius
`ρ₀` with `σ⁻¹(Z)` in the open disc of radius `ρ₀`. For a section zero-charge limit this value
exists and does not depend on the choice of `ρ`
(`TauCeti.IsSectionZeroChargeLimit.eventually_sectionZeroCharge_eq_limitSectionZeroCharge`). It
is `0` when no such `ρ₀` exists. -/
def limitSectionZeroCharge (l : Filter ι) (s : ι → C(Y, TotalSpace ℂ L)) (Z : Set Y)
    (σ : C(𝔻, Y)) : ℤ :=
  if h : ∃ ρ₀, 0 ≤ ρ₀ ∧ ρ₀ < 1 ∧ ∀ z : 𝔻, σ z ∈ Z → ‖(z : ℂ)‖ < ρ₀ then
    limUnder l fun k ↦ (s k).sectionZeroCharge (σ.comp (discRetraction ((h.choose + 1) / 2)
      (by linarith [h.choose_spec.1]) (by linarith [h.choose_spec.2.1])))
  else 0

/-- A family of continuous maps `s k` to the total space of a complex line bundle `L` along a filter
`l`, for instance the framing sections of a sequence of Seiberg–Witten solutions, is a **section
zero-charge limit with support `Z`** if it eventually vanishes nowhere on every compact set missing
`Z`, and if the zero charges of every disc cut off at a radius `ρ < 1` are eventually constant, as
soon as the disc sends no point of norm at least `ρ₀ < ρ` into `Z`. -/
structure IsSectionZeroChargeLimit (l : Filter ι) (s : ι → C(Y, TotalSpace ℂ L)) (Z : Set Y) :
    Prop where
  /-- On every compact set missing `Z`, the maps `s k` eventually have no zero. -/
  eventually_ne_zero ⦃K : Set Y⦄ : IsCompact K → Disjoint K Z →
    ∀ᶠ k in l, ∀ y ∈ K, (s k y).snd ≠ 0
  /-- The zero charges of a disc cut off at radius `ρ` are eventually constant, if the disc sends
  no point of norm at least `ρ₀ < ρ` into `Z`. -/
  exists_eventually_sectionZeroCharge_eq (σ : C(𝔻, Y)) {ρ₀ ρ : ℝ} (hρ : 0 ≤ ρ) (hρ₁ : ρ < 1)
    (hρ₀ : ρ₀ < ρ) (hσ : ∀ z : 𝔻, σ z ∈ Z → ‖(z : ℂ)‖ < ρ₀) :
    ∃ n : ℤ, ∀ᶠ k in l, (s k).sectionZeroCharge (σ.comp (discRetraction ρ hρ hρ₁)) = n

/-! #### Pulling back to functions along a map -/

/-- **Limit zero charges along a map.** Let `G : B → Y` be continuous and `c k : B → ℂ` functions
whose zero charges are those of `s k` along `G`. Then the limit zero charge of a disc `G ∘ τ` along
`s` is the limit zero charge of `τ` along `c`, with support `G⁻¹(Z)`. -/
theorem limitSectionZeroCharge_comp_eq_limitZeroCharge {B : Type*} [TopologicalSpace B]
    {G : C(B, Y)} {c : ι → C(B, ℂ)}
    (hc : ∀ k (τ : C(𝔻, B)), (s k).sectionZeroCharge (G.comp τ) = (c k).zeroCharge τ)
    (τ : C(𝔻, B)) :
    limitSectionZeroCharge l s Z (G.comp τ) = limitZeroCharge l c (G ⁻¹' Z) τ := by
  simp only [limitSectionZeroCharge, limitZeroCharge, ContinuousMap.comp_assoc, hc]
  -- The two conditions of the `dite`, `G (τ z) ∈ Z` and `τ z ∈ G ⁻¹' Z`, agree by
  -- `Set.mem_preimage`, which holds by `Iff.rfl`; `simp` cannot rewrite them, since the branches
  -- depend on the proof of the condition.
  rfl

/-- **Pulling back a section zero-charge limit.** Let `G : B → Y` be continuous and `c k : B → ℂ`
functions whose zero charges are those of `s k` along `G`, and which vanish only where `s k ∘ G`
does. If `s` is a section zero-charge limit with support `Z`, then `c` is a zero-charge limit with
support `G⁻¹(Z)`. -/
theorem IsSectionZeroChargeLimit.isZeroChargeLimit (h : IsSectionZeroChargeLimit l s Z)
    {B : Type*} [TopologicalSpace B] {G : C(B, Y)} {c : ι → C(B, ℂ)}
    (hc : ∀ k (τ : C(𝔻, B)), (s k).sectionZeroCharge (G.comp τ) = (c k).zeroCharge τ)
    (hc₀ : ∀ k b, c k b = 0 → (s k (G b)).snd = 0) :
    IsZeroChargeLimit l c (G ⁻¹' Z) where
  eventually_ne_zero K hK hKZ := by
    have hGK : Disjoint (G '' K) Z := Set.disjoint_image_left.2 hKZ
    filter_upwards [h.eventually_ne_zero (hK.image G.continuous) hGK] with k hk b hb hcb
    exact hk _ ⟨b, hb, rfl⟩ (hc₀ k b hcb)
  exists_eventually_zeroCharge_eq τ _ _ hρ hρ₁ hρ₀ hτ := by
    obtain ⟨n, hn⟩ := h.exists_eventually_sectionZeroCharge_eq (G.comp τ) hρ hρ₁ hρ₀ hτ
    refine ⟨n, hn.mono fun k hk ↦ ?_⟩
    rwa [← hc, ← ContinuousMap.comp_assoc]

/-- **A section zero-charge limit along a contractible space is a zero-charge limit.** Along a
continuous map `G : B → Y` from a contractible paracompact R₁ space, for instance a disc or a
cylinder `[0, 1] × 𝔻`, a section zero-charge limit `s` with support `Z` is read through functions
`c k : B → ℂ`, the coordinates of `s k ∘ G` in frames along `G`: they form a zero-charge limit with
support `G⁻¹(Z)`, and the limit zero charge of a disc `G ∘ τ` along `s` is that of `τ` along
`c`. -/
theorem IsSectionZeroChargeLimit.exists_isZeroChargeLimit (h : IsSectionZeroChargeLimit l s Z)
    {B : Type*} [TopologicalSpace B] [R1Space B] [ParacompactSpace B] [ContractibleSpace B]
    (G : C(B, Y)) :
    ∃ c : ι → C(B, ℂ), IsZeroChargeLimit l c (G ⁻¹' Z) ∧
      ∀ τ : C(𝔻, B), limitSectionZeroCharge l s Z (G.comp τ) = limitZeroCharge l c (G ⁻¹' Z) τ := by
  choose c hc hc₀ using fun k ↦ (s k).exists_sectionZeroCharge_comp_eq_zeroCharge G
  exact ⟨c, h.isZeroChargeLimit hc fun k b ↦ (hc₀ k b).1,
    limitSectionZeroCharge_comp_eq_limitZeroCharge hc⟩

/-! #### The laws of the limit zero charge -/

namespace IsSectionZeroChargeLimit

variable (h : IsSectionZeroChargeLimit l s Z)
include h

/-- Along a disc `σ`, a section zero-charge limit is read through a zero-charge limit `c` on `𝔻`
with support `σ⁻¹(Z)`, whose limit zero charge at the identity is that of `σ`. -/
private theorem exists_isZeroChargeLimit_disc (σ : C(𝔻, Y)) :
    ∃ c : ι → C(𝔻, ℂ), IsZeroChargeLimit l c (σ ⁻¹' Z) ∧
      limitSectionZeroCharge l s Z σ = limitZeroCharge l c (σ ⁻¹' Z) (ContinuousMap.id 𝔻) ∧
      ∀ τ : C(𝔻, 𝔻),
        limitSectionZeroCharge l s Z (σ.comp τ) = limitZeroCharge l c (σ ⁻¹' Z) τ := by
  obtain ⟨c, hc, hlim⟩ := h.exists_isZeroChargeLimit σ
  exact ⟨c, hc, by simpa using hlim (ContinuousMap.id 𝔻), hlim⟩

/-- **The zero charges of a disc converge to its limit zero charge.** If `σ` sends no point of norm
at least `ρ₀ < ρ` into `Z`, then the zero charges of `σ` cut off at radius `ρ < 1` are eventually
the limit zero charge of `σ`. -/
theorem eventually_sectionZeroCharge_eq_limitSectionZeroCharge [l.NeBot] {σ : C(𝔻, Y)}
    {ρ₀ ρ : ℝ} (hρ : 0 ≤ ρ) (hρ₁ : ρ < 1) (hρ₀ : ρ₀ < ρ)
    (hσ : ∀ z : 𝔻, σ z ∈ Z → ‖(z : ℂ)‖ < ρ₀) :
    ∀ᶠ k in l, (s k).sectionZeroCharge (σ.comp (discRetraction ρ hρ hρ₁)) =
      limitSectionZeroCharge l s Z σ := by
  -- Read `s k` along `σ` through its coordinate `c k` in a frame, a function on `𝔻`.
  choose c hc hc₀ using fun k ↦ (s k).exists_sectionZeroCharge_comp_eq_zeroCharge σ
  have hid := limitSectionZeroCharge_comp_eq_limitZeroCharge (l := l) (Z := Z) hc
    (ContinuousMap.id 𝔻)
  rw [ContinuousMap.comp_id] at hid
  rw [hid]
  have hcl := h.isZeroChargeLimit hc fun k b ↦ (hc₀ k b).1
  filter_upwards [hcl.eventually_zeroCharge_eq_limitZeroCharge (σ := ContinuousMap.id 𝔻) hρ hρ₁ hρ₀
    hσ] with k hk
  rw [← hk, ContinuousMap.id_comp, ← hc]

/-- **The limit zero charge is the eventual zero charge.** If the zero charges of `σ` cut off at
radius `ρ < 1` are eventually `n`, and `σ` sends no point of norm at least `ρ₀ < ρ` into `Z`, then
the limit zero charge of `σ` is `n`. -/
theorem limitSectionZeroCharge_eq_of_eventually [l.NeBot] {σ : C(𝔻, Y)} {ρ₀ ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ₁ : ρ < 1) (hρ₀ : ρ₀ < ρ) (hσ : ∀ z : 𝔻, σ z ∈ Z → ‖(z : ℂ)‖ < ρ₀) {n : ℤ}
    (hn : ∀ᶠ k in l, (s k).sectionZeroCharge (σ.comp (discRetraction ρ hρ hρ₁)) = n) :
    limitSectionZeroCharge l s Z σ = n := by
  obtain ⟨k, hk, hk'⟩ :=
    (hn.and (h.eventually_sectionZeroCharge_eq_limitSectionZeroCharge hρ hρ₁ hρ₀ hσ)).exists
  rw [← hk', hk]

/-- **Vacuum.** The limit zero charge of a disc missing `Z` vanishes. -/
theorem limitSectionZeroCharge_eq_zero [l.NeBot] {σ : C(𝔻, Y)} (hσ : ∀ z, σ z ∉ Z) :
    limitSectionZeroCharge l s Z σ = 0 := by
  obtain ⟨c, hc, hid, -⟩ := h.exists_isZeroChargeLimit_disc σ
  rw [hid]
  exact hc.limitZeroCharge_eq_zero hσ

/-- **Homotopy invariance.** The limit zero charge is constant along a homotopy of discs whose total
preimage of `Z` in `[0, 1] × 𝔻` is compact. -/
theorem limitSectionZeroCharge_eq_of_homotopy [l.NeBot] {σ₀ σ₁ : C(𝔻, Y)} (F : σ₀.Homotopy σ₁)
    (hF : IsCompact ((F : unitInterval × 𝔻 → Y) ⁻¹' Z)) :
    limitSectionZeroCharge l s Z σ₀ = limitSectionZeroCharge l s Z σ₁ := by
  -- Read `s` along the whole homotopy, on the contractible cylinder `[0, 1] × 𝔻`.
  obtain ⟨c, hc, hlim⟩ := h.exists_isZeroChargeLimit F.toContinuousMap
  let j (t : unitInterval) : C(𝔻, unitInterval × 𝔻) := ⟨fun z ↦ (t, z), by fun_prop⟩
  have hj₀ : F.toContinuousMap.comp (j 0) = σ₀ := ContinuousMap.ext F.apply_zero
  have hj₁ : F.toContinuousMap.comp (j 1) = σ₁ := ContinuousMap.ext F.apply_one
  -- The identity of the cylinder is a homotopy from `j 0` to `j 1`.
  let H : (j 0).Homotopy (j 1) :=
    { toContinuousMap := ContinuousMap.id _
      map_zero_left := fun _ ↦ rfl
      map_one_left := fun _ ↦ rfl }
  have hH := hc.limitZeroCharge_eq_of_homotopy H hF
  rwa [← hlim, ← hlim, hj₀, hj₁] at hH

/-- **The degree law.** For a proper reparametrization `θ : 𝔻 → 𝔻` of a disc `σ` with compact
preimage `σ⁻¹(Z)`, the limit zero charge of `σ ∘ θ` is `deg θ` times that of `σ`, the degree
being taken for any orientation `o` of `𝔻` on both sides. -/
theorem limitSectionZeroCharge_comp [l.NeBot] (o : HomologicalOrientation 𝔻 ℂ 2) {σ : C(𝔻, Y)}
    (hσ : IsCompact (σ ⁻¹' Z)) {θ : C(𝔻, 𝔻)} (hθ : IsProperMap θ) :
    limitSectionZeroCharge l s Z (σ.comp θ) =
      o.degree o Complex.finrank_real_complex θ * limitSectionZeroCharge l s Z σ := by
  obtain ⟨c, hc, hid, hlim⟩ := h.exists_isZeroChargeLimit_disc σ
  rw [hid, hlim]
  simpa using hc.limitZeroCharge_comp o (σ := ContinuousMap.id 𝔻) hσ hθ

/-- **Additivity.** If finitely many disjoint round discs `B(cᵢ, rᵢ) ⊆ 𝔻` contain the compact
preimage `σ⁻¹(Z)`, the limit zero charge of `σ` is the sum of the limit zero charges of its
restrictions `σ ∘ sᵢ` to them, where `sᵢ = TauCeti.Complex.UnitDisc.subdisc cᵢ rᵢ`. The family may
be empty. -/
theorem limitSectionZeroCharge_eq_sum [l.NeBot] {κ : Type} [Fintype κ] {σ : C(𝔻, Y)}
    (hσ : IsCompact (σ ⁻¹' Z)) (c : κ → ℂ) (r : κ → ℝ) (hc : ∀ i, ‖c i‖ + r i ≤ 1)
    (hr : ∀ i, 0 < r i) (hdisj : Pairwise fun i j ↦ Disjoint (ball (c i) (r i)) (ball (c j) (r j)))
    (hcov : ∀ z, σ z ∈ Z → ∃ i, (z : ℂ) ∈ ball (c i) (r i)) :
    limitSectionZeroCharge l s Z σ =
      ∑ i, limitSectionZeroCharge l s Z (σ.comp (subdisc (c i) (r i) (hc i) (hr i))) := by
  obtain ⟨a, ha, hid, hlim⟩ := h.exists_isZeroChargeLimit_disc σ
  rw [hid, ha.limitZeroCharge_eq_sum (σ := ContinuousMap.id 𝔻) hσ c r hc hr hdisj hcov]
  simp only [ContinuousMap.id_comp, hlim]

end IsSectionZeroChargeLimit

/-! #### Constant families -/

/-- A constant family `s k = t` is a section zero-charge limit with support the zero set of `t`. -/
theorem isSectionZeroChargeLimit_const (l : Filter ι) (t : C(Y, TotalSpace ℂ L)) :
    IsSectionZeroChargeLimit l (fun _ ↦ t) {y | (t y).snd = 0} where
  eventually_ne_zero _ _ hK := Eventually.of_forall fun _ _ hy hty ↦ Set.disjoint_left.1 hK hy hty
  exists_eventually_sectionZeroCharge_eq _ _ _ _ _ _ _ := ⟨_, Eventually.of_forall fun _ ↦ rfl⟩

/-- The limit zero charge of a constant family `s k = t` is the zero charge of `t`. -/
theorem limitSectionZeroCharge_const [l.NeBot] {t : C(Y, TotalSpace ℂ L)} {σ : C(𝔻, Y)}
    (hσ : IsCompact (σ ⁻¹' {y | (t y).snd = 0})) :
    limitSectionZeroCharge l (fun _ ↦ t) {y | (t y).snd = 0} σ = t.sectionZeroCharge σ := by
  -- Read `t` along `σ` through its coordinate `c` in a frame, a function on `𝔻`.
  obtain ⟨c, hc, hc₀⟩ := t.exists_sectionZeroCharge_comp_eq_zeroCharge σ
  have hZ : σ ⁻¹' {y | (t y).snd = 0} = c ⁻¹' {0} := by
    ext z
    simp [hc₀]
  have h := limitSectionZeroCharge_comp_eq_limitZeroCharge (l := l) (s := fun _ ↦ t)
    (Z := {y | (t y).snd = 0}) (fun _ ↦ hc) (ContinuousMap.id 𝔻)
  rw [ContinuousMap.comp_id] at h
  rw [h, hZ, limitZeroCharge_const (σ := ContinuousMap.id 𝔻) (hZ ▸ hσ), ← hc,
    ContinuousMap.comp_id]

/-! #### The positive cohomology assignment of a section zero-charge limit -/

section Assignment

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H Y] [IsManifold I ∞ Y]
  {J : SmoothAlmostComplexStructure I Y}

/-- **The positive cohomology assignment of a section zero-charge limit.** On an almost complex
manifold `(Y, J)`, the limit zero charges of a section zero-charge limit `s` of a complex line
bundle with support `Z` form a positive cohomology assignment to `Z`, provided they are positive on
nonconstant `J`-holomorphic discs meeting `Z`. The other laws hold for every section zero-charge
limit; positivity depends on the equations the family solves. -/
def PositiveCohomologyAssignment.ofIsSectionZeroChargeLimit [l.NeBot]
    (h : IsSectionZeroChargeLimit l s Z)
    (hpos : ∀ (σ : C(𝔻, Y)), IsCompact (σ ⁻¹' Z) → ∀ u : ℂ → Y, (∀ z : 𝔻, u z = σ z) →
      IsPseudoholomorphicOn (AlmostComplexStructure.ofComplexModule ℂ).constSmooth J u
        (ball 0 1) → (∃ z w, σ z ≠ σ w) → (∃ z, σ z ∈ Z) → 0 < limitSectionZeroCharge l s Z σ) :
    PositiveCohomologyAssignment J Z where
  charge σ _ := limitSectionZeroCharge l s Z σ
  charge_eq_zero _ _ hZ := h.limitSectionZeroCharge_eq_zero hZ
  charge_eq_of_homotopy F hF _ _ := h.limitSectionZeroCharge_eq_of_homotopy F hF
  charge_comp o _ hσ _ hθ _ := h.limitSectionZeroCharge_comp o hσ hθ
  charge_eq_sum _ hσ c r hc hr hdisj hcov _ :=
    h.limitSectionZeroCharge_eq_sum hσ c r hc hr hdisj hcov
  charge_pos σ hσ u hu hhol hnc hZ := hpos σ hσ u hu hhol hnc hZ

/-- The integer of a disc for the positive cohomology assignment of a section zero-charge limit is
its limit zero charge. -/
@[simp]
theorem PositiveCohomologyAssignment.charge_ofIsSectionZeroChargeLimit [l.NeBot]
    (h : IsSectionZeroChargeLimit l s Z)
    (hpos : ∀ (σ : C(𝔻, Y)), IsCompact (σ ⁻¹' Z) → ∀ u : ℂ → Y, (∀ z : 𝔻, u z = σ z) →
      IsPseudoholomorphicOn (AlmostComplexStructure.ofComplexModule ℂ).constSmooth J u
        (ball 0 1) → (∃ z w, σ z ≠ σ w) → (∃ z, σ z ∈ Z) → 0 < limitSectionZeroCharge l s Z σ)
    (σ : C(𝔻, Y)) (hσ : IsCompact (σ ⁻¹' Z)) :
    (PositiveCohomologyAssignment.ofIsSectionZeroChargeLimit h hpos).charge σ hσ =
      limitSectionZeroCharge l s Z σ :=
  (rfl)

end Assignment

end Section

end TauCeti

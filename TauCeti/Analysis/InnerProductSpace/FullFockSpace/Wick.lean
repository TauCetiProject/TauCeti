/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.FullFockSpace.Basic
public import TauCeti.Analysis.InnerProductSpace.Positive.VectorFunctional
public import TauCeti.Combinatorics.NoncrossingPartition.Pairing
import TauCeti.Data.Finset.Basic

/-!
# Vacuum state, field operators, and the Wick formula on full Fock space

On the full Fock space `FullFockSpace 𝕜 H` (`𝓕(H)`) over a real or complex inner product space `H`
(`[RCLike 𝕜]`, without requiring `H` to be complete), pairing bounded operators against the unit
vacuum vector `vacuum` defines the positive linear functional `FullFockSpace.vacuumState 𝕜 H`
(`ω_Ω(T) = ⟪Ω, T Ω⟫_𝕜`), and for each vector `h : H` the sum of left creation and left annihilation
defines the bounded self-adjoint *field* (or *position*) operator
`FullFockSpace.field 𝕜 h = creation 𝕜 h + annihilation 𝕜 h` (`s(h) = ℓ(h) + ℓ(h)*`).

Because left annihilation kills the vacuum (`ℓ(g)* Ω = 0`) and satisfies the Cuntz–Toeplitz
identity `ℓ(g)* ℓ(f) = ⟪g, f⟫_𝕜 • 1`, the vacuum expectation of an ordered product of sums
`ℓ(f i) + ℓ(g i)*` satisfies the same quadratic recurrence by the partner of the first position as
weighted noncrossing pairings
(`TauCeti.NoncrossingPartition.sum_isPairing_prod_orderedPairs_eq_sum`).
This yields the **Fock-space vacuum Wick formula**:

`ω_Ω(∏_{i ∈ s} (ℓ(f i) + ℓ(g i)*)) = ∑_{P ∈ NC₂(s)} ∏_{(i, j) ∈ P} ⟪g i, f j⟫_𝕜`.

Specializing to `g = f` gives the noncrossing-pairing expansion for products of self-adjoint field
operators `field 𝕜 (f i)` and, for a single vector `h : H`, the semicircular moment sequence
`ω_Ω(s(h)^n) = ‖h‖^n * catalan (n / 2)` for even `n` and `0` for odd `n`.

## Main definitions

* `TauCeti.FullFockSpace.vacuumState`: the normalized positive linear functional
  `T ↦ ⟪vacuum, T vacuum⟫_𝕜` on `FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H`.
* `TauCeti.FullFockSpace.field`: the self-adjoint field operator
  `field 𝕜 h = creation 𝕜 h + annihilation 𝕜 h` on `FullFockSpace 𝕜 H`.

## Main results

* `TauCeti.FullFockSpace.inner_vacuum_prod_creation_add_annihilation`,
  `TauCeti.FullFockSpace.vacuumState_prod_creation_add_annihilation`, and
  `TauCeti.FullFockSpace.vacuumState_prod_ofFn_creation_add_annihilation`: the vacuum Wick formula
  over noncrossing pairings for ordered products of `creation 𝕜 (f i) + annihilation 𝕜 (g i)`.
* `TauCeti.FullFockSpace.vacuumState_prod_field` and
  `TauCeti.FullFockSpace.vacuumState_prod_ofFn_field`: the vacuum Wick formula for products of
  self-adjoint field operators.
* `TauCeti.FullFockSpace.vacuumState_field_pow`: the semicircular moments of a single field
  operator `field 𝕜 h` of variance `‖h‖ ^ 2`.

## References

* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, CRM Monograph Series, Vol. 1,
  American Mathematical Society, 1992, §2.6.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, London Mathematical
  Society Lecture Note Series, Vol. 335, Cambridge University Press, 2006, Lecture 7.
-/

public section

noncomputable section

open Finset
open scoped ComplexOrder InnerProductSpace

namespace TauCeti

universe u v

namespace FullFockSpace

section VacuumState

/-- The normalized *vacuum functional* `T ↦ ⟪vacuum, T vacuum⟫_𝕜` on bounded operators on
`FullFockSpace 𝕜 H`, bundled as a positive linear map for the Loewner partial order. When `𝕜 = ℂ`
and `H` is complete, this is the vacuum vector state on the C⋆-algebra `𝓑(𝓕(H))`. -/
def vacuumState (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] :
    (FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H) →ₚ[𝕜] 𝕜 :=
  ContinuousLinearMap.innerPositiveLinearMap 𝕜 (vacuum : FullFockSpace 𝕜 H)

section

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

theorem vacuumState_def :
    vacuumState 𝕜 H =
      ContinuousLinearMap.innerPositiveLinearMap 𝕜 (vacuum : FullFockSpace 𝕜 H) :=
  (rfl)

@[simp]
theorem vacuumState_apply (T : FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H) :
    vacuumState 𝕜 H T = ⟪vacuum, T vacuum⟫_𝕜 :=
  ContinuousLinearMap.innerPositiveLinearMap_apply (vacuum : FullFockSpace 𝕜 H) T

theorem vacuumState_one : vacuumState 𝕜 H 1 = 1 := by
  simp

theorem norm_vacuumState_apply_le (T : FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H) :
    ‖vacuumState 𝕜 H T‖ ≤ ‖T‖ := by
  simpa using ContinuousLinearMap.norm_innerPositiveLinearMap_apply_le
    (𝕜 := 𝕜) (vacuum : FullFockSpace 𝕜 H) T

theorem continuous_vacuumState :
    Continuous (vacuumState 𝕜 H : (FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H) → 𝕜) := by
  have h : (vacuumState 𝕜 H : (FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H) → 𝕜) =
      (innerSL 𝕜 (vacuum : FullFockSpace 𝕜 H)) ∘
        (ContinuousLinearMap.apply 𝕜 (FullFockSpace 𝕜 H) vacuum) := by
    ext T
    simp
  rw [h]
  exact (innerSL 𝕜 (vacuum : FullFockSpace 𝕜 H)).continuous.comp
    (ContinuousLinearMap.apply 𝕜 (FullFockSpace 𝕜 H) vacuum).continuous

theorem vacuumState_vacuumProj : vacuumState 𝕜 H vacuumProj = 1 := by
  simp

theorem vacuumState_creation (h : H) : vacuumState 𝕜 H (creation 𝕜 h) = 0 := by
  simp

theorem vacuumState_annihilation (h : H) : vacuumState 𝕜 H (annihilation 𝕜 h) = 0 := by
  simp

theorem vacuumState_annihilation_mul_creation (h k : H) :
    vacuumState 𝕜 H (annihilation 𝕜 h * creation 𝕜 k) = ⟪h, k⟫_𝕜 := by
  simp

theorem vacuumState_creation_mul_annihilation (h k : H) :
    vacuumState 𝕜 H (creation 𝕜 h * annihilation 𝕜 k) = 0 := by
  simp

theorem vacuumState_creation_mul_creation (h k : H) :
    vacuumState 𝕜 H (creation 𝕜 h * creation 𝕜 k) = 0 := by
  simp

theorem vacuumState_annihilation_mul_annihilation (h k : H) :
    vacuumState 𝕜 H (annihilation 𝕜 h * annihilation 𝕜 k) = 0 := by
  simp

end

end VacuumState

section Field

/-- The self-adjoint *field* (or *position*) operator `s(h) = ℓ(h) + ℓ(h)*` on
`FullFockSpace 𝕜 H`. -/
def field (𝕜 : Type u) {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (h : H) :
    FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H :=
  creation 𝕜 h + annihilation 𝕜 h

section

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

theorem field_def (h : H) : field 𝕜 h = creation 𝕜 h + annihilation 𝕜 h :=
  (rfl)

theorem field_apply (h : H) (x : FullFockSpace 𝕜 H) :
    field 𝕜 h x = creation 𝕜 h x + annihilation 𝕜 h x :=
  (rfl)

@[simp]
theorem adjoint_field (h : H) : (field 𝕜 h).adjoint = field 𝕜 h := by
  rw [field_def, map_add, adjoint_creation, adjoint_annihilation, add_comm]

@[simp]
theorem star_field (h : H) : star (field 𝕜 h) = field 𝕜 h :=
  adjoint_field h

theorem isSelfAdjoint_field (h : H) : IsSelfAdjoint (field 𝕜 h) :=
  star_field h

@[simp]
theorem field_zero : field 𝕜 (0 : H) = 0 := by
  simp [field_def]

@[simp]
theorem field_add (h k : H) : field 𝕜 (h + k) = field 𝕜 h + field 𝕜 k := by
  rw [field_def, creation_add, annihilation_add, field_def, field_def, add_add_add_comm]

@[simp]
theorem field_neg (h : H) : field 𝕜 (-h) = -field 𝕜 h := by
  rw [field_def, creation_neg, annihilation_neg, ← neg_add, ← field_def]

@[simp]
theorem field_sub (h k : H) : field 𝕜 (h - k) = field 𝕜 h - field 𝕜 k := by
  rw [sub_eq_add_neg, field_add, field_neg, ← sub_eq_add_neg]

theorem field_smul_of_isSelfAdjoint {c : 𝕜} (hc : IsSelfAdjoint c) (h : H) :
    field 𝕜 (c • h) = c • field 𝕜 h := by
  rw [field_def, field_def, smul_add, creation_smul, annihilation_smul, hc.star_eq]

@[simp]
theorem field_ofReal_smul (r : ℝ) (h : H) :
    field 𝕜 ((r : 𝕜) • h) = (r : 𝕜) • field 𝕜 h :=
  field_smul_of_isSelfAdjoint (by simp [IsSelfAdjoint, RCLike.conj_ofReal]) h

@[simp]
theorem norm_field (h : H) : ‖field 𝕜 h‖ = 2 * ‖h‖ :=
  norm_creation_add_annihilation h

theorem field_injective : Function.Injective (field 𝕜 (H := H)) := by
  intro h k hhk
  have hnorm : 2 * ‖h - k‖ = 0 := by
    rw [← norm_field (𝕜 := 𝕜), field_sub, hhk, sub_self, norm_zero]
  simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or, norm_eq_zero] at hnorm
  exact sub_eq_zero.mp hnorm

@[simp]
theorem field_eq_zero_iff {h : H} : field 𝕜 h = 0 ↔ h = 0 :=
  ⟨fun hh => field_injective (hh.trans field_zero.symm), fun hh => hh ▸ field_zero⟩

@[simp]
theorem field_vacuum (h : H) : field 𝕜 h vacuum = creation 𝕜 h vacuum := by
  simp [field_apply]

theorem inner_vacuum_field_vacuum (h : H) : ⟪vacuum, field 𝕜 h vacuum⟫_𝕜 = 0 := by
  simp

theorem vacuumState_field (h : H) : vacuumState 𝕜 H (field 𝕜 h) = 0 := by
  simp

theorem vacuumState_field_mul_field (h k : H) :
    vacuumState 𝕜 H (field 𝕜 h * field 𝕜 k) = ⟪h, k⟫_𝕜 := by
  simp [field_def, inner_add_right, inner_smul_right]

theorem vacuumState_field_sq (h : H) :
    vacuumState 𝕜 H (field 𝕜 h ^ 2) = (‖h‖ ^ 2 : 𝕜) := by
  rw [sq, vacuumState_field_mul_field, inner_self_eq_norm_sq_to_K]

end

end Field

section Wick

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  {α : Type*} [LinearOrder α]

/-- Ordered product of `creation 𝕜 (f i) + annihilation 𝕜 (g i)` along `t : Finset α`. -/
private def wickWordOp (𝕜 : Type u) [RCLike 𝕜] [InnerProductSpace 𝕜 H]
    (f g : α → H) (t : Finset α) : FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H :=
  (t.sort.map fun i => creation 𝕜 (f i) + annihilation 𝕜 (g i)).prod

@[simp]
private theorem wickWordOp_empty (f g : α → H) : wickWordOp 𝕜 f g (∅ : Finset α) = 1 := by
  simp [wickWordOp]

/-- Separating the factor at `s.min' hs` from an ordered product over a nonempty finset `s`. -/
private theorem wickWordOp_eq_min'_mul {s : Finset α} (hs : s.Nonempty) (f g : α → H) :
    wickWordOp 𝕜 f g s =
      (creation 𝕜 (f (s.min' hs)) + annihilation 𝕜 (g (s.min' hs))) *
        wickWordOp 𝕜 f g {y ∈ s | s.min' hs < y} := by
  have hsort : s.sort = s.min' hs :: {y ∈ s | s.min' hs < y}.sort := by
    conv_lhs => rw [← insert_erase (s.min'_mem hs), ← filter_min'_lt_eq_erase hs]
    exact sort_insert (· ≤ ·) (fun y hy => (mem_filter.1 hy).2.le)
      fun hy => (mem_filter.1 hy).2.false
  rw [wickWordOp, hsort, List.map_cons, List.prod_cons, ← wickWordOp]

/-- Applying `annihilation 𝕜 w` to a vector decomposed into a vacuum multiple plus a sum of
`creation 𝕜 (f x)`-images contracts `w` against each `f x` via Cuntz–Toeplitz. -/
private theorem annihilation_wickWordOp_vacuum_of_decomp {t : Finset α} (f g : α → H) (w : H)
    (hdecomp : wickWordOp 𝕜 f g t vacuum =
      ⟪vacuum, wickWordOp 𝕜 f g t vacuum⟫_𝕜 • vacuum +
        ∑ x ∈ t, ⟪vacuum, wickWordOp 𝕜 f g {y ∈ t | y < x} vacuum⟫_𝕜 •
          creation 𝕜 (f x) (wickWordOp 𝕜 f g {y ∈ t | x < y} vacuum)) :
    annihilation 𝕜 w (wickWordOp 𝕜 f g t vacuum) =
      ∑ x ∈ t, (⟪w, f x⟫_𝕜 * ⟪vacuum, wickWordOp 𝕜 f g {y ∈ t | y < x} vacuum⟫_𝕜) •
        wickWordOp 𝕜 f g {y ∈ t | x < y} vacuum := by
  rw [hdecomp, map_add, map_smul, annihilation_vacuum, smul_zero, zero_add, map_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [map_smul, annihilation_creation, smul_smul, mul_comm]

/-- Once the ordered product on `{y ∈ s | s.min' hs < y}` decomposes on `vacuum` into its vacuum
projection plus first-creation terms, the vacuum expectation on `s` satisfies the partner
recurrence at `s.min' hs`. -/
private theorem inner_vacuum_wickWordOp_eq_sum_of_decomp {s : Finset α} (hs : s.Nonempty)
    (f g : α → H)
    (hdecomp : wickWordOp 𝕜 f g {y ∈ s | s.min' hs < y} vacuum =
      ⟪vacuum, wickWordOp 𝕜 f g {y ∈ s | s.min' hs < y} vacuum⟫_𝕜 • vacuum +
        ∑ x ∈ {y ∈ s | s.min' hs < y},
          ⟪vacuum, wickWordOp 𝕜 f g {y ∈ {y ∈ s | s.min' hs < y} | y < x} vacuum⟫_𝕜 •
            creation 𝕜 (f x)
              (wickWordOp 𝕜 f g {y ∈ {y ∈ s | s.min' hs < y} | x < y} vacuum)) :
    ⟪vacuum, wickWordOp 𝕜 f g s vacuum⟫_𝕜 =
      ∑ x ∈ s with s.min' hs < x,
        ⟪g (s.min' hs), f x⟫_𝕜 *
          ⟪vacuum, wickWordOp 𝕜 f g {y ∈ s | s.min' hs < y ∧ y < x} vacuum⟫_𝕜 *
          ⟪vacuum, wickWordOp 𝕜 f g {y ∈ s | x < y} vacuum⟫_𝕜 := by
  rw [wickWordOp_eq_min'_mul hs, mul_apply_eq_comp, add_apply,
    inner_add_right, inner_vacuum_creation, zero_add,
    annihilation_wickWordOp_vacuum_of_decomp f g (g (s.min' hs)) hdecomp, inner_sum]
  refine sum_congr rfl fun x hx => ?_
  have hmx : s.min' hs < x := (mem_filter.1 hx).2
  have hmid : {y ∈ {y ∈ s | s.min' hs < y} | y < x} = {y ∈ s | s.min' hs < y ∧ y < x} :=
    filter_filter _ _ _
  have hgt : {y ∈ {y ∈ s | s.min' hs < y} | x < y} = {y ∈ s | x < y} := by
    rw [filter_filter]
    exact filter_congr fun y _ => ⟨And.right, fun hxy => ⟨hmx.trans hxy, hxy⟩⟩
  rw [inner_smul_right, hmid, hgt]

/-- Swapping the double sum over `m < x < z` in the inductive step of the first-creation
decomposition identifies the coefficient of `creation 𝕜 (f z)` with the vacuum expectation on
`{y ∈ s | y < z}` and adjoins the `z = m` term. -/
private theorem sum_creation_partner_eq {s : Finset α} (hs : s.Nonempty) (f g : α → H)
    (ih : ∀ t : Finset α, #t < #s →
      wickWordOp 𝕜 f g t vacuum =
        ⟪vacuum, wickWordOp 𝕜 f g t vacuum⟫_𝕜 • vacuum +
          ∑ z ∈ t, ⟪vacuum, wickWordOp 𝕜 f g {y ∈ t | y < z} vacuum⟫_𝕜 •
            creation 𝕜 (f z) (wickWordOp 𝕜 f g {y ∈ t | z < y} vacuum)) :
    creation 𝕜 (f (s.min' hs)) (wickWordOp 𝕜 f g {y ∈ s | s.min' hs < y} vacuum) +
      (∑ x ∈ {y ∈ s | s.min' hs < y},
        (⟪g (s.min' hs), f x⟫_𝕜 *
          ⟪vacuum, wickWordOp 𝕜 f g {y ∈ {y ∈ s | s.min' hs < y} | y < x} vacuum⟫_𝕜) •
          ∑ z ∈ {y ∈ s | s.min' hs < y} with x < z,
            ⟪vacuum, wickWordOp 𝕜 f g {y ∈ s | x < y ∧ y < z} vacuum⟫_𝕜 •
              creation 𝕜 (f z) (wickWordOp 𝕜 f g {y ∈ s | z < y} vacuum)) =
      ∑ z ∈ s, ⟪vacuum, wickWordOp 𝕜 f g {y ∈ s | y < z} vacuum⟫_𝕜 •
        creation 𝕜 (f z) (wickWordOp 𝕜 f g {y ∈ s | z < y} vacuum) := by
  set m := s.min' hs
  set s' := {y ∈ s | m < y}
  have hswap :
      (∑ x ∈ s', (⟪g m, f x⟫_𝕜 * ⟪vacuum, wickWordOp 𝕜 f g {y ∈ s' | y < x} vacuum⟫_𝕜) •
        ∑ z ∈ s' with x < z,
          ⟪vacuum, wickWordOp 𝕜 f g {y ∈ s | x < y ∧ y < z} vacuum⟫_𝕜 •
            creation 𝕜 (f z) (wickWordOp 𝕜 f g {y ∈ s | z < y} vacuum)) =
      ∑ z ∈ s', ⟪vacuum, wickWordOp 𝕜 f g {y ∈ s | y < z} vacuum⟫_𝕜 •
        creation 𝕜 (f z) (wickWordOp 𝕜 f g {y ∈ s | z < y} vacuum) := by
    simp_rw [smul_sum, smul_smul, sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun z hz => ?_
    rw [← sum_filter, ← sum_smul]
    set u := {y ∈ s | y < z}
    have hmu : m ∈ u := mem_filter.2 ⟨s.min'_mem hs, (mem_filter.1 hz).2⟩
    have hu : u.Nonempty := ⟨m, hmu⟩
    have humin : u.min' hu = m :=
      le_antisymm (u.min'_le m hmu) (s.min'_le _ (mem_filter.1 (u.min'_mem hu)).1)
    have hu'lt : #{y ∈ u | u.min' hu < y} < #s :=
      card_lt_card (ssubset_iff_of_subset (fun y hy => (mem_filter.1 (mem_filter.1 hy).1).1) |>.2
        ⟨z, (mem_filter.1 hz).1, fun h => (mem_filter.1 (mem_filter.1 h).1).2.false⟩)
    rw [inner_vacuum_wickWordOp_eq_sum_of_decomp hu f g (ih _ hu'lt)]
    refine congrArg (· • creation 𝕜 (f z) (wickWordOp 𝕜 f g {y ∈ s | z < y} vacuum)) ?_
    have hdom : {x ∈ s' | x < z} = {x ∈ u | u.min' hu < x} := by
      ext x; simp only [s', u, humin, mem_filter]; tauto
    refine sum_congr hdom fun x hx => ?_
    have hxz : x < z := (mem_filter.1 (mem_filter.1 hx).1).2
    have hl : {y ∈ s' | y < x} = {y ∈ u | u.min' hu < y ∧ y < x} := by
      ext y; simp only [s', u, humin, mem_filter]
      exact ⟨fun ⟨⟨hys, hmy⟩, hyx⟩ => ⟨⟨hys, hyx.trans hxz⟩, hmy, hyx⟩,
        fun ⟨⟨hys, _⟩, hmy, hyx⟩ => ⟨⟨hys, hmy⟩, hyx⟩⟩
    have hr : {y ∈ s | x < y ∧ y < z} = {y ∈ u | x < y} := by
      ext y; simp only [u, mem_filter]; tauto
    rw [hl, hr, humin]
  have hmnot : m ∉ s' := fun h => (mem_filter.1 h).2.false
  have hempty : {y ∈ s | y < m} = ∅ :=
    eq_empty_of_forall_notMem fun y hy =>
      (s.min'_le y (mem_filter.1 hy).1).not_gt (mem_filter.1 hy).2
  have hmterm : ⟪vacuum, wickWordOp 𝕜 f g {y ∈ s | y < m} vacuum⟫_𝕜 •
      creation 𝕜 (f m) (wickWordOp 𝕜 f g {y ∈ s | m < y} vacuum) =
      creation 𝕜 (f m) (wickWordOp 𝕜 f g s' vacuum) := by
    simp [hempty, s']
  have hins : insert m s' = s := by
    simp only [m, s', filter_min'_lt_eq_erase hs, insert_erase (s.min'_mem hs)]
  have hsplit := sum_insert (f := fun z =>
    ⟪vacuum, wickWordOp 𝕜 f g {y ∈ s | y < z} vacuum⟫_𝕜 •
      creation 𝕜 (f z) (wickWordOp 𝕜 f g {y ∈ s | z < y} vacuum)) hmnot
  rw [hins] at hsplit
  rw [hswap, hsplit, hmterm]

private theorem wickWordOp_gt_vacuum_of_decomp {s : Finset α} {m x : α}
    (hx : x ∈ {y ∈ s | m < y}) (f g : α → H)
    (hdecomp : wickWordOp 𝕜 f g {y ∈ s | x < y} vacuum =
      ⟪vacuum, wickWordOp 𝕜 f g {y ∈ s | x < y} vacuum⟫_𝕜 • vacuum +
        ∑ z ∈ {y ∈ s | x < y},
          ⟪vacuum, wickWordOp 𝕜 f g {y ∈ {y ∈ s | x < y} | y < z} vacuum⟫_𝕜 •
            creation 𝕜 (f z) (wickWordOp 𝕜 f g {y ∈ {y ∈ s | x < y} | z < y} vacuum)) :
    wickWordOp 𝕜 f g {y ∈ s | x < y} vacuum =
      ⟪vacuum, wickWordOp 𝕜 f g {y ∈ s | x < y} vacuum⟫_𝕜 • vacuum +
        ∑ z ∈ {y ∈ s | m < y} with x < z,
          ⟪vacuum, wickWordOp 𝕜 f g {y ∈ s | x < y ∧ y < z} vacuum⟫_𝕜 •
            creation 𝕜 (f z) (wickWordOp 𝕜 f g {y ∈ s | z < y} vacuum) := by
  conv_lhs => rw [hdecomp]
  have hset : {y ∈ s | x < y} = {z ∈ {y ∈ s | m < y} | x < z} := by
    rw [filter_filter]
    exact filter_congr fun y _ => ⟨fun hxy => ⟨(mem_filter.1 hx).2.trans hxy, hxy⟩, And.right⟩
  refine congrArg (_ + ·) (sum_congr hset fun z hz => ?_)
  have hxz : x < z := (mem_filter.1 hz).2
  have hl : {y ∈ {y ∈ s | x < y} | y < z} = {y ∈ s | x < y ∧ y < z} := filter_filter _ _ _
  have hr : {y ∈ {y ∈ s | x < y} | z < y} = {y ∈ s | z < y} := by
    rw [filter_filter]
    exact filter_congr fun y _ => ⟨And.right, fun hzy => ⟨hxz.trans hzy, hzy⟩⟩
  rw [hl, hr]

/-- First-creation decomposition of an ordered product of `creation 𝕜 (f i) + annihilation 𝕜 (g i)`
applied to `vacuum`: every vector produced from `vacuum` splits uniquely by the position `z ∈ s` of
the surviving leftmost creation operator, weighted by the vacuum expectation before `z` and acting
on the vector produced after `z`. -/
private theorem wickWordOp_vacuum_eq (s : Finset α) (f g : α → H) :
    wickWordOp 𝕜 f g s vacuum =
      ⟪vacuum, wickWordOp 𝕜 f g s vacuum⟫_𝕜 • vacuum +
        ∑ z ∈ s, ⟪vacuum, wickWordOp 𝕜 f g {y ∈ s | y < z} vacuum⟫_𝕜 •
          creation 𝕜 (f z) (wickWordOp 𝕜 f g {y ∈ s | z < y} vacuum) := by
  induction hn : #s using Nat.strong_induction_on generalizing s with
  | _ n ih =>
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  set m := s.min' hs
  set s' := {y ∈ s | m < y}
  have ih' : ∀ t : Finset α, #t < #s →
      wickWordOp 𝕜 f g t vacuum =
        ⟪vacuum, wickWordOp 𝕜 f g t vacuum⟫_𝕜 • vacuum +
          ∑ z ∈ t, ⟪vacuum, wickWordOp 𝕜 f g {y ∈ t | y < z} vacuum⟫_𝕜 •
            creation 𝕜 (f z) (wickWordOp 𝕜 f g {y ∈ t | z < y} vacuum) :=
    fun t ht => ih #t (hn ▸ ht) t rfl
  have ih_s' := ih' s' (card_lt_card (filter_ssubset.2 ⟨m, s.min'_mem hs, lt_irrefl m⟩))
  have hstep : wickWordOp 𝕜 f g s vacuum = creation 𝕜 (f m) (wickWordOp 𝕜 f g s' vacuum) +
      ∑ x ∈ s', (⟪g m, f x⟫_𝕜 * ⟪vacuum, wickWordOp 𝕜 f g {y ∈ s' | y < x} vacuum⟫_𝕜) •
        wickWordOp 𝕜 f g {y ∈ s | x < y} vacuum := by
    rw [wickWordOp_eq_min'_mul hs, mul_apply_eq_comp, add_apply,
      annihilation_wickWordOp_vacuum_of_decomp f g (g m) ih_s']
    refine congrArg (_ + ·) (sum_congr rfl fun x hx => ?_)
    have hgt : {y ∈ s' | x < y} = {y ∈ s | x < y} := by
      rw [filter_filter]
      exact filter_congr fun y _ => ⟨And.right, fun hxy => ⟨(mem_filter.1 hx).2.trans hxy, hxy⟩⟩
    rw [hgt]
  have hexp (x : α) (hx : x ∈ s') := wickWordOp_gt_vacuum_of_decomp hx f g
    (ih' _ (card_lt_card (filter_ssubset.2 ⟨x, (mem_filter.1 hx).1, lt_irrefl x⟩)))
  have hvac : (∑ x ∈ s', (⟪g m, f x⟫_𝕜 * ⟪vacuum, wickWordOp 𝕜 f g {y ∈ s' | y < x} vacuum⟫_𝕜) •
        (⟪vacuum, wickWordOp 𝕜 f g {y ∈ s | x < y} vacuum⟫_𝕜 • (vacuum : FullFockSpace 𝕜 H))) =
      ⟪vacuum, wickWordOp 𝕜 f g s vacuum⟫_𝕜 • vacuum := by
    rw [inner_vacuum_wickWordOp_eq_sum_of_decomp hs f g ih_s', sum_smul]
    refine sum_congr rfl fun x _ => ?_
    have hmid : {y ∈ s' | y < x} = {y ∈ s | m < y ∧ y < x} := filter_filter _ _ _
    rw [smul_smul, hmid]
  conv_lhs => rw [hstep]
  rw [sum_congr rfl fun x hx => by rw [hexp x hx, smul_add], sum_add_distrib, ← add_assoc,
    add_comm (creation 𝕜 (f m) (wickWordOp 𝕜 f g s' vacuum)) _, add_assoc, hvac,
    sum_creation_partner_eq hs f g ih']

/-- **Fock-space vacuum Wick formula** (inner-product form): for any finite ordered index set `s`
and vectors `f, g : α → H`, the vacuum expectation of the ordered product of
`creation 𝕜 (f i) + annihilation 𝕜 (g i)` is the sum over noncrossing pairings `P ∈ NC₂(s)` of the
directed-arc inner products `∏_{(i, j) ∈ P} ⟪g i, f j⟫_𝕜`. -/
theorem inner_vacuum_prod_creation_add_annihilation (s : Finset α) (f g : α → H) :
    ⟪vacuum, ((s.sort.map fun i => creation 𝕜 (f i) + annihilation 𝕜 (g i)).prod) vacuum⟫_𝕜 =
      ∑ P : {P : NoncrossingPartition s // P.1.IsPairing},
        ∏ p ∈ P.1.1.orderedPairs, ⟪g p.1, f p.2⟫_𝕜 := by
  rw [← wickWordOp]
  induction hn : #s using Nat.strong_induction_on generalizing s with
  | _ n ih =>
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [wickWordOp_empty, one_apply_eq_self, inner_vacuum_self,
      NoncrossingPartition.sum_isPairing_prod_orderedPairs_empty fun i j => ⟪g i, f j⟫_𝕜]
  rw [inner_vacuum_wickWordOp_eq_sum_of_decomp hs f g
      (wickWordOp_vacuum_eq {y ∈ s | s.min' hs < y} f g),
    NoncrossingPartition.sum_isPairing_prod_orderedPairs_eq_sum hs fun i j => ⟪g i, f j⟫_𝕜]
  refine sum_congr rfl fun x hx => ?_
  have hmid : #{y ∈ s | s.min' hs < y ∧ y < x} < n :=
    hn ▸ card_lt_card (filter_ssubset.2 ⟨s.min' hs, s.min'_mem hs, fun h => h.1.false⟩)
  have hgt : #{y ∈ s | x < y} < n :=
    hn ▸ card_lt_card (filter_ssubset.2 ⟨x, (mem_filter.1 hx).1, lt_irrefl x⟩)
  rw [ih _ hmid _ rfl, ih _ hgt _ rfl]

/-- **Fock-space vacuum Wick formula** (`vacuumState` form on `Finset α`). -/
theorem vacuumState_prod_creation_add_annihilation (s : Finset α) (f g : α → H) :
    vacuumState 𝕜 H ((s.sort.map fun i => creation 𝕜 (f i) + annihilation 𝕜 (g i)).prod) =
      ∑ P : {P : NoncrossingPartition s // P.1.IsPairing},
        ∏ p ∈ P.1.1.orderedPairs, ⟪g p.1, f p.2⟫_𝕜 := by
  rw [vacuumState_apply, inner_vacuum_prod_creation_add_annihilation]

/-- **Fock-space vacuum Wick formula** for words indexed by `Fin n`. -/
theorem vacuumState_prod_ofFn_creation_add_annihilation {n : ℕ} (f g : Fin n → H) :
    vacuumState 𝕜 H ((List.ofFn fun i => creation 𝕜 (f i) + annihilation 𝕜 (g i)).prod) =
      ∑ P : {P : NoncrossingPartition (univ : Finset (Fin n)) // P.1.IsPairing},
        ∏ p ∈ P.1.1.orderedPairs, ⟪g p.1, f p.2⟫_𝕜 := by
  rw [List.ofFn_eq_map, ← Fin.sort_univ]
  exact vacuumState_prod_creation_add_annihilation univ f g

/-- Vacuum Wick formula for ordered products of self-adjoint field operators `field 𝕜 (f i)`. -/
theorem vacuumState_prod_field (s : Finset α) (f : α → H) :
    vacuumState 𝕜 H ((s.sort.map fun i => field 𝕜 (f i)).prod) =
      ∑ P : {P : NoncrossingPartition s // P.1.IsPairing},
        ∏ p ∈ P.1.1.orderedPairs, ⟪f p.1, f p.2⟫_𝕜 :=
  vacuumState_prod_creation_add_annihilation s f f

/-- Vacuum Wick formula for words of self-adjoint field operators indexed by `Fin n`. -/
theorem vacuumState_prod_ofFn_field {n : ℕ} (f : Fin n → H) :
    vacuumState 𝕜 H ((List.ofFn fun i => field 𝕜 (f i)).prod) =
      ∑ P : {P : NoncrossingPartition (univ : Finset (Fin n)) // P.1.IsPairing},
        ∏ p ∈ P.1.1.orderedPairs, ⟪f p.1, f p.2⟫_𝕜 :=
  vacuumState_prod_ofFn_creation_add_annihilation f f

/-- On an odd number of positions, the vacuum expectation of any ordered product of
`creation 𝕜 (f i) + annihilation 𝕜 (g i)` vanishes. -/
theorem vacuumState_prod_creation_add_annihilation_eq_zero_of_odd {s : Finset α} (hs : Odd #s)
    (f g : α → H) :
    vacuumState 𝕜 H ((s.sort.map fun i => creation 𝕜 (f i) + annihilation 𝕜 (g i)).prod) = 0 := by
  rw [vacuumState_prod_creation_add_annihilation, NoncrossingPartition.sum_isPairing_eq_zero hs]

/-- Semicircular vacuum moments of a single field operator `field 𝕜 h`: even powers `2 * k` have
vacuum expectation `(‖h‖ ^ 2) ^ k * catalan k` and odd powers vanish. -/
theorem vacuumState_field_pow (h : H) (n : ℕ) :
    vacuumState 𝕜 H (field 𝕜 h ^ n) =
      if Even n then (‖h‖ ^ 2 : 𝕜) ^ (n / 2) * catalan (n / 2) else 0 := by
  have hpow : field 𝕜 h ^ n = (List.ofFn fun _ : Fin n => field 𝕜 h).prod := by
    simp
  rw [hpow, vacuumState_prod_ofFn_field]
  have hc := NoncrossingPartition.sum_prod_ite_card_eq_two (univ : Finset (Fin n)) (‖h‖ ^ 2 : 𝕜)
  rw [NoncrossingPartition.sum_prod_ite_card_eq_two_eq_sum_isPairing] at hc
  rw [card_univ, Fintype.card_fin] at hc
  rw [← hc]
  refine sum_congr rfl fun P _ => ?_
  rw [← P.2.prod_orderedPairs]
  simp [inner_self_eq_norm_sq_to_K]

end Wick

end FullFockSpace

end TauCeti

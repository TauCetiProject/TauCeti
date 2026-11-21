/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.LinearMap
public import TauCeti.RepresentationTheory.LSPath.StringLength
import TauCeti.LinearAlgebra.Reflection

/-!
# Capped record reflection and dilation of paths

`PLPath.cappedReflection f x c` reflects the increasing records of a path up to height `c`,
keeping equal-height excursions. It is the presentation-independent version of
`PLPath.reflectRecords`. Lowering is capped reflection at the minimum height plus one,
when the lowering operator is defined.

Positive dilation multiplies all heights and caps by the same scalar, leaving the relative
cut positions unchanged (`PLPath.cappedReflection_map_smul`). For a normalized root-coroot
pair `f x = 2`, composing two capped reflections gives a single capped reflection whose cap
records the cumulative height drop (`PLPath.cappedReflection_cappedReflection`), and the
`n`-fold lowering operator `lowerIter f x n` is a single capped reflection up to
`p.minHeight f + n` (`PLPath.lowerIter_eq_some_cappedReflection`). Positive-scalar and
positive-integer stretching similarity is deduced from these two results in
`TauCeti.RepresentationTheory.LSPath.Similarity`.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §§1–2, 5 (Lemma 2.1(d) and Theorem 5.1).
-/

public section

namespace TauCeti.PLPath

open Module Relation

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] {f : Dual 𝕜 V} {x : V}

/-- Normalizing a presentation before record reflection does not change the resulting path. -/
@[simp]
theorem normalize_reflectRecords_normalize (c : 𝕜) (l : List V) :
    normalize 𝕜 (reflectRecords f x c (normalize 𝕜 l)) =
      normalize 𝕜 (reflectRecords f x c l) := by
  suffices ∀ m, ReflTransGen (Move 𝕜) l m →
      normalize 𝕜 (reflectRecords f x c m) = normalize 𝕜 (reflectRecords f x c l) from
    this _ (reflTransGen_move_normalize l)
  intro m h
  induction h with
  | refl => rfl
  | tail _ h ih => exact (h.normalize_reflectRecords c).symm.trans ih

/-- Reflect the increasing records up to the cap `c`, retaining equal-height excursions.
The operation is independent of the segment presentation. -/
noncomputable def cappedReflection (f : Dual 𝕜 V) (x : V) (c : 𝕜) (p : PLPath 𝕜 V) :
    PLPath 𝕜 V :=
  ofSegments 𝕜 (reflectRecords f x c p.segments)

/-- Compute capped reflection on any segment presentation, without normalizing it first. -/
@[simp]
theorem cappedReflection_ofSegments (c : 𝕜) (l : List V) :
    cappedReflection f x c (ofSegments 𝕜 l) = ofSegments 𝕜 (reflectRecords f x c l) := by
  apply PLPath.ext
  simp only [cappedReflection, segments_ofSegments, normalize_reflectRecords_normalize]

@[simp]
theorem cappedReflection_one (c : 𝕜) : cappedReflection f x c (1 : PLPath 𝕜 V) = 1 := by
  rw [← ofSegments_nil, cappedReflection_ofSegments, reflectRecords_nil]

/-- A cap below the minimum height reflects no part of the path. -/
@[simp]
theorem cappedReflection_eq_self {c : 𝕜} (p : PLPath 𝕜 V) (hc : c ≤ p.minHeight f) :
    cappedReflection f x c p = p := by
  rw [minHeight_def] at hc
  rw [cappedReflection, reflectRecords_of_le_listMinHeight hc, ofSegments_segments]

/-- The endpoint change is the capped increase from the minimum to the final height. -/
@[simp]
theorem endpoint_cappedReflection (c : 𝕜) (p : PLPath 𝕜 V) :
    (cappedReflection f x c p).endpoint =
      p.endpoint - (min (f p.endpoint) c - min (p.minHeight f) c) • x := by
  rw [cappedReflection, endpoint_ofSegments, sum_reflectRecords, endpoint_def, minHeight_def]

/-- For a normalized root-coroot pair, capped reflection lowers the minimum by the capped
increase from the minimum to the final height. -/
@[simp]
theorem minHeight_cappedReflection (hx : f x = 2) (c : 𝕜) (p : PLPath 𝕜 V) :
    (cappedReflection f x c p).minHeight f =
      p.minHeight f - (min (f p.endpoint) c - min (p.minHeight f) c) := by
  rw [cappedReflection, minHeight_ofSegments, listMinHeight_reflectRecords hx,
    endpoint_def, minHeight_def]

/-- Capped reflection of a concatenation uses the tail minimum for the first cap and translates
by the first factor's final height for the second cap. -/
theorem cappedReflection_mul (c : 𝕜) (p q : PLPath 𝕜 V) :
    cappedReflection f x c (p * q) =
      cappedReflection f x (min c (f p.endpoint + q.minHeight f)) p *
        cappedReflection f x (c - f p.endpoint) q := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  obtain ⟨m, rfl⟩ := ofSegments_surjective q
  rw [← ofSegments_append, cappedReflection_ofSegments, reflectRecords_append,
    ofSegments_append]
  simp only [cappedReflection_ofSegments, endpoint_ofSegments, minHeight_ofSegments]

/-- Capped reflection is natural for linear maps preserving the height form and carrying the
root to the target root, including maps that collapse segments. -/
theorem cappedReflection_map {W : Type*} [AddCommGroup W] [Module 𝕜 W]
    {g : V →ₗ[𝕜] W} {f' : Dual 𝕜 W} (hf : f'.comp g = f)
    (x : V) (c : 𝕜) (p : PLPath 𝕜 V) :
    cappedReflection f' (g x) c (p.map g) = (cappedReflection f x c p).map g := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  simp only [map_ofSegments, cappedReflection_ofSegments, reflectRecords_map hf]

/-- Lowering is capped reflection at the minimum plus one, provided the height string has
at least one step left. -/
theorem lower_eq_some_cappedReflection (p : PLPath 𝕜 V)
    (hp : 1 ≤ f p.endpoint - p.minHeight f) :
    lower f x p = some (cappedReflection f x (p.minHeight f + 1) p) := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  simp only [endpoint_ofSegments, minHeight_ofSegments] at hp
  rw [lower_ofSegments, listLower_def, ite_eq_left hp, Option.map_some,
    cappedReflection_ofSegments, minHeight_ofSegments]

/-! ## Composition of record reflections -/

/-- When the first positive cap `c₁` is reached strictly inside the initial segment `v`, the tail
`l` is untouched by the first reflection and a second reflection either leaves `v`'s kept part
alone (when `c₂ + c₁ ≤ 0`) or cuts it further along the same reflected ray. -/
private theorem normalize_reflectRecords_reflectRecords_cons_of_lt (hx : f x = 2)
    {v : V} {l : List V} {c₁ c₂ : 𝕜} (hc₁ : 0 < c₁) (hlt : c₁ < f v + listMinHeight f l) :
    normalize 𝕜 (reflectRecords f x c₂ (reflectRecords f x c₁ (v :: l))) =
      normalize 𝕜 (reflectRecords f x (max c₁ (c₂ + 2 * c₁)) (v :: l)) := by
  have hm_nonpos := listMinHeight_nonpos (f := f) l
  have hfv : 0 < f v := by linarith
  have hsub : 0 < f v - c₁ := by linarith
  have hr₁ : min (f v + listMinHeight f l) c₁ = c₁ := min_eq_right hlt.le
  have htail₁ : reflectRecords f x (c₁ - f v) l = l :=
    reflectRecords_of_le_listMinHeight (by linarith)
  have hu₁ : f (preReflection x f ((c₁ / f v) • v)) = -c₁ := by
    rw [apply_preReflection hx, map_smul, smul_eq_mul, div_mul_cancel₀ _ hfv.ne']
  have hu₂ : f ((1 - c₁ / f v) • v) = f v - c₁ := by
    rw [map_smul, smul_eq_mul, sub_mul, one_mul, div_mul_cancel₀ _ hfv.ne']
  rw [reflectRecords_cons_of_pos (hr₁.symm ▸ hc₁), hr₁, htail₁]
  -- The reflected initial piece descends by `c₁`, so the second reflection never cuts it.
  rw [reflectRecords_cons_of_nonpos (le_trans (min_le_left _ _)
    (by linarith [hu₁, listMinHeight_nonpos (f := f) ((1 - c₁ / f v) • v :: l)])),
    hu₁, sub_neg_eq_add]
  by_cases hc₂ : 0 < c₂ + c₁
  · set r₂ := min (f v - c₁ + listMinHeight f l) (c₂ + c₁)
    have hr₂_pos : 0 < r₂ := lt_min (by linarith) hc₂
    have hmax : max c₁ (c₂ + 2 * c₁) = c₂ + 2 * c₁ := max_eq_right (by linarith)
    have hR : min (f v + listMinHeight f l) (c₂ + 2 * c₁) = c₁ + r₂ := by
      have h₁ : f v + listMinHeight f l = c₁ + (f v - c₁ + listMinHeight f l) := by ring
      have h₂ : c₂ + 2 * c₁ = c₁ + (c₂ + c₁) := by ring
      rw [h₁, h₂, min_add_add_left]
    have hw₁ : (r₂ / (f v - c₁)) • ((1 - c₁ / f v) • v) = (r₂ / f v) • v := by
      rw [smul_smul]
      congr 1
      field_simp [hfv.ne', hsub.ne']
    have hw₂ : (1 - r₂ / (f v - c₁)) • ((1 - c₁ / f v) • v) = (1 - (c₁ + r₂) / f v) • v := by
      rw [smul_smul]
      congr 1
      field_simp [hfv.ne', hsub.ne']
      ring
    have hray : SameRay 𝕜 (preReflection x f ((c₁ / f v) • v))
        (preReflection x f ((r₂ / f v) • v)) := by
      rw [map_smul, map_smul]
      exact (SameRay.sameRay_nonneg_smul_left _ (div_nonneg hc₁.le hfv.le)).nonneg_smul_right
        (div_nonneg hr₂_pos.le hfv.le)
    have hadd : preReflection x f ((c₁ / f v) • v) + preReflection x f ((r₂ / f v) • v) =
        preReflection x f (((c₁ + r₂) / f v) • v) := by
      rw [← map_add, ← add_smul, add_div]
    have hshift : c₂ + c₁ - (f v - c₁) = c₂ + 2 * c₁ - f v := by ring
    rw [reflectRecords_cons_of_pos (by simpa only [hu₂] using hr₂_pos), hu₂, hw₁, hw₂,
      hshift, hmax, reflectRecords_cons_of_pos (by linarith [hR]), hR]
    simp only [normalize_cons, consMerge_consMerge hray, hadd]
  · rw [not_lt] at hc₂
    have hmax : max c₁ (c₂ + 2 * c₁) = c₁ := max_eq_left (by linarith)
    rw [reflectRecords_cons_of_nonpos (min_le_of_right_le hc₂), hu₂,
      reflectRecords_of_le_listMinHeight (by linarith),
      hmax, reflectRecords_cons_of_pos (hr₁.symm ▸ hc₁), hr₁, htail₁]

/-- When `0 < f v + listMinHeight f l ≤ c₁`, the first reflection reflects the entire record prefix
of `v` up to the tail minimum, leaving a nonpositive-height remainder before recursing on `l`. -/
private theorem normalize_reflectRecords_reflectRecords_cons_of_le (hx : f x = 2)
    {v : V} {l : List V} {c₁ c₂ : 𝕜} (hpos_vm : 0 < f v + listMinHeight f l)
    (hle : f v + listMinHeight f l ≤ c₁)
    (ih : ∀ c₁ c₂ : 𝕜, normalize 𝕜 (reflectRecords f x c₂ (reflectRecords f x c₁ l)) =
      normalize 𝕜 (reflectRecords f x
        (max c₁ (c₂ + 2 * (min (f l.sum) c₁ - min (listMinHeight f l) c₁))) l)) :
    normalize 𝕜 (reflectRecords f x c₂ (reflectRecords f x c₁ (v :: l))) =
      normalize 𝕜 (reflectRecords f x
        (max c₁ (c₂ + 2 * (min (f (v :: l).sum) c₁ - min (listMinHeight f (v :: l)) c₁)))
        (v :: l)) := by
  set m := listMinHeight f l
  set δ := min (f l.sum) (c₁ - f v) - min m (c₁ - f v)
  have hm_nonpos : m ≤ 0 := listMinHeight_nonpos (f := f) l
  have hδ_nonneg : 0 ≤ δ := sub_nonneg.mpr (min_le_min_right _ (listMinHeight_le_apply_sum l))
  have hc₁_pos : 0 < c₁ := hpos_vm.trans_le hle
  have hfv : 0 < f v := by linarith
  have hr₁ : min (f v + m) c₁ = f v + m := min_eq_left hle
  have hδ_all : min (f (v :: l).sum) c₁ - min (listMinHeight f (v :: l)) c₁ = f v + m + δ := by
    rw [List.sum_cons, map_add, listMinHeight_cons, min_eq_left hpos_vm.le, min_eq_left hc₁_pos.le]
    simp only [δ, m, min_def]
    split_ifs <;> linarith
  have hu₁ : f (preReflection x f (((f v + m) / f v) • v)) = -(f v + m) := by
    rw [apply_preReflection hx, map_smul, smul_eq_mul, div_mul_cancel₀ _ hfv.ne']
  have hu₂ : f ((1 - (f v + m) / f v) • v) = -m := by
    rw [map_smul, smul_eq_mul, sub_mul, one_mul, div_mul_cancel₀ _ hfv.ne']
    ring
  have htail_nonpos :
      listMinHeight f ((1 - (f v + m) / f v) • v :: reflectRecords f x (c₁ - f v) l) ≤ 0 :=
    listMinHeight_nonpos _
  have hR : min (f v + m) (max c₁ (c₂ + 2 * (f v + m + δ))) = f v + m :=
    min_eq_left (hle.trans (le_max_left _ _))
  have hshift : c₂ + (f v + m) - -m = c₂ + 2 * (f v + m) - f v := by ring
  rw [hδ_all, reflectRecords_cons_of_pos (hr₁.symm ▸ hpos_vm), hr₁,
    reflectRecords_cons_of_nonpos (le_trans (min_le_left _ _) (by linarith)),
    hu₁, sub_neg_eq_add,
    reflectRecords_cons_of_nonpos (le_trans (min_le_left _ _)
      (by rw [hu₂, listMinHeight_reflectRecords hx]; linarith)),
    hu₂, reflectRecords_cons_of_pos (hR.symm ▸ hpos_vm), hR]
  simp only [normalize_cons]
  congr 2
  rw [hshift, ih]
  congr 2
  simp only [δ, m, max_def]
  split_ifs <;> linarith

/-- **Composition of capped record reflections on segment lists.** When `f x = 2`, reflecting
records up to `c₁` and then up to `c₂` presents the same normalized path as reflecting records
once up to `max c₁ (c₂ + 2 * (min (f l.sum) c₁ - min (listMinHeight f l) c₁))`. -/
theorem normalize_reflectRecords_reflectRecords (hx : f x = 2) (c₁ c₂ : 𝕜) (l : List V) :
    normalize 𝕜 (reflectRecords f x c₂ (reflectRecords f x c₁ l)) =
      normalize 𝕜 (reflectRecords f x
        (max c₁ (c₂ + 2 * (min (f l.sum) c₁ - min (listMinHeight f l) c₁))) l) := by
  induction l generalizing c₁ c₂ with
  | nil => simp
  | cons v l ih =>
    set m := listMinHeight f l
    set s := f l.sum
    have hms : m ≤ s := listMinHeight_le_apply_sum (f := f) l
    set δ := min s (c₁ - f v) - min m (c₁ - f v)
    have hδ_nonneg : 0 ≤ δ := sub_nonneg.mpr (min_le_min_right _ hms)
    by_cases hr₁ : 0 < min (f v + m) c₁
    · have hpos_vm : 0 < f v + m := hr₁.trans_le (min_le_left _ _)
      have hc₁_pos : 0 < c₁ := hr₁.trans_le (min_le_right _ _)
      rcases lt_or_ge c₁ (f v + m) with hlt | hle
      · have hcap_eq : min (f (v :: l).sum) c₁ - min (listMinHeight f (v :: l)) c₁ = c₁ := by
          rw [List.sum_cons, map_add, listMinHeight_cons, min_eq_left hpos_vm.le,
            min_eq_left hc₁_pos.le, min_eq_right (by linarith : c₁ ≤ f v + s), sub_zero]
        rw [hcap_eq]
        exact normalize_reflectRecords_reflectRecords_cons_of_lt hx hc₁_pos hlt
      · exact normalize_reflectRecords_reflectRecords_cons_of_le hx hpos_vm hle ih
    · rw [not_lt] at hr₁
      rcases le_or_gt (f v + m) 0 with hvm | hvm
      · have hδ_all :
            min (f (v :: l).sum) c₁ - min (listMinHeight f (v :: l)) c₁ = δ := by
          rw [List.sum_cons, map_add, listMinHeight_cons, min_eq_right hvm]
          simp only [δ, min_def]
          split_ifs <;> linarith
        rw [hδ_all, reflectRecords_cons_of_nonpos hr₁,
          reflectRecords_cons_of_nonpos (le_trans (min_le_left _ _)
            (by rw [listMinHeight_reflectRecords hx]; linarith)),
          reflectRecords_cons_of_nonpos (min_le_of_left_le hvm)]
        simp only [normalize_cons]
        congr 1
        rw [ih]
        congr 2
        simp only [max_def]
        split_ifs <;> linarith
      · have hc₁_nonpos : c₁ ≤ 0 := by
          rcases min_le_iff.mp hr₁ with h | h <;> linarith
        have hδ_all :
            min (f (v :: l).sum) c₁ - min (listMinHeight f (v :: l)) c₁ = 0 := by
          rw [List.sum_cons, map_add, listMinHeight_cons, min_eq_left hvm.le,
            min_eq_right hc₁_nonpos, min_eq_right (by linarith : c₁ ≤ f v + s), sub_self]
        have htail : reflectRecords f x (c₁ - f v) l = l :=
          reflectRecords_of_le_listMinHeight (by linarith)
        rw [hδ_all, mul_zero, add_zero, reflectRecords_cons_of_nonpos hr₁, htail]
        rcases le_total c₁ c₂ with hc | hc
        · rw [max_eq_right hc]
        · have hm_cons : listMinHeight f (v :: l) = 0 := by
            rw [listMinHeight_cons, min_eq_left hvm.le]
          have hc₂_le : c₂ ≤ listMinHeight f (v :: l) := hm_cons ▸ hc.trans hc₁_nonpos
          have hc₁_le : c₁ ≤ listMinHeight f (v :: l) := hm_cons ▸ hc₁_nonpos
          rw [max_eq_left hc, reflectRecords_of_le_listMinHeight hc₂_le,
            reflectRecords_of_le_listMinHeight hc₁_le]

/-- **Composition of capped reflections.** For `f x = 2`, applying `cappedReflection` at cap `c₁`
and then at cap `c₂` equals a single `cappedReflection` at cap
`max c₁ (c₂ + 2 * (min (f p.endpoint) c₁ - min (p.minHeight f) c₁))`. -/
theorem cappedReflection_cappedReflection (hx : f x = 2) (c₁ c₂ : 𝕜) (p : PLPath 𝕜 V) :
    cappedReflection f x c₂ (cappedReflection f x c₁ p) =
      cappedReflection f x
        (max c₁ (c₂ + 2 * (min (f p.endpoint) c₁ - min (p.minHeight f) c₁))) p := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  apply PLPath.ext
  simp only [cappedReflection_ofSegments, endpoint_ofSegments, minHeight_ofSegments,
    segments_ofSegments, normalize_reflectRecords_reflectRecords hx]

/-- Successive capped reflections measured relative to the running minimum height add their steps:
if `0 ≤ a ≤ f p.endpoint - p.minHeight f` and `0 ≤ b`, reflecting up to `p.minHeight f + a` and
then up to `q.minHeight f + b` equals reflecting once up to `p.minHeight f + a + b`. -/
theorem cappedReflection_minHeight_add_cappedReflection (hx : f x = 2) (p : PLPath 𝕜 V)
    {a b : 𝕜} (ha₀ : 0 ≤ a) (ha₁ : a ≤ f p.endpoint - p.minHeight f) (hb : 0 ≤ b) :
    cappedReflection f x ((cappedReflection f x (p.minHeight f + a) p).minHeight f + b)
        (cappedReflection f x (p.minHeight f + a) p) =
      cappedReflection f x (p.minHeight f + a + b) p := by
  rw [cappedReflection_cappedReflection hx, minHeight_cappedReflection hx]
  have hmin₁ : min (f p.endpoint) (p.minHeight f + a) = p.minHeight f + a :=
    min_eq_right (by linarith)
  have hmin₂ : min (p.minHeight f) (p.minHeight f + a) = p.minHeight f :=
    min_eq_left (by linarith)
  rw [hmin₁, hmin₂, max_eq_right (by linarith)]
  congr 1
  ring

/-! ## Iterated root operators as capped reflections -/

/-- Single-step lowering as a conditional capped reflection at `p.minHeight f + 1`. -/
theorem lower_eq_ite_cappedReflection (p : PLPath 𝕜 V) :
    lower f x p = if 1 ≤ f p.endpoint - p.minHeight f then
      some (cappedReflection f x (p.minHeight f + 1) p) else none := by
  split_ifs with hp
  · exact lower_eq_some_cappedReflection p hp
  · exact lower_eq_none_iff.mpr (lt_of_not_ge hp)

/-- **Iterated lowering as a single capped reflection.** When `f x = 2` and `n` lowering steps are
defined (`(n : 𝕜) ≤ f p.endpoint - p.minHeight f`), `lowerIter f x n p` reflects the increasing
records of `p` once up to `p.minHeight f + n`. -/
theorem lowerIter_eq_some_cappedReflection (hx : f x = 2) {n : ℕ} (p : PLPath 𝕜 V)
    (hp : (n : 𝕜) ≤ f p.endpoint - p.minHeight f) :
    lowerIter f x n p = some (cappedReflection f x (p.minHeight f + n) p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (n : 𝕜) ≤ f p.endpoint - p.minHeight f :=
      le_trans (Nat.cast_le.mpr (Nat.le_succ n)) hp
    set q := cappedReflection f x (p.minHeight f + n) p
    have hq : lowerIter f x n p = some q := ih hn
    have hrem : 1 ≤ f q.endpoint - q.minHeight f := by
      rw [endpoint_of_lowerIter_eq_some hq, minHeight_of_lowerIter_eq_some hx hq,
        map_sub, map_nsmul, hx, nsmul_eq_mul]
      push_cast at hp ⊢
      linarith
    rw [lowerIter_succ', hq, Option.bind_some, lower_eq_some_cappedReflection q hrem,
      Option.some.injEq, cappedReflection_minHeight_add_cappedReflection hx p
        (Nat.cast_nonneg n) hn zero_le_one, Nat.cast_succ, ← add_assoc]

/-- Conditional capped-reflection formula for `lowerIter f x n p` on every path `p`. -/
theorem lowerIter_eq_ite_cappedReflection (hx : f x = 2) (n : ℕ) (p : PLPath 𝕜 V) :
    lowerIter f x n p = if (n : 𝕜) ≤ f p.endpoint - p.minHeight f then
      some (cappedReflection f x (p.minHeight f + n) p) else none := by
  split_ifs with hp
  · exact lowerIter_eq_some_cappedReflection hx p hp
  · exact (lowerIter_eq_none_iff hx).mpr (lt_of_not_ge hp)

/-- **Iterated raising via capped reflection on the reversed path.** When `f x = 2` and `n` raising
steps are defined (`(n : 𝕜) ≤ -p.minHeight f`), `raiseIter f x n p` reflects the increasing records
of `p.reverse` up to `p.minHeight f - f p.endpoint + n` and reverses the result. -/
theorem raiseIter_eq_some_reverse_cappedReflection_reverse (hx : f x = 2) {n : ℕ} (p : PLPath 𝕜 V)
    (hp : (n : 𝕜) ≤ -p.minHeight f) :
    raiseIter f x n p =
      some (cappedReflection f x (p.minHeight f - f p.endpoint + n) p.reverse).reverse := by
  have hrev : (n : 𝕜) ≤ f p.reverse.endpoint - p.reverse.minHeight f := by
    rw [endpoint_reverse, map_neg, minHeight_reverse]
    linarith
  rw [raiseIter_eq_map_lowerIter_reverse, lowerIter_eq_some_cappedReflection hx p.reverse hrev,
    minHeight_reverse, Option.map_some]

/-! ## Positive dilation -/

/-- Dilation by a positive scalar preserves every cut fraction in capped record reflection.
This is an equality of raw segment lists, before normalization. -/
theorem reflectRecords_map_smul {a : 𝕜} (ha : 0 < a) (c : 𝕜) (l : List V) :
    reflectRecords f x (a * c) (l.map (a • ·)) = (reflectRecords f x c l).map (a • ·) := by
  induction l generalizing c with
  | nil => simp
  | cons v l ih =>
    have hcap : min (f (a • v) + listMinHeight f (l.map (a • ·))) (a * c) =
        a * min (f v + listMinHeight f l) c := by
      rw [map_smul, smul_eq_mul, listMinHeight_map_smul ha.le, ← mul_add,
        mul_min_of_nonneg _ _ ha.le]
    have hshift : a * c - f (a • v) = a * (c - f v) := by
      simp only [map_smul, smul_eq_mul, mul_sub]
    have hcut : (a * min (f v + listMinHeight f l) c) / (a * f v) =
        min (f v + listMinHeight f l) c / f v := mul_div_mul_left _ _ ha.ne'
    by_cases h : 0 < min (f v + listMinHeight f l) c
    · rw [List.map_cons, reflectRecords_cons_of_pos (by rw [hcap]; exact mul_pos ha h),
        reflectRecords_cons_of_pos h]
      simp only [hcap, hshift]
      simp only [map_smul, smul_eq_mul, hcut, ih, List.map_cons]
      congr 1
      · rw [smul_comm]
      · rw [smul_comm]
    · rw [List.map_cons, reflectRecords_cons_of_nonpos (by
          rw [hcap]; exact mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt h)),
        reflectRecords_cons_of_nonpos (le_of_not_gt h), hshift, ih, List.map_cons]

/-- Positive dilation commutes with capped reflection when the cap is dilated as well.
Unlike height-preserving naturality, this keeps the root and coroot fixed. -/
theorem cappedReflection_map_smul {a : 𝕜} (ha : 0 < a) (c : 𝕜) (p : PLPath 𝕜 V) :
    cappedReflection f x (a * c) (p.map (a • LinearMap.id)) =
      (cappedReflection f x c p).map (a • LinearMap.id) := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  simpa only [map_ofSegments, cappedReflection_ofSegments, LinearMap.coe_smul,
    Pi.smul_def, LinearMap.id_apply] using
    congrArg (ofSegments 𝕜) (reflectRecords_map_smul (f := f) ha c l)

/-! ## Special cases of capped reflection -/

/-- Any cap at or above the endpoint height gives the same capped reflection as capping at the
endpoint height. -/
theorem cappedReflection_eq_of_apply_endpoint_le {c : 𝕜} (p : PLPath 𝕜 V)
    (hc : f p.endpoint ≤ c) :
    cappedReflection f x c p = cappedReflection f x (f p.endpoint) p := by
  rw [endpoint_def] at hc
  rw [cappedReflection, cappedReflection, endpoint_def, reflectRecords_of_apply_sum_le hc]

/-- When the minimal height equals the endpoint height, capped reflection fixes the path for every
cap. -/
theorem cappedReflection_eq_self_of_minHeight_eq_apply_endpoint (c : 𝕜) (p : PLPath 𝕜 V)
    (hp : p.minHeight f = f p.endpoint) :
    cappedReflection f x c p = p := by
  rw [minHeight_def, endpoint_def] at hp
  rw [cappedReflection, reflectRecords_of_listMinHeight_eq_apply_sum c hp, ofSegments_segments]

/-- Capped reflection fixes any straight path of nonpositive height. -/
@[simp]
theorem cappedReflection_straight_of_nonpos (c : 𝕜) {v : V} (hv : f v ≤ 0) :
    cappedReflection f x c (straight 𝕜 v) = straight 𝕜 v :=
  cappedReflection_eq_self_of_minHeight_eq_apply_endpoint c (straight 𝕜 v)
    (by simp [min_eq_right hv])

/-- On a straight path of positive height, capped reflection reflects the initial fraction
`max 0 (min (f v) c) / f v` and keeps the complementary fraction. -/
theorem cappedReflection_straight_of_pos (c : 𝕜) {v : V} (hv : 0 < f v) :
    cappedReflection f x c (straight 𝕜 v) =
      straight 𝕜 (preReflection x f ((max 0 (min (f v) c) / f v) • v)) *
        straight 𝕜 ((1 - max 0 (min (f v) c) / f v) • v) := by
  by_cases hc : 0 < c
  · have hpos : 0 < min (f v + listMinHeight f ([] : List V)) c := by
      simpa using lt_min hv hc
    rw [max_eq_right (le_min hv.le hc.le), straight_def, cappedReflection_ofSegments,
      reflectRecords_cons_of_pos hpos]
    simp [ofSegments_cons]
  · have hmax : max 0 (min (f v) c) = 0 := max_eq_left (min_le_of_right_le (not_lt.mp hc))
    simpa [hmax] using
      cappedReflection_eq_self (straight 𝕜 v) (by simpa [min_eq_left hv.le] using not_lt.mp hc)

end TauCeti.PLPath

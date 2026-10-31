/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Face
import Mathlib.Data.Set.Finite.Lemmas

/-!
# The initial minimal slope of a lower convex envelope

The secants from the first finite point to later finite points have slopes bounded
below whenever the height sequence is admissible. Their infimum gives a supporting
line through that first point. A point attaining the infimum determines an initial
affine segment of the envelope. If the infimum is not attained, approximation by
secants with arbitrarily large endpoints shows that the entire envelope to the
right is this affine ray. Unboundedly many attaining indices give the same ray.

Only finite endpoints enter the slope set. In particular an empty or singleton
point set has no secant slope; the ray conclusions require a later finite point.
These are the initial-step arguments for the minimal-slope construction, without
asserting that the last point on an affine segment is a strict change of slope.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §3.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

namespace TauCeti

/-- The real slopes from the height at `p` to later finite heights. Use these as
geometric secants only when `a p` is finite. Empty and singleton domains contribute
no slopes, and an infinite later height never contributes a slope. -/
noncomputable def secantSlopes (a : ℕ → WithTop ℝ) (p : ℕ) : Set ℝ :=
  {σ | ∃ n, p < n ∧ a n ≠ ⊤ ∧ σ = ((a n).untop₀ - (a p).untop₀) / ((n : ℝ) - p)}

/-- Membership in the secant-slope set is witnessed by a later finite endpoint. -/
@[simp]
theorem mem_secantSlopes {a : ℕ → WithTop ℝ} {p : ℕ} {σ : ℝ} :
    σ ∈ secantSlopes a p ↔
      ∃ n, p < n ∧ a n ≠ ⊤ ∧ σ = ((a n).untop₀ - (a p).untop₀) / ((n : ℝ) - p) :=
  Iff.rfl

/-- A secant slope exists exactly when there is a later finite height. -/
@[simp]
theorem secantSlopes_nonempty_iff {a : ℕ → WithTop ℝ} {p : ℕ} :
    (secantSlopes a p).Nonempty ↔ ∃ n, p < n ∧ a n ≠ ⊤ := by
  constructor
  · rintro ⟨_, ⟨n, hpn, hn, -⟩⟩
    exact ⟨n, hpn, hn⟩
  · rintro ⟨n, hpn, hn⟩
    exact ⟨_, mem_secantSlopes.mpr ⟨n, hpn, hn, rfl⟩⟩

variable {a : ℕ → WithTop ℝ} {p : ℕ}

/-- Secants from a finite height of an admissible sequence have a real lower bound. -/
theorem IsAdmissible.bddBelow_secantSlopes (ha : IsAdmissible a) (hp : a p ≠ ⊤) :
    BddBelow (secantSlopes a p) := by
  obtain ⟨c, m, hcm⟩ := isAdmissible_iff.mp ha
  have hpbound := hcm p
  rw [← WithTop.coe_untop₀_of_ne_top hp, WithTop.coe_le_coe] at hpbound
  refine ⟨m + (c + m * p - (a p).untop₀), ?_⟩
  rintro _ ⟨n, hpn, hn, rfl⟩
  have hnbound := hcm n
  rw [← WithTop.coe_untop₀_of_ne_top hn, WithTop.coe_le_coe] at hnbound
  have hpos : (0 : ℝ) < n - p := sub_pos.mpr (Nat.cast_lt.mpr hpn)
  have hone : (1 : ℝ) ≤ n - p := by
    have : (p : ℝ) + 1 ≤ n := by exact_mod_cast hpn
    linarith
  rw [le_div_iff₀ hpos]
  nlinarith [mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr hpbound) (sub_nonneg.mpr hone)]

/-- The infimum of later secant slopes supports an admissible sequence at its first
finite height. The conclusion also holds when there are no later finite heights. -/
theorem isSupportingLine_sInf_secantSlopes (ha : IsAdmissible a) (hp : a p ≠ ⊤)
    (hfirst : ∀ n < p, a n = ⊤) :
    IsSupportingLine a (sInf (secantSlopes a p))
      ((a p).untop₀ - sInf (secantSlopes a p) * p) := by
  apply isSupportingLine_iff_forall.mpr
  intro n
  by_cases hn : a n = ⊤
  · simp [hn]
  rw [← WithTop.coe_untop₀_of_ne_top hn, WithTop.coe_le_coe]
  rcases lt_trichotomy n p with hnp | rfl | hpn
  · exact False.elim (hn (hfirst n hnp))
  · simp
  · have hs := csInf_le (ha.bddBelow_secantSlopes hp)
      (mem_secantSlopes.mpr ⟨n, hpn, hn, rfl⟩)
    have hpos : (0 : ℝ) < n - p := sub_pos.mpr (Nat.cast_lt.mpr hpn)
    rw [le_div_iff₀ hpos] at hs
    linarith

/-- Every endpoint attaining the initial infimum gives an affine segment of the
envelope, from the first finite point to that endpoint. -/
theorem lowerConvexEnvelope_eq_of_secantSlope_eq_sInf
    (ha : IsAdmissible a) (hp : a p ≠ ⊤) (hfirst : ∀ n < p, a n = ⊤)
    {b : ℕ} (hpb : p < b) (hb : a b ≠ ⊤)
    (hbmin : ((a b).untop₀ - (a p).untop₀) / ((b : ℝ) - p) =
      sInf (secantSlopes a p)) {n : ℕ} (hpn : p ≤ n) (hnb : n ≤ b) :
    lowerConvexEnvelope a n =
      (((a p).untop₀ + sInf (secantSlopes a p) * ((n : ℝ) - p) : ℝ) : WithTop ℝ) := by
  let σ := sInf (secantSlopes a p)
  let c := (a p).untop₀ - σ * p
  have hline : IsSupportingLine a σ c := isSupportingLine_sInf_secantSlopes ha hp hfirst
  have hle := le_lowerConvexEnvelope (isConvexSeq_affine c σ)
    (isSupportingLine_iff_forall.mp hline)
  have henvelope : IsSupportingLine (lowerConvexEnvelope a) σ c :=
    isSupportingLine_iff_forall.mpr hle
  have hcontact (k : ℕ) (hk : a k = ((c + σ * k : ℝ) : WithTop ℝ)) :
      k ∈ supportingFace (lowerConvexEnvelope a) σ c := by
    exact mem_supportingFace.mpr
      (le_antisymm ((lowerConvexEnvelope_le ha k).trans_eq hk) (hle k))
  have hpface := hcontact p (by
    simp only [c, sub_add_cancel, WithTop.coe_untop₀_of_ne_top hp])
  have hbface := hcontact b (by
    rw [← WithTop.coe_untop₀_of_ne_top hb, WithTop.coe_eq_coe]
    have hpos : (0 : ℝ) < b - p := sub_pos.mpr (Nat.cast_lt.mpr hpb)
    have hs : (a b).untop₀ - (a p).untop₀ = σ * ((b : ℝ) - p) :=
      (div_eq_iff (ne_of_gt hpos)).mp hbmin
    dsimp [c]
    linarith)
  have hface := (isConvexSeq_lowerConvexEnvelope a).ordConnected_supportingFace
    henvelope |>.out hpface hbface ⟨hpn, hnb⟩
  rw [mem_supportingFace] at hface
  convert hface using 2
  dsimp [c]
  ring

/-- If the initial slope infimum is not attained, every larger slope is exceeded
downwards by secants whose endpoints are arbitrarily far to the right. -/
theorem exists_secantSlope_lt_of_sInf_notMem
    (ha : IsAdmissible a) (hp : a p ≠ ⊤) (hne : (secantSlopes a p).Nonempty)
    (hnot : sInf (secantSlopes a p) ∉ secantSlopes a p)
    {r : ℝ} (hr : sInf (secantSlopes a p) < r) (N : ℕ) :
    ∃ n, N < n ∧ p < n ∧ a n ≠ ⊤ ∧
      ((a n).untop₀ - (a p).untop₀) / ((n : ℝ) - p) < r := by
  let f := fun n : ℕ => ((a n).untop₀ - (a p).untop₀) / ((n : ℝ) - p)
  let s : Set ℕ := {n | p < n ∧ a n ≠ ⊤ ∧ n ≤ N}
  have hfinite : s.Finite := (Set.finite_Iic N).subset fun _ hn => hn.2.2
  have hexists {t : ℝ} (ht : sInf (secantSlopes a p) < t) :
      ∃ n, p < n ∧ a n ≠ ⊤ ∧ f n < t := by
    obtain ⟨_, ⟨n, hpn, hn, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne ht
    exact ⟨n, hpn, hn, hlt⟩
  rcases s.eq_empty_or_nonempty with hempty | hs
  · obtain ⟨n, hpn, hn, hlt⟩ := hexists hr
    refine ⟨n, ?_, hpn, hn, hlt⟩
    by_contra hN
    have hns : n ∈ s := ⟨hpn, hn, le_of_not_gt hN⟩
    simp [hempty] at hns
  · obtain ⟨i, hi, hmin⟩ := Set.exists_min_image s f hfinite hs
    have himem : f i ∈ secantSlopes a p := mem_secantSlopes.mpr ⟨i, hi.1, hi.2.1, rfl⟩
    have hiinf : sInf (secantSlopes a p) < f i :=
      lt_of_le_of_ne (csInf_le (ha.bddBelow_secantSlopes hp) himem)
        (fun heq => hnot (heq ▸ himem))
    obtain ⟨n, hpn, hn, hlt⟩ := hexists (lt_min hr hiinf)
    refine ⟨n, ?_, hpn, hn, hlt.trans_le (min_le_left _ _)⟩
    by_contra hN
    exact (not_lt_of_ge (hmin n ⟨hpn, hn, le_of_not_gt hN⟩))
      (hlt.trans_le (min_le_right _ _))

/-- A nonattained initial slope infimum gives an affine ray, even when the
coefficient heights themselves do not meet that ray again. -/
theorem lowerConvexEnvelope_eq_of_sInf_secantSlopes_notMem
    (ha : IsAdmissible a) (hp : a p ≠ ⊤) (hfirst : ∀ n < p, a n = ⊤)
    (hne : (secantSlopes a p).Nonempty)
    (hnot : sInf (secantSlopes a p) ∉ secantSlopes a p)
    {n : ℕ} (hpn : p ≤ n) :
    lowerConvexEnvelope a n =
      (((a p).untop₀ + sInf (secantSlopes a p) * ((n : ℝ) - p) : ℝ) : WithTop ℝ) := by
  let σ := sInf (secantSlopes a p)
  have hlower := le_lowerConvexEnvelope
    (isConvexSeq_affine ((a p).untop₀ - σ * p) σ)
    (isSupportingLine_iff_forall.mp (isSupportingLine_sInf_secantSlopes ha hp hfirst)) n
  have hlower' : (((a p).untop₀ + σ * ((n : ℝ) - p) : ℝ) : WithTop ℝ) ≤
      lowerConvexEnvelope a n := by
    convert hlower using 1
    congr 1
    ring
  rcases eq_or_lt_of_le hpn with rfl | hpn
  · rw [lowerConvexEnvelope_eq_of_forall_lt ha hfirst]
    simp only [sub_self, mul_zero, add_zero, WithTop.coe_untop₀_of_ne_top hp]
  obtain ⟨k, hnk, hpk, hk, -⟩ :=
    exists_secantSlope_lt_of_sInf_notMem ha hp hne hnot (lt_add_one σ) n
  have henvp : lowerConvexEnvelope a p = a p :=
    lowerConvexEnvelope_eq_of_forall_lt ha hfirst
  have henvp_fin : lowerConvexEnvelope a p ≠ ⊤ := henvp ▸ hp
  have henvk_fin := ne_top_of_le_ne_top hk (lowerConvexEnvelope_le ha k)
  have henvn_fin := (isConvexSeq_lowerConvexEnvelope a).ne_top_of_le_of_le
    henvp_fin henvk_fin hpn.le hnk.le
  refine le_antisymm ?_ hlower'
  rw [← WithTop.coe_untop₀_of_ne_top henvn_fin, WithTop.coe_le_coe]
  by_contra hupper
  have hD : (0 : ℝ) < n - p := sub_pos.mpr (Nat.cast_lt.mpr hpn)
  have hτ : σ < ((lowerConvexEnvelope a n).untop₀ - (a p).untop₀) / ((n : ℝ) - p) := by
    rw [lt_div_iff₀ hD]
    linarith
  obtain ⟨b, hnb, hpb, hb, hs⟩ :=
    exists_secantSlope_lt_of_sInf_notMem ha hp hne hnot hτ n
  have henvb_fin := ne_top_of_le_ne_top hb (lowerConvexEnvelope_le ha b)
  have hchord := (isConvexSeq_lowerConvexEnvelope a).chord_inequality
    henvp_fin henvb_fin hpn.le hnb.le
  rw [henvp] at hchord
  have hbupper := WithTop.untop₀_le_untop₀ hb (lowerConvexEnvelope_le ha b)
  have hB : (0 : ℝ) < b - p := sub_pos.mpr (Nat.cast_lt.mpr hpb)
  rw [div_lt_div_iff₀ hB hD] at hs
  have hbound := mul_le_mul_of_nonneg_left hbupper hD.le
  nlinarith

/-- If indices attaining the initial minimal slope are unbounded, the initial
affine segment extends to an entire ray. -/
theorem lowerConvexEnvelope_eq_of_unbounded_minimal_secant_indices
    (ha : IsAdmissible a) (hp : a p ≠ ⊤) (hfirst : ∀ n < p, a n = ⊤)
    (hunbounded : ¬ BddAbove {b : ℕ | p < b ∧ a b ≠ ⊤ ∧
      ((a b).untop₀ - (a p).untop₀) / ((b : ℝ) - p) = sInf (secantSlopes a p)})
    {n : ℕ} (hpn : p ≤ n) :
    lowerConvexEnvelope a n =
      (((a p).untop₀ + sInf (secantSlopes a p) * ((n : ℝ) - p) : ℝ) : WithTop ℝ) := by
  obtain ⟨b, ⟨hpb, hb, hbmin⟩, hnb⟩ := not_bddAbove_iff.mp hunbounded n
  exact lowerConvexEnvelope_eq_of_secantSlope_eq_sInf ha hp hfirst hpb hb hbmin hpn hnb.le

/-- The first finite unit edge of the envelope has slope equal to the infimum of
the secants from its first point. A later finite coefficient guarantees this edge
exists; no slope is assigned to an empty or singleton polygon. -/
theorem unitSlope_lowerConvexEnvelope_eq_sInf_secantSlopes
    (ha : IsAdmissible a) (hp : a p ≠ ⊤) (hfirst : ∀ n < p, a n = ⊤)
    (hne : (secantSlopes a p).Nonempty) :
    unitSlope (lowerConvexEnvelope a) p = sInf (secantSlopes a p) := by
  have hs : lowerConvexEnvelope a (p + 1) =
      (((a p).untop₀ + sInf (secantSlopes a p) * (((p + 1 : ℕ) : ℝ) - p) : ℝ) :
        WithTop ℝ) := by
    by_cases hmem : sInf (secantSlopes a p) ∈ secantSlopes a p
    · obtain ⟨b, hpb, hb, hmin⟩ := mem_secantSlopes.mp hmem
      exact lowerConvexEnvelope_eq_of_secantSlope_eq_sInf ha hp hfirst hpb hb hmin.symm
        (Nat.le_succ p) hpb
    · exact lowerConvexEnvelope_eq_of_sInf_secantSlopes_notMem ha hp hfirst hne hmem
        (Nat.le_succ p)
  rw [unitSlope_def, hs, lowerConvexEnvelope_eq_of_forall_lt ha hfirst,
    WithTop.untop₀_coe]
  push_cast
  ring

end TauCeti

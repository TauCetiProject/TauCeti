/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Envelope
public import TauCeti.Data.EReal.Operations

/-!
# Supporting values of height sequences

The supporting value of a height sequence at slope `σ` is the infimum of its
heights after subtracting `σ * n`. When finite, it is the greatest real intercept
of an affine line of slope `σ` below the sequence. Its values lie in `EReal`: the empty
sequence has supporting value `⊤`, while a tilted sequence unbounded below has
value `⊥`. Thus supporting values are defined even when no convex envelope exists.

The affine-minorant characterization shows that an admissible sequence and its
lower convex envelope have identical supporting values. Translation and shear
of the heights give the corresponding translation and parameter shift of the
supporting values. Convex heights, including infinite heights outside their finite
domain, are reconstructed as the supremum of their supporting lines. Consequently a convex
height sequence lies below another sequence exactly when its supporting values do.

The inclusion `WithTop.toEReal` regards heights in `WithTop ℝ` as extended reals
without installing a new coercion.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §3.
* K. S. Kedlaya, [*Newton polygons*](https://kskedlaya.org/18.787/newton-poly.pdf),
  MIT 18.787, fall 2007, §§1–3. Kedlaya plots coefficient points at negative
  indices; our convention uses positive indices, so the geometric slope has the
  opposite sign.
-/

public section

namespace TauCeti

/-- The infimum of the tilted heights at slope `σ`. The inclusion `WithTop.toEReal`
regards a height in `WithTop ℝ` as an extended real, so missing heights contribute
`⊤` and no individual height contributes `⊥`. -/
noncomputable def supportingValue (a : ℕ → WithTop ℝ) (σ : ℝ) : EReal :=
  ⨅ n : ℕ, (a n).toEReal - ((σ * n : ℝ) : EReal)

/-- The supporting value is the extended-real infimum of the tilted heights. -/
theorem supportingValue_def (a : ℕ → WithTop ℝ) (σ : ℝ) :
    supportingValue a σ =
      ⨅ n : ℕ, (a n).toEReal - ((σ * n : ℝ) : EReal) := (rfl)

variable {a b h : ℕ → WithTop ℝ} {c σ τ : ℝ}

/-- A lower bound on the supporting value is a lower bound on every tilted height. -/
theorem le_supportingValue_iff {r : EReal} :
    r ≤ supportingValue a σ ↔
      ∀ n, r ≤ (a n).toEReal - ((σ * n : ℝ) : EReal) :=
  le_iInf_iff

/-- A real intercept lies below the supporting value exactly when its affine
line lies below every height. No admissibility assumption is needed. -/
theorem coe_le_supportingValue_iff :
    (c : EReal) ≤ supportingValue a σ ↔
      ∀ n : ℕ, ((c + σ * n : ℝ) : WithTop ℝ) ≤ a n := by
  rw [le_supportingValue_iff]
  apply forall_congr'
  intro n
  rw [EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _))
    (.inl (EReal.coe_ne_top _)), ← EReal.coe_add]
  rw [← WithTop.toEReal_coe, WithTop.toEReal_le_toEReal_iff]

/-- A real intercept lies below the supporting value exactly when its affine line
lies below every finite height, compared as real numbers. -/
theorem coe_le_supportingValue_iff_untop₀ :
    (c : EReal) ≤ supportingValue a σ ↔
      ∀ n, a n ≠ ⊤ → c + σ * n ≤ (a n).untop₀ := by
  rw [coe_le_supportingValue_iff]
  constructor
  · intro hc n hn
    simpa only [WithTop.untop₀_coe] using WithTop.untop₀_le_untop₀ hn (hc n)
  · intro hc n
    by_cases hn : a n = ⊤
    · simp [hn]
    · exact WithTop.le_of_untop₀_le_untop₀ WithTop.coe_ne_top
        (by simpa only [WithTop.untop₀_coe] using hc n hn)

/-- The supporting value lies below each tilted height. -/
theorem supportingValue_le (a : ℕ → WithTop ℝ) (σ : ℝ) (n : ℕ) :
    supportingValue a σ ≤
      (a n).toEReal - ((σ * n : ℝ) : EReal) :=
  iInf_le _ n

/-- Increasing the heights increases every supporting value. -/
theorem supportingValue_mono (hab : a ≤ b) (σ : ℝ) :
    supportingValue a σ ≤ supportingValue b σ :=
  iInf_mono fun n => EReal.sub_le_sub (WithTop.toEReal_le_toEReal_iff.mpr (hab n)) le_rfl

/-- On natural-number indices the supporting value is antitone in the slope. -/
theorem supportingValue_antitone (a : ℕ → WithTop ℝ) : Antitone (supportingValue a) := by
  intro σ τ hστ
  exact iInf_mono fun n => EReal.sub_le_sub le_rfl
    (EReal.coe_le_coe (mul_le_mul_of_nonneg_right hστ (Nat.cast_nonneg n)))

/-- The empty point sequence has supporting value `⊤` at every slope. -/
@[simp]
theorem supportingValue_top (σ : ℝ) : supportingValue (⊤ : ℕ → WithTop ℝ) σ = ⊤ := by
  exact iInf_eq_top.mpr fun n => by
    rw [Pi.top_apply, WithTop.toEReal_top, EReal.top_sub_coe]

/-- A supporting value equals `⊤` exactly when the point sequence is empty. -/
@[simp]
theorem supportingValue_eq_top_iff : supportingValue a σ = ⊤ ↔ a = ⊤ := by
  constructor
  · intro hs
    funext n
    have hn := supportingValue_le a σ n
    rw [hs] at hn
    rw [EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _))
      (.inl (EReal.coe_ne_top _)), EReal.top_add_coe, top_le_iff,
      WithTop.toEReal_eq_top_iff] at hn
    exact hn
  · rintro rfl
    exact supportingValue_top σ

/-- A nonempty sequence has supporting value strictly below `⊤`, even when the
infimum is `⊥`. -/
theorem supportingValue_lt_top_iff :
    supportingValue a σ < ⊤ ↔ ∃ n, a n ≠ ⊤ := by
  rw [lt_top_iff_ne_top, ne_eq, supportingValue_eq_top_iff]
  simp only [funext_iff, Pi.top_apply, not_forall]

/-- A supporting value is not `⊥` exactly when there is a real affine minorant
with the specified slope. -/
theorem supportingValue_ne_bot_iff :
    supportingValue a σ ≠ ⊥ ↔
      ∃ c : ℝ, ∀ n : ℕ, ((c + σ * n : ℝ) : WithTop ℝ) ≤ a n := by
  constructor
  · intro hs
    exact ⟨(supportingValue a σ).toReal,
      coe_le_supportingValue_iff.mp (EReal.coe_toReal_le hs)⟩
  · rintro ⟨c, hc⟩
    exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot c) (coe_le_supportingValue_iff.mpr hc)

/-- The value `⊥` means that the tilted heights are unbounded below, equivalently
that no real affine line of this slope lies below the sequence. -/
theorem supportingValue_eq_bot_iff :
    supportingValue a σ = ⊥ ↔
      ∀ c : ℝ, ∃ n : ℕ, a n < ((c + σ * n : ℝ) : WithTop ℝ) := by
  rw [← not_iff_not]
  simp only [supportingValue_ne_bot_iff, not_forall, not_exists, not_lt]

/-- Admissibility means that at least one slope has supporting value above `⊥`. -/
theorem isAdmissible_iff_exists_supportingValue_ne_bot :
    IsAdmissible a ↔ ∃ σ : ℝ, supportingValue a σ ≠ ⊥ := by
  simp only [supportingValue_ne_bot_iff, isAdmissible_iff]
  exact exists_comm

/-- A finite supporting value is equivalent to nonempty support and a real
minorant of the specified slope. -/
theorem exists_coe_eq_supportingValue_iff :
    (∃ r : ℝ, (r : EReal) = supportingValue a σ) ↔
      (∃ n, a n ≠ ⊤) ∧
        ∃ c : ℝ, ∀ n : ℕ, ((c + σ * n : ℝ) : WithTop ℝ) ≤ a n := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨supportingValue_lt_top_iff.mp (hr ▸ EReal.coe_lt_top r),
      supportingValue_ne_bot_iff.mp (hr ▸ EReal.coe_ne_bot r)⟩
  · rintro ⟨hne, hline⟩
    exact ⟨_, EReal.coe_toReal (ne_of_lt (supportingValue_lt_top_iff.mpr hne))
      (supportingValue_ne_bot_iff.mpr hline)⟩

/-- A lower convex envelope has the same supporting values as the original
sequence. This is independent of the chosen construction of the envelope. -/
theorem IsLowerConvexEnvelope.supportingValue_eq (hh : IsLowerConvexEnvelope a h) (σ : ℝ) :
    supportingValue h σ = supportingValue a σ := by
  refine le_antisymm (supportingValue_mono hh.le σ) ?_
  by_contra hle
  obtain ⟨c, hc, hc'⟩ := EReal.exists_between_coe_real (lt_of_not_ge hle)
  have hline := coe_le_supportingValue_iff.mp hc'.le
  have hminor := hh.greatest (isConvexSeq_affine c σ) hline
  exact (not_le_of_gt hc) (coe_le_supportingValue_iff.mpr hminor)

/-- Taking the lower convex envelope of an admissible sequence preserves its
supporting-value function. -/
theorem supportingValue_lowerConvexEnvelope (ha : IsAdmissible a) :
    supportingValue (lowerConvexEnvelope a) = supportingValue a :=
  funext (isLowerConvexEnvelope_lowerConvexEnvelope ha).supportingValue_eq

/-! ### Reconstruction from supporting lines -/

/-- A convex height sequence is the supremum of all its supporting lines.
The equality holds also at infinite heights, for empty and singleton domains,
and at indices outside the finite domain. -/
theorem IsConvexSeq.iSup_supportingValue_add (hh : IsConvexSeq h) (n : ℕ) :
    (⨆ σ : ℝ, supportingValue h σ + ((σ * n : ℝ) : EReal)) =
      (h n).toEReal := by
  refine le_antisymm (iSup_le fun σ => EReal.add_le_of_le_sub (supportingValue_le h σ n)) ?_
  by_contra hle
  obtain ⟨r, hr, hr'⟩ := EReal.exists_between_coe_real (lt_of_not_ge hle)
  have hrh : (r : WithTop ℝ) ≤ h n :=
    WithTop.toEReal_le_toEReal_iff.mp ((WithTop.toEReal_coe r).trans_le hr'.le)
  obtain ⟨c, σ, hline, hrc⟩ := (hh.coe_le_iff_exists_affine_minorant n r).mp hrh
  have hs : ((c + σ * n : ℝ) : EReal) ≤
      supportingValue h σ + ((σ * n : ℝ) : EReal) := by
    rw [EReal.coe_add]
    exact add_le_add (coe_le_supportingValue_iff.mpr hline) le_rfl
  exact (not_le_of_gt hr) ((EReal.coe_le_coe hrc).trans
    (hs.trans (le_iSup (fun σ : ℝ => supportingValue h σ + ((σ * n : ℝ) : EReal)) σ)))

/-- A convex height sequence lies below another height sequence exactly when its supporting
values do. The second sequence need not be convex. -/
theorem IsConvexSeq.le_iff_forall_supportingValue_le (hh : IsConvexSeq h) :
    h ≤ a ↔ ∀ σ, supportingValue h σ ≤ supportingValue a σ := by
  refine ⟨fun hha σ => supportingValue_mono hha σ, fun hle n => ?_⟩
  rw [← WithTop.toEReal_le_toEReal_iff, ← hh.iSup_supportingValue_add n]
  exact iSup_le fun σ => (add_le_add (hle σ) le_rfl).trans
    (EReal.add_le_of_le_sub (supportingValue_le a σ n))

/-- The lower convex envelope of an admissible sequence is reconstructed from
the supporting values of the sequence itself. -/
theorem iSup_supportingValue_add_eq_lowerConvexEnvelope (ha : IsAdmissible a) (n : ℕ) :
    (⨆ σ : ℝ, supportingValue a σ + ((σ * n : ℝ) : EReal)) =
      (lowerConvexEnvelope a n).toEReal := by
  rw [← supportingValue_lowerConvexEnvelope ha]
  exact (isConvexSeq_lowerConvexEnvelope a).iSup_supportingValue_add n

/-- Adding a real affine height translates the supporting value and shifts its
slope parameter. The statement includes both infinite supporting values. -/
theorem supportingValue_add_affine (a : ℕ → WithTop ℝ) (c m σ : ℝ) :
    supportingValue (fun n => a n + ((c + m * n : ℝ) : WithTop ℝ)) σ =
      supportingValue a (σ - m) + (c : EReal) := by
  have hterm (n : ℕ) :
      (a n + ((c + m * n : ℝ) : WithTop ℝ)).toEReal -
          ((σ * n : ℝ) : EReal) =
        ((a n).toEReal - (((σ - m) * n : ℝ) : EReal)) -
          ((-c : ℝ) : EReal) := by
    induction a n using WithTop.recTopCoe with
    | top => simp only [top_add, WithTop.toEReal_top, EReal.top_sub_coe]
    | coe r =>
      rw [← WithTop.coe_add, WithTop.toEReal_coe, WithTop.toEReal_coe]
      simp only [← EReal.coe_sub]
      congr 1
      ring
  calc
    _ = ⨅ n : ℕ, ((a n).toEReal -
          (((σ - m) * n : ℝ) : EReal)) - ((-c : ℝ) : EReal) := iInf_congr hterm
    _ = supportingValue a (σ - m) - ((-c : ℝ) : EReal) :=
      EReal.iInf_sub_coe _ (-c)
    _ = supportingValue a (σ - m) + (c : EReal) := by
      rw [EReal.coe_neg]
      rw [sub_eq_add_neg, neg_neg]

end TauCeti

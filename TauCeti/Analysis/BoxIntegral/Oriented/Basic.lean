/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoxIntegral.IntervalIntegral
public import TauCeti.Analysis.BoxIntegral.HenstockPartition
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Oriented Henstock integrals on real intervals

`HasHenstockIntervalIntegral f a b y` is the existing Henstock box integral on the one-dimensional
interval box, with the sign reversed when `b < a` and value zero when the endpoints coincide.
No new choice of integral values is introduced. Restriction and subdivision use Mathlib's
subbox theorem and box additivity, and apply to conditionally integrable functions.
-/

public section

noncomputable section

open MeasureTheory Set

open BoxIntegral

namespace TauCeti.BoxIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual Henstock box integral with the orientation of a raw real parameter interval. -/
def HasHenstockIntervalIntegral (f : ℝ → E) (a b : ℝ) (y : E) : Prop :=
  if hab : a < b then
    HasIntegral (intervalBox a b hab) IntegrationParams.Henstock (fun x ↦ f (x 0))
      BoxAdditiveMap.volume y
  else if hba : b < a then
    HasIntegral (intervalBox b a hba) IntegrationParams.Henstock (fun x ↦ f (x 0))
      BoxAdditiveMap.volume (-y)
  else y = 0

/-- Genuine existence of an oriented Henstock interval integral. -/
def HenstockIntervalIntegrable (f : ℝ → E) (a b : ℝ) : Prop := ∃ y, HasHenstockIntervalIntegral
  f a b y

variable {f g : ℝ → E} {a b c d : ℝ} {y z : E}

/-- Oriented gauge integrability is existence of an actual integral value. -/
theorem henstockIntervalIntegrable_iff :
    HenstockIntervalIntegrable f a b ↔ ∃ y, HasHenstockIntervalIntegral f a b y := Iff.rfl


/-- On a positively oriented interval the predicate is exactly the existing box predicate. -/
theorem hasHenstockIntervalIntegral_iff_of_lt (hab : a < b) :
    HasHenstockIntervalIntegral f a b y ↔ HasIntegral (intervalBox a b hab)
      IntegrationParams.Henstock
      (fun x ↦ f (x 0)) BoxAdditiveMap.volume y := by
  simp [HasHenstockIntervalIntegral, hab]

/-- On a negatively oriented interval the existing box value has the opposite sign. -/
theorem hasHenstockIntervalIntegral_iff_of_gt (hba : b < a) :
    HasHenstockIntervalIntegral f a b y ↔ HasIntegral (intervalBox b a hba)
      IntegrationParams.Henstock
      (fun x ↦ f (x 0)) BoxAdditiveMap.volume (-y) := by
  simp [HasHenstockIntervalIntegral, hba, hba.not_gt]


/-- On positive intervals, oriented gauge integrability is existing box integrability. -/
theorem henstockIntervalIntegrable_iff_of_lt (hab : a < b) :
    HenstockIntervalIntegrable f a b ↔ Integrable (intervalBox a b hab) IntegrationParams.Henstock
      (fun x ↦ f (x 0)) BoxAdditiveMap.volume := by
  simp only [henstockIntervalIntegrable_iff, hasHenstockIntervalIntegral_iff_of_lt hab,
    BoxIntegral.Integrable]


/-- On negative intervals, oriented gauge integrability is existing box integrability. -/
theorem henstockIntervalIntegrable_iff_of_gt (hba : b < a) :
    HenstockIntervalIntegrable f a b ↔ Integrable (intervalBox b a hba)
      IntegrationParams.Henstock (fun x ↦ f (x 0)) BoxAdditiveMap.volume := by
  rw [henstockIntervalIntegrable_iff, BoxIntegral.Integrable]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨-y, (hasHenstockIntervalIntegral_iff_of_gt hba).mp hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨-y, (hasHenstockIntervalIntegral_iff_of_gt hba).mpr (by simpa only [neg_neg] using hy)⟩

@[simp]
theorem hasHenstockIntervalIntegral_same : HasHenstockIntervalIntegral f a a y ↔ y = 0 := by
  simp [HasHenstockIntervalIntegral]


/-- Every raw function is gauge integrable on a zero-length interval. -/
@[simp]
theorem henstockIntervalIntegrable_refl (f : ℝ → E) (a : ℝ) : HenstockIntervalIntegrable f a a :=
  ⟨0, by simp⟩

/-- Every raw function has integral zero over a zero-length parameter interval. -/
theorem hasHenstockIntervalIntegral_refl (f : ℝ → E) (a : ℝ) : HasHenstockIntervalIntegral f a a
  0 := by simp

/-- Reversing the parameter interval negates its actual gauge integral. -/
theorem HasHenstockIntervalIntegral.symm (h : HasHenstockIntervalIntegral f a b y) :
    HasHenstockIntervalIntegral f b a (-y) := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · simpa only [hasHenstockIntervalIntegral_iff_of_lt hab,
      hasHenstockIntervalIntegral_iff_of_gt hab, neg_neg] using h
  · simp only [hasHenstockIntervalIntegral_same] at h ⊢
    simp [h]
  · simpa only [hasHenstockIntervalIntegral_iff_of_gt hba,
      hasHenstockIntervalIntegral_iff_of_lt hba] using h

/-- Gauge interval integral values are unique, for either orientation. -/
theorem HasHenstockIntervalIntegral.unique (h : HasHenstockIntervalIntegral f a b y)
    (h' : HasHenstockIntervalIntegral f a b z) : y = z := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact ((hasHenstockIntervalIntegral_iff_of_lt hab).mp h).unique
      ((hasHenstockIntervalIntegral_iff_of_lt hab).mp h')
  · exact (hasHenstockIntervalIntegral_same.mp h).trans (hasHenstockIntervalIntegral_same.mp
    h').symm
  · exact neg_injective (((hasHenstockIntervalIntegral_iff_of_gt hba).mp h).unique
      ((hasHenstockIntervalIntegral_iff_of_gt hba).mp h'))

/-- Existence of a gauge interval value supplies genuine integrability. -/
theorem HasHenstockIntervalIntegral.henstockIntervalIntegrable
    (h : HasHenstockIntervalIntegral f a b y) :
    HenstockIntervalIntegrable f a b := ⟨y, h⟩

/-- Changing a raw integrand outside the unoriented interval changes no Henstock value. -/
theorem HasHenstockIntervalIntegral.congr (h : HasHenstockIntervalIntegral f a b y) (hfg : EqOn
  f g (uIcc a b)) :
    HasHenstockIntervalIntegral g a b y := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · rw [hasHenstockIntervalIntegral_iff_of_lt hab] at h ⊢
    apply (hasIntegral_congr _ _ ?_ (fun _ _ ↦ rfl) _).mp h
    intro x hx
    exact hfg (by simpa only [uIcc_of_le hab.le] using mem_Icc_intervalBox.mp hx)
  · simpa only [hasHenstockIntervalIntegral_same] using h
  · rw [hasHenstockIntervalIntegral_iff_of_gt hba] at h ⊢
    apply (hasIntegral_congr _ _ ?_ (fun _ _ ↦ rfl) _).mp h
    intro x hx
    exact hfg (by simpa only [uIcc_of_ge hba.le] using mem_Icc_intervalBox.mp hx)

/-- Almost-everywhere equal integrands have the same oriented Henstock value. -/
theorem HasHenstockIntervalIntegral.congr_ae (h : HasHenstockIntervalIntegral f a b y)
    (hfg : f =ᵐ[volume.restrict (uIoc a b)] g) : HasHenstockIntervalIntegral g a b y := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · rw [hasHenstockIntervalIntegral_iff_of_lt hab] at h ⊢
    exact h.congr_ae (ae_eq_intervalBox hab (by simpa only [uIoc_of_le hab.le] using hfg)) rfl
  · simpa only [hasHenstockIntervalIntegral_same] using h
  · rw [hasHenstockIntervalIntegral_iff_of_gt hba] at h ⊢
    exact h.congr_ae (ae_eq_intervalBox hba (by simpa only [uIoc_of_ge hba.le] using hfg)) rfl

/-- Addition is valid without absolute or Bochner integrability. -/
theorem HasHenstockIntervalIntegral.add (hf : HasHenstockIntervalIntegral f a b y)
    (hg : HasHenstockIntervalIntegral g a b z) : HasHenstockIntervalIntegral (fun t ↦ f t + g t)
      a b (y + z) := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · rw [hasHenstockIntervalIntegral_iff_of_lt hab] at *
    simpa only [Pi.add_def] using hf.add hg
  · simp only [hasHenstockIntervalIntegral_same] at *
    simp [hf, hg]
  · rw [hasHenstockIntervalIntegral_iff_of_gt hba] at *
    simpa only [Pi.add_def, neg_add] using hf.add hg

/-- Scalar multiplication of an oriented gauge integral. -/
theorem HasHenstockIntervalIntegral.smul (hf : HasHenstockIntervalIntegral f a b y) (r : ℝ) :
    HasHenstockIntervalIntegral (fun t ↦ r • f t) a b (r • y) := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · rw [hasHenstockIntervalIntegral_iff_of_lt hab] at *
    simpa only [Pi.smul_def] using hf.smul r
  · simp only [hasHenstockIntervalIntegral_same] at *
    simp [hf]
  · rw [hasHenstockIntervalIntegral_iff_of_gt hba] at *
    simpa only [Pi.smul_def, smul_neg] using hf.smul r

/-- Negation of an oriented gauge integrand. -/
theorem HasHenstockIntervalIntegral.neg (hf : HasHenstockIntervalIntegral f a b y) :
    HasHenstockIntervalIntegral (fun t ↦ -f t) a b (-y) := by
  simpa only [neg_one_smul] using hf.smul (-1)

/-- Subtraction of oriented gauge integrals. -/
theorem HasHenstockIntervalIntegral.sub (hf : HasHenstockIntervalIntegral f a b y)
    (hg : HasHenstockIntervalIntegral g a b z) : HasHenstockIntervalIntegral (fun t ↦ f t - g t)
      a b (y - z) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- Reversing endpoints preserves existence of an oriented gauge integral. -/
theorem HenstockIntervalIntegrable.symm (h : HenstockIntervalIntegrable f a b) :
    HenstockIntervalIntegrable f b a := by
  obtain ⟨y, hy⟩ := henstockIntervalIntegrable_iff.mp h
  exact hy.symm.henstockIntervalIntegrable

/-- Addition preserves existence of oriented gauge integrals. -/
theorem HenstockIntervalIntegrable.add (hf : HenstockIntervalIntegrable f a b)
    (hg : HenstockIntervalIntegrable g a b) : HenstockIntervalIntegrable (fun t ↦ f t + g t) a b
      := by
  obtain ⟨y, hy⟩ := henstockIntervalIntegrable_iff.mp hf
  obtain ⟨z, hz⟩ := henstockIntervalIntegrable_iff.mp hg
  exact (hy.add hz).henstockIntervalIntegrable

/-- Scalar multiplication preserves existence of an oriented gauge integral. -/
theorem HenstockIntervalIntegrable.smul (hf : HenstockIntervalIntegrable f a b) (r : ℝ) :
    HenstockIntervalIntegrable (fun t ↦ r • f t) a b := by
  obtain ⟨y, hy⟩ := henstockIntervalIntegrable_iff.mp hf
  exact (hy.smul r).henstockIntervalIntegrable


/-- Negation preserves existence of an oriented Henstock integral. -/
theorem HenstockIntervalIntegrable.neg (hf : HenstockIntervalIntegrable f a b) :
    HenstockIntervalIntegrable (fun t ↦ -f t) a b := by
  obtain ⟨y, hy⟩ := henstockIntervalIntegrable_iff.mp hf
  exact hy.neg.henstockIntervalIntegrable

/-- Subtraction preserves existence of oriented Henstock integrals. -/
theorem HenstockIntervalIntegrable.sub (hf : HenstockIntervalIntegrable f a b)
    (hg : HenstockIntervalIntegrable g a b) :
    HenstockIntervalIntegrable (fun t ↦ f t - g t) a b := by
  obtain ⟨y, hy⟩ := henstockIntervalIntegrable_iff.mp hf
  obtain ⟨z, hz⟩ := henstockIntervalIntegrable_iff.mp hg
  exact (hy.sub hz).henstockIntervalIntegrable

/-- A constant has oriented Henstock integral `(b - a) • v` for every pair of endpoints,
without any completeness assumption on its values. -/
theorem hasHenstockIntervalIntegral_const (v : E) (a b : ℝ) :
    HasHenstockIntervalIntegral (fun _ ↦ v) a b ((b - a) • v) := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · apply (hasHenstockIntervalIntegral_iff_of_lt hab).mpr
    simpa [BoxAdditiveMap.volume_apply] using
      (BoxIntegral.hasIntegral_const (I := intervalBox a b hab)
        (l := IntegrationParams.Henstock) (vol := BoxAdditiveMap.volume) v)
  · simp
  · apply (hasHenstockIntervalIntegral_iff_of_gt hba).mpr
    rw [← neg_smul, neg_sub]
    simpa [BoxAdditiveMap.volume_apply] using
      (BoxIntegral.hasIntegral_const (I := intervalBox b a hba)
        (l := IntegrationParams.Henstock) (vol := BoxAdditiveMap.volume) v)

/-- The zero function has oriented Henstock integral zero for every pair of endpoints. -/
@[simp]
theorem hasHenstockIntervalIntegral_zero (a b : ℝ) :
    HasHenstockIntervalIntegral (0 : ℝ → E) a b 0 := by
  simpa only [Pi.zero_def, smul_zero] using hasHenstockIntervalIntegral_const (0 : E) a b

variable [CompleteSpace E]

/-- Bochner integrability supplies the genuine oriented Henstock value, including zero and
reversed intervals. -/
theorem _root_.IntervalIntegrable.hasHenstockIntervalIntegral (hf : IntervalIntegrable f volume
  a b) :
    HasHenstockIntervalIntegral f a b (∫ t in a..b, f t) := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact (hasHenstockIntervalIntegral_iff_of_lt hab).mpr (hf.hasBoxIntegral hab _ rfl)
  · simp
  · rw [hasHenstockIntervalIntegral_iff_of_gt hba, ← intervalIntegral.integral_symm]
    exact hf.symm.hasBoxIntegral hba _ rfl

/-- Under genuine Bochner integrability, the oriented gauge value agrees with `intervalIntegral`. -/
theorem HasHenstockIntervalIntegral.eq_intervalIntegral (h : HasHenstockIntervalIntegral f a b y)
    (hf : IntervalIntegrable f volume a b) : y = ∫ t in a..b, f t :=
  h.unique hf.hasHenstockIntervalIntegral

private theorem restrict_of_lt (hab : a < b) (h : HasHenstockIntervalIntegral f a b y)
    (hcd : uIcc c d ⊆ Icc a b) : HenstockIntervalIntegrable f c d := by
  have hbox := (hasHenstockIntervalIntegral_iff_of_lt hab).mp h
  rcases lt_trichotomy c d with hlt | rfl | hgt
  · have hc := hcd left_mem_uIcc
    have hd := hcd right_mem_uIcc
    obtain ⟨z, hz⟩ := hbox.integrable.to_subbox
      ((intervalBox_le_intervalBox_iff hab hlt).mpr ⟨hc.1, hd.2⟩)
    exact ⟨z, (hasHenstockIntervalIntegral_iff_of_lt hlt).mpr hz⟩
  · exact (hasHenstockIntervalIntegral_refl f c).henstockIntervalIntegrable
  · have hc := hcd left_mem_uIcc
    have hd := hcd right_mem_uIcc
    obtain ⟨z, hz⟩ := hbox.integrable.to_subbox
      ((intervalBox_le_intervalBox_iff hab hgt).mpr ⟨hd.1, hc.2⟩)
    exact ⟨-z, (hasHenstockIntervalIntegral_iff_of_gt hgt).mpr (by simpa using hz)⟩

/-- Genuine conditional Henstock integrability restricts to any oriented subinterval. -/
theorem HasHenstockIntervalIntegral.henstockIntervalIntegrable_of_subset (h :
  HasHenstockIntervalIntegral f a b y)
    (hcd : uIcc c d ⊆ uIcc a b) : HenstockIntervalIntegrable f c d := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact restrict_of_lt hab h (by simpa only [uIcc_of_le hab.le] using hcd)
  · have hc : c = a := by simpa using hcd left_mem_uIcc
    have hd : d = a := by simpa using hcd right_mem_uIcc
    subst c
    subst d
    exact (hasHenstockIntervalIntegral_refl f a).henstockIntervalIntegrable
  · exact restrict_of_lt hba h.symm (by simpa only [uIcc_of_ge hba.le] using hcd)


/-- Integrability, without a named value, also restricts to every oriented subinterval. -/
theorem HenstockIntervalIntegrable.mono_set (h : HenstockIntervalIntegrable f a b)
    (hcd : uIcc c d ⊆ uIcc a b) : HenstockIntervalIntegrable f c d := by
  obtain ⟨y, hy⟩ := h
  exact hy.henstockIntervalIntegrable_of_subset hcd

private theorem integral_intervalBox_split (hac : a < c) (hcb : c < b)
    (h : Integrable (intervalBox a b (hac.trans hcb)) IntegrationParams.Henstock
      (fun x ↦ f (x 0)) BoxAdditiveMap.volume) :
    integral (intervalBox a c hac) IntegrationParams.Henstock (fun x ↦ f (x 0))
        BoxAdditiveMap.volume +
      integral (intervalBox c b hcb) IntegrationParams.Henstock (fun x ↦ f (x 0))
        BoxAdditiveMap.volume =
      integral (intervalBox a b (hac.trans hcb)) IntegrationParams.Henstock
        (fun x ↦ f (x 0)) BoxAdditiveMap.volume := by
  let I := intervalBox a b (hac.trans hcb)
  have hL := splitLower_intervalBox hac hcb
  have hR := splitUpper_intervalBox hac hcb
  have hadd := h.toBoxAdditive.map_split_add (I := I) le_rfl 0 c
  rw [hL, hR] at hadd
  exact hadd

/-- Splitting a gauge-integrable positively oriented interval gives actual integrals on both
pieces whose values add to the original value, without a Bochner-integrability assumption. -/
theorem HasHenstockIntervalIntegral.split_of_le (h : HasHenstockIntervalIntegral f a b y)
    (hac : a ≤ c) (hcb : c ≤ b) :
    ∃ y₁ y₂, HasHenstockIntervalIntegral f a c y₁ ∧ HasHenstockIntervalIntegral f c b y₂ ∧ y₁ +
      y₂ = y := by
  rcases hac.eq_or_lt with rfl | hac
  · exact ⟨0, y, hasHenstockIntervalIntegral_refl f a, h, zero_add y⟩
  rcases hcb.eq_or_lt with rfl | hcb
  · exact ⟨y, 0, h, hasHenstockIntervalIntegral_refl f c, add_zero y⟩
  have hbox := (hasHenstockIntervalIntegral_iff_of_lt (hac.trans hcb)).mp h
  have hL := hbox.integrable.to_subbox
    ((intervalBox_le_intervalBox_iff (hac.trans hcb) hac).mpr ⟨le_rfl, hcb.le⟩)
  have hR := hbox.integrable.to_subbox
    ((intervalBox_le_intervalBox_iff (hac.trans hcb) hcb).mpr ⟨hac.le, le_rfl⟩)
  refine ⟨_, _, (hasHenstockIntervalIntegral_iff_of_lt hac).mpr hL.hasIntegral,
    (hasHenstockIntervalIntegral_iff_of_lt hcb).mpr hR.hasIntegral, ?_⟩
  exact (integral_intervalBox_split hac hcb hbox.integrable).trans hbox.integral_eq

/-- Splitting at any point of the unoriented interval preserves the original orientation.
The two actual gauge values add to the value of the whole interval. -/
theorem HasHenstockIntervalIntegral.split (h : HasHenstockIntervalIntegral f a b y) (hc : c ∈
  uIcc a b) :
    ∃ y₁ y₂, HasHenstockIntervalIntegral f a c y₁ ∧ HasHenstockIntervalIntegral f c b y₂ ∧ y₁ +
      y₂ = y := by
  rcases le_total a b with hab | hba
  · rw [uIcc_of_le hab] at hc
    exact h.split_of_le hc.1 hc.2
  · rw [uIcc_of_ge hba] at hc
    obtain ⟨y₁, y₂, h₁, h₂, hy⟩ := h.symm.split_of_le hc.1 hc.2
    refine ⟨-y₂, -y₁, h₂.symm, h₁.symm, ?_⟩
    rw [← neg_add, add_comm, hy, neg_neg]

/-- Any independently established values on the two pieces agree with the subdivision values. -/
private theorem add_eq_of_mem (h : HasHenstockIntervalIntegral f a b y) (hc : c ∈ uIcc a b)
    {y₁ y₂ : E} (h₁ : HasHenstockIntervalIntegral f a c y₁) (h₂ : HasHenstockIntervalIntegral f
      c b y₂) :
    y₁ + y₂ = y := by
  obtain ⟨z₁, z₂, hz₁, hz₂, hz⟩ := h.split hc
  rwa [h₁.unique hz₁, h₂.unique hz₂]

private theorem trans_of_le (h₁ : HasHenstockIntervalIntegral f a c y)
    (h₂ : HasHenstockIntervalIntegral f c b z) (hac : a ≤ c) (hcb : c ≤ b) :
    HasHenstockIntervalIntegral f a b (y + z) := by
  rcases hac.eq_or_lt with rfl | hac
  · rw [hasHenstockIntervalIntegral_same] at h₁
    simpa only [h₁, zero_add] using h₂
  rcases hcb.eq_or_lt with rfl | hcb
  · rw [hasHenstockIntervalIntegral_same] at h₂
    simpa only [h₂, add_zero] using h₁
  let I := intervalBox a b (hac.trans hcb)
  have hL := splitLower_intervalBox hac hcb
  have hR := splitUpper_intervalBox hac hcb
  have hi : ∀ J ∈ Prepartition.split I 0 c,
      Integrable J IntegrationParams.Henstock (fun x ↦ f (x 0)) BoxAdditiveMap.volume := by
    intro J hJ
    rw [Prepartition.mem_split_iff, hL, hR] at hJ
    rcases hJ with hJ | hJ
    · cases WithBot.coe_injective hJ
      exact ((hasHenstockIntervalIntegral_iff_of_lt hac).mp h₁).integrable
    · cases WithBot.coe_injective hJ
      exact ((hasHenstockIntervalIntegral_iff_of_lt hcb).mp h₂).integrable
  have hg := hasIntegral_Henstock_of_partition (Prepartition.split I 0 c)
    (Prepartition.isPartitionSplit I 0 c)
    (fun J ↦ integral J IntegrationParams.Henstock (fun x ↦ f (x 0)) BoxAdditiveMap.volume)
    (fun J hJ ↦ (hi J hJ).hasIntegral)
  have hg' := (hasHenstockIntervalIntegral_iff_of_lt (hac.trans hcb)).mpr hg
  rwa [← add_eq_of_mem hg' (by rw [uIcc_of_le (hac.trans hcb).le]; exact ⟨hac.le, hcb.le⟩) h₁ h₂]
    at hg'

private theorem trans_forward (h₁ : HasHenstockIntervalIntegral f a c y)
    (h₂ : HasHenstockIntervalIntegral f c b z) (hab : a ≤ b) :
    HasHenstockIntervalIntegral f a b (y + z) := by
  rcases le_or_gt a c with hac | hca
  · rcases le_or_gt c b with hcb | hbc
    · exact trans_of_le h₁ h₂ hac hcb
    · obtain ⟨u, v, hu, hv, huv⟩ := h₁.split_of_le hab hbc.le
      have hv' : v = -z := hv.unique h₂.symm
      have hu' : u = y + z := by
        rw [hv'] at huv
        exact eq_add_of_sub_eq (by simpa only [sub_eq_add_neg] using huv)
      simpa only [hu'] using hu
  · obtain ⟨u, v, hu, hv, huv⟩ := h₂.split_of_le hca.le hab
    have hu' : u = -y := hu.unique h₁.symm
    have hv' : v = y + z := by rw [hu'] at huv; exact eq_add_of_neg_add_eq huv
    simpa only [hv'] using hv

/-- Local conditional Henstock integrals glue across any intermediate parameter, including
backtracking beyond either endpoint. No integrability on the whole interval is assumed. -/
theorem HasHenstockIntervalIntegral.trans (h₁ : HasHenstockIntervalIntegral f a c y)
    (h₂ : HasHenstockIntervalIntegral f c b z) : HasHenstockIntervalIntegral f a b (y + z) := by
  rcases le_total a b with hab | hba
  · exact trans_forward h₁ h₂ hab
  · simpa only [neg_add, neg_neg, add_comm] using
      (trans_forward h₂.symm h₁.symm hba).symm


/-- Any finite subdivision whose nodes lie in the endpoint interval admits actual gauge values
on its pieces whose sum is the value on the whole interval. Nodes may repeat and backtrack. -/
theorem HasHenstockIntervalIntegral.split_fin {N : ℕ} {s : Fin (N + 1) → ℝ}
    (h : HasHenstockIntervalIntegral f (s 0) (s (Fin.last N)) y)
    (hs : ∀ i, s i ∈ uIcc (s 0) (s (Fin.last N))) :
    ∃ v : Fin N → E, (∀ i, HasHenstockIntervalIntegral f (s i.castSucc) (s i.succ) (v i)) ∧
      ∑ i, v i = y := by
  have hprefix (i : Fin (N + 1)) : HenstockIntervalIntegrable f (s 0) (s i) :=
    h.henstockIntervalIntegrable_of_subset (uIcc_subset_uIcc_left (hs i))
  choose F hF using hprefix
  refine ⟨fun i ↦ F i.succ - F i.castSucc, ?_, ?_⟩
  · intro i
    simpa only [sub_eq_add_neg, add_comm] using (hF i.castSucc).symm.trans (hF i.succ)
  · have htel : ∑ i : Fin N, (F i.succ - F i.castSucc) = F (Fin.last N) - F 0 := by
      cases N with
      | zero => simp
      | succ n =>
        have hIic : Finset.Iic (Fin.last n) = Finset.univ := Finset.Iic_top
        simpa only [hIic, Fin.succ_last] using Fin.sum_Iic_sub (Fin.last n) F
    rw [htel, (hF (Fin.last N)).unique h, hasHenstockIntervalIntegral_same.mp (hF 0), sub_zero]

/-- Gauge integrability on adjacent parameter intervals glues, including backtracking. -/
theorem HenstockIntervalIntegrable.trans (h₁ : HenstockIntervalIntegrable f a c)
    (h₂ : HenstockIntervalIntegrable f c b) : HenstockIntervalIntegrable f a b := by
  obtain ⟨y, hy⟩ := henstockIntervalIntegrable_iff.mp h₁
  obtain ⟨z, hz⟩ := henstockIntervalIntegrable_iff.mp h₂
  exact (hy.trans hz).henstockIntervalIntegrable

/-- The oriented additivity identity holds at any intermediate parameter, including backtracking. -/
theorem HasHenstockIntervalIntegral.add_eq (h : HasHenstockIntervalIntegral f a b y)
    {y₁ y₂ : E} (h₁ : HasHenstockIntervalIntegral f a c y₁) (h₂ : HasHenstockIntervalIntegral f
      c b y₂) :
    y₁ + y₂ = y := (h₁.trans h₂).unique h

/-- Conditional Henstock integrals on a finite sequence of parameter intervals glue to the
sum of their values. The nodes may repeat, reverse direction, and leave the endpoint interval. -/
theorem hasHenstockIntervalIntegral_of_subdivision {N : ℕ} {s : Fin (N + 1) → ℝ} {v : Fin N → E}
    (hv : ∀ i, HasHenstockIntervalIntegral f (s i.castSucc) (s i.succ) (v i)) :
    HasHenstockIntervalIntegral f (s 0) (s (Fin.last N)) (∑ i, v i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have ht := ih (s := fun i ↦ s i.succ) (v := fun i ↦ v i.succ) (fun i ↦ hv i.succ)
    simpa only [Fin.sum_univ_succ, Fin.castSucc_zero, Fin.succ_last] using (hv 0).trans ht

end TauCeti.BoxIntegral

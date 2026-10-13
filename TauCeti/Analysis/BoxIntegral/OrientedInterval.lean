/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoxIntegral.IntervalIntegral
public import TauCeti.Analysis.BoxIntegral.HenstockPartition
public import TauCeti.Algebra.BigOperators.Fin

/-!
# Oriented Henstock integrals on real intervals

`HasIntervalIntegral f a b y` is the existing Henstock box integral on the one-dimensional
interval box, with the sign reversed when `b < a` and value zero when the endpoints coincide.
No new choice of integral values is introduced. Restriction and subdivision use Mathlib's
subbox theorem and box additivity, and apply to conditionally integrable functions.
-/

public section

noncomputable section

open MeasureTheory Set

namespace BoxIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual Henstock box integral with the orientation of a raw real parameter interval. -/
def HasIntervalIntegral (f : ℝ → E) (a b : ℝ) (y : E) : Prop :=
  if hab : a < b then
    HasIntegral (intervalBox a b hab) IntegrationParams.Henstock (fun x ↦ f (x 0))
      BoxAdditiveMap.volume y
  else if hba : b < a then
    HasIntegral (intervalBox b a hba) IntegrationParams.Henstock (fun x ↦ f (x 0))
      BoxAdditiveMap.volume (-y)
  else y = 0

/-- Genuine existence of an oriented Henstock interval integral. -/
def IntegrableOnInterval (f : ℝ → E) (a b : ℝ) : Prop := ∃ y, HasIntervalIntegral f a b y

variable {f g : ℝ → E} {a b c d : ℝ} {y z : E}

/-- On a positively oriented interval the predicate is exactly the existing box predicate. -/
theorem hasIntervalIntegral_iff_of_lt (hab : a < b) :
    HasIntervalIntegral f a b y ↔ HasIntegral (intervalBox a b hab) IntegrationParams.Henstock
      (fun x ↦ f (x 0)) BoxAdditiveMap.volume y := by
  simp [HasIntervalIntegral, hab]

/-- On a negatively oriented interval the existing box value has the opposite sign. -/
theorem hasIntervalIntegral_iff_of_gt (hba : b < a) :
    HasIntervalIntegral f a b y ↔ HasIntegral (intervalBox b a hba) IntegrationParams.Henstock
      (fun x ↦ f (x 0)) BoxAdditiveMap.volume (-y) := by
  simp [HasIntervalIntegral, hba, hba.not_gt]

@[simp]
theorem hasIntervalIntegral_same : HasIntervalIntegral f a a y ↔ y = 0 := by
  simp [HasIntervalIntegral]

/-- Every raw function has integral zero over a zero-length parameter interval. -/
theorem hasIntervalIntegral_refl (f : ℝ → E) (a : ℝ) : HasIntervalIntegral f a a 0 := by simp

/-- Reversing the parameter interval negates its actual gauge integral. -/
theorem HasIntervalIntegral.symm (h : HasIntervalIntegral f a b y) :
    HasIntervalIntegral f b a (-y) := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · simpa only [hasIntervalIntegral_iff_of_lt hab, hasIntervalIntegral_iff_of_gt hab,
      neg_neg] using h
  · simp only [hasIntervalIntegral_same] at h ⊢
    simp [h]
  · simpa only [hasIntervalIntegral_iff_of_gt hba, hasIntervalIntegral_iff_of_lt hba] using h

/-- Gauge interval integral values are unique, for either orientation. -/
theorem HasIntervalIntegral.unique (h : HasIntervalIntegral f a b y)
    (h' : HasIntervalIntegral f a b z) : y = z := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact ((hasIntervalIntegral_iff_of_lt hab).mp h).unique
      ((hasIntervalIntegral_iff_of_lt hab).mp h')
  · exact (hasIntervalIntegral_same.mp h).trans (hasIntervalIntegral_same.mp h').symm
  · exact neg_injective (((hasIntervalIntegral_iff_of_gt hba).mp h).unique
      ((hasIntervalIntegral_iff_of_gt hba).mp h'))

/-- Existence of a gauge interval value supplies genuine integrability. -/
theorem HasIntervalIntegral.integrable (h : HasIntervalIntegral f a b y) :
    IntegrableOnInterval f a b := ⟨y, h⟩

/-- Changing a raw integrand outside the unoriented interval changes no Henstock value. -/
theorem HasIntervalIntegral.congr (h : HasIntervalIntegral f a b y) (hfg : EqOn f g (uIcc a b)) :
    HasIntervalIntegral g a b y := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · rw [hasIntervalIntegral_iff_of_lt hab] at h ⊢
    apply (hasIntegral_congr _ _ ?_ (fun _ _ ↦ rfl) _).mp h
    intro x hx
    exact hfg (by simpa only [uIcc_of_le hab.le] using mem_Icc_intervalBox.mp hx)
  · simpa only [hasIntervalIntegral_same] using h
  · rw [hasIntervalIntegral_iff_of_gt hba] at h ⊢
    apply (hasIntegral_congr _ _ ?_ (fun _ _ ↦ rfl) _).mp h
    intro x hx
    exact hfg (by simpa only [uIcc_of_ge hba.le] using mem_Icc_intervalBox.mp hx)

/-- Almost-everywhere equal integrands have the same oriented Henstock value. -/
theorem HasIntervalIntegral.congr_ae (h : HasIntervalIntegral f a b y)
    (hfg : f =ᵐ[volume.restrict (uIoc a b)] g) : HasIntervalIntegral g a b y := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · rw [hasIntervalIntegral_iff_of_lt hab] at h ⊢
    exact h.congr_ae (ae_eq_intervalBox hab (by simpa only [uIoc_of_le hab.le] using hfg)) rfl
  · simpa only [hasIntervalIntegral_same] using h
  · rw [hasIntervalIntegral_iff_of_gt hba] at h ⊢
    exact h.congr_ae (ae_eq_intervalBox hba (by simpa only [uIoc_of_ge hba.le] using hfg)) rfl

/-- Addition is valid without absolute or Bochner integrability. -/
theorem HasIntervalIntegral.add (hf : HasIntervalIntegral f a b y)
    (hg : HasIntervalIntegral g a b z) : HasIntervalIntegral (fun t ↦ f t + g t) a b (y + z) := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · rw [hasIntervalIntegral_iff_of_lt hab] at *
    simpa only [Pi.add_def] using hf.add hg
  · simp only [hasIntervalIntegral_same] at *
    simp [hf, hg]
  · rw [hasIntervalIntegral_iff_of_gt hba] at *
    simpa only [Pi.add_def, neg_add] using hf.add hg

/-- Scalar multiplication of an oriented gauge integral. -/
theorem HasIntervalIntegral.smul (hf : HasIntervalIntegral f a b y) (r : ℝ) :
    HasIntervalIntegral (fun t ↦ r • f t) a b (r • y) := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · rw [hasIntervalIntegral_iff_of_lt hab] at *
    simpa only [Pi.smul_def] using hf.smul r
  · simp only [hasIntervalIntegral_same] at *
    simp [hf]
  · rw [hasIntervalIntegral_iff_of_gt hba] at *
    simpa only [Pi.smul_def, smul_neg] using hf.smul r

/-- Negation of an oriented gauge integrand. -/
theorem HasIntervalIntegral.neg (hf : HasIntervalIntegral f a b y) :
    HasIntervalIntegral (fun t ↦ -f t) a b (-y) := by
  simpa only [neg_one_smul] using hf.smul (-1)

/-- Subtraction of oriented gauge integrals. -/
theorem HasIntervalIntegral.sub (hf : HasIntervalIntegral f a b y)
    (hg : HasIntervalIntegral g a b z) : HasIntervalIntegral (fun t ↦ f t - g t) a b (y - z) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

variable [CompleteSpace E]

/-- Bochner integrability supplies the genuine oriented Henstock value, including zero and
reversed intervals. The converse is deliberately not required. -/
theorem _root_.IntervalIntegrable.hasIntervalIntegral (hf : IntervalIntegrable f volume a b) :
    HasIntervalIntegral f a b (∫ t in a..b, f t) := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact (hasIntervalIntegral_iff_of_lt hab).mpr (hf.hasBoxIntegral hab _ rfl)
  · simp
  · rw [hasIntervalIntegral_iff_of_gt hba, ← intervalIntegral.integral_symm]
    exact hf.symm.hasBoxIntegral hba _ rfl

/-- Under genuine Bochner integrability, the oriented gauge value agrees with `intervalIntegral`. -/
theorem HasIntervalIntegral.eq_intervalIntegral (h : HasIntervalIntegral f a b y)
    (hf : IntervalIntegrable f volume a b) : y = ∫ t in a..b, f t :=
  h.unique hf.hasIntervalIntegral

/-- Constants give nondegenerate witnesses to the oriented gauge predicate. -/
theorem hasIntervalIntegral_const (v : E) (a b : ℝ) :
    HasIntervalIntegral (fun _ ↦ v) a b ((b - a) • v) := by
  simpa only [intervalIntegral.integral_const] using
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ v) volume a b).hasIntervalIntegral

private theorem intervalBox_le_intervalBox {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hac : a ≤ c) (hdb : d ≤ b) : intervalBox c d hcd ≤ intervalBox a b hab := by
  rw [Box.le_iff_bounds]
  exact ⟨fun _ ↦ by simpa only [intervalBox_lower] using hac,
    fun _ ↦ by simpa only [intervalBox_upper] using hdb⟩

private theorem restrict_of_lt (hab : a < b) (h : HasIntervalIntegral f a b y)
    (hcd : uIcc c d ⊆ Icc a b) : IntegrableOnInterval f c d := by
  have hbox := (hasIntervalIntegral_iff_of_lt hab).mp h
  rcases lt_trichotomy c d with hlt | rfl | hgt
  · have hc := hcd left_mem_uIcc
    have hd := hcd right_mem_uIcc
    obtain ⟨z, hz⟩ := hbox.integrable.to_subbox
      (intervalBox_le_intervalBox hab hlt hc.1 hd.2)
    exact ⟨z, (hasIntervalIntegral_iff_of_lt hlt).mpr hz⟩
  · exact (hasIntervalIntegral_refl f c).integrable
  · have hc := hcd left_mem_uIcc
    have hd := hcd right_mem_uIcc
    obtain ⟨z, hz⟩ := hbox.integrable.to_subbox
      (intervalBox_le_intervalBox hab hgt hd.1 hc.2)
    exact ⟨-z, (hasIntervalIntegral_iff_of_gt hgt).mpr (by simpa using hz)⟩

/-- Genuine conditional Henstock integrability restricts to any oriented subinterval. -/
theorem HasIntervalIntegral.restrict (h : HasIntervalIntegral f a b y)
    (hcd : uIcc c d ⊆ uIcc a b) : IntegrableOnInterval f c d := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact restrict_of_lt hab h (by simpa only [uIcc_of_le hab.le] using hcd)
  · have hc : c = a := by simpa using hcd left_mem_uIcc
    have hd : d = a := by simpa using hcd right_mem_uIcc
    subst c
    subst d
    exact (hasIntervalIntegral_refl f a).integrable
  · exact restrict_of_lt hba h.symm (by simpa only [uIcc_of_ge hba.le] using hcd)

/-- Integrability, without a named value, also restricts to every oriented subinterval. -/
theorem IntegrableOnInterval.mono (h : IntegrableOnInterval f a b)
    (hcd : uIcc c d ⊆ uIcc a b) : IntegrableOnInterval f c d := by
  obtain ⟨y, hy⟩ := h
  exact hy.restrict hcd

private theorem intervalBox_splitLower (hac : a < c) (hcb : c < b) :
    (intervalBox a b (hac.trans hcb)).splitLower 0 c =
      (intervalBox a c hac : WithBot (Box (Fin 1))) := by
  rw [← Box.withBotCoe_inj]
  ext x
  simp only [Box.coe_splitLower, Box.coe_coe, mem_inter_iff, mem_ofPred_eq]
  change ((x ∈ intervalBox a b (hac.trans hcb)) ∧ x 0 ≤ c) ↔ x ∈ intervalBox a c hac
  simp only [mem_intervalBox, mem_Ioc]
  exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, h.2.trans hcb.le⟩, h.2⟩⟩

private theorem intervalBox_splitUpper (hac : a < c) (hcb : c < b) :
    (intervalBox a b (hac.trans hcb)).splitUpper 0 c =
      (intervalBox c b hcb : WithBot (Box (Fin 1))) := by
  rw [← Box.withBotCoe_inj]
  ext x
  simp only [Box.coe_splitUpper, Box.coe_coe, mem_inter_iff, mem_ofPred_eq]
  change ((x ∈ intervalBox a b (hac.trans hcb)) ∧ c < x 0) ↔ x ∈ intervalBox c b hcb
  simp only [mem_intervalBox, mem_Ioc]
  exact ⟨fun h ↦ ⟨h.2, h.1.2⟩, fun h ↦ ⟨⟨hac.trans h.1, h.2⟩, h.1⟩⟩

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
  have hL := intervalBox_splitLower hac hcb
  have hR := intervalBox_splitUpper hac hcb
  have hadd := h.toBoxAdditive.map_split_add (I := I) le_rfl 0 c
  rw [hL, hR] at hadd
  exact hadd

/-- Splitting a gauge-integrable positively oriented interval gives actual integrals on both
pieces whose values add to the original value, without a Bochner-integrability assumption. -/
theorem HasIntervalIntegral.split_of_le (h : HasIntervalIntegral f a b y)
    (hac : a ≤ c) (hcb : c ≤ b) :
    ∃ y₁ y₂, HasIntervalIntegral f a c y₁ ∧ HasIntervalIntegral f c b y₂ ∧ y₁ + y₂ = y := by
  rcases hac.eq_or_lt with rfl | hac
  · exact ⟨0, y, hasIntervalIntegral_refl f a, h, zero_add y⟩
  rcases hcb.eq_or_lt with rfl | hcb
  · exact ⟨y, 0, h, hasIntervalIntegral_refl f c, add_zero y⟩
  have hbox := (hasIntervalIntegral_iff_of_lt (hac.trans hcb)).mp h
  have hL := hbox.integrable.to_subbox
    (intervalBox_le_intervalBox (hac.trans hcb) hac le_rfl hcb.le)
  have hR := hbox.integrable.to_subbox
    (intervalBox_le_intervalBox (hac.trans hcb) hcb hac.le le_rfl)
  refine ⟨_, _, (hasIntervalIntegral_iff_of_lt hac).mpr hL.hasIntegral,
    (hasIntervalIntegral_iff_of_lt hcb).mpr hR.hasIntegral, ?_⟩
  exact (integral_intervalBox_split hac hcb hbox.integrable).trans hbox.integral_eq

/-- Splitting at any point of the unoriented interval preserves the original orientation.
The two actual gauge values add to the value of the whole interval. -/
theorem HasIntervalIntegral.split (h : HasIntervalIntegral f a b y) (hc : c ∈ uIcc a b) :
    ∃ y₁ y₂, HasIntervalIntegral f a c y₁ ∧ HasIntervalIntegral f c b y₂ ∧ y₁ + y₂ = y := by
  rcases le_total a b with hab | hba
  · rw [uIcc_of_le hab] at hc
    exact h.split_of_le hc.1 hc.2
  · rw [uIcc_of_ge hba] at hc
    obtain ⟨y₁, y₂, h₁, h₂, hy⟩ := h.symm.split_of_le hc.1 hc.2
    refine ⟨-y₂, -y₁, h₂.symm, h₁.symm, ?_⟩
    rw [← neg_add, add_comm, hy, neg_neg]

/-- Any independently established values on the two pieces agree with the subdivision values. -/
private theorem eq_add_of_mem (h : HasIntervalIntegral f a b y) (hc : c ∈ uIcc a b)
    {y₁ y₂ : E} (h₁ : HasIntervalIntegral f a c y₁) (h₂ : HasIntervalIntegral f c b y₂) :
    y₁ + y₂ = y := by
  obtain ⟨z₁, z₂, hz₁, hz₂, hz⟩ := h.split hc
  rwa [h₁.unique hz₁, h₂.unique hz₂]

/-- Any finite ordered subdivision, in either orientation and allowing repeated nodes, admits
actual gauge values on its pieces whose sum is the value on the entire interval. -/
theorem HasIntervalIntegral.split_fin {N : ℕ} {s : Fin (N + 1) → ℝ}
    (h : HasIntervalIntegral f (s 0) (s (Fin.last N)) y)
    (hs : Monotone s ∨ Antitone s) :
    ∃ v : Fin N → E, (∀ i, HasIntervalIntegral f (s i.castSucc) (s i.succ) (v i)) ∧
      ∑ i, v i = y := by
  have hmem (i j : Fin (N + 1)) (hij : i ≤ j) : s i ∈ uIcc (s 0) (s j) := by
    rcases hs with hs | hs
    · rw [uIcc_of_le (hs (Fin.zero_le j))]
      exact ⟨hs (Fin.zero_le i), hs hij⟩
    · rw [uIcc_of_ge (hs (Fin.zero_le j))]
      exact ⟨hs hij, hs (Fin.zero_le i)⟩
  have hprefix (i : Fin (N + 1)) : IntegrableOnInterval f (s 0) (s i) :=
    h.restrict (uIcc_subset_uIcc_left (hmem i (Fin.last N) (Fin.le_last i)))
  choose F hF using hprefix
  refine ⟨fun i ↦ F i.succ - F i.castSucc, ?_, ?_⟩
  · intro i
    obtain ⟨z₁, z₂, hz₁, hz₂, hz⟩ := (hF i.succ).split
      (hmem i.castSucc i.succ (Fin.castSucc_le_succ i))
    convert hz₂ using 1
    change F i.succ - F i.castSucc = z₂
    rw [← hz, (hF i.castSucc).unique hz₁, add_sub_cancel_left]
  · rw [Fin.sum_univ_succ_sub_castSucc, (hF (Fin.last N)).unique h,
      hasIntervalIntegral_same.mp (hF 0), sub_zero]

private theorem trans_of_le (h₁ : HasIntervalIntegral f a c y)
    (h₂ : HasIntervalIntegral f c b z) (hac : a ≤ c) (hcb : c ≤ b) :
    HasIntervalIntegral f a b (y + z) := by
  rcases hac.eq_or_lt with rfl | hac
  · rw [hasIntervalIntegral_same] at h₁
    simpa only [h₁, zero_add] using h₂
  rcases hcb.eq_or_lt with rfl | hcb
  · rw [hasIntervalIntegral_same] at h₂
    simpa only [h₂, add_zero] using h₁
  let I := intervalBox a b (hac.trans hcb)
  have hL := intervalBox_splitLower hac hcb
  have hR := intervalBox_splitUpper hac hcb
  have hi : ∀ J ∈ Prepartition.split I 0 c,
      Integrable J IntegrationParams.Henstock (fun x ↦ f (x 0)) BoxAdditiveMap.volume := by
    intro J hJ
    rw [Prepartition.mem_split_iff, hL, hR] at hJ
    rcases hJ with hJ | hJ
    · cases WithBot.coe_injective hJ
      exact ((hasIntervalIntegral_iff_of_lt hac).mp h₁).integrable
    · cases WithBot.coe_injective hJ
      exact ((hasIntervalIntegral_iff_of_lt hcb).mp h₂).integrable
  have hg := hasIntegral_Henstock_of_partition (Prepartition.split I 0 c)
    (Prepartition.isPartitionSplit I 0 c)
    (fun J ↦ integral J IntegrationParams.Henstock (fun x ↦ f (x 0)) BoxAdditiveMap.volume)
    (fun J hJ ↦ (hi J hJ).hasIntegral)
  have hg' := (hasIntervalIntegral_iff_of_lt (hac.trans hcb)).mpr hg
  rwa [← eq_add_of_mem hg' (by rw [uIcc_of_le (hac.trans hcb).le]; exact ⟨hac.le, hcb.le⟩) h₁ h₂]
    at hg'

private theorem trans_forward (h₁ : HasIntervalIntegral f a c y)
    (h₂ : HasIntervalIntegral f c b z) (hab : a ≤ b) :
    HasIntervalIntegral f a b (y + z) := by
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
theorem HasIntervalIntegral.trans (h₁ : HasIntervalIntegral f a c y)
    (h₂ : HasIntervalIntegral f c b z) : HasIntervalIntegral f a b (y + z) := by
  rcases le_total a b with hab | hba
  · exact trans_forward h₁ h₂ hab
  · simpa only [neg_add, neg_neg, add_comm] using
      (trans_forward h₂.symm h₁.symm hba).symm

/-- The oriented additivity identity holds at any intermediate parameter, including backtracking. -/
theorem HasIntervalIntegral.eq_add (h : HasIntervalIntegral f a b y)
    {y₁ y₂ : E} (h₁ : HasIntervalIntegral f a c y₁) (h₂ : HasIntervalIntegral f c b y₂) :
    y₁ + y₂ = y := (h₁.trans h₂).unique h

/-- Conditional Henstock integrals on a finite sequence of parameter intervals glue to the
sum of their values. The nodes may repeat, reverse direction, and leave the endpoint interval. -/
theorem hasIntervalIntegral_of_subdivision {N : ℕ} {s : Fin (N + 1) → ℝ} {v : Fin N → E}
    (hv : ∀ i, HasIntervalIntegral f (s i.castSucc) (s i.succ) (v i)) :
    HasIntervalIntegral f (s 0) (s (Fin.last N)) (∑ i, v i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have ht := ih (s := fun i ↦ s i.succ) (v := fun i ↦ v i.succ) (fun i ↦ hv i.succ)
    simpa only [Fin.sum_univ_succ, Fin.castSucc_zero, Fin.succ_last] using (hv 0).trans ht

end BoxIntegral

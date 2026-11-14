/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.Algebra.Star.MatrixUnits

/-!
# Polar Unitary Perturbation and Unitary Conjugacy of Matrix Units

Two nearby finite multi-block systems of matrix units in a C⋆-algebra are unitarily conjugate by a
unitary close to `1` in `Joined 1 u` (and with scalar part `1` in `Unitization ℂ A`). We first
develop `TauCeti.polarUnitary` for `‖z - 1‖ ≤ 1 / 3` (without order instances on `A`; compare
`Units.polarUnitary`) and apply it to `TauCeti.matrixUnitIntertwiner ℂ e f`.

## Main definitions

* `TauCeti.polarUnitaryElem`, `TauCeti.polarUnitary`.

## Main results

* `TauCeti.IsPartialIsometry.norm_le_one`, `TauCeti.polarUnitaryElem_mem_unitary`,
  `TauCeti.norm_polarUnitary_sub_one_le`, `TauCeti.conjugate_polarUnitary`.
* `TauCeti.IsMatrixUnitSystem.exists_unitary_conjugate_mem`,
  `TauCeti.IsMatrixUnitSystem.exists_unitary_conjugate`,
  `TauCeti.IsMatrixUnitSystem.exists_unitization_unitary_conjugate`.

## References

* B. Blackadar, *Operator Algebras*, Springer (2006), Proposition II.8.3.23.
* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge Univ. Press (1998), §4.6.
-/

public section

open scoped ContinuousFunctionalCalculus

namespace TauCeti

namespace IsPartialIsometry

/-- Every partial isometry in a C⋆-ring has norm at most `1`. -/
theorem norm_le_one {E : Type*} [NonUnitalNormedRing E] [StarRing E] [CStarRing E] {v : E}
    (hv : IsPartialIsometry v) : ‖v‖ ≤ 1 := by
  have hle : ‖star v * v‖ ≤ 1 := hv.isStarProjection_star_mul_self.norm_le _
  rw [CStarRing.norm_star_mul_self] at hle
  nlinarith [norm_nonneg v]

end IsPartialIsometry

section PolarUnitary

variable {A : Type*} [CStarAlgebra A]

/-- The polar-unitary candidate `z * cfc (fun x : ℝ ↦ (√x)⁻¹) (star z * z)`. -/
noncomputable def polarUnitaryElem (z : A) : A := z * cfc (fun x : ℝ ↦ (√x)⁻¹) (star z * z)

/-- Unfold `TauCeti.polarUnitaryElem`. -/
theorem polarUnitaryElem_def (z : A) :
    polarUnitaryElem z = z * cfc (fun x : ℝ ↦ (√x)⁻¹) (star z * z) := (rfl)

/-- `polarUnitaryElem z` belongs to every closed unital `ℂ`-⋆-subalgebra containing `z`. -/
theorem polarUnitaryElem_mem {S : Type*} [SetLike S A] [SubringClass S A] [SMulMemClass S ℂ A]
    [StarMemClass S A] {s : S} [IsClosed (s : Set A)] {z : A} (hz : z ∈ s) :
    polarUnitaryElem z ∈ s := by
  rw [polarUnitaryElem_def]; exact mul_mem hz (cfc_mem (𝕜' := ℂ) _ (mul_mem (star_mem hz) hz))

private lemma norm_star_mul_self_sub_one_le (z : A) :
    ‖star z * z - 1‖ ≤ ‖z - 1‖ ^ 2 + 2 * ‖z - 1‖ := by
  rw [show star z * z - 1 = star (z - 1) * (z - 1) + (star (z - 1) + (z - 1)) by
    simp only [star_sub, star_one, sub_mul, mul_sub, one_mul, mul_one]; abel]
  have h1 : ‖star (z - 1) * (z - 1)‖ = ‖z - 1‖ ^ 2 := by rw [CStarRing.norm_star_mul_self, sq]
  have h2 := norm_add_le (star (z - 1)) (z - 1); rw [norm_star] at h2
  linarith [norm_add_le (star (z - 1) * (z - 1)) (star (z - 1) + (z - 1))]

private lemma spectrum_star_mul_self_sub_one_abs_le (z : A) {x : ℝ}
    (hx : x ∈ spectrum ℝ (star z * z)) : |x - 1| ≤ ‖star z * z - 1‖ := by
  have hsa : IsSelfAdjoint (star z * z) := IsSelfAdjoint.star_mul_self z
  have hcfc : cfc (fun t : ℝ ↦ t - 1) (star z * z) = star z * z - 1 := by
    rw [cfc_sub (fun t : ℝ ↦ t) _ (star z * z) continuousOn_id continuousOn_const,
      cfc_id' ℝ (star z * z) hsa, cfc_const_one ℝ (star z * z) hsa]
  simpa [Real.norm_eq_abs, hcfc] using
    norm_apply_le_norm_cfc (fun t : ℝ ↦ t - 1) (star z * z) hx
      (continuousOn_id.sub continuousOn_const) hsa

private lemma pos_of_mem_spectrum_star_mul_self {z : A} (hz : ‖z - 1‖ ≤ 1 / 3) {x : ℝ}
    (hx : x ∈ spectrum ℝ (star z * z)) : 0 < x := by
  have habs := spectrum_star_mul_self_sub_one_abs_le z hx
  have hlt : ‖z - 1‖ ^ 2 + 2 * ‖z - 1‖ ≤ 7 / 9 := by nlinarith [norm_nonneg (z - 1)]
  linarith [(abs_le.mp habs).1, norm_star_mul_self_sub_one_le z]

private lemma continuousOn_inv_sqrt_star_mul_self {z : A} (hz : ‖z - 1‖ ≤ 1 / 3) :
    ContinuousOn (fun x : ℝ ↦ (√x)⁻¹) (spectrum ℝ (star z * z)) :=
  Real.continuous_sqrt.continuousOn.inv₀ fun _ hx ↦
    (Real.sqrt_pos.mpr (pos_of_mem_spectrum_star_mul_self hz hx)).ne'

private lemma cfc_inv_sqrt_mul_sqrt_star_mul_self {z : A} (hz : ‖z - 1‖ ≤ 1 / 3) :
    cfc (fun x : ℝ ↦ (√x)⁻¹) (star z * z) * cfc Real.sqrt (star z * z) = 1 ∧
      cfc Real.sqrt (star z * z) * cfc (fun x : ℝ ↦ (√x)⁻¹) (star z * z) = 1 := by
  have hh_sa : IsSelfAdjoint (star z * z) := IsSelfAdjoint.star_mul_self z
  have hf_cont := continuousOn_inv_sqrt_star_mul_self hz
  have hs_cont : ContinuousOn Real.sqrt (spectrum ℝ (star z * z)) :=
    Real.continuous_sqrt.continuousOn
  exact ⟨by rw [← cfc_mul _ _ (star z * z) hf_cont hs_cont, ← cfc_const_one ℝ (star z * z) hh_sa]
            exact cfc_congr fun _ hx ↦
              inv_mul_cancel₀ (Real.sqrt_pos.mpr (pos_of_mem_spectrum_star_mul_self hz hx)).ne',
         by rw [← cfc_mul _ _ (star z * z) hs_cont hf_cont, ← cfc_const_one ℝ (star z * z) hh_sa]
            exact cfc_congr fun _ hx ↦
              mul_inv_cancel₀ (Real.sqrt_pos.mpr (pos_of_mem_spectrum_star_mul_self hz hx)).ne'⟩

/-- When `‖z - 1‖ ≤ 1 / 3`, `polarUnitaryElem z` is a unitary element of `A`. -/
theorem polarUnitaryElem_mem_unitary {z : A} (hz : ‖z - 1‖ ≤ 1 / 3) :
    polarUnitaryElem z ∈ unitary A := by
  set h : A := star z * z; set f : ℝ → ℝ := fun x ↦ (√x)⁻¹
  set w : A := cfc f h; set s : A := cfc Real.sqrt h
  have hw_sa : IsSelfAdjoint w := cfc_predicate f h
  obtain ⟨hws, hsw⟩ := cfc_inv_sqrt_mul_sqrt_star_mul_self hz
  have hss : s * s = h := by
    rw [← cfc_mul Real.sqrt Real.sqrt h Real.continuous_sqrt.continuousOn
      Real.continuous_sqrt.continuousOn]
    conv_rhs => rw [← cfc_id' ℝ h (IsSelfAdjoint.star_mul_self z)]
    exact cfc_congr fun _ hx ↦ Real.mul_self_sqrt (pos_of_mem_spectrum_star_mul_self hz hx).le
  have hleft : star (polarUnitaryElem z) * polarUnitaryElem z = 1 := by
    rw [polarUnitaryElem_def, star_mul, hw_sa.star_eq]
    calc w * star z * (z * w) = w * h * w := by simp only [h, mul_assoc]
      _ = (w * s) * (s * w) := by rw [← hss]; simp only [mul_assoc]
      _ = 1 := by rw [hws, hsw, mul_one]
  have hz_unit : IsUnit z := by
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one
      (show ‖1 - z‖ < 1 by rw [norm_sub_rev]; linarith)
  have hu_unit : IsUnit (polarUnitaryElem z) := hz_unit.mul (isUnit_iff_exists.mpr ⟨s, hws, hsw⟩)
  exact Unitary.mem_iff.mpr ⟨hleft, hu_unit.star.mul_right_inj.mp <| by
    rw [← mul_assoc, hleft, one_mul, mul_one]⟩

/-- Bundled unitary `polarUnitary z hz : unitary A` for `z : A` with `‖z - 1‖ ≤ 1 / 3`. -/
noncomputable def polarUnitary (z : A) (hz : ‖z - 1‖ ≤ 1 / 3) : unitary A :=
  ⟨polarUnitaryElem z, polarUnitaryElem_mem_unitary hz⟩

/-- Coercion of `TauCeti.polarUnitary` to the ambient C⋆-algebra. -/
@[simp] theorem coe_polarUnitary (z : A) (hz : ‖z - 1‖ ≤ 1 / 3) :
    ((polarUnitary z hz : unitary A) : A) = polarUnitaryElem z := (rfl)

/-- Quantitative distance bound `‖(polarUnitary z hz : A) - 1‖ ≤ 4 * ‖z - 1‖`. -/
theorem norm_polarUnitary_sub_one_le {z : A} (hz : ‖z - 1‖ ≤ 1 / 3) :
    ‖(polarUnitary z hz : A) - 1‖ ≤ 4 * ‖z - 1‖ := by
  set h : A := star z * z; set s : A := cfc Real.sqrt h; set u : unitary A := polarUnitary z hz
  have hz_eq : z = (u : A) * s := by
    change z = (z * cfc (fun x : ℝ ↦ (√x)⁻¹) h) * s
    rw [mul_assoc, (cfc_inv_sqrt_mul_sqrt_star_mul_self hz).1, mul_one]
  have hs_sub_le : ‖s - 1‖ ≤ ‖h - 1‖ := by
    rw [show s - 1 = cfc (fun x : ℝ ↦ √x - 1) h by
      rw [cfc_sub Real.sqrt _ h Real.continuous_sqrt.continuousOn continuousOn_const,
        cfc_const_one ℝ h (IsSelfAdjoint.star_mul_self z)]]
    refine norm_cfc_le (norm_nonneg _) fun x hx ↦ ?_
    rw [Real.norm_eq_abs]
    have hx_pos := pos_of_mem_spectrum_star_mul_self hz hx
    have hsqrt_pos := Real.sqrt_pos.mpr hx_pos
    have habs := spectrum_star_mul_self_sub_one_abs_le z hx
    have hprod : |x - 1| = |√x - 1| * (√x + 1) := by
      rw [show x - 1 = (√x - 1) * (√x + 1) by
        rw [show (√x - 1) * (√x + 1) = √x * √x - 1 by ring, Real.mul_self_sqrt hx_pos.le],
        abs_mul, abs_of_pos (a := √x + 1) (by linarith)]
    nlinarith [abs_nonneg (√x - 1)]
  have htri : ‖(u : A) - 1‖ ≤ ‖z - 1‖ + ‖s - 1‖ := by
    rw [show (u : A) - 1 = (z - 1) - (u : A) * (s - 1) by rw [hz_eq, mul_sub, mul_one]; abel,
      ← CStarRing.norm_coe_unitary_mul u (s - 1)]
    exact norm_sub_le _ _
  nlinarith [norm_star_mul_self_sub_one_le z, norm_nonneg (z - 1)]

/-- `polarUnitary z hz` lies in the connected component of `1` in `unitary A`. -/
theorem joined_one_polarUnitary {z : A} (hz : ‖z - 1‖ ≤ 1 / 3) : Joined 1 (polarUnitary z hz) :=
  Unitary.joined 1 (polarUnitary z hz) <| (norm_polarUnitary_sub_one_le hz).trans_lt (by linarith)

/-- Intertwining `y * z = z * x` and `star z * y = x * star z` pass to `polarUnitaryElem z`. -/
theorem intertwine_polarUnitaryElem {z x y : A} (h1 : y * z = z * x)
    (h2 : star z * y = x * star z) : y * polarUnitaryElem z = polarUnitaryElem z * x := by
  have hcomm_h : Commute (star z * z) x := by
    rw [Commute, SemiconjBy, mul_assoc, ← h1, ← mul_assoc, h2, mul_assoc]
  rw [polarUnitaryElem_def, ← mul_assoc, h1, mul_assoc,
    (hcomm_h.cfc_real (fun t : ℝ ↦ (√t)⁻¹)).symm.eq, ← mul_assoc]

/-- Adjoint-compatible intertwining relations become exact unitary conjugation by `polarUnitary`. -/
theorem conjugate_polarUnitary {z x y : A} (hz : ‖z - 1‖ ≤ 1 / 3)
    (h1 : y * z = z * x) (h2 : star z * y = x * star z) :
    (polarUnitary z hz : A) * x * star (polarUnitary z hz : A) = y := by
  rw [coe_polarUnitary, ← intertwine_polarUnitaryElem h1 h2, mul_assoc,
    (polarUnitaryElem_mem_unitary hz).2, mul_one]

end PolarUnitary

/-- If `z.fst = 1` and `‖z - 1‖ ≤ 1 / 3` in `Unitization ℂ A`, `(polarUnitaryElem z).fst = 1`. -/
theorem fst_polarUnitaryElem {A : Type*} [NonUnitalCStarAlgebra A] {z : Unitization ℂ A}
    (hz_fst : z.fst = 1) (hz : ‖z - 1‖ ≤ 1 / 3) : (polarUnitaryElem z).fst = 1 := by
  set h : Unitization ℂ A := star z * z; set f : ℝ → ℝ := fun x ↦ (√x)⁻¹
  let φ : Unitization ℂ A →⋆ₐ[ℂ] ℂ :=
    { Unitization.fstHom ℂ A with map_star' := Unitization.fst_star }
  have hφh : φ h = 1 := by change (star z * z).fst = 1; simp [hz_fst]
  have hφ_cfc : (cfc f h).fst = 1 := by
    change φ (cfc f h) = 1
    rw [φ.map_cfc f h (continuousOn_inv_sqrt_star_mul_self hz) Unitization.continuous_fst
      (IsSelfAdjoint.star_mul_self z) (hφh.symm ▸ IsSelfAdjoint.one ℂ), hφh]
    simp [f]
  rw [polarUnitaryElem_def, Unitization.fst_mul, hz_fst, hφ_cfc, mul_one]

namespace IsMatrixUnitSystem

section Unital

variable {κ A : Type*} {n : κ → Type*} [Fintype κ] [∀ r, Fintype (n r)] [CStarAlgebra A]
  {e f : ∀ r : κ, n r → n r → A}

/-- `matrixUnitIntertwiner ℂ e f` belongs to any unital `ℂ`-subring containing `e` and `f`. -/
theorem matrixUnitIntertwiner_mem {S : Type*} [SetLike S A] [SubringClass S A]
    [SMulMemClass S ℂ A] {s : S} (he_mem : ∀ r i j, e r i j ∈ s)
    (hf_mem : ∀ r i j, f r i j ∈ s) : matrixUnitIntertwiner ℂ e f ∈ s := by
  rw [matrixUnitIntertwiner_def, matrixUnitSupport_def, matrixUnitSupport_def]
  exact add_mem
    (mul_mem (sub_mem (one_mem s) (sum_mem fun r _ ↦ sum_mem fun i _ ↦ hf_mem r i i))
      (sub_mem (one_mem s) (sum_mem fun r _ ↦ sum_mem fun i _ ↦ he_mem r i i)))
    (sum_mem fun r _ ↦ SMulMemClass.smul_mem _ <|
      sum_mem fun a _ ↦ sum_mem fun b _ ↦ mul_mem (hf_mem r a b) (he_mem r b a))

/-- Norm estimate `‖matrixUnitIntertwiner ℂ e f - 1‖ ≤ 2 * (∑ r, card (n r)) * δ`. -/
theorem norm_matrixUnitIntertwiner_sub_one_le (he : IsMatrixUnitSystem e)
    {δ : ℝ} (hδ : 0 ≤ δ) (hdist : ∀ r i j, ‖f r i j - e r i j‖ ≤ δ) :
    ‖matrixUnitIntertwiner ℂ e f - 1‖ ≤ 2 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ := by
  rw [← he.matrixUnitIntertwiner_self (𝕜 := ℂ), matrixUnitIntertwiner_def,
    matrixUnitIntertwiner_def, add_sub_add_comm, ← sub_mul,
    show (1 - matrixUnitSupport f) - (1 - matrixUnitSupport e) =
      matrixUnitSupport e - matrixUnitSupport f by abel]
  simp only [← Finset.sum_sub_distrib, ← smul_sub, ← sub_mul]
  refine (norm_add_le _ _).trans ?_
  have hpart1 : ‖(matrixUnitSupport e - matrixUnitSupport f) * (1 - matrixUnitSupport e)‖ ≤
      (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ := by
    refine (norm_mul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _)
      (he.isStarProjection_support.one_sub.norm_le _)).trans ?_)
    simp only [matrixUnitSupport_def, ← Finset.sum_sub_distrib, Finset.sum_mul]
    exact (norm_sum_le _ _).trans <| Finset.sum_le_sum fun r _ ↦
      (norm_sum_le _ _).trans <| (Finset.sum_le_sum fun i _ ↦
        (norm_sub_rev (e r i i) (f r i i)).le.trans (hdist r i i)).trans (by simp)
  have hpart2 : ‖∑ r : κ, (Fintype.card (n r) : ℂ)⁻¹ •
      ∑ a : n r, ∑ b : n r, (f r a b - e r a b) * e r b a‖ ≤
      (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans <| Finset.sum_le_sum fun r _ ↦ ?_
    by_cases hcard : Fintype.card (n r) = 0
    · simp [hcard]
    · have hpos : (0 : ℝ) < Fintype.card (n r) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcard)
      rw [norm_smul, norm_inv, Complex.norm_natCast,
        ← inv_mul_cancel_left₀ hpos.ne' ((Fintype.card (n r) : ℝ) * δ)]
      gcongr
      have hb (a b : n r) : ‖(f r a b - e r a b) * e r b a‖ ≤ δ :=
        (norm_mul_le _ _).trans <| (mul_le_mul (hdist r a b)
          (he.isPartialIsometry r b a).norm_le_one (norm_nonneg _) hδ).trans (mul_one δ).le
      exact (norm_sum_le _ _).trans <| (Finset.sum_le_sum fun a _ ↦
        (norm_sum_le _ _).trans <| Finset.sum_le_sum fun b _ ↦ hb a b).trans (by simp)
  linarith

/-- **Unitary conjugacy of nearby systems of matrix units** (with subalgebra preservation). -/
theorem exists_unitary_conjugate_mem {S : Type*} [SetLike S A] [SubringClass S A]
    [SMulMemClass S ℂ A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)]
    (he : IsMatrixUnitSystem e) (hf : IsMatrixUnitSystem f)
    (he_mem : ∀ r i j, e r i j ∈ s) (hf_mem : ∀ r i j, f r i j ∈ s)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : 6 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ ≤ 1)
    (hdist : ∀ r i j, ‖f r i j - e r i j‖ ≤ δ) :
    ∃ u : unitary A, (u : A) ∈ s ∧ Joined 1 u ∧
      (∀ r i j, (u : A) * e r i j * star (u : A) = f r i j) ∧
      ‖(u : A) - 1‖ ≤ 8 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ := by
  set z : A := matrixUnitIntertwiner ℂ e f
  have hz_le := he.norm_matrixUnitIntertwiner_sub_one_le hδ hdist
  have hz_third : ‖z - 1‖ ≤ 1 / 3 := by linarith
  exact ⟨polarUnitary z hz_third, polarUnitaryElem_mem (matrixUnitIntertwiner_mem he_mem hf_mem),
    joined_one_polarUnitary hz_third, fun r i j ↦ conjugate_polarUnitary hz_third
      (he.intertwine_matrixUnitIntertwiner ℂ hf r i j)
      (he.star_matrixUnitIntertwiner_mul ℂ hf r i j),
    by linarith [norm_polarUnitary_sub_one_le hz_third]⟩

/-- **Unitary conjugacy of nearby systems of matrix units** in a unital C⋆-algebra. -/
theorem exists_unitary_conjugate (he : IsMatrixUnitSystem e) (hf : IsMatrixUnitSystem f)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : 6 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ ≤ 1)
    (hdist : ∀ r i j, ‖f r i j - e r i j‖ ≤ δ) :
    ∃ u : unitary A, Joined 1 u ∧ (∀ r i j, (u : A) * e r i j * star (u : A) = f r i j) ∧
      ‖(u : A) - 1‖ ≤ 8 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ := by
  have : IsClosed ((⊤ : StarSubalgebra ℂ A) : Set A) := isClosed_univ
  obtain ⟨u, -, hjoined, hconj, hnorm⟩ :=
    he.exists_unitary_conjugate_mem (s := (⊤ : StarSubalgebra ℂ A)) hf
      (fun _ _ _ ↦ trivial) (fun _ _ _ ↦ trivial) hδ hsmall hdist
  exact ⟨u, hjoined, hconj, hnorm⟩

end Unital

/-- **Unitary conjugacy of nearby systems of matrix units in a non-unital C⋆-algebra** via
`Unitization ℂ A` with scalar part `1`. -/
theorem exists_unitization_unitary_conjugate {κ A : Type*} {n : κ → Type*} [Fintype κ]
    [∀ r, Fintype (n r)] [NonUnitalCStarAlgebra A] {e f : ∀ r : κ, n r → n r → A}
    (he : IsMatrixUnitSystem e) (hf : IsMatrixUnitSystem f) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : 6 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ ≤ 1)
    (hdist : ∀ r i j, ‖f r i j - e r i j‖ ≤ δ) :
    ∃ u : unitary (Unitization ℂ A), (u : Unitization ℂ A).fst = 1 ∧ Joined 1 u ∧
      (∀ r i j, (u : Unitization ℂ A) * (e r i j : Unitization ℂ A) *
        star (u : Unitization ℂ A) = (f r i j : Unitization ℂ A)) ∧
      ‖(u : Unitization ℂ A) - 1‖ ≤ 8 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ := by
  let ι := Unitization.inrNonUnitalStarAlgHom ℂ A
  set e' : ∀ r : κ, n r → n r → Unitization ℂ A := fun r i j ↦ e r i j
  set f' : ∀ r : κ, n r → n r → Unitization ℂ A := fun r i j ↦ f r i j
  have he' : IsMatrixUnitSystem e' := he.map ι
  have hf' : IsMatrixUnitSystem f' := hf.map ι
  have hdist' : ∀ r i j, ‖f' r i j - e' r i j‖ ≤ δ := fun r i j ↦ by
    simpa only [e', f', ← Unitization.inr_sub, Unitization.norm_inr] using hdist r i j
  set z : Unitization ℂ A := matrixUnitIntertwiner ℂ e' f'
  have hz_le := he'.norm_matrixUnitIntertwiner_sub_one_le hδ hdist'
  have hz_third : ‖z - 1‖ ≤ 1 / 3 := by linarith
  have hz_fst : z.fst = 1 := by
    let ψ := Unitization.fstHom ℂ A
    have hψ_inr : ∀ a : A, ψ a = 0 := Unitization.fst_inr ℂ
    change ψ z = 1; simp [z, matrixUnitIntertwiner_def, matrixUnitSupport_def, e', f', hψ_inr]
  exact ⟨polarUnitary z hz_third, fst_polarUnitaryElem hz_fst hz_third,
    joined_one_polarUnitary hz_third, fun r i j ↦ conjugate_polarUnitary hz_third
      (he'.intertwine_matrixUnitIntertwiner ℂ hf' r i j)
      (he'.star_matrixUnitIntertwiner_mul ℂ hf' r i j),
    by linarith [norm_polarUnitary_sub_one_le hz_third]⟩

end IsMatrixUnitSystem

end TauCeti

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

This file proves that two nearby finite multi-block systems of matrix units in a C⋆-algebra are
unitarily conjugate by a unitary close to `1` in the identity component `Joined 1 u` (and with
scalar component `1` in `Unitization ℂ A` when `A` is non-unital).

The proof factors into two reusable layers:

1. **Polar unitary of an element near `1`**: for any `z` in a unital C⋆-algebra `A` with
   `‖z - 1‖ ≤ 1 / 3`, `polarUnitaryElem z = z * cfc (fun x : ℝ ↦ (√x)⁻¹) (star z * z)` belongs to
   `unitary A`, lies in every closed unital `ℂ`-⋆-subalgebra containing `z`, satisfies
   `‖polarUnitaryElem z - 1‖ ≤ 4 * ‖z - 1‖` (hence `Joined 1 u`), and converts any pair of
   adjoint-compatible intertwining identities `y * z = z * x` and `star z * y = x * star z` into
   exact unitary conjugacy `u * x * star u = y`.
2. **Application to `TauCeti.matrixUnitIntertwiner`**: for two systems `e, f` of matrix units of
   total size `M = ∑ r, Fintype.card (n r)` with `‖f r i j - e r i j‖ ≤ δ`, the canonical
   intertwiner satisfies `‖matrixUnitIntertwiner ℂ e f - 1‖ ≤ 2 * M * δ`, so whenever
   `6 * M * δ ≤ 1` its polar unitary conjugates every `e r i j` to `f r i j` with
   `‖(u : A) - 1‖ ≤ 8 * M * δ`.

## Main definitions

* `TauCeti.polarUnitaryElem` and `TauCeti.polarUnitary`: polar unitary factor
  `z * (star z * z)⁻¹/²` of an element `z` with `‖z - 1‖ ≤ 1 / 3`.

## Main results

* `TauCeti.IsPartialIsometry.norm_le_one`: every partial isometry in a C⋆-ring has norm `≤ 1`.
* `TauCeti.polarUnitaryElem_mem_unitary`, `TauCeti.norm_polarUnitary_sub_one_le`,
  `TauCeti.conjugate_polarUnitary`: unitary membership, linear norm bound, and intertwining-to-
  conjugacy transfer for `polarUnitary`.
* `TauCeti.IsMatrixUnitSystem.exists_unitary_conjugate_mem`,
  `TauCeti.IsMatrixUnitSystem.exists_unitary_conjugate`, and
  `TauCeti.IsMatrixUnitSystem.exists_unitization_unitary_conjugate`: unitary conjugacy of nearby
  systems of matrix units in unital and non-unital C⋆-algebras.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  Encyclopaedia of Mathematical Sciences **122**, Springer (2006), Proposition II.8.3.23.
* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., MSRI Publications **5**,
  Cambridge University Press (1998), §4.6.
-/

public section

open scoped ContinuousFunctionalCalculus

namespace TauCeti

/-! ### Norm bound for partial isometries in C⋆-rings -/

namespace IsPartialIsometry

/-- Every partial isometry in a C⋆-ring has norm at most `1`. -/
theorem norm_le_one {E : Type*} [NonUnitalNormedRing E] [StarRing E] [CStarRing E] {v : E}
    (hv : IsPartialIsometry v) : ‖v‖ ≤ 1 := by
  have hle : ‖star v * v‖ ≤ 1 := hv.isStarProjection_star_mul_self.norm_le _
  rw [CStarRing.norm_star_mul_self] at hle
  nlinarith [norm_nonneg v]

end IsPartialIsometry

/-! ### Polar unitary of an element near `1` -/

section PolarUnitary

variable {A : Type*} [CStarAlgebra A]

/-- The polar-unitary candidate `z * cfc (fun x : ℝ ↦ (√x)⁻¹) (star z * z)` associated to an
element `z` of a unital C⋆-algebra. -/
noncomputable def polarUnitaryElem (z : A) : A :=
  z * cfc (fun x : ℝ ↦ (√x)⁻¹) (star z * z)

/-- Unfold `TauCeti.polarUnitaryElem`. -/
theorem polarUnitaryElem_def (z : A) :
    polarUnitaryElem z = z * cfc (fun x : ℝ ↦ (√x)⁻¹) (star z * z) :=
  (rfl)

/-- `polarUnitaryElem z` belongs to every closed unital `ℂ`-⋆-subalgebra containing `z`. -/
theorem polarUnitaryElem_mem {S : Type*} [SetLike S A] [SubringClass S A] [SMulMemClass S ℂ A]
    [StarMemClass S A] {s : S} [IsClosed (s : Set A)] {z : A} (hz : z ∈ s) :
    polarUnitaryElem z ∈ s := by
  rw [polarUnitaryElem_def]
  exact mul_mem hz (cfc_mem (𝕜' := ℂ) _ (mul_mem (star_mem hz) hz))

private lemma norm_star_mul_self_sub_one_le (z : A) :
    ‖star z * z - 1‖ ≤ ‖z - 1‖ ^ 2 + 2 * ‖z - 1‖ := by
  have h_id : star z * z - 1 = star (z - 1) * (z - 1) + (star (z - 1) + (z - 1)) := by
    simp only [star_sub, star_one, sub_mul, mul_sub, one_mul, mul_one]
    abel
  rw [h_id]
  have h1 : ‖star (z - 1) * (z - 1)‖ ≤ ‖z - 1‖ ^ 2 := by
    rw [CStarRing.norm_star_mul_self, sq]
  have h2 : ‖star (z - 1) + (z - 1)‖ ≤ 2 * ‖z - 1‖ := by
    have hle := norm_add_le (star (z - 1)) (z - 1)
    rw [norm_star] at hle
    linarith
  linarith [norm_add_le (star (z - 1) * (z - 1)) (star (z - 1) + (z - 1))]

private lemma spectrum_star_mul_self_sub_one_abs_le (z : A) {x : ℝ}
    (hx : x ∈ spectrum ℝ (star z * z)) :
    |x - 1| ≤ ‖star z * z - 1‖ := by
  have hsa : IsSelfAdjoint (star z * z) := IsSelfAdjoint.star_mul_self z
  have hcfc : cfc (fun t : ℝ ↦ t - 1) (star z * z) = star z * z - 1 := by
    rw [cfc_sub (fun t : ℝ ↦ t) (fun _ : ℝ ↦ (1 : ℝ)) (star z * z) continuousOn_id
      continuousOn_const, cfc_id' ℝ (star z * z) hsa, cfc_const_one ℝ (star z * z) hsa]
  simpa [Real.norm_eq_abs, hcfc] using
    norm_apply_le_norm_cfc (fun t : ℝ ↦ t - 1) (star z * z) hx
      (continuousOn_id.sub continuousOn_const) hsa

private lemma pos_of_mem_spectrum_star_mul_self {z : A} (hz : ‖z - 1‖ ≤ 1 / 3) {x : ℝ}
    (hx : x ∈ spectrum ℝ (star z * z)) : 0 < x := by
  have habs : |x - 1| ≤ ‖star z * z - 1‖ := spectrum_star_mul_self_sub_one_abs_le z hx
  have hnorm : ‖star z * z - 1‖ ≤ ‖z - 1‖ ^ 2 + 2 * ‖z - 1‖ := norm_star_mul_self_sub_one_le z
  have hlt : ‖z - 1‖ ^ 2 + 2 * ‖z - 1‖ ≤ 7 / 9 := by
    nlinarith [norm_nonneg (z - 1)]
  linarith [(abs_le.mp habs).1]

private lemma continuousOn_inv_sqrt_star_mul_self {z : A} (hz : ‖z - 1‖ ≤ 1 / 3) :
    ContinuousOn (fun x : ℝ ↦ (√x)⁻¹) (spectrum ℝ (star z * z)) :=
  Real.continuous_sqrt.continuousOn.inv₀ fun _ hx ↦
    (Real.sqrt_pos.mpr (pos_of_mem_spectrum_star_mul_self hz hx)).ne'

/-- When `‖z - 1‖ ≤ 1 / 3`, `polarUnitaryElem z` is a unitary element of `A`. -/
theorem polarUnitaryElem_mem_unitary {z : A} (hz : ‖z - 1‖ ≤ 1 / 3) :
    polarUnitaryElem z ∈ unitary A := by
  set h : A := star z * z
  set f : ℝ → ℝ := fun x ↦ (√x)⁻¹
  set w : A := cfc f h
  set s : A := cfc Real.sqrt h
  have hh_sa : IsSelfAdjoint h := IsSelfAdjoint.star_mul_self z
  have hf_cont : ContinuousOn f (spectrum ℝ h) := continuousOn_inv_sqrt_star_mul_self hz
  have hs_cont : ContinuousOn Real.sqrt (spectrum ℝ h) := Real.continuous_sqrt.continuousOn
  have hw_sa : IsSelfAdjoint w := cfc_predicate f h
  have hws : w * s = 1 := by
    rw [← cfc_mul f Real.sqrt h hf_cont hs_cont, ← cfc_const_one ℝ h hh_sa]
    refine cfc_congr fun x hx ↦ ?_
    exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (pos_of_mem_spectrum_star_mul_self hz hx)).ne'
  have hsw : s * w = 1 := by
    rw [← cfc_mul Real.sqrt f h hs_cont hf_cont, ← cfc_const_one ℝ h hh_sa]
    refine cfc_congr fun x hx ↦ ?_
    exact mul_inv_cancel₀ (Real.sqrt_pos.mpr (pos_of_mem_spectrum_star_mul_self hz hx)).ne'
  have hwhw : w * h * w = 1 := by
    have hh_id : h = cfc (fun x : ℝ ↦ x) h := (cfc_id' ℝ h hh_sa).symm
    conv_lhs => rw [hh_id]
    rw [← cfc_mul f (fun x : ℝ ↦ x) h hf_cont continuousOn_id,
      ← cfc_mul (fun x : ℝ ↦ f x * x) f h (hf_cont.mul continuousOn_id) hf_cont,
      ← cfc_const_one ℝ h hh_sa]
    refine cfc_congr fun x hx ↦ ?_
    have hx_pos : 0 < x := pos_of_mem_spectrum_star_mul_self hz hx
    have hne : √x ≠ 0 := (Real.sqrt_pos.mpr hx_pos).ne'
    dsimp [f]
    calc (√x)⁻¹ * x * (√x)⁻¹
        = (√x)⁻¹ * (√x * √x) * (√x)⁻¹ := by rw [Real.mul_self_sqrt hx_pos.le]
      _ = ((√x)⁻¹ * √x) * (√x * (√x)⁻¹) := by ring
      _ = 1 := by rw [inv_mul_cancel₀ hne, mul_inv_cancel₀ hne, mul_one]
  have hleft : star (polarUnitaryElem z) * polarUnitaryElem z = 1 := by
    rw [polarUnitaryElem_def, star_mul, hw_sa.star_eq]
    calc w * star z * (z * w)
        = w * (star z * z) * w := by simp only [mul_assoc]
      _ = 1 := hwhw
  have hz_unit : IsUnit z := by
    have hlt : ‖1 - z‖ < 1 := by
      rw [norm_sub_rev]
      linarith
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hlt
  have hw_unit : IsUnit w := isUnit_iff_exists.mpr ⟨s, hws, hsw⟩
  have hu_unit : IsUnit (polarUnitaryElem z) := by
    rw [polarUnitaryElem_def]
    exact hz_unit.mul hw_unit
  rw [Unitary.mem_iff]
  refine ⟨hleft, hu_unit.star.mul_right_inj.mp ?_⟩
  rw [← mul_assoc, hleft, one_mul, mul_one]

/-- Bundled unitary `polarUnitary z hz : unitary A` for `z : A` with `‖z - 1‖ ≤ 1 / 3`. -/
noncomputable def polarUnitary (z : A) (hz : ‖z - 1‖ ≤ 1 / 3) : unitary A :=
  ⟨polarUnitaryElem z, polarUnitaryElem_mem_unitary hz⟩

/-- Coercion of `TauCeti.polarUnitary` to the ambient C⋆-algebra. -/
@[simp]
theorem coe_polarUnitary (z : A) (hz : ‖z - 1‖ ≤ 1 / 3) :
    ((polarUnitary z hz : unitary A) : A) = polarUnitaryElem z :=
  (rfl)

/-- Quantitative distance bound `‖(polarUnitary z hz : A) - 1‖ ≤ 4 * ‖z - 1‖`. -/
theorem norm_polarUnitary_sub_one_le {z : A} (hz : ‖z - 1‖ ≤ 1 / 3) :
    ‖(polarUnitary z hz : A) - 1‖ ≤ 4 * ‖z - 1‖ := by
  set h : A := star z * z
  set f : ℝ → ℝ := fun x ↦ (√x)⁻¹
  set w : A := cfc f h
  set s : A := cfc Real.sqrt h
  set u : unitary A := polarUnitary z hz
  have hh_sa : IsSelfAdjoint h := IsSelfAdjoint.star_mul_self z
  have hf_cont : ContinuousOn f (spectrum ℝ h) := continuousOn_inv_sqrt_star_mul_self hz
  have hs_cont : ContinuousOn Real.sqrt (spectrum ℝ h) := Real.continuous_sqrt.continuousOn
  have hws : w * s = 1 := by
    rw [← cfc_mul f Real.sqrt h hf_cont hs_cont, ← cfc_const_one ℝ h hh_sa]
    refine cfc_congr fun x hx ↦ ?_
    exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (pos_of_mem_spectrum_star_mul_self hz hx)).ne'
  have hz_eq : z = (u : A) * s := by
    change z = (z * w) * s
    rw [mul_assoc, hws, mul_one]
  have hu_sub : (u : A) - 1 = (z - 1) - (u : A) * (s - 1) := by
    rw [hz_eq, mul_sub, mul_one]
    abel
  have hs_sub_le : ‖s - 1‖ ≤ ‖h - 1‖ := by
    have hs_eq : s - 1 = cfc (fun x : ℝ ↦ √x - 1) h := by
      rw [cfc_sub Real.sqrt (fun _ : ℝ ↦ (1 : ℝ)) h hs_cont continuousOn_const,
        cfc_const_one ℝ h hh_sa]
    rw [hs_eq]
    refine norm_cfc_le (norm_nonneg _) fun x hx ↦ ?_
    rw [Real.norm_eq_abs]
    have hx_pos : 0 < x := pos_of_mem_spectrum_star_mul_self hz hx
    have hsqrt_pos : 0 < √x := Real.sqrt_pos.mpr hx_pos
    have habs : |x - 1| ≤ ‖h - 1‖ := spectrum_star_mul_self_sub_one_abs_le z hx
    have hprod : |x - 1| = |√x - 1| * (√x + 1) := by
      have hsq : x - 1 = (√x - 1) * (√x + 1) := by
        calc x - 1
            = √x * √x - 1 := by rw [Real.mul_self_sqrt hx_pos.le]
          _ = (√x - 1) * (√x + 1) := by ring
      rw [hsq, abs_mul, abs_of_pos (show 0 < √x + 1 by linarith)]
    nlinarith [abs_nonneg (√x - 1)]
  have hh_le : ‖h - 1‖ ≤ ‖z - 1‖ ^ 2 + 2 * ‖z - 1‖ := norm_star_mul_self_sub_one_le z
  have hnorm_us : ‖(u : A) * (s - 1)‖ = ‖s - 1‖ := CStarRing.norm_coe_unitary_mul u (s - 1)
  have htri : ‖(u : A) - 1‖ ≤ ‖z - 1‖ + ‖s - 1‖ := by
    rw [hu_sub, ← hnorm_us]
    exact norm_sub_le _ _
  nlinarith [norm_nonneg (z - 1)]

/-- `polarUnitary z hz` lies in the connected component of `1` in `unitary A`. -/
theorem joined_one_polarUnitary {z : A} (hz : ‖z - 1‖ ≤ 1 / 3) :
    Joined 1 (polarUnitary z hz) := by
  refine Unitary.joined 1 (polarUnitary z hz) ?_
  calc ‖((polarUnitary z hz : A) - (1 : unitary A))‖
      = ‖(polarUnitary z hz : A) - 1‖ := rfl
    _ ≤ 4 * ‖z - 1‖ := norm_polarUnitary_sub_one_le hz
    _ ≤ 4 * (1 / 3) := by linarith
    _ < 2 := by norm_num

/-- Adjoint-compatible intertwining relations `y * z = z * x` and `star z * y = x * star z` pass to
`polarUnitaryElem z`. -/
theorem intertwine_polarUnitaryElem {z x y : A} (h1 : y * z = z * x)
    (h2 : star z * y = x * star z) :
    y * polarUnitaryElem z = polarUnitaryElem z * x := by
  have hcomm_h : Commute (star z * z) x := by
    rw [Commute, SemiconjBy]
    calc star z * z * x
        = star z * (z * x) := by simp only [mul_assoc]
      _ = star z * (y * z) := by rw [← h1]
      _ = (star z * y) * z := by simp only [mul_assoc]
      _ = (x * star z) * z := by rw [h2]
      _ = x * (star z * z) := by simp only [mul_assoc]
  have hcomm_w : Commute (cfc (fun t : ℝ ↦ (√t)⁻¹) (star z * z)) x :=
    hcomm_h.cfc_real (fun t : ℝ ↦ (√t)⁻¹)
  rw [polarUnitaryElem_def]
  calc y * (z * cfc (fun t : ℝ ↦ (√t)⁻¹) (star z * z))
      = (y * z) * cfc (fun t : ℝ ↦ (√t)⁻¹) (star z * z) := by simp only [mul_assoc]
    _ = (z * x) * cfc (fun t : ℝ ↦ (√t)⁻¹) (star z * z) := by rw [h1]
    _ = z * (x * cfc (fun t : ℝ ↦ (√t)⁻¹) (star z * z)) := by simp only [mul_assoc]
    _ = z * (cfc (fun t : ℝ ↦ (√t)⁻¹) (star z * z) * x) := by rw [hcomm_w.eq]
    _ = z * cfc (fun t : ℝ ↦ (√t)⁻¹) (star z * z) * x := by simp only [mul_assoc]

/-- Adjoint-compatible intertwining relations `y * z = z * x` and `star z * y = x * star z` become
exact unitary conjugation `(polarUnitary z hz : A) * x * star (polarUnitary z hz : A) = y`. -/
theorem conjugate_polarUnitary {z x y : A} (hz : ‖z - 1‖ ≤ 1 / 3)
    (h1 : y * z = z * x) (h2 : star z * y = x * star z) :
    (polarUnitary z hz : A) * x * star (polarUnitary z hz : A) = y := by
  rw [coe_polarUnitary, ← intertwine_polarUnitaryElem h1 h2, mul_assoc,
    (polarUnitaryElem_mem_unitary hz).2, mul_one]

end PolarUnitary

/-! ### Scalar component in `Unitization ℂ A` -/

/-- For an element `z : Unitization ℂ A` with `z.fst = 1` and `‖z - 1‖ ≤ 1 / 3`, its polar unitary
also has scalar component `1`. -/
theorem fst_polarUnitaryElem {A : Type*} [NonUnitalCStarAlgebra A] {z : Unitization ℂ A}
    (hz_fst : z.fst = 1) (hz : ‖z - 1‖ ≤ 1 / 3) :
    (polarUnitaryElem z).fst = 1 := by
  set h : Unitization ℂ A := star z * z
  set f : ℝ → ℝ := fun x ↦ (√x)⁻¹
  let φ : Unitization ℂ A →⋆ₐ[ℂ] ℂ :=
    { Unitization.fstHom ℂ A with map_star' := Unitization.fst_star }
  have hh_sa : IsSelfAdjoint h := IsSelfAdjoint.star_mul_self z
  have hf_cont : ContinuousOn f (spectrum ℝ h) := continuousOn_inv_sqrt_star_mul_self hz
  have hφh : φ h = 1 := by
    change (star z * z).fst = 1
    simp [hz_fst]
  have hφ_cfc : (cfc f h).fst = 1 := by
    change φ (cfc f h) = 1
    rw [φ.map_cfc f h hf_cont Unitization.continuous_fst hh_sa (hφh.symm ▸ IsSelfAdjoint.one ℂ),
      hφh]
    conv_rhs => rw [← cfc_const_one ℝ (1 : ℂ) (IsSelfAdjoint.one ℂ)]
    refine cfc_congr fun x hx ↦ ?_
    have hx1 : x = 1 := by
      by_contra hne
      apply hx
      refine IsUnit.mk0 _ ?_
      rw [Algebra.algebraMap_eq_smul_one, Complex.real_smul]
      norm_cast
      rw [mul_one]
      exact sub_ne_zero.mpr hne
    subst hx1
    simp [f]
  rw [polarUnitaryElem_def, Unitization.fst_mul, hz_fst, hφ_cfc, mul_one]

/-! ### Unitary conjugacy of nearby systems of matrix units -/

namespace IsMatrixUnitSystem

section Unital

variable {κ A : Type*} {n : κ → Type*} [Fintype κ] [∀ r, Fintype (n r)] [CStarAlgebra A]
  {e f : ∀ r : κ, n r → n r → A}

/-- `matrixUnitIntertwiner ℂ e f` belongs to any unital `ℂ`-subring containing all `e r i j` and
`f r i j`. -/
theorem matrixUnitIntertwiner_mem {S : Type*} [SetLike S A] [SubringClass S A]
    [SMulMemClass S ℂ A] {s : S} (he_mem : ∀ r i j, e r i j ∈ s)
    (hf_mem : ∀ r i j, f r i j ∈ s) :
    matrixUnitIntertwiner ℂ e f ∈ s := by
  have hsupp_e : matrixUnitSupport e ∈ s := by
    rw [matrixUnitSupport_def]
    exact sum_mem fun r _ ↦ sum_mem fun i _ ↦ he_mem r i i
  have hsupp_f : matrixUnitSupport f ∈ s := by
    rw [matrixUnitSupport_def]
    exact sum_mem fun r _ ↦ sum_mem fun i _ ↦ hf_mem r i i
  rw [matrixUnitIntertwiner_def]
  refine add_mem (mul_mem (sub_mem (one_mem s) hsupp_f) (sub_mem (one_mem s) hsupp_e)) ?_
  refine sum_mem fun r _ ↦ SMulMemClass.smul_mem _ ?_
  exact sum_mem fun a _ ↦ sum_mem fun b _ ↦ mul_mem (hf_mem r a b) (he_mem r b a)

/-- Norm estimate `‖matrixUnitIntertwiner ℂ e f - 1‖ ≤ 2 * (∑ r, card (n r)) * δ` when `e` is a
system of matrix units and `f` is any family whose entries are within `δ` of `e`. -/
theorem norm_matrixUnitIntertwiner_sub_one_le (he : IsMatrixUnitSystem e)
    {δ : ℝ} (hδ : 0 ≤ δ) (hdist : ∀ r i j, ‖f r i j - e r i j‖ ≤ δ) :
    ‖matrixUnitIntertwiner ℂ e f - 1‖ ≤ 2 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ := by
  rw [← he.matrixUnitIntertwiner_self (𝕜 := ℂ), matrixUnitIntertwiner_def,
    matrixUnitIntertwiner_def]
  have hsplit :
      ((1 - matrixUnitSupport f) * (1 - matrixUnitSupport e) +
          ∑ r : κ, (Fintype.card (n r) : ℂ)⁻¹ • ∑ a : n r, ∑ b : n r, f r a b * e r b a) -
        ((1 - matrixUnitSupport e) * (1 - matrixUnitSupport e) +
          ∑ r : κ, (Fintype.card (n r) : ℂ)⁻¹ • ∑ a : n r, ∑ b : n r, e r a b * e r b a) =
      (matrixUnitSupport e - matrixUnitSupport f) * (1 - matrixUnitSupport e) +
        ∑ r : κ, (Fintype.card (n r) : ℂ)⁻¹ •
          ∑ a : n r, ∑ b : n r, (f r a b - e r a b) * e r b a := by
    have h1 :
        (1 - matrixUnitSupport f) * (1 - matrixUnitSupport e) -
          (1 - matrixUnitSupport e) * (1 - matrixUnitSupport e) =
        (matrixUnitSupport e - matrixUnitSupport f) * (1 - matrixUnitSupport e) := by
      rw [← sub_mul]
      exact congrArg (· * (1 - matrixUnitSupport e)) (by abel)
    have h2 :
        (∑ r : κ, (Fintype.card (n r) : ℂ)⁻¹ • ∑ a : n r, ∑ b : n r, f r a b * e r b a) -
          (∑ r : κ, (Fintype.card (n r) : ℂ)⁻¹ • ∑ a : n r, ∑ b : n r, e r a b * e r b a) =
        ∑ r : κ, (Fintype.card (n r) : ℂ)⁻¹ •
          ∑ a : n r, ∑ b : n r, (f r a b - e r a b) * e r b a := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      rw [← smul_sub, ← Finset.sum_sub_distrib]
      refine congrArg ((Fintype.card (n r) : ℂ)⁻¹ • ·) (Finset.sum_congr rfl fun a _ ↦ ?_)
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun b _ ↦ (sub_mul _ _ _).symm
    calc _
        = ((1 - matrixUnitSupport f) * (1 - matrixUnitSupport e) -
            (1 - matrixUnitSupport e) * (1 - matrixUnitSupport e)) +
          ((∑ r : κ, (Fintype.card (n r) : ℂ)⁻¹ • ∑ a : n r, ∑ b : n r, f r a b * e r b a) -
            (∑ r : κ, (Fintype.card (n r) : ℂ)⁻¹ • ∑ a : n r, ∑ b : n r, e r a b * e r b a)) := by
              abel
      _ = _ := by rw [h1, h2]
  rw [hsplit]
  have hpart1 :
      ‖(matrixUnitSupport e - matrixUnitSupport f) * (1 - matrixUnitSupport e)‖ ≤
        (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ := by
    have hproj_norm : ‖1 - matrixUnitSupport e‖ ≤ 1 :=
      (he.isStarProjection_support.one_sub).norm_le _
    have hsupp_diff :
        matrixUnitSupport e - matrixUnitSupport f =
          ∑ r : κ, ∑ i : n r, (e r i i - f r i i) := by
      simp only [matrixUnitSupport_def, ← Finset.sum_sub_distrib]
    calc ‖(matrixUnitSupport e - matrixUnitSupport f) * (1 - matrixUnitSupport e)‖
        ≤ ‖matrixUnitSupport e - matrixUnitSupport f‖ * ‖1 - matrixUnitSupport e‖ :=
          norm_mul_le _ _
      _ ≤ ‖matrixUnitSupport e - matrixUnitSupport f‖ * 1 := by gcongr
      _ = ‖∑ r : κ, ∑ i : n r, (e r i i - f r i i)‖ := by rw [mul_one, hsupp_diff]
      _ ≤ ∑ r : κ, ‖∑ i : n r, (e r i i - f r i i)‖ := norm_sum_le _ _
      _ ≤ ∑ r : κ, ∑ i : n r, ‖e r i i - f r i i‖ := by
          gcongr with r
          exact norm_sum_le _ _
      _ ≤ ∑ r : κ, ∑ _i : n r, δ := by
          gcongr with r _ i
          rw [norm_sub_rev]
          exact hdist r i i
      _ = (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ := by
          simp [Finset.sum_mul]
  have hpart2 :
      ‖∑ r : κ, (Fintype.card (n r) : ℂ)⁻¹ •
          ∑ a : n r, ∑ b : n r, (f r a b - e r a b) * e r b a‖ ≤
        (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ := by
    calc ‖∑ r : κ, (Fintype.card (n r) : ℂ)⁻¹ •
            ∑ a : n r, ∑ b : n r, (f r a b - e r a b) * e r b a‖
        ≤ ∑ r : κ, ‖(Fintype.card (n r) : ℂ)⁻¹ •
            ∑ a : n r, ∑ b : n r, (f r a b - e r a b) * e r b a‖ := norm_sum_le _ _
      _ ≤ ∑ r : κ, (Fintype.card (n r) : ℝ) * δ := by
          gcongr with r
          by_cases hcard : Fintype.card (n r) = 0
          · simp [hcard]
          · have hpos : (0 : ℝ) < Fintype.card (n r) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcard)
            rw [norm_smul, norm_inv, Complex.norm_natCast]
            have hinner :
                ‖∑ a : n r, ∑ b : n r, (f r a b - e r a b) * e r b a‖ ≤
                  (Fintype.card (n r) : ℝ) * ((Fintype.card (n r) : ℝ) * δ) := by
              calc ‖∑ a : n r, ∑ b : n r, (f r a b - e r a b) * e r b a‖
                  ≤ ∑ a : n r, ‖∑ b : n r, (f r a b - e r a b) * e r b a‖ := norm_sum_le _ _
                _ ≤ ∑ a : n r, ∑ b : n r, ‖(f r a b - e r a b) * e r b a‖ := by
                    gcongr with a
                    exact norm_sum_le _ _
                _ ≤ ∑ _a : n r, ∑ _b : n r, δ := by
                    gcongr with a _ b
                    calc ‖(f r a b - e r a b) * e r b a‖
                        ≤ ‖f r a b - e r a b‖ * ‖e r b a‖ := norm_mul_le _ _
                      _ ≤ δ * 1 := by
                          gcongr
                          · exact hdist r a b
                          · exact (he.isPartialIsometry r b a).norm_le_one
                      _ = δ := mul_one δ
                _ = (Fintype.card (n r) : ℝ) * ((Fintype.card (n r) : ℝ) * δ) := by
                    simp
            calc (Fintype.card (n r) : ℝ)⁻¹ *
                  ‖∑ a : n r, ∑ b : n r, (f r a b - e r a b) * e r b a‖
                ≤ (Fintype.card (n r) : ℝ)⁻¹ *
                    ((Fintype.card (n r) : ℝ) * ((Fintype.card (n r) : ℝ) * δ)) := by gcongr
              _ = (Fintype.card (n r) : ℝ) * δ := inv_mul_cancel_left₀ hpos.ne' _
      _ = (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ := (Finset.sum_mul _ _ _).symm
  linarith [norm_add_le
    ((matrixUnitSupport e - matrixUnitSupport f) * (1 - matrixUnitSupport e))
    (∑ r : κ, (Fintype.card (n r) : ℂ)⁻¹ • ∑ a : n r, ∑ b : n r, (f r a b - e r a b) * e r b a)]

/-- **Unitary conjugacy of nearby systems of matrix units** (with subalgebra preservation): if `e`
and `f` are systems of matrix units in a closed unital `ℂ`-⋆-subalgebra `s` of `A` satisfying
`6 * (∑ r, card (n r)) * δ ≤ 1` and `∀ r i j, ‖f r i j - e r i j‖ ≤ δ`, there exists `u : unitary A`
with `(u : A) ∈ s`, `Joined 1 u`, `(u : A) * e r i j * star (u : A) = f r i j` for all `r, i, j`,
and `‖(u : A) - 1‖ ≤ 8 * (∑ r, card (n r)) * δ`. -/
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
  have hz_le_bound : ‖z - 1‖ ≤ 2 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ :=
    he.norm_matrixUnitIntertwiner_sub_one_le hδ hdist
  have hz_third : ‖z - 1‖ ≤ 1 / 3 := by linarith
  refine ⟨polarUnitary z hz_third, polarUnitaryElem_mem (matrixUnitIntertwiner_mem he_mem hf_mem),
    joined_one_polarUnitary hz_third, fun r i j ↦ ?_, ?_⟩
  · exact conjugate_polarUnitary hz_third
      (he.intertwine_matrixUnitIntertwiner ℂ hf r i j)
      (he.star_matrixUnitIntertwiner_mul ℂ hf r i j)
  · linarith [norm_polarUnitary_sub_one_le hz_third]

/-- **Unitary conjugacy of nearby systems of matrix units** in a unital C⋆-algebra. -/
theorem exists_unitary_conjugate (he : IsMatrixUnitSystem e) (hf : IsMatrixUnitSystem f)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : 6 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ ≤ 1)
    (hdist : ∀ r i j, ‖f r i j - e r i j‖ ≤ δ) :
    ∃ u : unitary A, Joined 1 u ∧
      (∀ r i j, (u : A) * e r i j * star (u : A) = f r i j) ∧
      ‖(u : A) - 1‖ ≤ 8 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ := by
  have : IsClosed ((⊤ : StarSubalgebra ℂ A) : Set A) := isClosed_univ
  obtain ⟨u, -, hjoined, hconj, hnorm⟩ :=
    he.exists_unitary_conjugate_mem (s := (⊤ : StarSubalgebra ℂ A)) hf
      (fun _ _ _ ↦ trivial) (fun _ _ _ ↦ trivial) hδ hsmall hdist
  exact ⟨u, hjoined, hconj, hnorm⟩

end Unital

/-! ### Non-unital C⋆-algebras via `Unitization ℂ A` -/

/-- **Unitary conjugacy of nearby systems of matrix units in a non-unital C⋆-algebra**: for two
nearby systems `e, f` in `A`, there exists a unitary `u : unitary (Unitization ℂ A)` with scalar
part `(u : Unitization ℂ A).fst = 1`, `Joined 1 u`, conjugating `(e r i j : Unitization ℂ A)` to
`(f r i j : Unitization ℂ A)`, and satisfying
`‖(u : Unitization ℂ A) - 1‖ ≤ 8 * (∑ r, card (n r)) * δ`. -/
theorem exists_unitization_unitary_conjugate {κ A : Type*} {n : κ → Type*} [Fintype κ]
    [∀ r, Fintype (n r)] [NonUnitalCStarAlgebra A] {e f : ∀ r : κ, n r → n r → A}
    (he : IsMatrixUnitSystem e) (hf : IsMatrixUnitSystem f) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : 6 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ ≤ 1)
    (hdist : ∀ r i j, ‖f r i j - e r i j‖ ≤ δ) :
    ∃ u : unitary (Unitization ℂ A),
      (u : Unitization ℂ A).fst = 1 ∧
      Joined 1 u ∧
      (∀ r i j, (u : Unitization ℂ A) * (e r i j : Unitization ℂ A) *
        star (u : Unitization ℂ A) = (f r i j : Unitization ℂ A)) ∧
      ‖(u : Unitization ℂ A) - 1‖ ≤ 8 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ := by
  let ι := Unitization.inrNonUnitalStarAlgHom ℂ A
  set e' : ∀ r : κ, n r → n r → Unitization ℂ A := fun r i j ↦ e r i j
  set f' : ∀ r : κ, n r → n r → Unitization ℂ A := fun r i j ↦ f r i j
  have he' : IsMatrixUnitSystem e' := he.map ι
  have hf' : IsMatrixUnitSystem f' := hf.map ι
  have hdist' : ∀ r i j, ‖f' r i j - e' r i j‖ ≤ δ := fun r i j ↦ by
    dsimp [e', f']
    rw [← Unitization.inr_sub, Unitization.norm_inr]
    exact hdist r i j
  set z : Unitization ℂ A := matrixUnitIntertwiner ℂ e' f'
  have hz_le_bound : ‖z - 1‖ ≤ 2 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ :=
    he'.norm_matrixUnitIntertwiner_sub_one_le hδ hdist'
  have hz_third : ‖z - 1‖ ≤ 1 / 3 := by linarith
  have hz_fst : z.fst = 1 := by
    let ψ := Unitization.fstHom ℂ A
    have hψ_inr : ∀ a : A, ψ a = 0 := Unitization.fst_inr ℂ
    change ψ z = 1
    simp only [z, matrixUnitIntertwiner_def, matrixUnitSupport_def, e', f',
      map_add, map_mul, map_sub, map_one, map_sum, map_smul, hψ_inr, zero_mul,
      Finset.sum_const_zero, smul_zero, sub_zero, mul_one, add_zero]
  refine ⟨polarUnitary z hz_third, fst_polarUnitaryElem hz_fst hz_third,
    joined_one_polarUnitary hz_third, fun r i j ↦ ?_, ?_⟩
  · exact conjugate_polarUnitary hz_third
      (he'.intertwine_matrixUnitIntertwiner ℂ hf' r i j)
      (he'.star_matrixUnitIntertwiner_mul ℂ hf' r i j)
  · linarith [norm_polarUnitary_sub_one_le hz_third]

end IsMatrixUnitSystem

end TauCeti

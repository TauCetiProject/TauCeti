/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import TauCeti.Geometry.Symplectic.Manifold.Torus.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Subtype.Cutoff
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import TauCeti.Geometry.Manifold.Instances.AddCircle.Angle
import TauCeti.Geometry.Symplectic.Manifold.LiouvilleMeasure
import TauCeti.Geometry.Symplectic.Manifold.Moser
import TauCeti.Topology.Circle.AddCircle

/-!
# Moser's theorem on the torus: an exact path and a path of changing area

Moser's stability theorem (`TauCeti.SmoothTwoForm.exists_isotopy_mpullback_eq`) turns a path of
symplectic forms `ω_t` on a compact manifold whose velocity is exact, `∂_t ω_t = dα_t`, into an
isotopy `ψ_t` with `ψ_t^* ω_t = ω_0`. On tori, this file gives a path of symplectic forms violating
the exactness hypothesis which admits no such isotopy, and a path satisfying it, with its isotopy.

**A path of changing area.** On the torus `T = ∀ i : ι ⊕ ι, AddCircle (p i)` with its standard
symplectic form `ω_T` (`TauCeti.torusSymplecticForm`), the forms `r • ω_T` and `ω_T` are not
symplectomorphic unless `|r| = 1`: a differentiable homeomorphism pulling `r • ω_T` back to `ω_T`
would carry the Liouville measure of `ω_T` to that of `r • ω_T`, which has `|r|ⁿ` times its total
mass (`Homeomorph.abs_pow_eq_one_of_mpullback_smul_eq`). So the path `(1 + t) ω_T`, whose classes
`(1 + t) [ω_T]` are not constant, admits no isotopy with `ψ_t^* ω_t = ω_0`
(`TauCeti.not_exists_isotopy_mpullback_one_add_smul_torusSymplecticForm`). Its velocity is `ω_T`,
which is not exact (`TauCeti.torusSymplecticForm_notMem_exactForms`), so it violates the
hypothesis of Moser's theorem.

**An exact path.** On the two-torus `T² = AddCircle (2π) × AddCircle (2π)`, written as
`∀ _ : Unit ⊕ Unit, AddCircle (2 * π)`, with angles `θ = x (inl ())` and `φ = x (inr ())` and
`ω_T = dθ ∧ dφ`, the one-form `sin θ dφ` (`TauCeti.twoTorusSinForm`) has exterior derivative
`d(sin θ dφ) = cos θ dθ ∧ dφ` (`TauCeti.mextDerivₗ_twoTorusSinForm`), by the Leibniz rule and the
closedness of `dφ`. Hence

`ω_t = dθ ∧ dφ + (t / 2) d(sin θ dφ) = (1 + (t / 2) cos θ) dθ ∧ dφ`

(`TauCeti.torusSymplecticForm_add_smul_mextDerivₗ_twoTorusSinForm`), which is symplectic for
`|t| < 2` (`TauCeti.isSymplectic_torusSymplecticForm_add_smul_mextDerivₗ_twoTorusSinForm`), in
particular for `t ∈ [0, 1]`. Its velocity `(1 / 2) d(sin θ dφ)` is exact, and Moser's isotopy
exists: there are diffeomorphisms `ψ_t`, jointly smooth in `(t, x)`, with `ψ_0 = id` and
`ψ_t^* ω_t = ω_0` for `t ∈ [0, 1]`
(`TauCeti.exists_isotopy_mpullback_torusSymplecticForm_add_smul_mextDerivₗ_twoTorusSinForm`).
Moser's theorem is stated for families over the whole line, so the proof reparametrizes the path
by a smooth function equal to `t` on `[0, 1]` and of absolute value less than `2`, keeping every
slice symplectic.

The two paths have the same initial form, and both stay symplectic for `t ∈ [0, 1]`. They differ
in their de Rham classes: the classes of the second path are constant, those of the first are not.

## Main definitions

* `TauCeti.twoTorusSin`, `TauCeti.twoTorusCos`: the functions `sin θ` and `cos θ` on the
  two-torus, the angle functions `TauCeti.torusAngleSin` and `TauCeti.torusAngleCos` of `θ`.
* `TauCeti.twoTorusSinForm`: the one-form `sin θ dφ` on the two-torus.

## Main results

* `TauCeti.mpullback_smul_torusSymplecticForm_ne`: no differentiable homeomorphism of the torus
  pulls `r • ω_T` back to `ω_T` when `|r| ≠ 1`.
* `TauCeti.not_exists_isotopy_mpullback_one_add_smul_torusSymplecticForm`: the path `(1 + t) ω_T`
  has no Moser isotopy.
* `TauCeti.mextDerivₗ_twoTorusSinForm`: `d(sin θ dφ) = cos θ dθ ∧ dφ`.
* `TauCeti.torusSymplecticForm_add_smul_mextDerivₗ_twoTorusSinForm`:
  `dθ ∧ dφ + s d(sin θ dφ) = (1 + s cos θ) dθ ∧ dφ`.
* `TauCeti.isSymplectic_torusSymplecticForm_add_smul_mextDerivₗ_twoTorusSinForm`: these forms are
  symplectic for `|s| < 1`.
* `TauCeti.exists_isotopy_mpullback_torusSymplecticForm_add_smul_mextDerivₗ_twoTorusSinForm`: the
  path `dθ ∧ dφ + (t / 2) d(sin θ dφ)`, `t ∈ [0, 1]`, has a Moser isotopy.

## References

* J. Moser, *On the volume elements on a manifold*, Transactions of the American Mathematical
  Society 120 (1965), 286–294.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2 (Moser isotopy and Moser stability).
-/

public section

noncomputable section

open Set Function MeasureTheory
open scoped Manifold ContDiff Real

namespace TauCeti

/-! ### Rescaling the standard symplectic form of a torus -/

section Rescaling

variable {ι : Type*} [Fintype ι] (p : ι ⊕ ι → ℝ) [∀ i, Fact (0 < p i)]

/-- **Rescaling changes the symplectic volume of a torus.** For nonempty `ι` and `|r| ≠ 1`, no
differentiable homeomorphism of the torus `∀ i : ι ⊕ ι, AddCircle (p i)` pulls `r • ω_T` back to the
standard symplectic form `ω_T`, since the Liouville volume of `r • ω_T` is `|r|^|ι|` times that of
`ω_T`. -/
theorem mpullback_smul_torusSymplecticForm_ne [Nonempty ι] {r : ℝ} (hr : |r| ≠ 1)
    (Φ : (∀ i, AddCircle (p i)) ≃ₜ (∀ i, AddCircle (p i)))
    (hΦ : MDifferentiable (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))
      (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) Φ) :
    TauCeti.mpullback (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))
        (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) Φ (r • torusSymplecticForm p).val ≠
      (torusSymplecticForm p).val := fun h ↦ by
  -- The torus has dimension `2 |ι|`.
  have : Fact (Module.finrank ℝ (ι ⊕ ι → ℝ) = 2 * Fintype.card ι) :=
    ⟨by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, two_mul]⟩
  exact hr ((pow_eq_one_iff_of_nonneg (abs_nonneg r) (Fintype.card_ne_zero (α := ι))).1
    (Φ.abs_pow_eq_one_of_mpullback_smul_eq hΦ
      (isSymplectic_torusSymplecticForm p).isNondegenerate h))

/-- **The path `(1 + t) ω_T` has no Moser isotopy.** For nonempty `ι`, there is no family of
diffeomorphisms `ψ_t` of the torus with `ψ_t^* ((1 + t) ω_T) = ω_T` for `t ∈ [0, 1]`. The velocity
`ω_T` of this path is not exact (`TauCeti.torusSymplecticForm_notMem_exactForms`), so Moser's
theorem does not apply to it. -/
theorem not_exists_isotopy_mpullback_one_add_smul_torusSymplecticForm [Nonempty ι] :
    ¬∃ ψ : ℝ → (∀ i, AddCircle (p i)) ≃ₘ⟮ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ),
        ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)⟯ (∀ i, AddCircle (p i)),
      ∀ t ∈ Icc (0 : ℝ) 1, SmoothForm.mpullback (ψ t) (ψ t).contMDiff
        ((1 + t) • torusSymplecticForm p) = torusSymplecticForm p := by
  rintro ⟨ψ, hψ⟩
  have h := congrArg Subtype.val (hψ 1 ⟨zero_le_one, le_rfl⟩)
  rw [SmoothForm.coe_mpullback] at h
  exact mpullback_smul_torusSymplecticForm_ne p (by norm_num) (ψ 1).toHomeomorph
    ((ψ 1).mdifferentiable (by simp)) h

end Rescaling

/-! ### The exact path `(1 + (t / 2) cos θ) dθ ∧ dφ` on the two-torus -/

section TwoTorus

/-- The period `2π` of the angles of the two-torus is positive. -/
local instance twoTorusTwoPiPos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- The function `sin θ` on the two-torus `∀ _ : Unit ⊕ Unit, AddCircle (2 * π)`, where
`θ = x (inl ())` is the first angle (`TauCeti.torusAngleSin`). -/
def twoTorusSin :
    C^∞⟮ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ), ∀ _ : Unit ⊕ Unit, AddCircle (2 * π); ℝ⟯ :=
  torusAngleSin (Unit ⊕ Unit) (.inl ())

/-- The function `cos θ` on the two-torus `∀ _ : Unit ⊕ Unit, AddCircle (2 * π)`, where
`θ = x (inl ())` is the first angle (`TauCeti.torusAngleCos`). -/
def twoTorusCos :
    C^∞⟮ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ), ∀ _ : Unit ⊕ Unit, AddCircle (2 * π); ℝ⟯ :=
  torusAngleCos (Unit ⊕ Unit) (.inl ())

/-- `sin θ` at a point whose first angle is the class of `t` is `sin t`. -/
theorem twoTorusSin_apply_of_eq {x : ∀ _ : Unit ⊕ Unit, AddCircle (2 * π)} {t : ℝ}
    (ht : x (.inl ()) = t) : twoTorusSin x = Real.sin t := by
  rw [twoTorusSin, torusAngleSin_apply, ht, AddCircle.im_toCircle_coe,
    div_self Real.two_pi_pos.ne', one_mul]

/-- `cos θ` at a point whose first angle is the class of `t` is `cos t`. -/
theorem twoTorusCos_apply_of_eq {x : ∀ _ : Unit ⊕ Unit, AddCircle (2 * π)} {t : ℝ}
    (ht : x (.inl ()) = t) : twoTorusCos x = Real.cos t := by
  rw [twoTorusCos, torusAngleCos_apply, ht, AddCircle.re_toCircle_coe,
    div_self Real.two_pi_pos.ne', one_mul]

/-- `sin θ` is `sin` lifted to the circle of the first angle `θ = x (inl ())`. -/
@[simp]
theorem twoTorusSin_apply (x : ∀ _ : Unit ⊕ Unit, AddCircle (2 * π)) :
    twoTorusSin x = Real.sin_periodic.lift (x (.inl ())) := by
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (x (.inl ()))
  rw [twoTorusSin_apply_of_eq ht.symm, ← ht, Real.sin_periodic.lift_coe]

/-- `cos θ` is `cos` lifted to the circle of the first angle `θ = x (inl ())`. -/
@[simp]
theorem twoTorusCos_apply (x : ∀ _ : Unit ⊕ Unit, AddCircle (2 * π)) :
    twoTorusCos x = Real.cos_periodic.lift (x (.inl ())) := by
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (x (.inl ()))
  rw [twoTorusCos_apply_of_eq ht.symm, ← ht, Real.cos_periodic.lift_coe]

/-- The values of `cos θ` lie in `[-1, 1]`. -/
theorem abs_twoTorusCos_le_one (x : ∀ _ : Unit ⊕ Unit, AddCircle (2 * π)) :
    |twoTorusCos x| ≤ 1 :=
  abs_torusAngleCos_le_one _ x

/-- The differential of `sin θ` is `cos θ dθ`: on a tangent vector `v` of the two-torus it is
`cos θ * v (inl ())`. -/
@[simp]
theorem mfderiv_twoTorusSin (x : ∀ _ : Unit ⊕ Unit, AddCircle (2 * π))
    (v : TangentSpace (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) x) :
    mfderiv (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) 𝓘(ℝ, ℝ) twoTorusSin x v =
      twoTorusCos x * v (.inl ()) := by
  unfold twoTorusSin twoTorusCos
  -- `mvfderiv` into `ℝ` is `mfderiv` read in the model.
  exact mvfderiv_torusAngleSin (ι := Unit ⊕ Unit) (.inl ()) x v

/-- The one-form `sin θ dφ` on the two-torus `∀ _ : Unit ⊕ Unit, AddCircle (2 * π)`, where
`θ = x (inl ())` and `φ = x (inr ())` are the two angles. -/
def twoTorusSinForm :
    SmoothForm (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ))
      (∀ _ : Unit ⊕ Unit, AddCircle (2 * π)) ℝ 1 :=
  SmoothForm.funSMulₗ twoTorusSin (torusTimeForm (fun _ ↦ 2 * π) (.inr ()))

/-- The one-form `sin θ dφ` is `sin θ` times the coordinate time form `dφ`. -/
theorem twoTorusSinForm_def :
    twoTorusSinForm =
      SmoothForm.funSMulₗ twoTorusSin (torusTimeForm (fun _ ↦ 2 * π) (.inr ())) :=
  (rfl)

/-- **`d(sin θ dφ) = cos θ dθ ∧ dφ`** on the two-torus. -/
theorem mextDerivₗ_twoTorusSinForm :
    mextDerivₗ (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) 1 twoTorusSinForm =
      SmoothForm.funSMulₗ twoTorusCos (torusSymplecticForm fun _ ↦ 2 * π) := by
  apply Subtype.ext
  funext x
  ext v
  have hclosed := isClosed_torusTimeForm (fun _ : Unit ⊕ Unit ↦ 2 * π) (.inr ())
  rw [SmoothForm.isClosed_iff_mextDerivₗ_eq_zero] at hclosed
  rw [twoTorusSinForm_def, SmoothForm.mextDerivₗ_funSMulₗ_apply, hclosed]
  -- The degree `0 + 1 + 1` of `d(sin θ) ∧ dφ` is `2`; read it as a wedge of two one-forms.
  have hv : v ∘ Fin.cast (show 0 + 1 + 1 = 1 + 1 by omega) = ![v 0, v 1] :=
    funext fun i ↦ by fin_cases i <;> rfl
  rw [hv, RoughForm.wedge_apply_one_one (mextDeriv (RoughForm.ofFunction _ twoTorusSin))
    (torusTimeForm (fun _ : Unit ⊕ Unit ↦ 2 * π) (.inr ())).val x (v 0) (v 1)]
  simp only [mextDeriv_ofFunction_apply, mfderiv_twoTorusSin]
  simp only [Fin.isValue, torusTimeForm_apply, Matrix.cons_val_fin_one, Nat.reduceAdd,
    ZeroMemClass.coe_zero, Pi.zero_apply, ContinuousAlternatingMap.coe_zero, mul_zero, add_zero,
    SmoothForm.coe_funSMulₗ, ContinuousAlternatingMap.coe_smul, Pi.smul_apply,
    torusSymplecticForm_apply, Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_sub_distrib,
    Finset.sum_singleton, smul_eq_mul]
  ring

/-- **`dθ ∧ dφ + s d(sin θ dφ) = (1 + s cos θ) dθ ∧ dφ`** on the two-torus. -/
theorem torusSymplecticForm_add_smul_mextDerivₗ_twoTorusSinForm (s : ℝ) :
    torusSymplecticForm (fun _ ↦ 2 * π) +
        s • mextDerivₗ (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) 1 twoTorusSinForm =
      SmoothForm.funSMulₗ (1 + s • twoTorusCos) (torusSymplecticForm fun _ ↦ 2 * π) := by
  rw [mextDerivₗ_twoTorusSinForm]
  apply Subtype.ext
  funext x
  simp [add_smul, smul_smul]

/-- **The forms `dθ ∧ dφ + s d(sin θ dφ) = (1 + s cos θ) dθ ∧ dφ` are symplectic for `|s| < 1`.**
In particular `dθ ∧ dφ + (t / 2) d(sin θ dφ)` is symplectic for `t ∈ [0, 1]`. -/
theorem isSymplectic_torusSymplecticForm_add_smul_mextDerivₗ_twoTorusSinForm {s : ℝ}
    (hs : |s| < 1) :
    SmoothTwoForm.IsSymplectic (torusSymplecticForm (fun _ ↦ 2 * π) +
      s • mextDerivₗ (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) 1 twoTorusSinForm) := by
  have hω := isSymplectic_torusSymplecticForm (fun _ : Unit ⊕ Unit ↦ 2 * π)
  refine ⟨hω.isClosed.add ((SmoothForm.isClosed_mextDerivₗ _).smul _), ?_⟩
  rw [torusSymplecticForm_add_smul_mextDerivₗ_twoTorusSinForm,
    SmoothTwoForm.isNondegenerate_iff_separatingLeft]
  intro x v hv
  -- The coefficient `1 + s cos θ` does not vanish, so `v` is in the kernel of `dθ ∧ dφ`.
  have hcoeff : 1 + s * twoTorusCos x ≠ 0 := by
    have h := abs_twoTorusCos_le_one x
    have : |s * twoTorusCos x| < 1 := by
      rw [abs_mul]
      nlinarith [abs_nonneg s, abs_nonneg (twoTorusCos x)]
    intro h0
    linarith [neg_abs_le (s * twoTorusCos x)]
  refine (SmoothTwoForm.isNondegenerate_iff_separatingLeft.1 hω.isNondegenerate) x v fun w ↦ ?_
  have h := hv w
  simp only [SmoothBundleForm.eval₂_apply, SmoothForm.coe_funSMulₗ,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, ContMDiffMap.coe_add,
    ContMDiffMap.coe_smul, Pi.add_apply, Pi.smul_apply, ContMDiffMap.coe_one, Pi.one_apply,
    mul_eq_zero, hcoeff, false_or] at h
  rwa [SmoothBundleForm.eval₂_apply]

/-- **Moser's isotopy for `(1 + (t / 2) cos θ) dθ ∧ dφ`.** On the two-torus, the path
`ω_t = dθ ∧ dφ + (t / 2) d(sin θ dφ)`, whose velocity `(1 / 2) d(sin θ dφ)` is exact, has a Moser
isotopy: there are diffeomorphisms `ψ_t`, jointly smooth in `(t, x)`, with `ψ_0 = id` and
`ψ_t^* ω_t = ω_0` for `t ∈ [0, 1]`. -/
theorem exists_isotopy_mpullback_torusSymplecticForm_add_smul_mextDerivₗ_twoTorusSinForm :
    ∃ ψ : ℝ → (∀ _ : Unit ⊕ Unit, AddCircle (2 * π)) ≃ₘ⟮ModelWithCorners.pi fun _ ↦ 𝓘(ℝ),
        ModelWithCorners.pi fun _ ↦ 𝓘(ℝ)⟯ (∀ _ : Unit ⊕ Unit, AddCircle (2 * π)),
      ContMDiff (𝓘(ℝ, ℝ).prod (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)))
        (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) ∞
        (fun q : ℝ × (∀ _ : Unit ⊕ Unit, AddCircle (2 * π)) ↦ ψ q.1 q.2) ∧
      (∀ x, ψ 0 x = x) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, SmoothForm.mpullback (ψ t) (ψ t).contMDiff
        (torusSymplecticForm (fun _ ↦ 2 * π) +
          (t / 2) • mextDerivₗ (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) 1
            twoTorusSinForm) =
        torusSymplecticForm fun _ ↦ 2 * π := by
  -- Reparametrize by a smooth `c` with `c t = t` on `[0, 1]` and `|c| < 2`, keeping the slices
  -- `ω_(c t)` symplectic.
  obtain ⟨g, hg, hgid⟩ :=
    (⟨Ioo (-2) 2, isOpen_Ioo⟩ : TopologicalSpace.Opens ℝ).exists_contMDiff_eventuallyEq_id
      (convex_Icc 0 1) isCompact_Icc (nonempty_Icc.2 zero_le_one)
      fun t ht ↦ ⟨by linarith [ht.1], by linarith [ht.2]⟩
  set c : ℝ → ℝ := fun t ↦ (g t : ℝ)
  have hc : ContDiff ℝ ∞ c := contMDiff_iff_contDiff.1 (contMDiff_subtypeVal.comp hg)
  have hct (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : c t = t := (hgid t ht).self_of_nhds
  have hc2 (t : ℝ) : |c t| < 2 := abs_lt.2 (g t).property
  have hc' : ContDiff ℝ ∞ (deriv c) := (contDiff_infty_iff_deriv.1 hc).2
  -- The family with slices `ω_(c t)`, and the family of primitives `c'(t) (1 / 2) sin θ dφ` of its
  -- velocities.
  have hslice (t : ℝ) : SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
      (SmoothForm.lineMapFamily (torusSymplecticForm fun _ ↦ 2 * π)
        (torusSymplecticForm (fun _ ↦ 2 * π) + (1 / 2 : ℝ) •
          mextDerivₗ (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) 1 twoTorusSinForm) hc) =
      torusSymplecticForm (fun _ ↦ 2 * π) + (c t / 2) •
        mextDerivₗ (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) 1 twoTorusSinForm := by
    rw [SmoothForm.mpullback_prodMk_lineMapFamily, add_sub_cancel_left, smul_smul]
    congr 2
    ring
  obtain ⟨ψ, hψ, hψ0, -, hψω⟩ := SmoothTwoForm.exists_isotopy_mpullback_eq _
    (SmoothForm.lineMapFamily 0 ((1 / 2 : ℝ) • twoTorusSinForm) hc')
    (fun t ↦ by
      rw [hslice]
      refine isSymplectic_torusSymplecticForm_add_smul_mextDerivₗ_twoTorusSinForm ?_
      rw [abs_div, abs_two]
      linarith [hc2 t])
    (fun t ↦ by
      rw [← SmoothForm.coe_timeDeriv,
        ← SmoothForm.coe_mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id),
        SmoothForm.mpullback_prodMk_timeDeriv_lineMapFamily,
        SmoothForm.mpullback_prodMk_lineMapFamily, ← mextDerivₗ_apply]
      simp only [sub_zero, zero_add, add_sub_cancel_left, map_smul])
  refine ⟨ψ, hψ, hψ0, fun t ht ↦ ?_⟩
  have h := hψω t
  rwa [hslice, hslice, hct t ht, hct 0 ⟨le_rfl, zero_le_one⟩, zero_div, zero_smul,
    add_zero] at h

end TwoTorus

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Pow
public import TauCeti.Geometry.Manifold.Orientation.TopForm
import TauCeti.Geometry.Contact.Transition
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import TauCeti.Geometry.Symplectic.Volume
import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Covector

/-!
# The contact volume criterion

On a manifold of dimension `2 n + 1`, a one-form `α` is a contact form exactly when the
top-degree form `α ∧ (dα)ⁿ` vanishes nowhere
(`TauCeti.SmoothForm.isContactForm_iff_wedge_wedgePow_apply_ne_zero`). This is the classical
definition of a contact form; in Tau Ceti the contact condition `TauCeti.SmoothForm.IsContactForm`
is the intrinsic one, that `α_x ≠ 0` and `dα_x` is nondegenerate on the hyperplane `ker α_x`, and
this file proves that the two agree. The criterion holds point by point
(`TauCeti.SmoothForm.isContactFormAt_iff_wedge_wedgePow_apply_ne_zero`), so it also identifies the
open set where a one-form is contact.

The pointwise statement is linear algebra
(`ContinuousAlternatingMap.pairedWedge_wedgePow_ne_zero_iff`). Let `a` be a covector and `B` a
two-form on a space `E` of dimension `2 n + 1`. If `a = 0` then `a ∧ Bⁿ = 0`. Otherwise choose `r`
with `a(r) = 1`. A top-degree form on `E` is determined by its interior product with `r` on the
hyperplane `ker a`, and since `a` vanishes on `ker a`,

`ι_r (a ∧ Bⁿ) = a(r) Bⁿ = (B|_(ker a))ⁿ` on `ker a`.

So `a ∧ Bⁿ ≠ 0` exactly when the top power of the restriction of `B` to the `2 n`-dimensional
hyperplane `ker a` is nonzero
(`ContinuousAlternatingMap.pairedWedge_eq_zero_iff_compContinuousLinearMap_subtypeL_eq_zero`),
that is, when this restriction is nondegenerate (`ContinuousAlternatingMap.wedgePow_ne_zero_iff`).

Consequently a contact form `α` makes `M` orientable: `α ∧ (dα)ⁿ` is a volume form, and
`TauCeti.SmoothForm.IsContactForm.volumeOrientation` is the orientation on which it is positive.

The volume form scales with the defining form: if `β = f α` for a function `f`, then

`β ∧ (dβ)ⁿ = fⁿ⁺¹ α ∧ (dα)ⁿ`

(`TauCeti.SmoothForm.wedge_wedgePow_apply_of_eq_smul`). Indeed `dβ = f dα + df ∧ α`, and after
the factor `f α` the summand `df ∧ α` drops out of every power, because each term it contributes
contains `α` twice (`ContinuousAlternatingMap.pairedWedge_smul_wedgePow_smul_add_pairedWedge`). This
holds in every dimension. So positive multiples of a contact form `α`, which define the same
cooriented contact structure, define the same orientation. A coorientation-reversing change
`f < 0` multiplies the volume form by `fⁿ⁺¹`, of sign `(-1)ⁿ⁺¹`. For `n` odd, every contact form
with the same kernel defines the same orientation, so a contact structure orients `M` by itself
(`TauCeti.SmoothForm.IsContactForm.volumeOrientation_eq_of_kerDistribution_eq_of_odd`). For `n`
even, `-α` defines the opposite orientation
(`TauCeti.SmoothForm.IsContactForm.volumeOrientation_neg_of_even`).

## Main results

* `ContinuousAlternatingMap.pairedWedge_wedgePow_ne_zero_iff`: a covector `a` and a two-form `B` on
  a space of dimension `2 n + 1` satisfy `a ∧ Bⁿ ≠ 0` exactly when `a ≠ 0` and `B` is
  nondegenerate on `ker a`.
* `TauCeti.SmoothForm.isContactFormAt_iff_wedge_wedgePow_apply_ne_zero`: a smooth one-form is a
  contact form at `x` exactly when `α ∧ (dα)ⁿ` does not vanish at `x`.
* `TauCeti.SmoothForm.isContactForm_iff_wedge_wedgePow_apply_ne_zero`: a smooth one-form is a
  contact form exactly when `α ∧ (dα)ⁿ` vanishes nowhere.
* `TauCeti.SmoothForm.IsContactForm.volumeOrientation`: the orientation of a manifold defined by a
  contact form.
* `TauCeti.SmoothForm.wedge_wedgePow_apply_of_eq_smul`: the scaling law
  `(f α) ∧ (d (f α))ⁿ = fⁿ⁺¹ α ∧ (dα)ⁿ`.
* `TauCeti.SmoothForm.IsContactForm.volumeOrientation_eq_of_eq_smul`,
  `TauCeti.SmoothForm.IsContactForm.volumeOrientation_eq_neg_of_eq_smul`: the orientation of `f α`
  is that of `α` where `fⁿ⁺¹ > 0` everywhere, and the opposite one where `fⁿ⁺¹ < 0` everywhere.
* `TauCeti.SmoothForm.IsContactForm.volumeOrientation_eq_of_eq_smul_of_pos`: positive multiples
  of a contact form define the same orientation.
* `TauCeti.SmoothForm.IsContactForm.volumeOrientation_eq_of_kerDistribution_eq_of_odd`: for `n`
  odd, contact forms with the same kernel define the same orientation.
* `TauCeti.SmoothForm.IsContactForm.volumeOrientation_neg_of_even`: for `n` even, `-α` defines the
  opposite orientation.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1 (the condition `α ∧ (dα)ⁿ ≠ 0` and Lemma 1.1.3) and Section 2.1.
* H. Geiges, *Contact geometry*, in Handbook of Differential Geometry, vol. 2, North-Holland,
  2006, 315–382, arXiv:math/0307242, Remark 2.2 (the scaling
  `(f α) ∧ (d (f α))ⁿ = fⁿ⁺¹ α ∧ (dα)ⁿ` and its consequences for orientations).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017, Section 3.5.
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff

namespace ContinuousAlternatingMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [FiniteDimensional ℝ E]
  {n : ℕ}

/-- **The linear contact volume criterion.** On a real vector space of dimension `2 n + 1`, a
covector `a` and a two-form `B` satisfy `a ∧ Bⁿ ≠ 0` exactly when `a ≠ 0` and `B` is nondegenerate
on the hyperplane `ker a`: the only vector of `ker a` which is `B`-orthogonal to all of `ker a` is
zero. -/
theorem pairedWedge_wedgePow_ne_zero_iff (hn : finrank ℝ E = 2 * n + 1)
    (a : E [⋀^Fin 1]→L[ℝ] ℝ) (B : E [⋀^Fin 2]→L[ℝ] ℝ) :
    pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ a
        (B.wedgePow n) ≠ 0 ↔
      a ≠ 0 ∧ ∀ v, a ![v] = 0 → (∀ w, a ![w] = 0 → B ![v, w] = 0) → v = 0 := by
  by_cases ha : a = 0
  · simp [ha]
  -- The covector `a` as a linear functional `f`, and its kernel `N`.
  set f : Dual ℝ E := ((ofSubsingleton ℝ E ℝ (0 : Fin 1)).symm a).toLinearMap
  have hf (u : E) : f u = a ![u] := by
    simp [f, Matrix.vec_single_eq_const]
  set N := LinearMap.ker f
  have hN (u : E) : u ∈ N ↔ a ![u] = 0 := by rw [LinearMap.mem_ker, hf]
  have hf₀ : f ≠ 0 := by
    refine fun h ↦ ha (ext fun u ↦ ?_)
    have hu : u = ![u 0] := by
      ext i
      fin_cases i
      rfl
    rw [hu, ← hf, h, LinearMap.zero_apply, coe_zero, Pi.zero_apply]
  have hNrank : finrank ℝ N = 2 * n := by
    have : finrank ℝ N + 1 = finrank ℝ E := Dual.finrank_ker_add_one_of_ne_zero hf₀
    omega
  obtain ⟨r, hr⟩ := LinearMap.surjective_iff_ne_zero.2 hf₀ 1
  -- `a ∧ Bⁿ ≠ 0` exactly when `(B|_N)ⁿ ≠ 0`, that is, when `B|_N` is nondegenerate.
  rw [Ne, pairedWedge_eq_zero_iff_compContinuousLinearMap_subtypeL_eq_zero hn a _ hN
      ((hf r).symm.trans hr), wedgePow_compContinuousLinearMap, ← Ne,
    wedgePow_ne_zero_iff hNrank]
  have hpair (p q : N) : (Subtype.val ∘ ![p, q] : Fin 2 → E) = ![(p : E), q] := by
    ext i
    fin_cases i <;> rfl
  simp only [ha, ne_eq, not_false_eq_true, true_and, compContinuousLinearMap_apply,
    Submodule.coe_subtypeL, Submodule.coe_subtype, hpair]
  constructor
  · intro h v hv hvw
    exact congrArg Subtype.val (h ⟨v, (hN v).2 hv⟩ fun w ↦ hvw w ((hN w).1 w.property))
  · intro h v hv
    exact Subtype.ext (h v ((hN v).1 v.property) fun w hw ↦ hv ⟨w, (hN w).2 hw⟩)

end ContinuousAlternatingMap

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] {n : ℕ}

/-- **The contact volume criterion at a point.** On a manifold of dimension `2 n + 1`, a smooth
one-form `α` is a contact form at `x` exactly when `α ∧ (dα)ⁿ` does not vanish at `x`. -/
theorem isContactFormAt_iff_wedge_wedgePow_apply_ne_zero (hn : finrank ℝ E = 2 * n + 1)
    (α : SmoothForm I M ℝ 1) (x : M) :
    IsContactFormAt α.val x ↔ (wedge α ((mextDerivₗ I 1 α).wedgePow n)).val x ≠ 0 := by
  -- The degree `1 + 1` of `dα` is the degree `2` of the linear criterion only definitionally.
  have key := ContinuousAlternatingMap.pairedWedge_wedgePow_ne_zero_iff hn (α.val x)
    (mextDeriv α.val x)
  rw [coe_wedge, RoughForm.wedge_def, RoughForm.wedgeWith_apply', wedgePow_apply,
    mextDerivₗ_apply]
  refine Iff.trans ?_ key.symm
  constructor
  · intro h
    exact ⟨h.ne_zero, fun v hv hvw ↦ h.nondegenerate v (RoughForm.mem_ker.2 hv)
      fun w hw ↦ hvw w (RoughForm.mem_ker.1 hw)⟩
  · intro h
    exact ⟨h.1, fun v hv hvw ↦ h.2 v (RoughForm.mem_ker.1 hv)
      fun w hw ↦ hvw w (RoughForm.mem_ker.2 hw)⟩

/-- **The contact volume criterion.** On a manifold of dimension `2 n + 1`, a smooth one-form `α`
is a contact form exactly when `α ∧ (dα)ⁿ` vanishes nowhere. -/
theorem isContactForm_iff_wedge_wedgePow_apply_ne_zero (hn : finrank ℝ E = 2 * n + 1)
    (α : SmoothForm I M ℝ 1) :
    α.IsContactForm ↔ ∀ x, (wedge α ((mextDerivₗ I 1 α).wedgePow n)).val x ≠ 0 := by
  rw [isContactForm_iff_forall_isContactFormAt]
  exact forall_congr' (isContactFormAt_iff_wedge_wedgePow_apply_ne_zero hn α)

/-- The **orientation of a contact form**: on a manifold of dimension `2 n + 1`, the orientation
on which the volume form `α ∧ (dα)ⁿ` of a contact form `α` is positive. -/
def IsContactForm.volumeOrientation {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm)
    (hn : finrank ℝ E = 2 * n + 1) : Manifold.Orientation I M (Fin (1 + 2 * n)) :=
  Manifold.Orientation.ofTopForm (hn.trans (Nat.add_comm _ _))
    (wedge α ((mextDerivₗ I 1 α).wedgePow n)).val
    ((wedge α ((mextDerivₗ I 1 α).wedgePow n)).isSmoothForm.of_le bot_le)
    ((isContactForm_iff_wedge_wedgePow_apply_ne_zero hn α).1 hα)

/-- A tangent basis is positive for the orientation of a contact form `α` exactly when the volume
form `α ∧ (dα)ⁿ` is positive on it. -/
theorem IsContactForm.orientation_eq_orientationAt_volumeOrientation_iff
    {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) (hn : finrank ℝ E = 2 * n + 1) {x : M}
    (b : Basis (Fin (1 + 2 * n)) ℝ (TangentSpace I x)) :
    b.orientation = Manifold.Orientation.orientationAt (hα.volumeOrientation hn) x ↔
      0 < (wedge α ((mextDerivₗ I 1 α).wedgePow n)).val x b :=
  Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff _ _ _ b

/-! ### Changing the contact form -/

omit [FiniteDimensional ℝ E] in
/-- **The scaling law of the contact volume form.** If `β = u α`, then at every point where `u`
is differentiable, `β ∧ (dβ)ⁿ = uⁿ⁺¹ α ∧ (dα)ⁿ`. This holds in every dimension, and for every
one-form `α`. -/
theorem wedge_wedgePow_apply_of_eq_smul {α β : SmoothForm I M ℝ 1} {u : M → ℝ} {x : M}
    (hu : MDifferentiableAt I 𝓘(ℝ) u x) (hβ : ∀ y, β.val y = u y • α.val y) (n : ℕ) :
    (wedge β ((mextDerivₗ I 1 β).wedgePow n)).val x =
      u x ^ (n + 1) • (wedge α ((mextDerivₗ I 1 α).wedgePow n)).val x := by
  simp only [coe_wedge, RoughForm.wedge_def, RoughForm.wedgeWith_apply', wedgePow_apply,
    mextDerivₗ_apply]
  rw [show β.val = fun y ↦ u y • α.val y from funext hβ,
    mextDeriv_fun_smul_eq_smul_add_pairedWedge hu (α.mdifferentiableAt x)]
  -- The degree `1 + 1` of `dα` is the degree `2` of the linear identity only definitionally.
  exact ContinuousAlternatingMap.pairedWedge_smul_wedgePow_smul_add_pairedWedge n (u x) _ _ _

namespace IsContactForm

variable {α β : SmoothForm I M ℝ 1} {u : M → ℝ} (hα : α.IsContactForm) (hβc : β.IsContactForm)
  (hn : finrank ℝ E = 2 * n + 1)
include hα hβc

/-- If `β = u α` with `uⁿ⁺¹ > 0` everywhere, the contact forms `α` and `β` define the same
orientation. -/
theorem volumeOrientation_eq_of_eq_smul (hu : MDifferentiable I 𝓘(ℝ) u)
    (hβ : ∀ y, β.val y = u y • α.val y) (hpos : ∀ x, 0 < u x ^ (n + 1)) :
    hβc.volumeOrientation hn = hα.volumeOrientation hn :=
  Manifold.Orientation.ofTopForm_eq_of_eq_smul _ _ _ _ _ hpos
    fun x ↦ wedge_wedgePow_apply_of_eq_smul (hu x) hβ n

/-- If `β = u α` with `uⁿ⁺¹ < 0` everywhere, the contact forms `α` and `β` define opposite
orientations. -/
theorem volumeOrientation_eq_neg_of_eq_smul (hu : MDifferentiable I 𝓘(ℝ) u)
    (hβ : ∀ y, β.val y = u y • α.val y) (hneg : ∀ x, u x ^ (n + 1) < 0) :
    hβc.volumeOrientation hn = -hα.volumeOrientation hn :=
  Manifold.Orientation.ofTopForm_eq_neg_of_eq_smul _ _ _ _ _ hneg
    fun x ↦ wedge_wedgePow_apply_of_eq_smul (hu x) hβ n

/-- Positive multiples of a contact form, which have the same kernel and induce the same
coorientation, define the same orientation. -/
theorem volumeOrientation_eq_of_eq_smul_of_pos (hu : MDifferentiable I 𝓘(ℝ) u)
    (hβ : ∀ y, β.val y = u y • α.val y) (hpos : ∀ x, 0 < u x) :
    hβc.volumeOrientation hn = hα.volumeOrientation hn :=
  hα.volumeOrientation_eq_of_eq_smul hβc hn hu hβ fun x ↦ pow_pos (hpos x) _

/-- **A contact structure of dimension `4 k + 3` orients the manifold.** When `n` is odd, two
contact forms with the same kernel define the same orientation, whatever their coorientations. -/
theorem volumeOrientation_eq_of_kerDistribution_eq_of_odd [IsManifold I ∞ M] (hodd : Odd n)
    (hker : β.kerDistribution = α.kerDistribution) :
    hβc.volumeOrientation hn = hα.volumeOrientation hn := by
  obtain ⟨u, ⟨hu, hu₀, hβ⟩, -⟩ :=
    (kerDistribution_eq_iff_existsUnique_fun_smul hα.apply_ne_zero).1 hker
  exact hα.volumeOrientation_eq_of_eq_smul hβc hn (hu.mdifferentiable (by simp)) hβ
    fun x ↦ hodd.add_one.pow_pos (hu₀ x)

omit hβc in
/-- When `n` is even, the contact forms `α` and `-α`, which have the same kernel and opposite
coorientations, define opposite orientations. -/
theorem volumeOrientation_neg_of_even (hev : Even n) :
    (isContactForm_neg_iff.2 hα).volumeOrientation hn = -hα.volumeOrientation hn :=
  hα.volumeOrientation_eq_neg_of_eq_smul _ hn (u := fun _ ↦ -1) mdifferentiable_const
    (fun y ↦ by simp) fun _ ↦ by rw [hev.add_one.neg_one_pow]; norm_num

end IsContactForm

end SmoothForm

end TauCeti

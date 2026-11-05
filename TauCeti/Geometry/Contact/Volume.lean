/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Pow
public import TauCeti.Geometry.Manifold.Orientation.TopForm
import TauCeti.Geometry.Symplectic.Volume
import TauCeti.LinearAlgebra.Alternating.TopDegree

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
hyperplane `ker a` is nonzero, that is, when this restriction is nondegenerate
(`ContinuousAlternatingMap.wedgePow_ne_zero_iff`).

Consequently a contact form `α` makes `M` orientable: `α ∧ (dα)ⁿ` is a volume form, and
`TauCeti.SmoothForm.IsContactForm.volumeOrientation` is the orientation on which it is positive.

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

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1 (the condition `α ∧ (dα)ⁿ ≠ 0` and Lemma 1.1.3) and Section 2.1.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017, Section 3.5.
-/

public section

noncomputable section

open Module

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
  obtain ⟨r, hr⟩ : ∃ r, f r = 1 := by
    obtain ⟨u, hu⟩ : ∃ u, f u ≠ 0 := by
      by_contra! h
      exact hf₀ (LinearMap.ext h)
    exact ⟨(f u)⁻¹ • u, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hu]⟩
  set Θ := pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ a
    (B.wedgePow n)
  -- The interior product of `Θ` with `r`, restricted to `N`, is the top power of `B|_N`.
  have hΘ : ((Θ.toAlternatingMap.domDomCongr (finCongr (Nat.add_comm 1 (2 * n)))).curryLeft r
      ).compLinearMap N.subtype =
        ((B.compContinuousLinearMap N.subtypeL).wedgePow n).toAlternatingMap := by
    ext w
    have hw (i : Fin (2 * n)) : a ![(w i : E)] = 0 := (hN _).1 (w i).2
    simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.curryLeft_apply_apply,
      AlternatingMap.domDomCongr_apply, coe_toAlternatingMap, Submodule.coe_subtype,
      ← wedgePow_compContinuousLinearMap, compContinuousLinearMap_apply,
      Submodule.coe_subtypeL]
    have hcast : (Matrix.vecCons r fun i ↦ (w i : E)) ∘ ⇑(finCongr (Nat.add_comm 1 (2 * n))) =
        Matrix.vecCons r (fun i ↦ (w i : E)) ∘ Fin.cast (Nat.add_comm 1 (2 * n)) := by
      ext
      simp
    rw [hcast, pairedWedge_apply_vecCons_of_forall _ _ _ _ r _ hw, ← hf, hr,
      ContinuousLinearMap.mul_apply', one_mul, Function.comp_def]
  rw [Ne, ← toAlternatingMap_injective.eq_iff, toAlternatingMap_zero,
    ← AlternatingMap.domDomCongr_eq_zero_iff (finCongr (Nat.add_comm 1 (2 * n))),
    ← AlternatingMap.curryLeft_compLinearMap_subtype_eq_zero_iff hn _ hr, hΘ,
    ← toAlternatingMap_zero, toAlternatingMap_injective.eq_iff, ← Ne,
    wedgePow_ne_zero_iff hNrank]
  have hpair (p q : N) : (Subtype.val ∘ ![p, q] : Fin 2 → E) = ![(p : E), q] := by
    ext i
    fin_cases i <;> rfl
  simp only [ha, ne_eq, not_false_eq_true, true_and, compContinuousLinearMap_apply,
    Submodule.coe_subtypeL, Submodule.coe_subtype, hpair]
  constructor
  · intro h v hv hvw
    exact congrArg Subtype.val (h ⟨v, (hN v).2 hv⟩ fun w ↦ hvw w ((hN w).1 w.2))
  · intro h v hv
    exact Subtype.ext (h v ((hN v).1 v.2) fun w hw ↦ hv ⟨w, (hN w).2 hw⟩)

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
    IsContactFormAt α.1 x ↔ (wedge α ((mextDerivₗ I 1 α).wedgePow n)).1 x ≠ 0 := by
  -- The degree `1 + 1` of `dα` is the degree `2` of the linear criterion only definitionally.
  have key := ContinuousAlternatingMap.pairedWedge_wedgePow_ne_zero_iff hn (α.1 x)
    (mextDeriv α.1 x)
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
    α.IsContactForm ↔ ∀ x, (wedge α ((mextDerivₗ I 1 α).wedgePow n)).1 x ≠ 0 := by
  rw [isContactForm_iff_forall_isContactFormAt]
  exact forall_congr' (isContactFormAt_iff_wedge_wedgePow_apply_ne_zero hn α)

/-- The **orientation of a contact form**: on a manifold of dimension `2 n + 1`, the orientation
on which the volume form `α ∧ (dα)ⁿ` of a contact form `α` is positive. -/
def IsContactForm.volumeOrientation {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm)
    (hn : finrank ℝ E = 2 * n + 1) : Manifold.Orientation I M (Fin (1 + 2 * n)) :=
  Manifold.Orientation.ofTopForm (hn.trans (Nat.add_comm _ _))
    (wedge α ((mextDerivₗ I 1 α).wedgePow n)).1
    ((wedge α ((mextDerivₗ I 1 α).wedgePow n)).isSmoothForm.of_le bot_le)
    ((isContactForm_iff_wedge_wedgePow_apply_ne_zero hn α).1 hα)

/-- A tangent basis is positive for the orientation of a contact form `α` exactly when the volume
form `α ∧ (dα)ⁿ` is positive on it. -/
theorem IsContactForm.orientation_eq_orientationAt_volumeOrientation_iff
    {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) (hn : finrank ℝ E = 2 * n + 1) {x : M}
    (b : Basis (Fin (1 + 2 * n)) ℝ (TangentSpace I x)) :
    b.orientation = Manifold.Orientation.orientationAt (hα.volumeOrientation hn) x ↔
      0 < (wedge α ((mextDerivₗ I 1 α).wedgePow n)).1 x b :=
  Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff _ _ _ b

end SmoothForm

end TauCeti

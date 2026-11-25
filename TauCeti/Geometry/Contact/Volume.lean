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

The volume form changes by a power of the multiplier when the contact form is rescaled. For a
function `f` differentiable at `x`,

`((f α) ∧ (d(f α))ⁿ)ₓ = f(x)ⁿ⁺¹ (α ∧ (dα)ⁿ)ₓ`

(`TauCeti.SmoothForm.wedge_wedgePow_apply_of_eq_smul`), in every dimension. Indeed
`d(f α) = df ∧ α + f dα`, whose first term vanishes on `ker αₓ`, and a covector `a` wedged with a
form only sees the restriction of that form to `ker a`
(`ContinuousAlternatingMap.pairedWedge_congr_right_of_compContinuousLinearMap_subtypeL_eq`). In
particular `(c α) ∧ (d(c α))ⁿ = cⁿ⁺¹ α ∧ (dα)ⁿ` for a constant `c`
(`TauCeti.SmoothForm.wedge_smul_wedgePow_mextDerivₗ_smul`), and
`(-α) ∧ (d(-α))ⁿ = (-1)ⁿ⁺¹ α ∧ (dα)ⁿ`. So a contact form `β = f α` defines the orientation of `α`
where `fⁿ⁺¹ > 0` and the opposite one where `fⁿ⁺¹ < 0`. For odd `n` all contact forms with the same
kernel define the same orientation, so the contact structure orients `M` by itself
(`TauCeti.SmoothForm.IsContactForm.volumeOrientation_eq_of_kerDistribution_eq`); for even `n` the
orientation changes with the coorientation, `α ↦ -α`.

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
  `(f α) ∧ (d(f α))ⁿ = fⁿ⁺¹ α ∧ (dα)ⁿ`.
* `TauCeti.SmoothForm.wedge_smul_wedgePow_mextDerivₗ_smul`,
  `TauCeti.SmoothForm.wedge_neg_wedgePow_mextDerivₗ_neg`: the scaling law for constants.
* `TauCeti.SmoothForm.IsContactForm.volumeOrientation_eq_of_eq_smul`,
  `TauCeti.SmoothForm.IsContactForm.volumeOrientation_eq_neg_of_eq_smul`: rescaling a contact form
  keeps or reverses its orientation according to the sign of `fⁿ⁺¹`.
* `TauCeti.SmoothForm.IsContactForm.volumeOrientation_neg_eq_of_odd`,
  `TauCeti.SmoothForm.IsContactForm.volumeOrientation_neg_eq_neg_of_even`: reversing the
  coorientation keeps the orientation for odd `n` and reverses it for even `n`.
* `TauCeti.SmoothForm.IsContactForm.volumeOrientation_eq_of_kerDistribution_eq`: for odd `n` the
  orientation depends only on the contact distribution.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1 (the condition `α ∧ (dα)ⁿ ≠ 0` and Lemma 1.1.3) and Section 2.1.
* H. Geiges, *Contact geometry*, in Handbook of Differential Geometry, vol. 2, North-Holland,
  2006, 315–382, arXiv:math/0307242, Remark 2.2 (the scaling law).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017, Section 3.5.
-/

public section

noncomputable section

open Module
open scoped ContDiff Manifold

namespace ContinuousAlternatingMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [FiniteDimensional ℝ E]
  {n : ℕ}

omit [FiniteDimensional ℝ E] in
/-- A two-form restricted to a subspace `N` takes the value of the form on the pair of underlying
vectors. -/
private theorem compContinuousLinearMap_subtypeL_apply_fin_two (B : E [⋀^Fin 2]→L[ℝ] ℝ)
    (N : Submodule ℝ E) (w : Fin 2 → N) :
    B.compContinuousLinearMap N.subtypeL w = B ![(w 0 : E), w 1] := by
  rw [compContinuousLinearMap_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

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
  simp only [ha, ne_eq, not_false_eq_true, true_and, compContinuousLinearMap_subtypeL_apply_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · intro h v hv hvw
    exact congrArg Subtype.val (h ⟨v, (hN v).2 hv⟩ fun w ↦ hvw w ((hN w).1 w.property))
  · intro h v hv
    exact Subtype.ext (h v ((hN v).1 v.property) fun w hw ↦ hv ⟨w, (hN w).2 hw⟩)

omit [FiniteDimensional ℝ E] in
/-- **The linear scaling law for `a ∧ Bⁿ`.** On a real vector space, let `a` be a covector and `B`,
`B'` two-forms with `B' = c B` on the hyperplane `ker a`. Then `(c a) ∧ B'ⁿ = cⁿ⁺¹ (a ∧ Bⁿ)`. -/
theorem pairedWedge_smul_wedgePow_of_eq_smul
    (a : E [⋀^Fin 1]→L[ℝ] ℝ) {B B' : E [⋀^Fin 2]→L[ℝ] ℝ} {c : ℝ}
    (hB : ∀ v w, a ![v] = 0 → a ![w] = 0 → B' ![v, w] = c * B ![v, w]) :
    pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (c • a)
        (B'.wedgePow n) =
      c ^ (n + 1) • pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂ a (B.wedgePow n) := by
  set N := LinearMap.ker ((ofSubsingleton ℝ E ℝ (0 : Fin 1)).symm a).toLinearMap
  have hN (u : E) : u ∈ N ↔ a ![u] = 0 := by
    simp [N, Matrix.vec_single_eq_const]
  -- On `ker a` the two-form `B'` is `c B`, so `a ∧ B'ⁿ = a ∧ (c B)ⁿ`.
  have hres : B'.compContinuousLinearMap N.subtypeL =
      (c • B).compContinuousLinearMap N.subtypeL := by
    ext w
    simp only [compContinuousLinearMap_subtypeL_apply_fin_two, smul_apply, smul_eq_mul]
    exact hB _ _ ((hN _).1 (w 0).property) ((hN _).1 (w 1).property)
  rw [pairedWedge_smul_left, pairedWedge_congr_right_of_compContinuousLinearMap_subtypeL_eq a hN
      (ψ' := (c • B).wedgePow n) (by rw [wedgePow_compContinuousLinearMap,
        wedgePow_compContinuousLinearMap, hres]),
    wedgePow_smul, pairedWedge_smul_right, smul_smul, pow_succ']

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

/-! ### The scaling law -/

omit [FiniteDimensional ℝ E] in
/-- **The contact volume scaling law at a point.** Let `β = f α` for a one-form `α` and a function
`f` differentiable at `x`. Then `(β ∧ (dβ)ⁿ)ₓ = f(x)ⁿ⁺¹ (α ∧ (dα)ⁿ)ₓ`. -/
theorem wedge_wedgePow_apply_of_eq_smul
    {α β : SmoothForm I M ℝ 1} {f : M → ℝ} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hβ : ∀ y, β.val y = f y • α.val y) :
    (wedge β ((mextDerivₗ I 1 β).wedgePow n)).val x =
      f x ^ (n + 1) • (wedge α ((mextDerivₗ I 1 α).wedgePow n)).val x := by
  have hβ' : β.val = fun y ↦ f y • α.val y := funext hβ
  simp only [coe_wedge, RoughForm.wedge_def, RoughForm.wedgeWith_apply', wedgePow_apply,
    mextDerivₗ_apply, hβ']
  refine ContinuousAlternatingMap.pairedWedge_smul_wedgePow_of_eq_smul (E := TangentSpace I x)
    (α.val x) fun v w hv hw ↦ ?_
  -- Restate `hv` and `hw` with the tangent-space instances that the Leibniz rule uses.
  have hv' : α.val x ![v] = 0 := hv
  have hw' : α.val x ![w] = 0 := hw
  have h := mextDeriv_fun_smul_apply hf (α.mdifferentiableAt x) v w
  rw [hv', hw', mul_zero, mul_zero, sub_zero, zero_add] at h
  exact h

omit [FiniteDimensional ℝ E] in
/-- **The scaling law for constant multiples.** Multiplying a one-form `α` by a constant `c`
multiplies `α ∧ (dα)ⁿ` by `cⁿ⁺¹`. -/
theorem wedge_smul_wedgePow_mextDerivₗ_smul (c : ℝ) (α : SmoothForm I M ℝ 1) :
    wedge (c • α) ((mextDerivₗ I 1 (c • α)).wedgePow n) =
      c ^ (n + 1) • wedge α ((mextDerivₗ I 1 α).wedgePow n) := by
  refine Subtype.ext (funext fun x ↦ ?_)
  rw [Submodule.coe_smul, Pi.smul_apply]
  exact wedge_wedgePow_apply_of_eq_smul mdifferentiableAt_const fun _ ↦ rfl

omit [FiniteDimensional ℝ E] in
/-- Reversing the coorientation, `α ↦ -α`, multiplies `α ∧ (dα)ⁿ` by `(-1)ⁿ⁺¹`. -/
theorem wedge_neg_wedgePow_mextDerivₗ_neg (α : SmoothForm I M ℝ 1) :
    wedge (-α) ((mextDerivₗ I 1 (-α)).wedgePow n) =
      (-1 : ℝ) ^ (n + 1) • wedge α ((mextDerivₗ I 1 α).wedgePow n) := by
  simpa only [neg_one_smul ℝ α] using wedge_smul_wedgePow_mextDerivₗ_smul (n := n) (-1) α

/-- Rescaling a contact form by a function `f` with `fⁿ⁺¹ > 0` keeps its orientation: if `α` and
`β = f α` are contact forms on a manifold of dimension `2 n + 1`, they define the same
orientation. This applies when `f > 0`, and for odd `n` whenever `f` vanishes nowhere. -/
theorem IsContactForm.volumeOrientation_eq_of_eq_smul {α β : SmoothForm I M ℝ 1}
    (hα : α.IsContactForm) (hβ : β.IsContactForm) (hn : finrank ℝ E = 2 * n + 1) {f : M → ℝ}
    (hf : ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (hβα : ∀ x, β.val x = f x • α.val x)
    (hpos : ∀ x, 0 < f x ^ (n + 1)) :
    hβ.volumeOrientation hn = hα.volumeOrientation hn :=
  Manifold.Orientation.ofTopForm_eq_of_eq_smul _ _ _ _ _ hpos fun x ↦
    wedge_wedgePow_apply_of_eq_smul (hf x) hβα

/-- Rescaling a contact form by a function `f` with `fⁿ⁺¹ < 0` reverses its orientation: if `α`
and `β = f α` are contact forms on a manifold of dimension `2 n + 1`, they define opposite
orientations. This applies for even `n` when `f < 0`. -/
theorem IsContactForm.volumeOrientation_eq_neg_of_eq_smul {α β : SmoothForm I M ℝ 1}
    (hα : α.IsContactForm) (hβ : β.IsContactForm) (hn : finrank ℝ E = 2 * n + 1) {f : M → ℝ}
    (hf : ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (hβα : ∀ x, β.val x = f x • α.val x)
    (hneg : ∀ x, f x ^ (n + 1) < 0) :
    hβ.volumeOrientation hn = -hα.volumeOrientation hn :=
  Manifold.Orientation.ofTopForm_eq_neg_of_eq_smul _ _ _ _ _ hneg fun x ↦
    wedge_wedgePow_apply_of_eq_smul (hf x) hβα

/-- For odd `n`, reversing the coorientation, `α ↦ -α`, keeps the orientation of a contact form
on a manifold of dimension `2 n + 1`. -/
theorem IsContactForm.volumeOrientation_neg_eq_of_odd {α : SmoothForm I M ℝ 1}
    (hα : α.IsContactForm) (hn : finrank ℝ E = 2 * n + 1) (hodd : Odd n) :
    (isContactForm_neg_iff.2 hα).volumeOrientation hn = hα.volumeOrientation hn :=
  hα.volumeOrientation_eq_of_eq_smul _ hn (f := fun _ ↦ -1) (fun _ ↦ mdifferentiableAt_const)
    (fun x ↦ by rw [Submodule.coe_neg, Pi.neg_apply, neg_one_smul])
    fun _ ↦ by rw [(hodd.add_one).neg_one_pow]; exact one_pos

/-- For even `n`, reversing the coorientation, `α ↦ -α`, reverses the orientation of a contact
form on a manifold of dimension `2 n + 1`. -/
theorem IsContactForm.volumeOrientation_neg_eq_neg_of_even {α : SmoothForm I M ℝ 1}
    (hα : α.IsContactForm) (hn : finrank ℝ E = 2 * n + 1) (heven : Even n) :
    (isContactForm_neg_iff.2 hα).volumeOrientation hn = -hα.volumeOrientation hn :=
  hα.volumeOrientation_eq_neg_of_eq_smul _ hn (f := fun _ ↦ -1) (fun _ ↦ mdifferentiableAt_const)
    (fun x ↦ by rw [Submodule.coe_neg, Pi.neg_apply, neg_one_smul])
    fun _ ↦ by rw [(heven.add_one).neg_one_pow]; exact neg_one_lt_zero

end SmoothForm

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {n : ℕ}

/-- **For odd `n`, a contact structure orients the manifold.** On a manifold of dimension `2 n + 1`
with `n` odd, two contact forms with the same kernel define the same orientation. -/
theorem IsContactForm.volumeOrientation_eq_of_kerDistribution_eq {α β : SmoothForm I M ℝ 1}
    (hα : α.IsContactForm) (hβ : β.IsContactForm) (hn : finrank ℝ E = 2 * n + 1) (hodd : Odd n)
    (h : β.kerDistribution = α.kerDistribution) :
    hβ.volumeOrientation hn = hα.volumeOrientation hn := by
  obtain ⟨f, ⟨hf, hf₀, hβα⟩, -⟩ :=
    (kerDistribution_eq_iff_existsUnique_fun_smul hα.apply_ne_zero).1 h
  exact hα.volumeOrientation_eq_of_eq_smul hβ hn (fun x ↦ hf.mdifferentiableAt (by simp)) hβα
    fun x ↦ hodd.add_one.pow_pos (hf₀ x)

end SmoothForm

end TauCeti

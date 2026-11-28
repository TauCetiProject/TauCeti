/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Distribution
public import TauCeti.Geometry.Contact.Volume

/-!
# The orientation of a contact structure in dimension `4 k + 3`

Let `ξ` be a contact structure (`TauCeti.IsContactDistribution`) on a manifold `M` of dimension
`2 n + 1`. Near every point `ξ` is the kernel of a contact form `α`, and `α ∧ (dα)ⁿ` is a volume
form there. A second local defining form `β` agrees with `α` up to a factor at each point, and the
volume forms scale by its `(n + 1)`-st power:

`(β ∧ (dβ)ⁿ)ₓ = cⁿ⁺¹ (α ∧ (dα)ⁿ)ₓ` where `βₓ = c αₓ`

(`TauCeti.SmoothForm.exists_ne_zero_wedge_wedgePow_apply_eq_pow_smul`). No multiplier function
on a neighbourhood is needed, only the kernels near `x`: on `ker αₓ` both exterior derivatives are
computed from the Levi form of the common kernel, `dβₓ(u, v) = βₓ(L(u, v)) = c αₓ(L(u, v))
= c dαₓ(u, v)` (`TauCeti.RoughForm.apply_eq_mextDeriv_of_mkQ_eq_distributionLeviForm`), and the
linear scaling law `ContinuousAlternatingMap.pairedWedge_smul_wedgePow_of_eq_smul` applies.

For odd `n` the factor `cⁿ⁺¹` is positive, so all local contact forms select the same orientation
of each tangent space. These orientations are locally constant
(`TauCeti.eventually_mapOrientation_topFormOrientationAt_eq`), so they orient `M`:
`TauCeti.IsContactDistribution.volumeOrientation` is the orientation of `M` on which `α ∧ (dα)ⁿ`
is positive for every local contact form `α` of `ξ`
(`TauCeti.IsContactDistribution.orientation_eq_orientationAt_volumeOrientation_iff`). A contact
structure in dimension `4 k + 3` therefore orients its manifold by itself, even when it is the
kernel of no global one-form, as for the space of contact elements of the plane
(`TauCeti.not_exists_smoothForm_ker_eq_contactElementDistribution`); when it is the kernel of a
contact form `α`, this is the orientation of `α`
(`TauCeti.IsContactDistribution.volumeOrientation_eq_of_kerDistribution_eq`). For even `n` there is
no such orientation in general: replacing `α` by `-α` reverses the orientation of `α ∧ (dα)ⁿ`
(`TauCeti.SmoothForm.IsContactForm.volumeOrientation_neg_eq_neg_of_even`).

## Main definitions

* `TauCeti.IsContactDistribution.volumeOrientation`: for odd `n`, the orientation of a manifold of
  dimension `2 n + 1` defined by a contact structure.

## Main results

* `TauCeti.SmoothForm.exists_ne_zero_wedge_wedgePow_apply_eq_pow_smul`: two one-forms whose kernels
  agree near `x` have proportional volume forms `α ∧ (dα)ⁿ` at `x`, with factor `cⁿ⁺¹` for
  `βₓ = c αₓ`.
* `TauCeti.IsContactDistribution.orientation_eq_orientationAt_volumeOrientation_iff`: a tangent
  basis is positive for the orientation of a contact structure exactly when the volume form of a
  local contact form is positive on it.
* `TauCeti.IsContactDistribution.volumeOrientation_eq_of_kerDistribution_eq`: for the kernel of a
  contact form, it is the orientation of that form.
* `TauCeti.IsContactDistribution.orientable`: in dimension `4 k + 3`, a manifold carrying a contact
  structure is orientable.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008, Section 1.1
  (Lemma 1.1.3 and the remark following it).
* H. Geiges, *Contact geometry*, in Handbook of Differential Geometry, vol. 2, North-Holland,
  2006, 315–382, arXiv:math/0307242, Remark 2.2.
-/

public section

noncomputable section

open Filter Module
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ}

namespace SmoothForm

variable [IsManifold I 2 M]

/-- **The contact volume scaling law for forms with the same local kernels.** Let `α` and `β` be
smooth one-forms whose kernels agree near `x`, with `αₓ ≠ 0`. Then `βₓ = c αₓ` for a number
`c ≠ 0`, and `(β ∧ (dβ)ⁿ)ₓ = cⁿ⁺¹ (α ∧ (dα)ⁿ)ₓ`, in every dimension. -/
theorem exists_ne_zero_wedge_wedgePow_apply_eq_pow_smul {α β : SmoothForm I M ℝ 1} {x : M}
    (hα : α.val x ≠ 0) (hβα : ∀ᶠ y in 𝓝 x, β.kerDistribution y = α.kerDistribution y) :
    ∃ c : ℝ, c ≠ 0 ∧ β.val x = c • α.val x ∧
      (wedge β ((mextDerivₗ I 1 β).wedgePow n)).val x =
        c ^ (n + 1) • (wedge α ((mextDerivₗ I 1 α).wedgePow n)).val x := by
  have : IsManifold I (1 + 1) M := IsManifold.of_le (n := 2) le_rfl
  -- A vector `v` with `αₓ(v) = 1` gives the factor `c = βₓ(v)`.
  obtain ⟨v, hv⟩ := RoughForm.exists_apply_ne_zero hα
  have hv₁ : α.val x ![(α.val x ![v])⁻¹ • v] = 1 := by
    rw [← degreeOneEquiv_coe_apply, map_smul, degreeOneEquiv_coe_apply, smul_eq_mul,
      inv_mul_cancel₀ hv]
  have hc := apply_eq_smul_of_kerDistribution_le hβα.self_of_nhds.ge hv₁
  set c := β.val x ![(α.val x ![v])⁻¹ • v]
  have hc₀ : c ≠ 0 := by
    intro h
    rw [h, zero_smul, ← kerDistribution_eq_top_iff, hβα.self_of_nhds,
      kerDistribution_eq_top_iff] at hc
    exact hα hc
  refine ⟨c, hc₀, hc, ?_⟩
  -- On `ker αₓ` both exterior derivatives are read off the Levi form of `ker α`.
  obtain ⟨U, hU, hxU, X, hX⟩ := exists_isDistributionFrameOn_kerDistribution (n := 1) hα
  have hlevi (γ : SmoothForm I M ℝ 1)
      (hγ : ∀ᶠ y in 𝓝 x, γ.kerDistribution y = α.kerDistribution y) (u w : α.kerDistribution x)
      {z : TangentSpace I x}
      (hz : (α.kerDistribution x).mkQ z = distributionLeviForm α.kerDistribution x u w) :
      γ.val x ![z] = mextDeriv γ.val x ![u, w] :=
    RoughForm.apply_eq_mextDeriv_of_mkQ_eq_distributionLeviForm hX (hU.mem_nhds hxU)
      (γ.mdifferentiableAt x) (hγ.mono fun y hy ↦ by rw [← kerDistribution_eq_ker, hy]) hz
  have hd (u w : TangentSpace I x) (hu : α.val x ![u] = 0) (hw : α.val x ![w] = 0) :
      mextDeriv β.val x ![u, w] = c * mextDeriv α.val x ![u, w] := by
    let u' : α.kerDistribution x := ⟨u, mem_kerDistribution.2 hu⟩
    let w' : α.kerDistribution x := ⟨w, mem_kerDistribution.2 hw⟩
    obtain ⟨z, hz⟩ := (α.kerDistribution x).mkQ_surjective
      (distributionLeviForm α.kerDistribution x u' w')
    rw [← hlevi β hβα u' w' hz, ← hlevi α (.of_forall fun _ ↦ rfl) u' w' hz, hc,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  simp only [coe_wedge, RoughForm.wedge_def, RoughForm.wedgeWith_apply', wedgePow_apply,
    mextDerivₗ_apply, hc]
  exact ContinuousAlternatingMap.pairedWedge_smul_wedgePow_of_eq_smul (E := TangentSpace I x)
    (α.val x) hd

end SmoothForm

namespace IsContactDistribution

variable [IsManifold I ∞ M] {D : Π x : M, Submodule ℝ (TangentSpace I x)}

/-- The volume form of a local defining form of a contact structure does not vanish. -/
private theorem wedge_wedgePow_apply_ne_zero (hD : IsContactDistribution I ∞ D)
    (hn : finrank ℝ E = 2 * n + 1) {α : SmoothForm I M ℝ 1} {x : M}
    (hα : ∀ᶠ y in 𝓝 x, α.kerDistribution y = D y) :
    (SmoothForm.wedge α ((mextDerivₗ I 1 α).wedgePow n)).val x ≠ 0 :=
  (SmoothForm.isContactFormAt_iff_wedge_wedgePow_apply_ne_zero hn α x).1
    (hD.isContactFormAt_of_eventually_kerDistribution_eq (by simp) hα)

/-- For odd `n`, two local defining forms of a contact structure near `x` select the same
orientation of `T_x M` through their volume forms. -/
private theorem topFormOrientationAt_eq (hD : IsContactDistribution I ∞ D)
    (hn : finrank ℝ E = 2 * n + 1) (hodd : Odd n) {α β : SmoothForm I M ℝ 1} {x : M}
    (hα : ∀ᶠ y in 𝓝 x, α.kerDistribution y = D y)
    (hβ : ∀ᶠ y in 𝓝 x, β.kerDistribution y = D y) :
    topFormOrientationAt (I := I) (hn.trans (Nat.add_comm _ _))
        (SmoothForm.wedge β ((mextDerivₗ I 1 β).wedgePow n)).val x =
      topFormOrientationAt (I := I) (hn.trans (Nat.add_comm _ _))
        (SmoothForm.wedge α ((mextDerivₗ I 1 α).wedgePow n)).val x := by
  have hα₀ : α.val x ≠ 0 := by
    rw [Ne, ← SmoothForm.kerDistribution_eq_top_iff, hα.self_of_nhds]
    exact hD.ne_top x
  obtain ⟨c, hc₀, -, hc⟩ := SmoothForm.exists_ne_zero_wedge_wedgePow_apply_eq_pow_smul (n := n)
    hα₀ (hβ.and hα |>.mono fun _ h ↦ h.1.trans h.2.symm)
  exact topFormOrientationAt_eq_of_apply_eq_smul _ (hodd.add_one.pow_pos hc₀) hc

variable [T2Space M]

/-- A chosen smooth one-form whose kernel is the contact structure near `x`. -/
private def localForm (hD : IsContactDistribution I ∞ D) (x : M) : SmoothForm I M ℝ 1 :=
  (hD.exists_smoothForm_eventually_kerDistribution_eq x).choose

private theorem eventually_kerDistribution_localForm (hD : IsContactDistribution I ∞ D) (x : M) :
    ∀ᶠ y in 𝓝 x, (hD.localForm x).kerDistribution y = D y :=
  (hD.exists_smoothForm_eventually_kerDistribution_eq x).choose_spec

/-- The orientation of `T_x M` selected by the volume form of the chosen local defining form. -/
private def volumeOrientationAt (hD : IsContactDistribution I ∞ D) (hn : finrank ℝ E = 2 * n + 1)
    (x : M) : _root_.Orientation ℝ (TangentSpace I x) (Fin (1 + 2 * n)) :=
  topFormOrientationAt (I := I) (hn.trans (Nat.add_comm _ _))
    (SmoothForm.wedge (hD.localForm x) ((mextDerivₗ I 1 (hD.localForm x)).wedgePow n)).val x

/-- For odd `n`, the orientations selected by local defining forms are locally constant. -/
private theorem eventually_mapOrientation_volumeOrientationAt_eq
    (hD : IsContactDistribution I ∞ D) (hn : finrank ℝ E = 2 * n + 1) (hodd : Odd n) (b : M) :
    ∀ᶠ x in 𝓝 b, ∀ hx : x ∈ (trivializationAt E (TangentSpace I) b).baseSet,
      (trivializationAt E (TangentSpace I) b).mapOrientation (Fin (1 + 2 * n)) hx
          (hD.volumeOrientationAt hn x) =
        (trivializationAt E (TangentSpace I) b).mapOrientation (Fin (1 + 2 * n))
          (FiberBundle.mem_baseSet_trivializationAt' b) (hD.volumeOrientationAt hn b) := by
  -- Near `b`, every point's chosen form may be replaced by the one chosen at `b`, whose volume
  -- form is continuous and does not vanish there.
  have hb := (hD.eventually_kerDistribution_localForm b).eventually_nhds
  filter_upwards [eventually_mapOrientation_topFormOrientationAt_eq (hn.trans (Nat.add_comm _ _))
      ((SmoothForm.wedge (hD.localForm b)
        ((mextDerivₗ I 1 (hD.localForm b)).wedgePow n)).isSmoothForm.of_le bot_le)
      (hb.mono fun _ hy ↦ hD.wedge_wedgePow_apply_ne_zero hn hy), hb] with y hy hyb hyy
  rw [volumeOrientationAt, hD.topFormOrientationAt_eq hn hodd hyb
    (hD.eventually_kerDistribution_localForm y)]
  exact hy hyy

/-- **The orientation of a contact structure in dimension `4 k + 3`.** For odd `n`, a contact
structure `D` on a Hausdorff manifold of dimension `2 n + 1` orients it: the tangent space at `x`
is oriented by the volume form `α ∧ (dα)ⁿ` of any one-form `α` with kernel `D` near `x`
(`TauCeti.IsContactDistribution.orientation_eq_orientationAt_volumeOrientation_iff`). No global
contact form or coorientation of `D` is needed. -/
def volumeOrientation (hD : IsContactDistribution I ∞ D) (hn : finrank ℝ E = 2 * n + 1)
    (hodd : Odd n) : Manifold.Orientation I M (Fin (1 + 2 * n)) :=
  Manifold.Orientation.ofVectorBundleOrientation
    (finBasisOfFinrankEq ℝ E (hn.trans (Nat.add_comm _ _))).orientation
    ((Fintype.card_fin _).trans (hn.trans (Nat.add_comm _ _)).symm)
    ⟨hD.volumeOrientationAt hn, hD.eventually_mapOrientation_volumeOrientationAt_eq hn hodd⟩

/-- The orientation of a contact structure at `x` is the one selected by the volume form
`α ∧ (dα)ⁿ` of any one-form `α` with kernel the contact structure near `x`. -/
theorem orientationAt_volumeOrientation (hD : IsContactDistribution I ∞ D)
    (hn : finrank ℝ E = 2 * n + 1) (hodd : Odd n) {α : SmoothForm I M ℝ 1} {x : M}
    (hα : ∀ᶠ y in 𝓝 x, α.kerDistribution y = D y) :
    Manifold.Orientation.orientationAt (hD.volumeOrientation hn hodd) x =
      topFormOrientationAt (I := I) (hn.trans (Nat.add_comm _ _))
        (SmoothForm.wedge α ((mextDerivₗ I 1 α).wedgePow n)).val x := by
  rw [volumeOrientation, Manifold.Orientation.orientationAt_ofVectorBundleOrientation,
    VectorBundleOrientation.coe_mk, volumeOrientationAt]
  exact hD.topFormOrientationAt_eq hn hodd hα (hD.eventually_kerDistribution_localForm x)

/-- A tangent basis is positive for the orientation of a contact structure exactly when the volume
form `α ∧ (dα)ⁿ` of a one-form `α` with kernel the contact structure near `x` is positive on it. -/
theorem orientation_eq_orientationAt_volumeOrientation_iff (hD : IsContactDistribution I ∞ D)
    (hn : finrank ℝ E = 2 * n + 1) (hodd : Odd n) {α : SmoothForm I M ℝ 1} {x : M}
    (hα : ∀ᶠ y in 𝓝 x, α.kerDistribution y = D y)
    (b : Basis (Fin (1 + 2 * n)) ℝ (TangentSpace I x)) :
    b.orientation = Manifold.Orientation.orientationAt (hD.volumeOrientation hn hodd) x ↔
      0 < (SmoothForm.wedge α ((mextDerivₗ I 1 α).wedgePow n)).val x b := by
  rw [hD.orientationAt_volumeOrientation hn hodd hα]
  exact topFormOrientationAt_spec _ x (hD.wedge_wedgePow_apply_ne_zero hn hα) b

/-- **The orientation of a contact structure is that of any global contact form defining it.**
For odd `n`, if `D` is the kernel of a contact form `α` on a manifold of dimension `2 n + 1`, then
the orientation of `D` is the orientation of `α ∧ (dα)ⁿ`. -/
theorem volumeOrientation_eq_of_kerDistribution_eq (hD : IsContactDistribution I ∞ D)
    (hn : finrank ℝ E = 2 * n + 1) (hodd : Odd n) {α : SmoothForm I M ℝ 1}
    (hα : α.IsContactForm) (h : α.kerDistribution = D) :
    hD.volumeOrientation hn hodd = hα.volumeOrientation hn := by
  ext x
  rw [hD.orientationAt_volumeOrientation hn hodd (.of_forall fun y ↦ congrFun h y),
    hα.orientationAt_volumeOrientation hn]

/-- **A contact manifold of dimension `4 k + 3` is orientable**, whether or not its contact
structure is the kernel of a global one-form. -/
theorem orientable (hD : IsContactDistribution I ∞ D) (hn : finrank ℝ E = 2 * n + 1)
    (hodd : Odd n) : Orientable I M :=
  ⟨⟨(hD.volumeOrientation hn hodd).reindex (finCongr (hn.trans (Nat.add_comm _ _)).symm)⟩⟩

end IsContactDistribution

end TauCeti

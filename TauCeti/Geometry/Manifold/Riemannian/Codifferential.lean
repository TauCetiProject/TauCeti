/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.HodgeStar
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.DeRham.CompactSupport
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.BoundarylessStokes
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.Squared
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz

/-!
# The codifferential of an oriented Riemannian manifold

On an oriented Riemannian manifold `M` of dimension `m`, the codifferential of smooth real forms
of degree `j = k + 1` is

`d* = (-1) ^ (m (j + 1) + 1) ⋆ d ⋆ : Ω^(k+1)(M) → Ω^k(M)`,

built from the Hodge star `TauCeti.SmoothForm.hodgeStar` and the exterior derivative. With this
sign it is the formal adjoint of `d` for the pointwise inner product of forms integrated against
the Riemannian volume form: on a boundaryless manifold, for smooth forms `α` of degree `k` and
`β` of degree `k + 1`, one of them compactly supported,

`∫_M ⟨dα, β⟩ vol = ∫_M ⟨α, d*β⟩ vol`.

The proof is Stokes' theorem for `α ∧ ⋆β`, whose exterior derivative is
`⟨dα, β⟩ vol - ⟨α, d*β⟩ vol` by the Leibniz rule, `α ∧ ⋆γ = ⟨α, γ⟩ vol` and the identity
`⋆d*β = (-1) ^ (k + 1) d⋆β`.

The codifferential does not depend on the orientation, since reversing it negates both stars,
it squares to zero, and it does not enlarge supports. The pairing `∫_M ⟨α, β⟩ vol` against which
`d*` is the adjoint of `d` is positive definite on compactly supported forms.

## Main definitions

* `TauCeti.SmoothForm.codifferential`: the codifferential `d* = (-1) ^ (m (k + 2) + 1) ⋆ d ⋆` of
  smooth `(k + 1)`-forms.

## Main results

* `TauCeti.SmoothForm.hodgeStar_codifferential`: `⋆d*β = (-1) ^ (k + 1) d⋆β`.
* `TauCeti.SmoothForm.codifferential_neg_orientation`: `d*` does not depend on the orientation.
* `TauCeti.SmoothForm.codifferential_codifferential`: `d* d* = 0`.
* `TauCeti.SmoothForm.mextDeriv_wedge_hodgeStar`: Green's formula
  `d (α ∧ ⋆β) = ⟨dα, β⟩ vol - ⟨α, d*β⟩ vol`.
* `TauCeti.SmoothForm.integralTopForm_inner_mextDeriv_eq_inner_codifferential`: `d*` is the
  formal adjoint of `d`,
  `∫_M ⟨dα, β⟩ vol = ∫_M ⟨α, d*β⟩ vol`.
* `TauCeti.SmoothForm.integralTopForm_inner_self_nonneg`,
  `TauCeti.SmoothForm.integralTopForm_inner_self_eq_zero_iff`: the `L²` norm `∫_M |α|² vol` is
  nonnegative, and for compactly supported `α` in positive dimension it vanishes only for
  `α = 0`.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), §6.1–6.2.
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {m k l : ℕ}

namespace SmoothForm

/-- The codifferential `d* = (-1) ^ (m (k + 2) + 1) ⋆ d ⋆` of smooth `(k + 1)`-forms on an
oriented Riemannian manifold of dimension `m = k + 1 + l`. For forms of degree `j = k + 1` the
sign is `(-1) ^ (m (j + 1) + 1)`, which makes `d*` the formal adjoint of the exterior derivative
(`TauCeti.SmoothForm.integralTopForm_inner_mextDeriv_eq_inner_codifferential`). -/
def codifferential (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m) :
    SmoothForm I M ℝ (k + 1) →ₗ[ℝ] SmoothForm I M ℝ k :=
  (-1 : ℝ) ^ (m * (k + 2) + 1) •
    hodgeStar o (show l + 1 + k = m by omega) ∘ₗ mextDerivₗ I l ∘ₗ hodgeStar o hkl

/-- The codifferential is `(-1) ^ (m (k + 2) + 1) ⋆ d ⋆`. -/
theorem codifferential_apply (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m)
    (hlk : l + 1 + k = m) (β : SmoothForm I M ℝ (k + 1)) :
    codifferential o hkl β =
      (-1 : ℝ) ^ (m * (k + 2) + 1) • hodgeStar o hlk (mextDerivₗ I l (hodgeStar o hkl β)) :=
  (rfl)

/-- The sign relating `⋆d*` to `d⋆`. -/
private theorem neg_one_pow_mul_neg_one_pow (hkl : k + 1 + l = m) :
    (-1 : ℝ) ^ (m * (k + 2) + 1) * (-1) ^ ((l + 1) * k) = (-1) ^ (k + 1) := by
  subst hkl
  rw [← pow_add]
  refine neg_one_pow_congr ?_
  simp only [Nat.even_add, Nat.even_mul, Nat.even_add_one]
  tauto

/-- **The Hodge star of the codifferential**: `⋆d*β = (-1) ^ (k + 1) d⋆β` for a
`(k + 1)`-form `β`. -/
theorem hodgeStar_codifferential (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m)
    (hkl' : k + (l + 1) = m) (β : SmoothForm I M ℝ (k + 1)) :
    hodgeStar o hkl' (codifferential o hkl β) =
      (-1 : ℝ) ^ (k + 1) • mextDerivₗ I l (hodgeStar o hkl β) := by
  rw [codifferential_apply o hkl (by omega : l + 1 + k = m), map_smul, hodgeStar_hodgeStar,
    smul_smul, neg_one_pow_mul_neg_one_pow hkl]

/-- The codifferential does not depend on the orientation: reversing it negates both Hodge
stars. -/
@[simp]
theorem codifferential_neg_orientation (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) : codifferential (-o) hkl = codifferential o hkl := by
  have hlk : l + 1 + k = m := by omega
  ext β : 1
  simp only [codifferential_apply _ hkl hlk, hodgeStar_neg_orientation, map_neg, neg_neg]

/-- **The codifferential squares to zero**: `d* d* β = 0`, since `⋆⋆` is a sign and
`d d = 0`. -/
@[simp]
theorem codifferential_codifferential {l' : ℕ} (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) (hkl' : k + 1 + 1 + l' = m) (β : SmoothForm I M ℝ (k + 1 + 1)) :
    codifferential o hkl (codifferential o hkl' β) = 0 := by
  obtain rfl : l = l' + 1 := by omega
  rw [codifferential_apply o hkl (by omega), codifferential_apply o hkl' (by omega), map_smul,
    map_smul, hodgeStar_hodgeStar, map_smul, map_smul,
    ← LinearMap.comp_apply (mextDerivₗ I (l' + 1)) (mextDerivₗ I l'), mextDerivₗ_comp_mextDerivₗ]
  simp

/-- The codifferential squares to zero as a linear map: `d* ∘ d* = 0`. -/
@[simp]
theorem codifferential_comp_codifferential {l' : ℕ} (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) (hkl' : k + 1 + 1 + l' = m) :
    codifferential o hkl ∘ₗ codifferential o hkl' = 0 :=
  LinearMap.ext (codifferential_codifferential o hkl hkl')

/-- The codifferential does not enlarge supports. -/
theorem tsupport_codifferential_subset (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) (β : SmoothForm I M ℝ (k + 1)) :
    _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) (codifferential o hkl β).1 ⊆
      _root_.tsupport (α := E [⋀^Fin (k + 1)]→L[ℝ] ℝ) β.1 := by
  rw [codifferential_apply o hkl (by omega : l + 1 + k = m), Submodule.coe_smul, coe_hodgeStar,
    mextDerivₗ_apply, coe_hodgeStar]
  refine (RoughForm.tsupport_smul_subset _ _).trans ?_
  refine (RoughForm.tsupport_hodgeStar_subset o _ _).trans ?_
  refine (RoughForm.tsupport_mextDeriv_subset _).trans ?_
  exact RoughForm.tsupport_hodgeStar_subset o hkl β.1

/-- **Green's formula for the codifferential**: for smooth forms `α` of degree `k` and `β` of
degree `k + 1` on an oriented Riemannian manifold of dimension `k + l + 1`,
`d (α ∧ ⋆β) = ⟨dα, β⟩ vol - ⟨α, d*β⟩ vol`, where `⟨·, ·⟩` is the pointwise inner product of forms
and `vol` the Riemannian volume form. -/
theorem mextDeriv_wedge_hodgeStar (o : Manifold.Orientation I M (Fin (k + l + 1)))
    (α : SmoothForm I M ℝ k) (β : SmoothForm I M ℝ (k + 1)) :
    mextDeriv (RoughForm.wedge α.1 (hodgeStar o (add_right_comm k 1 l) β).1) =
      (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1) ((mextDerivₗ I k α).1 x) (β.1 x) •
        riemannianVolumeForm o x) -
      fun x ↦ alternatingFormInner (TangentSpace I x) k (α.1 x)
        ((codifferential o (add_right_comm k 1 l) β).1 x) • riemannianVolumeForm o x := by
  have hkl' : k + (l + 1) = k + l + 1 := (add_assoc k l 1).symm
  -- `d⋆β = (-1) ^ (k + 1) ⋆d*β`, and the Leibniz sign is `(-1) ^ k`.
  have hdβ : mextDerivₗ I l (hodgeStar o (add_right_comm k 1 l) β) =
      (-1 : ℝ) ^ (k + 1) • hodgeStar o hkl' (codifferential o (add_right_comm k 1 l) β) := by
    rw [hodgeStar_codifferential o _ hkl', smul_smul, ← pow_add, ← two_mul, pow_mul,
      neg_one_sq, one_pow, one_smul]
  have hsign : (-1 : ℝ) ^ k * (-1) ^ (k + 1) = -1 := by
    rw [← pow_add]
    exact Odd.neg_one_pow ⟨k, by ring⟩
  rw [inner_smul_riemannianVolumeForm_eq_wedge_hodgeStar o hkl']
  funext x
  ext v
  rw [Pi.sub_apply, ContinuousAlternatingMap.sub_apply, cast_apply, coe_wedge,
    SmoothForm.mextDeriv_wedge_apply,
    ← mextDerivₗ_apply I l (hodgeStar o _ β), hdβ, Submodule.coe_smul,
    RoughForm.wedge_smul_right, ← mextDerivₗ_apply I k α]
  simp only [coe_hodgeStar, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
    RoughForm.wedge_def, RoughForm.wedgeWith_apply', ← ContinuousAlternatingMap.wedge_def,
    RoughForm.wedge_hodgeStar_apply, smul_eq_mul, Function.comp_def,
    finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
  linear_combination (alternatingFormInner (TangentSpace I x) k (α.1 x)
    ((codifferential o _ β).1 x) * riemannianVolumeForm o x v) * hsign

/-! ### The `L²` norm of forms -/

/-- The Hodge star of smooth forms preserves compact support. -/
theorem hodgeStar_mem_compactlySupportedForms (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) {α : SmoothForm I M ℝ k} (hα : α ∈ compactlySupportedForms I M k) :
    hodgeStar o hkl α ∈ compactlySupportedForms I M l := by
  rw [mem_compactlySupportedForms, coe_hodgeStar]
  exact ((mem_compactlySupportedForms I).1 hα).of_isClosed_subset (isClosed_tsupport _)
    (RoughForm.tsupport_hodgeStar_subset o hkl α.1)

/-- The density `⟨α, β⟩ vol` of two smooth `k`-forms on an oriented Riemannian manifold of
dimension `m = k + l` is a smooth top form. -/
theorem isSmoothForm_inner_smul_riemannianVolumeForm (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (α β : SmoothForm I M ℝ k) :
    IsSmoothForm I ∞ (fun x ↦ alternatingFormInner (TangentSpace I x) k (α.1 x) (β.1 x) •
      riemannianVolumeForm o x) := by
  rw [inner_smul_riemannianVolumeForm_eq_wedge_hodgeStar o hkl]
  exact isSmoothForm _

/-- The density `⟨α, β⟩ vol` of two smooth `k`-forms on an oriented Riemannian manifold of
dimension `m = k + l` is compactly supported when `α` or `β` is. -/
theorem isCompact_tsupport_inner_smul_riemannianVolumeForm
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) {α β : SmoothForm I M ℝ k}
    (h : α ∈ compactlySupportedForms I M k ∨ β ∈ compactlySupportedForms I M k) :
    IsCompact (_root_.tsupport (α := E [⋀^Fin m]→L[ℝ] ℝ)
      (fun x ↦ alternatingFormInner (TangentSpace I x) k (α.1 x) (β.1 x) •
        riemannianVolumeForm o x)) := by
  rw [inner_smul_riemannianVolumeForm_eq_wedge_hodgeStar o hkl, ← mem_compactlySupportedForms I,
    cast_mem_compactlySupportedForms_iff I hkl, mem_compactlySupportedForms, coe_wedge,
    coe_hodgeStar]
  rw [mem_compactlySupportedForms, mem_compactlySupportedForms] at h
  exact RoughForm.isCompact_tsupport_wedge_hodgeStar o hkl α.1 β.1 h

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The density `|α|² vol` takes nonnegative values on positively oriented tangent bases. -/
private theorem inner_self_smul_riemannianVolumeForm_apply_nonneg
    (o : Manifold.Orientation I M (Fin m)) (α : SmoothForm I M ℝ k) (x : M)
    (c : Module.Basis (Fin m) ℝ (TangentSpace I x)) (hc : c.orientation = o.orientationAt x) :
    0 ≤ (alternatingFormInner (TangentSpace I x) k (α.1 x) (α.1 x) •
      riemannianVolumeForm o x) c := by
  let := o.fact_finrank_tangentSpace x
  rw [ContinuousAlternatingMap.smul_apply, riemannianVolumeForm_apply]
  exact mul_nonneg (alternatingFormInner_self_nonneg _)
    (Orientation.volumeForm_apply_pos_iff.2 hc).le

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- **The `L²` norm of a form is nonnegative**: `0 ≤ ∫_M |α|² vol` on an oriented Riemannian
manifold of positive dimension, where `|α|²` is the pointwise inner product of `α` with itself. -/
theorem integralTopForm_inner_self_nonneg [NeZero m] (o : Manifold.Orientation I M (Fin m))
    (α : SmoothForm I M ℝ k) :
    0 ≤ integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k (α.1 x) (α.1 x) •
      riemannianVolumeForm o x) :=
  integralTopForm_nonneg o (inner_self_smul_riemannianVolumeForm_apply_nonneg o α)

/-- **The `L²` norm of forms is definite**: on an oriented Riemannian manifold of positive
dimension `m = k + l`, a compactly supported smooth `k`-form `α` with `∫_M |α|² vol = 0`
vanishes. -/
theorem integralTopForm_inner_self_eq_zero_iff [NeZero m] (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) {α : SmoothForm I M ℝ k} (hα : α ∈ compactlySupportedForms I M k) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k (α.1 x) (α.1 x) •
      riemannianVolumeForm o x) = 0 ↔ α = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  swap
  · simp only [h, ZeroMemClass.coe_zero, Pi.zero_apply, map_zero, zero_smul]
    exact integralTopForm_zero o
  by_contra hne
  obtain ⟨x, hx⟩ : ∃ x, α.1 x ≠ 0 := by
    by_contra! h'
    exact hne (Subtype.ext (funext h'))
  let := o.fact_finrank_tangentSpace x
  -- The density is positive on a positively oriented basis at a point where `α` is nonzero.
  let c := (Module.finBasisOfFinrankEq ℝ (TangentSpace I x) Fact.out).adjustToOrientation
    (o.orientationAt x)
  have hc : c.orientation = o.orientationAt x := Module.Basis.orientation_adjustToOrientation _ _
  have hpos : 0 < (alternatingFormInner (TangentSpace I x) k (α.1 x) (α.1 x) •
      riemannianVolumeForm o x) c := by
    rw [ContinuousAlternatingMap.smul_apply, riemannianVolumeForm_apply]
    exact mul_pos ((alternatingFormInner_self_nonneg _).lt_of_ne'
      (mt alternatingFormInner_self_eq_zero.1 hx)) (Orientation.volumeForm_apply_pos_iff.2 hc)
  exact (integralTopForm_pos o ((isSmoothForm_inner_smul_riemannianVolumeForm o hkl α α).of_le
    bot_le) (isCompact_tsupport_inner_smul_riemannianVolumeForm o hkl (.inl hα))
    (inner_self_smul_riemannianVolumeForm_apply_nonneg o α) ⟨x, c, hc, hpos⟩).ne' h

variable [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **The codifferential is the formal adjoint of the exterior derivative**: on an oriented
boundaryless Riemannian manifold, for smooth forms `α` of degree `k` and `β` of degree `k + 1`,
one of them compactly supported, `∫_M ⟨dα, β⟩ vol = ∫_M ⟨α, d*β⟩ vol`, where `⟨·, ·⟩` is the
pointwise inner product of forms and `vol` the Riemannian volume form. -/
theorem integralTopForm_inner_mextDeriv_eq_inner_codifferential
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m) (α : SmoothForm I M ℝ k)
    (β : SmoothForm I M ℝ (k + 1))
    (h : α ∈ compactlySupportedForms I M k ∨ β ∈ compactlySupportedForms I M (k + 1)) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1)
        ((mextDerivₗ I k α).1 x) (β.1 x) • riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        (α.1 x) ((codifferential o hkl β).1 x) • riemannianVolumeForm o x) := by
  obtain rfl : m = k + l + 1 := by omega
  rw [mem_compactlySupportedForms, mem_compactlySupportedForms] at h
  have hkl' : k + (l + 1) = k + l + 1 := (add_assoc k l 1).symm
  -- Both `α ∧ ⋆β` and `α ∧ ⋆d*β` are compactly supported.
  have hγ := RoughForm.isCompact_tsupport_wedge_hodgeStar o hkl α.1 β.1 h
  have hδ : wedge α (hodgeStar o hkl' (codifferential o hkl β)) ∈
      compactlySupportedForms I M (k + (l + 1)) := by
    rw [mem_compactlySupportedForms, coe_wedge, coe_hodgeStar]
    exact RoughForm.isCompact_tsupport_wedge_hodgeStar o hkl' α.1 _
      (h.imp_right fun hβ ↦ hβ.of_isClosed_subset (_root_.isClosed_tsupport _)
        (tsupport_codifferential_subset o hkl β))
  -- By Green's formula `⟨dα, β⟩ vol = ⟨α, d*β⟩ vol + d (α ∧ ⋆β)`, and Stokes kills the last term.
  have hdγ : IsSmoothForm I 0 (mextDeriv (RoughForm.wedge α.1 (hodgeStar o hkl β).1)) := by
    simpa only [mextDerivₗ_apply, coe_wedge] using
      (mextDerivₗ I (k + l) (wedge α (hodgeStar o hkl β))).isSmoothForm.of_le (by simp)
  rw [sub_eq_iff_eq_add.mp (mextDeriv_wedge_hodgeStar o α β).symm,
    integralTopForm_add o hdγ _ (RoughForm.isCompact_tsupport_mextDeriv (by rwa [coe_hodgeStar])),
    integralTopForm_mextDeriv_eq_zero o
      (by simpa only [coe_wedge] using (wedge α (hodgeStar o hkl β)).isSmoothForm.of_le (by simp))
      (by rwa [coe_hodgeStar]), zero_add]
  all_goals rw [inner_smul_riemannianVolumeForm_eq_wedge_hodgeStar o hkl']
  · exact (mem_compactlySupportedForms I).mp ((cast_mem_compactlySupportedForms_iff I hkl').mpr hδ)
  · exact (isSmoothForm _).of_le bot_le

end SmoothForm

end TauCeti

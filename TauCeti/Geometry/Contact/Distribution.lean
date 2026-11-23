/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Levi
public import TauCeti.Geometry.Symplectic.AlmostComplex
import Mathlib.Geometry.Manifold.BumpFunction
import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
import TauCeti.Geometry.Manifold.Distribution.Annihilator
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

/-!
# Contact distributions

A **contact structure** on a manifold `M` is a field of hyperplanes `ξ ⊂ TM` which is as far from
integrable as possible: its Levi form

`L_ξ : ξ × ξ → TM ⧸ ξ`, `L_ξ (U, V) = -[U, V] mod ξ`

(`TauCeti.distributionLeviForm`) is nondegenerate, in the sense that `u ↦ L_ξ (u, ·)` is an
isomorphism `ξ_x ≃ Hom(ξ_x, T_x M ⧸ ξ_x)` at every point. This is
`TauCeti.IsContactDistribution I n ξ`, for a `C^n` distribution of rank `dim M - 1`. The
definition involves only the hyperplane field: no contact form, coorientation or orientation of the
line `TM ⧸ ξ` is chosen, so it also covers contact structures which are not the kernel of any
global one-form.

Locally, a contact structure is the kernel of a contact form. Near every point, any `C^n`
hyperplane field is the kernel of a nowhere vanishing `C^n` one-form
(`TauCeti.IsContMDiffDistribution.exists_roughForm_ker_eq`), and for a contact structure every
such local defining form is a contact form at
every point where it defines `ξ` (`TauCeti.IsContactDistribution.exists_isContactFormAt`).
Conversely, a hyperplane field which near each point is the kernel of a one-form that is contact
at that point is a contact structure
(`TauCeti.isContactDistribution_iff_forall_exists_isContactFormAt`). Both directions rest on the
comparison `α_x (L_ξ (u, v)) = dα_x (u, v)` for a local defining form `α`
(`TauCeti.RoughForm.isContactFormAt_iff_bijective_distributionLeviForm`). For a global smooth
one-form `α`, the kernel `ker α` is a contact structure exactly when `α` is a contact form
(`TauCeti.SmoothForm.isContactForm_iff_isContactDistribution_kerDistribution`), and `dα` restricts
to a linear symplectic form on each contact hyperplane `ker α_x`
(`TauCeti.SmoothForm.IsContactForm.kerSymplecticForm`); for instance the standard distribution
`ker (dz - x dy)` on `ℝ³` is a contact structure
(`TauCeti.isContactDistribution_standardContactDistribution`, in
`TauCeti.Geometry.Contact.Standard`).

The Levi form of a contact structure is a nondegenerate alternating form with values in a line, so
the contact hyperplanes have even dimension and `M` has odd dimension `2 m + 1`
(`TauCeti.IsContactDistribution.odd_finrank`). In dimension at least three a contact structure is
not involutive (`TauCeti.IsContactDistribution.not_isInvolutiveDistribution`), so by Frobenius it
has no integral hypersurfaces.

## Main definitions

* `TauCeti.IsContactDistribution I n ξ`: `ξ` is a `C^n` hyperplane field with nondegenerate Levi
  form.
* `TauCeti.SmoothForm.IsContactForm.kerSymplecticForm`: the linear symplectic form on `ker α_x`
  induced by `dα_x`.

## Main results

* `TauCeti.IsContactDistribution.exists_isContactFormAt`: a contact structure is locally the kernel
  of a nowhere vanishing `C^n` one-form, which is a contact form at each point of its domain.
* `TauCeti.IsContactDistribution.exists_smoothForm_ker_eq_isContactFormAt`: on a Hausdorff manifold,
  a smooth contact structure is defined near each point by a smooth one-form on the whole manifold.
* `TauCeti.isContactDistribution_iff_forall_exists_isContactFormAt`: a `C^n` hyperplane field is a
  contact structure exactly when it is locally the kernel of one-forms that are contact.
* `TauCeti.IsContactDistribution.isContactFormAt_of_eventually_kerDistribution_eq`: a smooth
  one-form whose kernel is a contact structure near a point is a contact form at that point.
* `TauCeti.SmoothForm.isContactForm_iff_isContactDistribution_kerDistribution`: a smooth one-form
  is a contact form exactly when its kernel is a contact structure.
* `TauCeti.IsContactDistribution.even_finrank` and `TauCeti.IsContactDistribution.odd_finrank`:
  contact hyperplanes have even dimension, and contact manifolds odd dimension.
* `TauCeti.IsContactDistribution.not_isInvolutiveDistribution`: contact structures in dimension at
  least three are not involutive.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 1.1 (contact structures as maximally non-integrable hyperplane fields, and their
  local defining forms).
-/

public section

noncomputable section

open Set Filter Function Module Bundle
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] {n : ℕ∞ω} {D : Π x : M, Submodule ℝ (TangentSpace I x)}

variable (I n) in
/-- A distribution `D` on a finite-dimensional manifold is a **contact distribution**, or contact
structure, of class `C^n` when it is a `C^n` field of hyperplanes, of rank `dim E - 1`, whose Levi
form is nondegenerate: at every point `x`, the map `u ↦ L_D (u, ·)` is an isomorphism from `D x`
onto `Hom(D x, T_x M ⧸ D x)`. No defining one-form or coorientation is part of the data.

The model space `E` is required to be finite-dimensional: otherwise `finrank ℝ E - 1 = 0`, and the
zero distribution would satisfy every field without being a hyperplane field. -/
structure IsContactDistribution [FiniteDimensional ℝ E]
    (D : Π x : M, Submodule ℝ (TangentSpace I x)) : Prop where
  /-- A contact distribution is a `C^n` distribution of rank `dim E - 1`. -/
  isContMDiffDistribution : IsContMDiffDistribution I n (finrank ℝ E - 1) D
  /-- A contact distribution is a proper subspace at each point, hence a hyperplane. -/
  ne_top (x : M) : D x ≠ ⊤
  /-- The Levi form of a contact distribution is nondegenerate. -/
  bijective_distributionLeviForm (x : M) : Bijective (distributionLeviForm D x)

namespace IsContactDistribution

variable [FiniteDimensional ℝ E]

/-- A contact distribution is a hyperplane field: its rank is one less than the dimension of `M`. -/
theorem finrank_add_one (hD : IsContactDistribution I n D) (x : M) :
    finrank ℝ (D x) + 1 = finrank ℝ E := by
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have hk := hD.isContMDiffDistribution.finrank_eq x
  -- The tangent space at `x` is the model space `E`.
  have hT : finrank ℝ (TangentSpace I x) = finrank ℝ E := rfl
  -- On a zero-dimensional model space the only subspace would be `⊤`.
  have hE : finrank ℝ E ≠ 0 := fun h ↦ hD.ne_top x (Submodule.eq_top_of_finrank_eq (by omega))
  omega

/-- The contact line `T_x M ⧸ D x` of a contact distribution is one-dimensional. -/
theorem finrank_quotient (hD : IsContactDistribution I n D) (x : M) :
    finrank ℝ (TangentSpace I x ⧸ D x) = 1 := by
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have h := Submodule.finrank_quotient_add_finrank (D x)
  -- The tangent space at `x` is the model space `E`.
  have hT : finrank ℝ (TangentSpace I x) = finrank ℝ E := rfl
  have h' := hD.finrank_add_one x
  omega

/-- On a nonempty manifold, the rank `dim M - 1` of a contact structure and the rank `1` of its
contact line add up to the dimension of `M`. -/
theorem finrank_sub_one_add_one [Nonempty M] (hD : IsContactDistribution I n D) :
    finrank ℝ E - 1 + 1 = finrank ℝ E := by
  obtain ⟨x⟩ := ‹Nonempty M›
  have := hD.finrank_add_one x
  omega

/-- **Contact hyperplanes have even dimension**, since the Levi form is a nondegenerate alternating
form with values in a line. -/
theorem even_finrank (hD : IsContactDistribution I n D) (x : M) : Even (finrank ℝ (D x)) :=
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.IsAlt.even_finrank_of_injective (fun u ↦ distributionLeviForm_self u)
    (hD.bijective_distributionLeviForm x).injective (hD.finrank_quotient x)

/-- **A contact manifold has odd dimension.** -/
theorem odd_finrank [Nonempty M] (hD : IsContactDistribution I n D) : Odd (finrank ℝ E) := by
  obtain ⟨x⟩ := ‹Nonempty M›
  rw [← hD.finrank_add_one x]
  exact (hD.even_finrank x).add_one

/-- **A contact structure is not involutive** in dimension at least three: its Levi form, which
measures the failure of involutivity, is nondegenerate on nonzero hyperplanes. -/
theorem not_isInvolutiveDistribution [Nonempty M] (hD : IsContactDistribution I n D)
    (hE : 1 < finrank ℝ E) : ¬IsInvolutiveDistribution I D := by
  obtain ⟨x⟩ := ‹Nonempty M›
  intro hinv
  -- A bijective zero map has trivial domain, so the hyperplane `D x` would be zero.
  have hinj := (hD.bijective_distributionLeviForm x).injective
  rw [hinv.distributionLeviForm_eq_zero x] at hinj
  have : Subsingleton (D x) := ⟨fun u v ↦ hinj (by simp)⟩
  have := hD.finrank_add_one x
  rw [finrank_zero_of_subsingleton] at this
  omega

end IsContactDistribution

/-! ### Local defining forms -/

variable [FiniteDimensional ℝ E]

/-- **A contact structure is locally defined by contact forms.** Every point of a `C^n` contact
structure `D`, with `1 ≤ n`, has an open neighbourhood `U` on which `D` is the kernel of a one-form
`α` of class `C^n` on `U`; any such local defining form is a contact form at every point of `U`. -/
theorem IsContactDistribution.exists_isContactFormAt [IsManifold I (n + 1) M]
    (hD : IsContactDistribution I n D) (hn : 1 ≤ n) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ α : RoughForm I M ℝ 1,
      ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) n
        (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) U ∧
      ∀ y ∈ U, α.ker y = D y ∧ IsContactFormAt α y := by
  obtain ⟨U, hU, hxU, α, hα, hαD⟩ := hD.isContMDiffDistribution.exists_roughForm_ker_eq
    (hD.isContMDiffDistribution.finrank_eq x ▸ hD.finrank_add_one x) x
  refine ⟨U, hU, hxU, α, hα, fun y hy ↦ ⟨(hαD y hy).2, ?_⟩⟩
  obtain ⟨V, hV, hyV, X, hX⟩ := isContMDiffDistribution_iff.1 hD.isContMDiffDistribution y
  refine (RoughForm.isContactFormAt_iff_bijective_distributionLeviForm (hX.of_le hn)
    (hV.mem_nhds hyV) (((hα y hy).contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt
      (zero_lt_one.trans_le hn).ne') ?_).2 ⟨(hαD y hy).1, hD.bijective_distributionLeviForm y⟩
  exact eventually_of_mem (hU.mem_nhds hy) fun z hz ↦ (hαD z hz).2

/-- **A contact structure is defined near each point by a global contact form there.** Every point
`x` has an open neighbourhood `W` and a smooth one-form `α` on all of `M` such that, at every point
of `W`, the kernel of `α` is the contact hyperplane and `α` is a contact form. The form is a local
defining form cut off by a smooth bump function. -/
theorem IsContactDistribution.exists_smoothForm_ker_eq_isContactFormAt [IsManifold I ∞ M]
    [T2Space M] (hD : IsContactDistribution I ∞ D) (x : M) :
    ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ ∃ α : SmoothForm I M ℝ 1,
      ∀ y ∈ W, RoughForm.ker α.val y = D y ∧ IsContactFormAt α.val y := by
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  obtain ⟨U, hU, hxU, α, hα, hαξ⟩ := hD.exists_isContactFormAt (by simp) x
  obtain ⟨f, -, hfU⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.1
    (hU.mem_nhds hxU)
  obtain ⟨V, hVf, hV, hxV⟩ := mem_nhds_iff.1 f.eventuallyEq_one
  have hψ : IsSmoothForm I ∞ (fun y ↦ f y • α y : RoughForm I M ℝ 1) := by
    rw [isSmoothForm_def]
    exact f.contMDiff.contMDiffOn.smul_section_of_tsupport hU hfU hα
  refine ⟨V ∩ U, hV.inter hU, ⟨hxV, hxU⟩, ⟨_, hψ.mem_smoothBundleForms⟩, fun y hy ↦ ?_⟩
  -- On the open set `V`, where `f = 1`, the cut-off form is the local defining form.
  have hev : ∀ᶠ z in 𝓝 y, f z • α z = α z := by
    filter_upwards [hV.mem_nhds hy.1] with z hz
    rw [show f z = 1 from hVf hz, one_smul]
  have hval : f y • α y = α y := hev.self_of_nhds
  refine ⟨?_, (isContactFormAt_congr hval fun v _ w _ ↦ ?_).2 (hαξ y hy.2).2⟩
  · ext v
    simp only [RoughForm.mem_ker, hval, ← (hαξ y hy.2).1]
  · exact congrArg (fun A ↦ A ![v, w]) (mextDeriv_congr_of_eventuallyEq hev)

/-- **Contact structures are the hyperplane fields locally defined by contact forms.** A `C^n`
distribution `D` of rank `dim E - 1`, with `1 ≤ n`, is a contact structure exactly when near every
point `x` it is the kernel of some one-form, differentiable at `x`, which is a contact form at
`x`. -/
theorem isContactDistribution_iff_forall_exists_isContactFormAt [IsManifold I (n + 1) M]
    (hD : IsContMDiffDistribution I n (finrank ℝ E - 1) D) (hn : 1 ≤ n) :
    IsContactDistribution I n D ↔ ∀ x, ∃ α : RoughForm I M ℝ 1,
      MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ))
        (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) x ∧
      (∀ᶠ y in 𝓝 x, α.ker y = D y) ∧ IsContactFormAt α x := by
  refine ⟨fun h x ↦ ?_, fun h ↦ ⟨hD, fun x ↦ ?_, fun x ↦ ?_⟩⟩
  · obtain ⟨U, hU, hxU, α, hα, hαD⟩ := h.exists_isContactFormAt hn x
    exact ⟨α, ((hα x hxU).contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt
      (zero_lt_one.trans_le hn).ne', eventually_of_mem (hU.mem_nhds hxU) fun y hy ↦ (hαD y hy).1,
      (hαD x hxU).2⟩
  · obtain ⟨α, -, hαD, hα⟩ := h x
    rw [← hαD.self_of_nhds, Ne, RoughForm.ker_eq_top_iff]
    exact hα.ne_zero
  · obtain ⟨α, hαd, hαD, hα⟩ := h x
    obtain ⟨V, hV, hxV, X, hX⟩ := isContMDiffDistribution_iff.1 hD x
    exact ((RoughForm.isContactFormAt_iff_bijective_distributionLeviForm (hX.of_le hn)
      (hV.mem_nhds hxV) hαd hαD).1 hα).2

/-- **A smooth one-form defining a contact structure near a point is a contact form there.** If
the kernel of a smooth one-form `α` is the `C^n` contact structure `D` near `x`, with `1 ≤ n`, then
`α` is a contact form at `x`. -/
theorem IsContactDistribution.isContactFormAt_of_eventually_kerDistribution_eq
    (hD : IsContactDistribution I n D) (hn : 1 ≤ n) {α : SmoothForm I M ℝ 1} {x : M}
    (hαD : ∀ᶠ y in 𝓝 x, α.kerDistribution y = D y) : IsContactFormAt α.val x := by
  obtain ⟨V, hV, hxV, X, hX⟩ := isContMDiffDistribution_iff.1 hD.isContMDiffDistribution x
  refine (RoughForm.isContactFormAt_iff_bijective_distributionLeviForm (hX.of_le hn)
    (hV.mem_nhds hxV) (α.mdifferentiableAt x)
    (hαD.mono fun y hy ↦ (SmoothForm.kerDistribution_eq_ker α y).symm.trans hy)).2
    ⟨?_, hD.bijective_distributionLeviForm x⟩
  rw [Ne, ← RoughForm.ker_eq_top_iff, ← SmoothForm.kerDistribution_eq_ker, hαD.self_of_nhds]
  exact hD.ne_top x

/-! ### Kernels of contact forms -/

/-- **A smooth one-form is a contact form exactly when its kernel is a contact structure.** -/
theorem SmoothForm.isContactForm_iff_isContactDistribution_kerDistribution [ENat.LEInfty n]
    [IsManifold I (n + 1) M] {α : SmoothForm I M ℝ 1} :
    α.IsContactForm ↔ IsContactDistribution I n α.kerDistribution := by
  -- The kernel of `α` at `x` is all of `T_x M` exactly when `α_x = 0`.
  have htop (x : M) : α.kerDistribution x ≠ ⊤ ↔ α.val x ≠ 0 := by
    rw [SmoothForm.kerDistribution_eq_ker, Ne, RoughForm.ker_eq_top_iff]
  rw [isContactForm_iff_forall_bijective_distributionLeviForm]
  exact ⟨fun h ↦ ⟨isContMDiffDistribution_kerDistribution fun x ↦ (h x).1,
    fun x ↦ (htop x).2 (h x).1, fun x ↦ (h x).2⟩,
    fun h x ↦ ⟨(htop x).1 (h.ne_top x), h.bijective_distributionLeviForm x⟩⟩

/-- The kernel of a contact form is a contact structure. -/
theorem SmoothForm.IsContactForm.isContactDistribution_kerDistribution [ENat.LEInfty n]
    [IsManifold I (n + 1) M] {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) :
    IsContactDistribution I n α.kerDistribution :=
  isContactForm_iff_isContactDistribution_kerDistribution.1 hα

/-- **Global contact forms of a contact structure are its nowhere-vanishing defining forms.** A
smooth one-form is a contact form with kernel the contact structure `D` exactly when it vanishes
nowhere and has kernel `D`. -/
theorem IsContactDistribution.isContactForm_and_kerDistribution_eq_iff [ENat.LEInfty n]
    [IsManifold I (n + 1) M] (hD : IsContactDistribution I n D) {α : SmoothForm I M ℝ 1} :
    α.IsContactForm ∧ α.kerDistribution = D ↔ ∀ x, α.val x ≠ 0 ∧ RoughForm.ker α.val x = D x := by
  refine ⟨fun ⟨hα, hαD⟩ x ↦ ⟨hα.apply_ne_zero x, ?_⟩, fun h ↦ ?_⟩
  · rw [← SmoothForm.kerDistribution_eq_ker, hαD]
  · have hαD : α.kerDistribution = D :=
      funext fun x ↦ (SmoothForm.kerDistribution_eq_ker α x).trans (h x).2
    exact ⟨SmoothForm.isContactForm_iff_isContactDistribution_kerDistribution.2 (hαD ▸ hD), hαD⟩

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The linear symplectic form on the contact hyperplane `α.kerDistribution x` induced by `dα_x`:
`(v, w) ↦ dα_x(v, w)`. -/
def SmoothForm.IsContactForm.kerSymplecticForm {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm)
    (x : M) : SymplecticForm (α.kerDistribution x) :=
  let B : LinearMap.BilinForm ℝ (α.kerDistribution x) :=
    ((mextDerivₗ I 1 α).bilinFormAt x).domRestrict₁₂
      (α.kerDistribution x) (α.kerDistribution x)
  have hAlt : B.IsAlt := fun v ↦ by
    rw [LinearMap.domRestrict₁₂_apply]
    exact (SmoothForm.isAlt_bilinFormAt _ x).self_eq_zero v.val
  have hsep : B.SeparatingLeft := fun v hv ↦ Subtype.ext <|
    (SmoothForm.isContactForm_iff.1 hα x).2 v.val (SmoothForm.mem_kerDistribution.1 v.property)
      fun w hw ↦ by
        have h := hv ⟨w, SmoothForm.mem_kerDistribution.2 hw⟩
        rwa [LinearMap.domRestrict₁₂_apply, ← SmoothForm.mextDeriv_eq_bilinFormAt] at h
  { toBilinForm := B
    isAlt := hAlt
    nondegenerate := ⟨hsep, fun w hw ↦ hsep w fun v ↦ by
      rw [← hAlt.neg_eq v w, hw v, neg_zero]⟩ }

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Evaluating `kerSymplecticForm` on two vectors in `ker α_x` evaluates `dα_x` on them. -/
@[simp]
theorem SmoothForm.IsContactForm.kerSymplecticForm_apply {α : SmoothForm I M ℝ 1}
    (hα : α.IsContactForm) (x : M) (v w : α.kerDistribution x) :
    hα.kerSymplecticForm x v w = mextDeriv α.val x ![v.val, w.val] := by
  unfold SmoothForm.IsContactForm.kerSymplecticForm
  dsimp only
  rw [LinearMap.domRestrict₁₂_apply, ← SmoothForm.mextDeriv_eq_bilinFormAt]

end TauCeti

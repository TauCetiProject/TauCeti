/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Levi
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

Locally, a contact structure is the kernel of a contact form. Near every point, `ξ` is the kernel
of a nowhere vanishing `C^n` one-form, and every such local defining form is a contact form at
every point where it defines `ξ` (`TauCeti.IsContactDistribution.exists_isContactFormAt`).
Conversely, a hyperplane field which near each point is the kernel of a one-form that is contact
at that point is a contact structure
(`TauCeti.isContactDistribution_iff_forall_exists_isContactFormAt`). Both directions rest on the
comparison `α_x (L_ξ (u, v)) = dα_x (u, v)` for a local defining form `α`
(`TauCeti.RoughForm.isContactFormAt_iff_bijective_distributionLeviForm`). For a global smooth
one-form `α`, the kernel `ker α` is a contact structure exactly when `α` is a contact form
(`TauCeti.SmoothForm.isContactForm_iff_isContactDistribution_kerDistribution`); for instance the
standard distribution `ker (dz - x dy)` on `ℝ³` is a contact structure
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

## Main results

* `TauCeti.IsContactDistribution.exists_isContactFormAt`: a contact structure is locally the kernel
  of a nowhere vanishing `C^n` one-form, which is a contact form at each point of its domain.
* `TauCeti.isContactDistribution_iff_forall_exists_isContactFormAt`: a `C^n` hyperplane field is a
  contact structure exactly when it is locally the kernel of one-forms that are contact.
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

/-- The rank `dim E - 1` of a contact distribution is one less than the dimension of `M`. This is
the rank hypothesis of results stated for `C^n` hyperplane fields. -/
theorem finrank_sub_one_add_one (hD : IsContactDistribution I n D) (x : M) :
    finrank ℝ E - 1 + 1 = finrank ℝ E :=
  hD.isContMDiffDistribution.finrank_eq x ▸ hD.finrank_add_one x

/-- The contact line `T_x M ⧸ D x` of a contact distribution is one-dimensional. -/
theorem finrank_quotient (hD : IsContactDistribution I n D) (x : M) :
    finrank ℝ (TangentSpace I x ⧸ D x) = 1 := by
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have h := Submodule.finrank_quotient_add_finrank (D x)
  -- The tangent space at `x` is the model space `E`.
  have hT : finrank ℝ (TangentSpace I x) = finrank ℝ E := rfl
  have h' := hD.finrank_add_one x
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
    (hn : 1 ≤ n) (hE : 1 < finrank ℝ E) : ¬IsInvolutiveDistribution I D := by
  obtain ⟨x⟩ := ‹Nonempty M›
  rw [isInvolutiveDistribution_iff_distributionLeviForm_eq_zero hD.isContMDiffDistribution hn]
  intro h
  -- A bijective zero map has trivial domain, so the hyperplane `D x` would be zero.
  have hinj := (hD.bijective_distributionLeviForm x).injective
  rw [h x] at hinj
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
  obtain ⟨U, hU, hxU, α, hα, hαD⟩ :=
    hD.isContMDiffDistribution.exists_roughForm_ker_eq (hD.finrank_sub_one_add_one x) x
  refine ⟨U, hU, hxU, α, hα, fun y hy ↦ ⟨(hαD y hy).2, ?_⟩⟩
  obtain ⟨V, hV, hyV, X, hX⟩ := isContMDiffDistribution_iff.1 hD.isContMDiffDistribution y
  refine (RoughForm.isContactFormAt_iff_bijective_distributionLeviForm (hX.of_le hn)
    (hV.mem_nhds hyV) (((hα y hy).contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt
      (zero_lt_one.trans_le hn).ne') ?_).2 ⟨(hαD y hy).1, hD.bijective_distributionLeviForm y⟩
  exact eventually_of_mem (hU.mem_nhds hy) fun z hz ↦ (hαD z hz).2

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

/-! ### Kernels of contact forms -/

/-- **A smooth one-form is a contact form exactly when its kernel is a contact structure.** -/
theorem SmoothForm.isContactForm_iff_isContactDistribution_kerDistribution [ENat.LEInfty n]
    [IsManifold I (n + 1) M] {α : SmoothForm I M ℝ 1} :
    α.IsContactForm ↔ IsContactDistribution I n α.kerDistribution := by
  -- The kernel of `α` at `x` is all of `T_x M` exactly when `α_x = 0`.
  have htop (x : M) : α.kerDistribution x ≠ ⊤ ↔ α.1 x ≠ 0 := by
    have hker : α.kerDistribution x = RoughForm.ker α.1 x := by
      ext
      simp
    rw [hker, Ne, RoughForm.ker_eq_top_iff]
  rw [isContactForm_iff_forall_bijective_distributionLeviForm]
  exact ⟨fun h ↦ ⟨isContMDiffDistribution_kerDistribution fun x ↦ (h x).1,
    fun x ↦ (htop x).2 (h x).1, fun x ↦ (h x).2⟩,
    fun h x ↦ ⟨(htop x).1 (h.ne_top x), h.bijective_distributionLeviForm x⟩⟩

/-- The kernel of a contact form is a contact structure. -/
theorem SmoothForm.IsContactForm.isContactDistribution_kerDistribution [ENat.LEInfty n]
    [IsManifold I (n + 1) M] {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) :
    IsContactDistribution I n α.kerDistribution :=
  isContactForm_iff_isContactDistribution_kerDistribution.1 hα

end TauCeti

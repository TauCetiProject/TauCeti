/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Resolvent.Unbounded
public import TauCeti.LinearAlgebra.LinearPMap.RestrictScalars

/-!
# Resolvents and restriction of scalars

An unbounded operator `A : X →ₗ.[𝕜'] X` over a normed algebra `𝕜'` can also be read over a
smaller field `𝕜`, as `A.restrictScalars 𝕜`. This file shows that the two resolvent notions
agree at the points of `𝕜`: for `mu : 𝕜`,

`mu ∈ resolventSet (A.restrictScalars 𝕜) ↔ algebraMap 𝕜 𝕜' mu ∈ resolventSet A`,

and the resolvents themselves correspond under `ContinuousLinearMap.restrictScalars`.

Only the forward direction has content. A bounded `𝕜`-linear inverse `R` of `mu • I - A` is
automatically `𝕜'`-homogeneous: `z • R y` and `R (z • y)` have the same image under
`mu • I - A`, because `A` is `𝕜'`-linear, so they agree.

This is what lets a real-variable theorem about an operator on a complex Banach space — such as
the Laplace-transform resolvent of a C₀-semigroup, which is built over `ℝ` — be read as a
statement about the genuinely complex resolvent set.

## Main results

* `TauCeti.LinearPMap.IsResolventAt.restrictScalars`: restricting scalars in an inverse of
  `lambda • I - A`.
* `TauCeti.LinearPMap.map_smul_of_isResolventAt_restrictScalars`: a bounded inverse over `𝕜` is
  `𝕜'`-homogeneous.
* `TauCeti.LinearPMap.exists_isResolventAt_of_isResolventAt_restrictScalars`: it therefore comes
  from an inverse over `𝕜'`.
* `TauCeti.LinearPMap.mem_resolventSet_restrictScalars_iff`: the resolvent sets agree at the
  points of `𝕜`.
* `TauCeti.LinearPMap.restrictScalars_resolvent`: the resolvents agree there.
-/

public section

noncomputable section

namespace TauCeti.LinearPMap

variable {𝕜 𝕜' X : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedSpace 𝕜' X]
  [IsScalarTower 𝕜 𝕜' X] {A : X →ₗ.[𝕜'] X} {mu : 𝕜} {R : X →L[𝕜'] X} {R₀ : X →L[𝕜] X}

/-- An inverse of `algebraMap 𝕜 𝕜' mu • I - A` restricts to an inverse of `mu • I - A` for the
restriction of scalars. -/
theorem IsResolventAt.restrictScalars (h : IsResolventAt A (algebraMap 𝕜 𝕜' mu) R) :
    IsResolventAt (A.restrictScalars 𝕜) mu (R.restrictScalars 𝕜) where
  mem_domain y := by
    simp only [ContinuousLinearMap.coe_restrictScalars']
    exact (A.mem_restrictScalars_domain 𝕜).mpr (h.mem_domain y)
  smul_sub_apply y := by
    simp only [ContinuousLinearMap.coe_restrictScalars', LinearPMap.restrictScalars_apply,
      ← algebraMap_smul 𝕜' mu]
    exact h.smul_sub_apply y
  apply_smul_sub x := by
    simp only [ContinuousLinearMap.coe_restrictScalars', LinearPMap.restrictScalars_apply,
      ← algebraMap_smul 𝕜' mu]
    exact h.apply_smul_sub ⟨(x : X), (A.mem_restrictScalars_domain 𝕜).mp x.property⟩

/-- A bounded `𝕜`-linear inverse of `mu • I - A` is homogeneous for the larger field `𝕜'`: it is
the inverse of a `𝕜'`-linear bijection. -/
theorem map_smul_of_isResolventAt_restrictScalars
    (h : IsResolventAt (A.restrictScalars 𝕜) mu R₀) (z : 𝕜') (y : X) :
    R₀ (z • y) = z • R₀ y := by
  have hmem : ∀ w : X, R₀ w ∈ A.domain := fun w =>
    (A.mem_restrictScalars_domain 𝕜).mp (h.mem_domain w)
  have hsmul : z • R₀ y ∈ A.domain := A.domain.smul_mem z (hmem y)
  have hinv : algebraMap 𝕜 𝕜' mu • R₀ y - A ⟨R₀ y, hmem y⟩ = y := by
    have := h.smul_sub_apply y
    simpa only [LinearPMap.restrictScalars_apply, ← algebraMap_smul 𝕜' mu] using this
  have hkey : algebraMap 𝕜 𝕜' mu • (z • R₀ y) - A ⟨z • R₀ y, hsmul⟩ = z • y := by
    have hA : A ⟨z • R₀ y, hsmul⟩ = z • A ⟨R₀ y, hmem y⟩ := A.map_smul z ⟨R₀ y, hmem y⟩
    rw [hA, smul_comm, ← smul_sub, hinv]
  have hback := h.apply_smul_sub ⟨z • R₀ y, (A.mem_restrictScalars_domain 𝕜).mpr hsmul⟩
  simp only [LinearPMap.restrictScalars_apply, ← algebraMap_smul 𝕜' mu] at hback
  rw [hkey] at hback
  exact hback

/-- A bounded inverse of `mu • I - A` over the smaller field is the restriction of scalars of a
bounded inverse over the larger one. -/
theorem exists_isResolventAt_of_isResolventAt_restrictScalars
    (h : IsResolventAt (A.restrictScalars 𝕜) mu R₀) :
    ∃ R : X →L[𝕜'] X, R.restrictScalars 𝕜 = R₀ ∧
      IsResolventAt A (algebraMap 𝕜 𝕜' mu) R := by
  refine ⟨{ toFun := R₀
            map_add' := R₀.map_add
            map_smul' := map_smul_of_isResolventAt_restrictScalars h
            cont := R₀.continuous }, ContinuousLinearMap.ext fun _ => rfl, ?_⟩
  have hmem : ∀ y : X, R₀ y ∈ A.domain := fun y =>
    (A.mem_restrictScalars_domain 𝕜).mp (h.mem_domain y)
  have hright : ∀ y : X, algebraMap 𝕜 𝕜' mu • R₀ y - A ⟨R₀ y, hmem y⟩ = y := fun y => by
    have hy := h.smul_sub_apply y
    simpa only [LinearPMap.restrictScalars_apply, ← algebraMap_smul 𝕜' mu] using hy
  have hleft : ∀ x : A.domain, R₀ (algebraMap 𝕜 𝕜' mu • (x : X) - A x) = (x : X) := fun x => by
    have hx := h.apply_smul_sub ⟨(x : X), (A.mem_restrictScalars_domain 𝕜).mpr x.property⟩
    simpa only [LinearPMap.restrictScalars_apply, ← algebraMap_smul 𝕜' mu] using hx
  exact { mem_domain := hmem, smul_sub_apply := hright, apply_smul_sub := hleft }

/-- The resolvent sets of an operator and of its restriction of scalars agree at the points of the
smaller field. -/
@[simp]
theorem mem_resolventSet_restrictScalars_iff :
    mu ∈ resolventSet (A.restrictScalars 𝕜) ↔ algebraMap 𝕜 𝕜' mu ∈ resolventSet A := by
  rw [mem_resolventSet_iff, mem_resolventSet_iff]
  constructor
  · rintro ⟨R₀, hR₀⟩
    obtain ⟨R, -, hR⟩ := exists_isResolventAt_of_isResolventAt_restrictScalars hR₀
    exact ⟨R, hR⟩
  · rintro ⟨R, hR⟩
    exact ⟨R.restrictScalars 𝕜, hR.restrictScalars⟩

/-- The resolvent of the restriction of scalars is the restriction of scalars of the resolvent. -/
@[simp]
theorem restrictScalars_resolvent (h : mu ∈ resolventSet (A.restrictScalars 𝕜)) :
    (resolvent A (algebraMap 𝕜 𝕜' mu)).restrictScalars 𝕜 = resolvent (A.restrictScalars 𝕜) mu :=
  (resolvent_eq_of_isResolventAt
    (IsResolventAt.restrictScalars
      (isResolventAt_resolvent (mem_resolventSet_restrictScalars_iff.mp h)))).symm

end TauCeti.LinearPMap

end

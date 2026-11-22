/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.VonNeumannAlgebra.Polar
public import TauCeti.Analysis.VonNeumannAlgebra.Projection.Basic
import TauCeti.Analysis.InnerProductSpace.Projection.Basic

/-!
# Murray–von Neumann equivalence and Kaplansky's parallelogram law

We define Murray–von Neumann equivalence `VonNeumannAlgebra.ProjectionEquivalent M p q` of
projections in a concrete von Neumann algebra `M`, prove that it is an equivalence relation on star
projections in `M` preserving central supports, show that the initial and final projections of any
operator in `M` are equivalent via its polar factor
(`VonNeumannAlgebra.projectionEquivalent_orthogonal_ker_topologicalClosure_range`), and establish
**Kaplansky's parallelogram law** (`VonNeumannAlgebra.parallelogram_projectionEquivalent`):
`ProjectionEquivalent M ((p ⊔ q : M.Projection) - p) (q - (p ⊓ q : M.Projection))`.

## Main declarations

* `VonNeumannAlgebra.ProjectionEquivalent`, `VonNeumannAlgebra.projectionEquivalent_iff`,
  `VonNeumannAlgebra.ProjectionEquivalent.of_isPartialIsometry`,
  `VonNeumannAlgebra.ProjectionEquivalent.exists_isPartialIsometry`: Murray–von Neumann equivalence
  of projections in `M`, witnessed by a partial isometry in `M`.
* `VonNeumannAlgebra.ProjectionEquivalent.refl`, `VonNeumannAlgebra.ProjectionEquivalent.symm`,
  `VonNeumannAlgebra.ProjectionEquivalent.trans`, `VonNeumannAlgebra.ProjectionEquivalent.add`,
  `VonNeumannAlgebra.ProjectionEquivalent.centralSupport_eq`: equivalence-relation properties,
  orthogonal additivity, and central-support invariance.
* `VonNeumannAlgebra.projectionEquivalent_orthogonal_ker_topologicalClosure_range`: equivalence of
  initial and final projections via `x.polarFactor`.
* `VonNeumannAlgebra.parallelogram_projectionEquivalent`: Kaplansky's parallelogram law.

## References

* R. V. Kadison, J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras I*,
  Proposition 6.1.8 and Theorem 6.1.7.
* M. Takesaki, *Theory of Operator Algebras I*, Proposition V.1.6.
-/

public section

open scoped InnerProduct

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Murray–von Neumann equivalence `p ∼ q` in `M`, oriented from initial to final projection:
some `v ∈ M` has `star v * v = p` and `v * star v = q`. -/
def ProjectionEquivalent (M : VonNeumannAlgebra H) (p q : H →L[ℂ] H) : Prop :=
  IsStarProjection p ∧ IsStarProjection q ∧ p ∈ M ∧ q ∈ M ∧
  ∃ v : H →L[ℂ] H, v ∈ M ∧ star v * v = p ∧ v * star v = q

namespace ProjectionEquivalent

variable {M : VonNeumannAlgebra H} {p q r : H →L[ℂ] H}

/-- Introduce Murray–von Neumann equivalence from a partial isometry `v ∈ M` whose initial and
final projections are `p` and `q`. -/
theorem of_isPartialIsometry {v : H →L[ℂ] H} (hvM : v ∈ M) (hv : v.IsPartialIsometry)
    (hvp : star v * v = p) (hvq : v * star v = q) : ProjectionEquivalent M p q := by
  have hp : IsStarProjection p := by
    rw [← hvp, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
      hv.adjoint_comp_self_eq_starProjection]
    exact isStarProjection_starProjection
  have hq : IsStarProjection q := by
    rw [← hvq, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
      hv.comp_adjoint_eq_starProjection]
    exact isStarProjection_starProjection
  refine ⟨hp, hq, hvp ▸ mul_mem (star_mem hvM) hvM, hvq ▸ mul_mem hvM (star_mem hvM),
    v, hvM, hvp, hvq⟩

theorem isStarProjection_left (h : ProjectionEquivalent M p q) : IsStarProjection p :=
  h.1

theorem isStarProjection_right (h : ProjectionEquivalent M p q) : IsStarProjection q :=
  h.2.1

theorem mem_left (h : ProjectionEquivalent M p q) : p ∈ M :=
  h.2.2.1

theorem mem_right (h : ProjectionEquivalent M p q) : q ∈ M :=
  h.2.2.2.1

/-- Recover an implementing operator `v ∈ M` for a Murray–von Neumann equivalence
`ProjectionEquivalent M p q`. -/
theorem exists_mem (h : ProjectionEquivalent M p q) :
    ∃ v : H →L[ℂ] H, v ∈ M ∧ star v * v = p ∧ v * star v = q :=
  h.2.2.2.2

/-- Recover an implementing partial isometry `v ∈ M` for a Murray–von Neumann equivalence
`ProjectionEquivalent M p q`. -/
theorem exists_isPartialIsometry (h : ProjectionEquivalent M p q) :
    ∃ v : H →L[ℂ] H, v ∈ M ∧ v.IsPartialIsometry ∧ star v * v = p ∧ v * star v = q := by
  obtain ⟨hp, -, -, -, v, hvM, hvp, hvq⟩ := h
  refine ⟨v, hvM, ?_, hvp, hvq⟩
  rwa [ContinuousLinearMap.isPartialIsometry_iff_isStarProjection_adjoint_comp_self,
    ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.mul_def, hvp]

private theorem witness_mul_left_eq_self {p q v : H →L[ℂ] H} (hp : IsStarProjection p)
    (hvp : star v * v = p) (hvq : v * star v = q) : q * v = v := by
  have hv_pi : v.IsPartialIsometry := by
    rw [ContinuousLinearMap.isPartialIsometry_iff_isStarProjection_adjoint_comp_self,
      ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.mul_def, hvp]
    exact hp
  rw [← hvq, ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.star_eq_adjoint]
  exact hv_pi.comp_adjoint_comp

private theorem witness_mul_right_eq_self {p q v : H →L[ℂ] H} (hp : IsStarProjection p)
    (hvp : star v * v = p) (hvq : v * star v = q) : v * p = v := by
  calc v * p
    _ = (v * star v) * v := by rw [← hvp, mul_assoc]
    _ = v := by rw [hvq, witness_mul_left_eq_self hp hvp hvq]

/-- Reflexivity of Murray–von Neumann equivalence on star projections in `M`. -/
theorem refl (hp : IsStarProjection p) (hpM : p ∈ M) : ProjectionEquivalent M p p :=
  ⟨hp, hp, hpM, hpM, p, hpM,
    by rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq],
    by rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]⟩

/-- Symmetry of Murray–von Neumann equivalence. -/
theorem symm (h : ProjectionEquivalent M p q) : ProjectionEquivalent M q p := by
  obtain ⟨hp, hq, hpM, hqM, v, hvM, hvp, hvq⟩ := h
  exact ⟨hq, hp, hqM, hpM, star v, star_mem hvM,
    by rwa [star_star], by rwa [star_star]⟩

/-- Transitivity of Murray–von Neumann equivalence. -/
theorem trans (hpq : ProjectionEquivalent M p q) (hqr : ProjectionEquivalent M q r) :
    ProjectionEquivalent M p r := by
  obtain ⟨hp, -, hpM, -, v, hvM, hvp, hvq⟩ := hpq
  obtain ⟨-, hr, -, hrM, w, hwM, hwq, hwr⟩ := hqr
  refine ⟨hp, hr, hpM, hrM, w * v, mul_mem hwM hvM, ?_, ?_⟩
  · calc star (w * v) * (w * v)
      _ = star v * (star w * w) * v := by simp only [star_mul, mul_assoc]
      _ = star v * (v * star v) * v := by rw [hwq, ← hvq]
      _ = (star v * v) * (star v * v) := by simp only [mul_assoc]
      _ = p := by rw [hvp, hp.isIdempotentElem.eq]
  · calc w * v * star (w * v)
      _ = w * (v * star v) * star w := by simp only [star_mul, mul_assoc]
      _ = w * (star w * w) * star w := by rw [hvq, ← hwq]
      _ = (w * star w) * (w * star w) := by simp only [mul_assoc]
      _ = r := by rw [hwr, hr.isIdempotentElem.eq]

/-- Equivalent projections vanish simultaneously. -/
theorem eq_zero_iff (h : ProjectionEquivalent M p q) : p = 0 ↔ q = 0 := by
  suffices key : ∀ {e₁ e₂ : H →L[ℂ] H}, ProjectionEquivalent M e₁ e₂ → e₁ = 0 → e₂ = 0
    from ⟨key h, key h.symm⟩
  rintro e₁ e₂ ⟨-, -, -, -, v, -, hv₁, hv₂⟩ rfl
  have hv₀ : v = 0 := by
    rwa [star_mul_self_eq_zero] at hv₁
  rw [← hv₂, hv₀, zero_mul]

/-- Orthogonal sums of pairwise Murray–von Neumann equivalent projections in `M` are equivalent. -/
theorem add {p₁ p₂ q₁ q₂ : H →L[ℂ] H} (hp₁₂ : p₁ * p₂ = 0) (hq₁₂ : q₁ * q₂ = 0)
    (h₁ : ProjectionEquivalent M p₁ q₁) (h₂ : ProjectionEquivalent M p₂ q₂) :
    ProjectionEquivalent M (p₁ + p₂) (q₁ + q₂) := by
  obtain ⟨hp₁, hq₁, hp₁M, hq₁M, v₁, hv₁M, hv₁p, hv₁q⟩ := h₁
  obtain ⟨hp₂, hq₂, hp₂M, hq₂M, v₂, hv₂M, hv₂p, hv₂q⟩ := h₂
  have hqv₁ : q₁ * v₁ = v₁ := witness_mul_left_eq_self hp₁ hv₁p hv₁q
  have hqv₂ : q₂ * v₂ = v₂ := witness_mul_left_eq_self hp₂ hv₂p hv₂q
  have hv₁p_r : v₁ * p₁ = v₁ := witness_mul_right_eq_self hp₁ hv₁p hv₁q
  have hv₂p_r : v₂ * p₂ = v₂ := witness_mul_right_eq_self hp₂ hv₂p hv₂q
  have hcross₁ : star v₁ * v₂ = 0 := by
    calc star v₁ * v₂
      _ = star (q₁ * v₁) * (q₂ * v₂) := by rw [hqv₁, hqv₂]
      _ = star v₁ * (q₁ * q₂) * v₂ := by
        simp only [star_mul, hq₁.isSelfAdjoint.star_eq, mul_assoc]
      _ = 0 := by rw [hq₁₂, mul_zero, zero_mul]
  have hcross₂ : star v₂ * v₁ = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hcross₁
  have hcross₃ : v₁ * star v₂ = 0 := by
    calc v₁ * star v₂
      _ = (v₁ * p₁) * star (v₂ * p₂) := by rw [hv₁p_r, hv₂p_r]
      _ = v₁ * (p₁ * p₂) * star v₂ := by
        simp only [star_mul, hp₂.isSelfAdjoint.star_eq, mul_assoc]
      _ = 0 := by rw [hp₁₂, mul_zero, zero_mul]
  have hcross₄ : v₂ * star v₁ = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hcross₃
  refine ⟨hp₁.add hp₂ hp₁₂, hq₁.add hq₂ hq₁₂, add_mem hp₁M hp₂M, add_mem hq₁M hq₂M,
    v₁ + v₂, add_mem hv₁M hv₂M, ?_, ?_⟩
  · simp only [star_add, add_mul, mul_add, hv₁p, hv₂p, hcross₁, hcross₂, add_zero, zero_add]
  · simp only [star_add, add_mul, mul_add, hv₁q, hv₂q, hcross₃, hcross₄, add_zero, zero_add]

/-- Equivalent projections in `M` have the same central support. -/
theorem centralSupport_eq (h : ProjectionEquivalent M p q) :
    M.centralSupport p = M.centralSupport q := by
  suffices key : ∀ {e₁ e₂ : H →L[ℂ] H},
      ProjectionEquivalent M e₁ e₂ → M.centralSupportProjection e₁ ≤ M.centralSupportProjection e₂
    from by
      simpa only [coe_centralSupportProjection] using
        congrArg Projection.val (le_antisymm (key h) (key h.symm))
  intro e₁ e₂ ⟨he₁, _, _, _, v, hvM, hv₁, hv₂⟩
  rw [centralSupportProjection_le_iff, coe_centralSupportProjection]
  set z := M.centralSupport e₂
  have hqv : e₂ * v = v := witness_mul_left_eq_self he₁ hv₁ hv₂
  have hzv : z * star v = star v * z :=
    (mem_commutant_iff.1 (M.centralSupport_mem_commutant e₂) (star v) (star_mem hvM)).symm
  calc z * e₁
    _ = (z * star v) * v := by rw [← hv₁, mul_assoc]
    _ = star v * (z * (e₂ * v)) := by rw [hzv, hqv, mul_assoc]
    _ = star v * ((z * e₂) * v) := by rw [mul_assoc]
    _ = star v * (e₂ * v) := by rw [M.centralSupport_mul_self e₂]
    _ = e₁ := by rw [hqv, hv₁]

end ProjectionEquivalent

/-- Characterization of Murray–von Neumann equivalence `VonNeumannAlgebra.ProjectionEquivalent` in
terms of an implementing partial isometry in `M`. -/
theorem projectionEquivalent_iff {M : VonNeumannAlgebra H} {p q : H →L[ℂ] H} :
    ProjectionEquivalent M p q ↔
      ∃ v : H →L[ℂ] H, v ∈ M ∧ v.IsPartialIsometry ∧ star v * v = p ∧ v * star v = q :=
  ⟨ProjectionEquivalent.exists_isPartialIsometry,
    fun ⟨_, hvM, hv, hvp, hvq⟩ => ProjectionEquivalent.of_isPartialIsometry hvM hv hvp hvq⟩

/-- For any operator `x ∈ M`, its initial projection `x.kerᗮ.starProjection` and its final
projection `x.range.topologicalClosure.starProjection` are Murray–von Neumann equivalent in `M`,
witnessed by `x.polarFactor`. -/
theorem projectionEquivalent_orthogonal_ker_topologicalClosure_range {M : VonNeumannAlgebra H}
    {x : H →L[ℂ] H} (hx : x ∈ M) :
    ProjectionEquivalent M x.kerᗮ.starProjection x.range.topologicalClosure.starProjection := by
  refine ProjectionEquivalent.of_isPartialIsometry (polarFactor_mem hx)
    x.isPartialIsometry_polarFactor ?_ ?_
  · rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
      x.adjoint_polarFactor_comp_polarFactor]
  · rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
      x.polarFactor_comp_adjoint_polarFactor]

/-- **Kaplansky's parallelogram law.** For any two projections `p, q : M.Projection` in a von
Neumann algebra `M`, `(p ⊔ q) - p` and `q - (p ⊓ q)` are Murray–von Neumann equivalent in `M`. -/
theorem parallelogram_projectionEquivalent {M : VonNeumannAlgebra H} (p q : M.Projection) :
    ProjectionEquivalent M ((p ⊔ q : M.Projection) - p) (q - (p ⊓ q : M.Projection)) := by
  set x : H →L[ℂ] H := (1 - (p : H →L[ℂ] H)) * q
  have hx : x ∈ M := mul_mem (sub_mem (one_mem M) p.coe_mem) q.coe_mem
  have hinit : x.kerᗮ.starProjection = (q : H →L[ℂ] H) - (p ⊓ q : M.Projection) := by
    have : CompleteSpace ↥((p : H →L[ℂ] H).range ⊓ (q : H →L[ℂ] H).range) :=
      ((ContinuousLinearMap.IsIdempotentElem.isClosed_range
        p.isStarProjection.isIdempotentElem).inter
        (ContinuousLinearMap.IsIdempotentElem.isClosed_range
          q.isStarProjection.isIdempotentElem)).isComplete.completeSpace_coe
    calc x.kerᗮ.starProjection
      _ = ((1 - (p : H →L[ℂ] H).range.starProjection) *
          (q : H →L[ℂ] H).range.starProjection).kerᗮ.starProjection :=
        Submodule.starProjection_inj.2
          (by dsimp only [x]; rw [p.starProjection_range, q.starProjection_range])
      _ = (q : H →L[ℂ] H) - (p ⊓ q : M.Projection) := by
        rw [Submodule.starProjection_orthogonal_ker_one_sub_mul, q.starProjection_range,
          Projection.coe_inf]
        simp only [Projection.toSubmodule_closedRange, ClosedSubmodule.toSubmodule_inf]
  -- Pass to complements `qᶜ, pᶜ` via `star x = (1 - qᶜ) * pᶜ` and De Morgan's law.
  have hstar_x : star x = (1 - ((qᶜ : M.Projection) : H →L[ℂ] H)) * (pᶜ : M.Projection) := by
    simp only [x, star_mul, star_sub, star_one, Projection.star_coe, Projection.coe_compl,
      sub_sub_cancel]
  have hfinal : x.range.topologicalClosure.starProjection =
      (p ⊔ q : M.Projection) - (p : H →L[ℂ] H) := by
    have : CompleteSpace ↥(((qᶜ : M.Projection) : H →L[ℂ] H).range ⊓
        ((pᶜ : M.Projection) : H →L[ℂ] H).range) :=
      ((ContinuousLinearMap.IsIdempotentElem.isClosed_range
        (qᶜ : M.Projection).isStarProjection.isIdempotentElem).inter
        (ContinuousLinearMap.IsIdempotentElem.isClosed_range
          (pᶜ : M.Projection).isStarProjection.isIdempotentElem)).isComplete.completeSpace_coe
    have hrange : x.range.topologicalClosure =
        ((1 - ((qᶜ : M.Projection) : H →L[ℂ] H).range.starProjection) *
          ((pᶜ : M.Projection) : H →L[ℂ] H).range.starProjection).kerᗮ := by
      rw [← x.range.orthogonal_orthogonal_eq_closure, x.orthogonal_range,
        ← ContinuousLinearMap.star_eq_adjoint, hstar_x,
        (qᶜ : M.Projection).starProjection_range, (pᶜ : M.Projection).starProjection_range]
    calc x.range.topologicalClosure.starProjection
      _ = ((1 - ((qᶜ : M.Projection) : H →L[ℂ] H).range.starProjection) *
          ((pᶜ : M.Projection) : H →L[ℂ] H).range.starProjection).kerᗮ.starProjection :=
        Submodule.starProjection_inj.2 hrange
      _ = ((pᶜ : M.Projection) : H →L[ℂ] H) - (qᶜ ⊓ pᶜ : M.Projection) := by
        rw [Submodule.starProjection_orthogonal_ker_one_sub_mul,
          (pᶜ : M.Projection).starProjection_range, Projection.coe_inf]
        simp only [Projection.toSubmodule_closedRange, ClosedSubmodule.toSubmodule_inf]
      _ = (p ⊔ q : M.Projection) - (p : H →L[ℂ] H) := by
        rw [inf_comm, ← Projection.compl_sup, Projection.coe_compl, Projection.coe_compl]
        abel
  rw [← hfinal, ← hinit]
  exact (projectionEquivalent_orthogonal_ker_topologicalClosure_range hx).symm

end VonNeumannAlgebra

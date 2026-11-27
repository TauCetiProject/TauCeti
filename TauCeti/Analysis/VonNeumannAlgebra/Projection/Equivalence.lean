/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.VonNeumannAlgebra.Polar
public import TauCeti.Analysis.VonNeumannAlgebra.Projection.CentralSupport

/-!
# Murray–von Neumann equivalence and Kaplansky's parallelogram law

We define Murray–von Neumann equivalence `VonNeumannAlgebra.ProjectionEquivalent M p q` of
projections in a concrete von Neumann algebra `M`, prove that it is an equivalence relation on star
projections in `M` preserving central supports, show that the initial and final projections of any
operator in `M` are equivalent via its polar factor
(`VonNeumannAlgebra.projectionEquivalent_orthogonal_ker_topologicalClosure_range`), and establish
**Kaplansky's parallelogram law** (`VonNeumannAlgebra.parallelogram_projectionEquivalent`,
`VonNeumannAlgebra.parallelogram_projectionEquivalent'`):
`ProjectionEquivalent M ((p ⊔ q : M.Projection) - p) (q - (p ⊓ q : M.Projection))`.

## Main declarations

* `VonNeumannAlgebra.ProjectionEquivalent`, `VonNeumannAlgebra.projectionEquivalent_iff`,
  `VonNeumannAlgebra.ProjectionEquivalent.of_isPartialIsometry`: Murray–von Neumann equivalence
  of projections in `M`, witnessed by a partial isometry in `M`.
* `VonNeumannAlgebra.ProjectionEquivalent.mono`: monotonicity of Murray–von Neumann equivalence
  along inclusions `M ≤ N`.
* `VonNeumannAlgebra.ProjectionEquivalent.refl`, `VonNeumannAlgebra.ProjectionEquivalent.symm`,
  `VonNeumannAlgebra.ProjectionEquivalent.trans`, `VonNeumannAlgebra.ProjectionEquivalent.add`,
  `VonNeumannAlgebra.ProjectionEquivalent.centralSupport_eq`: equivalence-relation properties,
  orthogonal additivity, and central-support invariance.
* `VonNeumannAlgebra.projectionEquivalent_orthogonal_ker_topologicalClosure_range`: equivalence of
  initial and final projections via `x.polarFactor`.
* `VonNeumannAlgebra.parallelogram_projectionEquivalent`,
  `VonNeumannAlgebra.parallelogram_projectionEquivalent'`: Kaplansky's parallelogram law.

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
some partial isometry `v ∈ M` has `star v * v = p` and `v * star v = q`. -/
def ProjectionEquivalent (M : VonNeumannAlgebra H) (p q : H →L[ℂ] H) : Prop :=
  ∃ v : H →L[ℂ] H, v ∈ M ∧ v.IsPartialIsometry ∧ star v * v = p ∧ v * star v = q

namespace ProjectionEquivalent

variable {M N : VonNeumannAlgebra H} {p q r : H →L[ℂ] H}

/-- Introduce Murray–von Neumann equivalence from a partial isometry `v ∈ M` whose initial and
final projections are `p` and `q`. -/
theorem of_isPartialIsometry {v : H →L[ℂ] H} (hvM : v ∈ M) (hv : v.IsPartialIsometry)
    (hvp : star v * v = p) (hvq : v * star v = q) : ProjectionEquivalent M p q :=
  ⟨v, hvM, hv, hvp, hvq⟩

theorem isStarProjection_left (h : ProjectionEquivalent M p q) : IsStarProjection p :=
  let ⟨_, _, hv, hvp, _⟩ := h
  hvp ▸ (ContinuousLinearMap.isPartialIsometry_iff_starMul.1 hv).isStarProjection_star_mul_self

theorem isStarProjection_right (h : ProjectionEquivalent M p q) : IsStarProjection q :=
  let ⟨_, _, hv, _, hvq⟩ := h
  hvq ▸ (ContinuousLinearMap.isPartialIsometry_iff_starMul.1 hv).isStarProjection_mul_star_self

theorem mem_left (h : ProjectionEquivalent M p q) : p ∈ M :=
  let ⟨_, hvM, _, hvp, _⟩ := h
  hvp ▸ mul_mem (star_mem hvM) hvM

theorem mem_right (h : ProjectionEquivalent M p q) : q ∈ M :=
  let ⟨_, hvM, _, _, hvq⟩ := h
  hvq ▸ mul_mem hvM (star_mem hvM)

/-- Recover an implementing operator `v ∈ M` for a Murray–von Neumann equivalence
`ProjectionEquivalent M p q`. -/
theorem exists_mem (h : ProjectionEquivalent M p q) :
    ∃ v : H →L[ℂ] H, v ∈ M ∧ star v * v = p ∧ v * star v = q :=
  let ⟨v, hvM, _, hvp, hvq⟩ := h
  ⟨v, hvM, hvp, hvq⟩

/-- Murray–von Neumann equivalence is monotone in the ambient von Neumann algebra: if `M ≤ N`,
then projections equivalent in `M` are equivalent in `N`. -/
theorem mono (hMN : M ≤ N) (h : ProjectionEquivalent M p q) : ProjectionEquivalent N p q :=
  let ⟨v, hvM, hv, hvp, hvq⟩ := h
  ⟨v, hMN hvM, hv, hvp, hvq⟩

/-- Reflexivity of Murray–von Neumann equivalence on star projections in `M`. -/
theorem refl (hp : IsStarProjection p) (hpM : p ∈ M) : ProjectionEquivalent M p p :=
  ⟨p, hpM, ContinuousLinearMap.isPartialIsometry_iff_starMul.2 hp.isPartialIsometry,
    by rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq],
    by rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]⟩

/-- Symmetry of Murray–von Neumann equivalence. -/
theorem symm (h : ProjectionEquivalent M p q) : ProjectionEquivalent M q p := by
  obtain ⟨v, hvM, hv, hvp, hvq⟩ := h
  exact ⟨star v, star_mem hvM,
    by simpa only [ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.isPartialIsometry_adjoint_iff] using hv,
    by rwa [star_star], by rwa [star_star]⟩

/-- Transitivity of Murray–von Neumann equivalence. -/
theorem trans (hpq : ProjectionEquivalent M p q) (hqr : ProjectionEquivalent M q r) :
    ProjectionEquivalent M p r := by
  have hp := hpq.isStarProjection_left
  have hr := hqr.isStarProjection_right
  obtain ⟨v, hvM, _, hvp, hvq⟩ := hpq
  obtain ⟨w, hwM, _, hwq, hwr⟩ := hqr
  have hwvp : star (w * v) * (w * v) = p := by
    calc star (w * v) * (w * v)
      _ = star v * (star w * w) * v := by simp only [star_mul, mul_assoc]
      _ = star v * (v * star v) * v := by rw [hwq, ← hvq]
      _ = (star v * v) * (star v * v) := by simp only [mul_assoc]
      _ = p := by rw [hvp, hp.isIdempotentElem.eq]
  have hwvr : (w * v) * star (w * v) = r := by
    calc w * v * star (w * v)
      _ = w * (v * star v) * star w := by simp only [star_mul, mul_assoc]
      _ = w * (star w * w) * star w := by rw [hvq, ← hwq]
      _ = (w * star w) * (w * star w) := by simp only [mul_assoc]
      _ = r := by rw [hwr, hr.isIdempotentElem.eq]
  refine ⟨w * v, mul_mem hwM hvM, ?_, hwvp, hwvr⟩
  rw [ContinuousLinearMap.isPartialIsometry_iff_isStarProjection_star_mul_self, hwvp]
  exact hp

/-- Equivalent projections vanish simultaneously. -/
theorem eq_zero_iff (h : ProjectionEquivalent M p q) : p = 0 ↔ q = 0 := by
  suffices key : ∀ {e₁ e₂ : H →L[ℂ] H}, ProjectionEquivalent M e₁ e₂ → e₁ = 0 → e₂ = 0
    from ⟨key h, key h.symm⟩
  rintro e₁ e₂ ⟨v, -, -, hv₁, hv₂⟩ rfl
  have hv₀ : v = 0 := by
    rwa [star_mul_self_eq_zero] at hv₁
  rw [← hv₂, hv₀, zero_mul]

/-- Orthogonal sums of pairwise Murray–von Neumann equivalent projections in `M` are equivalent. -/
theorem add {p₁ p₂ q₁ q₂ : H →L[ℂ] H} (hp₁₂ : p₁ * p₂ = 0) (hq₁₂ : q₁ * q₂ = 0)
    (h₁ : ProjectionEquivalent M p₁ q₁) (h₂ : ProjectionEquivalent M p₂ q₂) :
    ProjectionEquivalent M (p₁ + p₂) (q₁ + q₂) := by
  have hp₁ := h₁.isStarProjection_left
  have hp₂ := h₂.isStarProjection_left
  obtain ⟨v₁, hv₁M, hv₁, hv₁p, hv₁q⟩ := h₁
  obtain ⟨v₂, hv₂M, hv₂, hv₂p, hv₂q⟩ := h₂
  have hv₁' : TauCeti.IsPartialIsometry v₁ :=
    ContinuousLinearMap.isPartialIsometry_iff_starMul.1 hv₁
  have hv₂' : TauCeti.IsPartialIsometry v₂ :=
    ContinuousLinearMap.isPartialIsometry_iff_starMul.1 hv₂
  have hstar_mul : star v₁ * v₂ = 0 :=
    (hv₁'.star_mul_eq_zero_iff hv₂').mpr (by rwa [hv₁q, hv₂q])
  have hortho : IsStarOrtho v₁ v₂ := by
    refine ⟨?_, by simpa only [star_mul, star_star, star_zero] using congrArg star hstar_mul⟩
    simpa only [star_star] using (hv₁'.star.star_mul_eq_zero_iff hv₂'.star).mpr
      (by simpa only [star_star, hv₁p, hv₂p] using hp₁₂)
  have hadd_p : star (v₁ + v₂) * (v₁ + v₂) = p₁ + p₂ := by
    rw [hortho.star_add_mul_add, hv₁p, hv₂p]
  have hadd_q : (v₁ + v₂) * star (v₁ + v₂) = q₁ + q₂ := by
    rw [hortho.add_mul_star_add, hv₁q, hv₂q]
  refine ⟨v₁ + v₂, add_mem hv₁M hv₂M, ?_, hadd_p, hadd_q⟩
  rw [ContinuousLinearMap.isPartialIsometry_iff_isStarProjection_star_mul_self, hadd_p]
  exact hp₁.add hp₂ hp₁₂

/-- Equivalent projections in `M` have the same central support. -/
theorem centralSupport_eq (h : ProjectionEquivalent M p q) :
    M.centralSupport p = M.centralSupport q := by
  suffices key : ∀ {e₁ e₂ : H →L[ℂ] H},
      ProjectionEquivalent M e₁ e₂ → M.centralSupportProjection e₁ ≤ M.centralSupportProjection e₂
    from by
      simpa only [coe_centralSupportProjection] using
        congrArg Projection.val (le_antisymm (key h) (key h.symm))
  intro e₁ e₂ he
  obtain ⟨v, hvM, hv, hv₁, hv₂⟩ := he
  rw [centralSupportProjection_le_iff, coe_centralSupportProjection]
  set z := M.centralSupport e₂
  have hqv : e₂ * v = v := by
    rw [← hv₂]
    exact (ContinuousLinearMap.isPartialIsometry_iff_starMul.1 hv).mul_star_mul_self
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
  Iff.rfl

/-- For any operator `x ∈ M`, its initial projection `x.kerᗮ.starProjection` and its final
projection `x.range.topologicalClosure.starProjection` are Murray–von Neumann equivalent in `M`,
witnessed by `x.polarFactor`. -/
theorem projectionEquivalent_orthogonal_ker_topologicalClosure_range {M : VonNeumannAlgebra H}
    {x : H →L[ℂ] H} (hx : x ∈ M) :
    ProjectionEquivalent M x.kerᗮ.starProjection x.range.topologicalClosure.starProjection :=
  ProjectionEquivalent.of_isPartialIsometry (polarFactor_mem hx) x.isPartialIsometry_polarFactor
    x.star_polarFactor_mul_polarFactor x.polarFactor_mul_star_polarFactor

/-- **Kaplansky's parallelogram law.** For any two projections `p, q : M.Projection` in a von
Neumann algebra `M`, `(p ⊔ q) - p` and `q - (p ⊓ q)` are Murray–von Neumann equivalent in `M`. -/
theorem parallelogram_projectionEquivalent {M : VonNeumannAlgebra H} (p q : M.Projection) :
    ProjectionEquivalent M ((p ⊔ q : M.Projection) - p) (q - (p ⊓ q : M.Projection)) := by
  set x : H →L[ℂ] H := (1 - (p : H →L[ℂ] H)) * q
  have hx : x ∈ M := mul_mem (sub_mem (one_mem M) p.coe_mem) q.coe_mem
  have hinit : x.kerᗮ.starProjection = (q : H →L[ℂ] H) - (p ⊓ q : M.Projection) :=
    Projection.starProjection_orthogonal_ker_one_sub_mul p q
  -- Pass to complements `qᶜ, pᶜ` via `star x = (1 - qᶜ) * pᶜ` and De Morgan's law.
  have hstar_x : star x = (1 - ((qᶜ : M.Projection) : H →L[ℂ] H)) * (pᶜ : M.Projection) := by
    simp only [x, star_mul, star_sub, star_one, Projection.star_coe, Projection.coe_compl,
      sub_sub_cancel]
  have hfinal : x.range.topologicalClosure.starProjection =
      (p ⊔ q : M.Projection) - (p : H →L[ℂ] H) := by
    have hrange : x.range.topologicalClosure = (star x).kerᗮ := by
      simpa only [ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.star_eq_adjoint] using
        (ContinuousLinearMap.orthogonal_ker (x†)).symm
    rw [Submodule.starProjection_inj.2 hrange, hstar_x,
      Projection.starProjection_orthogonal_ker_one_sub_mul qᶜ pᶜ,
      inf_comm, ← Projection.compl_sup, Projection.coe_compl, Projection.coe_compl]
    abel
  rw [← hfinal, ← hinit]
  exact (projectionEquivalent_orthogonal_ker_topologicalClosure_range hx).symm

/-- Symmetric form of **Kaplansky's parallelogram law** with `p` and `q` interchanged:
`(p ⊔ q) - q` and `p - (p ⊓ q)` are Murray–von Neumann equivalent in `M`. -/
theorem parallelogram_projectionEquivalent' {M : VonNeumannAlgebra H} (p q : M.Projection) :
    ProjectionEquivalent M ((p ⊔ q : M.Projection) - q) (p - (p ⊓ q : M.Projection)) := by
  rw [sup_comm, inf_comm]
  exact parallelogram_projectionEquivalent q p

end VonNeumannAlgebra

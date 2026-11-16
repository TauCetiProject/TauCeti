/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Level
public import TauCeti.Geometry.Symplectic.LinearReduction.Stages

/-!
# Reduction in stages at a point of a level of a moment map

Let `μ : M → 𝔤*` be a moment map of an infinitesimal action `Z ↦ Z_M` of a Lie algebra `𝔤` on a
manifold `M` with a nondegenerate two-form `σ`, in the convention `ι_{Z_M} σ = d⟨μ, Z⟩`, and let
`𝔫` be a Lie subalgebra of `𝔤`. Restricting the action to `𝔫` gives the moment map
`μ_𝔫 = μ|_𝔫 : M → 𝔫*`. Symplectic reduction in stages first reduces by `𝔫`, using a level of
`μ_𝔫`, and then reduces the result by the residual symmetry `𝔤 / 𝔫`, whose moment map is induced
by `μ` with values in the annihilator `𝔫⁰ ≅ (𝔤 / 𝔫)*`. This file carries out both stages on
tangent spaces at one point `x`.

Fix `x` at which the cocycle of `μ` vanishes and `μ(x)` vanishes on all brackets `⁅𝔫, 𝔤⁆`, that is
`𝔫 ≤ 𝔤_{μ(x)}`; this holds on the zero level of an infinitesimally equivariant moment map, and at
every point over a value fixed by the coadjoint action. Write `σ_x` for the symplectic form on
`T_x M`, `U = ker dμ_𝔫,x` for the tangent space of the first-stage level and
`U_red = U ⧸ (U ∩ U^σ)` for its reduced space (`TauCeti.SymplecticForm.ReducedSpace`).

* The whole orbit tangent space `𝔤 · x` lies in `U`
  (`TauCeti.SmoothTwoForm.IsMomentMap.orbitTangent_le_ker_differential_comp`), and the null
  directions `U ∩ U^σ` are the `𝔫`-orbit directions `𝔫 · x`
  (`TauCeti.SmoothTwoForm.IsMomentMap.ker_differential_comp_inf_orthogonal`).
* So `𝔤` acts on `U_red` by the **residual orbit map** `Z ↦ [Z_M x]`
  (`TauCeti.SmoothTwoForm.IsMomentMap.residualOrbitMap`), and `dμ_x` descends to the **residual
  differential** `U_red → 𝔤*`, `[v] ↦ dμ_x(v)`
  (`TauCeti.SmoothTwoForm.IsMomentMap.residualDifferential`), with values in `𝔫⁰`. They satisfy
  the moment-map identity of the residual stage, `σ_red([Z_M x], [v]) = ⟨dμ_x(v), Z⟩`
  (`TauCeti.SmoothTwoForm.IsMomentMap.reduction_residualOrbitMap_apply`).
* The residual orbit map kills exactly `𝔫 + 𝔤_x`
  (`TauCeti.SmoothTwoForm.IsMomentMap.ker_residualOrbitMap`), so the residual action of `𝔤 / 𝔫`
  is locally free where the action of `𝔤` is. If `dμ_x` is onto, the residual differential is
  onto `𝔫⁰` (`TauCeti.SmoothTwoForm.IsMomentMap.range_residualDifferential`). These are the
  pointwise regularity and freeness hypotheses of the residual stage.
* The kernel of the residual differential is the image in `U_red` of the level tangent space
  `ker dμ_x` (`TauCeti.SmoothTwoForm.IsMomentMap.ker_residualDifferential`), and its symplectic
  complement is the residual orbit tangent space
  (`TauCeti.SmoothTwoForm.IsMomentMap.orthogonal_ker_residualDifferential`).

Since `ker dμ_x ≤ U`
(`TauCeti.SmoothTwoForm.IsMomentMap.ker_differential_le_ker_differential_comp`), linear reduction
in stages (`TauCeti.SymplecticForm.reducedSpaceStagesEquiv`) then identifies the reduced space of
`ker dμ_x` with the reduction of `U_red` along the kernel of the residual differential,
symplectically: the tangent space of the direct reduction is that of the two-stage reduction.

## Main definitions

* `TauCeti.SmoothTwoForm.IsMomentMap.residualOrbitMap`: the residual orbit map `Z ↦ [Z_M x]`.
* `TauCeti.SmoothTwoForm.IsMomentMap.residualDifferential`: the residual differential
  `[v] ↦ dμ_x(v)`.

## References

* J. E. Marsden, G. Misiołek, J.-P. Ortega, M. Perlmutter, T. S. Ratiu, *Hamiltonian Reduction by
  Stages*, Lecture Notes in Mathematics 1913, Springer, 2007, Chapter 5 (reduction by stages for a
  normal subgroup, and the induced moment map of the residual group).
* V. Guillemin, S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984, Section 26 (the differential of a moment map).
-/

public section

open Module
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

namespace IsMomentMap

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {σ : SmoothTwoForm I M} {a : InfinitesimalAction 𝔤 I M} {μ : M → Module.Dual ℝ 𝔤}
  (h : σ.IsMomentMap a μ) (hσ : σ.IsNondegenerate) (𝔫 : LieSubalgebra ℝ 𝔤) {x : M}

/-! ### The two levels -/

/-- If `μ(x)` vanishes on the brackets `⁅𝔫, 𝔤⁆` and the cocycle of `μ` vanishes at `x`, the whole
orbit tangent space `𝔤 · x` is tangent to the level of the restricted moment map `μ|_𝔫`. -/
theorem orbitTangent_le_ker_differential_comp (hc : σ.momentCocycle a μ x = 0)
    (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x)) :
    a.orbitTangent x ≤ LinearMap.ker ((h.comp 𝔫.incl).differential x) := by
  intro v hv
  obtain ⟨Z, rfl⟩ := (a.mem_orbitTangent_iff x).1 hv
  refine LinearMap.mem_ker.2 (LinearMap.ext fun W ↦ ?_)
  have hW := LinearMap.congr_fun ((mem_lieAnnihilator ℝ 𝔤).1 (hμ W.2)) Z
  rw [Module.Dual.lie_apply, LinearMap.zero_apply, neg_eq_zero] at hW
  rw [h.differential_comp_apply, LinearMap.comp_apply,
    h.differential_apply_of_momentCocycle_eq_zero hc, Module.Dual.lie_apply, LinearMap.zero_apply,
    neg_eq_zero, ← lie_skew, map_neg, neg_eq_zero]
  simpa using hW

/-! ### The residual orbit map -/

/-- The **residual orbit map** `Z ↦ [Z_M x]` from `𝔤` to the reduced space
`U ⧸ (U ∩ U^σ)` of the level tangent space `U = ker dμ_𝔫,x` of the restricted moment map
`μ|_𝔫`. It is the orbit map of the residual action of `𝔤 / 𝔫` on the first-stage reduced space:
it vanishes on `𝔫` (`TauCeti.SmoothTwoForm.IsMomentMap.ker_residualOrbitMap`). -/
noncomputable def residualOrbitMap (hc : σ.momentCocycle a μ x = 0)
    (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x)) :
    𝔤 →ₗ[ℝ] (hσ.symplecticFormAt x).ReducedSpace
      (LinearMap.ker ((h.comp 𝔫.incl).differential x)) :=
  Submodule.mkQ _ ∘ₗ (a.eval x).codRestrict _ fun Z ↦ by
    rw [InfinitesimalAction.eval_apply]
    exact h.orbitTangent_le_ker_differential_comp 𝔫 hc hμ (a.mem_orbitTangent x Z)

/-- The residual orbit map sends `Z` to the class of `Z_M x`. -/
@[simp]
theorem residualOrbitMap_apply (hc : σ.momentCocycle a μ x = 0)
    (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x)) (Z : 𝔤) :
    h.residualOrbitMap hσ 𝔫 hc hμ Z = Submodule.Quotient.mk
      ⟨a Z x, h.orbitTangent_le_ker_differential_comp 𝔫 hc hμ (a.mem_orbitTangent x Z)⟩ := by
  rw [residualOrbitMap, LinearMap.comp_apply, Submodule.mkQ_apply]
  congr 1
  exact Subtype.ext (a.eval_apply x Z)

variable [FiniteDimensional ℝ E]

include hσ in
/-- The symplectic complement of the level tangent space of the restricted moment map `μ|_𝔫` is
the `𝔫`-orbit tangent space `𝔫 · x`. -/
theorem symplecticFormAt_orthogonal_ker_differential_comp :
    (hσ.symplecticFormAt x).orthogonal (LinearMap.ker ((h.comp 𝔫.incl).differential x)) =
      𝔫.toSubmodule.map (a.eval x) := by
  rw [(h.comp 𝔫.incl).symplecticFormAt_orthogonal_ker_differential hσ,
    InfinitesimalAction.orbitTangent_comp]
  congr 1
  ext Z
  simp

include hσ in
/-- **The null directions of the first stage are the `𝔫`-orbit directions.** If `μ(x)` vanishes on
`⁅𝔫, 𝔤⁆` and the cocycle of `μ` vanishes at `x`, the kernel of `σ_x` restricted to the level
tangent space `ker dμ_𝔫,x` of the restricted moment map is `𝔫 · x`. -/
theorem ker_differential_comp_inf_orthogonal (hc : σ.momentCocycle a μ x = 0)
    (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x)) :
    LinearMap.ker ((h.comp 𝔫.incl).differential x) ⊓
        (hσ.symplecticFormAt x).orthogonal (LinearMap.ker ((h.comp 𝔫.incl).differential x)) =
      𝔫.toSubmodule.map (a.eval x) := by
  rw [h.symplecticFormAt_orthogonal_ker_differential_comp hσ, inf_eq_right]
  rintro _ ⟨Z, -, rfl⟩
  rw [InfinitesimalAction.eval_apply]
  exact h.orbitTangent_le_ker_differential_comp 𝔫 hc hμ (a.mem_orbitTangent x Z)

include hσ in
/-- If `μ(x)` vanishes on `⁅𝔫, 𝔤⁆` and the cocycle of `μ` vanishes at `x`, the null directions of
the first stage are tangent to the level of `μ`. -/
private theorem orthogonal_ker_differential_comp_le_ker_differential
    (hc : σ.momentCocycle a μ x = 0) (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x)) :
    (hσ.symplecticFormAt x).orthogonal (LinearMap.ker ((h.comp 𝔫.incl).differential x)) ≤
      LinearMap.ker (h.differential x) := by
  rw [h.symplecticFormAt_orthogonal_ker_differential_comp hσ]
  rintro _ ⟨Z, hZ, rfl⟩
  rw [LinearMap.mem_ker, InfinitesimalAction.eval_apply,
    h.differential_apply_of_momentCocycle_eq_zero hc]
  exact (mem_lieAnnihilator ℝ 𝔤).1 (hμ hZ)

/-! ### The residual differential -/

/-- The **residual differential** `[v] ↦ dμ_x(v)` on the reduced space `U ⧸ (U ∩ U^σ)` of the
level tangent space `U = ker dμ_𝔫,x` of the restricted moment map `μ|_𝔫`. It is the differential
of the moment map of the residual stage, with values in the annihilator `𝔫⁰ ≅ (𝔤 / 𝔫)*`
(`TauCeti.SmoothTwoForm.IsMomentMap.residualDifferential_mem_dualAnnihilator`). -/
noncomputable def residualDifferential (hc : σ.momentCocycle a μ x = 0)
    (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x)) :
    (hσ.symplecticFormAt x).ReducedSpace (LinearMap.ker ((h.comp 𝔫.incl).differential x)) →ₗ[ℝ]
      Module.Dual ℝ 𝔤 :=
  Submodule.liftQ _ ((h.differential x).domRestrict _) fun _ hu ↦
    LinearMap.mem_ker.2 (LinearMap.mem_ker.1
      (h.orthogonal_ker_differential_comp_le_ker_differential hσ 𝔫 hc hμ
        ((SymplecticForm.mem_ker_restrict_iff _ _).1 hu)))

/-- The residual differential sends the class of `u` to `dμ_x(u)`. -/
@[simp]
theorem residualDifferential_mk (hc : σ.momentCocycle a μ x = 0)
    (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x))
    (u : LinearMap.ker ((h.comp 𝔫.incl).differential x)) :
    h.residualDifferential hσ 𝔫 hc hμ (Submodule.Quotient.mk u) = h.differential x u :=
  (rfl)

/-- **The moment-map identity of the residual stage**: `σ_red([Z_M x], y)` is the residual
differential of `y` evaluated at `Z`. -/
theorem reduction_residualOrbitMap_apply (hc : σ.momentCocycle a μ x = 0)
    (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x)) (Z : 𝔤)
    (y : (hσ.symplecticFormAt x).ReducedSpace
      (LinearMap.ker ((h.comp 𝔫.incl).differential x))) :
    (hσ.symplecticFormAt x).reduction _ (h.residualOrbitMap hσ 𝔫 hc hμ Z) y =
      h.residualDifferential hσ 𝔫 hc hμ y Z := by
  induction y using Submodule.Quotient.induction_on with
  | H u =>
  rw [residualOrbitMap_apply, SymplecticForm.reduction_mk, residualDifferential_mk,
    IsNondegenerate.symplecticFormAt_apply, h.differential_apply_eq_eval₂]

/-- The residual differential takes values in the annihilator `𝔫⁰` of `𝔫`, which is the dual of
`𝔤 / 𝔫`. -/
theorem residualDifferential_mem_dualAnnihilator (hc : σ.momentCocycle a μ x = 0)
    (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x))
    (y : (hσ.symplecticFormAt x).ReducedSpace
      (LinearMap.ker ((h.comp 𝔫.incl).differential x))) :
    h.residualDifferential hσ 𝔫 hc hμ y ∈ 𝔫.toSubmodule.dualAnnihilator := by
  induction y using Submodule.Quotient.induction_on with
  | H u =>
  rw [Submodule.mem_dualAnnihilator, residualDifferential_mk]
  intro W hW
  have hu := LinearMap.congr_fun (LinearMap.mem_ker.1 u.2) ⟨W, hW⟩
  rwa [h.differential_comp_apply, LinearMap.comp_apply, LinearMap.zero_apply] at hu

/-- **The kernel of the residual orbit map** is `𝔫 + 𝔤_x`: the residual action of `𝔤 / 𝔫` has
isotropy algebra `(𝔫 + 𝔤_x) / 𝔫` at the class of `x`. -/
theorem ker_residualOrbitMap (hc : σ.momentCocycle a μ x = 0)
    (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x)) :
    LinearMap.ker (h.residualOrbitMap hσ 𝔫 hc hμ) =
      𝔫.toSubmodule ⊔ (a.isotropy x).toSubmodule := by
  ext Z
  rw [LinearMap.mem_ker, residualOrbitMap_apply, Submodule.Quotient.mk_eq_zero,
    SymplecticForm.mem_ker_restrict_iff, h.symplecticFormAt_orthogonal_ker_differential_comp hσ,
    InfinitesimalAction.isotropy_toSubmodule, ← Submodule.comap_map_eq, Submodule.mem_comap,
    InfinitesimalAction.eval_apply]

/-- **The residual action is locally free where the action is.** If the action of `𝔤` is locally
free at `x`, the residual orbit map has kernel exactly `𝔫`. -/
theorem ker_residualOrbitMap_of_isotropy_eq_bot (hc : σ.momentCocycle a μ x = 0)
    (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x)) (hfree : a.isotropy x = ⊥) :
    LinearMap.ker (h.residualOrbitMap hσ 𝔫 hc hμ) = 𝔫.toSubmodule := by
  rw [h.ker_residualOrbitMap hσ 𝔫 hc hμ, hfree, LieSubalgebra.bot_toSubmodule, sup_bot_eq]

/-- **The residual level is the image of the level.** The kernel of the residual differential is
the image in the first-stage reduced space of the level tangent space `ker dμ_x`. -/
theorem ker_residualDifferential (hc : σ.momentCocycle a μ x = 0)
    (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x)) :
    LinearMap.ker (h.residualDifferential hσ 𝔫 hc hμ) =
      ((LinearMap.ker (h.differential x)).comap
          (LinearMap.ker ((h.comp 𝔫.incl).differential x)).subtype).map
        (LinearMap.ker
          ((hσ.symplecticFormAt x).toBilinForm.restrict
            (LinearMap.ker ((h.comp 𝔫.incl).differential x)))).mkQ := by
  have hK : LinearMap.ker ((hσ.symplecticFormAt x).toBilinForm.restrict
        (LinearMap.ker ((h.comp 𝔫.incl).differential x))) ≤
      (LinearMap.ker (h.differential x)).comap
        (LinearMap.ker ((h.comp 𝔫.incl).differential x)).subtype := fun u hu ↦
    h.orthogonal_ker_differential_comp_le_ker_differential hσ 𝔫 hc hμ
      ((SymplecticForm.mem_ker_restrict_iff _ _).1 hu)
  ext y
  induction y using Submodule.Quotient.induction_on with
  | H u =>
  rw [Submodule.Quotient.mk_mem_map_mkQ_iff hK, LinearMap.mem_ker, residualDifferential_mk,
    Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_ker]

/-- **The residual level is the symplectic complement of the residual orbit.** The symplectic
complement, in the first-stage reduced space, of the kernel of the residual differential is the
range of the residual orbit map. -/
theorem orthogonal_ker_residualDifferential (hc : σ.momentCocycle a μ x = 0)
    (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x)) :
    ((hσ.symplecticFormAt x).reduction _).orthogonal
        (LinearMap.ker (h.residualDifferential hσ 𝔫 hc hμ)) =
      LinearMap.range (h.residualOrbitMap hσ 𝔫 hc hμ) := by
  rw [h.ker_residualDifferential hσ 𝔫 hc hμ, SymplecticForm.reduction_orthogonal_map,
    inf_eq_left.2 (h.ker_differential_le_ker_differential_comp 𝔫.incl x),
    h.symplecticFormAt_orthogonal_ker_differential hσ, residualOrbitMap, LinearMap.range_comp,
    LinearMap.range_codRestrict, InfinitesimalAction.orbitTangent_eq_range]

/-- **The residual stage is regular where the level is.** If `dμ_x` is onto `𝔤*`, the residual
differential is onto the annihilator `𝔫⁰ ≅ (𝔤 / 𝔫)*`. -/
theorem range_residualDifferential (hc : σ.momentCocycle a μ x = 0)
    (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x)) (hreg : Function.Surjective (h.differential x)) :
    LinearMap.range (h.residualDifferential hσ 𝔫 hc hμ) = 𝔫.toSubmodule.dualAnnihilator := by
  refine le_antisymm ?_ fun ν hν ↦ ?_
  · rintro _ ⟨y, rfl⟩
    exact h.residualDifferential_mem_dualAnnihilator hσ 𝔫 hc hμ y
  · obtain ⟨v, hv⟩ := hreg ν
    have hvU : v ∈ LinearMap.ker ((h.comp 𝔫.incl).differential x) := by
      refine LinearMap.mem_ker.2 (LinearMap.ext fun W ↦ ?_)
      rw [h.differential_comp_apply, hv, LinearMap.comp_apply, LinearMap.zero_apply]
      exact (Submodule.mem_dualAnnihilator ν).1 hν W W.2
    exact ⟨Submodule.Quotient.mk ⟨v, hvU⟩, hv⟩

end IsMomentMap

end SmoothTwoForm

end TauCeti

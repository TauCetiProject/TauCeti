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
`𝔫 ≤ 𝔤_{μ(x)}`; for an infinitesimally equivariant moment map this holds on the zero level and at
every point over a coadjoint-fixed value. Write `σ_x` for the symplectic form on
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
symplectically (`TauCeti.SmoothTwoForm.IsMomentMap.reducedSpaceStagesEquiv`,
`TauCeti.SmoothTwoForm.IsMomentMap.isSymplectomorphism_reducedSpaceStagesEquiv`): the tangent
space of the direct reduction is that of the two-stage reduction.

## Main definitions

* `TauCeti.SmoothTwoForm.IsMomentMap.residualOrbitMap`: the residual orbit map `Z ↦ [Z_M x]`.
* `TauCeti.SmoothTwoForm.IsMomentMap.residualDifferential`: the residual differential
  `[v] ↦ dμ_x(v)`.
* `TauCeti.SmoothTwoForm.IsMomentMap.reducedSpaceStagesEquiv`: reduction in stages at `x`, the
  symplectic identification `[v] ↦ [[v]]` of the direct reduced tangent space with the two-stage
  one.

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

/-- A tangent vector lies in the level tangent space `ker dμ_𝔫,x` of the restricted moment map
`μ|_𝔫` exactly when `dμ_x` maps it into the annihilator `𝔫⁰`. -/
theorem mem_ker_differential_comp_iff {v : TangentSpace I x} :
    v ∈ LinearMap.ker ((h.comp 𝔫.incl).differential x) ↔
      h.differential x v ∈ 𝔫.toSubmodule.dualAnnihilator := by
  rw [LinearMap.mem_ker, h.differential_comp_apply, Submodule.mem_dualAnnihilator]
  exact ⟨fun hv W hW ↦ LinearMap.congr_fun hv ⟨W, hW⟩,
    fun hv ↦ LinearMap.ext fun W ↦ hv W W.property⟩

/-- If `μ(x)` vanishes on the brackets `⁅𝔫, 𝔤⁆` and the cocycle of `μ` vanishes at `x`, the whole
orbit tangent space `𝔤 · x` is tangent to the level of the restricted moment map `μ|_𝔫`. -/
theorem orbitTangent_le_ker_differential_comp (hc : σ.momentCocycle a μ x = 0)
    (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x)) :
    a.orbitTangent x ≤ LinearMap.ker ((h.comp 𝔫.incl).differential x) := by
  intro v hv
  obtain ⟨Z, rfl⟩ := (a.mem_orbitTangent_iff x).1 hv
  rw [h.mem_ker_differential_comp_iff, h.differential_apply_of_momentCocycle_eq_zero hc,
    Submodule.mem_dualAnnihilator]
  intro W hW
  have hW := LinearMap.congr_fun ((mem_lieAnnihilator ℝ 𝔤).1 (hμ hW)) Z
  simp only [Module.Dual.lie_apply, LinearMap.zero_apply, neg_eq_zero] at hW ⊢
  rw [← lie_skew, map_neg, hW, neg_zero]

/-! ### The residual orbit map -/

/-- The **residual orbit map** `Z ↦ [Z_M x]` from `𝔤` to the reduced space
`U ⧸ (U ∩ U^σ)` of the level tangent space `U = ker dμ_𝔫,x` of the restricted moment map
`μ|_𝔫`. It is the orbit map of the residual action of `𝔤 / 𝔫` on the first-stage reduced space:
it vanishes on `𝔫` (`TauCeti.SmoothTwoForm.IsMomentMap.ker_residualOrbitMap`). -/
noncomputable def residualOrbitMap (hc : σ.momentCocycle a μ x = 0)
    (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x)) :
    𝔤 →ₗ[ℝ] (hσ.symplecticFormAt x).ReducedSpace
      (LinearMap.ker ((h.comp 𝔫.incl).differential x)) :=
  Submodule.mkQ _ ∘ₗ (a.eval x).codRestrict _ fun Z ↦
    h.orbitTangent_le_ker_differential_comp 𝔫 hc hμ (a.orbitTangent_eq_range x ▸ ⟨Z, rfl⟩)

/-- The residual orbit map sends `Z` to the class of `Z_M x`. -/
@[simp]
theorem residualOrbitMap_apply (hc : σ.momentCocycle a μ x = 0)
    (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x)) (Z : 𝔤) :
    h.residualOrbitMap hσ 𝔫 hc hμ Z = Submodule.Quotient.mk
      ⟨a Z x, h.orbitTangent_le_ker_differential_comp 𝔫 hc hμ (a.mem_orbitTangent x Z)⟩ := by
  rw [residualOrbitMap, LinearMap.comp_apply, Submodule.mkQ_apply]
  congr 1
  exact Subtype.ext (a.eval_apply x Z)

/-- The range of the residual orbit map is the image of the orbit tangent space `𝔤 · x` in the
first-stage reduced space. -/
theorem range_residualOrbitMap (hc : σ.momentCocycle a μ x = 0)
    (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x)) :
    LinearMap.range (h.residualOrbitMap hσ 𝔫 hc hμ) =
      ((a.orbitTangent x).comap (LinearMap.ker ((h.comp 𝔫.incl).differential x)).subtype).map
        (LinearMap.ker ((hσ.symplecticFormAt x).toBilinForm.restrict
          (LinearMap.ker ((h.comp 𝔫.incl).differential x)))).mkQ := by
  rw [residualOrbitMap, LinearMap.range_comp, LinearMap.range_codRestrict,
    InfinitesimalAction.orbitTangent_eq_range]

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
  refine le_trans ?_ (h.orbitTangent_le_ker_differential_comp 𝔫 hc hμ)
  rw [InfinitesimalAction.orbitTangent_eq_range]
  exact LinearMap.map_le_range

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

include hσ in
/-- If `μ(x)` vanishes on `⁅𝔫, 𝔤⁆` and the cocycle of `μ` vanishes at `x`, the null directions
`U ∩ U^σ` of the first stage `U = ker dμ_𝔫,x` lie in the level of `μ`. -/
private theorem ker_restrict_le_comap_ker_differential (hc : σ.momentCocycle a μ x = 0)
    (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x)) :
    LinearMap.ker ((hσ.symplecticFormAt x).toBilinForm.restrict
        (LinearMap.ker ((h.comp 𝔫.incl).differential x))) ≤
      (LinearMap.ker (h.differential x)).comap
        (LinearMap.ker ((h.comp 𝔫.incl).differential x)).subtype := fun _ hu ↦
  h.orthogonal_ker_differential_comp_le_ker_differential hσ 𝔫 hc hμ
    ((SymplecticForm.mem_ker_restrict_iff _ _).1 hu)

/-! ### The residual differential -/

/-- The **residual differential** `[v] ↦ dμ_x(v)` on the reduced space `U ⧸ (U ∩ U^σ)` of the
level tangent space `U = ker dμ_𝔫,x` of the restricted moment map `μ|_𝔫`. It is the differential
of the moment map of the residual stage, with values in the annihilator `𝔫⁰ ≅ (𝔤 / 𝔫)*`
(`TauCeti.SmoothTwoForm.IsMomentMap.residualDifferential_mem_dualAnnihilator`). -/
noncomputable def residualDifferential (hc : σ.momentCocycle a μ x = 0)
    (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x)) :
    (hσ.symplecticFormAt x).ReducedSpace (LinearMap.ker ((h.comp 𝔫.incl).differential x)) →ₗ[ℝ]
      Module.Dual ℝ 𝔤 :=
  Submodule.liftQ _ ((h.differential x).domRestrict _)
    (h.ker_restrict_le_comap_ker_differential hσ 𝔫 hc hμ)

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
  exact (h.mem_ker_differential_comp_iff 𝔫).1 u.property

/-- **The kernel of the residual orbit map** is `𝔫 + 𝔤_x`: the residual action of `𝔤 / 𝔫` has
isotropy algebra `(𝔫 + 𝔤_x) / 𝔫` at the class of `x`. -/
theorem ker_residualOrbitMap (hc : σ.momentCocycle a μ x = 0)
    (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x)) :
    LinearMap.ker (h.residualOrbitMap hσ 𝔫 hc hμ) =
      𝔫.toSubmodule ⊔ (a.isotropy x).toSubmodule := by
  -- `[Z_M x] = 0` exactly when `Z_M x` lies in the null directions `𝔫 · x`, that is when `Z`
  -- lies in the preimage of `𝔫 · x` under `Z ↦ Z_M x`, which is `𝔫 + ker (Z ↦ Z_M x)`.
  rw [InfinitesimalAction.isotropy_toSubmodule, ← Submodule.comap_map_eq]
  ext Z
  rw [LinearMap.mem_ker, residualOrbitMap_apply, Submodule.Quotient.mk_eq_zero,
    SymplecticForm.mem_ker_restrict_iff, h.symplecticFormAt_orthogonal_ker_differential_comp hσ,
    Submodule.mem_comap, InfinitesimalAction.eval_apply]

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
  ext y
  induction y using Submodule.Quotient.induction_on with
  | H u =>
  rw [Submodule.Quotient.mk_mem_map_mkQ_iff (h.ker_restrict_le_comap_ker_differential hσ 𝔫 hc hμ),
    LinearMap.mem_ker, residualDifferential_mk,
    Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_ker]

/-- **The residual orbit is the symplectic complement of the residual level.** The symplectic
complement, in the first-stage reduced space, of the kernel of the residual differential is the
range of the residual orbit map. -/
theorem orthogonal_ker_residualDifferential (hc : σ.momentCocycle a μ x = 0)
    (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x)) :
    ((hσ.symplecticFormAt x).reduction _).orthogonal
        (LinearMap.ker (h.residualDifferential hσ 𝔫 hc hμ)) =
      LinearMap.range (h.residualOrbitMap hσ 𝔫 hc hμ) := by
  rw [h.ker_residualDifferential hσ 𝔫 hc hμ, SymplecticForm.reduction_orthogonal_map,
    inf_eq_left.2 (h.ker_differential_le_ker_differential_comp 𝔫.incl x),
    h.symplecticFormAt_orthogonal_ker_differential hσ, range_residualOrbitMap]

/-- **The residual stage is regular where the level is.** If `dμ_x` is onto `𝔤*`, the residual
differential is onto the annihilator `𝔫⁰ ≅ (𝔤 / 𝔫)*`. -/
theorem range_residualDifferential (hc : σ.momentCocycle a μ x = 0)
    (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x)) (hreg : Function.Surjective (h.differential x)) :
    LinearMap.range (h.residualDifferential hσ 𝔫 hc hμ) = 𝔫.toSubmodule.dualAnnihilator := by
  refine le_antisymm ?_ fun ν hν ↦ ?_
  · rintro _ ⟨y, rfl⟩
    exact h.residualDifferential_mem_dualAnnihilator hσ 𝔫 hc hμ y
  · obtain ⟨v, hv⟩ := hreg ν
    exact ⟨Submodule.Quotient.mk ⟨v, (h.mem_ker_differential_comp_iff 𝔫).2 (hv ▸ hν)⟩, hv⟩

/-! ### Reduction in stages -/

/-- **Reduction in stages at a point.** The reduced space of the level tangent space `ker dμ_x` is
linearly equivalent, by `[v] ↦ [[v]]`, to the reduction of the first-stage reduced space
`U ⧸ (U ∩ U^σ)`, `U = ker dμ_𝔫,x`, along the kernel of the residual differential. It is a
symplectomorphism
(`TauCeti.SmoothTwoForm.IsMomentMap.isSymplectomorphism_reducedSpaceStagesEquiv`): the tangent
space of the direct reduction is that of the two-stage reduction. -/
noncomputable def reducedSpaceStagesEquiv (hc : σ.momentCocycle a μ x = 0)
    (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x)) :
    (hσ.symplecticFormAt x).ReducedSpace (LinearMap.ker (h.differential x)) ≃ₗ[ℝ]
      ((hσ.symplecticFormAt x).reduction
          (LinearMap.ker ((h.comp 𝔫.incl).differential x))).ReducedSpace
        (LinearMap.ker (h.residualDifferential hσ 𝔫 hc hμ)) :=
  ((hσ.symplecticFormAt x).reducedSpaceStagesEquiv
      (h.ker_differential_le_ker_differential_comp 𝔫.incl x)).trans
    (SymplecticForm.reducedSpaceCongr _ _ (LinearEquiv.refl ℝ _)
      (SymplecticForm.IsSymplectomorphism.refl _) (by
        rw [LinearEquiv.refl_toLinearMap, Submodule.map_id, h.ker_residualDifferential hσ 𝔫 hc hμ]))

/-- The reduction-in-stages equivalence at a point sends `[v]` to `[[v]]`. -/
@[simp]
theorem reducedSpaceStagesEquiv_mk (hc : σ.momentCocycle a μ x = 0)
    (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x)) (v : LinearMap.ker (h.differential x)) :
    h.reducedSpaceStagesEquiv hσ 𝔫 hc hμ (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ⟨Submodule.Quotient.mk
          (Submodule.inclusion (h.ker_differential_le_ker_differential_comp 𝔫.incl x) v),
        (h.ker_residualDifferential hσ 𝔫 hc hμ).ge ⟨_, v.property, rfl⟩⟩ := by
  simp only [reducedSpaceStagesEquiv, LinearEquiv.trans_apply,
    SymplecticForm.reducedSpaceStagesEquiv_mk, SymplecticForm.reducedSpaceCongr_mk,
    LinearEquiv.refl_apply]

/-- **Reduction in stages at a point** is a symplectomorphism: the reduced form on the tangent
space of the direct reduction agrees with the reduced form of the residual stage. -/
theorem isSymplectomorphism_reducedSpaceStagesEquiv (hc : σ.momentCocycle a μ x = 0)
    (hμ : 𝔫 ≤ lieAnnihilator ℝ 𝔤 (μ x)) :
    SymplecticForm.IsSymplectomorphism
      ((hσ.symplecticFormAt x).reduction (LinearMap.ker (h.differential x)))
      (((hσ.symplecticFormAt x).reduction
          (LinearMap.ker ((h.comp 𝔫.incl).differential x))).reduction
        (LinearMap.ker (h.residualDifferential hσ 𝔫 hc hμ)))
      (h.reducedSpaceStagesEquiv hσ 𝔫 hc hμ) :=
  ((hσ.symplecticFormAt x).isSymplectomorphism_reducedSpaceStagesEquiv _).trans
    (SymplecticForm.isSymplectomorphism_reducedSpaceCongr _ _ _)

end IsMomentMap

end SmoothTwoForm

end TauCeti

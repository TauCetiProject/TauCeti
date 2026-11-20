/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothSingular.Cycles
public import TauCeti.Geometry.Manifold.SmoothSingular.IntegerIntegrals
public import TauCeti.Geometry.Manifold.SmoothSingular.Stokes
public import TauCeti.Geometry.Manifold.DeRham.Basic
import TauCeti.Topology.Circle.AddCircle

/-!
# Differential characters

Let `M` be a smooth manifold and `k : ℕ`. A *differential character* of degree `k`, in the sense of
Cheeger and Simons, is a homomorphism `χ : Z_k(M; ℤ) → ℝ/ℤ` from the smooth singular integral
`k`-cycles of `M` to the circle for which there is a smooth real `(k + 1)`-form `φ` with

`χ (∂c) = ∫_c φ mod ℤ`

for every smooth singular integral `(k + 1)`-chain `c`. They form the subgroup
`TauCeti.differentialCharacters I M k` of `Hom(Z_k(M; ℤ), ℝ/ℤ)`. This is the group Cheeger and
Simons denote by `H^k(M; ℝ/ℤ)` with a hat. In the grading in which degree-two differential
cohomology classifies circle bundles with connection, it is the integral differential cohomology
group of degree `k + 1`, and the form `φ`, its curvature, has degree `k + 1`.

On a boundaryless manifold the form `φ` is determined by `χ`
(`TauCeti.differentialCharacters.curvature_eq_of_forall`): forms whose integrals over all smooth
integral chains agree modulo `ℤ` are equal
(`TauCeti.SmoothForm.eq_of_forall_coe_integrationCochain_eq`), since a continuous form of
positive degree whose integral over every smooth simplex is an integer vanishes. This gives the
curvature homomorphism `TauCeti.differentialCharacters.curvature`. The curvature is closed
(`TauCeti.differentialCharacters.curvature_mem_closedForms`) and has integral periods
(`TauCeti.differentialCharacters.exists_integrationCochain_curvature_eq_intCast`). A smooth
`k`-form `η` defines the character `z ↦ ∫_z η mod ℤ`, whose curvature is `dη` by Stokes' theorem
(`TauCeti.differentialCharacters.ofForm`, `TauCeti.differentialCharacters.curvature_ofForm`), and
the characters of curvature zero are those vanishing on boundaries
(`TauCeti.differentialCharacters.curvature_eq_zero_iff`). Smooth maps pull characters back by
precomposition with the induced map on cycles, functorially, and curvatures by pullback of forms
(`TauCeti.differentialCharacters.pullback`, `TauCeti.differentialCharacters.pullback_id`,
`TauCeti.differentialCharacters.pullback_comp`,
`TauCeti.differentialCharacters.curvature_pullback`); the character of a form pulls back to the
character of the pulled-back form (`TauCeti.differentialCharacters.pullback_ofForm`).

Cycles and chains are the integral chains of the smooth singular simplicial set
`TauCeti.smoothSingularSubcomplex` (`TauCeti.smoothIntCycles`, `TauCeti.smoothIntBoundary`), with
integration `TauCeti.integrationCochain` with integer coefficients.

## References

* J. Cheeger and J. Simons, *Differential characters and geometric invariants*, Geometry and
  Topology (College Park, 1983/84), Lecture Notes in Math. 1167, Springer, 1985, §1.
-/

public section

noncomputable section

open CategoryTheory
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type) [TopologicalSpace M] [ChartedSpace H M]

section Characters

variable [IsManifold I 1 M]

/-- **Differential characters** of Cheeger and Simons, of degree `k`: the homomorphisms `χ` from
smooth singular integral `k`-cycles of `M` to `ℝ/ℤ` for which some smooth real `(k + 1)`-form `φ`
satisfies `χ (∂c) = ∫_c φ mod ℤ` for every smooth singular integral `(k + 1)`-chain `c`. This is
the integral differential cohomology group of degree `k + 1`. -/
def differentialCharacters (k : ℕ) : AddSubgroup (smoothIntCycles I M k →+ UnitAddCircle) where
  carrier := {χ | ∃ φ : SmoothForm I M ℝ (k + 1), ∀ c, χ (smoothIntBoundary I M k c) =
    ((integrationCochain φ.1).hom c : UnitAddCircle)}
  zero_mem' := ⟨0, fun c ↦ by simp⟩
  add_mem' := by
    rintro χ ψ ⟨φ, hφ⟩ ⟨θ, hθ⟩
    refine ⟨φ + θ, fun c ↦ ?_⟩
    rw [SmoothForm.integrationCochain_add]
    simp [hφ, hθ]
  neg_mem' := by
    rintro χ ⟨φ, hφ⟩
    exact ⟨-φ, fun c ↦ by simp [hφ]⟩

variable {I M} in
theorem mem_differentialCharacters_iff {k : ℕ} {χ : smoothIntCycles I M k →+ UnitAddCircle} :
    χ ∈ differentialCharacters I M k ↔ ∃ φ : SmoothForm I M ℝ (k + 1),
      ∀ c, χ (smoothIntBoundary I M k c) = ((integrationCochain φ.1).hom c : UnitAddCircle) :=
  Iff.rfl

end Characters

namespace differentialCharacters

variable {I M} {k : ℕ}

section Curvature

variable [IsManifold I ∞ M] [BoundarylessManifold I M]

/-- The **curvature** of a differential character `χ` on a boundaryless manifold: the unique smooth
`(k + 1)`-form `φ` with `χ (∂c) = ∫_c φ mod ℤ` for every smooth singular integral
`(k + 1)`-chain `c`. -/
def curvature : differentialCharacters I M k →+ SmoothForm I M ℝ (k + 1) where
  toFun χ := (mem_differentialCharacters_iff.mp χ.2).choose
  map_zero' := SmoothForm.eq_of_forall_coe_integrationCochain_eq k.succ_ne_zero fun c ↦ by
    rw [← (mem_differentialCharacters_iff.mp (0 : differentialCharacters I M k).2).choose_spec c]
    simp
  map_add' χ ψ := by
    have hχ := (mem_differentialCharacters_iff.mp χ.2).choose_spec
    have hψ := (mem_differentialCharacters_iff.mp ψ.2).choose_spec
    have hχψ := (mem_differentialCharacters_iff.mp (χ + ψ).2).choose_spec
    refine SmoothForm.eq_of_forall_coe_integrationCochain_eq k.succ_ne_zero fun c ↦ ?_
    rw [← hχψ c, SmoothForm.integrationCochain_add]
    simp [hχ c, hψ c]

/-- The defining property of the curvature: on the boundary of a smooth singular integral
`(k + 1)`-chain `c`, a differential character is the integral of its curvature over `c` modulo
`ℤ`. -/
theorem apply_smoothIntBoundary (χ : differentialCharacters I M k)
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X (k + 1)) :
    (χ : smoothIntCycles I M k →+ UnitAddCircle) (smoothIntBoundary I M k c) =
      ((integrationCochain (curvature χ).1).hom c : UnitAddCircle) :=
  (mem_differentialCharacters_iff.mp χ.2).choose_spec c

/-- The curvature of a differential character is the only form whose integrals over smooth
singular integral `(k + 1)`-chains are, modulo `ℤ`, the values of the character on their
boundaries. -/
theorem curvature_eq_of_forall {χ : differentialCharacters I M k}
    {φ : SmoothForm I M ℝ (k + 1)}
    (h : ∀ c, (χ : smoothIntCycles I M k →+ UnitAddCircle) (smoothIntBoundary I M k c) =
      ((integrationCochain φ.1).hom c : UnitAddCircle)) :
    curvature χ = φ :=
  SmoothForm.eq_of_forall_coe_integrationCochain_eq k.succ_ne_zero fun c ↦ by
    rw [← apply_smoothIntBoundary, h]

/-- **Integral periods.** The integral of the curvature of a differential character over every
smooth singular integral `(k + 1)`-cycle is an integer. -/
theorem exists_integrationCochain_curvature_eq_intCast (χ : differentialCharacters I M k)
    {z : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X (k + 1)}
    (hz : z ∈ smoothIntCycles I M (k + 1)) :
    ∃ n : ℤ, (integrationCochain (curvature χ).1).hom z = n := by
  have h := apply_smoothIntBoundary χ z
  have hzero : smoothIntBoundary I M k z = 0 :=
    Subtype.ext (by simpa using mem_smoothIntCycles_iff.mp hz)
  rwa [hzero, map_zero, eq_comm, UnitAddCircle.coe_eq_zero_iff] at h

/-- The curvature of a differential character is closed. -/
theorem curvature_mem_closedForms (χ : differentialCharacters I M k) :
    curvature χ ∈ closedForms I M (k + 1) := by
  rw [mem_closedForms]
  have hd : IsSmoothForm I 0 (mextDeriv (curvature χ).1) := by
    simpa only [mextDerivₗ_apply] using
      (mextDerivₗ I (k + 1) (curvature χ)).isSmoothForm.of_le (m := 0) (by simp)
  refine RoughForm.eq_zero_of_forall_integral_eq_intCast (k + 1).succ_ne_zero hd fun σ ↦ ?_
  -- By Stokes' theorem, `∫_σ dφ` is the integral of the curvature `φ` over the cycle `∂σ`, an
  -- integer by integral periods.
  let c := ((smoothSingularSubcomplex I M : SSet).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1
  have h := exists_integrationCochain_curvature_eq_intCast χ (smoothIntBoundary I M (k + 1) c).2
  rwa [coe_smoothIntBoundary,
    integrationCochain_d_apply ((curvature χ).isSmoothForm.of_le (by simp)),
    integrationCochain_ιChainComplex, one_smul] at h

/-- **Flat characters.** A differential character has curvature zero exactly when it vanishes on
boundaries. -/
theorem curvature_eq_zero_iff {χ : differentialCharacters I M k} :
    curvature χ = 0 ↔
      ∀ c, (χ : smoothIntCycles I M k →+ UnitAddCircle) (smoothIntBoundary I M k c) = 0 := by
  refine ⟨fun h c ↦ ?_, fun h ↦ curvature_eq_of_forall fun c ↦ by simp [h c]⟩
  rw [apply_smoothIntBoundary, h]
  simp

end Curvature

section OfForm

variable [IsManifold I 2 M]

/-- The differential character `z ↦ ∫_z η mod ℤ` of a smooth `k`-form `η`, as a homomorphism
from forms to differential characters. Its curvature is `dη`, by Stokes' theorem. -/
def ofForm : SmoothForm I M ℝ k →+ differentialCharacters I M k where
  toFun η := ⟨(QuotientAddGroup.mk' _).comp ((integrationCochain η.1).hom.toAddMonoidHom.comp
      (smoothIntCycles I M k).subtype),
    mextDerivₗ I k η, fun c ↦ by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
        AddSubgroup.coe_subtype, coe_smoothIntBoundary, mextDerivₗ_apply,
        QuotientAddGroup.mk'_apply]
      rw [integrationCochain_d_apply (η.isSmoothForm.of_le (by simp))]⟩
  map_zero' := by
    ext z
    simp
  map_add' η θ := by
    ext z
    simp only [SmoothForm.integrationCochain_add]
    simp

/-- The character of a form evaluates a cycle by integrating the form over it modulo `ℤ`. -/
@[simp]
theorem ofForm_apply (η : SmoothForm I M ℝ k) (z : smoothIntCycles I M k) :
    (ofForm η : smoothIntCycles I M k →+ UnitAddCircle) z =
      ((integrationCochain (R := ℤ) η.1).hom z : UnitAddCircle) := by
  simp [ofForm]

/-- The curvature of the character of a form `η` is `dη`. -/
@[simp]
theorem curvature_ofForm [IsManifold I ∞ M] [BoundarylessManifold I M]
    (η : SmoothForm I M ℝ k) : curvature (ofForm η) = mextDerivₗ I k η :=
  curvature_eq_of_forall fun c ↦ by
    rw [ofForm_apply, coe_smoothIntBoundary,
      integrationCochain_d_apply (η.isSmoothForm.of_le (by simp)), mextDerivₗ_apply]

end OfForm

section Pullback

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I 1 M] [IsManifold J 1 N] {f : M → N}

/-- **Pullback of differential characters** along a smooth map `f : M → N`: precomposition with
the pushforward of cycles. A curvature `φ` of `χ` pulls back to the curvature `f^*φ`. -/
def pullback (hf : ContMDiff I J ∞ f) : differentialCharacters J N k →+ differentialCharacters I M k
    where
  toFun χ := ⟨(χ : smoothIntCycles J N k →+ UnitAddCircle).comp (smoothIntCyclesMap hf k), by
    obtain ⟨φ, hφ⟩ := mem_differentialCharacters_iff.mp χ.2
    refine ⟨SmoothForm.mpullback f hf φ, fun c ↦ ?_⟩
    rw [AddMonoidHom.comp_apply, smoothIntCyclesMap_smoothIntBoundary, hφ,
      SmoothForm.coe_mpullback, integrationCochain_chainComplexMap_apply hf]⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The pullback of a character evaluates it on the pushforward of a cycle. -/
@[simp]
theorem pullback_apply (hf : ContMDiff I J ∞ f) (χ : differentialCharacters J N k)
    (z : smoothIntCycles I M k) :
    (pullback hf χ : smoothIntCycles I M k →+ UnitAddCircle) z =
      (χ : smoothIntCycles J N k →+ UnitAddCircle) (smoothIntCyclesMap hf k z) :=
  (rfl)

variable (I M k) in
/-- Pulling characters back along the identity is the identity. -/
@[simp]
theorem pullback_id :
    pullback (I := I) (J := I) (M := M) (N := M) (f := id) (k := k) contMDiff_id =
      AddMonoidHom.id _ := by
  refine AddMonoidHom.ext fun χ ↦ Subtype.ext (AddMonoidHom.ext fun z ↦ ?_)
  rw [pullback_apply, smoothIntCyclesMap_id, AddMonoidHom.id_apply, AddMonoidHom.id_apply]

/-- Pulling characters back along a composite is the composite of the pullbacks, in the opposite
order. -/
theorem pullback_comp {E'' H'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''} {P : Type} [TopologicalSpace P]
    [ChartedSpace H'' P] [IsManifold K 1 P] {g : N → P} (hg : ContMDiff J K ∞ g)
    (hf : ContMDiff I J ∞ f) :
    pullback (k := k) (hg.comp hf) = (pullback hf).comp (pullback hg) := by
  refine AddMonoidHom.ext fun χ ↦ Subtype.ext (AddMonoidHom.ext fun z ↦ ?_)
  rw [pullback_apply, smoothIntCyclesMap_comp hg hf, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply, pullback_apply, pullback_apply]

/-- The pullback of the character of a form is the character of the pulled-back form. -/
@[simp]
theorem pullback_ofForm [IsManifold I 2 M] [IsManifold J 2 N] (hf : ContMDiff I J ∞ f)
    (η : SmoothForm J N ℝ k) : pullback hf (ofForm η) = ofForm (SmoothForm.mpullback f hf η) := by
  refine Subtype.ext (AddMonoidHom.ext fun z ↦ ?_)
  rw [pullback_apply, ofForm_apply, ofForm_apply, coe_smoothIntCyclesMap, SmoothForm.coe_mpullback,
    integrationCochain_chainComplexMap_apply hf]

/-- The curvature of the pullback of a character is the pullback of its curvature. -/
@[simp]
theorem curvature_pullback [IsManifold I ∞ M] [BoundarylessManifold I M] [IsManifold J ∞ N]
    [BoundarylessManifold J N] (hf : ContMDiff I J ∞ f) (χ : differentialCharacters J N k) :
    curvature (pullback hf χ) = SmoothForm.mpullback f hf (curvature χ) :=
  curvature_eq_of_forall fun c ↦ by
    rw [pullback_apply, smoothIntCyclesMap_smoothIntBoundary, apply_smoothIntBoundary,
      SmoothForm.coe_mpullback, integrationCochain_chainComplexMap_apply hf]

end Pullback

end differentialCharacters

end TauCeti

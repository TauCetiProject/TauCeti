/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Basic
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
(`TauCeti.differentialCharacters.curvature_mem_integralPeriodForms`): its integral over every
smooth integral cycle is an integer, which for any form forces closedness
(`TauCeti.mem_closedForms_of_mem_integralPeriodForms`). A smooth
`k`-form `η` defines the character `z ↦ ∫_z η mod ℤ`, whose curvature is `dη` by Stokes' theorem
(`TauCeti.differentialCharacters.ofForm`, `TauCeti.differentialCharacters.curvature_ofForm`), and
the characters of curvature zero are those vanishing on boundaries
(`TauCeti.differentialCharacters.curvature_eq_zero_iff`). Smooth maps pull characters back by
precomposition with the induced map on cycles, functorially, and curvatures by pullback of forms
(`TauCeti.differentialCharacters.pullback`, `TauCeti.differentialCharacters.pullback_id`,
`TauCeti.differentialCharacters.pullback_comp`,
`TauCeti.differentialCharacters.curvature_pullback`); the character of a form pulls back to the
character of the pulled-back form (`TauCeti.differentialCharacters.pullback_ofForm`).

Chains are the integral chains of the smooth singular simplicial set
`TauCeti.smoothSingularSubcomplex`, cycles are the `HomologicalComplex.cycles` of its chain complex
with coefficients in `ℤ`, the boundary of a chain as a cycle is `HomologicalComplex.toCycles`, and
pushforward of cycles is `HomologicalComplex.cyclesMap`. Integration is
`TauCeti.integrationCochain` with integer coefficients.

## References

* J. Cheeger and J. Simons, *Differential characters and geometric invariants*, Geometry and
  Topology (College Park, 1983/84), Lecture Notes in Math. 1167, Springer, 1985, §1.
-/

public section

noncomputable section

open CategoryTheory HomologicalComplex
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
def differentialCharacters (k : ℕ) :
    AddSubgroup
      (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).cycles k →+
        UnitAddCircle) where
  carrier := {χ | ∃ φ : SmoothForm I M ℝ (k + 1), ∀ c,
    χ (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).toCycles (k + 1) k
      c) = ((integrationCochain φ.val).hom c : UnitAddCircle)}
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
theorem mem_differentialCharacters_iff {k : ℕ}
    {χ : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).cycles k →+
      UnitAddCircle} :
    χ ∈ differentialCharacters I M k ↔ ∃ φ : SmoothForm I M ℝ (k + 1), ∀ c,
      χ (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).toCycles (k + 1) k
        c) = ((integrationCochain φ.val).hom c : UnitAddCircle) :=
  Iff.rfl

variable {I M} in
/-- Two differential characters are equal once they agree on every cycle. -/
@[ext]
theorem differentialCharacters.ext {k : ℕ} {χ ψ : differentialCharacters I M k}
    (h : ∀ z, (χ : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).cycles k
      →+ UnitAddCircle) z =
        (ψ : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).cycles k
          →+ UnitAddCircle) z) : χ = ψ :=
  Subtype.ext (AddMonoidHom.ext h)

end Characters

namespace differentialCharacters

variable {I M} {k : ℕ}

section Curvature

variable [IsManifold I ∞ M] [BoundarylessManifold I M]

/-- The **curvature** of a differential character `χ` on a boundaryless manifold: the unique smooth
`(k + 1)`-form `φ` with `χ (∂c) = ∫_c φ mod ℤ` for every smooth singular integral
`(k + 1)`-chain `c`. -/
def curvature : differentialCharacters I M k →+ SmoothForm I M ℝ (k + 1) where
  toFun χ := (mem_differentialCharacters_iff.mp χ.property).choose
  map_zero' := SmoothForm.eq_of_forall_coe_integrationCochain_eq k.succ_ne_zero fun c ↦ by
    rw [← (mem_differentialCharacters_iff.mp
      (0 : differentialCharacters I M k).property).choose_spec c]
    simp
  map_add' χ ψ := by
    have hχ := (mem_differentialCharacters_iff.mp χ.property).choose_spec
    have hψ := (mem_differentialCharacters_iff.mp ψ.property).choose_spec
    have hχψ := (mem_differentialCharacters_iff.mp (χ + ψ).property).choose_spec
    refine SmoothForm.eq_of_forall_coe_integrationCochain_eq k.succ_ne_zero fun c ↦ ?_
    rw [← hχψ c, SmoothForm.integrationCochain_add]
    simp [hχ c, hψ c]

/-- The defining property of the curvature: on the boundary of a smooth singular integral
`(k + 1)`-chain `c`, a differential character is the integral of its curvature over `c` modulo
`ℤ`. -/
theorem apply_toCycles (χ : differentialCharacters I M k)
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X (k + 1)) :
    (χ : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).cycles k →+
      UnitAddCircle)
        (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).toCycles (k + 1) k
          c) =
      ((integrationCochain (curvature χ).val).hom c : UnitAddCircle) :=
  (mem_differentialCharacters_iff.mp χ.property).choose_spec c

/-- The curvature of a differential character is the only form whose integrals over smooth
singular integral `(k + 1)`-chains are, modulo `ℤ`, the values of the character on their
boundaries. -/
theorem curvature_eq_of_forall {χ : differentialCharacters I M k}
    {φ : SmoothForm I M ℝ (k + 1)}
    (h : ∀ c, (χ : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).cycles k
      →+ UnitAddCircle)
        (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).toCycles (k + 1) k
          c) = ((integrationCochain φ.val).hom c : UnitAddCircle)) :
    curvature χ = φ :=
  SmoothForm.eq_of_forall_coe_integrationCochain_eq k.succ_ne_zero fun c ↦ by
    rw [← apply_toCycles, h]

/-- **Integral periods.** The integral of the curvature of a differential character over every
smooth singular integral `(k + 1)`-cycle is an integer. -/
theorem curvature_mem_integralPeriodForms (χ : differentialCharacters I M k) :
    curvature χ ∈ integralPeriodForms I M (k + 1) := mem_integralPeriodForms_iff.2 fun z ↦ by
  have h := apply_toCycles χ
    (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).iCycles (k + 1) z)
  -- The boundary of a cycle vanishes.
  have hzero : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).toCycles
      (k + 1) k (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).iCycles
        (k + 1) z) = 0 :=
    moduleCat_iCycles_injective _ k (by simp)
  rwa [hzero, map_zero, eq_comm, UnitAddCircle.coe_eq_zero_iff] at h

/-- The curvature of a differential character is closed. -/
theorem curvature_mem_closedForms (χ : differentialCharacters I M k) :
    curvature χ ∈ closedForms I M (k + 1) :=
  mem_closedForms_of_mem_integralPeriodForms (curvature_mem_integralPeriodForms χ)

/-- **Flat characters.** A differential character has curvature zero exactly when it vanishes on
boundaries. -/
theorem curvature_eq_zero_iff {χ : differentialCharacters I M k} :
    curvature χ = 0 ↔
      ∀ c, (χ : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).cycles k
        →+ UnitAddCircle)
          (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).toCycles (k + 1)
            k c) = 0 := by
  refine ⟨fun h c ↦ ?_, fun h ↦ curvature_eq_of_forall fun c ↦ by simp [h c]⟩
  rw [apply_toCycles, h]
  simp

end Curvature

section OfForm

variable [IsManifold I 2 M]

/-- The differential character `z ↦ ∫_z η mod ℤ` of a smooth `k`-form `η`, as a homomorphism
from forms to differential characters. Its curvature is `dη`, by Stokes' theorem. -/
def ofForm : SmoothForm I M ℝ k →+ differentialCharacters I M k where
  toFun η := ⟨(QuotientAddGroup.mk' _).comp ((integrationCochain η.val).hom.toAddMonoidHom.comp
      (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).iCycles
        k).hom.toAddMonoidHom),
    mextDerivₗ I k η, fun c ↦ by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
        mextDerivₗ_apply, QuotientAddGroup.mk'_apply]
      rw [← integrationCochain_d_apply (η.isSmoothForm.of_le (by simp)),
        ← moduleCat_iCycles_toCycles_apply]⟩
  map_zero' := by
    ext z
    simp
  map_add' η θ := by
    ext z
    simp only [SmoothForm.integrationCochain_add]
    simp

/-- The character of a form evaluates a cycle by integrating the form over it modulo `ℤ`. -/
@[simp]
theorem ofForm_apply (η : SmoothForm I M ℝ k)
    (z : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).cycles k) :
    (ofForm η : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).cycles k
      →+ UnitAddCircle) z =
      ((integrationCochain (R := ℤ) η.val).hom
        (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).iCycles k z) :
          UnitAddCircle) := by
  simp [ofForm]

/-- The curvature of the character of a form `η` is `dη`. -/
@[simp]
theorem curvature_ofForm [IsManifold I ∞ M] [BoundarylessManifold I M]
    (η : SmoothForm I M ℝ k) : curvature (ofForm η) = mextDerivₗ I k η :=
  curvature_eq_of_forall fun c ↦ by
    rw [ofForm_apply, moduleCat_iCycles_toCycles_apply,
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
  toFun χ := ⟨(χ : ((smoothSingularSubcomplex J N : SSet).chainComplex (ModuleCat.of ℤ ℤ)).cycles k
      →+ UnitAddCircle).comp (cyclesMap (SSet.chainComplexMap (smoothSingularSubcomplexMap f hf)
        (ModuleCat.of ℤ ℤ)) k).hom.toAddMonoidHom, by
    obtain ⟨φ, hφ⟩ := mem_differentialCharacters_iff.mp χ.property
    refine ⟨SmoothForm.mpullback f hf φ, fun c ↦ ?_⟩
    rw [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
      moduleCat_cyclesMap_toCycles_apply, hφ, SmoothForm.coe_mpullback,
      integrationCochain_chainComplexMap_apply hf]⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The pullback of a character evaluates it on the pushforward of a cycle. -/
@[simp]
theorem pullback_apply (hf : ContMDiff I J ∞ f) (χ : differentialCharacters J N k)
    (z : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).cycles k) :
    (pullback hf χ : ((smoothSingularSubcomplex I M : SSet).chainComplex
      (ModuleCat.of ℤ ℤ)).cycles k →+ UnitAddCircle) z =
      (χ : ((smoothSingularSubcomplex J N : SSet).chainComplex (ModuleCat.of ℤ ℤ)).cycles k
        →+ UnitAddCircle)
        (cyclesMap (SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) (ModuleCat.of ℤ ℤ)) k
          z) :=
  (rfl)

variable (I M k) in
/-- Pulling characters back along the identity is the identity. -/
@[simp]
theorem pullback_id :
    pullback (I := I) (J := I) (M := M) (N := M) (f := id) (k := k) contMDiff_id =
      AddMonoidHom.id _ := by
  ext χ z
  rw [pullback_apply, AddMonoidHom.id_apply]
  exact congrArg _ (moduleCat_iCycles_injective _ k (by simp [smoothSingularSubcomplexMap_id]))

/-- Pulling characters back along a composite is the composite of the pullbacks, in the opposite
order. -/
theorem pullback_comp {E'' H'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''} {P : Type} [TopologicalSpace P]
    [ChartedSpace H'' P] [IsManifold K 1 P] {g : N → P} (hg : ContMDiff J K ∞ g)
    (hf : ContMDiff I J ∞ f) :
    pullback (k := k) (hg.comp hf) = (pullback hf).comp (pullback hg) := by
  ext χ z
  rw [AddMonoidHom.comp_apply, pullback_apply, pullback_apply, pullback_apply]
  refine congrArg _ (moduleCat_iCycles_injective _ k ?_)
  simp [smoothSingularSubcomplexMap_comp hg hf]

/-- The pullback of the character of a form is the character of the pulled-back form. -/
@[simp]
theorem pullback_ofForm [IsManifold I 2 M] [IsManifold J 2 N] (hf : ContMDiff I J ∞ f)
    (η : SmoothForm J N ℝ k) : pullback hf (ofForm η) = ofForm (SmoothForm.mpullback f hf η) := by
  ext z
  rw [pullback_apply, ofForm_apply, ofForm_apply, moduleCat_iCycles_cyclesMap_apply,
    SmoothForm.coe_mpullback, integrationCochain_chainComplexMap_apply hf]

/-- The curvature of the pullback of a character is the pullback of its curvature. -/
@[simp]
theorem curvature_pullback [IsManifold I ∞ M] [BoundarylessManifold I M] [IsManifold J ∞ N]
    [BoundarylessManifold J N] (hf : ContMDiff I J ∞ f) (χ : differentialCharacters J N k) :
    curvature (pullback hf χ) = SmoothForm.mpullback f hf (curvature χ) :=
  curvature_eq_of_forall fun c ↦ by
    rw [pullback_apply, moduleCat_cyclesMap_toCycles_apply, apply_toCycles,
      SmoothForm.coe_mpullback, integrationCochain_chainComplexMap_apply hf]

end Pullback

end differentialCharacters

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Hom
public import TauCeti.RingTheory.FormalGroup.TopNilpotentPoint.Basic

/-!
# Homomorphisms on topologically nilpotent points

A formal group homomorphism `f : F → G` induces an additive map `F(A) → G(A)` for every
complete Hausdorff linearly topologized coefficient algebra `A`. Its value is the convergent
series `∑ fₙ xⁿ`. Zero constant term ensures that this value is again topologically nilpotent.
These maps preserve identities and composition and commute with continuous algebra maps.
Consequently, a formal group isomorphism induces a natural additive equivalence on points.

The comparison with native power-series points identifies this evaluation action with formal
substitution. No topology or continuity assumption on the coefficient ring is needed: it is
given the discrete topology inside evaluation proofs.
-/

public section

open MvPowerSeries

namespace TauCeti

variable {R : Type*} [CommRing R] {F G H : FormalGroup R}
variable {A : Type*} [CommRing A] [Algebra R A] [UniformSpace A] [IsUniformAddGroup A]
  [CompleteSpace A] [T2Space A] [IsTopologicalRing A] [IsLinearTopology A A]

namespace FormalGroupHom

/-- Evaluate a homomorphism of formal group laws on topologically nilpotent points. -/
noncomputable def toTopNilpotentPointHom (f : FormalGroupHom F G) (A : Type*)
    [CommRing A] [Algebra R A] [UniformSpace A] [IsUniformAddGroup A]
    [CompleteSpace A] [T2Space A] [IsTopologicalRing A] [IsLinearTopology A A] :
    F.TopNilpotentPoint A →+ G.TopNilpotentPoint A :=
  AddMonoidHom.mk' (fun x ↦ ⟨let _ : UniformSpace R := ⊥
      PowerSeries.eval₂ (algebraMap R A) x.val f.toPowerSeries,
    let _ : UniformSpace R := ⊥
    (isTopologicallyNilpotent_eval₂_iff continuous_of_discreteTopology
      (PowerSeries.hasEval x.hasEval) f.toPowerSeries).2 (by
        simpa only [← PowerSeries.constantCoeff_eq, f.zero_constantCoeff, map_zero] using
          IsTopologicallyNilpotent.zero (R := A))⟩) (by
    intro x y
    let _ : UniformSpace R := ⊥
    let _ : ContinuousSMul R A := DiscreteTopology.instContinuousSMul R A
    have hxy := hasEval_finTwo x.hasEval y.hasEval
    have h := congrArg (eval₂ (algebraMap R A) ![x.val, y.val]) f.hom
    -- Express one-variable substitution and evaluation using the native constant family.
    simp only [PowerSeries.subst_def] at h
    rw [eval₂_subst (PowerSeries.HasSubst.const (.of_constantCoeff_zero F.zero_constantCoeff)) hxy,
      eval₂_subst (.toMvPowerSeries f.zero_constantCoeff) hxy] at h
    ext
    simp only [FormalGroup.TopNilpotentPoint.val_add_eq_eval₂]
    refine h.trans ?_
    congr 1
    funext i
    rw [PowerSeries.eval₂_toMvPowerSeries hxy]
    fin_cases i <;> rfl)

/-- The coordinate of the induced point is the value of the homomorphism's series. -/
theorem val_toTopNilpotentPointHom [UniformSpace R] [DiscreteUniformity R]
    (f : FormalGroupHom F G) (x : F.TopNilpotentPoint A) :
    (f.toTopNilpotentPointHom A x).val =
      PowerSeries.eval₂ (algebraMap R A) x.val f.toPowerSeries := by
  rw [DiscreteUniformity.eq_bot (X := R)]
  rfl

/-- The induced point is given by a convergent sum, without a topology on `R`. -/
theorem hasSum_val_toTopNilpotentPointHom (f : FormalGroupHom F G)
    (x : F.TopNilpotentPoint A) :
    HasSum (fun n ↦ PowerSeries.coeff n f.toPowerSeries • x.val ^ n)
      (f.toTopNilpotentPointHom A x).val := by
  let _ : UniformSpace R := ⊥
  rw [val_toTopNilpotentPointHom]
  simpa only [Algebra.smul_def] using
    PowerSeries.hasSum_eval₂ continuous_of_discreteTopology x.hasEval f.toPowerSeries

@[simp]
theorem toTopNilpotentPointHom_id :
    (id F).toTopNilpotentPointHom A = AddMonoidHom.id _ := by
  let _ : UniformSpace R := ⊥
  ext x
  simp [val_toTopNilpotentPointHom]

@[simp]
theorem toTopNilpotentPointHom_comp (g : FormalGroupHom G H) (f : FormalGroupHom F G) :
    (g.comp f).toTopNilpotentPointHom A =
      (g.toTopNilpotentPointHom A).comp (f.toTopNilpotentPointHom A) := by
  let _ : UniformSpace R := ⊥
  ext x
  simp only [AddMonoidHom.comp_apply, val_toTopNilpotentPointHom, comp_toPowerSeries,
    PowerSeries.eval₂, PowerSeries.subst_def]
  exact eval₂_subst f.hasSubst.const (PowerSeries.hasEval x.hasEval) g.toPowerSeries

variable {B : Type*} [CommRing B] [Algebra R B] [UniformSpace B] [IsUniformAddGroup B]
  [CompleteSpace B] [T2Space B] [IsTopologicalRing B] [IsLinearTopology B B]

/-- Evaluation of a formal group homomorphism commutes with continuous algebra maps. -/
theorem toTopNilpotentPointHom_map (f : FormalGroupHom F G) (φ : A →A[R] B)
    (x : F.TopNilpotentPoint A) :
    f.toTopNilpotentPointHom B (FormalGroup.TopNilpotentPoint.map F φ x) =
      FormalGroup.TopNilpotentPoint.map G φ (f.toTopNilpotentPointHom A x) := by
  let _ : UniformSpace R := ⊥
  ext
  simp only [val_toTopNilpotentPointHom, FormalGroup.TopNilpotentPoint.val_map]
  have h := congrFun (PowerSeries.comp_eval₂ (φ := algebraMap R A) continuous_of_discreteTopology
    x.hasEval (ε := (φ : A →+* B)) φ.cont) f.toPowerSeries
  have hφ : (φ : A →+* B).comp (algebraMap R A) = algebraMap R B := RingHom.ext φ.commutes
  simpa only [Function.comp_apply, hφ, RingHom.coe_coe] using h.symm

open scoped WithPiTopology in
/-- Evaluation on a power-series algebra agrees with the substitution action on native points. -/
@[simp]
theorem toTopNilpotentPointHom_pointEquiv [UniformSpace R] [DiscreteUniformity R]
    (f : FormalGroupHom F G) {σ : Type*} (x : F.Point σ) :
    f.toTopNilpotentPointHom (MvPowerSeries σ R) (F.pointEquivTopNilpotentPoint σ x) =
      G.pointEquivTopNilpotentPoint σ (f.applyPoint x) := by
  ext
  simp only [val_toTopNilpotentPointHom, FormalGroup.val_pointEquivTopNilpotentPoint,
    applyPoint_val, PowerSeries.eval₂, PowerSeries.subst_def, subst_eq_eval₂]

end FormalGroupHom

namespace FormalGroupIso

/-- A formal group isomorphism induces an additive equivalence on convergent points. -/
noncomputable def toTopNilpotentPointEquiv (f : FormalGroupIso F G) (A : Type*)
    [CommRing A] [Algebra R A] [UniformSpace A] [IsUniformAddGroup A]
    [CompleteSpace A] [T2Space A] [IsTopologicalRing A] [IsLinearTopology A A] :
    F.TopNilpotentPoint A ≃+ G.TopNilpotentPoint A where
  toFun := f.toHom.toTopNilpotentPointHom A
  invFun := f.invHom.toTopNilpotentPointHom A
  left_inv x := by
    have h := congrArg (fun g : FormalGroupHom F F ↦ g.toTopNilpotentPointHom A)
      f.invHom_comp_toHom
    simpa only [FormalGroupHom.toTopNilpotentPointHom_comp,
      FormalGroupHom.toTopNilpotentPointHom_id, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply] using DFunLike.congr_fun h x
  right_inv x := by
    have h := congrArg (fun g : FormalGroupHom G G ↦ g.toTopNilpotentPointHom A)
      f.toHom_comp_invHom
    simpa only [FormalGroupHom.toTopNilpotentPointHom_comp,
      FormalGroupHom.toTopNilpotentPointHom_id, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply] using DFunLike.congr_fun h x
  map_add' := map_add _

@[simp]
theorem toTopNilpotentPointEquiv_apply (f : FormalGroupIso F G) (x : F.TopNilpotentPoint A) :
    f.toTopNilpotentPointEquiv A x = f.toHom.toTopNilpotentPointHom A x := (rfl)

@[simp]
theorem toTopNilpotentPointEquiv_symm_apply (f : FormalGroupIso F G) (x : G.TopNilpotentPoint A) :
    (f.toTopNilpotentPointEquiv A).symm x = f.invHom.toTopNilpotentPointHom A x := (rfl)

@[simp]
theorem toTopNilpotentPointEquiv_refl :
    (refl F).toTopNilpotentPointEquiv A = AddEquiv.refl _ := by
  ext x
  simp

@[simp]
theorem toTopNilpotentPointEquiv_symm (f : FormalGroupIso F G) :
    f.symm.toTopNilpotentPointEquiv A = (f.toTopNilpotentPointEquiv A).symm := by
  ext x
  simp only [toTopNilpotentPointEquiv_apply, symm_toHom, toTopNilpotentPointEquiv_symm_apply]

@[simp]
theorem toTopNilpotentPointEquiv_trans (f : FormalGroupIso F G) (g : FormalGroupIso G H) :
    (f.trans g).toTopNilpotentPointEquiv A =
      (f.toTopNilpotentPointEquiv A).trans (g.toTopNilpotentPointEquiv A) := by
  ext x
  simp only [toTopNilpotentPointEquiv_apply, trans_toHom, AddEquiv.trans_apply,
    FormalGroupHom.toTopNilpotentPointHom_comp, AddMonoidHom.comp_apply]

end FormalGroupIso

end TauCeti

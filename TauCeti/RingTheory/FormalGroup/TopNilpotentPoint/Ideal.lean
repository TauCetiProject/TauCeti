/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.TopNilpotentPoint.Hom
import TauCeti.RingTheory.MvPowerSeries.Evaluation.IdealBounds
import TauCeti.RingTheory.PowerSeries.Evaluation

/-!
# Formal-group points in an ideal

For a formal group law `F` over `R` and a complete Hausdorff linearly topologized
`R`-algebra `A`, the points whose coordinates lie in an ideal `I` form the subgroup
`FormalGroup.idealPointSubgroup`. Homomorphisms of formal groups preserve these subgroups
and every power of `I`; an isomorphism preserves membership in each power in both directions.
For the additive law on an ideal of topologically nilpotent elements, the coordinate
identifies this subgroup with the ordinary additive group of `I`.

These restrictions allow integral formal coordinates, such as an integral logarithm, to
identify groups on a specified ideal rather than just on all topologically nilpotent elements.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.3 and IV.6.
-/

public section

namespace FormalGroup

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A] [T2Space A]
  [IsTopologicalRing A] [IsLinearTopology A A]

/-- The points of a formal group whose coordinates belong to the ideal `I`. -/
noncomputable def idealPointSubgroup (F : FormalGroup R) (I : Ideal A) :
    AddSubgroup (F.TopNilpotentPoint A) where
  carrier := {x | x.val ∈ I}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    let _ : UniformSpace R := ⊥
    rw [Set.mem_ofPred_eq, TopNilpotentPoint.val_add_eq_eval₂]
    refine MvPowerSeries.eval₂_mem_of_finite continuous_of_discreteTopology
      (MvPowerSeries.hasEval_finTwo x.hasEval y.hasEval) ?_ _ ?_
    · intro i
      fin_cases i
      · exact hx
      · exact hy
    · simp [F.zero_constantCoeff]
  neg_mem' {x} hx := by
    let _ : UniformSpace R := ⊥
    let _ : ContinuousSMul R A := DiscreteTopology.instContinuousSMul R A
    rw [Set.mem_ofPred_eq, TopNilpotentPoint.val_neg_eq_eval₂, ← PowerSeries.coe_aeval x.hasEval]
    exact PowerSeries.aeval_mem_of_constantCoeff_eq_zero x.hasEval F.constantCoeff_addInvX hx

@[simp]
theorem mem_idealPointSubgroup (F : FormalGroup R) (I : Ideal A)
    (x : F.TopNilpotentPoint A) : x ∈ F.idealPointSubgroup I ↔ x.val ∈ I := Iff.rfl

/-- Inclusion of ideals induces inclusion of their formal-group point subgroups. -/
theorem idealPointSubgroup_mono (F : FormalGroup R) :
    Monotone (F.idealPointSubgroup (A := A)) := by
  intro I J hIJ x hx
  exact (F.mem_idealPointSubgroup J x).2 (hIJ ((F.mem_idealPointSubgroup I x).1 hx))

/-- Two points in the ideal subgroup are equal exactly when their coordinates agree. -/
theorem idealPointSubgroup_ext_iff {F : FormalGroup R} {I : Ideal A}
    {x y : F.idealPointSubgroup I} : x = y ↔ x.val.val = y.val.val :=
  ⟨fun h ↦ congrArg (fun z : F.idealPointSubgroup I ↦ z.val.val) h,
    fun h ↦ Subtype.ext (TopNilpotentPoint.ext h)⟩

/-- The coordinates of the ideal subgroup are exactly the topologically nilpotent elements
of the ideal. -/
theorem range_val_idealPointSubgroup (F : FormalGroup R) (I : Ideal A) :
    Set.range (fun x : F.idealPointSubgroup I ↦ x.val.val) =
      (I : Set A) ∩ {s | IsTopologicallyNilpotent s} := by
  ext s
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(F.mem_idealPointSubgroup I x.val).1 x.property, x.val.hasEval⟩
  · rintro ⟨hs, hnil⟩
    exact ⟨⟨⟨s, hnil⟩, (F.mem_idealPointSubgroup I ⟨s, hnil⟩).2 hs⟩, rfl⟩

end FormalGroup

namespace Ideal

open FormalGroup

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A] [T2Space A]
  [IsTopologicalRing A] [IsLinearTopology A A]

/-- For the additive formal group, the points in an ideal of topologically nilpotent
elements form the ordinary additive group of that ideal. -/
noncomputable def additiveFormalGroupPointEquiv (I : Ideal A)
    (hI : ∀ x ∈ I, IsTopologicallyNilpotent x) :
    (𝔾ₐ (R := R)).idealPointSubgroup I ≃+ I where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, hI x.val x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' x y := by
    let _ : UniformSpace R := ⊥
    ext
    simp only [AddSubgroup.coe_add, TopNilpotentPoint.val_add_eq_eval₂, 𝔾ₐ_toPowerSeries,
      Submodule.coe_add]
    rw [← MvPowerSeries.coe_eval₂Hom continuous_of_discreteTopology
      (MvPowerSeries.hasEval_finTwo x.val.hasEval y.val.hasEval), map_add]
    simp [MvPowerSeries.coe_eval₂Hom]

@[simp]
theorem coe_additiveFormalGroupPointEquiv (I : Ideal A) (hI : ∀ x ∈ I, IsTopologicallyNilpotent x)
    (x : (𝔾ₐ (R := R)).idealPointSubgroup I) :
    (additiveFormalGroupPointEquiv (R := R) I hI x : A) = x.val.val := (rfl)

@[simp]
theorem val_additiveFormalGroupPointEquiv_symm (I : Ideal A)
    (hI : ∀ x ∈ I, IsTopologicallyNilpotent x) (x : I) :
    ((additiveFormalGroupPointEquiv (R := R) I hI).symm x).val.val = x := (rfl)

end Ideal

namespace TauCeti.FormalGroupHom

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A] [T2Space A]
  [IsTopologicalRing A] [IsLinearTopology A A] {F G : FormalGroup R}

/-- Evaluating a homomorphism of formal groups preserves membership of the coordinate in
any ideal, whether or not the ideal is closed or adic. -/
theorem val_toTopNilpotentPointHom_mem (f : FormalGroupHom F G)
    (I : Ideal A) {x : F.TopNilpotentPoint A} (hx : x.val ∈ I) :
    (f.toTopNilpotentPointHom A x).val ∈ I := by
  let _ : UniformSpace R := ⊥
  let _ : ContinuousSMul R A := DiscreteTopology.instContinuousSMul R A
  obtain ⟨c, hc⟩ := PowerSeries.exists_aeval_eq_mul_of_constantCoeff_eq_zero
    x.hasEval f.zero_constantCoeff
  rw [val_toTopNilpotentPointHom, ← PowerSeries.coe_aeval x.hasEval, hc]
  exact I.mul_mem_right c hx

/-- The action of a formal-group homomorphism on points restricts to each ideal. -/
noncomputable def toIdealPointHom (f : FormalGroupHom F G) (I : Ideal A) :
    F.idealPointSubgroup I →+ G.idealPointSubgroup I :=
  ((f.toTopNilpotentPointHom A).comp (F.idealPointSubgroup I).subtype).codRestrict _
    fun x ↦ f.val_toTopNilpotentPointHom_mem I x.property

@[simp]
theorem coe_toIdealPointHom (f : FormalGroupHom F G) (I : Ideal A)
    (x : F.idealPointSubgroup I) :
    (f.toIdealPointHom I x : G.TopNilpotentPoint A) = f.toTopNilpotentPointHom A x := (rfl)

end TauCeti.FormalGroupHom

namespace TauCeti.FormalGroupIso

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A] [T2Space A]
  [IsTopologicalRing A] [IsLinearTopology A A] {F G : FormalGroup R}

/-- A formal-group isomorphism restricts to an additive equivalence on points in each ideal. -/
noncomputable def toIdealPointEquiv (f : FormalGroupIso F G) (I : Ideal A) :
    F.idealPointSubgroup I ≃+ G.idealPointSubgroup I where
  toFun := f.toHom.toIdealPointHom I
  invFun := f.invHom.toIdealPointHom I
  left_inv x := by
    apply Subtype.ext
    simp only [FormalGroupHom.coe_toIdealPointHom,
      ← toTopNilpotentPointEquiv_apply, ← toTopNilpotentPointEquiv_symm_apply]
    exact (f.toTopNilpotentPointEquiv A).symm_apply_apply x.val
  right_inv x := by
    apply Subtype.ext
    simp only [FormalGroupHom.coe_toIdealPointHom,
      ← toTopNilpotentPointEquiv_apply, ← toTopNilpotentPointEquiv_symm_apply]
    exact (f.toTopNilpotentPointEquiv A).apply_symm_apply x.val
  map_add' := map_add _

@[simp]
theorem coe_toIdealPointEquiv (f : FormalGroupIso F G) (I : Ideal A)
    (x : F.idealPointSubgroup I) :
    (f.toIdealPointEquiv I x : G.TopNilpotentPoint A) =
      f.toHom.toTopNilpotentPointHom A x := (rfl)

@[simp]
theorem coe_toIdealPointEquiv_symm (f : FormalGroupIso F G) (I : Ideal A)
    (x : G.idealPointSubgroup I) :
    ((f.toIdealPointEquiv I).symm x : F.TopNilpotentPoint A) =
      f.invHom.toTopNilpotentPointHom A x := (rfl)

/-- The identity formal-group isomorphism restricts to the identity on ideal points. -/
@[simp]
theorem toIdealPointEquiv_refl (I : Ideal A) :
    (refl F).toIdealPointEquiv I = AddEquiv.refl _ := by
  apply AddEquiv.ext
  intro x
  apply Subtype.ext
  simp

/-- Restricting the inverse isomorphism gives the inverse equivalence on ideal points. -/
@[simp]
theorem toIdealPointEquiv_symm (f : FormalGroupIso F G) (I : Ideal A) :
    f.symm.toIdealPointEquiv I = (f.toIdealPointEquiv I).symm := by
  apply AddEquiv.ext
  intro x
  apply Subtype.ext
  simp

/-- Restriction to ideal points preserves composition of formal-group isomorphisms. -/
@[simp]
theorem toIdealPointEquiv_trans {H : FormalGroup R}
    (f : FormalGroupIso F G) (g : FormalGroupIso G H) (I : Ideal A) :
    (f.trans g).toIdealPointEquiv I = (f.toIdealPointEquiv I).trans (g.toIdealPointEquiv I) := by
  apply AddEquiv.ext
  intro x
  apply Subtype.ext
  simp only [coe_toIdealPointEquiv, trans_toHom, AddEquiv.trans_apply,
    FormalGroupHom.toTopNilpotentPointHom_comp, AddMonoidHom.comp_apply]

/-- A formal-group isomorphism preserves and reflects membership of the coordinate in any ideal. -/
@[simp]
theorem val_toTopNilpotentPointHom_mem_iff (f : FormalGroupIso F G) (I : Ideal A)
    (x : F.TopNilpotentPoint A) :
    (f.toHom.toTopNilpotentPointHom A x).val ∈ I ↔ x.val ∈ I := by
  constructor
  · intro hx
    have h := f.invHom.val_toTopNilpotentPointHom_mem I hx
    simpa only [← toTopNilpotentPointEquiv_apply, ← toTopNilpotentPointEquiv_symm_apply,
      AddEquiv.symm_apply_apply] using h
  · exact f.toHom.val_toTopNilpotentPointHom_mem I

end TauCeti.FormalGroupIso

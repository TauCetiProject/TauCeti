/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Monoidal.Rigid
public import TauCeti.CategoryTheory.Semisimple.GrothendieckRing
public import TauCeti.CategoryTheory.Simple.Rigid

/-!
# Duality in a finite semisimple rigid category

In a rigid monoidal abelian category with additive tensor product the right dual of a simple
object is simple (`TauCeti.simple_rightDual`), so duality acts on the simple isomorphism classes:
`TauCeti.SimpleClasses.dual` (in `TauCeti/CategoryTheory/Simple/Rigid.lean`) sends the class of
`X` to the class of `Xᘁ`. This file shows that this action is the involution of the Grothendieck
ring as a based ring, and that the fusion coefficients satisfy Frobenius reciprocity with respect
to it.

* **The involution.** If the category is moreover finite semisimple with simple tensor unit, then
  every simple object `X` is isomorphic to its double dual `Xᘁᘁ`. The coevaluation
  `𝟙_ C ⟶ X ⊗ Xᘁ` is nonzero, hence split by some `X ⊗ Xᘁ ⟶ 𝟙_ C`, and Frobenius reciprocity
  turns that splitting into a nonzero morphism `X ⟶ Xᘁᘁ` between simple objects. So the duality
  on simple classes is an involution, and the duality `[X] ↦ [Xᘁ]` of the Grothendieck ring is an
  involutive anti-automorphism permuting the basis of simple classes.
* **Frobenius reciprocity.** Over an algebraically closed field, with finite-dimensional morphism
  spaces, the fusion coefficients satisfy `N_{S* T}^U = N_{S U}^T` and `N_{S T*}^U = N_{U T}^S`,
  where `S*` is the dual class. Equivalently, the fusion matrix of `S*` is the transpose of that
  of `S`. The coefficient of the unit class is `N_{S T}^𝟙 = 1` if `S = T*` and `0` otherwise.
  In multiplicity form, `N_{S T}^U` is the multiplicity of `T` in `Sᘁ ⊗ U` and of `S` in
  `U ⊗ Tᘁ`.
* **Transitivity.** If the tensor unit is simple, the tensor product of nonzero objects is nonzero,
  so for all simple classes `S` and `U` some simple summand `T` of `Sᘁ ⊗ U` has `N_{S T}^U > 0`,
  and likewise on the other side. This is the transitivity of the based ring in the sense of
  Etingof–Gelaki–Nikshych–Ostrik. Consequently, the matrices of multiplication on either side by
  the sum of all simple classes have positive entries, which is what makes the Perron–Frobenius
  theorem for positive matrices apply to them.

No pivotal structure is used: the dual class is formed with right duals throughout, and
`ExactPairing S Sᘁ` supplies both reciprocity isomorphisms.

## Main declarations

* `TauCeti.nonempty_iso_rightDual_rightDual`: a simple object is isomorphic to its double dual.
* `TauCeti.SimpleClasses.dual_dual`: duality of simple classes is an involution.
* `TauCeti.SplitK0.dual_simpleBasis` and `TauCeti.SplitK0.dual_dual`: the duality of the
  Grothendieck ring permutes the simple basis and is an involution.
* `TauCeti.fusionCoeff_dual_left`, `TauCeti.fusionCoeff_dual_right` and
  `TauCeti.fusionCoeff_classOf_unit`: Frobenius reciprocity for fusion coefficients.
* `TauCeti.fusionMatrix_dual`: the fusion matrix of the dual class is the transpose.
* `TauCeti.fusionCoeff_eq_simpleMultiplicities_rightDual_tensor` and
  `TauCeti.fusionCoeff_eq_simpleMultiplicities_tensor_rightDual`: Frobenius reciprocity in
  multiplicity form.
* `TauCeti.exists_fusionCoeff_pos_right` and `TauCeti.exists_fusionCoeff_pos_left`: transitivity
  of the fusion rules.
* `TauCeti.sum_fusionCoeff_pos_left` and `TauCeti.sum_fusionCoeff_pos_right`: multiplication by
  the sum of all simple classes has a positive matrix.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§3.1, 3.3, 4.8,
  4.9
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace TauCeti

universe w w' v u

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [RigidCategory C]

section DoubleDual

variable [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)]

/-- In a finite semisimple rigid category with simple tensor unit, every simple object is
isomorphic to its double right dual. -/
theorem nonempty_iso_rightDual_rightDual (X : C) [Simple X] : Nonempty (X ≅ (Xᘁ)ᘁ) := by
  -- The coevaluation is nonzero, by the zigzag identity, so it has a retraction `r`.
  have := isSplitMono_of_nonzero_from_simple
    (coevaluation_ne_zero (Y := Xᘁ) (Simple.not_isZero X))
  -- Frobenius reciprocity turns `r : X ⊗ Xᘁ ⟶ 𝟙_ C` into `g : X ⟶ Xᘁᘁ`, nonzero since `r` is.
  let r := retraction (η_ X Xᘁ)
  let g : X ⟶ (Xᘁ)ᘁ := tensorRightHomEquiv X Xᘁ (Xᘁ)ᘁ (𝟙_ C) r ≫ (λ_ _).hom
  have hg : g ≠ 0 := by
    intro h
    have h' : tensorRightHomEquiv X Xᘁ (Xᘁ)ᘁ (𝟙_ C) r = 0 := by simpa [g] using h =≫ (λ_ _).inv
    have hr : r = 0 := by
      rw [← (tensorRightHomEquiv X Xᘁ (Xᘁ)ᘁ (𝟙_ C)).symm_apply_apply r, h']
      simp [tensorRightHomEquiv]
    have h0 : η_ X Xᘁ ≫ r = 0 := by rw [hr, comp_zero]
    exact id_nonzero (𝟙_ C) (by rw [← IsSplitMono.id (η_ X Xᘁ)]; exact h0)
  have := isIso_of_hom_simple hg
  exact ⟨asIso g⟩

end DoubleDual

namespace SimpleClasses

variable [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)]

/-- In a finite semisimple rigid category with simple tensor unit, duality of simple classes is
an involution. -/
@[simp]
theorem dual_dual (S : SimpleClasses C) : S.dual.dual = S := by
  obtain ⟨e⟩ := nonempty_iso_rightDual_rightDual S.repr
  rw [eq_iff_nonempty_iso]
  exact ⟨dualReprIso S.dual ≪≫ (dualReprIso S).rightAdjointMate.symm ≪≫ e.symm⟩

/-- Duality of simple classes is an involution. -/
theorem dual_involutive : Function.Involutive (dual : SimpleClasses C → SimpleClasses C) :=
  dual_dual

end SimpleClasses

namespace SplitK0

variable [EssentiallySmall.{w} C]

/-- The class of the representative of the dual simple class is the class of the right dual of the
representative. -/
@[simp]
theorem of_dual_repr (S : SimpleClasses C) : (of S.dual.repr : SplitK0 C) = of S.reprᘁ :=
  of_congr (SimpleClasses.dualReprIso S)

variable [IsFiniteSemisimpleCategory C]

/-- The duality of the Grothendieck ring sends the basis element of a simple class to the basis
element of the dual class. -/
theorem dual_simpleBasis (S : SimpleClasses C) :
    dual (simpleBasis C S) = simpleBasis C S.dual := by
  simp

variable [Simple (𝟙_ C)]

/-- In a finite semisimple rigid category with simple tensor unit, the duality of the Grothendieck
ring is an involution. -/
@[simp]
theorem dual_dual (x : SplitK0 C) : dual (dual x) = x := by
  have h : (dual.comp dual : SplitK0 C →+ SplitK0 C).toIntLinearMap = LinearMap.id :=
    (simpleBasis C).ext fun S ↦ by
      rw [AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.comp_apply, dual_simpleBasis,
        dual_simpleBasis, SimpleClasses.dual_dual, LinearMap.id_apply]
  simpa using LinearMap.congr_fun h x

/-- The duality of the Grothendieck ring is an involution. -/
theorem dual_involutive : Function.Involutive (dual : SplitK0 C → SplitK0 C) :=
  dual_dual

end SplitK0

section Fusion

variable (k : Type w') [Field k] [IsAlgClosed k] [Linear k C] [MonoidalLinear k C]
  [IsFiniteSemisimpleCategory C] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

/-- **Frobenius reciprocity** for fusion coefficients: `N_{S* T}^U = N_{S U}^T`, coming from
`(Sᘁ ⊗ T ⟶ U) ≃ (T ⟶ S ⊗ U)`. -/
theorem fusionCoeff_dual_left (S T U : SimpleClasses C) :
    fusionCoeff k S.dual T U = fusionCoeff k S U T := by
  rw [fusionCoeff_def, fusionCoeff_eq_finrank_hom,
    (Linear.homCongr k (whiskerRightIso (SimpleClasses.dualReprIso S) T.repr)
      (Iso.refl U.repr)).finrank_eq,
    (tensorLeftHomLinearEquiv k T.repr S.repr S.reprᘁ U.repr).finrank_eq]

/-- **Frobenius reciprocity** for fusion coefficients: `N_{S T*}^U = N_{U T}^S`, coming from
`(U ⊗ T ⟶ S) ≃ (U ⟶ S ⊗ Tᘁ)`. -/
theorem fusionCoeff_dual_right (S T U : SimpleClasses C) :
    fusionCoeff k S T.dual U = fusionCoeff k U T S := by
  rw [fusionCoeff_eq_finrank_hom, fusionCoeff_def,
    (tensorRightHomLinearEquiv k U.repr T.repr T.reprᘁ S.repr).finrank_eq,
    (Linear.homCongr k (Iso.refl U.repr)
      (whiskerLeftIso S.repr (SimpleClasses.dualReprIso T).symm)).finrank_eq]

/-- The fusion matrix of the dual class is the transpose of the fusion matrix:
`N_{S* T}^U = N_{S U}^T`. -/
@[simp]
theorem fusionMatrix_dual (S : SimpleClasses C) :
    fusionMatrix k S.dual = (fusionMatrix k S).transpose := by
  ext T U
  rw [fusionMatrix_apply, fusionCoeff_dual_left, Matrix.transpose_apply, fusionMatrix_apply]

/-- **Frobenius reciprocity** in multiplicity form: `N_{S T}^U` is the multiplicity of `T` in
`Sᘁ ⊗ U`, coming from `(Sᘁ ⊗ U ⟶ T) ≃ (U ⟶ S ⊗ T)`. -/
theorem fusionCoeff_eq_simpleMultiplicities_rightDual_tensor (S T U : SimpleClasses C) :
    fusionCoeff k S T U = simpleMultiplicities (S.reprᘁ ⊗ U.repr) T := by
  rw [fusionCoeff_eq_finrank_hom,
    ← (tensorLeftHomLinearEquiv k U.repr S.repr S.reprᘁ T.repr).finrank_eq,
    finrank_homTo_simple_eq_simpleMultiplicities, SimpleClasses.classOf_repr]

/-- **Frobenius reciprocity** in multiplicity form: `N_{S T}^U` is the multiplicity of `S` in
`U ⊗ Tᘁ`, coming from `(S ⊗ T ⟶ U) ≃ (S ⟶ U ⊗ Tᘁ)`. -/
theorem fusionCoeff_eq_simpleMultiplicities_tensor_rightDual (S T U : SimpleClasses C) :
    fusionCoeff k S T U = simpleMultiplicities (U.repr ⊗ T.reprᘁ) S := by
  rw [fusionCoeff_def, (tensorRightHomLinearEquiv k S.repr T.repr T.reprᘁ U.repr).finrank_eq,
    finrank_hom_simple_eq_simpleMultiplicities, SimpleClasses.classOf_repr]

section Transitive

variable [Simple (𝟙_ C)]

/-- **Transitivity** of the fusion rules: for simple classes `S` and `U` there is a simple class
`T` with `N_{S T}^U > 0`, that is, `U` is a summand of `S ⊗ T`. Any simple summand `T` of the
nonzero object `Sᘁ ⊗ U` will do. -/
theorem exists_fusionCoeff_pos_right (S U : SimpleClasses C) : ∃ T, 0 < fusionCoeff k S T U := by
  obtain ⟨T, hT⟩ := Finsupp.ne_iff.1 <| mt (simpleMultiplicities_eq_zero_iff _).1 <|
    not_isZero_tensorObj (Simple.not_isZero S.reprᘁ) (Simple.not_isZero U.repr)
  refine ⟨T, ?_⟩
  simpa [fusionCoeff_eq_simpleMultiplicities_rightDual_tensor, pos_iff_ne_zero] using hT

/-- **Transitivity** of the fusion rules: for simple classes `S` and `U` there is a simple class
`T` with `N_{T S}^U > 0`, that is, `U` is a summand of `T ⊗ S`. Any simple summand `T` of the
nonzero object `U ⊗ Sᘁ` will do. -/
theorem exists_fusionCoeff_pos_left (S U : SimpleClasses C) : ∃ T, 0 < fusionCoeff k T S U := by
  obtain ⟨T, hT⟩ := Finsupp.ne_iff.1 <| mt (simpleMultiplicities_eq_zero_iff _).1 <|
    not_isZero_tensorObj (Simple.not_isZero U.repr) (Simple.not_isZero S.reprᘁ)
  refine ⟨T, ?_⟩
  simpa [fusionCoeff_eq_simpleMultiplicities_tensor_rightDual, pos_iff_ne_zero] using hT

variable [Fintype (SimpleClasses C)]

/-- The matrix of multiplication on the left by the sum of all simple classes has positive
entries: `∑ S, N_{S T}^U > 0` for all simple classes `T` and `U`. -/
theorem sum_fusionCoeff_pos_left (T U : SimpleClasses C) : 0 < ∑ S, fusionCoeff k S T U := by
  obtain ⟨S, hS⟩ := exists_fusionCoeff_pos_left k T U
  exact Finset.sum_pos' (fun _ _ ↦ Nat.zero_le _) ⟨S, Finset.mem_univ S, hS⟩

/-- The matrix of multiplication on the right by the sum of all simple classes has positive
entries: `∑ S, N_{T S}^U > 0` for all simple classes `T` and `U`. -/
theorem sum_fusionCoeff_pos_right (T U : SimpleClasses C) : 0 < ∑ S, fusionCoeff k T S U := by
  obtain ⟨S, hS⟩ := exists_fusionCoeff_pos_right k T U
  exact Finset.sum_pos' (fun _ _ ↦ Nat.zero_le _) ⟨S, Finset.mem_univ S, hS⟩

end Transitive

omit [IsFiniteSemisimpleCategory C] in
/-- The multiplicity of the tensor unit in `S ⊗ T` is `1` if `S` is the dual class of `T`, and `0`
otherwise: `N_{S T}^𝟙 = δ_{S, T*}`. -/
@[simp]
theorem fusionCoeff_classOf_unit [Simple (𝟙_ C)] [DecidableEq (SimpleClasses C)]
    (S T : SimpleClasses C) :
    fusionCoeff k S T (SimpleClasses.classOf (𝟙_ C)) = if S = T.dual then 1 else 0 := by
  rw [fusionCoeff_def,
    (Linear.homCongr k (Iso.refl _) (SimpleClasses.classOfReprIso (𝟙_ C))).finrank_eq,
    (tensorRightHomLinearEquiv k S.repr T.repr T.reprᘁ (𝟙_ C)).finrank_eq,
    (Linear.homCongr k (Iso.refl S.repr) (λ_ T.reprᘁ)).finrank_eq, finrank_hom_simple_simple]
  by_cases h : S = T.dual
  · rw [ite_eq_left ((SimpleClasses.eq_dual_iff T S).1 h), ite_eq_left h]
  · rw [ite_eq_right (mt (SimpleClasses.eq_dual_iff T S).2 h), ite_eq_right h]

end Fusion

end TauCeti

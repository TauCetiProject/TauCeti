/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Center.Abelian
public import TauCeti.CategoryTheory.Monoidal.Center.Induction.LeftAdjunction
public import TauCeti.CategoryTheory.Monoidal.Center.Pivotal
public import TauCeti.CategoryTheory.Monoidal.Center.Simple
public import TauCeti.CategoryTheory.Monoidal.Pivotal.GlobalDim
public import TauCeti.CategoryTheory.Semisimple.Finite
public import TauCeti.CategoryTheory.Semisimple.Split
import TauCeti.CategoryTheory.Monoidal.Pivotal.Character

/-!
# Semisimplicity and global dimension of the Drinfeld centre

Let `C` be a fusion category over an algebraically closed field `k`, so that induction
`Center.induction k C : C ⥤ Center C` is both right adjoint (`forgetInductionAdjunction k C`) and
left adjoint (`inductionForgetAdjunction k C`) to `Center.forget C : Center C ⥤ C`.

Composing the unit of `forgetInductionAdjunction k C` with the counit of
`inductionForgetAdjunction k C` at any `Z : Center C` cancels the half-braiding on every simple
summand `S.repr ⊗ Z.1 ⊗ S.reprᘁ` and leaves scalar multiplication by `∑ S, η_S ≫ ε'_S`, where
`ε'_S` is the evaluation of `TauCeti.simpleOppositeExactPairing S.repr`. By
`TauCeti.squaredNorm_simpleDoubleDualIso` and `TauCeti.normGlobalDim_congr`, this sum equals the
pivot-free global dimension `TauCeti.normGlobalDim C a` for any family of double-dual isomorphisms
`a S : S.repr ≅ S.reprᘁᘁ`
(`forgetInductionAdjunction_unit_app_comp_inductionForgetAdjunction_counit_app`).

This yields the arbitrary-characteristic structural theorems of Etingof–Nikshych–Ostrik and Müger
on the Drinfeld centre:

* **Finiteness of simple classes**: whenever `Center C` is finite semisimple, faithfulness of
  `Center.forget C` and the right adjunction `forgetInductionAdjunction k C` imply that `Center C`
  has finitely many simple isomorphism classes (`finite_simpleClasses`), without assuming
  simplicity of `𝟙_ C` or a pivotal structure.
* **Pivot-free Maschke's theorem for the centre**: if `normGlobalDim C a ≠ 0`, every component of
  `(forgetInductionAdjunction k C).unit` is a split monomorphism and every component of
  `(inductionForgetAdjunction k C).counit` is a split epimorphism, so `Center C` is finite
  semisimple (`isFiniteSemisimpleCategory_of_normGlobalDim_ne_zero`) and has finitely many simple
  isomorphism classes (`finite_simpleClasses_of_normGlobalDim_ne_zero`).
* **Pivotal specialization and global dimension of the centre**: when `C` is pivotal,
  `TauCeti.normGlobalDim_pivotalIsoApp` identifies `normGlobalDim C` with `TauCeti.globalDim C`,
  giving the `globalDim C` corollaries (`isFiniteSemisimpleCategory_of_globalDim_ne_zero`,
  `finite_simpleClasses_of_globalDim_ne_zero`). Moreover, for every `X : C`, the left and right
  dimensions of `(induction k C).obj X` are `globalDim C` times those of `X`
  (`leftDim_induction_obj_f`, `rightDim_induction_obj_f`). When `Center C` is finite semisimple
  with finitely many simple classes, Frobenius reciprocity
  (`simpleMultiplicities_inductionCenterObj_apply`, `simpleMultiplicities_induction_obj_apply`)
  expands the dimensions of induced simples over the simple classes of `Center C` to give
  `dim(Center C) = (dim C)²` (`endAlgEquivOfSimple_globalDim`, `globalDim_f`).

The nonvanishing assumption `normGlobalDim C a ≠ 0` cannot be dropped in positive characteristic:
over an algebraically closed field `k` of characteristic `p > 0`, the category of `ℤ/p`-graded
`k`-vector spaces has `dim C = p = 0` and non-semisimple Drinfeld centre.

## Main declarations

* `CategoryTheory.Center.finite_simpleClasses`: whenever `Center C` is finite semisimple, it has
  finitely many isomorphism classes of simple objects;
* `CategoryTheory.Center.simpleMultiplicities_inductionCenterObj_apply` and
  `CategoryTheory.Center.simpleMultiplicities_induction_obj_apply`: Frobenius reciprocity for
  simple multiplicities of `inductionCenterObj k X` and `(induction k C).obj X`;
* `Center.forgetInductionAdjunction_unit_app_f_comp_inductionForgetAdjunction_counit_app_f` and
  `Center.forgetInductionAdjunction_unit_app_comp_inductionForgetAdjunction_counit_app`:
  the pivot-free Maschke averaging composite equals scalar multiplication by `normGlobalDim C a`;
* `CategoryTheory.Center.isSplitMono_forgetInductionAdjunction_unit_app_of_normGlobalDim_ne_zero`,
  `CategoryTheory.Center.isSplitEpi_inductionForgetAdjunction_counit_app_of_normGlobalDim_ne_zero`,
  `CategoryTheory.Center.isFiniteSemisimpleCategory_of_normGlobalDim_ne_zero`, and
  `CategoryTheory.Center.finite_simpleClasses_of_normGlobalDim_ne_zero`: pivot-free Maschke
  splittings, semisimplicity, and finiteness of simple classes when `normGlobalDim C a ≠ 0`;
* `Center.forgetInductionAdjunction_unit_app_comp_inductionForgetAdjunction_counit_app_of_pivotal`,
  `CategoryTheory.Center.isSplitMono_forgetInductionAdjunction_unit_app_of_globalDim_ne_zero`,
  `CategoryTheory.Center.isSplitEpi_inductionForgetAdjunction_counit_app_of_globalDim_ne_zero`,
  `CategoryTheory.Center.isFiniteSemisimpleCategory_of_globalDim_ne_zero`, and
  `CategoryTheory.Center.finite_simpleClasses_of_globalDim_ne_zero`: pivotal corollaries when
  `globalDim C ≠ 0`;
* `CategoryTheory.Center.leftDim_induction_obj_f` and
  `CategoryTheory.Center.rightDim_induction_obj_f`: `dim((induction k C).obj X) = dim(C) · dim(X)`;
* `CategoryTheory.Center.endAlgEquivOfSimple_globalDim` and `CategoryTheory.Center.globalDim_f`:
  `globalDim (Center C)` equals `(globalDim C)²`.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005),
  Theorem 2.15
* M. Müger, *From subfactors to categories and topology II: The quantum double of tensor
  categories and subfactors*, J. Pure Appl. Algebra **180** (2003), Theorem 3.16
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], Theorem 9.3.2
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory TauCeti

universe w v u

namespace CategoryTheory.Center

attribute [local instance] Abelian.hasFiniteBiproducts

/-- If `C` is a rigid `k`-linear finite semisimple abelian monoidal category over an algebraically
closed field `k` with finitely many simple isomorphism classes and finite-dimensional morphism
spaces, and `Center C` is finite semisimple, then `Center C` has finitely many isomorphism classes
of simple objects. -/
theorem finite_simpleClasses (k : Type w) [Field k] [IsAlgClosed k]
    {C : Type u} [Category.{v} C] [Abelian C] [Linear k C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C]
    [IsFiniteSemisimpleCategory C] [Finite (SimpleClasses C)]
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] [IsFiniteSemisimpleCategory (Center C)] :
    Finite (SimpleClasses (Center C)) := by
  classical
  let _ := Fintype.ofFinite (SimpleClasses C)
  exact (forget C).finite_simpleClasses_of_faithful_leftAdjoint (forgetInductionAdjunction k C)

section Fusion

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C]
  [IsFiniteSemisimpleCategory C] [Fintype (SimpleClasses C)]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

/-- **Frobenius reciprocity for centre induction**: when `Center C` is finite semisimple, the
multiplicity of a simple isomorphism class `M` of `Center C` in `inductionCenterObj k X` (for a
simple object `X : C`) equals the multiplicity of the class of `X` in `M.repr.1`. -/
@[simp]
theorem simpleMultiplicities_inductionCenterObj_apply [IsFiniteSemisimpleCategory (Center C)]
    (X : C) [Simple X] (M : SimpleClasses (Center C)) :
    simpleMultiplicities (inductionCenterObj k X) M =
      simpleMultiplicities M.repr.1 (SimpleClasses.classOf X) := by
  have : ∀ Z W : Center C, FiniteDimensional k (Z ⟶ W) := inferInstance
  let e : ((forget C).obj M.repr ⟶ X) ≃ₗ[k] (M.repr ⟶ (induction k C).obj X) :=
    ((forgetInductionAdjunction k C).homAddEquiv M.repr X).toLinearEquiv fun r g ↦ by
      rw [Adjunction.homAddEquiv_apply, Adjunction.homAddEquiv_apply,
        Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_smul, Linear.comp_smul]
  have hfin := e.finrank_eq.symm
  rw [induction_obj] at hfin
  rw [finrank_hom_simple_eq_simpleMultiplicities k, SimpleClasses.classOf_repr,
    forget_obj, finrank_homTo_simple_eq_simpleMultiplicities k] at hfin
  exact hfin

/-- **Frobenius reciprocity for centre induction**: when `Center C` is finite semisimple, the
multiplicity of a simple isomorphism class `M` of `Center C` in `(induction k C).obj X` (for a
simple object `X : C`) equals the multiplicity of the class of `X` in `M.repr.1`. -/
theorem simpleMultiplicities_induction_obj_apply [IsFiniteSemisimpleCategory (Center C)]
    (X : C) [Simple X] (M : SimpleClasses (Center C)) :
    simpleMultiplicities ((induction k C).obj X) M =
      simpleMultiplicities M.repr.1 (SimpleClasses.classOf X) := by
  rw [induction_obj, simpleMultiplicities_inductionCenterObj_apply]

variable [Simple (𝟙_ C)]

/-- Expanding `u ≫ c` across the biproduct decomposition of `inductionObj A` when the components of
`u` and `c` are given by the unit of `forgetInductionAdjunction` and counit of
`inductionForgetAdjunction`. -/
private theorem inductionObj_comp_eq_sum {A : C} (b : HalfBraiding A)
    {u : A ⟶ inductionObj A} {c : inductionObj A ⟶ A}
    (hu : ∀ S : SimpleClasses C, u ≫ biproduct.π (inductionSummand A) S =
      (ρ_ A).inv ≫ A ◁ η_ S.repr S.reprᘁ ≫ (α_ A S.repr S.reprᘁ).inv ≫
        (b.β S.repr).hom ▷ S.reprᘁ ≫ (α_ S.repr A S.reprᘁ).hom)
    (hc : ∀ S : SimpleClasses C, biproduct.ι (inductionSummand A) S ≫ c =
      (α_ S.repr A S.reprᘁ).inv ≫ (b.β S.repr).inv ▷ S.reprᘁ ≫
        (α_ A S.repr S.reprᘁ).hom ≫
        A ◁ @ExactPairing.evaluation C _ _ S.reprᘁ S.repr (simpleOppositeExactPairing S.repr) ≫
        (ρ_ A).hom) :
    u ≫ c =
      (ρ_ A).inv ≫
        A ◁ (∑ S : SimpleClasses C,
          η_ S.repr S.reprᘁ ≫
            @ExactPairing.evaluation C _ _ S.reprᘁ S.repr (simpleOppositeExactPairing S.repr)) ≫
        (ρ_ A).hom := by
  calc u ≫ c
      = u ≫ (∑ S : SimpleClasses C,
          biproduct.π (inductionSummand A) S ≫ biproduct.ι (inductionSummand A) S) ≫ c := by
        rw [biproduct.total, Category.id_comp]
    _ = ∑ S : SimpleClasses C,
          (u ≫ biproduct.π (inductionSummand A) S) ≫
          (biproduct.ι (inductionSummand A) S ≫ c) := by
        simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
    _ = _ := by
        simp only [hu, hc, whiskerLeft_sum, Preadditive.comp_sum, Preadditive.sum_comp,
          Category.assoc, Iso.hom_inv_id_assoc]
        refine Finset.sum_congr rfl fun S _ ↦ ?_
        rw [← comp_whiskerRight_assoc, Iso.hom_inv_id, id_whiskerRight, Category.id_comp,
          Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc]

/-- On underlying objects in a fusion category `C` over an algebraically closed field `k`, the
composite of the unit of `forgetInductionAdjunction` with the counit of `inductionForgetAdjunction`
at `Z : Center C` acts as multiplication by the pivot-free global dimension
`TauCeti.normGlobalDim C a`, for any family `a S : S.repr ≅ S.reprᘁᘁ`. -/
@[reassoc]
theorem forgetInductionAdjunction_unit_app_f_comp_inductionForgetAdjunction_counit_app_f
    (a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) (Z : Center C) :
    ((forgetInductionAdjunction k C).unit.app Z).f ≫
        ((inductionForgetAdjunction k C).counit.app Z).f =
      (ρ_ Z.1).inv ≫ Z.1 ◁ normGlobalDim C a ≫ (ρ_ Z.1).hom := by
  refine (inductionObj_comp_eq_sum Z.2 (forgetInductionAdjunction_unit_app_f_comp_π k C Z)
    (ι_comp_inductionForgetAdjunction_counit_app_f k C Z)).trans ?_
  have hsum : (∑ S : SimpleClasses C,
        η_ S.repr S.reprᘁ ≫
          @ExactPairing.evaluation C _ _ S.reprᘁ S.repr (simpleOppositeExactPairing S.repr)) =
      normGlobalDim C a := by
    simp_rw [← squaredNorm_simpleDoubleDualIso]
    rw [← normGlobalDim_def]
    exact normGlobalDim_congr C k (fun S ↦ bijective_algebraMap_end_of_simple k S.repr)
      (fun S ↦ simpleDoubleDualIso S.repr) a
  rw [hsum]

/-- In a fusion category `C` over an algebraically closed field `k`, the composite of the unit of
`forgetInductionAdjunction` with the counit of `inductionForgetAdjunction` at `Z : Center C` is
scalar multiplication by the pivot-free global dimension `TauCeti.normGlobalDim C a` (read in `k`),
for any family `a S : S.repr ≅ S.reprᘁᘁ`. -/
@[reassoc]
theorem forgetInductionAdjunction_unit_app_comp_inductionForgetAdjunction_counit_app
    (a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) (Z : Center C) :
    (forgetInductionAdjunction k C).unit.app Z ≫
        (inductionForgetAdjunction k C).counit.app Z =
      endAlgEquivOfSimple k (𝟙_ C) (End.of (normGlobalDim C a)) • 𝟙 Z := by
  refine Center.ext _ _ ?_
  rw [comp_f, smul_f, id_f,
    forgetInductionAdjunction_unit_app_f_comp_inductionForgetAdjunction_counit_app_f k a Z]
  set d := endAlgEquivOfSimple k (𝟙_ C) (End.of (normGlobalDim C a))
  have hg : normGlobalDim C a = d • 𝟙 (𝟙_ C) :=
    (endAlgEquivOfSimple_smul_id (k := k) (End.of (normGlobalDim C a))).symm
  rw [hg, MonoidalLinear.whiskerLeft_smul, whiskerLeft_id, Linear.smul_comp, Linear.comp_smul,
    Category.id_comp, Iso.inv_hom_id]

/-- In a fusion category `C` over an algebraically closed field `k` with
`TauCeti.normGlobalDim C a ≠ 0` (for some family `a S : S.repr ≅ S.reprᘁᘁ`), every component of
`(forgetInductionAdjunction k C).unit` is a split monomorphism. -/
theorem isSplitMono_forgetInductionAdjunction_unit_app_of_normGlobalDim_ne_zero
    {a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ}
    (hdim : normGlobalDim C a ≠ 0) (Z : Center C) :
    IsSplitMono ((forgetInductionAdjunction k C).unit.app Z) := by
  set d := endAlgEquivOfSimple k (𝟙_ C) (End.of (normGlobalDim C a))
  have hd : d ≠ 0 := fun h ↦
    hdim (by simpa using (endAlgEquivOfSimple_apply_eq_iff (End.of (normGlobalDim C a)) 0).1 h)
  exact IsSplitMono.mk'
    { retraction := d⁻¹ • (inductionForgetAdjunction k C).counit.app Z
      id := by
        rw [Linear.comp_smul,
          forgetInductionAdjunction_unit_app_comp_inductionForgetAdjunction_counit_app k a,
          smul_smul, inv_mul_cancel₀ hd, one_smul]
        rfl }

/-- In a fusion category `C` over an algebraically closed field `k` with
`TauCeti.normGlobalDim C a ≠ 0` (for some family `a S : S.repr ≅ S.reprᘁᘁ`), every component of
`(inductionForgetAdjunction k C).counit` is a split epimorphism. -/
theorem isSplitEpi_inductionForgetAdjunction_counit_app_of_normGlobalDim_ne_zero
    {a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ}
    (hdim : normGlobalDim C a ≠ 0) (Z : Center C) :
    IsSplitEpi ((inductionForgetAdjunction k C).counit.app Z) := by
  set d := endAlgEquivOfSimple k (𝟙_ C) (End.of (normGlobalDim C a))
  have hd : d ≠ 0 := fun h ↦
    hdim (by simpa using (endAlgEquivOfSimple_apply_eq_iff (End.of (normGlobalDim C a)) 0).1 h)
  exact IsSplitEpi.mk'
    { section_ := d⁻¹ • (forgetInductionAdjunction k C).unit.app Z
      id := by
        rw [Linear.smul_comp,
          forgetInductionAdjunction_unit_app_comp_inductionForgetAdjunction_counit_app k a,
          smul_smul, inv_mul_cancel₀ hd, one_smul]
        rfl }

include k in
/-- **Maschke's theorem for the Drinfeld centre** (Etingof–Nikshych–Ostrik, Müger): if `C` is a
fusion category over an algebraically closed field `k` with `TauCeti.normGlobalDim C a ≠ 0` (for
some family `a S : S.repr ≅ S.reprᘁᘁ`), then `Center C` is finite semisimple. -/
theorem isFiniteSemisimpleCategory_of_normGlobalDim_ne_zero
    {a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ}
    (hdim : normGlobalDim C a ≠ 0) :
    IsFiniteSemisimpleCategory (Center C) := by
  have (Z : Center C) : IsSplitMono ((forgetInductionAdjunction k C).unit.app Z) :=
    isSplitMono_forgetInductionAdjunction_unit_app_of_normGlobalDim_ne_zero k hdim Z
  exact IsFiniteSemisimpleCategory.of_natTrans (forget C) (induction k C)
    (forgetInductionAdjunction k C).unit

include k in
/-- If `C` is a fusion category over an algebraically closed field `k` with
`TauCeti.normGlobalDim C a ≠ 0` (for some family `a S : S.repr ≅ S.reprᘁᘁ`), then `Center C` has
finitely many isomorphism classes of simple objects. -/
theorem finite_simpleClasses_of_normGlobalDim_ne_zero
    {a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ}
    (hdim : normGlobalDim C a ≠ 0) :
    Finite (SimpleClasses (Center C)) := by
  have := isFiniteSemisimpleCategory_of_normGlobalDim_ne_zero k hdim
  exact finite_simpleClasses k

section Pivotal

variable [PivotalCategory C]

/-- On underlying objects in a pivotal fusion category `C` over an algebraically closed field `k`,
the composite of the unit of `forgetInductionAdjunction` with the counit of
`inductionForgetAdjunction` at `Z : Center C` is multiplication by `globalDim C`. -/
@[reassoc]
theorem forgetInductionAdjunction_unit_app_f_comp_inductionForgetAdjunction_counit_app_f_of_pivotal
    (Z : Center C) :
    ((forgetInductionAdjunction k C).unit.app Z).f ≫
        ((inductionForgetAdjunction k C).counit.app Z).f =
      (ρ_ Z.1).inv ≫ Z.1 ◁ globalDim C ≫ (ρ_ Z.1).hom := by
  rw [← normGlobalDim_pivotalIsoApp C]
  exact forgetInductionAdjunction_unit_app_f_comp_inductionForgetAdjunction_counit_app_f
    k (fun S ↦ pivotalIsoApp S.repr) Z

/-- In a pivotal fusion category `C` over an algebraically closed field `k`, the composite of the
unit of `forgetInductionAdjunction` with the counit of `inductionForgetAdjunction` at
`Z : Center C` is scalar multiplication by `globalDim C` (read in `k`). -/
@[reassoc]
theorem forgetInductionAdjunction_unit_app_comp_inductionForgetAdjunction_counit_app_of_pivotal
    (Z : Center C) :
    (forgetInductionAdjunction k C).unit.app Z ≫
        (inductionForgetAdjunction k C).counit.app Z =
      endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C)) • 𝟙 Z := by
  rw [← normGlobalDim_pivotalIsoApp C]
  exact forgetInductionAdjunction_unit_app_comp_inductionForgetAdjunction_counit_app
    k (fun S ↦ pivotalIsoApp S.repr) Z

/-- In a pivotal fusion category `C` over an algebraically closed field `k` with `globalDim C ≠ 0`,
every component of `(forgetInductionAdjunction k C).unit` is a split monomorphism. -/
theorem isSplitMono_forgetInductionAdjunction_unit_app_of_globalDim_ne_zero
    (hdim : globalDim C ≠ 0) (Z : Center C) :
    IsSplitMono ((forgetInductionAdjunction k C).unit.app Z) :=
  isSplitMono_forgetInductionAdjunction_unit_app_of_normGlobalDim_ne_zero k
    (a := fun S ↦ pivotalIsoApp S.repr) (by rwa [normGlobalDim_pivotalIsoApp]) Z

/-- In a pivotal fusion category `C` over an algebraically closed field `k` with `globalDim C ≠ 0`,
every component of `(inductionForgetAdjunction k C).counit` is a split epimorphism. -/
theorem isSplitEpi_inductionForgetAdjunction_counit_app_of_globalDim_ne_zero
    (hdim : globalDim C ≠ 0) (Z : Center C) :
    IsSplitEpi ((inductionForgetAdjunction k C).counit.app Z) :=
  isSplitEpi_inductionForgetAdjunction_counit_app_of_normGlobalDim_ne_zero k
    (a := fun S ↦ pivotalIsoApp S.repr) (by rwa [normGlobalDim_pivotalIsoApp]) Z

include k in
/-- **Maschke's theorem for the Drinfeld centre** (Etingof–Nikshych–Ostrik, Müger): if `C` is a
pivotal fusion category over an algebraically closed field `k` with `globalDim C ≠ 0`, then
`Center C` is finite semisimple. -/
theorem isFiniteSemisimpleCategory_of_globalDim_ne_zero (hdim : globalDim C ≠ 0) :
    IsFiniteSemisimpleCategory (Center C) :=
  isFiniteSemisimpleCategory_of_normGlobalDim_ne_zero k
    (a := fun S ↦ pivotalIsoApp S.repr) (by rwa [normGlobalDim_pivotalIsoApp])

include k in
/-- If `C` is a pivotal fusion category over an algebraically closed field `k` with
`globalDim C ≠ 0`, then `Center C` has finitely many isomorphism classes of simple objects. -/
theorem finite_simpleClasses_of_globalDim_ne_zero (hdim : globalDim C ≠ 0) :
    Finite (SimpleClasses (Center C)) :=
  finite_simpleClasses_of_normGlobalDim_ne_zero k
    (a := fun S ↦ pivotalIsoApp S.repr) (by rwa [normGlobalDim_pivotalIsoApp])

/-- In a pivotal fusion category `C` over an algebraically closed field `k`, the left dimension of
`(induction k C).obj X`, read in `C`, is `globalDim C ≫ leftDim X`. -/
theorem leftDim_induction_obj_f (X : C) :
    (leftDim ((induction k C).obj X)).f = globalDim C ≫ leftDim X := by
  have : EssentiallySmall.{max u v} C := essentiallySmall_of_small_of_locallySmall C
  refine (leftDim_f ((induction k C).obj X)).trans ?_
  rw [induction_obj, inductionCenterObj_fst, leftDim_biproduct, globalDim_eq_sum_leftDimChar_smul k,
    ← SplitK0.leftDimChar_of_smul_id k X, Linear.smul_comp, Linear.comp_smul,
    Category.id_comp, smul_smul, Finset.sum_mul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun T _ ↦ ?_
  rw [← SplitK0.leftDimChar_of_smul_id k (inductionSummand X T)]
  congr 1
  simp only [inductionSummand, ← SplitK0.of_mul_of, map_mul]
  ring

/-- In a pivotal fusion category `C` over an algebraically closed field `k`, the right dimension of
`(induction k C).obj X`, read in `C`, is `globalDim C ≫ rightDim X`. -/
theorem rightDim_induction_obj_f (X : C) :
    (rightDim ((induction k C).obj X)).f = globalDim C ≫ rightDim X := by
  have : EssentiallySmall.{max u v} C := essentiallySmall_of_small_of_locallySmall C
  refine (rightDim_f ((induction k C).obj X)).trans ?_
  rw [induction_obj, inductionCenterObj_fst, rightDim_biproduct,
    globalDim_eq_sum_leftDimChar_smul k, ← SplitK0.rightDimChar_of_smul_id k X,
    Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul, Finset.sum_mul,
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun T _ ↦ ?_
  rw [← SplitK0.rightDimChar_of_smul_id k (inductionSummand X T)]
  congr 1
  simp only [inductionSummand, ← SplitK0.of_mul_of, map_mul, ← SplitK0.dual_of,
    SplitK0.leftDimChar_dual, SplitK0.rightDimChar_dual]
  ring

/-- Weighted sum of left dimensions of simple objects of `Center C` by their multiplicity over a
simple class `S` of `C`, evaluated via Frobenius reciprocity on `(induction k C).obj S.repr`. -/
private theorem sum_simpleMultiplicities_mul_leftDimChar_eq
    [IsFiniteSemisimpleCategory (Center C)] [Fintype (SimpleClasses (Center C))]
    [EssentiallySmall.{max u v} C] [EssentiallySmall.{max u v} (Center C)]
    (S : SimpleClasses C) :
    ∑ M : SimpleClasses (Center C),
        (simpleMultiplicities M.repr.1 S : k) *
          SplitK0.leftDimChar k (Center C) (SplitK0.of M.repr) =
      endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C)) *
        SplitK0.leftDimChar k C (SplitK0.of S.repr) := by
  calc ∑ M : SimpleClasses (Center C),
          (simpleMultiplicities M.repr.1 S : k) *
            SplitK0.leftDimChar k (Center C) (SplitK0.of M.repr)
      = SplitK0.leftDimChar k (Center C) (SplitK0.of ((induction k C).obj S.repr)) := by
        conv_rhs => rw [SplitK0.of_eq_sum, Finsupp.sum_fintype _ _ (by simp)]
        simp only [map_sum, nsmul_eq_mul, map_mul, map_natCast,
          simpleMultiplicities_induction_obj_apply k, SimpleClasses.classOf_repr]
    _ = endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C)) *
          SplitK0.leftDimChar k C (SplitK0.of S.repr) := by
        refine (SplitK0.leftDimChar_of k ((induction k C).obj S.repr)).trans ?_
        refine (endAlgEquivOfSimple_unit_apply k (leftDim ((induction k C).obj S.repr))).trans ?_
        refine (congrArg (fun g ↦ endAlgEquivOfSimple k (𝟙_ C) (End.of g))
          (leftDim_induction_obj_f k S.repr)).trans ?_
        rw [End.of_comp, map_mul, SplitK0.leftDimChar_of]
        ring

variable (C)

/-- **Global dimension of the Drinfeld centre** (Müger, Etingof–Nikshych–Ostrik): for a pivotal
fusion category `C` over an algebraically closed field `k` whose centre `Center C` is finite
semisimple with finitely many simple classes, the global dimension of `Center C` in `k` is the
square of the global dimension of `C`. -/
theorem endAlgEquivOfSimple_globalDim [IsFiniteSemisimpleCategory (Center C)]
    [Fintype (SimpleClasses (Center C))] :
    endAlgEquivOfSimple k (𝟙_ (Center C)) (End.of (globalDim (Center C))) =
      endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C)) ^ 2 := by
  have : EssentiallySmall.{max u v} C := essentiallySmall_of_small_of_locallySmall C
  have : EssentiallySmall.{max u v} (Center C) :=
    essentiallySmall_of_small_of_locallySmall (Center C)
  let χC := SplitK0.leftDimChar k C
  let ψC := SplitK0.rightDimChar k C
  let χZ := SplitK0.leftDimChar k (Center C)
  let d := endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C))
  have hd : d = ∑ S : SimpleClasses C, χC (SplitK0.of S.repr) * ψC (SplitK0.of S.repr) := by
    simp only [d, globalDim_eq_sum_leftDimChar_smul k, End.of_smul, End.of_id, map_smul,
      map_one, smul_eq_mul, mul_one, ← SplitK0.dual_of, SplitK0.leftDimChar_dual, χC, ψC]
  have hM (M : SimpleClasses (Center C)) :
      ∑ S : SimpleClasses C, (simpleMultiplicities M.repr.1 S : k) * ψC (SplitK0.of S.repr) =
        χZ (SplitK0.of (M.repr)ᘁ) := by
    calc ∑ S : SimpleClasses C, (simpleMultiplicities M.repr.1 S : k) * ψC (SplitK0.of S.repr)
        = ψC (SplitK0.of M.repr.1) := by
          conv_rhs => rw [SplitK0.of_eq_sum, Finsupp.sum_fintype _ _ (by simp)]
          simp [map_sum]
      _ = χZ (SplitK0.of (M.repr)ᘁ) := by
          rw [← SplitK0.dual_of, SplitK0.leftDimChar_dual, SplitK0.rightDimChar_of,
            SplitK0.rightDimChar_of]
          exact (congrArg (fun g ↦ endAlgEquivOfSimple k (𝟙_ C) (End.of g))
            (rightDim_f M.repr)).symm.trans
            (endAlgEquivOfSimple_unit_apply k (rightDim M.repr)).symm
  calc endAlgEquivOfSimple k (𝟙_ (Center C)) (End.of (globalDim (Center C)))
      = ∑ M : SimpleClasses (Center C),
          χZ (SplitK0.of M.repr) *
            (∑ S : SimpleClasses C,
              (simpleMultiplicities M.repr.1 S : k) * ψC (SplitK0.of S.repr)) := by
        simp_rw [hM]
        simp [globalDim_eq_sum_leftDimChar_smul k, χZ]
    _ = ∑ S : SimpleClasses C,
          (∑ M : SimpleClasses (Center C),
            (simpleMultiplicities M.repr.1 S : k) * χZ (SplitK0.of M.repr)) *
          ψC (SplitK0.of S.repr) := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun S _ ↦ Finset.sum_congr rfl fun M _ ↦ by ring
    _ = d ^ 2 := by
        have hsum (S : SimpleClasses C) :
            (∑ M : SimpleClasses (Center C),
              (simpleMultiplicities M.repr.1 S : k) * χZ (SplitK0.of M.repr)) *
              ψC (SplitK0.of S.repr) =
            d * (χC (SplitK0.of S.repr) * ψC (SplitK0.of S.repr)) := by
          rw [sum_simpleMultiplicities_mul_leftDimChar_eq k S, mul_assoc]
        rw [Finset.sum_congr rfl fun S _ ↦ hsum S, ← Finset.mul_sum, ← hd, sq]

include k in
/-- For a pivotal fusion category `C` over an algebraically closed field `k` such that `Center C`
is finite semisimple with finitely many simple classes, on underlying endomorphisms of the unit
`globalDim (Center C)` is the composite `globalDim C ≫ globalDim C`. -/
theorem globalDim_f [IsFiniteSemisimpleCategory (Center C)]
    [Fintype (SimpleClasses (Center C))] :
    (globalDim (Center C)).f = globalDim C ≫ globalDim C := by
  let d := endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C))
  have hZ : globalDim (Center C) = d ^ 2 • 𝟙 (𝟙_ (Center C)) := by
    have h1 := (endAlgEquivOfSimple_smul_id (k := k) (End.of (globalDim (Center C)))).symm
    rw [endAlgEquivOfSimple_globalDim k C] at h1
    exact h1
  have hC : d ^ 2 • 𝟙 (𝟙_ C) = globalDim C ≫ globalDim C := by
    rw [sq, ← smul_smul, ← Category.id_comp (𝟙 (𝟙_ C)), ← Linear.smul_comp, ← Linear.comp_smul,
      endAlgEquivOfSimple_smul_id]
  have h1 := congrArg Hom.f hZ
  rw [smul_f, id_f] at h1
  exact h1.trans hC

end Pivotal

end Fusion

end CategoryTheory.Center

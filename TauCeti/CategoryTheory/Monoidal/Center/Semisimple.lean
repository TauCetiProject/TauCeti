/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Center.Abelian
public import TauCeti.CategoryTheory.Monoidal.Center.Induction.LeftAdjunction
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Character
public import TauCeti.CategoryTheory.Semisimple.Finite
public import TauCeti.CategoryTheory.Semisimple.Split

/-!
# Semisimplicity of the Drinfeld centre of a fusion category

Let `C` be a fusion category over an algebraically closed field `k`: a rigid `k`-linear finite
semisimple abelian monoidal category with simple unit, finitely many simple classes and
finite-dimensional morphism spaces. Its Drinfeld centre `Center C` is abelian, and the induction
functor `Center.induction k C : C ⥤ Center C` is adjoint to the forgetful functor on both sides.
By the averaging identity, the unit `Z ⟶ I (forget Z)` of the right adjunction followed by the
counit `I (forget Z) ⟶ Z` of the left adjunction is multiplication by the global dimension
`TauCeti.normGlobalDim C a`, an endomorphism of the simple unit, hence a scalar.

When the global dimension is nonzero, dividing the counit by it gives a retraction of the unit. So
every object of the centre is a retract of an induced object, and the Maschke-type criterion
`TauCeti.IsFiniteSemisimpleCategory.of_natTrans` shows that `Center C` is finite semisimple.
Since the forgetful functor is a faithful left adjoint, the centre then has finitely many simple
classes, by `CategoryTheory.Functor.finite_simpleClasses_of_faithful_leftAdjoint`.

No pivotal structure is assumed: the hypothesis is the nonvanishing of the pivot-free global
dimension. When `C` admits a pivotal structure and `k` has characteristic zero, this hypothesis
holds by the theorem of Etingof, Nikshych and Ostrik (`TauCeti.globalDim_ne_zero`, transported by
`TauCeti.normGlobalDim_eq_globalDim`). In characteristic `p` it can fail: for `C = Vec(C₂)` in
characteristic `2` the global dimension is `0` and the centre is not semisimple.

## Main declarations

* `CategoryTheory.Center.finite_simpleClasses_of_isFiniteSemisimpleCategory`: if `C` has finitely
  many simple classes and `Center C` is finite semisimple, then `Center C` has finitely many
  simple classes;
* `CategoryTheory.Center.isSplitMono_forgetInductionAdjunction_unit_app`: the unit of the right
  adjunction `Center.forget C ⊣ Center.induction k C` is a split monomorphism when the global
  dimension is nonzero;
* `CategoryTheory.Center.isFiniteSemisimpleCategory_of_normGlobalDim_ne_zero` and
  `CategoryTheory.Center.finite_simpleClasses_of_normGlobalDim_ne_zero`: the centre is finite
  semisimple with finitely many simple classes when the global dimension is nonzero;
* `CategoryTheory.Center.isFiniteSemisimpleCategory_of_charZero` and
  `CategoryTheory.Center.finite_simpleClasses_of_charZero`: the same conclusions for a pivotal
  fusion category over a field of characteristic zero.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005),
  Theorem 2.15
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§7.13, 9.3
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory TauCeti

universe w v u

namespace CategoryTheory.Center

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C] [IsFiniteSemisimpleCategory C]
  [Simple (𝟙_ C)] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

omit [Simple (𝟙_ C)] in
include k in
variable (C) in
/-- If `C` has finitely many isomorphism classes of simple objects and `Center C` is finite
semisimple, then `Center C` also has finitely many isomorphism classes of simple objects. -/
theorem finite_simpleClasses_of_isFiniteSemisimpleCategory [Finite (SimpleClasses C)]
    [IsFiniteSemisimpleCategory (Center C)] : Finite (SimpleClasses (Center C)) := by
  let := Fintype.ofFinite (SimpleClasses C)
  exact (forget C).finite_simpleClasses_of_faithful_leftAdjoint (forgetInductionAdjunction k C)

section GlobalDim

variable [Fintype (SimpleClasses C)]

/-- When the global dimension `TauCeti.normGlobalDim C a` of a fusion category is nonzero, the unit
`Z ⟶ I (forget Z)` of the right adjunction `Center.forget C ⊣ Center.induction k C` is a split
monomorphism: the counit of the left adjunction `Center.induction k C ⊣ Center.forget C`, divided
by the global dimension, is a retraction. -/
theorem isSplitMono_forgetInductionAdjunction_unit_app
    (a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) (ha : normGlobalDim C a ≠ 0)
    (Z : Center C) : IsSplitMono ((forgetInductionAdjunction k C).unit.app Z) := by
  obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id k (normGlobalDim C a)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact ha (by rw [← hc, zero_smul])
  refine IsSplitMono.mk' ⟨c⁻¹ • (inductionForgetAdjunction k C).counit.app Z, ?_⟩
  ext
  rw [Linear.comp_smul, smul_f,
    forgetInductionAdjunction_unit_app_comp_inductionForgetAdjunction_counit_app_f k Z a, ← hc]
  simp [smul_smul, inv_mul_cancel₀ hc0]

include k in
/-- **The centre of a fusion category of nonzero global dimension is finite semisimple**
(Etingof–Nikshych–Ostrik). Here `C` is a fusion category over an algebraically closed field `k`,
with no pivotal structure assumed, and `TauCeti.normGlobalDim C a` is its global dimension for any
family of isomorphisms `a S : S ≅ Sᘁᘁ`. -/
theorem isFiniteSemisimpleCategory_of_normGlobalDim_ne_zero
    (a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) (ha : normGlobalDim C a ≠ 0) :
    IsFiniteSemisimpleCategory (Center C) :=
  have := isSplitMono_forgetInductionAdjunction_unit_app k a ha
  IsFiniteSemisimpleCategory.of_natTrans (forget C) (induction k C)
    (forgetInductionAdjunction k C).unit

include k in
/-- **The centre of a fusion category of nonzero global dimension has finitely many simple
classes**, with no pivotal structure assumed. -/
theorem finite_simpleClasses_of_normGlobalDim_ne_zero
    (a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) (ha : normGlobalDim C a ≠ 0) :
    Finite (SimpleClasses (Center C)) :=
  have := isFiniteSemisimpleCategory_of_normGlobalDim_ne_zero k a ha
  finite_simpleClasses_of_isFiniteSemisimpleCategory k C

end GlobalDim

section CharZero

variable [CharZero k] [PivotalCategory C] [Finite (SimpleClasses C)]

include k

/-- **The centre of a pivotal fusion category over a field of characteristic zero is finite
semisimple**, since its global dimension is nonzero (`TauCeti.globalDim_ne_zero`). -/
theorem isFiniteSemisimpleCategory_of_charZero : IsFiniteSemisimpleCategory (Center C) :=
  let := Fintype.ofFinite (SimpleClasses C)
  isFiniteSemisimpleCategory_of_normGlobalDim_ne_zero k (fun S ↦ pivotalIsoApp S.repr)
    (by rw [normGlobalDim_eq_globalDim C k]; exact globalDim_ne_zero k C)

/-- **The centre of a pivotal fusion category over a field of characteristic zero has finitely many
simple classes**, since its global dimension is nonzero (`TauCeti.globalDim_ne_zero`). -/
theorem finite_simpleClasses_of_charZero : Finite (SimpleClasses (Center C)) :=
  let := Fintype.ofFinite (SimpleClasses C)
  finite_simpleClasses_of_normGlobalDim_ne_zero k (fun S ↦ pivotalIsoApp S.repr)
    (by rw [normGlobalDim_eq_globalDim C k]; exact globalDim_ne_zero k C)

end CharZero

end CategoryTheory.Center

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Center
public import TauCeti.RepresentationTheory.CharacterTable.ClassFunction
public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# The class-sum basis of the center

For a finite group `G` and a commutative semiring `k`, the coefficients of a central element of
the group algebra `k[G]` are constant on conjugacy classes. This identifies the center linearly
with the space of `k`-valued functions on `ConjClasses G`.

The corresponding family is a basis already over a commutative semiring. Over a ring satisfying
the strong rank condition, this implies that the dimension of the center is the number of
conjugacy classes.

The identification is built by sending a central element to its coefficient function as a
`TauCeti.ClassFunction`, and composing with the equivalence
`TauCeti.ClassFunction.equivConjClasses`, so the descent to the quotient and its linearity are
reused rather than repeated here.
-/

public section

namespace TauCeti

open scoped BigOperators

variable {G k : Type*} [Group G] [Fintype G] [DecidableEq G] [CommSemiring k]

omit [Fintype G] [DecidableEq G] in
/-- The coefficient function of a central group-algebra element, as a class function on `G`. -/
def centerToClassFunction :
    Subalgebra.center k (MonoidAlgebra k G) →ₗ[k] ClassFunction k G where
  toFun z := ⟨fun g => z.val.coeff g, ClassFunction.mem_iff.mpr fun g x => by
    have hz := congrArg (fun a : MonoidAlgebra k G => a.coeff (x * g))
      (Subalgebra.mem_center_iff.mp z.property (MonoidAlgebra.of k G x))
    simpa [mul_assoc] using hz.symm⟩
  map_add' z w := rfl
  map_smul' c z := rfl

omit [Fintype G] [DecidableEq G] in
/-- The class function of a central element is its coefficient function. -/
@[simp]
theorem centerToClassFunction_apply (z : Subalgebra.center k (MonoidAlgebra k G)) (g : G) :
    (centerToClassFunction z).val g = z.val.coeff g :=
  (rfl)

omit [Fintype G] [DecidableEq G] in
/-- The coefficients of a central group-algebra element agree on conjugate group elements. -/
theorem center_coeff_eq_of_isConj (z : Subalgebra.center k (MonoidAlgebra k G))
    {g h : G} (hgh : IsConj g h) :
    z.val.coeff g = z.val.coeff h :=
  ClassFunction.eq_of_isConj (centerToClassFunction z) hgh

omit [Fintype G] [DecidableEq G] in
/-- If `cls : G → ι` only identifies conjugate elements, the coefficients of a central element of
`k[G]` factor through `cls`. -/
theorem exists_center_coeff_eq_comp {ι : Type*} (cls : G → ι)
    (hcls : ∀ g h, cls g = cls h → IsConj g h) (z : Subalgebra.center k (MonoidAlgebra k G)) :
    ∃ ψ : ι → k, ⇑(z : MonoidAlgebra k G).coeff = ψ ∘ cls := by
  classical
  refine ⟨fun i ↦ (z : MonoidAlgebra k G).coeff (Function.invFun cls i), funext fun g ↦ ?_⟩
  exact center_coeff_eq_of_isConj z (hcls _ _ (Function.invFun_eq ⟨g, rfl⟩)).symm

omit [Fintype G] [DecidableEq G] in
/-- Read the coefficients of a central group-algebra element as a function on conjugacy classes. -/
noncomputable def centerToConjClasses
    (z : Subalgebra.center k (MonoidAlgebra k G)) : ConjClasses G → k :=
  ClassFunction.equivConjClasses (centerToClassFunction z)

omit [Fintype G] [DecidableEq G] in
/-- Reading the coefficient on the conjugacy class of `g` recovers the coefficient at `g`. -/
@[simp]
theorem centerToConjClasses_mk (z : Subalgebra.center k (MonoidAlgebra k G)) (g : G) :
    centerToConjClasses z (ConjClasses.mk g) = z.val.coeff g := by
  simp [centerToConjClasses]

/-- Regard a class sum as an element of the center of the group algebra. -/
noncomputable def classSumCenter (C : ConjClasses G) :
    Subalgebra.center k (MonoidAlgebra k G) :=
  ⟨classSum k C, classSum_mem_center k C⟩

/-- The underlying group-algebra element of a central class sum is the class sum. -/
@[simp]
theorem classSumCenter_coe (C : ConjClasses G) :
    (classSumCenter (k := k) C : MonoidAlgebra k G) = classSum k C :=
  (rfl)

/-- The conjugacy class of a central element `g` is `{g}`, so its class sum is `g`. -/
theorem classSumCenter_mk_of_mem_center {g : G} (hg : g ∈ Subgroup.center G) :
    (classSumCenter (k := k) (ConjClasses.mk g) : MonoidAlgebra k G) = MonoidAlgebra.of k G g := by
  ext x
  simp only [classSumCenter_coe, classSum_coeff, ConjClasses.mk_eq_mk_iff_isConj,
    MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  exact if_congr ⟨fun h => (h.eq_of_right_mem_center hg).symm, fun h => h ▸ IsConj.refl x⟩
    rfl rfl

/-- The class sum of the conjugacy class of `1`, as an element of the center, is `1`. -/
@[simp]
theorem classSumCenter_mk_one : classSumCenter (k := k) (ConjClasses.mk (1 : G)) = 1 :=
  Subtype.ext <| (classSumCenter_mk_of_mem_center (one_mem _)).trans (map_one _)

/-- Convert a function on conjugacy classes to the corresponding linear combination of class
sums. -/
noncomputable def ofConjClassesCenter (f : ConjClasses G → k) :
    Subalgebra.center k (MonoidAlgebra k G) :=
  ∑ C, f C • classSumCenter (k := k) C

/-- The coefficient at `g` of the class-sum expansion is the value on the class of `g`. -/
@[simp]
theorem ofConjClassesCenter_coeff (f : ConjClasses G → k) (g : G) :
    (ofConjClassesCenter f : MonoidAlgebra k G).coeff g = f (ConjClasses.mk g) := by
  simp [ofConjClassesCenter, eq_comm]

/-- The center of a finite group algebra is linearly equivalent to the functions on conjugacy
classes, by taking coefficients. -/
noncomputable def centerEquivConjClasses :
    Subalgebra.center k (MonoidAlgebra k G) ≃ₗ[k] (ConjClasses G → k) where
  toFun := centerToConjClasses
  invFun := ofConjClassesCenter
  map_add' z w := by
    simp only [centerToConjClasses, map_add]
  map_smul' c z := by
    simp only [centerToConjClasses, map_smul, RingHom.id_apply]
  left_inv z := by
    ext g
    simp
  right_inv f := by
    ext C
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
    simp

/-- The forward map of `centerEquivConjClasses` reads the coefficients of a central element. -/
@[simp]
theorem centerEquivConjClasses_apply (z : Subalgebra.center k (MonoidAlgebra k G)) :
    centerEquivConjClasses z = centerToConjClasses z :=
  (rfl)

/-- The inverse of `centerEquivConjClasses` forms the corresponding linear combination of class
sums. -/
@[simp]
theorem centerEquivConjClasses_symm_apply (f : ConjClasses G → k) :
    centerEquivConjClasses.symm f = ofConjClassesCenter f :=
  (rfl)

/-- The class sums, regarded as central group-algebra elements, form a basis of the center. -/
noncomputable def classSumBasis :
    Module.Basis (ConjClasses G) k (Subalgebra.center k (MonoidAlgebra k G)) :=
  Module.Basis.ofEquivFun centerEquivConjClasses

/-- A vector in the class-sum basis is the corresponding central class sum. -/
@[simp]
theorem classSumBasis_apply (C : ConjClasses G) :
    classSumBasis (k := k) C = classSumCenter (k := k) C := by
  apply centerEquivConjClasses.injective
  ext D
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep D
  simp [classSumBasis, Pi.single_apply, eq_comm]

/-- The coordinate of a central element in the class-sum basis is its coefficient on that
conjugacy class. -/
@[simp]
theorem classSumBasis_repr_apply (z : Subalgebra.center k (MonoidAlgebra k G)) (C : ConjClasses G) :
    (classSumBasis (k := k)).repr z C = centerToConjClasses z C :=
  Module.Basis.ofEquivFun_repr_apply centerEquivConjClasses z C

end TauCeti

namespace TauCeti

variable (k G : Type*) [CommSemiring k] [Group G] [Finite G]

/-- The center of a finite group algebra is finite as a module, with its class-sum basis. -/
noncomputable instance instModuleFiniteCenterMonoidAlgebra :
    Module.Finite k (Subalgebra.center k (MonoidAlgebra k G)) := by
  let := Fintype.ofFinite G
  let := Classical.decEq G
  exact Module.Finite.of_basis classSumBasis

variable [StrongRankCondition k]

/-- The dimension of the center of a finite group algebra is the number of conjugacy classes. -/
theorem finrank_center_monoidAlgebra :
    Module.finrank k (Subalgebra.center k (MonoidAlgebra k G)) =
      Nat.card (ConjClasses G) := by
  let := Fintype.ofFinite G
  let := Classical.decEq G
  rw [Module.finrank_eq_card_basis (classSumBasis (G := G) (k := k))]
  exact Fintype.card_eq_nat_card

end TauCeti

namespace TauCeti

variable {k G : Type*} [CommSemiring k] [CommGroup G] [Fintype G] [DecidableEq G]

/-- In a commutative group every element is central (`classSumCenter_mk_of_mem_center`), so the
class sum of `g`, as an element of the center, is `g`.

Its simp priority is low so that `classSumCenter_mk_one` still rewrites the class of `1`
to `1`, rather than to `toCenter (of k G 1)`, which simp leaves as `single 1 1`. -/
@[simp low]
theorem classSumCenter_mk_of_commGroup (g : G) :
    classSumCenter (k := k) (ConjClasses.mk g) =
      MonoidAlgebra.toCenter (MonoidAlgebra.of k G g) :=
  Subtype.ext <| (classSumCenter_mk_of_mem_center
    (Subgroup.mem_center_iff.mpr fun h => mul_comm h g)).trans (MonoidAlgebra.coe_toCenter _).symm

end TauCeti

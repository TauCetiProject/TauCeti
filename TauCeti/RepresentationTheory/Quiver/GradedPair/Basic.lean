/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Graded.LinearMap
public import TauCeti.RepresentationTheory.Quiver.GradedPair.Space
import TauCeti.LinearAlgebra.Graded.Nilpotent

/-!
# Raising and lowering operators on finite graded complex spaces

A `TauCeti.GradedPair S d` is an endomorphism of the coordinate graded space `S` which moves every
grade by one step in the direction `d`: it maps `S.grade a` into `S.grade (a + 1)` when `d = up`
and into `S.grade (a - 1)` when `d = down`. Such a pair is a representation of the infinite
linearly oriented type-`A` quiver supported on finitely many vertices, the raising operators being
the `VN` pairs and the lowering operators the `WL` pairs of Zelevinsky's multisegment duality.

A `TauCeti.GradedPairEquiv P Q` is a complex linear equivalence of the underlying spaces which
preserves every grade in both directions and intertwines the two operators, and
`TauCeti.GradedPair.Isomorphic` is the resulting isomorphism relation, an equivalence relation
between pairs on possibly different presentations.

## Main definitions

* `TauCeti.StepDirection`: the two directions `up` and `down`, with degree steps `1` and `-1`.
* `TauCeti.GradedPair`: an endomorphism of a coordinate graded space of degree `d.step`.
* `TauCeti.GradedPairEquiv`: a grade-preserving linear equivalence intertwining two pairs.
* `TauCeti.GradedPair.Isomorphic`: existence of a `GradedPairEquiv`.

## Main results

* `TauCeti.GradedPair.isNilpotent`: the operator of a pair is nilpotent, since its grading has
  finite support.
* `TauCeti.GradedPair.Isomorphic.finrank_grade_eq`: isomorphic pairs have grades of equal
  dimensions.
* `TauCeti.GradedPair.isomorphic_zero_iff`: two zero pairs are isomorphic exactly when their
  grades have equal dimensions.

## References

* H. Atobe, S. Kondo, S. Yasuda, *Local newforms for the general linear groups over a
  non-archimedean local field*, Forum of Mathematics, Pi 10 (2022), e24, §3.1.
* A. V. Zelevinskii, *p-adic analog of the Kazhdan–Lusztig hypothesis*, Funktsional. Anal. i
  Prilozhen. 15:2 (1981), 9–21, §4.
-/

public section

open Module

namespace TauCeti

/-! ### Directions -/

/-- The direction of a degree-one graded operator: `up` raises degree by one, `down` lowers it
by one. -/
inductive StepDirection
  /-- Raise degree by one. -/
  | up
  /-- Lower degree by one. -/
  | down
  deriving DecidableEq

namespace StepDirection

/-- The degree change of an operator in direction `d`: `1` for `up` and `-1` for `down`. -/
def step : StepDirection → ℤ
  | up => 1
  | down => -1

/-- The opposite direction. -/
def reverse : StepDirection → StepDirection
  | up => down
  | down => up

@[simp]
theorem step_up : up.step = 1 :=
  (rfl)

@[simp]
theorem step_down : down.step = -1 :=
  (rfl)

@[simp]
theorem reverse_up : up.reverse = down :=
  (rfl)

@[simp]
theorem reverse_down : down.reverse = up :=
  (rfl)

@[simp]
theorem reverse_reverse (d : StepDirection) : d.reverse.reverse = d := by
  cases d <;> rfl

@[simp]
theorem step_reverse (d : StepDirection) : d.reverse.step = -d.step := by
  cases d <;> rfl

theorem step_ne_zero (d : StepDirection) : d.step ≠ 0 := by
  cases d <;> decide

end StepDirection

/-! ### Graded pairs -/

/-- A degree-one operator on a coordinate graded space in direction `d`: an endomorphism of
`S.Carrier` mapping each grade `S.grade a` into `S.grade (a + d.step)`. -/
@[ext]
structure GradedPair (S : GradedCoordSpace) (d : StepDirection) where
  /-- The underlying endomorphism. -/
  operator : Module.End ℂ S.Carrier
  /-- The operator moves every grade by `d.step`. -/
  isHomogeneous : LinearMap.IsHomogeneous operator S.grade S.grade d.step

namespace GradedPair

variable {S T U : GradedCoordSpace} {d : StepDirection}

/-- The operator of a graded pair is nilpotent: its powers move every grade outside the finite
support of the grading. -/
theorem isNilpotent (P : GradedPair S d) : IsNilpotent P.operator :=
  P.isHomogeneous.isNilpotent S.isInternal_grade.submodule_iSup_eq_top
    S.finite_setOf_grade_ne_bot d.step_ne_zero

/-- The zero operator, which is homogeneous of every degree. -/
instance : Zero (GradedPair S d) :=
  ⟨⟨0, LinearMap.isHomogeneous_zero _ _ _⟩⟩

@[simp]
theorem operator_zero : (0 : GradedPair S d).operator = 0 :=
  (rfl)

end GradedPair

/-! ### Graded equivalences of pairs -/

/-- A graded equivalence of pairs: a complex linear equivalence of the underlying spaces that
preserves each grade in both directions and intertwines the operators. -/
structure GradedPairEquiv {S T : GradedCoordSpace} {d : StepDirection} (P : GradedPair S d)
    (Q : GradedPair T d) extends S.Carrier ≃ₗ[ℂ] T.Carrier where
  /-- A vector lies in a grade exactly when its image lies in the same grade. -/
  mem_grade_iff' : ∀ (a : ℤ) (v : S.Carrier), v ∈ S.grade a ↔ toLinearEquiv v ∈ T.grade a
  /-- The equivalence intertwines the operators. -/
  map_operator' : ∀ v, toLinearEquiv (P.operator v) = Q.operator (toLinearEquiv v)

namespace GradedPairEquiv

variable {S T U : GradedCoordSpace} {d : StepDirection} {P : GradedPair S d}
  {Q : GradedPair T d} {R : GradedPair U d}

instance : EquivLike (GradedPairEquiv P Q) S.Carrier T.Carrier where
  coe e := e.toLinearEquiv
  inv e := e.toLinearEquiv.symm
  left_inv e := e.toLinearEquiv.left_inv
  right_inv e := e.toLinearEquiv.right_inv
  coe_injective' e f h _ := by
    cases e
    cases f
    congr
    exact DFunLike.coe_injective h

instance : LinearEquivClass (GradedPairEquiv P Q) ℂ S.Carrier T.Carrier where
  map_add e := e.toLinearEquiv.map_add
  map_smulₛₗ e := e.toLinearEquiv.map_smul

@[ext]
theorem ext {e f : GradedPairEquiv P Q} (h : ∀ v, e v = f v) : e = f :=
  DFunLike.ext _ _ h

@[simp]
theorem coe_toLinearEquiv (e : GradedPairEquiv P Q) : ⇑e.toLinearEquiv = e :=
  (rfl)

@[simp]
theorem coe_mk (e : S.Carrier ≃ₗ[ℂ] T.Carrier) (h₁ h₂) :
    ⇑(⟨e, h₁, h₂⟩ : GradedPairEquiv P Q) = e :=
  (rfl)

/-- A graded equivalence of pairs preserves grade membership in both directions. -/
@[simp]
theorem mem_grade_iff (e : GradedPairEquiv P Q) {a : ℤ} {v : S.Carrier} :
    e v ∈ T.grade a ↔ v ∈ S.grade a :=
  (e.mem_grade_iff' a v).symm

/-- A graded equivalence of pairs intertwines the operators. -/
@[simp]
theorem map_operator (e : GradedPairEquiv P Q) (v : S.Carrier) :
    e (P.operator v) = Q.operator (e v) :=
  e.map_operator' v

/-- A graded equivalence of pairs preserves the dimension of every grade. -/
theorem finrank_grade_eq (e : GradedPairEquiv P Q) (a : ℤ) :
    finrank ℂ (S.grade a) = finrank ℂ (T.grade a) :=
  (S.exists_linearEquiv_iff_finrank_grade_eq T).1 ⟨e.toLinearEquiv, e.mem_grade_iff'⟩ a

/-- The identity graded equivalence of a pair. -/
def refl (P : GradedPair S d) : GradedPairEquiv P P where
  toLinearEquiv := LinearEquiv.refl ℂ S.Carrier
  mem_grade_iff' _ _ := Iff.rfl
  map_operator' _ := rfl

/-- The inverse of a graded equivalence of pairs. -/
def symm (e : GradedPairEquiv P Q) : GradedPairEquiv Q P where
  toLinearEquiv := e.toLinearEquiv.symm
  mem_grade_iff' a w := by
    rw [e.mem_grade_iff' a (e.toLinearEquiv.symm w), LinearEquiv.apply_symm_apply]
  map_operator' w := e.toLinearEquiv.injective (by
    simp only [e.map_operator', LinearEquiv.apply_symm_apply])

/-- The composite of two graded equivalences of pairs. -/
def trans (e : GradedPairEquiv P Q) (f : GradedPairEquiv Q R) : GradedPairEquiv P R where
  toLinearEquiv := e.toLinearEquiv.trans f.toLinearEquiv
  mem_grade_iff' a v := (e.mem_grade_iff' a v).trans (f.mem_grade_iff' a _)
  map_operator' v := by simp only [LinearEquiv.trans_apply, e.map_operator', f.map_operator']

@[simp]
theorem toLinearEquiv_symm (e : GradedPairEquiv P Q) :
    e.symm.toLinearEquiv = e.toLinearEquiv.symm :=
  (rfl)

@[simp]
theorem symm_symm (e : GradedPairEquiv P Q) : e.symm.symm = e :=
  (rfl)

@[simp]
theorem refl_apply (v : S.Carrier) : refl P v = v :=
  (rfl)

@[simp]
theorem trans_apply (e : GradedPairEquiv P Q) (f : GradedPairEquiv Q R) (v : S.Carrier) :
    e.trans f v = f (e v) :=
  (rfl)

@[simp]
theorem symm_apply_apply (e : GradedPairEquiv P Q) (v : S.Carrier) : e.symm (e v) = v :=
  e.toLinearEquiv.symm_apply_apply v

@[simp]
theorem apply_symm_apply (e : GradedPairEquiv P Q) (w : T.Carrier) : e (e.symm w) = w :=
  e.toLinearEquiv.apply_symm_apply w

/-- A graded equivalence of pairs maps each grade onto the corresponding grade. -/
theorem map_grade (e : GradedPairEquiv P Q) (a : ℤ) :
    (S.grade a).map (e.toLinearEquiv : S.Carrier →ₗ[ℂ] T.Carrier) = T.grade a :=
  GradedCoordSpace.map_grade_of_mem_grade_iff e.toLinearEquiv e.mem_grade_iff' a

end GradedPairEquiv

namespace GradedPair

variable {S T U : GradedCoordSpace} {d : StepDirection}

/-- Two pairs in the same direction are isomorphic when some graded equivalence intertwines
them. -/
def Isomorphic (P : GradedPair S d) (Q : GradedPair T d) : Prop :=
  Nonempty (GradedPairEquiv P Q)

theorem isomorphic_iff {P : GradedPair S d} {Q : GradedPair T d} :
    P.Isomorphic Q ↔ Nonempty (GradedPairEquiv P Q) :=
  Iff.rfl

/-- A graded equivalence witnesses that two pairs are isomorphic. -/
theorem _root_.TauCeti.GradedPairEquiv.isomorphic {P : GradedPair S d} {Q : GradedPair T d}
    (e : GradedPairEquiv P Q) : P.Isomorphic Q :=
  ⟨e⟩

/-- Isomorphic pairs admit a graded equivalence. -/
theorem Isomorphic.nonempty {P : GradedPair S d} {Q : GradedPair T d} (h : P.Isomorphic Q) :
    Nonempty (GradedPairEquiv P Q) :=
  h

theorem Isomorphic.refl (P : GradedPair S d) : P.Isomorphic P :=
  ⟨GradedPairEquiv.refl P⟩

theorem Isomorphic.symm {P : GradedPair S d} {Q : GradedPair T d} (h : P.Isomorphic Q) :
    Q.Isomorphic P :=
  h.map GradedPairEquiv.symm

theorem Isomorphic.trans {P : GradedPair S d} {Q : GradedPair T d} {R : GradedPair U d}
    (h : P.Isomorphic Q) (h' : Q.Isomorphic R) : P.Isomorphic R :=
  h.elim fun e ↦ h'.map e.trans

/-- Isomorphic pairs have grades of equal dimensions. -/
theorem Isomorphic.finrank_grade_eq {P : GradedPair S d} {Q : GradedPair T d}
    (h : P.Isomorphic Q) (a : ℤ) : finrank ℂ (S.grade a) = finrank ℂ (T.grade a) :=
  h.elim fun e ↦ e.finrank_grade_eq a

/-- Two zero pairs are isomorphic exactly when their grades have equal dimensions. -/
theorem isomorphic_zero_iff :
    (0 : GradedPair S d).Isomorphic (0 : GradedPair T d) ↔
      ∀ a, finrank ℂ (S.grade a) = finrank ℂ (T.grade a) := by
  refine ⟨Isomorphic.finrank_grade_eq, fun h ↦ ?_⟩
  obtain ⟨e, he⟩ := (S.exists_linearEquiv_iff_finrank_grade_eq T).2 h
  exact ⟨{ toLinearEquiv := e, mem_grade_iff' := he, map_operator' := by simp }⟩

end GradedPair

end TauCeti

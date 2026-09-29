/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedVectorSpace.Basic
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.ForgetGrading

/-!
# The q-Euler form of graded vector spaces

Let `k` be a field, and let `TauCeti.GradedVectorSpace k` be the category of `ℤ`-graded
vector spaces with its grading shift `(V{1})ᵢ = V_{i-1}`, from
`TauCeti.Algebra.Category.GradedVectorSpace.Basic`.

The one-dimensional space `M = k` placed in degree `0` is the smallest nontrivial test of the
q-Euler formalism: it is projective, it is not isomorphic to any of its shifts `M{j}` with
`j ≠ 0`, its degree-zero endomorphisms are one-dimensional, and it has no higher `Ext`. Hence

```text
χ_q(M, M) = 1,    χ_q(M, M{1}) = q = q χ_q(M, M),    χ_q(M{1}, M) = q⁻¹ = q⁻¹ χ_q(M, M).
```

At `q = 1` the three values agree, while at `q = -1` a single shift changes the sign.

Forgetting the grading is the functor `U` taking the direct sum `⨁ᵢ Vᵢ` of the pieces; it is
invariant under the shift, `{1} ⋙ U ≅ U`, and `U M ≅ k`. In every cohomological degree the
bigraded `Ext` groups of `(M, M)` assemble into the ungraded `Ext` groups of `(U M, U M)` in
`ModuleCat k`; this is checked directly, by computing both sides, and it identifies the value of
`χ_q(M, M)` at `q = 1` with the ordinary Ext-Euler characteristic `χ(U M, U M) = 1`.

## Main results

* `TauCeti.GradedVectorSpace.gradedExtEuler_unit`: `χ_q(M, M) = 1`.
* `TauCeti.GradedVectorSpace.gradedExtEuler_unit_shiftTarget` and
  `TauCeti.GradedVectorSpace.gradedExtEuler_unit_shiftSource`: `χ_q(M, M{1}) = q` and
  `χ_q(M{1}, M) = q⁻¹`.
* `TauCeti.GradedVectorSpace.laurentEval_gradedExtEuler_unit_shiftTarget` and
  `TauCeti.GradedVectorSpace.laurentEval_gradedExtEuler_unit_shiftSource`: their values at
  `q = ε` for `ε = ±1`; in particular
  `TauCeti.GradedVectorSpace.laurentEval_neg_one_gradedExtEuler_unit_shiftTarget`: at `q = -1`,
  `χ_q(M, M{1})` is the negative of `χ_q(M, M)`.
* `TauCeti.GradedVectorSpace.isGradedExtComparison_unit`: the bigraded `Ext` groups of `(M, M)`
  assemble into the `Ext` groups of the underlying ungraded pair `(U M, U M)` in `ModuleCat k`.
* `TauCeti.GradedVectorSpace.laurentEval_one_gradedExtEuler_unit`: `χ_q(M, M)` at `q = 1` is the
  ordinary Ext-Euler characteristic of `(U M, U M)`.
* `TauCeti.GradedVectorSpace.extEuler_moduleCat_field_self`: the ordinary Ext-Euler characteristic
  `χ(k, k)` in `ModuleCat k` is `1`.

## Implementation notes

The results hold for every choice of `HasExt` instances on the two categories: `Ext` groups are
only used through their dimensions.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* **185** (2022), Section 2.2, for graded Grothendieck groups, the
  q-Euler form and its shift conventions.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian LaurentPolynomial

universe w w' u

variable (k : Type u) [Field k]

namespace GradedVectorSpace

/-- The graded morphism spaces `Hom(M, M{j})` have finite Laurent support. -/
theorem hasFiniteLaurentSupport_hom_unit :
    HasFiniteLaurentSupport k fun j ↦ unit k ⟶ ((shift k) ^ j).functor.obj (unit k) := by
  refine HasFiniteLaurentSupport.of_finset (fun j ↦ ?_) {0} fun j hj ↦ ?_
  · obtain ⟨φ⟩ := nonempty_linearEquiv_hom_unit_shift_pow k j
    have := finiteDimensional_unit_obj k (-j)
    exact Module.Finite.equiv φ.symm
  · obtain ⟨φ⟩ := nonempty_linearEquiv_hom_unit_shift_pow k j
    have := ModuleCat.subsingleton_of_isZero (isZero_unit_obj k (neg_ne_zero.2
      (Finset.notMem_singleton.1 hj)))
    exact φ.toEquiv.subsingleton

/-! ### The q-Euler characteristic of `M = unit k` -/

section GradedExtEuler

variable [HasExt.{w} (GradedVectorSpace k)]

/-- The pair `(M, M)` is graded Euler-admissible: `M` is projective and its graded morphism spaces
have finite Laurent support. -/
theorem isGradedEulerAdmissible_unit :
    IsGradedEulerAdmissible.{w} k (shift k) (unit k) (unit k) :=
  isGradedEulerAdmissible_of_projective k (shift k) _ _ (hasFiniteLaurentSupport_hom_unit k)

/-- **`χ_q(M, M) = 1`**: the only surviving bigraded `Ext` group of `(M, M)` is the
one-dimensional space of degree-zero endomorphisms. -/
@[simp]
theorem gradedExtEuler_unit :
    gradedExtEuler k (shift k) (isGradedEulerAdmissible_unit.{w} k) = 1 := by
  rw [gradedExtEuler_projective k (shift k) (isGradedEulerAdmissible_unit.{w} k), ← T_zero]
  ext j
  rw [coeff_targetShiftGradedDimension, finrank_hom_unit_shift_pow, T_apply]
  simp [eq_comm (a := (0 : ℤ))]

/-- **`χ_q(M, M{1}) = q`**, that is, `q · χ_q(M, M)`: the q-Euler form is q-linear in its second
argument. This holds for any admissibility witness, e.g.
`(isGradedEulerAdmissible_unit k).shiftTarget`; the shifted target is written as
`shiftFunctor _ 1`, the `simp`-normal form of `(shift k).functor`. -/
@[simp]
theorem gradedExtEuler_unit_shiftTarget (h : IsGradedEulerAdmissible.{w} k (shift k) (unit k)
    ((shiftFunctor (GradedVectorSpace k) (1 : ℤ)).obj (unit k))) :
    gradedExtEuler k (shift k) h = T 1 := by
  -- `h` and `(isGradedEulerAdmissible_unit k).shiftTarget` differ only in how the shift is spelled.
  exact (gradedExtEuler_shiftTarget (isGradedEulerAdmissible_unit.{w} k)).trans <| by
    rw [gradedExtEuler_unit, mul_one]

/-- **`χ_q(M{1}, M) = q⁻¹`**, that is, `q⁻¹ · χ_q(M, M)`: the q-Euler form is q-antilinear in its
first argument. This holds for any admissibility witness, e.g.
`(isGradedEulerAdmissible_unit k).shiftSource`; the shifted source is written as
`shiftFunctor _ 1`, the `simp`-normal form of `(shift k).functor`. -/
@[simp]
theorem gradedExtEuler_unit_shiftSource (h : IsGradedEulerAdmissible.{w} k (shift k)
    ((shiftFunctor (GradedVectorSpace k) (1 : ℤ)).obj (unit k)) (unit k)) :
    gradedExtEuler k (shift k) h = T (-1) := by
  -- `h` and `(isGradedEulerAdmissible_unit k).shiftSource` differ only in how the shift is spelled.
  exact (gradedExtEuler_shiftSource (isGradedEulerAdmissible_unit.{w} k)).trans <| by
    rw [gradedExtEuler_unit, mul_one]

/-- At `q = ε` for a unit `ε : ℤˣ`, the value `χ_q(M, M{1})` becomes `ε`. -/
theorem laurentEval_gradedExtEuler_unit_shiftTarget (ε : ℤˣ) :
    laurentEval ε (gradedExtEuler k (shift k) (isGradedEulerAdmissible_unit.{w} k).shiftTarget) =
      ε := by
  simp

/-- At `q = ε` for a unit `ε : ℤˣ`, the value `χ_q(M{1}, M)` becomes `ε⁻¹`. -/
theorem laurentEval_gradedExtEuler_unit_shiftSource (ε : ℤˣ) :
    laurentEval ε (gradedExtEuler k (shift k) (isGradedEulerAdmissible_unit.{w} k).shiftSource) =
      ((ε⁻¹ : ℤˣ) : ℤ) := by
  simp

/-- **At `q = -1` a single shift changes the sign**: `χ_q(M, M{1})` specializes to the negative of
the specialization of `χ_q(M, M)`. -/
theorem laurentEval_neg_one_gradedExtEuler_unit_shiftTarget :
    laurentEval (-1 : ℤˣ)
        (gradedExtEuler k (shift k) (isGradedEulerAdmissible_unit.{w} k).shiftTarget) =
      -laurentEval (-1 : ℤˣ) (gradedExtEuler k (shift k) (isGradedEulerAdmissible_unit.{w} k)) := by
  rw [laurentEval_gradedExtEuler_unit_shiftTarget, gradedExtEuler_unit, map_one, Units.val_neg,
    Units.val_one]

end GradedExtEuler

/-! ### Comparison with the underlying ungraded pair `(U M, U M)` -/

section Comparison

variable [HasExt.{w'} (ModuleCat.{u} k)]

/-- **The ungraded Ext-Euler characteristic `χ(k, k) = 1`** in `ModuleCat k`, for any
admissibility witness: `k` is projective with one-dimensional endomorphisms. -/
@[simp]
theorem extEuler_moduleCat_field_self
    (h : IsEulerAdmissible.{w'} k (ModuleCat.of k k) (ModuleCat.of k k)) :
    extEuler.{w'} k h = 1 := by
  have : Projective (ModuleCat.of k k) :=
    ModuleCat.projective_of_free (Module.Basis.singleton Unit k)
  rw [extEuler_projective, ModuleCat.homLinearEquiv.finrank_eq,
    (LinearMap.ringLmapEquivSelf k k k).finrank_eq, Module.finrank_self, Nat.cast_one]

variable [HasExt.{w} (GradedVectorSpace k)]

/-- **The graded `Ext` groups of `(M, M)` assemble into the ungraded ones of `(U M, U M)`**: in
each cohomological degree `n`, `⨁ j, Extⁿ(M, M{j}) ≅ Extⁿ_k(U M, U M)`. Both sides are computed:
they are one-dimensional for `n = 0` and zero otherwise. -/
theorem isGradedExtComparison_unit :
    IsGradedExtComparison.{w, w'} k (shift k) (unit k) (unit k)
      ((GradedObject.total ℤ (ModuleCat.{u} k)).obj (unit k))
      ((GradedObject.total ℤ (ModuleCat.{u} k)).obj (unit k)) := by
  have : Projective ((GradedObject.total ℤ (ModuleCat.{u} k)).obj (unit k)) :=
    have := ModuleCat.projective_of_free (Module.Basis.singleton Unit k)
    Projective.of_iso (totalObjUnitIso k).symm this
  have hhom := Linear.homCongr k (totalObjUnitIso k) (totalObjUnitIso k)
  have : FiniteDimensional k
      ((GradedObject.total ℤ (ModuleCat.{u} k)).obj (unit k) ⟶
        (GradedObject.total ℤ (ModuleCat.{u} k)).obj (unit k)) :=
    Module.Finite.equiv (hhom.trans (ModuleCat.homLinearEquiv (S := k))).symm
  have hadm := isEulerAdmissible_of_projective.{w'} k
    ((GradedObject.total ℤ (ModuleCat.{u} k)).obj (unit k))
    ((GradedObject.total ℤ (ModuleCat.{u} k)).obj (unit k))
  refine ⟨fun n ↦ ?_⟩
  have hfin := (isGradedEulerAdmissible_unit.{w} k).internallyFinite.finiteLaurentSupport n
  have := hfin.finiteDimensional 0
  have := hadm.isExtFinite.finiteDimensional n
  -- In internal degree `j ≠ 0` there are no morphisms and no higher `Ext`.
  have hsub (j : ℤ) (hj : j ≠ 0) :
      Subsingleton (GradedExt.{w} (shift k) (unit k) (unit k) n j) := by
    have := hfin.finiteDimensional j
    rw [← Module.finrank_zero_iff (R := k)]
    cases n with
    | zero =>
      rw [(Ext.linearEquiv₀ (R := k)).finrank_eq, finrank_hom_unit_shift_pow]
      simp only [hj, ↓reduceIte]
    | succ m =>
      have := (isExtBoundedBy_one_of_projective.{w} (unit k)
        (((shift k) ^ j).functor.obj (unit k))).subsingleton (Nat.le_add_left 1 m)
      exact Module.finrank_zero_of_subsingleton
  -- In internal degree `0` both sides have the same dimension.
  refine ⟨(DirectSum.componentLinearEquiv _ 0 hsub).trans (LinearEquiv.ofFinrankEq _ _ ?_)⟩
  cases n with
  | zero =>
    rw [(Ext.linearEquiv₀ (R := k)).finrank_eq, finrank_hom_unit_shift_pow,
      (Ext.linearEquiv₀ (R := k)).finrank_eq, hhom.finrank_eq,
      ModuleCat.homLinearEquiv.finrank_eq,
      (LinearMap.ringLmapEquivSelf k k k).finrank_eq, Module.finrank_self]
    simp only [↓reduceIte]
  | succ m =>
    have := (isExtBoundedBy_one_of_projective.{w} (unit k)
      (((shift k) ^ (0 : ℤ)).functor.obj (unit k))).subsingleton (Nat.le_add_left 1 m)
    have := (isExtBoundedBy_one_of_projective.{w'}
      ((GradedObject.total ℤ (ModuleCat.{u} k)).obj (unit k))
      ((GradedObject.total ℤ (ModuleCat.{u} k)).obj (unit k))).subsingleton
        (Nat.le_add_left 1 m)
    rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]

/-- **At `q = 1` the q-Euler characteristic of `(M, M)` is the ordinary Ext-Euler characteristic of
the underlying ungraded pair `(U M, U M)`**, as it must be after forgetting the grading. -/
theorem laurentEval_one_gradedExtEuler_unit :
    laurentEval (1 : ℤˣ) (gradedExtEuler k (shift k) (isGradedEulerAdmissible_unit.{w} k)) =
      extEuler.{w'} k ((isGradedExtComparison_unit.{w, w'} k).isEulerAdmissible
        (isGradedEulerAdmissible_unit.{w} k)) :=
  (isGradedExtComparison_unit.{w, w'} k).laurentEval_one_gradedExtEuler _

end Comparison

end GradedVectorSpace

end TauCeti

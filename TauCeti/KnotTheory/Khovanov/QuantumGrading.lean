/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.Algebra.Module.GradedModule.Finsupp
public import TauCeti.Algebra.Module.GradedModule.GradedObject
public import TauCeti.Algebra.Module.GradedModule.Shift
public import TauCeti.Algebra.Module.GradedModule.TensorProduct
public import TauCeti.Algebra.Module.GradedModule.Trivial
public import TauCeti.KnotTheory.Khovanov.Frobenius

/-!
# The quantum grading of the Khovanov Frobenius algebra

Khovanov homology is bigraded: besides the cochain degree it carries a quantum degree, which on
the rank-two Frobenius algebra `V = R[ε]` of `TauCeti.KnotTheory.Khovanov.Frobenius` (with
`X = ε`) puts `1` in degree `1` and `X` in degree `-1`. This file constructs that grading and
records the degrees of the four Frobenius structure maps:

```text
m : V ⊗ V → V   and   Δ : V → V ⊗ V   have degree -1,
η : R → V       and   ε : V → R       have degree +1,
```

where `V ⊗ V` carries the total-degree grading and `R` the grading concentrated in degree `0`.
These degrees are what make the differential of the Khovanov complex preserve the quantum
grading once each resolution is shifted by its number of `1`-smoothings.

With the shift convention `(M⟨k⟩)ⱼ = Mⱼ₋ₖ`, the regraded algebra `W = V⟨-1⟩`, which is
`(TauCeti.Khovanov.quantumGrading R).shift 1`, has its unit and multiplication in degree `0` and
`X` in degree `-2`: it is a graded algebra.

The homogeneous pieces of `V` form a Mathlib graded object of `R`-modules,
`TauCeti.Khovanov.quantumGradedObject R`, whose categorical total is identified with the
underlying algebra `R[ε]` by `TauCeti.InternalGrading.totalIso`.

## Main definitions

* `TauCeti.Khovanov.quantumDegree`: the quantum degrees `1, -1` of the basis vectors `1, ε`.
* `TauCeti.Khovanov.quantumGrading`: the quantum grading of `R[ε]`, an internal grading.
* `TauCeti.Khovanov.quantumGradedObject`: its homogeneous pieces as a graded object of
  `ModuleCat R`.
* `TauCeti.Khovanov.instGradedAlgebraShiftOne`: the graded algebra `W = V⟨-1⟩`.

## Main results

* `TauCeti.Khovanov.mem_quantumGrading_piece_iff`: `x` has degree `p` exactly when its scalar
  coordinate vanishes unless `p = 1` and its `ε`-coordinate vanishes unless `p = -1`.
* `TauCeti.Khovanov.quantumGrading_piece_eq_bot`: every degree other than `±1` vanishes.
* `TauCeti.Khovanov.mul_mem_quantumGrading_piece`: multiplication lowers the total degree by one.
* `TauCeti.Khovanov.isHomogeneous_mul'`, `TauCeti.Khovanov.isHomogeneous_comul`,
  `TauCeti.Khovanov.isHomogeneous_algebraLinearMap`, `TauCeti.Khovanov.isHomogeneous_counit`:
  the degrees of the four structure maps.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §2.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §1.
-/

public section

open CategoryTheory TensorProduct DualNumber TrivSqZeroExt

namespace TauCeti.Khovanov

universe u

variable (R : Type u) [CommRing R]

/-- The quantum degrees of the basis `1, ε` of `R[ε]` (`TauCeti.dualNumberBasis`): `1` has
degree `1` and `X = ε` has degree `-1`. -/
def quantumDegree : Fin 2 → ℤ := ![1, -1]

/-- The basis vector `1` has quantum degree `1`. -/
@[simp]
theorem quantumDegree_zero : quantumDegree 0 = 1 := (rfl)

/-- The basis vector `ε` has quantum degree `-1`. -/
@[simp]
theorem quantumDegree_one : quantumDegree 1 = -1 := (rfl)

/-- The **quantum grading** of the Khovanov Frobenius algebra `R[ε]`: the basis vector `1` spans
degree `1`, the basis vector `ε` spans degree `-1`, and every other degree is zero. It is the
grading of the free module on the basis `1, ε` by `TauCeti.Khovanov.quantumDegree`, transported
to `R[ε]`. -/
noncomputable def quantumGrading : InternalGrading R R[ε] :=
  (InternalGrading.finsupp R quantumDegree).map (dualNumberBasis R).repr.symm

/-- The homogeneous pieces of the quantum grading as a graded object of `R`-modules: the
quantum-graded object `V` of Khovanov homology. Its categorical total is identified with `R[ε]` by
`(TauCeti.Khovanov.quantumGrading R).totalIso`. -/
noncomputable abbrev quantumGradedObject : GradedObject ℤ (ModuleCat.{u} R) :=
  (quantumGrading R).toGradedObject

variable {R}

/-- A dual number has quantum degree `p` exactly when its scalar coordinate vanishes unless
`p = 1`, and its `ε`-coordinate vanishes unless `p = -1`. -/
theorem mem_quantumGrading_piece_iff {p : ℤ} {x : R[ε]} :
    x ∈ (quantumGrading R).piece p ↔ (x.fst ≠ 0 → p = 1) ∧ (x.snd ≠ 0 → p = -1) := by
  rw [quantumGrading, InternalGrading.mem_map_piece_iff, LinearEquiv.symm_symm,
    InternalGrading.mem_finsupp_piece_iff, Fin.forall_fin_two]
  simp [eq_comm]

/-- Each basis vector of `R[ε]` is homogeneous of its quantum degree. -/
theorem dualNumberBasis_mem_quantumGrading_piece (i : Fin 2) :
    dualNumberBasis R i ∈ (quantumGrading R).piece (quantumDegree i) := by
  fin_cases i <;> simp [mem_quantumGrading_piece_iff]

/-- The degree-`1` piece consists of the scalars. -/
@[simp]
theorem mem_quantumGrading_piece_one_iff {x : R[ε]} :
    x ∈ (quantumGrading R).piece 1 ↔ x.snd = 0 := by
  simp [mem_quantumGrading_piece_iff]

/-- The degree-`-1` piece consists of the multiples of `ε`. -/
@[simp]
theorem mem_quantumGrading_piece_neg_one_iff {x : R[ε]} :
    x ∈ (quantumGrading R).piece (-1) ↔ x.fst = 0 := by
  simp [mem_quantumGrading_piece_iff]

/-- Every quantum degree other than `1` and `-1` is zero. -/
theorem quantumGrading_piece_eq_bot {p : ℤ} (h1 : p ≠ 1) (h2 : p ≠ -1) :
    (quantumGrading R).piece p = ⊥ := by
  ext x
  simp [mem_quantumGrading_piece_iff, h1, h2, TrivSqZeroExt.ext_iff]

/-- The quantum-graded object vanishes outside the degrees `1` and `-1`. -/
theorem isZero_quantumGradedObject {p : ℤ} (h1 : p ≠ 1) (h2 : p ≠ -1) :
    Limits.IsZero (quantumGradedObject R p) := by
  have : Subsingleton ((quantumGrading R).piece p) := by
    rw [quantumGrading_piece_eq_bot h1 h2]
    infer_instance
  exact ModuleCat.isZero_of_subsingleton _

/-- The unit `1` has quantum degree `1`. -/
theorem one_mem_quantumGrading_piece_one : (1 : R[ε]) ∈ (quantumGrading R).piece 1 := by
  simp

/-- The generator `X = ε` has quantum degree `-1`. -/
theorem eps_mem_quantumGrading_piece_neg_one : (ε : R[ε]) ∈ (quantumGrading R).piece (-1) := by
  simp

/-- **Multiplication has quantum degree `-1`**: the product of elements of degrees `p` and `q` has
degree `p + q - 1`. -/
theorem mul_mem_quantumGrading_piece {p q : ℤ} {x y : R[ε]}
    (hx : x ∈ (quantumGrading R).piece p) (hy : y ∈ (quantumGrading R).piece q) :
    x * y ∈ (quantumGrading R).piece (p + q - 1) := by
  rw [mem_quantumGrading_piece_iff] at hx hy ⊢
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [fst_mul] at h
    rw [hx1 (left_ne_zero_of_mul h), hy1 (right_ne_zero_of_mul h)]
    norm_num
  · rw [DualNumber.snd_mul] at h
    by_cases h' : x.fst * y.snd = 0
    · rw [h', zero_add] at h
      rw [hx2 (left_ne_zero_of_mul h), hy1 (right_ne_zero_of_mul h)]
      norm_num
    · rw [hx1 (left_ne_zero_of_mul h'), hy2 (right_ne_zero_of_mul h')]
      norm_num

/-- **The merge map `m : V ⊗ V → V` has quantum degree `-1`**, for the total-degree grading of
`V ⊗ V`. -/
theorem isHomogeneous_mul' :
    TauCeti.LinearMap.IsHomogeneous (LinearMap.mul' R R[ε])
      ((quantumGrading R).tensorProduct (quantumGrading R)).piece (quantumGrading R).piece
      (-1) := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p x hx
  refine (quantumGrading R).tensorProduct_piece_le (quantumGrading R)
    (C := ((quantumGrading R).piece (p + -1)).comap (LinearMap.mul' R R[ε]))
    (fun q a ha b hb ↦ ?_) hx
  rw [Submodule.mem_comap, LinearMap.mul'_apply]
  convert mul_mem_quantumGrading_piece ha hb using 2
  ring

/-- **The split map `Δ : V → V ⊗ V` has quantum degree `-1`**, for the total-degree grading of
`V ⊗ V`. -/
theorem isHomogeneous_comul :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := R[ε]))
      (quantumGrading R).piece ((quantumGrading R).tensorProduct (quantumGrading R)).piece
      (-1) := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p x hx
  rw [mem_quantumGrading_piece_iff] at hx
  rw [DualNumber.khovanov_comul_apply]
  have hmem {a b : R[ε]} {i j : ℤ} (ha : a ∈ (quantumGrading R).piece i)
      (hb : b ∈ (quantumGrading R).piece j) (hij : i + j = p + -1) :
      a ⊗ₜ[R] b ∈ ((quantumGrading R).tensorProduct (quantumGrading R)).piece (p + -1) :=
    hij ▸ InternalGrading.tmul_mem_tensorProduct _ _ ha hb
  refine add_mem ?_ ?_
  · by_cases h : x.fst = 0
    · simp [h]
    · obtain rfl := hx.1 h
      exact Submodule.smul_mem _ _ (add_mem
        (hmem one_mem_quantumGrading_piece_one eps_mem_quantumGrading_piece_neg_one (by norm_num))
        (hmem eps_mem_quantumGrading_piece_neg_one one_mem_quantumGrading_piece_one (by norm_num)))
  · by_cases h : x.snd = 0
    · simp [h]
    · obtain rfl := hx.2 h
      exact Submodule.smul_mem _ _
        (hmem eps_mem_quantumGrading_piece_neg_one eps_mem_quantumGrading_piece_neg_one rfl)

/-- **The unit `η : R → V` has quantum degree `1`**, for the grading of `R` concentrated in
degree `0`. -/
theorem isHomogeneous_algebraLinearMap :
    TauCeti.LinearMap.IsHomogeneous (Algebra.linearMap R R[ε]) (trivialGrading R R)
      (quantumGrading R).piece 1 := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p r hr
  rw [mem_trivialGrading_iff] at hr
  rcases hr with rfl | rfl
  · simp [TrivSqZeroExt.algebraMap_eq_inl]
  · simp

/-- **The counit `ε : V → R` has quantum degree `1`**, for the grading of `R` concentrated in
degree `0`. -/
theorem isHomogeneous_counit :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := R[ε]))
      (quantumGrading R).piece (trivialGrading R R) 1 := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p x hx
  rw [mem_quantumGrading_piece_iff] at hx
  rw [mem_trivialGrading_iff, DualNumber.khovanov_counit_apply]
  by_cases h : x.snd = 0
  · exact Or.inr h
  · exact Or.inl (by rw [hx.2 h]; norm_num)

section Shift

/-! ### The regraded algebra `W = V⟨-1⟩` -/

variable (R)

/-- In the regrading `W = V⟨-1⟩` of the quantum grading, in which `1` has degree `0`, the unit and
multiplication have degree `0`. -/
instance instGradedMonoidShiftOne : SetLike.GradedMonoid ((quantumGrading R).shift 1).piece where
  one_mem := by simp
  mul_mem i j x y hx hy := by
    simp only [InternalGrading.shift_piece] at hx hy ⊢
    convert mul_mem_quantumGrading_piece hx hy using 2
    ring

/-- The regrading `W = V⟨-1⟩` of the quantum grading makes `R[ε]` a graded algebra, with `1` in
degree `0` and `X = ε` in degree `-2`. Its decomposition is the one carried by the internal
grading. -/
noncomputable instance instGradedAlgebraShiftOne :
    GradedAlgebra ((quantumGrading R).shift 1).piece :=
  { instGradedMonoidShiftOne R,
    (inferInstance : DirectSum.Decomposition ((quantumGrading R).shift 1).piece) with }

variable {R}

/-- In the regrading `W = V⟨-1⟩`, the generator `X = ε` has degree `-2`. -/
theorem eps_mem_quantumGrading_shift_one_piece_neg_two :
    (ε : R[ε]) ∈ ((quantumGrading R).shift 1).piece (-2) := by
  simp

end Shift

end TauCeti.Khovanov

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Symplectic.Darboux.Basis
public import TauCeti.Geometry.Symplectic.StandardCompatible

import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

/-!
# Symplectic coordinate equivalences to standard Euclidean space

Given a real vector space `V` equipped with a basis indexed by `ι ⊕ ι` (in the `Matrix.J` block
convention) or by `Fin n × Fin 2` (in the interleaved Darboux convention of
`TauCeti.SymplecticForm.IsDarbouxBasis`), this file constructs the coordinate isomorphism from `V`
to the doubled Euclidean model `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι` carrying `b (inr a)` (or
`b (i, 0)`) to `(EuclideanSpace.single a 1, 0)` and `b (inl a)` (or `b (i, 1)`) to
`(0, EuclideanSpace.single a 1)`.

Because both `Matrix.J` (`ω (b (inr a)) (b (inl a)) = 1`) and `TauCeti.stdSymplecticForm`
(`ω₀ ((single a 1, 0), (0, single a 1)) = 1`) give `+1` to that ordered pair, this coordinate
equivalence is a linear symplectomorphism from `(V, ω)` to
`(EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, stdSymplecticForm)` if and only if the matrix of `ω` in
`b` is `Matrix.J` (respectively, `b` is a Darboux basis of `ω`).

On a normed space `V`, finite-dimensionality is automatic from the finite basis, upgrading both
equivalences to continuous linear equivalences. Combined with
`LinearMap.BilinForm.IsAlt.exists_basis_apply_eq_J_inl_zero_eq`, any nonzero vector in a
finite-dimensional symplectic vector space can be sent to either `(0, EuclideanSpace.single 0 1)` or
`(EuclideanSpace.single 0 1, 0)` by a continuous-linear symplectomorphism onto the standard
Euclidean model.

## Main declarations

* `TauCeti.stdSymplecticBasis`: the standard `ι ⊕ ι`-indexed basis of
  `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι` in which `stdSymplecticForm` has matrix `Matrix.J`.
* `TauCeti.stdDarbouxBasis`: the standard `Fin n × Fin 2`-indexed Darboux basis of
  `EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)`.
* `TauCeti.SymplecticForm.euclideanBasisEquiv` /
  `TauCeti.SymplecticForm.euclideanBasisContinuousLinearEquiv`: coordinate isomorphism from an
  `ι ⊕ ι`-indexed basis to `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι`.
* `TauCeti.SymplecticForm.darbouxBasisEquiv` /
  `TauCeti.SymplecticForm.darbouxBasisContinuousLinearEquiv`: coordinate isomorphism from a
  `Fin n × Fin 2`-indexed basis to `EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)`.
* `TauCeti.SymplecticForm.isSymplectomorphism_euclideanBasisEquiv_iff` and
  `TauCeti.SymplecticForm.isSymplectomorphism_darbouxBasisEquiv_iff`: necessary and sufficient
  conditions for these coordinate maps to intertwine `ω` with `stdSymplecticForm`.
* `TauCeti.SymplecticForm.exists_isSymplectomorphism_stdSymplecticForm`,
  `TauCeti.SymplecticForm.exists_continuousLinearEquiv_stdSymplecticForm`, and their fixed-dimension
  and vector-straightening variants (`_of_finrank_eq`, `_apply_eq_snd_single`,
  `_apply_eq_fst_single`): linear and continuous-linear symplectomorphisms onto the standard
  Euclidean model, optionally straightening a prescribed nonzero vector.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Sections 2.1 and 3.2.
-/

public section

open Module
open scoped InnerProductSpace

namespace TauCeti

section StandardBasis

variable {ι : Type*} [Fintype ι]

/-- The standard `ι ⊕ ι`-indexed basis of `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι` adapted to
`Matrix.J`: `Sum.inr a` maps to `(single a 1, 0)` in the first factor and `Sum.inl a` maps to
`(0, single a 1)` in the second factor. -/
noncomputable def stdSymplecticBasis (ι : Type*) [Fintype ι] :
    Basis (ι ⊕ ι) ℝ (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :=
  ((EuclideanSpace.basisFun ι ℝ).toBasis.prod (EuclideanSpace.basisFun ι ℝ).toBasis).reindex
    (Equiv.sumComm ι ι)

@[simp]
theorem stdSymplecticBasis_inr [DecidableEq ι] (a : ι) :
    stdSymplecticBasis ι (Sum.inr a) = (EuclideanSpace.single a 1, 0) := by
  simp [stdSymplecticBasis, Basis.prod_apply, EuclideanSpace.basisFun_apply]

@[simp]
theorem stdSymplecticBasis_inl [DecidableEq ι] (a : ι) :
    stdSymplecticBasis ι (Sum.inl a) = (0, EuclideanSpace.single a 1) := by
  simp [stdSymplecticBasis, Basis.prod_apply, EuclideanSpace.basisFun_apply]

@[simp]
theorem stdSymplecticBasis_repr_inr (u : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (a : ι) :
    (stdSymplecticBasis ι).repr u (Sum.inr a) = u.1 a := by
  simp [stdSymplecticBasis]

@[simp]
theorem stdSymplecticBasis_repr_inl (u : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (a : ι) :
    (stdSymplecticBasis ι).repr u (Sum.inl a) = u.2 a := by
  simp [stdSymplecticBasis]

/-- In `stdSymplecticBasis ι`, the matrix of `stdSymplecticForm` is `Matrix.J ι ℝ`. -/
@[simp]
theorem toMatrix_stdSymplecticBasis [DecidableEq ι] :
    LinearMap.BilinForm.toMatrix (stdSymplecticBasis ι)
      (stdSymplecticForm (V := EuclideanSpace ℝ ι)).toBilinForm = Matrix.J ι ℝ := by
  ext (a | a) (b | b) <;>
    simp [LinearMap.BilinForm.toMatrix_apply, Matrix.J, stdSymplecticForm_apply,
      EuclideanSpace.inner_single_left, PiLp.single_apply, Matrix.one_apply, eq_comm]

/-- The standard `Fin n × Fin 2`-indexed Darboux basis of
`EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)`, sending `(i, 0)` to `(single i 1, 0)` and
`(i, 1)` to `(0, single i 1)`. -/
noncomputable def stdDarbouxBasis (n : ℕ) :
    Basis (Fin n × Fin 2) ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
  (stdSymplecticBasis (Fin n)).reindex (SymplecticForm.darbouxIndexEquiv n).symm

@[simp]
theorem stdDarbouxBasis_zero {n : ℕ} (i : Fin n) :
    stdDarbouxBasis n (i, 0) = (EuclideanSpace.single i 1, 0) := by
  simp [stdDarbouxBasis]

@[simp]
theorem stdDarbouxBasis_one {n : ℕ} (i : Fin n) :
    stdDarbouxBasis n (i, 1) = (0, EuclideanSpace.single i 1) := by
  simp [stdDarbouxBasis]

@[simp]
theorem stdDarbouxBasis_repr_zero {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (stdDarbouxBasis n).repr u (i, 0) = u.1 i := by
  simp [stdDarbouxBasis]

@[simp]
theorem stdDarbouxBasis_repr_one {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (stdDarbouxBasis n).repr u (i, 1) = u.2 i := by
  simp [stdDarbouxBasis]

/-- `stdDarbouxBasis n` is a Darboux basis of `stdSymplecticForm` on
`EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)`. -/
theorem isDarbouxBasis_stdDarbouxBasis (n : ℕ) :
    (stdSymplecticForm (V := EuclideanSpace ℝ (Fin n))).IsDarbouxBasis (stdDarbouxBasis n) :=
  SymplecticForm.isDarbouxBasis_reindex_symm_iff.2 toMatrix_stdSymplecticBasis

end StandardBasis

namespace SymplecticForm

section Linear

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The linear coordinate equivalence from an `ι ⊕ ι`-indexed basis `b` of `V` to
`EuclideanSpace ℝ ι × EuclideanSpace ℝ ι` sending `b (Sum.inr a)` to `(single a 1, 0)` and
`b (Sum.inl a)` to `(0, single a 1)`. -/
noncomputable def euclideanBasisEquiv {ι : Type*} [Fintype ι] (b : Basis (ι ⊕ ι) ℝ V) :
    V ≃ₗ[ℝ] EuclideanSpace ℝ ι × EuclideanSpace ℝ ι :=
  b.equiv (stdSymplecticBasis ι) (Equiv.refl (ι ⊕ ι))

@[simp]
theorem euclideanBasisEquiv_apply_inr {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis (ι ⊕ ι) ℝ V) (a : ι) :
    euclideanBasisEquiv b (b (Sum.inr a)) = (EuclideanSpace.single a 1, 0) := by
  simp [euclideanBasisEquiv]

@[simp]
theorem euclideanBasisEquiv_apply_inl {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis (ι ⊕ ι) ℝ V) (a : ι) :
    euclideanBasisEquiv b (b (Sum.inl a)) = (0, EuclideanSpace.single a 1) := by
  simp [euclideanBasisEquiv]

@[simp]
theorem stdSymplecticBasis_repr_euclideanBasisEquiv {ι : Type*} [Fintype ι]
    (b : Basis (ι ⊕ ι) ℝ V) (v : V) :
    (stdSymplecticBasis ι).repr (euclideanBasisEquiv b v) = b.repr v := by
  simp [euclideanBasisEquiv, Basis.equiv]

@[simp]
theorem euclideanBasisEquiv_fst_apply {ι : Type*} [Fintype ι] (b : Basis (ι ⊕ ι) ℝ V)
    (v : V) (a : ι) : (euclideanBasisEquiv b v).1 a = b.repr v (Sum.inr a) := by
  rw [← stdSymplecticBasis_repr_inr, stdSymplecticBasis_repr_euclideanBasisEquiv]

@[simp]
theorem euclideanBasisEquiv_snd_apply {ι : Type*} [Fintype ι] (b : Basis (ι ⊕ ι) ℝ V)
    (v : V) (a : ι) : (euclideanBasisEquiv b v).2 a = b.repr v (Sum.inl a) := by
  rw [← stdSymplecticBasis_repr_inl, stdSymplecticBasis_repr_euclideanBasisEquiv]

/-- The inverse of `euclideanBasisEquiv b` expands `(q, p)` as
`∑ a, q a • b (inr a) + ∑ a, p a • b (inl a)`. -/
theorem euclideanBasisEquiv_symm_apply {ι : Type*} [Fintype ι] (b : Basis (ι ⊕ ι) ℝ V)
    (u : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    (euclideanBasisEquiv b).symm u =
      (∑ a, u.1 a • b (Sum.inr a)) + ∑ a, u.2 a • b (Sum.inl a) := by
  have hm := congrArg (euclideanBasisEquiv b).symm ((stdSymplecticBasis ι).sum_repr u).symm
  rw [map_sum, Fintype.sum_sum_type, add_comm] at hm
  refine hm.trans ?_
  congr 1 <;> refine Finset.sum_congr rfl fun a _ ↦ ?_ <;> simp [euclideanBasisEquiv]

/-- `euclideanBasisEquiv b` is a symplectomorphism from `ω` to `stdSymplecticForm` if and only if
the matrix of `ω` in `b` is `Matrix.J ι ℝ`. -/
theorem isSymplectomorphism_euclideanBasisEquiv_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ω : SymplecticForm V} {b : Basis (ι ⊕ ι) ℝ V} :
    IsSymplectomorphism ω (stdSymplecticForm (V := EuclideanSpace ℝ ι)) (euclideanBasisEquiv b) ↔
      LinearMap.BilinForm.toMatrix b ω.toBilinForm = Matrix.J ι ℝ := by
  have hstd (x y : ι ⊕ ι) :
      stdSymplecticForm (stdSymplecticBasis ι x) (stdSymplecticBasis ι y) = Matrix.J ι ℝ x y := by
    rw [← toMatrix_stdSymplecticBasis, LinearMap.BilinForm.toMatrix_apply]
  rw [isSymplectomorphism_iff]
  constructor
  · intro h
    ext x y
    rw [LinearMap.BilinForm.toMatrix_apply, ← hstd x y]
    simpa [euclideanBasisEquiv] using (h (b x) (b y)).symm
  · intro h
    have hxy (x y : ι ⊕ ι) :
        stdSymplecticForm (euclideanBasisEquiv b (b x)) (euclideanBasisEquiv b (b y)) =
          ω (b x) (b y) := by
      simp only [euclideanBasisEquiv, Basis.equiv_apply, Equiv.refl_apply, hstd]
      rw [← h, LinearMap.BilinForm.toMatrix_apply]
    intro u w
    have hl :
        ((stdSymplecticForm (V := EuclideanSpace ℝ ι)).toBilinForm.compl₁₂
          (euclideanBasisEquiv b).toLinearMap (euclideanBasisEquiv b).toLinearMap) =
          ω.toBilinForm :=
      b.ext fun x ↦ b.ext fun y ↦ hxy x y
    exact LinearMap.congr_fun₂ hl u w

/-- The linear coordinate equivalence from a `Fin n × Fin 2`-indexed basis `b` of `V` to
`EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)` sending `b (i, 0)` to `(single i 1, 0)` and
`b (i, 1)` to `(0, single i 1)`. -/
noncomputable def darbouxBasisEquiv {n : ℕ} (b : Basis (Fin n × Fin 2) ℝ V) :
    V ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
  b.equiv (stdDarbouxBasis n) (Equiv.refl (Fin n × Fin 2))

/-- `darbouxBasisEquiv b` agrees with `euclideanBasisEquiv` applied to `b` relabelled by
`darbouxIndexEquiv n`. -/
theorem darbouxBasisEquiv_eq_euclideanBasisEquiv_reindex {n : ℕ} (b : Basis (Fin n × Fin 2) ℝ V) :
    darbouxBasisEquiv b = euclideanBasisEquiv (b.reindex (darbouxIndexEquiv n)) := by
  refine (b.reindex (darbouxIndexEquiv n)).ext' fun x ↦ ?_
  rcases x with i | i
  · rw [euclideanBasisEquiv_apply_inl]
    simp [darbouxBasisEquiv]
  · rw [euclideanBasisEquiv_apply_inr]
    simp [darbouxBasisEquiv]

@[simp]
theorem darbouxBasisEquiv_apply_zero {n : ℕ} (b : Basis (Fin n × Fin 2) ℝ V) (i : Fin n) :
    darbouxBasisEquiv b (b (i, 0)) = (EuclideanSpace.single i 1, 0) := by
  simp [darbouxBasisEquiv]

@[simp]
theorem darbouxBasisEquiv_apply_one {n : ℕ} (b : Basis (Fin n × Fin 2) ℝ V) (i : Fin n) :
    darbouxBasisEquiv b (b (i, 1)) = (0, EuclideanSpace.single i 1) := by
  simp [darbouxBasisEquiv]

@[simp]
theorem darbouxBasisEquiv_fst_apply {n : ℕ} (b : Basis (Fin n × Fin 2) ℝ V)
    (v : V) (i : Fin n) : (darbouxBasisEquiv b v).1 i = b.repr v (i, 0) := by
  rw [darbouxBasisEquiv_eq_euclideanBasisEquiv_reindex, euclideanBasisEquiv_fst_apply]
  simp

@[simp]
theorem darbouxBasisEquiv_snd_apply {n : ℕ} (b : Basis (Fin n × Fin 2) ℝ V)
    (v : V) (i : Fin n) : (darbouxBasisEquiv b v).2 i = b.repr v (i, 1) := by
  rw [darbouxBasisEquiv_eq_euclideanBasisEquiv_reindex, euclideanBasisEquiv_snd_apply]
  simp

/-- The inverse of `darbouxBasisEquiv b` expands `(q, p)` as
`∑ i, q i • b (i, 0) + ∑ i, p i • b (i, 1)`. -/
theorem darbouxBasisEquiv_symm_apply {n : ℕ} (b : Basis (Fin n × Fin 2) ℝ V)
    (u : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    (darbouxBasisEquiv b).symm u =
      (∑ i, u.1 i • b (i, 0)) + ∑ i, u.2 i • b (i, 1) := by
  rw [darbouxBasisEquiv_eq_euclideanBasisEquiv_reindex, euclideanBasisEquiv_symm_apply]
  simp

/-- `darbouxBasisEquiv b` is a symplectomorphism from `ω` to `stdSymplecticForm` if and only if
`b` is a Darboux basis of `ω`. -/
theorem isSymplectomorphism_darbouxBasisEquiv_iff {n : ℕ} {ω : SymplecticForm V}
    {b : Basis (Fin n × Fin 2) ℝ V} :
    IsSymplectomorphism ω (stdSymplecticForm (V := EuclideanSpace ℝ (Fin n)))
        (darbouxBasisEquiv b) ↔ ω.IsDarbouxBasis b := by
  rw [darbouxBasisEquiv_eq_euclideanBasisEquiv_reindex, isSymplectomorphism_euclideanBasisEquiv_iff,
    isDarbouxBasis_iff_toMatrix_reindex]

/-- The coordinate equivalence of a Darboux basis is a linear symplectomorphism onto
`stdSymplecticForm`. -/
theorem IsDarbouxBasis.isSymplectomorphism_darbouxBasisEquiv {n : ℕ} {ω : SymplecticForm V}
    {b : Basis (Fin n × Fin 2) ℝ V} (hb : ω.IsDarbouxBasis b) :
    IsSymplectomorphism ω (stdSymplecticForm (V := EuclideanSpace ℝ (Fin n)))
      (darbouxBasisEquiv b) :=
  isSymplectomorphism_darbouxBasisEquiv_iff.2 hb

/-- Transporting `ω` along the coordinate equivalence of a Darboux basis yields
`stdSymplecticForm`. -/
theorem IsDarbouxBasis.transport_darbouxBasisEquiv {n : ℕ} {ω : SymplecticForm V}
    {b : Basis (Fin n × Fin 2) ℝ V} (hb : ω.IsDarbouxBasis b) :
    ω.transport (darbouxBasisEquiv b) = stdSymplecticForm (V := EuclideanSpace ℝ (Fin n)) :=
  isSymplectomorphism_iff_transport_eq.1 hb.isSymplectomorphism_darbouxBasisEquiv

/-- Every finite-dimensional symplectic space is linearly symplectomorphic to
`EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)` with `stdSymplecticForm`. -/
theorem exists_isSymplectomorphism_stdSymplecticForm [FiniteDimensional ℝ V]
    (ω : SymplecticForm V) :
    ∃ (n : ℕ) (e : V ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      IsSymplectomorphism ω (stdSymplecticForm (V := EuclideanSpace ℝ (Fin n))) e := by
  obtain ⟨n, b, hb⟩ := ω.exists_isDarbouxBasis
  exact ⟨n, darbouxBasisEquiv b, hb.isSymplectomorphism_darbouxBasisEquiv⟩

/-- A finite-dimensional symplectic space of dimension `2 * n` is linearly symplectomorphic to
`EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)` with `stdSymplecticForm`. -/
theorem exists_isSymplectomorphism_stdSymplecticForm_of_finrank_eq [FiniteDimensional ℝ V]
    {n : ℕ} (ω : SymplecticForm V) (hn : finrank ℝ V = 2 * n) :
    ∃ e : V ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      IsSymplectomorphism ω (stdSymplecticForm (V := EuclideanSpace ℝ (Fin n))) e := by
  obtain ⟨b, hb⟩ := ω.exists_isDarbouxBasis_of_finrank_eq (n := n) (hn.trans (Nat.mul_comm 2 n))
  exact ⟨darbouxBasisEquiv b, hb.isSymplectomorphism_darbouxBasisEquiv⟩

/-- Every nonzero vector in a finite-dimensional symplectic space is mapped to
`(0, EuclideanSpace.single 0 1)` by a linear symplectomorphism onto the standard Euclidean model. -/
theorem exists_isSymplectomorphism_stdSymplecticForm_apply_eq_snd_single [FiniteDimensional ℝ V]
    (ω : SymplecticForm V) {v : V} (hv : v ≠ 0) :
    ∃ (m : ℕ) (e : V ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)) × EuclideanSpace ℝ (Fin (m + 1))),
      IsSymplectomorphism ω (stdSymplecticForm (V := EuclideanSpace ℝ (Fin (m + 1)))) e ∧
        e v = (0, EuclideanSpace.single 0 1) := by
  obtain ⟨m, b, hb, hbv⟩ := ω.isAlt.exists_basis_apply_eq_J_inl_zero_eq ω.nondegenerate hv
  refine ⟨m, euclideanBasisEquiv b, isSymplectomorphism_euclideanBasisEquiv_iff.2 ?_, ?_⟩
  · ext x y
    rw [LinearMap.BilinForm.toMatrix_apply]
    exact hb x y
  · rw [← hbv, euclideanBasisEquiv_apply_inl]

/-- Every nonzero vector in a finite-dimensional symplectic space is mapped to
`(EuclideanSpace.single 0 1, 0)` by a linear symplectomorphism onto the standard Euclidean model. -/
theorem exists_isSymplectomorphism_stdSymplecticForm_apply_eq_fst_single [FiniteDimensional ℝ V]
    (ω : SymplecticForm V) {v : V} (hv : v ≠ 0) :
    ∃ (m : ℕ) (e : V ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)) × EuclideanSpace ℝ (Fin (m + 1))),
      IsSymplectomorphism ω (stdSymplecticForm (V := EuclideanSpace ℝ (Fin (m + 1)))) e ∧
        e v = (EuclideanSpace.single 0 1, 0) := by
  obtain ⟨m, e, he, hev⟩ := ω.exists_isSymplectomorphism_stdSymplecticForm_apply_eq_snd_single hv
  let J₀ := AlmostComplexStructure.product (EuclideanSpace ℝ (Fin (m + 1)))
  have hJ₀ : IsSymplectomorphism
      (stdSymplecticForm (V := EuclideanSpace ℝ (Fin (m + 1))))
      (stdSymplecticForm (V := EuclideanSpace ℝ (Fin (m + 1)))) J₀.linearEquiv :=
    isSymplectomorphism_iff.2
      ((invariant_iff _ J₀).1 (stdSymplecticForm_invariant_product (V := _)))
  refine ⟨m, e.trans J₀.linearEquiv.symm, he.trans hJ₀.symm, ?_⟩
  simp [J₀, hev]

end Linear

section Normed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The continuous-linear coordinate equivalence from an `ι ⊕ ι`-indexed basis `b` of a real
normed space `V` to `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι`. Finite-dimensionality of `V` is
inferred from the finite basis `b`. -/
noncomputable def euclideanBasisContinuousLinearEquiv {ι : Type*} [Fintype ι]
    (b : Basis (ι ⊕ ι) ℝ V) : V ≃L[ℝ] EuclideanSpace ℝ ι × EuclideanSpace ℝ ι :=
  haveI : FiniteDimensional ℝ V := Module.Finite.of_basis b
  (euclideanBasisEquiv b).toContinuousLinearEquiv

@[simp]
theorem euclideanBasisContinuousLinearEquiv_toLinearEquiv {ι : Type*} [Fintype ι]
    (b : Basis (ι ⊕ ι) ℝ V) :
    (euclideanBasisContinuousLinearEquiv b).toLinearEquiv = euclideanBasisEquiv b := by
  rfl

@[simp]
theorem coe_euclideanBasisContinuousLinearEquiv {ι : Type*} [Fintype ι]
    (b : Basis (ι ⊕ ι) ℝ V) :
    ⇑(euclideanBasisContinuousLinearEquiv b) = ⇑(euclideanBasisEquiv b) := by
  rfl

@[simp]
theorem coe_euclideanBasisContinuousLinearEquiv_symm {ι : Type*} [Fintype ι]
    (b : Basis (ι ⊕ ι) ℝ V) :
    ⇑(euclideanBasisContinuousLinearEquiv b).symm = ⇑(euclideanBasisEquiv b).symm := by
  rfl

/-- The continuous-linear coordinate equivalence from a `Fin n × Fin 2`-indexed basis `b` of a
real normed space `V` to `EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)`. -/
noncomputable def darbouxBasisContinuousLinearEquiv {n : ℕ} (b : Basis (Fin n × Fin 2) ℝ V) :
    V ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
  haveI : FiniteDimensional ℝ V := Module.Finite.of_basis b
  (darbouxBasisEquiv b).toContinuousLinearEquiv

@[simp]
theorem darbouxBasisContinuousLinearEquiv_toLinearEquiv {n : ℕ} (b : Basis (Fin n × Fin 2) ℝ V) :
    (darbouxBasisContinuousLinearEquiv b).toLinearEquiv = darbouxBasisEquiv b := by
  rfl

@[simp]
theorem coe_darbouxBasisContinuousLinearEquiv {n : ℕ} (b : Basis (Fin n × Fin 2) ℝ V) :
    ⇑(darbouxBasisContinuousLinearEquiv b) = ⇑(darbouxBasisEquiv b) := by
  rfl

@[simp]
theorem coe_darbouxBasisContinuousLinearEquiv_symm {n : ℕ} (b : Basis (Fin n × Fin 2) ℝ V) :
    ⇑(darbouxBasisContinuousLinearEquiv b).symm = ⇑(darbouxBasisEquiv b).symm := by
  rfl

/-- Every finite-dimensional normed symplectic space is continuous-linearly symplectomorphic to
`EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)` with `stdSymplecticForm`. -/
theorem exists_continuousLinearEquiv_stdSymplecticForm [FiniteDimensional ℝ V]
    (ω : SymplecticForm V) :
    ∃ (n : ℕ) (e : V ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      IsSymplectomorphism ω (stdSymplecticForm (V := EuclideanSpace ℝ (Fin n)))
        e.toLinearEquiv := by
  obtain ⟨n, e, he⟩ := ω.exists_isSymplectomorphism_stdSymplecticForm
  exact ⟨n, e.toContinuousLinearEquiv, he⟩

/-- A finite-dimensional normed symplectic space of dimension `2 * n` is continuous-linearly
symplectomorphic to `EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)` with
`stdSymplecticForm`. -/
theorem exists_continuousLinearEquiv_stdSymplecticForm_of_finrank_eq [FiniteDimensional ℝ V]
    {n : ℕ} (ω : SymplecticForm V) (hn : finrank ℝ V = 2 * n) :
    ∃ e : V ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      IsSymplectomorphism ω (stdSymplecticForm (V := EuclideanSpace ℝ (Fin n)))
        e.toLinearEquiv := by
  obtain ⟨e, he⟩ := ω.exists_isSymplectomorphism_stdSymplecticForm_of_finrank_eq hn
  exact ⟨e.toContinuousLinearEquiv, he⟩

/-- Every nonzero vector in a finite-dimensional normed symplectic space is carried to
`(0, EuclideanSpace.single 0 1)` by a continuous-linear symplectomorphism onto the standard
Euclidean model. -/
theorem exists_continuousLinearEquiv_stdSymplecticForm_apply_eq_snd_single [FiniteDimensional ℝ V]
    (ω : SymplecticForm V) {v : V} (hv : v ≠ 0) :
    ∃ (m : ℕ) (e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) × EuclideanSpace ℝ (Fin (m + 1))),
      IsSymplectomorphism ω (stdSymplecticForm (V := EuclideanSpace ℝ (Fin (m + 1))))
        e.toLinearEquiv ∧ e v = (0, EuclideanSpace.single 0 1) := by
  obtain ⟨m, e, he, hev⟩ := ω.exists_isSymplectomorphism_stdSymplecticForm_apply_eq_snd_single hv
  exact ⟨m, e.toContinuousLinearEquiv, he, hev⟩

/-- Every nonzero vector in a finite-dimensional normed symplectic space is carried to
`(EuclideanSpace.single 0 1, 0)` by a continuous-linear symplectomorphism onto the standard
Euclidean model. -/
theorem exists_continuousLinearEquiv_stdSymplecticForm_apply_eq_fst_single [FiniteDimensional ℝ V]
    (ω : SymplecticForm V) {v : V} (hv : v ≠ 0) :
    ∃ (m : ℕ) (e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) × EuclideanSpace ℝ (Fin (m + 1))),
      IsSymplectomorphism ω (stdSymplecticForm (V := EuclideanSpace ℝ (Fin (m + 1))))
        e.toLinearEquiv ∧ e v = (EuclideanSpace.single 0 1, 0) := by
  obtain ⟨m, e, he, hev⟩ := ω.exists_isSymplectomorphism_stdSymplecticForm_apply_eq_fst_single hv
  exact ⟨m, e.toContinuousLinearEquiv, he, hev⟩

end Normed

end SymplecticForm

end TauCeti

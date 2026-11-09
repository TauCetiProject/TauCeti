/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.LinearAlgebra.CliffordAlgebra.Classification

/-!
# The orthonormal coordinate model of the negative-definite Clifford form

Let `V` be a real inner product space of dimension `n` and `Q` the quadratic form
`Q v = -‖v‖²`, the sign convention under which geometric Clifford multiplication satisfies
`c(v) c(w) + c(w) c(v) = -2 ⟪v, w⟫`. The coordinate model of this form is the negative-definite
signature form `realCliffordForm 0 n`, `x ↦ -∑ᵢ xᵢ²`, whose Clifford algebra is the real Clifford
algebra `Cliff(0, n)`. An orthonormal basis `b` of `V` identifies the two: its coordinate map is a
quadratic isometry `OrthonormalBasis.isometryEquivRealCliffordForm` from `Q` to
`realCliffordForm 0 n`, sending each basis vector `b i` to the corresponding coordinate unit
vector. Through `CliffordAlgebra.equivOfIsometry` and the general isometry API this carries the
Clifford algebra to the coordinate model, compatibly with the grading
(`CliffordAlgebra.map_evenOdd_equivOfIsometry`), the grade involution and reversal
(`CliffordAlgebra.map_involute`, `CliffordAlgebra.map_reverse`), and the Spin groups
(`QuadraticMap.IsometryEquiv.spinGroupEquiv`); in particular every result about `Cliff(0, n)`
applies to `CliffordAlgebra Q`. The coordinate model
of a basis transported along a linear isometry is the transported coordinate model
(`OrthonormalBasis.isometryEquivRealCliffordForm_map`), so the identification is natural in the
Euclidean space.

The second part transports the classification of real Clifford algebras: in the residue class of
`n` modulo eight, `CliffordAlgebra Q` is the matrix algebra over `ℝ`, `ℂ` or `ℍ`, or the product
of two copies of one, prescribed by the table for `Cliff(0, n)`.

## Main definitions

* `OrthonormalBasis.isometryEquivRealCliffordForm`: the coordinate isometry from
  `Q v = -‖v‖²` to `realCliffordForm 0 n` given by an orthonormal basis.

## Main results

* `OrthonormalBasis.isometryEquivRealCliffordForm_apply_self`: a basis vector goes to the
  corresponding coordinate unit vector.
* `OrthonormalBasis.isometryEquivRealCliffordForm_map`: naturality along linear isometries.
* `TauCeti.nonempty_algEquiv_cliffordAlgebra_realCliffordForm`: `CliffordAlgebra Q` is isomorphic
  to `Cliff(0, dim V)`.
* `TauCeti.cliffordAlgebra_classification_of_finrank_mod_eight_eq_zero` and its seven companions:
  the real classification table for `CliffordAlgebra Q`, indexed by `dim V` modulo eight.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §§3–4, Table II.
-/

public section

open CliffordAlgebra Module
open scoped Quaternion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}
  (hQ : ∀ v, Q v = -‖v‖ ^ 2)
include hQ

namespace OrthonormalBasis

open TauCeti

variable {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ V)

/-- **The orthonormal coordinate model of the negative-definite form.** For `Q v = -‖v‖²`, the
coordinate map `v ↦ (b.repr v i)ᵢ` of an orthonormal basis `b` indexed by `Fin n` is an isometry
from `Q` to the negative-definite signature form `realCliffordForm 0 n`, whose coordinates are
indexed by `Fin (0 + n)`. -/
noncomputable def isometryEquivRealCliffordForm : Q.IsometryEquiv (realCliffordForm 0 n) where
  toLinearEquiv := b.repr.toLinearEquiv ≪≫ₗ WithLp.linearEquiv 2 ℝ (Fin n → ℝ) ≪≫ₗ
    LinearEquiv.funCongrLeft ℝ ℝ (finCongr (zero_add n))
  map_app' v := by
    simp only [realCliffordForm_apply, hQ, ← b.repr.norm_map, EuclideanSpace.real_norm_sq_eq,
      ← Finset.sum_neg_distrib]
    refine (Fintype.sum_equiv (finCongr (zero_add n)) _ _ fun i ↦ ?_)
    rw [realCliffordWeight_of_le (Nat.zero_le _)]
    simp [_root_.sq]

/-- The coordinate model sends `v` to its coordinates in the orthonormal basis, reindexed from
`Fin n` to `Fin (0 + n)`. -/
@[simp]
theorem isometryEquivRealCliffordForm_apply (v : V) (i : Fin (0 + n)) :
    b.isometryEquivRealCliffordForm hQ v i = b.repr v (Fin.cast (zero_add n) i) :=
  (rfl)

/-- The coordinate model sends the basis vector `b i` to the coordinate unit vector at `i`. -/
@[simp]
theorem isometryEquivRealCliffordForm_apply_self (i : Fin n) :
    b.isometryEquivRealCliffordForm hQ (b i) = Pi.single (Fin.cast (zero_add n).symm i) 1 := by
  ext j
  simp [Pi.single_apply, Fin.ext_iff]

/-- The inverse of the coordinate model sends a coordinate unit vector to the corresponding
basis vector. -/
@[simp]
theorem isometryEquivRealCliffordForm_symm_apply_single (i : Fin (0 + n)) :
    (b.isometryEquivRealCliffordForm hQ).symm (Pi.single i 1) = b (Fin.cast (zero_add n) i) := by
  rw [QuadraticMap.IsometryEquiv.symm_apply_eq, isometryEquivRealCliffordForm_apply_self,
    Fin.cast_cast, Fin.cast_eq_self]

/-- **Naturality of the coordinate model**: transporting the orthonormal basis along a linear
isometry `φ : V ≃ₗᵢ[ℝ] W` gives the coordinate model of `W` that agrees with that of `V` along
`φ`. -/
theorem isometryEquivRealCliffordForm_map {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] {Q' : QuadraticForm ℝ W} (hQ' : ∀ w, Q' w = -‖w‖ ^ 2)
    (φ : V ≃ₗᵢ[ℝ] W) (v : V) :
    (b.map φ).isometryEquivRealCliffordForm hQ' (φ v) = b.isometryEquivRealCliffordForm hQ v := by
  ext i
  simp only [isometryEquivRealCliffordForm_apply, OrthonormalBasis.repr_apply_apply,
    OrthonormalBasis.map_apply, LinearIsometryEquiv.inner_map_map]

end OrthonormalBasis

namespace TauCeti

variable [FiniteDimensional ℝ V]

/-- For `Q v = -‖v‖²`, the Clifford algebra of `Q` is isomorphic to the real Clifford algebra
`Cliff(0, dim V)` of the negative-definite signature form. An explicit isomorphism is
`CliffordAlgebra.equivOfIsometry` of the coordinate model
`OrthonormalBasis.isometryEquivRealCliffordForm` of any orthonormal basis. -/
theorem nonempty_algEquiv_cliffordAlgebra_realCliffordForm :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ] CliffordAlgebra (realCliffordForm 0 (finrank ℝ V))) :=
  ⟨equivOfIsometry ((stdOrthonormalBasis ℝ V).isometryEquivRealCliffordForm hQ)⟩

/-- A classification statement for `Cliff(0, n)` whose model is indexed by `0 + n`, transported to
`CliffordAlgebra Q` with the model indexed by `n = dim V`. -/
private theorem nonempty_algEquiv_of_realCliffordForm {A : ℕ → Type*} [∀ m, Ring (A m)]
    [∀ m, Algebra ℝ (A m)]
    (h : Nonempty (CliffordAlgebra (realCliffordForm 0 (finrank ℝ V)) ≃ₐ[ℝ]
      A (0 + finrank ℝ V))) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ] A (finrank ℝ V)) := by
  obtain ⟨e⟩ := nonempty_algEquiv_cliffordAlgebra_realCliffordForm hQ
  obtain ⟨f⟩ := h
  -- `0 + n` is not definitionally `n`, and rewriting it inside `f` would also hit the coordinate
  -- type of `realCliffordForm 0 n`, so the model is transported along an equality of indices.
  have hA : ∀ m, m = finrank ℝ V → Nonempty (A m ≃ₐ[ℝ] A (finrank ℝ V)) := by
    rintro m rfl
    exact ⟨AlgEquiv.refl⟩
  obtain ⟨g⟩ := hA _ (zero_add _)
  exact ⟨e.trans (f.trans g)⟩

/-- **The classification for `dim V ≡ 0 mod 8`**: for `Q v = -‖v‖²`, the Clifford algebra of `Q`
is the real matrix algebra of size `2 ^ (dim V / 2)`. -/
theorem cliffordAlgebra_classification_of_finrank_mod_eight_eq_zero
    (h : finrank ℝ V % 8 = 0) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ]
      Matrix (Fin (2 ^ (finrank ℝ V / 2))) (Fin (2 ^ (finrank ℝ V / 2))) ℝ) :=
  nonempty_algEquiv_of_realCliffordForm hQ
    (A := fun m ↦ Matrix (Fin (2 ^ (m / 2))) (Fin (2 ^ (m / 2))) ℝ)
    (realClifford_classification_of_residue_eq_zero 0 _
      (by rw [realCliffordResidue_def]; omega))

/-- **The classification for `dim V ≡ 1 mod 8`**: for `Q v = -‖v‖²`, the Clifford algebra of `Q`
is the complex matrix algebra of size `2 ^ ((dim V - 1) / 2)`. -/
theorem cliffordAlgebra_classification_of_finrank_mod_eight_eq_one
    (h : finrank ℝ V % 8 = 1) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((finrank ℝ V - 1) / 2))) (Fin (2 ^ ((finrank ℝ V - 1) / 2))) ℂ) :=
  nonempty_algEquiv_of_realCliffordForm hQ
    (A := fun m ↦ Matrix (Fin (2 ^ ((m - 1) / 2))) (Fin (2 ^ ((m - 1) / 2))) ℂ)
    (realClifford_classification_of_residue_eq_one 0 _
      (by rw [realCliffordResidue_def]; omega))

/-- **The classification for `dim V ≡ 2 mod 8`**: for `Q v = -‖v‖²`, the Clifford algebra of `Q`
is the quaternionic matrix algebra of size `2 ^ ((dim V - 2) / 2)`. -/
theorem cliffordAlgebra_classification_of_finrank_mod_eight_eq_two
    (h : finrank ℝ V % 8 = 2) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((finrank ℝ V - 2) / 2))) (Fin (2 ^ ((finrank ℝ V - 2) / 2))) ℍ[ℝ]) :=
  nonempty_algEquiv_of_realCliffordForm hQ
    (A := fun m ↦ Matrix (Fin (2 ^ ((m - 2) / 2))) (Fin (2 ^ ((m - 2) / 2))) ℍ[ℝ])
    (realClifford_classification_of_residue_eq_two 0 _
      (by rw [realCliffordResidue_def]; omega))

/-- **The classification for `dim V ≡ 3 mod 8`**: for `Q v = -‖v‖²`, the Clifford algebra of `Q`
is the product of two quaternionic matrix algebras of size `2 ^ ((dim V - 3) / 2)`. -/
theorem cliffordAlgebra_classification_of_finrank_mod_eight_eq_three
    (h : finrank ℝ V % 8 = 3) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((finrank ℝ V - 3) / 2))) (Fin (2 ^ ((finrank ℝ V - 3) / 2))) ℍ[ℝ] ×
        Matrix (Fin (2 ^ ((finrank ℝ V - 3) / 2))) (Fin (2 ^ ((finrank ℝ V - 3) / 2))) ℍ[ℝ]) :=
  nonempty_algEquiv_of_realCliffordForm hQ
    (A := fun m ↦ Matrix (Fin (2 ^ ((m - 3) / 2))) (Fin (2 ^ ((m - 3) / 2))) ℍ[ℝ] ×
      Matrix (Fin (2 ^ ((m - 3) / 2))) (Fin (2 ^ ((m - 3) / 2))) ℍ[ℝ])
    (realClifford_classification_of_residue_eq_three 0 _
      (by rw [realCliffordResidue_def]; omega))

/-- **The classification for `dim V ≡ 4 mod 8`**: for `Q v = -‖v‖²`, the Clifford algebra of `Q`
is the quaternionic matrix algebra of size `2 ^ ((dim V - 2) / 2)`. -/
theorem cliffordAlgebra_classification_of_finrank_mod_eight_eq_four
    (h : finrank ℝ V % 8 = 4) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((finrank ℝ V - 2) / 2))) (Fin (2 ^ ((finrank ℝ V - 2) / 2))) ℍ[ℝ]) :=
  nonempty_algEquiv_of_realCliffordForm hQ
    (A := fun m ↦ Matrix (Fin (2 ^ ((m - 2) / 2))) (Fin (2 ^ ((m - 2) / 2))) ℍ[ℝ])
    (realClifford_classification_of_residue_eq_four 0 _
      (by rw [realCliffordResidue_def]; omega))

/-- **The classification for `dim V ≡ 5 mod 8`**: for `Q v = -‖v‖²`, the Clifford algebra of `Q`
is the complex matrix algebra of size `2 ^ ((dim V - 1) / 2)`. -/
theorem cliffordAlgebra_classification_of_finrank_mod_eight_eq_five
    (h : finrank ℝ V % 8 = 5) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((finrank ℝ V - 1) / 2))) (Fin (2 ^ ((finrank ℝ V - 1) / 2))) ℂ) :=
  nonempty_algEquiv_of_realCliffordForm hQ
    (A := fun m ↦ Matrix (Fin (2 ^ ((m - 1) / 2))) (Fin (2 ^ ((m - 1) / 2))) ℂ)
    (realClifford_classification_of_residue_eq_five 0 _
      (by rw [realCliffordResidue_def]; omega))

/-- **The classification for `dim V ≡ 6 mod 8`**: for `Q v = -‖v‖²`, the Clifford algebra of `Q`
is the real matrix algebra of size `2 ^ (dim V / 2)`. -/
theorem cliffordAlgebra_classification_of_finrank_mod_eight_eq_six
    (h : finrank ℝ V % 8 = 6) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ]
      Matrix (Fin (2 ^ (finrank ℝ V / 2))) (Fin (2 ^ (finrank ℝ V / 2))) ℝ) :=
  nonempty_algEquiv_of_realCliffordForm hQ
    (A := fun m ↦ Matrix (Fin (2 ^ (m / 2))) (Fin (2 ^ (m / 2))) ℝ)
    (realClifford_classification_of_residue_eq_six 0 _
      (by rw [realCliffordResidue_def]; omega))

/-- **The classification for `dim V ≡ 7 mod 8`**: for `Q v = -‖v‖²`, the Clifford algebra of `Q`
is the product of two real matrix algebras of size `2 ^ ((dim V - 1) / 2)`. -/
theorem cliffordAlgebra_classification_of_finrank_mod_eight_eq_seven
    (h : finrank ℝ V % 8 = 7) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((finrank ℝ V - 1) / 2))) (Fin (2 ^ ((finrank ℝ V - 1) / 2))) ℝ ×
        Matrix (Fin (2 ^ ((finrank ℝ V - 1) / 2))) (Fin (2 ^ ((finrank ℝ V - 1) / 2))) ℝ) :=
  nonempty_algEquiv_of_realCliffordForm hQ
    (A := fun m ↦ Matrix (Fin (2 ^ ((m - 1) / 2))) (Fin (2 ^ ((m - 1) / 2))) ℝ ×
      Matrix (Fin (2 ^ ((m - 1) / 2))) (Fin (2 ^ ((m - 1) / 2))) ℝ)
    (realClifford_classification_of_residue_eq_seven 0 _
      (by rw [realCliffordResidue_def]; omega))

end TauCeti

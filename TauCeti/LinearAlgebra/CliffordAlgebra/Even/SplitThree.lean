/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import TauCeti.Algebra.Quaternion.Split
public import TauCeti.RepresentationTheory.Spin.Polarization.Split.Odd
import Mathlib.Tactic.FinCases
import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Conjugation

/-!
# The even Clifford algebra of the split ternary form

Let `R` be a commutative ring and `q₃ = TauCeti.splitOddForm R 1` the split quadratic form
`((φ, x), z) ↦ φ x + z²` on `(R¹)* × R¹ × R`. Its even Clifford algebra is the matrix algebra
`M₂(R)`. No hypothesis on `2` is needed, so this holds over `ℤ`.

Write `e = ((0, 1), 0)`, `f = ((ε, 0), 0)` (with `ε` the coordinate function) and `u = ((0, 0), 1)`,
so that `e² = f² = 0`, `ef + fe = 1`, `u² = 1`, and `u` anticommutes with `e` and `f`. The
Clifford map `m ↦ !![z, x; φ 1, -z]` sends `e`, `f`, `u` to `E₁₂`, `E₂₁` and `diag(1, -1)`,
and its restriction to the even subalgebra is the equivalence. For the inverse, the elements
`i = ef` and `j = eu + fu` satisfy `i² = i`, `j² = -1` and `ij + ji = j`, so they define a map from
the quaternion algebra `ℍ[R, 0, 1, -1]`, which is split by
`TauCeti.QuaternionAlgebra.zeroOneEquivMatrix` at `c = -1`.

## Main definitions

* `TauCeti.splitOddOneToMatrix`: the Clifford map `((φ, x), z) ↦ !![z, x; φ 1, -z]`.
* `TauCeti.splitOddOneEvenEquivMatrix`: the equivalence
  `CliffordAlgebra.even (splitOddForm R 1) ≃ₐ[R] M₂(R)`.

## Main results

* `TauCeti.splitOddOneEvenEquivMatrix_ι`: the equivalence sends the even element `ι m₁ ι m₂`
  to the product of the matrices `!![z, x; φ 1, -z]` of `m₁` and `m₂`.
-/

public section

open scoped Matrix Quaternion

namespace TauCeti

open _root_.CliffordAlgebra

variable (R : Type*) [CommRing R]

/-- The matrix `!![z, x; φ 1, -z]` of a vector `((φ, x), z)` of the split ternary space. Its
square is `q₃((φ, x), z) • 1`. -/
noncomputable def splitOddOneToMatrix : SplitOddSpace R 1 →ₗ[R] Matrix (Fin 2) (Fin 2) R where
  toFun m := !![m.2, m.1.2 0; m.1.1 (fun _ ↦ 1), -m.2]
  map_add' m n := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [add_comm]
  map_smul' c m := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- The matrix of `((φ, x), z)` is `!![z, x; φ 1, -z]`. -/
@[simp]
theorem splitOddOneToMatrix_apply (m : SplitOddSpace R 1) :
    splitOddOneToMatrix R m = !![m.2, m.1.2 0; m.1.1 (fun _ ↦ 1), -m.2] :=
  (rfl)

variable {R} in
private theorem fin_one_eq_smul (y : Fin 1 → R) : y = y 0 • fun _ ↦ 1 := by
  ext i
  fin_cases i
  simp

private theorem splitOddForm_one_apply (m : SplitOddSpace R 1) :
    splitOddForm R 1 m = m.1.2 0 * m.1.1 (fun _ ↦ 1) + m.2 * m.2 := by
  rw [splitOddForm_apply, fin_one_eq_smul m.1.2, map_smul, smul_eq_mul]
  simp

/-- The matrix of a vector `m` squares to `q₃(m)` times the identity, so `splitOddOneToMatrix`
is a Clifford map. -/
theorem splitOddOneToMatrix_mul_self (m : SplitOddSpace R 1) :
    splitOddOneToMatrix R m * splitOddOneToMatrix R m =
      algebraMap R _ (splitOddForm R 1 m) := by
  rw [splitOddForm_one_apply, splitOddOneToMatrix_apply, Algebra.algebraMap_eq_smul_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The algebra map from the Clifford algebra of the split ternary form to `M₂(R)` induced by
`splitOddOneToMatrix`. -/
private noncomputable def splitOddOneCliffordToMatrix :
    CliffordAlgebra (splitOddForm R 1) →ₐ[R] Matrix (Fin 2) (Fin 2) R :=
  CliffordAlgebra.lift _ ⟨splitOddOneToMatrix R, splitOddOneToMatrix_mul_self R⟩

/-- The vector `e = ((0, 1), 0)`. -/
private noncomputable def vecE : SplitOddSpace R 1 := ((0, fun _ ↦ 1), 0)

/-- The vector `f = ((ε, 0), 0)`. -/
private noncomputable def vecF : SplitOddSpace R 1 := ((LinearMap.proj 0, 0), 0)

/-- The vector `u = ((0, 0), 1)`. -/
private noncomputable def vecU : SplitOddSpace R 1 := ((0, 0), 1)

private theorem eq_vec (m : SplitOddSpace R 1) :
    m = m.1.2 0 • vecE R + m.1.1 (fun _ ↦ 1) • vecF R + m.2 • vecU R := by
  obtain ⟨⟨φ, x⟩, z⟩ := m
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · refine LinearMap.ext fun y ↦ ?_
    simp only [vecE, vecF, vecU, Prod.fst_add, Prod.smul_fst, smul_zero, zero_add, add_zero,
      LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
    conv_lhs => rw [fin_one_eq_smul y, map_smul, smul_eq_mul]
    ring
  · ext i
    fin_cases i
    simp [vecE, vecF, vecU]
  · simp [vecE, vecF, vecU]

/-! ### Relations among the generators -/

section Relations

/-- The generator `ι e`. -/
private noncomputable def cE : CliffordAlgebra (splitOddForm R 1) := ι _ (vecE R)
/-- The generator `ι f`. -/
private noncomputable def cF : CliffordAlgebra (splitOddForm R 1) := ι _ (vecF R)
/-- The generator `ι u`. -/
private noncomputable def cU : CliffordAlgebra (splitOddForm R 1) := ι _ (vecU R)

private theorem ι_vecE : ι (splitOddForm R 1) (vecE R) = cE R := rfl
private theorem ι_vecF : ι (splitOddForm R 1) (vecF R) = cF R := rfl
private theorem ι_vecU : ι (splitOddForm R 1) (vecU R) = cU R := rfl

private theorem cE_mul_cE : cE R * cE R = 0 := by
  rw [cE, ι_sq_scalar]
  simp [vecE]

private theorem cF_mul_cF : cF R * cF R = 0 := by
  rw [cF, ι_sq_scalar]
  simp [vecF]

private theorem cU_mul_cU : cU R * cU R = 1 := by
  rw [cU, ι_sq_scalar]
  simp [vecU]

private theorem cF_mul_cE : cF R * cE R = 1 - cE R * cF R := by
  rw [cE, cF, eq_sub_iff_add_eq, add_comm, ι_mul_ι_add_swap]
  simp [vecE, vecF]

private theorem cU_mul_cE : cU R * cE R = -(cE R * cU R) := by
  rw [cE, cU, eq_neg_iff_add_eq_zero, add_comm, ι_mul_ι_add_swap]
  simp [vecE, vecU]

private theorem cU_mul_cF : cU R * cF R = -(cF R * cU R) := by
  rw [cF, cU, eq_neg_iff_add_eq_zero, add_comm, ι_mul_ι_add_swap]
  simp [vecF, vecU]

private theorem mul_cE_mul_cE (x : CliffordAlgebra (splitOddForm R 1)) :
    x * cE R * cE R = 0 := by rw [mul_assoc, cE_mul_cE, mul_zero]

private theorem mul_cF_mul_cF (x : CliffordAlgebra (splitOddForm R 1)) :
    x * cF R * cF R = 0 := by rw [mul_assoc, cF_mul_cF, mul_zero]

private theorem mul_cU_mul_cU (x : CliffordAlgebra (splitOddForm R 1)) :
    x * cU R * cU R = x := by rw [mul_assoc, cU_mul_cU, mul_one]

private theorem mul_cF_mul_cE (x : CliffordAlgebra (splitOddForm R 1)) :
    x * cF R * cE R = x - x * cE R * cF R := by
  rw [mul_assoc, cF_mul_cE, mul_sub, mul_one, mul_assoc]

private theorem mul_cU_mul_cE (x : CliffordAlgebra (splitOddForm R 1)) :
    x * cU R * cE R = -(x * cE R * cU R) := by
  rw [mul_assoc, cU_mul_cE, mul_neg, mul_assoc]

private theorem mul_cU_mul_cF (x : CliffordAlgebra (splitOddForm R 1)) :
    x * cU R * cF R = -(x * cF R * cU R) := by
  rw [mul_assoc, cU_mul_cF, mul_neg, mul_assoc]

attribute [local simp] ι_vecE ι_vecF ι_vecU cE_mul_cE cF_mul_cF cU_mul_cU cF_mul_cE
  cU_mul_cE cU_mul_cF mul_cE_mul_cE mul_cF_mul_cF mul_cU_mul_cU mul_cF_mul_cE mul_cU_mul_cE
  mul_cU_mul_cF mul_add add_mul mul_sub sub_mul
attribute [local simp ←] mul_assoc

/-- The quaternion basis `i = ef`, `j = eu + fu`, `k = eu` of the even Clifford algebra. -/
private noncomputable def splitOddOneEvenBasis :
    _root_.QuaternionAlgebra.Basis (even (splitOddForm R 1)) (0 : R) 1 (-1) where
  i := (even.ι _).bilin (vecE R) (vecF R)
  j := (even.ι _).bilin (vecE R) (vecU R) + (even.ι _).bilin (vecF R) (vecU R)
  k := (even.ι _).bilin (vecE R) (vecU R)
  i_mul_i := by
    apply Subtype.ext
    simp
  j_mul_j := by
    apply Subtype.ext
    simp
    abel
  i_mul_j := by
    apply Subtype.ext
    simp
  j_mul_i := by
    apply Subtype.ext
    simp

end Relations

private theorem splitOddOneEvenBasis_liftHom_apply (q : ℍ[R,0,1,-1]) :
    (splitOddOneEvenBasis R).liftHom q =
      algebraMap R _ q.re + q.imI • (splitOddOneEvenBasis R).i +
        q.imJ • (splitOddOneEvenBasis R).j + q.imK • (splitOddOneEvenBasis R).k := by
  rw [_root_.QuaternionAlgebra.Basis.liftHom_apply, _root_.QuaternionAlgebra.Basis.lift]

/-- The forward map: the restriction of `splitOddOneCliffordToMatrix` to the even subalgebra. -/
private noncomputable def splitOddOneEvenToMatrix :
    even (splitOddForm R 1) →ₐ[R] Matrix (Fin 2) (Fin 2) R :=
  (splitOddOneCliffordToMatrix R).comp (even (splitOddForm R 1)).val

private theorem splitOddOneEvenToMatrix_ι (m₁ m₂ : SplitOddSpace R 1) :
    splitOddOneEvenToMatrix R ((even.ι _).bilin m₁ m₂) =
      splitOddOneToMatrix R m₁ * splitOddOneToMatrix R m₂ := by
  simp [splitOddOneEvenToMatrix, splitOddOneCliffordToMatrix]

private theorem splitOddOneEvenToMatrix_comp_liftHom :
    (splitOddOneEvenToMatrix R).comp (splitOddOneEvenBasis R).liftHom =
      (QuaternionAlgebra.zeroOneEquivMatrix (-1)).toAlgHom := by
  ext : 1 <;>
    rw [AlgHom.comp_apply, splitOddOneEvenBasis_liftHom_apply,
      AlgEquiv.toAlgHom_apply, QuaternionAlgebra.zeroOneEquivMatrix_apply] <;> ext i j <;>
    fin_cases i <;> fin_cases j <;>
    simp [splitOddOneEvenBasis, splitOddOneEvenToMatrix_ι, vecE, vecF, vecU]

private theorem liftHom_comp_symm_comp_splitOddOneEvenToMatrix :
    ((splitOddOneEvenBasis R).liftHom.comp
      (QuaternionAlgebra.zeroOneEquivMatrix (-1)).symm.toAlgHom).comp
        (splitOddOneEvenToMatrix R) = AlgHom.id R _ := by
  refine even.algHom_ext (splitOddForm R 1)
    (EvenHom.ext (LinearMap.ext₂ fun m₁ m₂ ↦ Subtype.ext ?_))
  simp only [EvenHom.compr₂_bilin, LinearMap.compr₂_apply, AlgHom.toLinearMap_apply,
    AlgHom.comp_apply, AlgHom.id_apply, splitOddOneEvenToMatrix_ι,
    splitOddOneEvenBasis_liftHom_apply, AlgEquiv.toAlgHom_apply,
    QuaternionAlgebra.zeroOneEquivMatrix_symm_apply]
  conv_rhs => rw [eq_vec R m₁, eq_vec R m₂]
  simp [splitOddOneEvenBasis, Algebra.algebraMap_eq_smul_one, ι_vecE, ι_vecF, ι_vecU, cE_mul_cE,
    cF_mul_cF, cU_mul_cU, cF_mul_cE, cU_mul_cE, cU_mul_cF]
  module

/-- **The even Clifford algebra of the split ternary form is `M₂(R)`**, over any commutative
ring `R`. The equivalence is induced by the Clifford map `((φ, x), z) ↦ !![z, x; φ 1, -z]`. -/
noncomputable def splitOddOneEvenEquivMatrix :
    even (splitOddForm R 1) ≃ₐ[R] Matrix (Fin 2) (Fin 2) R :=
  AlgEquiv.ofAlgHom (splitOddOneEvenToMatrix R)
    ((splitOddOneEvenBasis R).liftHom.comp
      (QuaternionAlgebra.zeroOneEquivMatrix (-1)).symm.toAlgHom)
    (by
      rw [← AlgHom.comp_assoc, splitOddOneEvenToMatrix_comp_liftHom]
      ext : 1
      simp)
    (liftHom_comp_symm_comp_splitOddOneEvenToMatrix R)

/-- The equivalence `splitOddOneEvenEquivMatrix` sends `ι m₁ ι m₂` to the product of the
matrices of `m₁` and `m₂`. -/
@[simp]
theorem splitOddOneEvenEquivMatrix_ι (m₁ m₂ : SplitOddSpace R 1) :
    splitOddOneEvenEquivMatrix R ((even.ι _).bilin m₁ m₂) =
      splitOddOneToMatrix R m₁ * splitOddOneToMatrix R m₂ :=
  splitOddOneEvenToMatrix_ι R m₁ m₂

end TauCeti

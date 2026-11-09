/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.LinearAlgebra.Matrix.Basis
public import TauCeti.LinearAlgebra.Matrix.ToLin
public import TauCeti.Algebra.Module.LinearMap.Precomp
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Trace.Defs

/-!
# The trace of differentials along a finite free extension

Let `k → R → B` be ring maps with `B` finite free over `R`, and `D : R → M` a `k`-derivation into
an `R`-module. For `a, c ∈ B` with matrices `A, C` (multiplication by `a`, `c` in an `R`-basis of
`B`) put `δ(a)(c) = Tr(C · D(A)) = ∑ᵢⱼ Cᵢⱼ D(Aⱼᵢ)`. This does not depend on the basis, and
`a ↦ δ(a)` is a `k`-derivation of `B` into `Hom_R(B, M)`, where `B` acts on `Hom_R(B, M)` by
precomposition with multiplication. By the universal property of Kähler differentials it gives a
`B`-linear map `Ω_{B/k} → Hom_R(B, M)`, and evaluating at `1` the *trace of differentials*
`Ω_{B/k} → M`, `c da ↦ Tr(C · D(A))`. For `D = d : R → Ω_{R/k}` this is the classical trace map
`Ω_{B/k} → Ω_{R/k}`; for `a ∈ R` it is `c da ↦ Tr(c) da`.

## Main definitions

- `Matrix.traceDerivForm D X Y = ∑ᵢⱼ Xᵢⱼ • D Yⱼᵢ`.
- `Algebra.traceDerivOfBasis D b a c`: `traceDerivForm D (leftMulMatrix b c) (leftMulMatrix b a)`.
- `Algebra.traceDeriv D a c`: the same for the chosen basis of `B`.
- `Algebra.traceDerivation D`: the derivation `B → Hom_R(B, M)`.
- `KaehlerDifferential.traceLin D`: the trace of differentials `Ω_{B/k} →ₗ[R] M`.

## Main statements

- `Algebra.traceDerivOfBasis_eq`: independence of the basis.
- `KaehlerDifferential.traceLin_smul_D`: `traceLin D (c • D a) = traceDeriv D a c`.

## Source

Adapted from `Jacobian/RingTheory/Kaehler/Trace.lean` in the Jacobian library,
accepted release `baef7723da528551b7d2f93bd9a9a53303b04dbc`.
-/

public section

open Matrix

namespace Matrix

variable {k R M : Type*} [CommRing k] [CommRing R] [Algebra k R] [AddCommGroup M] [Module R M]
  [Module k M] (D : Derivation k R M)

/-- The `M`-valued form `(X, Y) ↦ Tr(X · D(Y)) = ∑ᵢⱼ Xᵢⱼ • D(Yⱼᵢ)` on pairs of matrices. -/
def traceDerivForm {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n R) (Y : Matrix n m R) :
    M :=
  ∑ i, ∑ j, X i j • D (Y j i)

/-- The defining matrix-entry formula for the trace derivation form. -/
lemma traceDerivForm_def {m n : Type*} [Fintype m] [Fintype n]
    (X : Matrix m n R) (Y : Matrix n m R) :
    traceDerivForm D X Y = ∑ i, ∑ j, X i j • D (Y j i) := (rfl)


variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

lemma traceDerivForm_add_left (X X' : Matrix m n R) (Y : Matrix n m R) :
    traceDerivForm D (X + X') Y = traceDerivForm D X Y + traceDerivForm D X' Y := by
  simp only [traceDerivForm, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

lemma traceDerivForm_add_right (X : Matrix m n R) (Y Y' : Matrix n m R) :
    traceDerivForm D X (Y + Y') = traceDerivForm D X Y + traceDerivForm D X Y' := by
  simp only [traceDerivForm, Matrix.add_apply, map_add, smul_add, Finset.sum_add_distrib]

lemma traceDerivForm_smul_left (r : R) (X : Matrix m n R) (Y : Matrix n m R) :
    traceDerivForm D (r • X) Y = r • traceDerivForm D X Y := by
  simp only [traceDerivForm, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

@[simp]
lemma traceDerivForm_zero_left (Y : Matrix n m R) :
    traceDerivForm D (0 : Matrix m n R) Y = 0 := by
  simp [traceDerivForm]

@[simp]
lemma traceDerivForm_zero_right (X : Matrix m n R) :
    traceDerivForm D X (0 : Matrix n m R) = 0 := by
  simp [traceDerivForm]

/-- **Leibniz rule** for `traceDerivForm`:
`Tr(X D(YZ)) = Tr(XY D(Z)) + Tr(ZX D(Y))`. -/
lemma traceDerivForm_mul_right (X : Matrix m n R) (Y : Matrix n p R) (Z : Matrix p m R) :
    traceDerivForm D X (Y * Z) = traceDerivForm D (X * Y) Z + traceDerivForm D (Z * X) Y := by
  simp only [traceDerivForm, Matrix.mul_apply, map_sum, Derivation.leibniz, smul_add,
    Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_smul, smul_smul]
  congr 1
  · exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
  · calc _ = ∑ i, ∑ l, ∑ j, (X i j * Z l i) • D (Y j l) :=
          Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
      _ = ∑ l, ∑ i, ∑ j, (X i j * Z l i) • D (Y j l) := Finset.sum_comm
      _ = ∑ l, ∑ j, ∑ i, (X i j * Z l i) • D (Y j l) :=
          Finset.sum_congr rfl fun l _ ↦ Finset.sum_comm
      _ = _ := by simp only [mul_comm (X _ _)]

@[simp]
lemma traceDerivForm_one_right [DecidableEq m] (X : Matrix m m R) :
    traceDerivForm D X (1 : Matrix m m R) = 0 := by
  simp only [traceDerivForm, Matrix.one_apply]
  refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ ?_
  split_ifs <;> simp

/-- `Tr(X · D(c · 1)) = Tr(X) • D(c)`. -/
lemma traceDerivForm_scalar_right [DecidableEq m] (X : Matrix m m R) (c : R) :
    traceDerivForm D X (Matrix.scalar m c) = X.trace • D c := by
  simp only [traceDerivForm, scalar_apply, diagonal_apply, Matrix.trace, diag, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_eq_single i (fun j _ hj ↦ by rw [ite_eq_right hj, D.map_zero, smul_zero])
    (fun h ↦ (h (Finset.mem_univ _)).elim), ite_eq_left rfl]

/-- Conjugation invariance of `traceDerivForm` on commuting matrices: if `P Q = 1` and
`A C = C A`, then `Tr(QCP · D(QAP)) = Tr(C · D(A))`. -/
lemma traceDerivForm_conj [DecidableEq m] (P : Matrix m n R) (Q : Matrix n m R)
    (hPQ : P * Q = 1) (A C : Matrix m m R) (hAC : A * C = C * A) :
    traceDerivForm D (Q * C * P) (Q * A * P) = traceDerivForm D C A := by
  classical
  have h₁ := traceDerivForm_mul_right D (Q * C * P) Q (A * P)
  have h₂ := traceDerivForm_mul_right D (Q * C) A P
  have h₃ := traceDerivForm_mul_right D (A * C) P Q
  rw [hPQ, traceDerivForm_one_right] at h₃
  rw [Matrix.mul_assoc Q A P, h₁]
  have e₁ : Q * C * P * Q = Q * C := by
    simp [Matrix.mul_assoc, hPQ]
  have e₂ : A * P * (Q * C * P) = A * C * P := by
    simp [← Matrix.mul_assoc, Matrix.mul_assoc A P Q, hPQ]
  have e₃ : P * (Q * C) = C := by
    simp [← Matrix.mul_assoc, hPQ]
  have e₄ : Q * C * A = Q * (A * C) := by
    simp [Matrix.mul_assoc, ← hAC]
  rw [e₁, e₂, h₂, e₃, e₄]
  have h₃' : traceDerivForm D (A * C * P) Q = -traceDerivForm D (Q * (A * C)) P :=
    eq_neg_of_add_eq_zero_left h₃.symm
  rw [h₃']
  abel

end Matrix

namespace Algebra

variable {k R B M : Type*} [CommRing k] [CommRing R] [CommRing B] [Algebra k R] [Algebra R B]
  [AddCommGroup M] [Module R M] [Module k M] (D : Derivation k R M)

/-- `Tr(C · D(A))` for the matrices `A`, `C` of multiplication by `a`, `c` in the basis `b`. -/
noncomputable def traceDerivOfBasis {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R B)
    (a c : B) : M :=
  traceDerivForm D (leftMulMatrix b c) (leftMulMatrix b a)

/-- The formula for the trace derivation in a specified basis. -/
lemma traceDerivOfBasis_def {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R B) (a c : B) :
    traceDerivOfBasis D b a c = traceDerivForm D (leftMulMatrix b c) (leftMulMatrix b a) := (rfl)

/-- `traceDerivOfBasis` does not depend on the basis. -/
lemma traceDerivOfBasis_eq {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (b : Module.Basis ι R B) (b' : Module.Basis ι' R B) (a c : B) :
    traceDerivOfBasis D b a c = traceDerivOfBasis D b' a c := by
  have hconj (x : B) : leftMulMatrix b' x = b'.toMatrix b * leftMulMatrix b x * b.toMatrix b' :=
    (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b' b b' b _).symm
  rw [traceDerivOfBasis, traceDerivOfBasis, hconj, hconj]
  exact (traceDerivForm_conj D (b.toMatrix b') (b'.toMatrix b)
    (b.toMatrix_mul_toMatrix_flip b') _ _
    (by rw [← map_mul, ← map_mul, mul_comm])).symm

variable [Module.Free R B] [Module.Finite R B]

/-- `Tr(C · D(A))` for the matrices `A`, `C` of multiplication by `a`, `c` in any basis of the
finite free `R`-algebra `B` (`traceDerivOfBasis_eq`). -/
noncomputable def traceDeriv (a c : B) : M :=
  traceDerivOfBasis D (Module.Free.chooseBasis R B) a c

/-- The chosen-basis formula for the basis-independent trace derivation. -/
lemma traceDeriv_def (a c : B) : traceDeriv D a c =
    traceDerivOfBasis D (Module.Free.chooseBasis R B) a c := (rfl)

lemma traceDeriv_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R B) (a c : B) :
    traceDeriv D a c = traceDerivOfBasis D b a c :=
  traceDerivOfBasis_eq D _ b a c

lemma traceDeriv_add_left (a a' c : B) :
    traceDeriv D (a + a') c = traceDeriv D a c + traceDeriv D a' c := by
  simp only [traceDeriv, traceDerivOfBasis, map_add, traceDerivForm_add_right]

lemma traceDeriv_add_right (a c c' : B) :
    traceDeriv D a (c + c') = traceDeriv D a c + traceDeriv D a c' := by
  simp only [traceDeriv, traceDerivOfBasis, map_add, traceDerivForm_add_left]

lemma traceDeriv_smul_right (a : B) (r : R) (c : B) :
    traceDeriv D a (r • c) = r • traceDeriv D a c := by
  simp only [traceDeriv, traceDerivOfBasis, map_smul, traceDerivForm_smul_left]

/-- **Leibniz rule**: `δ(ab)(c) = δ(b)(ca) + δ(a)(bc)`. -/
lemma traceDeriv_mul (a b c : B) :
    traceDeriv D (a * b) c = traceDeriv D b (c * a) + traceDeriv D a (b * c) := by
  simp only [traceDeriv, traceDerivOfBasis, map_mul, traceDerivForm_mul_right]

/-- `δ(r)(c) = Tr(c) • D(r)` for `r ∈ R`. -/
lemma traceDeriv_algebraMap (r : R) (c : B) :
    traceDeriv D (algebraMap R B r) c = trace R B c • D r := by
  classical
  rw [traceDeriv_def, traceDerivOfBasis_def, leftMulMatrix_algebraMap,
    traceDerivForm_scalar_right, trace_eq_matrix_trace (Module.Free.chooseBasis R B)]

end Algebra

namespace Algebra

variable {k R B M : Type*} [CommRing k] [CommRing R] [CommRing B] [Algebra k R] [Algebra R B]
  [AddCommGroup M] [Module R M] [Module k M] [Algebra k B] [IsScalarTower k R B]
  [IsScalarTower k R M] (D : Derivation k R M) [Module.Free R B] [Module.Finite R B]

/-- `traceDeriv D (x • a) c = x • traceDeriv D a c` for `x ∈ k`. -/
lemma traceDeriv_smul_left (x : k) (a c : B) :
    traceDeriv D (x • a) c = x • traceDeriv D a c := by
  rw [traceDeriv, traceDeriv, traceDerivOfBasis, traceDerivOfBasis,
    ← algebraMap_smul R x a, map_smul]
  simp only [traceDerivForm, Matrix.smul_apply, algebraMap_smul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
    rw [D.map_smul, smul_comm]

/-- The trace derivation `a ↦ (c ↦ Tr(C · D(A)))` of `B` into `Hom_R(B, M)`. -/
noncomputable def traceDerivation : Derivation k B (PrecompLinearMap R B M) :=
  Derivation.mk'
    { toFun a := PrecompLinearMap.ofLinearMap
        { toFun := traceDeriv D a
          map_add' := traceDeriv_add_right D a
          map_smul' := traceDeriv_smul_right D a }
      map_add' a a' := PrecompLinearMap.ext fun c ↦ by
        simpa only [PrecompLinearMap.add_apply, PrecompLinearMap.ofLinearMap_apply,
          LinearMap.coe_mk, AddHom.coe_mk] using traceDeriv_add_left D a a' c
      map_smul' x a := PrecompLinearMap.ext fun c ↦ by
        simp only [PrecompLinearMap.smul_apply, PrecompLinearMap.ofLinearMap_apply,
          LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply]
        rw [traceDeriv_smul_left, ← algebraMap_smul R x c, traceDeriv_smul_right,
          algebraMap_smul] }
    fun a b ↦ PrecompLinearMap.ext fun c ↦ by
      simp only [PrecompLinearMap.add_apply, PrecompLinearMap.smul_apply,
        PrecompLinearMap.ofLinearMap_apply, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
      rw [traceDeriv_mul, mul_comm c a]

@[simp]
lemma traceDerivation_apply (a c : B) : traceDerivation (B := B) D a c = traceDeriv D a c := by
  simp [traceDerivation, Derivation.mk', PrecompLinearMap.ofLinearMap_apply]

end Algebra

namespace KaehlerDifferential

open Algebra

variable {k R B M : Type*} [CommRing k] [CommRing R] [CommRing B] [Algebra k R] [Algebra R B]
  [AddCommGroup M] [Module R M] [Module k M] [Algebra k B] [IsScalarTower k R B]
  [IsScalarTower k R M] (D : Derivation k R M) [Module.Free R B] [Module.Finite R B]

/-- The **trace of differentials** `Ω_{B/k} → M`, `c da ↦ Tr(C · D(A))`, for `B` finite free
over `R` and a `k`-derivation `D : R → M`. -/
noncomputable def traceLin : Ω[B⁄k] →ₗ[R] M :=
  PrecompLinearMap.eval 1 ∘ₗ
    ((traceDerivation (B := B) D).liftKaehlerDifferential).restrictScalars R

/-- The trace is evaluation of the lifted derivation at the unit. -/
lemma traceLin_apply (ω : Ω[B⁄k]) :
    traceLin D ω = (traceDerivation (B := B) D).liftKaehlerDifferential ω 1 := by
  simp only [traceLin, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    PrecompLinearMap.eval_apply]

lemma traceLin_smul (ω : Ω[B⁄k]) (c : B) :
    traceLin D (c • ω) = (traceDerivation (B := B) D).liftKaehlerDifferential ω c := by
  rw [traceLin_apply, LinearMap.map_smul, PrecompLinearMap.smul_apply, smul_eq_mul, mul_one]

/-- `traceLin D (c • da) = Tr(C · D(A))`. -/
@[simp]
lemma traceLin_smul_D (a c : B) :
    traceLin D (c • KaehlerDifferential.D k B a) = traceDeriv D a c := by
  rw [traceLin_smul, Derivation.liftKaehlerDifferential_comp_D, traceDerivation_apply]

@[simp]
lemma traceLin_D (a : B) : traceLin D (KaehlerDifferential.D k B a) = traceDeriv D a 1 := by
  rw [← traceLin_smul_D, one_smul]

end KaehlerDifferential

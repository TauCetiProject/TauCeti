/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.HochschildCohomology.Complex
public import TauCeti.RingTheory.CyclicCohomology.Matrix
import Mathlib.Data.Matrix.Basis
import TauCeti.Data.Fin.Tuple.Basic

/-!
# Matrix Morita invariance of Hochschild cohomology

Let `A` be an algebra over a commutative ring `R`, `M` an `R`-module and `ι` a nonempty finite
index type. In Connes' multilinear cochain model (`TauCeti.hochschildCochainComplex`), a degree-`n`
cochain takes `n + 1` arguments and computes, when `A` is unital, the Hochschild cohomology
`HHⁿ(A, Hom_R(A, M))` with coefficients in the dual bimodule `Hom_R(A, M)`.

The generalized matrix trace `φ ↦ φ#Tr` (`TauCeti.matrixCochainExtension`) commutes with the
Hochschild coboundary (`TauCeti.matrixCochainExtension_hochschildCoboundary`) and therefore induces
a linear map `TauCeti.hochschildCohomology.matrixExtension` from `HHⁿ(A, Hom_R(A, M))` to
`HHⁿ(M_ι(A), Hom_R(M_ι(A), M))`. In the opposite direction, for any diagonal corner `r : ι`, the
nonunital algebra homomorphism `a ↦ Matrix.single r r a` pulls Hochschild cochains of `M_ι(A)` back
to `A` (`TauCeti.matrixCornerCochainRestriction`). Corner restriction is already a left inverse to
`φ ↦ φ#Tr` at the cochain level (`TauCeti.matrixCornerCochainRestriction_matrixCochainExtension`).

When `A` is unital, the matrix units `e_{ir} = Matrix.single i r 1` and
`e_{ri} = Matrix.single r i 1` furnish an explicit presimplicial chain homotopy
`TauCeti.matrixHochschildHomotopy` between the identity on Hochschild cochains of `M_ι(A)` and
corner restriction followed by `φ ↦ φ#Tr`: for `0 ≤ k ≤ n`, the `k`-th homotopy operator inserts
`e_{r, p_k}` in position `k + 1` and sandwiches the preceding entries between `e_{r, p_{m-1}}` and
`e_{p_m, r}`, summing over paths `p : Fin (k + 1) → ι`. On the bar coboundary `b'` this contracts
the identity, while the cyclic last coface produces `(ψ|_r)#Tr`. Consequently, matrix extension and
corner restriction are mutually inverse linear equivalences on Hochschild cohomology in every
degree over every commutative ring `R`, and the inverse is independent of the chosen corner `r`.

## Main definitions

* `TauCeti.matrixCornerCochainRestriction`: restriction of multilinear cochains on `Matrix ι ι A`
  to the `(r, r)` diagonal corner.
* `TauCeti.matrixHochschildHomotopy`: the chain homotopy between `id` and
  `matrixCochainExtension ∘ matrixCornerCochainRestriction` on Hochschild cochains of
  `Matrix ι ι A`.
* `TauCeti.hochschildCohomology.matrixExtension`: the map on Hochschild cohomology induced by
  `φ ↦ φ#Tr`.
* `TauCeti.hochschildCohomology.cornerRestriction`: the map on Hochschild cohomology induced by
  restriction to a diagonal corner.
* `TauCeti.hochschildCohomology.matrixExtensionEquiv`: the linear equivalence
  `HHⁿ(A, Hom_R(A, M)) ≃ₗ[R] HHⁿ(M_ι(A), Hom_R(M_ι(A), M))`.

## Main results

* `TauCeti.matrixCornerCochainRestriction_hochschildCoboundary`: corner restriction commutes with
  the Hochschild coboundary.
* `TauCeti.matrixHochschildHomotopy_hochschildCoboundary_zero`,
  `TauCeti.hochschildCoboundary_matrixHochschildHomotopy_add`: the chain homotopy identity
  `b (H ψ) + H (b ψ) = ψ - (ψ|_r)#Tr`.
* `TauCeti.hochschildCohomology.bijective_matrixExtension`: matrix Morita invariance of Hochschild
  cohomology over any commutative ring.
* `TauCeti.hochschildCohomology.cornerRestriction_eq_cornerRestriction`: corner restriction on
  Hochschild cohomology does not depend on the choice of corner.

## References

* A. Connes, *Non-commutative differential geometry*, Publ. Math. IHÉS 62 (1985), Part II,
  Corollary 24.
* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §§1.2.4, 2.2.
-/

public section

noncomputable section

open scoped BigOperators

namespace TauCeti

/-! ### Diagonal corner restriction of cochains -/

section Corner

section Linear

variable {R A M ι : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
  [AddCommMonoid M] [Module R M] [SMulCommClass R R M] [DecidableEq ι]

/-- Restrict a degree-`n` cochain on `Matrix ι ι A` to the `(r, r)` diagonal corner by evaluating
on single-entry matrices `Matrix.single r r (x j)`. -/
def matrixCornerCochainRestriction (r : ι) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M where
  toFun ψ := ψ.compLinearMap fun _ ↦ Matrix.singleLinearMap R r r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Pointwise formula for `matrixCornerCochainRestriction`. -/
@[simp]
theorem matrixCornerCochainRestriction_apply (r : ι) (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M)
    (x : Fin (n + 1) → A) :
    matrixCornerCochainRestriction r n ψ x = ψ (fun j ↦ Matrix.single r r (x j)) :=
  (rfl)

/-- Restriction to any diagonal corner is a left inverse to `matrixCochainExtension`. -/
@[simp]
theorem matrixCornerCochainRestriction_matrixCochainExtension [Fintype ι] (r : ι) (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    matrixCornerCochainRestriction r n (matrixCochainExtension ι n φ) = φ := by
  ext x
  exact matrixCochainExtension_single ι r n φ x

/-- As linear maps, corner restriction composed with matrix extension is the identity. -/
@[simp]
theorem matrixCornerCochainRestriction_comp_matrixCochainExtension [Fintype ι] (r : ι) (n : ℕ) :
    matrixCornerCochainRestriction (R := R) (A := A) (M := M) r n ∘ₗ
      matrixCochainExtension ι n = LinearMap.id :=
  LinearMap.ext (matrixCornerCochainRestriction_matrixCochainExtension r n)

end Linear

section Algebra

variable {R A M ι : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] [DecidableEq ι]

/-- Corner restriction commutes with every Hochschild coface. -/
theorem matrixCornerCochainRestriction_hochschildCoface [Fintype ι] (r : ι) (n : ℕ)
    (i : Fin (n + 2))
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M) :
    matrixCornerCochainRestriction r (n + 1) (hochschildCoface R (Matrix ι ι A) M i ψ) =
      hochschildCoface R A M i (matrixCornerCochainRestriction r n ψ) := by
  let f : A →ₙₐ[R] Matrix ι ι A :=
    { Matrix.singleLinearMap R r r with
      map_mul' x y := (Matrix.single_mul_single_same x r r r y).symm
      map_zero' := Matrix.single_zero r r }
  ext x
  simp only [matrixCornerCochainRestriction_apply, hochschildCoface_apply]
  exact congrArg ψ (comp_hochschildFace f i x).symm

/-- Corner restriction commutes with the Hochschild coboundary. -/
theorem matrixCornerCochainRestriction_hochschildCoboundary [Fintype ι] (r : ι) (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M) :
    matrixCornerCochainRestriction r (n + 1) (hochschildCoboundary R (Matrix ι ι A) M n ψ) =
      hochschildCoboundary R A M n (matrixCornerCochainRestriction r n ψ) := by
  ext x
  simp only [matrixCornerCochainRestriction_apply, hochschildCoboundary_apply]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg ((-1 : ℤ) ^ (i : ℕ) • ·) ?_
  simpa only [matrixCornerCochainRestriction_apply, hochschildCoface_apply] using
    DFunLike.congr_fun (matrixCornerCochainRestriction_hochschildCoface r n i ψ) x

end Algebra

end Corner

/-! ### Presimplicial chain homotopy on matrix Hochschild cochains -/

section Homotopy

variable {R A M ι : Type*} [Semiring R] [Semiring A] [Module R A]
  [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

/-- Summing `(x * e_{ur}) * (e_{ru} * y)` in slot `i` of a multilinear cochain `ψ` on `M_ι(A)`
contracts to `x * y`. -/
private theorem sum_map_update_mul_single_mul_single_mul (r : ι) {m : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin m ↦ Matrix ι ι A) M)
    (b : Fin m → Matrix ι ι A) (i : Fin m) (x y : Matrix ι ι A) :
    ∑ u : ι, ψ (Function.update b i ((x * Matrix.single u r 1) * (Matrix.single r u 1 * y))) =
      ψ (Function.update b i (x * y)) := by
  rw [← ψ.map_update_sum]
  refine congrArg ψ (congrArg (Function.update b i) ?_)
  calc
    ∑ u : ι, (x * Matrix.single u r 1) * (Matrix.single r u 1 * y)
      = ∑ u : ι, x * Matrix.single u u 1 * y := Finset.sum_congr rfl fun u _ ↦ by
          rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.single u r (1 : A)),
            Matrix.single_mul_single_same, mul_one, Matrix.mul_assoc]
    _ = x * (∑ u : ι, Matrix.single u u 1) * y := by rw [Finset.mul_sum, Finset.sum_mul]
    _ = x * y := by rw [Matrix.sum_single_one, mul_one]

/-- Right-unit specialization of `sum_map_update_mul_single_mul_single_mul`. -/
private theorem sum_map_update_mul_single_mul_single (r : ι) {m : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin m ↦ Matrix ι ι A) M)
    (b : Fin m → Matrix ι ι A) (i : Fin m) (x : Matrix ι ι A) :
    ∑ u : ι, ψ (Function.update b i ((x * Matrix.single u r 1) * Matrix.single r u 1)) =
      ψ (Function.update b i x) := by
  simpa only [mul_one] using sum_map_update_mul_single_mul_single_mul r ψ b i x 1

variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- Linear map applied to the `j`-th matrix argument in the `k`-th homotopy operator along path
`p : Fin (k + 1) → ι`: right-multiplication by `e_{p_0, r}` at `j = 0`, two-sided sandwiching
`y ↦ e_{r, p_{j-1}} * y * e_{p_j, r}` for `1 ≤ j ≤ k`, and the identity for `j > k`. -/
private def homotopyArgLinearMap (r : ι) {n : ℕ} (k : Fin (n + 1)) (p : Fin (k + 1) → ι)
    (j : Fin (n + 1)) : Matrix ι ι A →ₗ[R] Matrix ι ι A :=
  if _ : (j : ℕ) = 0 then
    LinearMap.mulRight R (Matrix.single (p 0) r 1)
  else if hjk : (j : ℕ) ≤ k then
    LinearMap.mulRight R (Matrix.single (p ⟨j, Nat.lt_succ_of_le hjk⟩) r 1) ∘ₗ
      LinearMap.mulLeft R (Matrix.single r (p ⟨(j : ℕ) - 1, by omega⟩) 1)
  else
    LinearMap.id

/-- The `(n + 2)`-tuple of matrices fed to a degree-`(n + 1)` cochain by the `k`-th homotopy
operator along path `p : Fin (k + 1) → ι`, obtained by inserting `e_{r, p_k}` at slot `k + 1`. -/
private def homotopyTuple (r : ι) {n : ℕ} (k : Fin (n + 1)) (p : Fin (k + 1) → ι)
    (a : Fin (n + 1) → Matrix ι ι A) : Fin (n + 2) → Matrix ι ι A :=
  k.succ.insertNth (Matrix.single r (p (Fin.last k)) 1) fun j ↦
    homotopyArgLinearMap (R := R) r k p j (a j)

/-- Entry `0` of `homotopyTuple` is `a 0 * e_{p_0, r}`. -/
private theorem homotopyTuple_zero (r : ι) {n : ℕ} (k : Fin (n + 1)) (p : Fin (k + 1) → ι)
    (a : Fin (n + 1) → Matrix ι ι A) :
    homotopyTuple (R := R) r k p a 0 = a 0 * Matrix.single (p 0) r 1 := by
  conv_lhs =>
    rw [homotopyTuple, ← Fin.succAbove_castPred_of_lt k.succ 0 (Fin.succ_pos k),
      Fin.insertNth_apply_succAbove]
  simp [homotopyArgLinearMap]

/-- Entry `m` (`1 ≤ m ≤ k`) of `homotopyTuple` is `e_{r, p_{m-1}} * a m * e_{p_m, r}`. -/
private theorem homotopyTuple_of_pos_of_le (r : ι) {n : ℕ} (k : Fin (n + 1))
    (p : Fin (k + 1) → ι) (a : Fin (n + 1) → Matrix ι ι A) {m : Fin (n + 2)}
    (hm0 : 0 < (m : ℕ)) (hmk : (m : ℕ) ≤ k) :
    homotopyTuple (R := R) r k p a m =
      Matrix.single r (p ⟨(m : ℕ) - 1, by omega⟩) 1 * a ⟨m, by omega⟩ *
        Matrix.single (p ⟨m, by omega⟩) r 1 := by
  have hlt : m < k.succ := Fin.lt_def.2 (Nat.lt_succ_of_le hmk)
  conv_lhs =>
    rw [homotopyTuple, ← Fin.succAbove_castPred_of_lt k.succ m hlt, Fin.insertNth_apply_succAbove]
  set m' := m.castPred (Fin.ne_last_of_lt hlt)
  have hm'_val : (m' : ℕ) = m := rfl
  have hm_ne : ¬ (m' : ℕ) = 0 := hm'_val.symm ▸ hm0.ne'
  have hm_le : (m' : ℕ) ≤ k := hm'_val.symm ▸ hmk
  simp only [homotopyArgLinearMap, hm_ne, ↓reduceDIte, hm_le, LinearMap.comp_apply,
    LinearMap.mulRight_apply, LinearMap.mulLeft_apply]
  rfl

/-- Entry `k + 1` of `homotopyTuple` is the inserted matrix unit `e_{r, p_k}`. -/
private theorem homotopyTuple_succ (r : ι) {n : ℕ} (k : Fin (n + 1)) (p : Fin (k + 1) → ι)
    (a : Fin (n + 1) → Matrix ι ι A) :
    homotopyTuple (R := R) r k p a k.succ = Matrix.single r (p (Fin.last k)) 1 :=
  Fin.insertNth_apply_same _ _ _

/-- Entry `m > k + 1` of `homotopyTuple` is `a (m - 1)`. -/
private theorem homotopyTuple_of_gt (r : ι) {n : ℕ} (k : Fin (n + 1)) (p : Fin (k + 1) → ι)
    (a : Fin (n + 1) → Matrix ι ι A) {m : Fin (n + 2)} (hmk : (k : ℕ) + 1 < m) :
    homotopyTuple (R := R) r k p a m = a ⟨(m : ℕ) - 1, by omega⟩ := by
  have hgt : k.succ < m := Fin.lt_def.2 hmk
  conv_lhs =>
    rw [homotopyTuple, ← Fin.succAbove_pred_of_lt k.succ m hgt, Fin.insertNth_apply_succAbove]
  set m' := m.pred (Fin.ne_zero_of_lt hgt)
  have hm'_val : (m' : ℕ) = (m : ℕ) - 1 := Fin.val_pred _ _
  have hm_ne : ¬ (m' : ℕ) = 0 := by omega
  have hm_le : ¬ (m' : ℕ) ≤ k := by omega
  simp only [homotopyArgLinearMap, hm_ne, ↓reduceDIte, hm_le, LinearMap.id_apply]
  exact congrArg a (Fin.ext hm'_val)

/-- The presimplicial chain homotopy `H_n : C^{n+1}(M_ι(A); M) → C^n(M_ι(A); M)` for matrix Morita
invariance of Hochschild cohomology relative to corner `r : ι`. -/
def matrixHochschildHomotopy [SMulCommClass R R M] (r : ι) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M where
  toFun ω := ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • ∑ p : Fin (k + 1) → ι,
    (MultilinearMap.mk' (R := R) (ι := Fin (n + 1))
      (M := fun _ ↦ Matrix ι ι A) (N := M) (σ := RingHom.id R)
      (fun m ↦ ω (k.succ.insertNth (Matrix.single r (p (Fin.last k)) 1) m))
      (fun _ _ _ _ ↦ by simp) (fun _ _ _ _ ↦ by simp)).compLinearMap
        (homotopyArgLinearMap (R := R) r k p)
  map_add' ω₁ ω₂ := by
    ext a
    simp [MultilinearMap.compLinearMap_apply, Finset.sum_add_distrib]
  map_smul' c ω := by
    ext a
    simp [MultilinearMap.compLinearMap_apply, Finset.smul_sum, smul_comm _ c]

/-- Pointwise formula for `matrixHochschildHomotopy` in terms of `homotopyTuple`. -/
private theorem matrixHochschildHomotopy_apply_eq [SMulCommClass R R M] (r : ι) (n : ℕ)
    (ω : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    matrixHochschildHomotopy r n ω a =
      ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) •
        ∑ p : Fin (k + 1) → ι, ω (homotopyTuple (R := R) r k p a) := by
  simp [matrixHochschildHomotopy, MultilinearMap.compLinearMap_apply, homotopyTuple]

/-- Face `0` of the `0`-th homotopy tuple sums over `ι` to the identity cochain value `ψ a`. -/
private theorem sum_hochschildFace_zero_homotopyTuple_zero (r : ι) {n : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    ∑ p : Fin ((0 : Fin (n + 1)) + 1) → ι,
        ψ (hochschildFace 0 (homotopyTuple (R := R) r 0 p a)) = ψ a := by
  have huniq : Unique (Fin ((0 : Fin (n + 1)) + 1)) := by
    rw [Fin.val_zero]
    exact inferInstanceAs (Unique (Fin 1))
  have hlast : Fin.last ((0 : Fin (n + 1)) : ℕ) = 0 := Subsingleton.elim _ _
  have htuple (p : Fin ((0 : Fin (n + 1)) + 1) → ι) :
      hochschildFace 0 (homotopyTuple (R := R) r 0 p a) =
        Function.update a 0 ((a 0 * Matrix.single (p 0) r 1) * Matrix.single r (p 0) 1) := by
    funext m
    rw [← Fin.castSucc_zero (n := n + 1), hochschildFace_castSucc]
    cases m using Fin.cases with
    | zero =>
      rw [Function.update_self, Fin.contractNth_apply_of_eq _ _ _ _ rfl, Fin.castSucc_zero,
        homotopyTuple_zero, homotopyTuple_succ, hlast]
    | succ m =>
      rw [Function.update_of_ne (Fin.succ_ne_zero m),
        Fin.contractNth_apply_of_gt _ _ _ _ (Nat.succ_pos m),
        homotopyTuple_of_gt r 0 p a (by simp [Fin.val_succ])]
      rfl
  simp only [htuple]
  rw [← (Equiv.funUnique (Fin ((0 : Fin (n + 1)) + 1)) ι).symm.sum_comp]
  have happ (u : ι) :
      (Equiv.funUnique (Fin ((0 : Fin (n + 1)) + 1)) ι).symm u 0 = u := rfl
  simp only [happ]
  rw [sum_map_update_mul_single_mul_single r ψ a 0 (a 0), Function.update_eq_self]

/-- The cyclic last face of the top (`k = n`) homotopy tuple sums over paths in `ι` to the corner
restriction followed by `matrixCochainExtension`. -/
private theorem sum_hochschildFace_last_homotopyTuple_last [SMulCommClass R R M] (r : ι) {n : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    ∑ p : Fin ((Fin.last n : ℕ) + 1) → ι,
        ψ (hochschildFace (Fin.last (n + 1)) (homotopyTuple (R := R) r (Fin.last n) p a)) =
      matrixCochainExtension ι n (matrixCornerCochainRestriction r n ψ) a := by
  have hrot0 : (finRotate (n + 1)).symm 0 = Fin.last n :=
    (finRotate (n + 1)).symm_apply_eq.2 finRotate_last.symm
  have htuple (p : Fin (n + 1) → ι) :
      hochschildFace (Fin.last (n + 1)) (homotopyTuple (R := R) r (Fin.last n) p a) =
        fun j ↦ Matrix.single r r
          (a j ((p ∘ (finRotate (n + 1)).symm) j)
            ((p ∘ (finRotate (n + 1)).symm) (finRotate (n + 1) j))) := by
    funext j
    rw [hochschildFace_last]
    cases j using Fin.cases with
    | zero =>
      rw [Fin.cons_zero, ← Fin.succ_last, homotopyTuple_succ, homotopyTuple_zero,
        ← Matrix.mul_assoc, Matrix.single_mul_mul_single, one_mul, mul_one]
      simp [Function.comp_apply, hrot0]
    | succ l =>
      have hrot_succ : (finRotate (n + 1)).symm l.succ = l.castSucc :=
        (finRotate (n + 1)).symm_apply_eq.2 <| Fin.ext <| by
          rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last l), Fin.val_castSucc, Fin.val_succ]
      rw [Fin.cons_succ, homotopyTuple_of_pos_of_le r (Fin.last n) p a (Nat.succ_pos l)
        (Nat.succ_le_of_lt l.isLt), Matrix.single_mul_mul_single, one_mul, mul_one]
      simp only [Function.comp_apply, Equiv.symm_apply_apply, hrot_succ]
      rfl
  dsimp only [Fin.val_last]
  simp only [htuple, matrixCochainExtension_apply, matrixCornerCochainRestriction_apply]
  exact (Equiv.arrowCongr (finRotate (n + 1)) (Equiv.refl ι)).sum_comp fun q ↦
    ψ fun j ↦ Matrix.single r r (a j (q j) (q (finRotate (n + 1) j)))

/-- **Degree-zero homotopy identity:** `H_0 (b ψ) = ψ - (ψ|_r)#Tr` on `0`-cochains of `M_ι(A)`. -/
theorem matrixHochschildHomotopy_hochschildCoboundary_zero [SMulCommClass R R M] (r : ι)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 ↦ Matrix ι ι A) M) :
    matrixHochschildHomotopy r 0 (hochschildCoboundary R (Matrix ι ι A) M 0 ψ) =
      ψ - matrixCochainExtension ι 0 (matrixCornerCochainRestriction r 0 ψ) := by
  ext a
  have hpow : (-1 : ℤ) ^ ((0 : Fin 1) : ℕ) = 1 := rfl
  have hexp0 : (-1 : ℤ) ^ ((0 : Fin 2) : ℕ) = 1 := rfl
  have hexp1 : (-1 : ℤ) ^ (((0 : Fin 1).succ : Fin 2) : ℕ) = -1 := rfl
  rw [matrixHochschildHomotopy_apply_eq, Fin.sum_univ_one, hpow, one_smul]
  simp only [hochschildCoboundary_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    hexp0, hexp1, one_smul, neg_one_smul, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    sub_apply]
  rw [sum_hochschildFace_zero_homotopyTuple_zero, ← sub_eq_add_neg]
  congr 1
  exact sum_hochschildFace_last_homotopyTuple_last r ψ a

/-- Left factor at slot `i` when contracting `homotopyTuple r k'.succ` at `i ≤ k'`. -/
private def homotopyFaceLhs (r : ι) {n : ℕ} {k' i : Fin (n + 1)} (hik : (i : ℕ) ≤ k')
    (q : Fin (k' + 1) → ι) (a : Fin (n + 2) → Matrix ι ι A) : Matrix ι ι A :=
  if _ : (i : ℕ) = 0 then a 0
  else Matrix.single r (q ⟨(i : ℕ) - 1, by omega⟩) 1 * a i.castSucc

private theorem hochschildFace_lt_homotopyTuple_succ_insertNth_of_lt (r : ι) {n : ℕ}
    (k' : Fin (n + 1)) {i : Fin (n + 1)} (hik : (i : ℕ) ≤ k')
    (q : Fin (k' + 1) → ι) (u : ι) (a : Fin (n + 2) → Matrix ι ι A)
    {m : Fin (n + 2)} (hm : (m : ℕ) < i) :
    hochschildFace i.castSucc.castSucc
        (homotopyTuple (R := R) r k'.succ
          (Fin.insertNth (α := fun _ ↦ ι)
            (⟨i, Nat.lt_succ_of_lt (Nat.lt_succ_of_le hik)⟩ : Fin ((k' : ℕ) + 2)) u q) a) m =
      homotopyTuple (R := R) r k' q (hochschildFace i.castSucc a) m := by
  set i₀ : Fin ((k' : ℕ) + 2) := ⟨i, Nat.lt_succ_of_lt (Nat.lt_succ_of_le hik)⟩
  rw [hochschildFace_castSucc, Fin.contractNth_apply_of_lt _ _ _ _ hm]
  by_cases hm0 : (m : ℕ) = 0
  · obtain rfl : m = 0 := Fin.ext hm0
    have hi0 : (0 : Fin ((k' : ℕ) + 2)) < i₀ := Fin.lt_def.2 hm
    rw [Fin.castSucc_zero, homotopyTuple_zero, homotopyTuple_zero,
      ← Fin.succAbove_castPred_of_lt i₀ 0 hi0, Fin.insertNth_apply_succAbove, Fin.castPred_zero,
      hochschildFace_castSucc, Fin.contractNth_apply_of_lt _ _ _ _ hm, Fin.castSucc_zero]
  · have hm_pos : 0 < (m : ℕ) := Nat.pos_of_ne_zero hm0
    have hmk1 : (m.castSucc : ℕ) ≤ k'.succ := by simp only [Fin.val_castSucc, Fin.val_succ]; omega
    rw [homotopyTuple_of_pos_of_le (m := m.castSucc) _ _ _ _ hm_pos hmk1,
      homotopyTuple_of_pos_of_le (m := m) _ _ _ _ hm_pos (by omega), hochschildFace_castSucc,
      Fin.contractNth_apply_of_lt _ _ _ _ hm]
    have h1 : (⟨(m.castSucc : ℕ) - 1,
        by simp only [Fin.val_castSucc]; omega⟩ : Fin ((k' : ℕ) + 2)) < i₀ :=
      Fin.lt_def.2 (by simp only [Fin.val_castSucc, i₀]; omega)
    have h2 : (⟨(m.castSucc : ℕ),
        by simp only [Fin.val_castSucc]; omega⟩ : Fin ((k' : ℕ) + 2)) < i₀ := Fin.lt_def.2 hm
    rw [← Fin.succAbove_castPred_of_lt i₀ _ h1, Fin.insertNth_apply_succAbove,
      ← Fin.succAbove_castPred_of_lt i₀ _ h2, Fin.insertNth_apply_succAbove]
    rfl

private theorem hochschildFace_lt_homotopyTuple_succ_insertNth_self (r : ι) {n : ℕ}
    (k' : Fin (n + 1)) {i : Fin (n + 1)} (hik : (i : ℕ) ≤ k')
    (q : Fin (k' + 1) → ι) (u : ι) (a : Fin (n + 2) → Matrix ι ι A) :
    hochschildFace i.castSucc.castSucc
        (homotopyTuple (R := R) r k'.succ
          (Fin.insertNth (α := fun _ ↦ ι)
            (⟨i, Nat.lt_succ_of_lt (Nat.lt_succ_of_le hik)⟩ : Fin ((k' : ℕ) + 2)) u q) a)
          i.castSucc =
      (homotopyFaceLhs r hik q a * Matrix.single u r 1) *
        (Matrix.single r u 1 *
          (a i.succ * Matrix.single (q ⟨i, Nat.lt_succ_of_le hik⟩) r 1)) := by
  set i₀ : Fin ((k' : ℕ) + 2) := ⟨i, Nat.lt_succ_of_lt (Nat.lt_succ_of_le hik)⟩
  rw [hochschildFace_castSucc, Fin.contractNth_apply_of_eq _ _ _ _ rfl]
  congr 1
  · by_cases hi0 : (i : ℕ) = 0
    · obtain rfl : i = 0 := Fin.ext hi0
      have hiz : i₀ = 0 := rfl
      simp [homotopyFaceLhs, Fin.castSucc_zero, homotopyTuple_zero, hiz]
    · have hi_pos : 0 < (i.castSucc.castSucc : ℕ) := Nat.pos_of_ne_zero hi0
      have hik' : (i.castSucc.castSucc : ℕ) ≤ k'.succ := by
        simp only [Fin.val_castSucc, Fin.val_succ]; omega
      rw [homotopyTuple_of_pos_of_le _ _ _ _ hi_pos hik']
      have h1 : (⟨(i.castSucc.castSucc : ℕ) - 1,
          by simp only [Fin.val_castSucc]; omega⟩ : Fin ((k' : ℕ) + 2)) < i₀ :=
        Fin.lt_def.2 (by simp only [Fin.val_castSucc, i₀]; omega)
      have h2 : (⟨(i.castSucc.castSucc : ℕ),
          by simp only [Fin.val_castSucc]; omega⟩ : Fin ((k' : ℕ) + 2)) = i₀ :=
        Fin.ext (by simp [i₀])
      rw [h2, Fin.insertNth_apply_same, ← Fin.succAbove_castPred_of_lt i₀ _ h1,
        Fin.insertNth_apply_succAbove]
      simp only [homotopyFaceLhs, hi0, ↓reduceDIte]
      rfl
  · rw [homotopyTuple_of_pos_of_le _ _ _ _ (Nat.succ_pos i) (Nat.succ_le_succ hik),
      Matrix.mul_assoc]
    have h1 : (⟨(i.castSucc.succ : ℕ) - 1,
        by simp only [Fin.val_succ, Fin.val_castSucc]; omega⟩ : Fin ((k' : ℕ) + 2)) = i₀ :=
      Fin.ext (by simp [i₀])
    have h2 : i₀ < (⟨(i.castSucc.succ : ℕ),
        by simp only [Fin.val_succ, Fin.val_castSucc]; omega⟩ : Fin ((k' : ℕ) + 2)) :=
      Fin.lt_def.2 (Nat.lt_succ_self i)
    rw [h1, Fin.insertNth_apply_same, ← Fin.succAbove_pred_of_lt i₀ _ h2,
      Fin.insertNth_apply_succAbove]
    have ha : (⟨(i.castSucc.succ : ℕ),
        by simp only [Fin.val_succ, Fin.val_castSucc]; exact i.succ.isLt⟩ : Fin (n + 2)) = i.succ :=
      Fin.ext (by simp)
    have hq : ((⟨(i.castSucc.succ : ℕ),
        by simp only [Fin.val_succ, Fin.val_castSucc]; omega⟩ : Fin ((k' : ℕ) + 2)).pred
        (Fin.ne_zero_of_lt h2)) = ⟨i, Nat.lt_succ_of_le hik⟩ := Fin.ext (by simp)
    rw [ha, hq]

private theorem hochschildFace_lt_homotopyTuple_succ_insertNth_of_gt (r : ι) {n : ℕ}
    (k' : Fin (n + 1)) {i : Fin (n + 1)} (hik : (i : ℕ) ≤ k')
    (q : Fin (k' + 1) → ι) (u : ι) (a : Fin (n + 2) → Matrix ι ι A)
    {m : Fin (n + 2)} (hm : (i : ℕ) < m) :
    hochschildFace i.castSucc.castSucc
        (homotopyTuple (R := R) r k'.succ
          (Fin.insertNth (α := fun _ ↦ ι)
            (⟨i, Nat.lt_succ_of_lt (Nat.lt_succ_of_le hik)⟩ : Fin ((k' : ℕ) + 2)) u q) a) m =
      homotopyTuple (R := R) r k' q (hochschildFace i.castSucc a) m := by
  set i₀ : Fin ((k' : ℕ) + 2) := ⟨i, Nat.lt_succ_of_lt (Nat.lt_succ_of_le hik)⟩
  rw [hochschildFace_castSucc, Fin.contractNth_apply_of_gt _ _ _ _ hm]
  rcases lt_trichotomy (m : ℕ) ((k' : ℕ) + 1) with hmk | hmk | hmk
  · have hms_le : (m.succ : ℕ) ≤ k'.succ := by simp only [Fin.val_succ]; omega
    rw [homotopyTuple_of_pos_of_le _ _ _ _ (Nat.succ_pos m) hms_le,
      homotopyTuple_of_pos_of_le _ _ _ _ (by omega) (by omega), hochschildFace_castSucc]
    have h1 : i₀ < (⟨(m.succ : ℕ) - 1,
        by simp only [Fin.val_succ]; omega⟩ : Fin ((k' : ℕ) + 2)) := Fin.lt_def.2 hm
    have h2 : i₀ < (⟨(m.succ : ℕ),
        by simp only [Fin.val_succ]; omega⟩ : Fin ((k' : ℕ) + 2)) :=
      Fin.lt_def.2 (Nat.lt_succ_of_lt hm)
    rw [← Fin.succAbove_pred_of_lt i₀ _ h1, Fin.insertNth_apply_succAbove,
      ← Fin.succAbove_pred_of_lt i₀ _ h2, Fin.insertNth_apply_succAbove]
    have hm' : (i.castSucc : ℕ) < (⟨(m : ℕ), by omega⟩ : Fin (n + 1)) := hm
    rw [Fin.contractNth_apply_of_gt _ _ _ _ hm']
    have hq1 : ((⟨(m.succ : ℕ) - 1,
        by simp only [Fin.val_succ]; omega⟩ : Fin ((k' : ℕ) + 2)).pred
        (Fin.ne_zero_of_lt h1)) = ⟨(m : ℕ) - 1, by omega⟩ := Fin.ext (by simp)
    have ha : (⟨(m.succ : ℕ), by omega⟩ : Fin (n + 2)) =
        (⟨(m : ℕ), by omega⟩ : Fin (n + 1)).succ := Fin.ext (by simp)
    have hq2 : ((⟨(m.succ : ℕ),
        by simp only [Fin.val_succ]; omega⟩ : Fin ((k' : ℕ) + 2)).pred
        (Fin.ne_zero_of_lt h2)) = ⟨m, by omega⟩ := Fin.ext (by simp)
    rw [hq1, ha, hq2]
  · have hms : m.succ = k'.succ.succ := Fin.ext (by simp [hmk])
    have hm' : m = k'.succ := Fin.ext hmk
    have hlast : i₀ < Fin.last ((k' : ℕ) + 1) :=
      Fin.lt_def.2 (by simp only [Fin.val_last, i₀]; omega)
    rw [hms, homotopyTuple_succ, hm', homotopyTuple_succ]
    dsimp only [Fin.val_succ]
    rw [← Fin.succAbove_pred_of_lt i₀ _ hlast, Fin.insertNth_apply_succAbove]
    exact congrArg (fun idx ↦ Matrix.single r (q idx) 1) (Fin.ext (by simp))
  · have hms_gt : (k'.succ : ℕ) + 1 < m.succ := by simp only [Fin.val_succ]; omega
    have hm_gt : (i.castSucc : ℕ) < (⟨(m : ℕ) - 1, by have := m.isLt; omega⟩ : Fin (n + 1)) := by
      simp only [Fin.val_castSucc]; omega
    rw [homotopyTuple_of_gt _ _ _ _ hms_gt, homotopyTuple_of_gt _ _ _ _ hmk,
      hochschildFace_castSucc, Fin.contractNth_apply_of_gt _ _ _ _ hm_gt]
    exact congrArg a (Fin.ext (by simp; omega))

/-- Pointwise update formula for `hochschildFace i.castSucc.castSucc` applied to
`homotopyTuple r k'.succ` when `i ≤ k'`. -/
private theorem hochschildFace_lt_homotopyTuple_succ_insertNth (r : ι) {n : ℕ}
    (k' : Fin (n + 1)) {i : Fin (n + 1)} (hik : (i : ℕ) ≤ k')
    (q : Fin (k' + 1) → ι) (u : ι) (a : Fin (n + 2) → Matrix ι ι A) :
    hochschildFace i.castSucc.castSucc
        (homotopyTuple (R := R) r k'.succ
          (Fin.insertNth (α := fun _ ↦ ι)
            (⟨i, Nat.lt_succ_of_lt (Nat.lt_succ_of_le hik)⟩ : Fin ((k' : ℕ) + 2)) u q) a) =
      Function.update (homotopyTuple (R := R) r k' q (hochschildFace i.castSucc a)) i.castSucc
        ((homotopyFaceLhs r hik q a * Matrix.single u r 1) *
          (Matrix.single r u 1 *
            (a i.succ * Matrix.single (q ⟨i, Nat.lt_succ_of_le hik⟩) r 1))) := by
  funext m
  rcases lt_trichotomy (m : ℕ) i with hm | hm | hm
  · rw [Function.update_of_ne (Fin.ne_of_val_ne hm.ne)]
    exact hochschildFace_lt_homotopyTuple_succ_insertNth_of_lt r k' hik q u a hm
  · obtain rfl : m = i.castSucc := Fin.ext hm
    rw [Function.update_self]
    exact hochschildFace_lt_homotopyTuple_succ_insertNth_self r k' hik q u a
  · rw [Function.update_of_ne (Fin.ne_of_val_ne hm.ne')]
    exact hochschildFace_lt_homotopyTuple_succ_insertNth_of_gt r k' hik q u a hm

/-- Contracting adjacent entries at `i ≤ k'` in `homotopyTuple r k'.succ` and summing over the
inserted intermediate index `u` produces `homotopyTuple r k'` applied to
`hochschildFace i.castSucc a`. -/
private theorem sum_hochschildFace_lt_homotopyTuple_succ (r : ι) {n : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (k' : Fin (n + 1)) {i : Fin (n + 1)} (hik : (i : ℕ) ≤ k')
    (a : Fin (n + 2) → Matrix ι ι A) :
    ∑ p : Fin ((k'.succ : ℕ) + 1) → ι,
        ψ (hochschildFace i.castSucc.castSucc (homotopyTuple (R := R) r k'.succ p a)) =
      ∑ q : Fin ((k' : ℕ) + 1) → ι,
        ψ (homotopyTuple (R := R) r k' q (hochschildFace i.castSucc a)) := by
  let i₀ : Fin ((k' : ℕ) + 2) := ⟨i, Nat.lt_succ_of_lt (Nat.lt_succ_of_le hik)⟩
  dsimp only [Fin.val_succ]
  rw [← (Fin.insertNthEquiv (fun _ : Fin ((k' : ℕ) + 2) ↦ ι) i₀).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have hsum :
      ∑ u : ι, ψ (hochschildFace i.castSucc.castSucc
          (homotopyTuple (R := R) r k'.succ
            (Fin.insertNthEquiv (fun _ : Fin ((k' : ℕ) + 2) ↦ ι) i₀ (u, q)) a)) =
        ∑ u : ι, ψ (Function.update (homotopyTuple (R := R) r k' q (hochschildFace i.castSucc a))
          i.castSucc ((homotopyFaceLhs r hik q a * Matrix.single u r 1) *
            (Matrix.single r u 1 *
              (a i.succ * Matrix.single (q ⟨i, Nat.lt_succ_of_le hik⟩) r 1)))) :=
    Finset.sum_congr rfl fun u _ ↦
      congrArg ψ (hochschildFace_lt_homotopyTuple_succ_insertNth r k' hik q u a)
  rw [hsum, sum_map_update_mul_single_mul_single_mul]
  congr 1
  rw [Function.update_eq_self_iff]
  by_cases hi0 : (i : ℕ) = 0
  · obtain rfl : i = 0 := Fin.ext hi0
    simp only [homotopyFaceLhs, hi0, ↓reduceDIte, Fin.castSucc_zero, homotopyTuple_zero]
    rw [← Fin.castSucc_zero (n := n + 1), hochschildFace_castSucc,
      Fin.contractNth_apply_of_eq _ _ _ _ rfl, Fin.castSucc_zero, Fin.succ_zero_eq_one,
      Matrix.mul_assoc]
    rfl
  · rw [homotopyTuple_of_pos_of_le (m := i.castSucc) _ _ _ _ (Nat.pos_of_ne_zero hi0) hik]
    simp only [homotopyFaceLhs, hi0, ↓reduceDIte, hochschildFace_castSucc, Matrix.mul_assoc]
    have hidx : (⟨(i.castSucc : ℕ), i.isLt⟩ : Fin (n + 1)) = i := Fin.ext rfl
    rw [hidx, Fin.contractNth_apply_of_eq _ _ _ _ rfl, Matrix.mul_assoc]
    rfl

/-- Pointwise update formula for `hochschildFace k'.succ.castSucc` applied to
`homotopyTuple r k'.succ (Fin.snoc q u)`. -/
private theorem hochschildFace_succ_homotopyTuple_succ_snoc (r : ι) {n : ℕ}
    (k' : Fin (n + 1)) (q : Fin (k' + 1) → ι) (u : ι) (a : Fin (n + 2) → Matrix ι ι A) :
    hochschildFace k'.succ.castSucc (homotopyTuple (R := R) r k'.succ (Fin.snoc q u) a) =
      Function.update
        (hochschildFace k'.succ.castSucc (homotopyTuple (R := R) r k'.castSucc q a)) k'.succ
        (((Matrix.single r (q (Fin.last k')) 1 * a k'.succ) * Matrix.single u r 1) *
          Matrix.single r u 1) := by
  have hsnoc {c : ℕ} (hc : c < (k' : ℕ) + 1) (hc' : c < (k' : ℕ) + 2) :
      Fin.snoc (α := fun _ ↦ ι) q u ⟨c, hc'⟩ = q ⟨c, hc⟩ :=
    Fin.snoc_castSucc (α := fun _ ↦ ι) u q ⟨c, hc⟩
  funext m
  rw [hochschildFace_castSucc]
  rcases lt_trichotomy (m : ℕ) (k'.succ : ℕ) with hm | hm | hm
  · rw [Function.update_of_ne (Fin.ne_of_val_ne hm.ne), Fin.contractNth_apply_of_lt _ _ _ _ hm,
      hochschildFace_castSucc, Fin.contractNth_apply_of_lt _ _ _ _ hm]
    by_cases hm0 : (m : ℕ) = 0
    · obtain rfl : m = 0 := Fin.ext hm0
      rw [Fin.castSucc_zero, homotopyTuple_zero, homotopyTuple_zero]
      exact congrArg (fun idx ↦ a 0 * Matrix.single idx r 1)
        (Fin.snoc_castSucc (α := fun _ ↦ ι) u q 0)
    · have hm_pos : 0 < (m.castSucc : ℕ) := Nat.pos_of_ne_zero hm0
      have hle2 : (m.castSucc : ℕ) ≤ k'.castSucc := by
        simp only [Fin.val_castSucc] at hm ⊢; exact Nat.le_of_lt_succ hm
      rw [homotopyTuple_of_pos_of_le _ _ _ _ hm_pos hm.le,
        homotopyTuple_of_pos_of_le _ _ _ _ hm_pos hle2]
      simp only [Fin.val_succ] at hm
      rw [hsnoc (by simp only [Fin.val_castSucc]; omega),
        hsnoc (by simp only [Fin.val_castSucc]; omega)]
  · obtain rfl : m = k'.succ := Fin.ext hm
    have hlast_eq : (⟨(k'.succ.castSucc : ℕ),
        by simp only [Fin.val_castSucc, Fin.val_succ]; omega⟩ : Fin ((k' : ℕ) + 2)) =
        Fin.last ((k' : ℕ) + 1) := Fin.ext (by simp)
    rw [Function.update_self, Fin.contractNth_apply_of_eq _ _ _ _ rfl,
      homotopyTuple_of_pos_of_le _ _ _ _ (Nat.succ_pos k') (le_refl _), homotopyTuple_succ]
    dsimp only [Fin.val_succ]
    rw [hsnoc (by simp), hlast_eq, Fin.snoc_last (α := fun _ ↦ ι)]
    have hq : (⟨(k'.succ.castSucc : ℕ) - 1, by simp⟩ : Fin ((k' : ℕ) + 1)) = Fin.last k' :=
      Fin.ext (by simp)
    have ha : (⟨(k'.succ.castSucc : ℕ),
        by simp only [Fin.val_castSucc, Fin.val_succ]; exact k'.succ.isLt⟩ : Fin (n + 2)) =
        k'.succ := Fin.ext (by simp)
    rw [hq, ha]
  · have hgt1 : (k'.succ : ℕ) + 1 < m.succ := Nat.succ_lt_succ hm
    have hgt2 : (k'.castSucc : ℕ) + 1 < m.succ := by
      simp only [Fin.val_castSucc, Fin.val_succ]; simp only [Fin.val_succ] at hm; omega
    rw [Function.update_of_ne (Fin.ne_of_val_ne hm.ne'), Fin.contractNth_apply_of_gt _ _ _ _ hm,
      hochschildFace_castSucc, Fin.contractNth_apply_of_gt _ _ _ _ hm,
      homotopyTuple_of_gt _ _ _ _ hgt1, homotopyTuple_of_gt _ _ _ _ hgt2]

/-- Contracting at `k' + 1` in `homotopyTuple r k'.succ` and summing over the last path index
agrees with contracting at `k' + 1` in `homotopyTuple r k'.castSucc` (telescoping of `i = k` and
`i = k + 1`). -/
private theorem sum_hochschildFace_succ_homotopyTuple_succ (r : ι) {n : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (k' : Fin (n + 1)) (a : Fin (n + 2) → Matrix ι ι A) :
    ∑ p : Fin (k'.succ + 1) → ι,
        ψ (hochschildFace k'.succ.castSucc (homotopyTuple (R := R) r k'.succ p a)) =
      ∑ q : Fin (k'.castSucc + 1) → ι,
        ψ (hochschildFace k'.succ.castSucc (homotopyTuple (R := R) r k'.castSucc q a)) := by
  dsimp only [Fin.val_succ, Fin.val_castSucc]
  rw [← (Fin.snocEquiv fun _ : Fin ((k' : ℕ) + 2) ↦ ι).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk,
    hochschildFace_succ_homotopyTuple_succ_snoc r k' q _ a]
  rw [sum_map_update_mul_single_mul_single]
  congr 1
  rw [Function.update_eq_self_iff, hochschildFace_castSucc,
    Fin.contractNth_apply_of_eq _ _ _ _ rfl, ← Fin.succ_castSucc k', homotopyTuple_succ,
    homotopyTuple_of_gt _ _ _ _ (Nat.lt_succ_self _)]
  exact congrArg (Matrix.single r (q (Fin.last k')) 1 * ·) (congrArg a (Fin.ext (by simp)))

/-- Contracting above `k + 1` in `homotopyTuple r k.castSucc` commutes directly with
`homotopyTuple`. -/
private theorem hochschildFace_gt_homotopyTuple_castSucc (r : ι) {n : ℕ}
    (k : Fin (n + 1)) {j : Fin (n + 1)} (hkj : (k : ℕ) < j) (p : Fin (k + 1) → ι)
    (a : Fin (n + 2) → Matrix ι ι A) :
    hochschildFace j.succ.castSucc (homotopyTuple (R := R) r k.castSucc p a) =
      homotopyTuple (R := R) r k p (hochschildFace j.castSucc a) := by
  funext m
  have hmj_Bound := m.isLt
  rw [hochschildFace_castSucc]
  rcases lt_trichotomy (m : ℕ) (j.succ : ℕ) with hm | hm | hm
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ hm]
    by_cases hm0 : (m : ℕ) = 0
    · obtain rfl : m = 0 := Fin.ext hm0
      rw [Fin.castSucc_zero, homotopyTuple_zero, homotopyTuple_zero, hochschildFace_castSucc,
        Fin.contractNth_apply_of_lt _ _ _ _ (Nat.zero_lt_of_lt hkj), Fin.castSucc_zero]
    · rcases lt_trichotomy (m : ℕ) ((k : ℕ) + 1) with hmk | hmk | hmk
      · have hle : (m : ℕ) ≤ k := Nat.le_of_lt_succ hmk
        have hle_cs : (m.castSucc : ℕ) ≤ k.castSucc := hle
        have hmlt : ((⟨(m : ℕ), by omega⟩ : Fin (n + 1)) : ℕ) < (j.castSucc : ℕ) :=
          lt_of_le_of_lt hle hkj
        rw [homotopyTuple_of_pos_of_le (m := m.castSucc) _ _ _ _ (Nat.pos_of_ne_zero hm0) hle_cs,
          homotopyTuple_of_pos_of_le (m := m) _ _ _ _ (Nat.pos_of_ne_zero hm0) hle,
          hochschildFace_castSucc, Fin.contractNth_apply_of_lt _ _ _ _ hmlt]
        rfl
      · have hmc : m.castSucc = k.castSucc.succ := Fin.ext hmk
        have hms : m = k.succ := Fin.ext hmk
        rw [hmc, homotopyTuple_succ, hms, homotopyTuple_succ]
        rfl
      · have hlt2 : ((⟨(m : ℕ) - 1, by omega⟩ : Fin (n + 1)) : ℕ) < (j.castSucc : ℕ) := by
          simp only [Fin.val_castSucc]; simp only [Fin.val_succ] at hm; omega
        have hmk_cs : (k.castSucc : ℕ) + 1 < m.castSucc := hmk
        rw [homotopyTuple_of_gt (m := m.castSucc) _ _ _ _ hmk_cs,
          homotopyTuple_of_gt (m := m) _ _ _ _ hmk,
          hochschildFace_castSucc, Fin.contractNth_apply_of_lt _ _ _ _ hlt2]
        rfl
  · obtain rfl : m = j.succ := Fin.ext hm
    have hgt : (k.castSucc : ℕ) + 1 < j.succ.castSucc := Nat.succ_lt_succ hkj
    rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl,
      homotopyTuple_of_gt _ _ _ _ hgt, homotopyTuple_of_gt _ _ _ _ (Nat.lt_succ_of_lt hgt),
      homotopyTuple_of_gt _ _ _ _ (Nat.succ_lt_succ hkj), hochschildFace_castSucc]
    have hidx : (⟨(j.succ : ℕ) - 1, by omega⟩ : Fin (n + 1)) = j := Fin.ext (by simp)
    rw [hidx, Fin.contractNth_apply_of_eq _ _ _ _ rfl]
    rfl
  · simp only [Fin.val_succ] at hm
    have hgt1 : (k.castSucc : ℕ) + 1 < m.succ := by
      simp only [Fin.val_castSucc, Fin.val_succ]; omega
    have hgt3 : (j.castSucc : ℕ) < (⟨(m : ℕ) - 1, by omega⟩ : Fin (n + 1)) := by
      simp only [Fin.val_castSucc]; omega
    rw [Fin.contractNth_apply_of_gt _ _ _ _ hm,
      homotopyTuple_of_gt _ _ _ _ hgt1, homotopyTuple_of_gt _ _ _ _ (by omega),
      hochschildFace_castSucc, Fin.contractNth_apply_of_gt _ _ _ _ hgt3]
    exact congrArg a (Fin.ext (by simp; omega))

/-- For `k < n + 1`, the cyclic last face commutes with `homotopyTuple r k.castSucc`. -/
private theorem hochschildFace_last_homotopyTuple_castSucc (r : ι) {n : ℕ}
    (k : Fin (n + 1)) (p : Fin (k + 1) → ι) (a : Fin (n + 2) → Matrix ι ι A) :
    hochschildFace (Fin.last (n + 2)) (homotopyTuple (R := R) r k.castSucc p a) =
      homotopyTuple (R := R) r k p (hochschildFace (Fin.last (n + 1)) a) := by
  funext m
  have hk_lt := k.isLt
  rw [hochschildFace_last]
  cases m using Fin.cases with
  | zero =>
    have hlast_gt : (k.castSucc : ℕ) + 1 < Fin.last (n + 2) := by
      simp only [Fin.val_castSucc, Fin.val_last]; omega
    rw [Fin.cons_zero, homotopyTuple_of_gt _ _ _ _ hlast_gt,
      homotopyTuple_zero, homotopyTuple_zero, hochschildFace_last, Fin.cons_zero,
      Matrix.mul_assoc]
    rfl
  | succ l =>
    have hl_lt := l.isLt
    rw [Fin.cons_succ]
    rcases lt_trichotomy (l : ℕ) k with hlk | hlk | hlk
    · have hle1 : (l.castSucc.succ : ℕ) ≤ k.castSucc := by
        simp only [Fin.val_succ, Fin.val_castSucc]; omega
      have hle2 : (l.succ : ℕ) ≤ k := hlk
      rw [homotopyTuple_of_pos_of_le _ _ _ _ (Nat.succ_pos _) hle1,
        homotopyTuple_of_pos_of_le _ _ _ _ (Nat.succ_pos _) hle2, hochschildFace_last]
      have hl : (⟨(l.succ : ℕ), by omega⟩ : Fin (n + 1)) = (⟨l, by omega⟩ : Fin n).succ :=
        Fin.ext rfl
      rw [hl, Fin.cons_succ]
      rfl
    · have hls : l.castSucc.succ = k.castSucc.succ := Fin.ext (by simp [hlk])
      have hl' : l.succ = k.succ := Fin.ext (by simp [hlk])
      rw [hls, homotopyTuple_succ, hl', homotopyTuple_succ]
      rfl
    · have hgt1 : (k.castSucc : ℕ) + 1 < l.castSucc.succ := Nat.succ_lt_succ hlk
      have hgt2 : (k : ℕ) + 1 < l.succ := Nat.succ_lt_succ hlk
      rw [homotopyTuple_of_gt _ _ _ _ hgt1, homotopyTuple_of_gt _ _ _ _ hgt2, hochschildFace_last]
      have hl : (⟨(l.succ : ℕ) - 1, by omega⟩ : Fin (n + 1)) =
          (⟨(l : ℕ) - 1, by omega⟩ : Fin n).succ := Fin.ext (by simp; omega)
      rw [hl, Fin.cons_succ]
      exact congrArg a (Fin.ext (by simp; omega))

/-- Summand of `H_{n+1} (b' ψ)` indexed by `(k, i) : Fin (n + 2) × Fin (n + 2)`. -/
private def homotopyGridTerm (r : ι) {n : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 2) → Matrix ι ι A) (k i : Fin (n + 2)) : M :=
  (-1 : ℤ) ^ ((k : ℕ) + i) •
    ∑ p : Fin (k + 1) → ι,
      ψ (hochschildFace i.castSucc (homotopyTuple (R := R) r k p a))

/-- Decomposition of the `(n + 2) × (n + 2)` grid sum of `homotopyGridTerm` into off-diagonal,
diagonal, and superdiagonal parts via `Fin.sum_univ_succAbove`. -/
private theorem sum_sum_homotopyGridTerm (r : ι) {n : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 2) → Matrix ι ι A) :
    (∑ k : Fin (n + 2), ∑ i : Fin (n + 2), homotopyGridTerm r ψ a k i) =
      (∑ j : Fin (n + 1), ∑ k' : Fin (n + 1),
          homotopyGridTerm r ψ a (j.castSucc.succAbove k')
            ((j.castSucc.succAbove k').succAbove j)) +
        ((∑ k : Fin (n + 2), homotopyGridTerm r ψ a k k) +
          ∑ k' : Fin (n + 1), homotopyGridTerm r ψ a k'.castSucc k'.succ) := by
  calc
    (∑ k : Fin (n + 2), ∑ i : Fin (n + 2), homotopyGridTerm r ψ a k i)
      = ∑ k : Fin (n + 2), (homotopyGridTerm r ψ a k k +
          ∑ j : Fin (n + 1), homotopyGridTerm r ψ a k (k.succAbove j)) :=
          Finset.sum_congr rfl fun k _ ↦ Fin.sum_univ_succAbove (homotopyGridTerm r ψ a k) k
    _ = (∑ k : Fin (n + 2), homotopyGridTerm r ψ a k k) +
          ∑ j : Fin (n + 1), (homotopyGridTerm r ψ a j.castSucc j.succ +
            ∑ k' : Fin (n + 1), homotopyGridTerm r ψ a (j.castSucc.succAbove k')
              ((j.castSucc.succAbove k').succAbove j)) := by
          rw [Finset.sum_add_distrib, Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [Fin.sum_univ_succAbove (fun k ↦ homotopyGridTerm r ψ a k (k.succAbove j))
            j.castSucc, Fin.succAbove_castSucc_self]
    _ = _ := by rw [Finset.sum_add_distrib]; abel

/-- Off-diagonal terms in `b' (H_n ψ) + H_{n+1} (b' ψ)` cancel pairwise. -/
private theorem sum_homotopyGrid_offDiag_eq_zero (r : ι) {n : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 2) → Matrix ι ι A) :
    (∑ j : Fin (n + 1), ∑ k' : Fin (n + 1),
        (-1 : ℤ) ^ ((j : ℕ) + k') •
          ∑ q : Fin (k' + 1) → ι,
            ψ (homotopyTuple (R := R) r k' q (hochschildFace j.castSucc a))) +
      ∑ j : Fin (n + 1), ∑ k' : Fin (n + 1),
        homotopyGridTerm r ψ a (j.castSucc.succAbove k')
          ((j.castSucc.succAbove k').succAbove j) = 0 := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k' _ ↦ ?_
  rcases le_or_gt j k' with hjk | hkj
  · rw [Fin.succAbove_castSucc_of_le j k' hjk, Fin.succAbove_succ_of_le k' j hjk]
    unfold homotopyGridTerm
    have hexp : (k'.succ : ℕ) + j.castSucc = (j : ℕ) + k' + 1 := by
      simp only [Fin.val_succ, Fin.val_castSucc]; omega
    rw [sum_hochschildFace_lt_homotopyTuple_succ r ψ k' hjk a, hexp, pow_succ, mul_neg_one,
      neg_smul, add_neg_cancel]
  · rw [Fin.succAbove_castSucc_of_lt j k' hkj, Fin.succAbove_castSucc_of_le k' j hkj.le]
    unfold homotopyGridTerm
    have hsum :
        ∑ p : Fin (k'.castSucc + 1) → ι,
            ψ (hochschildFace j.succ.castSucc (homotopyTuple (R := R) r k'.castSucc p a)) =
          ∑ p : Fin (k' + 1) → ι,
            ψ (homotopyTuple (R := R) r k' p (hochschildFace j.castSucc a)) :=
      Finset.sum_congr rfl fun p _ ↦
        congrArg ψ (hochschildFace_gt_homotopyTuple_castSucc r k' hkj p a)
    have hexp : (k'.castSucc : ℕ) + j.succ = (j : ℕ) + k' + 1 := by
      simp only [Fin.val_castSucc, Fin.val_succ]; omega
    rw [hsum, hexp, pow_succ, mul_neg_one, neg_smul, add_neg_cancel]

/-- **Contracting homotopy identity for the bar coboundary:**
`b' (H_n ψ) + H_{n+1} (b' ψ) = ψ` on `(n + 1)`-cochains of `M_ι(A)`. -/
private theorem barCoboundary_matrixHochschildHomotopy_add [SMulCommClass R R M] (r : ι) (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M) :
    barCoboundary R (Matrix ι ι A) M n (matrixHochschildHomotopy r n ψ) +
      matrixHochschildHomotopy r (n + 1) (barCoboundary R (Matrix ι ι A) M (n + 1) ψ) = ψ := by
  ext a
  rw [add_apply, barCoboundary_apply, matrixHochschildHomotopy_apply_eq]
  simp only [matrixHochschildHomotopy_apply_eq, barCoboundary_apply, ← hochschildFace_castSucc]
  have lhs_eq :
      (∑ j : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) •
        ∑ k' : Fin (n + 1), (-1 : ℤ) ^ (k' : ℕ) •
          ∑ q : Fin (k' + 1) → ι,
            ψ (homotopyTuple (R := R) r k' q (hochschildFace j.castSucc a))) =
        ∑ j : Fin (n + 1), ∑ k' : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + k') •
          ∑ q : Fin (k' + 1) → ι,
            ψ (homotopyTuple (R := R) r k' q (hochschildFace j.castSucc a)) := by
    simp_rw [Finset.smul_sum, smul_smul, ← pow_add]
  have rhs_eq :
      (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        ∑ p : Fin (k + 1) → ι, ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          ψ (hochschildFace i.castSucc (homotopyTuple (R := R) r k p a))) =
        ∑ k : Fin (n + 2), ∑ i : Fin (n + 2), homotopyGridTerm r ψ a k i := by
    unfold homotopyGridTerm
    conv_lhs =>
      arg 2; ext k; arg 2; rw [Finset.sum_comm]
      arg 2; ext i; rw [← Finset.smul_sum]
    simp_rw [Finset.smul_sum, smul_smul, ← pow_add]
  rw [lhs_eq, rhs_eq, sum_sum_homotopyGridTerm, ← add_assoc,
    sum_homotopyGrid_offDiag_eq_zero r ψ a, zero_add, Fin.sum_univ_succ (n := n + 1)]
  have hdiag0 : homotopyGridTerm r ψ a 0 0 = ψ a := by
    unfold homotopyGridTerm
    simpa using sum_hochschildFace_zero_homotopyTuple_zero r ψ a
  rw [hdiag0, add_assoc]
  refine add_eq_left.2 ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k' _ ↦ ?_
  unfold homotopyGridTerm
  have hexp1 : (k'.succ : ℕ) + k'.succ = 2 * ((k' : ℕ) + 1) := by
    simp only [Fin.val_succ]; omega
  have hexp2 : (k'.castSucc : ℕ) + k'.succ = 2 * (k' : ℕ) + 1 := by
    simp only [Fin.val_castSucc, Fin.val_succ]; omega
  rw [sum_hochschildFace_succ_homotopyTuple_succ r ψ k' a, hexp1, hexp2, pow_mul, neg_one_sq,
    one_pow, one_smul, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, neg_one_smul,
    add_neg_cancel]

/-- Signed commutator of `matrixHochschildHomotopy` with the cyclic last coface produces
`-(ψ|_r)#Tr`. -/
private theorem hochschildCoface_last_matrixHochschildHomotopy_add [SMulCommClass R R M]
    (r : ι) (n : ℕ) (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M) :
    (-1 : ℤ) ^ (n + 1) •
        hochschildCoface R (Matrix ι ι A) M (Fin.last (n + 1)) (matrixHochschildHomotopy r n ψ) +
      (-1 : ℤ) ^ (n + 2) •
        matrixHochschildHomotopy r (n + 1)
          (hochschildCoface R (Matrix ι ι A) M (Fin.last (n + 2)) ψ) =
      -matrixCochainExtension ι (n + 1) (matrixCornerCochainRestriction r (n + 1) ψ) := by
  ext a
  simp only [add_apply, neg_apply, smul_apply, hochschildCoface_apply,
    matrixHochschildHomotopy_apply_eq, Finset.smul_sum, smul_smul, ← pow_add]
  simp only [← Finset.smul_sum]
  rw [Fin.sum_univ_castSucc (n := n + 1), ← add_assoc]
  have hcancel :
      (∑ x : Fin (n + 1),
          (-1 : ℤ) ^ (n + 1 + (x : ℕ)) •
            ∑ p : Fin (x + 1) → ι,
              ψ (homotopyTuple (R := R) r x p (hochschildFace (Fin.last (n + 1)) a))) +
        ∑ x : Fin (n + 1),
          (-1 : ℤ) ^ (n + 2 + (x.castSucc : ℕ)) •
            ∑ p : Fin (x.castSucc + 1) → ι,
              ψ (hochschildFace (Fin.last (n + 2))
                (homotopyTuple (R := R) r x.castSucc p a)) = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k' _ ↦ ?_
    have hsum :
        ∑ p : Fin (k'.castSucc + 1) → ι,
            ψ (hochschildFace (Fin.last (n + 2)) (homotopyTuple (R := R) r k'.castSucc p a)) =
          ∑ p : Fin (k' + 1) → ι,
            ψ (homotopyTuple (R := R) r k' p (hochschildFace (Fin.last (n + 1)) a)) :=
      Finset.sum_congr rfl fun p _ ↦
        congrArg ψ (hochschildFace_last_homotopyTuple_castSucc r k' p a)
    have hexp : n + 2 + (k'.castSucc : ℕ) = (n + 1 + (k' : ℕ)) + 1 := by
      simp only [Fin.val_castSucc]; omega
    rw [hsum, hexp, pow_succ, mul_neg_one, neg_smul, add_neg_cancel]
  have hexp_last : n + 2 + (Fin.last (n + 1) : ℕ) = 2 * (n + 1) + 1 := by
    simp only [Fin.val_last]; omega
  rw [hcancel, zero_add, sum_hochschildFace_last_homotopyTuple_last r ψ a, hexp_last, pow_succ,
    pow_mul, neg_one_sq, one_pow, one_mul, neg_one_smul]

/-- **Chain homotopy identity in positive degree:**
`b (H_n ψ) + H_{n+1} (b ψ) = ψ - (ψ|_r)#Tr` on `(n + 1)`-cochains of `M_ι(A)`. -/
theorem hochschildCoboundary_matrixHochschildHomotopy_add [SMulCommClass R R M] (r : ι) (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M) :
    hochschildCoboundary R (Matrix ι ι A) M n (matrixHochschildHomotopy r n ψ) +
      matrixHochschildHomotopy r (n + 1)
        (hochschildCoboundary R (Matrix ι ι A) M (n + 1) ψ) =
      ψ - matrixCochainExtension ι (n + 1) (matrixCornerCochainRestriction r (n + 1) ψ) := by
  rw [hochschildCoboundary_eq_barCoboundary_add (matrixHochschildHomotopy r n ψ),
    hochschildCoboundary_eq_barCoboundary_add ψ, map_add, map_zsmul]
  calc
    (barCoboundary R (Matrix ι ι A) M n (matrixHochschildHomotopy r n ψ) +
        (-1 : ℤ) ^ (n + 1) • hochschildCoface R (Matrix ι ι A) M (Fin.last (n + 1))
          (matrixHochschildHomotopy r n ψ)) +
      (matrixHochschildHomotopy r (n + 1) (barCoboundary R (Matrix ι ι A) M (n + 1) ψ) +
        (-1 : ℤ) ^ (n + 2) • matrixHochschildHomotopy r (n + 1)
          (hochschildCoface R (Matrix ι ι A) M (Fin.last (n + 2)) ψ))
      = (barCoboundary R (Matrix ι ι A) M n (matrixHochschildHomotopy r n ψ) +
          matrixHochschildHomotopy r (n + 1) (barCoboundary R (Matrix ι ι A) M (n + 1) ψ)) +
        ((-1 : ℤ) ^ (n + 1) • hochschildCoface R (Matrix ι ι A) M (Fin.last (n + 1))
          (matrixHochschildHomotopy r n ψ) +
        (-1 : ℤ) ^ (n + 2) • matrixHochschildHomotopy r (n + 1)
          (hochschildCoface R (Matrix ι ι A) M (Fin.last (n + 2)) ψ)) := by abel
    _ = ψ - matrixCochainExtension ι (n + 1) (matrixCornerCochainRestriction r (n + 1) ψ) := by
        rw [barCoboundary_matrixHochschildHomotopy_add,
          hochschildCoface_last_matrixHochschildHomotopy_add, sub_eq_add_neg]

end Homotopy

/-! ### Hochschild cocycles, coboundaries and cohomology -/

section Cocycles

variable {R A M ι : Type*} [Semiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] [Fintype ι] {n : ℕ}

/-- Matrix extension sends Hochschild cocycles to Hochschild cocycles. -/
theorem matrixCochainExtension_mem_hochschildCocycles
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ hochschildCocycles R A M n) :
    matrixCochainExtension ι n φ ∈ hochschildCocycles R (Matrix ι ι A) M n := by
  rw [mem_hochschildCocycles_iff] at hφ ⊢
  rw [← matrixCochainExtension_hochschildCoboundary, hφ, map_zero]

/-- Matrix extension sends Hochschild coboundaries to Hochschild coboundaries. -/
theorem matrixCochainExtension_mem_hochschildCoboundaries
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ hochschildCoboundaries R A M n) :
    matrixCochainExtension ι n φ ∈ hochschildCoboundaries R (Matrix ι ι A) M n := by
  cases n with
  | zero =>
    rw [hochschildCoboundaries_zero, Submodule.mem_bot] at hφ ⊢
    rw [hφ, map_zero]
  | succ n =>
    obtain ⟨ψ, rfl⟩ := mem_hochschildCoboundaries_succ_iff.1 hφ
    exact mem_hochschildCoboundaries_succ_iff.2
      ⟨matrixCochainExtension ι n ψ, (matrixCochainExtension_hochschildCoboundary ι n ψ).symm⟩

/-- Corner restriction sends Hochschild cocycles to Hochschild cocycles. -/
theorem matrixCornerCochainRestriction_mem_hochschildCocycles [DecidableEq ι] (r : ι)
    {ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M}
    (hψ : ψ ∈ hochschildCocycles R (Matrix ι ι A) M n) :
    matrixCornerCochainRestriction r n ψ ∈ hochschildCocycles R A M n := by
  rw [mem_hochschildCocycles_iff] at hψ ⊢
  rw [← matrixCornerCochainRestriction_hochschildCoboundary, hψ, map_zero]

/-- Corner restriction sends Hochschild coboundaries to Hochschild coboundaries. -/
theorem matrixCornerCochainRestriction_mem_hochschildCoboundaries [DecidableEq ι] (r : ι)
    {ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M}
    (hψ : ψ ∈ hochschildCoboundaries R (Matrix ι ι A) M n) :
    matrixCornerCochainRestriction r n ψ ∈ hochschildCoboundaries R A M n := by
  cases n with
  | zero =>
    rw [hochschildCoboundaries_zero, Submodule.mem_bot] at hψ ⊢
    rw [hψ, map_zero]
  | succ n =>
    obtain ⟨χ, rfl⟩ := mem_hochschildCoboundaries_succ_iff.1 hψ
    exact mem_hochschildCoboundaries_succ_iff.2
      ⟨matrixCornerCochainRestriction r n χ,
        (matrixCornerCochainRestriction_hochschildCoboundary r n χ).symm⟩

/-- Over a unital semiring `A`, every Hochschild cocycle on `Matrix ι ι A` is cohomologous to the
matrix extension of its restriction to any diagonal corner `r`. -/
theorem sub_matrixCochainExtension_matrixCornerCochainRestriction_mem_hochschildCoboundaries
    {B : Type*} [Semiring B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
    [DecidableEq ι] (r : ι)
    {ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι B) M}
    (hψ : ψ ∈ hochschildCocycles R (Matrix ι ι B) M n) :
    ψ - matrixCochainExtension ι n (matrixCornerCochainRestriction r n ψ) ∈
      hochschildCoboundaries R (Matrix ι ι B) M n := by
  rw [mem_hochschildCocycles_iff] at hψ
  cases n with
  | zero =>
    have h0 := matrixHochschildHomotopy_hochschildCoboundary_zero r ψ
    rw [hψ, map_zero, eq_comm] at h0
    rw [h0, hochschildCoboundaries_zero]
    exact Submodule.zero_mem _
  | succ n =>
    have h := hochschildCoboundary_matrixHochschildHomotopy_add r n ψ
    rw [hψ, map_zero, add_zero] at h
    exact mem_hochschildCoboundaries_succ_iff.2 ⟨matrixHochschildHomotopy r n ψ, h⟩

end Cocycles

namespace hochschildCohomology

section NonUnital

variable {R A : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- The map on Hochschild cohomology induced by the generalized matrix trace `φ ↦ φ#Tr`. -/
def matrixExtension (M : Type*) [AddCommGroup M] [Module R M] (ι : Type*) [Fintype ι] (n : ℕ) :
    hochschildCohomology R A M n →ₗ[R] hochschildCohomology R (Matrix ι ι A) M n :=
  desc n (mk R (Matrix ι ι A) M n ∘ₗ (matrixCochainExtension ι n).restrict
      fun _ ↦ matrixCochainExtension_mem_hochschildCocycles)
    fun _ hφ ↦ (mk_eq_zero_iff _ _ _ n _).2 (matrixCochainExtension_mem_hochschildCoboundaries hφ)

/-- `matrixExtension` sends the class of a Hochschild cocycle to the class of its matrix
extension. -/
@[simp]
theorem matrixExtension_mk {M : Type*} [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι]
    {n : ℕ} (φ : hochschildCocycles R A M n) :
    matrixExtension M ι n (mk R A M n φ) =
      mk R (Matrix ι ι A) M n ⟨matrixCochainExtension ι n φ.1,
        matrixCochainExtension_mem_hochschildCocycles φ.2⟩ :=
  desc_mk _ _ _ φ

/-- The map on Hochschild cohomology induced by restriction of cochains to the `(r, r)` diagonal
corner. -/
def cornerRestriction (M : Type*) [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (r : ι) (n : ℕ) :
    hochschildCohomology R (Matrix ι ι A) M n →ₗ[R] hochschildCohomology R A M n :=
  desc n (mk R A M n ∘ₗ (matrixCornerCochainRestriction r n).restrict
      fun _ ↦ matrixCornerCochainRestriction_mem_hochschildCocycles r)
    fun _ hψ ↦ (mk_eq_zero_iff _ _ _ n _).2
      (matrixCornerCochainRestriction_mem_hochschildCoboundaries r hψ)

/-- `cornerRestriction` sends the class of a Hochschild cocycle to the class of its corner
restriction. -/
@[simp]
theorem cornerRestriction_mk {M : Type*} [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (r : ι) {n : ℕ} (ψ : hochschildCocycles R (Matrix ι ι A) M n) :
    cornerRestriction M r n (mk R (Matrix ι ι A) M n ψ) =
      mk R A M n ⟨matrixCornerCochainRestriction r n ψ.1,
        matrixCornerCochainRestriction_mem_hochschildCocycles r ψ.2⟩ :=
  desc_mk _ _ _ ψ

/-- On Hochschild cohomology, restriction to any diagonal corner is a left inverse to
`matrixExtension`. -/
@[simp]
theorem cornerRestriction_matrixExtension {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) (n : ℕ)
    (c : hochschildCohomology R A M n) :
    cornerRestriction M r n (matrixExtension M ι n c) = c := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  rw [matrixExtension_mk, cornerRestriction_mk]
  congr 1
  exact Subtype.ext (matrixCornerCochainRestriction_matrixCochainExtension r n φ.1)

/-- As linear maps on Hochschild cohomology, `cornerRestriction` composed with `matrixExtension` is
the identity. -/
@[simp]
theorem cornerRestriction_comp_matrixExtension {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) (n : ℕ) :
    cornerRestriction (R := R) (A := A) M r n ∘ₗ matrixExtension M ι n = LinearMap.id :=
  LinearMap.ext (cornerRestriction_matrixExtension r n)

end NonUnital

section Unital

variable {R A M : Type*} [CommRing R] [Semiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Over a unital algebra, `matrixExtension` is a left inverse to `cornerRestriction` on Hochschild
cohomology. -/
@[simp]
theorem matrixExtension_cornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) (n : ℕ)
    (c : hochschildCohomology R (Matrix ι ι A) M n) :
    matrixExtension M ι n (cornerRestriction M r n c) = c := by
  obtain ⟨ψ, rfl⟩ := mk_surjective R (Matrix ι ι A) M n c
  rw [cornerRestriction_mk, matrixExtension_mk, eq_comm, mk_eq_mk_iff]
  exact sub_matrixCochainExtension_matrixCornerCochainRestriction_mem_hochschildCoboundaries r ψ.2

/-- As linear maps on Hochschild cohomology of a unital algebra, `matrixExtension` composed with
`cornerRestriction` is the identity. -/
@[simp]
theorem matrixExtension_comp_cornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι) (n : ℕ) :
    matrixExtension (R := R) (A := A) M ι n ∘ₗ cornerRestriction M r n = LinearMap.id :=
  LinearMap.ext (matrixExtension_cornerRestriction r n)

/-- On Hochschild cohomology of a unital algebra, corner restriction is independent of the chosen
diagonal corner. -/
theorem cornerRestriction_eq_cornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r s : ι) (n : ℕ) :
    cornerRestriction (R := R) (A := A) M r n = cornerRestriction M s n := by
  calc
    cornerRestriction (R := R) (A := A) M r n
      = cornerRestriction M r n ∘ₗ (matrixExtension M ι n ∘ₗ cornerRestriction M s n) := by simp
    _ = (cornerRestriction M r n ∘ₗ matrixExtension M ι n) ∘ₗ cornerRestriction M s n :=
        (LinearMap.comp_assoc _ _ _).symm
    _ = cornerRestriction M s n := by simp

/-- **Matrix Morita invariance of Hochschild cohomology.** For a unital algebra `A` over any
commutative ring `R`, coefficients in an `R`-module `M`, and a nonempty finite index type `ι`, the
generalized matrix trace `φ ↦ φ#Tr` induces a bijection
`HHⁿ(A, Hom_R(A, M)) → HHⁿ(M_ι(A), Hom_R(M_ι(A), M))` in every degree `n`. -/
theorem bijective_matrixExtension (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  classical
  obtain ⟨r⟩ := ‹Nonempty ι›
  exact ⟨Function.LeftInverse.injective (cornerRestriction_matrixExtension r n),
    Function.RightInverse.surjective (matrixExtension_cornerRestriction r n)⟩

variable (R A M) in
/-- **Matrix Morita equivalence for Hochschild cohomology:** the linear equivalence
`HHⁿ(A, Hom_R(A, M)) ≃ₗ[R] HHⁿ(M_ι(A), Hom_R(M_ι(A), M))` induced by `φ ↦ φ#Tr`. -/
def matrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    hochschildCohomology R A M n ≃ₗ[R] hochschildCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension ι n)

/-- Forgetting the inverse of `matrixExtensionEquiv` recovers `matrixExtension`. -/
@[simp]
theorem toLinearMap_matrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    (matrixExtensionEquiv R A M ι n).toLinearMap = matrixExtension M ι n :=
  (rfl)

/-- Applying `matrixExtensionEquiv` applies `matrixExtension`. -/
@[simp]
theorem matrixExtensionEquiv_apply (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ)
    (c : hochschildCohomology R A M n) :
    matrixExtensionEquiv R A M ι n c = matrixExtension M ι n c :=
  (rfl)

/-- For any diagonal corner `r : ι`, the inverse of `matrixExtensionEquiv` is `cornerRestriction`
at `r`. -/
theorem matrixExtensionEquiv_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (r : ι) (n : ℕ) (c : hochschildCohomology R (Matrix ι ι A) M n) :
    (matrixExtensionEquiv R A M ι n).symm c = cornerRestriction M r n c :=
  (matrixExtensionEquiv R A M ι n).symm_apply_eq.2
    (matrixExtension_cornerRestriction r n c).symm

end Unital

end hochschildCohomology

end TauCeti

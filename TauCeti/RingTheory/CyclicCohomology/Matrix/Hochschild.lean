/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Matrix.Basic
public import TauCeti.RingTheory.HochschildCohomology.Complex
import Mathlib.Tactic.Abel
import TauCeti.Data.Fin.Basic

/-!
# Matrix Morita invariance of Hochschild cohomology

For an algebra `A` over `R`, coefficients in an `R`-module `M`, and a finite index type `ι`, the
generalized matrix trace `TauCeti.matrixCochainExtension` sends an `M`-valued cochain `φ` on `A` to
`φ#Tr` on `Matrix ι ι A`. Choosing a diagonal corner `r : ι` gives a nonunital algebra homomorphism
`x ↦ Matrix.single r r x` (`TauCeti.matrixCornerNonUnitalAlgHom`), and pulling cochains back along
this corner map defines `TauCeti.matrixCornerRestriction`.

On cochains, corner restriction is a left inverse to matrix extension (`(φ#Tr) ∘ E_{rr} = φ`) and
commutes with every Hochschild coface and with the Hochschild coboundary. When `A` is unital, the
reverse composite `Φ ↦ (Φ ∘ E_{rr})#Tr` on `C^*(Matrix ι ι A; M)` is cochain homotopic to the
identity via an explicit homotopy `TauCeti.matrixHochschildHomotopy` built from matrix units and
the cyclic operator:

`(hₙ Φ) = ∑_{m = 0}^n λₙ^m (S_{n, m} Φ)`,

where `(S_{n, m} Φ)(b₀, …, bₙ)` sums
`Φ(E_{p₀, r}(1), E_{r, r}((b₀)_{p₀, p₁}), …, E_{r, r}((b_{m-1})_{p_{m-1}, p_m}),`
`  E_{r, p_m}(1) b_m, b_{m+1}, …, b_n)`
over index paths `p : Fin (m + 1) → ι`. This yields `h₀ (b₀ Ψ) = Ψ - (Ψ ∘ E_{rr})#Tr` in degree
zero—so every trace on `Matrix ι ι A` is the matrix extension of its corner restriction—and
`h_{k+1} (b_{k+1} Ψ) + b_k (h_k Ψ) = Ψ - (Ψ ∘ E_{rr})#Tr` in positive degrees.

Consequently, over every commutative ring `R`, when `A` is unital and `ι` is nonempty and finite,
`TauCeti.hochschildCohomology.matrixExtension` and
`TauCeti.hochschildCohomology.cornerRestriction` are mutually inverse linear maps between
`HHⁿ(A, Hom_R(A, M))` and `HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M))` in every degree `n`, and
corner restriction on cohomology is independent of the chosen diagonal corner.

## Main definitions

* `TauCeti.matrixCornerNonUnitalAlgHom`: the diagonal corner embedding `A →ₙₐ[R] Matrix ι ι A`.
* `TauCeti.matrixCornerRestriction`: pullback of multilinear cochains along a diagonal corner.
* `TauCeti.matrixHochschildHomotopy`: the cochain homotopy between the identity and corner
  projection followed by matrix extension on `C^*(Matrix ι ι A; M)`.
* `TauCeti.hochschildCohomology.matrixExtension`,
  `TauCeti.hochschildCohomology.cornerRestriction`: matrix extension and corner restriction on
  Hochschild cohomology.
* `TauCeti.hochschildCohomology.matrixExtensionEquiv`: the linear equivalence
  `HHⁿ(A, Hom_R(A, M)) ≃ₗ[R] HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M))`.

## Main results

* `TauCeti.matrixHochschildHomotopy_hochschildCoboundary_zero`,
  `TauCeti.matrixHochschildHomotopy_hochschildCoboundary_succ`: the cochain homotopy identities in
  degree zero and positive degree.
* `TauCeti.matrixCochainExtension_matrixCornerRestriction_of_mem_hochschildCocycles_zero`: every
  `M`-valued trace on `Matrix ι ι A` is the matrix extension of its restriction to a corner.
* `TauCeti.hochschildCohomology.bijective_matrixExtension`: matrix Morita invariance of Hochschild
  cohomology over any commutative ring.
* `TauCeti.hochschildCohomology.cornerRestriction_eq_cornerRestriction`: corner restriction on
  Hochschild cohomology is independent of the chosen diagonal index.

## References

* A. Connes, *Non-commutative differential geometry*, Publ. Math. IHÉS **62** (1985), Part II, §1.
* A. Connes, *Noncommutative Geometry* (1994), Chapter III, §1.
* R. McCarthy, *Morita equivalence and cyclic homology*, C. R. Acad. Sci. Paris Sér. I Math.
  **307** (1988), 91–95.
* J.-L. Loday, *Cyclic Homology*, 2nd ed., Springer, 1998, §§1.2.4, 1.5.6.
-/

public section

namespace TauCeti

open scoped BigOperators

/-! ### Diagonal corner restriction of cochains -/

section Corner

/-- The diagonal corner inclusion `x ↦ Matrix.single r r x` as a homomorphism of nonunital
`R`-algebras `A →ₙₐ[R] Matrix ι ι A`. -/
def matrixCornerNonUnitalAlgHom (R A : Type*) {ι : Type*} [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Fintype ι] [DecidableEq ι] (r : ι) :
    A →ₙₐ[R] Matrix ι ι A where
  toFun := Matrix.single r r
  map_smul' := (Matrix.singleLinearMap R r r).map_smul'
  map_zero' := (Matrix.singleLinearMap R r r).map_zero
  map_add' := (Matrix.singleLinearMap R r r).map_add'
  map_mul' x y := (Matrix.single_mul_single_same x r r r y).symm

/-- Evaluating `matrixCornerNonUnitalAlgHom` gives `Matrix.single r r`. -/
@[simp]
theorem matrixCornerNonUnitalAlgHom_apply {R A ι : Type*} [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Fintype ι] [DecidableEq ι] (r : ι) (x : A) :
    matrixCornerNonUnitalAlgHom R A r x = Matrix.single r r x :=
  (rfl)

/-- The underlying linear map of `matrixCornerNonUnitalAlgHom` is `Matrix.singleLinearMap`. -/
@[simp]
theorem toLinearMap_matrixCornerNonUnitalAlgHom (R A : Type*) {ι : Type*} [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Fintype ι] [DecidableEq ι] (r : ι) :
    (matrixCornerNonUnitalAlgHom R A r : A →ₗ[R] Matrix ι ι A) = Matrix.singleLinearMap R r r :=
  (rfl)

section Linear

variable {R A M ι : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
  [AddCommMonoid M] [Module R M] [SMulCommClass R R M] [DecidableEq ι]

/-- Restrict a degree-`n` cochain on `Matrix ι ι A` to `A` along the `(r, r)` diagonal corner:
`(matrixCornerRestriction r n Φ)(x₀, …, xₙ) = Φ(E_{rr}(x₀), …, E_{rr}(xₙ))`. -/
def matrixCornerRestriction (r : ι) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => A) M where
  toFun Φ := Φ.compLinearMap fun _ => Matrix.singleLinearMap R r r
  map_add' _ _ := by
    ext
    simp [MultilinearMap.compLinearMap_apply]
  map_smul' _ _ := by
    ext
    simp [MultilinearMap.compLinearMap_apply]

/-- Corner restriction evaluates a matrix cochain on diagonal corner matrices
`Matrix.single r r`. -/
@[simp]
theorem matrixCornerRestriction_apply (r : ι) (n : ℕ)
    (Φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => Matrix ι ι A) M)
    (x : Fin (n + 1) → A) :
    matrixCornerRestriction r n Φ x = Φ fun j => Matrix.single r r (x j) :=
  (rfl)

/-- Restricting a matrix-extended cochain to any diagonal corner recovers the original cochain. -/
@[simp]
theorem matrixCornerRestriction_matrixCochainExtension [Fintype ι] (r : ι) (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => A) M) :
    matrixCornerRestriction r n (matrixCochainExtension ι n φ) = φ := by
  ext x
  exact matrixCochainExtension_single ι r n φ x

/-- Corner restriction is a left inverse to matrix extension of cochains. -/
@[simp]
theorem matrixCornerRestriction_comp_matrixCochainExtension [Fintype ι] (r : ι) (n : ℕ) :
    matrixCornerRestriction (R := R) (A := A) (M := M) r n ∘ₗ matrixCochainExtension ι n =
      LinearMap.id :=
  LinearMap.ext (matrixCornerRestriction_matrixCochainExtension r n)

end Linear

section Coface

variable {R A M ι : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommMonoid M] [Module R M]
  [SMulCommClass R R M] [Fintype ι] [DecidableEq ι]

/-- Corner restriction commutes with every Hochschild coface. -/
theorem matrixCornerRestriction_hochschildCoface (r : ι) (n : ℕ) (i : Fin (n + 2))
    (Φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => Matrix ι ι A) M) :
    matrixCornerRestriction r (n + 1) (hochschildCoface R (Matrix ι ι A) M i Φ) =
      hochschildCoface R A M i (matrixCornerRestriction r n Φ) := by
  ext x
  simp only [matrixCornerRestriction_apply, hochschildCoface_apply]
  exact congrArg Φ (comp_hochschildFace (matrixCornerNonUnitalAlgHom R A r) i x).symm

end Coface

section Coboundary

variable {R A M ι : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] [Fintype ι] [DecidableEq ι]

/-- Corner restriction commutes with the Hochschild coboundary. -/
theorem matrixCornerRestriction_hochschildCoboundary (r : ι) (n : ℕ)
    (Φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => Matrix ι ι A) M) :
    matrixCornerRestriction r (n + 1) (hochschildCoboundary R (Matrix ι ι A) M n Φ) =
      hochschildCoboundary R A M n (matrixCornerRestriction r n Φ) :=
  (hochschildCoboundary_compLinearMap (matrixCornerNonUnitalAlgHom R A r) Φ).symm

omit [NonUnitalNonAssocSemiring A] [IsScalarTower R A A] [SMulCommClass R A A] [Fintype ι] in
/-- Corner restriction commutes with the cyclic operator. -/
theorem matrixCornerRestriction_cyclicOperator {A : Type*} [AddCommMonoid A] [Module R A]
    (r : ι) (n : ℕ)
    (Φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => Matrix ι ι A) M) :
    matrixCornerRestriction r n (cyclicOperator R (Matrix ι ι A) M n Φ) =
      cyclicOperator R A M n (matrixCornerRestriction r n Φ) := by
  ext x
  simp only [matrixCornerRestriction_apply, cyclicOperator_apply]
  rfl

end Coboundary

section Cocycles

variable {R A M ι : Type*} [Semiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] [Fintype ι] {n : ℕ}

/-- Matrix extension sends Hochschild cocycles to Hochschild cocycles. -/
theorem matrixCochainExtension_mem_hochschildCocycles
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => A) M}
    (hφ : φ ∈ hochschildCocycles R A M n) :
    matrixCochainExtension ι n φ ∈ hochschildCocycles R (Matrix ι ι A) M n := by
  rw [mem_hochschildCocycles_iff] at hφ ⊢
  rw [← matrixCochainExtension_hochschildCoboundary, hφ, map_zero]

/-- Matrix extension sends Hochschild coboundaries to Hochschild coboundaries. -/
theorem matrixCochainExtension_mem_hochschildCoboundaries
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => A) M}
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
theorem matrixCornerRestriction_mem_hochschildCocycles [DecidableEq ι] (r : ι)
    {Φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => Matrix ι ι A) M}
    (hΦ : Φ ∈ hochschildCocycles R (Matrix ι ι A) M n) :
    matrixCornerRestriction r n Φ ∈ hochschildCocycles R A M n := by
  rw [mem_hochschildCocycles_iff] at hΦ ⊢
  rw [← matrixCornerRestriction_hochschildCoboundary, hΦ, map_zero]

/-- Corner restriction sends Hochschild coboundaries to Hochschild coboundaries. -/
theorem matrixCornerRestriction_mem_hochschildCoboundaries [DecidableEq ι] (r : ι)
    {Φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => Matrix ι ι A) M}
    (hΦ : Φ ∈ hochschildCoboundaries R (Matrix ι ι A) M n) :
    matrixCornerRestriction r n Φ ∈ hochschildCoboundaries R A M n := by
  cases n with
  | zero =>
    rw [hochschildCoboundaries_zero, Submodule.mem_bot] at hΦ ⊢
    rw [hΦ, map_zero]
  | succ n =>
    obtain ⟨Ψ, rfl⟩ := mem_hochschildCoboundaries_succ_iff.1 hΦ
    exact mem_hochschildCoboundaries_succ_iff.2
      ⟨matrixCornerRestriction r n Ψ, (matrixCornerRestriction_hochschildCoboundary r n Ψ).symm⟩

end Cocycles

end Corner

/-! ### Cochain homotopy for matrix Morita invariance -/

section Homotopy

section CyclicIdentity

variable {R B M : Type*} [Semiring R] [NonUnitalNonAssocSemiring B] [Module R B]
  [IsScalarTower R B B] [SMulCommClass R B B] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M]

/-- Rotating the `m`-th coface `m + 1` times produces the last coface up to sign. -/
private theorem neg_one_pow_smul_cyclicOperator_pow_succ_hochschildCoface {k m : ℕ}
    (hm : m ≤ k) (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (k + 1) => B) M) :
    (-1 : ℤ) ^ (m + 1) • (cyclicOperator R B M (k + 1) ^ (m + 1))
        (hochschildCoface R B M (⟨m, by omega⟩ : Fin (k + 1)).castSucc φ) =
      -((-1 : ℤ) ^ (k + 1) •
        hochschildCoface R B M (Fin.last (k + 1)) ((cyclicOperator R B M k ^ m) φ)) := by
  have hcast : (⟨m, by omega⟩ : Fin (k + 1)).castSucc = ⟨m, by omega⟩ := rfl
  rw [hcast, pow_succ' (cyclicOperator R B M (k + 1)), _root_.mul_apply_eq_comp,
    cyclicOperator_pow_hochschildCoface m (by omega) φ, map_zsmul,
    cyclicOperator_hochschildCoface_zero, smul_smul, smul_smul]
  have hm_eq : m + 1 + m = 2 * m + 1 := by omega
  have hsign : (-1 : ℤ) ^ (m + 1) * (-1 : ℤ) ^ m * (-1 : ℤ) ^ (k + 1) =
      -((-1 : ℤ) ^ (k + 1)) := by
    rw [← pow_add, hm_eq, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, neg_one_mul]
  rw [hsign, neg_smul]

/-- Split-sum cancellation between rotated cofaces and the Hochschild coboundary of `λ^m φ`. -/
private theorem sum_filter_cyclicOperator_pow_hochschildCoface_add_hochschildCoboundary
    {k m : ℕ} (hm : m ≤ k)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (k + 1) => B) M) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin (k + 1) => m ≤ (i : ℕ)),
        (-1 : ℤ) ^ ((i : ℕ) + 1) •
          (cyclicOperator R B M (k + 1) ^ m) (hochschildCoface R B M i.castSucc φ)) +
      (∑ i ∈ Finset.univ.filter (fun i : Fin (k + 1) => (i : ℕ) ≤ m),
        (-1 : ℤ) ^ ((i : ℕ) + 1) •
          (cyclicOperator R B M (k + 1) ^ (m + 1)) (hochschildCoface R B M i.castSucc φ)) +
      hochschildCoboundary R B M k ((cyclicOperator R B M k ^ m) φ) = 0 := by
  induction m with
  | zero =>
    -- At `m = 0`, the first sum is `-b' φ` and the second is `-λ (δ₀ φ) = -(-1)^(k+1) δ_{k+1} φ`.
    have hA : (Finset.univ.filter fun i : Fin (k + 1) => 0 ≤ (i : ℕ)) = Finset.univ := by
      ext i; simp
    have hB : (Finset.univ.filter fun i : Fin (k + 1) => (i : ℕ) ≤ 0) = {0} := by
      ext ⟨i, hi⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff,
        Fin.val_zero]
      omega
    rw [hA, hB, Finset.sum_singleton, pow_zero, pow_zero, zero_add, pow_one, Fin.val_zero,
      zero_add, pow_one, neg_one_smul, Fin.castSucc_zero, cyclicOperator_hochschildCoface_zero,
      _root_.one_apply_eq_self, hochschildCoboundary_eq_barCoboundary_add]
    have hbar : (∑ x : Fin (k + 1),
        (-1 : ℤ) ^ ((x : ℕ) + 1) • (1 : Module.End R _) (hochschildCoface R B M x.castSucc φ)) =
        -barCoboundary R B M k φ := by
      ext a
      simp only [sum_apply, barCoboundary_apply, neg_apply, smul_apply, _root_.one_apply_eq_self,
        hochschildCoface_apply, hochschildFace_castSucc, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ, mul_neg_one, neg_smul]
    rw [hbar]
    abel
  | succ m ih =>
    -- Apply `λ` to the inductive hypothesis at `m`; peeling `i = m` from the upper sum and
    -- inserting `i = m + 1` into the lower sum produces the two wrap-around `Fin.last` terms that
    -- match `b (λ^(m+1) φ) - λ (b (λ^m φ))`.
    have hm' : m ≤ k := Nat.le_of_succ_le hm
    let im : Fin (k + 1) := ⟨m, by omega⟩
    let im1 : Fin (k + 1) := ⟨m + 1, by omega⟩
    have hinsA : (Finset.univ.filter fun i : Fin (k + 1) => m ≤ (i : ℕ)) =
        insert im (Finset.univ.filter fun i : Fin (k + 1) => m + 1 ≤ (i : ℕ)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, im]
      omega
    have hnotmemA : im ∉ Finset.univ.filter (fun i : Fin (k + 1) => m + 1 ≤ (i : ℕ)) := by
      simp [im]
    have hinsB : (Finset.univ.filter fun i : Fin (k + 1) => (i : ℕ) ≤ m + 1) =
        insert im1 (Finset.univ.filter fun i : Fin (k + 1) => (i : ℕ) ≤ m) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, im1]
      omega
    have hnotmemB : im1 ∉ Finset.univ.filter (fun i : Fin (k + 1) => (i : ℕ) ≤ m) := by
      simp [im1]
    have stepA := congrArg (cyclicOperator R B M (k + 1)) (ih hm')
    rw [map_zero, map_add, map_add, hinsA, Finset.sum_insert hnotmemA, map_add, map_sum,
      map_sum] at stepA
    have hsumA : (∑ x ∈ Finset.univ.filter (fun i : Fin (k + 1) => m + 1 ≤ (i : ℕ)),
        cyclicOperator R B M (k + 1)
          ((-1 : ℤ) ^ ((x : ℕ) + 1) •
            (cyclicOperator R B M (k + 1) ^ m) (hochschildCoface R B M x.castSucc φ))) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin (k + 1) => m + 1 ≤ (i : ℕ)),
          (-1 : ℤ) ^ ((i : ℕ) + 1) •
            (cyclicOperator R B M (k + 1) ^ (m + 1)) (hochschildCoface R B M i.castSucc φ) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, ← _root_.mul_apply_eq_comp, ← pow_succ']
    have hsumB : (∑ x ∈ Finset.univ.filter (fun i : Fin (k + 1) => (i : ℕ) ≤ m),
        cyclicOperator R B M (k + 1)
          ((-1 : ℤ) ^ ((x : ℕ) + 1) •
            (cyclicOperator R B M (k + 1) ^ (m + 1)) (hochschildCoface R B M x.castSucc φ))) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin (k + 1) => (i : ℕ) ≤ m),
          (-1 : ℤ) ^ ((i : ℕ) + 1) •
            (cyclicOperator R B M (k + 1) ^ (m + 1 + 1))
              (hochschildCoface R B M i.castSucc φ) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, ← _root_.mul_apply_eq_comp, ← pow_succ']
    have him : cyclicOperator R B M (k + 1)
        ((-1 : ℤ) ^ ((im : ℕ) + 1) •
          (cyclicOperator R B M (k + 1) ^ m) (hochschildCoface R B M im.castSucc φ)) =
        -((-1 : ℤ) ^ (k + 1) •
          hochschildCoface R B M (Fin.last (k + 1)) ((cyclicOperator R B M k ^ m) φ)) := by
      rw [map_zsmul, ← _root_.mul_apply_eq_comp, ← pow_succ']
      exact neg_one_pow_smul_cyclicOperator_pow_succ_hochschildCoface hm' φ
    have him1 : (-1 : ℤ) ^ ((im1 : ℕ) + 1) •
        (cyclicOperator R B M (k + 1) ^ (m + 1 + 1)) (hochschildCoface R B M im1.castSucc φ) =
        -((-1 : ℤ) ^ (k + 1) •
          hochschildCoface R B M (Fin.last (k + 1)) ((cyclicOperator R B M k ^ (m + 1)) φ)) :=
      neg_one_pow_smul_cyclicOperator_pow_succ_hochschildCoface hm φ
    have hcob : hochschildCoboundary R B M k ((cyclicOperator R B M k ^ (m + 1)) φ) =
        cyclicOperator R B M (k + 1)
          (hochschildCoboundary R B M k ((cyclicOperator R B M k ^ m) φ)) +
        (-1 : ℤ) ^ (k + 1) •
          hochschildCoface R B M (Fin.last (k + 1)) ((cyclicOperator R B M k ^ (m + 1)) φ) -
        (-1 : ℤ) ^ (k + 1) •
          hochschildCoface R B M (Fin.last (k + 1)) ((cyclicOperator R B M k ^ m) φ) := by
      rw [pow_succ', _root_.mul_apply_eq_comp, hochschildCoboundary_eq_barCoboundary_add,
        cyclicOperator_hochschildCoboundary]
      abel
    rw [hsumA, hsumB, him] at stepA
    rw [hinsB, Finset.sum_insert hnotmemB, him1, hcob]
    convert stepA using 1
    abel

end CyclicIdentity

section Coord

variable {R A ι : Type*} [Semiring R] [Semiring A] [Module R A]
  [SMulCommClass R A A] [Fintype ι] [DecidableEq ι]

/-- The `k`-th coordinate linear map in the `m`-th presimplicial homotopy step along path `p`:
diagonal corner entry `(p k, p (k + 1))` for `k < m`, left multiplication by `E_{r, p m}(1)` at
`k = m`, and the identity for `k > m`. -/
private def homotopyCoordLinearMap (r : ι) {m : ℕ} (p : Fin (m + 1) → ι) (k : ℕ) :
    Matrix ι ι A →ₗ[R] Matrix ι ι A :=
  if hk : k < m then
    Matrix.singleLinearMap R r r ∘ₗ
      Matrix.entryLinearMap R A (p ⟨k, by omega⟩) (p ⟨k + 1, by omega⟩)
  else if _ : k = m then
    LinearMap.mulLeft R (Matrix.single r (p ⟨m, by omega⟩) (1 : A))
  else
    LinearMap.id

private theorem homotopyCoordLinearMap_of_lt (r : ι) {m k : ℕ} (hk : k < m)
    (p : Fin (m + 1) → ι) (X : Matrix ι ι A) :
    homotopyCoordLinearMap (R := R) r p k X =
      Matrix.single r r (X (p ⟨k, by omega⟩) (p ⟨k + 1, by omega⟩)) := by
  simp [homotopyCoordLinearMap, hk]

private theorem homotopyCoordLinearMap_same (r : ι) (m : ℕ) (p : Fin (m + 1) → ι)
    (X : Matrix ι ι A) :
    homotopyCoordLinearMap (R := R) r p m X =
      Matrix.single r (p ⟨m, by omega⟩) (1 : A) * X := by
  simp [homotopyCoordLinearMap]

private theorem homotopyCoordLinearMap_of_gt (r : ι) {m k : ℕ} (hk : m < k)
    (p : Fin (m + 1) → ι) (X : Matrix ι ι A) :
    homotopyCoordLinearMap (R := R) r p k X = X := by
  have h1 : ¬k < m := by omega
  have h2 : k ≠ m := by omega
  simp [homotopyCoordLinearMap, h1, h2]

/-- Prepending an initial index `u` shifts `homotopyCoordLinearMap` by one slot. -/
private theorem homotopyCoordLinearMap_cons_succ (r u : ι) {m : ℕ} (q : Fin (m + 1) → ι)
    (k : ℕ) (X : Matrix ι ι A) :
    homotopyCoordLinearMap (R := R) r (Fin.cons u q) (k + 1) X =
      homotopyCoordLinearMap (R := R) r q k X := by
  by_cases hk : k < m
  · rw [homotopyCoordLinearMap_of_lt r (by omega) (Fin.cons u q),
      homotopyCoordLinearMap_of_lt r hk q]
    have h1 : (Fin.cons u q : Fin (m + 2) → ι) ⟨k + 1, by omega⟩ = q ⟨k, by omega⟩ :=
      Fin.cons_succ (α := fun _ => ι) u q (⟨k, by omega⟩ : Fin (m + 1))
    have h2 : (Fin.cons u q : Fin (m + 2) → ι) ⟨k + 1 + 1, by omega⟩ = q ⟨k + 1, by omega⟩ :=
      Fin.cons_succ (α := fun _ => ι) u q (⟨k + 1, by omega⟩ : Fin (m + 1))
    rw [h1, h2]
  · by_cases hkm : k = m
    · subst hkm
      rw [homotopyCoordLinearMap_same, homotopyCoordLinearMap_same]
      have h1 : (Fin.cons u q : Fin (k + 2) → ι) ⟨k + 1, by omega⟩ = q ⟨k, by omega⟩ :=
        Fin.cons_succ (α := fun _ => ι) u q (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))
      rw [h1]
    · have hgt : m < k := by omega
      rw [homotopyCoordLinearMap_of_gt r (by omega), homotopyCoordLinearMap_of_gt r hgt]

end Coord

section Step

variable {R A M ι : Type*} [Semiring R] [Semiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] [Fintype ι] [DecidableEq ι]

/-- The unrotated `m`-th homotopy step `S_{n, m} : C^{n+1}(M_ι(A); M) →ₗ[R] C^n(M_ι(A); M)`. -/
private noncomputable def homotopyStep (r : ι) (n m : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) => Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => Matrix ι ι A) M where
  toFun Φ := ∑ p : Fin (m + 1) → ι,
    (MultilinearMap.mk'
      (fun a : Fin (n + 1) → Matrix ι ι A => Φ (Fin.cons (Matrix.single (p 0) r 1) a))
      (fun a i x y => by
        rw [Fin.cons_update, Φ.map_update_add, ← Fin.cons_update, ← Fin.cons_update])
      (fun a i c x => by
        rw [Fin.cons_update, Φ.map_update_smul, RingHom.id_apply, ← Fin.cons_update])).compLinearMap
      fun k : Fin (n + 1) => homotopyCoordLinearMap r p k
  map_add' _ _ := by
    ext b
    simp [Finset.sum_add_distrib]
  map_smul' _ _ := by
    ext b
    simp [Finset.smul_sum]

omit [IsScalarTower R A A] in
private theorem homotopyStep_apply (r : ι) (n m : ℕ)
    (Φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) => Matrix ι ι A) M)
    (b : Fin (n + 1) → Matrix ι ι A) :
    homotopyStep r n m Φ b =
      ∑ p : Fin (m + 1) → ι,
        Φ (Fin.cons (Matrix.single (p 0) r 1) fun k =>
          homotopyCoordLinearMap (R := R) r p k (b k)) := by
  simp [homotopyStep]

/-- At `m = 0`, `S_{n, 0}` is a left inverse to the zeroth Hochschild coface `δ₀`. -/
private theorem homotopyStep_zero_hochschildCoface_zero (r : ι) (n : ℕ)
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => Matrix ι ι A) M) :
    homotopyStep r n 0 (hochschildCoface R (Matrix ι ι A) M 0 Ψ) = Ψ := by
  ext b
  rw [homotopyStep_apply]
  simp only [hochschildCoface_apply]
  rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
  have h1 (u : ι) :
      hochschildFace 0
        (Fin.cons (Matrix.single ((Equiv.funUnique (Fin 1) ι).symm u 0) r 1)
          fun k : Fin (n + 1) =>
            homotopyCoordLinearMap (R := R) r ((Equiv.funUnique (Fin 1) ι).symm u) k (b k)) =
      Function.update b 0 ((Matrix.single u r 1 * Matrix.single r u 1) * b 0) := by
    rw [← Fin.castSucc_zero, hochschildFace_castSucc]
    funext k
    cases k using Fin.cases with
    | zero =>
      simp only [Fin.contractNth, Fin.val_zero, Fin.castSucc_zero, lt_irrefl, ↓reduceIte,
        Fin.cons_zero, Fin.cons_succ, Function.update_self, homotopyCoordLinearMap_same,
        mul_assoc]
      rfl
    | succ k =>
      simp [Fin.contractNth, homotopyCoordLinearMap_of_gt r (Nat.succ_pos k)]
  simp_rw [h1, ← Ψ.map_update_sum, ← Finset.sum_mul, Matrix.single_mul_single_same, one_mul,
    Matrix.sum_single_one, one_mul, Function.update_eq_self]

/-- For `m < n`, rotating `S_{n, m + 1} (δ₀ Ψ)` once gives `(-1)ⁿ • S_{n, m} (δ_{n+1} Ψ)`. -/
private theorem cyclicOperator_homotopyStep_succ_hochschildCoface_zero (r : ι) {n m : ℕ}
    (hm : m < n) (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => Matrix ι ι A) M) :
    cyclicOperator R (Matrix ι ι A) M n
        (homotopyStep r n (m + 1) (hochschildCoface R (Matrix ι ι A) M 0 Ψ)) =
      (-1 : ℤ) ^ n •
        homotopyStep r n m (hochschildCoface R (Matrix ι ι A) M (Fin.last (n + 1)) Ψ) := by
  ext d
  simp only [cyclicOperator_apply, smul_apply]
  congr 1
  rw [homotopyStep_apply, homotopyStep_apply]
  simp only [hochschildCoface_apply]
  -- Split paths `p : Fin (m + 2) → ι` as `Fin.cons u q` and sum out the head index `u : ι`.
  rw [← (Fin.consEquiv (fun _ : Fin (m + 2) => ι)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  set c : Fin (n + 1) → Matrix ι ι A := d ∘ (finRotate (n + 1)).symm
  let base : Fin (n + 1) → Matrix ι ι A :=
    Fin.cons (c 0 * Matrix.single (q 0) r 1) fun k : Fin n =>
      homotopyCoordLinearMap (R := R) r q k (c k.succ)
  have hface (u : ι) :
      hochschildFace 0
        (Fin.cons (Matrix.single ((Fin.consEquiv (fun _ : Fin (m + 2) => ι) (u, q)) 0) r 1)
          fun k : Fin (n + 1) =>
            homotopyCoordLinearMap (R := R) r
              (Fin.consEquiv (fun _ : Fin (m + 2) => ι) (u, q)) k (c k)) =
      Function.update base 0
        (Matrix.single u r 1 * Matrix.single r r (c 0 u (q 0))) := by
    rw [← Fin.castSucc_zero, hochschildFace_castSucc]
    funext k
    cases k using Fin.cases with
    | zero =>
      simp only [Fin.consEquiv_apply, Fin.contractNth, Fin.val_zero, Fin.castSucc_zero, lt_irrefl,
        ↓reduceIte, Fin.cons_zero, Fin.cons_succ, Function.update_self]
      rw [homotopyCoordLinearMap_of_lt r (Nat.zero_lt_succ m) (Fin.cons u q)]
      rfl
    | succ k =>
      simp only [Fin.consEquiv_apply, Fin.contractNth, Fin.val_succ, Fin.castSucc_zero,
        Fin.val_zero, Nat.not_lt_zero, ↓reduceIte, Nat.succ_ne_zero, ne_eq, Fin.succ_ne_zero,
        Function.update_of_ne, not_false_eq_true, Fin.cons_succ]
      exact homotopyCoordLinearMap_cons_succ r u q k (c k.succ)
  have hsum : ∑ u : ι, Matrix.single u r (1 : A) * Matrix.single r r (c 0 u (q 0)) =
      c 0 * Matrix.single (q 0) r 1 := by
    have hmul (u : ι) : Matrix.single r r (c 0 u (q 0)) =
        Matrix.single r u (1 : A) * c 0 * Matrix.single (q 0) r (1 : A) := by
      simp
    simp_rw [hmul, ← mul_assoc, ← Finset.sum_mul, Matrix.single_mul_single_same, one_mul,
      Matrix.sum_single_one, one_mul]
  have hupd : Function.update base 0 (c 0 * Matrix.single (q 0) r 1) = base :=
    Function.update_eq_self_iff.2 rfl
  simp_rw [hface]
  rw [← Ψ.map_update_sum, hsum, hupd]
  -- Match `base` with `hochschildFace (Fin.last (n + 1))` using `c 0 = d (Fin.last n)` and `m < n`.
  congr 1
  rw [hochschildFace_last]
  have hc0 : c 0 = d (Fin.last n) :=
    congrArg d ((finRotate (n + 1)).symm_apply_eq.2 finRotate_last.symm)
  have hc_succ (k : Fin n) : c k.succ = d k.castSucc :=
    congrArg d ((finRotate (n + 1)).symm_apply_eq.2 (Fin.finRotate_castSucc k).symm)
  dsimp only [base]
  funext j
  cases j using Fin.cases with
  | zero =>
    rw [Fin.cons_zero, Fin.cons_zero, ← Fin.succ_last, Fin.cons_succ, Fin.cons_zero,
      Fin.val_last, homotopyCoordLinearMap_of_gt r hm, hc0]
  | succ k =>
    rw [Fin.cons_succ, Fin.cons_succ, Fin.cons_succ, Fin.val_castSucc, hc_succ]

/-- At `m = n`, `S_{n, n} (δ_{n+1} Ψ)` is the rotated matrix extension of `Ψ ∘ E_{rr}` up to
sign. -/
private theorem homotopyStep_self_hochschildCoface_last (r : ι) (n : ℕ)
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => Matrix ι ι A) M) :
    homotopyStep r n n (hochschildCoface R (Matrix ι ι A) M (Fin.last (n + 1)) Ψ) =
      (-1 : ℤ) ^ n •
        cyclicOperator R (Matrix ι ι A) M n
          (matrixCochainExtension ι n (matrixCornerRestriction r n Ψ)) := by
  ext d
  simp only [smul_apply, cyclicOperator_apply, smul_smul]
  rw [← pow_add, ← two_mul n, pow_mul, neg_one_sq, one_pow, one_smul,
    homotopyStep_apply, matrixCochainExtension_apply]
  simp only [hochschildCoface_apply, matrixCornerRestriction_apply]
  conv_rhs => rw [← (Equiv.arrowCongr (finRotate (n + 1)) (Equiv.refl ι)).sum_comp]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  rw [hochschildFace_last]
  have hrot0 : (finRotate (n + 1)).symm 0 = Fin.last n :=
    (finRotate (n + 1)).symm_apply_eq.2 finRotate_last.symm
  have hrot_succ (k : Fin n) : (finRotate (n + 1)).symm k.succ = k.castSucc :=
    (finRotate (n + 1)).symm_apply_eq.2 (Fin.finRotate_castSucc k).symm
  funext j
  cases j using Fin.cases with
  | zero =>
    simp only [Fin.cons_zero, ← Fin.succ_last, Fin.cons_succ, Fin.val_last,
      homotopyCoordLinearMap_same, Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply,
      hrot0, Equiv.symm_apply_apply]
    have hp : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n := rfl
    rw [hp, Matrix.single_mul_mul_single, one_mul, mul_one]
  | succ k =>
    simp only [Fin.cons_succ, Fin.val_castSucc, Equiv.arrowCongr_apply, Equiv.refl_apply,
      Function.comp_apply, hrot_succ, Equiv.symm_apply_apply]
    rw [homotopyCoordLinearMap_of_lt r k.isLt]
    rfl

/-- For `i ≤ m'`, `S_{k+1, m'+1}` intertwines `δ_{i+1}` with `δ_i ∘ S_{k, m'}`. -/
private theorem homotopyStep_succ_hochschildCoface_succ_of_le (r : ι) {k m' : ℕ}
    (i : Fin (k + 1)) (hi : (i : ℕ) ≤ m')
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) => Matrix ι ι A) M) :
    homotopyStep r (k + 1) (m' + 1)
        (hochschildCoface R (Matrix ι ι A) M i.succ.castSucc Ψ) =
      hochschildCoface R (Matrix ι ι A) M i.castSucc (homotopyStep r k m' Ψ) := by
  ext b
  rw [homotopyStep_apply, hochschildCoface_apply, homotopyStep_apply]
  simp only [hochschildCoface_apply]
  -- Decompose `p : Fin (m' + 2) → ι` by inserting the intermediate matrix index `u` at `i + 1`.
  let idx : Fin (m' + 2) := ⟨(i : ℕ) + 1, by omega⟩
  rw [← (Fin.insertNthEquiv (fun _ : Fin (m' + 2) => ι) idx).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  let target : Fin (k + 2) → Matrix ι ι A :=
    Fin.cons (Matrix.single (q 0) r 1) fun j : Fin (k + 1) =>
      homotopyCoordLinearMap (R := R) r q j (hochschildFace i.castSucc b j)
  have hp0 (u : ι) :
      (Fin.insertNth idx u q : Fin (m' + 2) → ι) 0 = q 0 := by
    have h0 : (0 : Fin (m' + 2)) = idx.succAbove 0 := by ext; simp [idx]
    rw [h0, Fin.insertNth_apply_succAbove]
  have hbelow (u : ι) {s : ℕ} (hs : s ≤ i) (hs' : s < m' + 2) :
      (Fin.insertNth idx u q : Fin (m' + 2) → ι) ⟨s, hs'⟩ = q ⟨s, by omega⟩ := by
    have heq : (⟨s, hs'⟩ : Fin (m' + 2)) = idx.succAbove ⟨s, by omega⟩ := by
      ext; simp only [Fin.val_succAbove, idx]; split_ifs <;> omega
    rw [heq, Fin.insertNth_apply_succAbove]
  have habove (u : ι) {s : ℕ} (hs : (i : ℕ) < s) (hs' : s + 1 < m' + 2) :
      (Fin.insertNth idx u q : Fin (m' + 2) → ι) ⟨s + 1, hs'⟩ = q ⟨s, by omega⟩ := by
    have heq : (⟨s + 1, hs'⟩ : Fin (m' + 2)) = idx.succAbove ⟨s, by omega⟩ := by
      ext
      simp only [Fin.val_succAbove, idx]
      split_ifs <;> omega
    rw [heq, Fin.insertNth_apply_succAbove]
  have hsame (u : ι) :
      (Fin.insertNth idx u q : Fin (m' + 2) → ι) ⟨(i : ℕ) + 1, by omega⟩ = u :=
    Fin.insertNth_apply_same (α := fun _ => ι) idx u q
  -- Off slot `i + 1`, the contracted arguments match `target`; at `i + 1` they equal `term u`.
  let term (u : ι) : Matrix ι ι A :=
    homotopyCoordLinearMap (R := R) r (Fin.insertNth idx u q) i (b i.castSucc) *
      homotopyCoordLinearMap (R := R) r (Fin.insertNth idx u q) ((i : ℕ) + 1) (b i.succ)
  have hface (u : ι) :
      hochschildFace i.succ.castSucc
        (Fin.cons (Matrix.single
            ((Fin.insertNthEquiv (fun _ : Fin (m' + 2) => ι) idx (u, q)) 0) r 1)
          fun j : Fin (k + 2) =>
            homotopyCoordLinearMap (R := R) r
              (Fin.insertNthEquiv (fun _ : Fin (m' + 2) => ι) idx (u, q)) j (b j)) =
      Function.update target i.succ (term u) := by
    simp only [Fin.insertNthEquiv_apply]
    rw [hochschildFace_succ_castSucc_cons, hp0]
    funext j
    cases j using Fin.cases with
    | zero =>
      rw [Function.update_of_ne (Fin.succ_ne_zero i).symm]
      simp [target]
    | succ j =>
      simp only [Fin.cons_succ, target]
      by_cases hji : j = i
      · subst hji
        simp [hochschildFace_castSucc, Fin.contractNth, term]
      · have hjne : j.succ ≠ i.succ := (Fin.succ_injective _).ne hji
        rw [Function.update_of_ne hjne, Fin.cons_succ]
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hji) with hlt | hgt
        · have hface_lt (a : Fin (k + 2) → Matrix ι ι A) :
              hochschildFace i.castSucc a j = a j.castSucc := by
            simp [hochschildFace_castSucc, Fin.contractNth, Fin.val_castSucc, hlt]
          rw [hface_lt, hface_lt, Fin.val_castSucc,
            homotopyCoordLinearMap_of_lt r (by omega),
            homotopyCoordLinearMap_of_lt r (by omega),
            hbelow u (by omega) (by omega), hbelow u (by omega) (by omega)]
        · have h1 : ¬(j : ℕ) < (i : ℕ) := by omega
          have h2 : (j : ℕ) ≠ (i : ℕ) := by omega
          have hface_gt (a : Fin (k + 2) → Matrix ι ι A) :
              hochschildFace i.castSucc a j = a j.succ := by
            simp [hochschildFace_castSucc, Fin.contractNth, Fin.val_castSucc, h1, h2]
          rw [hface_gt, hface_gt, Fin.val_succ]
          by_cases hjm : (j : ℕ) < m'
          · rw [homotopyCoordLinearMap_of_lt r (by omega),
              homotopyCoordLinearMap_of_lt r hjm,
              habove u hgt (by omega), habove u (by omega) (by omega)]
          · by_cases hjeq : (j : ℕ) = m'
            · subst hjeq
              rw [homotopyCoordLinearMap_same, homotopyCoordLinearMap_same,
                habove u hgt (by omega)]
            · rw [homotopyCoordLinearMap_of_gt r (by omega),
                homotopyCoordLinearMap_of_gt r (by omega)]
  -- Summing `term u` over the intermediate index `u : ι` multiplies `b i.castSucc` and `b i.succ`.
  have hsum : ∑ u : ι, term u = target i.succ := by
    have htar : target i.succ =
        homotopyCoordLinearMap (R := R) r q i (b i.castSucc * b i.succ) := by
      simp [target, hochschildFace_castSucc, Fin.contractNth]
    rw [htar]
    rcases lt_or_eq_of_le hi with hlt | heq
    · have hterm (u : ι) : term u =
          Matrix.single r r
            (b i.castSucc (q ⟨i, by omega⟩) u * b i.succ u (q ⟨(i : ℕ) + 1, by omega⟩)) := by
        simp only [term]
        rw [homotopyCoordLinearMap_of_lt r (by omega),
          homotopyCoordLinearMap_of_lt r (by omega),
          hbelow u le_rfl (by omega), hsame u, habove u (Nat.lt_succ_self i) (by omega),
          Matrix.single_mul_single_same]
      simp_rw [hterm, ← Matrix.singleAddMonoidHom_apply, ← map_sum,
        Matrix.singleAddMonoidHom_apply, ← Matrix.mul_apply,
        homotopyCoordLinearMap_of_lt r hlt]
    · subst heq
      have hterm (u : ι) : term u =
          (Matrix.single r (q ⟨i, by omega⟩) (1 : A) * b i.castSucc *
            Matrix.single u u (1 : A)) * b i.succ := by
        simp only [term]
        rw [homotopyCoordLinearMap_of_lt r (Nat.lt_succ_self _),
          homotopyCoordLinearMap_same, hbelow u le_rfl (by omega), hsame u,
          ← mul_assoc, Matrix.single_mul_single_same, mul_one,
          Matrix.single_mul_mul_single, one_mul, mul_one]
      simp_rw [hterm, ← Finset.sum_mul, ← Finset.mul_sum, Matrix.sum_single_one, mul_one,
        mul_assoc, homotopyCoordLinearMap_same]
  simp_rw [hface]
  rw [← Ψ.map_update_sum, hsum, Function.update_eq_self]

/-- For `m ≤ i`, `S_{k+1, m}` intertwines `δ_{i+1}` with `δ_i ∘ S_{k, m}` pathwise. -/
private theorem homotopyStep_hochschildCoface_succ_of_le (r : ι) {k m : ℕ}
    (i : Fin (k + 1)) (hm : m ≤ (i : ℕ))
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) => Matrix ι ι A) M) :
    homotopyStep r (k + 1) m
        (hochschildCoface R (Matrix ι ι A) M i.succ.castSucc Ψ) =
      hochschildCoface R (Matrix ι ι A) M i.castSucc (homotopyStep r k m Ψ) := by
  ext b
  rw [homotopyStep_apply, hochschildCoface_apply, homotopyStep_apply]
  simp only [hochschildCoface_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  rw [hochschildFace_succ_castSucc_cons]
  congr 1
  funext j
  by_cases hji : j = i
  · subst hji
    simp only [hochschildFace_castSucc, Fin.contractNth, Fin.val_castSucc, lt_irrefl, ↓reduceIte,
      Fin.val_succ]
    rw [homotopyCoordLinearMap_of_gt r (k := (j : ℕ) + 1) (by omega)]
    rcases eq_or_lt_of_le hm with rfl | hlt
    · rw [homotopyCoordLinearMap_same, homotopyCoordLinearMap_same, mul_assoc]
    · rw [homotopyCoordLinearMap_of_gt r hlt, homotopyCoordLinearMap_of_gt r hlt]
  · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hji) with hlt | hgt
    · simp [hochschildFace_castSucc, Fin.contractNth, Fin.val_castSucc, hlt]
    · have h1 : ¬(j : ℕ) < (i : ℕ) := by omega
      have h2 : (j : ℕ) ≠ (i : ℕ) := by omega
      simp only [hochschildFace_castSucc, Fin.contractNth, Fin.val_castSucc, h1, h2, ↓reduceIte,
        Fin.val_succ]
      rw [homotopyCoordLinearMap_of_gt r (by omega), homotopyCoordLinearMap_of_gt r (by omega)]

/-- The explicit Hochschild cochain homotopy
`hₙ = ∑_{m = 0}^n λₙ^m ∘ S_{n, m} : C^{n+1}(Matrix ι ι A; M) →ₗ[R] C^n(Matrix ι ι A; M)`
witnessing matrix Morita invariance between the identity and corner restriction followed by matrix
extension. -/
noncomputable def matrixHochschildHomotopy (r : ι) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) => Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => Matrix ι ι A) M :=
  ∑ m ∈ Finset.range (n + 1),
    (cyclicOperator R (Matrix ι ι A) M n ^ m) ∘ₗ homotopyStep r n m

/-- In degree zero, `h₀ (b₀ Ψ) = Ψ - (Ψ ∘ E_{rr})#Tr`. -/
theorem matrixHochschildHomotopy_hochschildCoboundary_zero (r : ι)
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 => Matrix ι ι A) M) :
    matrixHochschildHomotopy r 0 (hochschildCoboundary R (Matrix ι ι A) M 0 Ψ) =
      Ψ - matrixCochainExtension ι 0 (matrixCornerRestriction r 0 Ψ) := by
  have hcob : hochschildCoboundary R (Matrix ι ι A) M 0 Ψ =
      hochschildCoface R (Matrix ι ι A) M 0 Ψ -
        hochschildCoface R (Matrix ι ι A) M (Fin.last 1) Ψ := by
    ext a
    rw [hochschildCoboundary_apply, Fin.sum_univ_two]
    simp [Fin.last, sub_eq_add_neg]
  have hlam : cyclicOperator R (Matrix ι ι A) M 0 = 1 := by
    simpa only [zero_add, pow_one] using cyclicOperator_pow_eq_one (R := R) (A := Matrix ι ι A)
      (M := M) 0
  rw [matrixHochschildHomotopy, Finset.range_one, Finset.sum_singleton, pow_zero, hcob, map_sub,
    LinearMap.comp_apply, LinearMap.comp_apply, _root_.one_apply_eq_self,
    _root_.one_apply_eq_self, homotopyStep_zero_hochschildCoface_zero,
    homotopyStep_self_hochschildCoface_last, pow_zero, one_smul, hlam, _root_.one_apply_eq_self]

/-- Every `M`-valued trace on `Matrix ι ι A` (Hochschild `0`-cocycle) is the matrix extension of
its restriction to any diagonal corner. -/
theorem matrixCochainExtension_matrixCornerRestriction_of_mem_hochschildCocycles_zero (r : ι)
    {Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 => Matrix ι ι A) M}
    (hΨ : Ψ ∈ hochschildCocycles R (Matrix ι ι A) M 0) :
    matrixCochainExtension ι 0 (matrixCornerRestriction r 0 Ψ) = Ψ := by
  have h := matrixHochschildHomotopy_hochschildCoboundary_zero r Ψ
  rw [mem_hochschildCocycles_iff.1 hΨ, map_zero, eq_comm, sub_eq_zero] at h
  exact h.symm

private theorem matrixHochschildHomotopy_hochschildCoface_zero (r : ι) (k : ℕ)
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) => Matrix ι ι A) M) :
    matrixHochschildHomotopy r (k + 1) (hochschildCoface R (Matrix ι ι A) M 0 Ψ) =
      Ψ + ∑ m ∈ Finset.range (k + 1),
        (-1 : ℤ) ^ (k + 1) • (cyclicOperator R (Matrix ι ι A) M (k + 1) ^ m)
          (homotopyStep r (k + 1) m
            (hochschildCoface R (Matrix ι ι A) M (Fin.last (k + 2)) Ψ)) := by
  rw [matrixHochschildHomotopy, LinearMap.sum_apply, Finset.sum_range_succ',
    pow_zero, LinearMap.comp_apply, _root_.one_apply_eq_self,
    homotopyStep_zero_hochschildCoface_zero, add_comm _ Ψ, add_right_inj]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [LinearMap.comp_apply, pow_succ _ m, _root_.mul_apply_eq_comp,
    cyclicOperator_homotopyStep_succ_hochschildCoface_zero r (Finset.mem_range.1 hm), map_zsmul]

private theorem matrixHochschildHomotopy_zsmul_hochschildCoface_last (r : ι) (k : ℕ)
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) => Matrix ι ι A) M) :
    matrixHochschildHomotopy r (k + 1)
        ((-1 : ℤ) ^ (k + 2) • hochschildCoface R (Matrix ι ι A) M (Fin.last (k + 2)) Ψ) =
      -(∑ m ∈ Finset.range (k + 1),
          (-1 : ℤ) ^ (k + 1) • (cyclicOperator R (Matrix ι ι A) M (k + 1) ^ m)
            (homotopyStep r (k + 1) m
              (hochschildCoface R (Matrix ι ι A) M (Fin.last (k + 2)) Ψ))) -
        matrixCochainExtension ι (k + 1) (matrixCornerRestriction r (k + 1) Ψ) := by
  rw [map_zsmul, matrixHochschildHomotopy, LinearMap.sum_apply, Finset.sum_range_succ, smul_add]
  have hmid : (-1 : ℤ) ^ (k + 2) •
        (∑ m ∈ Finset.range (k + 1),
          ((cyclicOperator R (Matrix ι ι A) M (k + 1) ^ m) ∘ₗ
            homotopyStep r (k + 1) m)
            (hochschildCoface R (Matrix ι ι A) M (Fin.last (k + 2)) Ψ)) =
      -(∑ m ∈ Finset.range (k + 1),
          (-1 : ℤ) ^ (k + 1) • (cyclicOperator R (Matrix ι ι A) M (k + 1) ^ m)
            (homotopyStep r (k + 1) m
              (hochschildCoface R (Matrix ι ι A) M (Fin.last (k + 2)) Ψ))) := by
    rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [LinearMap.comp_apply, pow_succ (-1 : ℤ), mul_neg_one, neg_smul]
  have hpow : k + 2 + (k + 1) = 2 * (k + 1) + 1 := by omega
  have htop : (-1 : ℤ) ^ (k + 2) •
        (((cyclicOperator R (Matrix ι ι A) M (k + 1) ^ (k + 1)) ∘ₗ
            homotopyStep r (k + 1) (k + 1))
          (hochschildCoface R (Matrix ι ι A) M (Fin.last (k + 2)) Ψ)) =
      -matrixCochainExtension ι (k + 1) (matrixCornerRestriction r (k + 1) Ψ) := by
    rw [LinearMap.comp_apply, homotopyStep_self_hochschildCoface_last, map_zsmul,
      ← _root_.mul_apply_eq_comp, ← pow_succ, cyclicOperator_pow_eq_one,
      _root_.one_apply_eq_self, smul_smul, ← pow_add, hpow, pow_succ, pow_mul, neg_one_sq,
      one_pow, one_mul, neg_one_smul]
  rw [hmid, htop, sub_eq_add_neg]

private theorem matrixHochschildHomotopy_sum_hochschildCoface_succ_add_hochschildCoboundary
    (r : ι) (k : ℕ) (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) => Matrix ι ι A) M) :
    matrixHochschildHomotopy r (k + 1)
        (∑ i : Fin (k + 1),
          (-1 : ℤ) ^ ((i : ℕ) + 1) • hochschildCoface R (Matrix ι ι A) M i.succ.castSucc Ψ) +
      hochschildCoboundary R (Matrix ι ι A) M k (matrixHochschildHomotopy r k Ψ) = 0 := by
  have hsplit (m : ℕ) :
      (((cyclicOperator R (Matrix ι ι A) M (k + 1) ^ m) ∘ₗ homotopyStep r (k + 1) m)
          (∑ x : Fin (k + 1),
            (-1 : ℤ) ^ ((x : ℕ) + 1) •
              hochschildCoface R (Matrix ι ι A) M x.succ.castSucc Ψ)) =
        (∑ i ∈ Finset.univ.filter (fun i : Fin (k + 1) => m ≤ (i : ℕ)),
            (-1 : ℤ) ^ ((i : ℕ) + 1) • (cyclicOperator R (Matrix ι ι A) M (k + 1) ^ m)
              (hochschildCoface R (Matrix ι ι A) M i.castSucc (homotopyStep r k m Ψ))) +
          (∑ i ∈ Finset.univ.filter (fun i : Fin (k + 1) => (i : ℕ) < m),
            (-1 : ℤ) ^ ((i : ℕ) + 1) • (cyclicOperator R (Matrix ι ι A) M (k + 1) ^ m)
              (homotopyStep r (k + 1) m
                (hochschildCoface R (Matrix ι ι A) M i.succ.castSucc Ψ))) := by
    rw [map_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin (k + 1) => m ≤ (i : ℕ))]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [LinearMap.comp_apply, map_zsmul, map_zsmul,
        homotopyStep_hochschildCoface_succ_of_le r i (Finset.mem_filter.1 hi).2]
    · refine Finset.sum_congr (by ext i; simp [not_le]) fun i _ => ?_
      rw [LinearMap.comp_apply, map_zsmul, map_zsmul]
  have hA : (∑ m ∈ Finset.range (k + 2),
        ∑ i ∈ Finset.univ.filter (fun i : Fin (k + 1) => m ≤ (i : ℕ)),
          (-1 : ℤ) ^ ((i : ℕ) + 1) • (cyclicOperator R (Matrix ι ι A) M (k + 1) ^ m)
            (hochschildCoface R (Matrix ι ι A) M i.castSucc (homotopyStep r k m Ψ))) =
      ∑ m ∈ Finset.range (k + 1),
        ∑ i ∈ Finset.univ.filter (fun i : Fin (k + 1) => m ≤ (i : ℕ)),
          (-1 : ℤ) ^ ((i : ℕ) + 1) • (cyclicOperator R (Matrix ι ι A) M (k + 1) ^ m)
            (hochschildCoface R (Matrix ι ι A) M i.castSucc (homotopyStep r k m Ψ)) := by
    rw [Finset.sum_range_succ]
    have hemp : (Finset.univ.filter fun i : Fin (k + 1) => k + 1 ≤ (i : ℕ)) = ∅ := by
      ext i; simp; omega
    rw [hemp, Finset.sum_empty, add_zero]
  have hB : (∑ m ∈ Finset.range (k + 2),
        ∑ i ∈ Finset.univ.filter (fun i : Fin (k + 1) => (i : ℕ) < m),
          (-1 : ℤ) ^ ((i : ℕ) + 1) • (cyclicOperator R (Matrix ι ι A) M (k + 1) ^ m)
            (homotopyStep r (k + 1) m
              (hochschildCoface R (Matrix ι ι A) M i.succ.castSucc Ψ))) =
      ∑ m ∈ Finset.range (k + 1),
        ∑ i ∈ Finset.univ.filter (fun i : Fin (k + 1) => (i : ℕ) ≤ m),
          (-1 : ℤ) ^ ((i : ℕ) + 1) • (cyclicOperator R (Matrix ι ι A) M (k + 1) ^ (m + 1))
            (hochschildCoface R (Matrix ι ι A) M i.castSucc (homotopyStep r k m Ψ)) := by
    rw [Finset.sum_range_succ']
    have hemp : (Finset.univ.filter fun i : Fin (k + 1) => (i : ℕ) < 0) = ∅ := by
      ext i; simp
    rw [hemp, Finset.sum_empty, add_zero]
    refine Finset.sum_congr rfl fun m _ => ?_
    refine Finset.sum_congr (by ext i; simp) fun i hi => ?_
    rw [homotopyStep_succ_hochschildCoface_succ_of_le r i (Finset.mem_filter.1 hi).2]
  rw [matrixHochschildHomotopy, LinearMap.sum_apply, matrixHochschildHomotopy, LinearMap.sum_apply,
    map_sum]
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [hA, hB, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [LinearMap.comp_apply]
  exact sum_filter_cyclicOperator_pow_hochschildCoface_add_hochschildCoboundary
    (Nat.le_of_lt_succ (Finset.mem_range.1 hm)) (homotopyStep r k m Ψ)

/-- In positive degree `k + 1`, the Hochschild cochain homotopy satisfies
`h_{k+1} (b_{k+1} Ψ) + b_k (h_k Ψ) = Ψ - (Ψ ∘ E_{rr})#Tr`. -/
theorem matrixHochschildHomotopy_hochschildCoboundary_succ (r : ι) (k : ℕ)
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) => Matrix ι ι A) M) :
    matrixHochschildHomotopy r (k + 1) (hochschildCoboundary R (Matrix ι ι A) M (k + 1) Ψ) +
        hochschildCoboundary R (Matrix ι ι A) M k (matrixHochschildHomotopy r k Ψ) =
      Ψ - matrixCochainExtension ι (k + 1) (matrixCornerRestriction r (k + 1) Ψ) := by
  have hcob : hochschildCoboundary R (Matrix ι ι A) M (k + 1) Ψ =
      (hochschildCoface R (Matrix ι ι A) M 0 Ψ +
        ∑ i : Fin (k + 1),
          (-1 : ℤ) ^ ((i : ℕ) + 1) • hochschildCoface R (Matrix ι ι A) M i.succ.castSucc Ψ) +
        (-1 : ℤ) ^ (k + 2) • hochschildCoface R (Matrix ι ι A) M (Fin.last (k + 2)) Ψ := by
    ext a
    rw [hochschildCoboundary_apply, Fin.sum_univ_castSucc, Fin.sum_univ_succ]
    simp [Fin.castSucc_zero]
  rw [hcob, map_add, map_add, matrixHochschildHomotopy_hochschildCoface_zero,
    matrixHochschildHomotopy_zsmul_hochschildCoface_last]
  calc
    (Ψ + ∑ m ∈ Finset.range (k + 1),
          (-1 : ℤ) ^ (k + 1) • (cyclicOperator R (Matrix ι ι A) M (k + 1) ^ m)
            (homotopyStep r (k + 1) m
              (hochschildCoface R (Matrix ι ι A) M (Fin.last (k + 2)) Ψ)) +
        matrixHochschildHomotopy r (k + 1)
          (∑ i : Fin (k + 1),
            (-1 : ℤ) ^ ((i : ℕ) + 1) •
              hochschildCoface R (Matrix ι ι A) M i.succ.castSucc Ψ) +
        (-(∑ m ∈ Finset.range (k + 1),
            (-1 : ℤ) ^ (k + 1) • (cyclicOperator R (Matrix ι ι A) M (k + 1) ^ m)
              (homotopyStep r (k + 1) m
                (hochschildCoface R (Matrix ι ι A) M (Fin.last (k + 2)) Ψ))) -
          matrixCochainExtension ι (k + 1) (matrixCornerRestriction r (k + 1) Ψ))) +
        hochschildCoboundary R (Matrix ι ι A) M k (matrixHochschildHomotopy r k Ψ) =
      (Ψ - matrixCochainExtension ι (k + 1) (matrixCornerRestriction r (k + 1) Ψ)) +
        (matrixHochschildHomotopy r (k + 1)
            (∑ i : Fin (k + 1),
              (-1 : ℤ) ^ ((i : ℕ) + 1) •
                hochschildCoface R (Matrix ι ι A) M i.succ.castSucc Ψ) +
          hochschildCoboundary R (Matrix ι ι A) M k (matrixHochschildHomotopy r k Ψ)) := by
      abel
    _ = Ψ - matrixCochainExtension ι (k + 1) (matrixCornerRestriction r (k + 1) Ψ) := by
      rw [matrixHochschildHomotopy_sum_hochschildCoface_succ_add_hochschildCoboundary, add_zero]

end Step

end Homotopy

/-! ### Matrix Morita invariance on Hochschild cohomology -/

namespace hochschildCohomology

section NonUnital

variable {R A M ι : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [Fintype ι] {n : ℕ}

variable (M ι n) in
/-- Matrix extension `HHⁿ(A, Hom_R(A, M)) →ₗ[R] HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M))` on
Hochschild cohomology induced by `matrixCochainExtension`. -/
noncomputable def matrixExtension :
    hochschildCohomology R A M n →ₗ[R] hochschildCohomology R (Matrix ι ι A) M n :=
  desc n (mk R (Matrix ι ι A) M n ∘ₗ
      (matrixCochainExtension ι n).restrict fun _ => matrixCochainExtension_mem_hochschildCocycles)
    fun _ hφ => (mk_eq_zero_iff R (Matrix ι ι A) M n _).2
      (matrixCochainExtension_mem_hochschildCoboundaries hφ)

/-- Matrix extension on Hochschild cohomology sends the class of a cocycle `φ` to the class of
`φ#Tr`. -/
@[simp]
theorem matrixExtension_mk (φ : hochschildCocycles R A M n) :
    matrixExtension M ι n (mk R A M n φ) =
      mk R (Matrix ι ι A) M n ⟨matrixCochainExtension ι n φ,
        matrixCochainExtension_mem_hochschildCocycles φ.2⟩ :=
  desc_mk _ _ _ φ

variable (M n) in
/-- Diagonal corner restriction
`HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M)) →ₗ[R] HHⁿ(A, Hom_R(A, M))` on Hochschild cohomology
induced by `matrixCornerRestriction`. -/
noncomputable def cornerRestriction [DecidableEq ι] (r : ι) :
    hochschildCohomology R (Matrix ι ι A) M n →ₗ[R] hochschildCohomology R A M n :=
  desc n (mk R A M n ∘ₗ
      (matrixCornerRestriction r n).restrict
        fun _ => matrixCornerRestriction_mem_hochschildCocycles r)
    fun _ hΦ => (mk_eq_zero_iff R A M n _).2
      (matrixCornerRestriction_mem_hochschildCoboundaries r hΦ)

/-- Corner restriction on Hochschild cohomology sends the class of `Φ` to the class of
`Φ ∘ E_{rr}`. -/
@[simp]
theorem cornerRestriction_mk [DecidableEq ι] (r : ι)
    (Φ : hochschildCocycles R (Matrix ι ι A) M n) :
    cornerRestriction M n r (mk R (Matrix ι ι A) M n Φ) =
      mk R A M n ⟨matrixCornerRestriction r n Φ,
        matrixCornerRestriction_mem_hochschildCocycles r Φ.2⟩ :=
  desc_mk _ _ _ Φ

/-- Corner restriction is a left inverse to matrix extension on Hochschild cohomology, even for
nonunital algebras. -/
@[simp]
theorem cornerRestriction_matrixExtension [DecidableEq ι] (r : ι)
    (c : hochschildCohomology R A M n) :
    cornerRestriction M n r (matrixExtension M ι n c) = c := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  simp only [matrixExtension_mk, cornerRestriction_mk]
  congr 1
  ext x
  exact matrixCochainExtension_single ι r n φ.1 x

/-- Corner restriction composed with matrix extension is the identity on Hochschild cohomology. -/
@[simp]
theorem cornerRestriction_comp_matrixExtension [DecidableEq ι] (r : ι) :
    cornerRestriction (R := R) (A := A) M n r ∘ₗ matrixExtension M ι n = LinearMap.id :=
  LinearMap.ext (cornerRestriction_matrixExtension r)

/-- Matrix extension on Hochschild cohomology is injective for every nonempty finite index type,
even when `A` is nonunital. -/
theorem matrixExtension_injective [Nonempty ι] :
    Function.Injective (matrixExtension (R := R) (A := A) M ι n) := by
  classical
  obtain ⟨r⟩ := ‹Nonempty ι›
  exact Function.LeftInverse.injective (cornerRestriction_matrixExtension r)

end NonUnital

section Unital

variable {R A M ι : Type*} [CommRing R] [Semiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [Fintype ι] {n : ℕ}

/-- When `A` is unital, matrix extension is a left inverse to corner restriction on Hochschild
cohomology: `(Φ ∘ E_{rr})#Tr` represents the same cohomology class as `Φ`. -/
@[simp]
theorem matrixExtension_cornerRestriction [DecidableEq ι] (r : ι)
    (c : hochschildCohomology R (Matrix ι ι A) M n) :
    matrixExtension M ι n (cornerRestriction M n r c) = c := by
  obtain ⟨Φ, rfl⟩ := mk_surjective R (Matrix ι ι A) M n c
  rw [cornerRestriction_mk, matrixExtension_mk, mk_eq_mk_iff]
  dsimp only
  cases n with
  | zero =>
    have h := matrixCochainExtension_matrixCornerRestriction_of_mem_hochschildCocycles_zero r Φ.2
    rw [hochschildCoboundaries_zero, Submodule.mem_bot, h, sub_self]
  | succ k =>
    have h := matrixHochschildHomotopy_hochschildCoboundary_succ r k Φ.1
    rw [mem_hochschildCocycles_iff.1 Φ.2, map_zero, zero_add] at h
    refine mem_hochschildCoboundaries_succ_iff.2 ⟨-matrixHochschildHomotopy r k Φ.1, ?_⟩
    rw [map_neg, h, neg_sub]

/-- Matrix extension composed with corner restriction is the identity on Hochschild cohomology of
`Matrix ι ι A` when `A` is unital. -/
@[simp]
theorem matrixExtension_comp_cornerRestriction [DecidableEq ι] (r : ι) :
    matrixExtension (R := R) (A := A) M ι n ∘ₗ cornerRestriction M n r = LinearMap.id :=
  LinearMap.ext (matrixExtension_cornerRestriction r)

/-- On Hochschild cohomology of a unital algebra, diagonal corner restriction is independent of the
chosen corner index. -/
theorem cornerRestriction_eq_cornerRestriction [DecidableEq ι] (r s : ι) :
    cornerRestriction (R := R) (A := A) M n r = cornerRestriction M n s := by
  refine LinearMap.ext fun c => ?_
  calc
    cornerRestriction M n r c =
        cornerRestriction M n r (matrixExtension M ι n (cornerRestriction M n s c)) := by
      rw [matrixExtension_cornerRestriction]
    _ = cornerRestriction M n s c := cornerRestriction_matrixExtension r _

/-- **Matrix Morita invariance of Hochschild cohomology.** For a unital `R`-algebra `A` over any
commutative ring `R` and any nonempty finite index type `ι`, matrix extension on Hochschild
cohomology is bijective in every degree. -/
theorem bijective_matrixExtension (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  classical
  obtain ⟨r⟩ := ‹Nonempty ι›
  exact ⟨Function.LeftInverse.injective (cornerRestriction_matrixExtension r),
    Function.RightInverse.surjective (matrixExtension_cornerRestriction r)⟩

/-- Diagonal corner restriction on Hochschild cohomology is bijective for a unital algebra. -/
theorem bijective_cornerRestriction [DecidableEq ι] (r : ι) (n : ℕ) :
    Function.Bijective (cornerRestriction (R := R) (A := A) M n r) :=
  ⟨Function.LeftInverse.injective (matrixExtension_cornerRestriction r),
    Function.RightInverse.surjective (cornerRestriction_matrixExtension r)⟩

variable (M ι n) in
/-- Matrix extension as a linear equivalence
`HHⁿ(A, Hom_R(A, M)) ≃ₗ[R] HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M))` for a unital algebra `A`
and a nonempty finite index type `ι`. -/
noncomputable def matrixExtensionEquiv [Nonempty ι] :
    hochschildCohomology R A M n ≃ₗ[R] hochschildCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension ι n)

/-- Applying `matrixExtensionEquiv` agrees with `matrixExtension`. -/
@[simp]
theorem matrixExtensionEquiv_apply [Nonempty ι] (c : hochschildCohomology R A M n) :
    matrixExtensionEquiv M ι n c = matrixExtension M ι n c :=
  (rfl)

/-- Converting `matrixExtensionEquiv` to a linear map recovers `matrixExtension`. -/
@[simp]
theorem toLinearMap_matrixExtensionEquiv [Nonempty ι] :
    (matrixExtensionEquiv (R := R) (A := A) M ι n :
      hochschildCohomology R A M n →ₗ[R] hochschildCohomology R (Matrix ι ι A) M n) =
      matrixExtension M ι n :=
  (rfl)

/-- The inverse of `matrixExtensionEquiv` agrees with restriction to any diagonal corner `r : ι`. -/
theorem matrixExtensionEquiv_symm_apply [DecidableEq ι] [Nonempty ι] (r : ι)
    (c : hochschildCohomology R (Matrix ι ι A) M n) :
    (matrixExtensionEquiv M ι n).symm c = cornerRestriction M n r c := by
  apply (matrixExtensionEquiv M ι n).injective
  simp

end Unital

end hochschildCohomology

end TauCeti

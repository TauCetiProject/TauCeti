/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.RingTheory.FilteredAlgebra.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# Differential operators of finite order

Let `A` be a commutative `R`-algebra and `M`, `N` modules over `A`. Grothendieck's algebraic
definition of differential operators uses only commutators with multiplication by elements of
`A`. For an `R`-linear map `D : M →ₗ[R] N` and `a : A`, the commutator
`smulCommutator R a D` is `x ↦ D (a • x) - a • D x`. The `R`-submodule
`differentialOperators R A M N m` of operators of order at most `m` is defined recursively:
order at most `0` means `A`-linear, and `D` has order at most `m + 1` when every commutator
`smulCommutator R a D` has order at most `m`.

For the algebra of smooth functions on a manifold acting on spaces of smooth sections of vector
bundles, this is the classical characterisation of linear differential operators of order at
most `m` by the vanishing of `(m + 1)`-fold commutators with multiplication by functions, and
the iterated commutator `[⋯[P, f], …, f]` with `m` copies of `f` is `m!` times the principal
symbol of `P` evaluated at `df`. This file develops the algebraic theory:

* `mem_differentialOperators_iff_forall_list_prod`: order at most `m` means that every
  `(m + 1)`-fold iterated commutator vanishes; the commutators with different elements commute
  (`smulCommutator_comm`).
* `differentialOperators_mono` and `comp_mem_differentialOperators`: the orders are increasing
  and add under composition, so the operators on `M` form a filtered ring
  (`SetLike.GradedMonoid`).
* `Derivation.mem_differentialOperators_one` and `differentialOperatorsOneEquiv`: an operator
  `D : A →ₗ[R] M` has order at most one exactly when `D = δ + (· • m)` for a derivation `δ` and
  `m : M`, and this splitting is unique, with `m = D 1`.
* `apply_mem_smul_top_of_mem_pow_smul_top`: an operator of order at most `m` sends
  `I ^ (m + 1) • M` into `I • N` for every ideal `I`, so the value of `D x` modulo `I` depends
  only on `x` modulo `I ^ (m + 1)`. For the vanishing ideal of a point this is the statement
  that a differential operator of order `m` factors through `m`-jets.
* `smulCommutator_pow_comp_of_mem`: the top iterated commutators of a composition multiply,
  `ad_a ^ (m + k) (P ∘ Q) = (m + k).choose m • (ad_a ^ m P ∘ ad_a ^ k Q)`. Dividing by
  factorials over a `ℚ`-algebra, this is multiplicativity of principal symbols.
* `derivative_comp_derivative_notMem_differentialOperators_one`: the second derivative on
  `R[X]` does not have order one when `2 ≠ 0` in `R`, since `[[∂², X], X] = 2`.

## References

* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, §§12, 19.
-/

public section

open Finset

namespace TauCeti

section

variable (R : Type*) {A M N O : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M]
  [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
  [AddCommGroup O] [Module A O] [Module R O] [IsScalarTower R A O]

/-! ### Commutators with scalar multiplication -/

/-- The commutator `x ↦ D (a • x) - a • D x` of an `R`-linear map `D : M →ₗ[R] N` with
multiplication by `a : A`, as an `R`-linear operator on `M →ₗ[R] N`. -/
def smulCommutator (a : A) : Module.End R (M →ₗ[R] N) where
  toFun D :=
    D ∘ₗ Algebra.lsmul R R M a - Algebra.lsmul R R N a ∘ₗ D
  map_add' D E := by ext; simp only [LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.comp_apply, Algebra.lsmul_coe, smul_add]; abel
  map_smul' r D := by ext; simp [smul_sub, smul_comm a r]

variable {R}

@[simp]
theorem smulCommutator_apply_apply (a : A) (D : M →ₗ[R] N) (x : M) :
    smulCommutator R a D x = D (a • x) - a • D x := by
  simp [smulCommutator]

/-- For endomorphisms, `smulCommutator R a` is the Lie bracket with multiplication by `a` in the
associative algebra `Module.End R N`. -/
theorem smulCommutator_eq_lie (a : A) (D : Module.End R N) :
    smulCommutator R a D = ⁅D, Algebra.lsmul R R N a⁆ := by
  ext x
  simp [Ring.lie_def]

theorem apply_smul_eq_smulCommutator_add (a : A) (D : M →ₗ[R] N) (x : M) :
    D (a • x) = smulCommutator R a D x + a • D x := by
  simp

@[simp]
theorem smulCommutator_eq_zero_iff {a : A} {D : M →ₗ[R] N} :
    smulCommutator R a D = 0 ↔ ∀ x, D (a • x) = a • D x := by
  simp [LinearMap.ext_iff, sub_eq_zero]

@[simp]
theorem smulCommutator_zero : smulCommutator R (0 : A) = (0 : Module.End R (M →ₗ[R] N)) := by
  ext; simp

theorem smulCommutator_add (a b : A) :
    smulCommutator R (a + b) = (smulCommutator R a + smulCommutator R b :
      Module.End R (M →ₗ[R] N)) := by
  ext D x; simp only [smulCommutator_apply_apply, add_smul, map_add, LinearMap.add_apply]; abel

@[simp]
theorem smulCommutator_algebraMap (r : R) :
    smulCommutator R (algebraMap R A r) = (0 : Module.End R (M →ₗ[R] N)) := by
  ext; simp

@[simp]
theorem smulCommutator_one : smulCommutator R (1 : A) = (0 : Module.End R (M →ₗ[R] N)) := by
  simpa using smulCommutator_algebraMap (A := A) (M := M) (N := N) (1 : R)

/-- Commutators with multiplication by two elements commute: both iterated commutators equal
`x ↦ D ((a * b) • x) - a • D (b • x) - b • D (a • x) + (a * b) • D x`. -/
theorem smulCommutator_comm (a b : A) (D : M →ₗ[R] N) :
    smulCommutator R a (smulCommutator R b D) = smulCommutator R b (smulCommutator R a D) := by
  ext x
  simp only [smulCommutator_apply_apply, smul_sub, smul_smul, mul_comm a b]
  abel

theorem commute_smulCommutator (a b : A) :
    Commute (smulCommutator R a : Module.End R (M →ₗ[R] N)) (smulCommutator R b) :=
  LinearMap.ext fun D ↦ smulCommutator_comm a b D

/-- The commutator with a product: `[D, a * b] = a • [D, b] + b • [D, a] + [[D, a], b]`. -/
theorem smulCommutator_mul (a b : A) (D : M →ₗ[R] N) :
    smulCommutator R (a * b) D =
      a • smulCommutator R b D + b • smulCommutator R a D +
        smulCommutator R b (smulCommutator R a D) := by
  ext x
  simp only [smulCommutator_apply_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_sub,
    smul_smul, mul_comm b a]
  abel

/-- The Leibniz rule for commutators of a composition:
`[P ∘ Q, a] = P ∘ [Q, a] + [P, a] ∘ Q`. -/
theorem smulCommutator_comp (a : A) (P : N →ₗ[R] O) (Q : M →ₗ[R] N) :
    smulCommutator R a (P ∘ₗ Q) = P ∘ₗ smulCommutator R a Q + smulCommutator R a P ∘ₗ Q := by
  ext x
  simp only [smulCommutator_apply_apply, LinearMap.comp_apply, LinearMap.add_apply, map_sub]
  abel

/-- The general Leibniz rule for iterated commutators of a composition.

Adapted from `LieModule.toEnd_pow_lie` and `LieAlgebra.ad_pow_lie` in Mathlib. -/
theorem smulCommutator_pow_comp (a : A) (P : N →ₗ[R] O) (Q : M →ₗ[R] N) (n : ℕ) :
    (smulCommutator R a ^ n) (P ∘ₗ Q) =
      ∑ ij ∈ antidiagonal n,
        n.choose ij.1 • ((smulCommutator R a ^ ij.1) P ∘ₗ (smulCommutator R a ^ ij.2) Q) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_nsmul
      (fun i j ↦ (smulCommutator R a ^ i) P ∘ₗ (smulCommutator R a ^ j) Q) n]
    simp only [pow_succ', mul_apply_eq_comp, ih, map_sum, map_nsmul, smulCommutator_comp,
      nsmul_add, sum_add_distrib]
    congr 1
    refine sum_congr rfl fun ij hij ↦ ?_
    rw [Nat.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm]

/-! ### The order filtration -/

variable (R A M N) in
/-- The `R`-submodule of differential operators `M → N` of order at most `m`, in the sense of
Grothendieck: order at most `0` means commuting with multiplication by every `a : A`, and `D`
has order at most `m + 1` when every commutator `smulCommutator R a D` has order at most `m`. -/
def differentialOperators : ℕ → Submodule R (M →ₗ[R] N)
  | 0 => ⨅ a : A, LinearMap.ker (smulCommutator R a)
  | m + 1 => ⨅ a : A, (differentialOperators m).comap (smulCommutator R a)

theorem mem_differentialOperators_zero_iff_smulCommutator {D : M →ₗ[R] N} :
    D ∈ differentialOperators R A M N 0 ↔ ∀ a : A, smulCommutator R a D = 0 := by
  simp [differentialOperators, Submodule.mem_iInf]

/-- An operator has order at most `0` exactly when it is `A`-linear. -/
theorem mem_differentialOperators_zero_iff {D : M →ₗ[R] N} :
    D ∈ differentialOperators R A M N 0 ↔ ∀ (a : A) (x : M), D (a • x) = a • D x := by
  simp [mem_differentialOperators_zero_iff_smulCommutator]

theorem mem_differentialOperators_succ_iff {D : M →ₗ[R] N} {m : ℕ} :
    D ∈ differentialOperators R A M N (m + 1) ↔
      ∀ a : A, smulCommutator R a D ∈ differentialOperators R A M N m := by
  simp [differentialOperators, Submodule.mem_iInf]

theorem smulCommutator_mem_differentialOperators {D : M →ₗ[R] N} {m : ℕ}
    (hD : D ∈ differentialOperators R A M N (m + 1)) (a : A) :
    smulCommutator R a D ∈ differentialOperators R A M N m :=
  mem_differentialOperators_succ_iff.1 hD a

theorem smulCommutator_eq_zero_of_mem_differentialOperators_zero {D : M →ₗ[R] N}
    (hD : D ∈ differentialOperators R A M N 0) (a : A) : smulCommutator R a D = 0 :=
  mem_differentialOperators_zero_iff_smulCommutator.1 hD a

/-- An `A`-linear map is a differential operator of order `0`. -/
theorem _root_.LinearMap.restrictScalars_mem_differentialOperators_zero (f : M →ₗ[A] N) :
    f.restrictScalars R ∈ differentialOperators R A M N 0 :=
  mem_differentialOperators_zero_iff.2 fun a x ↦ by simp

theorem differentialOperators_le_succ (m : ℕ) :
    differentialOperators R A M N m ≤ differentialOperators R A M N (m + 1) := by
  induction m with
  | zero =>
    intro D hD
    rw [mem_differentialOperators_succ_iff]
    intro a
    rw [smulCommutator_eq_zero_of_mem_differentialOperators_zero hD a]
    exact zero_mem _
  | succ m ih =>
    intro D hD
    rw [mem_differentialOperators_succ_iff] at hD ⊢
    exact fun a ↦ ih (hD a)

theorem differentialOperators_mono : Monotone (differentialOperators R A M N) :=
  monotone_nat_of_le_succ differentialOperators_le_succ

/-- A differential operator has order at most `m` exactly when all its `(m + 1)`-fold iterated
commutators with multiplication by elements of `A` vanish. -/
theorem mem_differentialOperators_iff_forall_list_prod {D : M →ₗ[R] N} {m : ℕ} :
    D ∈ differentialOperators R A M N m ↔
      ∀ a : Fin (m + 1) → A, (List.ofFn fun i ↦ smulCommutator R (a i)).prod D = 0 := by
  induction m generalizing D with
  | zero =>
    rw [mem_differentialOperators_zero_iff_smulCommutator]
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
    exact ⟨fun h a ↦ h (a 0), fun h a ↦ h fun _ ↦ a⟩
  | succ m ih =>
    rw [mem_differentialOperators_succ_iff, Fin.forall_fin_succ_pi]
    refine forall_congr' fun c ↦ ?_
    rw [ih]
    refine forall_congr' fun v ↦ ?_
    have hc : Commute (smulCommutator R c : Module.End R (M →ₗ[R] N))
        (List.ofFn fun i ↦ smulCommutator R (v i)).prod :=
      Commute.list_prod_right _ _ fun _ hb ↦ by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hb
        exact commute_smulCommutator _ _
    conv_rhs => rw [List.ofFn_succ, List.prod_cons]
    simp only [Fin.cons_zero, Fin.cons_succ, hc.eq, mul_apply_eq_comp]

theorem smulCommutator_pow_mem_differentialOperators {D : M →ₗ[R] N} {m j : ℕ}
    (hD : D ∈ differentialOperators R A M N (m + j)) (a : A) :
    (smulCommutator R a ^ j) D ∈ differentialOperators R A M N m := by
  induction j generalizing D with
  | zero => simpa using hD
  | succ j ih =>
    rw [pow_succ, mul_apply_eq_comp]
    exact ih (smulCommutator_mem_differentialOperators hD a)

/-- The `j`-fold commutator of an operator of order at most `m` vanishes when `m < j`. -/
theorem smulCommutator_pow_eq_zero {D : M →ₗ[R] N} {m j : ℕ}
    (hD : D ∈ differentialOperators R A M N m) (hj : m < j) (a : A) :
    (smulCommutator R a ^ j) D = 0 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hj
  rw [show m + t + 1 = t + (m + 1) by omega, pow_add, mul_apply_eq_comp, pow_succ',
    mul_apply_eq_comp,
    smulCommutator_eq_zero_of_mem_differentialOperators_zero
      (smulCommutator_pow_mem_differentialOperators (by simpa using hD) a), map_zero]

/-- Orders add under composition. -/
theorem comp_mem_differentialOperators {P : N →ₗ[R] O} {Q : M →ₗ[R] N} {m k : ℕ}
    (hP : P ∈ differentialOperators R A N O m) (hQ : Q ∈ differentialOperators R A M N k) :
    P ∘ₗ Q ∈ differentialOperators R A M O (m + k) := by
  induction h : m + k generalizing m k P Q with
  | zero =>
    obtain ⟨rfl, rfl⟩ : m = 0 ∧ k = 0 := by omega
    rw [mem_differentialOperators_zero_iff] at hP hQ ⊢
    intro a x
    simp [hP, hQ]
  | succ n ih =>
    rw [mem_differentialOperators_succ_iff]
    intro a
    rw [smulCommutator_comp]
    refine add_mem ?_ ?_
    · rcases k with _ | k
      · simp [smulCommutator_eq_zero_of_mem_differentialOperators_zero hQ a]
      · exact ih hP (smulCommutator_mem_differentialOperators hQ a) (by omega)
    · rcases m with _ | m
      · simp [smulCommutator_eq_zero_of_mem_differentialOperators_zero hP a]
      · exact ih (smulCommutator_mem_differentialOperators hP a) hQ (by omega)

variable (R A N) in
/-- The differential operators on `N` form a filtered ring under composition. -/
instance : SetLike.GradedMonoid (differentialOperators R A N N) where
  one_mem := LinearMap.restrictScalars_mem_differentialOperators_zero (LinearMap.id : N →ₗ[A] N)
  mul_mem _ _ _ _ hP hQ := comp_mem_differentialOperators hP hQ

/-- The top iterated commutators of a composition multiply: for `P` of order at most `m` and
`Q` of order at most `k`, the `(m + k)`-fold commutator of `P ∘ Q` with `a` is
`(m + k).choose m` times the composition of the `m`-fold commutator of `P` with the `k`-fold
commutator of `Q`. -/
theorem smulCommutator_pow_comp_of_mem {P : N →ₗ[R] O} {Q : M →ₗ[R] N} {m k : ℕ}
    (hP : P ∈ differentialOperators R A N O m) (hQ : Q ∈ differentialOperators R A M N k)
    (a : A) :
    (smulCommutator R a ^ (m + k)) (P ∘ₗ Q) =
      (m + k).choose m • ((smulCommutator R a ^ m) P ∘ₗ (smulCommutator R a ^ k) Q) := by
  rw [smulCommutator_pow_comp, sum_eq_single (m, k)]
  · rintro ⟨i, j⟩ hij hne
    rw [mem_antidiagonal] at hij
    rcases lt_or_gt_of_ne (show i ≠ m by rintro rfl; exact hne (by simp; omega)) with h | h
    · simp [smulCommutator_pow_eq_zero hQ (show k < j by omega) a]
    · simp [smulCommutator_pow_eq_zero hP h a]
  · simp

/-! ### Locality: differential operators factor through jets -/

/-- A differential operator of order at most `m` sends `I ^ (m + 1) • M` into `I • N`. Thus the
class of `D x` modulo `I • N` depends only on the class of `x` modulo `I ^ (m + 1) • M`. -/
theorem apply_mem_smul_top_of_mem_pow_smul_top {D : M →ₗ[R] N} {m : ℕ}
    (hD : D ∈ differentialOperators R A M N m) (I : Ideal A) {x : M}
    (hx : x ∈ I ^ (m + 1) • (⊤ : Submodule A M)) : D x ∈ I • (⊤ : Submodule A N) := by
  induction m generalizing D x with
  | zero =>
    rw [zero_add, pow_one] at hx
    refine Submodule.smul_induction_on hx (fun a ha y _ ↦ ?_)
      fun y z hy hz ↦ by rw [map_add]; exact add_mem hy hz
    rw [mem_differentialOperators_zero_iff.1 hD]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  | succ m ih =>
    rw [pow_succ', Submodule.mul_smul] at hx
    refine Submodule.smul_induction_on hx (fun a ha y hy ↦ ?_)
      fun y z hy hz ↦ by rw [map_add]; exact add_mem hy hz
    rw [apply_smul_eq_smulCommutator_add]
    exact add_mem (ih (smulCommutator_mem_differentialOperators hD a) hy)
      (Submodule.smul_mem_smul ha Submodule.mem_top)

end

/-! ### First-order operators on the algebra -/

section FirstOrder

variable {R : Type*} {A M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]

/-- A derivation is a differential operator of order at most one: its commutator with
multiplication by `a` is multiplication by `D a`. -/
theorem _root_.Derivation.mem_differentialOperators_one (D : Derivation R A M) :
    (D : A →ₗ[R] M) ∈ differentialOperators R A A M 1 := by
  rw [mem_differentialOperators_succ_iff]
  intro a
  rw [mem_differentialOperators_zero_iff]
  intro b x
  simp only [smulCommutator_apply_apply, Derivation.coeFn_coe, smul_eq_mul, Derivation.leibniz,
    add_sub_cancel_left, smul_smul]

/-- For `D : A →ₗ[R] M` of order at most one, `f ↦ D f - f • D 1` is a derivation. -/
def derivationOfMemDifferentialOperatorsOne (D : A →ₗ[R] M)
    (hD : D ∈ differentialOperators R A A M 1) : Derivation R A M :=
  Derivation.mk' (D - (LinearMap.toSpanSingleton A M (D 1)).restrictScalars R) fun f g ↦ by
    have h := congr($(smulCommutator_eq_zero_of_mem_differentialOperators_zero
      (smulCommutator_mem_differentialOperators hD f) g) 1)
    simp only [smulCommutator_apply_apply, smul_eq_mul, mul_one, LinearMap.zero_apply] at h
    simp only [LinearMap.sub_apply, LinearMap.restrictScalars_apply,
      LinearMap.toSpanSingleton_apply]
    rw [sub_eq_zero, sub_eq_iff_eq_add] at h
    rw [h]
    simp only [smul_sub, smul_smul, mul_comm g f]
    abel

@[simp]
theorem derivationOfMemDifferentialOperatorsOne_apply (D : A →ₗ[R] M)
    (hD : D ∈ differentialOperators R A A M 1) (f : A) :
    derivationOfMemDifferentialOperatorsOne D hD f = D f - f • D 1 := by
  simp [derivationOfMemDifferentialOperatorsOne]

variable (R A M) in
/-- The first-order operators `A → M` are exactly the sums `δ + (· • m)` of a derivation `δ`
and multiplication by `m : M`, with `δ` and `m = D 1` determined by `D`. -/
def differentialOperatorsOneEquiv :
    differentialOperators R A A M 1 ≃ₗ[R] Derivation R A M × M where
  toFun D := (derivationOfMemDifferentialOperatorsOne D.1 D.2, D.1 1)
  invFun p := ⟨p.1 + (LinearMap.toSpanSingleton A M p.2).restrictScalars R,
    add_mem p.1.mem_differentialOperators_one <| differentialOperators_le_succ 0 <|
      LinearMap.restrictScalars_mem_differentialOperators_zero _⟩
  map_add' D E := by ext <;> simp; abel
  map_smul' r D := by ext <;> simp [smul_sub, smul_comm r]
  left_inv D := by ext; simp
  right_inv p := by ext <;> simp

@[simp]
theorem differentialOperatorsOneEquiv_apply_fst_apply (D : differentialOperators R A A M 1)
    (f : A) :
    (differentialOperatorsOneEquiv R A M D).1 f = (D : A →ₗ[R] M) f - f • (D : A →ₗ[R] M) 1 := by
  simp [differentialOperatorsOneEquiv]

@[simp]
theorem differentialOperatorsOneEquiv_apply_snd (D : differentialOperators R A A M 1) :
    (differentialOperatorsOneEquiv R A M D).2 = (D : A →ₗ[R] M) 1 := by
  simp [differentialOperatorsOneEquiv]

@[simp]
theorem coe_differentialOperatorsOneEquiv_symm_apply (p : Derivation R A M × M) (f : A) :
    ((differentialOperatorsOneEquiv R A M).symm p : A →ₗ[R] M) f = p.1 f + f • p.2 := by
  simp [differentialOperatorsOneEquiv]

/-- An operator `D : A →ₗ[R] M` has order at most one exactly when it is a derivation plus
multiplication by `D 1`. -/
theorem mem_differentialOperators_one_iff {D : A →ₗ[R] M} :
    D ∈ differentialOperators R A A M 1 ↔
      ∃ δ : Derivation R A M, ∀ f, D f = δ f + f • D 1 := by
  refine ⟨fun hD ↦ ⟨derivationOfMemDifferentialOperatorsOne D hD, fun f ↦ by simp⟩, ?_⟩
  rintro ⟨δ, hδ⟩
  have : D = ((differentialOperatorsOneEquiv R A M).symm (δ, D 1) : A →ₗ[R] M) := by
    ext f; simp [hδ f]
  exact this ▸ Subtype.prop _

end FirstOrder

/-! ### The second derivative on polynomials -/

open Polynomial in
/-- The second derivative on `R[X]` has order at most two, as a composition of two
derivations. -/
theorem derivative_comp_derivative_mem_differentialOperators_two {R : Type*} [CommRing R] :
    (derivative ∘ₗ derivative : R[X] →ₗ[R] R[X]) ∈ differentialOperators R R[X] R[X] R[X] 2 := by
  have h : ((derivative' : Derivation R R[X] R[X]) : R[X] →ₗ[R] R[X]) = derivative :=
    LinearMap.ext derivative'_apply
  have := comp_mem_differentialOperators (derivative' (R := R)).mem_differentialOperators_one
    (derivative' (R := R)).mem_differentialOperators_one
  rwa [h] at this

open Polynomial in
/-- The second derivative on `R[X]` does not have order at most one when `2 ≠ 0` in `R`: its
double commutator with multiplication by `X` sends `1` to `2`. -/
theorem derivative_comp_derivative_notMem_differentialOperators_one {R : Type*} [CommRing R]
    (h : (2 : R) ≠ 0) :
    (derivative ∘ₗ derivative : R[X] →ₗ[R] R[X]) ∉ differentialOperators R R[X] R[X] R[X] 1 := by
  intro hD
  have h2 := congr($(smulCommutator_eq_zero_of_mem_differentialOperators_zero
    (smulCommutator_mem_differentialOperators hD X) X) 1)
  simp only [smulCommutator_apply_apply, LinearMap.comp_apply, smul_eq_mul, mul_one,
    LinearMap.zero_apply, derivative_X, derivative_one, derivative_zero, mul_zero, sub_zero,
    ← pow_two, derivative_X_pow] at h2
  apply h
  simpa [← C_ofNat, ← map_ofNat C] using h2

end TauCeti

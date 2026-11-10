/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Filtration
public import TauCeti.LinearAlgebra.End.Recursion

/-!
# Finite recursion on quotient-tower limits

An endomorphism which raises a module filtration by one step is nilpotent on every
finite quotient, even when it is not nilpotent on the original module. The finite
geometric sums therefore solve the recursion `x = a + T x` in every quotient.
They commute with quotient transitions and assemble into a solution operator on
the completion.

Filtered coefficient intertwiners preserve these solutions, including when the
source and target cutoffs are compared by a nonidentity modulus. The solution
also retains the filtration order and the leading class of its input.

## Attribution

Adapted from `Mei/LinearAlgebra/ModuleFiltration/Nilpotent.lean` and
`Mei/LinearAlgebra/ModuleFiltration/Recursion.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
The constructions use the existing `ModuleTower.quotients` completion API.
-/

public noncomputable section

namespace TauCeti.ModuleTower

open Opposite

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  (J : ℕ → Submodule R M) (hJ : Antitone J)
  (T : Module.End R M) (hT : ∀ k, (J k).map T ≤ J (k + 1))

/-- A filtration-raising endomorphism induces an endomorphism at each finite order. -/
def quotientRaisingEnd (k : ℕ) : Module.End R ((quotients J hJ).obj (op (k + 1))) :=
  quotientsLift J hJ (k + 1) ((quotientsπ J hJ (k + 1)).comp T) (by
    rw [LinearMap.ker_comp, ker_quotientsπ]
    exact fun _ hx => hJ (Nat.le_succ (k + 1)) (hT (k + 1) ⟨_, hx, rfl⟩))

/-- On a representative, the finite endomorphism applies the original endomorphism. -/
@[simp] theorem quotientRaisingEnd_mk (k : ℕ) (x : M) :
    quotientRaisingEnd J hJ T hT k (quotientsπ J hJ (k + 1) x) =
      quotientsπ J hJ (k + 1) (T x) := by
  rw [quotientRaisingEnd, quotientsLift_quotientsπ, LinearMap.comp_apply]

/-- Every power of a finite endomorphism is induced by the corresponding original power. -/
@[simp] theorem quotientRaisingEnd_pow_mk (k n : ℕ) (x : M) :
    (quotientRaisingEnd J hJ T hT k ^ n) (quotientsπ J hJ (k + 1) x) =
      quotientsπ J hJ (k + 1) ((T ^ n) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp,
      ih, quotientRaisingEnd_mk]

/-- On the order-`k` quotient, the `(k + 1)`st power vanishes. -/
@[simp] theorem quotientRaisingEnd_pow_eq_zero (hzero : J 0 = ⊤) (k : ℕ) :
    quotientRaisingEnd J hJ T hT k ^ (k + 1) = 0 := by
  apply LinearMap.ext
  intro a
  obtain ⟨x, rfl⟩ := quotientsπ_surjective J hJ (k + 1) a
  have hx : (T ^ (k + 1)) x ∈ J (k + 1) := by
    simpa only [Nat.zero_add] using
      Module.End.pow_apply_mem_of_map_le (T := T) (F := J) hT
        (by simp [hzero] : x ∈ J 0) (k + 1)
  rw [quotientRaisingEnd_pow_mk, LinearMap.zero_apply, quotientsπ_eq_zero_iff]
  exact hx

/-- The quotient endomorphisms commute with all composite transition maps. -/
@[simp] theorem transitionOfLE_quotientRaisingEnd {k l : ℕ} (hkl : k ≤ l)
    (x : (quotients J hJ).obj (op (l + 1))) :
    (quotients J hJ).transitionOfLE (Nat.add_le_add_right hkl 1)
        (quotientRaisingEnd J hJ T hT l x) =
      quotientRaisingEnd J hJ T hT k
        ((quotients J hJ).transitionOfLE (Nat.add_le_add_right hkl 1) x) := by
  obtain ⟨a, rfl⟩ := quotientsπ_surjective J hJ (l + 1) x
  simp only [quotientRaisingEnd_mk, transitionOfLE_quotientsπ]

/-- The linear solution operator at each nonzero quotient order. -/
def quotientRecursion (k : ℕ) : Module.End R ((quotients J hJ).obj (op (k + 1))) :=
  (quotientRaisingEnd J hJ T hT k).finiteRecursion (k + 1)

/-- The finite quotient solution is the sum of powers zero through `k`. -/
theorem quotientRecursion_apply (k : ℕ) (a : (quotients J hJ).obj (op (k + 1))) :
    quotientRecursion J hJ T hT k a =
      ∑ j ∈ Finset.range (k + 1), (quotientRaisingEnd J hJ T hT k ^ j) a :=
  Module.End.finiteRecursion_apply _ _ _

/-- The quotient solution is represented by the same finite sum in the original module. -/
@[simp] theorem quotientRecursion_mk (k : ℕ) (a : M) :
    quotientRecursion J hJ T hT k (quotientsπ J hJ (k + 1) a) =
      quotientsπ J hJ (k + 1) (T.finiteRecursion (k + 1) a) := by
  simp only [quotientRecursion_apply, Module.End.finiteRecursion_apply, map_sum,
    quotientRaisingEnd_pow_mk]

/-- The finite sum solves the recursion in the quotient. -/
theorem quotientRecursion_eq_add (hzero : J 0 = ⊤) (k : ℕ) (a : (quotients J hJ).obj (op (k + 1))) :
    quotientRecursion J hJ T hT k a =
      a + quotientRaisingEnd J hJ T hT k (quotientRecursion J hJ T hT k a) :=
  Module.End.finiteRecursion_eq_add _ (quotientRaisingEnd_pow_eq_zero J hJ T hT hzero k) a

/-- Every solution of a quotient recursion is its finite geometric sum. -/
theorem eq_quotientRecursion_of_eq_add (hzero : J 0 = ⊤) (k : ℕ)
    {a x : (quotients J hJ).obj (op (k + 1))}
    (hx : x = a + quotientRaisingEnd J hJ T hT k x) :
    x = quotientRecursion J hJ T hT k a :=
  Module.End.eq_finiteRecursion_of_eq_add _
    (quotientRaisingEnd_pow_eq_zero J hJ T hT hzero k) hx

/-- The finite solution operators commute with every composite quotient transition. -/
@[simp] theorem transitionOfLE_quotientRecursion (hzero : J 0 = ⊤) {k l : ℕ} (hkl : k ≤ l)
    (a : (quotients J hJ).obj (op (l + 1))) :
    (quotients J hJ).transitionOfLE (Nat.add_le_add_right hkl 1)
        (quotientRecursion J hJ T hT l a) =
      quotientRecursion J hJ T hT k
        ((quotients J hJ).transitionOfLE (Nat.add_le_add_right hkl 1) a) := by
  have h := Module.End.comp_finiteRecursion
    (quotientRaisingEnd J hJ T hT l) (quotientRaisingEnd J hJ T hT k)
    ((quotients J hJ).transitionOfLE (Nat.add_le_add_right hkl 1))
    (LinearMap.ext (transitionOfLE_quotientRaisingEnd J hJ T hT hkl))
    (quotientRaisingEnd_pow_eq_zero J hJ T hT hzero l)
    (quotientRaisingEnd_pow_eq_zero J hJ T hT hzero k)
  exact LinearMap.congr_fun h a

/-- If `J 0 = ⊤`, the order-zero quotient is subsingleton. -/
theorem subsingleton_quotients_zero (hzero : J 0 = ⊤) :
    Subsingleton ((quotients J hJ).obj (op 0)) := by
  constructor
  intro a b
  obtain ⟨x, rfl⟩ := quotientsπ_surjective J hJ 0 a
  obtain ⟨y, rfl⟩ := quotientsπ_surjective J hJ 0 b
  have quotient_zero (z : M) : quotientsπ J hJ 0 z = 0 :=
    (quotientsπ_eq_zero_iff J hJ).mpr (hzero ▸ Submodule.mem_top)
  rw [quotient_zero x, quotient_zero y]

/-- The linear solution operator at the `n`-th quotient. The order-zero quotient is
subsingleton, so its solution operator is zero. -/
private def limQuotientRecursionCoord (n : ℕ) :
    (quotients J hJ).lim →ₗ[R] (quotients J hJ).obj (op n) :=
  match n with
  | 0 => 0
  | k + 1 => (quotientRecursion J hJ T hT k).comp ((quotients J hJ).limπ (k + 1))

@[simp] private theorem limQuotientRecursionCoord_zero :
    limQuotientRecursionCoord J hJ T hT 0 = 0 := by
  rw [limQuotientRecursionCoord]

@[simp] private theorem limQuotientRecursionCoord_succ (k : ℕ) :
    limQuotientRecursionCoord J hJ T hT (k + 1) =
      (quotientRecursion J hJ T hT k).comp ((quotients J hJ).limπ (k + 1)) := by
  rw [limQuotientRecursionCoord]

include hT in
private theorem transition_limRecursionCoord (hzero : J 0 = ⊤) (n : ℕ) :
    (quotients J hJ).transition n ∘ₗ limQuotientRecursionCoord J hJ T hT (n + 1) =
      limQuotientRecursionCoord J hJ T hT n := by
  cases n with
  | zero =>
    have := subsingleton_quotients_zero J hJ hzero
    ext a
    exact Subsingleton.elim _ _
  | succ k =>
    apply LinearMap.ext
    intro a
    rw [limQuotientRecursionCoord_succ, limQuotientRecursionCoord_succ,
      LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    rw [← transitionOfLE_succ]
    rw [← (quotients J hJ).transitionOfLE_comp_limπ (Nat.le_succ (k + 1)),
      LinearMap.comp_apply]
    exact transitionOfLE_quotientRecursion J hJ T hT hzero (Nat.le_succ k)
      ((quotients J hJ).limπ (k + 2) a)

/-- Compatible finite solutions define a linear solution operator on the completion. -/
def limQuotientsRecursion (hzero : J 0 = ⊤) : Module.End R (quotients J hJ).lim :=
  (quotients J hJ).limLift (limQuotientRecursionCoord J hJ T hT)
    (transition_limRecursionCoord (J := J) (hJ := hJ) (T := T) (hT := hT) hzero)

/-- At order zero, the completed solution is uniquely determined. -/
theorem limπ_zero_limQuotientsRecursion (hzero : J 0 = ⊤)
    (a : (quotients J hJ).lim) :
    (quotients J hJ).limπ 0 (limQuotientsRecursion J hJ T hT hzero a) = 0 := by
  have := subsingleton_quotients_zero J hJ hzero
  exact Subsingleton.elim _ _

/-- At a positive order, projection of the completed solution is its finite quotient solution. -/
theorem limπ_succ_limQuotientsRecursion (hzero : J 0 = ⊤) (k : ℕ)
    (a : (quotients J hJ).lim) :
    (quotients J hJ).limπ (k + 1) (limQuotientsRecursion J hJ T hT hzero a) =
      quotientRecursion J hJ T hT k ((quotients J hJ).limπ (k + 1) a) := by
  rw [limQuotientsRecursion, ← LinearMap.comp_apply,
    (quotients J hJ).limπ_comp_limLift, limQuotientRecursionCoord_succ,
    LinearMap.comp_apply]

/-- Completed recursion preserves every filtration term of its input. -/
theorem limQuotientsRecursion_mem_limFiltration (hzero : J 0 = ⊤) {k : ℕ}
    {a : (quotients J hJ).lim} (ha : a ∈ (quotients J hJ).limFiltration k) :
    limQuotientsRecursion J hJ T hT hzero a ∈ (quotients J hJ).limFiltration k := by
  cases k with
  | zero => simp
  | succ k =>
    cases k with
    | zero =>
      have := subsingleton_quotients_zero J hJ hzero
      rw [limFiltration_succ, LinearMap.mem_ker]
      exact Subsingleton.elim _ _
    | succ k =>
      rw [limFiltration_succ (quotients J hJ) (k + 1), LinearMap.mem_ker] at ha ⊢
      rw [limπ_succ_limQuotientsRecursion, ha, map_zero]

/-- The completed solution satisfies the recursion at each positive finite order. -/
theorem limπ_succ_limQuotientsRecursion_eq_add (hzero : J 0 = ⊤) (k : ℕ)
    (a : (quotients J hJ).lim) :
    (quotients J hJ).limπ (k + 1) (limQuotientsRecursion J hJ T hT hzero a) =
      (quotients J hJ).limπ (k + 1) a +
        quotientRaisingEnd J hJ T hT k
          ((quotients J hJ).limπ (k + 1) (limQuotientsRecursion J hJ T hT hzero a)) := by
  simpa only [limπ_succ_limQuotientsRecursion] using
    quotientRecursion_eq_add J hJ T hT hzero k ((quotients J hJ).limπ (k + 1) a)

/-- The completed solution retains exactly the filtration order of its input. -/
@[simp] theorem limQuotientsRecursion_mem_limFiltration_iff (hzero : J 0 = ⊤)
    (k : ℕ) (a : (quotients J hJ).lim) :
    limQuotientsRecursion J hJ T hT hzero a ∈ (quotients J hJ).limFiltration k ↔
      a ∈ (quotients J hJ).limFiltration k := by
  constructor
  · intro h
    cases k with
    | zero => simp
    | succ k =>
      cases k with
      | zero =>
        have := subsingleton_quotients_zero J hJ hzero
        rw [limFiltration_succ, LinearMap.mem_ker]
        exact Subsingleton.elim _ _
      | succ k =>
        rw [limFiltration_succ (quotients J hJ) (k + 1), LinearMap.mem_ker] at h ⊢
        have he := limπ_succ_limQuotientsRecursion_eq_add J hJ T hT hzero k a
        rw [h, map_zero, add_zero] at he
        exact he.symm
  · exact limQuotientsRecursion_mem_limFiltration J hJ T hT hzero

/-- At order zero, the completed solution differs from its input by a term of the first
positive filtration order. -/
theorem limQuotientsRecursion_sub_self_mem_limFiltration_zero (hzero : J 0 = ⊤)
    (a : (quotients J hJ).lim) :
    limQuotientsRecursion J hJ T hT hzero a - a ∈ (quotients J hJ).limFiltration 1 := by
  have := subsingleton_quotients_zero J hJ hzero
  rw [limFiltration_succ, LinearMap.mem_ker, map_sub,
    limπ_zero_limQuotientsRecursion, zero_sub, neg_eq_zero]
  exact Subsingleton.elim _ _

/-- For an input of order at least `k + 1`, the correction has order at least `k + 2`. -/
theorem limQuotientsRecursion_sub_self_mem_limFiltration_succ (hzero : J 0 = ⊤)
    (k : ℕ) {a : (quotients J hJ).lim}
    (ha : a ∈ (quotients J hJ).limFiltration (k + 1)) :
    limQuotientsRecursion J hJ T hT hzero a - a ∈
      (quotients J hJ).limFiltration (k + 2) := by
  have hs := limQuotientsRecursion_mem_limFiltration J hJ T hT hzero ha
  rw [limFiltration_succ, LinearMap.mem_ker, map_sub,
    limπ_succ_limQuotientsRecursion_eq_add, add_sub_cancel_left]
  obtain ⟨x, hx⟩ := quotientsπ_surjective J hJ (k + 1)
    ((quotients J hJ).limπ (k + 1) (limQuotientsRecursion J hJ T hT hzero a))
  have hs' := hs
  rw [limFiltration_succ, LinearMap.mem_ker] at hs'
  have hxmem : x ∈ J k :=
    (quotientsπ_eq_zero_iff J hJ).mp
      ((quotientsπ_eq_limπ_of_le (Nat.le_succ k) hx).trans hs')
  rw [← hx, quotientRaisingEnd_mk, quotientsπ_eq_zero_iff]
  exact hT k ⟨x, hxmem, rfl⟩

/-- A compatible solution is uniquely determined by its finite-order recursions. -/
theorem eq_limQuotientsRecursion_of_forall_limπ_eq_add (hzero : J 0 = ⊤)
    {a x : (quotients J hJ).lim}
    (hx : ∀ k : ℕ, (quotients J hJ).limπ (k + 1) x =
      (quotients J hJ).limπ (k + 1) a +
        quotientRaisingEnd J hJ T hT k ((quotients J hJ).limπ (k + 1) x)) :
    x = limQuotientsRecursion J hJ T hT hzero a := by
  apply (quotients J hJ).lim_ext
  intro n
  cases n with
  | zero =>
    have := subsingleton_quotients_zero J hJ hzero
    exact Subsingleton.elim _ _
  | succ k =>
    rw [limπ_succ_limQuotientsRecursion]
    exact eq_quotientRecursion_of_eq_add J hJ T hT hzero k (hx k)

/-- The completed endomorphism induced by a filtration-raising endomorphism. -/
def limQuotientsRaisingEnd (hT : ∀ k, (J k).map T ≤ J (k + 1)) :
    Module.End R (quotients J hJ).lim :=
  limQuotientsMap hJ hJ T (fun n => ⟨n + 1, fun _ hx =>
    hJ (show n ≤ n + 2 by omega) (hT (n + 1) ⟨_, hx, rfl⟩)⟩)

/-- The completed solution solves the recursion for the induced completed endomorphism. -/
theorem limQuotientsRecursion_eq_add_limQuotientsRaisingEnd (hzero : J 0 = ⊤)
    (a : (quotients J hJ).lim) :
    limQuotientsRecursion J hJ T hT hzero a =
      a + limQuotientsRaisingEnd J hJ T hT (limQuotientsRecursion J hJ T hT hzero a) := by
  apply (quotients J hJ).lim_ext
  intro n
  have hfT : ∀ n, ∃ m, J m ≤ (J n).comap T := (fun n => ⟨n + 1, fun _ hx =>
    hJ (show n ≤ n + 2 by omega) (hT (n + 1) ⟨_, hx, rfl⟩)⟩)
  cases n with
  | zero =>
    have := subsingleton_quotients_zero J hJ hzero
    exact Subsingleton.elim _ _
  | succ k =>
    obtain ⟨b, hb⟩ := quotientsπ_surjective J hJ (k + 2)
      ((quotients J hJ).limπ (k + 2) (limQuotientsRecursion J hJ T hT hzero a))
    calc
      (quotients J hJ).limπ (k + 1) (limQuotientsRecursion J hJ T hT hzero a) =
          (quotients J hJ).limπ (k + 1) a +
            quotientRaisingEnd J hJ T hT k
              ((quotients J hJ).limπ (k + 1)
                (limQuotientsRecursion J hJ T hT hzero a)) :=
        limπ_succ_limQuotientsRecursion_eq_add J hJ T hT hzero k a
      _ = (quotients J hJ).limπ (k + 1) a + quotientsπ J hJ (k + 1) (T b) := by
        rw [← quotientsπ_eq_limπ_of_le (Nat.le_succ (k + 1)) hb,
          quotientRaisingEnd_mk]
      _ = (quotients J hJ).limπ (k + 1)
          (a + limQuotientsRaisingEnd J hJ T hT
            (limQuotientsRecursion J hJ T hT hzero a)) := by
        rw [map_add, limQuotientsRaisingEnd]
        exact congrArg _ (limπ_limQuotientsMap hJ hJ T hfT
          (n := k + 1) (m := k + 2)
          (show J (k + 2) ≤ (J (k + 1)).comap T from fun _ hx =>
            hJ (show k + 1 ≤ k + 3 by omega) (hT (k + 2) ⟨_, hx, rfl⟩)) hb).symm

/-- Every solution of the recursion for the induced completed endomorphism is the completed
solution. -/
theorem eq_limQuotientsRecursion_of_eq_add_limQuotientsRaisingEnd (hzero : J 0 = ⊤)
    {a x : (quotients J hJ).lim}
    (hx : x = a + limQuotientsRaisingEnd J hJ T hT x) :
    x = limQuotientsRecursion J hJ T hT hzero a := by
  apply eq_limQuotientsRecursion_of_forall_limπ_eq_add J hJ T hT hzero
  intro k
  have hfT : ∀ n, ∃ m, J m ≤ (J n).comap T := (fun n => ⟨n + 1, fun _ hx =>
    hJ (show n ≤ n + 2 by omega) (hT (n + 1) ⟨_, hx, rfl⟩)⟩)
  obtain ⟨b, hb⟩ := quotientsπ_surjective J hJ (k + 2)
    ((quotients J hJ).limπ (k + 2) x)
  have proj := congrArg ((quotients J hJ).limπ (k + 1)) hx
  rw [map_add, limQuotientsRaisingEnd,
    limπ_limQuotientsMap hJ hJ T hfT (n := k + 1) (m := k + 2)
      (show J (k + 2) ≤ (J (k + 1)).comap T from fun _ hmem =>
        hJ (show k + 1 ≤ k + 3 by omega) (hT (k + 2) ⟨_, hmem, rfl⟩)) hb] at proj
  simpa only [← quotientsπ_eq_limπ_of_le (Nat.le_succ (k + 1)) hb,
    quotientRaisingEnd_mk] using proj

section Naturality

variable {N : Type*} [AddCommGroup N] [Module R N]
  (K : ℕ → Submodule R N) (hK : Antitone K)
  (U : Module.End R N) (hU : ∀ k, (K k).map U ≤ K (k + 1))
  (r : M →ₗ[R] N)

/-- A map between positive-order quotients induced by a filtered coefficient map. -/
def quotientsMapQ (m n : ℕ) (hr : J (m + 1) ≤ (K (n + 1)).comap r) :
    (quotients J hJ).obj (op (m + 1)) →ₗ[R] (quotients K hK).obj (op (n + 1)) :=
  quotientsLift J hJ (m + 1) ((quotientsπ K hK (n + 1)).comp r) (by
    rw [LinearMap.ker_comp, ker_quotientsπ]
    exact hr)

@[simp] theorem quotientsMapQ_mk {m n : ℕ} (hr : J (m + 1) ≤ (K (n + 1)).comap r)
    (x : M) :
    quotientsMapQ J hJ K hK r m n hr (quotientsπ J hJ (m + 1) x) =
      quotientsπ K hK (n + 1) (r x) := by
  rw [quotientsMapQ, quotientsLift_quotientsπ, LinearMap.comp_apply]

/-- Filtered coefficient intertwiners commute with the induced raising maps. -/
theorem quotientsMapQ_quotientRaisingEnd {m n : ℕ}
    (hr : J (m + 1) ≤ (K (n + 1)).comap r) (hcomm : r.comp T = U.comp r)
    (a : (quotients J hJ).obj (op (m + 1))) :
    quotientsMapQ J hJ K hK r m n hr (quotientRaisingEnd J hJ T hT m a) =
      quotientRaisingEnd K hK U hU n (quotientsMapQ J hJ K hK r m n hr a) := by
  obtain ⟨x, rfl⟩ := quotientsπ_surjective J hJ (m + 1) a
  simp only [quotientRaisingEnd_mk, quotientsMapQ_mk]
  exact congrArg (quotientsπ K hK (n + 1)) (LinearMap.congr_fun hcomm x)

/-- Filtered coefficient intertwiners preserve the finite quotient solutions. -/
theorem quotientsMapQ_quotientRecursion (hzeroJ : J 0 = ⊤) (hzeroK : K 0 = ⊤)
    {m n : ℕ} (hr : J (m + 1) ≤ (K (n + 1)).comap r) (hcomm : r.comp T = U.comp r)
    (a : (quotients J hJ).obj (op (m + 1))) :
    quotientsMapQ J hJ K hK r m n hr (quotientRecursion J hJ T hT m a) =
      quotientRecursion K hK U hU n (quotientsMapQ J hJ K hK r m n hr a) := by
  have h := Module.End.comp_finiteRecursion
    (quotientRaisingEnd J hJ T hT m) (quotientRaisingEnd K hK U hU n)
    (quotientsMapQ J hJ K hK r m n hr)
    (LinearMap.ext (quotientsMapQ_quotientRaisingEnd J hJ T hT K hK U hU r hr hcomm))
    (quotientRaisingEnd_pow_eq_zero J hJ T hT hzeroJ m)
    (quotientRaisingEnd_pow_eq_zero K hK U hU hzeroK n)
  exact LinearMap.congr_fun h a

/-- Filtered coefficient intertwiners preserve completed recursion solutions. No monotonicity
of the cutoff modulus, injectivity of the coefficient map, or nilpotence on the original modules
is required. -/
theorem limQuotientsMap_limQuotientsRecursion (hzeroJ : J 0 = ⊤) (hzeroK : K 0 = ⊤)
    (hf : ∀ n, ∃ m, J m ≤ (K n).comap r) (ρ : ℕ → ℕ) (hr : ∀ n, J (ρ n + 1) ≤ (K (n + 1)).comap r)
    (hcomm : r.comp T = U.comp r) (a : (quotients J hJ).lim) :
    limQuotientsMap hJ hK r hf
        (limQuotientsRecursion J hJ T hT hzeroJ a) =
      limQuotientsRecursion K hK U hU hzeroK
        (limQuotientsMap hJ hK r hf a) := by
  apply (quotients K hK).lim_ext
  intro n
  cases n with
  | zero =>
    have := subsingleton_quotients_zero K hK hzeroK
    exact Subsingleton.elim _ _
  | succ n =>
    obtain ⟨c, hc⟩ := quotientsπ_surjective J hJ (ρ n + 1)
      ((quotients J hJ).limπ (ρ n + 1) a)
    have hb : quotientsπ J hJ (ρ n + 1)
          (T.finiteRecursion (ρ n + 1) c) =
        (quotients J hJ).limπ (ρ n + 1)
          (limQuotientsRecursion J hJ T hT hzeroJ a) := by
      rw [limπ_succ_limQuotientsRecursion, ← hc, quotientRecursion_mk]
    calc
      (quotients K hK).limπ (n + 1)
          (limQuotientsMap hJ hK r hf
            (limQuotientsRecursion J hJ T hT hzeroJ a)) =
          quotientsπ K hK (n + 1) (r (T.finiteRecursion (ρ n + 1) c)) :=
        limπ_limQuotientsMap hJ hK r hf (hr n) hb
      _ = quotientsMapQ J hJ K hK r (ρ n) n (hr n)
          (quotientRecursion J hJ T hT (ρ n)
            (quotientsπ J hJ (ρ n + 1) c)) := by
        rw [quotientRecursion_mk, quotientsMapQ_mk]
      _ = quotientRecursion K hK U hU n (quotientsMapQ J hJ K hK r (ρ n) n (hr n)
          (quotientsπ J hJ (ρ n + 1) c)) :=
        quotientsMapQ_quotientRecursion J hJ T hT K hK U hU r hzeroJ hzeroK
          (hr n) hcomm (quotientsπ J hJ (ρ n + 1) c)
      _ = quotientRecursion K hK U hU n
          ((quotients K hK).limπ (n + 1)
            (limQuotientsMap hJ hK r hf a)) := by
        rw [quotientsMapQ_mk,
          limπ_limQuotientsMap hJ hK r hf (hr n) hc]
      _ = (quotients K hK).limπ (n + 1)
          (limQuotientsRecursion K hK U hU hzeroK
            (limQuotientsMap hJ hK r hf a)) :=
        (limπ_succ_limQuotientsRecursion K hK U hU hzeroK n
          (limQuotientsMap hJ hK r hf a)).symm

end Naturality

end TauCeti.ModuleTower

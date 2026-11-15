/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Pointwise
public import Mathlib.Data.Finsupp.Basic
public import TauCeti.Algebra.MvPolynomial.Laurent.Basic

import Mathlib.Tactic.Ring

/-!
# One-step skew Laurent exchange over a subsemiring

For a subsemiring `C ≤ B` normalized by `x, E : Bˣ` with `(E : B) ∈ C` and unique left Laurent
expansions `∑_m c_m * x^m`, let `y = E * x⁻¹` and `P_r = TauCeti.exchangeProduct x E r`. Over
semirings without subtraction, `y` normalizes `C` with unique left Laurent expansions
(`Subsemiring.skewLaurentSum_mul_inv_injective`), `∑_m c_m * x^m ∈ C.laurentAdjoin y` iff
`c_{-r} ∈ C * P_r` (`Subsemiring.mem_laurentAdjoin_mul_inv_iff`), and
`C.laurentAdjoin x ⊓ C.laurentAdjoin y = C ⊔ Subsemiring.closure {x, y}` with unique positive normal
forms (`Subsemiring.laurentAdjoin_inf_laurentAdjoin_mul_inv`,
`Subsemiring.exchangeNormalForm_mul_inv_injective`).

## References

* A. Berenstein, S. Fomin, and A. Zelevinsky, *Cluster algebras III*, Lemmas 4.1–4.2.
* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Adv. Math. 195 (2005), §§5.2–5.3.
-/

public section

open scoped Pointwise
namespace TauCeti
section Group
variable {G : Type*} [Group G] (x E : G)
/-- **Twisted exchange product** `P_r` associated to `x, E : G`: defined recursively by `P_0 = 1`
and `P_{r + 1} = P_r * ((x^r)⁻¹ * E * x^r)`, so `(E * x⁻¹)^r = P_r * (x^r)⁻¹`. -/
def exchangeProduct : ℕ → G
  | 0 => 1
  | r + 1 => exchangeProduct r * ((x ^ r)⁻¹ * E * x ^ r)
@[simp] theorem exchangeProduct_zero : exchangeProduct x E 0 = 1 := (rfl)
@[simp] theorem exchangeProduct_succ (r : ℕ) :
    exchangeProduct x E (r + 1) = exchangeProduct x E r * ((x ^ r)⁻¹ * E * x ^ r) := (rfl)
theorem exchangeProduct_one : exchangeProduct x E 1 = E := by simp [exchangeProduct]
theorem exchangeProduct_two : exchangeProduct x E 2 = E * (x⁻¹ * E * x) := by simp [exchangeProduct]
theorem mul_inv_pow_eq_exchangeProduct_mul_pow_inv (r : ℕ) :
    (E * x⁻¹) ^ r = exchangeProduct x E r * (x ^ r)⁻¹ := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, ih, exchangeProduct_succ, pow_succ', mul_inv_rev]
    simp only [mul_assoc, mul_inv_cancel_left]
theorem mul_inv_zpow_natCast_eq_exchangeProduct_mul_zpow_neg (r : ℕ) :
    (E * x⁻¹) ^ (r : ℤ) = exchangeProduct x E r * x ^ (-(r : ℤ)) := by
  rw [zpow_natCast, mul_inv_pow_eq_exchangeProduct_mul_pow_inv, zpow_neg, zpow_natCast]
theorem exchangeProduct_add (s t : ℕ) :
    exchangeProduct x E (s + t) =
      exchangeProduct x E s * ((x ^ s)⁻¹ * exchangeProduct x E t * x ^ s) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hpow : x ^ (s + t) = x ^ t * x ^ s := by rw [add_comm, pow_add]
    rw [Nat.add_succ, exchangeProduct_succ, ih, exchangeProduct_succ, hpow, mul_inv_rev]
    simp only [mul_assoc, mul_inv_cancel_left]
theorem mul_inv_zpow_sub_mul_exchangeProduct (k N : ℕ) :
    (E * x⁻¹) ^ ((k : ℤ) - (N : ℤ)) * exchangeProduct x E N =
      exchangeProduct x E k * x ^ ((N : ℤ) - (k : ℤ)) := by
  have hN : (E * x⁻¹) ^ (-(N : ℤ)) * exchangeProduct x E N = x ^ (N : ℤ) :=
    mul_left_cancel (a := (E * x⁻¹) ^ (N : ℤ)) <| by
      rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul,
        mul_inv_zpow_natCast_eq_exchangeProduct_mul_zpow_neg, mul_assoc, ← zpow_add,
        neg_add_cancel, zpow_zero, mul_one]
  rw [sub_eq_add_neg, zpow_add, mul_assoc, hN,
    mul_inv_zpow_natCast_eq_exchangeProduct_mul_zpow_neg, mul_assoc, ← zpow_add, neg_add_eq_sub]
end Group
theorem exchangeProduct_of_commute {G : Type*} [Group G] {x E : G} (h : Commute x E) (r : ℕ) :
    exchangeProduct x E r = E ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [exchangeProduct_succ, ih, (h.pow_left r).inv_left.eq, mul_assoc E, inv_mul_cancel, mul_one,
      pow_succ]
end TauCeti
namespace Subsemiring
open TauCeti
section Semiring
variable {B : Type*} [Semiring B]
theorem conjAct_inv_smul_eq {C : Subsemiring B} {x : Bˣ} (hx : ConjAct.toConjAct x • C = C) :
    ConjAct.toConjAct x⁻¹ • C = C := by
  simpa [← mul_smul] using (congrArg (ConjAct.toConjAct x⁻¹ • ·) hx).symm
theorem conjAct_zpow_smul_eq {C : Subsemiring B} {x : Bˣ} (hx : ConjAct.toConjAct x • C = C)
    (m : ℤ) : ConjAct.toConjAct (x ^ m) • C = C := by
  induction m using Int.induction_on with
  | zero => simp
  | succ _ hk => rw [zpow_add_one, map_mul, mul_smul, hx, hk]
  | pred _ hk => rw [zpow_sub_one, map_mul, mul_smul, conjAct_inv_smul_eq hx, hk]
theorem conjAct_mul_inv_smul_eq {C : Subsemiring B} {x E : Bˣ}
    (hx : ConjAct.toConjAct x • C = C) (hE : ConjAct.toConjAct E • C = C) :
    ConjAct.toConjAct (E * x⁻¹) • C = C := by
  rw [map_mul, mul_smul, conjAct_inv_smul_eq hx, hE]
theorem conj_zpow_mem {C : Subsemiring B} {x : Bˣ} (hx : ConjAct.toConjAct x • C = C) (m : ℤ)
    {c : B} (hc : c ∈ C) : ((x ^ m : Bˣ) : B) * c * ((x ^ (-m) : Bˣ) : B) ∈ C := by
  have hmem : ConjAct.toConjAct (x ^ m) • c ∈ C := by
    rw [← conjAct_zpow_smul_eq hx m]; exact smul_mem_pointwise_smul _ _ _ hc
  simpa [ConjAct.units_smul_def, zpow_neg] using hmem
theorem zpow_mul_eq_conj_mul_zpow (x : Bˣ) (m : ℤ) (c : B) :
    ((x ^ m : Bˣ) : B) * c =
      (((x ^ m : Bˣ) : B) * c * ((x ^ (-m) : Bˣ) : B)) * ((x ^ m : Bˣ) : B) := by
  rw [mul_assoc (((x ^ m : Bˣ) : B) * c), ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero,
    Units.val_one, mul_one]
theorem coe_exchangeProduct_mem {C : Subsemiring B} {x E : Bˣ}
    (hx : ConjAct.toConjAct x • C = C) (hEC : (E : B) ∈ C) (r : ℕ) :
    ((exchangeProduct x E r : Bˣ) : B) ∈ C := by
  induction r with
  | zero => simp [C.one_mem]
  | succ r ih =>
    rw [exchangeProduct_succ, Units.val_mul]
    exact C.mul_mem ih (by
      simpa [zpow_neg, zpow_natCast, mul_assoc] using conj_zpow_mem hx (-(r : ℤ)) hEC)
/-- The subsemiring `C[x^{±1}] = C ⊔ Subsemiring.closure {x, x⁻¹}` generated by `C` and `x^{±1}`. -/
def laurentAdjoin (C : Subsemiring B) (x : Bˣ) : Subsemiring B :=
  C ⊔ Subsemiring.closure {(x : B), ((x⁻¹ : Bˣ) : B)}
theorem laurentAdjoin_def (C : Subsemiring B) (x : Bˣ) :
    C.laurentAdjoin x = C ⊔ Subsemiring.closure {(x : B), ((x⁻¹ : Bˣ) : B)} := (rfl)
theorem le_laurentAdjoin (C : Subsemiring B) (x : Bˣ) : C ≤ C.laurentAdjoin x := le_sup_left
theorem coe_mem_laurentAdjoin (C : Subsemiring B) (x : Bˣ) : (x : B) ∈ C.laurentAdjoin x :=
  (le_sup_right : Subsemiring.closure _ ≤ C.laurentAdjoin x) <| subset_closure <| by simp
theorem coe_inv_mem_laurentAdjoin (C : Subsemiring B) (x : Bˣ) :
    ((x⁻¹ : Bˣ) : B) ∈ C.laurentAdjoin x :=
  (le_sup_right : Subsemiring.closure _ ≤ C.laurentAdjoin x) <| subset_closure <| by simp
theorem coe_zpow_mem_laurentAdjoin (C : Subsemiring B) (x : Bˣ) (m : ℤ) :
    ((x ^ m : Bˣ) : B) ∈ C.laurentAdjoin x := by
  induction m using Int.induction_on with
  | zero => simp [(C.laurentAdjoin x).one_mem]
  | succ _ hk => rw [zpow_add_one, Units.val_mul]; exact mul_mem hk (C.coe_mem_laurentAdjoin x)
  | pred _ hk => rw [zpow_sub_one, Units.val_mul]; exact mul_mem hk (C.coe_inv_mem_laurentAdjoin x)
/-- Evaluation of finite left Laurent expansions `f ↦ ∑_m f(m) * x^m` with coefficients in `C`. -/
def skewLaurentSum (C : Subsemiring B) (x : Bˣ) : (ℤ →₀ C) →+ B where
  toFun f := f.sum fun m c ↦ (c : B) * ((x ^ m : Bˣ) : B)
  map_zero' := Finsupp.sum_zero_index
  map_add' _ _ := Finsupp.sum_add_index' (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _)
theorem skewLaurentSum_apply (C : Subsemiring B) (x : Bˣ) (f : ℤ →₀ C) :
    C.skewLaurentSum x f = f.sum fun m c ↦ (c : B) * ((x ^ m : Bˣ) : B) := (rfl)
@[simp] theorem skewLaurentSum_single (C : Subsemiring B) (x : Bˣ) (m : ℤ) (c : C) :
    C.skewLaurentSum x (Finsupp.single m c) = (c : B) * ((x ^ m : Bˣ) : B) := by
  rw [skewLaurentSum_apply, Finsupp.sum_single_index (zero_mul _)]
theorem skewLaurentSum_mem_laurentAdjoin (C : Subsemiring B) (x : Bˣ) (f : ℤ →₀ C) :
    C.skewLaurentSum x f ∈ C.laurentAdjoin x := by
  induction f using Finsupp.induction_linear with
  | zero => simp [(C.laurentAdjoin x).zero_mem]
  | add _ _ hf hg => rw [map_add]; exact add_mem hf hg
  | single m c =>
    rw [skewLaurentSum_single]
    exact mul_mem (C.le_laurentAdjoin x c.2) (C.coe_zpow_mem_laurentAdjoin x m)
theorem range_skewLaurentSum {C : Subsemiring B} {x : Bˣ} (hx : ConjAct.toConjAct x • C = C) :
    Set.range (C.skewLaurentSum x) = (C.laurentAdjoin x : Set B) := by
  refine Set.Subset.antisymm (by rintro _ ⟨f, rfl⟩; exact C.skewLaurentSum_mem_laurentAdjoin x f) ?_
  let M := AddMonoidHom.mrange (C.skewLaurentSum x)
  have hmul : ∀ {a b : B}, a ∈ M → b ∈ M → a * b ∈ M := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    induction f using Finsupp.induction_linear with
    | zero => simp [M.zero_mem]
    | add _ _ hf₁ hf₂ => rw [map_add, add_mul]; exact M.add_mem hf₁ hf₂
    | single m c₁ =>
      induction g using Finsupp.induction_linear with
      | zero => simp [M.zero_mem]
      | add _ _ hg₁ hg₂ => rw [map_add, mul_add]; exact M.add_mem hg₁ hg₂
      | single n c₂ =>
        refine ⟨Finsupp.single (m + n) ⟨(c₁ : B) * (((x ^ m : Bˣ) : B) * (c₂ : B) *
          ((x ^ (-m) : Bˣ) : B)), C.mul_mem c₁.2 (conj_zpow_mem hx m c₂.2)⟩, ?_⟩
        simp only [skewLaurentSum_single, zpow_add, Units.val_mul]
        rw [← mul_assoc _ ((x ^ m : Bˣ) : B), mul_assoc (c₁ : B), ← zpow_mul_eq_conj_mul_zpow]
        simp only [mul_assoc]
  let S : Subsemiring B := { M with one_mem' := ⟨Finsupp.single 0 1, by simp⟩, mul_mem' := hmul }
  suffices C.laurentAdjoin x ≤ S from this
  refine sup_le (fun c hc ↦ ⟨Finsupp.single 0 ⟨c, hc⟩, by simp⟩) (closure_le.mpr ?_)
  rintro b (rfl | rfl)
  · exact ⟨Finsupp.single 1 1, by simp⟩
  · exact ⟨Finsupp.single (-1) 1, by simp⟩
private theorem finsupp_sum_single_apply_of_injective {α β M N : Type*} [AddCommMonoid M]
    [AddCommMonoid N] (f : α →₀ M) {φ : α → β} (hφ : Function.Injective φ) (ψ : α → M → N)
    (hψ : ∀ a, ψ a 0 = 0) (a₀ : α) :
    (f.sum fun a m ↦ Finsupp.single (φ a) (ψ a m)) (φ a₀) = ψ a₀ (f a₀) := by
  classical
  rw [Finsupp.sum_apply, Finsupp.sum]
  by_cases ha₀ : a₀ ∈ f.support
  · rw [Finset.sum_eq_single_of_mem a₀ ha₀
      (fun _ _ hne ↦ Finsupp.single_eq_of_ne (hφ.ne hne.symm)), Finsupp.single_eq_same]
  · rw [Finset.sum_eq_zero fun a ha ↦
      Finsupp.single_eq_of_ne (hφ.ne (by rintro rfl; exact ha₀ ha)),
      Finsupp.notMem_support_iff.mp ha₀, hψ]
/-- Evaluation of finite two-sided positive normal forms
`(c₀, c⁺, c⁻) ↦ c₀ + ∑_r c⁺(r) * x^{r + 1} + ∑_r c⁻(r) * y^{r + 1}`. -/
def exchangeNormalForm (C : Subsemiring B) (x y : B) : (C × (ℕ →₀ C) × (ℕ →₀ C)) →+ B where
  toFun t := (t.1 : B) + (t.2.1.sum fun r c ↦ (c : B) * x ^ (r + 1)) +
    (t.2.2.sum fun r c ↦ (c : B) * y ^ (r + 1))
  map_zero' := by simp
  map_add' _ _ := by
    rw [Prod.fst_add, Subsemiring.coe_add, Prod.snd_add, Prod.fst_add, Prod.snd_add,
      Finsupp.sum_add_index' (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _),
      Finsupp.sum_add_index' (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _)]
    simp only [add_assoc, add_left_comm]
theorem exchangeNormalForm_apply (C : Subsemiring B) (x y : B) (t : C × (ℕ →₀ C) × (ℕ →₀ C)) :
    C.exchangeNormalForm x y t = (t.1 : B) + (t.2.1.sum fun r c ↦ (c : B) * x ^ (r + 1)) +
      (t.2.2.sum fun r c ↦ (c : B) * y ^ (r + 1)) := (rfl)
theorem exchangeNormalForm_mem_sup_closure (C : Subsemiring B) (x y : B)
    (t : C × (ℕ →₀ C) × (ℕ →₀ C)) :
    C.exchangeNormalForm x y t ∈ C ⊔ Subsemiring.closure {x, y} := by
  let S : Subsemiring B := C ⊔ Subsemiring.closure {x, y}
  have hCS : C ≤ S := le_sup_left
  have hxS : x ∈ S := (le_sup_right : Subsemiring.closure _ ≤ S) <| subset_closure <| by simp
  have hyS : y ∈ S := (le_sup_right : Subsemiring.closure _ ≤ S) <| subset_closure <| by simp
  refine S.add_mem (S.add_mem (hCS t.1.2) ?_) ?_
  · rw [Finsupp.sum]; exact S.sum_mem fun r _ ↦ S.mul_mem (hCS (t.2.1 r).2) (S.pow_mem hxS _)
  · rw [Finsupp.sum]; exact S.sum_mem fun r _ ↦ S.mul_mem (hCS (t.2.2 r).2) (S.pow_mem hyS _)
theorem sup_closure_mul_inv_le_inf_laurentAdjoin {C : Subsemiring B} {x E : Bˣ}
    (hEC : (E : B) ∈ C) :
    C ⊔ Subsemiring.closure {(x : B), ((E * x⁻¹ : Bˣ) : B)} ≤
      C.laurentAdjoin x ⊓ C.laurentAdjoin (E * x⁻¹) := by
  refine le_inf (sup_le (C.le_laurentAdjoin x) <| closure_le.mpr ?_)
    (sup_le (C.le_laurentAdjoin (E * x⁻¹)) <| closure_le.mpr ?_)
  · rintro b (rfl | rfl)
    · exact C.coe_mem_laurentAdjoin x
    · exact mul_mem (C.le_laurentAdjoin x hEC) (C.coe_inv_mem_laurentAdjoin x)
  · rintro b (rfl | rfl)
    · have hx_val : (x : B) = (((E * x⁻¹)⁻¹ : Bˣ) : B) * (E : B) := by
        rw [← Units.val_mul]; exact congrArg Units.val (by simp [mul_inv_rev])
      rw [hx_val]
      exact mul_mem (C.coe_inv_mem_laurentAdjoin (E * x⁻¹)) (C.le_laurentAdjoin (E * x⁻¹) hEC)
    · exact C.coe_mem_laurentAdjoin (E * x⁻¹)
private theorem skewLaurentSum_mem_range_exchangeNormalForm {C : Subsemiring B} {x E : Bˣ}
    {f : ℤ →₀ C} (hd : ∀ r : ℕ, 0 < r →
      ∃ d : C, (f (-(r : ℤ)) : B) = (d : B) * ((exchangeProduct x E r : Bˣ) : B)) :
    C.skewLaurentSum x f ∈ Set.range (C.exchangeNormalForm (x : B) ((E * x⁻¹ : Bˣ) : B)) := by
  rw [← AddMonoidHom.coe_mrange, SetLike.mem_coe, skewLaurentSum_apply, Finsupp.sum]
  refine (AddMonoidHom.mrange (C.exchangeNormalForm (x : B) ((E * x⁻¹ : Bˣ) : B))).sum_mem
    fun m _ ↦ ?_
  rcases lt_trichotomy m 0 with hm | rfl | hm
  · let r : ℕ := (-m - 1).toNat
    obtain ⟨d, hd_eq⟩ := hd (r + 1) (Nat.succ_pos r)
    refine ⟨(0, 0, Finsupp.single r d), ?_⟩
    rw [exchangeNormalForm_apply, (by omega : m = -((r + 1 : ℕ) : ℤ)), hd_eq, mul_assoc,
      ← Units.val_mul, ← mul_inv_zpow_natCast_eq_exchangeProduct_mul_zpow_neg, zpow_natCast,
      Units.val_pow_eq_pow_val, Finsupp.sum_single_index (zero_mul _)]; simp
  · exact ⟨(f 0, 0, 0), by simp [exchangeNormalForm_apply]⟩
  · let r : ℕ := (m - 1).toNat
    refine ⟨(0, Finsupp.single r (f m), 0), ?_⟩
    rw [exchangeNormalForm_apply, (by omega : m = ((r + 1 : ℕ) : ℤ)), zpow_natCast,
      Units.val_pow_eq_pow_val, Finsupp.sum_single_index (zero_mul _)]; simp
private theorem finsupp_sum_single_eq_zero_of_forall_ne {C : Type*} [AddCommMonoid C]
    (f : ℕ →₀ C) (φ : ℕ → ℤ) (g : ℕ → C → C) {m : ℤ} (hm : ∀ r, φ r ≠ m) :
    (f.sum fun r c ↦ Finsupp.single (φ r) (g r c)) m = 0 := by
  rw [Finsupp.sum_apply, Finsupp.sum]
  exact Finset.sum_eq_zero fun r _ ↦ Finsupp.single_eq_of_ne (hm r).symm
section Uniqueness
variable {C : Subsemiring B} {x E : Bˣ} (hx : ConjAct.toConjAct x • C = C) (hEC : (E : B) ∈ C)
  (hinj : Function.Injective (C.skewLaurentSum x))
include hx hEC hinj
theorem skewLaurentSum_mul_inv_injective : Function.Injective (C.skewLaurentSum (E * x⁻¹)) := by
  intro f₁ f₂ hfg; ext m₀; classical
  let N : ℕ := (f₁.support ∪ f₂.support ∪ {m₀}).sup fun m ↦ (-m).toNat
  have hN (m : ℤ) (hm : m ∈ f₁.support ∪ f₂.support ∪ {m₀}) : 0 ≤ m + (N : ℤ) := by
    have := Finset.le_sup (f := fun k : ℤ ↦ (-k).toNat) hm; omega
  let p (m : ℤ) : C :=
    ⟨((exchangeProduct x E (m + (N : ℤ)).toNat : Bˣ) : B), coe_exchangeProduct_mem hx hEC _⟩
  let Φ (f : ℤ →₀ C) : ℤ →₀ C := f.sum fun m c ↦ Finsupp.single (-(m + (N : ℤ))) (c * p m)
  have hΦ (f : ℤ →₀ C) (hf : ∀ m ∈ f.support, 0 ≤ m + (N : ℤ)) :
      C.skewLaurentSum x (Φ f) =
        C.skewLaurentSum (E * x⁻¹) f * (((E * x⁻¹) ^ (N : ℤ) : Bˣ) : B) := by
    rw [map_finsuppSum, skewLaurentSum_apply, Finsupp.sum, Finsupp.sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    have hmN := Int.toNat_of_nonneg (hf m hm)
    rw [skewLaurentSum_single]; dsimp only [p]
    rw [Subsemiring.coe_mul, mul_assoc ((f m : C) : B), ← Units.val_mul,
      (by omega : -(m + (N : ℤ)) = -((m + (N : ℤ)).toNat : ℤ)),
      ← mul_inv_zpow_natCast_eq_exchangeProduct_mul_zpow_neg, hmN, zpow_add, Units.val_mul,
      mul_assoc]
  have hΦ_eq : Φ f₁ = Φ f₂ := hinj <| by
    rw [hΦ f₁ fun m hm ↦ hN m (by simp [hm]), hΦ f₂ fun m hm ↦ hN m (by simp [hm]), hfg]
  have hinj_neg : Function.Injective fun m : ℤ ↦ -(m + (N : ℤ)) :=
    fun a b (h : -(a + (N : ℤ)) = -(b + (N : ℤ))) ↦ by omega
  have hcoeff := congrArg (fun g : ℤ →₀ C ↦ (g (-(m₀ + (N : ℤ))) : B)) hΦ_eq
  dsimp only [Φ] at hcoeff
  rw [finsupp_sum_single_apply_of_injective f₁ hinj_neg (fun m c ↦ c * p m) (fun _ ↦ zero_mul _) m₀,
    finsupp_sum_single_apply_of_injective f₂ hinj_neg (fun m c ↦ c * p m)
      (fun _ ↦ zero_mul _) m₀] at hcoeff
  exact (Units.mul_left_inj (exchangeProduct x E (m₀ + (N : ℤ)).toNat)).mp hcoeff
private theorem exists_mul_exchangeProduct_of_skewLaurentSum_eq {f g : ℤ →₀ C}
    (hg : C.skewLaurentSum x f = C.skewLaurentSum (E * x⁻¹) g) (r : ℕ) :
    ∃ d : C, (f (-(r : ℤ)) : B) = (d : B) * ((exchangeProduct x E r : Bˣ) : B) := by
  let N : ℕ := g.support.sup fun n ↦ (-n).toNat
  have hN (n : ℤ) (hn : n ∈ g.support) : 0 ≤ n + (N : ℤ) := by
    have := Finset.le_sup (f := fun k : ℤ ↦ (-k).toNat) hn; omega
  let qL (m : ℤ) : C := ⟨((x ^ m : Bˣ) : B) * ((exchangeProduct x E N : Bˣ) : B) *
    ((x ^ (-m) : Bˣ) : B), conj_zpow_mem hx m (coe_exchangeProduct_mem hx hEC N)⟩
  let qR (n : ℤ) : C :=
    ⟨((exchangeProduct x E (n + (N : ℤ)).toNat : Bˣ) : B), coe_exchangeProduct_mem hx hEC _⟩
  let f' : ℤ →₀ C := f.sum fun m c ↦ Finsupp.single m (c * qL m)
  let g' : ℤ →₀ C := g.sum fun n d ↦ Finsupp.single (-n) (d * qR n)
  have hf' : C.skewLaurentSum x f' = C.skewLaurentSum x f * ((exchangeProduct x E N : Bˣ) : B) := by
    rw [map_finsuppSum, skewLaurentSum_apply, Finsupp.sum, Finsupp.sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ ↦ by
      rw [skewLaurentSum_single, Subsemiring.coe_mul, mul_assoc ((f m : C) : B),
        ← zpow_mul_eq_conj_mul_zpow, mul_assoc]
  have hg' : C.skewLaurentSum x g' =
      C.skewLaurentSum (E * x⁻¹) g * ((exchangeProduct x E N : Bˣ) : B) := by
    rw [map_finsuppSum, skewLaurentSum_apply, Finsupp.sum, Finsupp.sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have := Int.toNat_of_nonneg (hN n hn)
    rw [skewLaurentSum_single, Subsemiring.coe_mul, mul_assoc ((g n : C) : B), ← Units.val_mul,
      ← (by omega : (N : ℤ) - ((n + (N : ℤ)).toNat : ℤ) = -n),
      ← mul_inv_zpow_sub_mul_exchangeProduct, (by omega : ((n + (N : ℤ)).toNat : ℤ) - (N : ℤ) = n),
      Units.val_mul, mul_assoc]
  have hcoeff := congrArg (fun h : ℤ →₀ C ↦ (h (-(r : ℤ)) : B))
    (hinj (by rw [hf', hg', hg]) : f' = g')
  rw [finsupp_sum_single_apply_of_injective f (fun _ _ h ↦ h)
      (fun m c ↦ c * qL m) (fun _ ↦ zero_mul _) (-(r : ℤ)),
    finsupp_sum_single_apply_of_injective g neg_injective
      (fun n d ↦ d * qR n) (fun _ ↦ zero_mul _) (r : ℤ)] at hcoeff
  dsimp only [qL, qR, Subsemiring.coe_mul] at hcoeff
  let W : Bˣ := (x ^ r)⁻¹ * exchangeProduct x E N * x ^ r
  have hW : ((x ^ (-(r : ℤ)) : Bˣ) : B) * ((exchangeProduct x E N : Bˣ) : B) *
      ((x ^ (-(-(r : ℤ))) : Bˣ) : B) = (W : B) := by simp [W, zpow_neg, zpow_natCast, mul_assoc]
  rw [(by omega : (((r : ℤ) + (N : ℤ)).toNat : ℕ) = r + N), hW, exchangeProduct_add,
    Units.val_mul (exchangeProduct x E r) W, ← mul_assoc ((g (r : ℤ) : C) : B)] at hcoeff
  exact ⟨g (r : ℤ), (Units.mul_left_inj W).mp hcoeff⟩
theorem exchangeNormalForm_mul_inv_injective :
    Function.Injective (C.exchangeNormalForm (x : B) ((E * x⁻¹ : Bˣ) : B)) := by
  let P (r : ℕ) : C :=
    ⟨((exchangeProduct x E (r + 1) : Bˣ) : B), coe_exchangeProduct_mem hx hEC (r + 1)⟩
  let nf (t : C × (ℕ →₀ C) × (ℕ →₀ C)) : ℤ →₀ C :=
    Finsupp.single 0 t.1 + (t.2.1.sum fun r c ↦ Finsupp.single ((r + 1 : ℕ) : ℤ) c) +
      (t.2.2.sum fun r c ↦ Finsupp.single (-((r + 1 : ℕ) : ℤ)) (c * P r))
  have hnf (t) :
      C.skewLaurentSum x (nf t) = C.exchangeNormalForm (x : B) ((E * x⁻¹ : Bˣ) : B) t := by
    rw [map_add, map_add, skewLaurentSum_single, zpow_zero, Units.val_one, mul_one,
      map_finsuppSum, map_finsuppSum, exchangeNormalForm_apply]
    refine congrArg₂ (· + ·) (congrArg (t.1.1 + ·) <| Finsupp.sum_congr fun r _ ↦ ?_)
      (Finsupp.sum_congr fun r _ ↦ ?_)
    · rw [skewLaurentSum_single, zpow_natCast, Units.val_pow_eq_pow_val]
    · rw [skewLaurentSum_single, Subsemiring.coe_mul, mul_assoc, ← Units.val_mul,
        ← mul_inv_zpow_natCast_eq_exchangeProduct_mul_zpow_neg, zpow_natCast,
        Units.val_pow_eq_pow_val]
  have hp : Function.Injective fun r : ℕ ↦ ((r + 1 : ℕ) : ℤ) := fun _ _ h ↦ by dsimp at h; omega
  have hn : Function.Injective fun r : ℕ ↦ -((r + 1 : ℕ) : ℤ) := fun _ _ h ↦ by dsimp at h; omega
  have hpos0 (u : ℕ →₀ C) (m : ℤ) (hm : ∀ r : ℕ, ((r + 1 : ℕ) : ℤ) ≠ m) :=
    finsupp_sum_single_eq_zero_of_forall_ne u (fun r ↦ ((r + 1 : ℕ) : ℤ)) (fun _ c ↦ c) hm
  have hneg0 (u : ℕ →₀ C) (m : ℤ) (hm : ∀ r : ℕ, -((r + 1 : ℕ) : ℤ) ≠ m) :=
    finsupp_sum_single_eq_zero_of_forall_ne u (fun r ↦ -((r + 1 : ℕ) : ℤ)) (fun r c ↦ c * P r) hm
  intro t₁ t₂ ht
  have hEq : nf t₁ = nf t₂ := hinj (by rw [hnf, hnf, ht])
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simpa only [nf, Finsupp.add_apply, Finsupp.single_eq_same, hpos0 _ 0 (fun _ ↦ by omega),
      hneg0 _ 0 (fun _ ↦ by omega), add_zero] using congrArg (fun g : ℤ →₀ C ↦ g 0) hEq
  · ext s
    simpa only [nf, Finsupp.add_apply, Finsupp.single_eq_of_ne (by omega : ((s + 1 : ℕ) : ℤ) ≠ 0),
      finsupp_sum_single_apply_of_injective _ hp (fun _ c ↦ c) (fun _ ↦ rfl) s,
      hneg0 _ ((s + 1 : ℕ) : ℤ) (fun _ ↦ by omega), zero_add, add_zero] using
      congrArg (fun g : ℤ →₀ C ↦ (g ((s + 1 : ℕ) : ℤ) : B)) hEq
  · ext s
    have hs := congrArg (fun g : ℤ →₀ C ↦ (g (-((s + 1 : ℕ) : ℤ)) : B)) hEq
    simp only [nf, Finsupp.add_apply, Finsupp.single_eq_of_ne (by omega : -((s + 1 : ℕ) : ℤ) ≠ 0),
      hpos0 _ (-((s + 1 : ℕ) : ℤ)) (fun _ ↦ by omega),
      finsupp_sum_single_apply_of_injective _ hn (fun r c ↦ c * P r) (fun _ ↦ zero_mul _) s,
      zero_add, Subsemiring.coe_mul] at hs
    exact (Units.mul_left_inj (exchangeProduct x E (s + 1))).mp hs
end Uniqueness
section MainExchange
variable {C : Subsemiring B} {x E : Bˣ} (hx : ConjAct.toConjAct x • C = C)
  (hE : ConjAct.toConjAct E • C = C) (hEC : (E : B) ∈ C)
  (hinj : Function.Injective (C.skewLaurentSum x))
include hx hE hEC hinj
theorem mem_laurentAdjoin_mul_inv_iff (f : ℤ →₀ C) :
    C.skewLaurentSum x f ∈ C.laurentAdjoin (E * x⁻¹) ↔
      ∀ r : ℕ, 0 < r →
        ∃ d : C, (f (-(r : ℤ)) : B) = (d : B) * ((exchangeProduct x E r : Bˣ) : B) := by
  refine ⟨fun hmem r _ ↦ ?_, fun hd ↦ ?_⟩
  · obtain ⟨g, hg⟩ : C.skewLaurentSum x f ∈ Set.range (C.skewLaurentSum (E * x⁻¹)) := by
      rwa [range_skewLaurentSum (conjAct_mul_inv_smul_eq hx hE)]
    exact exists_mul_exchangeProduct_of_skewLaurentSum_eq hx hEC hinj hg.symm r
  · obtain ⟨t, ht⟩ := skewLaurentSum_mem_range_exchangeNormalForm hd
    exact ht ▸ (sup_closure_mul_inv_le_inf_laurentAdjoin hEC).trans inf_le_right
      (C.exchangeNormalForm_mem_sup_closure _ _ t)
private theorem inf_subset_range_exchangeNormalForm :
    ((C.laurentAdjoin x ⊓ C.laurentAdjoin (E * x⁻¹) : Subsemiring B) : Set B) ⊆
      Set.range (C.exchangeNormalForm (x : B) ((E * x⁻¹ : Bˣ) : B)) := by
  rintro b ⟨hbx, hby⟩
  obtain ⟨f, rfl⟩ : b ∈ Set.range (C.skewLaurentSum x) := by rwa [range_skewLaurentSum hx]
  exact skewLaurentSum_mem_range_exchangeNormalForm
    ((mem_laurentAdjoin_mul_inv_iff hx hE hEC hinj f).mp hby)
theorem laurentAdjoin_inf_laurentAdjoin_mul_inv :
    C.laurentAdjoin x ⊓ C.laurentAdjoin (E * x⁻¹) =
      C ⊔ Subsemiring.closure {(x : B), ((E * x⁻¹ : Bˣ) : B)} := by
  refine le_antisymm (fun b hb ↦ ?_) (sup_closure_mul_inv_le_inf_laurentAdjoin hEC)
  obtain ⟨t, rfl⟩ := inf_subset_range_exchangeNormalForm hx hE hEC hinj hb
  exact C.exchangeNormalForm_mem_sup_closure _ _ t
theorem range_exchangeNormalForm_mul_inv :
    Set.range (C.exchangeNormalForm (x : B) ((E * x⁻¹ : Bˣ) : B)) =
      ((C ⊔ Subsemiring.closure {(x : B), ((E * x⁻¹ : Bˣ) : B)} : Subsemiring B) : Set B) := by
  refine Set.Subset.antisymm
    (by rintro _ ⟨t, rfl⟩; exact C.exchangeNormalForm_mem_sup_closure _ _ t) ?_
  rw [← laurentAdjoin_inf_laurentAdjoin_mul_inv hx hE hEC hinj]
  exact inf_subset_range_exchangeNormalForm hx hE hEC hinj
end MainExchange
end Semiring
end Subsemiring
namespace Subring
variable {B : Type*} [Ring B]
@[simp] theorem toSubsemiring_sup_closure (S : Subring B) (s : Set B) :
    (S ⊔ Subring.closure s).toSubsemiring = S.toSubsemiring ⊔ Subsemiring.closure s := by
  refine le_antisymm ?_ (sup_le (fun _ hb ↦ (le_sup_left : S ≤ S ⊔ Subring.closure s) hb) <|
    Subsemiring.closure_le.mpr fun _ hb ↦
      (le_sup_right : Subring.closure s ≤ S ⊔ Subring.closure s) (Subring.subset_closure hb))
  let T : Subsemiring B := S.toSubsemiring ⊔ Subsemiring.closure s
  have hST : S.toSubsemiring ≤ T := le_sup_left
  have hclT : Subsemiring.closure s ≤ T := le_sup_right
  let T' : Subring B :=
    { T with neg_mem' {a} ha := by simpa using T.mul_mem (hST (S.neg_mem S.one_mem)) ha }
  exact (sup_le (fun _ hb ↦ hST hb)
    (Subring.closure_le.mpr fun _ hb ↦ hclT (Subsemiring.subset_closure hb)) : _ ≤ T')
/-- The subring `S[x^{±1}] = S ⊔ Subring.closure {x, x⁻¹}` generated by `S` and `x : Bˣ`. -/
def laurentAdjoin (S : Subring B) (x : Bˣ) : Subring B :=
  S ⊔ Subring.closure {(x : B), ((x⁻¹ : Bˣ) : B)}
@[simp] theorem toSubsemiring_laurentAdjoin (S : Subring B) (x : Bˣ) :
    (S.laurentAdjoin x).toSubsemiring = S.toSubsemiring.laurentAdjoin x :=
  S.toSubsemiring_sup_closure _
end Subring
namespace TauCeti
section Checks
theorem exchangeProduct_two_of_quasiComm {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]
    {v : Rˣ} {x E : Bˣ} {z : B}
    (hxz : (x : B) * z = algebraMap R B ((v ^ 2 : Rˣ) : R) * (z * (x : B)))
    (hE : (E : B) = 1 + z) :
    ((exchangeProduct x E 2 : Bˣ) : B) =
      (1 + z) * (1 + algebraMap R B ((v ^ (-2 : ℤ) : Rˣ) : R) * z) := by
  have hconj : ((x⁻¹ : Bˣ) : B) * z * (x : B) = algebraMap R B ((v ^ (-2 : ℤ) : Rˣ) : R) * z := by
    have h1 : ((x⁻¹ : Bˣ) : B) * ((x : B) * z) = z := by rw [← mul_assoc, Units.inv_mul, one_mul]
    rw [hxz, ← mul_assoc ((x⁻¹ : Bˣ) : B), ← Algebra.commutes ((v ^ 2 : Rˣ) : R), mul_assoc,
      ← mul_assoc ((x⁻¹ : Bˣ) : B) z] at h1
    have h2 := congrArg (algebraMap R B ((v ^ (-2 : ℤ) : Rˣ) : R) * ·) h1
    rw [← mul_assoc, ← map_mul, ← Units.val_mul,
      (by simp [zpow_ofNat] : v ^ (-2 : ℤ) * v ^ 2 = 1), Units.val_one, map_one, one_mul] at h2
    exact h2
  rw [exchangeProduct_two, Units.val_mul, Units.val_mul, Units.val_mul, hE]
  congr 1; rw [mul_add, mul_one, add_mul, Units.inv_mul, hconj]
theorem two_mul_inv_exchange_check :
    let B := LaurentRing ℚ Unit
    let C : Subsemiring B := (algebraMap ℤ B).rangeS
    let x : Bˣ := LaurentRing.unitX ()
    let E : Bˣ := Units.map (algebraMap ℚ B).toMonoidHom (Units.mk0 2 (by norm_num))
    (2 : B) * ((x⁻¹ : Bˣ) : B) ∈ C.laurentAdjoin x ⊓ C.laurentAdjoin (E * x⁻¹) ∧
      (4 : B) * ((x ^ (-2 : ℤ) : Bˣ) : B) ∈ C.laurentAdjoin x ⊓ C.laurentAdjoin (E * x⁻¹) ∧
      ((x⁻¹ : Bˣ) : B) ∉ C.laurentAdjoin (E * x⁻¹) ∧
      (2 : B) * ((x ^ (-2 : ℤ) : Bˣ) : B) ∉ C.laurentAdjoin (E * x⁻¹) := by
  intro B C x E
  have halg (z : ℤ) : algebraMap ℤ B z = AddMonoidAlgebra.single 0 (z : ℚ) := by
    rw [IsScalarTower.algebraMap_apply ℤ ℚ B, eq_intCast, Algebra.algebraMap_eq_smul_one,
      AddMonoidAlgebra.one_def, AddMonoidAlgebra.smul_single', mul_one]
  have hinj : Function.Injective (C.skewLaurentSum x) := by
    intro f₁ f₂ h; ext m
    have heval (f : ℤ →₀ C) :
        AddMonoidAlgebra.coeff (C.skewLaurentSum x f) (Finsupp.single () m) =
          AddMonoidAlgebra.coeff ((f m : C) : B) 0 := by
      have hbody (k : ℤ) (c : C) : (c : B) * ((x ^ k : Bˣ) : B) =
          AddMonoidAlgebra.single (Finsupp.single () k) (AddMonoidAlgebra.coeff (c : B) 0) := by
        obtain ⟨z, hz⟩ := c.2
        rw [← hz, halg z, LaurentRing.val_unitX_zpow () k, AddMonoidAlgebra.single_mul_single,
          zero_add, mul_one]; simp
      rw [Subsemiring.skewLaurentSum_apply, Finsupp.sum]; simp_rw [hbody]
      rw [AddMonoidAlgebra.coeff_sum, ← Finsupp.lapply_apply (R := ℕ), map_sum]
      by_cases hm_s : m ∈ f.support
      · rw [Finset.sum_eq_single_of_mem m hm_s fun k _ hne ↦ by
          simp [(Finsupp.single_injective ()).ne hne]]; simp
      · rw [Finset.sum_eq_zero fun k hk ↦ by
          simp [(Finsupp.single_injective ()).ne (fun hkm : k = m ↦ hm_s (hkm ▸ hk))],
          Finsupp.notMem_support_iff.mp hm_s]; rfl
    have hm := congrArg (fun p : B ↦ AddMonoidAlgebra.coeff p (Finsupp.single () m)) h
    rw [heval, heval] at hm
    obtain ⟨z₁, hz₁⟩ := (f₁ m).2; obtain ⟨z₂, hz₂⟩ := (f₂ m).2
    have hz : z₁ = z₂ := Int.cast_injective (α := ℚ)
      (by rw [← hz₁, ← hz₂, halg, halg] at hm; simpa using hm)
    rw [← hz₁, ← hz₂, hz]
  have hnorm (u : Bˣ) : ConjAct.toConjAct u • C = C := by
    ext; simp [Subsemiring.mem_smul_pointwise_iff_exists, ConjAct.units_smul_def, mul_comm,
      mul_assoc]
  have hiff (a : ℤ) {s : ℕ} (hs : 0 < s) :
      (a : B) * ((x ^ (-(s : ℤ)) : Bˣ) : B) ∈ C.laurentAdjoin (E * x⁻¹) ↔
        ∃ z : ℤ, a = z * (2 : ℤ) ^ s := by
    have hE_val : (E : B) = 2 := map_ofNat (algebraMap ℚ B) 2
    have hP (r : ℕ) : ((exchangeProduct x E r : Bˣ) : B) = (2 : B) ^ r := by
      rw [exchangeProduct_of_commute (Commute.all x E), Units.val_pow_eq_pow_val, hE_val]
    let ca : C := ⟨(a : B), a, map_intCast _ a⟩
    have hf : (a : B) * ((x ^ (-(s : ℤ)) : Bˣ) : B) =
        C.skewLaurentSum x (Finsupp.single (-(s : ℤ)) ca) := by simp [ca]
    rw [hf, Subsemiring.mem_laurentAdjoin_mul_inv_iff (hnorm x) (hnorm E)
      ⟨2, by rw [map_ofNat, hE_val]⟩ hinj]
    refine ⟨fun hall ↦ ?_, fun ⟨z, hz⟩ r _ ↦ ?_⟩
    · obtain ⟨⟨_, z, rfl⟩, hz⟩ := hall s hs
      rw [Finsupp.single_eq_same, hP] at hz
      have hev := congrArg (LaurentRing.aeval (R := ℚ) fun _ : Unit ↦ (1 : ℚˣ)) hz
      dsimp only [ca] at hev
      rw [map_intCast, map_mul, eq_intCast, map_intCast, map_pow, map_ofNat] at hev
      exact ⟨z, by exact_mod_cast hev⟩
    · subst hz; by_cases hrs : r = s
      · subst hrs; exact ⟨⟨(z : B), z, map_intCast _ z⟩, by
          rw [Finsupp.single_eq_same, hP]; dsimp only [ca]; push_cast; rfl⟩
      · exact ⟨0, by simp [Finsupp.single_eq_of_ne (by omega : -(r : ℤ) ≠ -(s : ℤ))]⟩
  refine ⟨Subsemiring.mem_inf.mpr ⟨mul_mem (C.le_laurentAdjoin x ⟨2, map_ofNat _ 2⟩)
      (C.coe_inv_mem_laurentAdjoin x), ?_⟩,
    Subsemiring.mem_inf.mpr ⟨mul_mem (C.le_laurentAdjoin x ⟨4, map_ofNat _ 4⟩)
      (C.coe_zpow_mem_laurentAdjoin x (-2)), ?_⟩, ?_, ?_⟩
  · simpa [zpow_neg_one] using (hiff 2 (s := 1) (by omega)).mpr ⟨1, rfl⟩
  · simpa using (hiff 4 (s := 2) (by omega)).mpr ⟨1, rfl⟩
  · intro h
    obtain ⟨_, hz⟩ := (hiff 1 (s := 1) (by omega)).mp (by simpa [zpow_neg_one] using h); omega
  · intro h; obtain ⟨_, hz⟩ := (hiff 2 (s := 2) (by omega)).mp (by simpa using h); omega
end Checks
end TauCeti

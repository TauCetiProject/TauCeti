/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.ResidueProduct
public import TauCeti.Algebra.Vertex.NormalOrder
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.Algebra.Vertex.FormalDistribution
import Mathlib.Algebra.Ring.Commute
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Cofinite
import Mathlib.Tactic.Abel

/-!
# Dong's lemma for vertex operators

Dong's lemma asserts that if fields `A`, `B`, `C` on an `R`-module `V` are pairwise local of orders
`r₁`, `r₂`, `r₃`, then every nonnegative residue product `Res_x (x - z)ⁿ [A(x), B(z)]` and the
normal-ordered product `:A(z) B(z):` are local with `C(w)` of order `r₁ + r₂ + r₃`, over any
commutative ring `R`.

## Main results

* `VertexOperator.IsLocalOfOrder.nonnegResidueProduct_left`, `nonnegResidueProduct_right`: Dong's
  lemma for nonnegative residue products.
* `VertexOperator.IsLocalOfOrder.normalOrder_left`, `normalOrder_right`: Dong's lemma for
  normal-ordered products.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §3.2 (Lemma 3.2, Dong's lemma).
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), Lemma 2.3.5.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.3.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset Filter TauCeti

namespace VertexOperator

section DongAux

variable {M : Type*} [AddCommGroup M]

private abbrev Dist3 (M : Type*) := ℤ → ℤ → ℤ → M

private def mulSubZW : AddMonoid.End (Dist3 M) :=
  AddMonoidHom.mk' (fun F a b c ↦ F a (b + 1) c - F a b (c + 1)) fun _ _ ↦ by ext; simp; abel
private def mulSubZX : AddMonoid.End (Dist3 M) :=
  AddMonoidHom.mk' (fun F a b c ↦ F a (b + 1) c - F (a + 1) b c) fun _ _ ↦ by ext; simp; abel
private def mulSubXW : AddMonoid.End (Dist3 M) :=
  AddMonoidHom.mk' (fun F a b c ↦ F (a + 1) b c - F a b (c + 1)) fun _ _ ↦ by ext; simp; abel
private abbrev swapXY (F : Dist3 M) : Dist3 M := fun a b c ↦ F b a c

@[simp] private theorem mulSubZW_apply (F : Dist3 M) (a b c : ℤ) :
    mulSubZW F a b c = F a (b + 1) c - F a b (c + 1) := rfl
@[simp] private theorem mulSubZX_apply (F : Dist3 M) (a b c : ℤ) :
    mulSubZX F a b c = F a (b + 1) c - F (a + 1) b c := rfl
@[simp] private theorem mulSubXW_apply (F : Dist3 M) (a b c : ℤ) :
    mulSubXW F a b c = F (a + 1) b c - F a b (c + 1) := rfl

private theorem mulSubZW_eq_add : (mulSubZW : AddMonoid.End (Dist3 M)) = mulSubZX + mulSubXW := by
  ext F a b c; exact (sub_add_sub_cancel _ _ _).symm

private theorem commute_mulSubZX_mulSubXW :
    Commute (mulSubZX : AddMonoid.End (Dist3 M)) mulSubXW := by
  ext F a b c; simp [AddMonoid.End.coe_mul]; abel

private theorem commute_mulSubZW_mulSubXW :
    Commute (mulSubZW : AddMonoid.End (Dist3 M)) mulSubXW :=
  mulSubZW_eq_add (M := M) ▸ commute_mulSubZX_mulSubXW.add_left (.refl _)

private theorem commute_mulSubZX_mulSubZW :
    Commute (mulSubZX : AddMonoid.End (Dist3 M)) mulSubZW :=
  mulSubZW_eq_add (M := M) ▸ (Commute.refl _).add_right commute_mulSubZX_mulSubXW

private theorem mulSubZW_pow_apply (k : ℕ) (F : Dist3 M) (a b c : ℤ) :
    ((mulSubZW ^ k) F) a b c = ((FormalDistribution.mulSub ^ k) (fun b' c' ↦ F a b' c')) b c := by
  simpa only [AddMonoid.End.coe_pow] using congrFun (congrFun (Function.Semiconj.iterate_right
    (f := fun H : Dist3 M ↦ fun b' c' ↦ H a b' c') (fun _ ↦ by ext; simp) k F) b) c

private theorem mulSubXW_pow_apply (k : ℕ) (F : Dist3 M) (a b c : ℤ) :
    ((mulSubXW ^ k) F) a b c = ((FormalDistribution.mulSub ^ k) (fun a' c' ↦ F a' b c')) a c := by
  simpa only [AddMonoid.End.coe_pow] using congrFun (congrFun (Function.Semiconj.iterate_right
    (f := fun H : Dist3 M ↦ fun a' c' ↦ H a' b c') (fun _ ↦ by ext; simp) k F) a) c

private theorem mulSubZX_pow_apply (k : ℕ) (F : Dist3 M) (a b c : ℤ) :
    ((mulSubZX ^ k) F) a b c = ((FormalDistribution.mulSub ^ k) (fun b' a' ↦ F a' b' c)) b a := by
  simpa only [AddMonoid.End.coe_pow] using congrFun (congrFun (Function.Semiconj.iterate_right
    (f := fun H : Dist3 M ↦ fun b' a' ↦ H a' b' c) (fun _ ↦ by ext; simp) k F) b) a

private def GoodOn (p : ℕ → ℤ) (q : ℤ → ℕ → ℤ) (F : Dist3 M) : Prop :=
  ∀ b c : ℤ, ∀ᶠ i : ℕ in atTop, F (p i) (q b i) c = 0

private def diagOn (p : ℕ → ℤ) (q : ℤ → ℕ → ℤ) (F : Dist3 M) : FormalDistribution M :=
  fun b c ↦ ∑ᶠ i : ℕ, F (p i) (q b i) c

private theorem pow_preserves {P : Dist3 M → Prop} (D : AddMonoid.End (Dist3 M))
    (hD : ∀ {F}, P F → P (D F)) (k : ℕ) {F : Dist3 M} (hF : P F) : P ((D ^ k) F) := by
  rw [AddMonoid.End.coe_pow]; exact Set.MapsTo.iterate (s := {F | P F}) (fun _ h ↦ hD h) k hF

private theorem diagOn_nsmul {p : ℕ → ℤ} {q : ℤ → ℕ → ℤ} {F : Dist3 M} (n : ℕ)
    (hF : GoodOn p q F) : diagOn p q (n • F) = n • diagOn p q F :=
  funext fun b ↦ funext fun c ↦
    (smul_finsum' n (Filter.eventually_cofinite.mp (Nat.cofinite_eq_atTop.symm ▸ hF b c))).symm

private theorem diagOn_sum {ι : Type*} {p : ℕ → ℤ} {q : ℤ → ℕ → ℤ} {s : Finset ι} {f : ι → Dist3 M}
    (hf : ∀ x ∈ s, GoodOn p q (f x)) : diagOn p q (∑ x ∈ s, f x) = ∑ x ∈ s, diagOn p q (f x) :=
  funext fun b ↦ funext fun c ↦ by
    simpa only [diagOn, Finset.sum_apply] using finsum_sum_comm s (fun i x ↦ f x (p i) (q b i) c)
      fun x hx ↦ Filter.eventually_cofinite.mp (Nat.cofinite_eq_atTop.symm ▸ hf x hx b c)

private theorem GoodOn.mulSubZW {p : ℕ → ℤ} {q : ℤ → ℕ → ℤ} (hq : ∀ b i, q (b + 1) i = q b i + 1)
    {F : Dist3 M} (hF : GoodOn p q F) : GoodOn p q (mulSubZW F) :=
  fun b c ↦ ((hF (b + 1) c).and (hF b (c + 1))).mono fun _ ⟨h₁, h₂⟩ ↦ by
    rw [mulSubZW_apply, ← hq, h₁, h₂, sub_zero]

private theorem mulSub_pow_diagOn {p : ℕ → ℤ} {q : ℤ → ℕ → ℤ}
    (hq : ∀ b i, q (b + 1) i = q b i + 1) (k : ℕ) {F : Dist3 M} (hF : GoodOn p q F) :
    (FormalDistribution.mulSub ^ k) (diagOn p q F) = diagOn p q ((mulSubZW ^ k) F) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply, ih]
    have hFk := pow_preserves mulSubZW (fun h ↦ h.mulSubZW hq) k hF
    ext b c
    rw [FormalDistribution.mulSub_apply, diagOn, diagOn, diagOn, ← finsum_sub_distrib
      (Filter.eventually_cofinite.mp (Nat.cofinite_eq_atTop.symm ▸ hFk (b + 1) c))
      (Filter.eventually_cofinite.mp (Nat.cofinite_eq_atTop.symm ▸ hFk b (c + 1)))]
    exact finsum_congr fun i ↦ by rw [hq, mulSubZW_apply]

private abbrev GoodPlus (F : Dist3 M) : Prop := GoodOn (fun i ↦ -(i : ℤ) - 1) (fun b i ↦ b + i) F
private abbrev GoodMinus (G : Dist3 M) : Prop := GoodOn (fun i ↦ (i : ℤ)) (fun b i ↦ b - i - 1) G
private abbrev diagPlus (F : Dist3 M) := diagOn (fun i ↦ -(i : ℤ) - 1) (fun b i ↦ b + i) F
private abbrev diagMinus (G : Dist3 M) := diagOn (fun i ↦ (i : ℤ)) (fun b i ↦ b - i - 1) G

private theorem goodPlus_shift {F : Dist3 M} (hF : GoodPlus F) (b c : ℤ) :
    ∀ᶠ i : ℕ in atTop, F (-(i : ℤ) - 1 + 1) (b + i) c = 0 :=
  (eventually_atTop.mp (hF (b + 1) c)).elim fun N hN ↦ eventually_atTop.mpr ⟨N + 1, fun i hi ↦ by
    simpa only [show -((i - 1 : ℕ) : ℤ) - 1 = -(i : ℤ) - 1 + 1 by omega,
      show b + 1 + ((i - 1 : ℕ) : ℤ) = b + i by omega] using hN (i - 1) (by omega)⟩

private theorem goodMinus_shift {G : Dist3 M} (hG : GoodMinus G) (b c : ℤ) :
    ∀ᶠ i : ℕ in atTop, G ((i : ℤ) + 1) (b - i - 1) c = 0 :=
  (eventually_atTop.mp (hG (b + 1) c)).elim fun N hN ↦ eventually_atTop.mpr ⟨N, fun i hi ↦ by
    simpa only [show ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 by omega,
      show b + 1 - ((i : ℤ) + 1) - 1 = b - i - 1 by omega] using hN (i + 1) (by omega)⟩

private theorem diagPlus_mulSubZX {F : Dist3 M} (hF : GoodPlus F) (b c : ℤ) :
    diagPlus (mulSubZX F) b c = -F 0 b c := by
  let w (i : ℕ) := F (-(i : ℤ)) (b + i) c
  have hw : Function.HasFiniteSupport w := Filter.eventually_cofinite.mp <|
    Nat.cofinite_eq_atTop.symm ▸ (goodPlus_shift hF b c).mono fun i hi ↦ by
      simpa only [sub_add_cancel] using hi
  rw [diagPlus, diagOn, finsum_congr fun i : ℕ ↦ show mulSubZX F (-(i : ℤ) - 1) (b + i) c =
      -(w i - w (i + 1)) by simp only [mulSubZX_apply, w, neg_sub]; congr 2 <;> push_cast <;> omega,
    finsum_neg_distrib, TauCeti.finsum_sub_add_one hw]; simp [w]

private theorem diagMinus_mulSubZX {G : Dist3 M} (hG : GoodMinus G) (b c : ℤ) :
    diagMinus (mulSubZX G) b c = G 0 b c := by
  let z (i : ℕ) := G (i : ℤ) ((b + 1) - i - 1) c
  have hz : Function.HasFiniteSupport z :=
    Filter.eventually_cofinite.mp (Nat.cofinite_eq_atTop.symm ▸ hG (b + 1) c)
  simpa [diagMinus, diagOn, z] using (finsum_congr fun i : ℕ ↦
    show mulSubZX G (i : ℤ) (b - i - 1) c = z i - z (i + 1) by
      simp only [mulSubZX_apply, z]; congr 2 <;> push_cast <;> omega).trans
    (TauCeti.finsum_sub_add_one hz)

private def dongTerm (r₂ p q : ℕ) : AddMonoid.End (Dist3 M) :=
  mulSubZX ^ p * mulSubXW ^ q * mulSubZW ^ r₂

private theorem mulSubZW_pow_apply_eq_sum_dongTerm (r₁ r₂ r₃ : ℕ) (H : Dist3 M) :
    (mulSubZW ^ (r₁ + r₂ + r₃)) H =
      ∑ pq ∈ antidiagonal (r₁ + r₃), (r₁ + r₃).choose pq.1 • dongTerm r₂ pq.1 pq.2 H := by
  have hpow : (mulSubZW : AddMonoid.End (Dist3 M)) ^ (r₁ + r₂ + r₃) =
      ∑ pq ∈ antidiagonal (r₁ + r₃), (r₁ + r₃).choose pq.1 • dongTerm r₂ pq.1 pq.2 := by
    rw [show r₁ + r₂ + r₃ = (r₁ + r₃) + r₂ by omega, pow_add, mulSubZW_eq_add,
      commute_mulSubZX_mulSubXW.add_pow', sum_mul]
    exact sum_congr rfl fun pq _ ↦ by rw [smul_mul_assoc, ← mulSubZW_eq_add, dongTerm]
  rw [hpow]; exact map_sum (AddMonoidHom.eval H) _ _

private theorem dongTerm_eq_zero_of_le_right {H : Dist3 M} {r₂ r₃ p q : ℕ}
    (hH : (mulSubZW ^ r₂) ((mulSubXW ^ r₃) H) = 0) (hq : r₃ ≤ q) : dongTerm r₂ p q H = 0 := by
  dsimp only [dongTerm]
  rw [show q = (q - r₃) + r₃ by omega, pow_add, mul_assoc (mulSubZX ^ p),
    mul_assoc (mulSubXW ^ (q - r₃)), (commute_mulSubZW_mulSubXW.pow_pow r₂ r₃).symm.eq]
  simp only [AddMonoid.End.coe_mul, Function.comp_apply, hH, map_zero]

private theorem dongTerm_eq_zero_of_le_left {H : Dist3 M} {r₁ r₂ p q : ℕ}
    (hH : (mulSubZX ^ r₁) H = 0) (hp : r₁ ≤ p) : dongTerm r₂ p q H = 0 := by
  dsimp only [dongTerm]
  have hc : Commute (mulSubZX ^ r₁)
      ((mulSubZX ^ (p - r₁) * mulSubXW ^ q * mulSubZW ^ r₂ : AddMonoid.End (Dist3 M))) :=
    ((Commute.pow_pow_self mulSubZX r₁ (p - r₁)).mul_right
      (commute_mulSubZX_mulSubXW.pow_pow r₁ q)).mul_right (commute_mulSubZX_mulSubZW.pow_pow r₁ r₂)
  rw [show p = r₁ + (p - r₁) by omega, pow_add, mul_assoc (mulSubZX ^ r₁),
    mul_assoc (mulSubZX ^ r₁), hc.eq, AddMonoid.End.coe_mul, Function.comp_apply, hH, map_zero]

private theorem GoodOn.dongTerm {p : ℕ → ℤ} {q : ℤ → ℕ → ℤ} (hq : ∀ b i, q (b + 1) i = q b i + 1)
    (hsh : ∀ {F : Dist3 M}, GoodOn p q F → ∀ b c, ∀ᶠ i : ℕ in atTop, F (p i + 1) (q b i) c = 0)
    {F : Dist3 M} (hF : GoodOn p q F) (r₂ a b : ℕ) : GoodOn p q (dongTerm r₂ a b F) := by
  simp only [VertexOperator.dongTerm, AddMonoid.End.coe_mul, Function.comp_apply]
  refine pow_preserves (P := GoodOn p q) mulSubZX (fun h b c ↦ ((h (b + 1) c).and (hsh h b c)).mono
      fun _ ⟨h₁, h₂⟩ ↦ by rw [mulSubZX_apply, ← hq, h₁, h₂, sub_zero]) a <|
    pow_preserves (P := GoodOn p q) mulSubXW (fun h b c ↦ ((hsh h b c).and (h b (c + 1))).mono
      fun _ ⟨h₁, h₂⟩ ↦ by rw [mulSubXW_apply, h₁, h₂, sub_zero]) b <|
    pow_preserves (P := GoodOn p q) VertexOperator.mulSubZW (fun h ↦ h.mulSubZW hq) r₂ hF

private theorem mulSubZW_pow_sub_eq_zero {Φ Ψ : Dist3 M} {r₁ r₂ r₃ : ℕ}
    (hAB : (mulSubZX ^ r₁) (Φ - Ψ) = 0) (hΦBC : (mulSubZW ^ r₂) ((mulSubXW ^ r₃) Φ) = 0)
    (hΨBC : (mulSubZW ^ r₂) ((mulSubXW ^ r₃) Ψ) = 0) :
    (mulSubZW ^ (r₁ + r₂ + r₃)) (Φ - Ψ) = 0 := by
  rw [mulSubZW_pow_apply_eq_sum_dongTerm]
  refine sum_eq_zero fun pq hpq ↦ ?_
  by_cases hq : r₃ ≤ pq.2
  · rw [map_sub, dongTerm_eq_zero_of_le_right hΦBC hq,
      dongTerm_eq_zero_of_le_right hΨBC hq, sub_zero, smul_zero]
  · rw [dongTerm_eq_zero_of_le_left hAB (by have := mem_antidiagonal.mp hpq; omega), smul_zero]

private theorem mulSub_pow_diagPlus_add_diagMinus_eq_zero {Φ Ψ : Dist3 M} {r₁ r₂ r₃ : ℕ}
    (hΦ : GoodPlus Φ) (hΨ : GoodMinus Ψ) (hAB : (mulSubZX ^ r₁) (Φ - Ψ) = 0)
    (hΦBC : (mulSubZW ^ r₂) ((mulSubXW ^ r₃) Φ) = 0)
    (hΨBC : (mulSubZW ^ r₂) ((mulSubXW ^ r₃) Ψ) = 0) :
    (FormalDistribution.mulSub ^ (r₁ + r₂ + r₃)) (diagPlus Φ + diagMinus Ψ) = 0 := by
  have hP (a b : ℕ) := hΦ.dongTerm (fun _ _ ↦ by omega) goodPlus_shift r₂ a b
  have hM (a b : ℕ) := hΨ.dongTerm (fun _ _ ↦ by omega) goodMinus_shift r₂ a b
  rw [map_add, mulSub_pow_diagOn (fun _ _ ↦ by omega) _ hΦ,
    mulSub_pow_diagOn (fun _ _ ↦ by omega) _ hΨ, mulSubZW_pow_apply_eq_sum_dongTerm,
    mulSubZW_pow_apply_eq_sum_dongTerm,
    diagOn_sum fun pq _ b c ↦ (hP pq.1 pq.2 b c).mono fun _ h ↦ by simp [h],
    diagOn_sum fun pq _ b c ↦ (hM pq.1 pq.2 b c).mono fun _ h ↦ by simp [h], ← sum_add_distrib]
  refine sum_eq_zero fun pq hpq ↦ ?_
  rw [diagOn_nsmul _ (hP pq.1 pq.2), diagOn_nsmul _ (hM pq.1 pq.2), ← smul_add]
  by_cases hq : r₃ ≤ pq.2
  · rw [dongTerm_eq_zero_of_le_right hΦBC hq, dongTerm_eq_zero_of_le_right hΨBC hq]
    ext; simp [diagOn]
  · obtain ⟨p', hp', hle⟩ : ∃ p', pq.1 = p' + 1 ∧ r₁ ≤ p' :=
      ⟨pq.1 - 1, by have := mem_antidiagonal.mp hpq; omega⟩
    have hstep (H : Dist3 M) : dongTerm r₂ pq.1 pq.2 H = mulSubZX (dongTerm r₂ p' pq.2 H) := by
      simp only [dongTerm, hp', pow_succ', mul_assoc mulSubZX, AddMonoid.End.coe_mul,
        Function.comp_apply]
    ext b c
    have hzero : dongTerm r₂ p' pq.2 Φ 0 b c = dongTerm r₂ p' pq.2 Ψ 0 b c := sub_eq_zero.mp <| by
      simpa only [map_sub, Pi.sub_apply, Pi.zero_apply] using congrFun (congrFun (congrFun
        (dongTerm_eq_zero_of_le_left (r₂ := r₂) (q := pq.2) hAB hle) 0) b) c
    simp only [Pi.smul_apply, Pi.add_apply, Pi.zero_apply, hstep,
      diagPlus_mulSubZX (hP p' pq.2), diagMinus_mulSubZX (hM p' pq.2), hzero, neg_add_cancel,
      smul_zero]

end DongAux

namespace IsLocalOfOrder

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable {A B C : VertexOperator R V} {r₁ r₂ r₃ : ℕ}

private def dongPhi (A B C : VertexOperator R V) (v : V) : Dist3 V :=
  fun a b c ↦ (A[[a]]) ((B[[b]]) ((C[[c]]) v)) - (C[[c]]) ((A[[a]]) ((B[[b]]) v))

private theorem dongPhi_goodPlus (A B C : VertexOperator R V) (v : V) :
    GoodPlus (dongPhi A B C v) := fun b c ↦ by
  obtain ⟨N₁, hN₁⟩ := B.exists_forall_ncoeff_apply_eq_zero ((C[[c]]) v)
  obtain ⟨N₂, hN₂⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  exact eventually_atTop.mpr ⟨(max (N₁ : ℤ) N₂ - b).toNat, fun i hi ↦ by
    simp [dongPhi, hN₁ (b + i) (by omega), hN₂ (b + i) (by omega)]⟩

private theorem dongPhi_swap_goodMinus (A B C : VertexOperator R V) (v : V) :
    GoodMinus (swapXY (dongPhi B A C v)) := fun b c ↦ by
  obtain ⟨N₁, hN₁⟩ := A.exists_forall_ncoeff_apply_eq_zero ((C[[c]]) v)
  obtain ⟨N₂, hN₂⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  exact eventually_atTop.mpr ⟨max N₁ N₂, fun i hi ↦ by
    simp [dongPhi, hN₁ i (by omega), hN₂ i (by omega)]⟩

private theorem mulSub_pow_eval_end (k : ℕ) (L : FormalDistribution (Module.End R V))
    (p : Module.End R V) (w : V) :
    (FormalDistribution.mulSub ^ k) (fun m n ↦ p ((L m n) w)) =
      fun m n ↦ p (((FormalDistribution.mulSub ^ k) L m n) w) := by
  ext m n; simp only [FormalDistribution.mulSub_pow_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_nsmul, map_zsmul]

private theorem isLocalOfOrder_of_commutatorDistribution_apply {X C : VertexOperator R V} {N : ℕ}
    (h : ∀ v : V,
      (FormalDistribution.mulSub ^ N) (fun b c ↦ (X.commutatorDistribution C b c) v) = 0) :
    X.IsLocalOfOrder C N := by
  rw [isLocalOfOrder_iff_mulSub_pow_eq_zero]; ext b c v
  have := congrFun (congrFun (mulSub_pow_eval_end N (X.commutatorDistribution C) 1 v) b) c
  simpa only [one_apply_eq_self, h v, Pi.zero_apply, LinearMap.zero_apply] using this.symm

private theorem mulSubZX_pow_dongPhi_sub (hAB : A.IsLocalOfOrder B r₁) (C : VertexOperator R V)
    (v : V) : (mulSubZX ^ r₁) (dongPhi A B C v - swapXY (dongPhi B A C v)) = 0 := by
  have hloc := (isLocalOfOrder_iff_mulSub_pow_eq_zero B A r₁).mp hAB.symm
  ext a b c; rw [mulSubZX_pow_apply]
  have hf : (fun b' a' ↦ (dongPhi A B C v - swapXY (dongPhi B A C v)) a' b' c) =
      (fun b' a' ↦ (C[[c]]) ((B.commutatorDistribution A b' a') v)) -
        fun b' a' ↦ (1 : Module.End R V) ((B.commutatorDistribution A b' a') ((C[[c]]) v)) := by
    ext b' a'; simp only [Pi.sub_apply, dongPhi, commutatorDistribution_apply,
      LinearMap.sub_apply, mul_apply_eq_comp, one_apply_eq_self, map_sub]; abel
  rw [hf, map_sub, mulSub_pow_eval_end, mulSub_pow_eval_end, hloc]; simp

private theorem mulSubZW_mulSubXW_dongPhi_eq_zero (hBC : B.IsLocalOfOrder C r₂)
    (hAC : A.IsLocalOfOrder C r₃) (v : V) :
    (mulSubZW ^ r₂) ((mulSubXW ^ r₃) (dongPhi A B C v)) = 0 := by
  let Φ₁ : Dist3 V := fun a b c ↦ (A[[a]]) ((B.commutatorDistribution C b c) v)
  let Φ₂ : Dist3 V := fun a b c ↦
    (1 : Module.End R V) ((A.commutatorDistribution C a c) ((B[[b]]) v))
  have hsplit : dongPhi A B C v = Φ₁ + Φ₂ := funext fun a ↦ funext fun b ↦ funext fun c ↦ by
    simp only [dongPhi, Φ₁, Φ₂, Pi.add_apply, commutatorDistribution_apply,
      LinearMap.sub_apply, mul_apply_eq_comp, one_apply_eq_self, map_sub]; abel
  have h₁ : (mulSubZW ^ r₂) Φ₁ = 0 := funext fun a ↦ funext fun b ↦ funext fun c ↦ by
    rw [mulSubZW_pow_apply,
      congrFun (congrFun (mulSub_pow_eval_end r₂ (B.commutatorDistribution C) (A[[a]]) v) b) c,
      (isLocalOfOrder_iff_mulSub_pow_eq_zero B C r₂).mp hBC]; simp
  have h₂ : (mulSubXW ^ r₃) Φ₂ = 0 := funext fun a ↦ funext fun b ↦ funext fun c ↦ by
    rw [mulSubXW_pow_apply,
      congrFun (congrFun (mulSub_pow_eval_end r₃ (A.commutatorDistribution C) 1 ((B[[b]]) v)) a) c,
      (isLocalOfOrder_iff_mulSub_pow_eq_zero A C r₃).mp hAC]; simp
  rw [hsplit, map_add, map_add, h₂, map_zero, add_zero]
  simpa only [AddMonoid.End.coe_mul, Function.comp_apply, h₁, map_zero] using
    congrArg (fun D : AddMonoid.End (Dist3 V) ↦ D Φ₁) (commute_mulSubZW_mulSubXW.pow_pow r₂ r₃).eq

private theorem mulSubZW_mulSubXW_dongPhi_swap_eq_zero (hBC : B.IsLocalOfOrder C r₂)
    (hAC : A.IsLocalOfOrder C r₃) (v : V) :
    (mulSubZW ^ r₂) ((mulSubXW ^ r₃) (swapXY (dongPhi B A C v))) = 0 := by
  have h1 := Function.Semiconj.iterate_right (f := swapXY) (ga := mulSubZW) (gb := mulSubXW)
    (fun _ ↦ rfl) r₃ (dongPhi B A C v)
  have h2 := Function.Semiconj.iterate_right (f := swapXY) (ga := mulSubXW) (gb := mulSubZW)
    (fun _ ↦ rfl) r₂ ((mulSubZW ^ r₃) (dongPhi B A C v))
  have hcomm := congrArg (fun D : AddMonoid.End (Dist3 V) ↦ D (dongPhi B A C v))
    (commute_mulSubZW_mulSubXW.pow_pow r₃ r₂).symm.eq
  have h0 := mulSubZW_mulSubXW_dongPhi_eq_zero hAC hBC v
  simp only [AddMonoid.End.coe_pow, AddMonoid.End.coe_mul, Function.comp_apply] at h1 h2 hcomm h0 ⊢
  rw [← h1, ← h2, hcomm, h0]; rfl

/-- **Dong's lemma** for nonnegative residue products (left form): if `(A, B)`, `(B, C)` and
`(A, C)` are local of orders `r₁`, `r₂`, `r₃`, then `nonnegResidueProduct n A B` is local with `C`
of order `r₁ + r₂ + r₃`. -/
theorem nonnegResidueProduct_left (hAB : A.IsLocalOfOrder B r₁) (hBC : B.IsLocalOfOrder C r₂)
    (hAC : A.IsLocalOfOrder C r₃) (n : ℕ) :
    (nonnegResidueProduct n A B).IsLocalOfOrder C (r₁ + r₂ + r₃) :=
  isLocalOfOrder_of_commutatorDistribution_apply fun v ↦ by
    let Δ : Dist3 V := dongPhi A B C v - swapXY (dongPhi B A C v)
    rw [show (fun b' c' ↦ ((nonnegResidueProduct n A B).commutatorDistribution C b' c') v) =
        ∑ ij ∈ antidiagonal n, n.choose ij.1 • (-1 : ℤ) ^ ij.2 •
          fun b' c' ↦ Δ ij.1 (b' + ij.2) c' by
      ext b' c'
      simp only [commutatorDistribution_apply, ncoeff_nonnegResidueProduct, LinearMap.sub_apply,
        mul_apply_eq_comp, LinearMap.sum_apply, map_sum, Finset.sum_apply, ← sum_sub_distrib]
      exact sum_congr rfl fun ij _ ↦ by
        simp only [LinearMap.smul_apply, LinearMap.sub_apply, mul_apply_eq_comp, map_nsmul,
          map_zsmul, map_sub, Pi.smul_apply, ← smul_sub, Δ, Pi.sub_apply, dongPhi]
        congr 2; abel, map_sum]
    refine sum_eq_zero fun ij _ ↦ ?_
    rw [map_nsmul, map_zsmul]; ext b c
    have h0 := congrFun (congrFun (congrFun (mulSubZW_pow_sub_eq_zero
      (mulSubZX_pow_dongPhi_sub hAB C v) (mulSubZW_mulSubXW_dongPhi_eq_zero hBC hAC v)
      (mulSubZW_mulSubXW_dongPhi_swap_eq_zero hBC hAC v)) ij.1) (b + ij.2)) c
    rw [mulSubZW_pow_apply] at h0
    simp only [Pi.smul_apply, Pi.zero_apply, FormalDistribution.mulSub_pow_apply] at h0 ⊢
    rw [sum_congr rfl fun kl _ ↦ by rw [show b + (kl.1 : ℤ) + ij.2 = b + ij.2 + kl.1 by omega],
      h0, smul_zero, smul_zero]

/-- **Dong's lemma** for nonnegative residue products (right form). -/
theorem nonnegResidueProduct_right (hCA : C.IsLocalOfOrder A r₃) (hCB : C.IsLocalOfOrder B r₂)
    (hAB : A.IsLocalOfOrder B r₁) (n : ℕ) :
    C.IsLocalOfOrder (nonnegResidueProduct n A B) (r₁ + r₂ + r₃) :=
  (hAB.nonnegResidueProduct_left hCB.symm hCA.symm n).symm

/-- **Dong's lemma** for normal-ordered products (left form): if `(A, B)`, `(B, C)` and `(A, C)`
are local of orders `r₁`, `r₂`, `r₃`, then `normalOrder A B` is local with `C` of order
`r₁ + r₂ + r₃`. -/
theorem normalOrder_left (hAB : A.IsLocalOfOrder B r₁) (hBC : B.IsLocalOfOrder C r₂)
    (hAC : A.IsLocalOfOrder C r₃) : (normalOrder A B).IsLocalOfOrder C (r₁ + r₂ + r₃) :=
  isLocalOfOrder_of_commutatorDistribution_apply fun v ↦ by
    rw [show (fun b' c' ↦ ((normalOrder A B).commutatorDistribution C b' c') v) =
        diagPlus (dongPhi A B C v) + diagMinus (swapXY (dongPhi B A C v)) by
      ext b' c'
      obtain ⟨P₁, hP₁⟩ := B.exists_forall_ncoeff_apply_eq_zero ((C[[c']]) v)
      obtain ⟨P₂, hP₂⟩ := B.exists_forall_ncoeff_apply_eq_zero v
      obtain ⟨Q₁, hQ₁⟩ := A.exists_forall_ncoeff_apply_eq_zero ((C[[c']]) v)
      obtain ⟨Q₂, hQ₂⟩ := A.exists_forall_ncoeff_apply_eq_zero v
      let P := (max (P₁ : ℤ) P₂ - b').toNat; let Q := max Q₁ Q₂
      simp only [commutatorDistribution_apply, LinearMap.sub_apply, mul_apply_eq_comp,
        ncoeff_normalOrder, Pi.add_apply, diagPlus, diagMinus, diagOn]
      rw [normalOrderCoeff_eq_sum A B b' ((C[[c']]) v) (P := P) (Q := Q)
          (fun _ _ ↦ hP₁ _ (by omega)) (fun _ _ ↦ hQ₁ _ (by omega)),
        normalOrderCoeff_eq_sum A B b' v (P := P) (Q := Q)
          (fun _ _ ↦ hP₂ _ (by omega)) (fun _ _ ↦ hQ₂ _ (by omega)),
        TauCeti.finsum_eq_sum_range_of_zero (N := P) (fun i _ ↦ by
          simp [dongPhi, hP₁ (b' + i) (by omega), hP₂ (b' + i) (by omega)]),
        TauCeti.finsum_eq_sum_range_of_zero (N := Q) (fun i _ ↦ by
          simp [dongPhi, hQ₁ i (by omega), hQ₂ i (by omega)])]
      simp only [map_add, map_sum, dongPhi, sum_sub_distrib]; abel]
    exact mulSub_pow_diagPlus_add_diagMinus_eq_zero (dongPhi_goodPlus A B C v)
      (dongPhi_swap_goodMinus A B C v) (mulSubZX_pow_dongPhi_sub hAB C v)
      (mulSubZW_mulSubXW_dongPhi_eq_zero hBC hAC v)
      (mulSubZW_mulSubXW_dongPhi_swap_eq_zero hBC hAC v)

/-- **Dong's lemma** for normal-ordered products (right form). -/
theorem normalOrder_right (hCA : C.IsLocalOfOrder A r₃) (hCB : C.IsLocalOfOrder B r₂)
    (hAB : A.IsLocalOfOrder B r₁) : C.IsLocalOfOrder (normalOrder A B) (r₁ + r₂ + r₃) :=
  (hAB.normalOrder_left hCB.symm hCA.symm).symm

end IsLocalOfOrder

end VertexOperator

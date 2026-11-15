/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.ResidueProduct
public import TauCeti.Algebra.Vertex.NormalOrder
public import TauCeti.Algebra.Vertex.FormalDistribution
import Mathlib.Algebra.Ring.Commute
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module

/-!
# Dong's lemma for vertex operators

Dong's lemma asserts that if three fields `A`, `B`, `C` on an `R`-module `V` are pairwise local of
orders `r₁`, `r₂`, `r₃`, then every nonnegative residue product `Res_x (x - z)ⁿ [A(x), B(z)]` and
the normal-ordered product `:A(z) B(z):` are local with `C(w)` of order `r₁ + r₂ + r₃`.

Rather than multiplying three-variable Hahn series with incompatible support orders, we represent
three-field expressions on each vector `v : V` as three-variable formal distributions in `(x, z, w)`
acted on by the commuting difference operators of multiplication by `z - w`, `z - x`, and `x - w`.
No characteristic or division hypothesis on `R` is required. Together with locality of Hasse
derivatives, these results show that all integer `n`-th products of fields preserve mutual locality,
feeding both the Borcherds identity and the reconstruction of formal vertex algebras from generating
fields.

## Main results

* `VertexOperator.IsLocalOfOrder.nonnegResidueProduct_left`,
  `VertexOperator.IsLocalOfOrder.nonnegResidueProduct_right`: Dong's lemma for nonnegative residue
  products.
* `VertexOperator.IsLocalOfOrder.normalOrder_left`,
  `VertexOperator.IsLocalOfOrder.normalOrder_right`: Dong's lemma for normal-ordered products.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §3.2 (Lemma 3.2, Dong's lemma).
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), Lemma 2.3.5 (attributing the lemma to C. Dong).
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.3.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset Filter TauCeti

namespace VertexOperator

section DongAux

variable {M : Type*} [AddCommGroup M]

/-- Three-variable formal distributions `F a b c` in modes of `(x, z, w)`. -/
private abbrev Dist3 (M : Type*) := ℤ → ℤ → ℤ → M

/-- Multiplication of a three-variable distribution by `z - w`. -/
private def mulSubZW : AddMonoid.End (Dist3 M) where
  toFun F a b c := F a (b + 1) c - F a b (c + 1)
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp; abel

@[simp]
private theorem mulSubZW_apply (F : Dist3 M) (a b c : ℤ) :
    mulSubZW F a b c = F a (b + 1) c - F a b (c + 1) := (rfl)

/-- Multiplication of a three-variable distribution by `z - x`. -/
private def mulSubZX : AddMonoid.End (Dist3 M) where
  toFun F a b c := F a (b + 1) c - F (a + 1) b c
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp; abel

@[simp]
private theorem mulSubZX_apply (F : Dist3 M) (a b c : ℤ) :
    mulSubZX F a b c = F a (b + 1) c - F (a + 1) b c := (rfl)

/-- Multiplication of a three-variable distribution by `x - w`. -/
private def mulSubXW : AddMonoid.End (Dist3 M) where
  toFun F a b c := F (a + 1) b c - F a b (c + 1)
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp; abel

@[simp]
private theorem mulSubXW_apply (F : Dist3 M) (a b c : ℤ) :
    mulSubXW F a b c = F (a + 1) b c - F a b (c + 1) := (rfl)

private theorem mulSubZW_eq_add :
    (mulSubZW : AddMonoid.End (Dist3 M)) = mulSubZX + mulSubXW := by
  ext F a b c
  change mulSubZW F a b c = mulSubZX F a b c + mulSubXW F a b c
  simp

private theorem commute_mulSubZX_mulSubXW :
    Commute (mulSubZX : AddMonoid.End (Dist3 M)) mulSubXW := by
  ext F a b c
  simp only [AddMonoid.End.coe_mul, Function.comp_apply, mulSubZX_apply, mulSubXW_apply]
  abel

private theorem commute_mulSubZW_mulSubXW :
    Commute (mulSubZW : AddMonoid.End (Dist3 M)) mulSubXW := by
  rw [mulSubZW_eq_add]
  exact commute_mulSubZX_mulSubXW.add_left (Commute.refl _)

private theorem commute_mulSubZX_mulSubZW :
    Commute (mulSubZX : AddMonoid.End (Dist3 M)) mulSubZW := by
  rw [mulSubZW_eq_add]
  exact (Commute.refl _).add_right commute_mulSubZX_mulSubXW

private theorem mulSubZW_pow_apply (k : ℕ) (F : Dist3 M) (a b c : ℤ) :
    ((mulSubZW ^ k) F) a b c =
      ((FormalDistribution.mulSub ^ k) (fun b' c' ↦ F a b' c')) b c := by
  induction k generalizing b c with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply,
      pow_succ', AddMonoid.End.coe_mul, Function.comp_apply, mulSubZW_apply,
      FormalDistribution.mulSub_apply, ih, ih]

private theorem mulSubXW_pow_apply (k : ℕ) (F : Dist3 M) (a b c : ℤ) :
    ((mulSubXW ^ k) F) a b c =
      ((FormalDistribution.mulSub ^ k) (fun a' c' ↦ F a' b c')) a c := by
  induction k generalizing a c with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply,
      pow_succ', AddMonoid.End.coe_mul, Function.comp_apply, mulSubXW_apply,
      FormalDistribution.mulSub_apply, ih, ih]

private theorem mulSubZX_pow_apply (k : ℕ) (F : Dist3 M) (a b c : ℤ) :
    ((mulSubZX ^ k) F) a b c =
      ((FormalDistribution.mulSub ^ k) (fun b' a' ↦ F a' b' c)) b a := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply,
      pow_succ', AddMonoid.End.coe_mul, Function.comp_apply, mulSubZX_apply,
      FormalDistribution.mulSub_apply, ih, ih]

/-- Distributions whose negative-`x` diagonal `i ↦ F (-i - 1) (b + i) c` is eventually zero. -/
private def GoodPlus (M : Type*) [AddCommGroup M] : AddSubgroup (Dist3 M) where
  carrier := {F | ∀ b c : ℤ, ∀ᶠ i : ℕ in atTop, F (-(i : ℤ) - 1) (b + i) c = 0}
  zero_mem' _ _ := Eventually.of_forall fun _ ↦ rfl
  add_mem' {F G} hF hG b c := ((hF b c).and (hG b c)).mono fun _ ⟨h₁, h₂⟩ ↦ by simp [h₁, h₂]
  neg_mem' {F} hF b c := (hF b c).mono fun _ h ↦ by simp [h]

/-- Distributions whose nonnegative-`x` diagonal `i ↦ G i (b - i - 1) c` is eventually zero. -/
private def GoodMinus (M : Type*) [AddCommGroup M] : AddSubgroup (Dist3 M) where
  carrier := {G | ∀ b c : ℤ, ∀ᶠ i : ℕ in atTop, G (i : ℤ) (b - i - 1) c = 0}
  zero_mem' _ _ := Eventually.of_forall fun _ ↦ rfl
  add_mem' {F G} hF hG b c := ((hF b c).and (hG b c)).mono fun _ ⟨h₁, h₂⟩ ↦ by simp [h₁, h₂]
  neg_mem' {F} hF b c := (hF b c).mono fun _ h ↦ by simp [h]

private theorem finite_support_of_goodPlus {F : Dist3 M} (hF : F ∈ GoodPlus M) (b c : ℤ) :
    (Function.support fun i : ℕ ↦ F (-(i : ℤ) - 1) (b + i) c).Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hF b c)
  refine (finite_toSet (range N)).subset fun i hi ↦ ?_
  simp only [mem_coe, mem_range]
  by_contra! h
  exact hi (hN i h)

private theorem finite_support_of_goodMinus {G : Dist3 M} (hG : G ∈ GoodMinus M) (b c : ℤ) :
    (Function.support fun i : ℕ ↦ G (i : ℤ) (b - i - 1) c).Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hG b c)
  refine (finite_toSet (range N)).subset fun i hi ↦ ?_
  simp only [mem_coe, mem_range]
  by_contra! h
  exact hi (hN i h)

private theorem mulSubZX_mem_goodPlus {F : Dist3 M} (hF : F ∈ GoodPlus M) :
    mulSubZX F ∈ GoodPlus M := by
  intro b c
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hF (b + 1) c)
  refine eventually_atTop.mpr ⟨N + 1, fun i hi ↦ ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [mulSubZX_apply]
  have h₁ : F (-((j + 1 : ℕ) : ℤ) - 1) (b + ↑(j + 1) + 1) c = 0 := by
    have e : b + ((j + 1 : ℕ) : ℤ) + 1 = (b + 1) + ((j + 1 : ℕ) : ℤ) := by omega
    rw [e]
    exact hN (j + 1) (by omega)
  have h₂ : F (-((j + 1 : ℕ) : ℤ) - 1 + 1) (b + ↑(j + 1)) c = 0 := by
    have e₁ : -((j + 1 : ℕ) : ℤ) - 1 + 1 = -(j : ℤ) - 1 := by omega
    have e₂ : b + ((j + 1 : ℕ) : ℤ) = (b + 1) + (j : ℤ) := by omega
    rw [e₁, e₂]
    exact hN j (by omega)
  rw [h₁, h₂, sub_zero]

private theorem mulSubXW_mem_goodPlus {F : Dist3 M} (hF : F ∈ GoodPlus M) :
    mulSubXW F ∈ GoodPlus M := by
  intro b c
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hF (b + 1) c)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hF b (c + 1))
  refine eventually_atTop.mpr ⟨max N₁ N₂ + 1, fun i hi ↦ ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [mulSubXW_apply]
  have h₁ : F (-((j + 1 : ℕ) : ℤ) - 1 + 1) (b + ↑(j + 1)) c = 0 := by
    have e₁ : -((j + 1 : ℕ) : ℤ) - 1 + 1 = -(j : ℤ) - 1 := by omega
    have e₂ : b + ((j + 1 : ℕ) : ℤ) = (b + 1) + (j : ℤ) := by omega
    rw [e₁, e₂]
    exact hN₁ j (by omega)
  have h₂ : F (-((j + 1 : ℕ) : ℤ) - 1) (b + ↑(j + 1)) (c + 1) = 0 :=
    hN₂ (j + 1) (by omega)
  rw [h₁, h₂, sub_zero]

private theorem mulSubZW_mem_goodPlus {F : Dist3 M} (hF : F ∈ GoodPlus M) :
    mulSubZW F ∈ GoodPlus M := by
  rw [mulSubZW_eq_add]
  exact (GoodPlus M).add_mem (mulSubZX_mem_goodPlus hF) (mulSubXW_mem_goodPlus hF)

private theorem mulSubZX_mem_goodMinus {G : Dist3 M} (hG : G ∈ GoodMinus M) :
    mulSubZX G ∈ GoodMinus M := by
  intro b c
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hG (b + 1) c)
  refine eventually_atTop.mpr ⟨N, fun i hi ↦ ?_⟩
  rw [mulSubZX_apply]
  have h₁ : G (i : ℤ) (b - i - 1 + 1) c = 0 := by
    have e : b - (i : ℤ) - 1 + 1 = (b + 1) - (i : ℤ) - 1 := by omega
    rw [e]
    exact hN i hi
  have h₂ : G ((i : ℤ) + 1) (b - i - 1) c = 0 := by
    have e₁ : (i : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) := by omega
    have e₂ : b - (i : ℤ) - 1 = (b + 1) - ((i + 1 : ℕ) : ℤ) - 1 := by omega
    rw [e₁, e₂]
    exact hN (i + 1) (by omega)
  rw [h₁, h₂, sub_zero]

private theorem mulSubXW_mem_goodMinus {G : Dist3 M} (hG : G ∈ GoodMinus M) :
    mulSubXW G ∈ GoodMinus M := by
  intro b c
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hG (b + 1) c)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hG b (c + 1))
  refine eventually_atTop.mpr ⟨max N₁ N₂, fun i hi ↦ ?_⟩
  rw [mulSubXW_apply]
  have h₁ : G ((i : ℤ) + 1) (b - i - 1) c = 0 := by
    have e₁ : (i : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) := by omega
    have e₂ : b - (i : ℤ) - 1 = (b + 1) - ((i + 1 : ℕ) : ℤ) - 1 := by omega
    rw [e₁, e₂]
    exact hN₁ (i + 1) (by omega)
  have h₂ : G (i : ℤ) (b - i - 1) (c + 1) = 0 := hN₂ i (by omega)
  rw [h₁, h₂, sub_zero]

private theorem mulSubZW_mem_goodMinus {G : Dist3 M} (hG : G ∈ GoodMinus M) :
    mulSubZW G ∈ GoodMinus M := by
  rw [mulSubZW_eq_add]
  exact (GoodMinus M).add_mem (mulSubZX_mem_goodMinus hG) (mulSubXW_mem_goodMinus hG)

private theorem pow_mem_goodPlus {D : AddMonoid.End (Dist3 M)}
    (hD : ∀ {F}, F ∈ GoodPlus M → D F ∈ GoodPlus M) (k : ℕ) {F : Dist3 M}
    (hF : F ∈ GoodPlus M) : (D ^ k) F ∈ GoodPlus M := by
  induction k with
  | zero => exact hF
  | succ k ih =>
    rw [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply]
    exact hD ih

private theorem pow_mem_goodMinus {D : AddMonoid.End (Dist3 M)}
    (hD : ∀ {G}, G ∈ GoodMinus M → D G ∈ GoodMinus M) (k : ℕ) {G : Dist3 M}
    (hG : G ∈ GoodMinus M) : (D ^ k) G ∈ GoodMinus M := by
  induction k with
  | zero => exact hG
  | succ k ih =>
    rw [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply]
    exact hD ih

/-- Left normal-ordering contraction `F ↦ ∑ᶠ i : ℕ, F (-i - 1) (b + i) c` on `GoodPlus`. -/
private def diagPlus : GoodPlus M →+ FormalDistribution M where
  toFun F b c := ∑ᶠ i : ℕ, F.1 (-(i : ℤ) - 1) (b + i) c
  map_zero' := by ext; simp
  map_add' F G := by
    ext b c
    exact finsum_add_distrib (finite_support_of_goodPlus F.2 b c)
      (finite_support_of_goodPlus G.2 b c)

@[simp]
private theorem diagPlus_apply (F : GoodPlus M) (b c : ℤ) :
    diagPlus F b c = ∑ᶠ i : ℕ, F.1 (-(i : ℤ) - 1) (b + i) c := (rfl)

/-- Right normal-ordering contraction `G ↦ ∑ᶠ i : ℕ, G i (b - i - 1) c` on `GoodMinus`. -/
private def diagMinus : GoodMinus M →+ FormalDistribution M where
  toFun G b c := ∑ᶠ i : ℕ, G.1 (i : ℤ) (b - i - 1) c
  map_zero' := by ext; simp
  map_add' F G := by
    ext b c
    exact finsum_add_distrib (finite_support_of_goodMinus F.2 b c)
      (finite_support_of_goodMinus G.2 b c)

@[simp]
private theorem diagMinus_apply (G : GoodMinus M) (b c : ℤ) :
    diagMinus G b c = ∑ᶠ i : ℕ, G.1 (i : ℤ) (b - i - 1) c := (rfl)

private theorem mulSub_diagPlus {F : Dist3 M} (hF : F ∈ GoodPlus M) :
    FormalDistribution.mulSub (diagPlus ⟨F, hF⟩) =
      diagPlus ⟨mulSubZW F, mulSubZW_mem_goodPlus hF⟩ := by
  ext b c
  simp only [FormalDistribution.mulSub_apply, diagPlus_apply,
    ← finsum_sub_distrib (finite_support_of_goodPlus hF (b + 1) c)
      (finite_support_of_goodPlus hF b (c + 1))]
  refine finsum_congr fun i ↦ ?_
  have e : b + 1 + (i : ℤ) = b + i + 1 := by omega
  rw [e, mulSubZW_apply]

private theorem mulSub_pow_diagPlus (k : ℕ) {F : Dist3 M} (hF : F ∈ GoodPlus M) :
    (FormalDistribution.mulSub ^ k) (diagPlus ⟨F, hF⟩) =
      diagPlus ⟨(mulSubZW ^ k) F, pow_mem_goodPlus (@mulSubZW_mem_goodPlus M _) k hF⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply, ih, mulSub_diagPlus]
    congr 1
    apply Subtype.ext
    dsimp only
    rw [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply]

private theorem mulSub_diagMinus {G : Dist3 M} (hG : G ∈ GoodMinus M) :
    FormalDistribution.mulSub (diagMinus ⟨G, hG⟩) =
      diagMinus ⟨mulSubZW G, mulSubZW_mem_goodMinus hG⟩ := by
  ext b c
  simp only [FormalDistribution.mulSub_apply, diagMinus_apply,
    ← finsum_sub_distrib (finite_support_of_goodMinus hG (b + 1) c)
      (finite_support_of_goodMinus hG b (c + 1))]
  refine finsum_congr fun i ↦ ?_
  have e : b + 1 - (i : ℤ) - 1 = b - i - 1 + 1 := by omega
  rw [e, mulSubZW_apply]

private theorem mulSub_pow_diagMinus (k : ℕ) {G : Dist3 M} (hG : G ∈ GoodMinus M) :
    (FormalDistribution.mulSub ^ k) (diagMinus ⟨G, hG⟩) =
      diagMinus ⟨(mulSubZW ^ k) G, pow_mem_goodMinus (@mulSubZW_mem_goodMinus M _) k hG⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply, ih, mulSub_diagMinus]
    congr 1
    apply Subtype.ext
    dsimp only
    rw [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply]

/-- Telescoping on the negative-`x` half: `diagPlus (mulSubZX F) b c = - F 0 b c`. -/
private theorem diagPlus_mulSubZX {F : Dist3 M} (hF : F ∈ GoodPlus M) (b c : ℤ) :
    diagPlus ⟨mulSubZX F, mulSubZX_mem_goodPlus hF⟩ b c = -F 0 b c := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hF (b + 1) c)
  let w : ℕ → M := fun
    | 0 => F 0 b c
    | j + 1 => F (-(j : ℤ) - 1) ((b + 1) + j) c
  have hstep (i : ℕ) : mulSubZX F (-(i : ℤ) - 1) (b + i) c = w (i + 1) - w i := by
    cases i with
    | zero => simp [w]
    | succ j =>
      rw [mulSubZX_apply]
      have e₁ : b + ((j + 1 : ℕ) : ℤ) + 1 = (b + 1) + ((j + 1 : ℕ) : ℤ) := by omega
      have e₂ : -((j + 1 : ℕ) : ℤ) - 1 + 1 = -(j : ℤ) - 1 := by omega
      have e₃ : b + ((j + 1 : ℕ) : ℤ) = (b + 1) + (j : ℤ) := by omega
      rw [e₁, e₂, e₃]
  have hsupp : (Function.support fun i : ℕ ↦ mulSubZX F (-(i : ℤ) - 1) (b + i) c) ⊆
      range (N + 1) := by
    intro i hi
    simp only [mem_coe, mem_range]
    by_contra! h
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    refine hi ?_
    dsimp only
    rw [hstep, show w (j + 1 + 1) = 0 from hN (j + 1) (by omega),
      show w (j + 1) = 0 from hN j (by omega), sub_self]
  rw [diagPlus_apply, finsum_eq_sum_of_support_subset _ hsupp,
    sum_congr rfl fun i _ ↦ hstep i, sum_range_sub (f := w) (N + 1),
    show w (N + 1) = 0 from hN N le_rfl, zero_sub]

/-- Telescoping on the nonnegative-`x` half: `diagMinus (mulSubZX G) b c = G 0 b c`. -/
private theorem diagMinus_mulSubZX {G : Dist3 M} (hG : G ∈ GoodMinus M) (b c : ℤ) :
    diagMinus ⟨mulSubZX G, mulSubZX_mem_goodMinus hG⟩ b c = G 0 b c := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hG (b + 1) c)
  let z : ℕ → M := fun i ↦ G (i : ℤ) ((b + 1) - i - 1) c
  have hstep (i : ℕ) : mulSubZX G (i : ℤ) (b - i - 1) c = z i - z (i + 1) := by
    rw [mulSubZX_apply]
    have e₁ : b - (i : ℤ) - 1 + 1 = (b + 1) - (i : ℤ) - 1 := by omega
    have e₂ : b - (i : ℤ) - 1 = (b + 1) - ((i + 1 : ℕ) : ℤ) - 1 := by omega
    rw [e₁, e₂]
    rfl
  have hsupp : (Function.support fun i : ℕ ↦ mulSubZX G (i : ℤ) (b - i - 1) c) ⊆ range N := by
    intro i hi
    simp only [mem_coe, mem_range]
    by_contra! h
    refine hi ?_
    dsimp only
    rw [hstep, show z i = 0 from hN i h, show z (i + 1) = 0 from hN (i + 1) (by omega), sub_self]
  rw [diagMinus_apply, finsum_eq_sum_of_support_subset _ hsupp,
    sum_congr rfl fun i _ ↦ hstep i, sum_range_sub' (f := z) N]
  cases N with
  | zero =>
    have h₀ : z 0 = 0 := hN 0 le_rfl
    simpa [z] using h₀.symm
  | succ n =>
    rw [show z (n + 1) = 0 from hN (n + 1) (by omega), sub_zero]
    simp [z]

/-- Monomial difference operator `(z - x)ᵖ (x - w)ᵍ (z - w)^{r₂}` in the binomial expansion of
`(z - w)^{r₁ + r₂ + r₃}`. -/
private def dongTerm (r₂ p q : ℕ) : AddMonoid.End (Dist3 M) :=
  mulSubZX ^ p * mulSubXW ^ q * mulSubZW ^ r₂

private theorem mulSubZW_pow_eq_sum_dongTerm (r₁ r₂ r₃ : ℕ) :
    (mulSubZW : AddMonoid.End (Dist3 M)) ^ (r₁ + r₂ + r₃) =
      ∑ pq ∈ antidiagonal (r₁ + r₃), (r₁ + r₃).choose pq.1 • dongTerm r₂ pq.1 pq.2 := by
  rw [show r₁ + r₂ + r₃ = (r₁ + r₃) + r₂ by omega, pow_add, mulSubZW_eq_add,
    commute_mulSubZX_mulSubXW.add_pow', sum_mul]
  refine sum_congr rfl fun pq _ ↦ ?_
  rw [smul_mul_assoc, ← mulSubZW_eq_add, dongTerm]

private theorem dongTerm_eq_zero_of_le_right {H : Dist3 M} {r₂ r₃ p q : ℕ}
    (hH : (mulSubZW ^ r₂) ((mulSubXW ^ r₃) H) = 0) (hq : r₃ ≤ q) :
    dongTerm r₂ p q H = 0 := by
  dsimp only [dongTerm]
  rw [show q = (q - r₃) + r₃ by omega, pow_add, mul_assoc (mulSubZX ^ p),
    mul_assoc (mulSubXW ^ (q - r₃)),
    (commute_mulSubZW_mulSubXW.pow_pow r₂ r₃).symm.eq]
  simp only [AddMonoid.End.coe_mul, Function.comp_apply, hH, map_zero]

private theorem dongTerm_eq_zero_of_le_left {H : Dist3 M} {r₁ r₂ p q : ℕ}
    (hH : (mulSubZX ^ r₁) H = 0) (hp : r₁ ≤ p) :
    dongTerm r₂ p q H = 0 := by
  dsimp only [dongTerm]
  have hc : Commute (mulSubZX ^ r₁)
      ((mulSubZX ^ (p - r₁) * mulSubXW ^ q * mulSubZW ^ r₂ : AddMonoid.End (Dist3 M))) :=
    (((Commute.pow_pow_self mulSubZX r₁ (p - r₁)).mul_right
      (commute_mulSubZX_mulSubXW.pow_pow r₁ q)).mul_right
      (commute_mulSubZX_mulSubZW.pow_pow r₁ r₂))
  rw [show p = r₁ + (p - r₁) by omega, pow_add, mul_assoc (mulSubZX ^ r₁),
    mul_assoc (mulSubZX ^ r₁), hc.eq, AddMonoid.End.coe_mul, Function.comp_apply, hH, map_zero]

private theorem dongTerm_mem_goodPlus {Φ : Dist3 M} (hΦ : Φ ∈ GoodPlus M) (r₂ p q : ℕ) :
    dongTerm r₂ p q Φ ∈ GoodPlus M := by
  dsimp only [dongTerm]
  simp only [AddMonoid.End.coe_mul, Function.comp_apply]
  exact pow_mem_goodPlus (@mulSubZX_mem_goodPlus M _) p
    (pow_mem_goodPlus (@mulSubXW_mem_goodPlus M _) q
      (pow_mem_goodPlus (@mulSubZW_mem_goodPlus M _) r₂ hΦ))

private theorem dongTerm_mem_goodMinus {Ψ : Dist3 M} (hΨ : Ψ ∈ GoodMinus M) (r₂ p q : ℕ) :
    dongTerm r₂ p q Ψ ∈ GoodMinus M := by
  dsimp only [dongTerm]
  simp only [AddMonoid.End.coe_mul, Function.comp_apply]
  exact pow_mem_goodMinus (@mulSubZX_mem_goodMinus M _) p
    (pow_mem_goodMinus (@mulSubXW_mem_goodMinus M _) q
      (pow_mem_goodMinus (@mulSubZW_mem_goodMinus M _) r₂ hΨ))

/-- Vanishing of `(z - w)^{r₁ + r₂ + r₃} (Φ - Ψ)` for nonnegative residue products in Dong's
lemma. -/
private theorem mulSubZW_pow_apply_eq_sum_dongTerm (r₁ r₂ r₃ : ℕ) (H : Dist3 M) :
    (mulSubZW ^ (r₁ + r₂ + r₃)) H =
      ∑ pq ∈ antidiagonal (r₁ + r₃), (r₁ + r₃).choose pq.1 • dongTerm r₂ pq.1 pq.2 H := by
  rw [mulSubZW_pow_eq_sum_dongTerm]
  exact map_sum (AddMonoidHom.eval H) _ _

private theorem mulSubZW_pow_sub_eq_zero {Φ Ψ : Dist3 M} {r₁ r₂ r₃ : ℕ}
    (hAB : (mulSubZX ^ r₁) (Φ - Ψ) = 0)
    (hΦBC : (mulSubZW ^ r₂) ((mulSubXW ^ r₃) Φ) = 0)
    (hΨBC : (mulSubZW ^ r₂) ((mulSubXW ^ r₃) Ψ) = 0) :
    (mulSubZW ^ (r₁ + r₂ + r₃)) (Φ - Ψ) = 0 := by
  rw [mulSubZW_pow_apply_eq_sum_dongTerm]
  refine sum_eq_zero fun pq hpq ↦ ?_
  by_cases hq : r₃ ≤ pq.2
  · rw [map_sub, dongTerm_eq_zero_of_le_right hΦBC hq,
      dongTerm_eq_zero_of_le_right hΨBC hq, sub_zero, smul_zero]
  · have hp : r₁ ≤ pq.1 := by have := mem_antidiagonal.mp hpq; omega
    rw [dongTerm_eq_zero_of_le_left hAB hp, smul_zero]

/-- Vanishing of `(z - w)^{r₁ + r₂ + r₃}` on `diagPlus Φ + diagMinus Ψ` for normal-ordered products
in Dong's lemma. -/
private theorem mulSub_pow_diagPlus_add_diagMinus_eq_zero {Φ Ψ : Dist3 M} {r₁ r₂ r₃ : ℕ}
    (hΦ : Φ ∈ GoodPlus M) (hΨ : Ψ ∈ GoodMinus M)
    (hAB : (mulSubZX ^ r₁) (Φ - Ψ) = 0)
    (hΦBC : (mulSubZW ^ r₂) ((mulSubXW ^ r₃) Φ) = 0)
    (hΨBC : (mulSubZW ^ r₂) ((mulSubXW ^ r₃) Ψ) = 0) :
    (FormalDistribution.mulSub ^ (r₁ + r₂ + r₃))
      (diagPlus ⟨Φ, hΦ⟩ + diagMinus ⟨Ψ, hΨ⟩) = 0 := by
  rw [map_add, mulSub_pow_diagPlus, mulSub_pow_diagMinus]
  have eqP : (⟨(mulSubZW ^ (r₁ + r₂ + r₃)) Φ,
      pow_mem_goodPlus (@mulSubZW_mem_goodPlus M _) _ hΦ⟩ : GoodPlus M) =
      ∑ pq ∈ antidiagonal (r₁ + r₃),
        (r₁ + r₃).choose pq.1 •
          ⟨dongTerm r₂ pq.1 pq.2 Φ, dongTerm_mem_goodPlus hΦ r₂ pq.1 pq.2⟩ := by
    apply Subtype.ext
    change (mulSubZW ^ (r₁ + r₂ + r₃)) Φ =
      (GoodPlus M).subtype (∑ pq ∈ antidiagonal (r₁ + r₃),
        (r₁ + r₃).choose pq.1 • ⟨dongTerm r₂ pq.1 pq.2 Φ, dongTerm_mem_goodPlus hΦ r₂ pq.1 pq.2⟩)
    rw [mulSubZW_pow_apply_eq_sum_dongTerm, map_sum]
    exact sum_congr rfl fun _ _ ↦ rfl
  have eqM : (⟨(mulSubZW ^ (r₁ + r₂ + r₃)) Ψ,
      pow_mem_goodMinus (@mulSubZW_mem_goodMinus M _) _ hΨ⟩ : GoodMinus M) =
      ∑ pq ∈ antidiagonal (r₁ + r₃),
        (r₁ + r₃).choose pq.1 •
          ⟨dongTerm r₂ pq.1 pq.2 Ψ, dongTerm_mem_goodMinus hΨ r₂ pq.1 pq.2⟩ := by
    apply Subtype.ext
    change (mulSubZW ^ (r₁ + r₂ + r₃)) Ψ =
      (GoodMinus M).subtype (∑ pq ∈ antidiagonal (r₁ + r₃),
        (r₁ + r₃).choose pq.1 • ⟨dongTerm r₂ pq.1 pq.2 Ψ, dongTerm_mem_goodMinus hΨ r₂ pq.1 pq.2⟩)
    rw [mulSubZW_pow_apply_eq_sum_dongTerm, map_sum]
    exact sum_congr rfl fun _ _ ↦ rfl
  rw [eqP, eqM, map_sum, map_sum, ← sum_add_distrib]
  refine sum_eq_zero fun pq hpq ↦ ?_
  rw [map_nsmul, map_nsmul, ← smul_add]
  by_cases hq : r₃ ≤ pq.2
  · rw [show (⟨dongTerm r₂ pq.1 pq.2 Φ, dongTerm_mem_goodPlus hΦ r₂ pq.1 pq.2⟩ : GoodPlus M) = 0
        from Subtype.ext (dongTerm_eq_zero_of_le_right hΦBC hq),
      show (⟨dongTerm r₂ pq.1 pq.2 Ψ, dongTerm_mem_goodMinus hΨ r₂ pq.1 pq.2⟩ : GoodMinus M) = 0
        from Subtype.ext (dongTerm_eq_zero_of_le_right hΨBC hq),
      map_zero, map_zero, add_zero, smul_zero]
  · obtain ⟨p', hp'⟩ : ∃ p', pq.1 = p' + 1 ∧ r₁ ≤ p' :=
      ⟨pq.1 - 1, by have := mem_antidiagonal.mp hpq; omega⟩
    ext b c
    simp only [Pi.add_apply, Pi.zero_apply, Pi.smul_apply]
    have stepP : (⟨dongTerm r₂ pq.1 pq.2 Φ, dongTerm_mem_goodPlus hΦ r₂ pq.1 pq.2⟩ : GoodPlus M) =
        ⟨mulSubZX (dongTerm r₂ p' pq.2 Φ),
          mulSubZX_mem_goodPlus (dongTerm_mem_goodPlus hΦ r₂ p' pq.2)⟩ := by
      apply Subtype.ext
      dsimp only [dongTerm]
      rw [hp'.1, pow_succ', mul_assoc mulSubZX, mul_assoc mulSubZX,
        AddMonoid.End.coe_mul, Function.comp_apply]
    have stepM : (⟨dongTerm r₂ pq.1 pq.2 Ψ, dongTerm_mem_goodMinus hΨ r₂ pq.1 pq.2⟩ : GoodMinus M) =
        ⟨mulSubZX (dongTerm r₂ p' pq.2 Ψ),
          mulSubZX_mem_goodMinus (dongTerm_mem_goodMinus hΨ r₂ p' pq.2)⟩ := by
      apply Subtype.ext
      dsimp only [dongTerm]
      rw [hp'.1, pow_succ', mul_assoc mulSubZX, mul_assoc mulSubZX,
        AddMonoid.End.coe_mul, Function.comp_apply]
    rw [stepP, stepM, diagPlus_mulSubZX (dongTerm_mem_goodPlus hΦ r₂ p' pq.2),
      diagMinus_mulSubZX (dongTerm_mem_goodMinus hΨ r₂ p' pq.2)]
    have hzero : dongTerm r₂ p' pq.2 Φ 0 b c = dongTerm r₂ p' pq.2 Ψ 0 b c := by
      have h := congrFun (congrFun (congrFun
        (dongTerm_eq_zero_of_le_left (r₂ := r₂) (q := pq.2) hAB hp'.2) 0) b) c
      rw [map_sub] at h
      exact sub_eq_zero.mp h
    rw [hzero, neg_add_cancel, smul_zero]

end DongAux

namespace IsLocalOfOrder

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable {A B C : VertexOperator R V} {r₁ r₂ r₃ : ℕ}

/-- Three-variable distribution `A₍ₐ₎ B₍ᵦ₎ C₍𝒸₎ v - C₍𝒸₎ A₍ₐ₎ B₍ᵦ₎ v` used in Dong's lemma. -/
private def dongPhi (A B C : VertexOperator R V) (v : V) : Dist3 V :=
  fun a b c ↦ (A[[a]]) ((B[[b]]) ((C[[c]]) v)) - (C[[c]]) ((A[[a]]) ((B[[b]]) v))

private theorem dongPhi_mem_goodPlus (A B C : VertexOperator R V) (v : V) :
    dongPhi A B C v ∈ GoodPlus V := by
  intro b c
  obtain ⟨N₁, hN₁⟩ := B.exists_forall_ncoeff_apply_eq_zero ((C[[c]]) v)
  obtain ⟨N₂, hN₂⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  refine eventually_atTop.mpr ⟨(max (N₁ : ℤ) N₂ - b).toNat, fun i hi ↦ ?_⟩
  simp [dongPhi, hN₁ (b + i) (by omega), hN₂ (b + i) (by omega)]

private theorem dongPhi_swap_mem_goodMinus (A B C : VertexOperator R V) (v : V) :
    (fun a b c ↦ dongPhi B A C v b a c) ∈ GoodMinus V := by
  intro b c
  obtain ⟨N₁, hN₁⟩ := A.exists_forall_ncoeff_apply_eq_zero ((C[[c]]) v)
  obtain ⟨N₂, hN₂⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  refine eventually_atTop.mpr ⟨max N₁ N₂, fun i hi ↦ ?_⟩
  simp [dongPhi, hN₁ i (by omega), hN₂ i (by omega)]

private theorem mulSub_pow_eval_end (k : ℕ) (L : FormalDistribution (Module.End R V))
    (p : Module.End R V) (w : V) :
    (FormalDistribution.mulSub ^ k) (fun m n ↦ p ((L m n) w)) =
      fun m n ↦ p (((FormalDistribution.mulSub ^ k) L m n) w) := by
  ext m n
  simp only [FormalDistribution.mulSub_pow_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_nsmul, map_zsmul]

private theorem mulSubZX_pow_dongPhi_sub (hAB : A.IsLocalOfOrder B r₁) (C : VertexOperator R V)
    (v : V) :
    (mulSubZX ^ r₁) (dongPhi A B C v - fun a b c ↦ dongPhi B A C v b a c) = 0 := by
  have hloc := (isLocalOfOrder_iff_mulSub_pow_eq_zero B A r₁).mp hAB.symm
  ext a b c
  rw [mulSubZX_pow_apply]
  let f : FormalDistribution V :=
    (fun b' a' ↦ (C[[c]]) ((B.commutatorDistribution A b' a') v)) -
      fun b' a' ↦ (1 : Module.End R V) ((B.commutatorDistribution A b' a') ((C[[c]]) v))
  have hf : (fun b' a' ↦ (dongPhi A B C v - fun a b c ↦ dongPhi B A C v b a c) a' b' c) = f := by
    ext b' a'
    simp only [Pi.sub_apply, dongPhi, f, commutatorDistribution_apply, LinearMap.sub_apply,
      mul_apply_eq_comp, one_apply_eq_self, map_sub]
    abel
  rw [hf, map_sub, mulSub_pow_eval_end, mulSub_pow_eval_end, hloc]
  simp

private theorem mulSubZW_mulSubXW_dongPhi_eq_zero (hBC : B.IsLocalOfOrder C r₂)
    (hAC : A.IsLocalOfOrder C r₃) (v : V) :
    (mulSubZW ^ r₂) ((mulSubXW ^ r₃) (dongPhi A B C v)) = 0 := by
  have hBC' := (isLocalOfOrder_iff_mulSub_pow_eq_zero B C r₂).mp hBC
  have hAC' := (isLocalOfOrder_iff_mulSub_pow_eq_zero A C r₃).mp hAC
  let Φ₁ : Dist3 V := fun a b c ↦ (A[[a]]) ((B.commutatorDistribution C b c) v)
  let Φ₂ : Dist3 V := fun a b c ↦ (1 : Module.End R V)
    ((A.commutatorDistribution C a c) ((B[[b]]) v))
  have hsplit : dongPhi A B C v = Φ₁ + Φ₂ := by
    ext a b c
    simp only [dongPhi, Φ₁, Φ₂, Pi.add_apply, commutatorDistribution_apply, LinearMap.sub_apply,
      mul_apply_eq_comp, one_apply_eq_self, map_sub]
    abel
  have h₁ : (mulSubZW ^ r₂) Φ₁ = 0 := by
    ext a b c
    rw [mulSubZW_pow_apply]
    have := congrFun (congrFun (mulSub_pow_eval_end r₂ (B.commutatorDistribution C) (A[[a]]) v) b) c
    rw [this, hBC']
    simp
  have h₂ : (mulSubXW ^ r₃) Φ₂ = 0 := by
    ext a b c
    rw [mulSubXW_pow_apply]
    have := congrFun (congrFun
      (mulSub_pow_eval_end r₃ (A.commutatorDistribution C) 1 ((B[[b]]) v)) a) c
    rw [this, hAC']
    simp
  have hcomm := congrArg (fun D : AddMonoid.End (Dist3 V) ↦ D Φ₁)
    (commute_mulSubZW_mulSubXW.pow_pow r₂ r₃).eq
  simp only [AddMonoid.End.coe_mul, Function.comp_apply] at hcomm
  rw [hsplit, map_add, map_add, h₂, map_zero, add_zero, hcomm, h₁, map_zero]

private theorem mulSubZW_mulSubXW_dongPhi_swap_eq_zero (hBC : B.IsLocalOfOrder C r₂)
    (hAC : A.IsLocalOfOrder C r₃) (v : V) :
    (mulSubZW ^ r₂) ((mulSubXW ^ r₃) (fun a b c ↦ dongPhi B A C v b a c)) = 0 := by
  have hBC' := (isLocalOfOrder_iff_mulSub_pow_eq_zero B C r₂).mp hBC
  have hAC' := (isLocalOfOrder_iff_mulSub_pow_eq_zero A C r₃).mp hAC
  let Ψ₁ : Dist3 V := fun a b c ↦ (B[[b]]) ((A.commutatorDistribution C a c) v)
  let Ψ₂ : Dist3 V := fun a b c ↦ (1 : Module.End R V)
    ((B.commutatorDistribution C b c) ((A[[a]]) v))
  have hsplit : (fun a b c ↦ dongPhi B A C v b a c) = Ψ₁ + Ψ₂ := by
    ext a b c
    simp only [dongPhi, Ψ₁, Ψ₂, Pi.add_apply, commutatorDistribution_apply, LinearMap.sub_apply,
      mul_apply_eq_comp, one_apply_eq_self, map_sub]
    abel
  have h₁ : (mulSubXW ^ r₃) Ψ₁ = 0 := by
    ext a b c
    rw [mulSubXW_pow_apply]
    have := congrFun (congrFun (mulSub_pow_eval_end r₃ (A.commutatorDistribution C) (B[[b]]) v) a) c
    rw [this, hAC']
    simp
  have h₂ : (mulSubZW ^ r₂) Ψ₂ = 0 := by
    ext a b c
    rw [mulSubZW_pow_apply]
    have := congrFun (congrFun
      (mulSub_pow_eval_end r₂ (B.commutatorDistribution C) 1 ((A[[a]]) v)) b) c
    rw [this, hBC']
    simp
  have hcomm := congrArg (fun D : AddMonoid.End (Dist3 V) ↦ D Ψ₂)
    (commute_mulSubZW_mulSubXW.pow_pow r₂ r₃).eq
  simp only [AddMonoid.End.coe_mul, Function.comp_apply] at hcomm
  rw [hsplit, map_add, map_add, h₁, map_zero, zero_add, hcomm, h₂, map_zero]

/-- **Dong's lemma** for nonnegative residue products (left form): if `(A, B)`, `(B, C)` and
`(A, C)` are local of orders `r₁`, `r₂`, `r₃`, then `nonnegResidueProduct n A B` is local with `C`
of order `r₁ + r₂ + r₃`. -/
theorem nonnegResidueProduct_left (hAB : A.IsLocalOfOrder B r₁) (hBC : B.IsLocalOfOrder C r₂)
    (hAC : A.IsLocalOfOrder C r₃) (n : ℕ) :
    (nonnegResidueProduct n A B).IsLocalOfOrder C (r₁ + r₂ + r₃) := by
  rw [isLocalOfOrder_iff_mulSub_pow_eq_zero]
  ext b c v
  have hd := mulSubZW_pow_sub_eq_zero (mulSubZX_pow_dongPhi_sub hAB C v)
    (mulSubZW_mulSubXW_dongPhi_eq_zero hBC hAC v)
    (mulSubZW_mulSubXW_dongPhi_swap_eq_zero hBC hAC v)
  let Δ : Dist3 V := dongPhi A B C v - fun a b c ↦ dongPhi B A C v b a c
  have hcomm :
      (fun b' c' ↦ ((nonnegResidueProduct n A B).commutatorDistribution C b' c') v) =
        ∑ ij ∈ antidiagonal n, n.choose ij.1 • (-1 : ℤ) ^ ij.2 •
          fun b' c' ↦ Δ ij.1 (b' + ij.2) c' := by
    ext b' c'
    rw [commutatorDistribution_apply, ncoeff_nonnegResidueProduct, LinearMap.sub_apply,
      mul_apply_eq_comp, mul_apply_eq_comp, LinearMap.sum_apply, LinearMap.sum_apply, map_sum,
      ← sum_sub_distrib, Finset.sum_apply, Finset.sum_apply]
    refine sum_congr rfl fun ij _ ↦ ?_
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, mul_apply_eq_comp, map_nsmul,
      map_zsmul, map_sub, Pi.smul_apply, ← smul_sub, Δ, Pi.sub_apply, dongPhi]
    congr 2
    abel
  have happ := congrFun (congrFun
    (mulSub_pow_eval_end (r₁ + r₂ + r₃) ((nonnegResidueProduct n A B).commutatorDistribution C)
      1 v) b) c
  simp only [one_apply_eq_self] at happ
  rw [← happ, hcomm, map_sum, Finset.sum_apply, Finset.sum_apply]
  simp only [Pi.zero_apply, LinearMap.zero_apply]
  refine sum_eq_zero fun ij _ ↦ ?_
  rw [map_nsmul, map_zsmul]
  simp only [Pi.smul_apply]
  have hshift :
      ((FormalDistribution.mulSub ^ (r₁ + r₂ + r₃)) (fun b' c' ↦ Δ ij.1 (b' + ij.2) c')) b c =
        ((mulSubZW ^ (r₁ + r₂ + r₃)) Δ) ij.1 (b + ij.2) c := by
    rw [mulSubZW_pow_apply]
    simp only [FormalDistribution.mulSub_pow_apply]
    refine sum_congr rfl fun kl _ ↦ ?_
    have e : b + (kl.1 : ℤ) + ij.2 = b + ij.2 + kl.1 := by omega
    rw [e]
  rw [hshift, show (mulSubZW ^ (r₁ + r₂ + r₃)) Δ = 0 from hd]
  simp

/-- **Dong's lemma** for nonnegative residue products (right form). -/
theorem nonnegResidueProduct_right (hCA : C.IsLocalOfOrder A r₃) (hCB : C.IsLocalOfOrder B r₂)
    (hAB : A.IsLocalOfOrder B r₁) (n : ℕ) :
    C.IsLocalOfOrder (nonnegResidueProduct n A B) (r₁ + r₂ + r₃) :=
  (hAB.nonnegResidueProduct_left hCB.symm hCA.symm n).symm

/-- **Dong's lemma** for normal-ordered products (left form): if `(A, B)`, `(B, C)` and `(A, C)`
are local of orders `r₁`, `r₂`, `r₃`, then `normalOrder A B` is local with `C` of order
`r₁ + r₂ + r₃`. -/
theorem normalOrder_left (hAB : A.IsLocalOfOrder B r₁) (hBC : B.IsLocalOfOrder C r₂)
    (hAC : A.IsLocalOfOrder C r₃) :
    (normalOrder A B).IsLocalOfOrder C (r₁ + r₂ + r₃) := by
  rw [isLocalOfOrder_iff_mulSub_pow_eq_zero]
  ext b c v
  have hd := mulSub_pow_diagPlus_add_diagMinus_eq_zero (dongPhi_mem_goodPlus A B C v)
    (dongPhi_swap_mem_goodMinus A B C v) (mulSubZX_pow_dongPhi_sub hAB C v)
    (mulSubZW_mulSubXW_dongPhi_eq_zero hBC hAC v)
    (mulSubZW_mulSubXW_dongPhi_swap_eq_zero hBC hAC v)
  have hcomm :
      (fun b' c' ↦ ((normalOrder A B).commutatorDistribution C b' c') v) =
        diagPlus ⟨dongPhi A B C v, dongPhi_mem_goodPlus A B C v⟩ +
          diagMinus ⟨fun a b c ↦ dongPhi B A C v b a c, dongPhi_swap_mem_goodMinus A B C v⟩ := by
    ext b' c'
    obtain ⟨P₁, hP₁⟩ := B.exists_forall_ncoeff_apply_eq_zero ((C[[c']]) v)
    obtain ⟨P₂, hP₂⟩ := B.exists_forall_ncoeff_apply_eq_zero v
    obtain ⟨Q₁, hQ₁⟩ := A.exists_forall_ncoeff_apply_eq_zero ((C[[c']]) v)
    obtain ⟨Q₂, hQ₂⟩ := A.exists_forall_ncoeff_apply_eq_zero v
    let P := (max (P₁ : ℤ) P₂ - b').toNat
    let Q := max Q₁ Q₂
    have cutB₁ (i : ℕ) (hi : P ≤ i) : (B[[b' + i]]) ((C[[c']]) v) = 0 := hP₁ _ (by omega)
    have cutB₂ (i : ℕ) (hi : P ≤ i) : (B[[b' + i]]) v = 0 := hP₂ _ (by omega)
    have cutA₁ (i : ℕ) (hi : Q ≤ i) : (A[[(i : ℤ)]]) ((C[[c']]) v) = 0 := hQ₁ _ (by omega)
    have cutA₂ (i : ℕ) (hi : Q ≤ i) : (A[[(i : ℤ)]]) v = 0 := hQ₂ _ (by omega)
    have suppP : (Function.support fun i : ℕ ↦ dongPhi A B C v (-(i : ℤ) - 1) (b' + i) c') ⊆
        range P := by
      intro i hi
      simp only [mem_coe, mem_range]
      by_contra! h
      exact hi (by simp [dongPhi, cutB₁ i h, cutB₂ i h])
    have suppM : (Function.support fun i : ℕ ↦ dongPhi B A C v (b' - i - 1) (i : ℤ) c') ⊆
        range Q := by
      intro i hi
      simp only [mem_coe, mem_range]
      by_contra! h
      exact hi (by simp [dongPhi, cutA₁ i h, cutA₂ i h])
    rw [commutatorDistribution_apply, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
      ncoeff_normalOrder, normalOrderCoeff_eq_sum A B b' ((C[[c']]) v) cutB₁ cutA₁,
      normalOrderCoeff_eq_sum A B b' v cutB₂ cutA₂, map_add, map_sum, map_sum,
      Pi.add_apply, Pi.add_apply, diagPlus_apply, diagMinus_apply,
      finsum_eq_sum_of_support_subset _ suppP, finsum_eq_sum_of_support_subset _ suppM]
    simp only [dongPhi, sum_sub_distrib]
    abel
  have happ := congrFun (congrFun
    (mulSub_pow_eval_end (r₁ + r₂ + r₃) ((normalOrder A B).commutatorDistribution C) 1 v) b) c
  simp only [one_apply_eq_self] at happ
  rw [← happ, hcomm]
  simpa using congrFun (congrFun hd b) c

/-- **Dong's lemma** for normal-ordered products (right form). -/
theorem normalOrder_right (hCA : C.IsLocalOfOrder A r₃) (hCB : C.IsLocalOfOrder B r₂)
    (hAB : A.IsLocalOfOrder B r₁) :
    C.IsLocalOfOrder (normalOrder A B) (r₁ + r₂ + r₃) :=
  (hAB.normalOrder_left hCB.symm hCA.symm).symm

end IsLocalOfOrder

end VertexOperator

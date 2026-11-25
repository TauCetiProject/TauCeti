/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import TauCeti.RingTheory.DennisStein.Relative

import Mathlib.Tactic.LinearCombination
import TauCeti.GroupTheory.QuotientGroup.KerEquiv
import TauCeti.RingTheory.Jacobson.Basic

/-!
# The lift-change sequence of Dennis–Stein groups

Let `g : B →+* B'` be a surjective homomorphism of commutative rings whose kernel `L` lies in the
Jacobson radical of `B`. This file proves that the sequence of Dennis–Stein groups

`D(B, L) → D(B) → D(B') → 0`

is exact, where the first map is the generator map
`TauCeti.RelativeDennisSteinGroup.toDennisSteinGroup` and the second is
`TauCeti.DennisSteinGroup.map g`. Equivalently, `D(B')` is the quotient of `D(B)` by the image of
the relative group.

The argument is a direct one from the relations D1–D3 and does not use any comparison with `K₂`.

* Every admissible pair of `B'` lifts to an admissible pair of `B`, since an element of `B` that is
  a unit modulo `L ⊆ Jac(B)` is a unit. This gives surjectivity.
* Two lifts of the same pair have symbols differing by the image of relative symbols. Changing the
  second entry of an admissible pair `(x, y)` by `l ∈ L` is the D2 relation
  `⟨x, y⟩ + ⟨x, l * (1 - x * y)⁻¹⟩ = ⟨x, y + l⟩`, whose middle term is a relative symbol; the first
  entry is changed in the same way after D1.
* Hence choosing lifts defines a map `D(B') → D(B) / im D(B, L)`, which respects D1–D3 because the
  lifted relations are again instances of D1–D3. It is inverse to the map induced by `g`, which
  proves exactness in the middle.

## Main results

* `TauCeti.DennisSteinGroup.map_surjective_of_ker_le_jacobson`: `D(B) → D(B')` is surjective.
* `TauCeti.DennisSteinGroup.exact_toDennisSteinGroup_map`: the sequence
  `D(B, L) → D(B) → D(B')` is exact.
* `TauCeti.DennisSteinGroup.quotientRangeEquiv`: `D(B) / im D(B, L) ≃+ D(B')`.

## References

* R. K. Dennis, M. R. Stein, *K₂ of radical ideals and semi-local rings*, in *Algebraic K-theory
  II*, Lecture Notes in Math. 342 (1973), Proposition 1.1 (the relations D1–D3).
* W. van der Kallen, H. Maazen, J. Stienstra, *A presentation for some K₂(n, R)*, Bull. Amer.
  Math. Soc. 81 (1975), 934–936, where this sequence reduces the local presentation of `K₂` to
  split radical pairs and to discrete valuation rings.
-/

public section

namespace TauCeti

namespace DennisSteinGroup

variable {B B' : Type*} [CommRing B] [CommRing B'] {g : B →+* B'}

/-- An element of `B` whose image under a surjection with kernel in the Jacobson radical is a
unit is itself a unit. -/
private theorem isUnit_of_isUnit_map (hg : Function.Surjective g)
    (hL : RingHom.ker g ≤ Ring.jacobson B) {x : B} (hx : IsUnit (g x)) : IsUnit x :=
  haveI : IsLocalHom g := (RingHom.isLocalHom_iff_ker_le_jacobson hg).2 hL
  isUnit_of_map_unit g x hx

variable (hg : Function.Surjective g) (hL : RingHom.ker g ≤ Ring.jacobson B)
include hg hL

/-- Changing the second entry of a pair within its class modulo the kernel changes the symbol by
the image of a relative symbol. -/
private theorem symbol_sub_symbol_mem_range_right {x y y₁ : B} (hy : g y = g y₁) :
    symbol x y - symbol x y₁ ∈
      (RelativeDennisSteinGroup.toDennisSteinGroup hL).range := by
  have hmap : g (1 - x * y) = g (1 - x * y₁) := by simp [hy]
  by_cases h : IsUnit (1 - x * y₁)
  · obtain ⟨u, hu⟩ := h
    -- `t = (y - y₁) * u⁻¹` lies in the kernel, and D2 for `(x, y₁)` and `(x, t)` reads
    -- `⟨x, y₁⟩ + ⟨x, t⟩ = ⟨x, y⟩`.
    set t : B := (y - y₁) * ↑u⁻¹ with ht_def
    have ht : t ∈ RingHom.ker g := by
      rw [RingHom.mem_ker, ht_def, map_mul, map_sub, hy, sub_self, zero_mul]
    have hxt : IsUnit (1 - x * t) :=
      Ideal.isUnit_one_sub_mul_of_le_jacobson hL (Or.inr ht)
    have hy' : y₁ + t - x * y₁ * t = y := by
      have : t * ↑u = y - y₁ := by rw [ht_def, mul_assoc, Units.inv_mul, mul_one]
      linear_combination this - t * hu
    refine ⟨RelativeDennisSteinGroup.symbol _ x t, ?_⟩
    rw [RelativeDennisSteinGroup.toDennisSteinGroup_symbol hL (Or.inr ht), eq_sub_iff_add_eq,
      add_comm, symbol_add_symbol ⟨u, hu⟩ hxt, hy']
  · have h' : ¬IsUnit (1 - x * y) := fun h' =>
      h (isUnit_of_isUnit_map hg hL (hmap ▸ h'.map g))
    rw [symbol_eq_zero_of_not_isUnit h, symbol_eq_zero_of_not_isUnit h', sub_zero]
    exact zero_mem _

/-- Two pairs congruent modulo the kernel have symbols differing by the image of the relative
group. -/
private theorem symbol_sub_symbol_mem_range {x y x₁ y₁ : B} (hx : g x = g x₁)
    (hy : g y = g y₁) :
    symbol x y - symbol x₁ y₁ ∈ (RelativeDennisSteinGroup.toDennisSteinGroup hL).range := by
  have h₁ := symbol_sub_symbol_mem_range_right hg hL (x := x) hy
  have h₂ := symbol_sub_symbol_mem_range_right hg hL (x := y₁) hx
  rw [symbol_swap x y₁, symbol_swap x₁ y₁, neg_sub_neg] at h₂
  have := sub_mem h₁ h₂
  rwa [sub_sub_sub_cancel_right] at this

/-- The symbol of chosen lifts, in the quotient of `D(B)` by the image of the relative group. -/
private noncomputable def liftSymbol (x y : B') :
    DennisSteinGroup B ⧸ (RelativeDennisSteinGroup.toDennisSteinGroup hL).range :=
  QuotientAddGroup.mk (symbol (Function.surjInv hg x) (Function.surjInv hg y))

private theorem liftSymbol_map (x y : B) :
    liftSymbol hg hL (g x) (g y) = QuotientAddGroup.mk (symbol x y) := by
  rw [liftSymbol, QuotientAddGroup.eq_iff_sub_mem, ← neg_mem_iff, neg_sub]
  exact symbol_sub_symbol_mem_range hg hL (Function.surjInv_eq hg _).symm
    (Function.surjInv_eq hg _).symm

/-- The inverse of the map `D(B) / im D(B, L) → D(B')` induced by `g`, sending `⟨x, y⟩` to the
class of the symbol of any lift. -/
private noncomputable def liftHom :
    DennisSteinGroup B' →+
      DennisSteinGroup B ⧸ (RelativeDennisSteinGroup.toDennisSteinGroup hL).range :=
  lift (liftSymbol hg hL)
    (fun x y _ => by
      obtain ⟨x, rfl⟩ := hg x
      obtain ⟨y, rfl⟩ := hg y
      rw [liftSymbol_map, liftSymbol_map, ← QuotientAddGroup.mk_add, symbol_add_symbol_swap,
        QuotientAddGroup.mk_zero])
    (fun x y z hy hz => by
      obtain ⟨x, rfl⟩ := hg x
      obtain ⟨y, rfl⟩ := hg y
      obtain ⟨z, rfl⟩ := hg z
      have hy' : IsUnit (1 - x * y) := isUnit_of_isUnit_map hg hL (by simpa using hy)
      have hz' : IsUnit (1 - x * z) := isUnit_of_isUnit_map hg hL (by simpa using hz)
      rw [liftSymbol_map, liftSymbol_map, ← QuotientAddGroup.mk_add, symbol_add_symbol hy' hz',
        ← liftSymbol_map hg hL]
      simp)
    (fun x y z _ => by
      obtain ⟨x, rfl⟩ := hg x
      obtain ⟨y, rfl⟩ := hg y
      obtain ⟨z, rfl⟩ := hg z
      simp only [← map_mul, liftSymbol_map]
      rw [← QuotientAddGroup.mk_add, symbol_mul_right])

private theorem liftHom_comp_map :
    (liftHom hg hL).comp (map g) = QuotientAddGroup.mk' _ := by
  ext x y h
  have h' : IsUnit (1 - g x * g y) := by simpa using h.map g
  simp [liftHom, h, h', liftSymbol_map]

/-- **Lifting Dennis–Stein symbols**: for a surjection `g : B →+* B'` of commutative rings whose
kernel lies in the Jacobson radical of `B`, the induced map `D(B) →+ D(B')` is surjective. -/
theorem map_surjective_of_ker_le_jacobson : Function.Surjective (map g) := by
  intro x
  induction x using induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | symbol x y h =>
    obtain ⟨x, rfl⟩ := hg x
    obtain ⟨y, rfl⟩ := hg y
    have h' : IsUnit (1 - x * y) := isUnit_of_isUnit_map hg hL (by simpa using h)
    exact ⟨symbol x y, map_symbol g h'⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ a b⟩
  | neg x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨-a, map_neg _ a⟩

/-- **The lift-change sequence** `D(B, L) → D(B) → D(B') → 0` is exact in the middle: for a
surjection `g : B →+* B'` of commutative rings with kernel `L` in the Jacobson radical of `B`, the
kernel of `D(B) →+ D(B')` is the image of the relative group `D(B, L)`. -/
theorem exact_toDennisSteinGroup_map :
    Function.Exact (RelativeDennisSteinGroup.toDennisSteinGroup hL) (map g) := by
  refine Function.Exact.of_comp_of_mem_range ?_ fun x hx => ?_
  · have : (map g).comp (RelativeDennisSteinGroup.toDennisSteinGroup hL) = 0 := by
      ext r s h
      have hu := Ideal.isUnit_one_sub_mul_of_le_jacobson hL h
      rcases h with hr | hs
      · simp [RingHom.mem_ker.1 hr, hu]
      · simp [RingHom.mem_ker.1 hs, hu]
    exact congrArg DFunLike.coe this
  · have := DFunLike.congr_fun (liftHom_comp_map hg hL) x
    rw [AddMonoidHom.comp_apply, hx, map_zero, QuotientAddGroup.mk'_apply, eq_comm,
      QuotientAddGroup.eq_zero_iff] at this
    exact this

/-- **`D(B')` as a quotient of `D(B)`**: for a surjection `g : B →+* B'` of commutative rings with
kernel `L` in the Jacobson radical of `B`, the map induced by `g` identifies the quotient of
`D(B)` by the image of the relative group `D(B, L)` with `D(B')`. -/
noncomputable def quotientRangeEquiv :
    DennisSteinGroup B ⧸ (RelativeDennisSteinGroup.toDennisSteinGroup hL).range ≃+
      DennisSteinGroup B' :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (exact_toDennisSteinGroup_map hg hL).addMonoidHom_ker_eq.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (map_surjective_of_ker_le_jacobson hg hL))

/-- `TauCeti.DennisSteinGroup.quotientRangeEquiv` sends the class of `x` to its image under `g`. -/
@[simp]
theorem quotientRangeEquiv_mk (x : DennisSteinGroup B) :
    quotientRangeEquiv hg hL (QuotientAddGroup.mk x) = map g x := by
  rw [quotientRangeEquiv, AddEquiv.trans_apply, QuotientAddGroup.quotientAddEquivOfEq_mk,
    TauCeti.QuotientAddGroup.quotientKerEquivOfSurjective_apply_mk]

end DennisSteinGroup

end TauCeti

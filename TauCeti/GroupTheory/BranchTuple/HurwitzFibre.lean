/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.BranchTuple.Hurwitz

/-!
# The fibres of Hurwitz spaces and their braid representations

Fix a group `G` and a conjugacy class `c` of `G`. The marked Hurwitz space `Hur^c_{G,n}` of
Ellenberg, Venkatesh and Westerland is the covering space of the configuration space `Conf_n` of
`n` unordered points in the disc whose fibre over the base configuration is the set `c^n` of
branch tuples of length `n` with all entries in `c`; its monodromy is the Hurwitz action of the
braid group `B_n = π₁(Conf_n)`. The full-monodromy part `CHur^c_{G,n}` keeps the tuples that
generate `G`. Since `Conf_n` is a `K(B_n, 1)`, the homology of these spaces is braid-group homology
with coefficients in the permutation representations of these fibres.

This file builds the fibres with their braid actions. `TauCeti.HurwitzFibre c full n` is the
fibre `c^n`, cut down to the generating tuples when `full` holds. Simultaneous conjugation, the
action of `ConjAct G`, preserves these conditions and commutes with the braid action, so the braid
action descends to the quotient `TauCeti.UnmarkedFibre c full n`: the fibre of the unmarked
Hurwitz spaces `Hur^c_{G,n}/G` and `CHur^c_{G,n}/G`, which forget the marking at the boundary.

The fibres impose no product-one condition: the ordered product of a fibre point is invariant under
the braid action (`TauCeti.BranchTuple.product_hurwitzAction`) and conjugated by simultaneous
conjugation (`TauCeti.BranchTuple.product_conjAct_smul`), but it is not fixed.

## Main definitions

* `TauCeti.HurwitzFibre c full n`: branch tuples of length `n` with entries in `c`, generating `G`
  when `full` holds, with the Hurwitz action of `TauCeti.BraidGroup n`
  (`TauCeti.HurwitzFibre.instMulActionBraidGroup`) and the action of `ConjAct G` by simultaneous
  conjugation (`TauCeti.HurwitzFibre.instMulActionConjAct`). The elementary braid `σ i` acts by
  the `i`-th Hurwitz move of the underlying tuple.
* `TauCeti.UnmarkedFibre c full n`: fibre points up to simultaneous conjugation, with the induced
  braid action.

## Main results

* `TauCeti.HurwitzFibre.tuple_smul` and `TauCeti.HurwitzFibre.tuple_conjAct_smul`: both actions are
  computed on the underlying tuples.
* `TauCeti.HurwitzFibre.instSMulCommClass`: the braid action commutes with simultaneous
  conjugation.
* `TauCeti.UnmarkedFibre.mk_eq_mk_iff`: two fibre points have the same unmarked class exactly when
  one element of `G` conjugates the first to the second entrywise.
* `TauCeti.HurwitzFibre.card_false`: the fibre `c^n` has `|c|^n` points.
* `TauCeti.HurwitzFibre.isEmpty_true_zero_iff`: the full-monodromy fibre over the empty
  configuration is empty unless `G` is trivial, since the empty tuple generates the trivial
  subgroup.

## References

* J. S. Ellenberg, A. Venkatesh, C. Westerland, *Homological stability for Hurwitz spaces and the
  Cohen-Lenstra conjecture over function fields*, Ann. of Math. 183 (2016), Definition 2.2 and
  §§2.2–2.4.
-/

public section

namespace TauCeti

open BraidGroup BranchTuple

variable {G : Type*} [Group G]

/-- The fibre of the marked Hurwitz space `Hur^c_{G,n}` over the base configuration: branch tuples
of length `n` all of whose entries lie in the conjugacy class `c`. When `full` holds the tuples are
also required to generate `G`, which gives the fibre of the full-monodromy Hurwitz space
`CHur^c_{G,n}`. -/
@[ext]
structure HurwitzFibre (c : ConjClasses G) (full : Bool) (n : ℕ) where
  /-- The underlying branch tuple. -/
  tuple : BranchTuple n G
  /-- Every entry lies in the class `c`. -/
  mem : ∀ i, tuple i ∈ c.carrier
  /-- The entries generate `G` when `full` holds. -/
  gen : full = true → generated tuple = ⊤

namespace HurwitzFibre

variable {c : ConjClasses G} {full : Bool} {n : ℕ}

/-- A fibre point is determined by its underlying tuple. -/
theorem tuple_injective : Function.Injective (tuple : HurwitzFibre c full n → BranchTuple n G) :=
  fun _ _ ↦ HurwitzFibre.ext

instance [Finite G] : Finite (HurwitzFibre c full n) :=
  Finite.of_injective _ tuple_injective

/-! ### The braid action -/

/-- The Hurwitz action of a braid on a fibre point. -/
instance instSMulBraidGroup : SMul (BraidGroup n) (HurwitzFibre c full n) where
  smul b s := ⟨hurwitzAction b s.tuple,
    (forall_hurwitzAction_apply_mem_carrier_iff b s.tuple).mpr s.mem,
    fun h ↦ (generated_hurwitzAction b s.tuple).trans (s.gen h)⟩

/-- The braid action on the fibre is the Hurwitz action on the underlying tuples. -/
@[simp]
theorem tuple_smul (b : BraidGroup n) (s : HurwitzFibre c full n) :
    (b • s).tuple = hurwitzAction b s.tuple :=
  (rfl)

/-- The Hurwitz action of the braid group on the fibre: the monodromy action of
`π₁(Conf_n) = B_n`. The elementary braid `σ i` acts by the `i`-th Hurwitz move. -/
instance instMulActionBraidGroup : MulAction (BraidGroup n) (HurwitzFibre c full n) where
  one_smul s := HurwitzFibre.ext (by simp)
  mul_smul b b' s := HurwitzFibre.ext (by simp)

/-! ### Simultaneous conjugation -/

/-- Simultaneous conjugation of all entries of a fibre point by one element of `G`. -/
instance instSMulConjAct : SMul (ConjAct G) (HurwitzFibre c full n) where
  smul x s := ⟨x • s.tuple,
    fun i ↦ ConjClasses.mem_carrier_iff_mk_eq.mpr <|
      (ConjClasses.mk_eq_mk_iff_isConj.mpr <| ConjAct.mem_orbit_conjAct.mp <|
        MulAction.mem_orbit (s.tuple i) x).trans (ConjClasses.mem_carrier_iff_mk_eq.mp (s.mem i)),
    fun h ↦ by rw [conjAct_smul_eq, generated_smul_eq_top_iff]; exact s.gen h⟩

/-- Simultaneous conjugation of a fibre point is computed on the underlying tuple. -/
@[simp]
theorem tuple_conjAct_smul (x : ConjAct G) (s : HurwitzFibre c full n) :
    (x • s).tuple = x • s.tuple :=
  (rfl)

/-- The action of `G` on the fibre by simultaneous conjugation. -/
instance instMulActionConjAct : MulAction (ConjAct G) (HurwitzFibre c full n) where
  one_smul s := HurwitzFibre.ext (by simp)
  mul_smul x y s := HurwitzFibre.ext (by simp [mul_smul])

/-- The braid action commutes with simultaneous conjugation. -/
instance instSMulCommClass : SMulCommClass (BraidGroup n) (ConjAct G) (HurwitzFibre c full n) where
  smul_comm b x s := HurwitzFibre.ext (by simp [hurwitzAction_conjAct_smul])

/-! ### Cardinality and the empty configuration -/

/-- Without the generation condition, a fibre point is just a tuple of elements of `c`. -/
def equivFunCarrier : HurwitzFibre c false n ≃ (Fin n → c.carrier) where
  toFun s i := ⟨s.tuple i, s.mem i⟩
  invFun t := ⟨fun i ↦ t i, fun i ↦ (t i).property, Bool.false_ne_true.elim⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_equivFunCarrier_apply (s : HurwitzFibre c false n) (i : Fin n) :
    (equivFunCarrier s i : G) = s.tuple i :=
  (rfl)

@[simp]
theorem tuple_equivFunCarrier_symm_apply (t : Fin n → c.carrier) (i : Fin n) :
    (equivFunCarrier.symm t).tuple i = t i :=
  (rfl)

/-- The fibre `c^n` of the marked Hurwitz space has `|c|^n` points. -/
theorem card_false : Nat.card (HurwitzFibre c false n) = Nat.card c.carrier ^ n := by
  rw [Nat.card_congr equivFunCarrier, Nat.card_fun, Nat.card_fin]

/-- The full-monodromy fibre over the empty configuration is empty exactly when `G` is nontrivial:
the empty tuple generates the trivial subgroup. -/
theorem isEmpty_true_zero_iff : IsEmpty (HurwitzFibre c true 0) ↔ Nontrivial G := by
  rw [← not_nonempty_iff, ← not_subsingleton_iff_nontrivial, not_iff_not,
    ← Subgroup.subsingleton_iff, ← subsingleton_iff_bot_eq_top]
  refine ⟨fun ⟨s⟩ ↦ (generated_zero s.tuple).symm.trans (s.gen rfl), fun h ↦ ?_⟩
  exact ⟨⟨finZeroElim, finZeroElim, fun _ ↦ (generated_zero _).trans h⟩⟩

end HurwitzFibre

/-! ### The unmarked fibre -/

/-- The fibre of the unmarked Hurwitz space `Hur^c_{G,n}/G` (or `CHur^c_{G,n}/G` when `full`
holds): fibre points up to simultaneous conjugation. The braid action descends to it
(`MulAction.orbitRel.Quotient.instMulActionOfSMulCommClass`) and is computed on representatives
(`MulAction.orbitRel.Quotient.smul_mk`). -/
abbrev UnmarkedFibre (c : ConjClasses G) (full : Bool) (n : ℕ) : Type _ :=
  MulAction.orbitRel.Quotient (ConjAct G) (HurwitzFibre c full n)

namespace UnmarkedFibre

variable {c : ConjClasses G} {full : Bool} {n : ℕ}

/-- Two fibre points have the same unmarked class exactly when one element of `G` conjugates the
first to the second entrywise. -/
theorem mk_eq_mk_iff {s t : HurwitzFibre c full n} :
    (Quotient.mk'' s : UnmarkedFibre c full n) = Quotient.mk'' t ↔
      ∃ g : G, ∀ i, t.tuple i = g * s.tuple i * g⁻¹ := by
  rw [eq_comm, Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨ConjAct.ofConjAct x, fun i ↦ ConjAct.smul_def x _⟩
  · rintro ⟨g, hg⟩
    exact ⟨ConjAct.toConjAct g, HurwitzFibre.ext <| funext fun i ↦ by
      rw [HurwitzFibre.tuple_conjAct_smul, Pi.smul_apply, ConjAct.smul_def,
        ConjAct.ofConjAct_toConjAct, hg]⟩

end UnmarkedFibre

end TauCeti

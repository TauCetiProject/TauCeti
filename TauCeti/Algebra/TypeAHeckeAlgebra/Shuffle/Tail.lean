/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.JucysMurphy.Tail
public import TauCeti.Algebra.TypeAHeckeAlgebra.Shuffle.InnerProduct

/-!
# First-site decomposition and Jucys–Murphy compression on shuffle modules

On the shuffle module `Sh_k(U)` (`ShuffleMask k l → U`) of `TypeAHeckeAlgebra R q (k + l)` (with
`0 < k + l`), partitioning masks according to whether site `0` is selected (`0 ∈ S.1`) or a rest
position (`0 ∉ S.1`) decomposes the carrier into two complementary projections `firstSelectedProj`
and `firstRestProj`:

* masks selecting site `0` correspond via `ShuffleMask.consSelectedEquiv` to
  `ShuffleMask (k - 1) l`, and shifted-tail generators `T q (i + 1)` act on this block as
  `shuffleRep (k - 1) ρ (T q i)` with unchanged rest representation `ρ`;
* masks leaving site `0` in the rest correspond via `ShuffleMask.consRestEquiv` to
  `ShuffleMask k (l - 1)`, and `tailIncl` acts on this block as
  `shuffleRep k (ρ.comp (tailIncl _))`.

Consequently both `firstSelectedProj` and `firstRestProj` commute with the shifted-tail subalgebra.
While the first-site Jucys–Murphy element `tailJucysMurphy q 0` (and its denominator-free additive
companion `tailAdditiveJucysMurphy q 0`) mixes the two blocks through `T q 0`, compressing it to the
first-site rest subspace eliminates all selected strands and recovers the first-site Jucys–Murphy
operator of the rest module `U`:

`firstRestProj ∘ₗ shuffleRep k ρ (tailAdditiveJucysMurphy q 0) ∘ₗ firstRestProj =
  (ρ (tailAdditiveJucysMurphy q 0)).compLeft _ ∘ₗ firstRestProj`,

and hence the same identity for `tailJucysMurphy q 0`. Proving the additive compression directly by
induction on `k + l` establishes both identities over every commutative ring `R` and unit `q`,
including the symmetric-group specialization `q² = 1`. On the orthonormal-mask Hilbert carrier
`PiLp 2`, `firstSelectedHilbertProj` and `firstRestHilbertProj` are bounded self-adjoint orthogonal
projections satisfying the corresponding Hilbert-space compression identities.

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.ShuffleMask.consSelected` and `consSelectedEquiv`: prepending a
  selected position at site `0`.
* `TauCeti.TypeAHeckeAlgebra.ShuffleMask.consRest` and `consRestEquiv`: prepending a rest position
  at site `0`.
* `TauCeti.TypeAHeckeAlgebra.firstSelectedProj` and `firstRestProj`: coordinate projections onto
  masks with `0 ∈ S.1` and `0 ∉ S.1`.
* `TauCeti.TypeAHeckeAlgebra.firstSelectedHilbertProj` and `firstRestHilbertProj`: the
  corresponding orthogonal projections on the `PiLp 2` shuffle Hilbert carrier.

## Main results

* `TauCeti.TypeAHeckeAlgebra.shuffleRep_T_succ_consSelected` and
  `TauCeti.TypeAHeckeAlgebra.shuffleRep_tailIncl_consRest`: Mackey restriction of `shuffleRep`
  along the shifted-tail generators on the two first-site blocks.
* `TauCeti.TypeAHeckeAlgebra.firstRestProj_comp_shuffleRep_tailIncl` and
  `TauCeti.TypeAHeckeAlgebra.firstSelectedProj_comp_shuffleRep_tailIncl`: first-site projections
  commute with `tailIncl`.
* `firstRestProj_comp_shuffleRep_tailAdditiveJucysMurphy_zero_comp_firstRestProj` and
  `firstRestProj_comp_shuffleRep_tailJucysMurphy_zero_comp_firstRestProj`: **first-site
  Jucys–Murphy rest-compression identity** (additive and multiplicative).
* `firstRestHilbertProj_shuffleHilbertRep_tailJucysMurphy_zero`:
  the Hilbert-carrier rest-compression identity.

## References

* R. Dipper and G. James, *Representations of Hecke algebras of general linear groups*,
  Proc. London Math. Soc. (3) 52 (1986), 20–52.
* G. E. Murphy, *On the representation theory of the symmetric groups and associated Hecke
  algebras*, J. Algebra 152 (1992), 492–513.
-/

public section

open Finset
open scoped InnerProductSpace

namespace TauCeti.TypeAHeckeAlgebra

namespace ShuffleMask

variable {k l : ℕ}

/-- Before position `0` there are no rest positions. -/
@[simp]
theorem restIndex_zero [NeZero (k + l)] (S : ShuffleMask k l) :
    S.restIndex (0 : Fin (k + l)) = 0 := by
  rw [restIndex_def]
  simp

/-! ### Prepending a selected or rest position at site `0` -/

/-- Embedding shifting positions by `+ 1` from `Fin (k + l)` into `Fin ((k + 1) + l)`. -/
def shiftSelectedEmb (k l : ℕ) : Fin (k + l) ↪ Fin ((k + 1) + l) :=
  ⟨fun p ↦ ⟨p.val + 1, by omega⟩, fun _ _ h ↦ Fin.ext (by simpa [Fin.ext_iff] using h)⟩

/-- `shiftSelectedEmb` increments the underlying natural-number position by `1`. -/
@[simp]
theorem val_shiftSelectedEmb (p : Fin (k + l)) : (shiftSelectedEmb k l p : ℕ) = p + 1 :=
  (rfl)

/-- A shifted position in `Fin ((k + 1) + l)` is never `0`. -/
@[simp]
theorem shiftSelectedEmb_ne_zero (p : Fin (k + l)) :
    shiftSelectedEmb k l p ≠ 0 := by
  simp [Fin.ext_iff]

/-- Prepending a selected position at site `0` inserts `0` and shifts all selected positions of `M`
by `+ 1`. -/
def consSelected (M : ShuffleMask k l) : ShuffleMask (k + 1) l :=
  ⟨insert 0 (M.1.map (shiftSelectedEmb k l)), by
    rw [card_insert_of_notMem, card_map, M.2]
    simp [Fin.ext_iff]⟩

/-- `M.consSelected` always selects site `0`. -/
@[simp]
theorem zero_mem_consSelected (M : ShuffleMask k l) :
    (0 : Fin ((k + 1) + l)) ∈ M.consSelected.1 :=
  mem_insert_self ..

/-- A shifted position belongs to `M.consSelected` if and only if the original position belongs to
`M`. -/
@[simp]
theorem shiftSelectedEmb_mem_consSelected {M : ShuffleMask k l} {p : Fin (k + l)} :
    shiftSelectedEmb k l p ∈ M.consSelected.1 ↔ p ∈ M.1 := by
  simp [consSelected, Fin.ext_iff]

/-- Prepending a selected position at site `0` is injective. -/
theorem consSelected_injective : Function.Injective (@consSelected k l) := by
  intro M₁ M₂ h
  refine Subtype.ext (Finset.ext fun p ↦ ?_)
  have hp := congrArg (fun M : ShuffleMask (k + 1) l ↦ shiftSelectedEmb k l p ∈ M.1) h
  simpa only [shiftSelectedEmb_mem_consSelected] using Iff.of_eq hp

/-- Exchanging two shifted positions in `M.consSelected` corresponds to exchanging them in `M`. -/
theorem consSelected_swap (a b : Fin (k + l)) (M : ShuffleMask k l) :
    (M.swap a b).consSelected =
      M.consSelected.swap (shiftSelectedEmb k l a) (shiftSelectedEmb k l b) := by
  refine Subtype.ext (Finset.ext fun y ↦ ?_)
  by_cases hy0 : y = 0
  · subst hy0
    have ha0 : (0 : Fin ((k + 1) + l)) ≠ shiftSelectedEmb k l a :=
      (shiftSelectedEmb_ne_zero a).symm
    have hb0 : (0 : Fin ((k + 1) + l)) ≠ shiftSelectedEmb k l b :=
      (shiftSelectedEmb_ne_zero b).symm
    rw [mem_swap, Equiv.swap_apply_of_ne_of_ne ha0 hb0]
    simp only [zero_mem_consSelected]
  · have hypos : 0 < (y : ℕ) := Nat.pos_of_ne_zero fun h ↦ hy0 (Fin.ext h)
    let p : Fin (k + l) := ⟨y.val - 1, by omega⟩
    have hyp : y = shiftSelectedEmb k l p := Fin.ext (by simp [p]; omega)
    have hswap : Equiv.swap (shiftSelectedEmb k l a) (shiftSelectedEmb k l b)
        (shiftSelectedEmb k l p) = shiftSelectedEmb k l (Equiv.swap a b p) := by
      by_cases hpa : p = a
      · subst hpa
        simp
      · by_cases hpb : p = b
        · subst hpb
          simp
        · rw [Equiv.swap_apply_of_ne_of_ne hpa hpb, Equiv.swap_apply_of_ne_of_ne
            ((shiftSelectedEmb k l).injective.ne hpa) ((shiftSelectedEmb k l).injective.ne hpb)]
    rw [hyp, mem_swap, hswap, shiftSelectedEmb_mem_consSelected, shiftSelectedEmb_mem_consSelected,
      mem_swap]

/-- Prepending a selected position at site `0` leaves the rest-position count before shifted
positions unchanged. -/
@[simp]
theorem restIndex_consSelected (M : ShuffleMask k l) (p : Fin (k + l)) :
    M.consSelected.restIndex (shiftSelectedEmb k l p) = M.restIndex p := by
  have hset : ({x ∈ M.consSelected.1ᶜ | x < shiftSelectedEmb k l p} : Finset _) =
      ({x ∈ M.1ᶜ | x < p} : Finset _).map (shiftSelectedEmb k l) := by
    ext y
    simp only [mem_filter, mem_compl, mem_map]
    constructor
    · rintro ⟨hyM, hylt⟩
      have hy0 : y ≠ 0 := fun h ↦ hyM (h ▸ zero_mem_consSelected M)
      have hypos : 0 < (y : ℕ) := Nat.pos_of_ne_zero fun h ↦ hy0 (Fin.ext h)
      have hlt_val : (y : ℕ) < (p : ℕ) + 1 := Fin.lt_def.mp hylt
      refine ⟨⟨y.val - 1, by omega⟩, ⟨?_, ?_⟩, Fin.ext (by simp; omega)⟩
      · intro hx
        exact hyM (by convert shiftSelectedEmb_mem_consSelected.mpr hx; ext; simp; omega)
      · rw [Fin.lt_def]
        simp only
        omega
    · rintro ⟨x, ⟨hxM, hxlt⟩, rfl⟩
      exact ⟨by simpa using hxM, by rw [Fin.lt_def] at hxlt ⊢; simp [hxlt]⟩
  have hcard := congrArg Finset.card hset
  simpa only [card_map, restIndex_def] using hcard

private theorem insert_zero_map_filter_shiftSelectedEmb (S : ShuffleMask (k + 1) l)
    (hS : (0 : Fin ((k + 1) + l)) ∈ S.1) :
    insert (0 : Fin ((k + 1) + l))
      ((univ.filter fun p : Fin (k + l) ↦ shiftSelectedEmb k l p ∈ S.1).map
        (shiftSelectedEmb k l)) = S.1 := by
  ext y
  simp only [mem_insert, mem_map, mem_filter, mem_univ, true_and]
  constructor
  · rintro (rfl | ⟨p, hp, rfl⟩) <;> assumption
  · intro hy
    by_cases hy0 : y = 0
    · exact Or.inl hy0
    · have hypos : 0 < (y : ℕ) := Nat.pos_of_ne_zero fun h ↦ hy0 (Fin.ext h)
      refine Or.inr ⟨⟨y.val - 1, by omega⟩, ?_, Fin.ext (by simp; omega)⟩
      convert hy
      ext
      simp
      omega

/-- Removing the selected position at site `0` from a mask `S` selecting `0`. -/
def tailOfZeroMem (S : ShuffleMask (k + 1) l)
    (hS : (0 : Fin ((k + 1) + l)) ∈ S.1) : ShuffleMask k l :=
  ⟨univ.filter fun p : Fin (k + l) ↦ shiftSelectedEmb k l p ∈ S.1, by
    have hcard := congrArg Finset.card (insert_zero_map_filter_shiftSelectedEmb S hS)
    rw [card_insert_of_notMem (by simp [Fin.ext_iff]), card_map, S.2] at hcard
    omega⟩

/-- Prepending `0` to `tailOfZeroMem S hS` recovers `S`. -/
@[simp]
theorem consSelected_tailOfZeroMem (S : ShuffleMask (k + 1) l)
    (hS : (0 : Fin ((k + 1) + l)) ∈ S.1) :
    (tailOfZeroMem S hS).consSelected = S :=
  Subtype.ext (insert_zero_map_filter_shiftSelectedEmb S hS)

/-- Removing site `0` from `M.consSelected` recovers `M`. -/
@[simp]
theorem tailOfZeroMem_consSelected (M : ShuffleMask k l) :
    tailOfZeroMem M.consSelected (zero_mem_consSelected M) = M :=
  consSelected_injective (consSelected_tailOfZeroMem ..)

/-- Bijection between `k`-masks on `k + l` strands and `(k + 1)`-masks on `(k + 1) + l` strands
selecting site `0`. -/
def consSelectedEquiv :
    ShuffleMask k l ≃
      {S : ShuffleMask (k + 1) l // (0 : Fin ((k + 1) + l)) ∈ S.1} where
  toFun M := ⟨M.consSelected, zero_mem_consSelected M⟩
  invFun S := tailOfZeroMem S.1 S.2
  left_inv M := tailOfZeroMem_consSelected M
  right_inv S := Subtype.ext (consSelected_tailOfZeroMem S.1 S.2)

/-- Prepending a rest position at site `0` shifts every selected position of `M` by `Fin.succ`. -/
def consRest (M : ShuffleMask k l) : ShuffleMask k (l + 1) :=
  ⟨M.1.map (Fin.succEmb (k + l)), by rw [card_map, M.2]⟩

/-- `M.consRest` never selects site `0`. -/
@[simp]
theorem zero_notMem_consRest (M : ShuffleMask k l) :
    (0 : Fin (k + (l + 1))) ∉ M.consRest.1 := by
  simp [consRest]

/-- A shifted position `p.succ` belongs to `M.consRest` if and only if `p` belongs to `M`. -/
@[simp]
theorem succ_mem_consRest {M : ShuffleMask k l} {p : Fin (k + l)} :
    p.succ ∈ M.consRest.1 ↔ p ∈ M.1 := by
  simp [consRest]

/-- Prepending a rest position at site `0` is injective. -/
theorem consRest_injective : Function.Injective (@consRest k l) := by
  intro M₁ M₂ h
  refine Subtype.ext (Finset.ext fun p ↦ ?_)
  exact Iff.of_eq (by simpa only [succ_mem_consRest] using congrArg (p.succ ∈ ·.1) h)

/-- Exchanging two shifted positions in `M.consRest` corresponds to exchanging them in `M`. -/
theorem consRest_swap (a b : Fin (k + l)) (M : ShuffleMask k l) :
    (M.swap a b).consRest = ShuffleMask.swap (k := k) (l := l + 1) a.succ b.succ M.consRest := by
  refine Subtype.ext (Finset.ext fun y ↦ ?_)
  refine Fin.cases ?_ (fun p ↦ ?_) y
  · rw [mem_swap, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero a).symm (Fin.succ_ne_zero b).symm]
    simp
  · have hswap : Equiv.swap a.succ b.succ p.succ = (Equiv.swap a b p).succ := by
      by_cases hpa : p = a
      · subst hpa
        simp
      · by_cases hpb : p = b
        · subst hpb
          simp
        · rw [Equiv.swap_apply_of_ne_of_ne hpa hpb, Equiv.swap_apply_of_ne_of_ne
            ((Fin.succ_injective _).ne hpa) ((Fin.succ_injective _).ne hpb)]
    rw [mem_swap, hswap, succ_mem_consRest, succ_mem_consRest, mem_swap]

/-- Prepending a rest position at site `0` adds `1` to the rest-position count before every
shifted position. -/
@[simp]
theorem restIndex_consRest_succ (M : ShuffleMask k l) (p : Fin (k + l)) :
    M.consRest.restIndex p.succ = M.restIndex p + 1 := by
  have hset : ({x ∈ M.consRest.1ᶜ | x < p.succ} : Finset _) =
      insert (0 : Fin (k + (l + 1)))
        (({x ∈ M.1ᶜ | x < p} : Finset _).map (Fin.succEmb (k + l))) := by
    ext y
    refine Fin.cases ?_ (fun x ↦ ?_) y
    · simp [Fin.succ_pos]
    · simp [Fin.succ_ne_zero]
  have hcard := congrArg Finset.card hset
  rw [card_insert_of_notMem (by simp), card_map] at hcard
  rw [restIndex_def, restIndex_def]
  exact hcard

/-- Removing the rest position at site `0` from a mask `S` not selecting `0`. -/
def tailOfZeroNotMem (S : ShuffleMask k (l + 1))
    (hS : (0 : Fin (k + (l + 1))) ∉ S.1) : ShuffleMask k l :=
  ⟨univ.filter fun p : Fin (k + l) ↦ p.succ ∈ S.1, by
    have hmap : ((univ.filter fun p : Fin (k + l) ↦ p.succ ∈ S.1).map (Fin.succEmb (k + l))) =
        S.1 := by
      ext y
      refine Fin.cases ?_ (fun p ↦ ?_) y
      · simp [hS]
      · simp
    rw [← card_map (Fin.succEmb (k + l)), hmap, S.2]⟩

/-- Prepending a rest position at site `0` to `tailOfZeroNotMem S hS` recovers `S`. -/
@[simp]
theorem consRest_tailOfZeroNotMem (S : ShuffleMask k (l + 1))
    (hS : (0 : Fin (k + (l + 1))) ∉ S.1) :
    (tailOfZeroNotMem S hS).consRest = S := by
  refine Subtype.ext (Finset.ext fun y ↦ ?_)
  refine Fin.cases ?_ (fun p ↦ ?_) y
  · simp [hS]
  · simp [tailOfZeroNotMem]

/-- Removing the rest position at site `0` from `M.consRest` recovers `M`. -/
@[simp]
theorem tailOfZeroNotMem_consRest (M : ShuffleMask k l) :
    tailOfZeroNotMem M.consRest (zero_notMem_consRest M) = M :=
  consRest_injective (consRest_tailOfZeroNotMem ..)

/-- Bijection between `k`-masks on `k + l` strands and `k`-masks on `k + (l + 1)` strands leaving
site `0` in the rest. -/
def consRestEquiv :
    ShuffleMask k l ≃ {S : ShuffleMask k (l + 1) // (0 : Fin (k + (l + 1))) ∉ S.1} where
  toFun M := ⟨M.consRest, zero_notMem_consRest M⟩
  invFun S := tailOfZeroNotMem S.1 S.2
  left_inv M := tailOfZeroNotMem_consRest M
  right_inv S := Subtype.ext (consRest_tailOfZeroNotMem S.1 S.2)

end ShuffleMask

/-! ### First-site coordinate projections -/

section FirstSiteProjections

variable {R : Type*} [Semiring R] {k l : ℕ}
variable {U : Type*} [AddCommMonoid U] [Module R U]

section Nonempty

variable (R U) [NeZero (k + l)]

/-- Linear projection on `ShuffleMask k l → U` retaining masks that select site `0` and zeroing
out masks that leave site `0` in the rest. -/
def firstSelectedProj : Module.End R (ShuffleMask k l → U) where
  toFun f S := if (0 : Fin (k + l)) ∈ S.1 then f S else 0
  map_add' f g := funext fun S ↦ by simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' r f := funext fun S ↦ by
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

/-- Linear projection on `ShuffleMask k l → U` retaining masks that leave site `0` in the rest and
zeroing out masks that select site `0`. -/
def firstRestProj : Module.End R (ShuffleMask k l → U) where
  toFun f S := if (0 : Fin (k + l)) ∈ S.1 then 0 else f S
  map_add' f g := funext fun S ↦ by simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' r f := funext fun S ↦ by
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

variable {R U}

/-- Pointwise evaluation of `firstSelectedProj` at mask `S`. -/
@[simp]
theorem firstSelectedProj_apply (f : ShuffleMask k l → U) (S : ShuffleMask k l) :
    firstSelectedProj R U f S = if (0 : Fin (k + l)) ∈ S.1 then f S else 0 :=
  (rfl)

/-- Pointwise evaluation of `firstRestProj` at mask `S`. -/
@[simp]
theorem firstRestProj_apply (f : ShuffleMask k l → U) (S : ShuffleMask k l) :
    firstRestProj R U f S = if (0 : Fin (k + l)) ∈ S.1 then 0 else f S :=
  (rfl)

/-- `firstSelectedProj` is idempotent under composition. -/
@[simp]
theorem firstSelectedProj_comp_firstSelectedProj :
    (firstSelectedProj R U : Module.End R (ShuffleMask k l → U)) ∘ₗ firstSelectedProj R U =
      firstSelectedProj R U := by
  refine LinearMap.ext fun f ↦ funext fun S ↦ ?_
  by_cases h : (0 : Fin (k + l)) ∈ S.1 <;> simp [h]

/-- `firstSelectedProj` is an idempotent endomorphism. -/
theorem isIdempotentElem_firstSelectedProj :
    IsIdempotentElem (firstSelectedProj R U : Module.End R (ShuffleMask k l → U)) :=
  firstSelectedProj_comp_firstSelectedProj

/-- `firstRestProj` is idempotent under composition. -/
@[simp]
theorem firstRestProj_comp_firstRestProj :
    (firstRestProj R U : Module.End R (ShuffleMask k l → U)) ∘ₗ firstRestProj R U =
      firstRestProj R U := by
  refine LinearMap.ext fun f ↦ funext fun S ↦ ?_
  by_cases h : (0 : Fin (k + l)) ∈ S.1 <;> simp [h]

/-- `firstRestProj` is an idempotent endomorphism. -/
theorem isIdempotentElem_firstRestProj :
    IsIdempotentElem (firstRestProj R U : Module.End R (ShuffleMask k l → U)) :=
  firstRestProj_comp_firstRestProj

/-- `firstSelectedProj` annihilates the image of `firstRestProj`. -/
@[simp]
theorem firstSelectedProj_comp_firstRestProj :
    (firstSelectedProj R U : Module.End R (ShuffleMask k l → U)) ∘ₗ firstRestProj R U =
      0 := by
  refine LinearMap.ext fun f ↦ funext fun S ↦ ?_
  by_cases h : (0 : Fin (k + l)) ∈ S.1 <;> simp [h]

/-- `firstRestProj` annihilates the image of `firstSelectedProj`. -/
@[simp]
theorem firstRestProj_comp_firstSelectedProj :
    (firstRestProj R U : Module.End R (ShuffleMask k l → U)) ∘ₗ firstSelectedProj R U =
      0 := by
  refine LinearMap.ext fun f ↦ funext fun S ↦ ?_
  by_cases h : (0 : Fin (k + l)) ∈ S.1 <;> simp [h]

/-- `firstSelectedProj` and `firstRestProj` sum to the identity operator. -/
@[simp]
theorem firstSelectedProj_add_firstRestProj :
    (firstSelectedProj R U : Module.End R (ShuffleMask k l → U)) + firstRestProj R U = 1 := by
  refine LinearMap.ext fun f ↦ funext fun S ↦ ?_
  by_cases h : (0 : Fin (k + l)) ∈ S.1 <;> simp [h]

end Nonempty

/-- When `l = 0` (`0 < k`), every mask selects all positions, so `firstRestProj` is `0`. -/
@[simp]
theorem firstRestProj_zero_right [NeZero k] :
    (firstRestProj R U : Module.End R (ShuffleMask k 0 → U)) = 0 := by
  refine LinearMap.ext fun f ↦ funext fun S ↦ ?_
  have hS : S.1 = univ := eq_univ_of_card S.1 (by simpa using S.2)
  simp [hS]

/-- When `l = 0` (`0 < k`), every mask selects site `0`, so `firstSelectedProj` is `1`. -/
@[simp]
theorem firstSelectedProj_zero_right [NeZero k] :
    (firstSelectedProj R U : Module.End R (ShuffleMask k 0 → U)) = 1 := by
  have h := firstSelectedProj_add_firstRestProj (R := R) (U := U) (k := k) (l := 0)
  rwa [firstRestProj_zero_right, add_zero] at h

/-- When `k = 0` (`0 < l`), every mask is empty, so `firstSelectedProj` is `0`. -/
@[simp]
theorem firstSelectedProj_zero_left [NeZero l] :
    (firstSelectedProj R U : Module.End R (ShuffleMask 0 l → U)) = 0 := by
  have : NeZero (0 + l) := by simpa only [Nat.zero_add] using ‹NeZero l›
  refine LinearMap.ext fun f ↦ funext fun S ↦ ?_
  have hS : S.1 = ∅ := card_eq_zero.mp S.2
  simp [hS]

/-- When `k = 0` (`0 < l`), every mask leaves site `0` in the rest, so `firstRestProj` is `1`. -/
@[simp]
theorem firstRestProj_zero_left [NeZero l] :
    (firstRestProj R U : Module.End R (ShuffleMask 0 l → U)) = 1 := by
  have : NeZero (0 + l) := by simpa only [Nat.zero_add] using ‹NeZero l›
  have h := firstSelectedProj_add_firstRestProj (R := R) (U := U) (k := 0) (l := l)
  rwa [firstSelectedProj_zero_left, zero_add] at h

end FirstSiteProjections

section Module

variable {R : Type*} [CommRing R] {q : Rˣ} {k l : ℕ}
variable {U : Type*} [AddCommGroup U] [Module R U]

/-! ### Shifted-tail restriction on the two first-site mask blocks -/

/-- On masks selecting site `0`, the shifted generator `T q (i + 1)` acts as `T q i` on the tail
mask with the same rest representation `ρ`. -/
theorem shuffleRep_T_succ_consSelected (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U)
    (i : Fin (k + l - 1)) (f : ShuffleMask (k + 1) l → U) (M : ShuffleMask k l) :
    shuffleRep (k + 1) ρ (T q ⟨i.val + 1, by omega⟩) f M.consSelected =
      shuffleRep k ρ (T q i) (fun M' ↦ f M'.consSelected) M := by
  set i' : Fin ((k + 1) + l - 1) := ⟨i.val + 1, by omega⟩
  have ha : BraidGroup.strand i' = ShuffleMask.shiftSelectedEmb k l (BraidGroup.strand i) :=
    Fin.ext (by simp [i'])
  have hb : BraidGroup.strandSucc i' =
      ShuffleMask.shiftSelectedEmb k l (BraidGroup.strandSucc i) :=
    Fin.ext (by simp [i'])
  by_cases h₁ : BraidGroup.strand i ∈ M.1 <;> by_cases h₂ : BraidGroup.strandSucc i ∈ M.1
  · rw [shuffleRep_T_apply_of_mem_of_mem ρ (by rw [ha]; simpa using h₁)
      (by rw [hb]; simpa using h₂), shuffleRep_T_apply_of_mem_of_mem ρ h₁ h₂]
  · rw [shuffleRep_T_apply_of_mem_of_notMem ρ (by rw [ha]; simpa using h₁)
      (by rw [hb]; simpa using h₂), shuffleRep_T_apply_of_mem_of_notMem ρ h₁ h₂, ha, hb,
      ← ShuffleMask.consSelected_swap]
  · rw [shuffleRep_T_apply_of_notMem_of_mem ρ (by rw [ha]; simpa using h₁)
      (by rw [hb]; simpa using h₂), shuffleRep_T_apply_of_notMem_of_mem ρ h₁ h₂, ha, hb,
      ← ShuffleMask.consSelected_swap]
  · rw [shuffleRep_T_apply_of_notMem_of_notMem ρ (by rw [ha]; simpa using h₁)
      (by rw [hb]; simpa using h₂), shuffleRep_T_apply_of_notMem_of_notMem ρ h₁ h₂]
    congr 3
    ext
    simp [ha]

/-- **Shifted-tail intertwining on the first-site rest block.** On masks leaving site `0` in the
rest, `tailIncl q (k + l) x` acts as `shuffleRep k (ρ.comp (tailIncl q l)) x` on the tail masks. -/
theorem shuffleRep_tailIncl_consRest
    (ρ : TypeAHeckeAlgebra R q (l + 1) →ₐ[R] Module.End R U)
    (x : TypeAHeckeAlgebra R q (k + l)) (f : ShuffleMask k (l + 1) → U) (M : ShuffleMask k l) :
    shuffleRep k ρ (tailIncl q (k + l) x) f M.consRest =
      shuffleRep k (ρ.comp (tailIncl q l)) x (fun M' ↦ f M'.consRest) M := by
  have hx : x ∈ Algebra.adjoin R (Set.range (T (n := k + l) q)) := by
    rw [adjoin_range_T]
    trivial
  induction hx using Algebra.adjoin_induction generalizing f M with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    rw [tailIncl_T]
    set i' : Fin (k + (l + 1) - 1) := ⟨i + 1, by omega⟩
    have ha : BraidGroup.strand i' = (BraidGroup.strand i).succ := Fin.ext (by simp [i'])
    have hb : BraidGroup.strandSucc i' = (BraidGroup.strandSucc i).succ :=
      Fin.ext (by simp [i'])
    by_cases h₁ : BraidGroup.strand i ∈ M.1 <;> by_cases h₂ : BraidGroup.strandSucc i ∈ M.1
    · rw [shuffleRep_T_apply_of_mem_of_mem ρ (by rw [ha]; simpa using h₁)
        (by rw [hb]; simpa using h₂), shuffleRep_T_apply_of_mem_of_mem _ h₁ h₂]
    · rw [shuffleRep_T_apply_of_mem_of_notMem ρ (by rw [ha]; simpa using h₁)
        (by rw [hb]; simpa using h₂), shuffleRep_T_apply_of_mem_of_notMem _ h₁ h₂, ha, hb,
        ← ShuffleMask.consRest_swap]
    · rw [shuffleRep_T_apply_of_notMem_of_mem ρ (by rw [ha]; simpa using h₁)
        (by rw [hb]; simpa using h₂), shuffleRep_T_apply_of_notMem_of_mem _ h₁ h₂, ha, hb,
        ← ShuffleMask.consRest_swap]
    · rw [shuffleRep_T_apply_of_notMem_of_notMem ρ (by rw [ha]; simpa using h₁)
        (by rw [hb]; simpa using h₂), shuffleRep_T_apply_of_notMem_of_notMem _ h₁ h₂,
        AlgHom.comp_apply, tailIncl_T]
      congr 3
      ext
      simp [ha]
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one, map_smul, map_one, map_smul, map_one]
    rfl
  | add x y _ _ hx hy =>
    simp [hx, hy]
  | mul x y _ _ hx hy =>
    simp only [map_mul, mul_apply_eq_comp]
    rw [hx (shuffleRep k ρ (tailIncl q (k + l) y) f) M]
    have hfun : (fun M' ↦ shuffleRep k ρ (tailIncl q (k + l) y) f M'.consRest) =
        shuffleRep k (ρ.comp (tailIncl q l)) y (fun M' ↦ f M'.consRest) :=
      funext fun M' ↦ hy f M'
    rw [hfun]

/-- Generators that do not cross site `0` commute with `firstRestProj`. -/
theorem firstRestProj_comp_shuffleRep_T_of_pos [NeZero (k + l)]
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U)
    {i : Fin (k + l - 1)} (hi : 0 < (i : ℕ)) :
    firstRestProj R U ∘ₗ shuffleRep k ρ (T q i) =
      shuffleRep k ρ (T q i) ∘ₗ firstRestProj R U := by
  refine LinearMap.ext fun f ↦ funext fun S ↦ ?_
  have ha0 : (0 : Fin (k + l)) ≠ BraidGroup.strand i := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_zero, BraidGroup.val_strand]
    omega
  have hb0 : (0 : Fin (k + l)) ≠ BraidGroup.strandSucc i := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_zero, BraidGroup.val_strandSucc]
    omega
  have hswap0 : ∀ M : ShuffleMask k l,
      (0 : Fin (k + l)) ∈ (M.swap (BraidGroup.strand i) (BraidGroup.strandSucc i)).1 ↔
        (0 : Fin (k + l)) ∈ M.1 := fun M ↦ by
    simp [Equiv.swap_apply_of_ne_of_ne ha0 hb0]
  by_cases h0 : (0 : Fin (k + l)) ∈ S.1 <;>
    by_cases ha : BraidGroup.strand i ∈ S.1 <;>
    by_cases hb : BraidGroup.strandSucc i ∈ S.1 <;>
    simp [h0, ha, hb, hswap0]

/-- **First-site rest projection commutes with `tailIncl`.** -/
theorem firstRestProj_comp_shuffleRep_tailIncl
    (ρ : TypeAHeckeAlgebra R q (l + 1) →ₐ[R] Module.End R U)
    (x : TypeAHeckeAlgebra R q (k + l)) :
    firstRestProj R U ∘ₗ shuffleRep k ρ (tailIncl q (k + l) x) =
      shuffleRep k ρ (tailIncl q (k + l) x) ∘ₗ firstRestProj R U := by
  have hx : x ∈ Algebra.adjoin R (Set.range (T (n := k + l) q)) := by
    rw [adjoin_range_T]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    rw [tailIncl_T]
    exact firstRestProj_comp_shuffleRep_T_of_pos ρ (by simp)
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one, map_smul, map_one]
    refine LinearMap.ext fun f ↦ funext fun S ↦ ?_
    by_cases h : (0 : Fin (k + (l + 1))) ∈ S.1 <;> simp [h]
  | add x y _ _ hx hy =>
    rw [map_add, map_add, LinearMap.comp_add, LinearMap.add_comp, hx, hy]
  | mul x y _ _ hx hy =>
    rw [map_mul, map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hx,
      LinearMap.comp_assoc, hy, ← LinearMap.comp_assoc]

/-- **First-site selected projection commutes with `tailIncl`.** -/
theorem firstSelectedProj_comp_shuffleRep_tailIncl
    (ρ : TypeAHeckeAlgebra R q (l + 1) →ₐ[R] Module.End R U)
    (x : TypeAHeckeAlgebra R q (k + l)) :
    firstSelectedProj R U ∘ₗ shuffleRep k ρ (tailIncl q (k + l) x) =
      shuffleRep k ρ (tailIncl q (k + l) x) ∘ₗ firstSelectedProj R U := by
  have hproj : (firstSelectedProj R U : Module.End R (ShuffleMask k (l + 1) → U)) =
      1 - firstRestProj R U :=
    eq_sub_of_add_eq firstSelectedProj_add_firstRestProj
  rw [hproj, LinearMap.sub_comp, LinearMap.comp_sub, Module.End.one_eq_id, LinearMap.id_comp,
    LinearMap.comp_id, firstRestProj_comp_shuffleRep_tailIncl]

/-! ### First-site Jucys–Murphy rest-compression identity -/

/-- Auxiliary intertwining relation between `(k' + m)`-strand and `((k' + 1) + m)`-strand Hecke
elements on the `consSelected` mask block, avoiding arithmetic casts on `TypeAHeckeAlgebra`. -/
private def IntertwinesConsSelected {k' m : ℕ}
    (ρ : TypeAHeckeAlgebra R q m →ₐ[R] Module.End R U)
    (x : TypeAHeckeAlgebra R q (k' + m)) (y : TypeAHeckeAlgebra R q ((k' + 1) + m)) : Prop :=
  ∀ (g : ShuffleMask (k' + 1) m → U) (N : ShuffleMask k' m),
    shuffleRep (k' + 1) ρ y g N.consSelected =
      shuffleRep k' ρ x (fun N' ↦ g N'.consSelected) N

private theorem intertwinesConsSelected_tailAdditiveJucysMurphy {k' m : ℕ}
    (ρ : TypeAHeckeAlgebra R q m →ₐ[R] Module.End R U) :
    ∀ (d : ℕ) (i : Fin (k' + m)) (i' : Fin ((k' + 1) + m)),
      k' + m - 1 - i.val = d → (i' : ℕ) = (i : ℕ) + 1 →
      IntertwinesConsSelected ρ (tailAdditiveJucysMurphy q i) (tailAdditiveJucysMurphy q i') := by
  intro d
  induction d with
  | zero =>
    intro i i' hd hi' g N
    rw [tailAdditiveJucysMurphy_eq_zero_of_val (by have := i.isLt; omega),
      tailAdditiveJucysMurphy_eq_zero_of_val (by have := i.isLt; omega)]
    simp
  | succ d ih =>
    intro i i' hd hi' g N
    have hlt : (i : ℕ) + 1 < k' + m := by have := i.isLt; omega
    have hlt' : (i' : ℕ) + 1 < (k' + 1) + m := by omega
    have hT :
        IntertwinesConsSelected (k' := k') ρ (T q ⟨i.val, by omega⟩) (T q ⟨i'.val, by omega⟩) := by
      intro h M'
      have hi'_eq : (⟨i'.val, by omega⟩ : Fin ((k' + 1) + m - 1)) = ⟨i.val + 1, by omega⟩ :=
        Fin.ext hi'
      rw [hi'_eq]
      exact shuffleRep_T_succ_consSelected ρ ⟨i.val, by omega⟩ h M'
    have hM := ih ⟨i.val + 1, hlt⟩ ⟨i'.val + 1, hlt'⟩ (by simp; omega) (by simp [hi'])
    rw [tailAdditiveJucysMurphy_of_lt hlt, tailAdditiveJucysMurphy_of_lt hlt']
    simp only [map_add, map_mul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      mul_apply_eq_comp, Pi.add_apply, Pi.smul_apply]
    congr 1
    · rw [hT _ N]
      have h₁ : (fun N₁ : ShuffleMask k' m ↦
          shuffleRep (k' + 1) ρ (tailAdditiveJucysMurphy q ⟨i'.val + 1, hlt'⟩)
            (shuffleRep (k' + 1) ρ (T q ⟨i'.val, by omega⟩) g) N₁.consSelected) =
          shuffleRep k' ρ (tailAdditiveJucysMurphy q ⟨i.val + 1, hlt⟩)
            (shuffleRep k' ρ (T q ⟨i.val, by omega⟩) (fun N₂ ↦ g N₂.consSelected)) := by
        funext N₁
        rw [hM _ N₁]
        have h₂ : (fun N₂ : ShuffleMask k' m ↦
            shuffleRep (k' + 1) ρ (T q ⟨i'.val, by omega⟩) g N₂.consSelected) =
            shuffleRep k' ρ (T q ⟨i.val, by omega⟩) (fun N₂ ↦ g N₂.consSelected) :=
          funext fun N₂ ↦ hT g N₂
        rw [h₂]
      rw [h₁]
    · rw [hT g N]

/-- Action of the first crossing `T q 0` on `firstRestProj R U f` along `N.consSelected`: if `N`
selects `0` then both crossed positions are selected and `firstRestProj` vanishes; if `N` leaves `0`
in the rest then `T q 0` swaps `0` out of the mask with sign `-1`. -/
private theorem shuffleRep_T_zero_firstRestProj_consSelected {k' l : ℕ}
    (ρ : TypeAHeckeAlgebra R q (l + 1) →ₐ[R] Module.End R U)
    (f : ShuffleMask (k' + 1) (l + 1) → U) :
    (fun N : ShuffleMask k' (l + 1) ↦
      shuffleRep (k' + 1) ρ (T (n := (k' + 1) + (l + 1)) q ⟨0, by omega⟩) (firstRestProj R U f)
        N.consSelected) =
      -firstRestProj R U fun N ↦
        f (N.consSelected.swap (BraidGroup.strand (⟨0, by omega⟩ : Fin ((k' + 1) + (l + 1) - 1)))
          (BraidGroup.strandSucc (⟨0, by omega⟩ : Fin ((k' + 1) + (l + 1) - 1)))) := by
  set z : Fin ((k' + 1) + (l + 1) - 1) := ⟨0, by omega⟩
  have ha0 : BraidGroup.strand z = (0 : Fin ((k' + 1) + (l + 1))) := Fin.ext (by simp [z])
  have hshift0 : ShuffleMask.shiftSelectedEmb k' (l + 1) 0 = BraidGroup.strandSucc z :=
    Fin.ext (by simp [z])
  funext N
  have haN : BraidGroup.strand z ∈ N.consSelected.1 := ha0 ▸ ShuffleMask.zero_mem_consSelected N
  have h0N : (0 : Fin ((k' + 1) + (l + 1))) ∈ N.consSelected.1 :=
    ShuffleMask.zero_mem_consSelected N
  by_cases hN0 : (0 : Fin (k' + (l + 1))) ∈ N.1
  · have hbN : BraidGroup.strandSucc z ∈ N.consSelected.1 := by
      rwa [← hshift0, ShuffleMask.shiftSelectedEmb_mem_consSelected]
    rw [shuffleRep_T_apply_of_mem_of_mem ρ haN hbN]
    simp [h0N, hN0]
  · have hbN : BraidGroup.strandSucc z ∉ N.consSelected.1 := by
      rwa [← hshift0, ShuffleMask.shiftSelectedEmb_mem_consSelected]
    have hswap_notMem : (0 : Fin ((k' + 1) + (l + 1))) ∉
        (N.consSelected.swap (BraidGroup.strand z) (BraidGroup.strandSucc z)).1 := by
      rw [← ha0, ShuffleMask.mem_swap, Equiv.swap_apply_left]
      exact hbN
    rw [shuffleRep_T_apply_of_mem_of_notMem ρ haN hbN]
    simp only [firstRestProj_apply, h0N, hswap_notMem, hN0, ↓reduceIte, Pi.neg_apply,
      smul_zero, zero_sub]
    rfl

/-- Branch 1 of the `(JM)` induction: `0 ∉ S.1` and `1 ∈ S.1` (`k = k' + 1`), reducing to
`(k', l)` with the same rest representation `ρ`. -/
private theorem tailAdditiveJM_branch_selected {k' l : ℕ}
    (ρ : TypeAHeckeAlgebra R q (l + 1) →ₐ[R] Module.End R U)
    (ih : ∀ (f : ShuffleMask k' (l + 1) → U) (S : ShuffleMask k' (l + 1)),
      (0 : Fin (k' + (l + 1))) ∉ S.1 →
      shuffleRep k' ρ (tailAdditiveJucysMurphy q (0 : Fin (k' + (l + 1))))
          (firstRestProj R U f) S =
        ρ (tailAdditiveJucysMurphy q (0 : Fin (l + 1))) (f S))
    (f : ShuffleMask (k' + 1) (l + 1) → U) (S : ShuffleMask (k' + 1) (l + 1))
    (hS0 : (0 : Fin ((k' + 1) + (l + 1))) ∉ S.1)
    (hbS : BraidGroup.strandSucc (⟨0, by omega⟩ : Fin ((k' + 1) + (l + 1) - 1)) ∈ S.1) :
    shuffleRep (k' + 1) ρ (tailAdditiveJucysMurphy q (0 : Fin ((k' + 1) + (l + 1))))
        (firstRestProj R U f) S =
      ρ (tailAdditiveJucysMurphy q (0 : Fin (l + 1))) (f S) := by
  let z : Fin ((k' + 1) + l) := ⟨0, by omega⟩
  have hbS' : BraidGroup.strandSucc (z : Fin ((k' + 1) + (l + 1) - 1)) ∈ S.1 := hbS
  have ha0 : BraidGroup.strand (z : Fin ((k' + 1) + (l + 1) - 1)) =
      (0 : Fin ((k' + 1) + (l + 1))) := Fin.ext (by simp [z])
  have hshift0 : ShuffleMask.shiftSelectedEmb k' (l + 1) 0 =
      BraidGroup.strandSucc (z : Fin ((k' + 1) + (l + 1) - 1)) := Fin.ext (by simp [z])
  have haS : BraidGroup.strand (z : Fin ((k' + 1) + (l + 1) - 1)) ∉ S.1 := ha0 ▸ hS0
  have hz0 : (0 : Fin ((k' + 1) + (l + 1))) = z.castSucc := Fin.ext rfl
  rw [hz0, tailAdditiveJucysMurphy_castSucc]
  simp only [map_add, map_mul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    mul_apply_eq_comp, Pi.add_apply, Pi.smul_apply]
  have hswap_mem : (0 : Fin ((k' + 1) + (l + 1))) ∈
      (S.swap (BraidGroup.strand (z : Fin ((k' + 1) + (l + 1) - 1)))
        (BraidGroup.strandSucc (z : Fin ((k' + 1) + (l + 1) - 1)))).1 := by
    rw [← ha0, ShuffleMask.mem_swap, Equiv.swap_apply_left]
    exact hbS'
  have hsecond : shuffleRep (k' + 1) ρ (T (n := (k' + 1) + (l + 1)) q z)
      (firstRestProj R U f) S = 0 := by
    rw [shuffleRep_T_apply_of_notMem_of_mem ρ haS hbS']
    simp [hswap_mem]
  rw [hsecond, smul_zero, add_zero, shuffleRep_T_apply_of_notMem_of_mem ρ haS hbS']
  let S₀ : ShuffleMask k' (l + 1) := ShuffleMask.tailOfZeroMem _ hswap_mem
  have hS₀_eq :
      S₀.consSelected = S.swap (BraidGroup.strand (z : Fin ((k' + 1) + (l + 1) - 1)))
        (BraidGroup.strandSucc (z : Fin ((k' + 1) + (l + 1) - 1))) :=
    ShuffleMask.consSelected_tailOfZeroMem _ hswap_mem
  have hS₀_notMem : (0 : Fin (k' + (l + 1))) ∉ S₀.1 := fun hmem ↦ by
    have h1 := ShuffleMask.shiftSelectedEmb_mem_consSelected.mpr hmem
    rw [hS₀_eq, ShuffleMask.mem_swap, hshift0, Equiv.swap_apply_right] at h1
    exact haS h1
  let f_sub : ShuffleMask k' (l + 1) → U := fun N ↦
    f (N.consSelected.swap (BraidGroup.strand (z : Fin ((k' + 1) + (l + 1) - 1)))
      (BraidGroup.strandSucc (z : Fin ((k' + 1) + (l + 1) - 1))))
  have hz_succ_val : (z.succ : ℕ) = ((0 : Fin (k' + (l + 1))) : ℕ) + 1 := by simp [z]
  have hinter := intertwinesConsSelected_tailAdditiveJucysMurphy ρ (k' + (l + 1) - 1)
    (0 : Fin (k' + (l + 1))) z.succ (by simp [Nat.zero_mod]) hz_succ_val
    (shuffleRep (k' + 1) ρ (T (n := (k' + 1) + (l + 1)) q z) (firstRestProj R U f)) S₀
  rw [← hS₀_eq, hinter, shuffleRep_T_zero_firstRestProj_consSelected ρ f, map_neg, Pi.neg_apply,
    neg_neg, ih f_sub S₀ hS₀_notMem]
  simp only [f_sub, hS₀_eq, ShuffleMask.swap_swap]

/-- Action of the first crossing `T q 0` on `firstRestProj R U f` along `N.consRest`: if `N`
selects `0` then `T q 0` swaps `0` into the mask where `firstRestProj` vanishes; if `N` leaves `0`
in the rest then `T q 0` acts fiberwise by the first rest generator `ρ (T q 0)`. -/
private theorem shuffleRep_T_zero_firstRestProj_consRest {k l' : ℕ}
    (ρ : TypeAHeckeAlgebra R q (l' + 2) →ₐ[R] Module.End R U)
    (f : ShuffleMask k (l' + 2) → U) :
    (fun N : ShuffleMask k (l' + 1) ↦
      shuffleRep k ρ (T (n := k + (l' + 1) + 1) q (0 : Fin (k + (l' + 1)))) (firstRestProj R U f)
        N.consRest) =
      firstRestProj R U fun N ↦ ρ (T (n := l' + 2) q (0 : Fin (l' + 1))) (f N.consRest) := by
  set z : Fin (k + (l' + 1)) := 0
  have ha0 : BraidGroup.strand z = (0 : Fin (k + (l' + 2))) := Fin.ext (by simp [z])
  have hsucc0 : (0 : Fin (k + (l' + 1))).succ = BraidGroup.strandSucc z := Fin.ext (by simp [z])
  funext N
  have haN : BraidGroup.strand z ∉ N.consRest.1 := ha0 ▸ ShuffleMask.zero_notMem_consRest N
  by_cases hN0 : (0 : Fin (k + (l' + 1))) ∈ N.1
  · have hbN : BraidGroup.strandSucc z ∈ N.consRest.1 := by
      rwa [← hsucc0, ShuffleMask.succ_mem_consRest]
    have hswap0 : (0 : Fin (k + (l' + 2))) ∈
        (N.consRest.swap (BraidGroup.strand z) (BraidGroup.strandSucc z)).1 := by
      rw [← ha0, ShuffleMask.mem_swap, Equiv.swap_apply_left]
      exact hbN
    rw [shuffleRep_T_apply_of_notMem_of_mem ρ haN hbN]
    simp [hswap0, hN0]
  · have hbN : BraidGroup.strandSucc z ∉ N.consRest.1 := by
      rwa [← hsucc0, ShuffleMask.succ_mem_consRest]
    rw [shuffleRep_T_apply_of_notMem_of_notMem ρ haN hbN]
    simp only [firstRestProj_apply, ShuffleMask.zero_notMem_consRest, ↓reduceIte, hN0]
    congr 3
    ext
    simp [ha0]

/-- Branch 2 of the `(JM)` induction: `0 ∉ S.1` and `1 ∉ S.1` (`l = l' + 1`), reducing to
`(k, l')` with rest representation `ρ.comp (tailIncl q (l' + 1))`. -/
private theorem tailAdditiveJM_branch_rest {k l' : ℕ}
    (ρ : TypeAHeckeAlgebra R q (l' + 2) →ₐ[R] Module.End R U)
    (ih : ∀ (f : ShuffleMask k (l' + 1) → U) (S : ShuffleMask k (l' + 1)),
      (0 : Fin (k + (l' + 1))) ∉ S.1 →
      shuffleRep k (ρ.comp (tailIncl q (l' + 1)))
          (tailAdditiveJucysMurphy q (0 : Fin (k + (l' + 1)))) (firstRestProj R U f) S =
        (ρ.comp (tailIncl q (l' + 1))) (tailAdditiveJucysMurphy q (0 : Fin (l' + 1))) (f S))
    (f : ShuffleMask k (l' + 2) → U) (S : ShuffleMask k (l' + 2))
    (hS0 : (0 : Fin (k + (l' + 2))) ∉ S.1)
    (hbS : BraidGroup.strandSucc (0 : Fin (k + (l' + 1))) ∉ S.1) :
    shuffleRep k ρ (tailAdditiveJucysMurphy q (0 : Fin (k + (l' + 2))))
        (firstRestProj R U f) S =
      ρ (tailAdditiveJucysMurphy q (0 : Fin (l' + 2))) (f S) := by
  let z : Fin (k + (l' + 1)) := 0
  have ha0 : BraidGroup.strand z = (0 : Fin (k + (l' + 2))) := Fin.ext (by simp [z])
  have hsucc0 : (0 : Fin (k + (l' + 1))).succ = BraidGroup.strandSucc z := Fin.ext (by simp [z])
  have haS : BraidGroup.strand z ∉ S.1 := ha0 ▸ hS0
  have hz0 : (0 : Fin (k + (l' + 2))) = z.castSucc := Fin.ext rfl
  rw [hz0, tailAdditiveJucysMurphy_castSucc]
  simp only [map_add, map_mul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    mul_apply_eq_comp, Pi.add_apply, Pi.smul_apply]
  have hT_at_S : ∀ h : ShuffleMask k (l' + 2) → U,
      shuffleRep k ρ (T (n := k + (l' + 1) + 1) q z) h S =
        ρ (T (n := l' + 2) q (0 : Fin (l' + 1))) (h S) := fun h ↦ by
    rw [shuffleRep_T_apply_of_notMem_of_notMem ρ haS hbS]
    congr 3
    ext
    simp [ha0]
  rw [hT_at_S, hT_at_S]
  simp only [firstRestProj_apply, hS0, ↓reduceIte]
  let S₁ : ShuffleMask k (l' + 1) := ShuffleMask.tailOfZeroNotMem S hS0
  have hS₁_eq : S₁.consRest = S := ShuffleMask.consRest_tailOfZeroNotMem S hS0
  have hS₁_notMem : (0 : Fin (k + (l' + 1))) ∉ S₁.1 := fun hmem ↦ by
    have h1 := ShuffleMask.succ_mem_consRest.mpr hmem
    rw [hS₁_eq, hsucc0] at h1
    exact hbS h1
  let g_sub : ShuffleMask k (l' + 1) → U := fun N ↦
    ρ (T (n := l' + 2) q (0 : Fin (l' + 1))) (f N.consRest)
  rw [← hS₁_eq, ← tailIncl_tailAdditiveJucysMurphy z, shuffleRep_tailIncl_consRest,
    shuffleRep_T_zero_firstRestProj_consRest ρ f, ih g_sub S₁ hS₁_notMem,
    tailAdditiveJucysMurphy_zero_succ l']
  simp [AlgHom.comp_apply, g_sub, hS₁_eq, mul_apply_eq_comp]

/-- Core induction on `n = k + l`: compressing `tailAdditiveJucysMurphy q 0` by `firstRestProj`
evaluates at every mask `S` with `0 ∉ S.1` to `ρ (tailAdditiveJucysMurphy q 0) (f S)`. -/
private theorem shuffleRep_tailAdditiveJucysMurphy_zero_firstRestProj_aux :
    ∀ (n k l : ℕ), k + l = n →
      ∀ (ρ : TypeAHeckeAlgebra R q (l + 1) →ₐ[R] Module.End R U)
        (f : ShuffleMask k (l + 1) → U) (S : ShuffleMask k (l + 1)),
        (0 : Fin (k + (l + 1))) ∉ S.1 →
        shuffleRep k ρ (tailAdditiveJucysMurphy q (0 : Fin (k + (l + 1))))
            (firstRestProj R U f) S =
          ρ (tailAdditiveJucysMurphy q (0 : Fin (l + 1))) (f S) := by
  intro n
  induction n with
  | zero =>
    intro k l hn ρ f S _
    obtain ⟨rfl, rfl⟩ : k = 0 ∧ l = 0 := by omega
    simp
  | succ n ih =>
    intro k l hn ρ f S hS0
    let i₀ : Fin (k + (l + 1) - 1) := ⟨0, by omega⟩
    have ha0 : BraidGroup.strand i₀ = (0 : Fin (k + (l + 1))) := Fin.ext (by simp [i₀])
    have haS : BraidGroup.strand i₀ ∉ S.1 := ha0 ▸ hS0
    by_cases hbS : BraidGroup.strandSucc i₀ ∈ S.1
    · have hk_pos : 0 < k := by
        rw [← S.2]
        exact card_pos.mpr ⟨_, hbS⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact tailAdditiveJM_branch_selected ρ (ih k' l (by omega) ρ) f S hS0 hbS
    · have hab_lt : BraidGroup.strand i₀ < BraidGroup.strandSucc i₀ := by
        rw [Fin.lt_def]
        simp [i₀]
      have hl_ge : 2 ≤ l + 1 := by
        have := ShuffleMask.restIndex_add_two_le hab_lt le_rfl haS hbS
        omega
      obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      exact tailAdditiveJM_branch_rest ρ (ih k l' (by omega) (ρ.comp (tailIncl q (l' + 1))))
        f S hS0 hbS

/-- **Pointwise first-site additive Jucys–Murphy compression on the rest block.** Over every
commutative ring `R` and unit `q`, including at `q² = 1`, evaluating
`tailAdditiveJucysMurphy q 0` on `firstRestProj R U f` at `M.consRest` acts solely on the rest
module `U` by `tailAdditiveJucysMurphy q 0`. -/
theorem shuffleRep_tailAdditiveJucysMurphy_zero_firstRestProj_consRest
    (ρ : TypeAHeckeAlgebra R q (l + 1) →ₐ[R] Module.End R U)
    (f : ShuffleMask k (l + 1) → U) (M : ShuffleMask k l) :
    shuffleRep k ρ (tailAdditiveJucysMurphy q (0 : Fin (k + (l + 1))))
        (firstRestProj R U f) M.consRest =
      ρ (tailAdditiveJucysMurphy q (0 : Fin (l + 1))) (f M.consRest) :=
  shuffleRep_tailAdditiveJucysMurphy_zero_firstRestProj_aux (k + l) k l rfl ρ f M.consRest
    (ShuffleMask.zero_notMem_consRest M)

/-- **First-site additive Jucys–Murphy rest-compression identity.** Compressing the first-site
additive Jucys–Murphy operator on `Sh_k(U)` by `firstRestProj` yields the first-site additive
Jucys–Murphy operator of the rest module `U` acting fiberwise on `firstRestProj`, valid over every
commutative ring `R` and unit `q` (including `q² = 1`). -/
theorem firstRestProj_comp_shuffleRep_tailAdditiveJucysMurphy_zero_comp_firstRestProj
    (k : ℕ) (ρ : TypeAHeckeAlgebra R q (l + 1) →ₐ[R] Module.End R U) :
    firstRestProj R U ∘ₗ
        shuffleRep k ρ (tailAdditiveJucysMurphy q (0 : Fin (k + (l + 1)))) ∘ₗ
          firstRestProj R U =
      (ρ (tailAdditiveJucysMurphy q (0 : Fin (l + 1)))).compLeft (ShuffleMask k (l + 1)) ∘ₗ
        firstRestProj R U := by
  refine LinearMap.ext fun f ↦ funext fun S ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.compLeft_apply, Function.comp_apply,
    firstRestProj_apply]
  split_ifs with hS0
  · simp
  · exact shuffleRep_tailAdditiveJucysMurphy_zero_firstRestProj_aux (k + l) k l rfl ρ f S hS0

/-- **First-site normalized Jucys–Murphy rest-compression identity.** Compressing the first-site
normalized Jucys–Murphy operator `tailJucysMurphy q 0` on `Sh_k(U)` by `firstRestProj` yields the
first-site normalized Jucys–Murphy operator of the rest module `U` acting fiberwise on
`firstRestProj`. -/
theorem firstRestProj_comp_shuffleRep_tailJucysMurphy_zero_comp_firstRestProj
    (k : ℕ) (ρ : TypeAHeckeAlgebra R q (l + 1) →ₐ[R] Module.End R U) :
    firstRestProj R U ∘ₗ
        shuffleRep k ρ (tailJucysMurphy q (0 : Fin (k + (l + 1)))) ∘ₗ
          firstRestProj R U =
      (ρ (tailJucysMurphy q (0 : Fin (l + 1)))).compLeft (ShuffleMask k (l + 1)) ∘ₗ
        firstRestProj R U := by
  rw [tailJucysMurphy_eq_one_add_smul_tailAdditiveJucysMurphy,
    tailJucysMurphy_eq_one_add_smul_tailAdditiveJucysMurphy, map_add, map_one, map_smul, map_add,
    map_one, map_smul]
  refine LinearMap.ext fun f ↦ funext fun S ↦ ?_
  have hS := congrFun (LinearMap.congr_fun
    (firstRestProj_comp_shuffleRep_tailAdditiveJucysMurphy_zero_comp_firstRestProj k ρ) f) S
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    one_apply_eq_self, LinearMap.compLeft_apply, Function.comp_apply] at hS ⊢
  rw [map_add, map_smul, Pi.add_apply, Pi.smul_apply, hS]
  by_cases h0 : (0 : Fin (k + (l + 1))) ∈ S.1 <;> simp [firstRestProj_apply, h0]

/-- **Pointwise first-site normalized Jucys–Murphy compression on the rest block.** -/
theorem shuffleRep_tailJucysMurphy_zero_firstRestProj_consRest
    (ρ : TypeAHeckeAlgebra R q (l + 1) →ₐ[R] Module.End R U)
    (f : ShuffleMask k (l + 1) → U) (M : ShuffleMask k l) :
    shuffleRep k ρ (tailJucysMurphy q (0 : Fin (k + (l + 1))))
        (firstRestProj R U f) M.consRest =
      ρ (tailJucysMurphy q (0 : Fin (l + 1))) (f M.consRest) := by
  have h := congrFun (LinearMap.congr_fun
    (firstRestProj_comp_shuffleRep_tailJucysMurphy_zero_comp_firstRestProj k ρ) f) M.consRest
  simpa [ShuffleMask.zero_notMem_consRest] using h

end Module

/-! ### Orthogonal projections and compression on the `PiLp 2` shuffle Hilbert carrier -/

section Hilbert

variable {𝕜 : Type*} [RCLike 𝕜] {q : 𝕜ˣ} {k l : ℕ}
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U]

section Projections

variable (𝕜 U) [NeZero (k + l)]

/-- Orthogonal projection onto masks selecting site `0` on the `PiLp 2` shuffle Hilbert carrier. -/
noncomputable def firstSelectedHilbertProj :
    Module.End 𝕜 (PiLp 2 fun _ : ShuffleMask k l ↦ U) :=
  ((WithLp.linearEquiv 2 𝕜 (ShuffleMask k l → U)).symm.conjAlgEquiv 𝕜)
    (firstSelectedProj 𝕜 U)

/-- Orthogonal projection onto masks leaving site `0` in the rest on the `PiLp 2` shuffle Hilbert
carrier. -/
noncomputable def firstRestHilbertProj :
    Module.End 𝕜 (PiLp 2 fun _ : ShuffleMask k l ↦ U) :=
  ((WithLp.linearEquiv 2 𝕜 (ShuffleMask k l → U)).symm.conjAlgEquiv 𝕜)
    (firstRestProj 𝕜 U)

variable {𝕜 U}

/-- Pointwise evaluation of `firstSelectedHilbertProj` at mask `S`. -/
@[simp]
theorem firstSelectedHilbertProj_apply (f : PiLp 2 fun _ : ShuffleMask k l ↦ U)
    (S : ShuffleMask k l) :
    firstSelectedHilbertProj 𝕜 U f S = if (0 : Fin (k + l)) ∈ S.1 then f S else 0 :=
  (rfl)

/-- Pointwise evaluation of `firstRestHilbertProj` at mask `S`. -/
@[simp]
theorem firstRestHilbertProj_apply (f : PiLp 2 fun _ : ShuffleMask k l ↦ U)
    (S : ShuffleMask k l) :
    firstRestHilbertProj 𝕜 U f S = if (0 : Fin (k + l)) ∈ S.1 then 0 else f S :=
  (rfl)

/-- `firstSelectedHilbertProj` and `firstRestHilbertProj` sum to `1`. -/
@[simp]
theorem firstSelectedHilbertProj_add_firstRestHilbertProj :
    (firstSelectedHilbertProj 𝕜 U : Module.End 𝕜 (PiLp 2 fun _ : ShuffleMask k l ↦ U)) +
      firstRestHilbertProj 𝕜 U = 1 := by
  rw [firstSelectedHilbertProj, firstRestHilbertProj, ← map_add,
    firstSelectedProj_add_firstRestProj, map_one]

/-- `firstSelectedHilbertProj` is idempotent under composition. -/
@[simp]
theorem firstSelectedHilbertProj_comp_firstSelectedHilbertProj :
    (firstSelectedHilbertProj 𝕜 U : Module.End 𝕜 (PiLp 2 fun _ : ShuffleMask k l ↦ U)) ∘ₗ
      firstSelectedHilbertProj 𝕜 U = firstSelectedHilbertProj 𝕜 U := by
  refine LinearMap.ext fun f ↦ PiLp.ext fun S ↦ ?_
  by_cases h : (0 : Fin (k + l)) ∈ S.1 <;> simp [h]

/-- `firstRestHilbertProj` is idempotent under composition. -/
@[simp]
theorem firstRestHilbertProj_comp_firstRestHilbertProj :
    (firstRestHilbertProj 𝕜 U : Module.End 𝕜 (PiLp 2 fun _ : ShuffleMask k l ↦ U)) ∘ₗ
      firstRestHilbertProj 𝕜 U = firstRestHilbertProj 𝕜 U := by
  refine LinearMap.ext fun f ↦ PiLp.ext fun S ↦ ?_
  by_cases h : (0 : Fin (k + l)) ∈ S.1 <;> simp [h]

/-- `firstSelectedHilbertProj` annihilates the image of `firstRestHilbertProj`. -/
@[simp]
theorem firstSelectedHilbertProj_comp_firstRestHilbertProj :
    (firstSelectedHilbertProj 𝕜 U : Module.End 𝕜 (PiLp 2 fun _ : ShuffleMask k l ↦ U)) ∘ₗ
      firstRestHilbertProj 𝕜 U = 0 := by
  refine LinearMap.ext fun f ↦ PiLp.ext fun S ↦ ?_
  by_cases h : (0 : Fin (k + l)) ∈ S.1 <;> simp [h]

/-- `firstRestHilbertProj` annihilates the image of `firstSelectedHilbertProj`. -/
@[simp]
theorem firstRestHilbertProj_comp_firstSelectedHilbertProj :
    (firstRestHilbertProj 𝕜 U : Module.End 𝕜 (PiLp 2 fun _ : ShuffleMask k l ↦ U)) ∘ₗ
      firstSelectedHilbertProj 𝕜 U = 0 := by
  refine LinearMap.ext fun f ↦ PiLp.ext fun S ↦ ?_
  by_cases h : (0 : Fin (k + l)) ∈ S.1 <;> simp [h]

/-- `firstSelectedHilbertProj` is symmetric with respect to the `PiLp 2` inner product. -/
theorem isSymmetric_firstSelectedHilbertProj :
    (firstSelectedHilbertProj 𝕜 U :
      Module.End 𝕜 (PiLp 2 fun _ : ShuffleMask k l ↦ U)).IsSymmetric := by
  intro f g
  simp only [PiLp.inner_apply, firstSelectedHilbertProj_apply]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  by_cases h : (0 : Fin (k + l)) ∈ S.1 <;> simp [h]

/-- `firstRestHilbertProj` is symmetric with respect to the `PiLp 2` inner product. -/
theorem isSymmetric_firstRestHilbertProj :
    (firstRestHilbertProj 𝕜 U :
      Module.End 𝕜 (PiLp 2 fun _ : ShuffleMask k l ↦ U)).IsSymmetric := by
  intro f g
  simp only [PiLp.inner_apply, firstRestHilbertProj_apply]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  by_cases h : (0 : Fin (k + l)) ∈ S.1 <;> simp [h]

/-- The images of `firstSelectedHilbertProj` and `firstRestHilbertProj` are pairwise orthogonal. -/
theorem inner_firstSelectedHilbertProj_firstRestHilbertProj
    (f g : PiLp 2 fun _ : ShuffleMask k l ↦ U) :
    ⟪firstSelectedHilbertProj 𝕜 U f, firstRestHilbertProj 𝕜 U g⟫_𝕜 = 0 := by
  simp only [PiLp.inner_apply, firstSelectedHilbertProj_apply, firstRestHilbertProj_apply]
  refine Finset.sum_eq_zero fun S _ ↦ ?_
  by_cases h : (0 : Fin (k + l)) ∈ S.1 <;> simp [h]

/-- `firstSelectedHilbertProj` is continuous on the `PiLp 2` shuffle Hilbert carrier. -/
theorem continuous_firstSelectedHilbertProj :
    Continuous (firstSelectedHilbertProj 𝕜 U :
      Module.End 𝕜 (PiLp 2 fun _ : ShuffleMask k l ↦ U)) := by
  -- Expose the `toLp ∘ firstSelectedProj ∘ ofLp` definition to apply `PiLp.continuous_toLp`.
  change Continuous (fun f ↦ WithLp.toLp 2 (firstSelectedProj 𝕜 U (WithLp.ofLp f)))
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun S ↦ ?_)
  by_cases h : (0 : Fin (k + l)) ∈ S.1
  · simpa [h] using PiLp.continuous_apply 2 (fun _ : ShuffleMask k l ↦ U) S
  · simpa [h] using continuous_const

/-- `firstRestHilbertProj` is continuous on the `PiLp 2` shuffle Hilbert carrier. -/
theorem continuous_firstRestHilbertProj :
    Continuous (firstRestHilbertProj 𝕜 U :
      Module.End 𝕜 (PiLp 2 fun _ : ShuffleMask k l ↦ U)) := by
  -- Expose the `toLp ∘ firstRestProj ∘ ofLp` definition to apply `PiLp.continuous_toLp`.
  change Continuous (fun f ↦ WithLp.toLp 2 (firstRestProj 𝕜 U (WithLp.ofLp f)))
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun S ↦ ?_)
  by_cases h : (0 : Fin (k + l)) ∈ S.1
  · simpa [h] using continuous_const
  · simpa [h] using PiLp.continuous_apply 2 (fun _ : ShuffleMask k l ↦ U) S

end Projections

/-- Tail normalized Jucys–Murphy elements act symmetrically on `shuffleHilbertRep` for a real
parameter and symmetric rest generators. -/
theorem isSymmetric_shuffleHilbertRep_tailJucysMurphy (hq : star (q : 𝕜) = q)
    (ρ : TypeAHeckeAlgebra 𝕜 q l →ₐ[𝕜] Module.End 𝕜 U)
    (hρ : ∀ i, (ρ (T q i)).IsSymmetric) (i : Fin (k + l)) :
    (shuffleHilbertRep k ρ (tailJucysMurphy q i)).IsSymmetric := by
  have : Fact (IsSelfAdjoint (q : 𝕜)) := ⟨hq⟩
  intro f g
  simpa only [star_tailJucysMurphy] using
    inner_shuffleHilbertRep_star k ρ hρ (tailJucysMurphy q i) f g

/-- Tail additive Jucys–Murphy elements act symmetrically on `shuffleHilbertRep` for a real
parameter and symmetric rest generators. -/
theorem isSymmetric_shuffleHilbertRep_tailAdditiveJucysMurphy (hq : star (q : 𝕜) = q)
    (ρ : TypeAHeckeAlgebra 𝕜 q l →ₐ[𝕜] Module.End 𝕜 U)
    (hρ : ∀ i, (ρ (T q i)).IsSymmetric) (i : Fin (k + l)) :
    (shuffleHilbertRep k ρ (tailAdditiveJucysMurphy q i)).IsSymmetric := by
  have : Fact (IsSelfAdjoint (q : 𝕜)) := ⟨hq⟩
  intro f g
  simpa only [star_tailAdditiveJucysMurphy] using
    inner_shuffleHilbertRep_star k ρ hρ (tailAdditiveJucysMurphy q i) f g

/-- **Pointwise Hilbert-carrier first-site additive Jucys–Murphy rest-compression identity.** -/
theorem firstRestHilbertProj_shuffleHilbertRep_tailAdditiveJucysMurphy_zero
    (k : ℕ) (ρ : TypeAHeckeAlgebra 𝕜 q (l + 1) →ₐ[𝕜] Module.End 𝕜 U)
    (f : PiLp 2 fun _ : ShuffleMask k (l + 1) ↦ U) (S : ShuffleMask k (l + 1)) :
    firstRestHilbertProj 𝕜 U
        (shuffleHilbertRep k ρ (tailAdditiveJucysMurphy q (0 : Fin (k + (l + 1))))
          (firstRestHilbertProj 𝕜 U f)) S =
      ρ (tailAdditiveJucysMurphy q (0 : Fin (l + 1))) (firstRestHilbertProj 𝕜 U f S) := by
  have hproj : WithLp.ofLp (firstRestHilbertProj 𝕜 U f) = firstRestProj 𝕜 U (WithLp.ofLp f) :=
    funext fun M ↦ firstRestHilbertProj_apply f M
  have h := congrFun (LinearMap.congr_fun
    (firstRestProj_comp_shuffleRep_tailAdditiveJucysMurphy_zero_comp_firstRestProj k ρ)
    (WithLp.ofLp f)) S
  simpa only [LinearMap.comp_apply, LinearMap.compLeft_apply, Function.comp_apply,
    firstRestHilbertProj_apply, shuffleHilbertRep_apply, hproj, firstRestProj_apply] using h

/-- **Pointwise Hilbert-carrier first-site normalized Jucys–Murphy rest-compression identity.** -/
theorem firstRestHilbertProj_shuffleHilbertRep_tailJucysMurphy_zero
    (k : ℕ) (ρ : TypeAHeckeAlgebra 𝕜 q (l + 1) →ₐ[𝕜] Module.End 𝕜 U)
    (f : PiLp 2 fun _ : ShuffleMask k (l + 1) ↦ U) (S : ShuffleMask k (l + 1)) :
    firstRestHilbertProj 𝕜 U
        (shuffleHilbertRep k ρ (tailJucysMurphy q (0 : Fin (k + (l + 1))))
          (firstRestHilbertProj 𝕜 U f)) S =
      ρ (tailJucysMurphy q (0 : Fin (l + 1))) (firstRestHilbertProj 𝕜 U f S) := by
  have hproj : WithLp.ofLp (firstRestHilbertProj 𝕜 U f) = firstRestProj 𝕜 U (WithLp.ofLp f) :=
    funext fun M ↦ firstRestHilbertProj_apply f M
  have h := congrFun (LinearMap.congr_fun
    (firstRestProj_comp_shuffleRep_tailJucysMurphy_zero_comp_firstRestProj k ρ)
    (WithLp.ofLp f)) S
  simpa only [LinearMap.comp_apply, LinearMap.compLeft_apply, Function.comp_apply,
    firstRestHilbertProj_apply, shuffleHilbertRep_apply, hproj, firstRestProj_apply] using h

/-- **Operator-level Hilbert-carrier first-site additive Jucys–Murphy rest-compression identity.**
Compressing `shuffleHilbertRep k ρ (tailAdditiveJucysMurphy q 0)` by `firstRestHilbertProj` equals
the fiberwise action of `ρ (tailAdditiveJucysMurphy q 0)` on `firstRestHilbertProj`. -/
theorem firstRestHilbertProj_comp_shuffleHilbertRep_tailAdditiveJucysMurphy_zero_comp
    (k : ℕ) (ρ : TypeAHeckeAlgebra 𝕜 q (l + 1) →ₐ[𝕜] Module.End 𝕜 U) :
    firstRestHilbertProj 𝕜 U ∘ₗ
        shuffleHilbertRep k ρ (tailAdditiveJucysMurphy q (0 : Fin (k + (l + 1)))) ∘ₗ
          firstRestHilbertProj 𝕜 U =
      (((WithLp.linearEquiv 2 𝕜 (ShuffleMask k (l + 1) → U)).symm.conjAlgEquiv 𝕜)
          ((ρ (tailAdditiveJucysMurphy q (0 : Fin (l + 1)))).compLeft (ShuffleMask k (l + 1)))) ∘ₗ
        firstRestHilbertProj 𝕜 U :=
  LinearMap.ext fun f ↦ PiLp.ext fun S ↦
    firstRestHilbertProj_shuffleHilbertRep_tailAdditiveJucysMurphy_zero k ρ f S

/-- **Operator-level Hilbert-carrier first-site normalized Jucys–Murphy rest-compression identity.**
Compressing `shuffleHilbertRep k ρ (tailJucysMurphy q 0)` by `firstRestHilbertProj` equals the
fiberwise action of `ρ (tailJucysMurphy q 0)` on `firstRestHilbertProj`. -/
theorem firstRestHilbertProj_comp_shuffleHilbertRep_tailJucysMurphy_zero_comp
    (k : ℕ) (ρ : TypeAHeckeAlgebra 𝕜 q (l + 1) →ₐ[𝕜] Module.End 𝕜 U) :
    firstRestHilbertProj 𝕜 U ∘ₗ
        shuffleHilbertRep k ρ (tailJucysMurphy q (0 : Fin (k + (l + 1)))) ∘ₗ
          firstRestHilbertProj 𝕜 U =
      (((WithLp.linearEquiv 2 𝕜 (ShuffleMask k (l + 1) → U)).symm.conjAlgEquiv 𝕜)
          ((ρ (tailJucysMurphy q (0 : Fin (l + 1)))).compLeft (ShuffleMask k (l + 1)))) ∘ₗ
        firstRestHilbertProj 𝕜 U :=
  LinearMap.ext fun f ↦ PiLp.ext fun S ↦
    firstRestHilbertProj_shuffleHilbertRep_tailJucysMurphy_zero k ρ f S

end Hilbert

end TauCeti.TypeAHeckeAlgebra

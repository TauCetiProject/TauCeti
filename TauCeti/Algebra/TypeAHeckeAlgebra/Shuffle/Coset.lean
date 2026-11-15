/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.ReducedWord
public import TauCeti.Algebra.TypeAHeckeAlgebra.Shuffle.Induced
public import TauCeti.GroupTheory.Perm.Parabolic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.Pi

/-!
# Shuffle masks as minimal coset representatives, coset bases, and the sign gauge

Let `H_l = TypeAHeckeAlgebra R q l` act on an `R`-module `U` through `ρ`, and let
`Sh_k(U) = (ShuffleMask k l → U)` be the shuffle module of `H = TypeAHeckeAlgebra R q (k + l)`
(`TauCeti.TypeAHeckeAlgebra.shuffleRep k ρ`). This file connects the mask combinatorics and
triangularity of `TauCeti.Algebra.TypeAHeckeAlgebra.Shuffle.Basic` to the Coxeter parabolic theory
of `S_k × S_l ≤ S_(k+l)` (`TauCeti.blockParabolicSet k l`):

1. **Masks and minimal coset representatives.** Permutations of `Fin (k + l)` act on
   `ShuffleMask k l` (`TauCeti.TypeAHeckeAlgebra.ShuffleMask.perm`), with stabilizer of the initial
   mask `{0, …, k - 1}` equal to `(Equiv.Perm.finSumPermHom k l).range`. Evaluating any shuffle path
   to a mask `S` in `TauCeti.permCoxeterSystem (k + l)` produces a well-defined `(k, l)`-shuffle
   `S.toPerm` (`TauCeti.TypeAHeckeAlgebra.ShuffleMask.toPerm`) of Coxeter length `S.length` and sign
   `(-1) ^ S.length`, and `TauCeti.TypeAHeckeAlgebra.ShuffleMask.minimalCosetRepEquiv` identifies
   `ShuffleMask k l` with the minimal left coset representatives of `S_k × S_l` in `S_(k+l)`.
   Consequently every shuffle path is a reduced word, whose Hecke generator product is
   `Tw q (permCoxeterSystem (k + l)) S.toPerm`.
2. **The coset basis of `Sh_k(U)`.** Sending the vector `u` at `S` to
   `T_(S.toPerm) • (Pi.single initial u)` defines an `R`-linear automorphism
   `TauCeti.TypeAHeckeAlgebra.shuffleCosetEquiv` of `Sh_k(U)` over every commutative ring `R`, unit
   `q : Rˣ`, and `H_l`-module `U`: after rescaling by `(-1) ^ S.length`, the operator is `1 - N`
   where `N` strictly raises mask lengths and so satisfies `N ^ (k * l + 1) = 0`. Mapping a basis
   `b` of `U` across this automorphism produces the PBW coset basis
   `TauCeti.TypeAHeckeAlgebra.shuffleCosetBasis` of `Sh_k(U)`, indexed by `ShuffleMask k l × ι`.
3. **The mask-length sign gauge.** Multiplying the value at each mask `S` by `(-1) ^ S.length`
   (`TauCeti.TypeAHeckeAlgebra.shuffleSignEquiv`) conjugates `shuffleRep k ρ` to an isomorphic
   Hecke representation `TauCeti.TypeAHeckeAlgebra.unsignedShuffleRep k ρ` in which mixed exchanges
   carry positive signs `[[q - q⁻¹, 1], [1, 0]]`, inverse shuffle words act without signs on the
   initial mask, and `T_(S.toPerm)` has leading coefficient `+1` at `S`.

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.ShuffleMask.perm`: the action of `Equiv.Perm (Fin (k + l))` on masks.
* `TauCeti.TypeAHeckeAlgebra.ShuffleMask.toPerm`: the minimal coset representative of `S_k × S_l`
  associated to a mask.
* `TauCeti.TypeAHeckeAlgebra.ShuffleMask.minimalCosetRepEquiv`: the equivalence between
  `ShuffleMask k l` and minimal left coset representatives for `TauCeti.blockParabolicSet k l`.
* `TauCeti.TypeAHeckeAlgebra.shuffleCosetEquiv`: the `R`-linear automorphism of `Sh_k(U)` sending
  `Pi.single S u` to `T_(S.toPerm) • Pi.single initial u`.
* `TauCeti.TypeAHeckeAlgebra.shuffleCosetBasis`: the resulting basis of `Sh_k(U)` from a basis of
  `U`.
* `TauCeti.TypeAHeckeAlgebra.shuffleSignEquiv`: the involutive linear equivalence multiplying the
  value at `S` by `(-1) ^ S.length`.
* `TauCeti.TypeAHeckeAlgebra.unsignedShuffleRep`: `shuffleRep` conjugated by `shuffleSignEquiv`.

## Main results

* `TauCeti.TypeAHeckeAlgebra.ShuffleMask.isMinimalCosetRep_toPerm`,
  `TauCeti.TypeAHeckeAlgebra.ShuffleMask.length_toPerm`,
  `TauCeti.TypeAHeckeAlgebra.ShuffleMask.sign_toPerm`, and
  `TauCeti.TypeAHeckeAlgebra.ShuffleMask.IsShufflePath.isReduced`.
* `TauCeti.TypeAHeckeAlgebra.ShuffleMask.toPerm_initial_perm`: the minimal coset representative of
  any `π : Equiv.Perm (Fin (k + l))` is `(initial.perm π).toPerm`.
* `TauCeti.TypeAHeckeAlgebra.shuffleCosetEquiv_single` and
  `TauCeti.TypeAHeckeAlgebra.shuffleCosetBasis_apply`.
* `TauCeti.TypeAHeckeAlgebra.unsignedShuffleRep_T_apply_of_mem_of_notMem` and
  `TauCeti.TypeAHeckeAlgebra.unsignedShuffleRep_T_apply_of_notMem_of_mem`: the sign-free generator
  formulas on mixed pairs.
* `TauCeti.TypeAHeckeAlgebra.unsignedShuffleRep_shuffleInvWord_single_initial`: in
  `unsignedShuffleRep`, `shuffleInvWord q S` sends `Pi.single initial u` directly to
  `Pi.single S u`.

## References

* R. Dipper and G. James, *Representations of Hecke algebras of general linear groups*,
  Proc. London Math. Soc. (3) 52 (1986), 20–52.
* M. Geck and G. Pfeiffer, *Characters of Finite Coxeter Groups and Iwahori-Hecke Algebras*,
  OUP (2000), Section 2.1.
-/

public section

open Finset

namespace TauCeti.TypeAHeckeAlgebra

namespace ShuffleMask

variable {k l : ℕ}

/-- Every `(k, l)`-mask has length at most `k * l`: each of its `k` selected positions is preceded
by at most `l` rest positions. -/
theorem length_le_mul (S : ShuffleMask k l) : S.length ≤ k * l := by
  rw [length_def]
  refine (Finset.sum_le_card_nsmul S.1 _ l fun s _ ↦ ?_).trans_eq (by rw [S.2, smul_eq_mul])
  rw [restIndex_def]
  exact (Finset.card_filter_le _ _).trans_eq
    (by rw [Finset.card_compl, Fintype.card_fin, S.2, Nat.add_sub_cancel_left])

/-! ### Permuting masks -/

/-- The image of a mask under a permutation of `Fin (k + l)`. -/
def perm (π : Equiv.Perm (Fin (k + l))) (S : ShuffleMask k l) : ShuffleMask k l :=
  ⟨S.1.map π.toEmbedding, by rw [card_map, S.2]⟩

/-- A position lies in `S.perm π` exactly when `π⁻¹` carries it into `S`. -/
@[simp]
theorem mem_perm {π : Equiv.Perm (Fin (k + l))} {S : ShuffleMask k l} {x : Fin (k + l)} :
    x ∈ (S.perm π).1 ↔ π⁻¹ x ∈ S.1 := by
  simp [perm, mem_map_equiv, Equiv.Perm.inv_def]

/-- The identity permutation fixes every mask. -/
@[simp]
theorem perm_one (S : ShuffleMask k l) : S.perm 1 = S :=
  Subtype.ext <| Finset.ext fun x ↦ by simp

/-- Permutations act on masks from the left: `(S.perm π₂).perm π₁ = S.perm (π₁ * π₂)`. -/
theorem perm_mul (π₁ π₂ : Equiv.Perm (Fin (k + l))) (S : ShuffleMask k l) :
    S.perm (π₁ * π₂) = (S.perm π₂).perm π₁ :=
  Subtype.ext <| Finset.ext fun x ↦ by simp

/-- Permuting a mask by a 2-cycle is `ShuffleMask.swap`. -/
@[simp]
theorem perm_swap_eq (a b : Fin (k + l)) (S : ShuffleMask k l) :
    S.perm (Equiv.swap a b) = S.swap a b :=
  Subtype.ext <| Finset.ext fun x ↦ by simp

/-- Permuting a mask by an adjacent transposition exchanges `strand i` and `strandSucc i`. -/
theorem perm_transposition (i : Fin (k + l - 1)) (S : ShuffleMask k l) :
    S.perm (BraidGroup.transposition i) =
      S.swap (BraidGroup.strand i) (BraidGroup.strandSucc i) := by
  rw [BraidGroup.transposition_eq_swap, perm_swap_eq]

/-- Permuting masks by a fixed `π` is injective. -/
theorem perm_injective (π : Equiv.Perm (Fin (k + l))) :
    Function.Injective (perm π : ShuffleMask k l → ShuffleMask k l) := fun S₁ S₂ h ↦ by
  simpa [← perm_mul] using congrArg (perm π⁻¹) h

/-- **The stabilizer of the initial mask is `S_k × S_l`.** -/
@[simp]
theorem initial_perm_eq_initial_iff {π : Equiv.Perm (Fin (k + l))} :
    (initial : ShuffleMask k l).perm π = initial ↔ π ∈ (Equiv.Perm.finSumPermHom k l).range := by
  rw [← inv_mem_iff, Equiv.Perm.mem_range_finSumPermHom_iff, Subtype.ext_iff, Finset.ext_iff]
  simp

/-- Two permutations send the initial mask to the same mask exactly when they lie in the same left
coset of `S_k × S_l`. -/
theorem initial_perm_eq_initial_perm_iff {π₁ π₂ : Equiv.Perm (Fin (k + l))} :
    (initial : ShuffleMask k l).perm π₁ = initial.perm π₂ ↔
      π₁⁻¹ * π₂ ∈ (Equiv.Perm.finSumPermHom k l).range := by
  rw [← (perm_injective π₁⁻¹).eq_iff, ← perm_mul, ← perm_mul, inv_mul_cancel, perm_one, eq_comm,
    initial_perm_eq_initial_iff]

/-! ### Minimal coset representatives from masks -/

/-- The `(k, l)`-shuffle permutation attached to a mask `S`: the product in
`TauCeti.permCoxeterSystem (k + l)` of the simple reflections along a shuffle path to `S`. It does
not depend on the chosen path (`ShuffleMask.IsShufflePath.wordProd_eq_toPerm`). -/
noncomputable def toPerm (S : ShuffleMask k l) : Equiv.Perm (Fin (k + l)) :=
  (permCoxeterSystem (k + l)).wordProd (exists_isShufflePath S).choose

/-- Every shuffle path to `S` spells `S.toPerm` in `TauCeti.permCoxeterSystem (k + l)`. -/
theorem IsShufflePath.wordProd_eq_toPerm {w : List (Fin (k + l - 1))} {S : ShuffleMask k l}
    (h : IsShufflePath w S) :
    (permCoxeterSystem (k + l)).wordProd w = S.toPerm := by
  rw [toPerm, permCoxeterSystem_wordProd, permCoxeterSystem_wordProd]
  exact h.prod_map_eq (fun i j hij ↦ BraidGroup.transposition_mul_transposition_comm (.inl hij))
    (exists_isShufflePath S).choose_spec

/-- The initial mask corresponds to the identity permutation. -/
@[simp]
theorem toPerm_initial : (initial : ShuffleMask k l).toPerm = 1 := by
  simp [← IsShufflePath.nil.wordProd_eq_toPerm]

/-- Moving a selected position `strand i` past the rest position `strandSucc i` left-multiplies
`toPerm` by `transposition i`. -/
theorem toPerm_swap {i : Fin (k + l - 1)} {S : ShuffleMask k l}
    (ha : BraidGroup.strand i ∈ S.1) (hb : BraidGroup.strandSucc i ∉ S.1) :
    (S.swap (BraidGroup.strand i) (BraidGroup.strandSucc i)).toPerm =
      BraidGroup.transposition i * S.toPerm := by
  obtain ⟨w, hw⟩ := exists_isShufflePath S
  rw [← (hw.cons ha hb).wordProd_eq_toPerm, ← hw.wordProd_eq_toPerm,
    CoxeterSystem.wordProd_cons, permCoxeterSystem_simple]

/-- Applying `S.toPerm` to the initial mask recovers `S`. -/
@[simp]
theorem initial_perm_toPerm (S : ShuffleMask k l) :
    (initial : ShuffleMask k l).perm S.toPerm = S := by
  obtain ⟨w, hw⟩ := exists_isShufflePath S
  rw [← hw.wordProd_eq_toPerm]
  induction hw with
  | nil => simp
  | cons _ _ _ ih =>
    rw [CoxeterSystem.wordProd_cons, permCoxeterSystem_simple, perm_mul, ih, perm_transposition]

/-- A position `x` is selected in `S` exactly when `S.toPerm⁻¹ x` lies in `{0, …, k - 1}`. -/
theorem mem_iff_toPerm_inv_lt {S : ShuffleMask k l} {x : Fin (k + l)} :
    x ∈ S.1 ↔ (S.toPerm⁻¹ x : ℕ) < k := by
  conv_lhs => rw [← S.initial_perm_toPerm]
  rw [mem_perm, mem_initial]

/-- `ShuffleMask.toPerm` is injective. -/
theorem toPerm_injective :
    Function.Injective (toPerm : ShuffleMask k l → Equiv.Perm (Fin (k + l))) := fun S₁ S₂ h ↦ by
  rw [← S₁.initial_perm_toPerm, ← S₂.initial_perm_toPerm, h]

/-- **Every mask's permutation is a minimal coset representative of `S_k × S_l` in `S_(k+l)`.** -/
theorem isMinimalCosetRep_toPerm (S : ShuffleMask k l) :
    (permCoxeterSystem (k + l)).IsMinimalCosetRep (blockParabolicSet k l) S.toPerm := by
  obtain ⟨w, hw⟩ := exists_isShufflePath S
  induction hw with
  | nil =>
    rw [toPerm_initial]
    exact (permCoxeterSystem (k + l)).isMinimalCosetRep_one _
  | @cons _ S i _ ha hb ih =>
    rw [toPerm_swap ha hb, isMinimalCosetRep_blockParabolicSet_iff]
    obtain ⟨h₁, h₂⟩ := isMinimalCosetRep_blockParabolicSet_iff.mp ih
    have ha' : (S.toPerm⁻¹ (BraidGroup.strand i) : ℕ) < k := mem_iff_toPerm_inv_lt.mp ha
    have hb' : ¬ (S.toPerm⁻¹ (BraidGroup.strandSucc i) : ℕ) < k :=
      mt mem_iff_toPerm_inv_lt.mpr hb
    refine ⟨fun p₁ p₂ hp ↦ ?_, fun q₁ q₂ hq ↦ ?_⟩
    · have hlt : (S.toPerm (Fin.castAdd l p₁) : ℕ) < S.toPerm (Fin.castAdd l p₂) :=
        Fin.lt_def.mp (h₁ hp)
      have hn₁ : (S.toPerm (Fin.castAdd l p₁) : ℕ) ≠ (i : ℕ) + 1 := fun h ↦ hb' <| by
        have heq : S.toPerm (Fin.castAdd l p₁) = BraidGroup.strandSucc i := Fin.ext (by simp [h])
        simp [← heq]
      have hn₂ : (S.toPerm (Fin.castAdd l p₂) : ℕ) ≠ (i : ℕ) + 1 := fun h ↦ hb' <| by
        have heq : S.toPerm (Fin.castAdd l p₂) = BraidGroup.strandSucc i := Fin.ext (by simp [h])
        simp [← heq]
      simp only [Fin.lt_def, Equiv.Perm.mul_apply, BraidGroup.val_transposition_apply]
      split_ifs <;> omega
    · have hlt : (S.toPerm (Fin.natAdd k q₁) : ℕ) < S.toPerm (Fin.natAdd k q₂) :=
        Fin.lt_def.mp (h₂ hq)
      have hn₁ : (S.toPerm (Fin.natAdd k q₁) : ℕ) ≠ i := fun h ↦ by
        have heq : S.toPerm (Fin.natAdd k q₁) = BraidGroup.strand i := Fin.ext (by simp [h])
        exact absurd ha' (by simp [← heq])
      have hn₂ : (S.toPerm (Fin.natAdd k q₂) : ℕ) ≠ i := fun h ↦ by
        have heq : S.toPerm (Fin.natAdd k q₂) = BraidGroup.strand i := Fin.ext (by simp [h])
        exact absurd ha' (by simp [← heq])
      simp only [Fin.lt_def, Equiv.Perm.mul_apply, BraidGroup.val_transposition_apply]
      split_ifs <;> omega

/-- **The Coxeter length of `S.toPerm` equals the mask length `S.length`.** -/
@[simp]
theorem length_toPerm (S : ShuffleMask k l) :
    (permCoxeterSystem (k + l)).length (B := Fin (k + l - 1)) S.toPerm = S.length := by
  obtain ⟨w, hw⟩ := exists_isShufflePath S
  induction hw with
  | nil => simp
  | @cons _ S i _ ha hb ih =>
    have ha' : (S.toPerm⁻¹ (BraidGroup.strand i) : ℕ) < k := mem_iff_toPerm_inv_lt.mp ha
    have hb' : ¬ (S.toPerm⁻¹ (BraidGroup.strandSucc i) : ℕ) < k :=
      mt mem_iff_toPerm_inv_lt.mpr hb
    have hnd : ¬ (permCoxeterSystem (k + l)).IsLeftDescent S.toPerm i := by
      rw [isLeftDescent_permCoxeterSystem_iff, Fin.lt_def]
      omega
    rw [toPerm_swap ha hb, ← permCoxeterSystem_simple,
      (permCoxeterSystem (k + l)).not_isLeftDescent_iff.mp hnd, ih,
      length_swap_of_mem_of_notMem (by simp) ha hb]

/-- **Every shuffle path is a reduced word in `TauCeti.permCoxeterSystem (k + l)`.** -/
theorem IsShufflePath.isReduced {w : List (Fin (k + l - 1))} {S : ShuffleMask k l}
    (h : IsShufflePath w S) :
    (permCoxeterSystem (k + l)).IsReduced w := by
  rw [CoxeterSystem.IsReduced, h.wordProd_eq_toPerm, S.length_toPerm, h.length_eq]

/-- **The sign of `S.toPerm` is `(-1) ^ S.length`.** -/
@[simp]
theorem sign_toPerm (S : ShuffleMask k l) :
    Equiv.Perm.sign S.toPerm = (-1 : ℤˣ) ^ S.length := by
  rw [← lengthPowHom_neg_one_permCoxeterSystem (k + l), CoxeterSystem.lengthPowHom_apply,
    S.length_toPerm]

/-- **The minimal coset representative of `π` is `(initial.perm π).toPerm`.** -/
theorem toPerm_initial_perm (π : Equiv.Perm (Fin (k + l))) :
    ((initial : ShuffleMask k l).perm π).toPerm =
      (permCoxeterSystem (k + l)).minimalCosetRep (blockParabolicSet k l) π := by
  rw [(permCoxeterSystem (k + l)).eq_minimalCosetRep_iff]
  refine ⟨isMinimalCosetRep_toPerm _, ?_⟩
  rw [permCoxeterSystem_parabolic_blockParabolicSet, ← initial_perm_eq_initial_perm_iff,
    initial_perm_toPerm]

/-- **Masks biject with minimal left coset representatives of `S_k × S_l` in `S_(k+l)`.** -/
noncomputable def minimalCosetRepEquiv (k l : ℕ) :
    ShuffleMask k l ≃
      {d : Equiv.Perm (Fin (k + l)) //
        (permCoxeterSystem (k + l)).IsMinimalCosetRep (blockParabolicSet k l) d} where
  toFun S := ⟨S.toPerm, S.isMinimalCosetRep_toPerm⟩
  invFun d := initial.perm d.1
  left_inv S := S.initial_perm_toPerm
  right_inv d := Subtype.ext <|
    (toPerm_initial_perm d.1).trans (d.2.minimalCosetRep_eq (permCoxeterSystem (k + l)))

/-- `ShuffleMask.minimalCosetRepEquiv` sends a mask `S` to `S.toPerm`. -/
@[simp]
theorem coe_minimalCosetRepEquiv_apply (S : ShuffleMask k l) :
    (minimalCosetRepEquiv k l S : Equiv.Perm (Fin (k + l))) = S.toPerm :=
  (rfl)

/-- The inverse of `ShuffleMask.minimalCosetRepEquiv` sends a minimal coset representative `d` to
`initial.perm d`. -/
@[simp]
theorem minimalCosetRepEquiv_symm_apply
    (d : {d : Equiv.Perm (Fin (k + l)) //
      (permCoxeterSystem (k + l)).IsMinimalCosetRep (blockParabolicSet k l) d}) :
    (minimalCosetRepEquiv k l).symm d = initial.perm d.1 :=
  (rfl)

end ShuffleMask

/-! ### The PBW coset isomorphism and coset basis of `Sh_k(U)` -/

section CosetBasis

variable {R : Type*} [CommRing R] {q : Rˣ} {k l : ℕ}
variable {U : Type*} [AddCommGroup U] [Module R U]

/-- Along any shuffle path to `S`, the product of the Hecke generators `T i` equals
`Tw q (permCoxeterSystem (k + l)) S.toPerm`. -/
theorem ShuffleMask.IsShufflePath.prod_map_T_eq_Tw_toPerm {w : List (Fin (k + l - 1))}
    {S : ShuffleMask k l} (h : ShuffleMask.IsShufflePath w S) :
    (w.map (T (R := R) q)).prod = Tw q (permCoxeterSystem (k + l)) S.toPerm := by
  rw [← h.wordProd_eq_toPerm, Tw_wordProd (permCoxeterSystem (k + l)) h.isReduced]

/-- **Leading coefficient of `T_(S.toPerm)` on the initial mask**: `T_(S.toPerm)` sends `u` at the
initial mask to a function whose value at `S` is `(-1) ^ S.length • u`. -/
theorem shuffleRep_Tw_toPerm_single_initial_apply_self
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) (S : ShuffleMask k l) (u : U) :
    shuffleRep k ρ (Tw q (permCoxeterSystem (k + l)) S.toPerm)
        (Pi.single ShuffleMask.initial u) S =
      (-1 : R) ^ S.length • u := by
  obtain ⟨w, hw⟩ := ShuffleMask.exists_isShufflePath S
  rw [← hw.prod_map_T_eq_Tw_toPerm, hw.shuffleRep_prod_T_single_initial_apply_self]

/-- **Lower terms of `T_(S.toPerm)` on the initial mask**: `T_(S.toPerm)` sends `u` at the initial
mask to a function vanishing at every mask `M ≠ S` with `S.length ≤ M.length`. -/
theorem shuffleRep_Tw_toPerm_single_initial_apply_of_length_le
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) (S : ShuffleMask k l) (u : U)
    {M : ShuffleMask k l} (hM : S.length ≤ M.length) (hne : M ≠ S) :
    shuffleRep k ρ (Tw q (permCoxeterSystem (k + l)) S.toPerm)
        (Pi.single ShuffleMask.initial u) M = 0 := by
  obtain ⟨w, hw⟩ := ShuffleMask.exists_isShufflePath S
  rw [← hw.prod_map_T_eq_Tw_toPerm,
    hw.shuffleRep_prod_T_single_initial_apply_of_length_le ρ u hM hne]

variable (R k l U) in
/-- The **mask-length sign gauge** on `Sh_k(U)`: the involutive `R`-linear equivalence multiplying
the value at each mask `S` by `(-1) ^ S.length`. -/
def shuffleSignEquiv : (ShuffleMask k l → U) ≃ₗ[R] (ShuffleMask k l → U) :=
  LinearEquiv.ofInvolutive
    { toFun f S := (-1 : R) ^ S.length • f S
      map_add' f g := funext fun S ↦ smul_add _ (f S) (g S)
      map_smul' c f := funext fun S ↦ smul_comm ((-1 : R) ^ S.length) c (f S) }
    fun f ↦ funext fun S ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, smul_smul, ← mul_pow, neg_one_mul, neg_neg,
        one_pow, one_smul]

/-- `TauCeti.TypeAHeckeAlgebra.shuffleSignEquiv` multiplies the value at `S` by
`(-1) ^ S.length`. -/
@[simp]
theorem shuffleSignEquiv_apply (f : ShuffleMask k l → U) (S : ShuffleMask k l) :
    shuffleSignEquiv R k l U f S = (-1 : R) ^ S.length • f S :=
  (rfl)

/-- `TauCeti.TypeAHeckeAlgebra.shuffleSignEquiv` is equal to its own inverse. -/
@[simp]
theorem shuffleSignEquiv_symm :
    (shuffleSignEquiv R k l U).symm = shuffleSignEquiv R k l U :=
  LinearEquiv.ext fun _ ↦ rfl

/-- Applying `TauCeti.TypeAHeckeAlgebra.shuffleSignEquiv` twice is the identity. -/
@[simp]
theorem shuffleSignEquiv_shuffleSignEquiv (f : ShuffleMask k l → U) :
    shuffleSignEquiv R k l U (shuffleSignEquiv R k l U f) = f :=
  (shuffleSignEquiv R k l U).symm_apply_apply f

/-- `TauCeti.TypeAHeckeAlgebra.shuffleSignEquiv` scales `Pi.single S u` by `(-1) ^ S.length`. -/
@[simp]
theorem shuffleSignEquiv_single (S : ShuffleMask k l) (u : U) :
    shuffleSignEquiv R k l U (Pi.single S u) = (-1 : R) ^ S.length • Pi.single S u := by
  ext M
  by_cases hM : M = S
  · subst hM
    simp
  · simp [Pi.single_eq_of_ne hM]

/-- `TauCeti.TypeAHeckeAlgebra.shuffleSignEquiv` fixes vectors supported on the initial mask. -/
theorem shuffleSignEquiv_single_initial (u : U) :
    shuffleSignEquiv R k l U (Pi.single ShuffleMask.initial u) =
      Pi.single ShuffleMask.initial u := by
  simp

private noncomputable def shuffleCosetMap
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) :
    (ShuffleMask k l → U) →ₗ[R] (ShuffleMask k l → U) :=
  LinearMap.lsum R (fun _ : ShuffleMask k l ↦ U) R fun S ↦
    shuffleRep k ρ (Tw q (permCoxeterSystem (k + l)) S.toPerm) ∘ₗ
      LinearMap.single R (fun _ : ShuffleMask k l ↦ U) ShuffleMask.initial

private theorem shuffleCosetMap_apply
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) (f : ShuffleMask k l → U) :
    shuffleCosetMap ρ f =
      ∑ S : ShuffleMask k l,
        shuffleRep k ρ (Tw q (permCoxeterSystem (k + l)) S.toPerm)
          (Pi.single ShuffleMask.initial (f S)) := by
  conv_lhs => rw [← Finset.univ_sum_single f]
  rw [map_sum]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [shuffleCosetMap, LinearMap.lsum_piSingle, LinearMap.comp_apply, LinearMap.single_apply]

variable (k) in
/-- **The PBW coset isomorphism of the shuffle module.** Over every commutative ring `R`, unit
`q : Rˣ`, and `H_l`-module `U`, the `R`-linear map sending `f : ShuffleMask k l → U` to
`∑ S, T_(S.toPerm) • Pi.single initial (f S)` is an isomorphism of `R`-modules. -/
noncomputable def shuffleCosetEquiv
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) :
    (ShuffleMask k l → U) ≃ₗ[R] (ShuffleMask k l → U) :=
  let D : Module.End R (ShuffleMask k l → U) := (shuffleSignEquiv R k l U).toLinearMap
  let N : Module.End R (ShuffleMask k l → U) := 1 - shuffleCosetMap ρ * D
  let C : Module.End R (ShuffleMask k l → U) := ∑ m ∈ Finset.range (k * l + 1), N ^ m
  have hBC_CB : (shuffleCosetMap ρ * D) * C = 1 ∧ C * (shuffleCosetMap ρ * D) = 1 := by
    have hN_apply (g : ShuffleMask k l → U) (M : ShuffleMask k l) :
        N g M = -∑ S ∈ Finset.univ.erase M,
          (-1 : R) ^ S.length • shuffleRep k ρ (Tw q (permCoxeterSystem (k + l)) S.toPerm)
            (Pi.single ShuffleMask.initial (g S)) M := by
      simp only [N, LinearMap.sub_apply, Pi.sub_apply, one_apply_eq_self, mul_apply_eq_comp,
        shuffleCosetMap_apply, Finset.sum_apply, D, LinearEquiv.coe_coe, shuffleSignEquiv_apply,
        Pi.single_smul, map_smul, Pi.smul_apply]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ M),
        shuffleRep_Tw_toPerm_single_initial_apply_self, smul_smul, ← mul_pow, neg_one_mul, neg_neg,
        one_pow, one_smul, sub_add_eq_sub_sub, sub_self, zero_sub]
    have hpow : ∀ (m : ℕ) (f : ShuffleMask k l → U) (M : ShuffleMask k l),
        k * l < M.length + m → (N ^ m) f M = 0 := by
      intro m
      induction m with
      | zero =>
        intro f M hM
        have := M.length_le_mul
        omega
      | succ m ih =>
        intro f M hM
        rw [pow_succ', mul_apply_eq_comp, hN_apply, neg_eq_zero]
        refine Finset.sum_eq_zero fun S hS ↦ ?_
        have hne : M ≠ S := (Finset.mem_erase.mp hS).1.symm
        rcases le_or_gt S.length M.length with hle | hgt
        · rw [shuffleRep_Tw_toPerm_single_initial_apply_of_length_le ρ S _ hle hne, smul_zero]
        · rw [ih f S (by omega), Pi.single_zero, map_zero, Pi.zero_apply, smul_zero]
    have hnil : N ^ (k * l + 1) = 0 :=
      LinearMap.ext fun f ↦ funext fun M ↦ hpow (k * l + 1) f M (by omega)
    have hB : shuffleCosetMap ρ * D = 1 - N := (sub_sub_cancel 1 _).symm
    exact ⟨by rw [hB, mul_neg_geom_sum, hnil, sub_zero],
      by rw [hB, geom_sum_mul_neg, hnil, sub_zero]⟩
  LinearEquiv.ofLinearMap (shuffleCosetMap ρ) (D * C)
    ((mul_assoc (shuffleCosetMap ρ) D C).symm.trans hBC_CB.1)
    (by
      have hD : D * D = 1 := LinearMap.ext (shuffleSignEquiv_shuffleSignEquiv (R := R))
      exact calc (D * C) * shuffleCosetMap ρ
          = (D * C) * (shuffleCosetMap ρ * (D * D)) := by rw [hD, mul_one]
        _ = D * (C * (shuffleCosetMap ρ * D)) * D := by simp only [mul_assoc]
        _ = D * D := by rw [hBC_CB.2, mul_one]
        _ = 1 := hD)

/-- `TauCeti.TypeAHeckeAlgebra.shuffleCosetEquiv` expands `f` as
`∑ S, T_(S.toPerm) • Pi.single initial (f S)`. -/
theorem shuffleCosetEquiv_apply
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) (f : ShuffleMask k l → U) :
    shuffleCosetEquiv k ρ f =
      ∑ S : ShuffleMask k l,
        shuffleRep k ρ (Tw q (permCoxeterSystem (k + l)) S.toPerm)
          (Pi.single ShuffleMask.initial (f S)) :=
  shuffleCosetMap_apply ρ f

/-- `TauCeti.TypeAHeckeAlgebra.shuffleCosetEquiv` sends `Pi.single S u` to
`T_(S.toPerm) • Pi.single initial u`. -/
@[simp]
theorem shuffleCosetEquiv_single
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) (S : ShuffleMask k l) (u : U) :
    shuffleCosetEquiv k ρ (Pi.single S u) =
      shuffleRep k ρ (Tw q (permCoxeterSystem (k + l)) S.toPerm)
        (Pi.single ShuffleMask.initial u) := by
  rw [shuffleCosetEquiv, LinearEquiv.coe_ofLinearMap, shuffleCosetMap, LinearMap.lsum_piSingle,
    LinearMap.comp_apply, LinearMap.single_apply]

variable (k) in
/-- **The PBW coset basis of `Sh_k(U)`** associated to a basis `b` of `U`: the vectors
`T_(S.toPerm) • Pi.single initial (b i)` for `(S, i) : ShuffleMask k l × ι` form an `R`-basis of
`Sh_k(U)`. -/
noncomputable def shuffleCosetBasis {ι : Type*}
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) (b : Module.Basis ι R U) :
    Module.Basis (ShuffleMask k l × ι) R (ShuffleMask k l → U) :=
  ((Pi.basis fun _ : ShuffleMask k l ↦ b).reindex
    (Equiv.sigmaEquivProd (ShuffleMask k l) ι)).map (shuffleCosetEquiv k ρ)

/-- At `(S, i)`, `TauCeti.TypeAHeckeAlgebra.shuffleCosetBasis` is
`T_(S.toPerm) • Pi.single initial (b i)`. -/
@[simp]
theorem shuffleCosetBasis_apply {ι : Type*}
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) (b : Module.Basis ι R U)
    (p : ShuffleMask k l × ι) :
    shuffleCosetBasis k ρ b p =
      shuffleRep k ρ (Tw q (permCoxeterSystem (k + l)) p.1.toPerm)
        (Pi.single ShuffleMask.initial (b p.2)) := by
  simp [shuffleCosetBasis]

end CosetBasis

/-! ### The unsigned shuffle module -/

section UnsignedShuffle

variable {R : Type*} [CommRing R] {q : Rˣ} {k l : ℕ}
variable {U : Type*} [AddCommGroup U] [Module R U]

variable (k) in
/-- **The unsigned shuffle module**: `TauCeti.TypeAHeckeAlgebra.shuffleRep k ρ` conjugated by the
mask-length sign gauge `TauCeti.TypeAHeckeAlgebra.shuffleSignEquiv`. Adjacent masks differ in
length by `1`, so conjugating by `(-1) ^ S.length` flips the off-diagonal signs `-1` of
`shuffleRep` to `+1`, turning the mixed block `[[q - q⁻¹, -1], [-1, 0]]` into
`[[q - q⁻¹, 1], [1, 0]]`. -/
noncomputable def unsignedShuffleRep
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) :
    TypeAHeckeAlgebra R q (k + l) →ₐ[R] Module.End R (ShuffleMask k l → U) :=
  (shuffleSignEquiv R k l U).conjAlgEquiv R |>.toAlgHom.comp (shuffleRep k ρ)

/-- `TauCeti.TypeAHeckeAlgebra.unsignedShuffleRep` conjugates `shuffleRep` by
`shuffleSignEquiv`. -/
theorem unsignedShuffleRep_apply
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U)
    (x : TypeAHeckeAlgebra R q (k + l)) :
    unsignedShuffleRep k ρ x =
      (shuffleSignEquiv R k l U).toLinearMap ∘ₗ shuffleRep k ρ x ∘ₗ
        (shuffleSignEquiv R k l U).toLinearMap := by
  refine LinearMap.ext fun f ↦ funext fun S ↦ ?_
  simp [unsignedShuffleRep, LinearEquiv.conjAlgEquiv_apply]

/-- `TauCeti.TypeAHeckeAlgebra.shuffleSignEquiv` intertwines `shuffleRep` and
`unsignedShuffleRep`. -/
theorem shuffleSignEquiv_comp_shuffleRep
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U)
    (x : TypeAHeckeAlgebra R q (k + l)) :
    (shuffleSignEquiv R k l U).toLinearMap ∘ₗ shuffleRep k ρ x =
      unsignedShuffleRep k ρ x ∘ₗ (shuffleSignEquiv R k l U).toLinearMap := by
  refine LinearMap.ext fun f ↦ funext fun S ↦ ?_
  rw [unsignedShuffleRep_apply]
  simp

/-- When both `i` and `i + 1` are selected in `S`, `T q i` acts by `q` at `S` in
`unsignedShuffleRep`. -/
@[simp]
theorem unsignedShuffleRep_T_apply_of_mem_of_mem
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) {i : Fin (k + l - 1)}
    {S : ShuffleMask k l} (ha : BraidGroup.strand i ∈ S.1) (hb : BraidGroup.strandSucc i ∈ S.1)
    (f : ShuffleMask k l → U) :
    unsignedShuffleRep k ρ (T q i) f S = (q : R) • f S := by
  rw [unsignedShuffleRep_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, shuffleSignEquiv_apply, shuffleRep_T_apply_of_mem_of_mem ρ ha hb,
    shuffleSignEquiv_apply, smul_comm, smul_smul ((-1 : R) ^ S.length), ← mul_pow,
    neg_one_mul, neg_neg, one_pow, one_smul]

/-- When `i` is selected and `i + 1` is not, `T q i` acts at `S` in `unsignedShuffleRep` by
`(q - q⁻¹) • f S + f (S.swap i (i + 1))`, with a `+` sign on the exchange term. -/
@[simp]
theorem unsignedShuffleRep_T_apply_of_mem_of_notMem
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) {i : Fin (k + l - 1)}
    {S : ShuffleMask k l} (ha : BraidGroup.strand i ∈ S.1) (hb : BraidGroup.strandSucc i ∉ S.1)
    (f : ShuffleMask k l → U) :
    unsignedShuffleRep k ρ (T q i) f S =
      ((q : R) - ↑q⁻¹) • f S + f (S.swap (BraidGroup.strand i) (BraidGroup.strandSucc i)) := by
  have hlen := ShuffleMask.length_swap_of_mem_of_notMem (by simp) ha hb
  rw [unsignedShuffleRep_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, shuffleSignEquiv_apply, shuffleRep_T_apply_of_mem_of_notMem ρ ha hb,
    shuffleSignEquiv_apply, shuffleSignEquiv_apply, hlen, pow_succ,
    mul_neg_one, neg_smul, sub_neg_eq_add, smul_add, smul_comm ((-1 : R) ^ S.length),
    smul_smul ((-1 : R) ^ S.length), smul_smul ((-1 : R) ^ S.length), ← mul_pow, neg_one_mul,
    neg_neg, one_pow, one_smul, one_smul]

/-- When `i` is not selected and `i + 1` is selected, `T q i` acts at `S` in `unsignedShuffleRep`
by `f (S.swap i (i + 1))`, with no `-` sign. -/
@[simp]
theorem unsignedShuffleRep_T_apply_of_notMem_of_mem
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) {i : Fin (k + l - 1)}
    {S : ShuffleMask k l} (ha : BraidGroup.strand i ∉ S.1) (hb : BraidGroup.strandSucc i ∈ S.1)
    (f : ShuffleMask k l → U) :
    unsignedShuffleRep k ρ (T q i) f S =
      f (S.swap (BraidGroup.strand i) (BraidGroup.strandSucc i)) := by
  have hlen := ShuffleMask.length_swap_add_one_of_notMem_of_mem (by simp) ha hb
  rw [unsignedShuffleRep_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, shuffleSignEquiv_apply, shuffleRep_T_apply_of_notMem_of_mem ρ ha hb,
    shuffleSignEquiv_apply, ← hlen, pow_succ, mul_neg_one, neg_smul,
    smul_neg, neg_neg, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

/-- When neither `i` nor `i + 1` is selected in `S`, `T q i` acts at `S` in `unsignedShuffleRep`
by the compressed `H_l`-generator `T q (S.restIndex i)`. -/
@[simp]
theorem unsignedShuffleRep_T_apply_of_notMem_of_notMem
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) {i : Fin (k + l - 1)}
    {S : ShuffleMask k l} (ha : BraidGroup.strand i ∉ S.1) (hb : BraidGroup.strandSucc i ∉ S.1)
    (f : ShuffleMask k l → U) :
    unsignedShuffleRep k ρ (T q i) f S =
      ρ (T q ⟨S.restIndex (BraidGroup.strand i),
        ShuffleMask.restIndex_lt_sub_one (by simp [Fin.lt_def]) ha hb⟩) (f S) := by
  rw [unsignedShuffleRep_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, shuffleSignEquiv_apply, shuffleRep_T_apply_of_notMem_of_notMem ρ ha hb,
    shuffleSignEquiv_apply, map_smul, smul_smul, ← mul_pow, neg_one_mul,
    neg_neg, one_pow, one_smul]

/-- **Sign-free monomial action of inverse shuffle words**: in `unsignedShuffleRep`, the inverse
shuffle word of `S` sends `Pi.single initial u` directly to `Pi.single S u`, with no `(-1)` sign. -/
theorem unsignedShuffleRep_shuffleInvWord_single_initial
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) (S : ShuffleMask k l) (u : U) :
    unsignedShuffleRep k ρ (shuffleInvWord q S) (Pi.single ShuffleMask.initial u) =
      Pi.single S u := by
  rw [unsignedShuffleRep_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, shuffleSignEquiv_single_initial, shuffleRep_shuffleInvWord_single_initial,
    map_smul, shuffleSignEquiv_single, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow,
    one_smul]

/-- **Sign-free leading coefficient of `T_(S.toPerm)`**: in `unsignedShuffleRep`, `T_(S.toPerm)`
sends `Pi.single initial u` to a function with value `u` at `S`. -/
theorem unsignedShuffleRep_Tw_toPerm_single_initial_apply_self
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) (S : ShuffleMask k l) (u : U) :
    unsignedShuffleRep k ρ (Tw q (permCoxeterSystem (k + l)) S.toPerm)
        (Pi.single ShuffleMask.initial u) S = u := by
  rw [unsignedShuffleRep_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, shuffleSignEquiv_single_initial,
    shuffleSignEquiv_apply, shuffleRep_Tw_toPerm_single_initial_apply_self, smul_smul,
    ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

end UnsignedShuffle

end TauCeti.TypeAHeckeAlgebra

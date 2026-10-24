/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Finite
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Last-strand coset words in the finite Hecke algebra

The descending words `T_(n-1) ⋯ T_i`, together with the empty word, span the Hecke
algebra on `n + 1` strands as a left module over the image of the algebra on `n`
strands. This is the spanning part of the parabolic coset basis theorem; it does
not assume that the tower map is injective or that the words are independent.

The words are defined recursively through the tower maps, so their indexing
includes the zero- and one-strand cases without special choices of generators.
The resulting finite coset expansions imply finite generation over the
coefficient ring for every unit parameter.

## References

* M. Geck and G. Pfeiffer, *Characters of Finite Coxeter Groups and Iwahori–Hecke
  Algebras*, Chapter 4, for parabolic coset bases of Hecke algebras.
-/

public section

namespace TauCeti.TypeAHeckeAlgebra

variable {R : Type*} [CommRing R] (q : Rˣ)

/-- The descending last-strand word `T_(n-1) ⋯ T_i` in the algebra on `n + 1`
strands, with the empty word at `i = n`. Generator indices start at zero. -/
def cosetWord : (n : ℕ) → Fin (n + 1) → TypeAHeckeAlgebra R q (n + 1)
  | 0, _ => 1
  | n + 1, i =>
    if h : i.val < n + 1 then
      T q (Fin.last n) * strandIncl R q (n + 1) (cosetWord n ⟨i.val, h⟩)
    else 1

/-- With no generators the only coset word is empty. -/
@[simp]
theorem cosetWord_zero (i : Fin 1) : cosetWord q 0 i = 1 := (rfl)

/-- The last coset word is empty. -/
@[simp]
theorem cosetWord_last (n : ℕ) : cosetWord q n (Fin.last n) = 1 := by
  cases n <;> simp [cosetWord]

/-- A nonempty coset word starts with the last generator. -/
@[simp]
theorem cosetWord_castSucc (n : ℕ) (i : Fin (n + 1)) :
    cosetWord q (n + 1) i.castSucc =
      T q (Fin.last n) * strandIncl R q (n + 1) (cosetWord q n i) := by
  simp [cosetWord, i.isLt]

variable {q}

private theorem commute_last_doubleIncl (n : ℕ) (x : TypeAHeckeAlgebra R q (n + 1)) :
    Commute (T q (Fin.last (n + 1)))
      (strandIncl R q (n + 2) (strandIncl R q (n + 1) x)) := by
  have hx : x ∈ Algebra.adjoin R (Set.range (T (n := n + 1) q)) := by
    rw [adjoin_range_T]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simp only [strandIncl_T]
    exact commute_T (Or.inr (by have := i.isLt; dsimp; omega))
  | algebraMap r => simp only [AlgHom.commutes]; exact Algebra.commute_algebraMap_right r _
  | add x y _ _ hx hy => simpa only [map_add] using hx.add_right hy
  | mul x y _ _ hx hy => simpa only [map_mul] using hx.mul_right hy

private def cosetSpan (n : ℕ) : Submodule R (TypeAHeckeAlgebra R q (n + 1)) :=
  Submodule.span R (Set.range fun p : TypeAHeckeAlgebra R q n × Fin (n + 1) ↦
    strandIncl R q n p.1 * cosetWord q n p.2)

private theorem incl_mul_word_mem (n : ℕ) (x : TypeAHeckeAlgebra R q n) (i : Fin (n + 1)) :
    strandIncl R q n x * cosetWord q n i ∈ cosetSpan (q := q) n :=
  Submodule.subset_span ⟨(x, i), rfl⟩

private theorem incl_mul_mem (n : ℕ) (x : TypeAHeckeAlgebra R q n)
    {y : TypeAHeckeAlgebra R q (n + 1)} (hy : y ∈ cosetSpan (q := q) n) :
    strandIncl R q n x * y ∈ cosetSpan (q := q) n := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨a, i⟩, rfl⟩ := hy
    simpa only [map_mul, mul_assoc] using incl_mul_word_mem n (x * a) i
  | zero => simp
  | add y z _ _ hy hz => simpa only [mul_add] using add_mem hy hz
  | smul r y _ hy => simpa only [mul_smul_comm] using Submodule.smul_mem _ r hy

private theorem incl_mem (n : ℕ) (x : TypeAHeckeAlgebra R q n) :
    strandIncl R q n x ∈ cosetSpan (q := q) n := by
  simpa only [cosetWord_last, mul_one] using incl_mul_word_mem n x (Fin.last n)

private theorem word_mem (n : ℕ) (i : Fin (n + 1)) :
    cosetWord q n i ∈ cosetSpan (q := q) n := by
  simpa only [map_one, one_mul] using incl_mul_word_mem n 1 i

private theorem word_mul_last (n : ℕ) (i : Fin (n + 1)) :
    cosetWord q (n + 2) i.castSucc.castSucc * T q (Fin.last (n + 1)) =
      strandIncl R q (n + 2) (T q (Fin.last n)) *
        cosetWord q (n + 2) i.castSucc.castSucc := by
  -- Commute the last generator through the earlier tail, then use one braid relation.
  have hc := (commute_last_doubleIncl n (cosetWord q n i)).eq
  have hb := T_braid (q := q) (n := n + 3)
    (i := (Fin.last n).castSucc) (j := Fin.last (n + 1)) (Or.inl (by simp))
  have hi : strandIncl R q (n + 2) (T q (Fin.last n)) =
      T q (Fin.last n).castSucc := by
    simp only [strandIncl_T]
    congr 1
  simp only [cosetWord_castSucc, map_mul, hi]
  calc
    _ = T q (Fin.last (n + 1)) * T q (Fin.last n).castSucc *
        T q (Fin.last (n + 1)) *
          strandIncl R q (n + 2) (strandIncl R q (n + 1) (cosetWord q n i)) := by
      simp only [mul_assoc]
      rw [← hc]
    _ = _ := by rw [← hb]; simp only [mul_assoc]

private theorem word_mul_last_mem (n : ℕ) (i : Fin (n + 2)) :
    cosetWord q (n + 1) i * T q (Fin.last n) ∈ cosetSpan (q := q) (n + 1) := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa only [cosetWord_last, one_mul, cosetWord_castSucc, cosetWord_last, map_one,
      mul_one] using word_mem (n + 1) (Fin.last n).castSucc
  · have hsquare : cosetWord q (n + 1) (Fin.last n).castSucc * T q (Fin.last n) ∈
        cosetSpan (q := q) (n + 1) := by
      simp only [cosetWord_castSucc, cosetWord_last, map_one, mul_one, T_mul_self]
      exact add_mem (Submodule.smul_mem _ _ <| by
        simpa only [cosetWord_castSucc, cosetWord_last, map_one, mul_one] using
          word_mem (q := q) (n + 1) (Fin.last n).castSucc)
        (by simpa only [map_one] using incl_mem (q := q) (n + 1) 1)
    cases n with
    | zero =>
      have hj : j = Fin.last 0 := Fin.ext (by omega)
      simpa only [hj] using hsquare
    | succ n =>
      refine Fin.lastCases hsquare (fun k ↦ ?_) j
      rw [word_mul_last]
      exact incl_mul_mem _ _ (word_mem _ _)

private theorem last_mul_incl_mem (n : ℕ)
    (ih : cosetSpan (q := q) n = ⊤) (x : TypeAHeckeAlgebra R q (n + 1)) :
    T q (Fin.last n) * strandIncl R q (n + 1) x ∈ cosetSpan (q := q) (n + 1) := by
  -- Expand in the preceding stage; its coefficients commute with the new generator.
  have hx : x ∈ cosetSpan (q := q) n := by rw [ih]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, i⟩, rfl⟩ := hx
    cases n with
    | zero =>
      obtain ⟨r, rfl⟩ := algebraMap_surjective_of_le_one (q := q) (by omega) a
      simp only [AlgHom.commutes, cosetWord, mul_one]
      rw [← Algebra.commutes, ← Algebra.smul_def]
      exact Submodule.smul_mem _ r <| by
        simpa only [cosetWord_castSucc, cosetWord_last, map_one, mul_one] using
          word_mem (q := q) 1 (Fin.last 0).castSucc
    | succ n =>
      rw [map_mul, ← mul_assoc, (commute_last_doubleIncl n a).eq, mul_assoc,
        ← cosetWord_castSucc]
      exact incl_mul_mem _ _ (word_mem _ _)
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add, mul_add] using add_mem hx hy
  | smul r x _ hx =>
    simpa only [map_smul, mul_smul_comm] using Submodule.smul_mem _ r hx

private theorem word_mul_T_mem (n : ℕ) (ih : cosetSpan (q := q) n = ⊤)
    (i : Fin (n + 2)) (j : Fin (n + 1)) :
    cosetWord q (n + 1) i * T q j ∈ cosetSpan (q := q) (n + 1) := by
  refine Fin.lastCases (word_mul_last_mem n i) (fun k ↦ ?_) j
  have hi : T q k.castSucc = strandIncl R q (n + 1) (T q k) := by
    simp only [strandIncl_T]
    congr 1
  rw [hi]
  refine Fin.lastCases ?_ (fun l ↦ ?_) i
  · simpa only [cosetWord_last, one_mul] using incl_mem (n + 1) (T q k)
  · rw [cosetWord_castSucc, mul_assoc, ← map_mul]
    exact last_mul_incl_mem n ih _

private theorem cosetSpan_eq_top (n : ℕ) : cosetSpan (q := q) n = ⊤ := by
  induction n with
  | zero =>
    apply top_unique
    intro x hx
    clear hx
    obtain ⟨r, rfl⟩ := algebraMap_surjective_of_le_one (q := q) (by omega) x
    simpa only [AlgHom.commutes] using incl_mem (q := q) 0 (algebraMap R _ r)
  | succ n ih =>
    have hmul (j : Fin (n + 1)) {x : TypeAHeckeAlgebra R q (n + 2)}
        (hx : x ∈ cosetSpan (q := q) (n + 1)) :
        x * T q j ∈ cosetSpan (q := q) (n + 1) := by
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨⟨a, i⟩, rfl⟩ := hx
        rw [mul_assoc]
        exact incl_mul_mem _ _ (word_mul_T_mem n ih i j)
      | zero => simp
      | add x y _ _ hx hy => simpa only [add_mul] using add_mem hx hy
      | smul r x _ hx => simpa only [smul_mul_assoc] using Submodule.smul_mem _ r hx
    apply top_unique
    intro x hx
    clear hx
    have hx : x ∈ Algebra.adjoin R (Set.range (T (n := n + 2) q)) := by
      rw [adjoin_range_T]
      trivial
    suffices h : ∀ y ∈ cosetSpan (q := q) (n + 1),
        y * x ∈ cosetSpan (q := q) (n + 1) by
      simpa only [one_mul] using h 1 (by simpa only [map_one] using incl_mem (q := q) (n + 1) 1)
    induction hx using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact fun y hy ↦ hmul j hy
    | algebraMap r =>
      intro y hy
      rw [← Algebra.commutes, ← Algebra.smul_def]
      exact Submodule.smul_mem _ r hy
    | add x z _ _ hx hz =>
      intro y hy
      simpa only [mul_add] using add_mem (hx y hy) (hz y hy)
    | mul x z _ _ hx hz =>
      intro y hy
      rw [← mul_assoc]
      exact hz _ (hx y hy)

/-- The last-strand coset words span the finite Hecke algebra as a left module over
the image of the preceding stage. No injectivity of the tower map is assumed. -/
theorem span_strandIncl_mul_cosetWord (n : ℕ) :
    Submodule.span R (Set.range fun p : TypeAHeckeAlgebra R q n × Fin (n + 1) ↦
      strandIncl R q n p.1 * cosetWord q n p.2) = ⊤ :=
  cosetSpan_eq_top n

variable (q)

/-- Every element has a last-strand coset expansion with `n + 1` coefficients in
the preceding Hecke algebra. The coefficients are not yet asserted unique. -/
theorem exists_sum_strandIncl_mul_cosetWord (n : ℕ) (x : TypeAHeckeAlgebra R q (n + 1)) :
    ∃ a : Fin (n + 1) → TypeAHeckeAlgebra R q n,
      x = ∑ i, strandIncl R q n (a i) * cosetWord q n i := by
  classical
  have hx : x ∈ Submodule.span R (Set.range fun p : TypeAHeckeAlgebra R q n × Fin (n + 1) ↦
      strandIncl R q n p.1 * cosetWord q n p.2) := by
    rw [span_strandIncl_mul_cosetWord]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, i⟩, rfl⟩ := hx
    exact ⟨fun j ↦ if j = i then a else 0, by simp [apply_ite]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, by simp [add_mul, Finset.sum_add_distrib]⟩
  | smul r x _ hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨r • a, by simp [Finset.smul_sum]⟩

/-- The finite Hecke algebra is finitely generated over its coefficient ring,
without any restriction on the unit parameter or on the characteristic. -/
instance (n : ℕ) : Module.Finite R (TypeAHeckeAlgebra R q n) := by
  induction n with
  | zero =>
    exact Module.Finite.of_surjective (Algebra.linearMap R _)
      (algebraMap_surjective_of_le_one (by omega))
  | succ n ih =>
    have := ih
    let f : (Fin (n + 1) → TypeAHeckeAlgebra R q n) →ₗ[R]
        TypeAHeckeAlgebra R q (n + 1) :=
      { toFun := fun a ↦ ∑ i, strandIncl R q n (a i) * cosetWord q n i
        map_add' := by intros; simp [add_mul, Finset.sum_add_distrib]
        map_smul' := by intros; simp [Finset.smul_sum] }
    exact Module.Finite.of_surjective f fun x ↦
      (exists_sum_strandIncl_mul_cosetWord q n x).imp fun _ h ↦ h.symm

end TauCeti.TypeAHeckeAlgebra

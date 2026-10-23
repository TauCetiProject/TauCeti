/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
import TauCeti.GroupTheory.Perm.Inversion

/-!
# Exchanging two blocks of arguments of an alternating map

An alternating map `f` in `a + b + (c + d)` arguments is evaluated on the concatenation
`(x, y, z, w)` of four families of lengths `a`, `b`, `c` and `d`. Exchanging the two middle
blocks `y` and `z` permutes the arguments by a block swap, which has `b * c` inversions; hence
`f (x, z, y, w) = (-1) ^ (b * c) • f (x, y, z, w)`
(`AlternatingMap.map_append_append_comm`). This is the Koszul sign rule for reordering two blocks
of vectors in a determinant, as in the multiplicativity of the torsion of chain complexes.
-/

public section

namespace AlternatingMap

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommGroup N] [Module R N]
  {a b c d : ℕ}

/-- Exchanging the two middle blocks of arguments, of lengths `b` and `c`, of an alternating map
evaluated on a concatenation of four families multiplies its value by `(-1) ^ (b * c)`. -/
theorem map_append_append_comm (f : M [⋀^Fin (a + b + (c + d))]→ₗ[R] N) (x : Fin a → M)
    (y : Fin b → M) (z : Fin c → M) (w : Fin d → M) :
    f (Fin.append (Fin.append x z) (Fin.append y w) ∘ Fin.cast (by omega)) =
      (-1 : ℤˣ) ^ (b * c) • f (Fin.append (Fin.append x y) (Fin.append z w)) := by
  -- The block swap `S` of `Fin (c + b)` moves the first `c` indices behind the last `b`; acting
  -- on the middle `c + b` indices of `Fin (a + ((c + b) + d))`, it carries the arguments
  -- `(x, z, y, w)` to `(x, y, z, w)`.
  set S : Equiv.Perm (Fin (c + b)) := finAddFlip.trans (finCongr (add_comm b c))
  set τ : Equiv.Perm (Fin (a + ((c + b) + d))) := finSumFinEquiv.permCongr
    (Equiv.Perm.sumCongr 1 (finSumFinEquiv.permCongr (Equiv.Perm.sumCongr S 1)))
  set e : Fin (a + ((c + b) + d)) ≃ Fin (a + b + (c + d)) := finCongr (by omega)
  have hsign : Equiv.Perm.sign (e.permCongr τ) = (-1) ^ (b * c) := by
    simp only [τ, S, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_one,
      one_mul, mul_one, TauCeti.sign_finAddFlip_trans_finCongr, mul_comm c b]
  -- On each of the four blocks, `e.permCongr τ` sends the position of an argument of
  -- `(x, z, y, w)` to the position of the same argument in `(x, y, z, w)`.
  have hp : a + c + (b + d) = a + b + (c + d) := by omega
  have h₁ (i : Fin a) : e.permCongr τ (finCongr hp (Fin.castAdd (b + d) (Fin.castAdd c i))) =
      Fin.castAdd (c + d) (Fin.castAdd b i) := by
    have : e.symm (finCongr hp (Fin.castAdd (b + d) (Fin.castAdd c i))) =
        Fin.castAdd ((c + b) + d) i := Fin.ext rfl
    simp only [Equiv.permCongr_apply, this]
    ext
    simp [τ, e]
  have h₂ (k : Fin c) : e.permCongr τ (finCongr hp (Fin.castAdd (b + d) (Fin.natAdd a k))) =
      Fin.natAdd (a + b) (Fin.castAdd d k) := by
    have : e.symm (finCongr hp (Fin.castAdd (b + d) (Fin.natAdd a k))) =
        Fin.natAdd a (Fin.castAdd d (Fin.castAdd b k)) := Fin.ext rfl
    simp only [Equiv.permCongr_apply, this]
    ext
    simp [τ, S, e, finAddFlip_apply_castAdd]
    omega
  have h₃ (j : Fin b) : e.permCongr τ (finCongr hp (Fin.natAdd (a + c) (Fin.castAdd d j))) =
      Fin.castAdd (c + d) (Fin.natAdd a j) := by
    have : e.symm (finCongr hp (Fin.natAdd (a + c) (Fin.castAdd d j))) =
        Fin.natAdd a (Fin.castAdd d (Fin.natAdd c j)) := Fin.ext (Nat.add_assoc a c j)
    simp only [Equiv.permCongr_apply, this]
    ext
    simp [τ, S, e, finAddFlip_apply_natAdd]
  have h₄ (l : Fin d) : e.permCongr τ (finCongr hp (Fin.natAdd (a + c) (Fin.natAdd b l))) =
      Fin.natAdd (a + b) (Fin.natAdd c l) := by
    have : e.symm (finCongr hp (Fin.natAdd (a + c) (Fin.natAdd b l))) =
        Fin.natAdd a (Fin.natAdd (c + b) l) := Fin.ext (by simp [e]; omega)
    simp only [Equiv.permCongr_apply, this]
    ext
    simp [τ, e]
    omega
  have hv : Fin.append (Fin.append x y) (Fin.append z w) ∘ e.permCongr τ =
      Fin.append (Fin.append x z) (Fin.append y w) ∘ Fin.cast (by omega) := by
    ext p
    obtain ⟨q, rfl⟩ := (finCongr hp).surjective p
    induction q using Fin.addCases with
    | left q => induction q using Fin.addCases <;> simp only [Function.comp_apply, h₁, h₂] <;> simp
    | right q => induction q using Fin.addCases <;> simp only [Function.comp_apply, h₃, h₄] <;> simp
  rw [← hv, f.map_perm, hsign]

end AlternatingMap

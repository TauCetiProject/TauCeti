/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WittVector.Truncated.Basic
public import TauCeti.RingTheory.WittVector.Teichmuller.Basic

/-!
# Teichmüller representatives in finite Witt rings

The finite Teichmüller map is the truncation of the full Witt representative.
Multiplication by `[a]` scales coordinate `i` by `a ^ p ^ i`.
-/

public section

noncomputable section

namespace TruncatedWittVector

variable (p : ℕ) [Fact p.Prime] (n : ℕ)
variable {A B : Type*} [CommRing A] [CommRing B]

/-- The Teichmüller representative in a finite Witt ring. -/
def teichmuller : A →* TruncatedWittVector p n A :=
  (WittVector.truncate n).toMonoidHom.comp (WittVector.teichmuller p)

/-- A finite Teichmüller representative is the truncation of the full representative. -/
theorem teichmuller_apply (a : A) :
    teichmuller p n a = WittVector.truncate n (WittVector.teichmuller p a) := (rfl)

/-- The Teichmüller representative of zero is zero. -/
@[simp]
theorem teichmuller_zero : teichmuller p n (0 : A) = 0 := by
  rw [teichmuller_apply, WittVector.teichmuller_zero, map_zero]

/-- Changing coefficients preserves finite Teichmüller representatives. -/
@[simp]
theorem map_teichmuller (f : A →+* B) (a : A) :
    map n f (teichmuller p n a) = teichmuller p n (f a) := by
  simp only [teichmuller_apply, map_wittVector_truncate, WittVector.map_teichmuller]

/-- The coordinates of a finite Teichmüller representative. -/
@[simp]
theorem teichmuller_coeff (a : A) (i : Fin n) :
    (teichmuller p n a).coeff i = if i.val = 0 then a else 0 := by
  rw [teichmuller_apply, WittVector.coeff_truncate]
  split_ifs with h
  · simp only [h, WittVector.teichmuller_coeff_zero]
  · exact WittVector.teichmuller_coeff_pos _ _ _ (Nat.pos_of_ne_zero h)

/-- Multiplication by a Teichmüller representative scales coordinate `i` by `a ^ p ^ i`. -/
@[simp]
theorem teichmuller_mul_coeff (a : A) (x : TruncatedWittVector p n A) (i : Fin n) :
    (teichmuller p n a * x).coeff i = a ^ p ^ i.val * x.coeff i := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective (p := p) n A x
  rw [teichmuller_apply, ← map_mul, WittVector.coeff_truncate,
    WittVector.teichmuller_mul_coeff, WittVector.coeff_truncate]

end TruncatedWittVector

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Semisimple
import TauCeti.RingTheory.SimpleModule.Basic

/-!
# Products of endomorphisms

This file proves that nilpotence and semisimplicity are preserved by componentwise products of
endomorphisms.

## Main declarations

* `IsNilpotent.prodMap`: a product of nilpotent endomorphisms is nilpotent.
* `Module.End.IsSemisimple.prodMap`: a product of semisimple endomorphisms is semisimple.
-/

public section

namespace TauCeti

open LinearMap Polynomial

section

universe u v w

section Semiring

variable {K : Type u} {V : Type v} {W : Type w}
variable [Semiring K] [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]

/-- A power of a componentwise product of endomorphisms is the componentwise product of the
powers. -/
@[simp]
private theorem _root_.Module.End.prodMap_pow (f : Module.End K V) (g : Module.End K W) (n : ℕ) :
    (f.prodMap g) ^ n = (f ^ n).prodMap (g ^ n) := by
  induction n with
  | zero => exact LinearMap.prodMap_one.symm
  | succ n hn => rw [pow_succ, pow_succ, pow_succ, hn, LinearMap.prodMap_mul]

/-- The componentwise product of two nilpotent endomorphisms is nilpotent. -/
theorem _root_.IsNilpotent.prodMap {f : Module.End K V} {g : Module.End K W}
    (hf : IsNilpotent f) (hg : IsNilpotent g) : IsNilpotent (f.prodMap g) := by
  obtain ⟨m, hm⟩ := hf
  obtain ⟨n, hn⟩ := hg
  refine ⟨m + n, ?_⟩
  rw [Module.End.prodMap_pow, pow_add, hm, zero_mul, pow_add, hn, mul_zero,
    LinearMap.prodMap_zero]

end Semiring

section CommSemiring

variable {K : Type u} {V : Type v} {W : Type w}
variable [CommSemiring K] [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]

/-- Evaluating a polynomial at a componentwise product of endomorphisms is the componentwise
product of the evaluations. -/
private theorem _root_.Module.End.aeval_prodMap (f : Module.End K V) (g : Module.End K W)
    (p : K[X]) :
    aeval (f.prodMap g) p = (aeval f p).prodMap (aeval g p) := by
  have h : aeval (f.prodMap g) =
      (LinearMap.prodMapAlgHom K V W).comp ((aeval f).prod (aeval g)) := by
    ext <;> simp
  exact DFunLike.congr_fun h p

end CommSemiring

section CommRing

variable {K : Type u} {V : Type v} {W : Type w}
variable [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The componentwise product of two semisimple endomorphisms is semisimple. -/
theorem _root_.Module.End.IsSemisimple.prodMap {f : Module.End K V} {g : Module.End K W}
    (hf : f.IsSemisimple) (hg : g.IsSemisimple) :
    Module.End.IsSemisimple (f.prodMap g) := by
  rw [Module.End.IsSemisimple] at hf hg ⊢
  let _ : IsSemisimpleModule K[X] (Module.AEval' f) := hf
  let _ : IsSemisimpleModule K[X] (Module.AEval' g) := hg
  have hprod : IsSemisimpleModule K[X] (Module.AEval' f × Module.AEval' g) := inferInstance
  let E : Module.AEval' (f.prodMap g) ≃ₗ[K[X]]
      Module.AEval' f × Module.AEval' g := {
    toFun x := (x.1, x.2)
    invFun x := (x.1, x.2)
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' p x := by
      -- Unfold the two `AEval` scalar actions to compare their underlying endomorphisms.
      apply Prod.ext
      · change ((aeval (f.prodMap g) p) x).1 = (aeval f p) x.1
        rw [Module.End.aeval_prodMap]
        rfl
      · change ((aeval (f.prodMap g) p) x).2 = (aeval g p) x.2
        rw [Module.End.aeval_prodMap]
        rfl
  }
  let _ := hprod
  exact IsSemisimpleModule.congr E

end CommRing

end

end TauCeti

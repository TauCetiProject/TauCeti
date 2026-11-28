/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Free.Basic
public import TauCeti.Algebra.Lie.Quotient

/-!
# Quotients of free Lie algebras

Generic extensionality and generation results for quotients `FreeLieAlgebra R X ⧸ J` of a free Lie
algebra over a commutative ring `R` by a Lie ideal `J`.

## Main results

* `TauCeti.FreeLieAlgebra.quotient_hom_ext`: two Lie homomorphisms out of a quotient of a free
  Lie algebra agreeing on the generator classes are equal.
* `LieIdeal.lieSpan_range_mkQ_of_eq_top`: the generator classes generate any quotient of a free
  Lie algebra as a Lie subalgebra.
-/

public section

namespace TauCeti

namespace FreeLieAlgebra

/-- Two Lie homomorphisms out of a quotient of a free Lie algebra that agree on the generator
classes are equal. -/
@[ext high]
theorem quotient_hom_ext {R X L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    {J : LieIdeal R (_root_.FreeLieAlgebra R X)}
    {g₁ g₂ : _root_.FreeLieAlgebra R X ⧸ J →ₗ⁅R⁆ L}
    (h : ∀ x : X, g₁ (J.mkQ (_root_.FreeLieAlgebra.of R x)) =
      g₂ (J.mkQ (_root_.FreeLieAlgebra.of R x))) : g₁ = g₂ := by
  refine J.lieHom_qext fun y => ?_
  exact DFunLike.congr_fun
    (_root_.FreeLieAlgebra.hom_ext h : g₁.comp J.mkQ = g₂.comp J.mkQ) y

end FreeLieAlgebra

end TauCeti

namespace LieIdeal

/-- The generator classes generate any quotient of a free Lie algebra as a Lie subalgebra. -/
theorem lieSpan_range_mkQ_of_eq_top {R : Type*} [CommRing R] {X : Type*}
    (J : LieIdeal R (FreeLieAlgebra R X)) :
    LieSubalgebra.lieSpan R (FreeLieAlgebra R X ⧸ J)
      (Set.range fun x : X => J.mkQ (FreeLieAlgebra.of R x)) = ⊤ := by
  have hcomp : FreeLieAlgebra.lift R (fun x : X => J.mkQ (FreeLieAlgebra.of R x)) = J.mkQ :=
    FreeLieAlgebra.hom_ext fun x => by simp
  rw [← TauCeti.FreeLieAlgebra.range_lift_eq_lieSpan, hcomp, LieIdeal.range_mkQ]

end LieIdeal

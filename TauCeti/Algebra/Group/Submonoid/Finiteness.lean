/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Finiteness
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Algebra.Order.Pi
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Order.Sub.Prod

/-!
# Preimages of finitely generated additive submonoids

The preimage of a finitely generated additive submonoid under a homomorphism from a finitely
generated commutative monoid is finitely generated, provided the target is cancellative.
For instance, since the nonnegative integer vectors form a finitely generated submonoid of
`ℤⁿ`, finitely many integral linear inequalities on a finitely generated abelian group cut out a
finitely generated additive submonoid.

The proof uses Mathlib's `AddSubmonoid.fg_iff_exists_fin_addMonoidHom` to parametrize both
monoids by finite products of naturals, and `AddSubmonoid.fg_eqLocusM` to impose equality of their
images. This is the slack-variable form of Gordan's lemma.

## References

* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §1.2, Gordan's lemma.
-/

public section

/-- The preimage of a finitely generated additive submonoid of a cancellative commutative monoid
under a homomorphism from a finitely generated commutative monoid is finitely generated. -/
theorem AddSubmonoid.FG.comap {M G : Type*} [AddCommMonoid M] [AddCommMonoid G]
    [IsCancelAdd G] [AddMonoid.FG M] {P : AddSubmonoid G} (hP : P.FG) (f : M →+ G) :
    (P.comap f).FG := by
  obtain ⟨n, q, hq⟩ := AddSubmonoid.fg_iff_exists_fin_addMonoidHom.mp
    (AddMonoid.FG.fg_top (M := M))
  obtain ⟨k, g, rfl⟩ := AddSubmonoid.fg_iff_exists_fin_addMonoidHom.mp hP
  -- Pair a parameter of `M` with a slack vector parametrizing `P`, and keep the pairs whose
  -- images under `f` and `g` agree.
  let π := q.comp (AddMonoidHom.fst _ (Fin k → ℕ))
  convert (AddSubmonoid.fg_eqLocusM (f.comp π) (g.comp (.snd ..))).map π
  ext x
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨a, rfl⟩ := AddMonoidHom.mrange_eq_top.mp hq x
    exact ⟨(a, b), hb.symm, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, ha.symm⟩

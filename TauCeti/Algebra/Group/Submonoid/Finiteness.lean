/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Algebra.Order.Pi
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Order.Sub.Prod

/-!
# Preimages of finitely generated additive submonoids

The preimage of a finitely generated additive submonoid under a homomorphism from a finitely
generated commutative monoid is finitely generated, provided the target is cancellative.
In particular, finitely many integral linear inequalities on a finitely generated abelian group
define a finitely generated additive submonoid: nonnegative integer vectors are the image of a
finite product of naturals under coordinatewise casting.

The construction uses Mathlib's `AddSubmonoid.fg_iff_exists_fin_addMonoidHom` to parametrize both
monoids by finite products of naturals, and `AddSubmonoid.fg_eqLocusM` to impose equality of their
images. This is the slack-variable form of Gordan's lemma.

## References

* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §1.2, Gordan's lemma.
-/

public section

namespace TauCeti

/-- The preimage of a finitely generated additive submonoid of a cancellative commutative monoid
is finitely generated when the source monoid is finitely generated. -/
theorem _root_.AddSubmonoid.FG.comap {M G : Type*} [AddCommMonoid M] [AddCommMonoid G]
    [IsCancelAdd G] [AddMonoid.FG M] {P : AddSubmonoid G} (hP : P.FG) (f : M →+ G) :
    (P.comap f).FG := by
  obtain ⟨n, q, hq⟩ := AddSubmonoid.fg_iff_exists_fin_addMonoidHom.mp
    (AddMonoid.FG.fg_top (M := M))
  obtain ⟨k, g, hg⟩ := AddSubmonoid.fg_iff_exists_fin_addMonoidHom.mp hP
  have hqsurj := AddMonoidHom.mrange_eq_top.mp hq
  let π := q.comp (AddMonoidHom.fst (Fin n → ℕ) (Fin k → ℕ))
  let γ := g.comp (AddMonoidHom.snd (Fin n → ℕ) (Fin k → ℕ))
  have hfg := (AddSubmonoid.fg_eqLocusM (f.comp π) γ).map π
  have heq : ((f.comp π).eqLocusM γ).map π = P.comap f := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [AddSubmonoid.mem_comap, ← hg, AddMonoidHom.mem_mrange]
      exact ⟨a.2, (AddMonoidHom.mem_eqLocusM.mp ha).symm⟩
    · intro hx
      obtain ⟨a, rfl⟩ := hqsurj x
      rw [AddSubmonoid.mem_comap, ← hg, AddMonoidHom.mem_mrange] at hx
      obtain ⟨b, hb⟩ := hx
      exact ⟨(a, b), AddMonoidHom.mem_eqLocusM.mpr hb.symm, rfl⟩
  exact heq ▸ hfg

end TauCeti

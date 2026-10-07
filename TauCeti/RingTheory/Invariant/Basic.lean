/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Invariant.Basic

/-!
# Fixed rings and characteristic polynomials of group actions

The fixed subring and fixed subalgebra are invariant extensions, so the integral-extension
and prime-orbit theorems apply to them.

Let a finite group `G` act on an integral domain `B`. Mathlib's
`MulSemiringAction.charpoly G b = ∏ g : G, (X - C (g • b))` is the monic polynomial whose roots
are the translates of `b`. When those translates are pairwise distinct, it divides every
polynomial vanishing on all of them. This is the step that turns "vanishes on the orbit" into
an explicit factorization, for instance when comparing the displacement of a generator of an
intermediate ring with a product of displacements of a generator of the top ring.

## Main results

* The fixed-subring and fixed-subalgebra instances of `Algebra.IsInvariant` identify the
  invariant extensions.
* `TauCeti.MulSemiringAction.charpoly_dvd`: if `g ↦ g • b` is injective and `f` vanishes at every
  `g • b`, then `charpoly G b ∣ f`.
* `TauCeti.MulSemiringAction.eval_smul_charpoly`: evaluating `σ • charpoly H b` at `b` gives the
  product of the displacements `b - σ • τ • b`.
-/

public section

open Polynomial

namespace TauCeti.Algebra.IsInvariant

/-- The fixed subring is an invariant extension: every fixed element lies in its image. -/
instance (A G : Type*) [CommRing A] [Group G] [MulSemiringAction G A] :
    Algebra.IsInvariant (FixedPoints.subring A G) A G where
  isInvariant a ha := ⟨⟨a, ha⟩, rfl⟩

/-- The fixed subalgebra is an invariant extension: every fixed element lies in its image. -/
-- Ambient commutativity supplies the commutative base and canonical inclusion algebra
-- required by `Algebra.IsInvariant`; neither follows from a general `Semiring A`.
instance (R A G : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] [Group G]
    [MulSemiringAction G A] [SMulCommClass G R A] :
    Algebra.IsInvariant (FixedPoints.subalgebra R A G) A G where
  isInvariant a ha := ⟨⟨a, ha⟩, rfl⟩

end TauCeti.Algebra.IsInvariant

namespace TauCeti.MulSemiringAction

section

variable {G B : Type*} [Group G] [Fintype G] [CommRing B] [IsDomain B] [MulSemiringAction G B]

/-- The characteristic polynomial of a point with pairwise distinct translates divides every
polynomial vanishing on its orbit. -/
theorem charpoly_dvd {b : B} (hb : Function.Injective fun g : G ↦ g • b) {f : B[X]}
    (hf : ∀ g : G, f.eval (g • b) = 0) : MulSemiringAction.charpoly G b ∣ f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact dvd_zero _
  convert (Multiset.prod_X_sub_C_dvd_iff_le_roots hf0 _).2
    ((Multiset.le_iff_subset (Finset.univ.nodup.map hb)).2 fun a ha ↦ ?_)
  · simp [MulSemiringAction.charpoly_eq]
  obtain ⟨g, -, rfl⟩ := Multiset.mem_map.1 ha
  exact (mem_roots hf0).2 (hf g)

end

variable {G H B : Type*} [Monoid G] [Group H] [Fintype H] [CommRing B]
  [MulSemiringAction G B] [MulSemiringAction H B]

/-- Evaluating a transformed characteristic polynomial at the point gives the product of its
displacements: `(σ • charpoly H b)(b) = ∏ τ, (b - σ • τ • b)`. -/
theorem eval_smul_charpoly (σ : G) (b : B) :
    (σ • MulSemiringAction.charpoly H b).eval b = ∏ τ : H, (b - σ • τ • b) := by
  simp [MulSemiringAction.charpoly_eq, Finset.smul_prod', eval_prod, smul_sub, smul_C]

end TauCeti.MulSemiringAction

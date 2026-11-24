/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Reduced
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Points

/-!
# Points of infinitesimal diagonalizable groups over reduced rings

Let `p` be a prime and `G` a finitely generated commutative group killed by a power `p^n`, so
that the diagonalizable group scheme `D(G)` is a product of copies of `μ_{p^k}` with `k ≤ n`. Over
a reduced ring `A` of characteristic `p`, the only `A`-valued point of `D(G)` is the identity: a
point is a character `χ : G → Aˣ`, and each value `u = χ g` satisfies `u^(p^n) = 1 = 1^(p^n)`, so
`u = 1` because the iterated Frobenius is injective on a reduced ring of characteristic `p`. In
particular every geometric point of `μ_p` over a field of characteristic `p` is the identity,
although `μ_p` has nonidentity points over nonreduced rings such as `𝔽_p[ε]/(ε²)`.

## Main results

* `TauCeti.DiagonalizableGroup.subsingleton_schemePoints_of_isReduced`: over a reduced ring of
  exponential characteristic `p`, the diagonalizable group scheme of a group killed by `p^n` has
  only one point.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace TauCeti.DiagonalizableGroup

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- **Points of `μ_{p^n}` over a reduced ring of characteristic `p`.** If every element of `G`
is killed by `p^n`, a reduced ring `A` of exponential characteristic `p` has only the identity as
an `A`-valued point of `D(G)`: every value `u` of a character satisfies `u^(p^n) = 1^(p^n)`, and
the iterated Frobenius is injective on `A`. -/
theorem subsingleton_schemePoints_of_isReduced (p n : ℕ) [ExpChar A p] [IsReduced A]
    (G : FGCommGrpCat.{u}) (hG : ∀ g : G, g ^ p ^ n = 1) :
    Subsingleton ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R G).X) := by
  refine (schemePointsMulEquiv (R := R) (A := A) G).toEquiv.subsingleton_congr.mpr ⟨fun χ ψ ↦ ?_⟩
  -- Every character is trivial.
  have h (χ : G →* Aˣ) : χ = 1 := by
    ext g
    apply iterateFrobenius_inj A p n
    simp [iterateFrobenius_def, ← Units.val_pow_eq_pow_val, ← map_pow, hG]
  rw [h χ, h ψ]

end TauCeti.DiagonalizableGroup

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PicardGroup

/-!
# Reduction of invertible modules modulo an ideal

If `M` is an invertible module over a commutative ring `R` and the Picard group of `R / J` is
trivial, then `M / JM` is isomorphic to `R / J`. Mathlib provides this triviality when `R / J`
is semilocal (for instance Artinian) or a GCD domain. The isomorphism need not be canonical:
it amounts to choosing a basis for the invertible module after reduction. Applied to an
invertible ideal `I`, it identifies `I / IJ` with `R / J`; this is the step that makes
finite codimension over a field additive on `I * J`.

The base-change argument generalizes the corresponding step of the point-to-class
surjectivity proof, adapted from Chris Birkbeck's AINTLIB (`github.com/CBirkbeck/AINTLIB`,
`HasseWeil/Pic0/ToClassSurjective.lean`, revision `dev/hasse-weil @ 513e83879e2f`, Apache-2.0).
-/

public section

open scoped TensorProduct

namespace Module.Invertible

variable {R : Type*} [CommRing R]

/-- An invertible module reduced modulo an ideal `J` is isomorphic to the quotient ring
`R / J` as an `R`-module, provided `R / J` has trivial Picard group (for instance, when `R / J`
is semilocal). No choice of a trivialization is specified. -/
theorem nonempty_quotientEquiv (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Invertible R M] (J : Ideal R) [Subsingleton (CommRing.Pic (R ⧸ J))] :
    Nonempty ((M ⧸ J • (⊤ : Submodule R M)) ≃ₗ[R] R ⧸ J) := by
  let A := R ⧸ J
  let e : A ⊗[R] M ≃ₗ[A] A :=
    (free_iff_linearEquiv.mp (inferInstance : Module.Free A (A ⊗[R] M))).some
  exact ⟨(TensorProduct.quotTensorEquivQuotSMul M J).symm.trans (e.restrictScalars R)⟩

end Module.Invertible

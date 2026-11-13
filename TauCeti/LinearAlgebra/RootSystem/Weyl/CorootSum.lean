/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.Vector
import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# The sum of the positive coroots measures height

Let `b` be a base of a reduced crystallographic root system `P`. The sum `2ρ^∨` of the positive
coroots is `TauCeti.twoWeylVector P.flip b.flip`, the sum of the positive roots of the flipped
root system. It pairs to `2` with every simple root (`TauCeti.coroot'_twoWeylVector`), so pairing
with it is twice the height functional `TauCeti.heightLinearMap P b`:

`⟨x, 2ρ^∨⟩ = 2 ht(x)` for every weight `x`.

In particular `2ρ^∨` pairs to a nonzero scalar with every nonzero member of the positive root
cone. This is the grading that the principal `sl₂` triple of a split semisimple Lie algebra
induces on its modules: a weight below a highest weight `λ` has strictly smaller pairing with
`2ρ^∨` than `λ`.

## Main results

* `TauCeti.twoWeylVector_flip_eq_sum_coroot`: `2ρ^∨` is the sum of the positive coroots.
* `TauCeti.toLinearMap_twoWeylVector_flip_eq_two_mul_heightLinearMap`: pairing with the sum of
  the positive coroots is twice the height functional.
* `TauCeti.toLinearMap_twoWeylVector_flip_ne_zero_of_mem_posRootCone`: a nonzero member of the
  positive root cone pairs to a nonzero scalar with the sum of the positive coroots.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Chapitre VI, §1.10.
-/

public section

namespace TauCeti

open RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N) [CharZero R] [IsDomain R] [Finite ι]
  [P.IsCrystallographic] [P.IsReduced] (b : P.Base)

/-- **`2ρ^∨` is the sum of the positive coroots.** The positive roots of the flipped base are the
positive roots of `b` (`TauCeti.posRoots_flip`), and the roots of the flipped root system are the
coroots. -/
theorem twoWeylVector_flip_eq_sum_coroot :
    twoWeylVector P.flip b.flip = ∑ i ∈ posRootsFinset P b, P.coroot i := by
  have := P.flip_isReduced
  have hfin : posRootsFinset P.flip b.flip = posRootsFinset P b := by
    ext i
    simp [mem_posRootsFinset]
  rw [twoWeylVector_def, hfin]
  simp only [RootPairing.flip_root]

variable [P.IsRootSystem]

/-- **Pairing with the sum of the positive coroots is twice the height.** Both sides are linear in
the weight, and on a simple root the left side is `2` (`TauCeti.coroot'_twoWeylVector` for the
flipped root system) while the height is `1`. -/
theorem toLinearMap_twoWeylVector_flip_eq_two_mul_heightLinearMap (x : M) :
    P.toLinearMap x (twoWeylVector P.flip b.flip) = 2 * heightLinearMap P b x := by
  have := P.flip_isReduced
  have hfun : P.toLinearMap.flip (twoWeylVector P.flip b.flip) = (2 : R) • heightLinearMap P b :=
    b.toWeightBasis.ext fun i ↦ by
      rw [LinearMap.flip_apply, b.toWeightBasis_apply, LinearMap.smul_apply,
        heightLinearMap_simpleRoot, smul_eq_mul, mul_one]
      exact coroot'_twoWeylVector P.flip b.flip i.2
  simpa using LinearMap.congr_fun hfun x

/-- **A nonzero member of the positive root cone pairs nontrivially with the sum of the positive
coroots.** The pairing is twice the height
(`TauCeti.toLinearMap_twoWeylVector_flip_eq_two_mul_heightLinearMap`), and the only member of the
cone of height zero is zero. -/
theorem toLinearMap_twoWeylVector_flip_ne_zero_of_mem_posRootCone {x : M}
    (hx : x ∈ posRootCone P b) (hx0 : x ≠ 0) :
    P.toLinearMap x (twoWeylVector P.flip b.flip) ≠ 0 := by
  rw [toLinearMap_twoWeylVector_flip_eq_two_mul_heightLinearMap, mul_ne_zero_iff]
  exact ⟨two_ne_zero, fun h ↦ hx0 (eq_zero_of_mem_posRootCone_of_heightLinearMap_eq_zero P b hx h)⟩

end TauCeti

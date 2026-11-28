/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic
public import TauCeti.Algebra.AlgebraicGroup.LoopGroup.Preimage

/-!
# The Iwahori subgroup of `GL_n`

For a commutative ring `k`, a commutative `k`-algebra `R` and the upper triangular subgroup
`B ⊆ GL_n` (`TauCeti.GeneralLinear.UpperTriangular.definingHopfIdeal`), the preimage of `B(R)`
under reduction modulo `t`, `TauCeti.HopfAlgebra.positiveLoopPreimage`, is the Iwahori subgroup
of `GL_n(R⟦t⟧)`: the matrices whose entries strictly below the diagonal are divisible by `t`.
For `n = 2` these are the matrices of `GL₂(R⟦t⟧)` whose lower left entry lies in `t R⟦t⟧`.

## Main results

* `TauCeti.GeneralLinear.UpperTriangular.mem_positiveLoopPreimage_definingHopfIdeal_iff`: a
  positive loop of `GL_n` lies in the Iwahori subgroup exactly when the entries of its matrix
  strictly below the diagonal are divisible by `t`.

## References

* N. Iwahori, H. Matsumoto, *On some Bruhat decomposition and the structure of the Hecke rings
  of p-adic Chevalley groups*, Publ. Math. IHÉS 25 (1965), §2.
-/

public section

open PowerSeries

universe u w

namespace TauCeti.GeneralLinear.UpperTriangular

variable {k : Type u} [CommRing k] {n : ℕ} {R : Type w} [CommRing R] [Algebra k R]

/-- **The Iwahori subgroup of `GL_n`.** A positive loop `g ∈ GL_n(R⟦t⟧)` reduces modulo `t` into
the upper triangular subgroup exactly when every entry of its matrix strictly below the diagonal
is divisible by `t`. -/
theorem mem_positiveLoopPreimage_definingHopfIdeal_iff
    (g : WithConv (GeneralLinear.coordinateHopfAlgebra k n →ₐ[k] R⟦X⟧)) :
    g ∈ HopfAlgebra.positiveLoopPreimage (GeneralLinear.coordinateHopfAlgebra k n)
        (definingHopfIdeal k n) R ↔
      ∀ i j, j < i → (X : R⟦X⟧) ∣ GeneralLinear.pointsMulEquiv n g i j := by
  rw [HopfAlgebra.mem_positiveLoopPreimage, mem_definingPointsSubgroup_iff,
    UpperTriangularGroup.mem_iff]
  simp only [Matrix.IsUpperTriangular, Matrix.BlockTriangular, id,
    GeneralLinear.pointsMulEquiv_apply, GeneralLinear.pointToGeneralLinear_apply,
    HopfAlgebra.ofConv_positiveLoopEvalZero_apply, X_dvd_iff]

/-- For `n = 2`, a matrix of `GL₂(R⟦t⟧)` lies in the Iwahori subgroup exactly when its lower left
entry is divisible by `t`. -/
example (g : GL (Fin 2) R⟦X⟧) :
    (GeneralLinear.pointsMulEquiv (R := k) 2).symm g ∈
        HopfAlgebra.positiveLoopPreimage (GeneralLinear.coordinateHopfAlgebra k 2)
          (definingHopfIdeal k 2) R ↔
      (X : R⟦X⟧) ∣ g 1 0 := by
  rw [mem_positiveLoopPreimage_definingHopfIdeal_iff, MulEquiv.apply_symm_apply]
  refine ⟨fun h ↦ h 1 0 Fin.zero_lt_one, fun h i j hji ↦ ?_⟩
  obtain rfl : i = 1 := by omega
  obtain rfl : j = 0 := by omega
  exact h

end TauCeti.GeneralLinear.UpperTriangular

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable
public import TauCeti.RingTheory.CyclicCohomology.OddPairing.Invariance

/-!
# The odd pairing of cyclic cohomology with algebraic `K₁`

Let `A` be a unital complex algebra and `M` a complex vector space. Connes' odd pairing
`⟨[u], [φ]⟩` of an invertible matrix `u` over `A` with a class `[φ] ∈ HC²ᵐ⁺¹(A; M)` is computed
through the matrix extension `φ#Tr` (`TauCeti.cyclicCohomology.oddPairing`). This file shows that
it descends to algebraic `K₁(A) = GL_∞(A) / E_∞(A)`:

* relabelling the rows and columns of `u` does not change the pairing
  (`Equiv.oddPairing_reindexGL`), and neither does the stabilization `u ↦ u ⊕ 1`, so the
  pairings of the groups `GL (Fin n) A` assemble into a homomorphism on `GL_∞(A)`;
* the pairing is multiplicative and takes values in an abelian group, so this homomorphism
  factors through the abelianization `K₁(A)` of `GL_∞(A)`.

The result is a homomorphism from `K₁(A)` to the additive group of functionals on
`HC²ᵐ⁺¹(A; M)`, written multiplicatively as for `TauCeti.cyclicCohomology.oddPairingHom`.

## Main definitions

* `TauCeti.AlgebraicK1.oddPairing`: Connes' odd pairing of algebraic `K₁` with odd cyclic
  cohomology.

## Main results

* `TauCeti.cyclicCohomology.oddPairing_stabilizeGL`: the odd pairing is invariant under
  stabilization `GL (Fin m) A → GL (Fin n) A`.
* `TauCeti.AlgebraicK1.oddPairing_mk`: on the class of an invertible matrix, the pairing on `K₁`
  is the odd pairing of the matrix.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §3, Proposition 3.
* J.-L. Loday, *Cyclic Homology*, §8.3.
-/

public section

noncomputable section

namespace TauCeti

variable {A M : Type*} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M]

namespace cyclicCohomology

/-- **Stabilization invariance of the odd pairing**: the stabilization `u ↦ u ⊕ 1` from
`GL (Fin m) A` to `GL (Fin n) A` does not change the odd pairing. -/
theorem oddPairing_stabilizeGL {m n : ℕ} (h : m ≤ n) (u : GL (Fin m) A) (k : ℕ)
    (c : cyclicCohomology ℂ A M (2 * k + 1)) :
    oddPairing (stabilizeGL A h u) k (matrixExtension M (Fin n) (2 * k + 1) c) =
      oddPairing u k (matrixExtension M (Fin m) (2 * k + 1) c) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [stabilizeGL_eq_reindexGL_fromBlocksGL, Equiv.oddPairing_reindexGL]
  exact oddPairing_matrixExtension_of_val_eq_fromBlocks_one (by simp) k c

end cyclicCohomology

namespace AlgebraicK1

open cyclicCohomology

variable (A M) in
/-- **Connes' odd pairing of algebraic `K₁` with cyclic cohomology** in degree `2m + 1`: the class
of an invertible matrix `u` is sent to the functional `[φ] ↦ ⟨[u], [φ]⟩` on `HC²ᵐ⁺¹(A; M)`,
computed through the matrix extension `φ#Tr`. It is a homomorphism to the additive group of
functionals, written multiplicatively. -/
def oddPairing (m : ℕ) :
    AlgebraicK1 A →* Multiplicative (cyclicCohomology ℂ A M (2 * m + 1) →ₗ[ℂ] M) :=
  lift (fun n ↦
    { toFun u := .ofAdd
        (cyclicCohomology.oddPairing u m ∘ₗ matrixExtension M (Fin n) (2 * m + 1))
      map_one' := by simp
      map_mul' u v := by simp [LinearMap.add_comp] })
    fun _ _ h u ↦ congrArg Multiplicative.ofAdd
      (LinearMap.ext fun c ↦ oddPairing_stabilizeGL h u m c)

/-- On the class of an invertible matrix `u`, the odd pairing of algebraic `K₁` is the odd pairing
of `u` with the matrix extensions of cyclic cohomology classes. -/
@[simp]
theorem oddPairing_mk (m n : ℕ) (u : GL (Fin n) A) :
    oddPairing A M m (mk A n u) =
      .ofAdd (cyclicCohomology.oddPairing u m ∘ₗ matrixExtension M (Fin n) (2 * m + 1)) :=
  lift_mk ..

end AlgebraicK1

end TauCeti

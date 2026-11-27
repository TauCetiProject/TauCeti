/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import TauCeti.LinearAlgebra.Charpoly.Dual
import TauCeti.LinearAlgebra.Matrix.Charpoly.Reverse

/-!
# Characteristic polynomials under a pairing with a multiplier

Let `B : M × M' → R` identify `M'` with the dual of a finite free module `M` of rank `n`, and let
`F`, `F'` be endomorphisms with `B (F x) (F' y) = c • B x y`. Under the identification, the
transpose of `F` composed with `F'` is `c`, so `F'` is `c` times the inverse transpose of `F` when
`c` is a unit. Its reversed characteristic polynomial `det (1 - X F')` is therefore determined by
that of `F`:

  `det F * det (1 - X F') = (-1) ^ n * χ_F (c X)`

(`LinearMap.C_det_mul_reverse_charpoly_of_compl₁₂_eq_smul`). This holds over any commutative ring,
for any `c`, and without any semisimplicity. It is the reciprocity of the Frobenius polynomials
`det (1 - t F)` of complementary cohomology groups under Poincaré duality: for a smooth proper
variety of dimension `d` over `𝔽_q`, `c = q ^ d`. Over a field and for `c ≠ 0`, it refines the
statement that the eigenvalues of `F'` are the `c / α` for the eigenvalues `α` of `F`
(`LinearMap.roots_charpoly_eq_map_div_of_compl₁₂_eq_smul`) to an identity of polynomials, and its
coefficients in degree `n` give the two-space determinant identity
`LinearMap.det_mul_det_eq_of_compl₁₂_eq_smul`.

## References

* P. Deligne, *La conjecture de Weil. I*, Publ. Math. IHÉS 43 (1974), (1.5.1) and (2.4).
-/

public section

open Module Polynomial

namespace LinearMap

variable {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
  [Module.Finite R M] [AddCommGroup M'] [Module R M'] [Module.Free R M'] [Module.Finite R M']

/-- **Reciprocity of characteristic polynomials under a pairing with a multiplier.** If `B`
identifies `M'` with the dual of the finite free module `M` of rank `n` and
`B (F x) (F' y) = c • B x y`, then `det F * det (1 - X F') = (-1) ^ n * χ_F (c X)`. -/
theorem C_det_mul_reverse_charpoly_of_compl₁₂_eq_smul (B : M →ₗ[R] M' →ₗ[R] R)
    (hB : Function.Bijective B.flip) {F : End R M} {F' : End R M'} {c : R}
    (h : B.compl₁₂ F F' = c • B) :
    C (LinearMap.det F) * F'.charpoly.reverse =
      (-1) ^ finrank R M * F.charpoly.comp (C c * X) := by
  nontriviality R
  let e : M' ≃ₗ[R] Dual R M := LinearEquiv.ofBijective B.flip hB
  -- under `e`, the transpose of `F` composed with `F'` is `c`
  have key : F.dualMap * e.conj F' = c • 1 := by
    ext φ x
    obtain ⟨y, rfl⟩ := e.surjective φ
    simpa [e, LinearEquiv.conj_apply] using congr($h x y)
  have := C_det_mul_reverse_charpoly_of_mul_eq_smul_one key
  rwa [det_dualMap, charpoly_dualMap, LinearEquiv.charpoly_conj,
    (Free.chooseBasis R M).toDualEquiv.finrank_eq.symm] at this

end LinearMap

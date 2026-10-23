/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.EvenUnimodular
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.Plus
public import TauCeti.NumberTheory.IntegralLattice.Genus
import TauCeti.LinearAlgebra.IntegralLattice.PosDef.RepresentationNumber
import TauCeti.NumberTheory.IntegralLattice.Dyadic.Unimodular

/-!
# The genus of even unimodular lattices

Two even unimodular lattices with equal signatures lie in one genus. The determinant of a
unimodular lattice is `(-1) ^ n₋`, a unit determined by the signature, so only the prime `2` needs
a local comparison, and there the even unimodular forms over `ℤ_[2]` are classified by rank and
determinant square class. In particular, the positive definite even unimodular lattices of a given
rank form a single genus.

From rank sixteen on, this genus has more than one class. For `k ≥ 2` the lattices `E₈^k` and
`D_{8k}⁺` are both positive definite, even and unimodular of rank `8k`, hence in one genus, but they
are not isometric: the roots of `E₈^k` span it, while every root of `D_{8k}⁺` lies in the
checkerboard sublattice `D_{8k}`, of index two. At `k = 2` this is the pair `E₈ ⊕ E₈` and `D₁₆⁺`.
That these two lattices are the only classes of their genus is not proved here. In rank eight the
same construction gives no second class: `D₈⁺` is isometric to `E₈`.

## Main results

* `TauCeti.IntegralLattice.sameGenus_of_isEven_of_isUnimodular`: even unimodular lattices with
  equal signatures lie in one genus.
* `TauCeti.IntegralLattice.IsPosDef.sameGenus_of_isEven_of_isUnimodular`: positive definite even
  unimodular lattices of equal rank lie in one genus.
* `TauCeti.IntegralLattice.sameGenus_e8PowLattice_checkerboardPlusLattice`: `E₈^k` and `D_{8k}⁺`
  lie in one genus.
* `TauCeti.IntegralLattice.isEmpty_isometry_e8PowLattice_checkerboardPlusLattice`: for `k ≥ 2`,
  `E₈^k` and `D_{8k}⁺` are not isometric.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter V, §1.4 and §2.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Chapter II.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 16, §1.
-/

public section

namespace TauCeti.IntegralLattice

open Module

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  {L : IntegralLattice V} {M : IntegralLattice W}

/-- **Even unimodular lattices with equal signatures lie in one genus.** Both determinants equal
`(-1) ^ n₋`. Away from `2` both localizations are unimodular of equal rank and determinant, and at
`2` even unimodular forms over `ℤ_[2]` are classified by rank and determinant square class. -/
theorem sameGenus_of_isEven_of_isUnimodular (hLe : L.IsEven) (hMe : M.IsEven)
    (hLu : L.IsUnimodular) (hMu : M.IsUnimodular) (hsig : L.signature = M.signature) :
    L.SameGenus M := by
  have : L.IsNondegenerate := ⟨hLu.nondegenerate⟩
  have : M.IsNondegenerate := ⟨hMu.nondegenerate⟩
  -- Both determinants are `(-1) ^ n₋`, since both discriminants are `1`.
  have hdet : L.determinant = M.determinant := by
    rw [L.determinant_eq_neg_one_pow_sigNeg_mul_discriminant,
      M.determinant_eq_neg_one_pow_sigNeg_mul_discriminant,
      L.isUnimodular_iff_discriminant_eq_one.mp hLu, M.isUnimodular_iff_discriminant_eq_one.mp hMu,
      show L.sigNeg = M.sigNeg from congrArg (·.2.2) hsig]
  have hL := L.isUnimodular_iff_isUnit_determinant.mp hLu
  have hM := M.isUnimodular_iff_isUnit_determinant.mp hMu
  refine (L.sameGenus_iff_localIntegralForm_equivalent_primeFactors M hdet hL.ne_zero).mpr
    ⟨hsig, fun p _ hp ↦ ?_⟩
  -- The determinant is a unit, so `2` is the only prime that needs checking.
  rw [Int.isUnit_iff_natAbs_eq.mp hL, mul_one, Nat.prime_two.primeFactors,
    Finset.mem_singleton] at hp
  subst hp
  refine (L.localIntegralForm_two_equivalent_iff_of_isEven M hLe hMe
    (hL.map (Int.castRingHom ℤ_[2])) (hM.map (Int.castRingHom ℤ_[2]))).mpr
    ⟨L.finrank_eq_of_signature_eq hsig, ?_⟩
  rw [hdet]
  exact IsSquare.mul_self _

/-- **Positive definite even unimodular lattices of equal rank lie in one genus.** -/
theorem IsPosDef.sameGenus_of_isEven_of_isUnimodular (hLp : L.IsPosDef) (hMp : M.IsPosDef)
    (hLe : L.IsEven) (hMe : M.IsEven) (hLu : L.IsUnimodular) (hMu : M.IsUnimodular)
    (hrank : finrank ℤ L = finrank ℤ M) : L.SameGenus M :=
  IntegralLattice.sameGenus_of_isEven_of_isUnimodular hLe hMe hLu hMu
    (by rw [hLp.signature_eq, hMp.signature_eq, hrank])

/-- **`E₈^k` and `D_{8k}⁺` lie in one genus**: both are positive definite, even and unimodular of
rank `8k`. -/
theorem sameGenus_e8PowLattice_checkerboardPlusLattice (k : ℕ) :
    (e8PowLattice k).SameGenus (checkerboardPlusLattice (8 * k) (dvd_mul_right 8 k)) :=
  (isPosDef_e8PowLattice k).sameGenus_of_isEven_of_isUnimodular
    (isPosDef_checkerboardPlusLattice _ _) (isEven_e8PowLattice k)
    (isEven_checkerboardPlusLattice _ _) (isUnimodular_e8PowLattice k)
    (isUnimodular_checkerboardPlusLattice _ _) (by simp)

/-- **`E₈^k` and `D_{8k}⁺` are not isometric for `k ≥ 2`.** The roots of `E₈^k` span it, while the
roots of `D_{8k}⁺` span at most `D_{8k}`. At `k = 2` these are the two even unimodular lattices
`E₈ ⊕ E₈` and `D₁₆⁺` of rank sixteen. -/
theorem isEmpty_isometry_e8PowLattice_checkerboardPlusLattice {k : ℕ} (hk : 2 ≤ k) :
    IsEmpty (Isometry (e8PowLattice k) (checkerboardPlusLattice (8 * k) (dvd_mul_right 8 k))) :=
  ⟨fun e ↦ span_vectorsOfNorm_two_checkerboardPlusLattice_ne_top _ _ (by omega)
    ((e.span_vectorsOfNorm_eq_top_iff 2).mp (span_vectorsOfNorm_two_e8PowLattice k))⟩

end TauCeti.IntegralLattice

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
import TauCeti.NumberTheory.IntegralLattice.UnimodularGenus

/-!
# The genus of even unimodular lattices

Two even unimodular lattices with equal signatures lie in one genus, by the description of the
genus of a unimodular lattice through its signature and type
(`TauCeti.IntegralLattice.sameGenus_iff_of_isUnimodular`). In particular, the positive definite
even unimodular lattices of a given rank form a single genus.

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

/-- **Even unimodular lattices with equal signatures lie in one genus.** This is the even case of
`TauCeti.IntegralLattice.sameGenus_iff_of_isUnimodular`. -/
theorem sameGenus_of_isEven_of_isUnimodular (hLe : L.IsEven) (hMe : M.IsEven)
    (hLu : L.IsUnimodular) (hMu : M.IsUnimodular) (hsig : L.signature = M.signature) :
    L.SameGenus M :=
  (sameGenus_iff_of_isUnimodular hLu hMu).mpr ⟨hsig, iff_of_true hLe hMe⟩

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

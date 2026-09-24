/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.IsSepClosed
import TauCeti.GroupTheory.FiniteAbelian.RankTwo
import TauCeti.Algebra.Group.Equiv.Pi
import TauCeti.Algebra.Module.Torsion.Basic
import TauCeti.Algebra.Module.Torsion.Decomposition
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# The finite-level torsion structure of an elliptic curve

Over a separably closed field, the `N`-torsion of an elliptic curve is a product of two cyclic
groups of order `N`, provided that `N` is invertible in the field. This identifies the finite
torsion available for studying isogenies and the Weil pairing.

## Main result

* `WeierstrassCurve.torsion_addEquiv_prod`: `E[N] ≃+ ZMod N × ZMod N`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.4(b).
-/

public section

namespace WeierstrassCurve

open scoped DirectSum

variable {K : Type*} [Field K] [IsSepClosed K]

open scoped Classical in
/-- A primary component of `E[N]` is a product of two cyclic groups of the expected order. -/
private noncomputable def primePowerComponentEquiv (W : WeierstrassCurve K) [W.IsElliptic]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (p : N.primeFactors) :
    let q := (p : ℕ) ^ N.factorization p
    Submodule.torsionBy ℤ (AddSubgroup.torsionBy W.toAffine.Point (N : ℤ)) (q : ℤ) ≃+
      ZMod q × ZMod q := by
  let G := AddSubgroup.torsionBy W.toAffine.Point (N : ℤ)
  let q := (p : ℕ) ^ N.factorization p
  have hN0 : N ≠ 0 := NeZero.ne N
  have hq_dvd : q ∣ N :=
    (Nat.prime_of_mem_primeFactors p.2).pow_dvd_iff_le_factorization hN0 |>.2 le_rfl
  have hp_dvd_q : (p : ℕ) ∣ q := by
    apply dvd_pow_self
    exact (Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors p.2) hN0
      (Nat.dvd_of_mem_primeFactors p.2)).ne'
  let : Finite G := W.finite_torsionBy (by exact_mod_cast hN0)
  let e : Submodule.torsionBy ℤ G (q : ℤ) ≃+
      AddSubgroup.torsionBy W.toAffine.Point (q : ℤ) :=
        TauCeti.AddSubgroup.torsionByTorsionByEquiv (by exact_mod_cast hq_dvd)
  have hpow (x : Submodule.torsionBy ℤ G (q : ℤ)) : q • x = 0 :=
    AddSubgroup.torsionBy.nsmul x
  have hcardq : Nat.card (Submodule.torsionBy ℤ G (q : ℤ)) = q ^ 2 := by
    rw [Nat.card_congr e.toEquiv]
    simpa only [Int.natAbs_natCast] using
      W.natCard_torsionBy (n := (q : ℤ)) (by
        exact_mod_cast ne_zero_of_dvd_ne_zero hN (Nat.cast_dvd_cast hq_dvd))
  have hcardp : Nat.card
      (AddSubgroup.torsionBy (Submodule.torsionBy ℤ G (q : ℤ)) (p : ℤ)) = p ^ 2 := by
    let ep := (AddEquiv.torsionByCongr e p).trans
      (TauCeti.AddSubgroup.torsionByTorsionByEquiv (by exact_mod_cast hp_dvd_q))
    rw [Nat.card_congr ep.toEquiv]
    simpa only [Int.natAbs_natCast] using
      W.natCard_torsionBy (n := (p : ℤ)) (by
        exact_mod_cast ne_zero_of_dvd_ne_zero hN
          (Nat.cast_dvd_cast (Nat.dvd_of_mem_primeFactors p.2)))
  have hcardq' : Nat.card (Submodule.torsionBy ℤ G (q : ℤ)) =
      p ^ (2 * N.factorization p) := by
    dsimp only [q] at hcardq ⊢
    convert hcardq using 1
    rw [← pow_mul, mul_comm]
  exact (TauCeti.AddCommGroup.nonempty_addEquiv_prod_zmod_primePow
    (Nat.prime_of_mem_primeFactors p.2) hpow hcardq' hcardp).some

open scoped Classical in
/-- The primary decomposition of `E[N]`, with each component put in rank-two cyclic form. -/
private noncomputable def primaryDecompositionEquiv (W : WeierstrassCurve K) [W.IsElliptic]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) :
    AddSubgroup.torsionBy W.toAffine.Point (N : ℤ) ≃+
      (∀ p : N.primeFactors,
        ZMod ((p : ℕ) ^ N.factorization p) × ZMod ((p : ℕ) ^ N.factorization p)) := by
  let G := AddSubgroup.torsionBy W.toAffine.Point (N : ℤ)
  let q : ℕ → ℕ := fun p ↦ p ^ N.factorization p
  let componentEquiv (p : N.primeFactors) :
      Submodule.torsionBy ℤ G (q p : ℤ) ≃+ ZMod (q p) × ZMod (q p) :=
    primePowerComponentEquiv W N hN p
  have hinternal : DirectSum.IsInternal fun p : N.primeFactors ↦
      Submodule.torsionBy ℤ G (q p : ℤ) :=
    TauCeti.AddSubgroup.torsionBy_primeFactors_isInternal N (NeZero.ne N)
  letI := hinternal.chooseDecomposition
  exact (DirectSum.decomposeAddEquiv fun p : N.primeFactors ↦
    Submodule.torsionBy ℤ G (q p : ℤ)).trans <|
    (DFinsupp.mapRange.addEquiv componentEquiv).trans (DirectSum.addEquivProd _)

open scoped Classical in
/-- **`E[N] ≃+ (ℤ/N)²`** over a separably closed field in which `N` is invertible.

The equivalence is noncanonical, so the result asserts its existence. -/
theorem torsion_addEquiv_prod (W : WeierstrassCurve K) [W.IsElliptic] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) :
    Nonempty (AddSubgroup.torsionBy W.toAffine.Point (N : ℤ) ≃+ ZMod N × ZMod N) := by
  classical
  let q : ℕ → ℕ := fun p ↦ p ^ N.factorization p
  have hN0 : N ≠ 0 := NeZero.ne N
  let primary := primaryDecompositionEquiv W N hN
  let crt : (∀ p : N.primeFactors, ZMod (q p)) ≃+ ZMod N :=
    (ZMod.equivPi (n := N) hN0).symm.toAddEquiv
  exact ⟨primary |>.trans (TauCeti.AddEquiv.arrowProdEquivProdArrow _ _) |>.trans
    (crt.prodCongr crt)⟩

end WeierstrassCurve

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.IsSepClosed
import TauCeti.GroupTheory.FiniteAbelian.RankTwo
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.QuotientRing

/-!
# The finite-level torsion structure of an elliptic curve

Over a separably closed field, the `N`-torsion of an elliptic curve is a product of two cyclic
groups of order `N`, provided that `N` is invertible in the field.  The proof first treats each
prime-power part using the structure theorem for finite abelian groups and the known torsion
counts.  The coprime parts are then reassembled by the Chinese remainder theorem.

## Main result

* `WeierstrassCurve.torsion_addEquiv_prod`: `E[N] ≃+ ZMod N × ZMod N`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.4(b).
-/

public section

namespace WeierstrassCurve

open scoped DirectSum

variable {A : Type*} [AddCommGroup A]

/-- Torsion by `a` inside the `b`-torsion subgroup is the ambient `a`-torsion when `a ∣ b`. -/
private def torsionByTorsionByEquiv {a b : ℕ} (hab : a ∣ b) :
    AddSubgroup.torsionBy (AddSubgroup.torsionBy A (b : ℤ)) (a : ℤ) ≃+
      AddSubgroup.torsionBy A (a : ℤ) := by
  have ha (x : AddSubgroup.torsionBy A (a : ℤ)) : a • (x.1 : A) = 0 := by
    have hx := (Submodule.mem_torsionBy_iff _ _).mp x.2
    rwa [natCast_zsmul] at hx
  exact
    { toFun := fun x ↦ ⟨x.1.1, AddSubgroup.torsionBy.nsmul_iff.2 <| by
          have hx := (Submodule.mem_torsionBy_iff _ _).mp x.2
          rw [natCast_zsmul] at hx
          exact congrArg Subtype.val hx⟩
      invFun := fun x ↦
        ⟨⟨x.1, AddSubgroup.torsionBy.nsmul_iff.2 <| by
            obtain ⟨c, rfl⟩ := hab
            calc
              (a * c) • (x.1 : A) = c • (a • (x.1 : A)) := by rw [mul_nsmul]
              _ = 0 := by simp only [ha x, nsmul_zero]⟩,
          AddSubgroup.torsionBy.nsmul_iff.2 <| Subtype.ext <| ha x⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }

/-- An additive equivalence carries the `n`-torsion subgroup to the `n`-torsion subgroup. -/
private def torsionByCongr {B : Type*} [AddCommGroup B] (e : A ≃+ B) (n : ℕ) :
    AddSubgroup.torsionBy A (n : ℤ) ≃+ AddSubgroup.torsionBy B (n : ℤ) where
  toFun x := ⟨e x, AddSubgroup.torsionBy.nsmul_iff.2 <| by
    have hx := (Submodule.mem_torsionBy_iff _ _).mp x.2
    rw [natCast_zsmul] at hx
    calc
      n • e x = e (n • (x.1 : A)) := (map_nsmul e n x.1).symm
      _ = e 0 := congrArg e hx
      _ = 0 := map_zero e⟩
  invFun x := ⟨e.symm x, AddSubgroup.torsionBy.nsmul_iff.2 <| by
    have hx := (Submodule.mem_torsionBy_iff _ _).mp x.2
    rw [natCast_zsmul] at hx
    calc
      n • e.symm x = e.symm (n • (x.1 : B)) := (map_nsmul e.symm n x.1).symm
      _ = e.symm 0 := congrArg e.symm hx
      _ = 0 := map_zero e.symm⟩
  left_inv x := Subtype.ext (e.left_inv x)
  right_inv x := Subtype.ext (e.right_inv x)
  map_add' _ _ := Subtype.ext (e.map_add _ _)

/-- Functions into products are additively equivalent to products of function spaces. -/
private def piProdAddEquiv {ι : Type*} (B C : ι → Type*)
    [∀ i, AddCommGroup (B i)] [∀ i, AddCommGroup (C i)] :
    (∀ i, B i × C i) ≃+ (∀ i, B i) × (∀ i, C i) :=
  { Equiv.arrowProdEquivProdArrow ι B C with map_add' := fun _ _ ↦ rfl }

variable {K : Type*} [Field K] [IsSepClosed K]

omit [IsSepClosed K] in
/-- A divisor of a nonzero field element is nonzero. -/
private theorem natCast_ne_zero_of_dvd {N d : ℕ} (hN : (N : K) ≠ 0) (hd : d ∣ N) :
    (d : K) ≠ 0 := by
  obtain ⟨c, rfl⟩ := hd
  contrapose! hN
  rw [Nat.cast_mul, hN, zero_mul]

open scoped Classical in
/-- The known geometric torsion count, transported across base change by the identity map. -/
private theorem natCard_torsionBy_self (W : WeierstrassCurve K) [W.IsElliptic]
    {N d : ℕ} (hN : (N : K) ≠ 0) (hd : d ∣ N) :
    Nat.card (AddSubgroup.torsionBy W.toAffine.Point (d : ℤ)) = d ^ 2 := by
  let eSelf : (W.toAffine⁄K).toAffine.Point ≃+ W.toAffine.Point :=
    AddEquiv.cast (M := fun V : Affine K ↦ V.Point) W.toAffine.baseChange_self
  rw [← Nat.card_congr (torsionByCongr eSelf d).toEquiv]
  simpa only [Int.natAbs_natCast] using W.toAffine.natCard_torsionBy (n := (d : ℤ)) (by
    exact_mod_cast natCast_ne_zero_of_dvd hN hd)

open scoped Classical in
omit [IsSepClosed K] in
/-- The torsion subgroup over the original field is finite, by transport from identity base
change. -/
private theorem finite_torsionBy_self (W : WeierstrassCurve K) [W.IsElliptic]
    {d : ℕ} (hd : d ≠ 0) : Finite (AddSubgroup.torsionBy W.toAffine.Point (d : ℤ)) := by
  let eSelf : (W.toAffine⁄K).toAffine.Point ≃+ W.toAffine.Point :=
    AddEquiv.cast (M := fun V : Affine K ↦ V.Point) W.toAffine.baseChange_self
  let : Finite (AddSubgroup.torsionBy (W.toAffine⁄K).toAffine.Point (d : ℤ)) :=
    W.toAffine.finite_torsionBy (n := (d : ℤ)) (by exact_mod_cast hd)
  exact Finite.of_equiv _ (torsionByCongr eSelf d).toEquiv

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
  let : Finite G := finite_torsionBy_self W hN0
  let e : Submodule.torsionBy ℤ G (q : ℤ) ≃+
      AddSubgroup.torsionBy W.toAffine.Point (q : ℤ) := torsionByTorsionByEquiv hq_dvd
  have hpow (x : Submodule.torsionBy ℤ G (q : ℤ)) : q • x = 0 :=
    AddSubgroup.torsionBy.nsmul x
  have hcardq : Nat.card (Submodule.torsionBy ℤ G (q : ℤ)) = q ^ 2 := by
    rw [Nat.card_congr e.toEquiv]
    exact natCard_torsionBy_self W hN hq_dvd
  have hcardp : Nat.card
      (AddSubgroup.torsionBy (Submodule.torsionBy ℤ G (q : ℤ)) (p : ℤ)) = p ^ 2 := by
    let ep := (torsionByCongr e p).trans (torsionByTorsionByEquiv hp_dvd_q)
    rw [Nat.card_congr ep.toEquiv]
    exact natCard_torsionBy_self W hN (Nat.dvd_of_mem_primeFactors p.2)
  have hcardq' : Nat.card (Submodule.torsionBy ℤ G (q : ℤ)) =
      p ^ (2 * N.factorization p) := by
    dsimp only [q] at hcardq ⊢
    convert hcardq using 1
    rw [← pow_mul, mul_comm]
  exact (AddCommGroup.nonempty_addEquiv_prod_zmod_primePow
    (Nat.prime_of_mem_primeFactors p.2) hpow hcardq' hcardp).some

open scoped Classical in
/-- Distinct primary powers in a factorization are coprime over the integers. -/
private theorem primePowerCoprimeInt (N : ℕ) : (N.primeFactors : Set ℕ).Pairwise
    (Function.onFun IsCoprime fun p ↦ ((p ^ N.factorization p : ℕ) : ℤ)) := by
  intro p hp r hr hpr
  exact (Nat.Coprime.cast <| N.pairwise_coprime_pow_primeFactors_factorization
    (show (⟨p, hp⟩ : N.primeFactors) ≠ ⟨r, hr⟩ by
      intro h
      exact hpr (congrArg Subtype.val h)))

open scoped Classical in
/-- The product of the integer primary powers is the original nonzero natural number. -/
private theorem prodPrimePowerInt {N : ℕ} (hN : N ≠ 0) :
    ∏ p ∈ N.primeFactors, (((p ^ N.factorization p : ℕ) : ℤ)) = (N : ℤ) := by
  exact_mod_cast (Nat.prod_primeFactors_pow_factorization hN).symm

open scoped Classical in
omit [IsSepClosed K] in
/-- The primary torsion subgroups form an internal direct sum of `E[N]`. -/
private theorem torsionPrimaryIsInternal (W : WeierstrassCurve K) [W.IsElliptic]
    (N : ℕ) [NeZero N] : DirectSum.IsInternal fun p : N.primeFactors ↦
    Submodule.torsionBy ℤ (AddSubgroup.torsionBy W.toAffine.Point (N : ℤ))
      ((p ^ N.factorization p : ℕ) : ℤ) := by
  have hN0 : N ≠ 0 := NeZero.ne N
  apply Submodule.torsionBy_isInternal (primePowerCoprimeInt N)
  rw [prodPrimePowerInt hN0]
  change Module.IsTorsionBy ℤ (AddSubgroup.torsionBy W.toAffine.Point (N : ℤ)) (N : ℤ)
  exact Submodule.torsionBy_isTorsionBy (R := ℤ) (M := W.toAffine.Point) (N : ℤ)

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
      Submodule.torsionBy ℤ G (q p : ℤ) := torsionPrimaryIsInternal W N
  letI := hinternal.chooseDecomposition
  exact (DirectSum.decomposeAddEquiv fun p : N.primeFactors ↦
    Submodule.torsionBy ℤ G (q p : ℤ)).trans <|
    (DFinsupp.mapRange.addEquiv componentEquiv).trans (DirectSum.addEquivProd _)

open scoped Classical in
/-- **`E[N] ≃+ (ℤ/N)²`** over a separably closed field in which `N` is invertible.

The equivalence is noncanonical: on each primary component it comes from the finite abelian group
structure theorem, and the primary components are assembled using the Chinese remainder theorem.
-/
theorem torsion_addEquiv_prod (W : WeierstrassCurve K) [W.IsElliptic] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) :
    Nonempty (AddSubgroup.torsionBy W.toAffine.Point (N : ℤ) ≃+ ZMod N × ZMod N) := by
  classical
  let q : ℕ → ℕ := fun p ↦ p ^ N.factorization p
  have hN0 : N ≠ 0 := NeZero.ne N
  let primary := primaryDecompositionEquiv W N hN
  let crt : (∀ p : N.primeFactors, ZMod (q p)) ≃+ ZMod N :=
    (ZMod.equivPi (n := N) hN0).symm.toAddEquiv
  exact ⟨primary |>.trans (piProdAddEquiv _ _) |>.trans (crt.prodCongr crt)⟩

end WeierstrassCurve

end

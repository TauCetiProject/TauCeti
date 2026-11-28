/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Torsion
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.ZMod
import TauCeti.Data.Nat.Pow
import TauCeti.GroupTheory.Torsion
import TauCeti.LinearAlgebra.Matrix.IdealEntries
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.RingTheory.AdicCompletion.Pi
import TauCeti.RingTheory.RootsOfUnity.Congruence

/-!
# Torsion in congruence kernels of the general linear group

If a commutative ring `R` is `ℓ`-adically separated and has no `ℓ`-torsion, for a prime
`ℓ`, then invertible matrices congruent to `1` modulo any power `ℓ ^ k ≥ 3` have infinite order
unless they are `1`. Over `ℤ` this gives Minkowski's lemma for every modulus `m ≥ 3`. In
particular, reduction modulo such an `m` is injective on every finite subgroup of `GL n ℤ`.
The bound on the modulus is sharp: `-1 ∈ GL 1 ℤ` has order `2` and reduces to `1` modulo `2`.

## Main results

* `Matrix.isLeftRegular_scalar`, `Matrix.eq_zero_of_forall_scalar_pow_dvd`: regularity and
  `r`-adic separatedness of `R` pass to the scalar matrix `r` in `Matrix n n R`.
* `Matrix.GeneralLinearGroup.isMulTorsionFree_ker_map`: if `φ : R →+* S` has kernel contained in
  `ℓ ^ k R` for a prime power `ℓ ^ k ≥ 3`, the induced kernel on `GL n R` is torsion-free under
  the regularity and separatedness hypotheses above.
* `Matrix.GeneralLinearGroup.domRestrict_map_injective`,
  `Matrix.GeneralLinearGroup.natCard_le_natCard_map`: under the same hypotheses,
  `GL n R → GL n S` is injective on every torsion subgroup. If `GL n S` is finite, its cardinality
  bounds `Nat.card G` for every subgroup `G` of `GL n R`. For finite `G`, this bounds its size.
* `Matrix.GeneralLinearGroup.isMulTorsionFree_ker_map_toZModPow`,
  `Matrix.GeneralLinearGroup.domRestrict_map_toZModPow_injective`: reduction of `GL n ℤ_[p]`
  modulo `p ^ k ≥ 3` has torsion-free kernel and is injective on torsion subgroups.
* `Matrix.GeneralLinearGroup.isMulTorsionFree_ker_map_toZMod`,
  `Matrix.GeneralLinearGroup.domRestrict_map_toZMod_injective`: for an odd prime `p`, reduction
  `GL n ℤ_[p] → GL n (ZMod p)` has torsion-free kernel and is injective on torsion subgroups.
* `Matrix.GeneralLinearGroup.eq_one_of_isOfFinOrder_of_map_intCast_eq_one`:
  Minkowski's lemma for every modulus `m ≥ 3`.
* `Matrix.GeneralLinearGroup.isMulTorsionFree_ker_map_intCast` and
  `Matrix.GeneralLinearGroup.domRestrict_map_intCast_injective`: the corresponding
  torsion-free kernel and injectivity on torsion subgroups.
* `Matrix.GeneralLinearGroup.natCard_le_natCard_zmod`: for `m ≥ 3`, the cardinality of
  `GL n (ZMod m)` bounds `Nat.card G` for every subgroup `G` of `GL n ℤ`, and hence the size of
  each finite subgroup.

## Implementation notes

Torsion-freeness of the congruence kernel is Serre's lemma
`TauCeti.eq_one_of_isOfFinOrder_of_pow_dvd_sub_one`, applied in the matrix ring `Matrix n n R`
with `ℓ ^ k ≥ 3`. The integer case uses `ZMod.ker_intCastRingHom` and
`Nat.exists_prime_pow_dvd_of_three_le`. The p-adic case uses `PadicInt.ker_toZModPow` and
`PadicInt.ker_toZMod`.

## References

* H. Minkowski, *Zur Theorie der positiven quadratischen Formen*, J. Reine Angew. Math. 101 (1887),
  196–202.
* J.-P. Serre, *Bounds for the orders of the finite subgroups of G(k)*, arXiv:1011.0346,
  §1.2, Lemma 1.
* D. Huybrechts, *Lectures on K3 surfaces*, Cambridge Stud. Adv. Math. 158, Chapter 17, proof of
  Lemma 2.6.
-/

public section

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- Left multiplication by the scalar matrix `r` is injective when multiplication by `r` is
injective on `R`. -/
theorem isLeftRegular_scalar {r : R} (h : IsSMulRegular R r) : IsLeftRegular (scalar n r) :=
  fun x y hxy ↦ h.matrix (by simpa only [scalar_apply, ← smul_eq_diagonal_mul] using hxy)

/-- If `R` is `r`-adically separated, the only matrix over `R` divisible by every power of the
scalar matrix `r` is `0`. -/
theorem eq_zero_of_forall_scalar_pow_dvd {r : R} (h : IsHausdorff (Ideal.span {r}) R)
    {x : Matrix n n R} (hx : ∀ k : ℕ, scalar n r ^ k ∣ x) : x = 0 := by
  have := h
  refine Matrix.ext fun i j ↦ congrFun (TauCeti.eq_zero_of_forall_pow_dvd r fun k j ↦ ?_) j
  obtain ⟨z, rfl⟩ := hx k
  rw [← map_pow, scalar_apply, ← smul_eq_diagonal_mul]
  exact Dvd.intro _ rfl

end Matrix

namespace Matrix.GeneralLinearGroup

variable {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]

/-- Let `ℓ` be prime and `R` an `ℓ`-adically separated commutative ring with no `ℓ`-torsion.
If the kernel of `φ : R →+* S` is contained in `ℓ ^ k R`, where `ℓ ^ k ≥ 3`, then the kernel
of the induced map on general linear groups is torsion-free. -/
theorem isMulTorsionFree_ker_map {ℓ k : ℕ} (hℓ : ℓ.Prime) (hk : 3 ≤ ℓ ^ k)
    (hreg : IsSMulRegular R (ℓ : R)) (hsep : IsHausdorff (Ideal.span {(ℓ : R)}) R) (φ : R →+* S)
    (hφ : RingHom.ker φ ≤ Ideal.span {((ℓ : R) ^ k)}) :
    IsMulTorsionFree (map (n := n) φ).ker := by
  refine IsMulTorsionFree.of_not_isOfFinOrder ?_
  rintro ⟨g, hg⟩ hne hfin
  refine hne ?_
  have hgφ : (g : Matrix n n R).map φ = 1 := by
    simpa only [Units.ext_iff, ← Matrix.ext_iff, Matrix.map_apply,
      Matrix.GeneralLinearGroup.map_apply, Units.val_one]
      using MonoidHom.mem_ker.mp hg
  have hgφ' : ((g : Matrix n n R) - 1).map φ = 0 := by
    rw [← RingHom.mapMatrix_apply, map_sub, map_one]
    exact sub_eq_zero.mpr ((RingHom.mapMatrix_apply _ _).trans hgφ)
  have hg1 : (ℓ : Matrix n n R) ^ k ∣ (g : Matrix n n R) - 1 := by
    simpa only [map_pow, map_natCast] using Matrix.scalar_dvd_of_map_eq_zero hφ hgφ'
  refine Subtype.ext (Units.ext (TauCeti.eq_one_of_isOfFinOrder_of_pow_dvd_sub_one hℓ ?_ ?_ hk
    (Units.isOfFinOrder_val.mpr ((Subgroup.subtype _).isOfFinOrder hfin)) hg1))
  · simpa using Matrix.isLeftRegular_scalar (n := n) hreg
  · exact fun _ hx ↦ Matrix.eq_zero_of_forall_scalar_pow_dvd hsep (by simpa using hx)

/-- Under the hypotheses of
`Matrix.GeneralLinearGroup.isMulTorsionFree_ker_map`, the map `GL n R → GL n S` induced by `φ` is
injective on every torsion subgroup of `GL n R`. -/
theorem domRestrict_map_injective {ℓ k : ℕ} (hℓ : ℓ.Prime) (hk : 3 ≤ ℓ ^ k)
    (hreg : IsSMulRegular R (ℓ : R)) (hsep : IsHausdorff (Ideal.span {(ℓ : R)}) R) (φ : R →+* S)
    (hφ : RingHom.ker φ ≤ Ideal.span {((ℓ : R) ^ k)}) (G : Subgroup (GL n R))
    (hG : IsMulTorsion G) : Function.Injective ((map φ).domRestrict G) :=
  have := isMulTorsionFree_ker_map (n := n) hℓ hk hreg hsep φ hφ
  (map φ).injective_domRestrict_of_isMulTorsion hG

/-- Under the hypotheses of `Matrix.GeneralLinearGroup.isMulTorsionFree_ker_map`, if `GL n S`
is finite, its cardinality bounds `Nat.card G` for every subgroup `G` of `GL n R`, and hence
the size of each finite subgroup. -/
theorem natCard_le_natCard_map {ℓ k : ℕ} (hℓ : ℓ.Prime) (hk : 3 ≤ ℓ ^ k)
    (hreg : IsSMulRegular R (ℓ : R)) (hsep : IsHausdorff (Ideal.span {(ℓ : R)}) R) (φ : R →+* S)
    (hφ : RingHom.ker φ ≤ Ideal.span {((ℓ : R) ^ k)}) [Finite (GL n S)] (G : Subgroup (GL n R)) :
    Nat.card G ≤ Nat.card (GL n S) :=
  have := isMulTorsionFree_ker_map (n := n) hℓ hk hreg hsep φ hφ
  (map φ).natCard_le_of_isMulTorsionFree_ker G

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- For a prime `p` and `p ^ k ≥ 3`, the kernel of reduction
`GL n ℤ_[p] → GL n (ZMod (p ^ k))` is torsion-free. -/
theorem isMulTorsionFree_ker_map_toZModPow {k : ℕ} (hk : 3 ≤ p ^ k) :
    IsMulTorsionFree (map (n := n) (PadicInt.toZModPow (p := p) k)).ker :=
  have hp : p.Prime := Fact.out
  isMulTorsionFree_ker_map hp hk (.of_ne_zero (by exact_mod_cast hp.ne_zero))
    inferInstance _ (PadicInt.ker_toZModPow k).le

/-- For a prime `p` and `p ^ k ≥ 3`, reduction `GL n ℤ_[p] → GL n (ZMod (p ^ k))`
is injective on every torsion subgroup. -/
theorem domRestrict_map_toZModPow_injective {k : ℕ} (hk : 3 ≤ p ^ k)
    (G : Subgroup (GL n ℤ_[p])) (hG : IsMulTorsion G) :
    Function.Injective ((map (PadicInt.toZModPow k)).domRestrict G) :=
  have := isMulTorsionFree_ker_map_toZModPow (n := n) hk
  (map _).injective_domRestrict_of_isMulTorsion hG

/-- **The first congruence subgroup of `GL n ℤ_[p]` is torsion-free** for an odd prime `p`: the
kernel of reduction `GL n ℤ_[p] → GL n (ZMod p)` has no nontrivial element of finite order. -/
theorem isMulTorsionFree_ker_map_toZMod (hp : Odd p) :
    IsMulTorsionFree (map (n := n) (PadicInt.toZMod : ℤ_[p] →+* ZMod p)).ker := by
  have hprime : p.Prime := Fact.out
  have hlevel : 3 ≤ p ^ 1 := by simpa only [pow_one] using hprime.odd_iff.mp hp
  refine isMulTorsionFree_ker_map hprime hlevel
    (.of_ne_zero (by exact_mod_cast hprime.ne_zero)) inferInstance _ ?_
  rw [pow_one, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p]

/-- For an odd prime `p`, reduction `GL n ℤ_[p] → GL n (ZMod p)` is injective on every
torsion subgroup. -/
theorem domRestrict_map_toZMod_injective (hp : Odd p) (G : Subgroup (GL n ℤ_[p]))
    (hG : IsMulTorsion G) :
    Function.Injective ((map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)).domRestrict G) :=
  have := isMulTorsionFree_ker_map_toZMod (n := n) hp
  (map _).injective_domRestrict_of_isMulTorsion hG

end Padic

section Int

/-- The kernel of reduction `GL n ℤ → GL n (ZMod m)` is torsion-free for every `m ≥ 3`. -/
theorem isMulTorsionFree_ker_map_intCast {m : ℕ} (hm : 3 ≤ m) :
    IsMulTorsionFree (map (n := n) (Int.castRingHom (ZMod m))).ker := by
  obtain ⟨p, k, hp, hpk, hdvd⟩ := Nat.exists_prime_pow_dvd_of_three_le hm
  refine isMulTorsionFree_ker_map hp hpk (.of_ne_zero (by exact_mod_cast hp.ne_zero))
    (.of_isDomain _ (by
      rw [Ne, Ideal.span_singleton_eq_top, Int.isUnit_iff]
      have := hp.two_le
      omega)) _ ?_
  rw [ZMod.ker_intCastRingHom, Ideal.span_singleton_le_span_singleton]
  exact_mod_cast hdvd

/-- **Minkowski's lemma.** An element of finite order in `GL n ℤ` that is congruent to the
identity modulo `m ≥ 3` is the identity. See Serre, §1.2, Lemma 1. -/
theorem eq_one_of_isOfFinOrder_of_map_intCast_eq_one {m : ℕ} (hm : 3 ≤ m)
    {g : GL n ℤ} (hg : IsOfFinOrder g) (h : map (Int.castRingHom (ZMod m)) g = 1) :
    g = 1 := by
  have := isMulTorsionFree_ker_map_intCast (n := n) hm
  let K := (map (n := n) (Int.castRingHom (ZMod m))).ker
  let x : K := ⟨g, MonoidHom.mem_ker.mpr h⟩
  have hxg : K.subtype x = g := by simp only [Subgroup.coe_subtype, x]
  have hx : IsOfFinOrder x := K.subtype_injective.isOfFinOrder_iff.mp (hxg.symm ▸ hg)
  exact hxg.symm.trans ((congrArg K.subtype hx.eq_one').trans (map_one K.subtype))

/-- Reduction modulo `m ≥ 3` is injective on every torsion subgroup of `GL n ℤ`. -/
theorem domRestrict_map_intCast_injective {m : ℕ} (hm : 3 ≤ m)
    (G : Subgroup (GL n ℤ)) (hG : IsMulTorsion G) :
    Function.Injective ((map (Int.castRingHom (ZMod m))).domRestrict G) :=
  have := isMulTorsionFree_ker_map_intCast (n := n) hm
  (map _).injective_domRestrict_of_isMulTorsion hG

/-- For `m ≥ 3`, the cardinality of `GL n (ZMod m)` bounds `Nat.card G` for every subgroup
`G` of `GL n ℤ`. For finite `G` this bounds its size, since reduction embeds it into
`GL n (ZMod m)`. -/
theorem natCard_le_natCard_zmod {m : ℕ} (hm : 3 ≤ m) {G : Subgroup (GL n ℤ)} :
    Nat.card G ≤ Nat.card (GL n (ZMod m)) :=
  have : NeZero m := NeZero.of_pos (by lia)
  have := isMulTorsionFree_ker_map_intCast (n := n) hm
  (map (Int.castRingHom (ZMod m))).natCard_le_of_isMulTorsionFree_ker G

/-- The threshold `m ≥ 3` is sharp. At level two the kernel contains `-1`, of order `2`, as
soon as `n` is nonempty. -/
theorem not_isMulTorsionFree_ker_map_intCast_two [Nonempty n] :
    ¬IsMulTorsionFree (map (n := n) (Int.castRingHom (ZMod 2))).ker := by
  rw [not_isMulTorsionFree_iff_isOfFinOrder]
  refine ⟨⟨-1, ?_⟩, ?_, isOfFinOrder_iff_pow_eq_one.mpr ⟨2, two_pos, by ext1; simp⟩⟩
  · rw [MonoidHom.mem_ker]
    ext i j
    by_cases h : i = j <;> simp [h]
  · intro h
    have := congrArg (fun g : (map (n := n) (Int.castRingHom (ZMod 2))).ker ↦
      ((g : GL n ℤ) : Matrix n n ℤ) (Classical.arbitrary n) (Classical.arbitrary n)) h
    simp at this

end Int

end Matrix.GeneralLinearGroup

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
import Mathlib.Data.Nat.Factors
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.ZMod
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
  `GL n R → GL n S` is injective on every torsion subgroup. In particular, if `GL n S` is finite,
  a finite subgroup of `GL n R` has at most `|GL n S|` elements.
* `Matrix.GeneralLinearGroup.isMulTorsionFree_ker_map_toZMod`,
  `Matrix.GeneralLinearGroup.injective_domRestrict_map_toZMod`: the first congruence subgroup of
  `GL n ℤ_[ℓ]` is torsion-free, and reduction `GL n ℤ_[ℓ] → GL n (ZMod ℓ)` is injective on every
  finite subgroup.
* `Matrix.GeneralLinearGroup.eq_one_of_isOfFinOrder_of_map_intCast_eq_one`:
  Minkowski's lemma for every modulus `m ≥ 3`.
* `Matrix.GeneralLinearGroup.isMulTorsionFree_ker_map_intCast` and
  `Matrix.GeneralLinearGroup.domRestrict_map_intCast_injective`: the corresponding
  torsion-free kernel and injectivity on torsion subgroups.
* `Matrix.GeneralLinearGroup.natCard_le_natCard_zmod_three`: a finite subgroup of `GL n ℤ` has at
  most `|GL n (ZMod 3)|` elements.

## Implementation notes

Torsion-freeness of the congruence kernel is Serre's lemma
`TauCeti.eq_one_of_isOfFinOrder_of_pow_dvd_sub_one`, applied in the matrix ring `Matrix n n R`
with `ℓ ^ k ≥ 3`. The integer case uses `ZMod.ker_intCastRingHom`: every `m ≥ 3` is
divisible by an odd prime or is a power of `2` greater than or equal to `4`.

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
  have hgφ : (g : Matrix n n R).map φ = 1 := Matrix.ext fun i j ↦ by
    simpa only [Matrix.map_apply, Matrix.GeneralLinearGroup.map_apply, Units.val_one]
      using congrArg (fun u : GL n S ↦ (u : Matrix n n S) i j) (MonoidHom.mem_ker.mp hg)
  have hgφ' : ((g : Matrix n n R) - 1).map φ = 0 := by
    rw [← RingHom.mapMatrix_apply, map_sub, map_one]
    exact sub_eq_zero.mpr ((RingHom.mapMatrix_apply _ _).trans hgφ)
  have hg1 : (ℓ : Matrix n n R) ^ k ∣ (g : Matrix n n R) - 1 := by
    let I : Ideal R := Ideal.span {((ℓ : R) ^ k)}
    have hzero : ((g : Matrix n n R) - 1).map (Ideal.Quotient.mk I) = 0 :=
      Matrix.forall_mem_ker_iff_map_eq_zero.mp fun i j ↦ by
        rw [Ideal.mk_ker]
        exact hφ (Matrix.forall_mem_ker_iff_map_eq_zero.mpr hgφ' i j)
    obtain ⟨Y, hY⟩ := (Matrix.map_eq_zero_iff_exists_eq_smul (Ideal.mk_ker (I := I))).mp hzero
    have hscalar : Matrix.scalar n ((ℓ : R) ^ k) = (ℓ : Matrix n n R) ^ k := by
      rw [map_pow, map_natCast]
    exact ⟨Y, by rw [hY, ← hscalar, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]⟩
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
is finite then a finite subgroup of `GL n R` has at most `|GL n S|` elements. -/
theorem natCard_le_natCard_map {ℓ k : ℕ} (hℓ : ℓ.Prime) (hk : 3 ≤ ℓ ^ k)
    (hreg : IsSMulRegular R (ℓ : R)) (hsep : IsHausdorff (Ideal.span {(ℓ : R)}) R) (φ : R →+* S)
    (hφ : RingHom.ker φ ≤ Ideal.span {((ℓ : R) ^ k)}) [Finite (GL n S)] (G : Subgroup (GL n R)) :
    Nat.card G ≤ Nat.card (GL n S) := by
  cases finite_or_infinite G with
  | inl _ =>
    exact Nat.card_le_card_of_injective _
      (domRestrict_map_injective hℓ hk hreg hsep φ hφ G isMulTorsion_of_finite)
  | inr _ => simp

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- **The first congruence subgroup of `GL n ℤ_[p]` is torsion-free** for an odd prime `p`: the
kernel of reduction `GL n ℤ_[p] → GL n (ZMod p)` has no nontrivial element of finite order. -/
theorem isMulTorsionFree_ker_map_toZMod (hp : Odd p) :
    IsMulTorsionFree (map (n := n) (PadicInt.toZMod : ℤ_[p] →+* ZMod p)).ker := by
  have hprime : p.Prime := Fact.out
  have hlevel : 3 ≤ p ^ 1 := by
    have := hprime.two_le
    obtain ⟨a, ha⟩ := hp
    simp only [pow_one]
    omega
  refine isMulTorsionFree_ker_map hprime hlevel
    (.of_ne_zero (by exact_mod_cast hprime.ne_zero)) inferInstance _ ?_
  rw [pow_one, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p]

/-- **Finite subgroups of `GL n ℤ_[p]` inject modulo `p`** for an odd prime `p`: reduction
`GL n ℤ_[p] → GL n (ZMod p)` is injective on every finite subgroup. -/
theorem injective_domRestrict_map_toZMod (hp : Odd p) (G : Subgroup (GL n ℤ_[p])) [Finite G] :
    Function.Injective ((map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)).domRestrict G) :=
  have := isMulTorsionFree_ker_map_toZMod (n := n) hp
  (map _).injective_domRestrict_of_isMulTorsion isMulTorsion_of_finite

end Padic

section Int

/-- The kernel of reduction `GL n ℤ → GL n (ZMod m)` is torsion-free for every `m ≥ 3`. -/
theorem isMulTorsionFree_ker_map_intCast {m : ℕ} (hm : 3 ≤ m) :
    IsMulTorsionFree (map (n := n) (Int.castRingHom (ZMod m))).ker := by
  obtain ⟨p, k, hp, hpk, hdvd⟩ : ∃ p k : ℕ, p.Prime ∧ 3 ≤ p ^ k ∧ p ^ k ∣ m := by
    by_cases h : ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ 3 ≤ p
    · obtain ⟨p, hp, hpm, hp3⟩ := h
      exact ⟨p, 1, hp, by simpa only [pow_one] using hp3, by simpa only [pow_one] using hpm⟩
    · have hm₂ : m = 2 ^ m.primeFactorsList.length :=
        Nat.eq_prime_pow_of_unique_prime_dvd (by omega) fun {p} hp hpm ↦ by
          have := hp.two_le
          have : ¬3 ≤ p := fun hp3 ↦ h ⟨p, hp, hpm, hp3⟩
          omega
      exact ⟨2, m.primeFactorsList.length, Nat.prime_two, hm₂ ▸ hm, hm₂ ▸ dvd_rfl⟩
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
  have hfin : IsOfFinOrder (⟨g, MonoidHom.mem_ker.mpr h⟩ :
      (map (Int.castRingHom (ZMod m))).ker) := Submonoid.isOfFinOrder_coe.mp hg
  exact congrArg Subtype.val hfin.eq_one'

/-- Reduction modulo `m ≥ 3` is injective on every torsion subgroup of `GL n ℤ`. -/
theorem domRestrict_map_intCast_injective {m : ℕ} (hm : 3 ≤ m)
    (G : Subgroup (GL n ℤ)) (hG : IsMulTorsion G) :
    Function.Injective ((map (Int.castRingHom (ZMod m))).domRestrict G) :=
  have := isMulTorsionFree_ker_map_intCast (n := n) hm
  (map _).injective_domRestrict_of_isMulTorsion hG

/-- A finite subgroup of `GL n ℤ` has at most `|GL n (ZMod 3)|` elements, since it embeds into
`GL n (ZMod 3)` by reduction. -/
theorem natCard_le_natCard_zmod_three {G : Subgroup (GL n ℤ)} :
    Nat.card G ≤ Nat.card (GL n (ZMod 3)) := by
  cases finite_or_infinite G with
  | inl _ =>
    exact Nat.card_le_card_of_injective _
      (domRestrict_map_intCast_injective (m := 3) le_rfl G isMulTorsion_of_finite)
  | inr _ => simp

/-- Oddness is needed: the kernel of `GL n ℤ → GL n (ZMod 2)` contains `-1`, of order `2`, as soon
as `n` is nonempty. -/
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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.ZMod
import TauCeti.GroupTheory.Torsion
import TauCeti.RingTheory.AdicCompletion.Pi
import TauCeti.RingTheory.RootsOfUnity.Congruence

/-!
# Finite subgroups of `GL n` inject modulo an odd prime

Let `ℓ` be an odd prime and `R` a commutative ring in which `ℓ` is a non-zero-divisor and which is
`ℓ`-adically separated, such as `ℤ` or `ℤ_[ℓ]`. An invertible matrix over `R` that is congruent
to `1` modulo `ℓ` and is not `1` has infinite order. Equivalently, the kernel of reduction modulo
`ℓ` on `GL n R` is torsion-free, so reduction modulo `ℓ` is injective on every finite subgroup of
`GL n R`. For `R = ℤ` and `ℓ = 3`, every finite subgroup of `GL n ℤ` embeds into `GL n (ZMod 3)`.
This bounds, for instance, the finite image of a Galois group acting on a lattice of rank `n` by
`|GL n (ZMod 3)|`.

The prime `2` is excluded: `-1 ∈ GL 1 ℤ` reduces to `1` modulo `2` and has order `2`
(`Matrix.GeneralLinearGroup.not_isMulTorsionFree_ker_map_intCast_two`).

## Main results

* `Matrix.isLeftRegular_scalar`, `Matrix.eq_zero_of_forall_scalar_pow_dvd`: regularity and
  `r`-adic separatedness of `R` pass to the scalar matrix `r` in `Matrix n n R`.
* `Matrix.GeneralLinearGroup.isMulTorsionFree_ker_map`: if `φ : R →+* S` has kernel contained in
  `ℓ R`, the kernel of `GL n R → GL n S` is torsion-free.
* `Matrix.GeneralLinearGroup.injective_domRestrict_map`,
  `Matrix.GeneralLinearGroup.natCard_le_natCard_map`: under the same hypotheses,
  `GL n R → GL n S` is injective on every finite subgroup, which therefore has at most
  `|GL n S|` elements.
* `Matrix.GeneralLinearGroup.isMulTorsionFree_ker_map_toZMod`,
  `Matrix.GeneralLinearGroup.injective_domRestrict_map_toZMod`: the first congruence subgroup of
  `GL n ℤ_[ℓ]` is torsion-free, and reduction `GL n ℤ_[ℓ] → GL n (ZMod ℓ)` is injective on every
  finite subgroup.
* `Matrix.GeneralLinearGroup.isMulTorsionFree_ker_map_intCast`,
  `Matrix.GeneralLinearGroup.injective_domRestrict_map_intCast`: for an odd prime `p`, the kernel
  of reduction `GL n ℤ → GL n (ZMod p)` is torsion-free, and the reduction is injective on every
  finite subgroup.
* `Matrix.GeneralLinearGroup.natCard_le_natCard_zmod_three`: a finite subgroup of `GL n ℤ` has at
  most `|GL n (ZMod 3)|` elements.

## Implementation notes

Torsion-freeness of the congruence kernel is Serre's lemma
`TauCeti.eq_one_of_isOfFinOrder_of_pow_dvd_sub_one`, applied in the matrix ring `Matrix n n R`
with `k = 1`; this is where `ℓ ≥ 3` is used.

## References

* H. Minkowski, *Zur Theorie der positiven quadratischen Formen*, J. Reine Angew. Math. 101 (1887),
  196–202.
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

/-- **The congruence kernel is torsion-free.** Let `ℓ` be an odd prime and `R` a commutative ring
in which `ℓ` is a non-zero-divisor and which is `ℓ`-adically separated. For a ring hom `φ : R →+* S`
whose kernel lies in `ℓ R`, the kernel of `GL n R → GL n S` is torsion-free: an invertible matrix
congruent to `1` modulo `ker φ` and of finite order is `1`. -/
theorem isMulTorsionFree_ker_map {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    (hreg : IsSMulRegular R (ℓ : R)) (hsep : IsHausdorff (Ideal.span {(ℓ : R)}) R) (φ : R →+* S)
    (hφ : RingHom.ker φ ≤ Ideal.span {(ℓ : R)}) :
    IsMulTorsionFree (map (n := n) φ).ker := by
  refine IsMulTorsionFree.of_not_isOfFinOrder ?_
  rintro ⟨g, hg⟩ hne hfin
  refine hne ?_
  -- the entries of `g - 1` are multiples of `ℓ`
  have hgφ : (g : Matrix n n R).map φ = 1 := by
    simpa [Units.ext_iff] using MonoidHom.mem_ker.mp hg
  have hdvd (i j : n) : ∃ r : R, r * ℓ = (g - 1 : Matrix n n R) i j := by
    refine Ideal.mem_span_singleton'.mp (hφ (RingHom.mem_ker.mpr ?_))
    have h0 : φ.mapMatrix ((g : Matrix n n R) - 1) = 0 := by
      rw [map_sub, map_one, RingHom.mapMatrix_apply, hgφ, sub_self]
    simpa using congrFun (congrFun h0 i) j
  choose Y hY using hdvd
  -- apply Serre's lemma in the matrix ring, where multiplication by `ℓ` is scalar multiplication
  have hregM : IsLeftRegular (ℓ : Matrix n n R) := by
    simpa using Matrix.isLeftRegular_scalar (n := n) hreg
  have hsepM (x : Matrix n n R) (hx : ∀ k : ℕ, (ℓ : Matrix n n R) ^ k ∣ x) : x = 0 :=
    Matrix.eq_zero_of_forall_scalar_pow_dvd hsep (by simpa using hx)
  have hk : 3 ≤ ℓ ^ 1 := by
    obtain ⟨m, hm⟩ := hodd
    have := hℓ.two_le
    rw [pow_one]
    omega
  have hg1 : (ℓ : Matrix n n R) ^ 1 ∣ (g : Matrix n n R) - 1 := by
    refine ⟨Matrix.of Y, ?_⟩
    rw [pow_one, ← nsmul_eq_mul]
    ext i j
    simp [← hY, mul_comm]
  have := TauCeti.eq_one_of_isOfFinOrder_of_pow_dvd_sub_one hℓ hregM hsepM hk
    (Units.isOfFinOrder_val.mpr ((Subgroup.subtype _).isOfFinOrder hfin)) hg1
  exact Subtype.ext (Units.ext this)

/-- **Reduction is injective on finite subgroups.** Under the hypotheses of
`Matrix.GeneralLinearGroup.isMulTorsionFree_ker_map`, the map `GL n R → GL n S` induced by `φ` is
injective on every finite subgroup of `GL n R`. -/
theorem injective_domRestrict_map {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    (hreg : IsSMulRegular R (ℓ : R)) (hsep : IsHausdorff (Ideal.span {(ℓ : R)}) R) (φ : R →+* S)
    (hφ : RingHom.ker φ ≤ Ideal.span {(ℓ : R)}) (G : Subgroup (GL n R)) [Finite G] :
    Function.Injective ((map φ).domRestrict G) :=
  have := isMulTorsionFree_ker_map (n := n) hℓ hodd hreg hsep φ hφ
  (map φ).injective_domRestrict_of_isMulTorsion isMulTorsion_of_finite

/-- Under the hypotheses of `Matrix.GeneralLinearGroup.isMulTorsionFree_ker_map`, a finite subgroup
of `GL n R` has at most `|GL n S|` elements, since it embeds into `GL n S`. -/
theorem natCard_le_natCard_map {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    (hreg : IsSMulRegular R (ℓ : R)) (hsep : IsHausdorff (Ideal.span {(ℓ : R)}) R) (φ : R →+* S)
    (hφ : RingHom.ker φ ≤ Ideal.span {(ℓ : R)}) [Finite S] (G : Subgroup (GL n R)) [Finite G] :
    Nat.card G ≤ Nat.card (GL n S) :=
  Nat.card_le_card_of_injective _ (injective_domRestrict_map hℓ hodd hreg hsep φ hφ G)

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- **The first congruence subgroup of `GL n ℤ_[p]` is torsion-free** for an odd prime `p`: the
kernel of reduction `GL n ℤ_[p] → GL n (ZMod p)` has no nontrivial element of finite order. -/
theorem isMulTorsionFree_ker_map_toZMod (hp : Odd p) :
    IsMulTorsionFree (map (n := n) (PadicInt.toZMod : ℤ_[p] →+* ZMod p)).ker := by
  have hsep : IsHausdorff (Ideal.span {(p : ℤ_[p])}) ℤ_[p] := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  exact isMulTorsionFree_ker_map Fact.out hp (IsSMulRegular.of_ne_zero (by exact_mod_cast
    (Fact.out : p.Prime).ne_zero)) hsep _
    (by rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p])

/-- **Finite subgroups of `GL n ℤ_[p]` inject modulo `p`** for an odd prime `p`: reduction
`GL n ℤ_[p] → GL n (ZMod p)` is injective on every finite subgroup. -/
theorem injective_domRestrict_map_toZMod (hp : Odd p) (G : Subgroup (GL n ℤ_[p])) [Finite G] :
    Function.Injective ((map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)).domRestrict G) :=
  have := isMulTorsionFree_ker_map_toZMod (n := n) hp
  (map _).injective_domRestrict_of_isMulTorsion isMulTorsion_of_finite

end Padic

section Int

/-- **The kernel of `GL n ℤ → GL n (ZMod p)` is torsion-free** for an odd prime `p`: an integer
matrix of finite order congruent to `1` modulo `p` is `1`. -/
theorem isMulTorsionFree_ker_map_intCast {p : ℕ} [hp : Fact p.Prime] (hodd : Odd p) :
    IsMulTorsionFree (map (n := n) (Int.castRingHom (ZMod p))).ker :=
  isMulTorsionFree_ker_map hp.out hodd (.of_ne_zero (by exact_mod_cast hp.out.ne_zero))
    (.of_isDomain _ (by
      rw [Ne, Ideal.span_singleton_eq_top, Int.isUnit_iff]
      have := hp.out.two_le
      omega)) _
    (ZMod.ker_intCastRingHom p).le

/-- **Finite subgroups of `GL n ℤ` inject modulo an odd prime `p`**: reduction
`GL n ℤ → GL n (ZMod p)` is injective on every finite subgroup. -/
theorem injective_domRestrict_map_intCast {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (G : Subgroup (GL n ℤ)) [Finite G] :
    Function.Injective ((map (Int.castRingHom (ZMod p))).domRestrict G) :=
  have := isMulTorsionFree_ker_map_intCast (n := n) hodd
  (map _).injective_domRestrict_of_isMulTorsion isMulTorsion_of_finite

/-- A finite subgroup of `GL n ℤ` has at most `|GL n (ZMod 3)|` elements, since it embeds into
`GL n (ZMod 3)` by reduction. -/
theorem natCard_le_natCard_zmod_three {G : Subgroup (GL n ℤ)} [Finite G] :
    Nat.card G ≤ Nat.card (GL n (ZMod 3)) :=
  Nat.card_le_card_of_injective _ (injective_domRestrict_map_intCast (p := 3) (by decide) G)

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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.PrimeDecomposition
public import TauCeti.NumberTheory.HeckeRing.Multiplication
import TauCeti.LinearAlgebra.Matrix.Divisibility

/-!
# The support of Hecke products

The structure constants of a product of two double cosets of the arithmetic Hecke triple of
`GL_n` are constrained in two ways. First, they are supported on cosets whose representatives
have the product determinant. Second, the elementary divisors of every coset in the support
dominate those of the factors: if `T(c)` occurs in `T(a) · T(b)`, then for each `k` the product
of the first `k` elementary divisors of `c` is divisible by those of `a` times those of `b`. A
representative of `T(c)` is `P · diag(a) · Q · diag(b) · S` with `P`, `Q`, `S` in `SL_n(ℤ)`, so
this is the divisibility of the `k × k` minors of such a product,
`Matrix.prod_castLE_mul_prod_castLE_dvd_of_mul_diagonal_mul_diagonal_mul_eq`.

For prime-power diagonals `T(p ^ e)` and `T(p ^ f)` with monotone exponent vectors, the second
constraint says that every coset of the support is `T(p ^ g)` with `∑ g = ∑ (e + f)` and with
leading partial sums `∑_{j < k} g j` at least those of `e + f`. This is the support half of the
triangular expansion of a product of diagonal prime-power cosets with respect to the leading
diagonal `T(p ^ (e + f))`, on which the presentation of the `p`-local Hecke ring as a polynomial
ring rests (Shimura, Theorem 3.20). The other half, that `T(p ^ (e + f))` occurs with
coefficient one, is `HeckeRing.GLn.diagElem_primePowDiag_mul_apply_diagCoset_add`, in
`GLn/LeadingCoefficient.lean`.

## Main results

* `HeckeCoset.rep_det_eq_mul_of_structureConstants_ne_zero`: the determinant of a coset in the
  support is the product of the determinants.
* `HeckeRing.GLn.prod_castLE_mul_prod_castLE_dvd_of_diagElem_mul_apply_ne_zero`: the leading
  elementary divisors of a coset in the support of `T(a) · T(b)` are divisible by those of
  `a` times those of `b`.
* `HeckeRing.GLn.exists_primePowDiag_of_diagElem_mul_apply_ne_zero`: every coset in the
  support of `T(p ^ e) · T(p ^ f)` is `T(p ^ g)` for a monotone `g` with total `∑ (e + f)` whose
  leading partial sums dominate those of `e + f`.

The determinant argument generalizes the one in AINTLIB's
`LeanModularForms/HeckeRIngs/GLn/PolynomialRing.lean`, which is used there for `n = 2`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.2, Theorem 3.20.
-/

public section

open Matrix HeckeRing DoubleCoset Matrix.SpecialLinearGroup

namespace HeckeRing.GLn

variable {n : ℕ}

/-- Representatives of the same `SL_n(ℤ)` double coset have equal determinant. -/
private lemma det_rep_eq_of_heckeCoset_eq {g₁ g₂ : posDetInt n}
    (h : HeckeCoset.mk (SLnZ n) (SLnZ n) g₁ = HeckeCoset.mk (SLnZ n) (SLnZ n) g₂) :
    (↑(↑g₁ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det =
      (↑(↑g₂ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det :=
    det_eq_of_mem_doubleCoset_SLnZ n
    (HeckeCoset.eq_iff.mp h ▸ DoubleCoset.mem_doubleCoset_self _ _ _)

end HeckeRing.GLn

namespace HeckeCoset

variable {n : ℕ}

/-- A nonzero structure constant can occur only at a coset whose representative determinant is
the product of the input representative determinants. -/
theorem rep_det_eq_mul_of_structureConstants_ne_zero
    [IsHeckeTriple (HeckeRing.GLn.posDetInt n) (HeckeRing.GLn.SLnZ n)
      (HeckeRing.GLn.SLnZ n)]
    (D₁ D₂ D : HeckeCoset (HeckeRing.GLn.posDetInt n)
      (HeckeRing.GLn.SLnZ n) (HeckeRing.GLn.SLnZ n))
    (h : (HeckeCosetModule.structureConstants ℤ (HeckeRing.GLn.SLnZ n)
      (HeckeRing.GLn.SLnZ n) (HeckeRing.GLn.SLnZ n)
      (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) D ≠ 0) :
    (↑(↑(HeckeCoset.rep D) : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det =
      (↑(↑(HeckeCoset.rep D₁) : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det *
      (↑(↑(HeckeCoset.rep D₂) : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det := by
  classical
  rw [HeckeCosetModule.structureConstants_apply] at h
  have hD : D ∈ Finset.univ.image
      (HeckeCoset.mulMap (HeckeRing.GLn.SLnZ n) (HeckeRing.GLn.SLnZ n) (HeckeRing.GLn.SLnZ n)
        (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) :=
    (HeckeCoset.mem_image_mulMap_iff _ _ _).mpr (Nat.cast_ne_zero.mp h)
  obtain ⟨p, -, hD⟩ := Finset.mem_image.mp hD
  have hcoset := (HeckeCoset.mk_rep
      (HeckeCoset.mulMap (HeckeRing.GLn.SLnZ n) (HeckeRing.GLn.SLnZ n) (HeckeRing.GLn.SLnZ n)
        (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) p)).trans
    (HeckeCoset.mulMap_eq_mk _ _ _ _ _ _)
  have hDrep : HeckeCoset.mk (HeckeRing.GLn.SLnZ n) (HeckeRing.GLn.SLnZ n)
      (HeckeCoset.rep D) =
    HeckeCoset.mk (HeckeRing.GLn.SLnZ n) (HeckeRing.GLn.SLnZ n)
      (HeckeCoset.rep (HeckeCoset.mulMap (HeckeRing.GLn.SLnZ n) (HeckeRing.GLn.SLnZ n)
        (HeckeRing.GLn.SLnZ n) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) p)) :=
    (HeckeCoset.mk_rep D).trans
      (hD.symm.trans (HeckeCoset.mk_rep _).symm)
  rw [HeckeRing.GLn.det_rep_eq_of_heckeCoset_eq (hDrep.trans hcoset)]
  simp only [GeneralLinearGroup.coe_mul, Matrix.det_mul]
  have h₁ := HeckeRing.GLn.det_eq_one_of_mem_SLnZ n p.1.out.2
  have h₂ := HeckeRing.GLn.det_eq_one_of_mem_SLnZ n p.2.out.2
  rw [h₁, h₂]
  ring

end HeckeCoset

namespace HeckeRing.GLn

variable {n : ℕ}

section Dominance

-- The multiplication of the Hecke ring needs the arithmetic Hecke triple, whose instance carries
-- `NeZero n`.
variable [NeZero n]

/-- A coset occurring in `T(a) · T(b)` has a nonzero structure constant there. -/
private lemma structureConstants_ne_zero_of_diagElem_mul_apply_ne_zero {a b : Fin n → ℕ}
    {D : HeckeCoset (posDetInt n) (SLnZ n) (SLnZ n)} (h : (diagElem a * diagElem b) D ≠ 0) :
    HeckeCosetModule.structureConstants ℤ (SLnZ n) (SLnZ n) (SLnZ n)
      (diagCoset a).rep (diagCoset b).rep D ≠ 0 := by
  rwa [diagElem_def, diagElem_def, HeckeCosetModule.single_mul_single,
    HeckeCosetModule.smul_apply, HeckeCosetModule.smul_apply, one_mul, one_mul] at h

/-- A coset `T(c)` occurring in `T(a) · T(b)` has the integral representative
`P * diag(a) * Q * diag(b) * S`: the product of two coset representatives, each of the form
`SL_n(ℤ) · diag · SL_n(ℤ)`, moved into `T(c)` by two further elements of `SL_n(ℤ)`. -/
private lemma exists_mul_diagonal_mul_diagonal_mul_eq_diagonal {a b c : Fin n → ℕ}
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (h : (diagElem a * diagElem b) (diagCoset c) ≠ 0) :
    ∃ P Q S : Matrix (Fin n) (Fin n) ℤ,
      P * diagonal (fun i ↦ (a i : ℤ)) * Q * diagonal (fun i ↦ (b i : ℤ)) * S =
        diagonal (fun i ↦ (c i : ℤ)) := by
  classical
  have h' := structureConstants_ne_zero_of_diagElem_mul_apply_ne_zero h
  rw [HeckeCosetModule.structureConstants_apply] at h'
  have hD := (HeckeCoset.mem_image_mulMap_iff _ _ _).mpr (Nat.cast_ne_zero.mp h')
  obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hD
  rw [HeckeCoset.mulMap_eq_mk, diagCoset_def c, HeckeCoset.eq_iff] at hp
  have hmem : natDiagGL n c ∈ doubleCoset ((p.1.out : GL (Fin n) ℚ) * (diagCoset a).rep *
      ((p.2.out : GL (Fin n) ℚ) * (diagCoset b).rep)) (SLnZ n) (SLnZ n) := by
    rw [hp]
    exact mem_doubleCoset_self _ _ _
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_doubleCoset.mp hmem
  -- forget the coset representatives, on whose types `p` depends
  have hu : (p.1.out : GL (Fin n) ℚ) ∈ SLnZ n := p.1.out.2
  have hv : (p.2.out : GL (Fin n) ℚ) ∈ SLnZ n := p.2.out.2
  generalize (p.1.out : GL (Fin n) ℚ) = u at hxy hu
  generalize (p.2.out : GL (Fin n) ℚ) = v at hxy hv
  obtain ⟨h₁, hh₁, h₂, hh₂, hA⟩ := exists_rep_diagCoset_eq_mul_natDiagGL_mul a
  obtain ⟨h₃, hh₃, h₄, hh₄, hB⟩ := exists_rep_diagCoset_eq_mul_natDiagGL_mul b
  -- collect the `SL_n(ℤ)` factors on the left, in the middle and on the right
  obtain ⟨σ, hσ⟩ := (mem_SLnZ_iff n).mp ((SLnZ n).mul_mem ((SLnZ n).mul_mem hx hu) hh₁)
  obtain ⟨τ, hτ⟩ := (mem_SLnZ_iff n).mp ((SLnZ n).mul_mem ((SLnZ n).mul_mem hh₂ hv) hh₃)
  obtain ⟨ρ, hρ⟩ := (mem_SLnZ_iff n).mp ((SLnZ n).mul_mem hh₄ hy)
  have heq : natDiagGL n c =
      mapGL ℚ σ * natDiagGL n a * mapGL ℚ τ * natDiagGL n b * mapGL ℚ ρ := by
    rw [hσ, hτ, hρ, hxy, hA, hB]
    simp only [mul_assoc]
  refine ⟨σ, τ, ρ, Matrix.map_injective (f := (Int.cast : ℤ → ℚ)) Int.cast_injective ?_⟩
  -- read the identity in `GL_n(ℚ)` through the entrywise cast, a ring homomorphism of matrices
  have hcast : ∀ X : Matrix (Fin n) (Fin n) ℤ,
      X.map (Int.cast : ℤ → ℚ) = (Int.castRingHom ℚ).mapMatrix X := fun _ ↦ (rfl)
  have hmat := congrArg (fun g : GL (Fin n) ℚ ↦ (g : Matrix (Fin n) (Fin n) ℚ)) heq
  simp only [Units.val_mul, natDiagGL_coe_eq_map_intCast n _ ha,
    natDiagGL_coe_eq_map_intCast n _ hb, natDiagGL_coe_eq_map_intCast n _ hc, mapGL_coe_matrix,
    map_apply_coe, RingHom.mapMatrix_apply, algebraMap_int_eq, Int.coe_castRingHom] at hmat
  beta_reduce
  rw [hmat]
  simp only [hcast, map_mul]

/-- **The leading elementary divisors of a Hecke product dominate those of its factors.** If the
double coset `T(c)` occurs in `T(a) · T(b)`, where `a` and `b` are positive divisibility chains
and `c` is positive, then for every `k ≤ n` the product of the first `k` entries of `c` is
divisible by the product of the first `k` entries of `a` times that of `b`. For `k = n` the
two sides are the determinants, and they are equal
(`HeckeCoset.rep_det_eq_mul_of_structureConstants_ne_zero`). -/
theorem prod_castLE_mul_prod_castLE_dvd_of_diagElem_mul_apply_ne_zero {a b c : Fin n → ℕ}
    (ha : ∀ i, 0 < a i) (ha' : IsDvdChain a) (hb : ∀ i, 0 < b i) (hb' : IsDvdChain b)
    (hc : ∀ i, 0 < c i) (h : (diagElem a * diagElem b) (diagCoset c) ≠ 0) {k : ℕ}
    (hk : k ≤ n) :
    (∏ j : Fin k, a (Fin.castLE hk j)) * ∏ j : Fin k, b (Fin.castLE hk j) ∣
      ∏ j : Fin k, c (Fin.castLE hk j) := by
  obtain ⟨P, Q, S, hPQS⟩ := exists_mul_diagonal_mul_diagonal_mul_eq_diagonal ha hb hc h
  exact_mod_cast Matrix.prod_castLE_mul_prod_castLE_dvd_of_mul_diagonal_mul_diagonal_mul_eq
    (fun _ _ hij ↦ Int.natCast_dvd_natCast.mpr (isDvdChain_iff.mp ha' hij))
    (fun _ _ hij ↦ Int.natCast_dvd_natCast.mpr (isDvdChain_iff.mp hb' hij)) P Q S hPQS hk

/-- **The support of a product of `p`-power diagonal cosets lies above the sum of the exponents.**
Let `p` be prime and `e`, `f` monotone exponent vectors. Every double coset occurring in
`T(p ^ e) · T(p ^ f)` is `T(p ^ g)` for a monotone exponent vector `g` with the same total
`∑ i, g i = ∑ i, (e i + f i)`, whose leading partial sums dominate those of `e + f`:
`∑_{j < k} (e j + f j) ≤ ∑_{j < k} g j` for every `k ≤ n`. -/
theorem exists_primePowDiag_of_diagElem_mul_apply_ne_zero {p : ℕ} (hp : p.Prime)
    {e f : Fin n → ℕ} (he : Monotone e) (hf : Monotone f)
    {D : HeckeCoset (posDetInt n) (SLnZ n) (SLnZ n)}
    (h : (diagElem (primePowDiag n p e) * diagElem (primePowDiag n p f)) D ≠ 0) :
    ∃ g : Fin n → ℕ, Monotone g ∧ D = diagCoset (primePowDiag n p g) ∧
      ∑ i, g i = ∑ i, (e i + f i) ∧
      ∀ (k : ℕ) (hk : k ≤ n), ∑ j : Fin k, (e (Fin.castLE hk j) + f (Fin.castLE hk j)) ≤
        ∑ j : Fin k, g (Fin.castLE hk j) := by
  obtain ⟨c, hc, hc', rfl⟩ := exists_diagonal_representative D
  -- the determinant of the occurring coset is `p ^ ∑ (e + f)`
  have hdet := HeckeCoset.rep_det_eq_mul_of_structureConstants_ne_zero _ _ _
    (structureConstants_ne_zero_of_diagElem_mul_apply_ne_zero h)
  rw [diagCoset_rep_det c hc, diagCoset_rep_det _ (primePowDiag_pos n p hp.pos e),
    diagCoset_rep_det _ (primePowDiag_pos n p hp.pos f)] at hdet
  have hprod : ∏ i, c i = p ^ ∑ i, (e i + f i) := by
    have hcast : ((∏ i, c i : ℕ) : ℚ) = ((p ^ ∑ i, (e i + f i) : ℕ) : ℚ) := by
      push_cast
      rw [hdet]
      simp [primePowDiag_apply, Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib, pow_add]
    exact_mod_cast hcast
  -- so its entries are powers of `p`
  choose g hg using fun i ↦ (Nat.dvd_prime_pow hp).mp
    (hprod ▸ Finset.dvd_prod_of_mem c (Finset.mem_univ i))
  obtain rfl : c = primePowDiag n p g := funext fun i ↦ by rw [primePowDiag_apply, (hg i).2]
  refine ⟨g, fun i j hij ↦ ?_, rfl, ?_, fun k hk ↦ ?_⟩
  · have hdvd := isDvdChain_iff.mp hc' hij
    rw [primePowDiag_apply, primePowDiag_apply] at hdvd
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
  · refine Nat.pow_right_injective hp.two_le ?_
    simpa [primePowDiag_apply, Finset.prod_pow_eq_pow_sum] using hprod
  · have hdvd := prod_castLE_mul_prod_castLE_dvd_of_diagElem_mul_apply_ne_zero
      (primePowDiag_pos n p hp.pos e) (isDvdChain_primePowDiag n p e he)
      (primePowDiag_pos n p hp.pos f) (isDvdChain_primePowDiag n p f hf) hc h hk
    simp only [primePowDiag_apply, Finset.prod_pow_eq_pow_sum, ← pow_add] at hdvd
    rw [Finset.sum_add_distrib]
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd

end Dominance

end HeckeRing.GLn

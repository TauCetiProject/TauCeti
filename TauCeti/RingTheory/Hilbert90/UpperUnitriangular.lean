/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import TauCeti.Algebra.Group.Hom.TwistedNorm
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Iwahori
-- `Finset.isFixedPt_sum_range_iterate_of_isPeriodicPt`: an additive endomorphism fixes a periodic
-- orbit sum; `RingHom.pow_apply_eq_self_of_sum_range_pow_apply_eq_one`: an element whose orbit sum
-- of length `n` is `1` is fixed by `σ ^ n`.
import TauCeti.Algebra.BigOperators.Finset.Periodic
-- `ValuationSubring.isLocalHom_restrict`: a valuation subring dominates its pullback.
import TauCeti.RingTheory.Valuation.ValuationSubring
-- `Matrix.GeneralLinearGroup.map_injective`: change of scalars along an injective map.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
-- `Matrix.GeneralLinearGroup.iterate_mul_map_eq_twistedNorm_mul_map`: iterates of `v ↦ s * σ(v)`.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.TwistedNorm

/-!
# Hilbert's Theorem 90 for upper-unitriangular congruence subgroups

Let `R` be a commutative ring, `I` an ideal in the Jacobson radical of `R`, `σ : R →+* R` a ring
endomorphism with `σ(I) ⊆ I`, and `U(I) ⊆ GL_m(R)` the upper-unitriangular congruence subgroup
modulo `I` (`TauCeti.upperUnitriangularCongruenceSubgroup`). Over a local ring with `I` the maximal
ideal, `U(I)` is `TauCeti.iwahoriOne`, the subgroup of matrices upper unitriangular modulo the
maximal ideal; over the valuation ring of a nonarchimedean local field with residue characteristic
`p`, this is the pro-`p` Iwahori subgroup.

Fix a length `n : ℕ`. If some `c : R` has `∑ i ∈ range n, σ^i(c) = 1`, then every `s ∈ U(I)` whose
twisted norm `N_σ(s) = s * σ(s) * ⋯ * σ^(n-1)(s)` is `1` is a coboundary in `U(I)`:
`s * σ(t) = t` for some `t ∈ U(I)`. With the partial twisted norms `N_i := N_{σ,i}(s)`, the
`i`-th iterate of `τ : v ↦ s * σ(v)` sends `c • 1` to `σ^i(c) • N_i`, and `τ^n (c • 1) = c • 1`
because `N_n = 1` and `σ^n(c) = c` (which follows from the trace condition on `c`). So `τ` fixes
the orbit sum `t := ∑ i ∈ range n, σ^i(c) • N_i`, the weighted sum of the classical proof of
Hilbert's Theorem 90. Each `N_i` lies in `U(I)`, as `U(I)` is stable under `σ`; so `t` is upper
triangular modulo `I` with diagonal entries `≡ ∑ i ∈ range n, σ^i(c) = 1`, and by
`TauCeti.exists_mem_upperUnitriangularCongruenceSubgroup_coe_eq` it is invertible and lies in
`U(I)`.

The theorem needs no finiteness of the period of `σ`, no Artinian or profinite hypothesis on `R`
and no condition on `σ` modulo primes, unlike the congruence-level Hilbert 90 of
`TauCeti.TameHilbert90.IsTameAtLevel.exists_mul_map_eq_of_twistedNorm_eq_one` and its profinite
version, which treat the principal congruence subgroups `1 + m • Matrix n n R`.

## Main results

* `TauCeti.exists_mul_map_eq_of_twistedNorm_eq_one_upperUnitriangularCongruenceSubgroup`:
  Hilbert's Theorem 90 for `U(I)`.
* `TauCeti.exists_mul_map_eq_of_twistedNorm_eq_one_iwahoriOne`: the case of `iwahoriOne m R` over a
  local ring `R`, for a local endomorphism `σ`.
* `TauCeti.exists_mul_map_eq_of_twistedNorm_eq_one_map_iwahoriOne`: the same inside `GL_m(K)` for
  a valuation subring `A` of a field `K` and an endomorphism `σ` of `K` with `σ⁻¹(A) = A`, for the
  image of `iwahoriOne m A` in `GL_m(K)` (the pro-`p` Iwahori subgroup of `GL_m(K)` when `K` is a
  nonarchimedean local field with valuation ring `A`).

## References

* J.-P. Serre, *Local Fields*, Chapter X, §1, Proposition 3 (Hilbert's Theorem 90 for `GL_n`).
* A related formalization of this result: the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207,
  `Lib/GaloisRep/BaseChange/IwahoriEigenforms` (`New.exists_coboundary_proIwahori`).
-/

public section

open Finset Matrix

namespace TauCeti

variable {m : Type*} [Fintype m] [LinearOrder m] {R : Type*} [CommRing R]

/-- **Hilbert's Theorem 90 for upper-unitriangular congruence subgroups.** Let `I` be an ideal in
the Jacobson radical of `R`, `σ : R →+* R` a ring endomorphism with `I ≤ I.comap σ`, `n : ℕ`, and
`c : R` with `∑ i ∈ range n, σ^i(c) = 1`. If `s` lies in the upper-unitriangular congruence
subgroup modulo `I` and its twisted norm `s * σ(s) * ⋯ * σ^(n-1)(s)` is `1`, then
`s * σ(t) = t` for some `t` in that subgroup. -/
theorem exists_mul_map_eq_of_twistedNorm_eq_one_upperUnitriangularCongruenceSubgroup
    {I : Ideal R} (hI : I ≤ Ring.jacobson R) {σ : R →+* R} (hσI : I ≤ I.comap σ) {n : ℕ} {c : R}
    (hc : ∑ i ∈ range n, (σ ^ i) c = 1)
    {s : GL m R} (hs : s ∈ upperUnitriangularCongruenceSubgroup m I)
    (hN : MonoidHom.twistedNorm (GeneralLinearGroup.map σ) n s = 1) :
    ∃ t ∈ upperUnitriangularCongruenceSubgroup m I, s * GeneralLinearGroup.map σ t = t := by
  set N : ℕ → GL m R := fun i ↦ MonoidHom.twistedNorm (GeneralLinearGroup.map σ) i s
  have hNmem (i : ℕ) : N i ∈ upperUnitriangularCongruenceSubgroup m I :=
    (GeneralLinearGroup.map σ).twistedNorm_mem
      (fun _ ↦ map_mem_upperUnitriangularCongruenceSubgroup hσI) hs i
  let τ : Matrix m m R →+ Matrix m m R :=
    (AddMonoidHom.mulLeft (s : Matrix m m R)).comp σ.mapMatrix.toAddMonoidHom
  -- Unfolding the definition of `τ`.
  have hτ_apply (X : Matrix m m R) : τ X = (s : Matrix m m R) * σ.mapMatrix X := rfl
  -- The iterates of `τ` on `c • 1` are the weighted terms `σ^i(c) • N_i`.
  have hτ_iter (i : ℕ) : τ^[i] (c • 1) = (σ ^ i) c • (N i : Matrix m m R) := by
    rw [show ⇑τ = fun w ↦ (s : Matrix m m R) * w.map σ from funext hτ_apply,
      GeneralLinearGroup.iterate_mul_map_eq_twistedNorm_mul_map]
    simp [Matrix.map_smul', N]
  have hper : Function.IsPeriodicPt τ n (c • 1) := by
    simp only [Function.IsPeriodicPt, Function.IsFixedPt, hτ_iter, N, hN, Units.val_one,
      σ.pow_apply_eq_self_of_sum_range_pow_apply_eq_one hc]
  have hsum : ∑ i ∈ range n, τ^[i] (c • 1) = ∑ i ∈ range n, (σ ^ i) c • (N i : Matrix m m R) :=
    sum_congr rfl fun i _ ↦ hτ_iter i
  obtain ⟨t, ht, htM⟩ := exists_mem_upperUnitriangularCongruenceSubgroup_coe_eq hI
    (M := ∑ i ∈ range n, (σ ^ i) c • (N i : Matrix m m R))
    (fun i j hji ↦ by
      simpa using sum_mem fun k _ ↦
        I.mul_mem_left ((σ ^ k) c) ((mem_upperUnitriangularCongruenceSubgroup_iff.mp
          (hNmem k)).1 hji))
    fun i ↦ by
      have hdiag : (∑ k ∈ range n, (σ ^ k) c • (N k : Matrix m m R)) i i - 1 =
          ∑ k ∈ range n, (σ ^ k) c * ((N k : Matrix m m R) i i - 1) := by
        simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_sub, mul_one,
          sum_sub_distrib, hc]
      rw [hdiag]
      exact sum_mem fun k _ ↦ I.mul_mem_left _
        ((mem_upperUnitriangularCongruenceSubgroup_iff.mp (hNmem k)).2 i)
  -- The fixed-point equation `s * σ(t) = t`, at matrix level.
  have hmat : (s : Matrix m m R) * σ.mapMatrix (t : Matrix m m R) = t := by
    rw [← hτ_apply, htM, ← hsum]
    exact isFixedPt_sum_range_iterate_of_isPeriodicPt hper
  refine ⟨t, ht, Units.ext ?_⟩
  rw [Units.val_mul, GeneralLinearGroup.val_map_apply]
  exact hmat

/-- **Hilbert's Theorem 90 for `iwahoriOne`.** Let `R` be a local ring (for instance the valuation
ring of a nonarchimedean local field, where `iwahoriOne m R` is the pro-`p` Iwahori subgroup),
`σ : R →+* R` a local ring endomorphism, `n : ℕ`, and `c : R` with `∑ i ∈ range n, σ^i(c) = 1`.
If `s` lies in `iwahoriOne m R`, the subgroup of matrices upper unitriangular modulo the maximal
ideal, and its twisted norm `s * σ(s) * ⋯ * σ^(n-1)(s)` is `1`, then `s * σ(t) = t` for some `t`
in `iwahoriOne m R`. -/
theorem exists_mul_map_eq_of_twistedNorm_eq_one_iwahoriOne [IsLocalRing R] {σ : R →+* R}
    [IsLocalHom σ] {n : ℕ} {c : R} (hc : ∑ i ∈ range n, (σ ^ i) c = 1) {s : GL m R}
    (hs : s ∈ iwahoriOne m R)
    (hN : MonoidHom.twistedNorm (GeneralLinearGroup.map σ) n s = 1) :
    ∃ t ∈ iwahoriOne m R, s * GeneralLinearGroup.map σ t = t :=
  exists_mul_map_eq_of_twistedNorm_eq_one_upperUnitriangularCongruenceSubgroup
    (IsLocalRing.ringJacobson_eq_maximalIdeal R).ge (IsLocalRing.maximalIdeal_comap σ).ge hc hs hN

section ValuationSubring

variable {K : Type*} [Field K] {A : ValuationSubring K}

/-- **Hilbert's Theorem 90 for the image of `iwahoriOne m A` in `GL_m(K)`.** Let `A` be a
valuation subring of a field `K` (for instance the valuation ring of a nonarchimedean local
field, where this image is the pro-`p` Iwahori subgroup of `GL_m(K)`), `σ : K →+* K` a field
endomorphism with `σ⁻¹(A) = A`, `n : ℕ`, and `c ∈ A` with `∑ i ∈ range n, σ^i(c) = 1`. If `s`
lies in the image of `iwahoriOne m A` in `GL_m(K)` and its twisted norm
`s * σ(s) * ⋯ * σ^(n-1)(s)` is `1`, then `s * σ(t) = t` for some `t` in that image. -/
theorem exists_mul_map_eq_of_twistedNorm_eq_one_map_iwahoriOne {σ : K →+* K}
    (hσ : A.comap σ = A) {n : ℕ} {c : A} (hc : ∑ i ∈ range n, (σ ^ i) (c : K) = 1) {s : GL m K}
    (hs : s ∈ (iwahoriOne m A).map (GeneralLinearGroup.map (algebraMap A K)))
    (hN : MonoidHom.twistedNorm (GeneralLinearGroup.map σ) n s = 1) :
    ∃ t ∈ (iwahoriOne m A).map (GeneralLinearGroup.map (algebraMap A K)),
      s * GeneralLinearGroup.map σ t = t := by
  have hσA : ∀ x ∈ A, σ x ∈ A := fun _ hx ↦ ValuationSubring.mem_comap.mp (hσ.ge hx)
  set σA := σ.restrict A A hσA
  -- `A` dominates its pullback `A.comap σ = A`, so the restriction of `σ` to `A` is local.
  have : IsLocalHom σA := ValuationSubring.isLocalHom_restrict A σ hσ.symm
  set ι : GL m A →* GL m K := GeneralLinearGroup.map (algebraMap A K)
  have hι : Function.Injective ι := GeneralLinearGroup.map_injective Subtype.val_injective
  -- Restricting scalars to `A` intertwines `GL_m(σA)` and `GL_m(σ)`.
  have hcomm (x : GL m A) : ι (GeneralLinearGroup.map σA x) = GeneralLinearGroup.map σ (ι x) :=
    by ext; simp [GeneralLinearGroup.map_apply, σA, ι]
  obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.mp hs
  -- The powers of `σA` act on underlying elements of `K` as the powers of `σ`.
  have hpow (i : ℕ) (x : A) : ((σA ^ i) x : K) = (σ ^ i) (x : K) := by
    simp only [RingHom.coe_pow]
    exact (Function.Semiconj.iterate_right (f := ((↑) : A → K))
      (RingHom.coe_restrict_apply σ A A hσA) i) x
  have hcA : ∑ i ∈ range n, (σA ^ i) c = 1 := Subtype.ext (by
    simpa only [AddSubmonoidClass.coe_finsetSum, hpow, OneMemClass.coe_one] using hc)
  have hNA : MonoidHom.twistedNorm (GeneralLinearGroup.map σA) n s₀ = 1 :=
    hι (by rw [MonoidHom.map_twistedNorm ι hcomm, hN, map_one])
  obtain ⟨t₀, ht₀, hst⟩ := exists_mul_map_eq_of_twistedNorm_eq_one_iwahoriOne hcA hs₀ hNA
  exact ⟨ι t₀, Subgroup.mem_map_of_mem _ ht₀, by rw [← hcomm, ← map_mul, hst]⟩

end ValuationSubring

end TauCeti

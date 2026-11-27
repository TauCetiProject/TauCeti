/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.Primorial
public import Mathlib.RingTheory.Adjoin.Basic
public import TauCeti.NumberTheory.DirichletCharacter.GeneralizedBernoulli
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.NumberTheory.Bernoulli.Polynomials
import TauCeti.LinearAlgebra.Matrix.GroupMatrix
import TauCeti.NumberTheory.DirichletCharacter.LFunction.TrivialZeros
import TauCeti.NumberTheory.MulChar.Basic

/-!
# Group determinants and a nonzero integer divisible by Bernoulli numbers

For a finite commutative group `G` and a function `g : G → R`, every homomorphism `χ : G →* R`
is an eigenvector of the group matrix `(g(t / s))_{s,t}`, with eigenvalue `∑ᵤ χ(u) g(u)`, and
each such eigenvalue divides the group determinant (`TauCeti.Matrix.of_div_mulVec_monoidHom`,
`TauCeti.Matrix.sum_mul_dvd_det_of_div`). For `G = (ZMod N)ˣ` and a domain of characteristic zero
with enough roots of unity, the Dirichlet characters are orthogonal, so their value matrix is
invertible and the group determinant is the product of the eigenvalues `∑ᵤ χ(u) g(u)` over all
Dirichlet characters `χ` modulo `N` (Dedekind's factorization); in particular it is nonzero exactly
when no eigenvalue vanishes.

Applied to `g(u) = 2 Pₖ₊₁ Mᵏ Bₖ(⟨u⟩ / M)`, corrected at `u = ±1` so that the eigenvalues of the
characters of the wrong parity are `±2` instead of `0`, this gives the Bernoulli group determinant
`TauCeti.bernoulliGroupDet M k`, a nonzero integer for `k ≥ 2` that is divisible by
`Pₖ₊₁ M Bₖ,ψ` in `ℤ[ψ]` for every Dirichlet character `ψ` modulo `M` with `ψ(-1) = (-1)ᵏ`, with
values in any `ℚ`-algebra. Here `Pₖ₊₁ = primorial (k + 1)`, and `Bₖ,ψ` is Tau Ceti's
`DirichletCharacter.generalizedBernoulli` at the modulus `M`. That the determinant is nonzero is
proved through the complex characters, whose Bernoulli numbers `Bₖ,ψ` of the right parity are
nonzero by `DirichletCharacter.generalizedBernoulli_ne_zero`. Its size is bounded in
`TauCeti.NumberTheory.DirichletCharacter.BernoulliBounds`.

## Main definitions

* `TauCeti.primorialBernoulli M k t`: the integer `Pₖ₊₁ Mᵏ Bₖ(⟨t⟩ / M)`.
* `TauCeti.bernoulliGroupEntry M k u`: the entry `2 Pₖ₊₁ Mᵏ Bₖ(⟨u⟩ / M)`, corrected at `u = ±1`.
* `TauCeti.bernoulliGroupDet M k`: the determinant of the group matrix of these entries.

## Main results

* `TauCeti.det_of_div_eq_prod`: the group determinant of `(ZMod N)ˣ` is the product of the
  eigenvalues.
* `TauCeti.det_of_div_ne_zero_iff`: the group determinant of `(ZMod N)ˣ` is nonzero
  exactly when every eigenvalue is.
* `TauCeti.sum_mul_bernoulliGroupEntry`, `TauCeti.sum_units_mul_primorialBernoulli`: the
  eigenvalues of the Bernoulli group matrix.
* `TauCeti.bernoulliGroupDet_ne_zero`: the Bernoulli group determinant is nonzero for `k ≥ 2`.
* `TauCeti.exists_mem_adjoin_bernoulliGroupDet_eq`: it is divisible by `Pₖ₊₁ M Bₖ,ψ` in `ℤ[ψ]`
  for every character `ψ` of parity `(-1)ᵏ`.
* `TauCeti.bernoulliGroupDet_eq_prod`: it is the product of the eigenvalues `2 Pₖ₊₁ M Bₖ,χ` (for
  `χ(-1) = (-1)ᵏ`) and `-2 (-1)ᵏ` (for the other characters).

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Lemma 5.26 (the group
  determinant).

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
PBC), file `src/Lib/Cyclotomic/Voronoi.lean`, declarations
`New.OddPart.det_ne_zero_of_forall_sum_mul_ne_zero` and the determinant step of
`New.OddPart.exists_isStickelbergerBound` (including the correction at `±1`). Here the
nonvanishing criterion is an equivalence, refined to the eigenvalue factorization, and the
Bernoulli values are normalised by the primorial and stated through
`DirichletCharacter.generalizedBernoulli`.
-/

public section

open Finset Matrix

namespace TauCeti

open DirichletCharacter

variable {N : ℕ}

/-- **Dedekind's factorization of the group determinant of `(ZMod N)ˣ`.** Over a domain of
characteristic zero with enough roots of unity, the determinant of the group matrix
`(g(t / s))_{s,t}` of `(ZMod N)ˣ` is the product, over the Dirichlet characters `χ` modulo `N`, of
the eigenvalues `∑ᵤ χ(u) g(u)`. -/
theorem det_of_div_eq_prod [NeZero N] {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod N)ˣ)] (g : (ZMod N)ˣ → R) :
    (of fun s t : (ZMod N)ˣ ↦ g (t / s)).det =
      ∏ χ : DirichletCharacter R N, ∑ u : (ZMod N)ˣ, χ u * g u := by
  classical
  -- index the characters by the units, and let `C` be the matrix of their values
  let e : (ZMod N)ˣ ≃ DirichletCharacter R N := (mulEquiv_units R N).some.toEquiv.symm
  let C : Matrix (ZMod N)ˣ (ZMod N)ˣ R := of fun t i ↦ e i t
  -- by orthogonality, `C` times the matrix of inverse values is `φ(N)`
  have hCD : C * (of fun i t : (ZMod N)ˣ ↦ e i (t : ZMod N)⁻¹) = (N.totient : R) • 1 := by
    refine Matrix.ext fun s t ↦ ?_
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    simp only [C, of_apply]
    rw [e.sum_comp fun χ ↦ χ s * χ (t : ZMod N)⁻¹]
    rw [sum_congr rfl fun χ _ ↦ mul_comm (χ s) _, sum_char_inv_mul_char_eq R t.isUnit]
    simp [eq_comm, Units.val_inj]
  have hC : C.det ≠ 0 := by
    have h := congrArg det hCD
    rw [det_mul, det_smul, det_one, mul_one] at h
    exact left_ne_zero_of_mul (h ▸ pow_ne_zero _ (Nat.cast_ne_zero.2 (Nat.totient_pos.2
      (Nat.pos_of_ne_zero (NeZero.ne N))).ne'))
  -- the columns of `C` are eigenvectors of the group matrix
  have hAC : (of fun s t : (ZMod N)ˣ ↦ g (t / s)) * C =
      C * diagonal fun i ↦ ∑ u : (ZMod N)ˣ, e i u * g u := by
    refine Matrix.ext fun s i ↦ ?_
    have h := congrFun (Matrix.of_div_mulVec_monoidHom g
      ((e i : ZMod N →* R).comp (Units.coeHom (ZMod N)))) s
    simp only [MulChar.coe_comp_coeHom_apply, mulVec, dotProduct, Pi.smul_apply,
      smul_eq_mul, of_apply] at h
    rw [Matrix.mul_apply, mul_diagonal]
    simpa [C, mul_comm (e i (s : ZMod N))] using h
  have h := congrArg det hAC
  rw [det_mul, det_mul, det_diagonal, mul_comm] at h
  rw [mul_left_cancel₀ hC h, e.prod_comp fun χ ↦ ∑ u : (ZMod N)ˣ, χ u * g u]

/-- **Group determinants of `(ZMod N)ˣ`.** Over a domain of characteristic zero with enough roots
of unity, the determinant of the group matrix `(g(t / s))_{s,t}` of `(ZMod N)ˣ` is nonzero
exactly when no eigenvalue `∑ᵤ χ(u) g(u)`, for `χ` a Dirichlet character modulo `N`, vanishes. -/
theorem det_of_div_ne_zero_iff [NeZero N] {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod N)ˣ)] (g : (ZMod N)ˣ → R) :
    (of fun s t : (ZMod N)ˣ ↦ g (t / s)).det ≠ 0 ↔
      ∀ χ : DirichletCharacter R N, ∑ u : (ZMod N)ˣ, χ u * g u ≠ 0 := by
  simp [det_of_div_eq_prod, prod_ne_zero_iff]

/-- The integer `Pₖ₊₁ Mᵏ Bₖ(⟨t⟩ / M)`, where `Pₖ₊₁ = primorial (k + 1)` and `⟨t⟩ ∈ [0, M)` is the
representative of `t` (`TauCeti.intCast_primorialBernoulli`). -/
noncomputable def primorialBernoulli (M k : ℕ) (t : ZMod M) : ℤ :=
  ⌊(primorial (k + 1) * M ^ k * (Polynomial.bernoulli k).eval ((t.val : ℚ) / M) : ℚ)⌋

/-- `TauCeti.primorialBernoulli M k t` is `Pₖ₊₁ Mᵏ Bₖ(⟨t⟩ / M)`, which is an integer. -/
theorem intCast_primorialBernoulli (M k : ℕ) (t : ZMod M) :
    (primorialBernoulli M k t : ℚ) =
      primorial (k + 1) * M ^ k * (Polynomial.bernoulli k).eval ((t.val : ℚ) / M) := by
  obtain ⟨z, hz⟩ : ∃ z : ℤ, (z : ℚ) =
      primorial (k + 1) * M ^ k * (Polynomial.bernoulli k).eval ((t.val : ℚ) / M) := by
    rcases eq_or_ne M 0 with rfl | hM
    · -- for `M = 0` the value is `P₁ B₀(0) = 1` at `k = 0` and `0` otherwise
      refine ⟨if k = 0 then 1 else 0, ?_⟩
      rcases k with _ | k <;> simp
    · simpa using exists_intCast_eq_primorial_mul_pow_mul_bernoulli_eval k hM t.val
  rw [primorialBernoulli, ← hz, Int.floor_intCast]

/-- **The Bernoulli eigenvalue.** `∑ᵤ ψ(u) Pₖ₊₁ Mᵏ Bₖ(⟨u⟩ / M) = Pₖ₊₁ M Bₖ,ψ` for a Dirichlet
character `ψ` modulo `M` with values in a `ℚ`-algebra and `k ≥ 2`. -/
theorem sum_units_mul_primorialBernoulli {M : ℕ} [NeZero M] {k : ℕ} (hk : 2 ≤ k) {R : Type*}
    [CommRing R] [Algebra ℚ R] (ψ : DirichletCharacter R M) :
    ∑ u : (ZMod M)ˣ, ψ u * (primorialBernoulli M k u : R) =
      primorial (k + 1) * M * ψ.generalizedBernoulli k := by
  rw [generalizedBernoulli_eq_pow_mul_sum_bernoulli_eval _ hk, ψ.sum_mul_eq_sum_units, mul_sum,
    mul_sum]
  refine sum_congr rfl fun u _ ↦ ?_
  have h := congrArg (algebraMap ℚ R) (intCast_primorialBernoulli M k u)
  simp only [map_intCast, map_mul, map_pow, map_natCast] at h
  have hMk : (M : R) ^ k = M ^ (k - 1) * M := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  rw [hMk] at h
  rw [h]
  ring

/-- The entries `2 Pₖ₊₁ Mᵏ Bₖ(⟨u⟩ / M)` of the Bernoulli group matrix of `(ZMod M)ˣ`, corrected at
`u = ±1` so that the characters of the wrong parity get the eigenvalue `±2`
(`TauCeti.sum_mul_bernoulliGroupEntry`). -/
noncomputable def bernoulliGroupEntry (M k : ℕ) (u : (ZMod M)ˣ) : ℤ :=
  2 * primorialBernoulli M k u + (if u = 1 then -(-1) ^ k else 0) + if u = -1 then 1 else 0

/-- The value of a Bernoulli group entry: `2 Pₖ₊₁ Mᵏ Bₖ(⟨u⟩ / M)`, minus `(-1)ᵏ` at `u = 1` and
plus `1` at `u = -1`. -/
theorem bernoulliGroupEntry_def (M k : ℕ) (u : (ZMod M)ˣ) :
    bernoulliGroupEntry M k u =
      2 * primorialBernoulli M k u + (if u = 1 then -(-1) ^ k else 0) +
        if u = -1 then 1 else 0 :=
  (rfl)

/-- **The Bernoulli group determinant** of `(ZMod M)ˣ`: the determinant of the group matrix
`(e(t / s))_{s,t}` of the corrected Bernoulli entries `e = TauCeti.bernoulliGroupEntry M k`. For
`k ≥ 2` it is nonzero (`TauCeti.bernoulliGroupDet_ne_zero`) and divisible by `Pₖ₊₁ M Bₖ,ψ` for
every character `ψ` of parity `(-1)ᵏ` (`TauCeti.exists_mem_adjoin_bernoulliGroupDet_eq`). -/
noncomputable def bernoulliGroupDet (M : ℕ) [NeZero M] (k : ℕ) : ℤ :=
  (of fun s t : (ZMod M)ˣ ↦ bernoulliGroupEntry M k (t / s)).det

/-- The eigenvalue of a homomorphism `χ : (ZMod M)ˣ →* R` on the Bernoulli group matrix is
`2 ∑ᵤ χ(u) Pₖ₊₁ Mᵏ Bₖ(⟨u⟩ / M) - (-1)ᵏ + χ(-1)`. -/
theorem sum_mul_bernoulliGroupEntry {M : ℕ} [NeZero M] {R : Type*} [CommRing R]
    (χ : (ZMod M)ˣ →* R) (k : ℕ) :
    ∑ u, χ u * (bernoulliGroupEntry M k u : R) =
      2 * ∑ u, χ u * (primorialBernoulli M k u : R) - (-1) ^ k + χ (-1) := by
  simp [bernoulliGroupEntry_def, mul_add, sum_add_distrib, mul_sum, mul_left_comm, sub_eq_add_neg]

/-- The Bernoulli group determinant, cast to a ring `S`, is the determinant of the cast entries. -/
theorem intCast_bernoulliGroupDet (M : ℕ) [NeZero M] (k : ℕ) (S : Type*) [CommRing S] :
    (bernoulliGroupDet M k : S) =
      (of fun s t : (ZMod M)ˣ ↦ (bernoulliGroupEntry M k (t / s) : S)).det := by
  rw [bernoulliGroupDet, ← eq_intCast (Int.castRingHom S), RingHom.map_det]
  refine congrArg Matrix.det (Matrix.ext fun s t ↦ ?_)
  simp [RingHom.mapMatrix_apply]

/-- **The Bernoulli group determinant is nonzero** for `k ≥ 2`: over `ℂ`, the eigenvalue of a
character of parity `(-1)ᵏ` is `2 Pₖ₊₁ M Bₖ,χ ≠ 0`, and that of a character of the other parity
is `-2 (-1)ᵏ`. -/
theorem bernoulliGroupDet_ne_zero (M : ℕ) [NeZero M] {k : ℕ} (hk : 2 ≤ k) :
    bernoulliGroupDet M k ≠ 0 := by
  have hC : (of fun s t : (ZMod M)ˣ ↦ (bernoulliGroupEntry M k (t / s) : ℂ)).det ≠ 0 := by
    refine (det_of_div_ne_zero_iff fun u ↦ (bernoulliGroupEntry M k u : ℂ)).2 fun χ ↦ ?_
    have h := sum_mul_bernoulliGroupEntry ((χ : ZMod M →* ℂ).comp (Units.coeHom (ZMod M))) k
    simp only [MulChar.coe_comp_coeHom_apply, Units.val_neg, Units.val_one] at h
    rw [h, sum_units_mul_primorialBernoulli hk χ]
    rcases χ.apply_neg_one_eq_neg_one_pow_or k with hχ | hχ
    · rw [hχ, sub_add_cancel]
      exact mul_ne_zero two_ne_zero (mul_ne_zero (mul_ne_zero (mod_cast primorial_ne_zero _)
        (mod_cast NeZero.ne M)) (generalizedBernoulli_ne_zero hk hχ))
    · rw [(generalizedBernoulli_eq_zero_iff hk).2 hχ, hχ]
      simp
  intro h0
  rw [← intCast_bernoulliGroupDet, h0, Int.cast_zero] at hC
  exact hC rfl

/-- **The Bernoulli group determinant is divisible by the Bernoulli numbers of one parity.** For
`k ≥ 2`, a `ℚ`-algebra `R` and a Dirichlet character `ψ` modulo `M` with values in `R` and
`ψ(-1) = (-1)ᵏ`, `TauCeti.bernoulliGroupDet M k = Pₖ₊₁ M Bₖ,ψ x` for some `x` in the subring
`ℤ[ψ]` generated by the values of `ψ`, where `Pₖ₊₁ = primorial (k + 1)` and `Bₖ,ψ` is the
generalized Bernoulli number at the modulus `M`. -/
theorem exists_mem_adjoin_bernoulliGroupDet_eq {M : ℕ} [NeZero M] {k : ℕ} (hk : 2 ≤ k)
    {R : Type*} [CommRing R] [Algebra ℚ R] (ψ : DirichletCharacter R M)
    (hψ : ψ (-1) = (-1) ^ k) :
    ∃ x ∈ Algebra.adjoin ℤ (Set.range ψ),
      (bernoulliGroupDet M k : R) = primorial (k + 1) * M * ψ.generalizedBernoulli k * x := by
  -- in `S = ℤ[ψ]`, the eigenvalue of `ψ` divides the determinant
  set S := Algebra.adjoin ℤ (Set.range ψ)
  let χ : (ZMod M)ˣ →* S := ((ψ : ZMod M →* R).comp (Units.coeHom (ZMod M))).codRestrict
    S.toSubmonoid fun u ↦ Algebra.subset_adjoin ⟨u, rfl⟩
  obtain ⟨y, hy⟩ := Matrix.sum_mul_dvd_det_of_div (fun u ↦ (bernoulliGroupEntry M k u : S)) χ
  refine ⟨2 * (y : R), S.mul_mem (S.natCast_mem 2) y.property, ?_⟩
  -- the eigenvalue of `ψ` is `2 Pₖ₊₁ M Bₖ,ψ`
  have h := congrArg S.val ((intCast_bernoulliGroupDet M k S).trans hy)
  rw [map_intCast, map_mul, sum_mul_bernoulliGroupEntry χ k] at h
  simp only [map_sum, map_mul, map_sub, map_add, map_pow, map_neg, map_one, map_ofNat,
    map_intCast, Subalgebra.coe_val, χ, MonoidHom.codRestrict_apply,
    MulChar.coe_comp_coeHom_apply, Units.val_neg, Units.val_one] at h
  rw [sum_units_mul_primorialBernoulli hk ψ, hψ] at h
  rw [h]
  ring

/-- **The eigenvalue factorization of the Bernoulli group determinant.** For `k ≥ 2` and a domain
`R` that is a `ℚ`-algebra with enough roots of unity, `TauCeti.bernoulliGroupDet M k` is the
product, over the Dirichlet characters `χ` modulo `M` with values in `R`, of
`2 Pₖ₊₁ M Bₖ,χ - (-1)ᵏ + χ(-1)`: this is `2 Pₖ₊₁ M Bₖ,χ` when `χ(-1) = (-1)ᵏ` and `-2 (-1)ᵏ`
otherwise. -/
theorem bernoulliGroupDet_eq_prod {M : ℕ} [NeZero M] {k : ℕ} (hk : 2 ≤ k) (R : Type*)
    [CommRing R] [IsDomain R] [Algebra ℚ R] [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod M)ˣ)] :
    (bernoulliGroupDet M k : R) = ∏ χ : DirichletCharacter R M,
      (2 * (primorial (k + 1) * M * χ.generalizedBernoulli k) - (-1) ^ k + χ (-1)) := by
  have : CharZero R := algebraRat.charZero R
  rw [intCast_bernoulliGroupDet, det_of_div_eq_prod fun u ↦ (bernoulliGroupEntry M k u : R)]
  refine prod_congr rfl fun χ _ ↦ ?_
  have h := sum_mul_bernoulliGroupEntry ((χ : ZMod M →* R).comp (Units.coeHom (ZMod M))) k
  simp only [MulChar.coe_comp_coeHom_apply, Units.val_neg, Units.val_one] at h
  rw [h, sum_units_mul_primorialBernoulli hk χ]

end TauCeti

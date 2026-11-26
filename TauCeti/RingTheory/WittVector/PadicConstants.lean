/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.RingTheory.WittVector.Compare
public import TauCeti.FieldTheory.Finite.FrobeniusFixed
public import TauCeti.RingTheory.WittVector.Frobenius

/-!
# `p`-adic and finite constants in Witt vectors

Let `k` be a domain of characteristic `p` (for instance a field). The inclusion `𝔽_p ⊆ k`
induces a ring homomorphism `ι_k : ℤ_[p] ≅ W(𝔽_p) → W(k)`, the *`p`-adic constants* of
`W(k)`. It is injective, natural in `k`, and its image is exactly the subring of Witt vectors
fixed by the Witt-vector Frobenius `σ`: since `σ` raises every Witt coordinate to its `p`-th
power, `σ x = x` says that every coordinate of `x` is a root of `X ^ p - X`, that is, lies in
`𝔽_p`.

For every ring `k` of characteristic `p`, reduction gives canonical finite constants
`ℤ/p^n → W(k)/p^n`. This map is injective because the `p`-adic constants reflect divisibility
by `p^n`, and its image is fixed by the induced Witt Frobenius.

As an application, if a matrix `T` over `W(k)` is conjugate to `σ(T)` over some faithful
`W(k)`-algebra `L` (for instance `L = W(k)[1/p]`), then its characteristic polynomial is fixed by
`σ` coefficientwise and so descends to a unique monic polynomial over `ℤ_[p]` of the same degree.
For a Dieudonné module over `𝔽_{p^a}` that is free over `W(𝔽_{p^a})`, the matrix `T` of the
linear map `F^a` satisfies this hypothesis with `B` the matrix of `F`, so the characteristic
polynomial of `F^a` has coefficients in `ℤ_p`.

## Main definitions and results

* `WittVector.mem_range_map_iff`: a Witt vector lies in the image of `W(f)` if and only if every
  coordinate lies in the image of `f`.
* `TauCeti.WittVector.padicConstants p k`: the homomorphism `ι_k : ℤ_[p] →+* W(k)`, with
  `TauCeti.WittVector.padicConstants_injective`, the naturality
  `TauCeti.WittVector.map_padicConstants` and the identification
  `TauCeti.WittVector.padicConstants_zmod` of `ι_{𝔽_p}` with `W(𝔽_p) ≅ ℤ_[p]`.
* `TauCeti.WittVector.constantsMod`: the canonical finite constants `ℤ/p^n → W(k)/p^n`, with
  reduction formula `TauCeti.WittVector.constantsMod_toZModPow` and Frobenius invariance
  `TauCeti.WittVector.frobeniusMod_constantsMod`.
* `TauCeti.WittVector.padicConstants_mem_span_pow_iff`: the `p`-adic constants reflect
  divisibility by `p^n`, yielding `TauCeti.WittVector.constantsMod_injective`.
* `TauCeti.WittVector.frobenius_eq_self_iff` and `TauCeti.WittVector.range_padicConstants`:
  the Frobenius-fixed Witt vectors are exactly the `p`-adic constants.
* `TauCeti.WittVector.map_frobenius_eq_self_iff_mem_lifts`: the same for polynomials.
* `TauCeti.WittVector.exists_padic_charpoly`: the characteristic polynomial of a matrix that is
  `σ`-conjugation invariant over a faithful `W(k)`-algebra descends uniquely to a monic polynomial
  over `ℤ_[p]` of the same degree.

## References

* R. Lipnowski and J. Tsimerman, *How large is A_g(𝔽_q)?*, Duke Math. J. 167 (2018),
  arXiv:1511.02212, §§2–3: the Dieudonné modules with `W(𝔽_q)`-coefficients in which these
  statements are used.
-/

public section

noncomputable section

open scoped Polynomial

namespace WittVector

variable {p : ℕ} [Fact p.Prime] {R S : Type*} [CommRing R] [CommRing S]

local notation "𝕎" => WittVector p

/-- A Witt vector lies in the image of `WittVector.map f` if and only if each of its coordinates
lies in the image of `f`. -/
theorem mem_range_map_iff (f : R →+* S) (x : 𝕎 S) :
    x ∈ Set.range (map f) ↔ ∀ n, x.coeff n ∈ Set.range f := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨y, rfl⟩ n
    exact ⟨y.coeff n, (map_coeff f y n).symm⟩
  · choose c hc using h
    exact ⟨mk p c, ext fun n ↦ by rw [map_coeff, coeff_mk, hc]⟩

end WittVector

namespace TauCeti.WittVector

open _root_.WittVector

variable (p : ℕ) [Fact p.Prime] (k : Type*) [CommRing k] [CharP k p]

local notation "𝕎" => _root_.WittVector p

/-- The *`p`-adic constants* `ι_k : ℤ_[p] →+* W(k)` of the Witt vectors of a ring `k` of
characteristic `p`: the identification `ℤ_[p] ≅ W(𝔽_p)` followed by the map of Witt vectors
induced by `𝔽_p → k`. -/
def padicConstants : ℤ_[p] →+* 𝕎 k :=
  (map (ZMod.castHom dvd_rfl k)).comp (equiv p).symm.toRingHom

variable {p k}

/-- The `p`-adic constant of `z` is the image under `W(𝔽_p → k)` of the Witt vector over `𝔽_p`
corresponding to `z`. -/
theorem padicConstants_apply (z : ℤ_[p]) :
    padicConstants p k z = map (ZMod.castHom dvd_rfl k) ((equiv p).symm z) := by
  rw [padicConstants, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]

/-- The `p`-adic constants of `W(𝔽_p)` are the identification `ℤ_[p] ≅ W(𝔽_p)` itself. -/
@[simp]
theorem padicConstants_zmod (z : ℤ_[p]) : padicConstants p (ZMod p) z = (equiv p).symm z := by
  rw [padicConstants_apply, RingHom.ext_zmod (ZMod.castHom dvd_rfl (ZMod p)) (RingHom.id _), map_id,
    RingHom.id_apply]

/-- The `p`-adic constants are natural in the ring of coefficients. -/
@[simp]
theorem map_padicConstants {k' : Type*} [CommRing k'] [CharP k' p] (f : k →+* k')
    (z : ℤ_[p]) : map f (padicConstants p k z) = padicConstants p k' z := by
  refine ext fun n ↦ ?_
  simp only [padicConstants_apply, map_coeff]
  rw [← RingHom.comp_apply, RingHom.ext_zmod (f.comp (ZMod.castHom dvd_rfl k))
    (ZMod.castHom dvd_rfl k')]

/-- The `p`-adic constants of a nontrivial ring of characteristic `p` are injective. -/
theorem padicConstants_injective [Nontrivial k] :
    Function.Injective (padicConstants p k) :=
  fun _ _ h ↦ (equiv p).symm.injective <| map_injective _ (ZMod.castHom dvd_rfl k).injective <| by
    simpa only [padicConstants_apply] using h

/-- The image of the `p`-adic constants consists of the Witt vectors all of whose coordinates lie
in the prime subring `𝔽_p`. -/
theorem range_padicConstants_eq_range_map :
    Set.range (padicConstants p k) = Set.range (map (ZMod.castHom dvd_rfl k)) := by
  rw [← (equiv p).symm.surjective.range_comp]
  exact congrArg Set.range (funext padicConstants_apply)

/-- The `p`-adic constants are fixed by the Witt-vector Frobenius. -/
@[simp]
theorem frobenius_padicConstants (z : ℤ_[p]) :
    frobenius (padicConstants p k z) = padicConstants p k z := by
  rw [frobenius_eq_self_iff_forall_coeff]
  intro n
  rw [padicConstants_apply, map_coeff, ← map_pow, ZMod.pow_card]

section FiniteConstants

variable (p k)

local notation "W" => _root_.WittVector p k

/-- The canonical finite constants `ℤ/p^n → W(k)/p^n`, obtained by reducing the p-adic constants.
This definition also applies to `n = 0`. -/
def constantsMod (n : ℕ) : ZMod (p ^ n) →+* W ⧸ Ideal.span {(p : W) ^ n} :=
  (Ideal.Quotient.lift (RingHom.ker (PadicInt.toZModPow n))
    ((Ideal.Quotient.mk _).comp (padicConstants p k)) <| by
      intro z hz
      rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hz
      simpa only [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_span_singleton, map_pow, map_natCast] using
        map_dvd (padicConstants p k) hz).comp
    (RingHom.quotientKerEquivOfSurjective
      (ZMod.ringHom_surjective (PadicInt.toZModPow n))).symm.toRingHom

/-- Finite constants commute with reduction of p-adic integers. -/
@[simp]
theorem constantsMod_toZModPow (n : ℕ) (z : ℤ_[p]) :
    constantsMod p k n (PadicInt.toZModPow n z) =
      Ideal.Quotient.mk _ (padicConstants p k z) := by
  simp [constantsMod, RingHom.quotientKerEquivOfSurjective_symm_apply,
    Ideal.Quotient.lift_mk]

/-- Frobenius fixes the canonical finite constants. -/
@[simp]
theorem frobeniusMod_constantsMod (n : ℕ) (z : ZMod (p ^ n)) :
    frobeniusMod p k n (constantsMod p k n z) = constantsMod p k n z := by
  obtain ⟨z, rfl⟩ := ZMod.ringHom_surjective (PadicInt.toZModPow n) z
  simp

variable {p k}

/-- A p-adic constant is divisible by `p^n` in `W(k)` exactly when it is divisible by `p^n`
in `ℤ_p`. -/
theorem padicConstants_mem_span_pow_iff (n : ℕ) (z : ℤ_[p]) :
    padicConstants p k z ∈ Ideal.span {(p : W) ^ n} ↔
      z ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by
  have : Nontrivial k := CharP.nontrivial_of_char_ne_one (Fact.out : p.Prime).ne_one
  constructor
  · intro hz
    have he : (equiv p).symm z ∈ Ideal.span {(p : _root_.WittVector p (ZMod p)) ^ n} := by
      obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hz
      rw [mem_span_p_pow_iff_le_coeff_eq_zero]
      intro i hi
      apply (ZMod.castHom dvd_rfl k).injective
      have hz := mul_pow_charP_coeff_zero u hi
      rw [hu] at hz
      simpa only [padicConstants_apply, map_coeff, map_zero] using hz
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp he
    rw [Ideal.mem_span_singleton]
    exact ⟨equiv p y, by simpa using congrArg (equiv p) hy⟩
  · intro hz
    simpa only [Ideal.mem_span_singleton, map_pow, map_natCast] using
      map_dvd (padicConstants p k) (Ideal.mem_span_singleton.mp hz)

/-- Over a ring of characteristic `p`, the finite constants embed in `W(k)/p^n`. -/
theorem constantsMod_injective (n : ℕ) :
    Function.Injective (constantsMod p k n) := by
  apply (injective_iff_map_eq_zero _).2
  intro z hz
  obtain ⟨z, rfl⟩ := ZMod.ringHom_surjective (PadicInt.toZModPow n) z
  rw [constantsMod_toZModPow, Ideal.Quotient.eq_zero_iff_mem,
    padicConstants_mem_span_pow_iff] at hz
  rwa [← PadicInt.ker_toZModPow, RingHom.mem_ker] at hz

end FiniteConstants

variable [IsDomain k]

/-- **Frobenius-fixed Witt vectors are the `p`-adic integers.** Over a domain `k` of
characteristic `p`, a Witt vector is fixed by the Witt-vector Frobenius if and only if it is a
`p`-adic constant. The constant is unique by `TauCeti.WittVector.padicConstants_injective`. -/
theorem frobenius_eq_self_iff {x : 𝕎 k} :
    frobenius x = x ↔ x ∈ Set.range (padicConstants p k) := by
  let := ZMod.algebra k p
  rw [frobenius_eq_self_iff_forall_coeff, range_padicConstants_eq_range_map, mem_range_map_iff]
  refine forall_congr' fun n ↦ ?_
  have h := FiniteField.pow_card_eq_self_iff_mem_range_algebraMap (K := ZMod p) (x.coeff n)
  rwa [ZMod.card, RingHom.ext_zmod (algebraMap (ZMod p) k) (ZMod.castHom dvd_rfl k)] at h

/-- Over a domain of characteristic `p`, the subring of Frobenius-fixed Witt vectors is the image
of the `p`-adic constants. -/
theorem range_padicConstants :
    (padicConstants p k).range = (frobenius : 𝕎 k →+* 𝕎 k).eqLocus (RingHom.id _) := by
  ext x
  simp [frobenius_eq_self_iff]

/-- A polynomial over `W(k)` is fixed coefficientwise by the Witt-vector Frobenius if and only if
it comes from a polynomial over `ℤ_[p]` along the `p`-adic constants. -/
theorem map_frobenius_eq_self_iff_mem_lifts {f : (𝕎 k)[X]} :
    f.map (frobenius : 𝕎 k →+* 𝕎 k) = f ↔ f ∈ Polynomial.lifts (padicConstants p k) := by
  rw [Polynomial.lifts_iff_coeff_lifts]
  refine ⟨fun h n ↦ ?_, fun h ↦ ?_⟩
  · rw [← frobenius_eq_self_iff, ← Polynomial.coeff_map, h]
  · ext n : 2
    rw [Polynomial.coeff_map]
    exact frobenius_eq_self_iff.mpr (h n)

/-- **The characteristic polynomial of a `σ`-conjugation-invariant matrix descends to `ℤ_[p]`.**
Let `k` be a domain of characteristic `p` and `L` a faithful `W(k)`-algebra (for instance
`W(k)[1/p]`). If a square matrix `T` over `W(k)` satisfies `T = B σ(T) B⁻¹` over `L` for an
invertible matrix `B`, then its characteristic polynomial is the image of a unique monic
polynomial over `ℤ_[p]` of degree the size of `T`. -/
theorem exists_padic_charpoly {n : Type*} [Fintype n] [DecidableEq n] {L : Type*} [CommRing L]
    [Algebra (𝕎 k) L] [FaithfulSMul (𝕎 k) L] {T : Matrix n n (𝕎 k)} {B : (Matrix n n L)ˣ}
    (hT : T.map (algebraMap (𝕎 k) L) =
      B.val * (T.map frobenius).map (algebraMap (𝕎 k) L) * B⁻¹.val) :
    ∃! P : ℤ_[p][X], P.Monic ∧ P.natDegree = Fintype.card n ∧
      P.map (padicConstants p k) = T.charpoly := by
  have hinj := padicConstants_injective (p := p) (k := k)
  have hfix : T.charpoly.map (frobenius : 𝕎 k →+* 𝕎 k) = T.charpoly := by
    refine Polynomial.map_injective _ (FaithfulSMul.algebraMap_injective (𝕎 k) L) ?_
    rw [Polynomial.map_map, ← Matrix.charpoly_map, ← Matrix.charpoly_map, RingHom.coe_comp,
      ← Matrix.map_map, hT, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  obtain ⟨P, hP⟩ :=
    (Polynomial.lifts_iff_set_range _).mp (map_frobenius_eq_self_iff_mem_lifts.mp hfix)
  refine ⟨P, ⟨Polynomial.monic_of_injective hinj (hP ▸ T.charpoly_monic), ?_, hP⟩,
    fun Q hQ ↦ Polynomial.map_injective _ hinj (hQ.2.2.trans hP.symm)⟩
  rw [← Polynomial.natDegree_map_eq_of_injective hinj, hP, Matrix.charpoly_natDegree_eq_dim]

end TauCeti.WittVector

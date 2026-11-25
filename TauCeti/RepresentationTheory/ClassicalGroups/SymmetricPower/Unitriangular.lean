/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import TauCeti.RingTheory.MvPolynomial.PolynomialOperator
import TauCeti.Data.Nat.Factorial.NatCast
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection
import TauCeti.LinearAlgebra.PolynomialFamily
import TauCeti.RepresentationTheory.Subrepresentation
import TauCeti.RingTheory.MvPolynomial.Finrank

/-!
# Irreducibility of binary forms from finitely many unitriangular matrices

Let `K` be a field and `d` a natural number with every binomial coefficient `d choose n` nonzero
in `K`. This file shows that the binary forms of degree `d` over `K`, with `GL₂(K)` acting by the
substitution of standard vectors `TauCeti.polynomialAction`, have no proper nonzero subspace
stable under the unitriangular matrices `!![1, t; 0, 1]` and `!![1, 0; t, 1]` for `d + 1` distinct
values of `t`. Consequently a group mapping to `GL₂(K)` whose image contains these matrices acts
irreducibly on the forms of degree `d` (`TauCeti.isIrreducible_polynomialRep_comp`).

The point is that only finitely many rational points are used. Over `𝔽_ℓ` there are `ℓ` values of
`t`, and for `d < ℓ` no binomial coefficient `d choose n` is divisible by `ℓ`, so the forms of
degree `d < ℓ` restrict irreducibly to `SL₂(𝔽_ℓ)`. These are the symmetric powers
`Sym^d 𝔽_ℓ²` from which the Serre weights of `GL₂(ℤ_ℓ)` are made. For `d ≥ ℓ` the hypothesis on
the number of points fails, and indeed `Sym^d` of dimension `d + 1 > ℓ` is then reducible over
`SL₂(𝔽_ℓ)`, whose irreducible representations in characteristic `ℓ` have dimension at most `ℓ`.
This differs from the simplicity of the binary forms as rational representations of the algebraic
group `SL₂` in `TauCeti.SpecialLinear.isAtom_binaryForms`, which tests stability on the universal
unitriangular points over `K[t]`.

The proof expands the action of `!![1, t; 0, 1]` on a form `f` as a polynomial in `t` with
coefficients in the forms. Its values at `d + 1` points lie in a stable subspace `W`, so its
coefficients do (`TauCeti.mem_of_forall_sum_range_pow_smul_mem`); the coefficient of `tʲ`, for `j`
the largest exponent of `y` occurring in `f`, is a nonzero multiple of `xᵈ`. Expanding the action
of `!![1, 0; t, 1]` on `xᵈ = e_0` in the same way gives `(d choose k) e_k ∈ W` for every
`k ≤ d`, and these binary monomials span the forms of degree `d`.

## Main results

* `TauCeti.X_zero_pow_mem_of_polynomialAction_transvection_mem`: a subspace stable under
  `!![1, t; 0, 1]` for `d + 1` values of `t` and containing a nonzero form of degree `d` contains
  `xᵈ`.
* `TauCeti.exists_eq_smul_X_zero_pow_of_polynomialAction_transvection_eq`: a form of degree `d`
  fixed by `!![1, t; 0, 1]` for `d + 1` values of `t` is a multiple of `xᵈ`.
* `TauCeti.homogeneousSubmodule_le_of_polynomialAction_transvection_mem`: a subspace stable
  under both unitriangular families and containing a nonzero form of degree `d` contains every
  form of degree `d`.
* `TauCeti.isIrreducible_polynomialRep_comp`: the forms of degree `d` are an irreducible
  representation of any group whose image in `GL₂(K)` contains both unitriangular families.
* `TauCeti.isIrreducible_polynomialRep_comp_map`: the forms of degree `d` are an irreducible
  representation of `GL₂(R)` acting through `R →+* K`, when `d !` is nonzero in `K`.

## References

* J. L. Alperin, *Local Representation Theory*, Cambridge Studies in Advanced Mathematics 11
  (1986), §1: the simple modules of `SL₂(𝔽_ℓ)` on the homogeneous polynomials of degree
  `d < ℓ`, found through their vectors fixed by the unitriangular matrices.
-/

public section

open MvPolynomial Matrix

namespace TauCeti

variable {K : Type*} [Field K] {d : ℕ}

/-- The coefficient of `tᵏ` in the action of `!![1, t; 0, 1]` on a form `f` of degree `d`: the
form `∑ᵢ (i choose k) fᵢ e_(i-k)`, where `fᵢ` is the coefficient of `f` at `e_i`. -/
private noncomputable def upperCoeff (d k : ℕ) (f : MvPolynomial (Fin 2) K) :
    MvPolynomial (Fin 2) K :=
  ∑ i ∈ Finset.range (d + 1),
    (f.coeff (Finsupp.single 0 (d - i) + Finsupp.single 1 i) * i.choose k) •
      polynomialMonomial K d (i - k)

/-- The action of `!![1, t; 0, 1]` on a form of degree `d` is a polynomial of degree at most `d`
in `t`, with coefficients `upperCoeff d k f`. -/
private theorem polynomialAction_transvection_zero_one_eq_sum {f : MvPolynomial (Fin 2) K}
    (hf : f.IsHomogeneous d) (t : K) :
    polynomialAction (transvection (0 : Fin 2) 1 t) f =
      ∑ k ∈ Finset.range (d + 1), t ^ k • upperCoeff d k f := by
  conv_lhs => rw [← sum_coeff_smul_polynomialMonomial hf]
  simp only [map_sum, map_smul]
  rw [Finset.sum_congr rfl fun i hi ↦ by
    rw [polynomialAction_transvection_zero_one_polynomialMonomial t
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]]
  simp only [upperCoeff, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  ring_nf

/-- The constant term of the action of `!![1, t; 0, 1]` on `f` is `f`. -/
private theorem upperCoeff_zero {f : MvPolynomial (Fin 2) K} (hf : f.IsHomogeneous d) :
    upperCoeff d 0 f = f := by
  simpa [upperCoeff] using sum_coeff_smul_polynomialMonomial hf

/-- For a nonzero form `f` and `j` the largest exponent of `y` occurring in `f`, the coefficient
of `tʲ` in the action of `!![1, t; 0, 1]` on `f` is a nonzero multiple of `xᵈ`. -/
private theorem exists_upperCoeff_eq_smul {f : MvPolynomial (Fin 2) K} (hf : f.IsHomogeneous d)
    (hf0 : f ≠ 0) : ∃ j ≤ d, ∃ c : K, c ≠ 0 ∧ upperCoeff d j f = c • X 0 ^ d := by
  classical
  -- The coefficients of `f` against the binary monomials `e_i = x ^ (d - i) * y ^ i`.
  set c : ℕ → K := fun i ↦ f.coeff (Finsupp.single 0 (d - i) + Finsupp.single 1 i)
  have hcoeff (i : ℕ) : f.coeff (Finsupp.single 0 (d - i) + Finsupp.single 1 i) = c i := rfl
  have hne : ((Finset.range (d + 1)).filter (c · ≠ 0)).Nonempty := by
    by_contra h
    refine hf0 ?_
    rw [← sum_coeff_smul_polynomialMonomial hf]
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    by_cases hci : c i = 0
    · rw [hcoeff, hci, zero_smul]
    · exact (h ⟨i, Finset.mem_filter.mpr ⟨hi, hci⟩⟩).elim
  -- The largest exponent `j` of `y` occurring in `f`.
  set j := ((Finset.range (d + 1)).filter (c · ≠ 0)).max' hne
  obtain ⟨hjd, hj⟩ := Finset.mem_filter.mp (Finset.max'_mem _ hne)
  refine ⟨j, Nat.lt_succ_iff.mp (Finset.mem_range.mp hjd), c j, hj, ?_⟩
  rw [upperCoeff, Finset.sum_eq_single j, Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_self,
    polynomialMonomial_zero_right]
  · intro i hi hij
    rcases lt_or_gt_of_ne hij with h | h
    · rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero, mul_zero, zero_smul]
    · have hci : c i = 0 := by
        by_contra hci
        exact (Finset.le_max' _ i (Finset.mem_filter.mpr ⟨hi, hci⟩)).not_gt h
      rw [hcoeff, hci, zero_mul, zero_smul]
  · exact fun h ↦ (h hjd).elim

/-- **A stable subspace containing a nonzero form contains `xᵈ`.** Let `W` be a subspace of the
polynomials in `x = X 0` and `y = X 1` over a field, stable under `!![1, t; 0, 1]` for `d + 1`
distinct values `t = x i`. If `W` contains a nonzero form of degree `d`, then it contains `xᵈ`. No
assumption on the characteristic is needed. -/
theorem X_zero_pow_mem_of_polynomialAction_transvection_mem {x : Fin (d + 1) → K}
    (hx : Function.Injective x) {W : Submodule K (MvPolynomial (Fin 2) K)}
    (hu : ∀ i, ∀ f ∈ W, polynomialAction (transvection (0 : Fin 2) 1 (x i)) f ∈ W)
    {f : MvPolynomial (Fin 2) K} (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hfW : f ∈ W) :
    X 0 ^ d ∈ W := by
  obtain ⟨j, hjd, c, hc, hj⟩ := exists_upperCoeff_eq_smul hf hf0
  have hjW : upperCoeff d j f ∈ W := mem_of_forall_sum_range_pow_smul_mem W hx
    (fun i ↦ polynomialAction_transvection_zero_one_eq_sum hf (x i) ▸ hu i f hfW)
    (Nat.lt_succ_of_le hjd)
  rw [hj] at hjW
  exact (W.smul_mem_iff hc).mp hjW

/-- **The forms fixed by enough upper unitriangular matrices are the multiples of `xᵈ`.** A form
of degree `d` over a field fixed by `!![1, t; 0, 1]` for `d + 1` distinct values `t = x i` is a
scalar multiple of `xᵈ`. No assumption on the characteristic is needed. -/
theorem exists_eq_smul_X_zero_pow_of_polynomialAction_transvection_eq {x : Fin (d + 1) → K}
    (hx : Function.Injective x) {f : MvPolynomial (Fin 2) K} (hf : f.IsHomogeneous d)
    (hfix : ∀ i, polynomialAction (transvection (0 : Fin 2) 1 (x i)) f = f) :
    ∃ c : K, f = c • X 0 ^ d := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨0, by rw [zero_smul]⟩
  obtain ⟨j, hjd, c, hc, hj⟩ := exists_upperCoeff_eq_smul hf hf0
  -- The nonconstant coefficients in `t` of the action on `f` vanish.
  have hzero : upperCoeff d j f - (if j = 0 then f else 0) ∈ (⊥ : Submodule K _) := by
    refine mem_of_forall_sum_range_pow_smul_mem ⊥ hx (u := fun k ↦
      upperCoeff d k f - if k = 0 then f else 0) (fun i ↦ ?_) (Nat.lt_succ_of_le hjd)
    simp [smul_sub, Finset.sum_sub_distrib, smul_ite, ←
      polynomialAction_transvection_zero_one_eq_sum hf, hfix]
  rcases eq_or_ne j 0 with rfl | hj0
  · exact ⟨c, (upperCoeff_zero hf).symm.trans hj⟩
  · simp only [hj0, ↓reduceIte, sub_zero, Submodule.mem_bot, hj, smul_eq_zero] at hzero
    exact (hzero.resolve_left hc |> pow_ne_zero d (X_ne_zero 0)).elim

/-- **A stable subspace containing `xᵈ` contains every binary monomial of degree `d`.** If `W` is
stable under `!![1, 0; t, 1]` for `d + 1` distinct values `t = x i` and contains `xᵈ`, then it
contains `(d choose i) x ^ (d - i) * y ^ i`, hence `x ^ (d - i) * y ^ i` when `d choose i` is
nonzero in the field. -/
theorem polynomialMonomial_mem_of_X_zero_pow_mem {x : Fin (d + 1) → K}
    (hx : Function.Injective x) {W : Submodule K (MvPolynomial (Fin 2) K)}
    (hl : ∀ i, ∀ f ∈ W, polynomialAction (transvection (1 : Fin 2) 0 (x i)) f ∈ W)
    (h0 : (X 0 ^ d : MvPolynomial (Fin 2) K) ∈ W) {i : ℕ} (hi : i ≤ d)
    (hdi : (d.choose i : K) ≠ 0) : polynomialMonomial K d i ∈ W := by
  have hexp (t : K) :
      polynomialAction (transvection (1 : Fin 2) 0 t) (X 0 ^ d) =
        ∑ k ∈ Finset.range (d + 1), t ^ k • ((d.choose k : K) • polynomialMonomial K d k) := by
    rw [← polynomialMonomial_zero_right, polynomialAction_transvection_one_zero_polynomialMonomial
      t (Nat.zero_le d)]
    simp only [Nat.sub_zero, zero_add, smul_smul, mul_comm]
  exact (W.smul_mem_iff hdi).mp <| mem_of_forall_sum_range_pow_smul_mem W hx
    (u := fun k ↦ (d.choose k : K) • polynomialMonomial K d k) (fun i ↦ hexp (x i) ▸ hl i _ h0)
    (Nat.lt_succ_of_le hi)

/-- **A subspace stable under both unitriangular families is zero or contains all forms.** Let
every `d choose n` be nonzero in the field `K`, and let `W` be a subspace of `K[x, y]` stable
under `!![1, t; 0, 1]` and `!![1, 0; t, 1]` for `d + 1` distinct values `t = x i`. If `W` contains
a nonzero form of degree `d`, it contains every form of degree `d`. -/
theorem homogeneousSubmodule_le_of_polynomialAction_transvection_mem
    (hd : ∀ n ≤ d, (d.choose n : K) ≠ 0) {x : Fin (d + 1) → K} (hx : Function.Injective x)
    {W : Submodule K (MvPolynomial (Fin 2) K)}
    (hu : ∀ i, ∀ f ∈ W, polynomialAction (transvection (0 : Fin 2) 1 (x i)) f ∈ W)
    (hl : ∀ i, ∀ f ∈ W, polynomialAction (transvection (1 : Fin 2) 0 (x i)) f ∈ W)
    {f : MvPolynomial (Fin 2) K} (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hfW : f ∈ W) :
    homogeneousSubmodule (Fin 2) K d ≤ W := by
  have h0 := X_zero_pow_mem_of_polynomialAction_transvection_mem hx hu hf hf0 hfW
  intro g hg
  rw [← sum_coeff_smul_polynomialMonomial hg]
  refine W.sum_mem fun i hi ↦ W.smul_mem _ ?_
  have hi : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  exact polynomialMonomial_mem_of_X_zero_pow_mem hx hl h0 hi (hd i hi)

/-- **Irreducibility of the binary forms from finitely many unitriangular matrices.** Let every
`d choose n` be nonzero in the field `K`, and let `φ : G →* GL₂(K)` be a monoid homomorphism whose
image contains `!![1, t; 0, 1]` and `!![1, 0; t, 1]` for `d + 1` distinct values `t = x i`. Then
`G` acts irreducibly on the binary forms of degree `d` through `φ`. -/
theorem isIrreducible_polynomialRep_comp {G : Type*} [Monoid G] (φ : G →* GL (Fin 2) K)
    (hd : ∀ n ≤ d, (d.choose n : K) ≠ 0) {x : Fin (d + 1) → K} (hx : Function.Injective x)
    (hu : ∀ i, ∃ g, (φ g : Matrix (Fin 2) (Fin 2) K) = transvection 0 1 (x i))
    (hl : ∀ i, ∃ g, (φ g : Matrix (Fin 2) (Fin 2) K) = transvection 1 0 (x i)) :
    Representation.IsIrreducible ((polynomialRep (Fin 2) K d).comp φ) := by
  have : Nontrivial (homogeneousSubmodule (Fin 2) K d) := Module.nontrivial_of_finrank_pos
    (R := K) (by rw [finrank_homogeneousSubmodule_fin_two]; omega)
  refine ⟨fun σ ↦ (eq_or_ne σ ⊥).imp_right fun hσ ↦ ?_⟩
  -- The subrepresentation `σ`, as a subspace of the ambient polynomial ring.
  set W := σ.toSubmodule.map (homogeneousSubmodule (Fin 2) K d).subtype
  have hstable {t : Matrix (Fin 2) (Fin 2) K} (ht : ∃ g, (φ g : Matrix (Fin 2) (Fin 2) K) = t)
      (f : MvPolynomial (Fin 2) K) (hf : f ∈ W) : polynomialAction t f ∈ W := by
    obtain ⟨g, rfl⟩ := ht
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hf
    exact Submodule.mem_map.mpr ⟨_, σ.apply_mem_toSubmodule g hp, by simp⟩
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot fun h ↦
    hσ (Subrepresentation.toSubmodule_injective (h.trans Subrepresentation.toSubmodule_bot.symm))
  have hle := homogeneousSubmodule_le_of_polynomialAction_transvection_mem hd hx
    (fun i ↦ hstable (hu i)) (fun i ↦ hstable (hl i)) p.property
    (fun h ↦ hp0 (Subtype.ext h)) (Submodule.mem_map_of_mem hp)
  refine Subrepresentation.toSubmodule_injective (eq_top_iff.mpr fun q _ ↦ ?_)
  obtain ⟨q', hq', hqq⟩ := Submodule.mem_map.mp (hle q.property)
  rwa [Subtype.ext hqq] at hq'

/-- **The binary forms of degree `d` are an irreducible representation of `GL₂(R)`** acting
through any ring homomorphism `R →+* K` to a field in which `d !` is nonzero, that is, of
characteristic zero or greater than `d`. For instance the reduction `GL₂(ℤ_ℓ) → GL₂(𝔽_ℓ)` gives an
irreducible representation of `GL₂(ℤ_ℓ)` on `Sym^d 𝔽_ℓ²` for every `d < ℓ`. The proof applies
`TauCeti.isIrreducible_polynomialRep_comp` to the unitriangular matrices with parameters
`0, …, d`. -/
theorem isIrreducible_polynomialRep_comp_map {R : Type*} [CommRing R] (f : R →+* K)
    (hd : (d.factorial : K) ≠ 0) :
    Representation.IsIrreducible
      ((polynomialRep (Fin 2) K d).comp (GeneralLinearGroup.map f)) := by
  refine isIrreducible_polynomialRep_comp _ (fun n hn h ↦ hd ?_)
    (injective_natCast_fin_of_factorial_ne_zero hd)
    (fun i ↦ ⟨transvectionUnit (i := 0) (j := 1) (by decide) (i : R), by simp⟩)
    (fun i ↦ ⟨transvectionUnit (i := 1) (j := 0) (by decide) (i : R), by simp⟩)
  rw [← Nat.choose_mul_factorial_mul_factorial hn, Nat.cast_mul, Nat.cast_mul, h, zero_mul,
    zero_mul]

end TauCeti

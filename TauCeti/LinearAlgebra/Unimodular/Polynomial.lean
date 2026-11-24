/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Monic
public import TauCeti.LinearAlgebra.Unimodular.Extension
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import TauCeti.RingTheory.Polynomial.Monic.LocalRing

/-!
# Horrocks' theorem over a local ring

Let `B` be a local ring and `f : ι → B[X]` a unimodular vector of polynomials (its entries
generate the unit ideal of `B[X]`) one of whose entries has a unit leading coefficient, for
instance is monic. Horrocks' theorem says that `f` is the first column of an invertible matrix
over `B[X]`: it is equivalent to every standard basis vector
(`TauCeti.unimodularEquiv_single_of_isUnit_leadingCoeff`). Equivalently, `f` is equivalent to the
vector `f(0)` of its constant terms (`TauCeti.unimodularEquiv_C_eval_zero_of_isLocalRing`).

This is the local case of Horrocks' theorem for an integral domain `B`, which Quillen's patching
argument deduces from it by localising at the maximal ideals of `B`: a unimodular vector over
`B[X]` with a monic entry is equivalent to the vector of its constant terms. That theorem is the
inductive step in the Quillen–Suslin theorem, and in its rigid-analytic version over
Monsky–Washnitzer algebras.

The proof inducts on the degree `d` of the entry `f i` with unit leading coefficient, made monic
by a unit rescaling. When `d = 0` the entry is a unit. Otherwise, reduce the other entries modulo
`f i`, so that they have degree less than `d`. Over the residue field the vector stays
unimodular while `f i` does not become a unit, so some other entry `f k` has a unit coefficient,
and then the ideal `(f i, f k)` contains a monic polynomial `h` of degree `d - 1`
(`Polynomial.exists_monic_mem_span_pair`). With a third entry `f l` at hand, either `f l` or
`f l + h` has a unit coefficient at `d - 1`, since the coefficients at `d - 1` of the two differ
by `1`. That entry has degree `d - 1` and unit leading coefficient. With only two entries, every
unimodular vector is equivalent to a standard basis vector anyway.

## Main results

* `TauCeti.unimodularEquiv_single_of_isUnit_leadingCoeff`: over a local ring `B`, a unimodular
  vector over `B[X]` with an entry of unit leading coefficient is equivalent to every standard
  basis vector; `TauCeti.unimodularEquiv_single_of_monic`: in particular when that entry is monic.
* `TauCeti.unimodularEquiv_C_eval_zero_of_isLocalRing`: such a vector is equivalent to the vector
  of its constant terms.

## References

* S. Lang, *Algebra*, 3rd ed., GTM 211, Springer, 2002, Chapter XXI, §3, the local case in the
  proof of Theorem 3.4.
* G. Horrocks, *Projective modules over an extension of a local ring*, Proc. London Math. Soc.
  (3) 14 (1964), 714–718.
-/

public section

noncomputable section

open Module Polynomial

namespace TauCeti

variable {B ι : Type*} [CommRing B] [IsLocalRing B] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Over a local ring, if `g` is unimodular over `B[X]` and its entry `g i` is monic of positive
degree, some other entry has a unit coefficient: otherwise `g i` would become a unit modulo the
maximal ideal. -/
private theorem exists_ne_isUnit_coeff [Finite ι] {g : ι → B[X]} (hg : IsUnimodular B[X] g) {i : ι}
    (hi : (g i).Monic) (hd : (g i).natDegree ≠ 0) : ∃ k ≠ i, ∃ n, IsUnit ((g k).coeff n) := by
  have := Fintype.ofFinite ι
  by_contra! h
  let φ : B[X] →+* (IsLocalRing.ResidueField B)[X] := mapRingHom (IsLocalRing.residue B)
  have hzero : ∀ k ≠ i, φ (g k) = 0 := fun k hk ↦ by
    ext n
    simpa [φ, IsLocalRing.residue_eq_zero_iff] using h k hk n
  obtain ⟨b, hb⟩ := TauCeti.Module.isUnimodular_pi_iff.mp (hg.ringHom_comp φ)
  rw [Finset.sum_eq_single i (fun k _ hk ↦ by simp [hzero k hk]) (by simp)] at hb
  have h1 := (hi.map (IsLocalRing.residue B)).eq_one_of_isUnit (IsUnit.of_mul_eq_one _ hb)
  exact hd (by rw [← hi.natDegree_map (IsLocalRing.residue B), h1, natDegree_one])

/-- The induction step of Horrocks' theorem: if `g i` is monic of degree `d + 1`, the other
entries of `g` have degree at most `d`, and some other entry `g k` has a unit coefficient, then
`g` is equivalent to a vector with an entry of degree `d` and unit leading coefficient, unless
`ι` has exactly two elements. -/
private theorem exists_unimodularEquiv_isUnit_leadingCoeff {g : ι → B[X]} {i k : ι} {d : ℕ}
    (hi : (g i).Monic) (hid : (g i).natDegree = d + 1) (hdeg : ∀ l ≠ i, (g l).natDegree ≤ d)
    (hki : k ≠ i) {n : ℕ} (hk : IsUnit ((g k).coeff n)) :
    Fintype.card ι = 2 ∨ ∃ g' l, UnimodularEquiv g g' ∧ (g' l).natDegree = d ∧
      IsUnit (g' l).leadingCoeff := by
  by_cases hl : ∃ l, l ≠ i ∧ l ≠ k
  swap
  · -- Only the indices `i` and `k` exist.
    push Not at hl
    left
    rw [← Finset.card_univ, ← Finset.card_pair hki.symm]
    refine congrArg Finset.card (Finset.eq_univ_of_forall fun l ↦ ?_).symm
    by_cases hli : l = i
    · simp [hli]
    · simp [hl l hli]
  right
  obtain ⟨l, hli, hlk⟩ := hl
  -- A monic polynomial `h = a * g i + b * g k` of degree `d`.
  obtain ⟨h, hI, hmon, hhd⟩ := exists_monic_mem_span_pair hi
    (degree_lt_degree (by rw [hid]; exact Nat.lt_succ_of_le (hdeg k hki))) hk
  obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hI
  rw [hid, Nat.add_right_cancel_iff] at hhd
  have hgl := hdeg l hli
  -- Either `g l` or `g l + h` has a unit coefficient at `d`.
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add
    (a := (g l).coeff d + 1) (b := -(g l).coeff d) (by simp) with hc | hc
  · let ψ : (ι → B[X]) →ₗ[B[X]] B[X] := a • LinearMap.proj i + b • LinearMap.proj k
    have hψ : ψ (Pi.single l 1) = 0 := by simp [ψ, Pi.single_eq_of_ne hli.symm,
      Pi.single_eq_of_ne hlk.symm]
    refine ⟨g + ψ g • Pi.single l 1, l, UnimodularEquiv.self_add_smul ψ hψ g, ?_⟩
    have hval : (g + ψ g • Pi.single l 1 : ι → B[X]) l = g l + (a * g i + b * g k) := by
      simp [ψ]
    have hdeg' : (g l + (a * g i + b * g k)).natDegree ≤ d :=
      natDegree_add_le_of_degree_le hgl hhd.le
    have hcoeff : (g l + (a * g i + b * g k)).coeff d = (g l).coeff d + 1 := by
      rw [coeff_add, ← hhd, hmon.coeff_natDegree]
    rw [hval]
    have hnd := natDegree_eq_of_le_of_coeff_ne_zero hdeg' (hcoeff ▸ hc.ne_zero)
    exact ⟨hnd, by rwa [leadingCoeff, hnd, hcoeff]⟩
  · rw [IsUnit.neg_iff] at hc
    have hnd := natDegree_eq_of_le_of_coeff_ne_zero hgl hc.ne_zero
    exact ⟨g, l, .rfl, hnd, by rwa [leadingCoeff, hnd]⟩

/-- **Horrocks' theorem over a local ring.** Over a local ring `B`, a unimodular vector of
polynomials `f : ι → B[X]` one of whose entries has a unit leading coefficient is equivalent to
every standard basis vector: it is the `j`-th column of an invertible matrix over `B[X]`. -/
theorem unimodularEquiv_single_of_isUnit_leadingCoeff {f : ι → B[X]} (hf : IsUnimodular B[X] f)
    {i : ι} (hi : IsUnit (f i).leadingCoeff) (j : ι) : UnimodularEquiv f (Pi.single j 1) := by
  -- Strong induction on the degree of the entry with unit leading coefficient.
  induction hd : (f i).natDegree using Nat.strong_induction_on generalizing f i with
  | _ d ih => ?_
  -- Rescale `f` by the unit `C u⁻¹`, `u` the leading coefficient of `f i`, to make `f i` monic.
  obtain ⟨U, hU⟩ : IsUnit (C (↑hi.unit⁻¹ : B)) := isUnit_C.mpr (Units.isUnit _)
  refine (UnimodularEquiv.units_smul_left U f).symm.trans ?_
  have hf₁ : IsUnimodular B[X] (U • f) :=
    (UnimodularEquiv.units_smul_left U f).isUnimodular_iff.mpr hf
  have hmon : (U • f) i = C (↑hi.unit⁻¹ : B) * f i := by rw [Pi.smul_apply, Units.smul_def, hU,
    smul_eq_mul]
  have hi₁ : ((U • f) i).Monic := by
    rw [hmon]
    exact monic_C_mul_of_mul_leadingCoeff_eq_one hi.val_inv_mul
  have hd₁ : ((U • f) i).natDegree = d := by
    rw [hmon, natDegree_C_mul_of_isUnit (Units.isUnit _), hd]
  generalize U • f = f at hf₁ hi₁ hd₁
  clear hU hmon hf hi hd
  obtain _ | d := d
  · -- A monic constant is `1`, a unit.
    exact unimodularEquiv_single_of_isUnit (hi₁.natDegree_eq_zero.mp hd₁ ▸ isUnit_one) j
  -- Reduce the other entries modulo the monic entry `f i`.
  let w : ι → B[X] := fun k ↦ if k = i then 0 else -(f k /ₘ f i)
  have hfg := UnimodularEquiv.self_add_smul (LinearMap.proj i) (w := w) (by simp [w]) f
  set g := f + (LinearMap.proj i : (ι → B[X]) →ₗ[B[X]] B[X]) f • w
  have hgi : g i = f i := by simp [g, w]
  have hgk : ∀ k ≠ i, g k = f k %ₘ f i := fun k hk ↦ by
    simp [g, w, hk, modByMonic_eq_sub_mul_div, sub_eq_add_neg]
  have hg : IsUnimodular B[X] g := hfg.isUnimodular_iff.mp hf₁
  have hdeg : ∀ k ≠ i, (g k).natDegree ≤ d := fun k hk ↦ by
    rw [hgk k hk, ← Nat.lt_add_one_iff, ← hd₁]
    exact natDegree_modByMonic_lt _ hi₁ fun h ↦ by simp [h] at hd₁
  rw [← hgi] at hi₁ hd₁
  obtain ⟨k, hki, n, hk⟩ := exists_ne_isUnit_coeff hg hi₁ (by rw [hd₁]; exact d.succ_ne_zero)
  refine hfg.trans ?_
  rcases exists_unimodularEquiv_isUnit_leadingCoeff hi₁ hd₁ hdeg hki hk with
    hcard | ⟨g', l, hgg', hl, hlu⟩
  · exact unimodularEquiv_single_of_card_eq_two hcard hg j
  · exact hgg'.trans (ih d d.lt_succ_self (hgg'.isUnimodular_iff.mp hg) hlu hl)

/-- **Horrocks' theorem over a local ring**, monic form: over a local ring `B`, a unimodular
vector of polynomials `f : ι → B[X]` with a monic entry is equivalent to every standard basis
vector. -/
theorem unimodularEquiv_single_of_monic {f : ι → B[X]} (hf : IsUnimodular B[X] f) {i : ι}
    (hi : (f i).Monic) (j : ι) : UnimodularEquiv f (Pi.single j 1) :=
  unimodularEquiv_single_of_isUnit_leadingCoeff hf (hi.leadingCoeff ▸ isUnit_one) j

/-- Over a local ring `B`, a unimodular vector of polynomials `f : ι → B[X]` one of whose entries
has a unit leading coefficient is equivalent to the vector `f(0)` of its constant terms. -/
theorem unimodularEquiv_C_eval_zero_of_isLocalRing {f : ι → B[X]} (hf : IsUnimodular B[X] f)
    {i : ι} (hi : IsUnit (f i).leadingCoeff) :
    UnimodularEquiv f (fun k ↦ C ((f k).eval 0)) := by
  -- The vector of constant terms is unimodular over the local ring `B`, so it has a unit entry.
  obtain ⟨k, hk⟩ := TauCeti.Module.isUnimodular_iff_exists_isUnit.mp
    (hf.ringHom_comp (evalRingHom 0))
  have hC : (C ∘ Pi.single k 1 : ι → B[X]) = Pi.single k 1 := by
    ext1 l
    by_cases hl : l = k
    · simp [hl]
    · simp [hl]
  have h0 : UnimodularEquiv (fun k ↦ C ((f k).eval 0)) (Pi.single k 1) := by
    simpa only [hC, Function.comp_def, coe_evalRingHom] using
      (unimodularEquiv_single_of_isUnit hk k).map C
  exact (unimodularEquiv_single_of_isUnit_leadingCoeff hf hi k).trans h0.symm

end TauCeti

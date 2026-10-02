/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.DegreeOneForm
public import TauCeti.Topology.Algebra.Group.Profinite.Free.ExponentSumKernel
import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.QInvariant

/-!
# The constrained span statement at the normal form `x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)`

Let `F = freeProP p (Fin n)` with `n` even, let `r` be the normal-form word
`TauCeti.demushkinWordNeTwo q n` on the generators of `F` with `p ∣ q`, and let `ρ ∈ gr_1(F)` be
its class. Throughout this file indices are the `0`-based indices of `Fin n`: `x_j = of j` is the
`j`-th generator, `ξ_j` its class in `gr_0(F)`, and `∂_j` is the partial derivative
`TauCeti.freeProP.degreeOneDeriv p (Fin n) j` at `x_j`; in these indices the word is
`r = x_0^q (x_0, x_1)(x_2, x_3) ⋯ (x_{n-2}, x_{n-1})`. The partial derivatives of `ρ` at the
generators other than `x_0` are `∂_{2a+1} ρ = -ξ_{2a}` whenever `2a + 1 < n`, and
`∂_{2a} ρ = ξ_{2a+1}` whenever `1 ≤ a` and `2a + 1 < n`
(`TauCeti.freeProP.degreeOneDeriv_gradedMk_demushkinWordNeTwo_odd`,
`TauCeti.freeProP.degreeOneDeriv_gradedMk_demushkinWordNeTwo_even`). So every generator class
`ξ_j` with `j ≠ 1` is a combination of these derivatives, which is the hypothesis of the
constrained span statement of `Free/ExponentSumKernel.lean` with `i₀ = 0` and `i₁ = 1`. The
conclusion is Labute's Lemma 3: for the kernel `X` of the exponent sum at `x_1` and every `m ≥ 1`,

  `gr_{m+1}(X) = δ_ρ(gr_m(X)^n) + T_{m+1}`,

where `T_{m+1}` is spanned by the `π^{m+1} ξ_j` with `j ≠ 1`. This is the span statement that the
uniqueness argument for the dyadic even-rank Demushkin groups with orientation image `U^[f]` runs
on: their relator `x₁^{2+2^f} (x₁, x₂)(x₃, x₄) ⋯` is this word at `p = 2` and `q = 2 + 2^f`, the
orientation is the exponent sum at `x_1` composed with `γ ↦ χ(x_1)^γ`, and the basis corrections
must be taken inside its kernel.

## Main results

* `TauCeti.freeProP.degreeOneDeriv_gradedMk_demushkinWordNeTwo_odd`,
  `TauCeti.freeProP.degreeOneDeriv_gradedMk_demushkinWordNeTwo_even`,
  `TauCeti.freeProP.degreeOneDeriv_gradedMk_demushkinWordNeTwo_zero`: the partial derivatives of
  the class of the word at the generators.
* `gradedPieceOf_exponentSumKer_demushkinWordNeTwo_eq_map_basisModificationDelta_sup` (in
  `TauCeti.freeProP`): the constrained span statement at this normal form.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §4,
  Lemmas 1–3 and the proof of Theorem 5.
-/

public section

namespace TauCeti

open Subgroup Submodule

namespace freeProP

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-- The normal-form word `x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)` lies in the kernel `X` of the exponent
sum at `x₂`: its exponent vector is `q` at `x₁` and `0` elsewhere. -/
theorem demushkinWordNeTwo_freeProPGen_mem_exponentSumKer (hn1 : 1 < n) (q : ℕ) :
    demushkinWordNeTwo q n (freeProPGen p n) ∈ exponentSumKer p (Fin n) ⟨1, hn1⟩ := by
  rw [mem_exponentSumKer_iff, toAdd_exponentSum_demushkinWordNeTwo, Pi.smul_apply,
    toAdd_exponentSum_freeProPGen_apply, ite_eq_right (by simp), smul_zero]

/-- The derivative `∂_k` of a bracket `[ξ_{2b}, ξ_{2b+1}]` of the commutator part of the word, when
`k` differs from both `2b` and `2b + 1`. -/
private theorem degreeOneDeriv_gradedBracket_freeProPGen_of_ne (k : Fin n) {b : ℕ}
    (hb : 2 * b + 1 < n) (h₁ : (k : ℕ) ≠ 2 * b) (h₂ : (k : ℕ) ≠ 2 * b + 1) :
    degreeOneDeriv p (Fin n) k (gradedBracket p (freeProP p (Fin n)) 0 0
      (gradedMkZero p (freeProP p (Fin n)) (freeProPGen p n (2 * b)))
      (gradedMkZero p (freeProP p (Fin n)) (freeProPGen p n (2 * b + 1)))) = 0 := by
  rw [freeProPGen_of_lt p (show 2 * b < n by omega), freeProPGen_of_lt p hb]
  exact degreeOneDeriv_gradedBracket_gradedMkZero_of_of_ne (Fin.mk_lt_mk.2 (Nat.lt_succ_self _))
    (fun h ↦ h₁ (congrArg Fin.val h).symm) fun h ↦ h₂ (congrArg Fin.val h).symm

/-- The derivative `∂_k` of the class of the word at a generator `x_k` with `k ≠ 0` and
`k ∈ {2a, 2a + 1}`: the `p`-power term and the brackets not containing `k` drop out, leaving the
derivative of the single bracket `[ξ_{2a}, ξ_{2a+1}]`. -/
private theorem degreeOneDeriv_gradedMk_demushkinWordNeTwo_eq {q : ℕ} (hq : p ∣ q) {a : ℕ}
    (ha : 2 * a + 1 < n) (k : Fin n) (hk₀ : (k : ℕ) ≠ 0)
    (hk : (k : ℕ) = 2 * a ∨ (k : ℕ) = 2 * a + 1) :
    degreeOneDeriv p (Fin n) k (gradedMk p (freeProP p (Fin n)) 1
        ⟨demushkinWordNeTwo q n (freeProPGen p n),
          demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩) =
      degreeOneDeriv p (Fin n) k (gradedBracket p (freeProP p (Fin n)) 0 0
        (gradedMkZero p (freeProP p (Fin n)) (of ⟨2 * a, by omega⟩))
        (gradedMkZero p (freeProP p (Fin n)) (of ⟨2 * a + 1, ha⟩))) := by
  rw [gradedMk_demushkinWordNeTwo hq, map_add, map_nsmul, map_sum,
    freeProPGen_of_lt p (show 0 < n by omega),
    degreeOneDeriv_gradedPow_gradedMkZero_of_of_ne (fun h ↦ hk₀ (congrArg Fin.val h).symm),
    nsmul_zero, zero_add,
    Finset.sum_eq_single a (fun b hb hba ↦ degreeOneDeriv_gradedBracket_freeProPGen_of_ne _
      (by rw [Finset.mem_range] at hb; omega) (by omega) (by omega))
      (fun h ↦ (h (Finset.mem_range.2 (by omega))).elim),
    freeProPGen_of_lt p (show 2 * a < n by omega), freeProPGen_of_lt p ha]

/-- **The derivative of the class of `x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)` at the generator `x_{2a}`**
(in the `0`-based indexing of `Fin n`), for `a ≥ 1`: `∂_{2a} ρ = ξ_{2a+1}`. -/
theorem degreeOneDeriv_gradedMk_demushkinWordNeTwo_even {q : ℕ} (hq : p ∣ q) {a : ℕ} (ha₀ : 0 < a)
    (ha : 2 * a + 1 < n) :
    degreeOneDeriv p (Fin n) ⟨2 * a, by omega⟩ (gradedMk p (freeProP p (Fin n)) 1
        ⟨demushkinWordNeTwo q n (freeProPGen p n),
          demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩) =
      gradedMkZero p (freeProP p (Fin n)) (freeProPGen p n (2 * a + 1)) := by
  rw [degreeOneDeriv_gradedMk_demushkinWordNeTwo_eq hq ha ⟨2 * a, by omega⟩
      (by simp only; omega) (Or.inl rfl),
    degreeOneDeriv_gradedBracket_gradedMkZero_of_left (Fin.mk_lt_mk.2 (Nat.lt_succ_self _)),
    freeProPGen_of_lt p ha]

/-- **The derivative of the class of `x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)` at the generator `x_{2a+1}`**
(in the `0`-based indexing of `Fin n`): `∂_{2a+1} ρ = -ξ_{2a}`. -/
theorem degreeOneDeriv_gradedMk_demushkinWordNeTwo_odd {q : ℕ} (hq : p ∣ q) {a : ℕ}
    (ha : 2 * a + 1 < n) :
    degreeOneDeriv p (Fin n) ⟨2 * a + 1, ha⟩ (gradedMk p (freeProP p (Fin n)) 1
        ⟨demushkinWordNeTwo q n (freeProPGen p n),
          demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩) =
      -gradedMkZero p (freeProP p (Fin n)) (freeProPGen p n (2 * a)) := by
  rw [degreeOneDeriv_gradedMk_demushkinWordNeTwo_eq hq ha ⟨2 * a + 1, ha⟩ (Nat.succ_ne_zero _)
      (Or.inr rfl),
    degreeOneDeriv_gradedBracket_gradedMkZero_of_right (Fin.mk_lt_mk.2 (Nat.lt_succ_self _)),
    freeProPGen_of_lt p (show 2 * a < n by omega)]

/-- **The derivative of the class of `x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)` at the generator `x_0`** (in
the `0`-based indexing of `Fin n`), for `n ≥ 2`: `∂_0 ρ = (q / p) • (p choose 2) • ξ_0 + ξ_1`, the
first term from the `p`-power factor `x_0^q` and the second from the bracket `[ξ_0, ξ_1]`. -/
theorem degreeOneDeriv_gradedMk_demushkinWordNeTwo_zero {q : ℕ} (hq : p ∣ q) (hn1 : 1 < n) :
    degreeOneDeriv p (Fin n) ⟨0, by omega⟩ (gradedMk p (freeProP p (Fin n)) 1
        ⟨demushkinWordNeTwo q n (freeProPGen p n),
          demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩) =
      (q / p) • p.choose 2 • gradedMkZero p (freeProP p (Fin n)) (of ⟨0, by omega⟩) +
        gradedMkZero p (freeProP p (Fin n)) (of ⟨1, hn1⟩) := by
  have hn0 : 0 < n := by omega
  -- The derivative at `x_0` of the first bracket `[ξ_0, ξ_1]` is `ξ_1`.
  have key : degreeOneDeriv p (Fin n) ⟨0, hn0⟩ (gradedBracket p (freeProP p (Fin n)) 0 0
      (gradedMkZero p (freeProP p (Fin n)) (freeProPGen p n (2 * 0)))
      (gradedMkZero p (freeProP p (Fin n)) (freeProPGen p n (2 * 0 + 1)))) =
      gradedMkZero p (freeProP p (Fin n)) (of ⟨1, hn1⟩) := by
    rw [freeProPGen_of_lt p (i := 2 * 0) hn0, freeProPGen_of_lt p (i := 2 * 0 + 1) hn1]
    exact degreeOneDeriv_gradedBracket_gradedMkZero_of_left (Fin.mk_lt_mk.2 (by omega))
  rw [gradedMk_demushkinWordNeTwo hq, map_add, map_nsmul, map_sum,
    freeProPGen_of_lt p hn0, degreeOneDeriv_gradedPow_gradedMkZero_of_self,
    Finset.sum_eq_single 0 (fun b hb hb0 ↦ degreeOneDeriv_gradedBracket_freeProPGen_of_ne _
      (by rw [Finset.mem_range] at hb; omega) (by rw [Fin.val_mk]; omega)
      (by rw [Fin.val_mk]; omega))
      fun h ↦ (h (Finset.mem_range.2 (by omega))).elim, key]

/-- **Every generator class other than `ξ_1` is a combination of the derivatives at the generators
other than `x_0`** (in the `0`-based indexing of `Fin n`), for the class of
`x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)` with `n` even. -/
theorem exists_sum_smul_degreeOneDeriv_gradedMk_demushkinWordNeTwo_eq (hn : Even n) {q : ℕ}
    (hq : p ∣ q) (hn1 : 1 < n) (j : Fin n) (hj : j ≠ ⟨1, hn1⟩) :
    ∃ b : Fin n → ZMod p, b ⟨0, by omega⟩ = 0 ∧
      ∑ k, b k • degreeOneDeriv p (Fin n) k (gradedMk p (freeProP p (Fin n)) 1
        ⟨demushkinWordNeTwo q n (freeProPGen p n),
          demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩) =
        gradedMkZero p (freeProP p (Fin n)) (of j) := by
  classical
  obtain ⟨N, hN⟩ := hn
  have hj' : (j : ℕ) ≠ 1 := fun h ↦ hj (Fin.ext h)
  -- A single derivative, up to sign, gives `ξ_j`.
  have key (k : Fin n) (c : ZMod p) (hk : k ≠ ⟨0, by omega⟩)
      (h : c • degreeOneDeriv p (Fin n) k (gradedMk p (freeProP p (Fin n)) 1
        ⟨demushkinWordNeTwo q n (freeProPGen p n),
          demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩) =
        gradedMkZero p (freeProP p (Fin n)) (of j)) :
      ∃ b : Fin n → ZMod p, b ⟨0, by omega⟩ = 0 ∧
        ∑ k, b k • degreeOneDeriv p (Fin n) k (gradedMk p (freeProP p (Fin n)) 1
          ⟨demushkinWordNeTwo q n (freeProPGen p n),
            demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩) =
          gradedMkZero p (freeProP p (Fin n)) (of j) :=
    ⟨Pi.single k c, Pi.single_eq_of_ne (Ne.symm hk) _, by
      simp only [Pi.single_apply, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true, h]⟩
  rcases Nat.even_or_odd (j : ℕ) with ⟨a, ha⟩ | ⟨a, ha⟩
  · -- `ξ_{2a} = -∂_{2a+1} ρ`.
    have ha' : 2 * a + 1 < n := by omega
    refine key ⟨2 * a + 1, ha'⟩ ((-1 : ℤ) : ZMod p) (fun h ↦ by simp [Fin.ext_iff] at h) ?_
    rw [degreeOneDeriv_gradedMk_demushkinWordNeTwo_odd hq ha', Int.cast_smul_eq_zsmul,
      neg_one_zsmul, neg_neg, freeProPGen_of_lt p (by omega)]
    congr 2
    exact Fin.ext (by simp only; omega)
  · -- `ξ_{2a+1} = ∂_{2a} ρ`, where `a ≥ 1` since `j ≠ 1`.
    have ha₀ : 0 < a := by omega
    have ha' : 2 * a + 1 < n := by omega
    refine key ⟨2 * a, by omega⟩ 1 (fun h ↦ by simp [Fin.ext_iff] at h; omega) ?_
    rw [degreeOneDeriv_gradedMk_demushkinWordNeTwo_even hq ha₀ ha', one_smul,
      freeProPGen_of_lt p ha']
    congr 2
    exact Fin.ext (by simp only; omega)

/-- **The constrained span statement at the normal form `x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)`**
(Labute, §4, Lemma 3). For `n` even, `p ∣ q`, the class `ρ` of the word, `X` the kernel of the
exponent sum at the generator `x_1` (in the `0`-based indexing of `Fin n`) and every `m ≥ 1`,

  `gr_{m+1}(X) = δ_ρ(gr_m(X)^n) + T_{m+1}`,

where the tail `T_{m+1}` is spanned by the `p`-powers `π^{m+1} ξ_j` with `j ≠ 1`. At `p = 2` and
`q = 2 + 2^f` this is the span statement for the relators `x₁^{2+2^f} (x₁, x₂)(x₃, x₄) ⋯` whose
basis corrections must respect the orientation. -/
theorem gradedPieceOf_exponentSumKer_demushkinWordNeTwo_eq_map_basisModificationDelta_sup
    (hn : Even n) (hn1 : 1 < n) {q : ℕ} (hq : p ∣ q) {m : ℕ} (hm : 1 ≤ m) :
    gradedPieceOf p (exponentSumKer p (Fin n) ⟨1, hn1⟩) (m + 1) =
      (Submodule.pi Set.univ
          fun _ : Fin n ↦ gradedPieceOf p (exponentSumKer p (Fin n) ⟨1, hn1⟩) m).map
        (basisModificationDelta p (Fin n) hm (gradedMk p (freeProP p (Fin n)) 1
          ⟨demushkinWordNeTwo q n (freeProPGen p n),
            demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩)) ⊔
      span (ZMod p) (Set.range fun a : {a : Fin n // a ≠ ⟨1, hn1⟩} ↦
        gradedPowIter p (freeProP p (Fin n)) (m + 1)
          (gradedMkZero p (freeProP p (Fin n)) (of a))) :=
  gradedPieceOf_exponentSumKer_eq_map_basisModificationDelta_sup_span_gradedPowIter hm
    ((span_range_degreeOneDeriv_eq_top_iff_nondegenerate_degreeOneForm _).2
      (nondegenerate_degreeOneForm_demushkinWordNeTwo hn hq))
    (i₀ := ⟨0, by omega⟩) (fun k hk ↦ by
      rw [degreeOneBasis_repr_gradedMk_demushkinWordNeTwo_inl hq k,
        ite_eq_right fun h ↦ hk (Fin.ext h)])
    fun j hj ↦ exists_sum_smul_degreeOneDeriv_gradedMk_demushkinWordNeTwo_eq hn hq hn1 j hj

end freeProP

end TauCeti

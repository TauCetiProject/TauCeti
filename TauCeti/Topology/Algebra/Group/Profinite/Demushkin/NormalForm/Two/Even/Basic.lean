/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.DegreeOneForm
public import TauCeti.Topology.Algebra.Group.Profinite.Free.BasisModification

/-!
# The span statement at the dyadic normal form of even rank

Let `F = freeProP 2 (Fin n)` be the free pro-`2` group on an even number `n ≥ 2` of generators,
and let `ρ ∈ gr_1(F)` be the class of Labute's normal-form word
`x₁^{2+α} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)` with `4 ∣ α` and `f ≥ 2`, which is
`π ξ₁ + [ξ₁, ξ₂] + [ξ₃, ξ₄] + ⋯ + [ξ_{n-1}, ξ_n]`. For every `m ≥ 1` the image of the
basis-modification map `δ_ρ : gr_m(F)^n → gr_{m+1}(F)` together with the span of the `2`-powers
`π^{m+1} ξ_i` for `i ≠ 2` is all of `gr_{m+1}(F)`:

  `gr_{m+1}(F) = Im δ_ρ + ⟨π^{m+1} ξ_i : i ≠ 2⟩`.

This is the dyadic span statement of Labute's successive-approximation argument for the relators
with `q = 2` of even rank: the class in `gr_{m+1}(F)` of a discrepancy between two relators with
class `ρ` is the class of a basis modification up to the classes of the powers `x_i^{2^{m+1}}`,
`i ≠ 2`, which the argument carries along rather than absorbs; in Labute's proof they give rise to
the exponents `2 + α` of `x₁` and `2^f` of `x₃` in the normal form. Unlike the odd-rank case, the
squared generator `x₁` occurs in a bracket, and the spanning set is not indexed by the generators
with vanishing `2`-power coefficient: it includes `π^{m+1} ξ₁` although `x₁` carries the `2`-power
part of `ρ`, and excludes `π^{m+1} ξ₂`, the power of its bracket partner. The statement is the
instance of
`TauCeti.freeProP.range_basisModificationDelta_sup_gradedPowIterSpan_compl_eq_top_two` at `x₂`:
the degree-one form of `ρ` is nondegenerate, and its column at the second coordinate character is
the vector of `2`-power coefficients of `ρ`, since `x₁` is the only generator with a `2`-power
coefficient and the second coordinate character pairs only with the first.

## Main results

* `freeProP.range_basisModificationDelta_sup_gradedPowIterSpan_eq_top_demushkinWordTwoEven`:
  `gr_{m+1}(F) = Im δ_ρ + ⟨π^{m+1} ξ_i : i ≠ 2⟩` for the class `ρ` of
  `x₁^{2+α} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)`.

## References

* J. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §3,
  Proposition 5 and the proof of Theorem 3.
-/

public section

namespace TauCeti

-- Preferring the ring path keeps a single additive structure on `ZMod 2`, so that the degree-one
-- form below is stated over the module structure of `ZMod 2` on itself.
attribute [local instance 2000] Ring.toAddCommGroup

namespace freeProP

variable {n : ℕ}

/-- **The dyadic span statement at the normal form of even rank** (Labute, Proposition 5, the case
`q = 2` with `n` even). Let `n ≥ 2` be even, `4 ∣ a`, `f ≥ 2`, and let `ρ ∈ gr_1(F)` be the class
of `x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)` in the free pro-`2` group `F` on `n`
generators. Then for every `m ≥ 1`
  `gr_{m+1}(F) = Im δ_ρ + ⟨π^{m+1} ξ_i : i ≠ 2⟩`,
the span being that of the `2`-powers `π^{m+1} ξ_i` of the generator classes other than `ξ₂`. -/
theorem range_basisModificationDelta_sup_gradedPowIterSpan_eq_top_demushkinWordTwoEven
    (hn : Even n) (hn0 : 0 < n) {a f : ℕ} (ha : 4 ∣ a) (hf : 2 ≤ f) {m : ℕ} (hm : 1 ≤ m) :
    LinearMap.range (basisModificationDelta 2 (Fin n) hm
        (gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨demushkinWordTwoEven a f n (freeProPGen 2 n),
          demushkinWordTwoEven_mem_pLowerCentralSeries_one (dvd_trans (Dvd.intro 2 rfl) ha)
            (zero_lt_two.trans_le hf) n _⟩)) ⊔
      gradedPowIterSpan 2 (Fin n) {i | (i : ℕ) ≠ 1} (m + 1) = ⊤ := by
  have hn1 : 1 < n := by
    obtain ⟨N, hN⟩ := hn
    omega
  have ha2 : 2 ∣ a := dvd_trans (Dvd.intro 2 rfl) ha
  have hf0 : 0 < f := zero_lt_two.trans_le hf
  have hset : ({i | (i : ℕ) ≠ 1} : Set (Fin n)) = {⟨1, hn1⟩}ᶜ := by
    ext i
    simp [Fin.ext_iff]
  rw [hset]
  refine range_basisModificationDelta_sup_gradedPowIterSpan_compl_eq_top_two hm
    (ρ := gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨demushkinWordTwoEven a f n (freeProPGen 2 n),
      demushkinWordTwoEven_mem_pLowerCentralSeries_one ha2 hf0 n _⟩)
    (i₁ := ⟨1, hn1⟩) ?_ fun i ↦ ?_
  · rw [span_range_degreeOneDeriv_eq_top_iff_nondegenerate_degreeOneForm]
    exact nondegenerate_degreeOneForm_demushkinWordTwoEven hn ha2 hf0
  · -- The column of the form at `χ₂` is `χ_i(x₁)`, and the coefficients of the `π ξ_i` are
    -- `1 + a/2 ≡ 1` at `i = 1`, since `4 ∣ a`, and `2^{f-1} ≡ 0` at `i = 3`, since `f ≥ 2`.
    rw [degreeOneForm_gradedMk_demushkinWordTwoEven_dualBasis_one hn1 ha2 hf0,
      toMul_dualBasis_freeProPGen, degreeOneBasis_repr_gradedMk_demushkinWordTwoEven_inl ha2 hf0]
    obtain ⟨g, hg⟩ : ∃ g, f - 1 = g + 1 := ⟨f - 2, by omega⟩
    obtain ⟨b, rfl⟩ := ha
    have hb : 4 * b / 2 = 2 * b := by omega
    rw [hg, hb]
    simp [nsmul_eq_mul, CharTwo.two_eq_zero]

end freeProP

end TauCeti

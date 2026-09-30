/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.DegreeOneForm
public import TauCeti.Topology.Algebra.Group.Profinite.Free.BasisModification

/-!
# The span statement at the dyadic normal form of odd rank

Let `F = freeProP 2 (Fin n)` be the free pro-`2` group on an odd number `n` of generators, and let
`ρ ∈ gr_1(F)` be the class of Labute's normal-form word `x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)`
with `f ≥ 2`, which is `π ξ₁ + [ξ₂, ξ₃] + ⋯ + [ξ_{n-1}, ξ_n]`. For every `m ≥ 1` the image of the
basis-modification map `δ_ρ : gr_m(F)^n → gr_{m+1}(F)` together with the tail `T_{m+1}(ρ)`,
spanned by the `2`-powers `π^{m+1} ξ_i` for `i ≥ 2`, is all of `gr_{m+1}(F)`:

  `gr_{m+1}(F) = Im δ_ρ + T_{m+1}(ρ)`.

This is the dyadic span statement of Labute's successive-approximation argument for the relators
with `q = 2` of odd rank: the class in `gr_{m+1}(F)` of a discrepancy between two relators with
class `ρ` is the class of a basis modification up to the classes of the powers `x_i^{2^{m+1}}`,
`i ≥ 2`, which the argument carries along rather than absorbs; in Labute's proof they give rise to
the factor `x₂^{2^f}` of the normal form. It is the instance of
`TauCeti.freeProP.range_basisModificationDelta_sup_basisModificationTail_eq_top_two` at the
generator `x₁`: the degree-one form of `ρ` is nondegenerate, `x₁` is the only generator with a
`2`-power coefficient, and the first coordinate character is orthogonal to the others.

## Main results

* `freeProP.range_basisModificationDelta_sup_basisModificationTail_eq_top_demushkinWordTwoOdd`:
  `gr_{m+1}(F) = Im δ_ρ + T_{m+1}(ρ)` for the class `ρ` of `x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)`.

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

/-- **The dyadic span statement at the normal form of odd rank** (Labute, Proposition 5, the case
`q = 2`). Let `n` be odd, `f ≥ 2`, and let `ρ ∈ gr_1(F)` be the class of
`x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)` in the free pro-`2` group `F` on `n` generators. Then for
every `m ≥ 1`
  `gr_{m+1}(F) = Im δ_ρ + T_{m+1}(ρ)`,
the tail `T_{m+1}(ρ)` being spanned by the `2`-powers `π^{m+1} ξ_i` of the generator classes other
than `ξ₁`. -/
theorem range_basisModificationDelta_sup_basisModificationTail_eq_top_demushkinWordTwoOdd
    (hn : Odd n) {f : ℕ} (hf : 2 ≤ f) {m : ℕ} (hm : 1 ≤ m) :
    LinearMap.range (basisModificationDelta 2 (Fin n) hm
        (gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨demushkinWordTwoOdd f n (freeProPGen 2 n),
          demushkinWordTwoOdd_mem_pLowerCentralSeries_one (zero_lt_two.trans_le hf) n _⟩)) ⊔
      basisModificationTail 2 (Fin n)
        (gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨demushkinWordTwoOdd f n (freeProPGen 2 n),
          demushkinWordTwoOdd_mem_pLowerCentralSeries_one (zero_lt_two.trans_le hf) n _⟩)
        (m + 1) = ⊤ := by
  have hn0 : 0 < n := hn.pos
  refine range_basisModificationDelta_sup_basisModificationTail_eq_top_two hm
    (i₀ := ⟨0, hn0⟩) ?_ (fun k hk ↦ ?_) fun i hi ↦ ?_
  · rw [span_range_degreeOneDeriv_eq_top_iff_nondegenerate_degreeOneForm]
    exact nondegenerate_degreeOneForm_demushkinWordTwoOdd hn (zero_lt_two.trans_le hf)
  · exact (degreeOneBasis_repr_gradedMk_demushkinWordTwoOdd_inl_eq_zero_iff hf k).2
      fun h ↦ hk (Fin.ext h)
  · rw [degreeOneForm_gradedMk_demushkinWordTwoOdd_dualBasis_zero hn0 (zero_lt_two.trans_le hf),
      toMul_dualBasis_freeProPGen, ite_eq_right fun h ↦ hi (Fin.ext h)]

end freeProP

end TauCeti

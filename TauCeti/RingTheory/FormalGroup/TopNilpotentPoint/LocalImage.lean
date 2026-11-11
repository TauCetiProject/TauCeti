/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.TopNilpotentPoint.Hom
public import TauCeti.RingTheory.PowerSeries.InverseFunction

/-!
# Exact images of small formal neighbourhoods

For a homomorphism `f : F → G` of integral formal groups over a complete discrete valuation
ring, write `(f'(0)) = 𝔪 ^ e`. Evaluation of `f` maps the points with coordinate in `𝔪 ^ k`
bijectively onto the points with coordinate in `𝔪 ^ (k + e)`, for `k > e`.

This supplies both the absence of a kernel on a sufficiently small neighbourhood and its
exact image. These are the analytic inputs for computing local isogeny indices from the
linear coefficient, rather than only bounding those indices by the degree.

## References

* J. Silverman, *The Arithmetic of Elliptic Curves*, IV.4 and IV.6.
* E. F. Schaefer, *Class groups and Selmer groups*, J. Number Theory 56 (1996), Lemma 3.8.
-/

public section

namespace TauCeti.FormalGroupHom

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R] [T2Space R]
  [IsTopologicalRing R] [IsLinearTopology R R]
  [Fact (IsAdic (IsLocalRing.maximalIdeal R))] {F G : FormalGroup R}

/-- An integral formal-group homomorphism whose linear coefficient has valuation `e` maps
the depth-`k` points bijectively onto the depth-`k + e` points whenever `e < k`. -/
theorem bijOn_toTopNilpotentPointHom_maximalIdeal_pow (f : FormalGroupHom F G) {e k : ℕ}
    (ha : Ideal.span {PowerSeries.coeff 1 f.toPowerSeries} = IsLocalRing.maximalIdeal R ^ e)
    (hek : e < k) :
    Set.BijOn (f.toTopNilpotentPointHom R)
      {x | x.val ∈ IsLocalRing.maximalIdeal R ^ k}
      {y | y.val ∈ IsLocalRing.maximalIdeal R ^ (k + e)} := by
  have h := PowerSeries.bijOn_eval₂_maximalIdeal_pow f.zero_constantCoeff ha hek
  have heval (x : F.TopNilpotentPoint R) :
      (f.toTopNilpotentPointHom R x).val =
        PowerSeries.eval₂ (RingHom.id R) x.val f.toPowerSeries := by
    apply HasSum.unique (f.hasSum_val_toTopNilpotentPointHom x)
    simpa only [smul_eq_mul, RingHom.id_apply] using
      PowerSeries.hasSum_eval₂ (φ := RingHom.id R) continuous_id x.hasEval f.toPowerSeries
  refine ⟨fun x hx ↦ ?_, fun x hx y hy hxy ↦ ?_, fun y hy ↦ ?_⟩
  · simpa only [Set.mem_ofPred_eq, heval, SetLike.mem_coe] using h.mapsTo hx
  · exact FormalGroup.TopNilpotentPoint.ext (h.injOn hx hy (by
      simpa only [heval] using congrArg FormalGroup.TopNilpotentPoint.val hxy))
  · obtain ⟨t, ht, hty⟩ := h.surjOn hy
    have ht' : t ∈ IsLocalRing.maximalIdeal R := Ideal.pow_le_self (by omega) ht
    let x : F.TopNilpotentPoint R :=
      ⟨t, (Fact.out : IsAdic (IsLocalRing.maximalIdeal R)).isTopologicallyNilpotent_of_mem ht'⟩
    exact ⟨x, ht, FormalGroup.TopNilpotentPoint.ext (by simpa only [heval] using hty)⟩

end TauCeti.FormalGroupHom

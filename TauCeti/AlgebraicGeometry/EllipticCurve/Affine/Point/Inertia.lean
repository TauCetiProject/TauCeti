/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Galois
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TorsionReduction
public import TauCeti.RingTheory.Valuation.RamificationGroup

/-!
# Inertia acts trivially on torsion prime to the residue characteristic at good reduction

Let `W` be a Weierstrass curve over a field `K`, let `L` be an extension of `K` with a valuation
`v`, and suppose that the equation `W`, read over `L`, has coefficients in the valuation ring of
`v`. An automorphism `σ` of `L / K` in the inertia group of `v` preserves the valuation ring of `v`
and acts trivially on its residue field, while it fixes the coefficients of `W`. It therefore does
not change the reduction of any point of `W(L)`: the reductions of `σ P` and `P` agree
(`WeierstrassCurve.Affine.Point.reduction_map_of_mem_inertiaSubgroup`). At good reduction this says
that `σ P - P` lies in the kernel of the reduction homomorphism.

Now let `L` be the fraction field of a Dedekind domain `A` and `v` the valuation at a height-one
prime `u` of `A`, and assume good reduction: the integral model of `W` over the valuation ring has
unit discriminant. For `n ∉ u` and `P ∈ W(L)[n]`, the point `σ P - P` is again killed by `n` and
reduces to the point at infinity, so it is zero, because reduction is injective on torsion of order
prime to `u` (`WeierstrassCurve.Affine.Point.injOn_reductionHom_torsionBy`). Hence the inertia
group of `u` acts trivially on `W(L)[n]`: the `n`-torsion is **unramified** at `u` (Silverman AEC
VII.4.1). This is the implication from good reduction to unramified torsion in the criterion of
Néron, Ogg and Shafarevich (AEC VII.7.1).

## Main results

* `WeierstrassCurve.Affine.Point.reduction_map_of_mem_inertiaSubgroup`: an element of the inertia
  group of `v` does not change the reduction of a point.
* `WeierstrassCurve.Affine.Point.reductionHom_map_of_mem_inertiaSubgroup`: the same statement for
  the reduction homomorphism at good reduction.
* `WeierstrassCurve.Affine.Point.map_eq_self_of_mem_inertiaSubgroup`: at good reduction, an
  element of the inertia group of `u` fixes every point of `W(L)` killed by an integer `n ∉ u`.
* `WeierstrassCurve.torsionGaloisAction_eq_one_of_mem_inertiaSubgroup`: equivalently, the inertia
  group of `u` acts trivially on `W(L)[N]` for `N ∉ u`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.4.1 and VII.7.1.
-/

public section

open IsDedekindDomain IsLocalRing

namespace WeierstrassCurve

namespace Affine.Point

section Reduction

variable {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L] [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation L Γ₀) {W : WeierstrassCurve K} [IsIntegral v.valuationSubring (W⁄L)]
  [DecidableEq L]

/-- **Inertia does not change reductions.** An automorphism of `L / K` in the inertia group of the
valuation `v` sends each point of `W(L)` to a point with the same reduction modulo `v`. -/
theorem reduction_map_of_mem_inertiaSubgroup {σ : v.valuationSubring.decompositionSubgroup K}
    (hσ : σ ∈ v.valuationSubring.inertiaSubgroup K) (P : (W⁄L).toAffine.Point) :
    reduction v (map (σ : L ≃ₐ[K] L).toAlgHom P) = reduction v P := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← zero_def, _root_.map_zero]
  rw [map_some]
  by_cases hx : v x ≤ 1
  · have hy := valuation_y_le_one_of_valuation_x_le_one v h.left hx
    -- `σ` preserves the valuation ring and fixes residues
    have hres (z : L) (hz : v z ≤ 1) :
        ∃ hσz : v ((σ : L ≃ₐ[K] L).toAlgHom z) ≤ 1,
          residue v.valuationSubring ⟨_, (v.mem_valuationSubring_iff _).mpr hσz⟩ =
            residue v.valuationSubring ⟨z, (v.mem_valuationSubring_iff z).mpr hz⟩ := by
      have hz' : z ∈ v.valuationSubring := (v.mem_valuationSubring_iff z).mpr hz
      refine ⟨(v.mem_valuationSubring_iff _).mp
        ((ValuationSubring.decompositionSubgroup_apply_mem_iff _ σ).mpr hz'), ?_⟩
      rw [← (ValuationSubring.mem_inertiaSubgroup_iff _ σ).mp hσ ⟨z, hz'⟩]
      exact congrArg _
        (Subtype.ext (ValuationSubring.coe_decompositionSubgroup_smul _ σ ⟨z, hz'⟩).symm)
    obtain ⟨hσx, hx'⟩ := hres x hx
    obtain ⟨hσy, hy'⟩ := hres y hy
    rw [reduction_some_of_valuation_le_one v h hx, reduction_some_of_valuation_le_one v _ hσx, hx',
      hy']
  · -- a coordinate with a pole keeps its pole, as `σ⁻¹` preserves the valuation ring too
    have hσx : 1 < v ((σ : L ≃ₐ[K] L).toAlgHom x) := by
      rw [← not_le, ← Valuation.mem_valuationSubring_iff]
      exact fun hσx ↦ hx ((v.mem_valuationSubring_iff x).mp
        ((ValuationSubring.decompositionSubgroup_apply_mem_iff _ σ).mp hσx))
    rw [reduction_some_of_one_lt v h (not_le.mp hx)]
    exact reduction_some_of_one_lt v _ hσx

variable [(integralModel v.valuationSubring (W⁄L)).IsElliptic]
  [DecidableEq (ResidueField v.valuationSubring)]

/-- **Inertia does not change reductions, at good reduction.** An automorphism of `L / K` in the
inertia group of `v` commutes with the reduction homomorphism `W(L) →+ W_k(k)`, in the sense that
it does not change the image of any point. -/
theorem reductionHom_map_of_mem_inertiaSubgroup {σ : v.valuationSubring.decompositionSubgroup K}
    (hσ : σ ∈ v.valuationSubring.inertiaSubgroup K) (P : (W⁄L).toAffine.Point) :
    reductionHom v (map (σ : L ≃ₐ[K] L).toAlgHom P) = reductionHom v P := by
  apply (Projective.Point.toAffineAddEquiv _).symm.injective
  rw [Projective.Point.toAffineAddEquiv_symm_apply, Projective.Point.toAffineAddEquiv_symm_apply]
  exact Projective.Point.ext ((reductionHom_toProjective_point v _).trans
    ((reduction_map_of_mem_inertiaSubgroup v hσ P).trans
      (reductionHom_toProjective_point v P).symm))

end Reduction

section Dedekind

variable {A : Type*} [CommRing A] [IsDedekindDomain A] {K L : Type*} [Field K] [Field L]
  [Algebra K L] [Algebra A L] [IsFractionRing A L] (u : HeightOneSpectrum A)
  {W : WeierstrassCurve K} [IsIntegral (u.valuation L).valuationSubring (W⁄L)]
  [(integralModel (u.valuation L).valuationSubring (W⁄L)).IsElliptic] [DecidableEq L]

/-- **Torsion prime to `u` is unramified at good reduction** (Silverman AEC VII.4.1): if `W` has
good reduction at `u`, an automorphism of `L / K` in the inertia group of `u` fixes every point of
`W(L)` killed by an integer `n ∉ u`. -/
theorem map_eq_self_of_mem_inertiaSubgroup {n : ℕ} (hn : (n : A) ∉ u.asIdeal)
    {σ : (u.valuation L).valuationSubring.decompositionSubgroup K}
    (hσ : σ ∈ (u.valuation L).valuationSubring.inertiaSubgroup K) {P : (W⁄L).toAffine.Point}
    (hP : n • P = 0) : map (σ : L ≃ₐ[K] L).toAlgHom P = P := by
  classical
  rw [← sub_eq_zero]
  -- `σ P - P` is killed by `n` and reduces to the point at infinity
  refine eq_zero_of_reductionHom_eq_zero_of_nsmul_eq_zero u hn ?_ ?_
  · rw [_root_.map_sub, reductionHom_map_of_mem_inertiaSubgroup _ hσ, sub_self]
  · rw [nsmul_sub, ← _root_.map_nsmul, hP, _root_.map_zero, sub_self]

end Dedekind

end Affine.Point

variable {A : Type*} [CommRing A] [IsDedekindDomain A] {K L : Type*} [Field K] [Field L]
  [Algebra K L] [Algebra A L] [IsFractionRing A L] (u : HeightOneSpectrum A)
  (W : WeierstrassCurve K) [IsIntegral (u.valuation L).valuationSubring (W⁄L)]
  [(integralModel (u.valuation L).valuationSubring (W⁄L)).IsElliptic] [DecidableEq L]

/-- **The `N`-torsion is unramified at good reduction** (Silverman AEC VII.4.1): if `W` has good
reduction at `u` and `N ∉ u`, every element of the inertia group of `u` acts trivially on
`W(L)[N]`. -/
theorem torsionGaloisAction_eq_one_of_mem_inertiaSubgroup {N : ℤ} (hN : (N : A) ∉ u.asIdeal)
    {σ : (u.valuation L).valuationSubring.decompositionSubgroup K}
    (hσ : σ ∈ (u.valuation L).valuationSubring.inertiaSubgroup K) :
    W.torsionGaloisAction N (σ : L ≃ₐ[K] L) = 1 := by
  apply Multiplicative.toAdd.injective
  ext P
  rw [torsionGaloisAction_apply_coe, pointGaloisAction_apply, toAdd_one, AddAut.zero_apply]
  -- `N` and `|N|` generate the same ideal, and kill the same points
  have hn : (N.natAbs : A) ∉ u.asIdeal := by
    rw [← Int.cast_natCast, Int.natCast_natAbs]
    rcases abs_choice N with h | h <;> rw [h]
    · exact hN
    · rwa [Int.cast_neg, neg_mem_iff]
  refine Affine.Point.map_eq_self_of_mem_inertiaSubgroup u hn hσ ?_
  rw [natAbs_nsmul_eq_zero]
  exact (Submodule.mem_torsionBy_iff (R := ℤ) _ _).mp P.2

end WeierstrassCurve

end

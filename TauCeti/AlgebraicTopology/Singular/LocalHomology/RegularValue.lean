/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Derivative
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LocalIndex
import TauCeti.Analysis.Calculus.FDeriv.Equiv

/-!
# Local indices at regular points and degrees at regular values

Let `E` be a finite-dimensional real normed space, regarded as a manifold modelled on itself and
oriented by a homological orientation `o` (`TauCeti.HomologicalOrientation`). A continuous map
`f : E → E` which is differentiable at `x` with derivative `f'` of nonzero determinant has local
index `sign (det f')` at `x` (`TauCeti.HomologicalOrientation.localIndex_eq_sign_det`), for the
orientation `o` on both source and target. Consequently the degree of a proper map is the signed
count of the preimages of a regular value: if every point of the fibre over `y` has an invertible
derivative, then

`deg f = ∑_{f x = y} sign (det Df(x))`

(`TauCeti.HomologicalOrientation.degree_eq_sum_sign_det`). The fibre is finite as soon as it is
compact (`IsCompact.finite_of_hasFDerivAt`), which is automatic for a proper map.

The local index at a regular point compares `f` with its affine linearization, which acts on
local homology by the sign of its determinant relative to a translation
(`TauCeti.localHomologyMap_domRestrict_eq_sign_det_smul_of_hasFDerivAt`), and translations have
local index one for every orientation (`TauCeti.HomologicalOrientation.localIndex_addRight`).

This identifies the homological degree of a smooth proper map with the classical differential
topological degree.

## Main results

* `TauCeti.HomologicalOrientation.localIndex_eq_sign_det`: the local index at a regular point is
  the sign of the Jacobian determinant.
* `TauCeti.HomologicalOrientation.degree_eq_sum_sign_det`: the degree of a proper map is the signed
  count of the preimages of a regular value.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5.
* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VIII, §4.
-/

public section

noncomputable section

open CategoryTheory Module Set Topology

namespace TauCeti

namespace HomologicalOrientation

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
  (o : HomologicalOrientation E E n) (hE : finrank ℝ E = n)

include hE in
/-- **The local index at a regular point is the sign of the Jacobian.** If `f : E → E` is
differentiable at `x` with derivative `f'` of nonzero determinant, then its local index at `x`, for
the same orientation of `E` on source and target, is `sign (det f')`. -/
theorem localIndex_eq_sign_det {f : C(E, E)} {f' : E →L[ℝ] E} {x : E} (hf : HasFDerivAt f f' x)
    (hdet : f'.det ≠ 0) : o.localIndex o f x = SignType.sign f'.det := by
  obtain ⟨U, hU, hUo, hxU⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1
    (hf.eventually_ne (c := f x)
      ⟨_, (f'.toContinuousLinearEquivOfDetNeZero hdet).antilipschitzWith⟩))
  have hUx : ∀ z ∈ U, f z = f x → z = x := fun z hz hfz ↦ by_contra fun h ↦ hU z hz h hfz
  -- The translation by `f x - x` carries `x` to `f x` and has local index one, computed in `U`.
  have hτ := o.localIndex_addRight hE (f x - x) x
  rw [o.localIndex_eq_iff o hE _ (y := f x) (add_sub_cancel x (f x)) hUo hxU
    (fun z _ hfz ↦ by simpa using congrArg (· - (f x - x)) hfz)] at hτ
  rw [o.localIndex_eq_iff o hE f rfl hUo hxU hUx]
  -- On local homology at `x`, the restriction of `f` to `U` is `sign (det f')` times that of the
  -- translation.
  have h := localHomologyMap_domRestrict_eq_sign_det_smul_of_hasFDerivAt
    (ModuleCat.of ℤ (ULift.{0} ℤ)) (hUo.mem_nhds hxU) f.continuous.continuousOn hf hdet hUx n
  -- Both sides are `f` evaluated at the underlying point of `U`.
  have e1 : ContinuousMap.restrict U f =
      ⟨U.domRestrict f, f.continuous.continuousOn.domRestrict⟩ :=
    ContinuousMap.ext fun _ ↦ rfl
  have e2 : ContinuousMap.restrict U (ContinuousMap.addRight (f x - x)) =
      ⟨fun y : U ↦ f x + (y - x), by fun_prop⟩ :=
    ContinuousMap.ext fun y ↦ by
      simp only [ContinuousMap.restrict_apply, ContinuousMap.coe_addRight, ContinuousMap.coe_mk]
      abel
  simp only [e2] at hτ
  simp only [e1, h, ModuleCat.hom_zsmul]
  -- The integer multiple of a linear map is evaluated pointwise.
  exact congrArg ((SignType.sign f'.det : ℤ) • ·) (hτ.trans (one_smul _ _))

include hE in
/-- **The degree is the sum of the Jacobian signs over a regular fibre.** Let `f : E → E` be a
proper map and `y` a point whose fibre is finite and consists of points where `f` has a derivative
`f' x` of nonzero determinant. Then the degree of `f` is the sum of `sign (det f' x)` over the
fibre. The finiteness of the fibre follows from the other hypotheses by
`IsCompact.finite_of_hasFDerivAt`. -/
theorem degree_eq_sum_sign_det {f : C(E, E)} (hf : IsProperMap f) {f' : E → E →L[ℝ] E} {y : E}
    (hfin : (f ⁻¹' {y}).Finite) (hderiv : ∀ x ∈ f ⁻¹' {y}, HasFDerivAt f (f' x) x)
    (hdet : ∀ x ∈ f ⁻¹' {y}, (f' x).det ≠ 0) :
    o.degree o hE f = ∑ x ∈ hfin.toFinset, (SignType.sign (f' x).det : ℤ) := by
  rw [o.degree_eq_sum_localIndex o hE hE hf hfin]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [Finite.mem_toFinset] at hx
  exact o.localIndex_eq_sign_det hE (hderiv x hx) (hdet x hx)

include hE in
/-- **The degree counts the preimages of a regular value with orientation signs.** If every point
of the fibre of the proper map `f : E → E` over `y` has a derivative `f' x` of nonzero
determinant, then the degree of `f` is the number of these points where `det f' x` is positive
minus the number where it is negative. -/
theorem degree_eq_ncard_sub_ncard {f : C(E, E)} (hf : IsProperMap f) {f' : E → E →L[ℝ] E}
    {y : E} (hderiv : ∀ x ∈ f ⁻¹' {y}, HasFDerivAt f (f' x) x)
    (hdet : ∀ x ∈ f ⁻¹' {y}, (f' x).det ≠ 0) :
    o.degree o hE f = ({x | 0 < (f' x).det} ∩ f ⁻¹' {y}).ncard -
      ({x | (f' x).det < 0} ∩ f ⁻¹' {y}).ncard := by
  have hfin := (hf.isCompact_preimage isCompact_singleton).finite_of_hasFDerivAt hderiv
    fun x hx ↦ ⟨_, ((f' x).toContinuousLinearEquivOfDetNeZero (hdet x hx)).antilipschitzWith⟩
  rw [o.degree_eq_sum_sign_det hE hf hfin hderiv hdet]
  have e (t : ℝ) :
      (SignType.sign t : ℤ) = (if 0 < t then 1 else 0) - (if t < 0 then 1 else 0) := by
    rcases lt_trichotomy t 0 with h | h | h <;> simp [h, h.not_gt]
  have hpos : {x | 0 < (f' x).det} ∩ f ⁻¹' {y} =
      ↑(hfin.toFinset.filter fun x ↦ 0 < (f' x).det) := by
    ext x; simp [and_comm]
  have hneg : {x | (f' x).det < 0} ∩ f ⁻¹' {y} =
      ↑(hfin.toFinset.filter fun x ↦ (f' x).det < 0) := by
    ext x; simp [and_comm]
  simp_rw [e]
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, hpos, hneg, ncard_coe_finset,
    ncard_coe_finset]

end HomologicalOrientation

end TauCeti

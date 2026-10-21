/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Basic
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Kernel
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.OpenQuotient
public import TauCeti.Topology.Algebra.Nonarchimedean.Quotient
import TauCeti.RingTheory.Huber.OpenMapping
import TauCeti.Topology.Algebra.Nonarchimedean.Pi
import TauCeti.Topology.LiftTendstoCofinite
import Mathlib.Data.Finsupp.Encodable

/-!
# Restricted power series over a quotient ring

Let `A` be a complete Hausdorff Tate ring with countably generated uniformity and `J` an ideal
of `A`. Reducing coefficients modulo `J` is a continuous surjection
`A⟨X₁, …, Xₖ⟩ → (A ⧸ J)⟨X₁, …, Xₖ⟩`, whose kernel consists of the series with every coefficient
in `J` (`TauCeti.Huber.mem_ker_weightedMap_iff`). This file identifies that kernel with the
extended ideal `J · A⟨X₁, …, Xₖ⟩` when `J` is finitely generated and closed — for instance for
every ideal of a noetherian `A` — and deduces the quotient isomorphism

```text
(A ⧸ J)⟨X₁, …, Xₖ⟩ ≅ A⟨X₁, …, Xₖ⟩ ⧸ J · A⟨X₁, …, Xₖ⟩,
```

of topological rings, the restricted-series analogue of Mathlib's
`Ideal.polynomialQuotientEquivQuotientPolynomial`.

The inclusion of `J · A⟨X⟩` in the series with coefficients in `J` is formal
(`Ideal.coeff_mem_of_mem_map_weightedC`). The converse is not: writing a series with coefficients
`cᵥ ∈ J` as `∑ᵢ gᵢ fᵢ` for generators `gᵢ` of `J` asks for coefficients `cᵥ = ∑ᵢ gᵢ aᵢᵥ` with
`aᵢᵥ → 0`, and lifting each coefficient separately need not give that. The open mapping theorem
over a Tate ring makes the presentation `Aⁿ → J` open, because `J` is closed, and open
surjections lift null families to null families (`TauCeti.exists_lift_tendsto_cofinite_nhds`).

For a noetherian `A` the isomorphism is also the case `M = A ⧸ J` of Wedhorn's Remark 8.29
(`TauCeti.Huber.restrictedMvPowerSeriesBaseChangeEquiv`), composed with
`(A ⧸ J) ⊗[A] A⟨X⟩ ≅ A⟨X⟩ ⧸ J · A⟨X⟩`. The direct argument here needs only the generators and the
closedness of `J`, not a noetherian `A`, and it produces a ring isomorphism and a homeomorphism.

Here `A⟨X₁, …, Xₖ⟩` is `TauCeti.Huber.weightedRestrictedSubring` at the trivial weight family
`Tᵢ = {1}`, the ring underlying `TauCeti.Huber.restrictedMvPowerSeriesCompletion` and strong
noetherianness, and the reduction map is `TauCeti.Huber.weightedMap`.

## Main results

* `Ideal.mem_map_weightedC_iff`: a restricted series lies in `J · A⟨X⟩` exactly when all of its
  coefficients lie in `J`, for a closed finitely generated ideal `J` of a complete Hausdorff Tate
  ring with countably generated uniformity.
* `Ideal.ker_weightedMap_quotientMk`: so the kernel of reduction modulo `J` is `J · A⟨X⟩`.
* `Ideal.restrictedQuotientEquivQuotientRestricted`: the ring isomorphism
  `(A ⧸ J)⟨X⟩ ≃+* A⟨X⟩ ⧸ J · A⟨X⟩`, a homeomorphism for the quotient topology
  (`Ideal.continuous_restrictedQuotientEquivQuotientRestricted` and its `_symm` form).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §5.6, Proposition 6.18 and
  Remark 8.29.
-/

public section

open Filter Topology
open scoped Uniformity

namespace Ideal

open TauCeti.Huber

variable {k : ℕ} {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
  [(𝓤 A).IsCountablyGenerated] [T0Space A] [NonarchimedeanRing A] [IsTateRing A]

/-- **`J · A⟨X⟩` is the set of series with coefficients in `J`**, for a closed finitely generated
ideal `J` of a complete Hausdorff Tate ring `A` with countably generated uniformity. Over a
noetherian such `A` every ideal is finitely generated and closed
(`TauCeti.Huber.isClosed_of_isNoetherian`). -/
theorem mem_map_weightedC_iff {J : Ideal A} (hJ : J.FG) (hJc : IsClosed (J : Set A))
    {f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight} :
    f ∈ J.map (weightedC _ isWeightFamily_one_weight) ↔
      ∀ ν, MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) ∈ J := by
  refine ⟨coeff_mem_of_mem_map_weightedC, fun hf ↦ ?_⟩
  -- Write `J = (g₁, …, gₙ)` and lift the null family of coefficients of `f` along the open
  -- presentation `Aⁿ → J`, `a ↦ ∑ aᵢ gᵢ`; the components `fᵢ` of the lift give `f = ∑ gᵢ fᵢ`.
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hJ
  let u := Fintype.linearCombination A g
  have hu : LinearMap.range u = J := by
    rw [Fintype.range_linearCombination]
    exact hg
  -- The presentation `Aⁿ → J` is open, by the open mapping theorem.
  have hopen := LinearMap.isStrictMap_iff_isOpenQuotientMap_rangeRestrict.mp <|
    IsTateRing.isStrictMap_of_isClosed_range u (LinearMap.continuous_on_pi u).continuousAt
      (hu ▸ hJc)
  have hf₀ : Tendsto (fun ν ↦ MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A))
      cofinite (𝓝 0) :=
    isWeightedRestricted_one_weight_iff.mp (mem_weightedRestrictedSubring.mp f.2)
  obtain ⟨a, ha, hlim⟩ := TauCeti.exists_lift_tendsto_cofinite_nhds u.rangeRestrict
    u.surjective_rangeRestrict (map_zero u.rangeRestrict ▸ hopen.isOpenMap.nhds_le 0)
    (fun ν ↦ (⟨_, hu ▸ hf ν⟩ : LinearMap.range u)) (tendsto_subtype_rng.mpr hf₀)
  -- The components of the lift are restricted series.
  let F (i : Fin n) : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight :=
    ⟨fun ν ↦ a ν i, mem_weightedRestrictedSubring.mpr <| isWeightedRestricted_one_weight_iff.mpr
      ((continuous_apply i).tendsto (0 : Fin n → A) |>.comp hlim)⟩
  have hfF : f = ∑ i, weightedC _ isWeightFamily_one_weight (g i) * F i := by
    refine Subtype.ext <| MvPowerSeries.ext fun ν ↦ ?_
    have hν := congrArg Subtype.val (ha ν)
    simp only [LinearMap.codRestrict_apply, Fintype.linearCombination_apply, smul_eq_mul,
      u] at hν
    rw [← hν, AddSubmonoidClass.coe_finsetSum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Subring.coe_mul, coe_weightedC, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_apply,
      mul_comm]
  rw [hfF]
  exact sum_mem _ fun i _ ↦ mul_mem_right _ _ <|
    mem_map_of_mem _ (hg ▸ Submodule.subset_span ⟨i, rfl⟩)

/-- **The kernel of reduction modulo `J` on restricted series is `J · A⟨X⟩`**, for a closed
finitely generated ideal `J` of a complete Hausdorff Tate ring `A` with countably generated
uniformity. -/
theorem ker_weightedMap_quotientMk {J : Ideal A} (hJ : J.FG) (hJc : IsClosed (J : Set A)) :
    RingHom.ker (weightedMap (k := k) (QuotientRing.isOpenQuotientMap_mk J).continuous
      isWeightFamily_one_weight isWeightFamily_one_weight (fun _ ↦ by simp)) =
      J.map (weightedC _ isWeightFamily_one_weight) := by
  ext f
  rw [mem_ker_weightedMap_iff, mem_map_weightedC_iff hJ hJc, mk_ker]

/-- **Restricted series over `A ⧸ J` are restricted series over `A` modulo `J`**:
`(A ⧸ J)⟨X₁, …, Xₖ⟩ ≃+* A⟨X₁, …, Xₖ⟩ ⧸ J · A⟨X₁, …, Xₖ⟩` for a closed finitely generated ideal `J`
of a complete Hausdorff Tate ring `A` with countably generated uniformity. Its inverse reduces
coefficients modulo `J` (`Ideal.restrictedQuotientEquivQuotientRestricted_symm_mk`); it is a
homeomorphism for the quotient topology on the right. -/
noncomputable def restrictedQuotientEquivQuotientRestricted {J : Ideal A} (hJ : J.FG)
    (hJc : IsClosed (J : Set A)) :
    weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J))) isWeightFamily_one_weight ≃+*
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight ⧸
        J.map (weightedC _ isWeightFamily_one_weight) :=
  (RingHom.quotientKerEquivOfSurjective
    ((QuotientRing.isOpenQuotientMap_mk J).weightedMap_surjective isWeightFamily_one_weight
      isWeightFamily_one_weight fun _ ↦ by simp)).symm.trans
    (quotEquivOfEq (ker_weightedMap_quotientMk hJ hJc))

/-- The inverse of `Ideal.restrictedQuotientEquivQuotientRestricted` reduces coefficients
modulo `J`. -/
@[simp]
theorem restrictedQuotientEquivQuotientRestricted_symm_mk {J : Ideal A} (hJ : J.FG)
    (hJc : IsClosed (J : Set A))
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    (restrictedQuotientEquivQuotientRestricted hJ hJc).symm (Quotient.mk _ f) =
      weightedMap (QuotientRing.isOpenQuotientMap_mk J).continuous isWeightFamily_one_weight
        isWeightFamily_one_weight (fun _ ↦ by simp) f := by
  simp [restrictedQuotientEquivQuotientRestricted]

/-- `Ideal.restrictedQuotientEquivQuotientRestricted` sends the reduction of `f` modulo `J` to the
class of `f`. -/
@[simp]
theorem restrictedQuotientEquivQuotientRestricted_weightedMap {J : Ideal A} (hJ : J.FG)
    (hJc : IsClosed (J : Set A))
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    restrictedQuotientEquivQuotientRestricted hJ hJc
        (weightedMap (QuotientRing.isOpenQuotientMap_mk J).continuous isWeightFamily_one_weight
          isWeightFamily_one_weight (fun _ ↦ by simp) f) =
      Quotient.mk _ f := by
  rw [← restrictedQuotientEquivQuotientRestricted_symm_mk hJ hJc, RingEquiv.apply_symm_apply]

/-- `Ideal.restrictedQuotientEquivQuotientRestricted` is continuous: reduction modulo `J` is a
quotient map onto `(A ⧸ J)⟨X⟩`. -/
theorem continuous_restrictedQuotientEquivQuotientRestricted {J : Ideal A} (hJ : J.FG)
    (hJc : IsClosed (J : Set A)) :
    Continuous (restrictedQuotientEquivQuotientRestricted (k := k) hJ hJc) := by
  have hq := (QuotientRing.isOpenQuotientMap_mk J).weightedMap (k := k) isWeightFamily_one_weight
    isWeightFamily_one_weight fun _ ↦ by simp
  refine hq.isQuotientMap.continuous_iff.mpr ?_
  rw [(funext (restrictedQuotientEquivQuotientRestricted_weightedMap hJ hJc) : _ ∘ _ = _)]
  exact (QuotientRing.isOpenQuotientMap_mk _).continuous

/-- The inverse of `Ideal.restrictedQuotientEquivQuotientRestricted` is continuous: reduction
modulo `J` is continuous on `A⟨X⟩`. -/
theorem continuous_restrictedQuotientEquivQuotientRestricted_symm {J : Ideal A} (hJ : J.FG)
    (hJc : IsClosed (J : Set A)) :
    Continuous (restrictedQuotientEquivQuotientRestricted (k := k) hJ hJc).symm := by
  refine (QuotientRing.isOpenQuotientMap_mk _).isQuotientMap.continuous_iff.mpr ?_
  rw [(funext (restrictedQuotientEquivQuotientRestricted_symm_mk hJ hJc) : _ ∘ _ = _)]
  exact continuous_weightedMap ..

end Ideal

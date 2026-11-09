/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.Analysis.Sobolev.Leibniz
import TauCeti.Analysis.Sobolev.WeakDeriv.Local

/-!
# Local Sobolev classes under smooth coefficients

`TauCeti.MemWkpLoc.clm_comp` composes a local Sobolev map with one fixed continuous linear map.
This file lets the coefficient vary smoothly with the point. A factor `χ : ℂ → ℝ` that is smooth
on an open set `Ω` containing `U` preserves `MemWkpLoc p U k` for every order `k` and exponent
`p`, and so does a field `A : ℂ → F →L[ℝ] G` of continuous linear maps between
finite-dimensional spaces that is smooth on `Ω`, acting pointwise by `z ↦ A z (u z)`.
Multiplying by a cutoff, applying a smooth almost complex structure `J` to a derivative, and
rewriting a map in a smooth trivialization are all of this form.

The proof is an induction on `k` through the weak Leibniz rule
`TauCeti.HasWeakFDerivOn.contDiffOn_smul`: the derivative of `χ u` is `χ Du + Dχ ⊗ u`, where the
first summand is again a smooth multiple of a map of order `k`, and the rank-one correction
`Dχ ⊗ u` splits along the real basis `1, i` of `ℂ` as `∂₁χ (re ⊗ u) + ∂₂χ (im ⊗ u)`, two smooth
multiples of constant continuous linear images of `u`. Neither step uses a basis of `F`, so the
scalar result holds for every real normed codomain. A field of maps between finite-dimensional
spaces is a finite sum of smooth scalar multiples of constant maps, which reduces the second
result to the first.

A factor whose support is a closed subset of the interior of `U` does more: the product extends by
zero to a local Sobolev map on the whole plane, since its weak derivatives on the interior of `U`
glue with zero off the support. This is the cutoff step that reduces local statements to compactly
supported ones.

Since the classes carry their `Lᵖ` bounds on compact subsets of `U` itself, the factor must be
continuous, with continuous derivatives, up to the boundary of `U`; asking for smoothness on an
open neighbourhood `Ω` of `U` provides this without a global smooth extension.

## Main declarations

* `TauCeti.MemLpLoc.continuousOn_smul`: a factor continuous on `U` preserves local `Lᵖ`.
* `TauCeti.MemWkpLoc.contDiffOn_smul`, `TauCeti.MemWkpLoc.contDiff_smul`: a smooth scalar
  factor preserves every local Sobolev class.
* `TauCeti.MemWkpLoc.hasWeakFDerivOn_contDiffOn_smul`: the Leibniz formula for the first weak
  derivative of `χ u`, with that derivative in the class of the preceding order.
* `TauCeti.MemLpLoc.continuous_smul_of_tsupport_subset`,
  `TauCeti.MemWkpLoc.contDiff_smul_of_tsupport_subset`: a cutoff supported inside `U` extends
  the product by zero to the whole plane.
* `TauCeti.MemWkpLoc.contDiffOn_clm_apply`, `TauCeti.MemWkpLoc.contDiff_clm_apply`: a smooth
  field of continuous linear maps between finite-dimensional spaces preserves every local Sobolev
  class.
* `TauCeti.MemWkpLoc.smul_contDiffOn`: a scalar local Sobolev function times a smooth
  finite-dimensional vector field.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (local Sobolev spaces and multiplication by smooth functions).
-/

public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ContDiff

namespace TauCeti

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {p : ENNReal} {U : Set ℂ} {Ω : Opens ℂ} {k : ℕ} {χ : ℂ → ℝ} {u : ℂ → F}

/-- A factor continuous on `U` preserves local `Lᵖ` membership on `U`, since it is bounded on
every compact subset of `U`. -/
theorem MemLpLoc.continuousOn_smul (hu : MemLpLoc p U u) (hχ : ContinuousOn χ U) :
    MemLpLoc p U (fun z => χ z • u z) :=
  memLpLoc_iff.2 fun K hK hc =>
    (memLpLoc_iff.1 (hχ.memLpLoc (p := ⊤)) K hK hc).smul (memLpLoc_iff.1 hu K hK hc)

/-- A continuous factor supported in `U` extends a local `Lᵖ` function on `U` by zero to a local
`Lᵖ` function on the whole plane: on a compact set `K` the product only sees
`K ∩ tsupport χ`, a compact subset of `U`. -/
theorem MemLpLoc.continuous_smul_of_tsupport_subset (hu : MemLpLoc p U u) (hχ : Continuous χ)
    (hsupp : tsupport χ ⊆ U) : MemLpLoc p Set.univ (fun z => χ z • u z) := by
  have hT := hu.continuousOn_smul hχ.continuousOn
  have hcl : IsClosed (tsupport χ) := isClosed_tsupport χ
  refine memLpLoc_iff.2 fun K _ hK => ?_
  have hf : (fun z => χ z • u z) = (tsupport χ).indicator (fun z => χ z • u z) := by
    refine (Set.indicator_eq_self.2 ?_).symm
    exact (Function.support_smul_subset_left χ u).trans (subset_tsupport χ)
  rw [hf, memLp_indicator_iff_restrict hcl.measurableSet.nullMeasurableSet,
    Measure.restrict_restrict hcl.measurableSet]
  exact memLpLoc_iff.1 hT _ (Set.inter_subset_left.trans hsupp) (hK.inter_left hcl)

/-- The rank-one map `L ⊗ w` determined by a real functional `L` on `ℂ` splits along the real
basis `1, i` of `ℂ`. -/
private theorem smulRight_eq_reCLM_add_imCLM (L : ℂ →L[ℝ] ℝ) (w : F) :
    L.smulRight w = L 1 • ContinuousLinearMap.smulRightL ℝ ℂ F Complex.reCLM w +
      L Complex.I • ContinuousLinearMap.smulRightL ℝ ℂ F Complex.imCLM w := by
  have hR : ∀ c : ℂ →L[ℝ] ℝ, ContinuousLinearMap.smulRightL ℝ ℂ F c w = c.smulRight w :=
    fun _ => rfl
  ext v
  have hv : L v = v.re * L 1 + v.im * L Complex.I := by
    conv_lhs => rw [show v = v.re • (1 : ℂ) + v.im • Complex.I by apply Complex.ext <;> simp]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  simp [hR, hv, smul_smul, add_smul, mul_comm]

/-- The derivative `χ Du + Dχ ⊗ u` of `χ u`, written as a sum of smooth scalar multiples. -/
private theorem leibniz_eq (χ : ℂ → ℝ) (u : ℂ → F) (D : ℂ → ℂ →L[ℝ] F) :
    (fun z => χ z • D z + (fderiv ℝ χ z).smulRight (u z)) =
      (fun z => χ z • D z) +
        ((fun z => fderiv ℝ χ z 1 • ContinuousLinearMap.smulRightL ℝ ℂ F Complex.reCLM (u z)) +
          fun z => fderiv ℝ χ z Complex.I •
            ContinuousLinearMap.smulRightL ℝ ℂ F Complex.imCLM (u z)) := by
  funext z
  simp only [Pi.add_apply, smulRight_eq_reCLM_add_imCLM]

/-- The partial derivatives of a factor smooth on an open set are smooth there. -/
private theorem contDiffOn_fderiv_apply (hχ : ContDiffOn ℝ ∞ χ Ω) (v : ℂ) :
    ContDiffOn ℝ ∞ (fun z => fderiv ℝ χ z v) Ω :=
  (hχ.fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply contDiffOn_const

/-- **Multiplication by a smooth factor.** A factor that is smooth on an open neighbourhood of
`U` preserves the local Sobolev class `MemWkpLoc p U k`, for every order, exponent and real normed
codomain. The weak derivatives are those of the Leibniz rule
`TauCeti.HasWeakFDerivOn.contDiffOn_smul`. -/
theorem MemWkpLoc.contDiffOn_smul (hu : MemWkpLoc p U k u) (hχ : ContDiffOn ℝ ∞ χ Ω)
    (hU : U ⊆ Ω) : MemWkpLoc p U k (fun z => χ z • u z) := by
  induction k generalizing F χ with
  | zero =>
    exact memWkpLoc_zero_iff.2 ((memWkpLoc_zero_iff.1 hu).continuousOn_smul
      (hχ.continuousOn.mono hU))
  | succ k ih =>
    have hu' : MemWkpLoc p U k u := hu.of_succ
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hu
    have := hD.completeSpace
    refine memWkpLoc_succ_iff.2 ⟨hp.continuousOn_smul (hχ.continuousOn.mono hU), _,
      hD.contDiffOn_smul (hχ.mono fun z hz => hU (interior_subset hz)), ?_⟩
    rw [leibniz_eq]
    exact (ih hk hχ).add
      ((ih (hu'.clm_comp _) (contDiffOn_fderiv_apply hχ 1)).add
        (ih (hu'.clm_comp _) (contDiffOn_fderiv_apply hχ Complex.I)))

/-- **Multiplication by a smooth factor**, for a factor smooth on all of `ℂ`. -/
theorem MemWkpLoc.contDiff_smul (hu : MemWkpLoc p U k u) (hχ : ContDiff ℝ ∞ χ) :
    MemWkpLoc p U k (fun z => χ z • u z) :=
  hu.contDiffOn_smul (Ω := ⊤) hχ.contDiffOn (by simp)

/-- **The Leibniz formula in a local Sobolev class.** If `D` is a weak derivative of `u` on the
interior of `U` and both lie in `MemWkpLoc p U k`, then `χ Du + Dχ ⊗ u` is a weak derivative of
`χ u` on the interior of `U`, again in `MemWkpLoc p U k`. -/
theorem MemWkpLoc.hasWeakFDerivOn_contDiffOn_smul {D : ℂ → ℂ →L[ℝ] F}
    (hu : MemWkpLoc p U k u) (hD : HasWeakFDerivOn volume (Opens.interior U) u D)
    (hDk : MemWkpLoc p U k D) (hχ : ContDiffOn ℝ ∞ χ Ω) (hU : U ⊆ Ω) :
    HasWeakFDerivOn volume (Opens.interior U) (fun z => χ z • u z)
        (fun z => χ z • D z + (fderiv ℝ χ z).smulRight (u z)) ∧
      MemWkpLoc p U k (fun z => χ z • D z + (fderiv ℝ χ z).smulRight (u z)) := by
  have := hD.completeSpace
  refine ⟨hD.contDiffOn_smul (hχ.mono fun z hz => hU (interior_subset hz)), ?_⟩
  rw [leibniz_eq]
  exact (hDk.contDiffOn_smul hχ hU).add
    (((hu.clm_comp _).contDiffOn_smul (contDiffOn_fderiv_apply hχ 1) hU).add
      ((hu.clm_comp _).contDiffOn_smul (contDiffOn_fderiv_apply hχ Complex.I) hU))

/-- **Cutoff localization.** Multiplying a local Sobolev map on `U` by a smooth factor whose
support is a closed subset of the interior of `U` gives a local Sobolev map on the whole plane:
the product and its weak derivatives vanish off `tsupport χ`, so the derivatives on the interior
of `U` glue with zero across the complement of the support. -/
theorem MemWkpLoc.contDiff_smul_of_tsupport_subset (hu : MemWkpLoc p U k u)
    (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ interior U) :
    MemWkpLoc p Set.univ k (fun z => χ z • u z) := by
  induction k generalizing F χ u with
  | zero =>
    exact memWkpLoc_zero_iff.2 ((memWkpLoc_zero_iff.1 hu).continuous_smul_of_tsupport_subset
      hχ.continuous (hsupp.trans interior_subset))
  | succ k ih =>
    have hu' : MemWkpLoc p U k u := hu.of_succ
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hu
    have := hD.completeSpace
    have hdχ : ∀ v, ContDiff ℝ ∞ (fun z => fderiv ℝ χ z v) := fun v =>
      contDiffOn_univ.1 (by simpa using contDiffOn_fderiv_apply (Ω := ⊤) hχ.contDiffOn v)
    have hsuppd : ∀ v, tsupport (fun z => fderiv ℝ χ z v) ⊆ interior U := fun v =>
      (closure_mono (Function.support_subset_iff'.2 fun z hz => by
        simp [Function.notMem_support.1 hz])).trans ((tsupport_fderiv_subset ℝ).trans hsupp)
    refine memWkpLoc_succ_iff.2 ⟨hp.continuous_smul_of_tsupport_subset hχ.continuous
      (hsupp.trans interior_subset), fun z => χ z • D z + (fderiv ℝ χ z).smulRight (u z), ?_, ?_⟩
    · -- Glue the Leibniz rule on the interior of `U` with zero off the support of `χ`.
      let V : Opens ℂ := ⟨(tsupport χ)ᶜ, (isClosed_tsupport χ).isOpen_compl⟩
      have h1 := hD.contDiffOn_smul (hχ.contDiffOn (s := Opens.interior U))
      have h2 : HasWeakFDerivOn volume V (fun z => χ z • u z)
          (fun z => χ z • D z + (fderiv ℝ χ z).smulRight (u z)) := by
        refine ((hasWeakFDerivOn_zero (μ := volume) (Ω := V) (F := F)).congr_ae ?_).congr_ae_deriv
          ?_ <;>
        · filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with z hz
          simp [image_eq_zero_of_notMem_tsupport hz, fderiv_of_notMem_tsupport ℝ hz]
      refine (h1.sup h2).mono fun z _ => ?_
      by_cases hz : z ∈ tsupport χ
      · exact Or.inl (hsupp hz)
      · exact Or.inr hz
    · rw [leibniz_eq]
      exact (ih hk hχ hsupp).add ((ih (hu'.clm_comp _) (hdχ 1) (hsuppd 1)).add
        (ih (hu'.clm_comp _) (hdχ Complex.I) (hsuppd Complex.I)))

/-- **Smooth fields of continuous linear maps.** A field `A` of continuous linear maps between
finite-dimensional spaces that is smooth on an open neighbourhood of `U` preserves the local
Sobolev class pointwise: `z ↦ A z (u z)` lies in `MemWkpLoc p U k` whenever `u` does. -/
theorem MemWkpLoc.contDiffOn_clm_apply [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]
    {A : ℂ → F →L[ℝ] G} (hu : MemWkpLoc p U k u) (hA : ContDiffOn ℝ ∞ A Ω) (hU : U ⊆ Ω) :
    MemWkpLoc p U k (fun z => A z (u z)) := by
  -- Expand `A` in a basis `(bₘ)` of `F →L[ℝ] G`: `A z = ∑ₘ cₘ (A z) • bₘ` with smooth scalar
  -- coordinates, to each of which the scalar result applies.
  set b := Module.finBasis ℝ (F →L[ℝ] G)
  let c : Fin (Module.finrank ℝ (F →L[ℝ] G)) → (F →L[ℝ] G) →L[ℝ] ℝ := fun m =>
    LinearMap.toContinuousLinearMap (b.coord m)
  have hrepr : (fun z => A z (u z)) = fun z => ∑ m, c m (A z) • b m (u z) := by
    funext z
    calc A z (u z) = (∑ m, b.repr (A z) m • b m) (u z) := by rw [b.sum_repr]
      _ = ∑ m, c m (A z) • b m (u z) := by
        simp [-Module.Basis.sum_repr, c]
  rw [hrepr]
  exact MemWkpLoc.sum Finset.univ fun m _ =>
    (hu.clm_comp (b m)).contDiffOn_smul ((c m).contDiff.comp_contDiffOn hA) hU

/-- **Smooth fields of continuous linear maps**, for a field smooth on all of `ℂ`. -/
theorem MemWkpLoc.contDiff_clm_apply [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]
    {A : ℂ → F →L[ℝ] G} (hu : MemWkpLoc p U k u) (hA : ContDiff ℝ ∞ A) :
    MemWkpLoc p U k (fun z => A z (u z)) :=
  hu.contDiffOn_clm_apply (Ω := ⊤) hA.contDiffOn (by simp)

/-- A scalar local Sobolev function times a vector field that is smooth on an open neighbourhood
of `U`, with values in a finite-dimensional space, is again in the local Sobolev class. -/
theorem MemWkpLoc.smul_contDiffOn [FiniteDimensional ℝ G] {a : ℂ → ℝ} {g : ℂ → G}
    (ha : MemWkpLoc p U k a) (hg : ContDiffOn ℝ ∞ g Ω) (hU : U ⊆ Ω) :
    MemWkpLoc p U k (fun z => a z • g z) := by
  have h := ha.contDiffOn_clm_apply
    (((ContinuousLinearMap.smulRightL ℝ ℝ G) (ContinuousLinearMap.id ℝ ℝ)).contDiff.comp_contDiffOn
      hg) hU
  simpa using h

end TauCeti

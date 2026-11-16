/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.Analysis.Calculus.ContDiff.FDerivApply
import TauCeti.Analysis.Complex.Coordinates
import TauCeti.Analysis.Sobolev.Leibniz
import TauCeti.Analysis.Sobolev.WeakDeriv.Local

/-!
# Local Sobolev classes under `C^k` coefficients

`TauCeti.MemWkpLoc.clm_comp` composes a local Sobolev map with one fixed continuous linear map.
This file lets the coefficient vary with the point. A factor `χ : ℂ → ℝ` that is `C^n` on an open
set `Ω` containing `U` preserves `MemWkpLoc p U k` for every order `k ≤ n` and exponent `p`, and so
does a field `A : ℂ → F →L[ℝ] G` of continuous linear maps between finite-dimensional spaces that
is `C^n` on `Ω`, acting pointwise by `z ↦ A z (u z)`. Multiplying by a cutoff, applying an almost
complex structure `J` of class `C^ℓ` to a derivative, and rewriting a map in a `C^ℓ`
trivialization are all of this form. Only `k` derivatives of the coefficient are used, so smooth
coefficients are the case `n = ∞`.

The induction on `k` runs through the Leibniz rule `D(χ u) = χ Du + Dχ ⊗ u`, which needs `χ` only
`C¹` (`TauCeti.HasWeakFDerivOn.contDiffOn_smul_of_ne_zero`); the two summands are coefficients
of class `C^{n-1}` applied to maps of order `k`. For `1 ≤ p` and any measure on which `|χ| ≤ A`
and `‖Dχ‖ ≤ B` almost everywhere, in particular Lebesgue measure restricted to a measurable set
`K`, the derivative obeys `‖D(χ u)‖_{Lᵖ} ≤ A ‖Du‖_{Lᵖ} + B ‖u‖_{Lᵖ}`
(`TauCeti.eLpNorm_smul_add_fderiv_smulRight_le`).

A factor whose support is a closed subset of the interior of `U` does more: the product extends by
zero to a local Sobolev map on the whole plane. This is the cutoff step that reduces local
statements to compactly supported ones.

Since the classes carry their `Lᵖ` bounds on compact subsets of `U` itself, the factor must be
continuous, with continuous derivatives, up to the boundary of `U`; asking for regularity on an
open neighbourhood `Ω` of `U` provides this without a global extension.

## Main declarations

* `TauCeti.MemWkpLoc.contDiffOn_smul`, `TauCeti.MemWkpLoc.contDiff_smul`: a `C^n` scalar factor
  preserves every local Sobolev class of order `k ≤ n`.
* `TauCeti.MemWkpLoc.hasWeakFDerivOn_contDiffOn_smul`: the Leibniz formula for the first weak
  derivative of `χ u`, for `χ` of class `C^n` with `k + 1 ≤ n`, with that derivative in the class
  of the preceding order.
* `TauCeti.MemWkpLoc.contDiff_smul_of_tsupport_subset`: a cutoff supported inside `U` extends
  the product by zero to the whole plane.
* `TauCeti.MemWkpLoc.contDiffOn_clm_apply`, `TauCeti.MemWkpLoc.contDiff_clm_apply`: a `C^n`
  field of continuous linear maps between finite-dimensional spaces preserves every local Sobolev
  class of order `k ≤ n`.
* `TauCeti.MemWkpLoc.smul_contDiffOn`: a scalar local Sobolev function times a `C^n`
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
  [NormedSpace ℝ G] {p : ENNReal} {U : Set ℂ} {Ω : Opens ℂ} {k : ℕ} {n : WithTop ℕ∞}
  {χ : ℂ → ℝ} {u : ℂ → F}

/-- The derivative `χ Du + Dχ ⊗ u` of `χ u`, written as a sum of scalar multiples by `χ` and the
components of `Dχ`. -/
private theorem leibniz_eq (χ : ℂ → ℝ) (u : ℂ → F) (D : ℂ → ℂ →L[ℝ] F) :
    (fun z => χ z • D z + (fderiv ℝ χ z).smulRight (u z)) =
      (fun z => χ z • D z) +
        ((fun z => fderiv ℝ χ z 1 • ContinuousLinearMap.smulRightL ℝ ℂ F Complex.reCLM (u z)) +
          fun z => fderiv ℝ χ z Complex.I •
            ContinuousLinearMap.smulRightL ℝ ℂ F Complex.imCLM (u z)) := by
  have hR (c : ℂ →L[ℝ] ℝ) (w : F) : ContinuousLinearMap.smulRightL ℝ ℂ F c w = c.smulRight w := by
    ext
    simp
  funext z
  rw [Pi.add_apply, Pi.add_apply, ContinuousLinearMap.smulRight_eq_re_add_im, hR, hR]

/-- **Multiplication by a `C^k` factor.** A factor that is `C^n` on an open neighbourhood of `U`,
with `k ≤ n`, preserves the local Sobolev class `MemWkpLoc p U k`, for every exponent and real
normed codomain. The weak derivatives are those of the Leibniz rule
`TauCeti.HasWeakFDerivOn.contDiffOn_smul_of_ne_zero`. -/
theorem MemWkpLoc.contDiffOn_smul (hu : MemWkpLoc p U k u) (hχ : ContDiffOn ℝ n χ Ω)
    (hk : (k : WithTop ℕ∞) ≤ n) (hU : U ⊆ Ω) : MemWkpLoc p U k (fun z => χ z • u z) := by
  -- Induct on `k` through the weak Leibniz rule: the derivative `χ Du + Dχ ⊗ u` of `χ u` is a
  -- `C^k` multiple of `Du` plus, after splitting `Dχ ⊗ u` along the real basis `1, I` of `ℂ`,
  -- two `C^k` multiples of constant continuous linear images of `u`; all three have order `k`.
  -- No basis of `F` is used, so `F` may be any real normed space.
  induction k generalizing F χ n with
  | zero =>
    exact memWkpLoc_zero_iff.2 ((memWkpLoc_zero_iff.1 hu).continuousOn_smul
      (hχ.continuousOn.mono hU))
  | succ k ih =>
    have hu' : MemWkpLoc p U k u := hu.of_succ
    obtain ⟨hp, D, hD, hDk⟩ := memWkpLoc_succ_iff.1 hu
    have := hD.completeSpace
    have hk' : (k : WithTop ℕ∞) + 1 ≤ n := by exact_mod_cast hk
    have hkn : (k : WithTop ℕ∞) ≤ n := le_trans (by exact_mod_cast k.le_succ) hk
    refine memWkpLoc_succ_iff.2 ⟨hp.continuousOn_smul (hχ.continuousOn.mono hU), _,
      hD.contDiffOn_smul_of_ne_zero (hχ.mono fun z hz => hU (interior_subset hz))
        (lt_of_lt_of_le (by simp) hk).ne', ?_⟩
    rw [leibniz_eq]
    exact (ih hDk hχ hkn).add
      ((ih (hu'.clm_comp _) (hχ.fderiv_apply_of_isOpen Ω.isOpen hk' 1) le_rfl).add
        (ih (hu'.clm_comp _) (hχ.fderiv_apply_of_isOpen Ω.isOpen hk' Complex.I) le_rfl))

/-- **Multiplication by a `C^k` factor**, for a factor that is `C^n` on all of `ℂ`, `k ≤ n`. -/
theorem MemWkpLoc.contDiff_smul (hu : MemWkpLoc p U k u) (hχ : ContDiff ℝ n χ)
    (hk : (k : WithTop ℕ∞) ≤ n) : MemWkpLoc p U k (fun z => χ z • u z) :=
  hu.contDiffOn_smul (Ω := ⊤) hχ.contDiffOn hk (by simp)

/-- **The Leibniz formula in a local Sobolev class.** If `D` is a weak derivative of `u` on the
interior of `U`, both lie in `MemWkpLoc p U k`, and `χ` is `C^n` on an open neighbourhood of `U`
with `k + 1 ≤ n`, then `χ Du + Dχ ⊗ u` is a weak derivative of `χ u` on the interior of `U`,
again in `MemWkpLoc p U k`. -/
theorem MemWkpLoc.hasWeakFDerivOn_contDiffOn_smul {D : ℂ → ℂ →L[ℝ] F}
    (hu : MemWkpLoc p U k u) (hD : HasWeakFDerivOn volume (Opens.interior U) u D)
    (hDk : MemWkpLoc p U k D) (hχ : ContDiffOn ℝ n χ Ω) (hk : (k : WithTop ℕ∞) + 1 ≤ n)
    (hU : U ⊆ Ω) :
    HasWeakFDerivOn volume (Opens.interior U) (fun z => χ z • u z)
        (fun z => χ z • D z + (fderiv ℝ χ z).smulRight (u z)) ∧
      MemWkpLoc p U k (fun z => χ z • D z + (fderiv ℝ χ z).smulRight (u z)) := by
  have := hD.completeSpace
  have hkn : (k : WithTop ℕ∞) ≤ n := le_trans (by simp) hk
  refine ⟨hD.contDiffOn_smul_of_ne_zero (hχ.mono fun z hz => hU (interior_subset hz))
    (lt_of_lt_of_le (by simp) hk).ne', ?_⟩
  rw [leibniz_eq]
  exact (hDk.contDiffOn_smul hχ hkn hU).add
    (((hu.clm_comp _).contDiffOn_smul (hχ.fderiv_apply_of_isOpen Ω.isOpen hk 1) le_rfl hU).add
      ((hu.clm_comp _).contDiffOn_smul (hχ.fderiv_apply_of_isOpen Ω.isOpen hk Complex.I) le_rfl
        hU))

/-- **Cutoff localization.** Multiplying a local Sobolev map on `U` by a `C^n` factor, `k ≤ n`,
whose support is a closed subset of the interior of `U` gives a local Sobolev map on the whole
plane: the product and its weak derivatives vanish off `tsupport χ`, so the derivatives on the
interior of `U` glue with zero across the complement of the support. -/
theorem MemWkpLoc.contDiff_smul_of_tsupport_subset (hu : MemWkpLoc p U k u)
    (hχ : ContDiff ℝ n χ) (hk : (k : WithTop ℕ∞) ≤ n) (hsupp : tsupport χ ⊆ interior U) :
    MemWkpLoc p Set.univ k (fun z => χ z • u z) := by
  induction k generalizing F χ u n with
  | zero =>
    exact memWkpLoc_zero_iff.2 ((memWkpLoc_zero_iff.1 hu).continuous_smul_of_tsupport_subset
      hχ.continuous (hsupp.trans interior_subset))
  | succ k ih =>
    have hu' : MemWkpLoc p U k u := hu.of_succ
    obtain ⟨hp, D, hD, hDk⟩ := memWkpLoc_succ_iff.1 hu
    have := hD.completeSpace
    have hk' : (k : WithTop ℕ∞) + 1 ≤ n := by exact_mod_cast hk
    have hkn : (k : WithTop ℕ∞) ≤ n := le_trans (by exact_mod_cast k.le_succ) hk
    have hdχ : ∀ v, ContDiff ℝ k (fun z => fderiv ℝ χ z v) := fun v =>
      (hχ.fderiv_right hk').clm_apply contDiff_const
    have hsuppd : ∀ v, tsupport (fun z => fderiv ℝ χ z v) ⊆ interior U := fun v =>
      (tsupport_fderiv_apply_subset ℝ v).trans hsupp
    refine memWkpLoc_succ_iff.2 ⟨hp.continuous_smul_of_tsupport_subset hχ.continuous
      (hsupp.trans interior_subset), fun z => χ z • D z + (fderiv ℝ χ z).smulRight (u z), ?_, ?_⟩
    · -- Glue the Leibniz rule on the interior of `U` with zero off the support of `χ`.
      let V : Opens ℂ := ⟨(tsupport χ)ᶜ, (isClosed_tsupport χ).isOpen_compl⟩
      have h1 := hD.contDiffOn_smul_of_ne_zero (hχ.contDiffOn (s := Opens.interior U))
        (lt_of_lt_of_le (by simp) hk).ne'
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
      exact (ih hDk hχ hkn hsupp).add ((ih (hu'.clm_comp _) (hdχ 1) le_rfl (hsuppd 1)).add
        (ih (hu'.clm_comp _) (hdχ Complex.I) le_rfl (hsuppd Complex.I)))

/-- **`C^k` fields of continuous linear maps.** A field `A` of continuous linear maps between
finite-dimensional spaces that is `C^n` on an open neighbourhood of `U`, with `k ≤ n`, preserves
the local Sobolev class pointwise: `z ↦ A z (u z)` lies in `MemWkpLoc p U k` whenever `u` does. -/
theorem MemWkpLoc.contDiffOn_clm_apply [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]
    {A : ℂ → F →L[ℝ] G} (hu : MemWkpLoc p U k u) (hA : ContDiffOn ℝ n A Ω)
    (hk : (k : WithTop ℕ∞) ≤ n) (hU : U ⊆ Ω) :
    MemWkpLoc p U k (fun z => A z (u z)) := by
  -- Expand `A` in a basis `(bₘ)` of `F →L[ℝ] G`: `A z = ∑ₘ cₘ (A z) • bₘ` with `C^n` scalar
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
    (hu.clm_comp (b m)).contDiffOn_smul ((c m).contDiff.comp_contDiffOn hA) hk hU

/-- **`C^k` fields of continuous linear maps**, for a field that is `C^n` on all of `ℂ`,
`k ≤ n`. -/
theorem MemWkpLoc.contDiff_clm_apply [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]
    {A : ℂ → F →L[ℝ] G} (hu : MemWkpLoc p U k u) (hA : ContDiff ℝ n A)
    (hk : (k : WithTop ℕ∞) ≤ n) : MemWkpLoc p U k (fun z => A z (u z)) :=
  hu.contDiffOn_clm_apply (Ω := ⊤) hA.contDiffOn hk (by simp)

/-- A scalar local Sobolev function times a vector field that is `C^n` on an open neighbourhood
of `U`, `k ≤ n`, with values in a finite-dimensional space, is again in the local Sobolev
class. -/
theorem MemWkpLoc.smul_contDiffOn [FiniteDimensional ℝ G] {a : ℂ → ℝ} {g : ℂ → G}
    (ha : MemWkpLoc p U k a) (hg : ContDiffOn ℝ n g Ω) (hk : (k : WithTop ℕ∞) ≤ n)
    (hU : U ⊆ Ω) : MemWkpLoc p U k (fun z => a z • g z) := by
  have h := ha.contDiffOn_clm_apply
    (((ContinuousLinearMap.smulRightL ℝ ℝ G) (ContinuousLinearMap.id ℝ ℝ)).contDiff.comp_contDiffOn
      hg) hk hU
  simpa using h

end TauCeti

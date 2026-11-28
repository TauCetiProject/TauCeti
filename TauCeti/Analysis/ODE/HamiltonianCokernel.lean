/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SymplecticCokernel
public import TauCeti.Analysis.ODE.Periodic

/-!
# The cokernel of a periodic linear Hamiltonian equation and its orientation

Let `X` be a finite-dimensional real inner product space, `J` an injective operator on `X` and
`M : ℝ → (X →L[ℝ] X)` a continuous `d`-periodic path, `d > 0`, of operators skew for the form
`ω(u, w) = ⟪J u, w⟫`: `ω(M r u, w) + ω(u, M r w) = 0`. For an orthogonal complex structure `J`
this says that `w' = M w` is a linear Hamiltonian equation; the normal equation `w' = J₀ S(t) w`
of a periodic orbit, with `S(t)` symmetric, is the example. The propagator `Ψ` of `w' = M w`
preserves `ω` (`TauCeti.inner_apply_dysonSeriesLeft_apply_dysonSeriesLeft_apply_of_skew`), and so
does the return map `P = Ψ(d)`.

For a sign `ε` with `ε ^ 2 = 1`, the operator `L w = w' - M w` on maps twisted by `ε` along `d`
(`TauCeti.twistedLinearOperator`) has kernel and cokernel identified with those of `ε - P`
(`TauCeti.kerTwistedLinearOperatorEquiv`, by evaluation at `0`, and
`TauCeti.quotientRangeTwistedLinearOperatorEquiv`, by the endpoint map
`E g = Ψ(d) ∫₀ᵈ Ψ(s)⁻¹ g(s) ds` of variation of constants). On the other hand
`x ↦ [J x]` identifies the kernel of `ε - P` with its cokernel
(`TauCeti.kerEquivQuotientRangeOfInnerApplyEq`). This file compares these identifications with the
map that applies `J` pointwise to the solutions of `w' = M w`
(`TauCeti.kerTwistedLinearOperatorToQuotientRange`), from the kernel of `L` to its cokernel.

For solutions `Ψ(t) x` and `Ψ(t) y` with `x` and `y` in the `ε`-eigenspace of `P`, the symplectic
invariance of `Ψ` gives

`⟪J y, E (J Ψ(·) x)⟫ = ε ∫₀ᵈ ⟪J Ψ(s) y, J Ψ(s) x⟫ ds`

(`TauCeti.kerQuotientRangePairing_kerTwistedLinearOperatorToQuotientRange`), a positive definite
symmetric form in `x` and `y`, up to the sign `ε`. So for the pairing `β(y, [z]) = ⟪J y, z⟫` of
the kernel of `ε - P` with its cokernel, the map `x ↦ [ε • E (J Ψ(·) x)]` is positive, like
`x ↦ [J x]`
(`TauCeti.kerQuotientRangePairing_smul_kerTwistedLinearOperatorToQuotientRange_pos`). Hence:

* pointwise application of `J` is an isomorphism from the kernel of `L` onto its cokernel
  (`TauCeti.bijective_kerTwistedLinearOperatorToQuotientRange`);
* read through the kernel and endpoint identifications and multiplied by `ε`, it differs from
  `x ↦ [J x]` by an automorphism of the kernel of `ε - P` of positive determinant
  (`TauCeti.det_pos_symm_comp_kerTwistedLinearOperatorToQuotientRange`).

So the two ways of identifying the determinant line `det (ker L) ⊗ (det (coker L))^*` with
`det (ker (ε - P)) ⊗ (det (ker (ε - P)))^*`, through `ε` times pointwise `J` and through the
endpoint map followed by `x ↦ [J x]`, induce the same orientation, whether or not `ε - P` is
invertible; pointwise `J` itself changes this orientation by the sign `ε ^ dim ker (ε - P)`. When
`J` is an orthogonal complex structure, `J` carries the kernel of `L` onto the kernel of its formal
adjoint, which is how the cokernel of the normal operator of an orbit torus is computed; this
fixes the sign of that identification. With `J₀ ^ 2 = -1` and `M = J₀ S`, the endpoint of the
solution of `J₀ w' + S w = Ψ(t) v` with `w(0) = 0` is `E (-J₀ Ψ(·) v)`, and multiplying both
identifications by `-ε` compares `v ↦ [E (-J₀ Ψ(·) v)]` with `v ↦ [-ε J₀ v]`.

## Main definitions

* `TauCeti.kerTwistedLinearOperatorToQuotientRange`: the map `w ↦ [J w]` from the kernel of
  `L = d/dt - M` to its cokernel.

## Main results

* `TauCeti.inner_apply_dysonSeriesLeft_apply_dysonSeriesLeft_apply_of_skew`: the propagator of a
  path skew for `⟪J ·, ·⟫` preserves this form.
* `TauCeti.kerQuotientRangePairing_kerTwistedLinearOperatorToQuotientRange`: the pairing of the
  endpoint of `J Ψ(·) x` with `y`, and its positivity
  `TauCeti.kerQuotientRangePairing_smul_kerTwistedLinearOperatorToQuotientRange_pos`.
* `TauCeti.det_pos_symm_comp_kerTwistedLinearOperatorToQuotientRange`: the orientation
  comparison.
* `TauCeti.bijective_kerTwistedLinearOperatorToQuotientRange`: pointwise `J` identifies the kernel
  of `L` with its cokernel.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (determinant lines).
-/

public section

noncomputable section

open Set
open scoped RealInnerProductSpace

namespace TauCeti

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  {M : ℝ → X →L[ℝ] X} {J : X →L[ℝ] X} {d ε : ℝ}

section Propagator

variable [CompleteSpace X]

/-- **The propagator of a linear Hamiltonian equation is symplectic.** If every `M r` is skew for
the form `⟪J ·, ·⟫`, the propagator `Ψ = dysonSeriesLeft M` of `w' = M w` preserves it. -/
theorem inner_apply_dysonSeriesLeft_apply_dysonSeriesLeft_apply_of_skew (hM : Continuous M)
    (hskew : ∀ r u w, ⟪J (M r u), w⟫ + ⟪J u, M r w⟫ = 0) (t : ℝ) (x y : X) :
    ⟪J (dysonSeriesLeft M t x), dysonSeriesLeft M t y⟫ = ⟪J x, y⟫ := by
  simpa using apply_dysonSeriesLeft_apply_dysonSeriesLeft hM ((innerSL ℝ).comp J)
    (by simpa using hskew) t x y

end Propagator

section Kernel

variable (J) in
/-- Pointwise application of `J` to the twisted solutions of `w' = M w`, with values in the
cokernel of `L = d/dt - M` on maps twisted by `ε` along `d`: `w ↦ [J w]`. -/
def kerTwistedLinearOperatorToQuotientRange (hM : Continuous M) (hper : Function.Periodic M d)
    (ε : ℝ) :
    LinearMap.ker (twistedLinearOperator hM hper ε) →ₗ[ℝ]
      twistedContinuous X d ε ⧸ LinearMap.range (twistedLinearOperator hM hper ε) :=
  (LinearMap.range (twistedLinearOperator hM hper ε)).mkQ ∘ₗ twistedContinuousCompLeft J ∘ₗ
    Submodule.inclusion twistedContDiff_le_twistedContinuous ∘ₗ
    (LinearMap.ker (twistedLinearOperator hM hper ε)).subtype

/-- The class `[J w]` of the pointwise image of a twisted solution `w` of `w' = M w`. -/
@[simp]
theorem kerTwistedLinearOperatorToQuotientRange_apply (hM : Continuous M)
    (hper : Function.Periodic M d) (w : LinearMap.ker (twistedLinearOperator hM hper ε)) :
    kerTwistedLinearOperatorToQuotientRange J hM hper ε w =
      Submodule.Quotient.mk (twistedContinuousCompLeft J
        (Submodule.inclusion twistedContDiff_le_twistedContinuous (w : twistedContDiff X d ε))) :=
  (rfl)

section Complete

variable [CompleteSpace X]

/-- Read through the endpoint identification of the cokernel of `L`, the class of `J w` is the
class of the endpoint `E (J w) = Ψ(d) ∫₀ᵈ Ψ(s)⁻¹ (J (w s)) ds`. -/
theorem quotientRangeTwistedLinearOperatorEquiv_kerTwistedLinearOperatorToQuotientRange
    (hM : Continuous M) (hper : Function.Periodic M d) (hd : 0 < d) (hε : ε ≠ 0)
    (w : LinearMap.ker (twistedLinearOperator hM hper ε)) :
    quotientRangeTwistedLinearOperatorEquiv hM hper hd hε
        (kerTwistedLinearOperatorToQuotientRange J hM hper ε w) =
      Submodule.Quotient.mk
        (dysonSeriesLeft M d (∫ s in 0..d, dysonSeries (-M) s (J ((w.val : ℝ → X) s)))) := by
  simp

/-- **The endpoint of `J Ψ(·) x` against `y`.** For `x` and `y` in the `ε`-eigenspace of the
return map `Ψ(d)` of a linear Hamiltonian equation, with `ε ^ 2 = 1`, the pairing of `y` with the
cokernel class of the endpoint of `J Ψ(·) x` is `ε ∫₀ᵈ ⟪J Ψ(s) y, J Ψ(s) x⟫ ds`. -/
theorem kerQuotientRangePairing_kerTwistedLinearOperatorToQuotientRange (hM : Continuous M)
    (hper : Function.Periodic M d) (hd : 0 < d) (hε : ε ^ 2 = 1)
    (hskew : ∀ r u w, ⟪J (M r u), w⟫ + ⟪J u, M r w⟫ = 0)
    (x y : LinearMap.ker (ε • 1 - ((dysonSeriesLeft M d : X →L[ℝ] X) : X →ₗ[ℝ] X))) :
    kerQuotientRangePairing (J : X →ₗ[ℝ] X) (ε • 1 - ((dysonSeriesLeft M d : X →L[ℝ] X) :
        X →ₗ[ℝ] X))
        (inner_apply_dysonSeriesLeft_apply_dysonSeriesLeft_apply_of_skew hM hskew d)
        hε (fun x => by simp) y
        (quotientRangeTwistedLinearOperatorEquiv hM hper hd
          (IsUnit.of_pow_eq_one hε two_ne_zero).ne_zero
          (kerTwistedLinearOperatorToQuotientRange J hM hper ε
            ((kerTwistedLinearOperatorEquiv hM hper ε).symm x))) =
      ε * ∫ s in 0..d, ⟪J (dysonSeriesLeft M s y), J (dysonSeriesLeft M s x)⟫ := by
  -- `y` is an `ε`-eigenvector of the return map.
  have hy : ε • (y : X) = dysonSeriesLeft M d y := by
    simpa [sub_eq_zero, -LinearMap.map_coe_ker] using LinearMap.map_coe_ker _ y
  -- The integrand of the endpoint is continuous.
  have hcont : Continuous fun s => dysonSeries (-M) s (J (dysonSeriesLeft M s x)) :=
    (continuous_dysonSeries hM.neg).clm_apply
      (J.continuous.comp ((continuous_dysonSeriesLeft hM).clm_apply continuous_const))
  -- Since `Ψ(d)` preserves `⟪J ·, ·⟫` and fixes `y` up to `ε`, `⟪J y, Ψ(d) z⟫ = ε ⟪J y, z⟫`.
  have hret (z : X) : ⟪J y, dysonSeriesLeft M d z⟫ = ε * ⟪J y, z⟫ := by
    have h := inner_apply_dysonSeriesLeft_apply_dysonSeriesLeft_apply_of_skew hM hskew d y z
    rw [← hy, map_smul, real_inner_smul_left] at h
    rw [← h, ← mul_assoc, ← sq, hε, one_mul]
  simp only [quotientRangeTwistedLinearOperatorEquiv_kerTwistedLinearOperatorToQuotientRange,
    kerTwistedLinearOperatorEquiv_symm_apply, kerQuotientRangePairing_mk,
    ContinuousLinearMap.coe_coe]
  have hcomm := (innerSL ℝ (J y)).intervalIntegral_comp_comm
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 d)
  -- `Ψ(s)⁻¹ = dysonSeries (-M) s` is the adjoint of `Ψ(s)` for `⟪J ·, ·⟫`.
  have hadj (s : ℝ) (z : X) : ⟪J y, dysonSeries (-M) s z⟫ = ⟪J (dysonSeriesLeft M s y), z⟫ := by
    simpa using apply_dysonSeries_neg_apply hM ((innerSL ℝ).comp J) (by simpa using hskew) s y z
  simp only [innerSL_apply_apply, hadj] at hcomm
  rw [hret, ← hcomm]

/-- **The endpoint of `ε • J Ψ(·) x` pairs positively with `x`.** For `x ≠ 0` in the `ε`-eigenspace
of the return map of a linear Hamiltonian equation with `J` injective, the pairing of `x` with the
cokernel class of `ε` times the endpoint of `J Ψ(·) x` is `∫₀ᵈ ‖J Ψ(s) x‖² ds > 0`. -/
theorem kerQuotientRangePairing_smul_kerTwistedLinearOperatorToQuotientRange_pos
    (hM : Continuous M) (hper : Function.Periodic M d) (hd : 0 < d) (hε : ε ^ 2 = 1)
    (hJ : Function.Injective J) (hskew : ∀ r u w, ⟪J (M r u), w⟫ + ⟪J u, M r w⟫ = 0)
    {x : LinearMap.ker (ε • 1 - ((dysonSeriesLeft M d : X →L[ℝ] X) : X →ₗ[ℝ] X))} (hx : x ≠ 0) :
    0 < kerQuotientRangePairing (J : X →ₗ[ℝ] X) (ε • 1 - ((dysonSeriesLeft M d : X →L[ℝ] X) :
        X →ₗ[ℝ] X))
        (inner_apply_dysonSeriesLeft_apply_dysonSeriesLeft_apply_of_skew hM hskew d)
        hε (fun x => by simp) x
        (quotientRangeTwistedLinearOperatorEquiv hM hper hd
          (IsUnit.of_pow_eq_one hε two_ne_zero).ne_zero
          (ε • kerTwistedLinearOperatorToQuotientRange J hM hper ε
            ((kerTwistedLinearOperatorEquiv hM hper ε).symm x))) := by
  rw [map_smul, map_smul, smul_eq_mul,
    kerQuotientRangePairing_kerTwistedLinearOperatorToQuotientRange hM hper hd hε hskew,
    ← mul_assoc, ← sq, hε, one_mul]
  -- The integrand `‖J Ψ(s) x‖²` is continuous and positive, since `Ψ(s)` and `J` are injective.
  have hJΨ : Continuous fun s => J (dysonSeriesLeft M s x) :=
    J.continuous.comp ((continuous_dysonSeriesLeft hM).clm_apply continuous_const)
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ((hJΨ.inner hJΨ).intervalIntegrable _ _)
    (fun s _ => ?_) hd
  rw [real_inner_self_eq_norm_sq]
  refine pow_pos (norm_pos_iff.2 fun h => hx (Submodule.coe_eq_zero.1 ?_)) 2
  have h0 := (injective_iff_map_eq_zero J).1 hJ _ h
  have hinv := congrArg (fun T : X →L[ℝ] X => T (x : X)) (dysonSeries_neg_mul_dysonSeriesLeft hM s)
  simpa [h0] using hinv.symm

end Complete

variable [FiniteDimensional ℝ X]

/-- **Pointwise `J` and the endpoint map induce the orientation of `x ↦ [J x]`.** Let `J` be
injective and `M` a continuous `d`-periodic path, `d > 0`, skew for `⟪J ·, ·⟫`, and let `ε ^ 2 = 1`.
The map `w ↦ [ε • J w]` from the kernel of `L = d/dt - M` on maps twisted by `ε` to its cokernel,
read through the identifications of both with the kernel and the cokernel of `ε - Ψ(d)` by
evaluation at `0` and by the endpoint map, differs from the isomorphism `x ↦ [J x]` by an
automorphism of the kernel of `ε - Ψ(d)` of positive determinant. -/
theorem det_pos_symm_comp_kerTwistedLinearOperatorToQuotientRange
    (hM : Continuous M) (hper : Function.Periodic M d) (hd : 0 < d) (hε : ε ^ 2 = 1)
    (hJ : Function.Injective J) (hskew : ∀ r u w, ⟪J (M r u), w⟫ + ⟪J u, M r w⟫ = 0) :
    0 < ((kerEquivQuotientRangeOfInnerApplyEq (J := (J : X →ₗ[ℝ] X))
          (f := ε • 1 - ((dysonSeriesLeft M d : X →L[ℝ] X) : X →ₗ[ℝ] X)) hJ
          (inner_apply_dysonSeriesLeft_apply_dysonSeriesLeft_apply_of_skew hM hskew d)
          hε (fun x => by simp)).symm.toLinearMap ∘ₗ
        (quotientRangeTwistedLinearOperatorEquiv hM hper hd
          (IsUnit.of_pow_eq_one hε two_ne_zero).ne_zero).toLinearMap ∘ₗ
        (ε • kerTwistedLinearOperatorToQuotientRange J hM hper ε) ∘ₗ
        (kerTwistedLinearOperatorEquiv hM hper ε).symm.toLinearMap).det :=
  det_pos_kerEquivQuotientRangeOfInnerApplyEq_symm_comp _ _ _ _ fun _ hx =>
    kerQuotientRangePairing_smul_kerTwistedLinearOperatorToQuotientRange_pos hM hper hd hε hJ
      hskew hx

/-- **Pointwise `J` identifies the kernel of `L` with its cokernel.** For `J` injective and `M`
a continuous `d`-periodic path, `d > 0`, skew for `⟪J ·, ·⟫`, and `ε ^ 2 = 1`, the map
`w ↦ [J w]` from the twisted solutions of `w' = M w` to the cokernel of `L = d/dt - M` on maps
twisted by `ε` is bijective. -/
theorem bijective_kerTwistedLinearOperatorToQuotientRange (hM : Continuous M)
    (hper : Function.Periodic M d) (hd : 0 < d) (hε : ε ^ 2 = 1) (hJ : Function.Injective J)
    (hskew : ∀ r u w, ⟪J (M r u), w⟫ + ⟪J u, M r w⟫ = 0) :
    Function.Bijective (kerTwistedLinearOperatorToQuotientRange J hM hper ε) := by
  have hε₀ : ε ≠ 0 := (IsUnit.of_pow_eq_one hε two_ne_zero).ne_zero
  set κ := kerTwistedLinearOperatorEquiv hM hper ε
  set c := quotientRangeTwistedLinearOperatorEquiv hM hper hd hε₀
  set j := kerTwistedLinearOperatorToQuotientRange J hM hper ε
  -- `φ = c ∘ (ε • j) ∘ κ⁻¹` is positive for the pairing, hence bijective.
  have hφ : Function.Bijective (c.toLinearMap ∘ₗ (ε • j) ∘ₗ κ.symm.toLinearMap) :=
    bijective_of_forall_pos_kerQuotientRangePairing hJ _ hε _ fun _ hx =>
      kerQuotientRangePairing_smul_kerTwistedLinearOperatorToQuotientRange_pos hM hper hd hε hJ
        hskew hx
  -- Hence `j = ε • (c⁻¹ ∘ φ ∘ κ)` is bijective.
  have hj : (j : _ → _) = LinearEquiv.smulOfNeZero ℝ _ ε hε₀ ∘ c.symm ∘
      (c.toLinearMap ∘ₗ (ε • j) ∘ₗ κ.symm.toLinearMap) ∘ κ := by
    ext w
    simp [smul_smul, ← sq, hε]
  rw [hj]
  exact (LinearEquiv.smulOfNeZero ℝ _ ε hε₀).bijective.comp
    (c.symm.bijective.comp (hφ.comp κ.bijective))

end Kernel

end TauCeti

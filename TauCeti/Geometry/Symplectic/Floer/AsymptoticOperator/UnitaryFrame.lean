/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex.UnitaryFrame
public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Geometry.Symplectic.Duality

/-!
# The asymptotic operator in a unitary trivialization

Let `(V, ω)` be a finite-dimensional symplectic vector space whose inner product is the metric
`ω(·, J₀ ·)` of an `ω`-compatible complex structure `J₀`, for instance `ℂⁿ` with `J₀ = i`. Along a
Hamiltonian orbit, the asymptotic operator `A ζ = J_t (ζ' - S_t ζ)`
(`TauCeti.Floer.asymptoticOperator`) and the stationary cylinder operator `∂s + A`
(`TauCeti.Floer.stationaryCylinderOperator`) involve a loop of compatible complex structures
`J_t`. The spectral decomposition of `A` on Sobolev loops
(`TauCeti.CircleSobolev.exists_hilbertBasis_I_smul_loopOperator_eq_smul`), through which `∂s + A`
splits into the scalar operators `d/ds + λ`, is available for the constant structure `J₀ = i` of
a complex inner product space. This file reduces a general loop `J_t` to a constant one.

The unitary frames `Φ_t = √(-J_t J₀)` (`TauCeti.AlmostComplexStructure.unitaryFrame`) are
symplectic isomorphisms with `J_t Φ_t = Φ_t J₀`, isometric from `⟪·, ·⟫` to `ω(·, J_t ·)`, and
they depend on `t` as smoothly as `J_t` does. Writing loops as `ζ = Φ η` turns the linearized
equation `ζ' = S_t ζ` into `η' = T_t η` for the loop

`T_t = Φ_t⁻¹ (S_t Φ_t - Φ_t')`

(`TauCeti.Floer.trivializedLoop`), and the asymptotic operator of `(J, S)` into the one of
`(J₀, T)`, conjugated by `Φ`:

`A_{J,S} (Φ η) = Φ A_{J₀,T} η`  (`TauCeti.Floer.asymptoticOperator_unitaryFrame`),

and likewise `D_{J,S} (Φ ξ) = Φ D_{J₀,T} ξ` for the stationary cylinder operators
(`TauCeti.Floer.stationaryCylinderOperator_unitaryFrame`). The trivialized loop keeps the
properties the analysis at `J₀` uses: it is again infinitesimally symplectic
(`TauCeti.Floer.apply_trivializedLoop_add_apply_eq_zero`), because `Φ_t` is symplectic
for every `t`; it is continuous when `J` is `C¹` and `S` is continuous
(`TauCeti.Floer.continuous_trivializedLoop`); and it is periodic when `J` and `S` are
(`TauCeti.Floer.periodic_trivializedLoop`). Since `Φ_t` is invertible, kernel elements correspond
(`TauCeti.Floer.asymptoticOperator_unitaryFrame_eq_zero_iff`), so the orbit is nondegenerate for
`T` exactly when it is for `S`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2 (unitary trivializations along periodic orbits and the operator
  `J₀ ∂t + S`).
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. 45 (1992), 1303–1360.
-/

public section

noncomputable section

open Function
open scoped InnerProductSpace

namespace TauCeti

namespace Floer

open AlmostComplexStructure

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V} {J : ℝ → AlmostComplexStructure V}
  {S : ℝ → V →L[ℝ] V} {η : ℝ → V} {t : ℝ}

variable (J₀ J S) in
/-- The **trivialized loop** `T_t = Φ_t⁻¹ (S_t Φ_t - Φ_t')` of a loop `S_t` of linear maps, in the
unitary frames `Φ_t = √(-J_t J₀)` of a loop of complex structures `J_t`. Along a Hamiltonian
orbit, with `S_t` the linearized Hamiltonian vector field, the linearized equation `ζ' = S_t ζ`
becomes `η' = T_t η` for `ζ = Φ η`. -/
def trivializedLoop (t : ℝ) : V →L[ℝ] V :=
  Ring.inverse (J₀.unitaryFrame (J t)) *
    (S t * J₀.unitaryFrame (J t) - deriv (fun t ↦ J₀.unitaryFrame (J t)) t)

/-- The defining formula of the trivialized loop. -/
theorem trivializedLoop_def (t : ℝ) :
    trivializedLoop J₀ J S t = Ring.inverse (J₀.unitaryFrame (J t)) *
      (S t * J₀.unitaryFrame (J t) - deriv (fun t ↦ J₀.unitaryFrame (J t)) t) :=
  (rfl)

/-- For the constant loop `J_t = J₀` the frames are the identity, and the trivialized loop is `S`
itself. -/
@[simp]
theorem trivializedLoop_const : trivializedLoop J₀ (fun _ ↦ J₀) S = S := by
  funext t
  simp [trivializedLoop_def]

section Compatible

variable (hJ₀ : ∀ u v, ω u (J₀ v) = ⟪u, v⟫_ℝ)
include hJ₀

/-- The trivialized loop is characterized by `Φ_t T_t = S_t Φ_t - Φ_t'`. -/
theorem unitaryFrame_mul_trivializedLoop (hJ : ω.Compatible (J t)) :
    J₀.unitaryFrame (J t) * trivializedLoop J₀ J S t =
      S t * J₀.unitaryFrame (J t) - deriv (fun t ↦ J₀.unitaryFrame (J t)) t := by
  rw [trivializedLoop_def, ← mul_assoc, Ring.mul_inverse_cancel _ (isUnit_unitaryFrame hJ₀ hJ),
    one_mul]

/-- **The asymptotic operator in the unitary frame.** For a loop `η` differentiable at `t`,
`A_{J,S} (Φ η) = Φ A_{J₀,T} η` at `t`, where `Φ_t` is the unitary frame of `J_t` and `T` the
trivialized loop. -/
theorem asymptoticOperator_unitaryFrame (hJ : ω.Compatible (J t))
    (hΦ : DifferentiableAt ℝ (fun t ↦ J₀.unitaryFrame (J t)) t) (hη : DifferentiableAt ℝ η t) :
    asymptoticOperator J S (fun t ↦ J₀.unitaryFrame (J t) (η t)) t =
      J₀.unitaryFrame (J t) (asymptoticOperator (fun _ ↦ J₀) (trivializedLoop J₀ J S) η t) := by
  have hd := (hΦ.hasDerivAt.clm_apply hη.hasDerivAt).deriv
  have hS := congrArg (· (η t)) (unitaryFrame_mul_trivializedLoop (S := S) hJ₀ hJ)
  simp only [mul_apply_eq_comp, sub_apply] at hS
  rw [asymptoticOperator_def, asymptoticOperator_def, ← apply_unitaryFrame_apply hJ₀ hJ]
  congr 1
  rw [map_sub, hS, hd]
  abel

/-- **Kernel elements correspond.** At each `t`, `A_{J,S} (Φ η)` vanishes exactly when
`A_{J₀,T} η` does. -/
theorem asymptoticOperator_unitaryFrame_eq_zero_iff (hJ : ω.Compatible (J t))
    (hΦ : DifferentiableAt ℝ (fun t ↦ J₀.unitaryFrame (J t)) t) (hη : DifferentiableAt ℝ η t) :
    asymptoticOperator J S (fun t ↦ J₀.unitaryFrame (J t) (η t)) t = 0 ↔
      asymptoticOperator (fun _ ↦ J₀) (trivializedLoop J₀ J S) η t = 0 := by
  rw [asymptoticOperator_unitaryFrame hJ₀ hJ hΦ hη]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero]⟩
  have hinv := congrArg (· (asymptoticOperator (fun _ ↦ J₀) (trivializedLoop J₀ J S) η t))
    (Ring.inverse_mul_cancel _ (isUnit_unitaryFrame hJ₀ hJ))
  simpa only [mul_apply_eq_comp, h, map_zero, one_apply_eq_self, eq_comm] using hinv

/-- **The stationary cylinder operator in the unitary frame.** For a map `ξ` of the cylinder
differentiable at `z`, `D_{J,S} (Φ ξ) = Φ D_{J₀,T} ξ` at `z`, where `Φ` acts at the angular
coordinate `t = z.2`. -/
theorem stationaryCylinderOperator_unitaryFrame {ξ : ℝ × ℝ → V} {z : ℝ × ℝ}
    (hJ : ω.Compatible (J z.2)) (hΦ : DifferentiableAt ℝ (fun t ↦ J₀.unitaryFrame (J t)) z.2)
    (hξ : DifferentiableAt ℝ ξ z) :
    stationaryCylinderOperator J S (fun w ↦ J₀.unitaryFrame (J w.2) (ξ w)) z =
      J₀.unitaryFrame (J z.2)
        (stationaryCylinderOperator (fun _ ↦ J₀) (trivializedLoop J₀ J S) ξ z) := by
  obtain ⟨s, t⟩ := z
  have hΦz : DifferentiableAt ℝ (fun w : ℝ × ℝ ↦ J₀.unitaryFrame (J w.2)) (s, t) :=
    hΦ.comp (s, t) differentiableAt_snd
  have hslice : DifferentiableAt ℝ (fun t ↦ ξ (s, t)) t :=
    hξ.comp t ((differentiableAt_const s).prodMk differentiableAt_id)
  -- The `s`-derivative does not see the frame, which depends only on `t`.
  have hds : fderiv ℝ (fun w ↦ J₀.unitaryFrame (J w.2) (ξ w)) (s, t) stdComplexLineReal =
      J₀.unitaryFrame (J t) (fderiv ℝ ξ (s, t) stdComplexLineReal) := by
    have hΦd : HasFDerivAt (fun w : ℝ × ℝ ↦ J₀.unitaryFrame (J w.2))
        ((fderiv ℝ (fun t ↦ J₀.unitaryFrame (J t)) t).comp (ContinuousLinearMap.snd ℝ ℝ ℝ))
        (s, t) :=
      hΦ.hasFDerivAt.comp (s, t) hasFDerivAt_snd
    rw [fderiv_clm_apply hΦz hξ, hΦd.fderiv]
    simp [stdComplexLineReal_snd]
  rw [stationaryCylinderOperator_eq_add_asymptoticOperator (hΦz.clm_apply hξ),
    stationaryCylinderOperator_eq_add_asymptoticOperator hξ, map_add, hds]
  exact congrArg _ (asymptoticOperator_unitaryFrame hJ₀ hJ hΦ hslice)

/-- **The trivialized loop is infinitesimally symplectic** when `S_t` is: the unitary frames are
symplectic for every `t`, so their derivative is infinitesimally symplectic relative to them. -/
theorem apply_trivializedLoop_add_apply_eq_zero (hJ : ∀ t, ω.Compatible (J t))
    (hΦ : DifferentiableAt ℝ (fun t ↦ J₀.unitaryFrame (J t)) t)
    (hS : ∀ u v, ω (S t u) v + ω u (S t v) = 0) (u v : V) :
    ω (trivializedLoop J₀ J S t u) v + ω u (trivializedLoop J₀ J S t v) = 0 := by
  set Φ := fun t ↦ J₀.unitaryFrame (J t)
  set Φ' := deriv Φ t
  -- `t ↦ ω(Φ_t u, Φ_t v)` is constant, so its derivative `ω(Φ' u, Φ v) + ω(Φ u, Φ' v)` vanishes.
  have hu : HasDerivAt (fun t ↦ Φ t u) (Φ' u) t := by
    simpa using hΦ.hasDerivAt.clm_apply (hasDerivAt_const t u)
  have hv : HasDerivAt (fun t ↦ Φ t v) (Φ' v) t := by
    simpa using hΦ.hasDerivAt.clm_apply (hasDerivAt_const t v)
  have hconst : (fun t ↦ ω (Φ t u) (Φ t v)) = fun _ ↦ ω u v :=
    funext fun t ↦ apply_unitaryFrame_unitaryFrame hJ₀ (hJ t) u v
  have hd := (ω.hasDerivAt_apply_comp hu hv).unique (hconst ▸ hasDerivAt_const t (ω u v))
  -- Moving `Φ_t` across `ω` turns the claim into the infinitesimal symplecticity of `S_t`.
  have hT (w : V) : Φ t (trivializedLoop J₀ J S t w) = S t (Φ t w) - Φ' w := by
    simpa using congrArg (· w) (unitaryFrame_mul_trivializedLoop (S := S) hJ₀ (hJ t))
  rw [← apply_unitaryFrame_unitaryFrame hJ₀ (hJ t) (trivializedLoop J₀ J S t u),
    ← apply_unitaryFrame_unitaryFrame hJ₀ (hJ t) u, hT, hT]
  simp only [map_sub, LinearMap.sub_apply]
  linarith [hS (Φ t u) (Φ t v)]

end Compatible

/-- **The trivialized loop is continuous** when `J` is a `C¹` loop of compatible structures and
`S` is continuous. -/
theorem continuous_trivializedLoop (hJ₀ : ∀ u v, ω u (J₀ v) = ⟪u, v⟫_ℝ)
    (hJ : ∀ t, ω.Compatible (J t))
    (hJc : ContDiff ℝ 1 fun t ↦ LinearMap.toContinuousLinearMap (J t).toLinearMap)
    (hS : Continuous S) : Continuous (trivializedLoop J₀ J S) := by
  have hΦ := hJc.unitaryFrame hJ₀ hJ
  have hinv : Continuous fun t ↦ Ring.inverse (J₀.unitaryFrame (J t)) :=
    continuous_iff_continuousAt.2 fun t ↦ by
      obtain ⟨e, he⟩ := isUnit_unitaryFrame hJ₀ (hJ t)
      exact ContinuousAt.comp (g := Ring.inverse) (he ▸ NormedRing.inverse_continuousAt e)
        hΦ.continuous.continuousAt
  rw [show trivializedLoop J₀ J S = _ from funext trivializedLoop_def]
  exact hinv.mul ((hS.mul hΦ.continuous).sub (hΦ.continuous_deriv le_rfl))

/-- **The trivialized loop is periodic** when `J` and `S` are. -/
theorem periodic_trivializedLoop {c : ℝ} (hJ : Periodic J c) (hS : Periodic S c) :
    Periodic (trivializedLoop J₀ J S) c := fun t ↦ by
  have hΦ : Periodic (fun t ↦ J₀.unitaryFrame (J t)) c := fun t ↦ by simp only [hJ t]
  rw [trivializedLoop_def, trivializedLoop_def, hJ t, hS t, hΦ.deriv t]

end Floer

end TauCeti

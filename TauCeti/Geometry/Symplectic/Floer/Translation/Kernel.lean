/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.UniqueContinuation
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Infinitesimal translations of Floer solutions and the zeros of `∂ₛu`

Let `u : ℝ × ℝ → V` solve the coordinate Floer equation
`∂ₛu - X_{K_s}(u) + J(z, u)(∂ₜu - X_{K_t}(u)) = 0` (`TauCeti.SymplecticForm.floerOperator`) on an
open set `Ω`, and suppose that at each point `z` of `Ω` the data `J`, `K_s` and `K_t` are
invariant under the small translations `z ↦ z + c v` in a direction `v`. Then for small `c` the
translate `y ↦ u(y + c v)` solves the same equation at `z`, and differentiating this family at
`c = 0` shows that the infinitesimal translation `∂ᵥu = du(v)` lies in the kernel of the
linearized operator:

`D_u (∂ᵥu) = 0`

(`TauCeti.SymplecticForm.floerLinearization_fderiv_apply_eq_zero`). This is read off the universal
variation formula `TauCeti.SymplecticForm.fderiv_floerOperator_apply`, in which the variations of
`J` and `K` vanish for this family.

The main case is the Floer equation `∂ₛu + J_t(u)(∂ₜu - X_{H_t}(u)) = 0` for a time-dependent
Hamiltonian `H` and almost complex structures `J_t`, that is `K_s = 0` and `K_t(s, t) = H_t`,
whose data do not depend on `s`, with `v = (1, 0)`: the derivative `∂ₛu` of a Floer trajectory
solves the linearized equation along `u`.

Unique continuation for the linearized operator
(`TauCeti.SymplecticForm.setOf_ne_zero_mem_codiscreteWithin_of_floerLinearization_eq_zero`)
then shows that on a connected open set `Ω` the zeros of `∂ᵥu` are isolated unless `∂ᵥu`
vanishes identically on `Ω`
(`TauCeti.SymplecticForm.setOf_fderiv_apply_ne_zero_mem_codiscreteWithin_of_floerOperator_eq_zero`),
so that a compact subset of `Ω` contains only finitely many of them
(`TauCeti.SymplecticForm.finite_inter_setOf_fderiv_apply_eq_zero_of_floerOperator_eq_zero`). For
Floer trajectories `∂ₛu = 0` is one of the conditions excluded from the regular points of
Floer, Hofer and Salamon, whose density is the basis of the transversality argument for the
moduli spaces of Floer trajectories.

## Main results

* `TauCeti.SymplecticForm.floerLinearization_fderiv_apply_eq_zero`: the infinitesimal translation
  `du(v)` of a solution solves the linearized equation.
* `TauCeti.SymplecticForm.setOf_fderiv_apply_ne_zero_mem_codiscreteWithin_of_floerOperator_eq_zero`:
  the zeros of `du(v)` are isolated in a connected domain unless `du(v)` vanishes identically.
* `TauCeti.SymplecticForm.finite_inter_setOf_fderiv_apply_eq_zero_of_floerOperator_eq_zero`: a
  compact subset of the domain meets them in a finite set.

## References

* A. Floer, H. Hofer and D. Salamon, *Transversality in elliptic Morse theory for the symplectic
  action*, Duke Math. J. **80** (1995), 251–292 (the regular points of a Floer trajectory, and the
  zeros of `∂ₛu` through unique continuation for the linearized equation it solves).
-/

public section

open Filter Function Set Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ}
  {u : ℝ × ℝ → V} {v : ℝ × ℝ}

/-- **Infinitesimal translations solve the linearized Floer equation.** Let `u` be `C²` at `z`
and solve the Floer equation `∂ₛu - X_{K_s}(u) + J(u)(∂ₜu - X_{K_t}(u)) = 0` near `z`, where `J`
and the Hamiltonians `K_s`, `K_t` are invariant under the translations of `z` by small multiples
of `v`, `J z` is differentiable and `K_s z`, `K_t z` are `C²` at `u z`. Then the derivative
`du(v)` of `u` in the direction `v` solves the linearized equation `D_u (du(v)) = 0` at `z`. -/
theorem floerLinearization_fderiv_apply_eq_zero {z : ℝ × ℝ}
    (hJv : ∀ᶠ c : ℝ in 𝓝 0, J (z + c • v) = J z)
    (hKsv : ∀ᶠ c : ℝ in 𝓝 0, Ks (z + c • v) = Ks z)
    (hKtv : ∀ᶠ c : ℝ in 𝓝 0, Kt (z + c • v) = Kt z) (hJ : DifferentiableAt ℝ (J z) (u z))
    (hKs : ContDiffAt ℝ 2 (Ks z) (u z)) (hKt : ContDiffAt ℝ 2 (Kt z) (u z))
    (hu : ContDiffAt ℝ 2 u z) (hF : ∀ᶠ y in 𝓝 z, ω.floerOperator J Ks Kt u y = 0) :
    ω.floerLinearization J Ks Kt u (fun y ↦ fderiv ℝ u y v) z = 0 := by
  -- The translates `u_c(y) = u(y + c v)` form a `C²` family with fixed data `J` and `K`.
  have hfam :
      ContDiffAt ℝ 2 (uncurry fun (c : ℝ) (y : ℝ × ℝ) ↦ u (y + c • v)) ((0 : ℝ), z) := by
    have hlin : ContDiffAt ℝ 2 (fun p : ℝ × (ℝ × ℝ) ↦ p.2 + p.1 • v) ((0 : ℝ), z) :=
      (contDiff_snd.add (contDiff_fst.smul contDiff_const)).contDiffAt
    have hu' : ContDiffAt ℝ 2 u (z + (0 : ℝ) • v) := by simpa using hu
    exact hu'.comp ((0 : ℝ), z) hlin
  have hu₀ : u (z + (0 : ℝ) • v) = u z := by simp
  have hJ' : DifferentiableAt ℝ (J z) (u (z + (0 : ℝ) • v)) := hu₀ ▸ hJ
  have hKs' : ContDiffAt ℝ 2 (Ks z) (u (z + (0 : ℝ) • v)) := hu₀ ▸ hKs
  have hKt' : ContDiffAt ℝ 2 (Kt z) (u (z + (0 : ℝ) • v)) := hu₀ ▸ hKt
  have h := fderiv_floerOperator_apply ω (fun _ : ℝ ↦ J) (fun _ ↦ Ks) (fun _ ↦ Kt)
    (fun c y ↦ u (y + c • v)) 0 z hfam (hJ'.comp ((0 : ℝ), _) differentiableAt_snd)
    (hKs'.comp ((0 : ℝ), _) contDiffAt_snd) (hKt'.comp ((0 : ℝ), _) contDiffAt_snd) 1
  -- The Floer operator of `u_c` at `z` vanishes for `c` near `0`, so its derivative vanishes.
  have hzero : (fun c : ℝ ↦ ω.floerOperator J Ks Kt (fun y ↦ u (y + c • v)) z) =ᶠ[𝓝 0] 0 := by
    have ht : Tendsto (fun c : ℝ ↦ z + c • v) (𝓝 0) (𝓝 z) := by
      simpa using ((continuous_id.smul continuous_const).const_add z).tendsto (0 : ℝ)
    filter_upwards [ht.eventually hF, hJv, hKsv, hKtv] with c hc hJc hKsc hKtc
    rw [Pi.zero_apply, ← hc, ← ω.floerOperator_comp_add_right]
    simp only [floerOperator_def, hJc, hKsc, hKtc]
  -- The direction field of the family is `du(v)` near `z`: at each point it is the derivative
  -- of `c ↦ u(y + c v)` at `0`, which is by definition the line derivative `lineDeriv ℝ u y v`.
  have hdir : (fun y ↦ fderiv ℝ (fun c : ℝ ↦ u (y + c • v)) 0 1) =ᶠ[𝓝 z]
      fun y ↦ fderiv ℝ u y v := by
    filter_upwards [hu.eventually (by simp)] with y hy
    rw [fderiv_apply_one_eq_deriv]
    exact (hy.differentiableAt (by norm_num)).lineDeriv_eq_fderiv
  -- In the universal variation formula the variations of `J` and `K` vanish.
  rw [hzero.fderiv_eq] at h
  simp only [fderiv_zero, Pi.zero_apply, zero_apply, zero_smul, add_zero, fderiv_fun_const,
    hamiltonianVectorField_const, sub_zero, map_zero] at h
  rw [← ω.floerLinearization_congr_of_eventuallyEq J Ks Kt u hdir]
  exact h.symm

/-- Under the hypotheses of the unique continuation theorems for the linearized Floer operator,
with `u` of class `C²` on `Ω`, the infinitesimal translation `du(v)` solves the linearized
equation on `Ω` and is of class `C¹` there. -/
private theorem floerLinearization_fderiv_apply_eq_zero_on {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (hJv : ∀ z ∈ Ω, ∀ᶠ c : ℝ in 𝓝 0, J (z + c • v) = J z)
    (hKsv : ∀ z ∈ Ω, ∀ᶠ c : ℝ in 𝓝 0, Ks (z + c • v) = Ks z)
    (hKtv : ∀ z ∈ Ω, ∀ᶠ c : ℝ in 𝓝 0, Kt (z + c • v) = Kt z)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiffOn ℝ 2 u Ω)
    (hF : ∀ z ∈ Ω, ω.floerOperator J Ks Kt u z = 0) :
    ContDiffOn ℝ 1 (fun z ↦ fderiv ℝ u z v) Ω ∧
      ∀ z ∈ Ω, ω.floerLinearization J Ks Kt u (fun y ↦ fderiv ℝ u y v) z = 0 := by
  refine ⟨(hu.fderiv_of_isOpen hΩ (by norm_num)).clm_apply contDiffOn_const, fun z hz ↦ ?_⟩
  -- The slices of the data at the domain point `z` inherit the regularity of the data.
  have hslice : ContDiffAt ℝ 2 (fun x : V ↦ (z, x)) (u z) :=
    contDiffAt_const.prodMk contDiffAt_id
  exact floerLinearization_fderiv_apply_eq_zero (hJv z hz) (hKsv z hz) (hKtv z hz)
    (((hJ z hz).comp (u z) (hslice.of_le (by norm_num))).differentiableAt one_ne_zero)
    ((hKs z hz).comp (u z) hslice) ((hKt z hz).comp (u z) hslice)
    (hu.contDiffAt (hΩ.mem_nhds hz))
    (eventually_of_mem (hΩ.mem_nhds hz) hF)

/-- **Isolated zeros of the infinitesimal translations of a Floer solution.** Let `u` be `C²` on
a connected open set `Ω ⊆ ℝ × ℝ` and solve the Floer equation
`∂ₛu - X_{K_s}(u) + J(u)(∂ₜu - X_{K_t}(u)) = 0` there, where `J` is `C¹` and the Hamiltonians
`K_s`, `K_t` are `C²` near the graph of `u`, `J(z, u z)² = -1` on `Ω`, and the data are invariant
under the translations of each point of `Ω` by small multiples of `v`. If `du(v)` does not vanish
identically on `Ω`, its zeros form a discrete subset of `Ω`. -/
theorem setOf_fderiv_apply_ne_zero_mem_codiscreteWithin_of_floerOperator_eq_zero
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hJv : ∀ z ∈ Ω, ∀ᶠ c : ℝ in 𝓝 0, J (z + c • v) = J z)
    (hKsv : ∀ z ∈ Ω, ∀ᶠ c : ℝ in 𝓝 0, Ks (z + c • v) = Ks z)
    (hKtv : ∀ z ∈ Ω, ∀ᶠ c : ℝ in 𝓝 0, Kt (z + c • v) = Kt z)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiffOn ℝ 2 u Ω)
    (hF : ∀ z ∈ Ω, ω.floerOperator J Ks Kt u z = 0) (hne : ∃ z ∈ Ω, fderiv ℝ u z v ≠ 0) :
    {z | fderiv ℝ u z v ≠ 0} ∈ codiscreteWithin Ω := by
  obtain ⟨hξ, hD⟩ :=
    floerLinearization_fderiv_apply_eq_zero_on hΩ hJv hKsv hKtv hJ hKs hKt hu hF
  exact setOf_ne_zero_mem_codiscreteWithin_of_floerLinearization_eq_zero hΩ hΩc hJ hJJ hKs hKt
    (hu.of_le (by norm_num)) hξ hD hne

/-- **Finitely many zeros of `du(v)` on a compact set.** Under the hypotheses of
`TauCeti.SymplecticForm.setOf_fderiv_apply_ne_zero_mem_codiscreteWithin_of_floerOperator_eq_zero`,
a compact subset of `Ω` contains only finitely many zeros of `du(v)`. -/
theorem finite_inter_setOf_fderiv_apply_eq_zero_of_floerOperator_eq_zero
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hJv : ∀ z ∈ Ω, ∀ᶠ c : ℝ in 𝓝 0, J (z + c • v) = J z)
    (hKsv : ∀ z ∈ Ω, ∀ᶠ c : ℝ in 𝓝 0, Ks (z + c • v) = Ks z)
    (hKtv : ∀ z ∈ Ω, ∀ᶠ c : ℝ in 𝓝 0, Kt (z + c • v) = Kt z)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiffOn ℝ 2 u Ω)
    (hF : ∀ z ∈ Ω, ω.floerOperator J Ks Kt u z = 0) (hne : ∃ z ∈ Ω, fderiv ℝ u z v ≠ 0)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    (K ∩ {z | fderiv ℝ u z v = 0}).Finite := by
  have h := hK.finite_sdiff_of_mem_codiscreteWithin (codiscreteWithin_mono hKΩ
    (setOf_fderiv_apply_ne_zero_mem_codiscreteWithin_of_floerOperator_eq_zero hΩ hΩc hJv hKsv
      hKtv hJ hJJ hKs hKt hu hF hne))
  simpa [sdiff_eq, compl_ofPred] using h

end TauCeti.SymplecticForm

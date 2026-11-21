/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Normalization.Continuation

/-!
# Normalizing the end Hamiltonians of the pair of pants

A Hamiltonian is determined by its Hamiltonian vector field only up to a function of time:
`H_q(t, x)` and `H_q(t, x) + c_q(t)` generate the same flow, have the same one-periodic orbits,
and give the same Floer equation. Their actions differ by the time average of `c_q`
(`TauCeti.SymplecticForm.hamiltonianAction_add_const`, and `TauCeti.cappedLoopAction_add_const`
for capped loops in a manifold). This file shows how the energy identity of the pair of pants

`E(u) = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt - ∫_S R_K(u)`

absorbs such a change of normalization on its three ends, for a manifold target `M` with a
two-form `ω`, such as a closed symplectic manifold, and for a symplectic vector space target.

The pair-of-pants perturbation (`TauCeti.Floer.pairOfPantsPerturbation`) is additive in the end
Hamiltonians, so normalizing by `c` adds to it the perturbation `k` of the target-independent
Hamiltonians `c_q`, which has no Hamiltonian vector field
(`TauCeti.Floer.pairOfPantsPerturbation_add_const`). Consequently:

* the perturbed derivative `du - X_K`, hence the Floer equation, and the Floer energy density
  are unchanged
  (`TauCeti.SmoothTwoForm.perturbedMFDeriv_pairOfPantsPerturbation_add_const`,
  `TauCeti.SmoothTwoForm.floerEnergyDensity_pairOfPantsPerturbation_add_const`);
* the curvature changes by the curvature of `k`, which does not depend on the target point
  (`TauCeti.SmoothTwoForm.hamiltonianCurvature_pairOfPantsPerturbation_add_const`);
* the integral of the curvature of `k` over the pair of pants is exactly the sum
  `∑ q, ±∫₀¹ c_q`, with the sign `+` on the input ends `0`, `1` and `-` on the output end `∞`
  (`TauCeti.SmoothTwoForm.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_const`).

So along every map whose curvature for `H_q` is integrable on `S`, the integrated curvature
changes by `∑ q, ±∫₀¹ c_q`
(`TauCeti.SmoothTwoForm.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_add_const`),
which is exactly the change `∑ q, ±∫₀¹ c_q` of the Hamiltonian terms at the asymptotic orbits.
The two changes cancel in the energy identity
`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation`, as
they must, since the energy itself is unchanged.

The pair-of-pants perturbation of `H` is the perturbation with continuation necks from `H` to
itself, at any neck positions (`TauCeti.Floer.pairOfPantsContinuationPerturbation_self`). So every
statement here is the special case `G = H`, `c = d` of the corresponding statement for the pair of
pants with continuation necks, in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Normalization.Continuation`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the energy identity.
-/

public section

open Set Function MeasureTheory TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture
open scoped Manifold

namespace TauCeti

/-! ### Symplectic vector spaces: the Floer equation and the curvature of a normalization -/

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {c : Puncture → ℝ → ℝ}

/-- **Normalizing the end Hamiltonians does not change the Floer equation.** The perturbed
derivative `du - X_K` of any map is the same for the end Hamiltonians `H_q` and
`H_q + c_q`. -/
@[simp]
theorem perturbedFDeriv_pairOfPantsPerturbation_add_const (ω : SymplecticForm V)
    (H : Puncture → ℝ → V → ℝ) (c : Puncture → ℝ → ℝ) (u : ℝ × ℝ → V) :
    ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u := by
  simpa only [pairOfPantsContinuationPerturbation_self] using
    ω.perturbedFDeriv_pairOfPantsContinuationPerturbation_add_const H H c c 0 u

/-- **Normalizing the end Hamiltonians does not change the energy density.** -/
@[simp]
theorem floerEnergyDensity_pairOfPantsPerturbation_add_const (ω : SymplecticForm V)
    (H : Puncture → ℝ → V → ℝ) (c : Puncture → ℝ → ℝ) (u : ℝ × ℝ → V) :
    ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u := by
  simpa only [pairOfPantsContinuationPerturbation_self] using
    ω.floerEnergyDensity_pairOfPantsContinuationPerturbation_add_const H H c c 0 u

/-- The curvature of the perturbation of target-independent Hamiltonians does not depend on the
target point. -/
theorem hamiltonianCurvature_pairOfPantsPerturbation_const_target (ω : SymplecticForm V)
    (c : Puncture → ℝ → ℝ) (z : ℝ × ℝ) (x y : V) :
    ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z y := by
  simpa only [pairOfPantsContinuationPerturbation_self, hamiltonianCurvature_constSmooth] using
    ω.constSmooth.hamiltonianCurvature_pairOfPantsContinuationPerturbation_const_target c c 0 z x y

/-- **The integrated curvature of a normalization.** For period-one `C¹` functions `c_q` of time,
the curvature of the pair-of-pants perturbation of the target-independent Hamiltonians `c_q`
integrates over the pair of pants to `∑ q, ±∫₀¹ c_q`, with the sign `+` on the input ends and `-`
on the output end, along any map `u`. -/
theorem setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_const (ω : SymplecticForm V)
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) (u : ℝ × ℝ → V) :
    ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, c q t := by
  have h := ω.constSmooth.setIntegral_hamiltonianCurvature_pairOfPantsContinuationPerturbation_const
    hc hc hcs hcs 0 u
  simp only [pairOfPantsContinuationPerturbation_self, hamiltonianCurvature_constSmooth,
    thricePuncturedSphereReal_def] at h
  exact h

end SymplecticForm

/-! ### Manifold targets -/

namespace SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {H : Puncture → ℝ → M → ℝ} {c : Puncture → ℝ → ℝ}

/-- **Normalizing the end Hamiltonians does not change the Floer equation, for a manifold
target.** The perturbed derivative `du - X_K` of any map into `M` is the same for the end
Hamiltonians `H_q` and `H_q + c_q`. -/
@[simp]
theorem perturbedMFDeriv_pairOfPantsPerturbation_add_const (ω : SmoothTwoForm I M)
    (H : Puncture → ℝ → M → ℝ) (c : Puncture → ℝ → ℝ) (u : ℝ × ℝ → M) :
    ω.perturbedMFDeriv
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.perturbedMFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u := by
  simpa only [pairOfPantsContinuationPerturbation_self] using
    ω.perturbedMFDeriv_pairOfPantsContinuationPerturbation_add_const H H c c 0 u

/-- **Normalizing the end Hamiltonians does not change the energy density, for a manifold
target.** -/
@[simp]
theorem floerEnergyDensity_pairOfPantsPerturbation_add_const (ω : SmoothTwoForm I M)
    (H : Puncture → ℝ → M → ℝ) (c : Puncture → ℝ → ℝ) (u : ℝ × ℝ → M) :
    ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u := by
  simpa only [pairOfPantsContinuationPerturbation_self] using
    ω.floerEnergyDensity_pairOfPantsContinuationPerturbation_add_const H H c c 0 u

/-- The curvature of the perturbation of target-independent Hamiltonians does not depend on the
target point, for a manifold target. -/
theorem hamiltonianCurvature_pairOfPantsPerturbation_const_target (ω : SmoothTwoForm I M)
    (c : Puncture → ℝ → ℝ) (z : ℝ × ℝ) (x y : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z y := by
  simpa only [pairOfPantsContinuationPerturbation_self] using
    ω.hamiltonianCurvature_pairOfPantsContinuationPerturbation_const_target c c 0 z x y

/-- **The curvature of the normalized perturbation, for a manifold target.** At every point of the
pair of pants, the curvature of the perturbation of the end Hamiltonians `H_q + c_q` is the
curvature for `H_q` plus the curvature of the perturbation of the target-independent Hamiltonians
`c_q`. -/
theorem hamiltonianCurvature_pairOfPantsPerturbation_add_const (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z x +
        ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
            (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
            (Complex.equivRealProdCLM.symm z) x Complex.I) z x := by
  simpa only [pairOfPantsContinuationPerturbation_self] using
    ω.hamiltonianCurvature_pairOfPantsContinuationPerturbation_add_const (L := 0) hH hH hHs hHs hc
      hc hcs hcs hz x

/-- **The integrated curvature of a normalization, for a manifold target.** For period-one `C¹`
functions `c_q` of time, the curvature of the pair-of-pants perturbation of the target-independent
Hamiltonians `c_q` on `M` integrates over the pair of pants to `∑ q, ±∫₀¹ c_q`, with the sign `+`
on the input ends and `-` on the output end, along any map `u`. -/
theorem setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_const (ω : SmoothTwoForm I M)
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) (u : ℝ × ℝ → M) :
    ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, c q t := by
  simpa only [pairOfPantsContinuationPerturbation_self] using
    ω.setIntegral_hamiltonianCurvature_pairOfPantsContinuationPerturbation_const hc hc hcs hcs 0 u

/-- **Normalizing the end Hamiltonians shifts the integrated curvature, for a manifold target.**
Along a map whose curvature for `H_q` is integrable on the pair of pants, the integrated curvature
of the perturbation of the end Hamiltonians `H_q + c_q` is the integrated curvature for `H_q` plus
`∑ q, ±∫₀¹ c_q`, with the sign `+` on the input ends and `-` on the output end. This is also the
change of the Hamiltonian terms `∑ q, ±∫₀¹ H_q(t, x_q(t)) dt` of the energy identity
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation`, so the two
changes cancel and the energy identity for `H_q + c_q` is the one for `H_q`. -/
theorem setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_add_const (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) {u : ℝ × ℝ → M}
    (hu : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)) thricePuncturedSphereReal) :
    ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      (∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, c q t := by
  simpa only [pairOfPantsContinuationPerturbation_self] using
    ω.setIntegral_hamiltonianCurvature_pairOfPantsContinuationPerturbation_add_const (L := 0) hH hH
      hHs hHs hc hc hcs hcs (by simpa only [pairOfPantsContinuationPerturbation_self] using hu)

end SmoothTwoForm

/-! ### Symplectic vector spaces: the curvature of the normalized perturbation -/

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {c : Puncture → ℝ → ℝ}

/-- **The curvature of the normalized perturbation.** At every point of the pair of pants, the
curvature of the perturbation of the end Hamiltonians `H_q + c_q` is the curvature for `H_q` plus
the curvature of the perturbation of the target-independent Hamiltonians `c_q`. This is the
vector-space case of `SmoothTwoForm.hamiltonianCurvature_pairOfPantsPerturbation_add_const`. -/
theorem hamiltonianCurvature_pairOfPantsPerturbation_add_const (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : V) :
    ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z x +
        ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
            (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
            (Complex.equivRealProdCLM.symm z) x Complex.I) z x := by
  have h := ω.constSmooth.hamiltonianCurvature_pairOfPantsPerturbation_add_const hH
    (fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHs q).contMDiff) hc hcs hz x
  simp only [hamiltonianCurvature_constSmooth] at h
  exact h

/-- **Normalizing the end Hamiltonians shifts the integrated curvature.** Along a map whose
curvature for `H_q` is integrable on the pair of pants, the integrated curvature of the
perturbation of the end Hamiltonians `H_q + c_q` is the integrated curvature for `H_q` plus
`∑ q, ±∫₀¹ c_q`, with the sign `+` on the input ends and `-` on the output end. This is also the
change of the Hamiltonian terms `∑ q, ±∫₀¹ H_q(t, x_q(t)) dt` of the energy identity
`SymplecticForm.integral_floerEnergyDensity_pairOfPantsPerturbation`, so the two changes cancel
and the energy identity for `H_q + c_q` is the one for `H_q`. This is the vector-space case of
`SmoothTwoForm.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_add_const`. -/
theorem setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_add_const (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) {u : ℝ × ℝ → V}
    (hu : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}) :
    ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      (∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, c q t := by
  rw [← thricePuncturedSphereReal_def] at hu ⊢
  have h := ω.constSmooth.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_add_const hH
    (fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHs q).contMDiff) hc hcs
    (by simpa only [hamiltonianCurvature_constSmooth] using hu)
  simp only [hamiltonianCurvature_constSmooth] at h
  exact h

end SymplecticForm

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.MeasureTheory.Integral.Kernel.Potential

/-!
# Green kernels of the Dirichlet Laplacian by duality

Let `Ω ⊆ ℝⁿ` be a bounded open set and let `G` be a symmetric kernel on `Ω`. Suppose that `G`
inverts the Dirichlet Laplacian on smooth data: for every smooth `ψ` with compact support in `Ω`,
the weak solution `w ∈ H¹₀(Ω)` of `-Δw = ψ` in `Ω`, `w = 0` on `∂Ω`, is the Green potential
`w(x) = ∫ G(x, y) ψ(y) dy`. Then `G` inverts it on every `f ∈ L²(Ω)` for which
`(x, y) ↦ G(x, y) f(y)` is integrable on `Ω × Ω`: the weak solution of `-Δu = f` is

`u(x) = ∫_Ω G(x, y) f(y) dy` for almost every `x ∈ Ω`

(`TauCeti.PDE.IsWeakSolutionDirichlet.value_ae_eq_setIntegral_mul_of_forall_contDiff`).

The argument is by duality. Let `ψ` be a test function on `Ω` and `w` the weak solution with datum
`ψ`, which is the Green potential of `ψ`. Testing the equation of `w` with `u`, that of `u` with
`w`, and using the symmetry of the Dirichlet form,

`∫_Ω ψ u = a(w, u) = a(u, w) = ∫_Ω f w = ∫_Ω f(x) ∫_Ω G(x, y) ψ(y) dy dx`,

and by Fubini's theorem and the symmetry of `G` the last integral is
`∫_Ω ψ(y) ∫_Ω G(y, x) f(x) dx dy`. As `ψ` ranges over the test functions on `Ω`, `u` agrees almost
everywhere with the Green potential of `f`.

This reduces Green's representation formula on a domain to the case of smooth data, where the
Green potential is a classical solution; it is applied to the unit ball in every dimension
(`TauCeti.Analysis.PDE.GreenFunction.Representation.Ball` and
`TauCeti.Analysis.PDE.GreenFunction.Representation.Disk`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 2.2.4 (Green's function) and
  Section 6.2 (weak solutions).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Sections 2.4 and 8.2.
-/

public section

namespace TauCeti

namespace PDE

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped ContDiff

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}

/-- **The duality identity.** If `u` is the weak solution of `-Δu = f` on `Ω` and the weak
solution of `-Δw = ψ` for a test function `ψ` is the Green potential of `ψ`, then
`∫_Ω ψ u = ∫_Ω f(x) ∫ G(x, y) ψ(y) dy dx`: test the equation of `u` with `w` and that of `w`
with `u`. -/
private theorem IsWeakSolutionDirichlet.setIntegral_mul_value_eq
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball z R)
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {f : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))}
    {u : W1p0 volume Omega 2} (hu : IsWeakSolutionDirichlet (fun _ => 1) 0 0 f u)
    {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hψ : MemLp ψ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hrep : ∀ w : W1p0 volume Omega 2, IsWeakSolutionDirichlet (fun _ => 1) 0 0 (hψ.toLp ψ) w →
      W1p.value (w : W1p volume Omega 2)
        =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))]
          fun x => ∫ y, G x y * ψ y) :
    ∫ x in Omega, ψ x * W1p.value (u : W1p volume Omega 2) x =
      ∫ x in Omega, f x * ∫ y, G x y * ψ y := by
  obtain ⟨w, hw, -⟩ := existsUnique_isWeakSolutionDirichlet_laplacian_of_subset_ball hΩ
    (hψ.toLp ψ)
  have h1 := (isWeakSolutionDirichlet_iff _ _).1 hw u
  have h2 := (isWeakSolutionDirichlet_iff _ _).1 hu w
  calc ∫ x in Omega, ψ x * W1p.value (u : W1p volume Omega 2) x
      = ∫ x in Omega, hψ.toLp ψ x * W1p.value (u : W1p volume Omega 2) x := by
        refine integral_congr_ae ?_
        filter_upwards [hψ.coeFn_toLp] with x hx
        rw [hx]
    _ = ∫ x in Omega, f x * W1p.value (w : W1p volume Omega 2) x := by
        rw [← h1, energyFormH1_comm_of_isSymm_ae (ae_of_all _ fun _ => Matrix.isSymm_one), h2]
    _ = _ := by
        refine integral_congr_ae ?_
        filter_upwards [hrep w hw] with x hx
        rw [hx]

/-- **Green kernels represent the weak solutions with `L²` data.** Let `Ω` be a bounded open
subset of `ℝⁿ⁺¹` and let `G` be a symmetric kernel that represents the weak solutions of the
Dirichlet problem for `-Δ` on `Ω` with smooth data: for every smooth `ψ` with compact support in
`Ω`, the weak solution `w ∈ H¹₀(Ω)` of `-Δw = ψ` is `w(x) = ∫ G(x, y) ψ(y) dy` for almost every
`x ∈ Ω`. If `f ∈ L²(Ω)` is such that `(x, y) ↦ G(x, y) f(y)` is integrable on `Ω × Ω`, then the
weak solution `u` of `-Δu = f` in `Ω`, `u = 0` on `∂Ω`, is the Green potential of `f`:

`u(x) = ∫_Ω G(x, y) f(y) dy` for almost every `x ∈ Ω`. -/
theorem IsWeakSolutionDirichlet.value_ae_eq_setIntegral_mul_of_forall_contDiff
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball z R)
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hG : ∀ x y, G x y = G y x)
    (hrep : ∀ ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →
      ∀ (g : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))),
      g =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))] ψ →
      ∀ w : W1p0 volume Omega 2, IsWeakSolutionDirichlet (fun _ => 1) 0 0 g w →
      W1p.value (w : W1p volume Omega 2)
        =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))]
          fun x => ∫ y, G x y * ψ y)
    {f : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))}
    (hGf : Integrable (Function.uncurry fun x y => G x y * f y)
      ((volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))).prod
        (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))))
    {u : W1p0 volume Omega 2} (hu : IsWeakSolutionDirichlet (fun _ => 1) 0 0 f u) :
    W1p.value (u : W1p volume Omega 2)
      =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))]
        fun x => ∫ y in Omega, G x y * f y := by
  have hfin : IsFiniteMeasure (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 ((measure_mono hΩ).trans_lt measure_ball_lt_top).ne
  have hint : ∀ v : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))),
      IntegrableOn v Omega := fun v => (Lp.memLp v).integrable one_le_two
  have hGfi : IntegrableOn (fun x => ∫ y in Omega, G x y * f y) Omega := hGf.integral_prod_left
  set D : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun x =>
    W1p.value (u : W1p volume Omega 2) x - ∫ y in Omega, G x y * f y with hD
  suffices h : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))), x ∈ Omega → D x = 0 by
    refine (ae_restrict_iff' Omega.isOpen.measurableSet).2 (h.mono fun x hx hxΩ => ?_)
    exact sub_eq_zero.1 (hx hxΩ)
  refine Omega.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hint _).sub hGfi).locallyIntegrableOn fun ψ hψ hψc hψsupp => ?_
  obtain ⟨C, hC⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  have hψmeas : AEStronglyMeasurable ψ (volume.restrict Omega) :=
    hψ.continuous.aestronglyMeasurable
  have hψ0 := Function.support_subset_iff'.1 ((subset_tsupport ψ).trans hψsupp)
  have hψL2 : MemLp ψ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    (hψ.continuous.memLp_of_hasCompactSupport hψc).restrict _
  calc ∫ x, ψ x • D x
      = ∫ x in Omega, ψ x * W1p.value (u : W1p volume Omega 2) x -
          ψ x * ∫ y in Omega, G x y * f y := by
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          rw [hψ0 x hx, zero_smul]]
        exact setIntegral_congr_fun Omega.isOpen.measurableSet fun x _ => by
          rw [hD, smul_eq_mul, mul_sub]
    _ = (∫ x in Omega, ψ x * W1p.value (u : W1p volume Omega 2) x) -
          ∫ x in Omega, ψ x * ∫ y in Omega, G x y * f y :=
        integral_sub ((hint _).bdd_mul hψmeas (Eventually.of_forall hC))
          (hGfi.bdd_mul hψmeas (Eventually.of_forall hC))
    -- The duality identity, then Fubini's theorem.
    _ = (∫ x in Omega, f x * ∫ y, G x y * ψ y) -
          ∫ y in Omega, ψ y * ∫ x in Omega, G y x * f x := by
        rw [hu.setIntegral_mul_value_eq hΩ hψL2
          (hrep ψ hψ hψc hψsupp (hψL2.toLp ψ) hψL2.coeFn_toLp)]
    _ = 0 := by
        rw [hGf.setIntegral_mul_integral_mul_comm Omega.isOpen.measurableSet hG hψmeas hC
          ((subset_tsupport ψ).trans hψsupp), sub_self]

end PDE

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Spectrum.Basic
public import TauCeti.Analysis.PDE.EnergyForm.Restriction

/-!
# Domain monotonicity of the first Dirichlet eigenvalue

For nested nonempty open sets `U ⊆ Ω`, the first Dirichlet eigenvalue of a symmetric
coercive energy form on `Ω` is at most its first Dirichlet eigenvalue on `U`. No boundary
regularity or connectedness is needed: extension by zero embeds `H¹₀(U)` into `H¹₀(Ω)`
and preserves both the energy and the `L²` norm.

The result is stated for the existing `firstDirichletEigenvalue`, the reciprocal norm of
the solution operator. It therefore also applies on unbounded open sets when the forms
are coercive, even if the spectral bottom is not attained. On bounded nonempty open sets
these quantities are actual eigenvalues. Nonemptiness of `U` is essential: on the empty
set the solution operator is zero and its reciprocal norm has the default value zero.

The coefficients are the same on the two domains. Coefficient boundedness, coercivity and
symmetry need only be supplied on `Ω`: boundedness restricts to `U`, and the other two
properties pass to `U` under zero extension. In particular the theorem applies to
`-Δ` on bounded open sets, with the coercivity data supplied by
`exists_isCoercive_laplacian_of_isBounded`.

## References

* L. C. Evans, *Partial Differential Equations*, Section 6.5: the Rayleigh principle for
  Dirichlet eigenvalues.
-/

public section

open MeasureTheory Set TopologicalSpace

open scoped ENNReal

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {U Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

/-- **Domain monotonicity of the first Dirichlet eigenvalue.** Enlarging a nonempty domain
can only decrease the spectral bottom of a symmetric coercive Dirichlet form with fixed
coefficients. Boundedness and boundary regularity of the domains are not required. -/
theorem firstDirichletEigenvalue_le_of_domain_le (hU : U ≤ Omega)
    (hU_nonempty : (U : Set (EuclideanSpace ℝ ι)).Nonempty)
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hsymm : ∀ u v : W1p0 mu Omega 2,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2)) :
    firstDirichletEigenvalue hcoeff hcoercive ≤
      firstDirichletEigenvalue
        (hcoeff.mono_measure (Measure.restrict_mono (SetLike.coe_subset_coe.mpr hU) le_rfl))
        (isCoercive_energyFormH1L0_of_domain_le hU hcoeff hcoercive) := by
  have hcoeffU :=
    hcoeff.mono_measure (Measure.restrict_mono (SetLike.coe_subset_coe.mpr hU) le_rfl)
  have hcoerciveU := isCoercive_energyFormH1L0_of_domain_le hU hcoeff hcoercive
  have hsymmU (u v : W1p0 mu U 2) :
      energyFormH1 a b c (u : W1p mu U 2) (v : W1p mu U 2) =
        energyFormH1 a b c (v : W1p mu U 2) (u : W1p mu U 2) := by
    rw [← energyFormH1_extendByZeroL a b c hU u v,
      ← energyFormH1_extendByZeroL a b c hU v u]
    exact hsymm _ _
  apply (isGreatest_firstDirichletEigenvalue hcoeffU hcoerciveU hsymmU hU_nonempty).2
  intro u
  have h := firstDirichletEigenvalue_mul_norm_value_sq_le hcoeff hcoercive hsymm
    (W1p0.extendByZeroL hU u)
  simpa only [W1p0.norm_value_extendByZeroL, energyFormH1_extendByZeroL] using h

end TauCeti.PDE

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Spectrum.Operator.Mixed
public import TauCeti.Analysis.Sobolev.LipschitzDomain.RellichKondrachov
import TauCeti.Analysis.InnerProductSpace.Variational.Rayleigh

/-!
# The first mixed eigenvalue

Let `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` be a divergence-form operator on an open set `Ω ⊆ ℝⁿ`, let
`Γ` be a set disjoint from `Ω`, typically a part of its boundary, and write `H¹_Γ(Ω)` for the
space `TauCeti.W1pVanishingOn mu Ω 2 Γ` of Sobolev functions vanishing on `Γ`. A **mixed
eigenvalue** is a `κ` for which

`a(u, v) = κ ∫_Ω u v` for every `v ∈ H¹_Γ(Ω)`

has a nonzero solution `u ∈ H¹_Γ(Ω)`: the Dirichlet condition on `Γ`, the natural (conormal)
condition on the rest of the boundary. When the energy form is coercive on `H¹_Γ(Ω)` itself, with
no shift, this file defines the **first mixed eigenvalue** `λ₁` as the reciprocal of the norm of
the solution operator `S` of the mixed problem (`TauCeti.PDE.firstMixedEigenvalue`), as
`TauCeti.PDE.firstDirichletEigenvalue` does for `Γ = ∂Ω`, with which it agrees there
(`TauCeti.PDE.firstMixedEigenvalue_frontier`). For a symmetric energy form:

* `λ₁ ‖u‖²_{L²} ≤ a(u, u)` on `H¹_Γ(Ω)`, and `λ₁` is the largest constant with this property
  (`TauCeti.PDE.isGreatest_firstMixedEigenvalue`);
* `λ₁` is at most every mixed eigenvalue (`TauCeti.PDE.firstMixedEigenvalue_le`), and on a domain
  with the Rellich property, that the value map `H¹(Ω) → L²(Ω)` is compact, it is itself a mixed
  eigenvalue: it is the minimum of the Rayleigh quotient `a(u, u) / ‖u‖²_{L²}`
  (`TauCeti.PDE.isLeast_rayleighQuotient_firstMixedEigenvalue`) and the least point of the
  spectrum of the mixed realization `A`
  (`TauCeti.PDE.isLeast_spectrum_mixedOperator_firstMixedEigenvalue`);
* `0` is a resolvent point of `A`, with resolvent `-S` there
  (`TauCeti.PDE.zero_mem_resolventSet_mixedOperator`, `TauCeti.PDE.resolvent_mixedOperator_zero`),
  so `A` has the inverse `S`, which is symmetric and, under the Rellich property, compact.

For the mixed Laplacian `-Δ_Γ`, with energy form `∫_Ω ∇u · ∇v`, coercivity on `H¹_Γ(Ω)` is exactly
a **Poincaré–Friedrichs inequality** `‖u‖_{L²} ≤ P ‖∇u‖_{L²}`
(`TauCeti.PDE.UniformlyEllipticOn.isCoercive_energyFormH1LVanishingOn_of_poincare`, transported
along `TauCeti.PDE.mixedForm_zero`), and `λ₁ = 1 / P²` for the optimal
constant `P` (`TauCeti.PDE.isLeast_norm_value_le_mul_norm_gradient_inv_sqrt_firstMixedEigenvalue`).
On a bounded connected Lipschitz domain the Poincaré–Friedrichs inequality holds as soon as `Γ`
meets the boundary in a set of positive surface measure. There, then, `λ₁ > 0` is the least point
of the spectrum of `-Δ_Γ`, it is the reciprocal of the square of the optimal Poincaré–Friedrichs
constant, and `-Δ_Γ` has a compact self-adjoint inverse
(`TauCeti.PDE.exists_firstMixedEigenvalue_laplacian_of_isLipschitzDomainWith`). For `Γ = ∅` none
of this holds on a bounded `Ω`: the constants have zero energy, and `0` is a mixed eigenvalue.

## Main declarations

* `TauCeti.PDE.firstMixedEigenvalue`: the first mixed eigenvalue `‖S‖⁻¹`.
* `TauCeti.PDE.firstMixedEigenvalue_pos`, `TauCeti.PDE.firstMixedEigenvalue_le`,
  `TauCeti.PDE.exists_ne_zero_forall_energyFormH1_eq_firstMixedEigenvalue_mul`: it is positive,
  at most every mixed eigenvalue, and under the Rellich property a mixed eigenvalue.
* `TauCeti.PDE.firstMixedEigenvalue_mul_norm_value_sq_le`,
  `TauCeti.PDE.isGreatest_firstMixedEigenvalue` and
  `TauCeti.PDE.isLeast_rayleighQuotient_firstMixedEigenvalue`: the Rayleigh principle.
* `TauCeti.PDE.isLeast_spectrum_mixedOperator_firstMixedEigenvalue`: it is the bottom of the
  spectrum of the mixed realization.
* `TauCeti.PDE.firstMixedEigenvalue_frontier`: at `Γ = ∂Ω` it is the first Dirichlet eigenvalue.
* `TauCeti.PDE.isLeast_norm_value_le_mul_norm_gradient_inv_sqrt_firstMixedEigenvalue`: for `-Δ_Γ`,
  the optimal Poincaré–Friedrichs constant.
* `TauCeti.PDE.exists_firstMixedEigenvalue_laplacian_of_isLipschitzDomainWith`: the mixed Laplacian
  on a bounded connected Lipschitz domain, for `Γ` of positive surface measure.
* `TauCeti.PDE.exists_ne_zero_forall_inner_gradient_eq_iff_of_complete`: for `-Δ_Γ`, on any open
  set, a family of eigenfunctions complete in `L²(Ω)` has all the eigenvalues. This is how the
  explicit spectra of intervals and rectangles are identified.
* `TauCeti.PDE.inner_gradient_eq_mul_inner_value_of_mem_w1pVanishingOnSubmodule`: a weak
  eigen-identity of `-Δ_Γ` extends from the generators of `H¹_Γ(Ω)` to all of it.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 9.31 and its proof (the Dirichlet case, which carries over to `H¹_Γ(Ω)`).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 6.5.1, Theorem 2 (the
  variational characterization of the principal eigenvalue).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Section 9.8 (eigenfunction expansions).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Bornology MeasureTheory Module Set TopologicalSpace
open scoped Distributions InnerProductSpace NNReal

/-! ### Eigenvalues of `-Δ_Γ` from a complete family of eigenfunctions -/

section Complete

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {Γ : Set E}

attribute [local instance] W1pVanishingOn.instNormedAddCommGroup

/-- **A weak eigen-identity extends from the generators of `H¹_Γ(Ω)` to all of it.** If
`∫ ∇u · ∇v = κ ∫ u v` holds whenever `v` is the restriction to `Ω` of a test function on `E` whose
support avoids the closure of `Γ`, then it holds for every `v ∈ H¹_Γ(Ω)`: both sides are continuous
in `v`, and `H¹_Γ(Ω)` is the closure of those restrictions. -/
theorem inner_gradient_eq_mul_inner_value_of_mem_w1pVanishingOnSubmodule {u : W1p mu Omega 2}
    {kappa : ℝ} (h : ∀ φ : 𝓓((⊤ : Opens E), ℝ), Disjoint (tsupport φ) (closure Γ) →
      ⟪W1p.gradient u, W1p.gradient (W1p.restrictL (le_top : Omega ≤ ⊤)
          (W1p.ofTestFunctionₗ mu ⊤ 2 φ))⟫_ℝ =
        kappa * ⟪W1p.value u, W1p.value (W1p.restrictL (le_top : Omega ≤ ⊤)
          (W1p.ofTestFunctionₗ mu ⊤ 2 φ))⟫_ℝ)
    {v : W1p mu Omega 2} (hv : v ∈ w1pVanishingOnSubmodule mu Omega 2 Γ) :
    ⟪W1p.gradient u, W1p.gradient v⟫_ℝ = kappa * ⟪W1p.value u, W1p.value v⟫_ℝ :=
  w1pVanishingOnSubmodule_subset_of_isClosed (s := {v | ⟪W1p.gradient u,
      W1p.gradient v⟫_ℝ = kappa * ⟪W1p.value u, W1p.value v⟫_ℝ})
    (isClosed_eq (continuous_const.inner (W1p.gradientL.continuous.congr W1p.gradientL_apply))
      (continuous_const.mul (continuous_const.inner
        (W1p.valueL.continuous.congr W1p.valueL_apply)))) h hv

/-- **The weak eigenvalues of `-Δ` on `H¹_Γ(Ω)` are those of a complete family of
eigenfunctions.** Let `w k ∈ H¹_Γ(Ω)`, `k ∈ ι`, be nonzero weak eigenfunctions,
`∫ ∇(w k) · ∇v = κₖ ∫ (w k) v` for every `v ∈ H¹_Γ(Ω)`, with values `F k`, and let the `F k` be
complete in `L²(Ω)`. Then the problem `∫ ∇u · ∇v = κ ∫ u v` for every `v ∈ H¹_Γ(Ω)` has a nonzero
solution `u ∈ H¹_Γ(Ω)` exactly when `κ` is one of the `κₖ`: the form `∫ ∇u · ∇v` is symmetric, so
an eigenfunction for any other `κ` is orthogonal in `L²(Ω)` to every `F k`, hence zero. -/
theorem exists_ne_zero_forall_inner_gradient_eq_iff_of_complete {ι : Type*} {kappas : ι → ℝ}
    (F : ι → E → ℝ) (w : ι → W1pVanishingOn mu Omega 2 Γ)
    (hwv : ∀ k, W1p.value (w k : W1p mu Omega 2) =ᵐ[mu.restrict Omega] F k)
    (hw0 : ∀ k, W1p.value (w k : W1p mu Omega 2) ≠ 0)
    (hw : ∀ k, ∀ v : W1pVanishingOn mu Omega 2 Γ,
      ⟪W1p.gradient (w k : W1p mu Omega 2), W1p.gradient (v : W1p mu Omega 2)⟫_ℝ =
        kappas k * ⟪W1p.value (w k : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ)
    (hc : ∀ f : Lp ℝ 2 (mu.restrict Omega), (∀ k, ∫ x in Omega, f x * F k x ∂mu = 0) → f = 0)
    {kappa : ℝ} :
    (∃ u : W1pVanishingOn mu Omega 2 Γ, u ≠ 0 ∧ ∀ v : W1pVanishingOn mu Omega 2 Γ,
      ⟪W1p.gradient (u : W1p mu Omega 2), W1p.gradient (v : W1p mu Omega 2)⟫_ℝ =
        kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ) ↔
      ∃ k, kappa = kappas k := by
  constructor
  · rintro ⟨u, hu0, hu⟩
    by_contra hne
    push Not at hne
    refine hu0 (W1pVanishingOn.valueL_injective ?_)
    rw [map_zero, W1pVanishingOn.valueL_apply]
    refine hc _ fun k => ?_
    -- `κ ⟪u, w k⟫ = ∫ ∇u · ∇(w k) = κₖ ⟪u, w k⟫`, and `κ ≠ κₖ`.
    have h1 := hu (w k)
    rw [real_inner_comm, hw k u, real_inner_comm (W1p.value _)] at h1
    have h2 : (kappa - kappas k) * ⟪W1p.value (u : W1p mu Omega 2),
        W1p.value (w k : W1p mu Omega 2)⟫_ℝ = 0 := by
      linarith
    rw [← (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (hne k)), L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hwv k] with x hx
    simp [hx, mul_comm]
  · rintro ⟨k, rfl⟩
    refine ⟨w k, fun h => hw0 k ?_, hw k⟩
    rw [← W1pVanishingOn.valueL_apply, h, map_zero]

end Complete

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {Γ : Set (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ}

attribute [local instance] W1pVanishingOn.instNormedAddCommGroup
  W1pVanishingOn.instInnerProductSpace

/-! ### The first mixed eigenvalue -/

/-- The **first mixed eigenvalue** of a divergence-form operator whose energy form is coercive on
`H¹_Γ(Ω)`: the reciprocal of the norm of the mixed solution operator. For a symmetric energy form
it is the optimal constant in `λ₁ ‖u‖²_{L²} ≤ a(u, u)`
(`TauCeti.PDE.isGreatest_firstMixedEigenvalue`), and on a domain with the Rellich property it is
the least mixed eigenvalue (`TauCeti.PDE.isLeast_spectrum_mixedOperator_firstMixedEigenvalue`). -/
def firstMixedEigenvalue
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (Γ : Set (EuclideanSpace ℝ ι)) (hB : IsCoercive (mixedForm hcoeff Γ 0)) : ℝ :=
  ‖mixedSolutionOperator hcoeff Γ hB‖⁻¹

/-- The first mixed eigenvalue is the reciprocal of the operator norm of the mixed solution
operator. -/
theorem firstMixedEigenvalue_def
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ 0)) :
    firstMixedEigenvalue hcoeff Γ hB = ‖mixedSolutionOperator hcoeff Γ hB‖⁻¹ :=
  (rfl)

/-- The unshifted mixed form of a symmetric energy form is symmetric. -/
private theorem mixedForm_zero_comm
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hsymm : ∀ u v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (u v : W1pVanishingOn mu Omega 2 Γ) :
    mixedForm hcoeff Γ 0 u v = mixedForm hcoeff Γ 0 v u := by
  rw [mixedForm_zero_apply, mixedForm_zero_apply]
  exact hsymm u v

/-- The first mixed eigenvalue is positive on a nonempty `Ω`, when `Γ` misses `Ω`. -/
theorem firstMixedEigenvalue_pos
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ 0)) (hΓ : Disjoint Γ Omega)
    (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) :
    0 < firstMixedEigenvalue hcoeff Γ hB := by
  rw [firstMixedEigenvalue_def, mixedSolutionOperator_def]
  exact inv_pos.mpr (norm_pos_iff.mpr
    (hB.formSolutionOperator_ne_zero (W1pVanishingOn.valueL_ne_zero hΓ hOmega)))

/-- **The first mixed eigenvalue is at most every mixed eigenvalue**: if
`a(u, v) = κ ∫_Ω u v` for some nonzero `u ∈ H¹_Γ(Ω)` and every `v ∈ H¹_Γ(Ω)`, then `λ₁ ≤ κ`. -/
theorem firstMixedEigenvalue_le
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ 0)) {kappa : ℝ} {u : W1pVanishingOn mu Omega 2 Γ}
    (hu : u ≠ 0)
    (heq : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ) :
    firstMixedEigenvalue hcoeff Γ hB ≤ kappa := by
  rw [firstMixedEigenvalue_def, mixedSolutionOperator_def]
  exact hB.inv_norm_formSolutionOperator_le W1pVanishingOn.valueL hu fun v ↦ by
    rw [mixedForm_zero_apply, heq v, W1pVanishingOn.valueL_apply,
      W1pVanishingOn.valueL_apply]

/-- **The first mixed eigenvalue is a mixed eigenvalue** on a nonempty domain with the Rellich
property, for a symmetric energy form: `a(u, v) = λ₁ ∫_Ω u v` for some nonzero `u ∈ H¹_Γ(Ω)` and
every `v ∈ H¹_Γ(Ω)`. -/
theorem exists_ne_zero_forall_energyFormH1_eq_firstMixedEigenvalue_mul
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ 0)) (hΓ : Disjoint Γ Omega)
    (hsymm : ∀ u v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) :
    ∃ u : W1pVanishingOn mu Omega 2 Γ, u ≠ 0 ∧
      ∀ v : W1pVanishingOn mu Omega 2 Γ,
        energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
          firstMixedEigenvalue hcoeff Γ hB *
            ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  obtain ⟨u, hu, heq⟩ := hB.exists_ne_zero_forall_apply_eq_inv_norm_smul_inner
    (W1pVanishingOn.isCompactOperator_valueL hK) (mixedForm_zero_comm hcoeff hsymm)
    (W1pVanishingOn.valueL_ne_zero hΓ hOmega)
  refine ⟨u, hu, fun v ↦ ?_⟩
  have hv := heq v
  rwa [mixedForm_zero_apply, W1pVanishingOn.valueL_apply,
    W1pVanishingOn.valueL_apply, ← mixedSolutionOperator_def, ← firstMixedEigenvalue_def] at hv

/-! ### The Rayleigh principle -/

/-- **The first mixed eigenvalue is a Poincaré constant for the energy form**:
`λ₁ ‖u‖²_{L²(Ω)} ≤ a(u, u)` for every `u ∈ H¹_Γ(Ω)`, for a symmetric energy form. By
`TauCeti.PDE.isGreatest_firstMixedEigenvalue` it is the largest such constant. -/
theorem firstMixedEigenvalue_mul_norm_value_sq_le
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ 0))
    (hsymm : ∀ u v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (u : W1pVanishingOn mu Omega 2 Γ) :
    firstMixedEigenvalue hcoeff Γ hB * ‖W1p.value (u : W1p mu Omega 2)‖ ^ 2 ≤
      energyFormH1 a b c (u : W1p mu Omega 2) (u : W1p mu Omega 2) := by
  rw [firstMixedEigenvalue_def, mixedSolutionOperator_def]
  have h := hB.inv_norm_formSolutionOperator_mul_norm_apply_sq_le W1pVanishingOn.valueL
    (mixedForm_zero_comm hcoeff hsymm) u
  rwa [mixedForm_zero_apply, W1pVanishingOn.valueL_apply] at h

/-- **The first mixed eigenvalue is the optimal Poincaré constant of the energy form**: on a
nonempty `Ω`, for `Γ` missing `Ω` and a symmetric energy form, `λ₁` is the largest `C` with
`C ‖u‖²_{L²(Ω)} ≤ a(u, u)` for every `u ∈ H¹_Γ(Ω)`. No compactness is needed. -/
theorem isGreatest_firstMixedEigenvalue
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ 0)) (hΓ : Disjoint Γ Omega)
    (hsymm : ∀ u v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) :
    IsGreatest {C : ℝ | ∀ u : W1pVanishingOn mu Omega 2 Γ,
        C * ‖W1p.value (u : W1p mu Omega 2)‖ ^ 2 ≤
          energyFormH1 a b c (u : W1p mu Omega 2) (u : W1p mu Omega 2)}
      (firstMixedEigenvalue hcoeff Γ hB) := by
  have hset : {C : ℝ | ∀ u : W1pVanishingOn mu Omega 2 Γ,
      C * ‖W1p.value (u : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (u : W1p mu Omega 2) (u : W1p mu Omega 2)} =
      {C : ℝ | ∀ u : W1pVanishingOn mu Omega 2 Γ,
        C * ‖W1pVanishingOn.valueL u‖ ^ 2 ≤ mixedForm hcoeff Γ 0 u u} := by
    simp only [W1pVanishingOn.valueL_apply, mixedForm_zero_apply]
  rw [hset, firstMixedEigenvalue_def, mixedSolutionOperator_def]
  exact hB.isGreatest_inv_norm_formSolutionOperator (mixedForm_zero_comm hcoeff hsymm)
    (W1pVanishingOn.valueL_ne_zero hΓ hOmega)

/-- **The Rayleigh principle for the mixed problem.** On a nonempty domain with the Rellich
property, for `Γ` missing `Ω` and a symmetric energy form, the first mixed eigenvalue is the
minimum of the Rayleigh quotient

`a(u, u) / ‖u‖²_{L²(Ω)}`

over the `u ∈ H¹_Γ(Ω)` with nonzero value; the minimum is attained at an eigenfunction. -/
theorem isLeast_rayleighQuotient_firstMixedEigenvalue
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ 0)) (hΓ : Disjoint Γ Omega)
    (hsymm : ∀ u v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) :
    IsLeast {r : ℝ | ∃ u : W1pVanishingOn mu Omega 2 Γ, W1p.value (u : W1p mu Omega 2) ≠ 0 ∧
        energyFormH1 a b c (u : W1p mu Omega 2) (u : W1p mu Omega 2) /
          ‖W1p.value (u : W1p mu Omega 2)‖ ^ 2 = r}
      (firstMixedEigenvalue hcoeff Γ hB) := by
  have hset : {r : ℝ | ∃ u : W1pVanishingOn mu Omega 2 Γ, W1p.value (u : W1p mu Omega 2) ≠ 0 ∧
      energyFormH1 a b c (u : W1p mu Omega 2) (u : W1p mu Omega 2) /
        ‖W1p.value (u : W1p mu Omega 2)‖ ^ 2 = r} =
      {r : ℝ | ∃ u : W1pVanishingOn mu Omega 2 Γ, W1pVanishingOn.valueL u ≠ 0 ∧
        mixedForm hcoeff Γ 0 u u / ‖W1pVanishingOn.valueL u‖ ^ 2 = r} := by
    simp only [W1pVanishingOn.valueL_apply, mixedForm_zero_apply]
  rw [hset, firstMixedEigenvalue_def, mixedSolutionOperator_def]
  exact hB.isLeast_rayleighQuotient (W1pVanishingOn.isCompactOperator_valueL hK)
    (mixedForm_zero_comm hcoeff hsymm) (W1pVanishingOn.valueL_ne_zero hΓ hOmega)

/-! ### The mixed realization -/

/-- Coercivity of the unshifted mixed form is the Gårding inequality with `ω = 0`. -/
private theorem exists_garding_of_isCoercive_mixedForm_zero
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ 0)) :
    ∃ theta : ℝ, 0 < theta ∧ ∀ v : W1pVanishingOn mu Omega 2 Γ,
      theta * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
          0 * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2 := by
  obtain ⟨C, hC, hle⟩ := hB
  refine ⟨C, hC, fun v ↦ ?_⟩
  have hv := hle v
  rw [mixedForm_zero_apply, ← Submodule.norm_coe] at hv
  rw [zero_mul, add_zero, sq, ← mul_assoc]
  exact hv

/-- **The first mixed eigenvalue is the bottom of the spectrum.** On a nonempty domain with the
Rellich property, for `Γ` missing `Ω` and a symmetric energy form coercive on `H¹_Γ(Ω)`, the first
mixed eigenvalue is the least point of the spectrum of the mixed realization. -/
theorem isLeast_spectrum_mixedOperator_firstMixedEigenvalue
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ 0)) (hΓ : Disjoint Γ Omega)
    (hsymm : ∀ u v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) :
    IsLeast (mixedOperator hcoeff Γ).spectrum (firstMixedEigenvalue hcoeff Γ hB) := by
  obtain ⟨theta, htheta, hgarding⟩ := exists_garding_of_isCoercive_mixedForm_zero hcoeff hB
  refine ⟨(mem_spectrum_mixedOperator_iff hcoeff hΓ htheta hgarding hK).2
    (exists_ne_zero_forall_energyFormH1_eq_firstMixedEigenvalue_mul hcoeff hB hΓ hsymm hK hOmega),
    fun kappa hkappa ↦ ?_⟩
  obtain ⟨u, hu, heq⟩ := (mem_spectrum_mixedOperator_iff hcoeff hΓ htheta hgarding hK).1 hkappa
  exact firstMixedEigenvalue_le hcoeff hB hu heq

/-- **At the whole frontier the first mixed eigenvalue is the first Dirichlet eigenvalue**: the
mixed realization at `Γ = ∂Ω` is the Dirichlet realization, so the two solution operators, minus
their resolvents at `0`, agree. -/
theorem firstMixedEigenvalue_frontier
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff (frontier (Omega : Set (EuclideanSpace ℝ ι))) 0))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) :
    firstMixedEigenvalue hcoeff (frontier (Omega : Set (EuclideanSpace ℝ ι))) hB =
      firstDirichletEigenvalue hcoeff hcoercive := by
  have h := resolvent_mixedOperator_zero hcoeff (disjoint_frontier_iff_isOpen.2 Omega.isOpen) hB
  rw [mixedOperator_frontier hcoeff hcoercive, resolvent_dirichletOperator_zero, neg_inj] at h
  rw [firstMixedEigenvalue_def, firstDirichletEigenvalue_def, h]

/-! ### The mixed Laplacian -/

section Laplacian

variable [DecidableEq ι]

/-- **The optimal Poincaré–Friedrichs constant is `1 / √λ₁`.** On a nonempty `Ω`, for `Γ` missing
`Ω`, when `∫_Ω ∇u · ∇v` is coercive on `H¹_Γ(Ω)`, the least `P ≥ 0` with
`‖u‖_{L²(Ω)} ≤ P ‖∇u‖_{L²(Ω)}` for every `u ∈ H¹_Γ(Ω)` is `1 / √λ₁` for the first mixed
eigenvalue `λ₁` of `-Δ_Γ`: `λ₁` is the reciprocal of the square of the optimal constant. -/
theorem isLeast_norm_value_le_mul_norm_gradient_inv_sqrt_firstMixedEigenvalue
    (hΓ : Disjoint Γ Omega) (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty)
    (hB : IsCoercive (mixedForm (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ 0)) :
    IsLeast {P : ℝ | 0 ≤ P ∧ ∀ u ∈ w1pVanishingOnSubmodule mu Omega 2 Γ,
        ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖}
      (√(firstMixedEigenvalue _ Γ hB))⁻¹ := by
  have hpos := firstMixedEigenvalue_pos _ hB hΓ hOmega
  have hgreat := isGreatest_firstMixedEigenvalue _ hB hΓ
    (fun u v ↦ energyFormH1_one_zero_zero_comm (u : W1p mu Omega 2) v) hOmega
  have hsqrt := Real.sqrt_pos.mpr hpos
  refine ⟨⟨inv_nonneg.mpr (Real.sqrt_nonneg _), fun u hu ↦ ?_⟩, fun P ⟨hP0, hP⟩ ↦ ?_⟩
  · -- `λ₁ ‖u‖² ≤ ‖∇u‖²`, so `√λ₁ ‖u‖ ≤ ‖∇u‖`.
    have h := hgreat.1 ⟨u, hu⟩
    rw [energyFormH1_one_zero_zero_eq_inner, real_inner_self_eq_norm_sq] at h
    rw [← div_eq_inv_mul, le_div_iff₀ hsqrt]
    refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp ?_
    rw [mul_pow, Real.sq_sqrt hpos.le]
    linarith
  · -- `P = 0` would kill every value; otherwise `1 / P²` is a Poincaré constant, so `≤ λ₁`.
    have hPpos : 0 < P := by
      refine hP0.lt_of_ne fun h ↦ W1pVanishingOn.valueL_ne_zero (mu := mu) (p := 2) hΓ hOmega ?_
      ext1 u
      have hu := hP _ u.property
      rw [← h, zero_mul, norm_le_zero_iff] at hu
      rw [W1pVanishingOn.valueL_apply, hu, zero_apply]
    have hC : (P ^ 2)⁻¹ ≤ firstMixedEigenvalue _ Γ hB := hgreat.2 fun u ↦ by
      rw [energyFormH1_one_zero_zero_eq_inner, real_inner_self_eq_norm_sq,
        inv_mul_le_iff₀ (by positivity), ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hP _ u.property) 2
    rw [inv_le_comm₀ hsqrt hPpos, Real.le_sqrt (inv_nonneg.mpr hP0) hpos.le, inv_pow]
    exact hC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {V : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0}

/-- **The first mixed eigenvalue of `-Δ_Γ` for a boundary part of positive measure.** Let an
affine isometry `e` carry the connected open set `Ω ⊆ EuclideanSpace ℝ ι` onto a bounded Lipschitz
domain `V`, and let `Γ`, disjoint from `Ω`, meet the frontier of `Ω` in a set of positive surface
measure. Then `∫_Ω ∇u · ∇v` is coercive on `H¹_Γ(Ω)`, and its first mixed eigenvalue `λ₁`

* is positive;
* is the least point of the spectrum of the mixed Laplacian `-Δ_Γ`;
* is the reciprocal of the square of the optimal Poincaré–Friedrichs constant: `1 / √λ₁` is the
  least `P ≥ 0` with `‖u‖_{L²(Ω)} ≤ P ‖∇u‖_{L²(Ω)}` on `H¹_Γ(Ω)`.

Moreover `-Δ_Γ` is invertible with a compact self-adjoint inverse: `0` is a resolvent point, where
the resolvent is `-S` for the mixed solution operator `S`, which is compact and symmetric. -/
theorem exists_firstMixedEigenvalue_laplacian_of_isLipschitzDomainWith
    (hV : (V : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hVb : IsBounded (V : Set (WithLp 2 (ℝ × E))))
    (e : EuclideanSpace ℝ ι ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
    (hVΩ : (V : Set (WithLp 2 (ℝ × E))) = e.symm ⁻¹' Omega)
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hΓ : (μHE[finrank ℝ E] : Measure (EuclideanSpace ℝ ι))
      (Γ ∩ frontier (Omega : Set (EuclideanSpace ℝ ι))) ≠ 0)
    (hΓΩ : Disjoint Γ Omega) :
    ∃ hB : IsCoercive (mixedForm (memLp_energyIntegrand_const_zero_zero (mu := volume)
        (Omega := Omega) (1 : Matrix ι ι ℝ)) Γ 0),
      0 < firstMixedEigenvalue _ Γ hB ∧
      IsLeast (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := volume)
        (Omega := Omega) (1 : Matrix ι ι ℝ)) Γ).spectrum (firstMixedEigenvalue _ Γ hB) ∧
      IsLeast {P : ℝ | 0 ≤ P ∧ ∀ u ∈ w1pVanishingOnSubmodule volume Omega 2 Γ,
          ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖} (√(firstMixedEigenvalue _ Γ hB))⁻¹ ∧
      (0 : ℝ) ∈ (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := volume)
        (Omega := Omega) (1 : Matrix ι ι ℝ)) Γ).resolventSet ∧
      (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := volume)
        (Omega := Omega) (1 : Matrix ι ι ℝ)) Γ).resolvent 0 =
          -mixedSolutionOperator _ Γ hB ∧
      IsCompactOperator (mixedSolutionOperator _ Γ hB) ∧
      LinearMap.IsSymmetric (mixedSolutionOperator _ Γ hB :
        Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι))) →ₗ[ℝ]
          Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) := by
  -- `Ω` is nonempty, since `Γ` meets its frontier in a set of positive measure.
  have hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty := by
    refine ne_empty_iff_nonempty.mp fun h ↦ hΓ ?_
    rw [h, frontier_empty, inter_empty, measure_empty]
  have hB := isCoercive_mixedForm_laplacian_of_isLipschitzDomainWith hV hVb e hVΩ hconn hΓ
  have hK := W1p.isCompactOperator_valueL_of_isLipschitzDomainWith_of_affineIsometryEquiv
    (p := 2) hV hVb e hVΩ
  have hsymm (u v : W1pVanishingOn volume Omega 2 Γ) :
      energyFormH1 (fun _ ↦ 1) 0 0 (u : W1p volume Omega 2) (v : W1p volume Omega 2) =
        energyFormH1 (fun _ ↦ 1) 0 0 (v : W1p volume Omega 2) (u : W1p volume Omega 2) :=
    energyFormH1_one_zero_zero_comm _ _
  exact ⟨hB, firstMixedEigenvalue_pos _ hB hΓΩ hOmega,
    isLeast_spectrum_mixedOperator_firstMixedEigenvalue _ hB hΓΩ hsymm hK hOmega,
    isLeast_norm_value_le_mul_norm_gradient_inv_sqrt_firstMixedEigenvalue hΓΩ hOmega hB,
    zero_mem_resolventSet_mixedOperator _ hΓΩ hB, resolvent_mixedOperator_zero _ hΓΩ hB,
    isCompactOperator_mixedSolutionOperator _ hB hK, isSymmetric_mixedSolutionOperator _ hB hsymm⟩

end Laplacian

end PDE

end TauCeti

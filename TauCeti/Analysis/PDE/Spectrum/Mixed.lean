/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Variational.Sequence
public import TauCeti.Analysis.PDE.Spectrum.MinMax
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart
import TauCeti.Analysis.Sobolev.LipschitzDomain.RellichKondrachov

/-!
# Mixed and Neumann eigenvalues

Let `Ω ⊆ ℝⁿ` be open, let `Γ` be a set disjoint from `Ω`, typically a part of its boundary, and
let `H¹_Γ(Ω)` be the space `TauCeti.w1pVanishingOnSubmodule mu Ω 2 Γ` of Sobolev functions
vanishing on `Γ`: the closure in `H¹(Ω)` of the restrictions of test functions supported away
from `closure Γ`, so it depends on `Γ` only through `closure Γ`. For the divergence-form operator
`L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` with energy form `a(u, v)`, a real number `κ` is a
**mixed eigenvalue** (`TauCeti.PDE.IsMixedEigenvalue`) when some nonzero `u ∈ H¹_Γ(Ω)` satisfies

`a(u, v) = κ ∫_Ω u v` for every `v ∈ H¹_Γ(Ω)`.

This is the weak form of `L u = κ u` in `Ω` with the Dirichlet condition `u = 0` on `closure Γ`,
which may be larger than `Γ`, and, formally (for solutions and boundaries regular enough for the
conormal derivative to make sense), the natural (conormal) condition on the remaining boundary
`∂Ω \ closure Γ`, where the test functions `v` are not constrained. For `Γ = ∂Ω` it is the
Dirichlet eigenvalue problem (`TauCeti.PDE.isMixedEigenvalue_frontier_iff`). For `Γ = ∅` it is
the Neumann eigenvalue problem whenever `H¹_∅(Ω) = H¹(Ω)`. This identity is currently proved
only for bounded Lipschitz domains in the model coordinates `ℝ × E` with Lebesgue measure
`volume` (`TauCeti.w1pVanishingOnSubmodule_empty_of_isLipschitzDomainWith`), not for this file's
domains in `EuclideanSpace ℝ ι` with a general Haar measure.

Unlike the Dirichlet case, the energy form need not be coercive on `H¹_Γ(Ω)`: for `-Δ` and
`Γ = ∅` the constants have zero energy. It is coercive after a shift by the `L²` inner product,
`θ ‖u‖²_{H¹} ≤ a(u, u) + ω ‖u‖²_{L²}` (a Gårding inequality on `H¹_Γ(Ω)`, with `θ = ω = 1` for
`-Δ`). Under this inequality, symmetry of the form and the **Rellich property** of `Ω`, that the
value map `H¹(Ω) → L²(Ω)` is compact, as it is on a bounded Lipschitz domain (for domains in
`ℝ × E` this is `TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomainWith`), the mixed
eigenvalues form a sequence

`λ₀ ≤ λ₁ ≤ λ₂ ≤ ⋯ → ∞`,

repeated according to multiplicity, with an orthonormal basis of `L²(Ω)` of eigenfunctions in
`H¹_Γ(Ω)` (`TauCeti.PDE.exists_hilbertBasis_nat_isMixedEigenvalue_monotone`). The eigenvalues of
the shifted form are `λₖ + ω`; they are positive, and the abstract eigenbasis of a coercive form
along a compact embedding of dense range applies to it. The value map `H¹_Γ(Ω) → L²(Ω)` has dense
range because `H¹_Γ(Ω)` contains `H¹₀(Ω)` when `Γ` misses `Ω`.

The **min–max principle** defines the `k`-th mixed eigenvalue `λₖ` without eigenfunctions
(`TauCeti.PDE.mixedEigenvalue`): the infimum of the `C` for which some subspace of `H¹_Γ(Ω)`, whose
values span a subspace of `L²(Ω)` of dimension at least `k + 1`, satisfies `a(v, v) ≤ C ‖v‖²_{L²}`
on it. For a symmetric form bounded below, `a(v, v) + ω ‖v‖²_{L²} ≥ 0`, with an eigenbasis it is
the `k`-th term of every nondecreasing listing of the eigenvalues
(`TauCeti.PDE.mixedEigenvalue_eq_of_hilbertBasis`), and the infimum is attained
(`TauCeti.PDE.isLeast_mixedEigenvalue`); a Gårding inequality makes the form bounded below. At
`Γ = ∂Ω` it is the Dirichlet eigenvalue `TauCeti.PDE.dirichletEigenvalue`
(`TauCeti.PDE.mixedEigenvalue_frontier`), and since `H¹_Γ(Ω)` shrinks as `Γ` grows, the
eigenvalues grow with `Γ`: `λₖ(Γ) ≤ λₖ(Γ')` for `Γ ⊆ Γ'`
(`TauCeti.PDE.mixedEigenvalue_le_of_subset`).

For `-Δ`, whose energy form is `∫_Ω ∇u · ∇v`, all hypotheses except the Rellich property hold
outright, and the Rellich property holds on every bounded Lipschitz domain of `ℝⁿ`
(`TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomain`). So on a nonempty bounded
Lipschitz domain the mixed eigenvalues of `-Δ` are nonnegative and the eigenbasis and min–max
hold outright (`TauCeti.PDE.mixedEigenvalue_laplacian_spectrum`).

## Main declarations

* `TauCeti.PDE.IsMixedEigenvalue`: the mixed eigenvalue problem, and
  `TauCeti.PDE.isMixedEigenvalue_frontier_iff`: at `Γ = ∂Ω` it is the Dirichlet one.
* `TauCeti.PDE.exists_hilbertBasis_nat_isMixedEigenvalue_monotone`: the mixed eigenvalues of a
  symmetric form satisfying a Gårding inequality on `H¹_Γ(Ω)`, as a nondecreasing sequence tending
  to infinity with an orthonormal eigenbasis of `L²(Ω)`.
* `TauCeti.PDE.mixedEigenvalue`: the `k`-th mixed eigenvalue, by min–max, with
  `TauCeti.PDE.mixedEigenvalue_eq_of_hilbertBasis`, `TauCeti.PDE.isLeast_mixedEigenvalue`,
  `TauCeti.PDE.exists_hilbertBasis_mixedEigenvalue`, `TauCeti.PDE.monotone_mixedEigenvalue`,
  `TauCeti.PDE.tendsto_mixedEigenvalue_atTop`,
  `TauCeti.PDE.isMixedEigenvalue_iff_exists_mixedEigenvalue_eq` and, for a nonnegative form,
  `TauCeti.PDE.mixedEigenvalue_nonneg`.
* `TauCeti.PDE.mixedEigenvalue_frontier` and `TauCeti.PDE.mixedEigenvalue_le_of_subset`: the
  Dirichlet case and monotonicity in `Γ`.
* `TauCeti.PDE.exists_hilbertBasis_mixedEigenvalue_laplacian`,
  `TauCeti.PDE.isLeast_mixedEigenvalue_laplacian`,
  `TauCeti.PDE.mixedEigenvalue_laplacian_spectrum` and
  `TauCeti.PDE.mixedEigenvalue_laplacian_le_of_subset`: the same for `-Δ`, and
  `TauCeti.PDE.mixedEigenvalue_laplacian_le_dirichletEigenvalue`: for `Γ ⊆ ∂Ω` the mixed
  eigenvalues of `-Δ` lie below the Dirichlet ones.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 9.31 and its proof (the Dirichlet case), and Proposition 9.24 (the Neumann problem).
* R. Courant and D. Hilbert, *Methods of Mathematical Physics*, Vol. I, Chapter VI, §1–§2 (the
  min–max principle and the comparison of boundary conditions).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Bornology Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace NNReal

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {Γ Γ' : Set (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ}

/-- Shortcut instance for the normed group structure of `H¹_Γ(Ω)`, inherited through the nested
Sobolev subspaces; instance search can time out on it inside abstract Hilbert space lemmas. -/
local instance : NormedAddCommGroup (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule :=
  inferInstance

/-- Shortcut instance for the Hilbert space structure of `H¹_Γ(Ω)`. -/
local instance : InnerProductSpace ℝ (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule :=
  inferInstance

/-- `H¹_Γ(Ω)` is complete, as a closed subspace of `H¹(Ω)`. -/
local instance : CompleteSpace (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule :=
  (w1pVanishingOnSubmodule mu Omega 2 Γ).isClosed.completeSpace_coe

/-! ### Mixed eigenvalues -/

variable (mu Omega Γ a b c) in
/-- **A mixed eigenvalue** of the divergence-form operator `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u`
on `Ω`, with the Dirichlet condition on `closure Γ`: a real number `κ` for which some
nonzero `u ∈ H¹_Γ(Ω)` satisfies

`a(u, v) = κ ∫_Ω u v` for every `v ∈ H¹_Γ(Ω)`,

where `a` is the energy form of `L` and `H¹_Γ(Ω)` is `TauCeti.w1pVanishingOnSubmodule`, the closure
of the test functions supported away from `closure Γ`. So the Dirichlet condition is imposed on
`closure Γ`, which may be larger than `Γ`. The test functions are unconstrained on the remaining
boundary `∂Ω \ closure Γ`, where, for regular enough solutions and boundaries, this weak
formulation encodes the natural (conormal) boundary condition. For
`Γ = ∂Ω` this is `TauCeti.PDE.IsDirichletEigenvalue`, and for `Γ = ∅`, on a domain where
`H¹_∅(Ω) = H¹(Ω)`, the Neumann eigenvalue problem. -/
def IsMixedEigenvalue (kappa : ℝ) : Prop :=
  ∃ u : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule, u ≠ 0 ∧
    ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ

/-- Unfolding `TauCeti.PDE.IsMixedEigenvalue`: a nonzero `u ∈ H¹_Γ(Ω)` with
`a(u, v) = κ ⟪u, v⟫_{L²(Ω)}` for every `v ∈ H¹_Γ(Ω)`. -/
theorem isMixedEigenvalue_iff (kappa : ℝ) :
    IsMixedEigenvalue mu Omega Γ a b c kappa ↔
      ∃ u : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule, u ≠ 0 ∧
        ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
          energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
            kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ :=
  Iff.rfl

/-- **At the whole frontier the mixed eigenvalues are the Dirichlet eigenvalues**, since
`H¹_{∂Ω}(Ω) = H¹₀(Ω)` (`TauCeti.w1pVanishingOnSubmodule_frontier`). -/
@[simp]
theorem isMixedEigenvalue_frontier_iff (kappa : ℝ) :
    IsMixedEigenvalue mu Omega (frontier (Omega : Set (EuclideanSpace ℝ ι))) a b c kappa ↔
      IsDirichletEigenvalue mu Omega a b c kappa := by
  rw [IsMixedEigenvalue, w1pVanishingOnSubmodule_frontier, isDirichletEigenvalue_iff]

/-! ### The shifted energy form on `H¹_Γ(Ω)` -/

/-- The value map `H¹_Γ(Ω) → L²(Ω)`. -/
private def valueL (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
    (Omega : Opens (EuclideanSpace ℝ ι)) (Γ : Set (EuclideanSpace ℝ ι)) :
    (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule →L[ℝ] Lp ℝ 2 (mu.restrict Omega) :=
  W1p.valueL.comp (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule.subtypeL

private theorem valueL_apply (u : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule) :
    valueL mu Omega Γ u = W1p.value (u : W1p mu Omega 2) := by
  simp [valueL]

/-- The energy form on `H¹_Γ(Ω)` shifted by `ω` times the `L²` inner product of the values, in
the shape `B + ω ⟪J ·, J ·⟫` of `TauCeti.isCoercive_add_smul_toSesqForm_comp_of_garding`. -/
private def shiftedForm
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (Γ : Set (EuclideanSpace ℝ ι)) (omega : ℝ) :
    (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule →L[ℝ]
      (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule →L[ℝ] ℝ :=
  (energyFormH1L hcoeff).bilinearComp (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule.subtypeL
      (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule.subtypeL +
    omega • ((ContinuousLinearMap.toSesqForm (valueL mu Omega Γ)).comp (valueL mu Omega Γ) :
      (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule →L[ℝ]
        (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule →L[ℝ] ℝ)

private theorem shiftedForm_apply
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (omega : ℝ) (u v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule) :
    shiftedForm hcoeff Γ omega u v =
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) +
        omega * ⟪valueL mu Omega Γ u, valueL mu Omega Γ v⟫_ℝ := by
  rw [← energyFormH1L_apply hcoeff]
  rfl

/-- The eigenvalue equations of the energy form and of its shift by `ω` correspond, with
eigenvalues `κ` and `κ + ω`. -/
private theorem forall_shiftedForm_eq_iff
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (omega kappa : ℝ) (u : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule) :
    (∀ v, shiftedForm hcoeff Γ omega u v =
        (kappa + omega) * ⟪valueL mu Omega Γ u, valueL mu Omega Γ v⟫_ℝ) ↔
      ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
        energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
          kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  refine forall_congr' fun v ↦ ?_
  rw [shiftedForm_apply, valueL_apply, valueL_apply, add_mul]
  exact add_left_inj _

/-- A Gårding inequality on `H¹_Γ(Ω)` is coercivity of the shifted form
(`TauCeti.isCoercive_add_smul_toSesqForm_comp_of_garding`). -/
private theorem isCoercive_shiftedForm
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    {theta omega : ℝ} (htheta : 0 < theta)
    (hgarding : ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      theta * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
          omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2) :
    IsCoercive (shiftedForm hcoeff Γ omega) :=
  isCoercive_add_smul_toSesqForm_comp_of_garding htheta fun v ↦ by
    rw [ContinuousLinearMap.bilinearComp_apply, Submodule.subtypeL_apply, energyFormH1L_apply,
      valueL_apply]
    exact hgarding v

/-- The value map `H¹_Γ(Ω) → L²(Ω)` has dense range when `Γ` misses `Ω`, since `H¹_Γ(Ω)` contains
`H¹₀(Ω)`. -/
private theorem denseRange_valueL (hΓ : Disjoint Γ Omega) : DenseRange (valueL mu Omega Γ) :=
  W1p0.denseRange_valueL_two.mono <| by
    rintro _ ⟨w, rfl⟩
    exact ⟨⟨w, w1p0Submodule_le_w1pVanishingOnSubmodule hΓ w.property⟩, by
      simp only [valueL_apply, W1p0.valueL_apply]⟩

/-! ### The mixed eigenvalues as a sequence -/

/-- **The mixed eigenvalues form a sequence `λ₀ ≤ λ₁ ≤ ⋯ → ∞`.** Let `Ω ⊆ ℝⁿ`, `n ≥ 1`, be a
nonempty open set with the Rellich property, that the value map `H¹(Ω) → L²(Ω)` is compact, for
instance a bounded Lipschitz domain, and let `Γ` miss `Ω`. Let the energy form `a` be symmetric on
`H¹_Γ(Ω)` and satisfy the Gårding inequality `θ ‖v‖²_{H¹} ≤ a(v, v) + ω ‖v‖²_{L²}` there, with
`θ > 0`. Then there are a nondecreasing sequence `λₖ` tending to infinity and an orthonormal basis
`(eₖ)` of `L²(Ω)` such that `eₖ` is the value of some `uₖ ∈ H¹_Γ(Ω)` with

`a(uₖ, v) = λₖ ∫_Ω uₖ v` for every `v ∈ H¹_Γ(Ω)`.

The sequence lists the mixed spectrum with multiplicity: `κ` is a mixed eigenvalue exactly when
`κ = λₖ` for some `k`. -/
theorem exists_hilbertBasis_nat_isMixedEigenvalue_monotone [Nonempty ι]
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hrellich : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hΓ : Disjoint Γ Omega)
    (hsymm : ∀ u v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    {theta omega : ℝ} (htheta : 0 < theta)
    (hgarding : ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      theta * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
          omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2)
    (hOmega_nonempty : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) :
    ∃ (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (mu.restrict Omega))) (kappa : ℕ → ℝ)
      (u : ℕ → (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule),
      Monotone kappa ∧ Tendsto kappa atTop atTop ∧
      (∀ k, W1p.value (u k : W1p mu Omega 2) = basis k) ∧
      (∀ (k : ℕ) (v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule),
        energyFormH1 a b c (u k : W1p mu Omega 2) (v : W1p mu Omega 2) =
          kappa k * ⟪W1p.value (u k : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ) ∧
      ∀ kappa' : ℝ, IsMixedEigenvalue mu Omega Γ a b c kappa' ↔ ∃ k, kappa k = kappa' := by
  have hB := isCoercive_shiftedForm hcoeff htheta hgarding
  obtain ⟨basis, kappa, u, hmono, htendsto, -, hvalue, heq, hiff, -⟩ :=
    hB.exists_hilbertBasis_nat_forall_apply_eq_smul_inner_monotone
      (hrellich.comp_clm (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule.subtypeL)
      (denseRange_valueL hΓ)
      (fun u v ↦ by rw [shiftedForm_apply, shiftedForm_apply, hsymm, real_inner_comm])
      (L2.not_finiteDimensional_restrict_of_isOpen mu Omega.isOpen hOmega_nonempty)
  refine ⟨basis, fun k ↦ kappa k - omega, u, fun k l hkl ↦ by simpa using hmono hkl,
    by simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-omega) htendsto,
    fun k ↦ by rw [← valueL_apply, hvalue],
    fun k ↦ (forall_shiftedForm_eq_iff hcoeff omega _ (u k)).1 ?_, fun kappa' ↦ ?_⟩
  · simpa only [sub_add_cancel] using heq k
  · rw [isMixedEigenvalue_iff]
    simp_rw [← forall_shiftedForm_eq_iff hcoeff omega kappa', hiff (kappa' + omega),
      sub_eq_iff_eq_add]

/-! ### The min–max principle -/

variable (mu Omega Γ a b c) in
/-- **The `k`-th mixed eigenvalue** of the divergence-form operator with coefficients `a, b, c` on
`Ω`, with the Dirichlet condition on `closure Γ`, counted from `k = 0` with multiplicity, by the
Courant–Fischer min–max principle: the infimum of the constants `C` such that
`a(v, v) ≤ C ‖v‖²_{L²(Ω)}` for every `v` in some subspace `W` of `H¹_Γ(Ω)` whose values span a
subspace of `L²(Ω)` of dimension at least `k + 1`.

For a symmetric form bounded below, `a(v, v) + ω ‖v‖²_{L²} ≥ 0`, with an orthonormal eigenbasis
the infimum is attained and equals the `k`-th term of the nondecreasing listing of the eigenvalues
(`TauCeti.PDE.mixedEigenvalue_eq_of_hilbertBasis`). Otherwise the infimum may be over an empty or
unbounded set, and the value carries no information. -/
def mixedEigenvalue (k : ℕ) : ℝ :=
  sInf {C : ℝ | ∃ W : Submodule ℝ (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
    k + 1 ≤ Module.finrank ℝ
      (W.map ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ
        (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule.subtype)) ∧
      ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
        C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2}

/-- The definition of the `k`-th mixed eigenvalue as an infimum. -/
theorem mixedEigenvalue_def (k : ℕ) :
    mixedEigenvalue mu Omega Γ a b c k =
      sInf {C : ℝ | ∃ W : Submodule ℝ (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
        k + 1 ≤ Module.finrank ℝ
          (W.map ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ
            (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule.subtype)) ∧
          ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
            C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2} :=
  (rfl)

/-- **At the whole frontier the mixed eigenvalues are the Dirichlet eigenvalues**, since
`H¹_{∂Ω}(Ω) = H¹₀(Ω)` (`TauCeti.w1pVanishingOnSubmodule_frontier`). -/
@[simp]
theorem mixedEigenvalue_frontier :
    mixedEigenvalue mu Omega (frontier (Omega : Set (EuclideanSpace ℝ ι))) a b c =
      dirichletEigenvalue mu Omega a b c := by
  have hJ : (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ
      (w1p0Submodule mu Omega 2).toSubmodule.subtype = (W1p0.valueL).toLinearMap :=
    LinearMap.ext fun v ↦ by simp
  funext k
  rw [mixedEigenvalue_def, dirichletEigenvalue_def, w1pVanishingOnSubmodule_frontier, hJ]

/-- The min–max principle `TauCeti.isLeast_minMax_of_hilbertBasis` for the energy form on
`H¹_Γ(Ω)` and the value map `H¹_Γ(Ω) → L²(Ω)`, for a form bounded below by `-ω ‖v‖²_{L²}`. It
is applied to the nonnegative form shifted by `ω`, with eigenvalues `κⱼ + ω`, and the least
constant is shifted back by `ω`. -/
private theorem isLeast_of_hilbertBasis
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hsymm : ∀ u v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    {omega : ℝ} (hlower : ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      0 ≤ energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
        omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2)
    (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (mu.restrict Omega))) {kappa : ℕ → ℝ}
    (hkappa : Monotone kappa) {u : ℕ → (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule}
    (hvalue : ∀ j, W1p.value (u j : W1p mu Omega 2) = basis j)
    (heq : ∀ (j : ℕ) (v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule),
      energyFormH1 a b c (u j : W1p mu Omega 2) (v : W1p mu Omega 2) =
        kappa j * ⟪W1p.value (u j : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ)
    (k : ℕ) :
    IsLeast {C : ℝ | ∃ W : Submodule ℝ (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      k + 1 ≤ Module.finrank ℝ
        (W.map ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ
          (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule.subtype)) ∧
        ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
          C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2} (kappa k) := by
  let J := (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ
    (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule.subtype
  have hJ (v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule) :
      J v = W1p.value (v : W1p mu Omega 2) := by
    simp [J]
  have hB (u v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule) :
      (shiftedForm hcoeff Γ omega).toLinearMap₁₂ u v =
        energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) +
          omega * ⟪J u, J v⟫_ℝ := by
    rw [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, shiftedForm_apply, valueL_apply,
      valueL_apply, hJ, hJ]
  -- `C` is admissible for the form exactly when `C + ω` is admissible for the shifted form.
  have hmem (W : Submodule ℝ (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule) (C : ℝ) :
      (∀ v ∈ W, (shiftedForm hcoeff Γ omega).toLinearMap₁₂ v v ≤ (C + omega) * ‖J v‖ ^ 2) ↔
        ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
          C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2 := by
    refine forall₂_congr fun v _ ↦ ?_
    rw [hB, real_inner_self_eq_norm_sq, hJ, add_mul]
    exact add_le_add_iff_right (omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2)
  have h := isLeast_minMax_of_hilbertBasis (B := (shiftedForm hcoeff Γ omega).toLinearMap₁₂)
    (J := J) (fun v w ↦ by rw [hB, hB, hsymm, real_inner_comm])
    (fun v ↦ by rw [hB, real_inner_self_eq_norm_sq, hJ]; exact hlower v)
    basis (kappa := fun j ↦ kappa j + omega) (fun _ _ hij ↦ by simpa using hkappa hij)
    (fun j ↦ by rw [hJ, hvalue]) (fun j v ↦ by rw [hB, hJ, hJ, heq, add_mul]) k
  refine ⟨?_, fun C ⟨W, hW, hC⟩ ↦ le_of_add_le_add_right (h.2 ⟨W, hW, (hmem W C).2 hC⟩)⟩
  obtain ⟨W, hW, hC⟩ := h.1
  exact ⟨W, hW, (hmem W (kappa k)).1 hC⟩

/-- **The Courant–Fischer min–max principle for the mixed eigenvalues.** Let the energy form `a`
be symmetric on `H¹_Γ(Ω)` and bounded below there, `a(v, v) + ω ‖v‖²_{L²} ≥ 0` for some `ω`,
as under a Gårding inequality, and let `κ₀ ≤ κ₁ ≤ ⋯` be eigenvalues with
eigenfunctions `uⱼ ∈ H¹_Γ(Ω)`, `a(uⱼ, v) = κⱼ ⟪uⱼ, v⟫_{L²}` for every `v ∈ H¹_Γ(Ω)`, whose values
form an orthonormal basis of `L²(Ω)`. Then `κₖ` is the `k`-th mixed eigenvalue `λₖ`. In
particular any two such listings agree. -/
theorem mixedEigenvalue_eq_of_hilbertBasis
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hsymm : ∀ u v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    {omega : ℝ} (hlower : ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      0 ≤ energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
        omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2)
    (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (mu.restrict Omega))) {kappa : ℕ → ℝ}
    (hkappa : Monotone kappa) {u : ℕ → (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule}
    (hvalue : ∀ j, W1p.value (u j : W1p mu Omega 2) = basis j)
    (heq : ∀ (j : ℕ) (v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule),
      energyFormH1 a b c (u j : W1p mu Omega 2) (v : W1p mu Omega 2) =
        kappa j * ⟪W1p.value (u j : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ)
    (k : ℕ) :
    mixedEigenvalue mu Omega Γ a b c k = kappa k :=
  (isLeast_of_hilbertBasis hcoeff hsymm hlower basis hkappa hvalue heq k).csInf_eq

/-- A Gårding inequality `θ ‖v‖²_{H¹} ≤ a(v, v) + ω ‖v‖²_{L²}` bounds the energy form below by
`-ω ‖v‖²_{L²}`. -/
private theorem energyFormH1_add_nonneg_of_garding {theta omega : ℝ} (htheta : 0 < theta)
    (hgarding : ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      theta * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
          omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2)
    (v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule) :
    0 ≤ energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
      omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2 :=
  (mul_nonneg htheta.le (sq_nonneg _)).trans (hgarding v)

/-- **The mixed eigenvalues of a nonnegative form are nonnegative**: if `a(v, v) ≥ 0` for every
`v ∈ H¹_Γ(Ω)`, then `0 ≤ λₖ` for every `k`. Every constant `C` admissible in the min–max
principle is nonnegative, since an admissible subspace contains some `v` with nonzero value in
`L²(Ω)`, and `0 ≤ a(v, v) ≤ C ‖v‖²_{L²(Ω)}`. -/
theorem mixedEigenvalue_nonneg
    (hnonneg : ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      0 ≤ energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2)) (k : ℕ) :
    0 ≤ mixedEigenvalue mu Omega Γ a b c k := by
  refine Real.sInf_nonneg fun C ⟨W, hW, hC⟩ ↦ ?_
  have hne : W.map ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ
      (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule.subtype) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hW
    omega
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hy
  have hpos : 0 < ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2 :=
    pow_pos (norm_pos_iff.2 (by simpa [W1p.valueL_apply] using hy0)) 2
  exact nonneg_of_mul_nonneg_left ((hnonneg v).trans (hC v hv)) hpos

section Spectrum

variable [Nonempty ι]
  (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
  (hrellich : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
  (hΓ : Disjoint Γ Omega)
  (hsymm : ∀ u v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
    energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
      energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
  {theta omega : ℝ} (htheta : 0 < theta)
  (hgarding : ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
    theta * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
      energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
        omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2)
  (hOmega_nonempty : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty)
include hcoeff hrellich hΓ hsymm htheta hgarding hOmega_nonempty

/-- **The mixed eigenvalues with an eigenbasis.** On a nonempty open set with the Rellich property,
for a symmetric energy form satisfying a Gårding inequality on `H¹_Γ(Ω)`, there is an
orthonormal basis `(eₖ)` of `L²(Ω)` such that `eₖ` is the value of some `uₖ ∈ H¹_Γ(Ω)` with
`a(uₖ, v) = λₖ ⟪uₖ, v⟫_{L²}` for every `v ∈ H¹_Γ(Ω)`, where `λₖ` is the min–max eigenvalue
`TauCeti.PDE.mixedEigenvalue`. -/
theorem exists_hilbertBasis_mixedEigenvalue :
    ∃ (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (mu.restrict Omega)))
      (u : ℕ → (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule),
      (∀ k, W1p.value (u k : W1p mu Omega 2) = basis k) ∧
      ∀ (k : ℕ) (v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule),
        energyFormH1 a b c (u k : W1p mu Omega 2) (v : W1p mu Omega 2) =
          mixedEigenvalue mu Omega Γ a b c k *
            ⟪W1p.value (u k : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  obtain ⟨basis, kappa, u, hmono, -, hvalue, heq, -⟩ :=
    exists_hilbertBasis_nat_isMixedEigenvalue_monotone hcoeff hrellich hΓ hsymm htheta hgarding
      hOmega_nonempty
  refine ⟨basis, u, hvalue, fun k v ↦ ?_⟩
  rw [mixedEigenvalue_eq_of_hilbertBasis hcoeff hsymm
    (energyFormH1_add_nonneg_of_garding htheta hgarding) basis hmono hvalue heq k, heq]

/-- **The min–max principle is attained.** On a nonempty open set with the Rellich property, for a
symmetric energy form satisfying a Gårding inequality on `H¹_Γ(Ω)`, `λₖ` is the least
`C` for which some subspace `W` of `H¹_Γ(Ω)`, whose values span a subspace of `L²(Ω)` of dimension
at least `k + 1`, satisfies `a(v, v) ≤ C ‖v‖²_{L²(Ω)}` for every `v ∈ W`. -/
theorem isLeast_mixedEigenvalue (k : ℕ) :
    IsLeast {C : ℝ | ∃ W : Submodule ℝ (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      k + 1 ≤ Module.finrank ℝ
        (W.map ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ
          (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule.subtype)) ∧
        ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
          C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2} (mixedEigenvalue mu Omega Γ a b c k) := by
  obtain ⟨basis, kappa, u, hmono, -, hvalue, heq, -⟩ :=
    exists_hilbertBasis_nat_isMixedEigenvalue_monotone hcoeff hrellich hΓ hsymm htheta hgarding
      hOmega_nonempty
  rw [mixedEigenvalue_eq_of_hilbertBasis hcoeff hsymm
    (energyFormH1_add_nonneg_of_garding htheta hgarding) basis hmono hvalue heq]
  exact isLeast_of_hilbertBasis hcoeff hsymm
    (energyFormH1_add_nonneg_of_garding htheta hgarding) basis hmono hvalue heq k

/-- Under the hypotheses of `TauCeti.PDE.exists_hilbertBasis_nat_isMixedEigenvalue_monotone`, the
mixed eigenvalues `λₖ` are that nondecreasing listing of the mixed spectrum. -/
private theorem mixedEigenvalue_properties :
    Monotone (mixedEigenvalue mu Omega Γ a b c) ∧
      Tendsto (mixedEigenvalue mu Omega Γ a b c) atTop atTop ∧
      ∀ kappa' : ℝ, IsMixedEigenvalue mu Omega Γ a b c kappa' ↔
        ∃ k, mixedEigenvalue mu Omega Γ a b c k = kappa' := by
  obtain ⟨basis, kappa, u, hmono, htendsto, hvalue, heq, hiff⟩ :=
    exists_hilbertBasis_nat_isMixedEigenvalue_monotone hcoeff hrellich hΓ hsymm htheta hgarding
      hOmega_nonempty
  obtain rfl : mixedEigenvalue mu Omega Γ a b c = kappa :=
    funext <| mixedEigenvalue_eq_of_hilbertBasis hcoeff hsymm
      (energyFormH1_add_nonneg_of_garding htheta hgarding) basis hmono hvalue heq
  exact ⟨hmono, htendsto, hiff⟩

/-- The mixed eigenvalues are nondecreasing: `λ₀ ≤ λ₁ ≤ ⋯`. -/
theorem monotone_mixedEigenvalue : Monotone (mixedEigenvalue mu Omega Γ a b c) :=
  (mixedEigenvalue_properties hcoeff hrellich hΓ hsymm htheta hgarding
    hOmega_nonempty).1

/-- The mixed eigenvalues tend to infinity. -/
theorem tendsto_mixedEigenvalue_atTop :
    Tendsto (mixedEigenvalue mu Omega Γ a b c) atTop atTop :=
  (mixedEigenvalue_properties hcoeff hrellich hΓ hsymm htheta hgarding
    hOmega_nonempty).2.1

/-- The mixed eigenvalues `λₖ` are exactly the mixed spectrum. -/
theorem isMixedEigenvalue_iff_exists_mixedEigenvalue_eq (kappa' : ℝ) :
    IsMixedEigenvalue mu Omega Γ a b c kappa' ↔
      ∃ k, mixedEigenvalue mu Omega Γ a b c k = kappa' :=
  (mixedEigenvalue_properties hcoeff hrellich hΓ hsymm htheta hgarding
    hOmega_nonempty).2.2 kappa'

end Spectrum

/-! ### Monotonicity in the boundary part -/

/-- The inclusion `H¹_{Γ'}(Ω) → H¹_Γ(Ω)` for `Γ ⊆ Γ'` turns a subspace admissible in the min–max
principle for `Γ'` into one admissible for `Γ` with the same constant. -/
private theorem mem_setOf_mixedEigenvalue_of_subset (hΓΓ' : Γ ⊆ Γ') {k : ℕ} {C : ℝ}
    (h : ∃ W : Submodule ℝ (w1pVanishingOnSubmodule mu Omega 2 Γ').toSubmodule,
      k + 1 ≤ Module.finrank ℝ
        (W.map ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ
          (w1pVanishingOnSubmodule mu Omega 2 Γ').toSubmodule.subtype)) ∧
        ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
          C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2) :
    ∃ W : Submodule ℝ (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      k + 1 ≤ Module.finrank ℝ
        (W.map ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ
          (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule.subtype)) ∧
        ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
          C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2 := by
  obtain ⟨W, hW, hC⟩ := h
  let i := Submodule.inclusion (p := (w1pVanishingOnSubmodule mu Omega 2 Γ').toSubmodule)
    (p' := (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule)
    (w1pVanishingOnSubmodule_antitone hΓΓ')
  refine ⟨W.map i, ?_, ?_⟩
  · rwa [← Submodule.map_comp, LinearMap.comp_assoc, Submodule.subtype_comp_inclusion]
  · rintro _ ⟨v, hv, rfl⟩
    exact hC v hv

/-- **The mixed eigenvalues grow with the Dirichlet part.** For `Γ ⊆ Γ'`, both missing `Ω`,
`λₖ(Γ) ≤ λₖ(Γ')` for every `k`, under the hypotheses of
`TauCeti.PDE.isLeast_mixedEigenvalue` for `Γ`. Indeed `H¹_{Γ'}(Ω) ⊆ H¹_Γ(Ω)`, so the min–max
principle for `Γ` runs over more subspaces. -/
theorem mixedEigenvalue_le_of_subset [Nonempty ι] (hΓΓ' : Γ ⊆ Γ')
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hrellich : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hΓ' : Disjoint Γ' Omega)
    (hsymm : ∀ u v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    {theta omega : ℝ} (htheta : 0 < theta)
    (hgarding : ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      theta * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
          omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2)
    (hOmega_nonempty : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) (k : ℕ) :
    mixedEigenvalue mu Omega Γ a b c k ≤ mixedEigenvalue mu Omega Γ' a b c k := by
  have hle := w1pVanishingOnSubmodule_antitone (mu := mu) (Omega := Omega) (p := 2) hΓΓ'
  -- The hypotheses pass from `H¹_Γ(Ω)` to its subspace `H¹_{Γ'}(Ω)`.
  let i : (w1pVanishingOnSubmodule mu Omega 2 Γ').toSubmodule →
      (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule := fun v ↦ ⟨v, hle v.property⟩
  exact csInf_le_csInf
    (isLeast_mixedEigenvalue hcoeff hrellich (hΓ'.mono_left hΓΓ') hsymm htheta hgarding
      hOmega_nonempty k).bddBelow
    (isLeast_mixedEigenvalue hcoeff hrellich hΓ' (fun u v ↦ hsymm (i u) (i v))
      htheta (fun v ↦ hgarding (i v)) hOmega_nonempty k).nonempty
    fun _ hC ↦ mem_setOf_mixedEigenvalue_of_subset hΓΓ' hC

/-! ### The mixed eigenvalues of `-Δ` -/

section Laplacian

variable [DecidableEq ι]

/-- The energy form of `-Δ` is symmetric. -/
private theorem energyFormH1_laplacian_comm (u v : W1p mu Omega 2) :
    energyFormH1 (fun _ ↦ 1) 0 0 u v = energyFormH1 (fun _ ↦ 1) 0 0 v u :=
  energyFormH1_comm_of_isSymm_ae (ae_of_all _ fun _ ↦ Matrix.isSymm_one) _ _

/-- The energy of `-Δ` is `‖∇v‖²_{L²}`, so it is nonnegative. -/
private theorem energyFormH1_laplacian_self_nonneg (v : W1p mu Omega 2) :
    0 ≤ energyFormH1 (fun _ ↦ 1) 0 0 v v := by
  rw [energyFormH1_one_zero_zero_eq_inner, real_inner_self_eq_norm_sq]
  positivity

/-- **The Gårding inequality for `-Δ`** with `θ = ω = 1`: `‖v‖²_{H¹} = ∫ |∇v|² + ‖v‖²_{L²}`. -/
private theorem norm_sq_le_energyFormH1_laplacian_add (v : W1p mu Omega 2) :
    1 * ‖v‖ ^ 2 ≤ energyFormH1 (fun _ ↦ 1) 0 0 v v + 1 * ‖W1p.value v‖ ^ 2 := by
  rw [energyFormH1_one_zero_zero_eq_inner, real_inner_self_eq_norm_sq,
    W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq]
  linarith

variable [Nonempty ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (hΩ : (Omega : Set (EuclideanSpace ℝ ι)).IsLipschitzDomain E)
  (hb : IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
  (hOmega_nonempty : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty)
include hΩ hb hOmega_nonempty

/-- **The mixed eigenvalues of `-Δ` grow with the Dirichlet part**: on a nonempty bounded
Lipschitz domain `Ω`, for `Γ ⊆ Γ'`, both missing `Ω`, `λₖ(Γ) ≤ λₖ(Γ')` for every `k`. -/
theorem mixedEigenvalue_laplacian_le_of_subset (hΓΓ' : Γ ⊆ Γ') (hΓ' : Disjoint Γ' Omega)
    (k : ℕ) :
    mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0 k ≤ mixedEigenvalue mu Omega Γ' (fun _ ↦ 1) 0 0 k :=
  mixedEigenvalue_le_of_subset hΓΓ' (memLp_energyIntegrand_const_zero_zero 1)
    (W1p.isCompactOperator_valueL_of_isLipschitzDomain hΩ hb) hΓ'
    (fun _ _ ↦ energyFormH1_laplacian_comm _ _) one_pos
    (fun _ ↦ norm_sq_le_energyFormH1_laplacian_add _) hOmega_nonempty k

/-- **The mixed eigenvalues of `-Δ` lie below the Dirichlet ones**: on a nonempty bounded
Lipschitz domain `Ω` and for a boundary part `Γ ⊆ ∂Ω`, `λₖ(Γ) ≤ λₖ(∂Ω)`, the `k`-th Dirichlet
eigenvalue of `-Δ`. -/
theorem mixedEigenvalue_laplacian_le_dirichletEigenvalue
    (hΓ : Γ ⊆ frontier (Omega : Set (EuclideanSpace ℝ ι))) (k : ℕ) :
    mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0 k ≤
      dirichletEigenvalue mu Omega (fun _ ↦ 1) 0 0 k := by
  rw [← mixedEigenvalue_frontier]
  exact mixedEigenvalue_laplacian_le_of_subset hΩ hb hOmega_nonempty hΓ
    (disjoint_frontier_iff_isOpen.2 Omega.isOpen) k

variable (hΓ : Disjoint Γ Omega)
include hΓ

/-- **The mixed eigenbasis of `-Δ`.** On a nonempty bounded Lipschitz domain `Ω ⊆ ℝⁿ` and for `Γ`
missing `Ω`, for instance `Γ ⊆ ∂Ω`, there is an orthonormal basis `(eₖ)` of `L²(Ω)` such that `eₖ`
is the value of some `uₖ ∈ H¹_Γ(Ω)` with
`∫_Ω ∇uₖ · ∇v = λₖ ∫_Ω uₖ v` for every `v ∈ H¹_Γ(Ω)`, where `λₖ` is the min–max eigenvalue
`TauCeti.PDE.mixedEigenvalue`. -/
theorem exists_hilbertBasis_mixedEigenvalue_laplacian :
    ∃ (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (mu.restrict Omega)))
      (u : ℕ → (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule),
      (∀ k, W1p.value (u k : W1p mu Omega 2) = basis k) ∧
      ∀ (k : ℕ) (v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule),
        energyFormH1 (fun _ ↦ 1) 0 0 (u k : W1p mu Omega 2) (v : W1p mu Omega 2) =
          mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0 k *
            ⟪W1p.value (u k : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ :=
  exists_hilbertBasis_mixedEigenvalue (memLp_energyIntegrand_const_zero_zero 1)
    (W1p.isCompactOperator_valueL_of_isLipschitzDomain hΩ hb) hΓ
    (fun _ _ ↦ energyFormH1_laplacian_comm _ _) one_pos
    (fun _ ↦ norm_sq_le_energyFormH1_laplacian_add _) hOmega_nonempty

/-- **The min–max principle for `-Δ` is attained**: `λₖ` is the least `C` for which some subspace
`W` of `H¹_Γ(Ω)`, whose values span a subspace of `L²(Ω)` of dimension at least `k + 1`, satisfies
`∫_Ω |∇v|² ≤ C ∫_Ω v²` for every `v ∈ W`. For `k = 0` this says that `λ₀` is the least Rayleigh
quotient over nonzero `v ∈ H¹_Γ(Ω)`. -/
theorem isLeast_mixedEigenvalue_laplacian (k : ℕ) :
    IsLeast {C : ℝ | ∃ W : Submodule ℝ (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      k + 1 ≤ Module.finrank ℝ
        (W.map ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ
          (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule.subtype)) ∧
        ∀ v ∈ W, energyFormH1 (fun _ ↦ 1) 0 0 (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
          C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2}
      (mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0 k) :=
  isLeast_mixedEigenvalue (memLp_energyIntegrand_const_zero_zero 1)
    (W1p.isCompactOperator_valueL_of_isLipschitzDomain hΩ hb) hΓ
    (fun _ _ ↦ energyFormH1_laplacian_comm _ _) one_pos
    (fun _ ↦ norm_sq_le_energyFormH1_laplacian_add _) hOmega_nonempty k

/-- **The mixed spectrum of `-Δ`.** On a nonempty bounded Lipschitz domain and for `Γ` missing
`Ω`, the mixed eigenvalues of `-Δ` satisfy `0 ≤ λ₀ ≤ λ₁ ≤ ⋯ → ∞`, and a real number is a
mixed eigenvalue of `-Δ` exactly when it is some `λₖ`. -/
theorem mixedEigenvalue_laplacian_spectrum :
    0 ≤ mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0 0 ∧
      Monotone (mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0) ∧
      Tendsto (mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0) atTop atTop ∧
      ∀ kappa : ℝ, IsMixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0 kappa ↔
        ∃ k, mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0 k = kappa := by
  have hcoeff := memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
    (1 : Matrix ι ι ℝ)
  have hsymm (u v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule) :=
    energyFormH1_laplacian_comm (u : W1p mu Omega 2) v
  have hnonneg (v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule) :=
    energyFormH1_laplacian_self_nonneg (v : W1p mu Omega 2)
  have hgarding (v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule) :=
    norm_sq_le_energyFormH1_laplacian_add (v : W1p mu Omega 2)
  have hrellich := W1p.isCompactOperator_valueL_of_isLipschitzDomain (mu := mu) (p := 2) hΩ hb
  exact ⟨mixedEigenvalue_nonneg hnonneg 0,
    monotone_mixedEigenvalue hcoeff hrellich hΓ hsymm one_pos hgarding hOmega_nonempty,
    tendsto_mixedEigenvalue_atTop hcoeff hrellich hΓ hsymm one_pos hgarding
      hOmega_nonempty,
    isMixedEigenvalue_iff_exists_mixedEigenvalue_eq hcoeff hrellich hΓ hsymm one_pos
      hgarding hOmega_nonempty⟩

end Laplacian

end PDE

end TauCeti

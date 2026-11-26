/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Variational.Eigenbasis
public import TauCeti.Analysis.InnerProductSpace.Variational.MinMax
public import TauCeti.Analysis.PDE.MixedProblem
public import TauCeti.Analysis.PDE.Spectrum.MinMax
public import TauCeti.MeasureTheory.Function.L2Space

/-!
# Mixed and Neumann eigenvalues

Let `Ω ⊆ ℝⁿ` be open, `Γ` a set disjoint from `Ω`, typically a part of the boundary, and `a` the
energy form of a divergence-form operator `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u`. A real `κ` is a
**mixed eigenvalue** (`TauCeti.PDE.IsMixedEigenvalue`) when some nonzero `u ∈ H¹_Γ(Ω)` satisfies

`a(u, v) = κ ∫_Ω u v` for every `v ∈ H¹_Γ(Ω)`,

where `H¹_Γ(Ω)` is the space `TauCeti.W1pVanishingOn` of Sobolev functions vanishing on `Γ`. This
is the weak form of `L u = κ u` with the Dirichlet condition `u = 0` on `Γ` and the natural
(conormal) boundary condition on the rest of the frontier. For `Γ = frontier Ω` it is the
Dirichlet eigenvalue problem (`TauCeti.PDE.isMixedEigenvalue_frontier_iff`), and for `Γ = ∅` the
weak Neumann eigenvalue problem, tested against all of `H¹(Ω)`.

## The min–max eigenvalues

The `k`-th mixed eigenvalue `λₖ`, counted from `k = 0` with multiplicity, is defined by the
Courant–Fischer min–max principle (`TauCeti.PDE.mixedEigenvalue`): the infimum of the constants
`C` for which some subspace `W` of `H¹_Γ(Ω)`, whose values span a subspace of `L²(Ω)` of
dimension at least `k + 1`, satisfies `a(v, v) ≤ C ‖v‖²_{L²(Ω)}` for every `v ∈ W`. At
`Γ = frontier Ω` it is the Dirichlet eigenvalue `TauCeti.PDE.dirichletEigenvalue`
(`TauCeti.PDE.mixedEigenvalue_frontier`).

## The eigenbasis

Unlike the Dirichlet form, the Neumann form `∫ ∇u · ∇v` is not coercive: the constants lie in its
kernel. What holds for every `Γ` is **Gårding's inequality** `C₀ ‖w‖²_{H¹} ≤ a(w, w) + β ‖w‖²_{L²}`
on `H¹_Γ(Ω)` with `C₀ > 0`, for instance with `C₀ = β = 1` for `-Δ`. Under it, for a symmetric
form, a nonempty `Ω` and a compact value map `H¹(Ω) → L²(Ω)` (Rellich's theorem, which holds on a
bounded Lipschitz domain by
`TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomainWith_of_affineIsometryEquiv`), the
abstract theorem `TauCeti.exists_hilbertBasis_nat_monotone_of_garding` applies with `V = H¹_Γ(Ω)`
and `J` its value map. `J` has dense range because `H¹_Γ(Ω)` contains `H¹₀(Ω)` when `Γ` misses
`Ω`. The result, `TauCeti.PDE.exists_hilbertBasis_mixedEigenvalue`, is an orthonormal basis of
`L²(Ω)` of values of eigenfunctions with eigenvalues `λ₀ ≤ λ₁ ≤ ⋯ → ∞`, and these are exactly the
mixed eigenvalues (`TauCeti.PDE.isMixedEigenvalue_iff_exists_mixedEigenvalue_eq`); the infimum
defining `λₖ` is attained (`TauCeti.PDE.isLeast_mixedEigenvalue`). Since `H¹_{Γ'}(Ω) ⊆ H¹_Γ(Ω)`
for `Γ ⊆ Γ'`, min–max gives `λₖ(Γ) ≤ λₖ(Γ')` (`TauCeti.PDE.mixedEigenvalue_le_of_subset`): more
Dirichlet boundary raises every eigenvalue.

For `-Δ` the hypotheses reduce to the compactness of the value map, a nonempty `Ω` and `Γ ∩ Ω = ∅`
(`TauCeti.PDE.exists_hilbertBasis_mixedEigenvalue_laplacian`,
`TauCeti.PDE.isLeast_mixedEigenvalue_laplacian`, `TauCeti.PDE.mixedEigenvalue_laplacian_spectrum`
and `TauCeti.PDE.mixedEigenvalue_laplacian_le_of_subset`). For instance, on `(0, 1)` the Neumann
eigenvalues `m²π²` of `cos(mπx)`, the mixed eigenvalues `(m + ½)²π²` of `sin((m + ½)πx)` for
`Γ = {0}` and the Dirichlet eigenvalues `(m + 1)²π²` increase with `Γ`.

## Main declarations

* `TauCeti.PDE.IsMixedEigenvalue` and `TauCeti.PDE.isMixedEigenvalue_frontier_iff`.
* `TauCeti.PDE.mixedEigenvalue`, `TauCeti.PDE.mixedEigenvalue_frontier`,
  `TauCeti.PDE.mixedEigenvalue_eq_of_hilbertBasis` and `TauCeti.PDE.mixedEigenvalue_nonneg`.
* `TauCeti.PDE.exists_hilbertBasis_mixedEigenvalue`, `TauCeti.PDE.isLeast_mixedEigenvalue`,
  `TauCeti.PDE.monotone_mixedEigenvalue`, `TauCeti.PDE.tendsto_mixedEigenvalue_atTop` and
  `TauCeti.PDE.isMixedEigenvalue_iff_exists_mixedEigenvalue_eq`: the mixed spectrum of a symmetric
  Gårding form.
* `TauCeti.PDE.mixedEigenvalue_le_of_subset`: monotonicity in the Dirichlet part.
* `TauCeti.PDE.exists_hilbertBasis_mixedEigenvalue_laplacian`,
  `TauCeti.PDE.isLeast_mixedEigenvalue_laplacian`,
  `TauCeti.PDE.mixedEigenvalue_laplacian_spectrum` and
  `TauCeti.PDE.mixedEigenvalue_laplacian_le_of_subset`: the same for `-Δ`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 9.31 (the Dirichlet eigenbasis, whose proof carries over to `H¹_Γ(Ω)`).
* R. Courant and D. Hilbert, *Methods of Mathematical Physics*, Vol. I, Chapter VI, §1–§2.
* S. Bauer, D. Pauly, M. Schomburg, *The Maxwell compactness property in bounded weak Lipschitz
  domains with mixed boundary conditions*, SIAM J. Math. Anal. **48** (2016) (the spaces
  `H¹_Γ(Ω)`).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Filter MeasureTheory Set TopologicalSpace
open scoped InnerProductSpace

section Domain

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {Γ Γ' : Set (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ} {C₀ β : ℝ}

attribute [local instance] instSeminormedAddCommGroupW1p instNormedSpaceW1p
  W1pVanishingOn.instNormedAddCommGroup W1pVanishingOn.instInnerProductSpace

/-- **A mixed eigenvalue** of the divergence-form operator with coefficients `a, b, c` on `Ω`,
with Dirichlet part `Γ`: a real `κ` for which some nonzero `u ∈ H¹_Γ(Ω)` satisfies
`a(u, v) = κ ∫_Ω u v` for every `v ∈ H¹_Γ(Ω)`.

For `Γ = frontier Ω` these are the Dirichlet eigenvalues
(`TauCeti.PDE.isMixedEigenvalue_frontier_iff`); for `Γ = ∅` the test space is all of `H¹(Ω)`,
which imposes the natural boundary condition, and these are the weak Neumann eigenvalues. -/
def IsMixedEigenvalue (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
    (Omega : Opens (EuclideanSpace ℝ ι)) (Γ : Set (EuclideanSpace ℝ ι))
    (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ) (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (c : EuclideanSpace ℝ ι → ℝ) (kappa : ℝ) : Prop :=
  ∃ u : W1pVanishingOn mu Omega 2 Γ, u ≠ 0 ∧ ∀ v : W1pVanishingOn mu Omega 2 Γ,
    energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
      kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ

/-- Unfolding `TauCeti.PDE.IsMixedEigenvalue`: a nonzero `u ∈ H¹_Γ(Ω)` with
`a(u, v) = κ ⟪u, v⟫_{L²(Ω)}` for every `v ∈ H¹_Γ(Ω)`. -/
theorem isMixedEigenvalue_iff (kappa : ℝ) :
    IsMixedEigenvalue mu Omega Γ a b c kappa ↔
      ∃ u : W1pVanishingOn mu Omega 2 Γ, u ≠ 0 ∧ ∀ v : W1pVanishingOn mu Omega 2 Γ,
        energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
          kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ :=
  Iff.rfl

/-- **The mixed eigenvalues at the whole frontier are the Dirichlet eigenvalues**, since
`H¹_Γ(Ω) = H¹₀(Ω)` for `Γ = frontier Ω` (`TauCeti.w1pVanishingOnSubmodule_frontier`). -/
theorem isMixedEigenvalue_frontier_iff (kappa : ℝ) :
    IsMixedEigenvalue mu Omega (frontier (Omega : Set (EuclideanSpace ℝ ι))) a b c kappa ↔
      IsDirichletEigenvalue mu Omega a b c kappa := by
  have hS (w : W1p mu Omega 2) :
      w ∈ W1pVanishingOn mu Omega 2 (frontier (Omega : Set (EuclideanSpace ℝ ι))) ↔
        w ∈ W1p0 mu Omega 2 :=
    SetLike.ext_iff.1 (congrArg ClosedSubmodule.toSubmodule w1pVanishingOnSubmodule_frontier) w
  rw [isDirichletEigenvalue_iff]
  constructor
  · rintro ⟨u, hu, heq⟩
    refine ⟨⟨u, (hS u).1 u.property⟩, fun h0 ↦ hu ?_, fun v ↦ heq ⟨v, (hS v).2 v.property⟩⟩
    rw [← Submodule.coe_eq_zero]
    exact congrArg Subtype.val h0
  · rintro ⟨u, hu, heq⟩
    refine ⟨⟨u, (hS u).2 u.property⟩, fun h0 ↦ hu ?_, fun v ↦ heq ⟨v, (hS v).1 v.property⟩⟩
    rw [← Submodule.coe_eq_zero]
    exact congrArg Subtype.val h0

variable (mu Omega Γ a b c) in
/-- **The `k`-th mixed eigenvalue** of the divergence-form operator with coefficients `a, b, c`
on `Ω`, with Dirichlet part `Γ`, counted from `k = 0` with multiplicity, by the Courant–Fischer
min–max principle: the infimum of the constants `C` such that `a(v, v) ≤ C ‖v‖²_{L²(Ω)}` for
every `v` in some subspace `W` of `H¹_Γ(Ω)` whose values span a subspace of `L²(Ω)` of dimension
at least `k + 1`.

For a symmetric Gårding form on a nonempty domain with compact value map the infimum is attained
and these are the mixed eigenvalues in nondecreasing order
(`TauCeti.PDE.exists_hilbertBasis_mixedEigenvalue`); otherwise the infimum may be over an empty
or unbounded set, and the value carries no information. -/
def mixedEigenvalue (k : ℕ) : ℝ :=
  sInf {C : ℝ | ∃ W : Submodule ℝ (W1pVanishingOn mu Omega 2 Γ),
    k + 1 ≤ Module.finrank ℝ (W.map ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap
      ∘ₗ (W1pVanishingOn mu Omega 2 Γ).subtype)) ∧
      ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
        C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2}

/-- The definition of the `k`-th mixed eigenvalue as an infimum. -/
theorem mixedEigenvalue_def (k : ℕ) :
    mixedEigenvalue mu Omega Γ a b c k =
      sInf {C : ℝ | ∃ W : Submodule ℝ (W1pVanishingOn mu Omega 2 Γ),
        k + 1 ≤ Module.finrank ℝ (W.map ((W1p.valueL (mu := mu) (Omega := Omega)
          (p := 2)).toLinearMap ∘ₗ (W1pVanishingOn mu Omega 2 Γ).subtype)) ∧
          ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
            C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2} :=
  (rfl)

/-- The min–max value over the closed subspace `S` of `H¹(Ω)`; `TauCeti.PDE.mixedEigenvalue` and
`TauCeti.PDE.dirichletEigenvalue` are its values at `H¹_Γ(Ω)` and at `H¹₀(Ω)`. -/
private def minMaxValue (S : ClosedSubmodule ℝ (W1p mu Omega 2))
    (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ) (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (c : EuclideanSpace ℝ ι → ℝ) (k : ℕ) : ℝ :=
  sInf {C : ℝ | ∃ W : Submodule ℝ S.toSubmodule,
    k + 1 ≤ Module.finrank ℝ (W.map ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap
      ∘ₗ S.toSubmodule.subtype)) ∧
      ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
        C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2}

/-- **The mixed eigenvalues at the whole frontier are the Dirichlet eigenvalues**, as min–max
values. -/
theorem mixedEigenvalue_frontier :
    mixedEigenvalue mu Omega (frontier (Omega : Set (EuclideanSpace ℝ ι))) a b c =
      dirichletEigenvalue mu Omega a b c := by
  funext k
  have hvalue : (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap =
      (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ (W1p0 mu Omega 2).subtype :=
    LinearMap.ext fun u ↦ by simp
  rw [dirichletEigenvalue_def, hvalue]
  change minMaxValue (w1pVanishingOnSubmodule mu Omega 2 (frontier (Omega : Set _))) a b c k =
    minMaxValue (w1p0Submodule mu Omega 2) a b c k
  rw [w1pVanishingOnSubmodule_frontier]

/-- The value map of `H¹_Γ(Ω)`, as a continuous linear map into `L²(Ω)`. -/
private abbrev valueVanishingOnL (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
    (Omega : Opens (EuclideanSpace ℝ ι)) (Γ : Set (EuclideanSpace ℝ ι)) :
    W1pVanishingOn mu Omega 2 Γ →L[ℝ] Lp ℝ 2 (mu.restrict Omega) :=
  (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).comp (W1pVanishingOn mu Omega 2 Γ).subtypeL

/-- The min–max principle `TauCeti.isLeast_minMax_of_hilbertBasis_of_neg_mul_le` for the energy
form on `H¹_Γ(Ω)` and the value map of `H¹_Γ(Ω)`. -/
private theorem isLeast_of_hilbertBasis
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hsymm : ∀ u v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (hlower : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      -β * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2))
    (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (mu.restrict Omega))) {kappa : ℕ → ℝ}
    (hkappa : Monotone kappa) {u : ℕ → W1pVanishingOn mu Omega 2 Γ}
    (hvalue : ∀ j, W1p.value (u j : W1p mu Omega 2) = basis j)
    (heq : ∀ (j : ℕ) (v : W1pVanishingOn mu Omega 2 Γ),
      energyFormH1 a b c (u j : W1p mu Omega 2) (v : W1p mu Omega 2) =
        kappa j * ⟪W1p.value (u j : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ)
    (k : ℕ) :
    IsLeast {C : ℝ | ∃ W : Submodule ℝ (W1pVanishingOn mu Omega 2 Γ),
      k + 1 ≤ Module.finrank ℝ (W.map ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap
        ∘ₗ (W1pVanishingOn mu Omega 2 Γ).subtype)) ∧
        ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
          C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2} (kappa k) := by
  simpa only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, energyFormH1LVanishingOn_apply,
    LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe, Submodule.coe_subtype,
    W1p.valueL_apply] using
    isLeast_minMax_of_hilbertBasis_of_neg_mul_le
      (B := (energyFormH1LVanishingOn hcoeff Γ).toLinearMap₁₂)
      (J := (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ
        (W1pVanishingOn mu Omega 2 Γ).subtype)
      (by simpa only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
        energyFormH1LVanishingOn_apply] using hsymm)
      (by simpa only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
        energyFormH1LVanishingOn_apply, LinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.coe_coe, Submodule.coe_subtype, W1p.valueL_apply] using hlower)
      basis hkappa
      (by simpa only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
        Submodule.coe_subtype, W1p.valueL_apply] using hvalue)
      (by simpa only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
        energyFormH1LVanishingOn_apply, LinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.coe_coe, Submodule.coe_subtype, W1p.valueL_apply] using heq) k

/-- **The Courant–Fischer min–max principle for the mixed eigenvalues.** Let the energy form `a`
be symmetric on `H¹_Γ(Ω)` and bounded below there by `-β ‖v‖²_{L²}`, and let `κ₀ ≤ κ₁ ≤ ⋯` be
eigenvalues with eigenfunctions `uⱼ ∈ H¹_Γ(Ω)`, `a(uⱼ, v) = κⱼ ⟪uⱼ, v⟫_{L²}` for every
`v ∈ H¹_Γ(Ω)`, whose values form an orthonormal basis of `L²(Ω)`. Then `κₖ` is the `k`-th mixed
eigenvalue `λₖ`. In particular any two such listings agree. -/
theorem mixedEigenvalue_eq_of_hilbertBasis
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hsymm : ∀ u v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (hlower : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      -β * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2))
    (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (mu.restrict Omega))) {kappa : ℕ → ℝ}
    (hkappa : Monotone kappa) {u : ℕ → W1pVanishingOn mu Omega 2 Γ}
    (hvalue : ∀ j, W1p.value (u j : W1p mu Omega 2) = basis j)
    (heq : ∀ (j : ℕ) (v : W1pVanishingOn mu Omega 2 Γ),
      energyFormH1 a b c (u j : W1p mu Omega 2) (v : W1p mu Omega 2) =
        kappa j * ⟪W1p.value (u j : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ)
    (k : ℕ) :
    mixedEigenvalue mu Omega Γ a b c k = kappa k :=
  (isLeast_of_hilbertBasis hcoeff hsymm hlower basis hkappa hvalue heq k).csInf_eq

/-- For a form that is nonnegative on `H¹_Γ(Ω)`, such as the energy form of `-Δ`, the mixed
eigenvalues are nonnegative: every constant admissible in the min–max principle is. -/
theorem mixedEigenvalue_nonneg
    (hnonneg : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      0 ≤ energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2)) (k : ℕ) :
    0 ≤ mixedEigenvalue mu Omega Γ a b c k := by
  refine Real.sInf_nonneg fun C ⟨W, hW, hC⟩ ↦ ?_
  -- Some `v ∈ W` has a nonzero value, since the values of `W` span a nonzero subspace.
  have hne : W.map ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ
      (W1pVanishingOn mu Omega 2 Γ).subtype) ≠ ⊥ := fun h ↦ by
    rw [h, finrank_bot] at hW
    omega
  obtain ⟨_, ⟨v, hv, rfl⟩, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hpos : 0 < ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2 := by
    simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
      Submodule.coe_subtype, W1p.valueL_apply] at hv0
    positivity
  exact le_of_mul_le_mul_right (by simpa using (hnonneg v).trans (hC v hv)) hpos

section Garding

variable [Nonempty ι]
  (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
  (hJ : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
  (hΓ : Disjoint Γ Omega) (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty)
  (hsymm : ∀ u v : W1pVanishingOn mu Omega 2 Γ,
    energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
      energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
  (hC₀ : 0 < C₀)
  (hgarding : ∀ w : W1pVanishingOn mu Omega 2 Γ,
    C₀ * ‖(w : W1p mu Omega 2)‖ ^ 2 ≤
      energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2) +
        β * ‖W1p.value (w : W1p mu Omega 2)‖ ^ 2)
include hcoeff hJ hΓ hOmega hsymm hC₀ hgarding

/-- The eigenbasis of `TauCeti.exists_hilbertBasis_nat_monotone_of_garding` for the energy form
on `H¹_Γ(Ω)`, whose eigenvalues are the min–max values `λₖ`. -/
private theorem exists_hilbertBasis_mixedEigenvalue_properties :
    ∃ (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (mu.restrict Omega)))
      (u : ℕ → W1pVanishingOn mu Omega 2 Γ),
      Monotone (mixedEigenvalue mu Omega Γ a b c) ∧
      Tendsto (mixedEigenvalue mu Omega Γ a b c) atTop atTop ∧
      (∀ k, W1p.value (u k : W1p mu Omega 2) = basis k) ∧
      (∀ (k : ℕ) (v : W1pVanishingOn mu Omega 2 Γ),
        energyFormH1 a b c (u k : W1p mu Omega 2) (v : W1p mu Omega 2) =
          mixedEigenvalue mu Omega Γ a b c k *
            ⟪W1p.value (u k : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ) ∧
      (∀ k, IsLeast {C : ℝ | ∃ W : Submodule ℝ (W1pVanishingOn mu Omega 2 Γ),
        k + 1 ≤ Module.finrank ℝ (W.map ((W1p.valueL (mu := mu) (Omega := Omega)
          (p := 2)).toLinearMap ∘ₗ (W1pVanishingOn mu Omega 2 Γ).subtype)) ∧
          ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
            C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2} (mixedEigenvalue mu Omega Γ a b c k)) ∧
      ∀ kappa' : ℝ, IsMixedEigenvalue mu Omega Γ a b c kappa' ↔
        ∃ k, mixedEigenvalue mu Omega Γ a b c k = kappa' := by
  -- The value map of `H¹_Γ(Ω)` is compact, and has dense range since `H¹₀(Ω) ⊆ H¹_Γ(Ω)`.
  have hJc : IsCompactOperator (valueVanishingOnL mu Omega Γ) := hJ.comp_clm _
  have hJd : DenseRange (valueVanishingOnL mu Omega Γ) := by
    refine Dense.mono ?_ W1p0.denseRange_valueL_two
    rintro _ ⟨u, rfl⟩
    exact ⟨⟨u, w1p0Submodule_le_w1pVanishingOnSubmodule hΓ u.property⟩, by simp⟩
  have hH : ¬ FiniteDimensional ℝ (Lp ℝ 2 (mu.restrict Omega)) :=
    L2.not_finiteDimensional_restrict_of_isOpen mu Omega.isOpen hOmega
  obtain ⟨basis, kappa, u, hmono, htendsto, hvalue, heq, hiff⟩ :=
    exists_hilbertBasis_nat_monotone_of_garding (Q := energyFormH1LVanishingOn hcoeff Γ) hJc hJd
      hH (fun u v ↦ by simpa only [energyFormH1LVanishingOn_apply] using hsymm u v) hC₀
      (fun w ↦ by
        rw [energyFormH1LVanishingOn_apply, ContinuousLinearMap.comp_apply,
          Submodule.subtypeL_apply, W1p.valueL_apply]
        exact hgarding w)
  simp only [energyFormH1LVanishingOn_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, W1p.valueL_apply] at hvalue heq hiff
  have hlower (v : W1pVanishingOn mu Omega 2 Γ) :
      -β * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) := by
    nlinarith [hgarding v, norm_nonneg (v : W1p mu Omega 2)]
  obtain rfl : mixedEigenvalue mu Omega Γ a b c = kappa :=
    funext <| mixedEigenvalue_eq_of_hilbertBasis hcoeff hsymm hlower basis hmono hvalue heq
  exact ⟨basis, u, hmono, htendsto, hvalue, heq,
    isLeast_of_hilbertBasis hcoeff hsymm hlower basis hmono hvalue heq, hiff⟩

/-- **The mixed eigenbasis.** Let the energy form `a` be symmetric on `H¹_Γ(Ω)` and satisfy
Gårding's inequality `C₀ ‖w‖²_{H¹} ≤ a(w, w) + β ‖w‖²_{L²}` there, with `C₀ > 0`, let `Ω` be
nonempty with compact value map `H¹(Ω) → L²(Ω)`, and let `Γ` miss `Ω`. Then there is an
orthonormal basis `(eₖ)` of `L²(Ω)` such that `eₖ` is the value of some `uₖ ∈ H¹_Γ(Ω)` with
`a(uₖ, v) = λₖ ⟪uₖ, v⟫_{L²}` for every `v ∈ H¹_Γ(Ω)`, where `λₖ` is the min–max eigenvalue
`TauCeti.PDE.mixedEigenvalue`. -/
theorem exists_hilbertBasis_mixedEigenvalue :
    ∃ (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (mu.restrict Omega)))
      (u : ℕ → W1pVanishingOn mu Omega 2 Γ),
      (∀ k, W1p.value (u k : W1p mu Omega 2) = basis k) ∧
      ∀ (k : ℕ) (v : W1pVanishingOn mu Omega 2 Γ),
        energyFormH1 a b c (u k : W1p mu Omega 2) (v : W1p mu Omega 2) =
          mixedEigenvalue mu Omega Γ a b c k *
            ⟪W1p.value (u k : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  obtain ⟨basis, u, -, -, hvalue, heq, -⟩ :=
    exists_hilbertBasis_mixedEigenvalue_properties hcoeff hJ hΓ hOmega hsymm hC₀ hgarding
  exact ⟨basis, u, hvalue, heq⟩

/-- **The min–max principle is attained.** Under the hypotheses of
`TauCeti.PDE.exists_hilbertBasis_mixedEigenvalue`, `λₖ` is the least `C` for which some subspace
`W` of `H¹_Γ(Ω)`, whose values span a subspace of `L²(Ω)` of dimension at least `k + 1`,
satisfies `a(v, v) ≤ C ‖v‖²_{L²(Ω)}` for every `v ∈ W`. -/
theorem isLeast_mixedEigenvalue (k : ℕ) :
    IsLeast {C : ℝ | ∃ W : Submodule ℝ (W1pVanishingOn mu Omega 2 Γ),
      k + 1 ≤ Module.finrank ℝ (W.map ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap
        ∘ₗ (W1pVanishingOn mu Omega 2 Γ).subtype)) ∧
        ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
          C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2} (mixedEigenvalue mu Omega Γ a b c k) :=
  (exists_hilbertBasis_mixedEigenvalue_properties hcoeff hJ hΓ hOmega hsymm hC₀
    hgarding).choose_spec.choose_spec.2.2.2.2.1 k

/-- The mixed eigenvalues are nondecreasing: `λ₀ ≤ λ₁ ≤ ⋯`. -/
theorem monotone_mixedEigenvalue : Monotone (mixedEigenvalue mu Omega Γ a b c) :=
  (exists_hilbertBasis_mixedEigenvalue_properties hcoeff hJ hΓ hOmega hsymm hC₀
    hgarding).choose_spec.choose_spec.1

/-- The mixed eigenvalues tend to infinity. -/
theorem tendsto_mixedEigenvalue_atTop :
    Tendsto (mixedEigenvalue mu Omega Γ a b c) atTop atTop :=
  (exists_hilbertBasis_mixedEigenvalue_properties hcoeff hJ hΓ hOmega hsymm hC₀
    hgarding).choose_spec.choose_spec.2.1

/-- The mixed eigenvalues `λₖ` are exactly the mixed spectrum, listed with multiplicity. -/
theorem isMixedEigenvalue_iff_exists_mixedEigenvalue_eq (kappa' : ℝ) :
    IsMixedEigenvalue mu Omega Γ a b c kappa' ↔ ∃ k, mixedEigenvalue mu Omega Γ a b c k = kappa' :=
  (exists_hilbertBasis_mixedEigenvalue_properties hcoeff hJ hΓ hOmega hsymm hC₀
    hgarding).choose_spec.choose_spec.2.2.2.2.2 kappa'

omit hOmega in
/-- **Monotonicity in the Dirichlet part.** If `Γ ⊆ Γ'`, with `Γ'` still disjoint from `Ω`, every
mixed eigenvalue for `Γ` is at most the corresponding one for `Γ'`: `λₖ(Γ) ≤ λₖ(Γ')`. The
hypotheses are those of `TauCeti.PDE.exists_hilbertBasis_mixedEigenvalue` for `Γ`; they pass to
the smaller space `H¹_{Γ'}(Ω) ⊆ H¹_Γ(Ω)`. -/
theorem mixedEigenvalue_le_of_subset (hΓΓ' : Γ ⊆ Γ') (hΓ' : Disjoint Γ' Omega) (k : ℕ) :
    mixedEigenvalue mu Omega Γ a b c k ≤ mixedEigenvalue mu Omega Γ' a b c k := by
  rcases (Omega : Set (EuclideanSpace ℝ ι)).eq_empty_or_nonempty with hempty | hOmega
  · -- On the empty set every value vanishes, so no subspace is admissible and both sides are
    -- the infimum of the empty set.
    have hS (Γ'' : Set (EuclideanSpace ℝ ι)) : mixedEigenvalue mu Omega Γ'' a b c k = sInf ∅ := by
      rw [mixedEigenvalue_def]
      congr 1
      refine eq_empty_of_forall_notMem fun C ⟨W, hW, _⟩ ↦ ?_
      have hbot : W.map ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ
          (W1pVanishingOn mu Omega 2 Γ'').subtype) = ⊥ :=
        (Submodule.eq_bot_iff _).2 fun f _ ↦ Lp.ext (by simp [hempty, Filter.EventuallyEq])
      rw [hbot, finrank_bot] at hW
      omega
    rw [hS, hS]
  have hle : W1pVanishingOn mu Omega 2 Γ' ≤ W1pVanishingOn mu Omega 2 Γ :=
    w1pVanishingOnSubmodule_antitone (mu := mu) (Omega := Omega) (p := 2) hΓΓ'
  -- The hypotheses pass to `H¹_{Γ'}(Ω)` through the inclusion.
  have hsymm' (u v : W1pVanishingOn mu Omega 2 Γ') :
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2) :=
    hsymm ⟨u, hle u.property⟩ ⟨v, hle v.property⟩
  have hgarding' (w : W1pVanishingOn mu Omega 2 Γ') :
      C₀ * ‖(w : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2) +
          β * ‖W1p.value (w : W1p mu Omega 2)‖ ^ 2 :=
    hgarding ⟨w, hle w.property⟩
  refine csInf_le_csInf (isLeast_mixedEigenvalue hcoeff hJ hΓ hOmega hsymm hC₀ hgarding k).bddBelow
    (isLeast_mixedEigenvalue hcoeff hJ hΓ' hOmega hsymm' hC₀ hgarding' k).nonempty ?_
  -- A subspace admissible for `Γ'` is admissible for `Γ`, through the inclusion.
  rintro C ⟨W, hW, hC⟩
  refine ⟨W.map (Submodule.inclusion hle), ?_, ?_⟩
  · rwa [← Submodule.map_comp]
  · rintro _ ⟨v, hv, rfl⟩
    exact hC v hv

end Garding

end Domain

/-! ### The mixed and Neumann eigenvalues of `-Δ` -/

section Laplacian

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {Γ Γ' : Set (EuclideanSpace ℝ ι)}
  (hJ : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
  (hΓ : Disjoint Γ Omega) (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty)

attribute [local instance] instSeminormedAddCommGroupW1p instNormedSpaceW1p
  W1pVanishingOn.instNormedAddCommGroup W1pVanishingOn.instInnerProductSpace

omit [Nonempty ι] in
/-- The energy form of `-Δ`, `∫ ∇u · ∇v`, has bounded coefficients, is symmetric and nonnegative,
and satisfies Gårding's inequality with `C₀ = β = 1`, since `‖w‖²_{H¹} = ∫ |∇w|² + ‖w‖²_{L²}`. -/
private theorem laplacian_hypotheses :
    MemLp (fun x ↦ energyIntegrand ((fun _ ↦ (1 : Matrix ι ι ℝ)) x)
        ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤
        (mu.restrict Omega) ∧
      (∀ u v : W1p mu Omega 2,
        energyFormH1 (fun _ ↦ 1) 0 0 u v = energyFormH1 (fun _ ↦ 1) 0 0 v u) ∧
      (∀ w : W1p mu Omega 2, 0 ≤ energyFormH1 (fun _ ↦ 1) 0 0 w w) ∧
      ∀ w : W1p mu Omega 2,
        1 * ‖w‖ ^ 2 ≤ energyFormH1 (fun _ ↦ 1) 0 0 w w + 1 * ‖W1p.value w‖ ^ 2 := by
  have h1 := uniformlyEllipticOn_const_one_one (n := ι) (Omega : Set (EuclideanSpace ℝ ι))
  refine ⟨memLp_energyIntegrand_of_bounds (mu := mu) (b := 0) (c := 0) (beta := 0) (gamma := 0)
    h1.upper_nonneg aestronglyMeasurable_const aestronglyMeasurable_const
    aestronglyMeasurable_const (fun _x hx eta xi ↦ h1.upper_bound hx eta xi) (fun _ _ ↦ by simp)
    (fun _ _ ↦ by simp), fun u v ↦ ?_, fun w ↦ ?_, fun w ↦ ?_⟩
  · rw [energyFormH1_one_zero_zero_eq_inner, energyFormH1_one_zero_zero_eq_inner,
      real_inner_comm]
  · rw [energyFormH1_one_zero_zero_eq_inner]
    exact real_inner_self_nonneg
  · rw [energyFormH1_one_zero_zero_eq_inner, real_inner_self_eq_norm_sq,
      W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq]
    linarith

include hJ hΓ hOmega

/-- **The mixed eigenbasis of `-Δ`.** Let `Ω` be nonempty with compact value map
`H¹(Ω) → L²(Ω)`, for instance a nonempty bounded Lipschitz domain, and let `Γ` miss `Ω`. Then
there is an orthonormal basis `(eₖ)` of `L²(Ω)` such that `eₖ` is the value of some
`uₖ ∈ H¹_Γ(Ω)` with `∫ ∇uₖ · ∇v = λₖ ∫ uₖ v` for every `v ∈ H¹_Γ(Ω)`, where `λₖ` is the min–max
eigenvalue `TauCeti.PDE.mixedEigenvalue`. For `Γ = ∅` these are the Neumann eigenfunctions. -/
theorem exists_hilbertBasis_mixedEigenvalue_laplacian :
    ∃ (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (mu.restrict Omega)))
      (u : ℕ → W1pVanishingOn mu Omega 2 Γ),
      (∀ k, W1p.value (u k : W1p mu Omega 2) = basis k) ∧
      ∀ (k : ℕ) (v : W1pVanishingOn mu Omega 2 Γ),
        energyFormH1 (fun _ ↦ 1) 0 0 (u k : W1p mu Omega 2) (v : W1p mu Omega 2) =
          mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0 k *
            ⟪W1p.value (u k : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ :=
  have h := laplacian_hypotheses (mu := mu) (Omega := Omega)
  exists_hilbertBasis_mixedEigenvalue h.1 hJ hΓ hOmega (fun u v ↦ h.2.1 u v) one_pos
    fun w ↦ h.2.2.2 w

/-- **The min–max principle for the mixed eigenvalues of `-Δ` is attained**: `λₖ` is the least
`C` for which some subspace `W` of `H¹_Γ(Ω)`, whose values span a subspace of `L²(Ω)` of
dimension at least `k + 1`, satisfies `∫ |∇v|² ≤ C ∫ v²` for every `v ∈ W`. In particular `λ₀` is
the least Rayleigh quotient `∫ |∇u|² / ∫ u²` over `u ∈ H¹_Γ(Ω)` with nonzero value. -/
theorem isLeast_mixedEigenvalue_laplacian (k : ℕ) :
    IsLeast {C : ℝ | ∃ W : Submodule ℝ (W1pVanishingOn mu Omega 2 Γ),
      k + 1 ≤ Module.finrank ℝ (W.map ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap
        ∘ₗ (W1pVanishingOn mu Omega 2 Γ).subtype)) ∧
        ∀ v ∈ W, energyFormH1 (fun _ ↦ 1) 0 0 (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
          C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2}
      (mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0 k) :=
  have h := laplacian_hypotheses (mu := mu) (Omega := Omega)
  isLeast_mixedEigenvalue h.1 hJ hΓ hOmega (fun u v ↦ h.2.1 u v) one_pos (fun w ↦ h.2.2.2 w) k

/-- **The mixed spectrum of `-Δ`.** Under the hypotheses of
`TauCeti.PDE.exists_hilbertBasis_mixedEigenvalue_laplacian`, the mixed eigenvalues form a
sequence `0 ≤ λ₀ ≤ λ₁ ≤ ⋯ → ∞` which lists the mixed spectrum of `-Δ` with multiplicity. -/
theorem mixedEigenvalue_laplacian_spectrum :
    0 ≤ mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0 0 ∧
      Monotone (mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0) ∧
      Tendsto (mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0) atTop atTop ∧
      ∀ kappa : ℝ, IsMixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0 kappa ↔
        ∃ k, mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0 k = kappa := by
  have h := laplacian_hypotheses (mu := mu) (Omega := Omega)
  have hsymm (u v : W1pVanishingOn mu Omega 2 Γ) := h.2.1 u v
  have hgarding (w : W1pVanishingOn mu Omega 2 Γ) := h.2.2.2 w
  refine ⟨mixedEigenvalue_nonneg (fun v ↦ h.2.2.1 v) 0,
    monotone_mixedEigenvalue h.1 hJ hΓ hOmega hsymm one_pos hgarding,
    tendsto_mixedEigenvalue_atTop h.1 hJ hΓ hOmega hsymm one_pos hgarding,
    isMixedEigenvalue_iff_exists_mixedEigenvalue_eq h.1 hJ hΓ hOmega hsymm one_pos hgarding⟩

omit hOmega in
/-- **More Dirichlet boundary raises the eigenvalues of `-Δ`.** For `Γ ⊆ Γ'`, both disjoint from
`Ω`, and a compact value map `H¹(Ω) → L²(Ω)`, `λₖ(Γ) ≤ λₖ(Γ')` for every `k`. With
`Γ = ∅` and `Γ' = frontier Ω`, every Neumann eigenvalue is at most the corresponding Dirichlet
eigenvalue (`TauCeti.PDE.mixedEigenvalue_frontier`). -/
theorem mixedEigenvalue_laplacian_le_of_subset (hΓΓ' : Γ ⊆ Γ') (hΓ' : Disjoint Γ' Omega)
    (k : ℕ) :
    mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0 k ≤ mixedEigenvalue mu Omega Γ' (fun _ ↦ 1) 0 0 k :=
  have h := laplacian_hypotheses (mu := mu) (Omega := Omega)
  mixedEigenvalue_le_of_subset h.1 hJ hΓ (fun u v ↦ h.2.1 u v) one_pos (fun w ↦ h.2.2.2 w) hΓΓ'
    hΓ' k

end Laplacian

end PDE

end TauCeti

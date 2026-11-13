/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Variational.MinMax
public import TauCeti.Analysis.PDE.Spectrum.Sequence
public import TauCeti.Analysis.PDE.EnergyForm.Restriction

/-!
# The min–max principle for the Dirichlet eigenvalues

Let `Ω ⊆ ℝⁿ` be open and let `a(u, v)` be the energy form of a divergence-form operator `L` on
`H¹₀(Ω)`. For `k ∈ ℕ` the **`k`-th Dirichlet eigenvalue** `λₖ(Ω)`, counted from `k = 0` with
multiplicity, is defined here by the Courant–Fischer min–max principle
(`TauCeti.PDE.dirichletEigenvalue`): it is the infimum of the constants `C` for which some
subspace `W` of `H¹₀(Ω)`, whose values span a subspace of `L²(Ω)` of dimension at least `k + 1`,
satisfies `a(v, v) ≤ C ‖v‖²_{L²(Ω)}` for every `v ∈ W`. The definition needs no eigenfunctions,
so it makes sense on every open set.

When the energy form is symmetric and nonnegative, the infimum is attained by any nondecreasing
listing `κ₀ ≤ κ₁ ≤ ⋯` of eigenvalues with eigenfunctions in `H¹₀(Ω)` whose values form an
orthonormal basis of `L²(Ω)`, and `λₖ(Ω) = κₖ`
(`TauCeti.PDE.dirichletEigenvalue_eq_of_hilbertBasis`). This is the min–max principle for a form
and an embedding, `TauCeti.isLeast_minMax_of_hilbertBasis`, applied to the energy form and the
inclusion `H¹₀(Ω) → L²(Ω)`. On a nonempty bounded open set with a symmetric coercive form such a
listing exists (`TauCeti.PDE.exists_hilbertBasis_nat_isDirichletEigenvalue_monotone`), so
`(λₖ(Ω))ₖ` is *the* sequence `0 < λ₀ ≤ λ₁ ≤ ⋯ → ∞` of Dirichlet eigenvalues, and every such
listing is this one.

The variational definition makes the eigenvalues **monotone in the domain**: for open `U ⊆ Ω`,
extension by zero maps `H¹₀(U)` into `H¹₀(Ω)` preserving the energy and the `L²` norm, so every
subspace admissible for `U` gives one admissible for `Ω` with the same constant, and

`λₖ(Ω) ≤ λₖ(U)` (`TauCeti.PDE.dirichletEigenvalue_le_of_domain_le`).

No regularity of the boundaries and no connectedness is needed. For `-Δ` this is
`TauCeti.PDE.dirichletEigenvalue_laplacian_le_of_domain_le`. For instance, the eigenvalues
`4 (k + 1)²` of the interval `(0, π / 2)` dominate the eigenvalues `(k + 1)²` of `(0, π)`.

## Main declarations

* `TauCeti.PDE.dirichletEigenvalue`: the `k`-th Dirichlet eigenvalue, by min–max.
* `TauCeti.PDE.dirichletEigenvalue_eq_of_hilbertBasis`: it is the `k`-th term of every
  nondecreasing listing of the eigenvalues with an orthonormal eigenbasis.
* `TauCeti.PDE.isLeast_dirichletEigenvalue`: on a nonempty bounded domain the infimum defining
  it is attained.
* `TauCeti.PDE.exists_hilbertBasis_dirichletEigenvalue`, `TauCeti.PDE.monotone_dirichletEigenvalue`,
  `TauCeti.PDE.tendsto_dirichletEigenvalue_atTop`, `TauCeti.PDE.dirichletEigenvalue_zero`,
  `TauCeti.PDE.dirichletEigenvalue_pos` and
  `TauCeti.PDE.isDirichletEigenvalue_iff_exists_dirichletEigenvalue_eq`: on a nonempty bounded
  domain the `λₖ(Ω)` are the Dirichlet spectrum, listed with multiplicity in nondecreasing order,
  with an orthonormal eigenbasis.
* `TauCeti.PDE.dirichletEigenvalue_le_of_domain_le` and
  `TauCeti.PDE.dirichletEigenvalue_laplacian_le_of_domain_le`: domain monotonicity.

## References

* R. Courant and D. Hilbert, *Methods of Mathematical Physics*, Vol. I, Chapter VI, §1–§2.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 6.5.1.
* D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 8.12.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Bornology Filter MeasureTheory Set TopologicalSpace
open scoped InnerProductSpace Topology

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {U Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

variable (mu Omega a b c) in
/-- **The `k`-th Dirichlet eigenvalue** of the divergence-form operator with coefficients
`a, b, c` on `Ω`, counted from `k = 0` with multiplicity, by the Courant–Fischer min–max
principle: the infimum of the constants `C` such that `a(v, v) ≤ C ‖v‖²_{L²(Ω)}` for every `v`
in some subspace `W` of `H¹₀(Ω)` whose values span a subspace of `L²(Ω)` of dimension at least
`k + 1`.

For a symmetric nonnegative form with an orthonormal eigenbasis, for instance a symmetric coercive
form on a nonempty bounded open set, the infimum is attained and equals the `k`-th term of the
nondecreasing listing of the eigenvalues (`TauCeti.PDE.dirichletEigenvalue_eq_of_hilbertBasis`).
Otherwise the infimum may be over an empty or unbounded set, and the value carries no
information. -/
def dirichletEigenvalue (k : ℕ) : ℝ :=
  sInf {C : ℝ | ∃ W : Submodule ℝ (W1p0 mu Omega 2),
    k + 1 ≤ Module.finrank ℝ
      (W.map (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap) ∧
      ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
        C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2}

/-- The definition of the `k`-th Dirichlet eigenvalue as an infimum. -/
theorem dirichletEigenvalue_def (k : ℕ) :
    dirichletEigenvalue mu Omega a b c k =
      sInf {C : ℝ | ∃ W : Submodule ℝ (W1p0 mu Omega 2),
        k + 1 ≤ Module.finrank ℝ
          (W.map (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap) ∧
          ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
            C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2} :=
  (rfl)

/-- The min–max principle `TauCeti.isLeast_minMax_of_hilbertBasis` for the energy form on
`H¹₀(Ω)` and the inclusion of `H¹₀(Ω)` in `L²(Ω)`. -/
private theorem isLeast_of_hilbertBasis
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hsymm : ∀ u v : W1p0 mu Omega 2,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (hnonneg : ∀ v : W1p0 mu Omega 2,
      0 ≤ energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2))
    (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (mu.restrict Omega))) {kappa : ℕ → ℝ}
    (hkappa : Monotone kappa) {u : ℕ → W1p0 mu Omega 2}
    (hvalue : ∀ j, W1p.value (u j : W1p mu Omega 2) = basis j)
    (heq : ∀ (j : ℕ) (v : W1p0 mu Omega 2),
      energyFormH1 a b c (u j : W1p mu Omega 2) (v : W1p mu Omega 2) =
        kappa j * ⟪W1p.value (u j : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ)
    (k : ℕ) :
    IsLeast {C : ℝ | ∃ W : Submodule ℝ (W1p0 mu Omega 2),
      k + 1 ≤ Module.finrank ℝ
        (W.map (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap) ∧
        ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
          C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2} (kappa k) := by
  simpa only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, ContinuousLinearMap.coe_coe,
    energyFormH1L0_apply, W1p0.valueL_apply] using
    isLeast_minMax_of_hilbertBasis (B := (energyFormH1L0 hcoeff).toLinearMap₁₂)
      (J := (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap)
      (by simpa only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
        energyFormH1L0_apply] using hsymm)
      (by simpa only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
        energyFormH1L0_apply] using hnonneg)
      basis hkappa (by simpa only [ContinuousLinearMap.coe_coe, W1p0.valueL_apply] using hvalue)
      (by simpa only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, energyFormH1L0_apply,
        ContinuousLinearMap.coe_coe, W1p0.valueL_apply] using heq) k

/-- **The Courant–Fischer min–max principle for the Dirichlet eigenvalues.** Let the energy form
`a` be symmetric and nonnegative on `H¹₀(Ω)`, and let `κ₀ ≤ κ₁ ≤ ⋯` be eigenvalues with
eigenfunctions `uⱼ ∈ H¹₀(Ω)`, `a(uⱼ, v) = κⱼ ⟪uⱼ, v⟫_{L²}` for every `v ∈ H¹₀(Ω)`, whose values
form an orthonormal basis of `L²(Ω)`. Then `κₖ` is the `k`-th Dirichlet eigenvalue `λₖ(Ω)`. In
particular any two such listings agree. -/
theorem dirichletEigenvalue_eq_of_hilbertBasis
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hsymm : ∀ u v : W1p0 mu Omega 2,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (hnonneg : ∀ v : W1p0 mu Omega 2,
      0 ≤ energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2))
    (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (mu.restrict Omega))) {kappa : ℕ → ℝ}
    (hkappa : Monotone kappa) {u : ℕ → W1p0 mu Omega 2}
    (hvalue : ∀ j, W1p.value (u j : W1p mu Omega 2) = basis j)
    (heq : ∀ (j : ℕ) (v : W1p0 mu Omega 2),
      energyFormH1 a b c (u j : W1p mu Omega 2) (v : W1p mu Omega 2) =
        kappa j * ⟪W1p.value (u j : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ)
    (k : ℕ) :
    dirichletEigenvalue mu Omega a b c k = kappa k :=
  (isLeast_of_hilbertBasis hcoeff hsymm hnonneg basis hkappa hvalue heq k).csInf_eq

/-- A coercive energy form is nonnegative on the diagonal. -/
private theorem energyFormH1_self_nonneg
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (v : W1p0 mu Omega 2) :
    0 ≤ energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) := by
  simpa only [energyFormH1L0_apply] using hcoercive.apply_self_nonneg v

section Bounded

variable [Nonempty ι]
  (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
  (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
  (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
  (hsymm : ∀ u v : W1p0 mu Omega 2,
    energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
      energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
  (hOmega_nonempty : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty)
include hcoercive hOmega hsymm hOmega_nonempty

/-- **The Dirichlet eigenvalues with an eigenbasis.** On a nonempty bounded open set, for a
symmetric coercive energy form, there is an orthonormal basis `(eₖ)` of `L²(Ω)` such that `eₖ`
is the value of some `uₖ ∈ H¹₀(Ω)` with `a(uₖ, v) = λₖ(Ω) ⟪uₖ, v⟫_{L²}` for every `v ∈ H¹₀(Ω)`,
where `λₖ(Ω)` is the min–max eigenvalue `TauCeti.PDE.dirichletEigenvalue`. -/
theorem exists_hilbertBasis_dirichletEigenvalue :
    ∃ (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (mu.restrict Omega))) (u : ℕ → W1p0 mu Omega 2),
      (∀ k, W1p.value (u k : W1p mu Omega 2) = basis k) ∧
      ∀ (k : ℕ) (v : W1p0 mu Omega 2),
        energyFormH1 a b c (u k : W1p mu Omega 2) (v : W1p mu Omega 2) =
          dirichletEigenvalue mu Omega a b c k *
            ⟪W1p.value (u k : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  obtain ⟨basis, kappa, u, hmono, -, -, hvalue, heq, -, -⟩ :=
    exists_hilbertBasis_nat_isDirichletEigenvalue_monotone hcoeff hcoercive hOmega hsymm
      hOmega_nonempty
  refine ⟨basis, u, hvalue, fun k v ↦ ?_⟩
  rw [dirichletEigenvalue_eq_of_hilbertBasis hcoeff hsymm
    (energyFormH1_self_nonneg hcoeff hcoercive) basis hmono hvalue heq k, heq]

/-- **The min–max principle is attained.** On a nonempty bounded open set, for a symmetric
coercive energy form, `λₖ(Ω)` is the least `C` for which some subspace `W` of `H¹₀(Ω)`, whose
values span a subspace of `L²(Ω)` of dimension at least `k + 1`, satisfies
`a(v, v) ≤ C ‖v‖²_{L²(Ω)}` for every `v ∈ W`. -/
theorem isLeast_dirichletEigenvalue (k : ℕ) :
    IsLeast {C : ℝ | ∃ W : Submodule ℝ (W1p0 mu Omega 2),
      k + 1 ≤ Module.finrank ℝ
        (W.map (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap) ∧
        ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
          C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2} (dirichletEigenvalue mu Omega a b c k) := by
  obtain ⟨basis, kappa, u, hmono, -, -, hvalue, heq, -, -⟩ :=
    exists_hilbertBasis_nat_isDirichletEigenvalue_monotone hcoeff hcoercive hOmega hsymm
      hOmega_nonempty
  have hnonneg := energyFormH1_self_nonneg hcoeff hcoercive
  rw [dirichletEigenvalue_eq_of_hilbertBasis hcoeff hsymm hnonneg basis hmono hvalue heq]
  exact isLeast_of_hilbertBasis hcoeff hsymm hnonneg basis hmono hvalue heq k

/-- On a nonempty bounded open set, for a symmetric coercive energy form, the Dirichlet
eigenvalues `λₖ(Ω)` have the properties of the nondecreasing listing of the Dirichlet spectrum
given by `TauCeti.PDE.exists_hilbertBasis_nat_isDirichletEigenvalue_monotone`. -/
private theorem dirichletEigenvalue_properties :
    Monotone (dirichletEigenvalue mu Omega a b c) ∧
      Tendsto (dirichletEigenvalue mu Omega a b c) atTop atTop ∧
      dirichletEigenvalue mu Omega a b c 0 = firstDirichletEigenvalue hcoeff hcoercive ∧
      ∀ kappa' : ℝ, IsDirichletEigenvalue mu Omega a b c kappa' ↔
        ∃ k, dirichletEigenvalue mu Omega a b c k = kappa' := by
  obtain ⟨basis, kappa, u, hmono, htendsto, hzero, hvalue, heq, hiff, -⟩ :=
    exists_hilbertBasis_nat_isDirichletEigenvalue_monotone hcoeff hcoercive hOmega hsymm
      hOmega_nonempty
  obtain rfl : dirichletEigenvalue mu Omega a b c = kappa :=
    funext <| dirichletEigenvalue_eq_of_hilbertBasis hcoeff hsymm
      (energyFormH1_self_nonneg hcoeff hcoercive) basis hmono hvalue heq
  exact ⟨hmono, htendsto, hzero, hiff⟩

/-- The Dirichlet eigenvalues are nondecreasing: `λ₀(Ω) ≤ λ₁(Ω) ≤ ⋯`. -/
theorem monotone_dirichletEigenvalue : Monotone (dirichletEigenvalue mu Omega a b c) :=
  (dirichletEigenvalue_properties hcoeff hcoercive hOmega hsymm hOmega_nonempty).1

/-- The Dirichlet eigenvalues tend to infinity. -/
theorem tendsto_dirichletEigenvalue_atTop :
    Tendsto (dirichletEigenvalue mu Omega a b c) atTop atTop :=
  (dirichletEigenvalue_properties hcoeff hcoercive hOmega hsymm hOmega_nonempty).2.1

/-- The least Dirichlet eigenvalue `λ₀(Ω)` is the first Dirichlet eigenvalue, the minimum of the
Rayleigh quotient. -/
theorem dirichletEigenvalue_zero :
    dirichletEigenvalue mu Omega a b c 0 = firstDirichletEigenvalue hcoeff hcoercive :=
  (dirichletEigenvalue_properties hcoeff hcoercive hOmega hsymm hOmega_nonempty).2.2.1

/-- The Dirichlet eigenvalues are positive. -/
theorem dirichletEigenvalue_pos (k : ℕ) : 0 < dirichletEigenvalue mu Omega a b c k :=
  (dirichletEigenvalue_zero hcoeff hcoercive hOmega hsymm hOmega_nonempty ▸
    firstDirichletEigenvalue_pos hcoeff hcoercive hOmega hsymm hOmega_nonempty).trans_le
      (monotone_dirichletEigenvalue hcoeff hcoercive hOmega hsymm hOmega_nonempty k.zero_le)

/-- The Dirichlet eigenvalues `λₖ(Ω)` are exactly the Dirichlet spectrum. -/
theorem isDirichletEigenvalue_iff_exists_dirichletEigenvalue_eq (kappa' : ℝ) :
    IsDirichletEigenvalue mu Omega a b c kappa' ↔
      ∃ k, dirichletEigenvalue mu Omega a b c k = kappa' :=
  (dirichletEigenvalue_properties hcoeff hcoercive hOmega hsymm hOmega_nonempty).2.2.2 kappa'

end Bounded

/-! ### Domain monotonicity -/

/-- Extension by zero from `U` to `Ω` turns a subspace admissible in the min–max principle on `U`
into one admissible on `Ω` with the same constant. -/
private theorem mem_setOf_dirichletEigenvalue_of_domain_le (hU : U ≤ Omega) {k : ℕ} {C : ℝ}
    (h : ∃ W : Submodule ℝ (W1p0 mu U 2),
      k + 1 ≤ Module.finrank ℝ (W.map (W1p0.valueL (mu := mu) (Omega := U) (p := 2)).toLinearMap) ∧
        ∀ v ∈ W, energyFormH1 a b c (v : W1p mu U 2) (v : W1p mu U 2) ≤
          C * ‖W1p.value (v : W1p mu U 2)‖ ^ 2) :
    ∃ W : Submodule ℝ (W1p0 mu Omega 2),
      k + 1 ≤ Module.finrank ℝ
        (W.map (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap) ∧
        ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
          C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2 := by
  obtain ⟨W, hW, hC⟩ := h
  let E := extendByZeroLpₗᵢ ℝ mu U.isOpen.measurableSet (F := ℝ) (p := 2)
    (SetLike.coe_subset_coe.mpr hU)
  refine ⟨W.map (W1p0.extendByZeroL (mu := mu) (p := 2) hU).toLinearMap, ?_, ?_⟩
  · -- The values of the extensions are the extensions of the values, and `E` is injective.
    have hcomp : (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ
        (W1p0.extendByZeroL (mu := mu) (p := 2) hU).toLinearMap =
          E.toLinearMap ∘ₗ (W1p0.valueL (mu := mu) (Omega := U) (p := 2)).toLinearMap := by
      ext v
      simp [E, W1p0.value_extendByZeroL]
    rw [← Submodule.map_comp, hcomp, Submodule.map_comp,
      ← (Submodule.equivMapOfInjective E.toLinearMap E.injective _).finrank_eq]
    exact hW
  · rintro _ ⟨v, hv, rfl⟩
    simpa only [ContinuousLinearMap.coe_coe, energyFormH1_extendByZeroL,
      W1p0.norm_value_extendByZeroL] using hC v hv

/-- **Domain monotonicity of the Dirichlet eigenvalues.** For open sets `U ⊆ Ω` with `U`
nonempty and `Ω` bounded, and a symmetric coercive energy form on `Ω`, every Dirichlet eigenvalue
of `U` is at least the corresponding one of `Ω`: `λₖ(Ω) ≤ λₖ(U)`. The coefficients are the same
on both domains, and no regularity of the boundaries is needed. -/
theorem dirichletEigenvalue_le_of_domain_le [Nonempty ι] (hU : U ≤ Omega)
    (hU_nonempty : (U : Set (EuclideanSpace ℝ ι)).Nonempty)
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (hsymm : ∀ u v : W1p0 mu Omega 2,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (k : ℕ) :
    dirichletEigenvalue mu Omega a b c k ≤ dirichletEigenvalue mu U a b c k := by
  have hUO : (U : Set (EuclideanSpace ℝ ι)) ⊆ Omega := SetLike.coe_subset_coe.mpr hU
  -- The hypotheses pass to `U` through extension by zero.
  have hcoeffU : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict U) :=
    hcoeff.mono_measure (Measure.restrict_mono hUO le_rfl)
  have hcoerciveU : IsCoercive (energyFormH1L0 hcoeffU) := by
    obtain ⟨C, hC, hbound⟩ := hcoercive
    refine ⟨C, hC, fun v ↦ ?_⟩
    simpa only [W1p0.norm_extendByZeroL, energyFormH1L0_apply, energyFormH1_extendByZeroL]
      using hbound (W1p0.extendByZeroL hU v)
  have hsymmU (v w : W1p0 mu U 2) :
      energyFormH1 a b c (v : W1p mu U 2) (w : W1p mu U 2) =
        energyFormH1 a b c (w : W1p mu U 2) (v : W1p mu U 2) := by
    rw [← energyFormH1_extendByZeroL a b c hU v w, ← energyFormH1_extendByZeroL a b c hU w v]
    exact hsymm _ _
  -- On both domains the infimum defining `λₖ` is attained.
  exact csInf_le_csInf
    (isLeast_dirichletEigenvalue hcoeff hcoercive hOmega hsymm (hU_nonempty.mono hUO) k).bddBelow
    (isLeast_dirichletEigenvalue hcoeffU hcoerciveU (hOmega.subset hUO) hsymmU hU_nonempty
      k).nonempty
    fun C hC ↦ mem_setOf_dirichletEigenvalue_of_domain_le hU hC


/-- **Domain monotonicity of the Dirichlet eigenvalues of `-Δ`.** For open sets `U ⊆ Ω` in
`ℝ^{n+1}` with `U` nonempty and `Ω` bounded, `λₖ(Ω) ≤ λₖ(U)` for every `k`. -/
theorem dirichletEigenvalue_laplacian_le_of_domain_le {n : ℕ}
    {U Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (hU : U ≤ Omega)
    (hU_nonempty : (U : Set (EuclideanSpace ℝ (Fin (n + 1)))).Nonempty)
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) (k : ℕ) :
    dirichletEigenvalue volume Omega (fun _ ↦ 1) 0 0 k ≤
      dirichletEigenvalue volume U (fun _ ↦ 1) 0 0 k :=
  (exists_isCoercive_laplacian_of_isBounded hOmega).elim fun hcoeff hcoercive ↦
    dirichletEigenvalue_le_of_domain_le hU hU_nonempty hcoeff hcoercive hOmega
      (fun _ _ ↦ energyFormH1_comm_of_isSymm_ae (ae_of_all _ fun _ ↦ Matrix.isSymm_one) _ _) k

end PDE

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Spectrum.MinMax
public import TauCeti.Analysis.PDE.Spectrum.Operator.Mixed

/-!
# The min–max principle for the mixed eigenvalues

Let `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` be a divergence-form operator on an open set
`Ω ⊆ ℝⁿ` with energy form `a(u, v)`, and let `Γ` be a set disjoint from `Ω`, typically a part of
its boundary. Write `H¹_Γ(Ω)` for the space `TauCeti.W1pVanishingOn mu Ω 2 Γ` of Sobolev
functions vanishing on `Γ`. For `k ∈ ℕ` the **`k`-th mixed eigenvalue** `λₖ(Γ)`, counted from
`k = 0` with multiplicity, is defined by the Courant–Fischer min–max principle
(`TauCeti.PDE.mixedEigenvalue`): it is the infimum of the constants `C` for which some subspace
`W` of `H¹_Γ(Ω)`, whose values span a subspace of `L²(Ω)` of dimension at least `k + 1`,
satisfies `a(v, v) ≤ C ‖v‖²_{L²(Ω)}` for every `v ∈ W`. This is the Dirichlet condition on `Γ`
and the natural (conormal) condition on the rest of the boundary; at `Γ = ∂Ω` it is the
Dirichlet eigenvalue `TauCeti.PDE.dirichletEigenvalue` (`TauCeti.PDE.mixedEigenvalue_frontier`),
and for `Γ = ∅` on a domain where `H¹_∅(Ω) = H¹(Ω)` it is the `k`-th Neumann eigenvalue.

Unlike the Dirichlet case the energy form need not be coercive on `H¹_Γ(Ω)`: for `-Δ` and
`Γ = ∅` the constants have zero energy. It is enough that the form is symmetric and that the
shifted form `a + ω ⟪·, ·⟫_{L²}` (`TauCeti.PDE.mixedForm`) is coercive on `H¹_Γ(Ω)` for some `ω`,
which is a Gårding inequality (`TauCeti.PDE.isCoercive_mixedForm`). Under the **Rellich
property**, that the value map `H¹(Ω) → L²(Ω)` is compact, as on a bounded Lipschitz domain
(`TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomainWith_of_affineIsometryEquiv`):

* the abstract eigenbasis of the coercive shifted form along the compact value map, listed in
  nondecreasing order of its eigenvalues `κ + ω` (`IsCoercive.exists_hilbertBasis_nat_monotone`),
  gives an orthonormal basis `(eₖ)` of `L²(Ω)` with `eₖ` the value of some `uₖ ∈ H¹_Γ(Ω)`,
  `a(uₖ, v) = λₖ ⟪uₖ, v⟫_{L²}` for every `v ∈ H¹_Γ(Ω)`
  (`TauCeti.PDE.exists_hilbertBasis_mixedEigenvalue`);
* the min–max infimum is attained (`TauCeti.PDE.isLeast_mixedEigenvalue`), the `λₖ` are
  nondecreasing and tend to infinity (`TauCeti.PDE.monotone_mixedEigenvalue`,
  `TauCeti.PDE.tendsto_mixedEigenvalue_atTop`), and they are exactly the mixed eigenvalues
  (`TauCeti.PDE.exists_ne_zero_forall_energyFormH1_eq_iff_exists_mixedEigenvalue_eq`), that is,
  the spectrum of the mixed realization (`TauCeti.PDE.spectrum_mixedOperator_eq_range`).

The min–max value is identified with the eigenbasis by the abstract min–max principle
`TauCeti.isLeast_minMax_of_hilbertBasis`, applied to the nonnegative shifted form, whose
eigenvalues are `λₖ + ω` (`TauCeti.PDE.mixedEigenvalue_eq_of_hilbertBasis`).

Under the Rellich property, on a nonempty domain, the eigenvalues are **monotone in the boundary
part**. Let the form be symmetric on `H¹_Γ(Ω)` and coercive there after a shift, let `Γ ⊆ Γ'` and
let `Γ'` miss `Ω`. Then `H¹_{Γ'}(Ω)` is a subspace of `H¹_Γ(Ω)`, so every subspace admissible in the
min–max for `Γ'` is admissible for `Γ`, and since both infima are attained, `λₖ(Γ) ≤ λₖ(Γ')`
(`TauCeti.PDE.mixedEigenvalue_mono`). For `-Δ`, again under the Rellich property on a nonempty
domain, the eigenvalues for `Γ = ∅`, for `Γ` and for `∂Ω` are therefore ordered: `0 = λ₀(∅)`
when `Ω` is moreover bounded (`TauCeti.PDE.mixedEigenvalue_laplacian_empty_zero`), and
`λₖ(Γ) ≤ λₖ(∂Ω)` for every `Γ ⊆ ∂Ω`
(`TauCeti.PDE.mixedEigenvalue_laplacian_le_dirichletEigenvalue`). For instance, on `(0, 1)` with
`Γ = {0}` the least Neumann, mixed and Dirichlet eigenvalues are `0`, `π² / 4` and `π²`.

## Main declarations

* `TauCeti.PDE.mixedEigenvalue`: the `k`-th mixed eigenvalue, by min–max.
* `TauCeti.PDE.mixedEigenvalue_eq_of_hilbertBasis`: it is the `k`-th term of every
  nondecreasing listing of the eigenvalues with an orthonormal eigenbasis.
* `TauCeti.PDE.mixedEigenvalue_frontier`: at `Γ = ∂Ω` it is the Dirichlet eigenvalue.
* `TauCeti.PDE.exists_hilbertBasis_mixedEigenvalue`, `TauCeti.PDE.isLeast_mixedEigenvalue`,
  `TauCeti.PDE.monotone_mixedEigenvalue`, `TauCeti.PDE.tendsto_mixedEigenvalue_atTop`,
  `TauCeti.PDE.exists_ne_zero_forall_energyFormH1_eq_iff_exists_mixedEigenvalue_eq` and
  `TauCeti.PDE.spectrum_mixedOperator_eq_range`: under the Rellich property, the `λₖ(Γ)` are the
  mixed spectrum, listed with multiplicity in nondecreasing order, with an orthonormal eigenbasis.
* `TauCeti.PDE.mixedEigenvalue_mono`: monotonicity in `Γ`.
* `TauCeti.PDE.exists_hilbertBasis_mixedEigenvalue_laplacian`,
  `TauCeti.PDE.mixedEigenvalue_laplacian_nonneg`, `TauCeti.PDE.mixedEigenvalue_laplacian_mono`,
  `TauCeti.PDE.mixedEigenvalue_laplacian_le_dirichletEigenvalue` and
  `TauCeti.PDE.mixedEigenvalue_laplacian_empty_zero`: the mixed Laplacian `-Δ_Γ`.

## References

* R. Courant and D. Hilbert, *Methods of Mathematical Physics*, Vol. I, Chapter VI, §1–§2
  (min–max with natural boundary conditions, and the comparison of boundary conditions).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 9.31 (the Dirichlet eigenbasis, whose proof carries over to `H¹_Γ(Ω)`).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Bornology Filter MeasureTheory Set TopologicalSpace
open scoped InnerProductSpace

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {Γ Γ' : Set (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ}

attribute [local instance] W1pVanishingOn.instNormedAddCommGroup
  W1pVanishingOn.instInnerProductSpace

variable (mu Omega Γ a b c) in
/-- **The `k`-th mixed eigenvalue** of the divergence-form operator with coefficients `a, b, c` on
`Ω`, with the Dirichlet condition on `Γ` and the natural condition on the rest of the boundary,
counted from `k = 0` with multiplicity, by the Courant–Fischer min–max principle: the infimum of
the constants `C` such that `a(v, v) ≤ C ‖v‖²_{L²(Ω)}` for every `v` in some subspace `W` of
`H¹_Γ(Ω)` whose values span a subspace of `L²(Ω)` of dimension at least `k + 1`.

For a symmetric form, coercive on `H¹_Γ(Ω)` after a shift, on a nonempty domain with the Rellich
property and for `Γ` missing `Ω`, the infimum is attained (`TauCeti.PDE.isLeast_mixedEigenvalue`)
and equals the `k`-th term of the nondecreasing listing of the mixed eigenvalues
(`TauCeti.PDE.mixedEigenvalue_eq_of_hilbertBasis`). Otherwise the infimum may be over an empty or
unbounded set, and the value carries no information. -/
def mixedEigenvalue (k : ℕ) : ℝ :=
  sInf {C : ℝ | ∃ W : Submodule ℝ (W1pVanishingOn mu Omega 2 Γ),
    k + 1 ≤ Module.finrank ℝ
      (W.map (W1pVanishingOn.valueL (mu := mu) (Omega := Omega) (p := 2) (Γ := Γ)).toLinearMap) ∧
      ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
        C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2}

/-- The definition of the `k`-th mixed eigenvalue as an infimum. -/
theorem mixedEigenvalue_def (k : ℕ) :
    mixedEigenvalue mu Omega Γ a b c k =
      sInf {C : ℝ | ∃ W : Submodule ℝ (W1pVanishingOn mu Omega 2 Γ),
        k + 1 ≤ Module.finrank ℝ
          (W.map (W1pVanishingOn.valueL (mu := mu) (Omega := Omega) (p := 2)
            (Γ := Γ)).toLinearMap) ∧
          ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
            C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2} :=
  (rfl)

/-- **At the whole frontier the mixed eigenvalues are the Dirichlet eigenvalues**, since
`H¹_{∂Ω}(Ω) = H¹₀(Ω)` (`TauCeti.w1pVanishingOnSubmodule_frontier`). -/
theorem mixedEigenvalue_frontier (k : ℕ) :
    mixedEigenvalue mu Omega (frontier (Omega : Set (EuclideanSpace ℝ ι))) a b c k =
      dirichletEigenvalue mu Omega a b c k := by
  -- `H¹_{∂Ω}(Ω)` and `H¹₀(Ω)` are the same subspace of `H¹(Ω)`, so the identity of `H¹(Ω)`
  -- matches the admissible subspaces of the two infima.
  let e : W1pVanishingOn mu Omega 2 (frontier (Omega : Set (EuclideanSpace ℝ ι))) ≃ₗ[ℝ]
      W1p0 mu Omega 2 :=
    LinearEquiv.ofEq _ _ (congrArg ClosedSubmodule.toSubmodule w1pVanishingOnSubmodule_frontier)
  have hval : (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ e.toLinearMap =
      (W1pVanishingOn.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap :=
    LinearMap.ext fun v ↦ by
      simp [e, W1p0.valueL_apply, W1pVanishingOn.valueL_apply, LinearEquiv.coe_ofEq_apply]
  have hval' : (W1pVanishingOn.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ
      e.symm.toLinearMap = (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap := by
    rw [← hval, LinearMap.comp_assoc, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.comp_id]
  rw [mixedEigenvalue_def, dirichletEigenvalue_def]
  congr 1
  ext C
  constructor
  · rintro ⟨W, hW, hC⟩
    refine ⟨W.map e.toLinearMap, by rwa [← Submodule.map_comp, hval], ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact hC v hv
  · rintro ⟨W, hW, hC⟩
    refine ⟨W.map e.symm.toLinearMap, by rwa [← Submodule.map_comp, hval'], ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact hC v hv

/-! ### The min–max principle -/

/-- The min–max principle `TauCeti.isLeast_minMax_of_hilbertBasis` for the energy form on
`H¹_Γ(Ω)` and the value map `H¹_Γ(Ω) → L²(Ω)`, applied to the energy form shifted by `ω`, which is
nonnegative, with eigenvalues shifted by `ω`. -/
private theorem isLeast_of_hilbertBasis {omega : ℝ}
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hsymm : ∀ u v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (hbdd : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      -omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2))
    (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (mu.restrict Omega))) {kappa : ℕ → ℝ}
    (hkappa : Monotone kappa) {u : ℕ → W1pVanishingOn mu Omega 2 Γ}
    (hvalue : ∀ j, W1p.value (u j : W1p mu Omega 2) = basis j)
    (heq : ∀ (j : ℕ) (v : W1pVanishingOn mu Omega 2 Γ),
      energyFormH1 a b c (u j : W1p mu Omega 2) (v : W1p mu Omega 2) =
        kappa j * ⟪W1p.value (u j : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ)
    (k : ℕ) :
    IsLeast {C : ℝ | ∃ W : Submodule ℝ (W1pVanishingOn mu Omega 2 Γ),
      k + 1 ≤ Module.finrank ℝ
        (W.map (W1pVanishingOn.valueL (mu := mu) (Omega := Omega) (p := 2) (Γ := Γ)).toLinearMap) ∧
        ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
          C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2} (kappa k) := by
  have h := isLeast_minMax_of_hilbertBasis (B := (mixedForm hcoeff Γ omega).toLinearMap₁₂)
    (J := (W1pVanishingOn.valueL (mu := mu) (Omega := Omega) (p := 2) (Γ := Γ)).toLinearMap)
    (kappa := fun j ↦ kappa j + omega)
    (fun v w ↦ by
      simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, mixedForm_apply, hsymm v w,
        real_inner_comm])
    (fun v ↦ by
      simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, mixedForm_apply,
        real_inner_self_eq_norm_sq]
      linarith [hbdd v])
    basis (fun i j hij ↦ by dsimp only; linarith [hkappa hij])
    (by simpa only [ContinuousLinearMap.coe_coe, W1pVanishingOn.valueL_apply] using hvalue)
    (fun j v ↦ by
      simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, mixedForm_apply, heq,
        ContinuousLinearMap.coe_coe, W1pVanishingOn.valueL_apply]
      ring) k
  -- A constant `C` is admissible for the energy form exactly when `C + ω` is admissible for the
  -- shifted form.
  have hmem (C : ℝ) :
      (∃ W : Submodule ℝ (W1pVanishingOn mu Omega 2 Γ),
        k + 1 ≤ Module.finrank ℝ (W.map
          (W1pVanishingOn.valueL (mu := mu) (Omega := Omega) (p := 2) (Γ := Γ)).toLinearMap) ∧
          ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
            C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2) ↔
        C + omega ∈ {C : ℝ | ∃ W : Submodule ℝ (W1pVanishingOn mu Omega 2 Γ),
          k + 1 ≤ Module.finrank ℝ (W.map
            (W1pVanishingOn.valueL (mu := mu) (Omega := Omega) (p := 2) (Γ := Γ)).toLinearMap) ∧
            ∀ v ∈ W, (mixedForm hcoeff Γ omega).toLinearMap₁₂ v v ≤
              C * ‖(W1pVanishingOn.valueL (mu := mu) (Omega := Omega) (p := 2)
                (Γ := Γ)).toLinearMap v‖ ^ 2} := by
    simp only [mem_ofPred_eq, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
      mixedForm_apply, real_inner_self_eq_norm_sq, ContinuousLinearMap.coe_coe,
      W1pVanishingOn.valueL_apply, add_mul, add_le_add_iff_right]
  exact ⟨(hmem _).2 h.1, fun C hC ↦ le_of_add_le_add_right (h.2 ((hmem C).1 hC))⟩

/-- **The Courant–Fischer min–max principle for the mixed eigenvalues.** Let the energy form `a`
be symmetric on `H¹_Γ(Ω)` and bounded below there, `a(v, v) ≥ -ω ‖v‖²_{L²}`, and let
`κ₀ ≤ κ₁ ≤ ⋯` be eigenvalues with eigenfunctions `uⱼ ∈ H¹_Γ(Ω)`,
`a(uⱼ, v) = κⱼ ⟪uⱼ, v⟫_{L²}` for every `v ∈ H¹_Γ(Ω)`, whose values form an orthonormal basis of
`L²(Ω)`. Then `κₖ` is the `k`-th mixed eigenvalue `λₖ(Γ)`. In particular any two such listings
agree. -/
theorem mixedEigenvalue_eq_of_hilbertBasis {omega : ℝ}
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hsymm : ∀ u v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (hbdd : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      -omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2))
    (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (mu.restrict Omega))) {kappa : ℕ → ℝ}
    (hkappa : Monotone kappa) {u : ℕ → W1pVanishingOn mu Omega 2 Γ}
    (hvalue : ∀ j, W1p.value (u j : W1p mu Omega 2) = basis j)
    (heq : ∀ (j : ℕ) (v : W1pVanishingOn mu Omega 2 Γ),
      energyFormH1 a b c (u j : W1p mu Omega 2) (v : W1p mu Omega 2) =
        kappa j * ⟪W1p.value (u j : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ)
    (k : ℕ) :
    mixedEigenvalue mu Omega Γ a b c k = kappa k :=
  (isLeast_of_hilbertBasis hcoeff hsymm hbdd basis hkappa hvalue heq k).csInf_eq

/-- A form coercive after the shift by `ω` is bounded below by `-ω ‖v‖²_{L²}`. -/
private theorem neg_mul_norm_sq_le_energyFormH1 {omega : ℝ}
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ omega)) (v : W1pVanishingOn mu Omega 2 Γ) :
    -omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2 ≤
      energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) := by
  have h := hB.apply_self_nonneg v
  rw [mixedForm_apply, real_inner_self_eq_norm_sq] at h
  linarith

/-! ### The mixed eigenvalues under the Rellich property -/

section Rellich

variable [Nonempty ι] {omega : ℝ}
  (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
  (hB : IsCoercive (mixedForm hcoeff Γ omega)) (hΓ : Disjoint Γ Omega)
  (hsymm : ∀ u v : W1pVanishingOn mu Omega 2 Γ,
    energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
      energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
  (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
  (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty)
include hB hΓ hsymm hK hOmega

/-- The eigenbasis of the shifted form along the value map, listed with its eigenvalues in
nondecreasing order. The eigenvalues have finite sublevel sets and exhaust the mixed spectrum. -/
private theorem exists_hilbertBasis_nat_monotone :
    ∃ (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (mu.restrict Omega))) (kappa : ℕ → ℝ)
      (u : ℕ → W1pVanishingOn mu Omega 2 Γ),
      Monotone kappa ∧ Tendsto kappa atTop atTop ∧
      (∀ k, W1p.value (u k : W1p mu Omega 2) = basis k) ∧
      (∀ (k : ℕ) (v : W1pVanishingOn mu Omega 2 Γ),
        energyFormH1 a b c (u k : W1p mu Omega 2) (v : W1p mu Omega 2) =
          kappa k * ⟪W1p.value (u k : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ) ∧
      ∀ kappa' : ℝ, (∃ w : W1pVanishingOn mu Omega 2 Γ, w ≠ 0 ∧
        ∀ v : W1pVanishingOn mu Omega 2 Γ,
          energyFormH1 a b c (w : W1p mu Omega 2) (v : W1p mu Omega 2) =
            kappa' * ⟪W1p.value (w : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ) ↔
        ∃ k, kappa k = kappa' := by
  obtain ⟨basis, nu, u, hmono, htendsto, -, hvalue, heq, hiff, -⟩ :=
    hB.exists_hilbertBasis_nat_monotone (W1pVanishingOn.isCompactOperator_valueL hK)
      (W1pVanishingOn.denseRange_valueL_two hΓ)
      (fun v w ↦ by rw [mixedForm_apply, mixedForm_apply, hsymm, real_inner_comm])
      (L2.not_finiteDimensional_restrict_of_isOpen mu Omega.isOpen hOmega)
  -- The eigenvalues of the energy form are those of the shifted form, shifted back by `ω`.
  have hshift (kappa : ℝ) (w : W1pVanishingOn mu Omega 2 Γ) :
      (∀ v, mixedForm hcoeff Γ omega w v =
        (kappa + omega) * ⟪W1pVanishingOn.valueL w, W1pVanishingOn.valueL v⟫_ℝ) ↔
        ∀ v : W1pVanishingOn mu Omega 2 Γ,
          energyFormH1 a b c (w : W1p mu Omega 2) (v : W1p mu Omega 2) =
            kappa * ⟪W1p.value (w : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ :=
    forall_congr' fun v ↦ by
      rw [mixedForm_apply, W1pVanishingOn.valueL_apply, W1pVanishingOn.valueL_apply, add_mul,
        add_left_inj]
  refine ⟨basis, fun k ↦ nu k - omega, u, fun i j hij ↦ sub_le_sub_right (hmono hij) _,
    by simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-omega) htendsto,
    fun k ↦ by rw [← W1pVanishingOn.valueL_apply, hvalue],
    fun k ↦ (hshift _ _).1 (by simpa only [sub_add_cancel] using heq k), fun kappa' ↦ ?_⟩
  have h := hiff (kappa' + omega)
  simp only [hshift] at h
  simpa only [sub_eq_iff_eq_add] using h

/-- **The mixed eigenvalues with an eigenbasis.** For a symmetric energy form, coercive on
`H¹_Γ(Ω)` after the shift by `ω`, on a nonempty domain with the Rellich property and for `Γ`
missing `Ω`, there is an orthonormal basis `(eₖ)` of `L²(Ω)` such that `eₖ` is the value of some
`uₖ ∈ H¹_Γ(Ω)` with `a(uₖ, v) = λₖ(Γ) ⟪uₖ, v⟫_{L²}` for every `v ∈ H¹_Γ(Ω)`, where `λₖ(Γ)` is the
min–max eigenvalue `TauCeti.PDE.mixedEigenvalue`. In this basis the solution operator `S` of the
shifted mixed problem is diagonal, `S f = ∑ₖ (λₖ(Γ) + ω)⁻¹ ⟪eₖ, f⟫ eₖ`. -/
theorem exists_hilbertBasis_mixedEigenvalue :
    ∃ (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (mu.restrict Omega)))
      (u : ℕ → W1pVanishingOn mu Omega 2 Γ),
      (∀ k, W1p.value (u k : W1p mu Omega 2) = basis k) ∧
      (∀ (k : ℕ) (v : W1pVanishingOn mu Omega 2 Γ),
        energyFormH1 a b c (u k : W1p mu Omega 2) (v : W1p mu Omega 2) =
          mixedEigenvalue mu Omega Γ a b c k *
            ⟪W1p.value (u k : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ) ∧
      ∀ f : Lp ℝ 2 (mu.restrict Omega),
        HasSum (fun k ↦ (mixedEigenvalue mu Omega Γ a b c k + omega)⁻¹ • basis.repr f k • basis k)
          (mixedSolutionOperator hcoeff Γ hB f) := by
  obtain ⟨basis, kappa, u, hmono, -, hvalue, heq, -⟩ :=
    exists_hilbertBasis_nat_monotone hcoeff hB hΓ hsymm hK hOmega
  have hk := mixedEigenvalue_eq_of_hilbertBasis hcoeff hsymm
    (neg_mul_norm_sq_le_energyFormH1 hcoeff hB) basis hmono hvalue heq
  refine ⟨basis, u, hvalue, fun k v ↦ by rw [hk, heq], fun f ↦ ?_⟩
  -- Each basis vector is an eigenvector of `S` with eigenvalue `(λₖ + ω)⁻¹`.
  have hS (k : ℕ) : mixedSolutionOperator hcoeff Γ hB (basis k) =
      (mixedEigenvalue mu Omega Γ a b c k + omega)⁻¹ • basis k := by
    rw [hk]
    -- `kappa k + ω` is an eigenvalue of the coercive shifted form, hence positive.
    have hpos : kappa k + omega ≠ 0 :=
      (hB.pos_of_forall_apply_eq_smul_inner W1pVanishingOn.valueL (u := u k)
        (fun h0 ↦ basis.orthonormal.ne_zero k (by
          rw [← hvalue k, h0, ZeroMemClass.coe_zero, W1p.value_zero]))
        fun v ↦ by
          rw [mixedForm_apply, W1pVanishingOn.valueL_apply, W1pVanishingOn.valueL_apply, heq,
            add_mul]).ne'
    refine (mixedSolutionOperator_apply_eq hcoeff hB (f := basis k)
      (u := (kappa k + omega)⁻¹ • u k) fun v ↦ ?_).trans ?_
    · rw [Submodule.coe_smul, energyFormH1_smul_left, heq, W1p.value_smul, real_inner_smul_left,
        hvalue]
      field_simp
    · rw [Submodule.coe_smul, W1p.value_smul, hvalue]
  exact (mixedSolutionOperator hcoeff Γ hB).hasSum_smul_repr_of_apply_eq_smul basis _ hS f

/-- **The min–max principle is attained.** For a symmetric energy form, coercive on `H¹_Γ(Ω)`
after a shift, on a nonempty domain with the Rellich property and for `Γ` missing `Ω`, `λₖ(Γ)` is
the least `C` for which some subspace `W` of `H¹_Γ(Ω)`, whose values span a subspace of `L²(Ω)`
of dimension at least `k + 1`, satisfies `a(v, v) ≤ C ‖v‖²_{L²(Ω)}` for every `v ∈ W`. -/
theorem isLeast_mixedEigenvalue (k : ℕ) :
    IsLeast {C : ℝ | ∃ W : Submodule ℝ (W1pVanishingOn mu Omega 2 Γ),
      k + 1 ≤ Module.finrank ℝ
        (W.map (W1pVanishingOn.valueL (mu := mu) (Omega := Omega) (p := 2) (Γ := Γ)).toLinearMap) ∧
        ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
          C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2} (mixedEigenvalue mu Omega Γ a b c k) := by
  obtain ⟨basis, kappa, u, hmono, -, hvalue, heq, -⟩ :=
    exists_hilbertBasis_nat_monotone hcoeff hB hΓ hsymm hK hOmega
  have hbdd := neg_mul_norm_sq_le_energyFormH1 hcoeff hB
  rw [mixedEigenvalue_eq_of_hilbertBasis hcoeff hsymm hbdd basis hmono hvalue heq]
  exact isLeast_of_hilbertBasis hcoeff hsymm hbdd basis hmono hvalue heq k

/-- Under the Rellich property the mixed eigenvalues `λₖ(Γ)` have the properties of the
nondecreasing listing of the mixed spectrum given by the eigenbasis. -/
private theorem mixedEigenvalue_properties :
    Monotone (mixedEigenvalue mu Omega Γ a b c) ∧
      Tendsto (mixedEigenvalue mu Omega Γ a b c) atTop atTop ∧
      ∀ kappa' : ℝ, (∃ w : W1pVanishingOn mu Omega 2 Γ, w ≠ 0 ∧
        ∀ v : W1pVanishingOn mu Omega 2 Γ,
          energyFormH1 a b c (w : W1p mu Omega 2) (v : W1p mu Omega 2) =
            kappa' * ⟪W1p.value (w : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ) ↔
        ∃ k, mixedEigenvalue mu Omega Γ a b c k = kappa' := by
  obtain ⟨basis, kappa, u, hmono, htendsto, hvalue, heq, hiff⟩ :=
    exists_hilbertBasis_nat_monotone hcoeff hB hΓ hsymm hK hOmega
  obtain rfl : mixedEigenvalue mu Omega Γ a b c = kappa :=
    funext <| mixedEigenvalue_eq_of_hilbertBasis hcoeff hsymm
      (neg_mul_norm_sq_le_energyFormH1 hcoeff hB) basis hmono hvalue heq
  exact ⟨hmono, htendsto, hiff⟩

/-- The mixed eigenvalues are nondecreasing: `λ₀(Γ) ≤ λ₁(Γ) ≤ ⋯`. -/
theorem monotone_mixedEigenvalue : Monotone (mixedEigenvalue mu Omega Γ a b c) :=
  (mixedEigenvalue_properties hcoeff hB hΓ hsymm hK hOmega).1

/-- The mixed eigenvalues tend to infinity. -/
theorem tendsto_mixedEigenvalue_atTop : Tendsto (mixedEigenvalue mu Omega Γ a b c) atTop atTop :=
  (mixedEigenvalue_properties hcoeff hB hΓ hsymm hK hOmega).2.1

/-- **The mixed eigenvalues `λₖ(Γ)` are exactly the mixed spectrum**: `a(w, v) = κ ⟪w, v⟫_{L²}`
has a nonzero solution `w ∈ H¹_Γ(Ω)` for every `v ∈ H¹_Γ(Ω)` exactly when `κ = λₖ(Γ)` for
some `k`. -/
theorem exists_ne_zero_forall_energyFormH1_eq_iff_exists_mixedEigenvalue_eq (kappa' : ℝ) :
    (∃ w : W1pVanishingOn mu Omega 2 Γ, w ≠ 0 ∧ ∀ v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (w : W1p mu Omega 2) (v : W1p mu Omega 2) =
        kappa' * ⟪W1p.value (w : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ) ↔
      ∃ k, mixedEigenvalue mu Omega Γ a b c k = kappa' :=
  (mixedEigenvalue_properties hcoeff hB hΓ hsymm hK hOmega).2.2 kappa'

/-- **The spectrum of the mixed realization is the sequence of mixed eigenvalues**
`{λ₀(Γ), λ₁(Γ), …}`. -/
theorem spectrum_mixedOperator_eq_range :
    (mixedOperator hcoeff Γ).spectrum = range (mixedEigenvalue mu Omega Γ a b c) := by
  obtain ⟨theta, htheta, hgarding⟩ := hB
  ext kappa'
  rw [mem_spectrum_mixedOperator_iff hcoeff hΓ htheta (omega := omega) (fun v ↦ by
      have h := hgarding v
      rwa [mixedForm_apply, real_inner_self_eq_norm_sq, mul_assoc, ← sq] at h) hK,
    exists_ne_zero_forall_energyFormH1_eq_iff_exists_mixedEigenvalue_eq hcoeff
      ⟨theta, htheta, hgarding⟩ hΓ hsymm hK hOmega, mem_range]

end Rellich

/-! ### Monotonicity in the boundary part -/

/-- **Monotonicity of the mixed eigenvalues in `Γ`.** If `Γ ⊆ Γ'` and `Γ'` misses `Ω`, then
`λₖ(Γ) ≤ λₖ(Γ')` for every `k`: the Dirichlet condition on the larger set `Γ'` raises every
eigenvalue. The hypotheses are on the larger space `H¹_Γ(Ω) ⊇ H¹_{Γ'}(Ω)`, a symmetric energy
form coercive there after the shift by `ω`, on a nonempty domain with the Rellich property. -/
theorem mixedEigenvalue_mono [Nonempty ι] {omega : ℝ}
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ omega)) (hΓΓ' : Γ ⊆ Γ') (hΓ' : Disjoint Γ' Omega)
    (hsymm : ∀ u v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) (k : ℕ) :
    mixedEigenvalue mu Omega Γ a b c k ≤ mixedEigenvalue mu Omega Γ' a b c k := by
  have hle : (w1pVanishingOnSubmodule mu Omega 2 Γ').toSubmodule ≤
      (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule :=
    ClosedSubmodule.toSubmodule_le_toSubmodule.2 (w1pVanishingOnSubmodule_antitone hΓΓ')
  let i := Submodule.inclusion hle
  -- The hypotheses pass to the subspace `H¹_{Γ'}(Ω)`.
  have hB' : IsCoercive (mixedForm hcoeff Γ' omega) := by
    obtain ⟨C, hC, hbound⟩ := hB
    refine ⟨C, hC, fun v ↦ ?_⟩
    have hn : ‖i v‖ = ‖v‖ := by
      rw [← Submodule.norm_coe, ← Submodule.norm_coe v, Submodule.coe_inclusion]
    simpa only [mixedForm_apply, hn, i, Submodule.coe_inclusion] using hbound (i v)
  have hsymm' (u v : W1pVanishingOn mu Omega 2 Γ') :
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2) :=
    hsymm (i u) (i v)
  have hvalue : (W1pVanishingOn.valueL (mu := mu) (Omega := Omega) (p := 2) (Γ := Γ)).toLinearMap
      ∘ₗ i = (W1pVanishingOn.valueL (mu := mu) (Omega := Omega) (p := 2) (Γ := Γ')).toLinearMap :=
    LinearMap.ext fun v ↦ by
      simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
        W1pVanishingOn.valueL_apply, i, Submodule.coe_inclusion]
  -- A subspace admissible for `Γ'` is admissible for `Γ`, with the same constant.
  refine csInf_le_csInf
    (isLeast_mixedEigenvalue hcoeff hB (hΓ'.mono_left hΓΓ') hsymm hK hOmega k).bddBelow
    (isLeast_mixedEigenvalue hcoeff hB' hΓ' hsymm' hK hOmega k).nonempty ?_
  rintro C ⟨W, hW, hC⟩
  refine ⟨W.map i, by rwa [← Submodule.map_comp, hvalue], ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  exact hC v hv

/-! ### The mixed Laplacian -/

section Laplacian

variable [DecidableEq ι]

/-- The mixed form of `-Δ` shifted by `1` is the inner product of `H¹(Ω)`, hence coercive. -/
private theorem isCoercive_mixedForm_laplacian_one :
    IsCoercive (mixedForm (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ 1) :=
  isCoercive_mixedForm _ (lt_min one_pos one_pos)
    fun v ↦ min_mul_norm_sq_le_energyFormH1_one_zero_zero_add 1 (v : W1p mu Omega 2)

/-- **The mixed eigenvalues of `-Δ` with an eigenbasis.** On a nonempty domain with the Rellich
property, for `Γ` missing `Ω`, there is an orthonormal basis `(eₖ)` of `L²(Ω)` such that `eₖ` is
the value of some `uₖ ∈ H¹_Γ(Ω)` with `∫_Ω ∇uₖ · ∇v = λₖ(Γ) ∫_Ω uₖ v` for every
`v ∈ H¹_Γ(Ω)`. -/
theorem exists_hilbertBasis_mixedEigenvalue_laplacian [Nonempty ι] (hΓ : Disjoint Γ Omega)
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) :
    ∃ (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (mu.restrict Omega)))
      (u : ℕ → W1pVanishingOn mu Omega 2 Γ),
      (∀ k, W1p.value (u k : W1p mu Omega 2) = basis k) ∧
      ∀ (k : ℕ) (v : W1pVanishingOn mu Omega 2 Γ),
        ⟪W1p.gradient (u k : W1p mu Omega 2), W1p.gradient (v : W1p mu Omega 2)⟫_ℝ =
          mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0 k *
            ⟪W1p.value (u k : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  obtain ⟨basis, u, hvalue, heq, -⟩ := exists_hilbertBasis_mixedEigenvalue _
    isCoercive_mixedForm_laplacian_one hΓ (fun _ _ ↦ energyFormH1_one_zero_zero_comm _ _) hK
    hOmega
  exact ⟨basis, u, hvalue, fun k v ↦ by rw [← energyFormH1_one_zero_zero_eq_inner, heq]⟩

/-- **The mixed eigenvalues of `-Δ` are nonnegative**: `λₖ(Γ) = ∫_Ω |∇uₖ|²` for an eigenfunction
`uₖ` of unit `L²` norm. -/
theorem mixedEigenvalue_laplacian_nonneg [Nonempty ι] (hΓ : Disjoint Γ Omega)
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) (k : ℕ) :
    0 ≤ mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0 k := by
  obtain ⟨basis, u, hvalue, heq⟩ := exists_hilbertBasis_mixedEigenvalue_laplacian hΓ hK hOmega
  have h := heq k (u k)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hvalue, basis.orthonormal.1 k,
    one_pow, mul_one] at h
  exact h ▸ sq_nonneg _

/-- **Monotonicity of the mixed eigenvalues of `-Δ` in `Γ`.** On a nonempty domain with the
Rellich property, if `Γ ⊆ Γ'` and `Γ'` misses `Ω`, then `λₖ(Γ) ≤ λₖ(Γ')`. -/
theorem mixedEigenvalue_laplacian_mono [Nonempty ι] (hΓΓ' : Γ ⊆ Γ') (hΓ' : Disjoint Γ' Omega)
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) (k : ℕ) :
    mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0 k ≤ mixedEigenvalue mu Omega Γ' (fun _ ↦ 1) 0 0 k :=
  mixedEigenvalue_mono _ isCoercive_mixedForm_laplacian_one hΓΓ' hΓ'
    (fun _ _ ↦ energyFormH1_one_zero_zero_comm _ _) hK hOmega k

/-- **The mixed eigenvalues of `-Δ` lie below the Dirichlet eigenvalues.** On a nonempty domain
with the Rellich property, for every `Γ ⊆ ∂Ω`, `λₖ(Γ)` is at most the `k`-th Dirichlet
eigenvalue. -/
theorem mixedEigenvalue_laplacian_le_dirichletEigenvalue [Nonempty ι]
    (hΓ : Γ ⊆ frontier (Omega : Set (EuclideanSpace ℝ ι)))
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) (k : ℕ) :
    mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0 k ≤ dirichletEigenvalue mu Omega (fun _ ↦ 1) 0 0 k :=
  (mixedEigenvalue_laplacian_mono hΓ (disjoint_frontier_iff_isOpen.2 Omega.isOpen) hK hOmega
    k).trans_eq (mixedEigenvalue_frontier k)

/-- **The least mixed eigenvalue of `-Δ` with `Γ = ∅` is `0`** (the Neumann eigenvalue where
`H¹_∅(Ω) = H¹(Ω)`). On a nonempty bounded domain with the Rellich property, `λ₀(∅) = 0`, with the
constants as eigenfunctions. -/
theorem mixedEigenvalue_laplacian_empty_zero [Nonempty ι]
    (hb : IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) :
    mixedEigenvalue mu Omega ∅ (fun _ ↦ 1) 0 0 0 = 0 := by
  have hspec := spectrum_mixedOperator_eq_range _
    (isCoercive_mixedForm_laplacian_one (mu := mu) (Omega := Omega) (Γ := ∅))
    (empty_disjoint _) (fun _ _ ↦ energyFormH1_one_zero_zero_comm _ _) hK hOmega
  obtain ⟨k, hk⟩ := hspec ▸ (isLeast_spectrum_mixedOperator_laplacian_empty hb hOmega).1
  refine le_antisymm ?_ (mixedEigenvalue_laplacian_nonneg (empty_disjoint _) hK hOmega 0)
  exact hk ▸ monotone_mixedEigenvalue _ (isCoercive_mixedForm_laplacian_one (Γ := ∅))
    (empty_disjoint _) (fun _ _ ↦ energyFormH1_one_zero_zero_comm _ _) hK hOmega k.zero_le

end Laplacian

end PDE

end TauCeti

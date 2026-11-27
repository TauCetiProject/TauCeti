/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Schmidt
public import TauCeti.Analysis.PDE.Spectrum.Basic
public import TauCeti.MeasureTheory.Function.L2Space

/-!
# The Dirichlet eigenvalues as a sequence

Let `Ω ⊆ ℝⁿ`, `n ≥ 1`, be a nonempty bounded open set and let `L` be a divergence-form operator
whose energy form `a` is symmetric and coercive on `H¹₀(Ω)`, for instance `-Δ`. The Dirichlet
eigenvalues of `L` then form a sequence

`0 < λ₀ ≤ λ₁ ≤ λ₂ ≤ ⋯ → ∞`,

repeated according to multiplicity, and there is an orthonormal basis `(eₖ)` of `L²(Ω)`, indexed
by `ℕ`, in which `eₖ` is the value of a weak solution `uₖ ∈ H¹₀(Ω)` of `L uₖ = λₖ uₖ`
(`TauCeti.PDE.exists_hilbertBasis_nat_isDirichletEigenvalue_monotone`). The sequence exhausts the
Dirichlet spectrum: a real number is a Dirichlet eigenvalue exactly when it is some `λₖ`, and the
first term `λ₀` is the first Dirichlet eigenvalue, the minimum of the Rayleigh quotient. For `-Δ`
on a nonempty bounded open subset of `ℝ^{n+1}` this is
`TauCeti.PDE.exists_hilbertBasis_nat_isDirichletEigenvalue_laplacian_monotone`, which also records
that `λ₀` is the optimal constant in the Poincaré inequality `C ‖u‖²_{L²(Ω)} ≤ a(u, u)` on
`H¹₀(Ω)`.

The eigenvalues are indexed by `ℕ` with `λₖ → ∞` because

* `L²(Ω)` is infinite-dimensional, `Ω` being a nonempty open set in positive dimension
  (`MeasureTheory.L2.not_finiteDimensional_restrict_of_isOpen`), so every orthonormal basis of
  `L²(Ω)` is infinite;
* the solution operator `S` of the Dirichlet problem is compact on a bounded domain and acts on
  the eigenbasis by `S eₖ = λₖ⁻¹ eₖ`, so only finitely many basis vectors have `λₖ⁻¹` above any
  positive threshold (`Orthonormal.finite_setOf_le_norm_apply`), that is, every sublevel set of
  the eigenvalues is finite.

Any infinite family with finite sublevel sets can be listed in nondecreasing order
(`exists_equiv_monotone_comp_of_finite_setOf_le`), and reindexing the eigenbasis along that
enumeration gives the sequence. This is the abstract
`IsCoercive.exists_hilbertBasis_nat_monotone`, applied to the energy form on `H¹₀(Ω)` and the
value map `H¹₀(Ω) → L²(Ω)`. In dimension zero `L²(Ω)` is one-dimensional and the spectrum is a
single eigenvalue, which is why positive dimension is assumed.

## Main declarations

* `TauCeti.PDE.exists_hilbertBasis_nat_isDirichletEigenvalue_monotone`: the Dirichlet eigenvalues
  of a symmetric coercive energy form on a nonempty bounded domain, as a nondecreasing sequence
  tending to infinity with an orthonormal eigenbasis of `L²(Ω)`.
* `TauCeti.PDE.exists_hilbertBasis_nat_isDirichletEigenvalue_laplacian_monotone`: the same for
  `-Δ`, with `λ₀ > 0` the optimal Poincaré constant.

## References

L. C. Evans, *Partial Differential Equations*, Section 6.5.1, Theorem 1; D. Gilbarg and
N. Trudinger, *Elliptic Partial Differential Equations of Second Order*, Section 8.12.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Bornology Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace

section Domain

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

/-- **The Dirichlet eigenvalues form a sequence `0 < λ₀ ≤ λ₁ ≤ ⋯ → ∞`.** Let `Ω ⊆ ℝⁿ`, `n ≥ 1`,
be a nonempty bounded open set and let the energy form `a` of `L` be symmetric and coercive on
`H¹₀(Ω)`. Then there are a nondecreasing sequence `λₖ` tending to infinity and an orthonormal
basis `(eₖ)` of `L²(Ω)` such that `eₖ` is the value of some `uₖ ∈ H¹₀(Ω)` with

`a(uₖ, v) = λₖ ∫_Ω uₖ v` for every `v ∈ H¹₀(Ω)`.

The sequence lists the Dirichlet spectrum with multiplicity: `κ` is a Dirichlet eigenvalue exactly
when `κ = λₖ` for some `k`, and `λ₀` is the first Dirichlet eigenvalue, positive by
`TauCeti.PDE.firstDirichletEigenvalue_pos`. In this basis the solution operator of the Dirichlet
problem is diagonal, `S f = ∑ₖ λₖ⁻¹ ⟪eₖ, f⟫ eₖ`. -/
theorem exists_hilbertBasis_nat_isDirichletEigenvalue_monotone [Nonempty ι]
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (hsymm : ∀ u v : W1p0 mu Omega 2,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (hOmega_nonempty : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) :
    ∃ (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (mu.restrict Omega))) (kappa : ℕ → ℝ)
      (u : ℕ → W1p0 mu Omega 2),
      Monotone kappa ∧ Tendsto kappa atTop atTop ∧
      kappa 0 = firstDirichletEigenvalue hcoeff hcoercive ∧
      (∀ k, W1p.value (u k : W1p mu Omega 2) = basis k) ∧
      (∀ (k : ℕ) (v : W1p0 mu Omega 2),
        energyFormH1 a b c (u k : W1p mu Omega 2) (v : W1p mu Omega 2) =
          kappa k * ⟪W1p.value (u k : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ) ∧
      (∀ kappa' : ℝ, IsDirichletEigenvalue mu Omega a b c kappa' ↔ ∃ k, kappa k = kappa') ∧
      ∀ f : Lp ℝ 2 (mu.restrict Omega),
        HasSum (fun k ↦ (kappa k)⁻¹ • basis.repr f k • basis k)
          (dirichletSolutionOperator hcoeff hcoercive f) := by
  obtain ⟨basis, kappa, u, he, htendsto, -, hvalue, heq, hiff, hsum⟩ :=
    hcoercive.exists_hilbertBasis_nat_monotone (W1p0.isCompactOperator_valueL (by simp) hOmega)
      W1p0.denseRange_valueL_two (energyFormH1L0_comm hcoeff hsymm)
      (L2.not_finiteDimensional_restrict_of_isOpen mu Omega.isOpen hOmega_nonempty)
  have hvalue' (k : ℕ) : W1p.value (u k : W1p mu Omega 2) = basis k := by
    simpa only [W1p0.valueL_apply] using hvalue k
  have heq' (k : ℕ) (v : W1p0 mu Omega 2) :
      energyFormH1 a b c (u k : W1p mu Omega 2) (v : W1p mu Omega 2) =
        kappa k * ⟪W1p.value (u k : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
    simpa only [energyFormH1L0_apply, W1p0.valueL_apply] using heq k v
  have hiff' (kappa' : ℝ) :
      IsDirichletEigenvalue mu Omega a b c kappa' ↔ ∃ k, kappa k = kappa' := by
    simpa only [isDirichletEigenvalue_iff, energyFormH1L0_apply, W1p0.valueL_apply] using
      hiff kappa'
  refine ⟨basis, kappa, u, he, htendsto, ?_, hvalue', heq', hiff', by
    rwa [dirichletSolutionOperator_def]⟩
  obtain ⟨k, hk⟩ := (hiff' _).1
    (isDirichletEigenvalue_first hcoeff hcoercive hOmega hsymm hOmega_nonempty)
  exact le_antisymm (hk ▸ he (Nat.zero_le k)) (firstDirichletEigenvalue_le hcoeff hcoercive
    ((hiff' _).2 ⟨0, rfl⟩))

end Domain

/-! ### The Dirichlet spectrum of `-Δ` -/

section Laplacian

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

/-- **The Dirichlet eigenvalues of `-Δ`.** On a nonempty bounded open set `Ω ⊆ ℝ^{n+1}` the
Dirichlet eigenvalues of `-Δ` form a sequence `0 < λ₀ ≤ λ₁ ≤ ⋯ → ∞`, repeated according to
multiplicity, with an orthonormal basis `(eₖ)` of `L²(Ω)` such that `eₖ` is the value of a weak
solution `uₖ ∈ H¹₀(Ω)` of `-Δuₖ = λₖ uₖ`. Every Dirichlet eigenvalue of `-Δ` is some `λₖ`, and `λ₀`
is the optimal constant `C` in the Poincaré inequality `C ‖u‖²_{L²(Ω)} ≤ ∫_Ω ‖∇u‖²` on
`H¹₀(Ω)`, the Dirichlet energy `∫_Ω ‖∇u‖²` being the energy form `a(u, u)` of `-Δ`. -/
theorem exists_hilbertBasis_nat_isDirichletEigenvalue_laplacian_monotone
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hOmega_nonempty : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))).Nonempty) :
    ∃ (basis : HilbertBasis ℕ ℝ
      (Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))) (kappa : ℕ → ℝ)
      (u : ℕ → W1p0 volume Omega 2),
      0 < kappa 0 ∧ Monotone kappa ∧ Tendsto kappa atTop atTop ∧
      IsGreatest {C : ℝ | ∀ v : W1p0 volume Omega 2,
          C * ‖W1p.value (v : W1p volume Omega 2)‖ ^ 2 ≤
            energyFormH1 (fun _ ↦ 1) 0 0 (v : W1p volume Omega 2) (v : W1p volume Omega 2)}
        (kappa 0) ∧
      (∀ k, W1p.value (u k : W1p volume Omega 2) = basis k) ∧
      (∀ (k : ℕ) (v : W1p0 volume Omega 2),
        energyFormH1 (fun _ ↦ 1) 0 0 (u k : W1p volume Omega 2) (v : W1p volume Omega 2) =
          kappa k * ⟪W1p.value (u k : W1p volume Omega 2),
            W1p.value (v : W1p volume Omega 2)⟫_ℝ) ∧
      ∀ kappa' : ℝ, IsDirichletEigenvalue volume Omega (fun _ ↦ 1) 0 0 kappa' ↔
        ∃ k, kappa k = kappa' := by
  have hsymm (u v : W1p0 volume Omega 2) :
      energyFormH1 (fun _ ↦ 1) 0 0 (u : W1p volume Omega 2) (v : W1p volume Omega 2) =
        energyFormH1 (fun _ ↦ 1) 0 0 (v : W1p volume Omega 2) (u : W1p volume Omega 2) :=
    energyFormH1_comm_of_isSymm_ae (ae_of_all _ fun _ ↦ Matrix.isSymm_one) _ _
  -- Destructuring with `obtain` or rewriting with `rw` makes elaboration of this large goal time
  -- out, while `Exists.elim` and `simpa` do not.
  refine (exists_isCoercive_laplacian_of_isBounded hOmega).elim fun hcoeff hcoercive ↦ ?_
  refine (exists_hilbertBasis_nat_isDirichletEigenvalue_monotone hcoeff hcoercive hOmega hsymm
    hOmega_nonempty).elim fun basis h ↦ h.elim fun kappa h ↦ h.elim fun u h ↦
      ⟨basis, kappa, u, ?_, h.1, h.2.1, ?_, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  · simpa only [h.2.2.1] using
      firstDirichletEigenvalue_pos hcoeff hcoercive hOmega hsymm hOmega_nonempty
  · simpa only [h.2.2.1] using
      isGreatest_firstDirichletEigenvalue hcoeff hcoercive hsymm hOmega_nonempty

end Laplacian

end PDE

end TauCeti

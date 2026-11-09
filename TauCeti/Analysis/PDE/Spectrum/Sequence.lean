/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Schmidt
public import TauCeti.Analysis.PDE.Spectrum.Basic
public import TauCeti.MeasureTheory.Function.L2Space
public import TauCeti.Order.Monotone.Enumeration

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
(`exists_equiv_monotone_comp_of_finite_setOf_le`), and reindexing the eigenbasis of
`TauCeti.PDE.exists_hilbertBasis_forall_isDirichletEigenvalue` along that enumeration gives the
sequence. In dimension zero `L²(Ω)` is one-dimensional and the spectrum is a single eigenvalue,
which is why positive dimension is assumed.

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
  obtain ⟨s, B, kappa, u, hB, hpos, heig, hvalue, heq, hsum⟩ :=
    exists_hilbertBasis_forall_isDirichletEigenvalue hcoeff hcoercive hOmega hsymm
  -- The solution operator acts on the basis vector `B g` by `κ_g⁻¹`.
  have hS (g : s) :
      dirichletSolutionOperator hcoeff hcoercive (B g) = (kappa g)⁻¹ • B g := by
    classical
    refine (hsum (B g)).unique ?_
    convert hasSum_single (f := fun g' ↦ (kappa g')⁻¹ • B.repr (B g) g' • B g') g
      (fun g' hg' ↦ by simp [B.repr_self, hg']) using 1
    simp [B.repr_self]
  -- Only finitely many eigenvalues lie below any bound, by compactness of the solution operator.
  have hfin (R : ℝ) : {g : s | kappa g ≤ R}.Finite := by
    rcases le_or_gt R 0 with hR | hR
    · exact (finite_empty).subset fun g hg ↦ absurd ((hpos g).trans_le hg) hR.not_gt
    refine (B.orthonormal.finite_setOf_le_norm_apply
      (isCompactOperator_dirichletSolutionOperator hcoeff hcoercive hOmega)
      (inv_pos.2 hR)).subset fun g (hg : kappa g ≤ R) ↦ ?_
    rw [mem_ofPred_eq, hS, norm_smul, B.orthonormal.1 g, mul_one, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 (hpos g))]
    exact inv_anti₀ (hpos g) hg
  -- The basis is infinite, since `L²(Ω)` is infinite-dimensional.
  have : Infinite s := by
    rw [← not_finite_iff_infinite]
    intro hs
    have := Fintype.ofFinite s
    exact L2.not_finiteDimensional_restrict_of_isOpen (𝕜 := ℝ) mu Omega.isOpen
      hOmega_nonempty (Module.Finite.of_basis B.toOrthonormalBasis.toBasis)
  obtain ⟨e, he⟩ := exists_equiv_monotone_comp_of_finite_setOf_le kappa hfin
  -- Reindex the eigenbasis along the nondecreasing enumeration `e`.
  let basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (mu.restrict Omega)) :=
    HilbertBasis.mk (B.orthonormal.comp e e.injective)
      (by rw [e.surjective.range_comp, B.dense_span])
  have hbasis (k : ℕ) : basis k = B (e k) := by
    simp only [basis, HilbertBasis.coe_mk, Function.comp_apply]
  have hrepr (f : Lp ℝ 2 (mu.restrict Omega)) (k : ℕ) : basis.repr f k = B.repr f (e k) := by
    rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, hbasis]
  have hvalue' (g : s) : W1p.value (u g : W1p mu Omega 2) = B g := by
    rw [hvalue g, hB]
  -- A Dirichlet eigenvalue occurs in the sequence: otherwise its eigenfunction would be
  -- orthogonal to the whole eigenbasis.
  have hiff (kappa' : ℝ) :
      IsDirichletEigenvalue mu Omega a b c kappa' ↔ ∃ k, kappa (e k) = kappa' := by
    refine ⟨fun h ↦ ?_, fun ⟨k, hk⟩ ↦ hk ▸ heig (e k)⟩
    obtain ⟨w, hw, hweq⟩ := (isDirichletEigenvalue_iff _).1 h
    by_contra! hne
    have hwJ : W1p0.valueL w ≠ 0 := hcoercive.apply_ne_zero_of_forall_apply_eq_smul_inner
      W1p0.valueL hw fun v ↦ by simpa only [energyFormH1L0_apply, W1p0.valueL_apply] using hweq v
    refine hwJ (B.repr.map_eq_zero_iff.1 (lp.ext (funext fun g ↦ ?_)))
    have hg : kappa g ≠ kappa' := by simpa using hne (e.symm g)
    have h := hsymm w (u g)
    rw [hweq, heq, hvalue', real_inner_comm] at h
    rw [HilbertBasis.repr_apply_apply, W1p0.valueL_apply, lp.coeFn_zero, Pi.zero_apply]
    exact (mul_eq_mul_right_iff.1 h.symm).resolve_left hg
  refine ⟨basis, kappa ∘ e, u ∘ e, he, tendsto_comp_atTop_of_finite_setOf_le hfin e.injective,
    ?_, fun k ↦ by rw [hbasis]; exact hvalue' (e k), fun k v ↦ heq (e k) v, hiff,
    fun f ↦ ?_⟩
  · obtain ⟨k, hk⟩ := (hiff _).1
      (isDirichletEigenvalue_first hcoeff hcoercive hOmega hsymm hOmega_nonempty)
    exact le_antisymm (hk ▸ he (Nat.zero_le k)) (firstDirichletEigenvalue_le hcoeff hcoercive
      (heig (e 0)))
  · convert (e.hasSum_iff).2 (hsum f) using 1
    funext k
    simp only [Function.comp_apply, hrepr, hbasis]

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

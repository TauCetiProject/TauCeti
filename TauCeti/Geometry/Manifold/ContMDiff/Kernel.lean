/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.Module.Projective
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Smoothly varying kernels of constant-rank operator families

Let `A y : E →L[𝕜] G` be a family of operators between finite-dimensional spaces, depending `C^n`
on a point `y` of a manifold, whose kernels all have the same dimension `k` on an open set `U`.
Then near every point of `U` the kernels are spanned by `k` linearly independent vectors which
depend `C^n` on `y` (`ContMDiffOn.exists_contMDiffOn_basis_ker`).

Fix `x₀ ∈ U`, write `R` for the range of `A x₀`, and choose a linear projection `ψ : G → R` and a
right inverse `κ : R → E` of `A x₀` over `R`. The compression `Q y = ψ ∘ A y ∘ κ` of `A y` to `R`
is the identity at `x₀`, hence invertible near `x₀`, and there the operator

`T y = 1 - κ ∘ (Q y)⁻¹ ∘ ψ ∘ A y`

maps `ker (A x₀)` injectively into `ker (ψ ∘ A y)`. Since `ψ ∘ A y` is onto `R`, its kernel has
dimension `dim E - dim R = k`, so it is the image of `ker (A x₀)` under `T y`; it also contains
`ker (A y)`, which has the same dimension `k`. Hence `T y` carries a basis of `ker (A x₀)` to a
basis of `ker (A y)`, and these vectors depend `C^n` on `y` because operator inversion is
analytic.

The constant-rank hypothesis cannot be dropped: for `A y = y • 1` on `𝕜`, the kernel is `𝕜` at
`y = 0` and zero elsewhere, so it has no continuous local basis at `0`.

This is the local frame construction for the kernel of a constant-rank bundle homomorphism,
read in local trivializations; it gives, for instance, the smoothness of the kernel distribution
of a two-form of constant rank.

## Main results

* `ContMDiffOn.exists_contMDiffOn_basis_ker`: the kernels of a `C^n` family of operators of
  constant rank have `C^n` local bases.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 10
  (kernels and images of constant-rank bundle homomorphisms are smooth subbundles).
-/

public section

noncomputable section

open Function Module Set
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] {I : ModelWithCorners 𝕜 EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G] {n : ℕ∞ω}

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 G] in
/-- The linear algebra behind `ContMDiffOn.exists_contMDiffOn_basis_ker`. Let `ψ : G → R` and
`κ : R → E` compress `A₀ : E → G` to the identity of `R`, where `dim R + dim ker A₀ = dim E`. If
the compression `ψ ∘ A ∘ κ` of a second operator `A` is invertible and `ker A` has the dimension of
`ker A₀`, then `T = 1 - κ ∘ (ψ ∘ A ∘ κ)⁻¹ ∘ ψ ∘ A` carries every basis of `ker A₀` to a basis of
`ker A`. -/
private theorem linearIndependent_and_span_eq_ker {R : Type*} [NormedAddCommGroup R]
    [NormedSpace 𝕜 R] {A₀ A : E →L[𝕜] G} {ψ : G →L[𝕜] R} {κ : R →L[𝕜] E}
    (hψκ : ∀ z, ψ (A₀ (κ z)) = z) (hR : finrank 𝕜 R + finrank 𝕜 A₀.ker = finrank 𝕜 E)
    (hA : finrank 𝕜 A.ker = finrank 𝕜 A₀.ker) (hQ : IsUnit (ψ ∘L A ∘L κ)) {T : E →L[𝕜] E}
    (hT : T = ContinuousLinearMap.id 𝕜 E - κ ∘L Ring.inverse (ψ ∘L A ∘L κ) ∘L ψ ∘L A) {k : ℕ}
    (b : Basis (Fin k) 𝕜 A₀.ker) :
    LinearIndependent 𝕜 (fun i ↦ T (b i)) ∧ Submodule.span 𝕜 (range fun i ↦ T (b i)) = A.ker := by
  have hQinv (z : R) : ψ (A (κ (Ring.inverse (ψ ∘L A ∘L κ) z))) = z := by
    simpa using congrArg (fun L : R →L[𝕜] R ↦ L z) (Ring.mul_inverse_cancel _ hQ)
  -- `T` maps `E` into `ker (ψ ∘ A)`.
  have hψAT (u : E) : ψ (A (T u)) = 0 := by
    simp [hT, hQinv]
  -- `T` is injective on `ker A₀`: its defect lies in the range of `κ`, which meets `ker A₀`
  -- only in `0`.
  have hTinj {u : E} (hu : A₀ u = 0) (hTu : T u = 0) : u = 0 := by
    have hκ : u = κ (Ring.inverse (ψ ∘L A ∘L κ) (ψ (A u))) := by
      simpa [hT, sub_eq_zero] using hTu
    have hz : Ring.inverse (ψ ∘L A ∘L κ) (ψ (A u)) = 0 := by
      rw [← hψκ (Ring.inverse (ψ ∘L A ∘L κ) (ψ (A u))), ← hκ, hu, map_zero]
    rw [hκ, hz, map_zero]
  -- `ψ ∘ A` is onto `R`, so its kernel has dimension `dim E - dim R = k`.
  have hk : finrank 𝕜 A₀.ker = k := by
    rw [finrank_eq_card_basis b, Fintype.card_fin]
  have hkerψA : finrank 𝕜 (ψ ∘L A).ker = k := by
    have hsurj : LinearMap.range (ψ ∘L A : E →ₗ[𝕜] R) = ⊤ :=
      LinearMap.range_eq_top.mpr fun z ↦ ⟨κ (Ring.inverse (ψ ∘L A ∘L κ) z), hQinv z⟩
    have h := LinearMap.finrank_range_add_finrank_ker (ψ ∘L A : E →ₗ[𝕜] R)
    rw [hsurj, finrank_top] at h
    omega
  have hli : LinearIndependent 𝕜 fun i ↦ T (b i) :=
    b.linearIndependent.map' ((T : E →ₗ[𝕜] E) ∘ₗ A₀.ker.subtype)
      (LinearMap.ker_eq_bot'.mpr fun u hu ↦ Subtype.ext (hTinj (LinearMap.mem_ker.mp u.2) hu))
  refine ⟨hli, ?_⟩
  -- Both the span and `ker A` are `k`-dimensional subspaces of `ker (ψ ∘ A)`.
  have hspan : Submodule.span 𝕜 (range fun i ↦ T (b i)) = (ψ ∘L A).ker := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hψAT _
    · rw [finrank_span_eq_card hli, Fintype.card_fin, hkerψA]
  have hker : A.ker = (ψ ∘L A).ker := by
    refine Submodule.eq_of_le_of_finrank_eq (fun u hu ↦ ?_) ?_
    · exact LinearMap.mem_ker.mpr (by simpa using congrArg ψ (LinearMap.mem_ker.mp hu))
    · rw [hA, hk, hkerψA]
  rw [hspan, hker]

/-- **Kernels of constant rank vary smoothly.** Let `A y : E →L[𝕜] G` be a family of operators
between finite-dimensional spaces, `C^n` on an open set `U` of a manifold, whose kernels all have
dimension `k` on `U`. Then every point of `U` has an open neighbourhood `W ⊆ U` on which there are
`k` maps `v i : M → E`, each `C^n` on `W`, whose values at every `y ∈ W` form a basis of
`ker (A y)`. -/
theorem ContMDiffOn.exists_contMDiffOn_basis_ker {A : M → E →L[𝕜] G} {U : Set M}
    (hA : ContMDiffOn I 𝓘(𝕜, E →L[𝕜] G) n A U) (hU : IsOpen U) {k : ℕ}
    (hk : ∀ y ∈ U, finrank 𝕜 (A y).ker = k) {x₀ : M} (hx₀ : x₀ ∈ U) :
    ∃ W : Set M, IsOpen W ∧ x₀ ∈ W ∧ W ⊆ U ∧ ∃ v : Fin k → M → E,
      (∀ i, ContMDiffOn I 𝓘(𝕜, E) n (v i) W) ∧ ∀ y ∈ W,
        LinearIndependent 𝕜 (v · y) ∧
          Submodule.span 𝕜 (range (v · y)) = (A y).ker := by
  classical
  -- A projection `ψ` onto the range `R` of `A x₀`, and a right inverse `κ` of `A x₀` over `R`.
  let R := LinearMap.range (A x₀ : E →ₗ[𝕜] G)
  have : CompleteSpace R := FiniteDimensional.complete 𝕜 R
  obtain ⟨p, hp⟩ := R.subtype.exists_leftInverse_of_injective R.ker_subtype
  obtain ⟨s, hs⟩ := (A x₀ : E →ₗ[𝕜] G).rangeRestrict.exists_rightInverse_of_surjective
    (A x₀ : E →ₗ[𝕜] G).range_rangeRestrict
  let ψ : G →L[𝕜] R := LinearMap.toContinuousLinearMap p
  let κ : R →L[𝕜] E := LinearMap.toContinuousLinearMap s
  have hψκ (z : R) : ψ (A x₀ (κ z)) = z := by
    have hAs : (A x₀ (s z) : G) = z := congrArg Subtype.val (LinearMap.congr_fun hs z)
    simpa [ψ, κ, hAs] using LinearMap.congr_fun hp z
  -- The compression `Q y` of `A y` to `R` is the identity at `x₀`, hence invertible near `x₀`.
  let Q : M → R →L[𝕜] R := fun y ↦ ψ ∘L A y ∘L κ
  have hQ : ContMDiffOn I 𝓘(𝕜, R →L[𝕜] R) n Q U :=
    contMDiffOn_const.clm_comp (hA.clm_comp contMDiffOn_const)
  have hQ₀ : Q x₀ = ((1 : (R →L[𝕜] R)ˣ) : R →L[𝕜] R) := ContinuousLinearMap.ext hψκ
  let W := U ∩ Q ⁻¹' {L | IsUnit L}
  have hW : IsOpen W := hQ.continuousOn.isOpen_inter_preimage hU Units.isOpen
  have hx₀W : x₀ ∈ W := ⟨hx₀, by simp only [mem_preimage, mem_ofPred_eq, hQ₀, Units.isUnit]⟩
  -- On `W`, the operators `T y` are `C^n`, since operator inversion is analytic.
  let T : M → E →L[𝕜] E := fun y ↦ ContinuousLinearMap.id 𝕜 E - κ ∘L Ring.inverse (Q y) ∘L ψ ∘L A y
  have hinv : ContMDiffOn I 𝓘(𝕜, R →L[𝕜] R) n (fun y ↦ Ring.inverse (Q y)) W := fun y hy ↦ by
    obtain ⟨u, hu⟩ := hy.2
    have hi : ContDiffAt 𝕜 n Ring.inverse (Q y) := hu ▸ contDiffAt_ringInverse 𝕜 u
    exact hi.comp_contMDiffWithinAt ((hQ y hy.1).mono inter_subset_left)
  have hsub : ContDiff 𝕜 n fun L : E →L[𝕜] E ↦ ContinuousLinearMap.id 𝕜 E - L :=
    contDiff_const.sub contDiff_id
  have hT : ContMDiffOn I 𝓘(𝕜, E →L[𝕜] E) n T W := fun y hy ↦
    hsub.comp_contMDiffWithinAt ((contMDiffOn_const.clm_comp
      (hinv.clm_comp (contMDiffOn_const.clm_comp (hA.mono inter_subset_left)))) y hy)
  -- They carry a basis of `ker (A x₀)` to bases of the kernels `ker (A y)`.
  have hrank : finrank 𝕜 R + finrank 𝕜 (A x₀).ker = finrank 𝕜 E :=
    LinearMap.finrank_range_add_finrank_ker (A x₀ : E →ₗ[𝕜] G)
  let bK := Module.finBasisOfFinrankEq 𝕜 (A x₀).ker (hk x₀ hx₀)
  exact ⟨W, hW, hx₀W, inter_subset_left, fun i y ↦ T y (bK i),
    fun i ↦ hT.clm_apply contMDiffOn_const, fun y hy ↦ linearIndependent_and_span_eq_ker hψκ
      hrank (by rw [hk y hy.1, hk x₀ hx₀]) hy.2 rfl bK⟩

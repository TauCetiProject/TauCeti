/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Rank
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
public import TauCeti.Geometry.Symplectic.Lagrangian.Manifold

import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Common levels of Poisson-commuting functions

Let `σ` be a nondegenerate two-form on a manifold `M` modelled on a finite-dimensional space `E`,
and let `F : M → (ι → ℝ)` be a finite family of functions `F_i = F (·) i`. This file relates
the kernel of the derivative `dF_x` to the Hamiltonian vector fields `X_{F_i}`, with the conventions
`ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g) = df(X_g)`. Interpreting `ker dF_x` as the tangent
space of a common level requires regularity and a compatible level-submanifold structure, or a
parametrization satisfying the hypotheses described below:

* the symplectic complement of `ker dF_x` is the span of the vectors `X_{F_i}(x)`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.orthogonal_ker_mfderiv`), at every point where `F` is
  differentiable;
* hence `ker dF_x` is coisotropic exactly when the `F_i` pairwise Poisson-commute at `x`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isCoisotropic_ker_mfderiv_iff`), and `X_{F_j}(x)` is
  in `ker dF_x` exactly when `F_j` Poisson-commutes at `x` with every `F_i`;
* functions whose differentials at `x` vanish on `ker dF_x`, such as functions of `F`, then
  Poisson-commute at `x` as well
  (`TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_eq_zero_of_ker_le`);
* the rank of `F` at `x` (`TauCeti.mfderivRank`, the dimension of the image of `dF_x`) is the
  dimension of the span of the `X_{F_i}(x)`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.mfderivRank_eq_finrank_span_hamiltonianVectorField`), so
  the points of rank zero are the common zeros of the Hamiltonian vector fields
  (`TauCeti.SmoothTwoForm.IsNondegenerate.mfderivRank_eq_zero_iff_hamiltonianVectorField_eq_zero`);
* where the `F_i` Poisson-commute this span is isotropic, so the rank of `F` there is at most half
  the dimension of `M`, whether or not `x` is a regular point
  (`TauCeti.SmoothTwoForm.IsNondegenerate.two_mul_mfderivRank_le`);
* at a regular point of `F` (the differentials `dF_i` are independent) the `X_{F_i}(x)` are
  linearly independent, so `k` independent Poisson-commuting functions on a `2n`-dimensional
  manifold satisfy `k ≤ n`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.two_mul_card_le_finrank`);
* the kernel is then Lagrangian exactly when `k = n`, and in that case the Hamiltonian vectors
  span `ker dF_x`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isLagrangian_ker_mfderiv_iff` and
  `TauCeti.SmoothTwoForm.IsNondegenerate.ker_mfderiv_eq_span_hamiltonianVectorField`).

On the manifold level these statements apply to any parametrization of a regular common level by
an immersion from a manifold of the dimension of the level: its tangent images are the kernels of
`dF` (`TauCeti.IsRegularPoint.range_mfderiv_eq_ker_mfderiv`), so it is a coisotropic map, and a
Lagrangian map when `k = n`
(`TauCeti.SmoothTwoForm.IsNondegenerate.isCoisotropicMap_of_forall_eq` and
`TauCeti.SmoothTwoForm.IsNondegenerate.isLagrangianMap_of_forall_eq`). For a completely integrable
system this is the statement that its regular fibres, such as the invariant tori of the
Liouville–Arnold theorem, are Lagrangian.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 49.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.
-/

public section

open Module
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

namespace IsNondegenerate

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate)
  {ι : Type*} [Fintype ι] {F : M → ι → ℝ} {x : M}

include hσ

/-! ### The symplectic complement of the derivative kernel -/

/-- The symplectic complement of the span of the Hamiltonian vectors `X_{F_i}(x)` is the kernel of
`dF_x`. -/
theorem orthogonal_span_hamiltonianVectorField (hF : MDifferentiableAt I 𝓘(ℝ, ι → ℝ) F x) :
    (hσ.symplecticFormAt x).orthogonal
        (Submodule.span ℝ (Set.range fun i ↦ σ.hamiltonianVectorField (F · i) x)) =
      (mfderiv I 𝓘(ℝ, ι → ℝ) F x).ker := by
  ext v
  simp only [SymplecticForm.mem_orthogonal_span_iff, Set.forall_mem_range,
    symplecticFormAt_apply, hσ.eval₂_hamiltonianVectorField, mvfderiv_apply hF,
    ContinuousLinearMap.comp_apply, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, mvfderiv_apply_eq_mfderiv_apply]
  exact funext_iff.symm

/-- **The symplectic complement of `ker dF_x`** is spanned by the Hamiltonian vectors
`X_{F_i}(x)`. -/
theorem orthogonal_ker_mfderiv (hF : MDifferentiableAt I 𝓘(ℝ, ι → ℝ) F x) :
    (hσ.symplecticFormAt x).orthogonal (mfderiv I 𝓘(ℝ, ι → ℝ) F x).ker =
      Submodule.span ℝ (Set.range fun i ↦ σ.hamiltonianVectorField (F · i) x) := by
  rw [← hσ.orthogonal_span_hamiltonianVectorField hF, SymplecticForm.orthogonal_orthogonal]

omit hσ [FiniteDimensional ℝ E] in
/-- The Hamiltonian vector `X_{F_j}(x)` lies in `ker dF_x` exactly when `F_j`
Poisson-commutes at `x` with every `F_i`. Where the flat map is not invertible, both sides hold,
since all Hamiltonian vectors vanish. -/
theorem _root_.TauCeti.SmoothTwoForm.hamiltonianVectorField_mem_ker_mfderiv_iff
    (hF : MDifferentiableAt I 𝓘(ℝ, ι → ℝ) F x) (j : ι) :
    σ.hamiltonianVectorField (F · j) x ∈ (mfderiv I 𝓘(ℝ, ι → ℝ) F x).ker ↔
      ∀ i, σ.poissonBracket (F · i) (F · j) x = 0 := by
  by_cases hinv : (σ.flat x).IsInvertible
  · have hev (f : M → ℝ) (v : TangentSpace I x) :
        SmoothBundleForm.eval₂ σ x (σ.hamiltonianVectorField f x) v = mvfderiv I f x v := by
      rw [← flat_apply, hamiltonianVectorField_def, hinv.self_apply_inverse]
    simp only [poissonBracket_def, hev, mvfderiv_apply hF, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      mvfderiv_apply_eq_mfderiv_apply]
    exact funext_iff
  · have h0 (f : M → ℝ) : σ.hamiltonianVectorField f x = 0 := by
      rw [hamiltonianVectorField_def, ContinuousLinearMap.inverse_of_not_isInvertible hinv]
      rfl
    simp [poissonBracket_def, h0]

/-- The kernel of `dF_x` is a coisotropic subspace of `T_x M` exactly when
`{F_i, F_j}(x) = 0` for all `i` and `j`. -/
theorem isCoisotropic_ker_mfderiv_iff (hF : MDifferentiableAt I 𝓘(ℝ, ι → ℝ) F x) :
    (hσ.symplecticFormAt x).IsCoisotropic (mfderiv I 𝓘(ℝ, ι → ℝ) F x).ker ↔
      ∀ i j, σ.poissonBracket (F · i) (F · j) x = 0 := by
  rw [SymplecticForm.isCoisotropic_iff_le, hσ.orthogonal_ker_mfderiv hF,
    ← hσ.orthogonal_span_hamiltonianVectorField hF, ← SymplecticForm.isIsotropic_iff_le,
    SymplecticForm.isIsotropic_span_iff]
  simp only [Set.forall_mem_range, symplecticFormAt_apply, poissonBracket_def]

/-- **Functions of Poisson-commuting functions Poisson-commute.** If the `F_i` Poisson-commute at
`x`, then any two functions whose differentials at `x` vanish on `ker dF_x`, such as functions
`h ∘ F` of `F`, Poisson-commute at `x`. -/
theorem poissonBracket_eq_zero_of_ker_le
    (hcomm : ∀ i j, σ.poissonBracket (F · i) (F · j) x = 0) {g k : M → ℝ}
    (hg : (mfderiv I 𝓘(ℝ, ι → ℝ) F x).ker ≤ (mvfderiv I g x).ker)
    (hk : (mfderiv I 𝓘(ℝ, ι → ℝ) F x).ker ≤ (mvfderiv I k x).ker) :
    σ.poissonBracket g k x = 0 := by
  by_cases hF : MDifferentiableAt I 𝓘(ℝ, ι → ℝ) F x
  · -- `X_k` is `σ`-orthogonal to `ker dk`, hence to `ker dF`, so it lies in the coisotropic
    -- `ker dF` and therefore in `ker dg`.
    have hXk : σ.hamiltonianVectorField k x ∈ (mfderiv I 𝓘(ℝ, ι → ℝ) F x).ker :=
      SymplecticForm.isCoisotropic_iff_le.1 ((hσ.isCoisotropic_ker_mfderiv_iff hF).2 hcomm) <|
        SymplecticForm.mem_orthogonal_iff'.2 fun v hv ↦ by
          rw [symplecticFormAt_apply, hσ.eval₂_hamiltonianVectorField]
          exact hk hv
    rw [hσ.poissonBracket_eq_mvfderiv]
    exact hg hXk
  · -- If `F` is not differentiable at `x` then `dF_x = 0`, so `dk_x = 0` and `X_k(x) = 0`.
    rw [mfderiv_zero_of_not_mdifferentiableAt hF] at hk
    have hdk : mvfderiv I k x = 0 := by
      ext v
      exact hk (by simp : v ∈ ((0 : TangentSpace I x →L[ℝ] TangentSpace 𝓘(ℝ, ι → ℝ) (F x)) :
        TangentSpace I x →ₗ[ℝ] TangentSpace 𝓘(ℝ, ι → ℝ) (F x)).ker)
    rw [hσ.poissonBracket_eq_mvfderiv, hσ.hamiltonianVectorField_eq_zero_iff.2 hdk, map_zero]

/-! ### Independent functions -/

/-- At a regular point of `F`, where the differentials `dF_i` are independent, the Hamiltonian
vectors `X_{F_i}(x)` are linearly independent. -/
theorem linearIndependent_hamiltonianVectorField (hreg : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x) :
    LinearIndependent ℝ fun i ↦ σ.hamiltonianVectorField (F · i) x := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  -- Pair the relation with a tangent vector `v` on which `dF_x` takes the value `e_j`: since
  -- `σ(X_{F_i}, v) = dF_i(v)`, this extracts the coefficient `c j`.
  obtain ⟨v, hv⟩ := isRegularPoint_iff.1 hreg (Pi.single j 1)
  have hσc := congrArg (fun u ↦ SmoothForm.bilinFormAt σ x u v) hc
  simpa [SmoothForm.bilinFormAt_apply, hσ.apply_hamiltonianVectorField,
    mvfderiv_apply hreg.mdifferentiableAt, hv, Pi.single_apply] using hσc

/-- The span of the Hamiltonian vectors `X_{F_i}(x)` at a regular point of `F` has dimension the
number of functions. -/
theorem finrank_span_hamiltonianVectorField (hreg : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x) :
    finrank ℝ (Submodule.span ℝ (Set.range fun i ↦ σ.hamiltonianVectorField (F · i) x)) =
      Fintype.card ι :=
  finrank_span_eq_card (hσ.linearIndependent_hamiltonianVectorField hreg)

/-! ### The rank of a family of functions -/

/-- **The rank of a family of functions is the dimension of its Hamiltonian span.** At a point
where `F` is differentiable, the rank of `F` (the dimension of the image of `dF_x`) is the dimension
of the span of the Hamiltonian vectors `X_{F_i}(x)`. -/
theorem mfderivRank_eq_finrank_span_hamiltonianVectorField
    (hF : MDifferentiableAt I 𝓘(ℝ, ι → ℝ) F x) :
    mfderivRank I 𝓘(ℝ, ι → ℝ) F x =
      finrank ℝ (Submodule.span ℝ (Set.range fun i ↦ σ.hamiltonianVectorField (F · i) x)) := by
  rw [← hσ.orthogonal_ker_mfderiv hF, SymplecticForm.finrank_orthogonal, finrank_tangentSpace]
  have := finrank_ker_mfderiv_add_mfderivRank (I := I) (J := 𝓘(ℝ, ι → ℝ)) (f := F) (x := x)
  omega

/-- **The points of rank zero are the common zeros of the Hamiltonian vectors.** A differentiable
family `F` has rank zero at `x` exactly when every Hamiltonian vector `X_{F_i}(x)` vanishes, that
is when `x` is an equilibrium of every Hamiltonian vector field `X_{F_i}`. -/
theorem mfderivRank_eq_zero_iff_hamiltonianVectorField_eq_zero
    (hF : MDifferentiableAt I 𝓘(ℝ, ι → ℝ) F x) :
    mfderivRank I 𝓘(ℝ, ι → ℝ) F x = 0 ↔ ∀ i, σ.hamiltonianVectorField (F · i) x = 0 := by
  rw [hσ.mfderivRank_eq_finrank_span_hamiltonianVectorField hF, Submodule.finrank_eq_zero,
    Submodule.span_eq_bot, Set.forall_mem_range]

/-- **The rank bound for Poisson-commuting functions.** At a point where the functions `F_i`
Poisson-commute, the rank of `F` is at most half the dimension of `M`: the Hamiltonian vectors
`X_{F_i}(x)` span an isotropic subspace of that dimension. Where `F` is not differentiable the
rank is zero, so no differentiability of `F` is assumed. -/
theorem two_mul_mfderivRank_le (hcomm : ∀ i j, σ.poissonBracket (F · i) (F · j) x = 0) :
    2 * mfderivRank I 𝓘(ℝ, ι → ℝ) F x ≤ finrank ℝ E := by
  by_cases hF : MDifferentiableAt I 𝓘(ℝ, ι → ℝ) F x
  swap
  · simp [mfderivRank_eq_zero_of_not_mdifferentiableAt hF]
  have hiso : (hσ.symplecticFormAt x).IsIsotropic
      (Submodule.span ℝ (Set.range fun i ↦ σ.hamiltonianVectorField (F · i) x)) := by
    rw [SymplecticForm.isIsotropic_span_iff]
    simpa only [Set.forall_mem_range, symplecticFormAt_apply, poissonBracket_def] using hcomm
  have := hiso.two_mul_finrank_le
  rwa [← hσ.mfderivRank_eq_finrank_span_hamiltonianVectorField hF, finrank_tangentSpace] at this

/-- **The dimension bound for Poisson-commuting functions.** If `k` functions Poisson-commute at a
regular point of a `2n`-dimensional manifold, then `k ≤ n`. -/
theorem two_mul_card_le_finrank (hreg : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x)
    (hcomm : ∀ i j, σ.poissonBracket (F · i) (F · j) x = 0) :
    2 * Fintype.card ι ≤ finrank ℝ E := by
  have := hσ.two_mul_mfderivRank_le hcomm
  rwa [isRegularPoint_iff_mfderivRank_eq.1 hreg, Module.finrank_fintype_fun_eq_card] at this

/-- **The Lagrangian criterion for `ker dF_x`.** At a regular point of `F`
at which the `F_i` Poisson-commute, the kernel of `dF_x` is Lagrangian exactly when there are
half as many functions as the dimension of `M`. -/
theorem isLagrangian_ker_mfderiv_iff (hreg : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x)
    (hcomm : ∀ i j, σ.poissonBracket (F · i) (F · j) x = 0) :
    (hσ.symplecticFormAt x).IsLagrangian (mfderiv I 𝓘(ℝ, ι → ℝ) F x).ker ↔
      2 * Fintype.card ι = finrank ℝ E := by
  have hco := (hσ.isCoisotropic_ker_mfderiv_iff hreg.mdifferentiableAt).2 hcomm
  have hdim := hreg.finrank_ker_mfderiv_add_finrank
  rw [Module.finrank_fintype_fun_eq_card] at hdim
  refine ⟨fun h ↦ ?_, fun h ↦ hco.isLagrangian_of_finrank ?_⟩
  · have := h.two_mul_finrank
    rw [finrank_tangentSpace] at this
    omega
  · rw [finrank_tangentSpace]
    omega

/-- **The Hamiltonian vectors span the Lagrangian kernel `ker dF_x`.** At a regular point of `F`
at which `n` functions on a `2n`-dimensional manifold Poisson-commute, the Hamiltonian vectors
`X_{F_i}(x)` span the kernel of `dF_x`. -/
theorem ker_mfderiv_eq_span_hamiltonianVectorField (hreg : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x)
    (hcomm : ∀ i j, σ.poissonBracket (F · i) (F · j) x = 0)
    (hdim : 2 * Fintype.card ι = finrank ℝ E) :
    (mfderiv I 𝓘(ℝ, ι → ℝ) F x).ker =
      Submodule.span ℝ (Set.range fun i ↦ σ.hamiltonianVectorField (F · i) x) := by
  have h := (hσ.isLagrangian_ker_mfderiv_iff hreg hcomm).2 hdim
  rw [← hσ.orthogonal_ker_mfderiv hreg.mdifferentiableAt]
  exact le_antisymm (SymplecticForm.isIsotropic_iff_le.1 h.isIsotropic)
    (SymplecticForm.isCoisotropic_iff_le.1 h.isCoisotropic)

/-! ### Parametrized common levels -/

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {g : N → M} {c : ι → ℝ}

/-- **Regular common levels of Poisson-commuting functions are coisotropic.** Let `g : N → M`
map into the common level `F = c`, with injective derivatives, from a manifold of the dimension of
the level. If every point of the image is a regular point of `F` at which the `F_i`
Poisson-commute, then `g` is a coisotropic map. -/
theorem isCoisotropicMap_of_forall_eq (hg : ∀ p, F (g p) = c)
    (hreg : ∀ p, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F (g p))
    (hcomm : ∀ p i j, σ.poissonBracket (F · i) (F · j) (g p) = 0)
    (hinj : ∀ p, Function.Injective (mfderiv J I g p))
    (hdim : finrank ℝ E' + Fintype.card ι = finrank ℝ E) :
    hσ.IsCoisotropicMap J g := isCoisotropicMap_iff.2 fun p ↦ by
  have hrange := (hreg p).range_mfderiv_eq_ker_mfderiv (.of_forall hg) (hinj p)
    (by rwa [Module.finrank_fintype_fun_eq_card])
  rw [hrange]
  exact (hσ.isCoisotropic_ker_mfderiv_iff (hreg p).mdifferentiableAt).2 (hcomm p)

/-- **Regular common levels of `n` Poisson-commuting functions are Lagrangian.** Let `g : N → M`
map into the common level `F = c` of `n` functions on a `2n`-dimensional manifold, with injective
derivatives, from an `n`-dimensional manifold. If every point of the image is a regular point of
`F` at which the `F_i` Poisson-commute, then `g` is a Lagrangian map. -/
theorem isLagrangianMap_of_forall_eq (hg : ∀ p, F (g p) = c)
    (hreg : ∀ p, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F (g p))
    (hcomm : ∀ p i j, σ.poissonBracket (F · i) (F · j) (g p) = 0)
    (hinj : ∀ p, Function.Injective (mfderiv J I g p))
    (hdimN : finrank ℝ E' = Fintype.card ι) (hdim : 2 * Fintype.card ι = finrank ℝ E) :
    hσ.IsLagrangianMap J g := isLagrangianMap_iff_forall.2 fun p ↦ by
  have hrange := (hreg p).range_mfderiv_eq_ker_mfderiv (.of_forall hg) (hinj p)
    (by rw [Module.finrank_fintype_fun_eq_card]; omega)
  rw [hrange]
  exact (hσ.isLagrangian_ker_mfderiv_iff (hreg p) (hcomm p)).2 hdim

end IsNondegenerate

end SmoothTwoForm

end TauCeti

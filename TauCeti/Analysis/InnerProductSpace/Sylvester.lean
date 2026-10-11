/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PointSpectrum

/-!
# The Sylvester operator and the finite-dimensional Sylvester equation

For bounded operators `A : E →L[𝕜] E` and `B : F →L[𝕜] F`, the *Sylvester operator*
`A.sylvester B` sends `X : F →L[𝕜] E` to `A ∘L X - X ∘L B`. The Sylvester equation
`A X - X B = C` is the linear equation through which spectral gaps control the motion of spectral
subspaces under perturbation (Davis–Kahan, Bhatia–Davis–McIntosh).

When `A` is symmetric, the equation diagonalises on eigenvectors: if `A u = α u` and `B v = β v`
with `α, β` real, then `⟪u, (A X - X B) v⟫ = (α - β) ⟪u, X v⟫`. In finite dimension, choosing
orthonormal eigenbases `(uᵢ)` of `A` and `(vⱼ)` of `B` turns the equation into the scalar equations
`(αᵢ - βⱼ) Xᵢⱼ = Cᵢⱼ` on the matrix coefficients `Xᵢⱼ = ⟪uᵢ, X vⱼ⟫`. If no eigenvalue of `A` is an
eigenvalue of `B`, every `αᵢ - βⱼ` is nonzero, so the Sylvester operator is bijective and the
unique solution is obtained by dividing each coefficient of `C` by the corresponding eigenvalue
difference.

The spectral hypothesis is phrased as disjointness of the real point spectra
`Module.End.restrictedPointSpectrum A ⊤` and `Module.End.restrictedPointSpectrum B ⊤`. A positive
separation `Module.End.PointSpectraSeparated A ⊤ B ⊤ δ` with `0 < δ` supplies it through
`Module.End.PointSpectraSeparated.disjoint`.

## Main definitions

* `ContinuousLinearMap.sylvester A B`: the continuous linear map `X ↦ A ∘L X - X ∘L B` on
  `F →L[𝕜] E`.

## Main statements

* `ContinuousLinearMap.inner_sylvester_apply_of_apply_eq_smul`: for symmetric `A` and eigenvectors
  `A u = α u`, `B v = β v`, `⟪u, A.sylvester B X v⟫ = (α - β) ⟪u, X v⟫`.
* `ContinuousLinearMap.inner_sylvester_apply_eigenvectorBasis`: the same identity on the matrix
  coefficients in ordered eigenbases.
* `ContinuousLinearMap.sylvester_injective`: in finite dimension, for symmetric `A` and `B` with
  disjoint point spectra, the Sylvester operator is injective.
* `ContinuousLinearMap.sylvester_sum_eigenvectorBasis`: under the same hypotheses, dividing the
  eigenbasis coefficients of `C` by the eigenvalue differences gives a solution of
  `A X - X B = C`.
* `ContinuousLinearMap.sylvester_bijective`, `ContinuousLinearMap.sylvester_apply_eq_iff`: the
  Sylvester operator is bijective, and that coefficient formula gives the unique solution.

## References

* J. J. Sylvester, *Sur l'équation en matrices `px = xq`*, C. R. Acad. Sci. Paris **99** (1884).
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), §VII.2.
* R. Bhatia, C. Davis, A. McIntosh, *Perturbation of spectral subspaces and solution of linear
  operator equations*, Linear Algebra Appl. **52/53** (1983), 45–67.
-/

public section

open InnerProductSpace Module
open scoped InnerProductSpace

namespace ContinuousLinearMap

section Normed

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The *Sylvester operator* of `A : E →L[𝕜] E` and `B : F →L[𝕜] F`: the continuous linear map
`X ↦ A ∘L X - X ∘L B` on `F →L[𝕜] E`. Its equation `A.sylvester B X = C` is the Sylvester
equation `A X - X B = C`, and its kernel consists of the intertwiners `A X = X B`. -/
noncomputable def sylvester (A : E →L[𝕜] E) (B : F →L[𝕜] F) : (F →L[𝕜] E) →L[𝕜] F →L[𝕜] E :=
  compL 𝕜 F E E A - (compL 𝕜 F F E).flip B

@[simp]
theorem sylvester_apply (A : E →L[𝕜] E) (B : F →L[𝕜] F) (X : F →L[𝕜] E) :
    A.sylvester B X = A ∘L X - X ∘L B := by
  simp [sylvester]

end Normed

section InnerProduct

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  {A : E →L[𝕜] E} {B : F →L[𝕜] F}

/-- **The Sylvester equation on eigenvectors.** If `A` is symmetric, `A u = α u` and `B v = β v`
with `α, β` real, then the coefficient of `A X - X B` between `v` and `u` is `α - β` times that of
`X`. Only the eigenvector `u` of `A` uses symmetry. -/
theorem inner_sylvester_apply_of_apply_eq_smul (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (X : F →L[𝕜] E) {α β : ℝ} {u : E} {v : F} (hu : A u = (α : 𝕜) • u)
    (hv : B v = (β : 𝕜) • v) :
    ⟪u, A.sylvester B X v⟫_𝕜 = ((α - β : ℝ) : 𝕜) * ⟪u, X v⟫_𝕜 := by
  have hAu : ⟪u, A (X v)⟫_𝕜 = (α : 𝕜) * ⟪u, X v⟫_𝕜 := by
    rw [← coe_coe A, ← hA u (X v), coe_coe, hu, inner_smul_left, RCLike.conj_ofReal]
  simp [hAu, hv, inner_sub_right, inner_smul_right, sub_mul]

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] {n m : ℕ}

/-- **The Sylvester equation in eigenbases.** For symmetric `A` and `B` with ordered orthonormal
eigenbases `(uᵢ)`, `(vⱼ)` and eigenvalues `(αᵢ)`, `(βⱼ)`, the matrix coefficients of
`C = A X - X B` are `Cᵢⱼ = (αᵢ - βⱼ) Xᵢⱼ`, where `Xᵢⱼ = ⟪uᵢ, X vⱼ⟫`. -/
theorem inner_sylvester_apply_eigenvectorBasis (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hB : (B : F →ₗ[𝕜] F).IsSymmetric) (hn : finrank 𝕜 E = n) (hm : finrank 𝕜 F = m)
    (X : F →L[𝕜] E) (i : Fin n) (j : Fin m) :
    ⟪hA.eigenvectorBasis hn i, A.sylvester B X (hB.eigenvectorBasis hm j)⟫_𝕜 =
      ((hA.eigenvalues hn i - hB.eigenvalues hm j : ℝ) : 𝕜) *
        ⟪hA.eigenvectorBasis hn i, X (hB.eigenvectorBasis hm j)⟫_𝕜 :=
  inner_sylvester_apply_of_apply_eq_smul hA X (hA.apply_eigenvectorBasis hn i)
    (hB.apply_eigenvectorBasis hm j)

/-- Disjoint point spectra force distinct eigenbasis eigenvalues. -/
private theorem eigenvalues_ne_eigenvalues (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hB : (B : F →ₗ[𝕜] F).IsSymmetric) (hn : finrank 𝕜 E = n) (hm : finrank 𝕜 F = m)
    (h : Disjoint (End.restrictedPointSpectrum (A : E →ₗ[𝕜] E) ⊤)
      (End.restrictedPointSpectrum (B : F →ₗ[𝕜] F) ⊤)) (i : Fin n) (j : Fin m) :
    hA.eigenvalues hn i - hB.eigenvalues hm j ≠ 0 := by
  rw [sub_ne_zero]
  intro hij
  refine Set.disjoint_left.mp h
    (End.mem_restrictedPointSpectrum Submodule.mem_top
      ((hA.eigenvectorBasis hn).orthonormal.ne_zero i) (hA.apply_eigenvectorBasis hn i)) ?_
  rw [hij]
  exact End.mem_restrictedPointSpectrum Submodule.mem_top
    ((hB.eigenvectorBasis hm).orthonormal.ne_zero j) (hB.apply_eigenvectorBasis hm j)

/-- **Uniqueness for the Sylvester equation.** In finite dimension, if `A` and `B` are symmetric and
no real eigenvalue of `A` is an eigenvalue of `B`, the Sylvester operator `X ↦ A X - X B` is
injective. -/
theorem sylvester_injective (hA : (A : E →ₗ[𝕜] E).IsSymmetric) (hB : (B : F →ₗ[𝕜] F).IsSymmetric)
    (h : Disjoint (End.restrictedPointSpectrum (A : E →ₗ[𝕜] E) ⊤)
      (End.restrictedPointSpectrum (B : F →ₗ[𝕜] F) ⊤)) :
    Function.Injective (A.sylvester B) := by
  set u := hA.eigenvectorBasis rfl
  set v := hB.eigenvectorBasis rfl
  refine (injective_iff_map_eq_zero _).mpr fun X hX ↦ ?_
  -- Every eigenbasis coefficient of `X` vanishes, since its eigenvalue difference does not.
  have hcoeff (i j) : ⟪u i, X (v j)⟫_𝕜 = 0 := by
    have := inner_sylvester_apply_eigenvectorBasis hA hB rfl rfl X i j
    rw [hX, zero_apply, inner_zero_right, eq_comm, mul_eq_zero, RCLike.ofReal_eq_zero] at this
    exact this.resolve_left (eigenvalues_ne_eigenvalues hA hB rfl rfl h i j)
  ext x
  rw [← v.sum_repr' x, map_sum, zero_apply]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [map_smul, ← u.sum_repr' (X (v j))]
  simp [hcoeff]

/-- **The canonical solution of the Sylvester equation.** In finite dimension, let `A` and `B` be
symmetric with ordered orthonormal eigenbases `(uᵢ)`, `(vⱼ)` and eigenvalues `(αᵢ)`, `(βⱼ)`, and
suppose no real eigenvalue of `A` is an eigenvalue of `B`. Then the operator whose coefficients are
`⟪uᵢ, C vⱼ⟫ / (αᵢ - βⱼ)`, namely the sum of `(αᵢ - βⱼ)⁻¹ ⟪uᵢ, C vⱼ⟫` times the rank-one operators
`rankOne 𝕜 uᵢ vⱼ : x ↦ ⟪vⱼ, x⟫ uᵢ`, solves `A X - X B = C`. -/
theorem sylvester_sum_eigenvectorBasis (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hB : (B : F →ₗ[𝕜] F).IsSymmetric) (hn : finrank 𝕜 E = n) (hm : finrank 𝕜 F = m)
    (h : Disjoint (End.restrictedPointSpectrum (A : E →ₗ[𝕜] E) ⊤)
      (End.restrictedPointSpectrum (B : F →ₗ[𝕜] F) ⊤)) (C : F →L[𝕜] E) :
    A.sylvester B (∑ i, ∑ j,
      ((((hA.eigenvalues hn i - hB.eigenvalues hm j)⁻¹ : ℝ) : 𝕜) *
          ⟪hA.eigenvectorBasis hn i, C (hB.eigenvectorBasis hm j)⟫_𝕜) •
        rankOne 𝕜 (hA.eigenvectorBasis hn i) (hB.eigenvectorBasis hm j)) = C := by
  set u := hA.eigenvectorBasis hn
  set v := hB.eigenvectorBasis hm
  set α := hA.eigenvalues hn
  set β := hB.eigenvalues hm
  -- The Sylvester operator acts on the rank-one operator `uᵢ ⊗ vⱼ` as the scalar `αᵢ - βⱼ`.
  have hrankOne (i j) : A.sylvester B (rankOne 𝕜 (u i) (v j)) =
      ((α i - β j : ℝ) : 𝕜) • rankOne 𝕜 (u i) (v j) := by
    ext x
    have hAui : A (u i) = (α i : 𝕜) • u i := hA.apply_eigenvectorBasis hn i
    have hBvj : B (v j) = (β j : 𝕜) • v j := hB.apply_eigenvectorBasis hm j
    have hBv : ⟪v j, B x⟫_𝕜 = (β j : 𝕜) * ⟪v j, x⟫_𝕜 := by
      rw [← coe_coe B, ← hB (v j) x, coe_coe, hBvj, inner_smul_left, RCLike.conj_ofReal]
    simp [hAui, hBv, smul_smul, sub_smul, mul_comm]
  -- Every operator is the sum of its eigenbasis coefficients times the rank-one operators.
  have hexp : ∑ i, ∑ j, ⟪u i, C (v j)⟫_𝕜 • rankOne 𝕜 (u i) (v j) = C := by
    have hC : C = (∑ i, rankOne 𝕜 (u i) (u i)) ∘L C ∘L ∑ j, rankOne 𝕜 (v j) (v j) := by
      simp [OrthonormalBasis.sum_rankOne_eq_id]
    conv_rhs => rw [hC]
    simp only [comp_finsetSum, comp_rankOne, sum_apply, rankOne_apply, map_sum, map_smul,
      smul_apply]
    exact Finset.sum_comm
  conv_rhs => rw [← hexp]
  simp only [map_sum, map_smul, hrankOne, smul_smul]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  have hij := eigenvalues_ne_eigenvalues hA hB hn hm h i j
  rw [mul_right_comm, ← RCLike.ofReal_mul, inv_mul_cancel₀ hij, RCLike.ofReal_one, one_mul]

/-- **Bijectivity of the Sylvester operator.** In finite dimension, if `A` and `B` are symmetric
and no real eigenvalue of `A` is an eigenvalue of `B`, then for every `C` the Sylvester equation
`A X - X B = C` has exactly one solution. -/
theorem sylvester_bijective (hA : (A : E →ₗ[𝕜] E).IsSymmetric) (hB : (B : F →ₗ[𝕜] F).IsSymmetric)
    (h : Disjoint (End.restrictedPointSpectrum (A : E →ₗ[𝕜] E) ⊤)
      (End.restrictedPointSpectrum (B : F →ₗ[𝕜] F) ⊤)) :
    Function.Bijective (A.sylvester B) :=
  ⟨sylvester_injective hA hB h, fun C ↦ ⟨_, sylvester_sum_eigenvectorBasis hA hB rfl rfl h C⟩⟩

/-- **The solution of the Sylvester equation.** In finite dimension, if `A` and `B` are symmetric
and no real eigenvalue of `A` is an eigenvalue of `B`, then `X` solves `A X - X B = C` exactly when
its coefficients in ordered orthonormal eigenbases `(uᵢ)`, `(vⱼ)` of `A` and `B` are
`⟪uᵢ, C vⱼ⟫ / (αᵢ - βⱼ)`. -/
theorem sylvester_apply_eq_iff (hA : (A : E →ₗ[𝕜] E).IsSymmetric) (hB : (B : F →ₗ[𝕜] F).IsSymmetric)
    (hn : finrank 𝕜 E = n) (hm : finrank 𝕜 F = m)
    (h : Disjoint (End.restrictedPointSpectrum (A : E →ₗ[𝕜] E) ⊤)
      (End.restrictedPointSpectrum (B : F →ₗ[𝕜] F) ⊤)) {X C : F →L[𝕜] E} :
    A.sylvester B X = C ↔ X = ∑ i, ∑ j,
      ((((hA.eigenvalues hn i - hB.eigenvalues hm j)⁻¹ : ℝ) : 𝕜) *
          ⟪hA.eigenvectorBasis hn i, C (hB.eigenvectorBasis hm j)⟫_𝕜) •
        rankOne 𝕜 (hA.eigenvectorBasis hn i) (hB.eigenvectorBasis hm j) := by
  constructor
  · intro hX
    exact sylvester_injective hA hB h
      (hX.trans (sylvester_sum_eigenvectorBasis hA hB hn hm h C).symm)
  · rintro rfl
    exact sylvester_sum_eigenvectorBasis hA hB hn hm h C

end InnerProduct

end ContinuousLinearMap

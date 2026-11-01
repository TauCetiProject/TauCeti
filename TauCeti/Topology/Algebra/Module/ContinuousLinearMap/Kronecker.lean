/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Kronecker products of operators on finite coordinates

For continuous linear maps `f : (Fin m → R) →L[R] (Fin m' → R)` and
`g : (Fin n → R) →L[R] (Fin n' → R)` over a commutative semiring `R` with a topology,
`ContinuousLinearMap.kronecker f g` is their tensor product acting on `Fin (m * n) → R`, where
the coordinate pair `(i, j)` is the index `finProdFinEquiv (i, j)`. Viewing a vector as an
`m × n` array, it applies `g` to every row and then `f` to every column. Its matrix is the
reindexed Kronecker product of the matrices of `f` and `g`
(`ContinuousLinearMap.toMatrix'_kronecker`).

The product is functorial (`ContinuousLinearMap.kronecker_comp_kronecker`,
`ContinuousLinearMap.id_kronecker_id`) and additive and homogeneous in each factor. These are
the transition maps and morphisms of tensor products of vector bundles presented by finite
coordinate charts. The norm bound and continuity in the two factors are in
`TauCeti.Analysis.Normed.Operator.Kronecker`.

The matrix comparison uses Mathlib's `Matrix.kronecker` and `LinearMap.toMatrix'`.
-/

public section

open scoped Kronecker

namespace ContinuousLinearMap

variable {R : Type*} [CommSemiring R] [TopologicalSpace R]
  {m n m' n' m'' n'' : ℕ}

/-- The Kronecker (tensor) product of two operators on finite coordinates, with the coordinate
pair `(i, j)` stored at index `finProdFinEquiv (i, j)`. -/
def kronecker (f : (Fin m → R) →L[R] (Fin m' → R)) (g : (Fin n → R) →L[R] (Fin n' → R)) :
    (Fin (m * n) → R) →L[R] (Fin (m' * n') → R) :=
  pi fun k ↦ (proj (finProdFinEquiv.symm k).1).comp <| f.comp <| pi fun i ↦
    (proj (finProdFinEquiv.symm k).2).comp <| g.comp <| pi fun j ↦ proj (finProdFinEquiv (i, j))

section Apply

variable (f f₂ : (Fin m → R) →L[R] (Fin m' → R)) (g g₂ : (Fin n → R) →L[R] (Fin n' → R))

/-- The Kronecker product applies `g` to the rows and then `f` to the columns. -/
@[simp] theorem kronecker_apply (v : Fin (m * n) → R) (i : Fin m') (j : Fin n') :
    f.kronecker g v (finProdFinEquiv (i, j)) =
      f (fun i' ↦ g (fun j' ↦ v (finProdFinEquiv (i', j'))) j) i := by
  simp only [kronecker, coe_pi', coe_comp, Function.comp_apply, proj_apply,
    Equiv.symm_apply_apply]

/-- The matrix of a Kronecker product is the reindexed Kronecker product of the matrices. -/
theorem toMatrix'_kronecker :
    LinearMap.toMatrix' (f.kronecker g : (Fin (m * n) → R) →ₗ[R] Fin (m' * n') → R) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (LinearMap.toMatrix' (f : (Fin m → R) →ₗ[R] Fin m' → R) ⊗ₖ
          LinearMap.toMatrix' (g : (Fin n → R) →ₗ[R] Fin n' → R)) := by
  ext k l
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective l
  -- The columns of a basis array are zero except for the basis column of `g`.
  have h : (fun i'' ↦ g (fun j'' ↦ Pi.single (M := fun _ ↦ R) (finProdFinEquiv (i', j')) 1
      (finProdFinEquiv (i'', j''))) j) = g (Pi.single j' 1) j • Pi.single i' 1 := by
    ext i''
    have hrow : (fun j'' ↦ Pi.single (M := fun _ ↦ R) (finProdFinEquiv (i', j')) 1
        (finProdFinEquiv (i'', j''))) = if i'' = i' then Pi.single j' 1 else 0 := by
      ext j''
      by_cases hi : i'' = i' <;> simp [Pi.single_apply, hi]
    rw [hrow]
    by_cases hi : i'' = i' <;> simp [hi]
  simp only [LinearMap.toMatrix'_apply, coe_coe, kronecker_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.kronecker_apply, h, map_smul,
    Pi.smul_apply, smul_eq_mul, mul_comm]

@[simp] theorem id_kronecker_id :
    (ContinuousLinearMap.id R (Fin m → R)).kronecker (ContinuousLinearMap.id R (Fin n → R)) =
      ContinuousLinearMap.id R _ := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun k ↦ ?_
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp

theorem add_kronecker [ContinuousAdd R] :
    (f + f₂).kronecker g = f.kronecker g + f₂.kronecker g := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun k ↦ ?_
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp

theorem kronecker_add [ContinuousAdd R] :
    f.kronecker (g + g₂) = f.kronecker g + f.kronecker g₂ := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun k ↦ ?_
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp only [kronecker_apply, _root_.add_apply, Pi.add_apply]
  rw [← Pi.add_def, map_add, Pi.add_apply]

theorem smul_kronecker [ContinuousMul R] (c : R) : (c • f).kronecker g = c • f.kronecker g := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun k ↦ ?_
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp

theorem kronecker_smul [ContinuousMul R] (c : R) : f.kronecker (c • g) = c • f.kronecker g := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun k ↦ ?_
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp only [kronecker_apply, _root_.smul_apply, Pi.smul_apply]
  rw [← Pi.smul_def, map_smul, Pi.smul_apply]

end Apply

/-- The mixed-product law: Kronecker products compose factorwise. -/
theorem kronecker_comp_kronecker (f : (Fin m' → R) →L[R] (Fin m'' → R))
    (g : (Fin n' → R) →L[R] (Fin n'' → R)) (f' : (Fin m → R) →L[R] (Fin m' → R))
    (g' : (Fin n → R) →L[R] (Fin n' → R)) :
    (f.kronecker g).comp (f'.kronecker g') = (f.comp f').kronecker (g.comp g') := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun k ↦ ?_
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp only [comp_apply, kronecker_apply]
  refine congrArg (fun u ↦ f u i) (funext fun i' ↦ ?_)
  -- It remains to show that `g` on rows commutes with `f'` on columns. Expand `f'` in the
  -- standard basis, so that its action on columns is a linear combination of rows.
  have hf (u : Fin m → R) : f' u i' = ∑ l, u l * f' (Pi.single l 1) i' := by
    calc f' u i' = f' (∑ l, u l • Pi.single (M := fun _ ↦ R) l 1) i' := by
          rw [← pi_eq_sum_univ' u]
      _ = _ := by simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have key (w : Fin m → Fin n' → R) :
      g (fun j' ↦ f' (fun l ↦ w l j') i') j = f' (fun l ↦ g (w l) j) i' := by
    have hrow : (fun j' ↦ f' (fun l ↦ w l j') i') = ∑ l, f' (Pi.single l 1) i' • w l := by
      ext j'
      rw [hf]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [hrow, hf]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  exact key fun l j' ↦ g' (fun j'' ↦ v (finProdFinEquiv (l, j''))) j'

@[simp] theorem zero_kronecker (g : (Fin n → R) →L[R] (Fin n' → R)) :
    (0 : (Fin m → R) →L[R] (Fin m' → R)).kronecker g = 0 := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun k ↦ ?_
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp

@[simp] theorem kronecker_zero (f : (Fin m → R) →L[R] (Fin m' → R)) :
    f.kronecker (0 : (Fin n → R) →L[R] (Fin n' → R)) = 0 := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun k ↦ ?_
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp only [kronecker_apply, zero_apply, Pi.zero_apply]
  rw [← Pi.zero_def, map_zero, Pi.zero_apply]

end ContinuousLinearMap

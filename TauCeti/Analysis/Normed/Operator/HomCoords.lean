/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Kronecker
public import TauCeti.Analysis.Normed.Operator.PiTranspose
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Coordinate representations of operator spaces

For finite dimensions `m` and `n` over a normed field `𝕜`, `ContinuousLinearEquiv.finHomEquiv`
identifies the space of continuous linear maps `(Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)` with the coordinate
space `Fin (m * n) → 𝕜` by storing the `(i, j)` matrix entry `f (Pi.single i 1) j` at index
`finProdFinEquiv (i, j)`. Neither nontriviality of the norm nor completeness of `𝕜` is needed:
evaluation at each basis vector is continuous for the topology of bounded convergence, and the
inverse linear map out of `Fin (m * n) → 𝕜` is continuous by `LinearMap.continuous_on_pi`.

Reading two-sided operator composition `T ↦ ψ.comp (T.comp φ)` through `finHomEquiv` gives the
coordinate operator `ContinuousLinearMap.finHomMap φ ψ` on `Fin (m * n) → 𝕜`. It is contravariant
in `φ` and covariant in `ψ`, depends continuously on `(φ, ψ)` (`Continuous.clm_finHomMap`,
`ContinuousOn.clm_finHomMap`), and agrees over a complete nontrivially normed field with the
Kronecker product `φ.piTranspose.kronecker ψ`
(`ContinuousLinearMap.finHomMap_eq_piTranspose_kronecker`).

The evaluation operator `ContinuousLinearMap.finHomEv` contracts `(Fin m → 𝕜)` against
`Fin (m * n) → 𝕜`, while the coevaluation operator `ContinuousLinearMap.finHomCoev` embeds
`Fin p → 𝕜` into `Fin (m * (m * p)) → 𝕜` as tensoring on the left with the identity of
`Fin m → 𝕜`. Together they satisfy the adjunction triangle identities and intertwine coordinate
transitions, supplying the closed monoidal structure on finite-rank vector-bundle cores.
-/

public section

namespace ContinuousLinearEquiv

variable (𝕜 : Type*) [NormedField 𝕜]

/-- Identification of `(Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)` with `Fin (m * n) → 𝕜`, storing the entry
`f (Pi.single i 1) j` at `finProdFinEquiv (i, j)`. -/
def finHomEquiv (m n : ℕ) : ((Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) ≃L[𝕜] (Fin (m * n) → 𝕜) where
  toFun f k := f (Pi.single (finProdFinEquiv.symm k).1 1) (finProdFinEquiv.symm k).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ContinuousLinearMap.pi fun j ↦
    ∑ i : Fin m, v (finProdFinEquiv (i, j)) • ContinuousLinearMap.proj i
  left_inv f := by
    ext u j
    simp only [ContinuousLinearMap.coe_pi', sum_apply, _root_.smul_apply,
      ContinuousLinearMap.proj_apply, Equiv.symm_apply_apply, smul_eq_mul]
    calc
      ∑ i : Fin m, f (Pi.single i 1) j * u i
        = ∑ i : Fin m, (u i • f (Pi.single i 1)) j := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          simp [mul_comm]
      _ = (∑ i : Fin m, f (u i • Pi.single i 1)) j := by simp [Finset.sum_apply]
      _ = f u j := by rw [← map_sum, ← pi_eq_sum_univ' u]
  right_inv v := by
    ext k
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
    simp [Pi.single_apply]
  continuous_toFun :=
    continuous_pi fun k ↦ (continuous_apply _).comp (continuous_eval_const _)
  continuous_invFun :=
    (LinearMap.mk
      { toFun := fun v ↦ ContinuousLinearMap.pi fun j ↦
          ∑ i : Fin m, v (finProdFinEquiv (i, j)) • ContinuousLinearMap.proj i
        map_add' := fun v w ↦ by
          ext u j
          simp [Finset.sum_add_distrib, add_mul] }
      fun c v ↦ by
        ext u j
        simp [Finset.mul_sum, mul_assoc]).continuous_on_pi

variable {𝕜} {m n : ℕ}

@[simp] theorem finHomEquiv_apply (f : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) (i : Fin m) (j : Fin n) :
    finHomEquiv 𝕜 m n f (finProdFinEquiv (i, j)) = f (Pi.single i 1) j := by
  simp only [finHomEquiv, coe_mk, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    Equiv.symm_apply_apply]

@[simp] theorem finHomEquiv_symm_apply (v : Fin (m * n) → 𝕜) (u : Fin m → 𝕜) (j : Fin n) :
    (finHomEquiv 𝕜 m n).symm v u j = ∑ i : Fin m, u i * v (finProdFinEquiv (i, j)) := by
  simp only [← coe_symm_toLinearEquiv, finHomEquiv, LinearEquiv.coe_symm_mk,
    ContinuousLinearMap.coe_pi', sum_apply, _root_.smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, mul_comm]

theorem finHomEquiv_symm_single_apply (i : Fin m) (j : Fin n) (u : Fin m → 𝕜) :
    (finHomEquiv 𝕜 m n).symm (Pi.single (finProdFinEquiv (i, j)) 1) u = u i • Pi.single j 1 := by
  ext j'
  have h (i' : Fin m) :
      u i' * (Pi.single (M := fun _ ↦ 𝕜) (finProdFinEquiv (i, j)) 1) (finProdFinEquiv (i', j')) =
        if i' = i then u i * (Pi.single (M := fun _ ↦ 𝕜) j 1 j') else 0 := by
    by_cases hi : i' = i
    · subst hi
      by_cases hj : j' = j <;> simp [hj]
    · have hne : finProdFinEquiv (i', j') ≠ finProdFinEquiv (i, j) := fun h ↦
        hi (congrArg Prod.fst (finProdFinEquiv.injective h))
      simp [hi, hne]
  simp [h]

end ContinuousLinearEquiv

namespace ContinuousLinearMap

open ContinuousLinearEquiv (finHomEquiv finHomEquiv_apply finHomEquiv_symm_apply
  finHomEquiv_symm_single_apply)

section NormedField

variable {𝕜 : Type*} [NormedField 𝕜] {m n p m' n' p' m'' n'' : ℕ}

/-- Two-sided composition `T ↦ ψ.comp (T.comp φ)`, transported along `finHomEquiv` to an operator
from `Fin (m * n) → 𝕜` to `Fin (m' * n') → 𝕜`. -/
def finHomMap (φ : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜)) (ψ : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) :
    (Fin (m * n) → 𝕜) →L[𝕜] (Fin (m' * n') → 𝕜) :=
  ⟨{ toFun := fun v ↦ finHomEquiv 𝕜 m' n' (ψ.comp (((finHomEquiv 𝕜 m n).symm v).comp φ))
     map_add' := fun v w ↦ by simp [comp_add, add_comp]
     map_smul' := fun c v ↦ by simp [smul_comp] },
    LinearMap.continuous_on_pi _⟩

@[simp] theorem finHomMap_finHomEquiv (φ : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜))
    (ψ : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) (f : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) :
    finHomMap φ ψ (finHomEquiv 𝕜 m n f) = finHomEquiv 𝕜 m' n' (ψ.comp (f.comp φ)) := by
  simp [finHomMap]

@[simp] theorem finHomEquiv_symm_finHomMap (φ : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜))
    (ψ : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) (v : Fin (m * n) → 𝕜) :
    (finHomEquiv 𝕜 m' n').symm (finHomMap φ ψ v) =
      ψ.comp (((finHomEquiv 𝕜 m n).symm v).comp φ) := by
  simp [finHomMap]

/-- In coordinates, `finHomMap φ ψ` applies `ψ` to each row of `v` and pairs the resulting column
with the `i'`-th column of `φ`. -/
theorem finHomMap_apply (φ : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜))
    (ψ : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) (v : Fin (m * n) → 𝕜) (i' : Fin m') (j' : Fin n') :
    finHomMap φ ψ v (finProdFinEquiv (i', j')) =
      ∑ i : Fin m, φ (Pi.single i' 1) i * ψ (fun j ↦ v (finProdFinEquiv (i, j))) j' := by
  have hv : (finHomEquiv 𝕜 m n).symm v (φ (Pi.single i' 1)) =
      ∑ i : Fin m, φ (Pi.single i' 1) i • (fun j ↦ v (finProdFinEquiv (i, j))) := by
    ext j
    simp [Finset.sum_apply]
  simp only [finHomMap, coe_mk', LinearMap.coe_mk, AddHom.coe_mk, finHomEquiv_apply, comp_apply,
    hv, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem finHomMap_single_apply (φ : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜))
    (ψ : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) (i : Fin m) (j : Fin n) (i' : Fin m') (j' : Fin n') :
    finHomMap φ ψ (Pi.single (finProdFinEquiv (i, j)) 1) (finProdFinEquiv (i', j')) =
      φ (Pi.single i' 1) i * ψ (Pi.single j 1) j' := by
  simp [finHomMap, finHomEquiv_symm_single_apply]

@[simp] theorem finHomMap_id :
    finHomMap (ContinuousLinearMap.id 𝕜 (Fin m → 𝕜)) (ContinuousLinearMap.id 𝕜 (Fin n → 𝕜)) =
      ContinuousLinearMap.id 𝕜 (Fin (m * n) → 𝕜) := by
  refine ContinuousLinearMap.ext fun v ↦ (finHomEquiv 𝕜 m n).symm.injective ?_
  simp

/-- Two-sided operator conjugation is contravariant in the first factor and covariant in the
second. -/
@[simp] theorem finHomMap_comp (φ : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜))
    (φ' : (Fin m'' → 𝕜) →L[𝕜] (Fin m' → 𝕜)) (ψ : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜))
    (ψ' : (Fin n' → 𝕜) →L[𝕜] (Fin n'' → 𝕜)) :
    (finHomMap φ' ψ').comp (finHomMap φ ψ) = finHomMap (φ.comp φ') (ψ'.comp ψ) := by
  refine ContinuousLinearMap.ext fun v ↦ (finHomEquiv 𝕜 m'' n'').symm.injective ?_
  simp [comp_assoc]

@[simp] theorem add_finHomMap (φ₁ φ₂ : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜))
    (ψ : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) :
    finHomMap (φ₁ + φ₂) ψ = finHomMap φ₁ ψ + finHomMap φ₂ ψ := by
  refine ContinuousLinearMap.ext fun v ↦ (finHomEquiv 𝕜 m' n').symm.injective ?_
  simp [comp_add]

@[simp] theorem finHomMap_add (φ : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜))
    (ψ₁ ψ₂ : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) :
    finHomMap φ (ψ₁ + ψ₂) = finHomMap φ ψ₁ + finHomMap φ ψ₂ := by
  refine ContinuousLinearMap.ext fun v ↦ (finHomEquiv 𝕜 m' n').symm.injective ?_
  simp [add_comp]

@[simp] theorem zero_finHomMap (ψ : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) :
    finHomMap (0 : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜)) ψ = 0 := by
  refine ContinuousLinearMap.ext fun v ↦ (finHomEquiv 𝕜 m' n').symm.injective ?_
  simp

@[simp] theorem finHomMap_zero (φ : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜)) :
    finHomMap φ (0 : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) = 0 := by
  refine ContinuousLinearMap.ext fun v ↦ (finHomEquiv 𝕜 m' n').symm.injective ?_
  simp

@[simp] theorem smul_finHomMap (c : 𝕜) (φ : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜))
    (ψ : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) :
    finHomMap (c • φ) ψ = c • finHomMap φ ψ := by
  refine ContinuousLinearMap.ext fun v ↦ (finHomEquiv 𝕜 m' n').symm.injective ?_
  simp

@[simp] theorem finHomMap_smul (c : 𝕜) (φ : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜))
    (ψ : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) :
    finHomMap φ (c • ψ) = c • finHomMap φ ψ := by
  refine ContinuousLinearMap.ext fun v ↦ (finHomEquiv 𝕜 m' n').symm.injective ?_
  simp [smul_comp]

variable (𝕜) in
/-- Coordinate evaluation `(Fin m → 𝕜) ⊗ ((Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) → (Fin n → 𝕜)`, summing
the diagonal entries `w (finProdFinEquiv (i, finProdFinEquiv (i, j)))`. -/
def finHomEv (m n : ℕ) : (Fin (m * (m * n)) → 𝕜) →L[𝕜] (Fin n → 𝕜) :=
  pi fun j ↦ ∑ i : Fin m, proj (finProdFinEquiv (i, finProdFinEquiv (i, j)))

@[simp] theorem finHomEv_apply (w : Fin (m * (m * n)) → 𝕜) (j : Fin n) :
    finHomEv 𝕜 m n w j = ∑ i : Fin m, w (finProdFinEquiv (i, finProdFinEquiv (i, j))) := by
  simp [finHomEv]

/-- On a pure Kronecker vector `u ⊗ v`, coordinate evaluation applies `(finHomEquiv 𝕜 m n).symm v`
to `u`. -/
theorem finHomEv_mul (u : Fin m → 𝕜) (v : Fin (m * n) → 𝕜) :
    finHomEv 𝕜 m n (fun k ↦ u (finProdFinEquiv.symm k).1 * v (finProdFinEquiv.symm k).2) =
      (finHomEquiv 𝕜 m n).symm v u := by
  ext j
  simp only [finHomEv_apply, Equiv.symm_apply_apply, finHomEquiv_symm_apply]

/-- Helper evaluating `finHomEv` after `β.kronecker id` on a standard basis vector. -/
private theorem finHomEv_comp_kronecker_id_single (β : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜))
    (i' : Fin m') (i : Fin m) (j : Fin n) :
    ((finHomEv 𝕜 m n).comp (β.kronecker (ContinuousLinearMap.id 𝕜 (Fin (m * n) → 𝕜))))
      (Pi.single (finProdFinEquiv (i', finProdFinEquiv (i, j))) 1) =
        β (Pi.single i' 1) i • Pi.single j 1 := by
  have hsingle (k : Fin m') :
      (fun t ↦ (Pi.single (M := fun _ ↦ 𝕜) (finProdFinEquiv (i', finProdFinEquiv (i, j))) 1)
        (finProdFinEquiv (k, t))) =
        if k = i' then Pi.single (finProdFinEquiv (i, j)) 1 else 0 := by
    ext t
    by_cases hk : k = i' <;> simp [Pi.single_apply, hk]
  ext j'
  have hentry (k : Fin m) :
      (β.kronecker (ContinuousLinearMap.id 𝕜 (Fin (m * n) → 𝕜)))
        (Pi.single (finProdFinEquiv (i', finProdFinEquiv (i, j))) 1)
        (finProdFinEquiv (k, finProdFinEquiv (k, j'))) =
        if k = i then β (Pi.single i' 1) i * Pi.single (M := fun _ ↦ 𝕜) j 1 j' else 0 := by
    rw [kronecker_apply]
    have harg : (fun k' ↦ (ContinuousLinearMap.id 𝕜 (Fin (m * n) → 𝕜))
        (fun t ↦ (Pi.single (M := fun _ ↦ 𝕜) (finProdFinEquiv (i', finProdFinEquiv (i, j))) 1)
          (finProdFinEquiv (k', t))) (finProdFinEquiv (k, j'))) =
        (if k = i then Pi.single (M := fun _ ↦ 𝕜) j 1 j' else 0) • Pi.single i' 1 := by
      ext k'
      simp only [id_apply, hsingle k', Pi.smul_apply, smul_eq_mul]
      by_cases hk' : k' = i'
      · subst hk'
        by_cases hk : k = i
        · subst hk
          by_cases hj : j' = j <;> simp [hj]
        · have hne : finProdFinEquiv (k, j') ≠ finProdFinEquiv (i, j) := fun h ↦
            hk (congrArg Prod.fst (finProdFinEquiv.injective h))
          simp [hk, hne]
      · simp [hk']
    rw [harg, map_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hk : k = i <;> simp [hk, mul_comm]
  simp [hentry]

/-- Dinaturality of coordinate evaluation: precomposing the operator factor with `β` and
postcomposing with `ψ` agrees with applying `β` to the vector factor and `ψ` to the output. -/
theorem finHomEv_comp_id_kronecker_finHomMap (β : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜))
    (ψ : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) :
    (finHomEv 𝕜 m' n').comp ((ContinuousLinearMap.id 𝕜 (Fin m' → 𝕜)).kronecker (finHomMap β ψ)) =
      ψ.comp ((finHomEv 𝕜 m n).comp
        (β.kronecker (ContinuousLinearMap.id 𝕜 (Fin (m * n) → 𝕜)))) := by
  refine ContinuousLinearMap.ext fun w ↦ ?_
  conv_lhs => rw [pi_eq_sum_univ' w]
  conv_rhs => rw [pi_eq_sum_univ' w]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [map_smul, map_smul]
  congr 1
  obtain ⟨⟨i', s⟩, rfl⟩ := finProdFinEquiv.surjective r
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective s
  have hsingle (k : Fin m') :
      (fun t ↦ (Pi.single (M := fun _ ↦ 𝕜) (finProdFinEquiv (i', finProdFinEquiv (i, j))) 1)
        (finProdFinEquiv (k, t))) =
        if k = i' then Pi.single (finProdFinEquiv (i, j)) 1 else 0 := by
    ext t
    by_cases hk : k = i' <;> simp [Pi.single_apply, hk]
  rw [comp_apply, comp_apply (g := ψ), finHomEv_comp_kronecker_id_single, map_smul]
  ext j'
  have hterm (k : Fin m') :
      (ContinuousLinearMap.id 𝕜 (Fin m' → 𝕜))
        (fun k' ↦ finHomMap β ψ
          (if k' = i' then Pi.single (finProdFinEquiv (i, j)) 1 else 0)
          (finProdFinEquiv (k, j'))) k =
        if k = i' then β (Pi.single i' 1) i * ψ (Pi.single j 1) j' else 0 := by
    simp only [id_apply]
    by_cases hk : k = i' <;> simp [hk, finHomMap_single_apply]
  simp [finHomEv_apply, kronecker_apply, hsingle, hterm]

/-- When `β.comp α = id`, coordinate evaluation intertwines `α ⊗ finHomMap β ψ` with `ψ`. -/
theorem finHomEv_comp_kronecker_finHomMap {α : (Fin m → 𝕜) →L[𝕜] (Fin m' → 𝕜)}
    {β : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜)} (hαβ : β.comp α = ContinuousLinearMap.id 𝕜 (Fin m → 𝕜))
    (ψ : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) :
    (finHomEv 𝕜 m' n').comp (α.kronecker (finHomMap β ψ)) = ψ.comp (finHomEv 𝕜 m n) := by
  have hsplit : α.kronecker (finHomMap β ψ) =
      ((ContinuousLinearMap.id 𝕜 (Fin m' → 𝕜)).kronecker (finHomMap β ψ)).comp
        (α.kronecker (ContinuousLinearMap.id 𝕜 (Fin (m * n) → 𝕜))) := by
    rw [kronecker_comp_kronecker, id_comp, comp_id]
  rw [hsplit, ← comp_assoc, finHomEv_comp_id_kronecker_finHomMap, comp_assoc, comp_assoc,
    kronecker_comp_kronecker, id_comp, hαβ, id_kronecker_id, comp_id]

variable (𝕜) in
/-- Coordinate coevaluation `(Fin p → 𝕜) → (Fin (m * (m * p)) → 𝕜)`, sending `y` to the coordinate
representation of `u ↦ u ⊗ y`. -/
def finHomCoev (m p : ℕ) : (Fin p → 𝕜) →L[𝕜] (Fin (m * (m * p)) → 𝕜) :=
  pi fun k ↦
    if (finProdFinEquiv.symm k).1 = (finProdFinEquiv.symm (finProdFinEquiv.symm k).2).1 then
      proj (finProdFinEquiv.symm (finProdFinEquiv.symm k).2).2
    else 0

@[simp] theorem finHomCoev_apply (y : Fin p → 𝕜) (i i' : Fin m) (l : Fin p) :
    finHomCoev 𝕜 m p y (finProdFinEquiv (i, finProdFinEquiv (i', l))) =
      if i = i' then y l else 0 := by
  simp only [finHomCoev, coe_pi', Equiv.symm_apply_apply]
  split_ifs <;> rfl

theorem finHomEquiv_symm_finHomCoev_apply (y : Fin p → 𝕜) (u : Fin m → 𝕜)
    (i : Fin m) (l : Fin p) :
    (finHomEquiv 𝕜 m (m * p)).symm (finHomCoev 𝕜 m p y) u (finProdFinEquiv (i, l)) =
      u i * y l := by
  simp

/-- Dinaturality of coordinate coevaluation: postcomposing `finHomCoev` with
`finHomMap β (α.kronecker γ)` when `α.comp β = id` agrees with `finHomCoev` after `γ`. -/
theorem finHomMap_kronecker_comp_finHomCoev {α : (Fin m → 𝕜) →L[𝕜] (Fin m' → 𝕜)}
    {β : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜)} (hαβ : α.comp β = ContinuousLinearMap.id 𝕜 (Fin m' → 𝕜))
    (γ : (Fin p → 𝕜) →L[𝕜] (Fin p' → 𝕜)) :
    (finHomMap β (α.kronecker γ)).comp (finHomCoev 𝕜 m p) =
      (finHomCoev 𝕜 m' p').comp γ := by
  refine ContinuousLinearMap.ext fun y ↦ (finHomEquiv 𝕜 m' (m' * p')).symm.injective ?_
  ext u' k
  obtain ⟨⟨i', l'⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp only [comp_apply, finHomEquiv_symm_finHomMap, kronecker_apply,
    finHomEquiv_symm_finHomCoev_apply]
  have hrow (i : Fin m) :
      γ (fun l ↦ (β u') i * y l) l' = (β u') i * γ y l' := by
    have hfun : (fun l ↦ (β u') i * y l) = (β u') i • y := rfl
    rw [hfun, map_smul, Pi.smul_apply, smul_eq_mul]
  have hcol : (fun i ↦ γ (fun l ↦ (β u') i * y l) l') = γ y l' • β u' := by
    ext i
    rw [hrow, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hαu : α (β u') = u' := by
    simpa using congrArg (fun T : (Fin m' → 𝕜) →L[𝕜] (Fin m' → 𝕜) ↦ T u') hαβ
  rw [hcol, map_smul, Pi.smul_apply, smul_eq_mul, hαu, mul_comm]

/-- Left triangle identity for `finHomEv` and `finHomCoev`. -/
@[simp] theorem finHomEv_comp_id_kronecker_finHomCoev (m p : ℕ) :
    (finHomEv 𝕜 m (m * p)).comp
        ((ContinuousLinearMap.id 𝕜 (Fin m → 𝕜)).kronecker (finHomCoev 𝕜 m p)) =
      ContinuousLinearMap.id 𝕜 (Fin (m * p) → 𝕜) := by
  ext v k
  obtain ⟨⟨i₀, l₀⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp

/-- Right triangle identity for `finHomEv` and `finHomCoev`. -/
@[simp] theorem finHomMap_id_finHomEv_comp_finHomCoev (m n : ℕ) :
    (finHomMap (ContinuousLinearMap.id 𝕜 (Fin m → 𝕜)) (finHomEv 𝕜 m n)).comp
        (finHomCoev 𝕜 m (m * n)) =
      ContinuousLinearMap.id 𝕜 (Fin (m * n) → 𝕜) := by
  refine ContinuousLinearMap.ext fun v ↦ (finHomEquiv 𝕜 m n).symm.injective ?_
  ext u j
  simp

/-- Iterated coordinate evaluation after `kroneckerAssoc.symm` evaluates the composite operator
`(finHomEquiv 𝕜 n p).symm w ∘ (finHomEquiv 𝕜 m n).symm v` on `u`. -/
theorem finHomEv_comp_kronecker_kroneckerAssoc_symm_mul (u : Fin m → 𝕜)
    (v : Fin (m * n) → 𝕜) (w : Fin (n * p) → 𝕜) :
    finHomEv 𝕜 n p
        (((finHomEv 𝕜 m n).kronecker (ContinuousLinearMap.id 𝕜 (Fin (n * p) → 𝕜)))
          ((ContinuousLinearEquiv.kroneckerAssoc 𝕜 m (m * n) (n * p)).symm
            (fun k ↦ u (finProdFinEquiv.symm k).1 *
              (v (finProdFinEquiv.symm (finProdFinEquiv.symm k).2).1 *
                w (finProdFinEquiv.symm (finProdFinEquiv.symm k).2).2)))) =
      (finHomEquiv 𝕜 n p).symm w ((finHomEquiv 𝕜 m n).symm v u) := by
  have hassoc : (ContinuousLinearEquiv.kroneckerAssoc 𝕜 m (m * n) (n * p)).symm
      (fun k ↦ u (finProdFinEquiv.symm k).1 *
        (v (finProdFinEquiv.symm (finProdFinEquiv.symm k).2).1 *
          w (finProdFinEquiv.symm (finProdFinEquiv.symm k).2).2)) =
      fun k ↦ (u (finProdFinEquiv.symm (finProdFinEquiv.symm k).1).1 *
        v (finProdFinEquiv.symm (finProdFinEquiv.symm k).1).2) *
          w (finProdFinEquiv.symm k).2 := by
    ext k
    obtain ⟨⟨r, t⟩, rfl⟩ := finProdFinEquiv.surjective k
    obtain ⟨⟨i, s⟩, rfl⟩ := finProdFinEquiv.surjective r
    simp only [ContinuousLinearEquiv.kroneckerAssoc_symm_apply, Equiv.symm_apply_apply, mul_assoc]
  have hmid : ((finHomEv 𝕜 m n).kronecker (ContinuousLinearMap.id 𝕜 (Fin (n * p) → 𝕜)))
      (fun k ↦ (u (finProdFinEquiv.symm (finProdFinEquiv.symm k).1).1 *
        v (finProdFinEquiv.symm (finProdFinEquiv.symm k).1).2) *
          w (finProdFinEquiv.symm k).2) =
      fun k ↦ ((finHomEquiv 𝕜 m n).symm v u) (finProdFinEquiv.symm k).1 *
        w (finProdFinEquiv.symm k).2 := by
    ext k
    obtain ⟨⟨j, t⟩, rfl⟩ := finProdFinEquiv.surjective k
    have hcol : (fun r ↦ (u (finProdFinEquiv.symm r).1 * v (finProdFinEquiv.symm r).2) * w t) =
        w t • fun r ↦ u (finProdFinEquiv.symm r).1 * v (finProdFinEquiv.symm r).2 := by
      ext r
      simp [mul_comm]
    rw [kronecker_apply]
    simp only [id_apply, Equiv.symm_apply_apply]
    rw [hcol, map_smul, Pi.smul_apply, smul_eq_mul, finHomEv_mul, mul_comm]
  rw [hassoc, hmid, finHomEv_mul]

end NormedField

section CompleteSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {m n m' n' : ℕ}

/-- Over a complete nontrivially normed field, `finHomMap φ ψ` agrees with the Kronecker product
of the coordinate transpose `φ.piTranspose` and `ψ`. -/
theorem finHomMap_eq_piTranspose_kronecker (φ : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜))
    (ψ : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) :
    finHomMap φ ψ = φ.piTranspose.kronecker ψ := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun k ↦ ?_
  obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective k
  rw [finHomMap_apply, kronecker_apply, piTranspose_apply]

end CompleteSpace

end ContinuousLinearMap

section Continuity

open ContinuousLinearEquiv (finHomEquiv finHomEquiv_apply)
open ContinuousLinearMap

variable {𝕜 X : Type*} [NormedField 𝕜] [TopologicalSpace X] {m n m' n' : ℕ}
  {f : X → (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜)} {g : X → (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)}

/-- Two-sided operator conjugation in finite coordinates preserves continuity of operator
families. -/
@[fun_prop]
theorem Continuous.clm_finHomMap (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x ↦ finHomMap (f x) (g x) := by
  have h : Continuous fun x ↦ finHomEquiv 𝕜 (m * n) (m' * n') (finHomMap (f x) (g x)) := by
    refine continuous_pi fun k ↦ ?_
    obtain ⟨⟨r, s⟩, rfl⟩ := finProdFinEquiv.surjective k
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective r
    obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective s
    simp only [finHomEquiv_apply, finHomMap_single_apply]
    exact (((continuous_apply i).comp ((continuous_eval_const (Pi.single i' 1)).comp hf)).mul
      ((continuous_apply j').comp ((continuous_eval_const (Pi.single j 1)).comp hg)))
  exact ((finHomEquiv 𝕜 (m * n) (m' * n')).symm.continuous.comp h).congr fun x ↦
    (finHomEquiv 𝕜 (m * n) (m' * n')).symm_apply_apply _

/-- Two-sided operator conjugation in finite coordinates preserves continuity on a set. -/
@[fun_prop]
theorem ContinuousOn.clm_finHomMap {s : Set X} (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x ↦ finHomMap (f x) (g x)) s := by
  rw [continuousOn_iff_continuous_domRestrict] at hf hg ⊢
  exact hf.clm_finHomMap hg

end Continuity

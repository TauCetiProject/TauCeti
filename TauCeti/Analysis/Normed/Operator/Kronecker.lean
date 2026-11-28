/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Kronecker
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Continuity of Kronecker products of operators

Over a nontrivially normed field, the Kronecker product `ContinuousLinearMap.kronecker f g` of
operators on finite coordinates is bounded by `‖f‖ * ‖g‖` for the supremum norms
(`ContinuousLinearMap.norm_kronecker_le`). Hence it is the continuous bilinear map
`ContinuousLinearMap.kroneckerL`, and continuous families of operators have continuous
Kronecker products (`Continuous.clm_kronecker`, `ContinuousOn.clm_kronecker`). The field need
not be complete. This continuity makes Kronecker products of continuous transition maps the
transition maps of a vector-bundle core.

Over any normed field `𝕜` (without assuming nontriviality of the norm or completeness),
`ContinuousLinearEquiv.finProdCLM` identifies `Fin (m * n) → 𝕜` with
`(Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)` by reading `finProdFinEquiv (i, j)` as the `(j, i)` matrix
entry, `Continuous.clm_homCoordConj` and `ContinuousOn.clm_homCoordConj` establish continuity of
coordinate operator conjugation `ContinuousLinearMap.homCoordConj` in both factors, and
`ContinuousLinearEquiv.kroneckerCurry` supplies the tensor-Hom currying equivalence on finite
coordinate spaces. Currying intertwines Kronecker precomposition with operator conjugation
(`ContinuousLinearMap.kroneckerCurry_comp_kronecker`); in particular the coevaluation
`kroneckerCurry (id)` transforms like a bundle map under changes of frame
(`ContinuousLinearMap.homCoordConj_kronecker_comp_kroneckerCurry_id`).
-/

public section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {m n m' n' : ℕ}

/-- The Kronecker product is bounded by the product of the operator norms. -/
theorem norm_kronecker_le (f : (Fin m → 𝕜) →L[𝕜] (Fin m' → 𝕜))
    (g : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) : ‖f.kronecker g‖ ≤ ‖f‖ * ‖g‖ := by
  refine opNorm_le_bound _ (by positivity) fun v ↦ ?_
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun k ↦ ?_
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  rw [kronecker_apply, mul_assoc]
  refine (norm_le_pi_norm _ i).trans ((f.le_opNorm _).trans ?_)
  gcongr
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun i' ↦ ?_
  refine (norm_le_pi_norm _ j).trans ((g.le_opNorm _).trans ?_)
  gcongr
  exact pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 fun j' ↦ norm_le_pi_norm _ _

variable (𝕜 m n m' n') in
/-- The Kronecker product as a continuous bilinear map. -/
noncomputable def kroneckerL : ((Fin m → 𝕜) →L[𝕜] (Fin m' → 𝕜)) →L[𝕜]
    ((Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) →L[𝕜] (Fin (m * n) → 𝕜) →L[𝕜] (Fin (m' * n') → 𝕜) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜 kronecker (fun f f₂ g ↦ add_kronecker f f₂ g)
      (fun c f g ↦ smul_kronecker f g c) (fun f g g₂ ↦ kronecker_add f g g₂)
      fun c f g ↦ kronecker_smul f g c)
    1 fun f g ↦ by simpa using norm_kronecker_le f g

@[simp] theorem kroneckerL_apply (f : (Fin m → 𝕜) →L[𝕜] (Fin m' → 𝕜))
    (g : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) : kroneckerL 𝕜 m n m' n' f g = f.kronecker g :=
  (rfl)

end ContinuousLinearMap

section Continuity

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace X] {m n m' n' : ℕ}
  {f : X → (Fin m → 𝕜) →L[𝕜] (Fin m' → 𝕜)} {g : X → (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)}

/-- The Kronecker product of two operator families continuous on a set is continuous on that
set. -/
@[fun_prop]
theorem ContinuousOn.clm_kronecker {s : Set X} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) : ContinuousOn (fun x ↦ (f x).kronecker (g x)) s :=
  (ContinuousLinearMap.kroneckerL 𝕜 m n m' n').continuous₂.comp_continuousOn (hf.prodMk hg)

/-- The Kronecker product of two continuous operator families is continuous. -/
@[fun_prop]
theorem Continuous.clm_kronecker (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x ↦ (f x).kronecker (g x) :=
  (ContinuousLinearMap.kroneckerL 𝕜 m n m' n').continuous₂.comp₂ hf hg

end Continuity

/-! ### Operators on finite coordinates as product-indexed vectors -/

namespace ContinuousLinearEquiv

variable (𝕜 : Type*) [NormedField 𝕜]

/-- Linear map reading `Fin (m * n) → 𝕜` as `(Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)`. -/
private def finProdToCLM (m n : ℕ) :
    (Fin (m * n) → 𝕜) →L[𝕜] ((Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) :=
  ∑ k : Fin (m * n), (ContinuousLinearMap.proj k).smulRight
    ((ContinuousLinearMap.single 𝕜 (fun _ : Fin n ↦ 𝕜) (finProdFinEquiv.symm k).2).comp
      (ContinuousLinearMap.proj (finProdFinEquiv.symm k).1))

/-- Linear map encoding `(Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)` in `Fin (m * n) → 𝕜` by its columns. -/
private def finProdOfCLM (m n : ℕ) :
    ((Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) →L[𝕜] (Fin (m * n) → 𝕜) :=
  ContinuousLinearMap.pi fun k ↦ (ContinuousLinearMap.proj (finProdFinEquiv.symm k).2).comp
    (ContinuousLinearMap.applyₗ (Fin n → 𝕜) (RingHom.id 𝕜)
      (Pi.single (finProdFinEquiv.symm k).1 1))

@[simp] private theorem finProdToCLM_apply {𝕜 : Type*} [NormedField 𝕜] {m n : ℕ}
    (v : Fin (m * n) → 𝕜) (u : Fin m → 𝕜) (j : Fin n) :
    finProdToCLM 𝕜 m n v u j = ∑ i : Fin m, u i * v (finProdFinEquiv (i, j)) := by
  simp only [finProdToCLM, sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, Finset.sum_apply]
  rw [← finProdFinEquiv.sum_comp]
  simp [Fintype.sum_prod_type, Pi.single_apply, mul_comm]

@[simp] private theorem finProdOfCLM_apply {𝕜 : Type*} [NormedField 𝕜] {m n : ℕ}
    (T : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) (i : Fin m) (j : Fin n) :
    finProdOfCLM 𝕜 m n T (finProdFinEquiv (i, j)) = T (Pi.single i 1) j := by
  simp only [finProdOfCLM, ContinuousLinearMap.coe_pi', ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.applyₗ_apply_apply,
    Equiv.symm_apply_apply]

/-- Identify `Fin (m * n) → 𝕜` with the continuous linear maps `(Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)`,
sending `v` to the operator `u ↦ fun j ↦ ∑ i, u i * v (finProdFinEquiv (i, j))`. Both directions
are explicit coordinate maps, so the scalar field need not be complete or nontrivially normed. -/
def finProdCLM (m n : ℕ) :
    (Fin (m * n) → 𝕜) ≃L[𝕜] ((Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) :=
  ofContinuousLinearMap (finProdToCLM 𝕜 m n) (finProdOfCLM 𝕜 m n)
    (ContinuousLinearMap.ext fun T ↦ ContinuousLinearMap.ext fun u ↦ funext fun j ↦ by
      rw [ContinuousLinearMap.comp_apply, finProdToCLM_apply]
      conv_rhs => rw [ContinuousLinearMap.id_apply, pi_eq_sum_univ' u, map_sum]
      simp [Finset.sum_apply, smul_eq_mul])
    (ContinuousLinearMap.ext fun v ↦ funext fun k ↦ by
      obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
      simp [Pi.single_apply])

variable {𝕜} {m n : ℕ}

@[simp] theorem finProdCLM_apply (v : Fin (m * n) → 𝕜) (u : Fin m → 𝕜) (j : Fin n) :
    finProdCLM 𝕜 m n v u j = ∑ i : Fin m, u i * v (finProdFinEquiv (i, j)) :=
  finProdToCLM_apply v u j

@[simp] theorem finProdCLM_symm_apply (T : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜))
    (i : Fin m) (j : Fin n) :
    (finProdCLM 𝕜 m n).symm T (finProdFinEquiv (i, j)) = T (Pi.single i 1) j :=
  finProdOfCLM_apply T i j

end ContinuousLinearEquiv

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NormedField 𝕜] {m m' n n' : ℕ}

@[simp] theorem finProdCLM_homCoordConj (S : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜))
    (R : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) (v : Fin (m * n) → 𝕜) :
    ContinuousLinearEquiv.finProdCLM 𝕜 m' n' (homCoordConj S R v) =
      R.comp ((ContinuousLinearEquiv.finProdCLM 𝕜 m n v).comp S) := by
  ext u' j'
  rw [ContinuousLinearEquiv.finProdCLM_apply, comp_apply, comp_apply]
  conv_rhs => rw [pi_eq_sum_univ' u', map_sum, map_sum, map_sum]
  simp only [homCoordConj_apply, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i' _ ↦ congrArg (u' i' * ·) ?_
  refine congrArg (fun w ↦ R w j') (funext fun j ↦ ?_)
  exact (ContinuousLinearEquiv.finProdCLM_apply v (S (Pi.single i' 1)) j).symm

@[simp] theorem homCoordConj_finProdCLM_symm (S : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜))
    (R : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) (T : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) :
    homCoordConj S R ((ContinuousLinearEquiv.finProdCLM 𝕜 m n).symm T) =
      (ContinuousLinearEquiv.finProdCLM 𝕜 m' n').symm (R.comp (T.comp S)) := by
  apply (ContinuousLinearEquiv.finProdCLM 𝕜 m' n').injective
  simp

@[simp] theorem smul_homCoordConj (c : 𝕜) (S : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜))
    (R : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) :
    homCoordConj (c • S) R = c • homCoordConj S R := by
  refine ContinuousLinearMap.ext fun v ↦ (ContinuousLinearEquiv.finProdCLM 𝕜 m' n').injective ?_
  simp

@[simp] theorem homCoordConj_smul (c : 𝕜) (S : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜))
    (R : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) :
    homCoordConj S (c • R) = c • homCoordConj S R := by
  refine ContinuousLinearMap.ext fun v ↦ (ContinuousLinearEquiv.finProdCLM 𝕜 m' n').injective ?_
  simp [smul_comp]

end ContinuousLinearMap

section HomCoordConjContinuity

variable {𝕜 X : Type*} [NormedField 𝕜] [TopologicalSpace X] {m m' n n' : ℕ}
  {S : X → (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜)} {R : X → (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)}

/-- Operator conjugation of two continuous operator families is continuous. -/
@[fun_prop]
theorem Continuous.clm_homCoordConj (hS : Continuous S) (hR : Continuous R) :
    Continuous fun x ↦ ContinuousLinearMap.homCoordConj (S x) (R x) := by
  have heq : (fun x ↦ ContinuousLinearMap.homCoordConj (S x) (R x)) =
      fun x ↦ ContinuousLinearEquiv.finProdCLM 𝕜 (m * n) (m' * n')
        ((ContinuousLinearEquiv.finProdCLM 𝕜 (m * n) (m' * n')).symm
          (ContinuousLinearMap.homCoordConj (S x) (R x))) := by
    ext x v k
    simp
  rw [heq]
  refine (ContinuousLinearEquiv.finProdCLM 𝕜 (m * n) (m' * n')).continuous.comp
    (continuous_pi fun r ↦ ?_)
  obtain ⟨⟨k, k'⟩, rfl⟩ := finProdFinEquiv.surjective r
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective k'
  have hval : (fun x ↦ (ContinuousLinearEquiv.finProdCLM 𝕜 (m * n) (m' * n')).symm
      (ContinuousLinearMap.homCoordConj (S x) (R x))
        (finProdFinEquiv (finProdFinEquiv (i, j), finProdFinEquiv (i', j')))) =
      fun x ↦ S x (Pi.single i' 1) i * R x (Pi.single j 1) j' := by
    ext x
    rw [ContinuousLinearEquiv.finProdCLM_symm_apply, ContinuousLinearMap.homCoordConj_apply]
    have hv : (fun j₀ : Fin n ↦ ∑ i₀ : Fin m, S x (Pi.single i' 1) i₀ *
        (Pi.single (M := fun _ : Fin (m * n) ↦ 𝕜) (finProdFinEquiv (i, j)) 1)
          (finProdFinEquiv (i₀, j₀))) =
        S x (Pi.single i' 1) i • Pi.single j 1 := by
      ext j₀
      simp [Pi.single_apply, Prod.mk.injEq, ite_and]
    rw [hv, (R x).map_smul, Pi.smul_apply, smul_eq_mul]
  rw [hval]
  exact ((continuous_apply i).comp ((continuous_eval_const (Pi.single i' 1)).comp hS)).mul
    ((continuous_apply j').comp ((continuous_eval_const (Pi.single j 1)).comp hR))

/-- Operator conjugation of two operator families continuous on a set is continuous on that set. -/
@[fun_prop]
theorem ContinuousOn.clm_homCoordConj {s : Set X} (hS : ContinuousOn S s)
    (hR : ContinuousOn R s) :
    ContinuousOn (fun x ↦ ContinuousLinearMap.homCoordConj (S x) (R x)) s :=
  continuousOn_iff_continuous_domRestrict.2
    (Continuous.clm_homCoordConj (continuousOn_iff_continuous_domRestrict.1 hS)
      (continuousOn_iff_continuous_domRestrict.1 hR))

end HomCoordConjContinuity

/-! ### Tensor-Hom currying on finite coordinates -/

namespace ContinuousLinearEquiv

variable (𝕜 : Type*) [NormedField 𝕜]

/-- Currying equivalence between operators out of Kronecker coordinates `Fin (m * p) → 𝕜` and
operators into Hom coordinates `Fin (m * n) → 𝕜`. -/
def kroneckerCurry (m p n : ℕ) :
    ((Fin (m * p) → 𝕜) →L[𝕜] (Fin n → 𝕜)) ≃L[𝕜] ((Fin p → 𝕜) →L[𝕜] (Fin (m * n) → 𝕜)) :=
  (finProdCLM 𝕜 (m * p) n).symm.trans <|
    ((piCongrLeft 𝕜 (fun _ ↦ 𝕜)
      (finProdFinEquiv.symm.trans <| (Equiv.prodCongrRight fun _ ↦ finProdFinEquiv.symm).trans <|
        (Equiv.prodAssoc _ _ _).symm.trans <|
          (Equiv.prodCongrLeft fun _ ↦ (Equiv.prodComm _ _).trans finProdFinEquiv).trans
            finProdFinEquiv)).symm).trans
      (finProdCLM 𝕜 p (m * n))

variable {𝕜} {m p n : ℕ}

@[simp] theorem kroneckerCurry_apply_apply (F : (Fin (m * p) → 𝕜) →L[𝕜] (Fin n → 𝕜))
    (c : Fin p → 𝕜) (i : Fin m) (j : Fin n) :
    kroneckerCurry 𝕜 m p n F c (finProdFinEquiv (i, j)) =
      ∑ l : Fin p, c l * F (Pi.single (finProdFinEquiv (i, l)) 1) j := by
  dsimp only [kroneckerCurry, trans_apply]
  rw [finProdCLM_apply]
  refine Finset.sum_congr rfl fun l _ ↦ congrArg (c l * ·) ?_
  exact (congrArg ((finProdCLM 𝕜 (m * p) n).symm F) (by simp)).trans
    (finProdCLM_symm_apply F (finProdFinEquiv (i, l)) j)

/-- Read through `finProdCLM`, the curried operator sends `(c, u)` to `F` applied to the pure
tensor `u ⊗ c`. -/
theorem finProdCLM_kroneckerCurry_apply (F : (Fin (m * p) → 𝕜) →L[𝕜] (Fin n → 𝕜))
    (c : Fin p → 𝕜) (u : Fin m → 𝕜) :
    finProdCLM 𝕜 m n (kroneckerCurry 𝕜 m p n F c) u =
      F (fun k ↦ u (finProdFinEquiv.symm k).1 * c (finProdFinEquiv.symm k).2) := by
  ext j
  rw [finProdCLM_apply]
  simp only [kroneckerCurry_apply_apply, Finset.mul_sum, ← mul_assoc]
  have hpure : (fun k : Fin (m * p) ↦
      u (finProdFinEquiv.symm k).1 * c (finProdFinEquiv.symm k).2) =
      ∑ i : Fin m, ∑ l : Fin p, (u i * c l) • Pi.single (finProdFinEquiv (i, l)) 1 :=
    (pi_eq_sum_univ' _).trans (by rw [← finProdFinEquiv.sum_comp]; simp [Fintype.sum_prod_type])
  rw [hpure, map_sum]
  simp [Finset.sum_apply, map_sum, smul_eq_mul]

end ContinuousLinearEquiv

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NormedField 𝕜] {m m' p p' n n' : ℕ}

/-- Currying intertwines Kronecker precomposition and target postcomposition with operator
conjugation on the Hom factor. -/
theorem kroneckerCurry_comp_kronecker (S : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜))
    (P : (Fin p → 𝕜) →L[𝕜] (Fin p' → 𝕜)) (R : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜))
    (F : (Fin (m * p') → 𝕜) →L[𝕜] (Fin n → 𝕜)) :
    ContinuousLinearEquiv.kroneckerCurry 𝕜 m' p n' (R.comp (F.comp (S.kronecker P))) =
      (homCoordConj S R).comp ((ContinuousLinearEquiv.kroneckerCurry 𝕜 m p' n F).comp P) := by
  refine ContinuousLinearMap.ext fun c ↦ (ContinuousLinearEquiv.finProdCLM 𝕜 m' n').injective <|
    ContinuousLinearMap.ext fun u ↦ ?_
  simp only [comp_apply, finProdCLM_homCoordConj,
    ContinuousLinearEquiv.finProdCLM_kroneckerCurry_apply, kronecker_apply_mul]

/-- The coevaluation `kroneckerCurry (id)` intertwines `P` with the operator conjugation by `S`
and `T ⊗ P`, whenever `T` is a left inverse of `S`. This is the transition law of the
coevaluation `C ⟶ hom A (A ⊗ C)` of vector bundles. -/
theorem homCoordConj_kronecker_comp_kroneckerCurry_id {S : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜)}
    {T : (Fin m → 𝕜) →L[𝕜] (Fin m' → 𝕜)} (hTS : T.comp S = ContinuousLinearMap.id 𝕜 _)
    (P : (Fin p → 𝕜) →L[𝕜] (Fin p' → 𝕜)) :
    (homCoordConj S (T.kronecker P)).comp
        (ContinuousLinearEquiv.kroneckerCurry 𝕜 m p (m * p) (ContinuousLinearMap.id 𝕜 _)) =
      (ContinuousLinearEquiv.kroneckerCurry 𝕜 m' p' (m' * p') (ContinuousLinearMap.id 𝕜 _)).comp
        P := by
  have h₁ := kroneckerCurry_comp_kronecker S (ContinuousLinearMap.id 𝕜 (Fin p → 𝕜))
    (T.kronecker P) (ContinuousLinearMap.id 𝕜 (Fin (m * p) → 𝕜))
  have h₂ := kroneckerCurry_comp_kronecker (ContinuousLinearMap.id 𝕜 (Fin m' → 𝕜)) P
    (ContinuousLinearMap.id 𝕜 (Fin (m' * p') → 𝕜)) (ContinuousLinearMap.id 𝕜 (Fin (m' * p') → 𝕜))
  rw [id_comp, comp_id, kronecker_comp_kronecker, hTS, comp_id] at h₁
  rw [id_comp, id_comp, id_homCoordConj_id, id_comp] at h₂
  exact h₁.symm.trans h₂

@[simp] theorem kroneckerCurry_kroneckerHomEv (m n : ℕ) :
    ContinuousLinearEquiv.kroneckerCurry 𝕜 m (m * n) n (kroneckerHomEv 𝕜 m n) =
      ContinuousLinearMap.id 𝕜 (Fin (m * n) → 𝕜) := by
  refine ContinuousLinearMap.ext fun c ↦ funext fun k ↦ ?_
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp [ContinuousLinearEquiv.kroneckerCurry_apply_apply, Pi.single_apply, Prod.mk.injEq, ite_and]

/-- Uncurrying any operator into Hom coordinates factors through `kroneckerHomEv`. -/
theorem kroneckerCurry_symm_apply_eq (G : (Fin p → 𝕜) →L[𝕜] (Fin (m * n) → 𝕜)) :
    (ContinuousLinearEquiv.kroneckerCurry 𝕜 m p n).symm G =
      (kroneckerHomEv 𝕜 m n).comp ((ContinuousLinearMap.id 𝕜 (Fin m → 𝕜)).kronecker G) := by
  apply (ContinuousLinearEquiv.kroneckerCurry 𝕜 m p n).injective
  have h := kroneckerCurry_comp_kronecker (ContinuousLinearMap.id 𝕜 (Fin m → 𝕜)) G
    (ContinuousLinearMap.id 𝕜 (Fin n → 𝕜)) (kroneckerHomEv 𝕜 m n)
  simpa using h.symm

end ContinuousLinearMap

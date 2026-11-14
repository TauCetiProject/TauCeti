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

In the same generality (without completeness of the field), `ContinuousLinearEquiv.finProdCLM`
identifies `Fin (m * n) → 𝕜` with `(Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)` by reading
`finProdFinEquiv (i, j)` as the `(j, i)` matrix entry, `ContinuousLinearMap.homCoordConj`
conjugates operators in these coordinates continuously in both factors, and
`ContinuousLinearEquiv.kroneckerCurry` with `ContinuousLinearMap.kroneckerHomEv` supplies the
tensor-Hom currying equivalence and evaluation on finite coordinate spaces.
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

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]

/-- Linear map reading `Fin (m * n) → 𝕜` as `(Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)`. -/
private def finProdToCLM (m n : ℕ) :
    (Fin (m * n) → 𝕜) →L[𝕜] ((Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) :=
  ∑ k : Fin (m * n), (ContinuousLinearMap.proj k).smulRight
    ((ContinuousLinearMap.single 𝕜 (fun _ : Fin n ↦ 𝕜) (finProdFinEquiv.symm k).2).comp
      (ContinuousLinearMap.proj (finProdFinEquiv.symm k).1))

/-- Linear map encoding `(Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)` in `Fin (m * n) → 𝕜` by its columns. -/
private noncomputable def finProdOfCLM (m n : ℕ) :
    ((Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) →L[𝕜] (Fin (m * n) → 𝕜) :=
  ContinuousLinearMap.pi fun k ↦ (ContinuousLinearMap.proj (finProdFinEquiv.symm k).2).comp
    (ContinuousLinearMap.apply 𝕜 (Fin n → 𝕜) (Pi.single (finProdFinEquiv.symm k).1 1))

@[simp] private theorem finProdToCLM_apply {𝕜 : Type*} [NontriviallyNormedField 𝕜] {m n : ℕ}
    (v : Fin (m * n) → 𝕜) (u : Fin m → 𝕜) (j : Fin n) :
    finProdToCLM 𝕜 m n v u j = ∑ i : Fin m, u i * v (finProdFinEquiv (i, j)) := by
  simp only [finProdToCLM, sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, Finset.sum_apply]
  rw [← finProdFinEquiv.sum_comp]
  simp [Fintype.sum_prod_type, Pi.single_apply, mul_comm]

@[simp] private theorem finProdOfCLM_apply {𝕜 : Type*} [NontriviallyNormedField 𝕜] {m n : ℕ}
    (T : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) (i : Fin m) (j : Fin n) :
    finProdOfCLM 𝕜 m n T (finProdFinEquiv (i, j)) = T (Pi.single i 1) j := by
  simp only [finProdOfCLM, ContinuousLinearMap.coe_pi', ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.apply_apply,
    Equiv.symm_apply_apply]

/-- Identify `Fin (m * n) → 𝕜` with the continuous linear maps `(Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)`,
sending `v` to the operator `u ↦ fun j ↦ ∑ i, u i * v (finProdFinEquiv (i, j))`. Both directions
are explicit coordinate maps, so the scalar field need not be complete. -/
noncomputable def finProdCLM (m n : ℕ) :
    (Fin (m * n) → 𝕜) ≃L[𝕜] ((Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) :=
  equivOfInverse (finProdToCLM 𝕜 m n) (finProdOfCLM 𝕜 m n)
    (fun v ↦ funext fun k ↦ by
      obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
      simp [Pi.single_apply])
    (fun T ↦ ContinuousLinearMap.ext fun u ↦ funext fun j ↦ by
      rw [finProdToCLM_apply]
      have hu : u = ∑ i : Fin m, u i • Pi.single i 1 := by
        ext i; simp [Finset.sum_apply, Pi.single_apply]
      conv_rhs => rw [hu, map_sum]
      simp [Finset.sum_apply, smul_eq_mul])

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

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {m m' m'' n n' n'' p p' : ℕ}

/-- Conjugate an operator encoded in `Fin (m * n) → 𝕜` by precomposing with `S` and postcomposing
with `R`. -/
noncomputable def homCoordConj (S : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜))
    (R : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) :
    (Fin (m * n) → 𝕜) →L[𝕜] (Fin (m' * n') → 𝕜) :=
  (ContinuousLinearEquiv.finProdCLM 𝕜 m' n').symm.toContinuousLinearMap.comp
    (((compL 𝕜 (Fin m' → 𝕜) (Fin n → 𝕜) (Fin n' → 𝕜) R).comp
      ((compL 𝕜 (Fin m' → 𝕜) (Fin m → 𝕜) (Fin n → 𝕜)).flip S)).comp
        (ContinuousLinearEquiv.finProdCLM 𝕜 m n).toContinuousLinearMap)

@[simp] theorem finProdCLM_homCoordConj (S : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜))
    (R : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) (v : Fin (m * n) → 𝕜) :
    ContinuousLinearEquiv.finProdCLM 𝕜 m' n' (homCoordConj S R v) =
      R.comp ((ContinuousLinearEquiv.finProdCLM 𝕜 m n v).comp S) := by
  simp [homCoordConj]

@[simp] theorem homCoordConj_finProdCLM_symm (S : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜))
    (R : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) (T : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) :
    homCoordConj S R ((ContinuousLinearEquiv.finProdCLM 𝕜 m n).symm T) =
      (ContinuousLinearEquiv.finProdCLM 𝕜 m' n').symm (R.comp (T.comp S)) := by
  apply (ContinuousLinearEquiv.finProdCLM 𝕜 m' n').injective
  simp

@[simp] theorem id_homCoordConj_id :
    homCoordConj (ContinuousLinearMap.id 𝕜 (Fin m → 𝕜)) (ContinuousLinearMap.id 𝕜 (Fin n → 𝕜)) =
      ContinuousLinearMap.id 𝕜 (Fin (m * n) → 𝕜) := by
  refine ContinuousLinearMap.ext fun v ↦ (ContinuousLinearEquiv.finProdCLM 𝕜 m n).injective ?_
  simp

/-- Operator conjugation is contravariant in the source map and covariant in the target map. -/
theorem homCoordConj_comp_homCoordConj (S' : (Fin m'' → 𝕜) →L[𝕜] (Fin m' → 𝕜))
    (R' : (Fin n' → 𝕜) →L[𝕜] (Fin n'' → 𝕜)) (S : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜))
    (R : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) :
    (homCoordConj S' R').comp (homCoordConj S R) = homCoordConj (S.comp S') (R'.comp R) := by
  refine ContinuousLinearMap.ext fun v ↦
    (ContinuousLinearEquiv.finProdCLM 𝕜 m'' n'').injective ?_
  simp [comp_assoc]

@[simp] theorem add_homCoordConj (S S₂ : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜))
    (R : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) :
    homCoordConj (S + S₂) R = homCoordConj S R + homCoordConj S₂ R := by
  refine ContinuousLinearMap.ext fun v ↦
    (ContinuousLinearEquiv.finProdCLM 𝕜 m' n').injective ?_
  simp [comp_add]

@[simp] theorem homCoordConj_add (S : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜))
    (R R₂ : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) :
    homCoordConj S (R + R₂) = homCoordConj S R + homCoordConj S R₂ := by
  refine ContinuousLinearMap.ext fun v ↦
    (ContinuousLinearEquiv.finProdCLM 𝕜 m' n').injective ?_
  simp [add_comp]

@[simp] theorem zero_homCoordConj (R : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) :
    homCoordConj (0 : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜)) R = 0 := by
  refine ContinuousLinearMap.ext fun v ↦
    (ContinuousLinearEquiv.finProdCLM 𝕜 m' n').injective ?_
  simp

@[simp] theorem homCoordConj_zero (S : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜)) :
    homCoordConj S (0 : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) = 0 := by
  refine ContinuousLinearMap.ext fun v ↦
    (ContinuousLinearEquiv.finProdCLM 𝕜 m' n').injective ?_
  simp

end ContinuousLinearMap

section HomCoordConjContinuity

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace X] {m m' n n' : ℕ}
  {S : X → (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜)} {R : X → (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)}

@[fun_prop]
theorem Continuous.clm_homCoordConj (hS : Continuous S) (hR : Continuous R) :
    Continuous fun x ↦ ContinuousLinearMap.homCoordConj (S x) (R x) :=
  (((((ContinuousLinearMap.compL 𝕜 (Fin m' → 𝕜) (Fin n → 𝕜) (Fin n' → 𝕜)).continuous.comp hR)
    |>.clm_comp
    ((ContinuousLinearMap.compL 𝕜 (Fin m' → 𝕜) (Fin m → 𝕜) (Fin n → 𝕜)).flip.continuous.comp hS))
    |>.clm_comp continuous_const).const_clm_comp _)

@[fun_prop]
theorem ContinuousOn.clm_homCoordConj {s : Set X} (hS : ContinuousOn S s)
    (hR : ContinuousOn R s) :
    ContinuousOn (fun x ↦ ContinuousLinearMap.homCoordConj (S x) (R x)) s :=
  continuousOn_iff_continuous_domRestrict.2
    (Continuous.clm_homCoordConj (continuousOn_iff_continuous_domRestrict.1 hS)
      (continuousOn_iff_continuous_domRestrict.1 hR))

end HomCoordConjContinuity

/-! ### Tensor-Hom currying and evaluation on finite coordinates -/

namespace ContinuousLinearEquiv

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]

/-- Currying equivalence between operators out of Kronecker coordinates `Fin (m * p) → 𝕜` and
operators into Hom coordinates `Fin (m * n) → 𝕜`. -/
noncomputable def kroneckerCurry (m p n : ℕ) :
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
      ∑ i : Fin m, ∑ l : Fin p, (u i * c l) • Pi.single (finProdFinEquiv (i, l)) 1 := by
    ext k
    obtain ⟨⟨i, l⟩, rfl⟩ := finProdFinEquiv.surjective k
    simp [Finset.sum_apply, Pi.single_apply, Prod.mk.injEq, ite_and]
  rw [hpure, map_sum]
  simp [Finset.sum_apply, map_sum, smul_eq_mul]

end ContinuousLinearEquiv

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {m m' p p' n n' : ℕ}

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

variable (𝕜) in
/-- Coordinate evaluation `(Fin m → 𝕜) ⊗ ((Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) → (Fin n → 𝕜)`,
defined by uncurrying the identity of `Fin (m * n) → 𝕜`. -/
noncomputable def kroneckerHomEv (m n : ℕ) : (Fin (m * (m * n)) → 𝕜) →L[𝕜] (Fin n → 𝕜) :=
  (ContinuousLinearEquiv.kroneckerCurry 𝕜 m (m * n) n).symm
    (ContinuousLinearMap.id 𝕜 (Fin (m * n) → 𝕜))

@[simp] theorem kroneckerCurry_kroneckerHomEv (m n : ℕ) :
    ContinuousLinearEquiv.kroneckerCurry 𝕜 m (m * n) n (kroneckerHomEv 𝕜 m n) =
      ContinuousLinearMap.id 𝕜 (Fin (m * n) → 𝕜) :=
  ContinuousLinearEquiv.apply_symm_apply _ _

/-- Uncurrying any operator into Hom coordinates factors through `kroneckerHomEv`. -/
theorem kroneckerCurry_symm_apply_eq (G : (Fin p → 𝕜) →L[𝕜] (Fin (m * n) → 𝕜)) :
    (ContinuousLinearEquiv.kroneckerCurry 𝕜 m p n).symm G =
      (kroneckerHomEv 𝕜 m n).comp ((ContinuousLinearMap.id 𝕜 (Fin m → 𝕜)).kronecker G) := by
  apply (ContinuousLinearEquiv.kroneckerCurry 𝕜 m p n).injective
  have h := kroneckerCurry_comp_kronecker (ContinuousLinearMap.id 𝕜 (Fin m → 𝕜)) G
    (ContinuousLinearMap.id 𝕜 (Fin n → 𝕜)) (kroneckerHomEv 𝕜 m n)
  simpa using h.symm

@[simp] theorem kroneckerHomEv_apply (w : Fin (m * (m * n)) → 𝕜) (j : Fin n) :
    kroneckerHomEv 𝕜 m n w j =
      ∑ i : Fin m, w (finProdFinEquiv (i, finProdFinEquiv (i, j))) := by
  have hw : w = ∑ i : Fin m, ∑ k : Fin (m * n),
      w (finProdFinEquiv (i, k)) • Pi.single (finProdFinEquiv (i, k)) 1 := by
    ext r
    obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective r
    simp [Finset.sum_apply, Pi.single_apply, Prod.mk.injEq, ite_and]
  have hsingle (i : Fin m) (k : Fin (m * n)) :
      kroneckerHomEv 𝕜 m n (Pi.single (finProdFinEquiv (i, k)) 1) j =
        (Pi.single (M := fun _ : Fin (m * n) ↦ 𝕜) k 1) (finProdFinEquiv (i, j)) := by
    have h := congrFun (ContinuousLinearEquiv.finProdCLM_kroneckerCurry_apply
      (kroneckerHomEv 𝕜 m n) (Pi.single k 1) (Pi.single i 1)) j
    rw [kroneckerCurry_kroneckerHomEv, id_apply, ContinuousLinearEquiv.finProdCLM_apply] at h
    have hp : (fun r : Fin (m * (m * n)) ↦
        (Pi.single (M := fun _ : Fin m ↦ 𝕜) i 1) (finProdFinEquiv.symm r).1 *
          (Pi.single (M := fun _ : Fin (m * n) ↦ 𝕜) k 1) (finProdFinEquiv.symm r).2) =
        Pi.single (finProdFinEquiv (i, k)) 1 := by
      ext r
      obtain ⟨⟨i', k'⟩, rfl⟩ := finProdFinEquiv.surjective r
      simp [Pi.single_apply, Prod.mk.injEq, ite_and]
      split_ifs <;> rfl
    rw [hp] at h
    rw [← h]
    exact (Finset.sum_eq_single i (fun x _ hxi ↦ by simp [Pi.single_apply, hxi])
      fun hi ↦ (hi (Finset.mem_univ i)).elim).trans (by simp)
  conv_lhs => rw [hw, map_sum]
  simp [Finset.sum_apply, map_sum, hsingle, Pi.single_apply]

/-- When `S.comp T = id`, coordinate evaluation intertwines `T ⊗ homCoordConj S R` with `R`. -/
theorem kroneckerHomEv_comp_kronecker_homCoordConj {S : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜)}
    {T : (Fin m → 𝕜) →L[𝕜] (Fin m' → 𝕜)} (hST : S.comp T = ContinuousLinearMap.id 𝕜 _)
    (R : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) :
    (kroneckerHomEv 𝕜 m' n').comp (T.kronecker (homCoordConj S R)) =
      R.comp (kroneckerHomEv 𝕜 m n) := by
  apply (ContinuousLinearEquiv.kroneckerCurry 𝕜 m (m * n) n').injective
  have h₁ := kroneckerCurry_comp_kronecker T (homCoordConj S R)
    (ContinuousLinearMap.id 𝕜 (Fin n' → 𝕜)) (kroneckerHomEv 𝕜 m' n')
  have h₂ := kroneckerCurry_comp_kronecker (ContinuousLinearMap.id 𝕜 (Fin m → 𝕜))
    (ContinuousLinearMap.id 𝕜 (Fin (m * n) → 𝕜)) R (kroneckerHomEv 𝕜 m n)
  simp only [id_comp, comp_id, id_kronecker_id, kroneckerCurry_kroneckerHomEv] at h₁ h₂ ⊢
  rw [h₁, h₂, homCoordConj_comp_homCoordConj, hST, id_comp]

end ContinuousLinearMap

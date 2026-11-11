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

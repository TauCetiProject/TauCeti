/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.PiTensorProduct.Projective.Seminorm
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# The cross property of projective tensor seminorms

Over the real or complex field, the projective seminorm associated to a finite family of
seminorms takes a pure tensor to the product of the factor seminorms. The factors need not
be separated or carry any topology. In particular, zero seminorms are allowed, and the empty
family gives the scalar field with its usual norm.

The lower bound follows by taking the product of Hahn–Banach norming functionals for the
factors, and applying `PiTensorProduct.seminorm_lift_le` to its tensor lift. This is the
finite-family version of the usual cross-norm argument, using Mathlib's
`exists_dual_vector''`. Specializing to the norm seminorms gives the cross property for
Mathlib's projective tensor seminorm on seminormed spaces.

## References

* A. Grothendieck, *Résumé des résultats essentiels dans la théorie des produits tensoriels
  topologiques et des espaces nucléaires*, Ann. Inst. Fourier 4 (1952), Chapter I, n° 1.
* R. A. Ryan, *Introduction to Tensor Products of Banach Spaces*, §2.1.
-/

public section

open scoped TensorProduct

namespace PiTensorProduct

variable {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜]
variable {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]

/-- The projective seminorm of a pure tensor equals the product of its factor seminorms,
including for degenerate seminorms and the empty family. -/
@[simp]
theorem projectiveSeminormOf_tprod (p : ∀ i, Seminorm 𝕜 (E i)) (m : ∀ i, E i) :
    projectiveSeminormOf p (⨂ₜ[𝕜] i, m i) = ∏ i, p i (m i) := by
  classical
  let : ∀ i, SeminormedAddCommGroup (E i) :=
    fun i => (p i).toAddGroupSeminorm.toSeminormedAddCommGroup
  let : ∀ i, NormedSpace 𝕜 (E i) :=
    fun i => ⟨fun a x => (map_smul_eq_mul (p i) a x).le⟩
  -- Record the norm of the temporary seminormed structure explicitly.
  have hnorm (i : ι) (x : E i) : ‖x‖ = p i x := rfl
  choose f hf hfm using fun i => exists_dual_vector'' 𝕜 (m i)
  let g := (MultilinearMap.mkPiAlgebra 𝕜 ι 𝕜).compLinearMap
    (fun i => (f i).toLinearMap)
  have hg (x : ∀ i, E i) : ‖g x‖ ≤ ∏ i, p i (x i) := by
    simp only [g, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
      ContinuousLinearMap.coe_coe, norm_prod]
    apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
    intro i _
    exact ((f i).le_opNorm (x i)).trans (by
      simpa only [hnorm, one_mul] using
        mul_le_mul_of_nonneg_right (hf i) (norm_nonneg (x i)))
  apply le_antisymm (projectiveSeminormOf_tprod_le p m)
  calc
    ∏ i, p i (m i) = ‖lift g (⨂ₜ[𝕜] i, m i)‖ := by
      simp [g, hfm, norm_prod, hnorm]
    _ ≤ 1 * projectiveSeminormOf p (⨂ₜ[𝕜] i, m i) :=
      seminorm_lift_le p (normSeminorm 𝕜 𝕜) g zero_le_one (by simpa using hg) _
    _ = projectiveSeminormOf p (⨂ₜ[𝕜] i, m i) := one_mul _

end PiTensorProduct

namespace PiTensorProduct

variable {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜]
variable {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

/-- The projective tensor seminorm on seminormed spaces is a cross seminorm. -/
@[simp]
theorem norm_tprod (m : ∀ i, E i) : ‖(⨂ₜ[𝕜] i, m i)‖ = ∏ i, ‖m i‖ := by
  simpa using projectiveSeminormOf_tprod (fun i => normSeminorm 𝕜 (E i)) m

end PiTensorProduct

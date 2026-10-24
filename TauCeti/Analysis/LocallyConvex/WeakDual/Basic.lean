/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WeakDual
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Weak-star continuous functionals on a weak dual

Every weak-star continuous linear functional on `WeakDual 𝕜 F` is evaluation at a point of `F`.
This is Mathlib's weak representation theorem `LinearMap.dualEmbedding_surjective` for the
canonical pairing `topDualPairing 𝕜 F`, stated directly for the `WeakDual` type synonym, so that
it applies to `WeakDual 𝕜 F` whatever instance path elaborated it. Hahn–Banach separation in a
weak dual produces such functionals, and this lemma turns them into points of the predual.

Over `𝕜 = ℝ` or `ℂ`, the dual `WeakDual 𝕜 F` is also a real vector space. A real multiple `c • f`
is the multiple of `f` by the scalar `(c : 𝕜)`, and acts pointwise as multiplication by `(c : 𝕜)`.
-/

public section

namespace WeakDual

/-- Every weak-star continuous linear functional on `WeakDual 𝕜 F` is evaluation at a point
of `F`. -/
theorem exists_forall_apply_eq_apply {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] (l : StrongDual 𝕜 (WeakDual 𝕜 F)) :
    ∃ x : F, ∀ φ : WeakDual 𝕜 F, l φ = φ x := by
  obtain ⟨x, rfl⟩ := LinearMap.dualEmbedding_surjective (topDualPairing 𝕜 F) l
  -- `WeakDual 𝕜 F` is by definition `WeakBilin (topDualPairing 𝕜 F)`, and `WeakBilin.eval`
  -- sends `x` to the functional `(topDualPairing 𝕜 F).flip x`.
  refine ⟨x, fun φ ↦ ?_⟩
  simp only [WeakBilin.eval, LinearMap.coe_mk, AddHom.coe_mk]
  exact topDualPairing_apply φ x

section RCLike

variable {𝕜 F : Type*} [RCLike 𝕜] [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]

/-- A real multiple of a functional in `WeakDual 𝕜 F` acts as multiplication by the corresponding
scalar of `𝕜`. The real action on `WeakDual 𝕜 F` is pointwise, so `(c • f) x` is `c • f x` by
definition, which `RCLike.real_smul_eq_coe_mul` rewrites. -/
@[simp]
theorem real_smul_apply (c : ℝ) (f : WeakDual 𝕜 F) (x : F) : (c • f) x = (c : 𝕜) * f x :=
  RCLike.real_smul_eq_coe_mul c (f x)

/-- A real multiple of a functional in `WeakDual 𝕜 F` is its multiple by the corresponding scalar
of `𝕜`. -/
theorem real_smul_eq_coe_smul (c : ℝ) (f : WeakDual 𝕜 F) : c • f = (c : 𝕜) • f :=
  DFunLike.ext _ _ fun x ↦ real_smul_apply c f x

end RCLike

end WeakDual

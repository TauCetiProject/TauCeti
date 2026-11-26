/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WeakDual
public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Weak-star continuous functionals and real structure on a weak dual

Every weak-star continuous linear functional on `WeakDual 𝕜 F` is evaluation at a point of `F`.
This is Mathlib's weak representation theorem `LinearMap.dualEmbedding_surjective` for the
canonical pairing `topDualPairing 𝕜 F`, stated directly for the `WeakDual` type synonym, so that
it applies to `WeakDual 𝕜 F` whatever instance path elaborated it. Hahn–Banach separation in a
weak dual produces such functionals, and this lemma turns them into points of the predual.

Over `𝕜 = ℝ` or `ℂ`, the dual `WeakDual 𝕜 F` is also a real vector space. A real multiple `c • f`
is the multiple of `f` by the scalar `(c : 𝕜)`, and acts pointwise as multiplication by `(c : 𝕜)`.
This real structure is compatible with the `𝕜`-structure by the general scalar tower instance
`WeakDual.instIsScalarTower` from `TauCeti.Topology.Algebra.Module.Spaces.WeakDual`, and the
instance `WeakDual.instLocallyConvexSpaceReal` records that the weak-star topology is real locally
convex, as needed for real Hahn–Banach separation and the Krein–Milman theorem.

Precomposition with a continuous linear map `T : E →L[𝕜] F` defines a weak-star continuous
linear map `WeakDual.precomp T : WeakDual 𝕜 F →L[𝕜] WeakDual 𝕜 E` (`WeakDual.precomp_apply`,
`WeakDual.precomp_id`, `WeakDual.precomp_comp`).
-/

public section

namespace WeakDual

section Precomp

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]
  [AddCommMonoid G] [Module 𝕜 G] [TopologicalSpace G]

/-- Precomposition with a continuous linear map `T : E →L[𝕜] F`, as a weak-star continuous
linear map `WeakDual 𝕜 F →L[𝕜] WeakDual 𝕜 E`. -/
noncomputable def precomp (T : E →L[𝕜] F) : WeakDual 𝕜 F →L[𝕜] WeakDual 𝕜 E where
  toFun ω := StrongDual.toWeakDual ((toStrongDual ω).comp T)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_of_continuous_eval fun a => eval_continuous (T a)

/-- Evaluating `WeakDual.precomp T ω` at `x` gives `ω (T x)`. -/
@[simp]
theorem precomp_apply (T : E →L[𝕜] F) (ω : WeakDual 𝕜 F) (x : E) :
    precomp T ω x = ω (T x) :=
  (rfl)

/-- As a strong dual functional, `WeakDual.precomp T ω` is `(toStrongDual ω).comp T`. -/
@[simp]
theorem toStrongDual_precomp (T : E →L[𝕜] F) (ω : WeakDual 𝕜 F) :
    toStrongDual (precomp T ω) = (toStrongDual ω).comp T :=
  (rfl)

/-- Precomposition by the identity map on `E` is the identity on `WeakDual 𝕜 E`. -/
@[simp]
theorem precomp_id :
    precomp (ContinuousLinearMap.id 𝕜 E) = ContinuousLinearMap.id 𝕜 (WeakDual 𝕜 E) :=
  ContinuousLinearMap.ext fun ω => DFunLike.ext _ _ fun x => by simp

/-- Precomposition in the weak-star dual reverses composition of continuous linear maps. -/
@[simp]
theorem precomp_comp (S : F →L[𝕜] G) (T : E →L[𝕜] F) :
    precomp (S.comp T) = (precomp T).comp (precomp S) :=
  ContinuousLinearMap.ext fun ω => DFunLike.ext _ _ fun x => by simp

end Precomp

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
scalar of `𝕜`. -/
theorem real_smul_apply (c : ℝ) (f : WeakDual 𝕜 F) (x : F) : (c • f) x = (c : 𝕜) * f x :=
  -- The real action on `WeakDual 𝕜 F` is pointwise, so `(c • f) x` is `c • f x` by definition,
  -- which `RCLike.real_smul_eq_coe_mul` rewrites.
  RCLike.real_smul_eq_coe_mul c (f x)

/-- A real multiple of a functional in `WeakDual 𝕜 F` is its multiple by the corresponding scalar
of `𝕜`. -/
theorem real_smul_eq_coe_smul (c : ℝ) (f : WeakDual 𝕜 F) : c • f = (c : 𝕜) • f :=
  DFunLike.ext _ _ fun x ↦ real_smul_apply c f x

/-- The weak-star topology on `WeakDual 𝕜 F` is real locally convex: it is defined by the
seminorms of the canonical dual pairing. -/
instance instLocallyConvexSpaceReal {F : Type*} [AddCommGroup F] [Module 𝕜 F]
    [TopologicalSpace F] : LocallyConvexSpace ℝ (WeakDual 𝕜 F) :=
  inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing 𝕜 F)))

end RCLike

end WeakDual

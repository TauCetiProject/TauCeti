/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Basic

/-!
# Representatives of normal classes in a complement of the tangent space

A topological complement `W` of the tangent space of an embedding at `x` picks a canonical
representative of every intrinsic normal class: the unique vector of the class lying in `W`.
This identifies the normal space with `W`, using Mathlib's `Submodule.quotientEquivOfIsTopCompl`.

Specific complements, such as the orthogonal complement for a Riemannian metric or the
symplectic complement of a symplectic submanifold, instantiate this construction.
-/

public section

noncomputable section

open Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω}

/-- A topological complement of the tangent space identifies the intrinsic normal space with
that complement. -/
def normalSpaceComplementEquiv (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    {W : Submodule 𝕜 (TangentSpace J (f x))} (hW : (f.tangentRange x hn).IsTopCompl W) :
    f.NormalSpace x hn ≃L[𝕜] W :=
  (f.tangentRange x hn).quotientEquivOfIsTopCompl W hW

/-- The inverse of the complement equivalence takes the normal class of a vector of the
complement. -/
@[simp]
theorem normalSpaceComplementEquiv_symm_apply (f : SmoothEmbedding I J n M N) (x : M)
    (hn : n ≠ 0) {W : Submodule 𝕜 (TangentSpace J (f x))}
    (hW : (f.tangentRange x hn).IsTopCompl W) (v : W) :
    (f.normalSpaceComplementEquiv x hn hW).symm v = f.normalClass x hn v := by
  rw [normalClass_def]
  exact Submodule.quotientEquivOfIsTopCompl_symm_apply hW v

/-- The **complement representative** of a normal class: the unique vector of the class lying
in the given topological complement `W` of the tangent space. -/
def complementRepresentative (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    {W : Submodule 𝕜 (TangentSpace J (f x))} (hW : (f.tangentRange x hn).IsTopCompl W) :
    f.NormalSpace x hn →L[𝕜] TangentSpace J (f x) :=
  W.subtypeL.comp (f.normalSpaceComplementEquiv x hn hW).toContinuousLinearMap

/-- The complement representative is the vector given by the complement equivalence. -/
theorem complementRepresentative_apply (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    {W : Submodule 𝕜 (TangentSpace J (f x))} (hW : (f.tangentRange x hn).IsTopCompl W)
    (v : f.NormalSpace x hn) :
    f.complementRepresentative x hn hW v = f.normalSpaceComplementEquiv x hn hW v := by
  rw [complementRepresentative, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    ContinuousLinearEquiv.coe_coe]

/-- Taking the normal class of the complement representative recovers the original class. -/
@[simp]
theorem normalClass_complementRepresentative (f : SmoothEmbedding I J n M N) (x : M)
    (hn : n ≠ 0) {W : Submodule 𝕜 (TangentSpace J (f x))}
    (hW : (f.tangentRange x hn).IsTopCompl W) (v : f.NormalSpace x hn) :
    f.normalClass x hn (f.complementRepresentative x hn hW v) = v := by
  rw [complementRepresentative_apply, ← f.normalSpaceComplementEquiv_symm_apply x hn hW,
    ContinuousLinearEquiv.symm_apply_apply]

/-- Complement representatives lie in the complement. -/
theorem complementRepresentative_mem (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    {W : Submodule 𝕜 (TangentSpace J (f x))} (hW : (f.tangentRange x hn).IsTopCompl W)
    (v : f.NormalSpace x hn) :
    f.complementRepresentative x hn hW v ∈ W := by
  rw [complementRepresentative_apply]
  exact (f.normalSpaceComplementEquiv x hn hW v).property

/-- The complement representative is the unique vector of the complement in its normal
class. -/
theorem complementRepresentative_eq_iff (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    {W : Submodule 𝕜 (TangentSpace J (f x))} (hW : (f.tangentRange x hn).IsTopCompl W)
    (v : f.NormalSpace x hn) (w : TangentSpace J (f x)) :
    f.complementRepresentative x hn hW v = w ↔ w ∈ W ∧ f.normalClass x hn w = v := by
  constructor
  · rintro rfl
    exact ⟨f.complementRepresentative_mem x hn hW v,
      f.normalClass_complementRepresentative x hn hW v⟩
  · rintro ⟨hw, rfl⟩
    rw [complementRepresentative_apply,
      ← f.normalSpaceComplementEquiv_symm_apply x hn hW ⟨w, hw⟩,
      ContinuousLinearEquiv.apply_symm_apply]

/-- A vector of the complement is the complement representative of its own normal class. -/
@[simp]
theorem complementRepresentative_normalClass_of_mem (f : SmoothEmbedding I J n M N) (x : M)
    (hn : n ≠ 0) {W : Submodule 𝕜 (TangentSpace J (f x))}
    (hW : (f.tangentRange x hn).IsTopCompl W) {w : TangentSpace J (f x)} (hw : w ∈ W) :
    f.complementRepresentative x hn hW (f.normalClass x hn w) = w :=
  (f.complementRepresentative_eq_iff x hn hW _ w).2 ⟨hw, rfl⟩

/-- The complement representatives fill the complement. -/
theorem range_complementRepresentative (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    {W : Submodule 𝕜 (TangentSpace J (f x))} (hW : (f.tangentRange x hn).IsTopCompl W) :
    LinearMap.range (f.complementRepresentative x hn hW).toLinearMap = W := by
  ext w
  refine ⟨?_, fun hw ↦ ⟨f.normalClass x hn w,
    f.complementRepresentative_normalClass_of_mem x hn hW hw⟩⟩
  rintro ⟨v, rfl⟩
  exact f.complementRepresentative_mem x hn hW v

/-- Taking complement representatives is injective. -/
theorem complementRepresentative_injective (f : SmoothEmbedding I J n M N) (x : M)
    (hn : n ≠ 0) {W : Submodule 𝕜 (TangentSpace J (f x))}
    (hW : (f.tangentRange x hn).IsTopCompl W) :
    Injective (f.complementRepresentative x hn hW) :=
  LeftInverse.injective (f.normalClass_complementRepresentative x hn hW)

end TauCeti.SmoothEmbedding

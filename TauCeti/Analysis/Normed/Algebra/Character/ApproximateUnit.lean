/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.Character.Basic
public import TauCeti.Topology.ApproximateUnit

/-!
# Nonunital characters and approximate units

On a complete normed algebra `A` over a normed field `𝕜`, every algebraic nonunital character
`φ : A →ₙₐ[𝕜] 𝕜` is automatically contractive and hence continuous, bundled as
`φ.toContinuousLinearMap : A →L[𝕜] 𝕜` with `‖φ.toContinuousLinearMap‖ ≤ 1` in
`TauCeti.Analysis.Normed.Algebra.Character.Basic`. This file packages the specialization to
two-sided approximate units (`Filter.IsApproximateUnit`):

* `NonUnitalAlgHom.tendsto_one_of_isApproximateUnit`: along any two-sided approximate unit `l`, a
  nonzero character converges to `1`.
* `NonUnitalAlgHom.norm_toContinuousLinearMap_eq_one_of_isApproximateUnit`: when `l` is eventually
  contained in the closed unit ball, every nonzero algebraic character `φ : A →ₙₐ[𝕜] 𝕜` has
  operator norm `1`.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., §VII.9, Proposition 9.6.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.9.
-/

public section

open Filter Topology

namespace NonUnitalAlgHom

section NormedField

variable {𝕜 A F : Type*} [NormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [CompleteSpace A] [FunLike F A 𝕜] [NonUnitalAlgHomClass F 𝕜 A 𝕜]

/-- Along any two-sided approximate unit `l`, a nonzero character `φ` tends to `1`. -/
theorem tendsto_one_of_isApproximateUnit {l : Filter A} (hl : l.IsApproximateUnit) {φ : F}
    (hφ : ∃ a, φ a ≠ 0) : Tendsto φ l (𝓝 1) :=
  have ⟨_, ha⟩ := hφ
  tendsto_one_of_tendsto_mul_right ha (hl.tendsto_mul_right _)

end NormedField

section NontriviallyNormedField

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [CompleteSpace A]

/-- If `A` has a two-sided approximate unit eventually in the closed unit ball, every nonzero
character `φ : A →ₙₐ[𝕜] 𝕜` has operator norm `1`. -/
theorem norm_toContinuousLinearMap_eq_one_of_isApproximateUnit {l : Filter A}
    (hl : l.IsApproximateUnit) (hl1 : ∀ᶠ u in l, ‖u‖ ≤ 1) {φ : A →ₙₐ[𝕜] 𝕜} (hφ : φ ≠ 0) :
    ‖φ.toContinuousLinearMap‖ = 1 :=
  have := hl.neBot
  norm_toContinuousLinearMap_eq_one_of_tendsto_mul_right hφ hl1 hl.tendsto_mul_right

end NontriviallyNormedField

end NonUnitalAlgHom

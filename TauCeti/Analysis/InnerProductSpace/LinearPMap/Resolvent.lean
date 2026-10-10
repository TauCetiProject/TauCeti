/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint
public import TauCeti.Analysis.Normed.Operator.Resolvent.LowerBound
public import TauCeti.Analysis.Normed.Operator.Resolvent.Spectrum

/-!
# Resolvents of self-adjoint partial linear maps

Every nonreal scalar is a resolvent point of a self-adjoint partial linear map, with the
sharp upper bound `‖R(z)‖ ≤ |im z|⁻¹`. Its spectrum is therefore real. Taking the adjoint of
a resolvent conjugates its scalar parameter; in particular, resolvents at real points are
self-adjoint. These facts provide the bounded inverses used in Cayley transforms and
imaginary-shift approximations of unbounded self-adjoint operators.

The off-real estimates and surjectivity come from
`TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint`; the bounded inverse uses
`LinearPMap.mem_resolventSet_of_surjective_of_norm_le`. The scalar field may be any `RCLike`
field, with no finite-dimensionality assumption.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  Chapter VIII.
* J. Weidmann, *Linear Operators in Hilbert Spaces*, Chapter 5.
-/

public section

namespace TauCeti

open _root_.LinearPMap
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {A B : E →ₗ.[𝕜] E} {z : 𝕜}

/-- At an existing resolvent point, symmetry alone gives the sharp off-real bound. -/
theorem _root_.LinearPMap.IsFormalAdjoint.norm_resolvent_le
    (hA : A.IsFormalAdjoint A) (hz : z ∈ A.resolventSet) (him : RCLike.im z ≠ 0) :
    ‖A.resolvent z‖ ≤ |RCLike.im z|⁻¹ :=
  (isResolventAt_resolvent hz).norm_le_inv (abs_pos.mpr him)
    (hA.abs_im_mul_norm_le_norm_smul_sub z)

variable [CompleteSpace E]

/-- Every nonreal scalar is a resolvent point of a self-adjoint partial linear map. -/
theorem _root_.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero
    (hA : IsSelfAdjoint A) (him : RCLike.im z ≠ 0) : z ∈ A.resolventSet :=
  mem_resolventSet_of_surjective_of_norm_le (hA.smul_sub_surjective him)
    (abs_pos.mpr him) (hA.isFormalAdjoint.abs_im_mul_norm_le_norm_smul_sub z)

/-- The spectrum of a self-adjoint partial linear map is contained in the real axis. -/
theorem _root_.IsSelfAdjoint.spectrum_subset_im_eq_zero (hA : IsSelfAdjoint A) :
    partialSpectrum A ⊆ {z | RCLike.im z = 0} := by
  intro z hz
  by_contra him
  exact (mem_partialSpectrum_iff A z).mp hz (hA.mem_resolventSet_of_im_ne_zero him)

/-- The resolvent of a self-adjoint partial linear map obeys the sharp off-real norm bound. -/
theorem _root_.IsSelfAdjoint.norm_resolvent_le (hA : IsSelfAdjoint A)
    (him : RCLike.im z ≠ 0) : ‖A.resolvent z‖ ≤ |RCLike.im z|⁻¹ :=
  hA.isFormalAdjoint.norm_resolvent_le (hA.mem_resolventSet_of_im_ne_zero him) him

/-- Resolvents of formally adjoint partial operators are adjoints at conjugate parameters,
whenever both resolvents exist. -/
theorem _root_.LinearPMap.IsFormalAdjoint.adjoint_resolvent_eq
    (hAB : A.IsFormalAdjoint B) (hz : z ∈ A.resolventSet)
    (hconj : (starRingEnd 𝕜) z ∈ B.resolventSet) :
    (A.resolvent z).adjoint = B.resolvent ((starRingEnd 𝕜) z) := by
  have hpair (u : A.domain) (v : B.domain) :
      ⟪z • (u : E) - A u, (v : E)⟫_𝕜 =
        ⟪(u : E), (starRingEnd 𝕜) z • (v : E) - B v⟫_𝕜 := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hAB u v]
  ext y
  apply ext_inner_left 𝕜
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  have h := hpair ⟨A.resolvent z x, resolvent_mem_domain hz x⟩
    ⟨B.resolvent ((starRingEnd 𝕜) z) y, resolvent_mem_domain hconj y⟩
  simpa only [smul_sub_apply_resolvent hz, smul_sub_apply_resolvent hconj] using h.symm

/-- The resolvent set of a self-adjoint partial linear map is stable under conjugation. -/
theorem _root_.IsSelfAdjoint.conj_mem_resolventSet (hA : IsSelfAdjoint A)
    (hz : z ∈ A.resolventSet) : (starRingEnd 𝕜) z ∈ A.resolventSet := by
  by_cases him : RCLike.im z = 0
  · rwa [RCLike.conj_eq_iff_im.mpr him]
  · apply hA.mem_resolventSet_of_im_ne_zero
    simpa only [RCLike.conj_im, ne_eq, neg_eq_zero] using him

/-- Taking the adjoint of a self-adjoint operator's resolvent conjugates the parameter. -/
theorem _root_.IsSelfAdjoint.adjoint_resolvent (hA : IsSelfAdjoint A)
    (hz : z ∈ A.resolventSet) :
    (A.resolvent z).adjoint = A.resolvent ((starRingEnd 𝕜) z) :=
  hA.isFormalAdjoint.adjoint_resolvent_eq hz (hA.conj_mem_resolventSet hz)

/-- At a real resolvent point, the bounded resolvent is self-adjoint. -/
theorem _root_.IsSelfAdjoint.isSelfAdjoint_resolvent (hA : IsSelfAdjoint A)
    (hz : z ∈ A.resolventSet) (him : RCLike.im z = 0) :
    IsSelfAdjoint (A.resolvent z) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', hA.adjoint_resolvent hz,
    RCLike.conj_eq_iff_im.mpr him]

end TauCeti

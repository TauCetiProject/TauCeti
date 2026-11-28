/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.Algebra.MonoidAlgebra.Star
import TauCeti.Algebra.MonoidAlgebra.Basic

/-!
# Identity coefficients of squares in a group algebra

The pairing given by the identity coefficient of `x * star x` is diagonal in the group basis.
In particular, the identity coefficient of a self-adjoint idempotent measures its coefficient
energy, not just its value at a single group element.
-/

public section

namespace IsStarProjection

/-- The squared coefficient norm of a self-adjoint idempotent in a real or complex group
algebra is the real part of its coefficient at the identity. -/
theorem sum_sq_norm_coeff_eq_re_coeff_one {𝕜 G : Type*} [RCLike 𝕜] [Group G] [Fintype G]
    {e : MonoidAlgebra 𝕜 G} (he : IsStarProjection e) :
    ∑ g : G, ‖e.coeff g‖ ^ 2 = RCLike.re (e.coeff 1) := by
  have he' : e * star e = e := by rw [he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq]
  have h := congrArg (fun x : MonoidAlgebra 𝕜 G ↦ RCLike.re (x.coeff 1)) he'
  simpa only [MonoidAlgebra.coeff_mul_eq_sum, mul_one, MonoidAlgebra.coeff_star, inv_inv,
    RCLike.star_def, RCLike.mul_conj, map_sum, ← RCLike.ofReal_pow, RCLike.ofReal_re] using h

end IsStarProjection

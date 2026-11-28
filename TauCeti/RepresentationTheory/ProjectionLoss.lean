/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius.Trace
public import TauCeti.RepresentationTheory.Unitary
public import TauCeti.Algebra.MonoidAlgebra.Star
import TauCeti.Algebra.MonoidAlgebra.Parseval
import TauCeti.RepresentationTheory.AsAlgebraHom

/-!
# Projection loss from a compression second moment

For a unitary action `ρ`, the energy of `P` captured by a group-algebra projection `e` is
controlled by the traces of a model for the compressions `P† ρ(g) P` and the second moment of the
model error. The factor contributed by the projection in the error term is the square root of
its identity coefficient, not the size of the group. Applied to the complement of a projection,
this bounds the discarded energy before the second-moment argument for spanning by translates.

The one-factor estimate is the linear-algebra step of
`New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_asAlgebraHom_comp_sq_le` in
`grh/src/New/Spanning/Unfolding/Moments.lean` of lsernau/grh-lean (revision `72fead1`).
-/

public section

open LinearMap Module TauCeti.UnitarilyInvariantSeminorm
open scoped InnerProductSpace

namespace Representation

/-- For a unitary representation and a self-adjoint idempotent `e` in the group algebra,
`‖ρ(e) P‖_F²` is bounded by the `e`-weighted trace of any model `R g` for `P† ρ(g) P`, plus
an error given by the compression error's second moment. This also applies to a representation
restricted to one factor of a product, without any bound on the other factors. -/
theorem sq_frobenius_asAlgebraHom_comp_le {𝕜 G S T : Type*} [RCLike 𝕜] [Group G] [Fintype G]
    [NormedAddCommGroup S] [InnerProductSpace 𝕜 S] [FiniteDimensional 𝕜 S]
    [NormedAddCommGroup T] [InnerProductSpace 𝕜 T] [FiniteDimensional 𝕜 T]
    (ρ : Representation 𝕜 G T) (hρ : ∀ g v w, ⟪ρ g v, ρ g w⟫_𝕜 = ⟪v, w⟫_𝕜)
    {e : MonoidAlgebra 𝕜 G} (he : IsStarProjection e) (P : S →ₗ[𝕜] T) (R : G → End 𝕜 S) :
    frobenius 𝕜 S T (ρ.asAlgebraHom e ∘ₗ P) ^ 2 ≤
      RCLike.re (∑ g, e.coeff g * trace 𝕜 S (R g)) +
        √(finrank 𝕜 S : ℝ) * √(RCLike.re (e.coeff 1)) *
          √(∑ g, frobenius 𝕜 S S (P.adjoint ∘ₗ ρ g ∘ₗ P - R g) ^ 2) := by
  let p := ρ.asAlgebraHom e
  let D (g : G) := P.adjoint ∘ₗ ρ g ∘ₗ P - R g
  have hs (g : G) : e.coeff g⁻¹ = star (e.coeff g) := by
    simpa only [he.isSelfAdjoint.star_eq, inv_inv] using MonoidAlgebra.coeff_star e g⁻¹
  have hp : p.IsSymmetricProjection :=
    ρ.isSymmetricProjection_asAlgebraHom hρ hs he.isIdempotentElem
  have hcompress : P.adjoint ∘ₗ p ∘ₗ P = ∑ g, e.coeff g • (P.adjoint ∘ₗ ρ g ∘ₗ P) := by
    ext v
    simp [p, asAlgebraHom_eq_sum]
  have htrace : frobenius 𝕜 S T (p ∘ₗ P) ^ 2 =
      RCLike.re (∑ g, e.coeff g * trace 𝕜 S (R g)) +
      RCLike.re (∑ g, e.coeff g * trace 𝕜 S (D g)) := by
    have hproj : (p ∘ₗ P).adjoint ∘ₗ (p ∘ₗ P) = P.adjoint ∘ₗ p ∘ₗ P := by
      have hpp : p ∘ₗ p = p := hp.isIdempotentElem.eq
      rw [adjoint_comp, hp.isSymmetric.adjoint_eq, comp_assoc, ← comp_assoc P p p, hpp]
    rw [sq_frobenius_eq_re_trace, hproj, hcompress]
    simp only [map_sum, map_smul, smul_eq_mul, D, map_sub, mul_sub, Finset.sum_sub_distrib]
    ring
  have hid : frobenius 𝕜 S S (.id : S →ₗ[𝕜] S) = √(finrank 𝕜 S : ℝ) := by
    simp [frobenius_apply (stdOrthonormalBasis 𝕜 S)]
  rw [htrace]
  apply add_le_add_right
  calc
    _ ≤ ∑ g, ‖e.coeff g‖ * ‖trace 𝕜 S (D g)‖ := by
      simpa only [map_sum, norm_mul] using
        (Finset.sum_le_sum fun g _ ↦ RCLike.re_le_norm (e.coeff g * trace 𝕜 S (D g)))
    _ ≤ ∑ g, ‖e.coeff g‖ * (√(finrank 𝕜 S : ℝ) * frobenius 𝕜 S S (D g)) := by
      refine Finset.sum_le_sum fun g _ ↦ mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      simpa only [adjoint_id, id_comp, hid] using norm_trace_adjoint_comp_le (.id : S →ₗ[𝕜] S) (D g)
    _ = √(finrank 𝕜 S : ℝ) * ∑ g, ‖e.coeff g‖ * frobenius 𝕜 S S (D g) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ mul_left_comm _ _ _
    _ ≤ _ := by
      rw [mul_assoc, ← he.sum_sq_norm_coeff_eq_re_coeff_one]
      exact mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) (Real.sqrt_nonneg _)

end Representation

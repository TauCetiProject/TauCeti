/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.FanDominance
public import TauCeti.Analysis.InnerProductSpace.PositiveSquareRoot

/-!
# The polar factorization of an injective map

Let `A : E → F` be an injective linear map between finite-dimensional real or complex inner
product spaces.  Its modulus `|A| = √(A† A)` (`LinearMap.operatorAbs`) has the same pointwise norms
as `A`, so it is injective, hence invertible.  The map `W = A |A|⁻¹` is then an isometric
embedding of `E` into `F`, and `A = W |A|`.  In other words `A` factors as an isometric embedding,
the *orthonormalization* of `A`, after an invertible positive coordinate change on its source.
The isometric factor has the same range as `A`, and the factorization is unique among
factorizations `A = W C` with `W` isometric and `C` positive.

A lower frame bound `‖x‖ ≤ c ‖A x‖` controls the inverse coordinate change:
`‖|A|⁻¹ y‖ ≤ c ‖y‖`.  Consequently, composing with `|A|⁻¹` on the right costs at most a factor `c`
in every unitarily invariant seminorm.  This is how estimates proved for isometric embeddings
transfer to arbitrary injective maps, such as a basis of a trial subspace in subspace
perturbation theory.

## Main declarations

* `LinearMap.operatorAbsEquiv`: the modulus of an injective map, as a linear automorphism.
* `LinearMap.polarIsometry`: the isometric polar factor `A |A|⁻¹` of an injective map.
* `LinearMap.polarIsometry_comp_operatorAbs`: the polar factorization `A = W |A|`.
* `LinearMap.range_polarIsometry`: the polar factor has the same range as `A`.
* `LinearMap.IsPositive.eq_operatorAbs_of_comp_eq`, `LinearMap.eq_polarIsometry_of_comp_eq`:
  uniqueness of the factorization.
* `LinearMap.norm_operatorAbsEquiv_symm_apply_le`: a lower frame bound for `A` bounds `|A|⁻¹`.
* `TauCeti.UnitarilyInvariantSeminorm.map_comp_operatorAbsEquiv_symm_le`: the resulting cost
  of composing with `|A|⁻¹` in a unitarily invariant seminorm.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Theorem 7.3.1.
-/

public section

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The modulus of a map is injective exactly when the map is. -/
@[simp]
theorem injective_operatorAbs_iff {A : E →ₗ[𝕜] F} :
    Function.Injective A.operatorAbs ↔ Function.Injective A := by
  rw [← ker_eq_bot, ← ker_eq_bot, ker_operatorAbs]

variable (A : E →ₗ[𝕜] F) (hA : Function.Injective A)

/-- The modulus `|A|` of an injective map `A`, as a linear automorphism of the source. -/
noncomputable def operatorAbsEquiv : E ≃ₗ[𝕜] E :=
  LinearEquiv.ofInjectiveEndo A.operatorAbs (injective_operatorAbs_iff.2 hA)

@[simp]
theorem coe_operatorAbsEquiv : ⇑(A.operatorAbsEquiv hA) = A.operatorAbs :=
  (rfl)

@[simp]
theorem toLinearMap_operatorAbsEquiv : (A.operatorAbsEquiv hA : E →ₗ[𝕜] E) = A.operatorAbs :=
  (rfl)

@[simp]
theorem operatorAbs_operatorAbsEquiv_symm_apply (y : E) :
    A.operatorAbs ((A.operatorAbsEquiv hA).symm y) = y :=
  (A.operatorAbsEquiv hA).apply_symm_apply y

@[simp]
theorem operatorAbsEquiv_symm_operatorAbs_apply (x : E) :
    (A.operatorAbsEquiv hA).symm (A.operatorAbs x) = x :=
  (A.operatorAbsEquiv hA).symm_apply_apply x

/-- The isometric polar factor `A |A|⁻¹` of an injective map `A`: the isometric embedding through
which `A` factors after the positive coordinate change `|A|` of its source. -/
noncomputable def polarIsometry : E →ₗᵢ[𝕜] F where
  toLinearMap := A ∘ₗ ((A.operatorAbsEquiv hA).symm : E →ₗ[𝕜] E)
  norm_map' y := by
    simpa using (A.norm_operatorAbs_apply ((A.operatorAbsEquiv hA).symm y)).symm

theorem polarIsometry_apply (y : E) :
    A.polarIsometry hA y = A ((A.operatorAbsEquiv hA).symm y) :=
  (rfl)

theorem polarIsometry_toLinearMap :
    (A.polarIsometry hA).toLinearMap = A ∘ₗ ((A.operatorAbsEquiv hA).symm : E →ₗ[𝕜] E) :=
  (rfl)

/-- The isometric polar factor carries `|A| x` to `A x`. -/
@[simp]
theorem polarIsometry_apply_operatorAbs (x : E) :
    A.polarIsometry hA (A.operatorAbs x) = A x := by
  simp [polarIsometry_apply]

/-- **Polar factorization of an injective map.** An injective map `A` is its isometric polar
factor composed with its modulus: `A = W |A|`. -/
@[simp]
theorem polarIsometry_comp_operatorAbs :
    (A.polarIsometry hA).toLinearMap ∘ₗ A.operatorAbs = A :=
  ext <| A.polarIsometry_apply_operatorAbs hA

/-- The isometric polar factor of an injective map has the same range as the map. -/
@[simp]
theorem range_polarIsometry : range (A.polarIsometry hA).toLinearMap = range A := by
  rw [polarIsometry_toLinearMap, range_comp_of_range_eq_top _ (A.operatorAbsEquiv hA).symm.range]

variable {A}

/-- **Uniqueness of the positive factor.** If `A = W C` with `W` an isometric embedding and `C`
positive, then `C` is the modulus of `A`. -/
theorem IsPositive.eq_operatorAbs_of_comp_eq {C : E →ₗ[𝕜] E} (hC : C.IsPositive) (W : E →ₗᵢ[𝕜] F)
    (hWC : W.toLinearMap ∘ₗ C = A) : C = A.operatorAbs := by
  have hT := isPositive_adjoint_comp_self A
  rw [hT.sqrt_unique A.isPositive_operatorAbs A.operatorAbs_sq]
  refine hT.sqrt_unique hC ?_
  rw [← hWC, adjoint_comp, comp_assoc, ← comp_assoc C, LinearIsometry.adjoint_comp_self', id_comp,
    hC.isSymmetric.adjoint_eq]

/-- **Uniqueness of the isometric factor.** If `A = W C` with `W` an isometric embedding and `C`
positive, then `W` is the isometric polar factor of `A`. -/
theorem eq_polarIsometry_of_comp_eq {C : E →ₗ[𝕜] E} (hC : C.IsPositive) (W : E →ₗᵢ[𝕜] F)
    (hWC : W.toLinearMap ∘ₗ C = A) : W = A.polarIsometry hA := by
  obtain rfl := hC.eq_operatorAbs_of_comp_eq W hWC
  ext y
  obtain ⟨x, rfl⟩ := (A.operatorAbsEquiv hA).surjective y
  simpa using congr($hWC x)

/-- **Inverse-coordinate bound.** If `A` satisfies the lower frame bound `‖x‖ ≤ c ‖A x‖`, then the
inverse of its modulus satisfies `‖|A|⁻¹ y‖ ≤ c ‖y‖`.  For `ε > 0`, the frame bound
`ε ‖x‖ ≤ ‖A x‖` is the case `c = ε⁻¹`. -/
theorem norm_operatorAbsEquiv_symm_apply_le {c : ℝ} (hc : ∀ x, ‖x‖ ≤ c * ‖A x‖) (y : E) :
    ‖(A.operatorAbsEquiv hA).symm y‖ ≤ c * ‖y‖ := by
  simpa [← A.norm_operatorAbs_apply] using hc ((A.operatorAbsEquiv hA).symm y)

end LinearMap

namespace TauCeti.UnitarilyInvariantSeminorm

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]

/-- **Composition cost of the inverse modulus.** If the injective map `A : E → F` satisfies the
lower frame bound `‖x‖ ≤ c ‖A x‖`, then `N (B |A|⁻¹) ≤ c N(B)` for every map `B : E → G` and every
unitarily invariant seminorm `N`. -/
theorem map_comp_operatorAbsEquiv_symm_le (N : UnitarilyInvariantSeminorm 𝕜 E G) (B : E →ₗ[𝕜] G)
    {A : E →ₗ[𝕜] F} (hA : Function.Injective A) {c : ℝ} (hc : ∀ x, ‖x‖ ≤ c * ‖A x‖) :
    N (B ∘ₗ ((A.operatorAbsEquiv hA).symm : E →ₗ[𝕜] E)) ≤ c * N B :=
  N.map_comp_le_right B _ (A.norm_operatorAbsEquiv_symm_apply_le hA hc)

end TauCeti.UnitarilyInvariantSeminorm

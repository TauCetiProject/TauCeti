/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Gram.Factor
public import TauCeti.Analysis.InnerProductSpace.PartialIsometry
public import TauCeti.Analysis.InnerProductSpace.PositiveSquareRoot

/-!
# The canonical finite-dimensional polar factor

Every linear map `A` between finite-dimensional real or complex inner product spaces factors as
`A = U |A|`, where `|A|` is its positive modulus and `U` is a partial isometry. The canonical
factor `A.polarFactor` extends the isometric rule `|A| x ↦ A x` by zero on `ker A`. It has the
same kernel and range as `A`, and is the unique factor through the modulus that vanishes on
`ker A`. This normalization distinguishes it from unitary extensions of the polar factor.

The construction uses `ContinuousLinearMap.factorThru` and the finite-dimensional modulus;
it applies to rectangular maps, including maps with nontrivial kernel. Its initial space is
`(ker A)ᗮ` and its final space is `range A`.

The adjoint of the polar factor inverts it on the modulus, `U† A = |A|`, and conjugates the two
moduli into each other, `|A†| = A U† = U |A| U†`. Consequently the canonical polar factor of `A†`
is `U†`, and `A = |A†| U` is the left polar decomposition. Between spaces of the same dimension,
`U` agrees on `(ker A)ᗮ` with a linear isometric equivalence, and it is one when `A` is
injective.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Theorem 7.3.1.
* J. B. Conway, *A Course in Functional Analysis*, second edition, Springer, 1990, §VI.3.
-/

public section

noncomputable section

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The canonical polar partial isometry of a finite-dimensional linear map. It sends
`|A| x` to `A x` and vanishes on `ker A`. -/
def polarFactor (A : E →ₗ[𝕜] F) : E →ₗ[𝕜] F :=
  letI := FiniteDimensional.complete 𝕜 E
  letI := FiniteDimensional.complete 𝕜 F
  (A.toContinuousLinearMap.factorThru A.operatorAbs.toContinuousLinearMap).toLinearMap

/-- The polar factor as a bounded operator is the canonical factor through the modulus. -/
theorem toContinuousLinearMap_polarFactor (A : E →ₗ[𝕜] F) :
    let := FiniteDimensional.complete 𝕜 E
    let := FiniteDimensional.complete 𝕜 F
    A.polarFactor.toContinuousLinearMap =
      A.toContinuousLinearMap.factorThru A.operatorAbs.toContinuousLinearMap := by
  intros
  apply ContinuousLinearMap.coe_inj.mp
  simp [polarFactor]

/-- The polar factor carries the modulus of a vector to its image under the original map. -/
@[simp]
theorem polarFactor_operatorAbs_apply (A : E →ₗ[𝕜] F) (x : E) :
    A.polarFactor (A.operatorAbs x) = A x := by
  let := FiniteDimensional.complete 𝕜 E
  let := FiniteDimensional.complete 𝕜 F
  rw [← coe_toContinuousLinearMap A.polarFactor, A.toContinuousLinearMap_polarFactor]
  exact ContinuousLinearMap.factorThru_apply_apply
    (T := A.toContinuousLinearMap) (A := A.operatorAbs.toContinuousLinearMap)
    ⟨1, fun x ↦ by simp⟩ x

/-- **Finite-dimensional polar decomposition:** `A = U |A|` for its canonical polar factor. -/
@[simp]
theorem polarFactor_comp_operatorAbs (A : E →ₗ[𝕜] F) :
    A.polarFactor ∘ₗ A.operatorAbs = A :=
  LinearMap.ext (A.polarFactor_operatorAbs_apply)

/-- The polar factor vanishes on the kernel of the original map. -/
@[simp]
theorem polarFactor_apply_of_mem_ker (A : E →ₗ[𝕜] F) {x : E} (hx : x ∈ A.ker) :
    A.polarFactor x = 0 := by
  let := FiniteDimensional.complete 𝕜 E
  let := FiniteDimensional.complete 𝕜 F
  rw [← coe_toContinuousLinearMap A.polarFactor, A.toContinuousLinearMap_polarFactor]
  apply ContinuousLinearMap.factorThru_apply_of_mem_orthogonal
    (T := A.toContinuousLinearMap) (A := A.operatorAbs.toContinuousLinearMap)
  simpa using hx

/-- The canonical polar factor preserves norms on the initial space `(ker A)ᗮ`. -/
theorem norm_polarFactor_apply (A : E →ₗ[𝕜] F) {x : E} (hx : x ∈ A.kerᗮ) :
    ‖A.polarFactor x‖ = ‖x‖ := by
  rw [← A.range_operatorAbs] at hx
  obtain ⟨y, rfl⟩ := hx
  simp

/-- The canonical polar factor has exactly the same kernel as the original map. -/
@[simp]
theorem ker_polarFactor (A : E →ₗ[𝕜] F) : A.polarFactor.ker = A.ker := by
  apply le_antisymm
  · intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := A.ker.exists_add_mem_mem_orthogonal x
    have hv₀ : A.polarFactor v = 0 := by
      simpa [LinearMap.mem_ker, A.polarFactor_apply_of_mem_ker hu] using hx
    have hvnorm := A.norm_polarFactor_apply hv
    rw [hv₀, norm_zero] at hvnorm
    simpa [norm_eq_zero.mp hvnorm.symm] using hu
  · intro x hx
    exact A.polarFactor_apply_of_mem_ker hx

/-- The canonical polar factor is a partial isometry. -/
@[simp]
theorem isPartialIsometry_polarFactor (A : E →ₗ[𝕜] F) : A.polarFactor.IsPartialIsometry := by
  rw [isPartialIsometry_iff_norm_map, A.ker_polarFactor]
  exact fun _ hx ↦ A.norm_polarFactor_apply hx

/-- The canonical polar factor has exactly the same range as the original map. -/
@[simp]
theorem range_polarFactor (A : E →ₗ[𝕜] F) : A.polarFactor.range = A.range := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := A.ker.exists_add_mem_mem_orthogonal x
    rw [← A.range_operatorAbs] at hv
    obtain ⟨y, rfl⟩ := hv
    simp only [map_add, A.polarFactor_apply_of_mem_ker hu,
      A.polarFactor_operatorAbs_apply, zero_add]
    exact ⟨y, rfl⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨A.operatorAbs x, A.polarFactor_operatorAbs_apply x⟩

/-- The factorization through the modulus and vanishing on `ker A` characterize the canonical
polar factor, without assuming that the competing factor is a partial isometry. -/
theorem eq_polarFactor (A : E →ₗ[𝕜] F) {V : E →ₗ[𝕜] F}
    (hV : V ∘ₗ A.operatorAbs = A) (hV₀ : ∀ x ∈ A.ker, V x = 0) : V = A.polarFactor := by
  let := FiniteDimensional.complete 𝕜 E
  let := FiniteDimensional.complete 𝕜 F
  apply toContinuousLinearMap.injective
  rw [A.toContinuousLinearMap_polarFactor]
  apply ContinuousLinearMap.eq_factorThru
  · apply ContinuousLinearMap.coe_inj.mp
    simpa using hV
  · simpa using hV₀

/-- A map is the canonical polar factor exactly when it factors the original map through its
modulus and vanishes on its kernel. -/
theorem eq_polarFactor_iff (A : E →ₗ[𝕜] F) {V : E →ₗ[𝕜] F} :
    V = A.polarFactor ↔ V ∘ₗ A.operatorAbs = A ∧ ∀ x ∈ A.ker, V x = 0 := by
  constructor
  · rintro rfl
    exact ⟨A.polarFactor_comp_operatorAbs, fun _ hx ↦ A.polarFactor_apply_of_mem_ker hx⟩
  · rintro ⟨hV, hV₀⟩
    exact A.eq_polarFactor hV hV₀

/-- The canonical polar factor of the zero map is zero. -/
@[simp]
theorem polarFactor_zero : (0 : E →ₗ[𝕜] F).polarFactor = 0 := by
  ext x
  exact (0 : E →ₗ[𝕜] F).polarFactor_apply_of_mem_ker (by simp)

/-! ### The adjoint of the polar factor -/

/-- The adjoint of the canonical polar factor carries the original map back to its modulus:
`U† A = |A|`. -/
@[simp]
theorem adjoint_polarFactor_comp (A : E →ₗ[𝕜] F) :
    A.polarFactor.adjoint ∘ₗ A = A.operatorAbs := by
  let := FiniteDimensional.complete 𝕜 E
  let := FiniteDimensional.complete 𝕜 F
  have h := ContinuousLinearMap.adjoint_factorThru_comp
    (T := A.toContinuousLinearMap) (A := A.operatorAbs.toContinuousLinearMap) (by simp)
  rw [← A.toContinuousLinearMap_polarFactor] at h
  ext x
  simpa [adjoint_eq_toCLM_adjoint] using congr($h x)

/-- The adjoint of the polar decomposition: `A† = |A| U†`. -/
@[simp]
theorem operatorAbs_comp_adjoint_polarFactor (A : E →ₗ[𝕜] F) :
    A.operatorAbs ∘ₗ A.polarFactor.adjoint = A.adjoint := by
  conv_rhs => rw [← A.polarFactor_comp_operatorAbs]
  rw [adjoint_comp, A.isPositive_operatorAbs.adjoint_eq]

/-- The modulus of the adjoint is the original map composed with the adjoint of its canonical
polar factor: `|A†| = A U†`, equivalently `|A†| = U |A| U†`. -/
theorem operatorAbs_adjoint (A : E →ₗ[𝕜] F) :
    A.adjoint.operatorAbs = A ∘ₗ A.polarFactor.adjoint := by
  symm
  refine IsPositive.eq_operatorAbs ?_ ?_
  · have h : A ∘ₗ A.polarFactor.adjoint =
        A.polarFactor ∘ₗ A.operatorAbs ∘ₗ A.polarFactor.adjoint := by
      rw [← comp_assoc, polarFactor_comp_operatorAbs]
    rw [h]
    exact A.isPositive_operatorAbs.conj_adjoint A.polarFactor
  · rw [adjoint_adjoint, comp_assoc, ← comp_assoc A.polarFactor.adjoint,
      adjoint_polarFactor_comp, operatorAbs_comp_adjoint_polarFactor]

/-- The canonical polar factor of the adjoint is the adjoint of the canonical polar factor. -/
@[simp]
theorem polarFactor_adjoint (A : E →ₗ[𝕜] F) : A.adjoint.polarFactor = A.polarFactor.adjoint := by
  symm
  refine A.adjoint.eq_polarFactor ?_ fun y hy ↦ ?_
  · rw [operatorAbs_adjoint, ← comp_assoc, adjoint_polarFactor_comp,
      operatorAbs_comp_adjoint_polarFactor]
  · -- `ker U† = (range U)ᗮ = (range A)ᗮ = ker A†`.
    have hy' : y ∈ A.polarFactor.adjoint.ker := by
      rwa [← orthogonal_range, range_polarFactor, orthogonal_range]
    exact mem_ker.mp hy'

/-- **Left polar decomposition:** `A = |A†| U` for the canonical polar factor `U` of `A`. -/
@[simp]
theorem operatorAbs_adjoint_comp_polarFactor (A : E →ₗ[𝕜] F) :
    A.adjoint.operatorAbs ∘ₗ A.polarFactor = A := by
  have h := congrArg adjoint A.adjoint.polarFactor_comp_operatorAbs
  rwa [polarFactor_adjoint, adjoint_comp, adjoint_adjoint, adjoint_adjoint,
    A.adjoint.isPositive_operatorAbs.adjoint_eq] at h

/-! ### Unitary extensions -/

/-- **Unitary extension of the polar factor.** Between spaces of the same dimension, the canonical
polar factor agrees on its initial space `(ker A)ᗮ` with a linear isometric equivalence. -/
theorem exists_linearIsometryEquiv_eqOn_polarFactor (A : E →ₗ[𝕜] F)
    (h : Module.finrank 𝕜 E = Module.finrank 𝕜 F) :
    ∃ U : E ≃ₗᵢ[𝕜] F, Set.EqOn U A.polarFactor A.kerᗮ := by
  let e : F ≃ₗᵢ[𝕜] E := ((stdOrthonormalBasis 𝕜 F).reindex (finCongr h.symm)).repr.trans
    (stdOrthonormalBasis 𝕜 E).repr.symm
  let L : A.kerᗮ →ₗᵢ[𝕜] E :=
    { toLinearMap := e.toLinearMap ∘ₗ A.polarFactor ∘ₗ A.kerᗮ.subtype
      norm_map' := fun x ↦ by simp [A.norm_polarFactor_apply x.2] }
  refine ⟨(L.extend.toLinearIsometryEquiv rfl).trans e.symm, fun x hx ↦ ?_⟩
  have hL : L.extend x = e (A.polarFactor x) := L.extend_apply ⟨x, hx⟩
  simp [hL]

/-- **Invertible polar unitary.** Between spaces of the same dimension, the canonical polar
factor of an injective map is a linear isometric equivalence. -/
theorem exists_linearIsometryEquiv_eq_polarFactor {A : E →ₗ[𝕜] F} (hA : Function.Injective A)
    (h : Module.finrank 𝕜 E = Module.finrank 𝕜 F) :
    ∃ U : E ≃ₗᵢ[𝕜] F, (U : E →ₗ[𝕜] F) = A.polarFactor := by
  obtain ⟨U, hU⟩ := A.exists_linearIsometryEquiv_eqOn_polarFactor h
  exact ⟨U, LinearMap.ext fun x ↦ hU (by simp [ker_eq_bot.mpr hA])⟩

end LinearMap

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Geometry.Symplectic.Complex.Module.Basic

/-!
# Real-linear complex structures are conjugate to multiplication by `i`

On a finite-dimensional complex normed space `V`, every real-linear `A` with `A² = -1` is
conjugate to multiplication by `i` through a real-linear automorphism: it sends an adapted basis
`(v₁, i v₁, …, vₙ, i vₙ)` of `i` (`TauCeti.AlmostComplexStructure.exists_basis_apply_one_eq`) to
one `(w₁, A w₁, …, wₙ, A wₙ)` of `A`. This is the pointwise normal form behind the reduction of a
variable complex structure to the standard one in the vector similarity principle.

On a finite-dimensional real normed space `E` the same normal form holds with a complex
coordinate space as the model: every real-linear `A` with `A² = -1` is multiplication by `i` in
some real-linear frame `ℂⁿ → E`. Such frames turn an equation involving a variable complex
structure near one point into an equation on a complex inner product space whose structure is
close to `i`.

## Main declarations

* `ContinuousLinearMap.exists_continuousLinearEquiv_comp_eq_comp_I_smul`: `A Φ₁ = Φ₁ i` for some
  real-linear automorphism `Φ₁`.
* `ContinuousLinearMap.exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul`:
  `A Φ = Φ i` for some real-linear isomorphism `Φ : ℂⁿ → E`, on a real normed space `E`.
* `ContinuousLinearEquiv.symm_apply_eq_I_smul_symm_of_comp_eq`: in such a frame,
  `Φ⁻¹ A = i Φ⁻¹`.
* `TauCeti.exists_complexLinear_and_bijective_coprod`: a complex-linear frame `ℂⁿ → E` of a
  complement of the image of a nonzero complex-linear map `ℂ → E`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.3 (proof of Theorem 2.3.5).
-/

public section

open Complex TauCeti

namespace ContinuousLinearMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- **Adapted frames at a point.** A real-linear `A` with `A² = -1` on a finite-dimensional complex
vector space is conjugate to multiplication by `i`: some real-linear automorphism `Φ₁` satisfies
`A Φ₁ = Φ₁ i`. It sends an adapted basis `(v₁, i v₁, …, vₙ, i vₙ)` to an adapted basis
`(w₁, A w₁, …, wₙ, A wₙ)`. -/
theorem exists_continuousLinearEquiv_comp_eq_comp_I_smul (A : V →L[ℝ] V)
    (hA : A ∘L A = -ContinuousLinearMap.id ℝ V) :
    ∃ Φ₁ : V ≃L[ℝ] V,
      A ∘L (Φ₁ : V →L[ℝ] V) = (Φ₁ : V →L[ℝ] V) ∘L (I • ContinuousLinearMap.id ℝ V) := by
  have hA' (v : V) : A (A v) = -v := congr($hA v)
  let JA : AlmostComplexStructure V := ⟨A.toLinearMap, by ext v; exact hA' v⟩
  obtain ⟨n, bA, hbA⟩ := JA.exists_basis_apply_one_eq
  obtain ⟨m, bI, hbI⟩ := (AlmostComplexStructure.ofComplexModule V).exists_basis_apply_one_eq
  obtain rfl : n = m := by
    have h := (Module.finrank_eq_card_basis bA).symm.trans (Module.finrank_eq_card_basis bI)
    simp only [Fintype.card_prod, Fintype.card_fin] at h
    omega
  have hbA' (i : Fin n) : bA (i, 1) = A (bA (i, 0)) := hbA i
  have hbI₀ (i : Fin n) : I • bI (i, 0) = bI (i, 1) := by
    rw [hbI i]
    exact (AlmostComplexStructure.ofComplexModule_apply _).symm
  have hbI₁ (i : Fin n) : I • bI (i, 1) = -bI (i, 0) := by
    rw [← hbI₀, smul_smul, I_mul_I, neg_one_smul]
  let e := (bI.equiv bA (Equiv.refl _)).toContinuousLinearEquiv
  have he (x) : e (bI x) = bA x := bI.equiv_apply x bA (Equiv.refl _)
  refine ⟨e, coe_injective (bI.ext fun ⟨i, k⟩ => ?_)⟩
  -- Both sides send `bI (i, 0)` to `bA (i, 1)` and `bI (i, 1)` to `-bA (i, 0)`.
  fin_cases k <;> simp [he, hbI₀, hbI₁, hbA', hA']

/-- **Complex frames of a complex structure.** A real-linear `A` with `A² = -1` on a
finite-dimensional real normed space `E` is multiplication by `i` in a complex coordinate frame:
some real-linear isomorphism `Φ : ℂⁿ → E` satisfies `A Φ = Φ i`. -/
theorem exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (A : E →L[ℝ] E)
    (hA : A ∘L A = -ContinuousLinearMap.id ℝ E) :
    ∃ (n : ℕ) (Φ : EuclideanSpace ℂ (Fin n) ≃L[ℝ] E),
      A ∘L (Φ : EuclideanSpace ℂ (Fin n) →L[ℝ] E) =
        (Φ : EuclideanSpace ℂ (Fin n) →L[ℝ] E) ∘L
          (I • ContinuousLinearMap.id ℝ (EuclideanSpace ℂ (Fin n))) := by
  have hA' (v : E) : A (A v) = -v := congr($hA v)
  obtain ⟨n, b, -⟩ := (⟨A.toLinearMap, by ext v; exact hA' v⟩ : AlmostComplexStructure E)
    |>.exists_basis_apply_one_eq
  -- Any real-linear isomorphism `Ψ : ℂⁿ → E` carries `A` to a complex structure on `ℂⁿ`, which is
  -- conjugate to `i` there.
  have hdim : Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) = Module.finrank ℝ E := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin, Module.finrank_eq_card_basis b]
    simp [mul_comm]
  let Ψ := ContinuousLinearEquiv.ofFinrankEq hdim
  let B : EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) := Ψ.symm.arrowCongr Ψ.symm A
  obtain ⟨Φ₁, hΦ₁⟩ := B.exists_continuousLinearEquiv_comp_eq_comp_I_smul (by ext v; simp [B, hA'])
  refine ⟨n, Φ₁.trans Ψ, ContinuousLinearMap.ext fun v ↦ ?_⟩
  have h := congr(Ψ ($hΦ₁ v))
  simpa [B] using h

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- **Coordinates in a complex frame.** If a real-linear isomorphism `Φ : V → E` turns `A` into
multiplication by `i`, that is `A Φ = Φ i`, then `Φ⁻¹ A = i Φ⁻¹`. -/
theorem symm_apply_eq_I_smul_symm_of_comp_eq (Φ : V ≃L[ℝ] E) {A : E →L[ℝ] E}
    (hA : A ∘L (Φ : V →L[ℝ] E) = (Φ : V →L[ℝ] E) ∘L (I • ContinuousLinearMap.id ℝ V)) (w : E) :
    Φ.symm (A w) = I • Φ.symm w := by
  have h := congr($hA (Φ.symm w))
  simp only [ContinuousLinearMap.comp_apply, coe_coe, apply_symm_apply,
    _root_.smul_apply, ContinuousLinearMap.id_apply] at h
  rw [h, symm_apply_apply]

end ContinuousLinearEquiv

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Complements of a complex line -/

/-- **A normal frame in a complex frame.** Let `Ψ : ℂⁿ → V` be a real-linear isomorphism
turning a complex structure `A` into multiplication by `i`, and `D : ℂ → V` a nonzero
complex-linear map, `D i = A (D 1)`, so that `D α = Ψ (α w)` with `w = Ψ⁻¹ (D 1) ≠ 0`. Then
`Ψ`, restricted to the orthogonal complement of the line `ℂ w`, is a normal frame `W` which is
complex-linear for `i` and `A`, and `(α, v) ↦ D α + W v` is bijective. -/
private theorem complexLinear_and_bijective_coprod_orthogonal {n : ℕ} {A : V →L[ℝ] V}
    (Ψ : EuclideanSpace ℂ (Fin n) ≃L[ℝ] V) (hΨ : ∀ x, A (Ψ x) = Ψ (I • x)) {D : ℂ →L[ℝ] V}
    (hDI : D I = A (D 1)) (hD : D ≠ 0) {w : EuclideanSpace ℂ (Fin n)} (hD1 : D 1 = Ψ w) :
    (∀ v : (ℂ ∙ w)ᗮ, A (Ψ v) = Ψ ↑(I • v)) ∧ Function.Bijective
      (D.coprod ((Ψ : EuclideanSpace ℂ (Fin n) →L[ℝ] V).comp
        ((ℂ ∙ w)ᗮ.subtypeL.restrictScalars ℝ))) := by
  have hDα (α : ℂ) : D α = Ψ (α • w) := by
    rw [show α = α.re • (1 : ℂ) + α.im • I by simp]
    simp only [map_add, map_smul, hDI, hD1, hΨ, add_smul, smul_assoc, one_smul]
  have hw0 : w ≠ 0 := fun h ↦ hD (ContinuousLinearMap.ext fun α ↦ by simp [hDα, h])
  have hcoprod (p : ℂ × (ℂ ∙ w)ᗮ) : D.coprod ((Ψ : EuclideanSpace ℂ (Fin n) →L[ℝ] V).comp
      ((ℂ ∙ w)ᗮ.subtypeL.restrictScalars ℝ)) p = Ψ (p.1 • w + p.2) := by
    rw [ContinuousLinearMap.coprod_apply, hDα, map_add]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      Submodule.subtypeL_apply, ContinuousLinearEquiv.coe_coe]
  refine ⟨fun v ↦ (hΨ v).trans (congrArg Ψ (Submodule.coe_smul I v).symm), ?_⟩
  -- `(α, v) ↦ α w + v` is the decomposition along the line `ℂ w` and its orthogonal complement.
  let E := ((LinearEquiv.toSpanNonzeroSingleton ℂ _ w hw0).prodCongr
    (LinearEquiv.refl ℂ (ℂ ∙ w)ᗮ)).trans (Submodule.prodEquivOfIsCompl _ _
      (ℂ ∙ w).isCompl_orthogonal)
  convert Ψ.bijective.comp E.bijective using 1
  funext p
  rw [Function.comp_apply, hcoprod]
  simp [E, LinearEquiv.toSpanNonzeroSingleton_apply]

/-- **Normal frames exist.** Let `A` be a complex structure on a finite-dimensional real normed
space `V`, `A² = -1`, and `D : ℂ →L[ℝ] V` a nonzero map satisfying the Cauchy–Riemann equation
`D 1 + A (D i) = 0`, that is complex-linear for `i` and `A`. Then there is a frame
`W : ℂⁿ →L[ℝ] V`, complex-linear for `i` and `A`, whose image is a complement of the image of
`D`: `(α, w) ↦ D α + W w` is bijective. For `A = J(u a₀)` and `D = du(a₀)` of a `J`-holomorphic
disc `u` immersed at `a₀`, this is the frame required by `TauCeti.exists_holomorphicAdaptedChart`
and `TauCeti.exists_holomorphicAdaptedChart_norm_pullbackEnd_sub_le`. -/
theorem exists_complexLinear_and_bijective_coprod [FiniteDimensional ℝ V] {A : V →L[ℝ] V}
    (hA : ∀ v, A (A v) = -v) {D : ℂ →L[ℝ] V} (hCR : D 1 + A (D I) = 0) (hD : D ≠ 0) :
    ∃ (n : ℕ) (W : EuclideanSpace ℂ (Fin n) →L[ℝ] V),
      (∀ w, A (W w) = W (I • w)) ∧ Function.Bijective (D.coprod W) := by
  -- A complex frame `Ψ : ℂᵐ → V` of the structure `A`.
  obtain ⟨m, Ψ, hΨ⟩ :=
    ContinuousLinearMap.exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul A
      (ContinuousLinearMap.ext fun v ↦ by simpa using hA v)
  have hΨI (x : EuclideanSpace ℂ (Fin m)) : A (Ψ x) = Ψ (I • x) := by simpa using congr($hΨ x)
  have hDI : D I = A (D 1) := by
    have h := congrArg A hCR
    rw [map_add, hA, map_zero] at h
    exact (add_neg_eq_zero.1 h).symm
  obtain ⟨hW, hbij⟩ := complexLinear_and_bijective_coprod_orthogonal Ψ hΨI hDI hD
    (Ψ.apply_symm_apply (D 1)).symm
  -- Identify the orthogonal complement of the tangent line with a coordinate space.
  set K := (ℂ ∙ Ψ.symm (D 1))ᗮ
  let b := stdOrthonormalBasis ℂ K
  refine ⟨Module.finrank ℂ K, (Ψ : EuclideanSpace ℂ (Fin m) →L[ℝ] V).comp
    ((K.subtypeL.restrictScalars ℝ).comp
      ((b.repr.symm.toContinuousLinearEquiv : _ →L[ℂ] K).restrictScalars ℝ)),
    fun x ↦ ?_, ?_⟩
  · simpa using hW (b.repr.symm x)
  · convert hbij.comp (Function.bijective_id.prodMap b.repr.symm.bijective) using 1
    funext p
    simp

end TauCeti

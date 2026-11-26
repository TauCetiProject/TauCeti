/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.LinearAlgebra.TotallyReal.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Geometry.Symplectic.Complex.Module.Basic
import TauCeti.LinearAlgebra.Complex.Module
import TauCeti.LinearAlgebra.TotallyReal.Frame

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
* `TauCeti.exists_euclideanSpace_bijective_coprod`: complex frames of a complement of a complex
  line `D (ℂ)`, for `D : ℂ → E` real-linear with `D 1 + A (D i) = 0`.
* `TauCeti.IsMaximalTotallyReal.exists_continuousLinearEquiv_pi_comp_eq_comp_I_smul_and_mem_iff`:
  for a maximal totally real subspace `L` of `A`, a frame `Φ : ℂⁿ → E` with `A Φ = Φ i` carrying
  the real vectors `ℝⁿ` onto `L`.

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

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Complex normal frames.** Let `A` be a complex structure on a finite-dimensional real normed
space `V`, `A² = -1`, and `D : ℂ → V` a nonzero real-linear map satisfying the Cauchy–Riemann
equation `D 1 + A (D i) = 0`. Then some real-linear `W : ℂⁿ → V` intertwines `i` with `A` and
spans a complement of the line `D (ℂ)`: the map `(α, w) ↦ D α + W w` is bijective. This is the
frame consumed by `TauCeti.exists_holomorphicAdaptedChart`, for `D` the derivative of a
pseudoholomorphic disc at an immersed point. -/
theorem exists_euclideanSpace_bijective_coprod {A : V →L[ℝ] V}
    (hA : A ∘L A = -ContinuousLinearMap.id ℝ V) {D : ℂ →L[ℝ] V} (hD : D 1 + A (D I) = 0)
    (hD0 : D ≠ 0) :
    ∃ (n : ℕ) (W : EuclideanSpace ℂ (Fin n) →L[ℝ] V),
      (∀ w, A (W w) = W (I • w)) ∧ Function.Bijective (D.coprod W) := by
  obtain ⟨m, Ψ, hΨ⟩ := A.exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul hA
  have hΨI (x : EuclideanSpace ℂ (Fin m)) : A (Ψ x) = Ψ (I • x) := by simpa using congr($hΨ x)
  have hA' (v : V) : A (A v) = -v := by simpa using congr($hA v)
  -- in the frame `Ψ`, the map `D` is `α ↦ α v`
  set v := Ψ.symm (D 1) with hv
  have hDI : D I = A (D 1) := by
    rw [eq_neg_of_add_eq_zero_left hD, map_neg, hA', neg_neg]
  have hDα (α : ℂ) : D α = Ψ (α • v) := by
    rw [← re_smul_add_im_smul, map_add, map_smul, map_smul, ← hΨI, hv,
      ContinuousLinearEquiv.apply_symm_apply, ← hDI]
    exact LinearMap.apply_eq_re_smul_one_add_im_smul_I (D : ℂ →ₗ[ℝ] V) α
  have hv0 : v ≠ 0 := fun h ↦ hD0 (ContinuousLinearMap.ext fun α ↦ by simp [hDα, h])
  -- the frame is an orthonormal frame of the orthogonal complement of the line `ℂ v`, and
  -- `(α, w) ↦ α v + w` is the decomposition of `ℂᵐ` as that line plus its complement
  set P := ℂ ∙ v
  let b := stdOrthonormalBasis ℂ Pᗮ
  let φ : (ℂ × EuclideanSpace ℂ (Fin (Module.finrank ℂ Pᗮ))) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    (LinearEquiv.prodCongr (LinearEquiv.toSpanNonzeroSingleton ℂ _ v hv0)
      b.repr.symm.toLinearEquiv).trans (P.prodEquivOfIsCompl Pᗮ P.isCompl_orthogonal)
  refine ⟨Module.finrank ℂ Pᗮ, (Ψ : EuclideanSpace ℂ (Fin m) →L[ℝ] V) ∘L
    (Pᗮ.subtypeL ∘L (b.repr.symm : _ →L[ℂ] Pᗮ)).restrictScalars ℝ, fun w ↦ by simp [hΨI], ?_⟩
  have hcoprod : ⇑(D.coprod ((Ψ : EuclideanSpace ℂ (Fin m) →L[ℝ] V) ∘L
      (Pᗮ.subtypeL ∘L (b.repr.symm : _ →L[ℂ] Pᗮ)).restrictScalars ℝ)) = Ψ ∘ ⇑φ := by
    ext p
    simp [φ, hDα, Submodule.coe_prodEquivOfIsCompl']
  rw [hcoprod]
  exact Ψ.bijective.comp φ.bijective

namespace IsMaximalTotallyReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {A : E →L[ℝ] E} {L : Submodule ℝ E}

/-- **Complex frames adapted to a totally real subspace.** Let `A` be a complex structure on a
finite-dimensional real normed space `E`, `A² = -1`, and `L` a maximal totally real subspace for
`A`, so that `E = L ⊕ A L`. Some real-linear isomorphism `Φ : ℂⁿ → E` turns `A` into
multiplication by `i`, `A Φ = Φ i`, and carries the real vectors of `ℂⁿ`, those fixed by the
coordinatewise conjugation `star`, exactly onto `L`. It sends the complex basis `(eᵢ, i eᵢ)` of
`ℂⁿ` to the doubled basis `(bᵢ, A bᵢ)` of a basis `b` of `L`
(`TauCeti.IsMaximalTotallyReal.doubledBasis`), so `v` goes to `x + A y`, where `x` and `y` are the
vectors of `L` with coordinates the real and imaginary parts of `v` in `b`. -/
theorem exists_continuousLinearEquiv_pi_comp_eq_comp_I_smul_and_mem_iff
    (hL : IsMaximalTotallyReal (A : E →ₗ[ℝ] E) L) (hA : A ∘L A = -ContinuousLinearMap.id ℝ E) :
    ∃ (n : ℕ) (Φ : (Fin n → ℂ) ≃L[ℝ] E),
      A ∘L (Φ : (Fin n → ℂ) →L[ℝ] E) =
          (Φ : (Fin n → ℂ) →L[ℝ] E) ∘L (I • ContinuousLinearMap.id ℝ (Fin n → ℂ)) ∧
        ∀ v, Φ v ∈ L ↔ star v = v := by
  have hA' (v : E) : A (A v) = -v := congr($hA v)
  have hAinj : Function.Injective A := fun x y h ↦ by simpa [hA'] using congr(A $h)
  let b := Module.finBasis ℝ L
  -- the frame sending the complex basis `(eᵢ, i eᵢ)` of `ℂⁿ` to the doubled basis `(bᵢ, A bᵢ)`
  let c := (Pi.basis fun _ : Fin (Module.finrank ℝ L) ↦ Complex.basisOneI).reindex
    (Equiv.sigmaEquivProd _ _)
  let d := hL.doubledBasis (hAinj.comp L.injective_subtype) b
  let Φ := c.equiv d (Equiv.refl _)
  have hΦ (i : Fin (Module.finrank ℝ L)) (k : Fin 2) :
      Φ (Pi.single i (Complex.basisOneI k)) = d (i, k) := by
    simpa [c] using c.equiv_apply (i, k) d (Equiv.refl _)
  have hΦ0 (i : Fin (Module.finrank ℝ L)) : Φ (Pi.single i 1) = b i := by
    simpa using (hΦ i 0).trans (doubledBasis_apply_zero ..)
  have hΦ1 (i : Fin (Module.finrank ℝ L)) : Φ (Pi.single i I) = A (b i) := by
    simpa using (hΦ i 1).trans (doubledBasis_apply_one ..)
  have hΦI (w : Fin (Module.finrank ℝ L) → ℂ) : Φ (I • w) = A (Φ w) := by
    refine LinearMap.congr_fun (c.ext (f₁ := Φ.toLinearMap ∘ₗ (I • LinearMap.id))
      (f₂ := (A : E →ₗ[ℝ] E) ∘ₗ Φ.toLinearMap) fun ⟨i, k⟩ ↦ ?_) w
    fin_cases k <;> simp [c, hΦ0, hΦ1, hA', ← Pi.single_smul, Pi.single_neg]
  -- `Φ` carries the real vector with coordinates `x` to the vector of `L` with coordinates `x`
  have hre (x : Fin (Module.finrank ℝ L) → ℝ) :
      Φ (fun i ↦ (x i : ℂ)) = b.equivFun.symm x := by
    have : (fun i ↦ (x i : ℂ)) = ∑ i, x i • Pi.single i 1 := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    simp [this, hΦ0, Module.Basis.equivFun_symm_apply]
  refine ⟨Module.finrank ℝ L, Φ.toContinuousLinearEquiv,
    ContinuousLinearMap.ext fun w ↦ by simpa using (hΦI w).symm, fun v ↦ ?_⟩
  -- `Φ v = x + A y` for the vectors `x`, `y` of `L` with coordinates the real and imaginary
  -- parts of `v`; `x + A y ∈ L` forces `A y ∈ L ∩ A L = 0`, that is `y = 0`
  have hΦv : Φ v =
      b.equivFun.symm (fun i ↦ (v i).re) + A (b.equivFun.symm fun i ↦ (v i).im) := by
    rw [← hre, ← hre, ← hΦI, ← map_add]
    congr 1
    funext i
    simp [mul_comm I]
  have hstar : star v = v ↔ b.equivFun.symm (fun i ↦ (v i).im) = 0 := by
    rw [LinearEquiv.map_eq_zero_iff, funext_iff, funext_iff]
    simp [Complex.conj_eq_iff_im]
  simp only [LinearEquiv.coe_toContinuousLinearEquiv', hΦv, hstar]
  rw [Submodule.add_mem_iff_right _ (Submodule.coe_mem _)]
  refine ⟨fun hmem ↦ ?_, fun h ↦ by simp [h]⟩
  have h0 := Submodule.disjoint_def.1 hL.disjoint _ hmem
    (Submodule.mem_map_of_mem (b.equivFun.symm fun i ↦ (v i).im).property)
  exact Subtype.ext (hAinj (by simpa using h0))

end IsMaximalTotallyReal

end TauCeti

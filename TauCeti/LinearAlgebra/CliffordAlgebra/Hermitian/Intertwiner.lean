/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.LinearAlgebra.CliffordAlgebra.BaseChange
import Mathlib.Algebra.Central.End
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import TauCeti.Analysis.InnerProductSpace.LinearIsometry.Rescale
import TauCeti.Analysis.Normed.Module.QuadraticMap
import TauCeti.LinearAlgebra.CliffordAlgebra.CentralSimple.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Complex

/-!
# Unitary Clifford intertwiners in even dimension

Combining fullness of complexified spinor actions
(`CliffordAlgebra.liftBaseChange_bijective_of_finrank_eq`), Skolem–Noether
(`AlgEquiv.eq_linearEquivConjAlgEquiv`), and uniqueness of the compatible Hermitian inner product
(`CliffordAlgebra.existsUnique_pos_mul_inner_of_surjective`) classifies unitary Clifford
intertwiners along linear isometries `f : V ≃ₗᵢ[ℝ] V'` as a `Circle`-torsor: existence
(`CliffordAlgebra.exists_unitary_intertwiner_of_finrank_eq`) and uniqueness up to a phase in
`Circle` (`CliffordAlgebra.existsUnique_circle_smul_intertwiner`).

## Main results

* `CliffordAlgebra.existsUnique_circle_smul_intertwiner`: any two unitary Clifford intertwiners of
  a surjective complexified action differ by a unique phase in `Circle`.
* `CliffordAlgebra.exists_unitary_intertwiner_of_finrank_eq`: existence of a unitary Clifford
  intertwiner along any linear isometry `f : V ≃ₗᵢ[ℝ] V'` in even dimension.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

noncomputable section

namespace CliffordAlgebra

open Module Module.End
open scoped InnerProductSpace TensorProduct ComplexOrder

section Intertwiners

variable {V V' W W' : Type*} [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}
  [AddCommGroup V'] [Module ℝ V'] {Q' : QuadraticForm ℝ V'}

/-- **Uniqueness of unitary Clifford intertwiners up to `Circle`.** If `liftBaseChange ℂ Q ρ` is
surjective onto `Module.End ℂ W` on a nontrivial complex inner product space `W`, any two unitary
intertwiners `U₁, U₂ : W ≃ₗᵢ[ℂ] W'` along a map `f : V → V'` differ by a unique phase in `Circle`.
-/
theorem existsUnique_circle_smul_intertwiner [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [Nontrivial W] [NormedAddCommGroup W'] [InnerProductSpace ℂ W']
    {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
    {ρ' : CliffordAlgebra Q' →ₐ[ℝ] Module.End ℂ W'}
    (hsurj : Function.Surjective (liftBaseChange ℂ Q ρ)) {f : V → V'}
    (U₁ U₂ : W ≃ₗᵢ[ℂ] W')
    (hU₁ : ∀ v, U₁.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
      ρ' (ι Q' (f v)) ∘ₗ U₁.toLinearEquiv.toLinearMap)
    (hU₂ : ∀ v, U₂.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
      ρ' (ι Q' (f v)) ∘ₗ U₂.toLinearEquiv.toLinearMap) :
    ∃! z : Circle, ∀ w, U₂ w = (z : ℂ) • U₁ w := by
  let L : W ≃ₗᵢ[ℂ] W := U₂.trans U₁.symm
  have hU₁L (w : W) : U₁ (L w) = U₂ w := U₁.apply_symm_apply (U₂ w)
  have hcomm_ι (v : V) : Commute L.toLinearEquiv.toLinearMap (ρ (ι Q v)) := by
    rw [Commute, SemiconjBy, mul_eq_comp, mul_eq_comp]
    ext w
    apply U₁.injective
    have hw₂ : U₂ (ρ (ι Q v) w) = ρ' (ι Q' (f v)) (U₂ w) := LinearMap.congr_fun (hU₂ v) w
    have hw₁ : U₁ (ρ (ι Q v) (L w)) = ρ' (ι Q' (f v)) (U₁ (L w)) :=
      LinearMap.congr_fun (hU₁ v) (L w)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
    rw [hU₁L, hw₂, hw₁, hU₁L]
  have hcenter : L.toLinearEquiv.toLinearMap ∈ Subalgebra.center ℂ (Module.End ℂ W) :=
    Subalgebra.mem_center_iff.mpr fun B ↦ by
      obtain ⟨a, rfl⟩ := hsurj B
      exact (commute_liftBaseChange_of_forall_ι hcomm_ι a).symm
  obtain ⟨c, hc⟩ := (Algebra.IsCentral.mem_center_iff ℂ).mp hcenter
  have hLw (w : W) : L w = c • w := by
    simpa [Algebra.algebraMap_eq_smul_one] using LinearMap.congr_fun hc w
  let := NormedSpace.restrictScalars ℝ ℂ W
  obtain ⟨u, hu⟩ := exists_norm_eq W zero_le_one
  have hc_norm : ‖c‖ = 1 := by simpa [hLw, norm_smul, hu] using L.norm_map u
  refine ⟨⟨c, mem_sphere_zero_iff_norm.mpr hc_norm⟩,
    fun w ↦ by rw [← hU₁L, hLw, map_smul], fun z hz ↦ Subtype.ext ?_⟩
  have hzu : ((z : ℂ) - c) • U₁ u = 0 := by
    rw [sub_smul, ← hz u, ← map_smul, ← hLw u, hU₁L, sub_self]
  have hu₁ : U₁ u ≠ 0 := fun h0 ↦ by simpa [h0, hu] using U₁.norm_map u
  exact sub_eq_zero.mp ((smul_eq_zero.mp hzu).resolve_right hu₁)

/-- **Existence of unitary Clifford intertwiners.** Let `V` and `V'` be real inner product spaces
of even dimension `2 * m` with negative norm-square forms `Q` and `Q'`, and let `f : V ≃ₗᵢ[ℝ] V'`
be a linear isometry. Any two Hermitian Clifford modules `(W, ρ)` and `(W', ρ')` of complex
dimension `2 ^ m` are intertwined along `f` by a complex linear isometry equivalence
`U : W ≃ₗᵢ[ℂ] W'`. -/
theorem exists_unitary_intertwiner_of_finrank_eq
    {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℝ V']
    {Q : QuadraticForm ℝ V} {Q' : QuadraticForm ℝ V'}
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hQ' : ∀ v, Q' v = -‖v‖ ^ 2)
    (f : V ≃ₗᵢ[ℝ] V') {m : ℕ} (hV : finrank ℝ V = 2 * m)
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [FiniteDimensional ℂ W']
    {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
    {ρ' : CliffordAlgebra Q' →ₐ[ℝ] Module.End ℂ W'}
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (hρ' : ∀ v, LinearMap.adjoint (ρ' (ι Q' v)) = -ρ' (ι Q' v))
    (hW : finrank ℂ W = 2 ^ m) (hW' : finrank ℂ W' = 2 ^ m) :
    ∃ U : W ≃ₗᵢ[ℂ] W', ∀ v,
      U.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
        ρ' (ι Q' (f v)) ∘ₗ U.toLinearEquiv.toLinearMap := by
  have : FiniteDimensional ℝ V' := f.toLinearEquiv.finiteDimensional
  have hQnd : Q.Nondegenerate := QuadraticForm.nondegenerate_of_eq_neg_norm_sq hQ
  have hQ'nd : Q'.Nondegenerate := QuadraticForm.nondegenerate_of_eq_neg_norm_sq hQ'
  let eQ : Q.IsometryEquiv Q' :=
    { f.toLinearEquiv with map_app' v := by simp [hQ', hQ] }
  let eCl : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] CliffordAlgebra (Q'.baseChange ℂ) :=
    AlgEquiv.ofAlgHom (CliffordAlgebra.map (eQ.toIsometry.baseChange ℂ))
      (CliffordAlgebra.map (eQ.symm.toIsometry.baseChange ℂ))
      (CliffordAlgebra.hom_ext <| by ext v; simp [eQ])
      (CliffordAlgebra.hom_ext <| by ext v; simp [eQ])
  let α := AlgEquiv.ofBijective (liftBaseChange ℂ Q ρ)
    (liftBaseChange_bijective_of_finrank_eq ρ hQnd hV hW)
  let α' := AlgEquiv.ofBijective (liftBaseChange ℂ Q' ρ')
    (liftBaseChange_bijective_of_finrank_eq ρ' hQ'nd
      (f.toLinearEquiv.finrank_eq.symm.trans hV) hW')
  obtain ⟨T, hT⟩ := (α.symm.trans (eCl.trans α')).eq_linearEquivConjAlgEquiv
  have hT_ι (v : V) (w : W) : T (ρ (ι Q v) w) = ρ' (ι Q' (f v)) (T w) := by
    have h := congr($hT (α (ι (Q.baseChange ℂ) (1 ⊗ₜ v))) (T w))
    simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, LinearEquiv.conjAlgEquiv_apply,
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h
    simpa [α, α', eCl, ← QuadraticMap.IsometryEquiv.coe_toLinearEquiv, eQ] using h.symm
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (by rw [hW]; positivity)
  let H : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ := ((innerₛₗ ℂ).comp T.toLinearMap).compl₂ T.toLinearMap
  have hH_apply (a b : W) : H a b = ⟪T a, T b⟫_ℂ := by simp [H]
  obtain ⟨r, ⟨hr, hrH⟩, _⟩ := existsUnique_pos_mul_inner_of_surjective (liftBaseChange ℂ Q ρ)
    α.surjective (fun v ↦ by simpa using hρ v) H
    ⟨fun x ↦ by rw [hH_apply, inner_self_eq_norm_sq_to_K]; positivity⟩
    (fun x hx h0 ↦
      hx <| T.injective ((inner_self_eq_zero.mp (hH_apply x x ▸ h0)).trans T.map_zero.symm))
    (fun v x y ↦ by
      rw [hH_apply, hH_apply, liftBaseChange_ι_tmul, one_smul, hT_ι,
        ← LinearMap.adjoint_inner_right, hρ', LinearMap.neg_apply, inner_neg_right, ← hT_ι])
  simp only [hH_apply] at hrH
  refine ⟨T.rescaleLinearIsometryEquiv hr hrH, fun v ↦ ?_⟩
  ext w
  simp [hT_ι]

end Intertwiners

end CliffordAlgebra

end

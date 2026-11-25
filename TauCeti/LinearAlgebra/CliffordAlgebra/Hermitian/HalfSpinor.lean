/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.HalfSpinor
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Intertwiner
import Mathlib.Analysis.InnerProductSpace.Spectrum
import TauCeti.Analysis.Normed.Module.QuadraticMap
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
import TauCeti.LinearAlgebra.Eigenspace.Transport

/-!
# Hermitian half-spinors and unitary chirality restrictions in dimension four

In dimension four with `Q v = -‖v‖²`, skew-adjoint generators make the chirality eigenspaces
mutually orthogonal (`CliffordAlgebra.inner_eq_zero_of_mem_eigenspace_chirality`), half-spin rank
two forces fullness of the complexified Clifford action
(`CliffordAlgebra.liftBaseChange_bijective_of_finrank_positiveHalfSpinors_eq_two`), and every
unitary intertwiner along an orientation-preserving isometry restricts to unitary chirality
equivalences (`CliffordAlgebra.halfSpinLinearIsometryEquiv`) whose operator conjugation is
independent of the `Circle` phase (`CliffordAlgebra.conj_halfSpinLinearIsometryEquiv_eq`).

## Main definitions

* `CliffordAlgebra.halfSpinLinearIsometryEquiv`: unitary restriction to `ε`-eigenspaces of `Γ`.

## Main results

* `CliffordAlgebra.liftBaseChange_bijective_of_finrank_positiveHalfSpinors_eq_two`: fullness of
  `liftBaseChange ℂ Q ρ` when `dim_ℂ W⁺ = 2`.
* `CliffordAlgebra.inner_eq_zero_of_mem_eigenspace_chirality`: distinct eigenspaces of `Γ` are
  orthogonal.
* `CliffordAlgebra.coe_adjoint_halfSpinCliffordMul_apply`,
  `CliffordAlgebra.norm_halfSpinCliffordMul_apply`,
  `CliffordAlgebra.adjoint_halfSpinCliffordMul_comp_self`,
  `CliffordAlgebra.adjoint_evenHalfSpinAction`: adjoint and norm laws for chiral Clifford
  multiplication and the even half-spin action.
* `CliffordAlgebra.conj_halfSpinLinearIsometryEquiv_eq`: operator conjugation by
  `halfSpinLinearIsometryEquiv` is independent of the choice of unitary intertwiner.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

noncomputable section

namespace CliffordAlgebra

open Module Module.End
open scoped InnerProductSpace

section DimensionFour

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin 4))

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 3

/-- **Half-spin rank two forces fullness of the complexified Clifford action** in dimension four. -/
theorem liftBaseChange_bijective_of_finrank_positiveHalfSpinors_eq_two
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) :
    Function.Bijective (liftBaseChange ℂ Q ρ) := by
  refine liftBaseChange_bijective_of_finrank_eq ρ
    (QuadraticForm.nondegenerate_of_eq_neg_norm_sq hQ) (m := 2)
    (Fact.out : finrank ℝ V = 4) ?_
  rw [finrank_eq_two_mul_finrank_positiveHalfSpinors o ρ hQ, h₂]
  norm_num

section HermitianModule

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}

/-- Distinct eigenspaces of `Γ` on a Hermitian Clifford module are mutually orthogonal; in
particular `W⁺` and `W⁻` are orthogonal. -/
theorem inner_eq_zero_of_mem_eigenspace_chirality
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {ε₁ ε₂ : ℂ} (hε : ε₁ ≠ ε₂)
    {ψ₁ ψ₂ : W} (hψ₁ : ψ₁ ∈ eigenspace (ρ (chirality Q o)) ε₁)
    (hψ₂ : ψ₂ ∈ eigenspace (ρ (chirality Q o)) ε₂) :
    ⟪ψ₁, ψ₂⟫_ℂ = 0 := by
  have hsymm : (ρ (chirality Q o)).IsSymmetric :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr (isSelfAdjoint_map_chirality o hρ)
  exact hsymm.orthogonalFamily_eigenspaces hε ⟨ψ₁, hψ₁⟩ ⟨ψ₂, hψ₂⟩

/-- **Adjoint of chiral Clifford multiplication**: for skew-adjoint generators, the adjoint of
`halfSpinCliffordMul o ρ ε v : W^ε → W^{-ε}` acts in the ambient module as `-c(v)`. -/
@[simp]
theorem coe_adjoint_halfSpinCliffordMul_apply
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (ε : ℂ) (v : V)
    (χ : eigenspace (ρ (chirality Q o)) (-ε)) :
    (LinearMap.adjoint (halfSpinCliffordMul o ρ ε v) χ : W) = -ρ (ι Q v) χ := by
  let A : eigenspace (ρ (chirality Q o)) (-ε) →ₗ[ℂ] eigenspace (ρ (chirality Q o)) ε :=
    { toFun η := ⟨-ρ (ι Q v) η, Submodule.neg_mem _
        (by simpa only [neg_neg] using map_ι_apply_mem_eigenspace_chirality_neg o η.property v)⟩
      map_add' _ _ := Subtype.ext (by simp only [map_add, neg_add, Submodule.coe_add])
      map_smul' _ _ := Subtype.ext (by simp only [map_smul, smul_neg, SetLike.val_smul,
        RingHom.id_apply]) }
  have hA_coe (η : eigenspace (ρ (chirality Q o)) (-ε)) : (A η : W) = -ρ (ι Q v) η := rfl
  have hA : A = LinearMap.adjoint (halfSpinCliffordMul o ρ ε v) :=
    (LinearMap.eq_adjoint_iff A _).mpr fun η ψ ↦ by
      rw [Submodule.coe_inner, Submodule.coe_inner, hA_coe, coe_halfSpinCliffordMul_apply_apply,
        inner_neg_left, ← LinearMap.adjoint_inner_right, hρ, LinearMap.neg_apply,
        inner_neg_right, neg_neg]
  rw [← hA, hA_coe]

/-- **Norm law for chiral Clifford multiplication**: for `Q v = -‖v‖²` and skew-adjoint generators,
`halfSpinCliffordMul` scales spinor norms by `‖v‖`. -/
theorem norm_halfSpinCliffordMul_apply (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (ε : ℂ) (v : V)
    (ψ : eigenspace (ρ (chirality Q o)) ε) :
    ‖halfSpinCliffordMul o ρ ε v ψ‖ = ‖v‖ * ‖ψ‖ := by
  rw [← Submodule.norm_coe, ← Submodule.norm_coe (x := ψ), coe_halfSpinCliffordMul_apply_apply]
  exact norm_map_ι_apply hQ hρ v ψ

/-- Composing chiral Clifford multiplication with its adjoint multiplies by `‖v‖²`. -/
@[simp]
theorem adjoint_halfSpinCliffordMul_comp_self (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (ε : ℂ) (v : V) :
    LinearMap.adjoint (halfSpinCliffordMul o ρ ε v) ∘ₗ halfSpinCliffordMul o ρ ε v =
      ((‖v‖ : ℂ) ^ 2) • LinearMap.id := by
  ext ψ
  simp [coe_adjoint_halfSpinCliffordMul_apply o hρ, hQ, ← Complex.ofReal_pow, Complex.coe_smul]

/-- **Adjoint of the even half-spin action**: for skew-adjoint generators, the adjoint of
`evenHalfSpinAction o ρ ε x` on any chirality eigenspace is `evenHalfSpinAction o ρ ε` evaluated at
`reverseEven Q x`. -/
@[simp]
theorem adjoint_evenHalfSpinAction (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (ε : ℂ) (x : even Q) :
    LinearMap.adjoint (evenHalfSpinAction o ρ ε x) =
      evenHalfSpinAction o ρ ε (reverseEven Q x) := by
  symm
  refine (LinearMap.eq_adjoint_iff _ _).mpr fun η ψ ↦ ?_
  rw [Submodule.coe_inner, Submodule.coe_inner, coe_evenHalfSpinAction_apply,
    coe_evenHalfSpinAction_apply, coe_reverseEven_apply, reverse_eq_star_of_mem_even,
    ← adjoint_map_eq_map_star hρ, LinearMap.adjoint_inner_left]

end HermitianModule

/-! ### Unitary half-spin restrictions and `Circle`-independence of operator transport -/

section HalfSpinIntertwiner

variable {V' W W' : Type*} [NormedAddCommGroup V'] [InnerProductSpace ℝ V']
  [Fact (finrank ℝ V' = 4)] {Q' : QuadraticForm ℝ V'}
  {o} (o' : Orientation ℝ V' (Fin 4))
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [NormedAddCommGroup W'] [InnerProductSpace ℂ W']
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {ρ' : CliffordAlgebra Q' →ₐ[ℝ] Module.End ℂ W'}
  {f : V ≃ₗᵢ[ℝ] V'} (ho : o.map (Fin 4) f.toLinearEquiv = o')

/-- **Unitary restriction of a Clifford intertwiner to a chirality eigenspace**: a unitary
equivalence `U : W ≃ₗᵢ[ℂ] W'` intertwining the real generators along an orientation-preserving
linear isometry `f : V ≃ₗᵢ[ℝ] V'` restricts to a unitary equivalence on the `ε`-eigenspaces of `Γ`
for every `ε : ℂ`. -/
def halfSpinLinearIsometryEquiv {U : W ≃ₗᵢ[ℂ] W'}
    (hU : ∀ v, U.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
      ρ' (ι Q' (f v)) ∘ₗ U.toLinearEquiv.toLinearMap) (ε : ℂ) :
    eigenspace (ρ (chirality Q o)) ε ≃ₗᵢ[ℂ] eigenspace (ρ' (chirality Q' o')) ε where
  toLinearEquiv := U.toLinearEquiv.ofSubmodules _ _ <| by
    have hΓ := comp_chirality_eq_chirality_comp ho hU
    rw [TauCeti.eigenspace_eq_comap_of_intertwine (e := U.toLinearEquiv)
      (LinearMap.congr_fun hΓ) ε]
    exact Submodule.map_comap_eq_of_surjective U.surjective _
  norm_map' ψ := U.norm_map ψ

/-- Coercion to the ambient spinor space commutes with `halfSpinLinearIsometryEquiv`. -/
@[simp]
theorem coe_halfSpinLinearIsometryEquiv_apply {U : W ≃ₗᵢ[ℂ] W'}
    (hU : ∀ v, U.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
      ρ' (ι Q' (f v)) ∘ₗ U.toLinearEquiv.toLinearMap) (ε : ℂ)
    (ψ : eigenspace (ρ (chirality Q o)) ε) :
    (halfSpinLinearIsometryEquiv o' ho hU ε ψ : W') = U ψ :=
  (rfl)

/-- Coercion to the ambient spinor space commutes with `(halfSpinLinearIsometryEquiv ...).symm`. -/
@[simp]
theorem coe_halfSpinLinearIsometryEquiv_symm_apply {U : W ≃ₗᵢ[ℂ] W'}
    (hU : ∀ v, U.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
      ρ' (ι Q' (f v)) ∘ₗ U.toLinearEquiv.toLinearMap) (ε : ℂ)
    (ψ : eigenspace (ρ' (chirality Q' o')) ε) :
    ((halfSpinLinearIsometryEquiv o' ho hU ε).symm ψ : W) = U.symm ψ :=
  (rfl)

/-- The unitary half-spin restriction intertwines odd Clifford multiplication `halfSpinCliffordMul`
along the vector isometry `f`. -/
theorem halfSpinLinearIsometryEquiv_comp_halfSpinCliffordMul {U : W ≃ₗᵢ[ℂ] W'}
    (hU : ∀ v, U.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
      ρ' (ι Q' (f v)) ∘ₗ U.toLinearEquiv.toLinearMap) (ε : ℂ) (v : V) :
    (halfSpinLinearIsometryEquiv o' ho hU (-ε)).toLinearEquiv.toLinearMap ∘ₗ
        halfSpinCliffordMul o ρ ε v =
      halfSpinCliffordMul o' ρ' ε (f v) ∘ₗ
        (halfSpinLinearIsometryEquiv o' ho hU ε).toLinearEquiv.toLinearMap := by
  ext ψ
  simpa using LinearMap.congr_fun (hU v) ψ

/-- The unitary half-spin restriction intertwines `evenHalfSpinAction` along the even Clifford
homomorphism of any quadratic isometry `e : Q →qᵢ Q'` agreeing with `f`. -/
theorem halfSpinLinearIsometryEquiv_comp_evenHalfSpinAction {U : W ≃ₗᵢ[ℂ] W'}
    (hU : ∀ v, U.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
      ρ' (ι Q' (f v)) ∘ₗ U.toLinearEquiv.toLinearMap)
    (e : Q →qᵢ Q') (he : ∀ v, e v = f v) (ε : ℂ) (x : even Q) :
    (halfSpinLinearIsometryEquiv o' ho hU ε).toLinearEquiv.toLinearMap ∘ₗ
        evenHalfSpinAction o ρ ε x =
      evenHalfSpinAction o' ρ' ε ⟨CliffordAlgebra.map e x, map_mem_even e x.property⟩ ∘ₗ
        (halfSpinLinearIsometryEquiv o' ho hU ε).toLinearEquiv.toLinearMap := by
  have hx := comp_eq_map_comp_of_forall_ι (f := e)
    (fun v ↦ by simpa [he v] using hU v) (x : CliffordAlgebra Q)
  ext ψ
  simpa using LinearMap.congr_fun hx ψ

/-- **Canonical transport of operators between chirality eigenspaces**: when `liftBaseChange ℂ Q ρ`
is surjective on a nontrivial module `W` (in particular whenever `dim_ℂ W⁺ = 2`), conjugating any
linear map `T : W^{ε₁} →ₗ[ℂ] W^{ε₂}` by `halfSpinLinearIsometryEquiv` is independent of the choice
of unitary Clifford intertwiner `U` along `(f, ho)`. -/
theorem conj_halfSpinLinearIsometryEquiv_eq [Nontrivial W]
    (hsurj : Function.Surjective (liftBaseChange ℂ Q ρ))
    {U₁ U₂ : W ≃ₗᵢ[ℂ] W'}
    (hU₁ : ∀ v, U₁.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
      ρ' (ι Q' (f v)) ∘ₗ U₁.toLinearEquiv.toLinearMap)
    (hU₂ : ∀ v, U₂.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
      ρ' (ι Q' (f v)) ∘ₗ U₂.toLinearEquiv.toLinearMap)
    {ε₁ ε₂ : ℂ}
    (T : eigenspace (ρ (chirality Q o)) ε₁ →ₗ[ℂ] eigenspace (ρ (chirality Q o)) ε₂) :
    (halfSpinLinearIsometryEquiv o' ho hU₂ ε₂).toLinearEquiv.toLinearMap ∘ₗ
        T ∘ₗ (halfSpinLinearIsometryEquiv o' ho hU₂ ε₁).symm.toLinearEquiv.toLinearMap =
      (halfSpinLinearIsometryEquiv o' ho hU₁ ε₂).toLinearEquiv.toLinearMap ∘ₗ
        T ∘ₗ (halfSpinLinearIsometryEquiv o' ho hU₁ ε₁).symm.toLinearEquiv.toLinearMap := by
  obtain ⟨z, hz, _⟩ := existsUnique_circle_smul_intertwiner hsurj U₁ U₂ hU₁ hU₂
  have hsymm (w' : W') : U₂.symm w' = (z⁻¹ : Circle) • U₁.symm w' := by
    apply U₂.injective
    rw [U₂.apply_symm_apply, Circle.smul_def, map_smul, hz, smul_smul, ← Circle.coe_mul,
      inv_mul_cancel, Circle.coe_one, one_smul, U₁.apply_symm_apply]
  ext ψ'
  have h₁ : (halfSpinLinearIsometryEquiv o' ho hU₂ ε₁).symm ψ' =
      ((z : ℂ)⁻¹) • (halfSpinLinearIsometryEquiv o' ho hU₁ ε₁).symm ψ' := by
    apply Subtype.ext
    simpa [Circle.smul_def] using hsymm ψ'
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
  rw [h₁, map_smul, map_smul, Submodule.coe_smul, coe_halfSpinLinearIsometryEquiv_apply,
    coe_halfSpinLinearIsometryEquiv_apply, hz, smul_smul, inv_mul_cancel₀ z.coe_ne_zero, one_smul]

end HalfSpinIntertwiner

end DimensionFour

end CliffordAlgebra

end

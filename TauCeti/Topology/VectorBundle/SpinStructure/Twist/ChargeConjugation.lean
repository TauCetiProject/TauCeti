/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.SpinStructure.ChargeConjugation
public import TauCeti.Topology.VectorBundle.SpinStructure.Twist.Basic

/-!
# The charge conjugate of a twisted `Spinᶜ` structure

Let `s` be a `Spinᶜ` structure of rank `n ≥ 1` with principal bundle `P`, and let `L` be a
principal `U(1)`-bundle over the same base. The twist `s.twist L`
(`TauCeti.SpinCStructure.twist`) has principal bundle `(P ×_X L) ×_μ Spinᶜ(n)`, where
`μ ([s, z], w) = [s, z w]` is multiplication by the central circle, and the charge conjugate
`s.chargeConj` (`TauCeti.SpinCStructure.chargeConj`) is the extension of `s` along
`χ : [g, z] ↦ [g, z⁻¹]`.

This file proves that charge conjugation turns a twist by `L` into a twist by the inverse of `L`.
An inverse of `L` is presented by a principal `U(1)`-bundle `L'` with a continuous fibrewise map
`ψ : L → L'` inverting the action, `ψ (l • w) = ψ l • w⁻¹`: for instance the unit circle bundle
of the dual of the Hermitian line of `L`, or the extension of structure group of `L` along the
inversion of `U(1)`, with `ψ = [·, 1]`. Then

`(s.twist L).chargeConj ≃ s.chargeConj.twist L'`

(`TauCeti.SpinCStructure.chargeConjTwistEquiv`), by
`[[(p, l), a], h] ↦ [([p, 1], ψ l), χ(a) h]`
(`TauCeti.SpinCStructure.chargeConjTwistEquiv_toEquiv_mk`). The identity behind it is
`χ (μ (a, w)) = μ (χ a, w⁻¹)`, since `χ [1, w] = [1, w⁻¹]`
(`CliffordAlgebra.spinCGroup.chargeConj_mulCircle`): the map `(p, l) ↦ [([p, 1], ψ l), 1]` from
`P ×_X L` is equivariant along `χ ∘ μ`, and extending along `μ` and then along `χ` is extending
along `χ ∘ μ` (`TauCeti.OrthonormalFrameLift.extendCompEquiv`).

On a symplectic four-manifold with canonical `Spinᶜ` structure `s_ω` and a Hermitian line `E`
with unit circle bundle `L`, this is the step `conj(s_ω ⊗ E) ≃ conj(s_ω) ⊗ E⁻¹` of Taubes's
identification `conj(s_ω ⊗ E) ≃ s_ω ⊗ (K ⊗ E⁻¹)`. The remaining steps are the identification
of `conj(s_ω)` with `s_ω ⊗ K` and the composition of twists.

## Main definitions

* `TauCeti.SpinCStructure.chargeConjTwistEquiv`: the equivalence
  `(s.twist L).chargeConj ≃ s.chargeConj.twist L'` for an inverse `L'` of `L`.

## Main results

* `TauCeti.SpinCStructure.chargeConjTwistEquiv_toEquiv_mk`,
  `TauCeti.SpinCStructure.chargeConjTwistEquiv_toEquiv_inl`: its formula in frames.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
* C. H. Taubes, *GR = SW: counting curves and connections*, J. Differential Geom. 52 (1999),
  453–609.
-/

public section

noncomputable section

open Bundle MulOpposite CliffordAlgebra TauCeti.PrincipalBundle

namespace TauCeti

namespace SpinCStructure

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : X → Type} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V] {n : ℕ} [NeZero n]
  {L : X → Type} [TopologicalSpace (TotalSpace Circle L)] [∀ x, TopologicalSpace (L x)]
  [FiberBundle Circle L] [∀ x, MulAction Circleᵐᵒᵖ (L x)] [PrincipalBundle Circle L]
  {L' : X → Type} [TopologicalSpace (TotalSpace Circle L')] [∀ x, TopologicalSpace (L' x)]
  [FiberBundle Circle L'] [∀ x, MulAction Circleᵐᵒᵖ (L' x)] [PrincipalBundle Circle L']

/-- The proof that the standard form on `ℝⁿ`, `n ≥ 1`, is nonzero, on which `Spinᶜ(n)` depends. -/
local notation "hQ" =>
  QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm n 0)

/-- Charge conjugation of `Spinᶜ(n)` as a homomorphism. -/
local notation "χ" => MonoidHom.ofClass (spinCGroup.chargeConj (realCliffordForm n 0) hQ)

/-- Charge conjugation is continuous. -/
local notation "hχ" => spinCGroup.continuous_chargeConj (realCliffordForm n 0) hQ

/-- Multiplication by the central circle, `([s, z], w) ↦ [s, z w]`. -/
local notation "μ" => spinCGroup.mulCircle (realCliffordForm n 0) hQ

/-- Multiplication by the central circle is continuous. -/
local notation "hμ" => spinCGroup.continuous_mulCircle (realCliffordForm n 0) hQ

/-- The rotation homomorphism `Spinᶜ(n) → SO(n) ⊆ GL(ℝⁿ)`, along which `Spinᶜ` structures lift
the orthonormal frame bundle. -/
local notation "πᶜ" => MonoidHom.comp
  (Subgroup.subtype (QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)))
  (spinCGroup.toSpecialOrthogonal (realCliffordForm n 0) hQ)

/-- Charge conjugation covers the identity rotation, `πᶜ ∘ χ = πᶜ`. -/
local notation "hπχ" => Eq.trans (MonoidHom.comp_assoc _ _ _)
  (congrArg (MonoidHom.comp
      (Subgroup.subtype (QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0))))
    (spinCGroup.toSpecialOrthogonal_comp_chargeConj (realCliffordForm n 0) hQ))

/-- Multiplication by the central circle covers the rotation of the first factor,
`πᶜ ∘ μ = πᶜ ∘ fst`. -/
private theorem rotation_comp_mulCircle :
    (πᶜ).comp μ = (πᶜ).comp (MonoidHom.fst (spinCGroup (realCliffordForm n 0) hQ) Circle) := by
  rw [MonoidHom.comp_assoc, spinCGroup.toSpecialOrthogonal_comp_mulCircle, MonoidHom.comp_assoc]

/-- The comparison map `(p, l) ↦ [([p, 1], ψ l), 1]` from the fibre product `P ×_X L` to the
principal bundle of `s.chargeConj.twist L'`. -/
private def chargeConjTwistMap (s : SpinCStructure F V n) (ψ : ∀ x, L x → L' x) (x : X)
    (z : (s.fiberProd Circle L).P x) : (s.chargeConj.twist L').P x :=
  Extend.inl μ hμ (P := (s.chargeConj.fiberProd Circle L').P)
    (FiberProd.mk (Extend.inl χ hχ (FiberProd.fst (P := s.P) (Q := L) z))
      (ψ x (FiberProd.snd (P := s.P) (Q := L) z)))

/-- The comparison map `(p, l) ↦ [([p, 1], ψ l), 1]` is equivariant along `χ ∘ μ` when `ψ`
inverts the action of `U(1)`, since `χ (μ (a, w)) = μ (χ a, w⁻¹)`. -/
private theorem chargeConjTwistMap_smul (s : SpinCStructure F V n) (ψ : ∀ x, L x → L' x)
    (hψ : ∀ x (l : L x) (w : Circle), ψ x (op w • l) = op w⁻¹ • ψ x l) (x : X)
    (z : (s.fiberProd Circle L).P x) (g : spinCGroup (realCliffordForm n 0) hQ × Circle) :
    chargeConjTwistMap s ψ x (op g • z) =
      op ((MonoidHom.comp χ μ) g) • chargeConjTwistMap s ψ x z :=
  (congrArg (Extend.inl μ hμ (P := (s.chargeConj.fiberProd Circle L').P) (b := x))
      (congrArg₂ FiberProd.mk (Extend.inl_smul χ hχ (FiberProd.fst (P := s.P) (Q := L) z) g.1)
        (hψ x (FiberProd.snd (P := s.P) (Q := L) z) g.2))).trans
    ((Extend.inl_smul μ hμ (P := (s.chargeConj.fiberProd Circle L').P) _ (χ g.1, g.2⁻¹)).trans
      (congrArg (fun k ↦ op k • chargeConjTwistMap s ψ x z)
        (spinCGroup.chargeConj_mulCircle _ hQ g.1 g.2).symm))

/-- **The charge conjugate of a twist is the twist of the charge conjugate by the inverse
bundle**: `(s.twist L).chargeConj ≃ s.chargeConj.twist L'` for a principal `U(1)`-bundle `L'`
inverse to `L`, in the sense of a continuous fibrewise map `ψ : L → L'` with
`ψ (l • w) = ψ l • w⁻¹`. It sends `[[(p, l), a], h]` to `[([p, 1], ψ l), χ(a) h]`
(`TauCeti.SpinCStructure.chargeConjTwistEquiv_toEquiv_mk`). -/
def chargeConjTwistEquiv (s : SpinCStructure F V n) (ψ : ∀ x, L x → L' x)
    (hψ : ∀ x (l : L x) (w : Circle), ψ x (op w • l) = op w⁻¹ • ψ x l)
    (hψc : Continuous fun l : TotalSpace Circle L ↦
      (⟨l.proj, ψ l.proj l.snd⟩ : TotalSpace Circle L')) :
    (s.twist L).chargeConj.Equiv (s.chargeConj.twist L') :=
  ((s.fiberProd Circle L).extendCompEquiv (ρ' := πᶜ) (ρ'' := πᶜ) μ hμ rotation_comp_mulCircle
      spinCGroup.norm_toLp_toSpecialOrthogonal_apply
      spinCGroup.continuous_toSpecialOrthogonal_apply χ hχ hπχ
      spinCGroup.norm_toLp_toSpecialOrthogonal_apply
      spinCGroup.continuous_toSpecialOrthogonal_apply).symm.trans
    ((s.fiberProd Circle L).extendEquivOfEquivariant (ρ' := πᶜ) _ _
      (by rw [← MonoidHom.comp_assoc, hπχ, rotation_comp_mulCircle]) _ _ _
      (chargeConjTwistMap s ψ) (chargeConjTwistMap_smul s ψ hψ)
      ((Extend.continuous_inl (s.chargeConj.fiberProd Circle L').P μ hμ).comp
        (Continuous.totalSpaceMk_fiberProdMk
          ((Extend.continuous_inl s.P χ hχ).comp FiberProd.continuous_totalSpaceMk_fst)
          (hψc.comp FiberProd.continuous_totalSpaceMk_snd)))
      fun x z ↦ (s.chargeConj.toFrame_twist_inl x _ _).trans (s.toFrame_chargeConj_inl x _))

/-- **The equivalence `(s.twist L).chargeConj ≃ s.chargeConj.twist L'` in frames**:
`[[(p, l), a], h] ↦ [([p, 1], ψ l), χ(a) h]`. -/
@[simp]
theorem chargeConjTwistEquiv_toEquiv_mk (s : SpinCStructure F V n) (ψ : ∀ x, L x → L' x)
    (hψ : ∀ x (l : L x) (w : Circle), ψ x (op w • l) = op w⁻¹ • ψ x l)
    (hψc : Continuous fun l : TotalSpace Circle L ↦
      (⟨l.proj, ψ l.proj l.snd⟩ : TotalSpace Circle L'))
    (x : X) (p : s.P x) (l : L x) (a h : spinCGroup (realCliffordForm n 0) hQ) :
    (chargeConjTwistEquiv s ψ hψ hψc).toEquiv x
        (Extend.mk χ hχ (P := (s.twist L).P) (b := x)
          (Extend.mk μ hμ (P := (s.fiberProd Circle L).P) (FiberProd.mk p l) a) h) =
      Extend.mk μ hμ (P := (s.chargeConj.fiberProd Circle L').P)
        (FiberProd.mk (Extend.inl χ hχ p) (ψ x l)) (spinCGroup.chargeConj _ hQ a * h) := by
  simp only [chargeConjTwistEquiv, OrthonormalFrameLift.Equiv.trans_toEquiv,
    OrthonormalFrameLift.Equiv.symm_toEquiv]
  -- `[[(p, l), a], h] = [[(p, l), 1], χ(a) h]` is the image of `[(p, l), χ(a) h]` under
  -- `extendCompEquiv`.
  have hcomp := (Equiv.symm_apply_eq _).2 (((s.fiberProd Circle L).extendCompEquiv_toEquiv_mk
    (ρ' := πᶜ) (ρ'' := πᶜ) μ hμ rotation_comp_mulCircle
    spinCGroup.norm_toLp_toSpecialOrthogonal_apply
    spinCGroup.continuous_toSpecialOrthogonal_apply χ hχ hπχ
    spinCGroup.norm_toLp_toSpecialOrthogonal_apply
    spinCGroup.continuous_toSpecialOrthogonal_apply x (FiberProd.mk p l) (χ a * h)).trans
      (Extend.mk_mk μ hμ χ hχ (P := (s.fiberProd Circle L).P) (FiberProd.mk p l) a h).symm).symm
  exact (Equiv.trans_apply _ _ _).trans <| (congrArg _ hcomp).trans <|
    (OrthonormalFrameLift.extendEquivOfEquivariant_toEquiv_mk (ρ' := πᶜ) ..).trans
      (Extend.smul_inl μ hμ (P := (s.chargeConj.fiberProd Circle L').P) _ _)

/-- **The equivalence `(s.twist L).chargeConj ≃ s.chargeConj.twist L'` at `[[(p, l), 1], 1]`**:
it is sent to `[([p, 1], ψ l), 1]`. -/
@[simp]
theorem chargeConjTwistEquiv_toEquiv_inl (s : SpinCStructure F V n) (ψ : ∀ x, L x → L' x)
    (hψ : ∀ x (l : L x) (w : Circle), ψ x (op w • l) = op w⁻¹ • ψ x l)
    (hψc : Continuous fun l : TotalSpace Circle L ↦
      (⟨l.proj, ψ l.proj l.snd⟩ : TotalSpace Circle L'))
    (x : X) (p : s.P x) (l : L x) :
    (chargeConjTwistEquiv s ψ hψ hψc).toEquiv x
        (Extend.inl χ hχ (P := (s.twist L).P) (b := x)
          (Extend.inl μ hμ (P := (s.fiberProd Circle L).P) (FiberProd.mk p l))) =
      Extend.inl μ hμ (P := (s.chargeConj.fiberProd Circle L').P)
        (FiberProd.mk (Extend.inl χ hχ p) (ψ x l)) :=
  (congrArg ((chargeConjTwistEquiv s ψ hψ hψc).toEquiv x)
      ((Extend.inl_def χ hχ (P := (s.twist L).P) _).trans
        (congrArg (fun y ↦ Extend.mk χ hχ (P := (s.twist L).P) y 1)
          (Extend.inl_def μ hμ (P := (s.fiberProd Circle L).P) (FiberProd.mk p l))))).trans
    ((chargeConjTwistEquiv_toEquiv_mk s ψ hψ hψc x p l 1 1).trans
      ((congrArg (Extend.mk μ hμ (P := (s.chargeConj.fiberProd Circle L').P) _)
        (by rw [map_one, one_mul])).trans (Extend.inl_def μ hμ _).symm))

end SpinCStructure

end TauCeti

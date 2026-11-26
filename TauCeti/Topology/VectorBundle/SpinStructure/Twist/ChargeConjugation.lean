/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.SpinStructure.ChargeConjugation
public import TauCeti.Topology.VectorBundle.SpinStructure.Twist.Basic

/-!
# Charge conjugation of a `Spinᶜ` structure as a twist

Let `s` be a `Spinᶜ` structure with principal `Spinᶜ(n)`-bundle `P` and determinant line `L`.
Its charge conjugate `s.chargeConj` (`TauCeti.SpinCStructure.chargeConj`) is the extension of `s`
along the automorphism `χ : [g, z] ↦ [g, z⁻¹]` of `Spinᶜ(n)`, and its twist by a principal
`U(1)`-bundle `Q` (`TauCeti.SpinCStructure.twist`) is `s ⊗ E` for the Hermitian line `E` of `Q`.
At the level of structure groups, charge conjugation is multiplication by the inverse
determinant, `χ(g) = g [1, (det g)⁻¹]`
(`CliffordAlgebra.spinCGroup.chargeConj_eq_mul_ofCircle_inv_det`). This file proves the
corresponding equivalences of `Spinᶜ` structures:

* **`conj s ≃ s ⊗ L⁻¹`.** The extension `P ×_{det⁻¹} U(1)` of `P` along the inverse determinant
  character (`TauCeti.SpinCStructure.inverseDeterminantBundle`) is the principal `U(1)`-bundle
  with transition functions `(det g_αβ)⁻¹`, those of `L⁻¹`, and `s.chargeConj` is equivalent to
  the twist of `s` by it
  (`TauCeti.SpinCStructure.chargeConjEquivTwist`), by `[p, 1] ↦ [(p, [p, 1]), 1]`.
* **`conj (s ⊗ E) ≃ s ⊗ (L⁻¹ ⊗ E⁻¹)`.** For a principal `U(1)`-bundle `Q`, the extension
  `(P ×_X Q) ×_ψ U(1)` of the fibre product of `P` and `Q` along
  `ψ (g, w) = (det g * w)⁻¹` (`TauCeti.SpinCStructure.inverseDeterminantTwistBundle`) is the
  principal `U(1)`-bundle with transition functions `(det g_αβ)⁻¹ w_αβ⁻¹`, those of
  `L⁻¹ ⊗ E⁻¹`.
  The charge conjugate of `s.twist Q` is equivalent to the twist of `s` by it
  (`TauCeti.SpinCStructure.twistChargeConjEquivTwist`), by
  `[[(p, q), 1], 1] ↦ [(p, [(p, q), 1]), 1]`. The group-level input is
  `χ (g [1, w]) = g [1, (det g)⁻¹ w⁻¹]` (`CliffordAlgebra.spinCGroup.chargeConj_mul_ofCircle`).

Both equivalences preserve frames, as equivalences of `Spinᶜ` structures do. For the canonical
`Spinᶜ` structure `s_ω` of an almost Hermitian four-manifold, whose determinant line is the
anticanonical line `K⁻¹`, the second is the isomorphism `conj (s_ω ⊗ E) ≃ s_ω ⊗ (K ⊗ E⁻¹)` that
compares the Seiberg–Witten equations of the labels `E` and `K ⊗ E⁻¹` (Taubes, *GR = SW*), once the
bundle `(P ×_X Q) ×_ψ U(1)` is identified with the circle bundle of `K ⊗ E⁻¹`. That identification
of associated lines is not made here.

## Main definitions

* `TauCeti.SpinCStructure.inverseDeterminantBundle`: the principal `U(1)`-bundle
  `P ×_{det⁻¹} U(1)` with the transition functions of the inverse determinant line.
* `TauCeti.SpinCStructure.chargeConjEquivTwist`: the equivalence `s.chargeConj ≃ s ⊗ L⁻¹`.
* `TauCeti.SpinCStructure.inverseDeterminantTwistBundle`: the principal `U(1)`-bundle
  `(P ×_X Q) ×_ψ U(1)` with the transition functions of `L⁻¹ ⊗ E⁻¹`.
* `TauCeti.SpinCStructure.twistChargeConjEquivTwist`: the equivalence
  `(s ⊗ E).chargeConj ≃ s ⊗ (L⁻¹ ⊗ E⁻¹)`.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
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

/-- The proof that the standard form on `ℝⁿ`, `n ≥ 1`, is nonzero, on which `Spinᶜ(n)` depends. -/
local notation "hQ" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm n 0)
local notation "SpinC" => spinCGroup (realCliffordForm n 0) hQ

/-- Charge conjugation of `Spinᶜ(n)` as a homomorphism. -/
local notation "χ" => MonoidHom.ofClass (spinCGroup.chargeConj (realCliffordForm n 0) hQ)

/-- Multiplication by the central circle, `μ (a, w) = a [1, w]`. -/
local notation "μ" => spinCGroup.mulCircle (realCliffordForm n 0) hQ

/-- The inverse determinant character `Spinᶜ(n) → U(1)`, `g ↦ (det g)⁻¹`. -/
local notation "δ" => (spinCGroup.det (realCliffordForm n 0) hQ)⁻¹

/-- The character `Spinᶜ(n) × U(1) → U(1)`, `(g, w) ↦ (det g * w)⁻¹`. -/
local notation "ψ" =>
  (MonoidHom.comp (spinCGroup.det (realCliffordForm n 0) hQ) (MonoidHom.fst SpinC Circle) *
    MonoidHom.snd SpinC Circle)⁻¹

/-- The inverse determinant character is continuous. -/
local notation "hδ" => spinCGroup.continuous_inv_det (realCliffordForm n 0) hQ

/-- The character `(g, w) ↦ (det g * w)⁻¹` is continuous. -/
local notation "hψ" => spinCGroup.continuous_inv_det_comp_fst_mul_snd (realCliffordForm n 0) hQ

/-- Charge conjugation is continuous. -/
local notation "hχ" => spinCGroup.continuous_chargeConj (realCliffordForm n 0) hQ

/-- Multiplication by the central circle is continuous. -/
local notation "hμ" => spinCGroup.continuous_mulCircle (realCliffordForm n 0) hQ

/-- The rotation homomorphism `Spinᶜ(n) → SO(n) ⊆ GL(ℝⁿ)`. -/
local notation "πᶜ" => MonoidHom.comp
  (Subgroup.subtype (QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)))
  (spinCGroup.toSpecialOrthogonal (realCliffordForm n 0) hQ)

/-- Charge conjugation covers the identity rotation, `πᶜ ∘ χ = πᶜ`. -/
local notation "hπχ" =>
  spinCGroup.subtype_comp_toSpecialOrthogonal_comp_chargeConj (realCliffordForm n 0) hQ

/-- Multiplication by the central circle covers the first projection, `πᶜ ∘ μ = πᶜ ∘ fst`. -/
local notation "hπμ" =>
  spinCGroup.subtype_comp_toSpecialOrthogonal_comp_mulCircle (realCliffordForm n 0) hQ

/-! ### Charge conjugation is the twist by the inverse determinant -/

/-- The **inverse determinant circle bundle** of a `Spinᶜ` structure `s` with principal bundle `P`:
the extension `P ×_{det⁻¹} U(1)` of `P` along the character `g ↦ (det g)⁻¹`. Its transition
functions are `(det g_αβ)⁻¹`, the inverses of those of the determinant line `P ×_det ℂ` of `s`. -/
abbrev inverseDeterminantBundle (s : SpinCStructure F V n) : X → Type :=
  Extend s.P δ hδ

variable (s : SpinCStructure F V n)

/-- The comparison map `p ↦ [(p, [p, 1]), 1]` from the principal bundle of `s` to that of its twist
by the inverse determinant bundle. -/
private def chargeConjTwistMap (x : X) (p : s.P x) :
    (s.twist s.inverseDeterminantBundle).P x :=
  Extend.inl μ hμ (P := (s.fiberProd Circle s.inverseDeterminantBundle).P)
    (FiberProd.mk p (Extend.inl δ hδ p))

/-- The comparison map is equivariant along charge conjugation: `χ g = g [1, (det g)⁻¹]`. -/
private theorem chargeConjTwistMap_smul (x : X) (p : s.P x) (g : SpinC) :
    chargeConjTwistMap s x (op g • p) = op (χ g) • chargeConjTwistMap s x p := by
  rw [chargeConjTwistMap, chargeConjTwistMap, Extend.inl_smul]
  -- `(p • g, [p, 1] • (det g)⁻¹)` is `(p, [p, 1]) • (g, (det g)⁻¹)`, and `μ (g, (det g)⁻¹) = χ g`.
  refine (Extend.inl_smul μ hμ (P := FiberProd s.P s.inverseDeterminantBundle)
    (FiberProd.mk p (Extend.inl δ hδ p)) (g, δ g)).trans ?_
  rw [spinCGroup.mulCircle_apply, MonoidHom.inv_apply, MonoidHom.coe_ofClass,
    spinCGroup.chargeConj_eq_mul_ofCircle_inv_det]
  -- The sides differ only in the fibre `FiberProd s.P _ x` versus `(s.fiberProd Circle _).P x`,
  -- which agree by unfolding `OrthonormalFrameLift.fiberProd`.
  rfl

/-- The comparison map is continuous on total spaces. -/
private theorem continuous_chargeConjTwistMap :
    Continuous fun p : TotalSpace SpinC s.P ↦
      (⟨p.proj, chargeConjTwistMap s p.proj p.snd⟩ :
        TotalSpace SpinC (s.twist s.inverseDeterminantBundle).P) :=
  (Extend.continuous_inl (FiberProd s.P s.inverseDeterminantBundle) μ hμ).comp
    (continuous_id.totalSpaceMk_fiberProdMk (Extend.continuous_inl s.P δ hδ))

/-- **Charge conjugation is twisting by the inverse determinant**: the charge conjugate of a
`Spinᶜ` structure `s` is equivalent to the twist of `s` by the principal `U(1)`-bundle
`P ×_{det⁻¹} U(1)`, which has the transition functions of the inverse of its determinant line:
`conj s ≃ s ⊗ L⁻¹`, by
`[p, h] ↦ [(p, [p, 1]), h]`. -/
def chargeConjEquivTwist : s.chargeConj.Equiv (s.twist s.inverseDeterminantBundle) :=
  s.extendSpinCEquivOfEquivariant χ hχ hπχ (s.twist s.inverseDeterminantBundle)
    (chargeConjTwistMap s) (chargeConjTwistMap_smul s)
    (continuous_chargeConjTwistMap s) fun x p ↦ toFrame_twist_inl s x p _

/-- **The comparison of charge conjugate and twist at `[p, 1]`**: it sends `[p, 1]` to
`[(p, [p, 1]), 1]`. -/
@[simp]
theorem chargeConjEquivTwist_toEquiv_inl (x : X) (p : s.P x) :
    s.chargeConjEquivTwist.toEquiv x (Extend.inl χ hχ p) =
      Extend.inl μ hμ (P := (s.fiberProd Circle s.inverseDeterminantBundle).P)
        (FiberProd.mk p (Extend.inl δ hδ p)) :=
  OrthonormalFrameLift.extendSpinCEquivOfEquivariant_toEquiv_inl ..

/-- **The comparison of charge conjugate and twist at `[p, h]`**: it sends `[p, h]` to
`[(p, [p, 1]), h]`. -/
@[simp]
theorem chargeConjEquivTwist_toEquiv_mk (x : X) (p : s.P x) (h : SpinC) :
    s.chargeConjEquivTwist.toEquiv x (Extend.mk χ hχ p h) =
      Extend.mk μ hμ (P := (s.fiberProd Circle s.inverseDeterminantBundle).P)
        (FiberProd.mk p (Extend.inl δ hδ p)) h :=
  (OrthonormalFrameLift.extendSpinCEquivOfEquivariant_toEquiv_mk ..).trans (Extend.smul_inl ..)

/-! ### The charge conjugate of a twist -/

variable (Q : X → Type) [TopologicalSpace (TotalSpace Circle Q)] [∀ x, TopologicalSpace (Q x)]
  [FiberBundle Circle Q] [∀ x, MulAction Circleᵐᵒᵖ (Q x)] [PrincipalBundle Circle Q]

/-- The **inverse determinant circle bundle of a twist**, for a `Spinᶜ` structure `s` with
principal bundle `P` and determinant line `L`, and a principal `U(1)`-bundle `Q` with line `E`: the
extension `(P ×_X Q) ×_ψ U(1)` of the fibre product of `P` and `Q` along the character
`ψ (g, w) = (det g * w)⁻¹`. Its transition functions are `(det g_αβ)⁻¹ w_αβ⁻¹`, those of
`L⁻¹ ⊗ E⁻¹`. -/
abbrev inverseDeterminantTwistBundle : X → Type :=
  Extend (FiberProd s.P Q) ψ hψ

/-- The comparison map `(p, q) ↦ [(p, [(p, q), 1]), 1]` from the fibre product of `P` and `Q` to
the principal bundle of the twist of `s` by `(P ×_X Q) ×_ψ U(1)`. -/
private def twistChargeConjTwistMap (x : X) (z : FiberProd s.P Q x) :
    (s.twist (s.inverseDeterminantTwistBundle Q)).P x :=
  Extend.inl μ hμ (P := (s.fiberProd Circle (s.inverseDeterminantTwistBundle Q)).P)
    (FiberProd.mk z.fst (Extend.inl ψ hψ z))

/-- The comparison map is equivariant along `χ ∘ μ`:
`χ (g [1, w]) = g [1, (det g * w)⁻¹]`. -/
private theorem twistChargeConjTwistMap_smul (x : X) (z : FiberProd s.P Q x)
    (g : SpinC × Circle) :
    twistChargeConjTwistMap s Q x (op g • z) =
      op ((χ).comp μ g) • twistChargeConjTwistMap s Q x z := by
  rw [twistChargeConjTwistMap, twistChargeConjTwistMap, Extend.inl_smul, FiberProd.fst_smul,
    unop_op]
  -- `(p • g, [z, 1] • ψ g)` is `(p, [z, 1]) • (g.1, ψ g)`, and `μ (g.1, ψ g) = χ (μ g)`.
  refine (Extend.inl_smul μ hμ (P := FiberProd s.P (s.inverseDeterminantTwistBundle Q))
    (FiberProd.mk z.fst (Extend.inl ψ hψ z)) (g.1, ψ g)).trans ?_
  have hg : μ (g.1, ψ g) = (χ).comp μ g := by
    obtain ⟨a, w⟩ := g
    simp only [MonoidHom.comp_apply, MonoidHom.coe_ofClass, MonoidHom.inv_apply,
      MonoidHom.mul_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, spinCGroup.mulCircle_apply,
      spinCGroup.chargeConj_mul_ofCircle, mul_inv]
  rw [hg]
  -- As above, the fibres `FiberProd s.P _ x` and `(s.fiberProd Circle _).P x` agree by unfolding.
  rfl

/-- The comparison map is continuous on total spaces. -/
private theorem continuous_twistChargeConjTwistMap :
    Continuous fun z : TotalSpace (SpinC × Circle) (s.fiberProd Circle Q).P ↦
      (⟨z.proj, twistChargeConjTwistMap s Q z.proj z.snd⟩ :
        TotalSpace SpinC (s.twist (s.inverseDeterminantTwistBundle Q)).P) :=
  (Extend.continuous_inl (FiberProd s.P (s.inverseDeterminantTwistBundle Q)) μ hμ).comp
    (FiberProd.continuous_totalSpaceMk_fst.totalSpaceMk_fiberProdMk
      (Extend.continuous_inl (FiberProd s.P Q) ψ hψ))

/-- **The charge conjugate of a twist**: for a `Spinᶜ` structure `s` with principal bundle `P`
and determinant line `L`, and a principal `U(1)`-bundle `Q` with line `E`, the charge conjugate of
`s ⊗ E` is equivalent to the twist of `s` by the principal `U(1)`-bundle `(P ×_X Q) ×_ψ U(1)`,
which has the transition functions of `L⁻¹ ⊗ E⁻¹`: `conj (s ⊗ E) ≃ s ⊗ (L⁻¹ ⊗ E⁻¹)`, by
`[[(p, q), 1], h] ↦ [(p, [(p, q), 1]), h]`. For the canonical `Spinᶜ` structure of an almost
Hermitian four-manifold, where `L = K⁻¹`, this gives `conj (s_ω ⊗ E) ≃ s_ω ⊗ (K ⊗ E⁻¹)` after
identifying `(P ×_X Q) ×_ψ U(1)` with the circle bundle of `K ⊗ E⁻¹`; that identification is not
part of this statement. -/
def twistChargeConjEquivTwist :
    (s.twist Q).chargeConj.Equiv (s.twist (s.inverseDeterminantTwistBundle Q)) :=
  ((s.fiberProd Circle Q).extendCompEquiv μ hμ hπμ
      spinCGroup.norm_toLp_toSpecialOrthogonal_apply spinCGroup.continuous_toSpecialOrthogonal_apply
      χ hχ hπχ spinCGroup.norm_toLp_toSpecialOrthogonal_apply
      spinCGroup.continuous_toSpecialOrthogonal_apply).symm.trans
    ((s.fiberProd Circle Q).extendSpinCEquivOfEquivariant ((χ).comp μ)
      (by rw [MonoidHom.coe_comp]; exact Continuous.comp hχ hμ)
      (by rw [← MonoidHom.comp_assoc, hπχ, hπμ])
      (s.twist (s.inverseDeterminantTwistBundle Q)) (twistChargeConjTwistMap s Q)
      (fun x z g ↦ twistChargeConjTwistMap_smul s Q x z g)
      (continuous_twistChargeConjTwistMap s Q)
      fun x z ↦ toFrame_twist_inl s x z.fst _)

/-- **The comparison of the charge conjugate of a twist with a twist at `[[(p, q), 1], 1]`**: it
sends `[[(p, q), 1], 1]` to `[(p, [(p, q), 1]), 1]`. -/
@[simp]
theorem twistChargeConjEquivTwist_toEquiv_inl (x : X) (p : s.P x) (q : Q x) :
    (s.twistChargeConjEquivTwist Q).toEquiv x
        (Extend.inl χ hχ (Extend.inl μ hμ (P := (s.fiberProd Circle Q).P) (FiberProd.mk p q))) =
      Extend.inl μ hμ (P := (s.fiberProd Circle (s.inverseDeterminantTwistBundle Q)).P)
        (FiberProd.mk p (Extend.inl ψ hψ (FiberProd.mk p q))) := by
  have h := (s.fiberProd Circle Q).extendCompEquiv_toEquiv_inl μ hμ hπμ
    spinCGroup.norm_toLp_toSpecialOrthogonal_apply spinCGroup.continuous_toSpecialOrthogonal_apply
    χ hχ hπχ spinCGroup.norm_toLp_toSpecialOrthogonal_apply
    spinCGroup.continuous_toSpecialOrthogonal_apply x (FiberProd.mk p q)
  simp only [twistChargeConjEquivTwist, OrthonormalFrameLift.Equiv.trans_toEquiv,
    OrthonormalFrameLift.Equiv.symm_toEquiv, ← h]
  -- The fibres of the charge conjugate of the twist are those of the iterated extension only up
  -- to unfolding, so `Equiv.trans_apply` and `Equiv.symm_apply_apply` are applied by unification.
  refine ((_root_.Equiv.trans_apply _ _ _).trans
    (congrArg _ (_root_.Equiv.symm_apply_apply _ _))).trans ?_
  exact OrthonormalFrameLift.extendSpinCEquivOfEquivariant_toEquiv_inl ..

/-- **The comparison of the charge conjugate of a twist with a twist at `[[(p, q), 1], h]`**: it
sends `[[(p, q), 1], h]` to `[(p, [(p, q), 1]), h]`. -/
@[simp]
theorem twistChargeConjEquivTwist_toEquiv_mk (x : X) (p : s.P x) (q : Q x) (h : SpinC) :
    (s.twistChargeConjEquivTwist Q).toEquiv x
        (Extend.mk χ hχ
          (Extend.inl μ hμ (P := (s.fiberProd Circle Q).P) (FiberProd.mk p q)) h) =
      Extend.mk μ hμ (P := (s.fiberProd Circle (s.inverseDeterminantTwistBundle Q)).P)
        (FiberProd.mk p (Extend.inl ψ hψ (FiberProd.mk p q))) h := by
  -- `[a, h] = [a, 1] • h` on both sides, and the equivalence is equivariant.
  refine (congrArg _ (Extend.smul_inl χ hχ _ h).symm).trans ?_
  exact ((s.twistChargeConjEquivTwist Q).map_smul x _ h).trans
    ((congrArg (op h • ·) (twistChargeConjEquivTwist_toEquiv_inl s Q x p q)).trans
      (Extend.smul_inl μ hμ _ h))

/-- **The comparison of the charge conjugate of a twist with a twist at `[[(p, q), k], h]`**: it
sends `[[(p, q), k], h]` to `[(p, [(p, q), 1]), χ k * h]`. -/
@[simp]
theorem twistChargeConjEquivTwist_toEquiv_mk_mk (x : X) (p : s.P x) (q : Q x) (k h : SpinC) :
    (s.twistChargeConjEquivTwist Q).toEquiv x
        (Extend.mk χ hχ
          (Extend.mk μ hμ (P := (s.fiberProd Circle Q).P) (FiberProd.mk p q) k) h) =
      Extend.mk μ hμ (P := (s.fiberProd Circle (s.inverseDeterminantTwistBundle Q)).P)
        (FiberProd.mk p (Extend.inl ψ hψ (FiberProd.mk p q))) (χ k * h) := by
  -- `[[(p, q), k], h] = [[(p, q), 1] • k, h] = [[(p, q), 1], χ k * h]`.
  refine (congrArg _ ((congrArg (Extend.mk χ hχ · h) (Extend.smul_inl μ hμ _ k).symm).trans
    (Extend.mk_smul χ hχ _ k h))).trans ?_
  exact twistChargeConjEquivTwist_toEquiv_mk s Q x p q _

end SpinCStructure

end TauCeti

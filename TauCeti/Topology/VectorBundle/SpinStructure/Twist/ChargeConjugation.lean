/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Principal.Tensor
public import TauCeti.Topology.VectorBundle.SpinStructure.ChargeConjugation
public import TauCeti.Topology.VectorBundle.SpinStructure.Twist.Basic

/-!
# Charge conjugation and twisting of `Spinᶜ` structures

Let `s` be a `Spinᶜ` structure with principal `Spinᶜ(n)`-bundle `P` and determinant line `L`.
Its charge conjugate `s.chargeConj` (`TauCeti.SpinCStructure.chargeConj`) is the extension of `s`
along the automorphism `χ : [g, z] ↦ [g, z⁻¹]` of `Spinᶜ(n)`, and its twist by a principal
`U(1)`-bundle `Q` (`TauCeti.SpinCStructure.twist`) is `s ⊗ E` for the Hermitian line `E` of `Q`,
with principal bundle `(P ×_X Q) ×_μ Spinᶜ(n)`, where `μ ([s, z], w) = [s, z w]` is
multiplication by the central circle. At the level of structure groups, charge conjugation is
multiplication by the inverse determinant, `χ(g) = g [1, (det g)⁻¹]`
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
* **`conj (s ⊗ E) ≃ conj s ⊗ E⁻¹`.** An inverse of a principal `U(1)`-bundle `L` is presented by
  a principal `U(1)`-bundle `L'` with a continuous fibrewise map `ψ : L → L'` inverting the
  action, `ψ (l • w) = ψ l • w⁻¹`: for instance the unit circle bundle of the dual of the
  Hermitian line of `L`, or the extension of structure group of `L` along the inversion of
  `U(1)`, with `ψ = [·, 1]`. Then `(s.twist L).chargeConj ≃ s.chargeConj.twist L'`
  (`TauCeti.SpinCStructure.chargeConjTwistEquiv`), by
  `[[(p, l), a], h] ↦ [([p, 1], ψ l), χ(a) h]`
  (`TauCeti.SpinCStructure.chargeConjTwistEquiv_toEquiv_mk`). The identity behind it is
  `χ (μ (a, w)) = μ (χ a, w⁻¹)`, since `χ [1, w] = [1, w⁻¹]`
  (`CliffordAlgebra.spinCGroup.chargeConj_mulCircle`): the map `(p, l) ↦ [([p, 1], ψ l), 1]` from
  `P ×_X L` is equivariant along `χ ∘ μ`, and extending along `μ` and then along `χ` is extending
  along `χ ∘ μ` (`TauCeti.OrthonormalFrameLift.extendCompEquiv`). For `L'` the inverse bundle
  `E⁻¹ = E ×_{z ↦ z⁻¹} U(1)` (`TauCeti.PrincipalBundle.Inverse`) this is
  `TauCeti.SpinCStructure.chargeConjTwistEquivInverse`.
* **`conj (s ⊗ E) ≃ s ⊗ ((P ×_{det⁻¹} U(1)) ⊗ E⁻¹)`.** With the tensor product
  `A ⊗ B = (A ×_X B) ×_{(a, b) ↦ a b} U(1)` of principal `U(1)`-bundles
  (`TauCeti.PrincipalBundle.Tensor`), the charge conjugate of `s.twist E` is equivalent to the
  twist of `s` by the tensor product of the inverse determinant bundle with `E⁻¹`
  (`TauCeti.SpinCStructure.chargeConjTwistEquivTwist`), by
  `[[(p, e), a], h] ↦ [(p, [([p, 1], [e, 1]), 1]), χ a h]`. This is the second equivalence with
  `L⁻¹ ⊗ E⁻¹` presented as a tensor product of the two circle bundles.

All these equivalences preserve frames, as equivalences of `Spinᶜ` structures do. For the
canonical `Spinᶜ` structure `s_ω` of an almost Hermitian four-manifold, whose determinant line is
the anticanonical line `K⁻¹`, the second is the isomorphism `conj (s_ω ⊗ E) ≃ s_ω ⊗ (K ⊗ E⁻¹)`
that compares the Seiberg–Witten equations of the labels `E` and `K ⊗ E⁻¹` (Taubes, *GR = SW*),
once the bundle `(P ×_X Q) ×_ψ U(1)` is identified with the circle bundle of `K ⊗ E⁻¹`. That
identification of associated lines is not made here. The third is the step
`conj(s_ω ⊗ E) ≃ conj(s_ω) ⊗ E⁻¹` of the same identification.

## Main definitions

* `TauCeti.SpinCStructure.inverseDeterminantBundle`: the principal `U(1)`-bundle
  `P ×_{det⁻¹} U(1)` with the transition functions of the inverse determinant line.
* `TauCeti.SpinCStructure.chargeConjEquivTwist`: the equivalence `s.chargeConj ≃ s ⊗ L⁻¹`.
* `TauCeti.SpinCStructure.inverseDeterminantTwistBundle`: the principal `U(1)`-bundle
  `(P ×_X Q) ×_ψ U(1)` with the transition functions of `L⁻¹ ⊗ E⁻¹`.
* `TauCeti.SpinCStructure.twistChargeConjEquivTwist`: the equivalence
  `(s ⊗ E).chargeConj ≃ s ⊗ (L⁻¹ ⊗ E⁻¹)`.
* `TauCeti.SpinCStructure.chargeConjTwistEquiv`: the equivalence
  `(s.twist L).chargeConj ≃ s.chargeConj.twist L'` for an inverse `L'` of `L`.
* `TauCeti.SpinCStructure.chargeConjTwistEquivInverse`: the equivalence
  `(s.twist E).chargeConj ≃ s.chargeConj.twist E⁻¹` for the inverse bundle `E⁻¹`.
* `TauCeti.SpinCStructure.chargeConjTwistEquivTwist`: the equivalence
  `(s.twist E).chargeConj ≃ s.twist ((P ×_{det⁻¹} U(1)) ⊗ E⁻¹)`.

## Main results

* `TauCeti.SpinCStructure.chargeConjTwistEquiv_toEquiv_mk`,
  `TauCeti.SpinCStructure.chargeConjTwistEquiv_toEquiv_inl`: the formula of
  `chargeConjTwistEquiv` in frames, and likewise `chargeConjTwistEquivInverse_toEquiv_mk`,
  `chargeConjTwistEquivTwist_toEquiv_mk` and their `_toEquiv_inl` versions.

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

/-- Charge conjugation is continuous. -/
local notation "hχ" => spinCGroup.continuous_chargeConj (realCliffordForm n 0) hQ

/-- Multiplication by the central circle, `μ (a, w) = a [1, w]`. -/
local notation "μ" => spinCGroup.mulCircle (realCliffordForm n 0) hQ

/-- Multiplication by the central circle is continuous. -/
local notation "hμ" => spinCGroup.continuous_mulCircle (realCliffordForm n 0) hQ

/-- The rotation homomorphism `Spinᶜ(n) → SO(n) ⊆ GL(ℝⁿ)`, along which `Spinᶜ` structures lift
the orthonormal frame bundle. -/
local notation "πᶜ" => MonoidHom.comp
  (Subgroup.subtype (QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)))
  (spinCGroup.toSpecialOrthogonal (realCliffordForm n 0) hQ)

/-- Charge conjugation covers the identity rotation, `πᶜ ∘ χ = πᶜ`. -/
local notation "hπχ" =>
  spinCGroup.subtype_comp_toSpecialOrthogonal_comp_chargeConj (realCliffordForm n 0) hQ

/-- Multiplication by the central circle covers the first projection, `πᶜ ∘ μ = πᶜ ∘ fst`. -/
local notation "hπμ" =>
  spinCGroup.subtype_comp_toSpecialOrthogonal_comp_mulCircle (realCliffordForm n 0) hQ

section InverseDeterminant

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

/-! ### Charge conjugation is the twist by the inverse determinant -/

/-- The **inverse determinant circle bundle** of a `Spinᶜ` structure `s` with principal bundle `P`:
the extension `P ×_{det⁻¹} U(1)` of `P` along the character `g ↦ (det g)⁻¹`. Its transition
functions are `(det g_αβ)⁻¹`, the inverses of those of the determinant line `P ×_det ℂ` of `s`. -/
abbrev inverseDeterminantBundle (s : SpinCStructure F V n) : X → Type :=
  Extend s.P δ hδ

variable (s : SpinCStructure F V n)

/-- The comparison map `p ↦ [(p, [p, 1]), 1]` from the principal bundle of `s` to that of its twist
by the inverse determinant bundle. -/
private def inverseDeterminantTwistMap (x : X) (p : s.P x) :
    (s.twist s.inverseDeterminantBundle).P x :=
  Extend.inl μ hμ (P := (s.fiberProd Circle s.inverseDeterminantBundle).P)
    (FiberProd.mk p (Extend.inl δ hδ p))

/-- The comparison map is equivariant along charge conjugation: `χ g = g [1, (det g)⁻¹]`. -/
private theorem inverseDeterminantTwistMap_smul (x : X) (p : s.P x) (g : SpinC) :
    inverseDeterminantTwistMap s x (op g • p) = op (χ g) • inverseDeterminantTwistMap s x p := by
  rw [inverseDeterminantTwistMap, inverseDeterminantTwistMap, Extend.inl_smul]
  -- `(p • g, [p, 1] • (det g)⁻¹)` is `(p, [p, 1]) • (g, (det g)⁻¹)`, and `μ (g, (det g)⁻¹) = χ g`.
  refine (Extend.inl_smul μ hμ (P := FiberProd s.P s.inverseDeterminantBundle)
    (FiberProd.mk p (Extend.inl δ hδ p)) (g, δ g)).trans ?_
  rw [spinCGroup.mulCircle_apply, MonoidHom.inv_apply, MonoidHom.coe_ofClass,
    spinCGroup.chargeConj_eq_mul_ofCircle_inv_det]
  -- The sides differ only in the fibre `FiberProd s.P _ x` versus `(s.fiberProd Circle _).P x`,
  -- which agree by unfolding `OrthonormalFrameLift.fiberProd`.
  rfl

/-- The comparison map is continuous on total spaces. -/
private theorem continuous_inverseDeterminantTwistMap :
    Continuous fun p : TotalSpace SpinC s.P ↦
      (⟨p.proj, inverseDeterminantTwistMap s p.proj p.snd⟩ :
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
    (inverseDeterminantTwistMap s) (inverseDeterminantTwistMap_smul s)
    (continuous_inverseDeterminantTwistMap s) fun x p ↦ toFrame_twist_inl s x p _

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

/-- **The comparison of the charge conjugate of a twist with a twist at `[[(p, q), k], 1]`**: it
sends `[[(p, q), k], 1]` to `[(p, [(p, q), 1]), χ k]`. -/
@[simp]
theorem twistChargeConjEquivTwist_toEquiv_inl_mk (x : X) (p : s.P x) (q : Q x) (k : SpinC) :
    (s.twistChargeConjEquivTwist Q).toEquiv x
        (Extend.inl χ hχ (Extend.mk μ hμ (P := (s.fiberProd Circle Q).P) (FiberProd.mk p q) k)) =
      Extend.mk μ hμ (P := (s.fiberProd Circle (s.inverseDeterminantTwistBundle Q)).P)
        (FiberProd.mk p (Extend.inl ψ hψ (FiberProd.mk p q))) (χ k) := by
  rw [Extend.inl_def, twistChargeConjEquivTwist_toEquiv_mk_mk, mul_one]

end InverseDeterminant

/-! ### The charge conjugate of a twist by an inverse bundle -/

section InverseTwist

variable {L : X → Type} [TopologicalSpace (TotalSpace Circle L)] [∀ x, TopologicalSpace (L x)]
  [FiberBundle Circle L] [∀ x, MulAction Circleᵐᵒᵖ (L x)] [PrincipalBundle Circle L]
  {L' : X → Type} [TopologicalSpace (TotalSpace Circle L')] [∀ x, TopologicalSpace (L' x)]
  [FiberBundle Circle L'] [∀ x, MulAction Circleᵐᵒᵖ (L' x)] [PrincipalBundle Circle L']

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
  ((s.fiberProd Circle L).extendCompEquiv (ρ' := πᶜ) (ρ'' := πᶜ) μ hμ hπμ
      spinCGroup.norm_toLp_toSpecialOrthogonal_apply
      spinCGroup.continuous_toSpecialOrthogonal_apply χ hχ hπχ
      spinCGroup.norm_toLp_toSpecialOrthogonal_apply
      spinCGroup.continuous_toSpecialOrthogonal_apply).symm.trans
    ((s.fiberProd Circle L).extendEquivOfEquivariant (ρ' := πᶜ) _ _
      (by rw [← MonoidHom.comp_assoc, hπχ, hπμ]) _ _ _
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
  simp only [chargeConjTwistEquiv, OrthonormalFrameLift.Equiv.trans_toEquiv]
  -- `[[(p, l), a], h]` is the image of `[(p, l), χ(a) h]` under `extendCompEquiv`.
  exact (Equiv.trans_apply _ _ _).trans <| (congrArg _
    ((s.fiberProd Circle L).extendCompEquiv_symm_toEquiv_mk_mk (ρ' := πᶜ) (ρ'' := πᶜ) μ hμ hπμ
    spinCGroup.norm_toLp_toSpecialOrthogonal_apply
    spinCGroup.continuous_toSpecialOrthogonal_apply χ hχ hπχ
    spinCGroup.norm_toLp_toSpecialOrthogonal_apply
    spinCGroup.continuous_toSpecialOrthogonal_apply x (FiberProd.mk p l) a h)).trans <|
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

end InverseTwist

/-! ### The charge conjugate of a twist via inverse and tensor product bundles -/

section TensorTwist

/-- The inverse determinant character `Spinᶜ(n) → U(1)`, `g ↦ (det g)⁻¹`. -/
local notation "δ" => (spinCGroup.det (realCliffordForm n 0) hQ)⁻¹

/-- The inverse determinant character is continuous. -/
local notation "hδ" => spinCGroup.continuous_inv_det (realCliffordForm n 0) hQ

/-- Inversion of the circle, along which a principal `U(1)`-bundle extends to its inverse
(`TauCeti.PrincipalBundle.Inverse`). -/
local notation "ν" => (ContinuousMonoidHom.inv Circle : Circle →* Circle)

/-- Inversion of the circle is continuous. -/
local notation "hν" => map_continuous (ContinuousMonoidHom.inv Circle)

/-- Multiplication of the circle, along which the fibre product of two principal `U(1)`-bundles
extends to their tensor product (`TauCeti.PrincipalBundle.Tensor`). -/
local notation "τ" => (ContinuousMonoidHom.mul Circle : Circle × Circle →* Circle)

/-- Multiplication of the circle is continuous. -/
local notation "hτ" => map_continuous (ContinuousMonoidHom.mul Circle)

variable (E : X → Type) [TopologicalSpace (TotalSpace Circle E)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle Circle E] [∀ x, MulAction Circleᵐᵒᵖ (E x)] [PrincipalBundle Circle E]

/-- **Charge conjugation inverts the twisting line**: for a `Spinᶜ` structure `s` and a principal
`U(1)`-bundle `E`, the charge conjugate of the twist `s ⊗ E` is equivalent to the twist of the
charge conjugate `s.chargeConj` by the inverse bundle `E⁻¹ = E ×_{z ↦ z⁻¹} U(1)`
(`TauCeti.PrincipalBundle.Inverse`). This is `TauCeti.SpinCStructure.chargeConjTwistEquiv` for the
map `e ↦ [e, 1]`. The equivalence sends `[[(p, e), a], h]` to `[([p, 1], [e, 1]), χ a h]`
(`TauCeti.SpinCStructure.chargeConjTwistEquivInverse_toEquiv_mk`). -/
def chargeConjTwistEquivInverse (s : SpinCStructure F V n) :
    (s.twist E).chargeConj.Equiv (s.chargeConj.twist (Inverse Circle E)) :=
  s.chargeConjTwistEquiv (fun _ e ↦ Extend.inl ν hν e) (fun _ e w ↦ Extend.inl_smul ν hν e w)
    (Extend.continuous_inl E ν hν)

/-- **The equivalence `(s.twist E).chargeConj ≃ s.chargeConj.twist E⁻¹` in a frame**: it sends
`[[(p, e), a], h]` to `[([p, 1], [e, 1]), χ a h]`. -/
@[simp]
theorem chargeConjTwistEquivInverse_toEquiv_mk (s : SpinCStructure F V n) (x : X) (p : s.P x)
    (e : E x) (a h : SpinC) :
    (s.chargeConjTwistEquivInverse E).toEquiv x
        (Extend.mk χ hχ (Extend.mk μ hμ (P := FiberProd s.P E) (FiberProd.mk p e) a) h) =
      Extend.mk μ hμ (P := FiberProd (Extend s.P χ hχ) (Inverse Circle E))
        (FiberProd.mk (Extend.inl χ hχ p) (Extend.inl ν hν e)) (χ a * h) :=
  chargeConjTwistEquiv_toEquiv_mk ..

/-- **The equivalence `(s.twist E).chargeConj ≃ s.chargeConj.twist E⁻¹` at `[[(p, e), 1], 1]`**: it
sends `[[(p, e), 1], 1]` to `[([p, 1], [e, 1]), 1]`. -/
@[simp]
theorem chargeConjTwistEquivInverse_toEquiv_inl (s : SpinCStructure F V n) (x : X) (p : s.P x)
    (e : E x) :
    (s.chargeConjTwistEquivInverse E).toEquiv x
        (Extend.inl χ hχ (Extend.inl μ hμ (P := FiberProd s.P E) (FiberProd.mk p e))) =
      Extend.inl μ hμ (P := FiberProd (Extend s.P χ hχ) (Inverse Circle E))
        (FiberProd.mk (Extend.inl χ hχ p) (Extend.inl ν hν e)) :=
  chargeConjTwistEquiv_toEquiv_inl ..

/-- An equivalence out of the charge conjugate of the twist `s ⊗ E`. Extending `P ×_X E` along `μ`
and then along `χ` is extending it along `χ ∘ μ` (`TauCeti.OrthonormalFrameLift.extendCompEquiv`),
so a continuous frame-preserving map `f` from `P ×_X E` to the principal bundle of `t` that
intertwines `g` with `χ (μ g)` induces `(s.twist E).chargeConj ≃ t`, sending `[[z, a], h]` to
`f z • χ a h`. -/
private def chargeConjTwistEquivOfEquivariant (s t : SpinCStructure F V n)
    (f : ∀ x, FiberProd s.P E x → t.P x)
    (hf : ∀ x (z : FiberProd s.P E x) (g : SpinC × Circle),
      f x (op g • z) = op (χ (μ g)) • f x z)
    (hfc : Continuous fun z : TotalSpace (SpinC × Circle) (FiberProd s.P E) ↦
        (⟨z.proj, f z.proj z.snd⟩ : TotalSpace SpinC t.P))
    (hft : ∀ x (z : FiberProd s.P E x), t.toFrame ⟨x, f x z⟩ = s.toFrame ⟨x, z.fst⟩) :
    (s.twist E).chargeConj.Equiv t :=
  ((s.fiberProd Circle E).extendCompEquiv (ρ' := πᶜ) (ρ'' := πᶜ) μ hμ hπμ
      spinCGroup.norm_toLp_toSpecialOrthogonal_apply
      spinCGroup.continuous_toSpecialOrthogonal_apply χ hχ hπχ
      spinCGroup.norm_toLp_toSpecialOrthogonal_apply
      spinCGroup.continuous_toSpecialOrthogonal_apply).symm.trans
    ((s.fiberProd Circle E).extendEquivOfEquivariant (ρ' := πᶜ) (MonoidHom.comp χ μ)
      (by rw [MonoidHom.coe_comp]; exact Continuous.comp hχ hμ)
      (by rw [← MonoidHom.comp_assoc, hπχ, hπμ])
      spinCGroup.norm_toLp_toSpecialOrthogonal_apply spinCGroup.continuous_toSpecialOrthogonal_apply
      t f hf hfc hft)

/-- The equivalence `TauCeti.SpinCStructure.chargeConjTwistEquivOfEquivariant` sends `[[z, a], h]`
to `f z • χ a h`. -/
private theorem chargeConjTwistEquivOfEquivariant_toEquiv_mk (s t : SpinCStructure F V n)
    (f : ∀ x, FiberProd s.P E x → t.P x)
    (hf : ∀ x (z : FiberProd s.P E x) (g : SpinC × Circle),
      f x (op g • z) = op (χ (μ g)) • f x z)
    (hfc : Continuous fun z : TotalSpace (SpinC × Circle) (FiberProd s.P E) ↦
        (⟨z.proj, f z.proj z.snd⟩ : TotalSpace SpinC t.P))
    (hft : ∀ x (z : FiberProd s.P E x), t.toFrame ⟨x, f x z⟩ = s.toFrame ⟨x, z.fst⟩) (x : X)
    (z : FiberProd s.P E x) (a h : SpinC) :
    (chargeConjTwistEquivOfEquivariant E s t f hf hfc hft).toEquiv x
        (Extend.mk χ hχ (Extend.mk μ hμ (P := FiberProd s.P E) z a) h) =
      op (χ a * h) • f x z := by
  simp only [chargeConjTwistEquivOfEquivariant, OrthonormalFrameLift.Equiv.trans_toEquiv]
  -- `[[z, a], h]` is the image of `[z, χ a h]` under `extendCompEquiv`.
  exact (Equiv.trans_apply _ _ _).trans <| (congrArg _
    ((s.fiberProd Circle E).extendCompEquiv_symm_toEquiv_mk_mk (ρ' := πᶜ) (ρ'' := πᶜ) μ hμ hπμ
    spinCGroup.norm_toLp_toSpecialOrthogonal_apply spinCGroup.continuous_toSpecialOrthogonal_apply
    χ hχ hπχ
    spinCGroup.norm_toLp_toSpecialOrthogonal_apply
    spinCGroup.continuous_toSpecialOrthogonal_apply x z a h)).trans <|
    (s.fiberProd Circle E).extendEquivOfEquivariant_toEquiv_mk (ρ' := πᶜ) (x := x) (p := z) ..

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V] [VectorBundle ℝ F V] in
/-- The map `(p, e) ↦ [(p, [([p, 1], [e, 1]), 1]), 1]` from `P ×_X E` to the principal bundle of
the twist of `s` by `(P ×_{det⁻¹} U(1)) ⊗ E⁻¹` intertwines `(g, w)` with
`χ (g [1, w]) = g [1, (det g)⁻¹ w⁻¹]`. -/
private theorem inl_fiberProdMk_inl_fiberProdMk_smul (s : SpinCStructure F V n) {x : X}
    (z : FiberProd s.P E x) (g : SpinC × Circle) :
    Extend.inl μ hμ
        (P := FiberProd s.P (Tensor Circle s.inverseDeterminantBundle (Inverse Circle E)))
        (FiberProd.mk (FiberProd.fst (op g • z))
          (Extend.inl τ hτ (FiberProd.mk (Extend.inl δ hδ (FiberProd.fst (op g • z)))
            (Extend.inl ν hν (FiberProd.snd (op g • z)))))) =
      Extend.mk μ hμ (FiberProd.mk z.fst
          (Extend.inl τ hτ (FiberProd.mk (Extend.inl δ hδ z.fst) (Extend.inl ν hν z.snd))))
        (χ (μ g)) := by
  obtain ⟨g, w⟩ := g
  rw [FiberProd.fst_smul, FiberProd.snd_smul, unop_op, Extend.inl_smul δ hδ, Extend.inl_smul ν hν,
    ← FiberProd.op_smul_mk, Extend.inl_smul τ hτ, ← FiberProd.op_smul_mk, Extend.inl_smul μ hμ,
    Extend.smul_inl]
  simp [spinCGroup.chargeConj_mul_ofCircle]

/-- **The charge conjugate of a twist, through the tensor product**: for a `Spinᶜ` structure `s`
with principal bundle `P` and a principal `U(1)`-bundle `E`, the charge conjugate of `s ⊗ E` is
equivalent to the twist of `s` by the tensor product `(P ×_{det⁻¹} U(1)) ⊗ E⁻¹` of the inverse
determinant bundle of `s` (`TauCeti.SpinCStructure.inverseDeterminantBundle`) with the inverse of
`E` (`TauCeti.PrincipalBundle.Tensor`, `TauCeti.PrincipalBundle.Inverse`). The equivalence sends
`[[(p, e), a], h]` to `[(p, [([p, 1], [e, 1]), 1]), χ a h]`
(`TauCeti.SpinCStructure.chargeConjTwistEquivTwist_toEquiv_mk`); it is well defined because
`χ (g [1, w]) = g [1, (det g)⁻¹ w⁻¹]`. For the canonical `Spinᶜ` structure `s_ω` of an almost
Hermitian four-manifold, identifying the determinant line of `s_ω` with the anticanonical line
`K⁻¹`, which is not proved here, would turn this into Taubes's isomorphism
`conj (s_ω ⊗ E) ≃ s_ω ⊗ (K ⊗ E⁻¹)`. -/
def chargeConjTwistEquivTwist (s : SpinCStructure F V n) :
    (s.twist E).chargeConj.Equiv
      (s.twist (Tensor Circle s.inverseDeterminantBundle (Inverse Circle E))) :=
  chargeConjTwistEquivOfEquivariant E s
    (s.twist (Tensor Circle s.inverseDeterminantBundle (Inverse Circle E)))
    (fun _ z ↦ Extend.inl μ hμ
      (P := FiberProd s.P (Tensor Circle s.inverseDeterminantBundle (Inverse Circle E)))
      (FiberProd.mk (FiberProd.fst (P := s.P) (Q := E) z)
        (Extend.inl τ hτ (FiberProd.mk (Extend.inl δ hδ (FiberProd.fst (P := s.P) (Q := E) z))
          (Extend.inl ν hν (FiberProd.snd (P := s.P) (Q := E) z))))))
    (fun _ z g ↦
      (inl_fiberProdMk_inl_fiberProdMk_smul E s z g).trans (Extend.smul_inl μ hμ _ _).symm)
    ((Extend.continuous_inl
        (FiberProd s.P (Tensor Circle s.inverseDeterminantBundle (Inverse Circle E))) μ hμ).comp
      (Continuous.totalSpaceMk_fiberProdMk FiberProd.continuous_totalSpaceMk_fst
        ((Extend.continuous_inl
            (FiberProd s.inverseDeterminantBundle (Inverse Circle E)) τ hτ).comp
          (Continuous.totalSpaceMk_fiberProdMk
            ((Extend.continuous_inl s.P δ hδ).comp FiberProd.continuous_totalSpaceMk_fst)
            ((Extend.continuous_inl E ν hν).comp FiberProd.continuous_totalSpaceMk_snd)))))
    (fun x z ↦ toFrame_twist_inl s x (FiberProd.fst (P := s.P) (Q := E) z) _)

/-- **The equivalence `(s.twist E).chargeConj ≃ s.twist ((P ×_{det⁻¹} U(1)) ⊗ E⁻¹)` in a frame**:
it sends `[[(p, e), a], h]` to `[(p, [([p, 1], [e, 1]), 1]), χ a h]`. -/
@[simp]
theorem chargeConjTwistEquivTwist_toEquiv_mk (s : SpinCStructure F V n) (x : X) (p : s.P x)
    (e : E x) (a h : SpinC) :
    (s.chargeConjTwistEquivTwist E).toEquiv x
        (Extend.mk χ hχ (Extend.mk μ hμ (P := FiberProd s.P E) (FiberProd.mk p e) a) h) =
      Extend.mk μ hμ
        (P := FiberProd s.P (Tensor Circle s.inverseDeterminantBundle (Inverse Circle E)))
        (FiberProd.mk p
          (Extend.inl τ hτ (FiberProd.mk (Extend.inl δ hδ p) (Extend.inl ν hν e))))
        (χ a * h) :=
  (chargeConjTwistEquivOfEquivariant_toEquiv_mk E s _ _ _ _ _ x _ a h).trans
    (Extend.smul_inl μ hμ _ _)

/-- **The equivalence `(s.twist E).chargeConj ≃ s.twist ((P ×_{det⁻¹} U(1)) ⊗ E⁻¹)` at
`[[(p, e), 1], 1]`**: it sends `[[(p, e), 1], 1]` to `[(p, [([p, 1], [e, 1]), 1]), 1]`. -/
@[simp]
theorem chargeConjTwistEquivTwist_toEquiv_inl (s : SpinCStructure F V n) (x : X) (p : s.P x)
    (e : E x) :
    (s.chargeConjTwistEquivTwist E).toEquiv x
        (Extend.inl χ hχ (Extend.inl μ hμ (P := FiberProd s.P E) (FiberProd.mk p e))) =
      Extend.inl μ hμ
        (P := FiberProd s.P (Tensor Circle s.inverseDeterminantBundle (Inverse Circle E)))
        (FiberProd.mk p
          (Extend.inl τ hτ (FiberProd.mk (Extend.inl δ hδ p) (Extend.inl ν hν e)))) := by
  rw [Extend.inl_def χ, Extend.inl_def μ, chargeConjTwistEquivTwist_toEquiv_mk, map_one, one_mul]
  exact (Extend.inl_def μ hμ _).symm

end TensorTwist

end SpinCStructure

end TauCeti

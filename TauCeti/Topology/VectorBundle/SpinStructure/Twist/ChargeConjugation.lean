/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.SpinStructure.ChargeConjugation
public import TauCeti.Topology.VectorBundle.SpinStructure.Twist.Basic

/-!
# Charge conjugation of twisted `Spinᶜ` structures

Charge conjugation `χ : [g, z] ↦ [g, z⁻¹]` of `Spinᶜ(n)` is right multiplication by the central
circle through the inverse determinant, `χ x = x [1, (det x)⁻¹]`
(`CliffordAlgebra.spinCGroup.chargeConj_eq_mul_ofCircle_inv_det`). On principal bundles this says
that the charge conjugate `s.chargeConj` of a `Spinᶜ` structure `s` with principal bundle `P`
(`TauCeti.SpinCStructure.chargeConj`) is the twist of `s` (`TauCeti.SpinCStructure.twist`) by the
principal `U(1)`-bundle

`P ×_{det⁻¹} U(1)`,

the extension of `P` along the inverse determinant character `x ↦ (det x)⁻¹`, whose associated
line is the inverse of the determinant line of `s`. The equivalence
`TauCeti.SpinCStructure.chargeConjEquivTwist` sends `[p, h]` to `[(p, [p, 1]), χ h]`.

The same group identity, in the form `χ (x [1, z]) = x [1, (det x)⁻¹ z⁻¹]`
(`CliffordAlgebra.spinCGroup.chargeConj_mul_ofCircle`), describes the charge conjugate of a twist.
For a principal `U(1)`-bundle `E`, write `E⁻¹ = E ×_{z ↦ z⁻¹} U(1)` for the inverse bundle and
`A ⊗ B = (A ×_X B) ×_{(a, b) ↦ a b} U(1)` for the tensor product of two principal `U(1)`-bundles.
Then

* `(s.twist E).chargeConj ≃ s.chargeConj.twist E⁻¹`
  (`TauCeti.SpinCStructure.twistChargeConjEquiv`): charge conjugation inverts the twisting line;
* `(s.twist E).chargeConj ≃ s.twist ((P ×_{det⁻¹} U(1)) ⊗ E⁻¹)`
  (`TauCeti.SpinCStructure.twistChargeConjEquivTwist`): the conjugate of `s ⊗ E` is `s` twisted by
  the tensor product of the inverse determinant bundle of `s` with `E⁻¹`.

For the canonical `Spinᶜ` structure `s_ω` of an almost Hermitian four-manifold the determinant line
is the anticanonical line `K⁻¹`, so `P ×_{det⁻¹} U(1)` is the unitary frame bundle of the canonical
line `K` and the last equivalence is Taubes's isomorphism `conj (s_ω ⊗ E) ≃ s_ω ⊗ (K ⊗ E⁻¹)`,
which relates the Seiberg–Witten invariants of the labels `E` and `K ⊗ E⁻¹`. These are
equivalences of `Spinᶜ` structures on the same oriented bundle, constructed on principal bundles,
so they keep every torsion class of the twisting lines; the identity
`c₁(s.chargeConj) = -c₁(s)` (`TauCeti.SpinCStructure.firstChernClass_chargeConj`) is only the
corresponding statement about determinant classes.

## Main definitions

* `TauCeti.SpinCStructure.chargeConjEquivTwist`: `s.chargeConj ≃ s.twist (P ×_{det⁻¹} U(1))`.
* `TauCeti.SpinCStructure.twistChargeConjEquiv`: `(s.twist E).chargeConj ≃ s.chargeConj.twist E⁻¹`.
* `TauCeti.SpinCStructure.twistChargeConjEquivTwist`:
  `(s.twist E).chargeConj ≃ s.twist ((P ×_{det⁻¹} U(1)) ⊗ E⁻¹)`.

## Main results

* `TauCeti.SpinCStructure.chargeConjEquivTwist_toEquiv_mk`,
  `TauCeti.SpinCStructure.twistChargeConjEquiv_toEquiv_mk`,
  `TauCeti.SpinCStructure.twistChargeConjEquivTwist_toEquiv_mk`: the formulas of the
  equivalences in frames, with the `_toEquiv_inl` versions at the points `[p, 1]`.

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

variable {n : ℕ} [NeZero n]

/-- The proof that the standard form on `ℝⁿ`, `n ≥ 1`, is nonzero, on which `Spinᶜ(n)` depends. -/
local notation "hQ" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm n 0)

/-- Charge conjugation of `Spinᶜ(n)` as a homomorphism. -/
local notation "χ" => MonoidHom.ofClass (spinCGroup.chargeConj (realCliffordForm n 0) hQ)

/-- Charge conjugation is continuous. -/
local notation "hχ" => spinCGroup.continuous_chargeConj (realCliffordForm n 0) hQ

/-- Charge conjugation covers the identity rotation: the compatibility hypothesis of
`TauCeti.OrthonormalFrameLift.extendSpinC` for `χ`. -/
local notation "hπχ" => Eq.trans (MonoidHom.comp_assoc _ _ _)
  (congrArg (MonoidHom.comp
      (Subgroup.subtype (QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0))))
    (spinCGroup.toSpecialOrthogonal_comp_chargeConj (realCliffordForm n 0) hQ))

/-- Multiplication by the central circle, `([s, z], w) ↦ [s, z w]`. -/
local notation "μ" => spinCGroup.mulCircle (realCliffordForm n 0) hQ

/-- Multiplication by the central circle is continuous. -/
local notation "hμ" => spinCGroup.continuous_mulCircle (realCliffordForm n 0) hQ

/-- Multiplication by the central circle covers the rotation of the first factor: the compatibility
hypothesis of `TauCeti.OrthonormalFrameLift.extend` for `μ`, as in
`TauCeti.SpinCStructure.twist`. -/
local notation "hπμ" => Eq.trans (MonoidHom.comp_assoc _ _ _)
  (Eq.trans (congrArg (MonoidHom.comp
      (Subgroup.subtype (QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0))))
    (spinCGroup.toSpecialOrthogonal_comp_mulCircle (realCliffordForm n 0) hQ))
    (Eq.symm (MonoidHom.comp_assoc _ _ _)))

/-- The composite `χ ∘ μ` covers the rotation of the first factor. -/
local notation "hπχμ" => Eq.trans (Eq.symm (MonoidHom.comp_assoc _ _ _))
  (Eq.trans (congrArg (fun f ↦ MonoidHom.comp f μ) hπχ) hπμ)

/-- The inverse determinant character `x ↦ (det x)⁻¹` of `Spinᶜ(n)`, `[s, z] ↦ z⁻²`, as a
homomorphism. -/
local notation "δ" => (ContinuousMonoidHom.comp (ContinuousMonoidHom.inv Circle)
  (spinCGroup.detContinuousMonoidHom (realCliffordForm n 0) hQ) :
    spinCGroup (realCliffordForm n 0) hQ →* Circle)

/-- The inverse determinant character is continuous. -/
local notation "hδ" => map_continuous (ContinuousMonoidHom.comp
  (ContinuousMonoidHom.inv Circle) (spinCGroup.detContinuousMonoidHom (realCliffordForm n 0) hQ))

/-- Inversion of the circle, along which a principal `U(1)`-bundle extends to its inverse. -/
local notation "ν" => (ContinuousMonoidHom.inv Circle : Circle →* Circle)

/-- Inversion of the circle is continuous. -/
local notation "hν" => map_continuous (ContinuousMonoidHom.inv Circle)

/-- Multiplication of the circle, along which the fibre product of two principal `U(1)`-bundles
extends to their tensor product. -/
local notation "τ" => (ContinuousMonoidHom.mul Circle : Circle × Circle →* Circle)

/-- Multiplication of the circle is continuous. -/
local notation "hτ" => map_continuous (ContinuousMonoidHom.mul Circle)

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : X → Type} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]

/-! ### Charge conjugation is twisting by the inverse determinant -/

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V] [VectorBundle ℝ F V] in
/-- The map `p ↦ [(p, [p, 1]), 1]` from the principal bundle of `s` to that of its twist by
`P ×_{det⁻¹} U(1)` intertwines `g` with `χ g`, since `χ g = g [1, (det g)⁻¹]`. -/
private theorem inl_fiberProdMk_inl_smul (s : SpinCStructure F V n) {x : X} (p : s.P x)
    (g : spinCGroup (realCliffordForm n 0) hQ) :
    Extend.inl μ hμ (P := FiberProd s.P (Extend s.P δ hδ))
        (FiberProd.mk (op g • p) (Extend.inl δ hδ (op g • p))) =
      Extend.mk μ hμ (FiberProd.mk p (Extend.inl δ hδ p)) (χ g) := by
  rw [Extend.inl_smul δ hδ p g, ← FiberProd.op_smul_mk, Extend.inl_smul μ hμ, Extend.smul_inl]
  simp [spinCGroup.chargeConj_eq_mul_ofCircle_inv_det]

/-- **Charge conjugation is twisting by the inverse determinant bundle**: for a `Spinᶜ` structure
`s` with principal bundle `P`, the charge conjugate `s.chargeConj` is equivalent to the twist of `s`
by the principal `U(1)`-bundle `P ×_{det⁻¹} U(1)`, whose associated line is the inverse of the
determinant line of `s`. The equivalence sends `[p, h]` to `[(p, [p, 1]), h]`
(`TauCeti.SpinCStructure.chargeConjEquivTwist_toEquiv_mk`); it is well defined because
`χ g = g [1, (det g)⁻¹]`. -/
def chargeConjEquivTwist (s : SpinCStructure F V n) :
    s.chargeConj.Equiv (s.twist (Extend s.P δ hδ)) :=
  s.extendSpinCEquivOfEquivariant χ hχ hπχ (s.twist (Extend s.P δ hδ))
    (fun _ p ↦ Extend.inl μ hμ (P := FiberProd s.P (Extend s.P δ hδ))
      (FiberProd.mk p (Extend.inl δ hδ p)))
    (fun _ p g ↦ (inl_fiberProdMk_inl_smul s p g).trans (Extend.smul_inl μ hμ _ _).symm)
    ((Extend.continuous_inl (FiberProd s.P (Extend s.P δ hδ)) μ hμ).comp
      (Continuous.totalSpaceMk_fiberProdMk continuous_id (Extend.continuous_inl s.P δ hδ)))
    (fun x p ↦ toFrame_twist_inl s x p _)

/-- **The equivalence `s.chargeConj ≃ s.twist (P ×_{det⁻¹} U(1))` in a frame**: it sends `[p, h]` to
`[(p, [p, 1]), h]`. -/
@[simp]
theorem chargeConjEquivTwist_toEquiv_mk (s : SpinCStructure F V n) (x : X) (p : s.P x)
    (h : spinCGroup (realCliffordForm n 0) hQ) :
    s.chargeConjEquivTwist.toEquiv x (Extend.mk χ hχ p h) =
      Extend.mk μ hμ (P := FiberProd s.P (Extend s.P δ hδ))
        (FiberProd.mk p (Extend.inl δ hδ p)) h :=
  (s.extendSpinCEquivOfEquivariant_toEquiv_mk χ hχ hπχ _ _ _ _ _ x p h).trans
    (Extend.smul_inl μ hμ _ h)

/-- **The equivalence `s.chargeConj ≃ s.twist (P ×_{det⁻¹} U(1))` at `[p, 1]`**: it sends `[p, 1]`
to `[(p, [p, 1]), 1]`. -/
@[simp]
theorem chargeConjEquivTwist_toEquiv_inl (s : SpinCStructure F V n) (x : X) (p : s.P x) :
    s.chargeConjEquivTwist.toEquiv x (Extend.inl χ hχ p) =
      Extend.inl μ hμ (P := FiberProd s.P (Extend s.P δ hδ))
        (FiberProd.mk p (Extend.inl δ hδ p)) :=
  s.extendSpinCEquivOfEquivariant_toEquiv_inl χ hχ hπχ _ _ _ _ _ x p

/-! ### The charge conjugate of a twist -/

variable (E : X → Type) [TopologicalSpace (TotalSpace Circle E)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle Circle E] [∀ x, MulAction Circleᵐᵒᵖ (E x)] [PrincipalBundle Circle E]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V] [VectorBundle ℝ F V] in
/-- The map `(p, e) ↦ [([p, 1], [e, 1]), 1]` from `P ×_X E` to the principal bundle of the twist of
`s.chargeConj` by `E⁻¹` intertwines `(g, w)` with `χ (g [1, w]) = χ g [1, w⁻¹]`. -/
private theorem inl_fiberProdMk_inl_inl_smul (s : SpinCStructure F V n) {x : X}
    (z : FiberProd s.P E x) (g : spinCGroup (realCliffordForm n 0) hQ × Circle) :
    Extend.inl μ hμ (P := FiberProd (Extend s.P χ hχ) (Extend E ν hν))
        (FiberProd.mk (Extend.inl χ hχ (FiberProd.fst (op g • z)))
          (Extend.inl ν hν (FiberProd.snd (op g • z)))) =
      Extend.mk μ hμ (FiberProd.mk (Extend.inl χ hχ z.fst) (Extend.inl ν hν z.snd)) (χ (μ g)) := by
  obtain ⟨g, w⟩ := g
  rw [FiberProd.fst_smul, FiberProd.snd_smul, unop_op, Extend.inl_smul χ hχ, Extend.inl_smul ν hν,
    ← FiberProd.op_smul_mk, Extend.inl_smul μ hμ, Extend.smul_inl]
  simp

/-- **Charge conjugation inverts the twisting line**: for a `Spinᶜ` structure `s` and a principal
`U(1)`-bundle `E`, the charge conjugate of the twist `s ⊗ E` is equivalent to the twist of the
charge conjugate `s.chargeConj` by the inverse bundle `E⁻¹ = E ×_{z ↦ z⁻¹} U(1)`. The equivalence
sends `[[(p, e), a], h]` to `[([p, 1], [e, 1]), χ a h]`
(`TauCeti.SpinCStructure.twistChargeConjEquiv_toEquiv_mk`); it is well defined because
`χ (g [1, w]) = χ g [1, w⁻¹]`. -/
def twistChargeConjEquiv (s : SpinCStructure F V n) :
    (s.twist E).chargeConj.Equiv (s.chargeConj.twist (Extend E ν hν)) :=
  ((s.fiberProd Circle E).extendCompEquiv μ hμ hπμ spinCGroup.norm_toLp_toSpecialOrthogonal_apply
      spinCGroup.continuous_toSpecialOrthogonal_apply χ hχ hπχ
      spinCGroup.norm_toLp_toSpecialOrthogonal_apply
      spinCGroup.continuous_toSpecialOrthogonal_apply).symm.trans
    ((s.fiberProd Circle E).extendEquivOfEquivariant (MonoidHom.comp χ μ)
      (show Continuous (⇑χ ∘ ⇑μ) from Continuous.comp hχ hμ) hπχμ
      spinCGroup.norm_toLp_toSpecialOrthogonal_apply spinCGroup.continuous_toSpecialOrthogonal_apply
      (s.chargeConj.twist (Extend E ν hν))
      (fun _ z ↦ Extend.inl μ hμ (P := FiberProd (Extend s.P χ hχ) (Extend E ν hν))
        (FiberProd.mk (Extend.inl χ hχ (FiberProd.fst (P := s.P) (Q := E) z))
          (Extend.inl ν hν (FiberProd.snd (P := s.P) (Q := E) z))))
      (fun _ z g ↦ (inl_fiberProdMk_inl_inl_smul E s z g).trans (Extend.smul_inl μ hμ _ _).symm)
      ((Extend.continuous_inl (FiberProd (Extend s.P χ hχ) (Extend E ν hν)) μ hμ).comp
        (Continuous.totalSpaceMk_fiberProdMk
          ((Extend.continuous_inl s.P χ hχ).comp FiberProd.continuous_totalSpaceMk_fst)
          ((Extend.continuous_inl E ν hν).comp FiberProd.continuous_totalSpaceMk_snd)))
      (fun x z ↦ (toFrame_twist_inl s.chargeConj x _ _).trans
        (toFrame_chargeConj_inl s x (FiberProd.fst (P := s.P) (Q := E) z))))

/-- **The equivalence `(s.twist E).chargeConj ≃ s.chargeConj.twist E⁻¹` in a frame**: it sends
`[[(p, e), a], h]` to `[([p, 1], [e, 1]), χ a h]`. -/
@[simp]
theorem twistChargeConjEquiv_toEquiv_mk (s : SpinCStructure F V n) (x : X) (p : s.P x) (e : E x)
    (a h : spinCGroup (realCliffordForm n 0) hQ) :
    (s.twistChargeConjEquiv E).toEquiv x
        (Extend.mk χ hχ (Extend.mk μ hμ (P := FiberProd s.P E) (FiberProd.mk p e) a) h) =
      Extend.mk μ hμ (P := FiberProd (Extend s.P χ hχ) (Extend E ν hν))
        (FiberProd.mk (Extend.inl χ hχ p) (Extend.inl ν hν e)) (χ a * h) := by
  simp only [twistChargeConjEquiv, OrthonormalFrameLift.Equiv.trans_toEquiv,
    OrthonormalFrameLift.Equiv.symm_toEquiv]
  -- `[[(p, e), a], h] = [[(p, e), 1], χ a h]` is the image of `[(p, e), χ a h]` under
  -- `extendCompEquiv`.
  have hcomp := (Equiv.symm_apply_eq _).2 (((s.fiberProd Circle E).extendCompEquiv_toEquiv_mk μ hμ
    hπμ spinCGroup.norm_toLp_toSpecialOrthogonal_apply
    spinCGroup.continuous_toSpecialOrthogonal_apply
    χ hχ hπχ spinCGroup.norm_toLp_toSpecialOrthogonal_apply
    spinCGroup.continuous_toSpecialOrthogonal_apply x (FiberProd.mk p e) (χ a * h)).trans
      (Extend.mk_mk μ hμ χ hχ (FiberProd.mk p e) a h).symm).symm
  exact (Equiv.trans_apply _ _ _).trans <| (congrArg _ hcomp).trans <|
    ((s.fiberProd Circle E).extendEquivOfEquivariant_toEquiv_mk (x := x) (p := FiberProd.mk p e)
      ..).trans (Extend.smul_inl μ hμ _ _)

/-- **The equivalence `(s.twist E).chargeConj ≃ s.chargeConj.twist E⁻¹` at `[[(p, e), 1], 1]`**: it
sends `[[(p, e), 1], 1]` to `[([p, 1], [e, 1]), 1]`. -/
@[simp]
theorem twistChargeConjEquiv_toEquiv_inl (s : SpinCStructure F V n) (x : X) (p : s.P x) (e : E x) :
    (s.twistChargeConjEquiv E).toEquiv x
        (Extend.inl χ hχ (Extend.inl μ hμ (P := FiberProd s.P E) (FiberProd.mk p e))) =
      Extend.inl μ hμ (P := FiberProd (Extend s.P χ hχ) (Extend E ν hν))
        (FiberProd.mk (Extend.inl χ hχ p) (Extend.inl ν hν e)) := by
  rw [Extend.inl_def χ, Extend.inl_def μ, twistChargeConjEquiv_toEquiv_mk, map_one, one_mul]
  exact (Extend.inl_def μ hμ _).symm

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V] [VectorBundle ℝ F V] in
/-- The map `(p, e) ↦ [(p, [([p, 1], [e, 1]), 1]), 1]` from `P ×_X E` to the principal bundle of
the twist of `s` by `(P ×_{det⁻¹} U(1)) ⊗ E⁻¹` intertwines `(g, w)` with
`χ (g [1, w]) = g [1, (det g)⁻¹ w⁻¹]`. -/
private theorem inl_fiberProdMk_inl_fiberProdMk_smul (s : SpinCStructure F V n) {x : X}
    (z : FiberProd s.P E x) (g : spinCGroup (realCliffordForm n 0) hQ × Circle) :
    Extend.inl μ hμ
        (P := FiberProd s.P (Extend (FiberProd (Extend s.P δ hδ) (Extend E ν hν)) τ hτ))
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

/-- **The charge conjugate of a twist** (Taubes): for a `Spinᶜ` structure `s` with principal bundle
`P` and a principal `U(1)`-bundle `E`, the charge conjugate of `s ⊗ E` is equivalent to the twist
of `s` by the tensor product `(P ×_{det⁻¹} U(1)) ⊗ E⁻¹` of the inverse determinant bundle of `s`
with the inverse of `E`. The equivalence sends `[[(p, e), a], h]` to
`[(p, [([p, 1], [e, 1]), 1]), χ a h]`
(`TauCeti.SpinCStructure.twistChargeConjEquivTwist_toEquiv_mk`); it is well defined because
`χ (g [1, w]) = g [1, (det g)⁻¹ w⁻¹]`. The determinant line of the canonical `Spinᶜ` structure
`s_ω` of an almost Hermitian four-manifold is the anticanonical line `K⁻¹`, so for `s = s_ω` the
inverse determinant bundle is the unitary frame bundle of the canonical line `K`, and this is the
isomorphism `conj (s_ω ⊗ E) ≃ s_ω ⊗ (K ⊗ E⁻¹)`. -/
def twistChargeConjEquivTwist (s : SpinCStructure F V n) :
    (s.twist E).chargeConj.Equiv
      (s.twist (Extend (FiberProd (Extend s.P δ hδ) (Extend E ν hν)) τ hτ)) :=
  ((s.fiberProd Circle E).extendCompEquiv μ hμ hπμ spinCGroup.norm_toLp_toSpecialOrthogonal_apply
      spinCGroup.continuous_toSpecialOrthogonal_apply χ hχ hπχ
      spinCGroup.norm_toLp_toSpecialOrthogonal_apply
      spinCGroup.continuous_toSpecialOrthogonal_apply).symm.trans
    ((s.fiberProd Circle E).extendEquivOfEquivariant (MonoidHom.comp χ μ)
      (show Continuous (⇑χ ∘ ⇑μ) from Continuous.comp hχ hμ) hπχμ
      spinCGroup.norm_toLp_toSpecialOrthogonal_apply spinCGroup.continuous_toSpecialOrthogonal_apply
      (s.twist (Extend (FiberProd (Extend s.P δ hδ) (Extend E ν hν)) τ hτ))
      (fun _ z ↦ Extend.inl μ hμ
        (P := FiberProd s.P (Extend (FiberProd (Extend s.P δ hδ) (Extend E ν hν)) τ hτ))
        (FiberProd.mk (FiberProd.fst (P := s.P) (Q := E) z)
          (Extend.inl τ hτ (FiberProd.mk (Extend.inl δ hδ (FiberProd.fst (P := s.P) (Q := E) z))
            (Extend.inl ν hν (FiberProd.snd (P := s.P) (Q := E) z))))))
      (fun _ z g ↦
        (inl_fiberProdMk_inl_fiberProdMk_smul E s z g).trans (Extend.smul_inl μ hμ _ _).symm)
      ((Extend.continuous_inl
          (FiberProd s.P (Extend (FiberProd (Extend s.P δ hδ) (Extend E ν hν)) τ hτ)) μ hμ).comp
        (Continuous.totalSpaceMk_fiberProdMk FiberProd.continuous_totalSpaceMk_fst
          ((Extend.continuous_inl (FiberProd (Extend s.P δ hδ) (Extend E ν hν)) τ hτ).comp
            (Continuous.totalSpaceMk_fiberProdMk
              ((Extend.continuous_inl s.P δ hδ).comp FiberProd.continuous_totalSpaceMk_fst)
              ((Extend.continuous_inl E ν hν).comp FiberProd.continuous_totalSpaceMk_snd)))))
      (fun x z ↦ toFrame_twist_inl s x (FiberProd.fst (P := s.P) (Q := E) z) _))

/-- **The equivalence `(s.twist E).chargeConj ≃ s.twist ((P ×_{det⁻¹} U(1)) ⊗ E⁻¹)` in a frame**:
it sends `[[(p, e), a], h]` to `[(p, [([p, 1], [e, 1]), 1]), χ a h]`. -/
@[simp]
theorem twistChargeConjEquivTwist_toEquiv_mk (s : SpinCStructure F V n) (x : X) (p : s.P x)
    (e : E x) (a h : spinCGroup (realCliffordForm n 0) hQ) :
    (s.twistChargeConjEquivTwist E).toEquiv x
        (Extend.mk χ hχ (Extend.mk μ hμ (P := FiberProd s.P E) (FiberProd.mk p e) a) h) =
      Extend.mk μ hμ
        (P := FiberProd s.P (Extend (FiberProd (Extend s.P δ hδ) (Extend E ν hν)) τ hτ))
        (FiberProd.mk p
          (Extend.inl τ hτ (FiberProd.mk (Extend.inl δ hδ p) (Extend.inl ν hν e))))
        (χ a * h) := by
  simp only [twistChargeConjEquivTwist, OrthonormalFrameLift.Equiv.trans_toEquiv,
    OrthonormalFrameLift.Equiv.symm_toEquiv]
  -- `[[(p, e), a], h] = [[(p, e), 1], χ a h]` is the image of `[(p, e), χ a h]` under
  -- `extendCompEquiv`.
  have hcomp := (Equiv.symm_apply_eq _).2 (((s.fiberProd Circle E).extendCompEquiv_toEquiv_mk μ hμ
    hπμ spinCGroup.norm_toLp_toSpecialOrthogonal_apply
    spinCGroup.continuous_toSpecialOrthogonal_apply
    χ hχ hπχ spinCGroup.norm_toLp_toSpecialOrthogonal_apply
    spinCGroup.continuous_toSpecialOrthogonal_apply x (FiberProd.mk p e) (χ a * h)).trans
      (Extend.mk_mk μ hμ χ hχ (FiberProd.mk p e) a h).symm).symm
  exact (Equiv.trans_apply _ _ _).trans <| (congrArg _ hcomp).trans <|
    ((s.fiberProd Circle E).extendEquivOfEquivariant_toEquiv_mk (x := x) (p := FiberProd.mk p e)
      ..).trans (Extend.smul_inl μ hμ _ _)

/-- **The equivalence `(s.twist E).chargeConj ≃ s.twist ((P ×_{det⁻¹} U(1)) ⊗ E⁻¹)` at
`[[(p, e), 1], 1]`**: it sends `[[(p, e), 1], 1]` to `[(p, [([p, 1], [e, 1]), 1]), 1]`. -/
@[simp]
theorem twistChargeConjEquivTwist_toEquiv_inl (s : SpinCStructure F V n) (x : X) (p : s.P x)
    (e : E x) :
    (s.twistChargeConjEquivTwist E).toEquiv x
        (Extend.inl χ hχ (Extend.inl μ hμ (P := FiberProd s.P E) (FiberProd.mk p e))) =
      Extend.inl μ hμ
        (P := FiberProd s.P (Extend (FiberProd (Extend s.P δ hδ) (Extend E ν hν)) τ hτ))
        (FiberProd.mk p
          (Extend.inl τ hτ (FiberProd.mk (Extend.inl δ hδ p) (Extend.inl ν hν e)))) := by
  rw [Extend.inl_def χ, Extend.inl_def μ, twistChargeConjEquivTwist_toEquiv_mk, map_one, one_mul]
  exact (Extend.inl_def μ hμ _).symm

end SpinCStructure

end TauCeti

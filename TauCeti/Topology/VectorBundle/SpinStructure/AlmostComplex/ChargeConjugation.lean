/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.SpinStructure.AlmostComplex.Basic
public import TauCeti.Topology.VectorBundle.SpinStructure.Twist.ChargeConjugation

/-!
# Charge conjugation of the canonical `Spinᶜ` structure and the canonical line

Let `E → X` be a rank-four real vector bundle with fibre inner products and a continuous fibrewise
orthogonal complex structure `J`, with unitary frame bundle `P`
(`TauCeti.OrthonormalFrameBundle.unitaryFrameLift`) and canonical `Spinᶜ` structure
`s_ω = P ×_σ Spinᶜ(4)` (`TauCeti.OrthonormalFrameBundle.canonicalSpinCStructure`), for the lift
`σ : U(ℝ⁴, J₀) → Spinᶜ(4)` of a unitary frame `e` of the model complex structure `J₀`. The
determinant character of `σ` is the complex determinant `det_ℂ` of the unitary matrix in the frame
`e` (`TauCeti.det_unitarySpinCLift`), so the determinant line of `s_ω` is `P ×_{det_ℂ} ℂ`, the
anticanonical line `K⁻¹ = Λ²_ℂ (E, J)`
(`TauCeti.OrthonormalFrameBundle.canonicalDeterminantLineEquivDetBundle`).

The **canonical circle bundle** `TauCeti.OrthonormalFrameBundle.canonicalBundle` is the
extension `P ×_{det_ℂ⁻¹} U(1)` of the unitary frames along the inverse complex determinant
(`TauCeti.canonicalLineCharacter`, defined with the lift `σ` in
`TauCeti.Topology.Algebra.CliffordAlgebra.Spin.UnitaryLift`). Its transition functions are
`det_ℂ(g_αβ)⁻¹`, the inverses of those of `Λ²_ℂ (E, J)`: it is the principal `U(1)`-bundle of
the canonical line `K = (Λ²_ℂ (E, J))*`, for an almost Hermitian four-manifold with `E` its tangent
bundle the line `K = Λ^{2,0}`, described through the unitary frames. Its associated line is not
compared here with the dual of `Λ²_ℂ (E, J)` as a vector bundle. This file identifies the bundles
of the charge conjugation theorems of
`TauCeti.Topology.VectorBundle.SpinStructure.Twist.ChargeConjugation` for `s_ω`:

* **`L⁻¹ ≃ K`.** The inverse determinant bundle `P_ω ×_{det⁻¹} U(1)` of `s_ω`
  (`TauCeti.SpinCStructure.inverseDeterminantBundle`) is equivalent to the canonical circle
  bundle (`TauCeti.OrthonormalFrameBundle.inverseDeterminantBundleEquivCanonicalBundle`), by
  `[[p, h], w] ↦ [p, (det h)⁻¹ w]`. Extending first along `σ` and then along `det⁻¹` is extending
  along `det⁻¹ ∘ σ = det_ℂ⁻¹`.
* **`conj s_ω ≃ s_ω ⊗ K`** (`TauCeti.OrthonormalFrameBundle.chargeConjEquivTwistCanonicalBundle`),
  from `conj s ≃ s ⊗ L⁻¹` (`TauCeti.SpinCStructure.chargeConjEquivTwist`).
* **`conj (s_ω ⊗ E) ≃ s_ω ⊗ (K ⊗ E⁻¹)`** for every principal `U(1)`-bundle `E`
  (`TauCeti.OrthonormalFrameBundle.chargeConjTwistEquivTwistCanonicalBundle`), from
  `conj (s ⊗ E) ≃ s ⊗ (L⁻¹ ⊗ E⁻¹)` (`TauCeti.SpinCStructure.chargeConjTwistEquivTwist`) and the
  functoriality of the tensor product (`TauCeti.PrincipalBundle.Equiv.extend`).

The last is Taubes's isomorphism `conj (s_ω ⊗ E) ≃ s_ω ⊗ (K ⊗ E⁻¹)`, which carries the
Seiberg–Witten equations of the label `E` to those of the label `K ⊗ E⁻¹`. It is an equivalence of
`Spinᶜ` structures over the frame bundle, constructed through the `U(2)` and `Spinᶜ`
representations, so it keeps every two-torsion label: no class is replaced by its first Chern
class. In frames it sends `[[(p, e), 1], 1]` to `[(p, [([p, 1], [e, 1]), 1]), 1]` for a unitary
frame `p` (`TauCeti.OrthonormalFrameBundle.chargeConjTwistEquivTwistCanonicalBundle_toEquiv_inl`).

## Main definitions

* `TauCeti.OrthonormalFrameBundle.canonicalBundle`: the circle bundle `P ×_{det_ℂ⁻¹} U(1)` of
  the canonical line `K`.
* `TauCeti.OrthonormalFrameBundle.inverseDeterminantBundleEquivCanonicalBundle`: the equivalence
  of the inverse determinant bundle of `s_ω` with `K`.
* `TauCeti.OrthonormalFrameBundle.chargeConjEquivTwistCanonicalBundle`: `conj s_ω ≃ s_ω ⊗ K`.
* `TauCeti.OrthonormalFrameBundle.chargeConjTwistEquivTwistCanonicalBundle`:
  `conj (s_ω ⊗ E) ≃ s_ω ⊗ (K ⊗ E⁻¹)`.

## Main results

* `TauCeti.OrthonormalFrameBundle.inverseDeterminantBundleEquivCanonicalBundle_toEquiv_mk`,
  `TauCeti.OrthonormalFrameBundle.chargeConjEquivTwistCanonicalBundle_toEquiv_mk` and
  `TauCeti.OrthonormalFrameBundle.chargeConjTwistEquivTwistCanonicalBundle_toEquiv_mk`: the three
  equivalences in frames, with their `_toEquiv_inl` versions.

## References

* C. H. Taubes, *GR = SW: counting curves and connections*, J. Differential Geom. 52 (1999),
  453–609.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.4.
* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
-/

public section

noncomputable section

open Bundle CliffordAlgebra Module MulOpposite TauCeti.PrincipalBundle

namespace TauCeti

namespace OrthonormalFrameBundle

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : X → Type} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E] {J : ∀ x, E x ≃ₗᵢ[ℝ] E x}
  {J₀ : unitary (EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))}
  (hJ : Continuous fun v : TotalSpace F E ↦ (⟨v.proj, J v.proj v.snd⟩ : TotalSpace F E))
  (hJ₂ : ∀ x v, J x (J x v) = -v)
  (hJ₀ : ∀ v, (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    ((J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) v) = -v)
  (hF : finrank ℝ F = 4) (e : OrthonormalBasis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4)))
  (h₀ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 0) = e 1)
  (h₂ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 2) = e 3)

/-- The proof that the standard form on `ℝ⁴` is nonzero, on which `Spinᶜ(4)` depends. -/
local notation "hQ" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm 4 0)

/-- The group `Spinᶜ(4)`. -/
local notation "SpinC" => spinCGroup (realCliffordForm 4 0) hQ

/-- The canonical lift `σ : U(ℝ⁴, J₀) → Spinᶜ(4)`. -/
local notation "σ" => unitarySpinCLift hJ₀ e h₀ h₂

/-- The canonical lift is continuous. -/
local notation "hσ" => continuous_unitarySpinCLift hJ₀ e h₀ h₂

/-- The inverse determinant character `Spinᶜ(4) → U(1)`, `g ↦ (det g)⁻¹`. -/
local notation "δ" => (spinCGroup.det (realCliffordForm 4 0) hQ)⁻¹

/-- The inverse determinant character is continuous. -/
local notation "hδ" => spinCGroup.continuous_inv_det (realCliffordForm 4 0) hQ

/-- The inverse complex determinant `κ : U(ℝ⁴, J₀) → U(1)`
(`TauCeti.canonicalLineCharacter`). -/
local notation "κ" => ContinuousMonoidHom.toMonoidHom (canonicalLineCharacter hJ₀ e h₀ h₂)

/-- The inverse complex determinant is continuous. -/
local notation "hκ" => map_continuous (canonicalLineCharacter hJ₀ e h₀ h₂)

/-- Charge conjugation of `Spinᶜ(4)` as a homomorphism. -/
local notation "χ" => MonoidHom.ofClass (spinCGroup.chargeConj (realCliffordForm 4 0) hQ)

/-- Charge conjugation is continuous. -/
local notation "hχ" => spinCGroup.continuous_chargeConj (realCliffordForm 4 0) hQ

/-- Multiplication by the central circle, `μ (a, w) = a [1, w]`. -/
local notation "μ" => spinCGroup.mulCircle (realCliffordForm 4 0) hQ

/-- Multiplication by the central circle is continuous. -/
local notation "hμ" => spinCGroup.continuous_mulCircle (realCliffordForm 4 0) hQ

/-- Inversion of the circle, along which a principal `U(1)`-bundle extends to its inverse. -/
local notation "ν" => (ContinuousMonoidHom.inv Circle : Circle →* Circle)

/-- Inversion of the circle is continuous. -/
local notation "hν" => map_continuous (ContinuousMonoidHom.inv Circle)

/-- Multiplication of the circle, along which the fibre product of two principal `U(1)`-bundles
extends to their tensor product. -/
local notation "τ" => (ContinuousMonoidHom.mul Circle : Circle × Circle →* Circle)

/-- Multiplication of the circle is continuous. -/
local notation "hτ" => map_continuous (ContinuousMonoidHom.mul Circle)

/-! ### The canonical circle bundle -/

/-- The **canonical circle bundle** of a rank-four bundle with an orthogonal complex structure
`J`: the extension `P ×_{det_ℂ⁻¹} U(1)` of the unitary frame bundle `P` along the inverse complex
determinant, read in the unitary frame `e` of the model. Its transition functions are
`det_ℂ(g_αβ)⁻¹`, the inverses of those of the anticanonical line `Λ²_ℂ (E, J) = P ×_{det_ℂ} ℂ`
(`TauCeti.OrthonormalFrameBundle.unitaryFrameDetEquiv`): it is the principal `U(1)`-bundle of the
canonical line `K`, described by its transition functions. -/
abbrev canonicalBundle : X → Type :=
  Extend (unitaryFrameLift hJ hJ₂ hJ₀ hF).P κ hκ

/-- **The inverse determinant bundle of the canonical `Spinᶜ` structure is the canonical circle
bundle**: `P_ω ×_{det⁻¹} U(1) ≃ P ×_{det_ℂ⁻¹} U(1)`, by `[[p, h], w] ↦ [p, (det h)⁻¹ w]`. This is
`L⁻¹ ≃ K` for the determinant line `L = K⁻¹` of `s_ω`: extending first along `σ` and then along
`det⁻¹` is extending along `det⁻¹ ∘ σ`, which is the character `det_ℂ⁻¹` of `K`
(`TauCeti.inv_det_comp_unitarySpinCLift`). -/
def inverseDeterminantBundleEquivCanonicalBundle :
    PrincipalBundle.Equiv Circle
      (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).inverseDeterminantBundle
      (canonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂) :=
  (Extend.compPrincipalEquiv σ hσ δ hδ).trans
    (Extend.congrPrincipalEquiv (inv_det_comp_unitarySpinCLift hJ₀ e h₀ h₂) ((hδ).comp hσ) hκ)

/-- **The equivalence `L⁻¹ ≃ K` in a frame**: it sends `[[p, h], w]` to `[p, (det h)⁻¹ w]`. -/
@[simp]
theorem inverseDeterminantBundleEquivCanonicalBundle_toEquiv_mk {x : X}
    (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x) (h : SpinC) (w : Circle) :
    (inverseDeterminantBundleEquivCanonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂).toEquiv x
        (Extend.mk δ hδ (Extend.mk σ hσ p h) w) =
      Extend.mk κ hκ p (δ h * w) := by
  simp only [inverseDeterminantBundleEquivCanonicalBundle, PrincipalBundle.Equiv.trans_toEquiv,
    Extend.compPrincipalEquiv_toEquiv, Extend.congrPrincipalEquiv_toEquiv]
  exact (congrArg
    (Extend.congrEquiv (inv_det_comp_unitarySpinCLift hJ₀ e h₀ h₂) ((hδ).comp hσ) hκ x)
    (Extend.compEquiv_mk σ hσ δ hδ p h w)).trans (Extend.congrEquiv_mk _ _ _ p _)

/-- **The equivalence `L⁻¹ ≃ K` at `[[p, 1], 1]`**: it sends `[[p, 1], 1]` to `[p, 1]`. -/
@[simp]
theorem inverseDeterminantBundleEquivCanonicalBundle_toEquiv_inl {x : X}
    (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x) :
    (inverseDeterminantBundleEquivCanonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂).toEquiv x
        (Extend.inl δ hδ (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p)) =
      Extend.inl κ hκ p := by
  simp only [inverseDeterminantBundleEquivCanonicalBundle, PrincipalBundle.Equiv.trans_toEquiv,
    Extend.compPrincipalEquiv_toEquiv, Extend.congrPrincipalEquiv_toEquiv]
  exact (congrArg
    (Extend.congrEquiv (inv_det_comp_unitarySpinCLift hJ₀ e h₀ h₂) ((hδ).comp hσ) hκ x)
    (Extend.compEquiv_inl σ hσ δ hδ p)).trans (Extend.congrEquiv_inl _ _ _ p)

/-! ### Charge conjugation of the canonical `Spinᶜ` structure -/

/-- **The charge conjugate of the canonical `Spinᶜ` structure is its twist by the canonical
line**: `conj s_ω ≃ s_ω ⊗ K`. It is `conj s ≃ s ⊗ L⁻¹`
(`TauCeti.SpinCStructure.chargeConjEquivTwist`) followed by `L⁻¹ ≃ K`
(`TauCeti.OrthonormalFrameBundle.inverseDeterminantBundleEquivCanonicalBundle`), and sends
`[[p, 1], 1]` to `[([p, 1], [p, 1]), 1]` for a unitary frame `p`. -/
def chargeConjEquivTwistCanonicalBundle :
    (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).chargeConj.Equiv
      ((canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).twist
        (canonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂)) :=
  (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).chargeConjEquivTwist.trans
    (SpinCStructure.twistEquiv (OrthonormalFrameLift.Equiv.refl _)
      (inverseDeterminantBundleEquivCanonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂))

/-- **The equivalence `conj s_ω ≃ s_ω ⊗ K` at `[[p, 1], 1]`**: it sends `[[p, 1], 1]` to
`[([p, 1], [p, 1]), 1]`. -/
@[simp]
theorem chargeConjEquivTwistCanonicalBundle_toEquiv_inl {x : X}
    (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x) :
    (chargeConjEquivTwistCanonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂).toEquiv x
        (Extend.inl χ hχ (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p)) =
      Extend.inl μ hμ
        (P := FiberProd (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).P
          (canonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂))
        (FiberProd.mk (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p)
          (Extend.inl κ hκ p)) := by
  have hdef (a : (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).chargeConj.P x) :
      (chargeConjEquivTwistCanonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂).toEquiv x a =
        (SpinCStructure.twistEquiv (OrthonormalFrameLift.Equiv.refl _)
          (inverseDeterminantBundleEquivCanonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂)).toEquiv x
          ((canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).chargeConjEquivTwist.toEquiv x a) :=
    (congrFun (congrArg DFunLike.coe (OrthonormalFrameLift.Equiv.trans_toEquiv _ _ x)) a).trans
      (_root_.Equiv.trans_apply _ _ a)
  refine (hdef _).trans ?_
  exact (congrArg ((SpinCStructure.twistEquiv (OrthonormalFrameLift.Equiv.refl _)
      (inverseDeterminantBundleEquivCanonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂)).toEquiv x)
    ((canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).chargeConjEquivTwist_toEquiv_inl x
      (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p))).trans <|
  (SpinCStructure.twistEquiv_toEquiv_inl _ _ x _ _).trans <| by
    rw [OrthonormalFrameLift.Equiv.refl_toEquiv, _root_.Equiv.refl_apply,
      inverseDeterminantBundleEquivCanonicalBundle_toEquiv_inl]
    -- The two sides differ only in the fibre `FiberProd (P ×_σ Spinᶜ(4)) _ x` versus
    -- `(s_ω.fiberProd Circle _).P x`, which agree by unfolding `OrthonormalFrameLift.fiberProd`.
    rfl

/-- **The equivalence `conj s_ω ≃ s_ω ⊗ K` in a frame**: it sends `[[p, 1], h]` to
`[([p, 1], [p, 1]), h]` for a unitary frame `p`. Every point of `conj s_ω` has this form. -/
@[simp]
theorem chargeConjEquivTwistCanonicalBundle_toEquiv_mk {x : X}
    (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x) (h : SpinC) :
    (chargeConjEquivTwistCanonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂).toEquiv x
        (Extend.mk χ hχ (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p) h) =
      Extend.mk μ hμ
        (P := FiberProd (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).P
          (canonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂))
        (FiberProd.mk (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p)
          (Extend.inl κ hκ p)) h :=
  (congrArg ((chargeConjEquivTwistCanonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂).toEquiv x)
    (Extend.smul_inl χ hχ (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p) h).symm).trans <|
  ((chargeConjEquivTwistCanonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂).map_smul x _ h).trans <|
  (congrArg (op h • ·)
    (chargeConjEquivTwistCanonicalBundle_toEquiv_inl hJ hJ₂ hJ₀ hF e h₀ h₂ p)).trans
    (Extend.smul_inl μ hμ _ h)

variable (Q : X → Type) [TopologicalSpace (TotalSpace Circle Q)] [∀ x, TopologicalSpace (Q x)]
  [FiberBundle Circle Q] [∀ x, MulAction Circleᵐᵒᵖ (Q x)] [PrincipalBundle Circle Q]

/-- **Taubes's charge conjugation isomorphism** `conj (s_ω ⊗ E) ≃ s_ω ⊗ (K ⊗ E⁻¹)`: for the
canonical `Spinᶜ` structure `s_ω` of a rank-four bundle with an orthogonal complex structure and a
principal `U(1)`-bundle `Q` with line `E`, the charge conjugate of `s_ω ⊗ E` is equivalent to the
twist of `s_ω` by the tensor product of the canonical circle bundle with the inverse of `Q`
(`TauCeti.PrincipalBundle.Tensor`, `TauCeti.PrincipalBundle.Inverse`). It is
`conj (s ⊗ E) ≃ s ⊗ (L⁻¹ ⊗ E⁻¹)` (`TauCeti.SpinCStructure.chargeConjTwistEquivTwist`) followed by
`L⁻¹ ⊗ E⁻¹ ≃ K ⊗ E⁻¹`, the tensor product of `L⁻¹ ≃ K`
(`TauCeti.OrthonormalFrameBundle.inverseDeterminantBundleEquivCanonicalBundle`) with the
identity. -/
def chargeConjTwistEquivTwistCanonicalBundle :
    ((canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).twist Q).chargeConj.Equiv
      ((canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).twist
        (Tensor Circle (canonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂) (Inverse Circle Q))) :=
  ((canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).chargeConjTwistEquivTwist Q).trans
    (SpinCStructure.twistEquiv (OrthonormalFrameLift.Equiv.refl _)
      (((inverseDeterminantBundleEquivCanonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂).fiberProd
        (PrincipalBundle.Equiv.refl Circle (Inverse Circle Q))).extend τ hτ))

/-- **Taubes's isomorphism `conj (s_ω ⊗ E) ≃ s_ω ⊗ (K ⊗ E⁻¹)` at `[[([p, 1], q), 1], 1]`**: it
sends `[[([p, 1], q), 1], 1]` to `[([p, 1], [([p, 1], [q, 1]), 1]), 1]` for a unitary frame `p`
and a point `q` of `Q`. -/
@[simp]
theorem chargeConjTwistEquivTwistCanonicalBundle_toEquiv_inl {x : X}
    (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x) (q : Q x) :
    (chargeConjTwistEquivTwistCanonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂ Q).toEquiv x
        (Extend.inl χ hχ (Extend.inl μ hμ
          (P := FiberProd (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).P Q)
          (FiberProd.mk (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p) q))) =
      Extend.inl μ hμ
        (P := FiberProd (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).P
          (Tensor Circle (canonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂) (Inverse Circle Q)))
        (FiberProd.mk (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p)
          (Extend.inl τ hτ (FiberProd.mk (Extend.inl κ hκ p) (Extend.inl ν hν q)))) := by
  have hdef (a : ((canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).twist Q).chargeConj.P x) :
      (chargeConjTwistEquivTwistCanonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂ Q).toEquiv x a =
        (SpinCStructure.twistEquiv (OrthonormalFrameLift.Equiv.refl _)
          (((inverseDeterminantBundleEquivCanonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂).fiberProd
            (PrincipalBundle.Equiv.refl Circle (Inverse Circle Q))).extend τ hτ)).toEquiv x
          (((canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).chargeConjTwistEquivTwist Q).toEquiv x
            a) :=
    (congrFun (congrArg DFunLike.coe (OrthonormalFrameLift.Equiv.trans_toEquiv _ _ x)) a).trans
      (_root_.Equiv.trans_apply _ _ a)
  refine (hdef _).trans ?_
  exact (congrArg ((SpinCStructure.twistEquiv (OrthonormalFrameLift.Equiv.refl _)
      (((inverseDeterminantBundleEquivCanonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂).fiberProd
        (PrincipalBundle.Equiv.refl Circle (Inverse Circle Q))).extend τ hτ)).toEquiv x)
    ((canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).chargeConjTwistEquivTwist_toEquiv_inl Q x
      (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p) q)).trans <|
  (SpinCStructure.twistEquiv_toEquiv_inl _ _ x _ _).trans <| by
    rw [OrthonormalFrameLift.Equiv.refl_toEquiv, _root_.Equiv.refl_apply,
      PrincipalBundle.Equiv.extend_toEquiv_inl, PrincipalBundle.Equiv.fiberProd_toEquiv_mk,
      inverseDeterminantBundleEquivCanonicalBundle_toEquiv_inl, PrincipalBundle.Equiv.refl_toEquiv,
      _root_.Equiv.refl_apply]
    -- As above, the fibres agree by unfolding `OrthonormalFrameLift.fiberProd`.
    rfl

/-- **Taubes's isomorphism `conj (s_ω ⊗ E) ≃ s_ω ⊗ (K ⊗ E⁻¹)` in a frame**: it sends
`[[([p, 1], q), 1], h]` to `[([p, 1], [([p, 1], [q, 1]), 1]), h]` for a unitary frame `p` and a
point `q` of `Q`. Every point of `conj (s_ω ⊗ E)` has this form. -/
@[simp]
theorem chargeConjTwistEquivTwistCanonicalBundle_toEquiv_mk {x : X}
    (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x) (q : Q x) (h : SpinC) :
    (chargeConjTwistEquivTwistCanonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂ Q).toEquiv x
        (Extend.mk χ hχ (Extend.inl μ hμ
          (P := FiberProd (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).P Q)
          (FiberProd.mk (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p) q)) h) =
      Extend.mk μ hμ
        (P := FiberProd (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).P
          (Tensor Circle (canonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂) (Inverse Circle Q)))
        (FiberProd.mk (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p)
          (Extend.inl τ hτ (FiberProd.mk (Extend.inl κ hκ p) (Extend.inl ν hν q)))) h :=
  (congrArg ((chargeConjTwistEquivTwistCanonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂ Q).toEquiv x)
    (Extend.smul_inl χ hχ _ h).symm).trans <|
  ((chargeConjTwistEquivTwistCanonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂ Q).map_smul x _ h).trans <|
  (congrArg (op h • ·)
    (chargeConjTwistEquivTwistCanonicalBundle_toEquiv_inl hJ hJ₂ hJ₀ hF e h₀ h₂ Q p q)).trans
    (Extend.smul_inl μ hμ _ h)

end OrthonormalFrameBundle

end TauCeti

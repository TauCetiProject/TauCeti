/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.SpinStructure.AlmostComplex.Anticanonical
public import TauCeti.Topology.VectorBundle.SpinStructure.AlmostComplex.ChargeConjugation

/-!
# The canonical line of an almost Hermitian rank-four bundle

Let `E → X` be a rank-four real vector bundle with fibre inner products and a continuous fibrewise
orthogonal complex structure `J`, with unitary frame bundle `P` and canonical `Spinᶜ` structure
`s_ω` (`TauCeti.OrthonormalFrameBundle.canonicalSpinCStructure`). The canonical circle bundle
`P ×_{det_ℂ⁻¹} U(1)` (`TauCeti.OrthonormalFrameBundle.canonicalBundle`) is the twisting bundle of
Taubes's charge conjugation isomorphism `conj (s_ω ⊗ E) ≃ s_ω ⊗ (K ⊗ E⁻¹)`
(`TauCeti.OrthonormalFrameBundle.chargeConjTwistEquivTwistCanonicalBundle`). This file identifies
its Hermitian line, the **canonical line** `K = P ×_{det_ℂ⁻¹} ℂ`
(`TauCeti.OrthonormalFrameBundle.canonicalLine`), as a complex line bundle, and computes its first
Chern class `κ = c₁(K)`.

* **`K ≃ conj L`.** The determinant line `L` of `s_ω` is fibrewise conjugate-linearly isomorphic to
  `K` (`TauCeti.OrthonormalFrameBundle.canonicalLineEquivDeterminantLine`), by
  `[p, w] ↦ [[p, 1], conj w]` for a unitary frame `p`, continuously in both directions. It is the
  identification of the line of the inverse determinant bundle with the conjugate of `L`
  (`TauCeti.SpinCStructure.inverseDeterminantLineEquiv`) followed by the line of the equivalence
  `L⁻¹ ≃ K` of circle bundles
  (`TauCeti.OrthonormalFrameBundle.inverseDeterminantBundleEquivCanonicalBundle`).
* **`K ≃ conj Λ²_ℂ (E, J)`.** Since `L` is the anticanonical line `Λ²_ℂ (E, J)`
  (`TauCeti.OrthonormalFrameBundle.canonicalDeterminantLineEquivDetBundle`), `K` is fibrewise
  conjugate-linearly isomorphic to `Λ²_ℂ (E, J)`, by `[p, w] ↦ conj w (p e₀ ∧ p e₂)`
  (`TauCeti.OrthonormalFrameBundle.canonicalLineEquivDetBundle`), continuously on total spaces.
  For Hermitian lines the conjugate is the dual, so this is `K = (Λ²_ℂ (E, J))*`; for an almost
  Hermitian four-manifold, with `E` its tangent bundle, this is the canonical line `Λ^{2,0}`.
* **`c₁(K) = -c₁(E, J)`.** A conjugate-linear isomorphism of complex lines, continuous on total
  spaces, negates the first Chern class
  (`TauCeti.complexEulerClass_eq_neg_of_finrank_eq_one_of_conjugateFiberwise`), so
  `c₁(K) = -c₁(s_ω)` (`TauCeti.OrthonormalFrameBundle.lineFirstChernClass_canonicalLine`), and
  `c₁(s_ω) = c₁(E, J)`
  (`TauCeti.OrthonormalFrameBundle.firstChernClass_canonicalSpinCStructure_eq_firstChernClass`)
  gives `κ = -c₁(E, J)`
  (`TauCeti.OrthonormalFrameBundle.lineFirstChernClass_canonicalLine_eq_neg_firstChernClass`).
  Equivalently `c₁(s_ω) = -κ`: the determinant line of the canonical `Spinᶜ` structure is `K⁻¹`,
  with first Chern class `-κ`, as in the dimension formula of the Seiberg–Witten moduli spaces of
  the twisted structures `s_ω ⊗ E`.

## Main definitions

* `TauCeti.OrthonormalFrameBundle.canonicalLine`: the canonical line `K = P ×_{det_ℂ⁻¹} ℂ`.
* `TauCeti.OrthonormalFrameBundle.canonicalLineEquivDeterminantLine`: `K ≃ conj L`.
* `TauCeti.OrthonormalFrameBundle.canonicalLineEquivDetBundle`: `K ≃ conj Λ²_ℂ (E, J)`.

## Main results

* `TauCeti.OrthonormalFrameBundle.canonicalLineEquivDeterminantLine_mk_inl`,
  `TauCeti.OrthonormalFrameBundle.canonicalLineEquivDeterminantLine_symm_mk_inl` and
  `TauCeti.OrthonormalFrameBundle.canonicalLineEquivDetBundle_mk_inl`: the identifications in a
  unitary frame.
* `TauCeti.OrthonormalFrameBundle.continuous_canonicalLineEquivDeterminantLine`,
  `TauCeti.OrthonormalFrameBundle.continuous_canonicalLineEquivDeterminantLine_symm` and
  `TauCeti.OrthonormalFrameBundle.continuous_canonicalLineEquivDetBundle`: continuity on total
  spaces.
* `TauCeti.OrthonormalFrameBundle.lineFirstChernClass_canonicalLine`: `c₁(K) = -c₁(s_ω)`.
* `TauCeti.OrthonormalFrameBundle.lineFirstChernClass_canonicalLine_eq_neg_firstChernClass`:
  `c₁(K) = -c₁(E, J)`.

## References

* C. H. Taubes, *GR = SW: counting curves and connections*, J. Differential Geom. 52 (1999),
  453–609.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.4.
* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
-/

public section

noncomputable section

open Bundle CliffordAlgebra Module TauCeti.PrincipalBundle

namespace TauCeti

namespace OrthonormalFrameBundle

variable {X : Type} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
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

/-- The inverse determinant character `Spinᶜ(4) → U(1)`, `g ↦ (det g)⁻¹`. -/
local notation "δ" => (spinCGroup.det (realCliffordForm 4 0) hQ)⁻¹

/-- The inverse determinant character is continuous. -/
local notation "hδ" => spinCGroup.continuous_inv_det (realCliffordForm 4 0) hQ

/-- The inverse complex determinant `U(ℝ⁴, J₀) → U(1)` (`TauCeti.canonicalLineCharacter`), as a
monoid homomorphism in the form `simp` normalizes to. -/
local notation "κ" => MonoidHom.ofClass (canonicalLineCharacter hJ₀ e h₀ h₂)

/-- The inverse complex determinant is continuous. -/
local notation "hκ" => map_continuous (canonicalLineCharacter hJ₀ e h₀ h₂)

/-! ### The canonical line and the determinant line -/

/-- The **canonical line** `K = P ×_{det_ℂ⁻¹} ℂ` of a rank-four bundle with an orthogonal complex
structure: the Hermitian line of the canonical circle bundle
(`TauCeti.OrthonormalFrameBundle.canonicalBundle`), associated to the unitary frames `P` by the
inverse complex determinant. It is the conjugate of the anticanonical line `Λ²_ℂ (E, J)`
(`TauCeti.OrthonormalFrameBundle.canonicalLineEquivDetBundle`). -/
abbrev canonicalLine : X → Type :=
  AssociatedBundle Circle (canonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂) ℂ

/-- **The canonical line is the conjugate of the determinant line of `s_ω`**, at a fibre: the
conjugate-linear isomorphism sending `[p, w]` to `[[p, 1], conj w]` for every unitary frame `p`
(`TauCeti.OrthonormalFrameBundle.canonicalLineEquivDeterminantLine_mk_inl`). It is continuous on
total spaces in both directions
(`TauCeti.OrthonormalFrameBundle.continuous_canonicalLineEquivDeterminantLine`,
`TauCeti.OrthonormalFrameBundle.continuous_canonicalLineEquivDeterminantLine_symm`). -/
def canonicalLineEquivDeterminantLine (x : X) :
    canonicalLine hJ hJ₂ hJ₀ hF e h₀ h₂ x ≃L⋆[ℂ]
      (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).determinantLine x :=
  (Equiv.associatedContinuousLinearEquiv ℂ ℂ
    (inverseDeterminantBundleEquivCanonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂) x).symm.trans
      ((canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).inverseDeterminantLineEquiv x).symm

variable {hJ hJ₂ hJ₀ hF e h₀ h₂}

/-- **The identification `K ≃ conj L` in a unitary frame**: it sends `[p, w]` to
`[[p, 1], conj w]`. -/
@[simp]
theorem canonicalLineEquivDeterminantLine_mk_inl {x : X}
    (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x) (w : ℂ) :
    canonicalLineEquivDeterminantLine hJ hJ₂ hJ₀ hF e h₀ h₂ x
        (AssociatedBundle.mk Circle (Extend.inl κ hκ p) w) =
      AssociatedBundle.mk _ (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p)
        (SpinCStructure.DeterminantModel.toComplex.symm (starRingEnd ℂ w)) := by
  -- The equivalence `L⁻¹ ≃ K` of circle bundles sends `[[p, 1], 1]` to `[p, 1]`.
  have h := Equiv.associatedContinuousLinearEquiv_symm_mk (𝕜 := ℂ)
    (inverseDeterminantBundleEquivCanonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂)
    (Extend.inl δ hδ (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p)) w
  rw [inverseDeterminantBundleEquivCanonicalBundle_toEquiv_inl] at h
  -- `unfold` rather than `rw` or `simp` with the definition, which time out on its body.
  unfold canonicalLineEquivDeterminantLine
  rw [ContinuousLinearEquiv.trans_apply]
  -- `h` names the character `κ` through `ContinuousMonoidHom.toMonoidHom`, which is the coercion
  -- `MonoidHom.ofClass` of the goal by definition (`ContinuousMonoidHom.coe_toMonoidHom`).
  exact (congrArg _ h).trans
    ((canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).inverseDeterminantLineEquiv_symm_inl _ w)

/-- **The inverse identification `conj L ≃ K` in a unitary frame**: it sends `[[p, 1], w]` to
`[p, conj w]`. -/
@[simp]
theorem canonicalLineEquivDeterminantLine_symm_mk_inl {x : X}
    (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x) (w : SpinCStructure.DeterminantModel 4) :
    (canonicalLineEquivDeterminantLine hJ hJ₂ hJ₀ hF e h₀ h₂ x).symm
        (AssociatedBundle.mk _ (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p) w) =
      AssociatedBundle.mk Circle (Extend.inl κ hκ p)
        (starRingEnd ℂ (SpinCStructure.DeterminantModel.toComplex w)) := by
  rw [ContinuousLinearEquiv.symm_apply_eq, canonicalLineEquivDeterminantLine_mk_inl,
    starRingEnd_self_apply, LinearIsometryEquiv.symm_apply_apply]

/-- **The identification `K ≃ conj L` is continuous** on total spaces. -/
theorem continuous_canonicalLineEquivDeterminantLine :
    Continuous fun v : TotalSpace ℂ (canonicalLine hJ hJ₂ hJ₀ hF e h₀ h₂) ↦
      TotalSpace.mk' (SpinCStructure.DeterminantModel 4)
        (E := (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).determinantLine) v.proj
        (canonicalLineEquivDeterminantLine hJ hJ₂ hJ₀ hF e h₀ h₂ v.proj v.snd) := by
  have h := SpinCStructure.continuous_inverseDeterminantLineEquiv_symm
    (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂) |>.comp
      (Equiv.continuous_associatedContinuousLinearEquiv (𝕜 := ℂ) (F := ℂ)
        (inverseDeterminantBundleEquivCanonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂).symm)
  simp only [Equiv.associatedContinuousLinearEquiv_symm] at h
  exact h

/-- **The identification `conj L ≃ K` is continuous** on total spaces. -/
theorem continuous_canonicalLineEquivDeterminantLine_symm :
    Continuous fun v : TotalSpace (SpinCStructure.DeterminantModel 4)
        (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).determinantLine ↦
      TotalSpace.mk' ℂ (E := canonicalLine hJ hJ₂ hJ₀ hF e h₀ h₂) v.proj
        ((canonicalLineEquivDeterminantLine hJ hJ₂ hJ₀ hF e h₀ h₂ v.proj).symm v.snd) := by
  -- The inverse of `e.trans e'` applies `e'.symm` and then `e.symm`, by definition.
  exact (Equiv.continuous_associatedContinuousLinearEquiv (𝕜 := ℂ) (F := ℂ)
      (inverseDeterminantBundleEquivCanonicalBundle hJ hJ₂ hJ₀ hF e h₀ h₂)).comp
    (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).continuous_inverseDeterminantLineEquiv

/-- **The first Chern class of the canonical line** is minus that of the canonical `Spinᶜ`
structure: `c₁(K) = -c₁(s_ω)`, since `K` is the conjugate of the determinant line of `s_ω`. -/
theorem lineFirstChernClass_canonicalLine :
    lineFirstChernClass ℂ (canonicalLine hJ hJ₂ hJ₀ hF e h₀ h₂) (finrank_self ℂ) =
      -(canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).firstChernClass := by
  rw [SpinCStructure.firstChernClass_def, lineFirstChernClass_def, lineFirstChernClass_def]
  exact complexEulerClass_eq_neg_of_finrank_eq_one_of_conjugateFiberwise
    (SpinCStructure.DeterminantModel.finrank_eq_one 4) (finrank_self ℂ)
    continuous_canonicalLineEquivDeterminantLine

/-! ### The canonical line and the anticanonical line -/

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ F = 2 * finrank ℂ G)] [FiniteDimensional ℝ F]
  {Jc : Bundle.ContinuousComplexStructure F E} (hJc : ∀ x v, Jc x v = J x v)

variable (hJ hJ₂ hJ₀ hF e h₀ h₂) in
include hJc in
/-- **The canonical line is the conjugate of the anticanonical line** `Λ²_ℂ (E, J)`, at a fibre:
the conjugate-linear isomorphism sending `[p, w]` to `conj w (p e₀ ∧ p e₂)` for every unitary
frame `p` (`TauCeti.OrthonormalFrameBundle.canonicalLineEquivDetBundle_mk_inl`), continuous on
total spaces (`TauCeti.OrthonormalFrameBundle.continuous_canonicalLineEquivDetBundle`). For
Hermitian lines the conjugate is the dual, so `K = (Λ²_ℂ (E, J))*`. -/
def canonicalLineEquivDetBundle (x : X) :
    canonicalLine hJ hJ₂ hJ₀ hF e h₀ h₂ x ≃L⋆[ℂ] DetBundle ℂ G Jc.Fiber x :=
  (canonicalLineEquivDeterminantLine hJ hJ₂ hJ₀ hF e h₀ h₂ x).trans
    (canonicalDeterminantLineEquivDetBundle hJ hJ₂ hJ₀ hF e h₀ h₂ hJc x)

/-- **The identification `K ≃ conj Λ²_ℂ (E, J)` in a unitary frame**: it sends `[p, w]` to
`conj w (p e₀ ∧ p e₂)`. -/
@[simp]
theorem canonicalLineEquivDetBundle_mk_inl {x : X} (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x)
    (w : ℂ) :
    canonicalLineEquivDetBundle (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc x
        (AssociatedBundle.mk Circle (Extend.inl κ hκ p) w) =
      starRingEnd ℂ w • unitaryFrameWedge (G := G) h₀ h₂ hJc p := by
  unfold canonicalLineEquivDetBundle
  rw [ContinuousLinearEquiv.trans_apply, canonicalLineEquivDeterminantLine_mk_inl,
    canonicalDeterminantLineEquivDetBundle_mk_inl, LinearIsometryEquiv.apply_symm_apply]

/-- **The inverse identification `conj Λ²_ℂ (E, J) ≃ K` in a unitary frame**: it sends
`p e₀ ∧ p e₂` to `[p, 1]`, and so `w (p e₀ ∧ p e₂)` to `[p, conj w]`. -/
@[simp]
theorem canonicalLineEquivDetBundle_symm_unitaryFrameWedge {x : X}
    (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x) :
    (canonicalLineEquivDetBundle (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc x).symm
        (unitaryFrameWedge (G := G) h₀ h₂ hJc p) =
      AssociatedBundle.mk Circle (Extend.inl κ hκ p) 1 := by
  rw [ContinuousLinearEquiv.symm_apply_eq, canonicalLineEquivDetBundle_mk_inl, map_one, one_smul]

/-- **The identification `K ≃ conj Λ²_ℂ (E, J)` is continuous** on total spaces. -/
theorem continuous_canonicalLineEquivDetBundle :
    Continuous fun v : TotalSpace ℂ (canonicalLine hJ hJ₂ hJ₀ hF e h₀ h₂) ↦
      TotalSpace.mk' ℂ (E := DetBundle ℂ G Jc.Fiber) v.proj
        (canonicalLineEquivDetBundle (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc v.proj v.snd) :=
  (continuous_canonicalDeterminantLineEquivDetBundle (G := G) h₀ h₂ hJc).comp
    continuous_canonicalLineEquivDeterminantLine

include hJc in
/-- **The first Chern class of the canonical line** is minus that of `E` as a complex vector
bundle: `κ = c₁(K) = -c₁(E, J)`. -/
theorem lineFirstChernClass_canonicalLine_eq_neg_firstChernClass :
    lineFirstChernClass ℂ (canonicalLine hJ hJ₂ hJ₀ hF e h₀ h₂) (finrank_self ℂ) =
      -TauCeti.firstChernClass G Jc.Fiber := by
  rw [lineFirstChernClass_canonicalLine,
    firstChernClass_canonicalSpinCStructure_eq_firstChernClass (G := G) h₀ h₂ hJc]

end OrthonormalFrameBundle

end TauCeti

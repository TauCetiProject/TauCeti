/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.SpinStructure.FirstChernClass
import TauCeti.Topology.VectorBundle.Associated.Extension
import TauCeti.Topology.VectorBundle.Orientation.Complex.FiberwiseEquiv

/-!
# Charge conjugation of `Spinᶜ` structures

Charge conjugation of `Spinᶜ(n)` is the involutive automorphism `χ : [g, z] ↦ [g, z⁻¹]`
(`CliffordAlgebra.spinCGroup.chargeConj`). It covers the identity rotation and inverts the
determinant character. The **charge conjugate** `s.chargeConj` of a `Spinᶜ` structure `s` with
principal bundle `P` (`TauCeti.SpinCStructure.chargeConj`) is the extension of `s` along `χ`: its
principal bundle is `P ×_χ Spinᶜ(n)`, and the frame of `[p, 1]` is the frame of `p`
(`TauCeti.SpinCStructure.toFrame_chargeConj_inl`). So `s.chargeConj` is a `Spinᶜ` structure on the
same oriented bundle, with transition functions `χ ∘ g_αβ`.

**The determinant line.** The determinant line of `s.chargeConj` is the complex conjugate of that
of `s`. Since `conj (det (χ g) w) = det g (conj w)` on the determinant model `ℂ`, the map
`[[p, h], w] ↦ [p, conj (det h w)]` is a well-defined fibrewise conjugate-linear isomorphism
`L(s.chargeConj) ≃ L(s)` (`TauCeti.SpinCStructure.determinantLineChargeConjEquiv`), continuous on
total spaces. Consequently

`c₁(s.chargeConj) = -c₁(s)`

(`TauCeti.SpinCStructure.firstChernClass_chargeConj`), with integral coefficients, torsion
included.

**Functoriality and involutivity.** Equivalences of `Spinᶜ` structures induce equivalences of
their charge conjugates (`TauCeti.OrthonormalFrameLift.Equiv.chargeConj`). Since `χ ∘ χ = id`,
charge conjugation is involutive: `[[p, h], k] ↦ p • χ(h) k` is an equivalence
`s.chargeConj.chargeConj ≃ s` (`TauCeti.SpinCStructure.chargeConjChargeConjEquiv`).

**Relation to twisting.** Twisting a `Spinᶜ` structure by a principal `U(1)`-bundle is
`TauCeti.SpinCStructure.twist`. Since `χ x = x [1, (det x)⁻¹]`
(`CliffordAlgebra.spinCGroup.chargeConj_eq_mul_ofCircle_inv_det`), `s.chargeConj` is equivalent
to the twist of `s` by the inverse determinant bundle `P ×_{det⁻¹} U(1)`, and the charge
conjugate of `s ⊗ E` to `s ⊗ (L⁻¹ ⊗ E⁻¹)`, with `L⁻¹ ⊗ E⁻¹` realised either as a circle bundle
built from `P` and the circle bundle of `E` or as the tensor product `(P ×_{det⁻¹} U(1)) ⊗ E⁻¹`.
Moreover charge conjugation turns a twist by `L` into a twist by an inverse `L'` of `L`,
`(s.twist L).chargeConj ≃ s.chargeConj.twist L'` (`TauCeti.SpinCStructure.chargeConjTwistEquiv`).
These equivalences are in `TauCeti.Topology.VectorBundle.SpinStructure.Twist.ChargeConjugation`.
On a symplectic four-manifold the second gives `conj (s_ω ⊗ E) ≃ s_ω ⊗ (K ⊗ E⁻¹)`
(`TauCeti.OrthonormalFrameBundle.chargeConjTwistEquivTwistCanonicalBundle`), using the
identification `L⁻¹ ≃ K` of the inverse determinant bundle of `s_ω` with the canonical bundle
(`TauCeti.OrthonormalFrameBundle.inverseDeterminantBundleEquivCanonicalBundle`). The identity
`c₁(s.chargeConj) = -c₁(s)` is the corresponding statement about determinant classes.

**The half-spinor bundles.** In rank four, let `j : W ≃ W'` be a conjugate-linear isometric
equivalence of model Hermitian Clifford modules commuting with Clifford multiplication, such as
the quaternionic structure of the spinors. It intertwines the half-spin representation of `g` with
that of `χ g` (`Orientation.HalfSpinModel.conjEquiv_smul`), so `[p, ψ] ↦ [[p, 1], j ψ]` is a
well-defined fibrewise conjugate-linear isometric isomorphism
`W^ε(s) ≃ W'^ε'(s.chargeConj)`, `ε' = conj ε`, from the half-spinors of `s` to those of its charge
conjugate (`TauCeti.SpinCStructure.halfSpinorBundleChargeConjEquiv`). This is charge conjugation
of spinors `ψ ↦ j ψ`. It is continuous on total spaces and commutes with Clifford multiplication,
because the frames `p` of `s` and `[p, 1]` of `s.chargeConj` give the same frame of `E`
(`TauCeti.SpinCStructure.frameAt_chargeConj_inl`).

## Main definitions

* `TauCeti.SpinCStructure.chargeConj`: the charge conjugate of a `Spinᶜ` structure.
* `TauCeti.SpinCStructure.determinantLineChargeConjEquiv`: the fibrewise conjugate-linear
  isomorphism `L(s.chargeConj) ≃ L(s)`.
* `TauCeti.OrthonormalFrameLift.Equiv.chargeConj`: equivalences of charge conjugates.
* `TauCeti.SpinCStructure.chargeConjChargeConjEquiv`: `s.chargeConj.chargeConj ≃ s`.
* `TauCeti.SpinCStructure.halfSpinorBundleChargeConjEquiv`: charge conjugation of spinors, the
  fibrewise conjugate-linear isometric isomorphism `W^ε(s)_x ≃ W'^ε'(s.chargeConj)_x`.

## Main results

* `TauCeti.SpinCStructure.toFrame_chargeConj_inl`, `TauCeti.SpinCStructure.frameAt_chargeConj_inl`:
  the frame of `[p, 1]` is the frame of `p`.
* `TauCeti.SpinCStructure.determinantLineChargeConjEquiv_mk`: the formula
  `[[p, h], w] ↦ [p, conj (det h w)]`.
* `TauCeti.SpinCStructure.continuous_determinantLineChargeConjEquiv`: it is continuous on total
  spaces.
* `TauCeti.SpinCStructure.firstChernClass_chargeConj`: `c₁(s.chargeConj) = -c₁(s)`.
* `TauCeti.SpinCStructure.halfSpinorBundleChargeConjEquiv_mk`,
  `TauCeti.SpinCStructure.halfSpinorBundleChargeConjEquiv_symm_mk`: the formulas
  `[p, ψ] ↦ [[p, 1], j ψ]` and `[[p, h], φ] ↦ [p, j⁻¹ (h φ)]`.
* `TauCeti.SpinCStructure.continuous_halfSpinorBundleChargeConjEquiv`,
  `TauCeti.SpinCStructure.continuous_halfSpinorBundleChargeConjEquiv_symm`: charge conjugation of
  spinors and its inverse are continuous on total spaces.
* `TauCeti.SpinCStructure.cliffordMul_halfSpinorBundleChargeConjEquiv`:
  `c(v) (j ψ) = j (c(v) ψ)`.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996.
* C. H. Taubes, *GR = SW: counting curves and connections*, J. Differential Geom. 52 (1999),
  453–609.
-/

public section

noncomputable section

open Bundle MulOpposite CliffordAlgebra TauCeti.PrincipalBundle

namespace TauCeti

variable {n : ℕ} [NeZero n]

/-- The proof that the standard form on `ℝⁿ`, `n ≥ 1`, is nonzero, on which `Spinᶜ(n)` depends. -/
local notation "hQ" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm n 0)
local notation "SpinC" => spinCGroup (realCliffordForm n 0) hQ

/-- The rotation homomorphism `Spinᶜ(n) → SO(n) ⊆ GL(ℝⁿ)`, along which `Spinᶜ` structures lift the
orthonormal frame bundle. -/
local notation "πᶜ" => MonoidHom.comp
  (Subgroup.subtype (QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)))
  (spinCGroup.toSpecialOrthogonal (realCliffordForm n 0) hQ)

/-- Charge conjugation of `Spinᶜ(n)` as a homomorphism. -/
local notation "χ" => MonoidHom.ofClass (spinCGroup.chargeConj (realCliffordForm n 0) hQ)

/-- Charge conjugation is continuous (`CliffordAlgebra.spinCGroup.continuous_chargeConj`). -/
local notation "hχ" => spinCGroup.continuous_chargeConj (realCliffordForm n 0) hQ

/-- Charge conjugation covers the identity rotation, `πᶜ ∘ χ = πᶜ`
(`CliffordAlgebra.spinCGroup.subtype_comp_toSpecialOrthogonal_comp_chargeConj`): the
compatibility hypothesis of `TauCeti.OrthonormalFrameLift.extendSpinC` for `χ`. -/
local notation "hπχ" =>
  spinCGroup.subtype_comp_toSpecialOrthogonal_comp_chargeConj (realCliffordForm n 0) hQ

section Structure

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : X → Type} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]

namespace SpinCStructure

/-- The **charge conjugate** of a `Spinᶜ` structure `s` with principal bundle `P`: the extension of
`s` along charge conjugation `χ : [g, z] ↦ [g, z⁻¹]` of `Spinᶜ(n)`
(`CliffordAlgebra.spinCGroup.chargeConj`). Its principal bundle is `P ×_χ Spinᶜ(n)`, and the frame
of `[p, 1]` is the frame of `p` (`TauCeti.SpinCStructure.toFrame_chargeConj_inl`). Its determinant
line is the conjugate of that of `s`, so `c₁(s.chargeConj) = -c₁(s)`
(`TauCeti.SpinCStructure.firstChernClass_chargeConj`). Its body is exposed so that the fibre
`s.chargeConj.P x` unfolds to `P ×_χ Spinᶜ(n)` downstream. -/
@[expose]
def chargeConj (s : SpinCStructure F V n) : SpinCStructure F V n :=
  s.extendSpinC χ hχ hπχ

/-- **The frame of `[p, 1]`** in the charge conjugate of a `Spinᶜ` structure is the frame of `p`. -/
@[simp]
theorem toFrame_chargeConj_inl (s : SpinCStructure F V n) (x : X) (p : s.P x) :
    s.chargeConj.toFrame ⟨x, Extend.inl χ hχ p⟩ = s.toFrame ⟨x, p⟩ :=
  s.toFrame_extendSpinC_inl χ hχ hπχ x p

/-- **The frame of `[p, 1]`** in the charge conjugate of a `Spinᶜ` structure is the frame of `p`,
as a frame of the fibre. -/
@[simp]
theorem frameAt_chargeConj_inl (s : SpinCStructure F V n) {x : X} (p : s.P x) :
    s.chargeConj.frameAt (Extend.inl χ hχ p) = s.frameAt p :=
  s.frameAt_extend_inl χ hχ hπχ spinCGroup.norm_toLp_toSpecialOrthogonal_apply
    spinCGroup.continuous_toSpecialOrthogonal_apply p

/-- **The frame of `[p, h]`** in the charge conjugate of a `Spinᶜ` structure is the frame of `p`
composed with the rotation of `h`. -/
theorem toFrame_chargeConj_mk (s : SpinCStructure F V n) (x : X) (p : s.P x)
    (h : spinCGroup (realCliffordForm n 0) hQ) (v : Fin n → ℝ) :
    TotalSpace.mk' F (s.chargeConj.toFrame ⟨x, Extend.mk χ hχ p h⟩).proj
        ((s.chargeConj.toFrame ⟨x, Extend.mk χ hχ p h⟩).frame (WithLp.toLp 2 v)) =
      TotalSpace.mk' F (s.toFrame ⟨x, p⟩).proj
        ((s.toFrame ⟨x, p⟩).frame (WithLp.toLp 2 (πᶜ h v))) :=
  s.toFrame_extend_mk χ hχ hπχ spinCGroup.norm_toLp_toSpecialOrthogonal_apply
    spinCGroup.continuous_toSpecialOrthogonal_apply x p h v

end SpinCStructure

/-! ### Functoriality and involutivity -/

namespace OrthonormalFrameLift

/-- **Charge conjugation is functorial**: an equivalence `s ≃ t` of `Spinᶜ` structures induces an
equivalence of their charge conjugates, by `[p, h] ↦ [φ p, h]`. -/
def Equiv.chargeConj {s t : SpinCStructure F V n} (φ : s.Equiv t) :
    s.chargeConj.Equiv t.chargeConj :=
  φ.extend χ hχ hπχ spinCGroup.norm_toLp_toSpecialOrthogonal_apply
    spinCGroup.continuous_toSpecialOrthogonal_apply

@[simp]
theorem Equiv.chargeConj_toEquiv_mk {s t : SpinCStructure F V n} (φ : s.Equiv t) (x : X)
    (p : s.P x) (h : spinCGroup (realCliffordForm n 0) hQ) :
    φ.chargeConj.toEquiv x (Extend.mk χ hχ p h) = Extend.mk χ hχ (φ.toEquiv x p) h :=
  φ.extend_toEquiv_mk χ hχ hπχ spinCGroup.norm_toLp_toSpecialOrthogonal_apply
    spinCGroup.continuous_toSpecialOrthogonal_apply x p h

end OrthonormalFrameLift

namespace SpinCStructure

/-- **Charge conjugation is involutive**: `s.chargeConj.chargeConj ≃ s`, by
`[[p, h], k] ↦ p • χ(h) k`. Extending along `χ` twice is extending along `χ ∘ χ`
(`TauCeti.OrthonormalFrameLift.extendCompEquiv`), and `χ ∘ χ = id`. -/
def chargeConjChargeConjEquiv (s : SpinCStructure F V n) : s.chargeConj.chargeConj.Equiv s :=
  (s.extendCompEquiv χ hχ hπχ spinCGroup.norm_toLp_toSpecialOrthogonal_apply
      spinCGroup.continuous_toSpecialOrthogonal_apply χ hχ hπχ
      spinCGroup.norm_toLp_toSpecialOrthogonal_apply
      spinCGroup.continuous_toSpecialOrthogonal_apply).symm.trans
    (s.extendSpinCEquivOfEquivariant (MonoidHom.comp χ χ)
      (by rw [spinCGroup.chargeConj_comp_chargeConj]; exact continuous_id)
      (by rw [spinCGroup.chargeConj_comp_chargeConj, MonoidHom.comp_id]) s (fun _ p ↦ p)
      (fun _ p g ↦ by rw [spinCGroup.chargeConj_comp_chargeConj, MonoidHom.id_apply]) continuous_id
      fun _ _ ↦ rfl)

@[simp]
theorem chargeConjChargeConjEquiv_toEquiv_mk (s : SpinCStructure F V n) (x : X) (p : s.P x)
    (h k : spinCGroup (realCliffordForm n 0) hQ) :
    (chargeConjChargeConjEquiv s).toEquiv x (Extend.mk χ hχ (Extend.mk χ hχ p h) k) =
      op (spinCGroup.chargeConj _ hQ h * k) • p := by
  simp only [chargeConjChargeConjEquiv, OrthonormalFrameLift.Equiv.trans_toEquiv]
  -- `[[p, h], k]` is the image of `[p, χ(h) k]` under `extendCompEquiv`.
  exact (Equiv.trans_apply _ _ _).trans <| (congrArg _ (s.extendCompEquiv_symm_toEquiv_mk_mk χ hχ
    hπχ spinCGroup.norm_toLp_toSpecialOrthogonal_apply
    spinCGroup.continuous_toSpecialOrthogonal_apply χ hχ hπχ
    spinCGroup.norm_toLp_toSpecialOrthogonal_apply
    spinCGroup.continuous_toSpecialOrthogonal_apply x p h k)).trans <|
    OrthonormalFrameLift.extendSpinCEquivOfEquivariant_toEquiv_mk (x := x) (p := p) ..

end SpinCStructure

end Structure

/-! ### The determinant line -/

section DeterminantLine

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : X → Type} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]

namespace SpinCStructure

/-- Conjugation of the determinant model is `χ`-equivariant: `conj (det g w) = det (χ g) (conj w)`,
from `DeterminantModel.conj_chargeConj_smul` and `χ ∘ χ = id`. -/
private theorem conj_smul (g : SpinC) (w : DeterminantModel n) :
    DeterminantModel.conj (g • w) = χ g • DeterminantModel.conj w := by
  simpa only [MonoidHom.coe_ofClass, spinCGroup.chargeConj_chargeConj] using
    DeterminantModel.conj_chargeConj_smul (χ g) w

/-- **The determinant line of the charge conjugate is the conjugate line**: the fibrewise
conjugate-linear isomorphism `L(s.chargeConj)_x ≃ L(s)_x`, `[[p, h], w] ↦ [p, conj (det h w)]`
(`TauCeti.SpinCStructure.determinantLineChargeConjEquiv_mk`). It is the inverse of the associated
map of the `χ`-equivariant conjugation of the determinant model
(`TauCeti.PrincipalBundle.Extend.associatedEquivOfEquivariant`), and continuous on total spaces
(`TauCeti.SpinCStructure.continuous_determinantLineChargeConjEquiv`). -/
def determinantLineChargeConjEquiv (s : SpinCStructure F V n) (x : X) :
    s.chargeConj.determinantLine x ≃L⋆[ℂ] s.determinantLine x :=
  (Extend.associatedEquivOfEquivariant χ hχ (P := s.P) DeterminantModel.conj conj_smul x).symm

/-- **The comparison of determinant lines in a frame**: `[[p, h], w] ↦ [p, conj (det h w)]`. -/
@[simp]
theorem determinantLineChargeConjEquiv_mk (s : SpinCStructure F V n) {x : X} (p : s.P x)
    (h : SpinC) (w : DeterminantModel n) :
    s.determinantLineChargeConjEquiv x
        (AssociatedBundle.mk (P := Extend s.P χ hχ) SpinC (Extend.mk χ hχ p h) w) =
      AssociatedBundle.mk SpinC p (DeterminantModel.toComplex.symm
        (starRingEnd ℂ ((spinCGroup.det _ hQ h : ℂ) * DeterminantModel.toComplex w))) := by
  -- Conjugation of the determinant model is an involution.
  have hconj (y : DeterminantModel n) : DeterminantModel.conj.symm y = DeterminantModel.conj y :=
    (ContinuousLinearEquiv.symm_apply_eq _).2 (DeterminantModel.toComplex.injective (by simp))
  have hs := Extend.associatedEquivOfEquivariant_symm_mk χ hχ DeterminantModel.conj conj_smul p h w
  rw [hconj] at hs
  rw [← DeterminantModel.toComplex_smul, ← DeterminantModel.toComplex_conj,
    LinearIsometryEquiv.symm_apply_apply]
  exact hs

/-- **The comparison of determinant lines at `[p, 1]`**: `[[p, 1], w] ↦ [p, conj w]`. -/
@[simp]
theorem determinantLineChargeConjEquiv_inl (s : SpinCStructure F V n) {x : X} (p : s.P x)
    (w : DeterminantModel n) :
    s.determinantLineChargeConjEquiv x
        (AssociatedBundle.mk (P := Extend s.P χ hχ) SpinC (Extend.inl χ hχ p) w) =
      AssociatedBundle.mk SpinC p
        (DeterminantModel.toComplex.symm (starRingEnd ℂ (DeterminantModel.toComplex w))) := by
  rw [Extend.inl_def, determinantLineChargeConjEquiv_mk, map_one, Circle.coe_one, one_mul]

/-- **The comparison of determinant lines is continuous** on total spaces. -/
theorem continuous_determinantLineChargeConjEquiv (s : SpinCStructure F V n) :
    Continuous fun v : TotalSpace (DeterminantModel n) s.chargeConj.determinantLine ↦
      TotalSpace.mk' (DeterminantModel n) v.proj
        (s.determinantLineChargeConjEquiv v.proj v.snd) :=
  Extend.continuous_associatedEquivOfEquivariant_symm χ hχ DeterminantModel.conj conj_smul

end SpinCStructure

end DeterminantLine

/-! ### The first Chern class -/

section FirstChernClass

variable {X : Type} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : X → Type} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]

namespace SpinCStructure

/-- **The first Chern class of the charge conjugate is the negative**: `c₁(s.chargeConj) = -c₁(s)`
in `H²(X; ℤ)`, since the determinant line of `s.chargeConj` is the complex conjugate of that of
`s` (`TauCeti.SpinCStructure.determinantLineChargeConjEquiv`). -/
@[simp]
theorem firstChernClass_chargeConj (s : SpinCStructure F V n) :
    s.chargeConj.firstChernClass = -s.firstChernClass := by
  rw [firstChernClass_def, firstChernClass_def, lineFirstChernClass_def, lineFirstChernClass_def]
  exact complexEulerClass_eq_neg_of_finrank_eq_one_of_conjugateFiberwise
    (DeterminantModel.finrank_eq_one n) (DeterminantModel.finrank_eq_one n)
    (continuous_determinantLineChargeConjEquiv s)

end SpinCStructure

end FirstChernClass

/-! ### The half-spinor bundles -/

section HalfSpinor

/-- The proof that the standard form on `ℝ⁴` is nonzero, on which `Spinᶜ(4)` depends. -/
local notation "hpos" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm 4 0)
local notation "SpinC₄" => spinCGroup (realCliffordForm 4 0) hpos

/-- Charge conjugation of `Spinᶜ(4)` as a homomorphism. -/
local notation "χ₄" => MonoidHom.ofClass (spinCGroup.chargeConj (realCliffordForm 4 0) hpos)

/-- Charge conjugation of `Spinᶜ(4)` is continuous. -/
local notation "hχ₄" => spinCGroup.continuous_chargeConj (realCliffordForm 4 0) hpos

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : X → Type} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin 4)) (hQV : ∀ v, Q v = -‖v‖ ^ 2)
  (b : OrthonormalBasis (Fin 4) ℝ V)
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
  {W' : Type*} [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [FiniteDimensional ℂ W']
  {ρ' : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W'}
  (hρ' : ∀ v, LinearMap.adjoint (ρ' (ι Q v)) = -ρ' (ι Q v))
  (j : W ≃ₗᵢ⋆[ℂ] W') (hj : ∀ v w, j (ρ (ι Q v) w) = ρ' (ι Q v) (j w)) {ε ε' : ℂ}
  (hε : starRingEnd ℂ ε = ε')

namespace SpinCStructure

omit [Fact (Module.finrank ℝ V = 4)] in
/-- **The vector frame of `[p, 1]`** in the charge conjugate of a `Spinᶜ` structure of rank four
is the vector frame `κ_p` of `p`. -/
@[simp]
theorem vectorFrame_chargeConj_inl (s : SpinCStructure F E 4) {x : X} (p : s.P x) :
    s.chargeConj.vectorFrame b (Extend.inl χ₄ hχ₄ p) = s.vectorFrame b p :=
  vectorFrame_eq_of_frameAt_eq (frameAt_chargeConj_inl s p)

/-- **Charge conjugation of spinors** `ψ ↦ j ψ`: the fibrewise conjugate-linear isometric
isomorphism `W^ε(s)_x ≃ W'^ε'(s.chargeConj)_x` from the half-spinors of a `Spinᶜ` structure of rank
four to those of its charge conjugate, induced by a conjugate-linear isometric equivalence
`j : W ≃ W'` of the model Hermitian Clifford modules commuting with Clifford multiplication, such
as the quaternionic structure of the spinors, with `ε' = conj ε`. In frames it is
`[p, ψ] ↦ [[p, 1], j ψ]` (`TauCeti.SpinCStructure.halfSpinorBundleChargeConjEquiv_mk`), which is
well defined because `j (g • ψ) = χ(g) • j ψ` for charge conjugation `χ` of `Spinᶜ(4)`
(`Orientation.HalfSpinModel.conjEquiv_smul`): it is the associated map of the `χ`-equivariant
model map `j` (`TauCeti.PrincipalBundle.Extend.associatedEquivOfEquivariant`). It is continuous on
total spaces (`TauCeti.SpinCStructure.continuous_halfSpinorBundleChargeConjEquiv`) and commutes
with Clifford multiplication (`TauCeti.SpinCStructure.cliffordMul_halfSpinorBundleChargeConjEquiv`).
-/
def halfSpinorBundleChargeConjEquiv (s : SpinCStructure F E 4) (x : X) :
    s.halfSpinorBundle o hQV b ρ hρ ε x ≃ₗᵢ⋆[ℂ]
      s.chargeConj.halfSpinorBundle o hQV b ρ' hρ' ε' x where
  toLinearEquiv := (Extend.associatedEquivOfEquivariant χ₄ hχ₄
    (Orientation.HalfSpinModel.conjEquiv hρ hρ' j hj hε).toContinuousLinearEquiv
    (Orientation.HalfSpinModel.conjEquiv_smul hρ hρ' j hj hε) x).toLinearEquiv
  norm_map' ψ := by
    obtain ⟨p, ψ, rfl⟩ := AssociatedBundle.exists_mk ψ
    refine (congrArg Norm.norm (Extend.associatedEquivOfEquivariant_mk χ₄ hχ₄ _
      (Orientation.HalfSpinModel.conjEquiv_smul hρ hρ' j hj hε) p ψ)).trans ?_
    -- Both classes have the norm of their model vectors, which `j` preserves.
    exact (AssociatedBundle.norm_mk _ _).trans
      (((Orientation.HalfSpinModel.conjEquiv hρ hρ' j hj hε).norm_map ψ).trans
        (AssociatedBundle.norm_mk p ψ).symm)

/-- **Charge conjugation of spinors in a frame**: `[p, ψ] ↦ [[p, 1], j ψ]` for every point `p` of
the principal bundle over `x`. -/
@[simp]
theorem halfSpinorBundleChargeConjEquiv_mk (s : SpinCStructure F E 4) {x : X} (p : s.P x)
    (ψ : o.HalfSpinModel hQV b ρ hρ ε) :
    s.halfSpinorBundleChargeConjEquiv o hQV b hρ hρ' j hj hε x (AssociatedBundle.mk SpinC₄ p ψ) =
      AssociatedBundle.mk (P := s.chargeConj.P) SpinC₄ (Extend.inl χ₄ hχ₄ p)
        (Orientation.HalfSpinModel.conjEquiv hρ hρ' j hj hε ψ) :=
  -- By definition, `halfSpinorBundleChargeConjEquiv` applies the associated map of `j`.
  Extend.associatedEquivOfEquivariant_mk χ₄ hχ₄ _
    (Orientation.HalfSpinModel.conjEquiv_smul hρ hρ' j hj hε) p ψ

/-- **The inverse of charge conjugation of spinors in a frame**: `[[p, h], φ] ↦ [p, j⁻¹ (h φ)]`
for every point `[p, h]` of the principal bundle of the charge conjugate over `x`. -/
@[simp]
theorem halfSpinorBundleChargeConjEquiv_symm_mk (s : SpinCStructure F E 4) {x : X} (p : s.P x)
    (h : SpinC₄) (φ : o.HalfSpinModel hQV b ρ' hρ' ε') :
    (s.halfSpinorBundleChargeConjEquiv o hQV b hρ hρ' j hj hε x).symm
        (AssociatedBundle.mk (P := s.chargeConj.P) SpinC₄ (Extend.mk χ₄ hχ₄ p h) φ) =
      AssociatedBundle.mk SpinC₄ p
        ((Orientation.HalfSpinModel.conjEquiv hρ hρ' j hj hε).symm (h • φ)) :=
  -- By definition, the inverse is the inverse of the associated map of `j`.
  Extend.associatedEquivOfEquivariant_symm_mk χ₄ hχ₄ _
    (Orientation.HalfSpinModel.conjEquiv_smul hρ hρ' j hj hε) p h φ

/-- **The inverse of charge conjugation of spinors at `[p, 1]`**: `[[p, 1], ψ] ↦ [p, j⁻¹ ψ]`. -/
@[simp]
theorem halfSpinorBundleChargeConjEquiv_symm_mk_inl (s : SpinCStructure F E 4) {x : X}
    (p : s.P x) (ψ : o.HalfSpinModel hQV b ρ' hρ' ε') :
    (s.halfSpinorBundleChargeConjEquiv o hQV b hρ hρ' j hj hε x).symm
        (AssociatedBundle.mk (P := s.chargeConj.P) SpinC₄ (Extend.inl χ₄ hχ₄ p) ψ) =
      AssociatedBundle.mk SpinC₄ p
        ((Orientation.HalfSpinModel.conjEquiv hρ hρ' j hj hε).symm ψ) := by
  rw [Extend.inl_def, halfSpinorBundleChargeConjEquiv_symm_mk, one_smul]

/-- **Charge conjugation of spinors is continuous** on total spaces. -/
theorem continuous_halfSpinorBundleChargeConjEquiv (s : SpinCStructure F E 4) :
    Continuous fun v : TotalSpace (o.HalfSpinModel hQV b ρ hρ ε)
        (s.halfSpinorBundle o hQV b ρ hρ ε) ↦
      TotalSpace.mk' (o.HalfSpinModel hQV b ρ' hρ' ε') v.proj
        (s.halfSpinorBundleChargeConjEquiv o hQV b hρ hρ' j hj hε v.proj v.snd) :=
  Extend.continuous_associatedEquivOfEquivariant χ₄ hχ₄ _
    (Orientation.HalfSpinModel.conjEquiv_smul hρ hρ' j hj hε)

/-- **The inverse of charge conjugation of spinors is continuous** on total spaces. -/
theorem continuous_halfSpinorBundleChargeConjEquiv_symm (s : SpinCStructure F E 4) :
    Continuous fun v : TotalSpace (o.HalfSpinModel hQV b ρ' hρ' ε')
        (s.chargeConj.halfSpinorBundle o hQV b ρ' hρ' ε') ↦
      TotalSpace.mk' (o.HalfSpinModel hQV b ρ hρ ε) v.proj
        ((s.halfSpinorBundleChargeConjEquiv o hQV b hρ hρ' j hj hε v.proj).symm v.snd) :=
  Extend.continuous_associatedEquivOfEquivariant_symm χ₄ hχ₄ _
    (Orientation.HalfSpinModel.conjEquiv_smul hρ hρ' j hj hε)

/-- **Charge conjugation of spinors commutes with Clifford multiplication**:
`c(v) (j ψ) = j (c(v) ψ)` for `c(v) : W^ε(s)_x → W^{-ε}(s)_x` and
`c(v) : W'^ε'(s.chargeConj)_x → W'^{-ε'}(s.chargeConj)_x`. -/
theorem cliffordMul_halfSpinorBundleChargeConjEquiv (s : SpinCStructure F E 4) {δ δ' : ℂ}
    (hδ : δ = -ε) (hδ' : δ' = -ε') {x : X} (v : E x) (ψ : s.halfSpinorBundle o hQV b ρ hρ ε x) :
    s.chargeConj.cliffordMul o hQV b ρ' hρ' hδ' x v
        (s.halfSpinorBundleChargeConjEquiv o hQV b hρ hρ' j hj hε x ψ) =
      s.halfSpinorBundleChargeConjEquiv o hQV b hρ hρ' j hj (by rw [hδ, hδ', map_neg, hε]) x
        (s.cliffordMul o hQV b ρ hρ hδ x v ψ) := by
  obtain ⟨p, ψ, rfl⟩ := AssociatedBundle.exists_mk ψ
  rw [halfSpinorBundleChargeConjEquiv_mk, cliffordMul_mk, halfSpinorBundleChargeConjEquiv_mk]
  -- `rw` does not unfold `chargeConj`, so the point `[p, 1]` of `s.chargeConj.P x` is explicit.
  rw [s.chargeConj.cliffordMul_mk hδ' (Extend.inl χ₄ hχ₄ p), vectorFrame_chargeConj_inl,
    Orientation.HalfSpinModel.cliffordMul_conjEquiv]

end SpinCStructure

end HalfSpinor

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.SpinStructure.FirstChernClass
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
`TauCeti.SpinCStructure.twist`. Charge conjugation turns a twist by `L` into a twist by an
inverse `L'` of `L`, `(s.twist L).chargeConj ≃ s.chargeConj.twist L'`
(`TauCeti.SpinCStructure.chargeConjTwistEquiv`, in
`TauCeti.Topology.VectorBundle.SpinStructure.Twist.ChargeConjugation`). Since
`χ x = x [1, (det x)⁻¹]` (`CliffordAlgebra.spinCGroup.chargeConj_eq_mul_ofCircle_inv_det`),
`s.chargeConj` should moreover be equivalent to the twist of `s` by the inverse of the
`U(1)`-bundle of its determinant line. On a symplectic four-manifold the two together give
`conj (s_ω ⊗ E) ≃ s_ω ⊗ (K ⊗ E⁻¹)`, whose group-level input is
`CliffordAlgebra.spinCGroup.chargeConj_mul_ofCircle`. The second equivalence is not proved; the
identity `c₁(s.chargeConj) = -c₁(s)` is the corresponding statement about determinant classes.

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

* `TauCeti.SpinCStructure.toFrame_chargeConj_inl`: the frame of `[p, 1]` is the frame of `p`.
* `TauCeti.SpinCStructure.determinantLineChargeConjEquiv_mk`: the formula
  `[[p, h], w] ↦ [p, conj (det h w)]`.
* `TauCeti.SpinCStructure.continuous_determinantLineChargeConjEquiv`: it is continuous on total
  spaces.
* `TauCeti.SpinCStructure.firstChernClass_chargeConj`: `c₁(s.chargeConj) = -c₁(s)`.
* `TauCeti.SpinCStructure.halfSpinorBundleChargeConjEquiv_mk`: the formula
  `[p, ψ] ↦ [[p, 1], j ψ]`.
* `TauCeti.SpinCStructure.continuous_halfSpinorBundleChargeConjEquiv`: charge conjugation of
  spinors is continuous on total spaces.
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
(`CliffordAlgebra.spinCGroup.toSpecialOrthogonal_comp_chargeConj`): the compatibility
hypothesis of `TauCeti.OrthonormalFrameLift.extendSpinC` for `χ`. -/
local notation "hπχ" => Eq.trans (MonoidHom.comp_assoc _ _ _)
  (congrArg (MonoidHom.comp
      (Subgroup.subtype (QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0))))
    (spinCGroup.toSpecialOrthogonal_comp_chargeConj (realCliffordForm n 0) hQ))

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
  OrthonormalFrameBundle.mk_eq_mk_iff.1 ((s.chargeConj.toFrame_mk (Extend.inl χ hχ p)).symm.trans
    ((s.toFrame_chargeConj_inl x p).trans (s.toFrame_mk p)))

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
  simp only [chargeConjChargeConjEquiv, OrthonormalFrameLift.Equiv.trans_toEquiv,
    OrthonormalFrameLift.Equiv.symm_toEquiv]
  -- `[[p, h], k] = [[p, 1], χ(h) k]` is the image of `[p, χ(h) k]` under `extendCompEquiv`.
  have hcomp := (Equiv.symm_apply_eq _).2 ((s.extendCompEquiv_toEquiv_mk χ hχ hπχ
    spinCGroup.norm_toLp_toSpecialOrthogonal_apply spinCGroup.continuous_toSpecialOrthogonal_apply
    χ hχ hπχ spinCGroup.norm_toLp_toSpecialOrthogonal_apply
    spinCGroup.continuous_toSpecialOrthogonal_apply x p (χ h * k)).trans
      (Extend.mk_mk χ hχ χ hχ p h k).symm).symm
  exact (Equiv.trans_apply _ _ _).trans <| (congrArg _ hcomp).trans <|
    OrthonormalFrameLift.extendSpinCEquivOfEquivariant_toEquiv_mk (x := x) (p := p) ..

end SpinCStructure

end Structure

/-! ### The determinant line -/

section DeterminantLine

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : X → Type} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]

namespace SpinCStructure

/-- **The determinant line of the charge conjugate is the conjugate line**: the fibrewise
conjugate-linear isomorphism `L(s.chargeConj)_x ≃ L(s)_x`, `[[p, h], w] ↦ [p, conj (det h w)]`
(`TauCeti.SpinCStructure.determinantLineChargeConjEquiv_mk`). It is well defined because
`conj (det (χ g) w) = det g (conj w)`, and continuous on total spaces
(`TauCeti.SpinCStructure.continuous_determinantLineChargeConjEquiv`). -/
def determinantLineChargeConjEquiv (s : SpinCStructure F V n) (x : X) :
    s.chargeConj.determinantLine x ≃L⋆[ℂ] s.determinantLine x :=
  ((AssociatedBundle.mkContinuousLinearEquiv ℂ SpinC (F := DeterminantModel n)
      (Extend.inl χ hχ (Classical.arbitrary (s.P x)))).symm.trans DeterminantModel.conj).trans
    (AssociatedBundle.mkContinuousLinearEquiv ℂ SpinC (Classical.arbitrary (s.P x)))

/-- The comparison of determinant lines through the frames `[p₀, 1]` and `p₀`, for the chosen
point `p₀` of `s.P x`, stated on the fibre `Extend s.P χ hχ` of the charge conjugate. -/
private theorem determinantLineChargeConjEquiv_apply (s : SpinCStructure F V n) {x : X}
    (z : AssociatedBundle SpinC (Extend s.P χ hχ) (DeterminantModel n) x) :
    s.determinantLineChargeConjEquiv x z =
      AssociatedBundle.mkContinuousLinearEquiv ℂ SpinC (Classical.arbitrary (s.P x))
        (DeterminantModel.conj ((AssociatedBundle.mkContinuousLinearEquiv ℂ SpinC
          (F := DeterminantModel n) (Extend.inl χ hχ (Classical.arbitrary (s.P x)))).symm z)) :=
  (rfl)

/-- The comparison of determinant lines in terms of the conjugation of the determinant model. -/
private theorem determinantLineChargeConjEquiv_mk_eq_conj (s : SpinCStructure F V n) {x : X}
    (p : s.P x) (h : SpinC) (w : DeterminantModel n) :
    s.determinantLineChargeConjEquiv x
        (AssociatedBundle.mk (P := Extend s.P χ hχ) SpinC (Extend.mk χ hχ p h) w) =
      AssociatedBundle.mk SpinC p (DeterminantModel.conj (h • w)) := by
  simp only [determinantLineChargeConjEquiv_apply,
    AssociatedBundle.mkContinuousLinearEquiv_symm_apply_mk,
    AssociatedBundle.mkContinuousLinearEquiv_apply, Extend.inl_def, Extend.division_mk, inv_one,
    one_mul, mul_smul, MonoidHom.coe_ofClass]
  rw [DeterminantModel.conj_chargeConj_smul, ← AssociatedBundle.mk_smul,
    PrincipalBundle.smul_division]

/-- **The comparison of determinant lines in a frame**: `[[p, h], w] ↦ [p, conj (det h w)]`. -/
@[simp]
theorem determinantLineChargeConjEquiv_mk (s : SpinCStructure F V n) {x : X} (p : s.P x)
    (h : SpinC) (w : DeterminantModel n) :
    s.determinantLineChargeConjEquiv x
        (AssociatedBundle.mk (P := Extend s.P χ hχ) SpinC (Extend.mk χ hχ p h) w) =
      AssociatedBundle.mk SpinC p (DeterminantModel.toComplex.symm
        (starRingEnd ℂ ((spinCGroup.det _ hQ h : ℂ) * DeterminantModel.toComplex w))) := by
  rw [determinantLineChargeConjEquiv_mk_eq_conj, ← DeterminantModel.toComplex_smul,
    ← DeterminantModel.toComplex_conj, LinearIsometryEquiv.symm_apply_apply]

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
        (s.determinantLineChargeConjEquiv v.proj v.snd) := by
  -- The total space of `L(s.chargeConj)` is a quotient of `(P × Spinᶜ(n)) × ℂ`, on which the
  -- comparison is `((p, h), w) ↦ [p, conj (det h w)]`.
  have hq := (AssociatedBundle.isOpenQuotientMap_totalSpaceMk_mk SpinC (Extend s.P χ hχ)
    (DeterminantModel n)).comp
      ((Extend.isOpenQuotientMap_totalSpaceMk_mk s.P χ hχ).prodMap IsOpenQuotientMap.id)
  refine hq.continuous_comp_iff.1 ?_
  have hc : Continuous fun y : (TotalSpace SpinC s.P × SpinC) × DeterminantModel n ↦
      TotalSpace.mk' (DeterminantModel n) y.1.1.proj
        (AssociatedBundle.mk SpinC y.1.1.snd (DeterminantModel.conj (y.1.2 • y.2))) :=
    Continuous.totalSpaceMk_associatedBundleMk
      (f := fun y : (TotalSpace SpinC s.P × SpinC) × DeterminantModel n ↦ y.1.1.proj)
      (continuous_fst.comp continuous_fst) (DeterminantModel.conj.continuous.comp
        (continuous_smul.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))
  refine hc.congr fun y ↦ ?_
  exact (congrArg (TotalSpace.mk _)
    (determinantLineChargeConjEquiv_mk_eq_conj s y.1.1.snd y.1.2 y.2)).symm

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
(`Orientation.HalfSpinModel.conjEquiv_smul`). It is continuous on total spaces
(`TauCeti.SpinCStructure.continuous_halfSpinorBundleChargeConjEquiv`) and commutes with Clifford
multiplication (`TauCeti.SpinCStructure.cliffordMul_halfSpinorBundleChargeConjEquiv`). -/
def halfSpinorBundleChargeConjEquiv (s : SpinCStructure F E 4) (x : X) :
    s.halfSpinorBundle o hQV b ρ hρ ε x ≃ₗᵢ⋆[ℂ]
      s.chargeConj.halfSpinorBundle o hQV b ρ' hρ' ε' x :=
  ((AssociatedBundle.mkLinearIsometryEquiv ℂ SpinC₄ (Classical.arbitrary (s.P x))).symm.trans
      (Orientation.HalfSpinModel.conjEquiv hρ hρ' j hj hε)).trans
    (AssociatedBundle.mkLinearIsometryEquiv ℂ SpinC₄
      (Extend.inl χ₄ hχ₄ (Classical.arbitrary (s.P x))))

/-- Charge conjugation of spinors through the chosen point `p₀` of `s.P x`, stated with the fibre
`Extend s.P χ hχ` that `s.chargeConj.P` unfolds to, so that `rw` can match the point `[p₀, 1]` of
this fibre. -/
private theorem halfSpinorBundleChargeConjEquiv_apply (s : SpinCStructure F E 4) {x : X}
    (ψ : s.halfSpinorBundle o hQV b ρ hρ ε x) :
    s.halfSpinorBundleChargeConjEquiv o hQV b hρ hρ' j hj hε x ψ =
      AssociatedBundle.mkLinearIsometryEquiv (P := Extend s.P χ₄ hχ₄) ℂ SpinC₄
        (Extend.inl χ₄ hχ₄ (Classical.arbitrary (s.P x)))
        (Orientation.HalfSpinModel.conjEquiv hρ hρ' j hj hε
          ((AssociatedBundle.mkLinearIsometryEquiv ℂ SpinC₄ (Classical.arbitrary (s.P x))).symm
            ψ)) :=
  (rfl)

/-- **Charge conjugation of spinors in a frame**: `[p, ψ] ↦ [[p, 1], j ψ]` for every point `p` of
the principal bundle over `x`. -/
@[simp]
theorem halfSpinorBundleChargeConjEquiv_mk (s : SpinCStructure F E 4) {x : X} (p : s.P x)
    (ψ : o.HalfSpinModel hQV b ρ hρ ε) :
    s.halfSpinorBundleChargeConjEquiv o hQV b hρ hρ' j hj hε x (AssociatedBundle.mk SpinC₄ p ψ) =
      AssociatedBundle.mk (P := s.chargeConj.P) SpinC₄ (Extend.inl χ₄ hχ₄ p)
        (Orientation.HalfSpinModel.conjEquiv hρ hρ' j hj hε ψ) := by
  rw [halfSpinorBundleChargeConjEquiv_apply, AssociatedBundle.mkLinearIsometryEquiv_symm_apply_mk,
    AssociatedBundle.mkLinearIsometryEquiv_apply]
  -- Compare the chosen frame `p₀` with `p = p₀ • g`.
  generalize Classical.arbitrary (s.P x) = p₀
  obtain ⟨g, hg⟩ : ∃ g, PrincipalBundle.division SpinC₄ p₀ p = g := ⟨_, rfl⟩
  obtain rfl : op g • p₀ = p := hg ▸ PrincipalBundle.smul_division p₀ p
  rw [hg, Orientation.HalfSpinModel.conjEquiv_smul, Extend.inl_smul]
  -- The goal is stated on `s.chargeConj.P`, which unfolds to `Extend s.P χ₄ hχ₄`.
  exact (AssociatedBundle.mk_smul (P := Extend s.P χ₄ hχ₄) _ _ _).symm

/-- **The inverse of charge conjugation of spinors in a frame**: `[[p, 1], ψ] ↦ [p, j⁻¹ ψ]`. -/
@[simp]
theorem halfSpinorBundleChargeConjEquiv_symm_mk (s : SpinCStructure F E 4) {x : X} (p : s.P x)
    (ψ : o.HalfSpinModel hQV b ρ' hρ' ε') :
    (s.halfSpinorBundleChargeConjEquiv o hQV b hρ hρ' j hj hε x).symm
        (AssociatedBundle.mk (P := s.chargeConj.P) SpinC₄ (Extend.inl χ₄ hχ₄ p) ψ) =
      AssociatedBundle.mk SpinC₄ p
        ((Orientation.HalfSpinModel.conjEquiv hρ hρ' j hj hε).symm ψ) := by
  refine (LinearIsometryEquiv.symm_apply_eq _).2 ?_
  rw [halfSpinorBundleChargeConjEquiv_mk, LinearIsometryEquiv.apply_symm_apply]

/-- **Charge conjugation of spinors is continuous** on total spaces. -/
theorem continuous_halfSpinorBundleChargeConjEquiv (s : SpinCStructure F E 4) :
    Continuous fun v : TotalSpace (o.HalfSpinModel hQV b ρ hρ ε)
        (s.halfSpinorBundle o hQV b ρ hρ ε) ↦
      TotalSpace.mk' (o.HalfSpinModel hQV b ρ' hρ' ε') v.proj
        (s.halfSpinorBundleChargeConjEquiv o hQV b hρ hρ' j hj hε v.proj v.snd) := by
  -- The total space of `W^ε(s)` is a quotient of `P × S^ε`, on which the map is
  -- `(p, ψ) ↦ [[p, 1], j ψ]`, stated on `Extend s.P χ₄ hχ₄`, the unfolding of `s.chargeConj.P`.
  refine (AssociatedBundle.isOpenQuotientMap_totalSpaceMk_mk SpinC₄ s.P
    (o.HalfSpinModel hQV b ρ hρ ε)).continuous_comp_iff.1 ?_
  have hc : Continuous fun y : TotalSpace SpinC₄ s.P × o.HalfSpinModel hQV b ρ hρ ε ↦
      TotalSpace.mk' (o.HalfSpinModel hQV b ρ' hρ' ε') y.1.proj
        (AssociatedBundle.mk (P := Extend s.P χ₄ hχ₄) SpinC₄ (Extend.inl χ₄ hχ₄ y.1.snd)
          (Orientation.HalfSpinModel.conjEquiv hρ hρ' j hj hε y.2)) :=
    Continuous.totalSpaceMk_associatedBundleMk
      (f := fun y : TotalSpace SpinC₄ s.P × o.HalfSpinModel hQV b ρ hρ ε ↦ y.1.proj)
      ((Extend.continuous_inl s.P χ₄ hχ₄).comp continuous_fst)
      ((Orientation.HalfSpinModel.conjEquiv hρ hρ' j hj hε).continuous.comp continuous_snd)
  refine hc.congr fun y ↦ ?_
  exact (congrArg (TotalSpace.mk _)
    (halfSpinorBundleChargeConjEquiv_mk o hQV b hρ hρ' j hj hε s y.1.snd y.2)).symm

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

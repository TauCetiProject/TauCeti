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
`TauCeti.SpinCStructure.twist`. Since `χ x = x [1, (det x)⁻¹]`
(`CliffordAlgebra.spinCGroup.chargeConj_eq_mul_ofCircle_inv_det`), `s.chargeConj` should be
equivalent to the twist of `s` by the inverse of the `U(1)`-bundle of its determinant line. On a
symplectic four-manifold this gives `conj (s_ω ⊗ E) ≃ s_ω ⊗ (K ⊗ E⁻¹)`, whose group-level input
is `CliffordAlgebra.spinCGroup.chargeConj_mul_ofCircle`. Neither equivalence is proved here; the
identity `c₁(s.chargeConj) = -c₁(s)` is the corresponding statement about determinant classes.

## Main definitions

* `TauCeti.SpinCStructure.chargeConj`: the charge conjugate of a `Spinᶜ` structure.
* `TauCeti.SpinCStructure.determinantLineChargeConjEquiv`: the fibrewise conjugate-linear
  isomorphism `L(s.chargeConj) ≃ L(s)`.
* `TauCeti.OrthonormalFrameLift.Equiv.chargeConj`: equivalences of charge conjugates.
* `TauCeti.SpinCStructure.chargeConjChargeConjEquiv`: `s.chargeConj.chargeConj ≃ s`.

## Main results

* `TauCeti.SpinCStructure.toFrame_chargeConj_inl`: the frame of `[p, 1]` is the frame of `p`.
* `TauCeti.SpinCStructure.determinantLineChargeConjEquiv_mk`: the formula
  `[[p, h], w] ↦ [p, conj (det h w)]`.
* `TauCeti.SpinCStructure.continuous_determinantLineChargeConjEquiv`: it is continuous on total
  spaces.
* `TauCeti.SpinCStructure.firstChernClass_chargeConj`: `c₁(s.chargeConj) = -c₁(s)`.

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

end TauCeti

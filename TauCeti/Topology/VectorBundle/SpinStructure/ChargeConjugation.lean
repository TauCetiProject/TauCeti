/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.SpinStructure.FirstChernClass
import Mathlib.Topology.Algebra.Module.Star
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

On a symplectic four-manifold, the canonical `Spinᶜ` structure `s_ω` twisted by a Hermitian line
`E`, with determinant line `K⁻¹ E²`, has conjugate `s_ω ⊗ (K ⊗ E⁻¹)`, with determinant line
`K E⁻²`. At the level of structure groups this is
`CliffordAlgebra.spinCGroup.chargeConj_mul_ofCircle`; twisting `Spinᶜ` structures by Hermitian
lines is not constructed here, and the identity `c₁(s.chargeConj) = -c₁(s)` is the corresponding
statement about determinant classes.

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

/-- Charge conjugation is continuous. -/
local notation "hχ" => Continuous.congr
  (g := DFunLike.coe
    (MonoidHom.ofClass (spinCGroup.chargeConj (realCliffordForm n 0) hQ)))
  (spinCGroup.continuous_chargeConj (realCliffordForm n 0) hQ)
  (congrFun (Eq.symm (MonoidHom.coe_ofClass (spinCGroup.chargeConj (realCliffordForm n 0) hQ))))

/-- The rotations of `Spinᶜ(n)` preserve the Euclidean norm. -/
local notation "hπn" => fun (g : spinCGroup (realCliffordForm n 0) hQ) (v : Fin n → ℝ) ↦
  TauCeti.CliffordAlgebra.norm_toLp_specialOrthogonalGroup_realCliffordForm_apply n
    (spinCGroup.toSpecialOrthogonal (realCliffordForm n 0) hQ g) v

/-- Rotating a fixed vector is continuous in the element of `Spinᶜ(n)`. -/
local notation "hπc" => fun (v : Fin n → ℝ) ↦
  Continuous.comp
    (TauCeti.CliffordAlgebra.continuous_specialOrthogonalGroup_realCliffordForm_apply n v)
    (spinCGroup.continuous_toSpecialOrthogonal_pi (realCliffordForm n 0) hQ)

section Structure

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : X → Type} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]

namespace SpinCStructure

/-- Charge conjugation covers the identity rotation: the rotation of `χ g` is that of `g`. -/
private theorem rotation_comp_chargeConj : (πᶜ).comp χ = πᶜ :=
  MonoidHom.ext fun g ↦ by simp

/-- Charge conjugation is an involution: `χ ∘ χ = id`, as homomorphisms. -/
private theorem chargeConj_comp_chargeConj : MonoidHom.comp χ χ = MonoidHom.id _ :=
  MonoidHom.ext fun g ↦ by simp

/-- `χ ∘ χ` is continuous, being the identity. -/
private theorem continuous_chargeConj_comp_chargeConj : Continuous (MonoidHom.comp χ χ) := by
  rw [chargeConj_comp_chargeConj]
  exact continuous_id

/-- The **charge conjugate** of a `Spinᶜ` structure `s` with principal bundle `P`: the extension of
`s` along charge conjugation `χ : [g, z] ↦ [g, z⁻¹]` of `Spinᶜ(n)`
(`CliffordAlgebra.spinCGroup.chargeConj`). Its principal bundle is `P ×_χ Spinᶜ(n)`, and the frame
of `[p, 1]` is the frame of `p` (`TauCeti.SpinCStructure.toFrame_chargeConj_inl`). Its determinant
line is the conjugate of that of `s`, so `c₁(s.chargeConj) = -c₁(s)`
(`TauCeti.SpinCStructure.firstChernClass_chargeConj`). Its body is exposed so that the fibre
`s.chargeConj.P x` unfolds to `P ×_χ Spinᶜ(n)` downstream. -/
@[expose]
def chargeConj (s : SpinCStructure F V n) : SpinCStructure F V n :=
  s.extendSpinC χ hχ (MonoidHom.ext fun _ ↦ by simp)

/-- **The frame of `[p, 1]`** in the charge conjugate of a `Spinᶜ` structure is the frame of `p`. -/
@[simp]
theorem toFrame_chargeConj_inl (s : SpinCStructure F V n) (x : X) (p : s.P x) :
    s.chargeConj.toFrame ⟨x, Extend.inl χ hχ p⟩ = s.toFrame ⟨x, p⟩ :=
  s.toFrame_extendSpinC_inl χ hχ rotation_comp_chargeConj x p

/-- **The frame of `[p, h]`** in the charge conjugate of a `Spinᶜ` structure is the frame of `p`
composed with the rotation of `h`. -/
theorem toFrame_chargeConj_mk (s : SpinCStructure F V n) (x : X) (p : s.P x)
    (h : spinCGroup (realCliffordForm n 0) hQ) (v : Fin n → ℝ) :
    TotalSpace.mk' F (s.chargeConj.toFrame ⟨x, Extend.mk χ hχ p h⟩).proj
        ((s.chargeConj.toFrame ⟨x, Extend.mk χ hχ p h⟩).frame (WithLp.toLp 2 v)) =
      TotalSpace.mk' F (s.toFrame ⟨x, p⟩).proj
        ((s.toFrame ⟨x, p⟩).frame (WithLp.toLp 2 (πᶜ h v))) :=
  s.toFrame_extend_mk χ hχ rotation_comp_chargeConj hπn hπc x p h v

end SpinCStructure

/-! ### Functoriality and involutivity -/

namespace OrthonormalFrameLift

/-- **Charge conjugation is functorial**: an equivalence `s ≃ t` of `Spinᶜ` structures induces an
equivalence of their charge conjugates, by `[p, h] ↦ [φ p, h]`. -/
def Equiv.chargeConj {s t : SpinCStructure F V n} (φ : s.Equiv t) :
    s.chargeConj.Equiv t.chargeConj :=
  φ.extend χ hχ SpinCStructure.rotation_comp_chargeConj hπn hπc

@[simp]
theorem Equiv.chargeConj_toEquiv_mk {s t : SpinCStructure F V n} (φ : s.Equiv t) (x : X)
    (p : s.P x) (h : spinCGroup (realCliffordForm n 0) hQ) :
    φ.chargeConj.toEquiv x (Extend.mk χ hχ p h) = Extend.mk χ hχ (φ.toEquiv x p) h :=
  φ.extend_toEquiv_mk χ hχ SpinCStructure.rotation_comp_chargeConj hπn hπc x p h

end OrthonormalFrameLift

namespace SpinCStructure

/-- The map `[p, h] ↦ p • χ(h)` from the principal bundle of the charge conjugate back to that of
`s`: the composite of the identifications `(P ×_χ Spinᶜ(n)) ×_χ Spinᶜ(n) ≃ P ×_{χ ∘ χ} Spinᶜ(n)`,
`P ×_{χ ∘ χ} Spinᶜ(n) = P ×_{id} Spinᶜ(n)` and `P ×_{id} Spinᶜ(n) ≃ P`, applied to `[[p, h], 1]`. -/
private def chargeConjRetract (s : SpinCStructure F V n) (x : X) (q : s.chargeConj.P x) : s.P x :=
  Extend.idEquiv x (Extend.congrEquiv chargeConj_comp_chargeConj
    continuous_chargeConj_comp_chargeConj continuous_id x
      (Extend.compEquiv χ hχ χ hχ x (Extend.inl (P := Extend s.P χ hχ) χ hχ q)))

private theorem chargeConjRetract_mk (s : SpinCStructure F V n) (x : X) (p : s.P x)
    (h : spinCGroup (realCliffordForm n 0) hQ) :
    chargeConjRetract s x (Extend.mk χ hχ p h) = op (spinCGroup.chargeConj _ hQ h) • p := by
  unfold chargeConjRetract
  rw [Extend.inl_def, Extend.compEquiv_mk, mul_one, Extend.congrEquiv_mk, Extend.idEquiv_mk,
    MonoidHom.coe_ofClass]

private theorem chargeConjRetract_smul (s : SpinCStructure F V n) (x : X) (q : s.chargeConj.P x)
    (g : spinCGroup (realCliffordForm n 0) hQ) :
    chargeConjRetract s x (op g • q) = op (χ g) • chargeConjRetract s x q := by
  obtain ⟨p, h, rfl⟩ := Extend.exists_mk (P := s.P) (ρ := χ) (hρ := hχ) (b := x) q
  -- The action of `Spinᶜ(n)` on the fibre `s.chargeConj.P x` is that of `Extend s.P χ hχ x`, but
  -- `rw` cannot see through the fibre, so `Extend.smul_mk` is applied by `congrArg`.
  refine (congrArg (chargeConjRetract s x) (Extend.smul_mk χ hχ p h g)).trans ?_
  rw [chargeConjRetract_mk, chargeConjRetract_mk, map_mul, op_mul, mul_smul,
    MonoidHom.coe_ofClass]

private theorem continuous_chargeConjRetract (s : SpinCStructure F V n) :
    Continuous fun q : TotalSpace SpinC s.chargeConj.P ↦
      (⟨q.proj, chargeConjRetract s q.proj q.snd⟩ : TotalSpace SpinC s.P) :=
  (Extend.idHomeomorph.continuous.comp ((Extend.congrHomeomorph chargeConj_comp_chargeConj
    continuous_chargeConj_comp_chargeConj continuous_id).continuous.comp
      ((Extend.compHomeomorph χ hχ χ hχ).continuous.comp
        (Extend.continuous_inl (Extend s.P χ hχ) χ hχ)))).congr fun q ↦ by
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, Extend.compHomeomorph_apply,
      Extend.congrHomeomorph_apply, Extend.idHomeomorph_apply]
    rfl

private theorem toFrame_chargeConjRetract (s : SpinCStructure F V n) (x : X)
    (q : s.chargeConj.P x) :
    s.toFrame ⟨x, chargeConjRetract s x q⟩ = s.chargeConj.toFrame ⟨x, q⟩ := by
  obtain ⟨p, h, rfl⟩ := Extend.exists_mk (P := s.P) (ρ := χ) (hρ := hχ) (b := x) q
  refine OrthonormalFrameBundle.ext_totalSpaceMk fun v ↦ ?_
  rw [chargeConjRetract_mk, s.toFrame_smul, toFrame_chargeConj_mk]
  simp

/-- **Charge conjugation is involutive**: `s.chargeConj.chargeConj ≃ s`, by
`[[p, h], k] ↦ p • χ(h) k`, since `χ ∘ χ = id`. -/
def chargeConjChargeConjEquiv (s : SpinCStructure F V n) : s.chargeConj.chargeConj.Equiv s :=
  s.chargeConj.extendEquivOfEquivariant χ hχ rotation_comp_chargeConj hπn hπc s
    (chargeConjRetract s) (chargeConjRetract_smul s) (continuous_chargeConjRetract s)
    (toFrame_chargeConjRetract s)

@[simp]
theorem chargeConjChargeConjEquiv_toEquiv_mk (s : SpinCStructure F V n) (x : X) (p : s.P x)
    (h k : spinCGroup (realCliffordForm n 0) hQ) :
    (chargeConjChargeConjEquiv s).toEquiv x (Extend.mk χ hχ (Extend.mk χ hχ p h) k) =
      op (spinCGroup.chargeConj _ hQ h * k) • p := by
  refine (s.chargeConj.extendEquivOfEquivariant_toEquiv_mk χ hχ rotation_comp_chargeConj hπn hπc
    s (chargeConjRetract s) (chargeConjRetract_smul s) (continuous_chargeConjRetract s)
    (toFrame_chargeConjRetract s) x (Extend.mk χ hχ p h) k).trans ?_
  rw [chargeConjRetract_mk, smul_smul, ← op_mul]

end SpinCStructure

end Structure

/-! ### The determinant line -/

section DeterminantLine

variable {X : Type} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : X → Type} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]

namespace SpinCStructure

/-- Complex conjugation of the determinant model. -/
private def detConj : DeterminantModel n ≃L⋆[ℂ] DeterminantModel n :=
  (DeterminantModel.toComplex.toContinuousLinearEquiv.trans (starL ℂ)).trans
    DeterminantModel.toComplex.symm.toContinuousLinearEquiv

omit [NeZero n] in
private theorem toComplex_detConj (w : DeterminantModel n) :
    DeterminantModel.toComplex (detConj w) = starRingEnd ℂ (DeterminantModel.toComplex w) := by
  simp [detConj]

/-- Conjugation of the determinant model carries the action of `χ g` to that of `g`:
`conj (det (χ g) w) = det g (conj w)`, since `det (χ g) = (det g)⁻¹` lies on the circle. -/
private theorem detConj_chargeConj_smul (g : SpinC) (w : DeterminantModel n) :
    detConj (spinCGroup.chargeConj _ hQ g • w) = g • detConj w := by
  apply DeterminantModel.toComplex.injective
  rw [toComplex_detConj, DeterminantModel.toComplex_smul, DeterminantModel.toComplex_smul,
    toComplex_detConj, spinCGroup.det_chargeConj, map_mul, Circle.coe_inv_eq_conj,
    Complex.conj_conj]

/-- **The determinant line of the charge conjugate is the conjugate line**: the fibrewise
conjugate-linear isomorphism `L(s.chargeConj)_x ≃ L(s)_x`, `[[p, h], w] ↦ [p, conj (det h w)]`
(`TauCeti.SpinCStructure.determinantLineChargeConjEquiv_mk`). It is well defined because
`conj (det (χ g) w) = det g (conj w)`, and continuous on total spaces
(`TauCeti.SpinCStructure.continuous_determinantLineChargeConjEquiv`). -/
def determinantLineChargeConjEquiv (s : SpinCStructure F V n) (x : X) :
    s.chargeConj.determinantLine x ≃L⋆[ℂ] s.determinantLine x :=
  ((AssociatedBundle.mkContinuousLinearEquiv ℂ SpinC (F := DeterminantModel n)
      (Extend.inl χ hχ (Classical.arbitrary (s.P x)))).symm.trans detConj).trans
    (AssociatedBundle.mkContinuousLinearEquiv ℂ SpinC (Classical.arbitrary (s.P x)))

/-- The comparison of determinant lines through the frames `[p₀, 1]` and `p₀`, for the chosen
point `p₀` of `s.P x`, stated on the fibre `Extend s.P χ hχ` of the charge conjugate. -/
private theorem determinantLineChargeConjEquiv_apply (s : SpinCStructure F V n) {x : X}
    (z : AssociatedBundle SpinC (Extend s.P χ hχ) (DeterminantModel n) x) :
    s.determinantLineChargeConjEquiv x z =
      AssociatedBundle.mkContinuousLinearEquiv ℂ SpinC (Classical.arbitrary (s.P x))
        (detConj ((AssociatedBundle.mkContinuousLinearEquiv ℂ SpinC (F := DeterminantModel n)
          (Extend.inl χ hχ (Classical.arbitrary (s.P x)))).symm z)) :=
  (rfl)

/-- The comparison of determinant lines in terms of the conjugation of the determinant model. -/
private theorem determinantLineChargeConjEquiv_mk_eq_detConj (s : SpinCStructure F V n) {x : X}
    (p : s.P x) (h : SpinC) (w : DeterminantModel n) :
    s.determinantLineChargeConjEquiv x
        (AssociatedBundle.mk (P := Extend s.P χ hχ) SpinC (Extend.mk χ hχ p h) w) =
      AssociatedBundle.mk SpinC p (detConj (h • w)) := by
  rw [determinantLineChargeConjEquiv_apply, AssociatedBundle.mkContinuousLinearEquiv_symm_apply_mk,
    AssociatedBundle.mkContinuousLinearEquiv_apply, Extend.inl_def, Extend.division_mk, inv_one,
    one_mul, mul_smul, MonoidHom.coe_ofClass, detConj_chargeConj_smul,
    ← AssociatedBundle.mk_smul, PrincipalBundle.smul_division]

/-- **The comparison of determinant lines in a frame**: `[[p, h], w] ↦ [p, conj (det h w)]`. -/
theorem determinantLineChargeConjEquiv_mk (s : SpinCStructure F V n) {x : X} (p : s.P x)
    (h : SpinC) (w : DeterminantModel n) :
    s.determinantLineChargeConjEquiv x
        (AssociatedBundle.mk (P := Extend s.P χ hχ) SpinC (Extend.mk χ hχ p h) w) =
      AssociatedBundle.mk SpinC p (DeterminantModel.toComplex.symm
        (starRingEnd ℂ ((spinCGroup.det _ hQ h : ℂ) * DeterminantModel.toComplex w))) := by
  rw [determinantLineChargeConjEquiv_mk_eq_detConj, ← DeterminantModel.toComplex_smul,
    ← toComplex_detConj, LinearIsometryEquiv.symm_apply_apply]

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
        (AssociatedBundle.mk SpinC y.1.1.snd (detConj (y.1.2 • y.2))) :=
    Continuous.totalSpaceMk_associatedBundleMk
      (f := fun y : (TotalSpace SpinC s.P × SpinC) × DeterminantModel n ↦ y.1.1.proj)
      (continuous_fst.comp continuous_fst) (detConj.continuous.comp
        (continuous_smul.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))
  refine hc.congr fun y ↦ ?_
  exact (congrArg (TotalSpace.mk _)
    (determinantLineChargeConjEquiv_mk_eq_detConj s y.1.1.snd y.1.2 y.2)).symm

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

end DeterminantLine

end TauCeti

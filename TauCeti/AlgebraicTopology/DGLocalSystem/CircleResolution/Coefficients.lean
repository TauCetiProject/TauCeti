/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.CircleResolution
public import TauCeti.AlgebraicTopology.DGLocalSystem.Covering
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Coefficients

/-!
# The circle with coefficients in a DG local system concentrated in degree zero

Let `γ` be a Moore loop at `b` and `K` the free module of the twisting cocycle
`TauCeti.loopCellCocycle R γ`, with generators `e₀` of index `0` and `e₁` of index `1` and
`D e₁ = ([γ] - [1]) e₀`. For the complex unit circle and its counterclockwise loop
`Circle.expLoop`, `K` is Brown's semi-free resolution of `R` over the chains `C_*(Ω S¹; R)` on the
Moore loops
(`TauCeti.exists_loopCellCocycle_expLoop_differential_eq_of_loopCellAugmentation_eq_zero`), so
the twisted complex `𝓕 ⊗ K` with coefficients in a DG local system `𝓕` represents the derived
tensor product `𝓕 ⊗^𝐋 R`, the homology of the circle with coefficients in `𝓕`
(`TauCeti.nonempty_loopCellCocycle_localizedFunctor_iso_derivedTensor_loopChainAugmentation`).
For other loops going once around a circle, such as `AddCircle.zsmulLoop 1 0 1` on `ℝ ⧸ ℤ`, this
is expected but not proved; the computation below does not use it and holds for any Moore loop.

This file computes that twisted complex when `𝓕` is concentrated in degree zero, as the DG local
system of a covering map is (`IsCoveringMap.isConcentratedInDegreeZero_liftingLocalSystem`). Write
`T` for the action of the point chain `[γ]` on `𝓕`, the action
`DGRightModuleCat.IsConcentratedInDegreeZero.representation` of the inverse of the class of `γ` in
the fundamental group. The complex has two nonzero terms, `𝓕 e₁` in degree `-1` and `𝓕 e₀` in
degree `0`, and its differential sends `α e₁` to `(T α - α) e₀`
(`TauCeti.loopCellCocycle_coefficientDifferential_single_inr`). So, through the grading bridge
`C^{-q} = C_q`,

* `H₀` is the module of coinvariants `𝓕 ⧸ range (T - 1)`
  (`TauCeti.loopCellCocycleHomologyZeroIso`);
* `H₁` is the module of invariants `ker (T - 1)`
  (`TauCeti.loopCellCocycleHomologyNegOneIso`);
* all other homology vanishes (`TauCeti.isZero_loopCellCocycle_coefficientCochainComplex_homology`).

This is the classical computation of the homology of the circle with local coefficients. For the
singular homology of the circle with a classical local system the same modules appear
(`TauCeti.circleTwistedHomologyIso₀`, `TauCeti.circleTwistedHomologyIso₁`); here they are computed
on the twisted complex of the DG local system, the complex that Brown's model and the DG Morse
complex produce.

For the double cover `x ↦ 2 • x` of `ℝ ⧸ ℤ`, whose DG local system is `R²` with the generator of
the fundamental group acting by the swap
(`TauCeti.representation_liftingLocalSystemEquiv_addCircleDoubleCover`), the coinvariants are
`R` through the sum of the coordinates and the invariants are the diagonal `R`. So the twisted
homology is `R` in degrees `0` and `-1` and vanishes elsewhere
(`TauCeti.nonempty_loopCellCocycle_homology_iso_addCircleDoubleCover`): it is the homology of
the total space `S¹` of the cover, as the fibration theorem predicts. With the trivial action of
the loops on `R²` it would be `R²` in both degrees
(`TauCeti.nonempty_loopCellCocycle_homology_iso_of_forall_op_smul_eq`), the homology of the total
space `S¹ ⊔ S¹` of the trivial double cover, so the monodromy is visible in the twisted homology.

## Main definitions

* `TauCeti.loopCellCocycleHomologyZeroIso`: `H⁰(𝓕 ⊗ K)` is the module of coinvariants of `T`.
* `TauCeti.loopCellCocycleHomologyNegOneIso`: `H⁻¹(𝓕 ⊗ K)` is the module of invariants of `T`.

## Main results

* `TauCeti.loopCellCocycle_coefficientDifferential_single_inl`,
  `TauCeti.loopCellCocycle_coefficientDifferential_single_inr`: the differential of the twisted
  complex.
* `TauCeti.loopCellCocycleHomologyZeroIso_hom_homologyπ`,
  `TauCeti.coe_loopCellCocycleHomologyNegOneIso_hom_homologyπ`: the two isomorphisms read off the
  coefficient of `e₀`, respectively `e₁`, of a cycle.
* `TauCeti.isZero_loopCellCocycle_coefficientCochainComplex_homology`: the twisted homology
  vanishes outside degrees `0` and `-1`.
* `TauCeti.nonempty_loopCellCocycle_homology_iso_of_forall_op_smul_eq`: with the trivial action
  the twisted homology is `𝓕` in degrees `0` and `-1`.
* `TauCeti.nonempty_loopCellCocycle_homology_iso_addCircleDoubleCover`: for the double cover of the
  circle, the twisted homology is `R` in degrees `0` and `-1`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 7 (the fibration
  theorem).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.H (homology with
  local coefficients).
-/

public noncomputable section

open CategoryTheory Limits MulOpposite

universe u w

namespace TauCeti

variable {R : Type u} [CommRing R] {B : TopCat.{u}} {b : B} {𝓕 : DGLocalSystem.{w} B b R}
  (h𝓕 : 𝓕.IsConcentratedInDegreeZero) (γ : MooreLoopSpace B b)

/-! ### The differential -/

section Differential

include h𝓕

/-- On a DG local system concentrated in degree zero, the differential of the twisted complex of
`TauCeti.loopCellCocycle R γ` vanishes on the vectors `α e₀`. -/
theorem loopCellCocycle_coefficientDifferential_single_inl (α : 𝓕) :
    (loopCellCocycle R γ).coefficientDifferential 𝓕.isDGRightModule
      (Finsupp.single (Sum.inl ()) α) = 0 := by
  rw [(loopCellCocycle R γ).coefficientDifferential_single _ _ (h𝓕.mem_grading_zero α),
    h𝓕.differential_eq_zero, loopCellCocycle_m_inl]
  simp

/-- On a DG local system concentrated in degree zero, the differential of the twisted complex of
`TauCeti.loopCellCocycle R γ` sends `α e₁` to `([γ] α - α) e₀`. -/
theorem loopCellCocycle_coefficientDifferential_single_inr (α : 𝓕) :
    (loopCellCocycle R γ).coefficientDifferential 𝓕.isDGRightModule
        (Finsupp.single (Sum.inr ()) α) =
      Finsupp.single (Sum.inl ())
        (op (cubicalChainPoint (MooreLoopSpace B b) R γ) • α - α) := by
  rw [(loopCellCocycle R γ).coefficientDifferential_single _ _ (h𝓕.mem_grading_zero α),
    h𝓕.differential_eq_zero, loopCellCocycle_m_inr, Finsupp.sum_single_index (by simp)]
  simp [sub_smul]

end Differential

/-! ### The terms of the twisted complex -/

section Terms

/-- The indices of the generators `e₀` and `e₁`. -/
local notation "ι" => (Sum.elim (fun _ ↦ 0) (fun _ ↦ 1) : Unit ⊕ Unit → ℤ)

/-- A vector of the twisted complex is determined by its values at `e₀` and `e₁`. -/
private theorem eq_single_add_single (f : Unit ⊕ Unit →₀ 𝓕) :
    f = Finsupp.single (Sum.inl ()) (f (Sum.inl ())) +
      Finsupp.single (Sum.inr ()) (f (Sum.inr ())) := by
  ext (⟨⟩ | ⟨⟩) <;> simp

include h𝓕

/-- A vector of total degree `n` of the twisted complex vanishes at `e₀` unless `n = 0`. -/
private theorem apply_inl_eq_zero {n : ℤ} (hn : n ≠ 0) {f : Unit ⊕ Unit →₀ 𝓕}
    (hf : f ∈ rowFiniteTotalGrading 𝓕.grading ι n) : f (Sum.inl ()) = 0 := by
  have := (mem_rowFiniteTotalGrading_iff _ _).1 hf (Sum.inl ())
  simp only [Sum.elim_inl, add_zero, h𝓕.mem_grading_iff] at this
  exact this.resolve_left hn

/-- A vector of total degree `n` of the twisted complex vanishes at `e₁` unless `n = -1`. -/
private theorem apply_inr_eq_zero {n : ℤ} (hn : n ≠ -1) {f : Unit ⊕ Unit →₀ 𝓕}
    (hf : f ∈ rowFiniteTotalGrading 𝓕.grading ι n) : f (Sum.inr ()) = 0 := by
  have := (mem_rowFiniteTotalGrading_iff _ _).1 hf (Sum.inr ())
  simp only [Sum.elim_inr, h𝓕.mem_grading_iff] at this
  exact this.resolve_left fun h ↦ hn (by omega)

/-- The twisted complex vanishes outside degrees `0` and `-1`. -/
theorem subsingleton_loopCellCocycle_coefficientCochainComplex_X {n : ℤ} (h₀ : n ≠ 0)
    (h₁ : n ≠ -1) :
    Subsingleton (((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).X n) := by
  refine ((loopCellCocycle R γ).coefficientCochainComplexXEquiv 𝓕.isDGRightModule n).toEquiv
    |>.subsingleton_congr.2 ⟨fun f g ↦ Subtype.ext ?_⟩
  rw [eq_single_add_single (f : Unit ⊕ Unit →₀ 𝓕), eq_single_add_single (g : Unit ⊕ Unit →₀ 𝓕),
    apply_inl_eq_zero h𝓕 h₀ f.property, apply_inr_eq_zero h𝓕 h₁ f.property,
    apply_inl_eq_zero h𝓕 h₀ g.property, apply_inr_eq_zero h𝓕 h₁ g.property]

/-- The vectors of total degree `0` of the twisted complex are the vectors `α e₀`. -/
private def gradingZeroEquiv : rowFiniteTotalGrading 𝓕.grading ι 0 ≃ₗ[R] 𝓕 where
  toFun f := (f : Unit ⊕ Unit →₀ 𝓕) (Sum.inl ())
  invFun α := ⟨Finsupp.single (Sum.inl ()) α, (mem_rowFiniteTotalGrading_iff _ _).2 fun x ↦ by
    rcases x with ⟨⟩ | ⟨⟩
    · simpa using h𝓕.mem_grading_zero α
    · simp⟩
  left_inv f := Subtype.ext <| by
    conv_rhs => rw [eq_single_add_single (f : Unit ⊕ Unit →₀ 𝓕),
      apply_inr_eq_zero h𝓕 (by norm_num) f.property]
    simp
  right_inv α := by simp
  map_add' f g := by simp
  map_smul' r f := by simp

/-- The vectors of total degree `-1` of the twisted complex are the vectors `α e₁`. -/
private def gradingNegOneEquiv : rowFiniteTotalGrading 𝓕.grading ι (-1) ≃ₗ[R] 𝓕 where
  toFun f := (f : Unit ⊕ Unit →₀ 𝓕) (Sum.inr ())
  invFun α := ⟨Finsupp.single (Sum.inr ()) α, (mem_rowFiniteTotalGrading_iff _ _).2 fun x ↦ by
    rcases x with ⟨⟩ | ⟨⟩
    · simp
    · simpa using h𝓕.mem_grading_zero α⟩
  left_inv f := Subtype.ext <| by
    conv_rhs => rw [eq_single_add_single (f : Unit ⊕ Unit →₀ 𝓕),
      apply_inl_eq_zero h𝓕 (by norm_num) f.property]
    simp
  right_inv α := by simp
  map_add' f g := by simp
  map_smul' r f := by simp

/-- The term of degree `0` of the twisted complex is `𝓕 e₀`. -/
private def xZeroEquiv :
    ((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).X 0 ≃ₗ[R] 𝓕 :=
  ((loopCellCocycle R γ).coefficientCochainComplexXEquiv 𝓕.isDGRightModule 0).trans
    (gradingZeroEquiv h𝓕)

/-- The term of degree `-1` of the twisted complex is `𝓕 e₁`. -/
private def xNegOneEquiv :
    ((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).X (-1) ≃ₗ[R] 𝓕 :=
  ((loopCellCocycle R γ).coefficientCochainComplexXEquiv 𝓕.isDGRightModule (-1)).trans
    (gradingNegOneEquiv h𝓕)

/-- The term of degree `0` is read on `𝓕` through the coefficient of `e₀`. -/
private theorem xZeroEquiv_apply
    (x : ((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).X 0) :
    xZeroEquiv h𝓕 γ x =
      ((loopCellCocycle R γ).coefficientCochainComplexXEquiv 𝓕.isDGRightModule 0 x :
        Unit ⊕ Unit →₀ 𝓕) (Sum.inl ()) :=
  (rfl)

/-- The term of degree `-1` is read on `𝓕` through the coefficient of `e₁`. -/
private theorem xNegOneEquiv_apply
    (x : ((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).X (-1)) :
    xNegOneEquiv h𝓕 γ x =
      ((loopCellCocycle R γ).coefficientCochainComplexXEquiv 𝓕.isDGRightModule (-1) x :
        Unit ⊕ Unit →₀ 𝓕) (Sum.inr ()) :=
  (rfl)

/-- The differential from degree `-1` to degree `0`, read on `𝓕`, is `α ↦ [γ] α - α`. -/
private theorem xZeroEquiv_d {i : ℤ} (hi : i + 1 = 0)
    (x : ((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).X i) :
    xZeroEquiv h𝓕 γ
        ((((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).d i 0).hom x) =
      op (cubicalChainPoint (MooreLoopSpace B b) R γ) •
          (((loopCellCocycle R γ).coefficientCochainComplexXEquiv 𝓕.isDGRightModule i x :
            Unit ⊕ Unit →₀ 𝓕) (Sum.inr ())) -
        ((loopCellCocycle R γ).coefficientCochainComplexXEquiv 𝓕.isDGRightModule i x :
          Unit ⊕ Unit →₀ 𝓕) (Sum.inr ()) := by
  obtain rfl : i = -1 := by omega
  set f := ((loopCellCocycle R γ).coefficientCochainComplexXEquiv 𝓕.isDGRightModule (-1) x :
    Unit ⊕ Unit →₀ 𝓕)
  -- `coefficientCochainComplexXEquiv_d` is stated for the differential into degree `-1 + 1`,
  -- which is the numeral `0` by evaluation.
  have hd : ((loopCellCocycle R γ).coefficientCochainComplexXEquiv 𝓕.isDGRightModule 0
      ((((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).d (-1) 0).hom x) :
        Unit ⊕ Unit →₀ 𝓕) =
      (loopCellCocycle R γ).coefficientDifferential 𝓕.isDGRightModule f :=
    (loopCellCocycle R γ).coefficientCochainComplexXEquiv_d 𝓕.isDGRightModule (-1) x
  rw [xZeroEquiv_apply, hd, eq_single_add_single f, apply_inl_eq_zero h𝓕 (by norm_num)
    ((loopCellCocycle R γ).coefficientCochainComplexXEquiv 𝓕.isDGRightModule (-1) x).property,
    Finsupp.single_zero, zero_add, loopCellCocycle_coefficientDifferential_single_inr h𝓕]
  simp

/-- The differential from degree `-1` to degree `0` vanishes on `x` exactly when the coefficient
`α` of `e₁` satisfies `[γ] α = α`. -/
private theorem d_eq_zero_iff {j : ℤ} (hj : -1 + 1 = j)
    (x : ((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).X (-1)) :
    (((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).d (-1) j).hom x = 0 ↔
      op (cubicalChainPoint (MooreLoopSpace B b) R γ) • xNegOneEquiv h𝓕 γ x -
        xNegOneEquiv h𝓕 γ x = 0 := by
  obtain rfl : j = 0 := by omega
  rw [← (xZeroEquiv h𝓕 γ).map_eq_zero_iff, xZeroEquiv_d h𝓕 γ (by norm_num), xNegOneEquiv_apply]

/-- `T - 1` sends `α` to `[γ] α - α`, where `T` is the action of the point chain of `γ`. -/
private theorem representation_inv_sub_one_apply (α : 𝓕) :
    (h𝓕.representation (MooreLoopSpace.fundamentalGroupHom b γ)⁻¹ - 1) α =
      op (cubicalChainPoint (MooreLoopSpace B b) R γ) • α - α := by
  rw [LinearMap.sub_apply, h𝓕.representation_fundamentalGroupHom_inv_apply, one_apply_eq_self]

/-- The image of the differential into degree `0`, read on `𝓕`, is the range of `T - 1`, where `T`
is the action of the point chain of `γ`. -/
private theorem map_range_d {i : ℤ} (hi : i + 1 = 0) :
    (LinearMap.range
        (((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).d i 0).hom).map
        (xZeroEquiv h𝓕 γ : _ →ₗ[R] 𝓕) =
      LinearMap.range (h𝓕.representation (MooreLoopSpace.fundamentalGroupHom b γ)⁻¹ - 1) := by
  ext α
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨((loopCellCocycle R γ).coefficientCochainComplexXEquiv 𝓕.isDGRightModule i x :
      Unit ⊕ Unit →₀ 𝓕) (Sum.inr ()), ?_⟩
    rw [representation_inv_sub_one_apply, xZeroEquiv_d h𝓕 γ hi]
  · rintro ⟨β, rfl⟩
    obtain rfl : i = -1 := by omega
    refine ⟨_, ⟨(xNegOneEquiv h𝓕 γ).symm β, rfl⟩, ?_⟩
    rw [xZeroEquiv_d h𝓕 γ hi, representation_inv_sub_one_apply, ← xNegOneEquiv_apply h𝓕,
      LinearEquiv.apply_symm_apply]

/-- The cycles of degree `-1`, read on `𝓕`, are the kernel of `T - 1`, where `T` is the action of
the point chain of `γ`. -/
private theorem map_ker_d {j : ℤ} (hj : -1 + 1 = j) :
    (LinearMap.ker
        (((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).d (-1) j).hom).map
        (xNegOneEquiv h𝓕 γ : _ →ₗ[R] 𝓕) =
      LinearMap.ker (h𝓕.representation (MooreLoopSpace.fundamentalGroupHom b γ)⁻¹ - 1) := by
  ext α
  rw [Submodule.mem_map_equiv, LinearMap.mem_ker, d_eq_zero_iff h𝓕 γ hj,
    LinearEquiv.apply_symm_apply, LinearMap.mem_ker, representation_inv_sub_one_apply]

end Terms

/-! ### The homology of the twisted complex -/

section Homology

include h𝓕

/-- **The twisted homology of the circle in degree `0` is the module of coinvariants**: the
homology of degree `0` of the twisted complex of `TauCeti.loopCellCocycle R γ` with coefficients
in a DG local system `𝓕` concentrated in degree zero is `𝓕 ⧸ range (T - 1)`, where `T` is the
action of the point chain of `γ`, the action of the inverse of the class of `γ`
(`DGRightModuleCat.IsConcentratedInDegreeZero.representation_fundamentalGroupHom_inv_apply`). -/
def loopCellCocycleHomologyZeroIso :
    ((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).homology 0 ≅
      ModuleCat.of R (𝓕 ⧸ LinearMap.range
        (h𝓕.representation (MooreLoopSpace.fundamentalGroupHom b γ)⁻¹ - 1)) :=
  have := subsingleton_loopCellCocycle_coefficientCochainComplex_X h𝓕 γ (n := 1) (by norm_num)
    (by norm_num)
  ((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).isoHomologyι 0 1
      (by simp) ((ModuleCat.isZero_of_subsingleton _).eq_of_tgt _ _) ≪≫
    (((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).sc
      0).moduleCatOpcyclesIso ≪≫
    (Submodule.Quotient.equiv _ _ (xZeroEquiv h𝓕 γ) (map_range_d h𝓕 γ (by simp))).toModuleIso

/-- **The twisted homology of the circle in degree `-1` is the module of invariants**: the
homology of degree `-1` of the twisted complex of `TauCeti.loopCellCocycle R γ` with coefficients
in a DG local system `𝓕` concentrated in degree zero is `ker (T - 1)`, where `T` is the action of
the point chain of `γ`, the action of the inverse of the class of `γ`
(`DGRightModuleCat.IsConcentratedInDegreeZero.representation_fundamentalGroupHom_inv_apply`). -/
def loopCellCocycleHomologyNegOneIso :
    ((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).homology (-1) ≅
      ModuleCat.of R (LinearMap.ker
        (h𝓕.representation (MooreLoopSpace.fundamentalGroupHom b γ)⁻¹ - 1)) :=
  have := subsingleton_loopCellCocycle_coefficientCochainComplex_X h𝓕 γ (n := -2) (by norm_num)
    (by norm_num)
  (((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).isoHomologyπ (-2) (-1)
      (by simp) ((ModuleCat.isZero_of_subsingleton _).eq_of_src _ _)).symm ≪≫
    (((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).sc
      (-1)).moduleCatCyclesIso ≪≫
    (LinearEquiv.ofSubmodules (xNegOneEquiv h𝓕 γ) _ _ (map_ker_d h𝓕 γ (by simp))).toModuleIso

/-- The isomorphism `TauCeti.loopCellCocycleHomologyZeroIso` sends the class of a cycle to the
class of its coefficient of `e₀`. -/
@[simp]
theorem loopCellCocycleHomologyZeroIso_hom_homologyπ
    (z : ((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).cycles 0) :
    (loopCellCocycleHomologyZeroIso h𝓕 γ).hom
        (((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).homologyπ 0 z) =
      Submodule.Quotient.mk (((loopCellCocycle R γ).coefficientCochainComplexXEquiv
        𝓕.isDGRightModule 0
          (((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).iCycles 0 z) :
            Unit ⊕ Unit →₀ 𝓕) (Sum.inl ())) := by
  have h := congr($(((loopCellCocycle R γ).coefficientCochainComplex
    𝓕.isDGRightModule).homology_π_ι 0) z)
  simp only [ConcreteCategory.comp_apply] at h
  simp only [loopCellCocycleHomologyZeroIso, Iso.trans_hom, ConcreteCategory.comp_apply,
    HomologicalComplex.isoHomologyι_hom, h, LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom,
    LinearEquiv.coe_coe, Submodule.Quotient.equiv_apply]
  -- Unfold `HomologicalComplex.pOpcycles` to the `pOpcycles` of the short complex `sc 0`.
  rw [HomologicalComplex.pOpcycles, ShortComplex.pOpcycles_comp_moduleCatOpcyclesIso_hom_apply]
  rw [Submodule.mapQ_apply, LinearEquiv.coe_coe, xZeroEquiv_apply]

/-- The isomorphism `TauCeti.loopCellCocycleHomologyNegOneIso` sends the class of a cycle to its
coefficient of `e₁`. -/
@[simp]
theorem coe_loopCellCocycleHomologyNegOneIso_hom_homologyπ
    (z : ((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).cycles (-1)) :
    ((loopCellCocycleHomologyNegOneIso h𝓕 γ).hom
        (((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).homologyπ (-1) z) :
          𝓕) =
      ((loopCellCocycle R γ).coefficientCochainComplexXEquiv 𝓕.isDGRightModule (-1)
        (((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).iCycles (-1) z) :
          Unit ⊕ Unit →₀ 𝓕) (Sum.inr ()) := by
  rw [← ConcreteCategory.comp_apply]
  simp only [loopCellCocycleHomologyNegOneIso, Iso.trans_hom, Iso.symm_hom,
    HomologicalComplex.isoHomologyπ_hom_inv_id_assoc, ConcreteCategory.comp_apply,
    LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom, LinearEquiv.coe_coe]
  have hz := congr($((((loopCellCocycle R γ).coefficientCochainComplex
    𝓕.isDGRightModule).sc (-1)).moduleCatCyclesIso_hom_i) z)
  simp only [ConcreteCategory.comp_apply, ShortComplex.moduleCatLeftHomologyData_i_hom] at hz
  rw [LinearEquiv.ofSubmodules_apply, xNegOneEquiv_apply]
  -- `hz` reads the inclusion of the kernel as `Submodule.subtype` and the cycles through the short
  -- complex `sc (-1)`, whose `iCycles` is by definition `HomologicalComplex.iCycles`.
  exact congrArg (fun v ↦ ((loopCellCocycle R γ).coefficientCochainComplexXEquiv
    𝓕.isDGRightModule (-1) v : Unit ⊕ Unit →₀ 𝓕) (Sum.inr ())) hz

/-- The twisted homology of the circle with coefficients in a DG local system concentrated in
degree zero vanishes outside degrees `0` and `-1`. -/
theorem isZero_loopCellCocycle_coefficientCochainComplex_homology {n : ℤ} (h₀ : n ≠ 0)
    (h₁ : n ≠ -1) :
    IsZero (((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).homology n) :=
  have := subsingleton_loopCellCocycle_coefficientCochainComplex_X h𝓕 γ h₀ h₁
  ShortComplex.isZero_homology_of_isZero_X₂ _
    (ModuleCat.isZero_of_subsingleton
      (((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).X n))

/-- **With the trivial action the twisted homology is `𝓕` in degrees `0` and `-1`.** If the point
chain of `γ` acts trivially on a DG local system `𝓕` concentrated in degree zero, the twisted
homology of the circle is `𝓕` in degrees `0` and `-1`, the homology of the circle with constant
coefficients `𝓕`. -/
theorem nonempty_loopCellCocycle_homology_iso_of_forall_op_smul_eq
    (h : ∀ α : 𝓕, op (cubicalChainPoint (MooreLoopSpace B b) R γ) • α = α) :
    Nonempty (((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).homology 0 ≅
        ModuleCat.of R 𝓕) ∧
      Nonempty (((loopCellCocycle R γ).coefficientCochainComplex 𝓕.isDGRightModule).homology (-1) ≅
        ModuleCat.of R 𝓕) := by
  have hT : h𝓕.representation (MooreLoopSpace.fundamentalGroupHom b γ)⁻¹ - 1 = 0 :=
    LinearMap.ext fun α ↦ by
      rw [representation_inv_sub_one_apply, h, sub_self, LinearMap.zero_apply]
  refine ⟨⟨loopCellCocycleHomologyZeroIso h𝓕 γ ≪≫
    (Submodule.quotEquivOfEqBot _ (by rw [hT, LinearMap.range_zero])).toModuleIso⟩,
    ⟨loopCellCocycleHomologyNegOneIso h𝓕 γ ≪≫
      (LinearEquiv.ofTop _ (by rw [hT, LinearMap.ker_zero])).toModuleIso⟩⟩

end Homology

/-! ### The double cover of the circle -/

section DoubleCover

/-- The fibre of the double cover `x ↦ 2 • x` of `ℝ ⧸ ℤ` over `0`. -/
local notation "Fib" =>
  {e : AddCircle (1 : ℝ) // addCircleDoubleCover e = ((0 : ℝ) : AddCircle (1 : ℝ))}

/-- The point `0` of the fibre. -/
private def fibZero : Fib := ⟨_, addCircleDoubleCover_zero⟩

/-- The point `1 / 2` of the fibre. -/
private def fibHalf : Fib := ⟨_, addCircleDoubleCover_half⟩

/-- A vector supported at `0` vanishes at `1 / 2`. -/
@[simp]
private theorem single_fibZero_apply_fibHalf {R : Type*} [AddCommMonoid R] (a : R) :
    Finsupp.single fibZero a fibHalf = 0 :=
  Finsupp.single_eq_of_ne' addCircleDoubleCover_zero_ne_half

/-- A vector supported at `1 / 2` vanishes at `0`. -/
@[simp]
private theorem single_fibHalf_apply_fibZero {R : Type*} [AddCommMonoid R] (a : R) :
    Finsupp.single fibHalf a fibZero = 0 :=
  Finsupp.single_eq_of_ne addCircleDoubleCover_zero_ne_half

/-- A coefficient vector on the fibre is determined by its values at `0` and `1 / 2`. -/
private theorem eq_single_fibZero_add_single_fibHalf {R : Type*} [AddCommMonoid R] (w : Fib →₀ R) :
    w = Finsupp.single fibZero (w fibZero) + Finsupp.single fibHalf (w fibHalf) := by
  ext q
  obtain rfl | rfl : q = fibZero ∨ q = fibHalf := addCircleDoubleCover_fiber_eq_zero_or_eq_half q
  all_goals simp

section Swap

/-! The coinvariants and invariants of the swap of the two coordinates of `R²`, read on a module
`M` through a linear equivalence `e : R² ≃ M`. -/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (e : (Fib →₀ R) ≃ₗ[R] M)
  {T : M →ₗ[R] M}

/-- The sum of the two coordinates. -/
private def fibSum : M →ₗ[R] R :=
  Finsupp.linearCombination R (fun _ : Fib ↦ (1 : R)) ∘ₗ e.symm.toLinearMap

private theorem fibSum_apply (w : Fib →₀ R) : fibSum e (e w) = w fibZero + w fibHalf := by
  conv_lhs => rw [eq_single_fibZero_add_single_fibHalf w]
  simp [fibSum]

private theorem surjective_fibSum : Function.Surjective (fibSum e) := fun r ↦
  ⟨e (Finsupp.single fibZero r), by
    simp [fibSum_apply]⟩

/-- The diagonal. -/
private def fibDiag : R →ₗ[R] M :=
  e.toLinearMap ∘ₗ (Finsupp.lsingle fibZero + Finsupp.lsingle fibHalf)

private theorem fibDiag_apply (r : R) :
    fibDiag e r = e (Finsupp.single fibZero r + Finsupp.single fibHalf r) :=
  (rfl)

private theorem injective_fibDiag : Function.Injective (fibDiag e) := fun r s hrs ↦ by
  have := congrArg (· fibZero)
    (e.injective ((fibDiag_apply e r).symm.trans (hrs.trans (fibDiag_apply e s))))
  simpa using this

variable {e}

/-- The coinvariants of the swap are the kernel of the sum of the coordinates. -/
private theorem range_sub_one_eq_ker_fibSum
    (hT : ∀ w : Fib →₀ R,
      T (e w) = e (Finsupp.single fibHalf (w fibZero) + Finsupp.single fibZero (w fibHalf))) :
    LinearMap.range (T - 1) = LinearMap.ker (fibSum e) := by
  ext α
  obtain ⟨w, rfl⟩ := e.surjective α
  rw [LinearMap.mem_range, LinearMap.mem_ker, fibSum_apply]
  constructor
  · rintro ⟨β, hβ⟩
    obtain ⟨v, rfl⟩ := e.surjective β
    rw [LinearMap.sub_apply, one_apply_eq_self, hT, ← map_sub] at hβ
    rw [← e.injective hβ]
    simp only [Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_eq_same,
      single_fibZero_apply_fibHalf, single_fibHalf_apply_fibZero, add_zero, zero_add]
    abel
  · intro hw
    refine ⟨e (Finsupp.single fibZero (w fibHalf)), ?_⟩
    rw [LinearMap.sub_apply, one_apply_eq_self, hT, ← map_sub]
    congr 1
    conv_rhs => rw [eq_single_fibZero_add_single_fibHalf w, eq_neg_of_add_eq_zero_left hw]
    simp only [Finsupp.single_eq_same, single_fibZero_apply_fibHalf, Finsupp.single_zero,
      add_zero, Finsupp.single_neg]
    abel

/-- The invariants of the swap are the diagonal. -/
private theorem ker_sub_one_eq_range_fibDiag
    (hT : ∀ w : Fib →₀ R,
      T (e w) = e (Finsupp.single fibHalf (w fibZero) + Finsupp.single fibZero (w fibHalf))) :
    LinearMap.ker (T - 1) = LinearMap.range (fibDiag e) := by
  ext α
  obtain ⟨w, rfl⟩ := e.surjective α
  rw [LinearMap.mem_ker, LinearMap.mem_range, LinearMap.sub_apply, one_apply_eq_self, hT,
    sub_eq_zero]
  constructor
  · intro hw
    have h₁ : w fibZero = w fibHalf := by
      simpa using congrArg (· fibHalf) (e.injective hw)
    refine ⟨w fibZero, ?_⟩
    rw [fibDiag_apply]
    conv_rhs => rw [eq_single_fibZero_add_single_fibHalf w, ← h₁]
  · rintro ⟨r, hr⟩
    rw [fibDiag_apply] at hr
    rw [← e.injective hr]
    simp [add_comm]

end Swap

variable {R : Type} [CommRing R]
  (Φ : MooreLiftingFunction addCircleDoubleCover)
  {γ : MooreLoopSpace (AddCircle (1 : ℝ)) ((0 : ℝ) : AddCircle (1 : ℝ))}

/-- **The twisted homology of the circle with coefficients in its double cover is the homology of
the circle.** Let `γ` be a Moore loop at `0` whose class is the generator `[t ↦ t]` of the
fundamental group of `ℝ ⧸ ℤ`, the class of `AddCircle.zsmulLoop 1 0 1`. (This is the loop for
which `TauCeti.loopCellCocycle R γ` is expected to be Brown's resolution over the chains on the
loops; that is motivation only, proved for the complex unit circle and `Circle.expLoop`, and not
used here.) With coefficients in the DG local system of the double cover `x ↦ 2 • x`, which is
`R²` with the generator swapping the two coordinates, the twisted complex has homology `R` in
degrees `0` and `-1`: the coinvariants and the invariants of the swap. Through the grading bridge
`C^{-q} = C_q` this is the homology of the total space `S¹` of the cover, and not `R²`, the
homology of `S¹ ⊔ S¹` that the trivial action would give
(`TauCeti.nonempty_loopCellCocycle_homology_iso_of_forall_op_smul_eq`). The homology in all other
degrees vanishes (`TauCeti.isZero_loopCellCocycle_coefficientCochainComplex_homology`). -/
theorem nonempty_loopCellCocycle_homology_iso_addCircleDoubleCover
    (hγ : MooreLoopSpace.fundamentalGroupHom _ γ =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (AddCircle.zsmulLoop 1 0 1))) :
    letI := (isCoveringMap_addCircleDoubleCover.isTransitive Φ).mulAction
      ((0 : ℝ) : AddCircle (1 : ℝ))
    letI := (isCoveringMap_addCircleDoubleCover.isTransitive Φ).continuousSMul
      ((0 : ℝ) : AddCircle (1 : ℝ))
    Nonempty (((loopCellCocycle R γ).coefficientCochainComplex
          (liftingLocalSystem (R := R) (isCoveringMap_addCircleDoubleCover.isTransitive Φ)
            ((0 : ℝ) : AddCircle (1 : ℝ))).isDGRightModule).homology 0 ≅ ModuleCat.of R R) ∧
      Nonempty (((loopCellCocycle R γ).coefficientCochainComplex
          (liftingLocalSystem (R := R) (isCoveringMap_addCircleDoubleCover.isTransitive Φ)
            ((0 : ℝ) : AddCircle (1 : ℝ))).isDGRightModule).homology (-1) ≅
        ModuleCat.of R R) := by
  set h𝓕 := isCoveringMap_addCircleDoubleCover.isConcentratedInDegreeZero_liftingLocalSystem R Φ
    (B := TopCat.of (AddCircle (1 : ℝ))) ((0 : ℝ) : AddCircle (1 : ℝ))
  set e := isCoveringMap_addCircleDoubleCover.liftingLocalSystemEquiv R Φ
    (B := TopCat.of (AddCircle (1 : ℝ))) ((0 : ℝ) : AddCircle (1 : ℝ))
  set T := h𝓕.representation (MooreLoopSpace.fundamentalGroupHom _ γ)⁻¹ with hT_def
  set g := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (AddCircle.zsmulLoop 1 0 1))
  -- The point chain of `γ` acts as the inverse of the generator `g`, which swaps the two sheets.
  have hswap := representation_liftingLocalSystemEquiv_addCircleDoubleCover (R := R) Φ
  have hinv (x) : T (h𝓕.representation g x) = x := by
    rw [hT_def, hγ, Representation.inv_self_apply]
  have hT₀ (r : R) : T (e (Finsupp.single fibZero r)) = e (Finsupp.single fibHalf r) := by
    have h : h𝓕.representation g (e (Finsupp.single fibHalf r)) =
        e (Finsupp.single fibZero r) := (hswap r).2
    rw [← h, hinv]
  have hT₁ (r : R) : T (e (Finsupp.single fibHalf r)) = e (Finsupp.single fibZero r) := by
    have h : h𝓕.representation g (e (Finsupp.single fibZero r)) =
        e (Finsupp.single fibHalf r) := (hswap r).1
    rw [← h, hinv]
  have hT (w : Fib →₀ R) : T (e w) =
      e (Finsupp.single fibHalf (w fibZero) + Finsupp.single fibZero (w fibHalf)) := by
    conv_lhs => rw [eq_single_fibZero_add_single_fibHalf w]
    rw [map_add, map_add, hT₀, hT₁, map_add]
  exact ⟨⟨loopCellCocycleHomologyZeroIso h𝓕 γ ≪≫
      ((Submodule.quotEquivOfEq _ _ (range_sub_one_eq_ker_fibSum hT)).trans
        ((fibSum e).quotKerEquivOfSurjective (surjective_fibSum e))).toModuleIso⟩,
    ⟨loopCellCocycleHomologyNegOneIso h𝓕 γ ≪≫
      ((LinearEquiv.ofEq _ _ (ker_sub_one_eq_range_fibDiag hT)).trans
        (LinearEquiv.ofInjective (fibDiag e) (injective_fibDiag e)).symm).toModuleIso⟩⟩

end DoubleCover

end TauCeti

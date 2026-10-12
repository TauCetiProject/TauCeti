/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.ClosedCategory
public import TauCeti.Algebra.Module.GradedModule.Shift
public import TauCeti.Algebra.Ring.NegOnePow
public import TauCeti.CategoryTheory.DG.Functor
public import Mathlib.CategoryTheory.Shift.Induced

/-!
# Cohomological shifts of curved differential graded right modules

The shift by `n : ℤ` keeps the underlying right module, replaces the degree-`p` piece by the
degree-`(p + n)` piece, and multiplies the differential by `(-1)^n`. The right action is unchanged.
The sign in the differential compensates for the change of degree in the right Leibniz rule,
and its square is still right multiplication by the same curvature, without a centrality
hypothesis.

On homogeneous cochains of degree `p`, the DG shift multiplies the underlying map by
`(-1)^(n * p)`. In particular it keeps closed degree-zero maps and negates odd homotopies when
`n = 1`.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Sections 6.2
  and 7.6. His curvature is the negative of the right-module curvature stored here.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti.CurvedDGRightModuleCat

universe uR uA uM uN

section Cochains

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}

/-- The cohomological shift: `M[n]ᵖ = Mᵖ⁺ⁿ`, with differential `(-1)^n dM` and unchanged
right action and curvature. -/
-- The carrier must reduce to `M` in the element-level differential and cochain formulas.
@[expose, implicit_reducible]
noncomputable def shift (M : CurvedDGRightModuleCat.{uR, uA, uM} h) (n : ℤ) :
    CurvedDGRightModuleCat.{uR, uA, uM} h := by
  let G := (InternalGrading.ofDecomposition M.grading).shift n
  letI : SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece G.piece :=
    ⟨fun i j a x ha hx ↦ by
      simp only [G, InternalGrading.shift_piece, InternalGrading.ofDecomposition_piece,
        vadd_eq_add] at hx ⊢
      simpa only [vadd_eq_add, add_assoc] using
        (SetLike.GradedSMul.smul_mem (B := M.grading) ha hx)⟩
  refine
    { carrier := M
      grading := G.piece
      differential := negOnePowCast R n • M.differential
      isCurvedDGRightModule := ?_ }
  refine ⟨?_, ?_, ?_⟩
  · apply LinearMap.isHomogeneous_shift_piece_iff.mpr
    simpa only [InternalGrading.ofDecomposition_piece] using
      (M.isCurvedDGRightModule.isHomogeneous.smul (negOnePowCast R n))
  · intro q x hx a
    simp only [G, InternalGrading.shift_piece, InternalGrading.ofDecomposition_piece] at hx
    simp only [LinearMap.smul_apply, M.isCurvedDGRightModule.leibniz hx a, smul_add]
    simp only [← negOnePow_smul_eq_negOnePowCast_smul]
    rw [smul_comm n.negOnePow (op a)]
    congr 1
    rw [← mul_smul, Int.negOnePow_add, mul_left_comm, Int.units_mul_self,
      mul_one]
  · intro x
    simp only [LinearMap.smul_apply, map_smul, negOnePowCast_smul_negOnePowCast_smul,
      M.isCurvedDGRightModule.sq_eq]

/-- Shifting replaces the degree-`p` piece by the degree-`(p + n)` piece. -/
@[simp]
theorem shift_grading (M : CurvedDGRightModuleCat.{uR, uA, uM} h) (n p : ℤ) :
    (M.shift n).grading p = M.grading (p + n) := by
  simp only [shift, InternalGrading.shift_piece, InternalGrading.ofDecomposition_piece]

/-- The differential of the shift acts by the shift sign. -/
@[simp]
theorem shift_differential_apply (M : CurvedDGRightModuleCat.{uR, uA, uM} h) (n : ℤ)
    (x : M) : (M.shift n).differential x = n.negOnePow • M.differential x := by
  dsimp only [shift]
  rw [LinearMap.smul_apply, ← negOnePow_smul_eq_negOnePowCast_smul]

variable (M : CurvedDGRightModuleCat.{uR, uA, uM} h)
  (N : CurvedDGRightModuleCat.{uR, uA, uN} h)

/-- The shift on degree-`p` cochains, with the sign `(-1)^(n * p)` that makes it commute with
the Hom differential. -/
noncomputable def shiftCochain (n p : ℤ) :
    dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := N.grading) p →ₗ[R]
      dgRightModuleCochains (R := R) (A := A)
        (ℳ := (M.shift n).grading) (ℳN := (N.shift n).grading) p := by
  -- Reduce the shifted carriers and their scalar structures before restricting the map.
  dsimp only [shift]
  refine LinearMap.codRestrict _
    (negOnePowCast R (n * p) • (dgRightModuleCochains (R := R) (A := A)
      (ℳ := M.grading) (ℳN := N.grading) p).subtype) ?_
  intro f
  apply dgRightModuleCochains.mem_iff.mpr
  apply LinearMap.isHomogeneous_shift_piece_iff.mpr
  simpa only [LinearMap.smul_apply, Submodule.subtype_apply,
    InternalGrading.ofDecomposition_piece, LinearMap.restrictScalars_smul] using
    (dgRightModuleCochains.mem_iff.mp f.2).smul (negOnePowCast R (n * p))

/-- On underlying maps the cochain shift is multiplication by its Koszul sign. -/
@[simp]
theorem shiftCochain_apply (n p : ℤ)
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := N.grading) p)
    (x : M) : (shiftCochain M N n p f).1 x = (n * p).negOnePow • f.1 x := by
  dsimp only [shiftCochain, LinearMap.codRestrict_apply, LinearMap.smul_apply,
    Submodule.subtype_apply]
  exact (negOnePow_smul_eq_negOnePowCast_smul _ _).symm

/-- Shifting cochains commutes with the Hom differential. -/
theorem shiftCochain_curvedDifferential (n p : ℤ)
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := N.grading) p) :
    shiftCochain M N n (p + 1)
        (dgRightModuleCochains.curvedDifferential
          (hM := M.isCurvedDGRightModule) (hN := N.isCurvedDGRightModule) p f) =
      dgRightModuleCochains.curvedDifferential
        (hM := (M.shift n).isCurvedDGRightModule) (hN := (N.shift n).isCurvedDGRightModule) p
        (shiftCochain M N n p f) := by
  ext x
  simp only [shiftCochain_apply, dgRightModuleCochains.curvedDifferential_apply,
    shift_differential_apply, Units.smul_def, map_zsmul, smul_sub, smul_smul]
  simp only [mul_add, mul_one, Int.negOnePow_add, Units.val_mul]
  congr 1; congr 1; ring

/-- The shift by one negates the differential. -/
theorem shift_one_differential_apply (x : M) : (M.shift 1).differential x = -M.differential x := by
  simp

/-- The shift leaves degree-zero underlying maps unchanged. -/
@[simp]
theorem shiftCochain_zero
    (n : ℤ) (f : dgRightModuleCochains (R := R) (A := A)
      (ℳ := M.grading) (ℳN := N.grading) 0) : (shiftCochain M N n 0 f).1 = f.1 := by
  ext x
  simp

/-- The shift multiplies an odd homotopy by `(-1)^n`. -/
theorem shiftCochain_neg_one_apply (n : ℤ)
    (k : dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := N.grading) (-1))
    (x : M) : (shiftCochain M N n (-1) k).1 x = n.negOnePow • k.1 x := by
  simp

end Cochains

/-! ### The DG shift functor and its induced functors -/

-- These builders retain their object carriers; exposing those projections locally keeps
-- the formulas for maps between explicit shifted objects definitionally type-correct.
attribute [local implicit_reducible] EnrichedFunctor.ofDGMap
  EnrichedFunctor.mapDGHomotopyCategory
  DGHomotopyCategory.of DGHomotopyCategory.underlying

universe u

section Category

variable {R : Type u} {A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}

/-- The shift preserves identity cochains. -/
@[simp]
theorem shiftCochain_id (n : ℤ) (M : CurvedDGRightModuleCat.{u, u, u} h) :
    shiftCochain M M n 0 (dgRightModuleCochains.id (R := R) (A := A) (ℳ := M.grading)) =
      dgRightModuleCochains.id (R := R) (A := A) (ℳ := (M.shift n).grading) := by
  ext x
  simp

/-- The shift preserves composition of homogeneous cochains. -/
theorem shiftCochain_comp (n : ℤ) {M N P : CurvedDGRightModuleCat.{u, u, u} h}
    {p q r : ℤ}
    (g : dgRightModuleCochains (R := R) (A := A) (ℳ := N.grading) (ℳN := P.grading) p)
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := N.grading) q)
    (hpq : p + q = r) :
    shiftCochain M P n r (dgRightModuleCochains.comp g f hpq) =
      dgRightModuleCochains.comp (shiftCochain N P n p g) (shiftCochain M N n q f) hpq := by
  subst r
  ext x
  simp only [shiftCochain_apply, dgRightModuleCochains.comp_apply, Units.smul_def,
    map_zsmul, smul_smul, mul_add, Int.negOnePow_add, Units.val_mul]
  rw [mul_comm]

/-- The action of the shift on homogeneous morphisms of the existing DG category. -/
noncomputable def shiftDGMap (n p : ℤ) {M N : CurvedDGRightModuleCat.{u, u, u} h} :
    DGHom R p M N →ₗ[R] DGHom R p (M.shift n) (N.shift n) :=
  (dgHomLinearEquivCochains (M.shift n) (N.shift n) p).symm.toLinearMap.comp
    ((shiftCochain M N n p).comp (dgHomLinearEquivCochains M N p).toLinearMap)

/-- Transport to cochains identifies the DG shift action with the signed cochain shift. -/
@[simp]
theorem dgHomLinearEquivCochains_shiftDGMap (n p : ℤ)
    {M N : CurvedDGRightModuleCat.{u, u, u} h} (f : DGHom R p M N) :
    dgHomLinearEquivCochains (M.shift n) (N.shift n) p (shiftDGMap n p f) =
      shiftCochain M N n p (dgHomLinearEquivCochains M N p f) := by
  simp [shiftDGMap]

/-- The DG shift action commutes with the differential. -/
theorem shiftDGMap_dgDifferential (n p : ℤ) {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : DGHom R p M N) :
    shiftDGMap n (p + 1) (dgDifferential R p f) = dgDifferential R p (shiftDGMap n p f) := by
  apply (dgHomLinearEquivCochains (M.shift n) (N.shift n) (p + 1)).injective
  simp only [dgHomLinearEquivCochains_shiftDGMap, dgDifferential_eq,
    shiftCochain_curvedDifferential]

/-- The DG shift action preserves identities. -/
theorem shiftDGMap_dgId (n : ℤ) (M : CurvedDGRightModuleCat.{u, u, u} h) :
    shiftDGMap n 0 (dgId R M) = dgId R (M.shift n) := by
  apply (dgHomLinearEquivCochains (M.shift n) (M.shift n) 0).injective
  simp

/-- The DG shift action preserves composition in Mathlib's enriched factor order. -/
theorem shiftDGMap_dgComp (n : ℤ) {M N P : CurvedDGRightModuleCat.{u, u, u} h}
    {p q r : ℤ} (f : DGHom R p M N) (g : DGHom R q N P) (hpq : p + q = r) :
    shiftDGMap n r (dgComp R f g hpq) = dgComp R (shiftDGMap n p f) (shiftDGMap n q g) hpq := by
  apply (dgHomLinearEquivCochains (M.shift n) (P.shift n) r).injective
  simp only [dgHomLinearEquivCochains_shiftDGMap, dgComp_eq, Units.smul_def, map_zsmul,
    shiftCochain_comp]

/-- The cohomological shift as a DG endofunctor of curved right modules. -/
@[expose, implicit_reducible]
noncomputable def dgShiftFunctor (n : ℤ) :
    EnrichedFunctor (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)
      (CurvedDGRightModuleCat.{u, u, u} h) :=
  EnrichedFunctor.ofDGMap (fun M ↦ M.shift n)
    (fun {M N} p ↦ shiftDGMap n p (M := M) (N := N))
    (fun {_ _} p f ↦ shiftDGMap_dgDifferential n p f) (shiftDGMap_dgId n)
    (fun {_ _ _} {_ _ _} f g hpq ↦ shiftDGMap_dgComp n f g hpq)

/-- The DG shift sends a module to its explicit cohomological shift. -/
@[simp]
theorem dgShiftFunctor_obj (n : ℤ) (M : CurvedDGRightModuleCat.{u, u, u} h) :
    (dgShiftFunctor (h := h) n).obj M = M.shift n :=
  (rfl)

/-- The DG shift acts on homogeneous morphisms by the signed cochain shift. -/
@[simp]
theorem dgShiftFunctor_dgMap (n p : ℤ) {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : DGHom R p M N) : (dgShiftFunctor (h := h) n).dgMap p f = shiftDGMap n p f := by
  dsimp only [dgShiftFunctor]
  exact EnrichedFunctor.dgMap_ofDGMap _ _ _ _ _ p f

/-- The cohomological shift on the closed degree-zero category of curved modules. -/
@[expose, implicit_reducible]
noncomputable def closedShiftFunctor (n : ℤ) :
    ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h) ⥤
      ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h) :=
  (dgShiftFunctor (h := h) n).forget

/-- The closed shift sends a module to its explicit shift. -/
@[simp]
theorem closedShiftFunctor_obj_of (n : ℤ) (M : CurvedDGRightModuleCat.{u, u, u} h) :
    (closedShiftFunctor n).obj (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) =
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M.shift n) :=
  (rfl)

/-- On closed morphisms the shift keeps the underlying right-linear map. -/
@[simp]
theorem closedHom_closedShiftFunctor_map (n : ℤ)
    {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    closedHom ((closedShiftFunctor n).map f) = closedHom f := by
  have hmap : dgClosedHom R ((closedShiftFunctor n).map f) =
      shiftDGMap n 0 (dgClosedHom R f) := by
    simpa only [closedShiftFunctor, EnrichedFunctor.forget_map, dgShiftFunctor_dgMap,
      ForgetEnrichment.to_of] using (dgShiftFunctor (h := h) n).dgClosedHom_forget_map f
  calc
    closedHom ((closedShiftFunctor n).map f) =
        (dgHomLinearEquivCochains (M.shift n) (N.shift n) 0
          (dgClosedHom R ((closedShiftFunctor n).map f))).1 := closedHom_eq _
    _ = (dgHomLinearEquivCochains (M.shift n) (N.shift n) 0
        (shiftDGMap n 0 (dgClosedHom R f))).1 :=
      congrArg (fun c : DGHom R 0 (M.shift n) (N.shift n) ↦
        (dgHomLinearEquivCochains (M.shift n) (N.shift n) 0 c).1) hmap
    _ = closedHom f := by
      rw [dgHomLinearEquivCochains_shiftDGMap, shiftCochain_zero]
      exact (closedHom_eq f).symm

/-! ### Zero and addition comparisons in the closed category -/

/-- A module shifted by zero is canonically isomorphic to the original module. -/
noncomputable def closedShiftZeroIso (M : CurvedDGRightModuleCat.{u, u, u} h) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M.shift 0) ≅
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M :=
  closedIsoOf (M := M.shift 0) (N := M) (LinearEquiv.refl Aᵐᵒᵖ M)
    (fun p x ↦ by simp only [shift_grading, add_zero]; rfl)
    (fun x ↦ by simp only [shift_differential_apply, Int.negOnePow_zero, one_smul]; rfl)

/-- Successive cohomological shifts add their amounts. -/
noncomputable def closedShiftAddIso (M : CurvedDGRightModuleCat.{u, u, u} h) (n m : ℤ) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M.shift (n + m)) ≅
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) ((M.shift n).shift m) :=
  closedIsoOf (M := M.shift (n + m)) (N := (M.shift n).shift m) (LinearEquiv.refl Aᵐᵒᵖ M)
    (fun p x ↦ by simp only [shift_grading, add_assoc, add_comm m n]; rfl)
    (fun x ↦ by
      simp only [shift_differential_apply, Int.negOnePow_add, smul_smul]
      rw [mul_comm]
      rfl)

/-- The zero-shift comparison has identity underlying map. -/
@[simp]
theorem closedHom_closedShiftZeroIso_hom (M : CurvedDGRightModuleCat.{u, u, u} h) :
    closedHom (closedShiftZeroIso M).hom = LinearMap.id := by
  simp only [closedShiftZeroIso, closedHom_closedIsoOf_hom, LinearEquiv.refl_toLinearMap]

/-- The inverse zero-shift comparison has identity underlying map. -/
@[simp]
theorem closedHom_closedShiftZeroIso_inv (M : CurvedDGRightModuleCat.{u, u, u} h) :
    closedHom (closedShiftZeroIso M).inv = LinearMap.id := by
  rw [closedShiftZeroIso, closedHom_closedIsoOf_inv]
  rfl

/-- The addition comparison has identity underlying map. -/
@[simp]
theorem closedHom_closedShiftAddIso_hom (M : CurvedDGRightModuleCat.{u, u, u} h) (n m : ℤ) :
    closedHom (closedShiftAddIso M n m).hom = LinearMap.id := by
  simp only [closedShiftAddIso, closedHom_closedIsoOf_hom, LinearEquiv.refl_toLinearMap]

/-- The inverse addition comparison has identity underlying map. -/
@[simp]
theorem closedHom_closedShiftAddIso_inv (M : CurvedDGRightModuleCat.{u, u, u} h) (n m : ℤ) :
    closedHom (closedShiftAddIso M n m).inv = LinearMap.id := by
  rw [closedShiftAddIso, closedHom_closedIsoOf_inv]
  rfl

/-- Shifting closed modules by zero is naturally isomorphic to the identity. -/
noncomputable def closedShiftFunctorZeroIso :
    closedShiftFunctor (h := h) 0 ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M ↦ closedShiftZeroIso (ForgetEnrichment.to _ M)) fun f ↦ by
    apply closedHom_ext
    intro x
    -- The functor object map is definitionally the explicit shifted module.
    erw [closedHom_comp, closedHom_comp, closedHom_closedShiftZeroIso_hom,
      closedHom_closedShiftZeroIso_hom]
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Functor.id_map]
    erw [closedHom_closedShiftFunctor_map]

/-- The addition comparisons are natural in closed morphisms. -/
noncomputable def closedShiftFunctorAddIso (n m : ℤ) :
    closedShiftFunctor (h := h) (n + m) ≅ closedShiftFunctor n ⋙ closedShiftFunctor m :=
  NatIso.ofComponents (fun M ↦ closedShiftAddIso (ForgetEnrichment.to _ M) n m) fun f ↦ by
    apply closedHom_ext
    intro x
    -- The functor object map is definitionally the explicit shifted module.
    erw [closedHom_comp, closedHom_comp]
    simp only [closedHom_closedShiftAddIso_hom, LinearMap.comp_apply, LinearMap.id_apply,
      Functor.comp_map]
    erw [closedHom_closedShiftFunctor_map, closedHom_closedShiftFunctor_map,
      closedHom_closedShiftFunctor_map]

/-- The zero comparison is the canonical object comparison. -/
@[simp]
theorem closedShiftFunctorZeroIso_hom_app
    (X : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) :
    (closedShiftFunctorZeroIso (h := h)).hom.app X =
      (closedShiftZeroIso (ForgetEnrichment.to _ X)).hom :=
  (rfl)

/-- The inverse zero comparison is the canonical object comparison. -/
@[simp]
theorem closedShiftFunctorZeroIso_inv_app
    (X : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) :
    (closedShiftFunctorZeroIso (h := h)).inv.app X =
      (closedShiftZeroIso (ForgetEnrichment.to _ X)).inv :=
  (rfl)

/-- The addition comparison is the canonical object comparison. -/
@[simp]
theorem closedShiftFunctorAddIso_hom_app (n m : ℤ)
    (X : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) :
    (closedShiftFunctorAddIso (h := h) n m).hom.app X =
      (closedShiftAddIso (ForgetEnrichment.to _ X) n m).hom :=
  (rfl)

/-- The inverse addition comparison is the canonical object comparison. -/
@[simp]
theorem closedShiftFunctorAddIso_inv_app (n m : ℤ)
    (X : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) :
    (closedShiftFunctorAddIso (h := h) n m).inv.app X =
      (closedShiftAddIso (ForgetEnrichment.to _ X) n m).inv :=
  (rfl)

/-- Transport along equality of shift amounts has identity underlying map. -/
@[simp]
theorem closedHom_eqToHom_shift (M : CurvedDGRightModuleCat.{u, u, u} h)
    (n m : ℤ) (hnm : n = m) :
    closedHom (eqToHom (congrArg (fun k : ℤ ↦
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M.shift k)) hnm)) =
      LinearMap.id := by
  subst m
  simp

/-- The cohomological shifts form a coherent integer shift on the closed category. -/
noncomputable instance : HasShift
    (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) ℤ :=
  hasShiftMk _ ℤ
    { F := closedShiftFunctor (h := h)
      zero := closedShiftFunctorZeroIso
      add := closedShiftFunctorAddIso
      assoc_hom_app := fun n m k X ↦ by
        apply closedHom_ext
        intro x
        erw [closedHom_comp, closedHom_comp, closedHom_comp]
        simp only [closedShiftFunctorAddIso_hom_app, closedHom_closedShiftAddIso_hom,
          LinearMap.comp_apply, LinearMap.id_apply]
        erw [closedHom_closedShiftFunctor_map, closedHom_closedShiftAddIso_hom,
          closedHom_eqToHom_shift (ForgetEnrichment.to _ X) _ _ (add_assoc n m k)]
      zero_add_hom_app := fun n X ↦ by
        apply closedHom_ext
        intro x
        erw [closedHom_comp]
        simp only [closedShiftFunctorAddIso_hom_app, closedShiftFunctorZeroIso_inv_app,
          closedHom_closedShiftAddIso_hom, LinearMap.comp_apply, LinearMap.id_apply]
        erw [closedHom_closedShiftFunctor_map, closedHom_closedShiftZeroIso_inv,
          closedHom_eqToHom_shift (ForgetEnrichment.to _ X) _ _ (zero_add n)]
        rfl
      add_zero_hom_app := fun n X ↦ by
        apply closedHom_ext
        intro x
        erw [closedHom_comp]
        simp only [closedShiftFunctorAddIso_hom_app, closedShiftFunctorZeroIso_inv_app,
          closedHom_closedShiftAddIso_hom, LinearMap.comp_apply, LinearMap.id_apply]
        erw [closedHom_closedShiftZeroIso_inv,
          closedHom_eqToHom_shift (ForgetEnrichment.to _ X) _ _ (add_zero n)]
        rfl }

/-- The cohomological shift on the existing curved homotopy category. -/
@[expose, implicit_reducible]
noncomputable def homotopyShiftFunctor (n : ℤ) :
    DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h) ⥤
      DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h) :=
  (dgShiftFunctor (h := h) n).mapDGHomotopyCategory

noncomputable instance (n : ℤ) : (homotopyShiftFunctor (h := h) n).Additive :=
  inferInstanceAs (dgShiftFunctor (h := h) n).mapDGHomotopyCategory.Additive

noncomputable instance (n : ℤ) : (homotopyShiftFunctor (h := h) n).Linear R :=
  inferInstanceAs (Functor.Linear R (dgShiftFunctor (h := h) n).mapDGHomotopyCategory)

/-- The homotopy shift sends the class of a module to the class of its explicit shift. -/
@[simp]
theorem homotopyShiftFunctor_obj_of (n : ℤ) (M : CurvedDGRightModuleCat.{u, u, u} h) :
    (homotopyShiftFunctor n).obj (DGHomotopyCategory.of R M) =
      DGHomotopyCategory.of R (M.shift n) :=
  (rfl)

/-- The signed shift of a closed DG morphism is closed. -/
theorem shiftDGMap_mem_dgCycles (n : ℤ) {M N : CurvedDGRightModuleCat.{u, u, u} h}
    {f : DGHom R 0 M N} (hf : f ∈ dgCycles R M N) :
    shiftDGMap n 0 f ∈ dgCycles R (M.shift n) (N.shift n) := by
  apply (mem_dgCycles R).mpr
  rw [← shiftDGMap_dgDifferential, (mem_dgCycles R).mp hf, map_zero]

/-- The homotopy shift maps a represented closed morphism to its shifted representative. -/
@[simp]
theorem homotopyShiftFunctor_map_homOf (n : ℤ) {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : DGHom R 0 M N) (hf : f ∈ dgCycles R M N) :
    (homotopyShiftFunctor n).map (DGHomotopyCategory.homOf R f hf) =
      DGHomotopyCategory.homOf R (shiftDGMap n 0 f)
        (shiftDGMap_mem_dgCycles n hf) := by
  simpa only [homotopyShiftFunctor, dgShiftFunctor_dgMap, dgShiftFunctor_obj,
    EnrichedFunctor.mapDGHomotopyCategory_obj_of] using
    (dgShiftFunctor (h := h) n).mapDGHomotopyCategory_map_homOf f hf

/-! ### The coherent shift on the curved homotopy category -/

/-- The integer shifts descend to the existing homotopy category, with coherence supplied
by Mathlib's induced-shift construction. -/
noncomputable instance : HasShift
    (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) ℤ :=
  HasShift.induced (dgClosedToHomotopy R) ℤ (homotopyShiftFunctor (h := h))
    (fun n ↦ (dgShiftFunctor (h := h) n).forgetCompDgClosedToHomotopyIso.symm)

/-- The quotient functor commutes with the coherent integer shifts. -/
noncomputable instance :
    (dgClosedToHomotopy (C := CurvedDGRightModuleCat.{u, u, u} h) R).CommShift ℤ :=
  Functor.CommShift.ofInduced (dgClosedToHomotopy R) ℤ (homotopyShiftFunctor (h := h))
    (fun n ↦ (dgShiftFunctor (h := h) n).forgetCompDgClosedToHomotopyIso.symm)

/-- Shifting the class of a closed map is the class of its closed shift. -/
theorem homotopyShiftFunctor_map_quotient (n : ℤ)
    {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    (homotopyShiftFunctor n).map ((dgClosedToHomotopy R).map f) =
      (dgClosedToHomotopy R).map ((closedShiftFunctor n).map f) := by
  have hn := (dgShiftFunctor (h := h) n).forgetCompDgClosedToHomotopyIso.hom.naturality f
  simp only [Functor.comp_map, EnrichedFunctor.forgetCompDgClosedToHomotopyIso_hom_app] at hn
  erw [Category.comp_id, Category.id_comp] at hn
  exact hn.symm

/-- The categorical integer shift is the explicitly constructed homotopy shift. -/
@[simp]
theorem shiftFunctor_eq_homotopyShiftFunctor (n : ℤ) :
    shiftFunctor (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) n =
      homotopyShiftFunctor n :=
  (rfl)

noncomputable instance (n : ℤ) :
    (shiftFunctor (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) n).Additive :=
  inferInstanceAs (homotopyShiftFunctor (h := h) n).Additive

noncomputable instance (n : ℤ) :
    (shiftFunctor (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) n).Linear R :=
  inferInstanceAs (Functor.Linear R (homotopyShiftFunctor (h := h) n))

/-- A categorical shift of a module class is its explicit cohomological shift. -/
theorem shift_of (M : CurvedDGRightModuleCat.{u, u, u} h) (n : ℤ) :
    (DGHomotopyCategory.of R M)⟦n⟧ = DGHomotopyCategory.of R (M.shift n) :=
  (rfl)

end Category

end TauCeti.CurvedDGRightModuleCat

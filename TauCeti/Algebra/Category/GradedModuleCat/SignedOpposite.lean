/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Shift
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Homology.DG.Module.Right.Composition
public import TauCeti.Algebra.Module.GradedModule.LeftToRight

/-!
# Homogeneous maps through the signed opposite

For graded left modules, conjugation by the quadratic grading involutions transports linear
maps to maps of right modules over the Koszul-signed opposite. Multiplying a degree-`p` map by
the quadratic sign gives the evaluation formula `I_p(f)(x_r) = (-1)^(p*r) f(x_r)`.

The comparison uses arbitrary commutative coefficient rings and separate coefficient, algebra
and module universes. Keller composition has the factor `(-1)^(s*t)` for maps into shifts `s`
and `t`; the quadratic normalization preserves composition. The existing DG enrichment can use
these cochains when the coefficient, algebra and module universes coincide.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

noncomputable section

namespace TauCeti.GradedModuleCat

open CategoryTheory

universe uR uA v

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  (G : InternalGrading R A)

local notation "B" => (GradedOpposite G)ᵐᵒᵖ

@[instance_reducible]
private local instance signedModule (M : GradedModuleCat.{v} G.piece) : Module B M :=
  GradedOpposite.leftToRightModule G M.grading

private local instance signedTower (M : GradedModuleCat.{v} G.piece) : IsScalarTower R B M :=
  GradedOpposite.leftToRight_isScalarTower G M.grading

private noncomputable def quadraticModuleEquivData (M : GradedModuleCat.{v} G.piece) :
    {e : M ≃ₗ[B]
        ((_root_.ModuleCat.restrictScalars (GradedOpposite.opAlgEquiv G).toRingHom).obj
          (_root_.ModuleCat.of A M)) //
      (∀ x, e x = M.grading.quadraticTwist x) ∧
        ∀ x, e.symm x = M.grading.quadraticTwist x} := by
  letI : Module B M := inferInstanceAs (Module B
    ((_root_.ModuleCat.restrictScalars (GradedOpposite.opAlgEquiv G).toRingHom).obj
      (_root_.ModuleCat.of A M)))
  have h : signedModule G M = M.grading.quadraticTwistEquiv.toAddEquiv.module B := by
    apply Module.ext'
    intro b x
    rw [GradedOpposite.leftToRight_smul G M.grading, Equiv.smul_def]
    -- Transfer stores the restricted action on the raw carrier M; smul_def is stated
    -- on the bundled restricted object. Present that same carrier with the latter type.
    change _ = M.grading.quadraticTwistEquiv.symm
      (b • (show ((_root_.ModuleCat.restrictScalars
        (GradedOpposite.opAlgEquiv G).toRingHom).obj (_root_.ModuleCat.of A M)) from
          M.grading.quadraticTwistEquiv x))
    rw [_root_.ModuleCat.restrictScalars.smul_def,
      M.grading.quadraticTwistEquiv_symm_apply, M.grading.quadraticTwistEquiv_apply]
    rfl
  -- Transport the evaluation witnesses along with the equivalence across the action identity.
  rw [h]
  refine ⟨M.grading.quadraticTwistEquiv.toAddEquiv.linearEquiv B, ?_, ?_⟩
  · intro x
    exact (AddEquiv.linearEquiv_apply (R := B) M.grading.quadraticTwistEquiv.toAddEquiv x).trans
      (M.grading.quadraticTwistEquiv_apply x)
  · intro x
    exact (AddEquiv.linearEquiv_symm_apply (R := B)
      M.grading.quadraticTwistEquiv.toAddEquiv x).trans
        (M.grading.quadraticTwistEquiv_symm_apply x)

private noncomputable def quadraticModuleEquiv (M : GradedModuleCat.{v} G.piece) :
    M ≃ₗ[B]
      ((_root_.ModuleCat.restrictScalars (GradedOpposite.opAlgEquiv G).toRingHom).obj
        (_root_.ModuleCat.of A M)) :=
  (quadraticModuleEquivData G M).1

private theorem quadraticModuleEquiv_apply (M : GradedModuleCat.{v} G.piece) (x : M) :
    quadraticModuleEquiv G M x = M.grading.quadraticTwist x :=
  (quadraticModuleEquivData G M).2.1 x

private theorem quadraticModuleEquiv_symm_apply (M : GradedModuleCat.{v} G.piece) (x : M) :
    (quadraticModuleEquiv G M).symm x = M.grading.quadraticTwist x :=
  (quadraticModuleEquivData G M).2.2 x

private noncomputable def quadraticHomMap (M N : GradedModuleCat.{v} G.piece) :
    (M →ₗ[A] N) →ₗ[R] (M →ₗ[B] N) where
  toFun f := (quadraticModuleEquiv G N).symm.toLinearMap.comp
    (((_root_.ModuleCat.restrictScalars (GradedOpposite.opAlgEquiv G).toRingHom).map
      (_root_.ModuleCat.ofHom f)).hom.comp (quadraticModuleEquiv G M).toLinearMap)
  map_add' f g := by
    ext x
    -- The sum is evaluated as a linear map on bundled restricted carriers. The categorical
    -- map_apply equation cannot rewrite that Hom.hom/composition coercion directly.
    change (quadraticModuleEquiv G N).symm ((f + g) (quadraticModuleEquiv G M x)) =
      (quadraticModuleEquiv G N).symm (f (quadraticModuleEquiv G M x)) +
        (quadraticModuleEquiv G N).symm (g (quadraticModuleEquiv G M x))
    rw [quadraticModuleEquiv_apply, quadraticModuleEquiv_symm_apply,
      quadraticModuleEquiv_symm_apply, quadraticModuleEquiv_symm_apply]
    simp only [LinearMap.add_apply, map_add]
  map_smul' r f := by
    ext x
    -- Expose the restricted Hom.hom and composition evaluations using the chosen R-action;
    -- rewriting the categorical map alone leaves no inferred R-action on its bundled target.
    change (quadraticModuleEquiv G N).symm (r • f (quadraticModuleEquiv G M x)) =
      r • (quadraticModuleEquiv G N).symm (f (quadraticModuleEquiv G M x))
    rw [quadraticModuleEquiv_symm_apply, quadraticModuleEquiv_symm_apply]
    exact map_smul _ _ _

private theorem quadraticHomMap_apply (M N : GradedModuleCat.{v} G.piece)
    (f : M →ₗ[A] N) (x : M) :
    quadraticHomMap G M N f x =
      N.grading.quadraticTwist (f (M.grading.quadraticTwist x)) := by
  have h := _root_.ModuleCat.restrictScalars.map_apply (M := _root_.ModuleCat.of A M)
    (M' := _root_.ModuleCat.of A N) (GradedOpposite.opAlgEquiv G).toRingHom
      (_root_.ModuleCat.ofHom f) (quadraticModuleEquiv G M x)
  calc
    _ = (quadraticModuleEquiv G N).symm
        (((_root_.ModuleCat.restrictScalars (GradedOpposite.opAlgEquiv G).toRingHom).map
          (_root_.ModuleCat.ofHom f)) (quadraticModuleEquiv G M x)) := rfl
    _ = (quadraticModuleEquiv G N).symm (f (quadraticModuleEquiv G M x)) :=
      congrArg (quadraticModuleEquiv G N).symm h
    _ = _ := by rw [quadraticModuleEquiv_apply, quadraticModuleEquiv_symm_apply]

private noncomputable def quadraticHomEquiv (M N : GradedModuleCat.{v} G.piece) :
    (M →ₗ[A] N) ≃ₗ[R] (M →ₗ[B] N) := by
  let F := _root_.ModuleCat.restrictScalars (GradedOpposite.opAlgEquiv G).toRingHom
  let e : (M →ₗ[A] N) ≃ (M →ₗ[B] N) :=
    (_root_.ModuleCat.homEquiv (M := _root_.ModuleCat.of A M)
      (N := _root_.ModuleCat.of A N)).symm.trans
      ((Functor.FullyFaithful.ofFullyFaithful F).homEquiv.trans
        ((Iso.homCongr (quadraticModuleEquiv G M).toModuleIso.symm
          (quadraticModuleEquiv G N).toModuleIso.symm).trans _root_.ModuleCat.homEquiv))
  -- ModuleCat.homEquiv supplies ofHom/Hom.hom; the fully faithful homEquiv supplies F.map.
  -- Iso.homCongr for the reversed toModuleIso values precomposes by quadraticModuleEquiv G M
  -- and postcomposes by (quadraticModuleEquiv G N).symm, the same conjugation as quadraticHomMap.
  -- Thus the bare equivalence and the R-linear map have definitionally equal forward functions.
  exact LinearEquiv.ofBijective (quadraticHomMap G M N) e.bijective

private theorem quadraticHomEquiv_apply (M N : GradedModuleCat.{v} G.piece)
    (f : M →ₗ[A] N) (x : M) :
    quadraticHomEquiv G M N f x =
      N.grading.quadraticTwist (f (M.grading.quadraticTwist x)) :=
  quadraticHomMap_apply G M N f x

private theorem quadraticHomEquiv_symm_apply (M N : GradedModuleCat.{v} G.piece)
    (f : M →ₗ[B] N) (x : M) :
    (quadraticHomEquiv G M N).symm f x =
      N.grading.quadraticTwist (f (M.grading.quadraticTwist x)) := by
  have h := congrArg (fun g ↦ g (M.grading.quadraticTwist x))
    ((quadraticHomEquiv G M N).apply_symm_apply f)
  rw [quadraticHomEquiv_apply, M.grading.quadraticTwist_involutive x] at h
  have h' := congrArg N.grading.quadraticTwist h
  rwa [N.grading.quadraticTwist_involutive] at h'

private def flattenShiftHom (M N : GradedModuleCat.{v} G.piece) (s : ℤ) :
    (M ⟶ N.shiftObj s) →ₗ[R] (M →ₗ[A] N) where
  toFun f := ((shiftFunctorCompToModuleCatIso s).hom.app N).hom.comp f.hom
  map_add' f g := by
    simp only [shiftFunctorCompToModuleCatIso_hom_app_hom]
    rfl
  map_smul' r f := by
    simp only [shiftFunctorCompToModuleCatIso_hom_app_hom]
    rfl

private theorem flattenShiftHom_apply (M N : GradedModuleCat.{v} G.piece) (s : ℤ)
    (f : M ⟶ N.shiftObj s) (x : M) : flattenShiftHom G M N s f x = f.hom x := by
  -- Expose the private flattening map and its composition before using the public iso equation.
  -- Its identity map is typed on the shifted carrier, so identity-composition rewriting misses it.
  change ((shiftFunctorCompToModuleCatIso s).hom.app N).hom (f.hom x) = _
  rw [shiftFunctorCompToModuleCatIso_hom_app_hom]
  rfl

private theorem flattenShiftHom_homogeneous (M N : GradedModuleCat.{v} G.piece) (s : ℤ)
    (f : M ⟶ N.shiftObj s) :
    LinearMap.IsHomogeneous (flattenShiftHom G M N s f) M.grading.piece N.grading.piece (-s) := by
  rw [LinearMap.isHomogeneous_def]
  intro r x hx
  rw [flattenShiftHom_apply]
  simpa only [InternalGrading.shift_piece] using map_mem f hx

private theorem flattenShiftHom_ofHom (M N : GradedModuleCat.{v} G.piece) (s : ℤ)
    (f : M →ₗ[A] N)
    (hf : LinearMap.IsHomogeneous f M.grading.piece (N.shiftObj s).grading.piece 0) :
    flattenShiftHom G M N s (ofHom f hf) = f := by
  ext x
  exact flattenShiftHom_apply G M N s _ x

/-- Maps into the internal shift `N{s}` are degree-`-s` cochains between the signed right
modules. The quadratic normalization supplies the input-degree Koszul sign. -/
noncomputable def homShiftEquivSignedOppositeCochains
    (M N : GradedModuleCat.{v} G.piece) (s : ℤ) :
    letI : Module B M := GradedOpposite.leftToRightModule G M.grading
    letI : Module B N := GradedOpposite.leftToRightModule G N.grading
    letI : IsScalarTower R B M := GradedOpposite.leftToRight_isScalarTower G M.grading
    letI : IsScalarTower R B N := GradedOpposite.leftToRight_isScalarTower G N.grading
    (M ⟶ N.shiftObj s) ≃ₗ[R]
      dgRightModuleCochains (R := R) (A := GradedOpposite G)
        (ℳ := M.grading.piece) (ℳN := N.grading.piece) (-s) where
  toFun f := ⟨(InternalGrading.quadraticExponent (-s)).negOnePow •
    quadraticHomEquiv G M N (flattenShiftHom G M N s f), by
    apply dgRightModuleCochains.mem_iff.mpr
    rw [LinearMap.isHomogeneous_def]
    intro r x hx
    -- Homogeneity tests the scalar restriction of a scaled B-linear map. Expose its value
    -- through restriction and the unit action before applying the quadratic evaluation lemma.
    change (InternalGrading.quadraticExponent (-s)).negOnePow •
      quadraticHomEquiv G M N (flattenShiftHom G M N s f) x ∈ N.grading.piece (r + -s)
    rw [quadraticHomEquiv_apply, Units.smul_def]
    exact zsmul_mem (N.grading.quadraticTwist_mem_piece
      ((flattenShiftHom_homogeneous G M N s f).map_mem
        (M.grading.quadraticTwist_mem_piece hx))) _⟩
  invFun f := ofHom
    ((InternalGrading.quadraticExponent (-s)).negOnePow • (quadraticHomEquiv G M N).symm f.1)
    (by
      rw [LinearMap.isHomogeneous_def]
      intro r x hx
      simp only [InternalGrading.shift_piece, add_zero]
      -- The shifted carrier and the unit-scaled linear-map coercion hide the value on N.
      -- Reduce those wrappers so the inverse quadratic evaluation equation can rewrite it.
      change (InternalGrading.quadraticExponent (-s)).negOnePow •
        (quadraticHomEquiv G M N).symm f.1 x ∈ N.grading.piece (r + -s)
      rw [quadraticHomEquiv_symm_apply, Units.smul_def]
      exact zsmul_mem (N.grading.quadraticTwist_mem_piece
        (dgRightModuleCochains.map_mem f (M.grading.quadraticTwist_mem_piece hx))) _)
  left_inv f := by
    apply hom_ext
    ext x
    -- Unpack the equivalence, cochain subtype and ofHom projection at x; the inverse
    -- equivalence equation otherwise sees the enclosing graded-Hom constructor.
    change (InternalGrading.quadraticExponent (-s)).negOnePow •
      (quadraticHomEquiv G M N).symm
        ((InternalGrading.quadraticExponent (-s)).negOnePow •
          quadraticHomEquiv G M N (flattenShiftHom G M N s f)) x = f.hom x
    rw [map_zsmul_unit, LinearEquiv.symm_apply_apply]
    -- The inner unit still scales a linear map, so mul_smul cannot match its evaluation.
    -- Reduce the pointwise action to the two successive unit actions on the output.
    change (InternalGrading.quadraticExponent (-s)).negOnePow •
      (InternalGrading.quadraticExponent (-s)).negOnePow • flattenShiftHom G M N s f x = _
    rw [← mul_smul, Int.units_mul_self, one_smul, flattenShiftHom_apply]
  right_inv f := by
    apply Subtype.ext
    ext x
    -- Expose the forward subtype value after the inverse ofHom constructor; this brings
    -- flattenShiftHom_ofHom into the expression without unfolding either conjugation proof.
    change (InternalGrading.quadraticExponent (-s)).negOnePow •
      quadraticHomEquiv G M N (flattenShiftHom G M N s
        (ofHom ((InternalGrading.quadraticExponent (-s)).negOnePow •
          (quadraticHomEquiv G M N).symm f.1) _)) x = f.1 x
    rw [flattenShiftHom_ofHom, map_zsmul_unit, LinearEquiv.apply_symm_apply]
    -- Evaluate the remaining unit-scaled linear map before cancelling the two output signs;
    -- mul_smul acts on values and does not rewrite through this map coercion.
    change (InternalGrading.quadraticExponent (-s)).negOnePow •
      (InternalGrading.quadraticExponent (-s)).negOnePow • f.1 x = _
    rw [← mul_smul, Int.units_mul_self, one_smul]
  map_add' f g := by
    apply Subtype.ext
    simp only [map_add, smul_add, Submodule.coe_add]
  map_smul' r f := by
    apply Subtype.ext
    simp only [map_smul, Submodule.coe_smul_of_tower, RingHom.id_apply]
    exact smul_comm _ _ _

/-- The comparison on arbitrary inputs is quadratic conjugation with the degree sign. -/
@[simp]
theorem homShiftEquivSignedOppositeCochains_apply
    (M N : GradedModuleCat.{v} G.piece) (s : ℤ) (f : M ⟶ N.shiftObj s) (x : M) :
    (homShiftEquivSignedOppositeCochains G M N s f).1 x =
      (InternalGrading.quadraticExponent (-s)).negOnePow •
        N.grading.quadraticTwist (f.hom (M.grading.quadraticTwist x)) := by
  -- This establishes the public evaluation equation: expose only the forward subtype value
  -- and the scaled-map coercion so the existing private evaluation lemmas can rewrite them.
  change (InternalGrading.quadraticExponent (-s)).negOnePow •
    quadraticHomEquiv G M N (flattenShiftHom G M N s f) x = _
  rw [quadraticHomEquiv_apply, flattenShiftHom_apply]

/-- The inverse comparison uses the same quadratic conjugation and degree sign. -/
@[simp]
theorem homShiftEquivSignedOppositeCochains_symm_apply
    (M N : GradedModuleCat.{v} G.piece) (s : ℤ)
    (f : letI : Module B M := GradedOpposite.leftToRightModule G M.grading
      letI : Module B N := GradedOpposite.leftToRightModule G N.grading
      letI : IsScalarTower R B M := GradedOpposite.leftToRight_isScalarTower G M.grading
      letI : IsScalarTower R B N := GradedOpposite.leftToRight_isScalarTower G N.grading
      dgRightModuleCochains (R := R) (A := GradedOpposite G)
        (ℳ := M.grading.piece) (ℳN := N.grading.piece) (-s)) (x : M) :
    ((homShiftEquivSignedOppositeCochains G M N s).symm f).hom x =
      (InternalGrading.quadraticExponent (-s)).negOnePow •
        N.grading.quadraticTwist (f.1 (M.grading.quadraticTwist x)) := by
  -- The inverse returns an ofHom on the shifted carrier. Expose that Hom projection and
  -- its unit-scaled value before rewriting with quadraticHomEquiv_symm_apply.
  change (InternalGrading.quadraticExponent (-s)).negOnePow •
    (quadraticHomEquiv G M N).symm f.1 x = _
  rw [quadraticHomEquiv_symm_apply]

private theorem quadraticTwist_apply_unit (M : GradedModuleCat.{v} G.piece)
    {r : ℤ} {x : M} (hx : x ∈ M.grading.piece r) :
    M.grading.quadraticTwist x = (InternalGrading.quadraticExponent r).negOnePow • x := by
  rw [M.grading.quadraticTwist_apply_of_mem hx, Int.cast_smul_eq_zsmul, Units.smul_def]

/-- A map of degree `-s` acquires the Koszul sign from the degree of its input. -/
theorem homShiftEquivSignedOppositeCochains_apply_of_mem
    (M N : GradedModuleCat.{v} G.piece) (s : ℤ) (f : M ⟶ N.shiftObj s)
    {r : ℤ} {x : M} (hx : x ∈ M.grading.piece r) :
    (homShiftEquivSignedOppositeCochains G M N s f).1 x = (-s * r).negOnePow • f.hom x := by
  have hf : f.hom x ∈ N.grading.piece (r + -s) := by
    simpa only [flattenShiftHom_apply] using
      (flattenShiftHom_homogeneous G M N s f).map_mem hx
  rw [homShiftEquivSignedOppositeCochains_apply, quadraticTwist_apply_unit G M hx,
    map_zsmul_unit, map_zsmul_unit, quadraticTwist_apply_unit G N hf]
  simp only [← mul_smul, ← mul_assoc, InternalGrading.negOnePow_quadraticExponent_cancel]

/-- On a homogeneous input the inverse has the same Koszul sign as the forward comparison. -/
theorem homShiftEquivSignedOppositeCochains_symm_apply_of_mem
    (M N : GradedModuleCat.{v} G.piece) (s : ℤ)
    (f : letI : Module B M := GradedOpposite.leftToRightModule G M.grading
      letI : Module B N := GradedOpposite.leftToRightModule G N.grading
      letI : IsScalarTower R B M := GradedOpposite.leftToRight_isScalarTower G M.grading
      letI : IsScalarTower R B N := GradedOpposite.leftToRight_isScalarTower G N.grading
      dgRightModuleCochains (R := R) (A := GradedOpposite G)
        (ℳ := M.grading.piece) (ℳN := N.grading.piece) (-s))
    {r : ℤ} {x : M} (hx : x ∈ M.grading.piece r) :
    ((homShiftEquivSignedOppositeCochains G M N s).symm f).hom x =
      (-s * r).negOnePow • f.1 x := by
  have h := congrArg (fun g ↦ g.1 x)
    ((homShiftEquivSignedOppositeCochains G M N s).apply_symm_apply f)
  rw [homShiftEquivSignedOppositeCochains_apply_of_mem G M N s _ hx] at h
  calc
    _ = (-s * r).negOnePow • (-s * r).negOnePow •
        ((homShiftEquivSignedOppositeCochains G M N s).symm f).hom x := by
      rw [← mul_smul, Int.units_mul_self, one_smul]
    _ = (-s * r).negOnePow • f.1 x := congrArg ((-s * r).negOnePow • ·) h

/-- Removing the degree sign leaves the quadratic normalization `J = Q_N f Q_M`. -/
theorem homShiftEquivSignedOppositeCochains_normalized_apply
    (M N : GradedModuleCat.{v} G.piece) (s : ℤ) (f : M ⟶ N.shiftObj s) (x : M) :
    (InternalGrading.quadraticExponent (-s)).negOnePow •
        (homShiftEquivSignedOppositeCochains G M N s f).1 x =
      N.grading.quadraticTwist (f.hom (M.grading.quadraticTwist x)) := by
  rw [homShiftEquivSignedOppositeCochains_apply, ← mul_smul, Int.units_mul_self, one_smul]

/-- Keller composition carries the Koszul sign relative to the actual shifted composite. -/
theorem homShiftEquivSignedOppositeCochains_comp
    (M N P : GradedModuleCat.{v} G.piece) (s t : ℤ)
    (f : M ⟶ N.shiftObj s) (g : N ⟶ P.shiftObj t) :
    let : Module B M := GradedOpposite.leftToRightModule G M.grading
    let : Module B N := GradedOpposite.leftToRightModule G N.grading
    let : Module B P := GradedOpposite.leftToRightModule G P.grading
    let : IsScalarTower R B M := GradedOpposite.leftToRight_isScalarTower G M.grading
    let : IsScalarTower R B N := GradedOpposite.leftToRight_isScalarTower G N.grading
    let : IsScalarTower R B P := GradedOpposite.leftToRight_isScalarTower G P.grading
    dgRightModuleCochains.comp
        (homShiftEquivSignedOppositeCochains G N P t g)
        (homShiftEquivSignedOppositeCochains G M N s f) (by omega) =
      (s * t).negOnePow • homShiftEquivSignedOppositeCochains G M P (t + s)
        (f ≫ (shiftFunctor s).map g ≫ (shiftFunctorAddIso G.piece t s).hom.app P) := by
  apply Subtype.ext
  ext x
  rw [dgRightModuleCochains.comp_apply]
  -- comp_apply exposes the composite; the right side still has the unit action on a
  -- cochain subtype. Reduce its subtype and linear-map coercions to the output action.
  change (homShiftEquivSignedOppositeCochains G N P t g).1
      ((homShiftEquivSignedOppositeCochains G M N s f).1 x) =
    (s * t).negOnePow • (homShiftEquivSignedOppositeCochains G M P (t + s)
      (f ≫ (shiftFunctor s).map g ≫ (shiftFunctorAddIso G.piece t s).hom.app P)).1 x
  simp only [homShiftEquivSignedOppositeCochains_apply, map_zsmul_unit]
  rw [N.grading.quadraticTwist_involutive (f.hom (M.grading.quadraticTwist x))]
  simp only [hom_comp, hom_shiftFunctor_map, hom_shiftFunctorAddIso_hom_app]
  -- The shifted composite now contains the addition-iso identity on a shifted carrier.
  -- Evaluate its linear-map composition there to expose the two scalar actions on P.
  change (InternalGrading.quadraticExponent (-s)).negOnePow •
      (InternalGrading.quadraticExponent (-t)).negOnePow •
        P.grading.quadraticTwist (g.hom (f.hom (M.grading.quadraticTwist x))) = _
  rw [← mul_smul, mul_comm (InternalGrading.quadraticExponent (-s)).negOnePow,
    InternalGrading.negOnePow_quadraticExponent_neg_add, mul_smul]
  rfl

/-- The quadratic normalization preserves the actual shifted composition on every input. -/
theorem homShiftEquivSignedOppositeCochains_normalized_comp_apply
    (M N P : GradedModuleCat.{v} G.piece) (s t : ℤ)
    (f : M ⟶ N.shiftObj s) (g : N ⟶ P.shiftObj t) (x : M) :
    (InternalGrading.quadraticExponent (-t)).negOnePow •
        (homShiftEquivSignedOppositeCochains G N P t g).1
          ((InternalGrading.quadraticExponent (-s)).negOnePow •
            (homShiftEquivSignedOppositeCochains G M N s f).1 x) =
      (InternalGrading.quadraticExponent (-(t + s))).negOnePow •
        (homShiftEquivSignedOppositeCochains G M P (t + s)
          (f ≫ (shiftFunctor s).map g ≫ (shiftFunctorAddIso G.piece t s).hom.app P)).1 x := by
  simp only [homShiftEquivSignedOppositeCochains_normalized_apply]
  rw [N.grading.quadraticTwist_involutive]
  rw [hom_comp, hom_comp, hom_shiftFunctor_map, hom_shiftFunctorAddIso_hom_app]
  rfl

end TauCeti.GradedModuleCat

end

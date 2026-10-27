/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.SignedOpposite
public import TauCeti.Algebra.Homology.DG.Module.Opposite
public import TauCeti.Algebra.Homology.DG.Module.Right.DGCategory
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Hom

/-!
# Zero-DG vertex projectives and their corner dictionary

The actual left vertex projective `P_i = Z e_i`, with its signed path-length grading and zero
differential, is a right DG module over the signed graded opposite of `Z`. Its homogeneous
cochains of degree `-s` correspond to the corner `e_i Z e_j` in degree `-s`.

The corner vector of a cochain is its value at the degree-zero vertex generator. The cochain
associated to a corner vector `x` sends an input `m` of degree `r` to
`(-1)^((-s)*r) m x`. Keller composition contributes `(-1)^(s*t)` for internal target shifts
`s` and `t`. Quadratic normalization removes this factor from the corner dictionary.

The existing common-universe DG enrichment gives a `DGHom` dictionary whose enriched composition
corresponds directly to multiplication of corner vectors. The object and cochain constructions
keep coefficient and vertex universes separate; the enriched statements use one common universe.

## References

* Huerfano--Khovanov, *A category for the adjoint representation*, Sections 3 and 4.6.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section
noncomputable section

namespace TauCeti

open CategoryTheory

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

section Cochains

universe u w

variable (k : Type w) [CommRing k] {V : Type u} [Finite V] (G : SimpleGraph V)

local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "Γ" => zigzagAlgebraInternalGrading k G
local notation "P" => zigzagAlgebraGradedProjective k G
local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)
local notation "C" => fun (i j : V) (d : ℤ) ↦
  cornerSubmodule k (e i) (e j) ⊓ zigzagAlgebraIntegerGrade k G d
local notation "H" => zigzagAlgebraGradedProjectiveHomEquivCorner k G
local notation "I" => GradedModuleCat.homShiftEquivSignedOppositeCochains Γ

/-- The left vertex projective, with its original grading and zero differential, transported
to the signed right-module convention over the graded opposite. -/
-- This structural abbreviation keeps the actual projective carrier and grading visible
-- in the public cochain types; no replacement module or grading is introduced.
noncomputable abbrev zigzagAlgebraProjectiveDGRightModule (i : V) :
    DGRightModuleCat.{w, max u w, max u w}
      (IsDGAlgebra.gradedOpposite (G := Γ) (isDGAlgebra_zero (Γ).piece)) := by
  letI : SetLike.GradedSMul (Γ).piece (P i).grading.piece := (P i).gradedSMul
  let hM := (isDGLeftModule_zero (R := k) (A := zigzagAlgebra k G)
    (Γ).piece (P i).grading.piece).gradedOppositeRight (G := Γ) («H» := (P i).grading)
  -- gradedOppositeRight proves the DG law for the existing signed right action. Supply
  -- leftToRightModule, its scalar tower and its graded action together, rather than asking
  -- inference to choose an opposite action. The existing of constructor only bundles them.
  exact @DGRightModuleCat.of k (GradedOpposite Γ) _ _ _ _ _ _ _ (P i) _ _
    (GradedOpposite.leftToRightModule Γ (P i).grading)
    (GradedOpposite.leftToRight_isScalarTower Γ (P i).grading) (P i).grading.piece _
    (GradedOpposite.leftToRight_gradedSMul Γ (P i).grading) 0 hM

local notation "D" => zigzagAlgebraProjectiveDGRightModule k G

/-- The DG input retains the actual named left vertex ideal as its carrier. -/
@[simp]
theorem zigzagAlgebraProjectiveDGRightModule_carrier (i : V) :
    (D i).carrier = (P i : Type (max u w)) := rfl

/-- The DG input retains the signed path-length grading of the vertex projective. -/
@[simp]
theorem zigzagAlgebraProjectiveDGRightModule_grading (i : V) :
    (D i).grading = (P i).grading.piece := rfl

/-- The vertex projective has zero module differential in the DG input. -/
@[simp]
theorem zigzagAlgebraProjectiveDGRightModule_differential (i : V) :
    (D i).differential = 0 := rfl

/-- Homogeneous cochains between the actual zero-DG vertex projectives. The parameter `s`
records the internal target shift, so the cochain degree is `-s`. -/
noncomputable abbrev zigzagAlgebraProjectiveCochains (i j : V) (s : ℤ) :
    Type (max u w) := by
  letI : Module (GradedOpposite Γ)ᵐᵒᵖ (P i) := (D i).moduleOp
  letI : Module (GradedOpposite Γ)ᵐᵒᵖ (P j) := (D j).moduleOp
  letI : IsScalarTower k (GradedOpposite Γ)ᵐᵒᵖ (P i) := (D i).scalarTower
  letI : IsScalarTower k (GradedOpposite Γ)ᵐᵒᵖ (P j) := (D j).scalarTower
  exact ↥(dgRightModuleCochains (R := k) (A := GradedOpposite Γ) (M := P i) (N := P j)
    (ℳ := (D i).grading) (ℳN := (D j).grading) (-s))

local notation "K" => zigzagAlgebraProjectiveCochains k G

/-- Evaluation at the vertex generator identifies degree-`-s` signed right-module cochains
with degree-`-s` vectors of the actual componentwise corner. -/
noncomputable def zigzagAlgebraProjectiveCochainsEquivCorner (i j : V) (s : ℤ) :
    K i j s ≃ₗ[k] ↥(C i j (-s)) :=
  (I (P i) (P j) s).symm.trans (H i j s)

local notation "E" => zigzagAlgebraProjectiveCochainsEquivCorner k G

/-- The forward dictionary is the actual cochain evaluation at the vertex generator. -/
@[simp]
theorem coe_zigzagAlgebraProjectiveCochainsEquivCorner_apply
    (i j : V) (s : ℤ) (f : K i j s) :
    (E i j s f : Z) = (f.1 (spanSingletonGenerator (e i)) : Z) := by
  let g := (I (P i) (P j) s).symm f
  calc
    _ = (g.hom (spanSingletonGenerator (e i)) : Z) :=
      coe_zigzagAlgebraGradedProjectiveHomEquivCorner_apply k G i j s g
    _ = _ := by
      have h := congrArg (fun y : P j ↦ (y : Z))
        (GradedModuleCat.homShiftEquivSignedOppositeCochains_symm_apply_of_mem
          Γ (P i) (P j) s f
            (spanSingletonGenerator_mem_zigzagAlgebraGradedProjective_piece_zero k G i))
      simpa only [g, mul_zero, Int.negOnePow_zero, one_smul] using h

/-- The inverse corner dictionary is signed right multiplication on a homogeneous input. -/
private theorem projectiveCochainsEquivCorner_symm_apply_of_mem
    (i j : V) (s : ℤ) (x : C i j (-s)) {r : ℤ} {m : P i}
    (hm : m ∈ (P i).grading.piece r) :
    ((E i j s).symm x).1 m = (-s * r).negOnePow •
      ((H i j s).symm x).hom m := by
  simpa only [zigzagAlgebraProjectiveCochainsEquivCorner, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm] using
      (GradedModuleCat.homShiftEquivSignedOppositeCochains_apply_of_mem
        Γ (P i) (P j) s ((H i j s).symm x) hm)

/-- In the ambient algebra, the inverse is `m ↦ (-1)^((-s)*r) m x` on degree `r`. -/
theorem coe_zigzagAlgebraProjectiveCochainsEquivCorner_symm_mul_of_mem
    (i j : V) (s : ℤ) (x : C i j (-s)) {r : ℤ} {m : P i}
    (hm : m ∈ (P i).grading.piece r) :
    (((E i j s).symm x).1 m : Z) = (-s * r).negOnePow • ((m : Z) * (x : Z)) := by
  have h := congrArg (fun y : P j ↦ (y : Z))
    (projectiveCochainsEquivCorner_symm_apply_of_mem k G i j s x hm)
  calc
    _ = (-s * r).negOnePow • (((H i j s).symm x).hom m : Z) := by
      simpa only [Units.smul_def, Submodule.coe_smul_of_tower] using h
    _ = _ := congrArg ((-s * r).negOnePow • ·)
      (coe_zigzagAlgebraGradedProjectiveHomEquivCorner_symm_apply k G i j s x m)

/-- Inverse cochains retain the unscaled corner vector on the degree-zero generator. -/
@[simp]
theorem coe_zigzagAlgebraProjectiveCochainsEquivCorner_symm_apply_generator
    (i j : V) (s : ℤ) (x : C i j (-s)) :
    (((E i j s).symm x).1 (spanSingletonGenerator (e i)) : Z) = (x : Z) := by
  have h := coe_zigzagAlgebraProjectiveCochainsEquivCorner_apply k G i j s
    ((E i j s).symm x)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- The corner vector of Keller composition is the product of corner vectors with its sign. -/
-- Normalize composition before generator evaluation unfolds the dictionary.
@[simp↓]
theorem coe_zigzagAlgebraProjectiveCochainsEquivCorner_comp
    (i j l : V) (s t : ℤ) (f : K i j s) (g : K j l t) :
    letI : Module (GradedOpposite Γ)ᵐᵒᵖ (P i) := (D i).moduleOp
    letI : Module (GradedOpposite Γ)ᵐᵒᵖ (P j) := (D j).moduleOp
    letI : Module (GradedOpposite Γ)ᵐᵒᵖ (P l) := (D l).moduleOp
    letI : IsScalarTower k (GradedOpposite Γ)ᵐᵒᵖ (P i) := (D i).scalarTower
    letI : IsScalarTower k (GradedOpposite Γ)ᵐᵒᵖ (P j) := (D j).scalarTower
    letI : IsScalarTower k (GradedOpposite Γ)ᵐᵒᵖ (P l) := (D l).scalarTower
    (E i l (t + s) (dgRightModuleCochains.comp g f (by omega)) : Z) =
      (s * t).negOnePow • ((E i j s f : Z) * (E j l t g : Z)) := by
  let f' := (I (P i) (P j) s).symm f
  let g' := (I (P j) (P l) t).symm g
  have h := GradedModuleCat.homShiftEquivSignedOppositeCochains_comp
    Γ (P i) (P j) (P l) s t f' g'
  simp only [f', g', LinearEquiv.apply_symm_apply] at h
  have hc := congrArg (fun z : K i l (t + s) ↦ (E i l (t + s) z : Z)) h
  calc
    _ = (s * t).negOnePow •
        (H i l (t + s) (f' ≫ (GradedModuleCat.shiftFunctor s).map g' ≫
          (GradedModuleCat.shiftFunctorAddIso (Γ).piece t s).hom.app (P l)) : Z) := by
      simpa only [Units.smul_def, map_zsmul, Submodule.coe_smul_of_tower,
        zigzagAlgebraProjectiveCochainsEquivCorner, LinearEquiv.trans_apply,
        LinearEquiv.symm_apply_apply] using hc
    _ = _ := by
      rw [coe_zigzagAlgebraGradedProjectiveHomEquivCorner_comp]
      rfl

/-- The quadratic normalization of the corner dictionary preserves Keller composition.
Here the normalized dictionary is `eta(-s)` times the generator-evaluation dictionary. -/
theorem coe_zigzagAlgebraProjectiveCochainsEquivCorner_normalized_comp
    (i j l : V) (s t : ℤ) (f : K i j s) (g : K j l t) :
    letI : Module (GradedOpposite Γ)ᵐᵒᵖ (P i) := (D i).moduleOp
    letI : Module (GradedOpposite Γ)ᵐᵒᵖ (P j) := (D j).moduleOp
    letI : Module (GradedOpposite Γ)ᵐᵒᵖ (P l) := (D l).moduleOp
    letI : IsScalarTower k (GradedOpposite Γ)ᵐᵒᵖ (P i) := (D i).scalarTower
    letI : IsScalarTower k (GradedOpposite Γ)ᵐᵒᵖ (P j) := (D j).scalarTower
    letI : IsScalarTower k (GradedOpposite Γ)ᵐᵒᵖ (P l) := (D l).scalarTower
    (InternalGrading.quadraticExponent (-(t + s))).negOnePow •
        (E i l (t + s) (dgRightModuleCochains.comp g f (by omega)) : Z) =
      ((InternalGrading.quadraticExponent (-s)).negOnePow • (E i j s f : Z)) *
        ((InternalGrading.quadraticExponent (-t)).negOnePow • (E j l t g : Z)) := by
  rw [coe_zigzagAlgebraProjectiveCochainsEquivCorner_comp, ← mul_smul]
  have hsign :
      (InternalGrading.quadraticExponent (-(t + s))).negOnePow * (s * t).negOnePow =
        (InternalGrading.quadraticExponent (-s)).negOnePow *
          (InternalGrading.quadraticExponent (-t)).negOnePow := by
    calc
      _ = (s * t).negOnePow *
          (InternalGrading.quadraticExponent (-(t + s))).negOnePow := mul_comm _ _
      _ = (InternalGrading.quadraticExponent (-t)).negOnePow *
          (InternalGrading.quadraticExponent (-s)).negOnePow :=
        (InternalGrading.negOnePow_quadraticExponent_neg_add s t).symm
      _ = _ := mul_comm _ _
  rw [hsign, mul_smul, smul_mul_assoc, mul_smul_comm]

end Cochains

section Enriched

universe u

variable (k : Type u) [CommRing k] {V : Type u} [Finite V] (G : SimpleGraph V)

local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "Γ" => zigzagAlgebraInternalGrading k G
local notation "P" => zigzagAlgebraGradedProjective k G
local notation "D" => zigzagAlgebraProjectiveDGRightModule k G
local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)
local notation "C" => fun (i j : V) (d : ℤ) ↦
  cornerSubmodule k (e i) (e j) ⊓ zigzagAlgebraIntegerGrade k G d
local notation "H" => zigzagAlgebraGradedProjectiveHomEquivCorner k G
local notation "E" => zigzagAlgebraProjectiveCochainsEquivCorner k G

/-- In the common universe of the existing DG enrichment, homogeneous morphisms between the
actual vertex inputs are linearly identified with their graded corner vectors. -/
noncomputable def zigzagAlgebraProjectiveDGHomEquivCorner (i j : V) (s : ℤ) :
    DGHom k (-s) (D i) (D j) ≃ₗ[k] ↥(C i j (-s)) :=
  (DGRightModuleCat.dgHomLinearEquivCochains (D i) (D j) (-s)).trans (E i j s)

local notation "L" => zigzagAlgebraProjectiveDGHomEquivCorner k G

/-- The enriched dictionary evaluates the corresponding cochain at the actual vertex generator. -/
@[simp]
theorem coe_zigzagAlgebraProjectiveDGHomEquivCorner_apply
    (i j : V) (s : ℤ) (f : DGHom k (-s) (D i) (D j)) :
    (L i j s f : Z) =
      ((DGRightModuleCat.dgHomLinearEquivCochains (D i) (D j) (-s) f).1
        (spanSingletonGenerator (e i)) : Z) := by
  exact coe_zigzagAlgebraProjectiveCochainsEquivCorner_apply k G i j s _

/-- Inverse homogeneous morphisms give the same signed right multiplication after cochain
identification. This statement uses the common-universe enrichment. -/
theorem coe_zigzagAlgebraProjectiveDGHomEquivCorner_symm_mul_of_mem
    (i j : V) (s : ℤ) (x : C i j (-s)) {r : ℤ} {m : P i}
    (hm : m ∈ (P i).grading.piece r) :
    ((DGRightModuleCat.dgHomLinearEquivCochains (D i) (D j) (-s)
        ((L i j s).symm x)).1 m : Z) =
      (-s * r).negOnePow • ((m : Z) * (x : Z)) := by
  have h : DGRightModuleCat.dgHomLinearEquivCochains (D i) (D j) (-s)
      ((L i j s).symm x) = (E i j s).symm x := by
    simp only [zigzagAlgebraProjectiveDGHomEquivCorner, LinearEquiv.symm_trans_apply,
      LinearEquiv.apply_symm_apply]
  rw [h]
  exact coe_zigzagAlgebraProjectiveCochainsEquivCorner_symm_mul_of_mem k G i j s x hm

/-- The enriched composition factor cancels the Keller factor: corner vectors multiply in the
same order as the original shifted graded maps. -/
-- Normalize composition before generator evaluation unfolds the dictionary.
@[simp↓]
theorem coe_zigzagAlgebraProjectiveDGHomEquivCorner_comp
    (i j l : V) (s t : ℤ) (f : DGHom k (-s) (D i) (D j))
    (g : DGHom k (-t) (D j) (D l)) :
    (L i l (t + s) (dgComp k f g (by omega)) : Z) =
      (L i j s f : Z) * (L j l t g : Z) := by
  let : Module (GradedOpposite Γ)ᵐᵒᵖ (P i) := (D i).moduleOp
  let : Module (GradedOpposite Γ)ᵐᵒᵖ (P j) := (D j).moduleOp
  let : Module (GradedOpposite Γ)ᵐᵒᵖ (P l) := (D l).moduleOp
  let : IsScalarTower k (GradedOpposite Γ)ᵐᵒᵖ (P i) := (D i).scalarTower
  let : IsScalarTower k (GradedOpposite Γ)ᵐᵒᵖ (P j) := (D j).scalarTower
  let : IsScalarTower k (GradedOpposite Γ)ᵐᵒᵖ (P l) := (D l).scalarTower
  -- L composes the DG/cochain identification with E. Expose only its value on dgComp
  -- so dgComp_eq can match; retain the two corner dictionaries on the right as abstract L.
  change (E i l (t + s)
    (DGRightModuleCat.dgHomLinearEquivCochains (D i) (D l) (-(t + s))
      (dgComp k f g (by omega))) : Z) = _
  calc
    _ = (s * t).negOnePow •
        (E i l (t + s) (dgRightModuleCochains.comp
          (DGRightModuleCat.dgHomLinearEquivCochains (D j) (D l) (-t) g)
          (DGRightModuleCat.dgHomLinearEquivCochains (D i) (D j) (-s) f) (by omega)) : Z) := by
      rw [DGRightModuleCat.dgComp_eq, neg_mul_neg]
      simp only [Units.smul_def, map_zsmul, Submodule.coe_smul_of_tower]
    _ = (s * t).negOnePow • (s * t).negOnePow •
        ((L i j s f : Z) * (L j l t g : Z)) := by
      rw [coe_zigzagAlgebraProjectiveCochainsEquivCorner_comp]
      rfl
    _ = _ := by rw [← mul_smul, Int.units_mul_self, one_smul]

/-- The enriched dictionary carries the actual shifted graded-map composition without a sign. -/
theorem zigzagAlgebraProjectiveDGHomEquivCorner_shifted_comp
    (i j l : V) (s t : ℤ) (f : P i ⟶ (P j).shiftObj s)
    (g : P j ⟶ (P l).shiftObj t) :
    dgComp k ((L i j s).symm (H i j s f)) ((L j l t).symm (H j l t g)) (by omega) =
      (L i l (t + s)).symm
        (H i l (t + s) (f ≫ (GradedModuleCat.shiftFunctor s).map g ≫
          (GradedModuleCat.shiftFunctorAddIso (Γ).piece t s).hom.app (P l))) := by
  apply (L i l (t + s)).injective
  apply Subtype.ext
  rw [coe_zigzagAlgebraProjectiveDGHomEquivCorner_comp,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]
  exact (coe_zigzagAlgebraGradedProjectiveHomEquivCorner_comp k G i j l s t f g).symm

/-!
## Cohomology of the vertex Hom complexes

Vanishing Hom differentials identify canonical cohomology with the homogeneous vertex
corners. The degree here belongs to the chosen path-graded DG model, independently of the
external cohomological degree in the ordinary derived category of graded modules.
-/

/-- Canonical cohomology in path degree `-s` identifies with the graded vertex corner. -/
def zigzagAlgebraProjectiveHomologyEquivCorner (i j : V) (s : ℤ) :
    (dgHomComplex k (D i) (D j)).homology (-s) ≃ₗ[k] ↥(C i j (-s)) :=
  (((dgHomComplex k (D i) (D j)).isoHomologyπ (-s - 1) (-s) (by simp)
      (DGRightModuleCat.dgHomComplex_d_eq_zero (D i) (D j)
        (zigzagAlgebraProjectiveDGRightModule_differential k G i)
        (zigzagAlgebraProjectiveDGRightModule_differential k G j) (-s - 1) (-s))).symm ≪≫
    (dgHomComplex k (D i) (D j)).iCyclesIso (-s) (-s + 1) (by simp)
      (DGRightModuleCat.dgHomComplex_d_eq_zero (D i) (D j)
        (zigzagAlgebraProjectiveDGRightModule_differential k G i)
        (zigzagAlgebraProjectiveDGRightModule_differential k G j)
        (-s) (-s + 1))).toLinearEquiv.trans (L i j s)

/-- The corner of a canonical cohomology class is the corner of its representing cycle. -/
@[simp]
theorem zigzagAlgebraProjectiveHomologyEquivCorner_homologyπ
    (i j : V) (s : ℤ) (z : (dgHomComplex k (D i) (D j)).cycles (-s)) :
    zigzagAlgebraProjectiveHomologyEquivCorner k G i j s
        (((dgHomComplex k (D i) (D j)).homologyπ (-s)).hom z) =
      L i j s (((dgHomComplex k (D i) (D j)).iCycles (-s)).hom z) := by
  let Kij := dgHomComplex k (D i) (D j)
  let eπ := Kij.isoHomologyπ (-s - 1) (-s) (by simp)
    (DGRightModuleCat.dgHomComplex_d_eq_zero (D i) (D j)
        (zigzagAlgebraProjectiveDGRightModule_differential k G i)
        (zigzagAlgebraProjectiveDGRightModule_differential k G j) (-s - 1) (-s))
  have heπ : eπ.inv.hom (eπ.hom.hom z) = z := by
    simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using
      congrArg (fun f : Kij.cycles (-s) ⟶ Kij.cycles (-s) ↦ f.hom z) eπ.hom_inv_id
  simpa only [zigzagAlgebraProjectiveHomologyEquivCorner, LinearEquiv.trans_apply,
    Iso.toLinearEquiv_apply, Iso.trans_hom, Iso.symm_hom, ModuleCat.comp_apply,
    HomologicalComplex.iCyclesIso_hom, eπ, HomologicalComplex.isoHomologyπ_hom, Kij] using
      congrArg (fun z' : Kij.cycles (-s) ↦ L i j s ((Kij.iCycles (-s)).hom z')) heπ

end Enriched

end TauCeti

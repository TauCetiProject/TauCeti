/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.HomComplex
public import TauCeti.Algebra.Homology.Monoidal.Braiding

/-!
# Composition in differential graded right-module Hom complexes

Homogeneous right-module cochains are closed under composition.  If `g` has degree `p` and `f`
has degree `q`, their composite has degree `p + q`, and the graded-commutator differential obeys

`\delta(g \circ f) = \delta(g) \circ f + (-1)^p g \circ \delta(f)`.

Consequently composition assembles into a morphism of cochain complexes

`Hom(N, P) \otimes Hom(M, N) \longrightarrow Hom(M, P)`.

The order of the tensor factors is Keller's order: the map applied second occurs first.  This is
also the order for which the tensor-product differential gives the displayed Leibniz rule.  The
closed composition and unit maps are the algebraic input for the DG category of right modules.

## Main definitions

* `TauCeti.dgRightModuleCochains.comp`: composition of homogeneous right-module cochains.
* `TauCeti.dgRightModuleCochainCompTensor`: composition on a pair of homogeneous degrees.
* `TauCeti.dgRightModuleHomComplexComp`: composition as a morphism of cochain complexes.
* `TauCeti.dgRightModuleHomComplexUnit`: the identity cochain as a morphism from the tensor unit.

## References

* B. Keller, *Deriving DG categories*, Section 2.
-/

public section

open CategoryTheory Limits MonoidalCategory MulOpposite

namespace TauCeti

universe u

variable {R A M N P : Type u}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module Aᵐᵒᵖ N] [IsScalarTower R Aᵐᵒᵖ N]
  [AddCommGroup P] [Module R P] [Module Aᵐᵒᵖ P] [IsScalarTower R Aᵐᵒᵖ P]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}
  {h : IsDGAlgebra 𝒜 d}
  {ℳ : ℤ → Submodule R M}
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
    [DirectSum.Decomposition ℳ] {dM : M →ₗ[R] M}
  {ℳN : ℤ → Submodule R N}
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳN]
    [DirectSum.Decomposition ℳN] {dN : N →ₗ[R] N}
  {ℳP : ℤ → Submodule R P}
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳP]
    [DirectSum.Decomposition ℳP] {dP : P →ₗ[R] P}
  {hM : IsDGRightModule h ℳ dM} {hN : IsDGRightModule h ℳN dN}
  {hP : IsDGRightModule h ℳP dP}

namespace dgRightModuleCochains

/-- Composition of homogeneous right-module cochains. -/
def comp {p q j : ℤ}
    (g : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳN) (ℳN := ℳP) p)
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) q)
    (hpq : p + q = j) :
    dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳP) j := by
  subst j
  exact ⟨g.1.comp f.1, by
    apply mem_iff.mpr
    rw [LinearMap.isHomogeneous_def]
    intro r x hx
    have := map_mem g (map_mem f hx)
    -- The restricted `Aᵐᵒᵖ`-linear composite coerces here to an `R`-linear map, and no
    -- evaluation lemma rewrites through that restriction.  Align its value with the two
    -- successive applications once; the remaining goal is only degree arithmetic.
    change g.1 (f.1 x) ∈ ℳP (r + (p + q))
    simpa only [add_assoc, add_comm q p] using this⟩

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition ℳN]
    [DirectSum.Decomposition ℳP] in
/-- Composition of homogeneous right-module cochains is pointwise composition. -/
@[simp]
theorem comp_apply {p q j : ℤ}
    (g : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳN) (ℳN := ℳP) p)
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) q)
    (hpq : p + q = j) (x : M) :
    ((comp g f hpq).1 : M →ₗ[Aᵐᵒᵖ] P) x = g.1 (f.1 x) := by
  subst j
  rfl

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition ℳN]
    [DirectSum.Decomposition ℳP] in
@[simp]
theorem add_comp {p q j : ℤ}
    (g g' : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳN) (ℳN := ℳP) p)
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) q)
    (hpq : p + q = j) : comp (g + g') f hpq = comp g f hpq + comp g' f hpq := by
  ext x
  simp only [comp_apply, Submodule.coe_add, LinearMap.add_apply]

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition ℳN]
    [DirectSum.Decomposition ℳP] in
@[simp]
theorem comp_add {p q j : ℤ}
    (g : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳN) (ℳN := ℳP) p)
    (f f' : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) q)
    (hpq : p + q = j) : comp g (f + f') hpq = comp g f hpq + comp g f' hpq := by
  ext x
  simp only [comp_apply, Submodule.coe_add, LinearMap.add_apply, map_add]

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition ℳN]
    [DirectSum.Decomposition ℳP] in
@[simp]
theorem zero_comp {p q j : ℤ}
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) q)
    (hpq : p + q = j) :
    comp (0 : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳN) (ℳN := ℳP) p)
      f hpq = 0 := by
  ext x
  simp only [comp_apply, Submodule.coe_zero, LinearMap.zero_apply]

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition ℳN]
    [DirectSum.Decomposition ℳP] in
@[simp]
theorem comp_zero {p q j : ℤ}
    (g : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳN) (ℳN := ℳP) p)
    (hpq : p + q = j) :
    comp g (0 : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) q)
      hpq = 0 := by
  ext x
  simp only [comp_apply, Submodule.coe_zero, LinearMap.zero_apply, map_zero]

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition ℳN]
    [DirectSum.Decomposition ℳP] in
@[simp]
theorem smul_comp {p q j : ℤ} (r : R)
    (g : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳN) (ℳN := ℳP) p)
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) q)
    (hpq : p + q = j) : comp (r • g) f hpq = r • comp g f hpq := by
  ext x
  simp only [comp_apply, Submodule.coe_smul_of_tower, LinearMap.smul_apply]

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition ℳN]
    [DirectSum.Decomposition ℳP] in
@[simp]
theorem comp_smul {p q j : ℤ} (r : R)
    (g : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳN) (ℳN := ℳP) p)
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) q)
    (hpq : p + q = j) : comp g (r • f) hpq = r • comp g f hpq := by
  ext x
  simp only [comp_apply, Submodule.coe_smul_of_tower, LinearMap.smul_apply]
  exact g.1.map_smul_of_tower r (f.1 x)

/-- The degree-zero identity cochain of a graded right module. -/
def id :
    dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳ) 0 :=
  ⟨LinearMap.id, by
    apply mem_iff.mpr
    rw [LinearMap.isHomogeneous_def]
    intro p x hx
    -- The restricted identity map coerces to an `R`-linear map here, but
    -- `LinearMap.id_coe` does not rewrite through that restriction.
    change x ∈ ℳ (p + 0)
    simpa only [LinearMap.id_coe, id_eq, add_zero] using hx⟩

omit [DirectSum.Decomposition ℳ] in
/-- The identity cochain acts as the identity map. -/
@[simp]
theorem id_apply (x : M) :
    ((id (R := R) (A := A) (ℳ := ℳ)).1 : M →ₗ[Aᵐᵒᵖ] M) x = x :=
  (rfl)

omit [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳN]
    [DirectSum.Decomposition ℳN] [DirectSum.Decomposition ℳ] in
/-- Composing on the right with the identity cochain changes nothing. -/
@[simp]
theorem comp_id {p : ℤ}
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) p) :
    comp f (id (R := R) (A := A) (ℳ := ℳ)) (add_zero p) = f := by
  ext x
  simp only [comp_apply, id_apply]

omit [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
    [DirectSum.Decomposition ℳ] [DirectSum.Decomposition ℳN] in
/-- Composing on the left with the identity cochain changes nothing. -/
@[simp]
theorem id_comp {p : ℤ}
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) p) :
    comp (id (R := R) (A := A) (ℳ := ℳN)) f (zero_add p) = f := by
  ext x
  simp only [comp_apply, id_apply]

omit [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
    [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳN]
    [DirectSum.Decomposition ℳN]
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳP]
    [DirectSum.Decomposition ℳP] in
/-- Composition of homogeneous right-module cochains is associative. -/
@[simp]
theorem comp_assoc {Q : Type u} [AddCommGroup Q] [Module R Q] [Module Aᵐᵒᵖ Q]
    [IsScalarTower R Aᵐᵒᵖ Q]
    {ℳQ : ℤ → Submodule R Q}
    {r p q j : ℤ}
    (k : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳP) (ℳN := ℳQ) r)
    (g : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳN) (ℳN := ℳP) p)
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) q)
    (hrpq : (r + p) + q = j) :
    comp (comp k g rfl) f hrpq = comp k (comp g f rfl) (by omega) := by
  ext x
  simp only [comp_apply]

/-- The differential on homogeneous right-module cochains satisfies the graded Leibniz rule for
composition. -/
theorem differential_comp {p q : ℤ}
    (g : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳN) (ℳN := ℳP) p)
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) q) :
    differential (hM := hM) (hN := hP) (p + q) (comp g f rfl) =
      comp (differential (hM := hN) (hN := hP) p g) f (by omega) +
        p.negOnePow • comp g (differential (hM := hM) (hN := hN) q f) (by omega) := by
  ext x
  simp only [differential_apply, comp_apply, map_sub, Submodule.coe_add,
    LinearMap.add_apply, Submodule.coe_smul_of_tower, LinearMap.smul_apply]
  have hmap (z : N) : g.1 (q.negOnePow • z) = q.negOnePow • g.1 z := by
    rw [Units.smul_def, map_zsmul, ← Units.smul_def]
  rw [hmap]
  rw [Int.negOnePow_add]
  rw [smul_sub, smul_smul]
  abel

/-- The identity cochain is closed. -/
@[simp]
theorem differential_id (hM : IsDGRightModule h ℳ dM) :
    differential (hM := hM) (hN := hM) 0 (id (R := R) (A := A) (ℳ := ℳ)) = 0 := by
  ext x
  simp only [differential_apply, id_apply, Int.negOnePow_zero, one_smul, sub_self,
    Submodule.coe_zero, LinearMap.zero_apply]

end dgRightModuleCochains

/-- Composition on a pair of homogeneous degrees, as a map out of the tensor product of the two
cochain modules. -/
noncomputable def dgRightModuleCochainCompTensor (p q j : ℤ) (hpq : p + q = j) :
    (dgRightModuleHomComplex hN hP).X p ⊗ (dgRightModuleHomComplex hM hN).X q ⟶
      (dgRightModuleHomComplex hM hP).X j :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun g f ↦ dgRightModuleCochains.comp g f hpq)
    (fun _ _ _ ↦ dgRightModuleCochains.add_comp _ _ _ hpq)
    (fun _ _ _ ↦ dgRightModuleCochains.smul_comp _ _ _ hpq)
    (fun _ _ _ ↦ dgRightModuleCochains.comp_add _ _ _ hpq)
    (fun _ _ _ ↦ dgRightModuleCochains.comp_smul _ _ _ hpq)

/-- On a pure tensor, homogeneous composition is ordinary composition of the underlying maps. -/
@[simp]
theorem dgRightModuleCochainCompTensor_tmul (p q j : ℤ) (hpq : p + q = j)
    (g : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳN) (ℳN := ℳP) p)
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) q) :
    ModuleCat.Hom.hom
        (A := ModuleCat.of R
            (dgRightModuleCochains (R := R) (A := A) (ℳ := ℳN) (ℳN := ℳP) p) ⊗
          ModuleCat.of R
            (dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) q))
        (B := ModuleCat.of R
          (dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳP) j))
        (dgRightModuleCochainCompTensor (hM := hM) (hN := hN) (hP := hP) p q j hpq)
        (g ⊗ₜ f) = dgRightModuleCochains.comp g f hpq :=
  (rfl)

private theorem dgRightModuleCochainCompTensor_d_apply (p q j : ℤ) (hpq : p + q = j)
    (g : (dgRightModuleHomComplex hN hP).X p)
    (f : (dgRightModuleHomComplex hM hN).X q) :
    ModuleCat.Hom.hom
        (dgRightModuleCochainCompTensor (hM := hM) (hN := hN) (hP := hP)
          (p + 1) q (j + 1) (by omega))
        (ModuleCat.Hom.hom ((dgRightModuleHomComplex hN hP).d p (p + 1)) g ⊗ₜ f) +
      p.negOnePow • ModuleCat.Hom.hom
        (dgRightModuleCochainCompTensor (hM := hM) (hN := hN) (hP := hP)
          p (q + 1) (j + 1) (by omega))
        (g ⊗ₜ ModuleCat.Hom.hom ((dgRightModuleHomComplex hM hN).d q (q + 1)) f) =
    ModuleCat.Hom.hom ((dgRightModuleHomComplex hM hP).d j (j + 1))
      (ModuleCat.Hom.hom
        (dgRightModuleCochainCompTensor (hM := hM) (hN := hN) (hP := hP) p q j hpq)
        (g ⊗ₜ f)) := by
  rw [dgRightModuleHomComplex_d, dgRightModuleHomComplex_d, dgRightModuleHomComplex_d]
  let g' : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳN) (ℳN := ℳP) p := g
  let f' : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) q := f
  -- The component and pure-tensor lemmas do not rewrite through the nested `ModuleCat.ofHom`
  -- applications in this goal.  Align those wrappers once with the degreewise cochain modules;
  -- the characteristic differential and composition lemmas then finish the proof.
  change dgRightModuleCochains.comp
        (dgRightModuleCochains.differential (hM := hN) (hN := hP) p g') f' _ +
      p.negOnePow • dgRightModuleCochains.comp g'
        (dgRightModuleCochains.differential (hM := hM) (hN := hN) q f') _ =
    dgRightModuleCochains.differential (hM := hM) (hN := hP) j
      (dgRightModuleCochains.comp g' f' hpq)
  subst j
  exact (dgRightModuleCochains.differential_comp g' f').symm

private theorem dgRightModuleCochainCompTensor_d (p q j : ℤ) (hpq : p + q = j) :
    HomologicalComplex.ιMapBifunctor (dgRightModuleHomComplex hN hP)
          (dgRightModuleHomComplex hM hN) (curriedTensor (ModuleCat.{u} R))
          (ComplexShape.up ℤ) p q j hpq ≫
        (dgRightModuleHomComplex hN hP ⊗ dgRightModuleHomComplex hM hN).d j (j + 1) ≫
        HomologicalComplex.mapBifunctorDesc
          (dgRightModuleCochainCompTensor (hM := hM) (hN := hN) (hP := hP) · · (j + 1) ·) =
      dgRightModuleCochainCompTensor (hM := hM) (hN := hN) (hP := hP) p q j hpq ≫
        (dgRightModuleHomComplex hM hP).d j (j + 1) := by
  rw [← Category.assoc, ι_tensorObj_d R _ _ p q j hpq]
  rw [Preadditive.add_comp, Linear.units_smul_comp]
  rw [Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
  rw [Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro g f
  simp only [curriedTensor_obj_obj, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply, curriedTensor_map_app, curriedTensor_obj_map, ModuleCat.hom_add,
    ModuleCat.hom_smul, LinearMap.add_apply, ModuleCat.MonoidalCategory.whiskerRight_apply,
    LinearMap.smul_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply]
  exact dgRightModuleCochainCompTensor_d_apply p q j hpq g f

/-- Composition of DG right-module cochains is a closed degree-zero map of Hom complexes. -/
noncomputable def dgRightModuleHomComplexComp :
    dgRightModuleHomComplex hN hP ⊗ dgRightModuleHomComplex hM hN ⟶
      dgRightModuleHomComplex hM hP where
  f j := HomologicalComplex.mapBifunctorDesc
    (dgRightModuleCochainCompTensor (hM := hM) (hN := hN) (hP := hP) · · j ·)
  comm' j j' hjj' := by
    replace hjj' : j + 1 = j' := hjj'
    subst j'
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    rw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
    exact (dgRightModuleCochainCompTensor_d p q j hpq).symm

/-- The identity cochain, as a closed morphism from the tensor unit to the endomorphism Hom
complex. -/
noncomputable def dgRightModuleHomComplexUnit (hM : IsDGRightModule h ℳ dM) :
    𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ) ⟶ dgRightModuleHomComplex hM hM :=
  HomologicalComplex.mkHomFromSingle
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R
      (dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳ) 0)
      (dgRightModuleCochains.id (R := R) (A := A) (ℳ := ℳ))))
    (fun i hi ↦ by
      replace hi : (0 : ℤ) + 1 = i := hi
      subst i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      rw [dgRightModuleHomComplex_d]
      -- `mkHomFromSingle` has no evaluation lemma for its closure proof.  Unfold its
      -- `ModuleCat.ofHom` composite once so the characteristic differential lemmas apply.
      change dgRightModuleCochains.differential (hM := hM) (hN := hM) 0
        (r • dgRightModuleCochains.id (R := R) (A := A) (ℳ := ℳ)) = 0
      rw [map_smul, dgRightModuleCochains.differential_id, smul_zero])

/-- The degree-zero component of the unit sends a scalar to that scalar multiple of the identity
cochain. -/
@[simp]
theorem dgRightModuleHomComplexUnit_f_zero_apply (hM : IsDGRightModule h ℳ dM) (r : R) :
    ModuleCat.Hom.hom
        (B := ModuleCat.of R
          (dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳ) 0))
        ((dgRightModuleHomComplexUnit hM).f 0)
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat.{u} R))).inv r) =
      (r • dgRightModuleCochains.id (R := R) (A := A) (ℳ := ℳ) :
        ModuleCat.of R
          (dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳ) 0)) := by
  -- `mkHomFromSingle_f` is the only component theorem for this constructor; expose that
  -- component inline so the following calculation can use the unit-iso evaluation lemmas.
  rw [show (dgRightModuleHomComplexUnit hM).f 0 =
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (𝟙_ (ModuleCat.{u} R))).hom ≫
        ModuleCat.ofHom (LinearMap.toSpanSingleton R
          (dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳ) 0)
          (dgRightModuleCochains.id (R := R) (A := A) (ℳ := ℳ))) from
    HomologicalComplex.mkHomFromSingle_f _ _]
  -- `ModuleCat.hom_comp` does not expose application through `ModuleCat.ofHom` in the form
  -- expected by the unit-iso and span-singleton evaluation lemmas.  Align that composite once;
  -- no implementation detail remains after the rewrites.
  change LinearMap.toSpanSingleton R
    (dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳ) 0)
    (dgRightModuleCochains.id (R := R) (A := A) (ℳ := ℳ))
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat.{u} R))).hom
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (𝟙_ (ModuleCat.{u} R))).inv r)) =
      r • dgRightModuleCochains.id (R := R) (A := A) (ℳ := ℳ)
  rw [Iso.inv_hom_id_apply, LinearMap.toSpanSingleton_apply]

/-- Restricting closed composition to a pair of homogeneous summands gives pointwise
composition. -/
@[reassoc (attr := simp)]
theorem ι_dgRightModuleHomComplexComp (p q j : ℤ) (hpq : p + q = j) :
    HomologicalComplex.ιMapBifunctor (dgRightModuleHomComplex hN hP)
          (dgRightModuleHomComplex hM hN) (curriedTensor (ModuleCat.{u} R))
          (ComplexShape.up ℤ) p q j hpq ≫
        (dgRightModuleHomComplexComp (hM := hM) (hN := hN) (hP := hP)).f j =
      dgRightModuleCochainCompTensor (hM := hM) (hN := hN) (hP := hP) p q j hpq := by
  unfold dgRightModuleHomComplexComp
  -- Unfolding leaves the structure component projection unreduced, while
  -- `ι_mapBifunctorDesc` is stated directly for `mapBifunctorDesc`; expose that component once.
  change HomologicalComplex.ιMapBifunctor (dgRightModuleHomComplex hN hP)
        (dgRightModuleHomComplex hM hN) (curriedTensor (ModuleCat.{u} R))
        (ComplexShape.up ℤ) p q j hpq ≫
      HomologicalComplex.mapBifunctorDesc
        (dgRightModuleCochainCompTensor (hM := hM) (hN := hN) (hP := hP) · · j ·) =
    dgRightModuleCochainCompTensor (hM := hM) (hN := hN) (hP := hP) p q j hpq
  apply HomologicalComplex.ι_mapBifunctorDesc

end TauCeti

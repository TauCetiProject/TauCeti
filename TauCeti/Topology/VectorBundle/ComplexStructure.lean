/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Topology.VectorBundle.Hom
public import TauCeti.Geometry.Symplectic.Finrank
public import TauCeti.LinearAlgebra.Complex.Module
public import TauCeti.Topology.Algebra.Module.ComplexSmulI
public import TauCeti.Topology.VectorBundle.Hom

/-!
# Complex vector bundles from fibrewise complex structures

Let `V` be a real vector bundle over `B` with model fibre `F`. A *continuous complex structure* on
`V` (`Bundle.ContinuousComplexStructure F V`) is a continuous section `J` of the endomorphism bundle
`fun b ↦ V b →L[ℝ] V b` with `J b ∘ J b = -1` on every fibre. Each fibre is then a complex vector
space, `(a + b i) • v = a • v + b • J v` (`TauCeti.AlmostComplexStructure.complexModule`). This file
shows that these complex vector spaces form a complex vector bundle `J.Fiber`, whose fibre over `b`
is `V b` with this complex structure. When `F` is finite-dimensional, the model fibre is any
finite-dimensional complex normed space `G` with `finrank ℝ F = 2 * finrank ℂ G`, supplied as an
instance `Fact (finrank ℝ F = 2 * finrank ℂ G)`. The total space of `J.Fiber` is homeomorphic to
that of `V` by the identity of the fibres
(`Bundle.ContinuousComplexStructure.totalSpaceHomeomorph`): the complex vector bundle is the real
bundle `V`, with `J` as multiplication by `i`.

The main example is the tangent bundle of a manifold with an almost complex structure, for instance
a symplectic manifold with a compatible almost complex structure. Its first Chern class is that of
the resulting complex vector bundle.

## Construction

Near a point `b₀`, read `J` in the trivialization of `V` at `b₀`: this gives a continuous family
`J' b` of complex structures on `F`, defined on the base set of that trivialization. Its complex
linear part

`A b = (1 - J' b ∘ J' b₀) / 2`

satisfies `J' b ∘ A b = A b ∘ J' b₀` (`Bundle.ContinuousComplexStructure.coord_comp_linearPart`),
so it is complex linear from `(F, J' b₀)` to `(F, J' b)`. It is the identity at `b₀`, so it is
invertible on a neighbourhood of `b₀`. Composing the trivialization of `V` with `(A b)⁻¹` and with
a fixed complex linear isomorphism `(F, J' b₀) ≃ G` gives a trivialization of `J.Fiber` that is
complex linear on every fibre (`Bundle.ContinuousComplexStructure.pretrivializationAt`). The
coordinate changes between two of them are continuous, since inversion is continuous on the
invertible operators, so these local trivializations form a `VectorPrebundle` over `ℂ`.

## Main definitions

* `Bundle.ContinuousComplexStructure F V`: a continuous section of the endomorphism bundle of `V`
  squaring to `-1`.
* `Bundle.ContinuousComplexStructure.Fiber`: the fibres of `V` with the complex structures given by
  `J`.
* `Bundle.ContinuousComplexStructure.vectorPrebundle`: the complex vector prebundle structure on
  `J.Fiber` with model fibre `G`, which gives the instances
  `FiberBundle G J.Fiber` and `VectorBundle ℂ G J.Fiber`.
* `Bundle.ContinuousComplexStructure.totalSpaceHomeomorph`: the total space of `J.Fiber` is
  homeomorphic to that of `V`, by the identity on fibres.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (a complex vector bundle is a real vector bundle with a complex structure on
  each fibre).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford (2017),
  Section 2.6 (complex structures on symplectic vector bundles).
-/

public section

noncomputable section

open Bundle FiberBundle Set Topology Module

namespace Bundle

variable {B : Type*} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (V : B → Type*) [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)] [∀ b, TopologicalSpace (V b)]
  [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousSMul ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]

/-- A *continuous complex structure* on a real vector bundle `V` with model fibre `F`: a
continuous section of the endomorphism bundle of `V` whose value at every point squares to `-1`.
-/
structure ContinuousComplexStructure where
  /-- The endomorphism of each fibre, usually denoted `J`. -/
  toFun : ∀ b, V b →L[ℝ] V b
  /-- The defining identity `J ∘ J = -1` on each fibre. -/
  comp_self : ∀ b, (toFun b).comp (toFun b) = -ContinuousLinearMap.id ℝ (V b)
  /-- `J` is a continuous section of the endomorphism bundle. -/
  continuous : Continuous fun b ↦
    TotalSpace.mk' (F →L[ℝ] F) (E := fun b ↦ V b →L[ℝ] V b) b (toFun b)

namespace ContinuousComplexStructure

variable {F V} (J : ContinuousComplexStructure F V)

/-- A continuous complex structure is applied as `J b v`. -/
instance : CoeFun (ContinuousComplexStructure F V) fun _ ↦ ∀ b, V b →L[ℝ] V b :=
  ⟨toFun⟩

@[simp]
theorem coe_mk (f : ∀ b, V b →L[ℝ] V b) (h₁ h₂) :
    (⟨f, h₁, h₂⟩ : ContinuousComplexStructure F V) = f := (rfl)

theorem coe_injective :
    Function.Injective fun J : ContinuousComplexStructure F V ↦ (⇑J : ∀ b, V b →L[ℝ] V b) := by
  rintro ⟨f, _, _⟩ ⟨g, _, _⟩ h
  congr

@[ext]
theorem ext {J K : ContinuousComplexStructure F V} (h : ∀ b v, J b v = K b v) : J = K :=
  coe_injective <| funext fun b ↦ ContinuousLinearMap.ext (h b)

@[simp]
theorem apply_apply (b : B) (v : V b) : J b (J b v) = -v := by
  simpa using congrArg (fun T : V b →L[ℝ] V b ↦ T v) (J.comp_self b)

/-- The value of `J` at `b`, as an almost complex structure on the fibre `V b`. -/
def almostComplexStructureAt (b : B) : TauCeti.AlmostComplexStructure (V b) where
  toLinearMap := (J b).toLinearMap
  square_neg := LinearMap.ext fun v ↦ by simp

@[simp]
theorem almostComplexStructureAt_apply (b : B) (v : V b) :
    J.almostComplexStructureAt b v = J b v := (rfl)

/-- The fibre `V b` of the complex vector bundle given by `J`: the same space, on which `J b` is
multiplication by `i`. -/
@[expose] def Fiber (_J : ContinuousComplexStructure F V) (b : B) : Type _ := V b

instance (b : B) : AddCommGroup (J.Fiber b) := inferInstanceAs (AddCommGroup (V b))

instance (b : B) : TopologicalSpace (J.Fiber b) := inferInstanceAs (TopologicalSpace (V b))

instance (b : B) : IsTopologicalAddGroup (J.Fiber b) :=
  inferInstanceAs (IsTopologicalAddGroup (V b))

instance (b : B) : Module ℂ (J.Fiber b) := (J.almostComplexStructureAt b).complexModule

/-- The identification of the fibre `J.Fiber b` with `V b`, as an additive equivalence. -/
def fiberEquiv (b : B) : J.Fiber b ≃+ V b := AddEquiv.refl _

theorem smul_def (b : B) (z : ℂ) (v : J.Fiber b) :
    J.fiberEquiv b (z • v) = z.re • J.fiberEquiv b v + z.im • J b (J.fiberEquiv b v) :=
  (J.almostComplexStructureAt b).complexModule_smul_def z v

@[simp]
theorem I_smul (b : B) (v : J.Fiber b) :
    J.fiberEquiv b (Complex.I • v) = J b (J.fiberEquiv b v) := by
  simp [smul_def]

@[simp]
theorem real_smul (b : B) (r : ℝ) (v : J.Fiber b) :
    J.fiberEquiv b (r • v) = r • J.fiberEquiv b v := by
  rw [← Complex.coe_smul, smul_def]
  simp

instance (b : B) : ContinuousSMul ℂ (J.Fiber b) where
  continuous_smul := by
    -- `z • v = re z • v + im z • J v`, and every operation on the right is continuous.
    have hf : Continuous fun p : ℂ × V b ↦ p.1.re • p.2 + p.1.im • J b p.2 :=
      ((Complex.continuous_re.comp continuous_fst).smul continuous_snd).add
        ((Complex.continuous_im.comp continuous_fst).smul ((J b).continuous.comp continuous_snd))
    exact hf.congr fun p ↦ (J.smul_def b p.1 p.2).symm

/-! ### `J` in the trivializations of `V` -/

/-- `J` read in the trivialization of `V` at `b₀`, as an operator on the model fibre `F`. -/
def coord (b₀ b : B) : F →L[ℝ] F :=
  ContinuousLinearMap.inCoordinates F V F V b₀ b b₀ b (J b)

theorem continuousOn_coord (b₀ : B) :
    ContinuousOn (J.coord b₀) (trivializationAt F V b₀).baseSet := by
  rw [← inter_self (trivializationAt F V b₀).baseSet]
  exact TauCeti.continuousOn_inCoordinates J.continuous b₀

/-- On the base set of the trivialization `e` of `V` at `b₀`, `J.coord b₀ b` is `J b` transported
by `e`. -/
theorem coord_apply {b₀ b : B} (hb : b ∈ (trivializationAt F V b₀).baseSet) (v : V b) :
    J.coord b₀ b ((trivializationAt F V b₀).continuousLinearMapAt ℝ b v) =
      (trivializationAt F V b₀).continuousLinearMapAt ℝ b (J b v) := by
  simp only [coord, ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Trivialization.symmL_continuousLinearMapAt _ hb]

theorem coord_comp_coord {b₀ b : B} (hb : b ∈ (trivializationAt F V b₀).baseSet) :
    (J.coord b₀ b).comp (J.coord b₀ b) = -ContinuousLinearMap.id ℝ F := by
  ext w
  obtain ⟨v, rfl⟩ : ∃ v, (trivializationAt F V b₀).continuousLinearMapAt ℝ b v = w :=
    ⟨(trivializationAt F V b₀).symmL ℝ b w,
      Trivialization.continuousLinearMapAt_symmL _ hb w⟩
  simp only [ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.id_apply]
  rw [coord_apply J hb, coord_apply J hb, apply_apply, map_neg]

/-- The complex linear part `(1 - J' b ∘ J' b₀) / 2` of the identity of `F`, from the complex
structure `J' b₀ = J.coord b₀ b₀` to the complex structure `J' b = J.coord b₀ b`. -/
def linearPart (b₀ b : B) : F →L[ℝ] F :=
  (2⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ F - (J.coord b₀ b).comp (J.coord b₀ b₀))

theorem continuousOn_linearPart (b₀ : B) :
    ContinuousOn (J.linearPart b₀) (trivializationAt F V b₀).baseSet :=
  (continuousOn_const.sub ((J.continuousOn_coord b₀).clm_comp continuousOn_const)).const_smul
    (2⁻¹ : ℝ)

@[simp]
theorem linearPart_self (b₀ : B) : J.linearPart b₀ b₀ = 1 := by
  rw [linearPart, coord_comp_coord J (mem_baseSet_trivializationAt F V b₀), sub_neg_eq_add,
    ← two_smul ℝ, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul, ContinuousLinearMap.one_def]

/-- `J.linearPart b₀ b` intertwines the complex structures `J' b₀` and `J' b`. -/
theorem coord_comp_linearPart {b₀ b : B} (hb : b ∈ (trivializationAt F V b₀).baseSet) :
    (J.coord b₀ b).comp (J.linearPart b₀ b) = (J.linearPart b₀ b).comp (J.coord b₀ b₀) := by
  ext w
  have hw := congrArg (fun T : F →L[ℝ] F ↦ T (J.coord b₀ b₀ w)) (coord_comp_coord J hb)
  have hw₀ := congrArg (fun T : F →L[ℝ] F ↦ T w)
    (coord_comp_coord J (mem_baseSet_trivializationAt F V b₀))
  simp only [ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.id_apply] at hw hw₀
  simp only [linearPart, ContinuousLinearMap.comp_apply, smul_apply,
    sub_apply, ContinuousLinearMap.id_apply, map_smul, map_sub, map_neg, hw,
    hw₀]
  rw [sub_neg_eq_add, sub_neg_eq_add, add_comm]

/-- The neighbourhood of `b₀` on which `J.linearPart b₀` is invertible: the base set of the
complex trivialization at `b₀`. -/
def unitSet (b₀ : B) : Set B :=
  (trivializationAt F V b₀).baseSet ∩ J.linearPart b₀ ⁻¹' {T | IsUnit T}

theorem isOpen_unitSet [CompleteSpace F] (b₀ : B) : IsOpen (J.unitSet b₀) :=
  (J.continuousOn_linearPart b₀).isOpen_inter_preimage (trivializationAt F V b₀).open_baseSet
    Units.isOpen

theorem mem_unitSet_self (b₀ : B) : b₀ ∈ J.unitSet b₀ :=
  ⟨mem_baseSet_trivializationAt F V b₀, by simp [isUnit_one]⟩

theorem unitSet_subset (b₀ : B) : J.unitSet b₀ ⊆ (trivializationAt F V b₀).baseSet :=
  inter_subset_left

theorem continuousOn_inverse_linearPart [CompleteSpace F] (b₀ : B) :
    ContinuousOn (fun b ↦ Ring.inverse (J.linearPart b₀ b)) (J.unitSet b₀) := by
  intro b hb
  have hunit : IsUnit (J.linearPart b₀ b) := hb.2
  obtain ⟨u, hu⟩ := hunit
  have hc : ContinuousAt Ring.inverse (J.linearPart b₀ b) :=
    hu ▸ NormedRing.inverse_continuousAt u
  exact hc.comp_continuousWithinAt
    ((J.continuousOn_linearPart b₀).mono (J.unitSet_subset b₀) b hb)

theorem inverse_linearPart_mul {b₀ b : B} (hb : b ∈ J.unitSet b₀) :
    Ring.inverse (J.linearPart b₀ b) * J.linearPart b₀ b = 1 :=
  Ring.inverse_mul_cancel _ hb.2

theorem linearPart_mul_inverse {b₀ b : B} (hb : b ∈ J.unitSet b₀) :
    J.linearPart b₀ b * Ring.inverse (J.linearPart b₀ b) = 1 :=
  Ring.mul_inverse_cancel _ hb.2

/-- The inverse of `J.linearPart b₀ b` intertwines `J' b` and `J' b₀`. -/
theorem inverse_linearPart_coord {b₀ b : B} (hb : b ∈ J.unitSet b₀) (w : F) :
    Ring.inverse (J.linearPart b₀ b) (J.coord b₀ b w) =
      J.coord b₀ b₀ (Ring.inverse (J.linearPart b₀ b) w) := by
  set A := J.linearPart b₀ b
  set A' := Ring.inverse A
  have h := congrArg (fun T : F →L[ℝ] F ↦ A' (T (A' w))) (J.coord_comp_linearPart hb.1)
  have h₁ := congrArg (fun T : F →L[ℝ] F ↦ T w) (J.linearPart_mul_inverse hb)
  have h₂ := congrArg (fun T : F →L[ℝ] F ↦ T (J.coord b₀ b₀ (A' w)))
    (J.inverse_linearPart_mul hb)
  simp only [ContinuousLinearMap.comp_apply, mul_apply_eq_comp,
    one_apply_eq_self] at h h₁ h₂
  rw [h₁] at h
  rw [h, h₂]

/-- `J' b₀ = J.coord b₀ b₀`, as an almost complex structure on the model fibre `F`. -/
private def coordAt (b₀ : B) : TauCeti.AlmostComplexStructure F where
  toLinearMap := (J.coord b₀ b₀).toLinearMap
  square_neg := LinearMap.ext fun w ↦ by
    simpa using congrArg (fun T : F →L[ℝ] F ↦ T w)
      (J.coord_comp_coord (mem_baseSet_trivializationAt F V b₀))

/-! ### The model fibre -/

section Model

variable (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [FiniteDimensional ℝ F]
variable [Fact (finrank ℝ F = 2 * finrank ℂ G)]

/-- A real linear isomorphism `G ≃ F` carrying multiplication by `i` to `J' b₀`. -/
def modelEquiv (b₀ : B) : G ≃L[ℝ] F :=
  ((J.coordAt b₀).exists_linearEquiv_I_smul Fact.out).choose.toContinuousLinearEquiv

theorem modelEquiv_I_smul (b₀ : B) (z : G) :
    J.modelEquiv G b₀ (Complex.I • z) = J.coord b₀ b₀ (J.modelEquiv G b₀ z) :=
  ((J.coordAt b₀).exists_linearEquiv_I_smul (G := G) Fact.out).choose_spec z

theorem modelEquiv_symm_coord (b₀ : B) (w : F) :
    (J.modelEquiv G b₀).symm (J.coord b₀ b₀ w) = Complex.I • (J.modelEquiv G b₀).symm w := by
  apply (J.modelEquiv G b₀).injective
  rw [modelEquiv_I_smul, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply]

/-! ### The local trivializations -/

/-- The fibre map of the complex trivialization at `b₀`: the trivialization of `V` at `b₀`,
followed by the inverse of `J.linearPart b₀ b` and the identification of `F` with `G`. -/
def fiberMap (b₀ b : B) : V b →L[ℝ] G :=
  ((J.modelEquiv G b₀).symm : F →L[ℝ] G).comp
    ((Ring.inverse (J.linearPart b₀ b)).comp
      ((trivializationAt F V b₀).continuousLinearMapAt ℝ b))

/-- The fibre maps of the complex trivialization at `b₀` carry `J` to multiplication by `i`. -/
theorem fiberMap_apply_apply {b₀ b : B} (hb : b ∈ J.unitSet b₀) (v : V b) :
    J.fiberMap G b₀ b (J b v) = Complex.I • J.fiberMap G b₀ b v := by
  simp only [fiberMap, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ← J.coord_apply (J.unitSet_subset b₀ hb), J.inverse_linearPart_coord hb,
    modelEquiv_symm_coord]

/-- The pretrivialization of `J.Fiber` at `b₀`, with base set `J.unitSet b₀`. -/
def pretrivializationAt (b₀ : B) : Pretrivialization G (π G J.Fiber) where
  toFun p := (p.1, J.fiberMap G b₀ p.1 (J.fiberEquiv p.1 p.2))
  invFun p := ⟨p.1, (J.fiberEquiv p.1).symm ((trivializationAt F V b₀).symm p.1
    (J.linearPart b₀ p.1 (J.modelEquiv G b₀ p.2)))⟩
  source := TotalSpace.proj ⁻¹' J.unitSet b₀
  target := J.unitSet b₀ ×ˢ univ
  map_source' _ h := ⟨h, mem_univ _⟩
  map_target' _ h := h.1
  left_inv' := fun ⟨b, v⟩ hb ↦ by
    have hb' : b ∈ (trivializationAt F V b₀).baseSet := J.unitSet_subset b₀ hb
    have h := congrArg (fun T : F →L[ℝ] F ↦
      T ((trivializationAt F V b₀).continuousLinearMapAt ℝ b (J.fiberEquiv b v)))
      (J.linearPart_mul_inverse hb)
    simp only [mul_apply_eq_comp, one_apply_eq_self] at h
    simp only [fiberMap, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, h]
    rw [← Trivialization.symmL_apply (R := ℝ) _ hb',
      Trivialization.symmL_continuousLinearMapAt _ hb', AddEquiv.symm_apply_apply]
  right_inv' := fun ⟨b, z⟩ hb ↦ by
    have hb' : b ∈ (trivializationAt F V b₀).baseSet := J.unitSet_subset b₀ hb.1
    have h := congrArg (fun T : F →L[ℝ] F ↦ T (J.modelEquiv G b₀ z))
      (J.inverse_linearPart_mul hb.1)
    simp only [mul_apply_eq_comp, one_apply_eq_self] at h
    simp only [fiberMap, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      AddEquiv.apply_symm_apply]
    rw [← Trivialization.symmL_apply (R := ℝ) _ hb',
      Trivialization.continuousLinearMapAt_symmL _ hb', h,
      ContinuousLinearEquiv.symm_apply_apply]
  open_target :=
    have := FiniteDimensional.complete ℝ F
    (J.isOpen_unitSet b₀).prod isOpen_univ
  baseSet := J.unitSet b₀
  open_baseSet :=
    have := FiniteDimensional.complete ℝ F
    J.isOpen_unitSet b₀
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

@[simp]
theorem pretrivializationAt_apply (b₀ : B) (p : TotalSpace G J.Fiber) :
    J.pretrivializationAt G b₀ p = (p.1, J.fiberMap G b₀ p.1 (J.fiberEquiv p.1 p.2)) := (rfl)

@[simp]
theorem baseSet_pretrivializationAt (b₀ : B) :
    (J.pretrivializationAt G b₀).baseSet = J.unitSet b₀ := (rfl)

theorem pretrivializationAt_symm_apply {b₀ b : B} (hb : b ∈ J.unitSet b₀) (z : G) :
    J.fiberEquiv b ((J.pretrivializationAt G b₀).symm b z) =
      (trivializationAt F V b₀).symm b (J.linearPart b₀ b (J.modelEquiv G b₀ z)) := by
  rw [Pretrivialization.symm_apply _ hb]
  rfl

instance isLinear_pretrivializationAt (b₀ : B) : (J.pretrivializationAt G b₀).IsLinear ℂ where
  linear b hb :=
    { map_add v w := by simp
      map_smul c v := by
        simp only [pretrivializationAt_apply]
        rw [← Complex.re_smul_add_im_smul c v]
        simp [smul_def, J.fiberMap_apply_apply G hb] }

/-- The coordinate change from the complex trivialization at `b₀` to the one at `b₁`, as a real
linear operator on `G`. -/
private def realCoordChange (b₀ b₁ b : B) : G →L[ℝ] G :=
  ((J.modelEquiv G b₁).symm : F →L[ℝ] G).comp ((Ring.inverse (J.linearPart b₁ b)).comp
    (((trivializationAt F V b₀).coordChangeL ℝ (trivializationAt F V b₁) b : F →L[ℝ] F).comp
      ((J.linearPart b₀ b).comp (J.modelEquiv G b₀ : G →L[ℝ] F))))

private theorem realCoordChange_apply {b₀ b₁ b : B} (hb : b ∈ J.unitSet b₀ ∩ J.unitSet b₁)
    (z : G) :
    J.realCoordChange G b₀ b₁ b z =
      (J.pretrivializationAt G b₁ ⟨b, (J.pretrivializationAt G b₀).symm b z⟩).2 := by
  have hb' : b ∈ (trivializationAt F V b₀).baseSet ∩ (trivializationAt F V b₁).baseSet :=
    ⟨J.unitSet_subset b₀ hb.1, J.unitSet_subset b₁ hb.2⟩
  simp only [realCoordChange, pretrivializationAt_apply, J.pretrivializationAt_symm_apply G hb.1,
    fiberMap, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Trivialization.coordChangeL_apply _ _ hb',
    Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hb'.2]

private theorem continuousOn_realCoordChange (b₀ b₁ : B) :
    ContinuousOn (J.realCoordChange G b₀ b₁) (J.unitSet b₀ ∩ J.unitSet b₁) := by
  have := FiniteDimensional.complete ℝ F
  have hsub : J.unitSet b₀ ∩ J.unitSet b₁ ⊆
      (trivializationAt F V b₀).baseSet ∩ (trivializationAt F V b₁).baseSet :=
    inter_subset_inter (J.unitSet_subset b₀) (J.unitSet_subset b₁)
  exact continuousOn_const.clm_comp (((J.continuousOn_inverse_linearPart b₁).mono
    inter_subset_right).clm_comp (((continuousOn_coordChange ℝ _ _).mono hsub).clm_comp
      ((((J.continuousOn_linearPart b₀).mono (J.unitSet_subset b₀)).mono
        inter_subset_left).clm_comp continuousOn_const)))

private theorem realCoordChange_I_smul {b₀ b₁ b : B} (hb : b ∈ J.unitSet b₀ ∩ J.unitSet b₁)
    (z : G) :
    J.realCoordChange G b₀ b₁ b (Complex.I • z) = Complex.I • J.realCoordChange G b₀ b₁ b z := by
  rw [J.realCoordChange_apply G hb, J.realCoordChange_apply G hb,
    ← Pretrivialization.symmₗ_apply ℂ _ hb.1, map_smul, Pretrivialization.symmₗ_apply ℂ _ hb.1]
  exact ((J.pretrivializationAt G b₁).linear ℂ hb.2).map_smul _ _

private theorem exists_coordChange (b₀ b₁ : B) :
    ∃ f : B → G →L[ℂ] G, ContinuousOn f (J.unitSet b₀ ∩ J.unitSet b₁) ∧
      ∀ b ∈ J.unitSet b₀ ∩ J.unitSet b₁, ∀ z : G,
        f b z = (J.pretrivializationAt G b₁ ⟨b, (J.pretrivializationAt G b₀).symm b z⟩).2 := by
  classical
  let f : B → G →L[ℂ] G := fun b ↦
    if h : ∀ z, J.realCoordChange G b₀ b₁ b (Complex.I • z) =
        Complex.I • J.realCoordChange G b₀ b₁ b z then
      (J.realCoordChange G b₀ b₁ b).complexOfMapISmul h
    else 0
  have hf : ∀ b ∈ J.unitSet b₀ ∩ J.unitSet b₁,
      (f b).restrictScalars ℝ = J.realCoordChange G b₀ b₁ b := fun b hb ↦ by
    simp only [f, J.realCoordChange_I_smul G hb, implies_true, dite_true,
      ContinuousLinearMap.restrictScalars_complexOfMapISmul]
  refine ⟨f, ?_, fun b hb z ↦ ?_⟩
  · rw [(ContinuousLinearMap.restrictScalarsIsometry ℂ G G ℝ ℝ).isometry.isUniformInducing
      |>.isInducing.continuousOn_iff]
    exact (J.continuousOn_realCoordChange G b₀ b₁).congr fun b hb ↦ hf b hb
  · rw [← J.realCoordChange_apply G hb, ← hf b hb, ContinuousLinearMap.coe_restrictScalars']

/-- On its own centre, the fibre map of the complex trivialization at `b` is a real linear
homeomorphism. -/
private theorem isInducing_fiberMap_self (b : B) : IsInducing (J.fiberMap G b b) := by
  have hb := mem_baseSet_trivializationAt F V b
  have h : ⇑(J.fiberMap G b b) =
      ((trivializationAt F V b).continuousLinearEquivAt ℝ b hb).trans (J.modelEquiv G b).symm := by
    ext v
    simp [fiberMap, Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hb]
  rw [h]
  exact (((trivializationAt F V b).continuousLinearEquivAt ℝ b hb).trans
    (J.modelEquiv G b).symm).toHomeomorph.isInducing

/-- The complex vector prebundle structure on `J.Fiber` with model fibre `G`, whose
pretrivializations are the complex trivializations `J.pretrivializationAt G b₀`. -/
def vectorPrebundle : VectorPrebundle ℂ G J.Fiber where
  pretrivializationAtlas := range (J.pretrivializationAt G)
  pretrivialization_linear' := by
    rintro _ ⟨b₀, rfl⟩
    infer_instance
  pretrivializationAt := J.pretrivializationAt G
  mem_base_pretrivializationAt := J.mem_unitSet_self
  pretrivialization_mem_atlas b := mem_range_self b
  exists_coordChange := by
    rintro _ ⟨b₀, rfl⟩ _ ⟨b₁, rfl⟩
    exact J.exists_coordChange G b₀ b₁
  totalSpaceMk_isInducing b :=
    isInducing_const_prod.mpr (J.isInducing_fiberMap_self G b)

/-- The topology on the total space of `J.Fiber` given by its complex trivializations; by
`Bundle.ContinuousComplexStructure.totalSpaceHomeomorph` it is the topology of the total space of
`V`. -/
instance : TopologicalSpace (TotalSpace G J.Fiber) := (J.vectorPrebundle G).totalSpaceTopology

/-- `J.Fiber` is a fibre bundle with model fibre `G`. -/
instance : FiberBundle G J.Fiber := (J.vectorPrebundle G).toFiberBundle

/-- `J.Fiber` is a complex vector bundle with model fibre `G`. -/
instance : VectorBundle ℂ G J.Fiber := (J.vectorPrebundle G).toVectorBundle

@[simp]
theorem trivializationAt_apply (b₀ : B) (p : TotalSpace G J.Fiber) :
    trivializationAt G J.Fiber b₀ p = (p.1, J.fiberMap G b₀ p.1 (J.fiberEquiv p.1 p.2)) := (rfl)

@[simp]
theorem baseSet_trivializationAt (b₀ : B) :
    (trivializationAt G J.Fiber b₀).baseSet = J.unitSet b₀ := (rfl)

private theorem linearPart_modelEquiv_fiberMap {b₀ b : B} (hb : b ∈ J.unitSet b₀) (v : V b) :
    J.linearPart b₀ b (J.modelEquiv G b₀ (J.fiberMap G b₀ b v)) =
      (trivializationAt F V b₀).continuousLinearMapAt ℝ b v := by
  have h := congrArg (fun T : F →L[ℝ] F ↦
    T ((trivializationAt F V b₀).continuousLinearMapAt ℝ b v)) (J.linearPart_mul_inverse hb)
  simpa only [fiberMap, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, mul_apply_eq_comp, one_apply_eq_self] using h

/-- The identity of the fibres, from the total space of `J.Fiber` to that of `V`, is continuous.
-/
private theorem continuous_toTotalSpace :
    Continuous fun p : TotalSpace G J.Fiber ↦ (⟨p.1, J.fiberEquiv p.1 p.2⟩ : TotalSpace F V) := by
  refine continuous_iff_continuousAt.mpr fun p₀ ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(FiberBundle.continuous_proj G J.Fiber).continuousAt, ?_⟩
  -- Near `p₀`, the coordinate of `p` in the trivialization of `V` at `p₀.1` is
  -- `A (φ z)`, where `z` is its coordinate in the complex trivialization at `p₀.1`.
  have hsrc : (trivializationAt G J.Fiber p₀.1).source ∈ 𝓝 p₀ :=
    (trivializationAt G J.Fiber p₀.1).open_source.mem_nhds
      (FiberBundle.mem_trivializationAt_proj_source)
  have hA : ContinuousAt (fun p : TotalSpace G J.Fiber ↦ J.linearPart p₀.1 p.1) p₀ :=
    ((J.continuousOn_linearPart p₀.1).continuousAt
      ((trivializationAt F V p₀.1).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F V p₀.1))).comp
      (FiberBundle.continuous_proj G J.Fiber).continuousAt
  have hT : ContinuousAt (fun p ↦ (trivializationAt G J.Fiber p₀.1 p).2) p₀ :=
    ((trivializationAt G J.Fiber p₀.1).continuousAt
      FiberBundle.mem_trivializationAt_proj_source).snd
  refine (hA.clm_apply ((J.modelEquiv G p₀.1).continuous.continuousAt.comp hT))
    |>.congr_of_eventuallyEq ?_
  filter_upwards [hsrc] with p hp
  have hp' : p.1 ∈ (trivializationAt F V p₀.1).baseSet := J.unitSet_subset _ hp
  simp only [Function.comp_apply, trivializationAt_apply,
    J.linearPart_modelEquiv_fiberMap G hp,
    Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hp']

/-- The identity of the fibres, from the total space of `V` to that of `J.Fiber`, is continuous.
-/
private theorem continuous_ofTotalSpace :
    Continuous fun p : TotalSpace F V ↦
      (⟨p.1, (J.fiberEquiv p.1).symm p.2⟩ : TotalSpace G J.Fiber) := by
  have := FiniteDimensional.complete ℝ F
  refine continuous_iff_continuousAt.mpr fun q₀ ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(FiberBundle.continuous_proj F V).continuousAt, ?_⟩
  -- Near `q₀`, the complex coordinate of `q` is `φ⁻¹ (A⁻¹ w)`, where `w` is its coordinate in
  -- the trivialization of `V` at `q₀.1`.
  have hU : J.unitSet q₀.1 ∈ 𝓝 q₀.1 := (J.isOpen_unitSet q₀.1).mem_nhds (J.mem_unitSet_self q₀.1)
  have hA : ContinuousAt (fun q : TotalSpace F V ↦ Ring.inverse (J.linearPart q₀.1 q.1)) q₀ :=
    ((J.continuousOn_inverse_linearPart q₀.1).continuousAt hU).comp
      (FiberBundle.continuous_proj F V).continuousAt
  have he : ContinuousAt (fun q ↦ (trivializationAt F V q₀.1 q).2) q₀ :=
    ((trivializationAt F V q₀.1).continuousAt FiberBundle.mem_trivializationAt_proj_source).snd
  refine ((J.modelEquiv G q₀.1).symm.continuous.continuousAt.comp
    (hA.clm_apply he)).congr_of_eventuallyEq ?_
  filter_upwards [(FiberBundle.continuous_proj F V).continuousAt.preimage_mem_nhds hU] with q hq
  have hq' : q.1 ∈ (trivializationAt F V q₀.1).baseSet := J.unitSet_subset _ hq
  simp only [Function.comp_apply, trivializationAt_apply, fiberMap, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, AddEquiv.apply_symm_apply,
    Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hq']

/-- The total space of the complex vector bundle `J.Fiber` is homeomorphic to that of `V`, by the
identity of the fibres. -/
def totalSpaceHomeomorph : TotalSpace G J.Fiber ≃ₜ TotalSpace F V where
  toFun p := ⟨p.1, J.fiberEquiv p.1 p.2⟩
  invFun p := ⟨p.1, (J.fiberEquiv p.1).symm p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := J.continuous_toTotalSpace G
  continuous_invFun := J.continuous_ofTotalSpace G

@[simp]
theorem totalSpaceHomeomorph_apply (p : TotalSpace G J.Fiber) :
    J.totalSpaceHomeomorph G p = ⟨p.1, J.fiberEquiv p.1 p.2⟩ := (rfl)

@[simp]
theorem totalSpaceHomeomorph_symm_apply (p : TotalSpace F V) :
    (J.totalSpaceHomeomorph G).symm p = ⟨p.1, (J.fiberEquiv p.1).symm p.2⟩ := (rfl)

end Model

end ContinuousComplexStructure

end Bundle

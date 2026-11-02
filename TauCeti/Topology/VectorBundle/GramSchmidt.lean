/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Topology.VectorBundle.Riemannian

/-!
# Continuous orthonormal frames

The native Gram–Schmidt process is continuous for continuous families of linearly independent
vectors in a continuous Riemannian vector bundle. Applying it to the inverse image of a fixed
basis under a bundle trivialization gives continuous local orthonormal bases. The construction
uses Mathlib's `InnerProductSpace.gramSchmidt` and `gramSchmidtNormed`, including their span
and orthonormality theorems, rather than a separate orthogonalization procedure.

The continuity argument follows the sectionwise Gram–Schmidt construction of Patrick Massot
and Michael Rothgang in Mathlib PR [#26221](https://github.com/leanprover-community/mathlib4/pull/26221),
revision `c487a9a1d25ee47368d6e095f701fc633bb6847a`, adapted to arbitrary continuous base spaces
and families over a varying base map.
-/

public section

open Bundle Filter Set InnerProductSpace
open scoped Topology

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]
  {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]

attribute [local instance] IsWellOrder.toHasWellFounded

variable {X : Type*} [TopologicalSpace X] {b : X → B} {v : ι → ∀ x, E (b x)}
  {s : Set X} {x : X}

/-- Gram–Schmidt applied in each fiber is continuous at a linearly independent family. -/
theorem ContinuousWithinAt.gramSchmidt_bundle
    (hv : ∀ i, ContinuousWithinAt (fun y ↦ (v i y : TotalSpace F E)) s x)
    (hli : LinearIndependent ℝ (fun i ↦ v i x)) (n : ι) :
    ContinuousWithinAt
      (fun y ↦ TotalSpace.mk' F (b y) (gramSchmidt ℝ (fun i ↦ v i y) n)) s x := by
  classical
  induction n using WellFoundedLT.induction with
  | ind n ih =>
    let e := trivializationAt F E (b x)
    have hb := ((FiberBundle.continuousWithinAt_totalSpace F _).1 (hv n)).1
    have hmem : ∀ᶠ y in 𝓝[s] x, b y ∈ e.baseSet :=
      hb (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E (b x)))
    have hc (i : ι) := ((FiberBundle.continuousWithinAt_totalSpace F _).1 (hv i)).2
    have hg (i : ι) (hi : i < n) :=
      ((FiberBundle.continuousWithinAt_totalSpace F _).1 (ih i hi)).2
    have hnorm (i : ι) (hi : i < n) :
        ContinuousWithinAt (fun y ↦ ‖gramSchmidt ℝ (fun j ↦ v j y) i‖) s x := by
      simpa only [norm_eq_sqrt_real_inner] using ((ih i hi).inner_bundle (ih i hi)).sqrt
    have hcont := (hc n).sub <| tendsto_finsetSum (Finset.Iio n) fun i hi ↦
      let hi' := Finset.mem_Iio.mp hi
      (((ih i hi').inner_bundle (hv n)).div ((hnorm i hi').pow 2)
        (pow_ne_zero 2 (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i hli)))).smul (hg i hi')
    have hformula (y : X) (hy : b y ∈ e.baseSet) :
        (e ⟨b y, gramSchmidt ℝ (fun i ↦ v i y) n⟩).2 =
          (e ⟨b y, v n y⟩).2 - ∑ i ∈ Finset.Iio n,
            (@Inner.inner ℝ _ _ (gramSchmidt ℝ (fun j ↦ v j y) i) (v n y) /
              ‖gramSchmidt ℝ (fun j ↦ v j y) i‖ ^ 2) •
                (e ⟨b y, gramSchmidt ℝ (fun j ↦ v j y) i⟩).2 := by
      simp only [← e.continuousLinearMapAt_apply_of_mem (R := ℝ) hy,
        ← map_smul, ← map_sum, ← map_sub]
      exact congrArg (e.continuousLinearMapAt ℝ (b y))
        (eq_sub_iff_add_eq.mpr (gramSchmidt_def'' ℝ (fun i ↦ v i y) n).symm)
    rw [FiberBundle.continuousWithinAt_totalSpace]
    exact ⟨hb, hcont.congr_of_eventuallyEq (hmem.mono hformula)
      (hformula x (mem_baseSet_trivializationAt F E (b x)))⟩

/-- Normalized Gram–Schmidt is continuous at a linearly independent family. -/
theorem ContinuousWithinAt.gramSchmidtNormed_bundle
    (hv : ∀ i, ContinuousWithinAt (fun y ↦ (v i y : TotalSpace F E)) s x)
    (hli : LinearIndependent ℝ (fun i ↦ v i x)) (n : ι) :
    ContinuousWithinAt
      (fun y ↦ TotalSpace.mk' F (b y) (gramSchmidtNormed ℝ (fun i ↦ v i y) n)) s x := by
  have hg := ContinuousWithinAt.gramSchmidt_bundle hv hli n
  have hn : ContinuousWithinAt (fun y ↦ ‖gramSchmidt ℝ (fun i ↦ v i y) n‖) s x := by
    simpa only [norm_eq_sqrt_real_inner] using (hg.inner_bundle hg).sqrt
  let e := trivializationAt F E (b x)
  obtain ⟨hb, hc⟩ := (FiberBundle.continuousWithinAt_totalSpace F _).1 hg
  have hmem : ∀ᶠ y in 𝓝[s] x, b y ∈ e.baseSet :=
    hb (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E (b x)))
  have hformula (y : X) (hy : b y ∈ e.baseSet) :
      (e ⟨b y, gramSchmidtNormed ℝ (fun i ↦ v i y) n⟩).2 =
        ‖gramSchmidt ℝ (fun i ↦ v i y) n‖⁻¹ •
          (e ⟨b y, gramSchmidt ℝ (fun i ↦ v i y) n⟩).2 := by
    simp only [gramSchmidtNormed, ← e.continuousLinearMapAt_apply_of_mem (R := ℝ) hy,
      map_smul, RCLike.ofReal_real_eq_id, id_eq]
  have H := (hn.inv₀ (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero n hli))).smul hc
  rw [FiberBundle.continuousWithinAt_totalSpace]
  exact ⟨hb, H.congr_of_eventuallyEq (hmem.mono hformula)
    (hformula x (mem_baseSet_trivializationAt F E (b x)))⟩

/-- Normalized Gram–Schmidt is continuous at a linearly independent family. -/
theorem ContinuousAt.gramSchmidtNormed_bundle
    (hv : ∀ i, ContinuousAt (fun y ↦ (v i y : TotalSpace F E)) x)
    (hli : LinearIndependent ℝ (fun i ↦ v i x)) (n : ι) :
    ContinuousAt
      (fun y ↦ TotalSpace.mk' F (b y) (gramSchmidtNormed ℝ (fun i ↦ v i y) n)) x := by
  rw [← continuousWithinAt_univ]
  exact ContinuousWithinAt.gramSchmidtNormed_bundle
    (fun i ↦ (hv i).continuousWithinAt) hli n

/-- Normalized Gram–Schmidt preserves continuity on a set where the input families are
linearly independent. -/
theorem ContinuousOn.gramSchmidtNormed_bundle
    (hv : ∀ i, ContinuousOn (fun y ↦ (v i y : TotalSpace F E)) s)
    (hli : ∀ y ∈ s, LinearIndependent ℝ (fun i ↦ v i y)) (n : ι) :
    ContinuousOn (fun y ↦ TotalSpace.mk' F (b y) (gramSchmidtNormed ℝ (fun i ↦ v i y) n)) s :=
  fun y hy ↦ ContinuousWithinAt.gramSchmidtNormed_bundle (fun i ↦ hv i y hy) (hli y hy) n

/-- Normalized Gram–Schmidt preserves a continuous family of linearly independent vectors. -/
theorem Continuous.gramSchmidtNormed_bundle
    (hv : ∀ i, Continuous (fun y ↦ (v i y : TotalSpace F E)))
    (hli : ∀ y, LinearIndependent ℝ (fun i ↦ v i y)) (n : ι) :
    Continuous (fun y ↦ TotalSpace.mk' F (b y) (gramSchmidtNormed ℝ (fun i ↦ v i y) n)) := by
  rw [← continuousOn_univ]
  exact ContinuousOn.gramSchmidtNormed_bundle (fun i ↦ (hv i).continuousOn) (fun y _ ↦ hli y) n

namespace Bundle.Trivialization

variable [Fintype ι] (e : Trivialization F (π F E)) [e.IsLinear ℝ]
  (c : Module.Basis ι ℝ F)

/-- The orthonormal basis obtained from a model basis by Gram–Schmidt in a local
trivialization. Its domain is the base set of the trivialization. -/
noncomputable def orthonormalBasis (y : e.baseSet) : OrthonormalBasis ι ℝ (E y) := by
  let d := c.map (e.continuousLinearEquivAt ℝ y y.property).symm.toLinearEquiv
  exact OrthonormalBasis.mk (gramSchmidtNormed_orthonormal d.linearIndependent)
    (by rw [span_gramSchmidtNormed_range, span_gramSchmidt, d.span_eq])

omit [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E] in
/-- The local orthonormal basis is the native normalized Gram–Schmidt family on the
inverse images of the model basis vectors. -/
theorem orthonormalBasis_apply (y : e.baseSet) (i : ι) :
    e.orthonormalBasis c y i =
      gramSchmidtNormed ℝ (fun j ↦ e.symmL ℝ y (c j)) i := by
  simp only [orthonormalBasis, OrthonormalBasis.coe_mk, Module.Basis.coe_map,
    ContinuousLinearEquiv.coe_toLinearEquiv,
    symm_continuousLinearEquivAt_eq, Function.comp_def]

/-- Each vector of the local orthonormal basis is a continuous section over the
trivialization's base set. -/
theorem continuous_orthonormalBasis (i : ι) :
    Continuous (fun y : e.baseSet ↦ TotalSpace.mk' F (y : B) (e.orthonormalBasis c y i)) := by
  have hv (j : ι) : Continuous
      (fun y : e.baseSet ↦ TotalSpace.mk' F (y : B) (e.symmL ℝ y (c j))) := by
    have H := e.continuousOn_symm_prodMk_left (v := c j)
    exact (H.comp_continuous continuous_subtype_val (fun y ↦ y.property)).congr fun y ↦
      (e.mk_symm y.property (c j)).symm.trans
        (congrArg (TotalSpace.mk (y : B)) (e.symmL_apply y.property (c j)).symm)
  have hli (y : e.baseSet) : LinearIndependent ℝ (fun j ↦ e.symmL ℝ y (c j)) := by
    simpa only [Module.Basis.coe_map, ContinuousLinearEquiv.coe_toLinearEquiv,
      symm_continuousLinearEquivAt_eq, Function.comp_def] using
      (c.map (e.continuousLinearEquivAt ℝ y y.property).symm.toLinearEquiv).linearIndependent
  simpa only [orthonormalBasis_apply] using
    (Continuous.gramSchmidtNormed_bundle hv hli i)

end Bundle.Trivialization

namespace Module.Basis

variable [Fintype ι]

/-- A finite-rank continuous Riemannian vector bundle has continuous local orthonormal
bases near each point. The index type and model basis are supplied by the caller. -/
theorem exists_continuous_local_orthonormalBasis (c : Module.Basis ι ℝ F) (x : B) :
    ∃ U : Set B, IsOpen U ∧ x ∈ U ∧
      ∃ d : ∀ y : U, OrthonormalBasis ι ℝ (E y),
        ∀ i, Continuous (fun y : U ↦ TotalSpace.mk' F (y : B) (d y i)) := by
  let e := trivializationAt F E x
  exact ⟨e.baseSet, e.open_baseSet, mem_baseSet_trivializationAt F E x,
    e.orthonormalBasis c, e.continuous_orthonormalBasis c⟩

end Module.Basis

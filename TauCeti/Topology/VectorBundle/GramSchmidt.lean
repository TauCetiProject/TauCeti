/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import TauCeti.Topology.VectorBundle.Riemannian.Hermitian

/-!
# Continuous orthonormal frames

The native Gram–Schmidt process is continuous for continuous families of linearly independent
vectors in a vector bundle over an `RCLike` field `𝕜` whose fibres carry inner products with
continuous norm (`TauCeti.ContinuousFiberNorm`): a continuous Riemannian bundle for `𝕜 = ℝ`, a
continuous Hermitian bundle for `𝕜 = ℂ`. Only an initial segment of the family matters: the
`n`-th vector needs the inputs up to and including `n` to be continuous, and those strictly
before `n` to be linearly independent, or those up to and including `n` for the normalized
process. Applying it to the inverse image of a fixed basis under a bundle trivialization gives
continuous local orthonormal bases. The construction uses Mathlib's
`InnerProductSpace.gramSchmidt` and `gramSchmidtNormed`, including their span and orthonormality
theorems, rather than a separate orthogonalization procedure.

The continuity argument follows the sectionwise Gram–Schmidt construction of Patrick Massot
and Michael Rothgang in Mathlib PR [#26221](https://github.com/leanprover-community/mathlib4/pull/26221),
revision `c487a9a1d25ee47368d6e095f701fc633bb6847a`, adapted to arbitrary continuous base spaces,
families over a varying base map and `RCLike` scalars.
-/

public section

open Bundle Filter Set InnerProductSpace
open scoped Topology

variable {𝕜 : Type*} [RCLike 𝕜] {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace 𝕜 (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E] [TauCeti.ContinuousFiberNorm F E]
  {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]

attribute [local instance] IsWellOrder.toHasWellFounded

variable {X : Type*} [TopologicalSpace X] {b : X → B} {v : ι → ∀ x, E (b x)}
  {s : Set X} {x : X}

/-- Gram–Schmidt applied in each fiber is continuous at every parameter where the input sections
up to and including the index are continuous and the input vectors strictly before the index are
linearly independent. The input vector at the index itself may lie in their span. -/
theorem ContinuousWithinAt.gramSchmidt_bundle (n : ι)
    (hv : ∀ i ≤ n, ContinuousWithinAt (fun y ↦ (v i y : TotalSpace F E)) s x)
    (hli : LinearIndepOn 𝕜 (fun i ↦ v i x) (Set.Iio n)) :
    ContinuousWithinAt
      (fun y ↦ TotalSpace.mk' F (b y) (gramSchmidt 𝕜 (fun i ↦ v i y) n)) s x := by
  classical
  induction n using WellFoundedLT.induction with
  | ind n ih =>
    let e := trivializationAt F E (b x)
    obtain ⟨hb, hc⟩ := (FiberBundle.continuousWithinAt_totalSpace F _).1 (hv n le_rfl)
    have hmem : ∀ᶠ y in 𝓝[s] x, b y ∈ e.baseSet :=
      hb (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E (b x)))
    have hgs (i : ι) (hi : i < n) :=
      ih i hi (fun k hk ↦ hv k (hk.trans hi.le)) (hli.mono (Set.Iio_subset_Iio hi.le))
    have hg (i : ι) (hi : i < n) :=
      ((FiberBundle.continuousWithinAt_totalSpace F _).1 (hgs i hi)).2
    have hnorm (i : ι) (hi : i < n) :
        ContinuousWithinAt (fun y ↦ ((‖gramSchmidt 𝕜 (fun j ↦ v j y) i‖ : ℝ) : 𝕜)) s x :=
      RCLike.continuous_ofReal.continuousAt.comp_continuousWithinAt
        (hgs i hi).norm_bundle_of_continuousFiberNorm
    have hne (i : ι) (hi : i < n) : gramSchmidt 𝕜 (fun j ↦ v j x) i ≠ 0 :=
      gramSchmidt_ne_zero_coe i (hli.mono (Set.Iic_subset_Iio.2 hi)).linearIndependent
    have hcont := hc.sub <| tendsto_finsetSum (Finset.Iio n) fun i hi ↦
      let hi' := Finset.mem_Iio.mp hi
      (((hgs i hi').inner_bundle_of_continuousFiberNorm (hv n le_rfl)).div ((hnorm i hi').pow 2)
        (pow_ne_zero 2 (RCLike.ofReal_ne_zero.2
          (norm_ne_zero_iff.mpr (hne i hi'))))).smul (hg i hi')
    have hformula (y : X) (hy : b y ∈ e.baseSet) :
        (e ⟨b y, gramSchmidt 𝕜 (fun i ↦ v i y) n⟩).2 =
          (e ⟨b y, v n y⟩).2 - ∑ i ∈ Finset.Iio n,
            (@Inner.inner 𝕜 _ _ (gramSchmidt 𝕜 (fun j ↦ v j y) i) (v n y) /
              ((‖gramSchmidt 𝕜 (fun j ↦ v j y) i‖ : ℝ) : 𝕜) ^ 2) •
                (e ⟨b y, gramSchmidt 𝕜 (fun j ↦ v j y) i⟩).2 := by
      simp only [← e.continuousLinearMapAt_apply_of_mem (R := 𝕜) hy,
        ← map_smul, ← map_sum, ← map_sub]
      exact congrArg (e.continuousLinearMapAt 𝕜 (b y))
        (eq_sub_iff_add_eq.mpr (gramSchmidt_def'' 𝕜 (fun i ↦ v i y) n).symm)
    rw [FiberBundle.continuousWithinAt_totalSpace]
    exact ⟨hb, hcont.congr_of_eventuallyEq (hmem.mono hformula)
      (hformula x (mem_baseSet_trivializationAt F E (b x)))⟩

/-- Normalized Gram–Schmidt applied in each fiber is continuous at every parameter where the input
sections up to and including the index are continuous and the input vectors up to and including
the index are linearly independent. -/
theorem ContinuousWithinAt.gramSchmidtNormed_bundle (n : ι)
    (hv : ∀ i ≤ n, ContinuousWithinAt (fun y ↦ (v i y : TotalSpace F E)) s x)
    (hli : LinearIndepOn 𝕜 (fun i ↦ v i x) (Set.Iic n)) :
    ContinuousWithinAt
      (fun y ↦ TotalSpace.mk' F (b y) (gramSchmidtNormed 𝕜 (fun i ↦ v i y) n)) s x := by
  have hg := ContinuousWithinAt.gramSchmidt_bundle n hv (hli.mono Set.Iio_subset_Iic_self)
  have hn : ContinuousWithinAt (fun y ↦ ((‖gramSchmidt 𝕜 (fun i ↦ v i y) n‖ : ℝ) : 𝕜)) s x :=
    RCLike.continuous_ofReal.continuousAt.comp_continuousWithinAt
      hg.norm_bundle_of_continuousFiberNorm
  let e := trivializationAt F E (b x)
  obtain ⟨hb, hc⟩ := (FiberBundle.continuousWithinAt_totalSpace F _).1 hg
  have hmem : ∀ᶠ y in 𝓝[s] x, b y ∈ e.baseSet :=
    hb (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E (b x)))
  have hformula (y : X) (hy : b y ∈ e.baseSet) :
      (e ⟨b y, gramSchmidtNormed 𝕜 (fun i ↦ v i y) n⟩).2 =
        ((‖gramSchmidt 𝕜 (fun i ↦ v i y) n‖ : ℝ) : 𝕜)⁻¹ •
          (e ⟨b y, gramSchmidt 𝕜 (fun i ↦ v i y) n⟩).2 := by
    simp only [gramSchmidtNormed, ← e.continuousLinearMapAt_apply_of_mem (R := 𝕜) hy, map_smul]
  have H := (hn.inv₀ (RCLike.ofReal_ne_zero.2
    (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero_coe n hli.linearIndependent)))).smul hc
  rw [FiberBundle.continuousWithinAt_totalSpace]
  exact ⟨hb, H.congr_of_eventuallyEq (hmem.mono hformula)
    (hformula x (mem_baseSet_trivializationAt F E (b x)))⟩

/-- Normalized Gram–Schmidt applied in each fiber is continuous at every parameter where the input
sections up to and including the index are continuous and the input vectors up to and including
the index are linearly independent. -/
theorem ContinuousAt.gramSchmidtNormed_bundle (n : ι)
    (hv : ∀ i ≤ n, ContinuousAt (fun y ↦ (v i y : TotalSpace F E)) x)
    (hli : LinearIndepOn 𝕜 (fun i ↦ v i x) (Set.Iic n)) :
    ContinuousAt
      (fun y ↦ TotalSpace.mk' F (b y) (gramSchmidtNormed 𝕜 (fun i ↦ v i y) n)) x := by
  rw [← continuousWithinAt_univ]
  exact ContinuousWithinAt.gramSchmidtNormed_bundle n
    (fun i hi ↦ (hv i hi).continuousWithinAt) hli

/-- Normalized Gram–Schmidt applied in each fiber is continuous on a set on which the input
sections up to and including the index are continuous and, at each point, the input vectors up to
and including the index are linearly independent. -/
theorem ContinuousOn.gramSchmidtNormed_bundle (n : ι)
    (hv : ∀ i ≤ n, ContinuousOn (fun y ↦ (v i y : TotalSpace F E)) s)
    (hli : ∀ y ∈ s, LinearIndepOn 𝕜 (fun i ↦ v i y) (Set.Iic n)) :
    ContinuousOn (fun y ↦ TotalSpace.mk' F (b y) (gramSchmidtNormed 𝕜 (fun i ↦ v i y) n)) s :=
  fun y hy ↦ ContinuousWithinAt.gramSchmidtNormed_bundle n (fun i hi ↦ hv i hi y hy) (hli y hy)

/-- Normalized Gram–Schmidt applied in each fiber is continuous when the input sections up to and
including the index are continuous and the input vectors up to and including the index are
linearly independent at every parameter. -/
theorem Continuous.gramSchmidtNormed_bundle (n : ι)
    (hv : ∀ i ≤ n, Continuous (fun y ↦ (v i y : TotalSpace F E)))
    (hli : ∀ y, LinearIndepOn 𝕜 (fun i ↦ v i y) (Set.Iic n)) :
    Continuous (fun y ↦ TotalSpace.mk' F (b y) (gramSchmidtNormed 𝕜 (fun i ↦ v i y) n)) := by
  rw [← continuousOn_univ]
  exact ContinuousOn.gramSchmidtNormed_bundle n (fun i hi ↦ (hv i hi).continuousOn)
    (fun y _ ↦ hli y)

namespace Bundle.Trivialization

variable [Fintype ι] (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
  (c : Module.Basis ι 𝕜 F)

/-- The orthonormal basis obtained from a model basis by Gram–Schmidt in a local
trivialization. Its domain is the base set of the trivialization. -/
noncomputable def orthonormalBasis (y : e.baseSet) : OrthonormalBasis ι 𝕜 (E y) := by
  let d := c.map (e.continuousLinearEquivAt 𝕜 y y.property).symm.toLinearEquiv
  exact OrthonormalBasis.mk (gramSchmidtNormed_orthonormal d.linearIndependent)
    (by rw [span_gramSchmidtNormed_range, span_gramSchmidt, d.span_eq])

omit [VectorBundle 𝕜 F E] [TauCeti.ContinuousFiberNorm F E] in
/-- The local orthonormal basis is the native normalized Gram–Schmidt family on the
inverse images of the model basis vectors. -/
theorem orthonormalBasis_apply (y : e.baseSet) (i : ι) :
    e.orthonormalBasis c y i =
      gramSchmidtNormed 𝕜 (fun j ↦ e.symmL 𝕜 y (c j)) i := by
  simp only [orthonormalBasis, OrthonormalBasis.coe_mk, Module.Basis.coe_map,
    ContinuousLinearEquiv.coe_toLinearEquiv,
    symm_continuousLinearEquivAt_eq, Function.comp_def]

/-- Each vector of the local orthonormal basis is a continuous section over the
trivialization's base set. -/
theorem continuous_orthonormalBasis (i : ι) :
    Continuous (fun y : e.baseSet ↦ TotalSpace.mk' F (y : B) (e.orthonormalBasis c y i)) := by
  have hv (j : ι) : Continuous
      (fun y : e.baseSet ↦ TotalSpace.mk' F (y : B) (e.symmL 𝕜 y (c j))) := by
    have H := e.continuousOn_symm_prodMk_left (v := c j)
    exact (H.comp_continuous continuous_subtype_val (fun y ↦ y.property)).congr fun y ↦
      (e.mk_symm y.property (c j)).symm.trans
        (congrArg (TotalSpace.mk (y : B)) (e.symmL_apply y.property (c j)).symm)
  have hli (y : e.baseSet) : LinearIndependent 𝕜 (fun j ↦ e.symmL 𝕜 y (c j)) := by
    simpa only [Module.Basis.coe_map, ContinuousLinearEquiv.coe_toLinearEquiv,
      symm_continuousLinearEquivAt_eq, Function.comp_def] using
      (c.map (e.continuousLinearEquivAt 𝕜 y y.property).symm.toLinearEquiv).linearIndependent
  simpa only [orthonormalBasis_apply] using
    (Continuous.gramSchmidtNormed_bundle i (fun j _ ↦ hv j) fun y ↦ (hli y).linearIndepOn _)

end Bundle.Trivialization

namespace Module.Basis

variable [Fintype ι]

omit [LinearOrder ι] [LocallyFiniteOrderBot ι] in
/-- A finite-rank vector bundle with continuous fibre metric has continuous local orthonormal
bases near each point. The index type and model basis are supplied by the caller. -/
theorem exists_continuous_local_orthonormalBasis (c : Module.Basis ι 𝕜 F) (x : B) :
    ∃ U : Set B, IsOpen U ∧ x ∈ U ∧
      ∃ d : ∀ y : U, OrthonormalBasis ι 𝕜 (E y),
        ∀ i, Continuous (fun y : U ↦ TotalSpace.mk' F (y : B) (d y i)) := by
  let : LinearOrder ι :=
    LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  classical
  let : LocallyFiniteOrderBot ι := LocallyFiniteOrderBot.ofIic ι
    (fun i ↦ Finset.univ.filter (· ≤ i)) (fun i j ↦ by simp)
  let e := trivializationAt F E x
  exact ⟨e.baseSet, e.open_baseSet, mem_baseSet_trivializationAt F E x,
    e.orthonormalBasis c, e.continuous_orthonormalBasis c⟩

end Module.Basis

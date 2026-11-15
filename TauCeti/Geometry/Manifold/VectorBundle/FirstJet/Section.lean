/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.FirstJet.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.RingTheory.Derivation.DifferentialOperator

/-!
# First-jet extension as a differential operator

The first-jet extension sends a smooth section of `V` to a smooth section of `J¹V`.
It is linear over the ground field, but generally not over smooth functions: its Leibniz rule is

`j¹(f s)(x) = f(x) • j¹s(x) + ofDeriv ((df)(x).smulRight (s(x)))`.

Consequently its commutator with multiplication by `f` is a smooth-function-linear map,
and first-jet extension is a differential operator of order at most one in the iterated
commutator filtration. The formula identifies the derivative contribution intrinsically
in the kernel of the first-jet projection, without choosing a connection. A nonzero value
of `df ⊗ s` witnesses that the operator does not have order zero.

The pointwise rules require only differentiability at the point and `C¹` bundle charts.
Neither finite rank nor finite dimension of the base is needed.

## References

* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*,
  §§12.16–12.17.
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace TauCeti.FirstJetBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

section Pointwise

variable [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I]

/-- First jets are additive on differentiable sections. -/
theorem jet_add {s t : ∀ x, V x} {x : M}
    (hs : MDiffAt (T% s) x) (ht : MDiffAt (T% t) x) :
    jet I F (s + t) x = jet I F s x + jet I F t x := by
  have huniq : UniqueDiffWithinAt 𝕜 (range I) (extChartAt I x x) :=
    I.uniqueDiffOn _ (extChartAt_target_subset_range x (mem_extChartAt_target x))
  apply Prod.ext
  · -- Jet fibres inherit the product operations through `VectorBundleCore.Fiber`.
    erw [Prod.fst_add]
    simpa only [jet_fst, Pi.add_apply] using
      (trivializationAt F V x).linear 𝕜 (mem_baseSet_trivializationAt F V x) |>.map_add (s x) (t x)
  · rw [jet_snd, (localRep_eventuallyEq_add I F s t x).fderivWithin_eq_of_mem
        (extChartAt_target_subset_range x (mem_extChartAt_target x))]
    -- Read the inherited product addition through the fibre type synonym.
    erw [Prod.snd_add]
    simp only [jet_snd]
    rw [fderivWithin_add huniq
      (differentiableWithinAt_localRep I F hs (mem_baseSet_self F V x))
      (differentiableWithinAt_localRep I F ht (mem_baseSet_self F V x))]

/-- First jets commute with constant scalar multiplication, even for nondifferentiable sections. -/
theorem jet_const_smul (c : 𝕜) (s : ∀ x, V x) (x : M) :
    jet I F (c • s) x = c • jet I F s x := by
  apply Prod.ext
  · -- Jet fibres inherit scalar multiplication from the product model fibre.
    erw [Prod.smul_fst]
    simpa only [jet_fst, Pi.smul_apply] using
      (trivializationAt F V x).linear 𝕜 (mem_baseSet_trivializationAt F V x) |>.map_smul c (s x)
  · have h : localRep I F (c • s) x =ᶠ[𝓝[range I] extChartAt I x x]
        c • localRep I F s x := by
      simpa only [Pi.smul_def, Pi.smul_def', Function.comp_def] using
        localRep_eventuallyEq_smul (I := I) (F := F) (fun _ ↦ c) s x
    rw [jet_snd, h.fderivWithin_eq_of_mem
      (extChartAt_target_subset_range x (mem_extChartAt_target x))]
    -- Read the inherited product action through the fibre type synonym.
    erw [Prod.smul_snd]
    rw [jet_snd]
    exact fderivWithin_const_smul_field c
      (I.uniqueDiffOn _ (extChartAt_target_subset_range x (mem_extChartAt_target x)))

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]

/-- The first-jet Leibniz rule; the derivative term lies in the kernel of the value projection. -/
theorem jet_smul {f : M → 𝕜} {s : ∀ x, V x} {x : M}
    (hf : MDiffAt f x) (hs : MDiffAt (T% s) x) :
    jet I F (f • s) x = f x • jet I F s x +
      ofDeriv I F x ((mvfderiv I f x).smulRight (s x)) := by
  have hx := mem_extChartAt_source (I := I) x
  have hrep : writtenInExtChartAt I 𝓘(𝕜) x f = f ∘ (extChartAt I x).symm := by
    simp [writtenInExtChartAt]
  have hf' : DifferentiableWithinAt 𝕜 (f ∘ (extChartAt I x).symm)
      (range I) (extChartAt I x x) := by
    rw [← hrep]
    exact hf.differentiableWithinAt_writtenInExtChartAt
  have hdf : fderivWithin 𝕜 (f ∘ (extChartAt I x).symm) (range I) (extChartAt I x x) =
      mvfderiv I f x := by
    rw [hf.mvfderiv, hrep]
  have huniq : UniqueDiffWithinAt 𝕜 (range I) (extChartAt I x x) :=
    I.uniqueDiffOn _ (extChartAt_target_subset_range x (mem_extChartAt_target x))
  apply Prod.ext
  · -- Use the product operations underlying `VectorBundleCore.Fiber`.
    erw [Prod.fst_add, Prod.smul_fst]
    rw [jet_fst, jet_fst, ofDeriv_apply, add_zero]
    exact (trivializationAt F V x).linear 𝕜 (mem_baseSet_trivializationAt F V x)
      |>.map_smul (f x) (s x)
  · rw [jet_snd, (localRep_eventuallyEq_smul I F f s x).fderivWithin_eq_of_mem
        (extChartAt_target_subset_range x (mem_extChartAt_target x))]
    -- Use the product operations underlying `VectorBundleCore.Fiber`.
    erw [Prod.snd_add, Prod.smul_snd]
    rw [jet_snd, fderivWithin_smul huniq hf'
        (differentiableWithinAt_localRep I F hs (mem_baseSet_self F V x)), hdf]
    rw [Function.comp_apply, (extChartAt I x).left_inv hx,
      localRep_extChartAt I F s (mem_chart_source H x), ofDeriv_apply]
    congr 1
    ext v
    -- The domain is the tangent-space type synonym; evaluating both linear maps
    -- exposes the scalar multiplication in the fibre.
    change mvfderiv I f x v • (trivializationAt F V x ⟨x, s x⟩).2 =
      (trivializationAt F V x).continuousLinearMapAt 𝕜 x (mvfderiv I f x v • s x)
    rw [map_smul, Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) _
      (mem_baseSet_trivializationAt F V x)]

end Pointwise

section Smooth

variable [IsManifold I ∞ M] [ContMDiffVectorBundle ∞ F V I]

variable (I F V) in
/-- The ground-field-linear first-jet extension of smooth sections. -/
def jetExtension : Cₛ^∞⟮I; F, V⟯ →ₗ[𝕜]
    Cₛ^∞⟮I; F × (E →L[𝕜] F), FirstJetBundle I F V⟯ where
  toFun s := ⟨jet I F s, by
    have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
    have : ContMDiffVectorBundle (∞ + 1) F V I := by
      simpa using (inferInstance : ContMDiffVectorBundle ∞ F V I)
    exact contMDiff_jet (n := ∞) I F (by simpa using s.contMDiff)⟩
  map_add' s t := ContMDiffSection.ext fun x ↦
    jet_add (s.contMDiff.mdifferentiable (by simp) x) (t.contMDiff.mdifferentiable (by simp) x)
  map_smul' c s := ContMDiffSection.ext fun x ↦ jet_const_smul c s x

/-- Jet extension evaluates to the pointwise first jet. -/
@[simp]
theorem jetExtension_apply (s : Cₛ^∞⟮I; F, V⟯) (x : M) :
    jetExtension I F V s x = jet I F s x := (rfl)

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]

/-- The commutator of jet extension and multiplication is insertion of `df ⊗ s`. -/
theorem smulCommutator_jetExtension_apply (f : C^∞⟮I, M; 𝕜⟯)
    (s : Cₛ^∞⟮I; F, V⟯) (x : M) :
    smulCommutator 𝕜 f (jetExtension I F V) s x =
      ofDeriv I F x ((mvfderiv I f x).smulRight (s x)) := by
  rw [smulCommutator_apply_apply]
  simp only [ContMDiffSection.coe_sub, Pi.sub_apply, ContMDiffSection.smul_apply,
    jetExtension_apply]
  have hfs : ⇑(f • s) = (f : M → 𝕜) • (s : ∀ x, V x) :=
    funext fun y ↦ ContMDiffSection.smul_apply f s y
  rw [hfs, jet_smul (f.contMDiff.mdifferentiable (by simp) x)
    (s.contMDiff.mdifferentiable (by simp) x), add_sub_cancel_left]

/-- The commutator of first-jet extension with multiplication is smooth-function-linear. -/
theorem smulCommutator_jetExtension_smul (f g : C^∞⟮I, M; 𝕜⟯)
    (s : Cₛ^∞⟮I; F, V⟯) :
    smulCommutator 𝕜 f (jetExtension I F V) (g • s) =
      g • smulCommutator 𝕜 f (jetExtension I F V) s := by
  ext x
  simp only [ContMDiffSection.smul_apply, smulCommutator_jetExtension_apply]
  rw [← map_smul]
  congr 1
  ext v
  exact smul_comm _ _ _

/-- First-jet extension is a differential operator of order at most one. -/
theorem jetExtension_mem_differentialOperators_one :
    jetExtension I F V ∈ differentialOperators 𝕜 C^∞⟮I, M; 𝕜⟯
      Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F × (E →L[𝕜] F), FirstJetBundle I F V⟯ 1 := by
  rw [mem_differentialOperators_succ_iff]
  intro f
  rw [mem_differentialOperators_zero_iff]
  exact smulCommutator_jetExtension_smul f

/-- A nonzero derivative tensor witnesses that first-jet extension does not have order zero. -/
theorem jetExtension_notMem_differentialOperators_zero (f : C^∞⟮I, M; 𝕜⟯)
    (s : Cₛ^∞⟮I; F, V⟯) (x : M) (h : (mvfderiv I f x).smulRight (s x) ≠ 0) :
    jetExtension I F V ∉ differentialOperators 𝕜 C^∞⟮I, M; 𝕜⟯
      Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F × (E →L[𝕜] F), FirstJetBundle I F V⟯ 0 := by
  intro hj
  have hz := congrArg (fun D ↦ D s x)
    (smulCommutator_eq_zero_of_mem_differentialOperators_zero hj f)
  rw [smulCommutator_jetExtension_apply] at hz
  exact h ((ofDeriv_injective I F x) (hz.trans (map_zero (ofDeriv I F x)).symm))

end Smooth

end TauCeti.FirstJetBundle

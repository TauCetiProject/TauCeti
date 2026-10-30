/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Continuous
public import Mathlib.Topology.Algebra.Module.Multilinear.Topology

/-!
# Bounded-convergence topology of continuous cyclic cochain operators

The cyclic, Hochschild and mixed-complex operators on jointly continuous multilinear
cochains are continuous for uniform convergence on bounded sets of tuples. We use the
native topology on `ContinuousMultilinearMap` from Mathlib. By
`Bornology.isVonNBounded_pi_iff`, bounded sets of tuples are contained in products of
bounded coordinate sets, so this is also uniform convergence on products of bounded sets.

In particular the cyclic Hochschild differential is continuous on the cyclic subspaces
with their induced topologies. These facts apply to locally convex algebras without
requiring local convexity, completeness, separation, a norm on the algebra, or closed
differential ranges. Multiplication must be jointly continuous. The operators are
defined on the naive cochains of a nonunital algebra; no comparison with the relative
complex of its forced unitization is asserted here.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §§1.1, 2.1.

The topology is Mathlib's native topology on continuous multilinear maps. Operator
continuity reuses `UniformOnFun.precomp_uniformContinuous`, and the bounded-image
argument reuses `Bornology.IsVonNBounded.image_multilinear'`.
-/

public section

noncomputable section

open Bornology Function Set Topology

namespace TauCeti

section Cyclic

variable (𝕜 A M : Type*) [NormedField 𝕜] [AddCommGroup A] [Module 𝕜 A]
  [TopologicalSpace A] [AddCommGroup M] [Module 𝕜 M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul 𝕜 M]

/-- Signed cyclic rotation is continuous for bounded convergence of cochains. -/
@[fun_prop]
theorem continuous_continuousCyclicOperator (n : ℕ) :
    Continuous (continuousCyclicOperator 𝕜 A M n) := by
  have h := (ContinuousMultilinearMap.domDomCongrL (𝕜 := 𝕜) (F := A) (G := M)
    (finRotate (n + 1)).symm).continuous.zsmul ((-1 : ℤ) ^ n)
  convert h using 1
  ext φ a
  rw [continuousCyclicOperator_apply, cyclicOperator_apply]
  rfl

/-- The finite cyclic norm is continuous for bounded convergence of cochains. -/
@[fun_prop]
theorem continuous_continuousCyclicNorm (n : ℕ) :
    Continuous (continuousCyclicNorm 𝕜 A M n) := by
  have h : Continuous (fun φ : ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) M ↦
      ∑ k ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ (n * k) • φ.domDomCongr (finRotate (n + 1) ^ k).symm) :=
    continuous_finsetSum _ fun k _ ↦
      (ContinuousMultilinearMap.domDomCongrL (𝕜 := 𝕜) (F := A) (G := M)
        (finRotate (n + 1) ^ k).symm).continuous.zsmul _
  convert h using 1
  ext φ a
  simpa only [continuousCyclicNorm_apply, Finset.sum_apply, sum_apply, smul_apply,
    ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.coe_coe,
    Function.comp_def] using cyclicNorm_apply φ.toMultilinearMap a

end Cyclic

section Multiplication

variable (𝕜 A : Type*) [NormedField 𝕜] [NonUnitalNonAssocRing A] [Module 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [TopologicalSpace A] [ContinuousMul A]

/-- A Hochschild face sends bounded sets of tuples to bounded sets of tuples. -/
theorem isVonNBounded_image_hochschildFace {n : ℕ} {s : Set (Fin (n + 2) → A)}
    (hs : IsVonNBounded 𝕜 s) (i : Fin (n + 2)) :
    IsVonNBounded 𝕜 (hochschildFace i '' s) := by
  -- The zeroth coface of the unary identity is the native binary multiplication map.
  let id₁ := ContinuousMultilinearMap.ofSubsingleton 𝕜 A A (0 : Fin 1)
    (ContinuousLinearMap.id 𝕜 A)
  let mul : ContinuousMultilinearMap 𝕜 (fun _ : Fin 2 ↦ A) A :=
    ⟨hochschildCoface 𝕜 A A 0 id₁.toMultilinearMap, id₁.continuous_hochschildCoface 0⟩
  have hcoord := isVonNBounded_pi_iff.1 hs
  have hmul (j k : Fin (n + 2)) : IsVonNBounded 𝕜 ((fun a : Fin (n + 2) → A ↦ a j * a k) '' s) := by
    have hpair : IsVonNBounded 𝕜 ((fun a : Fin (n + 2) → A ↦ ![a j, a k]) '' s) := by
      rw [isVonNBounded_pi_iff]
      intro l
      fin_cases l
      · simpa [image_image] using hcoord j
      · simpa [image_image] using hcoord k
    have hmul_apply (a : Fin 2 → A) : mul a = a 0 * a 1 := by
      -- Reduce the local record projection before using the opaque coface's public equation.
      change hochschildCoface 𝕜 A A 0 id₁.toMultilinearMap a = _
      simp only [hochschildCoface_apply, ContinuousMultilinearMap.coe_coe]
      rw [← Fin.castSucc_zero, hochschildFace_castSucc]
      simp [id₁, Fin.contractNth]
    simpa [image_image, hmul_apply] using hpair.image_multilinear' mul
  rw [isVonNBounded_pi_iff]
  intro j
  cases i using Fin.lastCases with
  | last =>
    simpa [image_image, Function.comp_def, hochschildFace_last, Fin.cons] using
      (Fin.cases (hmul (Fin.last (n + 1)) 0)
        (fun k ↦ hcoord k.castSucc.succ) j)
  | cast i =>
    simp only [image_image, hochschildFace_castSucc, Fin.contractNth]
    split_ifs
    · exact hcoord j.castSucc
    · exact hmul j.castSucc j.succ
    · exact hcoord j.succ

variable (M : Type*) [AddCommGroup M] [Module 𝕜 M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul 𝕜 M]

omit [ContinuousConstSMul 𝕜 M] in
private theorem continuous_coface {n : ℕ} (i : Fin (n + 2)) :
    Continuous (fun φ : ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) M ↦
      (⟨hochschildCoface 𝕜 A M i φ.toMultilinearMap,
        φ.continuous_hochschildCoface i⟩ :
          ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 2) ↦ A) M)) := by
  let := IsTopologicalAddGroup.rightUniformSpace M
  have : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
  apply ContinuousMultilinearMap.isEmbedding_toUniformOnFun.continuous_iff.2
  have h : UniformContinuous (fun φ : ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) M ↦
      UniformOnFun.ofFun {s | IsVonNBounded 𝕜 s} (fun a ↦ φ (hochschildFace i a))) :=
    (UniformOnFun.precomp_uniformContinuous
    (𝔖 := {s | IsVonNBounded 𝕜 s}) (𝔗 := {s | IsVonNBounded 𝕜 s})
    (f := hochschildFace i) (fun _ hs ↦ isVonNBounded_image_hochschildFace 𝕜 A hs i)).comp
    ContinuousMultilinearMap.isUniformEmbedding_toUniformOnFun.uniformContinuous
  convert h.continuous using 1
  ext φ
  apply (UniformOnFun.toFun _).injective
  ext a
  exact hochschildCoface_apply 𝕜 A M i φ.toMultilinearMap a

/-- The Hochschild coboundary is continuous for bounded convergence of cochains. -/
@[fun_prop]
theorem continuous_continuousHochschildCoboundary (n : ℕ) :
    Continuous (continuousHochschildCoboundary 𝕜 A M n) := by
  have h := continuous_finsetSum Finset.univ fun (i : Fin (n + 2)) _ ↦
    (continuous_coface 𝕜 A M i).zsmul ((-1 : ℤ) ^ (i : ℕ))
  convert h using 1
  ext φ a
  simp only [continuousHochschildCoboundary_apply, hochschildCoboundary_apply,
    sum_apply]
  congr 1
  ext i
  congr 1
  exact (hochschildCoface_apply 𝕜 A M i φ.toMultilinearMap a).symm

/-- The bar coboundary is continuous for bounded convergence of cochains. -/
@[fun_prop]
theorem continuous_continuousBarCoboundary (n : ℕ) :
    Continuous (continuousBarCoboundary 𝕜 A M n) := by
  have h := continuous_finsetSum Finset.univ fun i : Fin (n + 1) ↦ fun _ ↦
    (continuous_coface 𝕜 A M i.castSucc).zsmul ((-1 : ℤ) ^ (i : ℕ))
  convert h using 1
  ext φ a
  simp only [continuousBarCoboundary_apply, barCoboundary_apply,
    sum_apply, ← hochschildFace_castSucc]
  congr 1
  ext i
  congr 1
  exact (hochschildCoface_apply 𝕜 A M i.castSucc φ.toMultilinearMap a).symm

/-- The cyclic Hochschild differential is continuous on the cyclic cochain subspaces. -/
@[fun_prop]
theorem continuous_continuousCyclicHochschildCoboundary (n : ℕ) :
    Continuous (continuousCyclicHochschildCoboundary 𝕜 A M n) := by
  apply continuous_induced_rng.2
  simpa only [Function.comp_def, coe_continuousCyclicHochschildCoboundary] using
    (continuous_continuousHochschildCoboundary 𝕜 A M n).comp continuous_subtype_val

end Multiplication

section Unit

variable (𝕜 A M : Type*) [NormedField 𝕜] [AddCommGroup A] [Module 𝕜 A]
  [TopologicalSpace A] [ContinuousSMul 𝕜 A] [One A]
  [AddCommGroup M] [Module 𝕜 M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul 𝕜 M]

/-- Insertion of the unit is continuous for bounded convergence of cochains. -/
@[fun_prop]
theorem continuous_continuousBarContraction (n : ℕ) :
    Continuous (continuousBarContraction 𝕜 A M n) := by
  have hcons {s : Set (Fin (n + 1) → A)} (hs : IsVonNBounded 𝕜 s) :
      IsVonNBounded 𝕜 ((fun a : Fin (n + 1) → A ↦
        (Fin.cons (1 : A) a : Fin (n + 2) → A)) '' s) := by
    rw [isVonNBounded_pi_iff]
    intro i
    cases i using Fin.cases with
    | zero =>
      apply (isVonNBounded_singleton (𝕜 := 𝕜) (1 : A)).subset
      rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      simp
    | succ i => simpa [image_image, Function.comp_def] using isVonNBounded_pi_iff.1 hs i
  let := IsTopologicalAddGroup.rightUniformSpace M
  have : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
  apply ContinuousMultilinearMap.isEmbedding_toUniformOnFun.continuous_iff.2
  have h : UniformContinuous (fun φ : ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 2) ↦ A) M ↦
      UniformOnFun.ofFun {s : Set (Fin (n + 1) → A) | IsVonNBounded 𝕜 s}
        (fun a ↦ φ (Fin.cons 1 a))) :=
    (UniformOnFun.precomp_uniformContinuous
      (𝔖 := {s : Set (Fin (n + 2) → A) | IsVonNBounded 𝕜 s})
      (𝔗 := {s : Set (Fin (n + 1) → A) | IsVonNBounded 𝕜 s})
      (f := fun a : Fin (n + 1) → A ↦ (Fin.cons (1 : A) a : Fin (n + 2) → A))
      (fun _ hs ↦ hcons hs)).comp
      ContinuousMultilinearMap.isUniformEmbedding_toUniformOnFun.uniformContinuous
  convert h.continuous using 1
  ext φ
  apply (UniformOnFun.toFun _).injective
  ext a
  simp only [Function.comp_apply, ContinuousMultilinearMap.toUniformOnFun_toFun,
    UniformOnFun.toFun_ofFun, continuousBarContraction_apply, barContraction_apply,
    ContinuousMultilinearMap.coe_coe]

/-- Connes' operator is continuous for bounded convergence of cochains. -/
@[fun_prop]
theorem continuous_continuousConnesB (n : ℕ) :
    Continuous (continuousConnesB 𝕜 A M n) := by
  have h := (continuous_continuousCyclicNorm 𝕜 A M n).comp
    ((continuous_continuousBarContraction 𝕜 A M n).comp
      (continuous_id.sub (continuous_continuousCyclicOperator 𝕜 A M (n + 1))))
  convert h using 1
  ext φ a
  simp only [Function.comp_apply, Pi.sub_apply, id_eq, continuousConnesB_apply, connesB_apply,
    continuousCyclicNorm_apply, toMultilinearMap_continuousBarContraction]
  congr 3
  ext a
  simp only [ContinuousMultilinearMap.coe_coe, sub_apply,
    continuousCyclicOperator_apply]

end Unit

end TauCeti

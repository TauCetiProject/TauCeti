/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Weyl
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.StructureConstant
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Basic

/-!
# Diagram automorphisms on all Chevalley root vectors

The pinned diagram automorphism sends a simple root vector to the renumbered simple root
vector. On other roots a sign is necessary: the chosen Chevalley system need not be equivariant
under diagram symmetries. This file defines `TauCeti.DynkinType.chevalleyDiagramSign` and proves
that `diagramLieEquiv` sends `e_α` to that sign times `e_{σ α}` in the native root enumeration.
The sign is one on positive and negative simple roots, agrees at opposite roots, and satisfies
the composition law for diagram symmetries. The structure-constant equation gives its compatibility
with root brackets.

These equations identify the signs in the action of a pinned graph automorphism on root
subgroups: exponentiating a signed root vector multiplies the additive parameter by the same
sign. No sign-one assertion is made for nonsimple roots.

The construction uses the signed Weyl action of
`TauCeti.DynkinType.weylAut_chevalleySystem`, root-system induction, and the naturality theorem
`LieHom.map_expAd`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 29.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.15.
-/

public section

namespace TauCeti.DynkinType

open LieAlgebra LieAlgebra.IsKilling LieModule

noncomputable section

variable {t : DynkinType} (ht : t.Valid) {σ τ : Equiv.Perm (Fin t.rank)}

private theorem diagramLieEquiv_weylAut_simple (hσ : σ ∈ t.diagramSymmetry)
    (i : Fin t.rank) (z : t.lieAlgebra ht) :
    t.diagramLieEquiv ht hσ
        (weylAut (t.isSl2Triple_chevalleySystem ht (t.simpleIndex ht i))
          (t.isNilpotent_ad_chevalleySystem ht _).exists_pow_apply_eq_zero
          (t.isNilpotent_ad_chevalleySystem ht _).exists_pow_apply_eq_zero z) =
      weylAut (t.isSl2Triple_chevalleySystem ht (t.simpleIndex ht (σ i)))
        (t.isNilpotent_ad_chevalleySystem ht _).exists_pow_apply_eq_zero
        (t.isNilpotent_ad_chevalleySystem ht _).exists_pow_apply_eq_zero
        (t.diagramLieEquiv ht hσ z) := by
  let f := (t.diagramLieEquiv ht hσ).toLieHom
  have he (y : t.lieAlgebra ht) :
      f (expAd (t.chevalleySystem ht (t.simpleIndex ht i))
          (t.isNilpotent_ad_chevalleySystem ht _).exists_pow_apply_eq_zero y) =
        expAd (t.chevalleySystem ht (t.simpleIndex ht (σ i)))
          (t.isNilpotent_ad_chevalleySystem ht _).exists_pow_apply_eq_zero (f y) := by
    have hm : f (t.chevalleySystem ht (t.simpleIndex ht i)) =
        t.chevalleySystem ht (t.simpleIndex ht (σ i)) := by simp [f]
    have H := f.map_expAd
      (t.isNilpotent_ad_chevalleySystem ht _).exists_pow_apply_eq_zero
      (hm ▸ (t.isNilpotent_ad_chevalleySystem ht _).exists_pow_apply_eq_zero) y
    generalize_proofs at H
    simpa only [hm] using H
  have hf (y : t.lieAlgebra ht) :
      f (expAd (-t.chevalleySystem ht
            ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i)
              (t.simpleIndex ht i)))
          (by simpa only [map_neg] using
            (t.isNilpotent_ad_chevalleySystem ht _).neg.exists_pow_apply_eq_zero) y) =
        expAd (-t.chevalleySystem ht
            ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht (σ i))
              (t.simpleIndex ht (σ i))))
          (by simpa only [map_neg] using
            (t.isNilpotent_ad_chevalleySystem ht _).neg.exists_pow_apply_eq_zero) (f y) := by
    have hm : f (-t.chevalleySystem ht
          ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i)
            (t.simpleIndex ht i))) =
        -t.chevalleySystem ht
          ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht (σ i))
            (t.simpleIndex ht (σ i))) := by simp [f]
    have hn : IsNilpotent (ad ℚ (t.lieAlgebra ht)
        (-t.chevalleySystem ht
          ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i)
            (t.simpleIndex ht i)))) := by
      simpa only [map_neg] using (t.isNilpotent_ad_chevalleySystem ht _).neg
    have hfn := f.isNilpotent_ad_of_surjective (t.diagramLieEquiv ht hσ).surjective hn
    have H := f.map_expAd hn.exists_pow_apply_eq_zero hfn.exists_pow_apply_eq_zero y
    generalize_proofs at H
    simpa only [hm] using H
  simpa only [weylAut_apply, f, LieEquiv.coe_toLieHom] using
    (he _).trans (congrArg _ ((hf _).trans (congrArg _ (he z))))

/-- A pinned diagram automorphism carries every root vector to the root vector of the
permuted root, up to an integral unit. -/
private theorem exists_diagramLieEquiv_chevalleySystem (hσ : σ ∈ t.diagramSymmetry)
    (α : Fin t.numRoots) :
    ∃ ε : ℤˣ, t.diagramLieEquiv ht hσ (t.chevalleySystem ht α) =
      (ε : ℤ) • t.chevalleySystem ht (t.diagramRootPerm ht hσ α) := by
  have step (i : Fin t.rank) (β : Fin t.numRoots)
      (hβ : ∃ ε : ℤˣ, t.diagramLieEquiv ht hσ (t.chevalleySystem ht β) =
        (ε : ℤ) • t.chevalleySystem ht (t.diagramRootPerm ht hσ β)) :
      ∃ ε : ℤˣ, t.diagramLieEquiv ht hσ
          (t.chevalleySystem ht
            ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) β)) =
        (ε : ℤ) • t.chevalleySystem ht
          (t.diagramRootPerm ht hσ
            ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) β)) := by
    obtain ⟨ε, hε⟩ := hβ
    have hp := (t.diagramAut ht hσ).toHom.indexEquiv_reflectionPerm (t.simpleIndex ht i) β
    simp only [diagramAut_indexEquiv, diagramRootPerm_simpleIndex] at hp
    have hw := diagramLieEquiv_weylAut_simple ht hσ i (t.chevalleySystem ht β)
    rw [weylAut_chevalleySystem, map_zsmul, hε, map_zsmul, weylAut_chevalleySystem] at hw
    refine ⟨t.chevalleyWeylSign ht (t.simpleIndex ht i) β * ε *
      t.chevalleyWeylSign ht (t.simpleIndex ht (σ i)) (t.diagramRootPerm ht hσ β), ?_⟩
    rw [hp, Units.val_mul, Units.val_mul, mul_smul, mul_smul]
    rw [← hw, smul_smul]
    simp [← Units.val_mul]
  refine (t.rationalBase ht).induction_simple_reflect α
    (p := fun β => ∃ ε : ℤˣ, t.diagramLieEquiv ht hσ (t.chevalleySystem ht β) =
      (ε : ℤ) • t.chevalleySystem ht (t.diagramRootPerm ht hσ β))
    (fun β hβ => ?_) (fun β j hβ hj => ?_)
  · obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support hβ
    exact ⟨1, by simp⟩
  · obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support hj
    simpa only [reflectionPerm_rationalRootSystem] using step i β hβ

/-- The integral sign in the action of a pinned diagram automorphism on a named Chevalley
root vector. Its characteristic equation is `diagramLieEquiv_chevalleySystem`. -/
def chevalleyDiagramSign (hσ : σ ∈ t.diagramSymmetry) (α : Fin t.numRoots) : ℤˣ :=
  open Classical in
  if t.diagramLieEquiv ht hσ (t.chevalleySystem ht α) =
      t.chevalleySystem ht (t.diagramRootPerm ht hσ α) then 1 else -1

/-- The pinned diagram automorphism acts on every root vector by its root permutation and
the sign `chevalleyDiagramSign`. -/
theorem diagramLieEquiv_chevalleySystem (hσ : σ ∈ t.diagramSymmetry) (α : Fin t.numRoots) :
    t.diagramLieEquiv ht hσ (t.chevalleySystem ht α) =
      (t.chevalleyDiagramSign ht hσ α : ℤ) •
        t.chevalleySystem ht (t.diagramRootPerm ht hσ α) := by
  obtain ⟨ε, hε⟩ := exists_diagramLieEquiv_chevalleySystem ht hσ α
  rcases Int.units_eq_one_or ε with h | h
  · simp only [h, Units.val_one, one_smul] at hε
    simp [chevalleyDiagramSign, hε]
  · simp only [h, Units.val_neg, Units.val_one, neg_one_smul] at hε
    rw [chevalleyDiagramSign]
    split_ifs with h'
    · simpa using h'
    · simpa using hε

/-- The sign is uniquely characterized by the image of its nonzero root vector. -/
theorem eq_chevalleyDiagramSign_iff (hσ : σ ∈ t.diagramSymmetry)
    {α : Fin t.numRoots} {ε : ℤˣ} :
    ε = t.chevalleyDiagramSign ht hσ α ↔
      t.diagramLieEquiv ht hσ (t.chevalleySystem ht α) =
        (ε : ℤ) • t.chevalleySystem ht (t.diagramRootPerm ht hσ α) := by
  refine ⟨fun h => h ▸ diagramLieEquiv_chevalleySystem ht hσ α, fun h => ?_⟩
  rw [diagramLieEquiv_chevalleySystem] at h
  simp only [← Int.cast_smul_eq_zsmul ℚ] at h
  apply Units.ext
  exact_mod_cast (smul_left_injective ℚ
    (t.isSl2Triple_chevalleySystem ht _).e_ne_zero h).symm

/-- The pinned diagram action has sign one on every positive simple root. -/
@[simp]
theorem chevalleyDiagramSign_simpleIndex (hσ : σ ∈ t.diagramSymmetry) (i : Fin t.rank) :
    t.chevalleyDiagramSign ht hσ (t.simpleIndex ht i) = 1 := by
  symm
  apply (eq_chevalleyDiagramSign_iff ht hσ).mpr
  simp

/-- A pinned diagram automorphism has the same sign at opposite roots, because it commutes
with the Chevalley involution. -/
@[simp]
theorem chevalleyDiagramSign_reflectionPerm_self (hσ : σ ∈ t.diagramSymmetry)
    (α : Fin t.numRoots) :
    t.chevalleyDiagramSign ht hσ ((t.simplyConnectedRootDatum ht).reflectionPerm α α) =
      t.chevalleyDiagramSign ht hσ α := by
  symm
  apply (eq_chevalleyDiagramSign_iff ht hσ).mpr
  have hp := (t.diagramAut ht hσ).toHom.indexEquiv_reflectionPerm α α
  simp only [diagramAut_indexEquiv] at hp
  have H := congrArg (t.chevalleyInvolution ht)
    (diagramLieEquiv_chevalleySystem ht hσ α)
  rw [← diagramLieEquiv_chevalleyInvolution, chevalleyInvolution_chevalleySystem,
    map_neg, map_zsmul, chevalleyInvolution_chevalleySystem, smul_neg, neg_inj] at H
  simpa only [hp] using H

/-- The identity diagram symmetry has sign one at every root. -/
@[simp]
theorem chevalleyDiagramSign_one (α : Fin t.numRoots) :
    t.chevalleyDiagramSign ht t.diagramSymmetry.one_mem α = 1 := by
  symm
  apply (eq_chevalleyDiagramSign_iff ht _).mpr
  simp

/-- Diagram signs satisfy the cocycle law: the right-hand symmetry acts first on the root. -/
theorem chevalleyDiagramSign_mul (hσ : σ ∈ t.diagramSymmetry) (hτ : τ ∈ t.diagramSymmetry)
    (α : Fin t.numRoots) :
    t.chevalleyDiagramSign ht (t.diagramSymmetry.mul_mem hσ hτ) α =
      t.chevalleyDiagramSign ht hτ α *
        t.chevalleyDiagramSign ht hσ (t.diagramRootPerm ht hτ α) := by
  symm
  apply (eq_chevalleyDiagramSign_iff ht (t.diagramSymmetry.mul_mem hσ hτ)).mpr
  rw [diagramLieEquiv_mul ht hσ hτ, LieEquiv.trans_apply,
    diagramLieEquiv_chevalleySystem ht hτ, map_zsmul,
    diagramLieEquiv_chevalleySystem ht hσ]
  rw [diagramRootPerm_mul ht hσ hτ]
  simp [mul_smul]

/-- Compatibility of the diagram signs with the integral structure constants at a root sum.
Thus the signs can be propagated from simple roots using the bracket equations. -/
theorem chevalleyDiagramSign_mul_structureConstant (hσ : σ ∈ t.diagramSymmetry)
    {α β γ : Fin t.numRoots}
    (h : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β) :
    (t.chevalleyDiagramSign ht hσ α : ℤ) * (t.chevalleyDiagramSign ht hσ β : ℤ) *
        t.structureConstant ht (t.diagramRootPerm ht hσ α) (t.diagramRootPerm ht hσ β) =
      t.structureConstant ht α β * (t.chevalleyDiagramSign ht hσ γ : ℤ) := by
  have hp : (t.simplyConnectedRootDatum ht).root (t.diagramRootPerm ht hσ γ) =
      (t.simplyConnectedRootDatum ht).root (t.diagramRootPerm ht hσ α) +
        (t.simplyConnectedRootDatum ht).root (t.diagramRootPerm ht hσ β) := by
    ext j
    simpa only [root_diagramRootPerm, Pi.add_apply] using congrFun h (σ.symm j)
  have H := congrArg (t.diagramLieEquiv ht hσ)
    (lie_chevalleySystem_eq_structureConstant_zsmul h)
  rw [LieEquiv.map_lie, diagramLieEquiv_chevalleySystem, diagramLieEquiv_chevalleySystem,
    zsmul_lie, lie_zsmul, lie_chevalleySystem_eq_structureConstant_zsmul hp,
    map_zsmul, diagramLieEquiv_chevalleySystem] at H
  simp only [smul_smul, ← Int.cast_smul_eq_zsmul ℚ] at H
  have H' := smul_left_injective ℚ (t.isSl2Triple_chevalleySystem ht _).e_ne_zero H
  norm_cast at H'
  simpa only [mul_assoc] using H'

end

end TauCeti.DynkinType

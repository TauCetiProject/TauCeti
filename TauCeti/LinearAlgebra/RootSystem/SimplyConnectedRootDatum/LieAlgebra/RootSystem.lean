/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Isomorphism
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Chevalley

import TauCeti.LinearAlgebra.RootSystem.HomInvariance

/-!
# The root system of the pinned rational Lie algebra

This file identifies the rational root system attached to a valid Dynkin type with the Killing
root system of its pinned rational Geck Lie algebra. The identification is pinned: on simple roots
it follows the common Bourbaki numbering supplied by `Fin t.rank`. Unlike
`RootPairing.GeckConstruction.equivRootSystem`, which assumes an algebraically closed coefficient
field, this construction works over `ℚ` by using the rational splitting and distinguished basis
already established for the pinned Lie algebra.

Through this identification the roots of the Lie algebra, its nonzero weights, are numbered by the
root indices of `TauCeti.DynkinType.simplyConnectedRootDatum`, so that root vectors, structure
constants and root subgroups can all be indexed by the one enumeration of the roots fixed there.
The general theory of normalized root-vector systems indexes its families by all weights, the zero
weight included, so the file also translates a family indexed by the root numbers into that form.

## Main declarations

* `TauCeti.DynkinType.rationalRootSystemEquiv`: the pinned equivalence from the rational root
  system to the Killing root system of the rational Lie algebra.
* `TauCeti.DynkinType.rootEquiv`: the resulting enumeration of the roots of the rational Lie
  algebra by the root indices `Fin t.numRoots` of the pinned root datum.
* `TauCeti.DynkinType.rootEquiv_apply_cartanBasis` and `TauCeti.DynkinType.coe_rootEquiv_eq_iff`:
  the root numbered `α` takes the values of root `α` of the pinned datum on the Cartan generators,
  and is characterized by them.
* `TauCeti.DynkinType.rootEquiv_simpleIndex` and
  `TauCeti.DynkinType.rootEquiv_reflectionPerm_self`: the enumeration matches the numbered simple
  roots and commutes with negation.
* `TauCeti.DynkinType.extendRootFamily`: a family of vectors indexed by the root numbers, extended
  by `0` to the weight-indexed family that `TauCeti.IsSl2System` and `TauCeti.IsChevalleySystem`
  take.
* `TauCeti.DynkinType.isSl2System_extendRootFamily_iff` and
  `TauCeti.DynkinType.isChevalleySystem_extendRootFamily_iff`: the two conditions read in the root
  numbering.
-/

public section

namespace TauCeti.DynkinType

open LieAlgebra LieAlgebra.IsKilling LieModule

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-- The support equivalence between the pinned rational base and the base of the distinguished
Lie-algebra basis, following the common Bourbaki numbering. -/
private def rationalLieBaseSupportEquiv :
    (t.rationalBase ht).support ≃ (t.lieBasis ht).base.support :=
  (t.simpleSupportEquiv ht).symm.trans (t.lieBasis ht).baseSupportEquiv

private theorem cartanMatrix_rationalLieBaseSupportEquiv (i j : (t.rationalBase ht).support) :
    (t.lieBasis ht).base.cartanMatrix (t.rationalLieBaseSupportEquiv ht i)
        (t.rationalLieBaseSupportEquiv ht j) =
      (t.rationalBase ht).cartanMatrix i j := by
  let a := (t.simpleSupportEquiv ht).symm i
  let b := (t.simpleSupportEquiv ht).symm j
  have hi : t.simpleSupportEquiv ht a = i := (t.simpleSupportEquiv ht).apply_symm_apply i
  have hj : t.simpleSupportEquiv ht b = j := (t.simpleSupportEquiv ht).apply_symm_apply j
  rw [← hi, ← hj]
  simp only [rationalLieBaseSupportEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    LieAlgebra.Basis.cartanMatrix_base_eq, Matrix.reindex_apply, Matrix.submatrix_apply,
    lieBasis_A_eq, cartanMatrix_rationalBase]

/-- **The pinned rational root system is equivalent to the Killing root system of the pinned
rational Lie algebra.** The equivalence sends each rational simple root to the root attached to
the correspondingly numbered generator of the distinguished Lie-algebra basis. -/
def rationalRootSystemEquiv :
    (t.rationalRootSystem ht).Equiv (rootSystem (t.cartanSubalgebra ht)) :=
  (t.rationalBase ht).equivOfCartanMatrixEq (t.lieBasis ht).base
    (t.rationalLieBaseSupportEquiv ht) (t.cartanMatrix_rationalLieBaseSupportEquiv ht)

/-! ## The pinned enumeration of the roots -/

/-- **The pinned enumeration of the roots of the rational Lie algebra.** The roots of
`TauCeti.DynkinType.lieAlgebra` are its nonzero weights for the distinguished Cartan subalgebra,
collected in `LieSubalgebra.root`. This is their bijection with the root indices `Fin t.numRoots`
of `TauCeti.DynkinType.simplyConnectedRootDatum`, carried by
`TauCeti.DynkinType.rationalRootSystemEquiv`; no second enumeration of the roots is introduced. -/
def rootEquiv : Fin t.numRoots ≃ (t.cartanSubalgebra ht).root :=
  (t.rationalRootSystemEquiv ht).indexEquiv

/-- The root enumeration is the index bijection of the pinned root-system equivalence. Rewriting
with this equation makes the general `RootPairing.Hom` API available for the enumeration. -/
theorem rootEquiv_eq_indexEquiv :
    t.rootEquiv ht = (t.rationalRootSystemEquiv ht).indexEquiv := (rfl)

/-- The enumeration, the index bijection of the pinned root-system equivalence, sends a
Bourbaki-numbered simple root to the simple root of the correspondingly numbered Chevalley
generator. -/
@[simp] theorem rootEquiv_simpleIndex (i : Fin t.rank) :
    t.rootEquiv ht (t.simpleIndex ht i) = (t.lieBasis ht).baseSupportEquiv i := by
  simpa only [rootEquiv, rationalRootSystemEquiv, rationalLieBaseSupportEquiv, Equiv.trans_apply,
    Equiv.symm_apply_apply, coe_simpleSupportEquiv] using
    equivOfCartanMatrixEq_indexEquiv_apply (t.rationalBase ht) (t.lieBasis ht).base
      (t.rationalLieBaseSupportEquiv ht) (t.cartanMatrix_rationalLieBaseSupportEquiv ht)
      (t.simpleSupportEquiv ht i)

/-- On a Bourbaki-numbered simple root, the weight equivalence lands at the simple Killing root
of the correspondingly numbered Lie-algebra generator. -/
@[simp] theorem rationalRootSystemEquiv_weightMap_root_simpleIndex (i : Fin t.rank) :
    (t.rationalRootSystemEquiv ht).weightMap
        ((t.rationalRootSystem ht).root (t.simpleIndex ht i)) =
      (rootSystem (t.cartanSubalgebra ht)).root
        ((t.lieBasis ht).baseSupportEquiv i) := by
  calc
    _ = (rootSystem (t.cartanSubalgebra ht)).root
        ((t.rationalRootSystemEquiv ht).indexEquiv (t.simpleIndex ht i)) := by
      exact RootPairing.Hom.root_weightMap_apply _ _ (t.simpleIndex ht i)
        (t.rationalRootSystemEquiv ht).toHom
    _ = _ := congrArg _ (t.rootEquiv_simpleIndex ht i)

/-- On a Bourbaki-numbered simple coroot, the covariant inverse coweight equivalence lands at the
simple Killing coroot of the correspondingly numbered Lie-algebra generator. -/
@[simp] theorem rationalRootSystemEquiv_coweightEquiv_symm_coroot_simpleIndex (i : Fin t.rank) :
    (t.rationalRootSystemEquiv ht).coweightEquiv.symm
        ((t.rationalRootSystem ht).coroot (t.simpleIndex ht i)) =
      (rootSystem (t.cartanSubalgebra ht)).coroot
        ((t.lieBasis ht).baseSupportEquiv i) := by
  simpa only [rationalRootSystemEquiv, rationalLieBaseSupportEquiv, Equiv.trans_apply,
    Equiv.symm_apply_apply, coe_simpleSupportEquiv] using
    equivOfCartanMatrixEq_coweightEquiv_symm_apply_coroot (t.rationalBase ht) (t.lieBasis ht).base
      (t.rationalLieBaseSupportEquiv ht) (t.cartanMatrix_rationalLieBaseSupportEquiv ht)
      (t.simpleSupportEquiv ht i)

/-- The `i`-th vector of the Cartan basis is the `i`-th coroot generator of the numbered basis. -/
private theorem cartanBasis_eq_h' (i : Fin t.rank) : t.cartanBasis ht i = (t.lieBasis ht).h' i :=
  Subtype.ext (t.coe_cartanBasis ht i)

/-- **The enumerated roots are the roots of the pinned root datum.** Root number `α` takes the
value `⟨α, αᵢ^∨⟩` on the `i`-th Cartan generator `hᵢ = αᵢ^∨`, which is the `i`-th coordinate of
`α` in `TauCeti.DynkinType.simplyConnectedRootDatum`, written against the fundamental weights. -/
@[simp] theorem rootEquiv_apply_cartanBasis (α : Fin t.numRoots) (i : Fin t.rank) :
    (t.rootEquiv ht α : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht)) (t.cartanBasis ht i) =
      (t.simplyConnectedRootDatum ht).root α i := by
  have hcoroot : coroot ((t.lieBasis ht).baseSupportEquiv i :
      Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht)) = (t.lieBasis ht).h' i := by
    -- Mathlib states this coroot under the instance `(t.lieBasis ht).isCartanSubalgebra`; the two
    -- sides differ only in such propositional instance arguments, which `convert` identifies.
    convert (t.lieBasis ht).coroot_eq_h' i using 1
  have hpairing : (t.rationalRootSystem ht).pairing α (t.simpleIndex ht i) =
      (t.simplyConnectedRootDatum ht).root α i := by
    rw [pairing_rationalRootSystem, ← RootPairing.root_coroot'_eq_pairing,
      coroot'_simpleIndex_apply]
  have h := (t.rationalRootSystemEquiv ht).toHom.pairing (i := α) (j := t.simpleIndex ht i)
  rw [← rootEquiv_eq_indexEquiv, rootEquiv_simpleIndex, rootSystem_pairing_apply, hcoroot] at h
  exact (congrArg _ (cartanBasis_eq_h' t ht i)).trans (h.trans hpairing)

/-- **A weight is the root with a given number exactly when it takes the values of that root of the
pinned datum on the Cartan generators.** The Cartan generators are a basis of the Cartan
subalgebra, so this characterizes the enumeration completely. -/
theorem coe_rootEquiv_eq_iff {α : Fin t.numRoots}
    {χ : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht)} :
    (t.rootEquiv ht α : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht)) = χ ↔
      ∀ i, χ (t.cartanBasis ht i) = (t.simplyConnectedRootDatum ht).root α i := by
  refine ⟨fun h i => h ▸ t.rootEquiv_apply_cartanBasis ht α i, fun h => ?_⟩
  have hlin : ((t.rootEquiv ht α : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht)) :
      t.cartanSubalgebra ht →ₗ[ℚ] ℚ) = (χ : t.cartanSubalgebra ht →ₗ[ℚ] ℚ) :=
    (t.cartanBasis ht).ext fun i => by
      simp only [Weight.toLinear_apply, rootEquiv_apply_cartanBasis, h]
  exact Weight.ext fun x => LinearMap.congr_fun hlin x

/-- **The enumeration commutes with negation**: the root indexed by the reflection of `α` in itself,
which is the index of `-α` in the pinned datum, is the negative of the root indexed by `α`. -/
@[simp] theorem rootEquiv_reflectionPerm_self (α : Fin t.numRoots) :
    t.rootEquiv ht ((t.simplyConnectedRootDatum ht).reflectionPerm α α) = -t.rootEquiv ht α := by
  rw [← reflectionPerm_rationalRootSystem]
  exact ((t.rationalRootSystemEquiv ht).toHom.indexEquiv_reflectionPerm α α).trans
    (rootSystem_reflectionPerm_self_eq_neg _)

/-- The numbered raising generator `eᵢ` is a root vector for the enumerated simple root
`αᵢ`. -/
theorem lieBasis_e_mem_rootSpace_rootEquiv (i : Fin t.rank) :
    (t.lieBasis ht).e i ∈ rootSpace (t.cartanSubalgebra ht)
      (t.rootEquiv ht (t.simpleIndex ht i) :
        Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht)) := by
  rw [rootEquiv_simpleIndex]
  exact lieBasis_e_mem_rootSpace (t.lieBasis ht) i

/-- The numbered lowering generator `fᵢ` is a root vector for the negative of the enumerated simple
root `αᵢ`. -/
theorem lieBasis_f_mem_rootSpace_rootEquiv (i : Fin t.rank) :
    (t.lieBasis ht).f i ∈ rootSpace (t.cartanSubalgebra ht)
      (-(t.rootEquiv ht (t.simpleIndex ht i) :
        Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht))) := by
  rw [rootEquiv_simpleIndex]
  exact lieBasis_f_mem_rootSpace (t.lieBasis ht) i

/-- Every root of the rational Lie algebra is enumerated. -/
theorem exists_coe_rootEquiv_eq {χ : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht)}
    (hχ : χ.IsNonZero) :
    ∃ α, (t.rootEquiv ht α : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht)) = χ :=
  ⟨(t.rootEquiv ht).symm ⟨χ, by simpa using hχ⟩, by simp⟩

/-! ## Root-indexed families of root vectors

`TauCeti.IsSl2System` and `TauCeti.IsChevalleySystem` are stated for families indexed by all
weights of the Cartan subalgebra, including the zero weight, where they ask for the value `0`. A
family indexed by the pinned root numbering is turned into such a family by
`TauCeti.DynkinType.extendRootFamily`, and the two conditions are restated in that numbering. -/

variable {t ht}

/-- **The weight-indexed family of a root-indexed family.** It takes the value `x α` at the root
numbered `α` and the value `0` at the zero weight, which is the value `TauCeti.IsSl2System`
prescribes there. -/
def extendRootFamily (x : Fin t.numRoots → t.lieAlgebra ht) :
    Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht) → t.lieAlgebra ht :=
  Function.extend
    (fun α => (t.rootEquiv ht α : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht))) x 0

/-- The extended family takes the value `x α` at the root numbered `α`. -/
@[simp] theorem extendRootFamily_rootEquiv (x : Fin t.numRoots → t.lieAlgebra ht)
    (α : Fin t.numRoots) :
    extendRootFamily x (t.rootEquiv ht α) = x α :=
  (Subtype.val_injective.comp (t.rootEquiv ht).injective).extend_apply x 0 α

/-- The extended family takes the value `x (-α)` at the negative of the root numbered `α`, where
`-α` is numbered by the reflection of `α` in itself. -/
@[simp] theorem extendRootFamily_neg_rootEquiv (x : Fin t.numRoots → t.lieAlgebra ht)
    (α : Fin t.numRoots) :
    extendRootFamily x (-(t.rootEquiv ht α : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht))) =
      x ((t.simplyConnectedRootDatum ht).reflectionPerm α α) := by
  rw [← val_neg_root, ← rootEquiv_reflectionPerm_self, extendRootFamily_rootEquiv]

/-- The extended family vanishes at the zero weight. -/
@[simp] theorem extendRootFamily_of_isZero (x : Fin t.numRoots → t.lieAlgebra ht)
    {χ : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht)} (hχ : χ.IsZero) :
    extendRootFamily x χ = 0 := by
  refine Function.extend_apply' _ _ _ fun ⟨α, hα⟩ => ?_
  exact LieSubalgebra.isNonZero_coe_root (t.rootEquiv ht α) (hα ▸ hχ)

/-- A weight-indexed family vanishing at the zero weight is the extension of its restriction to
the enumerated roots. -/
theorem extendRootFamily_restrict
    {y : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht) → t.lieAlgebra ht}
    (hy : ∀ χ, χ.IsZero → y χ = 0) :
    extendRootFamily (fun α => y (t.rootEquiv ht α)) = y := by
  funext χ
  by_cases hχ : χ.IsNonZero
  · obtain ⟨α, rfl⟩ := t.exists_coe_rootEquiv_eq ht hχ
    exact extendRootFamily_rootEquiv _ α
  · have hχ' : χ.IsZero := not_not.mp hχ
    rw [extendRootFamily_of_isZero _ hχ', hy χ hχ']

/-- **The `sl₂` normalization in the root numbering.** The extension of a root-indexed family is
a `TauCeti.IsSl2System` exactly when each `x α` lies in the root space of the root numbered `α`
and `⁅x α, x (-α)⁆` is the coroot of that root. -/
theorem isSl2System_extendRootFamily_iff (x : Fin t.numRoots → t.lieAlgebra ht) :
    IsSl2System (extendRootFamily x) ↔
      (∀ α, x α ∈ rootSpace (t.cartanSubalgebra ht)
        (t.rootEquiv ht α : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht))) ∧
      ∀ α, ⁅x α, x ((t.simplyConnectedRootDatum ht).reflectionPerm α α)⁆ =
        ((coroot (t.rootEquiv ht α : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht)) :
          t.cartanSubalgebra ht) : t.lieAlgebra ht) := by
  refine ⟨fun hx => ⟨fun α => ?_, fun α => ?_⟩, fun ⟨hmem, hlie⟩ => ⟨fun χ => ?_, fun χ hχ => ?_,
    fun χ hχ => extendRootFamily_of_isZero x hχ⟩⟩
  · simpa using hx.mem_rootSpace (t.rootEquiv ht α)
  · simpa using hx.lie_neg (t.rootEquiv ht α) (LieSubalgebra.isNonZero_coe_root _)
  · by_cases hχ : χ.IsNonZero
    · obtain ⟨α, rfl⟩ := t.exists_coe_rootEquiv_eq ht hχ
      simpa using hmem α
    · rw [extendRootFamily_of_isZero x (not_not.mp hχ)]
      exact zero_mem _
  · obtain ⟨α, rfl⟩ := t.exists_coe_rootEquiv_eq ht hχ
    simpa using hlie α

/-- **Chevalley systems in the root numbering.** The extension of a root-indexed family is a
`TauCeti.IsChevalleySystem` for `ω` exactly when it is normalized and `ω (x α) = -x (-α)` for every
root number `α`. -/
theorem isChevalleySystem_extendRootFamily_iff (ω : t.lieAlgebra ht ≃ₗ⁅ℚ⁆ t.lieAlgebra ht)
    (x : Fin t.numRoots → t.lieAlgebra ht) :
    IsChevalleySystem ω (extendRootFamily x) ↔
      IsSl2System (extendRootFamily x) ∧
        ∀ α, ω (x α) = -x ((t.simplyConnectedRootDatum ht).reflectionPerm α α) := by
  refine ⟨fun hx => ⟨hx.toIsSl2System, fun α => ?_⟩, fun ⟨hs, hω⟩ => ⟨hs, fun χ => ?_⟩⟩
  · simpa using hx.map_root (t.rootEquiv ht α)
  · by_cases hχ : χ.IsNonZero
    · obtain ⟨α, rfl⟩ := t.exists_coe_rootEquiv_eq ht hχ
      simpa using hω α
    · have hχ' : χ.IsZero := not_not.mp hχ
      rw [extendRootFamily_of_isZero x hχ', extendRootFamily_of_isZero x
        (Weight.isZero_neg.mpr hχ'), map_zero, neg_zero]

end


end TauCeti.DynkinType

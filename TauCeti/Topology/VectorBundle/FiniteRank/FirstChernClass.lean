/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Biproduct
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FirstChernClass.Prod

/-!
# The first Chern class of a complex finite-rank core

A complex point-indexed finite-rank core `C` over `B` reconstructs a complex vector bundle
`C.core.Fiber` with model fibre `Fin C.rank → ℂ`. Its first Chern class
`TauCeti.FiniteRankBundleCore.firstChernClass` is `TauCeti.firstChernClass` of this bundle, the
first Chern class `c₁ ∈ H²(B; ℤ)` of its determinant line.

Isomorphic cores have the same first Chern class (`firstChernClass_eq_of_iso`): the fibre maps of
an isomorphism of cores form a fibrewise complex-linear isomorphism of the reconstructed bundles,
continuous on total spaces. The ranks of isomorphic cores agree over a nonempty base, and over the
empty base every first Chern class vanishes (`TauCeti.firstChernClass_eq_zero_of_isEmpty`). The
first Chern class of a trivial core vanishes (`firstChernClass_trivial`), and that of the core
presenting an actual complex vector bundle is the first Chern class of the bundle
(`firstChernClass_ofBundle`).

A trivial summand does not change the first Chern class (`firstChernClass_trivial_whitneySum`,
`firstChernClass_whitneySum_trivial`): the Whitney sum of cores reconstructs Mathlib's direct-sum
bundle (`TauCeti.FiniteRankBundleCore.whitneySumTotalSpaceHomeomorph`), so this is
`TauCeti.firstChernClass_trivial_prod`.
-/

public section

noncomputable section

open Bundle CategoryTheory Module

namespace TauCeti.FiniteRankBundleCore

variable {B : Type} [TopologicalSpace B]

/-- The first Chern class `c₁(C) ∈ H²(B; ℤ)` of a complex finite-rank core `C`: the first Chern
class `TauCeti.firstChernClass` of the reconstructed complex vector bundle `C.core.Fiber`, with
model fibre `Fin C.rank → ℂ`. -/
def firstChernClass (C : FiniteRankBundleCore ℂ B) :
    (TopCat.of B).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) 2 :=
  _root_.TauCeti.firstChernClass (Fin C.rank → ℂ) C.core.Fiber

/-- The first Chern class of a core is that of its reconstructed bundle. -/
theorem firstChernClass_def (C : FiniteRankBundleCore ℂ B) :
    C.firstChernClass = _root_.TauCeti.firstChernClass (Fin C.rank → ℂ) C.core.Fiber :=
  (rfl)

/-- The first Chern class of the core presenting an actual complex vector bundle `E` is the first
Chern class of `E`: the reconstructed bundle is isomorphic to `E`. -/
@[simp]
theorem firstChernClass_ofBundle (n : ℕ) (E : B → Type) [∀ b, AddCommGroup (E b)]
    [∀ b, Module ℂ (E b)] [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace (Fin n → ℂ) E)] [FiberBundle (Fin n → ℂ) E]
    [VectorBundle ℂ (Fin n → ℂ) E] :
    (ofBundle ℂ n E).firstChernClass = _root_.TauCeti.firstChernClass (Fin n → ℂ) E := by
  -- `ofBundle ℂ n E` has rank `n` and core `pointIndexedCore ℂ (Fin n → ℂ) E` by definition
  -- (`rank_ofBundle`, `core_ofBundle`); the rank occurs in the model fibre, so the class is
  -- restated rather than rewritten.
  change _root_.TauCeti.firstChernClass (Fin n → ℂ) (pointIndexedCore ℂ (Fin n → ℂ) E).Fiber = _
  exact _root_.TauCeti.firstChernClass_eq_of_fiberwise
    (φ := pointIndexedCoreFiberEquiv ℂ (Fin n → ℂ) E)
    ((pointIndexedCoreHomeomorph ℂ (Fin n → ℂ) E).continuous.congr
      (pointIndexedCoreHomeomorph_apply ℂ (Fin n → ℂ) E))

/-- **Isomorphic cores have the same first Chern class.** -/
theorem firstChernClass_eq_of_iso {C C' : FiniteRankBundleCore ℂ B} (e : C ≅ C') :
    C.firstChernClass = C'.firstChernClass := by
  cases isEmpty_or_nonempty B
  · rw [firstChernClass_def, firstChernClass_def, _root_.TauCeti.firstChernClass_eq_zero_of_isEmpty,
      _root_.TauCeti.firstChernClass_eq_zero_of_isEmpty]
  obtain ⟨r', core', h'⟩ := C'
  obtain rfl : C.rank = r' := rank_eq_of_iso e
  let φ (b : B) : C.core.Fiber b ≃L[ℂ] core'.Fiber b :=
    ContinuousLinearEquiv.ofContinuousLinearMap (e.hom.fiberMap b) (e.inv.fiberMap b)
      (ContinuousLinearMap.ext (e.fiberMap_inv_hom_id_apply b))
      (ContinuousLinearMap.ext (e.fiberMap_hom_inv_id_apply b))
  exact (_root_.TauCeti.firstChernClass_eq_of_fiberwise (φ := φ)
    (e.hom.continuous_totalSpaceMap.congr fun ⟨b, v⟩ ↦ e.hom.totalSpaceMap_mk b v))

/-- **The first Chern class of a trivial core vanishes**: the standard basis vectors are constant
sections forming a global frame. -/
@[simp]
theorem firstChernClass_trivial (n : ℕ) : (trivial ℂ B n).firstChernClass = 0 :=
  _root_.TauCeti.firstChernClass_eq_zero_of_linearIndependent
    (s := fun i _ ↦ Module.finBasis ℂ (Fin n → ℂ) i)
    (fun _ ↦ continuous_trivial_iff.2 ⟨continuous_id, continuous_const⟩)
    fun _ ↦ (Module.finBasis ℂ (Fin n → ℂ)).linearIndependent

/-- **A trivial summand does not change the first Chern class**: `c₁(ℂⁿ ⊕ D) = c₁(D)`. -/
@[simp]
theorem firstChernClass_trivial_whitneySum (n : ℕ) (D : FiniteRankBundleCore ℂ B) :
    (whitneySum (trivial ℂ B n) D).firstChernClass = D.firstChernClass := by
  refine (_root_.TauCeti.firstChernClass_eq_of_fiberwise_trivialProd (V := Fin n → ℂ)
    (φ := fun b ↦ (whitneySumFiberEquiv (trivial ℂ B n) D b).symm) ?_).symm
  have hsplit (b : B) (w) : splitCoords (𝕜 := ℂ) (trivial ℂ B n).rank D.rank
      ((whitneySumFiberEquiv (trivial ℂ B n) D b).symm w) = w :=
    (whitneySumFiberEquiv_apply _ _ _ _).symm.trans
      ((whitneySumFiberEquiv (trivial ℂ B n) D b).apply_symm_apply w)
  have hdiag := (FiberBundle.Prod.isInducing_diag (Fin n → ℂ) (Trivial B (Fin n → ℂ))
    (Fin D.rank → ℂ) D.core.Fiber).continuous
  refine (continuous_mk_whitneySum_iff (trivial ℂ B n) D).2 ⟨?_, ?_⟩
  · refine Continuous.congr (f := fun y ↦ (⟨y.proj, y.snd.1⟩ : (trivial ℂ B n).core.TotalSpace))
      (continuous_trivial_iff.2 ⟨FiberBundle.continuous_proj _ _, continuous_snd.comp
        ((Trivial.homeomorphProd B _).continuous.comp (continuous_fst.comp hdiag))⟩) fun y ↦ ?_
    exact TotalSpace.ext rfl (heq_of_eq (congrArg Prod.fst (hsplit y.proj y.snd)).symm)
  · refine (continuous_snd.comp hdiag).congr fun y ↦ ?_
    exact TotalSpace.ext rfl (heq_of_eq (congrArg Prod.snd (hsplit y.proj y.snd)).symm)

/-- **A trivial summand does not change the first Chern class**: `c₁(C ⊕ ℂⁿ) = c₁(C)`. -/
@[simp]
theorem firstChernClass_whitneySum_trivial (C : FiniteRankBundleCore ℂ B) (n : ℕ) :
    (whitneySum C (trivial ℂ B n)).firstChernClass = C.firstChernClass := by
  rw [firstChernClass_eq_of_iso (whitneyCommIso C (trivial ℂ B n)),
    firstChernClass_trivial_whitneySum]

end TauCeti.FiniteRankBundleCore

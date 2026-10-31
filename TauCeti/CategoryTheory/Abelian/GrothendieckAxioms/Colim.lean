/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Monomorphisms out of exact sequential colimits

In an abelian category in which colimits indexed by `ℕ` are exact, a morphism out of the colimit
of a sequence is a monomorphism as soon as, at every stage, the next transition map kills
everything that the induced morphism from that stage kills
(`CategoryTheory.Limits.IsColimit.mono_of_comp_map_succ_eq_zero`). The kernels of the stages
then form a sequence with zero transitions, whose colimit vanishes, and exactness identifies
that colimit with the kernel of the morphism. This criterion detects injectivity on homology
for complexes built by successively killing homology classes, such as K-flat resolutions
obtained by attaching cells.
-/

public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [Abelian C]

/-- In an abelian category in which sequential colimits are exact, a morphism `ψ` out of the
colimit of a sequence is a monomorphism when at every stage the next transition map kills
everything which the induced morphism from that stage kills. -/
theorem IsColimit.mono_of_comp_map_succ_eq_zero [HasColimitsOfShape ℕ C]
    [HasExactColimitsOfShape ℕ C] {F : ℕ ⥤ C} {c : Cocone F} (hc : IsColimit c) {T : C}
    (ψ : c.pt ⟶ T)
    (h : ∀ (k : ℕ) {X : C} (g : X ⟶ F.obj k), g ≫ c.ι.app k ≫ ψ = 0 →
      g ≫ F.map (homOfLE (k.le_add_right 1)) = 0) :
    Mono ψ := by
  let α : F ⟶ (Functor.const ℕ).obj T :=
    { app k := c.ι.app k ≫ ψ
      naturality _ _ _ := by simp }
  -- the kernels of the stages form a sequence with zero transitions, so its colimit is zero
  have hzero : IsZero (colimit (kernel α)) := by
    have hmap (k : ℕ) : (kernel α).map (homOfLE (k.le_add_right 1)) = 0 := by
      rw [← cancel_mono ((kernel.ι α).app (k + 1)), NatTrans.naturality, zero_comp]
      have hk := congr_app (kernel.condition α) k
      rw [NatTrans.comp_app, NatTrans.app_zero] at hk
      exact h k _ hk
    rw [IsZero.iff_id_eq_zero]
    refine colimit.hom_ext fun k ↦ ?_
    rw [← colimit.w (kernel α) (homOfLE (k.le_add_right 1)), hmap]
    simp
  -- `colim` preserves kernels, so `colim.map α` is a monomorphism
  have : Mono (colim.map α) :=
    Preadditive.mono_of_isZero_kernel _ (hzero.of_iso (PreservesKernel.iso colim α).symm)
  -- `colim.map α` is `ψ` followed by the inclusion of `T` into the colimit of the constant
  -- sequence
  have hfac : colim.map α = (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) hc).hom ≫
      ψ ≫ colimit.ι ((Functor.const ℕ).obj T) 0 := by
    refine colimit.hom_ext fun k ↦ ?_
    rw [colim_map, ι_colimMap, ← colimit.w ((Functor.const ℕ).obj T) (homOfLE (Nat.zero_le k))]
    have := IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit F) hc k
    simp only [colimit.cocone_ι] at this
    simp [α, reassoc_of% this]
  rw [hfac] at this
  have : Mono (ψ ≫ colimit.ι ((Functor.const ℕ).obj T) 0) := by
    simpa using mono_comp
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) hc).inv
      ((IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) hc).hom ≫
        ψ ≫ colimit.ι ((Functor.const ℕ).obj T) 0)
  exact mono_of_mono ψ (colimit.ι ((Functor.const ℕ).obj T) 0)

end CategoryTheory.Limits

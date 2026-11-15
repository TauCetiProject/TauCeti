/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pushforward
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Closed
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Pullback of tensor products with globally presented sheaves

For a continuous final functor of ringed sites, the canonical pullback tensor comparison
`φ^*(M ⊗ N) ⟶ φ^*M ⊗ φ^*N` is invertible whenever either factor has a global presentation
by free sheaves. The other factor is arbitrary, and the generators and relations of the
presentation need not be finite. In particular, the comparison is invertible for a free
sheaf of any rank. These are the free and presented chart computations used to check
compatibility of pullback with tensor products locally.

The comparison is the existing oplax tensorator, rather than a separately chosen isomorphism.
Its naturality and compatibility with composition therefore follow from the canonical
oplax pullback structure. The proof uses Mathlib's `SheafOfModules.Presentation.isColimit`:
free sheaves are coproducts of the tensor unit, and presented sheaves are cokernels of maps
between free sheaves. Pullback and tensoring preserve these colimits.

## References

* The Stacks Project, *Sheaves of Modules*, Lemma 03EL (pullback of tensor products).
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

universe u

noncomputable section

namespace SheafOfModules

open _root_.SheafOfModules

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {F : C ⥤ D} [F.IsContinuous J K] [F.Final]
  {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  (φ : ringCatSheaf S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj (ringCatSheaf R))
  [(pushforward.{u} φ).IsRightAdjoint]

/-- Pullback preserves the tensor product with a free sheaf, of any rank. -/
theorem isIso_pullback_δ_free (I : Type u) (N : _root_.SheafOfModules.{u} (ringCatSheaf S)) :
    IsIso (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) (free I) N) := by
  have : IsIso (Functor.OplaxMonoidal.η (_root_.SheafOfModules.pullback φ)) := by
    rw [pullback_η]
    infer_instance
  exact Functor.OplaxMonoidal.isIso_δ_of_isColimit_left (_root_.SheafOfModules.pullback φ)
    (Discrete.functor (fun _ : I ↦ unit (ringCatSheaf S)))
    (freeCofan I) (isColimitFreeCofan I) N
    (fun _ ↦ Functor.OplaxMonoidal.isIso_δ_tensorUnit_left (_root_.SheafOfModules.pullback φ) N)

/-- Pullback preserves the tensor product with a free right factor, of any rank. -/
theorem isIso_pullback_δ_free_right (I : Type u) (M : _root_.SheafOfModules.{u} (ringCatSheaf S)) :
    IsIso (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M (free I)) := by
  have : IsIso (Functor.OplaxMonoidal.η (_root_.SheafOfModules.pullback φ)) := by
    rw [pullback_η]
    infer_instance
  exact Functor.OplaxMonoidal.isIso_δ_of_isColimit_right (_root_.SheafOfModules.pullback φ)
    (Discrete.functor (fun _ : I ↦ unit (ringCatSheaf S)))
    (freeCofan I) (isColimitFreeCofan I) M
    (fun _ ↦ Functor.OplaxMonoidal.isIso_δ_tensorUnit_right (_root_.SheafOfModules.pullback φ) M)

variable [HasSheafify J AddCommGrpCat.{u}]

/-- Pullback preserves the tensor product with a globally presented sheaf. No finiteness
condition is imposed on the presentation, and the other tensor factor is arbitrary. -/
theorem _root_.SheafOfModules.Presentation.isIso_pullback_δ
    {M : _root_.SheafOfModules.{u} (ringCatSheaf S)} (P : M.Presentation)
    (N : _root_.SheafOfModules.{u} (ringCatSheaf S)) :
    IsIso (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N) := by
  refine Functor.OplaxMonoidal.isIso_δ_of_isColimit_left
    (_root_.SheafOfModules.pullback φ) _ _ P.isColimit N ?_
  rintro (_ | _)
  all_goals exact isIso_pullback_δ_free φ _ N

/-- Pullback preserves the tensor product with a globally presented right factor. No finiteness
condition is imposed on the presentation, and the other tensor factor is arbitrary. -/
theorem _root_.SheafOfModules.Presentation.isIso_pullback_δ_right
    {N : _root_.SheafOfModules.{u} (ringCatSheaf S)} (P : N.Presentation)
    (M : _root_.SheafOfModules.{u} (ringCatSheaf S)) :
    IsIso (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N) := by
  refine Functor.OplaxMonoidal.isIso_δ_of_isColimit_right
    (_root_.SheafOfModules.pullback φ) _ _ P.isColimit M ?_
  rintro (_ | _)
  all_goals exact isIso_pullback_δ_free_right φ _ M

/-- The canonical tensor comparison isomorphism for pullback of a tensor product whose first
factor has a global free presentation. -/
def _root_.SheafOfModules.Presentation.pullbackTensorIso
    {M : _root_.SheafOfModules.{u} (ringCatSheaf S)} (P : M.Presentation)
    (N : _root_.SheafOfModules.{u} (ringCatSheaf S)) :
    (_root_.SheafOfModules.pullback φ).obj (M ⊗ N) ≅
      (_root_.SheafOfModules.pullback φ).obj M ⊗ (_root_.SheafOfModules.pullback φ).obj N :=
  have := P.isIso_pullback_δ φ N
  asIso (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N)

/-- The presented tensor comparison isomorphism uses the canonical oplax tensor comparison. -/
@[simp]
theorem _root_.SheafOfModules.Presentation.pullbackTensorIso_hom
    {M : _root_.SheafOfModules.{u} (ringCatSheaf S)} (P : M.Presentation)
    (N : _root_.SheafOfModules.{u} (ringCatSheaf S)) :
    (P.pullbackTensorIso φ N).hom =
      Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N :=
  (rfl)

/-- The canonical tensor comparison isomorphism for pullback of a tensor product whose second
factor has a global free presentation. -/
def _root_.SheafOfModules.Presentation.pullbackTensorIsoRight
    {N : _root_.SheafOfModules.{u} (ringCatSheaf S)} (P : N.Presentation)
    (M : _root_.SheafOfModules.{u} (ringCatSheaf S)) :
    (_root_.SheafOfModules.pullback φ).obj (M ⊗ N) ≅
      (_root_.SheafOfModules.pullback φ).obj M ⊗ (_root_.SheafOfModules.pullback φ).obj N :=
  have := P.isIso_pullback_δ_right φ M
  asIso (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N)

/-- The presented tensor comparison isomorphism uses the canonical oplax tensor comparison. -/
@[simp]
theorem _root_.SheafOfModules.Presentation.pullbackTensorIsoRight_hom
    {N : _root_.SheafOfModules.{u} (ringCatSheaf S)} (P : N.Presentation)
    (M : _root_.SheafOfModules.{u} (ringCatSheaf S)) :
    (P.pullbackTensorIsoRight φ M).hom =
      Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N :=
  (rfl)

end SheafOfModules

end

end TauCeti

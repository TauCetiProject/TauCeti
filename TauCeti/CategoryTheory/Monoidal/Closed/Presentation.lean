/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Closed.Functor
public import TauCeti.CategoryTheory.Monoidal.Closed.Kernels

/-!
# Internal-Hom comparisons and cokernel presentations

For a fixed target `N`, if a functor `F` preserves the cokernel presentation `f, g` of `M`
and the kernel of `(pre f).app N`, then invertibility of its internal-Hom comparisons for
the two presenting objects at `N` implies invertibility of its comparison for `M` at `N`.
This reduces the comparison for finitely presented modules to the finite free case, without
requiring the presented object to be projective.

The construction compares the two kernel presentations using `KernelFork.mapIsoOfIsLimit`.
-/

public section

open CategoryTheory Limits MonoidalClosed

namespace CategoryTheory.Functor

noncomputable section

variable {C D : Type*} [Category* C] [Category* D]
  [HasZeroMorphisms C] [HasZeroObject C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C]
  [HasZeroMorphisms D] [HasZeroObject D] [MonoidalCategory D] [BraidedCategory D]
  [MonoidalClosed D]
  (F : C ⥤ D) [F.LaxMonoidal] [F.PreservesZeroMorphisms]
  {A B M : C} (f : A ⟶ B) (g : B ⟶ M) (w : f ≫ g = 0)
  (h : IsColimit (CokernelCofork.ofπ g w)) (N : C)

include h in
/-- If `F` preserves the cokernel presentation `f, g` and the kernel of `(pre f).app N`,
and its internal-Hom comparisons for `A` and `B` are invertible at `N`, then its comparison
for `M` is invertible at `N`. -/
theorem ihomComparison_isIso_of_cokernel
    [PreservesColimit (parallelPair f 0) F]
    [PreservesLimit (parallelPair ((pre f).app N) 0) F]
    [IsIso ((F.ihomComparison A).app N)] [IsIso ((F.ihomComparison B).app N)] :
    IsIso ((F.ihomComparison M).app N) := by
  let k := KernelFork.ofι ((pre g).app N)
    (TauCeti.pre_app_comp_pre_app_eq_zero f g w N)
  let hk := KernelFork.mapIsLimit k
    (TauCeti.isLimitKernelForkPreOfIsColimit f g w h N) F
  let hq := CokernelCofork.mapIsColimit _ h F
  let ht := TauCeti.isLimitKernelForkPreOfIsColimit (F.map f) (F.map g)
    (by simp [← F.map_comp, w]) hq (F.obj N)
  have naturality {P Q : C} (a : P ⟶ Q) :
      (F.ihomComparison Q).app N ≫ (pre (F.map a)).app (F.obj N) =
        F.map ((pre a).app N) ≫ (F.ihomComparison P).app N := by
    -- Source naturality is packaged as an equality of squares; take its component at `N`.
    exact congrArg (fun s ↦ s.app N) (ihomComparison_whiskerLeft (F := F) a)
  let e := KernelFork.mapIsoOfIsLimit hk ht
    (Arrow.isoMk (asIso ((F.ihomComparison B).app N))
      (asIso ((F.ihomComparison A).app N)) (naturality f))
  have he : e.hom = (F.ihomComparison M).app N := by
    apply Fork.IsLimit.hom_ext ht
    exact (KernelFork.mapOfIsLimit_ι _ ht _).trans (naturality g).symm
  rw [← he]
  infer_instance

end

end CategoryTheory.Functor

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Short exact sequences from the homology of a distinguished triangle

The homology sequence of a distinguished triangle `F → X → Y → F[1]` exhibits `Hⁱ(F)`
as an extension of `ker (Hⁱ(X) → Hⁱ(Y))` by `coker (Hⁱ⁻¹(X) → Hⁱ⁻¹(Y))`.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DerivedCategory DerivedCategory.HomologySequence

namespace CategoryTheory.Pretriangulated.Triangle

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang _) (i : ℤ)

/-- The homology of the first vertex of a distinguished triangle, between the cokernel in the
preceding degree and the kernel in the current degree of the map on homology of `T.mor₂`. -/
@[expose, implicit_reducible]
noncomputable def homologyKernelCokernelSequence : ShortComplex A :=
  ShortComplex.mk (cokernel.desc _ (δ T (i - 1) i) (comp_δ T hT (i - 1) i))
    (kernel.lift ((homologyFunctor A i).map T.mor₂) ((homologyFunctor A i).map T.mor₁) (by
      simp only [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT, Functor.map_zero])) (by
      rw [← cancel_epi (cokernel.π _), ← cancel_mono (kernel.ι _)]
      simp [δ_comp T hT (i - 1) i])

/-- The first map is induced by the connecting homomorphism. -/
@[reassoc (attr := simp)]
theorem cokernel_π_comp_homologyKernelCokernelSequence_f :
    cokernel.π _ ≫ (T.homologyKernelCokernelSequence hT i).f = δ T (i - 1) i :=
  cokernel.π_desc _ _ _

/-- The second map is induced by the first morphism of the triangle. -/
@[reassoc (attr := simp)]
theorem homologyKernelCokernelSequence_g_comp_kernel_ι :
    (T.homologyKernelCokernelSequence hT i).g ≫ kernel.ι _ = (homologyFunctor A i).map T.mor₁ :=
  kernel.lift_ι _ _ _

/-- The kernel–cokernel segment of the homology sequence of a distinguished triangle is
short exact. -/
theorem homologyKernelCokernelSequence_shortExact :
    (T.homologyKernelCokernelSequence hT i).ShortExact where
  mono_f := (exact₃ T hT (i - 1) i).mono_cokernelDesc
  epi_g := (exact₂ T hT i).epi_kernelLift
  exact := by
    let S := T.homologyKernelCokernelSequence hT i
    have hf : cokernel.π _ ≫ S.f = δ T (i - 1) i :=
      T.cokernel_π_comp_homologyKernelCokernelSequence_f hT i
    have hg : S.g ≫ kernel.ι _ = (homologyFunctor A i).map T.mor₁ :=
      T.homologyKernelCokernelSequence_g_comp_kernel_ι hT i
    -- Compare through the sequence with the cokernel on the left only.
    let S' := ShortComplex.mk S.f ((homologyFunctor A i).map T.mor₁)
      (by rw [← hg, ← Category.assoc, S.zero, zero_comp])
    let p : ShortComplex.mk _ _ (δ_comp T hT (i - 1) i) ⟶ S' :=
      { τ₁ := cokernel.π _, τ₂ := 𝟙 _, τ₃ := 𝟙 _
        comm₁₂ := by simpa [S'] using hf
        comm₂₃ := by simp [S'] }
    let j : S ⟶ S' :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι _
        comm₁₂ := by simp [S']
        comm₂₃ := by simpa [S'] using hg.symm }
    have := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono p).1 (exact₁ T hT (i - 1) i)
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono j).2 this

end CategoryTheory.Pretriangulated.Triangle

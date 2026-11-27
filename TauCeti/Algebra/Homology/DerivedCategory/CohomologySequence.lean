/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# Kernel and cokernel sequences of distinguished triangles

The long exact cohomology sequence of a distinguished triangle gives a canonical short exact
sequence from the cokernel of its second map in the preceding degree to the kernel in the
current degree, through the cohomology of its first vertex. Vanishing of adjacent cohomology
identifies the middle term with the kernel or cokernel. The same long exact sequence bounds
the cohomological amplitude of the first vertex.
-/

public section

noncomputable section

universe w v u

open CategoryTheory Limits Pretriangulated DerivedCategory

namespace CategoryTheory.Pretriangulated.Triangle

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) (n : ℤ)

include hT

/-- The map from the cokernel of the second map on `H^(n-1)` to cohomology of the first vertex. -/
def cohomologyι :
    cokernel ((homologyFunctor C (n - 1)).map T.mor₂) ⟶
      (homologyFunctor C n).obj T.obj₁ :=
  cokernel.desc _ (HomologySequence.δ T (n - 1) n (by omega))
    (HomologySequence.comp_δ T hT (n - 1) n (by omega))

/-- The projection of cohomology of the first vertex to the kernel of the second map on `H^n`. -/
def cohomologyπ :
    (homologyFunctor C n).obj T.obj₁ ⟶
      kernel ((homologyFunctor C n).map T.mor₂) :=
  kernel.lift _ ((homologyFunctor C n).map T.mor₁) (by
    exact (homologyFunctor C 0).homologySequence_comp
      T hT n)

@[reassoc (attr := simp)]
lemma cokernel_π_cohomologyι :
    cokernel.π ((homologyFunctor C (n - 1)).map T.mor₂) ≫
      T.cohomologyι hT n = HomologySequence.δ T (n - 1) n (by omega) :=
  cokernel.π_desc _ _ _

@[reassoc (attr := simp)]
lemma cohomologyπ_kernel_ι :
    T.cohomologyπ hT n ≫
      kernel.ι ((homologyFunctor C n).map T.mor₂) =
        (homologyFunctor C n).map T.mor₁ :=
  kernel.lift_ι _ _ _

@[reassoc (attr := simp)]
lemma cohomologyι_π :
    T.cohomologyι hT n ≫ T.cohomologyπ hT n = 0 := by
  rw [← cancel_epi (cokernel.π _), ← cancel_mono (kernel.ι _)]
  simpa using HomologySequence.δ_comp T hT (n - 1) n

/-- The canonical sequence
`coker H^(n-1)(mor₂) → H^n(obj₁) → ker H^n(mor₂)`. -/
@[simps, implicit_reducible]
def cohomologySequence : ShortComplex C :=
  ShortComplex.mk (T.cohomologyι hT n) (T.cohomologyπ hT n)
    (T.cohomologyι_π hT n)

/-- The cokernel term embeds into cohomology of the first vertex. -/
instance mono_cohomologyι : Mono (T.cohomologyι hT n) :=
  (HomologySequence.exact₃ _ hT (n - 1) n
    (by omega)).mono_cokernelDesc

/-- Cohomology of the first vertex surjects onto the kernel term. -/
instance epi_cohomologyπ : Epi (T.cohomologyπ hT n) :=
  (HomologySequence.exact₂ _ hT n).epi_kernelLift

/-- The canonical kernel/cokernel sequence for a distinguished triangle is short exact. -/
theorem cohomologySequence_shortExact :
    (T.cohomologySequence hT n).ShortExact :=
  (HomologySequence.exact₁ T hT (n - 1) n).shortExact_cokernelDesc_kernelLift _ _
    (HomologySequence.exact₃ T hT (n - 1) n)
    (HomologySequence.exact₂ T hT n)

/-- If the preceding cohomology of the third vertex vanishes, cohomology of the first vertex
is the kernel of the second map in the current degree, via the canonical projection. -/
def cohomologyIsoKernel
    (h : IsZero ((homologyFunctor C (n - 1)).obj T.obj₃)) :
    (homologyFunctor C n).obj T.obj₁ ≅
      kernel ((homologyFunctor C n).map T.mor₂) := by
  have hz : IsZero (cokernel
      ((homologyFunctor C (n - 1)).map T.mor₂)) :=
    h.of_epi (cokernel.π _)
  have : IsIso (T.cohomologyπ hT n) :=
    (T.cohomologySequence_shortExact hT n).isIso_g_iff.mpr hz
  exact asIso (T.cohomologyπ hT n)

@[simp]
lemma cohomologyIsoKernel_hom
    (h : IsZero ((homologyFunctor C (n - 1)).obj T.obj₃)) :
    (T.cohomologyIsoKernel hT n h).hom = T.cohomologyπ hT n := (rfl)

/-- If the current cohomology of the second vertex vanishes, cohomology of the first vertex
is the cokernel of the second map in the preceding degree. Its inverse is the boundary map. -/
def cohomologyIsoCokernel
    (h : IsZero ((homologyFunctor C n).obj T.obj₂)) :
    (homologyFunctor C n).obj T.obj₁ ≅
      cokernel ((homologyFunctor C (n - 1)).map T.mor₂) := by
  have hz : IsZero (kernel ((homologyFunctor C n).map T.mor₂)) :=
    h.of_mono (kernel.ι _)
  have : IsIso (T.cohomologyι hT n) :=
    (T.cohomologySequence_shortExact hT n).isIso_f_iff.mpr hz
  exact (asIso (T.cohomologyι hT n)).symm

@[simp]
lemma cohomologyIsoCokernel_inv
    (h : IsZero ((homologyFunctor C n).obj T.obj₂)) :
    (T.cohomologyIsoCokernel hT n h).inv = T.cohomologyι hT n := (rfl)

/-- Vanishing in the adjacent degrees at the second and third vertices forces vanishing
at the first vertex. -/
lemma isZero_homology_obj₁
    (h₀ : IsZero ((homologyFunctor C (n - 1)).obj T.obj₃))
    (h₁ : IsZero ((homologyFunctor C n).obj T.obj₂)) :
    IsZero ((homologyFunctor C n).obj T.obj₁) :=
  (HomologySequence.exact₁ T hT (n - 1) n).isZero_of_both_zeros
    (h₀.eq_of_src _ _) (h₁.eq_of_tgt _ _)

/-- A fibre of a map between objects bounded below by `a` is bounded below by `a`. -/
lemma isGE_obj₁ (a : ℤ) [T.obj₂.IsGE a] [T.obj₃.IsGE a] : T.obj₁.IsGE a := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  exact T.isZero_homology_obj₁ hT i
    (DerivedCategory.isZero_of_isGE T.obj₃ a (i - 1) (by omega))
    (DerivedCategory.isZero_of_isGE T.obj₂ a i hi)

/-- A fibre of a map between objects bounded above by `b` is bounded above by `b + 1`. -/
lemma isLE_obj₁ (b : ℤ) [T.obj₂.IsLE b] [T.obj₃.IsLE b] : T.obj₁.IsLE (b + 1) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  exact T.isZero_homology_obj₁ hT i
    (DerivedCategory.isZero_of_isLE T.obj₃ b (i - 1) (by omega))
    (DerivedCategory.isZero_of_isLE T.obj₂ b i (by omega))

end CategoryTheory.Pretriangulated.Triangle

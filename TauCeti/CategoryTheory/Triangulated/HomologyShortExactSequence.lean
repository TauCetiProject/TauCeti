/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# Kernel and cokernel sequences of distinguished triangles

The long exact sequence of a homological functor on a distinguished triangle gives a short
exact sequence from the cokernel of its second map in the preceding degree to the kernel in
the current degree, through the homology of its first vertex. The sequence is natural in the
triangle. If the preceding second map is epi or the current one is mono, the middle term is
canonically isomorphic to the kernel or cokernel, respectively.
-/

public section

noncomputable section

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory.Pretriangulated.Triangle

variable {D A : Type*} [Category* D] [Category* A] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ (n : ℤ), (CategoryTheory.shiftFunctor D n).Additive]
  [Pretriangulated D] [Abelian A]
  (T : Triangle D) (F : D ⥤ A) [F.IsHomological] [F.ShiftSequence ℤ]
  (hT : T ∈ distTriang D) (n : ℤ)

include hT

/-- The map from the cokernel of the second map in the preceding degree to the homology
of the first vertex. -/
def homologyι : cokernel ((F.shift (n - 1)).map T.mor₂) ⟶ (F.shift n).obj T.obj₁ :=
  cokernel.desc _ (F.homologySequenceδ T (n - 1) n (by omega))
    (F.comp_homologySequenceδ T hT (n - 1) n (by omega))

/-- The projection of the homology of the first vertex to the kernel of the second map
in the current degree. -/
def homologyπ : (F.shift n).obj T.obj₁ ⟶ kernel ((F.shift n).map T.mor₂) :=
  kernel.lift _ ((F.shift n).map T.mor₁) (F.homologySequence_comp T hT n)

@[reassoc (attr := simp)]
lemma cokernel_π_homologyι :
    cokernel.π ((F.shift (n - 1)).map T.mor₂) ≫
      T.homologyι F hT n = F.homologySequenceδ T (n - 1) n (by omega) :=
  cokernel.π_desc _ _ _

@[reassoc (attr := simp)]
lemma homologyπ_kernel_ι :
    T.homologyπ F hT n ≫ kernel.ι ((F.shift n).map T.mor₂) = (F.shift n).map T.mor₁ :=
  kernel.lift_ι _ _ _

@[reassoc (attr := simp)]
lemma homologyι_π : T.homologyι F hT n ≫ T.homologyπ F hT n = 0 := by
  rw [← cancel_epi (cokernel.π _), ← cancel_mono (kernel.ι _)]
  simpa using F.homologySequenceδ_comp T hT (n - 1) n (by omega)

/-- The canonical sequence
`coker H^(n-1)(mor₂) → H^n(obj₁) → ker H^n(mor₂)`. Its three objects reduce so
the components of induced morphisms can be used directly as maps between them. -/
@[expose, simps, implicit_reducible]
def homologyShortExactSequence : ShortComplex A :=
  ShortComplex.mk (T.homologyι F hT n) (T.homologyπ F hT n) (T.homologyι_π F hT n)

/-- The cokernel term embeds into the homology of the first vertex. -/
instance mono_homologyι : Mono (T.homologyι F hT n) :=
  (F.homologySequence_exact₃ T hT (n - 1) n (by omega)).mono_cokernelDesc

/-- The homology of the first vertex surjects onto the kernel term. -/
instance epi_homologyπ : Epi (T.homologyπ F hT n) :=
  (F.homologySequence_exact₂ T hT n).epi_kernelLift

/-- The canonical kernel/cokernel sequence for a distinguished triangle is short exact. -/
theorem homologyShortExactSequence_shortExact :
    (T.homologyShortExactSequence F hT n).ShortExact :=
  (F.homologySequence_exact₁ T hT (n - 1) n (by omega)).shortExact_cokernelDesc_kernelLift _ _
    (F.homologySequence_exact₃ T hT (n - 1) n (by omega))
    (F.homologySequence_exact₂ T hT n)

/-- The morphism of the kernel/cokernel sequences induced by a morphism of distinguished
triangles. -/
def homologyShortExactSequenceMap {T' : Triangle D} (hT' : T' ∈ distTriang D) (φ : T ⟶ T') :
    T.homologyShortExactSequence F hT n ⟶ T'.homologyShortExactSequence F hT' n where
  τ₁ := cokernel.map _ _ ((F.shift (n - 1)).map φ.hom₂) ((F.shift (n - 1)).map φ.hom₃)
    (by simp only [← Functor.map_comp, φ.comm₂])
  τ₂ := (F.shift n).map φ.hom₁
  τ₃ := kernel.map _ _ ((F.shift n).map φ.hom₂) ((F.shift n).map φ.hom₃)
    (by simp only [← Functor.map_comp, φ.comm₂])
  comm₁₂ := by
    rw [← cancel_epi (cokernel.π ((F.shift (n - 1)).map T.mor₂))]
    simpa using F.homologySequenceδ_naturality φ (n - 1) n (by omega)
  comm₂₃ := by
    rw [← cancel_mono (kernel.ι ((F.shift n).map T'.mor₂))]
    simp [← Functor.map_comp]

variable {T} {T' : Triangle D} (hT' : T' ∈ distTriang D) (φ : T ⟶ T')

@[simp]
lemma homologyShortExactSequenceMap_τ₁ :
    (T.homologyShortExactSequenceMap F hT n hT' φ).τ₁ =
      cokernel.map _ _ ((F.shift (n - 1)).map φ.hom₂) ((F.shift (n - 1)).map φ.hom₃)
        (by simp only [← Functor.map_comp, φ.comm₂]) := (rfl)

@[simp]
lemma homologyShortExactSequenceMap_τ₂ :
    (T.homologyShortExactSequenceMap F hT n hT' φ).τ₂ = (F.shift n).map φ.hom₁ := (rfl)

@[simp]
lemma homologyShortExactSequenceMap_τ₃ :
    (T.homologyShortExactSequenceMap F hT n hT' φ).τ₃ =
      kernel.map _ _ ((F.shift n).map φ.hom₂) ((F.shift n).map φ.hom₃)
        (by simp only [← Functor.map_comp, φ.comm₂]) := (rfl)

variable (T)

/-- If the preceding second map is epi, the homology of the first vertex is the kernel of
the current second map, via the canonical projection. -/
def homologyIsoKernel [Epi ((F.shift (n - 1)).map T.mor₂)] :
    (F.shift n).obj T.obj₁ ≅ kernel ((F.shift n).map T.mor₂) := by
  have : IsIso (T.homologyπ F hT n) :=
    (T.homologyShortExactSequence_shortExact F hT n).isIso_g_iff.mpr (isZero_cokernel_of_epi _)
  exact asIso (T.homologyπ F hT n)

@[simp]
lemma homologyIsoKernel_hom [Epi ((F.shift (n - 1)).map T.mor₂)] :
    (T.homologyIsoKernel F hT n).hom = T.homologyπ F hT n := (rfl)

/-- If the current second map is mono, the homology of the first vertex is the cokernel of
the preceding second map. The inverse is induced by the connecting morphism. -/
def homologyIsoCokernel [Mono ((F.shift n).map T.mor₂)] :
    (F.shift n).obj T.obj₁ ≅ cokernel ((F.shift (n - 1)).map T.mor₂) := by
  have : IsIso (T.homologyι F hT n) :=
    (T.homologyShortExactSequence_shortExact F hT n).isIso_f_iff.mpr (isZero_kernel_of_mono _)
  exact (asIso (T.homologyι F hT n)).symm

@[simp]
lemma homologyIsoCokernel_inv [Mono ((F.shift n).map T.mor₂)] :
    (T.homologyIsoCokernel F hT n).inv = T.homologyι F hT n := (rfl)

/-- Vanishing of the preceding homology at the third vertex and current homology at the
second vertex forces vanishing of the current homology at the first vertex. -/
lemma isZero_homology_obj₁
    (h₃ : IsZero ((F.shift (n - 1)).obj T.obj₃)) (h₂ : IsZero ((F.shift n).obj T.obj₂)) :
    IsZero ((F.shift n).obj T.obj₁) :=
  (F.homologySequence_exact₁ T hT (n - 1) n (by omega)).isZero_of_both_zeros
    (h₃.eq_of_src _ _) (h₂.eq_of_tgt _ _)

end CategoryTheory.Pretriangulated.Triangle

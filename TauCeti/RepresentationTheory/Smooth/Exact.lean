/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Rep.TensorShortExact
public import TauCeti.RepresentationTheory.Smooth.Abelian

/-!
# Exactness of smooth representations on underlying modules

The inclusion `SmoothRep A G ⥤ Rep A G` preserves finite limits and colimits, so it preserves
homology (Mathlib's instance `CategoryTheory.Functor.preservesHomologyOfExact`). Hence a short
complex of smooth representations is exact exactly when the underlying linear maps form an exact
pair (`TauCeti.SmoothRep.exact_iff_function_exact`): kernels and cokernels in `SmoothRep A G` are
computed on the underlying `A`-modules. In particular the kernel of a morphism `f` is the linear
kernel of `f` (`TauCeti.SmoothRep.range_kernel_ι`), and its cokernel is the linear cokernel
(`TauCeti.SmoothRep.ker_cokernel_π`).
-/

public section

open CategoryTheory Limits

namespace TauCeti

namespace SmoothRep

variable {A G : Type*} [Ring A] [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- **Exactness is computed on underlying modules.** A short complex of smooth representations is
exact if and only if the underlying linear maps form an exact pair. -/
theorem exact_iff_function_exact (S : ShortComplex (SmoothRep A G)) :
    S.Exact ↔ Function.Exact S.f.hom.hom S.g.hom.hom := by
  rw [← ShortComplex.exact_map_iff_of_faithful S (ι A G), Rep.exact_iff_function_exact]
  simp only [ShortComplex.map_f, ShortComplex.map_g, ObjectProperty.ι_map]

/-- **The kernel of a morphism of smooth representations is its linear kernel**: the image of
`kernel.ι f` is the kernel of the underlying linear map of `f`. -/
theorem range_kernel_ι {V W : SmoothRep A G} (f : V ⟶ W) :
    LinearMap.range (kernel.ι f).hom.hom.toLinearMap = LinearMap.ker f.hom.hom.toLinearMap :=
  ((exact_iff_function_exact _).1
    (ShortComplex.exact_of_f_is_kernel (ShortComplex.mk (kernel.ι f) f (kernel.condition f))
      (kernelIsKernel f))).linearMap_ker_eq.symm

/-- **The cokernel of a morphism of smooth representations is its linear cokernel**: the kernel of
`cokernel.π f` is the image of the underlying linear map of `f`. -/
theorem ker_cokernel_π {V W : SmoothRep A G} (f : V ⟶ W) :
    LinearMap.ker (cokernel.π f).hom.hom.toLinearMap = LinearMap.range f.hom.hom.toLinearMap :=
  ((exact_iff_function_exact _).1
    (ShortComplex.exact_of_g_is_cokernel (ShortComplex.mk f (cokernel.π f) (cokernel.condition f))
      (cokernelIsCokernel f))).linearMap_ker_eq

end SmoothRep

end TauCeti

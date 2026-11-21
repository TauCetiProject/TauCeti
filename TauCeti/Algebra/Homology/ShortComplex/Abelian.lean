/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Kernels

import Mathlib.CategoryTheory.Abelian.Exact
import TauCeti.CategoryTheory.ObjectProperty.AdditiveFunction
import TauCeti.CategoryTheory.ObjectProperty.Kernels

/-!
# Short complexes in abelian categories

For a short complex `S = (X₁ ⟶ X₂ ⟶ X₃)` in an abelian category, the cokernel of the canonical
inclusion `S.abelianImageToKernel : Abelian.image S.f ⟶ kernel S.g` identifies with `S.homology`
(`CategoryTheory.ShortComplex.cokernelAbelianImageToKernelIsoHomology`).

Combining the two resulting short exact sequences `0 ⟶ ker g ⟶ X₂ ⟶ coim g ⟶ 0` and
`0 ⟶ im f ⟶ ker g ⟶ coker (im f ⟶ ker g) ⟶ 0`, any function `v : C → G` into an abelian group
that is additive on short exact sequences in a class `P` containing zero and closed under kernels
and cokernels satisfies the short-complex rank--nullity identity
`v S.X₂ = v S.homology + v (Abelian.image S.f) + v (Abelian.image S.g)`
(`CategoryTheory.ShortComplex.map_X₂_eq_add_image`).
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The cokernel of the canonical monomorphism `S.abelianImageToKernel : Abelian.image S.f ⟶
kernel S.g` is isomorphic to `S.homology`. -/
noncomputable def cokernelAbelianImageToKernelIsoHomology (S : ShortComplex C) :
    cokernel S.abelianImageToKernel ≅ S.homology := by
  have hfac :
      kernel.lift S.g S.f S.zero = Abelian.factorThruImage S.f ≫ S.abelianImageToKernel := by
    rw [← cancel_mono (kernel.ι S.g), kernel.lift_ι, Category.assoc,
      S.abelianImageToKernel_comp_kernel_ι, Abelian.image.fac]
  exact (cokernelEpiComp (Abelian.factorThruImage S.f) S.abelianImageToKernel).symm ≪≫
    cokernelIsoOfEq hfac.symm ≪≫ S.homologyIsoCokernelLift.symm

/-- **Short-complex rank--nullity identity for an additive function on a kernel/cokernel-closed
class.** For a short complex `S = (X₁ ⟶ X₂ ⟶ X₃)` whose terms lie in a class `P` containing zero
and closed under kernels and cokernels, any function `v` additive on short exact sequences in `P`
satisfies `v X₂ = v (H S) + v (im f) + v (im g)`. -/
theorem map_X₂_eq_add_image (S : ShortComplex C) (P : ObjectProperty C)
    [P.ContainsZero] [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
    {G : Type*} [AddCommGroup G] (v : C → G)
    (hv : ∀ T : ShortComplex C, T.ShortExact → P T.X₁ → P T.X₂ → P T.X₃ →
      v T.X₂ = v T.X₁ + v T.X₃)
    (h₁ : P S.X₁) (h₂ : P S.X₂) (h₃ : P S.X₃) :
    v S.X₂ = v S.homology + v (Abelian.image S.f) + v (Abelian.image S.g) := by
  have := P.isClosedUnderIsomorphisms_of_isClosedUnderKernels
  have hK : P (kernel S.g) := P.prop_kernel S.g h₂ h₃
  have hImF : P (Abelian.image S.f) :=
    P.prop_kernel (cokernel.π S.f) h₂ (P.prop_cokernel S.f h₁ h₂)
  have hCoimG : P (Abelian.coimage S.g) := P.prop_cokernel (kernel.ι S.g) hK h₂
  have hCok : P (cokernel S.abelianImageToKernel) :=
    P.prop_cokernel S.abelianImageToKernel hImF hK
  -- Short exact sequence `0 ⟶ ker g ⟶ X₂ ⟶ coim g ⟶ 0`.
  have hS₁ : (ShortComplex.mk (kernel.ι S.g) (cokernel.π (kernel.ι S.g))
      (cokernel.condition _)).ShortExact :=
    ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  have h₁' : v S.X₂ = v (kernel S.g) + v (Abelian.coimage S.g) := hv _ hS₁ hK h₂ hCoimG
  -- Short exact sequence `0 ⟶ im f ⟶ ker g ⟶ coker(im f ⟶ ker g) ⟶ 0`.
  have hS₂ : (ShortComplex.mk S.abelianImageToKernel (cokernel.π S.abelianImageToKernel)
      (cokernel.condition _)).ShortExact :=
    ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  have h₂' : v (kernel S.g) = v (Abelian.image S.f) + v (cokernel S.abelianImageToKernel) :=
    hv _ hS₂ hImF hK hCok
  rw [h₁', h₂', P.map_eq_of_iso hv (Abelian.coimageIsoImage S.g) hCoimG,
    P.map_eq_of_iso hv S.cokernelAbelianImageToKernelIsoHomology hCok]
  abel

end CategoryTheory.ShortComplex

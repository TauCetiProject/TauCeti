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
public import TauCeti.CategoryTheory.ObjectProperty.AdditiveFunction

import Mathlib.CategoryTheory.Abelian.Exact
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
  exact (cokernelEpiComp S.abelianImageToKernel (Abelian.factorThruImage S.f)).symm ≪≫
    cokernelIsoOfEq hfac.symm ≪≫ S.homologyIsoCokernelLift.symm

/-- The canonical projection `kernel S.g ⟶ cokernel S.abelianImageToKernel` followed by
`S.cokernelAbelianImageToKernelIsoHomology.hom` is the projection `kernel S.g ⟶ S.homology`. -/
@[reassoc (attr := simp)]
lemma cokernel_π_comp_cokernelAbelianImageToKernelIsoHomology_hom (S : ShortComplex C) :
    cokernel.π S.abelianImageToKernel ≫ S.cokernelAbelianImageToKernelIsoHomology.hom =
      S.liftCycles (kernel.ι S.g) (kernel.condition S.g) ≫ S.homologyπ := by
  dsimp [cokernelAbelianImageToKernelIsoHomology]
  simp only [cokernelEpiComp_inv, cokernel.π_desc_assoc, π_comp_cokernelIsoOfEq_hom_assoc]
  let h := LeftHomologyData.ofHasKernelOfHasCokernel S
  have h₁ : h.π ≫ h.homologyIso.inv = h.cyclesIso.inv ≫ S.homologyπ := h.π_comp_homologyIso_inv
  have h₂ : h.cyclesIso.inv = S.liftCycles h.i h.wi := by
    rw [← cancel_mono S.iCycles, h.cyclesIso_inv_comp_iCycles, S.liftCycles_i]
  rw [h₂] at h₁
  exact h₁

/-- The homology projection `S.homologyπ` followed by
`S.cokernelAbelianImageToKernelIsoHomology.inv` factors through the cokernel projection
`kernel S.g ⟶ cokernel S.abelianImageToKernel`. -/
@[reassoc (attr := simp)]
lemma homologyπ_comp_cokernelAbelianImageToKernelIsoHomology_inv (S : ShortComplex C) :
    S.homologyπ ≫ S.cokernelAbelianImageToKernelIsoHomology.inv =
      kernel.lift S.g S.iCycles S.iCycles_g ≫ cokernel.π S.abelianImageToKernel := by
  have hl : kernel.lift S.g S.iCycles S.iCycles_g ≫
      S.liftCycles (kernel.ι S.g) (kernel.condition S.g) = 𝟙 S.cycles := by
    rw [← cancel_mono S.iCycles]
    simp
  rw [← cancel_mono S.cokernelAbelianImageToKernelIsoHomology.hom, Category.assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id,
    cokernel_π_comp_cokernelAbelianImageToKernelIsoHomology_hom, ← Category.assoc, hl,
    Category.id_comp]

/-- **Short-complex rank--nullity identity for an additive function on a kernel/cokernel-closed
class.** For a short complex `S = (X₁ ⟶ X₂ ⟶ X₃)` whose terms lie in a class `P` containing zero
and closed under kernels and cokernels, any function `v` additive on short exact sequences in `P`
satisfies `v X₂ = v (H S) + v (im f) + v (im g)`. -/
theorem map_X₂_eq_add_image (S : ShortComplex C) (P : ObjectProperty C)
    [P.ContainsZero] [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
    {G : Type*} [AddCommGroup G] (v : C → G) (hv : P.IsAdditiveOn v)
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
  have h₁' : v S.X₂ = v (kernel S.g) + v (Abelian.coimage S.g) :=
    hv.map_shortExact hS₁ hK h₂ hCoimG
  -- Short exact sequence `0 ⟶ im f ⟶ ker g ⟶ coker(im f ⟶ ker g) ⟶ 0`.
  have hS₂ : (ShortComplex.mk S.abelianImageToKernel (cokernel.π S.abelianImageToKernel)
      (cokernel.condition _)).ShortExact :=
    ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  have h₂' : v (kernel S.g) = v (Abelian.image S.f) + v (cokernel S.abelianImageToKernel) :=
    hv.map_shortExact hS₂ hImF hK hCok
  rw [h₁', h₂', P.map_eq_of_iso hv (Abelian.coimageIsoImage S.g) hCoimG,
    P.map_eq_of_iso hv S.cokernelAbelianImageToKernelIsoHomology hCok]
  abel

end CategoryTheory.ShortComplex

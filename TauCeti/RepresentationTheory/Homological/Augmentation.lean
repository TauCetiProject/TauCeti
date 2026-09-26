/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RepresentationTheory.Rep.Res

/-!
# The augmentation ideal and the augmentation sequence

For a group `G` and a commutative ring `k`, the **augmentation** `k[G] ⟶ k` sends a group ring
element to the sum of its coefficients, and its kernel `I_G` is the **augmentation ideal**, here
taken as a representation of `G`. The **augmentation sequence** `0 ⟶ I_G ⟶ k[G] ⟶ k ⟶ 0` is short
exact, and stays short exact after restriction along any monoid homomorphism.

Nothing here mentions cohomology: the cohomological consequences live in
`TauCeti.RepresentationTheory.Homological.TateCohomology.Augmentation`, which imports this file.

## Main definitions

* `Rep.augmentation`: the augmentation `k[G] ⟶ k`.
* `Rep.augmentationIdeal`: the augmentation ideal `I_G`, the kernel of the augmentation.
* `Rep.augmentationSES`: the short exact sequence `I_G ⟶ k[G] ⟶ k`.
* `Rep.augmentationιIsKernel`: the augmentation ideal is a kernel of the augmentation.

## Main statements

* `Rep.augmentationSES_shortExact`, `Rep.augmentationSES_res_shortExact`: the augmentation
  sequence is short exact, also after restriction along a monoid homomorphism.
* `TauCeti.AugmentationIdeal.singleSub`, `TauCeti.AugmentationIdeal.ι_singleSub`:
  an element mapping to
  `[g] a - [1] a` and its image under the inclusion.
* `TauCeti.AugmentationIdeal.ρ_singleSub`, `TauCeti.AugmentationIdeal.singleSub_one`:
  the group action and value at the identity.

## References

* J. S. Milne, *Class Field Theory*, Chapter II, proof of Theorem 3.11.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, (3.1.4).
* The same construction appears in `ClassFieldTheory/Cohomology/AugmentationModule.lean` in
  `kbuzzard/ClassFieldTheory`, commit `ccc3323c6750abca25b49b35106f54eb3a398509` (Apache-2.0);
  it is reimplemented here on Mathlib's `Rep` API rather than copied.
-/

public noncomputable section

universe u

open CategoryTheory Limits

namespace Rep

variable (k G : Type u) [CommRing k] [Group G]

/-- The **augmentation** `k[G] ⟶ k`, the map of representations sending a group ring element to
the sum of its coefficients; it is the map out of the left regular representation attached to
`1 : k`. -/
abbrev augmentation : leftRegular k G ⟶ trivial k G k := leftRegularHom (trivial k G k) 1

/-- The augmentation is surjective. -/
instance augmentation_epi : Epi (augmentation k G) :=
  (epi_iff_surjective _).2 fun r ↦ ⟨.single 1 r, by simp⟩

/-- The **augmentation ideal** `I_G`, the kernel of the augmentation `k[G] ⟶ k`, as a
representation of `G`. The body is exposed because the endpoints of the connecting homomorphism
built from `augmentationSES` appear in downstream statement types. -/
@[expose] def augmentationIdeal : Rep k G := kernel (augmentation k G)

/-- The inclusion of the augmentation ideal into the left regular representation. -/
def augmentationι : augmentationIdeal k G ⟶ leftRegular k G := kernel.ι (augmentation k G)

/-- The inclusion of the augmentation ideal is a monomorphism. -/
instance augmentationι_mono : Mono (augmentationι k G) :=
  inferInstanceAs (Mono (kernel.ι (augmentation k G)))

/-- The inclusion of the augmentation ideal followed by the augmentation is zero. -/
@[reassoc (attr := simp)]
theorem augmentationι_comp_augmentation : augmentationι k G ≫ augmentation k G = 0 :=
  kernel.condition (augmentation k G)

/-- The inclusion of the augmentation ideal is a kernel of the augmentation. -/
def augmentationιIsKernel :
    IsLimit (KernelFork.ofι (augmentationι k G) (augmentationι_comp_augmentation k G)) :=
  kernelIsKernel (augmentation k G)

/-- The **augmentation sequence** `I_G ⟶ k[G] ⟶ k`. The body is exposed for the same reason as
`augmentationIdeal`: downstream statements name the endpoints of its connecting homomorphism. -/
@[expose] def augmentationSES : ShortComplex (Rep k G) :=
  ShortComplex.kernelSequence (augmentation k G)

/-- The augmentation sequence has maps the inclusion of the augmentation ideal and the
augmentation. -/
theorem augmentationSES_def :
    augmentationSES k G = ShortComplex.mk (augmentationι k G) (augmentation k G)
      (augmentationι_comp_augmentation k G) :=
  (rfl)

/-- The first term of the augmentation sequence is the augmentation ideal. -/
@[simp]
theorem augmentationSES_X₁ : (augmentationSES k G).X₁ = augmentationIdeal k G := (rfl)

/-- The middle term of the augmentation sequence is the left regular representation. -/
@[simp]
theorem augmentationSES_X₂ : (augmentationSES k G).X₂ = leftRegular k G := (rfl)

/-- The last term of the augmentation sequence is the trivial representation on `k`. -/
@[simp]
theorem augmentationSES_X₃ : (augmentationSES k G).X₃ = trivial k G k := (rfl)

/-- The augmentation sequence is short exact. -/
theorem augmentationSES_shortExact : (augmentationSES k G).ShortExact where
  exact := ShortComplex.kernelSequence_exact (augmentation k G)
  mono_f := augmentationι_mono k G
  epi_g := augmentation_epi k G

/-- The augmentation sequence stays short exact after restriction along any monoid homomorphism
`f : H →* G`. -/
theorem augmentationSES_res_shortExact {H : Type*} [Monoid H] (f : H →* G) :
    ((augmentationSES k G).map (resFunctor f)).ShortExact :=
  (shortExact_res f).mpr (augmentationSES_shortExact k G)

end Rep

namespace TauCeti.AugmentationIdeal

open _root_.Rep

variable (k G : Type u) [CommRing k] [Group G]

private theorem exact_augmentation :
    Function.Exact (augmentationι k G).hom (augmentation k G).hom := by
  have h := (augmentationSES_shortExact k G).exact.map (forget₂ (Rep k G) (ModuleCat k))
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h
  exact h

private theorem augmentation_single_sub (a : k) (g : G) :
    (augmentation k G).hom (MonoidAlgebra.single g a - MonoidAlgebra.single 1 a) = 0 := by
  rw [map_sub]
  simp

/-- The element of the augmentation ideal whose image in `k[G]` is `[g] a - [1] a`. -/
def singleSub (a : k) (g : G) : augmentationIdeal k G :=
  Classical.choose <| (exact_augmentation k G _).1 (augmentation_single_sub k G a g)

/-- The image of `singleSub a g` under the inclusion into `k[G]`. -/
@[simp]
theorem ι_singleSub (a : k) (g : G) :
    (augmentationι k G).hom (singleSub k G a g) =
      MonoidAlgebra.single g a - MonoidAlgebra.single 1 a :=
  Classical.choose_spec <| (exact_augmentation k G _).1 (augmentation_single_sub k G a g)

/-- The inclusion of the augmentation ideal into `k[G]` is injective. -/
theorem augmentationι_injective : Function.Injective (augmentationι k G).hom :=
  (Rep.mono_iff_injective _).1 inferInstance

/-- The action of `G` on an augmentation ideal element `[g] a - [1] a`. -/
theorem ρ_singleSub (a : k) (x y : G) :
    (augmentationIdeal k G).ρ x (singleSub k G a y) =
      singleSub k G a (x * y) - singleSub k G a x := by
  apply augmentationι_injective k G
  rw [hom_comm_apply, map_sub, ι_singleSub, ι_singleSub, ι_singleSub, map_sub]
  simp

/-- The augmentation ideal element `[1] a - [1] a` is zero. -/
@[simp]
theorem singleSub_one (a : k) : singleSub k G a (1 : G) = 0 := by
  apply augmentationι_injective k G
  rw [ι_singleSub, sub_self, map_zero]

end TauCeti.AugmentationIdeal

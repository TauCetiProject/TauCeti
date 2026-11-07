/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGlueing.Lifting

/-!
# Algebraizing a module model in formal gluing

Suppose `R → S` is faithfully flat and induces `R/I ≅ S/IS`, where a finite set `G` generates
`I`. Let `B` be an `S`-algebra, and let `P ⊆ B` be an `R`-submodule whose scalar extension to
`S` is `B`. To turn this module model into an algebra model, it suffices to check the unit
and multiplication after localization at each generator of `I`.

`Submodule.one_mem_of_formalGlueing` and `Submodule.mul_mem_of_formalGlueing` give the closure
proofs needed by `Submodule.toSubalgebra`, retaining its definitional carrier and membership API.
The local hypotheses are stated as membership in the image of the localized inclusion of `P`;
they can therefore be supplied by algebra models on the complementary principal opens, without
choosing ring structures on localized modules. The resulting algebra has the same underlying
module model, so its scalar extension is still `B`. This separates descent of algebra operations
from reconstruction of the underlying module.

The element-descent input is `IsBaseChange.mem_range_iff_locally_mem_range`, the abstract
base-change form of `TensorProduct.mem_range_mk_one_iff_locally_mem_range`.

## References

* The Stacks Project, Remark 15.91.20 (05EU), passage from formal module gluing to algebra
  structures. Here the underlying module model is given and the ring map is faithfully flat.
-/

public section

namespace Submodule

variable {R S B : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Ring B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  [Module.FaithfullyFlat R S] {G : Finset R}

/-- **Descent of the unit in formal gluing.** An `R`-submodule `P` of an `S`-algebra `B`
that base changes to `B` contains the unit if the unit belongs to the image of `P` after
localization at each generator of the defining ideal. -/
@[stacks 05EU "descending the unit on a given module model, for faithfully flat ring maps"]
theorem one_mem_of_formalGlueing (P : Submodule R B)
    (hP : IsBaseChange S P.subtype)
    (hI : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (G : Set R)).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map))
    (hone : ∀ g ∈ G, LocalizedModule.mkLinearMap (.powers g) B 1 ∈
      LinearMap.range (IsLocalizedModule.map (.powers g)
        (LocalizedModule.mkLinearMap (.powers g) P)
        (LocalizedModule.mkLinearMap (.powers g) B) P.subtype)) :
    (1 : B) ∈ P := by
  simpa only [Submodule.range_subtype] using
    (hP.mem_range_iff_locally_mem_range hI 1).mpr hone

/-- **Descent of multiplication in formal gluing.** An `R`-submodule `P` of an `S`-algebra `B`
that base changes to `B` is closed under multiplication if products of elements of `P` belong
to the image of `P` after localization at each generator of the defining ideal. No finiteness
or commutativity assumption on `B` is needed. -/
@[stacks 05EU "descending multiplication on a given module model, for faithfully flat ring maps"]
theorem mul_mem_of_formalGlueing (P : Submodule R B)
    (hP : IsBaseChange S P.subtype)
    (hI : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (G : Set R)).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map))
    (hmul : ∀ (x y : P) (g : R), g ∈ G →
      LocalizedModule.mkLinearMap (.powers g) B ((x : B) * y) ∈
        LinearMap.range (IsLocalizedModule.map (.powers g)
          (LocalizedModule.mkLinearMap (.powers g) P)
          (LocalizedModule.mkLinearMap (.powers g) B) P.subtype))
    (x y : B) (hx : x ∈ P) (hy : y ∈ P) : x * y ∈ P := by
  simpa only [Submodule.range_subtype] using
    (hP.mem_range_iff_locally_mem_range hI (x * y)).mpr (hmul ⟨x, hx⟩ ⟨y, hy⟩)

end Submodule

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGlueing.Lifting
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Algebraizing a module model in formal gluing

Suppose `R → S` is faithfully flat and induces `R/I ≅ S/IS`, where a finite set `G` generates
`I`. Let `B` be an `S`-algebra, and let `P ⊆ B` be an `R`-submodule whose scalar extension to
`S` is `B`. To turn this module model into an algebra model, it suffices to check the unit
and multiplication after localization at each generator of `I`.

`Submodule.existsUnique_subalgebra_of_formalGlueing` constructs the unique `R`-subalgebra
with underlying submodule `P`. The local hypotheses are stated as membership in the image
of the localized inclusion of `P`; they can therefore be supplied by algebra models on the
complementary principal opens, without choosing ring structures on localized modules.
The resulting algebra has the same underlying module model, so its scalar extension is still
`B`. This separates descent of algebra operations from reconstruction of the underlying module.

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

/-- **Descent of the unit and multiplication in formal gluing.** An `R`-submodule `P` of an
`S`-algebra `B` that base changes to `B` is the underlying module of a unique `R`-subalgebra
if the unit and products of elements of `P` belong to the image of `P` after localization at
each generator of the defining ideal. No finiteness or commutativity assumption on `B` is
needed. -/
@[stacks 05EU "algebraizing a given module model, for faithfully flat ring maps"]
theorem existsUnique_subalgebra_of_formalGlueing (P : Submodule R B)
    (hP : IsBaseChange S P.subtype)
    (hI : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (G : Set R)).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map))
    (hone : ∀ g ∈ G, LocalizedModule.mkLinearMap (.powers g) B 1 ∈
      LinearMap.range (IsLocalizedModule.map (.powers g)
        (LocalizedModule.mkLinearMap (.powers g) P)
        (LocalizedModule.mkLinearMap (.powers g) B) P.subtype))
    (hmul : ∀ (x y : P) (g : R), g ∈ G →
      LocalizedModule.mkLinearMap (.powers g) B ((x : B) * y) ∈
        LinearMap.range (IsLocalizedModule.map (.powers g)
          (LocalizedModule.mkLinearMap (.powers g) P)
          (LocalizedModule.mkLinearMap (.powers g) B) P.subtype)) :
    ∃! A : Subalgebra R B, A.toSubmodule = P := by
  have hmem (b : B) : b ∈ P ↔ ∀ g ∈ G,
      LocalizedModule.mkLinearMap (.powers g) B b ∈
        LinearMap.range (IsLocalizedModule.map (.powers g)
          (LocalizedModule.mkLinearMap (.powers g) P)
          (LocalizedModule.mkLinearMap (.powers g) B) P.subtype) := by
    simpa only [Submodule.range_subtype] using hP.mem_range_iff_locally_mem_range hI b
  have h1 : (1 : B) ∈ P := (hmem 1).mpr hone
  have hprod : ∀ x y : B, x ∈ P → y ∈ P → x * y ∈ P := by
    intro x y hx hy
    exact (hmem (x * y)).mpr (hmul ⟨x, hx⟩ ⟨y, hy⟩)
  refine ⟨P.toSubalgebra h1 hprod, P.toSubalgebra_toSubmodule h1 hprod, ?_⟩
  intro A hA
  exact Subalgebra.toSubmodule.injective (hA.trans (P.toSubalgebra_toSubmodule h1 hprod).symm)

end Submodule

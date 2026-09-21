/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

import TauCeti.Algebra.Homology.ShortComplex.ShortExact

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.RepresentationTheory.Induction.TrivialSubgroup

/-!
# The dimension-shifting sequences

For a representation `A` of a group `G`, the embedding `A ⟶ Coind_⊥^G A` into the representation
coinduced from the trivial subgroup and the projection `Ind_⊥^G A ⟶ A` from the induced
representation give short exact sequences

`0 ⟶ A ⟶ Coind_⊥^G A ⟶ dimensionShiftUp A ⟶ 0` and
`0 ⟶ dimensionShiftDown A ⟶ Ind_⊥^G A ⟶ A ⟶ 0`,

which stay short exact after restriction along any monoid homomorphism `H →* G`. The middle terms
have vanishing positive-degree cohomology, respectively homology, and for a finite group vanishing
Tate cohomology in every degree, so the connecting homomorphisms of these sequences shift degrees.
This is the *dimension shifting* of Milne, *Class Field Theory*, II 1.13 and 1.28; this file
provides the sequences themselves.

The constructions follow `ClassFieldTheory/Cohomology/Functors/UpDown.lean` in
`kbuzzard/ClassFieldTheory`, commit `ccc3323c6750abca25b49b35106f54eb3a398509`.

## Main definitions

* `Rep.dimensionShiftUp`, `Rep.dimensionShiftUpπ`, `Rep.dimensionShiftUpSES`: the cokernel of
  `A ⟶ Coind_⊥^G A` and its short complex.
* `Rep.dimensionShiftDown`, `Rep.dimensionShiftDownι`, `Rep.dimensionShiftDownSES`: the kernel of
  `Ind_⊥^G A ⟶ A` and its short complex.
* `Rep.dimensionShiftUpπIsCokernel`, `Rep.dimensionShiftDownιIsKernel`: their universal
  properties. The definitions are opaque, so consumers construct maps through these properties.

## Main statements

* `Rep.dimensionShiftUpSES_def`, `Rep.dimensionShiftDownSES_def`: the maps in the two short
  complexes.
* `Rep.dimensionShiftUpSES_shortExact`, `Rep.dimensionShiftUpSES_res_shortExact`: the upward
  sequence is short exact, also after restriction.
* `Rep.dimensionShiftDownSES_shortExact`, `Rep.dimensionShiftDownSES_res_shortExact`: the same for
  the downward sequence.

## References

* J. S. Milne, *Class Field Theory*, Chapter II, §1.
* K. S. Brown, *Cohomology of Groups*, Chapter III, §7.
-/

public noncomputable section

universe u

open CategoryTheory Limits

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

/-! ### The upward dimension shift -/

/-- The cokernel of the embedding `A ⟶ Coind_⊥^G A`, so that
`Hⁿ⁺¹(G, dimensionShiftUp A) ≅ Hⁿ⁺²(G, A)`. -/
def dimensionShiftUp (A : Rep k G) : Rep k G := cokernel (coindBotUnit A)

/-- The projection from the coinduced module onto `dimensionShiftUp A`. -/
def dimensionShiftUpπ (A : Rep k G) : coindBot k G A.V ⟶ dimensionShiftUp A :=
  cokernel.π (coindBotUnit A)

/-- The projection onto `dimensionShiftUp A` is an epimorphism. -/
instance dimensionShiftUpπ_epi (A : Rep k G) : Epi (dimensionShiftUpπ A) :=
  inferInstanceAs (Epi (cokernel.π (coindBotUnit A)))

/-- The embedding into the coinduced module followed by the dimension-shift projection is zero. -/
@[reassoc (attr := simp)]
theorem coindBotUnit_comp_dimensionShiftUpπ (A : Rep k G) :
    coindBotUnit A ≫ dimensionShiftUpπ A = 0 :=
  cokernel.condition (coindBotUnit A)

/-- The dimension-shift projection is a cokernel of the embedding into the coinduced module. -/
def dimensionShiftUpπIsCokernel (A : Rep k G) :
    IsColimit (CokernelCofork.ofπ (dimensionShiftUpπ A)
      (coindBotUnit_comp_dimensionShiftUpπ A)) :=
  cokernelIsCokernel (coindBotUnit A)

/-- The short complex `A ⟶ Coind_⊥^G A ⟶ dimensionShiftUp A`. -/
def dimensionShiftUpSES (A : Rep k G) : ShortComplex (Rep k G) :=
  ShortComplex.cokernelSequence (coindBotUnit A)

/-- The upward dimension-shifting short complex has maps the embedding into the coinduced module
and the dimension-shift projection. -/
theorem dimensionShiftUpSES_def (A : Rep k G) :
    dimensionShiftUpSES A = ShortComplex.mk (coindBotUnit A) (dimensionShiftUpπ A)
      (coindBotUnit_comp_dimensionShiftUpπ A) :=
  (rfl)

/-- The first object in the upward dimension-shifting short complex is `A`. -/
@[simp]
theorem dimensionShiftUpSES_X₁ (A : Rep k G) : (dimensionShiftUpSES A).X₁ = A :=
  (rfl)

/-- The middle object in the upward dimension-shifting short complex is coinduced from `⊥`. -/
@[simp]
theorem dimensionShiftUpSES_X₂ (A : Rep k G) :
    (dimensionShiftUpSES A).X₂ = coindBot k G A.V :=
  (rfl)

/-- The last object in the upward dimension-shifting short complex is `dimensionShiftUp A`. -/
@[simp]
theorem dimensionShiftUpSES_X₃ (A : Rep k G) :
    (dimensionShiftUpSES A).X₃ = dimensionShiftUp A :=
  (rfl)

/-- The short complex `A ⟶ Coind_⊥^G A ⟶ dimensionShiftUp A` is short exact. -/
theorem dimensionShiftUpSES_shortExact (A : Rep k G) : (dimensionShiftUpSES A).ShortExact :=
  TauCeti.cokernelSequence_shortExact (coindBotUnit A)

/-- The upward dimension-shifting short complex stays short exact after restriction along any
monoid homomorphism `f : H →* G`. -/
theorem dimensionShiftUpSES_res_shortExact (A : Rep k G) {H : Type*} [Monoid H] (f : H →* G) :
    ((dimensionShiftUpSES A).map (resFunctor f)).ShortExact :=
  (shortExact_res f).mpr (dimensionShiftUpSES_shortExact A)

/-! ### The downward dimension shift -/

/-- The kernel of the projection `Ind_⊥^G A ⟶ A`, so that
`Ĥⁿ(G, A) ≅ Ĥⁿ⁺¹(G, dimensionShiftDown A)` when `G` is finite. -/
def dimensionShiftDown (A : Rep k G) : Rep k G := kernel (indBotCounit A)

/-- The inclusion of `dimensionShiftDown A` into the induced module. -/
def dimensionShiftDownι (A : Rep k G) : dimensionShiftDown A ⟶ indBot k G A.V :=
  kernel.ι (indBotCounit A)

/-- The inclusion of `dimensionShiftDown A` is a monomorphism. -/
instance dimensionShiftDownι_mono (A : Rep k G) : Mono (dimensionShiftDownι A) :=
  inferInstanceAs (Mono (kernel.ι (indBotCounit A)))

/-- The dimension-shift inclusion followed by the projection onto `A` is zero. -/
@[reassoc (attr := simp)]
theorem dimensionShiftDownι_comp_indBotCounit (A : Rep k G) :
    dimensionShiftDownι A ≫ indBotCounit A = 0 :=
  kernel.condition (indBotCounit A)

/-- The dimension-shift inclusion is a kernel of the projection onto `A`. -/
def dimensionShiftDownιIsKernel (A : Rep k G) :
    IsLimit (KernelFork.ofι (dimensionShiftDownι A)
      (dimensionShiftDownι_comp_indBotCounit A)) :=
  kernelIsKernel (indBotCounit A)

/-- The short complex `dimensionShiftDown A ⟶ Ind_⊥^G A ⟶ A`. -/
def dimensionShiftDownSES (A : Rep k G) : ShortComplex (Rep k G) :=
  ShortComplex.kernelSequence (indBotCounit A)

/-- The downward dimension-shifting short complex has maps the dimension-shift inclusion and the
projection onto `A`. -/
theorem dimensionShiftDownSES_def (A : Rep k G) :
    dimensionShiftDownSES A = ShortComplex.mk (dimensionShiftDownι A) (indBotCounit A)
      (dimensionShiftDownι_comp_indBotCounit A) :=
  (rfl)

/-- The first object in the downward dimension-shifting short complex is `dimensionShiftDown A`. -/
@[simp]
theorem dimensionShiftDownSES_X₁ (A : Rep k G) :
    (dimensionShiftDownSES A).X₁ = dimensionShiftDown A :=
  (rfl)

/-- The middle object in the downward dimension-shifting short complex is induced from `⊥`. -/
@[simp]
theorem dimensionShiftDownSES_X₂ (A : Rep k G) :
    (dimensionShiftDownSES A).X₂ = indBot k G A.V :=
  (rfl)

/-- The last object in the downward dimension-shifting short complex is `A`. -/
@[simp]
theorem dimensionShiftDownSES_X₃ (A : Rep k G) : (dimensionShiftDownSES A).X₃ = A :=
  (rfl)

/-- The short complex `dimensionShiftDown A ⟶ Ind_⊥^G A ⟶ A` is short exact. -/
theorem dimensionShiftDownSES_shortExact (A : Rep k G) :
    (dimensionShiftDownSES A).ShortExact :=
  TauCeti.kernelSequence_shortExact (indBotCounit A)

/-- The downward dimension-shifting short complex stays short exact after restriction along any
monoid homomorphism `f : H →* G`. -/
theorem dimensionShiftDownSES_res_shortExact (A : Rep k G) {H : Type*} [Monoid H] (f : H →* G) :
    ((dimensionShiftDownSES A).map (resFunctor f)).ShortExact :=
  (shortExact_res f).mpr (dimensionShiftDownSES_shortExact A)

end Rep

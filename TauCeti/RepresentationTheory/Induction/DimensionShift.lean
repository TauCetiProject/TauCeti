/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.RepresentationTheory.Induction.TrivialSubgroup

/-!
# The dimension-shifting sequences

For a representation `A` of a group `G`, the embedding `A ⟶ Coind_⊥^G A` into the representation
coinduced from the trivial subgroup and the projection `Ind_⊥^G A ⟶ A` from the induced
representation give short exact sequences

`0 ⟶ A ⟶ Coind_⊥^G A ⟶ up A ⟶ 0` and `0 ⟶ down A ⟶ Ind_⊥^G A ⟶ A ⟶ 0`,

which stay short exact after restriction along any group homomorphism. The middle terms have
vanishing positive-degree cohomology, respectively homology, and for a finite group vanishing Tate
cohomology in every degree, so the connecting homomorphisms of these sequences shift degrees. This
is the *dimension shifting* of Milne, *Class Field Theory*, II 1.13 and 1.28; this file provides
the sequences themselves.

The constructions follow `ClassFieldTheory/Cohomology/Functors/UpDown.lean` in
`kbuzzard/ClassFieldTheory`, commit `ccc3323c6750abca25b49b35106f54eb3a398509`.

## Main definitions

* `Rep.up`, `Rep.upπ`, `Rep.upSES`: the cokernel of `A ⟶ Coind_⊥^G A` and its short complex.
* `Rep.down`, `Rep.downι`, `Rep.downSES`: the kernel of `Ind_⊥^G A ⟶ A` and its short complex.

## Main statements

* `Rep.upSES_shortExact`, `Rep.upSES_res_shortExact`: the sequence for `up` is short exact, also
  after restriction.
* `Rep.downSES_shortExact`, `Rep.downSES_res_shortExact`: the same for `down`.

## References

* J. S. Milne, *Class Field Theory*, Chapter II, §1.
* K. S. Brown, *Cohomology of Groups*, Chapter III, §7.
-/

public noncomputable section

universe u

open CategoryTheory Limits

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

/-! ### The cokernel `up` -/

/-- The cokernel of the embedding `A ⟶ Coind_⊥^G A`, so that `Hⁿ⁺¹(G, up A) ≅ Hⁿ⁺²(G, A)`. -/
def up (A : Rep k G) : Rep k G := cokernel (coindBotUnit A)

/-- The projection from the coinduced module onto `up A`. -/
def upπ (A : Rep k G) : coindBot k G A.V ⟶ up A := cokernel.π (coindBotUnit A)

/-- The projection onto `up A` is an epimorphism. -/
instance upπ_epi (A : Rep k G) : Epi (upπ A) :=
  inferInstanceAs (Epi (cokernel.π (coindBotUnit A)))

/-- The embedding into the coinduced module followed by the projection onto `up A` is zero. -/
@[reassoc (attr := simp)]
theorem coindBotUnit_comp_upπ (A : Rep k G) : coindBotUnit A ≫ upπ A = 0 :=
  cokernel.condition (coindBotUnit A)

/-- The projection onto `up A` is a cokernel of the embedding into the coinduced module. -/
def upπIsCokernel (A : Rep k G) :
    IsColimit (CokernelCofork.ofπ (upπ A) (coindBotUnit_comp_upπ A)) :=
  cokernelIsCokernel (coindBotUnit A)

/-- The short complex `A ⟶ Coind_⊥^G A ⟶ up A` defining `up A`. -/
def upSES (A : Rep k G) : ShortComplex (Rep k G) :=
  ShortComplex.cokernelSequence (coindBotUnit A)

/-- The short complex defining `up A` has maps the embedding into the coinduced module and the
projection onto `up A`. -/
theorem upSES_def (A : Rep k G) :
    upSES A = ShortComplex.mk (coindBotUnit A) (upπ A) (coindBotUnit_comp_upπ A) :=
  (rfl)

/-- The first term of the short complex defining `up A` is `A`. -/
@[simp]
theorem upSES_X₁ (A : Rep k G) : (upSES A).X₁ = A := (rfl)

/-- The middle term of the short complex defining `up A` is the coinduced module. -/
@[simp]
theorem upSES_X₂ (A : Rep k G) : (upSES A).X₂ = coindBot k G A.V := (rfl)

/-- The last term of the short complex defining `up A` is `up A`. -/
@[simp]
theorem upSES_X₃ (A : Rep k G) : (upSES A).X₃ = up A := (rfl)

/-- The short complex `A ⟶ Coind_⊥^G A ⟶ up A` is short exact. -/
theorem upSES_shortExact (A : Rep k G) : (upSES A).ShortExact where
  exact := ShortComplex.cokernelSequence_exact (coindBotUnit A)
  mono_f := inferInstanceAs (Mono (coindBotUnit A))
  epi_g := inferInstanceAs (Epi (upπ A))

/-- The short complex `A ⟶ Coind_⊥^G A ⟶ up A` stays short exact after restriction along any
monoid homomorphism `f : H →* G`. -/
theorem upSES_res_shortExact (A : Rep k G) {H : Type*} [Monoid H] (f : H →* G) :
    ((upSES A).map (resFunctor f)).ShortExact :=
  (shortExact_res f).mpr (upSES_shortExact A)

/-! ### The kernel `down` -/

/-- The kernel of the projection `Ind_⊥^G A ⟶ A`, so that `Ĥⁿ(G, A) ≅ Ĥⁿ⁺¹(G, down A)` when `G` is
finite. -/
def down (A : Rep k G) : Rep k G := kernel (indBotCounit A)

/-- The inclusion of `down A` into the induced module. -/
def downι (A : Rep k G) : down A ⟶ indBot k G A.V := kernel.ι (indBotCounit A)

/-- The inclusion of `down A` is a monomorphism. -/
instance downι_mono (A : Rep k G) : Mono (downι A) :=
  inferInstanceAs (Mono (kernel.ι (indBotCounit A)))

/-- The inclusion of `down A` followed by the projection onto `A` is zero. -/
@[reassoc (attr := simp)]
theorem downι_comp_indBotCounit (A : Rep k G) : downι A ≫ indBotCounit A = 0 :=
  kernel.condition (indBotCounit A)

/-- The inclusion of `down A` is a kernel of the projection onto `A`. -/
def downιIsKernel (A : Rep k G) :
    IsLimit (KernelFork.ofι (downι A) (downι_comp_indBotCounit A)) :=
  kernelIsKernel (indBotCounit A)

/-- The short complex `down A ⟶ Ind_⊥^G A ⟶ A` defining `down A`. -/
def downSES (A : Rep k G) : ShortComplex (Rep k G) :=
  ShortComplex.kernelSequence (indBotCounit A)

/-- The short complex defining `down A` has maps the inclusion of `down A` and the projection onto
`A`. -/
theorem downSES_def (A : Rep k G) :
    downSES A = ShortComplex.mk (downι A) (indBotCounit A) (downι_comp_indBotCounit A) :=
  (rfl)

/-- The first term of the short complex defining `down A` is `down A`. -/
@[simp]
theorem downSES_X₁ (A : Rep k G) : (downSES A).X₁ = down A := (rfl)

/-- The middle term of the short complex defining `down A` is the induced module. -/
@[simp]
theorem downSES_X₂ (A : Rep k G) : (downSES A).X₂ = indBot k G A.V := (rfl)

/-- The last term of the short complex defining `down A` is `A`. -/
@[simp]
theorem downSES_X₃ (A : Rep k G) : (downSES A).X₃ = A := (rfl)

/-- The short complex `down A ⟶ Ind_⊥^G A ⟶ A` is short exact. -/
theorem downSES_shortExact (A : Rep k G) : (downSES A).ShortExact where
  exact := ShortComplex.kernelSequence_exact (indBotCounit A)
  mono_f := inferInstanceAs (Mono (downι A))
  epi_g := inferInstanceAs (Epi (indBotCounit A))

/-- The short complex `down A ⟶ Ind_⊥^G A ⟶ A` stays short exact after restriction along any
monoid homomorphism `f : H →* G`. -/
theorem downSES_res_shortExact (A : Rep k G) {H : Type*} [Monoid H] (f : H →* G) :
    ((downSES A).map (resFunctor f)).ShortExact :=
  (shortExact_res f).mpr (downSES_shortExact A)

end Rep

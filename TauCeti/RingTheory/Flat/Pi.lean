/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import TauCeti.RingTheory.Coherent.Basic

import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.Flat.Tensor
import TauCeti.LinearAlgebra.TensorProduct.Pi
import TauCeti.RingTheory.Ideal.Operations

/-!
# Products of flat modules, and when they are faithfully flat

Mathlib knows that an arbitrary direct sum of flat modules is flat (`Module.Flat.directSum`), but
`∀ i, M i` is not definitionally a direct sum, so nothing fires for a product. Over a finite index
the two agree. Over a coherent ring, in particular over a noetherian ring, an *arbitrary* product
of flat modules is flat (Chase): flatness is tested on the inclusions `I → R` of finitely generated
ideals, these are finitely presented, and tensoring with a finitely presented module commutes with
arbitrary products (`TensorProduct.piRightHom_bijective_of_finitePresentation`), so `I ⊗ ∏ M i`
embeds in `∏ (I ⊗ M i)`, which embeds in `∏ M i`.

Mathlib defines `Module.FaithfullyFlat` as flatness plus `m • ⊤ ≠ ⊤` for every maximal ideal `m`,
so the criterion is about locating a single component that keeps `m` proper — the factorwise half
of that is `Ideal.smul_top_eq_top_of_surjective`, a general ideal-action fact with no flatness or
finiteness in it, which lives in `TauCeti/RingTheory/Ideal/Operations.lean`: a flat product is
faithfully flat as soon as **no maximal ideal expands in every factor at once**. Individually the
factors may all fail to be faithfully flat.

## Main results

* `Module.Flat.pi`: a finite product of flat modules is flat.
* `Module.Flat.prod`: the product `N × P` of two flat modules is flat.
* `Module.Flat.pi_of_isCoherentRing`: over a coherent ring, an arbitrary product of flat modules is
  flat.
* `Module.FaithfullyFlat.pi_of_exists_submodule_ne_top`: a flat product is faithfully flat as soon
  as every maximal ideal stays proper in *some* factor.
* `Module.FaithfullyFlat.pi_of_faithfullyFlat`: the special case of one distinguished faithfully
  flat factor.
* `Module.FaithfullyFlat.pi`: a flat *nonempty* product of faithfully flat modules is faithfully
  flat; the product is flat if the index is finite or the ring is coherent.

## Implementation notes

`Module.FaithfullyFlat.pi` asks `[Nonempty ι]`, and that is not slack: for `ι` empty the product
is the trivial module, in which `m • ⊤ = ⊤ = ⊥` for every `m`, so it is faithfully flat over no
nonzero ring at all — while `∀ i, FaithfullyFlat R (M i)` holds vacuously. Dropping the hypothesis
would make the instance false. Flatness has no such caveat: the trivial module is flat.

Either finiteness of the index or coherence of the ring is needed: by Chase's theorem a ring is
coherent exactly when every product of flat modules is flat, so over a non-coherent ring the
statement fails outright for a large enough index.

## References

* S. U. Chase, *Direct products of modules*, Trans. Amer. Math. Soc. 97 (1960), Theorem 2.1.
-/

public section

variable {R : Type*} {ι : Type*} {M : ι → Type*}

namespace Module

section Flat

variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- **A finite product of flat modules is flat.** Over a non-coherent ring the finiteness cannot be
dropped; over a coherent ring see `Module.Flat.pi_of_isCoherentRing`. -/
instance Flat.pi [Finite ι] [∀ i, Flat R (M i)] : Flat R (∀ i, M i) := by
  have := Fintype.ofFinite ι
  exact Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype R ι M).symm

/-- The product of two flat modules is flat. -/
instance Flat.prod {N P : Type*} [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]
    [Flat R N] [Flat R P] : Flat R (N × P) := by
  refine Flat.iff_lTensor_injectiveₛ.mpr fun Q _ _ Q' ↦ ?_
  have h : (TensorProduct.prodLeft R R N P Q).toLinearMap ∘ₗ Q'.subtype.lTensor (N × P) =
      (Q'.subtype.lTensor N).prodMap (Q'.subtype.lTensor P) ∘ₗ
        (TensorProduct.prodLeft R R N P Q').toLinearMap := by
    ext <;> simp
  -- Up to `prodLeft`, tensoring `Q' → Q` with `N × P` is the product of the two tensored maps.
  refine Function.Injective.of_comp (f := TensorProduct.prodLeft R R N P Q) ?_
  rw [← LinearEquiv.coe_coe, ← LinearMap.coe_comp, h, LinearMap.coe_comp]
  exact ((Flat.lTensor_preserves_injective_linearMap _ Q'.injective_subtype).prodMap
    (Flat.lTensor_preserves_injective_linearMap _ Q'.injective_subtype)).comp
      (LinearEquiv.injective _)

end Flat

section Coherent

variable [CommRing R] [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- **Chase's theorem: over a coherent ring, an arbitrary product of flat modules is flat.** This
covers every noetherian ring (`IsNoetherianRing.isCoherentRing`). -/
instance Flat.pi_of_isCoherentRing [TauCeti.IsCoherentRing R] [∀ i, Flat R (M i)] :
    Flat R (∀ i, M i) := by
  refine Flat.iff_rTensor_injective.mpr fun I hI ↦ ?_
  have : FinitePresentation R I := (TauCeti.isCoherentRing_iff_ideal_finitePresentation R).mp ‹_› hI
  -- Up to the injective comparison map, `I ⊗ ∏ M i → R ⊗ ∏ M i` is `∏ (I ⊗ M i) → ∏ (R ⊗ M i)`.
  refine Function.Injective.of_comp (f := TensorProduct.piRightHom R R R M) ?_
  rw [← LinearMap.coe_comp, TensorProduct.piRightHom_comp_rTensor, LinearMap.coe_comp,
    LinearMap.coe_piMap]
  exact (Function.Injective.piMap fun i ↦ Flat.rTensor_preserves_injective_linearMap _
    I.injective_subtype).comp
      (TensorProduct.piRightHom_bijective_of_finitePresentation R).injective

end Coherent

section FaithfullyFlat

variable [CommRing R] [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- **A flat product is faithfully flat as soon as no maximal ideal expands every factor at
once.** Each individual factor may fail to be faithfully flat; what is needed is that the failures
are not simultaneous. The product is flat when the index is finite (`Module.Flat.pi`) or the ring
is coherent (`Module.Flat.pi_of_isCoherentRing`). -/
theorem FaithfullyFlat.pi_of_exists_submodule_ne_top [Flat R (∀ i, M i)]
    (h : ∀ m : Ideal R, m.IsMaximal → ∃ i, m • (⊤ : Submodule R (M i)) ≠ ⊤) :
    FaithfullyFlat R (∀ i, M i) where
  submodule_ne_top m hm htop := (h m hm).elim fun i hi ↦
    hi (m.smul_top_eq_top_of_surjective (LinearMap.proj i) (Function.surjective_eval i) htop)

/-- **One faithfully flat factor carries a flat product.** This is the special case of
`FaithfullyFlat.pi_of_exists_submodule_ne_top` where one fixed index works for every maximal
ideal; when no single factor does, that criterion is the one to use. -/
theorem FaithfullyFlat.pi_of_faithfullyFlat [Flat R (∀ i, M i)] (j : ι)
    [FaithfullyFlat R (M j)] : FaithfullyFlat R (∀ i, M i) :=
  FaithfullyFlat.pi_of_exists_submodule_ne_top fun _ hm ↦
    ⟨j, FaithfullyFlat.submodule_ne_top hm⟩

/-- A flat **nonempty** product of faithfully flat modules is faithfully flat. The product is flat
when the index is finite (`Module.Flat.pi`) or the ring is coherent
(`Module.Flat.pi_of_isCoherentRing`). The nonemptiness hypothesis is essential; see the module
docstring. -/
instance FaithfullyFlat.pi [Nonempty ι] [∀ i, FaithfullyFlat R (M i)] [Flat R (∀ i, M i)] :
    FaithfullyFlat R (∀ i, M i) :=
  FaithfullyFlat.pi_of_faithfullyFlat (Classical.arbitrary ι)

end FaithfullyFlat

end Module

end

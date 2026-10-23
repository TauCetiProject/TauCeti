/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
public import Mathlib.RepresentationTheory.FDRep
public import Mathlib.RingTheory.Flat.CategoryTheory
public import TauCeti.CategoryTheory.Action.EssentiallySmall
public import TauCeti.CategoryTheory.GrothendieckGroup.Monoidal.Exact

/-!
# The Grothendieck ring of finite-dimensional representations

Let `G` be a monoid and `k` a field. Tensoring with a fixed finite-dimensional representation, on
either side, carries short exact sequences in `FDRep k G` to short exact sequences: the forgetful
functor to `k`-modules is faithful, exact and monoidal, and every `k`-module is flat. So the
canonical exact structure on the abelian category `FDRep k G` is monoidal, and its exact
Grothendieck group, the free abelian group on the classes `[V]` modulo `[V₂] = [V₁] + [V₃]` for
every short exact sequence `0 → V₁ → V₂ → V₃ → 0`, is a commutative ring with `[V] * [W] =
[V ⊗ W]` (`TauCeti.ExactK0.instCommRing`).

For a finite group this is the ring `R_k(G) = G₀(k[G])` of Serre, Part III, in every
characteristic. The comparison `TauCeti.ExactK0.fromSplitRingHom` from the split Grothendieck ring
`TauCeti.repRing k G` is a ring homomorphism whose underlying additive map is the surjection
`TauCeti.ExactK0.fromSplit`; it need not be injective when the characteristic of `k` divides the
order of `G`, since short exact sequences of representations then need not split.

## Main results

* `FDRep.shortExact_map_tensorLeft`, `FDRep.shortExact_map_tensorRight`: tensoring with a fixed
  representation preserves short exact sequences.
* `TauCeti.isMonoidal_abelian_fdRep`: the canonical exact structure on `FDRep k G` is monoidal, so
  its exact `K₀` is a commutative ring.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), §14.1.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v

variable {k : Type u} {G : Type v} [Field k] [Monoid G]

namespace FDRep

/-- **Tensoring on the left is exact.** Tensoring with a fixed finite-dimensional representation
on the left carries a short exact sequence of representations to a short exact sequence. -/
theorem shortExact_map_tensorLeft {S : ShortComplex (FDRep k G)} (hS : S.ShortExact)
    (V : FDRep k G) : (S.map (tensorLeft V)).ShortExact := by
  -- Reflect along the faithful, exact, monoidal forgetful functor to `k`-modules, where
  -- tensoring with the flat module `V` is exact.
  let F : FDRep k G ⥤ ModuleCat k :=
    Action.forget (FGModuleCat k) G ⋙ forget₂ (FGModuleCat k) (ModuleCat k)
  refine ShortExact.reflects_shortExact_of_faithful F ?_
  refine ShortComplex.shortExact_of_iso (S.mapNatIso (Functor.Monoidal.commTensorLeft F V)) ?_
  rw [ShortComplex.map_comp]
  exact (hS.map_of_exact F).map_of_exact (tensorLeft (F.obj V))

/-- **Tensoring on the right is exact.** Tensoring with a fixed finite-dimensional representation
on the right carries a short exact sequence of representations to a short exact sequence. -/
theorem shortExact_map_tensorRight {S : ShortComplex (FDRep k G)} (hS : S.ShortExact)
    (V : FDRep k G) : (S.map (tensorRight V)).ShortExact :=
  ShortComplex.shortExact_of_iso (S.mapNatIso (BraidedCategory.tensorLeftIsoTensorRight V))
    (shortExact_map_tensorLeft hS V)

end FDRep

namespace TauCeti

/-- **The tensor product of finite-dimensional representations is biexact.** The canonical exact
structure on `FDRep k G` is monoidal, so its exact Grothendieck group is a commutative ring under
the tensor product. -/
instance isMonoidal_abelian_fdRep : (ExactStructure.abelian (FDRep k G)).IsMonoidal where
  isConflationExact_tensorLeft V := ⟨fun hS => (ExactStructure.abelian_conflation _).2
    (FDRep.shortExact_map_tensorLeft ((ExactStructure.abelian_conflation _).1 hS) V)⟩
  isConflationExact_tensorRight V := ⟨fun hS => (ExactStructure.abelian_conflation _).2
    (FDRep.shortExact_map_tensorRight ((ExactStructure.abelian_conflation _).1 hS) V)⟩

noncomputable example : CommRing (ExactK0.{max u v} (ExactStructure.abelian (FDRep k G))) :=
  inferInstance

end TauCeti

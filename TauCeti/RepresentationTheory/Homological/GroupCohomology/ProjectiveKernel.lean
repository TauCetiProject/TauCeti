/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Coinduced

/-!
# Cohomology maps with projective kernels

For a finite group `G`, a short exact sequence `0 → P → M → N → 0` with `P` projective over
`k[G]` induces an isomorphism `Hⁿ(G, M) ≅ Hⁿ(G, N)` in every positive degree. No finiteness or
projectivity assumption is needed on `M` or `N`.

In particular, a surjection from a relation module onto a completed multiplicative module with
kernel `ℤ_p[G]` induces an isomorphism on `H²`. This comparison preserves the coefficient map
itself, which is essential when comparing the classes of group extensions.

## Main results

* `TauCeti.groupCohomology.isZero_succ_of_projective`: projective representations of finite
  groups have vanishing positive-degree cohomology.
* `TauCeti.groupCohomology.isIso_map_of_surjective_of_projective_ker`: a surjective coefficient
  map with projective kernel induces an isomorphism in every positive degree.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  proof of (7.4.1).
* K. S. Brown, *Cohomology of Groups*, Chapter III, §6.
-/

public section

namespace TauCeti.groupCohomology

open CategoryTheory Limits _root_.Rep _root_.groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-- A projective representation of a finite group has vanishing cohomology in every positive
degree. -/
theorem isZero_succ_of_projective (A : Rep k G) [Projective A] (n : ℕ) :
    IsZero (groupCohomology A (n + 1)) := by
  -- Projectivity splits the epimorphism from the representation induced from the trivial group.
  have h := (Retract.mk _ _ (Projective.factorThru_comp (𝟙 A) (indBotCounit A))).map
    (_root_.groupCohomology.functor k G (n + 1))
  have hzero := (isZero_coindBot_succ A.V n).of_iso
    ((_root_.groupCohomology.functor k G (n + 1)).mapIso (indBotIsoCoindBot A.V))
  rw [IsZero.iff_id_eq_zero]
  exact h.retract.symm.trans (by
    rw [hzero.eq_zero_of_tgt h.i, zero_comp]
    rfl)

/-- A surjective `k[G]`-linear map with projective kernel induces an isomorphism in every
positive degree of group cohomology. The coefficient representations are the canonical ones
attached to the two `k[G]`-modules. -/
theorem isIso_map_of_surjective_of_projective_ker {M N : Type u}
    [AddCommGroup M] [Module (MonoidAlgebra k G) M]
    [AddCommGroup N] [Module (MonoidAlgebra k G) N]
    (f : M →ₗ[MonoidAlgebra k G] N) (hf : Function.Surjective f)
    [Module.Projective (MonoidAlgebra k G) (LinearMap.ker f)] (n : ℕ) :
    IsIso ((_root_.groupCohomology.functor k G (n + 1)).map
      (ofModuleMonoidAlgebra.map (ModuleCat.ofHom f))) := by
  have hS := (ModuleCat.shortComplex_shortExact
    (ModuleCat.shortComplexOfCompEqZero (LinearMap.ker f).subtype f
      f.exact_subtype_ker_map.linearMap_comp_eq_zero)
    f.exact_subtype_ker_map (LinearMap.ker f).injective_subtype hf).map_of_exact
      ofModuleMonoidAlgebra
  have hP : Projective (ofModuleMonoidAlgebra.obj
      (ModuleCat.of (MonoidAlgebra k G) (LinearMap.ker f))) :=
    inferInstance
  exact isIso_map_of_shortExact_of_isZero hS (n + 1)
    (@isZero_succ_of_projective k G _ _ _ _ hP n)
    (@isZero_succ_of_projective k G _ _ _ _ hP (n + 1))

end TauCeti.groupCohomology

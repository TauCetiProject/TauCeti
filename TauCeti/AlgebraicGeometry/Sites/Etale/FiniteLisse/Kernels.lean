/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Etale.ModuleSheaf
public import TauCeti.CategoryTheory.Sites.LocallyConstant.Module

/-!
# Kernels and cokernels of finite lisse étale sheaves

Let `S` be a scheme and `Λ` a ring. This file shows that finite lisse étale sheaves of
`Λ`-modules on `S` (`CategoryTheory.Sheaf.IsFiniteLisse`) are closed under cokernels, and under
kernels when `Λ` is Noetherian (for instance finite):

* `CategoryTheory.Sheaf.IsFiniteLisse.kernel`: the kernel of a morphism of finite lisse sheaves
  is finite lisse when `Λ` is Noetherian.
* `CategoryTheory.Sheaf.IsFiniteLisse.cokernel`: the cokernel of a morphism of finite lisse
  sheaves is finite lisse.

These are the étale cases of the statements for locally constant sheaves of finite type on a site
(`CategoryTheory.Sheaf.IsLocallyConstantIn.kernel`,
`CategoryTheory.Sheaf.IsLocallyConstantIn.cokernel`).
The cokernel statement uses that restricting étale sheaves to `Over U` preserves cokernels: it is
a left adjoint (`AlgebraicGeometry.Scheme.Etale.isLeftAdjoint_overPullback`), since up to the
equivalence `AlgebraicGeometry.Scheme.Etale.overSheafEquiv` it is the inverse image along the
étale morphism `U ⟶ S`.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IX, §2.
* The Stacks Project, Section 59.64, Locally constant sheaves.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry Scheme

namespace CategoryTheory.Sheaf

variable {S : Scheme.{u}} {Λ : Type u} [Ring Λ]

/-- **Kernels of finite lisse sheaves.** Over a Noetherian ring `Λ`, the kernel of a morphism of
finite lisse étale sheaves of `Λ`-modules is finite lisse. -/
theorem IsFiniteLisse.kernel [IsNoetherianRing Λ]
    {F G : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)} (hF : F.IsFiniteLisse)
    (hG : G.IsFiniteLisse) (φ : F ⟶ G) : (kernel φ).IsFiniteLisse :=
  IsLocallyConstantIn.kernel hF hG φ

/-- **Cokernels of finite lisse sheaves.** The cokernel of a morphism of finite lisse étale
sheaves of `Λ`-modules is finite lisse. -/
theorem IsFiniteLisse.cokernel {F G : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)}
    (hF : F.IsFiniteLisse) (hG : G.IsFiniteLisse) (φ : F ⟶ G) : (cokernel φ).IsFiniteLisse :=
  IsLocallyConstantIn.cokernel hF hG φ

end CategoryTheory.Sheaf

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Algebra.RegularFunctions
public import TauCeti.AlgebraicGeometry.RelativeSpec.Functor
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated

/-!
# Quasi-coherent direct-image algebras

For a quasi-compact quasi-separated morphism `f : X ⟶ S`, the actual direct image
`f_* 𝒪_X`, with its canonical algebra structure, is a quasi-coherent `𝒪_S`-algebra.
This bundle supplies the regular-function algebra to constructions requiring quasi-coherence,
such as algebra pullback and relative spectra.

## References

* The Stacks Project, Lemma 26.24.1 (01LC), quasi-coherence of direct images.
-/

public section

open CategoryTheory MonoidalCategory
open TauCeti.AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- The quasi-coherent direct-image algebra of a quasi-compact quasi-separated morphism,
carried by the actual direct image of its structure sheaf. -/
def pushforwardAlgebra (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    QuasicoherentAlgebra S :=
  ⟨f.pushforwardStructureAlgebra,
    inferInstanceAs (((Scheme.Modules.pushforward f).obj (𝟙_ X.Modules)).IsQuasicoherent)⟩

/-- Forgetting quasi-coherence recovers the canonical direct-image structure algebra. -/
@[simp]
lemma pushforwardAlgebra_obj (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    f.pushforwardAlgebra.obj = f.pushforwardStructureAlgebra :=
  (rfl)

end AlgebraicGeometry.Scheme.Hom

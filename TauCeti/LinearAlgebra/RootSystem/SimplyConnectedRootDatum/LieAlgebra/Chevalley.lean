/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.Chevalley.BaseSquare
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Killing

/-!
# Chevalley systems for the pinned rational Lie algebra

The signed Geck involution exchanges the simple raising and lowering generators of the pinned
Lie-algebra basis. The generic base-square propagation theorem therefore constructs a Chevalley
system over `ℚ` itself; no extension to an algebraic closure is needed for this choice. This does
not establish nondegeneracy of the rational Killing form, which is an independent input supplied
by the imported Killing-form module.

## Main results

* `TauCeti.DynkinType.instIsTriangularizableLieAlgebra`: the distinguished Cartan acts
  triangularizably on the pinned rational Lie algebra.
* `TauCeti.DynkinType.exists_isChevalleySystem`: the signed Geck involution admits a compatible
  Chevalley system over `ℚ` whose simple root vectors are the numbered generators `eᵢ` and `fᵢ`.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* R. W. Carter, *Simple Groups of Lie Type*, §4.2.
-/

public section

namespace TauCeti.DynkinType

open _root_.LieAlgebra LieModule

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-- The Cartan action on the pinned rational Lie algebra is triangularizable over `ℚ`. -/
instance instIsTriangularizableLieAlgebra :
    IsTriangularizable ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht) :=
  (t.lieBasis ht).isTriangularizable

/-- **The pinned rational Lie algebra has a Chevalley system pinned to its Chevalley generators.**
There is a Chevalley system for the signed Geck involution whose root vectors at the `i`-th simple
root and its negative are the Bourbaki-numbered generators `eᵢ` and `fᵢ` of
`TauCeti.DynkinType.lieBasis`. These equations fix it only up to signs at the non-simple roots
(`TauCeti.IsChevalleySystem.eq_or_eq_neg`). -/
theorem exists_isChevalleySystem :
    ∃ x : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht) → t.lieAlgebra ht,
      TauCeti.IsChevalleySystem (t.chevalleyInvolution ht) x ∧
        ∀ i : Fin t.rank, x ((t.lieBasis ht).baseSupportEquiv i) = (t.lieBasis ht).e i ∧
          x (-(t.lieBasis ht).baseSupportEquiv i) = (t.lieBasis ht).f i :=
  (TauCeti.exists_isSl2System ℚ (t.cartanSubalgebra ht)).elim fun _ hx =>
    (hx.exists_isChevalleySystem_of_lieBasis (t.chevalleyInvolution ht)
      (fun y hy => t.chevalleyInvolution_cartan ht ⟨y, hy⟩) (t.lieBasis ht)
      (t.chevalleyInvolution_lieBasis_e ht)).elim fun _ hy =>
    hy.exists_isChevalleySystem_simple_eq_lieBasis (t.lieBasis ht)
      (t.chevalleyInvolution_lieBasis_e ht)

end

end TauCeti.DynkinType

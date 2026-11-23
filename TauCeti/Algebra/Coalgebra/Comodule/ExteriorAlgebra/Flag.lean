/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.ExteriorAlgebra.Power
public import TauCeti.Algebra.Coalgebra.Comodule.TensorProduct
public import TauCeti.Algebra.Coalgebra.Comodule.Transport
public import TauCeti.LinearAlgebra.ExteriorPower.Flag.Basic

/-!
# Exterior flag comodules

For a right comodule `M` over a commutative bialgebra `H`, each exterior power `⋀[R]^i M` is a
right `H`-comodule (`TauCeti.Comodule.exteriorPower`). Transporting tensor products recursively
along `flagSpaceZeroEquiv` and `flagSpaceSuccEquiv` equips `exteriorPower.FlagSpace R M d` with
the right `H`-comodule structure `TauCeti.Comodule.exteriorFlag`.

## Main definitions

* `TauCeti.Comodule.exteriorFlag`: the `H`-comodule structure on `exteriorPower.FlagSpace R M d`.

## Main results

* `TauCeti.Comodule.exteriorFlag_zero` and `TauCeti.Comodule.exteriorFlag_succ`: recursive
  unfolding equations for `TauCeti.Comodule.exteriorFlag`.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

variable (R H M : Type*) [CommRing R] [CommSemiring H] [Bialgebra R H]
  [AddCommGroup M] [Module R M] [Comodule R H M]

/-- The right `H`-comodule structure on `exteriorPower.FlagSpace R M d`, built recursively from
`Comodule.exteriorPower` and `Comodule.tensor` via `Comodule.Transport`. Select it explicitly as a
local instance. -/
@[implicit_reducible]
noncomputable def exteriorFlag : (d : ℕ) → Comodule R H (exteriorPower.FlagSpace R M d)
  | 0 =>
      let _ : Comodule R H (⋀[R]^0 M) := exteriorPower R H M 0
      Transport (exteriorPower.flagSpaceZeroEquiv R M).symm
  | r + 1 =>
      let _ : Comodule R H (exteriorPower.FlagSpace R M r) := exteriorFlag r
      let _ : Comodule R H (⋀[R]^(r + 1) M) := exteriorPower R H M (r + 1)
      let _ : Comodule R H (exteriorPower.FlagSpace R M r ⊗[R] ⋀[R]^(r + 1) M) :=
        tensor R H (exteriorPower.FlagSpace R M r) (⋀[R]^(r + 1) M)
      Transport (exteriorPower.flagSpaceSuccEquiv R M r).symm

/-- Base-case unfolding of `exteriorFlag` in degree `0`. -/
theorem exteriorFlag_zero :
    exteriorFlag R H M 0 =
      (letI : Comodule R H (⋀[R]^0 M) := exteriorPower R H M 0
       Transport (exteriorPower.flagSpaceZeroEquiv R M).symm) :=
  (rfl)

/-- Recursive unfolding of `exteriorFlag` in degree `r + 1`. -/
theorem exteriorFlag_succ (r : ℕ) :
    exteriorFlag R H M (r + 1) =
      (letI : Comodule R H (exteriorPower.FlagSpace R M r) := exteriorFlag R H M r
       letI : Comodule R H (⋀[R]^(r + 1) M) := exteriorPower R H M (r + 1)
       letI : Comodule R H (exteriorPower.FlagSpace R M r ⊗[R] ⋀[R]^(r + 1) M) :=
         tensor R H (exteriorPower.FlagSpace R M r) (⋀[R]^(r + 1) M)
       Transport (exteriorPower.flagSpaceSuccEquiv R M r).symm) :=
  (rfl)

end TauCeti.Comodule

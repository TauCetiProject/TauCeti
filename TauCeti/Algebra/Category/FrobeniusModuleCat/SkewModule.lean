/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FrobeniusModuleCat.Basic
public import TauCeti.Algebra.OreExtension.SkewModule

/-!
# Frobenius modules as modules over the skew polynomial ring

Let `M` be a linearized Frobenius module over `(S, σ)`, with `σ`-semilinear Frobenius `F`. The
skew polynomial ring `S{F} = S[F; σ]`, with `F * a = σ a * F`, is the Ore extension
`TauCeti.OreExtension σ.toIntAlgHom 0`. Letting `F` act by the Frobenius makes `M` a left
`S{F}`-module.

## Main definitions

* `TauCeti.FrobeniusModuleCat.skewFrobenius`: the Frobenius, as a semilinear map over the twist
  of `S{F}`.
* `TauCeti.FrobeniusModuleCat.toSkewModuleCat`: a linearized Frobenius module as a left module
  over the skew polynomial ring `S{F}`.

## Main results

* `TauCeti.FrobeniusModuleCat.X_smul_of` and `TauCeti.FrobeniusModuleCat.X_sub_one_smul_of`: `F`
  acts on `M.toSkewModuleCat` by the Frobenius, and `F - 1` by `F - 1`.
-/

public section

noncomputable section

universe u

namespace TauCeti.FrobeniusModuleCat

open OreExtension

variable {S : Type u} [CommRing S] {σ : S →+* S} (M : FrobeniusModuleCat σ)

/-- The Frobenius of `M`, as a semilinear map over the ring endomorphism underlying
`σ.toIntAlgHom`, the twist of the skew polynomial ring `S{F}`. -/
def skewFrobenius : M.carrier →ₛₗ[(σ.toIntAlgHom : S →+* S)] M.carrier :=
  M.frobenius

@[simp]
theorem skewFrobenius_apply (m : M.carrier) : M.skewFrobenius m = M.frobenius m :=
  (rfl)

/-- A linearized Frobenius module as a left module over the skew polynomial ring
`S{F} = S[F; σ]`, in which `F` acts by the Frobenius. -/
abbrev toSkewModuleCat : ModuleCat.{u} (OreExtension σ.toIntAlgHom 0) :=
  ModuleCat.of _ (SkewModule M.skewFrobenius)

/-- `F` acts on `M.toSkewModuleCat` by the Frobenius of `M`. -/
theorem X_smul_of (m : M.carrier) :
    (X : OreExtension σ.toIntAlgHom 0) • SkewModule.of M.skewFrobenius m =
      SkewModule.of M.skewFrobenius (M.frobenius m) :=
  SkewModule.X_smul_of _ m

/-- `F - 1` acts on `M.toSkewModuleCat` by `F - 1` on `M`. -/
theorem X_sub_one_smul_of (m : M.carrier) :
    (X - 1 : OreExtension σ.toIntAlgHom 0) • SkewModule.of M.skewFrobenius m =
      SkewModule.of M.skewFrobenius (M.frobenius m - m) :=
  SkewModule.X_sub_one_smul_of _ m

end TauCeti.FrobeniusModuleCat

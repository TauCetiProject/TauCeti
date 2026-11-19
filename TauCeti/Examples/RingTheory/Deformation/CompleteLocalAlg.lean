/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import TauCeti.RingTheory.Deformation.CompleteLocalAlg

/-!
# Checks for the complete local coefficient category

The `p`-adic integers `ℤ_[p]`, reduced modulo `p`, form an object of the complete local coefficient
category over `ℤ` with residue field `𝔽_p`, but not of the Artinian coefficient category: the
chain of ideals `p ^ n ℤ_[p]` does not stabilise, so a definition of `\hat{C}_Λ` that also imposed
the Artinian condition would exclude it. Its truncations are the quotients `ℤ_[p] ⧸ 𝔪 ^ (n + 1)`,
and level `0` reduces to the residue field.
-/

public section

open CategoryTheory IsLocalRing

namespace TauCeti.Examples

open Deformation CompleteLocalAlg

variable (p : ℕ) [Fact p.Prime]

/-- `ℤ_[p]` with its reduction modulo `p` is an object of `\hat{C}_ℤ` with residue field `𝔽_p`. -/
example : IsCompleteLocalAug ℤ (ZMod p)
    (Over.mk (CommAlgCat.ofHom (PadicInt.toZMod (p := p)).toIntAlgHom)) :=
  ⟨(inferInstance : IsNoetherianRing ℤ_[p]), (inferInstance : IsLocalRing ℤ_[p]),
    (inferInstance : IsAdicComplete (maximalIdeal ℤ_[p]) ℤ_[p]), ZMod.ringHom_surjective _⟩

/-- `ℤ_[p]` with its reduction modulo `p` is not an object of `C_ℤ`: an Artinian reduced local ring
is a field, while `p` is a nonzero nonunit of `ℤ_[p]`. -/
example : ¬ IsArtinLocalAug ℤ (ZMod p)
    (Over.mk (CommAlgCat.ofHom (PadicInt.toZMod (p := p)).toIntAlgHom)) := fun h ↦ by
  have : IsArtinianRing ℤ_[p] := h.isArtinianRing
  obtain ⟨q, hq⟩ := (IsArtinianRing.isField_of_isReduced_of_isLocalRing ℤ_[p]).mul_inv_cancel
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  exact PadicInt.p_nonunit (IsUnit.of_mul_eq_one q hq)

/-- The truncations of `ℤ_[p]` are its quotients by the powers `𝔪 ^ (n + 1)` of its maximal ideal,
and their augmentations reduce modulo `p`. -/
example (n : ℕ) (a : ℤ_[p]) :
    ((mk' ℤ_[p] (PadicInt.toZMod (p := p)).toIntAlgHom (ZMod.ringHom_surjective _)).truncation
      n).augmentation (Ideal.Quotient.mk (maximalIdeal ℤ_[p] ^ (n + 1)) a) = PadicInt.toZMod a :=
  (augmentation_truncation_mk
    (mk' ℤ_[p] (PadicInt.toZMod (p := p)).toIntAlgHom (ZMod.ringHom_surjective _)) n a).trans
    (DFunLike.congr_fun (augmentation_mk' ℤ_[p] _ _) a)

end TauCeti.Examples

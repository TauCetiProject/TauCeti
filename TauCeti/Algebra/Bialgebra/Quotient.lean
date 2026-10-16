/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Quotient

/-!
# The universal property of a bialgebra quotient

For a two-sided ideal `J` of an `R`-bialgebra `H` whose underlying `R`-submodule is a coideal,
Mathlib equips the quotient ring `H ⧸ J` with the structure of an `R`-bialgebra, descending the
comultiplication and counit from `H` (see `Mathlib.RingTheory.Bialgebra.Quotient`). This file
supplies the matching **universal property** that Mathlib lacks: `Bialgebra.Quotient.liftBialgHom`,
the unique bialgebra morphism `H ⧸ J →ₐc[R] K` induced from a bialgebra morphism `H →ₐc[R] K` which
kills `J`.

The construction uses only the bialgebra-quotient structure — a two-sided ideal `J` that is a
coideal — so neither an antipode nor a Hopf-algebra structure is required. For the underlying ideal
of a `TauCeti.HopfIdeal`, use `Bialgebra.Quotient.liftBialgHom I.toIdeal` directly.

## Main definitions

* `Bialgebra.Quotient.liftBialgHom`: the bialgebra morphism `H ⧸ J →ₐc[R] K` induced from a
  bialgebra morphism `f : H →ₐc[R] K` which kills the two-sided coideal `J`, together with its
  computation lemmas (`liftBialgHom_mk`, `liftBialgHom_comp_mkBialgHom`) and its uniqueness
  characterization (`liftBialgHom_unique`).

## References

The construction descends an algebra homomorphism through the algebra quotient
`Ideal.Quotient.liftₐ` and upgrades it to a bialgebra morphism via `BialgHom.ofAlgHom`, on top of
Mathlib's quotient bialgebra machinery (`Mathlib.RingTheory.Bialgebra.Quotient`).
-/

public section

namespace Bialgebra.Quotient

variable {R H : Type*} [CommRing R] [Ring H] [Bialgebra R H]
variable (J : Ideal H) [J.IsTwoSided]
variable {K : Type*} [Semiring K] [Bialgebra R K]

variable [(J.restrictScalars R).IsCoideal]

/-- The algebra homomorphism underlying the quotient bialgebra morphism is the quotient map. -/
@[simp]
theorem mkBialgHom_toAlgHom :
    (mkBialgHom (R := R) J).toAlgHom = Ideal.Quotient.mkₐ R J := rfl

/-- A bialgebra morphism out of `H` which kills a two-sided coideal `J` factors through the
quotient bialgebra `H ⧸ J`. -/
noncomputable def liftBialgHom (f : H →ₐc[R] K)
    (hf : J ≤ RingHom.ker f.toAlgHom.toRingHom) : H ⧸ J →ₐc[R] K :=
  BialgHom.ofAlgHom
    (Ideal.Quotient.liftₐ J f.toAlgHom
      fun _ ha ↦ (RingHom.mem_ker (f := f.toAlgHom.toRingHom)).mp (hf ha))
    (by
      apply Ideal.Quotient.algHom_ext R
      simp only [AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp]
      simpa only [mkBialgHom_toAlgHom] using
        f.counitAlgHom_comp.trans (mkBialgHom (R := R) J).counitAlgHom_comp.symm)
    (by
      apply Ideal.Quotient.algHom_ext R
      simp only [AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp]
      rw [← mkBialgHom_toAlgHom J, ← (mkBialgHom (R := R) J).map_comp_comulAlgHom]
      rw [← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp]
      simp only [mkBialgHom_toAlgHom, Ideal.Quotient.liftₐ_comp]
      exact f.map_comp_comulAlgHom)

/-- The quotient lift, evaluated on a quotient class. -/
@[simp]
theorem liftBialgHom_mk (f : H →ₐc[R] K)
    (hf : J ≤ RingHom.ker f.toAlgHom.toRingHom) (h : H) :
    liftBialgHom J f hf (Ideal.Quotient.mk J h) = f h := by
  rfl

/-- The quotient lift composed with the quotient map is the original bialgebra morphism. -/
@[simp]
theorem liftBialgHom_comp_mkBialgHom (f : H →ₐc[R] K)
    (hf : J ≤ RingHom.ker f.toAlgHom.toRingHom) :
    (liftBialgHom J f hf).comp (Bialgebra.Quotient.mkBialgHom J) = f := by
  ext h
  rw [BialgHom.comp_apply, Bialgebra.Quotient.mkBialgHom_apply, liftBialgHom_mk]

/-- A bialgebra morphism out of the quotient is determined by its precomposition with the
quotient map. -/
theorem liftBialgHom_unique (f : H →ₐc[R] K)
    (hf : J ≤ RingHom.ker f.toAlgHom.toRingHom) (g : H ⧸ J →ₐc[R] K)
    (hg : g.comp (Bialgebra.Quotient.mkBialgHom J) = f) :
    g = liftBialgHom J f hf := by
  ext q
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective R J q
  simpa only [BialgHom.comp_apply, Bialgebra.Quotient.mkBialgHom_apply,
    Ideal.Quotient.mkₐ_eq_mk, liftBialgHom_mk] using BialgHom.congr_fun hg h

end Bialgebra.Quotient

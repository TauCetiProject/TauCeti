/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import TauCeti.FieldTheory.Galois.Restriction

-- Roadmap source: `TauCetiRoadmap/NumberFieldArithmetic/README.md` @ `fa4d0309ae1d`, Layer 2.7,
-- the canonical element at a ramified real place, whose normal-tower restriction these general
-- facts serve. The credit sits outside the module docstring deliberately: the docstring
-- documents the mathematics.

/-!
# Infinite places in a normal tower

For a tower `K ⊆ F ⊆ L` with `F / K` normal, restriction of automorphisms along
`AlgEquiv.restrictNormalHom` is compatible with the Galois action on infinite places: moving a
place of `L` by `σ` and then inducing a place of `F` gives the same place as inducing first and
then moving by the restricted automorphism.

Two consequences of that compatibility are recorded here too. A place of `F` induced by a place
of `L` ramified over `K` is itself ramified over `K` as soon as it stays complex, because both
places lie over the same place of `K`. And an automorphism restricting trivially to `F` is
itself trivial whenever it fixes a place that is unramified over `F`, because such a place has
trivial stabilizer in `Gal(L/F)`.

Nothing here mentions complex conjugation: these are general facts about the action on places,
used by `TauCeti/NumberTheory/NumberField/ComplexConjugation.lean`.

## Main results

* `TauCeti.NumberField.restrictNormalHom_smul_comap`: the action is equivariant along the tower.
* `TauCeti.NumberField.isRamified_comap_of_isComplex`: a complex induced place is itself ramified.
* `TauCeti.NumberField.eq_one_of_restrictNormalHom_eq_one`: an automorphism restricting trivially
  to `F` and fixing a place unramified over `F` is the identity.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter III, §3.
-/

public section

open NumberField NumberField.InfinitePlace

namespace TauCeti.NumberField

variable (K : Type*) [Field K] {L : Type*} [Field L] [Algebra K L]
  {F : Type*} [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]

/-- **The Galois action on infinite places is equivariant along a normal tower.** Restricting `σ`
to `F` and then moving the place `w` induces on `F` gives the same place as moving `w` by `σ` and
inducing afterwards. -/
theorem restrictNormalHom_smul_comap [Normal K F] (σ : L ≃ₐ[K] L) (w : InfinitePlace L) :
    AlgEquiv.restrictNormalHom F σ • w.comap (algebraMap F L)
      = (σ • w).comap (algebraMap F L) := by
  have bridge : ∀ x : F, algebraMap F L ((AlgEquiv.restrictNormalHom F σ).symm x)
      = σ.symm (algebraMap F L x) := fun x => by
    -- The goal carries `(restrictNormalHom F σ).symm` — symm-of-image — whereas
    -- `AlgEquiv.restrictNormal_commutes` is about image-of-symm. `aut_inv` and `map_inv` cross
    -- that spelling, and `restrictNormalHom_eq_restrictNormal` then makes the two restriction
    -- APIs agree *syntactically*, rather than leaving the step to the `MonoidHom.mk'` unfolding.
    rw [← AlgEquiv.aut_inv, ← map_inv, AlgEquiv.aut_inv,
      AlgEquiv.restrictNormalHom_eq_restrictNormal]
    exact AlgEquiv.restrictNormal_commutes σ.symm F x
  ext x
  simp only [smul_eq_comap, comap_apply, RingHom.coe_coe]
  exact congrArg w (bridge x)

/-- **A complex induced place is itself ramified.** The place `w` induces on `F` lies over the
same place of `K` that `w` does, and that place is real because `w` is ramified; so once the
induced place is complex it is ramified over `K`. -/
theorem isRamified_comap_of_isComplex {w : InfinitePlace L} (hw : w.IsRamified K)
    (hv : (w.comap (algebraMap F L)).IsComplex) :
    (w.comap (algebraMap F L)).IsRamified K := by
  rw [isRamified_iff]
  refine ⟨hv, ?_⟩
  rw [← comap_comp, ← IsScalarTower.algebraMap_eq]
  exact (isRamified_iff.mp hw).2

/-- **An automorphism restricting trivially to `F`, and fixing a place unramified over `F`, is the
identity.** A trivial restriction makes it fix `F` pointwise, hence an `F`-automorphism; a place
unramified over `F` has trivial stabilizer in `Gal(L/F)`, leaving only the identity. -/
theorem eq_one_of_restrictNormalHom_eq_one [Normal K F] {w : InfinitePlace L}
    (hu : w.IsUnramified F) {σ : L ≃ₐ[K] L} (hσ : σ • w = w)
    (h1 : AlgEquiv.restrictNormalHom F σ = 1) : σ = 1 := by
  have hfix : ∀ x : F, σ (algebraMap F L x) = algebraMap F L x := fun x => by
    rw [← AlgEquiv.restrictNormal_commutes σ F x,
      ← AlgEquiv.restrictNormalHom_eq_restrictNormal, h1]
    simp
  set τ : L ≃ₐ[F] L := { σ with commutes' := hfix }
  have hmem : τ ∈ MulAction.stabilizer (L ≃ₐ[F] L) w := by
    rw [MulAction.mem_stabilizer_iff, smul_eq_comap]
    rw [smul_eq_comap] at hσ
    exact hσ
  rw [hu.stabilizer_eq_bot, Subgroup.mem_bot] at hmem
  ext x
  exact congrFun (congrArg (fun e : L ≃ₐ[F] L => (e : L → L)) hmem) x

end TauCeti.NumberField

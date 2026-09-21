/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Cont.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.ResidueField.Basic
public import Mathlib.Topology.Algebra.Valued.WithVal

/-!
# The residue field of a point as a topological field

`residueFieldValuation v` topologises the residue field `κ(v)` of a point `v : Spv A`, through
Mathlib's type synonym `WithVal`. This file describes the canonical map `A → κ(v)` for that
topology: the valuation it computes, and its continuity when `v` is a continuous point.

The algebraic content of `κ(v)` — the residue ring, the three valuations and their characteristic
equations — is in `TauCeti.AlgebraicGeometry.AdicSpace.ResidueField.Basic`, which carries no
topology. This file is where the topology enters, so that a consumer of `κ(v)` as a field need not
depend on the continuous-valuation API.

## Main results

* `TauCeti.ValuationSpectrum.valued_algebraMap_residueFieldValuation`: the valuation topologising
  `κ(v)` takes the image of `a : A` to `v.valuation a`.
* `TauCeti.ValuationSpectrum.continuous_algebraMap_residueFieldValuation`: for a continuous point
  of a ring with separately continuous operations, `A → κ(v)` is continuous.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §2.4 for the residue field and
  Definition 7.7 for continuity of a valuation.
-/

public section

namespace TauCeti

namespace ValuationSpectrum

variable {A : Type*} [CommRing A]

/-- **The valuation topologising `κ(v)` takes the image of `a : A` to `v.valuation a`.** The
residue field carries the topology of `residueFieldValuation v` through Mathlib's type synonym
`WithVal`, and `Valued.v` is that valuation.

This is the characteristic equation of `residueFieldValuation` at the level of `A` itself,
rather than of the residue ring `A ⧸ supp v`. -/
@[simp]
theorem valued_algebraMap_residueFieldValuation (v : Spv A) (a : A) :
    Valued.v (algebraMap A (WithVal (residueFieldValuation v)) a) = v.valuation a := by
  rw [WithVal.algebraMap_right_apply, WithVal.valued_toVal]
  exact (residueFieldValuation_algebraMap v (Ideal.Quotient.mk _ a)).trans <|
    DFunLike.congr_fun (quotientValuation_comap_quotientMk v) a

/-- **A continuous point maps continuously to its residue field.** If `v : Spv A` is continuous
then the canonical map `A → WithVal (residueFieldValuation v)` is continuous, `κ(v)` carrying
the topology of `residueFieldValuation v`.

Separate continuity of the ring operations is enough: the topology and the ring structure of `A`
are related only through translations and multiplication by a constant. Continuity is what lets
the map be extended along a completion of `A`. -/
theorem continuous_algebraMap_residueFieldValuation [TopologicalSpace A]
    [IsSemitopologicalRing A] {v : Spv A} (hv : v.IsContinuous) :
    Continuous (algebraMap A (WithVal (residueFieldValuation v))) := by
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  let _ : ValuativeRel A := v.toValuativeRel
  -- the radius embeds to a nonzero element of the value group of `v`, so it is a ratio
  -- `v a / v b` of values of `v` itself, and continuity opens the ball of that radius
  have hγ : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp [γ.ne_zero]
  obtain ⟨a, b, -, hb, hab⟩ := (ValuativeRel.valuation A).exists_div_eq_of_unit
    (Units.mk0 (ValuativeRel.ValueGroupWithZero.orderMonoidIso (ValuativeRel.valuation A)
      (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)) (by simp [hγ]))
  simp only [Units.val_mk0] at hab
  have hb' : v.valuation b ≠ 0 := by rw [valuation_def]; exact hb.ne'
  have hemb : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = v.valuation a / v.valuation b := by
    rw [valuation_def, ← ValuativeRel.ValueGroupWithZero.embedding_orderMonoidIso_valuation_eq
      (MonoidWithZeroHom.ValueGroup₀.embedding γ.1), ← hab, map_div₀,
      Valuation.embedding_restrict, Valuation.embedding_restrict]
  filter_upwards [(((isContinuous_def v).mp hv).isOpen_lt_div a hb').mem_nhds
    (by simp [← hemb, zero_lt_iff])] with z hz
  rwa [Valuation.restrict_lt_iff_lt_embedding, valued_algebraMap_residueFieldValuation, hemb]

end ValuationSpectrum

end TauCeti

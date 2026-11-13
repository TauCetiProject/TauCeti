/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Multiplicity
import TauCeti.Algebra.DirectSum.Internal
import TauCeti.RepresentationTheory.Rep.DirectSum.AsModule

/-!
# The regrouping of a representation into copies of the irreducible models

Let `G` be a finite group and `k` an algebraically closed field in which `|G|` is invertible, and
let `Zᵢ = TauCeti.irreducibleRepresentation k i` be the chosen irreducible representations, one for
each row `i` of the character table. `Representation.nonempty_regrouping` regroups a
finite-dimensional representation `ρ`, as a `k[G]`-module, into `m_ρ(i)` copies of each `Zᵢ`, where
`m_ρ(i)` is the intrinsic multiplicity `Representation.intrinsicMultiplicity ρ i`.

This file transports that regrouping from group-algebra modules back to representations, through
the direct-sum comparison `Representation.directSumAsModuleEquiv` and
`TauCeti.Representation.equivOfAsModuleLinearEquiv`. The summands are indexed by the pairs `(i, j)`
with `j : Fin (m_ρ(i))`, the summand at `(i, j)` being the `j`-th copy of `Zᵢ`. The result appears
in three forms:

* as an equivalence of representations `ρ ≃ ⨁_(i, j) Zᵢ` with the concrete direct-sum
  representation `Representation.directSum`;
* as an isomorphism in `FDRep k G`, the categorical mirror;
* internally, as a decomposition of the carrier of `ρ` into an internal direct sum of
  subrepresentations, `m_ρ(i)` of them equivalent to `Zᵢ`. They are the images of the summands of
  the direct sum under the equivalence of the first form.

Only the existence of these decompositions is intrinsic: choosing one amounts to choosing bases of
the multiplicity spaces.

## Main results

* `Representation.nonempty_equiv_directSum_irreducibleRepresentation`: a finite-dimensional `ρ` is
  equivalent to the direct sum of `m_ρ(i)` copies of each `Zᵢ`.
* `FDRep.nonempty_iso_directSum_irreducibleRepresentation`: the same statement in `FDRep k G`.
* `Representation.exists_isInternal_equiv_irreducibleRepresentation`: the carrier of a
  finite-dimensional `ρ` is an internal direct sum of subrepresentations, indexed by the pairs
  `(i, j)` with `j < m_ρ(i)`, the one at `(i, j)` being equivalent to `Zᵢ`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, §2.4, formula (2.31),
  and §3.4 for the dictionary between representations and group-algebra modules.
-/

public section

open DirectSum
open scoped MonoidAlgebra

universe u v w

namespace Representation

open TauCeti

variable {k : Type u} {G : Type v} [Field k] [IsAlgClosed k] [Group G] [Finite G]
  [Invertible (Nat.card G : k)]
variable {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k G V)

/-- **The regrouping of a representation.** A finite-dimensional representation `ρ` is equivalent
to the direct sum of `m_ρ(i)` copies of each irreducible model `Zᵢ`: the summands are indexed by
the pairs `(i, j)` with `j : Fin (m_ρ(i))`, and the summand at `(i, j)` is `Zᵢ`. This is
`Representation.nonempty_regrouping` transported from group-algebra modules to representations. -/
theorem nonempty_equiv_directSum_irreducibleRepresentation [FiniteDimensional k V] :
    Nonempty (ρ.Equiv (directSum fun p : Σ i, Fin (ρ.intrinsicMultiplicity i) ↦
      irreducibleRepresentation k p.1)) := by
  classical
  obtain ⟨e⟩ := ρ.nonempty_regrouping
  -- Flatten `Π₀ i, Fin (m_ρ(i)) → Zᵢ` into a direct sum over the pairs `(i, j)`.
  exact ⟨TauCeti.Representation.equivOfAsModuleLinearEquiv <|
    e ≪≫ₗ DFinsupp.linearEquivFunOnFintype ≪≫ₗ
      (LinearEquiv.piCurry k[G] fun i (_ : Fin (ρ.intrinsicMultiplicity i)) ↦
        (irreducibleRepresentation k i).asModule).symm ≪≫ₗ
      DFinsupp.linearEquivFunOnFintype.symm ≪≫ₗ
      (directSumAsModuleEquiv fun p : Σ i, Fin (ρ.intrinsicMultiplicity i) ↦
        irreducibleRepresentation k p.1).symm⟩

/-- **The internal regrouping.** The carrier of a finite-dimensional representation `ρ` is the
internal direct sum of a family of subrepresentations indexed by the pairs `(i, j)` with
`j : Fin (m_ρ(i))`, the subrepresentation at `(i, j)` being equivalent to the model `Zᵢ`. In
particular `m_ρ(i)` of the summands are equivalent to `Zᵢ`. -/
theorem exists_isInternal_equiv_irreducibleRepresentation [FiniteDimensional k V] :
    ∃ W : (Σ i, Fin (ρ.intrinsicMultiplicity i)) → Subrepresentation ρ,
      IsInternal (fun p ↦ (W p).toSubmodule) ∧
        ∀ p, Nonempty ((W p).toRepresentation.Equiv (irreducibleRepresentation k p.1)) := by
  classical
  obtain ⟨φ⟩ := ρ.nonempty_equiv_directSum_irreducibleRepresentation
  let σ := fun p : Σ i, Fin (ρ.intrinsicMultiplicity i) ↦ irreducibleRepresentation k p.1
  -- The summand at `p`, included into `ρ` through the regrouping.
  let f p : IntertwiningMap (σ p) ρ :=
    φ.symm.toIntertwiningMap.comp
      ⟨lof k _ (fun q : Σ i, Fin (ρ.intrinsicMultiplicity i) ↦ Fin (characterDegree k q.1) → k) p,
        fun g ↦ LinearMap.ext fun x ↦ by simp [σ]⟩
  -- `lof` has the left inverse `component`.
  have hf p : Function.Injective (f p) :=
    φ.symm.toLinearEquiv.injective.comp fun x y h ↦ by
      simpa using congrArg (component k _ _ p) h
  let e p := (f p).equivOfRange (hf p) (P := (f p).range) rfl
  exact ⟨fun p ↦ (f p).range,
    TauCeti.DirectSum.isInternal_of_lof (fun p ↦ (e p).toLinearEquiv) φ.symm.toLinearEquiv
      fun p x ↦ ((f p).equivOfRange_apply_coe (hf p) rfl x).symm,
    fun p ↦ ⟨(e p).symm⟩⟩

end Representation

namespace FDRep

open TauCeti

variable {k : Type u} {G : Type v} [Field k] [IsAlgClosed k] [Group G] [Finite G]
  [Invertible (Nat.card G : k)]

/-- **The regrouping in `FDRep k G`.** Every object `V` of `FDRep k G` is isomorphic to the direct
sum of `m_V(i)` copies of each irreducible model `Zᵢ`, indexed by the pairs `(i, j)` with
`j : Fin (m_V(i))`. -/
theorem nonempty_iso_directSum_irreducibleRepresentation (V : FDRep k G) :
    Nonempty (V ≅ FDRep.of (Representation.directSum
      fun p : Σ i, Fin (Representation.intrinsicMultiplicity V.ρ i) ↦
        irreducibleRepresentation k p.1)) :=
  nonempty_fdRepIso_iff.mpr
    (Representation.nonempty_equiv_directSum_irreducibleRepresentation V.ρ)

end FDRep

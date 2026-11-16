/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Squares
public import TauCeti.RepresentationTheory.Dual
public import TauCeti.RepresentationTheory.ExteriorPower
public import TauCeti.RepresentationTheory.InvariantForm
public import TauCeti.RepresentationTheory.SymmetricPower

/-!
# Invariant forms and the invariants of the two squares

A functional on the symmetric square `Sym²V` becomes a symmetric bilinear form on `V`, and a
functional on the exterior square `⋀²V` an alternating one
(`TauCeti.BilinForm.ofSymmetricSquareDual` and `TauCeti.BilinForm.ofExteriorSquareDual`).  This
file shows that, for a representation `ρ` of a group `G`, these assignments carry the invariant
functionals on each square exactly onto the invariant symmetric, respectively alternating, forms,
over any commutative ring and with no finiteness assumption.  Over a field in which `|G|` is
invertible, a representation and its dual have equally many invariants
(`TauCeti.Representation.finrank_invariants_dual`), so the invariant symmetric, respectively
alternating, forms have the `finrank` of the invariants of the symmetric, respectively exterior,
square: the same dimension when finite-dimensional, and `0` on both sides, by convention,
otherwise.

Nothing here uses characters or the Frobenius-Schur indicator;
`TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.Trichotomy` combines these counts with
the character formula for the indicator.

## Main results

* `Representation.map_ofSymmetricSquareDual_eq_symmetricInvariantForms` and
  `Representation.map_ofExteriorSquareDual_eq_alternatingInvariantForms`: **every invariant
  symmetric, respectively alternating, form comes from an invariant functional on the corresponding
  square**, and every invariant functional gives one.
* `Representation.finrank_symmetricInvariantForms` and
  `Representation.finrank_alternatingInvariantForms`: over a field in which `|G|` is invertible,
  the invariant symmetric, respectively alternating, forms have the same `finrank` as the
  invariants of the symmetric, respectively exterior, square.
* `Representation.finrank_invariantForms`: **the invariant forms are as many as the invariants of
  the two squares together**, for a finite-dimensional `V` over a field in which `|G|` is
  invertible, in every characteristic.

The last count combines the two square counts with the count of the invariant forms by the
invariant symmetric and alternating forms together, in
`TauCeti/RepresentationTheory/InvariantForm.lean`, which holds in every characteristic not dividing
`|G|`, including characteristic two, where the two kinds of form overlap.

## Implementation notes

Symmetric and alternating forms lift to functionals via
`LinearMap.BilinForm.IsSymm.exists_ofSymmetricSquareDual_eq` and
`LinearMap.BilinForm.IsAlt.exists_ofExteriorSquareDual_eq`, and the injectivity lemmas
`TauCeti.BilinForm.ofSymmetricSquareDual_injective` and
`TauCeti.BilinForm.ofExteriorSquareDual_injective` give `G`-invariance of those functionals.

The results about the symmetric square take the ring in `Type`: Mathlib's symmetric power
`Sym[k]^2 V` indexes its tensor factors by `Fin 2`, in the universe of `k`.  The results about the
exterior square allow a ring in any universe.
-/

public section

open scoped TensorProduct

open Module (finrank)

namespace Representation

open LinearMap (BilinForm)
open TauCeti.Representation

section SymmetricSquare

variable {k : Type} {G V : Type*} [CommRing k] [Group G] [AddCommMonoid V] [Module k V]

/-- An invariant functional on the symmetric square gives an invariant symmetric form. -/
theorem ofSymmetricSquareDual_mem_symmetricInvariantForms (ρ : Representation k G V)
    {ψ : Module.Dual k (Sym[k]^2V)} (hψ : ψ ∈ ((ρ.symmetricPower 2).dual).invariants) :
    TauCeti.BilinForm.ofSymmetricSquareDual ψ ∈ symmetricInvariantForms ρ := by
  refine mem_symmetricInvariantForms.mpr
    ⟨isInvariantForm_iff.mpr fun g x y => ?_, TauCeti.BilinForm.isSymm_ofSymmetricSquareDual ψ⟩
  have hvec : (fun i => ρ g (![x, y] i)) = ![ρ g x, ρ g y] := (FinVec.map_eq _ _).symm
  simp only [TauCeti.BilinForm.ofSymmetricSquareDual_apply]
  rw [← hvec, ← ρ.symmetricPower_apply_tprod 2 g ![x, y],
    apply_of_mem_invariants_dual hψ g]

/-- Over any commutative ring, `TauCeti.BilinForm.ofSymmetricSquareDual` maps the invariant
functionals on the symmetric square onto the invariant symmetric forms. -/
theorem map_ofSymmetricSquareDual_eq_symmetricInvariantForms (ρ : Representation k G V) :
    Submodule.map (TauCeti.BilinForm.ofSymmetricSquareDual (k := k) (V := V))
        ((ρ.symmetricPower 2).dual).invariants = symmetricInvariantForms ρ := by
  refine le_antisymm (Submodule.map_le_iff_le_comap.mpr fun _ hψ =>
    ofSymmetricSquareDual_mem_symmetricInvariantForms ρ hψ) fun B hB' => ?_
  obtain ⟨hB, hsymm⟩ := mem_symmetricInvariantForms.mp hB'
  obtain ⟨ψ, rfl⟩ := hsymm.exists_ofSymmetricSquareDual_eq
  refine ⟨ψ, mem_invariants_dual_iff.mpr fun g u => ?_, rfl⟩
  have hext : ψ ∘ₗ (ρ.symmetricPower 2 g) = ψ := by
    apply TauCeti.BilinForm.ofSymmetricSquareDual_injective
    ext x y
    have hvec : (fun i => ρ g (![x, y] i)) = ![ρ g x, ρ g y] := (FinVec.map_eq _ _).symm
    simp only [TauCeti.BilinForm.ofSymmetricSquareDual_apply, LinearMap.comp_apply,
      ρ.symmetricPower_apply_tprod 2 g ![x, y], hvec]
    simp only [← TauCeti.BilinForm.ofSymmetricSquareDual_apply]
    exact hB.apply g x y
  exact LinearMap.congr_fun hext u

end SymmetricSquare

section ExteriorSquare

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]

/-- An invariant functional on the exterior square gives an invariant alternating form. -/
theorem ofExteriorSquareDual_mem_alternatingInvariantForms (ρ : Representation k G V)
    {ψ : Module.Dual k (⋀[k]^2 V)} (hψ : ψ ∈ ((ρ.exteriorPower 2).dual).invariants) :
    TauCeti.BilinForm.ofExteriorSquareDual ψ ∈ alternatingInvariantForms ρ := by
  refine mem_alternatingInvariantForms.mpr
    ⟨isInvariantForm_iff.mpr fun g x y => ?_, TauCeti.BilinForm.isAlt_ofExteriorSquareDual ψ⟩
  have hvec : (ρ g ∘ ![x, y]) = ![ρ g x, ρ g y] := (FinVec.map_eq _ _).symm
  simp only [TauCeti.BilinForm.ofExteriorSquareDual_apply]
  rw [← hvec, ← ρ.exteriorPower_apply_ιMulti 2 g ![x, y],
    apply_of_mem_invariants_dual hψ g]

/-- Over any commutative ring, `TauCeti.BilinForm.ofExteriorSquareDual` maps the invariant
functionals on the exterior square onto the invariant alternating forms. -/
theorem map_ofExteriorSquareDual_eq_alternatingInvariantForms (ρ : Representation k G V) :
    Submodule.map (TauCeti.BilinForm.ofExteriorSquareDual (k := k) (V := V))
        ((ρ.exteriorPower 2).dual).invariants = alternatingInvariantForms ρ := by
  refine le_antisymm (Submodule.map_le_iff_le_comap.mpr fun _ hψ =>
    ofExteriorSquareDual_mem_alternatingInvariantForms ρ hψ) fun B hB' => ?_
  obtain ⟨hB, halt⟩ := mem_alternatingInvariantForms.mp hB'
  obtain ⟨ψ, rfl⟩ := halt.exists_ofExteriorSquareDual_eq
  refine ⟨ψ, mem_invariants_dual_iff.mpr fun g u => ?_, rfl⟩
  have hext : ψ ∘ₗ (ρ.exteriorPower 2 g) = ψ := by
    apply TauCeti.BilinForm.ofExteriorSquareDual_injective
    ext x y
    have hvec : (ρ g ∘ ![x, y]) = ![ρ g x, ρ g y] := (FinVec.map_eq _ _).symm
    simp only [TauCeti.BilinForm.ofExteriorSquareDual_apply, LinearMap.comp_apply,
      ρ.exteriorPower_apply_ιMulti 2 g ![x, y], hvec]
    simp only [← TauCeti.BilinForm.ofExteriorSquareDual_apply]
    exact hB.apply g x y
  exact LinearMap.congr_fun hext u

end ExteriorSquare

section SymmetricCount

variable {k : Type} {G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [Invertible (Nat.card G : k)]

/-- **The invariant symmetric forms and the invariants of the symmetric square have the same
`finrank`**, whenever `|G|` is invertible in the field `k`.  They have the same dimension when
finite-dimensional, and both `finrank`s are `0`, by convention, when infinite-dimensional. -/
theorem finrank_symmetricInvariantForms (ρ : Representation k G V) :
    finrank k (symmetricInvariantForms ρ) = finrank k (ρ.symmetricPower 2).invariants := by
  rw [← map_ofSymmetricSquareDual_eq_symmetricInvariantForms ρ,
    ← (Submodule.equivMapOfInjective (TauCeti.BilinForm.ofSymmetricSquareDual (k := k) (V := V))
      TauCeti.BilinForm.ofSymmetricSquareDual_injective
      ((ρ.symmetricPower 2).dual).invariants).finrank_eq, finrank_invariants_dual]

end SymmetricCount

section AlternatingCount

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [Invertible (Nat.card G : k)]

/-- **The invariant alternating forms and the invariants of the exterior square have the same
`finrank`**, whenever `|G|` is invertible in the field `k`.  They have the same dimension when
finite-dimensional, and both `finrank`s are `0`, by convention, when infinite-dimensional. -/
theorem finrank_alternatingInvariantForms (ρ : Representation k G V) :
    finrank k (alternatingInvariantForms ρ) = finrank k (ρ.exteriorPower 2).invariants := by
  rw [← map_ofExteriorSquareDual_eq_alternatingInvariantForms ρ,
    ← (Submodule.equivMapOfInjective (TauCeti.BilinForm.ofExteriorSquareDual (k := k) (V := V))
      TauCeti.BilinForm.ofExteriorSquareDual_injective
      ((ρ.exteriorPower 2).dual).invariants).finrank_eq, finrank_invariants_dual]

end AlternatingCount

section InvariantFormsCount

variable {k : Type} {G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [Invertible (Nat.card G : k)]

/-- **The invariant forms are as many as the invariants of the two squares together**, for a
finite-dimensional `V` over a field in which `|G|` is invertible, in every characteristic.  The
invariant symmetric and alternating forms together are as many as the invariant forms, by
`Representation.finrank_symmetricInvariantForms_add_finrank_alternatingInvariantForms_of_invertible`
and they are as many as the invariants of the symmetric, respectively exterior, square. -/
theorem finrank_invariantForms (ρ : Representation k G V) :
    finrank k (invariantForms ρ) =
      finrank k (ρ.symmetricPower 2).invariants + finrank k (ρ.exteriorPower 2).invariants := by
  rw [← ρ.finrank_symmetricInvariantForms_add_finrank_alternatingInvariantForms_of_invertible,
    ρ.finrank_symmetricInvariantForms, ρ.finrank_alternatingInvariantForms]

end InvariantFormsCount

end Representation

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
* `Representation.exists_mem_invariantForms_sub_flip_eq`: when `|G|` is invertible, an invariant
  form of the shape `B₀ - B₀.flip` is `B - B.flip` for an invariant form `B`, by averaging.

For a finite-dimensional `V` over a field in which `|G|` is invertible, the invariant symmetric and
alternating forms together are as many as the invariant forms, in every characteristic:
`Representation.finrank_symmetricInvariantForms_add_finrank_alternatingInvariantForms_of_invertible`
counts them through the map `B ↦ B - B.flip`, which carries the invariant forms onto the invariant
alternating forms with the invariant symmetric forms as kernel.  Away from characteristic two the
two kinds of form are complementary
(`Representation.finrank_symmetricInvariantForms_add_finrank_alternatingInvariantForms`); in
characteristic two they overlap, and the count still holds.

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

section SymmetricAlternatingCount

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [Invertible (Nat.card G : k)]

/-- **An invariant alternating form is `B - B.flip` for an invariant form `B`** when `|G|` is
invertible in the field `k`, as soon as it is `B₀ - B₀.flip` for some form `B₀`: average `B₀` over
`G`. -/
theorem exists_mem_invariantForms_sub_flip_eq (ρ : Representation k G V) {A B₀ : BilinForm k V}
    (hA : IsInvariantForm ρ A) (hB₀ : B₀ - B₀.flip = A) :
    ∃ B ∈ invariantForms ρ, B - B.flip = A := by
  have : Finite G := Nat.finite_of_card_ne_zero fun h => by
    simpa [h] using Invertible.ne_zero (Nat.card G : k)
  have := Fintype.ofFinite G
  have hB₀' (x y : V) : B₀ x y - B₀ y x = A x y := by
    simpa using LinearMap.congr_fun₂ hB₀ x y
  refine ⟨⅟(Nat.card G : k) • ∑ g : G, B₀.compl₁₂ (ρ g) (ρ g),
    mem_invariantForms.mpr (isInvariantForm_iff.mpr fun h x y => ?_), ?_⟩
  · have hmul (g : G) (v : V) : ρ g (ρ h v) = ρ (g * h) v := by rw [map_mul]; rfl
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.compl₁₂_apply, hmul]
    exact congrArg _ (Equiv.sum_comp (Equiv.mulRight h) fun g => B₀ (ρ g x) (ρ g y))
  · ext x y
    simp only [LinearMap.sub_apply, LinearMap.BilinForm.flip_apply, LinearMap.smul_apply,
      LinearMap.sum_apply, LinearMap.compl₁₂_apply, smul_eq_mul, ← mul_sub,
      ← Finset.sum_sub_distrib, hB₀', hA.apply, Finset.sum_const, Finset.card_univ,
      Fintype.card_eq_nat_card, nsmul_eq_mul, invOf_mul_cancel_left]

/-- **The invariant symmetric and alternating forms together are as many as the invariant forms**,
for a finite-dimensional `V` over a field in which `|G|` is invertible, in every characteristic.
In characteristic two the two kinds of form overlap and do not span the invariant forms, but the
map `B ↦ B - B.flip` still carries the invariant forms onto the invariant alternating forms, by
averaging, with the invariant symmetric forms as kernel. -/
theorem finrank_symmetricInvariantForms_add_finrank_alternatingInvariantForms_of_invertible
    [FiniteDimensional k V] (ρ : Representation k G V) :
    finrank k (symmetricInvariantForms ρ) + finrank k (alternatingInvariantForms ρ) =
      finrank k (invariantForms ρ) := by
  let φ : BilinForm k V →ₗ[k] BilinForm k V :=
    { toFun B := B - B.flip
      map_add' B C := by ext; simp [sub_add_sub_comm]
      map_smul' c B := by ext; simp [mul_sub] }
  have hrange : (invariantForms ρ).map φ = alternatingInvariantForms ρ := by
    refine le_antisymm (Submodule.map_le_iff_le_comap.mpr fun B hB => ?_) fun A hA => ?_
    · refine mem_alternatingInvariantForms.mpr ⟨?_, fun x => by simp [φ]⟩
      have e : φ B = B + (-1 : k) • B.flip := by
        ext x y
        simp [φ, sub_eq_add_neg]
      rw [e]
      exact (mem_invariantForms.mp hB).add ((mem_invariantForms.mp hB).flip.smul _)
    · obtain ⟨hAinv, hAalt⟩ := mem_alternatingInvariantForms.mp hA
      obtain ⟨B₀, hB₀⟩ := hAalt.exists_sub_flip_eq
      exact exists_mem_invariantForms_sub_flip_eq ρ hAinv hB₀
  have hker : LinearMap.ker (φ.domRestrict (invariantForms ρ)) =
      (symmetricInvariantForms ρ).comap (invariantForms ρ).subtype := by
    ext ⟨B, hB⟩
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply, Submodule.mem_comap,
      Submodule.subtype_apply, mem_symmetricInvariantForms, mem_invariantForms.mp hB, true_and,
      LinearMap.BilinForm.isSymm_iff_flip]
    exact (sub_eq_zero (a := B) (b := B.flip)).trans eq_comm
  have hrange' : finrank k (LinearMap.range (φ.domRestrict (invariantForms ρ))) =
      finrank k (alternatingInvariantForms ρ) := by
    rw [LinearMap.range_domRestrict, hrange]
  have hker' : finrank k (LinearMap.ker (φ.domRestrict (invariantForms ρ))) =
      finrank k (symmetricInvariantForms ρ) := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe (symmetricInvariantForms_le ρ)).finrank_eq
  -- Instance search does not see `invariantForms ρ` as a subgroup of the additive group of forms,
  -- whose `AddCommMonoid` structure it carries from the semiring setting, so both are supplied.
  let : AddCommGroup (invariantForms ρ) :=
    Submodule.addCommGroup (M := BilinForm k V) (invariantForms ρ)
  have : FiniteDimensional k (invariantForms ρ) :=
    FiniteDimensional.finiteDimensional_submodule (V := BilinForm k V) (invariantForms ρ)
  have h := LinearMap.finrank_range_add_finrank_ker (K := k) (V₂ := BilinForm k V)
    (φ.domRestrict (invariantForms ρ))
  omega

end SymmetricAlternatingCount

end Representation

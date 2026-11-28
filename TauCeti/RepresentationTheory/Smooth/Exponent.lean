/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Averaging

/-!
# Exponents of smooth representations at a compact subgroup

Let `ρ` be a smooth representation of a topological group `G` (with separately continuous
multiplication) on a module `V` over a commutative ring `A`, let `C` be a compact subgroup of `G`
whose pro-order is invertible in `A`, and let `e_C` be the averaging projector
`Representation.smoothAverage (ρ.comp C.subtype) hC` onto `V^C`. Given a submonoid `T` of `G` and
a monoid homomorphism `ξ : T →* A`, a linear map `ℓ : V →ₗ[A] W` is an **exponent** for `ξ`
(`Representation.IsExponent`) if `ℓ (ρ t (e_C v)) = ξ t • ℓ v` for every `t ∈ T` and `v ∈ V`.

Evaluating at `t = 1` shows that `ℓ ∘ e_C = ℓ` and hence `ℓ` is `C`-invariant. Whenever every
`c ∈ C` factors as `c = a * b` with `t a t⁻¹ ∈ C` and `ρ b v = v` (in particular whenever `t`
normalises `C`, such as a diagonal matrix with unit entries normalising the pro-`p` Iwahori
subgroup `I₁` of `GL_N`), the linear map `z ↦ ℓ (ρ t z)` is constant on the `C`-orbit of `v`, so
the averaging projector `e_C` drops out and `ℓ (ρ t v) = ξ t • ℓ v`.

## Main definitions

* `Representation.IsExponent`: `ℓ (ρ t (e_C v)) = ξ t • ℓ v` for all `t ∈ T` and `v ∈ V`.

## Main results

* `Representation.isExponent_iff`, `Representation.IsExponent.apply`:
  characterization and elimination of the exponent identity `ℓ (ρ t (e_C v)) = ξ t • ℓ v`.
* `Representation.IsExponent.map_smoothAverage`, `Representation.IsExponent.comp_smoothAverage`:
  `ℓ (e_C v) = ℓ v` and `ℓ ∘ₗ e_C = ℓ`.
* `Representation.IsExponent.map_apply_of_mem`: `ℓ (ρ c v) = ℓ v` for `c ∈ C`.
* `Representation.IsExponent.map_apply_of_factor`: if every `c ∈ C` factors as `c = a * b` with
  `t a t⁻¹ ∈ C` and `ρ b v = v`, then `ℓ (ρ t v) = ξ t • ℓ v`.
* `Representation.IsExponent.map_apply_of_conj_mem`: if `t c t⁻¹ ∈ C` for every `c ∈ C`, then
  `ℓ (ρ t v) = ξ t • ℓ v` for every `v ∈ V`.

## References

* W. Casselman, *Introduction to the theory of admissible representations of `p`-adic reductive
  groups* (unpublished notes, 1995).

Adapted from `src/Lib/LocalGL/Iwahori/QuadraticRelation.lean` in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC):
`New.IsExponent.apply_compactMean`, `New.IsExponent.apply_proIwahori`, and
`New.IsExponent.apply_diagGL_unit`, generalised from the pro-`p` Iwahori subgroup of `GL_N(F)` to
an arbitrary compact subgroup `C` of invertible pro-order and submonoid `T`.
-/

public section

namespace Representation

variable {A G V W : Type*} [CommRing A] [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
  {ρ : Representation A G V} [IsSmooth ρ]
  {C : Subgroup G} [CompactSpace C] {hC : TauCeti.HasUnitProOrder A C}
  {T : Submonoid G} {ξ : T →* A} {ℓ : V →ₗ[A] W}

/-- A linear map `ℓ : V →ₗ[A] W` is an **exponent** for a smooth representation `ρ` at a compact
subgroup `C` and submonoid `T` with character `ξ : T →* A` if `ℓ (ρ t (e_C v)) = ξ t • ℓ v` for
every `t ∈ T` and `v ∈ V`. -/
def IsExponent (ρ : Representation A G V) [IsSmooth ρ]
    (C : Subgroup G) [CompactSpace C] (hC : TauCeti.HasUnitProOrder A C)
    (T : Submonoid G) (ξ : T →* A) (ℓ : V →ₗ[A] W) : Prop :=
  ∀ (t : T) (v : V), ℓ (ρ t (smoothAverage (ρ.comp C.subtype) hC v)) = ξ t • ℓ v

/-- Characterization of `Representation.IsExponent`. -/
theorem isExponent_iff :
    IsExponent ρ C hC T ξ ℓ ↔
      ∀ (t : T) (v : V), ℓ (ρ t (smoothAverage (ρ.comp C.subtype) hC v)) = ξ t • ℓ v :=
  Iff.rfl

/-- Applying an exponent `ℓ` to `ρ t (e_C v)` scales `ℓ v` by `ξ t`. -/
theorem IsExponent.apply (hℓ : IsExponent ρ C hC T ξ ℓ) (t : T) (v : V) :
    ℓ (ρ t (smoothAverage (ρ.comp C.subtype) hC v)) = ξ t • ℓ v :=
  hℓ t v

/-- An exponent `ℓ` is invariant under the averaging projector `e_C`: `ℓ (e_C v) = ℓ v`. -/
@[simp]
theorem IsExponent.map_smoothAverage (hℓ : IsExponent ρ C hC T ξ ℓ) (v : V) :
    ℓ (smoothAverage (ρ.comp C.subtype) hC v) = ℓ v := by
  simpa using hℓ.apply 1 v

/-- An exponent `ℓ` satisfies `ℓ ∘ e_C = ℓ` as linear maps. -/
@[simp]
theorem IsExponent.comp_smoothAverage (hℓ : IsExponent ρ C hC T ξ ℓ) :
    ℓ ∘ₗ smoothAverage (ρ.comp C.subtype) hC = ℓ :=
  LinearMap.ext hℓ.map_smoothAverage

/-- An exponent `ℓ` is invariant under the compact subgroup `C`: `ℓ (ρ c v) = ℓ v` for `c ∈ C`. -/
theorem IsExponent.map_apply_of_mem (hℓ : IsExponent ρ C hC T ξ ℓ) {c : G} (hc : c ∈ C) (v : V) :
    ℓ (ρ c v) = ℓ v := by
  rw [← hℓ.map_smoothAverage (ρ c v), ← hℓ.map_smoothAverage v]
  exact congrArg ℓ (smoothAverage_apply_apply (ρ.comp C.subtype) hC ⟨c, hc⟩ v)

/-- If `t ∈ T` and every `c ∈ C` factors as `c = a * b` with `t a t⁻¹ ∈ C` and `ρ b v = v`, then
the averaging projector drops out of the exponent identity at `(t, v)`: `ℓ (ρ t v) = ξ t • ℓ v`. -/
theorem IsExponent.map_apply_of_factor (hℓ : IsExponent ρ C hC T ξ ℓ) {t : T} {v : V}
    (ht : ∀ c ∈ C, ∃ a b : G, c = a * b ∧ (t : G) * a * (t : G)⁻¹ ∈ C ∧ ρ b v = v) :
    ℓ (ρ t v) = ξ t • ℓ v := by
  rw [← hℓ.apply t v]
  refine (map_smoothAverage_of_forall_apply_eq (ρ.comp C.subtype) hC (ℓ ∘ₗ ρ t) fun c ↦ ?_).symm
  obtain ⟨a, b, hcab, ha, hb⟩ := ht c.val c.property
  have hmul : (t : G) * c.val = ((t : G) * a * (t : G)⁻¹) * (t : G) * b := by
    rw [hcab]
    group
  calc
    (ℓ ∘ₗ ρ t) ((ρ.comp C.subtype) c v)
        = ℓ (ρ ((t : G) * c.val) v) := by simp [map_mul]
    _ = ℓ (ρ ((t : G) * a * (t : G)⁻¹) (ρ t v)) := by simp [hmul, map_mul, hb]
    _ = (ℓ ∘ₗ ρ t) v := hℓ.map_apply_of_mem ha (ρ t v)

/-- If `t ∈ T` conjugates `C` into `C` (`t c t⁻¹ ∈ C` for all `c ∈ C`), then `ℓ (ρ t v) = ξ t • ℓ v`
for every `v ∈ V`, without the averaging projector. -/
theorem IsExponent.map_apply_of_conj_mem (hℓ : IsExponent ρ C hC T ξ ℓ) {t : T}
    (ht : ∀ c ∈ C, (t : G) * c * (t : G)⁻¹ ∈ C) (v : V) :
    ℓ (ρ t v) = ξ t • ℓ v :=
  hℓ.map_apply_of_factor fun c hc ↦ ⟨c, 1, (mul_one c).symm, ht c hc, by simp⟩

end Representation

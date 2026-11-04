/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Divisible
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic
public import TauCeti.LinearAlgebra.End.Basic
-- Baer's criterion for divisible groups, used only in `torusPointMap_surjective_of_injective`.
import Mathlib.Algebra.Category.Grp.Injective

/-!
# Character maps of endomorphisms of a split torus

A homomorphism `φ : (ι → ℤ) →ₗ[ℤ] (κ → ℤ)` of character lattices determines a homomorphism of
the points of the split tori in the opposite direction,
`TauCeti.torusPointMap φ : (κ → Rˣ) →* (ι → Rˣ)`, whose `i`-th coordinate at `s` is the value of
the character `φ eᵢ` at `s`. It is characterized by
`torusCharacter (torusPointMap φ s) χ = torusCharacter s (φ χ)`: evaluating a character at the
image point is evaluating its image under `φ` at the original point, so `φ` is the pullback of
characters along `torusPointMap φ`. It is `TauCeti.torusCharacterHom` applied to the images of the
basic characters, and its coordinates are the Laurent monomials that also describe the points of
the scheme morphism `TauCeti.SplitTorus.ofLinearMap`
(`TauCeti.SplitTorus.schemePointsMulEquiv_ofLinearMap`). This file works with the points
`κ → Rˣ` directly, which is how the Chevalley carriers parametrize their tori.

For a group `G` with a parametrized torus `T : (κ → Rˣ) →* G`, an endomorphism `F` of `G` and an
endomorphism `φ` of the character lattice `κ → ℤ`, the predicate `TauCeti.IsCharacterMap T F φ`
says that `F` preserves the torus and acts on its points through `φ`:
`F (T s) = T (torusPointMap φ s)`. The character map is data supplied with `F` and checked, not a
function of `F`. An abstract endomorphism that preserves the torus need not act on it through
characters at all: entrywise complex conjugation preserves the diagonal torus of `SL₂(ℂ)` and acts
on its coordinate by `z ↦ conj z`, which is not an integer power. And when `R` is a finite field the
character map of `F` need not be unique, since distinct characters can agree as functions on the
finitely many torus points.

The results proved here are the general properties of character maps that Steinberg
endomorphisms of groups of Lie type use:

* character maps compose contravariantly;
* over an infinite field and for an injective parametrization, the character map is unique;
* if the units of `R` are divisible, as over an algebraically closed field, an endomorphism with an
  injective character map maps the torus onto itself, because a divisible group is an injective
  `ℤ`-module (Mathlib's `Module.Baer.of_divisible`) and so the dual of an injective map of lattices
  is surjective;
* **Lang's equation on the torus**: under the same divisibility hypothesis, if `1 - φ` is
  injective then every torus point is `T u * (F (T u))⁻¹` for some `u`. This holds in particular
  when `φ ^ n = m • 1` for an integer `m ≠ 1`, which covers the `q`-power Frobenius
  (`φ = q • 1`) and every Steinberg endomorphism of a torus over the algebraic closure of a finite
  field. It is the torus case of the Lang–Steinberg theorem.

## Main definitions

* `TauCeti.torusPointMap`: the homomorphism of split-torus points dual to a homomorphism of
  character lattices.
* `TauCeti.IsCharacterMap`: an endomorphism acts on a parametrized torus through a given
  endomorphism of the character lattice.

## Main results

* `TauCeti.torusCharacter_torusPointMap`: the characterizing equation of `torusPointMap`.
* `TauCeti.torusPointMap_comp`, `TauCeti.torusPointMap_sub`, `TauCeti.torusPointMap_nsmul`:
  `torusPointMap` is contravariant and additive in the lattice map.
* `TauCeti.torusPointMap_injective`: over an infinite field, the lattice map is determined by the
  map on points.
* `TauCeti.torusPointMap_surjective_of_injective`: if the units of `R` are divisible, the dual of
  an injective lattice map is surjective on points.
* `TauCeti.IsCharacterMap.comp` and `TauCeti.IsCharacterMap.unique`: composition and uniqueness of
  character maps.
* `TauCeti.IsCharacterMap.map_range_eq`: an injective character map makes the endomorphism map
  the torus onto itself.
* `TauCeti.IsCharacterMap.exists_eq_mul_inv`: Lang's equation on the torus, with
  `TauCeti.injective_one_sub_of_pow_eq_smul_one` supplying its hypothesis.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Mem. Amer. Math. Soc. **80** (1968),
  Theorem 10.1 (the Lang–Steinberg theorem).
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
-/

public section

namespace TauCeti

variable {ι κ ν R : Type*} [CommRing R]

/-! ## The map on torus points dual to a map of character lattices -/

section TorusPointMap

variable [Fintype κ] [DecidableEq ι]

/-- **The homomorphism of split-torus points dual to a homomorphism of character lattices.** For
`φ : (ι → ℤ) →ₗ[ℤ] (κ → ℤ)`, the point `s : κ → Rˣ` of `𝔾ₘ^κ` is sent to the point of `𝔾ₘ^ι` whose
`i`-th coordinate is the value at `s` of the character `φ eᵢ`. Pulling characters back along it is
`φ` (`TauCeti.torusCharacter_torusPointMap`). -/
def torusPointMap (φ : (ι → ℤ) →ₗ[ℤ] (κ → ℤ)) : (κ → Rˣ) →* (ι → Rˣ) :=
  torusCharacterHom fun i => φ (Pi.single i 1)

/-- The coordinates of the image point are the values of the images of the basic characters. -/
@[simp]
theorem torusPointMap_apply (φ : (ι → ℤ) →ₗ[ℤ] (κ → ℤ)) (s : κ → Rˣ) (i : ι) :
    torusPointMap φ s i = torusCharacter s (φ (Pi.single i 1)) :=
  torusCharacterHom_apply _ s i

/-- **Characters pull back along `torusPointMap φ` by `φ`.** The value of a character `χ` at the
image of `s` is the value of `φ χ` at `s`. -/
@[simp]
theorem torusCharacter_torusPointMap [Fintype ι] (φ : (ι → ℤ) →ₗ[ℤ] (κ → ℤ)) (s : κ → Rˣ)
    (χ : ι → ℤ) : torusCharacter (torusPointMap φ s) χ = torusCharacter s (φ χ) := by
  conv_rhs => rw [pi_eq_sum_univ' χ, map_sum, torusCharacter_sum]
  rw [torusCharacter_def]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zsmul, torusCharacter_zsmul, torusPointMap_apply]

/-- The identity of the character lattice gives the identity of the torus. -/
@[simp]
theorem torusPointMap_id [Fintype ι] :
    torusPointMap (R := R) (LinearMap.id : Module.End ℤ (ι → ℤ)) = MonoidHom.id (ι → Rˣ) := by
  refine MonoidHom.ext fun s => funext fun i => ?_
  simp

/-- **`torusPointMap` is contravariant.** -/
theorem torusPointMap_comp [Fintype ν] [DecidableEq κ] (ψ : (κ → ℤ) →ₗ[ℤ] (ν → ℤ))
    (φ : (ι → ℤ) →ₗ[ℤ] (κ → ℤ)) :
    torusPointMap (R := R) (ψ ∘ₗ φ) = (torusPointMap φ).comp (torusPointMap ψ) := by
  refine MonoidHom.ext fun s => funext fun i => ?_
  simp

/-- `torusPointMap` turns sums of lattice maps into products of point maps. -/
theorem torusPointMap_add (φ ψ : (ι → ℤ) →ₗ[ℤ] (κ → ℤ)) :
    torusPointMap (R := R) (φ + ψ) = torusPointMap φ * torusPointMap ψ := by
  refine MonoidHom.ext fun s => funext fun i => ?_
  simp [torusCharacter_add]

/-- `torusPointMap` turns differences of lattice maps into quotients of point maps. -/
theorem torusPointMap_sub (φ ψ : (ι → ℤ) →ₗ[ℤ] (κ → ℤ)) :
    torusPointMap (R := R) (φ - ψ) = torusPointMap φ / torusPointMap ψ := by
  refine MonoidHom.ext fun s => funext fun i => ?_
  simp [torusCharacter_sub]

/-- `torusPointMap` turns multiples of lattice maps into powers of point maps. -/
theorem torusPointMap_nsmul (n : ℕ) (φ : (ι → ℤ) →ₗ[ℤ] (κ → ℤ)) :
    torusPointMap (R := R) (n • φ) = torusPointMap φ ^ n := by
  refine MonoidHom.ext fun s => funext fun i => ?_
  simp [← torusCharacter_nsmul]

/-- The identity endomorphism of the character lattice gives the identity of the torus. -/
@[simp]
theorem torusPointMap_one [Fintype ι] :
    torusPointMap (R := R) (1 : Module.End ℤ (ι → ℤ)) = MonoidHom.id (ι → Rˣ) :=
  torusPointMap_id

/-- **`torusPointMap` reverses products in the endomorphism ring of the character lattice.** -/
theorem torusPointMap_mul [Fintype ι] (φ ψ : Module.End ℤ (ι → ℤ)) :
    torusPointMap (R := R) (ψ * φ) = (torusPointMap φ).comp (torusPointMap ψ) :=
  torusPointMap_comp ψ φ

/-- **Over an infinite field the lattice map is determined by the map on torus points.** Some
hypothesis is needed: over `𝔽₂` the torus has a single point. -/
theorem torusPointMap_injective [Finite ι] {K : Type*} [Field K] [Infinite K] :
    Function.Injective (torusPointMap (R := K) (ι := ι) (κ := κ)) := by
  intro φ ψ h
  refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
  exact weightChar_injective (K := K) <| MonoidHom.ext fun s => by
    simpa only [weightChar_apply, torusPointMap_apply, LinearMap.comp_apply, LinearMap.coe_single]
      using congrFun (DFunLike.congr_fun h s) i

/-- **The dual of an injective lattice map is surjective on torus points when the units are
divisible**, for instance over an algebraically closed field. The units form a divisible, hence
injective, `ℤ`-module, so every character of the source lattice, read as a homomorphism into the
units, extends along `φ`. -/
theorem torusPointMap_surjective_of_injective [Finite ι] [RootableBy Rˣ ℕ]
    {φ : (ι → ℤ) →ₗ[ℤ] (κ → ℤ)} (hφ : Function.Injective φ) :
    Function.Surjective (torusPointMap (R := R) φ) := by
  classical
  have := Fintype.ofFinite ι
  intro s
  let : DivisibleBy (Additive Rˣ) ℕ :=
    divisibleByOfSMulRightSurj _ _ fun {n} hn a => by
      obtain ⟨b, hb⟩ := RootableBy.surjective_pow Rˣ ℕ hn a.toMul
      exact ⟨Additive.ofMul b, by simpa using congrArg Additive.ofMul hb⟩
  let : DivisibleBy (Additive Rˣ) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  -- The values of the characters at `s`, as a homomorphism from the source lattice.
  let g : (ι → ℤ) →+ Additive Rˣ :=
    { toFun χ := Additive.ofMul (torusCharacter s χ)
      map_zero' := by simp
      map_add' χ ψ := by simp [torusCharacter_add] }
  obtain ⟨h, hh⟩ :=
    (Module.Baer.of_divisible (Additive Rˣ)).extension_property_addMonoidHom φ.toAddMonoidHom hφ g
  -- The extension `h` is the evaluation of characters at the point `u` it determines.
  let u : κ → Rˣ := fun j => (h (Pi.single j 1)).toMul
  have hu (μ : κ → ℤ) : torusCharacter u μ = (h μ).toMul := by
    conv_rhs => rw [pi_eq_sum_univ' μ, map_sum, toMul_sum]
    rw [torusCharacter_def]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_zsmul, toMul_zsmul]
  refine ⟨u, funext fun i => ?_⟩
  have hi := congrArg Additive.toMul (DFunLike.congr_fun hh (Pi.single i 1))
  rw [torusPointMap_apply, hu]
  simpa [g] using hi

end TorusPointMap

/-! ## Character maps of endomorphisms of a parametrized torus -/

section IsCharacterMap

variable [Fintype κ] [DecidableEq κ] {G : Type*}

section Monoid

variable [Monoid G]

/-- **`φ` is a character map of `F` on the torus `T`**: the endomorphism `F` of `G` preserves the
image of the torus parametrization `T` and acts on its points through the endomorphism `φ` of the
character lattice, `F (T s) = T (torusPointMap φ s)`. By
`TauCeti.torusCharacter_torusPointMap`, a character `χ` evaluated at the parameter of `F (T s)` is
`φ χ` evaluated at `s`, so `φ` is the pullback of characters along `F`.

The character map is data supplied together with `F`: over a finite field it is not determined
by `F`, and an endomorphism preserving the torus need not have one. -/
def IsCharacterMap (T : (κ → Rˣ) →* G) (F : G →* G) (φ : Module.End ℤ (κ → ℤ)) : Prop :=
  ∀ s, F (T s) = T (torusPointMap φ s)

variable {T : (κ → Rˣ) →* G} {F F' : G →* G} {φ ψ : Module.End ℤ (κ → ℤ)}

/-- Unfolding `TauCeti.IsCharacterMap`: the endomorphism acts on each torus point through the
point map dual to the character map. -/
theorem isCharacterMap_iff :
    IsCharacterMap T F φ ↔ ∀ s, F (T s) = T (torusPointMap φ s) :=
  Iff.rfl

/-- A character map as an equation of homomorphisms out of the torus. -/
theorem isCharacterMap_iff_comp :
    IsCharacterMap T F φ ↔ F.comp T = T.comp (torusPointMap φ) := by
  rw [isCharacterMap_iff, MonoidHom.ext_iff]
  rfl

/-- The value of an endomorphism on a torus point, read through a character map. -/
theorem IsCharacterMap.map_apply (h : IsCharacterMap T F φ) (s : κ → Rˣ) :
    F (T s) = T (torusPointMap φ s) :=
  h s

variable (T) in
/-- The identity has the identity as character map. -/
theorem isCharacterMap_id : IsCharacterMap T (MonoidHom.id G) 1 := fun s => by simp

/-- **Character maps compose contravariantly.** If `φ` is a character map of `F` and `ψ` one of
`F'`, then `ψ * φ` is a character map of `F ∘ F'`, since characters pull back along `F'` after
pulling back along `F`. -/
theorem IsCharacterMap.comp (hF : IsCharacterMap T F φ) (hF' : IsCharacterMap T F' ψ) :
    IsCharacterMap T (F.comp F') (ψ * φ) := fun s => by
  rw [MonoidHom.comp_apply, hF', hF, torusPointMap_mul, MonoidHom.comp_apply]

/-- **Uniqueness of character maps over an infinite field.** If the torus parametrization is
injective, an endomorphism has at most one character map. Over a finite field this fails, which
is why a character map is data rather than a function of the endomorphism. -/
theorem IsCharacterMap.unique {K : Type*} [Field K] [Infinite K] {T : (κ → Kˣ) →* G}
    (hT : Function.Injective T) (hφ : IsCharacterMap T F φ) (hψ : IsCharacterMap T F ψ) :
    φ = ψ :=
  torusPointMap_injective <| MonoidHom.ext fun s => hT <| (hφ s).symm.trans (hψ s)

end Monoid

section Group

variable [Group G] {T : (κ → Rˣ) →* G} {F : G →* G} {φ : Module.End ℤ (κ → ℤ)}

/-- **An injective character map makes the endomorphism map the torus onto itself**, when the
units of `R` are divisible, for instance over an algebraically closed field: the image under `F` of
the image of `T` is the image of `T`. -/
theorem IsCharacterMap.map_range_eq [RootableBy Rˣ ℕ] (h : IsCharacterMap T F φ)
    (hφ : Function.Injective φ) : T.range.map F = T.range := by
  rw [MonoidHom.map_range, isCharacterMap_iff_comp.mp h, ← MonoidHom.map_range,
    MonoidHom.range_eq_top.mpr (torusPointMap_surjective_of_injective hφ),
    ← MonoidHom.range_eq_map]

/-- **Lang's equation on the torus.** If the units of `R` are divisible and `1 - φ` is injective,
then every torus point is `T u * (F (T u))⁻¹` for some torus point `T u`: the homomorphism
`t ↦ t * F(t)⁻¹` of the torus is surjective. Its character map is `1 - φ`, whose dual is
surjective. `TauCeti.injective_one_sub_of_pow_eq_smul_one` supplies the hypothesis for the
Steinberg endomorphisms. -/
theorem IsCharacterMap.exists_eq_mul_inv [RootableBy Rˣ ℕ] (h : IsCharacterMap T F φ)
    (hφ : Function.Injective ⇑(1 - φ)) (s : κ → Rˣ) : ∃ u, T s = T u * (F (T u))⁻¹ := by
  obtain ⟨u, rfl⟩ := torusPointMap_surjective_of_injective hφ s
  refine ⟨u, ?_⟩
  rw [h, torusPointMap_sub, torusPointMap_one, MonoidHom.div_apply, MonoidHom.id_apply, map_div,
    div_eq_mul_inv]

end Group

end IsCharacterMap

end TauCeti

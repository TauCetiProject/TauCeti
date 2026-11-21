/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.OreLocalization.Ring
public import Mathlib.Algebra.Algebra.Hom

/-!
# Algebra maps out of Ore localizations

For a commutative semiring `R₀`, an `R₀`-algebra `R` and a left Ore set `S ⊆ R`, Mathlib gives the
Ore localization `OreLocalization S R` an `R₀`-algebra structure and proves the universal property
of `OreLocalization.universalHom` for ring homomorphisms. This file records the `R₀`-linear
versions: the numerator map as an algebra map (`OreLocalization.numeratorAlgHom`), extensionality
of algebra maps out of `OreLocalization S R` (`OreLocalization.algHom_ext`), and the universal lift
(`OreLocalization.universalAlgHom`) with its uniqueness.

When `R` is nontrivial with no zero divisors and its nonzero elements form a left Ore set,
`OreLocalization R⁰ R` is Mathlib's division ring of fractions of `R`. An injective `R₀`-algebra
map from `R` into a division ring sends nonzero elements to units, so it extends uniquely to this
division ring (`OreLocalization.liftAlgHom`), the noncommutative analogue of
`IsFractionRing.liftAlgHom`.
-/

public section

open nonZeroDivisors

namespace OreLocalization

section Semiring

variable (R₀ : Type*) {R : Type*} [CommSemiring R₀] [Semiring R] [Algebra R₀ R]
  {S : Submonoid R} [OreSet S]

/-- The canonical `R₀`-algebra map from `R` to its Ore localization `OreLocalization S R`, sending
`r` to the fraction `r /ₒ 1`. -/
def numeratorAlgHom : R →ₐ[R₀] OreLocalization S R where
  __ := numeratorRingHom
  commutes' _ := rfl

@[simp]
theorem numeratorAlgHom_apply (r : R) : numeratorAlgHom R₀ (S := S) r = numeratorHom r := (rfl)

@[simp]
theorem toRingHom_numeratorAlgHom :
    (numeratorAlgHom R₀ (S := S) : R →+* OreLocalization S R) = numeratorRingHom := (rfl)

variable {R₀} {T : Type*} [Semiring T] [Algebra R₀ T]

/-- Two `R₀`-algebra maps out of an Ore localization agreeing on numerators are equal. -/
@[ext high] -- This should have higher precedence than `AlgHom.ext`.
theorem algHom_ext {φ ψ : OreLocalization S R →ₐ[R₀] T}
    (h : φ.comp (numeratorAlgHom R₀) = ψ.comp (numeratorAlgHom R₀)) : φ = ψ := by
  have hφψ (r : R) : φ (numeratorHom r) = ψ (numeratorHom r) := AlgHom.congr_fun h r
  ext x
  induction x using OreLocalization.ind with | _ r s
  -- `r /ₒ s` is the inverse of the unit `s /ₒ 1` times `r /ₒ 1`.
  have hr : r /ₒ s = (((numeratorUnit s)⁻¹ : (OreLocalization S R)ˣ) : OreLocalization S R) *
      numeratorHom r := by
    have h1 := OreLocalization.one_div_mul (r := r) (s := 1) (t := s)
    rw [one_mul] at h1
    -- The inverse of `numeratorUnit s` is `1 /ₒ s` by definition.
    exact h1.symm
  have hs := congrArg (fun v : Tˣ ↦ (v⁻¹ : Tˣ).val)
    (Units.ext (hφψ s) : Units.map (φ : OreLocalization S R →* T) (numeratorUnit s) =
      Units.map (ψ : OreLocalization S R →* T) (numeratorUnit s))
  simp only [Units.coe_map_inv, MonoidHom.coe_ofClass] at hs
  rw [hr, map_mul, map_mul, hφψ, hs]

/-- The universal lift of an `R₀`-algebra map `f : R →ₐ[R₀] T` sending `S` to units of `T`
to an `R₀`-algebra map `OreLocalization S R →ₐ[R₀] T`: the `R₀`-linear form of
`OreLocalization.universalHom`. -/
def universalAlgHom (f : R →ₐ[R₀] T) (fS : S →* Tˣ) (hf : ∀ s : S, f s = fS s) :
    OreLocalization S R →ₐ[R₀] T where
  __ := universalHom f.toRingHom fS hf
  commutes' r :=
    (universalHom_commutes f.toRingHom fS hf (r := algebraMap R₀ R r)).trans (f.commutes r)

@[simp]
theorem universalAlgHom_apply (f : R →ₐ[R₀] T) (fS : S →* Tˣ) (hf : ∀ s : S, f s = fS s)
    (r : R) (s : S) : universalAlgHom f fS hf (r /ₒ s) = ((fS s)⁻¹ : Tˣ) * f r :=
  (rfl)

theorem universalAlgHom_numeratorHom (f : R →ₐ[R₀] T) (fS : S →* Tˣ)
    (hf : ∀ s : S, f s = fS s) (r : R) : universalAlgHom f fS hf (numeratorHom r) = f r :=
  universalHom_commutes f.toRingHom fS hf

@[simp]
theorem universalAlgHom_comp_numeratorAlgHom (f : R →ₐ[R₀] T) (fS : S →* Tˣ)
    (hf : ∀ s : S, f s = fS s) : (universalAlgHom f fS hf).comp (numeratorAlgHom R₀) = f :=
  AlgHom.ext <| universalAlgHom_numeratorHom f fS hf

/-- The universal lift is the only `R₀`-algebra map extending `f`. -/
theorem universalAlgHom_unique (f : R →ₐ[R₀] T) (fS : S →* Tˣ) (hf : ∀ s : S, f s = fS s)
    (φ : OreLocalization S R →ₐ[R₀] T) (hφ : ∀ r : R, φ (numeratorHom r) = f r) :
    φ = universalAlgHom f fS hf :=
  algHom_ext <| AlgHom.ext fun r ↦ (hφ r).trans (universalAlgHom_numeratorHom f fS hf r).symm

end Semiring

section Ring

variable {R₀ R : Type*} [CommSemiring R₀] [Ring R] [Algebra R₀ R] {S : Submonoid R} [OreSet S]

/-- The numerator map is injective when `S` consists of left non-zero-divisors, for instance
when `S ≤ R⁰`. -/
theorem numeratorAlgHom_injective (hS : S ≤ nonZeroDivisorsLeft R) :
    Function.Injective (numeratorAlgHom R₀ (S := S)) :=
  numeratorHom_inj hS

end Ring

section DivisionRing

variable {R₀ R D : Type*} [CommSemiring R₀] [Semiring R] [Nontrivial R] [Algebra R₀ R]
  [OreSet R⁰] [DivisionRing D] [Algebra R₀ D]

/-- An injective `R₀`-algebra map `f` from a nontrivial semiring `R`, whose non-zero-divisors
form a left Ore set, into a division ring extends to `OreLocalization R⁰ R`, as
`r /ₒ s ↦ (f s)⁻¹ * f r`. -/
noncomputable def liftAlgHom (f : R →ₐ[R₀] D) (hf : Function.Injective f) :
    OreLocalization R⁰ R →ₐ[R₀] D :=
  universalAlgHom f
    { toFun s := Units.mk0 (f s) ((map_ne_zero_iff f hf).2 (nonZeroDivisors.ne_zero s.property))
      map_one' := Units.ext (map_one f)
      map_mul' _ _ := Units.ext (map_mul f _ _) } fun _ ↦ rfl

@[simp]
theorem liftAlgHom_apply (f : R →ₐ[R₀] D) (hf : Function.Injective f) (r : R) (s : R⁰) :
    liftAlgHom f hf (r /ₒ s) = (f s)⁻¹ * f r := by
  refine (universalAlgHom_apply _ _ _ r s).trans ?_
  simp

theorem liftAlgHom_numeratorHom (f : R →ₐ[R₀] D) (hf : Function.Injective f) (r : R) :
    liftAlgHom f hf (numeratorHom r) = f r :=
  universalAlgHom_numeratorHom ..

@[simp]
theorem liftAlgHom_comp_numeratorAlgHom (f : R →ₐ[R₀] D) (hf : Function.Injective f) :
    (liftAlgHom f hf).comp (numeratorAlgHom R₀) = f :=
  universalAlgHom_comp_numeratorAlgHom ..

/-- The lift is the only `R₀`-algebra map extending `f`. -/
theorem liftAlgHom_unique (f : R →ₐ[R₀] D) (hf : Function.Injective f)
    (φ : OreLocalization R⁰ R →ₐ[R₀] D) (hφ : ∀ r : R, φ (numeratorHom r) = f r) :
    φ = liftAlgHom f hf :=
  universalAlgHom_unique _ _ _ φ hφ

end DivisionRing

end OreLocalization

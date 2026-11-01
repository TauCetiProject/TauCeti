/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Derivation.Basic
public import TauCeti.RingTheory.NovikovSeries.Functoriality

/-!
# Degree derivations of Novikov series

Let `ℓ : H →+ R` be an additive map from the exponent group into the coefficient ring. Multiplying
the coefficient at each exponent `h` by `ℓ h` is a derivation of the Novikov ring `Nov(R, H, N)`,
the *degree derivation* `TauCeti.NovikovSeries.degreeDerivation ℓ`: the Leibniz rule is the
identity `ℓ (u + v) = ℓ u + ℓ v` on the pairs of exponents contributing to a product. Since it does
not enlarge supports, the degree derivation preserves every period neighbourhood `U_C`, so it is
continuous and preserves the nonnegative subring. It is compatible with the inclusion of Novikov
series on a subgroup and with restriction along exponent homomorphisms.

Over a `ℚ`-algebra, the degree derivations along the period detect the coefficients of nonzero
period: composing `N` with a `ℚ`-linear functional `f : ℝ → ℚ` gives a degree derivation, and a
series killed by all of them vanishes at every exponent `h` with `N h ≠ 0`
(`TauCeti.NovikovSeries.coeff_eq_zero_of_forall_degreeDerivation_eq_zero`). This replaces the
derivative in the parameter of a one-parameter family: an identity between series supported in
positive periods follows from the identity between their degree derivatives.

## Main definitions

* `TauCeti.NovikovSeries.degreeDerivation ℓ`: the degree derivation along `ℓ : H →+ R`.
* `TauCeti.NovikovSeries.nonnegDegreeDerivation ℓ`: its restriction to the nonnegative subring.

## Main results

* `TauCeti.NovikovSeries.continuous_degreeDerivation`,
  `TauCeti.NovikovSeries.continuous_nonnegDegreeDerivation`: degree derivations are continuous.
* `TauCeti.NovikovSeries.degreeDerivation_algebraMap_addSubgroup`: compatibility with the inclusion
  of Novikov series on a subgroup.
* `TauCeti.NovikovSeries.comap_degreeDerivation`: compatibility with restriction.
* `TauCeti.NovikovSeries.coeff_eq_zero_of_forall_degreeDerivation_eq_zero`: the degree
  derivations along the period detect the coefficients of nonzero period.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Section 2.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti

namespace NovikovSeries

variable {R H : Type*}

section Definition

variable [CommSemiring R] [AddCommMonoid H] {N : H →+ ℝ}

/-- The *degree derivation* of Novikov series along an additive map `ℓ : H →+ R`: it multiplies
the coefficient at each exponent `h` by `ℓ h`. -/
def degreeDerivation (ℓ : H →+ R) :
    Derivation R (NovikovSeries R H N) (NovikovSeries R H N) where
  toFun a :=
    { coeff h := ℓ h * a.coeff h
      finite_lt C := (a.finite_lt C).subset fun _ hh => ⟨right_ne_zero_of_mul hh.1, hh.2⟩ }
  map_add' a b := ext fun h => mul_add _ _ _
  map_smul' r a := ext fun h => mul_left_comm _ _ _
  map_one_eq_zero' := ext fun h => by
    classical
    -- `coeff_degreeDerivation` is not available inside the definition, so unfold `toFun` by
    -- definition: the coefficient at `h` of the image of `1` is `ℓ h * coeff 1 h`.
    change ℓ h * (1 : NovikovSeries R H N).coeff h = 0
    rw [coeff_one]
    split_ifs with hh <;> simp [hh]
  leibniz' a b := ext fun h => by
    classical
    -- Unfold `toFun` the same way on all three images; the scalar actions `a • D b` and
    -- `b • D a` of the Leibniz rule are multiplication in the Novikov ring by definition.
    change ℓ h * (a * b).coeff h = (a * _).coeff h + (b * _).coeff h
    set s := (finite_setOf_add_eq a b h).toFinset
    have hs : ∀ p ∈ s, p.1 + p.2 = h := fun p hp => ((Set.Finite.mem_toFinset _).1 hp).1
    have hmem (u v : H) (huv : u + v = h) (hu : a.coeff u ≠ 0) (hv : b.coeff v ≠ 0) :
        (u, v) ∈ s := (Set.Finite.mem_toFinset _).2 ⟨huv, hu, hv⟩
    rw [mul_comm b, coeff_mul, coeff_mul_eq_sum (s := s) hs fun u v huv hu hv =>
      hmem u v huv hu (right_ne_zero_of_mul hv), coeff_mul_eq_sum (s := s) hs
      fun u v huv hu hv => hmem u v huv (right_ne_zero_of_mul hu) hv, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [← hs p hp, map_add]
    ring

/-- The coefficient of the degree derivative at `h` is `ℓ h` times the coefficient at `h`. -/
@[simp]
theorem coeff_degreeDerivation (ℓ : H →+ R) (a : NovikovSeries R H N) (h : H) :
    (degreeDerivation ℓ a).coeff h = ℓ h * a.coeff h :=
  (rfl)

/-- The degree derivation multiplies the monomial `r e^g` by `ℓ g`. -/
@[simp]
theorem degreeDerivation_single (ℓ : H →+ R) (g : H) (r : R) :
    degreeDerivation ℓ (single g r : NovikovSeries R H N) = single g (ℓ g * r) := by
  classical
  ext h
  rw [coeff_degreeDerivation, coeff_single, coeff_single]
  by_cases hh : h = g
  · subst hh
    simp
  · simp [Pi.single_eq_of_ne hh]

end Definition

section Ring

variable [CommRing R] [AddCommMonoid H] {N : H →+ ℝ} (ℓ : H →+ R) {C : ℝ}
  {a : NovikovSeries R H N}

/-- The degree derivation preserves each period neighbourhood `U_C`. -/
theorem degreeDerivation_mem_periodFiltration (ha : a ∈ periodFiltration R N C) :
    degreeDerivation ℓ a ∈ periodFiltration R N C :=
  mem_periodFiltration.2 fun h hh => by
    rw [coeff_degreeDerivation, mem_periodFiltration.1 ha h hh, mul_zero]

/-- Degree derivations are continuous for the period topology. -/
@[fun_prop]
theorem continuous_degreeDerivation :
    Continuous (degreeDerivation ℓ : NovikovSeries R H N → NovikovSeries R H N) := by
  refine continuous_of_continuousAt_zero (degreeDerivation ℓ) ?_
  rw [ContinuousAt, map_zero]
  exact (hasBasis_nhds_zero.tendsto_iff hasBasis_nhds_zero).2 fun C _ =>
    ⟨C, trivial, fun _ ha => degreeDerivation_mem_periodFiltration ℓ ha⟩

/-- The degree derivation preserves the nonnegative subring. -/
theorem degreeDerivation_mem_nonnegSubring (ha : a ∈ nonnegSubring R N) :
    degreeDerivation ℓ a ∈ nonnegSubring R N :=
  mem_nonnegSubring.2 fun h hh => by
    rw [coeff_degreeDerivation, mem_nonnegSubring.1 ha h hh, mul_zero]

/-- The degree derivation along `ℓ`, restricted to the nonnegative subring. -/
def nonnegDegreeDerivation : Derivation ℤ (nonnegSubring R N) (nonnegSubring R N) :=
  Derivation.mk'
    { toFun a := ⟨degreeDerivation ℓ a, degreeDerivation_mem_nonnegSubring ℓ a.2⟩
      map_add' a b := Subtype.ext (map_add (degreeDerivation ℓ) _ _)
      map_smul' n a := Subtype.ext (by simp) }
    fun a b => Subtype.ext (by simp [Derivation.leibniz, smul_eq_mul])

/-- The restricted degree derivation agrees with the degree derivation on Novikov series. -/
@[simp]
theorem coe_nonnegDegreeDerivation (a : nonnegSubring R N) :
    (nonnegDegreeDerivation ℓ a : NovikovSeries R H N) = degreeDerivation ℓ a :=
  (rfl)

/-- The restricted degree derivation is continuous for the subspace topology. -/
@[fun_prop]
theorem continuous_nonnegDegreeDerivation :
    Continuous (nonnegDegreeDerivation (N := N) ℓ) :=
  ((continuous_degreeDerivation ℓ).comp continuous_subtype_val).subtype_mk _

end Ring

section Subgroup

variable [CommSemiring R] [AddCommGroup H] {N : H →+ ℝ} {K : AddSubgroup H}

/-- The degree derivation commutes with the inclusion of Novikov series on a subgroup `K`, for the
restriction of `ℓ` to `K`. -/
theorem degreeDerivation_algebraMap_addSubgroup (ℓ : H →+ R)
    (b : NovikovSeries R K (N.comp K.subtype)) :
    degreeDerivation ℓ (algebraMap _ (NovikovSeries R H N) b) =
      algebraMap _ _ (degreeDerivation (ℓ.comp K.subtype) b) := by
  ext h
  by_cases hh : h ∈ K
  · lift h to K using hh
    simp
  · simp [coeff_algebraMap_addSubgroup_of_notMem _ hh]

end Subgroup

section Comap

variable [CommSemiring R] [AddCommGroup H] {N : H →+ ℝ} {H' : Type*} [AddCommMonoid H']
  {N' : H' →+ ℝ}

/-- The degree derivation commutes with restriction along `φ`, for the composite `ℓ ∘ φ`. -/
theorem comap_degreeDerivation (φ : H →+ H') (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h)
    (hker : (φ.ker : Set H).Finite) (ℓ : H' →+ R) (b : NovikovSeries R H' N') :
    comap φ hφ hker (degreeDerivation ℓ b) = degreeDerivation (ℓ.comp φ) (comap φ hφ hker b) := by
  ext
  simp

end Comap

section Rat

variable [CommRing R] [Algebra ℚ R] [AddCommMonoid H] {N : H →+ ℝ}

/-- Over a `ℚ`-algebra, the degree derivations along the period detect the coefficients of nonzero
period: if `a` is killed by the degree derivation along `f ∘ N` for every `ℚ`-linear functional
`f : ℝ → ℚ`, then `a` vanishes at every exponent `h` with `N h ≠ 0`. -/
theorem coeff_eq_zero_of_forall_degreeDerivation_eq_zero {a : NovikovSeries R H N}
    (ha : ∀ f : Module.Dual ℚ ℝ,
      degreeDerivation (((algebraMap ℚ R).toAddMonoidHom.comp f.toAddMonoidHom).comp N) a = 0)
    {h : H} (hh : N h ≠ 0) : a.coeff h = 0 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero ℚ hh
  have := congrArg (coeff · h) (ha f)
  simp only [coeff_degreeDerivation, AddMonoidHom.coe_comp, Function.comp_apply,
    RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass, LinearMap.toAddMonoidHom_coe,
    coeff_zero] at this
  exact ((IsUnit.mk0 _ hf).map (algebraMap ℚ R)).mul_right_eq_zero.1 this

end Rat

end NovikovSeries

end TauCeti

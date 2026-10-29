/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Periodicity

/-!
# Connes' operator `B` and the exactness of the SBI sequence

Let `A` be a unital algebra. This file constructs the map
`B : HH^(m+1)(A, Hom_R(A, M)) → H^m(Tot)` from Hochschild cohomology to the cohomology of the
total complex of Connes' cyclic bicomplex, and completes the proof that the SBI sequence

`0 → H^0(Tot) →I HH^0 → 0 → H^1(Tot) →I HH^1 →B H^0(Tot) →S H^2(Tot) →I HH^2 →B H^1(Tot) → ⋯`

of the bicomplex is exact at every term. Exactness at `H^(m+2)(Tot)`, between `S` and `I`, is
`TauCeti.exact_cyclicTotalHomologyPeriodicity_homologyMap_cyclicTotalComplexToHochschild`; this
file proves it at `HH^(m+1)`, at `H^m(Tot)` between `B` and `S`, and at the initial terms
`H^0(Tot)`, `HH^0` and `H^1(Tot)`.

The map `B` is Connes' operator on Hochschild cohomology,
`TauCeti.hochschildCohomology.connesB`, followed by the inclusion of cyclic cochains into column
zero of the total complex. It is the connecting map of the sequence: a Hochschild cocycle `φ` of
degree `m + 1` lifts to the total cochain `φ + s (1 - λ) φ` in columns zero and one, where `s` is
the contraction of the bar complex, and the total differential of this lift is `N s (1 - λ) φ = B φ`
in column two, the image of `B φ` under the periodicity map. The other ingredient is that the bar
complex in column one is contractible: if the total differential of a total cochain vanishing in
column zero lies in the image of the periodicity map, then its preimage is a total coboundary
(or zero, in degree zero).

Over a ring containing `ℚ`, the total cohomology is cyclic cohomology
(`TauCeti.quasiIso_cyclicCochainComplexToTotal`), so the exactness at `HH^(m+1)` gives the
exactness of `HC^(m+1) →I HH^(m+1) →B HC^m` for the maps `TauCeti.cyclicCohomology.toHochschild`
and `TauCeti.hochschildCohomology.connesB` defined by cyclic cochains. (Exactness at `HC^1`, the
injectivity of `I`, holds over every commutative ring, see
`TauCeti.cyclicCohomology.injective_toHochschild_one`.)
The periodicity map of the bicomplex is the shift of columns; it is not compared here with
Connes' operator `S`, normalized as the exterior product with the cyclic `2`-cocycle
`(a₀, a₁, a₂) ↦ a₀a₁a₂`.

## Main definitions

* `TauCeti.cyclicTotalHomologyConnesB`: the map `B : HH^(m+1)(A, Hom_R(A, M)) → H^m(Tot)`.

## Main results

* `TauCeti.cyclicTotalHomologyConnesB_mk`: `B` sends the class of a Hochschild cocycle `φ` to the
  class of the cyclic cocycle `B φ` in column zero.
* `TauCeti.cyclicTotalHomologyMk_eq_zero_iff`: for a unital algebra, a total cocycle has zero class
  exactly when its image under the periodicity map is the total differential of a total cochain
  vanishing in column zero.
* `TauCeti.exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB`:
  `H^(m+1)(Tot) → HH^(m+1) → H^m(Tot)` is exact.
* `TauCeti.exact_cyclicTotalHomologyConnesB_cyclicTotalHomologyPeriodicity`:
  `HH^(m+1) → H^m(Tot) → H^(m+2)(Tot)` is exact.
* `TauCeti.injective_cyclicTotalHomologyPeriodicity_of_isZero`,
  `TauCeti.surjective_cyclicTotalHomologyPeriodicity_of_isZero`: `S : H^m(Tot) → H^(m+2)(Tot)` is
  injective when `HH^(m+1)` vanishes and surjective when `HH^(m+2)` vanishes.
* `TauCeti.isIso_homologyMap_cyclicTotalComplexToHochschild_zero`,
  `TauCeti.injective_homologyMap_cyclicTotalComplexToHochschild_one`: `I` is an isomorphism in
  degree zero and injective in degree one.
* `TauCeti.cyclicCohomology.exact_toHochschild_connesB`: over a ring containing `ℚ`,
  `HC^(m+1) → HH^(m+1) → HC^m` is exact.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §§2.1–2.2.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

universe u

/-! ### Cochain-level constructions -/

section Cochains

variable {R A M : Type*} [CommRing R] [Semiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- The lift `φ + s (1 - λ) φ` of a Hochschild `(m + 1)`-cochain `φ` to a total cochain of degree
`m + 1`, with `φ` in column zero and `s (1 - λ) φ` in column one. -/
private def cyclicTotalLift {m : ℕ} (φ : MultilinearMap R (fun _ : Fin (m + 1 + 1) ↦ A) M) :
    cyclicTotalCochains R A M (m + 1) :=
  ⟨Pi.single (m + 1) φ +
      Pi.single m (barContraction R A M m ((1 - cyclicOperator R A M (m + 1)) φ)),
    add_mem (single_mem_cyclicTotalCochains le_rfl φ)
      (single_mem_cyclicTotalCochains (Nat.le_succ m) _)⟩

omit [IsScalarTower R A A] [SMulCommClass R A A] in
/-- The column-zero component of the lift of `φ` is `φ`. -/
private theorem cyclicTotalLift_apply_column_zero {m : ℕ}
    (φ : MultilinearMap R (fun _ : Fin (m + 1 + 1) ↦ A) M) :
    (cyclicTotalLift φ).1 (m + 1) = φ := by
  simp [cyclicTotalLift]

omit [IsScalarTower R A A] [SMulCommClass R A A] in
/-- The column-one component of the lift of `φ` is `s (1 - λ) φ`. -/
private theorem cyclicTotalLift_apply_column_one {m : ℕ}
    (φ : MultilinearMap R (fun _ : Fin (m + 1 + 1) ↦ A) M) :
    (cyclicTotalLift φ).1 m = barContraction R A M m ((1 - cyclicOperator R A M (m + 1)) φ) := by
  simp [cyclicTotalLift]

/-- **The total differential of the lift.** For a Hochschild cocycle `φ`, the total differential
of `φ + s (1 - λ) φ` is `N s (1 - λ) φ = B φ` in row `m`, column two. -/
private theorem coe_cyclicTotalDifferential_cyclicTotalLift {m : ℕ}
    {φ : MultilinearMap R (fun _ : Fin (m + 1 + 1) ↦ A) M}
    (hφ : hochschildCoboundary R A M (m + 1) φ = 0) :
    (cyclicTotalDifferential R A M (m + 1) (cyclicTotalLift φ)).1 =
      Pi.single m (connesB R A M m φ) := by
  -- the column-one component `ψ = s (1 - λ) φ` satisfies `b' ψ = (1 - λ) φ`
  have hψ : barCoboundary R A M m
      (barContraction R A M m ((1 - cyclicOperator R A M (m + 1)) φ)) =
        (1 - cyclicOperator R A M (m + 1)) φ := by
    have hb := LinearMap.congr_fun
      (one_sub_cyclicOperator_comp_hochschildCoboundary R A M (m + 1)) φ
    simp only [LinearMap.comp_apply, hφ, map_zero] at hb
    have h := barCoboundary_barContraction_add_barContraction_barCoboundary
      ((1 - cyclicOperator R A M (m + 1)) φ)
    rwa [← hb, map_zero, add_zero] at h
  funext q
  obtain hq | hq | hq | hq | hq : q < m ∨ q = m ∨ q = m + 1 ∨ q = m + 2 ∨ m + 2 < q := by omega
  · rw [Pi.single_eq_of_ne hq.ne]
    cases q with
    | zero =>
      simp [cyclicTotalLift, Pi.single_eq_of_ne (show 0 ≠ m by omega)]
    | succ q =>
      simp [cyclicTotalLift, Pi.single_eq_of_ne (show q ≠ m by omega),
        Pi.single_eq_of_ne (show q + 1 ≠ m by omega), Pi.single_eq_of_ne (show q ≠ m + 1 by omega),
        Pi.single_eq_of_ne (show q + 1 ≠ m + 1 by omega)]
  · subst q
    rw [Pi.single_eq_same]
    cases m with
    | zero =>
      simp [cyclicTotalLift, connesB_apply]
    | succ m =>
      have h₂ : m + 1 + 1 - m = 2 := by omega
      have h₁ : m + 1 + 1 - (m + 1) = 1 := by omega
      simp [cyclicTotalLift, h₁, h₂, connesB_apply,
        Pi.single_eq_of_ne (show m ≠ m + 1 + 1 by omega)]
  · subst q
    rw [Pi.single_eq_of_ne (show m + 1 ≠ m by omega), cyclicTotalDifferential_apply_succ]
    have h₁ : m + 1 - m = 1 := by omega
    rw [h₁, Nat.sub_self, cyclicTotalLift_apply_column_zero, cyclicTotalLift_apply_column_one,
      cyclicBicomplexVertical_of_odd odd_one, cyclicBicomplexHorizontal_of_even Even.zero,
      LinearMap.neg_apply, hψ, neg_add_cancel]
  · subst q
    rw [Pi.single_eq_of_ne (show m + 2 ≠ m by omega), cyclicTotalDifferential_apply_succ]
    simp [cyclicTotalLift, hφ]
  · rw [Pi.single_eq_of_ne (show q ≠ m by omega)]
    exact coe_cyclicTotalCochains_apply_of_lt _ hq

/-- Let `y` be a total cochain of degree `k + 1` vanishing in column zero whose total differential
vanishes in column one. Then its column-one component is a cocycle for the bar coboundary. -/
private theorem barCoboundary_eq_zero_of_cyclicTotalDifferential_apply_eq_zero {k : ℕ}
    (y : cyclicTotalCochains R A M (k + 1)) (hy : y.1 (k + 1) = 0)
    (h : (cyclicTotalDifferential R A M (k + 1) y).1 (k + 1) = 0) :
    barCoboundary R A M k (y.1 k) = 0 := by
  have h₁ : k + 1 - k = 1 := by omega
  rwa [cyclicTotalDifferential_apply_succ, h₁, Nat.sub_self, hy, map_zero, add_zero,
    cyclicBicomplexVertical_of_odd odd_one, LinearMap.neg_apply, neg_eq_zero] at h

/-- A total cochain of degree one vanishing in column zero whose total differential vanishes in
column one is zero: the bar coboundary is injective on `0`-cochains. -/
private theorem eq_zero_of_cyclicTotalDifferential_apply_one_eq_zero
    (y : cyclicTotalCochains R A M 1) (hy : y.1 1 = 0)
    (h : (cyclicTotalDifferential R A M 1 y).1 1 = 0) : y = 0 := by
  -- `y 0 = s (b' (y 0)) = 0`
  have hy₀ : y.1 0 = 0 := by
    rw [← barContraction_barCoboundary_zero (y.1 0),
      barCoboundary_eq_zero_of_cyclicTotalDifferential_apply_eq_zero y hy h, map_zero]
  refine Subtype.ext (funext fun q ↦ ?_)
  obtain rfl | rfl | hq : q = 0 ∨ q = 1 ∨ 1 < q := by omega
  · exact hy₀
  · exact hy
  · exact coe_cyclicTotalCochains_apply_of_lt y hq

/-- **The bar complex in column one is contractible, degree zero.** Let `y` be a total cochain of
degree one vanishing in column zero whose total differential is the image under the periodicity map
of a total cochain `v` of degree zero. Then `v` vanishes. -/
private theorem eq_zero_of_coe_eq_coe_cyclicTotalDifferential (v : cyclicTotalCochains R A M 0)
    (y : cyclicTotalCochains R A M 1) (hy : y.1 1 = 0)
    (h : v.1 = (cyclicTotalDifferential R A M 1 y).1) : v = 0 := by
  rw [eq_zero_of_cyclicTotalDifferential_apply_one_eq_zero y hy
    (by rw [← h]; exact coe_cyclicTotalCochains_apply_of_lt v one_pos), map_zero] at h
  exact Subtype.ext h

/-- **The bar complex in column one is contractible.** Let `y` be a total cochain of degree
`n + 2` vanishing in column zero whose total differential is the image under the periodicity map of
a total cochain `v` of degree `n + 1`. Then `v` is a total coboundary. -/
private theorem exists_cyclicTotalDifferential_eq_of_coe_eq_coe_cyclicTotalDifferential {n : ℕ}
    (v : cyclicTotalCochains R A M (n + 1)) (y : cyclicTotalCochains R A M (n + 2))
    (hy : y.1 (n + 2) = 0) (h : v.1 = (cyclicTotalDifferential R A M (n + 2) y).1) :
    ∃ w, cyclicTotalDifferential R A M n w = v := by
  -- killing column one of `y` does not change its total differential
  obtain ⟨w, z, hw⟩ := exists_cyclicTotalPeriodicity_eq_add_cyclicTotalDifferential y hy
    (barCoboundary_eq_zero_of_cyclicTotalDifferential_apply_eq_zero y hy
      (by rw [← h]; exact coe_cyclicTotalCochains_apply_of_lt v (by omega)))
  refine ⟨w, cyclicTotalPeriodicity_injective R A M (n + 1) (Subtype.ext ?_)⟩
  rw [← cyclicTotalDifferential_cyclicTotalPeriodicity, hw, map_add,
    cyclicTotalDifferential_cyclicTotalDifferential, add_zero, ← h,
    coe_cyclicTotalPeriodicity_apply]

end Cochains

/-! ### The initial terms of the SBI sequence -/

section NonUnital

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- In degree zero, the projection onto column zero is an isomorphism
`H^0(Tot) → HH^0(A, Hom_R(A, M))`: every `0`-cochain is cyclic, and there are no coboundaries in
degree zero. This is the exactness of the SBI sequence at `H^0(Tot)` and at `HH^0`. -/
instance isIso_homologyMap_cyclicTotalComplexToHochschild_zero :
    IsIso (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) 0) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(injective_iff_map_eq_zero _).2 fun c hc ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective 0 c
    rw [homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMk,
      hochschildCohomology.mk_eq_zero_iff, hochschildCoboundaries_zero, Submodule.mem_bot] at hc
    -- a total cochain of degree zero is concentrated in row zero
    rw [cyclicTotalHomologyMk_zero_eq_zero_iff]
    refine Subtype.ext (Subtype.ext (funext fun q ↦ ?_))
    cases q with
    | zero => exact hc
    | succ q => exact coe_cyclicTotalCochains_apply_of_lt x.1 q.succ_pos
  · obtain ⟨φ, rfl⟩ := hochschildCohomology.mk_surjective R A M 0 c
    have hφ : φ.1 ∈ cyclicCochains R A M 0 := by simp
    refine ⟨cyclicTotalHomologyMk R A M 0 ⟨_, cyclicCochainsToTotal_mem_ker
      ⟨⟨φ, hφ⟩, (mem_cyclicCocycles_iff R A M).2 (mem_hochschildCocycles_iff.1 φ.2)⟩⟩, ?_⟩
    rw [homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMk]
    congr 1
    exact Subtype.ext (by simp)

end NonUnital

section Unital

variable {R : Type*} {A : Type u} {M : Type*} [CommRing R] [Semiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- A total cocycle of degree `m` has zero class exactly when the image under the periodicity map is
the total differential of a total cochain vanishing in column zero. -/
theorem cyclicTotalHomologyMk_eq_zero_iff {m : ℕ}
    (x : LinearMap.ker (cyclicTotalDifferential R A M m)) :
    cyclicTotalHomologyMk R A M m x = 0 ↔ ∃ u : cyclicTotalCochains R A M (m + 1),
      u.1 (m + 1) = 0 ∧ (cyclicTotalDifferential R A M (m + 1) u).1 = x.1.1 := by
  cases m with
  | zero =>
    rw [cyclicTotalHomologyMk_zero_eq_zero_iff]
    refine ⟨fun hx ↦ ⟨0, by simp, by simp [hx]⟩, fun ⟨u, hu, hux⟩ ↦ ?_⟩
    exact Subtype.ext (eq_zero_of_coe_eq_coe_cyclicTotalDifferential x.1 u hu hux.symm)
  | succ n =>
    rw [cyclicTotalHomologyMk_succ_eq_zero_iff]
    refine ⟨fun ⟨w, hw⟩ ↦ ⟨cyclicTotalPeriodicity R A M n w, ?_, ?_⟩, fun ⟨u, hu, hux⟩ ↦
      exists_cyclicTotalDifferential_eq_of_coe_eq_coe_cyclicTotalDifferential x.1 u hu hux.symm⟩
    · rw [coe_cyclicTotalPeriodicity_apply]
      exact coe_cyclicTotalCochains_apply_of_lt w (by omega)
    · rw [cyclicTotalDifferential_cyclicTotalPeriodicity, coe_cyclicTotalPeriodicity_apply, hw]

/-- In degree one, the projection onto column zero `H^1(Tot) → HH^1(A, Hom_R(A, M))` is injective:
a total cocycle of degree one vanishing in column zero is zero, since the bar coboundary is
injective on `0`-cochains of a unital algebra. This is the exactness of the SBI sequence at
`H^1(Tot)`. -/
theorem injective_homologyMap_cyclicTotalComplexToHochschild_one :
    Function.Injective
      (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) 1) := by
  refine (injective_iff_map_eq_zero _).2 fun c hc ↦ ?_
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective 1 c
  rw [homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMk,
    hochschildCohomology.mk_eq_zero_iff, mem_hochschildCoboundaries_succ_iff] at hc
  obtain ⟨χ, hχ⟩ := hc
  -- the cochain `χ` in column zero has total differential `b χ = x 1` in column zero
  let w : cyclicTotalCochains R A M 0 := ⟨Pi.single 0 χ, single_mem_cyclicTotalCochains le_rfl χ⟩
  rw [cyclicTotalHomologyMk_succ_eq_zero_iff]
  refine ⟨w, (sub_eq_zero.1 (eq_zero_of_cyclicTotalDifferential_apply_one_eq_zero
    (x.1 - cyclicTotalDifferential R A M 0 w) ?_ ?_)).symm⟩
  · simp [w, hχ]
  · simp [LinearMap.mem_ker.1 x.2]

/-- For a unital algebra, the periodicity map `S : H^m(Tot) → H^(m+2)(Tot)` is surjective when
`HH^(m+2)(A, Hom_R(A, M))` vanishes. -/
theorem surjective_cyclicTotalHomologyPeriodicity_of_isZero {m : ℕ}
    (h : Limits.IsZero (hochschildCohomology R A M (m + 2))) :
    Function.Surjective (cyclicTotalHomologyPeriodicity R A M m) := by
  have := ModuleCat.isZero_iff_subsingleton.1 h
  exact fun c ↦ (exact_cyclicTotalHomologyPeriodicity_homologyMap_cyclicTotalComplexToHochschild
    R A M m c).1 (Subsingleton.elim _ 0)

end Unital

/-! ### The map `B` and the exactness of the SBI sequence -/

section Exactness

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M]
  [Module R M]

/-- The map `B : HH^(m+1)(A, Hom_R(A, M)) → H^m(Tot)` of the SBI sequence of the cyclic
bicomplex: Connes' operator `B` on Hochschild cohomology, followed by the inclusion of cyclic
cochains into column zero of the total complex. -/
def cyclicTotalHomologyConnesB (m : ℕ) :
    hochschildCohomology R A M (m + 1) ⟶ (cyclicTotalComplex R A M).homology m :=
  hochschildCohomology.connesB R A M m ≫
    HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) m

/-- The map `B` of the cyclic bicomplex is Connes' operator `B` on Hochschild cohomology followed
by the map induced on cohomology by the inclusion of cyclic cochains into column zero. -/
theorem cyclicTotalHomologyConnesB_def (m : ℕ) :
    cyclicTotalHomologyConnesB R A M m = hochschildCohomology.connesB R A M m ≫
      HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) m :=
  (rfl)

variable {R A M}

/-- The map `B` sends the class of a Hochschild cocycle `φ` to the class of the cyclic cocycle
`B φ`, included into column zero of the total complex. -/
@[simp]
theorem cyclicTotalHomologyConnesB_mk {m : ℕ} (φ : hochschildCocycles R A M (m + 1)) :
    cyclicTotalHomologyConnesB R A M m (hochschildCohomology.mk R A M (m + 1) φ) =
      cyclicTotalHomologyMk R A M m ⟨_, cyclicCochainsToTotal_mem_ker
        ⟨⟨connesB R A M m φ, connesB_mem_cyclicCochains _⟩, connesB_mem_cyclicCocycles φ.2⟩⟩ := by
  rw [cyclicTotalHomologyConnesB_def, ModuleCat.comp_apply, hochschildCohomology.connesB_mk,
    homologyMap_cyclicCochainComplexToTotal_mk]

/-- **Exactness of `H^(m+1)(Tot) → HH^(m+1) → H^m(Tot)`.** For a unital algebra, a Hochschild
class is killed by `B` exactly when it is the projection onto column zero of a class in the
cohomology of the total cyclic bicomplex. -/
theorem exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB (m : ℕ) :
    Function.Exact (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) (m + 1))
      (cyclicTotalHomologyConnesB R A M m) := by
  refine fun c ↦ ⟨fun hc ↦ ?_, ?_⟩
  · obtain ⟨φ, rfl⟩ := hochschildCohomology.mk_surjective R A M (m + 1) c
    rw [cyclicTotalHomologyConnesB_mk, cyclicTotalHomologyMk_eq_zero_iff] at hc
    obtain ⟨u, hu, hDu⟩ := hc
    -- the lift of `φ` minus `u` is a total cocycle whose column-zero component is `φ`
    have hx : cyclicTotalLift φ.1 - u ∈ LinearMap.ker (cyclicTotalDifferential R A M (m + 1)) := by
      refine LinearMap.mem_ker.2 (Subtype.ext ?_)
      rw [map_sub, Submodule.coe_sub, coe_cyclicTotalDifferential_cyclicTotalLift
        (mem_hochschildCocycles_iff.1 φ.2), hDu]
      simp
    refine ⟨cyclicTotalHomologyMk R A M (m + 1) ⟨_, hx⟩, ?_⟩
    rw [homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMk]
    congr 1
    exact Subtype.ext (by simp [cyclicTotalLift_apply_column_zero, hu])
  · rintro ⟨c, rfl⟩
    obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective (m + 1) c
    rw [homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMk,
      cyclicTotalHomologyConnesB_mk, cyclicTotalHomologyMk_eq_zero_iff]
    have hD : cyclicTotalDifferential R A M (m + 1) x.1 = 0 := LinearMap.mem_ker.1 x.2
    have hφ : hochschildCoboundary R A M (m + 1) (x.1.1 (m + 1)) = 0 := by
      rw [← cyclicTotalToHochschild_apply, ← cyclicTotalToHochschild_cyclicTotalDifferential, hD,
        map_zero]
    refine ⟨cyclicTotalLift (x.1.1 (m + 1)) - x.1, ?_, ?_⟩
    · rw [Submodule.coe_sub, Pi.sub_apply, cyclicTotalLift_apply_column_zero, sub_self]
    · simp only [map_sub, hD, sub_zero]
      rw [coe_cyclicTotalDifferential_cyclicTotalLift hφ]
      simp

variable (R A M) in
/-- The composite `B ∘ I : H^(m+1)(Tot) → HH^(m+1) → H^m(Tot)` vanishes. -/
@[reassoc (attr := simp)]
theorem homologyMap_cyclicTotalComplexToHochschild_comp_cyclicTotalHomologyConnesB (m : ℕ) :
    HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) (m + 1) ≫
      cyclicTotalHomologyConnesB R A M m = 0 :=
  ModuleCat.hom_ext (LinearMap.ext fun c ↦
    (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB
      m).apply_apply_eq_zero c)

/-- **Exactness of `HH^(m+1) → H^m(Tot) → H^(m+2)(Tot)`.** For a unital algebra, a class in the
cohomology of the total cyclic bicomplex is killed by the periodicity map exactly when it is the
image under `B` of a Hochschild class. -/
theorem exact_cyclicTotalHomologyConnesB_cyclicTotalHomologyPeriodicity (m : ℕ) :
    Function.Exact (cyclicTotalHomologyConnesB R A M m)
      (cyclicTotalHomologyPeriodicity R A M m) := by
  refine fun c ↦ ⟨fun hc ↦ ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective m c
    rw [cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMk,
      cyclicTotalHomologyMk_succ_eq_zero_iff] at hc
    obtain ⟨y, hy⟩ := hc
    -- the column-zero component of `y` is a Hochschild cocycle
    have hφ : hochschildCoboundary R A M (m + 1) (y.1 (m + 1)) = 0 := by
      rw [← cyclicTotalToHochschild_apply, ← cyclicTotalToHochschild_cyclicTotalDifferential,
        cyclicTotalToHochschild_apply, hy]
      rw [Subtype.coe_mk, coe_cyclicTotalPeriodicity_apply]
      exact coe_cyclicTotalCochains_apply_of_lt x.1 (by omega)
    refine ⟨hochschildCohomology.mk R A M (m + 1) ⟨_, mem_hochschildCocycles_iff.2 hφ⟩, ?_⟩
    rw [← sub_eq_zero, cyclicTotalHomologyConnesB_mk, ← map_sub,
      cyclicTotalHomologyMk_eq_zero_iff]
    refine ⟨cyclicTotalLift (y.1 (m + 1)) - y, by simp [cyclicTotalLift_apply_column_zero], ?_⟩
    rw [map_sub, Submodule.coe_sub, coe_cyclicTotalDifferential_cyclicTotalLift hφ, hy]
    simp
  · rintro ⟨c, rfl⟩
    obtain ⟨φ, rfl⟩ := hochschildCohomology.mk_surjective R A M (m + 1) c
    rw [cyclicTotalHomologyConnesB_mk, cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMk,
      cyclicTotalHomologyMk_succ_eq_zero_iff]
    refine ⟨cyclicTotalLift φ.1, Subtype.ext ?_⟩
    rw [coe_cyclicTotalDifferential_cyclicTotalLift (mem_hochschildCocycles_iff.1 φ.2)]
    simp

variable (R A M) in
/-- The composite `S ∘ B : HH^(m+1) → H^m(Tot) → H^(m+2)(Tot)` vanishes. -/
@[reassoc (attr := simp)]
theorem cyclicTotalHomologyConnesB_comp_cyclicTotalHomologyPeriodicity (m : ℕ) :
    cyclicTotalHomologyConnesB R A M m ≫ cyclicTotalHomologyPeriodicity R A M m = 0 :=
  ModuleCat.hom_ext (LinearMap.ext
    (exact_cyclicTotalHomologyConnesB_cyclicTotalHomologyPeriodicity m).apply_apply_eq_zero)

/-- For a unital algebra, the periodicity map `S : H^m(Tot) → H^(m+2)(Tot)` is injective when
`HH^(m+1)(A, Hom_R(A, M))` vanishes. -/
theorem injective_cyclicTotalHomologyPeriodicity_of_isZero {m : ℕ}
    (h : Limits.IsZero (hochschildCohomology R A M (m + 1))) :
    Function.Injective (cyclicTotalHomologyPeriodicity R A M m) := by
  refine (injective_iff_map_eq_zero _).2 fun c hc ↦ ?_
  obtain ⟨b, rfl⟩ := (exact_cyclicTotalHomologyConnesB_cyclicTotalHomologyPeriodicity m c).1 hc
  have := ModuleCat.isZero_iff_subsingleton.1 h
  rw [Subsingleton.elim b 0, map_zero]

/-- **Exactness of `HC^(m+1) → HH^(m+1) → HC^m`.** For a unital algebra over a ring containing
`ℚ`, a Hochschild class is killed by Connes' operator `B` exactly when it is the image under `I`
of a cyclic cohomology class. -/
theorem cyclicCohomology.exact_toHochschild_connesB [Algebra ℚ R] (m : ℕ) :
    Function.Exact (cyclicCohomology.toHochschild R A M (m + 1))
      (hochschildCohomology.connesB R A M m) := by
  refine (LinearMap.exact_iff_of_surjective_of_bijective_of_injective _ _ _ _
    (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) (m + 1)).hom LinearMap.id
    (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) m).hom ?_ ?_
    (bijective_homologyMap_cyclicCochainComplexToTotal R A M (m + 1)).2 Function.bijective_id
    (bijective_homologyMap_cyclicCochainComplexToTotal R A M m).1).2
    (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB m)
  · rw [LinearMap.id_comp,
      ← homologyMap_cyclicCochainComplexToTotal_comp_homologyMap_cyclicTotalComplexToHochschild]
    exact (ModuleCat.hom_comp _ _).symm
  · rw [LinearMap.comp_id, cyclicTotalHomologyConnesB_def]
    exact ModuleCat.hom_comp _ _

end Exactness

end TauCeti

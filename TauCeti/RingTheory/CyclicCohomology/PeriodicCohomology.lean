/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.ExactSequence
public import TauCeti.RingTheory.CyclicCohomology.GroundRing
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Periodic cyclic cohomology

The periodicity map `S : H^m(Tot) → H^(m+2)(Tot)` of Connes' cyclic bicomplex
(`TauCeti.cyclicTotalHomologyPeriodicity`) makes the cohomology of the total complex in the
degrees of a fixed parity into a direct system

`H^n(Tot) →S H^(n+2)(Tot) →S H^(n+4)(Tot) →S ⋯`.

Its direct limit is the periodic cyclic cohomology `HP^n(A; M)`.

Every class in `HP^n` comes from a stage `H^(n+2k)(Tot)`, a class at a stage maps to zero
exactly when some iterate of `S` kills it, and `HP^(n+2) ≅ HP^n`. For a unital algebra the SBI
sequence controls the transition maps: `S : H^m(Tot) → H^(m+2)(Tot)` is injective when `HH^(m+1)`
vanishes and surjective when `HH^(m+2)` vanishes. Hence if the Hochschild cohomology
`HH^m(A, Hom_R(A, M))` vanishes in all degrees `m > n + 2k`, the stage `H^(n+2k)(Tot)` already
computes `HP^n`. This applies to the ground ring `R`, whose Hochschild cohomology vanishes in
positive degree: `HP^n(R; M)` is `H^n(Tot)`, and `HP^1(R; M) = 0`.

Over a `ℚ`-algebra, Connes' periodicity operator `TauCeti.cyclicCohomology.periodicity` corresponds
under `TauCeti.cyclicCochainComplexToTotal` to `-((m + 1) * (m + 2))` times the bicomplex
periodicity map
(`TauCeti.cyclicCohomology.periodicity_comp_homologyMap_cyclicCochainComplexToTotal`). Rescaling
the `k`-th stage inclusion by `TauCeti.periodicComparisonScalar n k` — equal to `(-1)^m / (2m)!`
in even degree `2m` (`n = 0`) and `(-1)^k / (2k + 1)!` relative to degree one (`n = 1`) — produces
canonical maps `TauCeti.periodicCyclicCohomology.fromCyclicCohomology` compatible with Connes'
operator `S`, exhibiting `HP^n(A; M)` as the direct limit of `HC^(n+2k)(A; M)` along `S` and
sending the calibrated ground-ring class `[m! (a₀ ⋯ a_(2m)) • x]` in `HC^(0+2m)(R; M)` to
`[a₀ ↦ a₀ • x]` in `HP^0(R; M)`.

## Main definitions

* `TauCeti.cyclicTotalHomologyPeriodicTransition`: the transition maps
  `S^(j-i) : H^(n+2i)(Tot) → H^(n+2j)(Tot)` of the direct system.
* `TauCeti.periodicCyclicCohomology`: periodic cyclic cohomology `HP^n(A; M)`, its direct limit.
* `TauCeti.periodicCyclicCohomology.ι`: the canonical map `H^(n+2k)(Tot) → HP^n`.
* `TauCeti.periodicCyclicCohomology.desc`: the universal property of the direct limit.
* `TauCeti.periodicCyclicCohomology.shiftIso`: the `2`-periodicity `HP^(n+2) ≅ HP^n`.
* `TauCeti.cyclicCohomology.periodicTransition`: the transition maps
  `S^(j-i) : HC^(n+2i)(A; M) → HC^(n+2j)(A; M)` under Connes' operator `S`.
* `TauCeti.periodicComparisonScalar`: the rational normalization factor comparing the `k`-th cyclic
  cohomology stage with the bicomplex direct system (`(-1)^m / (2m)!` at `n = 0`).
* `TauCeti.periodicCyclicCohomology.fromCyclicCohomology`,
  `TauCeti.periodicCyclicCohomology.descCyclicCohomology`: the normalized stage maps
  `HC^(n+2k)(A; M) → HP^n(A; M)` and the colimit universal property along Connes' `S`.

## Main results

* `TauCeti.periodicCyclicCohomology.exists_ι_eq`: every periodic class comes from some stage.
* `TauCeti.periodicCyclicCohomology.ι_eq_zero_iff`: a class at a stage has zero periodic image
  exactly when an iterate of `S` kills it.
* `TauCeti.periodicCyclicCohomology.isIso_ι_of_isZero_hochschildCohomology`: if the Hochschild
  cohomology of a unital algebra vanishes above degree `n + 2k`, then
  `H^(n+2k)(Tot) → HP^n` is an isomorphism.
* `TauCeti.periodicCyclicCohomology.isIso_ι_self`,
  `TauCeti.isZero_periodicCyclicCohomology_self_one`: `HP^n(R; M) ≅ H^n(Tot)` and
  `HP^1(R; M) = 0` for the ground ring.
* `TauCeti.periodicComparisonScalar_zero_left`, `TauCeti.periodicComparisonScalar_one_left`:
  `periodicComparisonScalar 0 m = (-1)^m / (2m)!` and
  `periodicComparisonScalar 1 k = (-1)^k / (2k + 1)!`.
* `TauCeti.periodicCyclicCohomology.periodicity_fromCyclicCohomology`,
  `TauCeti.periodicCyclicCohomology.exists_fromCyclicCohomology_eq`,
  `TauCeti.periodicCyclicCohomology.fromCyclicCohomology_eq_zero_iff`: `HP^n(A; M)` is the direct
  limit of `HC^(n+2k)(A; M)` under Connes' operator `S`.
* `TauCeti.cyclicCohomology.periodicity_mkPiRing`,
  `TauCeti.periodicCyclicCohomology.fromCyclicCohomology_factorial_smul_mkPiRing`: ground-ring
  action of `S` and scalar calibration in `HP^0(R; M)`.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §5.1.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

universe u v

section NonUnital

variable (R : Type*) (A : Type u) (M : Type v) [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- The transition map `S^(j-i) : H^(n+2i)(Tot) → H^(n+2j)(Tot)` of the direct system of the
cohomology of the total cyclic bicomplex in the degrees `n + 2k`: the composite of the periodicity
maps `S` from degree `n + 2i` to degree `n + 2j`. -/
def cyclicTotalHomologyPeriodicTransition (n : ℕ) {i j : ℕ} (h : i ≤ j) :
    (cyclicTotalComplex R A M).homology (n + 2 * i) ⟶
      (cyclicTotalComplex R A M).homology (n + 2 * j) :=
  Functor.OfSequence.map (X := fun k ↦ (cyclicTotalComplex R A M).homology (n + 2 * k))
    (fun k ↦ cyclicTotalHomologyPeriodicity R A M (n + 2 * k)) i j h

/-- The transition map from a stage to itself is the identity. -/
@[simp]
theorem cyclicTotalHomologyPeriodicTransition_self (n i : ℕ) :
    cyclicTotalHomologyPeriodicTransition R A M n (le_refl i) = 𝟙 _ :=
  Functor.OfSequence.map_id _ i

/-- The transition map from the `k`-th to the `(k + 1)`-st stage is the periodicity map `S`. -/
@[simp]
theorem cyclicTotalHomologyPeriodicTransition_succ (n k : ℕ) :
    cyclicTotalHomologyPeriodicTransition R A M n (Nat.le_add_right k 1) =
      cyclicTotalHomologyPeriodicity R A M (n + 2 * k) :=
  Functor.OfSequence.map_le_succ _ k

/-- The transition maps compose. -/
@[reassoc (attr := simp)]
theorem cyclicTotalHomologyPeriodicTransition_comp (n : ℕ) {i j k : ℕ} (hij : i ≤ j)
    (hjk : j ≤ k) :
    cyclicTotalHomologyPeriodicTransition R A M n hij ≫
        cyclicTotalHomologyPeriodicTransition R A M n hjk =
      cyclicTotalHomologyPeriodicTransition R A M n (hij.trans hjk) :=
  (Functor.OfSequence.map_comp _ i j k hij hjk).symm

instance (n : ℕ) :
    DirectedSystem (fun k ↦ (cyclicTotalComplex R A M).homology (n + 2 * k))
      fun _ _ h ↦ (cyclicTotalHomologyPeriodicTransition R A M n h).hom where
  map_self i x := by rw [cyclicTotalHomologyPeriodicTransition_self, ModuleCat.id_apply]
  map_map _ _ _ hij hjk x := by
    rw [← ModuleCat.comp_apply, cyclicTotalHomologyPeriodicTransition_comp]

/-- **Periodic cyclic cohomology** `HP^n(A; M)`: the direct limit of the cohomology groups
`H^(n+2k)(Tot)` of the total cyclic bicomplex under the periodicity maps `S`. -/
def periodicCyclicCohomology (n : ℕ) : ModuleCat R :=
  ModuleCat.of R (Module.DirectLimit (fun k ↦ (cyclicTotalComplex R A M).homology (n + 2 * k))
    fun _ _ h ↦ (cyclicTotalHomologyPeriodicTransition R A M n h).hom)

namespace periodicCyclicCohomology

/-- The canonical map `H^(n+2k)(Tot) → HP^n` from the `k`-th stage to periodic cyclic
cohomology. -/
def ι (n k : ℕ) :
    (cyclicTotalComplex R A M).homology (n + 2 * k) ⟶ periodicCyclicCohomology R A M n :=
  ModuleCat.ofHom (Module.DirectLimit.of R ℕ
    (fun k ↦ (cyclicTotalComplex R A M).homology (n + 2 * k))
    (fun _ _ h ↦ (cyclicTotalHomologyPeriodicTransition R A M n h).hom) k)

variable {R A M}

/-- The canonical maps to periodic cyclic cohomology are compatible with the transition maps of
the direct system. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem cyclicTotalHomologyPeriodicTransition_ι {n i j : ℕ} (h : i ≤ j) :
    cyclicTotalHomologyPeriodicTransition R A M n h ≫ ι R A M n j = ι R A M n i :=
  ModuleCat.hom_ext (LinearMap.ext fun _ ↦ Module.DirectLimit.of_f)

variable (R A M) in
/-- The canonical maps to periodic cyclic cohomology are compatible with the periodicity map:
`ι_(k+1) ∘ S = ι_k`. -/
@[reassoc (attr := simp)]
theorem cyclicTotalHomologyPeriodicity_ι (n k : ℕ) :
    cyclicTotalHomologyPeriodicity R A M (n + 2 * k) ≫ ι R A M n (k + 1) = ι R A M n k := by
  rw [← cyclicTotalHomologyPeriodicTransition_succ, cyclicTotalHomologyPeriodicTransition_ι]

/-- Every periodic cyclic cohomology class comes from some stage `H^(n+2k)(Tot)`. -/
theorem exists_ι_eq {n : ℕ} (x : periodicCyclicCohomology R A M n) :
    ∃ k y, ι R A M n k y = x :=
  Module.DirectLimit.exists_of x

/-- A class in `H^(n+2k)(Tot)` has zero image in periodic cyclic cohomology exactly when it is
killed by some iterate of the periodicity map. -/
theorem ι_eq_zero_iff {n k : ℕ} (y : (cyclicTotalComplex R A M).homology (n + 2 * k)) :
    ι R A M n k y = 0 ↔
      ∃ (j : ℕ) (h : k ≤ j), cyclicTotalHomologyPeriodicTransition R A M n h y = 0 :=
  ⟨fun hy ↦ Module.DirectLimit.of.zero_exact hy, fun ⟨_, h, hy⟩ ↦ by
    rw [← cyclicTotalHomologyPeriodicTransition_ι_apply h, hy]
    exact map_zero _⟩

/-- Two maps out of periodic cyclic cohomology agree when they agree on every stage. -/
@[ext]
theorem hom_ext {n : ℕ} {P : ModuleCat R} {f g : periodicCyclicCohomology R A M n ⟶ P}
    (h : ∀ k, ι R A M n k ≫ f = ι R A M n k ≫ g) : f = g :=
  ModuleCat.hom_ext (Module.DirectLimit.hom_ext fun k ↦ congrArg ModuleCat.Hom.hom (h k))

/-- A family of maps out of the stages compatible with the periodicity maps is compatible with
every transition map of the periodic system. -/
private theorem map_comp_of_periodicity_comp {n : ℕ} {P : ModuleCat R}
    (g : ∀ k, (cyclicTotalComplex R A M).homology (n + 2 * k) ⟶ P)
    (hg : ∀ k, cyclicTotalHomologyPeriodicity R A M (n + 2 * k) ≫ g (k + 1) = g k)
    {i j : ℕ} (h : i ≤ j) :
    cyclicTotalHomologyPeriodicTransition R A M n h ≫ g j = g i := by
  induction j, h using Nat.le_induction with
  | base => rw [cyclicTotalHomologyPeriodicTransition_self, Category.id_comp]
  | succ j hij ih =>
    rw [← cyclicTotalHomologyPeriodicTransition_comp_assoc R A M n hij (Nat.le_add_right j 1),
      cyclicTotalHomologyPeriodicTransition_succ, hg, ih]

/-- The universal property of periodic cyclic cohomology: a family of maps out of the stages
`H^(n+2k)(Tot)` compatible with the periodicity maps factors through `HP^n`. -/
def desc {n : ℕ} {P : ModuleCat R} (g : ∀ k, (cyclicTotalComplex R A M).homology (n + 2 * k) ⟶ P)
    (hg : ∀ k, cyclicTotalHomologyPeriodicity R A M (n + 2 * k) ≫ g (k + 1) = g k) :
    periodicCyclicCohomology R A M n ⟶ P :=
  ModuleCat.ofHom (Module.DirectLimit.lift R ℕ _ _ (fun k ↦ (g k).hom) fun _ _ h x ↦
    congrArg (fun f ↦ f.hom x) (map_comp_of_periodicity_comp g hg h))

/-- The map out of periodic cyclic cohomology induced by a compatible family restricts to the
family on each stage. -/
@[reassoc (attr := simp)]
theorem ι_desc {n : ℕ} {P : ModuleCat R}
    (g : ∀ k, (cyclicTotalComplex R A M).homology (n + 2 * k) ⟶ P)
    (hg : ∀ k, cyclicTotalHomologyPeriodicity R A M (n + 2 * k) ≫ g (k + 1) = g k) (k : ℕ) :
    ι R A M n k ≫ desc g hg = g k := by
  ext x
  exact Module.DirectLimit.lift_of
    (f := fun _ _ h ↦ (cyclicTotalHomologyPeriodicTransition R A M n h).hom)
    (fun k ↦ (g k).hom)
    (fun _ _ h y ↦ congrArg (fun f ↦ f.hom y) (map_comp_of_periodicity_comp g hg h)) x

/-- The canonical map `H^m(Tot) → HP^n` from a degree `m` equal to `n + 2k`, through the
identification of `H^m(Tot)` with the `k`-th stage. -/
private def ιOfEq (n k : ℕ) {m : ℕ} (h : m = n + 2 * k) :
    (cyclicTotalComplex R A M).homology m ⟶ periodicCyclicCohomology R A M n :=
  eqToHom (by rw [h]) ≫ ι R A M n k

/-- At the degree `n + 2k` itself, `ιOfEq` is the canonical map from the `k`-th stage. -/
private theorem ιOfEq_rfl (n k : ℕ) : ιOfEq (R := R) (A := A) (M := M) n k rfl = ι R A M n k := by
  simp [ιOfEq]

/-- The maps `ιOfEq` are compatible with the periodicity map. -/
private theorem cyclicTotalHomologyPeriodicity_ιOfEq {n k m : ℕ} (h : m = n + 2 * k)
    (h' : m + 2 = n + 2 * (k + 1)) :
    cyclicTotalHomologyPeriodicity R A M m ≫ ιOfEq n (k + 1) h' = ιOfEq n k h := by
  subst h
  simp [ιOfEq]

/-- The map induced by a compatible family, restricted along `ιOfEq`. -/
private theorem ιOfEq_desc {n j m : ℕ} (h : m = n + 2 * j) {P : ModuleCat R}
    (g : ∀ k, (cyclicTotalComplex R A M).homology (n + 2 * k) ⟶ P)
    (hg : ∀ k, cyclicTotalHomologyPeriodicity R A M (n + 2 * k) ≫ g (k + 1) = g k) :
    ιOfEq n j h ≫ desc g hg = eqToHom (by rw [h]) ≫ g j := by
  subst h
  simp [ιOfEq]

/-- Identifications of equal degrees compose with `ιOfEq`. -/
private theorem eqToHom_ιOfEq {n k m m' : ℕ} (e : m' = m) (h : m = n + 2 * k) :
    eqToHom (by rw [e]) ≫ ιOfEq (R := R) (A := A) (M := M) n k h = ιOfEq n k (e.trans h) := by
  subst e
  simp

/-- The periodicity map commutes with identifications of equal degrees, followed by `ιOfEq`. -/
private theorem eqToHom_cyclicTotalHomologyPeriodicity_ιOfEq {n k i m : ℕ} (n' : ℕ)
    (h : m = n + 2 * k) (h' : n + 2 * k + 2 = n' + 2 * i) (h'' : m + 2 = n' + 2 * i) :
    eqToHom (by rw [h]) ≫ cyclicTotalHomologyPeriodicity R A M (n + 2 * k) ≫ ιOfEq n' i h' =
      cyclicTotalHomologyPeriodicity R A M m ≫ ιOfEq n' i h'' := by
  subst h
  simp

variable (R A M) in
/-- Periodic cyclic cohomology is `2`-periodic: `HP^(n+2) ≅ HP^n`, identifying the stage
`H^(n+2+2k)(Tot)` of `HP^(n+2)` with the stage `H^(n+2(k+1))(Tot)` of `HP^n`. -/
def shiftIso (n : ℕ) :
    periodicCyclicCohomology R A M (n + 2) ≅ periodicCyclicCohomology R A M n where
  hom := desc (fun k ↦ ιOfEq n (k + 1) (by omega)) fun k ↦
    cyclicTotalHomologyPeriodicity_ιOfEq (by omega) _
  inv := desc (fun k ↦ cyclicTotalHomologyPeriodicity R A M (n + 2 * k) ≫
      ιOfEq (n + 2) k (by omega)) fun k ↦ by
    rw [cyclicTotalHomologyPeriodicity_ιOfEq]
  hom_inv_id := by
    ext k : 1
    rw [ι_desc_assoc, ιOfEq_desc, eqToHom_cyclicTotalHomologyPeriodicity_ιOfEq (n + 2)
      (k := k + 1) (i := k + 1) (m := n + 2 + 2 * k) (by omega) (by omega) (by omega),
      cyclicTotalHomologyPeriodicity_ιOfEq rfl, ιOfEq_rfl, Category.comp_id]
  inv_hom_id := by
    ext k : 1
    rw [ι_desc_assoc, Category.assoc, ιOfEq_desc, eqToHom_ιOfEq (by omega),
      cyclicTotalHomologyPeriodicity_ιOfEq rfl, ιOfEq_rfl, Category.comp_id]

variable (R A M) in
/-- On the `k`-th stage `H^(n+2+2k)(Tot)` of `HP^(n+2)`, the `2`-periodicity isomorphism is the
canonical map from the `(k + 1)`-st stage `H^(n+2(k+1))(Tot)` of `HP^n`. -/
@[reassoc (attr := simp)]
theorem ι_shiftIso_hom (n k : ℕ) :
    ι R A M (n + 2) k ≫ (shiftIso R A M n).hom =
      eqToHom (by rw [show n + 2 + 2 * k = n + 2 * (k + 1) by omega]) ≫ ι R A M n (k + 1) :=
  ι_desc _ (fun _ ↦ cyclicTotalHomologyPeriodicity_ιOfEq (by omega) _) k

end periodicCyclicCohomology

end NonUnital

section Unital

variable {R : Type*} {A : Type u} {M : Type v} [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M]

/-- If the Hochschild cohomology vanishes above degree `n + 2k`, the transition maps between
stages `≥ k` are bijective. -/
private theorem bijective_cyclicTotalHomologyPeriodicTransition {n k : ℕ}
    (h : ∀ m, n + 2 * k < m → Limits.IsZero (hochschildCohomology R A M m)) {i j : ℕ}
    (hki : k ≤ i) (hij : i ≤ j) :
    Function.Bijective (cyclicTotalHomologyPeriodicTransition R A M n hij) := by
  induction j, hij using Nat.le_induction with
  | base =>
    rw [cyclicTotalHomologyPeriodicTransition_self]
    exact Function.bijective_id
  | succ j hij ih =>
    rw [← cyclicTotalHomologyPeriodicTransition_comp R A M n hij (Nat.le_add_right j 1),
      cyclicTotalHomologyPeriodicTransition_succ, ConcreteCategory.coe_comp]
    exact Function.Bijective.comp
      ⟨injective_cyclicTotalHomologyPeriodicity_of_isZero (h _ (by omega)),
        surjective_cyclicTotalHomologyPeriodicity_of_isZero (h _ (by omega))⟩ ih

namespace periodicCyclicCohomology

/-- **Stabilization of periodic cyclic cohomology.** For a unital algebra whose Hochschild
cohomology `HH^m(A, Hom_R(A, M))` vanishes in all degrees `m > n + 2k`, the canonical map
`H^(n+2k)(Tot) → HP^n` is an isomorphism. -/
theorem isIso_ι_of_isZero_hochschildCohomology {n k : ℕ}
    (h : ∀ m, n + 2 * k < m → Limits.IsZero (hochschildCohomology R A M m)) :
    IsIso (ι R A M n k) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(injective_iff_map_eq_zero _).2 fun y hy ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨j, hkj, hj⟩ := (ι_eq_zero_iff y).1 hy
    exact (bijective_cyclicTotalHomologyPeriodicTransition h le_rfl hkj).1
      (hj.trans (map_zero _).symm)
  · obtain ⟨j, z, rfl⟩ := exists_ι_eq x
    obtain hjk | hkj := le_total j k
    · exact ⟨_, cyclicTotalHomologyPeriodicTransition_ι_apply hjk z⟩
    · obtain ⟨y, rfl⟩ := (bijective_cyclicTotalHomologyPeriodicTransition h le_rfl hkj).2 z
      exact ⟨y, (cyclicTotalHomologyPeriodicTransition_ι_apply hkj y).symm⟩

end periodicCyclicCohomology

end Unital

/-! ### The ground ring -/

section GroundRing

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

namespace periodicCyclicCohomology

/-- The Hochschild cohomology of the ground ring vanishes in positive degree, so its periodic
cyclic cohomology `HPⁿ(R; M)` is the cohomology `Hⁿ(Tot)` of its total cyclic bicomplex. -/
instance isIso_ι_self (n : ℕ) : IsIso (ι R R M n 0) :=
  isIso_ι_of_isZero_hochschildCohomology fun _ hm ↦
    isZero_hochschildCohomology_self R M (Nat.ne_zero_of_lt hm)

end periodicCyclicCohomology

/-- The odd periodic cyclic cohomology `HP¹(R; M)` of the ground ring vanishes: `H¹(Tot)` embeds
into `HH¹(R, Hom_R(R, M)) = 0`. -/
theorem isZero_periodicCyclicCohomology_self_one :
    Limits.IsZero (periodicCyclicCohomology R R M 1) := by
  have := ModuleCat.isZero_iff_subsingleton.1 (isZero_hochschildCohomology_self R M one_ne_zero)
  have h : Limits.IsZero ((cyclicTotalComplex R R M).homology 1) :=
    ModuleCat.isZero_iff_subsingleton.2
      injective_homologyMap_cyclicTotalComplexToHochschild_one.subsingleton
  exact h.of_iso (asIso (periodicCyclicCohomology.ι R R M 1 0)).symm

end GroundRing

/-! ### Comparison with Connes' periodicity operator on cyclic cohomology -/

section ComparisonScalar

open scoped Nat

/-- The rational normalization scalar comparing the `k`-th cyclic cohomology stage `HC^(n+2k)` with
the `k`-th stage `H^(n+2k)(Tot)` of the periodic bicomplex direct system, compensating for the
factor `-((n + 2i + 1) * (n + 2i + 2))` in
`TauCeti.cyclicCohomology.periodicity_comp_homologyMap_cyclicCochainComplexToTotal`. -/
def periodicComparisonScalar (n k : ℕ) : ℚ :=
  ∏ i ∈ Finset.range k, (-((n + 2 * i + 1 : ℚ) * (n + 2 * i + 2 : ℚ)))⁻¹

/-- At stage zero (`k = 0`), the comparison scalar is `1`. -/
@[simp]
theorem periodicComparisonScalar_zero_right (n : ℕ) : periodicComparisonScalar n 0 = 1 :=
  (rfl)

/-- Stepping from stage `k` to `k + 1` divides by `-((n + 2k + 1) * (n + 2k + 2))`. -/
theorem periodicComparisonScalar_succ (n k : ℕ) :
    periodicComparisonScalar n (k + 1) =
      periodicComparisonScalar n k * (-((n + 2 * k + 1 : ℚ) * (n + 2 * k + 2 : ℚ)))⁻¹ :=
  Finset.prod_range_succ _ k

/-- Multiplying the `(k + 1)`-st comparison scalar by `-((n + 2k + 1) * (n + 2k + 2))` recovers the
`k`-th comparison scalar. -/
theorem periodicComparisonScalar_mul_neg (n k : ℕ) :
    periodicComparisonScalar n (k + 1) * (-((n + 2 * k + 1 : ℚ) * (n + 2 * k + 2 : ℚ))) =
      periodicComparisonScalar n k := by
  have hne : -((n + 2 * k + 1 : ℚ) * (n + 2 * k + 2 : ℚ)) ≠ 0 :=
    neg_ne_zero.2 (mul_ne_zero (by positivity) (by positivity))
  rw [periodicComparisonScalar_succ, mul_assoc, inv_mul_cancel₀ hne, mul_one]

/-- Every comparison scalar `periodicComparisonScalar n k` is nonzero. -/
theorem periodicComparisonScalar_ne_zero (n k : ℕ) : periodicComparisonScalar n k ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun i _ ↦ inv_ne_zero ?_
  exact neg_ne_zero.2 (mul_ne_zero (by positivity) (by positivity))

/-- In any `ℚ`-algebra, the image of `periodicComparisonScalar n k` is a unit. -/
theorem isUnit_algebraMap_periodicComparisonScalar {R : Type*} [CommRing R] [Algebra ℚ R]
    (n k : ℕ) : IsUnit (algebraMap ℚ R (periodicComparisonScalar n k)) :=
  (periodicComparisonScalar_ne_zero n k).isUnit.map (algebraMap ℚ R)

/-- **Even column comparison constant.** For `n = 0` and even degree `2m`, the comparison scalar is
`(-1)^m / (2m)!`. -/
theorem periodicComparisonScalar_zero_left (m : ℕ) :
    periodicComparisonScalar 0 m = (-1 : ℚ) ^ m / ((2 * m)! : ℚ) := by
  induction m with
  | zero => simp [periodicComparisonScalar]
  | succ k ih =>
    rw [periodicComparisonScalar_succ, ih, show 2 * (k + 1) = 2 * k + 1 + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ]
    have h2 : ((2 * k + 1 + 1 : ℕ) : ℚ) = 2 * (k : ℚ) + 2 := by push_cast; ring
    have h1 : ((2 * k + 1 : ℕ) : ℚ) = 2 * (k : ℚ) + 1 := by push_cast; ring
    simp only [Nat.cast_zero, zero_add, Nat.cast_mul, h2, h1, div_eq_mul_inv, inv_neg, mul_inv,
      pow_succ]
    ring

/-- **Odd column comparison constant.** Relative to degree `1`, the `k`-th odd stage `2k + 1` has
comparison scalar `(-1)^k / (2k + 1)!`. -/
theorem periodicComparisonScalar_one_left (k : ℕ) :
    periodicComparisonScalar 1 k = (-1 : ℚ) ^ k / ((2 * k + 1)! : ℚ) := by
  induction k with
  | zero => simp [periodicComparisonScalar]
  | succ r ih =>
    conv_rhs =>
      rw [show 2 * (r + 1) + 1 = (2 * r + 1) + 1 + 1 by omega, Nat.factorial_succ,
        Nat.factorial_succ]
    rw [periodicComparisonScalar_succ, ih]
    have h4 : ((1 : ℕ) : ℚ) + 2 * (r : ℚ) + 2 = ((2 * r + 1 + 1 + 1 : ℕ) : ℚ) := by
      push_cast; ring
    have h3 : ((1 : ℕ) : ℚ) + 2 * (r : ℚ) + 1 = ((2 * r + 1 + 1 : ℕ) : ℚ) := by
      push_cast; ring
    rw [h4, h3]
    simp only [Nat.cast_mul, div_eq_mul_inv, inv_neg, mul_inv, pow_succ]
    ring

end ComparisonScalar

section RationalDirectLimit

open scoped Nat

variable (R : Type*) (A : Type u) (M : Type v) [CommRing R] [Algebra ℚ R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M]

/-- The transition map `S^(j-i) : HC^(n+2i)(A; M) → HC^(n+2j)(A; M)` of cyclic cohomology in the
degrees `n + 2k` under Connes' periodicity operator `TauCeti.cyclicCohomology.periodicity`. -/
def cyclicCohomology.periodicTransition (n : ℕ) {i j : ℕ} (h : i ≤ j) :
    cyclicCohomology R A M (n + 2 * i) ⟶ cyclicCohomology R A M (n + 2 * j) :=
  Functor.OfSequence.map (X := fun k ↦ cyclicCohomology R A M (n + 2 * k))
    (fun k ↦ cyclicCohomology.periodicity R A M (n + 2 * k)) i j h

/-- The transition map from a stage to itself is the identity. -/
@[simp]
theorem cyclicCohomology.periodicTransition_self (n i : ℕ) :
    cyclicCohomology.periodicTransition R A M n (le_refl i) = 𝟙 _ :=
  Functor.OfSequence.map_id _ i

/-- The transition map from the `k`-th to the `(k + 1)`-st stage is Connes' periodicity map `S`. -/
@[simp]
theorem cyclicCohomology.periodicTransition_succ (n k : ℕ) :
    cyclicCohomology.periodicTransition R A M n (Nat.le_add_right k 1) =
      cyclicCohomology.periodicity R A M (n + 2 * k) :=
  Functor.OfSequence.map_le_succ _ k

/-- The cyclic cohomology transition maps compose. -/
@[reassoc (attr := simp)]
theorem cyclicCohomology.periodicTransition_comp (n : ℕ) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    cyclicCohomology.periodicTransition R A M n hij ≫
        cyclicCohomology.periodicTransition R A M n hjk =
      cyclicCohomology.periodicTransition R A M n (hij.trans hjk) :=
  (Functor.OfSequence.map_comp _ i j k hij hjk).symm

/-- Compatibility between `cyclicCohomology.periodicTransition` and
`cyclicTotalHomologyPeriodicTransition` after rescaling by `periodicComparisonScalar`. -/
theorem cyclicCohomology.smul_periodicTransition_comp_homologyMap (n : ℕ) {i j : ℕ} (h : i ≤ j) :
    algebraMap ℚ R (periodicComparisonScalar n j) •
        (cyclicCohomology.periodicTransition R A M n h ≫
          HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) (n + 2 * j)) =
      algebraMap ℚ R (periodicComparisonScalar n i) •
        (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) (n + 2 * i) ≫
          cyclicTotalHomologyPeriodicTransition R A M n h) := by
  induction j, h using Nat.le_induction with
  | base =>
    rw [cyclicCohomology.periodicTransition_self, cyclicTotalHomologyPeriodicTransition_self,
      Category.id_comp, Category.comp_id]
  | succ j hij ih =>
    have hscalar :
        algebraMap ℚ R (periodicComparisonScalar n (j + 1)) *
            -((((n + 2 * j : ℕ) : R) + 1) * (((n + 2 * j : ℕ) : R) + 2)) =
          algebraMap ℚ R (periodicComparisonScalar n j) := by
      have hm := congrArg (algebraMap ℚ R) (periodicComparisonScalar_mul_neg n j)
      simp only [map_mul, map_add, map_neg, map_one, map_ofNat, map_natCast] at hm
      rw [← hm]
      push_cast
      ring
    -- Expose the definitional equality `n + 2 * (j + 1) = (n + 2 * j) + 2` for `rw`.
    have hcomp :
        cyclicCohomology.periodicity R A M (n + 2 * j) ≫
            HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) (n + 2 * (j + 1)) =
          -((((n + 2 * j : ℕ) : R) + 1) * (((n + 2 * j : ℕ) : R) + 2)) •
            (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) (n + 2 * j) ≫
              cyclicTotalHomologyPeriodicity R A M (n + 2 * j)) :=
      cyclicCohomology.periodicity_comp_homologyMap_cyclicCochainComplexToTotal R A M (n + 2 * j)
    rw [← cyclicCohomology.periodicTransition_comp R A M n hij (Nat.le_add_right j 1),
      cyclicCohomology.periodicTransition_succ, Category.assoc, hcomp, Linear.comp_smul,
      smul_smul, hscalar, ← Linear.smul_comp, ← Category.assoc, Linear.smul_comp, ih,
      Linear.smul_comp, Category.assoc, ← cyclicTotalHomologyPeriodicTransition_succ,
      cyclicTotalHomologyPeriodicTransition_comp]

namespace periodicCyclicCohomology

/-- The normalized canonical map `HC^(n+2k)(A; M) → HP^n(A; M)` from the `k`-th cyclic cohomology
stage to periodic cyclic cohomology, scaled by `periodicComparisonScalar n k` so that it commutes
with Connes' periodicity operator `S`. -/
def fromCyclicCohomology (n k : ℕ) :
    cyclicCohomology R A M (n + 2 * k) ⟶ periodicCyclicCohomology R A M n :=
  algebraMap ℚ R (periodicComparisonScalar n k) •
    (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) (n + 2 * k) ≫
      ι R A M n k)

/-- At stage zero (`k = 0`), `fromCyclicCohomology` is the unscaled inclusion into `HP^n`. -/
@[simp]
theorem fromCyclicCohomology_zero (n : ℕ) :
    fromCyclicCohomology R A M n 0 =
      HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n ≫ ι R A M n 0 := by
  simp [fromCyclicCohomology]

variable {R A M}

/-- The normalized stage maps commute with every transition map `S^(j-i)` of cyclic cohomology. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem periodicTransition_fromCyclicCohomology {n i j : ℕ} (h : i ≤ j) :
    cyclicCohomology.periodicTransition R A M n h ≫ fromCyclicCohomology R A M n j =
      fromCyclicCohomology R A M n i := by
  dsimp only [fromCyclicCohomology]
  rw [Linear.comp_smul, ← Category.assoc, ← Linear.smul_comp,
    cyclicCohomology.smul_periodicTransition_comp_homologyMap, Linear.smul_comp, Category.assoc,
    cyclicTotalHomologyPeriodicTransition_ι]

variable (R A M) in
/-- **Compatibility with Connes' operator `S`:**
`fromCyclicCohomology (k + 1) ∘ S = fromCyclicCohomology k`. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem periodicity_fromCyclicCohomology (n k : ℕ) :
    cyclicCohomology.periodicity R A M (n + 2 * k) ≫ fromCyclicCohomology R A M n (k + 1) =
      fromCyclicCohomology R A M n k := by
  rw [← cyclicCohomology.periodicTransition_succ, periodicTransition_fromCyclicCohomology]

/-- Every periodic cyclic cohomology class comes from some cyclic cohomology stage
`HC^(n+2k)(A; M)`. -/
theorem exists_fromCyclicCohomology_eq {n : ℕ} (x : periodicCyclicCohomology R A M n) :
    ∃ k y, fromCyclicCohomology R A M n k y = x := by
  obtain ⟨k, z, rfl⟩ := exists_ι_eq x
  obtain ⟨y, rfl⟩ := (bijective_homologyMap_cyclicCochainComplexToTotal R A M (n + 2 * k)).2 z
  obtain ⟨u, hu⟩ := isUnit_algebraMap_periodicComparisonScalar (R := R) n k
  refine ⟨k, (↑u⁻¹ : R) • y, ?_⟩
  simp only [fromCyclicCohomology, map_smul, ModuleCat.hom_smul, ModuleCat.hom_comp,
    LinearMap.smul_apply, LinearMap.comp_apply, ← hu, smul_smul, Units.inv_mul, one_smul]

/-- A cyclic cohomology class in `HC^(n+2k)(A; M)` has zero image in `HP^n(A; M)` if and only if
some iterate of Connes' periodicity operator `S` kills it. -/
theorem fromCyclicCohomology_eq_zero_iff {n k : ℕ} (y : cyclicCohomology R A M (n + 2 * k)) :
    fromCyclicCohomology R A M n k y = 0 ↔
      ∃ (j : ℕ) (h : k ≤ j), cyclicCohomology.periodicTransition R A M n h y = 0 := by
  obtain ⟨uk, huk⟩ := isUnit_algebraMap_periodicComparisonScalar (R := R) n k
  constructor
  · intro hy
    have hι : ι R A M n k
        (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) (n + 2 * k) y) = 0 := by
      have h1 := congrArg ((↑uk⁻¹ : R) • ·) hy
      simpa only [fromCyclicCohomology, ModuleCat.hom_smul, ModuleCat.hom_comp,
        LinearMap.smul_apply, LinearMap.comp_apply, ← huk, smul_smul, Units.inv_mul, one_smul,
        smul_zero] using h1
    obtain ⟨j, hkj, hj⟩ := (ι_eq_zero_iff _).1 hι
    obtain ⟨uj, huj⟩ := isUnit_algebraMap_periodicComparisonScalar (R := R) n j
    refine ⟨j, hkj, (bijective_homologyMap_cyclicCochainComplexToTotal R A M (n + 2 * j)).1 ?_⟩
    rw [map_zero]
    have heq := congrArg (fun f : cyclicCohomology R A M (n + 2 * k) ⟶ _ ↦ f y)
      (cyclicCohomology.smul_periodicTransition_comp_homologyMap R A M n hkj)
    simp only [ModuleCat.hom_smul, ModuleCat.hom_comp, LinearMap.smul_apply, LinearMap.comp_apply,
      hj, smul_zero] at heq
    have h2 := congrArg ((↑uj⁻¹ : R) • ·) heq
    simpa only [← huj, smul_smul, Units.inv_mul, one_smul, smul_zero] using h2
  · rintro ⟨j, hkj, hj⟩
    rw [← periodicTransition_fromCyclicCohomology_apply hkj, hj, map_zero]

/-- Two morphisms out of `HP^n(A; M)` agree once they agree on all stages `fromCyclicCohomology`. -/
theorem hom_ext_fromCyclicCohomology {n : ℕ} {P : ModuleCat R}
    {f g : periodicCyclicCohomology R A M n ⟶ P}
    (h : ∀ k, fromCyclicCohomology R A M n k ≫ f = fromCyclicCohomology R A M n k ≫ g) :
    f = g := by
  refine hom_ext fun k ↦ ?_
  have := quasiIso_cyclicCochainComplexToTotal R A M
  obtain ⟨u, hu⟩ := isUnit_algebraMap_periodicComparisonScalar (R := R) n k
  rw [← cancel_epi (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) (n + 2 * k))]
  have hk := congrArg ((↑u⁻¹ : R) • ·) (h k)
  simpa only [fromCyclicCohomology, Linear.smul_comp, Category.assoc, ← hu, smul_smul,
    Units.inv_mul, one_smul] using hk

/-- **Universal property of `HP^n(A; M)` along Connes' operator `S`:** a family of morphisms out of
`HC^(n+2k)(A; M)` compatible with `cyclicCohomology.periodicity` factors uniquely through
`periodicCyclicCohomology R A M n`. -/
def descCyclicCohomology {n : ℕ} {P : ModuleCat R}
    (g : ∀ k, cyclicCohomology R A M (n + 2 * k) ⟶ P)
    (hg : ∀ k, cyclicCohomology.periodicity R A M (n + 2 * k) ≫ g (k + 1) = g k) :
    periodicCyclicCohomology R A M n ⟶ P := by
  have := quasiIso_cyclicCochainComplexToTotal R A M
  refine desc
    (fun k ↦ algebraMap ℚ R (periodicComparisonScalar n k)⁻¹ •
      (inv (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) (n + 2 * k)) ≫ g k))
    fun k ↦ ?_
  have hc :
      algebraMap ℚ R (periodicComparisonScalar n (k + 1))⁻¹ =
        algebraMap ℚ R (periodicComparisonScalar n k)⁻¹ *
          -((((n + 2 * k : ℕ) : R) + 1) * (((n + 2 * k : ℕ) : R) + 2)) := by
    have hq : (periodicComparisonScalar n (k + 1))⁻¹ =
        (periodicComparisonScalar n k)⁻¹ * (-((n + 2 * k + 1 : ℚ) * (n + 2 * k + 2 : ℚ))) := by
      rw [periodicComparisonScalar_succ, mul_inv, inv_inv]
    have hm := congrArg (algebraMap ℚ R) hq
    simp only [map_mul, map_add, map_neg, map_one, map_ofNat, map_natCast] at hm
    rw [hm]
    push_cast
    ring
  -- Expose the definitional equality `n + 2 * (k + 1) = (n + 2 * k) + 2` for `rw`.
  have hcomp :
      cyclicCohomology.periodicity R A M (n + 2 * k) ≫
          HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) (n + 2 * (k + 1)) =
        -((((n + 2 * k : ℕ) : R) + 1) * (((n + 2 * k : ℕ) : R) + 2)) •
          (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) (n + 2 * k) ≫
            cyclicTotalHomologyPeriodicity R A M (n + 2 * k)) :=
    cyclicCohomology.periodicity_comp_homologyMap_cyclicCochainComplexToTotal R A M (n + 2 * k)
  rw [← cancel_epi (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) (n + 2 * k)),
    Linear.comp_smul, Linear.comp_smul, hc, mul_smul, ← Category.assoc, ← Linear.smul_comp,
    ← hcomp, Category.assoc, IsIso.hom_inv_id_assoc, hg, Linear.comp_smul, IsIso.hom_inv_id_assoc]

/-- The map out of `HP^n(A; M)` induced by a compatible family restricts to the given family on each
cyclic cohomology stage. -/
@[reassoc (attr := simp)]
theorem fromCyclicCohomology_descCyclicCohomology {n : ℕ} {P : ModuleCat R}
    (g : ∀ k, cyclicCohomology R A M (n + 2 * k) ⟶ P)
    (hg : ∀ k, cyclicCohomology.periodicity R A M (n + 2 * k) ≫ g (k + 1) = g k) (k : ℕ) :
    fromCyclicCohomology R A M n k ≫ descCyclicCohomology g hg = g k := by
  have := quasiIso_cyclicCochainComplexToTotal R A M
  have hmul : algebraMap ℚ R (periodicComparisonScalar n k) *
      algebraMap ℚ R (periodicComparisonScalar n k)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ (periodicComparisonScalar_ne_zero n k), map_one]
  dsimp only [fromCyclicCohomology, descCyclicCohomology]
  rw [Linear.smul_comp, Category.assoc, ι_desc, Linear.comp_smul, smul_smul, hmul, one_smul,
    IsIso.hom_inv_id_assoc]

end periodicCyclicCohomology

end RationalDirectLimit

/-! ### Ground-ring calibration under Connes' operator `S` -/

section GroundRingCalibration

open scoped Nat

variable (R : Type u) (M : Type v) [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Module R M]

/-- On the ground ring `R`, Connes' periodicity operator sends the even-degree product class
`mkPiRing R M n hn x` to `n / 2 + 1` times `mkPiRing R M (n + 2) _ x`. -/
@[simp]
theorem cyclicCohomology.periodicity_mkPiRing {n : ℕ} (hn : Even n) (x : M) :
    cyclicCohomology.periodicity R R M n (cyclicCohomology.mkPiRing R M n hn x) =
      ((n / 2 + 1 : ℕ) : R) • cyclicCohomology.mkPiRing R M (n + 2) (hn.add even_two) x := by
  rw [cyclicCohomology.mkPiRing_apply, cyclicCohomology.periodicity_mk, ← map_smul,
    cyclicCohomology.mkPiRing_apply]
  refine congrArg (cyclicCohomology.mk R R M (n + 2))
    (Subtype.ext <| Subtype.ext <| MultilinearMap.ext fun a ↦ ?_)
  simp only [coe_cyclicCocyclesPeriodicity_apply, cochainPeriodicity_mkPiRing,
    Nat.cast_smul_eq_nsmul R]

/-- Iterating Connes' periodicity operator `m` times from degree zero sends `[a₀ ↦ a₀ • x]` to the
calibrated product class `[m! (a₀ ⋯ a_(2m)) • x]`. -/
@[simp]
theorem cyclicCohomology.periodicTransition_zero_mkPiRing (m : ℕ) (x : M) :
    cyclicCohomology.periodicTransition R R M 0 (Nat.zero_le m)
        (cyclicCohomology.mkPiRing R M 0 even_zero x) =
      (m ! : R) • cyclicCohomology.mkPiRing R M (0 + 2 * m) (even_zero.add (even_two_mul m)) x := by
  induction m with
  | zero =>
    have h0 : Nat.zero_le 0 = le_refl 0 := rfl
    rw [h0, cyclicCohomology.periodicTransition_self, ModuleCat.id_apply, Nat.factorial_zero,
      Nat.cast_one, one_smul]
    rfl
  | succ k ih =>
    rw [show Nat.zero_le (k + 1) = (Nat.zero_le k).trans (Nat.le_add_right k 1) from rfl,
      ← cyclicCohomology.periodicTransition_comp R R M 0 (Nat.zero_le k) (Nat.le_add_right k 1),
      ModuleCat.comp_apply, ih, cyclicCohomology.periodicTransition_succ, map_smul,
      cyclicCohomology.periodicity_mkPiRing, smul_smul, Nat.factorial_succ,
      show (0 + 2 * k) / 2 + 1 = k + 1 by omega]
    congr 1
    push_cast
    ring

/-- **Scalar calibration in `HP⁰(R; M)`.** Under the normalized stage map `fromCyclicCohomology`
(with column scalar `(-1)^m / (2m)!`), the degree-`2m` class `[m! (a₀ ⋯ a_(2m)) • x]` maps to the
degree-zero class `[a₀ ↦ a₀ • x]`. -/
theorem periodicCyclicCohomology.fromCyclicCohomology_factorial_smul_mkPiRing (m : ℕ) (x : M) :
    periodicCyclicCohomology.fromCyclicCohomology R R M 0 m
        ((m ! : R) •
          cyclicCohomology.mkPiRing R M (0 + 2 * m) (even_zero.add (even_two_mul m)) x) =
      periodicCyclicCohomology.fromCyclicCohomology R R M 0 0
        (cyclicCohomology.mkPiRing R M 0 even_zero x) := by
  have h := periodicCyclicCohomology.periodicTransition_fromCyclicCohomology_apply
    (R := R) (A := R) (M := M) (n := 0) (Nat.zero_le m)
    (cyclicCohomology.mkPiRing R M 0 even_zero x)
  rwa [cyclicCohomology.periodicTransition_zero_mkPiRing] at h

end GroundRingCalibration

end TauCeti

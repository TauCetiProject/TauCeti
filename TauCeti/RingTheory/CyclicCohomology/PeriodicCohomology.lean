/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.ExactSequence
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.CategoryTheory.Functor.OfSequence
import TauCeti.RingTheory.CyclicCohomology.GroundRing

/-!
# Periodic cyclic cohomology

The periodicity map `S : H^m(Tot) → H^(m+2)(Tot)` of Connes' cyclic bicomplex
(`TauCeti.cyclicTotalHomologyPeriodicity`) makes the cohomology of the total complex in the
degrees of a fixed parity into a direct system

`H^n(Tot) →S H^(n+2)(Tot) →S H^(n+4)(Tot) →S ⋯`.

Its direct limit is the periodic cyclic cohomology `HP^n(A; M)`. Over a ring containing `ℚ`
the total cohomology is cyclic cohomology (`TauCeti.quasiIso_cyclicCochainComplexToTotal`), so
`HP^n` is the same-parity direct limit of the cyclic cohomology groups `HC^(n+2k)`. Here the
transition maps are the column shift of the bicomplex; this file does not compare them with
Connes' operator `S` normalized as the exterior product with the cyclic `2`-cocycle
`(a₀, a₁, a₂) ↦ a₀a₁a₂`.

Every class in `HP^n` comes from a stage `H^(n+2k)(Tot)`, a class at a stage maps to zero
exactly when some iterate of `S` kills it, and `HP^(n+2) ≅ HP^n`. For a unital algebra the SBI
sequence controls the transition maps: `S : H^m(Tot) → H^(m+2)(Tot)` is injective when `HH^(m+1)`
vanishes and surjective when `HH^(m+2)` vanishes. Hence if the Hochschild cohomology
`HH^m(A, Hom_R(A, M))` vanishes in all degrees `m > n + 2k`, the stage `H^(n+2k)(Tot)` already
computes `HP^n`. This applies to the ground ring `R`, whose Hochschild cohomology vanishes in
positive degree: `HP^n(R; M)` is `H^n(Tot)`, and `HP^1(R; M) = 0`.

## Main definitions

* `TauCeti.cyclicTotalHomologyPeriodicTransition`: the transition maps
  `S^(j-i) : H^(n+2i)(Tot) → H^(n+2j)(Tot)` of the direct system.
* `TauCeti.periodicCyclicCohomology`: periodic cyclic cohomology `HP^n(A; M)`, its direct limit.
* `TauCeti.periodicCyclicCohomology.ι`: the canonical map `H^(n+2k)(Tot) → HP^n`.
* `TauCeti.periodicCyclicCohomology.desc`: the universal property of the direct limit.
* `TauCeti.periodicCyclicCohomology.shiftIso`: the `2`-periodicity `HP^(n+2) ≅ HP^n`.

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

end TauCeti

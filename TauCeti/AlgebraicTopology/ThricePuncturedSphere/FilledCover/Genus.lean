/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.AnalyticBelyiPair
public import TauCeti.Analysis.Complex.RiemannSurface.Branch.Sphere
public import TauCeti.Analysis.Complex.RiemannSurface.Genus
public import TauCeti.Combinatorics.PermutationTriple.ClassInvariants
public import TauCeti.Geometry.Manifold.Complex.FiniteCWType

import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Sphere

/-!
# Genus and Riemann–Hurwitz for analytic Belyi pairs and three-point covers

Every compact Riemann surface has finite CW type (`TauCeti.ComplexManifold.instFiniteCWType`), so
every analytic Belyi pair `P` has a finite-CW Euler characteristic `eulerChar P.X` and topological
genus `RiemannSurface.genus P.X`. This file establishes their isomorphism invariance, computes them
on sphere examples and degree-one pairs in every universe, and identifies them in `Type 0` with the
combinatorial Euler characteristic and genus of the monodromy triple of `P`:

1. **Three-fibre decomposition** (`ramificationDegree_β_eq_sum_three_fibers`): `ramificationDegree`
   of `P.β` splits as the sum of `localMultiplicity P.β x - 1` over the fibres above `0`, `1`, `∞`.
2. **Monodromy and filled points** (`natCast_ramificationDegree_toAnalyticBelyiPair`):
   the fibre cardinalities over `0`, `1`, `∞` are the cycle counts of `σ0`, `σ1`, `σinf`, giving
   `ramificationDegree P.β = 2 * degree P.β - χ(t) = ∑ (FilledCover.degree p i - 1)`.
3. **Topological Euler characteristic and genus** (`eulerChar_X_eq_eulerChar_monodromyTriple`,
   `genus_X_eq_genus_monodromyTriple`, `two_mul_genus_X_sub_two_eq`): combining with
   `FiniteHolomorphicMap.eulerChar_eq_two_mul_degree_sub_ramificationDegree` yields `χ(P.X) = χ(t)`,
   `genus P.X = t.genus`, `χ(P.X) = 2 - 2 g(P.X)`, and genus-form Riemann–Hurwitz, and transfers
   `FiniteCWType`, `eulerChar`, and `genus` to `TopBranchedCover.{0} n`.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, Springer, 1981, §17, Theorem 17.14.
* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, LMS Student Texts 79, Cambridge University Press, 2012, §1.2.7 and §4.2.
-/

public noncomputable section

open Equiv.Perm Function Metric Module Set
open scoped Manifold OnePoint

namespace TauCeti

open ThricePuncturedSphere RiemannSurface

universe u

/-! ### Cardinality of the marked set -/

/-- The set `marked = {0, 1, ∞}` of marked points on the Riemann sphere has cardinality `3`. -/
@[simp] theorem ThricePuncturedSphere.ncard_marked : marked.ncard = 3 := by
  have hmarked : marked =
      insert ((0 : ℂ) : OnePoint ℂ) (insert ((1 : ℂ) : OnePoint ℂ) {(∞ : OnePoint ℂ)}) :=
    Set.ext fun _ ↦ by simp [mem_marked]
  rw [hmarked, ncard_insert_of_notMem (by simp), ncard_insert_of_notMem (by simp), ncard_singleton]

namespace AnalyticBelyiPair

/-! ### Invariance, degree-one pairs, and sphere examples -/

/-- Isomorphic analytic Belyi pairs have the same Euler characteristic. -/
theorem Iso.eulerChar_eq {P Q : AnalyticBelyiPair.{u}} (e : P.Iso Q) :
    eulerChar P.X = eulerChar Q.X := e.toHomeomorph.eulerChar_eq

/-- Isomorphic analytic Belyi pairs have the same topological genus. -/
theorem Iso.genus_eq {P Q : AnalyticBelyiPair.{u}} (e : P.Iso Q) : genus P.X = genus Q.X :=
  e.toHomeomorph.toHomotopyEquiv.genus_eq

/-- **An analytic Belyi pair of degree one has Euler characteristic `2`.** -/
theorem eulerChar_X_eq_two_of_degree_eq_one {P : AnalyticBelyiPair.{u}} (hP : degree P.β = 1) :
    eulerChar P.X = 2 := by
  let e : P.X ≃ₜ sphere (0 : EuclideanSpace ℝ (ULift.{u} (Fin 3))) 1 :=
    (biholomorphOfDegreeEqOne P.β hP).toHomeomorph.trans
      (onePointEquivSphereOfFinrankEq (ι := ULift.{u} (Fin 3))
        (by simp [Complex.finrank_real_complex]))
  rw [e.eulerChar_eq, eulerChar_sphere (n := 2) (by simp)]; norm_num

/-- **An analytic Belyi pair of degree one has genus `0`.** -/
theorem genus_X_eq_zero_of_degree_eq_one {P : AnalyticBelyiPair.{u}} (hP : degree P.β = 1) :
    genus P.X = 0 :=
  genus_eq_of_eulerChar_eq (by rw [eulerChar_X_eq_two_of_degree_eq_one hP]; norm_num)

/-- The power Belyi pair `z ↦ z ^ n` on the Riemann sphere has Euler characteristic `2`. -/
@[simp] theorem eulerChar_X_pow {n : ℕ} (hn : n ≠ 0) : eulerChar (pow hn).X = 2 := by
  rw [pow, eulerChar_onePoint, Complex.finrank_real_complex]; norm_num

/-- The power Belyi pair `z ↦ z ^ n` on the Riemann sphere has genus `0`. -/
@[simp] theorem genus_X_pow {n : ℕ} (hn : n ≠ 0) : genus (pow hn).X = 0 := genus_onePoint_complex

/-- The Chebyshev Belyi pair `z ↦ 4z(1 - z)` on the Riemann sphere has Euler characteristic `2`. -/
@[simp] theorem eulerChar_X_chebyshev : eulerChar chebyshev.X = 2 := by
  rw [chebyshev, eulerChar_onePoint, Complex.finrank_real_complex]; norm_num

/-- The Chebyshev Belyi pair `z ↦ 4z(1 - z)` on the Riemann sphere has genus `0`. -/
@[simp] theorem genus_X_chebyshev : genus chebyshev.X = 0 := genus_onePoint_complex

/-- The Euler characteristic of an isomorphism class of degree-`n` analytic Belyi pairs. -/
def isoClassEulerChar (n : ℕ) : Quotient (isoSetoid.{u} n) → ℤ :=
  Quotient.lift (fun P ↦ eulerChar P.1.X) fun _ _ h ↦ (isoSetoid_r.1 h).elim Iso.eulerChar_eq

/-- On the class of a pair, `isoClassEulerChar` evaluates to `eulerChar P.1.X`. -/
@[simp] theorem isoClassEulerChar_mk {n : ℕ} (P : {P : AnalyticBelyiPair.{u} // degree P.β = n}) :
    isoClassEulerChar n ⟦P⟧ = eulerChar P.1.X := (rfl)

/-- The topological genus of an isomorphism class of degree-`n` analytic Belyi pairs. -/
def isoClassGenus (n : ℕ) : Quotient (isoSetoid.{u} n) → ℕ :=
  Quotient.lift (fun P ↦ genus P.1.X) fun _ _ h ↦ (isoSetoid_r.1 h).elim Iso.genus_eq

/-- On the class of a pair, `isoClassGenus` evaluates to `genus P.1.X`. -/
@[simp] theorem isoClassGenus_mk {n : ℕ} (P : {P : AnalyticBelyiPair.{u} // degree P.β = n}) :
    isoClassGenus n ⟦P⟧ = genus P.1.X := (rfl)

/-! ### Three-fibre decomposition of ramification -/

/-- Every branch value of a Belyi map belongs to `marked = {0, 1, ∞}`. -/
theorem branchValues_subset_marked (P : AnalyticBelyiPair.{u}) : P.β.branchValues ⊆ marked :=
  fun _ hy ↦ by simpa only [mem_marked, mem_insert_iff, mem_singleton_iff] using
    P.branchValues_subset hy

/-- Over `marked`, `(P.β ⁻¹' marked).ncard + ramificationDegree P.β = 3 * degree P.β`. -/
theorem ncard_preimage_marked_add_ramificationDegree_β (P : AnalyticBelyiPair.{u}) :
    (P.β ⁻¹' marked).ncard + ramificationDegree P.β = 3 * degree P.β := by
  rw [P.β.ncard_preimage_add_ramificationDegree finite_marked P.branchValues_subset_marked,
    ncard_marked, mul_comm]

/-- The preimage of `marked` splits into the three disjoint fibres over `0`, `1` and `∞`. -/
theorem ncard_preimage_marked (P : AnalyticBelyiPair.{u}) :
    (P.β ⁻¹' marked).ncard = (P.β ⁻¹' {((0 : ℂ) : OnePoint ℂ)}).ncard +
      (P.β ⁻¹' {((1 : ℂ) : OnePoint ℂ)}).ncard + (P.β ⁻¹' {(∞ : OnePoint ℂ)}).ncard := by
  have hpre : P.β ⁻¹' marked =
      (P.β ⁻¹' {((0 : ℂ) : OnePoint ℂ)} ∪ P.β ⁻¹' {((1 : ℂ) : OnePoint ℂ)}) ∪
        P.β ⁻¹' {(∞ : OnePoint ℂ)} := Set.ext fun _ ↦ by simp [mem_marked, or_assoc]
  have hdisj01 : Disjoint (P.β ⁻¹' {((0 : ℂ) : OnePoint ℂ)}) (P.β ⁻¹' {((1 : ℂ) : OnePoint ℂ)}) :=
    Set.disjoint_left.2 fun _ h0 h1 ↦ zero_ne_one (OnePoint.coe_injective (h0.symm.trans h1))
  have hdisj_inf : Disjoint (P.β ⁻¹' {((0 : ℂ) : OnePoint ℂ)} ∪ P.β ⁻¹' {((1 : ℂ) : OnePoint ℂ)})
      (P.β ⁻¹' {(∞ : OnePoint ℂ)}) :=
    Set.disjoint_left.2 fun _ hx hinf ↦ hx.elim
      (fun h0 ↦ OnePoint.coe_ne_infty 0 (h0.symm.trans hinf))
      (fun h1 ↦ OnePoint.coe_ne_infty 1 (h1.symm.trans hinf))
  rw [hpre, ncard_union_eq hdisj_inf
      ((P.β.finite_fiber _).union (P.β.finite_fiber _)) (P.β.finite_fiber _),
    ncard_union_eq hdisj01 (P.β.finite_fiber _) (P.β.finite_fiber _)]

/-- **Three-fibre decomposition of the ramification degree** over `0`, `1` and `∞`. -/
theorem ramificationDegree_β_eq_sum_three_fibers (P : AnalyticBelyiPair.{u}) :
    ramificationDegree P.β =
      (∑ x ∈ (P.β.finite_fiber ((0 : ℂ) : OnePoint ℂ)).toFinset, (localMultiplicity P.β x - 1)) +
      (∑ x ∈ (P.β.finite_fiber ((1 : ℂ) : OnePoint ℂ)).toFinset, (localMultiplicity P.β x - 1)) +
      (∑ x ∈ (P.β.finite_fiber (∞ : OnePoint ℂ)).toFinset, (localMultiplicity P.β x - 1)) := by
  have h0 := card_fiber_add_sum_localMultiplicity_sub_one P.β ((0 : ℂ) : OnePoint ℂ)
  have h1 := card_fiber_add_sum_localMultiplicity_sub_one P.β ((1 : ℂ) : OnePoint ℂ)
  have hinf := card_fiber_add_sum_localMultiplicity_sub_one P.β (∞ : OnePoint ℂ)
  rw [← ncard_eq_toFinset_card _ (P.β.finite_fiber _)] at h0 h1 hinf
  have htot := P.ncard_preimage_marked_add_ramificationDegree_β
  rw [P.ncard_preimage_marked] at htot; omega

/-! ### Monodromy cycle counts, Euler characteristic, and genus in `Type 0` -/

section TypeZero

variable (P : AnalyticBelyiPair.{0}) {n : ℕ} (ν : P.restrict ⁻¹' {basePt} ≃ Fin n)

private theorem card_finite_fiber_eq_orbitCount {P : AnalyticBelyiPair.{0}} {y : OnePoint ℂ}
    {σ : Equiv.Perm (Fin n)}
    (h : (P.β.finite_fiber y).toFinset.val.map (localMultiplicity P.β) = fullCycleType σ) :
    (P.β.finite_fiber y).toFinset.card = orbitCount σ := by
  have hc := congrArg Multiset.card h
  rwa [Multiset.card_map, Finset.card_val, fullCycleType_def,
    ← orbitCount_eq_card_parts_partition] at hc

/-- The number of points of `P.X` over `0` is `orbitCount σ0` of the monodromy triple. -/
theorem card_finite_fiber_zero :
    (P.β.finite_fiber ((0 : ℂ) : OnePoint ℂ)).toFinset.card =
      orbitCount (P.isCoveringMap_restrict.monodromyTriple ν).σ0 :=
  card_finite_fiber_eq_orbitCount (P.map_localMultiplicity_fiber_zero ν)

/-- The number of points of `P.X` over `1` is `orbitCount σ1` of the monodromy triple. -/
theorem card_finite_fiber_one :
    (P.β.finite_fiber ((1 : ℂ) : OnePoint ℂ)).toFinset.card =
      orbitCount (P.isCoveringMap_restrict.monodromyTriple ν).σ1 :=
  card_finite_fiber_eq_orbitCount (P.map_localMultiplicity_fiber_one ν)

/-- The number of points of `P.X` over `∞` is `orbitCount σinf` of the monodromy triple. -/
theorem card_finite_fiber_inf :
    (P.β.finite_fiber (∞ : OnePoint ℂ)).toFinset.card =
      orbitCount (P.isCoveringMap_restrict.monodromyTriple ν).σinf :=
  card_finite_fiber_eq_orbitCount (P.map_localMultiplicity_fiber_inf ν)

/-- The `Set.ncard` of the fibre of `P.β` over `0` is `orbitCount σ0`. -/
theorem ncard_preimage_singleton_zero :
    (P.β ⁻¹' {((0 : ℂ) : OnePoint ℂ)}).ncard =
      orbitCount (P.isCoveringMap_restrict.monodromyTriple ν).σ0 :=
  (ncard_eq_toFinset_card _ (P.β.finite_fiber _)).trans (P.card_finite_fiber_zero ν)

/-- The `Set.ncard` of the fibre of `P.β` over `1` is `orbitCount σ1`. -/
theorem ncard_preimage_singleton_one :
    (P.β ⁻¹' {((1 : ℂ) : OnePoint ℂ)}).ncard =
      orbitCount (P.isCoveringMap_restrict.monodromyTriple ν).σ1 :=
  (ncard_eq_toFinset_card _ (P.β.finite_fiber _)).trans (P.card_finite_fiber_one ν)

/-- The `Set.ncard` of the fibre of `P.β` over `∞` is `orbitCount σinf`. -/
theorem ncard_preimage_singleton_inf :
    (P.β ⁻¹' {(∞ : OnePoint ℂ)}).ncard =
      orbitCount (P.isCoveringMap_restrict.monodromyTriple ν).σinf :=
  (ncard_eq_toFinset_card _ (P.β.finite_fiber _)).trans (P.card_finite_fiber_inf ν)

/-- `(P.β ⁻¹' marked).ncard` equals `orbitCount σ0 + orbitCount σ1 + orbitCount σinf`. -/
theorem ncard_preimage_marked_eq_orbitCount :
    (P.β ⁻¹' marked).ncard =
      orbitCount (P.isCoveringMap_restrict.monodromyTriple ν).σ0 +
        orbitCount (P.isCoveringMap_restrict.monodromyTriple ν).σ1 +
        orbitCount (P.isCoveringMap_restrict.monodromyTriple ν).σinf := by
  rw [P.ncard_preimage_marked, P.ncard_preimage_singleton_zero ν,
    P.ncard_preimage_singleton_one ν, P.ncard_preimage_singleton_inf ν]

/-- Over `0`, the local ramification indices `e_x - 1` sum to `n - orbitCount σ0`. -/
theorem sum_localMultiplicity_sub_one_fiber_zero :
    ∑ x ∈ (P.β.finite_fiber ((0 : ℂ) : OnePoint ℂ)).toFinset, (localMultiplicity P.β x - 1) =
      n - orbitCount (P.isCoveringMap_restrict.monodromyTriple ν).σ0 := by
  have h := card_fiber_add_sum_localMultiplicity_sub_one P.β ((0 : ℂ) : OnePoint ℂ)
  rw [P.card_finite_fiber_zero ν, P.degree_β_eq_of_restrict_preimage_singleton_equiv ν] at h; omega

/-- Over `1`, the local ramification indices `e_x - 1` sum to `n - orbitCount σ1`. -/
theorem sum_localMultiplicity_sub_one_fiber_one :
    ∑ x ∈ (P.β.finite_fiber ((1 : ℂ) : OnePoint ℂ)).toFinset, (localMultiplicity P.β x - 1) =
      n - orbitCount (P.isCoveringMap_restrict.monodromyTriple ν).σ1 := by
  have h := card_fiber_add_sum_localMultiplicity_sub_one P.β ((1 : ℂ) : OnePoint ℂ)
  rw [P.card_finite_fiber_one ν, P.degree_β_eq_of_restrict_preimage_singleton_equiv ν] at h; omega

/-- Over `∞`, the local ramification indices `e_x - 1` sum to `n - orbitCount σinf`. -/
theorem sum_localMultiplicity_sub_one_fiber_inf :
    ∑ x ∈ (P.β.finite_fiber (∞ : OnePoint ℂ)).toFinset, (localMultiplicity P.β x - 1) =
      n - orbitCount (P.isCoveringMap_restrict.monodromyTriple ν).σinf := by
  have h := card_fiber_add_sum_localMultiplicity_sub_one P.β (∞ : OnePoint ℂ)
  rw [P.card_finite_fiber_inf ν, P.degree_β_eq_of_restrict_preimage_singleton_equiv ν] at h; omega

/-- **Total ramification from monodromy**: `ramificationDegree P.β = 2 * degree P.β - χ(t)`. -/
theorem natCast_ramificationDegree_β_eq_two_mul_degree_sub_eulerChar :
    (ramificationDegree P.β : ℤ) =
      2 * (degree P.β : ℤ) - (P.isCoveringMap_restrict.monodromyTriple ν).eulerChar := by
  have htot := P.ncard_preimage_marked_add_ramificationDegree_β
  rw [P.ncard_preimage_marked_eq_orbitCount ν,
    P.degree_β_eq_of_restrict_preimage_singleton_equiv ν] at htot
  rw [P.degree_β_eq_of_restrict_preimage_singleton_equiv ν, PermutationTriple.eulerChar_def]; omega

/-- **The Euler characteristic of an analytic Belyi pair is that of its monodromy triple.** -/
theorem eulerChar_X_eq_eulerChar_monodromyTriple :
    eulerChar P.X = (P.isCoveringMap_restrict.monodromyTriple ν).eulerChar := by
  linear_combination P.β.eulerChar_eq_two_mul_degree_sub_ramificationDegree -
    P.natCast_ramificationDegree_β_eq_two_mul_degree_sub_eulerChar ν

/-- **The topological genus of an analytic Belyi pair is the genus of its monodromy triple.** -/
theorem genus_X_eq_genus_monodromyTriple :
    genus P.X = (P.isCoveringMap_restrict.monodromyTriple ν).genus := by
  rw [genus_def, PermutationTriple.genus_def, P.eulerChar_X_eq_eulerChar_monodromyTriple ν]

/-- **Euler characteristic in terms of genus**: `eulerChar P.X = 2 - 2 * genus P.X`. -/
theorem eulerChar_X_eq_two_sub_two_mul_genus : eulerChar P.X = 2 - 2 * (genus P.X : ℤ) := by
  obtain ⟨ν'⟩ := P.nonempty_restrict_preimage_singleton_equiv basePt
  rw [P.eulerChar_X_eq_eulerChar_monodromyTriple ν', P.genus_X_eq_genus_monodromyTriple ν']
  exact (P.isCoveringMap_restrict.isConnected_monodromyTriple ν').two_sub_two_mul_genus.symm

/-- **Riemann–Hurwitz**: `2 * genus P.X - 2 = -2 * degree P.β + ramificationDegree P.β`. -/
theorem two_mul_genus_X_sub_two_eq :
    2 * (genus P.X : ℤ) - 2 = -2 * (degree P.β : ℤ) + ramificationDegree P.β := by
  linear_combination P.eulerChar_X_eq_two_sub_two_mul_genus -
    P.β.eulerChar_eq_two_mul_degree_sub_ramificationDegree

/-- **Riemann–Hurwitz in genus form**, with the target genus `genus (OnePoint ℂ)` written out. -/
theorem two_mul_genus_X_sub_two_eq_degree_mul_genus_onePoint :
    2 * (genus P.X : ℤ) - 2 =
      (degree P.β : ℤ) * (2 * (genus (OnePoint ℂ) : ℤ) - 2) + ramificationDegree P.β := by
  rw [genus_onePoint_complex]; linear_combination P.two_mul_genus_X_sub_two_eq

end TypeZero

/-- The equivalence `isoClassEquivConnectedIsoClass` preserves the Euler characteristic. -/
@[simp] theorem eulerChar_isoClassEquivConnectedIsoClass {n : ℕ} (P : Quotient (isoSetoid.{0} n)) :
    (isoClassEquivConnectedIsoClass n P).eulerChar = isoClassEulerChar n P :=
  Quotient.inductionOn P fun P ↦ by
    obtain ⟨ν⟩ := P.1.nonempty_restrict_preimage_singleton_equiv basePt
    rw [isoClassEquivConnectedIsoClass_mk P (ν.trans (finCongr P.2)),
      ConnectedIsoClass.eulerChar_mk, isoClassEulerChar_mk,
      P.1.eulerChar_X_eq_eulerChar_monodromyTriple]

/-- The equivalence `isoClassEquivConnectedIsoClass` preserves the genus. -/
@[simp] theorem genus_isoClassEquivConnectedIsoClass {n : ℕ} (P : Quotient (isoSetoid.{0} n)) :
    (isoClassEquivConnectedIsoClass n P).genus = isoClassGenus n P :=
  Quotient.inductionOn P fun P ↦ by
    obtain ⟨ν⟩ := P.1.nonempty_restrict_preimage_singleton_equiv basePt
    rw [isoClassEquivConnectedIsoClass_mk P (ν.trans (finCongr P.2)), ConnectedIsoClass.genus_mk,
      isoClassGenus_mk, P.1.genus_X_eq_genus_monodromyTriple]

end AnalyticBelyiPair

/-! ### Reconciliation on filled covers and topological branched covers -/

namespace ConnectedCover

variable {n : ℕ} (C : ConnectedCover (X := TopCat.of ThricePuncturedSphere) basePt n)

/-- The Euler characteristic of `C.toAnalyticBelyiPair.X` equals that of the monodromy triple. -/
theorem eulerChar_toAnalyticBelyiPair (ν : ⇑C.cover.proj ⁻¹' {basePt} ≃ Fin n) :
    eulerChar C.toAnalyticBelyiPair.X =
      (C.cover.isCoveringMap_proj.monodromyTriple ν).eulerChar := by
  obtain ⟨ν'⟩ := C.toAnalyticBelyiPair.nonempty_restrict_preimage_singleton_equiv basePt
  let ν'' := ν'.trans (finCongr C.degree_toAnalyticBelyiPair)
  exact (C.toAnalyticBelyiPair.eulerChar_X_eq_eulerChar_monodromyTriple ν'').trans
    (PermutationTriple.eulerChar_eq_of_equivalent (PermutationTriple.IsoClass.mk_eq_mk_iff.1
      (C.isoClass_monodromyTriple_toAnalyticBelyiPair ν'' ν)))

/-- The topological genus of `C.toAnalyticBelyiPair.X` equals that of the monodromy triple. -/
theorem genus_toAnalyticBelyiPair (ν : ⇑C.cover.proj ⁻¹' {basePt} ≃ Fin n) :
    genus C.toAnalyticBelyiPair.X = (C.cover.isCoveringMap_proj.monodromyTriple ν).genus := by
  rw [genus_def, PermutationTriple.genus_def, C.eulerChar_toAnalyticBelyiPair ν]

/-- **Reconciliation of the analytic and filled-cover ramification sums.** -/
theorem natCast_ramificationDegree_toAnalyticBelyiPair [Fintype (FilledPoint ⇑C.cover.proj)] :
    (ramificationDegree C.toAnalyticBelyiPair.β : ℤ) =
      ∑ i : FilledPoint ⇑C.cover.proj, ((FilledCover.degree ⇑C.cover.proj i : ℤ) - 1) := by
  obtain ⟨ν⟩ := C.nonempty_equiv_fin
  obtain ⟨ν'⟩ := C.toAnalyticBelyiPair.nonempty_restrict_preimage_singleton_equiv basePt
  let ν'' := ν'.trans (finCongr C.degree_toAnalyticBelyiPair)
  rw [C.toAnalyticBelyiPair.natCast_ramificationDegree_β_eq_two_mul_degree_sub_eulerChar ν'',
    C.degree_toAnalyticBelyiPair, FilledCover.sum_degree_sub_one C.cover.isCoveringMap_proj ν,
    PermutationTriple.eulerChar_eq_of_equivalent (PermutationTriple.IsoClass.mk_eq_mk_iff.1
      (C.isoClass_monodromyTriple_toAnalyticBelyiPair ν'' ν))]

end ConnectedCover

namespace TopBranchedCover

/-- **Every topological branched cover is isomorphic to `P.toTopBranchedCover h` for some `P`.** -/
theorem exists_iso_toTopBranchedCover {n : ℕ} (X : TopBranchedCover.{0} n) :
    ∃ (P : AnalyticBelyiPair.{0}) (h : degree P.β = n),
      Nonempty (X.Iso (P.toTopBranchedCover h)) := by
  obtain ⟨q, hq⟩ := AnalyticBelyiPair.toTopBranchedCoverIsoClass_surjective n (.mk X)
  obtain ⟨⟨P, h⟩, rfl⟩ := Quotient.exists_rep q
  rw [AnalyticBelyiPair.toTopBranchedCoverIsoClass_mk, IsoClass.mk_eq_mk_iff] at hq
  exact ⟨P, h, hq.map Iso.symm⟩

/-- Every topological branched cover `X : TopBranchedCover.{0} n` has finite CW type. -/
instance instFiniteCWType {n : ℕ} (X : TopBranchedCover.{0} n) : FiniteCWType X.Z := by
  obtain ⟨P, _, ⟨ι⟩⟩ := X.exists_iso_toTopBranchedCover
  exact Homeomorph.finiteCWType (Y := P.X) ι.toHomeomorph

/-- Isomorphic topological branched covers have the same Euler characteristic. -/
theorem Iso.eulerChar_eq {n : ℕ} {X Y : TopBranchedCover.{u} n} [FiniteCWType X.Z]
    [FiniteCWType Y.Z] (ι : X.Iso Y) : eulerChar X.Z = eulerChar Y.Z :=
  ι.toHomeomorph.eulerChar_eq

/-- Isomorphic topological branched covers have the same topological genus. -/
theorem Iso.genus_eq {n : ℕ} {X Y : TopBranchedCover.{u} n} [FiniteCWType X.Z] [FiniteCWType Y.Z]
    (ι : X.Iso Y) : genus X.Z = genus Y.Z :=
  ι.toHomeomorph.toHomotopyEquiv.genus_eq

/-- **The Euler characteristic of a topological branched cover is that of its monodromy triple.** -/
theorem eulerChar_Z_eq_eulerChar_monodromyTriple {n : ℕ} (X : TopBranchedCover.{0} n)
    (ν : X.restrict ⁻¹' {basePt} ≃ Fin n) :
    eulerChar X.Z = (X.isCoveringMap_restrict.monodromyTriple ν).eulerChar := by
  obtain ⟨P, h, ⟨ι⟩⟩ := X.exists_iso_toTopBranchedCover
  obtain ⟨νP⟩ := P.nonempty_restrict_preimage_singleton_equiv basePt
  let νP' := νP.trans (finCongr h)
  obtain ⟨νT⟩ := (P.toTopBranchedCover h).nonempty_restrict_preimage_singleton_equiv basePt
  rw [ι.eulerChar_eq]
  refine (P.eulerChar_X_eq_eulerChar_monodromyTriple νP').trans
    (PermutationTriple.eulerChar_eq_of_equivalent (PermutationTriple.IsoClass.mk_eq_mk_iff.1 ?_))
  exact (P.isoClass_monodromyTriple_toTopBranchedCover h νP' νT).symm.trans
    (X.isCoveringMap_restrict.isoClass_monodromyTriple_eq_of_homeomorph ν
      (P.toTopBranchedCover h).isCoveringMap_restrict νT ι.restrict (funext ι.restrict_restrict))

/-- **The topological genus of a topological branched cover is that of its monodromy triple.** -/
theorem genus_Z_eq_genus_monodromyTriple {n : ℕ} (X : TopBranchedCover.{0} n)
    (ν : X.restrict ⁻¹' {basePt} ≃ Fin n) :
    genus X.Z = (X.isCoveringMap_restrict.monodromyTriple ν).genus := by
  rw [genus_def, PermutationTriple.genus_def, X.eulerChar_Z_eq_eulerChar_monodromyTriple ν]

/-- Every `X : TopBranchedCover.{0} n` satisfies `eulerChar X.Z = 2 - 2 * genus X.Z`. -/
theorem eulerChar_Z_eq_two_sub_two_mul_genus {n : ℕ} (X : TopBranchedCover.{0} n) :
    eulerChar X.Z = 2 - 2 * (genus X.Z : ℤ) := by
  obtain ⟨ν⟩ := X.nonempty_restrict_preimage_singleton_equiv basePt
  rw [X.eulerChar_Z_eq_eulerChar_monodromyTriple ν, X.genus_Z_eq_genus_monodromyTriple ν]
  exact (X.isCoveringMap_restrict.isConnected_monodromyTriple ν).two_sub_two_mul_genus.symm

/-- The Euler characteristic of an isomorphism class of topological branched covers. -/
def IsoClass.eulerChar {n : ℕ} (c : IsoClass.{0} n) : ℤ :=
  TauCeti.eulerChar (surjInv mk_surjective c).Z

/-- On the class of `X`, `IsoClass.eulerChar` evaluates to `eulerChar X.Z`. -/
@[simp] theorem IsoClass.eulerChar_mk {n : ℕ} (X : TopBranchedCover.{0} n) :
    (IsoClass.mk X).eulerChar = TauCeti.eulerChar X.Z :=
  (mk_eq_mk_iff.1 (surjInv_eq mk_surjective (.mk X))).some.eulerChar_eq

/-- The topological genus of an isomorphism class of topological branched covers. -/
def IsoClass.genus {n : ℕ} (c : IsoClass.{0} n) : ℕ :=
  RiemannSurface.genus (surjInv mk_surjective c).Z

/-- On the class of `X`, `IsoClass.genus` evaluates to `genus X.Z`. -/
@[simp] theorem IsoClass.genus_mk {n : ℕ} (X : TopBranchedCover.{0} n) :
    (IsoClass.mk X).genus = RiemannSurface.genus X.Z :=
  (mk_eq_mk_iff.1 (surjInv_eq mk_surjective (.mk X))).some.genus_eq

end TopBranchedCover

namespace AnalyticBelyiPair

/-- Passing to the underlying topological branched cover preserves the Euler characteristic. -/
@[simp] theorem eulerChar_toTopBranchedCoverIsoClass {n : ℕ} (P : Quotient (isoSetoid.{0} n)) :
    (toTopBranchedCoverIsoClass n P).eulerChar = isoClassEulerChar n P :=
  Quotient.inductionOn P fun P ↦ by
    rw [toTopBranchedCoverIsoClass_mk, TopBranchedCover.IsoClass.eulerChar_mk,
      isoClassEulerChar_mk]; rfl

/-- Passing to the underlying topological branched cover preserves the topological genus. -/
@[simp] theorem genus_toTopBranchedCoverIsoClass {n : ℕ} (P : Quotient (isoSetoid.{0} n)) :
    (toTopBranchedCoverIsoClass n P).genus = isoClassGenus n P :=
  Quotient.inductionOn P fun P ↦ by
    rw [toTopBranchedCoverIsoClass_mk, TopBranchedCover.IsoClass.genus_mk,
      isoClassGenus_mk]; rfl

end AnalyticBelyiPair

end TauCeti

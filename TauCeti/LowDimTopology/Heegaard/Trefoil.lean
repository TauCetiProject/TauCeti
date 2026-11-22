/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.KnotEulerCharacteristic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Qify
import TauCeti.GroupTheory.Perm.Fin

/-!
# The genus-one doubly pointed Heegaard diagram of the trefoil

On the torus `ℝ² / ℤ²` let `α` be the circle `y = 0`, oriented by increasing `x`, and let `x₀`,
`x₁`, `x₂` be three points on it, in this order along `α`. Cutting the torus along `α` leaves an
annulus whose bottom and top boundary circles are both copies of `α`. The curve `β` meets this
annulus in three arcs:

* a *vertical* arc from `x₀` on the bottom circle to `x₁` on the top circle;
* a *rainbow* near the bottom circle from `x₁` to `x₂`, which together with the `α`-arc from `x₁`
  to `x₂` bounds a bigon `B_w` just above `α`;
* a rainbow near the top circle from `x₂` to `x₀`, which together with the `α`-arc from `x₂` to
  `x₀` bounds a bigon `B_z` just below `α`.

Orient `β` along `x₀ → x₁ → x₂ → x₀`. It crosses `α` upwards at `x₀` and `x₁` and downwards at
`x₂`, so `α · β = 1` and `(α, β)` is a genus-one Heegaard diagram of `S³`. The complement of
`α ∪ β` consists of the two bigons and a disk `R` with eight corners. Placing `w` in `B_w` and `z`
in `B_z` gives a doubly pointed diagram of a `(1, 1)`-knot, which is a trefoil. The
identification of the knot, like that of the region labels below with the complementary regions
of the curves, is geometric and is not formalized here; the computations below concern the
recorded incidence data.

`TauCeti.HeegaardRegionSystem.trefoil b` records this incidence data, with the points indexed by
`Fin 3`, the regions `R`, `B_w`, `B_z` by `0, 1, 2 : Fin 3`, and a basepoint `t` in the region
`b t`. The doubly pointed diagram is `trefoil ![1, 2]`, with `w = 0` and `z = 1`; the singly
pointed diagram `(Σ, α, β, w)` of `S³` is `trefoil fun _ : Unit => 1`.

The two bigons are domains from `x₀` to `x₂` (the bigon `B_z`) and from `x₁` to `x₂` (the bigon
`B_w`), each of Maslov index one, and the only domains from a generator to itself are the
multiples of the whole surface. Hence:

* the relative Alexander gradings are `A(x₀, x₂) = 1` and `A(x₁, x₂) = -1`, so, normalizing
  `A(x₂) = 0`, the three generators have Alexander gradings `1`, `-1`, `0`;
* the relative Maslov gradings, computed in the diagram pointed at `w`, are `gr(x₀, x₂) = 1` and
  `gr(x₁, x₂) = -1`, so, in the order `x₀`, `x₂`, `x₁` of decreasing Alexander grading, the
  Maslov grading drops by one at each step;
* no nonnegative domain joining two generators avoids both basepoints, so the hat knot Floer
  differential vanishes and `HFK̂` has one generator in each of the Alexander gradings `1`, `0`,
  `-1`, with this normalization. The bigon `B_z` joins the generators of Alexander gradings `1`
  and `0` with `n_z - n_w = 1`, and is not counted;
* the Alexander gradings `1`, `-1`, `0` form an Alexander function for `w`, the hypothesis of the
  Alexander filtration of the hat complex of the diagram `(Σ, α, β, w)`, whose count of domains
  avoiding `w` does include `B_z`, from `x₀` to `x₂`. That count is
  combinatorial: the region `R` has eight corners, so this diagram is not nice, and the count
  of domains is not claimed to be the count of holomorphic disks.

The relative gradings are determined only up to an overall shift. The Maslov gradings `0`, `-2`,
`-1` and the Alexander gradings `1`, `-1`, `0` of `x₀`, `x₁`, `x₂` are integer lifts of them,
a knot grading in the sense of `TauCeti.HeegaardRegionSystem.IsKnotGrading`
(`TauCeti.HeegaardRegionSystem.isKnotGrading_trefoil`). Their graded Euler characteristic
`∑ₓ (-1)^{M(x)} T^{A(x)}` is `T - 1 + T⁻¹`, the symmetrized Alexander polynomial of the trefoil
(`TauCeti.HeegaardRegionSystem.gradedEulerChar_trefoil`); forgetting the Maslov parity would give
`T + 1 + T⁻¹` instead. Since it is symmetric, these are the only Alexander gradings of a knot
grading of this diagram with symmetric graded Euler characteristic
(`TauCeti.HeegaardRegionSystem.eq_trefoilAlexanderGrading_of_isKnotGrading`). The identification
of this symmetric normalization with the one by a Seifert surface, and of the Maslov normalization
with the absolute grading of `HF̂(S³)`, is not formalized here.

## Main definitions

* `TauCeti.HeegaardRegionSystem.trefoil`: the diagram, with its basepoints in given regions.
* `TauCeti.HeegaardRegionSystem.trefoilGenerator`: its three generators.
* `TauCeti.HeegaardRegionSystem.trefoilGeneratorEquiv`: the generators indexed by `Fin 3`.
* `TauCeti.HeegaardRegionSystem.trefoilMaslovGrading` and
  `TauCeti.HeegaardRegionSystem.trefoilAlexanderGrading`: their integer gradings.

## Main results

* `TauCeti.HeegaardRegionSystem.isDomainBetween_trefoil_single_two` and
  `TauCeti.HeegaardRegionSystem.isDomainBetween_trefoil_single_one`: the bigons `B_z` and `B_w`
  are domains from `x₀` to `x₂` and from `x₁` to `x₂`.
* `TauCeti.HeegaardRegionSystem.isDomainBetween_trefoil_self_iff`: the domains from a generator to
  itself are the multiples of the whole surface.
* `TauCeti.HeegaardRegionSystem.periodicDomains_trefoil` and
  `TauCeti.HeegaardRegionSystem.weaklyAdmissible_trefoil`: once a basepoint is placed, the only
  periodic domain is zero, so the diagram is weakly admissible.
* `TauCeti.HeegaardRegionSystem.periodicAlexanderValues_trefoil`: for any placement of the
  basepoints, the Alexander grading is an integer.
* `TauCeti.HeegaardRegionSystem.relativeAlexanderGrading_trefoil_zero_two` and
  `TauCeti.HeegaardRegionSystem.relativeAlexanderGrading_trefoil_one_two`: the relative Alexander
  gradings.
* `TauCeti.HeegaardRegionSystem.relativeGrading_trefoil_zero_two` and
  `TauCeti.HeegaardRegionSystem.relativeGrading_trefoil_one_two`: the relative Maslov gradings.
* `TauCeti.HeegaardRegionSystem.hatDomains_trefoil` and
  `TauCeti.HeegaardRegionSystem.hatDifferential_trefoil`: the hat knot Floer differential
  vanishes.
* `TauCeti.HeegaardRegionSystem.isKnotGrading_trefoil`: integer Maslov and Alexander gradings.
* `TauCeti.HeegaardRegionSystem.gradedEulerChar_trefoil`: the graded Euler characteristic is
  `T - 1 + T⁻¹`.
* `TauCeti.HeegaardRegionSystem.eq_trefoilAlexanderGrading_of_isKnotGrading`: the symmetric
  Alexander grading is unique.
* `TauCeti.HeegaardRegionSystem.isAlexanderFunction_trefoil`: the Alexander gradings `1`, `-1`,
  `0` satisfy the hypothesis of the Alexander filtration
  of the hat complex of the diagram pointed at `w`.
* `TauCeti.HeegaardRegionSystem.hatCoefficient_trefoil_zero_two`: in that complex the bigon
  `B_z` gives a coefficient one from `x₀` to `x₂`, lowering the Alexander grading by one.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and knot invariants*, Adv. Math. **186** (2004),
  [arXiv:math/0209056](https://arxiv.org/abs/math/0209056), for doubly pointed diagrams, the
  gradings of knot Floer homology and its computation for the trefoil.
* H. Goda, H. Matsuda and T. Morifuji, *Knot Floer homology of (1,1)-knots*, Geom. Dedicata
  **112** (2005), 197–214, for genus-one doubly pointed diagrams built from one vertical arc and
  rainbows.
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

variable {B : Type*}

/-- In `Fin 3`, `-1 = 2`. -/
private theorem neg_one_fin_three : (-1 : Fin 3) = 2 :=
  rfl

/-- The genus-one doubly pointed Heegaard diagram of the trefoil, with a basepoint `t` in the
region `b t`. The points `x₀`, `x₁`, `x₂` are indexed by `Fin 3` and follow each other in this
order along both curves. The regions `0`, `1`, `2` are the disk `R` with eight corners and the
bigons `B_w` and `B_z`. The `α`-arc starting at `x₁` has `B_w` on its left, the `α`-arc starting
at `x₂` has `B_z` on its right, the `β`-arc starting at `x₁` has `B_w` on its right and the
`β`-arc starting at `x₂` has `B_z` on its left; every other side of an arc is `R`. -/
def trefoil (b : B → Fin 3) : HeegaardRegionSystem 1 (Fin 3) (Fin 3) B where
  pointFintype := inferInstance
  alpha _ := 0
  beta _ := 0
  alphaNext := finRotate 3
  alphaNext_isCycleOn i :=
    Set.eq_univ_of_forall (s := {_p : Fin 3 | (0 : Fin 1) = i}) (fun _ => Subsingleton.elim _ _) ▸
      isCycleOn_finRotate
  betaNext := finRotate 3
  betaNext_isCycleOn i :=
    Set.eq_univ_of_forall (s := {_p : Fin 3 | (0 : Fin 1) = i}) (fun _ => Subsingleton.elim _ _) ▸
      isCycleOn_finRotate
  alphaLeft j := if j = 1 then 1 else 0
  alphaRight j := if j = 2 then 2 else 0
  betaLeft j := if j = 2 then 2 else 0
  betaRight j := if j = 1 then 1 else 0
  regionNonempty := inferInstance
  crossingCompatible := by simp only [isCrossingCompatible_iff]; decide
  regionCovered r := Or.inl (by revert r; decide)
  basepoint := b

variable {b : B → Fin 3}

/-- All three intersection points lie on the unique `α`-curve. -/
@[simp]
theorem trefoil_alpha (j : Fin 3) : (trefoil b).alpha j = 0 :=
  (rfl)

/-- All three intersection points lie on the unique `β`-curve. -/
@[simp]
theorem trefoil_beta (j : Fin 3) : (trefoil b).beta j = 0 :=
  (rfl)

@[simp]
theorem trefoil_alphaNext_apply (j : Fin 3) : (trefoil b).alphaNext j = j + 1 :=
  finRotate_apply j

@[simp]
theorem trefoil_betaNext_apply (j : Fin 3) : (trefoil b).betaNext j = j + 1 :=
  finRotate_apply j

@[simp]
theorem trefoil_alphaNext_symm_apply (j : Fin 3) : (trefoil b).alphaNext.symm j = j - 1 := by
  rw [Equiv.symm_apply_eq, trefoil_alphaNext_apply, sub_add_cancel]

@[simp]
theorem trefoil_betaNext_symm_apply (j : Fin 3) : (trefoil b).betaNext.symm j = j - 1 := by
  rw [Equiv.symm_apply_eq, trefoil_betaNext_apply, sub_add_cancel]

@[simp]
theorem trefoil_alphaLeft (j : Fin 3) : (trefoil b).alphaLeft j = if j = 1 then 1 else 0 :=
  (rfl)

@[simp]
theorem trefoil_alphaRight (j : Fin 3) : (trefoil b).alphaRight j = if j = 2 then 2 else 0 :=
  (rfl)

@[simp]
theorem trefoil_betaLeft (j : Fin 3) : (trefoil b).betaLeft j = if j = 2 then 2 else 0 :=
  (rfl)

@[simp]
theorem trefoil_betaRight (j : Fin 3) : (trefoil b).betaRight j = if j = 1 then 1 else 0 :=
  (rfl)

@[simp]
theorem trefoil_basepoint (t : B) : (trefoil b).basepoint t = b t :=
  (rfl)

/-- The generator of `trefoil b` at the intersection point `x_a`. -/
def trefoilGenerator (b : B → Fin 3) (a : Fin 3) : (trefoil b).Generator :=
  (trefoil b).generatorOf 1 (fun _ => a) (fun _ => Subsingleton.elim _ _)
    (fun _ => Subsingleton.elim _ _)

/-- The unique point chosen by `trefoilGenerator b a` is `x_a`. -/
@[simp 1100]
theorem trefoilGenerator_point (a : Fin 3) (i : Fin 1) :
    (trefoil b).point (trefoilGenerator b a) i = a := by
  simp [trefoilGenerator]

/-- Every generator of `trefoil b` is the generator at its intersection point. -/
@[simp]
theorem trefoilGenerator_snd_zero (x : (trefoil b).Generator) : trefoilGenerator b (x.2 0) = x :=
  HeegaardIntersectionSystem.point_injective _ (funext fun i => by simp [Subsingleton.elim i 0])

/-- The generators of `trefoil b` correspond to the intersection points `x₀`, `x₁`, `x₂`. -/
@[expose, simps apply symm_apply]
def trefoilGeneratorEquiv (b : B → Fin 3) : Fin 3 ≃ (trefoil b).Generator where
  toFun := trefoilGenerator b
  invFun x := x.2 0
  left_inv a := by
    simpa only [HeegaardIntersectionSystem.point_apply] using trefoilGenerator_point (b := b) a 0
  right_inv := trefoilGenerator_snd_zero

/-- The generator chain of `trefoilGenerator b a` is supported at `x_a`. -/
@[simp 1100]
theorem generatorChain_trefoilGenerator (a q : Fin 3) :
    (trefoil b).generatorChain (trefoilGenerator b a) q = if a = q then 1 else 0 := by
  rw [HeegaardIntersectionSystem.generatorChain_apply]
  simp [trefoilGenerator]

/-- The value of the `α`-boundary cycle condition of `trefoil b` at the three points. -/
private theorem alphaArcBoundary_alphaBoundary_trefoil (D : Fin 3 → ℤ) (q : Fin 3) :
    (trefoil b).alphaArcBoundary ((trefoil b).alphaBoundary D) q =
      ![D 0 - D 2, D 0 - D 1, D 1 + D 2 - 2 * D 0] q := by
  fin_cases q
  · simp [neg_one_fin_three]
  · simp
  · simp
    ring

/-- The value of the `β`-boundary cycle condition of `trefoil b` at the three points. -/
private theorem betaArcBoundary_betaBoundary_trefoil (D : Fin 3 → ℤ) (q : Fin 3) :
    (trefoil b).betaArcBoundary ((trefoil b).betaBoundary D) q =
      ![D 2 - D 0, D 1 - D 0, 2 * D 0 - D 1 - D 2] q := by
  fin_cases q
  · simp [neg_one_fin_three]
  · simp
  · simp
    ring

/-- A domain of `trefoil b` joins `x_a` to `x_c` exactly when its multiplicities satisfy
`D R - D B_z = δ_{c,0} - δ_{a,0}` and `D R - D B_w = δ_{c,1} - δ_{a,1}`. -/
theorem isDomainBetween_trefoil_iff (a c : Fin 3) (D : Fin 3 → ℤ) :
    (trefoil b).IsDomainBetween (trefoilGenerator b a) (trefoilGenerator b c) D ↔
      D 0 - D 2 = (if c = 0 then 1 else 0) - (if a = 0 then 1 else 0) ∧
        D 0 - D 1 = (if c = 1 then 1 else 0) - (if a = 1 then 1 else 0) := by
  simp only [isDomainBetween_iff, funext_iff, alphaArcBoundary_alphaBoundary_trefoil,
    betaArcBoundary_betaBoundary_trefoil, Pi.sub_apply, generatorChain_trefoilGenerator]
  constructor
  · intro h
    have h0 := h.1 0
    have h1 := h.1 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact ⟨h0.trans (by simp), h1.trans (by simp)⟩
  · rintro ⟨h0, h1⟩
    refine ⟨fun q => ?_, fun q => ?_⟩ <;>
      fin_cases a <;> fin_cases c <;> fin_cases q <;> simp_all <;> omega

/-- The bigon `B_z` is a domain from `x₀` to `x₂`. -/
theorem isDomainBetween_trefoil_single_two :
    (trefoil b).IsDomainBetween (trefoilGenerator b 0) (trefoilGenerator b 2) (Pi.single 2 1) := by
  rw [isDomainBetween_trefoil_iff]
  decide

/-- The bigon `B_w` is a domain from `x₁` to `x₂`. -/
theorem isDomainBetween_trefoil_single_one :
    (trefoil b).IsDomainBetween (trefoilGenerator b 1) (trefoilGenerator b 2) (Pi.single 1 1) := by
  rw [isDomainBetween_trefoil_iff]
  decide

/-- The domains from a generator of `trefoil b` to itself are the multiples of the whole
surface. -/
theorem isDomainBetween_trefoil_self_iff (x : (trefoil b).Generator) (E : Fin 3 → ℤ) :
    (trefoil b).IsDomainBetween x x E ↔ E = E 0 • 1 := by
  rw [← trefoilGenerator_snd_zero x, isDomainBetween_trefoil_iff, funext_iff]
  simp only [sub_self, Fin.forall_fin_succ, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
  constructor
  · rintro ⟨h0, h1⟩
    simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, IsEmpty.forall_iff,
      and_true, true_and]
    omega
  · rintro ⟨-, h1, h2, -⟩
    simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at h1 h2
    omega

/-- A domain whose boundary is a combination of whole curves is a multiple of the whole surface. -/
private theorem trefoil_eq_smul_one_of_arcBoundary_eq_zero {E : Fin 3 → ℤ}
    (hα : (trefoil b).alphaArcBoundary ((trefoil b).alphaBoundary E) = 0)
    (hβ : (trefoil b).betaArcBoundary ((trefoil b).betaBoundary E) = 0) : E = E 0 • 1 :=
  (isDomainBetween_trefoil_self_iff (trefoilGenerator b 0) E).mp
    (isDomainBetween_self_iff_arcBoundary_eq_zero.mpr ⟨hα, hβ⟩)

/-- Once a basepoint is placed, the only periodic domain of `trefoil b` is zero. -/
theorem periodicDomains_trefoil [Nonempty B] : (trefoil b).periodicDomains = ⊥ := by
  refine (AddSubgroup.eq_bot_iff_forall _).mpr fun P hP => ?_
  obtain ⟨hz, hα, hβ⟩ := mem_periodicDomains_iff.mp hP
  have hP1 := trefoil_eq_smul_one_of_arcBoundary_eq_zero hα hβ
  obtain ⟨t⟩ := ‹Nonempty B›
  have h := congrFun hP1 (b t)
  have hzt : P (b t) = 0 := hz t
  simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] at h
  rw [hP1, ← h, hzt, zero_smul]

/-- Once a basepoint is placed, the diagram `trefoil b` is weakly admissible. -/
theorem weaklyAdmissible_trefoil [Nonempty B] : (trefoil b).WeaklyAdmissible := by
  rw [weaklyAdmissible_iff, periodicDomains_trefoil]
  intro P hP _
  exact hP

/-- The periodic Alexander values of `trefoil b` vanish for every pair of basepoints, so its
Alexander grading is an integer: the whole surface has the same multiplicity at `w` and at `z`. -/
@[simp]
theorem periodicAlexanderValues_trefoil (w z : B) :
    (trefoil b).periodicAlexanderValues w z = ⊥ := by
  refine periodicAlexanderValues_eq_bot_iff.mpr fun E hα hβ => ?_
  have h := trefoil_eq_smul_one_of_arcBoundary_eq_zero hα hβ
  rw [h]
  simp

/-- The generator `x₀` lies one Alexander grading above `x₂`, computed from the bigon `B_z`, which
contains `z` and not `w`. -/
@[simp]
theorem relativeAlexanderGrading_trefoil_zero_two :
    (trefoil ![1, 2]).relativeAlexanderGrading 0 1 (trefoilGenerator _ 0)
      (trefoilGenerator _ 2) = 1 := by
  rw [isDomainBetween_trefoil_single_two.relativeAlexanderGrading_eq
    (periodicAlexanderValues_trefoil 0 1)]
  decide

/-- The generator `x₁` lies one Alexander grading below `x₂`, computed from the bigon `B_w`, which
contains `w` and not `z`. -/
@[simp]
theorem relativeAlexanderGrading_trefoil_one_two :
    (trefoil ![1, 2]).relativeAlexanderGrading 0 1 (trefoilGenerator _ 1)
      (trefoilGenerator _ 2) = -1 := by
  rw [isDomainBetween_trefoil_single_one.relativeAlexanderGrading_eq
    (periodicAlexanderValues_trefoil 0 1)]
  decide

/-- The region `R` has eight corners and each bigon has two. -/
@[simp]
theorem cornerCount_trefoil (r : Fin 3) : (trefoil b).cornerCount r = ![8, 2, 2] r := by
  simp only [cornerCount_eq_card, cornerRegion_eq, trefoil_alphaLeft, trefoil_alphaRight,
    trefoil_alphaNext_symm_apply]
  revert r
  decide

/-- The bigon `B_z`, a disk with two corners, has Maslov index one as a domain from `x₀` to
`x₂`. -/
theorem maslovIndex_trefoil_single_two :
    (trefoil b).maslovIndex 1 (trefoilGenerator b 0) (trefoilGenerator b 2) (Pi.single 2 1) =
      1 := by
  norm_num +decide [maslovIndex_apply, eulerMeasure_apply, generatorPointMeasure_apply,
    pointMeasure_apply, Pi.single_apply]

/-- The bigon `B_w`, a disk with two corners, has Maslov index one as a domain from `x₁` to
`x₂`. -/
theorem maslovIndex_trefoil_single_one :
    (trefoil b).maslovIndex 1 (trefoilGenerator b 1) (trefoilGenerator b 2) (Pi.single 1 1) =
      1 := by
  norm_num [maslovIndex_apply, eulerMeasure_apply, generatorPointMeasure_apply,
    pointMeasure_apply, Pi.single_apply]

/-- In the diagram `(Σ, α, β, w)` of `S³`, the generator `x₀` lies one Maslov grading above `x₂`,
computed from the bigon `B_z`, which avoids `w`. -/
@[simp]
theorem relativeGrading_trefoil_zero_two :
    (trefoil fun _ : Unit => 1).relativeGrading 1 (trefoilGenerator _ 0)
      (trefoilGenerator _ 2) = 1 := by
  rw [isDomainBetween_trefoil_single_two.relativeGrading_eq
    (maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_of_subsingleton () (by decide))
    (by simp [periodicDomains_trefoil]), maslovIndex_trefoil_single_two]
  simp

/-- In the diagram `(Σ, α, β, w)` of `S³`, the generator `x₁` lies one Maslov grading below `x₂`,
computed from the bigon `B_w`, which contains `w`. -/
@[simp]
theorem relativeGrading_trefoil_one_two :
    (trefoil fun _ : Unit => 1).relativeGrading 1 (trefoilGenerator _ 1)
      (trefoilGenerator _ 2) = -1 := by
  rw [isDomainBetween_trefoil_single_one.relativeGrading_eq
    (maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_of_subsingleton () (by decide))
    (by simp [periodicDomains_trefoil]), maslovIndex_trefoil_single_one]
  norm_num

/-- A domain from `x_a` to `x_c` with multiplicity zero on both bigons is zero and joins a
generator to itself. -/
private theorem trefoil_eq_zero_of_isDomainBetween {a c : Fin 3} {D : Fin 3 → ℤ}
    (hD : (trefoil b).IsDomainBetween (trefoilGenerator b a) (trefoilGenerator b c) D)
    (h1 : D 1 = 0) (h2 : D 2 = 0) : D = 0 := by
  rw [isDomainBetween_trefoil_iff, h1, h2] at hD
  have h0 : D 0 = 0 := by
    fin_cases a <;> fin_cases c <;> simp at hD <;> omega
  funext r
  fin_cases r <;> simp [h0, h1, h2]

/-- No domain is counted by the hat differential of the doubly pointed diagram: a nonnegative
domain joining two generators and avoiding both bigons is zero, of Maslov index zero. -/
@[simp]
theorem hatDomains_trefoil (χ : Fin 3 → ℤ) (x y : (trefoil ![1, 2]).Generator) :
    (trefoil ![1, 2]).hatDomains χ x y = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun D hD => ?_
  obtain ⟨hD, hz, -, hμ⟩ := mem_hatDomains_iff.mp hD
  rw [← trefoilGenerator_snd_zero x, ← trefoilGenerator_snd_zero y] at hD hμ
  obtain rfl := trefoil_eq_zero_of_isDomainBetween hD (by simpa using hz 0) (by simpa using hz 1)
  simp at hμ

/-- **The hat knot Floer differential of the trefoil diagram vanishes.** So `HFK̂` of this
diagram has the three generators `x₀`, `x₂`, `x₁`, in the relative Alexander gradings `1`, `0`,
`-1`, normalized by `A(x₂) = 0`. -/
@[simp]
theorem hatDifferential_trefoil (χ : Fin 3 → ℤ) : (trefoil ![1, 2]).hatDifferential χ = 0 :=
  hatDifferential_eq_zero_iff.mpr fun x y =>
    hatCoefficient_eq_zero_of_hatDomains_eq_empty (hatDomains_trefoil χ x y)

/-! ### Integer knot gradings and the graded Euler characteristic -/

section KnotEulerCharacteristic

open LaurentPolynomial

/-- Every two generators of `trefoil b` are joined by a domain. -/
theorem exists_isDomainBetween_trefoil (x y : (trefoil b).Generator) :
    ∃ D, (trefoil b).IsDomainBetween x y D := by
  obtain ⟨a, rfl⟩ := (trefoilGeneratorEquiv b).surjective x
  obtain ⟨c, rfl⟩ := (trefoilGeneratorEquiv b).surjective y
  simp_rw [trefoilGeneratorEquiv_apply, isDomainBetween_trefoil_iff]
  exact ⟨![0, (if a = 1 then 1 else 0) - (if c = 1 then 1 else 0),
    (if a = 0 then 1 else 0) - (if c = 0 then 1 else 0)], by simp⟩

/-- The Maslov grading of the generators `x₀`, `x₁`, `x₂` of the doubly pointed trefoil
diagram: `0`, `-2` and `-1`. -/
def trefoilMaslovGrading (x : (trefoil ![1, 2]).Generator) : ℤ :=
  ![0, -2, -1] ((trefoil ![1, 2]).point x 0)

/-- The Alexander grading of the generators `x₀`, `x₁`, `x₂` of the doubly pointed trefoil
diagram: `1`, `-1` and `0`. -/
def trefoilAlexanderGrading (x : (trefoil ![1, 2]).Generator) : ℤ :=
  ![1, -1, 0] ((trefoil ![1, 2]).point x 0)

@[simp]
theorem trefoilMaslovGrading_trefoilGenerator (a : Fin 3) :
    trefoilMaslovGrading (trefoilGenerator _ a) = ![0, -2, -1] a := by
  simp [trefoilMaslovGrading]

@[simp]
theorem trefoilAlexanderGrading_trefoilGenerator (a : Fin 3) :
    trefoilAlexanderGrading (trefoilGenerator _ a) = ![1, -1, 0] a := by
  simp [trefoilAlexanderGrading]

/-- **The integer gradings of the trefoil diagram.** With `w` in `B_w` and `z` in `B_z`, the
Maslov gradings `0`, `-2`, `-1` and the Alexander gradings `1`, `-1`, `0` of `x₀`, `x₁`, `x₂`
form a knot grading. In the order `x₀`, `x₂`, `x₁` of decreasing Alexander grading, the Maslov
grading drops by one at each step. -/
theorem isKnotGrading_trefoil :
    (trefoil ![1, 2]).IsKnotGrading 1 0 1 trefoilMaslovGrading trefoilAlexanderGrading where
  maslov_sub_maslov {x y D} hD := by
    obtain ⟨a, rfl⟩ := (trefoilGeneratorEquiv _).surjective x
    obtain ⟨c, rfl⟩ := (trefoilGeneratorEquiv _).surjective y
    rw [trefoilGeneratorEquiv_apply, trefoilGeneratorEquiv_apply] at hD ⊢
    obtain ⟨h0, h1⟩ := (isDomainBetween_trefoil_iff a c D).mp hD
    qify at h0 h1
    fin_cases a <;> fin_cases c <;>
      norm_num +decide [trefoilMaslovGrading, maslovIndex_apply, eulerMeasure_apply,
        generatorPointMeasure_apply, pointMeasure_apply, Fin.sum_univ_three,
        neg_one_fin_three] at h0 h1 ⊢ <;>
      linarith
  alexander_sub_alexander {x y D} hD := by
    obtain ⟨a, rfl⟩ := (trefoilGeneratorEquiv _).surjective x
    obtain ⟨c, rfl⟩ := (trefoilGeneratorEquiv _).surjective y
    rw [trefoilGeneratorEquiv_apply, trefoilGeneratorEquiv_apply] at hD ⊢
    obtain ⟨h0, h1⟩ := (isDomainBetween_trefoil_iff a c D).mp hD
    fin_cases a <;> fin_cases c <;> simp at h0 h1 ⊢ <;> omega

/-- **The graded Euler characteristic of the trefoil diagram is `T - 1 + T⁻¹`**, the symmetrized
Alexander polynomial of the trefoil. -/
theorem gradedEulerChar_trefoil :
    (trefoil ![1, 2]).gradedEulerChar trefoilMaslovGrading trefoilAlexanderGrading =
      T 1 - 1 + T (-1) := by
  rw [gradedEulerChar_def, ← (trefoilGeneratorEquiv _).sum_comp, Fin.sum_univ_three]
  simp [Int.negOnePow_def]
  abel

/-- **The symmetric Alexander grading of the trefoil diagram.** Every knot grading of the trefoil
diagram whose graded Euler characteristic is symmetric under `T ↦ T⁻¹` has the Alexander gradings
`1`, `-1`, `0` of `x₀`, `x₁`, `x₂`. -/
theorem eq_trefoilAlexanderGrading_of_isKnotGrading {M A : (trefoil ![1, 2]).Generator → ℤ}
    (h : (trefoil ![1, 2]).IsKnotGrading 1 0 1 M A)
    (hs : LaurentPolynomial.invert ((trefoil ![1, 2]).gradedEulerChar M A) =
      (trefoil ![1, 2]).gradedEulerChar M A) :
    A = trefoilAlexanderGrading := by
  refine isKnotGrading_trefoil.alexander_eq_of_invert_gradedEulerChar_eq h
    exists_isDomainBetween_trefoil ?_ ?_ hs
  · rw [gradedEulerChar_trefoil]
    intro h
    have h0 := congrArg (fun p : ℤ[T;T⁻¹] => p.coeff 0) h
    simp at h0
  · rw [gradedEulerChar_trefoil]
    simp only [map_add, map_sub, invert_T, map_one, neg_neg]
    abel

end KnotEulerCharacteristic

/-! ### The Alexander filtration -/

/-- Moving the basepoints of `trefoil b` gives `trefoil b'`. -/
@[simp]
theorem withBasepoints_trefoil {B' : Type*} (b' : B' → Fin 3) :
    (trefoil b).withBasepoints b' = trefoil b' :=
  (rfl)

/-- **The Alexander filtration of the trefoil diagram.** The Alexander gradings `1`, `-1`, `0` of
`x₀`, `x₁`, `x₂`, relative to `x₂`, form an Alexander function for `w`: every domain avoiding `w`
lowers them by its multiplicity at `z`. So they filter the hat complex of the diagram pointed at
`w` (`IsAlexanderFunction.hatDifferential_withBasepoints_mem_supported_setOf_le`). -/
theorem isAlexanderFunction_trefoil :
    (trefoil ![1, 2]).IsAlexanderFunction (fun _ : Unit => 0) trefoilAlexanderGrading := by
  have hx : ∀ x, ∃ E, (trefoil ![1, 2]).IsDomainBetween x (trefoilGenerator _ 2) E := by
    intro x
    rw [← trefoilGenerator_snd_zero x]
    generalize (x.2 0 : Fin 3) = a
    fin_cases a
    exacts [⟨_, isDomainBetween_trefoil_single_two⟩, ⟨_, isDomainBetween_trefoil_single_one⟩,
      ⟨_, isDomainBetween_zero _⟩]
  convert isAlexanderFunction_relativeAlexanderGrading (fun b => by fin_cases b <;> simp)
    (periodicAlexanderValues_trefoil 0 1) hx using 1
  funext x
  rw [← trefoilGenerator_snd_zero x]
  generalize (x.2 0 : Fin 3) = a
  fin_cases a <;> simp [relativeAlexanderGrading_self]

/-- The bigon `B_z`, which avoids `w`, is counted by the hat differential of the diagram pointed
at `w` alone, from `x₀` to `x₂`. It lowers the Alexander grading by one, so the hat differential
of the doubly pointed diagram, which vanishes
(`TauCeti.HeegaardRegionSystem.hatDifferential_trefoil`), does not count it. -/
theorem single_two_mem_hatDomains_trefoil :
    Pi.single 2 1 ∈ (trefoil fun _ : Unit => 1).hatDomains 1 (trefoilGenerator _ 0)
      (trefoilGenerator _ 2) :=
  mem_hatDomains_iff.mpr ⟨isDomainBetween_trefoil_single_two, fun _ => by simp,
    Pi.single_nonneg.mpr zero_le_one, maslovIndex_trefoil_single_two⟩

/-- In the diagram pointed at `w` alone, the hat differential has coefficient one from `x₀` to
`x₂`, coming from the bigon `B_z`. -/
theorem hatCoefficient_trefoil_zero_two :
    (trefoil fun _ : Unit => 1).hatCoefficient 1 (trefoilGenerator _ 0) (trefoilGenerator _ 2) =
      1 :=
  (hatCoefficient_eq_one_iff_of_periodicDomains_eq_bot periodicDomains_trefoil).mpr
    ⟨_, single_two_mem_hatDomains_trefoil⟩

end HeegaardRegionSystem

end TauCeti

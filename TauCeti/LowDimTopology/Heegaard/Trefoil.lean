/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.AlexanderGrading
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.FinCases

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
  and `0` with `n_z - n_w = 1`, and is not counted.

All gradings here are relative: the values `1`, `0`, `-1` are determined only up to an overall
shift, and `A(x₂) = 0` is a choice. The canonical absolute Alexander grading of knot Floer
homology, fixed by the symmetry of `HFK̂` (equivalently, by the Seifert class), is not formalized
here; with it, these are the gradings of the knot Floer homology of the trefoil, whose graded
Euler characteristic is its Alexander polynomial `t - 1 + t⁻¹`.

## Main definitions

* `TauCeti.HeegaardRegionSystem.trefoil`: the diagram, with its basepoints in given regions.
* `TauCeti.HeegaardRegionSystem.trefoilGenerator`: its three generators.

## Main results

* `TauCeti.HeegaardRegionSystem.isDomainBetween_trefoil_single_two` and
  `TauCeti.HeegaardRegionSystem.isDomainBetween_trefoil_single_one`: the bigons `B_z` and `B_w`
  are domains from `x₀` to `x₂` and from `x₁` to `x₂`.
* `TauCeti.HeegaardRegionSystem.isDomainBetween_trefoil_self_iff`: the domains from a generator to
  itself are the multiples of the whole surface.
* `TauCeti.HeegaardRegionSystem.periodicDomains_trefoil` and
  `TauCeti.HeegaardRegionSystem.weaklyAdmissible_trefoil`: once a basepoint is placed, the only
  periodic domain is zero, so the diagram is weakly admissible.
* `TauCeti.HeegaardRegionSystem.periodicAlexanderValues_trefoil`: the Alexander grading is an
  integer.
* `TauCeti.HeegaardRegionSystem.relativeAlexanderGrading_trefoil_zero_two` and
  `TauCeti.HeegaardRegionSystem.relativeAlexanderGrading_trefoil_one_two`: the relative Alexander
  gradings.
* `TauCeti.HeegaardRegionSystem.relativeGrading_trefoil_zero_two` and
  `TauCeti.HeegaardRegionSystem.relativeGrading_trefoil_one_two`: the relative Maslov gradings.
* `TauCeti.HeegaardRegionSystem.hatDomains_trefoil` and
  `TauCeti.HeegaardRegionSystem.hatDifferential_trefoil`: the hat knot Floer differential
  vanishes.

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

/-- The rotation of `Fin 3` is one cycle on every fibre of a map to `Fin 1`. -/
private theorem isCycleOn_finRotate_three_fiber (i : Fin 1) :
    (finRotate 3).IsCycleOn {_p : Fin 3 | (0 : Fin 1) = i} := by
  convert (isCycle_finRotate (n := 1)).isCycleOn using 1
  ext p
  simp only [Set.mem_ofPred_eq, Subsingleton.elim i 0, true_iff]
  revert p
  decide

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
  alphaNext_isCycleOn _ := isCycleOn_finRotate_three_fiber _
  betaNext := finRotate 3
  betaNext_isCycleOn _ := isCycleOn_finRotate_three_fiber _
  alphaLeft j := if j = 1 then 1 else 0
  alphaRight j := if j = 2 then 2 else 0
  betaLeft j := if j = 2 then 2 else 0
  betaRight j := if j = 1 then 1 else 0
  regionNonempty := inferInstance
  crossingCompatible := by decide
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
  fin_cases q <;> simp [neg_one_fin_three]; ring

/-- The value of the `β`-boundary cycle condition of `trefoil b` at the three points. -/
private theorem betaArcBoundary_betaBoundary_trefoil (D : Fin 3 → ℤ) (q : Fin 3) :
    (trefoil b).betaArcBoundary ((trefoil b).betaBoundary D) q =
      ![D 2 - D 0, D 1 - D 0, 2 * D 0 - D 1 - D 2] q := by
  fin_cases q <;> simp [neg_one_fin_three]; ring

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

/-- The periodic Alexander values of the doubly pointed diagram vanish, so its Alexander grading
is an integer: the whole surface has the same multiplicity at `w` and at `z`. -/
@[simp]
theorem periodicAlexanderValues_trefoil : (trefoil ![1, 2]).periodicAlexanderValues 0 1 = ⊥ := by
  refine periodicAlexanderValues_eq_bot_iff.mpr fun E hα hβ => ?_
  have h := trefoil_eq_smul_one_of_arcBoundary_eq_zero hα hβ
  rw [h]
  simp

/-- The generator `x₀` lies one Alexander grading above `x₂`, computed from the bigon `B_z`, which
contains `z` and not `w`. -/
theorem relativeAlexanderGrading_trefoil_zero_two :
    (trefoil ![1, 2]).relativeAlexanderGrading 0 1 (trefoilGenerator _ 0)
      (trefoilGenerator _ 2) = 1 := by
  rw [isDomainBetween_trefoil_single_two.relativeAlexanderGrading_eq
    periodicAlexanderValues_trefoil]
  decide

/-- The generator `x₁` lies one Alexander grading below `x₂`, computed from the bigon `B_w`, which
contains `w` and not `z`. -/
theorem relativeAlexanderGrading_trefoil_one_two :
    (trefoil ![1, 2]).relativeAlexanderGrading 0 1 (trefoilGenerator _ 1)
      (trefoilGenerator _ 2) = -1 := by
  rw [isDomainBetween_trefoil_single_one.relativeAlexanderGrading_eq
    periodicAlexanderValues_trefoil]
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
  simp [maslovIndex_apply, eulerMeasure_apply, generatorPointMeasure_apply, pointMeasure_apply,
    Pi.single_apply, neg_one_fin_three]
  norm_num

/-- The bigon `B_w`, a disk with two corners, has Maslov index one as a domain from `x₁` to
`x₂`. -/
theorem maslovIndex_trefoil_single_one :
    (trefoil b).maslovIndex 1 (trefoilGenerator b 1) (trefoilGenerator b 2) (Pi.single 1 1) =
      1 := by
  simp [maslovIndex_apply, eulerMeasure_apply, generatorPointMeasure_apply, pointMeasure_apply,
    Pi.single_apply]
  norm_num

/-- In the diagram `(Σ, α, β, w)` of `S³`, the generator `x₀` lies one Maslov grading above `x₂`,
computed from the bigon `B_z`, which avoids `w`. -/
theorem relativeGrading_trefoil_zero_two :
    (trefoil fun _ : Unit => 1).relativeGrading 1 () (trefoilGenerator _ 0)
      (trefoilGenerator _ 2) = 1 := by
  rw [isDomainBetween_trefoil_single_two.relativeGrading_eq () (by decide)
    (by simp [periodicDomains_trefoil]), maslovIndex_trefoil_single_two]
  simp

/-- In the diagram `(Σ, α, β, w)` of `S³`, the generator `x₁` lies one Maslov grading below `x₂`,
computed from the bigon `B_w`, which contains `w`. -/
theorem relativeGrading_trefoil_one_two :
    (trefoil fun _ : Unit => 1).relativeGrading 1 () (trefoilGenerator _ 1)
      (trefoilGenerator _ 2) = -1 := by
  rw [isDomainBetween_trefoil_single_one.relativeGrading_eq () (by decide)
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

end HeegaardRegionSystem

end TauCeti

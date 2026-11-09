/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.AlexanderGrading
public import TauCeti.LowDimTopology.Heegaard.RelativeGrading
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.FinCases

/-!
# The genus-one doubly pointed Heegaard diagram of the trefoil

On the torus `ℝ² / ℤ²` let `α` be the circle `y = 0`, oriented by increasing `x`, and let `β` be
a closed curve meeting `α` transversally in the three points `a = (0, 0)`, `b = (1/3, 0)` and
`c = (2/3, 0)`: from `a` it dips below `α` and comes back up through `b`, then rises above `α`
and comes back down through `c`, and from `c` it runs once around the torus downwards, returning
to `a` from above. The complement of `α ∪ β` has three regions: the bigon `B₁` below `α` between
`a` and `b`, the bigon `B₂` above `α` between `b` and `c`, and an octagon `O`, a disk with eight
corners making up the rest of the torus. The class of `β` is `(1, -1)`, which meets that of `α`
once, so `(T², α, β)` is a Heegaard diagram of `S³`. With the basepoint `w` in `B₁` and the
second basepoint `z` in `B₂` it is a doubly pointed diagram of the trefoil.

In `TauCeti.HeegaardRegionSystem.trefoil` the points `a`, `b`, `c` are `0, 1, 2 : Fin 3`, the
regions `O`, `B₁`, `B₂` are `0, 1, 2 : Fin 3`, and the basepoint lies in `B₁`. The bigon `B₁` is
a domain from `b` to `a` and the bigon `B₂` is a domain from `b` to `c`. The only periodic domain
is zero, so the relative Alexander grading (with `z` in `B₂`) and the relative Maslov grading are
integer valued. From the two bigons, `A(a) - A(b) = A(b) - A(c) = 1` and the Maslov gradings
also drop by one from `a` to `b` and from `b` to `c`. These are the gradings `1, 0, -1` and
`0, -1, -2` of the three generators of the knot Floer homology `HFK̂` of the trefoil, whose graded
Euler characteristic is its Alexander polynomial `t - 1 + t⁻¹`. The absolute normalizations (the
symmetry of `HFK̂` and `HF̂(S³)` lying in degree `0`) are not formalized here.

The domains counted by the combinatorial hat differential of `CF̂(S³)` from `b` to `c` and from
`a` to `b` are the bigon `B₂` and the domain `O + B₂ = Σ - B₁`, both of Maslov index one. Both
avoid `w` and contain `z`, so they lower the Alexander grading by one and are not counted by the
differential of `HFK̂`; the second is the Whitney disk from the generator of Alexander grading `1`
to that of grading `0` with `n_z - n_w = 1`. The octagon is neither a bigon nor a square, so the
diagram is not nice and the combinatorial count of `O + B₂` need not be its holomorphic count.

## Main definitions

* `TauCeti.HeegaardRegionSystem.trefoil`: the diagram, with its basepoint `w` in `B₁`.
* `TauCeti.HeegaardRegionSystem.trefoilGenerator`: its three generators.

## Main results

* `TauCeti.HeegaardRegionSystem.isDomainBetween_trefoil_one_zero` and
  `TauCeti.HeegaardRegionSystem.isDomainBetween_trefoil_one_two`: the bigons `B₁` and `B₂` are
  domains from `b` to `a` and from `b` to `c`.
* `TauCeti.HeegaardRegionSystem.periodicDomains_trefoil`: the only periodic domain is zero.
* `TauCeti.HeegaardRegionSystem.relativeAlexanderGrading_trefoil_zero_one` and
  `TauCeti.HeegaardRegionSystem.relativeAlexanderGrading_trefoil_one_two`: the Alexander grading
  drops by one from `a` to `b` and from `b` to `c`.
* `TauCeti.HeegaardRegionSystem.relativeGrading_trefoil_zero_one` and
  `TauCeti.HeegaardRegionSystem.relativeGrading_trefoil_one_two`: so does the Maslov grading.
* `TauCeti.HeegaardRegionSystem.hatDomains_trefoil_one_two` and
  `TauCeti.HeegaardRegionSystem.hatDomains_trefoil_zero_one`: the hat differential counts the
  bigon `B₂` from `b` to `c` and the domain `O + B₂` from `a` to `b`, both containing `z`.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and knot invariants*, Adv. Math. **186** (2004),
  [arXiv:math/0209056](https://arxiv.org/abs/math/0209056), §2 (doubly pointed diagrams) and the
  computation of `HFK̂` for the trefoil from a genus-one diagram.
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

/-- The rotation of the three intersection points of the trefoil diagram is one cycle on the
unique curve fibre. -/
private theorem isCycleOn_finRotate_three (i : Fin 1) :
    (finRotate 3).IsCycleOn {_p : Fin 3 | (0 : Fin 1) = i} := by
  convert (isCycle_finRotate (n := 1)).isCycleOn using 1
  ext p
  simp only [Set.mem_ofPred_eq, Subsingleton.elim (0 : Fin 1) i, ← Equiv.Perm.mem_support,
    support_finRotate, Finset.mem_univ]

/-- The genus-one doubly pointed Heegaard diagram of the trefoil, with its basepoint `w` in the
bigon `B₁`. The intersection points `0`, `1`, `2` are `a`, `b`, `c` in order along both curves,
and the regions `0`, `1`, `2` are the octagon and the two bigons `B₁` and `B₂`; the second
basepoint `z` of the knot lies in `B₂`. -/
def trefoil : HeegaardRegionSystem 1 (Fin 3) (Fin 3) Unit where
  pointFintype := inferInstance
  alpha _ := 0
  beta _ := 0
  alphaNext := finRotate 3
  alphaNext_isCycleOn := isCycleOn_finRotate_three
  betaNext := finRotate 3
  betaNext_isCycleOn := isCycleOn_finRotate_three
  alphaLeft := ![0, 2, 0]
  alphaRight := ![1, 0, 0]
  betaLeft := ![1, 0, 0]
  betaRight := ![0, 2, 0]
  regionNonempty := inferInstance
  crossingCompatible := by
    intro p
    fin_cases p
    · right
      decide
    · left
      decide
    · right
      decide
  regionCovered := by
    intro s
    left
    fin_cases s
    · exact ⟨0, Or.inl rfl⟩
    · exact ⟨0, Or.inr (Or.inl rfl)⟩
    · exact ⟨1, Or.inl rfl⟩
  basepoint _ := 1

/-- All three intersection points lie on the unique `α`-curve. -/
@[simp]
theorem trefoil_alpha (p : Fin 3) : trefoil.alpha p = 0 :=
  (rfl)

/-- All three intersection points lie on the unique `β`-curve. -/
@[simp]
theorem trefoil_beta (p : Fin 3) : trefoil.beta p = 0 :=
  (rfl)

/-- The successor on the `α`-curve is `a ↦ b ↦ c ↦ a`. -/
@[simp]
theorem trefoil_alphaNext (p : Fin 3) : trefoil.alphaNext p = ![1, 2, 0] p := by
  fin_cases p <;> rfl

/-- The successor on the `β`-curve is `a ↦ b ↦ c ↦ a`. -/
@[simp]
theorem trefoil_betaNext (p : Fin 3) : trefoil.betaNext p = ![1, 2, 0] p := by
  fin_cases p <;> rfl

/-- The predecessor on the `α`-curve is `a ↦ c ↦ b ↦ a`. -/
@[simp]
theorem trefoil_alphaNext_symm (p : Fin 3) : trefoil.alphaNext.symm p = ![2, 0, 1] p := by
  fin_cases p <;> rfl

/-- The predecessor on the `β`-curve is `a ↦ c ↦ b ↦ a`. -/
@[simp]
theorem trefoil_betaNext_symm (p : Fin 3) : trefoil.betaNext.symm p = ![2, 0, 1] p := by
  fin_cases p <;> rfl

/-- The regions to the left of the three `α`-arcs. -/
@[simp]
theorem trefoil_alphaLeft (p : Fin 3) : trefoil.alphaLeft p = ![0, 2, 0] p :=
  (rfl)

/-- The regions to the right of the three `α`-arcs. -/
@[simp]
theorem trefoil_alphaRight (p : Fin 3) : trefoil.alphaRight p = ![1, 0, 0] p :=
  (rfl)

/-- The regions to the left of the three `β`-arcs. -/
@[simp]
theorem trefoil_betaLeft (p : Fin 3) : trefoil.betaLeft p = ![1, 0, 0] p :=
  (rfl)

/-- The regions to the right of the three `β`-arcs. -/
@[simp]
theorem trefoil_betaRight (p : Fin 3) : trefoil.betaRight p = ![0, 2, 0] p :=
  (rfl)

/-- The basepoint `w` of the trefoil diagram lies in the bigon `B₁`. -/
@[simp]
theorem trefoil_basepoint (w : Unit) : trefoil.basepoint w = 1 :=
  (rfl)

/-- The generator of the trefoil diagram at the intersection point `a`. -/
def trefoilGenerator (a : Fin 3) : trefoil.Generator :=
  trefoil.generatorOf 1 (fun _ => a) (fun _ => Subsingleton.elim _ _)
    (fun _ => Subsingleton.elim _ _)

/-- The unique point chosen by `trefoilGenerator a` is `a`. -/
@[simp 1100]
theorem trefoilGenerator_point (a : Fin 3) (i : Fin 1) :
    trefoil.point (trefoilGenerator a) i = a := by
  simp [trefoilGenerator]

/-- The generator chain of `trefoilGenerator a` is supported at `a`. -/
theorem generatorChain_trefoilGenerator (a q : Fin 3) :
    trefoil.generatorChain (trefoilGenerator a) q = if a = q then 1 else 0 := by
  rw [HeegaardIntersectionSystem.generatorChain_apply]
  simp [trefoilGenerator]

/-- The value of the `α`-boundary cycle condition of the trefoil diagram on the three points. -/
private theorem alphaArcBoundary_alphaBoundary_trefoil (D : Fin 3 → ℤ) (q : Fin 3) :
    trefoil.alphaArcBoundary (trefoil.alphaBoundary D) q =
      ![(D 0 - D 0) - (D 0 - D 1), (D 0 - D 1) - (D 2 - D 0), (D 2 - D 0) - (D 0 - D 0)] q := by
  fin_cases q <;> simp [trefoil]

/-- The value of the `β`-boundary cycle condition of the trefoil diagram on the three points. -/
private theorem betaArcBoundary_betaBoundary_trefoil (D : Fin 3 → ℤ) (q : Fin 3) :
    trefoil.betaArcBoundary (trefoil.betaBoundary D) q =
      ![(D 0 - D 0) - (D 1 - D 0), (D 1 - D 0) - (D 0 - D 2), (D 0 - D 2) - (D 0 - D 0)] q := by
  fin_cases q <;> simp [trefoil]

/-- The only periodic domain of the trefoil diagram is zero: its boundary along `α` is a multiple
of `α` only when all three regions have the same multiplicity, which is then the multiplicity
`0` at the basepoint. -/
theorem periodicDomains_trefoil : trefoil.periodicDomains = ⊥ := by
  refine (AddSubgroup.eq_bot_iff_forall _).mpr fun D hD => ?_
  obtain ⟨hw, hα, -⟩ := mem_periodicDomains_iff.mp hD
  have h0 := congr_fun hα 0
  have h1 := congr_fun hα 1
  rw [alphaArcBoundary_alphaBoundary_trefoil] at h0 h1
  have h := hw ()
  simp only [trefoil_basepoint] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
  funext i
  fin_cases i <;> simp <;> omega

/-- Every periodic domain of the trefoil diagram vanishes, in particular at the region `z`. -/
theorem apply_eq_zero_of_mem_periodicDomains_trefoil (z : Fin 3) {P : Fin 3 → ℤ}
    (hP : P ∈ trefoil.periodicDomains) : P z = 0 := by
  rw [periodicDomains_trefoil, AddSubgroup.mem_bot] at hP
  simp [hP]

/-- The bigon `B₁` is a domain from `b` to `a`. -/
theorem isDomainBetween_trefoil_one_zero :
    trefoil.IsDomainBetween (trefoilGenerator 1) (trefoilGenerator 0) (Pi.single 1 1) := by
  refine isDomainBetween_iff.mpr ⟨funext fun q => ?_, funext fun q => ?_⟩ <;>
    simp only [alphaArcBoundary_alphaBoundary_trefoil, betaArcBoundary_betaBoundary_trefoil,
      Pi.sub_apply, generatorChain_trefoilGenerator] <;>
    fin_cases q <;> simp

/-- The bigon `B₂` is a domain from `b` to `c`. -/
theorem isDomainBetween_trefoil_one_two :
    trefoil.IsDomainBetween (trefoilGenerator 1) (trefoilGenerator 2) (Pi.single 2 1) := by
  refine isDomainBetween_iff.mpr ⟨funext fun q => ?_, funext fun q => ?_⟩ <;>
    simp only [alphaArcBoundary_alphaBoundary_trefoil, betaArcBoundary_betaBoundary_trefoil,
      Pi.sub_apply, generatorChain_trefoilGenerator] <;>
    fin_cases q <;> simp

/-- The domain `O + B₂ = Σ - B₁` is a domain from `a` to `b`. -/
theorem isDomainBetween_trefoil_zero_one :
    trefoil.IsDomainBetween (trefoilGenerator 0) (trefoilGenerator 1) ![1, 0, 1] := by
  refine isDomainBetween_iff.mpr ⟨funext fun q => ?_, funext fun q => ?_⟩ <;>
    simp only [alphaArcBoundary_alphaBoundary_trefoil, betaArcBoundary_betaBoundary_trefoil,
      Pi.sub_apply, generatorChain_trefoilGenerator] <;>
    fin_cases q <;> simp

/-- With the second basepoint `z` in `B₂`, the Alexander grading drops by one from `a` to `b`:
`-B₁` is a domain from `a` to `b` with `n_z - n_w = 0 - (-1) = 1`. -/
theorem relativeAlexanderGrading_trefoil_zero_one :
    trefoil.relativeAlexanderGrading () 2 (trefoilGenerator 0) (trefoilGenerator 1) = 1 := by
  rw [isDomainBetween_trefoil_one_zero.neg.relativeAlexanderGrading_eq ()
    fun _ => apply_eq_zero_of_mem_periodicDomains_trefoil 2]
  simp

/-- With the second basepoint `z` in `B₂`, the Alexander grading drops by one from `b` to `c`:
`B₂` is a domain from `b` to `c` with `n_z - n_w = 1 - 0 = 1`. -/
theorem relativeAlexanderGrading_trefoil_one_two :
    trefoil.relativeAlexanderGrading () 2 (trefoilGenerator 1) (trefoilGenerator 2) = 1 := by
  rw [isDomainBetween_trefoil_one_two.relativeAlexanderGrading_eq ()
    fun _ => apply_eq_zero_of_mem_periodicDomains_trefoil 2]
  simp

/-- The octagon has eight corners and each bigon has two. -/
@[simp]
theorem cornerCount_trefoil (s : Fin 3) : trefoil.cornerCount s = ![8, 2, 2] s := by
  revert s
  simp only [cornerCount_eq_card, cornerRegion_eq]
  decide

/-- The bigon `B₁`, a disk with two corners, has Maslov index one. -/
theorem maslovIndex_trefoil_single_one :
    trefoil.maslovIndex ![1, 1, 1] (trefoilGenerator 1) (trefoilGenerator 0) (Pi.single 1 1) =
      1 := by
  simp [Pi.single_apply]
  norm_num

/-- The bigon `B₂`, a disk with two corners, has Maslov index one. -/
theorem maslovIndex_trefoil_single_two :
    trefoil.maslovIndex ![1, 1, 1] (trefoilGenerator 1) (trefoilGenerator 2) (Pi.single 2 1) =
      1 := by
  simp [Pi.single_apply]
  norm_num

/-- The domain `O + B₂` from `a` to `b` has Maslov index one. -/
theorem maslovIndex_trefoil_octagon_add_bigon :
    trefoil.maslovIndex ![1, 1, 1] (trefoilGenerator 0) (trefoilGenerator 1) ![1, 0, 1] = 1 := by
  simp [Fin.sum_univ_three]
  norm_num

/-- The regions of the trefoil diagram, all disks, assemble to a torus. -/
private theorem sum_eulerChar_trefoil :
    ∑ r, (![1, 1, 1] : Fin 3 → ℤ) r - Fintype.card (Fin 3) = 2 - 2 * ((1 : ℕ) : ℤ) := by
  decide

/-- The Maslov grading drops by one from `a` to `b`: `-B₁` is a domain from `a` to `b` of Maslov
index `-1` with `n_w = -1`, so `μ - 2 n_w = 1`. -/
theorem relativeGrading_trefoil_zero_one :
    trefoil.relativeGrading ![1, 1, 1] () (trefoilGenerator 0) (trefoilGenerator 1) = 1 := by
  rw [isDomainBetween_trefoil_one_zero.neg.relativeGrading_eq () sum_eulerChar_trefoil
    fun P hP => by simp [(AddSubgroup.mem_bot).mp (periodicDomains_trefoil ▸ hP)],
    maslovIndex_neg, maslovIndex_trefoil_single_one]
  simp
  norm_num

/-- The Maslov grading drops by one from `b` to `c`: `B₂` is a domain from `b` to `c` of Maslov
index one avoiding the basepoint `w`. -/
theorem relativeGrading_trefoil_one_two :
    trefoil.relativeGrading ![1, 1, 1] () (trefoilGenerator 1) (trefoilGenerator 2) = 1 := by
  rw [isDomainBetween_trefoil_one_two.relativeGrading_eq () sum_eulerChar_trefoil
    fun P hP => by simp [(AddSubgroup.mem_bot).mp (periodicDomains_trefoil ▸ hP)],
    maslovIndex_trefoil_single_two]
  simp

/-- The only domain counted by the hat differential of `CF̂(S³)` from `b` to `c` is the bigon
`B₂`. It contains the second basepoint `z`, so it lowers the Alexander grading by one
(`TauCeti.HeegaardRegionSystem.relativeAlexanderGrading_trefoil_one_two`) and is not counted by
the differential of `HFK̂`. -/
theorem hatDomains_trefoil_one_two :
    trefoil.hatDomains ![1, 1, 1] (trefoilGenerator 1) (trefoilGenerator 2) = {Pi.single 2 1} := by
  ext D
  rw [mem_hatDomains_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hD, hw, -, -⟩
    -- `D - B₂` is periodic, hence zero.
    have hP := isDomainBetween_trefoil_one_two.sub_mem_periodicDomains_iff.mpr
      ⟨hD, fun w => by simpa using hw w⟩
    rwa [periodicDomains_trefoil, AddSubgroup.mem_bot, sub_eq_zero] at hP
  · rintro rfl
    exact ⟨isDomainBetween_trefoil_one_two, fun _ => by simp,
      Pi.single_nonneg.mpr zero_le_one, maslovIndex_trefoil_single_two⟩

/-- The only domain counted by the hat differential of `CF̂(S³)` from `a` to `b` is `O + B₂`. It
contains the second basepoint `z`, so it lowers the Alexander grading by one
(`TauCeti.HeegaardRegionSystem.relativeAlexanderGrading_trefoil_zero_one`) and is not counted by
the differential of `HFK̂`. -/
theorem hatDomains_trefoil_zero_one :
    trefoil.hatDomains ![1, 1, 1] (trefoilGenerator 0) (trefoilGenerator 1) = {![1, 0, 1]} := by
  ext D
  rw [mem_hatDomains_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hD, hw, -, -⟩
    -- `D - (O + B₂)` is periodic, hence zero.
    have hP := isDomainBetween_trefoil_zero_one.sub_mem_periodicDomains_iff.mpr
      ⟨hD, fun w => by simpa using hw w⟩
    rwa [periodicDomains_trefoil, AddSubgroup.mem_bot, sub_eq_zero] at hP
  · rintro rfl
    refine ⟨isDomainBetween_trefoil_zero_one, fun _ => by simp, fun i => ?_,
      maslovIndex_trefoil_octagon_add_bigon⟩
    fin_cases i <;> simp

end HeegaardRegionSystem

end TauCeti

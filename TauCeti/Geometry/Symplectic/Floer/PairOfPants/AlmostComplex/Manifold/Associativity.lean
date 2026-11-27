/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Manifold.MovingEnds
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Manifold.Plumbing
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Cayley.Segment

/-!
# The almost complex structures of the associativity family in a manifold

The associativity of the pair-of-pants product compares the two compositions `(x₁ x₂) x₃` and
`x₁ (x₂ x₃)` through a family of Floer data on four-punctured spheres. Its Hamiltonian
perturbations are `TauCeti.Floer.associativityPerturbation H Hout G G' L τ`: the datum of the
moving input ends along the associativity path, plus the neck data of the two compositions scaled
by `β(-τ)` and `β(τ - 1)`, where `β` is the smooth transition function. This file constructs the
matching domain-dependent almost complex structures on the tangent bundle of a manifold `M` with a
nondegenerate two-form `σ`, such as a closed symplectic manifold.

Fix a `σ`-compatible base structure `J₀`, `σ`-tame structures `J i t` on the three input ends and
`Jout t` on the output end, and `σ`-tame structures `G t` and `G' t` on the necks of `(x₁ x₂) x₃`
and of `x₁ (x₂ x₃)`. For a neck length `L ≥ 0`, a parameter `τ` and a domain point `w`, the
structure `TauCeti.SmoothTwoForm.Compatible.associativityAlmostComplex h₀ J hJ Jout hJout G hG G'
hG' L τ w` is

* for `τ ≤ 0`, the Cayley segment (`TauCeti.SmoothTwoForm.Compatible.cayleySegment`) at time `-τ`
  from the structure of the moving input ends to the plumbed structure of `(x₁ x₂) x₃`, which
  carries `G` on its neck (`TauCeti.SmoothTwoForm.Compatible.associativityAlmostComplex_of_lt_one`,
  and `TauCeti.SmoothTwoForm.Compatible.associativityAlmostComplex_of_nonpos` when the inputs are
  read off from the two pairs of pants);
* for `τ ≥ 1`, the Cayley segment at time `τ - 1` from the structure of the moving input ends to
  the plumbed structure of `x₁ (x₂ x₃)`, which carries `G'` on its neck
  (`TauCeti.SmoothTwoForm.Compatible.associativityAlmostComplex_of_pos`, and
  `TauCeti.SmoothTwoForm.Compatible.associativityAlmostComplex_of_one_le` when the inputs are read
  off from the two pairs of pants);
* for `τ ∈ [0, 1]`, the structure of the moving input ends along the associativity path
  (`TauCeti.SmoothTwoForm.Compatible.associativityAlmostComplex_of_mem_Icc`).

On the moving input ends the configuration at `τ ≤ 0` is that of `(x₁ x₂) x₃`, and the structure
there is the plumbed structure with the two glued ends switched off
(`TauCeti.SmoothTwoForm.Compatible.puncturedSphereAlmostComplex_associativity_of_nonpos`). So the
segments switch the neck structures on, as `β(-τ)` and `β(τ - 1)` switch on the neck
Hamiltonians of the perturbations. The results are:

* it is tamed by `σ`, and compatible with `σ` when all the end and neck structures are
  (`TauCeti.SmoothTwoForm.Compatible.tames_associativityAlmostComplex`,
  `TauCeti.SmoothTwoForm.Compatible.compatible_associativityAlmostComplex`);
* for `τ ≤ -1` it is the plumbed structure of `(x₁ x₂) x₃`
  (`TauCeti.SmoothTwoForm.Compatible.associativityAlmostComplex_of_le_neg_one`), and for `τ ≥ 2`
  that of `x₁ (x₂ x₃)` (`TauCeti.SmoothTwoForm.Compatible.associativityAlmostComplex_of_two_le`),
  just as the perturbations are the plumbed perturbations there
  (`TauCeti.Floer.associativityPerturbation_of_le_neg_one`,
  `TauCeti.Floer.associativityPerturbation_of_two_le`);
* for `L ≥ 2` and end structures of period one, it is `J i t` far out on the input end `i` and
  `Jout t` far out on the output end, in the end coordinates of the configuration at `τ`, for
  every `τ` (`TauCeti.SmoothTwoForm.Compatible.associativityAlmostComplex_cylindricalEndLift`,
  `TauCeti.SmoothTwoForm.Compatible.associativityAlmostComplex_cylindricalEndLift_inf`), as the
  perturbations are `H_i(t) dt` and `Hout(t) dt` there;
* for end and neck structures of period one which are jointly `C^n` on `ℝ × M`, it is `C^n`
  jointly in the neck length `L > 4`, the parameter `τ`, the domain point and the point of `M`,
  away from the three moving input punctures
  (`TauCeti.SmoothTwoForm.Compatible.contMDiffAt_associativityAlmostComplex`), as the
  perturbations are (`TauCeti.Floer.contMDiffAt_associativityPerturbation`).

Together with the perturbations, these are the Floer data of the family of four-punctured spheres
whose two ends are the two compositions of pair-of-pants products, and whose moduli spaces give the
associativity homotopy.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the associativity of the pair-of-pants product.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Sections 9 and 10, on
  consistent Floer data over families of punctured surfaces.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  University Press, 2017, Proposition 2.5.13, on the Cayley chart of tame structures.
-/

public noncomputable section

open Bundle Set Real Manifold Topology Function
open scoped ContDiff
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture
open TauCeti.Floer (associativityLeftInserted associativityLeftReceiving associativityRightInserted
  associativityRightReceiving associativityLeftInserted_mem associativityLeftReceiving_mem
  associativityRightInserted_mem associativityRightReceiving_mem)

namespace TauCeti.SmoothTwoForm.Compatible

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {σ : SmoothTwoForm I M} {J₀ : SmoothAlmostComplexStructure I M}

/-! ### The two compositions -/

section Pieces

variable {J : Fin 3 → ℝ → SmoothAlmostComplexStructure I M}
  {Jout G G' : ℝ → SmoothAlmostComplexStructure I M}

omit [FiniteDimensional ℝ E] in
private theorem tames_leftInserted (hJ : ∀ i t, σ.Tames (J i t)) (hG : ∀ t, σ.Tames (G t)) :
    ∀ p t, σ.Tames (associativityLeftInserted J G p t) :=
  associativityLeftInserted_mem
    (S := {K : ℝ → SmoothAlmostComplexStructure I M | ∀ t, σ.Tames (K t)}) hJ hG

omit [FiniteDimensional ℝ E] in
private theorem tames_leftReceiving (hJ : ∀ i t, σ.Tames (J i t)) (hJout : ∀ t, σ.Tames (Jout t))
    (hG : ∀ t, σ.Tames (G t)) : ∀ p t, σ.Tames (associativityLeftReceiving J Jout G p t) :=
  associativityLeftReceiving_mem
    (S := {K : ℝ → SmoothAlmostComplexStructure I M | ∀ t, σ.Tames (K t)}) hJ hJout hG

omit [FiniteDimensional ℝ E] in
private theorem tames_rightInserted (hJ : ∀ i t, σ.Tames (J i t)) (hG' : ∀ t, σ.Tames (G' t)) :
    ∀ p t, σ.Tames (associativityRightInserted J G' p t) :=
  associativityRightInserted_mem
    (S := {K : ℝ → SmoothAlmostComplexStructure I M | ∀ t, σ.Tames (K t)}) hJ hG'

omit [FiniteDimensional ℝ E] in
private theorem tames_rightReceiving (hJ : ∀ i t, σ.Tames (J i t))
    (hJout : ∀ t, σ.Tames (Jout t)) (hG' : ∀ t, σ.Tames (G' t)) :
    ∀ p t, σ.Tames (associativityRightReceiving J Jout G' p t) :=
  associativityRightReceiving_mem
    (S := {K : ℝ → SmoothAlmostComplexStructure I M | ∀ t, σ.Tames (K t)}) hJ hJout hG'

end Pieces

/-! ### The family -/

variable (h₀ : σ.Compatible J₀) (J : Fin 3 → ℝ → SmoothAlmostComplexStructure I M)
  (hJ : ∀ i t, σ.Tames (J i t)) (Jout : ℝ → SmoothAlmostComplexStructure I M)
  (hJout : ∀ t, σ.Tames (Jout t)) (G : ℝ → SmoothAlmostComplexStructure I M)
  (hG : ∀ t, σ.Tames (G t)) (G' : ℝ → SmoothAlmostComplexStructure I M)
  (hG' : ∀ t, σ.Tames (G' t))

/-- The structure of the moving input ends along the associativity path of neck length `L ≥ 0`. -/
private def movingEnds {L : ℝ} (hL : 0 ≤ L) (τ : ℝ) (w : ℂ) : SmoothAlmostComplexStructure I M :=
  h₀.puncturedSphereAlmostComplex J hJ Jout hJout
    (Floer.associativityCenter (Real.exp (-(2 * π * L)) / 4) τ)
    (Floer.associativityScale (Real.exp (-(2 * π * L)) / 4) τ)
    (Floer.pairwise_mul_exp_add_le_norm_associativityCenter_sub_of_nonneg hL τ)
    (Floer.norm_associativityCenter_add_mul_exp_le_of_nonneg hL τ) w

/-- The plumbed structure of `(x₁ x₂) x₃`, with `G` on its neck. -/
private def leftPlumbed (L : ℝ) (w : ℂ) (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ zero.plumbingMap L 1) :
    SmoothAlmostComplexStructure I M :=
  h₀.plumbedAlmostComplex h₀ (associativityLeftInserted J G) (associativityLeftReceiving J Jout G)
    (tames_leftInserted hJ hG) (tames_leftReceiving hJ hJout hG) zero L w hw

/-- The plumbed structure of `x₁ (x₂ x₃)`, with `G'` on its neck. -/
private def rightPlumbed (L : ℝ) (w : ℂ) (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ one.plumbingMap L 1) :
    SmoothAlmostComplexStructure I M :=
  h₀.plumbedAlmostComplex h₀ (associativityRightInserted J G')
    (associativityRightReceiving J Jout G')
    (tames_rightInserted hJ hG') (tames_rightReceiving hJ hJout hG') one L w hw

private theorem tames_movingEnds {L : ℝ} (hL : 0 ≤ L) (τ : ℝ) (w : ℂ) :
    σ.Tames (movingEnds h₀ J hJ Jout hJout hL τ w) :=
  tames_puncturedSphereAlmostComplex h₀ _ _ _ _ _ _ w

private theorem tames_leftPlumbed (L : ℝ) (w : ℂ)
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ zero.plumbingMap L 1) :
    σ.Tames (leftPlumbed h₀ J hJ Jout hJout G hG L w hw) :=
  tames_plumbedAlmostComplex h₀ h₀ _ _ _ _ w hw

private theorem tames_rightPlumbed (L : ℝ) (w : ℂ)
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ one.plumbingMap L 1) :
    σ.Tames (rightPlumbed h₀ J hJ Jout hJout G' hG' L w hw) :=
  tames_plumbedAlmostComplex h₀ h₀ _ _ _ _ w hw

/-- **The almost complex structures of the associativity family.** For a neck length `L ≥ 0`, a
parameter `τ` and a domain point `w`: for `τ ≤ 0` the Cayley segment at time `-τ` from the
structure of the moving input ends along the associativity path to the plumbed structure of
`(x₁ x₂) x₃` with `G` on its neck; for `τ ≥ 1` the Cayley segment at time `τ - 1` to the plumbed
structure of `x₁ (x₂ x₃)` with `G'` on its neck; for `τ ∈ (0, 1)`, and at the punctures of the
plumbed spheres, the structure of the moving input ends. For `L < 0` it is `J₀`. -/
def associativityAlmostComplex (L τ : ℝ) (w : ℂ) : SmoothAlmostComplexStructure I M :=
  if hL : 0 ≤ L then
    if hl : τ ≤ 0 ∧ ((w ≠ 0 ∧ w ≠ 1) ∧ w ≠ zero.plumbingMap L 1) then
      h₀.cayleySegment (tames_movingEnds h₀ J hJ Jout hJout hL τ w)
        (tames_leftPlumbed h₀ J hJ Jout hJout G hG L w hl.2) (-τ)
    else if hr : 1 ≤ τ ∧ ((w ≠ 0 ∧ w ≠ 1) ∧ w ≠ one.plumbingMap L 1) then
      h₀.cayleySegment (tames_movingEnds h₀ J hJ Jout hJout hL τ w)
        (tames_rightPlumbed h₀ J hJ Jout hJout G' hG' L w hr.2) (τ - 1)
    else movingEnds h₀ J hJ Jout hJout hL τ w
  else J₀

variable {L τ : ℝ} {w : ℂ}

/-- Before the right switch, the family is the segment towards the left composition. -/
private theorem associativityAlmostComplex_eq_cayleySegment_leftPlumbed (hL : 0 ≤ L) (hτ : τ < 1)
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ zero.plumbingMap L 1) :
    h₀.associativityAlmostComplex J hJ Jout hJout G hG G' hG' L τ w =
      h₀.cayleySegment (tames_movingEnds h₀ J hJ Jout hJout hL τ w)
        (tames_leftPlumbed h₀ J hJ Jout hJout G hG L w hw) (-τ) := by
  rw [associativityAlmostComplex, dite_eq_left hL]
  by_cases hτ₀ : τ ≤ 0
  · rw [dite_eq_left ⟨hτ₀, hw⟩]
  · rw [dite_eq_right (fun h => hτ₀ h.1), dite_eq_right (fun h => (h.1.trans_lt hτ).false),
      cayleySegment_of_nonpos h₀ _ _ (by linarith)]

/-- After the left switch, the family is the segment towards the right composition. -/
private theorem associativityAlmostComplex_eq_cayleySegment_rightPlumbed (hL : 0 ≤ L) (hτ : 0 < τ)
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ one.plumbingMap L 1) :
    h₀.associativityAlmostComplex J hJ Jout hJout G hG G' hG' L τ w =
      h₀.cayleySegment (tames_movingEnds h₀ J hJ Jout hJout hL τ w)
        (tames_rightPlumbed h₀ J hJ Jout hJout G' hG' L w hw) (τ - 1) := by
  rw [associativityAlmostComplex, dite_eq_left hL,
    dite_eq_right (fun h => (h.1.trans_lt' hτ).false)]
  by_cases hτ₁ : 1 ≤ τ
  · rw [dite_eq_left ⟨hτ₁, hw⟩]
  · rw [dite_eq_right (fun h => hτ₁ h.1), cayleySegment_of_nonpos h₀ _ _ (by linarith)]

/-- **Before the right switch, the family is the segment towards `(x₁ x₂) x₃`.** For `L ≥ 0`,
`τ < 1` and a domain point `w` of the plumbed sphere of `(x₁ x₂) x₃`, the family is the Cayley
segment at time `-τ` from the structure of the moving input ends to the plumbed structure of
`(x₁ x₂) x₃`, whose end structures are `TauCeti.Floer.associativityLeftInserted J G` and
`TauCeti.Floer.associativityLeftReceiving J Jout G`. For `τ > 0` the time is negative, so this is
the structure of the moving input ends. -/
theorem associativityAlmostComplex_of_lt_one (hL : 0 ≤ L) (hτ : τ < 1)
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ zero.plumbingMap L 1) :
    h₀.associativityAlmostComplex J hJ Jout hJout G hG G' hG' L τ w =
      h₀.cayleySegment
        (tames_puncturedSphereAlmostComplex h₀ J hJ Jout hJout
          (Floer.pairwise_mul_exp_add_le_norm_associativityCenter_sub_of_nonneg hL τ)
          (Floer.norm_associativityCenter_add_mul_exp_le_of_nonneg hL τ) w)
        (tames_plumbedAlmostComplex h₀ h₀ (associativityLeftInserted J G)
          (associativityLeftReceiving J Jout G)
          (associativityLeftInserted_mem
            (S := {K : ℝ → SmoothAlmostComplexStructure I M | ∀ t, σ.Tames (K t)}) hJ hG)
          (associativityLeftReceiving_mem
            (S := {K : ℝ → SmoothAlmostComplexStructure I M | ∀ t, σ.Tames (K t)}) hJ hJout hG)
          w hw)
        (-τ) :=
  -- `movingEnds` and `leftPlumbed` abbreviate the two endpoints of the segment.
  associativityAlmostComplex_eq_cayleySegment_leftPlumbed h₀ J hJ Jout hJout G hG G' hG' hL hτ hw

/-- **After the left switch, the family is the segment towards `x₁ (x₂ x₃)`.** For `L ≥ 0`,
`τ > 0` and a domain point `w` of the plumbed sphere of `x₁ (x₂ x₃)`, the family is the Cayley
segment at time `τ - 1` from the structure of the moving input ends to the plumbed structure of
`x₁ (x₂ x₃)`, whose end structures are `TauCeti.Floer.associativityRightInserted J G'` and
`TauCeti.Floer.associativityRightReceiving J Jout G'`. For `τ < 1` the time is negative, so this
is the structure of the moving input ends. -/
theorem associativityAlmostComplex_of_pos (hL : 0 ≤ L) (hτ : 0 < τ)
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ one.plumbingMap L 1) :
    h₀.associativityAlmostComplex J hJ Jout hJout G hG G' hG' L τ w =
      h₀.cayleySegment
        (tames_puncturedSphereAlmostComplex h₀ J hJ Jout hJout
          (Floer.pairwise_mul_exp_add_le_norm_associativityCenter_sub_of_nonneg hL τ)
          (Floer.norm_associativityCenter_add_mul_exp_le_of_nonneg hL τ) w)
        (tames_plumbedAlmostComplex h₀ h₀ (associativityRightInserted J G')
          (associativityRightReceiving J Jout G')
          (associativityRightInserted_mem
            (S := {K : ℝ → SmoothAlmostComplexStructure I M | ∀ t, σ.Tames (K t)}) hJ hG')
          (associativityRightReceiving_mem
            (S := {K : ℝ → SmoothAlmostComplexStructure I M | ∀ t, σ.Tames (K t)}) hJ hJout hG')
          w hw)
        (τ - 1) :=
  -- `movingEnds` and `rightPlumbed` abbreviate the two endpoints of the segment.
  associativityAlmostComplex_eq_cayleySegment_rightPlumbed h₀ J hJ Jout hJout G hG G' hG' hL hτ hw

/-- On `[0, 1]` the family is the structure of the moving input ends. -/
private theorem associativityAlmostComplex_eq_movingEnds (hL : 0 ≤ L) (hτ : τ ∈ Icc 0 1) :
    h₀.associativityAlmostComplex J hJ Jout hJout G hG G' hG' L τ w =
      movingEnds h₀ J hJ Jout hJout hL τ w := by
  rw [associativityAlmostComplex, dite_eq_left hL]
  split_ifs with hl hr
  · exact cayleySegment_of_nonpos h₀ _ _ (by linarith [hτ.1])
  · exact cayleySegment_of_nonpos h₀ _ _ (by linarith [hτ.2])
  · rfl

/-- **On `[0, 1]` the family is the structure of the moving input ends.** -/
theorem associativityAlmostComplex_of_mem_Icc (hL : 0 ≤ L) (hτ : τ ∈ Icc 0 1) :
    h₀.associativityAlmostComplex J hJ Jout hJout G hG G' hG' L τ w =
      h₀.puncturedSphereAlmostComplex J hJ Jout hJout
        (Floer.associativityCenter (Real.exp (-(2 * π * L)) / 4) τ)
        (Floer.associativityScale (Real.exp (-(2 * π * L)) / 4) τ)
        (Floer.pairwise_mul_exp_add_le_norm_associativityCenter_sub_of_nonneg hL τ)
        (Floer.norm_associativityCenter_add_mul_exp_le_of_nonneg hL τ) w := by
  rw [associativityAlmostComplex_eq_movingEnds h₀ J hJ Jout hJout G hG G' hG' hL hτ, movingEnds]

/-- The family is tamed by `σ`. -/
theorem tames_associativityAlmostComplex (L τ : ℝ) (w : ℂ) :
    σ.Tames (h₀.associativityAlmostComplex J hJ Jout hJout G hG G' hG' L τ w) := by
  rw [associativityAlmostComplex]
  split_ifs
  · exact tames_cayleySegment h₀ _ _ _
  · exact tames_cayleySegment h₀ _ _ _
  · exact tames_movingEnds h₀ J hJ Jout hJout _ τ w
  · exact h₀.tames

/-- The family is compatible with `σ` when all the end and neck structures are. -/
theorem compatible_associativityAlmostComplex (hJc : ∀ i t, σ.Compatible (J i t))
    (hJoutc : ∀ t, σ.Compatible (Jout t)) (hGc : ∀ t, σ.Compatible (G t))
    (hG'c : ∀ t, σ.Compatible (G' t)) (L τ : ℝ) (w : ℂ) :
    σ.Compatible (h₀.associativityAlmostComplex J hJ Jout hJout G hG G' hG' L τ w) := by
  have hmov {L : ℝ} (hL : 0 ≤ L) (τ : ℝ) (w : ℂ) :
      σ.Compatible (movingEnds h₀ J hJ Jout hJout hL τ w) :=
    compatible_puncturedSphereAlmostComplex h₀ _ _ _ _ _ _ hJc hJoutc w
  -- The families of compatible structures, which contain all the end and neck structures.
  let S : Set (ℝ → SmoothAlmostComplexStructure I M) := {K | ∀ t, σ.Compatible (K t)}
  rw [associativityAlmostComplex]
  split_ifs with hL hl hr
  · refine compatible_cayleySegment h₀ (hmov hL τ w) ?_ (-τ)
    exact compatible_plumbedAlmostComplex h₀ h₀ _ _ _ _
      (associativityLeftInserted_mem (S := S) hJc hGc)
      (associativityLeftReceiving_mem (S := S) hJc hJoutc hGc) w hl.2
  · refine compatible_cayleySegment h₀ (hmov hL τ w) ?_ (τ - 1)
    exact compatible_plumbedAlmostComplex h₀ h₀ _ _ _ _
      (associativityRightInserted_mem (S := S) hJc hG'c)
      (associativityRightReceiving_mem (S := S) hJc hJoutc hG'c) w hr.2
  · exact hmov hL τ w
  · exact h₀

/-- **For `τ ≤ 0` the family switches on the neck of `(x₁ x₂) x₃`.** Inserting a pair of pants
with end structures `Ja` into the input `0` of one with end structures `Jb`, along a neck carrying
`Jb 0 = Ja ∞`, the family with inputs `Ja 0, Ja 1, Jb 1`, output `Jb ∞` and left neck structure
`Ja ∞` is, for `τ ≤ 0`, the Cayley segment at time `-τ` from the structure of the moving input
ends to the plumbed structure. The former is the plumbed structure with the two glued ends
switched off
(`TauCeti.SmoothTwoForm.Compatible.puncturedSphereAlmostComplex_associativity_of_nonpos`). -/
theorem associativityAlmostComplex_of_nonpos
    {Ja Jb : Puncture → ℝ → SmoothAlmostComplexStructure I M} (hJa : ∀ p t, σ.Tames (Ja p t))
    (hJb : ∀ p t, σ.Tames (Jb p t)) (hab : Jb zero = Ja inf) (hL : 0 ≤ L) (hτ : τ ≤ 0)
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ zero.plumbingMap L 1) :
    h₀.associativityAlmostComplex ![Ja zero, Ja one, Jb one]
        (fun i t => by fin_cases i <;> simp [hJa, hJb]) (Jb inf) (hJb inf) (Ja inf) (hJa inf)
        G' hG' L τ w =
      h₀.cayleySegment
        (tames_puncturedSphereAlmostComplex h₀ ![Ja zero, Ja one, Jb one]
          (fun i t => by fin_cases i <;> simp [hJa, hJb]) (Jb inf) (hJb inf)
          (Floer.pairwise_mul_exp_add_le_norm_associativityCenter_sub_of_nonneg hL τ)
          (Floer.norm_associativityCenter_add_mul_exp_le_of_nonneg hL τ) w)
        (tames_plumbedAlmostComplex h₀ h₀ Ja Jb hJa hJb w hw) (-τ) := by
  rw [associativityAlmostComplex_of_lt_one h₀ ![Ja zero, Ja one, Jb one] _ (Jb inf) (hJb inf)
    (Ja inf) (hJa inf) G' hG' hL (by linarith) hw]
  refine cayleySegment_congr h₀ _ _ _ _ rfl ?_ _
  refine plumbedAlmostComplex_congr h₀ h₀ _ _ _ _ _ _ ?_ ?_ _ hw
  · funext p
    cases p <;> simp
  · funext p
    cases p <;> simp [hab]

/-- **For `τ ≥ 1` the family switches on the neck of `x₁ (x₂ x₃)`.** Inserting a pair of pants
with end structures `Ja` into the input `1` of one with end structures `Jb`, along a neck carrying
`Jb 1 = Ja ∞`, the family with inputs `Jb 0, Ja 0, Ja 1`, output `Jb ∞` and right neck structure
`Ja ∞` is, for `τ ≥ 1`, the Cayley segment at time `τ - 1` from the structure of the moving input
ends to the plumbed structure. The former is the plumbed structure with the two glued ends
switched off
(`TauCeti.SmoothTwoForm.Compatible.puncturedSphereAlmostComplex_associativity_of_one_le`). -/
theorem associativityAlmostComplex_of_one_le
    {Ja Jb : Puncture → ℝ → SmoothAlmostComplexStructure I M} (hJa : ∀ p t, σ.Tames (Ja p t))
    (hJb : ∀ p t, σ.Tames (Jb p t)) (hab : Jb one = Ja inf) (hL : 0 ≤ L) (hτ : 1 ≤ τ)
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ one.plumbingMap L 1) :
    h₀.associativityAlmostComplex ![Jb zero, Ja zero, Ja one]
        (fun i t => by fin_cases i <;> simp [hJa, hJb]) (Jb inf) (hJb inf) G hG (Ja inf)
        (hJa inf) L τ w =
      h₀.cayleySegment
        (tames_puncturedSphereAlmostComplex h₀ ![Jb zero, Ja zero, Ja one]
          (fun i t => by fin_cases i <;> simp [hJa, hJb]) (Jb inf) (hJb inf)
          (Floer.pairwise_mul_exp_add_le_norm_associativityCenter_sub_of_nonneg hL τ)
          (Floer.norm_associativityCenter_add_mul_exp_le_of_nonneg hL τ) w)
        (tames_plumbedAlmostComplex h₀ h₀ Ja Jb hJa hJb w hw) (τ - 1) := by
  rw [associativityAlmostComplex_of_pos h₀ ![Jb zero, Ja zero, Ja one] _ (Jb inf) (hJb inf) G hG
    (Ja inf) (hJa inf) hL (by linarith) hw]
  refine cayleySegment_congr h₀ _ _ _ _ rfl ?_ _
  refine plumbedAlmostComplex_congr h₀ h₀ _ _ _ _ _ _ ?_ ?_ _ hw
  · funext p
    cases p <;> simp
  · funext p
    cases p <;> simp [hab]

/-- **For `τ ≤ -1` the family is the plumbed structure of `(x₁ x₂) x₃`.** Inserting a pair of
pants with end structures `Ja` into the input `0` of one with end structures `Jb`, along a neck
carrying `Jb 0 = Ja ∞`, the family with inputs `Ja 0, Ja 1, Jb 1`, output `Jb ∞` and left neck
structure `Ja ∞` is the plumbed structure. -/
theorem associativityAlmostComplex_of_le_neg_one
    {Ja Jb : Puncture → ℝ → SmoothAlmostComplexStructure I M} (hJa : ∀ p t, σ.Tames (Ja p t))
    (hJb : ∀ p t, σ.Tames (Jb p t)) (hab : Jb zero = Ja inf) (hL : 0 ≤ L) (hτ : τ ≤ -1)
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ zero.plumbingMap L 1) :
    h₀.associativityAlmostComplex ![Ja zero, Ja one, Jb one]
        (fun i t => by fin_cases i <;> simp [hJa, hJb]) (Jb inf) (hJb inf) (Ja inf) (hJa inf)
        G' hG' L τ w =
      h₀.plumbedAlmostComplex h₀ Ja Jb hJa hJb zero L w hw := by
  rw [associativityAlmostComplex_of_nonpos h₀ G' hG' hJa hJb hab hL (by linarith) hw,
    cayleySegment_of_one_le h₀ _ _ (by linarith)]

/-- **For `τ ≥ 2` the family is the plumbed structure of `x₁ (x₂ x₃)`.** Inserting a pair of
pants with end structures `Ja` into the input `1` of one with end structures `Jb`, along a neck
carrying `Jb 1 = Ja ∞`, the family with inputs `Jb 0, Ja 0, Ja 1`, output `Jb ∞` and right neck
structure `Ja ∞` is the plumbed structure. -/
theorem associativityAlmostComplex_of_two_le
    {Ja Jb : Puncture → ℝ → SmoothAlmostComplexStructure I M} (hJa : ∀ p t, σ.Tames (Ja p t))
    (hJb : ∀ p t, σ.Tames (Jb p t)) (hab : Jb one = Ja inf) (hL : 0 ≤ L) (hτ : 2 ≤ τ)
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ one.plumbingMap L 1) :
    h₀.associativityAlmostComplex ![Jb zero, Ja zero, Ja one]
        (fun i t => by fin_cases i <;> simp [hJa, hJb]) (Jb inf) (hJb inf) G hG (Ja inf)
        (hJa inf) L τ w =
      h₀.plumbedAlmostComplex h₀ Ja Jb hJa hJb one L w hw := by
  rw [associativityAlmostComplex_of_one_le h₀ G hG hJa hJb hab hL (by linarith) hw,
    cayleySegment_of_one_le h₀ _ _ (by linarith)]

/-! ### The ends -/

/-- At a point where the structure of the moving input ends and, whenever they are used there, the
plumbed structures of the two compositions are all `K`, the family is `K`. -/
private theorem associativityAlmostComplex_eq_of (hL : 0 ≤ L)
    {K : SmoothAlmostComplexStructure I M} (hm : movingEnds h₀ J hJ Jout hJout hL τ w = K)
    (hl : τ ≤ 0 → ∀ hw, leftPlumbed h₀ J hJ Jout hJout G hG L w hw = K)
    (hr : 1 ≤ τ → ∀ hw, rightPlumbed h₀ J hJ Jout hJout G' hG' L w hw = K) :
    h₀.associativityAlmostComplex J hJ Jout hJout G hG G' hG' L τ w = K := by
  have hseg {A B : SmoothAlmostComplexStructure I M} (hA : σ.Tames A) (hB : σ.Tames B)
      (hAK : A = K) (hBK : B = K) (t : ℝ) : h₀.cayleySegment hA hB t = K := by
    subst hAK hBK
    exact cayleySegment_self h₀ hA t
  rw [associativityAlmostComplex, dite_eq_left hL]
  split_ifs with h₁ h₂
  · exact hseg _ _ hm (hl h₁.1 h₁.2) _
  · exact hseg _ _ hm (hr h₂.1 h₂.2) _
  · exact hm

/-- For `τ ≤ 0`, the plumbed structure of `(x₁ x₂) x₃` is `J i t` far out on the input end `i`
of the configuration at `τ`, which is an input end of that plumbed sphere. -/
private theorem leftPlumbed_cylindricalEndLift (i : Fin 3) (hJp : Periodic (J i) 1)
    (hL : 2 ≤ L) (hτ : τ ≤ 0) {z : ℂ} (hz : 2 ≤ z.re) (hw) :
    leftPlumbed h₀ J hJ Jout hJout G hG L
        (Floer.associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
          Floer.associativityScale (Real.exp (-(2 * π * L)) / 4) τ i *
            zero.cylindricalEndLift z) hw =
      J i z.im := by
  revert hw
  generalize hP : Floer.associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
    Floer.associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z = w'
  rw [Floer.associativityCenter_of_nonpos hτ, Floer.associativityScale_of_nonpos hτ] at hP
  fin_cases i
  · obtain rfl : w' = zero.plumbingMap L (zero.cylindricalEndLift z) := by
      rw [← hP]
      simp [plumbingMap_apply, plumbingFactor_zero]
    exact fun hw => (plumbedAlmostComplex_plumbingMap_cylindricalEndLift h₀ h₀
      (associativityLeftInserted J G) (associativityLeftReceiving J Jout G) _ _
      (q := zero) (r := zero) (by simp) (by simp) hL (by simp) (by simpa using hJp) hz
      hw).trans (by simp)
  · obtain rfl : w' = zero.plumbingMap L (one.cylindricalEndLift z) := by
      rw [← hP]
      simp only [Fin.reduceFinMk, Matrix.cons_val, plumbingMap_apply, endCenter_zero,
        plumbingFactor_zero, cylindricalEndLift_zero, cylindricalEndLift_one]
      ring
    exact fun hw => (plumbedAlmostComplex_plumbingMap_cylindricalEndLift h₀ h₀
      (associativityLeftInserted J G) (associativityLeftReceiving J Jout G) _ _
      (q := zero) (r := one) (by simp) (by simp) hL (by simp) (by simpa using hJp) hz
      hw).trans (by simp)
  · obtain rfl : w' = one.cylindricalEndLift z := by
      rw [← hP]
      simp only [Fin.reduceFinMk, Matrix.cons_val, cylindricalEndLift_zero, cylindricalEndLift_one]
      ring
    exact fun hw => (plumbedAlmostComplex_cylindricalEndLift h₀ h₀
      (associativityLeftInserted J G) (associativityLeftReceiving J Jout G) _ _
      (q := zero) (r := one) (by simp) (by simp) hL
      (by simp) (by simpa using hJp) (by simpa using hz) hw).trans (by simp)

/-- For `τ ≥ 1`, the plumbed structure of `x₁ (x₂ x₃)` is `J i t` far out on the input end `i`
of the configuration at `τ`, which is an input end of that plumbed sphere. -/
private theorem rightPlumbed_cylindricalEndLift (i : Fin 3) (hJp : Periodic (J i) 1)
    (hL : 2 ≤ L) (hτ : 1 ≤ τ) {z : ℂ} (hz : 2 ≤ z.re) (hw) :
    rightPlumbed h₀ J hJ Jout hJout G' hG' L
        (Floer.associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
          Floer.associativityScale (Real.exp (-(2 * π * L)) / 4) τ i *
            zero.cylindricalEndLift z) hw =
      J i z.im := by
  revert hw
  generalize hP : Floer.associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
    Floer.associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z = w'
  rw [Floer.associativityCenter_of_one_le hτ, Floer.associativityScale_of_one_le hτ] at hP
  fin_cases i
  · obtain rfl : w' = zero.cylindricalEndLift z := by
      rw [← hP]
      simp
    exact fun hw => (plumbedAlmostComplex_cylindricalEndLift h₀ h₀
      (associativityRightInserted J G') (associativityRightReceiving J Jout G') _ _
      (q := one) (r := zero) (by simp) (by simp) hL
      (by simp) (by simpa using hJp) (by simpa using hz) hw).trans (by simp)
  · obtain rfl : w' = one.plumbingMap L (zero.cylindricalEndLift z) := by
      rw [← hP]
      simp [plumbingMap_apply, plumbingFactor_one, plumbingFactor_zero]
    exact fun hw => (plumbedAlmostComplex_plumbingMap_cylindricalEndLift h₀ h₀
      (associativityRightInserted J G') (associativityRightReceiving J Jout G') _ _
      (q := one) (r := zero) (by simp) (by simp) hL (by simp) (by simpa using hJp) hz
      hw).trans (by simp)
  · obtain rfl : w' = one.plumbingMap L (one.cylindricalEndLift z) := by
      rw [← hP]
      simp only [Fin.reduceFinMk, Matrix.cons_val, plumbingMap_apply, endCenter_one,
        plumbingFactor_one, plumbingFactor_zero, cylindricalEndLift_zero, cylindricalEndLift_one]
      ring
    exact fun hw => (plumbedAlmostComplex_plumbingMap_cylindricalEndLift h₀ h₀
      (associativityRightInserted J G') (associativityRightReceiving J Jout G') _ _
      (q := one) (r := one) (by simp) (by simp) hL (by simp) (by simpa using hJp) hz
      hw).trans (by simp)

/-- **The family is `J i t` far out on each input end.** If `J i` has period one in `t` and
`L ≥ 2`, then for every `τ`, on the part `s ≥ 2` of the input end `i` of the configuration at
`τ`, the structure at the point `c i + a i φ₀(z)` with end coordinates `z = s + i t` is `J i t`. -/
theorem associativityAlmostComplex_cylindricalEndLift (i : Fin 3) (hJp : Periodic (J i) 1)
    (hL : 2 ≤ L) (τ : ℝ) {z : ℂ} (hz : 2 ≤ z.re) :
    h₀.associativityAlmostComplex J hJ Jout hJout G hG G' hG' L τ
        (Floer.associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
          Floer.associativityScale (Real.exp (-(2 * π * L)) / 4) τ i *
            zero.cylindricalEndLift z) =
      J i z.im := by
  refine associativityAlmostComplex_eq_of h₀ J hJ Jout hJout G hG G' hG' (by linarith) ?_
    (fun hτ => leftPlumbed_cylindricalEndLift h₀ J hJ Jout hJout G hG i hJp hL hτ hz)
    (fun hτ => rightPlumbed_cylindricalEndLift h₀ J hJ Jout hJout G' hG' i hJp hL hτ hz)
  exact puncturedSphereAlmostComplex_cylindricalEndLift h₀ J hJ Jout hJout _ _ hJp
    (Floer.associativityScale_ne_zero (by positivity) τ i) hz

/-- **The family is `Jout t` far out on the output end.** If `Jout` has period one in `t` and
`L ≥ 2`, then for every `τ`, on the part `s ≤ -2` of the output end, the structure at the point
with end coordinates `z = s + i t` is `Jout t`. -/
theorem associativityAlmostComplex_cylindricalEndLift_inf (hJoutp : Periodic Jout 1)
    (hL : 2 ≤ L) (τ : ℝ) {z : ℂ} (hz : z.re ≤ -2) :
    h₀.associativityAlmostComplex J hJ Jout hJout G hG G' hG' L τ (inf.cylindricalEndLift z) =
      Jout z.im := by
  have hz' : 2 ≤ inf.endSign * z.re := by
    rw [endSign_inf]
    linarith
  refine associativityAlmostComplex_eq_of h₀ J hJ Jout hJout G hG G' hG' (by linarith) ?_
    (fun _ hw => ?_) (fun _ hw => ?_)
  · exact puncturedSphereAlmostComplex_cylindricalEndLift_inf h₀ J hJ Jout hJout _ _ hJoutp hz
  · exact (plumbedAlmostComplex_cylindricalEndLift h₀ h₀ (associativityLeftInserted J G)
      (associativityLeftReceiving J Jout G) _ _ (q := zero) (r := inf) (by simp) (by simp) hL
      (by simp) (by simpa using hJoutp) hz' hw).trans (by simp)
  · exact (plumbedAlmostComplex_cylindricalEndLift h₀ h₀ (associativityRightInserted J G')
      (associativityRightReceiving J Jout G') _ _ (q := one) (r := inf) (by simp) (by simp) hL
      (by simp) (by simpa using hJoutp) hz' hw).trans (by simp)

/-! ### Smoothness -/

section Smooth

/-- The parameters `(L, τ, w, x)` with `4 < L` at which `w` is not an input puncture of the
associativity path and lies in the region `W` of the domain, `τ ∈ T` and `W` depending on `L`. -/
private def paramOpens (T : Set ℝ) (hT : IsOpen T) (W : ℝ → Set ℂ)
    (hW : IsOpen {q : ℝ × ℂ | q.2 ∈ W q.1}) : TopologicalSpace.Opens (ℝ × ℝ × ℂ × M) where
  carrier := {p | 4 < p.1 ∧ p.2.1 ∈ T ∧ p.2.2.1 ∈ W p.1 ∧
    ∀ i, p.2.2.1 ≠ Floer.associativityCenter (Real.exp (-(2 * π * p.1)) / 4) p.2.1 i}
  is_open' := by
    simp only [Set.ofPred_and, Set.ofPred_forall]
    refine (isOpen_lt continuous_const continuous_fst).inter
      ((hT.preimage (continuous_fst.comp continuous_snd)).inter
        ((hW.preimage (continuous_fst.prodMk (continuous_fst.comp
          (continuous_snd.comp continuous_snd)))).inter
        (isOpen_iInter_of_finite fun i => isOpen_ne_fun
          (continuous_fst.comp (continuous_snd.comp continuous_snd))
          ((Floer.continuous_associativityCenter_apply i).comp
            (continuous_fst.prodMk (continuous_fst.comp continuous_snd))))))

omit [FiniteDimensional ℝ E] [IsManifold I (⊤ : ℕ∞) M] in
private theorem mem_paramOpens {T : Set ℝ} {hT : IsOpen T} {W : ℝ → Set ℂ}
    {hW : IsOpen {q : ℝ × ℂ | q.2 ∈ W q.1}} {p : ℝ × ℝ × ℂ × M} :
    p ∈ paramOpens T hT W hW ↔ 4 < p.1 ∧ p.2.1 ∈ T ∧ p.2.2.1 ∈ W p.1 ∧
      ∀ i, p.2.2.1 ≠ Floer.associativityCenter (Real.exp (-(2 * π * p.1)) / 4) p.2.1 i :=
  Iff.rfl

variable {n : ℕ∞ω} [ENat.LEInfty n]

variable (n) in
/-- The families of structures indexed by `t ∈ ℝ` which are jointly `C^n` on `ℝ × M`, as sections
of the tangent endomorphism bundle. -/
private def smoothFamilies : Set (ℝ → SmoothAlmostComplexStructure I M) :=
  {K | ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
    (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
      p.2 ((K p.1).toEndomorphism p.2))}

variable
  (hJp : ∀ i, Periodic (J i) 1)
  (hJs : ∀ i, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
    (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
      p.2 ((J i p.1).toEndomorphism p.2)))
  (hJoutp : Periodic Jout 1)
  (hJouts : ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
    (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
      p.2 ((Jout p.1).toEndomorphism p.2)))
  (hGp : Periodic G 1)
  (hGs : ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
    (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
      p.2 ((G p.1).toEndomorphism p.2)))
  (hG'p : Periodic G' 1)
  (hG's : ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
    (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
      p.2 ((G' p.1).toEndomorphism p.2)))

include hJp hJs hJoutp hJouts in
/-- On an open set of parameters `(L, τ, w, x)` avoiding the input punctures, the structures of the
moving input ends form a smooth family. -/
private theorem contMDiffAt_movingEnds_opens {T : Set ℝ} {hT : IsOpen T} {W : ℝ → Set ℂ}
    {hW : IsOpen {q : ℝ × ℂ | q.2 ∈ W q.1}} (u : paramOpens (M := M) T hT W hW) :
    ContMDiffAt (𝓘(ℝ).prod (𝓘(ℝ).prod (𝓘(ℝ, ℂ).prod I))) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun v : paramOpens (M := M) T hT W hW => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) v.val.2.2.2
        ((movingEnds h₀ J hJ Jout hJout (by linarith [v.property.1] : (0 : ℝ) ≤ v.val.1) v.val.2.1
          v.val.2.2.1).toEndomorphism v.val.2.2.2)) u := by
  have hval := (contMDiff_subtypeVal (n := n) (I := 𝓘(ℝ).prod (𝓘(ℝ).prod (𝓘(ℝ, ℂ).prod I)))
    (U := paramOpens (M := M) T hT W hW)).contMDiffAt (x := u)
  have hf : ContDiff ℝ n fun L : ℝ => Real.exp (-(2 * π * L)) / 4 := by fun_prop
  exact h₀.contMDiffAt_puncturedSphereAlmostComplex_associativity Jout hJout hJ hJp hJs hJoutp
    hJouts (f := fun v : paramOpens (M := M) T hT W hW => Real.exp (-(2 * π * v.val.1)) / 4)
    (τ := fun v => v.val.2.1) (g := fun v => v.val.2.2.1) (b := fun v => v.val.2.2.2)
    (fun v => Floer.pairwise_mul_exp_add_le_norm_associativityCenter_sub_of_nonneg
      (by linarith [v.property.1]) _)
    (fun v => Floer.norm_associativityCenter_add_mul_exp_le_of_nonneg
      (by linarith [v.property.1]) _)
    (hf.contMDiff.contMDiffAt.comp u (contMDiffAt_fst.comp u hval))
    (contMDiffAt_fst.comp u (contMDiffAt_snd.comp u hval))
    (contMDiffAt_fst.comp u (contMDiffAt_snd.comp u (contMDiffAt_snd.comp u hval)))
    (contMDiffAt_snd.comp u (contMDiffAt_snd.comp u (contMDiffAt_snd.comp u hval)))
    (by positivity) u.property.2.2.2


include hJp hJs hJoutp hJouts hGp hGs in
/-- On an open set of parameters `(L, τ, w, x)` whose domain points avoid the punctures of the
plumbed sphere of `(x₁ x₂) x₃`, its plumbed structures form a smooth family. -/
private theorem contMDiff_leftPlumbed_opens {T : Set ℝ} {hT : IsOpen T} {W : ℝ → Set ℂ}
    {hW : IsOpen {q : ℝ × ℂ | q.2 ∈ W q.1}}
    (hWl : ∀ L w, w ∈ W L → (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ zero.plumbingMap L 1) :
    ContMDiff (𝓘(ℝ).prod (𝓘(ℝ).prod (𝓘(ℝ, ℂ).prod I))) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun v : paramOpens (M := M) T hT W hW => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) v.val.2.2.2
        ((leftPlumbed h₀ J hJ Jout hJout G hG v.val.1 v.val.2.2.1
          (hWl _ _ v.property.2.2.1)).toEndomorphism v.val.2.2.2)) := by
  have hval := contMDiff_subtypeVal (n := n) (I := 𝓘(ℝ).prod (𝓘(ℝ).prod (𝓘(ℝ, ℂ).prod I)))
    (U := paramOpens (M := M) T hT W hW)
  exact contMDiff_plumbedAlmostComplex h₀ h₀ (associativityLeftInserted J G)
    (associativityLeftReceiving J Jout G) _ _
    (associativityLeftInserted_mem (S := {K | Periodic K 1}) hJp hGp)
    (associativityLeftInserted_mem (S := smoothFamilies n) hJs hGs)
    (associativityLeftReceiving_mem (S := {K | Periodic K 1}) hJp hJoutp hGp)
    (associativityLeftReceiving_mem (S := smoothFamilies n) hJs hJouts hGs) (by simp) (by simp)
    (contMDiff_fst.comp hval) (contMDiff_fst.comp (contMDiff_snd.comp (contMDiff_snd.comp hval)))
    (contMDiff_snd.comp (contMDiff_snd.comp (contMDiff_snd.comp hval))) (fun v => v.property.1)
    (fun v => hWl _ _ v.property.2.2.1)

include hJp hJs hJoutp hJouts hG'p hG's in
/-- On an open set of parameters `(L, τ, w, x)` whose domain points avoid the punctures of the
plumbed sphere of `x₁ (x₂ x₃)`, its plumbed structures form a smooth family. -/
private theorem contMDiff_rightPlumbed_opens {T : Set ℝ} {hT : IsOpen T} {W : ℝ → Set ℂ}
    {hW : IsOpen {q : ℝ × ℂ | q.2 ∈ W q.1}}
    (hWr : ∀ L w, w ∈ W L → (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ one.plumbingMap L 1) :
    ContMDiff (𝓘(ℝ).prod (𝓘(ℝ).prod (𝓘(ℝ, ℂ).prod I))) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun v : paramOpens (M := M) T hT W hW => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) v.val.2.2.2
        ((rightPlumbed h₀ J hJ Jout hJout G' hG' v.val.1 v.val.2.2.1
          (hWr _ _ v.property.2.2.1)).toEndomorphism v.val.2.2.2)) := by
  have hval := contMDiff_subtypeVal (n := n) (I := 𝓘(ℝ).prod (𝓘(ℝ).prod (𝓘(ℝ, ℂ).prod I)))
    (U := paramOpens (M := M) T hT W hW)
  exact contMDiff_plumbedAlmostComplex h₀ h₀ (associativityRightInserted J G')
    (associativityRightReceiving J Jout G') _ _
    (associativityRightInserted_mem (S := {K | Periodic K 1}) hJp hG'p)
    (associativityRightInserted_mem (S := smoothFamilies n) hJs hG's)
    (associativityRightReceiving_mem (S := {K | Periodic K 1}) hJp hJoutp hG'p)
    (associativityRightReceiving_mem (S := smoothFamilies n) hJs hJouts hG's) (by simp) (by simp)
    (contMDiff_fst.comp hval) (contMDiff_fst.comp (contMDiff_snd.comp (contMDiff_snd.comp hval)))
    (contMDiff_snd.comp (contMDiff_snd.comp (contMDiff_snd.comp hval))) (fun v => v.property.1)
    (fun v => hWr _ _ v.property.2.2.1)

include hJp hJs hJoutp hJouts hGp hGs in
/-- Near a parameter `τ ≤ 0` the family is the Cayley segment towards the plumbed structure of
`(x₁ x₂) x₃`, on an open set of parameters where both endpoints are smooth families. -/
private theorem contMDiffAt_associativityAlmostComplex_prod_of_nonpos
    {p₀ : ℝ × ℝ × ℂ × M} (hL₀ : 4 < p₀.1)
    (hw₀ : ∀ i, p₀.2.2.1 ≠ Floer.associativityCenter (Real.exp (-(2 * π * p₀.1)) / 4) p₀.2.1 i)
    (hτ : p₀.2.1 ≤ 0) :
    ContMDiffAt (𝓘(ℝ).prod (𝓘(ℝ).prod (𝓘(ℝ, ℂ).prod I))) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × ℝ × ℂ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) p.2.2.2
        ((h₀.associativityAlmostComplex J hJ Jout hJout G hG G' hG' p.1 p.2.1
          p.2.2.1).toEndomorphism p.2.2.2)) p₀ := by
  let U := paramOpens (M := M) (Iio 1) isOpen_Iio
    (fun L => {w | (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ zero.plumbingMap L 1}) (isOpen_plumbedSphere_prod zero)
  have hc := Floer.associativityCenter_eq_plumbingMap_of_nonpos (L := p₀.1) hτ
  have hp₀ : p₀ ∈ U := mem_paramOpens.2 ⟨hL₀, Set.mem_Iio.2 (by linarith),
    ⟨⟨by simpa [hc] using hw₀ 0, by simpa [hc] using hw₀ 2⟩, by simpa [hc] using hw₀ 1⟩, hw₀⟩
  refine (contMDiffAt_subtype_iff (U := U) (x := ⟨p₀, hp₀⟩)).mp ?_
  have hval := (contMDiff_subtypeVal (n := n)
    (I := 𝓘(ℝ).prod (𝓘(ℝ).prod (𝓘(ℝ, ℂ).prod I))) (U := U)).contMDiffAt (x := ⟨p₀, hp₀⟩)
  refine (contMDiffAt_cayleySegment h₀ (fun v : U => tames_movingEnds h₀ J hJ Jout hJout
      (by linarith [(mem_paramOpens.1 v.property).1] : (0 : ℝ) ≤ v.val.1) v.val.2.1 v.val.2.2.1)
    (fun v : U => tames_leftPlumbed h₀ J hJ Jout hJout G hG v.val.1 v.val.2.2.1
      (mem_paramOpens.1 v.property).2.2.1) (t := fun v => -v.val.2.1)
    (contMDiffAt_fst.comp _ (contMDiffAt_snd.comp _ hval)).neg
    (contMDiffAt_snd.comp _ (contMDiffAt_snd.comp _ (contMDiffAt_snd.comp _ hval)))
    (contMDiffAt_movingEnds_opens h₀ J hJ Jout hJout hJp hJs hJoutp hJouts _)
    (contMDiff_leftPlumbed_opens h₀ J hJ Jout hJout G hG hJp hJs hJoutp hJouts hGp hGs
      (fun _ _ h => h) _)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => ?_)
  obtain ⟨hv₁, hv₂, hv₃, -⟩ := mem_paramOpens.1 v.property
  dsimp only [Function.comp_apply]
  rw [associativityAlmostComplex_eq_cayleySegment_leftPlumbed h₀ J hJ Jout hJout G hG G' hG'
    (by linarith) hv₂ hv₃]

include hJp hJs hJoutp hJouts in
/-- Near a parameter `τ ∈ (0, 1)` the family is the structure of the moving input ends. -/
private theorem contMDiffAt_associativityAlmostComplex_prod_of_mem_Ioo
    {p₀ : ℝ × ℝ × ℂ × M} (hL₀ : 4 < p₀.1)
    (hw₀ : ∀ i, p₀.2.2.1 ≠ Floer.associativityCenter (Real.exp (-(2 * π * p₀.1)) / 4) p₀.2.1 i)
    (hτ : 0 < p₀.2.1) (hτ₁ : p₀.2.1 < 1) :
    ContMDiffAt (𝓘(ℝ).prod (𝓘(ℝ).prod (𝓘(ℝ, ℂ).prod I))) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × ℝ × ℂ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) p.2.2.2
        ((h₀.associativityAlmostComplex J hJ Jout hJout G hG G' hG' p.1 p.2.1
          p.2.2.1).toEndomorphism p.2.2.2)) p₀ := by
  let U := paramOpens (M := M) (Ioo 0 1) isOpen_Ioo (fun _ => univ) isOpen_univ
  have hp₀ : p₀ ∈ U := mem_paramOpens.2 ⟨hL₀, ⟨hτ, hτ₁⟩, trivial, hw₀⟩
  refine (contMDiffAt_subtype_iff (U := U) (x := ⟨p₀, hp₀⟩)).mp ?_
  refine (contMDiffAt_movingEnds_opens h₀ J hJ Jout hJout hJp hJs hJoutp hJouts
    _).congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => ?_)
  obtain ⟨hv₁, hv₂, -, -⟩ := mem_paramOpens.1 v.property
  dsimp only
  rw [associativityAlmostComplex_eq_movingEnds h₀ J hJ Jout hJout G hG G' hG' (by linarith)
    (Ioo_subset_Icc_self hv₂)]

include hJp hJs hJoutp hJouts hG'p hG's in
/-- Near a parameter `τ ≥ 1` the family is the Cayley segment towards the plumbed structure of
`x₁ (x₂ x₃)`, on an open set of parameters where both endpoints are smooth families. -/
private theorem contMDiffAt_associativityAlmostComplex_prod_of_one_le
    {p₀ : ℝ × ℝ × ℂ × M} (hL₀ : 4 < p₀.1)
    (hw₀ : ∀ i, p₀.2.2.1 ≠ Floer.associativityCenter (Real.exp (-(2 * π * p₀.1)) / 4) p₀.2.1 i)
    (hτ₁ : 1 ≤ p₀.2.1) :
    ContMDiffAt (𝓘(ℝ).prod (𝓘(ℝ).prod (𝓘(ℝ, ℂ).prod I))) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × ℝ × ℂ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) p.2.2.2
        ((h₀.associativityAlmostComplex J hJ Jout hJout G hG G' hG' p.1 p.2.1
          p.2.2.1).toEndomorphism p.2.2.2)) p₀ := by
  let U := paramOpens (M := M) (Ioi 0) isOpen_Ioi
    (fun L => {w | (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ one.plumbingMap L 1}) (isOpen_plumbedSphere_prod one)
  have hc := congrFun (Floer.associativityCenter_comp_finRotate_of_one_le (L := p₀.1) hτ₁)
  have hc' (i : Fin 3) :
      p₀.2.2.1 ≠ ![one.endCenter, one.plumbingMap p₀.1 1, zero.endCenter] i := by
    rw [← hc i]
    exact hw₀ (finRotate 3 i)
  have hp₀ : p₀ ∈ U := mem_paramOpens.2 ⟨hL₀, Set.mem_Ioi.2 (by linarith),
    ⟨⟨by simpa using hc' 2, by simpa using hc' 0⟩, by simpa using hc' 1⟩, hw₀⟩
  refine (contMDiffAt_subtype_iff (U := U) (x := ⟨p₀, hp₀⟩)).mp ?_
  have hval := (contMDiff_subtypeVal (n := n)
    (I := 𝓘(ℝ).prod (𝓘(ℝ).prod (𝓘(ℝ, ℂ).prod I))) (U := U)).contMDiffAt (x := ⟨p₀, hp₀⟩)
  refine (contMDiffAt_cayleySegment h₀ (fun v : U => tames_movingEnds h₀ J hJ Jout hJout
      (by linarith [(mem_paramOpens.1 v.property).1] : (0 : ℝ) ≤ v.val.1) v.val.2.1 v.val.2.2.1)
    (fun v : U => tames_rightPlumbed h₀ J hJ Jout hJout G' hG' v.val.1 v.val.2.2.1
      (mem_paramOpens.1 v.property).2.2.1) (t := fun v => v.val.2.1 - 1)
    ((contMDiffAt_fst.comp _ (contMDiffAt_snd.comp _ hval)).sub contMDiffAt_const)
    (contMDiffAt_snd.comp _ (contMDiffAt_snd.comp _ (contMDiffAt_snd.comp _ hval)))
    (contMDiffAt_movingEnds_opens h₀ J hJ Jout hJout hJp hJs hJoutp hJouts _)
    (contMDiff_rightPlumbed_opens h₀ J hJ Jout hJout G' hG' hJp hJs hJoutp hJouts hG'p hG's
      (fun _ _ h => h) _)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => ?_)
  obtain ⟨hv₁, hv₂, hv₃, -⟩ := mem_paramOpens.1 v.property
  dsimp only [Function.comp_apply]
  rw [associativityAlmostComplex_eq_cayleySegment_rightPlumbed h₀ J hJ Jout hJout G hG G' hG'
    (by linarith) hv₂ hv₃]

include hJp hJs hJoutp hJouts hGp hGs hG'p hG's in
/-- The family is smooth on the product `ℝ × ℝ × ℂ × M` of neck lengths, parameters, domain points
and points of `M`, at every point with `L > 4` whose domain point is not an input puncture. -/
private theorem contMDiffAt_associativityAlmostComplex_prod {p₀ : ℝ × ℝ × ℂ × M}
    (hL₀ : 4 < p₀.1)
    (hw₀ : ∀ i, p₀.2.2.1 ≠ Floer.associativityCenter (Real.exp (-(2 * π * p₀.1)) / 4) p₀.2.1 i) :
    ContMDiffAt (𝓘(ℝ).prod (𝓘(ℝ).prod (𝓘(ℝ, ℂ).prod I))) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × ℝ × ℂ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) p.2.2.2
        ((h₀.associativityAlmostComplex J hJ Jout hJout G hG G' hG' p.1 p.2.1
          p.2.2.1).toEndomorphism p.2.2.2)) p₀ := by
  rcases le_or_gt p₀.2.1 0 with hτ | hτ
  · exact contMDiffAt_associativityAlmostComplex_prod_of_nonpos h₀ J hJ Jout hJout G hG G' hG' hJp
      hJs hJoutp hJouts hGp hGs hL₀ hw₀ hτ
  rcases lt_or_ge p₀.2.1 1 with hτ₁ | hτ₁
  · exact contMDiffAt_associativityAlmostComplex_prod_of_mem_Ioo h₀ J hJ Jout hJout G hG G' hG' hJp
      hJs hJoutp hJouts hL₀ hw₀ hτ hτ₁
  · exact contMDiffAt_associativityAlmostComplex_prod_of_one_le h₀ J hJ Jout hJout G hG G' hG' hJp
      hJs hJoutp hJouts hG'p hG's hL₀ hw₀ hτ₁

include hJp hJs hJoutp hJouts hGp hGs hG'p hG's in
/-- **The family is smooth.** For end and neck structures which have period one in `t` and are
jointly `C^n` on `ℝ × M`, the structures of the associativity family are `C^n` jointly in the neck
length, the parameter `τ`, the domain point and the point of `M`, as sections of the tangent
endomorphism bundle, at every neck length `L > 4` and every domain point other than the three input
punctures `TauCeti.Floer.associativityCenter (exp (-2πL) / 4) τ` of the configuration at `τ`. -/
theorem contMDiffAt_associativityAlmostComplex {EN HN N : Type*} [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN} [TopologicalSpace N]
    [ChartedSpace HN N] {ℓ τ : N → ℝ} {g : N → ℂ} {b : N → M} {y₀ : N}
    (hℓ : ContMDiffAt IN 𝓘(ℝ) n ℓ y₀) (hτ : ContMDiffAt IN 𝓘(ℝ) n τ y₀)
    (hg : ContMDiffAt IN 𝓘(ℝ, ℂ) n g y₀) (hb : ContMDiffAt IN I n b y₀) (hℓ₀ : 4 < ℓ y₀)
    (hg₀ : ∀ i, g y₀ ≠ Floer.associativityCenter (Real.exp (-(2 * π * ℓ y₀)) / 4) (τ y₀) i) :
    ContMDiffAt IN (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) (b y)
        ((h₀.associativityAlmostComplex J hJ Jout hJout G hG G' hG' (ℓ y) (τ y)
          (g y)).toEndomorphism (b y))) y₀ :=
  (contMDiffAt_associativityAlmostComplex_prod h₀ J hJ Jout hJout G hG G' hG' hJp hJs hJoutp
    hJouts hGp hGs hG'p hG's (p₀ := (ℓ y₀, τ y₀, g y₀, b y₀)) hℓ₀ hg₀).comp y₀
    (hℓ.prodMk (hτ.prodMk (hg.prodMk hb)))

end Smooth

end TauCeti.SmoothTwoForm.Compatible

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Stabilizer
public import TauCeti.Analysis.Complex.RootsOfUnityQuotient

/-!
# Precisely invariant discs at points of a Fuchsian group

Let `Γ ≤ PSL(2, ℝ)` and `z ∈ ℍ`. Since `PSL(2, ℝ)` acts by hyperbolic isometries, the
stabilizer of `z` in `Γ` preserves every hyperbolic disc `B(z, r)` about `z`. When that stabilizer
is finite, of order `m`, the disc coordinate centred at `z` turns its action on `B(z, r)` into the
action of the `m`-th roots of unity on the Euclidean disc of radius `tanh (r / 2)`, so the orbit
space of `B(z, r)` under the stabilizer is again a disc, with coordinate `u ↦ u ^ m`
(`Subgroup.stabilizerBallQuotientHomeomorph`).

For a discrete `Γ`, a small enough disc `B(z, r)` is *precisely invariant*: an element of `Γ`
that moves some point of `B(z, r)` into `B(z, r)` fixes `z`
(`Subgroup.eventually_mem_stabilizer_of_image_smul_ball_inter_nonempty`), so the translates of
`B(z, r)` by elements outside the stabilizer are disjoint from `B(z, r)`. For such `r` the orbit
space of `B(z, r)` under the stabilizer is an open subset of the orbit space `Γ \ ℍ`
(`Subgroup.eventually_isOpenEmbedding_stabilizerBallQuotientToQuotient`). Together these give
the local chart of the quotient at an elliptic point of order `m`: near the orbit of `z`, the
quotient `Γ \ ℍ` is a disc, and the orbit of `τ` has coordinate `(discCoordinate z τ) ^ m`.

## Main declarations

* `Subgroup.stabilizerBall`: the hyperbolic disc of radius `r` about `z`, as a set invariant under
  the stabilizer of `z`.
* `Subgroup.stabilizerBallQuotientHomeomorph`: its orbit space under a finite stabilizer of order
  `m` is homeomorphic to the Euclidean disc of radius `tanh (r / 2) ^ m`, sending the orbit of `τ`
  to `(discCoordinate z τ) ^ m`.
* `Subgroup.eventually_mem_stabilizer_of_image_smul_ball_inter_nonempty`: small discs about a
  point are precisely invariant under a properly discontinuous `Γ`.
* `Subgroup.stabilizerBallQuotientToQuotient`: the induced map from the local orbit space to
  `Γ \ ℍ`, and `Subgroup.eventually_isOpenEmbedding_stabilizerBallQuotientToQuotient`: it is an
  open embedding for small discs.

## References

* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of
  Chicago Press, 1992, §2.2.
* Hershel M. Farkas and Irwin Kra, *Riemann Surfaces*, second edition, Graduate Texts in
  Mathematics 71, Springer, 1992, Chapter I §4.
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter III §3.
-/

public section

noncomputable section

open Filter Matrix.ProjectiveSpecialLinearGroup Metric MulAction Set Topology UpperHalfPlane

open scoped MatrixGroups

namespace Subgroup

variable (Γ : Subgroup PSL(2, ℝ)) (z : ℍ)

/-- The open hyperbolic disc of radius `r` about `z`, as a set invariant under the stabilizer of
`z` in `Γ`. -/
def stabilizerBall (r : ℝ) : SubMulAction (stabilizer Γ z) ℍ where
  carrier := ball z r
  smul_mem' q τ hτ := by
    have hq : ((q : Γ) : PSL(2, ℝ)) • z = z := q.2
    have hdist := dist_smul ((q : Γ) : PSL(2, ℝ)) τ z
    rw [hq] at hdist
    rw [mem_ball, Subgroup.smul_def, Subgroup.smul_def, hdist]
    exact hτ

@[simp]
theorem coe_stabilizerBall (r : ℝ) : (stabilizerBall Γ z r : Set ℍ) = ball z r :=
  (rfl)

@[simp]
theorem mem_stabilizerBall {r : ℝ} {τ : ℍ} : τ ∈ stabilizerBall Γ z r ↔ dist τ z < r :=
  Iff.rfl

section LocalModel

variable [Finite (stabilizer Γ z)]

/-- Two points of `ℍ` lie in the same orbit of a finite stabilizer of `z` of order `m` exactly
when their disc coordinates centred at `z` have the same `m`-th power. -/
theorem mem_orbit_stabilizer_iff_discCoordinate_pow_eq_pow {τ σ : ℍ} :
    τ ∈ orbit (stabilizer Γ z) σ ↔
      discCoordinate z τ ^ Nat.card (stabilizer Γ z) =
        discCoordinate z σ ^ Nat.card (stabilizer Γ z) := by
  have : NeZero (Nat.card (stabilizer Γ z)) := ⟨Nat.card_pos.ne'⟩
  rw [TauCeti.pow_eq_pow_iff_exists_rootsOfUnity_smul (NeZero.ne _)]
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨rootsOfUnity.mkOfPowEq _ (stabilizerDeriv_pow_card Γ z q⁻¹), ?_⟩
    rw [rootsOfUnity.smul_eq_mul, rootsOfUnity.coe_mkOfPowEq, discCoordinate_smul_stabilizer,
      ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  · rintro ⟨ζ, hζ⟩
    obtain ⟨q, hq⟩ : ((ζ : ℂˣ) : ℂ) ∈ Set.range (stabilizerDeriv Γ z) := by
      rw [range_stabilizerDeriv]
      exact (mem_rootsOfUnity' _ _).mp ζ.2
    refine ⟨q⁻¹, discCoordinate_injective z ?_⟩
    rw [discCoordinate_smul_stabilizer, ← hζ, rootsOfUnity.smul_eq_mul, ← hq, ← mul_assoc,
      ← map_mul, inv_mul_cancel, map_one, one_mul]

/-- The disc coordinate centred at `z`, from the hyperbolic disc of radius `r` about `z` onto the
Euclidean disc of radius `tanh (r / 2)`, as a map of sets invariant under the stabilizer and
under the roots of unity of its order. -/
private def stabilizerBallHomeomorph (r : ℝ) :
    stabilizerBall Γ z r ≃ₜ
      TauCeti.rootsOfUnityBall (Nat.card (stabilizer Γ z)) (Real.tanh (r / 2)) :=
  (Homeomorph.setCongr (coe_stabilizerBall Γ z r)).trans ((discCoordinateBallHomeomorph z r).trans
    (Homeomorph.setCongr (TauCeti.coe_rootsOfUnityBall _).symm))

private theorem coe_stabilizerBallHomeomorph (r : ℝ) (τ : stabilizerBall Γ z r) :
    (stabilizerBallHomeomorph Γ z r τ : ℂ) = discCoordinate z τ := by
  rw [stabilizerBallHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply,
    Homeomorph.setCongr_apply, Homeomorph.setCongr_apply, coe_discCoordinateBallHomeomorph_apply]

private theorem orbitRel_stabilizerBallHomeomorph_iff (r : ℝ)
    (τ σ : stabilizerBall Γ z r) :
    orbitRel (stabilizer Γ z) (stabilizerBall Γ z r) τ σ ↔
      orbitRel (rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ)
        (TauCeti.rootsOfUnityBall (Nat.card (stabilizer Γ z)) (Real.tanh (r / 2)))
        (stabilizerBallHomeomorph Γ z r τ) (stabilizerBallHomeomorph Γ z r σ) := by
  have : NeZero (Nat.card (stabilizer Γ z)) := ⟨Nat.card_pos.ne'⟩
  rw [orbitRel_apply, orbitRel_apply, SubMulAction.mem_orbit_subMul_iff,
    SubMulAction.mem_orbit_subMul_iff, mem_orbit_stabilizer_iff_discCoordinate_pow_eq_pow,
    ← orbitRel_apply (G := rootsOfUnity _ ℂ), TauCeti.orbitRel_rootsOfUnity_apply (NeZero.ne _),
    coe_stabilizerBallHomeomorph, coe_stabilizerBallHomeomorph]

/-- **The local model of the quotient at a point with finite stabilizer.** If the stabilizer of
`z` in `Γ` has order `m` and `0 ≤ r`, the orbit space of the hyperbolic disc of radius `r`
about `z` under that stabilizer is homeomorphic to the Euclidean disc of radius
`tanh (r / 2) ^ m`, by sending the orbit of `τ` to `(discCoordinate z τ) ^ m`. -/
def stabilizerBallQuotientHomeomorph {r : ℝ} (hr : 0 ≤ r) :
    orbitRel.Quotient (stabilizer Γ z) (stabilizerBall Γ z r) ≃ₜ
      ball (0 : ℂ) (Real.tanh (r / 2) ^ Nat.card (stabilizer Γ z)) :=
  have : NeZero (Nat.card (stabilizer Γ z)) := ⟨Nat.card_pos.ne'⟩
  (Homeomorph.Quotient.congr (stabilizerBallHomeomorph Γ z r)
      (orbitRel_stabilizerBallHomeomorph_iff Γ z r)).trans
    (TauCeti.rootsOfUnityBallQuotientHomeomorph (by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg (Real.sinh_nonneg_iff.mpr (by positivity)) (Real.cosh_pos _).le))

@[simp]
theorem coe_stabilizerBallQuotientHomeomorph_mk {r : ℝ} (hr : 0 ≤ r)
    (τ : stabilizerBall Γ z r) :
    (stabilizerBallQuotientHomeomorph Γ z hr (Quotient.mk _ τ) : ℂ) =
      discCoordinate z τ ^ Nat.card (stabilizer Γ z) := by
  have : NeZero (Nat.card (stabilizer Γ z)) := ⟨Nat.card_pos.ne'⟩
  rw [stabilizerBallQuotientHomeomorph, Homeomorph.trans_apply]
  rw [show
    Homeomorph.Quotient.congr (stabilizerBallHomeomorph Γ z r)
        (orbitRel_stabilizerBallHomeomorph_iff Γ z r) (Quotient.mk _ τ) =
      Quotient.mk _ (stabilizerBallHomeomorph Γ z r τ) by
    exact Quotient.congr_mk (stabilizerBallHomeomorph Γ z r).toEquiv
      (orbitRel_stabilizerBallHomeomorph_iff Γ z r) τ]
  rw [TauCeti.coe_rootsOfUnityBallQuotientHomeomorph_mk]
  exact congrArg (fun w : ℂ ↦ w ^ Nat.card (stabilizer Γ z))
    (coe_stabilizerBallHomeomorph Γ z r τ)

end LocalModel

/-- The map from the orbit space of the disc of radius `r` about `z` under the stabilizer of `z`
to the orbit space of `Γ`, sending the orbit of `τ` to its `Γ`-orbit. -/
def stabilizerBallQuotientToQuotient (r : ℝ) :
    orbitRel.Quotient (stabilizer Γ z) (stabilizerBall Γ z r) → orbitRel.Quotient Γ ℍ :=
  Quotient.map' (↑) fun _ _ h ↦ by
    rw [orbitRel_apply, SubMulAction.mem_orbit_subMul_iff] at h
    exact orbitRel_apply.mpr (orbit_subgroup_subset _ _ h)

@[simp]
theorem stabilizerBallQuotientToQuotient_mk (r : ℝ) (τ : stabilizerBall Γ z r) :
    stabilizerBallQuotientToQuotient Γ z r (Quotient.mk _ τ) = Quotient.mk _ (τ : ℍ) :=
  (rfl)

/-- The map from the local orbit space of a disc to the orbit space of `Γ` is continuous. -/
theorem continuous_stabilizerBallQuotientToQuotient (r : ℝ) :
    Continuous (stabilizerBallQuotientToQuotient Γ z r) :=
  continuous_subtype_val.quotient_map' _

/-- The map from the local orbit space of a disc to the orbit space of `Γ` is open. -/
theorem isOpenMap_stabilizerBallQuotientToQuotient (r : ℝ) :
    IsOpenMap (stabilizerBallQuotientToQuotient Γ z r) := by
  intro V hV
  have himage : stabilizerBallQuotientToQuotient Γ z r '' V =
      Quotient.mk _ '' ((↑) '' (Quotient.mk _ ⁻¹' V : Set (stabilizerBall Γ z r))) := by
    conv_lhs => rw [← image_preimage_eq V Quotient.mk_surjective]
    simp only [image_image, stabilizerBallQuotientToQuotient_mk]
  rw [himage]
  exact isOpenMap_quotient_mk'_mul _
    (isOpen_ball.isOpenMap_subtype_val _ (hV.preimage continuous_quotient_mk'))

variable [ProperlyDiscontinuousSMul Γ ℍ]

/-- **Small discs are precisely invariant.** If `Γ` acts properly discontinuously, then for every
small enough `r > 0`, an element of `Γ` that moves some point of the hyperbolic disc of radius `r`
about `z` into that disc fixes `z`. -/
theorem eventually_mem_stabilizer_of_image_smul_ball_inter_nonempty :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ g : Γ,
      ((g • ·) '' ball z r ∩ ball z r).Nonempty → g ∈ stabilizer Γ z := by
  obtain ⟨U, hU, hsmul⟩ := ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self Γ z
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  filter_upwards [Ioo_mem_nhdsGT hε] with r hr g hg
  have hsub : ball z r ⊆ U := (ball_subset_ball hr.2.le).trans hball
  exact hsmul g (hg.mono (inter_subset_inter (image_mono hsub) hsub))

/-- **The local orbit space of a small disc is open in `Γ \ ℍ`.** If `Γ` acts properly
discontinuously, then for every small enough `r > 0` the map from the orbit space of the
hyperbolic disc of radius `r` about `z` under the stabilizer of `z` to the orbit space of `Γ` is
an open embedding. -/
theorem eventually_isOpenEmbedding_stabilizerBallQuotientToQuotient :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z r) := by
  filter_upwards [eventually_mem_stabilizer_of_image_smul_ball_inter_nonempty Γ z] with r hr
  refine .of_continuous_injective_isOpenMap (continuous_stabilizerBallQuotientToQuotient Γ z r)
    ?_ (isOpenMap_stabilizerBallQuotientToQuotient Γ z r)
  rintro ⟨τ⟩ ⟨σ⟩ h
  obtain ⟨g, hg⟩ := orbitRel_apply.mp (Quotient.exact h)
  have hmem := hr g ⟨_, ⟨σ, σ.2, rfl⟩, by rw [hg]; exact τ.2⟩
  exact Quotient.sound (orbitRel_apply.mpr
    (SubMulAction.mem_orbit_subMul_iff.mpr ⟨⟨g, hmem⟩, hg⟩))

end Subgroup

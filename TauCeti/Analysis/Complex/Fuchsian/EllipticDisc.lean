/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Stabilizer
public import TauCeti.Analysis.Complex.UpperHalfPlane.Elliptic

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

* `Subgroup.mem_orbit_stabilizer_iff_discCoordinate_pow_eq_pow`: two points lie in the same
  finite-stabilizer orbit exactly when their disc coordinates have the same `m`-th power.
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
    refine ⟨stabilizerRotation Γ z q⁻¹, ?_⟩
    rw [discCoordinate_smul_eq_rotation_smul, smul_smul, ← map_mul, inv_mul_cancel, map_one,
      one_smul]
  · rintro ⟨ζ, hζ⟩
    let q := (stabilizerRotationEquiv Γ z).symm ζ
    have hq : stabilizerRotation Γ z q = ζ := by
      rw [← coe_stabilizerRotationEquiv]
      exact (stabilizerRotationEquiv Γ z).apply_symm_apply ζ
    refine ⟨q⁻¹, discCoordinate_injective z ?_⟩
    rw [discCoordinate_smul_eq_rotation_smul, ← hζ, ← hq, smul_smul, ← map_mul, inv_mul_cancel,
      map_one, one_smul]

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
  have hopen : IsOpen (stabilizerBall Γ z r : Set ℍ) := by
    rw [coe_stabilizerBall]
    exact isOpen_ball
  exact isOpenMap_quotient_mk'_mul _
    (hopen.isOpenMap_subtype_val _ (hV.preimage continuous_quotient_mk'))

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
  have hσ : (σ : ℍ) ∈ ball z r := by
    rw [← coe_stabilizerBall Γ z r]
    exact σ.2
  have hτ : (τ : ℍ) ∈ ball z r := by
    rw [← coe_stabilizerBall Γ z r]
    exact τ.2
  have hmem := hr g ⟨_, ⟨σ, hσ, rfl⟩, by rw [hg]; exact hτ⟩
  exact Quotient.sound (orbitRel_apply.mpr
    (SubMulAction.mem_orbit_subMul_iff.mpr ⟨⟨g, hmem⟩, hg⟩))

end Subgroup

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RootsOfUnity.Quotient
public import TauCeti.Analysis.Complex.UpperHalfPlane.ProperAction
public import TauCeti.Analysis.Complex.UpperHalfPlane.Stabilizer
public import TauCeti.Topology.MetricSpace.ProperlyDiscontinuous

/-!
# The elliptic disc of a point of the upper half-plane

Let `Γ ≤ PSL(2, ℝ)` be a subgroup and `z` a point of the upper half-plane. The stabilizer of `z`
in `Γ` acts by hyperbolic isometries fixing `z`, so it preserves every hyperbolic disc
`Subgroup.stabilizerBall Γ z ε` about `z`. If the action of `Γ` is properly discontinuous — in
particular if `Γ` is discrete — then for small `ε` no other element of `Γ` moves that disc to meet
itself (`TauCeti.exists_ball_disjoint_smul_of_notMem_stabilizer`). This separation result is the
key input identifying a neighbourhood in the full orbit space with the quotient of the disc by
the finite group `MulAction.stabilizer Γ z`.

That orbit space is computed here. In the disc coordinate centred at `z` the stabilizer acts by
the group of `m`-th roots of unity, `m` its order
(`Subgroup.stabilizerRotationEquiv`, `Subgroup.discCoordinate_smul_eq_rotation_smul`), and the
disc of hyperbolic radius `ε` becomes the Euclidean disc of radius `tanh (ε / 2)`
(`UpperHalfPlane.image_discCoordinate_ball`). The orbit map of a rotation group of order `m` on a
disc is `u ↦ u ^ m` (`TauCeti.rootsOfUnityBallQuotientHomeomorph`), so the orbit space is again a
disc, with coordinate `(disc coordinate) ^ m`. This power-map model is intended for the later
construction of a smooth chart on the full quotient and the proof that its quotient map has
multiplicity `m`; those conclusions are not established in this file.

## Main declarations

* `Subgroup.stabilizerBall`: the hyperbolic disc about `z`, as a set invariant under the
  stabilizer of `z`.
* `Subgroup.stabilizerBallHomeomorph`: the disc coordinate, as a homeomorphism from that disc onto
  a Euclidean disc, equivariant for `Subgroup.stabilizerRotationEquiv`.
* `Subgroup.stabilizerBallQuotientHomeomorph`: the orbit space of the invariant disc under the
  stabilizer is the Euclidean disc of radius `tanh (ε / 2) ^ m`, with coordinate the `m`-th power
  of the disc coordinate.
* `Subgroup.stabilizerBallQuotientToQuotient`: the induced map from the local orbit space to
  `Γ \ ℍ`; for all sufficiently small positive radii it is an open embedding.

## References

* Hershel Farkas and Irwin Kra, *Riemann Surfaces*, Graduate Texts in Mathematics 71, Springer,
  second edition, 1992, Chapter I §§4–5.
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §2.4.
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter III §§3–4.
-/

public section

noncomputable section

open Filter Matrix.ProjectiveSpecialLinearGroup Metric MulAction Set Topology UpperHalfPlane

open scoped MatrixGroups Pointwise

namespace Subgroup

open TauCeti

variable (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) (ε : ℝ)

/-- The hyperbolic disc of radius `ε` about `z`, as a set invariant under the stabilizer of `z`
in `Γ`: that stabilizer acts by hyperbolic isometries fixing `z`. -/
def stabilizerBall : SubMulAction (stabilizer Γ z) ℍ where
  carrier := ball z ε
  smul_mem' q τ hτ := by
    have hq : ((q : Γ) : PSL(2, ℝ)) • z = z := by
      have h := q.2
      rwa [mem_stabilizer_iff, Subgroup.smul_def] at h
    have hball : ((q : Γ) : PSL(2, ℝ)) • ball z ε = ball z ε := by
      rw [Metric.smul_ball, hq]
    simp only [Subgroup.smul_def]
    exact hball ▸ Set.smul_mem_smul_set hτ

@[simp]
theorem coe_stabilizerBall : (stabilizerBall Γ z ε : Set ℍ) = ball z ε := (rfl)

@[simp]
theorem mem_stabilizerBall {τ : ℍ} : τ ∈ stabilizerBall Γ z ε ↔ dist τ z < ε := Iff.rfl

/-- **The disc coordinate flattens the invariant hyperbolic disc**: it is a homeomorphism from
the hyperbolic disc of radius `ε` about `z` onto the Euclidean disc of radius `tanh (ε / 2)`
about `0`, carrying the stabilizer action to the rotation action of the `m`-th roots of unity by
`Subgroup.stabilizerBallHomeomorph_smul`. Its underlying coordinate and explicit inverse are
holomorphic by `UpperHalfPlane.mdifferentiable_discCoordinate` and
`UpperHalfPlane.analyticOnNhd_discCoordinateHomeomorph_symm`.

The stabilizer is assumed finite because the codomain needs it: `TauCeti.rootsOfUnityBall m` is
defined only for `m ≠ 0`, and for `m = 0` the group `rootsOfUnity 0 ℂ` is the whole unit group,
which does not preserve a disc. The finiteness-free geometry is
`UpperHalfPlane.discCoordinateHomeomorph` together with `UpperHalfPlane.image_discCoordinate_ball`,
of which this is the packaging against the roots-of-unity model. -/
def stabilizerBallHomeomorph [Finite (stabilizer Γ z)] :
    stabilizerBall Γ z ε ≃ₜ
      rootsOfUnityBall (Nat.card (stabilizer Γ z)) (Real.tanh (ε / 2)) where
  toFun τ :=
    ⟨discCoordinate z τ, mem_rootsOfUnityBall.mpr (mem_ball_iff_norm_discCoordinate_lt.mp τ.2)⟩
  invFun u :=
    ⟨(discCoordinateHomeomorph z).symm
        (.mk u ((mem_rootsOfUnityBall.mp u.2).trans (Real.tanh_lt_one _))),
      mem_ball_iff_norm_discCoordinate_lt.mpr (by
        rw [discCoordinate_discCoordinateHomeomorph_symm, Complex.UnitDisc.coe_mk]
        exact mem_rootsOfUnityBall.mp u.2)⟩
  left_inv τ :=
    Subtype.ext <| discCoordinate_injective z <| by
      simp only [discCoordinate_discCoordinateHomeomorph_symm, Complex.UnitDisc.coe_mk]
  right_inv u :=
    Subtype.ext <| by
      simp only [discCoordinate_discCoordinateHomeomorph_symm, Complex.UnitDisc.coe_mk]
  continuous_toFun :=
    Continuous.subtype_mk ((continuous_discCoordinate z).comp continuous_subtype_val) _
  continuous_invFun := by
    refine Continuous.subtype_mk
      ((discCoordinateHomeomorph z).symm.continuous.comp ?_) _
    exact Complex.UnitDisc.isEmbedding_coe.continuous_iff.mpr continuous_subtype_val

@[simp]
theorem coe_stabilizerBallHomeomorph [Finite (stabilizer Γ z)] (τ : stabilizerBall Γ z ε) :
    (stabilizerBallHomeomorph Γ z ε τ : ℂ) = discCoordinate z τ :=
  (rfl)

/-- **The disc coordinate conjugates the stabilizer action to a rotation action**: it is
equivariant along the identification `Subgroup.stabilizerRotationEquiv` of the stabilizer of `z`
with the `m`-th roots of unity. -/
@[simp]
theorem stabilizerBallHomeomorph_smul [Finite (stabilizer Γ z)] (q : stabilizer Γ z)
    (τ : stabilizerBall Γ z ε) :
    stabilizerBallHomeomorph Γ z ε (q • τ) =
      Subgroup.stabilizerRotationEquiv Γ z q • stabilizerBallHomeomorph Γ z ε τ :=
  Subtype.ext <| by
    rw [coe_stabilizerBallHomeomorph, SubMulAction.val_smul, SubMulAction.val_smul,
      Subgroup.coe_stabilizerRotationEquiv, coe_stabilizerBallHomeomorph,
      Subgroup.discCoordinate_smul_eq_rotation_smul]

/-- On the invariant disc, two points lie in the same stabilizer orbit exactly when their disc
coordinates lie in the same orbit of the `m`-th roots of unity. -/
theorem orbitRel_stabilizerBall_iff [Finite (stabilizer Γ z)] (τ σ : stabilizerBall Γ z ε) :
    orbitRel (stabilizer Γ z) (stabilizerBall Γ z ε) τ σ ↔
      orbitRel (rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ)
        (rootsOfUnityBall (Nat.card (stabilizer Γ z)) (Real.tanh (ε / 2)))
        (stabilizerBallHomeomorph Γ z ε τ) (stabilizerBallHomeomorph Γ z ε σ) := by
  simp only [orbitRel_apply, mem_orbit_iff]
  refine ⟨fun ⟨q, hq⟩ ↦ ⟨Subgroup.stabilizerRotationEquiv Γ z q, ?_⟩, fun ⟨ζ, hζ⟩ ↦ ?_⟩
  · rw [← stabilizerBallHomeomorph_smul, hq]
  · obtain ⟨q, rfl⟩ := (Subgroup.stabilizerRotationEquiv Γ z).surjective ζ
    exact ⟨q, (stabilizerBallHomeomorph Γ z ε).injective
      (by rw [stabilizerBallHomeomorph_smul, hζ])⟩

/-- **The stabilizer quotient coordinate.** For `0 ≤ ε`, the orbit space of the invariant
hyperbolic disc of radius `ε` about `z` under the stabilizer of `z`, a group of order `m`, is the
Euclidean disc of radius `tanh (ε / 2) ^ m`; the identification sends the orbit of `τ` to the
`m`-th power of its disc coordinate. A positive radius and a later quotient-neighbourhood
construction are needed to turn this model into a chart on the full `Γ`-orbit space. The
separation supplied by `TauCeti.exists_ball_disjoint_smul_of_notMem_stabilizer` is one input to
that later construction. -/
def stabilizerBallQuotientHomeomorph [Finite (stabilizer Γ z)] (hε : 0 ≤ ε) :
    orbitRel.Quotient (stabilizer Γ z) (stabilizerBall Γ z ε) ≃ₜ
      ball (0 : ℂ) (Real.tanh (ε / 2) ^ Nat.card (stabilizer Γ z)) :=
  (Homeomorph.Quotient.congr (stabilizerBallHomeomorph Γ z ε)
      (orbitRel_stabilizerBall_iff Γ z ε)).trans
    (rootsOfUnityBallQuotientHomeomorph (r := Real.tanh (ε / 2)) (by
      rw [← Real.tanh_zero]
      exact Real.tanh_strictMono.monotone (by linarith)))

@[simp]
theorem coe_stabilizerBallQuotientHomeomorph_mk [Finite (stabilizer Γ z)] (hε : 0 ≤ ε)
    (τ : stabilizerBall Γ z ε) :
    (stabilizerBallQuotientHomeomorph Γ z ε hε (Quotient.mk _ τ) : ℂ) =
      discCoordinate z τ ^ Nat.card (stabilizer Γ z) := by
  rw [stabilizerBallQuotientHomeomorph, Homeomorph.trans_apply,
    Homeomorph.Quotient.congr_mk,
    coe_rootsOfUnityBallQuotientHomeomorph_mk, coe_stabilizerBallHomeomorph]

/-- The map from the orbit space of the disc of radius `ε` about `z` under the stabilizer of `z`
to the orbit space of `Γ`, sending the orbit of `τ` to its `Γ`-orbit. -/
def stabilizerBallQuotientToQuotient :
    orbitRel.Quotient (stabilizer Γ z) (stabilizerBall Γ z ε) → orbitRel.Quotient Γ ℍ :=
  Quotient.map' (↑) fun _ _ h ↦ by
    rw [orbitRel_apply, SubMulAction.mem_orbit_subMul_iff] at h
    exact orbitRel_apply.mpr (orbit_subgroup_subset _ _ h)

@[simp]
theorem stabilizerBallQuotientToQuotient_mk (τ : stabilizerBall Γ z ε) :
    stabilizerBallQuotientToQuotient Γ z ε (Quotient.mk _ τ) = Quotient.mk _ (τ : ℍ) :=
  (rfl)

/-- The map from the local orbit space of a disc to the orbit space of `Γ` is continuous. -/
theorem continuous_stabilizerBallQuotientToQuotient :
    Continuous (stabilizerBallQuotientToQuotient Γ z ε) :=
  continuous_subtype_val.quotient_map' _

/-- The map from the local orbit space of a disc to the orbit space of `Γ` is open. -/
theorem isOpenMap_stabilizerBallQuotientToQuotient :
    IsOpenMap (stabilizerBallQuotientToQuotient Γ z ε) := by
  intro V hV
  have himage : stabilizerBallQuotientToQuotient Γ z ε '' V =
      Quotient.mk _ '' ((↑) '' (Quotient.mk _ ⁻¹' V : Set (stabilizerBall Γ z ε))) := by
    conv_lhs => rw [← image_preimage_eq V Quotient.mk_surjective]
    simp only [image_image, stabilizerBallQuotientToQuotient_mk]
  rw [himage]
  have hopen : IsOpen (stabilizerBall Γ z ε : Set ℍ) := by
    rw [coe_stabilizerBall]
    exact isOpen_ball
  exact isOpenMap_quotient_mk'_mul _
    (hopen.isOpenMap_subtype_val _ (hV.preimage continuous_quotient_mk'))

variable [ProperlyDiscontinuousSMul Γ ℍ]

/-- **The local orbit space of a small disc is open in `Γ \ ℍ`.** If `Γ` acts properly
discontinuously, then for every small enough `ε > 0` the map from the orbit space of the
hyperbolic disc of radius `ε` about `z` under the stabilizer of `z` to the orbit space of `Γ` is
an open embedding. -/
theorem eventually_isOpenEmbedding_stabilizerBallQuotientToQuotient :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z ε) := by
  filter_upwards [TauCeti.eventually_smul_eq_self_of_image_smul_ball_inter_nonempty Γ z] with ε hε
  refine .of_continuous_injective_isOpenMap
    (continuous_stabilizerBallQuotientToQuotient Γ z ε) ?_
    (isOpenMap_stabilizerBallQuotientToQuotient Γ z ε)
  rintro ⟨τ⟩ ⟨σ⟩ h
  obtain ⟨g, hg⟩ := orbitRel_apply.mp (Quotient.exact h)
  have hσ : (σ : ℍ) ∈ ball z ε := by
    rw [← coe_stabilizerBall Γ z ε]
    exact σ.2
  have hτ : (τ : ℍ) ∈ ball z ε := by
    rw [← coe_stabilizerBall Γ z ε]
    exact τ.2
  have hmem : g ∈ stabilizer Γ z :=
    MulAction.mem_stabilizer_iff.mpr (hε g ⟨_, ⟨σ, hσ, rfl⟩, by rw [hg]; exact hτ⟩)
  exact Quotient.sound (orbitRel_apply.mpr
    (SubMulAction.mem_orbit_subMul_iff.mpr ⟨⟨g, hmem⟩, hg⟩))

end Subgroup

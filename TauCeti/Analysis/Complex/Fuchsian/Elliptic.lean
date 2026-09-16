/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Stabilizer
public import TauCeti.Analysis.Complex.RootsOfUnityQuotient
public import TauCeti.Topology.MetricSpace.ProperlyDiscontinuous

/-!
# The elliptic disc of a point of the upper half-plane

Let `Γ ≤ PSL(2, ℝ)` be a subgroup and `z` a point of the upper half-plane. The stabilizer of `z`
in `Γ` acts by hyperbolic isometries fixing `z`, so it preserves every hyperbolic disc
`TauCeti.stabilizerBall Γ z ε` about `z`. If `Γ` is discrete, then for small `ε` no other element
of `Γ` moves that disc to meet itself (`TauCeti.exists_ball_disjoint_smul_of_notMem_stabilizer`),
so near `z` the orbit space of `Γ` is the orbit space of the disc under the single finite group
`MulAction.stabilizer Γ z`.

That orbit space is computed here. In the disc coordinate centred at `z` the stabilizer acts by
the group of `m`-th roots of unity, `m` its order
(`Subgroup.stabilizerRotationEquiv`, `Subgroup.discCoordinate_smul_eq_rotation_smul`), and the
disc of hyperbolic radius `ε` becomes the Euclidean disc of radius `tanh (ε / 2)`
(`UpperHalfPlane.image_discCoordinate_ball`). The orbit map of a rotation group of order `m` on a
disc is `u ↦ u ^ m` (`TauCeti.rootsOfUnityBallQuotientHomeomorph`), so the orbit space is again a
disc, with coordinate `(disc coordinate) ^ m`. This is the local model at an elliptic point: the
quotient is smooth there, and the quotient map has multiplicity `m`.

## Main declarations

* `TauCeti.stabilizerBall`: the hyperbolic disc about `z`, as a set invariant under the
  stabilizer of `z`.
* `TauCeti.stabilizerBallHomeomorph`: the disc coordinate, as a homeomorphism from that disc onto
  a Euclidean disc, equivariant for `Subgroup.stabilizerRotationEquiv`.
* `TauCeti.stabilizerBallQuotientHomeomorph`: the orbit space of the invariant disc under the
  stabilizer is the Euclidean disc of radius `tanh (ε / 2) ^ m`, with coordinate the `m`-th power
  of the disc coordinate.

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

open Metric MulAction UpperHalfPlane

open scoped MatrixGroups Pointwise

namespace TauCeti

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
`TauCeti.stabilizerBallHomeomorph_smul`. -/
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

/-- **The elliptic disc chart.** The orbit space of the invariant hyperbolic disc of radius
`ε > 0` about `z` under the stabilizer of `z`, a group of order `m`, is the Euclidean disc of
radius `tanh (ε / 2) ^ m`; the identification sends the orbit of `τ` to the `m`-th power of its
disc coordinate. The radius is positive so that the source really is a chart about `z`: it
contains `z` itself (`TauCeti.mem_stabilizerBall`), and the target contains `0`. For a discrete
`Γ` and a small enough `ε` this orbit space is a neighbourhood of the image of `z` in the orbit
space of `Γ`, by `TauCeti.exists_ball_disjoint_smul_of_notMem_stabilizer`. -/
def stabilizerBallQuotientHomeomorph [Finite (stabilizer Γ z)] (hε : 0 < ε) :
    orbitRel.Quotient (stabilizer Γ z) (stabilizerBall Γ z ε) ≃ₜ
      ball (0 : ℂ) (Real.tanh (ε / 2) ^ Nat.card (stabilizer Γ z)) :=
  (Homeomorph.Quotient.congr (stabilizerBallHomeomorph Γ z ε)
      (orbitRel_stabilizerBall_iff Γ z ε)).trans
    (rootsOfUnityBallQuotientHomeomorph (r := Real.tanh (ε / 2)) (by
      rw [← Real.tanh_zero]
      exact Real.tanh_strictMono.monotone (by linarith)))

@[simp]
theorem coe_stabilizerBallQuotientHomeomorph_mk [Finite (stabilizer Γ z)] (hε : 0 < ε)
    (τ : stabilizerBall Γ z ε) :
    (stabilizerBallQuotientHomeomorph Γ z ε hε (Quotient.mk _ τ) : ℂ) =
      discCoordinate z τ ^ Nat.card (stabilizer Γ z) := by
  have hcongr :
      Homeomorph.Quotient.congr (stabilizerBallHomeomorph Γ z ε)
          (orbitRel_stabilizerBall_iff Γ z ε) (Quotient.mk _ τ) =
        Quotient.mk _ (stabilizerBallHomeomorph Γ z ε τ) :=
    rfl
  rw [stabilizerBallQuotientHomeomorph, Homeomorph.trans_apply, hcongr,
    coe_rootsOfUnityBallQuotientHomeomorph_mk, coe_stabilizerBallHomeomorph]

end TauCeti

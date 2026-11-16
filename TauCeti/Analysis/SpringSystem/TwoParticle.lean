/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RepresentationTheory.Equiv
public import TauCeti.Algebra.MonoidAlgebra.CyclicTwo
public import TauCeti.Analysis.SpringSystem.Basic
public import TauCeti.Data.ZMod.MonoidHomEquiv
public import TauCeti.RepresentationTheory.GroupAlgebra.CharIdempotent
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Two particles on a spring: symmetry, normal modes, and the failure of the linearization

Two particles rest at `p₁ = (0, 0)` and `p₂ = (1, 0)` in the plane, joined by a spring of
stiffness `κ` and rest length `1`. Displacing them by `u₁` and `u₂` changes the relative vector to
`(1, 0) + u₂ - u₁`, and the exact force on the first particle is
`TauCeti.springForce κ 1 ((1, 0) + u₂ - u₁)`, the second particle feeling its opposite. The
declarations specific to this example live in the namespace `TauCeti.TwoParticleSpring`.

**The linearization.** In the coordinate order `(x₁, y₁, x₂, y₂)` the exact force on the two
particles (`TauCeti.TwoParticleSpring.exactForce`) has derivative `u ↦ κ H u` at the rest
configuration, with `H = TauCeti.TwoParticleSpring.forceMatrix`
(`TauCeti.TwoParticleSpring.hasFDerivAt_exactForce_zero`): only the stretching of the spring along
the rest direction is felt to first order. Its eigenvectors are the stretching mode
`(1, 0, -1, 0)`, of eigenvalue `-2`, the two translations `(1, 0, 1, 0)` and `(0, 1, 0, 1)` and
the transverse mode `(0, 1, 0, -1)`, all three of eigenvalue `0`.

**The symmetry.** The reflection `r` in the axis `y = 0` of the spring
(`TauCeti.TwoParticleSpring.axisReflection`, the matrix `diag(1, -1, 1, -1)`) and the reflection
`s` in its perpendicular bisector `x = 1/2` (`TauCeti.TwoParticleSpring.bisectorReflection`, which
exchanges the particles) are commuting involutions, so `C₂ × C₂` acts on displacements
(`TauCeti.TwoParticleSpring.symmetryRep`) and `H` commutes with this action. The four eigenvectors
above have the `(r, s)`-signs `(+, +)`, `(+, -)`, `(-, +)` and `(-, -)` respectively, so each of
the four real characters of `C₂ × C₂` occurs exactly once: the displacement representation is the
regular representation (`TauCeti.TwoParticleSpring.leftRegularEquiv`), and the joint eigenspace of
each character is exactly the line through its eigenvector. Each symmetry preserves the dot
product. The character idempotent `¼ ∑_g χ(g) g` of each character `χ` acts as the orthogonal
projection onto the corresponding eigenvector line (`TauCeti.TwoParticleSpring.isotypicProjector`);
the four projectors are idempotent, symmetric for the dot product, annihilate each other pairwise
and sum to the identity, and `H` is `-2` times the projector of the trivial character.

**The transverse zero mode, made exact.** Along the transverse displacement `u₁ = (0, ε)`,
`u₂ = (0, -ε)` the relative vector is `(1, -2ε)`, of length
`ℓ(ε) = √(1 + 4ε²)` (`TauCeti.TwoParticleSpring.transverseLength`), and the exact potential is

`E(ε) = (κ / 2) (ℓ(ε) - 1)² = 8 κ ε⁴ / (ℓ(ε) + 1)²`

(`TauCeti.TwoParticleSpring.transverseEnergy`, `TauCeti.TwoParticleSpring.transverseEnergy_eq_div`).
It vanishes at `ε = 0` to fourth order: `E(0) = E'(0) = E''(0) = 0`, yet `E(ε) > 0` for `ε ≠ 0`,
and `E(ε) / ε⁴ → 2κ` (`TauCeti.TwoParticleSpring.transverseEnergy_quartic`). The exact force on
the first particle is `κ (1 - 1/ℓ(ε)) (1, -2ε)`. It vanishes to first order at `ε = 0`, as the
linearization predicts, but its first coordinate is positive for `ε ≠ 0`. Hence the affine paths
`u₁(t) = (0, a t)`, `u₂(t) = (0, -a t)` with `a ≠ 0`, which solve the linearized equation because
`H` annihilates them, fail the exact Newton equation at every `t ≠ 0` and for every mass
(`TauCeti.TwoParticleSpring.mass_smul_deriv_deriv_ne_springForce_transverse`): their acceleration
is zero and the exact force is not.

The zero eigenvalue on the transverse mode is instead the tangent of a curve of rest
configurations: the clockwise rotations by `2ε`, `p₁(ε) = (½ - ½ cos 2ε, ½ sin 2ε)` and
`p₂(ε) = (½ + ½ cos 2ε, -½ sin 2ε)`, of the rest configuration about its midpoint keep the
particles at distance `1`, so they store no energy, and their velocity at `ε = 0` is
`(0, 1, 0, -1)` (`TauCeti.TwoParticleSpring.hasDerivAt_rotatedRestFirst_zero`,
`TauCeti.TwoParticleSpring.hasDerivAt_rotatedRestSecond_zero`). These are configuration curves,
not solutions of the spring equation.

## Main definitions

* `TauCeti.TwoParticleSpring.forceMatrix`: the linearized force matrix `H`.
* `TauCeti.TwoParticleSpring.exactForce`: the exact force on the two particles, in coordinates.
* `TauCeti.TwoParticleSpring.axisReflection`, `TauCeti.TwoParticleSpring.bisectorReflection`: the
  two reflections `r` and `s`.
* `TauCeti.TwoParticleSpring.symmetryRep`: the representation of `C₂ × C₂` on displacements.
* `TauCeti.TwoParticleSpring.leftRegularEquiv`: its isomorphism with the regular representation.
* `TauCeti.TwoParticleSpring.isotypicProjector`: the action of the character idempotent of a real
  character of `C₂ × C₂`.
* `TauCeti.TwoParticleSpring.transverseLength`, `TauCeti.TwoParticleSpring.transverseEnergy`: the
  exact length and potential along the transverse displacement.
* `TauCeti.TwoParticleSpring.rotatedRestFirst`, `TauCeti.TwoParticleSpring.rotatedRestSecond`: the
  rotated rest configurations.

## Main results

* `TauCeti.TwoParticleSpring.hasFDerivAt_exactForce_zero`,
  `TauCeti.TwoParticleSpring.hasFDerivAt_inv_smul_exactForce_zero`: the exact force linearizes to
  `κ H` at the rest configuration, and the acceleration of particles of mass `m` to `(κ / m) H`.
* `TauCeti.TwoParticleSpring.forceMatrix_mulVec_symmetryRep`: `H` is equivariant, and
  `TauCeti.TwoParticleSpring.dotProduct_symmetryRep`: the action is orthogonal, so
  `TauCeti.TwoParticleSpring.symmetryRep_dotProduct`: each symmetry is symmetric for the dot
  product.
* `TauCeti.TwoParticleSpring.symmetryRep_stretch` and its three companions: the symmetry type of
  each eigenvector of `H`.
* `TauCeti.TwoParticleSpring.isotypicProjector_one_apply` and its three companions: the
  projectors are the orthogonal projections onto the eigenvector lines, and
  `TauCeti.TwoParticleSpring.isotypicProjector_add_add_add_eq_one`: they sum to the identity.
* `TauCeti.TwoParticleSpring.isotypicProjector_dotProduct`: the projectors are symmetric for the
  dot product.
* `TauCeti.TwoParticleSpring.isotypicProjector_mul_self`,
  `TauCeti.TwoParticleSpring.isotypicProjector_mul_isotypicProjector_of_ne`: the projectors are
  idempotent and those of distinct characters annihilate each other.
* `TauCeti.TwoParticleSpring.mem_iInf_eigenspace_symmetryRep_iff`: a displacement lies in the
  isotypic component of `χ` exactly when the two reflections act on it by the values of `χ`.
* `TauCeti.TwoParticleSpring.range_isotypicProjector`: the image of each projector is its isotypic
  component, and `TauCeti.TwoParticleSpring.iInf_eigenspace_symmetryRep_one` and its three
  companions: the four isotypic components are exactly the eigenvector lines.
* `TauCeti.TwoParticleSpring.toLin'_forceMatrix`: `H = -2 P`, with `P` the projector of the
  trivial character.
* `TauCeti.TwoParticleSpring.springPotential_transverse`,
  `TauCeti.TwoParticleSpring.springForce_transverse`: the exact potential and force along the
  transverse displacement.
* `TauCeti.TwoParticleSpring.hasDerivAt_springForce_transverse_zero`: that force vanishes to first
  order at `0`, as `H` predicts.
* `TauCeti.TwoParticleSpring.transverseEnergy_eq_div`: the closed form
  `E(ε) = 8 κ ε⁴ / (ℓ(ε) + 1)²`.
* `TauCeti.TwoParticleSpring.deriv_transverseEnergy_zero`,
  `TauCeti.TwoParticleSpring.deriv_deriv_transverseEnergy_zero`,
  `TauCeti.TwoParticleSpring.transverseEnergy_pos`: the potential vanishes to second order at `0`
  but is positive elsewhere.
* `TauCeti.TwoParticleSpring.transverseEnergy_quartic`: `E(ε) / ε⁴ → 2κ` as `ε → 0`, `ε ≠ 0`, and
  `TauCeti.TwoParticleSpring.transverseEnergy_div_pow_four_lt`: the quotient stays below `2κ`.
* `TauCeti.TwoParticleSpring.mass_smul_deriv_deriv_ne_springForce_transverse`: the affine
  transverse paths are not solutions of the exact equation of motion.

## References

* A. Knutson, *Group theory in physics: an example*, notes for Math 261 (Cornell, 2001),
  pp. 1–3 (the two-particle spring, its `C₂ × C₂` symmetry, and the limitation of the linear
  approximation). The handout prints the labels `r = 1`, `s = -1` for the vertical translation
  `(0, 1, 0, 1)`; the axis reflection reverses it, so its signs are `r = -1`, `s = 1`.
-/

public section

namespace TauCeti.TwoParticleSpring

open Real Filter Topology Matrix

/-! ### The linearized force matrix -/

/-- The **force matrix** `H` of the linearized system of two particles at `(0, 0)` and `(1, 0)`
joined by a spring of stiffness `κ` and rest length `1`, in the coordinate order
`(x₁, y₁, x₂, y₂)`: the linearized force is `κ H u`
(`TauCeti.TwoParticleSpring.hasFDerivAt_exactForce_zero`), in which only the stretching `x₂ - x₁`
along the rest direction is felt. Along the transverse mode `(0, 1, 0, -1)` this first-order
vanishing of the exact force is
`TauCeti.TwoParticleSpring.hasDerivAt_springForce_transverse_zero`. -/
def forceMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1, 0, 1, 0; 0, 0, 0, 0; 1, 0, -1, 0; 0, 0, 0, 0]

theorem forceMatrix_def :
    forceMatrix = !![-1, 0, 1, 0; 0, 0, 0, 0; 1, 0, -1, 0; 0, 0, 0, 0] :=
  (rfl)

/-- The stretching mode `(1, 0, -1, 0)` is an eigenvector of `H` of eigenvalue `-2`. -/
theorem forceMatrix_mulVec_stretch :
    forceMatrix *ᵥ ![1, 0, -1, 0] = ![-2, 0, 2, 0] := by
  ext i
  fin_cases i <;> simp [forceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
    norm_num

/-- The horizontal translation `(1, 0, 1, 0)` is a zero mode of `H`. -/
theorem forceMatrix_mulVec_translation_x :
    forceMatrix *ᵥ ![1, 0, 1, 0] = 0 := by
  ext i
  fin_cases i <;> simp [forceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The vertical translation `(0, 1, 0, 1)` is a zero mode of `H`. -/
theorem forceMatrix_mulVec_translation_y :
    forceMatrix *ᵥ ![0, 1, 0, 1] = 0 := by
  ext i
  fin_cases i <;> simp [forceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The transverse displacement `(0, ε, 0, -ε)` is a zero mode of `H`. -/
theorem forceMatrix_mulVec_transverse (ε : ℝ) :
    forceMatrix *ᵥ ![0, ε, 0, -ε] = 0 := by
  ext i
  fin_cases i <;> simp [forceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-! ### `H` is the linearization of the exact force -/

/-- The **exact force** on the two particles at the displacement `u = (x₁, y₁, x₂, y₂)`, in the same
coordinate order: the force `F = springForce κ 1 ((1, 0) + u₂ - u₁)` on the first particle,
followed by the opposite force `-F` on the second. -/
noncomputable def exactForce (κ : ℝ) (u : Fin 4 → ℝ) : Fin 4 → ℝ :=
  let F := springForce κ 1 (!₂[1, 0] + !₂[u 2, u 3] - !₂[u 0, u 1] : EuclideanSpace ℝ (Fin 2))
  ![F 0, F 1, -F 0, -F 1]

theorem exactForce_def (κ : ℝ) (u : Fin 4 → ℝ) :
    exactForce κ u =
      let F := springForce κ 1 (!₂[1, 0] + !₂[u 2, u 3] - !₂[u 0, u 1] : EuclideanSpace ℝ (Fin 2))
      ![F 0, F 1, -F 0, -F 1] :=
  (rfl)

/-- The rest configuration is an equilibrium: the exact force vanishes at `u = 0`. -/
@[simp]
theorem exactForce_zero (κ : ℝ) : exactForce κ 0 = 0 := by
  have h : (!₂[1, 0] + !₂[0, 0] - !₂[0, 0] : EuclideanSpace ℝ (Fin 2)) = !₂[1, 0] := by
    ext i
    fin_cases i <;> simp
  have hn : ‖(!₂[1, 0] : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  ext i
  fin_cases i <;> simp [exactForce_def, h, springForce_def, hn]

/-- **`H` is the linearization of the exact force**: the exact force on the two particles has
derivative `u ↦ κ H u` at the rest configuration `u = 0`. This is the pair-force linearization
`TauCeti.hasFDerivAt_springForce_add_sub` for the rest vector `(1, 0)`, whose projection keeps
only the stretching `x₂ - x₁`. -/
theorem hasFDerivAt_exactForce_zero (κ : ℝ) :
    HasFDerivAt (exactForce κ) (κ • (Matrix.toLin' forceMatrix).toContinuousLinearMap)
      0 := by
  have hv : (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) ≠ 0 := fun h ↦ by simpa using congr($h 0)
  have hn : ‖(!₂[1, 0] : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  -- the positions of the two particles, as a linear function of the coordinates
  let L : (Fin 4 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) :=
    LinearMap.toContinuousLinearMap
      { toFun u := (!₂[u 0, u 1], !₂[u 2, u 3])
        map_add' u w := by ext i <;> fin_cases i <;> simp
        map_smul' c u := by ext i <;> fin_cases i <;> simp }
  have hp := hasFDerivAt_springForce_add_sub κ hv
  rw [← map_zero L, hn] at hp
  have hF := hp.comp (0 : Fin 4 → ℝ) L.hasFDerivAt
  refine hasFDerivAt_pi'.2 fun i ↦ ?_
  -- each coordinate of the exact force is `±` a coordinate of the force on the first particle
  fin_cases i <;> [
    convert (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt.comp 0 hF using 1;
    convert (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt.comp 0 hF using 1;
    convert ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt.comp 0 hF).neg using 1;
    convert ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt.comp 0 hF).neg using 1] <;>
  first
    | funext u
      simp [exactForce_def, L]
    | ext u
      simp [L, forceMatrix, Submodule.starProjection_singleton, dotProduct, Fin.sum_univ_four,
        PiLp.inner_apply, Fin.sum_univ_two, hn, neg_add_eq_sub, ← sub_eq_add_neg, ← mul_neg]

/-- **The linearized equation of motion.** For particles of equal mass `m`, the acceleration
`m⁻¹ • exactForce κ u` has derivative `u ↦ (κ / m) H u` at the rest configuration. -/
theorem hasFDerivAt_inv_smul_exactForce_zero (κ m : ℝ) :
    HasFDerivAt (fun u ↦ m⁻¹ • exactForce κ u)
      ((κ / m) • (Matrix.toLin' forceMatrix).toContinuousLinearMap) 0 := by
  simpa [smul_smul, div_eq_inv_mul] using (hasFDerivAt_exactForce_zero κ).const_smul m⁻¹

/-! ### The exact length and potential along the transverse displacement -/

/-- The exact length `ℓ(ε) = √(1 + 4ε²)` of the spring at the transverse displacement
`u₁ = (0, ε)`, `u₂ = (0, -ε)`, with rest length `1`. -/
noncomputable def transverseLength (ε : ℝ) : ℝ :=
  √(1 + 4 * ε ^ 2)

/-- The exact potential `E(ε) = (κ / 2) (ℓ(ε) - 1)²` of the transverse displacement
`u₁ = (0, ε)`, `u₂ = (0, -ε)`, for a spring of stiffness `κ` and rest length `1`. -/
noncomputable def transverseEnergy (κ ε : ℝ) : ℝ :=
  κ / 2 * (transverseLength ε - 1) ^ 2

theorem transverseLength_def (ε : ℝ) : transverseLength ε = √(1 + 4 * ε ^ 2) :=
  (rfl)

theorem transverseEnergy_def (κ ε : ℝ) :
    transverseEnergy κ ε = κ / 2 * (transverseLength ε - 1) ^ 2 :=
  (rfl)

@[simp]
theorem transverseLength_zero : transverseLength 0 = 1 := by
  simp [transverseLength_def]

theorem sq_transverseLength (ε : ℝ) : transverseLength ε ^ 2 = 1 + 4 * ε ^ 2 :=
  sq_sqrt (by positivity)

theorem one_le_transverseLength (ε : ℝ) : 1 ≤ transverseLength ε :=
  one_le_sqrt.mpr (by nlinarith [sq_nonneg ε])

theorem one_lt_transverseLength {ε : ℝ} (hε : ε ≠ 0) : 1 < transverseLength ε :=
  lt_sqrt zero_le_one |>.mpr (by nlinarith [sq_pos_of_ne_zero hε])

theorem transverseLength_pos (ε : ℝ) : 0 < transverseLength ε :=
  zero_lt_one.trans_le (one_le_transverseLength ε)

theorem inv_transverseLength_lt_one {ε : ℝ} (hε : ε ≠ 0) : (transverseLength ε)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (one_lt_transverseLength hε)

theorem hasDerivAt_transverseLength (ε : ℝ) :
    HasDerivAt transverseLength (4 * ε / transverseLength ε) ε := by
  have h : HasDerivAt (fun x : ℝ ↦ 1 + 4 * x ^ 2) (8 * ε) ε := by
    convert ((hasDerivAt_pow 2 ε).const_mul (4 : ℝ)).const_add 1 using 1
    push_cast
    ring
  rw [show transverseLength = fun x ↦ √(1 + 4 * x ^ 2) from funext transverseLength_def]
  convert h.sqrt (by positivity) using 1
  field_simp [(transverseLength_pos ε).ne']
  ring

/-- The factor `1 - 1/ℓ(ε)` of the exact force has derivative `0` at `ε = 0`. -/
theorem hasDerivAt_one_sub_inv_transverseLength_zero :
    HasDerivAt (fun ε ↦ 1 - (transverseLength ε)⁻¹) 0 0 := by
  simpa using ((hasDerivAt_transverseLength 0).inv (transverseLength_pos 0).ne').const_sub 1

/-- The relative vector of the transverse displacement is `(1, -2ε)`. -/
private theorem transverse_relative (ε : ℝ) :
    !₂[1, 0] + !₂[0, -ε] - !₂[0, ε] = (!₂[1, -2 * ε] : EuclideanSpace ℝ (Fin 2)) := by
  ext i
  fin_cases i <;> simp [two_mul, sub_eq_add_neg]

private theorem norm_transverse_relative (ε : ℝ) :
    ‖(!₂[1, -2 * ε] : EuclideanSpace ℝ (Fin 2))‖ = transverseLength ε := by
  rw [EuclideanSpace.norm_eq, transverseLength_def]
  congr 1
  simp only [norm_eq_abs, sq_abs, Fin.sum_univ_two, cons_val_zero, one_pow, cons_val_one,
    cons_val_fin_one]
  ring

/-- The exact potential of the transverse displacement `u₁ = (0, ε)`, `u₂ = (0, -ε)` is
`TauCeti.TwoParticleSpring.transverseEnergy κ ε`. -/
theorem springPotential_transverse (κ ε : ℝ) :
    springPotential κ 1 (!₂[1, 0] + !₂[0, -ε] - !₂[0, ε] : EuclideanSpace ℝ (Fin 2)) =
      transverseEnergy κ ε := by
  rw [transverse_relative, springPotential_def, norm_transverse_relative, transverseEnergy_def]

/-- The exact force on the first particle at the transverse displacement `u₁ = (0, ε)`,
`u₂ = (0, -ε)` is `κ (1 - 1/ℓ(ε)) (1, -2ε)`. -/
theorem springForce_transverse (κ ε : ℝ) :
    springForce κ 1 (!₂[1, 0] + !₂[0, -ε] - !₂[0, ε] : EuclideanSpace ℝ (Fin 2)) =
      (κ * (1 - (transverseLength ε)⁻¹)) • !₂[1, -2 * ε] := by
  rw [transverse_relative, springForce_def, norm_transverse_relative]
  congr 1
  field_simp [(transverseLength_pos ε).ne']

/-- Away from `ε = 0` the first coordinate of the exact force on the first particle is positive:
the stretched spring pulls it towards the second particle. -/
theorem springForce_transverse_apply_zero_pos {κ ε : ℝ} (hκ : 0 < κ) (hε : ε ≠ 0) :
    0 < springForce κ 1 (!₂[1, 0] + !₂[0, -ε] - !₂[0, ε] : EuclideanSpace ℝ (Fin 2)) 0 := by
  rw [springForce_transverse]
  simp only [PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one]
  exact mul_pos hκ (sub_pos.mpr (inv_transverseLength_lt_one hε))

/-- **To first order the transverse displacement feels no force**: the exact force on the first
particle along `u₁ = (0, ε)`, `u₂ = (0, -ε)` has derivative `0` at `ε = 0`, in accordance with
`H (0, 1, 0, -1) = 0` (`TauCeti.TwoParticleSpring.forceMatrix_mulVec_transverse`). -/
theorem hasDerivAt_springForce_transverse_zero (κ : ℝ) :
    HasDerivAt (fun ε : ℝ ↦
      springForce κ 1 (!₂[1, 0] + !₂[0, -ε] - !₂[0, ε] : EuclideanSpace ℝ (Fin 2))) 0 0 := by
  simp_rw [springForce_transverse]
  have hc : HasDerivAt (fun ε ↦ κ * (1 - (transverseLength ε)⁻¹)) 0 0 := by
    simpa using hasDerivAt_one_sub_inv_transverseLength_zero.const_mul κ
  have hv : HasDerivAt (fun ε : ℝ ↦ (!₂[1, -2 * ε] : EuclideanSpace ℝ (Fin 2))) !₂[0, -2] 0 := by
    have h := ((hasDerivAt_id' (0 : ℝ)).smul_const (!₂[0, -2] : EuclideanSpace ℝ (Fin 2))).const_add
      (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))
    convert h using 1
    · funext ε
      ext i
      fin_cases i <;> simp [mul_comm]
    · simp
  simpa using hc.fun_smul hv

/-! ### The potential vanishes to fourth order -/

/-- The **closed form** `E(ε) = 8 κ ε⁴ / (ℓ(ε) + 1)²`, from `(ℓ - 1)(ℓ + 1) = ℓ² - 1 = 4ε²`. -/
theorem transverseEnergy_eq_div (κ ε : ℝ) :
    transverseEnergy κ ε = 8 * κ * ε ^ 4 / (transverseLength ε + 1) ^ 2 := by
  have h := sq_transverseLength ε
  have hpos : transverseLength ε + 1 ≠ 0 := by linarith [transverseLength_pos ε]
  rw [transverseEnergy_def, eq_div_iff (pow_ne_zero 2 hpos)]
  linear_combination (κ / 2 * (transverseLength ε ^ 2 - 1 + 4 * ε ^ 2)) * h

@[simp]
theorem transverseEnergy_zero (κ : ℝ) : transverseEnergy κ 0 = 0 := by
  simp [transverseEnergy_def]

/-- The transverse displacement costs positive energy away from `ε = 0`. -/
theorem transverseEnergy_pos {κ ε : ℝ} (hκ : 0 < κ) (hε : ε ≠ 0) : 0 < transverseEnergy κ ε := by
  rw [transverseEnergy_eq_div]
  have := transverseLength_pos ε
  positivity

/-- The derivative `E'(ε) = 4 κ ε (1 - 1/ℓ(ε))`. -/
theorem hasDerivAt_transverseEnergy (κ ε : ℝ) :
    HasDerivAt (transverseEnergy κ) (4 * κ * ε * (1 - (transverseLength ε)⁻¹)) ε := by
  rw [show transverseEnergy κ = fun x ↦ κ / 2 * (transverseLength x - 1) ^ 2 from
    funext (transverseEnergy_def κ)]
  convert (((hasDerivAt_transverseLength ε).sub_const 1).fun_pow 2).const_mul (κ / 2) using 1
  field_simp [(transverseLength_pos ε).ne']
  ring

theorem deriv_transverseEnergy (κ : ℝ) :
    deriv (transverseEnergy κ) = fun ε ↦ 4 * κ * ε * (1 - (transverseLength ε)⁻¹) :=
  funext fun ε ↦ (hasDerivAt_transverseEnergy κ ε).deriv

/-- `E'(0) = 0`. -/
theorem deriv_transverseEnergy_zero (κ : ℝ) : deriv (transverseEnergy κ) 0 = 0 := by
  simp [deriv_transverseEnergy]

/-- `E''(0) = 0`: the transverse displacement is a zero mode of the linearization. -/
theorem deriv_deriv_transverseEnergy_zero (κ : ℝ) :
    deriv (deriv (transverseEnergy κ)) 0 = 0 := by
  rw [deriv_transverseEnergy]
  have h := ((hasDerivAt_id' (0 : ℝ)).const_mul (4 * κ)).fun_mul
    hasDerivAt_one_sub_inv_transverseLength_zero
  simpa using h.deriv

/-- Away from `ε = 0`, `E(ε) / ε⁴ = 8κ / (ℓ(ε) + 1)²`. -/
theorem transverseEnergy_div_pow_four (κ : ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    transverseEnergy κ ε / ε ^ 4 = 8 * κ / (transverseLength ε + 1) ^ 2 := by
  have hpos : transverseLength ε + 1 ≠ 0 := by linarith [transverseLength_pos ε]
  rw [transverseEnergy_eq_div]
  field_simp

/-- Away from `ε = 0` the quotient `E(ε) / ε⁴ = 8κ / (ℓ(ε) + 1)²` lies below its limit `2κ`,
because `ℓ(ε) > 1`. At `ε = 1/2`, for instance, it is `8κ / (√2 + 1)²`. -/
theorem transverseEnergy_div_pow_four_lt {κ ε : ℝ} (hκ : 0 < κ) (hε : ε ≠ 0) :
    transverseEnergy κ ε / ε ^ 4 < 2 * κ := by
  have hl := one_lt_transverseLength hε
  rw [transverseEnergy_div_pow_four κ hε, div_lt_iff₀ (by positivity)]
  nlinarith [mul_pos hκ (by nlinarith : (0 : ℝ) < (transverseLength ε + 1) ^ 2 - 4)]

/-- **The quartic leading term.** `E(ε) / ε⁴ → 2κ` as `ε → 0` through `ε ≠ 0`: the linearized
force vanishes on the transverse mode while the exact potential is quartic, which is the
limitation of the linear approximation. The puncture is necessary, since the quotient is `0` at
`ε = 0`. -/
theorem transverseEnergy_quartic (κ : ℝ) :
    Tendsto (fun ε : ℝ ↦ transverseEnergy κ ε / ε ^ 4) (𝓝[≠] 0) (𝓝 (2 * κ)) := by
  have hl : Tendsto (fun ε ↦ (transverseLength ε + 1) ^ 2) (𝓝 0) (𝓝 4) := by
    have := ((hasDerivAt_transverseLength 0).continuousAt.tendsto.add_const 1).pow 2
    norm_num at this
    exact this
  have hcont : Tendsto (fun ε ↦ 8 * κ / (transverseLength ε + 1) ^ 2) (𝓝 0) (𝓝 (2 * κ)) := by
    convert tendsto_const_nhds.div hl four_ne_zero using 2
    ring
  refine (hcont.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (transverseEnergy_div_pow_four κ hε).symm

/-! ### The affine transverse paths are not solutions -/

/-- **The linearization fails on the transverse zero mode.** For `κ ≠ 0` and `a ≠ 0`, the affine
paths `u₁(t) = (0, a t)`, `u₂(t) = (0, -a t)` solve the linearized equation of motion, as `H`
annihilates them (`TauCeti.TwoParticleSpring.forceMatrix_mulVec_transverse`), but at every
`t ≠ 0` and for every mass `m` they violate the exact Newton equation `m u₁'' = F₁` of the first
particle: their acceleration is zero, while the exact force is not. -/
theorem mass_smul_deriv_deriv_ne_springForce_transverse {κ a t : ℝ} (hκ : κ ≠ 0) (ha : a ≠ 0)
    (ht : t ≠ 0) (m : ℝ) :
    m • deriv (deriv fun s : ℝ ↦ (!₂[0, a * s] : EuclideanSpace ℝ (Fin 2))) t ≠
      springForce κ 1 (!₂[1, 0] + !₂[0, -(a * t)] - !₂[0, a * t] : EuclideanSpace ℝ (Fin 2)) := by
  have hpath : (fun s : ℝ ↦ (!₂[0, a * s] : EuclideanSpace ℝ (Fin 2))) =
      fun s ↦ s • !₂[0, a] := by
    funext s
    ext i
    fin_cases i <;> simp [mul_comm]
  have hvel : deriv (fun s : ℝ ↦ (!₂[0, a * s] : EuclideanSpace ℝ (Fin 2))) = fun _ ↦ !₂[0, a] :=
    funext fun s ↦ by rw [hpath]; exact ((hasDerivAt_id' s).smul_const _).deriv.trans (one_smul _ _)
  rw [hvel, deriv_const, smul_zero, springForce_transverse]
  intro h
  have h0 := congr($h 0)
  simp only [PiLp.zero_apply, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one] at h0
  exact mul_ne_zero hκ (sub_ne_zero.mpr
    (inv_transverseLength_lt_one (mul_ne_zero ha ht)).ne') h0.symm

/-! ### The rotated rest configurations -/

/-- The first particle of the rest configuration rotated clockwise by `2ε` about its midpoint
`(½, 0)`: `p₁(ε) = (½ - ½ cos 2ε, ½ sin 2ε)`. -/
noncomputable def rotatedRestFirst (ε : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[1 / 2 - cos (2 * ε) / 2, sin (2 * ε) / 2]

/-- The second particle of the rest configuration rotated clockwise by `2ε` about its midpoint
`(½, 0)`: `p₂(ε) = (½ + ½ cos 2ε, -½ sin 2ε)`. -/
noncomputable def rotatedRestSecond (ε : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[1 / 2 + cos (2 * ε) / 2, -(sin (2 * ε) / 2)]

theorem rotatedRestFirst_def (ε : ℝ) :
    rotatedRestFirst ε = !₂[1 / 2 - cos (2 * ε) / 2, sin (2 * ε) / 2] :=
  (rfl)

theorem rotatedRestSecond_def (ε : ℝ) :
    rotatedRestSecond ε = !₂[1 / 2 + cos (2 * ε) / 2, -(sin (2 * ε) / 2)] :=
  (rfl)

@[simp]
theorem rotatedRestFirst_zero : rotatedRestFirst 0 = !₂[0, 0] := by
  ext i
  fin_cases i <;> norm_num [rotatedRestFirst_def]

@[simp]
theorem rotatedRestSecond_zero : rotatedRestSecond 0 = !₂[1, 0] := by
  ext i
  fin_cases i <;> norm_num [rotatedRestSecond_def]

/-- The rotated particles stay at distance `1`. -/
theorem norm_rotatedRestSecond_sub_rotatedRestFirst (ε : ℝ) :
    ‖rotatedRestSecond ε - rotatedRestFirst ε‖ = 1 := by
  rw [EuclideanSpace.norm_eq, sqrt_eq_one]
  simp only [rotatedRestSecond_def, rotatedRestFirst_def, PiLp.sub_apply, norm_eq_abs, sq_abs,
    Fin.sum_univ_two, cons_val_zero, cons_val_one, cons_val_fin_one]
  nlinarith [sin_sq_add_cos_sq (2 * ε)]

/-- The rotated rest configurations store no energy. Their displacements from the rest
configuration are `uᵢ = pᵢ(ε) - pᵢ(0)`, so their relative vector `(1, 0) + u₂ - u₁` is
`p₂(ε) - p₁(ε)`. -/
theorem springPotential_rotatedRest (κ ε : ℝ) :
    springPotential κ 1 (rotatedRestSecond ε - rotatedRestFirst ε) = 0 := by
  simp [springPotential_def, norm_rotatedRestSecond_sub_rotatedRestFirst]

theorem hasDerivAt_rotatedRestFirst (ε : ℝ) :
    HasDerivAt rotatedRestFirst !₂[sin (2 * ε), cos (2 * ε)] ε := by
  have h2 := (hasDerivAt_id' ε).const_mul (2 : ℝ)
  have h := ((h2.cos.div_const 2).const_sub (1 / 2)).smul_const
      (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) |>.add ((h2.sin.div_const 2).smul_const
      (!₂[0, 1] : EuclideanSpace ℝ (Fin 2)))
  convert h using 1
  · funext x
    ext i
    fin_cases i <;> simp [rotatedRestFirst_def]
  · ext i
    fin_cases i <;> simp [neg_div]

theorem hasDerivAt_rotatedRestSecond (ε : ℝ) :
    HasDerivAt rotatedRestSecond !₂[-sin (2 * ε), -cos (2 * ε)] ε := by
  have h2 := (hasDerivAt_id' ε).const_mul (2 : ℝ)
  have h := ((h2.cos.div_const 2).const_add (1 / 2)).smul_const
      (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) |>.add ((h2.sin.div_const 2).neg.smul_const
      (!₂[0, 1] : EuclideanSpace ℝ (Fin 2)))
  convert h using 1
  · funext x
    ext i
    fin_cases i <;> simp [rotatedRestSecond_def]
  · ext i
    fin_cases i <;> simp [neg_div]

/-- At `ε = 0` the first rotated particle moves with velocity `(0, 1)`, the velocity of the first
particle along the transverse mode `(0, 1, 0, -1)`. -/
theorem hasDerivAt_rotatedRestFirst_zero : HasDerivAt rotatedRestFirst !₂[0, 1] 0 := by
  simpa using hasDerivAt_rotatedRestFirst 0

/-- At `ε = 0` the second rotated particle moves with velocity `(0, -1)`, the velocity of the
second particle along the transverse mode `(0, 1, 0, -1)`. -/
theorem hasDerivAt_rotatedRestSecond_zero : HasDerivAt rotatedRestSecond !₂[0, -1] 0 := by
  simpa using hasDerivAt_rotatedRestSecond 0

/-! ### The symmetry group `C₂ × C₂` -/

/-- The **reflection in the axis** `y = 0` of the spring, through both rest positions: it fixes
both particles and reverses their vertical displacements, acting on `(x₁, y₁, x₂, y₂)` by the
matrix `diag(1, -1, 1, -1)`. -/
noncomputable def axisReflection : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  have h : toLin' (diagonal ![(1 : ℝ), -1, 1, -1]) ∘ₗ toLin' (diagonal ![1, -1, 1, -1]) = .id := by
    rw [← toLin'_mul, diagonal_mul_diagonal, ← toLin'_one, ← diagonal_one]
    congr 2
    ext i
    fin_cases i <;> simp
  .ofLinearMap _ _ h h

/-- The axis reflection in coordinates, `r (x₁, y₁, x₂, y₂) = (x₁, -y₁, x₂, -y₂)`. -/
@[simp]
theorem axisReflection_apply (u : Fin 4 → ℝ) :
    axisReflection u = ![u 0, -u 1, u 2, -u 3] := by
  ext i
  fin_cases i <;> simp [axisReflection, mulVec_diagonal]

/-- The matrix of the axis reflection is `diag(1, -1, 1, -1)`. -/
theorem toMatrix'_axisReflection :
    LinearMap.toMatrix' (axisReflection : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ) =
      diagonal ![1, -1, 1, -1] :=
  LinearMap.toMatrix'_toLin' _

/-- The **reflection in the perpendicular bisector** `x = 1/2` of the spring: it exchanges the two
particles and reverses horizontal displacements, acting on `(x₁, y₁, x₂, y₂)` by the matrix
`[[0, 0, -1, 0], [0, 0, 0, 1], [-1, 0, 0, 0], [0, 1, 0, 0]]`. -/
noncomputable def bisectorReflection : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  have h : toLin' !![(0 : ℝ), 0, -1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, 1, 0, 0] ∘ₗ
      toLin' !![0, 0, -1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, 1, 0, 0] = .id := by
    rw [← toLin'_mul, ← toLin'_one]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  .ofLinearMap _ _ h h

/-- The bisector reflection in coordinates, `s (x₁, y₁, x₂, y₂) = (-x₂, y₂, -x₁, y₁)`. -/
@[simp]
theorem bisectorReflection_apply (u : Fin 4 → ℝ) :
    bisectorReflection u = ![-u 2, u 3, -u 0, u 1] := by
  ext i
  fin_cases i <;> simp [bisectorReflection, mulVec, dotProduct, Fin.sum_univ_four]

/-- The matrix of the bisector reflection. -/
theorem toMatrix'_bisectorReflection :
    LinearMap.toMatrix' (bisectorReflection : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ) =
      !![0, 0, -1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, 1, 0, 0] :=
  LinearMap.toMatrix'_toLin' _

/-- The axis reflection is an involution. -/
theorem axisReflection_sq : axisReflection ^ 2 = 1 := by
  ext u i
  fin_cases i <;> simp [pow_two]

/-- The bisector reflection is an involution. -/
theorem bisectorReflection_sq : bisectorReflection ^ 2 = 1 := by
  ext u i
  fin_cases i <;> simp [pow_two]

/-- The two reflections commute; their product is the half-turn about the midpoint `(1/2, 0)`. -/
theorem commute_axisReflection_bisectorReflection :
    Commute axisReflection bisectorReflection := by
  rw [commute_iff_eq]
  ext u i
  fin_cases i <;> simp

/-- The **representation of `C₂ × C₂` on the displacements** of the two particles: the generator
`(Multiplicative.ofAdd 1, 1)` acts by the axis reflection and `(1, Multiplicative.ofAdd 1)` by the
bisector reflection. -/
noncomputable def symmetryRep :
    Representation ℝ (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) (Fin 4 → ℝ) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp <|
    MonoidHom.noncommCoprod
      ((zmodMonoidHomEquiv 2 _).symm ⟨axisReflection, axisReflection_sq⟩)
      ((zmodMonoidHomEquiv 2 _).symm ⟨bisectorReflection, bisectorReflection_sq⟩)
      fun a b ↦ by
        rw [← ofAdd_toAdd a, ← ofAdd_toAdd b, zmodMonoidHomEquiv_symm_apply,
          zmodMonoidHomEquiv_symm_apply]
        exact commute_axisReflection_bisectorReflection.pow_pow _ _

/-- The first generator of `C₂ × C₂` acts by the axis reflection. -/
@[simp]
theorem symmetryRep_ofAdd_one_one_apply (u : Fin 4 → ℝ) :
    symmetryRep (.ofAdd 1, 1) u = axisReflection u := by
  simp [symmetryRep, MonoidHom.noncommCoprod_apply, ZMod.val_one]

/-- The second generator of `C₂ × C₂` acts by the bisector reflection. -/
@[simp]
theorem symmetryRep_one_ofAdd_one_apply (u : Fin 4 → ℝ) :
    symmetryRep (1, .ofAdd 1) u = bisectorReflection u := by
  simp [symmetryRep, MonoidHom.noncommCoprod_apply, ZMod.val_one]

/-- The product of the two generators acts by the half-turn, the composite of the two
reflections. -/
@[simp]
theorem symmetryRep_ofAdd_one_ofAdd_one_apply (u : Fin 4 → ℝ) :
    symmetryRep (.ofAdd 1, .ofAdd 1) u = axisReflection (bisectorReflection u) := by
  simp [symmetryRep, MonoidHom.noncommCoprod_apply, ZMod.val_one]

/-- **`H` is equivariant**: the linearized force commutes with the symmetries of the spring. -/
theorem forceMatrix_mulVec_symmetryRep (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
    (u : Fin 4 → ℝ) :
    forceMatrix *ᵥ symmetryRep g u = symmetryRep g (forceMatrix *ᵥ u) := by
  obtain ⟨a, b⟩ := g
  rcases a.eq_one_or_eq_ofAdd_one with rfl | rfl <;>
    rcases b.eq_one_or_eq_ofAdd_one with rfl | rfl <;>
    · ext i
      fin_cases i <;>
        simp [forceMatrix, mulVec, dotProduct, Fin.sum_univ_four, Prod.mk_one_one]

/-- **The action is orthogonal**: every symmetry preserves the standard dot product of
displacements. -/
theorem dotProduct_symmetryRep (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
    (u v : Fin 4 → ℝ) :
    symmetryRep g u ⬝ᵥ symmetryRep g v = u ⬝ᵥ v := by
  obtain ⟨a, b⟩ := g
  rcases a.eq_one_or_eq_ofAdd_one with rfl | rfl <;>
    rcases b.eq_one_or_eq_ofAdd_one with rfl | rfl <;>
    simp [dotProduct, Fin.sum_univ_four, Prod.mk_one_one] <;> ring

/-- **Each symmetry is symmetric for the dot product**: an involution preserving the dot product,
it is its own adjoint. -/
theorem symmetryRep_dotProduct (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
    (u w : Fin 4 → ℝ) : symmetryRep g u ⬝ᵥ w = u ⬝ᵥ symmetryRep g w := by
  obtain ⟨a, b⟩ := g
  rcases a.eq_one_or_eq_ofAdd_one with rfl | rfl <;>
    rcases b.eq_one_or_eq_ofAdd_one with rfl | rfl <;>
    simp [Prod.mk_one_one, dotProduct, Fin.sum_univ_four] <;> ring

/-! ### The four symmetry types of displacement -/

/-- The stretching mode `(1, 0, -1, 0)` is fixed by both reflections: it spans a copy of the
trivial character of `C₂ × C₂`. -/
theorem symmetryRep_stretch (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    symmetryRep g ![1, 0, -1, 0] = ![1, 0, -1, 0] := by
  obtain ⟨a, b⟩ := g
  rcases a.eq_one_or_eq_ofAdd_one with rfl | rfl <;>
    rcases b.eq_one_or_eq_ofAdd_one with rfl | rfl <;>
    · ext i
      fin_cases i <;> simp [Prod.mk_one_one]

/-- The vertical translation `(0, 1, 0, 1)` is reversed by the axis reflection and fixed by the
bisector reflection: `C₂ × C₂` acts on it by the sign of the first factor. -/
theorem symmetryRep_translation_y (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    symmetryRep g ![0, 1, 0, 1] = cyclicTwoSign ℝ g.1 • ![0, 1, 0, 1] := by
  obtain ⟨a, b⟩ := g
  rcases a.eq_one_or_eq_ofAdd_one with rfl | rfl <;>
    rcases b.eq_one_or_eq_ofAdd_one with rfl | rfl <;>
    · ext i
      fin_cases i <;> simp [Prod.mk_one_one]

/-- The horizontal translation `(1, 0, 1, 0)` is fixed by the axis reflection and reversed by the
bisector reflection: `C₂ × C₂` acts on it by the sign of the second factor. -/
theorem symmetryRep_translation_x (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    symmetryRep g ![1, 0, 1, 0] = cyclicTwoSign ℝ g.2 • ![1, 0, 1, 0] := by
  obtain ⟨a, b⟩ := g
  rcases a.eq_one_or_eq_ofAdd_one with rfl | rfl <;>
    rcases b.eq_one_or_eq_ofAdd_one with rfl | rfl <;>
    · ext i
      fin_cases i <;> simp [Prod.mk_one_one]

/-- The transverse mode `(0, 1, 0, -1)` is reversed by both reflections: `C₂ × C₂` acts on it by
the product of the signs of the two factors. -/
theorem symmetryRep_transverse (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    symmetryRep g ![0, 1, 0, -1] =
      (cyclicTwoSign ℝ g.1 * cyclicTwoSign ℝ g.2) • ![0, 1, 0, -1] := by
  obtain ⟨a, b⟩ := g
  rcases a.eq_one_or_eq_ofAdd_one with rfl | rfl <;>
    rcases b.eq_one_or_eq_ofAdd_one with rfl | rfl <;>
    · ext i
      fin_cases i <;> simp [Prod.mk_one_one]

/-! ### The regular representation -/

private theorem bijective_leftRegularMapEquiv_symm :
    Function.Bijective
      ((Representation.leftRegularMapEquiv symmetryRep).symm ![1, 1, 0, 0]) := by
  have hsurj : Function.Surjective
      ((Representation.leftRegularMapEquiv symmetryRep).symm ![1, 1, 0, 0]) := fun u ↦ by
    refine ⟨.single 1 ((u 0 + u 1) / 2) + .single (.ofAdd 1, 1) ((u 0 - u 1) / 2) +
      .single (1, .ofAdd 1) ((u 3 - u 2) / 2) + .single (.ofAdd 1, .ofAdd 1) (-(u 2 + u 3) / 2),
      ?_⟩
    ext i
    fin_cases i <;> simp [Finsupp.sum_add_index', add_smul] <;> ring
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    ((MonoidAlgebra.coeffLinearEquiv ℝ).finrank_eq.trans (by simp))).2 hsurj, hsurj⟩

/-- **The displacements carry the regular representation of `C₂ × C₂`**: the four images
`(1, 1, 0, 0)`, `(1, -1, 0, 0)`, `(0, 0, -1, 1)`, `(0, 0, -1, -1)` of the displacement
`(1, 1, 0, 0)` form a basis, so the intertwining map `δ_g ↦ g • (1, 1, 0, 0)` from the left
regular representation is an isomorphism. -/
noncomputable def leftRegularEquiv :
    (Representation.leftRegular ℝ (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))).Equiv
      symmetryRep :=
  Representation.IntertwiningMap.ofBijective
    ((Representation.leftRegularMapEquiv symmetryRep).symm ![1, 1, 0, 0])
    bijective_leftRegularMapEquiv_symm

/-- The isomorphism from the regular representation sends `c δ_g` to `c (g • (1, 1, 0, 0))`. -/
@[simp]
theorem leftRegularEquiv_single (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) (c : ℝ) :
    leftRegularEquiv (.single g c) = c • symmetryRep g ![1, 1, 0, 0] := by
  rw [leftRegularEquiv, Representation.IntertwiningMap.coe_ofBijective]
  simp

/-! ### The isotypic projectors -/

/-- The **isotypic projector** of a real character `χ` of `C₂ × C₂` on displacements: the action
of the character idempotent `TauCeti.charIdempotent` of `χ`, which is `¼ ∑_g χ(g) g` because
every element of `C₂ × C₂` is its own inverse, so `χ(g⁻¹) = χ(g)`. -/
noncomputable def isotypicProjector
    (χ : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* ℝ) : Module.End ℝ (Fin 4 → ℝ) :=
  symmetryRep.asAlgebraHom (charIdempotent χ.toHomUnits)

/-- The isotypic projector of `χ` written out with the two reflections and their product. -/
theorem isotypicProjector_apply (χ : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* ℝ)
    (u : Fin 4 → ℝ) :
    isotypicProjector χ u = (4 : ℝ)⁻¹ • (u + χ (.ofAdd 1, 1) • axisReflection u +
      χ (1, .ofAdd 1) • bisectorReflection u +
      χ (.ofAdd 1, .ofAdd 1) • axisReflection (bisectorReflection u)) := by
  have hinv : (Multiplicative.ofAdd (1 : ZMod 2))⁻¹ = .ofAdd 1 := by decide
  have hcard : (Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) : ℝ) = 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_multiplicative, ZMod.card]
    norm_num
  rw [isotypicProjector, charIdempotent_eq_sum, hcard, Ring.inverse_eq_inv', map_smul, map_sum]
  simp only [map_smul, Representation.asAlgebraHom_of, ← map_inv, MonoidHom.coe_toHomUnits,
    Fintype.sum_prod_type, sum_cyclicTwo, Prod.inv_mk, inv_one, hinv, Prod.mk_one_one, map_one,
    LinearMap.smul_apply, LinearMap.add_apply, one_apply_eq_self, one_smul,
    symmetryRep_ofAdd_one_one_apply, symmetryRep_one_ofAdd_one_apply,
    symmetryRep_ofAdd_one_ofAdd_one_apply]
  abel_nf

/-- **The isotypic projectors are symmetric for the dot product**, since each symmetry is
(`TauCeti.TwoParticleSpring.symmetryRep_dotProduct`); being idempotent, they are orthogonal
projectors. -/
theorem isotypicProjector_dotProduct
    (χ : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* ℝ) (u w : Fin 4 → ℝ) :
    isotypicProjector χ u ⬝ᵥ w = u ⬝ᵥ isotypicProjector χ w := by
  have hsr : axisReflection (bisectorReflection w) = bisectorReflection (axisReflection w) :=
    congrArg (fun f ↦ f w) commute_axisReflection_bisectorReflection.eq
  rw [isotypicProjector_apply, isotypicProjector_apply, hsr]
  simp only [smul_dotProduct, dotProduct_smul, add_dotProduct, dotProduct_add,
    ← symmetryRep_ofAdd_one_one_apply, ← symmetryRep_one_ofAdd_one_apply, symmetryRep_dotProduct]

/-- A symmetry applied after the isotypic projector of `χ` acts by the scalar `χ g`: the image of
the projector is contained in the `χ`-isotypic component. -/
theorem symmetryRep_mul_isotypicProjector
    (χ : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* ℝ)
    (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    symmetryRep g * isotypicProjector χ = χ g • isotypicProjector χ := by
  rw [isotypicProjector, ← Representation.asAlgebraHom_single_one, ← map_mul,
    single_mul_charIdempotent, MonoidHom.coe_toHomUnits, map_smul]

/-- **The isotypic projectors are idempotent.** -/
@[simp]
theorem isotypicProjector_mul_self (χ : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* ℝ) :
    isotypicProjector χ * isotypicProjector χ = isotypicProjector χ :=
  (isIdempotentElem_charIdempotent χ.toHomUnits).map symmetryRep.asAlgebraHom

/-- **The isotypic projectors of distinct characters annihilate each other.** -/
@[simp]
theorem isotypicProjector_mul_isotypicProjector_of_ne
    {χ ψ : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* ℝ} (h : χ ≠ ψ) :
    isotypicProjector χ * isotypicProjector ψ = 0 := by
  rw [isotypicProjector, isotypicProjector, ← map_mul,
    charIdempotent_mul_charIdempotent_of_ne fun hχψ ↦ h <| MonoidHom.ext fun g ↦ by
      simpa using congrArg Units.val (DFunLike.congr_fun hχψ g),
    map_zero]

/-- The projector of the trivial character is the orthogonal projection
`u ↦ (v ⬝ᵥ u / v ⬝ᵥ v) v` onto the stretching mode `v = (1, 0, -1, 0)`, with `v ⬝ᵥ v = 2`. -/
theorem isotypicProjector_one_apply (u : Fin 4 → ℝ) :
    isotypicProjector 1 u = ((![1, 0, -1, 0] ⬝ᵥ u) / 2) • ![1, 0, -1, 0] := by
  rw [isotypicProjector_apply]
  ext i
  fin_cases i <;> simp [dotProduct, Fin.sum_univ_four, vecHead, vecTail] <;> ring

/-- The projector of the sign character of the first factor is the orthogonal projection onto the
vertical translation `(0, 1, 0, 1)`. -/
theorem isotypicProjector_comp_fst_apply (u : Fin 4 → ℝ) :
    isotypicProjector ((cyclicTwoSign ℝ).comp (MonoidHom.fst _ _)) u =
      ((![0, 1, 0, 1] ⬝ᵥ u) / 2) • ![0, 1, 0, 1] := by
  rw [isotypicProjector_apply]
  ext i
  fin_cases i <;> simp [dotProduct, Fin.sum_univ_four, vecHead, vecTail] <;> ring

/-- The projector of the sign character of the second factor is the orthogonal projection onto
the horizontal translation `(1, 0, 1, 0)`. -/
theorem isotypicProjector_comp_snd_apply (u : Fin 4 → ℝ) :
    isotypicProjector ((cyclicTwoSign ℝ).comp (MonoidHom.snd _ _)) u =
      ((![1, 0, 1, 0] ⬝ᵥ u) / 2) • ![1, 0, 1, 0] := by
  rw [isotypicProjector_apply]
  ext i
  fin_cases i <;> simp [dotProduct, Fin.sum_univ_four, vecHead, vecTail] <;> ring

/-- The projector of the product of the two sign characters is the orthogonal projection onto the
transverse mode `(0, 1, 0, -1)`. -/
theorem isotypicProjector_mul_apply (u : Fin 4 → ℝ) :
    isotypicProjector ((cyclicTwoSign ℝ).comp (MonoidHom.fst _ _) *
        (cyclicTwoSign ℝ).comp (MonoidHom.snd _ _)) u =
      ((![0, 1, 0, -1] ⬝ᵥ u) / 2) • ![0, 1, 0, -1] := by
  rw [isotypicProjector_apply]
  ext i
  fin_cases i <;> simp [dotProduct, Fin.sum_univ_four, vecHead, vecTail] <;> ring

/-- The four isotypic projectors sum to the identity: every displacement is uniquely the sum of
its components along the stretching mode, the two translations and the transverse mode. -/
theorem isotypicProjector_add_add_add_eq_one :
    isotypicProjector 1 + isotypicProjector ((cyclicTwoSign ℝ).comp (MonoidHom.fst _ _)) +
        isotypicProjector ((cyclicTwoSign ℝ).comp (MonoidHom.snd _ _)) +
        isotypicProjector ((cyclicTwoSign ℝ).comp (MonoidHom.fst _ _) *
          (cyclicTwoSign ℝ).comp (MonoidHom.snd _ _)) = 1 := by
  refine LinearMap.ext fun u ↦ funext fun i ↦ ?_
  simp only [LinearMap.add_apply, isotypicProjector_one_apply, isotypicProjector_comp_fst_apply,
    isotypicProjector_comp_snd_apply, isotypicProjector_mul_apply, one_apply_eq_self]
  fin_cases i <;> simp [dotProduct, Fin.sum_univ_four, vecHead, vecTail] <;> ring

/-! ### The isotypic components -/

/-- A displacement lies in the joint eigenspace of a real character `χ` of `C₂ × C₂` exactly when
the two reflections multiply it by the values of `χ` at the two generators. -/
@[grind ←]
theorem mem_iInf_eigenspace_symmetryRep_iff
    (χ : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* ℝ) (u : Fin 4 → ℝ) :
    u ∈ ⨅ g, Module.End.eigenspace (symmetryRep g) (χ g) ↔
      axisReflection u = χ (.ofAdd 1, 1) • u ∧ bisectorReflection u = χ (1, .ofAdd 1) • u := by
  rw [Submodule.mem_iInf]
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hr, hs⟩ g ↦ Module.End.mem_eigenspace_iff.2 ?_⟩
  · simpa using Module.End.mem_eigenspace_iff.1 (h (.ofAdd 1, 1))
  · simpa using Module.End.mem_eigenspace_iff.1 (h (1, .ofAdd 1))
  have hχ : χ (.ofAdd 1, .ofAdd 1) = χ (1, .ofAdd 1) * χ (.ofAdd 1, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, one_mul, mul_one]
  obtain ⟨a, b⟩ := g
  rcases a.eq_one_or_eq_ofAdd_one with rfl | rfl <;>
    rcases b.eq_one_or_eq_ofAdd_one with rfl | rfl
  · simp [Prod.mk_one_one]
  · simpa using hs
  · simpa using hr
  · rw [symmetryRep_ofAdd_one_ofAdd_one_apply, hs, map_smul, hr, smul_smul, hχ]

/-- The image of the isotypic projector of `χ` is the `χ`-isotypic component, the joint eigenspace
on which every symmetry `g` acts by the scalar `χ g`. -/
theorem range_isotypicProjector (χ : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* ℝ) :
    LinearMap.range (isotypicProjector χ) = ⨅ g, Module.End.eigenspace (symmetryRep g) (χ g) :=
  symmetryRep.range_asAlgebraHom_charIdempotent (Nat.cast_ne_zero.2 Nat.card_pos.ne').isUnit
    χ.toHomUnits

/-- The **trivial isotypic component**, on which both reflections act trivially, is the stretching
line through `(1, 0, -1, 0)`. -/
theorem iInf_eigenspace_symmetryRep_one :
    ⨅ g, Module.End.eigenspace (symmetryRep g)
        ((1 : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* ℝ) g) =
      ℝ ∙ ![1, 0, -1, 0] := by
  have hP : isotypicProjector 1 =
      ((2 : ℝ)⁻¹ • dotProductBilin ℝ ℝ ![1, 0, -1, 0]).smulRight ![1, 0, -1, 0] := by
    refine LinearMap.ext fun u ↦ ?_
    simp [isotypicProjector_one_apply, div_eq_inv_mul]
  rw [← range_isotypicProjector, hP]
  apply LinearMap.range_smulRight_apply
  intro h
  have := LinearMap.congr_fun h ![1, 0, -1, 0]
  norm_num [dotProduct, Fin.sum_univ_four] at this

/-- The isotypic component of the sign of the first factor, reversed by the axis reflection and
fixed by the bisector reflection, is the line of vertical translations through `(0, 1, 0, 1)`. -/
theorem iInf_eigenspace_symmetryRep_comp_fst :
    ⨅ g, Module.End.eigenspace (symmetryRep g)
        ((cyclicTwoSign ℝ).comp (MonoidHom.fst _ _) g) = ℝ ∙ ![0, 1, 0, 1] := by
  have hP : isotypicProjector ((cyclicTwoSign ℝ).comp (MonoidHom.fst _ _)) =
      ((2 : ℝ)⁻¹ • dotProductBilin ℝ ℝ ![0, 1, 0, 1]).smulRight ![0, 1, 0, 1] := by
    refine LinearMap.ext fun u ↦ ?_
    simp [isotypicProjector_comp_fst_apply, div_eq_inv_mul]
  rw [← range_isotypicProjector, hP]
  apply LinearMap.range_smulRight_apply
  intro h
  have := LinearMap.congr_fun h ![0, 1, 0, 1]
  norm_num [dotProduct, Fin.sum_univ_four] at this

/-- The isotypic component of the sign of the second factor, fixed by the axis reflection and
reversed by the bisector reflection, is the line of horizontal translations through
`(1, 0, 1, 0)`. -/
theorem iInf_eigenspace_symmetryRep_comp_snd :
    ⨅ g, Module.End.eigenspace (symmetryRep g)
        ((cyclicTwoSign ℝ).comp (MonoidHom.snd _ _) g) = ℝ ∙ ![1, 0, 1, 0] := by
  have hP : isotypicProjector ((cyclicTwoSign ℝ).comp (MonoidHom.snd _ _)) =
      ((2 : ℝ)⁻¹ • dotProductBilin ℝ ℝ ![1, 0, 1, 0]).smulRight ![1, 0, 1, 0] := by
    refine LinearMap.ext fun u ↦ ?_
    simp [isotypicProjector_comp_snd_apply, div_eq_inv_mul]
  rw [← range_isotypicProjector, hP]
  apply LinearMap.range_smulRight_apply
  intro h
  have := LinearMap.congr_fun h ![1, 0, 1, 0]
  norm_num [dotProduct, Fin.sum_univ_four] at this

/-- The isotypic component of the product of the two signs, reversed by both reflections, is the
line of the transverse mode `(0, 1, 0, -1)`. -/
theorem iInf_eigenspace_symmetryRep_mul :
    ⨅ g, Module.End.eigenspace (symmetryRep g)
        (((cyclicTwoSign ℝ).comp (MonoidHom.fst _ _) * (cyclicTwoSign ℝ).comp (MonoidHom.snd _ _) :
          Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* ℝ) g) = ℝ ∙ ![0, 1, 0, -1] := by
  have hP : isotypicProjector ((cyclicTwoSign ℝ).comp (MonoidHom.fst _ _) *
        (cyclicTwoSign ℝ).comp (MonoidHom.snd _ _)) =
      ((2 : ℝ)⁻¹ • dotProductBilin ℝ ℝ ![0, 1, 0, -1]).smulRight ![0, 1, 0, -1] := by
    refine LinearMap.ext fun u ↦ ?_
    simp [isotypicProjector_mul_apply, div_eq_inv_mul]
  rw [← range_isotypicProjector, hP]
  apply LinearMap.range_smulRight_apply
  intro h
  have := LinearMap.congr_fun h ![0, 1, 0, -1]
  norm_num [dotProduct, Fin.sum_univ_four] at this

/-- **The spectral decomposition of `H`**: the force matrix is `-2` times the projector of the
trivial character, so its eigenvalue is `-2` on the stretching mode and `0` on the other three
isotypic lines. -/
theorem toLin'_forceMatrix : toLin' forceMatrix = (-2 : ℝ) • isotypicProjector 1 := by
  refine LinearMap.ext fun u ↦ funext fun i ↦ ?_
  rw [LinearMap.smul_apply, isotypicProjector_one_apply, toLin'_apply]
  fin_cases i <;> simp [forceMatrix, mulVec, dotProduct, Fin.sum_univ_four] <;> ring

end TauCeti.TwoParticleSpring

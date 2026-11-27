/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Polar
public import TauCeti.Geometry.Manifold.Instances.AddCircle.Cover
public import TauCeti.Geometry.Manifold.DifferentialForm.AddCircle
public import TauCeti.Geometry.Symplectic.Manifold.Prod
public import TauCeti.Geometry.Manifold.Instances.Cylinder
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Opens

/-!
# Smooth global polar canonical coordinates

Let `b` be an orthonormal basis of a real inner product plane `V`. The polar canonical
parametrization `(r, p_r, θ, L) ↦ (r e_r, p_r e_r + (L / r) e_θ)` of
`TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Polar` is `2π`-periodic in `θ`, so it
descends to the actual circle of angles `AddCircle (2 * π)`, with its quotient smooth structure:

`(ℝ × ℝ) × (AddCircle (2 * π) × ℝ) → V × V` (`TauCeti.polarCylinderMap`).

On the open set `r > 0` (`TauCeti.polarCanonicalCylinder`) this map is a diffeomorphism onto the
punctured phase space `{(q, p) | q ≠ 0}` (`TauCeti.polarCanonicalDiffeomorph`), whose inverse sends
`(q, p)` to its length `‖q‖`, its radial momentum `⟪q, p⟫ / ‖q‖`, the circle-valued polar angle of
`q` and its angular momentum. These are global canonical coordinates, including across the angle
seam: the diffeomorphism pulls the standard symplectic form `ω₀ = Σ dqᵢ ∧ dpᵢ` back to the product
form `dr ∧ dp_r + dθ ∧ dL`, where `dθ` is the time form of the period-`2π` circle
(`TauCeti.mpullback_polarCanonicalDiffeomorph`), and the Liouville form `⟪p, dq⟫` back to
`p_r dr + L dθ` (`TauCeti.inner_snd_polarCanonicalDiffeomorph_mfderiv_fst`). In them a central-force
Hamiltonian is `p_r² / (2m) + U_L(r)`, with the effective potential `U_L`
(`TauCeti.centralForceHamiltonian_polarCanonicalDiffeomorph`).

The position component of these coordinates only involves `(r, θ)`: it is the diffeomorphism
`(r, θ) ↦ r e_r` of the half-cylinder `(0, ∞) × (ℝ / 2πℤ)` onto the punctured plane `V ∖ {0}`
(`TauCeti.polarPlaneDiffeomorph`, `TauCeti.fst_polarCanonicalDiffeomorph`), with inverse
`q ↦ (‖q‖, θ(q))`. Together with the pullback of the Liouville form, this says that `p_r` and `L`
are the momenta conjugate to `r` and `θ`: the values of the covector `p` on the coordinate vectors
`∂_r q` and `∂_θ q`.

## Main definitions

* `TauCeti.polarCylinderMap u w`: the polar canonical parametrization on the circle of angles.
* `TauCeti.polarCanonicalCylinder`: its domain `r > 0`, an open subset of
  `(ℝ × ℝ) × (AddCircle (2 * π) × ℝ)`.
* `TauCeti.polarCanonicalDiffeomorph b`: global smooth polar canonical coordinates, a
  diffeomorphism from `polarCanonicalCylinder` onto the punctured phase space.
* `TauCeti.polarPlaneDiffeomorph b`: smooth polar coordinates `(r, θ) ↦ r e_r` from the
  half-cylinder `TauCeti.polarHalfCylinder` onto the punctured plane.

## Main results

* `TauCeti.contMDiffOn_polarCylinderMap`, `TauCeti.isLocalDiffeomorphAt_polarCylinderMap`: the
  parametrization is smooth on `r ≠ 0` and a local diffeomorphism there.
* `TauCeti.coe_polarCanonicalDiffeomorph_symm_apply`: the inverse coordinates.
* `TauCeti.mpullback_polarCanonicalDiffeomorph`: `ω₀ = dr ∧ dp_r + dθ ∧ dL`.
* `TauCeti.mpullback_stdSymplecticForm_of_angularMomentum_eq`: on a level of the angular momentum,
  `ω₀` pulls back to `dr ∧ dp_r` along the radial projection.
* `TauCeti.inner_snd_polarCanonicalDiffeomorph_mfderiv_fst`: `⟪p, dq⟫ = p_r dr + L dθ`.
* `TauCeti.centralForceHamiltonian_polarCanonicalDiffeomorph`: `H = p_r² / (2m) + U_L(r)`.
* `TauCeti.fst_polarCanonicalDiffeomorph`: the coordinates cover the polar coordinates of the
  plane.
* `TauCeti.isLocalDiffeomorphAt_smul_polarRadialUnit`: polar coordinates `(r, θ) ↦ r e_r` with a
  real angle are a local diffeomorphism on `r > 0`.

The descent along the quotient map `ℝ → AddCircle (2 * π)` and the passage from a bijective local
diffeomorphism to a global diffeomorphism follow the oscillator action-angle coordinates of
`TauCeti.Geometry.Symplectic.Hamiltonian.Oscillator.Coordinates`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 8 (motion in a central field, in polar coordinates).
-/

public noncomputable section

open Set Function Real TopologicalSpace
open scoped Manifold ContDiff InnerProductSpace

namespace TauCeti

local instance centralForceCoordinatesTwoPiPos : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### The parametrization on the circle of angles -/

/-- The polar canonical parametrization is `2π`-periodic in the angle. -/
theorem periodic_polarCanonical (u w : V) (rp : ℝ × ℝ) (L : ℝ) :
    Periodic (fun θ ↦ polarCanonical u w (rp, (θ, L))) (2 * π) := fun θ ↦
  polarCanonical_eq_of_coe_eq u w (by rw [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero])
    rp.1 rp.2 L

/-- The **polar canonical parametrization on the circle of angles** `AddCircle (2 * π)`: the
descent of `(r, p_r, θ, L) ↦ (r e_r, p_r e_r + (L / r) e_θ)` along `θ ↦ θ mod 2π`. -/
def polarCylinderMap (u w : V) (x : (ℝ × ℝ) × (AddCircle (2 * π) × ℝ)) : V × V :=
  (periodic_polarCanonical u w x.1 x.2.2).lift x.2.1

/-- On a real lift of the angle, the parametrization on the circle is the polar canonical
parametrization. -/
@[simp]
theorem polarCylinderMap_coe (u w : V) (rp : ℝ × ℝ) (θ L : ℝ) :
    polarCylinderMap u w (rp, ((θ : AddCircle (2 * π)), L)) = polarCanonical u w (rp, (θ, L)) :=
  (periodic_polarCanonical u w rp L).lift_coe θ

/-- The domain `r > 0` of global polar canonical coordinates, an open subset of
`(ℝ × ℝ) × (AddCircle (2 * π) × ℝ)` with coordinates `((r, p_r), (θ, L))`. -/
def polarCanonicalCylinder : Opens ((ℝ × ℝ) × (AddCircle (2 * π) × ℝ)) :=
  ⟨{x | 0 < x.1.1}, isOpen_lt continuous_const (continuous_fst.comp continuous_fst)⟩

@[simp]
theorem mem_polarCanonicalCylinder {x : (ℝ × ℝ) × (AddCircle (2 * π) × ℝ)} :
    x ∈ polarCanonicalCylinder ↔ 0 < x.1.1 :=
  Iff.rfl

/-- The quotient map `((r, p_r), (θ, L)) ↦ ((r, p_r), (θ mod 2π, L))` onto the cylinder. -/
private def polarCover : (ℝ × ℝ) × (ℝ × ℝ) → (ℝ × ℝ) × (AddCircle (2 * π) × ℝ) :=
  Prod.map id (Prod.map ((↑) : ℝ → AddCircle (2 * π)) id)

private theorem polarCylinderMap_comp_polarCover (u w : V) :
    polarCylinderMap u w ∘ polarCover = polarCanonical u w :=
  funext fun x ↦ polarCylinderMap_coe u w x.1 x.2.1 x.2.2

/-- The quotient map onto the cylinder is a local diffeomorphism. -/
private theorem isLocalDiffeomorph_polarCover :
    IsLocalDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × (ℝ × ℝ)) (𝓘(ℝ, ℝ × ℝ).prod (𝓘(ℝ).prod 𝓘(ℝ))) ∞
      polarCover := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact (Diffeomorph.refl 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ∞).isLocalDiffeomorph.prodMap
    (AddCircle.isLocalDiffeomorph_prodMap_coe_id (2 * π) ∞)

/-- The quotient map onto the cylinder has derivative the identity in the real tangent
coordinates. -/
private theorem mfderiv_polarCover (x : (ℝ × ℝ) × (ℝ × ℝ)) :
    mfderiv 𝓘(ℝ, (ℝ × ℝ) × (ℝ × ℝ)) (𝓘(ℝ, ℝ × ℝ).prod (𝓘(ℝ).prod 𝓘(ℝ))) polarCover x =
      ContinuousLinearMap.id ℝ ((ℝ × ℝ) × (ℝ × ℝ)) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  rw [polarCover, mfderiv_prodMap mdifferentiableAt_id
    ((AddCircle.isLocalDiffeomorph_prodMap_coe_id (2 * π) ∞ x.2).mdifferentiableAt (by simp)),
    mfderiv_id, AddCircle.mfderiv_prodMap_coe_id]
  -- The product tangent model is `(ℝ × ℝ) × (ℝ × ℝ)`; both factor derivatives are identities.
  rfl

/-- The parametrization on the circle of angles is smooth at every point with `r ≠ 0`. -/
theorem contMDiffAt_polarCylinderMap (u w : V) {x : (ℝ × ℝ) × (AddCircle (2 * π) × ℝ)}
    (hr : x.1.1 ≠ 0) :
    ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod (𝓘(ℝ).prod 𝓘(ℝ))) 𝓘(ℝ, V × V) ∞ (polarCylinderMap u w) x := by
  obtain ⟨rp, a, L⟩ := x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective a
  have hs := contDiffAt_polarCanonical u w (n := ∞) (x := (rp, (θ, L))) hr
  exact ((isLocalDiffeomorph_polarCover (rp, (θ, L))).contMDiffAt_comp_iff le_rfl).1
    (by rw [polarCylinderMap_comp_polarCover]; exact hs.contMDiffAt)

/-- The parametrization on the circle of angles is smooth on `r ≠ 0`. -/
theorem contMDiffOn_polarCylinderMap (u w : V) :
    ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod (𝓘(ℝ).prod 𝓘(ℝ))) 𝓘(ℝ, V × V) ∞ (polarCylinderMap u w)
      {x | x.1.1 ≠ 0} :=
  fun _ hr ↦ (contMDiffAt_polarCylinderMap u w hr).contMDiffWithinAt

/-- The differential of the parametrization on the circle, read at a real lift of the angle, is
the derivative of the polar canonical parametrization. -/
theorem mfderiv_polarCylinderMap_coe (u w : V) {rp : ℝ × ℝ} (θ L : ℝ) (hr : rp.1 ≠ 0) :
    mfderiv (𝓘(ℝ, ℝ × ℝ).prod (𝓘(ℝ).prod 𝓘(ℝ))) 𝓘(ℝ, V × V) (polarCylinderMap u w)
        (rp, ((θ : AddCircle (2 * π)), L)) = fderiv ℝ (polarCanonical u w) (rp, (θ, L)) := by
  have hf := (contMDiffAt_polarCylinderMap u w (x := (rp, ((θ : AddCircle (2 * π)), L)))
    hr).mdifferentiableAt (by simp)
  have h := mfderiv_comp (rp, (θ, L)) hf
    ((isLocalDiffeomorph_polarCover (rp, (θ, L))).mdifferentiableAt (by simp))
  rw [polarCylinderMap_comp_polarCover, mfderiv_polarCover] at h
  ext v
  -- Both tangent spaces are read in the real coordinates `(ℝ × ℝ) × (ℝ × ℝ)`, where the
  -- derivative of the quotient map is the identity.
  exact (DFunLike.congr_fun h v).symm.trans (DFunLike.congr_fun (mfderiv_eq_fderiv (𝕜 := ℝ)
    (f := polarCanonical u w) (x := (rp, (θ, L)))) v)

/-! ### Local and global diffeomorphism -/

section Basis

variable (b : OrthonormalBasis (Fin 2) ℝ V)

/-- At a point with `r ≠ 0`, the polar canonical parametrization over a plane is a local
diffeomorphism. -/
theorem isLocalDiffeomorphAt_polarCanonical {x : (ℝ × ℝ) × (ℝ × ℝ)} (hr : x.1.1 ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, (ℝ × ℝ) × (ℝ × ℝ)) 𝓘(ℝ, V × V) ∞ (polarCanonical (b 0) (b 1)) x := by
  let e := (LinearEquiv.ofBijective (fderiv ℝ (polarCanonical (b 0) (b 1)) x).toLinearMap
    (bijective_fderiv_polarCanonical b hr)).toContinuousLinearEquiv
  have hs : IsOpen {x : (ℝ × ℝ) × (ℝ × ℝ) | x.1.1 ≠ 0} :=
    isOpen_ne_fun (continuous_fst.comp continuous_fst) continuous_const
  refine isLocalDiffeomorphAt_of_mfderiv_eq
    (fun y hy ↦ (contDiffAt_polarCanonical (b 0) (b 1) hy).contMDiffAt.contMDiffWithinAt) hs hr
    BoundarylessManifold.isInteriorPoint (by simp)
    (e := (NormedSpace.fromTangentSpace x).trans
      (e.trans (NormedSpace.fromTangentSpace (polarCanonical (b 0) (b 1) x)).symm)) ?_
  rw [mfderiv_eq_fderiv]
  -- The self-model tangent equivalences act as identities; `ofBijective` retains the derivative.
  rfl

/-- On `r ≠ 0`, the parametrization on the circle of angles is a local diffeomorphism, including
across the angle seam. -/
theorem isLocalDiffeomorphAt_polarCylinderMap {y : (ℝ × ℝ) × (AddCircle (2 * π) × ℝ)}
    (hy : y.1.1 ≠ 0) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℝ × ℝ).prod (𝓘(ℝ).prod 𝓘(ℝ))) 𝓘(ℝ, V × V) ∞
      (polarCylinderMap (b 0) (b 1)) y := by
  obtain ⟨rp, a, L⟩ := y
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective a
  have hf := isLocalDiffeomorphAt_polarCanonical b (x := (rp, (θ, L))) hy
  rw [← polarCylinderMap_comp_polarCover] at hf
  exact hf.of_comp_right (isLocalDiffeomorph_polarCover (rp, (θ, L)))

/-- The polar canonical coordinates `((‖q‖, p_r), (θ, L))` of a phase point `(q, p)`, with the
radial momentum `p_r`, the circle-valued polar angle `θ` and the angular momentum `L`. -/
private def polarCanonicalCoords (x : V × V) : (ℝ × ℝ) × (AddCircle (2 * π) × ℝ) :=
  ((‖x.1‖, radialMomentum x),
    (((polarAngle (b 0) (b 1) x.1).toReal : ℝ), angularMomentum (b 0) (b 1) x))

private theorem polarCanonicalCoords_polarCylinderMap {y : (ℝ × ℝ) × (AddCircle (2 * π) × ℝ)}
    (hy : y ∈ polarCanonicalCylinder) :
    polarCanonicalCoords b (polarCylinderMap (b 0) (b 1) y) = y := by
  obtain ⟨⟨r, pᵣ⟩, a, L⟩ := y
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective a
  have h0 := b.norm_eq_one 0
  have h1 := b.norm_eq_one 1
  have h01 : ⟪b 0, b 1⟫_ℝ = 0 := b.inner_eq_zero (by decide)
  have hr : 0 < ((r, pᵣ), (θ, L)).1.1 := mem_polarCanonicalCylinder.1 hy
  simp only [polarCanonicalCoords, polarCylinderMap_coe, norm_fst_polarCanonical h0 h1 h01,
    abs_of_pos hr, radialMomentum_polarCanonical h0 h1 h01 hr,
    polarAngle_polarCanonical h0 h1 h01 hr, angularMomentum_polarCanonical h0 h1 h01 hr.ne',
    Prod.mk.injEq, and_true, true_and]
  -- `Real.Angle` is `AddCircle (2 * π)` and the two real coercions agree definitionally.
  exact Real.Angle.coe_toReal (θ : Real.Angle)

private theorem polarCylinderMap_polarCanonicalCoords {x : V × V} (hx : x.1 ≠ 0) :
    polarCylinderMap (b 0) (b 1) (polarCanonicalCoords b x) = x := by
  rw [polarCanonicalCoords, polarCylinderMap_coe]
  exact polarCanonical_polarAngle b x.2 hx (Real.Angle.coe_toReal _)

/-- The position of the point with polar canonical coordinates `((r, p_r), (θ, L))`, `r > 0`, has
length `r`. -/
theorem norm_fst_polarCylinderMap {y : (ℝ × ℝ) × (AddCircle (2 * π) × ℝ)}
    (hy : y ∈ polarCanonicalCylinder) : ‖(polarCylinderMap (b 0) (b 1) y).1‖ = y.1.1 :=
  congrArg (fun z ↦ z.1.1) (polarCanonicalCoords_polarCylinderMap b hy)

/-- The parametrization on the circle of angles, from the cylinder `r > 0` to the punctured phase
space. -/
private def polarCanonicalCoordinates (y : polarCanonicalCylinder) : puncturedPhaseSpace V :=
  ⟨polarCylinderMap (b 0) (b 1) y, by
    rw [mem_puncturedPhaseSpace, ← norm_ne_zero_iff, norm_fst_polarCylinderMap b y.property]
    exact (mem_polarCanonicalCylinder.1 y.property).ne'⟩

private theorem bijective_polarCanonicalCoordinates : Bijective (polarCanonicalCoordinates b) := by
  refine ⟨fun y z hyz ↦ Subtype.ext ?_, fun x ↦ ⟨⟨polarCanonicalCoords b x, ?_⟩, ?_⟩⟩
  · rw [← polarCanonicalCoords_polarCylinderMap b y.property,
      ← polarCanonicalCoords_polarCylinderMap b z.property]
    exact congrArg (fun x : puncturedPhaseSpace V ↦ polarCanonicalCoords b x) hyz
  · exact mem_polarCanonicalCylinder.2 (norm_pos_iff.2 (mem_puncturedPhaseSpace.1 x.property))
  · exact Subtype.ext
      (polarCylinderMap_polarCanonicalCoords b (mem_puncturedPhaseSpace.1 x.property))

private theorem isLocalDiffeomorph_polarCanonicalCoordinates :
    IsLocalDiffeomorph (𝓘(ℝ, ℝ × ℝ).prod (𝓘(ℝ).prod 𝓘(ℝ))) 𝓘(ℝ, V × V) ∞
      (polarCanonicalCoordinates b) := by
  intro y
  have hf : IsLocalDiffeomorphAt (𝓘(ℝ, ℝ × ℝ).prod (𝓘(ℝ).prod 𝓘(ℝ))) 𝓘(ℝ, V × V) ∞
      (Subtype.val ∘ polarCanonicalCoordinates b) y :=
    (isLocalDiffeomorph_subtype_val (U := polarCanonicalCylinder) (n := ∞) y).comp
      (hg := isLocalDiffeomorphAt_polarCylinderMap b (mem_polarCanonicalCylinder.1 y.property).ne')
  exact hf.of_comp_left (isLocalDiffeomorph_subtype_val (U := puncturedPhaseSpace V) _)
    ((Topology.IsInducing.subtypeVal.continuousAt_iff).mpr hf.contMDiffAt.continuousAt)

/-- **Global smooth polar canonical coordinates.** For an orthonormal basis `b` of a plane `V`, the
polar canonical parametrization `((r, p_r), (θ, L)) ↦ (r e_r, p_r e_r + (L / r) e_θ)`, with the
angle `θ` in the circle `AddCircle (2 * π)`, is a diffeomorphism from the cylinder `r > 0` onto the
punctured phase space `{(q, p) | q ≠ 0}`. -/
def polarCanonicalDiffeomorph :
    polarCanonicalCylinder ≃ₘ⟮𝓘(ℝ, ℝ × ℝ).prod (𝓘(ℝ).prod 𝓘(ℝ)), 𝓘(ℝ, V × V)⟯
      puncturedPhaseSpace V :=
  (isLocalDiffeomorph_polarCanonicalCoordinates b).diffeomorphOfBijective
    (bijective_polarCanonicalCoordinates b)

/-- The polar canonical diffeomorphism is the parametrization on the circle of angles. -/
@[simp]
theorem coe_polarCanonicalDiffeomorph_apply (y : polarCanonicalCylinder) :
    (polarCanonicalDiffeomorph b y : V × V) = polarCylinderMap (b 0) (b 1) y := by
  simp [polarCanonicalDiffeomorph, polarCanonicalCoordinates]

/-- **The inverse polar canonical coordinates.** The coordinates of `(q, p)`, `q ≠ 0`, are its
length `‖q‖`, its radial momentum `⟪q, p⟫ / ‖q‖`, its polar angle modulo `2π` and its angular
momentum `q₁ p₂ - q₂ p₁` in the basis `b`. -/
@[simp]
theorem coe_polarCanonicalDiffeomorph_symm_apply (x : puncturedPhaseSpace V) :
    ((polarCanonicalDiffeomorph b).symm x : (ℝ × ℝ) × (AddCircle (2 * π) × ℝ)) =
      ((‖x.val.1‖, radialMomentum x.val),
        ((((polarAngle (b 0) (b 1) x.val.1).toReal : ℝ) : AddCircle (2 * π)),
          angularMomentum (b 0) (b 1) x.val)) := by
  have h := polarCanonicalCoords_polarCylinderMap b ((polarCanonicalDiffeomorph b).symm x).property
  rw [← coe_polarCanonicalDiffeomorph_apply, Diffeomorph.apply_symm_apply] at h
  simpa only [polarCanonicalCoords] using h.symm

/-! ### The canonical structures in global polar coordinates -/

/-- The differential of the parametrization on the cylinder `r > 0`, read at a real lift of the
angle, is the derivative of the polar canonical parametrization. -/
private theorem mfderiv_polarCylinderMap_subtype_apply {rp : ℝ × ℝ} (θ L : ℝ)
    (hr : (rp, ((θ : AddCircle (2 * π)), L)) ∈ polarCanonicalCylinder)
    (v : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod (𝓘(ℝ).prod 𝓘(ℝ)))
      (⟨(rp, ((θ : AddCircle (2 * π)), L)), hr⟩ : polarCanonicalCylinder)) :
    mfderiv (𝓘(ℝ, ℝ × ℝ).prod (𝓘(ℝ).prod 𝓘(ℝ))) 𝓘(ℝ, V × V)
        (fun z : polarCanonicalCylinder ↦ (polarCanonicalDiffeomorph b z : V × V))
        ⟨(rp, ((θ : AddCircle (2 * π)), L)), hr⟩ v =
      fderiv ℝ (polarCanonical (b 0) (b 1)) (rp, (θ, L)) v := by
  have hr' : rp.1 ≠ 0 := (mem_polarCanonicalCylinder.1 hr).ne'
  have hcoe : (fun z : polarCanonicalCylinder ↦ (polarCanonicalDiffeomorph b z : V × V)) =
      polarCylinderMap (b 0) (b 1) ∘ Subtype.val :=
    funext (coe_polarCanonicalDiffeomorph_apply b)
  rw [hcoe]
  exact (Manifold.mfderiv_comp_subtype_val_apply v).trans
    (DFunLike.congr_fun (mfderiv_polarCylinderMap_coe (b 0) (b 1) θ L hr') v)

/-- **The Liouville form in global polar coordinates is `p_r dr + L dθ`.** The polar canonical
diffeomorphism pulls the Liouville form `⟪p, dq⟫` of `V × V` back to the one-form sending a tangent
vector `((δr, δp_r), (δθ, δL))` at `((r, p_r), (θ, L))` to `p_r δr + L δθ`. -/
theorem inner_snd_polarCanonicalDiffeomorph_mfderiv_fst (y : polarCanonicalCylinder)
    (v : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod (𝓘(ℝ).prod 𝓘(ℝ))) y) :
    ⟪(polarCanonicalDiffeomorph b y : V × V).2,
        (mfderiv (𝓘(ℝ, ℝ × ℝ).prod (𝓘(ℝ).prod 𝓘(ℝ))) 𝓘(ℝ, V × V)
          (fun z : polarCanonicalCylinder ↦ (polarCanonicalDiffeomorph b z : V × V)) y v).1⟫_ℝ =
      (y : (ℝ × ℝ) × (AddCircle (2 * π) × ℝ)).1.2 * v.1.1 +
        (y : (ℝ × ℝ) × (AddCircle (2 * π) × ℝ)).2.2 * v.2.1 := by
  obtain ⟨⟨rp, a, L⟩, hr⟩ := y
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [mfderiv_polarCylinderMap_subtype_apply b θ L hr, coe_polarCanonicalDiffeomorph_apply,
    polarCylinderMap_coe]
  exact inner_snd_polarCanonical_fderiv_fst (b.norm_eq_one 0) (b.norm_eq_one 1)
    (b.inner_eq_zero (by decide)) (x := (rp, (θ, L))) (mem_polarCanonicalCylinder.1 hr).ne' v

/-- **The central-force Hamiltonian in global polar coordinates.** At the point with coordinates
`((r, p_r), (θ, L))`, the energy `‖p‖² / (2m) + U(‖q‖)` is `p_r² / (2m) + U_L(r)`, with the
effective potential `U_L(r) = L² / (2 m r²) + U(r)`. -/
theorem centralForceHamiltonian_polarCanonicalDiffeomorph (m : ℝ) (U : ℝ → ℝ)
    (y : polarCanonicalCylinder) :
    centralForceHamiltonian m U (polarCanonicalDiffeomorph b y : V × V) =
      (y : (ℝ × ℝ) × (AddCircle (2 * π) × ℝ)).1.2 ^ 2 / (2 * m) +
        effectivePotential m (y : (ℝ × ℝ) × (AddCircle (2 * π) × ℝ)).2.2 U
          (y : (ℝ × ℝ) × (AddCircle (2 * π) × ℝ)).1.1 := by
  obtain ⟨⟨rp, a, L⟩, hr⟩ := y
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [coe_polarCanonicalDiffeomorph_apply, polarCylinderMap_coe]
  exact centralForceHamiltonian_polarCanonical (b.norm_eq_one 0) (b.norm_eq_one 1)
    (b.inner_eq_zero (by decide)) m U (x := (rp, (θ, L))) (mem_polarCanonicalCylinder.1 hr)

/-- The radial projection `(q, p) ↦ (‖q‖, ⟪q, p⟫ / ‖q‖)` is smooth on the punctured phase space
`{(q, p) | q ≠ 0}`. -/
theorem contMDiff_radialProjection_comp_subtypeVal :
    ContMDiff 𝓘(ℝ, V × V) 𝓘(ℝ, ℝ × ℝ) ∞
      (radialProjection ∘ Subtype.val : puncturedPhaseSpace V → ℝ × ℝ) := by
  intro x
  have hq : (x : V × V).1 ≠ 0 := mem_puncturedPhaseSpace.1 x.property
  have hn : ContDiffAt ℝ ∞ (fun y : V × V ↦ ‖y.1‖) (x : V × V) :=
    (contDiffAt_norm ℝ hq).comp _ contDiffAt_fst
  have hr : ContDiffAt ℝ ∞ radialProjection (x : V × V) := by
    rw [show radialProjection = fun y : V × V ↦ (‖y.1‖, ⟪y.1, y.2⟫_ℝ / ‖y.1‖) from
      funext fun y ↦ radialProjection_apply y.1 y.2]
    exact hn.prodMk ((contDiffAt_fst.inner ℝ contDiffAt_snd).div hn (norm_ne_zero_iff.2 hq))
  exact hr.contMDiffAt.comp x contMDiff_subtypeVal.contMDiffAt

variable [FiniteDimensional ℝ V]

/-- **Global polar canonical coordinates are symplectic.** The polar canonical diffeomorphism pulls
the standard symplectic form `ω₀ = Σ dqᵢ ∧ dpᵢ` of the punctured phase space back to the product
form `dr ∧ dp_r + dθ ∧ dL` on the cylinder `r > 0`, where `dθ` is the time form of the circle
`AddCircle (2 * π)` and `dL` the coordinate form of the real line. -/
theorem mpullback_polarCanonicalDiffeomorph :
    SmoothForm.mpullback (polarCanonicalDiffeomorph b) (polarCanonicalDiffeomorph b).contMDiff
        (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
          (stdSymplecticForm (V := V)).constSmooth) =
      SmoothForm.mpullback
        (Subtype.val : polarCanonicalCylinder → (ℝ × ℝ) × (AddCircle (2 * π) × ℝ))
        contMDiff_subtypeVal
        (SmoothTwoForm.prod (stdSymplecticForm (V := ℝ)).constSmooth
          (SmoothForm.wedge
            (SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm (2 * π)))
            (SmoothForm.mpullback Prod.snd contMDiff_snd SmoothForm.realLineCoordForm))) := by
  have hcomp : (Subtype.val : puncturedPhaseSpace V → V × V) ∘ polarCanonicalDiffeomorph b =
      fun z : polarCanonicalCylinder ↦ (polarCanonicalDiffeomorph b z : V × V) := rfl
  rw [← LinearMap.comp_apply, ← SmoothForm.mpullback_comp]
  simp only [hcomp]
  apply SmoothBundleForm.ext_eval₂
  rintro ⟨⟨rp, a, L⟩, hr⟩ v w
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective a
  simp only [SmoothForm.eval₂_mpullback, Manifold.mfderiv_subtype_val,
    ContinuousLinearEquiv.coe_coe, SymplecticForm.fromTangentSpace_constSmooth_apply,
    NormedSpace.fromTangentSpace_apply]
  simp only [mfderiv_polarCylinderMap_subtype_apply b θ L hr]
  refine (stdSymplecticForm_fderiv_polarCanonical (b.norm_eq_one 0) (b.norm_eq_one 1)
    (b.inner_eq_zero (by decide)) (x := (rp, (θ, L))) (mem_polarCanonicalCylinder.1 hr).ne'
    v w).trans ?_
  refine (SymplecticForm.prod_apply _ _ (v : (ℝ × ℝ) × (ℝ × ℝ)) w).trans ?_
  simp only [SmoothTwoForm.eval₂_prod, AddCircle.eval₂_wedge_timeForm_realLineCoordForm,
    SymplecticForm.fromTangentSpace_constSmooth_apply, NormedSpace.fromTangentSpace_apply]
  -- The tangent-space equivalences retype `v` and `w`, so only `rw` can remove them.
  rw [Manifold.tangentSpaceProdEquiv_apply, Manifold.tangentSpaceProdEquiv_apply,
    Manifold.tangentSpaceOpenEquiv_apply, Manifold.tangentSpaceOpenEquiv_apply]
  simp only [stdSymplecticForm_apply, RCLike.inner_apply, conj_trivial]
  ring

/-- **On a level of the angular momentum, the standard form is `dr ∧ dp_r`.** Let `b` be an
orthonormal basis of a plane `V` and `f` a smooth map into the punctured phase space
`{(q, p) | q ≠ 0}` along which the angular momentum `q₁ p₂ - q₂ p₁` in the basis `b` is constant.
Then `f` pulls the standard symplectic form `ω₀ = Σ dqᵢ ∧ dpᵢ` back to the pullback of the area
form `dr ∧ dp_r` of `ℝ × ℝ` along the radius and radial momentum `(‖q‖, ⟪q, p⟫ / ‖q‖)` of `f`. -/
theorem mpullback_stdSymplecticForm_of_angularMomentum_eq {EZ HZ Z : Type*}
    [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
    {IZ : ModelWithCorners ℝ EZ HZ} [TopologicalSpace Z] [ChartedSpace HZ Z] [IsManifold IZ ∞ Z]
    {f : Z → puncturedPhaseSpace V} (hf : ContMDiff IZ 𝓘(ℝ, V × V) ∞ f) {ℓ : ℝ}
    (hℓ : ∀ z, angularMomentum (b 0) (b 1) (f z : V × V) = ℓ) :
    SmoothForm.mpullback f hf (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V)
        contMDiff_subtypeVal (SymplecticForm.constSmooth (stdSymplecticForm (V := V)))) =
      SmoothForm.mpullback ((radialProjection ∘ Subtype.val) ∘ f)
        (contMDiff_radialProjection_comp_subtypeVal.comp hf)
        (SymplecticForm.constSmooth (stdSymplecticForm (V := ℝ))) := by
  set φ := polarCanonicalDiffeomorph b
  have hG : ContMDiff IZ (𝓘(ℝ, ℝ × ℝ).prod (𝓘(ℝ).prod 𝓘(ℝ))) ∞ (Subtype.val ∘ φ.symm ∘ f) :=
    contMDiff_subtypeVal.comp (φ.symm.contMDiff.comp hf)
  -- In polar canonical coordinates, `ω₀ = dr ∧ dp_r + dθ ∧ dL`.
  rw [← SmoothForm.mpullback_symm_eq_of_mpullback_eq (mpullback_polarCanonicalDiffeomorph b),
    SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback, SmoothTwoForm.prod_def,
    map_add, SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback]
  rw [SmoothForm.mpullback_wedge (k := 1) (l := 1) _ (contMDiff_snd.comp hG)]
  -- The coordinate `L` is constant along `f`, so `dL` pulls back to zero.
  have hL : SmoothForm.mpullback _ (contMDiff_snd.comp hG)
      (SmoothForm.mpullback Prod.snd contMDiff_snd SmoothForm.realLineCoordForm) = 0 := by
    rw [SmoothForm.mpullback_mpullback,
      SmoothForm.mpullback_congr (g := fun _ ↦ ℓ) _ contMDiff_const (funext fun z ↦ by
        simp only [comp_apply, φ, coe_polarCanonicalDiffeomorph_symm_apply, hℓ])]
    exact Subtype.ext (by
      rw [SmoothForm.coe_mpullback, TauCeti.mpullback_const one_ne_zero, ZeroMemClass.coe_zero])
  rw [hL, map_zero, add_zero]
  -- The coordinates `(r, p_r)` are the radial projection.
  refine SmoothForm.mpullback_congr _ _ (funext fun z ↦ ?_) _
  simp only [comp_apply, coe_polarCanonicalDiffeomorph_symm_apply]
  exact (Prod.ext (radialProjection_fst _) (radialProjection_snd _)).symm

end Basis

/-! ### Polar coordinates of the plane -/

/-- The position `r e_r` of polar coordinates is `2π`-periodic in the angle. -/
theorem periodic_smul_polarRadialUnit (u w : V) (r : ℝ) :
    Periodic (fun θ ↦ r • polarRadialUnit u w θ) (2 * π) := fun θ ↦ by
  simp only [polarRadialUnit_eq_of_coe_eq u w
    (show ((θ + 2 * π : ℝ) : Real.Angle) = θ by
      rw [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero])]

/-- **Polar coordinates of the plane** on the circle of angles: `(r, θ) ↦ r e_r`, with
`e_r = cos θ u + sin θ w` and `θ ∈ AddCircle (2 * π)`. -/
def polarPlaneMap (u w : V) (y : ℝ × AddCircle (2 * π)) : V :=
  (periodic_smul_polarRadialUnit u w y.1).lift y.2

/-- On a real lift of the angle, polar coordinates of the plane are `(r, θ) ↦ r e_r`. -/
@[simp]
theorem polarPlaneMap_coe (u w : V) (r θ : ℝ) :
    polarPlaneMap u w (r, (θ : AddCircle (2 * π))) = r • polarRadialUnit u w θ :=
  (periodic_smul_polarRadialUnit u w r).lift_coe θ

/-- The position of the point with polar canonical coordinates `((r, p_r), (θ, L))` has polar
coordinates `(r, θ)`. -/
theorem fst_polarCylinderMap (u w : V) (x : (ℝ × ℝ) × (AddCircle (2 * π) × ℝ)) :
    (polarCylinderMap u w x).1 = polarPlaneMap u w (x.1.1, x.2.1) := by
  obtain ⟨⟨r, pᵣ⟩, a, L⟩ := x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [polarCylinderMap_coe, polarPlaneMap_coe, polarCanonical_apply]

/-- The half-cylinder `r > 0` in `ℝ × AddCircle (2 * π)`, the domain of polar coordinates of the
plane. -/
def polarHalfCylinder : Opens (ℝ × AddCircle (2 * π)) :=
  ⟨{y | 0 < y.1}, isOpen_lt continuous_const continuous_fst⟩

@[simp]
theorem mem_polarHalfCylinder {y : ℝ × AddCircle (2 * π)} : y ∈ polarHalfCylinder ↔ 0 < y.1 :=
  Iff.rfl

/-- Polar coordinates of the plane are smooth. -/
theorem contMDiff_polarPlaneMap (u w : V) :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, V) ∞ (polarPlaneMap u w) := by
  have hcomp : polarPlaneMap u w ∘ Prod.map (id : ℝ → ℝ) ((↑) : ℝ → AddCircle (2 * π)) =
      fun y ↦ y.1 • polarRadialUnit u w y.2 :=
    funext fun y ↦ polarPlaneMap_coe u w y.1 y.2
  refine ((AddCircle.isLocalDiffeomorph_prodMap_id_coe (2 * π) ∞).contMDiff_comp_iff
    (surjective_id.prodMap QuotientAddGroup.mk_surjective) le_rfl).1 ?_
  rw [hcomp]
  exact (contDiff_fst.smul ((contDiff_polarRadialUnit u w).comp contDiff_snd)).contMDiff

section Basis

variable (b : OrthonormalBasis (Fin 2) ℝ V)

/-- The position of the point with polar coordinates `(r, θ)`, `r > 0`, has length `r`. -/
theorem norm_polarPlaneMap {y : ℝ × AddCircle (2 * π)} (hy : y ∈ polarHalfCylinder) :
    ‖polarPlaneMap (b 0) (b 1) y‖ = y.1 := by
  have h := norm_fst_polarCylinderMap b (y := ((y.1, 0), (y.2, 0)))
    (mem_polarCanonicalCylinder.2 (mem_polarHalfCylinder.1 hy))
  rwa [fst_polarCylinderMap] at h

/-- The radius and angle components of the inverse polar canonical coordinates of `(q, p)`, `q ≠ 0`,
are the length and the polar angle modulo `2π` of `q`. -/
private theorem radius_angle_polarCanonicalDiffeomorph_symm (x : puncturedPhaseSpace V) :
    ((((polarCanonicalDiffeomorph b).symm x : (ℝ × ℝ) × (AddCircle (2 * π) × ℝ)).1.1,
        ((polarCanonicalDiffeomorph b).symm x : (ℝ × ℝ) × (AddCircle (2 * π) × ℝ)).2.1) :
        ℝ × AddCircle (2 * π)) =
      (‖x.val.1‖, (((polarAngle (b 0) (b 1) x.val.1).toReal : ℝ) : AddCircle (2 * π))) := by
  rw [coe_polarCanonicalDiffeomorph_symm_apply]

/-- **Smooth polar coordinates of the plane.** For an orthonormal basis `b` of a plane `V`, the map
`(r, θ) ↦ r (cos θ b₀ + sin θ b₁)`, with `θ ∈ AddCircle (2 * π)`, is a diffeomorphism from the
half-cylinder `r > 0` onto the punctured plane `V ∖ {0}`, with inverse `q ↦ (‖q‖, θ(q))`. -/
def polarPlaneDiffeomorph :
    polarHalfCylinder ≃ₘ⟮𝓘(ℝ).prod 𝓘(ℝ), 𝓘(ℝ, V)⟯ puncturedSpace V where
  toFun y := ⟨polarPlaneMap (b 0) (b 1) y, by
    rw [mem_puncturedSpace, ← norm_ne_zero_iff, norm_polarPlaneMap b y.property]
    exact (mem_polarHalfCylinder.1 y.property).ne'⟩
  invFun q := ⟨(‖(q : V)‖, (((polarAngle (b 0) (b 1) q).toReal : ℝ) : AddCircle (2 * π))),
    mem_polarHalfCylinder.2 (norm_pos_iff.2 (mem_puncturedSpace.1 q.property))⟩
  left_inv y := by
    have h := radius_angle_polarCanonicalDiffeomorph_symm b (polarCanonicalDiffeomorph b
      ⟨((y.val.1, 0), (y.val.2, 0)), mem_polarCanonicalCylinder.2
          (mem_polarHalfCylinder.1 y.property)⟩)
    rw [Diffeomorph.symm_apply_apply, coe_polarCanonicalDiffeomorph_apply,
      fst_polarCylinderMap] at h
    exact Subtype.ext h.symm
  right_inv q := by
    have hq := polarCanonical_polarAngle b 0 (mem_puncturedSpace.1 q.property)
      (Real.Angle.coe_toReal _)
    refine Subtype.ext ?_
    simpa only [polarCanonical_apply, polarPlaneMap_coe] using congrArg Prod.fst hq
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff (puncturedSpace V) _).1
    ((contMDiff_polarPlaneMap (b 0) (b 1)).comp contMDiff_subtypeVal)
  contMDiff_invFun := by
    -- The inverse is read off from the inverse polar canonical coordinates of `(q, 0)`.
    let incl : puncturedSpace V → puncturedPhaseSpace V := fun q ↦
      ⟨((q : V), 0), mem_puncturedPhaseSpace.2 (mem_puncturedSpace.1 q.property)⟩
    let proj : polarCanonicalCylinder → polarHalfCylinder := fun z ↦
      ⟨((z : (ℝ × ℝ) × (AddCircle (2 * π) × ℝ)).1.1,
        (z : (ℝ × ℝ) × (AddCircle (2 * π) × ℝ)).2.1),
        mem_polarHalfCylinder.2 (mem_polarCanonicalCylinder.1 z.property)⟩
    have hincl : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, V × V) ∞ incl :=
      (ContMDiff.subtypeVal_comp_iff (puncturedPhaseSpace V) _).1
        (contMDiff_subtypeVal.prodMk_space contMDiff_const)
    have hproj : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod (𝓘(ℝ).prod 𝓘(ℝ))) (𝓘(ℝ).prod 𝓘(ℝ)) ∞ proj :=
      (ContMDiff.subtypeVal_comp_iff polarHalfCylinder _).1
        ((((contDiff_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ)).contMDiff (n := ∞)).comp
          contMDiff_fst).prodMk (contMDiff_fst.comp contMDiff_snd) |>.comp contMDiff_subtypeVal)
    refine (hproj.comp ((polarCanonicalDiffeomorph b).symm.contMDiff.comp hincl)).congr
      fun q ↦ ?_
    exact Subtype.ext (radius_angle_polarCanonicalDiffeomorph_symm b (incl q)).symm

@[simp]
theorem coe_polarPlaneDiffeomorph_apply (y : polarHalfCylinder) :
    (polarPlaneDiffeomorph b y : V) = polarPlaneMap (b 0) (b 1) y :=
  (rfl)

/-- The inverse polar coordinates of `q ≠ 0` are its length and its polar angle modulo `2π`. -/
@[simp]
theorem coe_polarPlaneDiffeomorph_symm_apply (q : puncturedSpace V) :
    ((polarPlaneDiffeomorph b).symm q : ℝ × AddCircle (2 * π)) =
      (‖(q : V)‖, (((polarAngle (b 0) (b 1) q).toReal : ℝ) : AddCircle (2 * π))) :=
  (rfl)

/-- **Polar coordinates with a real angle are a local diffeomorphism off the origin.** At
`(r, θ)` with `r > 0`, the map `(r, θ) ↦ r e_r` from `ℝ × ℝ` to the plane is a local
diffeomorphism: it is the quotient map `θ ↦ θ mod 2π` followed by
`TauCeti.polarPlaneDiffeomorph`. -/
theorem isLocalDiffeomorphAt_smul_polarRadialUnit {x : ℝ × ℝ} (hr : 0 < x.1) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V) ∞
      (fun x : ℝ × ℝ ↦ x.1 • polarRadialUnit (b 0) (b 1) x.2) x := by
  let y : polarHalfCylinder := ⟨(x.1, x.2), mem_polarHalfCylinder.2 hr⟩
  -- On the half-cylinder, `polarPlaneMap` is the diffeomorphism `polarPlaneDiffeomorph`.
  have hP :
      IsLocalDiffeomorphAt (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, V) ∞ (polarPlaneMap (b 0) (b 1)) y := by
    have h : IsLocalDiffeomorphAt (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, V) ∞
        (polarPlaneMap (b 0) (b 1) ∘ Subtype.val) y :=
      IsLocalDiffeomorphAt.comp (hf := (polarPlaneDiffeomorph b).isLocalDiffeomorph y)
        (hg := isLocalDiffeomorph_subtype_val _)
    exact h.of_comp_right (isLocalDiffeomorph_subtype_val y)
  have hcomp : (fun x : ℝ × ℝ ↦ x.1 • polarRadialUnit (b 0) (b 1) x.2) =
      polarPlaneMap (b 0) (b 1) ∘ Prod.map id ((↑) : ℝ → AddCircle (2 * π)) :=
    funext fun x ↦ (polarPlaneMap_coe _ _ x.1 x.2).symm
  rw [hcomp]
  exact IsLocalDiffeomorphAt.comp (hf := AddCircle.isLocalDiffeomorph_prodMap_id_coe (2 * π) ∞ x)
    (hg := hP)

/-- **Global polar canonical coordinates lie over polar coordinates of the plane.** The position of
the point with polar canonical coordinates `((r, p_r), (θ, L))` is the point with polar coordinates
`(r, θ)`. -/
theorem fst_polarCanonicalDiffeomorph (y : polarCanonicalCylinder) :
    (polarCanonicalDiffeomorph b y : V × V).1 =
      polarPlaneDiffeomorph b ⟨((y : (ℝ × ℝ) × (AddCircle (2 * π) × ℝ)).1.1,
        (y : (ℝ × ℝ) × (AddCircle (2 * π) × ℝ)).2.1),
        mem_polarHalfCylinder.2 (mem_polarCanonicalCylinder.1 y.property)⟩ := by
  rw [coe_polarCanonicalDiffeomorph_apply, fst_polarCylinderMap, coe_polarPlaneDiffeomorph_apply]

end Basis

end TauCeti

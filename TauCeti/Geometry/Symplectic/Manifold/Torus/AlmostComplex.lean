/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Descent
public import TauCeti.Geometry.Symplectic.Manifold.Energy.Surface
public import TauCeti.Geometry.Symplectic.Manifold.Torus.SphericalArea

/-!
# The standard almost complex structure of the torus

For positive periods `p i`, `i : ι ⊕ ι`, the torus `T = ∀ i, AddCircle (p i)` is the quotient of
complex coordinate space `ι → ℂ` by the covering map `π z = ([Re z_j], [Im z_j])`
(`TauCeti.complexPiTorusCover`). Multiplication by `i` on `ι → ℂ` commutes with the deck
translations, so it descends to a smooth almost complex structure on `T`
(`TauCeti.torusAlmostComplexStructure p`), the unique one for which `π` is pseudoholomorphic
(`TauCeti.isPseudoholomorphic_complexPiTorusCover`). In the real coordinates of the circles it
sends the direction `∂_(inl j)` of the real part of `z_j` to the direction `∂_(inr j)` of its
imaginary part, and `∂_(inr j)` to `-∂_(inl j)` (`TauCeti.torusAlmostComplexStructure_apply_inr`,
`TauCeti.torusAlmostComplexStructure_apply_inl`). Since `π` pulls the standard symplectic form
`ω_T` back to the standard form of `ι → ℂ`, which is compatible with multiplication by `i`, the
structure is compatible with `ω_T` (`TauCeti.compatible_torusAlmostComplexStructure`).

A pseudoholomorphic sphere in `T`, for any almost complex structure tamed by `ω_T`, is constant
(`TauCeti.apply_eq_of_isPseudoholomorphic_of_tames_torusSymplecticForm`). More generally, let `C`
be a compact connected simply connected boundaryless surface with an almost complex structure `j`,
oriented so that the frames `(e, j e)` are positive, and let `w : C → T` be smooth and
pseudoholomorphic for an `ω_T`-tame structure. Its energy is its symplectic area `∫_C w^* ω_T`,
which vanishes because `C` is simply connected
(`TauCeti.integralTopForm_mpullback_torusSymplecticForm_eq_zero`), and a map of zero energy for a
tame structure is constant. This is the torus half of the identification of the
pseudoholomorphic spheres of `S²(a) × T` for the product structure, in Gromov's proof of the
nonsqueezing theorem.

## Main definitions

* `TauCeti.torusAlmostComplexStructure p`: the standard almost complex structure of the torus
  `∀ i : ι ⊕ ι, AddCircle (p i)`.

## Main results

* `TauCeti.torusAlmostComplexStructure_apply_mfderiv`: the differential of the covering map is
  complex linear, `J (dπ v) = dπ (i v)`.
* `TauCeti.torusAlmostComplexStructure_apply_inl`, `TauCeti.torusAlmostComplexStructure_apply_inr`:
  the structure in the real coordinates of the circles.
* `TauCeti.isPseudoholomorphic_complexPiTorusCover`,
  `TauCeti.eq_torusAlmostComplexStructure_iff_isPseudoholomorphic`: the covering map is
  pseudoholomorphic, and this characterizes the structure.
* `TauCeti.compatible_torusAlmostComplexStructure`: the structure is compatible with `ω_T`.
* `TauCeti.apply_eq_of_isPseudoholomorphic_of_tames_torusSymplecticForm`: pseudoholomorphic maps
  from a compact connected simply connected surface to the torus, for an `ω_T`-tame structure, are
  constant.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Mathematicae 82
  (1985), 307–347, §0.3.A (the nonsqueezing theorem, proved through `S² × T^(2n-2)`).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 9.3 (the proof of the nonsqueezing theorem).
-/

public section

noncomputable section

open Function
open scoped Manifold ContDiff

namespace TauCeti

variable {ι : Type*} [Fintype ι] (p : ι ⊕ ι → ℝ) [∀ i, Fact (0 < p i)]

/-- Multiplication by `i` on `ι → ℂ` respects the identifications of the covering map: the
differential of `π` is `TauCeti.complexToRealPi` at every point, which is injective. -/
private theorem mfderiv_complexPiTorusCover_I_smul ⦃z z' : ι → ℂ⦄ (v : TangentSpace 𝓘(ℝ, ι → ℂ) z)
    (v' : TangentSpace 𝓘(ℝ, ι → ℂ) z') (_ : complexPiTorusCover p z = complexPiTorusCover p z')
    (h : mfderiv 𝓘(ℝ, ι → ℂ) (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))
        (complexPiTorusCover p) z v =
      mfderiv 𝓘(ℝ, ι → ℂ) (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))
        (complexPiTorusCover p) z' v') :
    mfderiv 𝓘(ℝ, ι → ℂ) (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) (complexPiTorusCover p) z
        ((AlmostComplexStructure.ofComplexModule (ι → ℂ)).constSmooth z v) =
      mfderiv 𝓘(ℝ, ι → ℂ) (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) (complexPiTorusCover p) z'
        ((AlmostComplexStructure.ofComplexModule (ι → ℂ)).constSmooth z' v') := by
  rw [mfderiv_complexPiTorusCover, mfderiv_complexPiTorusCover] at h ⊢
  rw [(complexToRealPi ι).injective h]
  exact congrArg _ ((AlmostComplexStructure.constSmooth_apply _ z v').trans
    (AlmostComplexStructure.constSmooth_apply _ z' v').symm)

/-- The **standard almost complex structure** of the torus `∀ i : ι ⊕ ι, AddCircle (p i)`: the
descent of multiplication by `i` on `ι → ℂ` along the covering map
`π z = ([Re z_j], [Im z_j])`. It sends `∂_(inl j)` to `∂_(inr j)` and `∂_(inr j)` to
`-∂_(inl j)` (`TauCeti.torusAlmostComplexStructure_apply_inr`,
`TauCeti.torusAlmostComplexStructure_apply_inl`). -/
def torusAlmostComplexStructure :
    SmoothAlmostComplexStructure (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))
      (∀ i, AddCircle (p i)) :=
  SmoothAlmostComplexStructure.descend (isLocalDiffeomorph_complexPiTorusCover p)
    (complexPiTorusCover_surjective p) (AlmostComplexStructure.ofComplexModule (ι → ℂ)).constSmooth
    (mfderiv_complexPiTorusCover_I_smul p)

/-- The differential of the covering map is complex linear: `J (dπ v) = dπ (i v)`. -/
@[simp]
theorem torusAlmostComplexStructure_apply_mfderiv (z v : ι → ℂ) :
    torusAlmostComplexStructure p (complexPiTorusCover p z)
        (mfderiv 𝓘(ℝ, ι → ℂ) (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))
          (complexPiTorusCover p) z v) =
      mfderiv 𝓘(ℝ, ι → ℂ) (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) (complexPiTorusCover p) z
        (Complex.I • v) := by
  refine (SmoothAlmostComplexStructure.descend_apply_mfderiv _ _ _ _ z v).trans ?_
  rw [AlmostComplexStructure.constSmooth_apply, AlmostComplexStructure.ofComplexModule_apply]

/-- Every tangent vector of the torus at `π z` is the image of a tangent vector of `ι → ℂ` under
the differential of the covering map. -/
private theorem exists_mfderiv_complexPiTorusCover_eq (z : ι → ℂ)
    (v : TangentSpace (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) (complexPiTorusCover p z)) :
    ∃ w : ι → ℂ, mfderiv 𝓘(ℝ, ι → ℂ) (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))
      (complexPiTorusCover p) z w = v :=
  ⟨(complexToRealPi ι).symm v, by
    rw [mfderiv_complexPiTorusCover]
    exact (complexToRealPi ι).apply_symm_apply v⟩

/-- In the real coordinates of the circles, the real-part coordinate of `J v` is minus the
imaginary-part coordinate of `v`, `(J v)_(inl j) = -v_(inr j)`: the standard structure sends
`∂_(inr j)` to `-∂_(inl j)`. -/
@[simp]
theorem torusAlmostComplexStructure_apply_inl (x : ∀ i, AddCircle (p i))
    (v : TangentSpace (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) x) (j : ι) :
    torusAlmostComplexStructure p x v (.inl j) = -v (.inr j) := by
  obtain ⟨z, rfl⟩ := complexPiTorusCover_surjective p x
  obtain ⟨w, rfl⟩ := exists_mfderiv_complexPiTorusCover_eq p z v
  simp

/-- In the real coordinates of the circles, the imaginary-part coordinate of `J v` is the
real-part coordinate of `v`, `(J v)_(inr j) = v_(inl j)`: the standard structure sends `∂_(inl j)`
to `∂_(inr j)`. -/
@[simp]
theorem torusAlmostComplexStructure_apply_inr (x : ∀ i, AddCircle (p i))
    (v : TangentSpace (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) x) (j : ι) :
    torusAlmostComplexStructure p x v (.inr j) = v (.inl j) := by
  obtain ⟨z, rfl⟩ := complexPiTorusCover_surjective p x
  obtain ⟨w, rfl⟩ := exists_mfderiv_complexPiTorusCover_eq p z v
  simp

/-- The covering map `ι → ℂ → T` is pseudoholomorphic from multiplication by `i` to the standard
structure of the torus. -/
theorem isPseudoholomorphic_complexPiTorusCover :
    IsPseudoholomorphic (AlmostComplexStructure.ofComplexModule (ι → ℂ)).constSmooth
      (torusAlmostComplexStructure p) (complexPiTorusCover p) :=
  SmoothAlmostComplexStructure.isPseudoholomorphic_descend _ _ _ _

/-- The standard structure is the only almost complex structure on the torus for which the
covering map is pseudoholomorphic. -/
theorem eq_torusAlmostComplexStructure_iff_isPseudoholomorphic
    (K : SmoothAlmostComplexStructure (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))
      (∀ i, AddCircle (p i))) :
    K = torusAlmostComplexStructure p ↔
      IsPseudoholomorphic (AlmostComplexStructure.ofComplexModule (ι → ℂ)).constSmooth K
        (complexPiTorusCover p) :=
  SmoothAlmostComplexStructure.eq_descend_iff_isPseudoholomorphic _ _ _ _ K

/-- **The standard structure of the torus is compatible with its standard symplectic form.** The
covering map pulls `ω_T` back to the standard form of `ι → ℂ`, which is compatible with
multiplication by `i`. -/
theorem compatible_torusAlmostComplexStructure :
    (torusSymplecticForm p).Compatible (torusAlmostComplexStructure p) := by
  rw [torusAlmostComplexStructure, SmoothAlmostComplexStructure.compatible_descend_iff,
    mpullback_complexPiTorusCover_torusSymplecticForm]
  exact SymplecticForm.compatible_constSmooth_iff.2 stdComplexPiSymplecticForm_compatible

/-! ### Pseudoholomorphic spheres in the torus -/

variable {E H C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace C] [ChartedSpace H C]
  [IsManifold I ∞ C] [BoundarylessManifold I C] [T2Space C] [CompactSpace C]
  [SimplyConnectedSpace C] {j : SmoothAlmostComplexStructure I C}
  {o : Manifold.Orientation I C (Fin 2)} {w : C → ∀ i, AddCircle (p i)}
  {K : SmoothAlmostComplexStructure (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))
    (∀ i, AddCircle (p i))}

/-- **Pseudoholomorphic spheres in the torus are constant.** Let `C` be a compact simply connected
boundaryless surface with an almost complex structure `j`, oriented so that the frames `(e, j e)`
are positive, and let `K` be an almost complex structure on the torus tamed by `ω_T`, such as the
standard one (`TauCeti.compatible_torusAlmostComplexStructure`). A smooth map `w : C → T` that is
pseudoholomorphic for `K` is constant: its energy is its symplectic area `∫_C w^* ω_T`, which
vanishes since `C` is simply connected. -/
theorem apply_eq_of_isPseudoholomorphic_of_tames_torusSymplecticForm
    (ho : ∀ c (b : Module.Basis (Fin 2) ℝ (TangentSpace I c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hw : ContMDiff I (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) ∞ w)
    (hK : (torusSymplecticForm p).Tames K) (hhol : IsPseudoholomorphic j K w) (c c' : C) :
    w c = w c' := by
  have h : (torusSymplecticForm p).energy K j o w = 0 := by
    rw [SmoothTwoForm.energy_eq_integralTopForm_mpullback (isPseudoholomorphic_iff.1 hhol),
      ← integralTopForm_mpullback_torusSymplecticForm_eq_zero o hw, SmoothForm.coe_mpullback]
  exact hK.apply_eq_of_energy_eq_zero ho (hw.of_le (by simp)) h c c'

end TauCeti

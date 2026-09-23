/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Regular
public import TauCeti.Geometry.Toric.Analytic.MixedMonomial
public import TauCeti.Geometry.Toric.Analytic.RegularChart

/-!
# The affine analytic chart of a regular cone

An integral basis of the lattice whose vectors at the ray indices are the primitive ray generators
of a cone `σ` splits the dual semigroup of `σ` as `(ToricRay σ →₀ ℕ) × (ι →₀ ℤ)`, so the complex
points of the affine toric scheme of `σ` become the mixed chart `ℂ ^ k × (ℂ ^ *) ^ l`, with `k` the
number of rays of `σ` and `l` the number of complementary basis vectors. This file names that
chart, computes its coordinate functions, and compares the charts of two extending bases.

The coordinates are values of the point on monomials: the coordinate indexed by a ray is the value
on the monomial of the dual basis character of that ray, and the coordinates indexed by the
complementary basis vectors are the invertible values on their dual basis characters. They are
therefore characters, not choices, once the basis is fixed, and the chart is a homeomorphism for the
monomial-embedding topology of an arbitrary finite generating family of the dual semigroup, which
was defined without reference to any splitting.

Two extending bases cannot differ at the ray indices, since a ray of a toric cone in an integral
lattice has a single primitive generator. The comparison of their charts is therefore a mixed
monomial map of the restricted shape that `TauCeti.Toric.MixedExponent` permits: each boundary
coordinate is kept and multiplied by a monomial in the torus coordinates, and the torus coordinates
are transformed among themselves by the complementary block of the transition matrix. No boundary
coordinate contributes to a torus coordinate. Read in the ambient coordinates `ℂ ^ k × ℂ ^ l`
attached to a numbering of the rays, the comparison is the map
`TauCeti.Toric.basisChangeOpenPartialHomeomorph` of the transition block, whose torus block is
unimodular; that map is holomorphic in both directions, which is the compatibility an atlas
assembled from these charts needs.

## Main declarations

* `TauCeti.Toric.coneChartEquiv`: the affine analytic chart of a cone with an extending basis, with
  `TauCeti.Toric.coneChartEquiv_fst_apply` and `TauCeti.Toric.val_coneChartEquiv_snd_apply`
  identifying its coordinate functions with the dual basis characters and
  `TauCeti.Toric.coneChartEquiv_symm_apply_single` and
  `TauCeti.Toric.apply_single_ne_zero_iff_coneChartEquiv_fst_ne_zero` describing the value and
  nonvanishing of a point on an arbitrary monomial.
* `TauCeti.Toric.coneChartHomeomorph`: the chart is a homeomorphism for the monomial-embedding
  topology of any finite generating family of the dual semigroup.
* `TauCeti.Toric.coneChartEquiv_fst_apply_basisChange` and
  `TauCeti.Toric.coneChartEquiv_snd_apply_basisChange`: changing the extending basis multiplies
  each boundary coordinate by a monomial in the torus coordinates and transforms the torus
  coordinates by the complementary block of the transition matrix.
* `TauCeti.Toric.coneChartAmbient`: the chart in the ambient mixed coordinates attached to a
  numbering of the rays, which lands in `TauCeti.Toric.mixedChartDomain`.
* `TauCeti.Toric.coneChartAmbientHomeomorph`: the ambient chart as a homeomorphism onto
  `TauCeti.Toric.mixedChartDomain`.
* `TauCeti.Toric.mixedMonomialMap_ofTorusBlock_coneChartAmbient` and
  `TauCeti.Toric.basisChangeOpenPartialHomeomorph_coneChartAmbient`: in those coordinates the
  change of extending basis is the mixed monomial biholomorphism of the transition block.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2 and 2.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.2 and 3.1.
-/

public section

namespace TauCeti.Toric

open Finset Multiplicative

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {σ : PointedCone ℝ V} {s : ℕ}

variable (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
  {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N} (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ)))

/-! ### The chart of an extending basis -/

/-- The affine analytic chart of a cone with an extending basis: the complex points of its affine
toric scheme in the mixed coordinates supplied by the basis. The coordinates indexed by the rays of
the cone may vanish, while the coordinates indexed by the complementary basis vectors are
invertible. -/
noncomputable def coneChartEquiv :
    AffineSemigroupComplexPoint (dualSemigroup hi σ) ≃ ((ToricRay σ → ℂ) × (ι → ℂˣ)) :=
  regularAffinePointEquiv (regularDualSemigroupEquiv hi hσ hb)

/-- The value on the monomial of a character of the dual semigroup of the complex point with
prescribed mixed coordinates: it is the mixed monomial whose exponents are the regular coordinates
of the character, natural at the ray indices and integral at the complementary ones. -/
@[simp]
theorem coneChartEquiv_symm_apply_single (z : (ToricRay σ → ℂ) × (ι → ℂˣ))
    (m : dualSemigroup hi σ) :
    (coneChartEquiv hi hσ hb).symm z (MonoidAlgebra.single (ofAdd m) 1) =
      ((regularDualSemigroupEquiv hi hσ hb m).1.prod fun ρ n ↦ z.1 ρ ^ n) *
        ((regularDualSemigroupEquiv hi hσ hb m).2.prod fun j n ↦ z.2 j ^ n : ℂˣ) :=
  regularAffinePointEquiv_symm_apply_single _ z m

/-- A monomial is nonzero at a complex point exactly when every ray coordinate occurring in its
support is nonzero. The complementary-coordinate factor is always a unit. -/
theorem apply_single_ne_zero_iff_coneChartEquiv_fst_ne_zero
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) (m : dualSemigroup hi σ) :
    x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0 ↔
      ∀ ρ ∈ (regularDualSemigroupEquiv hi hσ hb m).1.support,
        (coneChartEquiv hi hσ hb x).1 ρ ≠ 0 := by
  obtain ⟨z, rfl⟩ := (coneChartEquiv hi hσ hb).symm.surjective x
  rw [coneChartEquiv_symm_apply_single, mul_ne_zero_iff, Finsupp.prod_ne_zero_iff]
  simp only [Equiv.apply_symm_apply]
  constructor
  · rintro ⟨hz, -⟩ ρ hρ hzero
    exact hz ρ hρ (by simp [hzero, Finsupp.mem_support_iff.mp hρ])
  · intro hz
    exact ⟨fun ρ hρ ↦ pow_ne_zero _ (hz ρ hρ), Units.ne_zero _⟩

/-- The coordinate of a complex point indexed by a ray is its value on the monomial of the dual
basis character of that ray. -/
@[simp]
theorem coneChartEquiv_fst_apply (x : AffineSemigroupComplexPoint (dualSemigroup hi σ))
    (ρ : ToricRay σ) :
    (coneChartEquiv hi hσ hb x).1 ρ =
      x (MonoidAlgebra.single (ofAdd (dualSemigroupCoord hi hσ hb (Sum.inl ρ))) 1) := by
  rw [coneChartEquiv, regularAffinePointEquiv_fst_apply,
    regularDualSemigroupEquiv_symm_apply_single_zero]

/-- The coordinate of a complex point indexed by a complementary basis vector is, as a complex
number, its value on the monomial of the dual basis character of that vector. -/
@[simp]
theorem val_coneChartEquiv_snd_apply (x : AffineSemigroupComplexPoint (dualSemigroup hi σ))
    (j : ι) :
    ((coneChartEquiv hi hσ hb x).2 j : ℂ) =
      x (MonoidAlgebra.single (ofAdd (dualSemigroupCoord hi hσ hb (Sum.inr j))) 1) := by
  rw [coneChartEquiv, val_regularAffinePointEquiv_snd_apply,
    regularDualSemigroupEquiv_symm_apply_zero_single]

/-- The affine analytic chart is a homeomorphism for the monomial-embedding topology of any finite
generating family of the dual semigroup: the complex points of the affine toric scheme of a cone
with an extending basis are the mixed chart `ℂ ^ k × (ℂ ^ *) ^ l`, whatever generating family
topologizes them. -/
noncomputable def coneChartHomeomorph (g : AddGeneratingFamily (dualSemigroup hi σ) s) :
    @Homeomorph (AffineSemigroupComplexPoint (dualSemigroup hi σ)) ((ToricRay σ → ℂ) × (ι → ℂˣ))
      (affinePointTopology g) inferInstance :=
  regularAffinePointHomeomorph g (regularDualSemigroupEquiv hi hσ hb)

@[simp]
theorem coe_coneChartHomeomorph (g : AddGeneratingFamily (dualSemigroup hi σ) s) :
    ⇑(coneChartHomeomorph hi hσ hb g) = coneChartEquiv hi hσ hb := by
  simp [coneChartHomeomorph, coneChartEquiv]

@[simp]
theorem coe_coneChartHomeomorph_symm (g : AddGeneratingFamily (dualSemigroup hi σ) s) :
    ⇑(@Homeomorph.symm _ _ (affinePointTopology g) _ (coneChartHomeomorph hi hσ hb g)) =
      (coneChartEquiv hi hσ hb).symm := by
  simp [coneChartHomeomorph, coneChartEquiv]

/-! ### Changing the extending basis -/

section BasisChange

variable [Fintype ι] {b' : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
  (hb' : ∀ ρ, IsPrimitiveGenerator i ρ (b' (Sum.inl ρ)))

include hi hσ hb hb'

/-- Changing the extending basis multiplies the coordinate indexed by a ray by a monomial in the
torus coordinates, whose exponents are the complementary entries of the ray row of the transition
matrix. The coordinate itself occurs to the first power: both bases carry the primitive generator of
a ray at the index of that ray, so the ray block of the transition matrix is the identity. -/
theorem coneChartEquiv_fst_apply_basisChange
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) (ρ : ToricRay σ) :
    (coneChartEquiv hi hσ hb' x).1 ρ = (coneChartEquiv hi hσ hb x).1 ρ *
      ∏ j, ((coneChartEquiv hi hσ hb x).2 j : ℂ) ^ b'.toMatrix b (Sum.inl ρ) (Sum.inr j) := by
  -- Read the statement at the point with prescribed coordinates for the first basis.
  obtain ⟨z, rfl⟩ := (coneChartEquiv hi hσ hb).symm.surjective x
  simp only [Equiv.apply_symm_apply]
  -- The coordinate is the value on the dual basis character of `ρ` for the second basis, whose
  -- regular coordinates for the first basis are the standard ray generator and the ray row.
  rw [coneChartEquiv_fst_apply, coneChartEquiv_symm_apply_single,
    regularDualSemigroupEquiv_fst_dualSemigroupCoord_inl hi hσ hb hb',
    Finsupp.prod_single_index (h := fun ρ' (n : ℕ) ↦ z.1 ρ' ^ n) (pow_zero _), pow_one,
    Finsupp.prod_fintype _ _ fun j ↦ zpow_zero (z.2 j), ← Units.coeHom_apply, map_prod]
  exact congrArg _ (prod_congr rfl fun j _ ↦ by
    rw [Units.coeHom_apply, Units.val_zpow_eq_zpow_val,
      regularDualSemigroupEquiv_snd_dualSemigroupCoord hi hσ hb hb'])

/-- Changing the extending basis transforms the invertible coordinates among themselves, by the
complementary block of the transition matrix. No coordinate indexed by a ray contributes: the
complementary rows of the ray columns of the transition matrix vanish, because both bases carry the
primitive generator of a ray at the index of that ray. -/
theorem coneChartEquiv_snd_apply_basisChange
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) (j : ι) :
    (coneChartEquiv hi hσ hb' x).2 j =
      ∏ j', (coneChartEquiv hi hσ hb x).2 j' ^ b'.toMatrix b (Sum.inr j) (Sum.inr j') := by
  refine Units.ext ?_
  -- Read the statement at the point with prescribed coordinates for the first basis.
  obtain ⟨z, rfl⟩ := (coneChartEquiv hi hσ hb).symm.surjective x
  simp only [Equiv.apply_symm_apply]
  -- The dual basis character of a complementary index has no ray coordinate, so no coordinate
  -- indexed by a ray occurs in the monomial.
  rw [val_coneChartEquiv_snd_apply, coneChartEquiv_symm_apply_single,
    regularDualSemigroupEquiv_fst_dualSemigroupCoord_inr hi hσ hb hb', Finsupp.prod_zero_index,
    one_mul, Finsupp.prod_fintype _ _ fun j ↦ zpow_zero (z.2 j)]
  exact congrArg _ (prod_congr rfl fun j' _ ↦ by
    rw [regularDualSemigroupEquiv_snd_dualSemigroupCoord hi hσ hb hb'])

/-- The complex value of a transformed invertible coordinate, as a monomial in the complex values of
the invertible coordinates of the other chart. -/
theorem val_coneChartEquiv_snd_apply_basisChange
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) (j : ι) :
    ((coneChartEquiv hi hσ hb' x).2 j : ℂ) =
      ∏ j', ((coneChartEquiv hi hσ hb x).2 j' : ℂ) ^ b'.toMatrix b (Sum.inr j) (Sum.inr j') := by
  rw [coneChartEquiv_snd_apply_basisChange hi hσ hb hb', ← Units.coeHom_apply, map_prod]
  exact prod_congr rfl fun j' _ ↦ by rw [Units.coeHom_apply, Units.val_zpow_eq_zpow_val]

end BasisChange

/-! ### The chart in ambient mixed coordinates -/

section Ambient

variable {k l : ℕ} {B B' : Module.Basis (ToricRay σ ⊕ Fin l) ℤ N}
  (hB : ∀ ρ, IsPrimitiveGenerator i ρ (B (Sum.inl ρ)))
  (hB' : ∀ ρ, IsPrimitiveGenerator i ρ (B' (Sum.inl ρ))) (κ : ToricRay σ ≃ Fin k)

/-- The affine analytic chart of a cone with an extending basis, in the ambient mixed coordinates
`ℂ ^ k × ℂ ^ l` attached to a numbering `κ` of its rays: the coordinates indexed by the rays are
reindexed along `κ`, and the invertible coordinates are viewed as complex numbers. This is the shape
on which mixed monomial maps act. -/
noncomputable def coneChartAmbient (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) :
    (Fin k → ℂ) × (Fin l → ℂ) :=
  (fun a ↦ (coneChartEquiv hi hσ hB x).1 (κ.symm a),
    fun c ↦ ((coneChartEquiv hi hσ hB x).2 c : ℂ))

@[simp]
theorem coneChartAmbient_fst_apply (x : AffineSemigroupComplexPoint (dualSemigroup hi σ))
    (a : Fin k) :
    (coneChartAmbient hi hσ hB κ x).1 a = (coneChartEquiv hi hσ hB x).1 (κ.symm a) := by
  simp [coneChartAmbient]

@[simp]
theorem coneChartAmbient_snd_apply (x : AffineSemigroupComplexPoint (dualSemigroup hi σ))
    (c : Fin l) :
    (coneChartAmbient hi hσ hB κ x).2 c = ((coneChartEquiv hi hσ hB x).2 c : ℂ) := by
  simp [coneChartAmbient]

/-- The ambient coordinates of a complex point lie in the mixed-chart locus: the coordinates indexed
by the complementary basis vectors are invertible. -/
theorem coneChartAmbient_mem_mixedChartDomain
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) :
    coneChartAmbient hi hσ hB κ x ∈ mixedChartDomain k l :=
  mem_mixedChartDomain.2 fun c ↦ by
    rw [coneChartAmbient_snd_apply]
    exact Units.ne_zero _

/-- The ambient coordinates give a homeomorphism from the complex points of the affine toric
scheme onto the mixed-chart locus. It is obtained from `coneChartHomeomorph` by reindexing the ray
coordinates and applying `unitsHomeomorphNeZero` coordinatewise to the torus coordinates. -/
noncomputable def coneChartAmbientHomeomorph (g : AddGeneratingFamily (dualSemigroup hi σ) s) :
    @Homeomorph (AffineSemigroupComplexPoint (dualSemigroup hi σ))
      {z // z ∈ mixedChartDomain k l} (affinePointTopology g) instTopologicalSpaceSubtype :=
  let _ := affinePointTopology g
  let ambientValueHomeomorph :
      ((Fin k → ℂ) × (Fin l → {z : ℂ // z ≠ 0})) ≃ₜ {z // z ∈ mixedChartDomain k l} :=
    { toFun := fun z ↦ ⟨(z.1, fun c ↦ z.2 c), mem_mixedChartDomain.2 fun c ↦ (z.2 c).2⟩
      invFun := fun z ↦ (z.1.1, fun c ↦ ⟨z.1.2 c, mem_mixedChartDomain.1 z.2 c⟩)
      left_inv := fun z ↦ rfl
      right_inv := fun z ↦ rfl
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_fst.prodMk <| continuous_pi fun c ↦
          continuous_subtype_val.comp <| (continuous_apply c).comp continuous_snd
      continuous_invFun := continuous_fst.comp continuous_subtype_val |>.prodMk <|
        continuous_pi fun c ↦ Continuous.subtype_mk
          ((continuous_apply c).comp <| continuous_snd.comp continuous_subtype_val) _ }
  (coneChartHomeomorph hi hσ hB g).trans <|
    ((Homeomorph.piCongrLeft κ).prodCongr
      (Homeomorph.piCongrRight fun _ ↦ unitsHomeomorphNeZero (G₀ := ℂ))).trans
        ambientValueHomeomorph

@[simp]
theorem coneChartAmbientHomeomorph_apply (g : AddGeneratingFamily (dualSemigroup hi σ) s)
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) :
    (coneChartAmbientHomeomorph hi hσ hB κ g x).1 = coneChartAmbient hi hσ hB κ x :=
  by
    have hRay : (Homeomorph.piCongrLeft κ) (coneChartEquiv hi hσ hB x).1 =
        fun a ↦ (coneChartEquiv hi hσ hB x).1 (κ.symm a) := by
      funext a
      simpa only [κ.apply_symm_apply] using
        (Homeomorph.piCongrLeft_apply_apply (Y := fun _ : Fin k ↦ ℂ) κ
          (coneChartEquiv hi hσ hB x).1 (κ.symm a))
    have hUnits : (fun c ↦ ((unitsHomeomorphNeZero
        ((coneChartEquiv hi hσ hB x).2 c) : {ζ : ℂ // ζ ≠ 0}) : ℂ)) =
        fun c ↦ ((coneChartEquiv hi hσ hB x).2 c : ℂ) := by
      funext c
      rw [unitsHomeomorphNeZero]
      rfl
    have hPair :
        ((Homeomorph.piCongrLeft κ) (coneChartEquiv hi hσ hB x).1,
            fun c ↦ ((unitsHomeomorphNeZero
              ((coneChartEquiv hi hσ hB x).2 c) : {ζ : ℂ // ζ ≠ 0}) : ℂ)) =
          coneChartAmbient hi hσ hB κ x := by
      rw [hRay, hUnits]
      rfl
    simpa [coneChartAmbientHomeomorph] using hPair

/-- The range of the ambient cone chart is exactly the mixed-chart locus. -/
@[simp]
theorem range_coneChartAmbient :
    Set.range (coneChartAmbient hi hσ hB κ) = mixedChartDomain k l := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact coneChartAmbient_mem_mixedChartDomain hi hσ hB κ x
  · intro hz
    refine ⟨(coneChartEquiv hi hσ hB).symm
      (fun ρ ↦ z.1 (κ ρ), fun c ↦ Units.mk0 (z.2 c) (mem_mixedChartDomain.1 hz c)), ?_⟩
    rw [coneChartAmbient]
    simp only [Equiv.apply_symm_apply]
    exact Prod.ext (funext fun a ↦ by simp) (funext fun c ↦ rfl)

@[simp]
theorem coneChartAmbientHomeomorph_symm_apply
    (g : AddGeneratingFamily (dualSemigroup hi σ) s) (z : {z // z ∈ mixedChartDomain k l}) :
    @Homeomorph.symm _ _ (affinePointTopology g) instTopologicalSpaceSubtype
        (coneChartAmbientHomeomorph hi hσ hB κ g) z =
      (coneChartEquiv hi hσ hB).symm
        (fun ρ ↦ z.1.1 (κ ρ), fun c ↦
          Units.mk0 (z.1.2 c) (mem_mixedChartDomain.1 z.2 c)) :=
  by
    have hUnits :
        (Homeomorph.piCongrRight fun _ : Fin l ↦
            (unitsHomeomorphNeZero (G₀ := ℂ)).symm)
            (fun c ↦ ⟨z.1.2 c, mem_mixedChartDomain.1 z.2 c⟩) =
          fun c ↦ Units.mk0 (z.1.2 c) (mem_mixedChartDomain.1 z.2 c) := by
      funext c
      apply Units.ext
      rw [Homeomorph.piCongrRight_apply]
      have h := congrArg Subtype.val
        ((unitsHomeomorphNeZero (G₀ := ℂ)).apply_symm_apply
          ⟨z.1.2 c, mem_mixedChartDomain.1 z.2 c⟩)
      rw [unitsHomeomorphNeZero] at h
      exact h
    have hPair :
        ((Homeomorph.piCongrLeft κ).symm z.1.1,
            (Homeomorph.piCongrRight fun _ : Fin l ↦
              (unitsHomeomorphNeZero (G₀ := ℂ)).symm)
              (fun c ↦ ⟨z.1.2 c, mem_mixedChartDomain.1 z.2 c⟩)) =
          (fun ρ ↦ z.1.1 (κ ρ), fun c ↦
            Units.mk0 (z.1.2 c) (mem_mixedChartDomain.1 z.2 c)) := by
      rw [hUnits]
      rfl
    simpa [coneChartAmbientHomeomorph] using
      congrArg (coneChartEquiv hi hσ hB).symm hPair

/-- Changing the basis extending the primitive ray generators acts on the ambient mixed coordinates
of the affine chart by the mixed monomial map of the transition block: each boundary coordinate is
kept and twisted by the complementary entries of its ray row, and the torus coordinates are
transformed by the complementary block of the transition matrix. -/
theorem mixedMonomialMap_ofTorusBlock_coneChartAmbient
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) :
    mixedMonomialMap (MixedExponent.ofTorusBlock
          (Matrix.of fun a c ↦ B'.toMatrix B (Sum.inl (κ.symm a)) (Sum.inr c))
          ((B'.toMatrix B).submatrix Sum.inr Sum.inr))
        (coneChartAmbient hi hσ hB κ x) = coneChartAmbient hi hσ hB' κ x := by
  refine Prod.ext (funext fun a ↦ ?_) (funext fun c ↦ ?_)
  · rw [mixedMonomialMap_fst_apply, coneChartAmbient_fst_apply,
      coneChartEquiv_fst_apply_basisChange hi hσ hB hB']
    refine congrArg₂ _ ?_ (prod_congr rfl fun c _ ↦ by simp)
    -- The identity boundary block leaves only the boundary coordinate indexed by `a`.
    rw [prod_eq_single a (fun a' _ hne ↦ by
      simp [Matrix.one_apply_ne (Ne.symm hne)]) (by simp)]
    simp
  · rw [mixedMonomialMap_snd_apply, coneChartAmbient_snd_apply,
      val_coneChartEquiv_snd_apply_basisChange hi hσ hB hB']
    exact prod_congr rfl fun c _ ↦ by simp

/-- The transition between the ambient mixed coordinates attached to two extending bases is the
mixed monomial map of the transition block, whose torus block is unimodular: the boundary
coordinates are kept and twisted. It is therefore a biholomorphism of the mixed-chart locus, by
`TauCeti.Toric.contDiffOn_basisChangeOpenPartialHomeomorph` and
`TauCeti.Toric.contDiffOn_basisChangeOpenPartialHomeomorph_symm`. -/
theorem basisChangeOpenPartialHomeomorph_coneChartAmbient
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) :
    basisChangeOpenPartialHomeomorph
        (Matrix.of fun a c ↦ B'.toMatrix B (Sum.inl (κ.symm a)) (Sum.inr c))
        ((B'.toMatrix B).submatrix Sum.inr Sum.inr)
        (isUnit_det_toMatrix_submatrix_inr hi hσ.salient hB hB')
        (coneChartAmbient hi hσ hB κ x) = coneChartAmbient hi hσ hB' κ x := by
  rw [basisChangeOpenPartialHomeomorph_coe]
  exact mixedMonomialMap_ofTorusBlock_coneChartAmbient hi hσ hB hB' κ x

end Ambient

end TauCeti.Toric

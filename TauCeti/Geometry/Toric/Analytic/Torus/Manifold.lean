/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import TauCeti.Analysis.Calculus.ContDiffZPow
public import TauCeti.Geometry.Toric.Analytic.Torus.Topology

/-!
# The complex manifold structure of the coordinate-free complex torus

A free presentation `e : (N →+ ℤ) ≃+ (ι →₀ ℤ)` of the character lattice, with `ι` finite, embeds
the complex torus `ComplexTorus N` openly into `ℂ^ι`, as the locus where every coordinate is
nonzero.  Mathlib's singleton-chart construction therefore makes the torus a complex manifold
modelled on `ℂ^ι`.

Although the chart names coordinates, the complex structure does not depend on the presentation:
in the coordinates of two presentations, every torus map induced by a lattice map, and in
particular the identity, is a Laurent monomial map, which is holomorphic where all coordinates are
invertible.  Character evaluations are holomorphic for the same reason.

## Main declarations

* `TauCeti.Toric.complexTorusChartedSpace`: the complex charted-space structure induced by a free
  presentation of the character lattice.
* `TauCeti.Toric.isManifold_complexTorusChartedSpace`: this charted space is a complex manifold.
* `TauCeti.Toric.complexTorusAmbient_complexTorusMap`: in coordinates, a torus map induced by a
  lattice map is a Laurent monomial map.
* `TauCeti.Toric.contMDiff_complexTorusMap`: torus maps induced by lattice maps are holomorphic.
* `TauCeti.Toric.contMDiff_id_complexTorusChartedSpace`: changing the presentation preserves the
  complex structure.
* `TauCeti.Toric.contMDiff_characterEvaluation`: character evaluations are holomorphic.

## References

* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §1.1 and §3.1.
* W. Fulton, *Introduction to Toric Varieties*, §1.1 and §2.1.
-/

public section

open scoped ContDiff Manifold
open Function Set Topology

namespace TauCeti.Toric

variable {N N' ι ι' : Type*} [AddCommGroup N] [AddCommGroup N']
  [Fintype ι] (e : IntegralCharacter N ≃+ (ι →₀ ℤ)) (e' : IntegralCharacter N' ≃+ (ι' →₀ ℤ))

/-- The complex charted-space structure on the torus induced by a free presentation of the
character lattice.  Its sole chart is the open embedding by the ambient coordinates. -/
@[instance_reducible]
noncomputable def complexTorusChartedSpace : ChartedSpace (ι → ℂ) (ComplexTorus N) :=
  (isOpenEmbedding_complexTorusAmbient e).singletonChartedSpace

/-- Every chart of the torus charted-space structure is the ambient coordinate map. -/
theorem complexTorusChartedSpace_chartAt (x : ComplexTorus N) :
    ⇑(@chartAt (ι → ℂ) _ (ComplexTorus N) _ (complexTorusChartedSpace e) x) =
      complexTorusAmbient e :=
  (isOpenEmbedding_complexTorusAmbient e).singletonChartedSpace_chartAt_eq

/-- The target of every chart of the torus charted-space structure is the locus where every
coordinate is nonzero. -/
theorem complexTorusChartedSpace_chartAt_target (x : ComplexTorus N) :
    (@chartAt (ι → ℂ) _ (ComplexTorus N) _ (complexTorusChartedSpace e) x).target =
      {z : ι → ℂ | ∀ i, z i ≠ 0} := by
  rw [OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq
      ((isOpenEmbedding_complexTorusAmbient e).toOpenPartialHomeomorph (complexTorusAmbient e))
      (IsOpenEmbedding.toOpenPartialHomeomorph_source _ _),
    IsOpenEmbedding.toOpenPartialHomeomorph_target, range_complexTorusAmbient]

/-- The complex torus, with the chart induced by a free presentation of its character lattice, is
a complex manifold to every differentiability order. -/
theorem isManifold_complexTorusChartedSpace (n : ℕ∞ω) :
    let _ := complexTorusChartedSpace e
    IsManifold 𝓘(ℂ, ι → ℂ) n (ComplexTorus N) :=
  (isOpenEmbedding_complexTorusAmbient e).isManifold_singleton

/-- The ambient coordinates are holomorphic for the charted-space structure they induce. -/
theorem contMDiff_complexTorusAmbient (n : ℕ∞ω) :
    let _ := complexTorusChartedSpace e
    ContMDiff 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, ι → ℂ) n (complexTorusAmbient e) :=
  contMDiff_isOpenEmbedding (isOpenEmbedding_complexTorusAmbient e)

/-- A Laurent monomial in the ambient coordinates is a holomorphic function on the torus. -/
theorem contMDiff_prod_zpow_complexTorusAmbient (a : ι → ℤ) (n : ℕ∞ω) :
    let _ := complexTorusChartedSpace e
    ContMDiff 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, ℂ) n
      fun x : ComplexTorus N ↦ ∏ i, complexTorusAmbient e x i ^ a i := by
  let _ := complexTorusChartedSpace e
  have hL : ContDiffOn ℂ n (fun z : ι → ℂ ↦ ∏ i, z i ^ a i) {z : ι → ℂ | ∀ i, z i ≠ 0} :=
    fun _ hz ↦ (contDiffAt_prod fun i _ ↦
      (contDiff_apply ℂ ℂ i).contDiffAt.zpow (Or.inl (hz i))).contDiffWithinAt
  exact hL.contMDiffOn.comp_contMDiff (contMDiff_complexTorusAmbient e n)
    fun x ↦ complexTorusAmbient_ne_zero e x

/-- Evaluation of an integral character is a holomorphic map from the torus to `ℂˣ`. -/
theorem contMDiff_characterEvaluation (m : IntegralCharacter N) (n : ℕ∞ω) :
    let _ := complexTorusChartedSpace e
    ContMDiff 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, ℂ) n (characterEvaluation m) := by
  let _ := complexTorusChartedSpace e
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  refine (contMDiff_prod_zpow_complexTorusAmbient e (e m) n).congr fun x ↦ ?_
  rw [comp_apply, characterEvaluation_apply, complexTorus_apply_eq_prod_zpow_of_fintype e x m,
    Units.coe_prod]
  simp only [Units.val_zpow_eq_zpow_val, complexTorusAmbient_apply, complexTorusCoordinates_apply]

/-- In the coordinates of two free presentations, the torus map induced by a lattice map `f` is
the Laurent monomial map whose exponents are the coordinates of the pulled-back coordinate
characters. -/
theorem complexTorusAmbient_complexTorusMap (f : N →+ N') (x : ComplexTorus N) (j : ι') :
    complexTorusAmbient e' (complexTorusMap f x) j =
      ∏ i, complexTorusAmbient e x i ^
        e (AddMonoidHom.compHom' f (e'.symm (Finsupp.single j 1))) i := by
  rw [complexTorusAmbient_apply, complexTorusMap_apply, characterEvaluation_apply,
    complexTorus_apply_eq_prod_zpow_of_fintype e x, Units.coe_prod]
  simp only [Units.val_zpow_eq_zpow_val, complexTorusAmbient_apply, complexTorusCoordinates_apply]

/-- The torus map induced by a lattice map is holomorphic for the charted-space structures
induced by any free presentations of the two character lattices. -/
theorem contMDiff_complexTorusMap [Fintype ι'] (f : N →+ N') (n : ℕ∞ω) :
    @ContMDiff ℂ _ (ι → ℂ) _ _ (ι → ℂ) _ 𝓘(ℂ, ι → ℂ)
      (ComplexTorus N) _ (complexTorusChartedSpace e)
      (ι' → ℂ) _ _ (ι' → ℂ) _ 𝓘(ℂ, ι' → ℂ)
      (ComplexTorus N') _ (complexTorusChartedSpace e') n (complexTorusMap f) := by
  let _ := complexTorusChartedSpace e
  apply ContMDiff.of_comp_isOpenEmbedding (isOpenEmbedding_complexTorusAmbient e')
  rw [contMDiff_pi_space]
  intro j
  exact (contMDiff_prod_zpow_complexTorusAmbient e _ n).congr fun x ↦
    complexTorusAmbient_complexTorusMap e e' f x j

/-- The identity map between the torus equipped with the charted-space structures of two free
presentations of its character lattice is holomorphic: the complex structure does not depend on
the presentation. -/
theorem contMDiff_id_complexTorusChartedSpace [Fintype ι']
    (e₂ : IntegralCharacter N ≃+ (ι' →₀ ℤ)) (n : ℕ∞ω) :
    @ContMDiff ℂ _ (ι → ℂ) _ _ (ι → ℂ) _ 𝓘(ℂ, ι → ℂ)
      (ComplexTorus N) _ (complexTorusChartedSpace e)
      (ι' → ℂ) _ _ (ι' → ℂ) _ 𝓘(ℂ, ι' → ℂ)
      (ComplexTorus N) _ (complexTorusChartedSpace e₂) n id := by
  have h := contMDiff_complexTorusMap e e₂ (AddMonoidHom.id N) n
  rwa [complexTorusMap_id, MonoidHom.coe_id] at h

end TauCeti.Toric

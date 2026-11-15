/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Unramified.Frobenius
public import TauCeti.Topology.Algebra.PointTopology.Scheme.MapCodomain
import TauCeti.Topology.Algebra.ValuativeRel.ContinuousRingHom

/-!
# Rational and integral points as Frobenius fixed points over `Breve E`

Let `E` be a nonarchimedean local field and `Breve E` its completed maximal unramified extension,
equipped with the arithmetic Frobenius `σ = frobenius E` and its integral restriction
`integerFrobenius E : 𝒪[Breve E] ≃ₐ[𝒪[E]] 𝒪[Breve E]`. Because `algebraMap E (Breve E)` and
`algebraMap 𝒪[E] 𝒪[Breve E]` are closed embeddings whose images are the fixed loci of Frobenius
(`isClosedEmbedding_algebraMap`, `fixedPoints_frobenius`, `fixedPoints_integerFrobenius`), the
general fixed-locus descent for point topologies specializes to identify `E`-points and
`𝒪[E]`-points with Frobenius-fixed points over `Breve E` and `𝒪[Breve E]`:

* **Affine `E`-algebras (`A →ₐ[E] Breve E`):** `galAction τ` and `frobenius E` act by
  homeomorphisms (`galActionPointsHomeomorph`, `frobeniusPointsHomeomorph`), post-composition with
  `Algebra.ofId E (Breve E)` is a closed embedding (`isClosedEmbedding_points_breve`), and its
  image is the `σ`-fixed locus (`points_eq_fixedPoints`), giving a homeomorphism
  `(A →ₐ[E] E) ≃ₜ {x : A →ₐ[E] Breve E // σ.comp x = x}` (`pointsHomeomorphFixedPoints`). For
  `n ≠ 0`, the `σ^n`-fixed points descend to the degree-`n` unramified extension `E_n`
  (`points_eq_fixedPoints_pow`).
* **Affine group schemes (`WithConv (H →ₐ[E] Breve E)`):** for a Hopf algebra `H` over `E`,
  `AlgHom.mapValue (Algebra.ofId E (Breve E))` is a closed embedding whose image subgroup is the
  `σ`-fixed subgroup (`range_mapValue_breve_eq_fixedPoints`), inducing a topological-group
  isomorphism `G(E) ≃ₜ* G(Breve E)^σ` (`groupPointsContinuousMulEquivFixedPoints`).
* **Integral points over `𝒪[E]` and `𝒪[Breve E]`:** both intrinsically for `𝒪[Breve E]`-valued
  points (`integralPoints_eq_fixedPoints`, `integralPointsHomeomorphFixedPoints`,
  `integralGroupPointsContinuousMulEquivFixedPoints`) and inside `Breve E`-valued points via
  integrality reflection (`integralPoints_in_breve_eq_fixedPoints`,
  `range_mapValue_integer_in_breve_eq_fixedPoints`).
* **Scheme-valued points (`SchemePointTopology.Points`):** for any `E`-scheme `X` and any
  `𝒪[E]`-scheme `𝒳`, `X(E) ≃ₜ X(Breve E)^σ` (`schemePointsHomeomorphFixedPoints`) and
  `𝒳(𝒪[E]) ≃ₜ 𝒳(𝒪[Breve E])^σ` (`integralSchemePointsHomeomorphFixedPoints`).

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1 and Prop. 3.1, pp. 2–4.
* X. He, *Some results on affine Deligne–Lusztig varieties*, Proc. ICM 2018, §4.3, p. 12.
* R. E. Kottwitz, *Isocrystals with additional structure. II*, Compositio Math. 109 (1997), §1.1.
-/

public section
noncomputable section

open CategoryTheory AlgebraicGeometry Topology WithConv ValuativeRel IntermediateField
open scoped TauCeti.PointTopology TauCeti.SchemePointTopology

namespace TauCeti.MaxUnramifiedCompletion

section IntegerTopology

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- The inverse of the Galois action of `τ` on `Breve E` is continuous. -/
@[fun_prop, continuity]
theorem continuous_galAction_symm (τ : Gal(Unramified E/E)) :
    Continuous (galAction τ).symm := by
  rw [galAction_symm]
  exact continuous_galAction τ⁻¹

/-- The inverse of Frobenius on `Breve E` is continuous. -/
@[fun_prop, continuity]
theorem continuous_frobenius_symm : Continuous (frobenius E).symm := by
  rw [frobenius_eq_galAction]
  exact continuous_galAction_symm (unramifiedFrobenius E)

variable (E) in
/-- **The valuation ring `𝒪[E]` embeds into `𝒪[Breve E]` as a closed subring.** -/
theorem isClosedEmbedding_algebraMap_integer :
    IsClosedEmbedding (algebraMap 𝒪[E] 𝒪[Breve E]) :=
  TauCeti.isClosedEmbedding_algebraMap_integerRing_of_isClosedEmbedding
    (isClosedEmbedding_algebraMap E)

/-- The integral Frobenius `integerFrobenius E` on `𝒪[Breve E]` is continuous. -/
@[fun_prop, continuity]
theorem continuous_integerFrobenius : Continuous (integerFrobenius E) :=
  continuous_induced_rng.2 <| by
    simpa only [Function.comp_def, coe_integerFrobenius_apply] using
      continuous_frobenius.comp continuous_subtype_val

/-- The inverse of `integerFrobenius E` on `𝒪[Breve E]` is continuous. -/
@[fun_prop, continuity]
theorem continuous_integerFrobenius_symm : Continuous (integerFrobenius E).symm :=
  continuous_induced_rng.2 <| by
    simpa only [Function.comp_def, coe_integerFrobenius_symm_apply] using
      continuous_frobenius_symm.comp continuous_subtype_val

end IntegerTopology

section AffinePoints

variable {E A : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [Semiring A] [Algebra E A]

/-- Every `τ ∈ Gal(E^{ur}/E)` acts as a homeomorphism on the space of `Breve E`-points of `A`. -/
def galActionPointsHomeomorph (A : Type*) [Semiring A] [Algebra E A]
    (τ : Gal(Unramified E/E)) : (A →ₐ[E] Breve E) ≃ₜ (A →ₐ[E] Breve E) :=
  (galAction τ).pointsHomeomorph A (continuous_galAction τ) (continuous_galAction_symm τ)

/-- `galActionPointsHomeomorph` post-composes a point with `galAction τ`. -/
@[simp]
theorem galActionPointsHomeomorph_apply (τ : Gal(Unramified E/E)) (x : A →ₐ[E] Breve E) :
    galActionPointsHomeomorph A τ x = (galAction τ).toAlgHom.comp x :=
  (galAction τ).pointsHomeomorph_apply _ _ x

/-- The inverse of `galActionPointsHomeomorph A τ` is `galActionPointsHomeomorph A τ⁻¹`. -/
@[simp]
theorem galActionPointsHomeomorph_symm (τ : Gal(Unramified E/E)) :
    (galActionPointsHomeomorph A τ).symm = galActionPointsHomeomorph A τ⁻¹ := by
  ext x a
  simp [galActionPointsHomeomorph, galAction_symm]

variable (E A) in
/-- Arithmetic Frobenius acts as a homeomorphism on the space of `Breve E`-points of `A`. -/
def frobeniusPointsHomeomorph : (A →ₐ[E] Breve E) ≃ₜ (A →ₐ[E] Breve E) :=
  (frobenius E).pointsHomeomorph A continuous_frobenius continuous_frobenius_symm

/-- `frobeniusPointsHomeomorph` post-composes a point with `frobenius E`. -/
@[simp]
theorem frobeniusPointsHomeomorph_apply (x : A →ₐ[E] Breve E) :
    frobeniusPointsHomeomorph E A x = (frobenius E).toAlgHom.comp x :=
  (frobenius E).pointsHomeomorph_apply _ _ x

/-- `(frobeniusPointsHomeomorph E A).symm` post-composes a point with `(frobenius E).symm`. -/
@[simp]
theorem frobeniusPointsHomeomorph_symm_apply (x : A →ₐ[E] Breve E) :
    (frobeniusPointsHomeomorph E A).symm x = (frobenius E).symm.toAlgHom.comp x := by
  rw [frobeniusPointsHomeomorph, AlgEquiv.pointsHomeomorph_symm]
  exact (frobenius E).symm.pointsHomeomorph_apply _ _ x

variable (E A) in
/-- Base change of affine points from `E` to `Breve E` is a closed embedding. -/
theorem isClosedEmbedding_points_breve :
    IsClosedEmbedding fun x : A →ₐ[E] E ↦ (Algebra.ofId E (Breve E)).comp x :=
  PointTopology.isClosedEmbedding_map_codomain (Algebra.ofId E (Breve E))
    (by simpa only [funext (Algebra.ofId_apply (R := E) (Breve E))] using
      isClosedEmbedding_algebraMap E)

variable (E A) in
/-- **Rational points of an `E`-algebra are the Frobenius-fixed `Breve E`-points.** -/
theorem points_eq_fixedPoints :
    {x : A →ₐ[E] Breve E | (frobenius E).toAlgHom.comp x = x} =
      Set.range fun x : A →ₐ[E] E ↦ (Algebra.ofId E (Breve E)).comp x :=
  (PointTopology.range_comp_eq_fixedPoints (Algebra.ofId E (Breve E)).injective
    (frobenius E).toAlgHom
    (by simpa only [AlgEquiv.coe_toAlgHom, funext (Algebra.ofId_apply (R := E) (Breve E))] using
      fixedPoints_frobenius E)).symm

variable (E A) in
/-- **Homeomorphism `X(E) ≃ₜ X(Breve E)^σ` for affine `E`-schemes.** -/
def pointsHomeomorphFixedPoints :
    (A →ₐ[E] E) ≃ₜ {x : A →ₐ[E] Breve E // (frobenius E).toAlgHom.comp x = x} :=
  PointTopology.fixedPointsHomeomorph (ψ := Algebra.ofId E (Breve E)) A
    (by simpa only [funext (Algebra.ofId_apply (R := E) (Breve E))] using
      (isClosedEmbedding_algebraMap E).isEmbedding)
    (by simpa only [AlgEquiv.coe_toAlgHom, funext (Algebra.ofId_apply (R := E) (Breve E))] using
      fixedPoints_frobenius E)

/-- Coercing `pointsHomeomorphFixedPoints` to a `Breve E`-point post-composes with
`Algebra.ofId E (Breve E)`. -/
@[simp]
theorem coe_pointsHomeomorphFixedPoints_apply (x : A →ₐ[E] E) :
    (pointsHomeomorphFixedPoints E A x : A →ₐ[E] Breve E) =
      (Algebra.ofId E (Breve E)).comp x :=
  PointTopology.coe_fixedPointsHomeomorph_apply _ _ x

/-- Post-composing `(pointsHomeomorphFixedPoints E A).symm y` with `Algebra.ofId E (Breve E)`
recovers `y`. -/
@[simp]
theorem comp_pointsHomeomorphFixedPoints_symm
    (y : {x : A →ₐ[E] Breve E // (frobenius E).toAlgHom.comp x = x}) :
    (Algebra.ofId E (Breve E)).comp ((pointsHomeomorphFixedPoints E A).symm y) = y.1 := by
  rw [← coe_pointsHomeomorphFixedPoints_apply, Homeomorph.apply_symm_apply]

variable (E) in
/-- The canonical `E`-algebra embedding of the degree-`n` unramified extension `E_n` into
`Breve E`. -/
def unramifiedExtensionToBreve (n : ℕ) :
    unramifiedExtension E (AlgebraicClosure E) n →ₐ[E] Breve E :=
  (IsScalarTower.toAlgHom E (Unramified E) (Breve E)).comp
    (inclusion (unramifiedExtension_le_maximalUnramifiedExtension E (AlgebraicClosure E) n))

/-- `unramifiedExtensionToBreve E n` coerces through `Unramified E` into `Breve E`. -/
@[simp]
theorem unramifiedExtensionToBreve_apply (n : ℕ)
    (z : unramifiedExtension E (AlgebraicClosure E) n) :
    unramifiedExtensionToBreve E n z =
      ((inclusion (unramifiedExtension_le_maximalUnramifiedExtension E (AlgebraicClosure E) n) z :
        Unramified E) : Breve E) := by
  simp [unramifiedExtensionToBreve, UniformSpace.Completion.algebraMap_def]

/-- **For `n ≠ 0`, the `σ^n`-fixed `Breve E`-points of `A` are the points over the degree-`n`
unramified extension `E_n`.** -/
theorem points_eq_fixedPoints_pow {n : ℕ} (hn : n ≠ 0) :
    {x : A →ₐ[E] Breve E | (frobenius E ^ n).toAlgHom.comp x = x} =
      Set.range fun x : A →ₐ[E] unramifiedExtension E (AlgebraicClosure E) n ↦
        (unramifiedExtensionToBreve E n).comp x := by
  refine (PointTopology.range_comp_eq_fixedPoints (unramifiedExtensionToBreve E n).injective
    (frobenius E ^ n).toAlgHom ?_).symm
  simp only [AlgEquiv.coe_toAlgHom, fixedPoints_frobenius_pow hn]
  ext z
  simp [Function.comp_apply]

end AffinePoints

section AffineGroupPoints

variable {E H : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- Every `τ ∈ Gal(E^{ur}/E)` acts as a topological multiplicative automorphism on
`WithConv (H →ₐ[E] Breve E)`. -/
def galActionGroupContinuousMulEquiv (H : Type*) [Semiring H] [Bialgebra E H]
    (τ : Gal(Unramified E/E)) :
    WithConv (H →ₐ[E] Breve E) ≃ₜ* WithConv (H →ₐ[E] Breve E) :=
  (galAction τ).mapValueContinuousMulEquiv H (continuous_galAction τ) (continuous_galAction_symm τ)

/-- `galActionGroupContinuousMulEquiv` acts via `AlgHom.mapValue (galAction τ).toAlgHom`. -/
@[simp]
theorem galActionGroupContinuousMulEquiv_apply [Semiring H] [Bialgebra E H]
    (τ : Gal(Unramified E/E)) (f : WithConv (H →ₐ[E] Breve E)) :
    galActionGroupContinuousMulEquiv H τ f = AlgHom.mapValue (galAction τ).toAlgHom f :=
  (galAction τ).mapValueContinuousMulEquiv_apply _ _ f

/-- The inverse of `galActionGroupContinuousMulEquiv H τ` is
`galActionGroupContinuousMulEquiv H τ⁻¹`. -/
@[simp]
theorem galActionGroupContinuousMulEquiv_symm [Semiring H] [Bialgebra E H]
    (τ : Gal(Unramified E/E)) :
    (galActionGroupContinuousMulEquiv H τ).symm = galActionGroupContinuousMulEquiv H τ⁻¹ := by
  ext f
  simp [galActionGroupContinuousMulEquiv, galAction_symm]

variable (E H) in
/-- Arithmetic Frobenius acts as a topological multiplicative automorphism on
`WithConv (H →ₐ[E] Breve E)`. -/
def frobeniusGroupContinuousMulEquiv [Semiring H] [Bialgebra E H] :
    WithConv (H →ₐ[E] Breve E) ≃ₜ* WithConv (H →ₐ[E] Breve E) :=
  (frobenius E).mapValueContinuousMulEquiv H continuous_frobenius continuous_frobenius_symm

/-- `frobeniusGroupContinuousMulEquiv` acts via `AlgHom.mapValue (frobenius E).toAlgHom`. -/
@[simp]
theorem frobeniusGroupContinuousMulEquiv_apply [Semiring H] [Bialgebra E H]
    (f : WithConv (H →ₐ[E] Breve E)) :
    frobeniusGroupContinuousMulEquiv E H f = AlgHom.mapValue (frobenius E).toAlgHom f :=
  (frobenius E).mapValueContinuousMulEquiv_apply _ _ f

/-- `(frobeniusGroupContinuousMulEquiv E H).symm` acts via
`AlgHom.mapValue (frobenius E).symm.toAlgHom`. -/
@[simp]
theorem frobeniusGroupContinuousMulEquiv_symm_apply [Semiring H] [Bialgebra E H]
    (f : WithConv (H →ₐ[E] Breve E)) :
    (frobeniusGroupContinuousMulEquiv E H).symm f =
      AlgHom.mapValue (frobenius E).symm.toAlgHom f := by
  rw [frobeniusGroupContinuousMulEquiv, AlgEquiv.mapValueContinuousMulEquiv_symm]
  exact (frobenius E).symm.mapValueContinuousMulEquiv_apply _ _ f

variable (E H) in
/-- Base change `G(E) → G(Breve E)` on convolution monoids of points is a closed embedding. -/
theorem isClosedEmbedding_mapValue_breve [Semiring H] [Bialgebra E H] :
    IsClosedEmbedding (AlgHom.mapValue (H := H) (Algebra.ofId E (Breve E))) :=
  AlgHom.isClosedEmbedding_mapValue
    (by simpa only [funext (Algebra.ofId_apply (R := E) (Breve E))] using
      isClosedEmbedding_algebraMap E)

variable (E H) in
/-- For a Hopf algebra `H` over `E`, the image subgroup of `G(E)` in `G(Breve E)` is the
Frobenius-fixed subgroup. -/
theorem range_mapValue_breve_eq_fixedPoints [Semiring H] [HopfAlgebra E H] :
    MonoidHom.range (G := WithConv (H →ₐ[E] E)) (N := WithConv (H →ₐ[E] Breve E))
        (AlgHom.mapValue (H := H) (Algebra.ofId E (Breve E))) =
      MonoidHom.eqLocus (G := WithConv (H →ₐ[E] Breve E))
        (AlgHom.mapValue (H := H) (frobenius E).toAlgHom) (MonoidHom.id _) :=
  PointTopology.range_mapValue_eq_eqLocus (Algebra.ofId E (Breve E)).injective
    (frobenius E).toAlgHom
    (by simpa only [AlgEquiv.coe_toAlgHom, funext (Algebra.ofId_apply (R := E) (Breve E))] using
      fixedPoints_frobenius E)

variable (E H) in
/-- **Topological-group isomorphism `G(E) ≃ₜ* G(Breve E)^σ` for affine `E`-group schemes.** -/
def groupPointsContinuousMulEquivFixedPoints [Semiring H] [HopfAlgebra E H] :
    WithConv (H →ₐ[E] E) ≃ₜ*
      MonoidHom.eqLocus (G := WithConv (H →ₐ[E] Breve E))
        (AlgHom.mapValue (H := H) (frobenius E).toAlgHom) (MonoidHom.id _) :=
  PointTopology.fixedPointsContinuousMulEquiv (ψ := Algebra.ofId E (Breve E)) H
    (by simpa only [funext (Algebra.ofId_apply (R := E) (Breve E))] using
      (isClosedEmbedding_algebraMap E).isEmbedding)
    (by simpa only [AlgEquiv.coe_toAlgHom, funext (Algebra.ofId_apply (R := E) (Breve E))] using
      fixedPoints_frobenius E)

/-- Coercing `groupPointsContinuousMulEquivFixedPoints` to `WithConv (H →ₐ[E] Breve E)` applies
`AlgHom.mapValue (Algebra.ofId E (Breve E))`. -/
@[simp]
theorem coe_groupPointsContinuousMulEquivFixedPoints_apply [Semiring H] [HopfAlgebra E H]
    (f : WithConv (H →ₐ[E] E)) :
    (groupPointsContinuousMulEquivFixedPoints E H f : WithConv (H →ₐ[E] Breve E)) =
      AlgHom.mapValue (Algebra.ofId E (Breve E)) f :=
  PointTopology.coe_fixedPointsContinuousMulEquiv_apply _ _ f

/-- Applying `AlgHom.mapValue (Algebra.ofId E (Breve E))` to the inverse of
`groupPointsContinuousMulEquivFixedPoints` recovers the Frobenius-fixed point. -/
theorem mapValue_groupPointsContinuousMulEquivFixedPoints_symm [Semiring H] [HopfAlgebra E H]
    (g : MonoidHom.eqLocus (G := WithConv (H →ₐ[E] Breve E))
      (AlgHom.mapValue (H := H) (frobenius E).toAlgHom) (MonoidHom.id _)) :
    AlgHom.mapValue (Algebra.ofId E (Breve E))
      ((groupPointsContinuousMulEquivFixedPoints E H).symm g) = g.1 := by
  rw [← coe_groupPointsContinuousMulEquivFixedPoints_apply, ContinuousMulEquiv.apply_symm_apply]

/-- Post-composing the underlying algebra map of
`(groupPointsContinuousMulEquivFixedPoints E H).symm g` with `Algebra.ofId E (Breve E)` recovers
`g.1.ofConv`. -/
@[simp]
theorem comp_ofConv_groupPointsContinuousMulEquivFixedPoints_symm [Semiring H] [HopfAlgebra E H]
    (g : MonoidHom.eqLocus (G := WithConv (H →ₐ[E] Breve E))
      (AlgHom.mapValue (H := H) (frobenius E).toAlgHom) (MonoidHom.id _)) :
    (Algebra.ofId E (Breve E)).comp
      ((groupPointsContinuousMulEquivFixedPoints E H).symm g).ofConv = g.1.ofConv := by
  simpa only [AlgHom.mapValue_apply, ← WithConv.ofConv_injective.eq_iff, ofConv_toConv] using
    mapValue_groupPointsContinuousMulEquivFixedPoints_symm g

end AffineGroupPoints

section IntegralPoints

variable {E A H : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

variable (E A) in
/-- Integral Frobenius acts as a homeomorphism on `𝒪[Breve E]`-points of an `𝒪[E]`-algebra `A`. -/
def integerFrobeniusPointsHomeomorph [Semiring A] [Algebra 𝒪[E] A] :
    (A →ₐ[𝒪[E]] 𝒪[Breve E]) ≃ₜ (A →ₐ[𝒪[E]] 𝒪[Breve E]) :=
  (integerFrobenius E).pointsHomeomorph A continuous_integerFrobenius
    continuous_integerFrobenius_symm

/-- `integerFrobeniusPointsHomeomorph` post-composes a point with `integerFrobenius E`. -/
@[simp]
theorem integerFrobeniusPointsHomeomorph_apply [Semiring A] [Algebra 𝒪[E] A]
    (x : A →ₐ[𝒪[E]] 𝒪[Breve E]) :
    integerFrobeniusPointsHomeomorph E A x = (integerFrobenius E).toAlgHom.comp x :=
  (integerFrobenius E).pointsHomeomorph_apply _ _ x

/-- `(integerFrobeniusPointsHomeomorph E A).symm` post-composes a point with
`(integerFrobenius E).symm`. -/
@[simp]
theorem integerFrobeniusPointsHomeomorph_symm_apply [Semiring A] [Algebra 𝒪[E] A]
    (x : A →ₐ[𝒪[E]] 𝒪[Breve E]) :
    (integerFrobeniusPointsHomeomorph E A).symm x = (integerFrobenius E).symm.toAlgHom.comp x := by
  rw [integerFrobeniusPointsHomeomorph, AlgEquiv.pointsHomeomorph_symm]
  exact (integerFrobenius E).symm.pointsHomeomorph_apply _ _ x

variable (E A) in
/-- Base change of integral affine points from `𝒪[E]` to `𝒪[Breve E]` is a closed embedding. -/
theorem isClosedEmbedding_integralPoints_breve [Semiring A] [Algebra 𝒪[E] A] :
    IsClosedEmbedding fun x : A →ₐ[𝒪[E]] 𝒪[E] ↦ (Algebra.ofId 𝒪[E] 𝒪[Breve E]).comp x :=
  PointTopology.isClosedEmbedding_map_codomain (Algebra.ofId 𝒪[E] 𝒪[Breve E])
    (by simpa only [funext (Algebra.ofId_apply (R := 𝒪[E]) 𝒪[Breve E])] using
      isClosedEmbedding_algebraMap_integer E)

variable (E A) in
/-- **Integral points over `𝒪[E]` are the Frobenius-fixed `𝒪[Breve E]`-points.** -/
theorem integralPoints_eq_fixedPoints [Semiring A] [Algebra 𝒪[E] A] :
    {x : A →ₐ[𝒪[E]] 𝒪[Breve E] | (integerFrobenius E).toAlgHom.comp x = x} =
      Set.range fun x : A →ₐ[𝒪[E]] 𝒪[E] ↦ (Algebra.ofId 𝒪[E] 𝒪[Breve E]).comp x :=
  (PointTopology.range_comp_eq_fixedPoints
    (ψ := Algebra.ofId 𝒪[E] 𝒪[Breve E])
    (by simpa only [funext (Algebra.ofId_apply (R := 𝒪[E]) 𝒪[Breve E])] using
      (isClosedEmbedding_algebraMap_integer E).injective)
    (integerFrobenius E).toAlgHom
    (by simpa only [AlgEquiv.coe_toAlgHom,
        funext (Algebra.ofId_apply (R := 𝒪[E]) 𝒪[Breve E])] using
      fixedPoints_integerFrobenius E)).symm

variable (E A) in
/-- **Homeomorphism `𝒳(𝒪[E]) ≃ₜ 𝒳(𝒪[Breve E])^σ` for affine `𝒪[E]`-schemes.** -/
def integralPointsHomeomorphFixedPoints [Semiring A] [Algebra 𝒪[E] A] :
    (A →ₐ[𝒪[E]] 𝒪[E]) ≃ₜ
      {x : A →ₐ[𝒪[E]] 𝒪[Breve E] // (integerFrobenius E).toAlgHom.comp x = x} :=
  PointTopology.fixedPointsHomeomorph (ψ := Algebra.ofId 𝒪[E] 𝒪[Breve E]) A
    (by simpa only [funext (Algebra.ofId_apply (R := 𝒪[E]) 𝒪[Breve E])] using
      (isClosedEmbedding_algebraMap_integer E).isEmbedding)
    (by simpa only [AlgEquiv.coe_toAlgHom,
        funext (Algebra.ofId_apply (R := 𝒪[E]) 𝒪[Breve E])] using
      fixedPoints_integerFrobenius E)

/-- Coercing `integralPointsHomeomorphFixedPoints` to an `𝒪[Breve E]`-point post-composes with
`Algebra.ofId 𝒪[E] 𝒪[Breve E]`. -/
@[simp]
theorem coe_integralPointsHomeomorphFixedPoints_apply [Semiring A] [Algebra 𝒪[E] A]
    (x : A →ₐ[𝒪[E]] 𝒪[E]) :
    (integralPointsHomeomorphFixedPoints E A x : A →ₐ[𝒪[E]] 𝒪[Breve E]) =
      (Algebra.ofId 𝒪[E] 𝒪[Breve E]).comp x :=
  PointTopology.coe_fixedPointsHomeomorph_apply _ _ x

/-- Post-composing `(integralPointsHomeomorphFixedPoints E A).symm y` with
`Algebra.ofId 𝒪[E] 𝒪[Breve E]` recovers `y`. -/
@[simp]
theorem comp_integralPointsHomeomorphFixedPoints_symm [Semiring A] [Algebra 𝒪[E] A]
    (y : {x : A →ₐ[𝒪[E]] 𝒪[Breve E] // (integerFrobenius E).toAlgHom.comp x = x}) :
    (Algebra.ofId 𝒪[E] 𝒪[Breve E]).comp
      ((integralPointsHomeomorphFixedPoints E A).symm y) = y.1 := by
  rw [← coe_integralPointsHomeomorphFixedPoints_apply, Homeomorph.apply_symm_apply]

variable (E H) in
/-- **Topological-group isomorphism `𝒢(𝒪[E]) ≃ₜ* 𝒢(𝒪[Breve E])^σ` for affine `𝒪[E]`-group
schemes.** -/
def integralGroupPointsContinuousMulEquivFixedPoints [Semiring H] [HopfAlgebra 𝒪[E] H] :
    WithConv (H →ₐ[𝒪[E]] 𝒪[E]) ≃ₜ*
      MonoidHom.eqLocus (G := WithConv (H →ₐ[𝒪[E]] 𝒪[Breve E]))
        (AlgHom.mapValue (H := H) (integerFrobenius E).toAlgHom) (MonoidHom.id _) :=
  PointTopology.fixedPointsContinuousMulEquiv (ψ := Algebra.ofId 𝒪[E] 𝒪[Breve E]) H
    (by simpa only [funext (Algebra.ofId_apply (R := 𝒪[E]) 𝒪[Breve E])] using
      (isClosedEmbedding_algebraMap_integer E).isEmbedding)
    (by simpa only [AlgEquiv.coe_toAlgHom,
        funext (Algebra.ofId_apply (R := 𝒪[E]) 𝒪[Breve E])] using
      fixedPoints_integerFrobenius E)

/-- Coercing `integralGroupPointsContinuousMulEquivFixedPoints` to
`WithConv (H →ₐ[𝒪[E]] 𝒪[Breve E])` applies `AlgHom.mapValue (Algebra.ofId 𝒪[E] 𝒪[Breve E])`. -/
@[simp]
theorem coe_integralGroupPointsContinuousMulEquivFixedPoints_apply [Semiring H]
    [HopfAlgebra 𝒪[E] H] (f : WithConv (H →ₐ[𝒪[E]] 𝒪[E])) :
    (integralGroupPointsContinuousMulEquivFixedPoints E H f : WithConv (H →ₐ[𝒪[E]] 𝒪[Breve E])) =
      AlgHom.mapValue (Algebra.ofId 𝒪[E] 𝒪[Breve E]) f :=
  PointTopology.coe_fixedPointsContinuousMulEquiv_apply _ _ f

/-- Applying `AlgHom.mapValue (Algebra.ofId 𝒪[E] 𝒪[Breve E])` to the inverse of
`integralGroupPointsContinuousMulEquivFixedPoints` recovers the Frobenius-fixed point. -/
theorem mapValue_integralGroupPointsContinuousMulEquivFixedPoints_symm [Semiring H]
    [HopfAlgebra 𝒪[E] H]
    (g : MonoidHom.eqLocus (G := WithConv (H →ₐ[𝒪[E]] 𝒪[Breve E]))
      (AlgHom.mapValue (H := H) (integerFrobenius E).toAlgHom) (MonoidHom.id _)) :
    AlgHom.mapValue (Algebra.ofId 𝒪[E] 𝒪[Breve E])
      ((integralGroupPointsContinuousMulEquivFixedPoints E H).symm g) = g.1 := by
  rw [← coe_integralGroupPointsContinuousMulEquivFixedPoints_apply,
    ContinuousMulEquiv.apply_symm_apply]

/-- Post-composing the underlying algebra map of
`(integralGroupPointsContinuousMulEquivFixedPoints E H).symm g` with
`Algebra.ofId 𝒪[E] 𝒪[Breve E]` recovers `g.1.ofConv`. -/
@[simp]
theorem comp_ofConv_integralGroupPointsContinuousMulEquivFixedPoints_symm [Semiring H]
    [HopfAlgebra 𝒪[E] H]
    (g : MonoidHom.eqLocus (G := WithConv (H →ₐ[𝒪[E]] 𝒪[Breve E]))
      (AlgHom.mapValue (H := H) (integerFrobenius E).toAlgHom) (MonoidHom.id _)) :
    (Algebra.ofId 𝒪[E] 𝒪[Breve E]).comp
      ((integralGroupPointsContinuousMulEquivFixedPoints E H).symm g).ofConv = g.1.ofConv := by
  simpa only [AlgHom.mapValue_apply, ← WithConv.ofConv_injective.eq_iff, ofConv_toConv] using
    mapValue_integralGroupPointsContinuousMulEquivFixedPoints_symm g

variable (E A) in
/-- **An `𝒪[E]`-algebra map `A →ₐ[𝒪[E]] Breve E` comes from `𝒪[E]` if and only if its values lie
in `𝒪[Breve E]` and it is fixed by `frobenius E`.** -/
theorem integralPoints_in_breve_eq_fixedPoints [Semiring A] [Algebra 𝒪[E] A] :
    {x : A →ₐ[𝒪[E]] Breve E |
      (∀ a, x a ∈ 𝒪[Breve E]) ∧ ((frobenius E).toAlgHom.restrictScalars 𝒪[E]).comp x = x} =
      Set.range fun x : A →ₐ[𝒪[E]] 𝒪[E] ↦ (Algebra.ofId 𝒪[E] (Breve E)).comp x :=
  (PointTopology.range_integralPoints_eq_fixedPoints (algebraMap E (Breve E)).injective
    (frobenius E).toAlgHom (fixedPoints_frobenius E)).symm

variable (E H) in
/-- **For an `𝒪[E]`-Hopf algebra `H`, the integral points `𝒢(𝒪[E])` inside `𝒢(Breve E)` are the
Frobenius-fixed points whose coordinate values lie in `𝒪[Breve E]`.** -/
theorem range_mapValue_integer_in_breve_eq_fixedPoints [Semiring H] [HopfAlgebra 𝒪[E] H] :
    ((MonoidHom.range (G := WithConv (H →ₐ[𝒪[E]] 𝒪[E])) (N := WithConv (H →ₐ[𝒪[E]] Breve E))
      (AlgHom.mapValue (H := H) (Algebra.ofId 𝒪[E] (Breve E))) : Subgroup _) :
      Set (WithConv (H →ₐ[𝒪[E]] Breve E))) =
      {f : WithConv (H →ₐ[𝒪[E]] Breve E) |
        (∀ h, f.ofConv h ∈ 𝒪[Breve E]) ∧
          AlgHom.mapValue ((frobenius E).toAlgHom.restrictScalars 𝒪[E]) f = f} :=
  PointTopology.range_mapValue_integer_eq_fixedPoints (algebraMap E (Breve E)).injective
    (frobenius E).toAlgHom (fixedPoints_frobenius E)

end IntegralPoints

section SchemePoints

universe u

variable {E : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- Arithmetic Frobenius acts as a homeomorphism on the `Breve E`-points of any `E`-scheme `X`. -/
def frobeniusSchemePointsHomeomorph {X : Scheme.{u}} (f : X ⟶ Spec (.of E)) :
    SchemePointTopology.Points (R := Breve E) f ≃ₜ SchemePointTopology.Points (R := Breve E) f :=
  SchemePointTopology.algEquivHomeomorph (e := frobenius E) f
    (continuous_frobenius (E := E)) (continuous_frobenius_symm (E := E))

/-- `frobeniusSchemePointsHomeomorph` acts via
`SchemePointTopology.mapCodomain f (frobenius E).toAlgHom`. -/
@[simp]
theorem frobeniusSchemePointsHomeomorph_apply {X : Scheme.{u}} (f : X ⟶ Spec (.of E))
    (x : SchemePointTopology.Points (R := Breve E) f) :
    frobeniusSchemePointsHomeomorph f x =
      SchemePointTopology.mapCodomain f (frobenius E).toAlgHom x :=
  SchemePointTopology.algEquivHomeomorph_apply (e := frobenius E) f
    (continuous_frobenius (E := E)) (continuous_frobenius_symm (E := E)) x

/-- `(frobeniusSchemePointsHomeomorph f).symm` acts via
`SchemePointTopology.mapCodomain f (frobenius E).symm.toAlgHom`. -/
@[simp]
theorem frobeniusSchemePointsHomeomorph_symm_apply {X : Scheme.{u}} (f : X ⟶ Spec (.of E))
    (x : SchemePointTopology.Points (R := Breve E) f) :
    (frobeniusSchemePointsHomeomorph f).symm x =
      SchemePointTopology.mapCodomain f (frobenius E).symm.toAlgHom x := by
  rw [frobeniusSchemePointsHomeomorph, SchemePointTopology.algEquivHomeomorph_symm]
  exact SchemePointTopology.algEquivHomeomorph_apply f _ _ x

/-- Base change `X(E) → X(Breve E)` of scheme-valued points is a closed embedding for every
`E`-scheme `X`. -/
theorem isClosedEmbedding_schemePoints_breve {X : Scheme.{u}} (f : X ⟶ Spec (.of E)) :
    IsClosedEmbedding (SchemePointTopology.mapCodomain f (Algebra.ofId E (Breve E))) := by
  have : IsLocalHom (Algebra.ofId E (Breve E)) :=
    ⟨IsLocalHom.map_nonunit (f := algebraMap E (Breve E))⟩
  exact SchemePointTopology.isClosedEmbedding_mapCodomain (ψ := Algebra.ofId E (Breve E)) f
    (by simpa only [funext (Algebra.ofId_apply (R := E) (Breve E))] using
      isClosedEmbedding_algebraMap E)

/-- **For every `E`-scheme `X`, the `Breve E`-points fixed by Frobenius are the `E`-points.** -/
theorem schemePoints_eq_fixedPoints {X : Scheme.{u}} (f : X ⟶ Spec (.of E)) :
    {y : SchemePointTopology.Points (R := Breve E) f |
      SchemePointTopology.mapCodomain f (frobenius E).toAlgHom y = y} =
      Set.range (SchemePointTopology.mapCodomain f (Algebra.ofId E (Breve E))) :=
  (SchemePointTopology.range_mapCodomain_eq_fixedPoints (ψ := Algebra.ofId E (Breve E)) f
    (Algebra.ofId E (Breve E)).injective (frobenius E).toAlgHom
    (by simpa only [AlgEquiv.coe_toAlgHom, funext (Algebra.ofId_apply (R := E) (Breve E))] using
      fixedPoints_frobenius E)).symm

/-- **Homeomorphism `X(E) ≃ₜ X(Breve E)^σ` for arbitrary `E`-schemes.** -/
def schemePointsHomeomorphFixedPoints {X : Scheme.{u}} (f : X ⟶ Spec (.of E)) :
    SchemePointTopology.Points (R := E) f ≃ₜ
      {y : SchemePointTopology.Points (R := Breve E) f //
        SchemePointTopology.mapCodomain f (frobenius E).toAlgHom y = y} :=
  have : IsLocalHom (Algebra.ofId E (Breve E)) :=
    ⟨IsLocalHom.map_nonunit (f := algebraMap E (Breve E))⟩
  SchemePointTopology.fixedPointsHomeomorphOfIsClosedEmbedding (ψ := Algebra.ofId E (Breve E)) f
    (by simpa only [funext (Algebra.ofId_apply (R := E) (Breve E))] using
      isClosedEmbedding_algebraMap E)
    (by simpa only [AlgEquiv.coe_toAlgHom, funext (Algebra.ofId_apply (R := E) (Breve E))] using
      fixedPoints_frobenius E)

/-- Coercing `schemePointsHomeomorphFixedPoints` to `X(Breve E)` applies
`mapCodomain f (Algebra.ofId E (Breve E))`. -/
@[simp]
theorem coe_schemePointsHomeomorphFixedPoints_apply {X : Scheme.{u}} (f : X ⟶ Spec (.of E))
    (x : SchemePointTopology.Points (R := E) f) :
    (schemePointsHomeomorphFixedPoints f x : SchemePointTopology.Points (R := Breve E) f) =
      SchemePointTopology.mapCodomain f (Algebra.ofId E (Breve E)) x := by
  have : IsLocalHom (Algebra.ofId E (Breve E)) :=
    ⟨IsLocalHom.map_nonunit (f := algebraMap E (Breve E))⟩
  exact SchemePointTopology.coe_fixedPointsHomeomorphOfIsClosedEmbedding_apply f _ _ x

/-- Applying `mapCodomain f (Algebra.ofId E (Breve E))` to the inverse of
`schemePointsHomeomorphFixedPoints` recovers the Frobenius-fixed point. -/
@[simp]
theorem mapCodomain_schemePointsHomeomorphFixedPoints_symm {X : Scheme.{u}} (f : X ⟶ Spec (.of E))
    (y : {y : SchemePointTopology.Points (R := Breve E) f //
      SchemePointTopology.mapCodomain f (frobenius E).toAlgHom y = y}) :
    SchemePointTopology.mapCodomain f (Algebra.ofId E (Breve E))
      ((schemePointsHomeomorphFixedPoints f).symm y) = y.1 := by
  rw [← coe_schemePointsHomeomorphFixedPoints_apply, Homeomorph.apply_symm_apply]

/-- Base change `𝒳(𝒪[E]) → 𝒳(𝒪[Breve E])` of integral scheme-valued points is a closed embedding
for every `𝒪[E]`-scheme `𝒳`. -/
theorem isClosedEmbedding_integralSchemePoints_breve {𝒳 : Scheme.{u}} (f : 𝒳 ⟶ Spec (.of 𝒪[E])) :
    IsClosedEmbedding (SchemePointTopology.mapCodomain f (Algebra.ofId 𝒪[E] 𝒪[Breve E])) := by
  have : IsLocalHom (Algebra.ofId 𝒪[E] 𝒪[Breve E]) :=
    ⟨IsLocalHom.map_nonunit (f := algebraMap 𝒪[E] 𝒪[Breve E])⟩
  exact SchemePointTopology.isClosedEmbedding_mapCodomain (ψ := Algebra.ofId 𝒪[E] 𝒪[Breve E]) f
    (by simpa only [funext (Algebra.ofId_apply (R := 𝒪[E]) 𝒪[Breve E])] using
      isClosedEmbedding_algebraMap_integer E)

/-- **For every `𝒪[E]`-scheme `𝒳`, the `𝒪[Breve E]`-points fixed by Frobenius are the
`𝒪[E]`-points.** -/
theorem integralSchemePoints_eq_fixedPoints {𝒳 : Scheme.{u}} (f : 𝒳 ⟶ Spec (.of 𝒪[E])) :
    {y : SchemePointTopology.Points (R := 𝒪[Breve E]) f |
      SchemePointTopology.mapCodomain f (integerFrobenius E).toAlgHom y = y} =
      Set.range (SchemePointTopology.mapCodomain f (Algebra.ofId 𝒪[E] 𝒪[Breve E])) :=
  (SchemePointTopology.range_mapCodomain_eq_fixedPoints (ψ := Algebra.ofId 𝒪[E] 𝒪[Breve E]) f
    (by simpa only [funext (Algebra.ofId_apply (R := 𝒪[E]) 𝒪[Breve E])] using
      (isClosedEmbedding_algebraMap_integer E).injective)
    (integerFrobenius E).toAlgHom
    (by simpa only [AlgEquiv.coe_toAlgHom,
        funext (Algebra.ofId_apply (R := 𝒪[E]) 𝒪[Breve E])] using
      fixedPoints_integerFrobenius E)).symm

/-- **Homeomorphism `𝒳(𝒪[E]) ≃ₜ 𝒳(𝒪[Breve E])^σ` for arbitrary `𝒪[E]`-schemes.** -/
def integralSchemePointsHomeomorphFixedPoints {𝒳 : Scheme.{u}} (f : 𝒳 ⟶ Spec (.of 𝒪[E])) :
    SchemePointTopology.Points (R := 𝒪[E]) f ≃ₜ
      {y : SchemePointTopology.Points (R := 𝒪[Breve E]) f //
        SchemePointTopology.mapCodomain f (integerFrobenius E).toAlgHom y = y} :=
  have : IsLocalHom (Algebra.ofId 𝒪[E] 𝒪[Breve E]) :=
    ⟨IsLocalHom.map_nonunit (f := algebraMap 𝒪[E] 𝒪[Breve E])⟩
  SchemePointTopology.fixedPointsHomeomorphOfIsClosedEmbedding
    (ψ := Algebra.ofId 𝒪[E] 𝒪[Breve E]) f
    (by simpa only [funext (Algebra.ofId_apply (R := 𝒪[E]) 𝒪[Breve E])] using
      isClosedEmbedding_algebraMap_integer E)
    (by simpa only [AlgEquiv.coe_toAlgHom,
        funext (Algebra.ofId_apply (R := 𝒪[E]) 𝒪[Breve E])] using
      fixedPoints_integerFrobenius E)

/-- Coercing `integralSchemePointsHomeomorphFixedPoints` to `𝒳(𝒪[Breve E])` applies
`mapCodomain f (Algebra.ofId 𝒪[E] 𝒪[Breve E])`. -/
@[simp]
theorem coe_integralSchemePointsHomeomorphFixedPoints_apply {𝒳 : Scheme.{u}}
    (f : 𝒳 ⟶ Spec (.of 𝒪[E])) (x : SchemePointTopology.Points (R := 𝒪[E]) f) :
    (integralSchemePointsHomeomorphFixedPoints f x :
      SchemePointTopology.Points (R := 𝒪[Breve E]) f) =
      SchemePointTopology.mapCodomain f (Algebra.ofId 𝒪[E] 𝒪[Breve E]) x := by
  have : IsLocalHom (Algebra.ofId 𝒪[E] 𝒪[Breve E]) :=
    ⟨IsLocalHom.map_nonunit (f := algebraMap 𝒪[E] 𝒪[Breve E])⟩
  exact SchemePointTopology.coe_fixedPointsHomeomorphOfIsClosedEmbedding_apply f _ _ x

/-- Applying `mapCodomain f (Algebra.ofId 𝒪[E] 𝒪[Breve E])` to the inverse of
`integralSchemePointsHomeomorphFixedPoints` recovers the Frobenius-fixed point. -/
@[simp]
theorem mapCodomain_integralSchemePointsHomeomorphFixedPoints_symm {𝒳 : Scheme.{u}}
    (f : 𝒳 ⟶ Spec (.of 𝒪[E]))
    (y : {y : SchemePointTopology.Points (R := 𝒪[Breve E]) f //
      SchemePointTopology.mapCodomain f (integerFrobenius E).toAlgHom y = y}) :
    SchemePointTopology.mapCodomain f (Algebra.ofId 𝒪[E] 𝒪[Breve E])
      ((integralSchemePointsHomeomorphFixedPoints f).symm y) = y.1 := by
  rw [← coe_integralSchemePointsHomeomorphFixedPoints_apply, Homeomorph.apply_symm_apply]

end SchemePoints

end TauCeti.MaxUnramifiedCompletion

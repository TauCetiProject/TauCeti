/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Full
public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Discrete
import TauCeti.MeasureTheory.Integral.Bochner.SumMeasure
import TauCeti.Analysis.CStarAlgebra.Representation.GNS

/-!
# Full crossed products by discrete groups

Let `G` be a discrete group with counting measure and `α` an action of `G` on a unital
C⋆-algebra `A`. The point mass `δ_1 ⊗ 1` is a unit of the twisted convolution algebra
(`ConvolutionAlgebra.single_one_one_mul`), so the full crossed product `A ⋊_α G` is a unital
C⋆-algebra (`FullCrossedProduct.instCStarAlgebra`). The point masses `δ_g ⊗ 1` are unitaries of
`A ⋊_α G` forming a homomorphism `FullCrossedProduct.groupUnitary : G →* unitary (A ⋊_α G)`.

For the trivial action on `ℂ` this is the full group C⋆-algebra `C*(G)` of the discrete group
`G`, the closed span of the unitaries `groupUnitary g` (`dense_span_range_groupUnitary`). Its
universal property (`FullCrossedProduct.liftUnitary`) identifies unital ⋆-homomorphisms
`C*(G) → B` into a unital C⋆-algebra `B`, in any universe, with homomorphisms `G →* unitary B`: a
homomorphism `u` integrates to `f ↦ ∑ g, f(g) u_g`. This is bounded by the full seminorm and
multiplicative because, composed with a faithful representation of `B`, it is the integrated form
of a covariant pair.

## Main definitions

* `TauCeti.CStarAction.FullCrossedProduct.instCStarAlgebra`: for unital `A`, the full crossed
  product by a discrete group is a unital C⋆-algebra with unit the image of `δ_1 ⊗ 1`.
* `TauCeti.CStarAction.FullCrossedProduct.groupUnitary`: the canonical unitaries `δ_g ⊗ 1`.
* `TauCeti.CStarAction.FullCrossedProduct.liftUnitary`: unital ⋆-homomorphisms out of `C*(G)` are
  the unitary representations of `G` in unital C⋆-algebras.

## Main statements

* `TauCeti.CStarAction.FullCrossedProduct.dense_span_range_groupUnitary`: the canonical unitaries
  span a dense subspace of `C*(G)`.
* `TauCeti.CStarAction.FullCrossedProduct.liftUnitary_groupUnitary` and
  `TauCeti.CStarAction.FullCrossedProduct.starAlgHom_ext_groupUnitary`: the universal property of
  `C*(G)`.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
* K. R. Davidson, *C*-Algebras by Example*, Chapter VII (the full group C⋆-algebra of a discrete
  group and its universal property).
-/

public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported CStarAlgebra

namespace TauCeti.CStarAction

variable {G A : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G] [MeasurableSpace G]

namespace FullCrossedProduct

open ConvolutionAlgebra

variable [BorelSpace G] [CStarAlgebra A] (α : CStarAction G A)

/-- For a unital coefficient algebra, the full crossed product by a discrete group is a unital
ring with unit the image of `δ_1 ⊗ 1`. -/
instance : Ring (FullCrossedProduct α Measure.count) where
  __ : NonUnitalRing (FullCrossedProduct α Measure.count) := inferInstance
  one := of α Measure.count (single 1 1)
  -- The unit is `of (single 1 1)` by definition, so `map_mul` applies to `1 * of f`.
  one_mul x :=
    induction_on x (isClosed_eq (continuous_const.mul continuous_id) continuous_id) fun f =>
      (map_mul (of α Measure.count) (single 1 1) f).symm.trans
        (congrArg _ (single_one_one_mul f))
  mul_one x :=
    induction_on x (isClosed_eq (continuous_id.mul continuous_const) continuous_id) fun f =>
      (map_mul (of α Measure.count) f (single 1 1)).symm.trans
        (congrArg _ (mul_single_one_one f))

/-- The unit of the full crossed product by a discrete group is the image of `δ_1 ⊗ 1`. -/
@[simp]
theorem of_single_one_one : of α Measure.count (single 1 1) = 1 :=
  (rfl)

/-- For a unital coefficient algebra, the full crossed product by a discrete group is a
`ℂ`-algebra, with `algebraMap ℂ _ c = c • 1`. -/
instance : Algebra ℂ (FullCrossedProduct α Measure.count) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

/-- **The full crossed product of a unital C⋆-algebra by a discrete group is a unital
C⋆-algebra**, with unit the image of `δ_1 ⊗ 1`. -/
instance instCStarAlgebra : CStarAlgebra (FullCrossedProduct α Measure.count) where
  __ : NonUnitalCStarAlgebra (FullCrossedProduct α Measure.count) := inferInstance
  __ : Ring (FullCrossedProduct α Measure.count) := inferInstance
  __ : Algebra ℂ (FullCrossedProduct α Measure.count) := inferInstance

/-- The canonical unitaries `δ_g ⊗ 1` of the full crossed product by a discrete group. -/
def groupUnitary : G →* unitary (FullCrossedProduct α Measure.count) where
  toFun g := ⟨of α Measure.count (single g 1), by
    rw [Unitary.mem_iff, ← map_star, star_single, ← map_mul, ← map_mul, single_mul_single,
      single_mul_single]
    simp [of_single_one_one]⟩
  map_one' := Subtype.ext (of_single_one_one α)
  map_mul' g h := Subtype.ext <| by
    rw [MulMemClass.coe_mul]
    simp only [← map_mul, single_mul_single, map_one, one_mul]

/-- The canonical unitary `groupUnitary α g` is the image of `δ_g ⊗ 1`. -/
theorem coe_groupUnitary (g : G) :
    (groupUnitary α g : FullCrossedProduct α Measure.count) = of α Measure.count (single g 1) :=
  (rfl)

/-! ### The full group C⋆-algebra of a discrete group -/

section GroupAlgebra

/-- In the full group C⋆-algebra `C*(G)` of a discrete group, the image of `δ_g ⊗ c` is
`c • groupUnitary g`. -/
@[simp]
theorem of_single_eq_smul_groupUnitary (g : G) (c : ℂ) :
    of (trivial : CStarAction G ℂ) Measure.count (single g c) =
      c • (groupUnitary (trivial : CStarAction G ℂ) g :
        FullCrossedProduct (trivial : CStarAction G ℂ) Measure.count) := by
  rw [coe_groupUnitary, ← map_smul, ← single_smul, smul_eq_mul, mul_one]

/-- The canonical unitaries span a dense subspace of the full group C⋆-algebra `C*(G)` of a
discrete group. -/
theorem dense_span_range_groupUnitary :
    Dense (Submodule.span ℂ (Set.range fun g => (groupUnitary (trivial : CStarAction G ℂ) g :
      FullCrossedProduct (trivial : CStarAction G ℂ) Measure.count)) :
        Set (FullCrossedProduct (trivial : CStarAction G ℂ) Measure.count)) := by
  refine (denseRange_of (α := (trivial : CStarAction G ℂ)) (μ := Measure.count)).mono ?_
  rintro _ ⟨f, rfl⟩
  rw [← sum_single f (finite_support_ofConv f).coe_toFinset.ge, map_sum]
  refine Submodule.sum_mem _ fun g _ => ?_
  rw [of_single_eq_smul_groupUnitary]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

/-- **⋆-homomorphisms out of the full group C⋆-algebra of a discrete group are determined by their
values on the canonical unitaries.** -/
@[ext]
theorem starAlgHom_ext_groupUnitary {B : Type*} [CStarAlgebra B]
    {φ ψ : FullCrossedProduct (trivial : CStarAction G ℂ) Measure.count →⋆ₐ[ℂ] B}
    (h : ∀ g, φ (groupUnitary (trivial : CStarAction G ℂ) g) =
      ψ (groupUnitary (trivial : CStarAction G ℂ) g)) : φ = ψ := by
  have hspan := LinearMap.eqOn_span' (f := φ.toLinearMap) (g := ψ.toLinearMap)
    (s := Set.range fun g => (groupUnitary (trivial : CStarAction G ℂ) g :
      FullCrossedProduct (trivial : CStarAction G ℂ) Measure.count)) (by
        rintro _ ⟨g, rfl⟩
        exact h g)
  exact StarAlgHom.ext fun x =>
    hspan.closure (map_continuous φ) (map_continuous ψ) (dense_span_range_groupUnitary x)

variable {B : Type*} [CStarAlgebra B]

private theorem integrable_smul_unitary (u : G →* unitary B) (f : C_c(G, ℂ)) :
    Integrable (fun g => f g • (u g : B)) Measure.count :=
  continuous_of_discreteTopology.integrable_of_hasCompactSupport f.hasCompactSupport.smul_right

/-- The integrated form `f ↦ ∫ f(g) u_g` of a unitary representation `u` of a discrete group in a
unital C⋆-algebra, as a linear map on the convolution algebra. -/
private def integralUnitary (u : G →* unitary B) :
    ConvolutionAlgebra (trivial : CStarAction G ℂ) Measure.count →ₗ[ℂ] B where
  toFun f := ∫ g, f.ofConv g • (u g : B) ∂Measure.count
  map_add' f h := by
    simp only [ofConv_add, CompactlySupportedContinuousMap.coe_add, Pi.add_apply, add_smul]
    exact integral_add (integrable_smul_unitary u _) (integrable_smul_unitary u _)
  map_smul' c f := by
    simp only [ofConv_smul, CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul,
      mul_smul, RingHom.id_apply]
    exact integral_smul c _

private theorem integralUnitary_apply (u : G →* unitary B)
    (f : ConvolutionAlgebra (trivial : CStarAction G ℂ) Measure.count) :
    integralUnitary u f = ∫ g, f.ofConv g • (u g : B) ∂Measure.count :=
  rfl

private theorem integralUnitary_single (u : G →* unitary B) (g : G) (c : ℂ) :
    integralUnitary u (single g c) = c • (u g : B) := by
  rw [integralUnitary_apply, integral_count_eq_single g fun r hr => by
    rw [ofConv_single_of_ne hr, zero_smul], ofConv_single_same]

/-- The covariant pair for the trivial action on `ℂ` given by a representation `π` of `B` and a
unitary representation `u` of `G` in `B`: scalars act by scalar multiplication. -/
private def unitaryCovariant {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (u : G →* unitary B) :
    CovariantRepresentation (trivial : CStarAction G ℂ) H where
  coefficient := (StarAlgHom.ofId ℂ (H →L[ℂ] H)).toNonUnitalStarAlgHom
  group := .ofMonoidHom (π.toMonoidHom.comp ((unitary B).subtype.comp u))
  isUnitary := (ContRepresentation.isUnitary_iff_mem_unitary _).2 fun g =>
    Unitary.map_mem π (u g).property
  continuous_orbit _ := continuous_of_discreteTopology
  covariance g c v := by simp [← ContRepresentation.toMonoidHom_apply]

omit [MeasurableSpace G] [BorelSpace G] in
private theorem unitaryCovariant_coefficient_apply {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (u : G →* unitary B)
    (c : ℂ) : (unitaryCovariant π u).coefficient c = algebraMap ℂ (H →L[ℂ] H) c :=
  rfl

omit [MeasurableSpace G] [BorelSpace G] in
private theorem unitaryCovariant_group_apply {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (u : G →* unitary B)
    (g : G) : (unitaryCovariant π u).group g = π (u g) :=
  rfl

/-- A representation of `B` carries the integrated form of `u` to the integrated form of the
corresponding covariant pair. -/
private theorem map_integralUnitary {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (u : G →* unitary B)
    (f : ConvolutionAlgebra (trivial : CStarAction G ℂ) Measure.count) :
    π (integralUnitary u f) = (unitaryCovariant π u).integratedStarAlgHom Measure.count f := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  let Φ : B →L[ℂ] H := (ContinuousLinearMap.apply ℂ H ξ).comp
    { toLinearMap := (π : B →ₗ[ℂ] (H →L[ℂ] H)), cont := map_continuous π }
  have hΦ (b : B) : Φ b = π b ξ := rfl
  rw [← hΦ, integralUnitary_apply, ← Φ.integral_comp_comm (integrable_smul_unitary u _),
    CovariantRepresentation.integratedStarAlgHom_apply,
    CovariantRepresentation.integratedOperator_apply]
  simp [hΦ, unitaryCovariant_group_apply, unitaryCovariant_coefficient_apply,
    Algebra.algebraMap_eq_smul_one]

/-- The integrated form of a unitary representation of a discrete group in a unital C⋆-algebra, as
a ⋆-homomorphism on the convolution algebra. It is multiplicative and preserves the star because a
faithful representation of `B` carries it to the integrated form of a covariant pair. -/
private def integralUnitaryStarAlgHom (u : G →* unitary B) :
    ConvolutionAlgebra (trivial : CStarAction G ℂ) Measure.count →⋆ₙₐ[ℂ] B where
  __ := integralUnitary u
  map_zero' := map_zero (integralUnitary u)
  map_mul' f h := by
    obtain ⟨H, _, _, _, π, hπ⟩ := TauCeti.CStarAlgebra.exists_faithful_representation B
    apply hπ
    simp only [LinearMap.toFun_eq_coe, map_mul, map_integralUnitary π u]
  map_star' f := by
    obtain ⟨H, _, _, _, π, hπ⟩ := TauCeti.CStarAlgebra.exists_faithful_representation B
    apply hπ
    simp only [LinearMap.toFun_eq_coe, map_star, map_integralUnitary π u]

private theorem integralUnitaryStarAlgHom_apply (u : G →* unitary B)
    (f : ConvolutionAlgebra (trivial : CStarAction G ℂ) Measure.count) :
    integralUnitaryStarAlgHom u f = integralUnitary u f :=
  rfl

private theorem norm_integralUnitaryStarAlgHom_le (u : G →* unitary B)
    (f : ConvolutionAlgebra (trivial : CStarAction G ℂ) Measure.count) :
    ‖integralUnitaryStarAlgHom u f‖ ≤ ConvolutionAlgebra.fullSeminorm trivial Measure.count f := by
  obtain ⟨H, _, _, _, π, hπ⟩ := TauCeti.CStarAlgebra.exists_faithful_representation B
  rw [← NonUnitalStarAlgHom.norm_map π hπ]
  exact (congrArg norm (map_integralUnitary π u f)).trans_le
    (ConvolutionAlgebra.norm_integratedStarAlgHom_le_fullSeminorm _ f)

/-- The unital ⋆-homomorphism out of `C*(G)` integrating a unitary representation. -/
private def liftUnitaryAux (u : G →* unitary B) :
    FullCrossedProduct (trivial : CStarAction G ℂ) Measure.count →⋆ₐ[ℂ] B :=
  let L := lift (integralUnitaryStarAlgHom u) (norm_integralUnitaryStarAlgHom_le u)
  have hL : L 1 = 1 := by
    rw [← of_single_one_one, lift_of, integralUnitaryStarAlgHom_apply, integralUnitary_single,
      map_one, OneMemClass.coe_one, one_smul]
  { toFun := L
    map_one' := hL
    map_mul' := map_mul L
    map_zero' := map_zero L
    map_add' := map_add L
    commutes' c := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hL, Algebra.algebraMap_eq_smul_one]
    map_star' := map_star L }

private theorem liftUnitaryAux_of (u : G →* unitary B)
    (f : ConvolutionAlgebra (trivial : CStarAction G ℂ) Measure.count) :
    liftUnitaryAux u (of trivial Measure.count f) = ∫ g, f.ofConv g • (u g : B) ∂Measure.count :=
  lift_of _ _ f

private theorem liftUnitaryAux_groupUnitary (u : G →* unitary B) (g : G) :
    liftUnitaryAux u (groupUnitary (trivial : CStarAction G ℂ) g) = u g := by
  rw [coe_groupUnitary, liftUnitaryAux_of, ← integralUnitary_apply, integralUnitary_single,
    one_smul]

variable (G B) in
/-- **The universal property of the full group C⋆-algebra of a discrete group.** Unital
⋆-homomorphisms from `C*(G)` into a unital C⋆-algebra `B`, in any universe, are the
homomorphisms `G →* unitary B`: a unitary representation `u` integrates to the unique unital
⋆-homomorphism sending `groupUnitary g` to `u g`, acting by `f ↦ ∫ f(g) u_g` on compactly
supported functions (`liftUnitary_of`). -/
def liftUnitary :
    (G →* unitary B) ≃ (FullCrossedProduct (trivial : CStarAction G ℂ) Measure.count →⋆ₐ[ℂ] B) where
  toFun := liftUnitaryAux
  invFun φ :=
    { toFun g := ⟨φ (groupUnitary (trivial : CStarAction G ℂ) g),
        Unitary.map_mem φ (groupUnitary (trivial : CStarAction G ℂ) g).property⟩
      map_one' := Subtype.ext (by simp)
      map_mul' g h := Subtype.ext (by simp) }
  left_inv u := MonoidHom.ext fun g => Subtype.ext (liftUnitaryAux_groupUnitary u g)
  right_inv φ := starAlgHom_ext_groupUnitary fun g => liftUnitaryAux_groupUnitary _ g

/-- On compactly supported functions, the ⋆-homomorphism integrating `u` acts by
`f ↦ ∫ f(g) u_g` against counting measure. -/
theorem liftUnitary_of (u : G →* unitary B)
    (f : ConvolutionAlgebra (trivial : CStarAction G ℂ) Measure.count) :
    liftUnitary G B u (of trivial Measure.count f) =
      ∫ g, f.ofConv g • (u g : B) ∂Measure.count :=
  liftUnitaryAux_of u f

/-- The ⋆-homomorphism integrating `u` sends each canonical unitary `groupUnitary g` to `u g`. -/
@[simp]
theorem liftUnitary_groupUnitary (u : G →* unitary B) (g : G) :
    liftUnitary G B u (groupUnitary (trivial : CStarAction G ℂ) g) = u g :=
  liftUnitaryAux_groupUnitary u g

/-- The unitary representation corresponding to a unital ⋆-homomorphism out of `C*(G)` is its
restriction to the canonical unitaries. -/
@[simp]
theorem liftUnitary_symm_apply_coe
    (φ : FullCrossedProduct (trivial : CStarAction G ℂ) Measure.count →⋆ₐ[ℂ] B) (g : G) :
    ((liftUnitary G B).symm φ g : B) = φ (groupUnitary (trivial : CStarAction G ℂ) g) :=
  (rfl)

end GroupAlgebra

end FullCrossedProduct

end TauCeti.CStarAction

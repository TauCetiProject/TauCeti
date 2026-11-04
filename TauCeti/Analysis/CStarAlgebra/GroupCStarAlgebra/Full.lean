/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Topology.Algebra.LinearMapCompletion
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import TauCeti.Analysis.CStarAlgebra.Completion
public import TauCeti.Analysis.CStarAlgebra.GroupCStarAlgebra.Seminorm
public import TauCeti.Analysis.CStarAlgebra.Multiplier
public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate

/-!
# The full group C⋆-algebra of a locally compact group

Let `G : Type u` be a locally compact group and `μ` a left Haar measure on `G`. The *full* (or
*universal*) *group C⋆-algebra* `FullGroupCStarAlgebra G μ` is the completion of the group
convolution algebra `C_c(G, ℂ)` in the universal group C⋆-seminorm
`GroupConvolutionAlgebra.fullSeminorm G μ`,

`‖f‖ᵤ = sup ‖U(f)‖`,

ranging over strongly continuous unitary representations `U` of `G` on complex Hilbert spaces in
`Type u`. Because `GroupConvolutionAlgebra G μ` already carries the `L¹(μ)` norm, the universal
norm is placed on the type synonym `FullGroupConvolutionAlgebra G μ`.

Completing `FullGroupConvolutionAlgebra G μ` yields a nonunital C⋆-algebra
`FullGroupCStarAlgebra G μ` (and a commutative nonunital C⋆-algebra when `G` is abelian), together
with:

* the canonical injective dense-range ⋆-homomorphism `FullGroupCStarAlgebra.of`;
* the extension `ContRepresentation.IsUnitary.integratedGroupCStar` of every integrated unitary
  representation on a Hilbert space in `Type u` to a nondegenerate ⋆-representation of
  `FullGroupCStarAlgebra G μ`;
* the strictly continuous unitary multiplier generator homomorphism
  `FullGroupCStarAlgebra.groupMultiplier : G →* unitary 𝓜(ℂ, FullGroupCStarAlgebra G μ)` acting on
  compactly supported elements by left translation;
* the inverse correspondence `FullGroupCStarAlgebra.toGroupRepresentation` recovering a strongly
  continuous unitary representation of `G` from any nondegenerate ⋆-representation of
  `FullGroupCStarAlgebra G μ` via its multiplier extension, establishing the bijection between
  strongly continuous unitary representations of `G` and nondegenerate representations of `C⋆(G)`
  on Hilbert spaces in `Type u`;
* the canonical isometric ⋆-isomorphism `FullGroupCStarAlgebra.haarMeasureEquiv G μ ν` between the
  full group C⋆-algebras associated with any two left Haar measures `μ` and `ν` on `G`, intertwining
  integrated representations and the canonical unitary group multipliers.

No Hausdorff, separability, second-countability, regularity or σ-finiteness assumption is imposed.

## Main definitions

* `TauCeti.FullGroupConvolutionAlgebra`: `GroupConvolutionAlgebra G μ` equipped with the universal
  group C⋆-norm.
* `TauCeti.FullGroupCStarAlgebra`: the full group C⋆-algebra `C⋆(G)` with respect to `μ`.
* `TauCeti.FullGroupCStarAlgebra.of`: the canonical injective dense-range ⋆-homomorphism from
  `GroupConvolutionAlgebra G μ`.
* `TauCeti.FullGroupCStarAlgebra.lift`: extension of a ⋆-homomorphism bounded by `fullSeminorm`.
* `ContRepresentation.IsUnitary.integratedGroupCStar`: extension of an integrated unitary
  representation to `FullGroupCStarAlgebra G μ`.
* `TauCeti.FullGroupCStarAlgebra.groupMultiplier`: the canonical unitary multiplier homomorphism
  `G →* unitary 𝓜(ℂ, FullGroupCStarAlgebra G μ)`.
* `TauCeti.FullGroupCStarAlgebra.toGroupRepresentation`: the strongly continuous unitary group
  representation attached to a nondegenerate representation of `FullGroupCStarAlgebra G μ`.
* `TauCeti.GroupConvolutionAlgebra.haarMeasureEquiv` and
  `TauCeti.FullGroupCStarAlgebra.haarMeasureEquiv`: canonical ⋆-isomorphisms rescaling between two
  left Haar measures.

## Main statements

* `TauCeti.FullGroupCStarAlgebra.of_injective`: injectivity of `of` for every left Haar measure.
* `ContRepresentation.IsUnitary.isNondegenerate_integratedGroupCStar`: every integrated unitary
  representation on `FullGroupCStarAlgebra G μ` is nondegenerate.
* `TauCeti.FullGroupCStarAlgebra.of_mul_eq_integral_groupMultiplier`: Bochner integral formula
  `of f * x = ∫ r, f r • i_G(r) x ∂μ` in `FullGroupCStarAlgebra G μ`.
* `TauCeti.FullGroupCStarAlgebra.integratedGroupCStar_toGroupRepresentation` and
  `TauCeti.FullGroupCStarAlgebra.toGroupRepresentation_integratedGroupCStar`: the universal
  bijection between strongly continuous unitary representations of `G` and nondegenerate
  representations of `FullGroupCStarAlgebra G μ`.
* `TauCeti.FullGroupCStarAlgebra.congr_haarMeasureEquiv_groupMultiplier` and
  `ContRepresentation.IsUnitary.integratedGroupCStar_haarMeasureEquiv`: Haar-measure independence of
  generator maps and integrated representations.

## References

* Jacques Dixmier, *C*-Algebras*, Section 13.9.
* Gerald B. Folland, *A Course in Abstract Harmonic Analysis*, Section 7.1.
* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
* The crossed-product completion and canonical multiplier patterns of
  `TauCeti.CStarAction.FullCrossedProduct` and
  `TauCeti.CStarAction.FullCrossedProduct.groupMultiplier` in
  `TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Full` and
  `TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Multiplier`.
-/

public section

noncomputable section

open MeasureTheory UniformSpace Filter Topology
open scoped CompactlySupported CStarAlgebra MultiplierAlgebra NNReal

namespace TauCeti

universe u

section Group

variable {G : Type u} [Group G] [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}

variable (G μ) in
/-- The group convolution algebra `C_c(G, ℂ)` equipped with the universal group C⋆-seminorm
`GroupConvolutionAlgebra.fullSeminorm G μ` in place of the `L¹(μ)` norm. Its completion is
`FullGroupCStarAlgebra G μ`. -/
@[expose] def FullGroupConvolutionAlgebra : Type u :=
  GroupConvolutionAlgebra G μ

namespace FullGroupConvolutionAlgebra

/-- Regard an element of `GroupConvolutionAlgebra G μ` as an element of
`FullGroupConvolutionAlgebra G μ`. -/
def toFull : GroupConvolutionAlgebra G μ ≃ FullGroupConvolutionAlgebra G μ :=
  Equiv.refl _

/-- Extract the underlying element of `GroupConvolutionAlgebra G μ`. -/
def ofFull : FullGroupConvolutionAlgebra G μ ≃ GroupConvolutionAlgebra G μ :=
  Equiv.refl _

@[simp]
theorem toFull_symm : (toFull (G := G) (μ := μ)).symm = ofFull :=
  (rfl)

@[simp]
theorem ofFull_symm : (ofFull (G := G) (μ := μ)).symm = toFull :=
  (rfl)

@[simp]
theorem ofFull_toFull (f : GroupConvolutionAlgebra G μ) : ofFull (toFull f) = f :=
  (rfl)

@[simp]
theorem toFull_ofFull (f : FullGroupConvolutionAlgebra G μ) : toFull (ofFull f) = f :=
  (rfl)

variable [IsTopologicalGroup G] [BorelSpace G] [μ.IsHaarMeasure]

instance : NonUnitalRing (FullGroupConvolutionAlgebra G μ) :=
  inferInstanceAs (NonUnitalRing (GroupConvolutionAlgebra G μ))

instance : Module ℂ (FullGroupConvolutionAlgebra G μ) :=
  inferInstanceAs (Module ℂ (GroupConvolutionAlgebra G μ))

instance : IsScalarTower ℂ (FullGroupConvolutionAlgebra G μ) (FullGroupConvolutionAlgebra G μ) :=
  inferInstanceAs
    (IsScalarTower ℂ (GroupConvolutionAlgebra G μ) (GroupConvolutionAlgebra G μ))

instance : SMulCommClass ℂ (FullGroupConvolutionAlgebra G μ) (FullGroupConvolutionAlgebra G μ) :=
  inferInstanceAs
    (SMulCommClass ℂ (GroupConvolutionAlgebra G μ) (GroupConvolutionAlgebra G μ))

@[simp]
theorem toFull_zero : toFull (0 : GroupConvolutionAlgebra G μ) = 0 :=
  (rfl)

@[simp]
theorem toFull_add (f g : GroupConvolutionAlgebra G μ) : toFull (f + g) = toFull f + toFull g :=
  (rfl)

@[simp]
theorem toFull_neg (f : GroupConvolutionAlgebra G μ) : toFull (-f) = -toFull f :=
  (rfl)

@[simp]
theorem toFull_sub (f g : GroupConvolutionAlgebra G μ) : toFull (f - g) = toFull f - toFull g :=
  (rfl)

@[simp]
theorem toFull_mul (f g : GroupConvolutionAlgebra G μ) : toFull (f * g) = toFull f * toFull g :=
  (rfl)

@[simp]
theorem toFull_smul (c : ℂ) (f : GroupConvolutionAlgebra G μ) : toFull (c • f) = c • toFull f :=
  (rfl)

@[simp]
theorem ofFull_zero : ofFull (0 : FullGroupConvolutionAlgebra G μ) = 0 :=
  (rfl)

@[simp]
theorem ofFull_add (f g : FullGroupConvolutionAlgebra G μ) :
    ofFull (f + g) = ofFull f + ofFull g :=
  (rfl)

@[simp]
theorem ofFull_neg (f : FullGroupConvolutionAlgebra G μ) : ofFull (-f) = -ofFull f :=
  (rfl)

@[simp]
theorem ofFull_sub (f g : FullGroupConvolutionAlgebra G μ) :
    ofFull (f - g) = ofFull f - ofFull g :=
  (rfl)

@[simp]
theorem ofFull_mul (f g : FullGroupConvolutionAlgebra G μ) :
    ofFull (f * g) = ofFull f * ofFull g :=
  (rfl)

@[simp]
theorem ofFull_smul (c : ℂ) (f : FullGroupConvolutionAlgebra G μ) :
    ofFull (c • f) = c • ofFull f :=
  (rfl)

variable [LocallyCompactSpace G]

instance : StarRing (FullGroupConvolutionAlgebra G μ) :=
  inferInstanceAs (StarRing (GroupConvolutionAlgebra G μ))

instance : StarModule ℂ (FullGroupConvolutionAlgebra G μ) :=
  inferInstanceAs (StarModule ℂ (GroupConvolutionAlgebra G μ))

@[simp]
theorem toFull_star (f : GroupConvolutionAlgebra G μ) : toFull (star f) = star (toFull f) :=
  (rfl)

@[simp]
theorem ofFull_star (f : FullGroupConvolutionAlgebra G μ) : ofFull (star f) = star (ofFull f) :=
  (rfl)

variable (G μ) in
/-- `FullGroupConvolutionAlgebra.toFull` as a complex ⋆-algebra isomorphism. -/
def toFullStarAlgEquiv : GroupConvolutionAlgebra G μ ≃⋆ₐ[ℂ] FullGroupConvolutionAlgebra G μ where
  __ := toFull
  map_mul' _ _ := (rfl)
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)
  map_star' _ := (rfl)

@[simp]
theorem toFullStarAlgEquiv_apply (f : GroupConvolutionAlgebra G μ) :
    toFullStarAlgEquiv G μ f = toFull f :=
  (rfl)

@[simp]
theorem toFullStarAlgEquiv_symm_apply (f : FullGroupConvolutionAlgebra G μ) :
    (toFullStarAlgEquiv G μ).symm f = ofFull f :=
  (rfl)

instance : SeminormedAddCommGroup (FullGroupConvolutionAlgebra G μ) :=
  @AddGroupSeminorm.toSeminormedAddCommGroup (FullGroupConvolutionAlgebra G μ) _
    (GroupConvolutionAlgebra.fullSeminorm G μ).toAddGroupSeminorm

@[simp]
theorem norm_toFull (f : GroupConvolutionAlgebra G μ) :
    ‖toFull f‖ = GroupConvolutionAlgebra.fullSeminorm G μ f :=
  (rfl)

theorem norm_def (f : FullGroupConvolutionAlgebra G μ) :
    ‖f‖ = GroupConvolutionAlgebra.fullSeminorm G μ (ofFull f) :=
  (rfl)

instance : NormedSpace ℂ (FullGroupConvolutionAlgebra G μ) where
  __ : Module ℂ (FullGroupConvolutionAlgebra G μ) := inferInstance
  norm_smul_le c f := by
    simp only [norm_def, ofFull_smul]
    exact (map_smul_eq_mul _ _ _).le

instance : NonUnitalSeminormedRing (FullGroupConvolutionAlgebra G μ) where
  __ : SeminormedAddCommGroup (FullGroupConvolutionAlgebra G μ) := inferInstance
  __ : NonUnitalRing (FullGroupConvolutionAlgebra G μ) := inferInstance
  norm_mul_le f g := by
    simpa only [norm_def, ofFull_mul] using
      GroupConvolutionAlgebra.fullSeminorm_mul_le (ofFull f) (ofFull g)

instance : NormedAddCommGroup (FullGroupConvolutionAlgebra G μ) :=
  .ofSeparation fun f hf => ofFull.injective <| by
    rw [ofFull_zero]
    exact GroupConvolutionAlgebra.fullSeminorm_eq_zero_iff.1 hf

instance : NonUnitalNormedRing (FullGroupConvolutionAlgebra G μ) where
  __ : NonUnitalSeminormedRing (FullGroupConvolutionAlgebra G μ) := inferInstance
  __ : NormedAddCommGroup (FullGroupConvolutionAlgebra G μ) := inferInstance

instance : NormedStarGroup (FullGroupConvolutionAlgebra G μ) where
  norm_star_le f := by
    simp only [norm_def, ofFull_star, GroupConvolutionAlgebra.fullSeminorm_star, le_refl]

theorem norm_star_mul_self (f : FullGroupConvolutionAlgebra G μ) : ‖star f * f‖ = ‖f‖ * ‖f‖ := by
  simpa only [norm_def, ofFull_mul, ofFull_star] using
    GroupConvolutionAlgebra.fullSeminorm_star_mul_self (ofFull f)

end FullGroupConvolutionAlgebra

open FullGroupConvolutionAlgebra

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure]

variable (G μ) in
/-- The full (or universal) group C⋆-algebra `C⋆(G)` of a locally compact group `G` with respect to
a left Haar measure `μ`: the completion of `GroupConvolutionAlgebra G μ` in the universal group
C⋆-seminorm. -/
@[expose] def FullGroupCStarAlgebra : Type u :=
  Completion (FullGroupConvolutionAlgebra G μ)

namespace FullGroupCStarAlgebra

instance : NonUnitalCStarAlgebra (Completion (FullGroupConvolutionAlgebra G μ)) where
  toCStarRing := Completion.cstarRing fun f => (norm_star_mul_self f).ge

instance : NonUnitalCStarAlgebra (FullGroupCStarAlgebra G μ) :=
  inferInstanceAs (NonUnitalCStarAlgebra (Completion (FullGroupConvolutionAlgebra G μ)))

variable (G μ) in
/-- The canonical dense-range ⋆-homomorphism from `GroupConvolutionAlgebra G μ` into
`FullGroupCStarAlgebra G μ`. -/
def of : GroupConvolutionAlgebra G μ →⋆ₙₐ[ℂ] FullGroupCStarAlgebra G μ where
  toFun f := (toFullStarAlgEquiv G μ f : Completion (FullGroupConvolutionAlgebra G μ))
  map_smul' c f := by
    rw [map_smul]
    exact Completion.coe_smul c _
  map_zero' := by
    rw [map_zero]
    exact Completion.coe_zero
  map_add' f g := by
    rw [map_add]
    exact Completion.coe_add _ _
  map_mul' f g := by
    rw [map_mul]
    exact Completion.coe_mul' _ _
  map_star' f := by
    rw [map_star]
    exact Completion.coe_star _

@[simp]
theorem coe_toFull_eq_of (f : GroupConvolutionAlgebra G μ) :
    ((toFull f : Completion (FullGroupConvolutionAlgebra G μ)) : FullGroupCStarAlgebra G μ) =
      of G μ f :=
  (rfl)

/-- The norm of `of G μ f` in `FullGroupCStarAlgebra G μ` is the universal group C⋆-seminorm of
`f`. -/
@[simp]
theorem norm_of (f : GroupConvolutionAlgebra G μ) :
    ‖of G μ f‖ = GroupConvolutionAlgebra.fullSeminorm G μ f :=
  Completion.norm_coe (toFull f)

/-- The C⋆-norm of `of G μ f` is bounded by the `L¹(μ)` norm of `f`. -/
theorem norm_of_le (f : GroupConvolutionAlgebra G μ) : ‖of G μ f‖ ≤ ‖f‖ :=
  (norm_of f).trans_le (GroupConvolutionAlgebra.fullSeminorm_le_norm f)

/-- The canonical map `of G μ` is continuous for the `L¹(μ)` topology. -/
theorem continuous_of : Continuous (of G μ) :=
  AddMonoidHomClass.continuous_of_bound (of G μ) 1 fun f => by
    simpa only [one_mul] using norm_of_le f

/-- Compactly supported continuous functions have dense image in `FullGroupCStarAlgebra G μ`. -/
theorem denseRange_of : DenseRange (of G μ) :=
  Completion.denseRange_coe.comp toFull.surjective.denseRange (Completion.continuous_coe _)

/-- Closed properties on `FullGroupCStarAlgebra G μ` reduce to `GroupConvolutionAlgebra G μ`. -/
@[elab_as_elim]
theorem induction_on {p : FullGroupCStarAlgebra G μ → Prop} (x : FullGroupCStarAlgebra G μ)
    (hp : IsClosed {x | p x}) (ih : ∀ f, p (of G μ f)) : p x :=
  Completion.induction_on (p := p) x hp fun f => coe_toFull_eq_of (ofFull f) ▸ ih (ofFull f)

/-- The canonical map from `GroupConvolutionAlgebra G μ` into `FullGroupCStarAlgebra G μ` is
injective for every left Haar measure `μ`. -/
theorem of_injective : Function.Injective (of G μ) :=
  (injective_iff_map_eq_zero (of G μ)).2 fun f hf =>
    GroupConvolutionAlgebra.fullSeminorm_eq_zero_iff.1 (by rw [← norm_of, hf, norm_zero])

/-- Nonunital ⋆-homomorphisms out of `FullGroupCStarAlgebra G μ` are determined by their restriction
to `GroupConvolutionAlgebra G μ`. -/
@[ext]
theorem starAlgHom_ext {B : Type*} [NonUnitalCStarAlgebra B]
    {φ ψ : FullGroupCStarAlgebra G μ →⋆ₙₐ[ℂ] B} (h : φ.comp (of G μ) = ψ.comp (of G μ)) :
    φ = ψ :=
  NonUnitalStarAlgHom.ext fun x => induction_on x
    (isClosed_eq (map_continuous φ) (map_continuous ψ)) fun f => congr($h f)

/-- Continuous linear maps out of `FullGroupCStarAlgebra G μ` are determined on
`GroupConvolutionAlgebra G μ`. -/
@[ext]
theorem continuousLinearMap_ext {E : Type*} [TopologicalSpace E] [T2Space E] [AddCommMonoid E]
    [Module ℂ E] {S T : FullGroupCStarAlgebra G μ →L[ℂ] E}
    (h : ∀ f, S (of G μ f) = T (of G μ f)) : S = T :=
  ContinuousLinearMap.ext fun x => induction_on x (isClosed_eq S.continuous T.continuous) h

section Lift

variable {D : Type*} [NonUnitalCStarAlgebra D]
  (ρ : GroupConvolutionAlgebra G μ →⋆ₙₐ[ℂ] D)
  (hρ : ∀ f, ‖ρ f‖ ≤ GroupConvolutionAlgebra.fullSeminorm G μ f)

private def liftCLM : FullGroupConvolutionAlgebra G μ →L[ℂ] D :=
  ((ρ : GroupConvolutionAlgebra G μ →ₗ[ℂ] D).comp
    ((toFullStarAlgEquiv G μ).symm :
      FullGroupConvolutionAlgebra G μ →ₗ[ℂ] GroupConvolutionAlgebra G μ)).mkContinuous 1 fun f => by
      simpa [norm_def] using hρ (ofFull f)

private theorem fromCompletion_liftCLM_of (f : GroupConvolutionAlgebra G μ) :
    (liftCLM ρ hρ).fromCompletion (of G μ f) = ρ f := by
  simpa [liftCLM] using
    ContinuousLinearMap.fromCompletion_apply_coe (liftCLM ρ hρ) (toFull f)

/-- Extend a nonunital ⋆-homomorphism bounded by `GroupConvolutionAlgebra.fullSeminorm G μ` to
`FullGroupCStarAlgebra G μ`. -/
def lift : FullGroupCStarAlgebra G μ →⋆ₙₐ[ℂ] D where
  toFun := (liftCLM ρ hρ).fromCompletion
  map_smul' := map_smul _
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' x y := by
    induction x using induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih f =>
      induction y using induction_on with
      | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
      | ih g => simp only [← map_mul, fromCompletion_liftCLM_of]
  map_star' x := by
    induction x using induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih f => simp only [← map_star, fromCompletion_liftCLM_of]

@[simp]
theorem lift_of (f : GroupConvolutionAlgebra G μ) : lift ρ hρ (of G μ f) = ρ f :=
  fromCompletion_liftCLM_of ρ hρ f

@[simp]
theorem lift_comp_of : (lift ρ hρ).comp (of G μ) = ρ :=
  NonUnitalStarAlgHom.ext (lift_of ρ hρ)

end Lift

end FullGroupCStarAlgebra

end Group

end TauCeti

/-! ### Extended integrated unitary representations -/

namespace ContRepresentation.IsUnitary

universe u

open TauCeti TauCeti.FullGroupCStarAlgebra

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The integrated form of a strongly continuous unitary representation on a Hilbert space in
`Type u`, extended by continuity to `FullGroupCStarAlgebra G μ`. -/
def integratedGroupCStar {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure] :
    FullGroupCStarAlgebra G μ →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
  FullGroupCStarAlgebra.lift (hU.integratedStarAlgHom hcont μ)
    (GroupConvolutionAlgebra.norm_integratedStarAlgHom_le_fullSeminorm hU hcont)

@[simp]
theorem integratedGroupCStar_of {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure]
    (f : GroupConvolutionAlgebra G μ) :
    hU.integratedGroupCStar hcont μ (of G μ f) = hU.integratedStarAlgHom hcont μ f :=
  lift_of _ _ f

@[simp]
theorem integratedGroupCStar_comp_of {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure] :
    (hU.integratedGroupCStar hcont μ).comp (of G μ) = hU.integratedStarAlgHom hcont μ :=
  NonUnitalStarAlgHom.ext (hU.integratedGroupCStar_of hcont μ)

/-- Every integrated representation of `FullGroupCStarAlgebra G μ` coming from a strongly continuous
unitary representation of `G` is nondegenerate. -/
theorem isNondegenerate_integratedGroupCStar {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure] :
    (hU.integratedGroupCStar hcont μ).IsNondegenerate := by
  rw [NonUnitalStarAlgHom.isNondegenerate_iff_dense]
  refine (hU.dense_span_integratedOperator hcont μ).mono (Submodule.span_mono fun ξ hξ => ?_)
  obtain ⟨f, hf⟩ := Set.mem_iUnion.1 hξ
  exact Set.mem_iUnion.2 ⟨of G μ (GroupConvolutionAlgebra.toConv f), by simpa using hf⟩

end ContRepresentation.IsUnitary

namespace TauCeti

universe u

section NormAndMultipliers

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]

namespace FullGroupCStarAlgebra

open FullGroupConvolutionAlgebra GroupConvolutionAlgebra

/-- The norm on `FullGroupCStarAlgebra G μ` is the least nonnegative bound for all extended
integrated unitary representations on Hilbert spaces in `Type u`. -/
theorem norm_le_iff {x : FullGroupCStarAlgebra G μ} {c : ℝ} (hc : 0 ≤ c) :
    ‖x‖ ≤ c ↔
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (U : ContRepresentation ℂ G H) (hU : U.IsUnitary)
        (hcont : ∀ v, Continuous fun g => U g v),
          ‖hU.integratedGroupCStar hcont μ x‖ ≤ c := by
  refine ⟨fun h _ _ _ _ _ hU hcont => (NonUnitalStarAlgHom.norm_apply_le _ x).trans h, fun h => ?_⟩
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨f, hf⟩ := (denseRange_of (G := G) (μ := μ)).exists_dist_lt x (half_pos hε)
  have hf' : ‖x - of G μ f‖ < ε / 2 := by rwa [← dist_eq_norm]
  have hfc : ‖of G μ f‖ ≤ c + ε / 2 := by
    rw [norm_of, fullSeminorm_le_iff (by positivity)]
    intro H _ _ _ U hU hcont
    rw [← hU.integratedGroupCStar_of hcont μ]
    calc ‖hU.integratedGroupCStar hcont μ (of G μ f)‖
        ≤ ‖hU.integratedGroupCStar hcont μ x‖ +
            ‖hU.integratedGroupCStar hcont μ (x - of G μ f)‖ := by
          rw [map_sub, norm_sub_rev]
          exact norm_le_insert' _ _
      _ ≤ c + ε / 2 :=
          add_le_add (h H U hU hcont) ((NonUnitalStarAlgHom.norm_apply_le _ _).trans hf'.le)
  calc ‖x‖ ≤ ‖of G μ f‖ + ‖x - of G μ f‖ := norm_le_insert' x (of G μ f)
    _ < c + ε := by linarith

/-- Two elements of `FullGroupCStarAlgebra G μ` are equal if and only if all their extended
integrated unitary representations on Hilbert spaces in `Type u` agree. -/
theorem eq_iff_forall_integratedGroupCStar_eq {x y : FullGroupCStarAlgebra G μ} :
    x = y ↔
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (U : ContRepresentation ℂ G H) (hU : U.IsUnitary)
        (hcont : ∀ v, Continuous fun g => U g v),
          hU.integratedGroupCStar hcont μ x = hU.integratedGroupCStar hcont μ y := by
  refine ⟨fun h _ _ _ _ _ _ _ => h ▸ rfl, fun h => ?_⟩
  rw [← sub_eq_zero, ← norm_le_zero_iff, norm_le_iff le_rfl]
  intro H _ _ _ U hU hcont
  rw [map_sub, h H U hU hcont, sub_self, norm_zero]

/-- Two elements of `GroupConvolutionAlgebra G μ` have the same image in `FullGroupCStarAlgebra G μ`
if and only if their integrated forms agree in every strongly continuous unitary representation on a
Hilbert space in `Type u`. -/
theorem of_eq_of_iff {f g : GroupConvolutionAlgebra G μ} :
    of G μ f = of G μ g ↔
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (U : ContRepresentation ℂ G H) (hU : U.IsUnitary)
        (hcont : ∀ v, Continuous fun g => U g v),
          hU.integratedStarAlgHom hcont μ f = hU.integratedStarAlgHom hcont μ g := by
  simpa using eq_iff_forall_integratedGroupCStar_eq (x := of G μ f) (y := of G μ g)

/-! ### Canonical unitary group multipliers -/

private def extendCLM (T : GroupConvolutionAlgebra G μ →ₗ[ℂ] GroupConvolutionAlgebra G μ) (C : ℝ)
    (hT : ∀ f, fullSeminorm G μ (T f) ≤ C * fullSeminorm G μ f) :
    FullGroupCStarAlgebra G μ →L[ℂ] FullGroupCStarAlgebra G μ :=
  let toFullLM : GroupConvolutionAlgebra G μ →ₗ[ℂ] FullGroupConvolutionAlgebra G μ :=
    toFullStarAlgEquiv G μ
  let ofFullLM : FullGroupConvolutionAlgebra G μ →ₗ[ℂ] GroupConvolutionAlgebra G μ :=
    (toFullStarAlgEquiv G μ).symm
  ((toFullLM.comp (T.comp ofFullLM)).mkContinuous C fun f => by
    simpa [FullGroupConvolutionAlgebra.norm_def, toFullLM, ofFullLM] using hT (ofFull f)).completion

private theorem extendCLM_of (T : GroupConvolutionAlgebra G μ →ₗ[ℂ] GroupConvolutionAlgebra G μ)
    (C : ℝ) (hT : ∀ f, fullSeminorm G μ (T f) ≤ C * fullSeminorm G μ f)
    (f : GroupConvolutionAlgebra G μ) :
    extendCLM T C hT (of G μ f) = of G μ (T f) := by
  rw [← coe_toFull_eq_of, ← coe_toFull_eq_of, extendCLM]
  exact (ContinuousLinearMap.completion_apply_coe _ _).trans (by simp [-coe_toFull_eq_of])

private def translateCLM (r : G) : FullGroupCStarAlgebra G μ →L[ℂ] FullGroupCStarAlgebra G μ :=
  extendCLM (translateLIE r).toLinearEquiv.toLinearMap 1 fun f => by simp

private theorem translateCLM_of (r : G) (f : GroupConvolutionAlgebra G μ) :
    translateCLM r (of G μ f) = of G μ (translateLIE r f) := by
  rw [translateCLM, extendCLM_of, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]

private theorem translateCLM_one : translateCLM (G := G) (μ := μ) 1 = 1 :=
  continuousLinearMap_ext fun f => by simp [translateCLM_of]

private theorem translateCLM_mul (r t : G) :
    translateCLM (G := G) (μ := μ) (r * t) = translateCLM r * translateCLM t :=
  continuousLinearMap_ext fun f => by
    simp [translateCLM_of, translateLIE_mul, LinearIsometryEquiv.coe_mul]

private theorem norm_translateCLM_apply (r : G) (x : FullGroupCStarAlgebra G μ) :
    ‖translateCLM r x‖ = ‖x‖ := by
  induction x using induction_on with
  | hp => exact isClosed_eq (by fun_prop) continuous_norm
  | ih f => simp [translateCLM_of]

private theorem star_translateCLM_mul (r : G) (x y : FullGroupCStarAlgebra G μ) :
    star (translateCLM r⁻¹ x) * y = star x * translateCLM r y := by
  induction x using induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f =>
    induction y using induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih g =>
      rw [translateCLM_of, translateCLM_of]
      simp only [← map_star (of G μ), ← map_mul (of G μ)]
      refine of_eq_of_iff.2 fun H _ _ _ U hU hcont => ?_
      simp only [map_mul, map_star, hU.integratedStarAlgHom_translateLIE, star_mul, mul_assoc]
      rw [ContinuousLinearMap.star_eq_adjoint (U r⁻¹), hU.adjoint_eq_inv, inv_inv]

private def groupMultiplierAux (r : G) : 𝓜(ℂ, FullGroupCStarAlgebra G μ) :=
  .ofAdjoint (translateCLM r) (translateCLM r⁻¹) (star_translateCLM_mul r)

private theorem groupMultiplierAux_mem_unitary (r : G) :
    groupMultiplierAux (G := G) (μ := μ) r ∈ unitary 𝓜(ℂ, FullGroupCStarAlgebra G μ) := by
  rw [Unitary.mem_iff]
  constructor <;> refine DoubleCentralizer.ext_fst fun x => ?_ <;>
    simp [groupMultiplierAux, ← translateCLM_mul, translateCLM_one]

variable (G μ) in
/-- The canonical unitary multiplier generator map `i_G : G →* unitary 𝓜(ℂ, C⋆(G))`. On compactly
supported elements `of G μ f`, the left action of `i_G(r)` is `translateLIE r f`. -/
def groupMultiplier : G →* unitary 𝓜(ℂ, FullGroupCStarAlgebra G μ) where
  toFun r := ⟨groupMultiplierAux r, groupMultiplierAux_mem_unitary r⟩
  map_one' := Subtype.ext <| DoubleCentralizer.ext_fst fun x => by
    simp [groupMultiplierAux, translateCLM_one]
  map_mul' r t := Subtype.ext <| DoubleCentralizer.ext_fst fun x => by
    simp [groupMultiplierAux, translateCLM_mul]

private theorem groupMultiplier_fst (r : G) :
    (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)).fst = translateCLM r :=
  DoubleCentralizer.ofAdjoint_fst

private theorem groupMultiplier_snd_apply (r : G) (x : FullGroupCStarAlgebra G μ) :
    (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)).snd x =
      star (translateCLM r⁻¹ (star x)) :=
  DoubleCentralizer.ofAdjoint_snd_apply x

/-- The right action of `i_G(r)` is conjugate to the left action of `i_G(r⁻¹)`. -/
theorem groupMultiplier_snd_eq_star_fst_inv (r : G) (x : FullGroupCStarAlgebra G μ) :
    (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)).snd x =
      star ((groupMultiplier G μ r⁻¹ : 𝓜(ℂ, FullGroupCStarAlgebra G μ)).fst (star x)) := by
  rw [groupMultiplier_snd_apply, groupMultiplier_fst]

/-- The left action of the canonical unitary multiplier `i_G(r)` on `of G μ f` is left translation
by `r`. -/
@[simp]
theorem groupMultiplier_fst_of (r : G) (f : GroupConvolutionAlgebra G μ) :
    (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)).fst (of G μ f) =
      of G μ (translateLIE r f) := by
  rw [groupMultiplier_fst, translateCLM_of]

/-- The right action of `i_G(r)` on `of G μ f` is the adjoint of left translation by `r⁻¹`. -/
@[simp]
theorem groupMultiplier_snd_of (r : G) (f : GroupConvolutionAlgebra G μ) :
    (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)).snd (of G μ f) =
      star (of G μ (translateLIE r⁻¹ (star f))) := by
  rw [groupMultiplier_snd_apply, ← map_star (of G μ), translateCLM_of]

/-- The canonical unitary group map is strictly continuous on the left: `r ↦ i_G(r) x` is norm
continuous for every `x` in `FullGroupCStarAlgebra G μ`. -/
theorem continuous_groupMultiplier_fst_apply (x : FullGroupCStarAlgebra G μ) :
    Continuous fun r => (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)).fst x := by
  simp only [groupMultiplier_fst]
  have hequi : Equicontinuous fun r : G => ⇑(translateCLM (G := G) (μ := μ) r) :=
    (LipschitzWith.uniformEquicontinuous _ 1 fun r =>
      (AddMonoidHomClass.isometry_of_norm (translateCLM r)
        (norm_translateCLM_apply r)).lipschitzWith).equicontinuous
  refine continuous_iff_continuousAt.2 fun r => ?_
  induction x using induction_on with
  | hp => exact hequi.isClosed_setOfPred_tendsto (translateCLM r).continuous
  | ih f =>
    simp only [ContinuousAt, translateCLM_of]
    exact (continuous_of.comp (continuous_translateLIE f)).continuousAt

/-- The canonical unitary group map is strictly continuous on the right: `r ↦ x i_G(r)` is norm
continuous for every `x` in `FullGroupCStarAlgebra G μ`. -/
theorem continuous_groupMultiplier_snd_apply (x : FullGroupCStarAlgebra G μ) :
    Continuous fun r => (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)).snd x := by
  simp only [groupMultiplier_snd_apply]
  have h := (continuous_groupMultiplier_fst_apply (G := G) (μ := μ) (star x)).comp continuous_inv
  simp only [groupMultiplier_fst] at h
  exact h.star

end FullGroupCStarAlgebra

end NormAndMultipliers

end TauCeti

namespace ContRepresentation.IsUnitary

universe u

open TauCeti TauCeti.FullGroupCStarAlgebra

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The extended integrated form intertwines the left action of `groupMultiplier G μ r` with left
multiplication by `U r`. -/
@[simp]
theorem integratedGroupCStar_groupMultiplier_fst {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure]
    (r : G) (x : FullGroupCStarAlgebra G μ) :
    hU.integratedGroupCStar hcont μ
        ((groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)).fst x) =
      U r * hU.integratedGroupCStar hcont μ x := by
  induction x using induction_on with
  | hp =>
    exact isClosed_eq
      ((map_continuous (hU.integratedGroupCStar hcont μ)).comp (ContinuousLinearMap.continuous _))
      (continuous_const.mul (map_continuous _))
  | ih f => simp

/-- The extended integrated form intertwines the right action of `groupMultiplier G μ r` with right
multiplication by `U r`. -/
@[simp]
theorem integratedGroupCStar_groupMultiplier_snd {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure]
    (r : G) (x : FullGroupCStarAlgebra G μ) :
    hU.integratedGroupCStar hcont μ
        ((groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)).snd x) =
      hU.integratedGroupCStar hcont μ x * U r := by
  rw [groupMultiplier_snd_eq_star_fst_inv, map_star, hU.integratedGroupCStar_groupMultiplier_fst]
  simp [star_mul, map_star (hU.integratedGroupCStar hcont μ),
    ContinuousLinearMap.star_eq_adjoint (U r⁻¹), hU.adjoint_eq_inv]

end ContRepresentation.IsUnitary

/-! ### Universal property for nondegenerate representations -/

namespace TauCeti.FullGroupCStarAlgebra

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]

/-- Left multiplication by `of G μ f` in `FullGroupCStarAlgebra G μ` is given by the Bochner
integral `of G μ f * x = ∫ r, f r • i_G(r) x ∂μ`. -/
theorem of_mul_eq_integral_groupMultiplier (f : GroupConvolutionAlgebra G μ)
    (x : FullGroupCStarAlgebra G μ) :
    of G μ f * x =
      ∫ r, f.ofConv r • (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)).fst x ∂μ := by
  set F : G → FullGroupCStarAlgebra G μ :=
    fun r => f.ofConv r • (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)).fst x
  have hF_cont : Continuous F :=
    f.ofConv.continuous.smul (continuous_groupMultiplier_fst_apply x)
  have hF_supp : HasCompactSupport F :=
    f.ofConv.hasCompactSupport.mono fun r hr hz => hr (by simp [F, hz])
  have hF_int : Integrable F μ := hF_cont.integrable_of_hasCompactSupport hF_supp
  refine eq_iff_forall_integratedGroupCStar_eq.2 fun H _ _ _ U hU hcont => ?_
  let φ := hU.integratedGroupCStar hcont μ
  ext v
  let φCLM : FullGroupCStarAlgebra G μ →L[ℂ] (H →L[ℂ] H) :=
    { toLinearMap := (φ : FullGroupCStarAlgebra G μ →ₗ[ℂ] (H →L[ℂ] H)), cont := map_continuous φ }
  let ev : FullGroupCStarAlgebra G μ →L[ℂ] H := (ContinuousLinearMap.apply ℂ H v).comp φCLM
  have hev (z : FullGroupCStarAlgebra G μ) : ev z = φ z v := rfl
  rw [← hev (∫ r, F r ∂μ), ← ev.integral_comp_comm hF_int]
  simp only [hev, F, map_smul, smul_apply, φ, hU.integratedGroupCStar_groupMultiplier_fst,
    mul_apply_eq_comp, map_mul, hU.integratedGroupCStar_of, hU.integratedStarAlgHom_apply,
    hU.integratedOperator_apply]

section UniversalProperty

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {π : FullGroupCStarAlgebra G μ →⋆ₙₐ[ℂ] (H →L[ℂ] H)}

/-- The unitary group representation `r ↦ π'(i_G(r))` associated with a nondegenerate
representation `π` of `FullGroupCStarAlgebra G μ` via its multiplier extension `π'`. -/
def toGroupRepresentation (hπ : π.IsNondegenerate) : ContRepresentation ℂ G H where
  toMonoidHom :=
    { toFun r := π.multiplierExtension hπ (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ))
      map_one' := by simp
      map_mul' r t := by simp [map_mul] }

@[simp]
theorem toGroupRepresentation_apply (hπ : π.IsNondegenerate) (r : G) :
    toGroupRepresentation hπ r =
      π.multiplierExtension hπ (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)) :=
  (rfl)

theorem toGroupRepresentation_mul_eq_fst (hπ : π.IsNondegenerate) (r : G)
    (x : FullGroupCStarAlgebra G μ) :
    toGroupRepresentation hπ r * π x =
      π ((groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)).fst x) :=
  π.multiplierExtension_mul_eq_fst hπ _ x

theorem toGroupRepresentation_apply_apply (hπ : π.IsNondegenerate) (r : G)
    (x : FullGroupCStarAlgebra G μ) (ξ : H) :
    toGroupRepresentation hπ r (π x ξ) =
      π ((groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)).fst x) ξ :=
  π.multiplierExtension_apply_apply hπ _ x ξ

/-- The group representation recovered from a nondegenerate representation of
`FullGroupCStarAlgebra G μ` is unitary. -/
theorem isUnitary_toGroupRepresentation (hπ : π.IsNondegenerate) :
    (toGroupRepresentation hπ).IsUnitary := by
  refine (ContRepresentation.isUnitary_iff_mem_unitary _).2 fun r => ?_
  rw [Unitary.mem_iff]
  have hr := Unitary.mem_iff.1 (groupMultiplier G μ r).2
  constructor
  · rw [toGroupRepresentation_apply, ← map_star, ← map_mul, hr.1, map_one]
  · rw [toGroupRepresentation_apply, ← map_star, ← map_mul, hr.2, map_one]

/-- The group representation recovered from a nondegenerate representation of
`FullGroupCStarAlgebra G μ` is strongly continuous. -/
theorem continuous_toGroupRepresentation_apply (hπ : π.IsNondegenerate) (ξ : H) :
    Continuous fun r => toGroupRepresentation hπ r ξ := by
  refine π.continuous_multiplierExtension_apply hπ
    (fun x => continuous_groupMultiplier_fst_apply x) (C := 1) (fun r => ?_) ξ
  rcases subsingleton_or_nontrivial 𝓜(ℂ, FullGroupCStarAlgebra G μ) with _ | _
  · rw [Subsingleton.elim (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)) 0, norm_zero]
    exact zero_le_one
  · exact (CStarRing.norm_coe_unitary (groupMultiplier G μ r)).le

/-- Integrating the recovered strongly continuous unitary representation on
`GroupConvolutionAlgebra G μ` reproduces `π ∘ of G μ`, in any Hilbert-space universe. -/
@[simp]
theorem integratedStarAlgHom_toGroupRepresentation (hπ : π.IsNondegenerate) :
    (isUnitary_toGroupRepresentation hπ).integratedStarAlgHom
      (continuous_toGroupRepresentation_apply hπ) μ = π.comp (of G μ) := by
  ext1 f
  refine hπ.ext fun x => ContinuousLinearMap.ext fun ξ => ?_
  let πCLM : FullGroupCStarAlgebra G μ →L[ℂ] (H →L[ℂ] H) :=
    { toLinearMap := (π : FullGroupCStarAlgebra G μ →ₗ[ℂ] (H →L[ℂ] H)), cont := map_continuous π }
  let ev : FullGroupCStarAlgebra G μ →L[ℂ] H := (ContinuousLinearMap.apply ℂ H ξ).comp πCLM
  have hev (z : FullGroupCStarAlgebra G μ) : ev z = π z ξ := rfl
  have hF_cont : Continuous fun r =>
      f.ofConv r • (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)).fst x :=
    f.ofConv.continuous.smul (continuous_groupMultiplier_fst_apply x)
  have hint : Integrable
      (fun r => f.ofConv r • (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)).fst x) μ :=
    hF_cont.integrable_of_hasCompactSupport
      (f.ofConv.hasCompactSupport.mono fun r hr hz => hr (by simp [hz]))
  simp only [NonUnitalStarAlgHom.comp_apply, mul_apply_eq_comp, ← map_mul π,
    of_mul_eq_integral_groupMultiplier]
  rw [← hev (∫ r, _ ∂μ), ← ev.integral_comp_comm hint]
  simp only [hev, map_smul, smul_apply, ← toGroupRepresentation_apply_apply hπ,
    ContRepresentation.IsUnitary.integratedStarAlgHom_apply,
    ContRepresentation.IsUnitary.integratedOperator_apply]

end UniversalProperty

section SameUniverse

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every nondegenerate representation `π` of `FullGroupCStarAlgebra G μ` on a Hilbert space in
`Type u` is the extended integrated form of its associated strongly continuous unitary
representation `toGroupRepresentation hπ`. -/
@[simp]
theorem integratedGroupCStar_toGroupRepresentation
    {π : FullGroupCStarAlgebra G μ →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hπ : π.IsNondegenerate) :
    (isUnitary_toGroupRepresentation hπ).integratedGroupCStar
      (continuous_toGroupRepresentation_apply hπ) μ = π := by
  apply starAlgHom_ext
  rw [ContRepresentation.IsUnitary.integratedGroupCStar_comp_of,
    integratedStarAlgHom_toGroupRepresentation]

/-- Passing from a strongly continuous unitary representation `U` on `H : Type u` to its
nondegenerate integrated representation on `FullGroupCStarAlgebra G μ` and back recovers `U`. -/
@[simp]
theorem toGroupRepresentation_integratedGroupCStar {U : ContRepresentation ℂ G H}
    (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v) :
    toGroupRepresentation (hU.isNondegenerate_integratedGroupCStar hcont μ) = U := by
  refine DFunLike.coe_injective (funext fun r => ?_)
  refine (hU.isNondegenerate_integratedGroupCStar hcont μ).ext fun x => ?_
  rw [toGroupRepresentation_mul_eq_fst, hU.integratedGroupCStar_groupMultiplier_fst]

end SameUniverse

end TauCeti.FullGroupCStarAlgebra

/-! ### Commutative group C⋆-algebras -/

section CommGroup

namespace TauCeti.FullGroupCStarAlgebra

universe u

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]

/-- The full group C⋆-algebra of a locally compact abelian group is commutative. -/
instance : NonUnitalCommCStarAlgebra (FullGroupCStarAlgebra G μ) where
  mul_comm x y := by
    induction x using induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih f =>
      induction y using induction_on with
      | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
      | ih g =>
        simp only [← map_mul (of G μ)]
        exact of_eq_of_iff.2 fun H _ _ _ U hU hcont => by
          rw [map_mul, map_mul]
          exact (hU.integratedStarAlgHom_commute hcont μ f g).eq

end TauCeti.FullGroupCStarAlgebra

end CommGroup

/-! ### Independence of the choice of Haar measure -/

section HaarMeasureEquiv

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

namespace TauCeti.GroupConvolutionAlgebra

variable (G) in
/-- Rescaling by `Measure.haarScalarFactor μ ν` identifies `GroupConvolutionAlgebra G μ` with
`GroupConvolutionAlgebra G ν` as a complex ⋆-algebra for any two left Haar measures `μ` and `ν`. -/
def haarMeasureEquiv (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure] :
    GroupConvolutionAlgebra G μ ≃⋆ₐ[ℂ] GroupConvolutionAlgebra G ν where
  toFun f := toConv (((Measure.haarScalarFactor μ ν : ℝ) : ℂ) • f.ofConv)
  invFun f := toConv (((Measure.haarScalarFactor ν μ : ℝ) : ℂ) • f.ofConv)
  left_inv f := by
    apply ext; ext s
    simp only [CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply,
      smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul, ← NNReal.coe_mul,
      ← Measure.haarScalarFactor_eq_mul ν μ ν, Measure.haarScalarFactor_self,
      NNReal.coe_one, Complex.ofReal_one, one_mul]
  right_inv f := by
    apply ext; ext s
    simp only [CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply,
      smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul, ← NNReal.coe_mul,
      ← Measure.haarScalarFactor_eq_mul μ ν μ, Measure.haarScalarFactor_self,
      NNReal.coe_one, Complex.ofReal_one, one_mul]
  map_add' f g := by
    apply ext; ext s
    simp only [ofConv_add, CompactlySupportedContinuousMap.coe_add,
      CompactlySupportedContinuousMap.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add]
  map_smul' c f := by
    apply ext; ext s
    simp only [ofConv_smul, CompactlySupportedContinuousMap.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    ring
  map_mul' f g := by
    apply ext; ext s
    simp only [ofConv_mul_apply,
      CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
    have hint : ∫ r, f.ofConv r * g.ofConv (r⁻¹ * s) ∂μ =
        ((Measure.haarScalarFactor μ ν : ℝ) : ℂ) * ∫ r, f.ofConv r * g.ofConv (r⁻¹ * s) ∂ν := by
      rw [TauCeti.integral_isMulLeftInvariant_eq_haarScalarFactor_smul μ ν (by fun_prop)
        (f.ofConv.hasCompactSupport.mono fun r hr hz => hr (by simp [hz])),
        Complex.real_smul]
    rw [hint]
    simp_rw [mul_mul_mul_comm ((Measure.haarScalarFactor μ ν : ℝ) : ℂ)]
    rw [integral_const_mul]
    ring
  map_star' f := by
    apply ext; ext s
    simp only [ofConv_star_apply, CompactlySupportedContinuousMap.coe_smul,
      Pi.smul_apply, smul_eq_mul, star_mul', Complex.star_def, Complex.conj_ofReal,
      Complex.real_smul]
    ring

@[simp]
theorem ofConv_haarMeasureEquiv_apply (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    (f : GroupConvolutionAlgebra G μ) (s : G) :
    (haarMeasureEquiv G μ ν f).ofConv s =
      ((Measure.haarScalarFactor μ ν : ℝ) : ℂ) * f.ofConv s :=
  (rfl)

@[simp]
theorem haarMeasureEquiv_symm (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure] :
    (haarMeasureEquiv G μ ν).symm = haarMeasureEquiv G ν μ :=
  (rfl)

@[simp]
theorem haarMeasureEquiv_refl (μ : Measure G) [μ.IsHaarMeasure] :
    haarMeasureEquiv G μ μ = StarAlgEquiv.refl ℂ (GroupConvolutionAlgebra G μ) := by
  ext f : 1
  apply ext; ext s
  simp

@[simp]
theorem haarMeasureEquiv_apply_haarMeasureEquiv (μ ν κ : Measure G) [μ.IsHaarMeasure]
    [ν.IsHaarMeasure] [κ.IsHaarMeasure] (f : GroupConvolutionAlgebra G μ) :
    haarMeasureEquiv G ν κ (haarMeasureEquiv G μ ν f) = haarMeasureEquiv G μ κ f := by
  apply ext; ext s
  rw [ofConv_haarMeasureEquiv_apply, ofConv_haarMeasureEquiv_apply, ofConv_haarMeasureEquiv_apply,
    ← mul_assoc, ← Complex.ofReal_mul, ← NNReal.coe_mul,
    mul_comm (Measure.haarScalarFactor ν κ), ← Measure.haarScalarFactor_eq_mul μ ν κ]

theorem haarMeasureEquiv_trans (μ ν κ : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    [κ.IsHaarMeasure] :
    (haarMeasureEquiv G μ ν).trans (haarMeasureEquiv G ν κ) = haarMeasureEquiv G μ κ := by
  ext f : 1
  exact haarMeasureEquiv_apply_haarMeasureEquiv μ ν κ f

/-- `haarMeasureEquiv G μ ν` is an isometry for the `L¹` norms. -/
@[simp]
theorem norm_haarMeasureEquiv (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    (f : GroupConvolutionAlgebra G μ) :
    ‖haarMeasureEquiv G μ ν f‖ = ‖f‖ := by
  rw [norm_eq_integral_norm, norm_eq_integral_norm,
    TauCeti.integral_isMulLeftInvariant_eq_haarScalarFactor_smul μ ν
      (f := fun s => ‖f.ofConv s‖) (by fun_prop) f.ofConv.hasCompactSupport.norm,
    smul_eq_mul, ← integral_const_mul]
  congr 1 with s
  simp [abs_of_nonneg (NNReal.coe_nonneg _)]

/-- `haarMeasureEquiv G μ ν` commutes with left translation. -/
@[simp]
theorem translateLIE_haarMeasureEquiv (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    (r : G) (f : GroupConvolutionAlgebra G μ) :
    translateLIE r (haarMeasureEquiv G μ ν f) = haarMeasureEquiv G μ ν (translateLIE r f) := by
  apply ext; ext s
  simp

end TauCeti.GroupConvolutionAlgebra

namespace ContRepresentation.IsUnitary

open TauCeti

/-- Rescaling between two Haar measures preserves integrated unitary representations on the group
convolution algebra. -/
theorem integratedStarAlgHom_haarMeasureEquiv {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {U : ContRepresentation ℂ G H}
    (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    (f : GroupConvolutionAlgebra G μ) :
    hU.integratedStarAlgHom hcont ν (GroupConvolutionAlgebra.haarMeasureEquiv G μ ν f) =
      hU.integratedStarAlgHom hcont μ f := by
  ext v
  simp only [integratedStarAlgHom_apply, integratedOperator_apply,
    GroupConvolutionAlgebra.ofConv_haarMeasureEquiv_apply, mul_smul]
  rw [integral_smul, Complex.coe_smul,
    ← TauCeti.integral_isMulLeftInvariant_eq_haarScalarFactor_smul μ ν
      (ContRepresentation.IsUnitary.continuous_integrand hcont f.ofConv v)
      (ContRepresentation.IsUnitary.hasCompactSupport_integrand U f.ofConv v)]

end ContRepresentation.IsUnitary

namespace TauCeti.GroupConvolutionAlgebra

/-- `haarMeasureEquiv G μ ν` preserves the universal group C⋆-seminorm. -/
@[simp]
theorem fullSeminorm_haarMeasureEquiv (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    (f : GroupConvolutionAlgebra G μ) :
    fullSeminorm G ν (haarMeasureEquiv G μ ν f) = fullSeminorm G μ f := by
  have h {α β : Measure G} [α.IsHaarMeasure] [β.IsHaarMeasure] (g : GroupConvolutionAlgebra G α) :
      fullSeminorm G β (haarMeasureEquiv G α β g) ≤ fullSeminorm G α g := by
    refine (fullSeminorm_le_iff (apply_nonneg _ g)).2 fun H _ _ _ U hU hcont => ?_
    rw [hU.integratedStarAlgHom_haarMeasureEquiv hcont α β]
    exact norm_integratedStarAlgHom_le_fullSeminorm hU hcont g
  exact le_antisymm (h f) (by simpa using h (α := ν) (β := μ) (haarMeasureEquiv G μ ν f))

end TauCeti.GroupConvolutionAlgebra

namespace TauCeti.FullGroupCStarAlgebra

open GroupConvolutionAlgebra

private def haarMeasureHom (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure] :
    FullGroupCStarAlgebra G μ →⋆ₙₐ[ℂ] FullGroupCStarAlgebra G ν :=
  lift ((of G ν).comp (GroupConvolutionAlgebra.haarMeasureEquiv G μ ν).toNonUnitalStarAlgHom)
    fun f => by simp

private theorem haarMeasureHom_of (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    (f : GroupConvolutionAlgebra G μ) :
    haarMeasureHom μ ν (of G μ f) = of G ν (GroupConvolutionAlgebra.haarMeasureEquiv G μ ν f) :=
  lift_of _ _ f

private theorem haarMeasureHom_comp (μ ν κ : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    [κ.IsHaarMeasure] :
    (haarMeasureHom ν κ).comp (haarMeasureHom μ ν) = haarMeasureHom μ κ := by
  apply starAlgHom_ext
  ext f
  simp [haarMeasureHom_of]

private theorem haarMeasureHom_self (μ : Measure G) [μ.IsHaarMeasure] :
    haarMeasureHom (G := G) μ μ = NonUnitalStarAlgHom.id ℂ (FullGroupCStarAlgebra G μ) := by
  apply starAlgHom_ext
  ext f
  simp [haarMeasureHom_of]

variable (G) in
/-- Canonical isometric ⋆-isomorphism `C⋆(G, μ) ≃⋆ₐ[ℂ] C⋆(G, ν)` relating the full group
C⋆-algebras constructed from any two left Haar measures `μ` and `ν` on `G`. -/
def haarMeasureEquiv (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure] :
    FullGroupCStarAlgebra G μ ≃⋆ₐ[ℂ] FullGroupCStarAlgebra G ν :=
  StarAlgEquiv.ofNonUnitalStarAlgHom (haarMeasureHom μ ν) (haarMeasureHom ν μ)
    ((haarMeasureHom_comp μ ν μ).trans (haarMeasureHom_self μ))
    ((haarMeasureHom_comp ν μ ν).trans (haarMeasureHom_self ν))

@[simp]
theorem haarMeasureEquiv_of (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    (f : GroupConvolutionAlgebra G μ) :
    haarMeasureEquiv G μ ν (of G μ f) =
      of G ν (GroupConvolutionAlgebra.haarMeasureEquiv G μ ν f) :=
  haarMeasureHom_of μ ν f

@[simp]
theorem haarMeasureEquiv_symm (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure] :
    (haarMeasureEquiv G μ ν).symm = haarMeasureEquiv G ν μ :=
  (rfl)

@[simp]
theorem haarMeasureEquiv_refl (μ : Measure G) [μ.IsHaarMeasure] :
    haarMeasureEquiv G μ μ = StarAlgEquiv.refl ℂ (FullGroupCStarAlgebra G μ) := by
  ext x
  exact congr($(haarMeasureHom_self (G := G) μ) x)

@[simp]
theorem haarMeasureEquiv_apply_haarMeasureEquiv (μ ν κ : Measure G) [μ.IsHaarMeasure]
    [ν.IsHaarMeasure] [κ.IsHaarMeasure] (x : FullGroupCStarAlgebra G μ) :
    haarMeasureEquiv G ν κ (haarMeasureEquiv G μ ν x) = haarMeasureEquiv G μ κ x :=
  congr($(haarMeasureHom_comp (G := G) μ ν κ) x)

theorem haarMeasureEquiv_trans (μ ν κ : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    [κ.IsHaarMeasure] :
    (haarMeasureEquiv G μ ν).trans (haarMeasureEquiv G ν κ) = haarMeasureEquiv G μ κ := by
  ext x
  exact haarMeasureEquiv_apply_haarMeasureEquiv μ ν κ x

/-- `FullGroupCStarAlgebra.haarMeasureEquiv G μ ν` intertwines the canonical unitary group
multipliers on `C⋆(G, μ)` and `C⋆(G, ν)`. -/
@[simp]
theorem congr_haarMeasureEquiv_groupMultiplier (μ ν : Measure G) [μ.IsHaarMeasure]
    [ν.IsHaarMeasure] (r : G) :
    DoubleCentralizer.congr (haarMeasureEquiv G μ ν)
        (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)) =
      (groupMultiplier G ν r : 𝓜(ℂ, FullGroupCStarAlgebra G ν)) := by
  refine DoubleCentralizer.ext_fst fun x => ?_
  induction x using induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f => simp

end TauCeti.FullGroupCStarAlgebra

namespace ContRepresentation.IsUnitary

open TauCeti TauCeti.FullGroupCStarAlgebra

/-- Extended integrated unitary representations commute with the Haar-measure rescaling isomorphism
`FullGroupCStarAlgebra.haarMeasureEquiv`. -/
@[simp]
theorem integratedGroupCStar_haarMeasureEquiv {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {U : ContRepresentation ℂ G H}
    (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    (x : FullGroupCStarAlgebra G μ) :
    hU.integratedGroupCStar hcont ν (haarMeasureEquiv G μ ν x) =
      hU.integratedGroupCStar hcont μ x := by
  induction x using induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f =>
    rw [haarMeasureEquiv_of, integratedGroupCStar_of, integratedGroupCStar_of,
      integratedStarAlgHom_haarMeasureEquiv]

end ContRepresentation.IsUnitary

end HaarMeasureEquiv

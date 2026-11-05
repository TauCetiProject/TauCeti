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

For a locally compact group `G : Type u` and a left Haar measure `μ`, the *full* (or *universal*)
*group C⋆-algebra* `FullGroupCStarAlgebra G μ` is the completion of `GroupConvolutionAlgebra G μ`
in `GroupConvolutionAlgebra.fullSeminorm G μ`, forming a `NonUnitalCStarAlgebra` (and a
`NonUnitalCommCStarAlgebra` when `G` is abelian).

## Main definitions

* `TauCeti.FullGroupCStarAlgebra`, `of`, `lift`: `C⋆(G)`, its dense embedding, and extension map.
* `ContRepresentation.IsUnitary.integratedGroupCStar`: nondegenerate extension of `U` to `C⋆(G)`.
* `TauCeti.FullGroupCStarAlgebra.groupMultiplier`: strictly continuous unitary generator map
  `G →* unitary 𝓜(ℂ, FullGroupCStarAlgebra G μ)`.
* `TauCeti.FullGroupCStarAlgebra.toGroupRepresentation`: inverse map recovering a strongly
  continuous unitary representation from a nondegenerate representation of `C⋆(G)`.
* `TauCeti.FullGroupCStarAlgebra.haarMeasureEquiv`: Haar-measure rescaling ⋆-isomorphism on
  `FullGroupCStarAlgebra`.

## Main statements

* `TauCeti.FullGroupCStarAlgebra.of_injective` and `TauCeti.FullGroupCStarAlgebra.denseRange_of`:
  `GroupConvolutionAlgebra G μ` embeds injectively and densely into `FullGroupCStarAlgebra G μ`.
* `TauCeti.FullGroupCStarAlgebra.continuous_groupMultiplier_fst_apply` and
  `TauCeti.FullGroupCStarAlgebra.continuous_groupMultiplier_snd_apply`: strict continuity of `i_G`.
* `TauCeti.FullGroupCStarAlgebra.integratedGroupCStar_toGroupRepresentation` and
  `TauCeti.FullGroupCStarAlgebra.toGroupRepresentation_integratedGroupCStar`: bijection between
  strongly continuous unitary representations of `G` and nondegenerate representations of `C⋆(G)`.

## References

* Kenneth R. Davidson, *C*-Algebras by Example*, Chapter VII.
* Jacques Dixmier, *C*-Algebras*, Section 13.9.
* Gerald B. Folland, *A Course in Abstract Harmonic Analysis*, Section 7.1.
* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory UniformSpace Filter Topology
open scoped CompactlySupported CStarAlgebra MultiplierAlgebra NNReal

namespace TauCeti

universe u

section Group

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]

/-- Type synonym for `GroupConvolutionAlgebra G μ` equipped with `fullSeminorm G μ`, whose
Hausdorff completion is `FullGroupCStarAlgebra G μ`. -/
def FullGroupConvolutionAlgebra (G : Type u) [Group G] [TopologicalSpace G]
    [MeasurableSpace G] (μ : Measure G) : Type u := GroupConvolutionAlgebra G μ

namespace FullGroupConvolutionAlgebra

instance : NonUnitalRing (FullGroupConvolutionAlgebra G μ) :=
  inferInstanceAs (NonUnitalRing (GroupConvolutionAlgebra G μ))
instance : Module ℂ (FullGroupConvolutionAlgebra G μ) :=
  inferInstanceAs (Module ℂ (GroupConvolutionAlgebra G μ))
instance : IsScalarTower ℂ (FullGroupConvolutionAlgebra G μ) (FullGroupConvolutionAlgebra G μ) :=
  inferInstanceAs (IsScalarTower ℂ (GroupConvolutionAlgebra G μ) (GroupConvolutionAlgebra G μ))
instance : SMulCommClass ℂ (FullGroupConvolutionAlgebra G μ) (FullGroupConvolutionAlgebra G μ) :=
  inferInstanceAs (SMulCommClass ℂ (GroupConvolutionAlgebra G μ) (GroupConvolutionAlgebra G μ))
instance : StarRing (FullGroupConvolutionAlgebra G μ) :=
  inferInstanceAs (StarRing (GroupConvolutionAlgebra G μ))
instance : StarModule ℂ (FullGroupConvolutionAlgebra G μ) :=
  inferInstanceAs (StarModule ℂ (GroupConvolutionAlgebra G μ))

variable (G μ) in
/-- The identity ⋆-algebra equivalence with `FullGroupConvolutionAlgebra G μ`. -/
def equiv : GroupConvolutionAlgebra G μ ≃⋆ₐ[ℂ] FullGroupConvolutionAlgebra G μ :=
  StarAlgEquiv.refl ℂ (GroupConvolutionAlgebra G μ)

instance : SeminormedAddCommGroup (FullGroupConvolutionAlgebra G μ) :=
  ((GroupConvolutionAlgebra.fullSeminorm G μ).comp
    ((equiv G μ).symm :
      FullGroupConvolutionAlgebra G μ →ₗ[ℂ] _)).toAddGroupSeminorm.toSeminormedAddCommGroup

/-- The norm on `FullGroupConvolutionAlgebra G μ` is the full group C⋆-seminorm of the underlying
element of `GroupConvolutionAlgebra G μ`. -/
theorem norm_def (f : FullGroupConvolutionAlgebra G μ) :
    ‖f‖ = GroupConvolutionAlgebra.fullSeminorm G μ ((equiv G μ).symm f) := (rfl)

/-- The norm of `equiv G μ f` in `FullGroupConvolutionAlgebra G μ` is its full group C⋆-seminorm. -/
@[simp] theorem norm_equiv (f : GroupConvolutionAlgebra G μ) :
    ‖equiv G μ f‖ = GroupConvolutionAlgebra.fullSeminorm G μ f := by
  simp [norm_def]

instance : NormedSpace ℂ (FullGroupConvolutionAlgebra G μ) where
  __ : Module ℂ (FullGroupConvolutionAlgebra G μ) := inferInstance
  norm_smul_le c f := by
    simp only [norm_def, map_smul]
    exact (map_smul_eq_mul (GroupConvolutionAlgebra.fullSeminorm G μ) c ((equiv G μ).symm f)).le
instance : NonUnitalSeminormedRing (FullGroupConvolutionAlgebra G μ) where
  __ : SeminormedAddCommGroup (FullGroupConvolutionAlgebra G μ) := inferInstance
  __ : NonUnitalRing (FullGroupConvolutionAlgebra G μ) := inferInstance
  norm_mul_le f g := by
    simpa only [norm_def, map_mul] using
      GroupConvolutionAlgebra.fullSeminorm_mul_le ((equiv G μ).symm f) ((equiv G μ).symm g)
instance : NormedStarGroup (FullGroupConvolutionAlgebra G μ) where
  norm_star_le f := by
    simp only [norm_def, map_star, GroupConvolutionAlgebra.fullSeminorm_star, le_rfl]
instance : NonUnitalCStarAlgebra (Completion (FullGroupConvolutionAlgebra G μ)) where
  toCStarRing := Completion.cstarRing fun f => by
    simpa only [norm_def, map_mul, map_star] using
      (GroupConvolutionAlgebra.fullSeminorm_star_mul_self ((equiv G μ).symm f)).ge

end FullGroupConvolutionAlgebra

variable (G μ) in
/-- The full (or universal) group C⋆-algebra `C⋆(G)` of `G` with respect to `μ`: the completion of
`GroupConvolutionAlgebra G μ` in the universal group C⋆-seminorm. -/
def FullGroupCStarAlgebra : Type u := Completion (FullGroupConvolutionAlgebra G μ)

namespace FullGroupCStarAlgebra

open FullGroupConvolutionAlgebra

instance : NonUnitalCStarAlgebra (FullGroupCStarAlgebra G μ) :=
  inferInstanceAs (NonUnitalCStarAlgebra (Completion (FullGroupConvolutionAlgebra G μ)))

variable (G μ) in
/-- The canonical injective dense-range ⋆-homomorphism into `FullGroupCStarAlgebra G μ`. -/
def of : GroupConvolutionAlgebra G μ →⋆ₙₐ[ℂ] FullGroupCStarAlgebra G μ where
  toFun f := (equiv G μ f : Completion (FullGroupConvolutionAlgebra G μ))
  map_smul' c f := by rw [map_smul]; exact Completion.coe_smul c _
  map_zero' := by rw [map_zero]; exact Completion.coe_zero
  map_add' f g := by rw [map_add]; exact Completion.coe_add _ _
  map_mul' f g := by rw [map_mul]; exact Completion.coe_mul' _ _
  map_star' f := by rw [map_star]; exact Completion.coe_star _

private theorem coe_equiv_eq_of (f : GroupConvolutionAlgebra G μ) :
    ((equiv G μ f : Completion (FullGroupConvolutionAlgebra G μ)) : FullGroupCStarAlgebra G μ) =
      of G μ f := (rfl)

/-- The norm of `of G μ f` in `C⋆(G)` equals the universal group C⋆-seminorm `‖f‖ᵤ`. -/
@[simp] theorem norm_of (f : GroupConvolutionAlgebra G μ) :
    ‖of G μ f‖ = GroupConvolutionAlgebra.fullSeminorm G μ f :=
  (Completion.norm_coe (equiv G μ f)).trans (norm_equiv f)

/-- The canonical embedding `of G μ` is contractive for the `L¹(μ)` norm. -/
theorem norm_of_le (f : GroupConvolutionAlgebra G μ) : ‖of G μ f‖ ≤ ‖f‖ :=
  (norm_of f).trans_le (GroupConvolutionAlgebra.fullSeminorm_le_norm f)

/-- The canonical embedding `of G μ` is continuous with respect to the `L¹(μ)` topology. -/
theorem continuous_of : Continuous (of G μ) :=
  AddMonoidHomClass.continuous_of_bound (of G μ) 1 fun f => by simpa using norm_of_le f

/-- `GroupConvolutionAlgebra G μ` has dense image in `FullGroupCStarAlgebra G μ`. -/
theorem denseRange_of : DenseRange (of G μ) :=
  Completion.denseRange_coe.comp (equiv G μ).surjective.denseRange (Completion.continuous_coe _)

/-- To prove a closed predicate on `FullGroupCStarAlgebra G μ`, it suffices to check `of G μ f`. -/
@[elab_as_elim] theorem induction_on {p : FullGroupCStarAlgebra G μ → Prop}
    (x : FullGroupCStarAlgebra G μ) (hp : IsClosed {x | p x}) (ih : ∀ f, p (of G μ f)) : p x :=
  Completion.induction_on (p := p) x hp fun f =>
    coe_equiv_eq_of ((equiv G μ).symm f) ▸ ih ((equiv G μ).symm f)

/-- The canonical map `of G μ` into `FullGroupCStarAlgebra G μ` is injective for every left Haar
measure `μ`. -/
theorem of_injective : Function.Injective (of G μ) :=
  (injective_iff_map_eq_zero (of G μ)).2 fun _ hf =>
    GroupConvolutionAlgebra.fullSeminorm_eq_zero_iff.1 (by rw [← norm_of, hf, norm_zero])

/-- Nonunital ⋆-homomorphisms from `C⋆(G)` into a C⋆-algebra are determined on `of G μ`. -/
@[ext] theorem starAlgHom_ext {B : Type*} [NonUnitalCStarAlgebra B]
    {φ ψ : FullGroupCStarAlgebra G μ →⋆ₙₐ[ℂ] B} (h : φ.comp (of G μ) = ψ.comp (of G μ)) :
    φ = ψ :=
  NonUnitalStarAlgHom.ext fun x => induction_on x
    (isClosed_eq (map_continuous φ) (map_continuous ψ)) fun f => congr($h f)

/-- Continuous linear maps out of `C⋆(G)` into a `T₂` space are determined on `of G μ`. -/
@[ext] theorem continuousLinearMap_ext {E : Type*} [TopologicalSpace E] [T2Space E]
    [AddCommMonoid E] [Module ℂ E] {S T : FullGroupCStarAlgebra G μ →L[ℂ] E}
    (h : ∀ f, S (of G μ f) = T (of G μ f)) : S = T :=
  ContinuousLinearMap.ext fun x => induction_on x (isClosed_eq S.continuous T.continuous) h

section Lift

variable {D : Type*} [NonUnitalCStarAlgebra D] (ρ : GroupConvolutionAlgebra G μ →⋆ₙₐ[ℂ] D)
  (hρ : ∀ f, ‖ρ f‖ ≤ GroupConvolutionAlgebra.fullSeminorm G μ f)

private def liftCLM : FullGroupConvolutionAlgebra G μ →L[ℂ] D :=
  ((ρ : GroupConvolutionAlgebra G μ →ₗ[ℂ] D).comp
    ((equiv G μ).symm : FullGroupConvolutionAlgebra G μ →ₗ[ℂ] _)).mkContinuous 1 fun f => by
      simpa [norm_def] using hρ ((equiv G μ).symm f)

private theorem fromCompletion_liftCLM_of (f : GroupConvolutionAlgebra G μ) :
    (liftCLM ρ hρ).fromCompletion (of G μ f) = ρ f := by
  rw [← coe_equiv_eq_of, ContinuousLinearMap.fromCompletion_apply_coe]; rfl

/-- Extend a `fullSeminorm`-bounded ⋆-homomorphism to `FullGroupCStarAlgebra G μ`. -/
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

@[simp] theorem lift_of (f : GroupConvolutionAlgebra G μ) : lift ρ hρ (of G μ f) = ρ f :=
  fromCompletion_liftCLM_of ρ hρ f
@[simp] theorem lift_comp_of : (lift ρ hρ).comp (of G μ) = ρ :=
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

/-- The integrated form of a strongly continuous unitary representation on `H : Type u`, extended by
continuity to `FullGroupCStarAlgebra G μ`. -/
def integratedGroupCStar {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure] :
    FullGroupCStarAlgebra G μ →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
  FullGroupCStarAlgebra.lift (hU.integratedStarAlgHom hcont μ)
    (GroupConvolutionAlgebra.norm_integratedStarAlgHom_le_fullSeminorm hU hcont)

@[simp] theorem integratedGroupCStar_of {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure]
    (f : GroupConvolutionAlgebra G μ) :
    hU.integratedGroupCStar hcont μ (of G μ f) = hU.integratedStarAlgHom hcont μ f := lift_of _ _ f
@[simp] theorem integratedGroupCStar_comp_of {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure] :
    (hU.integratedGroupCStar hcont μ).comp (of G μ) = hU.integratedStarAlgHom hcont μ :=
  NonUnitalStarAlgHom.ext (hU.integratedGroupCStar_of hcont μ)

/-- Every extended integrated unitary representation on `H : Type u` is nondegenerate. -/
theorem isNondegenerate_integratedGroupCStar {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure] :
    (hU.integratedGroupCStar hcont μ).IsNondegenerate := by
  rw [NonUnitalStarAlgHom.isNondegenerate_iff_dense]
  refine (hU.dense_span_integratedOperator hcont μ).mono (Submodule.span_mono fun ξ hξ => ?_)
  obtain ⟨f, hf⟩ := Set.mem_iUnion.1 hξ
  exact Set.mem_iUnion.2 ⟨of G μ (.toConv f), by simpa using hf⟩

end ContRepresentation.IsUnitary

namespace TauCeti

universe u

section NormAndMultipliers

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]

namespace FullGroupCStarAlgebra

open GroupConvolutionAlgebra

/-- The norm on `FullGroupCStarAlgebra G μ` is the least nonnegative upper bound over extended
integrated unitary representations on Hilbert spaces in `Type u`. -/
theorem norm_le_iff {x : FullGroupCStarAlgebra G μ} {c : ℝ} (hc : 0 ≤ c) :
    ‖x‖ ≤ c ↔
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (U : ContRepresentation ℂ G H) (hU : U.IsUnitary)
        (hcont : ∀ v, Continuous fun g => U g v), ‖hU.integratedGroupCStar hcont μ x‖ ≤ c := by
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
          rw [map_sub, norm_sub_rev]; exact norm_le_insert' _ _
      _ ≤ c + ε / 2 :=
          add_le_add (h H U hU hcont) ((NonUnitalStarAlgHom.norm_apply_le _ _).trans hf'.le)
  exact (norm_le_insert' x (of G μ f)).trans_lt (by linarith)

/-- Extended integrated unitary representations in `Type u` separate points of `C⋆(G)`. -/
theorem eq_iff_forall_integratedGroupCStar_eq {x y : FullGroupCStarAlgebra G μ} :
    x = y ↔
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (U : ContRepresentation ℂ G H) (hU : U.IsUnitary)
        (hcont : ∀ v, Continuous fun g => U g v),
          hU.integratedGroupCStar hcont μ x = hU.integratedGroupCStar hcont μ y := by
  refine ⟨fun h _ _ _ _ _ _ _ => h ▸ rfl, fun h => ?_⟩
  rw [← sub_eq_zero, ← norm_le_zero_iff, norm_le_iff le_rfl]
  intro H _ _ _ U hU hcont; simp [h H U hU hcont]

/-- Two elements of `GroupConvolutionAlgebra G μ` have equal images in `C⋆(G)` if and only if all
their integrated unitary representations in `Type u` agree. -/
theorem of_eq_of_iff {f g : GroupConvolutionAlgebra G μ} :
    of G μ f = of G μ g ↔
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (U : ContRepresentation ℂ G H) (hU : U.IsUnitary)
        (hcont : ∀ v, Continuous fun g => U g v),
          hU.integratedStarAlgHom hcont μ f = hU.integratedStarAlgHom hcont μ g := by
  simpa using eq_iff_forall_integratedGroupCStar_eq (x := of G μ f) (y := of G μ g)

/-! ### Canonical unitary group multipliers -/

private def translateCLM (r : G) : FullGroupCStarAlgebra G μ →L[ℂ] FullGroupCStarAlgebra G μ :=
  ((((FullGroupConvolutionAlgebra.equiv G μ : GroupConvolutionAlgebra G μ →ₗ[ℂ] _).comp
    ((CStarAction.ConvolutionAlgebra.translateLIE r).toLinearEquiv.toLinearMap.comp
      ((FullGroupConvolutionAlgebra.equiv G μ).symm :
        FullGroupConvolutionAlgebra G μ →ₗ[ℂ] _))).mkContinuous 1
          fun _ => by simp [FullGroupConvolutionAlgebra.norm_def])).completion

private theorem translateCLM_of (r : G) (f : GroupConvolutionAlgebra G μ) :
    translateCLM r (of G μ f) = of G μ (CStarAction.ConvolutionAlgebra.translateLIE r f) := by
  rw [← coe_equiv_eq_of, ← coe_equiv_eq_of, translateCLM]
  exact ContinuousLinearMap.completion_apply_coe _ _
private theorem translateCLM_one : translateCLM (G := G) (μ := μ) 1 = 1 :=
  continuousLinearMap_ext fun f => by simp [translateCLM_of]
private theorem translateCLM_mul (r t : G) :
    translateCLM (G := G) (μ := μ) (r * t) = translateCLM r * translateCLM t :=
  continuousLinearMap_ext fun f => by
    simp [translateCLM_of, CStarAction.ConvolutionAlgebra.translateLIE_mul,
      LinearIsometryEquiv.coe_mul]
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

variable (G μ) in
/-- The canonical unitary multiplier generator map `i_G : G →* unitary 𝓜(ℂ, C⋆(G))`. -/
def groupMultiplier : G →* unitary 𝓜(ℂ, FullGroupCStarAlgebra G μ) where
  toFun r := ⟨.ofAdjoint (translateCLM r) (translateCLM r⁻¹) (star_translateCLM_mul r),
    Unitary.mem_iff.2 ⟨DoubleCentralizer.ext_fst fun _ => by
      simp [← translateCLM_mul, translateCLM_one],
      DoubleCentralizer.ext_fst fun _ => by simp [← translateCLM_mul, translateCLM_one]⟩⟩
  map_one' := Subtype.ext <| DoubleCentralizer.ext_fst fun _ => by simp [translateCLM_one]
  map_mul' _ _ := Subtype.ext <| DoubleCentralizer.ext_fst fun _ => by simp [translateCLM_mul]

private theorem groupMultiplier_fst (r : G) :
    (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)).fst = translateCLM r :=
  DoubleCentralizer.ofAdjoint_fst
private theorem groupMultiplier_snd_apply (r : G) (x : FullGroupCStarAlgebra G μ) :
    (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)).snd x =
      star (translateCLM r⁻¹ (star x)) := DoubleCentralizer.ofAdjoint_snd_apply x

theorem groupMultiplier_snd_eq_star_fst_inv (r : G) (x : FullGroupCStarAlgebra G μ) :
    (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)).snd x =
      star ((groupMultiplier G μ r⁻¹ : 𝓜(ℂ, FullGroupCStarAlgebra G μ)).fst (star x)) :=
  (groupMultiplier_snd_apply r x).trans (by rw [groupMultiplier_fst])
@[simp] theorem groupMultiplier_fst_of (r : G) (f : GroupConvolutionAlgebra G μ) :
    (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)).fst (of G μ f) =
      of G μ (CStarAction.ConvolutionAlgebra.translateLIE r f) := by
  rw [groupMultiplier_fst, translateCLM_of]
@[simp] theorem groupMultiplier_snd_of (r : G) (f : GroupConvolutionAlgebra G μ) :
    (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)).snd (of G μ f) =
      star (of G μ (CStarAction.ConvolutionAlgebra.translateLIE r⁻¹ (star f))) := by
  rw [groupMultiplier_snd_apply, ← map_star (of G μ), translateCLM_of]

/-- Strict left continuity of the canonical group multiplier map `i_G`. -/
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
    exact (continuous_of.comp
      (CStarAction.ConvolutionAlgebra.continuous_translateLIE f)).continuousAt.congr
      (.of_forall fun _ => (translateCLM_of _ f).symm)

/-- Strict right continuity of the canonical group multiplier map `i_G`. -/
theorem continuous_groupMultiplier_snd_apply (x : FullGroupCStarAlgebra G μ) :
    Continuous fun r => (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)).snd x := by
  simp only [groupMultiplier_snd_apply]
  have h := (continuous_groupMultiplier_fst_apply (G := G) (μ := μ) (star x)).comp continuous_inv
  simp only [groupMultiplier_fst] at h; exact h.star

end FullGroupCStarAlgebra
end NormAndMultipliers
end TauCeti

namespace ContRepresentation.IsUnitary

universe u

open TauCeti TauCeti.FullGroupCStarAlgebra

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Extended integrated representations intertwine left action of `groupMultiplier` with `U r`. -/
@[simp] theorem integratedGroupCStar_groupMultiplier_fst {U : ContRepresentation ℂ G H}
    (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure]
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

/-- Extended integrated representations intertwine right action of `groupMultiplier` with `U r`. -/
@[simp] theorem integratedGroupCStar_groupMultiplier_snd {U : ContRepresentation ℂ G H}
    (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure]
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

private theorem integrable_smul_groupMultiplier_fst (f : GroupConvolutionAlgebra G μ)
    (x : FullGroupCStarAlgebra G μ) :
    Integrable (fun r =>
      f.ofConv r • (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)).fst x) μ :=
  (f.ofConv.continuous.smul
    (continuous_groupMultiplier_fst_apply x)).integrable_of_hasCompactSupport
    (f.ofConv.hasCompactSupport.mono fun _ hr hz => hr (by simp [hz]))

private theorem map_integral_apply {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (φ : FullGroupCStarAlgebra G μ →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    {F : G → FullGroupCStarAlgebra G μ} (hF : Integrable F μ) (v : H) :
    φ (∫ r, F r ∂μ) v = ∫ r, φ (F r) v ∂μ :=
  (((ContinuousLinearMap.apply ℂ H v).comp
    { toLinearMap := (φ : FullGroupCStarAlgebra G μ →ₗ[ℂ] (H →L[ℂ] H))
      cont := map_continuous φ }).integral_comp_comm hF).symm

/-- Left multiplication by `of G μ f` on `C⋆(G)` is given by Bochner integration against
`groupMultiplier`. -/
theorem of_mul_eq_integral_groupMultiplier (f : GroupConvolutionAlgebra G μ)
    (x : FullGroupCStarAlgebra G μ) :
    of G μ f * x =
      ∫ r, f.ofConv r • (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)).fst x ∂μ := by
  refine eq_iff_forall_integratedGroupCStar_eq.2 fun H _ _ _ U hU hcont => ?_
  ext v
  rw [map_integral_apply (hU.integratedGroupCStar hcont μ)
    (integrable_smul_groupMultiplier_fst f x) v]
  simp only [map_smul, smul_apply, hU.integratedGroupCStar_groupMultiplier_fst,
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
      map_mul' _ _ := by simp [map_mul] }

@[simp] theorem toGroupRepresentation_apply (hπ : π.IsNondegenerate) (r : G) :
    toGroupRepresentation hπ r =
      π.multiplierExtension hπ (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)) := (rfl)

/-- The group representation recovered from a nondegenerate representation of `C⋆(G)` is unitary. -/
theorem isUnitary_toGroupRepresentation (hπ : π.IsNondegenerate) :
    (toGroupRepresentation hπ).IsUnitary := by
  refine (ContRepresentation.isUnitary_iff_mem_unitary _).2 fun r => ?_
  have hr := Unitary.mem_iff.1 (groupMultiplier G μ r).2
  exact Unitary.mem_iff.2
    ⟨by rw [toGroupRepresentation_apply, ← map_star, ← map_mul, hr.1, map_one],
      by rw [toGroupRepresentation_apply, ← map_star, ← map_mul, hr.2, map_one]⟩

/-- The group representation recovered from a nondegenerate representation of `C⋆(G)` is strongly
continuous. -/
theorem continuous_toGroupRepresentation_apply (hπ : π.IsNondegenerate) (ξ : H) :
    Continuous fun r => toGroupRepresentation hπ r ξ := by
  refine π.continuous_multiplierExtension_apply hπ
    (fun x => continuous_groupMultiplier_fst_apply x) (C := 1) (fun r => ?_) ξ
  rcases subsingleton_or_nontrivial 𝓜(ℂ, FullGroupCStarAlgebra G μ) with _ | _
  · simp [Subsingleton.elim (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)) 0]
  · exact (CStarRing.norm_coe_unitary (groupMultiplier G μ r)).le

/-- Integrating `toGroupRepresentation hπ` on `C_c(G, ℂ)` recovers `π.comp (of G μ)`. -/
@[simp] theorem integratedStarAlgHom_toGroupRepresentation (hπ : π.IsNondegenerate) :
    (isUnitary_toGroupRepresentation hπ).integratedStarAlgHom
      (continuous_toGroupRepresentation_apply hπ) μ = π.comp (of G μ) := by
  ext1 f
  refine hπ.ext fun x => ContinuousLinearMap.ext fun ξ => ?_
  simp only [NonUnitalStarAlgHom.comp_apply, mul_apply_eq_comp, ← map_mul π,
    of_mul_eq_integral_groupMultiplier,
    map_integral_apply π (integrable_smul_groupMultiplier_fst f x) ξ]
  simp only [map_smul, smul_apply, ← π.multiplierExtension_apply_apply hπ,
    ← toGroupRepresentation_apply, ContRepresentation.IsUnitary.integratedStarAlgHom_apply,
    ContRepresentation.IsUnitary.integratedOperator_apply]

end UniversalProperty

section SameUniverse

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every nondegenerate representation of `C⋆(G)` on `H : Type u` is the extended integrated form
of its associated unitary group representation. -/
@[simp] theorem integratedGroupCStar_toGroupRepresentation
    {π : FullGroupCStarAlgebra G μ →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hπ : π.IsNondegenerate) :
    (isUnitary_toGroupRepresentation hπ).integratedGroupCStar
      (continuous_toGroupRepresentation_apply hπ) μ = π :=
  starAlgHom_ext <| (ContRepresentation.IsUnitary.integratedGroupCStar_comp_of _ _ μ).trans
    (integratedStarAlgHom_toGroupRepresentation hπ)

/-- Recovering the group representation from an extended integrated unitary representation yields
the original representation `U`. -/
@[simp] theorem toGroupRepresentation_integratedGroupCStar {U : ContRepresentation ℂ G H}
    (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v) :
    toGroupRepresentation (hU.isNondegenerate_integratedGroupCStar hcont μ) = U :=
  DFunLike.coe_injective <| funext fun r =>
    (hU.isNondegenerate_integratedGroupCStar hcont μ).ext fun x => by
      rw [toGroupRepresentation_apply, NonUnitalStarAlgHom.multiplierExtension_mul_eq_fst,
        hU.integratedGroupCStar_groupMultiplier_fst]

end SameUniverse
end TauCeti.FullGroupCStarAlgebra

/-! ### Commutative group C⋆-algebras -/

section CommGroup
namespace TauCeti.FullGroupCStarAlgebra

universe u

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]

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
          simpa only [map_mul] using (hU.integratedStarAlgHom_commute hcont μ f g).eq

end TauCeti.FullGroupCStarAlgebra
end CommGroup

/-! ### Independence of the choice of Haar measure -/

section HaarMeasureEquiv

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

namespace TauCeti.FullGroupCStarAlgebra

open GroupConvolutionAlgebra

private def haarMeasureHom (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure] :
    FullGroupCStarAlgebra G μ →⋆ₙₐ[ℂ] FullGroupCStarAlgebra G ν :=
  lift ((of G ν).comp (GroupConvolutionAlgebra.haarMeasureEquiv G μ ν).toNonUnitalStarAlgHom)
    fun _ => by simp

variable (G) in
/-- Canonical isometric ⋆-isomorphism `C⋆(G, μ) ≃⋆ₐ[ℂ] C⋆(G, ν)` for any two left Haar measures. -/
def haarMeasureEquiv (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure] :
    FullGroupCStarAlgebra G μ ≃⋆ₐ[ℂ] FullGroupCStarAlgebra G ν :=
  StarAlgEquiv.ofNonUnitalStarAlgHom (haarMeasureHom μ ν) (haarMeasureHom ν μ)
    (starAlgHom_ext <| NonUnitalStarAlgHom.ext fun _ => by simp [haarMeasureHom])
    (starAlgHom_ext <| NonUnitalStarAlgHom.ext fun _ => by simp [haarMeasureHom])

@[simp] theorem haarMeasureEquiv_of (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    (f : GroupConvolutionAlgebra G μ) :
    haarMeasureEquiv G μ ν (of G μ f) =
      of G ν (GroupConvolutionAlgebra.haarMeasureEquiv G μ ν f) := lift_of _ _ f
@[simp] theorem haarMeasureEquiv_symm (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure] :
    (haarMeasureEquiv G μ ν).symm = haarMeasureEquiv G ν μ := (rfl)
@[simp] theorem haarMeasureEquiv_refl (μ : Measure G) [μ.IsHaarMeasure] :
    haarMeasureEquiv G μ μ = StarAlgEquiv.refl ℂ (FullGroupCStarAlgebra G μ) :=
  StarAlgEquiv.ext fun x => induction_on x (isClosed_eq (by fun_prop) (by fun_prop))
    fun _ => by simp
@[simp] theorem haarMeasureEquiv_apply_haarMeasureEquiv (μ ν κ : Measure G) [μ.IsHaarMeasure]
    [ν.IsHaarMeasure] [κ.IsHaarMeasure] (x : FullGroupCStarAlgebra G μ) :
    haarMeasureEquiv G ν κ (haarMeasureEquiv G μ ν x) = haarMeasureEquiv G μ κ x :=
  induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) fun _ => by simp
theorem haarMeasureEquiv_trans (μ ν κ : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    [κ.IsHaarMeasure] :
    (haarMeasureEquiv G μ ν).trans (haarMeasureEquiv G ν κ) = haarMeasureEquiv G μ κ :=
  StarAlgEquiv.ext (haarMeasureEquiv_apply_haarMeasureEquiv μ ν κ)

/-- `haarMeasureEquiv` intertwines the canonical unitary generator maps `groupMultiplier`. -/
@[simp] theorem congr_haarMeasureEquiv_groupMultiplier (μ ν : Measure G) [μ.IsHaarMeasure]
    [ν.IsHaarMeasure] (r : G) :
    DoubleCentralizer.congr (haarMeasureEquiv G μ ν)
        (groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)) =
      (groupMultiplier G ν r : 𝓜(ℂ, FullGroupCStarAlgebra G ν)) := by
  refine DoubleCentralizer.ext_fst fun x => ?_
  induction x using induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f => simp

/-- `haarMeasureEquiv` intertwines extended integrated unitary representations on `C⋆(G)`. -/
@[simp] theorem _root_.ContRepresentation.IsUnitary.integratedGroupCStar_haarMeasureEquiv
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {U : ContRepresentation ℂ G H} (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure] (x : FullGroupCStarAlgebra G μ) :
    hU.integratedGroupCStar hcont ν (haarMeasureEquiv G μ ν x) =
      hU.integratedGroupCStar hcont μ x := by
  induction x using induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f => simp [hU.integratedStarAlgHom_haarMeasureEquiv]

end TauCeti.FullGroupCStarAlgebra
end HaarMeasureEquiv
end

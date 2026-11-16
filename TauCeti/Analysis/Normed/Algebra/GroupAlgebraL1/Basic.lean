/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Topology.Algebra.Module.Star
public import TauCeti.MeasureTheory.Function.Lp.Star
public import TauCeti.MeasureTheory.Group.Convolution.ApproximateIdentity
public import TauCeti.MeasureTheory.Group.Convolution.Pointwise
import TauCeti.MeasureTheory.Function.Lp.LocallyCompact

/-!
# The `L¹` group Banach `⋆`-algebra

For a locally compact group `G` equipped with a left Haar measure `μ` and an `RCLike` scalar field
`𝕜` (`ℝ` or `ℂ`), the Bochner space `L¹(G, μ; 𝕜)` carries a natural nonunital Banach `⋆`-algebra
structure under group convolution
`(f * g)(x) = ∫ y, f y * g (y⁻¹ * x) ∂μ`
and the modular-weighted involution
`f*(x) = c(x) • star (f x⁻¹)`,
where `c = MeasureTheory.Measure.modularCharacter : G →* ℝ≥0` is the modular character of `G`.

Because `MeasureTheory.Lp 𝕜 1 μ` already carries pointwise `Star` (see
`TauCeti.MeasureTheory.Function.Lp.Star`) and because `Lp` unfolds to a `Subtype`, equipping
`Lp 𝕜 1 μ` or `WithConv (Lp 𝕜 1 μ)` directly would collide with pointwise conjugation or additive
convolution instances. Following `TauCeti.CStarAction.ConvolutionAlgebra`, we package the group
algebra on a dedicated one-field carrier `TauCeti.GroupAlgebraL1 𝕜 μ` with projections
`GroupAlgebraL1.toConv` and `GroupAlgebraL1.ofConv : GroupAlgebraL1 𝕜 μ → Lp 𝕜 1 μ`.

Each layer assumes only the hypotheses it genuinely uses:

1. **Banach space structure (`GroupAlgebraL1.linearIsometryEquiv`):** Over any measure space
   `(G, μ)` and normed group/module `𝕜`, `GroupAlgebraL1 𝕜 μ` inherits the `L¹` norm, scalar
   actions, and completeness from `Lp 𝕜 1 μ`.
2. **Nonunital Banach algebra (`instNonUnitalNormedRing`):** When `G` is a topological group with
   Borel `σ`-algebra and `μ` is left-invariant, locally finite, and inner regular for compact sets
   of finite measure, operator convolution `MeasureTheory.Lp.convolutionL` equips
   `GroupAlgebraL1 𝕜 μ` with a `NonUnitalNormedRing` structure satisfying `‖f * g‖ ≤ ‖f‖ * ‖g‖`.
3. **Pointwise convolution formulas (`ofConv_mul_ae_eq`, `ofConv_mul_ae_eq_right`):** On a locally
   compact Hausdorff group with a regular left Haar measure `μ`, `(f * g).ofConv` agrees `μ`-almost
   everywhere both with `x ↦ ∫ y, f y * g (y⁻¹ * x) ∂μ` and with the right-variable form
   `x ↦ ∫ z, c(z) • (f (x * z⁻¹) * g z) ∂μ`, independently of the chosen `L¹` representatives.
4. **Banach `⋆`-algebra (`instStarRing`, `instNormedStarGroup`, `instStarModule`):** On any locally
   compact group with a regular left Haar measure `μ` (without `T2Space G`), composing
   `MeasureTheory.Lp.modularInversion` with pointwise conjugation gives an isometric
   conjugate-linear anti-multiplicative involution.
5. **Isometric left and right translations (`leftTranslation`, `rightTranslation`):** Strongly
   continuous isometric actions of `G` compatible with convolution and the involution
   (`star (L_g f) = R_g (star f)`).
6. **Haar-normalization comparison (`smulMeasureStarAlgEquiv`, `haarStarAlgEquiv`):** Rescaling by
   `MeasureTheory.Measure.haarScalarFactor μ' μ` yields a canonical isometric `⋆`-algebra
   isomorphism `GroupAlgebraL1 𝕜 μ' ≃⋆ₐ[𝕜] GroupAlgebraL1 𝕜 μ` between any two regular left Haar
   measures `μ'` and `μ` on `G`, with no second-countability or `σ`-compactness assumption.

## Main definitions and statements

* `MeasureTheory.Lp.star_leftTranslation`, `MeasureTheory.Lp.modularInversion_star`,
  `MeasureTheory.Lp.star_convolutionL`: compatibility of pointwise `star` on `Lp` with left
  translation, modular inversion, and operator convolution.
* `TauCeti.GroupAlgebraL1 𝕜 μ`: the `L¹` group algebra carrier wrapping `Lp 𝕜 1 μ`.
* `TauCeti.GroupAlgebraL1.linearIsometryEquiv`: isometric linear equivalence with `Lp 𝕜 1 μ`.
* `TauCeti.GroupAlgebraL1.toL1`: constructor from an integrable function `f : G → 𝕜`.
* `TauCeti.GroupAlgebraL1.leftTranslation`, `TauCeti.GroupAlgebraL1.rightTranslation`: strongly
  continuous isometric translation actions of `G`.
* `TauCeti.GroupAlgebraL1.rescaleLinearIsometryEquiv`,
  `TauCeti.GroupAlgebraL1.smulMeasureStarAlgEquiv`: isometric `⋆`-algebra isomorphism for positive
  scalar multiples `c • μ` (`c : ℝ≥0`, `c ≠ 0`).
* `TauCeti.GroupAlgebraL1.haarLinearIsometryEquiv`, `TauCeti.GroupAlgebraL1.haarStarAlgEquiv`:
  canonical isometric `⋆`-algebra isomorphism between any two regular left Haar measures on `G`.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., §VII.9.
* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., §2.5.
* V. Runde, *Lectures on Amenability*, Lecture Notes in Mathematics 1774, Appendix A.
-/

public section

noncomputable section

open Filter Function MeasureTheory MeasureTheory.Measure Topology
open scoped ENNReal NNReal

namespace MeasureTheory.Lp

section StarHelpers

variable {G E 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Pointwise `star` on `Lp` commutes with left translation. -/
theorem star_leftTranslation [μ.IsMulLeftInvariant] [NormedAddCommGroup E] [StarAddMonoid E]
    [NormedStarGroup E] [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (g : G) (f : Lp E p μ) :
    star (leftTranslation μ p 𝕜 g f) = leftTranslation μ p 𝕜 g (star f) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_star (leftTranslation μ p 𝕜 g f), coeFn_leftTranslation (𝕜 := 𝕜) g f,
    coeFn_leftTranslation (𝕜 := 𝕜) g (star f),
    (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae (coeFn_star f)]
    with x hx₁ hx₂ hx₃ hx₄
  rw [hx₁, Pi.star_apply, hx₂, hx₃, hx₄, Pi.star_apply]

/-- Pointwise `star` on `Lp` commutes with the modular inversion `J`. -/
theorem modularInversion_star [LocallyCompactSpace G] [μ.IsHaarMeasure] [μ.Regular]
    [NormedAddCommGroup E] [StarAddMonoid E] [NormedStarGroup E] [NormedSpace ℝ E] [StarModule ℝ E]
    [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [SMulCommClass ℝ 𝕜 E] (f : Lp E p μ) :
    modularInversion μ p 𝕜 (star f) = star (modularInversion μ p 𝕜 f) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_modularInversion (𝕜 := 𝕜) (star f),
    coeFn_star (modularInversion μ p 𝕜 f), coeFn_modularInversion (𝕜 := 𝕜) f,
    (quasiMeasurePreserving_inv_of_regular μ).ae (coeFn_star f)] with x hx₁ hx₂ hx₃ hx₄
  rw [hx₁, hx₂, Pi.star_apply, hx₃, star_smul, star_trivial (_ : ℝ), hx₄, Pi.star_apply]

/-- Pointwise `star` on `L¹(G, μ; 𝕜)` distributes over operator convolution:
`star (h ⋆ f) = star h ⋆ star f`. -/
theorem star_convolutionL [μ.IsMulLeftInvariant] [IsLocallyFiniteMeasure μ]
    [μ.InnerRegularCompactLTTop] [RCLike 𝕜] (h f : Lp 𝕜 1 μ) :
    star (convolutionL μ 1 ENNReal.one_ne_top h f) =
      convolutionL μ 1 ENNReal.one_ne_top (star h) (star f) := by
  have hcomm := (starL' ℝ : Lp 𝕜 1 μ ≃L[ℝ] Lp 𝕜 1 μ).integral_comp_comm
    (μ := μ) fun y => h y • leftTranslation μ 1 𝕜 y f
  rw [convolutionL_apply, convolutionL_apply, ← starL'_apply (R := ℝ), ← hcomm]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_star h] with y hy
  rw [starL'_apply, star_smul, hy, Pi.star_apply, star_leftTranslation]

end StarHelpers

end MeasureTheory.Lp

namespace TauCeti

/-- The `L¹` group algebra of `(G, μ)` over `𝕜`: a one-field wrapper around `MeasureTheory.Lp 𝕜 1 μ`
carrying group convolution as multiplication and the modular-weighted involution
`f*(x) = c(x) • star (f x⁻¹)` as `star`. Use `GroupAlgebraL1.toConv` and `GroupAlgebraL1.ofConv`
to pass to and from `Lp 𝕜 1 μ`. -/
structure GroupAlgebraL1 (𝕜 : Type*) {G : Type*} [MeasurableSpace G] [NormedAddCommGroup 𝕜]
    (μ : Measure G) where
  /-- Regard an `L¹` equivalence class as an element of the group convolution algebra. -/
  toConv ::
  /-- The underlying `L¹` equivalence class of an element of the group convolution algebra. -/
  ofConv : Lp 𝕜 1 μ

namespace GroupAlgebraL1

/-! ### Linear and Banach space structure -/

section NormedSpace

variable {G R S 𝕜 : Type*} [MeasurableSpace G] [NormedAddCommGroup 𝕜] {μ : Measure G}

@[simp]
theorem ofConv_toConv (f : Lp 𝕜 1 μ) : (toConv f).ofConv = f :=
  (rfl)

@[simp]
theorem toConv_ofConv (f : GroupAlgebraL1 𝕜 μ) : toConv f.ofConv = f :=
  (rfl)

theorem ofConv_injective : Function.Injective (ofConv : GroupAlgebraL1 𝕜 μ → Lp 𝕜 1 μ) :=
  fun f g h => by rw [← toConv_ofConv f, h, toConv_ofConv]

theorem toConv_injective : Function.Injective (toConv : Lp 𝕜 1 μ → GroupAlgebraL1 𝕜 μ) :=
  fun f g h => by rw [← ofConv_toConv (μ := μ) f, h, ofConv_toConv]

@[ext]
theorem ext {f g : GroupAlgebraL1 𝕜 μ} (h : f.ofConv = g.ofConv) : f = g :=
  ofConv_injective h

/-- Two elements of `GroupAlgebraL1 𝕜 μ` are equal if their `L¹` representatives agree `μ`-almost
everywhere. -/
theorem ext_ae {f g : GroupAlgebraL1 𝕜 μ} (h : f.ofConv =ᵐ[μ] g.ofConv) : f = g :=
  ext (Lp.ext h)

variable (𝕜 μ) in
/-- `GroupAlgebraL1.ofConv` and `GroupAlgebraL1.toConv` as an equivalence. -/
@[expose] def equiv : GroupAlgebraL1 𝕜 μ ≃ Lp 𝕜 1 μ where
  toFun := ofConv
  invFun := toConv
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem equiv_apply (f : GroupAlgebraL1 𝕜 μ) : equiv 𝕜 μ f = f.ofConv :=
  rfl

@[simp]
theorem equiv_symm_apply (f : Lp 𝕜 1 μ) : (equiv 𝕜 μ).symm f = toConv f :=
  rfl

instance : Zero (GroupAlgebraL1 𝕜 μ) := ⟨⟨0⟩⟩
instance : Add (GroupAlgebraL1 𝕜 μ) := ⟨fun f g => ⟨f.ofConv + g.ofConv⟩⟩
instance : Neg (GroupAlgebraL1 𝕜 μ) := ⟨fun f => ⟨-f.ofConv⟩⟩
instance : Sub (GroupAlgebraL1 𝕜 μ) := ⟨fun f g => ⟨f.ofConv - g.ofConv⟩⟩
instance [SMul R (Lp 𝕜 1 μ)] : SMul R (GroupAlgebraL1 𝕜 μ) := ⟨fun r f => ⟨r • f.ofConv⟩⟩

@[simp] theorem ofConv_zero : (0 : GroupAlgebraL1 𝕜 μ).ofConv = 0 := (rfl)
@[simp] theorem toConv_zero : toConv (0 : Lp 𝕜 1 μ) = 0 := (rfl)

@[simp]
theorem ofConv_add (f g : GroupAlgebraL1 𝕜 μ) : (f + g).ofConv = f.ofConv + g.ofConv :=
  (rfl)

@[simp]
theorem toConv_add (f g : Lp 𝕜 1 μ) : toConv (f + g) = toConv f + toConv g :=
  (rfl)

@[simp]
theorem ofConv_neg (f : GroupAlgebraL1 𝕜 μ) : (-f).ofConv = -f.ofConv :=
  (rfl)

@[simp]
theorem toConv_neg (f : Lp 𝕜 1 μ) : toConv (-f) = -toConv f :=
  (rfl)

@[simp]
theorem ofConv_sub (f g : GroupAlgebraL1 𝕜 μ) : (f - g).ofConv = f.ofConv - g.ofConv :=
  (rfl)

@[simp]
theorem toConv_sub (f g : Lp 𝕜 1 μ) : toConv (f - g) = toConv f - toConv g :=
  (rfl)

@[simp]
theorem ofConv_smul [SMul R (Lp 𝕜 1 μ)] (r : R) (f : GroupAlgebraL1 𝕜 μ) :
    (r • f).ofConv = r • f.ofConv :=
  (rfl)

@[simp]
theorem toConv_smul [SMul R (Lp 𝕜 1 μ)] (r : R) (f : Lp 𝕜 1 μ) :
    toConv (r • f) = r • toConv f :=
  (rfl)

instance : AddCommGroup (GroupAlgebraL1 𝕜 μ) :=
  Function.Injective.addCommGroup ofConv ofConv_injective rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

variable (𝕜 μ) in
/-- `GroupAlgebraL1.ofConv` as an additive equivalence with `Lp 𝕜 1 μ`. -/
@[expose] def addEquiv : GroupAlgebraL1 𝕜 μ ≃+ Lp 𝕜 1 μ where
  __ := equiv 𝕜 μ
  map_add' _ _ := rfl

@[simp]
theorem addEquiv_apply (f : GroupAlgebraL1 𝕜 μ) : addEquiv 𝕜 μ f = f.ofConv :=
  rfl

@[simp]
theorem addEquiv_symm_apply (f : Lp 𝕜 1 μ) : (addEquiv 𝕜 μ).symm f = toConv f :=
  rfl

instance [Semiring R] [Module R (Lp 𝕜 1 μ)] : Module R (GroupAlgebraL1 𝕜 μ) :=
  Function.Injective.module R (addEquiv 𝕜 μ).toAddMonoidHom ofConv_injective fun _ _ => rfl

instance [SMul R (Lp 𝕜 1 μ)] [SMul S (Lp 𝕜 1 μ)] [SMul R S]
    [IsScalarTower R S (Lp 𝕜 1 μ)] :
    IsScalarTower R S (GroupAlgebraL1 𝕜 μ) where
  smul_assoc r s f := ext <| smul_assoc r s f.ofConv

instance [SMul R (Lp 𝕜 1 μ)] [SMul S (Lp 𝕜 1 μ)] [SMulCommClass R S (Lp 𝕜 1 μ)] :
    SMulCommClass R S (GroupAlgebraL1 𝕜 μ) where
  smul_comm r s f := ext <| smul_comm r s f.ofConv

variable (R 𝕜 μ) in
/-- `GroupAlgebraL1.ofConv` as an `R`-linear equivalence with `Lp 𝕜 1 μ`. -/
@[expose] def linearEquiv [Semiring R] [Module R (Lp 𝕜 1 μ)] :
    GroupAlgebraL1 𝕜 μ ≃ₗ[R] Lp 𝕜 1 μ where
  __ := addEquiv 𝕜 μ
  map_smul' _ _ := rfl

@[simp]
theorem linearEquiv_apply [Semiring R] [Module R (Lp 𝕜 1 μ)]
    (f : GroupAlgebraL1 𝕜 μ) : linearEquiv R 𝕜 μ f = f.ofConv :=
  rfl

@[simp]
theorem linearEquiv_symm_apply [Semiring R] [Module R (Lp 𝕜 1 μ)]
    (f : Lp 𝕜 1 μ) : (linearEquiv R 𝕜 μ).symm f = toConv f :=
  rfl

instance : NormedAddCommGroup (GroupAlgebraL1 𝕜 μ) :=
  NormedAddCommGroup.induced _ _ (addEquiv 𝕜 μ) (addEquiv 𝕜 μ).injective

@[simp]
theorem norm_ofConv (f : GroupAlgebraL1 𝕜 μ) : ‖f.ofConv‖ = ‖f‖ :=
  (rfl)

@[simp]
theorem norm_toConv (f : Lp 𝕜 1 μ) : ‖toConv f‖ = ‖f‖ :=
  (rfl)

/-- The `L¹` norm of `f : GroupAlgebraL1 𝕜 μ` is `∫ x, ‖f.ofConv x‖ ∂μ`. -/
theorem norm_eq_integral_norm (f : GroupAlgebraL1 𝕜 μ) :
    ‖f‖ = ∫ x, ‖f.ofConv x‖ ∂μ :=
  L1.norm_eq_integral_norm f.ofConv

instance [NormedField R] [NormedSpace R 𝕜] : NormedSpace R (GroupAlgebraL1 𝕜 μ) :=
  NormedSpace.induced R _ _ (linearEquiv R 𝕜 μ)

variable (R 𝕜 μ) in
/-- `GroupAlgebraL1.ofConv` as an `R`-linear isometry equivalence with `Lp 𝕜 1 μ`. -/
@[expose] def linearIsometryEquiv [NormedField R] [NormedSpace R 𝕜] :
    GroupAlgebraL1 𝕜 μ ≃ₗᵢ[R] Lp 𝕜 1 μ where
  __ := linearEquiv R 𝕜 μ
  norm_map' := norm_ofConv

@[simp]
theorem linearIsometryEquiv_apply [NormedField R] [NormedSpace R 𝕜] (f : GroupAlgebraL1 𝕜 μ) :
    linearIsometryEquiv R 𝕜 μ f = f.ofConv :=
  rfl

@[simp]
theorem linearIsometryEquiv_symm_apply [NormedField R] [NormedSpace R 𝕜] (f : Lp 𝕜 1 μ) :
    (linearIsometryEquiv R 𝕜 μ).symm f = toConv f :=
  rfl

instance [CompleteSpace 𝕜] : CompleteSpace (GroupAlgebraL1 𝕜 μ) :=
  (completeSpace_congr (e := equiv 𝕜 μ)
    (Isometry.of_dist_eq fun _ _ => rfl).isUniformEmbedding).2 inferInstance

/-- Construct an element of `GroupAlgebraL1 𝕜 μ` from a `μ`-integrable function `f : G → 𝕜`. -/
def toL1 {f : G → 𝕜} (hf : Integrable f μ) : GroupAlgebraL1 𝕜 μ :=
  toConv (hf.toL1 f)

@[simp]
theorem ofConv_toL1 {f : G → 𝕜} (hf : Integrable f μ) : (toL1 hf).ofConv = hf.toL1 f :=
  (rfl)

theorem coeFn_ofConv_toL1 {f : G → 𝕜} (hf : Integrable f μ) :
    (toL1 hf).ofConv =ᵐ[μ] f :=
  hf.coeFn_toL1

/-- On a weakly locally compact `R₁` space with a regular Borel measure, classes of compactly
supported continuous functions are dense in `GroupAlgebraL1 𝕜 μ`. -/
theorem dense_setOf_continuous_hasCompactSupport [TopologicalSpace G] [R1Space G]
    [WeaklyLocallyCompactSpace G] [BorelSpace G] [μ.Regular] [NormedSpace ℝ 𝕜] :
    Dense {u : GroupAlgebraL1 𝕜 μ |
      ∃ f : G → 𝕜, Continuous f ∧ HasCompactSupport f ∧ u.ofConv =ᵐ[μ] f} := by
  intro u
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨v, ⟨f, hfc, hfs, hvf⟩, hv⟩ :=
    Metric.mem_closure_iff.1
      (Lp.dense_setOf_continuous_hasCompactSupport ENNReal.one_ne_top u.ofConv) ε hε
  exact ⟨toConv v, ⟨f, hfc, hfs, hvf⟩, hv⟩

end NormedSpace

/-! ### Nonunital Banach algebra structure -/

section ConvolutionAlgebra

variable {G 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
  [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [NormedSpace ℝ 𝕜] [SMulCommClass ℝ 𝕜 𝕜]

instance : Mul (GroupAlgebraL1 𝕜 μ) where
  mul f g := toConv (Lp.convolutionL μ 1 ENNReal.one_ne_top f.ofConv g.ofConv)

@[simp]
theorem ofConv_mul (f g : GroupAlgebraL1 𝕜 μ) :
    (f * g).ofConv = Lp.convolutionL μ 1 ENNReal.one_ne_top f.ofConv g.ofConv :=
  (rfl)

@[simp]
theorem toConv_convolutionL (f g : Lp 𝕜 1 μ) :
    toConv (Lp.convolutionL μ 1 ENNReal.one_ne_top f g) = toConv f * toConv g :=
  (rfl)

instance : NonUnitalNonAssocRing (GroupAlgebraL1 𝕜 μ) where
  left_distrib f g h := ext <| by
    rw [ofConv_mul, ofConv_add, ofConv_add, ofConv_mul, ofConv_mul, map_add]
  right_distrib f g h := ext <| by
    rw [ofConv_mul, ofConv_add, ofConv_add, ofConv_mul, ofConv_mul, map_add,
      FunLike.coe_add, Pi.add_apply]
  zero_mul f := ext <| by
    rw [ofConv_mul, ofConv_zero, map_zero, FunLike.coe_zero, Pi.zero_apply]
  mul_zero f := ext <| by
    rw [ofConv_mul, ofConv_zero, map_zero]

instance : IsScalarTower 𝕜 (GroupAlgebraL1 𝕜 μ) (GroupAlgebraL1 𝕜 μ) where
  smul_assoc c f g := ext <| by
    rw [smul_eq_mul, smul_eq_mul, ofConv_mul, ofConv_smul, ofConv_smul, ofConv_mul, map_smul,
      FunLike.coe_smul, Pi.smul_apply]

instance : SMulCommClass 𝕜 (GroupAlgebraL1 𝕜 μ) (GroupAlgebraL1 𝕜 μ) where
  smul_comm c f g := ext <| by
    rw [smul_eq_mul, smul_eq_mul, ofConv_smul, ofConv_mul, ofConv_mul, ofConv_smul, map_smul]

end NontriviallyNormedField

section RCLike

variable [RCLike 𝕜]

instance : NonUnitalRing (GroupAlgebraL1 𝕜 μ) :=
  { (inferInstance : NonUnitalNonAssocRing (GroupAlgebraL1 𝕜 μ)) with
    mul_assoc f g h := ext <| by
      rw [ofConv_mul, ofConv_mul, ofConv_mul, ofConv_mul,
        Lp.convolutionL_assoc f.ofConv g.ofConv h.ofConv] }

instance : NonUnitalNormedRing (GroupAlgebraL1 𝕜 μ) :=
  { (inferInstance : NormedAddCommGroup (GroupAlgebraL1 𝕜 μ)),
    (inferInstance : NonUnitalRing (GroupAlgebraL1 𝕜 μ)) with
    norm_mul_le f g := Lp.norm_convolutionL_apply_le f.ofConv g.ofConv }

/-- Submultiplicativity of the `L¹` convolution norm: `‖f * g‖ ≤ ‖f‖ * ‖g‖`. -/
theorem norm_mul_le (f g : GroupAlgebraL1 𝕜 μ) : ‖f * g‖ ≤ ‖f‖ * ‖g‖ :=
  _root_.norm_mul_le f g

end RCLike

end ConvolutionAlgebra

/-! ### Pointwise convolution formulas -/

section Pointwise

variable {G 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular] [RCLike 𝕜]

/-- On a locally compact Hausdorff group with a regular left Haar measure `μ`, the product `f * g`
in `GroupAlgebraL1 𝕜 μ` is represented `μ`-almost everywhere by `x ↦ ∫ y, f y * g (y⁻¹ * x) ∂μ`. -/
theorem ofConv_mul_ae_eq (f g : GroupAlgebraL1 𝕜 μ) :
    (f * g).ofConv =ᵐ[μ] fun x => ∫ y, f.ofConv y * g.ofConv (y⁻¹ * x) ∂μ := by
  simpa only [ofConv_mul, smul_eq_mul] using
    Lp.convolutionL_ae_eq (hp := ENNReal.one_ne_top) f.ofConv g.ofConv

/-- **Right-variable pointwise convolution formula.** On a locally compact Hausdorff group with a
regular left Haar measure `μ`, `(f * g)(x) = ∫ z, c(z) • (f (x * z⁻¹) * g z) ∂μ` for `μ`-almost
every `x`, where `c` is the modular character. -/
theorem ofConv_mul_ae_eq_right (f g : GroupAlgebraL1 𝕜 μ) :
    (f * g).ofConv =ᵐ[μ]
      fun x => ∫ z, (modularCharacter z : ℝ) • (f.ofConv (x * z⁻¹) * g.ofConv z) ∂μ :=
  (ofConv_mul_ae_eq f g).trans <| .of_forall fun x => by
    simpa only [smul_eq_mul] using
      TauCeti.integral_smul_inv_mul_eq_integral_modularCharacter_smul
        (μ := μ) f.ofConv g.ofConv x

/-- Representative-independent pointwise formula for the product of `toL1` elements in
`GroupAlgebraL1 𝕜 μ`. -/
theorem ofConv_toL1_mul_toL1_ae_eq {f g : G → 𝕜} (hf : Integrable f μ) (hg : Integrable g μ) :
    (toL1 hf * toL1 hg).ofConv =ᵐ[μ] fun x => ∫ y, f y * g (y⁻¹ * x) ∂μ := by
  simpa only [ofConv_mul, ofConv_toL1, smul_eq_mul] using hf.convolutionL_toL1_ae_eq hg

end Pointwise

/-! ### Modular involution and Banach `⋆`-algebra structure -/

section StarAlgebra

variable {G 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular] [RCLike 𝕜]

instance : Star (GroupAlgebraL1 𝕜 μ) where
  star f := toConv (Lp.modularInversion μ 1 𝕜 (star f.ofConv))

@[simp]
theorem ofConv_star (f : GroupAlgebraL1 𝕜 μ) :
    (star f).ofConv = Lp.modularInversion μ 1 𝕜 (star f.ofConv) :=
  (rfl)

/-- The modular involution on `GroupAlgebraL1 𝕜 μ` is represented `μ`-almost everywhere by
`x ↦ c(x) • star (f x⁻¹)`, where `c` is the modular character of `G`. -/
theorem ofConv_star_ae_eq (f : GroupAlgebraL1 𝕜 μ) :
    (star f).ofConv =ᵐ[μ] fun x => (modularCharacter x : ℝ) • star (f.ofConv x⁻¹) := by
  filter_upwards [Lp.coeFn_modularInversion (𝕜 := 𝕜) (star f.ofConv),
    (quasiMeasurePreserving_inv_of_regular μ).ae (Lp.coeFn_star f.ofConv)] with x hx₁ hx₂
  rw [ofConv_star, hx₁, ENNReal.toReal_one, inv_one, Real.rpow_one, hx₂, Pi.star_apply]

instance : InvolutiveStar (GroupAlgebraL1 𝕜 μ) where
  star_involutive f := ext <| by
    rw [ofConv_star, ofConv_star, Lp.modularInversion_star,
      Lp.modularInversion_modularInversion, star_star]

instance : StarAddMonoid (GroupAlgebraL1 𝕜 μ) where
  star_add f g := ext <| by rw [ofConv_star, ofConv_add, star_add, map_add]; rfl

instance : StarRing (GroupAlgebraL1 𝕜 μ) :=
  { (inferInstance : StarAddMonoid (GroupAlgebraL1 𝕜 μ)) with
    star_mul f g := ext <| by
      rw [ofConv_star, ofConv_mul, Lp.star_convolutionL, Lp.modularInversion_convolutionL,
        ofConv_mul, ofConv_star, ofConv_star] }

instance : NormedStarGroup (GroupAlgebraL1 𝕜 μ) where
  norm_star_le f := by
    rw [← norm_ofConv, ofConv_star, LinearIsometryEquiv.norm_map, norm_star, norm_ofConv]

instance : StarModule 𝕜 (GroupAlgebraL1 𝕜 μ) where
  star_smul c f := ext <| by
    rw [ofConv_star, ofConv_smul, star_smul, map_smul, ofConv_smul, ofConv_star]

end StarAlgebra

/-! ### Isometric left and right translation actions -/

section Translations

variable {G 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G}

section Left

variable [μ.IsMulLeftInvariant] [RCLike 𝕜]

variable (𝕜 μ) in
/-- **Left translation** `g ↦ L_g` on `GroupAlgebraL1 𝕜 μ`, acting on representatives by
`(L_g f)(x) = f (g⁻¹ * x)`, as a group homomorphism into `𝕜`-linear isometry equivalences. -/
def leftTranslation : G →* (GroupAlgebraL1 𝕜 μ ≃ₗᵢ[𝕜] GroupAlgebraL1 𝕜 μ) where
  toFun g :=
    (linearIsometryEquiv 𝕜 𝕜 μ).trans
      ((Lp.leftTranslation μ 1 𝕜 g).trans (linearIsometryEquiv 𝕜 𝕜 μ).symm)
  map_one' := LinearIsometryEquiv.ext fun f => ext <| by simp
  map_mul' g₁ g₂ := LinearIsometryEquiv.ext fun f => ext <| by
    simp [map_mul, LinearIsometryEquiv.coe_mul]

@[simp]
theorem ofConv_leftTranslation (g : G) (f : GroupAlgebraL1 𝕜 μ) :
    (leftTranslation 𝕜 μ g f).ofConv = Lp.leftTranslation μ 1 𝕜 g f.ofConv := by
  simp [leftTranslation]

theorem ofConv_leftTranslation_ae_eq (g : G) (f : GroupAlgebraL1 𝕜 μ) :
    (leftTranslation 𝕜 μ g f).ofConv =ᵐ[μ] fun x => f.ofConv (g⁻¹ * x) := by
  rw [ofConv_leftTranslation]
  exact Lp.coeFn_leftTranslation (𝕜 := 𝕜) g f.ofConv

/-- Left translation is strongly continuous on `GroupAlgebraL1 𝕜 μ`. -/
theorem continuous_leftTranslation_apply [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    (f : GroupAlgebraL1 𝕜 μ) :
    Continuous fun g : G => leftTranslation 𝕜 μ g f :=
  (linearIsometryEquiv 𝕜 𝕜 μ).symm.continuous.comp
    (Lp.continuous_leftTranslation_apply (𝕜 := 𝕜) ENNReal.one_ne_top f.ofConv)

/-- Convolution is left-equivariant: `L_g (f * h) = (L_g f) * h`. -/
@[simp]
theorem leftTranslation_mul [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    (g : G) (f h : GroupAlgebraL1 𝕜 μ) :
    leftTranslation 𝕜 μ g (f * h) = leftTranslation 𝕜 μ g f * h :=
  ext <| by
    rw [ofConv_leftTranslation, ofConv_mul, ofConv_mul, ofConv_leftTranslation,
      Lp.leftTranslation_convolutionL]

end Left

section Right

variable [LocallyCompactSpace G] [μ.IsHaarMeasure] [μ.Regular] [RCLike 𝕜]

variable (𝕜 μ) in
/-- **Right translation** `g ↦ R_g` on `GroupAlgebraL1 𝕜 μ`, acting on representatives by
`(R_g f)(x) = c(g⁻¹) • f (x * g)`, as a group homomorphism into `𝕜`-linear isometry equivalences. -/
def rightTranslation : G →* (GroupAlgebraL1 𝕜 μ ≃ₗᵢ[𝕜] GroupAlgebraL1 𝕜 μ) where
  toFun g :=
    (linearIsometryEquiv 𝕜 𝕜 μ).trans
      ((Lp.rightTranslation μ 1 𝕜 g).trans (linearIsometryEquiv 𝕜 𝕜 μ).symm)
  map_one' := LinearIsometryEquiv.ext fun f => ext <| by simp
  map_mul' g₁ g₂ := LinearIsometryEquiv.ext fun f => ext <| by
    simp [map_mul, LinearIsometryEquiv.coe_mul]

@[simp]
theorem ofConv_rightTranslation (g : G) (f : GroupAlgebraL1 𝕜 μ) :
    (rightTranslation 𝕜 μ g f).ofConv = Lp.rightTranslation μ 1 𝕜 g f.ofConv := by
  simp [rightTranslation]

theorem ofConv_rightTranslation_ae_eq (g : G) (f : GroupAlgebraL1 𝕜 μ) :
    (rightTranslation 𝕜 μ g f).ofConv =ᵐ[μ]
      fun x => (modularCharacter g⁻¹ : ℝ) • f.ofConv (x * g) := by
  rw [ofConv_rightTranslation]
  simpa only [ENNReal.toReal_one, inv_one, Real.rpow_one] using
    Lp.coeFn_rightTranslation (𝕜 := 𝕜) g f.ofConv

/-- Right translation is strongly continuous on `GroupAlgebraL1 𝕜 μ`. -/
theorem continuous_rightTranslation_apply (f : GroupAlgebraL1 𝕜 μ) :
    Continuous fun g : G => rightTranslation 𝕜 μ g f :=
  (linearIsometryEquiv 𝕜 𝕜 μ).symm.continuous.comp
    (Lp.continuous_rightTranslation_apply (𝕜 := 𝕜) ENNReal.one_ne_top f.ofConv)

/-- Convolution is right-equivariant on the second factor: `R_g (f * h) = f * R_g h`. -/
@[simp]
theorem rightTranslation_mul (g : G) (f h : GroupAlgebraL1 𝕜 μ) :
    rightTranslation 𝕜 μ g (f * h) = f * rightTranslation 𝕜 μ g h :=
  ext <| by
    rw [ofConv_rightTranslation, ofConv_mul, ofConv_mul, ofConv_rightTranslation,
      Lp.rightTranslation_convolutionL]

/-- The modular involution intertwines left and right translation:
`star (L_g f) = R_g (star f)`. -/
@[simp]
theorem star_leftTranslation (g : G) (f : GroupAlgebraL1 𝕜 μ) :
    star (leftTranslation 𝕜 μ g f) = rightTranslation 𝕜 μ g (star f) :=
  ext <| by
    rw [ofConv_star, ofConv_leftTranslation, Lp.star_leftTranslation, ofConv_rightTranslation,
      ofConv_star, Lp.rightTranslation_apply, Lp.modularInversion_modularInversion]

/-- The modular involution intertwines right and left translation:
`star (R_g f) = L_g (star f)`. -/
@[simp]
theorem star_rightTranslation (g : G) (f : GroupAlgebraL1 𝕜 μ) :
    star (rightTranslation 𝕜 μ g f) = leftTranslation 𝕜 μ g (star f) := by
  rw [← star_inj, star_star, star_leftTranslation, star_star]

end Right

end Translations

/-! ### Dependence on the Haar normalization -/

section HaarComparison

section RescaleMeasure

variable {G 𝕜 : Type*} [MeasurableSpace G] [RCLike 𝕜] {μ' μ : Measure G}

private theorem ae_of_eq_smul {c : ℝ≥0} (hc : c ≠ 0) (hμ : μ' = c • μ) {p : G → Prop}
    (hp : ∀ᵐ x ∂μ', p x) : ∀ᵐ x ∂μ, p x := by
  rwa [hμ, ae_smul_measure_iff hc] at hp

private theorem integrable_smul_of_eq_smul {c : ℝ≥0} (hc : c ≠ 0) (hμ : μ' = c • μ)
    (f : Lp 𝕜 1 μ') : Integrable (fun x => (c : ℝ) • f x) μ := by
  have hf : Integrable f ((c : ℝ≥0∞) • μ) := hμ ▸ L1.integrable_coeFn f
  exact ((integrable_smul_measure (ENNReal.coe_ne_zero.2 hc) ENNReal.coe_ne_top).1 hf).smul (c : ℝ)

private def rescaleₗ (c : ℝ≥0) (hc : c ≠ 0) (hμ : μ' = c • μ) :
    GroupAlgebraL1 𝕜 μ' →ₗ[𝕜] GroupAlgebraL1 𝕜 μ where
  toFun f := toL1 (integrable_smul_of_eq_smul hc hμ f.ofConv)
  map_add' f g := ext_ae <| by
    filter_upwards [coeFn_ofConv_toL1 (integrable_smul_of_eq_smul hc hμ (f + g).ofConv),
      Lp.coeFn_add (toL1 (integrable_smul_of_eq_smul hc hμ f.ofConv)).ofConv
        (toL1 (integrable_smul_of_eq_smul hc hμ g.ofConv)).ofConv,
      coeFn_ofConv_toL1 (integrable_smul_of_eq_smul hc hμ f.ofConv),
      coeFn_ofConv_toL1 (integrable_smul_of_eq_smul hc hμ g.ofConv),
      ae_of_eq_smul hc hμ (Lp.coeFn_add f.ofConv g.ofConv)] with x h₁ h₂ hf hg hadd
    rw [h₁, ofConv_add, ofConv_add, h₂, Pi.add_apply, hf, hg, hadd, Pi.add_apply, smul_add]
  map_smul' k f := ext_ae <| by
    filter_upwards [coeFn_ofConv_toL1 (integrable_smul_of_eq_smul hc hμ (k • f).ofConv),
      Lp.coeFn_smul k (toL1 (integrable_smul_of_eq_smul hc hμ f.ofConv)).ofConv,
      coeFn_ofConv_toL1 (integrable_smul_of_eq_smul hc hμ f.ofConv),
      ae_of_eq_smul hc hμ (Lp.coeFn_smul k f.ofConv)] with x h₁ h₂ hf hsmul
    rw [RingHom.id_apply, h₁, ofConv_smul, ofConv_smul, h₂, Pi.smul_apply, hf, hsmul, Pi.smul_apply,
      smul_comm (c : ℝ) k]

private theorem ofConv_rescaleₗ_ae_eq {c : ℝ≥0} (hc : c ≠ 0) (hμ : μ' = c • μ)
    (f : GroupAlgebraL1 𝕜 μ') :
    (rescaleₗ (𝕜 := 𝕜) c hc hμ f).ofConv =ᵐ[μ] fun x => (c : ℝ) • f.ofConv x :=
  coeFn_ofConv_toL1 _

private theorem norm_rescaleₗ {c : ℝ≥0} (hc : c ≠ 0) (hμ : μ' = c • μ)
    (f : GroupAlgebraL1 𝕜 μ') : ‖rescaleₗ (𝕜 := 𝕜) c hc hμ f‖ = ‖f‖ := by
  have hrhs : ∫ x, ‖f.ofConv x‖ ∂μ' = ∫ x, ‖f.ofConv x‖ ∂((c : ℝ≥0∞) • μ) :=
    congr_arg (integral · fun x => ‖f.ofConv x‖) hμ
  rw [norm_eq_integral_norm, norm_eq_integral_norm, hrhs, integral_smul_measure,
    ENNReal.coe_toReal, smul_eq_mul, ← integral_const_mul]
  refine integral_congr_ae ((ofConv_rescaleₗ_ae_eq hc hμ f).mono fun x hx => ?_)
  dsimp only
  rw [hx, norm_smul, Real.norm_of_nonneg c.coe_nonneg]

/-- If `μ' = c • μ` for a positive scalar `c : ℝ≥0` (`c ≠ 0`), rescaling functions by `(c : ℝ)`
defines a `𝕜`-linear isometry equivalence `GroupAlgebraL1 𝕜 μ' ≃ₗᵢ[𝕜] GroupAlgebraL1 𝕜 μ`. -/
def rescaleLinearIsometryEquiv (𝕜 : Type*) [RCLike 𝕜] {μ' μ : Measure G}
    (c : ℝ≥0) (hc : c ≠ 0) (hμ : μ' = c • μ) :
    GroupAlgebraL1 𝕜 μ' ≃ₗᵢ[𝕜] GroupAlgebraL1 𝕜 μ := by
  have hμ' : μ = c⁻¹ • μ' := by rw [hμ, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hinv : ∀ f : GroupAlgebraL1 𝕜 μ',
      rescaleₗ c⁻¹ (inv_ne_zero hc) hμ' (rescaleₗ c hc hμ f) = f := fun f => ext_ae <| by
    filter_upwards [ofConv_rescaleₗ_ae_eq (inv_ne_zero hc) hμ' (rescaleₗ c hc hμ f),
      ae_of_eq_smul (inv_ne_zero hc) hμ' (ofConv_rescaleₗ_ae_eq hc hμ f)] with x h₁ h₂
    rw [h₁, h₂, smul_smul, ← NNReal.coe_mul, inv_mul_cancel₀ hc, NNReal.coe_one, one_smul]
  have hrinv : ∀ g : GroupAlgebraL1 𝕜 μ,
      rescaleₗ c hc hμ (rescaleₗ c⁻¹ (inv_ne_zero hc) hμ' g) = g := fun g => ext_ae <| by
    filter_upwards [ofConv_rescaleₗ_ae_eq hc hμ (rescaleₗ c⁻¹ (inv_ne_zero hc) hμ' g),
      ae_of_eq_smul hc hμ (ofConv_rescaleₗ_ae_eq (inv_ne_zero hc) hμ' g)] with x h₁ h₂
    rw [h₁, h₂, smul_smul, ← NNReal.coe_mul, mul_inv_cancel₀ hc, NNReal.coe_one, one_smul]
  exact
    { toLinearEquiv := LinearEquiv.ofLinearMap (rescaleₗ c hc hμ)
        (rescaleₗ c⁻¹ (inv_ne_zero hc) hμ') (LinearMap.ext hrinv) (LinearMap.ext hinv)
      norm_map' := norm_rescaleₗ hc hμ }

theorem ofConv_rescaleLinearIsometryEquiv_ae_eq {c : ℝ≥0} (hc : c ≠ 0) (hμ : μ' = c • μ)
    (f : GroupAlgebraL1 𝕜 μ') :
    (rescaleLinearIsometryEquiv 𝕜 c hc hμ f).ofConv =ᵐ[μ] fun x => (c : ℝ) • f.ofConv x :=
  ofConv_rescaleₗ_ae_eq hc hμ f

end RescaleMeasure

section RescaleGroup

variable {G 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [RCLike 𝕜] {μ' μ : Measure G}

private theorem rescaleLinearIsometryEquiv_leftTranslation [μ'.IsMulLeftInvariant]
    [μ.IsMulLeftInvariant] {c : ℝ≥0} (hc : c ≠ 0) (hμ : μ' = c • μ) (g : G)
    (f : GroupAlgebraL1 𝕜 μ') :
    rescaleLinearIsometryEquiv 𝕜 c hc hμ (leftTranslation 𝕜 μ' g f) =
      leftTranslation 𝕜 μ g (rescaleLinearIsometryEquiv 𝕜 c hc hμ f) := by
  refine ext_ae ?_
  filter_upwards [ofConv_rescaleLinearIsometryEquiv_ae_eq hc hμ (leftTranslation 𝕜 μ' g f),
    ae_of_eq_smul hc hμ (ofConv_leftTranslation_ae_eq g f),
    ofConv_leftTranslation_ae_eq g (rescaleLinearIsometryEquiv 𝕜 c hc hμ f),
    (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae
      (ofConv_rescaleLinearIsometryEquiv_ae_eq hc hμ f)] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]

private theorem rescaleLinearIsometryEquiv_mul [μ'.IsMulLeftInvariant] [IsLocallyFiniteMeasure μ']
    [μ'.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant] [IsLocallyFiniteMeasure μ]
    [μ.InnerRegularCompactLTTop] {c : ℝ≥0} (hc : c ≠ 0) (hμ : μ' = c • μ)
    (f g : GroupAlgebraL1 𝕜 μ') :
    rescaleLinearIsometryEquiv 𝕜 c hc hμ (f * g) =
      rescaleLinearIsometryEquiv 𝕜 c hc hμ f * rescaleLinearIsometryEquiv 𝕜 c hc hμ g := by
  set T := rescaleLinearIsometryEquiv 𝕜 c hc hμ
  let E : Lp 𝕜 1 μ' ≃ₗᵢ[𝕜] Lp 𝕜 1 μ :=
    (linearIsometryEquiv 𝕜 𝕜 μ').symm.trans (T.trans (linearIsometryEquiv 𝕜 𝕜 μ))
  have hcomm := E.toContinuousLinearEquiv.integral_comp_comm
    (μ := μ') fun y => f.ofConv y • Lp.leftTranslation μ' 1 𝕜 y g.ofConv
  refine ext ?_
  have hlhs : (T (f * g)).ofConv =
      ∫ y, f.ofConv y • Lp.leftTranslation μ 1 𝕜 y (T g).ofConv ∂μ' := by
    calc (T (f * g)).ofConv
        = E (∫ y, f.ofConv y • Lp.leftTranslation μ' 1 𝕜 y g.ofConv ∂μ') := by
          rw [← toConv_ofConv (f * g), ofConv_mul, Lp.convolutionL_apply]
          rfl
      _ = ∫ y, E (f.ofConv y • Lp.leftTranslation μ' 1 𝕜 y g.ofConv) ∂μ' := by
          simpa using hcomm.symm
      _ = ∫ y, f.ofConv y • Lp.leftTranslation μ 1 𝕜 y (T g).ofConv ∂μ' := by
          refine integral_congr_ae (.of_forall fun y => ?_)
          dsimp only
          rw [map_smul]
          congr 1
          have htr := congr_arg ofConv (rescaleLinearIsometryEquiv_leftTranslation hc hμ y g)
          rw [← toConv_ofConv (leftTranslation 𝕜 μ' y g), ofConv_leftTranslation,
            ofConv_leftTranslation] at htr
          exact htr
  have hsmul_meas : ∫ y, f.ofConv y • Lp.leftTranslation μ 1 𝕜 y (T g).ofConv ∂μ' =
      ∫ y, f.ofConv y • Lp.leftTranslation μ 1 𝕜 y (T g).ofConv ∂((c : ℝ≥0∞) • μ) :=
    congr_arg (integral · fun y => f.ofConv y • Lp.leftTranslation μ 1 𝕜 y (T g).ofConv) hμ
  rw [hlhs, hsmul_meas, integral_smul_measure, ENNReal.coe_toReal, ← integral_smul,
    ofConv_mul, Lp.convolutionL_apply]
  refine integral_congr_ae ?_
  filter_upwards [ofConv_rescaleLinearIsometryEquiv_ae_eq hc hμ f] with y hy
  rw [hy, smul_assoc]

private theorem rescaleLinearIsometryEquiv_star [LocallyCompactSpace G] [μ'.IsHaarMeasure]
    [μ'.Regular] [μ.IsHaarMeasure] [μ.Regular] {c : ℝ≥0} (hc : c ≠ 0) (hμ : μ' = c • μ)
    (f : GroupAlgebraL1 𝕜 μ') :
    rescaleLinearIsometryEquiv 𝕜 c hc hμ (star f) =
      star (rescaleLinearIsometryEquiv 𝕜 c hc hμ f) := by
  refine ext_ae ?_
  filter_upwards [ofConv_rescaleLinearIsometryEquiv_ae_eq hc hμ (star f),
    ae_of_eq_smul hc hμ (ofConv_star_ae_eq f),
    ofConv_star_ae_eq (rescaleLinearIsometryEquiv 𝕜 c hc hμ f),
    (quasiMeasurePreserving_inv_of_regular μ).ae
      (ofConv_rescaleLinearIsometryEquiv_ae_eq hc hμ f)] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄, star_smul, star_trivial (_ : ℝ),
    smul_comm (c : ℝ) (modularCharacter x : ℝ)]

/-- Rescaling by `(c : ℝ)` yields an isometric `⋆`-algebra isomorphism
`GroupAlgebraL1 𝕜 (c • μ) ≃⋆ₐ[𝕜] GroupAlgebraL1 𝕜 μ` for any `c : ℝ≥0` (`c ≠ 0`) and regular left
Haar measure `μ`. -/
def smulMeasureStarAlgEquiv [LocallyCompactSpace G] (𝕜 : Type*) [RCLike 𝕜] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.Regular] (c : ℝ≥0) (hc : c ≠ 0) :
    haveI : (c • μ).IsHaarMeasure := IsHaarMeasure.nnreal_smul μ hc
    GroupAlgebraL1 𝕜 (c • μ) ≃⋆ₐ[𝕜] GroupAlgebraL1 𝕜 μ :=
  haveI : (c • μ).IsHaarMeasure := IsHaarMeasure.nnreal_smul μ hc
  { (rescaleLinearIsometryEquiv 𝕜 c hc rfl).toLinearEquiv with
    map_mul' := rescaleLinearIsometryEquiv_mul hc rfl
    map_star' := rescaleLinearIsometryEquiv_star hc rfl
    map_smul' r a := map_smul (rescaleLinearIsometryEquiv 𝕜 c hc rfl) r a }

end RescaleGroup

section RegularHaar

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (𝕜 : Type*) [RCLike 𝕜] (μ' μ : Measure G) [μ'.IsHaarMeasure] [μ'.Regular]
  [μ.IsHaarMeasure] [μ.Regular]

/-- **Canonical isometric linear equivalence between `L¹` group algebras for any two regular left
Haar measures `μ'` and `μ` on `G`**, defined by multiplying representatives by
`MeasureTheory.Measure.haarScalarFactor μ' μ`. No second-countability or `σ`-compactness hypothesis
is needed. -/
def haarLinearIsometryEquiv : GroupAlgebraL1 𝕜 μ' ≃ₗᵢ[𝕜] GroupAlgebraL1 𝕜 μ :=
  rescaleLinearIsometryEquiv 𝕜 (haarScalarFactor μ' μ)
    (haarScalarFactor_pos_of_isHaarMeasure μ' μ).ne' (isMulLeftInvariant_eq_smul_of_regular μ' μ)

/-- **Canonical `⋆`-algebra isomorphism between `L¹` group algebras for any two regular left Haar
measures `μ'` and `μ` on `G`**. Together with `norm_haarStarAlgEquiv`, this shows that the
isometric Banach `⋆`-algebra isomorphism type of `GroupAlgebraL1 𝕜 μ` is independent of the choice
of regular left Haar measure on `G`. -/
def haarStarAlgEquiv : GroupAlgebraL1 𝕜 μ' ≃⋆ₐ[𝕜] GroupAlgebraL1 𝕜 μ where
  __ := (haarLinearIsometryEquiv 𝕜 μ' μ).toLinearEquiv
  map_mul' := rescaleLinearIsometryEquiv_mul
    (haarScalarFactor_pos_of_isHaarMeasure μ' μ).ne' (isMulLeftInvariant_eq_smul_of_regular μ' μ)
  map_star' := rescaleLinearIsometryEquiv_star
    (haarScalarFactor_pos_of_isHaarMeasure μ' μ).ne' (isMulLeftInvariant_eq_smul_of_regular μ' μ)
  map_smul' r a := map_smul (haarLinearIsometryEquiv 𝕜 μ' μ) r a

theorem coe_haarStarAlgEquiv :
    ⇑(haarStarAlgEquiv 𝕜 μ' μ) = ⇑(haarLinearIsometryEquiv 𝕜 μ' μ) :=
  (rfl)

/-- `haarStarAlgEquiv 𝕜 μ' μ` is norm-preserving. -/
@[simp]
theorem norm_haarStarAlgEquiv (f : GroupAlgebraL1 𝕜 μ') :
    ‖haarStarAlgEquiv 𝕜 μ' μ f‖ = ‖f‖ :=
  (haarLinearIsometryEquiv 𝕜 μ' μ).norm_map f

/-- `haarStarAlgEquiv 𝕜 μ' μ` acts on representatives by multiplying by `haarScalarFactor μ' μ`. -/
theorem ofConv_haarStarAlgEquiv_ae_eq (f : GroupAlgebraL1 𝕜 μ') :
    (haarStarAlgEquiv 𝕜 μ' μ f).ofConv =ᵐ[μ]
      fun x => (haarScalarFactor μ' μ : ℝ) • f.ofConv x :=
  ofConv_rescaleLinearIsometryEquiv_ae_eq
    (haarScalarFactor_pos_of_isHaarMeasure μ' μ).ne' (isMulLeftInvariant_eq_smul_of_regular μ' μ) f

@[simp]
theorem haarStarAlgEquiv_self (f : GroupAlgebraL1 𝕜 μ) :
    haarStarAlgEquiv 𝕜 μ μ f = f := by
  refine ext_ae ?_
  filter_upwards [ofConv_haarStarAlgEquiv_ae_eq 𝕜 μ μ f] with x hx
  rw [hx, haarScalarFactor_self, NNReal.coe_one, one_smul]

/-- Functoriality of `haarStarAlgEquiv` across three regular left Haar measures. -/
@[simp]
theorem haarStarAlgEquiv_haarStarAlgEquiv (μ'' : Measure G) [μ''.IsHaarMeasure] [μ''.Regular]
    (f : GroupAlgebraL1 𝕜 μ'') :
    haarStarAlgEquiv 𝕜 μ' μ (haarStarAlgEquiv 𝕜 μ'' μ' f) = haarStarAlgEquiv 𝕜 μ'' μ f := by
  refine ext_ae ?_
  filter_upwards [ofConv_haarStarAlgEquiv_ae_eq 𝕜 μ' μ (haarStarAlgEquiv 𝕜 μ'' μ' f),
    ae_of_eq_smul (haarScalarFactor_pos_of_isHaarMeasure μ' μ).ne'
      (isMulLeftInvariant_eq_smul_of_regular μ' μ) (ofConv_haarStarAlgEquiv_ae_eq 𝕜 μ'' μ' f),
    ofConv_haarStarAlgEquiv_ae_eq 𝕜 μ'' μ f] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, smul_smul, ← NNReal.coe_mul, mul_comm, ← haarScalarFactor_eq_mul μ'' μ' μ]

@[simp]
theorem haarStarAlgEquiv_symm :
    (haarStarAlgEquiv 𝕜 μ' μ).symm = haarStarAlgEquiv 𝕜 μ μ' := by
  ext1 f
  rw [StarAlgEquiv.symm_apply_eq, haarStarAlgEquiv_haarStarAlgEquiv, haarStarAlgEquiv_self]

end RegularHaar

end HaarComparison

end GroupAlgebraL1

end TauCeti

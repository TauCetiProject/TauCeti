/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Function.Lp.Duality
public import TauCeti.MeasureTheory.Function.Lp.Linfty.Sigma
import TauCeti.MeasureTheory.Function.LpSeminorm.OperatorField
import TauCeti.MeasureTheory.Function.StronglyMeasurable.FiniteSupport

/-!
# The integral pairing between Bochner spaces

For Hölder conjugate exponents `1 ≤ p, q ≤ ∞` and a normed space `X` over a complete nontrivially
normed field `𝕜` with a compatible real structure, the integral pairing `⟨f, g⟩ = ∫ g s (f s) dμ`
of `f ∈ Lᵖ(μ; X)` with `g ∈ L^q(μ; X⋆)` gives the canonical contraction

`TauCeti.bochnerDualMap 𝕜 X μ p q : L^q(μ; X⋆) →L[𝕜] (Lᵖ(μ; X))⋆`.

It is Mathlib's bilinear `Lp` pairing `ContinuousLinearMap.lpPairing` of the evaluation map
`X⋆ × X → 𝕜`, with the arguments ordered so that `L^q(μ; X⋆)` acts on `Lᵖ(μ; X)`. The pairing is
bilinear, also over `ℂ`.

The main results compute norms through this pairing, for `𝕜 = ℝ` or `ℂ`.

* `TauCeti.norm_bochnerDualMap_of_ne_top` and `TauCeti.norm_bochnerDualMap`: the map is an
  isometry when `q < ∞`, on an arbitrary measure space, and for all conjugate exponents on a
  σ-finite measure space. In particular its range is closed.
* `TauCeti.norm_bochnerDualMap_linftySigma` and
  `TauCeti.isometry_bochnerDualMap_comp_subtypeL_linftySigma`: at `p = 1`, `q = ∞`, the map is
  isometric on an arbitrary measure space when restricted to the support-restricted space
  `TauCeti.linftySigma`.
* `TauCeti.norm_le_of_dual_pairing_bound_of_ne_top` and `TauCeti.norm_le_of_dual_pairing_bound`:
  conversely, the functions in `L^q(μ; X⋆)` norm `Lᵖ(μ; X)`, when `p < ∞` on an arbitrary measure
  space and for all conjugate exponents on a σ-finite measure space.
* `TauCeti.norm_le_of_dual_pairing_bound_linftySigma` and
  `TauCeti.norm_le_of_linftySigma_pairing_bound`: on an arbitrary measure space, `L¹(μ; X⋆)`
  norms `TauCeti.linftySigma 𝕜 X μ`, and `TauCeti.linftySigma 𝕜 X⋆ μ` norms `L¹(μ; X)`.
* `ContinuousLinearMap.bochnerDualMap_apply_compLp`: naturality of the pairing for bounded linear
  maps of the target and their adjoints `ContinuousLinearMap.precomp`.

## Implementation notes

The isometry theorems reduce to the scalar norming theorems for `Lᵖ(μ)` against simple test
functions, such as `MeasureTheory.MemLp.eLpNorm_le_of_forall_enorm_integral_mul_le`. The strongly
measurable almost norming vectors of
`MeasureTheory.AEStronglyMeasurable.exists_stronglyMeasurable_norming` turn `g` into the scalar
function `s ↦ g s (x s)`, whose `L^q` norm is almost that of `g` and is normed by the scalar
test functions `φ` through the vector test functions `φ • x`. The norming statements are the
isometry theorems for `X⋆` with the exponents exchanged, applied to the image of `f` in
`Lᵖ(μ; X⋆⋆)` under the isometric embedding into the bidual
(`TauCeti.bochnerDualMap_inclusionInDoubleDual_compLp_apply`). To test `f ∈ L¹(μ; X)` against
`TauCeti.linftySigma`, a test function in `L∞(μ; X⋆)` is cut down to a measurable set on which `μ`
is σ-finite and off which `f` vanishes.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*, Volume I,
  Proposition 1.3.1.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

section Pairing

variable {𝕜 S X : Type*} [NontriviallyNormedField 𝕜] [NormedSpace ℝ 𝕜] [SMulCommClass ℝ 𝕜 𝕜]
  [CompleteSpace 𝕜] [MeasurableSpace S] {μ : Measure S}
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [q.HolderConjugate p]

variable (𝕜 X μ p q) in
/-- The integral pairing `g ↦ (f ↦ ∫ g s (f s) dμ)` from `L^q(μ; X⋆)` to the continuous dual of
`Lᵖ(μ; X)`, for Hölder conjugate exponents `p` and `q`. This abbreviation of Mathlib's bilinear
pairing `ContinuousLinearMap.lpPairing` of the evaluation map only fixes the order of the
arguments. -/
noncomputable abbrev bochnerDualMap : Lp (StrongDual 𝕜 X) q μ →L[𝕜] StrongDual 𝕜 (Lp X p μ) :=
  (ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 X)).lpPairing μ q p

/-- The integral formula for the pairing of `g ∈ L^q(μ; X⋆)` with `f ∈ Lᵖ(μ; X)`. -/
@[simp]
theorem bochnerDualMap_apply (g : Lp (StrongDual 𝕜 X) q μ) (f : Lp X p μ) :
    bochnerDualMap 𝕜 X μ p q g f = ∫ s, g s (f s) ∂μ := by
  simp [ContinuousLinearMap.lpPairing_eq_integral]

/-- The integral pairing is a contraction: Hölder's inequality. -/
theorem norm_bochnerDualMap_apply_le (g : Lp (StrongDual 𝕜 X) q μ) :
    ‖bochnerDualMap 𝕜 X μ p q g‖ ≤ ‖g‖ :=
  ((bochnerDualMap 𝕜 X μ p q).le_opNorm g).trans <| mul_le_of_le_one_left (norm_nonneg g) <|
    (ContinuousLinearMap.norm_lpPairing_le _).trans ContinuousLinearMap.norm_id_le

/-- Pairing `g ∈ L^q(μ; X⋆)` with `f ∈ Lᵖ(μ; X)` is pairing the image of `f` in `Lᵖ(μ; X⋆⋆)`
under the embedding into the bidual with `g`. (The named arguments of `compLp` only help the
elaborator to unify the instances on the bidual.) -/
theorem bochnerDualMap_inclusionInDoubleDual_compLp_apply (f : Lp X p μ)
    (g : Lp (StrongDual 𝕜 X) q μ) :
    bochnerDualMap 𝕜 (StrongDual 𝕜 X) μ q p (ContinuousLinearMap.compLp (𝕜' := 𝕜)
        (F := StrongDual 𝕜 (StrongDual 𝕜 X)) (NormedSpace.inclusionInDoubleDual 𝕜 X) f) g =
      bochnerDualMap 𝕜 X μ p q g f := by
  simp only [bochnerDualMap_apply]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousLinearMap.coeFn_compLp (𝕜' := 𝕜) (F := StrongDual 𝕜 (StrongDual 𝕜 X))
    (NormedSpace.inclusionInDoubleDual 𝕜 X) f] with s hs
  rw [hs, NormedSpace.dual_def]

end Pairing

end TauCeti

namespace ContinuousLinearMap

open TauCeti

variable {𝕜 S X Y : Type*} [NontriviallyNormedField 𝕜] [NormedSpace ℝ 𝕜] [SMulCommClass ℝ 𝕜 𝕜]
  [CompleteSpace 𝕜] [MeasurableSpace S] {μ : Measure S}
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- **Naturality of the integral pairing.** For a bounded linear map `T : X →L[𝕜] Y`, pairing
`g ∈ L^q(μ; Y⋆)` with `T ∘ f` is pairing the pullback `s ↦ g s ∘L T` by the adjoint
`T.precomp 𝕜` with `f ∈ Lᵖ(μ; X)`. -/
theorem bochnerDualMap_apply_compLp (T : X →L[𝕜] Y) (g : Lp (StrongDual 𝕜 Y) q μ)
    (f : Lp X p μ) :
    bochnerDualMap 𝕜 Y μ p q g (T.compLp f) =
      bochnerDualMap 𝕜 X μ p q ((T.precomp 𝕜).compLp g) f := by
  simp only [bochnerDualMap_apply]
  refine integral_congr_ae ?_
  filter_upwards [T.coeFn_compLp f, (T.precomp 𝕜).coeFn_compLp g] with s hf hg
  simp [hf, hg]

end ContinuousLinearMap

namespace TauCeti

section Norm

variable {𝕜 S X : Type*} [RCLike 𝕜] [MeasurableSpace S] {μ : Measure S}
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [q.HolderConjugate p]

/-- The scalar norming principle for `h ∈ L^r(μ)` against simple test functions in the conjugate
`L^{r'}(μ)`, in the form supplied by
`MeasureTheory.MemLp.eLpNorm_le_of_forall_enorm_integral_mul_le` and its variants. -/
private def ScalarNorming (μ : Measure S) (r r' : ℝ≥0∞) (h : S → 𝕜) : Prop :=
  ∀ C : ℝ≥0∞, (∀ φ : SimpleFunc S 𝕜, MemLp φ r' μ → ‖∫ s, h s * φ s ∂μ‖ₑ ≤ C * eLpNorm φ r' μ) →
    eLpNorm h r μ ≤ C

/-- The core of the isometry theorems for `bochnerDualMap`: if the scalar norming principle for
`L^q(μ)` holds for scalar functions dominated by `‖g‖`, then the functional
`f ↦ ∫ g s (f s) dμ` has norm `‖g‖_q`. -/
private theorem norm_bochnerDualMap_of_scalarNorming (g : Lp (StrongDual 𝕜 X) q μ)
    (hnorm : ∀ h : S → 𝕜, MemLp h q μ → (∀ᵐ s ∂μ, ‖h s‖ ≤ ‖g s‖) → ScalarNorming μ q p h) :
    ‖bochnerDualMap 𝕜 X μ p q g‖ = ‖g‖ := by
  set Λ := bochnerDualMap 𝕜 X μ p q g
  refine le_antisymm (norm_bochnerDualMap_apply_le g) ?_
  rw [Lp.norm_def, ← toReal_eNorm Λ]
  refine ENNReal.toReal_mono eNorm_ne_top ?_
  -- Test `g` against strongly measurable fields `x` of vectors of norm at most one.
  refine (Lp.aestronglyMeasurable g).eLpNorm_le_of_forall_eLpNorm_apply_le fun x hx _ hx1 ↦ ?_
  have hle : ∀ s, ‖g s (x s)‖ ≤ ‖g s‖ := fun s ↦ (g s).unit_le_opNorm _ (hx1 s)
  have hh : MemLp (fun s ↦ g s (x s)) q μ :=
    (Lp.memLp g).of_le ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
      (Lp.aestronglyMeasurable g) hx.aestronglyMeasurable) (ae_of_all _ hle)
  refine hnorm _ hh (ae_of_all _ hle) _ fun φ hφ ↦ ?_
  -- The scalar test function `φ` pairs with `s ↦ g s (x s)` as `φ • x` pairs with `g`.
  have hφx : ∀ s, ‖φ s • x s‖ ≤ ‖φ s‖ := fun s ↦ by
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hx1 s)
  have hm : AEStronglyMeasurable (fun s ↦ φ s • x s) μ :=
    hφ.aestronglyMeasurable.smul hx.aestronglyMeasurable
  have hf : MemLp (fun s ↦ φ s • x s) p μ := hφ.of_le hm (ae_of_all _ hφx)
  calc ‖∫ s, g s (x s) * φ s ∂μ‖ₑ = ‖Λ (hf.toLp fun s ↦ φ s • x s)‖ₑ := by
        rw [bochnerDualMap_apply]
        congr 1
        refine integral_congr_ae (hf.coeFn_toLp.mono fun s hs ↦ ?_)
        simp [hs, mul_comm]
    _ ≤ ‖Λ‖ₑ * ‖hf.toLp fun s ↦ φ s • x s‖ₑ := Λ.le_opENorm _
    _ ≤ ‖Λ‖ₑ * eLpNorm φ p μ := by rw [Lp.eNorm_toLp hf]; gcongr; exact eLpNorm_mono hm hφx

/-- **The Bochner integral pairing is an isometry for `q < ∞`.** On an arbitrary measure space, for
Hölder conjugate exponents `p` and `q` with `q < ∞`, the functional `f ↦ ∫ g s (f s) dμ` on
`Lᵖ(μ; X)` has norm `‖g‖_q` for every `g ∈ L^q(μ; X⋆)`. -/
@[simp]
theorem norm_bochnerDualMap_of_ne_top (hq : q ≠ ∞) (g : Lp (StrongDual 𝕜 X) q μ) :
    ‖bochnerDualMap 𝕜 X μ p q g‖ = ‖g‖ :=
  norm_bochnerDualMap_of_scalarNorming g fun _ hh _ _ htest ↦
    hh.eLpNorm_le_of_forall_enorm_integral_mul_le_of_ne_top hq htest

/-- **The Bochner integral pairing is an isometry.** On a σ-finite measure space, for all Hölder
conjugate exponents `p` and `q`, the functional `f ↦ ∫ g s (f s) dμ` on `Lᵖ(μ; X)` has norm
`‖g‖_q` for every `g ∈ L^q(μ; X⋆)`. -/
@[simp]
theorem norm_bochnerDualMap [SigmaFinite μ] (g : Lp (StrongDual 𝕜 X) q μ) :
    ‖bochnerDualMap 𝕜 X μ p q g‖ = ‖g‖ :=
  norm_bochnerDualMap_of_scalarNorming g fun _ hh _ _ htest ↦
    hh.eLpNorm_le_of_forall_enorm_integral_mul_le htest

/-- **The integral pairing on the support-restricted infinity space.** On an arbitrary measure
space, the functional `f ↦ ∫ g s (f s) dμ` on `L¹(μ; X)` has norm `‖g‖_∞` for every `g` in the
support-restricted space `L∞_σ(μ; X⋆) = TauCeti.linftySigma 𝕜 X⋆ μ`. For the whole native space
`L∞(μ; X⋆)` this fails when `μ` has a measurable set of infinite measure with no measurable subset
of finite positive measure: every integrable function vanishes almost everywhere on it. -/
@[simp]
theorem norm_bochnerDualMap_linftySigma (g : linftySigma 𝕜 (StrongDual 𝕜 X) μ) :
    ‖bochnerDualMap 𝕜 X μ 1 ∞ (g : Lp (StrongDual 𝕜 X) ∞ μ)‖ = ‖g‖ := by
  -- `g` vanishes almost everywhere off a measurable set on which `μ` is σ-finite.
  obtain ⟨t, ht, hvan, hσ⟩ := (mem_linftySigma_iff.1 g.property).exists_set_sigmaFinite
  rw [← Submodule.norm_coe]
  refine norm_bochnerDualMap_of_scalarNorming _ fun h hh hle _ htest ↦ ?_
  have hm := hh.aestronglyMeasurable
  refine hm.eLpNorm_top_le_of_forall_enorm_integral_mul_le_of_restrict_compl_ae_eq_zero ht ?_ htest
  filter_upwards [ae_restrict_of_ae hle, hvan] with s h1 h2
  simpa [h2] using h1

/-- On an arbitrary measure space, the integral pairing is an isometry for `q < ∞`. -/
theorem isometry_bochnerDualMap_of_ne_top (hq : q ≠ ∞) :
    Isometry (bochnerDualMap 𝕜 X μ p q) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_bochnerDualMap_of_ne_top hq)

/-- On a σ-finite measure space, the integral pairing is an isometry. -/
theorem isometry_bochnerDualMap [SigmaFinite μ] : Isometry (bochnerDualMap 𝕜 X μ p q) :=
  AddMonoidHomClass.isometry_of_norm _ norm_bochnerDualMap

/-- On an arbitrary measure space, the integral pairing `L∞(μ; X⋆) → (L¹(μ; X))⋆` restricted to
the support-restricted space `TauCeti.linftySigma 𝕜 X⋆ μ` is an isometry. -/
theorem isometry_bochnerDualMap_comp_subtypeL_linftySigma :
    Isometry ((bochnerDualMap 𝕜 X μ 1 ∞).comp (linftySigma 𝕜 (StrongDual 𝕜 X) μ).subtypeL) :=
  AddMonoidHomClass.isometry_of_norm _ norm_bochnerDualMap_linftySigma

/-- On an arbitrary measure space, the integral pairing has closed range for `q < ∞`. -/
theorem isClosed_range_bochnerDualMap_of_ne_top (hq : q ≠ ∞) :
    IsClosed (Set.range (bochnerDualMap 𝕜 X μ p q)) :=
  (isometry_bochnerDualMap_of_ne_top hq).isClosedEmbedding.isClosed_range

/-- On a σ-finite measure space, the integral pairing has closed range. -/
theorem isClosed_range_bochnerDualMap [SigmaFinite μ] :
    IsClosed (Set.range (bochnerDualMap 𝕜 X μ p q)) :=
  isometry_bochnerDualMap.isClosedEmbedding.isClosed_range

/-- The core of the norming theorems: if the integral pairing for `X⋆` with the exponents
exchanged is isometric at the image of `f ∈ Lᵖ(μ; X)` in `Lᵖ(μ; X⋆⋆)`, then a bound on the
pairings of `f` with the `g ∈ L^q(μ; X⋆)` bounds `‖f‖_p`. -/
private theorem norm_le_of_dual_pairing_bound_of_norm_eq (f : Lp X p μ) {C : ℝ} (hC : 0 ≤ C)
    (hnorm : ‖bochnerDualMap 𝕜 (StrongDual 𝕜 X) μ q p (ContinuousLinearMap.compLp (𝕜' := 𝕜)
        (F := StrongDual 𝕜 (StrongDual 𝕜 X)) (NormedSpace.inclusionInDoubleDual 𝕜 X) f)‖ =
      ‖ContinuousLinearMap.compLp (𝕜' := 𝕜) (F := StrongDual 𝕜 (StrongDual 𝕜 X))
        (NormedSpace.inclusionInDoubleDual 𝕜 X) f‖)
    (hbound : ∀ g : Lp (StrongDual 𝕜 X) q μ, ‖bochnerDualMap 𝕜 X μ p q g f‖ ≤ C * ‖g‖) :
    ‖f‖ ≤ C := by
  have hJ : Isometry (NormedSpace.inclusionInDoubleDual 𝕜 X) :=
    AddMonoidHomClass.isometry_of_norm (NormedSpace.inclusionInDoubleDual 𝕜 X) fun x ↦ by
      -- `inclusionInDoubleDualLi` is `inclusionInDoubleDual` bundled as a linear isometry.
      change ‖NormedSpace.inclusionInDoubleDualLi 𝕜 x‖ = ‖x‖
      exact LinearIsometry.norm_map _ x
  rw [← ContinuousLinearMap.norm_compLp_of_isometry (𝕜' := 𝕜) (F := StrongDual 𝕜 (StrongDual 𝕜 X))
    (L := NormedSpace.inclusionInDoubleDual 𝕜 X) hJ, ← hnorm]
  exact ContinuousLinearMap.opNorm_le_bound _ hC fun g ↦ by
    simpa only [bochnerDualMap_inclusionInDoubleDual_compLp_apply] using hbound g

/-- **`L^q(μ; X⋆)` norms `Lᵖ(μ; X)` for `p < ∞`.** On an arbitrary measure space, for Hölder
conjugate exponents `p` and `q` with `p < ∞` and a constant `C ≥ 0`, if
`‖∫ g s (f s) dμ‖ ≤ C ‖g‖_q` for every `g ∈ L^q(μ; X⋆)`, then `‖f‖_p ≤ C`. -/
theorem norm_le_of_dual_pairing_bound_of_ne_top (hp : p ≠ ∞) (f : Lp X p μ) {C : ℝ}
    (hC : 0 ≤ C)
    (hbound : ∀ g : Lp (StrongDual 𝕜 X) q μ, ‖bochnerDualMap 𝕜 X μ p q g f‖ ≤ C * ‖g‖) :
    ‖f‖ ≤ C :=
  norm_le_of_dual_pairing_bound_of_norm_eq f hC (norm_bochnerDualMap_of_ne_top hp _) hbound

/-- **`L^q(μ; X⋆)` norms `Lᵖ(μ; X)`.** On a σ-finite measure space, for all Hölder conjugate
exponents `p` and `q` and a constant `C ≥ 0`, if `‖∫ g s (f s) dμ‖ ≤ C ‖g‖_q` for every
`g ∈ L^q(μ; X⋆)`, then `‖f‖_p ≤ C`. -/
theorem norm_le_of_dual_pairing_bound [SigmaFinite μ] (f : Lp X p μ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ g : Lp (StrongDual 𝕜 X) q μ, ‖bochnerDualMap 𝕜 X μ p q g f‖ ≤ C * ‖g‖) :
    ‖f‖ ≤ C :=
  norm_le_of_dual_pairing_bound_of_norm_eq f hC (norm_bochnerDualMap _) hbound

/-- **`L¹(μ; X⋆)` norms the support-restricted infinity space.** On an arbitrary measure space,
for `f` in `L∞_σ(μ; X) = TauCeti.linftySigma 𝕜 X μ` and a constant `C ≥ 0`, if
`‖∫ g s (f s) dμ‖ ≤ C ‖g‖₁` for every `g ∈ L¹(μ; X⋆)`, then `‖f‖_∞ ≤ C`. -/
theorem norm_le_of_dual_pairing_bound_linftySigma (f : linftySigma 𝕜 X μ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ g : Lp (StrongDual 𝕜 X) 1 μ,
      ‖bochnerDualMap 𝕜 X μ ∞ 1 g (f : Lp X ∞ μ)‖ ≤ C * ‖g‖) :
    ‖f‖ ≤ C := by
  rw [← Submodule.norm_coe]
  exact norm_le_of_dual_pairing_bound_of_norm_eq _ hC
    (norm_bochnerDualMap_linftySigma ⟨_, ContinuousLinearMap.compLp_mem_linftySigma _ f.property⟩)
    hbound

/-- **The support-restricted infinity space norms `L¹(μ; X)`.** On an arbitrary measure space,
for `f ∈ L¹(μ; X)` and a constant `C ≥ 0`, if `‖∫ g s (f s) dμ‖ ≤ C ‖g‖_∞` for every `g` in
`L∞_σ(μ; X⋆) = TauCeti.linftySigma 𝕜 X⋆ μ`, then `‖f‖₁ ≤ C`. -/
theorem norm_le_of_linftySigma_pairing_bound (f : Lp X 1 μ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ g : linftySigma 𝕜 (StrongDual 𝕜 X) μ,
      ‖bochnerDualMap 𝕜 X μ 1 ∞ (g : Lp (StrongDual 𝕜 X) ∞ μ) f‖ ≤ C * ‖g‖) :
    ‖f‖ ≤ C := by
  -- `f` vanishes almost everywhere off a measurable set `t` on which `μ` is σ-finite, so a test
  -- function `g ∈ L∞(μ; X⋆)` pairs with `f` as its restriction `1_t g ∈ L∞_σ(μ; X⋆)` does.
  obtain ⟨t, ht, hvan, hσ⟩ :=
    ((Lp.memLp f).aefinStronglyMeasurable one_ne_zero ENNReal.one_ne_top).exists_set_sigmaFinite
  refine norm_le_of_dual_pairing_bound_of_ne_top (𝕜 := 𝕜) (q := ∞) ENNReal.one_ne_top f hC
    fun g ↦ ?_
  have hgt : MemLp (t.indicator g) ∞ μ := (Lp.memLp g).indicator ht.nullMeasurableSet
  have hmem : hgt.toLp _ ∈ linftySigma 𝕜 (StrongDual 𝕜 X) μ := by
    rw [mem_linftySigma_iff_of_ae_eq hgt.coeFn_toLp,
      aefinStronglyMeasurable_iff_aestronglyMeasurable_and_exists_set_sigmaFinite]
    exact ⟨hgt.aestronglyMeasurable, t, ht,
      ae_restrict_of_forall_mem ht.compl fun s hs ↦ Set.indicator_of_notMem hs _, hσ⟩
  calc ‖bochnerDualMap 𝕜 X μ 1 ∞ g f‖
      = ‖bochnerDualMap 𝕜 X μ 1 ∞ ((⟨_, hmem⟩ : linftySigma 𝕜 (StrongDual 𝕜 X) μ) :
          Lp (StrongDual 𝕜 X) ∞ μ) f‖ := by
        simp only [bochnerDualMap_apply]
        congr 1
        refine integral_congr_ae ?_
        filter_upwards [hgt.coeFn_toLp, ae_restrict_iff' ht.compl |>.1 hvan] with s hs hfs
        by_cases hst : s ∈ t
        · simp [hs, hst]
        · simp [hs, hst, hfs hst]
    _ ≤ C * ‖hgt.toLp _‖ := hbound _
    _ ≤ C * ‖g‖ := by
        gcongr
        rw [Lp.norm_toLp, Lp.norm_def]
        exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top g)
          (eLpNorm_indicator_le _ ht.nullMeasurableSet)

end Norm

end TauCeti

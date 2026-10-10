/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-!
# The `star`-fixed part of a complex `Lᵖ` space is the real `Lᵖ` space

Mathlib gives `Lp K p μ` a bare `Star` and an `InvolutiveStar` and nothing else: there is no
`StarAddMonoid (Lp K p μ)`, so `selfAdjoint (Lp K p μ)` is not even a legal expression, and no
comparison between `Lp ℝ p μ` and `Lp K p μ` exists at any level.  This module supplies the
comparison.

The content is that a `star`-fixed class is almost everywhere real, so it is the image of a real
class under pointwise `RCLike.ofReal`; the embedding is `ℝ`-linear and norm preserving because
`‖(r : K)‖ = |r|`.  The `ℝ` is not an artefact of the proof -- the `star`-fixed set is closed
under real scalars and *not* under `K`-scalars (multiply by `I`), so `ℝ`-linear is the strongest
statement available.

## The `star`-as-`compLp` trick

The awkward part is that `Lp` has no `StarAddMonoid`, so `star (F + G) = star F + star G` is not
available and cannot be quoted.  Rather than reprove each algebraic law from representatives,
`star_eq_compLp` identifies `star` on `Lp K p μ` with `ContinuousLinearMap.compLp` of the
`ℝ`-linear map `RCLike.conjCLE`.  Every additivity and real-homogeneity law then comes from
Mathlib's `ContinuousLinearMap.add_compLp` and `ContinuousLinearMap.smul_compLp` for free, and
`starFixedSubmodule` can be built without a single further `Lp.ext`.

## Main results

* `TauCeti.ae_ofReal_re_eq_of_star_eq_self` and `TauCeti.star_eq_self_of_ae_ofReal_re_eq`:
  **C1**, the two directions of the a.e.-real characterisation.
* `TauCeti.star_eq_self_iff_ae_ofReal_re_eq` and `TauCeti.star_eq_self_iff_ae_im_eq_zero`: the
  biconditional, in the `ofReal ∘ re` and the `im = 0` phrasings.
* `TauCeti.ofRealLp` and `TauCeti.reLp`: **C2**, the two directions as maps, with
  `TauCeti.reLp_ofRealLp` and `TauCeti.ofRealLp_reLp_of_star_eq_self` inverse to each other.
* `TauCeti.ofRealLpₗᵢ`: **C3**, the embedding as an `ℝ`-linear isometry, with
  `TauCeti.range_ofRealLpₗᵢ` computing its range as `TauCeti.starFixedSubmodule`.
* `TauCeti.starFixedLpEquivRealLp`: the deliverable, `{F : Lp K p μ // star F = F} ≃ₗᵢ[ℝ]
  Lp ℝ p μ`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib.
-/

public section

open MeasureTheory

open scoped ENNReal ComplexConjugate

namespace TauCeti

variable {K : Type*} [RCLike K] {p : ℝ≥0∞} {α : Type*} [MeasurableSpace α] {μ : Measure α}

section StarFixed

/-- **A `star`-fixed `Lᵖ` class is almost everywhere real**, in the form that recovers the
class from its real part.  This is the direction that does the work: it is what lets a real
representative be chosen. -/
theorem ae_ofReal_re_eq_of_star_eq_self {F : Lp K p μ} (hF : star F = F) :
    ∀ᵐ x ∂μ, ((RCLike.re ((F : α → K) x) : ℝ) : K) = (F : α → K) x := by
  have h := Lp.coeFn_star F
  rw [hF] at h
  filter_upwards [h] with x hx
  have hconj : conj ((F : α → K) x) = (F : α → K) x := by
    simpa [Pi.star_apply, RCLike.star_def] using hx.symm
  exact RCLike.conj_eq_iff_re.mp hconj

/-- The converse of `ae_ofReal_re_eq_of_star_eq_self`: an almost everywhere real class is
`star`-fixed. -/
theorem star_eq_self_of_ae_ofReal_re_eq {F : Lp K p μ}
    (h : ∀ᵐ x ∂μ, ((RCLike.re ((F : α → K) x) : ℝ) : K) = (F : α → K) x) :
    star F = F := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star F, h] with x hx hre
  rw [hx]
  simpa [Pi.star_apply, RCLike.star_def] using RCLike.conj_eq_iff_re.mpr hre

/-- **C1: `star F = F` exactly when `F` has an almost everywhere real representative.** -/
theorem star_eq_self_iff_ae_ofReal_re_eq {F : Lp K p μ} :
    star F = F ↔ ∀ᵐ x ∂μ, ((RCLike.re ((F : α → K) x) : ℝ) : K) = (F : α → K) x :=
  ⟨ae_ofReal_re_eq_of_star_eq_self, star_eq_self_of_ae_ofReal_re_eq⟩

/-- The `im = 0` phrasing of `star_eq_self_iff_ae_ofReal_re_eq`.  Kept separate because the
two phrasings are convenient at different call sites: this one is the cheap test, the other
carries the real representative. -/
theorem star_eq_self_iff_ae_im_eq_zero {F : Lp K p μ} :
    star F = F ↔ ∀ᵐ x ∂μ, RCLike.im ((F : α → K) x) = 0 := by
  rw [star_eq_self_iff_ae_ofReal_re_eq]
  constructor
  · intro h
    filter_upwards [h] with x hx
    exact RCLike.conj_eq_iff_im.mp (RCLike.conj_eq_iff_re.mpr hx)
  · intro h
    filter_upwards [h] with x hx
    exact RCLike.conj_eq_iff_re.mp (RCLike.conj_eq_iff_im.mpr hx)

end StarFixed

section LpStar

/-- **`star` on `Lp K p μ` is `compLp` of the `ℝ`-linear conjugation of `K`.**

Mathlib gives `Lp` a bare `Star` and an `InvolutiveStar` and no `StarAddMonoid`, so none of the
algebraic laws for `star` are available and each would otherwise be proved from
representatives.  Identifying `star` with a `compLp` imports all of them at once from
`ContinuousLinearMap.compLpₗ`, which Mathlib has already proved linear. -/
theorem star_eq_compLp (F : Lp K p μ) :
    star F = ((RCLike.conjCLE (K := K)).toContinuousLinearMap).compLp F := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star F,
    ((RCLike.conjCLE (K := K)).toContinuousLinearMap).coeFn_compLp F] with x h1 h2
  rw [h1, h2]
  simp [Pi.star_apply, RCLike.star_def]

/-- Pointwise conjugation on `Lᵖ` is additive.  Not available from Mathlib, which puts no
`StarAddMonoid` on `Lp`; see `star_eq_compLp`. -/
theorem star_add_lp (F G : Lp K p μ) : star (F + G) = star F + star G := by
  simp only [star_eq_compLp]
  exact map_add (((RCLike.conjCLE (K := K)).toContinuousLinearMap).compLpₗ p μ) F G

/-- Pointwise conjugation on `Lᵖ` kills zero. -/
theorem star_zero_lp : star (0 : Lp K p μ) = 0 := by
  simp only [star_eq_compLp]
  exact map_zero (((RCLike.conjCLE (K := K)).toContinuousLinearMap).compLpₗ p μ)

/-- Pointwise conjugation on `Lᵖ` is homogeneous for **real** scalars.  It is not homogeneous
for `K`-scalars -- that is exactly why the `star`-fixed part below is an `ℝ`-submodule and not
a `K`-submodule. -/
theorem star_real_smul_lp (r : ℝ) (F : Lp K p μ) : star (r • F) = r • star F := by
  simp only [star_eq_compLp]
  exact map_smul (((RCLike.conjCLE (K := K)).toContinuousLinearMap).compLpₗ p μ) r F

end LpStar

section Maps

/-- **The real class attached to a complex one**: pointwise real part. -/
noncomputable def reLp (F : Lp K p μ) : Lp ℝ p μ :=
  (RCLike.reCLM : K →L[ℝ] ℝ).compLp F

/-- **The complex class attached to a real one**: pointwise `RCLike.ofReal`. -/
noncomputable def ofRealLp (f : Lp ℝ p μ) : Lp K p μ :=
  (RCLike.ofRealCLM : ℝ →L[ℝ] K).compLp f

/-- `reLp` is represented by the pointwise real part. -/
theorem coeFn_reLp (F : Lp K p μ) :
    ∀ᵐ x ∂μ, ((reLp F : Lp ℝ p μ) : α → ℝ) x = RCLike.re ((F : α → K) x) :=
  (RCLike.reCLM : K →L[ℝ] ℝ).coeFn_compLp F

/-- `ofRealLp` is represented by the pointwise coercion `ℝ → K`. -/
theorem coeFn_ofRealLp (f : Lp ℝ p μ) :
    ∀ᵐ x ∂μ, ((ofRealLp f : Lp K p μ) : α → K) x = (((f : α → ℝ) x : ℝ) : K) :=
  (RCLike.ofRealCLM : ℝ →L[ℝ] K).coeFn_compLp f

/-- `ofRealLp` is additive.  Stated unbundled, because consumers that also mention the
`ℝ`-module structure `Lp K p μ` inherits from `InnerProductSpace K` cannot use the bundled
`ofRealLpₗᵢ` without the two `Module ℝ` instances having to match syntactically. -/
theorem ofRealLp_add (f g : Lp ℝ p μ) :
    (ofRealLp (f + g) : Lp K p μ) = ofRealLp f + ofRealLp g :=
  map_add ((RCLike.ofRealCLM : ℝ →L[ℝ] K).compLpₗ p μ) f g

/-- `ofRealLp` is homogeneous for real scalars; stated unbundled for the same reason as
`ofRealLp_add`. -/
theorem ofRealLp_real_smul (r : ℝ) (f : Lp ℝ p μ) :
    (ofRealLp (r • f) : Lp K p μ) = r • ofRealLp f :=
  map_smul ((RCLike.ofRealCLM : ℝ →L[ℝ] K).compLpₗ p μ) r f

/-- `ofRealLp` carries a real scalar to the **coerced** scalar acting through the `K`-module
structure.  This is the form a descent argument wants: a complex space carries two `Module ℝ`
structures, and mentioning only the `K`-action is unambiguous.  Proved pointwise rather than by
transporting `ofRealLp_real_smul`, for exactly that reason. -/
theorem ofRealLp_coe_smul (r : ℝ) (f : Lp ℝ p μ) :
    (ofRealLp (r • f) : Lp K p μ) = (r : K) • ofRealLp f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_ofRealLp (K := K) (r • f), Lp.coeFn_smul r f,
    Lp.coeFn_smul (r : K) (ofRealLp f : Lp K p μ), coeFn_ofRealLp (K := K) f] with x h1 h2 h3 h4
  rw [h1, h3, h2]
  simp [Pi.smul_apply, h4, RCLike.ofReal_mul]

/-- **The image of `ofRealLp` is `star`-fixed.** -/
theorem star_ofRealLp (f : Lp ℝ p μ) : star (ofRealLp f : Lp K p μ) = ofRealLp f := by
  refine star_eq_self_of_ae_ofReal_re_eq ?_
  filter_upwards [coeFn_ofRealLp (K := K) f] with x hx
  rw [hx, RCLike.ofReal_re]

/-- **`reLp` is a left inverse of `ofRealLp`**, with no hypothesis: the real part of a real
class is itself. -/
theorem reLp_ofRealLp (f : Lp ℝ p μ) : reLp (ofRealLp f : Lp K p μ) = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_reLp (ofRealLp f : Lp K p μ), coeFn_ofRealLp (K := K) f] with x h1 h2
  rw [h1, h2, RCLike.ofReal_re]

/-- **`reLp` is a right inverse of `ofRealLp` on the `star`-fixed classes**, and only there:
this is the direction that consumes `C1`. -/
theorem ofRealLp_reLp_of_star_eq_self {F : Lp K p μ} (hF : star F = F) :
    (ofRealLp (reLp F) : Lp K p μ) = F := by
  refine Lp.ext ?_
  filter_upwards [coeFn_ofRealLp (K := K) (reLp F), coeFn_reLp F,
    ae_ofReal_re_eq_of_star_eq_self hF] with x h1 h2 h3
  rw [h1, h2]
  exact h3

/-- **`ofRealLp` preserves the norm**, because `‖(r : K)‖ = |r|` pointwise.  This is where the
statement stops being formal: no `compLp` of a general continuous linear map is isometric, and
Mathlib supplies only the bound `‖L.compLp f‖ ≤ ‖L‖ * ‖f‖`. -/
theorem norm_ofRealLp (f : Lp ℝ p μ) : ‖(ofRealLp f : Lp K p μ)‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable (ofRealLp f : Lp K p μ))
    (Lp.aestronglyMeasurable f) ?_
  filter_upwards [coeFn_ofRealLp (K := K) f] with x hx
  rw [hx, RCLike.norm_ofReal, Real.norm_eq_abs]

end Maps

section Equiv

variable (K p μ) [Fact (1 ≤ p)]

/-- **The `star`-fixed classes of `Lp K p μ`, as an `ℝ`-submodule.**

`ℝ` and not `K`: the carrier is not closed under multiplication by `RCLike.I`, so no
`K`-submodule structure exists on it.  Mathlib cannot state this as `selfAdjoint (Lp K p μ)`,
which needs a `StarAddMonoid (Lp K p μ)` instance that does not exist; the carrier here is the
literal set `{F | star F = F}`, so `↥(starFixedSubmodule K p μ)` *is* the subtype
`{F : Lp K p μ // star F = F}`. -/
def starFixedSubmodule : Submodule ℝ (Lp K p μ) where
  carrier := {F | star F = F}
  zero_mem' := star_zero_lp
  add_mem' {F G} hF hG := by
    have hF' : star F = F := hF
    have hG' : star G = G := hG
    change star (F + G) = F + G
    rw [star_add_lp, hF', hG']
  smul_mem' r F hF := by
    have hF' : star F = F := hF
    change star (r • F) = r • F
    rw [star_real_smul_lp, hF']

variable {K p μ}

omit [Fact (1 ≤ p)] in
/-- Membership in `starFixedSubmodule` is `star F = F` on the nose; the carrier was chosen so
that this is `Iff.rfl` and consumers never see the submodule packaging. -/
@[simp]
theorem mem_starFixedSubmodule {F : Lp K p μ} :
    F ∈ starFixedSubmodule K p μ ↔ star F = F := Iff.rfl

variable (K p μ)

/-- **C3: pointwise `RCLike.ofReal` as an `ℝ`-linear isometry `Lp ℝ p μ →ₗᵢ[ℝ] Lp K p μ`.**

The linear map is Mathlib's `ContinuousLinearMap.compLpₗ`; what is added is `norm_ofRealLp`,
since Mathlib has no isometric form of `compLp`. -/
noncomputable def ofRealLpₗᵢ : Lp ℝ p μ →ₗᵢ[ℝ] Lp K p μ where
  toLinearMap := (RCLike.ofRealCLM : ℝ →L[ℝ] K).compLpₗ p μ
  norm_map' f := norm_ofRealLp (K := K) f

/-- The bundled embedding acts as `ofRealLp`.  Written out rather than generated by `@[simps]`:
with the body unexposed `simps` cannot see the projection, and this is the lemma it would have
produced. -/
@[simp]
theorem ofRealLpₗᵢ_apply (f : Lp ℝ p μ) : ofRealLpₗᵢ K p μ f = (ofRealLp f : Lp K p μ) := (rfl)

/-- **The range of the real embedding is exactly the `star`-fixed part.**  Both inclusions are
`C2`: `star_ofRealLp` one way, `ofRealLp_reLp_of_star_eq_self` the other. -/
theorem range_ofRealLpₗᵢ :
    LinearMap.range (ofRealLpₗᵢ K p μ).toLinearMap = starFixedSubmodule K p μ := by
  apply le_antisymm
  · rintro F ⟨f, rfl⟩
    exact star_ofRealLp (K := K) f
  · intro F hF
    exact ⟨reLp F, ofRealLp_reLp_of_star_eq_self hF⟩

/-- **The deliverable.**  The `star`-fixed part of a complex `Lᵖ` space is the real `Lᵖ` space,
`ℝ`-linearly and isometrically.  Mathlib has no comparison of `Lp ℝ p μ` with `Lp K p μ` at any
level, so every piece of this is new.

The map is the pointwise real part; its inverse is the pointwise coercion `ℝ → K`.  Note that
`↥(starFixedSubmodule K p μ)` is by construction the subtype `{F : Lp K p μ // star F = F}`. -/
noncomputable def starFixedLpEquivRealLp :
    starFixedSubmodule K p μ ≃ₗᵢ[ℝ] Lp ℝ p μ where
  toFun F := reLp (F : Lp K p μ)
  map_add' F G := by
    change reLp ((F : Lp K p μ) + (G : Lp K p μ)) = _
    exact map_add ((RCLike.reCLM : K →L[ℝ] ℝ).compLpₗ p μ) _ _
  map_smul' r F := by
    change reLp (r • (F : Lp K p μ)) = _
    exact map_smul ((RCLike.reCLM : K →L[ℝ] ℝ).compLpₗ p μ) r _
  invFun f := ⟨ofRealLp f, star_ofRealLp f⟩
  left_inv F := Subtype.ext (ofRealLp_reLp_of_star_eq_self F.2)
  right_inv f := reLp_ofRealLp f
  norm_map' F := by
    have h := norm_ofRealLp (K := K) (reLp (F : Lp K p μ))
    rw [ofRealLp_reLp_of_star_eq_self F.2] at h
    exact h.symm

/-- The equivalence acts as the pointwise real part, for the same reason `ofRealLpₗᵢ_apply` is
written out. -/
@[simp]
theorem starFixedLpEquivRealLp_apply (F : starFixedSubmodule K p μ) :
    starFixedLpEquivRealLp K p μ F = reLp (F : Lp K p μ) := (rfl)

/-- The inverse of the equivalence acts as the pointwise coercion `ℝ → K`.  This is the form
consumers need: it says the real class `f` sits inside `Lp K p μ` as `ofRealLp f` and nothing
else. -/
@[simp]
theorem starFixedLpEquivRealLp_symm_apply (f : Lp ℝ p μ) :
    ((starFixedLpEquivRealLp K p μ).symm f : Lp K p μ) = ofRealLp f := (rfl)

end Equiv

end TauCeti

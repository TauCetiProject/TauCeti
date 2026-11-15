/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.CategoryTheory.Sites.SheafCohomology.LongExactSequence
public import TauCeti.Geometry.Manifold.Sheaf.Smooth.Fine
public import TauCeti.Topology.Sheaves.LocallyConstant.AddCommGrp
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Sheaves.LocallySurjective
import TauCeti.Geometry.Manifold.Instances.Sphere
import TauCeti.Geometry.Manifold.MFDeriv.Constancy

/-!
# The smooth exponential short exact sequence of sheaves

For a charted space `M` modelled on a real normed space `E` with corners `I`, the character
`Real.fourierChar : ℝ → Circle`, `t ↦ exp(2πi t)`, induces a short exact sequence of sheaves of
abelian groups on `M`,
`0 ⟶ ℤ_M ⟶ C^∞_M(ℝ) ⟶ C^∞_M(S¹) ⟶ 0`,
packaged as `TauCeti.smoothExponentialShortComplex I M` together with its proof of short exactness
`TauCeti.smoothExponentialShortComplex_shortExact`:

* `TauCeti.locallyConstantToSmoothAddCommGroupHom` embeds locally constant `A`-valued functions into
  smooth `B`-valued functions along any additive homomorphism `φ : A →+ B`; specializing to
  `Int.castAddHom ℝ` gives `TauCeti.locallyConstantIntToSmoothHom`.
* `TauCeti.smoothCircleExpHom` composes smooth real-valued functions on the left with
  `Real.fourierChar.toAddMonoidHom : ℝ →+ Additive Circle`.
* Over every open `W`, the kernel of `smoothCircleExpHom` is the image of
  `locallyConstantIntToSmoothHom`
  (`TauCeti.exact_locallyConstantIntToSmoothHom_smoothCircleExpHom`), and `smoothCircleExpHom` is
  locally surjective (`TauCeti.epi_smoothCircleExpHom`) by smooth local branches of `Complex.arg`
  on translates of `Complex.slitPlane`.

When `M` is a Hausdorff `σ`-compact (in particular, Hausdorff second-countable) `C^∞` manifold
modelled on a finite-dimensional real normed space, `C^∞_M(ℝ)` is fine
(`TauCeti.isFine_smoothSheafAddCommGroup`), so its positive-degree sheaf cohomology vanishes and the
long exact cohomology sequence yields:

* surjectivity of the degree-zero connecting map `H⁰(M, C^∞_M(S¹)) →+ H¹(M, ℤ_M)`
  (`TauCeti.smoothExponential_δ_zero_surjective`), with kernel equal to the image of
  `H⁰(M, C^∞_M(ℝ))` (`TauCeti.exact_map_smoothCircleExpHom_δ_zero`);
* canonical additive equivalences `H^q(M, C^∞_M(S¹)) ≃+ H^{q + 1}(M, ℤ_M)` for all `q > 0`
  (`TauCeti.smoothExponentialConnectingAddEquiv`);
* on any open subset `U` of a Hausdorff second-countable manifold `M`, smooth `S¹`-valued functions
  on `U` lift to smooth real-valued functions if and only if `H¹(U, ℤ_M)` vanishes
  (`TauCeti.smoothCircleExpHom_app_surjective_iff_subsingleton_H'_one`).

## Main definitions and results

* `Real.fourierChar_eq_one_iff`, `Real.contMDiff_fourierChar`,
  `Real.contMDiff_fourierChar_toAddMonoidHom`: kernel and `C^m` regularity of `Real.fourierChar`.
* `TauCeti.locallyConstantToSmoothAddCommGroupHom`, `TauCeti.locallyConstantIntToSmoothHom`:
  sheaf morphisms from locally constant functions to smooth functions.
* `TauCeti.smoothCircleExpHom`, `TauCeti.smoothCircleExpMulHom`: additive and multiplicative
  smooth exponential sheaf morphisms.
* `TauCeti.smoothExponentialShortComplex`, `TauCeti.smoothExponentialShortComplex_shortExact`:
  the short exact sequence `0 ⟶ ℤ_M ⟶ C^∞_M(ℝ) ⟶ C^∞_M(S¹) ⟶ 0`.
* `TauCeti.smoothExponential_δ_zero_surjective`,
  `TauCeti.smoothExponentialConnectingAddEquiv`,
  `TauCeti.smoothCircleExpHom_app_surjective_iff_subsingleton_H'_one`: cohomological consequences.

## References

* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., World Scientific, 2021,
  §7.5.4, Example 7.5.31, p. 327, and §8.2, Remark 8.2.2, p. 363.
* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer, 1983, Chapter 5.
* The smooth sheaves are those of `Mathlib/Geometry/Manifold/Sheaf/Smooth.lean`, by Heather Macbeth
  and Adam Topaz.
-/

public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open scoped ContDiff Manifold

/-! ### Smoothness and kernel of the unit-period circle exponential -/

/-- `Real.fourierChar t = exp(2πi t)` equals `1` if and only if `t` is an integer. -/
theorem Real.fourierChar_eq_one_iff {t : ℝ} : Real.fourierChar t = 1 ↔ ∃ n : ℤ, t = n := by
  rw [Real.fourierChar_apply', Circle.exp_eq_one]
  have h2pi : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  exact exists_congr fun n ↦
    ⟨fun h ↦ mul_right_cancel₀ h2pi ((mul_comm t _).trans h), fun h ↦ by rw [h, mul_comm]⟩

/-- The character `Real.fourierChar : ℝ → Circle` is `C^m` for every `m : ℕ∞ω`. -/
theorem Real.contMDiff_fourierChar {m : ℕ∞ω} : CMDiff m Real.fourierChar :=
  contMDiff_circleExp.comp (contMDiff_const.mul contMDiff_id)

/-- Viewed as an additive homomorphism `ℝ →+ Additive Circle`, `Real.fourierChar` is `C^m`. -/
theorem Real.contMDiff_fourierChar_toAddMonoidHom {m : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) m Real.fourierChar.toAddMonoidHom := by
  rw [AddChar.coe_toAddMonoidHom, Additive.contMDiff_ofMul_comp_iff]
  exact Real.contMDiff_fourierChar

/-- Viewed as a multiplicative homomorphism `Multiplicative ℝ →* Circle`, `Real.fourierChar` is
`C^m`. -/
theorem Real.contMDiff_fourierChar_toMonoidHom {m : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) m (AddChar.toMonoidHomEquiv Real.fourierChar) := by
  rw [AddChar.coe_toMonoidHomEquiv]
  exact Real.contMDiff_fourierChar.comp Multiplicative.contMDiff_toAdd

namespace TauCeti

/-! ### Embedding locally constant sections into smooth sections -/

section LocallyConstantToSmooth

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  (M : Type u) [TopologicalSpace M] [ChartedSpace HM M]
  {A B : Type u} [AddCommGroup A] [AddCommGroup B]
  [TopologicalSpace B] [ChartedSpace H B] [LieAddGroup I ∞ B]

private def locallyConstantToSmoothSectionHom (φ : A →+ B) (W : Opens (TopCat.of M)) :
    LocallyConstant W A →+ C^∞⟮IM, W; I, B⟯ where
  toFun g := ⟨φ ∘ g, (g.isLocallyConstant.comp φ).contMDiff⟩
  map_zero' := ContMDiffMap.ext fun _ ↦ map_zero φ
  map_add' g₁ g₂ := ContMDiffMap.ext fun x ↦ map_add φ (g₁ x) (g₂ x)

/-- Any additive homomorphism `φ : A →+ B` into an additive Lie group `B` sends locally constant
`A`-valued sections to smooth `B`-valued sections, giving a morphism of sheaves of abelian
groups. -/
def locallyConstantToSmoothAddCommGroupHom (φ : A →+ B) :
    TopCat.locallyConstantAddCommGrpSheaf (TopCat.of M) A ⟶
      smoothSheafAddCommGroup IM I M B :=
  ObjectProperty.homMk
    { app := fun W ↦ AddCommGrpCat.ofHom (locallyConstantToSmoothSectionHom IM I M φ W.unop)
      naturality := fun {_ _} _ ↦ by ext g; exact ContMDiffMap.ext fun _ ↦ rfl }

-- Stored simp keys keep the carrier of `TopCat.of M` unreduced, so keep the section and point
-- arguments out of the index.
@[simp]
theorem locallyConstantToSmoothAddCommGroupHom_hom_app_apply (φ : A →+ B)
    (W : Opens (TopCat.of M)) (g : LocallyConstant W A) (x : W) :
    @DFunLike.coe (no_index C^∞⟮IM, W; I, B⟯) (no_index ↥W) (fun _ ↦ B) _
        (no_index ((locallyConstantToSmoothAddCommGroupHom IM I M φ).hom.app (op W) g)) x =
      φ (g x) :=
  (rfl)

/-- If `φ : A →+ B` is injective, `locallyConstantToSmoothAddCommGroupHom IM I M φ` is a
monomorphism of sheaves. -/
theorem mono_locallyConstantToSmoothAddCommGroupHom {φ : A →+ B} (hφ : Function.Injective φ) :
    Mono (locallyConstantToSmoothAddCommGroupHom IM I M φ) :=
  ⟨fun {K} α₁ α₂ h ↦ by
    ext W k
    have hk := congrArg (fun η : K ⟶ smoothSheafAddCommGroup IM I M B ↦ η.hom.app W k) h
    exact LocallyConstant.ext fun x ↦ hφ (DFunLike.congr_fun
      (F := C^∞⟮IM, W.unop; I, B⟯) hk x)⟩

end LocallyConstantToSmooth

/-! ### The smooth exponential morphisms and short exact sequence -/

section ExponentialSequence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- Inclusion of locally constant integer-valued functions `ℤ_M` into smooth real-valued functions
`C^∞_M(ℝ)`. -/
def locallyConstantIntToSmoothHom :
    TopCat.locallyConstantAddCommGrpSheaf (TopCat.of M) ℤ ⟶
      smoothSheafAddCommGroup I 𝓘(ℝ, ℝ) M ℝ :=
  locallyConstantToSmoothAddCommGroupHom I 𝓘(ℝ, ℝ) M (Int.castAddHom ℝ)

@[simp]
theorem locallyConstantIntToSmoothHom_hom_app_apply (W : Opens (TopCat.of M))
    (g : LocallyConstant W ℤ) (x : W) :
    @DFunLike.coe (no_index C^∞⟮I, W; 𝓘(ℝ, ℝ), ℝ⟯) (no_index ↥W) (fun _ ↦ ℝ) _
        (no_index ((locallyConstantIntToSmoothHom I M).hom.app (op W) g)) x =
      (g x : ℝ) :=
  (rfl)

/-- The inclusion `ℤ_M ⟶ C^∞_M(ℝ)` is a monomorphism of sheaves. -/
instance mono_locallyConstantIntToSmoothHom : Mono (locallyConstantIntToSmoothHom I M) :=
  mono_locallyConstantToSmoothAddCommGroupHom I 𝓘(ℝ, ℝ) M Int.cast_injective

/-- Postcomposition of smooth real-valued functions with `Real.fourierChar : t ↦ exp(2πi t)`, as a
morphism of sheaves of abelian groups `C^∞_M(ℝ) ⟶ C^∞_M(Additive Circle)`. -/
def smoothCircleExpHom :
    smoothSheafAddCommGroup I 𝓘(ℝ, ℝ) M ℝ ⟶
      smoothSheafAddCommGroup I (𝓡 1) M (Additive Circle) :=
  ObjectProperty.homMk
    { app := fun W ↦ AddCommGrpCat.ofHom <|
        ContMDiffMap.compLeftAddMonoidHom I W.unop Real.fourierChar.toAddMonoidHom
          Real.contMDiff_fourierChar_toAddMonoidHom
      naturality := fun {_ _} _ ↦ by ext f; exact ContMDiffMap.ext fun _ ↦ rfl }

@[simp]
theorem smoothCircleExpHom_hom_app_apply (W : Opens (TopCat.of M))
    (f : C^∞⟮I, W; 𝓘(ℝ, ℝ), ℝ⟯) (x : W) :
    @DFunLike.coe (no_index C^∞⟮I, W; 𝓡 1, Additive Circle⟯) (no_index ↥W)
        (fun _ ↦ Additive Circle) _
        (no_index ((smoothCircleExpHom I M).hom.app (op W) f)) x =
      Additive.ofMul (Real.fourierChar (f x)) :=
  (rfl)

/-- Multiplicative counterpart of `smoothCircleExpHom`, sending sections of
`smoothSheafCommGroup I 𝓘(ℝ, ℝ) M (Multiplicative ℝ)` to sections of
`smoothSheafCommGroup I (𝓡 1) M Circle` via `Real.fourierChar`. -/
def smoothCircleExpMulHom :
    smoothSheafCommGroup I 𝓘(ℝ, ℝ) M (Multiplicative ℝ) ⟶
      smoothSheafCommGroup I (𝓡 1) M Circle :=
  ObjectProperty.homMk
    { app := fun W ↦ CommGrpCat.ofHom <|
        ContMDiffMap.compLeftMonoidHom I W.unop (AddChar.toMonoidHomEquiv Real.fourierChar)
          Real.contMDiff_fourierChar_toMonoidHom
      naturality := fun {_ _} _ ↦ by ext f; exact ContMDiffMap.ext fun _ ↦ rfl }

@[simp]
theorem smoothCircleExpMulHom_hom_app_apply (W : Opens (TopCat.of M))
    (f : C^∞⟮I, W; 𝓘(ℝ, ℝ), Multiplicative ℝ⟯) (x : W) :
    @DFunLike.coe (no_index C^∞⟮I, W; 𝓡 1, Circle⟯) (no_index ↥W) (fun _ ↦ Circle) _
        (no_index ((smoothCircleExpMulHom I M).hom.app (op W) f)) x =
      Real.fourierChar (Multiplicative.toAdd (f x)) :=
  (rfl)

/-- Integer-valued locally constant functions lie in the kernel of `smoothCircleExpHom`. -/
@[simp, reassoc]
theorem locallyConstantIntToSmoothHom_comp_smoothCircleExpHom :
    locallyConstantIntToSmoothHom I M ≫ smoothCircleExpHom I M = 0 := by
  ext W g
  let g' : LocallyConstant W.unop ℤ := g
  refine ContMDiffMap.ext fun x ↦ ?_
  -- Reduce zero in `Additive Circle` to `1` in `Circle` via `Real.fourierChar_eq_one_iff`.
  change Additive.ofMul (Real.fourierChar (g' x : ℝ)) = 0
  rw [← ofMul_one]
  exact congrArg Additive.ofMul (Real.fourierChar_eq_one_iff.mpr ⟨g' x, rfl⟩)

/-- Over every open subset `W`, a smooth real-valued function maps to `0` under `smoothCircleExpHom`
if and only if it is a locally constant integer-valued function. -/
theorem exact_locallyConstantIntToSmoothHom_smoothCircleExpHom (W : Opens (TopCat.of M)) :
    Function.Exact ((locallyConstantIntToSmoothHom I M).hom.app (op W)).hom
      ((smoothCircleExpHom I M).hom.app (op W)).hom := by
  intro f
  let f' : C^∞⟮I, W; 𝓘(ℝ, ℝ), ℝ⟯ := f
  refine ⟨fun hf ↦ ?_, fun ⟨g, hg⟩ ↦ ?_⟩
  · have hint (x : W) : ∃ k : ℤ, f' x = k := by
      have hx : Additive.ofMul (Real.fourierChar (f' x)) = 0 :=
        DFunLike.congr_fun (F := C^∞⟮I, W; 𝓡 1, Additive Circle⟯) hf x
      exact Real.fourierChar_eq_one_iff.mp (ofMul_eq_zero.mp hx)
    have hfloor (x : W) : (⌊f' x⌋ : ℝ) = f' x := by
      obtain ⟨k, hk⟩ := hint x
      rw [hk, Int.floor_intCast]
    have hlc : IsLocallyConstant fun x : W ↦ ⌊f' x⌋ := by
      refine (IsLocallyConstant.iff_exists_open _).mpr fun x ↦ ?_
      refine ⟨{y : W | |f' y - f' x| < 1},
        isOpen_lt (f'.contMDiff.continuous.sub continuous_const).abs continuous_const,
        by simp, fun y hy ↦ ?_⟩
      have hlt : |((⌊f' y⌋ - ⌊f' x⌋ : ℤ) : ℝ)| < (1 : ℤ) := by
        simpa [Int.cast_sub, hfloor y, hfloor x] using hy
      have habs : |⌊f' y⌋ - ⌊f' x⌋| < 1 := by
        exact_mod_cast hlt
      obtain ⟨_, _⟩ := abs_lt.mp habs
      omega
    exact ⟨⟨fun x ↦ ⌊f' x⌋, hlc⟩, ContMDiffMap.ext hfloor⟩
  · rw [← hg]
    have hcomp := congrArg (fun η ↦ (η.hom.app (op W)).hom g)
      (locallyConstantIntToSmoothHom_comp_smoothCircleExpHom I M)
    exact hcomp

/-- Smooth local logarithm around any point `x ∈ U`: a smooth `Additive Circle`-valued section `u`
lifts on an open neighborhood `V ≤ U` of `x` to a smooth real-valued section. -/
private lemma exists_smooth_local_lift (U : Opens (TopCat.of M))
    (u : C^∞⟮I, U; 𝓡 1, Additive Circle⟯) (x : M) (hxU : x ∈ U) :
    ∃ (V : Opens (TopCat.of M)) (hVU : V ≤ U),
      (∃ s : C^∞⟮I, V; 𝓘(ℝ, ℝ), ℝ⟯,
        (smoothCircleExpHom I M).hom.app (op V) s =
          (smoothSheafAddCommGroup I (𝓡 1) M (Additive Circle)).obj.map (homOfLE hVU).op u) ∧
      x ∈ V := by
  let u' : U → Circle := fun y ↦ Additive.toMul (u y)
  have hu' : CMDiff ∞ u' := Additive.contMDiff_toMul.comp u.contMDiff
  let z₀ : Circle := u' ⟨x, hxU⟩
  let q : U → Circle := fun y ↦ z₀⁻¹ * u' y
  have hq : CMDiff ∞ q := contMDiff_const.mul hu'
  let V₀ : Set U := {y : U | ((q y : Circle) : ℂ) ∈ Complex.slitPlane}
  have hV₀_open : IsOpen V₀ :=
    Complex.isOpen_slitPlane.preimage (continuous_subtype_val.comp hq.continuous)
  have hxV₀ : (⟨x, hxU⟩ : U) ∈ V₀ := by
    have hq0 : ((q ⟨x, hxU⟩ : Circle) : ℂ) = 1 :=
      (congrArg (fun w : Circle ↦ (w : ℂ)) (inv_mul_cancel z₀)).trans Circle.coe_one
    -- Unfold membership in `V₀` to rewrite `(q ⟨x, hxU⟩ : ℂ)` to `1`.
    change ((q ⟨x, hxU⟩ : Circle) : ℂ) ∈ Complex.slitPlane
    rw [hq0]
    exact Complex.mem_slitPlane_iff_arg.mpr ⟨by simp [Real.pi_ne_zero.symm], one_ne_zero⟩
  let V : Opens (TopCat.of M) := ⟨Subtype.val '' V₀, U.isOpen.isOpenMap_subtype_val V₀ hV₀_open⟩
  have hVU : V ≤ U := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have hvSlit (v : V) : ((q (Opens.inclusion hVU v) : Circle) : ℂ) ∈ Complex.slitPlane := by
    obtain ⟨y, hy, heq⟩ := v.2
    exact (Subtype.ext heq : y = Opens.inclusion hVU v) ▸ hy
  have harg : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun v : V ↦ Complex.arg (q (Opens.inclusion hVU v))) :=
    fun v ↦ (contMDiffAt_circle_arg (abs_lt.mpr
      ⟨Complex.neg_pi_lt_arg _, lt_of_le_of_ne (Complex.arg_le_pi _)
        (Complex.slitPlane_arg_ne_pi (hvSlit v))⟩)).comp v
      (hq.comp (contMDiff_inclusion hVU)).contMDiffAt
  let s : C^∞⟮I, V; 𝓘(ℝ, ℝ), ℝ⟯ :=
    ⟨fun v ↦ (Complex.arg z₀ + Complex.arg (q (Opens.inclusion hVU v))) / (2 * Real.pi),
      (contMDiff_const.add harg).div_const (2 * Real.pi)⟩
  refine ⟨V, hVU, ⟨s, ContMDiffMap.ext fun v ↦ ?_⟩, ⟨⟨x, hxU⟩, hxV₀, rfl⟩⟩
  have h2pi : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  -- Evaluate both smooth sections at `v` and cancel `z₀ * z₀⁻¹` in `Circle`.
  change Additive.ofMul (Real.fourierChar (s v)) = u (Opens.inclusion hVU v)
  rw [← ofMul_toMul (u (Opens.inclusion hVU v))]
  refine congrArg Additive.ofMul ?_
  have hsv : s v = (Complex.arg z₀ + Complex.arg (q (Opens.inclusion hVU v))) / (2 * Real.pi) :=
    rfl
  have hqv : q (Opens.inclusion hVU v) = z₀⁻¹ * u' (Opens.inclusion hVU v) := rfl
  exact (congrArg Real.fourierChar hsv).trans <|
    (Real.fourierChar_apply' _).trans <|
      (congrArg Circle.exp (mul_div_cancel₀ _ h2pi)).trans <|
        (Circle.exp_add _ _).trans <|
          (congrArg₂ (· * ·) (Circle.exp_arg z₀) ((Circle.exp_arg _).trans hqv)).trans
            (mul_inv_cancel_left z₀ (u' (Opens.inclusion hVU v)))

/-- `smoothCircleExpHom I M` is an epimorphism of sheaves of abelian groups, by existence of smooth
local logarithms around every point. -/
instance epi_smoothCircleExpHom : Epi (smoothCircleExpHom I M) := by
  rw [← TopCat.Sheaf.isLocallySurjective_iff_epi, TopCat.Presheaf.isLocallySurjective_iff]
  intro U u x hxU
  exact exists_smooth_local_lift I M U u x hxU

/-- The smooth exponential short complex `ℤ_M ⟶ C^∞_M(ℝ) ⟶ C^∞_M(Additive Circle)` in
`(TopCat.of M).Sheaf AddCommGrpCat`. -/
@[expose] def smoothExponentialShortComplex :
    ShortComplex ((TopCat.of M).Sheaf AddCommGrpCat.{0}) :=
  ShortComplex.mk (locallyConstantIntToSmoothHom I M) (smoothCircleExpHom I M)
    (locallyConstantIntToSmoothHom_comp_smoothCircleExpHom I M)

@[simp]
theorem smoothExponentialShortComplex_X₁ :
    (smoothExponentialShortComplex I M).X₁ =
      TopCat.locallyConstantAddCommGrpSheaf (TopCat.of M) ℤ :=
  (rfl)

@[simp]
theorem smoothExponentialShortComplex_X₂ :
    (smoothExponentialShortComplex I M).X₂ = smoothSheafAddCommGroup I 𝓘(ℝ, ℝ) M ℝ :=
  (rfl)

@[simp]
theorem smoothExponentialShortComplex_X₃ :
    (smoothExponentialShortComplex I M).X₃ =
      smoothSheafAddCommGroup I (𝓡 1) M (Additive Circle) :=
  (rfl)

@[simp]
theorem smoothExponentialShortComplex_f :
    (smoothExponentialShortComplex I M).f = locallyConstantIntToSmoothHom I M :=
  (rfl)

@[simp]
theorem smoothExponentialShortComplex_g :
    (smoothExponentialShortComplex I M).g = smoothCircleExpHom I M :=
  (rfl)

/-- **Exactness of the smooth exponential sequence.** For any charted space `M` modelled on `(E, H)`
with corners `I`, `0 ⟶ ℤ_M ⟶ C^∞_M(ℝ) ⟶ C^∞_M(Additive Circle) ⟶ 0` is short exact. -/
theorem smoothExponentialShortComplex_shortExact :
    (smoothExponentialShortComplex I M).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_
    (mono_locallyConstantIntToSmoothHom I M) (epi_smoothCircleExpHom I M)
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  rw [ShortComplex.ab_exact_iff]
  intro s hs
  let S := smoothExponentialShortComplex I M
  let P₁ : (TopCat.of M).Presheaf AddCommGrpCat.{0} := S.X₁.obj
  let P₂ : (TopCat.of M).Presheaf AddCommGrpCat.{0} := S.X₂.obj
  let P₃ : (TopCat.of M).Presheaf AddCommGrpCat.{0} := S.X₃.obj
  obtain ⟨U, hxU, f, rfl⟩ := P₂.exists_germ_eq s
  have hgerm : P₃.germ U x hxU (S.g.hom.app (op U) f) = P₃.germ U x hxU 0 := by
    rw [map_zero]
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU S.g.hom f).symm.trans hs
  obtain ⟨W, hxW, i₁, _, hW⟩ := P₃.germ_eq x hxU hxU (S.g.hom.app (op U) f) 0 hgerm
  rw [map_zero] at hW
  have hW' : S.g.hom.app (op W) (P₂.map i₁.op f) = 0 := by
    rw [← ConcreteCategory.comp_apply, S.g.hom.naturality, ConcreteCategory.comp_apply]
    exact hW
  obtain ⟨gW, hgW⟩ := (exact_locallyConstantIntToSmoothHom_smoothCircleExpHom I M W _).mp hW'
  refine ⟨P₁.germ W x hxW gW, ?_⟩
  exact (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW S.f.hom gW).trans <|
    (congrArg (P₂.germ W x hxW) hgW).trans (P₂.germ_res_apply i₁ x hxW f)

end ExponentialSequence

/-! ### Cohomological consequences on smooth manifolds -/

section Cohomology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- The image of `H⁰(M, C^∞_M(ℝ)) →+ H⁰(M, C^∞_M(Additive Circle))` is the kernel of the
degree-zero connecting homomorphism into `H¹(M, ℤ_M)`. -/
theorem exact_map_smoothCircleExpHom_δ_zero :
    Function.Exact (CategoryTheory.Sheaf.H.map (smoothCircleExpHom I M) 0)
      (CategoryTheory.Sheaf.H.δ (smoothExponentialShortComplex_shortExact I M) 0 1 rfl) :=
  CategoryTheory.Sheaf.H.exact_map_δ (smoothExponentialShortComplex_shortExact I M) 0 1 rfl

/-- On a Hausdorff `σ`-compact manifold modelled on a finite-dimensional real normed space, the
degree-zero connecting homomorphism `H⁰(M, C^∞_M(Additive Circle)) →+ H¹(M, ℤ_M)` is surjective. -/
theorem smoothExponential_δ_zero_surjective_of_sigmaCompactSpace
    [IsManifold I ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] :
    Function.Surjective
      (CategoryTheory.Sheaf.H.δ (smoothExponentialShortComplex_shortExact I M) 0 1 rfl) :=
  CategoryTheory.Sheaf.H.δ_surjective (smoothExponentialShortComplex_shortExact I M) 0 1 rfl
    (subsingleton_H_smoothSheafAddCommGroup_of_sigmaCompactSpace I 1 Nat.one_pos)

/-- On a Hausdorff second-countable manifold modelled on a finite-dimensional real normed space, the
degree-zero connecting homomorphism `H⁰(M, C^∞_M(Additive Circle)) →+ H¹(M, ℤ_M)` is surjective. -/
theorem smoothExponential_δ_zero_surjective
    [IsManifold I ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SecondCountableTopology M] :
    Function.Surjective
      (CategoryTheory.Sheaf.H.δ (smoothExponentialShortComplex_shortExact I M) 0 1 rfl) :=
  CategoryTheory.Sheaf.H.δ_surjective (smoothExponentialShortComplex_shortExact I M) 0 1 rfl
    (subsingleton_H_smoothSheafAddCommGroup I 1 Nat.one_pos)

/-- On a Hausdorff `σ`-compact manifold modelled on a finite-dimensional real normed space, the
connecting homomorphism of the smooth exponential sequence is an additive isomorphism
`H^q(M, C^∞_M(Additive Circle)) ≃+ H^{q + 1}(M, ℤ_M)` in every positive degree `q > 0`. -/
def smoothExponentialConnectingAddEquivOfSigmaCompactSpace
    [IsManifold I ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    (q : ℕ) (hq : 0 < q) :
    (smoothSheafAddCommGroup I (𝓡 1) M (Additive Circle)).H q ≃+
      (TopCat.locallyConstantAddCommGrpSheaf (TopCat.of M) ℤ).H (q + 1) :=
  AddEquiv.ofBijective
    (CategoryTheory.Sheaf.H.δ (smoothExponentialShortComplex_shortExact I M) q (q + 1) rfl)
    (CategoryTheory.Sheaf.H.δ_bijective (smoothExponentialShortComplex_shortExact I M) q (q + 1)
      rfl (subsingleton_H_smoothSheafAddCommGroup_of_sigmaCompactSpace I q hq)
      (subsingleton_H_smoothSheafAddCommGroup_of_sigmaCompactSpace I (q + 1) (Nat.succ_pos q)))

@[simp]
theorem smoothExponentialConnectingAddEquivOfSigmaCompactSpace_apply
    [IsManifold I ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    (q : ℕ) (hq : 0 < q) (x : (smoothSheafAddCommGroup I (𝓡 1) M (Additive Circle)).H q) :
    smoothExponentialConnectingAddEquivOfSigmaCompactSpace I M q hq x =
      CategoryTheory.Sheaf.H.δ (smoothExponentialShortComplex_shortExact I M) q (q + 1) rfl x :=
  (rfl)

/-- On a Hausdorff second-countable manifold modelled on a finite-dimensional real normed space, the
connecting homomorphism of the smooth exponential sequence is an additive isomorphism
`H^q(M, C^∞_M(Additive Circle)) ≃+ H^{q + 1}(M, ℤ_M)` in every positive degree `q > 0`. -/
def smoothExponentialConnectingAddEquiv
    [IsManifold I ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SecondCountableTopology M]
    (q : ℕ) (hq : 0 < q) :
    (smoothSheafAddCommGroup I (𝓡 1) M (Additive Circle)).H q ≃+
      (TopCat.locallyConstantAddCommGrpSheaf (TopCat.of M) ℤ).H (q + 1) :=
  AddEquiv.ofBijective
    (CategoryTheory.Sheaf.H.δ (smoothExponentialShortComplex_shortExact I M) q (q + 1) rfl)
    (CategoryTheory.Sheaf.H.δ_bijective (smoothExponentialShortComplex_shortExact I M) q (q + 1)
      rfl (subsingleton_H_smoothSheafAddCommGroup I q hq)
      (subsingleton_H_smoothSheafAddCommGroup I (q + 1) (Nat.succ_pos q)))

@[simp]
theorem smoothExponentialConnectingAddEquiv_apply
    [IsManifold I ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SecondCountableTopology M]
    (q : ℕ) (hq : 0 < q) (x : (smoothSheafAddCommGroup I (𝓡 1) M (Additive Circle)).H q) :
    smoothExponentialConnectingAddEquiv I M q hq x =
      CategoryTheory.Sheaf.H.δ (smoothExponentialShortComplex_shortExact I M) q (q + 1) rfl x :=
  (rfl)

/-- On any open subset `U` of a Hausdorff second-countable manifold `M` modelled on a
finite-dimensional real normed space, every smooth circle-valued function on `U` lifts to a smooth
real-valued function if and only if `H¹(U, ℤ_M)` vanishes. -/
theorem smoothCircleExpHom_app_surjective_iff_subsingleton_H'_one
    [IsManifold I ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SecondCountableTopology M]
    (U : Opens (TopCat.of M)) :
    Function.Surjective ((smoothCircleExpHom I M).hom.app (op U)) ↔
      Subsingleton ((TopCat.locallyConstantAddCommGrpSheaf (TopCat.of M) ℤ).H' 1 U) :=
  ⟨fun hg ↦ CategoryTheory.Sheaf.H'.subsingleton_X₁_one
      (smoothExponentialShortComplex_shortExact I M) U hg
      (subsingleton_H'_smoothSheafAddCommGroup I U 1 Nat.one_pos),
    CategoryTheory.Sheaf.H'.g_hom_app_surjective (smoothExponentialShortComplex_shortExact I M) U⟩

end Cohomology

end TauCeti

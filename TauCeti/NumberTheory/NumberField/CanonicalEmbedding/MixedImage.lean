/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# The mixed image of an `𝓞 K`-module

Let `K` be a number field and `ι` a finite type. An `𝓞 K`-submodule `Λ` of `ι → K` is carried
into `ι → mixedSpace K` by applying the mixed embedding in every coordinate. Its image
`Submodule.mixedImage Λ` is a `ℤ`-submodule of a finite-dimensional real vector space, and it is a
full lattice there, a `ZLattice` in the sense of Mathlib, as soon as `Λ` is finitely generated and
spans `ι → K` over `K`. This is how a finitely generated `𝓞 K`-module of `Kⁿ` becomes a lattice
to which the real geometry of numbers applies: covolumes, successive minima and Minkowski's
theorems for `Λ` are those of `Λ.mixedImage`.

The two hypotheses split, and each is also necessary: the mixed image is discrete exactly when `Λ`
is finitely generated, and it spans over `ℝ` exactly when `Λ` spans over `K`.

## Main definitions

* `Submodule.mixedImage Λ`: the image of `Λ` in `ι → mixedSpace K` under the coordinatewise mixed
  embedding, as a `ℤ`-submodule.
* `Submodule.mixedImageEquiv Λ`: the `ℤ`-linear equivalence `Λ ≃ₗ[ℤ] Λ.mixedImage`.

## Main results

* `NumberField.mixedEmbedding.mem_span_pi_latticeBasis`: the `ℤ`-span of
  `Pi.basis fun _ ↦ latticeBasis K` is the coordinatewise image of `ι → 𝓞 K`.
* `Submodule.discreteTopology_mixedImage_iff`: the mixed image is discrete exactly when the
  module is finitely generated; the instance form takes `[Module.Finite (𝓞 K) Λ]`.
* `Submodule.span_real_mixedImage_eq_top_iff`: the mixed image spans `ι → mixedSpace K` over `ℝ`
  exactly when the module spans `ι → K` over `K`.
* `Submodule.isZLattice_mixedImage`, `Submodule.isZLattice_mixedImage_iff`: a discrete mixed
  image is a full lattice exactly when the module spans `ι → K` over `K`.

## Implementation notes

For finite generation, the generators of `Λ` have a common integer denominator `y`, so
multiplication by `y` sends the mixed image into the span of the `ℤ`-basis
`Pi.basis fun _ ↦ latticeBasis K` of the image of `(𝓞 K)^ι`, which is discrete. For the spanning
condition, every `c ∈ K` is `a / n` with `a ∈ 𝓞 K` and `n` a nonzero integer, so the image of
`c • x` for `x ∈ Λ` is a real multiple of the image of `a • x ∈ Λ`; hence the real span of the
mixed image contains the image of all of `ι → K`, and in particular the basis above. Conversely,
a nonzero `K`-linear functional `f` vanishing on `Λ` gives the real-linear map
`z ↦ ∑ i, f eᵢ * zᵢ` to `mixedSpace K`, which vanishes on the mixed image but not everywhere;
and a discrete subgroup of a finite-dimensional real space is finitely generated.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  Appendix C.2 (the lattice of an `𝓞 K`-module in the Minkowski space).
-/

public section

open Module NumberField NumberField.mixedEmbedding

variable {K : Type*} [Field K] {ι : Type*}

namespace NumberField.mixedEmbedding

/-- The `ℤ`-span of the basis `Pi.basis fun _ ↦ latticeBasis K` of `ι → mixedSpace K` is the image
of `ι → 𝓞 K` under the mixed embedding applied in every coordinate; the coordinatewise form of
`NumberField.mixedEmbedding.mem_span_latticeBasis`. -/
theorem mem_span_pi_latticeBasis [NumberField K] [Fintype ι] {z : ι → mixedSpace K} :
    z ∈ Submodule.span ℤ (Set.range (Pi.basis fun _ : ι ↦ latticeBasis K)) ↔
      ∃ x : ι → 𝓞 K, (fun i ↦ mixedEmbedding K (x i)) = z := by
  rw [(Pi.basis fun _ : ι ↦ latticeBasis K).mem_span_iff_repr_mem ℤ]
  simp only [Pi.basis_repr, Sigma.forall, ← (latticeBasis K).mem_span_iff_repr_mem ℤ,
    mem_span_latticeBasis, LinearMap.mem_range]
  refine ⟨fun h ↦ ?_, fun ⟨x, hx⟩ i ↦ ⟨x i, by simp [← hx]⟩⟩
  choose x hx using h
  exact ⟨x, funext fun i ↦ by simpa using hx i⟩

end NumberField.mixedEmbedding

namespace Submodule

/-- The **mixed image** of an `𝓞 K`-submodule `Λ` of `ι → K`: its image in `ι → mixedSpace K`
under the mixed embedding applied in every coordinate, as a `ℤ`-submodule. -/
noncomputable def mixedImage (Λ : Submodule (𝓞 K) (ι → K)) :
    Submodule ℤ (ι → mixedSpace K) :=
  (Λ.restrictScalars ℤ).map (LinearMap.piMap fun _ ↦ (mixedEmbedding K).toIntAlgHom.toLinearMap)

@[simp]
theorem mem_mixedImage {Λ : Submodule (𝓞 K) (ι → K)} {y : ι → mixedSpace K} :
    y ∈ Λ.mixedImage ↔ ∃ x ∈ Λ, (fun i ↦ mixedEmbedding K (x i)) = y :=
  Iff.rfl

@[gcongr]
theorem mixedImage_mono {Λ Λ' : Submodule (𝓞 K) (ι → K)} (h : Λ ≤ Λ') :
    Λ.mixedImage ≤ Λ'.mixedImage :=
  fun _ ⟨x, hx, hxy⟩ ↦ ⟨x, h hx, hxy⟩

variable [NumberField K]

/-- The `ℤ`-linear equivalence between an `𝓞 K`-submodule `Λ` of `ι → K` and its mixed image,
given by the mixed embedding in every coordinate. -/
noncomputable def mixedImageEquiv (Λ : Submodule (𝓞 K) (ι → K)) :
    Λ.restrictScalars ℤ ≃ₗ[ℤ] Λ.mixedImage :=
  equivMapOfInjective _ (Function.Injective.piMap fun _ ↦ mixedEmbedding_injective K) _

@[simp]
theorem coe_mixedImageEquiv_apply (Λ : Submodule (𝓞 K) (ι → K)) (x : Λ.restrictScalars ℤ) :
    (Λ.mixedImageEquiv x : ι → mixedSpace K) = fun i ↦ mixedEmbedding K ((x : ι → K) i) :=
  coe_equivMapOfInjective_apply ..

section Finite

variable [Finite ι]

private theorem discreteTopology_mixedImage_of_fg {Λ : Submodule (𝓞 K) (ι → K)} (hΛ : Λ.FG) :
    DiscreteTopology Λ.mixedImage := by
  classical
  cases nonempty_fintype ι
  obtain ⟨s, rfl⟩ := hΛ
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    (s.biUnion fun x ↦ Finset.univ.image x)
  -- Multiplication by `y` sends `span (𝓞 K) s` into the vectors with integral coordinates.
  have hint : ∀ x ∈ span (𝓞 K) (s : Set (ι → K)), ∀ i, IsIntegral ℤ (y • x i) := by
    intro x hx
    induction hx using span_induction with
    | mem x hx =>
      exact fun i ↦ hy _ (Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image_of_mem _ (by simp)⟩)
    | zero => simpa using fun _ ↦ isIntegral_zero
    | add x z _ _ hx hz => simpa [smul_add] using fun i ↦ (hx i).add (hz i)
    | smul a x _ hx =>
      intro i
      have : y • (a • x) i = (a : K) * y • x i := by
        simp [Algebra.smul_def, mul_left_comm]
      rw [this]
      exact (a.isIntegral_coe.tower_top).mul (hx i)
  have hmaps : ∀ z : (span (𝓞 K) (s : Set (ι → K))).mixedImage,
      (y : ℝ) • (z : ι → mixedSpace K) ∈
        span ℤ (Set.range (Pi.basis fun _ : ι ↦ latticeBasis K)) := by
    rintro ⟨_, hz⟩
    obtain ⟨x, hx, rfl⟩ := mem_mixedImage.mp hz
    have : (y : ℝ) • (fun i ↦ mixedEmbedding K (x i)) =
        fun i ↦ mixedEmbedding K (y • x i) := by
      ext1 i
      rw [Pi.smul_apply, map_zsmul, Int.cast_smul_eq_zsmul]
    rw [this]
    exact mem_span_pi_latticeBasis.mpr ⟨fun i ↦ ⟨y • x i, hint x hx i⟩, rfl⟩
  refine DiscreteTopology.of_continuous_injective
    (f := fun z ↦ (⟨_, hmaps z⟩ : span ℤ (Set.range (Pi.basis fun _ : ι ↦ latticeBasis K))))
    (by fun_prop) fun z z' h ↦ ?_
  have hy0' : (y : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hy0
  exact Subtype.ext (smul_right_injective _ hy0' (congrArg Subtype.val h))

/-- **The mixed image of an `𝓞 K`-module is discrete exactly when the module is finitely
generated.** -/
theorem discreteTopology_mixedImage_iff {Λ : Submodule (𝓞 K) (ι → K)} :
    DiscreteTopology Λ.mixedImage ↔ Λ.FG := by
  refine ⟨fun _ ↦ ?_, discreteTopology_mixedImage_of_fg⟩
  classical
  cases nonempty_fintype ι
  have hinj : Function.Injective
      (LinearMap.piMap fun _ : ι ↦ (mixedEmbedding K).toIntAlgHom.toLinearMap) :=
    Function.Injective.piMap fun _ ↦ mixedEmbedding_injective K
  exact FG.of_restrictScalars ℤ
    (fg_of_fg_map_injective _ hinj (Module.Finite.iff_fg.mp (inferInstance :
      Module.Finite ℤ Λ.mixedImage)))

/-- The mixed image of a finitely generated `𝓞 K`-module is discrete. -/
instance (Λ : Submodule (𝓞 K) (ι → K)) [Module.Finite (𝓞 K) Λ] :
    DiscreteTopology Λ.mixedImage :=
  discreteTopology_mixedImage_iff.mpr (Module.Finite.iff_fg.mp ‹_›)

private theorem span_real_mixedImage_of_span_eq_top {Λ : Submodule (𝓞 K) (ι → K)}
    (hΛ : span K (Λ : Set (ι → K)) = ⊤) :
    span ℝ (Λ.mixedImage : Set (ι → mixedSpace K)) = ⊤ := by
  classical
  cases nonempty_fintype ι
  set V := span ℝ (Λ.mixedImage : Set (ι → mixedSpace K))
  -- The image of `c • x` lies in `V` for every `c ∈ K` and `x ∈ Λ`.
  have hsmul : ∀ (c : K), ∀ x ∈ Λ, (fun i ↦ mixedEmbedding K (c * x i)) ∈ V := by
    intro c x hx
    obtain ⟨n, hn0, hn⟩ := exists_integral_multiples ℤ ℚ {c}
    have ha : IsIntegral ℤ (n • c) := hn c (Finset.mem_singleton_self c)
    have hmem : (fun i ↦ mixedEmbedding K ((n • c) * x i)) ∈ V := by
      refine subset_span (mem_mixedImage.mpr ⟨(⟨n • c, ha⟩ : 𝓞 K) • x, smul_mem _ _ hx, ?_⟩)
      ext1 i
      simp [Algebra.smul_def]
    have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn0
    convert V.smul_mem (n : ℝ)⁻¹ hmem using 1
    ext1 i
    have : mixedEmbedding K (n • c * x i) = (n : ℝ) • mixedEmbedding K (c * x i) := by
      rw [smul_mul_assoc, map_zsmul, Int.cast_smul_eq_zsmul]
    rw [Pi.smul_apply, this, smul_smul, inv_mul_cancel₀ hn', one_smul]
  -- Hence the image of every vector of `ι → K` lies in `V`.
  have hall : ∀ x : ι → K, (fun i ↦ mixedEmbedding K (x i)) ∈ V := by
    intro x
    have hx : x ∈ span K (Λ : Set (ι → K)) := hΛ ▸ mem_top
    obtain ⟨m, f, g, rfl⟩ := mem_span_set'.mp hx
    have : (fun i ↦ mixedEmbedding K ((∑ k, f k • (g k : ι → K)) i)) =
        ∑ k, fun i ↦ mixedEmbedding K (f k * (g k : ι → K) i) := by
      ext1 i
      simp [Finset.sum_apply, map_sum]
    rw [this]
    exact V.sum_mem fun k _ ↦ hsmul (f k) _ (g k).2
  refine eq_top_iff.mpr ?_
  rw [← (Pi.basis fun _ : ι ↦ latticeBasis K).span_eq, span_le]
  rintro _ ⟨⟨i, j⟩, rfl⟩
  have : Pi.basis (fun _ : ι ↦ latticeBasis K) ⟨i, j⟩ =
      fun i' ↦ mixedEmbedding K (Pi.single (M := fun _ ↦ K) i (integralBasis K j) i') := by
    ext1 i'
    rw [Pi.basis_apply, latticeBasis_apply]
    by_cases h : i' = i
    · subst h; simp
    · simp [h]
  rw [this]
  exact hall _

/-- **The mixed image of an `𝓞 K`-module spans `ι → mixedSpace K` over `ℝ` exactly when the
module spans `ι → K` over `K`.** -/
theorem span_real_mixedImage_eq_top_iff {Λ : Submodule (𝓞 K) (ι → K)} :
    span ℝ (Λ.mixedImage : Set (ι → mixedSpace K)) = ⊤ ↔ span K (Λ : Set (ι → K)) = ⊤ := by
  refine ⟨fun h ↦ ?_, span_real_mixedImage_of_span_eq_top⟩
  classical
  cases nonempty_fintype ι
  by_contra hne
  obtain ⟨f, hf0, hle⟩ :=
    (span K (Λ : Set (ι → K))).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hne)
  -- The real-linear map `z ↦ ∑ i, f eᵢ * zᵢ` on the mixed side, which reads `f` off the image.
  let F : (ι → mixedSpace K) →ₗ[ℝ] mixedSpace K :=
    ∑ i, LinearMap.mulLeft ℝ (mixedEmbedding K (f fun j ↦ if i = j then 1 else 0)) ∘ₗ
      LinearMap.proj i
  have hF (x : ι → K) : F (fun i ↦ mixedEmbedding K (x i)) = mixedEmbedding K (f x) := by
    rw [LinearMap.pi_apply_eq_sum_univ f x, map_sum]
    simp [F, map_mul, mul_comm]
  have hker : span ℝ (Λ.mixedImage : Set (ι → mixedSpace K)) ≤ LinearMap.ker F := by
    rw [span_le]
    intro z hz
    obtain ⟨x, hx, rfl⟩ := mem_mixedImage.mp hz
    rw [SetLike.mem_coe, LinearMap.mem_ker, hF, hle (subset_span hx), map_zero]
  refine hf0 (LinearMap.ext fun x ↦ ?_)
  have hx : F (fun i ↦ mixedEmbedding K (x i)) = 0 := hker (h ▸ mem_top)
  rw [hF] at hx
  exact (map_eq_zero_iff _ (mixedEmbedding_injective K)).mp hx

end Finite

variable [Fintype ι]

open scoped Classical in
/-- **The mixed image of an `𝓞 K`-module spanning `ι → K` is a full lattice** whenever it is
discrete, in particular when the module is finitely generated
(`Submodule.discreteTopology_mixedImage_iff`). -/
theorem isZLattice_mixedImage {Λ : Submodule (𝓞 K) (ι → K)} [DiscreteTopology Λ.mixedImage]
    (hΛ : span K (Λ : Set (ι → K)) = ⊤) :
    IsZLattice ℝ Λ.mixedImage :=
  ⟨span_real_mixedImage_eq_top_iff.mpr hΛ⟩

open scoped Classical in
/-- A discrete mixed image is a full lattice exactly when the module spans `ι → K` over `K`. -/
theorem isZLattice_mixedImage_iff {Λ : Submodule (𝓞 K) (ι → K)} [DiscreteTopology Λ.mixedImage] :
    IsZLattice ℝ Λ.mixedImage ↔ span K (Λ : Set (ι → K)) = ⊤ :=
  ⟨fun h ↦ span_real_mixedImage_eq_top_iff.mp h.span_top, isZLattice_mixedImage⟩

end Submodule

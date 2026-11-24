/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.DiscSphere
public import TauCeti.Geometry.Manifold.LocallyFlat.Bicollar
public import TauCeti.Topology.VectorBundle.UnitSection
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# The normal collar of a two-sided compact hypersurface

Let `f : M → N` be a smooth embedding of a compact manifold into a Riemannian manifold, of
codimension one, and `ν` a continuous field of unit normal vectors along `f`, a section of the
normal bundle of `f` (`TauCeti.SmoothEmbedding.NormalSpace`, with its induced normal metric). The
**normal collar** of `f` along `ν` is

`c_ν (x, t) = exp_{f x} (t ν x)`,

the normal exponential `TauCeti.SmoothEmbedding.normalExp` at `t ν x`, with `c_ν (x, 0) = f x`.

* `TauCeti.SmoothEmbedding.exists_isOpenEmbedding_normalCollar`: for some `ε > 0`, the normal
  collar is defined on `M × (-ε, ε)` and is an open embedding there, that is, a homeomorphism onto
  an open neighbourhood of `f M`.
* `TauCeti.SmoothEmbedding.exists_isBicollar_normalCollar`: reparametrized by
  `s ↦ (2ε / π) arctan s`, the normal collar is a bicollar of `f` (`TauCeti.IsBicollar`).

The unit normal field trivializes the normal line bundle, `(x, t) ↦ t ν x` being a homeomorphism
`M × ℝ ≃ₜ ν_f` (`TauCeti.VectorBundle.unitSectionHomeomorph`) that carries `M × (-ε, ε)` onto the
normal vectors of length less than `ε`. By the tubular neighbourhood theorem
(`TauCeti.SmoothEmbedding.exists_isClosedEmbedding_normalExp_disc`), the normal exponential is an
open embedding on the normal vectors of length less than a positive function `r`, and `M` being
compact, `ε` can be taken below `r` everywhere.

The unit normal field is only assumed continuous: a smooth one is in particular continuous. The
smoothness of the collar, the crossing form and the defining function are not treated here.
-/

public section

open Bundle Manifold Set Topology Function

open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

variable {E V P H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [I.Boundaryless] [J.Boundaryless] [T2Space N] [SecondCountableTopology N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ V (fun y : N ↦ TangentSpace J y)]

/-- The shared step of `exists_isOpenEmbedding_normalCollar` and `exists_isBicollar_normalCollar`:
for some `ε > 0`, every open embedding `h` into `M × (-ε, ε)`, followed by
`(x, t) ↦ exp_{f x} (t ν x)`, is an open embedding, with the normal vectors `t ν x` in the domain
of the normal exponential. -/
private theorem exists_isOpenEmbedding_normalExp_comp
    (f : SmoothEmbedding I J ∞ M N)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    (hP : Module.finrank ℝ P = 1) :
    let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    letI := f.normalSpaceFiberBundle hn hdim
    let ν : M → Type _ := fun x ↦ f.NormalSpace x hn
    letI : RiemannianBundle ν := ⟨f.normalRiemannianMetric hn⟩
    ∀ u : (x : M) → ν x, Continuous (fun x ↦ TotalSpace.mk' P x (u x)) → (∀ x, ‖u x‖ = 1) →
      ∃ ε > 0, (∀ x (t : ℝ), |t| < ε → TotalSpace.mk' P x (t • u x) ∈ f.normalExpDomain hn) ∧
        ∀ {X : Type*} [TopologicalSpace X] (h : X → M × ℝ), IsOpenEmbedding h →
          (∀ y, |(h y).2| < ε) →
          IsOpenEmbedding (fun y ↦ f.normalExp hn (TotalSpace.mk' P (h y).1 ((h y).2 • u (h y).1)))
    := by
  intro hn ν u hu hu1
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  let : RiemannianBundle ν := ⟨f.normalRiemannianMetric hn⟩
  let : ∀ x, NormedAddCommGroup (ν x) := fun x => inferInstance
  let : ∀ x, InnerProductSpace ℝ (ν x) := fun x => inferInstance
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : IsManifold J (∞ + 1) N := by simpa using (inferInstance : IsManifold J ∞ N)
  let := f.normalSpaceContMDiffVectorBundle (m := ∞) hn (by simp) hdim
  let := f.isContMDiffRiemannianBundle_normalRiemannianMetric (m := ∞) hn (by simp) hdim
  let : IsContinuousRiemannianBundle P ν :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  obtain ⟨r, hr, hdom, -, hopen, -⟩ :=
    f.exists_isClosedEmbedding_normalExp_disc hdim isOpen_univ (subset_univ _)
  -- On the compact `M`, the positive radius `r` is bounded below by some `ε > 0`.
  obtain ⟨ε, hε, hεr⟩ : ∃ ε > 0, ∀ x, ε ≤ r x := by
    cases isEmpty_or_nonempty M with
    | inl _ => exact ⟨1, one_pos, fun x ↦ isEmptyElim x⟩
    | inr _ =>
      obtain ⟨x₀, -, hx₀⟩ :=
        isCompact_univ.exists_isMinOn univ_nonempty r.contMDiff.continuous.continuousOn
      exact ⟨r x₀, hr x₀, fun x ↦ hx₀ (mem_univ x)⟩
  let Φ := TauCeti.VectorBundle.unitSectionHomeomorph P ν hP hu hu1
  have hnorm (x : M) (t : ℝ) (ht : |t| < ε) : ‖t • u x‖ < r x := by
    rw [norm_smul, hu1, mul_one, Real.norm_eq_abs]
    exact ht.trans_le (hεr x)
  refine ⟨ε, hε, fun x t ht ↦ hdom (le_of_lt (hnorm x t ht)), fun {X} _ h hh hhε ↦ ?_⟩
  let D := {p : TotalSpace P ν | ‖p.snd‖ < r p.proj}
  have hmem (p : M × ℝ) (hp : |p.2| < ε) : Φ p ∈ D := by
    change ‖(Φ p).snd‖ < r (Φ p).proj
    rw [TauCeti.VectorBundle.unitSectionHomeomorph_apply]
    exact hnorm p.1 p.2 hp
  -- the map `y ↦ (h y).2 • u (h y).1` into the disc bundle `D`
  let g : X → D := fun y ↦ ⟨Φ (h y), hmem (h y) (hhε y)⟩
  have hΦh : IsOpenEmbedding (Φ ∘ h) := Φ.isOpenEmbedding.comp hh
  have hg : IsOpenEmbedding g := by
    refine ⟨hΦh.isEmbedding.codRestrict D _, ?_⟩
    have hrange : range g = Subtype.val ⁻¹' range (Φ ∘ h) := by
      ext p
      exact ⟨fun ⟨y, hy⟩ ↦ ⟨y, congrArg Subtype.val hy⟩, fun ⟨y, hy⟩ ↦ ⟨y, Subtype.ext hy⟩⟩
    rw [hrange]
    exact hΦh.isOpen_range.preimage continuous_subtypeVal
  convert hopen.comp hg using 1
  funext y
  change _ = f.normalExp _ (Φ (h y))
  rw [TauCeti.VectorBundle.unitSectionHomeomorph_apply]

/-- **The normal collar is an open embedding.** Let `f : M → N` be a smooth embedding of a compact
manifold, of codimension one, into a Riemannian manifold, and `ν` a continuous unit normal field
along `f`. For some `ε > 0`, the normal collar `(x, t) ↦ exp_{f x} (t ν x)` is defined on
`M × (-ε, ε)` and is an open embedding there: a homeomorphism onto an open neighbourhood of
`f M`, sending `(x, 0)` to `f x` (`TauCeti.SmoothEmbedding.normalExp_zeroSection`). -/
theorem exists_isOpenEmbedding_normalCollar
    (f : SmoothEmbedding I J ∞ M N)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    (hP : Module.finrank ℝ P = 1) :
    let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    letI := f.normalSpaceFiberBundle hn hdim
    let ν : M → Type _ := fun x ↦ f.NormalSpace x hn
    letI : RiemannianBundle ν := ⟨f.normalRiemannianMetric hn⟩
    ∀ u : (x : M) → ν x, Continuous (fun x ↦ TotalSpace.mk' P x (u x)) → (∀ x, ‖u x‖ = 1) →
      ∃ ε > 0, (∀ x (t : ℝ), |t| < ε → TotalSpace.mk' P x (t • u x) ∈ f.normalExpDomain hn) ∧
        IsOpenEmbedding (fun p : M × Ioo (-ε) ε ↦
          f.normalExp hn (TotalSpace.mk' P p.1 ((p.2 : ℝ) • u p.1))) := by
  intro hn ν u hu hu1
  obtain ⟨ε, hε, hdom, hemb⟩ := exists_isOpenEmbedding_normalExp_comp f hdim hP u hu hu1
  refine ⟨ε, hε, hdom, hemb (fun p : M × Ioo (-ε) ε ↦ (p.1, (p.2 : ℝ)))
    (IsOpenEmbedding.id.prodMap isOpen_Ioo.isOpenEmbedding_subtypeVal) fun p ↦ ?_⟩
  exact abs_lt.mpr p.2.property

/-- The reparametrization `s ↦ (2ε / π) arctan s` of the real line onto `(-ε, ε)`. -/
private theorem isOpenEmbedding_mul_arctan {ε : ℝ} (hε : 0 < ε) :
    IsOpenEmbedding (fun s : ℝ ↦ 2 * ε / Real.pi * Real.arctan s) := by
  have hc : 0 < 2 * ε / Real.pi := by positivity
  have hrange : range (fun s : ℝ ↦ 2 * ε / Real.pi * Real.arctan s) = Ioo (-ε) ε := by
    rw [range_comp' (fun t ↦ 2 * ε / Real.pi * t) Real.arctan, Real.range_arctan,
      image_mul_left_Ioo hc]
    congr 1 <;> field_simp
  have hmono : StrictMono (fun s : ℝ ↦ 2 * ε / Real.pi * Real.arctan s) :=
    Real.arctan_strictMono.const_mul hc
  refine ⟨hmono.isEmbedding_of_ordConnected ?_, ?_⟩
  · rw [hrange]
    exact ordConnected_Ioo
  · rw [hrange]
    exact isOpen_Ioo

/-- **The normal collar is a bicollar.** Let `f : M → N` be a smooth embedding of a compact
manifold, of codimension one, into a Riemannian manifold, and `ν` a continuous unit normal field
along `f`. For some `ε > 0`, the normal collar `c_ν (x, t) = exp_{f x} (t ν x)` reparametrized by
`s ↦ (2ε / π) arctan s`, a homeomorphism of the real line onto `(-ε, ε)` fixing `0`, is a
bicollar of `f`. -/
theorem exists_isBicollar_normalCollar
    (f : SmoothEmbedding I J ∞ M N)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    (hP : Module.finrank ℝ P = 1) :
    let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    letI := f.normalSpaceFiberBundle hn hdim
    let ν : M → Type _ := fun x ↦ f.NormalSpace x hn
    letI : RiemannianBundle ν := ⟨f.normalRiemannianMetric hn⟩
    ∀ u : (x : M) → ν x, Continuous (fun x ↦ TotalSpace.mk' P x (u x)) → (∀ x, ‖u x‖ = 1) →
      ∃ ε > 0, IsBicollar f (fun p : M × ℝ ↦
        f.normalExp hn (TotalSpace.mk' P p.1 ((2 * ε / Real.pi * Real.arctan p.2) • u p.1))) := by
  intro hn ν u hu hu1
  obtain ⟨ε, hε, -, hemb⟩ := exists_isOpenEmbedding_normalExp_comp f hdim hP u hu hu1
  refine ⟨ε, hε, hemb (fun p : M × ℝ ↦ (p.1, 2 * ε / Real.pi * Real.arctan p.2))
    (IsOpenEmbedding.id.prodMap (isOpenEmbedding_mul_arctan hε)) fun p ↦ ?_, fun x ↦ ?_⟩
  · have := Real.pi_pos
    rw [abs_lt]
    constructor
    · have := Real.neg_pi_div_two_lt_arctan p.2
      calc -ε = 2 * ε / Real.pi * (-(Real.pi / 2)) := by field_simp
        _ < 2 * ε / Real.pi * Real.arctan p.2 := by gcongr
    · have := Real.arctan_lt_pi_div_two p.2
      calc 2 * ε / Real.pi * Real.arctan p.2 < 2 * ε / Real.pi * (Real.pi / 2) := by gcongr
        _ = ε := by field_simp
  · simp only [Real.arctan_zero, mul_zero, zero_smul]
    exact f.normalExp_zeroSection hn x

end TauCeti.SmoothEmbedding

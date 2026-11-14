/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Unbundled.MulRingSeminorm

/-!
# The Gel'fand spectrum of a seminormed ring and Berkovich's spectral formula

The *Gel'fand spectrum* (or *Berkovich spectrum*) `TauCeti.GelfandSpectrum A` of a seminormed ring
`A` is the type of multiplicative ring seminorms `α : MulRingSeminorm A` bounded by a positive
constant multiple of the ambient norm (`∃ C > 0, ∀ x, α x ≤ C * ‖x‖`), equipped with the topology
of pointwise convergence induced from `A → ℝ`.

Because `α (x ^ n) = α x ^ n`, any bound `α x ≤ C * ‖x‖` forces contractivity `α x ≤ ‖x‖` in the
limit `n → ∞` (`GelfandSpectrum.apply_le_norm`), and over a commutative ring it sharpens to
`α x ≤ smoothingFun (normRingSeminorm A) x` (`GelfandSpectrum.apply_le_smoothingFun`). Thus the
image of `GelfandSpectrum A` in `A → ℝ` is cut out inside the Tychonoff box `Set.Icc 0 (‖·‖)` by
closed pointwise algebraic relations and inequalities, making `GelfandSpectrum A` a compact
Hausdorff space (`GelfandSpectrum.instCompactSpace`, `GelfandSpectrum.instT2Space`).

Over a commutative seminormed ring, combining `RingSeminorm.smoothing` with
Bosch–Güntzer–Remmert Theorem 1.3.2/2 (`RingSeminorm.exists_mulRingSeminorm_le_and_apply_eq`) yields
**Berkovich's spectral formula** (`GelfandSpectrum.smoothingFun_eq_sSup`): for every `x : A`,
`smoothingFun (normRingSeminorm A) x` is the supremum of `α x` over `α : GelfandSpectrum A`, and
when `normRingSeminorm A ≠ 0` (in particular on every nontrivial normed commutative ring) the
spectrum is nonempty and the maximum is attained at a point of `GelfandSpectrum A`.

Bounded ring homomorphisms `φ : A →+* B` act contravariantly on Gel'fand spectra by continuous
pullback (`GelfandSpectrum.comap`, `GelfandSpectrum.continuous_comap`), and retractions whose error
is pointwise nilpotent induce homeomorphisms of spectra (`GelfandSpectrum.retractHomeomorph`). When
the ambient norm is itself multiplicative and normalized (`[NormMulClass A] [NormOneClass A]`), it
defines the top point `GelfandSpectrum.normPoint A`; on any `NormedDivisionRing` it is the unique
point of the spectrum (`GelfandSpectrum.instUnique`).

## Main definitions

* `TauCeti.GelfandSpectrum A`: bounded multiplicative ring seminorms on `A`, with pointwise
  topology and analytic specialization order `α ≤ β ↔ ∀ x, α x ≤ β x`.
* `TauCeti.GelfandSpectrum.ofLeNorm`: construct a spectrum point from `∀ x, α x ≤ ‖x‖`.
* `TauCeti.GelfandSpectrum.comap`: contravariant pullback along a bounded ring homomorphism.
* `TauCeti.GelfandSpectrum.retractHomeomorph`: homeomorphism
  `GelfandSpectrum B ≃ₜ GelfandSpectrum A` for a bounded retraction modulo nilpotents.
* `TauCeti.GelfandSpectrum.normPoint`: the ambient norm as the top point of `GelfandSpectrum A`
  when `[NormMulClass A] [NormOneClass A]`.

## Main results

* `TauCeti.GelfandSpectrum.apply_le_norm`, `TauCeti.GelfandSpectrum.exists_le_mul_norm_iff`:
  every bounded multiplicative seminorm is contractive (`α x ≤ ‖x‖`).
* `TauCeti.GelfandSpectrum.isClosedEmbedding_coeFn`, `TauCeti.GelfandSpectrum.instT2Space`,
  `TauCeti.GelfandSpectrum.instCompactSpace`: `GelfandSpectrum A` embeds as a closed subset of
  `A → ℝ` and is compact Hausdorff.
* `TauCeti.GelfandSpectrum.smoothingFun_eq_sSup`,
  `TauCeti.GelfandSpectrum.exists_apply_eq_smoothingFun`,
  `TauCeti.GelfandSpectrum.isGreatest_range_eval`: Berkovich's formula for the spectral seminorm.
* `TauCeti.GelfandSpectrum.instNonempty`, `TauCeti.GelfandSpectrum.compactSpace_nonempty`:
  nonemptiness on nontrivial normed commutative rings.
* `TauCeti.GelfandSpectrum.apply_eq_norm`, `TauCeti.GelfandSpectrum.instUnique`: the Gel'fand
  spectrum of a normed division ring is a singleton consisting of the norm.

## References

* V. G. Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*,
  Mathematical Surveys and Monographs 33, AMS, 1990, §1.2 (Theorem 1.2.1) and §1.3 (Theorem 1.3.1).
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.3 (Definition 2.3.2, Theorem 2.3.4, Theorem 2.3.10, Remark 2.3.11(b)).
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §1.3.2, Theorem 2.
-/

public section

open Filter Topology

namespace TauCeti

/-- The **Gel'fand spectrum** (or **Berkovich spectrum**) `M(A)` of a seminormed ring `A`: the
multiplicative ring seminorms on `A` bounded by a positive constant multiple of the norm, equipped
with the topology of pointwise convergence. Every such seminorm is contractive
(`GelfandSpectrum.apply_le_norm`). -/
structure GelfandSpectrum (A : Type*) [SeminormedRing A] where
  /-- The underlying multiplicative ring seminorm. -/
  toMulRingSeminorm : MulRingSeminorm A
  /-- The multiplicative seminorm is bounded by a positive constant multiple of the norm. -/
  bound' : ∃ C > 0, ∀ x, toMulRingSeminorm x ≤ C * ‖x‖

namespace GelfandSpectrum

section SeminormedRing

variable {A B C : Type*} [SeminormedRing A] [SeminormedRing B] [SeminormedRing C]

instance instFunLike : FunLike (GelfandSpectrum A) A ℝ where
  coe α := ⇑α.toMulRingSeminorm
  coe_injective α β h := by
    cases α
    cases β
    congr
    exact DFunLike.coe_injective h

instance instMulRingSeminormClass : MulRingSeminormClass (GelfandSpectrum A) A ℝ where
  map_zero α := map_zero α.toMulRingSeminorm
  map_one α := map_one α.toMulRingSeminorm
  map_add_le_add α := map_add_le_add α.toMulRingSeminorm
  map_mul α := map_mul α.toMulRingSeminorm
  map_neg_eq_map α := map_neg_eq_map α.toMulRingSeminorm

/-- Coercing `α.toMulRingSeminorm` to a function gives `α`. -/
@[simp]
theorem coe_toMulRingSeminorm (α : GelfandSpectrum A) :
    ⇑α.toMulRingSeminorm = α :=
  (rfl)

/-- Evaluating `α.toMulRingSeminorm` agrees with `α`. -/
@[simp]
theorem toMulRingSeminorm_apply (α : GelfandSpectrum A) (x : A) :
    α.toMulRingSeminorm x = α x :=
  (rfl)

/-- The forgetful map to `MulRingSeminorm A` is injective. -/
theorem toMulRingSeminorm_injective :
    Function.Injective (toMulRingSeminorm : GelfandSpectrum A → MulRingSeminorm A) :=
  fun α β h ↦ by cases α; cases β; cases h; rfl

/-- Evaluating a constructed spectrum point applies the underlying seminorm. -/
@[simp]
theorem mk_apply (α : MulRingSeminorm A) (h : ∃ C > 0, ∀ x, α x ≤ C * ‖x‖) (x : A) :
    (⟨α, h⟩ : GelfandSpectrum A) x = α x :=
  (rfl)

/-- Two points of `GelfandSpectrum A` are equal iff they agree on every element of `A`. -/
@[ext]
theorem ext {α β : GelfandSpectrum A} (h : ∀ x, α x = β x) : α = β :=
  DFunLike.ext α β h

/-- Every point of `GelfandSpectrum A` is bounded by a positive multiple of the norm. -/
theorem bound (α : GelfandSpectrum A) : ∃ C > 0, ∀ x, α x ≤ C * ‖x‖ :=
  α.bound'

/-- **Contractivity of spectrum points.** Every `α : GelfandSpectrum A` satisfies `α x ≤ ‖x‖` for
all `x : A`, because `α (x ^ n) = α x ^ n` absorbs multiplicative constants as `n → ∞`. -/
theorem apply_le_norm (α : GelfandSpectrum A) (x : A) : α x ≤ ‖x‖ := by
  obtain ⟨C, -, hC⟩ := α.bound'
  exact α.toMulRingSeminorm.le_of_le_mul (μ := normRingSeminorm A) hC x

/-- Construct a point of `GelfandSpectrum A` from a contractive multiplicative ring seminorm. -/
def ofLeNorm (α : MulRingSeminorm A) (h : ∀ x, α x ≤ ‖x‖) : GelfandSpectrum A :=
  ⟨α, 1, zero_lt_one, fun x ↦ by simpa only [one_mul] using h x⟩

/-- Evaluating `ofLeNorm α h` applies `α`. -/
@[simp]
theorem ofLeNorm_apply (α : MulRingSeminorm A) (h : ∀ x, α x ≤ ‖x‖) (x : A) :
    ofLeNorm α h x = α x :=
  (rfl)

/-- `ofLeNorm` recovers the given `MulRingSeminorm`. -/
@[simp]
theorem toMulRingSeminorm_ofLeNorm (α : MulRingSeminorm A) (h : ∀ x, α x ≤ ‖x‖) :
    (ofLeNorm α h).toMulRingSeminorm = α :=
  (rfl)

/-- A multiplicative ring seminorm is bounded by some positive multiple of the norm if and only if
it is bounded by the norm itself. -/
theorem exists_le_mul_norm_iff {α : MulRingSeminorm A} :
    (∃ C > 0, ∀ x, α x ≤ C * ‖x‖) ↔ ∀ x, α x ≤ ‖x‖ :=
  ⟨fun h x ↦ (⟨α, h⟩ : GelfandSpectrum A).apply_le_norm x,
    fun h ↦ ⟨1, zero_lt_one, fun x ↦ by simpa only [one_mul] using h x⟩⟩

/-- Every point of `GelfandSpectrum A` is `1`-Lipschitz on `A`: `|α x - α y| ≤ ‖x - y‖`. -/
theorem abs_apply_sub_le_norm_sub (α : GelfandSpectrum A) (x y : A) :
    |α x - α y| ≤ ‖x - y‖ :=
  (abs_sub_map_le_sub α x y).trans (α.apply_le_norm (x - y))

/-- Every point of `GelfandSpectrum A` is continuous as a map `A → ℝ`. -/
@[continuity, fun_prop]
theorem continuous_apply_self (α : GelfandSpectrum A) : Continuous (α : A → ℝ) :=
  Metric.continuous_iff.2 fun x ε hε ↦ ⟨ε, hε, fun y hy ↦ by
    rw [Real.dist_eq]
    exact (α.abs_apply_sub_le_norm_sub y x).trans_lt (by rwa [← dist_eq_norm])⟩

/-- The analytic specialization order on `GelfandSpectrum A`, given by pointwise comparison. -/
instance instPartialOrder : PartialOrder (GelfandSpectrum A) :=
  PartialOrder.lift (⇑·) DFunLike.coe_injective

/-- Pointwise characterization of the order on `GelfandSpectrum A`. -/
@[simp]
theorem le_def {α β : GelfandSpectrum A} : α ≤ β ↔ ∀ x, α x ≤ β x :=
  Iff.rfl

/-- If `GelfandSpectrum A` is nonempty, then `A` is nontrivial. -/
theorem nontrivial_of_nonempty [h : Nonempty (GelfandSpectrum A)] : Nontrivial A :=
  let ⟨α⟩ := h
  α.toMulRingSeminorm.nontrivial

/-- The Gel'fand spectrum of a subsingleton ring is empty, since `α 1 = 1 ≠ 0 = α 0`. -/
instance instIsEmpty [Subsingleton A] : IsEmpty (GelfandSpectrum A) :=
  ⟨fun α ↦ by
    have := α.toMulRingSeminorm.nontrivial
    exact false_of_nontrivial_of_subsingleton A⟩

/-- If `‖(1 : A)‖ = 0`, then `GelfandSpectrum A` is empty. -/
theorem isEmpty_of_norm_one_eq_zero (h : ‖(1 : A)‖ = 0) : IsEmpty (GelfandSpectrum A) :=
  ⟨fun α ↦ by linarith [α.apply_le_norm 1, map_one α]⟩

/-- Every point of `GelfandSpectrum A` vanishes on nilpotent elements. -/
theorem eq_zero_of_isNilpotent (α : GelfandSpectrum A) {x : A} (hx : IsNilpotent x) : α x = 0 :=
  α.toMulRingSeminorm.eq_zero_of_isNilpotent hx

/-- Adding a nilpotent element leaves every point of `GelfandSpectrum A` unchanged. -/
theorem map_add_eq_left_of_isNilpotent (α : GelfandSpectrum A) (x : A) {y : A}
    (hy : IsNilpotent y) : α (x + y) = α x :=
  α.toMulRingSeminorm.map_add_eq_left_of_map_eq_zero x (α.eq_zero_of_isNilpotent hy)

/-! ### Pointwise topology and compactness -/

/-- The topology of pointwise convergence on `GelfandSpectrum A`, induced from `A → ℝ`. -/
instance instTopologicalSpace : TopologicalSpace (GelfandSpectrum A) :=
  TopologicalSpace.induced (⇑· : GelfandSpectrum A → A → ℝ) inferInstance

/-- Function coercion `GelfandSpectrum A → (A → ℝ)` is a topological inducing map. -/
theorem isInducing_coeFn : Topology.IsInducing (⇑· : GelfandSpectrum A → A → ℝ) :=
  ⟨rfl⟩

/-- Function coercion `GelfandSpectrum A → (A → ℝ)` is a topological embedding. -/
theorem isEmbedding_coeFn : Topology.IsEmbedding (⇑· : GelfandSpectrum A → A → ℝ) :=
  ⟨isInducing_coeFn, DFunLike.coe_injective⟩

/-- Evaluation at any element `x : A` is continuous on `GelfandSpectrum A`. -/
@[continuity, fun_prop]
theorem continuous_eval (x : A) : Continuous (fun α : GelfandSpectrum A ↦ α x) :=
  (continuous_apply x).comp isInducing_coeFn.continuous

/-- A map into `GelfandSpectrum A` is continuous iff all its pointwise evaluations are
continuous. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → GelfandSpectrum A} :
    Continuous f ↔ ∀ x : A, Continuous (fun t ↦ f t x) := by
  rw [isInducing_coeFn.continuous_iff, continuous_pi_iff]
  rfl

/-- Explicit description of the image of `GelfandSpectrum A` inside `A → ℝ`. -/
theorem range_coeFn :
    Set.range (⇑· : GelfandSpectrum A → A → ℝ) =
      {f : A → ℝ | f 0 = 0 ∧ f 1 = 1 ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f (-x) = f x) ∧
        (∀ x y, f (x + y) ≤ f x + f y) ∧ (∀ x y, f (x * y) = f x * f y) ∧ ∀ x, f x ≤ ‖x‖} := by
  ext f
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨α, rfl⟩
    exact ⟨map_zero α, map_one α, apply_nonneg α, map_neg_eq_map α, map_add_le_add α,
      map_mul α, α.apply_le_norm⟩
  · rintro ⟨hf0, hf1, _, hfneg, hfadd, hfmul, hfle⟩
    refine ⟨ofLeNorm
      { toFun := f
        map_zero' := hf0
        add_le' := hfadd
        neg' := hfneg
        map_one' := hf1
        map_mul' := hfmul } hfle, rfl⟩

/-- The image of `GelfandSpectrum A` in `A → ℝ` is closed for the product topology. -/
theorem isClosed_range_coeFn : IsClosed (Set.range (⇑· : GelfandSpectrum A → A → ℝ)) := by
  rw [range_coeFn]
  have h0 : IsClosed {f : A → ℝ | f 0 = 0} := isClosed_eq (continuous_apply 0) continuous_const
  have h1 : IsClosed {f : A → ℝ | f 1 = 1} := isClosed_eq (continuous_apply 1) continuous_const
  have hnn : IsClosed {f : A → ℝ | ∀ x, 0 ≤ f x} := by
    simpa only [Set.ofPred_forall] using
      isClosed_iInter fun x ↦ isClosed_le continuous_const (continuous_apply x)
  have hneg : IsClosed {f : A → ℝ | ∀ x, f (-x) = f x} := by
    simpa only [Set.ofPred_forall] using
      isClosed_iInter fun x ↦ isClosed_eq (continuous_apply (-x)) (continuous_apply x)
  have hadd : IsClosed {f : A → ℝ | ∀ x y, f (x + y) ≤ f x + f y} := by
    simpa only [Set.ofPred_forall] using isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
      isClosed_le (continuous_apply (x + y)) ((continuous_apply x).add (continuous_apply y))
  have hmul : IsClosed {f : A → ℝ | ∀ x y, f (x * y) = f x * f y} := by
    simpa only [Set.ofPred_forall] using isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
      isClosed_eq (continuous_apply (x * y)) ((continuous_apply x).mul (continuous_apply y))
  have hle : IsClosed {f : A → ℝ | ∀ x, f x ≤ ‖x‖} := by
    simpa only [Set.ofPred_forall] using
      isClosed_iInter fun x ↦ isClosed_le (continuous_apply x) continuous_const
  exact h0.inter <| h1.inter <| hnn.inter <| hneg.inter <| hadd.inter <| hmul.inter hle

/-- Function coercion embeds `GelfandSpectrum A` as a closed subset of `A → ℝ`. -/
theorem isClosedEmbedding_coeFn : Topology.IsClosedEmbedding (⇑· : GelfandSpectrum A → A → ℝ) :=
  ⟨isEmbedding_coeFn, isClosed_range_coeFn⟩

/-- `GelfandSpectrum A` is Hausdorff. -/
instance instT2Space : T2Space (GelfandSpectrum A) :=
  isEmbedding_coeFn.t2Space

/-- **Compactness of the Gel'fand spectrum** (Berkovich Theorem 1.2.1; Kedlaya–Liu Theorem 2.3.4).
`GelfandSpectrum A` embeds as a closed subset of the compact Tychonoff box `Set.Icc 0 (‖·‖)` in
`A → ℝ`. -/
instance instCompactSpace : CompactSpace (GelfandSpectrum A) := by
  rw [← isCompact_univ_iff, isEmbedding_coeFn.isCompact_iff, Set.image_univ]
  refine (isCompact_Icc (a := (0 : A → ℝ)) (b := fun x : A ↦ ‖x‖)).of_isClosed_subset
    isClosed_range_coeFn ?_
  rintro _ ⟨α, rfl⟩
  exact ⟨fun x ↦ apply_nonneg α x, α.apply_le_norm⟩

/-! ### Contravariant functoriality -/

/-- Contravariant pullback of Gel'fand spectra along a bounded ring homomorphism `φ : A →+* B`. -/
def comap (φ : A →+* B) (hφ : ∃ C > 0, ∀ x, ‖φ x‖ ≤ C * ‖x‖)
    (β : GelfandSpectrum B) : GelfandSpectrum A :=
  ⟨β.toMulRingSeminorm.comp φ,
    let ⟨C, hC0, hC⟩ := hφ
    ⟨C, hC0, fun x ↦ by
      rw [MulRingSeminorm.comp_apply, toMulRingSeminorm_apply]
      exact (β.apply_le_norm (φ x)).trans (hC x)⟩⟩

/-- Evaluating `comap φ hφ β` at `x` evaluates `β` at `φ x`. -/
@[simp]
theorem comap_apply (φ : A →+* B) (hφ : ∃ C > 0, ∀ x, ‖φ x‖ ≤ C * ‖x‖)
    (β : GelfandSpectrum B) (x : A) :
    comap φ hφ β x = β (φ x) :=
  MulRingSeminorm.comp_apply β.toMulRingSeminorm φ x

/-- The underlying `MulRingSeminorm` of `comap φ hφ β` is `β.toMulRingSeminorm.comp φ`. -/
@[simp]
theorem toMulRingSeminorm_comap (φ : A →+* B) (hφ : ∃ C > 0, ∀ x, ‖φ x‖ ≤ C * ‖x‖)
    (β : GelfandSpectrum B) :
    (comap φ hφ β).toMulRingSeminorm = β.toMulRingSeminorm.comp φ :=
  (rfl)

/-- `comap φ hφ` is continuous for the pointwise convergence topologies. -/
@[continuity, fun_prop]
theorem continuous_comap (φ : A →+* B) (hφ : ∃ C > 0, ∀ x, ‖φ x‖ ≤ C * ‖x‖) :
    Continuous (comap φ hφ) :=
  continuous_iff.2 fun x ↦ by simpa only [comap_apply] using continuous_eval (φ x)

/-- Pullback along the identity ring homomorphism is the identity on `GelfandSpectrum A`. -/
@[simp]
theorem comap_id (h : ∃ C > 0, ∀ x : A, ‖x‖ ≤ C * ‖x‖) (α : GelfandSpectrum A) :
    comap (RingHom.id A) h α = α :=
  ext fun _ ↦ by simp

/-- Pullback of Gel'fand spectra is contravariant under composition of bounded ring homomorphisms:
pulling back along `ψ.comp φ` first pulls back along `ψ`, then along `φ`. -/
theorem comap_comp (ψ : B →+* C) (hψ : ∃ C₁ > 0, ∀ y, ‖ψ y‖ ≤ C₁ * ‖y‖)
    (φ : A →+* B) (hφ : ∃ C₂ > 0, ∀ x, ‖φ x‖ ≤ C₂ * ‖x‖)
    (hψφ : ∃ C₃ > 0, ∀ x, ‖(ψ.comp φ) x‖ ≤ C₃ * ‖x‖) (γ : GelfandSpectrum C) :
    comap φ hφ (comap ψ hψ γ) = comap (ψ.comp φ) hψφ γ :=
  ext fun _ ↦ by simp

/-- If `φ : A →+* B` and `ψ : B →+* A` are bounded ring homomorphisms with `ψ ∘ φ = id` such that
`y - φ (ψ y)` is nilpotent for every `y : B`, then `comap φ` and `comap ψ` form a homeomorphism
`GelfandSpectrum B ≃ₜ GelfandSpectrum A`. -/
def retractHomeomorph (φ : A →+* B) (hφ : ∃ C₁ > 0, ∀ x, ‖φ x‖ ≤ C₁ * ‖x‖)
    (ψ : B →+* A) (hψ : ∃ C₂ > 0, ∀ y, ‖ψ y‖ ≤ C₂ * ‖y‖)
    (hψφ : ∀ x : A, ψ (φ x) = x) (hnil : ∀ y : B, IsNilpotent (y - φ (ψ y))) :
    GelfandSpectrum B ≃ₜ GelfandSpectrum A where
  toFun := comap φ hφ
  invFun := comap ψ hψ
  left_inv β := ext fun y ↦ by
    simp only [comap_apply]
    conv_rhs => rw [(add_sub_cancel (φ (ψ y)) y).symm]
    exact (β.map_add_eq_left_of_isNilpotent (φ (ψ y)) (hnil y)).symm
  right_inv α := ext fun x ↦ by simp [hψφ x]
  continuous_toFun := continuous_comap φ hφ
  continuous_invFun := continuous_comap ψ hψ

/-- Applying `retractHomeomorph` pulls back along `φ`. -/
@[simp]
theorem retractHomeomorph_apply (φ : A →+* B) (hφ : ∃ C₁ > 0, ∀ x, ‖φ x‖ ≤ C₁ * ‖x‖)
    (ψ : B →+* A) (hψ : ∃ C₂ > 0, ∀ y, ‖ψ y‖ ≤ C₂ * ‖y‖)
    (hψφ : ∀ x : A, ψ (φ x) = x) (hnil : ∀ y : B, IsNilpotent (y - φ (ψ y)))
    (β : GelfandSpectrum B) (x : A) :
    retractHomeomorph φ hφ ψ hψ hψφ hnil β x = β (φ x) :=
  comap_apply φ hφ β x

/-- Applying `(retractHomeomorph ...).symm` pulls back along `ψ`. -/
@[simp]
theorem retractHomeomorph_symm_apply (φ : A →+* B) (hφ : ∃ C₁ > 0, ∀ x, ‖φ x‖ ≤ C₁ * ‖x‖)
    (ψ : B →+* A) (hψ : ∃ C₂ > 0, ∀ y, ‖ψ y‖ ≤ C₂ * ‖y‖)
    (hψφ : ∀ x : A, ψ (φ x) = x) (hnil : ∀ y : B, IsNilpotent (y - φ (ψ y)))
    (α : GelfandSpectrum A) (y : B) :
    (retractHomeomorph φ hφ ψ hψ hψφ hnil).symm α y = α (ψ y) :=
  comap_apply ψ hψ α y

/-! ### Multiplicative ambient norms and division rings -/

section NormMulClass

variable [NormMulClass A] [NormOneClass A]

/-- When the ambient seminorm on `A` is multiplicative and normalized (`‖1‖ = 1`), the seminorm
itself is a point of `GelfandSpectrum A`. -/
def normPoint (A : Type*) [SeminormedRing A] [NormMulClass A] [NormOneClass A] :
    GelfandSpectrum A :=
  ofLeNorm
    { toFun := norm
      map_zero' := norm_zero
      add_le' := norm_add_le
      neg' := norm_neg
      map_one' := norm_one
      map_mul' := norm_mul }
    (fun _ ↦ le_rfl)

/-- `normPoint A` evaluates to the ambient norm. -/
@[simp]
theorem normPoint_apply (x : A) : normPoint A x = ‖x‖ :=
  (rfl)

/-- When the ambient norm is multiplicative and normalized, `normPoint A` is the greatest element
of `GelfandSpectrum A`. -/
instance instOrderTop : OrderTop (GelfandSpectrum A) where
  top := normPoint A
  le_top α := le_def.2 fun x ↦ by
    rw [normPoint_apply]
    exact α.apply_le_norm x

/-- The top element of `GelfandSpectrum A` is `normPoint A`. -/
@[simp]
theorem top_eq_normPoint : (⊤ : GelfandSpectrum A) = normPoint A :=
  (rfl)

/-- Every point of `GelfandSpectrum A` is bounded above by `normPoint A`. -/
theorem le_normPoint (α : GelfandSpectrum A) : α ≤ normPoint A :=
  top_eq_normPoint (A := A) ▸ le_top

/-- When the ambient norm is multiplicative and normalized, `normPoint A` attains the maximum of
`α x` over `GelfandSpectrum A` for every `x : A` simultaneously. -/
theorem isGreatest_range_eval_of_normMulClass (x : A) :
    IsGreatest (Set.range fun α : GelfandSpectrum A ↦ α x) ‖x‖ :=
  ⟨⟨normPoint A, normPoint_apply x⟩, by rintro _ ⟨α, rfl⟩; exact α.apply_le_norm x⟩

/-- When the ambient norm is multiplicative and normalized, the supremum over `GelfandSpectrum A`
at `x` equals `‖x‖`. -/
theorem sSup_range_eval_of_normMulClass (x : A) :
    sSup (Set.range fun α : GelfandSpectrum A ↦ α x) = ‖x‖ :=
  (isGreatest_range_eval_of_normMulClass x).csSup_eq

end NormMulClass

end SeminormedRing

section NormedDivisionRing

variable {K : Type*} [NormedDivisionRing K]

/-- On a normed division ring `K`, every point of `GelfandSpectrum K` coincides with the norm:
for `x ≠ 0`, `α x ≤ ‖x‖` and `(α x)⁻¹ = α x⁻¹ ≤ ‖x⁻¹‖ = ‖x‖⁻¹`. -/
@[simp]
theorem apply_eq_norm (α : GelfandSpectrum K) (x : K) : α x = ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · refine le_antisymm (α.apply_le_norm x) ?_
    have hmul : α x * α x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hx, map_one]
    have hinv : α x⁻¹ ≤ ‖x‖⁻¹ := (α.apply_le_norm x⁻¹).trans_eq (norm_inv x)
    have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hle : 1 ≤ α x * ‖x‖⁻¹ :=
      hmul.symm.trans_le (mul_le_mul_of_nonneg_left hinv (apply_nonneg α x))
    simpa only [one_mul] using (le_mul_inv_iff₀ hpos).1 hle

/-- The Gel'fand spectrum of a normed division ring has a unique point, the ambient norm. -/
instance instUnique : Unique (GelfandSpectrum K) where
  default := normPoint K
  uniq α := ext fun x ↦ (apply_eq_norm α x).trans (normPoint_apply x).symm

/-- The default point of `GelfandSpectrum K` is `normPoint K`. -/
@[simp]
theorem default_eq_normPoint : (default : GelfandSpectrum K) = normPoint K :=
  (rfl)

/-- Every point of `GelfandSpectrum K` equals `normPoint K`. -/
theorem eq_normPoint (α : GelfandSpectrum K) : α = normPoint K :=
  (Unique.eq_default α).trans default_eq_normPoint

end NormedDivisionRing

/-! ### Berkovich's spectral formula and nonemptiness -/

section SeminormedCommRing

variable {A : Type*} [SeminormedCommRing A]

/-- Over a commutative seminormed ring, every `α : GelfandSpectrum A` is bounded above by the
spectral seminorm `smoothingFun (normRingSeminorm A)`. -/
theorem apply_le_smoothingFun (α : GelfandSpectrum A) (x : A) :
    α x ≤ smoothingFun (normRingSeminorm A) x := by
  obtain ⟨C, -, hC⟩ := α.bound'
  exact α.toMulRingSeminorm.le_smoothingFun_of_le_mul (μ := normRingSeminorm A) hC x

/-- If the ambient seminorm on a commutative ring is not identically zero, then for every `x : A`
there exists a point `α : GelfandSpectrum A` attaining `smoothingFun (normRingSeminorm A) x`. -/
theorem exists_apply_eq_smoothingFun_of_norm_ne_zero (h : normRingSeminorm A ≠ 0) (x : A) :
    ∃ α : GelfandSpectrum A, α x = smoothingFun (normRingSeminorm A) x := by
  have hsm : (normRingSeminorm A).smoothing ≠ 0 :=
    RingSeminorm.smoothing_eq_zero_iff.not.2 h
  obtain ⟨α₀, hα₀, hα₀x⟩ :=
    RingSeminorm.exists_mulRingSeminorm_le_and_apply_eq
      (normRingSeminorm A).isPowMul_smoothing hsm x
  exact ⟨ofLeNorm α₀ fun y ↦ (hα₀ y).trans ((normRingSeminorm A).smoothing_le_self y),
    hα₀x.trans ((normRingSeminorm A).smoothing_apply x)⟩

/-- Over a commutative seminormed ring, `GelfandSpectrum A` is nonempty if and only if
`‖(1 : A)‖ ≠ 0`. -/
theorem nonempty_iff_norm_one_ne_zero :
    Nonempty (GelfandSpectrum A) ↔ ‖(1 : A)‖ ≠ 0 := by
  refine ⟨fun ⟨α⟩ h1 ↦ (isEmpty_of_norm_one_eq_zero h1).false α, fun h1 ↦ ?_⟩
  have hne : normRingSeminorm A ≠ 0 := RingSeminorm.ne_zero_iff.2 ⟨1, show ‖(1 : A)‖ ≠ 0 from h1⟩
  obtain ⟨α, -⟩ := exists_apply_eq_smoothingFun_of_norm_ne_zero hne 1
  exact ⟨α⟩

/-- **Berkovich's spectral formula** (Berkovich Theorem 1.3.1; Kedlaya–Liu Theorem 2.3.10 and
Remark 2.3.11(b)). For every commutative seminormed ring `A` and every `x : A`, the spectral
seminorm `smoothingFun (normRingSeminorm A) x` equals the supremum of `α x` over
`α : GelfandSpectrum A` (including when `GelfandSpectrum A` is empty, where both sides are `0`). -/
theorem smoothingFun_eq_sSup (x : A) :
    smoothingFun (normRingSeminorm A) x = sSup (Set.range fun α : GelfandSpectrum A ↦ α x) := by
  rw [← (normRingSeminorm A).smoothing_apply,
    (normRingSeminorm A).smoothing_eq_sSup_mulRingSeminorm x]
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  refine ⟨?_, ?_⟩
  · rintro ⟨α₀, hα₀, rfl⟩
    exact ⟨ofLeNorm α₀ hα₀, rfl⟩
  · rintro ⟨α, rfl⟩
    exact ⟨α.toMulRingSeminorm, α.apply_le_norm, rfl⟩

end SeminormedCommRing

section NormedCommRing

variable {A : Type*} [NormedCommRing A]

/-- **Nonemptiness of the Gel'fand spectrum** (Berkovich Theorem 1.2.1(i); Kedlaya–Liu
Theorem 2.3.4): every nontrivial normed commutative ring has a nonempty Gel'fand spectrum. -/
instance instNonempty [Nontrivial A] : Nonempty (GelfandSpectrum A) :=
  nonempty_iff_norm_one_ne_zero.2 (norm_ne_zero_iff.2 one_ne_zero)

/-- Over a normed commutative ring, `GelfandSpectrum A` is nonempty if and only if `A` is
nontrivial. -/
theorem nonempty_iff_nontrivial : Nonempty (GelfandSpectrum A) ↔ Nontrivial A :=
  ⟨fun _ ↦ nontrivial_of_nonempty, fun _ ↦ inferInstance⟩

/-- `GelfandSpectrum A` is compact, and nonempty whenever `A` is nontrivial
(Berkovich Theorem 1.2.1; Kedlaya–Liu Theorem 2.3.4). -/
theorem compactSpace_nonempty :
    CompactSpace (GelfandSpectrum A) ∧ (Nontrivial A → Nonempty (GelfandSpectrum A)) :=
  ⟨inferInstance, fun _ ↦ inferInstance⟩

/-- On a nontrivial normed commutative ring, every `x : A` attains its spectral seminorm at some
point of `GelfandSpectrum A` (Berkovich Theorem 1.3.1; Kedlaya–Liu Theorem 2.3.10). -/
theorem exists_apply_eq_smoothingFun [Nontrivial A] (x : A) :
    ∃ α : GelfandSpectrum A, α x = smoothingFun (normRingSeminorm A) x :=
  exists_apply_eq_smoothingFun_of_norm_ne_zero
    (RingSeminorm.ne_zero_iff.2 ⟨1, show ‖(1 : A)‖ ≠ 0 from norm_ne_zero_iff.2 one_ne_zero⟩) x

/-- On a nontrivial normed commutative ring, `smoothingFun (normRingSeminorm A) x` is the greatest
element of `{α x | α : GelfandSpectrum A}`. -/
theorem isGreatest_range_eval [Nontrivial A] (x : A) :
    IsGreatest (Set.range fun α : GelfandSpectrum A ↦ α x)
      (smoothingFun (normRingSeminorm A) x) := by
  obtain ⟨α, hα⟩ := exists_apply_eq_smoothingFun x
  exact ⟨⟨α, hα⟩, by rintro _ ⟨β, rfl⟩; exact β.apply_le_smoothingFun x⟩

end NormedCommRing

end GelfandSpectrum

end TauCeti

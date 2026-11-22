/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.IsBounded
public import TauCeti.Analysis.Normed.Unbundled.MulRingSeminorm
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order.Compact
public import TauCeti.Analysis.Normed.Ring.Completion

/-!
# The Berkovich spectrum of a seminormed ring

For a seminormed ring `A`, the Berkovich spectrum `M(A)` (`TauCeti.BerkovichSpectrum A`) is the
set of multiplicative seminorms `x` on `A` dominated by the norm, `x a ≤ ‖a‖` for every `a`, with
the topology of pointwise convergence. Points are actual real-valued seminorms, not equivalence
classes, and neither completeness, a base field, nor a multiplicative or nonarchimedean norm is
assumed. The norm is part of the data: `ℤ` with its usual norm and with its trivial norm have the
same discrete topology but different spectra.

This is the spectrum `M(A)` of Berkovich's book, called `Spectrum` in the
TropicalAndBerkovichArithmetic roadmap. It is not the spectrum of continuous nonarchimedean
seminorms normalized to take the value `1/2` at a topologically nilpotent unit `ϖ`, which
DiamondsAndVStacks §D5.13 also suggests calling `BerkovichSpectrum R ϖ`; that normalized spectrum
needs a different Lean name, such as `NormalizedBerkovichSpectrum`.

A point `x` is coerced to a function `A → ℝ` and is an instance of `MulRingSeminormClass`, so
`map_one`, `map_mul`, `map_zero`, `map_neg_eq_map`, `map_add_le_add` and `apply_nonneg` apply to
it directly.

## Main definitions and results

* `TauCeti.BerkovichSpectrum A`: the norm-dominated multiplicative seminorms on `A`.
* `TauCeti.BerkovichSpectrum.ofIsBoundedWrt`: a multiplicative seminorm bounded by a constant
  multiple of the norm is a point; by the power trick
  (`RingHom.isBoundedWrt_norm_iff`) the bounded points of Berkovich's definition are exactly
  the dominated ones.
* `TauCeti.BerkovichSpectrum.isEmbedding_coe`: evaluation embeds `M(A)` into `A → ℝ`, and
  `TauCeti.BerkovichSpectrum.range_coe` describes the image by equations and inequalities.
* `TauCeti.BerkovichSpectrum.isClosed_range_coe`: that image is closed.
* `TauCeti.BerkovichSpectrum.instCompactSpace`: `M(A)` is compact, since the image lies in
  `∏ₐ [0, ‖a‖]`. No completeness or nontriviality is assumed; the spectrum of a ring with
  `‖1‖ < 1`, the zero ring for instance, is empty.
* `TauCeti.BerkovichSpectrum.instT2Space`: `M(A)` is Hausdorff.
* `TauCeti.BerkovichSpectrum.comap`: a bounded ring homomorphism `f : A →+* B` induces the
  continuous map `M(B) → M(A)`, `x ↦ x ∘ f`, contravariantly functorially.
* `TauCeti.BerkovichSpectrum.completionHomeomorph`: restriction from the completion `Â` of `A`
  is a homeomorphism `M(Â) ≃ₜ M(A)` that does not change the value at any `a : A`. Its inverse
  extends a point by continuity, which is possible since every point is `1`-Lipschitz
  (`TauCeti.BerkovichSpectrum.lipschitzWith_one`). Statements about the spectra of complete
  normed rings thus transfer to arbitrary seminormed rings.
* `TauCeti.BerkovichSpectrum.normPoint`: the norm of a seminormed ring with multiplicative norm
  and `‖1‖ = 1` is a point, and for a normed division ring it is the only point
  (`TauCeti.BerkovichSpectrum.eq_normPoint`).

## References

* V. G. Berkovich, *Spectral theory and analytic geometry over non-Archimedean fields*,
  Mathematical Surveys and Monographs 33, AMS, 1990, §1.2.
* M. Temkin, *Introduction to Berkovich analytic spaces*, Definition/Exercise 2.1.2.1(i),
  Definition 2.2.2.1(i), Fact 2.2.2.3(i) and Exercise 2.2.2.4(i).
-/

public section

open Set Topology UniformSpace

namespace TauCeti

/-- The Berkovich spectrum `M(A)` of a seminormed ring `A`: the multiplicative seminorms on `A`
that are dominated by the norm of `A`. Its topology, the topology of pointwise convergence, is
`TauCeti.BerkovichSpectrum.instTopologicalSpace`. -/
structure BerkovichSpectrum (A : Type*) [SeminormedRing A] where
  /-- The underlying multiplicative seminorm of a point of the Berkovich spectrum. -/
  toMulRingSeminorm : MulRingSeminorm A
  /-- A point of the Berkovich spectrum is dominated by the norm. -/
  apply_le_norm' : ∀ a, toMulRingSeminorm a ≤ ‖a‖

namespace BerkovichSpectrum

section SeminormedRing

variable {A B C : Type*} [SeminormedRing A] [SeminormedRing B] [SeminormedRing C]

instance : FunLike (BerkovichSpectrum A) A ℝ where
  coe x := x.toMulRingSeminorm
  coe_injective x y h := by
    obtain ⟨p, _⟩ := x
    obtain ⟨q, _⟩ := y
    congr
    exact DFunLike.coe_injective h

instance : MulRingSeminormClass (BerkovichSpectrum A) A ℝ where
  map_zero x := map_zero x.toMulRingSeminorm
  map_one x := map_one x.toMulRingSeminorm
  map_mul x := map_mul x.toMulRingSeminorm
  map_add_le_add x := map_add_le_add x.toMulRingSeminorm
  map_neg_eq_map x := map_neg_eq_map x.toMulRingSeminorm

@[simp]
theorem coe_toMulRingSeminorm (x : BerkovichSpectrum A) : ⇑x.toMulRingSeminorm = ⇑x :=
  (rfl)

@[simp]
theorem coe_mk (p : MulRingSeminorm A) (hp : ∀ a, p a ≤ ‖a‖) :
    ⇑(⟨p, hp⟩ : BerkovichSpectrum A) = ⇑p :=
  (rfl)

/-- Two points of the Berkovich spectrum with the same values are equal. -/
@[ext]
theorem ext {x y : BerkovichSpectrum A} (h : ∀ a, x a = y a) : x = y :=
  DFunLike.ext x y h

theorem toMulRingSeminorm_injective :
    Function.Injective (toMulRingSeminorm : BerkovichSpectrum A → MulRingSeminorm A) :=
  fun x y h => ext fun a => by simp [← coe_toMulRingSeminorm, h]

/-- A point of the Berkovich spectrum is dominated by the norm. -/
theorem apply_le_norm (x : BerkovichSpectrum A) (a : A) : x a ≤ ‖a‖ :=
  x.apply_le_norm' a

/-- A ring with a point in its Berkovich spectrum has `1 ≤ ‖1‖`. -/
theorem one_le_norm_one (x : BerkovichSpectrum A) : 1 ≤ ‖(1 : A)‖ := by
  simpa using x.apply_le_norm 1

/-- A ring whose Berkovich spectrum has a point is nontrivial. -/
theorem nontrivial (x : BerkovichSpectrum A) : Nontrivial A :=
  ⟨⟨1, 0, fun h => by simpa [h] using map_one x⟩⟩

/-- The zero ring has empty Berkovich spectrum. -/
instance [Subsingleton A] : IsEmpty (BerkovichSpectrum A) :=
  ⟨fun x => not_nontrivial A x.nontrivial⟩

/-! ### Bounded points -/

/-- A multiplicative seminorm bounded by a constant multiple of the norm, as a point of the
Berkovich spectrum; it is dominated by the norm itself by the power trick. -/
noncomputable def ofIsBoundedWrt (p : MulRingSeminorm A)
    (hp : (RingHom.id A).IsBoundedWrt norm p) : BerkovichSpectrum A :=
  ⟨p, (RingHom.isBoundedWrt_norm_iff p (RingHom.id A)).mp hp⟩

@[simp]
theorem coe_ofIsBoundedWrt (p : MulRingSeminorm A) (hp : (RingHom.id A).IsBoundedWrt norm p) :
    ⇑(ofIsBoundedWrt p hp) = ⇑p :=
  (rfl)

/-! ### The topology of pointwise convergence -/

/-- The topology of pointwise convergence on the Berkovich spectrum, induced by the evaluation
map `M(A) → (A → ℝ)`. -/
instance instTopologicalSpace : TopologicalSpace (BerkovichSpectrum A) :=
  .induced (fun x : BerkovichSpectrum A => (x : A → ℝ)) inferInstance

/-- Evaluation embeds the Berkovich spectrum into the product space `A → ℝ`. -/
theorem isEmbedding_coe : IsEmbedding (fun x : BerkovichSpectrum A => (x : A → ℝ)) :=
  ⟨⟨rfl⟩, DFunLike.coe_injective⟩

/-- A map into the Berkovich spectrum is continuous exactly when each of its evaluations is. -/
theorem continuous_iff {Z : Type*} [TopologicalSpace Z] {f : Z → BerkovichSpectrum A} :
    Continuous f ↔ ∀ a, Continuous fun z => f z a := by
  rw [isEmbedding_coe.isInducing.continuous_iff, continuous_pi_iff]
  rfl

/-- The evaluation map of the Berkovich spectrum is continuous. -/
@[fun_prop, continuity]
theorem continuous_coe : Continuous (fun x : BerkovichSpectrum A => (x : A → ℝ)) :=
  isEmbedding_coe.continuous

/-- Evaluation at a ring element is continuous on the Berkovich spectrum. -/
@[fun_prop, continuity]
theorem continuous_eval (a : A) : Continuous fun x : BerkovichSpectrum A => x a :=
  (_root_.continuous_apply a).comp continuous_coe

/-- The image of the evaluation map: the functions `v : A → ℝ` with `v 0 = 0`, `v 1 = 1`,
`v (a * b) = v a * v b`, `v (a + b) ≤ v a + v b`, `v (-a) = v a` and `v a ≤ ‖a‖`. -/
theorem range_coe : range (fun x : BerkovichSpectrum A => (x : A → ℝ)) =
    {v | v 0 = 0 ∧ v 1 = 1 ∧ (∀ a b, v (a * b) = v a * v b) ∧
      (∀ a b, v (a + b) ≤ v a + v b) ∧ (∀ a, v (-a) = v a) ∧ ∀ a, v a ≤ ‖a‖} := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨map_zero x, map_one x, map_mul x, map_add_le_add x, map_neg_eq_map x, x.apply_le_norm⟩
  · rintro ⟨h0, h1, hmul, hadd, hneg, hle⟩
    let p : MulRingSeminorm A :=
      { toFun := v
        map_zero' := h0
        add_le' := hadd
        neg' := hneg
        map_one' := h1
        map_mul' := hmul }
    exact ⟨⟨p, hle⟩, rfl⟩

/-- The image of the evaluation map of the Berkovich spectrum is closed in `A → ℝ`. -/
theorem isClosed_range_coe : IsClosed (range (fun x : BerkovichSpectrum A => (x : A → ℝ))) := by
  rw [range_coe]
  simp only [ofPred_and, ofPred_forall]
  refine .inter (isClosed_eq (by fun_prop) (by fun_prop)) <|
    .inter (isClosed_eq (by fun_prop) (by fun_prop)) <|
    .inter (isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_eq (by fun_prop) (by fun_prop)) <|
    .inter (isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_le (by fun_prop) (by fun_prop)) <|
    .inter (isClosed_iInter fun a => isClosed_eq (by fun_prop) (by fun_prop)) <|
    isClosed_iInter fun a => isClosed_le (by fun_prop) (by fun_prop)

/-- The evaluation map of the Berkovich spectrum is a closed embedding. -/
theorem isClosedEmbedding_coe :
    IsClosedEmbedding (fun x : BerkovichSpectrum A => (x : A → ℝ)) :=
  ⟨isEmbedding_coe, isClosed_range_coe⟩

/-- The image of the evaluation map lies in the product `∏ₐ [0, ‖a‖]`. -/
theorem range_coe_subset_pi :
    range (fun x : BerkovichSpectrum A => (x : A → ℝ)) ⊆ univ.pi fun a => Icc 0 ‖a‖ := by
  rintro _ ⟨x, rfl⟩ a -
  exact ⟨apply_nonneg x a, x.apply_le_norm a⟩

/-- The Berkovich spectrum of a seminormed ring is compact. -/
instance instCompactSpace : CompactSpace (BerkovichSpectrum A) :=
  ⟨isEmbedding_coe.isCompact_iff.mpr <| by
    simpa using (isCompact_univ_pi fun a => isCompact_Icc).of_isClosed_subset
      isClosed_range_coe range_coe_subset_pi⟩

/-- The Berkovich spectrum of a seminormed ring is Hausdorff. -/
instance instT2Space : T2Space (BerkovichSpectrum A) :=
  isEmbedding_coe.t2Space

/-! ### Pullback along bounded homomorphisms -/

/-- The continuous map of Berkovich spectra `M(B) → M(A)`, `x ↦ x ∘ f`, induced by a bounded ring
homomorphism `f : A →+* B`. -/
noncomputable def comap (f : A →+* B) (hf : f.IsBounded) :
    C(BerkovichSpectrum B, BerkovichSpectrum A) where
  toFun x := ⟨x.toMulRingSeminorm.comp f, by
    obtain ⟨C, hC, hfC⟩ := hf
    simpa using (RingHom.isBoundedWrt_norm_iff x f).mp
      ⟨C, hC, fun a => (x.apply_le_norm (f a)).trans (hfC a)⟩⟩
  continuous_toFun := continuous_iff.mpr fun a => by simpa using continuous_eval (f a)

@[simp]
theorem comap_apply (f : A →+* B) (hf : f.IsBounded) (x : BerkovichSpectrum B) (a : A) :
    comap f hf x a = x (f a) := by
  simp [comap]

@[simp]
theorem comap_id : comap (RingHom.id A) RingHom.isBounded_id = ContinuousMap.id _ :=
  ContinuousMap.ext fun x => ext fun a => by simp

theorem comap_comp (g : B →+* C) (f : A →+* B) (hg : g.IsBounded) (hf : f.IsBounded) :
    comap (g.comp f) (hg.comp hf) = (comap f hf).comp (comap g hg) :=
  ContinuousMap.ext fun x => ext fun a => by simp

/-! ### Lipschitz continuity and the completion -/

/-- A point of the Berkovich spectrum is `1`-Lipschitz: `|x a - x b| ≤ x (a - b) ≤ ‖a - b‖`. -/
theorem lipschitzWith_one (x : BerkovichSpectrum A) : LipschitzWith 1 x :=
  LipschitzWith.of_dist_le_mul fun a b => by
    simpa [Real.dist_eq, dist_eq_norm] using
      (abs_sub_map_le_sub x a b).trans (x.apply_le_norm (a - b))

/-- A point of the Berkovich spectrum is uniformly continuous. -/
theorem uniformContinuous (x : BerkovichSpectrum A) : UniformContinuous x :=
  x.lipschitzWith_one.uniformContinuous

/-- A point of the Berkovich spectrum is continuous. -/
protected theorem continuous (x : BerkovichSpectrum A) : Continuous x :=
  x.lipschitzWith_one.continuous

/-- The extension by continuity of a point of `M(A)` to the completion of `A`, a point of the
Berkovich spectrum of the completion. -/
noncomputable def extendCompletion (x : BerkovichSpectrum A) :
    BerkovichSpectrum (Completion A) where
  toMulRingSeminorm := x.toMulRingSeminorm.completion x.uniformContinuous
  apply_le_norm' a := by
    induction a using Completion.induction_on with
    | hp => exact isClosed_le (MulRingSeminorm.continuous_completion _ _) continuous_norm
    | ih a => simpa using x.apply_le_norm a

@[simp]
theorem extendCompletion_coe (x : BerkovichSpectrum A) (a : A) :
    x.extendCompletion a = x a := by
  simp [extendCompletion, ← coe_toMulRingSeminorm]

/-- Restriction to `A`, as an equivalence between the Berkovich spectrum of the completion of
`A` and that of `A`. -/
private noncomputable def completionEquiv :
    BerkovichSpectrum (Completion A) ≃ BerkovichSpectrum A where
  toFun := comap Completion.coeRingHom Completion.isBounded_coeRingHom
  invFun := extendCompletion
  left_inv y := ext <| Completion.ext' (BerkovichSpectrum.continuous _) y.continuous
    fun a => by simp
  right_inv x := ext fun a => by simp

private theorem coe_completionEquiv :
    ⇑(completionEquiv : BerkovichSpectrum (Completion A) ≃ BerkovichSpectrum A) =
      ⇑(comap Completion.coeRingHom Completion.isBounded_coeRingHom) :=
  (rfl)

/-- Restriction to `A` is a homeomorphism from the Berkovich spectrum of the completion of `A`
onto that of `A`; its inverse extends a point by continuity. -/
noncomputable def completionHomeomorph :
    BerkovichSpectrum (Completion A) ≃ₜ BerkovichSpectrum A :=
  have hc : Continuous (completionEquiv : BerkovichSpectrum (Completion A) ≃ _) := by
    rw [coe_completionEquiv]
    exact ContinuousMap.continuous _
  { completionEquiv with
    continuous_toFun := hc
    continuous_invFun := hc.continuous_symm_of_equiv_compact_to_t2 }

@[simp]
theorem completionHomeomorph_apply (x : BerkovichSpectrum (Completion A)) (a : A) :
    completionHomeomorph x a = x a := by
  simp [completionHomeomorph, coe_completionEquiv]

/-- The inverse of `completionHomeomorph` extends a point by continuity. -/
@[simp]
theorem completionHomeomorph_symm_apply (x : BerkovichSpectrum A) :
    completionHomeomorph.symm x = x.extendCompletion :=
  (rfl)

theorem completionHomeomorph_symm_apply_coe (x : BerkovichSpectrum A) (a : A) :
    completionHomeomorph.symm x a = x a := by
  simp

end SeminormedRing

/-! ### The norm point -/

section NormPoint

variable {A : Type*} [SeminormedRing A] [NormOneClass A] [NormMulClass A]

/-- The norm of a seminormed ring with multiplicative norm and `‖1‖ = 1`, as a point of its
Berkovich spectrum. -/
noncomputable def normPoint : BerkovichSpectrum A where
  toMulRingSeminorm :=
    { normRingSeminorm A with
      map_one' := norm_one
      map_mul' := norm_mul }
  apply_le_norm' _ := le_rfl

@[simp]
theorem coe_normPoint : ⇑(normPoint : BerkovichSpectrum A) = norm :=
  (rfl)

theorem normPoint_apply (a : A) : (normPoint : BerkovichSpectrum A) a = ‖a‖ :=
  (rfl)

/-- The multiplicative map underlying the norm point is `normHom`. -/
@[simp]
theorem toMonoidWithZeroHom_toMulRingSeminorm_normPoint :
    (normPoint : BerkovichSpectrum A).toMulRingSeminorm.toMonoidWithZeroHom = normHom :=
  (rfl)

/-- A point of the Berkovich spectrum is the norm point exactly when its values are the norms. -/
theorem eq_normPoint_iff {x : BerkovichSpectrum A} : x = normPoint ↔ ∀ a, x a = ‖a‖ :=
  ⟨fun h a => h ▸ normPoint_apply a, fun h => ext fun a => (h a).trans (normPoint_apply a).symm⟩

end NormPoint

section NormedDivisionRing

variable {K : Type*} [NormedDivisionRing K]

/-- On a normed division ring every point of the Berkovich spectrum is the norm: a point `x`
satisfies `x a⁻¹ ≤ ‖a‖⁻¹`, so `1 = x a * x a⁻¹` forces `‖a‖ ≤ x a`. -/
theorem eq_normPoint (x : BerkovichSpectrum K) : x = normPoint := by
  refine eq_normPoint_iff.mpr fun a => (x.apply_le_norm a).antisymm ?_
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hinv : x a⁻¹ ≤ ‖a‖⁻¹ := (x.apply_le_norm a⁻¹).trans_eq (norm_inv a)
  have h1 : x a * x a⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  have : 1 ≤ x a * ‖a‖⁻¹ := h1 ▸ mul_le_mul_of_nonneg_left hinv (apply_nonneg x a)
  rwa [le_mul_inv_iff₀ hpos, one_mul] at this

/-- The Berkovich spectrum of a normed division ring is the single point `normPoint`. -/
noncomputable instance : Unique (BerkovichSpectrum K) where
  default := normPoint
  uniq := eq_normPoint

end NormedDivisionRing

end BerkovichSpectrum

end TauCeti

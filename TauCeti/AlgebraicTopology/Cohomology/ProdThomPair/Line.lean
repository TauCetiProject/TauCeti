/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.Singular.ProdThomPair
import TauCeti.AlgebraicTopology.Cohomology.Additivity.Basic
import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance

/-!
# Cohomology of the Thom pair of a rank-one product bundle

Let `B` be a topological space and `F` a one-dimensional real topological vector space, given with
a continuous linear equivalence `e : F ≃L[ℝ] ℝ`. This file computes the singular cohomology, with
coefficients in any module `M` over a commutative ring `k`, of the complement `B × (F ∖ {0})` of
the zero section of the product bundle `B × F → B` in every degree `n`, and of its Thom pair
`(B × F, B × (F ∖ {0}))` (`TauCeti.prodThomPair`) in every positive degree `n + 1`:

* `B × (F ∖ {0})` splits into the two open half-spaces `{p | 0 < e p.2}` and `{p | e p.2 < 0}`,
  each deformation retracting onto a copy of `B` along straight lines to `±e⁻¹ 1`. Let
  `σ ∈ H⁰(B × (F ∖ {0}); k)` be the degree-zero class taking the value `1` on `{p | 0 < e p.2}` and
  `0` on `{p | e p.2 < 0}` (`TauCeti.prodThomPairPuncturedLineClass`), and
  `π : B × (F ∖ {0}) → B` the projection (`TauCeti.prodThomPairPuncturedProj`). Then
  `(b, c) ↦ π^* b + σ ⌣ π^* c` is a `k`-linear equivalence
  `Hⁿ(B; M) × Hⁿ(B; M) ≃ Hⁿ(B × (F ∖ {0}); M)`
  (`TauCeti.prodThomPairPuncturedSingularCohomologyLineEquiv`).
* In the long exact sequence of the pair, the restriction from `Hᵐ(B × F; M)` to
  `Hᵐ(B × (F ∖ {0}); M)` is injective, since `F` is contractible and `π` has a section, and its
  image is the classes `π^* b`. So the connecting morphism `δ` identifies the classes
  `σ ⌣ π^* c` with the whole relative cohomology in degree `n + 1`:
  `c ↦ δ (σ ⌣ π^* c)` is a `k`-linear equivalence
  `Hⁿ(B; M) ≃ Hⁿ⁺¹(B × F, B × (F ∖ {0}); M)` for every `n`
  (`TauCeti.prodThomPairSingularCohomologyLineEquiv`). It sends the unit of `H⁰(B; k)` to `δ σ`
  (`TauCeti.prodThomPairSingularCohomologyLineEquiv_homologyπ_constSingularCocycle`).

This is the rank-one counterpart of `TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Sphere`,
which treats ranks `d + 2 ≥ 2` where `F ∖ {0}` has connected sphere homotopy type `Sᵈ⁺¹` rather
than two contractible components.

## Main definitions and results

* `TauCeti.prodThomPairPuncturedLineClass`: the indicator class `σ ∈ H⁰(B × (F ∖ {0}); k)` of the
  positive half-space `{p | 0 < e p.2}`.
* `TauCeti.prodThomPairPuncturedSingularCohomologyLineEquiv`:
  `Hⁿ(B; M) × Hⁿ(B; M) ≃ Hⁿ(B × (F ∖ {0}); M)`, `(b, c) ↦ π^* b + σ ⌣ π^* c`.
* `TauCeti.prodThomPairSingularCohomologyLineEquiv`:
  `Hⁿ(B; M) ≃ Hⁿ⁺¹(B × F, B × (F ∖ {0}); M)`, `c ↦ δ (σ ⌣ π^* c)`.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe w

namespace TauCeti

variable {k : Type w} [CommRing k] (M : ModuleCat.{w} k)

variable {B : Type w} [TopologicalSpace B]
  {F : Type w} [TopologicalSpace F] [AddCommMonoid F] [Module ℝ F]

/-! ### The positive half-space indicator class -/

/-- For `e : F ≃L[ℝ] ℝ`, a point of `B × (F ∖ {0})` has nonzero coordinate `e p.2`. -/
private theorem apply_ne_zero_of_mem_snd (e : F ≃L[ℝ] ℝ) (p : (prodThomPair B F).snd) :
    e p.1.2 ≠ 0 :=
  (map_ne_zero_iff e e.injective).2 p.2

/-- The positive open half-space `{p | 0 < e p.2}` of `B × (F ∖ {0})` is both closed and open, as
its complement in `B × (F ∖ {0})` is the negative open half-space `{p | e p.2 < 0}`. -/
private theorem isClopen_posHalfSpace (e : F ≃L[ℝ] ℝ) :
    IsClopen {p : (prodThomPair B F).snd | 0 < e p.1.2} := by
  have hcont : Continuous fun p : (prodThomPair B F).snd ↦ e p.1.2 :=
    e.continuous.comp (continuous_snd.comp continuous_subtype_val)
  refine ⟨?_, isOpen_lt continuous_const hcont⟩
  rw [← isOpen_compl_iff]
  have hcompl : ({p : (prodThomPair B F).snd | 0 < e p.1.2})ᶜ =
      {p : (prodThomPair B F).snd | e p.1.2 < 0} := by
    ext p
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
    exact le_iff_lt_or_eq.trans (or_iff_left (apply_ne_zero_of_mem_snd e p))
  rw [hcompl]
  exact isOpen_lt hcont continuous_const

/-- Points of `B × (F ∖ {0})` joined by a path lie in the same half-space of `e`. -/
private theorem pos_iff_of_joined (e : F ≃L[ℝ] ℝ) {p q : (prodThomPair B F).snd} (h : Joined p q) :
    0 < e p.1.2 ↔ 0 < e q.1.2 := by
  obtain ⟨γ⟩ := h
  rcases isClopen_iff.1 ((isClopen_posHalfSpace e).preimage γ.continuous) with h0 | h1
  · have hp : (0 : unitInterval) ∉ γ ⁻¹' {x | 0 < e x.1.2} := by simp [h0]
    have hq : (1 : unitInterval) ∉ γ ⁻¹' {x | 0 < e x.1.2} := by simp [h0]
    simpa [Set.mem_preimage] using iff_of_false hp hq
  · have hp : (0 : unitInterval) ∈ γ ⁻¹' {x | 0 < e x.1.2} := by simp [h1]
    have hq : (1 : unitInterval) ∈ γ ⁻¹' {x | 0 < e x.1.2} := by simp [h1]
    simpa [Set.mem_preimage] using iff_of_true hp hq

private theorem exists_puncturedLineClass (k : Type w) [CommRing k] (B : Type w)
    [TopologicalSpace B] (e : F ≃L[ℝ] ℝ) :
    ∃ u : (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) 0,
      ∀ p : (prodThomPair B F).snd,
        singularCohomologyZeroEval p u = if 0 < e p.1.2 then 1 else 0 := by
  classical
  exact exists_singularCohomologyZeroEval_eq _ fun p q h ↦ by
    simp only [pos_iff_of_joined e h]

variable (k B) in
/-- The degree-zero class `σ ∈ H⁰(B × (F ∖ {0}); k)` that takes the value `1` on the positive
half-space `{p | 0 < e p.2}` and `0` on the negative half-space `{p | e p.2 < 0}`
(`TauCeti.singularCohomologyZeroEval_prodThomPairPuncturedLineClass`). -/
def prodThomPairPuncturedLineClass (e : F ≃L[ℝ] ℝ) :
    (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0 :=
  (exists_puncturedLineClass k B e).choose

/-- `TauCeti.prodThomPairPuncturedLineClass` evaluates to `1` on `{p | 0 < e p.2}` and to `0`
elsewhere. -/
@[simp]
theorem singularCohomologyZeroEval_prodThomPairPuncturedLineClass (e : F ≃L[ℝ] ℝ)
    (p : (prodThomPair B F).snd) :
    singularCohomologyZeroEval p (prodThomPairPuncturedLineClass k B e) =
      if 0 < e p.1.2 then 1 else 0 :=
  (exists_puncturedLineClass k B e).choose_spec p

/-- A degree-zero class of `B × (F ∖ {0})` equals `TauCeti.prodThomPairPuncturedLineClass` if and
only if it evaluates to `1` on `{p | 0 < e p.2}` and `0` elsewhere. -/
theorem eq_prodThomPairPuncturedLineClass_iff (e : F ≃L[ℝ] ℝ)
    {u : (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) 0} :
    u = prodThomPairPuncturedLineClass k B e ↔
      ∀ p : (prodThomPair B F).snd,
        singularCohomologyZeroEval p u = if 0 < e p.1.2 then 1 else 0 :=
  ⟨fun h p ↦ h ▸ singularCohomologyZeroEval_prodThomPairPuncturedLineClass e p,
    fun h ↦ singularCohomologyZero_ext fun p ↦
      (h p).trans (singularCohomologyZeroEval_prodThomPairPuncturedLineClass e p).symm⟩

/-! ### Decomposition of the punctured rank-one product bundle -/

/-- Two copies of `B`, indexed by `ULift Bool`, onto which `B × (F ∖ {0})` deformation retracts. -/
private abbrev twoCopies (B : Type w) [TopologicalSpace B] : ULift.{w} Bool → TopCat.{w} :=
  fun _ ↦ TopCat.of B

/-- The section `b ↦ (b, ±e⁻¹ 1)` of `B × (F ∖ {0}) → B` corresponding to `s : Bool`. -/
private def signedSection (e : F ≃L[ℝ] ℝ) (s : Bool) :
    TopCat.of B ⟶ (prodThomPair B F).snd :=
  TopCat.ofHom ⟨fun b ↦ ⟨(b, e.symm (if s then 1 else -1)), by
    -- Membership in `{p | p.2 ≠ 0}` is `e.symm (if s then 1 else -1) ≠ 0`.
    change e.symm (if s then 1 else -1) ≠ 0
    rw [ne_eq, map_eq_zero_iff e.symm e.symm.injective]
    cases s <;> norm_num⟩, by fun_prop⟩

private theorem signedSection_comp_prodThomPairPuncturedProj (e : F ≃L[ℝ] ℝ) (s : Bool) :
    signedSection (B := B) e s ≫ prodThomPairPuncturedProj B F = 𝟙 _ :=
  TopCat.ext fun b ↦ prodThomPairPuncturedProj_apply F (signedSection e s b)

private theorem singularCohomologyMap_signedSection_true_puncturedLineClass (e : F ≃L[ℝ] ℝ) :
    TopCat.singularCohomologyMap (signedSection (B := B) e true) 0
        (prodThomPairPuncturedLineClass k B e) =
      (TopCat.of B).singularCohomologyZeroOne :=
  singularCohomologyZero_ext fun b ↦ by
    have hb : (signedSection e true b).1.2 = e.symm 1 := rfl
    rw [singularCohomologyZeroEval_naturality,
      singularCohomologyZeroEval_prodThomPairPuncturedLineClass, hb,
      ContinuousLinearEquiv.apply_symm_apply,
      singularCohomologyZeroEval_singularCohomologyZeroOne]
    norm_num

private theorem singularCohomologyMap_signedSection_false_puncturedLineClass (e : F ≃L[ℝ] ℝ) :
    TopCat.singularCohomologyMap (signedSection (B := B) e false) 0
        (prodThomPairPuncturedLineClass k B e) = 0 :=
  singularCohomologyZero_ext fun b ↦ by
    have hb : (signedSection e false b).1.2 = e.symm (-1) := rfl
    rw [singularCohomologyZeroEval_naturality, map_zero,
      singularCohomologyZeroEval_prodThomPairPuncturedLineClass, hb,
      ContinuousLinearEquiv.apply_symm_apply]
    norm_num

open scoped Classical in
private def toTwoCopiesFun (e : F ≃L[ℝ] ℝ) (p : (prodThomPair B F).snd) :
    Σ i : ULift.{w} Bool, twoCopies B i :=
  ⟨⟨decide (0 < e p.1.2)⟩, p.1.1⟩

open scoped Classical in
private theorem continuous_toTwoCopiesFun (e : F ≃L[ℝ] ℝ) :
    Continuous (toTwoCopiesFun (B := B) e) :=
  continuous_def.2 fun U hU ↦ by
    rw [isOpen_sigma_iff] at hU
    have hcont : Continuous fun p : (prodThomPair B F).snd ↦ e p.1.2 :=
      e.continuous.comp (continuous_snd.comp continuous_subtype_val)
    have hfst : Continuous fun p : (prodThomPair B F).snd ↦ p.1.1 :=
      continuous_fst.comp continuous_subtype_val
    let ιt : B → Σ i : ULift.{w} Bool, twoCopies B i := fun b ↦ ⟨⟨true⟩, b⟩
    let ιf : B → Σ i : ULift.{w} Bool, twoCopies B i := fun b ↦ ⟨⟨false⟩, b⟩
    have heq : toTwoCopiesFun e ⁻¹' U =
        ({p | 0 < e p.1.2} ∩ (fun p : (prodThomPair B F).snd ↦ p.1.1) ⁻¹' (ιt ⁻¹' U)) ∪
        ({p | e p.1.2 < 0} ∩ (fun p : (prodThomPair B F).snd ↦ p.1.1) ⁻¹' (ιf ⁻¹' U)) := by
      ext p
      rcases lt_trichotomy 0 (e p.1.2) with hp | hp | hp
      · have hnp : ¬ e p.1.2 < 0 := not_lt.2 hp.le
        simp [toTwoCopiesFun, hp, hnp, ιt]
      · exact (apply_ne_zero_of_mem_snd e p hp.symm).elim
      · have hnp : ¬ 0 < e p.1.2 := not_lt.2 hp.le
        simp [toTwoCopiesFun, hp, hnp, ιf]
    rw [heq]
    exact ((isOpen_lt continuous_const hcont).inter (hfst.isOpen_preimage _ (hU ⟨true⟩))).union
      ((isOpen_lt hcont continuous_const).inter (hfst.isOpen_preimage _ (hU ⟨false⟩)))

open scoped Classical in
/-- Collapsing each half-space of `B × (F ∖ {0})` to its copy of `B` in `∐_{ULift Bool} B`. -/
private def toTwoCopies (e : F ≃L[ℝ] ℝ) :
    (prodThomPair B F).snd ⟶ TopCat.of (Σ i : ULift.{w} Bool, twoCopies B i) :=
  TopCat.ofHom ⟨toTwoCopiesFun e, continuous_toTwoCopiesFun e⟩

/-- Embedding `∐_{ULift Bool} B` into `B × (F ∖ {0})` via `signedSection`. -/
private def fromTwoCopies (e : F ≃L[ℝ] ℝ) :
    TopCat.of (Σ i : ULift.{w} Bool, twoCopies B i) ⟶ (prodThomPair B F).snd :=
  TopCat.ofHom ⟨fun q ↦ signedSection e q.1.down q.2,
    continuous_sigma_iff.2 fun i ↦ (signedSection (B := B) e i.down).hom.continuous⟩

private theorem sigmaι_comp_fromTwoCopies (e : F ≃L[ℝ] ℝ) (s : Bool) :
    TopCat.sigmaι.{w, w} (twoCopies B) (ULift.up.{w} s) ≫ fromTwoCopies e = signedSection e s :=
  TopCat.ext fun _ ↦ rfl

open scoped Classical in
private theorem fst_toTwoCopies_fromTwoCopies_apply (e : F ≃L[ℝ] ℝ)
    (p : (prodThomPair B F).snd) :
    ((toTwoCopies e ≫ fromTwoCopies e) p).1.1 = p.1.1 :=
  -- The first coordinate of `signedSection` is the base point.
  (rfl)

open scoped Classical in
private theorem snd_toTwoCopies_fromTwoCopies_apply (e : F ≃L[ℝ] ℝ)
    (p : (prodThomPair B F).snd) :
    ((toTwoCopies e ≫ fromTwoCopies e) p).1.2 = e.symm (if 0 < e p.1.2 then 1 else -1) := by
  -- Both sides evaluate `(signedSection e (decide (0 < e p.1.2)) p.1.1).1.2`.
  change (e.symm (if decide (0 < e p.1.2) = true then 1 else -1)) = _
  simp

open scoped Classical in
/-- Straight-line homotopy from `toTwoCopies ≫ fromTwoCopies` to `𝟙 (B × (F ∖ {0}))`, formed in `ℝ`
and transported by `e.symm` so no topological vector space axioms on `F` beyond `e` are needed. -/
private def retractHomotopy (e : F ≃L[ℝ] ℝ) :
    TopCat.Homotopy (toTwoCopies (B := B) e ≫ fromTwoCopies e) (𝟙 _) where
  toFun q :=
    ⟨(q.2.1.1, e.symm ((q.1 : ℝ) * e q.2.1.2 +
        (1 - (q.1 : ℝ)) * e ((toTwoCopies e ≫ fromTwoCopies e) q.2).1.2)),
      by
        -- Membership in `{p | p.2 ≠ 0}` is nonvanishing of the second coordinate.
        change e.symm _ ≠ 0
        rw [ne_eq, map_eq_zero_iff e.symm e.symm.injective, snd_toTwoCopies_fromTwoCopies_apply,
          ContinuousLinearEquiv.apply_symm_apply]
        intro he0
        have ht0 : 0 ≤ (q.1 : ℝ) := q.1.2.1
        have ht1 : 0 ≤ 1 - (q.1 : ℝ) := sub_nonneg.2 q.1.2.2
        rcases lt_trichotomy 0 (e q.2.1.2) with hp | hp | hp
        · simp only [hp, ↓reduceIte] at he0
          rcases eq_or_lt_of_le ht0 with ht | ht
          · rw [← ht] at he0; norm_num at he0
          · linarith [mul_pos ht hp, mul_nonneg ht1 zero_le_one]
        · exact apply_ne_zero_of_mem_snd e q.2 hp.symm
        · simp only [not_lt.2 hp.le, ↓reduceIte] at he0
          rcases eq_or_lt_of_le ht0 with ht | ht
          · rw [← ht] at he0; norm_num at he0
          · linarith [mul_neg_of_pos_of_neg ht hp,
              mul_nonpos_of_nonneg_of_nonpos ht1 (by norm_num : (-1 : ℝ) ≤ 0)]⟩
  continuous_toFun := by
    have h1 : Continuous fun q : unitInterval × (prodThomPair B F).snd ↦ q.2.1.1 :=
      continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
    have h2 : Continuous fun q : unitInterval × (prodThomPair B F).snd ↦ e q.2.1.2 :=
      e.continuous.comp (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))
    have h3 : Continuous fun q : unitInterval × (prodThomPair B F).snd ↦
        e ((toTwoCopies e ≫ fromTwoCopies e) q.2).1.2 :=
      e.continuous.comp (continuous_snd.comp (continuous_subtype_val.comp
        ((toTwoCopies e ≫ fromTwoCopies e).hom.continuous.comp continuous_snd)))
    have ht : Continuous fun q : unitInterval × (prodThomPair B F).snd ↦ (q.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    exact Continuous.subtype_mk
      (h1.prodMk (e.symm.continuous.comp ((ht.mul h2).add ((continuous_const.sub ht).mul h3)))) _
  map_zero_left p := by
    apply Subtype.ext
    apply Prod.ext
    · exact (fst_toTwoCopies_fromTwoCopies_apply e p).symm
    · simp only [Set.Icc.coe_zero, zero_mul, sub_zero, one_mul, zero_add,
        ContinuousLinearEquiv.symm_apply_apply]
  map_one_left p := by
    apply Subtype.ext
    simp

/-- Two cohomology classes on `B × (F ∖ {0})` agree as soon as their pullbacks along both signed
sections `b ↦ (b, ±e⁻¹ 1)` agree. -/
private theorem puncturedLine_cohomology_ext (e : F ≃L[ℝ] ℝ) (n : ℕ)
    {x y : (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n}
    (ht : TopCat.singularCohomologyMap (signedSection e true) n x =
      TopCat.singularCohomologyMap (signedSection e true) n y)
    (hf : TopCat.singularCohomologyMap (signedSection e false) n x =
      TopCat.singularCohomologyMap (signedSection e false) n y) : x = y := by
  have hfan := isLimitFanSingularCohomology (twoCopies B) (ModuleCat.{w} k)
    (𝟙_ (ModuleCat.{w} k)) k M n
  have hfrom : TopCat.singularCohomologyMap (fromTwoCopies e) n x =
      TopCat.singularCohomologyMap (fromTwoCopies e) n y := by
    refine Concrete.isLimit_ext _ hfan _ _ fun ⟨⟨s⟩⟩ ↦ ?_
    simp only [Fan.mk_π_app, ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
      sigmaι_comp_fromTwoCopies]
    cases s
    · exact hf
    · exact ht
  have hret := (retractHomotopy (B := B) e).congr_singularCohomologyMap
    (𝟙_ (ModuleCat.{w} k)) k M n
  have hx := ConcreteCategory.congr_hom hret x
  have hy := ConcreteCategory.congr_hom hret y
  rw [TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply,
    TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply] at hx hy
  exact hx.symm.trans ((congrArg _ hfrom).trans hy)

/-- The map `(b, c) ↦ π^* b + σ ⌣ π^* c` into the cohomology of `B × (F ∖ {0})`. -/
private def puncturedLineMap (e : F ≃L[ℝ] ℝ) (n : ℕ) :
    ((TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) →ₗ[k]
      (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n :=
  LinearMap.coprod (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n).hom
    ((prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
        0 n n (zero_add n) (prodThomPairPuncturedLineClass k B e) ∘ₗ
      (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n).hom)

private theorem puncturedLineMap_apply (e : F ≃L[ℝ] ℝ) (n : ℕ)
    (bc : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    puncturedLineMap M e n bc =
      TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n bc.1 +
        (prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
          0 n n (zero_add n) (prodThomPairPuncturedLineClass k B e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n bc.2) :=
  -- `puncturedLineMap` is this sum by definition.
  (rfl)

private theorem singularCohomologyMap_signedSection_true_puncturedLineMap (e : F ≃L[ℝ] ℝ) (n : ℕ)
    (bc : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    TopCat.singularCohomologyMap (signedSection e true) n (puncturedLineMap M e n bc) =
      bc.1 + bc.2 := by
  rw [puncturedLineMap_apply, map_add, ← TopCat.singularCup_naturality,
    singularCohomologyMap_signedSection_true_puncturedLineClass]
  simp only [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    signedSection_comp_prodThomPairPuncturedProj, TopCat.singularCohomologyMap_id,
    ConcreteCategory.id_apply]
  rw [TopCat.singularCohomologyZeroOne_def,
    TopCat.singularCup_constSingularCocycle_left _ k (η := 𝟙 _) (by simp) (by simp) (zero_add n)]

private theorem singularCohomologyMap_signedSection_false_puncturedLineMap (e : F ≃L[ℝ] ℝ) (n : ℕ)
    (bc : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    TopCat.singularCohomologyMap (signedSection e false) n (puncturedLineMap M e n bc) = bc.1 := by
  rw [puncturedLineMap_apply, map_add, ← TopCat.singularCup_naturality,
    singularCohomologyMap_signedSection_false_puncturedLineClass, LinearMap.map_zero₂,
    add_zero, ← ConcreteCategory.comp_apply,
    ← TopCat.singularCohomologyMap_comp, signedSection_comp_prodThomPairPuncturedProj,
    TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply]

private theorem bijective_puncturedLineMap (e : F ≃L[ℝ] ℝ) (n : ℕ) :
    Function.Bijective (puncturedLineMap (B := B) M e n) := by
  refine ⟨fun bc bc' h ↦ ?_, fun x ↦ ?_⟩
  · have h₁ : bc.1 = bc'.1 := by
      simpa [singularCohomologyMap_signedSection_false_puncturedLineMap] using
        congrArg (TopCat.singularCohomologyMap (signedSection e false) n) h
    have h₂ : bc.1 + bc.2 = bc'.1 + bc'.2 := by
      simpa [singularCohomologyMap_signedSection_true_puncturedLineMap] using
        congrArg (TopCat.singularCohomologyMap (signedSection e true) n) h
    exact Prod.ext h₁ (add_left_cancel (h₁ ▸ h₂))
  · refine ⟨(TopCat.singularCohomologyMap (signedSection e false) n x,
      TopCat.singularCohomologyMap (signedSection e true) n x -
        TopCat.singularCohomologyMap (signedSection e false) n x),
      puncturedLine_cohomology_ext M e n ?_ ?_⟩
    · rw [singularCohomologyMap_signedSection_true_puncturedLineMap, add_sub_cancel]
    · rw [singularCohomologyMap_signedSection_false_puncturedLineMap]

variable (B) in
/-- **The cohomology of the punctured rank-one product bundle.** For a continuous linear equivalence
`e : F ≃L[ℝ] ℝ` and every degree `n`, every class of `Hⁿ(B × (F ∖ {0}); M)` is uniquely
`π^* b + σ ⌣ π^* c` with `b, c ∈ Hⁿ(B; M)`, where `π` is the projection to `B` and `σ` is the
positive half-space indicator class `TauCeti.prodThomPairPuncturedLineClass`
(`TauCeti.prodThomPairPuncturedSingularCohomologyLineEquiv_apply`). -/
def prodThomPairPuncturedSingularCohomologyLineEquiv (e : F ≃L[ℝ] ℝ) (n : ℕ) :
    ((TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) ≃ₗ[k]
      (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n :=
  LinearEquiv.ofBijective (puncturedLineMap M e n) (bijective_puncturedLineMap M e n)

/-- The decomposition `TauCeti.prodThomPairPuncturedSingularCohomologyLineEquiv` sends `(b, c)` to
`π^* b + σ ⌣ π^* c`. -/
@[simp]
theorem prodThomPairPuncturedSingularCohomologyLineEquiv_apply (e : F ≃L[ℝ] ℝ) (n : ℕ)
    (bc : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    prodThomPairPuncturedSingularCohomologyLineEquiv M B e n bc =
      TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n bc.1 +
        (prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
          0 n n (zero_add n) (prodThomPairPuncturedLineClass k B e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n bc.2) :=
  puncturedLineMap_apply M e n bc

/-! ### Relative cohomology of the rank-one Thom pair -/

omit [Module ℝ F] in
/-- Every class of `Hᵐ(B × F; M)` is pulled back from the base, since `F` is contractible. -/
private theorem exists_singularCohomologyMap_prodThomPairProj_eq [ContractibleSpace F] (m : ℕ)
    (y : (prodThomPair B F).fst.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m) :
    ∃ b, TopCat.singularCohomologyMap (prodThomPairProj B F) m b = y := by
  have := (ContinuousMap.HomotopyEquiv.prodContractible B F).isIso_singularCohomologyMap
    (𝟙_ (ModuleCat.{w} k)) k M m
  rw [ContinuousMap.HomotopyEquiv.prodContractible_toFun] at this
  have hproj : TopCat.ofHom ContinuousMap.fst = prodThomPairProj B F :=
    TopCat.ext fun p ↦ (prodThomPairProj_apply F p).symm
  have : IsIso (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k) (M := M)
    (prodThomPairProj B F) m) := hproj ▸ this
  refine ⟨inv (TopCat.singularCohomologyMap (prodThomPairProj B F) m) y, ?_⟩
  rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]

/-- Pulling back along `B × (F ∖ {0}) → B` is injective, as `signedSection e true` is a section. -/
private theorem injective_singularCohomologyMap_prodThomPairPuncturedProj (e : F ≃L[ℝ] ℝ)
    (m : ℕ) :
    Function.Injective (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
      (M := M) (prodThomPairPuncturedProj B F) m) := by
  refine Function.LeftInverse.injective (g := TopCat.singularCohomologyMap (signedSection e true) m)
    fun b ↦ ?_
  rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    signedSection_comp_prodThomPairPuncturedProj, TopCat.singularCohomologyMap_id,
    ConcreteCategory.id_apply]

/-- The classes `π^* b` of `TauCeti.prodThomPairPuncturedSingularCohomologyLineEquiv` are the
restrictions of the classes of `B × F` pulled back from `B`. -/
private theorem prodThomPairPuncturedSingularCohomologyLineEquiv_apply_zero (e : F ≃L[ℝ] ℝ)
    (n : ℕ) (b : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    prodThomPairPuncturedSingularCohomologyLineEquiv M B e n (b, 0) =
      TopCat.singularCohomologyMap (prodThomPair B F).map n
        (TopCat.singularCohomologyMap (prodThomPairProj B F) n b) := by
  rw [prodThomPairPuncturedSingularCohomologyLineEquiv_apply, map_zero, map_zero, add_zero,
    ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, map_comp_prodThomPairProj]

/-- The map `c ↦ δ (σ ⌣ π^* c)` into the relative cohomology of the rank-one Thom pair. -/
private def lineDeltaMap (e : F ≃L[ℝ] ℝ) (n m : ℕ) (h : n + 1 = m) :
    (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n →ₗ[k]
      (prodThomPair B F).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m :=
  ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M n m h).hom ∘ₗ
    (prodThomPairPuncturedSingularCohomologyLineEquiv M B e n).toLinearMap ∘ₗ
      LinearMap.inr k _ _

private theorem lineDeltaMap_apply (e : F ≃L[ℝ] ℝ) (n m : ℕ) (h : n + 1 = m)
    (c : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    lineDeltaMap M e n m h c =
      ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M n m h)
        ((prodThomPairPuncturedSingularCohomologyLineEquiv M B e n) (0, c)) :=
  -- `lineDeltaMap` is this composite by definition.
  (rfl)

private theorem injective_lineDeltaMap (e : F ≃L[ℝ] ℝ) (n m : ℕ) (h : n + 1 = m) :
    Function.Injective (lineDeltaMap (B := B) M e n m h) := by
  have := e.toHomeomorph.contractibleSpace
  refine (injective_iff_map_eq_zero _).2 fun c hc ↦ ?_
  rw [lineDeltaMap_apply] at hc
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1
    ((prodThomPair B F).singularCohomology_exact_subspace (𝟙_ (ModuleCat.{w} k)) k M n m h) _ hc
  obtain ⟨b, rfl⟩ := exists_singularCohomologyMap_prodThomPairProj_eq M n y
  rw [← prodThomPairPuncturedSingularCohomologyLineEquiv_apply_zero M e n] at hy
  exact congrArg Prod.snd
    ((prodThomPairPuncturedSingularCohomologyLineEquiv M B e n).injective hy).symm

private theorem surjective_lineDeltaMap (e : F ≃L[ℝ] ℝ) (n m : ℕ) (h : n + 1 = m) :
    Function.Surjective (lineDeltaMap (B := B) M e n m h) := by
  have := e.toHomeomorph.contractibleSpace
  let P := prodThomPair B F
  let D := prodThomPairPuncturedSingularCohomologyLineEquiv M B e n
  intro z
  obtain ⟨b, hb⟩ := exists_singularCohomologyMap_prodThomPairProj_eq M m
    (P.singularCohomologyπ _ k M m z)
  have hπ : P.singularCohomologyπ _ k M m z = 0 := by
    have h0 := ConcreteCategory.congr_hom
      (P.singularCohomologyπ_comp_singularCohomologyMap (𝟙_ (ModuleCat.{w} k)) k M m) z
    rw [ConcreteCategory.comp_apply, ← hb, ← ConcreteCategory.comp_apply,
      ← TopCat.singularCohomologyMap_comp, map_comp_prodThomPairProj] at h0
    rw [← hb, injective_singularCohomologyMap_prodThomPairPuncturedProj M e m
      (h0.trans (map_zero _).symm), map_zero]
  obtain ⟨x, rfl⟩ : ∃ x, (P.singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M n m h) x = z :=
    (ShortComplex.moduleCat_exact_iff _).1
      (P.singularCohomology_exact_relative (𝟙_ (ModuleCat.{w} k)) k M n m h) z hπ
  obtain ⟨⟨b', c⟩, rfl⟩ := D.surjective x
  refine ⟨c, ?_⟩
  have hδ : (P.singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M n m h) (D (b', 0)) = 0 := by
    rw [prodThomPairPuncturedSingularCohomologyLineEquiv_apply_zero M e n b',
      ← ConcreteCategory.comp_apply,
      P.singularCohomologyMap_comp_singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M n m h]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply]
  have hbc : ((b', c) : _ × _) = (b', 0) + (0, c) := by simp
  rw [lineDeltaMap_apply, hbc, map_add, map_add, hδ, zero_add]

private theorem bijective_lineDeltaMap (e : F ≃L[ℝ] ℝ) (n m : ℕ) (h : n + 1 = m) :
    Function.Bijective (lineDeltaMap (B := B) M e n m h) :=
  ⟨injective_lineDeltaMap M e n m h, surjective_lineDeltaMap M e n m h⟩

variable (B) in
/-- **The cohomology of the Thom pair of a rank-one product bundle in degrees at least one.** Let
`e : F ≃L[ℝ] ℝ` be a continuous linear equivalence. Then, for every base degree `n` and
`m = n + 1`, `c ↦ δ (σ ⌣ π^* c)` is a `k`-linear equivalence
`Hⁿ(B; M) ≃ Hᵐ(B × F, B × (F ∖ {0}); M)`, where `π : B × (F ∖ {0}) → B` is the projection,
`σ ∈ H⁰(B × (F ∖ {0}); k)` is `TauCeti.prodThomPairPuncturedLineClass`, and `δ` is the connecting
morphism of the pair (`TauCeti.prodThomPairSingularCohomologyLineEquiv_apply`). -/
def prodThomPairSingularCohomologyLineEquiv (e : F ≃L[ℝ] ℝ) (n m : ℕ) (h : n + 1 = m := by lia) :
    (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n ≃ₗ[k]
      (prodThomPair B F).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m :=
  LinearEquiv.ofBijective (lineDeltaMap M e n m h) (bijective_lineDeltaMap M e n m h)

/-- The equivalence `TauCeti.prodThomPairSingularCohomologyLineEquiv` sends `c` to
`δ (σ ⌣ π^* c)`. -/
@[simp]
theorem prodThomPairSingularCohomologyLineEquiv_apply (e : F ≃L[ℝ] ℝ) (n m : ℕ) (h : n + 1 = m)
    (c : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    prodThomPairSingularCohomologyLineEquiv M B e n m h c =
      ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M n m h)
        ((prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
          0 n n (zero_add n) (prodThomPairPuncturedLineClass k B e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n c)) := by
  rw [prodThomPairSingularCohomologyLineEquiv, LinearEquiv.ofBijective_apply,
    lineDeltaMap_apply, prodThomPairPuncturedSingularCohomologyLineEquiv_apply, map_zero, zero_add]

/-- The equivalence `TauCeti.prodThomPairSingularCohomologyLineEquiv` sends the unit
`1 ∈ H⁰(B; k)`, the class of the constant `0`-cocycle, to `δ σ`, where `σ` is
`TauCeti.prodThomPairPuncturedLineClass`. -/
theorem prodThomPairSingularCohomologyLineEquiv_homologyπ_constSingularCocycle (e : F ≃L[ℝ] ℝ) :
    (prodThomPairSingularCohomologyLineEquiv (𝟙_ (ModuleCat.{w} k)) B e 0 1)
        (((TopCat.of B).singularCochainComplex (𝟙_ (ModuleCat.{w} k)) k
          (𝟙_ (ModuleCat.{w} k))).homologyπ 0
          ((TopCat.of B).constSingularCocycle k (𝟙 (𝟙_ (ModuleCat.{w} k))))) =
      ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))
        0 1) (prodThomPairPuncturedLineClass k B e) := by
  rw [prodThomPairSingularCohomologyLineEquiv_apply,
    TopCat.singularCohomologyMap_homologyπ_constSingularCocycle,
    TopCat.singularCup_constSingularCocycle_right _ k (η := 𝟙 _)
      (by simp [unitors_inv_equal]) (by simp [unitors_equal])]

/-! ### Naturality in the base -/

section Naturality

variable {B' : Type w} [TopologicalSpace B'] (g : C(B, B'))

/-- The class `σ` of `TauCeti.prodThomPairPuncturedLineClass` is natural in the base. -/
@[simp]
theorem singularCohomologyMap_snd_prodThomPairMap_prodThomPairPuncturedLineClass (e : F ≃L[ℝ] ℝ) :
    TopCat.singularCohomologyMap (TopPair.Hom.snd (prodThomPairMap F g)) 0
        (prodThomPairPuncturedLineClass k B' e) = prodThomPairPuncturedLineClass k B e :=
  singularCohomologyZero_ext fun p ↦ by simp

/-- The decomposition `TauCeti.prodThomPairPuncturedSingularCohomologyLineEquiv` is natural in the
base: restricting `π^* b + σ ⌣ π^* c` along the map induced by `g : B → B'` gives
`π^* (g^* b) + σ ⌣ π^* (g^* c)`. -/
theorem prodThomPairPuncturedSingularCohomologyLineEquiv_naturality (e : F ≃L[ℝ] ℝ) (n : ℕ)
    (bc : (TopCat.of B').singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n ×
      (TopCat.of B').singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    TopCat.singularCohomologyMap (TopPair.Hom.snd (prodThomPairMap F g)) n
        (prodThomPairPuncturedSingularCohomologyLineEquiv M B' e n bc) =
      prodThomPairPuncturedSingularCohomologyLineEquiv M B e n
        (TopCat.singularCohomologyMap (TopCat.ofHom g) n bc.1,
          TopCat.singularCohomologyMap (TopCat.ofHom g) n bc.2) := by
  rw [prodThomPairPuncturedSingularCohomologyLineEquiv_apply,
    prodThomPairPuncturedSingularCohomologyLineEquiv_apply, map_add,
    ← TopCat.singularCup_naturality,
    singularCohomologyMap_snd_prodThomPairMap_prodThomPairPuncturedLineClass]
  simp only [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    snd_prodThomPairMap_comp_prodThomPairPuncturedProj]

/-- **Naturality of the cohomology of the rank-one Thom pair.** The equivalence
`TauCeti.prodThomPairSingularCohomologyLineEquiv` commutes with the maps induced by a continuous
map `g : B → B'` of the bases. -/
theorem prodThomPairSingularCohomologyLineEquiv_naturality (e : F ≃L[ℝ] ℝ) (n m : ℕ)
    (h : n + 1 = m := by lia)
    (c : (TopCat.of B').singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    TopPair.singularCohomologyMap (prodThomPairMap F g) m
        (prodThomPairSingularCohomologyLineEquiv M B' e n m h c) =
      prodThomPairSingularCohomologyLineEquiv M B e n m h
        (TopCat.singularCohomologyMap (TopCat.ofHom g) n c) := by
  rw [prodThomPairSingularCohomologyLineEquiv, prodThomPairSingularCohomologyLineEquiv,
    LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply, lineDeltaMap_apply,
    lineDeltaMap_apply, ← ConcreteCategory.comp_apply,
    TopPair.singularCohomologyδ_naturality (prodThomPairMap F g) n m h,
    ConcreteCategory.comp_apply,
    prodThomPairPuncturedSingularCohomologyLineEquiv_naturality M g e n, map_zero]

end Naturality

end TauCeti

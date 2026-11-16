/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.Singular.ProdThomPair
import Mathlib.Topology.LocallyConstant.Basic
import TauCeti.AlgebraicTopology.Cohomology.Additivity.Basic
import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Basic

/-!
# Cohomology of the Thom pair of a product line bundle

Let `B` be a topological space and `F` a real topological vector space of dimension one, given
with a continuous linear equivalence `e : F ≃L[ℝ] ℝ`. This file computes the singular cohomology,
with coefficients in any module `M` over a commutative ring `k`, of the complement
`B × (F ∖ {0})` of the zero section of the product bundle `B × F → B`, and of its Thom pair
`(B × F, B × (F ∖ {0}))` (`TauCeti.prodThomPair`) in every degree `n + 1 ≥ 1`. It is the rank-one
counterpart of `TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Sphere`, which treats ranks at
least two, where `F ∖ {0}` is connected.

* In rank one `F ∖ {0}` has two contractible components, the half-lines `e > 0` and `e < 0`, so
  `B × (F ∖ {0})` is homotopy equivalent to two disjoint copies of `B`. Let
  `σ ∈ H⁰(B × (F ∖ {0}); k)` be the class with the value `1` on the half `e > 0` and `0` on the
  half `e < 0` (`TauCeti.prodThomPairPuncturedLineClass`), and `π : B × (F ∖ {0}) → B` the
  projection. Every class of `Hᵐ(B × (F ∖ {0}); M)` is uniquely `π^* b + σ ⌣ π^* c` with `b` and
  `c` in `Hᵐ(B; M)` (`TauCeti.prodThomPairPuncturedLineSingularCohomologyEquiv`): the pullbacks of
  this class along the sections `b ↦ (b, e⁻¹ 1)` and `b ↦ (b, e⁻¹ (-1))` are `b + c` and `b`, and a
  class is determined by these two pullbacks, by additivity of singular cohomology
  (`TauCeti.isLimitFanSingularCohomology`).
* In the long exact sequence of the pair, the restriction from `Hᵐ(B × F; M)` to
  `Hᵐ(B × (F ∖ {0}); M)` is injective with image the classes `π^* b`, since `F` is contractible
  and the projection has a section. So the connecting morphism `δ` identifies the classes
  `σ ⌣ π^* c` with the whole relative cohomology in degree `n + 1`: `c ↦ δ (σ ⌣ π^* c)` is a
  `k`-linear equivalence `Hⁿ(B; M) ≃ Hⁿ⁺¹(B × F, B × (F ∖ {0}); M)` for every `n`
  (`TauCeti.prodThomPairSingularCohomologyLineEquiv`). It sends the unit of `H⁰(B; k)` to `δ σ`
  (`TauCeti.prodThomPairSingularCohomologyLineEquiv_singularCohomologyZeroOne`).

This is the product case of the Thom isomorphism for real line bundles, such as the negative
normal bundle of a Morse–Bott critical submanifold of index one. Both equivalences are natural in
the base (`TauCeti.prodThomPairPuncturedLineSingularCohomologyEquiv_naturality` and
`TauCeti.prodThomPairSingularCohomologyLineEquiv_naturality`).

## Main definitions and results

* `TauCeti.prodThomPairPuncturedLineClass`: the class `σ` of the half `e > 0`, with its values
  `TauCeti.singularCohomologyZeroEval_prodThomPairPuncturedLineClass`.
* `TauCeti.prodThomPairPuncturedLineSingularCohomologyEquiv`:
  `Hᵐ(B; M) × Hᵐ(B; M) ≃ Hᵐ(B × (F ∖ {0}); M)`, `(b, c) ↦ π^* b + σ ⌣ π^* c`.
* `TauCeti.prodThomPairSingularCohomologyLineEquiv`:
  `Hⁿ(B; M) ≃ Hⁿ⁺¹(B × F, B × (F ∖ {0}); M)`, `c ↦ δ (σ ⌣ π^* c)`.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof (the Thom
  isomorphism, first for a product bundle and then by Mayer–Vietoris).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Topology

universe w

namespace TauCeti

variable {k : Type w} [CommRing k] (M : ModuleCat.{w} k)

variable {B : Type w} [TopologicalSpace B]
  {F : Type w} [TopologicalSpace F] [AddCommMonoid F] [Module ℝ F]

/-! ### The two half-lines -/

section Halves

/-- `e⁻¹ t` is nonzero for `t ≠ 0`. -/
private lemma symm_apply_ne_zero (e : F ≃L[ℝ] ℝ) {t : ℝ} (ht : t ≠ 0) : e.symm t ≠ 0 :=
  EmbeddingLike.map_ne_zero_iff.2 ht

/-- The value of `e` at a point of the punctured product bundle is nonzero. -/
private lemma apply_snd_ne_zero (e : F ≃L[ℝ] ℝ) (p : (prodThomPair B F).snd) : e p.1.2 ≠ 0 :=
  EmbeddingLike.map_ne_zero_iff.2 p.2

/-- Two copies of `B`, indexed by the half-lines `e > 0` (`true`) and `e < 0` (`false`). -/
private abbrev halves (B : Type w) [TopologicalSpace B] : ULift.{w} Bool → TopCat.{w} :=
  fun _ ↦ TopCat.of B

/-- The value `1` or `-1` of `e` on the section of a half-line. -/
private def halfSign (i : ULift.{w} Bool) : ℝ := if i.down then 1 else -1

private lemma halfSign_ne_zero (i : ULift.{w} Bool) : halfSign i ≠ 0 := by
  rcases i with ⟨_ | _⟩ <;> norm_num [halfSign]

/-- The map from two copies of `B` to `B × (F ∖ {0})`, the section `b ↦ (b, e⁻¹ 1)` on the copy
`true` and `b ↦ (b, e⁻¹ (-1))` on the copy `false`. -/
private def halvesMap (e : F ≃L[ℝ] ℝ) : C(Σ i, halves B i, (prodThomPair B F).snd) :=
  ⟨fun p ↦ ⟨(p.2, e.symm (halfSign p.1)), symm_apply_ne_zero e (halfSign_ne_zero p.1)⟩,
    continuous_sigma fun _ ↦ by fun_prop⟩

private lemma halvesMap_apply (e : F ≃L[ℝ] ℝ) (p : Σ i, halves B i) :
    (halvesMap e p).1 = (p.2, e.symm (halfSign p.1)) :=
  (rfl)

/-- The half-line containing a point of `B × (F ∖ {0})` is locally constant. -/
private lemma eventually_decide_pos_eq (e : F ≃L[ℝ] ℝ) (p : (prodThomPair B F).snd) :
    ∀ᶠ q in 𝓝 p, decide (0 < e q.1.2) = decide (0 < e p.1.2) := by
  have hc : Continuous fun q : (prodThomPair B F).snd ↦ e q.1.2 := by fun_prop
  rcases (apply_snd_ne_zero e p).lt_or_gt with hp | hp
  · filter_upwards [hc.continuousAt.eventually (gt_mem_nhds hp)] with q hq
    simp [hq.le.not_gt, hp.le.not_gt]
  · filter_upwards [hc.continuousAt.eventually (lt_mem_nhds hp)] with q hq
    simp [hq, hp]

/-- The map from `B × (F ∖ {0})` to two copies of `B` recording the half-line of a point. -/
private def halvesInv (e : F ≃L[ℝ] ℝ) : C((prodThomPair B F).snd, Σ i, halves B i) :=
  ⟨fun p ↦ ⟨⟨decide (0 < e p.1.2)⟩, p.1.1⟩,
    continuous_iff_continuousAt.2 fun p ↦
      ((continuous_sigmaMk (σ := fun i ↦ halves B i) (i := ⟨decide (0 < e p.1.2)⟩)).comp
        (by fun_prop : Continuous fun q : (prodThomPair B F).snd ↦ q.1.1)).continuousAt.congr
        ((eventually_decide_pos_eq e p).mono fun q hq ↦ by simp only [Function.comp_apply, hq])⟩

private lemma halvesInv_apply (e : F ≃L[ℝ] ℝ) (p : (prodThomPair B F).snd) :
    halvesInv e p = ⟨⟨decide (0 < e p.1.2)⟩, p.1.1⟩ :=
  (rfl)

/-- The factor `(1 - t) + t / |a|` contracting `a` onto `±1` is positive. -/
private lemma one_sub_add_mul_inv_abs_pos {a : ℝ} (ha : a ≠ 0) (t : unitInterval) :
    0 < 1 - (t : ℝ) + t * |a|⁻¹ := by
  have ha' : 0 < |a|⁻¹ := inv_pos.2 (abs_pos.2 ha)
  rcases eq_or_lt_of_le t.2.2 with ht | ht
  · rw [ht]
    linarith
  · nlinarith [t.2.1]

/-- `a / |a|` is the sign `±1` of the half-line of `a ≠ 0`. -/
private lemma inv_abs_mul_self {a : ℝ} (ha : a ≠ 0) :
    |a|⁻¹ * a = halfSign (⟨decide (0 < a)⟩ : ULift.{w} Bool) := by
  rcases ha.lt_or_gt with ha | ha
  · simp [halfSign, abs_of_neg ha, ha.le.not_gt, ha.ne]
  · simp [halfSign, abs_of_pos ha, ha, ha.ne']

/-- The straight-line homotopy in `F ∖ {0}`, fibrewise over `B`, from the identity of
`B × (F ∖ {0})` to the retraction onto the two sections at `e⁻¹ (±1)`. -/
private def halvesHomotopy (e : F ≃L[ℝ] ℝ) :
    ContinuousMap.Homotopy (ContinuousMap.id (prodThomPair B F).snd)
      ((halvesMap e).comp (halvesInv e)) where
  toFun x :=
    have hx := apply_snd_ne_zero e x.2
    ⟨(x.2.1.1, e.symm ((1 - (x.1 : ℝ) + x.1 * |e x.2.1.2|⁻¹) * e x.2.1.2)),
      symm_apply_ne_zero e (mul_ne_zero (one_sub_add_mul_inv_abs_pos hx x.1).ne' hx)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop (disch := exact fun x ↦ abs_ne_zero.2 (apply_snd_ne_zero e x.2))
  map_zero_left x := Subtype.ext (Prod.ext rfl (by simp))
  map_one_left x := Subtype.ext (Prod.ext rfl (by
    simpa [halvesMap_apply, halvesInv_apply] using
      congrArg e.symm (inv_abs_mul_self (apply_snd_ne_zero e x))))

/-- `B × (F ∖ {0})` is homotopy equivalent to two disjoint copies of `B`. -/
private def halvesHomotopyEquiv (e : F ≃L[ℝ] ℝ) :
    ContinuousMap.HomotopyEquiv (Σ i, halves B i) (prodThomPair B F).snd where
  toFun := halvesMap e
  invFun := halvesInv e
  left_inv := by
    have : (halvesInv (B := B) e).comp (halvesMap e) = ContinuousMap.id _ :=
      ContinuousMap.ext fun ⟨⟨i⟩, b⟩ ↦ by
        cases i <;> simp [halvesMap_apply, halvesInv_apply, halfSign, Sigma.ext_iff]
    rw [this]
  right_inv := ⟨(halvesHomotopy e).symm⟩

/-- Two copies of `B` include into `B × (F ∖ {0})` as the sections at `e⁻¹ 1` and `e⁻¹ (-1)`. -/
private lemma sigmaι_comp_halvesMap (e : F ≃L[ℝ] ℝ) (i : ULift.{w} Bool) :
    TopCat.sigmaι.{w, w} (halves B) i ≫ TopCat.ofHom (halvesMap e) =
      prodThomPairPuncturedSection B F (symm_apply_ne_zero e (halfSign_ne_zero i)) :=
  -- `TopCat.sigmaι` is `Sigma.mk i` by definition, so the composite sends `b` to
  -- `halvesMap e ⟨i, b⟩ = (b, e.symm (halfSign i))`.
  TopCat.ext fun b ↦ Subtype.ext <| (halvesMap_apply e ⟨i, b⟩).trans
    (prodThomPairPuncturedSection_apply _ _ b).symm

end Halves

/-! ### The class of the half-line `e > 0` -/

section Class

/-- Along a path in `B × (F ∖ {0})`, `e` keeps its sign: the half-line of a point is locally
constant. -/
private lemma pos_iff_of_joined (e : F ≃L[ℝ] ℝ) {p q : (prodThomPair B F).snd}
    (h : Joined p q) : 0 < e p.1.2 ↔ 0 < e q.1.2 := by
  have hloc : IsLocallyConstant fun p : (prodThomPair B F).snd ↦ decide (0 < e p.1.2) :=
    (IsLocallyConstant.iff_eventually_eq _).2 (eventually_decide_pos_eq e)
  simpa using (hloc.comp_continuous h.somePath.continuous).apply_eq_of_preconnectedSpace 0 1

variable (k B) in
/-- **The class of the half-line `e > 0`**: the class of `H⁰(B × (F ∖ {0}); k)` with the value `1`
at the points `(b, x)` with `e x > 0` and `0` at those with `e x < 0`
(`TauCeti.singularCohomologyZeroEval_prodThomPairPuncturedLineClass`). It exists because these
values are constant on the path components. -/
def prodThomPairPuncturedLineClass (e : F ≃L[ℝ] ℝ) :
    (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0 :=
  (exists_singularCohomologyZeroEval_eq
    (fun p : (prodThomPair B F).snd ↦ if 0 < e p.1.2 then (1 : k) else 0)
    fun _ _ h ↦ by simp only [pos_iff_of_joined e h]).choose

/-- The class `TauCeti.prodThomPairPuncturedLineClass` has the value `1` at `(b, x)` if `e x > 0`
and `0` otherwise. -/
@[simp]
theorem singularCohomologyZeroEval_prodThomPairPuncturedLineClass (e : F ≃L[ℝ] ℝ)
    (p : (prodThomPair B F).snd) :
    singularCohomologyZeroEval p (prodThomPairPuncturedLineClass k B e) =
      if 0 < e p.1.2 then 1 else 0 :=
  (exists_singularCohomologyZeroEval_eq
    (fun p : (prodThomPair B F).snd ↦ if 0 < e p.1.2 then (1 : k) else 0)
    fun _ _ h ↦ by simp only [pos_iff_of_joined e h]).choose_spec p

/-- Along the section at a vector `v` with `e v > 0`, the class of the half-line `e > 0` pulls back
to the unit class. -/
theorem singularCohomologyMap_prodThomPairPuncturedSection_prodThomPairPuncturedLineClass_of_pos
    (e : F ≃L[ℝ] ℝ) {v : F} (hv : v ≠ 0) (h : 0 < e v) :
    TopCat.singularCohomologyMap (prodThomPairPuncturedSection B F hv) 0
        (prodThomPairPuncturedLineClass k B e) =
      (TopCat.of B).singularCohomologyZeroOne :=
  singularCohomologyZero_ext fun b ↦ by
    rw [singularCohomologyZeroEval_naturality,
      singularCohomologyZeroEval_prodThomPairPuncturedLineClass, prodThomPairPuncturedSection_apply,
      singularCohomologyZeroEval_singularCohomologyZeroOne]
    simp [h]

/-- Along the section at a vector `v` with `e v ≤ 0`, the class of the half-line `e > 0` pulls back
to zero. -/
theorem singularCohomologyMap_prodThomPairPuncturedSection_prodThomPairPuncturedLineClass_of_nonpos
    (e : F ≃L[ℝ] ℝ) {v : F} (hv : v ≠ 0) (h : e v ≤ 0) :
    TopCat.singularCohomologyMap (prodThomPairPuncturedSection B F hv) 0
        (prodThomPairPuncturedLineClass k B e) = 0 :=
  singularCohomologyZero_ext fun b ↦ by
    rw [singularCohomologyZeroEval_naturality,
      singularCohomologyZeroEval_prodThomPairPuncturedLineClass, prodThomPairPuncturedSection_apply,
      map_zero]
    simp [h.not_gt]

/-- The class of the half-line `e > 0` is natural in the base. -/
@[simp]
theorem singularCohomologyMap_snd_prodThomPairMap_prodThomPairPuncturedLineClass
    {B' : Type w} [TopologicalSpace B'] (g : C(B, B')) (e : F ≃L[ℝ] ℝ) :
    TopCat.singularCohomologyMap (TopPair.Hom.snd (prodThomPairMap F g)) 0
        (prodThomPairPuncturedLineClass k B' e) = prodThomPairPuncturedLineClass k B e :=
  singularCohomologyZero_ext fun p ↦ by simp

end Class

/-! ### The cohomology of the punctured product bundle -/

section Punctured

/-- The section `b ↦ (b, e⁻¹ 1)` of the half-line `e > 0`. -/
private abbrev posSection (e : F ≃L[ℝ] ℝ) : TopCat.of B ⟶ (prodThomPair B F).snd :=
  prodThomPairPuncturedSection B F (symm_apply_ne_zero e one_ne_zero)

/-- The section `b ↦ (b, e⁻¹ (-1))` of the half-line `e < 0`. -/
private abbrev negSection (e : F ≃L[ℝ] ℝ) : TopCat.of B ⟶ (prodThomPair B F).snd :=
  prodThomPairPuncturedSection B F (symm_apply_ne_zero e (neg_ne_zero.2 one_ne_zero))

/-- **A class on `B × (F ∖ {0})` is determined by its pullbacks along the two sections** at
`e⁻¹ 1` and `e⁻¹ (-1)`: pulled back to two copies of `B`, along a homotopy equivalence, it is
determined by its restrictions to the copies. -/
private theorem singularCohomology_ext_of_sections (e : F ≃L[ℝ] ℝ) {m : ℕ}
    {y y' : (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m}
    (hpos : TopCat.singularCohomologyMap (posSection e) m y =
      TopCat.singularCohomologyMap (posSection e) m y')
    (hneg : TopCat.singularCohomologyMap (negSection e) m y =
      TopCat.singularCohomologyMap (negSection e) m y') :
    y = y' := by
  have : IsIso (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k) (M := M)
      (TopCat.ofHom (halvesMap (B := B) e)) m) :=
    (halvesHomotopyEquiv e).isIso_singularCohomologyMap _ k M m
  refine
    (asIso (TopCat.singularCohomologyMap (TopCat.ofHom (halvesMap e)) m)).toLinearEquiv.injective
    (Concrete.isLimit_ext _ (isLimitFanSingularCohomology (halves B) (ModuleCat.{w} k)
      (𝟙_ (ModuleCat.{w} k)) k M m) _ _ fun ⟨i⟩ ↦ ?_)
  simp only [Fan.mk_π_app, Iso.toLinearEquiv_apply, asIso_hom,
    ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, sigmaι_comp_halvesMap]
  rcases i with ⟨_ | _⟩
  exacts [hneg, hpos]

/-- The map `(b, c) ↦ π^* b + σ ⌣ π^* c` into the cohomology of the punctured product bundle. -/
private def lineMap (e : F ≃L[ℝ] ℝ) (m : ℕ) :
    ((TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m) →ₗ[k]
      (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m :=
  LinearMap.coprod (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) m).hom
    ((prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
        0 m m (zero_add m) (prodThomPairPuncturedLineClass k B e) ∘ₗ
      (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) m).hom)

private theorem lineMap_apply (e : F ≃L[ℝ] ℝ) (m : ℕ)
    (bc : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m) :
    lineMap M e m bc =
      TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) m bc.1 +
        (prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
          0 m m (zero_add m) (prodThomPairPuncturedLineClass k B e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) m bc.2) :=
  -- `lineMap` is this sum by definition.
  (rfl)

/-- Along the section at `e⁻¹ 1`, `π^* b + σ ⌣ π^* c` pulls back to `b + c`. -/
private theorem singularCohomologyMap_posSection_lineMap (e : F ≃L[ℝ] ℝ) (m : ℕ)
    (bc : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m) :
    TopCat.singularCohomologyMap (posSection e) m (lineMap M e m bc) = bc.1 + bc.2 := by
  rw [lineMap_apply, map_add, ← TopCat.singularCup_naturality,
    singularCohomologyMap_prodThomPairPuncturedSection_prodThomPairPuncturedLineClass_of_pos e _
      (by simp), leftInverse_singularCohomologyMap_prodThomPairPuncturedSection,
    leftInverse_singularCohomologyMap_prodThomPairPuncturedSection,
    TopCat.singularCup_singularCohomologyZeroOne_left]

/-- Along the section at `e⁻¹ (-1)`, `π^* b + σ ⌣ π^* c` pulls back to `b`. -/
private theorem singularCohomologyMap_negSection_lineMap (e : F ≃L[ℝ] ℝ) (m : ℕ)
    (bc : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m) :
    TopCat.singularCohomologyMap (negSection e) m (lineMap M e m bc) = bc.1 := by
  rw [lineMap_apply, map_add, ← TopCat.singularCup_naturality,
    singularCohomologyMap_prodThomPairPuncturedSection_prodThomPairPuncturedLineClass_of_nonpos e _
      (by simp), leftInverse_singularCohomologyMap_prodThomPairPuncturedSection, map_zero,
    LinearMap.zero_apply, add_zero]

private theorem bijective_lineMap (e : F ≃L[ℝ] ℝ) (m : ℕ) :
    Function.Bijective (lineMap (B := B) M e m) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun bc hbc ↦ ?_, fun y ↦ ?_⟩
  · have hpos := singularCohomologyMap_posSection_lineMap M e m bc
    have hneg := singularCohomologyMap_negSection_lineMap M e m bc
    rw [hbc, map_zero] at hpos hneg
    exact Prod.ext hneg.symm (by rw [← hneg, zero_add] at hpos; exact hpos.symm)
  · refine ⟨(TopCat.singularCohomologyMap (negSection e) m y,
      TopCat.singularCohomologyMap (posSection e) m y -
        TopCat.singularCohomologyMap (negSection e) m y), ?_⟩
    refine singularCohomology_ext_of_sections M e ?_ ?_
    · rw [singularCohomologyMap_posSection_lineMap, add_sub_cancel]
    · rw [singularCohomologyMap_negSection_lineMap]

variable (B) in
/-- **The cohomology of the punctured product line bundle.** For a continuous linear equivalence
`e : F ≃L[ℝ] ℝ`, every class of `Hᵐ(B × (F ∖ {0}); M)` is uniquely `π^* b + σ ⌣ π^* c` with `b`
and `c` in `Hᵐ(B; M)`, where `π` is the projection to `B` and `σ` is the class of the half-line
`e > 0`, `TauCeti.prodThomPairPuncturedLineClass`
(`TauCeti.prodThomPairPuncturedLineSingularCohomologyEquiv_apply`). -/
def prodThomPairPuncturedLineSingularCohomologyEquiv (e : F ≃L[ℝ] ℝ) (m : ℕ) :
    ((TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m) ≃ₗ[k]
      (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m :=
  LinearEquiv.ofBijective (lineMap M e m) (bijective_lineMap M e m)

/-- The decomposition `TauCeti.prodThomPairPuncturedLineSingularCohomologyEquiv` sends `(b, c)` to
`π^* b + σ ⌣ π^* c`. -/
@[simp]
theorem prodThomPairPuncturedLineSingularCohomologyEquiv_apply (e : F ≃L[ℝ] ℝ) (m : ℕ)
    (bc : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m) :
    prodThomPairPuncturedLineSingularCohomologyEquiv M B e m bc =
      TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) m bc.1 +
        (prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
          0 m m (zero_add m) (prodThomPairPuncturedLineClass k B e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) m bc.2) :=
  lineMap_apply M e m bc

end Punctured

/-! ### The cohomology of the Thom pair -/

section ThomPair

/-- The map `c ↦ δ (σ ⌣ π^* c)`, written as `δ ∘ D ∘ inr` for the decomposition `D` of the
cohomology of the punctured product bundle. -/
private def lineDeltaMap (e : F ≃L[ℝ] ℝ) (n m : ℕ) (h : n + 1 = m) :
    (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n →ₗ[k]
      (prodThomPair B F).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m :=
  ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M n m).hom ∘ₗ
    (prodThomPairPuncturedLineSingularCohomologyEquiv M B e n).toLinearMap ∘ₗ
      LinearMap.inr k _ _

private theorem lineDeltaMap_apply (e : F ≃L[ℝ] ℝ) (n m : ℕ) (h : n + 1 = m)
    (c : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    lineDeltaMap M e n m h c =
      ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M n m)
        ((prodThomPairPuncturedLineSingularCohomologyEquiv M B e n) (0, c)) :=
  -- `lineDeltaMap` is this composite by definition.
  (rfl)

/-- `c ↦ δ (σ ⌣ π^* c)` is bijective, since the decomposition is the pullback along the projection
on its first factor (`TauCeti.bijective_prodThomPair_singularCohomologyδ_comp_inr`). -/
private theorem bijective_lineDeltaMap (e : F ≃L[ℝ] ℝ) (n m : ℕ) (h : n + 1 = m) :
    Function.Bijective (lineDeltaMap (B := B) M e n m h) := by
  have := e.toHomeomorph.contractibleSpace
  exact bijective_prodThomPair_singularCohomologyδ_comp_inr _ M
    (symm_apply_ne_zero e one_ne_zero) h
    (prodThomPairPuncturedLineSingularCohomologyEquiv M B e n) fun b ↦ by simp

variable (B) in
/-- **The cohomology of the Thom pair of a product line bundle.** Let `e : F ≃L[ℝ] ℝ` be a
continuous linear equivalence, so that `F` has dimension one. Then, for every degree `n` and
`m = n + 1`, `c ↦ δ (σ ⌣ π^* c)` is a `k`-linear equivalence
`Hⁿ(B; M) ≃ Hᵐ(B × F, B × (F ∖ {0}); M)`, where `π : B × (F ∖ {0}) → B` is the projection,
`σ ∈ H⁰(B × (F ∖ {0}); k)` is the class of the half-line `e > 0`,
`TauCeti.prodThomPairPuncturedLineClass`, and `δ` is the connecting morphism of the pair
(`TauCeti.prodThomPairSingularCohomologyLineEquiv_apply`). -/
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
      ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M n m)
        ((prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
          0 n n (zero_add n) (prodThomPairPuncturedLineClass k B e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n c)) := by
  rw [prodThomPairSingularCohomologyLineEquiv, LinearEquiv.ofBijective_apply, lineDeltaMap_apply,
    prodThomPairPuncturedLineSingularCohomologyEquiv_apply, map_zero, zero_add]

/-- The equivalence `TauCeti.prodThomPairSingularCohomologyLineEquiv` sends the unit
`1 ∈ H⁰(B; k)` to `δ σ`, where `σ` is `TauCeti.prodThomPairPuncturedLineClass`. -/
theorem prodThomPairSingularCohomologyLineEquiv_singularCohomologyZeroOne (e : F ≃L[ℝ] ℝ) :
    (prodThomPairSingularCohomologyLineEquiv (𝟙_ (ModuleCat.{w} k)) B e 0 1)
        (TopCat.of B).singularCohomologyZeroOne =
      ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0 1)
        (prodThomPairPuncturedLineClass k B e) := by
  rw [prodThomPairSingularCohomologyLineEquiv_apply,
    singularCohomologyMap_singularCohomologyZeroOne,
    TopCat.singularCup_singularCohomologyZeroOne_right]

end ThomPair

/-! ### Naturality in the base -/

section Naturality

variable {B' : Type w} [TopologicalSpace B'] (g : C(B, B'))

/-- The decomposition `TauCeti.prodThomPairPuncturedLineSingularCohomologyEquiv` is natural in the
base: restricting `π^* b + σ ⌣ π^* c` along the map induced by `g : B → B'` gives
`π^* (g^* b) + σ ⌣ π^* (g^* c)`. -/
theorem prodThomPairPuncturedLineSingularCohomologyEquiv_naturality (e : F ≃L[ℝ] ℝ) (m : ℕ)
    (bc : (TopCat.of B').singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m ×
      (TopCat.of B').singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m) :
    TopCat.singularCohomologyMap (TopPair.Hom.snd (prodThomPairMap F g)) m
        (prodThomPairPuncturedLineSingularCohomologyEquiv M B' e m bc) =
      prodThomPairPuncturedLineSingularCohomologyEquiv M B e m
        (TopCat.singularCohomologyMap (TopCat.ofHom g) m bc.1,
          TopCat.singularCohomologyMap (TopCat.ofHom g) m bc.2) := by
  rw [prodThomPairPuncturedLineSingularCohomologyEquiv_apply,
    prodThomPairPuncturedLineSingularCohomologyEquiv_apply, map_add,
    ← TopCat.singularCup_naturality,
    singularCohomologyMap_snd_prodThomPairMap_prodThomPairPuncturedLineClass]
  simp only [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    snd_prodThomPairMap_comp_prodThomPairPuncturedProj]

/-- **Naturality of the cohomology of the Thom pair of a product line bundle.** The equivalence
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
    TopPair.singularCohomologyδ_naturality (prodThomPairMap F g) n m,
    ConcreteCategory.comp_apply,
    prodThomPairPuncturedLineSingularCohomologyEquiv_naturality M g e n, map_zero]

end Naturality

end TauCeti

/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Rational.PiecewiseAffine
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Finite semilinear families and finite branches

A finite semilinear family is a finite collection of charts. Each chart has a rational
semilinear domain in a real vector space `V` with an integral lattice and an evaluation map
to a real vector space `W` with its own integral lattice. The evaluation is piecewise
affine: finitely many rational semilinear pieces cover the domain, and on each piece the
evaluation is an affine map whose linear part is rational and whose offset is unrestricted.
Charts need not be proper and fibers need not be finite. The fiber over a point of `W`
records the chart together with
the preimage point, so overlapping images in different charts are not identified.

The evaluation of a chart is a map on its domain. Two families are equal if their domains
and evaluations agree at every chart label of a common index type. A family consists of
finite branches when on every chart the domain is a finite
union of locally closed rational-normal polyhedra. Its evaluation agrees on each piece with
an affine map whose linear part is rational and which is injective on that piece.
Such domains need not be closed, and a finite branch has finite
fibers.

## Main definitions

* `FiniteSemilinearFamily`: finitely many charts with rational piecewise-affine evaluation.
* `FiniteSemilinearFamily.fiber`: the fiber over a point, indexed by chart and preimage.
* `FiniteSemilinearFamily.IsFiniteBranch`: every chart is a finite branch.

## Main results

* `FiniteSemilinearFamily.sum`, `FiniteSemilinearFamily.restrict` and
  `FiniteSemilinearFamily.postcomp`: disjoint union, restriction to chartwise rational semilinear
  sets and post-composition with an affine map with rational linear part, with their
  fibers (`fiberSumEquiv`, `fiberRestrictEquiv`, `fiberPostcompEquiv`).
* `FiniteSemilinearFamily.isFiniteBranch_sum_iff`, `FiniteSemilinearFamily.IsFiniteBranch.restrict`:
  finite branches are stable under disjoint union and restriction to rational semilinear sets.
* `FiniteSemilinearFamily.IsFiniteBranch.finite_fiber`: a family of finite branches has finite
  fibers.

Adapted from `Mei/Geometry/Convex/Polyhedron/Rational/SemilinearFamily/Basic.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0).
-/

public section

open TauCeti (IsLocallyClosedPolyhedron IsRationalSemilinear
  isLocallyClosedPolyhedron_setOf_forall_neg)

namespace TauCeti

variable {N V N' W N'' X : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [AddCommGroup N'] [AddCommGroup W] [Module ℝ W] [AddCommGroup N''] [AddCommGroup X]
  [Module ℝ X] {i : N →+ V} {i' : N' →+ W} {i'' : N'' →+ X}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {h'' : TauCeti.Toric.IsIntegralLattice i''}

variable (h h') in
/-- A finite semilinear family: finitely many charts, each with a rational semilinear domain
in `V` and a rational piecewise-affine evaluation map on that domain to `W`. -/
structure FiniteSemilinearFamily (ι : Type*) [Finite ι] where
  /-- The domain of each chart. -/
  domain : ι → Set V
  /-- The evaluation map of each chart, defined on its domain. -/
  eval : ∀ c, domain c → W
  /-- Each chart is piecewise affine with rational linear parts on its domain. -/
  isRationalPiecewiseAffine : ∀ c, IsRationalPiecewiseAffine h h' (domain c) (eval c)

namespace FiniteSemilinearFamily

variable {ι κ : Type*} [Finite ι] [Finite κ] (F : FiniteSemilinearFamily h h' ι)
  (G : FiniteSemilinearFamily h h' κ)

/-- Two families are equal when their domains and evaluations agree chart by chart
at each label of the common index type. -/
@[ext]
theorem ext {F G : FiniteSemilinearFamily h h' ι} (hd : ∀ c, F.domain c = G.domain c)
    (he : ∀ c (x : V) (hF : x ∈ F.domain c) (hG : x ∈ G.domain c),
      F.eval c ⟨x, hF⟩ = G.eval c ⟨x, hG⟩) : F = G := by
  obtain ⟨d, e, p⟩ := F
  obtain ⟨d', e', p'⟩ := G
  obtain rfl : d = d' := funext hd
  obtain rfl : e = e' := funext fun c => funext fun x => he c x.val x.property x.property
  rfl

/-- The fiber of a family over `w`: a chart together with a point of its domain evaluating to
`w`. Points of different charts are never identified. -/
structure fiber (w : W) where
  /-- The chart label of the preimage. -/
  chart : ι
  /-- The point in the domain of this chart. -/
  point : F.domain chart
  /-- This point evaluates to the specified target. -/
  eval_eq : F.eval chart point = w

/-- Fiber points are equal when their chart labels and ambient points agree. -/
@[ext]
theorem fiber.ext {w : W} {x y : F.fiber w} (hc : x.chart = y.chart)
    (hp : (x.point : V) = y.point) : x = y := by
  obtain ⟨c, x, hx⟩ := x
  obtain ⟨d, y, hy⟩ := y
  cases hc
  obtain rfl := Subtype.ext hp
  rfl

/-- The representation equivalence used to apply the generic dependent-sum APIs. -/
private def fiberSigmaEquiv (w : W) : F.fiber w ≃ Σ c, {x : F.domain c // F.eval c x = w} where
  toFun x := ⟨x.chart, x.point, x.eval_eq⟩
  invFun x := ⟨x.1, x.2.val, x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Transporting a fiber point along equality of families preserves its chart label. -/
@[simp]
theorem fiber_cast_chart {F G : FiniteSemilinearFamily h h' ι} (e : F = G)
    (w : W) (z : F.fiber w) :
    (cast (congrArg (fun F : FiniteSemilinearFamily h h' ι => F.fiber w) e) z).chart = z.chart := by
  subst G
  rfl

/-- A family whose charts are all finite branches. -/
def IsFiniteBranch : Prop := ∀ c, IsFiniteBranchOn h h' (F.domain c) (F.eval c)

/-- A finite semilinear family consists of finite branches exactly when every chart does. -/
theorem isFiniteBranch_iff :
    F.IsFiniteBranch ↔ ∀ c, IsFiniteBranchOn h h' (F.domain c) (F.eval c) := (Iff.rfl)

/-- A family of finite branches has finite fibers. -/
theorem IsFiniteBranch.finite_fiber {F : FiniteSemilinearFamily h h' ι} (hF : F.IsFiniteBranch)
    (w : W) : Finite (F.fiber w) := by
  have := fun c => (hF c).finite_fiber w
  exact Finite.of_equiv _ (F.fiberSigmaEquiv w).symm

/-- The family with a single chart. -/
def single {D : Set V} {f : D → W} (hf : IsRationalPiecewiseAffine h h' D f) :
    FiniteSemilinearFamily h h' Unit where
  domain _ := D
  eval _ := f
  isRationalPiecewiseAffine _ := hf

/-- A single-chart family has the specified domain. -/
@[simp]
theorem single_domain {D : Set V} {f : D → W} (hf : IsRationalPiecewiseAffine h h' D f)
    (c : Unit) : (single hf).domain c = D := (rfl)

/-- A single-chart family has the specified domain-indexed evaluation. -/
@[simp]
theorem single_eval {D : Set V} {f : D → W} (hf : IsRationalPiecewiseAffine h h' D f)
    (c : Unit) (x : (single hf).domain c) :
    (single hf).eval c x = f ⟨x.val, by simpa only [single_domain] using x.property⟩ := (rfl)

/-- A single-chart family consists of finite branches exactly when its chart is a finite
branch. -/
@[simp]
theorem isFiniteBranch_single_iff {D : Set V} {f : D → W}
    (hf : IsRationalPiecewiseAffine h h' D f) :
    (single hf).IsFiniteBranch ↔ IsFiniteBranchOn h h' D f :=
  Unique.forall_iff

/-- The fiber of a single chart is the fiber of its evaluation map. -/
def fiberSingleEquiv {D : Set V} {f : D → W} (hf : IsRationalPiecewiseAffine h h' D f)
    (w : W) : (single hf).fiber w ≃ {x : D // f x = w} :=
  (fiberSigmaEquiv _ w).trans (Equiv.uniqueSigma _)

/-- The single-chart fiber comparison retains the ambient point. -/
@[simp]
theorem fiberSingleEquiv_apply_point {D : Set V} {f : D → W}
    (hf : IsRationalPiecewiseAffine h h' D f) (w : W) (z : (single hf).fiber w) :
    ((fiberSingleEquiv hf w z).val : V) = z.point := by
  obtain ⟨⟨⟩, x, hx⟩ := z
  rfl

/-- The inverse single-chart fiber comparison retains the ambient point. -/
@[simp]
theorem fiberSingleEquiv_symm_apply_point {D : Set V} {f : D → W}
    (hf : IsRationalPiecewiseAffine h h' D f) (w : W) (z : {x : D // f x = w}) :
    (((fiberSingleEquiv hf w).symm z).point : V) = z.val := (rfl)

/-- The disjoint union of two families, with the charts of both. -/
def sum : FiniteSemilinearFamily h h' (ι ⊕ κ) where
  domain := Sum.elim F.domain G.domain
  eval := fun
    | .inl c => F.eval c
    | .inr c => G.eval c
  isRationalPiecewiseAffine := by
    rintro (c | c)
    exacts [F.isRationalPiecewiseAffine c, G.isRationalPiecewiseAffine c]

/-- The left charts of a disjoint union retain their original domains. -/
@[simp]
theorem sum_domain_inl (c : ι) : (F.sum G).domain (.inl c) = F.domain c := (rfl)

/-- The right charts of a disjoint union retain their original domains. -/
@[simp]
theorem sum_domain_inr (c : κ) : (F.sum G).domain (.inr c) = G.domain c := (rfl)

/-- The left charts of a disjoint union retain their original evaluations. -/
@[simp]
theorem sum_eval_inl (c : ι) (x : (F.sum G).domain (.inl c)) :
    (F.sum G).eval (.inl c) x = F.eval c ⟨x.val, F.sum_domain_inl G c ▸ x.property⟩ := (rfl)

/-- The right charts of a disjoint union retain their original evaluations. -/
@[simp]
theorem sum_eval_inr (c : κ) (x : (F.sum G).domain (.inr c)) :
    (F.sum G).eval (.inr c) x = G.eval c ⟨x.val, F.sum_domain_inr G c ▸ x.property⟩ := (rfl)

/-- The fiber of a disjoint union is the disjoint union of the fibers. -/
def fiberSumEquiv (w : W) : (F.sum G).fiber w ≃ F.fiber w ⊕ G.fiber w :=
  ((F.sum G).fiberSigmaEquiv w).trans
    ((Equiv.sumSigmaDistrib fun c => {x : (F.sum G).domain c // (F.sum G).eval c x = w}).trans
      (Equiv.sumCongr (F.fiberSigmaEquiv w).symm (G.fiberSigmaEquiv w).symm))

/-- The inverse fiber comparison preserves the chart label on the left summand. -/
@[simp]
theorem fiberSumEquiv_symm_apply_inl_chart (w : W) (z : F.fiber w) :
    ((F.fiberSumEquiv G w).symm (.inl z)).chart = .inl z.chart := by
  change ((Equiv.sumSigmaDistrib
    (fun c => {x : (F.sum G).domain c // (F.sum G).eval c x = w})).symm
      (.inl ⟨z.chart, ⟨z.point, z.eval_eq⟩⟩)).1 = .inl z.chart
  rw [Equiv.sumSigmaDistrib_symm_apply]
  rfl

/-- The inverse fiber comparison preserves the chart label on the right summand. -/
@[simp]
theorem fiberSumEquiv_symm_apply_inr_chart (w : W) (z : G.fiber w) :
    ((F.fiberSumEquiv G w).symm (.inr z)).chart = .inr z.chart := by
  change ((Equiv.sumSigmaDistrib
    (fun c => {x : (F.sum G).domain c // (F.sum G).eval c x = w})).symm
      (.inr ⟨z.chart, ⟨z.point, z.eval_eq⟩⟩)).1 = .inr z.chart
  rw [Equiv.sumSigmaDistrib_symm_apply]
  rfl

/-- The inverse fiber comparison retains the ambient point on the left summand. -/
@[simp]
theorem fiberSumEquiv_symm_apply_inl_point (w : W) (z : F.fiber w) :
    (((F.fiberSumEquiv G w).symm (.inl z)).point : V) = z.point := by
  change (((Equiv.sumSigmaDistrib
    (fun c => {x : (F.sum G).domain c // (F.sum G).eval c x = w})).symm
      (.inl ⟨z.chart, ⟨z.point, z.eval_eq⟩⟩)).2.val : V) = z.point
  rw [Equiv.sumSigmaDistrib_symm_apply]
  rfl

/-- The inverse fiber comparison retains the ambient point on the right summand. -/
@[simp]
theorem fiberSumEquiv_symm_apply_inr_point (w : W) (z : G.fiber w) :
    (((F.fiberSumEquiv G w).symm (.inr z)).point : V) = z.point := by
  change (((Equiv.sumSigmaDistrib
    (fun c => {x : (F.sum G).domain c // (F.sum G).eval c x = w})).symm
      (.inr ⟨z.chart, ⟨z.point, z.eval_eq⟩⟩)).2.val : V) = z.point
  rw [Equiv.sumSigmaDistrib_symm_apply]
  rfl

/-- Forward transport retains the chart label, interpreted in the disjoint index type. -/
@[simp]
theorem fiberSumEquiv_apply_chart (w : W) (z : (F.sum G).fiber w) :
    Sum.elim (fun x => Sum.inl x.chart) (fun x => Sum.inr x.chart)
      (F.fiberSumEquiv G w z) = z.chart := by
  obtain ⟨(c | c), x, hx⟩ := z
  all_goals
    simp only [fiberSumEquiv, Equiv.trans_apply]
    rw [Equiv.sumSigmaDistrib_apply]
    rfl

/-- Forward transport retains the ambient point regardless of the summand. -/
@[simp]
theorem fiberSumEquiv_apply_point (w : W) (z : (F.sum G).fiber w) :
    Sum.elim (fun x => (x.point : V)) (fun x => (x.point : V))
      (F.fiberSumEquiv G w z) = z.point := by
  obtain ⟨(c | c), x, hx⟩ := z
  all_goals
    simp only [fiberSumEquiv, Equiv.trans_apply]
    rw [Equiv.sumSigmaDistrib_apply]
    rfl

/-- Extended fiber cardinalities add under disjoint union, including infinite fibers. -/
theorem enat_card_fiber_sum (w : W) :
    ENat.card ((F.sum G).fiber w) = ENat.card (F.fiber w) + ENat.card (G.fiber w) := by
  rw [ENat.card_congr (F.fiberSumEquiv G w), ENat.card_sum]

/-- A disjoint union of families with finite fibers has finite fibers. -/
instance (w : W) [Finite (F.fiber w)] [Finite (G.fiber w)] :
    Finite ((F.sum G).fiber w) :=
  Finite.of_equiv _ (F.fiberSumEquiv G w).symm

/-- Natural-number fiber counts add when both fibers over `w` are finite.
For the unrestricted count, including infinite fibers, see `enat_card_fiber_sum`. -/
theorem nat_card_fiber_sum (w : W) [Finite (F.fiber w)] [Finite (G.fiber w)] :
    Nat.card ((F.sum G).fiber w) = Nat.card (F.fiber w) + Nat.card (G.fiber w) := by
  rw [Nat.card_congr (F.fiberSumEquiv G w), Nat.card_sum]

/-- A disjoint union consists of finite branches exactly when both families do. -/
@[simp]
theorem isFiniteBranch_sum_iff :
    (F.sum G).IsFiniteBranch ↔ F.IsFiniteBranch ∧ G.IsFiniteBranch :=
  Sum.forall

/-- Restriction of each chart to its own rational semilinear set. -/
def restrict (P : ι → Set V) (hP : ∀ c, IsRationalSemilinear h (P c)) :
    FiniteSemilinearFamily h h' ι where
  domain c := F.domain c ∩ P c
  eval c := Set.domRestrict₂ (π := fun _ : V => W) Set.inter_subset_left (F.eval c)
  isRationalPiecewiseAffine c := (F.isRationalPiecewiseAffine c).inter (hP c)

/-- Restricting a family intersects each domain with the restricting set. -/
@[simp]
theorem restrict_domain (P : ι → Set V) (hP : ∀ c, IsRationalSemilinear h (P c)) (c : ι) :
    (F.restrict P hP).domain c = F.domain c ∩ P c := (rfl)

/-- Restriction evaluates a point using its original domain membership. -/
@[simp]
theorem restrict_eval (P : ι → Set V) (hP : ∀ c, IsRationalSemilinear h (P c)) (c : ι)
    (x : (F.restrict P hP).domain c) :
    (F.restrict P hP).eval c x =
      Set.domRestrict₂ (π := fun _ : V => W)
        (Set.inter_subset_left : F.domain c ∩ P c ⊆ F.domain c) (F.eval c)
        ⟨x.val, by simpa only [restrict_domain] using x.property⟩ := (rfl)

/-- The fiber of a restriction consists of the original fiber points in the restricting set. -/
def fiberRestrictEquiv (P : ι → Set V) (hP : ∀ c, IsRationalSemilinear h (P c)) (w : W) :
    (F.restrict P hP).fiber w ≃ {p : F.fiber w // (p.point : V) ∈ P p.chart} where
  toFun p := ⟨⟨p.chart, ⟨p.point.val, p.point.property.1⟩, p.eval_eq⟩, p.point.property.2⟩
  invFun p := ⟨p.val.chart, ⟨p.val.point.val, p.val.point.property, p.property⟩, p.val.eval_eq⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Restriction preserves the chart label. -/
@[simp]
theorem fiberRestrictEquiv_apply_chart (P : ι → Set V) (hP : ∀ c, IsRationalSemilinear h (P c))
    (w : W) (z : (F.restrict P hP).fiber w) :
    (F.fiberRestrictEquiv P hP w z).val.chart = z.chart := (rfl)

/-- Restriction retains the ambient point. -/
@[simp]
theorem fiberRestrictEquiv_apply_point (P : ι → Set V)
    (hP : ∀ c, IsRationalSemilinear h (P c)) (w : W) (z : (F.restrict P hP).fiber w) :
    ((F.fiberRestrictEquiv P hP w z).val.point : V) = z.point := (rfl)

/-- Inverse restriction retains the chart label. -/
@[simp]
theorem fiberRestrictEquiv_symm_apply_chart (P : ι → Set V)
    (hP : ∀ c, IsRationalSemilinear h (P c)) (w : W)
    (z : {p : F.fiber w // (p.point : V) ∈ P p.chart}) :
    ((F.fiberRestrictEquiv P hP w).symm z).chart = z.val.chart := (rfl)

/-- Inverse restriction retains the ambient point. -/
@[simp]
theorem fiberRestrictEquiv_symm_apply_point (P : ι → Set V)
    (hP : ∀ c, IsRationalSemilinear h (P c)) (w : W)
    (z : {p : F.fiber w // (p.point : V) ∈ P p.chart}) :
    (((F.fiberRestrictEquiv P hP w).symm z).point : V) = z.val.point := (rfl)

/-- Restricting chart domains preserves finiteness of the fibers. -/
instance (P : ι → Set V) (hP : ∀ c, IsRationalSemilinear h (P c)) (w : W) [Finite (F.fiber w)] :
    Finite ((F.restrict P hP).fiber w) :=
  Finite.of_equiv _ (F.fiberRestrictEquiv P hP w).symm

/-- Restricting a family of finite branches to a rational semilinear set gives a family of
finite branches. -/
theorem IsFiniteBranch.restrict {F : FiniteSemilinearFamily h h' ι} (P : ι → Set V)
    (hP : ∀ c, IsRationalSemilinear h (P c)) (hF : F.IsFiniteBranch) :
    (F.restrict P hP).IsFiniteBranch :=
  fun c => (hF c).inter (hP c)

/-- Post-composition with an affine map whose linear part is rational. This need not
preserve finite branches when the affine map is not injective on their images. -/
def postcomp (φ : W →ᵃ[ℝ] X) (hφ : TauCeti.Toric.IsRationalLinearMap h' h'' φ.linear) :
    FiniteSemilinearFamily h h'' ι where
  domain := F.domain
  eval c x := φ (F.eval c x)
  isRationalPiecewiseAffine c := (F.isRationalPiecewiseAffine c).postcomp φ hφ

/-- Post-composition leaves all chart domains unchanged. -/
@[simp]
theorem postcomp_domain (φ : W →ᵃ[ℝ] X) (hφ : TauCeti.Toric.IsRationalLinearMap h' h'' φ.linear) :
    (F.postcomp φ hφ).domain = F.domain := (rfl)

/-- Post-composition applies the affine map to each evaluation. -/
@[simp]
theorem postcomp_eval (φ : W →ᵃ[ℝ] X) (hφ : TauCeti.Toric.IsRationalLinearMap h' h'' φ.linear)
    (c : ι) (x : (F.postcomp φ hφ).domain c) :
    (F.postcomp φ hφ).eval c x =
      φ (F.eval c ⟨x.val, congrFun (F.postcomp_domain φ hφ) c ▸ x.property⟩) := (rfl)

/-- The fiber of a post-composition over `w'` is the disjoint union of the original fibers
indexed by the intermediate values in `φ ⁻¹' {w'}`. -/
def fiberPostcompEquiv (φ : W →ᵃ[ℝ] X) (hφ : TauCeti.Toric.IsRationalLinearMap h' h'' φ.linear)
    (w' : X) : (F.postcomp φ hφ).fiber w' ≃ Σ w : {w : W // φ w = w'}, F.fiber w where
  toFun z := ⟨⟨F.eval z.chart z.point, z.eval_eq⟩, z.chart, z.point, rfl⟩
  invFun z := ⟨z.2.chart, z.2.point, (congrArg φ z.2.eval_eq).trans z.1.property⟩
  left_inv z := by cases z; rfl
  right_inv z := by
    obtain ⟨⟨w, hw⟩, c, x, hx⟩ := z
    cases hx
    rfl

/-- Post-composition preserves the original chart label. -/
@[simp]
theorem fiberPostcompEquiv_apply_chart (φ : W →ᵃ[ℝ] X)
    (hφ : TauCeti.Toric.IsRationalLinearMap h' h'' φ.linear) (w' : X)
    (z : (F.postcomp φ hφ).fiber w') :
    (F.fiberPostcompEquiv φ hφ w' z).2.chart = z.chart := (rfl)

/-- Post-composition records the original evaluation as the intermediate value. -/
@[simp]
theorem fiberPostcompEquiv_apply_value (φ : W →ᵃ[ℝ] X)
    (hφ : TauCeti.Toric.IsRationalLinearMap h' h'' φ.linear) (w' : X)
    (z : (F.postcomp φ hφ).fiber w') :
    (F.fiberPostcompEquiv φ hφ w' z).1.val =
      F.eval z.chart ⟨z.point.val,
        congrFun (F.postcomp_domain φ hφ) z.chart ▸ z.point.property⟩ := (rfl)

/-- Post-composition retains the original ambient point. -/
@[simp]
theorem fiberPostcompEquiv_apply_point (φ : W →ᵃ[ℝ] X)
    (hφ : TauCeti.Toric.IsRationalLinearMap h' h'' φ.linear) (w' : X)
    (z : (F.postcomp φ hφ).fiber w') :
    ((F.fiberPostcompEquiv φ hφ w' z).2.point : V) = z.point := (rfl)

/-- The inverse post-composition comparison retains the chart label. -/
@[simp]
theorem fiberPostcompEquiv_symm_apply_chart (φ : W →ᵃ[ℝ] X)
    (hφ : TauCeti.Toric.IsRationalLinearMap h' h'' φ.linear) (w' : X)
    (z : Σ w : {w : W // φ w = w'}, F.fiber w) :
    ((F.fiberPostcompEquiv φ hφ w').symm z).chart = z.2.chart := (rfl)

/-- The inverse post-composition comparison retains the ambient point. -/
@[simp]
theorem fiberPostcompEquiv_symm_apply_point (φ : W →ᵃ[ℝ] X)
    (hφ : TauCeti.Toric.IsRationalLinearMap h' h'' φ.linear) (w' : X)
    (z : Σ w : {w : W // φ w = w'}, F.fiber w) :
    (((F.fiberPostcompEquiv φ hφ w').symm z).point : V) = z.2.point := (rfl)

end FiniteSemilinearFamily

end TauCeti

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

The evaluation of a chart is a map on its domain, so families with the same domains and the same
values are equal. A family consists of finite branches when on every chart the domain is a finite
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

/-- Two families with the same domains and the same values on them are equal. -/
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
@[expose] def fiber (w : W) : Type _ := Σ c, {x : F.domain c // F.eval c x = w}

/-- Transporting a fiber point along equality of families preserves its chart label. -/
theorem fiber_cast_fst {F G : FiniteSemilinearFamily h h' ι} (e : F = G)
    (w : W) (z : F.fiber w) :
    (cast (congrArg (fun F : FiniteSemilinearFamily h h' ι => F.fiber w) e) z).1 = z.1 := by
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
  exact inferInstanceAs (Finite (Σ c, {x : F.domain c // F.eval c x = w}))

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
  Equiv.uniqueSigma _

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
  Equiv.sumSigmaDistrib fun c => {x : (F.sum G).domain c // (F.sum G).eval c x = w}

/-- The inverse fiber comparison preserves the chart label on each summand. -/
@[simp]
theorem fiberSumEquiv_symm_apply_fst (w : W) (z : F.fiber w ⊕ G.fiber w) :
    ((F.fiberSumEquiv G w).symm z).1 = Sum.map Sigma.fst Sigma.fst z := by
  cases z <;> rfl

/-- The inverse fiber comparison retains the ambient point on the left summand. -/
@[simp]
theorem fiberSumEquiv_symm_apply_inl_point (w : W) (z : F.fiber w) :
    (((F.fiberSumEquiv G w).symm (.inl z)).2.val : V) = z.2.val := (rfl)

/-- The inverse fiber comparison retains the ambient point on the right summand. -/
@[simp]
theorem fiberSumEquiv_symm_apply_inr_point (w : W) (z : G.fiber w) :
    (((F.fiberSumEquiv G w).symm (.inr z)).2.val : V) = z.2.val := (rfl)

/-- The fiber comparison retains the ambient point regardless of the summand. -/
@[simp]
theorem fiberSumEquiv_apply_point (w : W) (z : (F.sum G).fiber w) :
    Sum.elim (fun x => (x.2.val : V)) (fun x => (x.2.val : V))
      (F.fiberSumEquiv G w z) = z.2.val := by
  obtain ⟨(c | c), x⟩ := z <;> rfl

/-- Extended fiber cardinalities add under disjoint union, including infinite fibers. -/
theorem enat_card_fiber_sum (w : W) :
    ENat.card ((F.sum G).fiber w) = ENat.card (F.fiber w) + ENat.card (G.fiber w) := by
  rw [ENat.card_congr (F.fiberSumEquiv G w), ENat.card_sum]

/-- A disjoint union of families with finite fibers has finite fibers. -/
instance (w : W) [Finite (F.fiber w)] [Finite (G.fiber w)] :
    Finite ((F.sum G).fiber w) :=
  Finite.of_equiv _ (F.fiberSumEquiv G w).symm

/-- Fiber cardinalities add under disjoint union. -/
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
  eval c x := F.eval c ⟨x.val, x.property.1⟩
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
      F.eval c ⟨x.val, (F.restrict_domain P hP c ▸ x.property :
        x.val ∈ F.domain c ∩ P c).1⟩ := (rfl)

/-- The fiber of a restriction consists of the points of the original fiber lying in the
restricting set. -/
def fiberRestrictEquiv (P : ι → Set V) (hP : ∀ c, IsRationalSemilinear h (P c)) (w : W) :
    (F.restrict P hP).fiber w ≃ {p : F.fiber w // (p.2.val : V) ∈ P p.1} where
  toFun p := ⟨⟨p.1, ⟨p.2.val.val, p.2.val.property.1⟩, p.2.property⟩, p.2.val.property.2⟩
  invFun p := ⟨p.val.1, ⟨p.val.2.val.val, p.val.2.val.property, p.property⟩, p.val.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Restriction of chart domains preserves each point's original chart label. -/
@[simp]
theorem fiberRestrictEquiv_apply_val_fst (P : ι → Set V) (hP : ∀ c, IsRationalSemilinear h (P c))
    (w : W) (z : (F.restrict P hP).fiber w) :
    (F.fiberRestrictEquiv P hP w z).val.1 = z.1 := (rfl)

/-- The restricted fiber comparison retains the ambient point. -/
@[simp]
theorem fiberRestrictEquiv_apply_point (P : ι → Set V)
    (hP : ∀ c, IsRationalSemilinear h (P c)) (w : W) (z : (F.restrict P hP).fiber w) :
    ((F.fiberRestrictEquiv P hP w z).val.2.val : V) = z.2.val := (rfl)

/-- The inverse restricted fiber comparison retains the chart label and ambient point. -/
@[simp]
theorem fiberRestrictEquiv_symm_apply_chart_point (P : ι → Set V)
    (hP : ∀ c, IsRationalSemilinear h (P c)) (w : W)
    (z : {p : F.fiber w // (p.2.val : V) ∈ P p.1}) :
    (((F.fiberRestrictEquiv P hP w).symm z).1,
      ((F.fiberRestrictEquiv P hP w).symm z).2.val.val) = (z.val.1, z.val.2.val.val) := (rfl)

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

/-- The fiber of a post-composition over `w'` is the union of the original fibers over the
points of `φ ⁻¹' {w'}`. -/
def fiberPostcompEquiv (φ : W →ᵃ[ℝ] X) (hφ : TauCeti.Toric.IsRationalLinearMap h' h'' φ.linear)
    (w' : X) : (F.postcomp φ hφ).fiber w' ≃ Σ w : {w : W // φ w = w'}, F.fiber w :=
  let Y := {w : W // φ w = w'}
  calc
    _ ≃ Σ c : ι, Σ w : Y, {x : F.domain c // F.eval c x = w} :=
      Equiv.sigmaCongrRight fun c =>
        (Equiv.sigmaSubtypeFiberEquivSubtype (F.eval c) (fun _ => Iff.rfl)).symm
    _ ≃ Σ p : ι × Y, {x : F.domain p.1 // F.eval p.1 x = p.2} := Equiv.sigmaAssocProd.symm
    _ ≃ Σ p : Y × ι, {x : F.domain p.2 // F.eval p.2 x = p.1} :=
      Equiv.sigmaCongrLeft' (Equiv.prodComm ι Y)
    _ ≃ Σ w : Y, Σ c : ι, {x : F.domain c // F.eval c x = w} :=
      Equiv.sigmaAssocProd (α := Y) (β := ι)
        (γ := fun w c => {x : F.domain c // F.eval c x = (w : W)})

/-- Post-composition preserves the original chart label. -/
@[simp]
theorem fiberPostcompEquiv_apply_chart (φ : W →ᵃ[ℝ] X)
    (hφ : TauCeti.Toric.IsRationalLinearMap h' h'' φ.linear) (w' : X)
    (z : (F.postcomp φ hφ).fiber w') :
    (F.fiberPostcompEquiv φ hφ w' z).2.1 = z.1 := (rfl)

/-- Post-composition retains the ambient point and records the intermediate value. -/
@[simp]
theorem fiberPostcompEquiv_apply_value_point (φ : W →ᵃ[ℝ] X)
    (hφ : TauCeti.Toric.IsRationalLinearMap h' h'' φ.linear) (w' : X)
    (z : (F.postcomp φ hφ).fiber w') :
    ((F.fiberPostcompEquiv φ hφ w' z).1.val, (F.fiberPostcompEquiv φ hφ w' z).2.2.val.val) =
      (F.eval z.1 ⟨z.2.val.val,
        congrFun (F.postcomp_domain φ hφ) z.1 ▸ z.2.val.property⟩, z.2.val.val) := (rfl)

/-- The inverse post-composition comparison retains the chart label and ambient point. -/
@[simp]
theorem fiberPostcompEquiv_symm_apply_chart_point (φ : W →ᵃ[ℝ] X)
    (hφ : TauCeti.Toric.IsRationalLinearMap h' h'' φ.linear) (w' : X)
    (z : Σ w : {w : W // φ w = w'}, F.fiber w) :
    (((F.fiberPostcompEquiv φ hφ w').symm z).1,
      ((F.fiberPostcompEquiv φ hφ w').symm z).2.val.val) = (z.2.1, z.2.2.val.val) := (rfl)

end FiniteSemilinearFamily

end TauCeti

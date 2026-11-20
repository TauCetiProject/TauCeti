/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Rational.LocallyClosed

/-!
# Finite semilinear families and finite branches

A finite semilinear family is a finite collection of charts. Each chart has a rational
semilinear domain in a real vector space `V` with an integral lattice and an evaluation map
to a real vector space `W` with its own integral lattice. The evaluation is piecewise
affine: finitely many rational semilinear pieces cover the domain, and on each piece the
evaluation is an affine map whose linear part is rational. Charts need not be proper and
fibers need not be finite. The fiber over a point of `W` records the chart together with
the preimage point, so overlapping images in different charts are not identified.

The evaluation of a chart is a map on its domain, so families with the same domains and the same
values are equal. A family consists of finite branches when on every chart the domain is a finite
union of locally closed rational-normal polyhedra, and the evaluation restricts to an injective
affine map on each of them. Such domains need not be closed, and a finite branch has finite
fibers.

## Main definitions

* `IsRationalPiecewiseAffine`: a map on a rational semilinear domain that is piecewise affine
  with rational linear parts.
* `IsFiniteBranchOn`: a map on a domain that restricts to affine embeddings, with rational
  linear parts, of finitely many locally closed polyhedra covering the domain.
* `FiniteSemilinearFamily`: finitely many charts with rational piecewise-affine evaluation.
* `FiniteSemilinearFamily.fiber`: the fiber over a point, indexed by chart and preimage.
* `FiniteSemilinearFamily.IsFiniteBranch`: every chart is a finite branch.

## Main results

* `FiniteSemilinearFamily.sum`, `FiniteSemilinearFamily.restrict` and
  `FiniteSemilinearFamily.postcomp`: disjoint union, restriction of the charts to a rational
  semilinear set and post-composition of the evaluation with a rational affine map, with their
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

/-- A map `f` on `D` is piecewise affine with rational linear parts: finitely many rational
semilinear pieces cover `D`, and on each piece `f` is an affine map, with arbitrary real
offset, whose linear part is rational for the two lattices. -/
def IsRationalPiecewiseAffine (h : TauCeti.Toric.IsIntegralLattice i)
    (h' : TauCeti.Toric.IsIntegralLattice i') (D : Set V) (f : D → W) : Prop :=
  ∃ (κ : Type) (_ : Finite κ) (S : κ → Set V) (g : κ → (V →ᵃ[ℝ] W)),
    (⋃ k, S k) = D ∧ ∀ k, IsRationalSemilinear h (S k) ∧
      TauCeti.Toric.IsRationalLinearMap h h' (g k).linear ∧ ∀ x : D, x.val ∈ S k → f x = g k x

/-- A map `f` on `D` is a finite branch: finitely many locally closed rational-normal
polyhedra cover `D`, and on each of them `f` agrees with an affine map, with rational
linear part, that is injective on the polyhedron. The domain need not be closed. -/
def IsFiniteBranchOn (h : TauCeti.Toric.IsIntegralLattice i)
    (h' : TauCeti.Toric.IsIntegralLattice i') (D : Set V) (f : D → W) : Prop :=
  ∃ (κ : Type) (_ : Finite κ) (S : κ → Set V) (g : κ → (V →ᵃ[ℝ] W)),
    (⋃ k, S k) = D ∧ ∀ k, IsLocallyClosedPolyhedron h (S k) ∧
      TauCeti.Toric.IsRationalLinearMap h h' (g k).linear ∧ Set.InjOn (g k) (S k) ∧
        ∀ x : D, x.val ∈ S k → f x = g k x

namespace IsRationalPiecewiseAffine

/-- The domain of a rational piecewise-affine map is rational semilinear. -/
theorem isRationalSemilinear {D : Set V} {f : D → W} (hf : IsRationalPiecewiseAffine h h' D f) :
    IsRationalSemilinear h D := by
  obtain ⟨κ, _, S, g, rfl, hS⟩ := hf
  exact IsRationalSemilinear.iUnion fun k => (hS k).1

/-- Restricting to a rational semilinear set keeps the map piecewise affine. -/
theorem inter {D : Set V} {f : D → W} (hf : IsRationalPiecewiseAffine h h' D f) {P : Set V}
    (hP : IsRationalSemilinear h P) :
    IsRationalPiecewiseAffine h h' (D ∩ P) fun x => f ⟨x.val, x.property.1⟩ := by
  obtain ⟨κ, _, S, g, rfl, hS⟩ := hf
  refine ⟨κ, ‹_›, fun k => S k ∩ P, g, (Set.iUnion_inter ..).symm, fun k =>
    ⟨(hS k).1.inter hP, (hS k).2.1, fun x hx => (hS k).2.2 ⟨x.val, x.property.1⟩ hx.1⟩⟩

/-- Composing the values with a rational affine map keeps the map piecewise affine. -/
theorem postcomp {D : Set V} {f : D → W} (hf : IsRationalPiecewiseAffine h h' D f)
    (φ : W →ᵃ[ℝ] X) (hφ : TauCeti.Toric.IsRationalLinearMap h' h'' φ.linear) :
    IsRationalPiecewiseAffine h h'' D fun x => φ (f x) := by
  obtain ⟨κ, _, S, g, hD, hS⟩ := hf
  refine ⟨κ, ‹_›, S, fun k => φ.comp (g k), hD, fun k => ⟨(hS k).1, ?_, fun x hx => ?_⟩⟩
  · rw [AffineMap.comp_linear]
    exact hφ.comp (hS k).2.1
  · simp only [AffineMap.comp_apply, (hS k).2.2 x hx]

end IsRationalPiecewiseAffine

namespace IsFiniteBranchOn

/-- A finite branch is piecewise affine with rational linear parts. -/
theorem isRationalPiecewiseAffine {D : Set V} {f : D → W} (hf : IsFiniteBranchOn h h' D f) :
    IsRationalPiecewiseAffine h h' D f := by
  obtain ⟨κ, _, S, g, hD, hS⟩ := hf
  exact ⟨κ, ‹_›, S, g, hD, fun k =>
    ⟨(hS k).1.isRationalSemilinear, (hS k).2.1, (hS k).2.2.2⟩⟩

/-- Restricting a finite branch to a rational semilinear set gives a finite branch. -/
theorem inter {D : Set V} {f : D → W} (hf : IsFiniteBranchOn h h' D f) {P : Set V}
    (hP : IsRationalSemilinear h P) :
    IsFiniteBranchOn h h' (D ∩ P) fun x => f ⟨x.val, x.property.1⟩ := by
  obtain ⟨κ, _, S, g, rfl, hS⟩ := hf
  obtain ⟨μ, _, C, hC, -, rfl⟩ := TauCeti.isRationalSemilinear_iff_exists_pairwise_disjoint.mp hP
  refine ⟨κ × μ, inferInstance, fun p => S p.1 ∩ C p.2, fun p => g p.1, ?_, fun p =>
    ⟨(hS p.1).1.inter (hC p.2), (hS p.1).2.1, (hS p.1).2.2.1.mono Set.inter_subset_left,
      fun x hx => (hS p.1).2.2.2 ⟨x.val, x.property.1⟩ hx.1⟩⟩
  ext x
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Prod.exists]
  tauto

/-- A finite branch has finite fibers: on each piece the affine map is injective. -/
theorem finite_fiber {D : Set V} {f : D → W} (hf : IsFiniteBranchOn h h' D f) (w : W) :
    Finite {x : D // f x = w} := by
  obtain ⟨κ, _, S, g, hD, hS⟩ := hf
  have hpiece : ∀ x : D, ∃ k, x.val ∈ S k := fun x => by
    simpa only [Set.mem_iUnion, ← hD] using x.property
  choose k hk using hpiece
  refine Finite.of_injective (fun x : {x : D // f x = w} => k x.val) fun x y hxy => ?_
  have hxy : k x.val = k y.val := hxy
  refine Subtype.ext (Subtype.ext ((hS (k x.val)).2.2.1 (hk x.val) (hxy ▸ hk y.val) ?_))
  rw [← (hS (k x.val)).2.2.2 x.val (hk x.val), hxy, ← (hS (k y.val)).2.2.2 y.val (hk y.val)]
  exact x.property.trans y.property.symm

end IsFiniteBranchOn

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

/-- A family of finite branches has finite fibers. -/
theorem IsFiniteBranch.finite_fiber {F : FiniteSemilinearFamily h h' ι} (hF : F.IsFiniteBranch)
    (w : W) : Finite (F.fiber w) := by
  have := fun c => (hF c).finite_fiber w
  exact inferInstanceAs (Finite (Σ c, {x : F.domain c // F.eval c x = w}))

/-- The family with a single chart. -/
@[expose] def single {D : Set V} {f : D → W} (hf : IsRationalPiecewiseAffine h h' D f) :
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
    (c : Unit) : (single hf).eval c = f := (rfl)

/-- A single-chart family consists of finite branches exactly when its chart is a finite
branch. -/
theorem isFiniteBranch_single_iff {D : Set V} {f : D → W}
    (hf : IsRationalPiecewiseAffine h h' D f) :
    (single hf).IsFiniteBranch ↔ IsFiniteBranchOn h h' D f :=
  ⟨fun H => H (), fun H _ => H⟩

/-- The disjoint union of two families, with the charts of both. -/
@[expose] def sum : FiniteSemilinearFamily h h' (ι ⊕ κ) where
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
theorem sum_eval_inl (c : ι) : (F.sum G).eval (.inl c) = F.eval c := (rfl)

/-- The right charts of a disjoint union retain their original evaluations. -/
@[simp]
theorem sum_eval_inr (c : κ) : (F.sum G).eval (.inr c) = G.eval c := (rfl)

/-- The fiber of a disjoint union is the disjoint union of the fibers. -/
def fiberSumEquiv (w : W) : (F.sum G).fiber w ≃ F.fiber w ⊕ G.fiber w :=
  Equiv.sumSigmaDistrib fun c => {x : (F.sum G).domain c // (F.sum G).eval c x = w}

/-- The inverse fiber comparison preserves the chart label on each summand. -/
@[simp]
theorem fiberSumEquiv_symm_apply_fst (w : W) (z : F.fiber w ⊕ G.fiber w) :
    ((F.fiberSumEquiv G w).symm z).1 = Sum.map Sigma.fst Sigma.fst z := by
  cases z <;> rfl

/-- A disjoint union of families with finite fibers has finite fibers. -/
instance (w : W) [Finite (F.fiber w)] [Finite (G.fiber w)] :
    Finite ((F.sum G).fiber w) :=
  Finite.of_equiv _ (F.fiberSumEquiv G w).symm

/-- Fiber cardinalities add under disjoint union. -/
theorem nat_card_fiber_sum (w : W) [Finite (F.fiber w)] [Finite (G.fiber w)] :
    Nat.card ((F.sum G).fiber w) = Nat.card (F.fiber w) + Nat.card (G.fiber w) := by
  rw [Nat.card_congr (F.fiberSumEquiv G w), Nat.card_sum]

/-- A disjoint union consists of finite branches exactly when both families do. -/
theorem isFiniteBranch_sum_iff :
    (F.sum G).IsFiniteBranch ↔ F.IsFiniteBranch ∧ G.IsFiniteBranch :=
  ⟨fun H => ⟨fun c => H (.inl c), fun c => H (.inr c)⟩, fun H => by
    rintro (c | c)
    exacts [H.1 c, H.2 c]⟩

/-- Restriction of all charts to a rational semilinear set. -/
@[expose] def restrict {P : Set V} (hP : IsRationalSemilinear h P) :
    FiniteSemilinearFamily h h' ι where
  domain c := F.domain c ∩ P
  eval c x := F.eval c ⟨x.val, x.property.1⟩
  isRationalPiecewiseAffine c := (F.isRationalPiecewiseAffine c).inter hP

/-- Restricting a family intersects each domain with the restricting set. -/
@[simp]
theorem restrict_domain {P : Set V} (hP : IsRationalSemilinear h P) (c : ι) :
    (F.restrict hP).domain c = F.domain c ∩ P := (rfl)

/-- Restriction evaluates a point using its original domain membership. -/
@[simp]
theorem restrict_eval {P : Set V} (hP : IsRationalSemilinear h P) (c : ι)
    (x : ↥(F.domain c ∩ P)) : (F.restrict hP).eval c x = F.eval c ⟨x.val, x.property.1⟩ := (rfl)

/-- The fiber of a restriction consists of the points of the original fiber lying in the
restricting set. -/
def fiberRestrictEquiv {P : Set V} (hP : IsRationalSemilinear h P) (w : W) :
    (F.restrict hP).fiber w ≃ {p : F.fiber w // (p.2.val : V) ∈ P} where
  toFun p := ⟨⟨p.1, ⟨p.2.val.val, p.2.val.property.1⟩, p.2.property⟩, p.2.val.property.2⟩
  invFun p := ⟨p.val.1, ⟨p.val.2.val.val, p.val.2.val.property, p.property⟩, p.val.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Restriction of chart domains preserves each point's original chart label. -/
@[simp]
theorem fiberRestrictEquiv_apply_val_fst {P : Set V} (hP : IsRationalSemilinear h P)
    (w : W) (z : (F.restrict hP).fiber w) :
    (F.fiberRestrictEquiv hP w z).val.1 = z.1 := (rfl)

/-- Restricting chart domains preserves finiteness of the fibers. -/
instance {P : Set V} (hP : IsRationalSemilinear h P) (w : W) [Finite (F.fiber w)] :
    Finite ((F.restrict hP).fiber w) :=
  Finite.of_equiv _ (F.fiberRestrictEquiv hP w).symm

/-- Restricting a family of finite branches to a rational semilinear set gives a family of
finite branches. -/
theorem IsFiniteBranch.restrict {F : FiniteSemilinearFamily h h' ι} {P : Set V}
    (hP : IsRationalSemilinear h P) (hF : F.IsFiniteBranch) :
    (F.restrict hP).IsFiniteBranch :=
  fun c => (hF c).inter hP

/-- Post-composition of all evaluations with a rational affine map. This need not
preserve finite branches when the affine map is not injective on their images. -/
@[expose] def postcomp (φ : W →ᵃ[ℝ] X) (hφ : TauCeti.Toric.IsRationalLinearMap h' h'' φ.linear) :
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
    (c : ι) (x : F.domain c) : (F.postcomp φ hφ).eval c x = φ (F.eval c x) := (rfl)

/-- The fiber of a post-composition over `w'` is the union of the original fibers over the
points of `φ ⁻¹' {w'}`. -/
def fiberPostcompEquiv (φ : W →ᵃ[ℝ] X) (hφ : TauCeti.Toric.IsRationalLinearMap h' h'' φ.linear)
    (w' : X) : (F.postcomp φ hφ).fiber w' ≃ Σ w : {w : W // φ w = w'}, F.fiber w where
  toFun p := ⟨⟨F.eval p.1 p.2.val, p.2.property⟩, p.1, p.2.val, rfl⟩
  invFun p := ⟨p.2.1, p.2.2.val, (congrArg φ p.2.2.property).trans p.1.property⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨w, hw⟩, c, x, hx⟩
    cases hx
    rfl

end FiniteSemilinearFamily

end TauCeti

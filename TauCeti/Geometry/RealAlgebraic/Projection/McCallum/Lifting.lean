/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.GlobalOrder
public import TauCeti.Geometry.RealAlgebraic.Projection.McCallum.Basic
public import TauCeti.Geometry.RealAlgebraic.Projection.McCallum.FamilyOrder
public import TauCeti.Geometry.RealAlgebraic.Stack.Analytic
public import TauCeti.Geometry.RealAlgebraic.Stack.Chart
public import TauCeti.Geometry.RealAlgebraic.Stack.Discriminant
public import TauCeti.Geometry.RealAlgebraic.Stack.Product
public import TauCeti.Geometry.RealAlgebraic.Stack.Sectors

/-!
# McCallum lifting over an order-invariant base

An irreducible polynomial basis is analytically delineable over a connected analytic
submanifold when none of its fibers is nullified and the McCallum projection is
order-invariant there. Every input polynomial reconstructed from the basis then has constant
ambient order, and hence constant sign, on every section and sector of the resulting stack.

The proof applies the local discriminant theorem to the product of the basis members in
analytic chart coordinates. Its local root stacks are split back into a family delineation and
glued over the base. McCallum projection data controls the formal discriminant order of the
product, the fiber degrees, and the input contents. This is the non-nullified lifting step;
nullified fibers over zero-dimensional cells require delineating-polynomial refinement.

## References

S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
Springer (1998), Sections 2–3.
-/

public section

open Filter Metric MvPolynomial Polynomial Set Topology

namespace Finset.IsIrreducibleBasis

variable {n d : ℕ} [NormalizedGCDMonoid (MvPolynomial (Fin n) ℝ)]
  {F B : Finset (Polynomial (MvPolynomial (Fin n) ℝ))}
  {S : Set (Fin n → ℝ)}

/-- **McCallum lifting over an order-invariant base.** If an irreducible basis has no
nullified fiber over a connected analytic submanifold and every member of its McCallum
projection has constant ambient order there, then the basis has a common delineation.
Every stack cell is an analytic submanifold, and every original input has constant ambient
order and sign on that cell. -/
theorem exists_delineation_orderAt_eq_of_mcCallumProjection
    (hB : F.IsIrreducibleBasis B) (hS : TauCeti.IsAnalyticSubmanifold d S)
    (hconn : IsPreconnected S)
    (hfiber : ∀ b ∈ B, ∀ x ∈ S, b.map (MvPolynomial.eval x) ≠ 0)
    (hproj : ∀ q ∈ F.mcCallumProjection B, ∀ x ∈ S, ∀ y ∈ S,
      q.orderAt x = q.orderAt y) :
    ∃ D : TauCeti.Delineation fun (b : B) (x : S) ↦ b.1.map (MvPolynomial.eval x.1),
      ∀ E ∈ TauCeti.stackCells S D.root,
        (∃ e, (e = d ∨ e = d + 1) ∧ TauCeti.IsAnalyticSubmanifold e E) ∧
        ∀ f ∈ F,
          (∀ y ∈ E, ∀ y' ∈ E, ((finSuccEquiv ℝ n).symm f).orderAt y =
            ((finSuccEquiv ℝ n).symm f).orderAt y') ∧
          TauCeti.SignInvariant
            (fun y ↦ MvPolynomial.eval y ((finSuccEquiv ℝ n).symm f)) E := by
  classical
  let p : Polynomial (MvPolynomial (Fin n) ℝ) := ∏ b : B, b.1
  -- Projection order controls the zero pattern of coefficients, hence all fiber degrees.
  have hp_eq : p = ∏ b ∈ B, b := by
    change (∏ b ∈ B.attach, b.1) = ∏ b ∈ B, b
    exact Finset.prod_attach B id
  have hp_discr_ne : p.discr ≠ 0 := by
    rw [hp_eq]
    exact hB.discr_prod_ne_zero Subset.rfl
  have hzero (x : Fin n → ℝ) (hx : x ∈ S) (y : Fin n → ℝ) (hy : y ∈ S)
      (q : MvPolynomial (Fin n) ℝ) (hq : q ∈ F.mcCallumProjection B) :
      MvPolynomial.eval x q = 0 ↔ MvPolynomial.eval y q = 0 := by
    rw [← MvPolynomial.orderAt_pos_iff, hproj q hq x hx y hy,
      MvPolynomial.orderAt_pos_iff]
  have hdegree (b : B) (x : Fin n → ℝ) (hx : x ∈ S) (y : Fin n → ℝ) (hy : y ∈ S) :
      (b.1.map (MvPolynomial.eval x)).natDegree =
        (b.1.map (MvPolynomial.eval y)).natDegree :=
    Finset.natDegree_map_eq_of_mcCallumProjection
      (fun q hq ↦ hzero x hx y hy q hq) b.2
  have hp_ne (x : Fin n → ℝ) (hx : x ∈ S) : p.map (MvPolynomial.eval x) ≠ 0 := by
    simp only [p, Polynomial.map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun b _ ↦ hfiber b b.2 x hx
  have hp_degree (x : Fin n → ℝ) (hx : x ∈ S) (y : Fin n → ℝ) (hy : y ∈ S) :
      (p.map (MvPolynomial.eval x)).natDegree =
        (p.map (MvPolynomial.eval y)).natDegree := by
    rw [hp_eq, Polynomial.map_prod, Polynomial.map_prod]
    rw [natDegree_prod _ _ (fun b hb ↦ hfiber b hb x hx),
      natDegree_prod _ _ (fun b hb ↦ hfiber b hb y hy)]
    exact Finset.sum_congr rfl fun b hb ↦ hdegree ⟨b, hb⟩ x hx y hy
  have hp_discr (x : Fin n → ℝ) (hx : x ∈ S) (y : Fin n → ℝ) (hy : y ∈ S) :
      p.discr.orderAt x = p.discr.orderAt y := by
    rw [hp_eq]
    exact hB.orderAt_discr_prod_eq_of_mcCallumProjection (A := B) Subset.rfl x y
      (fun q hq ↦ hproj q hq x hx y hy)
  have hcontent (f : Polynomial (MvPolynomial (Fin n) ℝ)) (hf : f ∈ F)
      (x : Fin n → ℝ) (hx : x ∈ S) (y : Fin n → ℝ) (hy : y ∈ S) :
      f.content.orderAt x = f.content.orderAt y :=
    hproj f.content (content_mem_mcCallumProjection hf) x hx y hy
  -- Build a family stack in every analytic chart, carrying constant product order on sections.
  have hlocal (x : Fin n → ℝ) (hx : x ∈ S) :
      ∃ e : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ),
        TauCeti.IsAnalyticChart d S e ∧ x ∈ e.source ∧
          ∃ V : Set (Fin d → ℝ), IsOpen V ∧ TauCeti.firstCoords ℝ n d (e x) ∈ V ∧
            ∃ D : TauCeti.Delineation fun (b : B) (u : V) ↦
              b.1.map (MvPolynomial.eval
                (e.symm (TauCeti.firstCoords ℝ d n u))),
              ∀ i, ∀ u v : V,
                ((finSuccEquiv ℝ n).symm p).orderAt
                    (Fin.cons (D.root i u)
                      (e.symm (TauCeti.firstCoords ℝ d n u))) =
                  ((finSuccEquiv ℝ n).symm p).orderAt
                    (Fin.cons (D.root i v)
                      (e.symm (TauCeti.firstCoords ℝ d n v))) := by
    obtain ⟨e, hxe, he⟩ := hS.exists_isAnalyticChart x hx
    let a := TauCeti.firstCoords ℝ n d (e x)
    let φ : (Fin d → ℝ) → Fin n → ℝ :=
      fun u ↦ e.symm (TauCeti.firstCoords ℝ d n u)
    have hφa : AnalyticAt ℝ φ a := he.analyticAt_symm_firstCoords hxe hx
    have hmem : ∀ᶠ u in 𝓝 a, φ u ∈ e.source ∩ S := he.eventually_symm_firstCoords_mem hxe hx
    have hφa_eq : φ a = x := he.symm_firstCoords_firstCoords_apply hxe hx
    have hp0 : p.map (MvPolynomial.eval (φ a)) ≠ 0 := by
      rw [hφa_eq]
      exact hp_ne x hx
    have hd : ∀ᶠ u in 𝓝 a,
        (p.map (MvPolynomial.eval (φ u))).natDegree =
          (p.map (MvPolynomial.eval (φ a))).natDegree := by
      filter_upwards [hmem] with u hu
      exact hp_degree _ hu.2 _ (by
        rw [hφa_eq]
        exact hx)
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
      (MvPolynomial.orderAt_eq_top_iff.not.mpr hp_discr_ne : p.discr.orderAt (φ a) ≠ ⊤)
    have hm' : ∀ᶠ u in 𝓝 a, p.discr.orderAt (φ u) = (m : ℕ∞) := by
      filter_upwards [hmem] with u hu
      exact (hp_discr _ hu.2 _ (by
        rw [hφa_eq]
        exact hx)).trans hm.symm
    obtain ⟨ε, hε, D₀, -⟩ := p.exists_delineation_of_orderAt_discr_eq hφa hp0 hd hm'
    obtain ⟨ρ, hρ, hφρ⟩ := hφa.exists_ball_analyticOnNhd
    obtain ⟨δ, hδ, hδmem⟩ := Metric.mem_nhds_iff.mp hmem
    let r := min ε (min ρ δ)
    have hr : 0 < r := lt_min hε (lt_min hρ hδ)
    let ι : ball a r → ball a ε := fun u ↦ ⟨u, ball_subset_ball (min_le_left _ _) u.2⟩
    have hι : Continuous ι := continuous_subtype_val.subtype_mk _
    let D₁ := D₀.comp ι hι
    have hφr : AnalyticOnNhd ℝ φ (ball a r) :=
      hφρ.mono (ball_subset_ball (min_le_right _ _ |>.trans (min_le_left _ _)))
    have hrmem (u : ball a r) : φ u ∈ S :=
      (hδmem (ball_subset_ball (min_le_right _ _ |>.trans (min_le_right _ _)) u.2)).2
    have hn (b : B) (u : ball a r) : b.1.map (MvPolynomial.eval (φ u)) ≠ 0 :=
      hfiber b b.2 _ (hrmem u)
    have hdeg (b : B) (u v : ball a r) :
        (b.1.map (MvPolynomial.eval (φ u))).natDegree =
          (b.1.map (MvPolynomial.eval (φ v))).natDegree :=
      hdegree b _ (hrmem u) _ (hrmem v)
    have hφcont : Continuous fun u : ball a r ↦ φ u :=
      continuousOn_iff_continuous_domRestrict.mp hφr.continuousOn
    have hc (b : B) (j : ℕ) :
        Continuous fun u : ball a r ↦ (b.1.map (MvPolynomial.eval (φ u))).coeff j := by
      simp only [Polynomial.coeff_map]
      exact (MvPolynomial.continuous_eval (b.1.coeff j)).comp hφcont
    have D₁' : TauCeti.Delineation fun (_ : Unit) (u : ball a r) ↦
        ∏ b : B, b.1.map (MvPolynomial.eval (φ u)) := by
      have hfamily : (fun (_ : Unit) (u : ball a r) ↦
          p.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ u))) =
          (fun (_ : Unit) (u : ball a r) ↦
            ∏ b : B, b.1.map (MvPolynomial.eval (φ u))) := by
        funext _ u
        simp only [p, Polynomial.map_prod]
        congr 1
      -- The local theorem states evaluation with `eval₂Hom`; expose that family so the
      -- extensional equality above can transport the dependent delineation type.
      change TauCeti.Delineation fun (_ : Unit) (u : ball a r) ↦
        p.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ u)) at D₁
      rw [hfamily] at D₁
      exact D₁
    have : PreconnectedSpace (ball a r) :=
      isPreconnected_iff_preconnectedSpace.1 (convex_ball a r).isPreconnected
    have : Nonempty (ball a r) := ⟨⟨a, mem_ball_self hr⟩⟩
    let D := D₁'.ofProd hc hn hdeg
    refine ⟨e, he, hxe, ball a r, isOpen_ball, mem_ball_self hr, D, ?_⟩
    intro i u v
    let θ : (Fin d → ℝ) → ℝ := Function.extend Subtype.val (D.root i) 0
    have hθ (z : ball a r) : θ z = D.root i z :=
      Subtype.val_injective.extend_apply _ _ z
    have hθcont : ContinuousOn θ (ball a r) := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact (D.continuous_root i).congr fun z ↦ (hθ z).symm
    have hroot (z : Fin d → ℝ) (hz : z ∈ ball a r) :
        (p.map (MvPolynomial.eval (φ z))).IsRoot (θ z) := by
      let z' : ball a r := ⟨z, hz⟩
      rw [hθ z']
      rw [D₁'.ofProd_root hc hn hdeg]
      obtain ⟨_, hpos⟩ := D₁'.exists_multiplicity_pos
        (Fin.cast (D₁'.ofProd_count hc hn hdeg) i)
      simpa only [p, Polynomial.map_prod] using
        (D₁'.multiplicity_pos_iff z').mp hpos |>.2
    simpa only [hθ u, hθ v] using
      p.orderAt_root_eq_of_orderAt_discr_eq isOpen_ball (convex_ball a r).isPreconnected hφr
        (fun z hz ↦ hp_ne _ (hrmem ⟨z, hz⟩))
        (fun z hz ↦ (hp_discr _ (hrmem ⟨z, hz⟩) _ (by
          rw [hφa_eq]
          exact hx)).trans hm.symm) hθcont hroot u.2 v.2
  -- Glue the chart-local stacks, then transfer product order through the irreducible basis.
  obtain ⟨D, hprod⟩ := TauCeti.exists_delineation_of_locally_chart
    (d := d) (P := fun (b : B) x ↦ b.1.map (MvPolynomial.eval x))
    (q := fun x t ↦ ((finSuccEquiv ℝ n).symm p).orderAt (Fin.cons t x)) hconn hlocal
  have hcoeff : ∀ (b : B) (j : ℕ), TauCeti.AnalyticOnSubmanifold d
      (fun x ↦ (b.1.map (MvPolynomial.eval x)).coeff j) S := by
    intro b j
    simp only [Polynomial.coeff_map]
    exact ((AnalyticOnNhd.eval_continuousLinearMap
      (ContinuousLinearMap.id ℝ (Fin n → ℝ)) (b.1.coeff j)).mono
        (Set.subset_univ S)).analyticOnSubmanifold hS
  refine ⟨D, fun E hE ↦ ⟨D.exists_isAnalyticSubmanifold_of_mem_stackCells hS hcoeff hE, ?_⟩⟩
  have hp_mv_eq : (finSuccEquiv ℝ n).symm p =
      ∏ b ∈ B, (finSuccEquiv ℝ n).symm b := by
    rw [hp_eq, map_prod]
  exact hB.orderAt_eq_of_prod_delineation hconn D hfiber hcontent
    (by
      rw [← hp_mv_eq]
      intro i a ha a' ha'
      obtain ⟨haS, hai⟩ := TauCeti.mem_image_cylinder.mp ha
      obtain ⟨haS', hai'⟩ := TauCeti.mem_image_cylinder.mp ha'
      simp only [TauCeti.mem_sectionSet] at hai hai'
      have h := hprod i ⟨Fin.tail a, haS⟩ ⟨Fin.tail a', haS'⟩
      rw [hai, hai', Fin.cons_self_tail, Fin.cons_self_tail] at h
      exact h) E hE

end Finset.IsIrreducibleBasis

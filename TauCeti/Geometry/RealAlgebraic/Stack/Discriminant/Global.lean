/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.MvPolynomial
public import TauCeti.Analysis.Analytic.Submanifold.Polynomial
public import TauCeti.Analysis.Polynomial.Puiseux.GlobalOrder
public import TauCeti.Geometry.RealAlgebraic.Stack.Discriminant.Basic
public import TauCeti.Geometry.RealAlgebraic.Stack.Chart
public import TauCeti.Geometry.RealAlgebraic.Stack.Analytic
public import TauCeti.Geometry.RealAlgebraic.Stack.Product

/-!
# Analytic delineability from constant discriminant order

A real polynomial family with nonzero fibers of constant degree over a connected analytic
submanifold has a global analytic delineation when its nonzero formal discriminant has constant
ambient order on the base. The ordered real root functions are intrinsically analytic, their
positive multiplicities are constant, and the polynomial has constant sign on every section
and sector. Moreover, the polynomial, read in all coordinates of the cylinder, has constant
ambient order of vanishing along each root section. The formal leading coefficient may vanish
on the base, so the fiber degree need not equal the formal degree. Constant polynomials and
families without real roots are included.

The chart-local step `TauCeti.IsAnalyticChart.exists_delineation_orderAt_prod_eq` treats a
finite family through its product: it combines the local discriminant-order theorem
`Polynomial.exists_delineation_of_orderAt_discr_eq` with constancy of ambient order on root
sections over connected open bases. The global theorem glues these chart-local stacks and adds
the intrinsic analytic root-section API. Constancy of ambient order along a section is distinct
from constancy of fiber root multiplicity, and is the form needed when McCallum lifting is
iterated over the resulting sections.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
  Springer (1998), 242–268, Sections 2–3.
* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), Section 4.
-/

public section

open Filter Metric Polynomial Set Topology

namespace TauCeti.IsAnalyticChart

variable {n d : ℕ} {κ : Type*} [Fintype κ] {P : κ → Polynomial (MvPolynomial (Fin n) ℝ)}
  {S : Set (Fin n → ℝ)} {e : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)} {x : Fin n → ℝ}

/-- **Chart-local lifting of a non-nullified family.** Let `e` be an analytic chart of `S` around
`x ∈ S`. If every member of a finite family has nonzero fibers of constant degree over `S`, and
the formal discriminant of the product is nonzero with constant ambient order on `S`, then the
family has a delineation over an open neighbourhood of the chart coordinates of `x`. Along each
of its root sections, the product has constant ambient order. -/
theorem exists_delineation_orderAt_prod_eq (he : IsAnalyticChart d S e) (hxe : x ∈ e.source)
    (hx : x ∈ S) (hfiber : ∀ k, ∀ y ∈ S, (P k).map (MvPolynomial.eval y) ≠ 0)
    (hdegree : ∀ k, ∀ y ∈ S, ∀ z ∈ S,
      ((P k).map (MvPolynomial.eval y)).natDegree = ((P k).map (MvPolynomial.eval z)).natDegree)
    (hdiscr_ne : (∏ k, P k).discr ≠ 0)
    (hdiscr : ∀ y ∈ S, ∀ z ∈ S, (∏ k, P k).discr.orderAt y = (∏ k, P k).discr.orderAt z) :
    ∃ V : Set (Fin d → ℝ), IsOpen V ∧ firstCoords ℝ n d (e x) ∈ V ∧
      ∃ D : Delineation fun k (u : V) ↦
          (P k).map (MvPolynomial.eval (e.symm (firstCoords ℝ d n u))),
        ∀ i, ∀ u v : V,
          ((MvPolynomial.finSuccEquiv ℝ n).symm (∏ k, P k)).orderAt
              (Fin.cons (D.root i u) (e.symm (firstCoords ℝ d n u))) =
            ((MvPolynomial.finSuccEquiv ℝ n).symm (∏ k, P k)).orderAt
              (Fin.cons (D.root i v) (e.symm (firstCoords ℝ d n v))) := by
  classical
  let p := ∏ k, P k
  have hp_ne (y : Fin n → ℝ) (hy : y ∈ S) : p.map (MvPolynomial.eval y) ≠ 0 := by
    rw [Polynomial.map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ hfiber k y hy
  have hp_degree (y : Fin n → ℝ) (hy : y ∈ S) (z : Fin n → ℝ) (hz : z ∈ S) :
      (p.map (MvPolynomial.eval y)).natDegree = (p.map (MvPolynomial.eval z)).natDegree := by
    rw [Polynomial.map_prod, Polynomial.map_prod,
      natDegree_prod _ _ (fun k _ ↦ hfiber k y hy), natDegree_prod _ _ (fun k _ ↦ hfiber k z hz)]
    exact Finset.sum_congr rfl fun k _ ↦ hdegree k y hy z hz
  let a := firstCoords ℝ n d (e x)
  let φ : (Fin d → ℝ) → Fin n → ℝ := fun u ↦ e.symm (firstCoords ℝ d n u)
  have hφa : AnalyticAt ℝ φ a := he.analyticAt_symm_firstCoords hxe hx
  have hmem : ∀ᶠ u in 𝓝 a, φ u ∈ e.source ∩ S := he.eventually_symm_firstCoords_mem hxe hx
  have hφa_eq : φ a = x := he.symm_firstCoords_firstCoords_apply hxe hx
  have hφaS : φ a ∈ S := hφa_eq ▸ hx
  -- The local theorem evaluates with `eval₂Hom`, the definition of `MvPolynomial.eval`.
  have heval (y : Fin n → ℝ) : MvPolynomial.eval₂Hom (RingHom.id ℝ) y = MvPolynomial.eval y :=
    RingHom.ext fun q ↦ by rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_id]
  have hp0 : p.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ a)) ≠ 0 := by
    rw [heval]
    exact hp_ne _ hφaS
  have hd : ∀ᶠ u in 𝓝 a,
      (p.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ u))).natDegree =
        (p.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ a))).natDegree := by
    filter_upwards [hmem] with u hu
    rw [heval, heval]
    exact hp_degree _ hu.2 _ hφaS
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
    (MvPolynomial.orderAt_eq_top_iff.not.mpr hdiscr_ne : p.discr.orderAt (φ a) ≠ ⊤)
  have hm' : ∀ᶠ u in 𝓝 a, p.discr.orderAt (φ u) = (m : ℕ∞) := by
    filter_upwards [hmem] with u hu
    exact (hdiscr _ hu.2 _ hφaS).trans hm.symm
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
  have hn (k : κ) (u : ball a r) : (P k).map (MvPolynomial.eval (φ u)) ≠ 0 :=
    hfiber k _ (hrmem u)
  have hdeg (k : κ) (u v : ball a r) :
      ((P k).map (MvPolynomial.eval (φ u))).natDegree =
        ((P k).map (MvPolynomial.eval (φ v))).natDegree :=
    hdegree k _ (hrmem u) _ (hrmem v)
  have hφcont : Continuous fun u : ball a r ↦ φ u :=
    continuousOn_iff_continuous_domRestrict.mp hφr.continuousOn
  have hc (k : κ) (j : ℕ) :
      Continuous fun u : ball a r ↦ ((P k).map (MvPolynomial.eval (φ u))).coeff j := by
    simp only [Polynomial.coeff_map]
    exact (MvPolynomial.continuous_eval ((P k).coeff j)).comp hφcont
  have D₁' : Delineation fun (_ : Unit) (u : ball a r) ↦
      ∏ k, (P k).map (MvPolynomial.eval (φ u)) := by
    have hfamily : (fun (_ : Unit) (u : ball a r) ↦
        p.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ u))) =
        (fun (_ : Unit) (u : ball a r) ↦ ∏ k, (P k).map (MvPolynomial.eval (φ u))) := by
      funext _ u
      rw [heval, Polynomial.map_prod]
    -- Restricting along `ι` composes the family with `ι`; expose the restricted family so the
    -- extensional equality above can transport the dependent delineation type.
    change Delineation fun (_ : Unit) (u : ball a r) ↦
      p.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ u)) at D₁
    rw [hfamily] at D₁
    exact D₁
  have : PreconnectedSpace (ball a r) :=
    isPreconnected_iff_preconnectedSpace.1 (convex_ball a r).isPreconnected
  have : Nonempty (ball a r) := ⟨⟨a, mem_ball_self hr⟩⟩
  let D := D₁'.ofProd hc hn hdeg
  refine ⟨ball a r, isOpen_ball, mem_ball_self hr, D, ?_⟩
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
    rw [hθ z', D₁'.ofProd_root hc hn hdeg]
    obtain ⟨_, hpos⟩ := D₁'.exists_multiplicity_pos
      (Fin.cast (D₁'.ofProd_count hc hn hdeg) i)
    simpa only [p, Polynomial.map_prod] using
      (D₁'.multiplicity_pos_iff z').mp hpos |>.2
  simpa only [hθ u, hθ v] using
    p.orderAt_root_eq_of_orderAt_discr_eq isOpen_ball (convex_ball a r).isPreconnected hφr
      (fun z hz ↦ hp_ne _ (hrmem ⟨z, hz⟩))
      (fun z hz ↦ (hdiscr _ (hrmem ⟨z, hz⟩) _ hφaS).trans hm.symm) hθcont hroot u.2 v.2

end TauCeti.IsAnalyticChart

namespace TauCeti

variable {n d : ℕ} {S : Set (Fin n → ℝ)} {p : Polynomial (MvPolynomial (Fin n) ℝ)}

/-- **Analytic delineability from constant discriminant order.** A polynomial with nonzero
fibers of constant degree over a preconnected analytic submanifold, whose nonzero formal
discriminant has constant ambient order on the base, has a global delineation with intrinsically
analytic root functions. Each root function is represented by an ambient function whose values
off the base are immaterial. Along each root section, the polynomial, viewed as a polynomial in
all `n + 1` variables, has constant ambient order of vanishing.

No preservation of the formal degree or nonvanishing of the discriminant values is required.
Multiple roots are allowed, and their fiber multiplicities are constant. -/
theorem exists_analytic_delineation_of_orderAt_discr_eq
    (hS : IsAnalyticSubmanifold d S) (hconn : IsPreconnected S)
    (hp : ∀ x ∈ S, p.map (MvPolynomial.eval x) ≠ 0)
    (hdegree : ∀ x ∈ S, ∀ y ∈ S,
      (p.map (MvPolynomial.eval x)).natDegree = (p.map (MvPolynomial.eval y)).natDegree)
    (hdiscr : p.discr ≠ 0)
    (horder : ∀ x ∈ S, ∀ y ∈ S, p.discr.orderAt x = p.discr.orderAt y) :
    ∃ D : Delineation (fun (_ : Unit) (x : S) ↦ p.map (MvPolynomial.eval x.1)),
      (∀ i, ∃ r : (Fin n → ℝ) → ℝ, AnalyticOnSubmanifold d r S ∧
        ∀ x : S, r x = D.root i x) ∧
      ∀ i, ∀ x y : S,
        ((MvPolynomial.finSuccEquiv ℝ n).symm p).orderAt (Fin.cons (D.root i x) x.1) =
          ((MvPolynomial.finSuccEquiv ℝ n).symm p).orderAt (Fin.cons (D.root i y) y.1) := by
  classical
  -- Glue the chart-local stacks of the one-member family; ordered root lists glue without any
  -- choice of a global complex-root labelling, and constant order along sections is preserved.
  obtain ⟨D, hD⟩ := exists_delineation_of_locally_chart
    (P := fun (_ : Unit) x ↦ p.map (MvPolynomial.eval x))
    (q := fun x t ↦ ((MvPolynomial.finSuccEquiv ℝ n).symm (∏ _ : Unit, p)).orderAt
      (Fin.cons t x)) hconn fun x hx ↦ by
    obtain ⟨e, hxe, he⟩ := hS.exists_isAnalyticChart x hx
    exact ⟨e, he, hxe, he.exists_delineation_orderAt_prod_eq (P := fun _ : Unit ↦ p) hxe hx
      (fun _ ↦ hp) (fun _ ↦ hdegree) (by rwa [Fintype.prod_unique])
      (by rwa [Fintype.prod_unique])⟩
  simp only [Fintype.prod_unique] at hD
  -- Polynomial coefficients are intrinsically analytic, so the glued real roots are too.
  have hcoeff (k : Unit) (j : ℕ) : AnalyticOnSubmanifold d
      (fun x ↦ (p.map (MvPolynomial.eval x)).coeff j) S :=
    hS.analyticOnSubmanifold_coeff_map_eval p j
  refine ⟨D, fun i ↦ ?_, hD⟩
  let r := Function.extend Subtype.val (D.root i) (fun _ ↦ 0)
  have hr (x : S) : r x = D.root i x := Subtype.val_injective.extend_apply _ _ x
  exact ⟨r, D.analyticOnSubmanifold_root hS hcoeff i hr, hr⟩

end TauCeti

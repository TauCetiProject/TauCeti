/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian
public import TauCeti.Geometry.Symplectic.Prod
public import TauCeti.Geometry.Symplectic.SymplecticTransport

/-!
# The graph of a symplectomorphism is Lagrangian

Two symplectic vector spaces `(V, ω₁)` and `(W, ω₂)` assemble into the *twisted* product
`(V × W, ω₁ ⊖ ω₂)`, where the second form is negated:
`(ω₁ ⊖ ω₂)((v₁, w₁), (v₂, w₂)) = ω₁(v₁, v₂) - ω₂(w₁, w₂)`. The point of the sign is that the
graph `{(v, e v)}` of a real-linear isomorphism `e : V ≃ W` is *Lagrangian* for `ω₁ ⊖ ω₂`
exactly when `e` is a symplectomorphism (`ω₂(e v, e w) = ω₁(v, w)`). This is the linear model of
the Lagrangian-correspondence principle: symplectomorphisms are the same data as Lagrangian
graphs, and the special case `e = id` makes the diagonal of `(V × V, ω ⊖ ω)` Lagrangian.

This is the pointwise linear-algebra layer the analytic Heegaard Floer roadmap
(`TauCetiRoadmap/HeegaardFloer/README.md`, Lane F3) needs before Lagrangian Floer homology:
the boundary conditions of Floer strips between two Lagrangians `L₀`, `L₁` are packaged as a
single Lagrangian in the twisted product, and the diagonal is the model boundary condition for
the identity continuation. The twisted product reuses the direct sum
`TauCeti.SymplecticForm.prod` with the second factor negated by
`TauCeti.SymplecticForm.rescale`, and the graph is Mathlib's submodule `LinearMap.graph`.

The Lagrangian conclusion needs no finite-dimensionality hypothesis.

The twisted product form `ω₁ ⊖ ω₂` itself lives with the rest of the product-form API in
`TauCeti.Geometry.Symplectic.Prod`.

## Main declarations

* `TauCeti.SymplecticForm.IsSymplectomorphism`: a linear equivalence `e` with
  `ω₂(e v, e w) = ω₁(v, w)`, together with `refl`, `symm`, and `trans`.
* `TauCeti.SymplecticForm.isSymplectomorphism_iff`: the pointwise characterization of
  `IsSymplectomorphism`.
* `TauCeti.SymplecticForm.isSymplectomorphism_iff_transport_eq`: this predicate is equivalent
  to equality with the transported symplectic form.
* `TauCeti.SymplecticForm.isIsotropic_graph_iff`: the graph of a linear map is isotropic for
  `ω₁ ⊖ ω₂` iff it preserves the forms pointwise.
* `TauCeti.SymplecticForm.IsSymplectomorphism.isLagrangian_graph` and
  `TauCeti.SymplecticForm.isLagrangian_graph_iff`: the graph of `e` is Lagrangian for `ω₁ ⊖ ω₂`
  iff `e` is a symplectomorphism.
* `TauCeti.SymplecticForm.isLagrangian_diagonal`: the diagonal of `(V × V, ω ⊖ ω)` is Lagrangian.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.3, where symplectomorphisms are identified with Lagrangian graphs in the twisted
product.
-/

public section

namespace TauCeti

namespace SymplecticForm

variable {V W : Type*}
variable [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
variable {ω₁ : SymplecticForm V} {ω₂ : SymplecticForm W}

/-- The graph of `f` is isotropic for the twisted product form iff `f` preserves the symplectic
forms pointwise: `ω₂(f v, f w) = ω₁(v, w)`. -/
@[simp]
lemma isIsotropic_graph_iff {f : V →ₗ[ℝ] W} :
    (twistedProd ω₁ ω₂).IsIsotropic f.graph ↔ ∀ v w, ω₂ (f v) (f w) = ω₁ v w := by
  rw [isIsotropic_iff]
  constructor
  · intro h v w
    have hv : ((v, f v) : V × W) ∈ f.graph := by simp [LinearMap.mem_graph_iff]
    have hw : ((w, f w) : V × W) ∈ f.graph := by simp [LinearMap.mem_graph_iff]
    have hvw := h (v, f v) hv (w, f w) hw
    simp only [twistedProd_apply] at hvw
    linarith
  · intro h p hp q hq
    rw [LinearMap.mem_graph_iff] at hp hq
    rw [twistedProd_apply, hp, hq]
    linarith [h p.1 q.1]

/-- The graph of `e` is isotropic for the twisted product form iff `e` is a symplectomorphism.

This is a plain bridging lemma, not a `simp` lemma: the general `isIsotropic_graph_iff` already
puts graph isotropy into its own normal form, so marking this `@[simp]` too would leave two
competing normal forms for `e.toLinearMap.graph`. -/
lemma isIsotropic_linearEquiv_graph_iff {e : V ≃ₗ[ℝ] W} :
    (twistedProd ω₁ ω₂).IsIsotropic e.toLinearMap.graph ↔ IsSymplectomorphism ω₁ ω₂ e := by
  rw [isIsotropic_graph_iff]
  constructor
  · intro h
    exact isSymplectomorphism_iff.2 fun v w => h v w
  · intro h v w
    exact h.apply v w

/-- The graph of a symplectomorphism `e : V ≃ₗ[ℝ] W` is a Lagrangian subspace of the twisted
product `(V × W, ω₁ ⊖ ω₂)`. No finite-dimensionality is required. -/
lemma IsSymplectomorphism.isLagrangian_graph {e : V ≃ₗ[ℝ] W} (h : IsSymplectomorphism ω₁ ω₂ e) :
    (twistedProd ω₁ ω₂).IsLagrangian e.toLinearMap.graph := by
  rw [isLagrangian_iff]
  refine ⟨isIsotropic_linearEquiv_graph_iff.2 h, ?_⟩
  rw [isCoisotropic_iff]
  intro x hx
  rw [mem_orthogonal_iff] at hx
  -- For every `w`, testing against `(w, e w) ∈ graph` gives `ω₁ w x.1 = ω₂ (e w) x.2`.
  have key : ∀ w : V, ω₁ w x.1 - ω₂ (e w) x.2 = 0 := by
    intro w
    have hw : ((w, e w) : V × W) ∈ e.toLinearMap.graph := by simp [LinearMap.mem_graph_iff]
    have hthis := hx (w, e w) hw
    simp only [twistedProd_apply] at hthis
    exact hthis
  -- Rewrite `ω₂ (e w) x.2 = ω₁ w (e.symm x.2)`, so `ω₁ w (x.1 - e.symm x.2) = 0` for all `w`.
  have key2 : ∀ w : V, (ω₁.toBilinForm w) (x.1 - e.symm x.2) = 0 := by
    intro w
    have hb : ω₂ (e w) x.2 = ω₁ w (e.symm x.2) := by
      have hh := h.apply w (e.symm x.2)
      rwa [e.apply_symm_apply] at hh
    have hk := key w
    rw [hb] at hk
    rw [map_sub]
    exact hk
  have hz : x.1 - e.symm x.2 = 0 := ω₁.separatingRight _ key2
  have hx1 : x.1 = e.symm x.2 := sub_eq_zero.mp hz
  rw [LinearMap.mem_graph_iff]
  simp [hx1]

/-- The graph of `e` is Lagrangian for the twisted product form iff `e` is a symplectomorphism. -/
@[simp]
lemma isLagrangian_graph_iff {e : V ≃ₗ[ℝ] W} :
    (twistedProd ω₁ ω₂).IsLagrangian e.toLinearMap.graph ↔ IsSymplectomorphism ω₁ ω₂ e :=
  ⟨fun h => isIsotropic_linearEquiv_graph_iff.1 h.isIsotropic,
    IsSymplectomorphism.isLagrangian_graph⟩

/-- The diagonal of `(V × V, ω ⊖ ω)`, realized as the graph of the identity equivalence, is
Lagrangian. This is the boundary condition modeled by the identity continuation in Lagrangian
Floer homology. -/
lemma isLagrangian_diagonal (ω : SymplecticForm V) :
    (twistedProd ω ω).IsLagrangian (LinearEquiv.refl ℝ V).toLinearMap.graph :=
  (IsSymplectomorphism.refl ω).isLagrangian_graph

end SymplecticForm

end TauCeti

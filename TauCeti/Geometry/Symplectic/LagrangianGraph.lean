/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Prod
public import TauCeti.Geometry.Symplectic.Lagrangian
public import TauCeti.Geometry.Symplectic.Prod
public import TauCeti.Geometry.Symplectic.Rescale

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
the identity continuation. The construction reuses the direct-sum form
`TauCeti.SymplecticForm.prod` (from `Prod.lean`) precomposed with the nonzero rescaling
`TauCeti.SymplecticForm.rescale` by `-1` (from `Rescale.lean`), and Mathlib's graph submodule
`LinearMap.graph`, so no new nondegeneracy bookkeeping is introduced.

The Lagrangian conclusion needs no finite-dimensionality hypothesis: it is proved through the
isotropic-plus-coisotropic characterization `SymplecticForm.isLagrangian_iff`, with coisotropy
coming from nondegeneracy of `ω₁` alone.

## Main declarations

* `TauCeti.SymplecticForm.twistedProd`: the twisted product form `ω₁ ⊖ ω₂` on `V × W`.
* `TauCeti.SymplecticForm.IsSymplectomorphism`: a linear equivalence `e` with
  `ω₂(e v, e w) = ω₁(v, w)`, together with `refl`, `symm`, and `trans`.
* `TauCeti.SymplecticForm.isIsotropic_graph_iff`: the graph of `e` is isotropic for `ω₁ ⊖ ω₂`
  iff `e` is a symplectomorphism.
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

variable {V W U : Type*}
variable [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] [AddCommGroup U] [Module ℝ U]

/-- The twisted product symplectic form `ω₁ ⊖ ω₂` on `V × W`, given by
`(ω₁ ⊖ ω₂)((v₁, w₁), (v₂, w₂)) = ω₁(v₁, v₂) - ω₂(w₁, w₂)`.

It is the direct-sum form `ω₁ ⊕ ω₂` of `Prod.lean` with the second factor rescaled by `-1`. -/
noncomputable def twistedProd (ω₁ : SymplecticForm V) (ω₂ : SymplecticForm W) :
    SymplecticForm (V × W) :=
  ω₁.prod (ω₂.rescale (-1) (by norm_num))

@[simp]
lemma twistedProd_apply (ω₁ : SymplecticForm V) (ω₂ : SymplecticForm W) (p q : V × W) :
    twistedProd ω₁ ω₂ p q = ω₁ p.1 q.1 - ω₂ p.2 q.2 := by
  unfold twistedProd
  rw [prod_apply, rescale_apply]
  ring

/-- A real-linear equivalence `e : V ≃ₗ[ℝ] W` is a symplectomorphism from `(V, ω₁)` to `(W, ω₂)`
when it intertwines the two symplectic forms, `ω₂(e v, e w) = ω₁(v, w)`. -/
def IsSymplectomorphism (ω₁ : SymplecticForm V) (ω₂ : SymplecticForm W) (e : V ≃ₗ[ℝ] W) : Prop :=
  ∀ v w, ω₂ (e v) (e w) = ω₁ v w

variable {ω₁ : SymplecticForm V} {ω₂ : SymplecticForm W} {ω₃ : SymplecticForm U}

/-- The identity equivalence is a symplectomorphism. -/
lemma IsSymplectomorphism.refl (ω : SymplecticForm V) :
    IsSymplectomorphism ω ω (LinearEquiv.refl ℝ V) := by
  intro v w
  simp

/-- The inverse of a symplectomorphism is a symplectomorphism. -/
lemma IsSymplectomorphism.symm {e : V ≃ₗ[ℝ] W} (h : IsSymplectomorphism ω₁ ω₂ e) :
    IsSymplectomorphism ω₂ ω₁ e.symm := by
  intro v w
  have h2 := h (e.symm v) (e.symm w)
  rw [e.apply_symm_apply, e.apply_symm_apply] at h2
  exact h2.symm

/-- Symplectomorphisms compose. -/
lemma IsSymplectomorphism.trans {e : V ≃ₗ[ℝ] W} {f : W ≃ₗ[ℝ] U}
    (h₁ : IsSymplectomorphism ω₁ ω₂ e) (h₂ : IsSymplectomorphism ω₂ ω₃ f) :
    IsSymplectomorphism ω₁ ω₃ (e.trans f) := by
  intro v w
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h₂ (e v) (e w), h₁ v w]

/-- The graph of `e` is isotropic for the twisted product form iff `e` is a symplectomorphism:
isotropy of the graph is precisely the intertwining identity `ω₂(e v, e w) = ω₁(v, w)`. -/
lemma isIsotropic_graph_iff {e : V ≃ₗ[ℝ] W} :
    (twistedProd ω₁ ω₂).IsIsotropic e.toLinearMap.graph ↔ IsSymplectomorphism ω₁ ω₂ e := by
  rw [isIsotropic_iff]
  constructor
  · intro h v w
    have hv : ((v, e v) : V × W) ∈ e.toLinearMap.graph := by simp [LinearMap.mem_graph_iff]
    have hw : ((w, e w) : V × W) ∈ e.toLinearMap.graph := by simp [LinearMap.mem_graph_iff]
    have hvw := h (v, e v) hv (w, e w) hw
    simp only [twistedProd_apply] at hvw
    linarith
  · intro h p hp q hq
    rw [LinearMap.mem_graph_iff] at hp hq
    simp only [LinearEquiv.coe_toLinearMap] at hp hq
    rw [twistedProd_apply, hp, hq]
    linarith [h p.1 q.1]

/-- The graph of a symplectomorphism `e : V ≃ₗ[ℝ] W` is a Lagrangian subspace of the twisted
product `(V × W, ω₁ ⊖ ω₂)`. No finite-dimensionality is required: coisotropy follows from
nondegeneracy of `ω₁`. -/
lemma IsSymplectomorphism.isLagrangian_graph {e : V ≃ₗ[ℝ] W} (h : IsSymplectomorphism ω₁ ω₂ e) :
    (twistedProd ω₁ ω₂).IsLagrangian e.toLinearMap.graph := by
  rw [isLagrangian_iff]
  refine ⟨isIsotropic_graph_iff.2 h, ?_⟩
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
      have hh := h w (e.symm x.2)
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
lemma isLagrangian_graph_iff {e : V ≃ₗ[ℝ] W} :
    (twistedProd ω₁ ω₂).IsLagrangian e.toLinearMap.graph ↔ IsSymplectomorphism ω₁ ω₂ e :=
  ⟨fun h => isIsotropic_graph_iff.1 h.isIsotropic, IsSymplectomorphism.isLagrangian_graph⟩

/-- The diagonal of `(V × V, ω ⊖ ω)`, realized as the graph of the identity equivalence, is
Lagrangian. This is the boundary condition modeled by the identity continuation in Lagrangian
Floer homology. -/
lemma isLagrangian_diagonal (ω : SymplecticForm V) :
    (twistedProd ω ω).IsLagrangian (LinearEquiv.refl ℝ V).toLinearMap.graph :=
  (IsSymplectomorphism.refl ω).isLagrangian_graph

end SymplecticForm

end TauCeti

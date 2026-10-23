/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Direct sums of partial linear maps on `L^p` products

For partial linear maps `f : E →ₗ.[R] E'` and `g : F →ₗ.[R] F'`, the direct sum `f ⊕ g` acts on
the `L^p` product `WithLp p (E × F)` by `(x, y) ↦ (f x, g y)`. Its domain is the product of the
two domains, transported through the identification `WithLp p (E × F) ≃ E × F`. For `p = 2` and
Hilbert spaces `E`, `F` this is the orthogonal direct sum of two unbounded operators, acting on
the Hilbert direct sum `WithLp 2 (E × F)`.

The direct sum is densely defined exactly when both summands are, and closed exactly when both
summands are. Both statements hold over arbitrary topological modules, since `WithLp p (E × F)`
carries the product topology for every `p`.

## Main declarations

* `LinearPMap.withLpProdMap p f g`: the direct sum of `f` and `g` on `WithLp p (E × F)`.
* `LinearPMap.mem_withLpProdMap_domain`: `(x, y)` lies in the domain exactly when `x` lies in the
  domain of `f` and `y` in the domain of `g`.
* `LinearPMap.withLpProdMap_apply_toLp`: on the domain, `(f ⊕ g) (x, y) = (f x, g y)`.
* `LinearPMap.mem_graph_withLpProdMap_iff`: the graph of `f ⊕ g` is the product of the graphs.
* `LinearPMap.dense_withLpProdMap_domain_iff`: `f ⊕ g` is densely defined if and only if `f` and
  `g` are.
* `LinearPMap.isClosed_withLpProdMap_iff`: `f ⊕ g` is closed if and only if `f` and `g` are.

## References

* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Graduate Texts in
  Mathematics 265, Springer (2012), Chapter 1.
-/

public section

open Set WithLp

namespace LinearPMap

variable {R E E' F F' : Type*} (p : ENNReal)

section Algebra

variable [Ring R] [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E']
  [AddCommGroup F] [Module R F] [AddCommGroup F'] [Module R F']

/-- The direct sum of two partial linear maps on the `L^p` product: the partial linear map
`(x, y) ↦ (f x, g y)` on `WithLp p (E × F)`, whose domain is the product of the domains of `f`
and `g`. -/
noncomputable def withLpProdMap (f : E →ₗ.[R] E') (g : F →ₗ.[R] F') :
    WithLp p (E × F) →ₗ.[R] WithLp p (E' × F') where
  domain := (f.domain.prod g.domain).comap (WithLp.linearEquiv p R (E × F)).toLinearMap
  toFun :=
    let D := (f.domain.prod g.domain).comap (WithLp.linearEquiv p R (E × F)).toLinearMap
    let fstD : D →ₗ[R] f.domain :=
      ((fstₗ p R E F).comp D.subtype).codRestrict f.domain fun x => x.2.1
    let sndD : D →ₗ[R] g.domain :=
      ((sndₗ p R E F).comp D.subtype).codRestrict g.domain fun x => x.2.2
    (WithLp.linearEquiv p R (E' × F')).symm.toLinearMap.comp
      ((f.toFun.comp fstD).prod (g.toFun.comp sndD))

variable {p} {f : E →ₗ.[R] E'} {g : F →ₗ.[R] F'}

/-- The domain of the direct sum is the product of the two domains, transported to the `L^p`
product. -/
theorem withLpProdMap_domain (f : E →ₗ.[R] E') (g : F →ₗ.[R] F') :
    (f.withLpProdMap p g).domain =
      (f.domain.prod g.domain).comap (WithLp.linearEquiv p R (E × F)).toLinearMap :=
  (rfl)

/-- A vector lies in the domain of the direct sum exactly when its first coordinate lies in the
domain of `f` and its second coordinate in the domain of `g`. -/
@[simp]
theorem mem_withLpProdMap_domain {x : WithLp p (E × F)} :
    x ∈ (f.withLpProdMap p g).domain ↔ x.fst ∈ f.domain ∧ x.snd ∈ g.domain :=
  Iff.rfl

/-- The first coordinate of the direct sum is `f` applied to the first coordinate. -/
@[simp]
theorem withLpProdMap_apply_fst (x : (f.withLpProdMap p g).domain) :
    (f.withLpProdMap p g x).fst =
      f ⟨(x : WithLp p (E × F)).fst, (mem_withLpProdMap_domain.mp x.2).1⟩ :=
  (rfl)

/-- The second coordinate of the direct sum is `g` applied to the second coordinate. -/
@[simp]
theorem withLpProdMap_apply_snd (x : (f.withLpProdMap p g).domain) :
    (f.withLpProdMap p g x).snd =
      g ⟨(x : WithLp p (E × F)).snd, (mem_withLpProdMap_domain.mp x.2).2⟩ :=
  (rfl)

/-- A pair of domain vectors gives a vector in the domain of the direct sum. -/
theorem toLp_mem_withLpProdMap_domain (x : f.domain) (y : g.domain) :
    toLp p ((x : E), (y : F)) ∈ (f.withLpProdMap p g).domain :=
  ⟨x.2, y.2⟩

/-- On the domain, the direct sum acts by `(f ⊕ g) (x, y) = (f x, g y)`. -/
theorem withLpProdMap_apply_toLp (x : f.domain) (y : g.domain) :
    f.withLpProdMap p g ⟨toLp p ((x : E), (y : F)), toLp_mem_withLpProdMap_domain x y⟩ =
      toLp p (f x, g y) :=
  (rfl)

/-- The graph of the direct sum is the product of the graphs: `(u, v)` lies on the graph of
`f ⊕ g` exactly when the first coordinates lie on the graph of `f` and the second coordinates on
the graph of `g`. -/
theorem mem_graph_withLpProdMap_iff {z : WithLp p (E × F) × WithLp p (E' × F')} :
    z ∈ (f.withLpProdMap p g).graph ↔
      (z.1.fst, z.2.fst) ∈ f.graph ∧ (z.1.snd, z.2.snd) ∈ g.graph := by
  obtain ⟨u, v⟩ := z
  simp only [mem_graph_iff]
  constructor
  · rintro ⟨x, rfl, rfl⟩
    exact ⟨⟨_, rfl, (withLpProdMap_apply_fst x).symm⟩,
      ⟨_, rfl, (withLpProdMap_apply_snd x).symm⟩⟩
  · rintro ⟨⟨x, hx, hfx⟩, ⟨y, hy, hgy⟩⟩
    refine ⟨⟨u, mem_withLpProdMap_domain.mpr ⟨hx ▸ x.2, hy ▸ y.2⟩⟩, rfl, ?_⟩
    refine ofLp_injective p (Prod.ext ?_ ?_) <;> simp only [ofLp_fst, ofLp_snd]
    · rw [withLpProdMap_apply_fst, ← hfx]
      exact congrArg f (Subtype.ext hx.symm)
    · rw [withLpProdMap_apply_snd, ← hgy]
      exact congrArg g (Subtype.ext hy.symm)

variable [TopologicalSpace E] [TopologicalSpace F]

/-- The direct sum is densely defined if and only if both summands are. -/
theorem dense_withLpProdMap_domain_iff :
    Dense ((f.withLpProdMap p g).domain : Set (WithLp p (E × F))) ↔
      Dense (f.domain : Set E) ∧ Dense (g.domain : Set F) := by
  have hdom : ((f.withLpProdMap p g).domain : Set (WithLp p (E × F))) =
      homeomorphProd p E F ⁻¹' ((f.domain : Set E) ×ˢ (g.domain : Set F)) :=
    rfl
  rw [hdom, (homeomorphProd p E F).isOpenQuotientMap.dense_preimage_iff, dense_iff_closure_eq,
    closure_prod_eq, prod_eq_univ, ← dense_iff_closure_eq, ← dense_iff_closure_eq]

/-- The direct sum of densely defined partial linear maps is densely defined. -/
theorem dense_withLpProdMap_domain (hf : Dense (f.domain : Set E))
    (hg : Dense (g.domain : Set F)) :
    Dense ((f.withLpProdMap p g).domain : Set (WithLp p (E × F))) :=
  dense_withLpProdMap_domain_iff.mpr ⟨hf, hg⟩

end Algebra

section Closed

variable {p} [CommRing R] [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E']
  [AddCommGroup F] [Module R F] [AddCommGroup F'] [Module R F']
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace F] [TopologicalSpace F']
  {f : E →ₗ.[R] E'} {g : F →ₗ.[R] F'}

/-- The direct sum is closed if and only if both summands are closed. -/
theorem isClosed_withLpProdMap_iff : (f.withLpProdMap p g).IsClosed ↔ f.IsClosed ∧ g.IsClosed := by
  -- The graph of `f ⊕ g` is the preimage of `graph f ×ˢ graph g` under a coordinate shuffle.
  let Φ : WithLp p (E × F) × WithLp p (E' × F') → (E × E') × (F × F') :=
    fun z => ((z.1.fst, z.2.fst), (z.1.snd, z.2.snd))
  have hgraph : ((f.withLpProdMap p g).graph : Set (WithLp p (E × F) × WithLp p (E' × F'))) =
      Φ ⁻¹' ((f.graph : Set (E × E')) ×ˢ (g.graph : Set (F × F'))) :=
    Set.ext fun _ => mem_graph_withLpProdMap_iff
  rw [LinearPMap.IsClosed, hgraph]
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨hf, hg⟩ => (hf.prod hg).preimage (by fun_prop)⟩
  · -- `graph f` is the slice of the graph of `f ⊕ g` through the zero vector of `graph g`.
    have hf : (f.graph : Set (E × E')) =
        (fun w : E × E' => (toLp p (w.1, (0 : F)), toLp p (w.2, (0 : F')))) ⁻¹'
          (Φ ⁻¹' ((f.graph : Set (E × E')) ×ˢ (g.graph : Set (F × F')))) := by
      ext w
      simp [Φ]
    rw [LinearPMap.IsClosed, hf]
    exact h.preimage (by fun_prop)
  · have hg : (g.graph : Set (F × F')) =
        (fun w : F × F' => (toLp p ((0 : E), w.1), toLp p ((0 : E'), w.2))) ⁻¹'
          (Φ ⁻¹' ((f.graph : Set (E × E')) ×ˢ (g.graph : Set (F × F')))) := by
      ext w
      simp [Φ]
    rw [LinearPMap.IsClosed, hg]
    exact h.preimage (by fun_prop)

/-- The direct sum of closed partial linear maps is closed. -/
theorem IsClosed.withLpProdMap (hf : f.IsClosed) (hg : g.IsClosed) :
    (f.withLpProdMap p g).IsClosed :=
  isClosed_withLpProdMap_iff.mpr ⟨hf, hg⟩

end Closed

end LinearPMap

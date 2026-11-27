/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.LinearPMap
public import TauCeti.Analysis.Normed.Lp.PiLp.Submodule

/-!
# Direct sums of families of partial linear maps on `L^p` products

For a family of partial linear maps `f i : E i →ₗ.[R] F i`, the direct sum `⊕ i, f i` acts on the
`L^p` product `PiLp p E` coordinatewise, `x ↦ (i ↦ f i (x i))`. Its domain `Submodule.piLp` is
the product of the domains, transported through the identification `PiLp p E ≃ ∀ i, E i`. For
`p = 2`, a finite index type and Hilbert spaces `E i`, this is the orthogonal direct sum of finitely
many unbounded operators, acting on the Hilbert direct sum `PiLp 2 E`. It is the family version of
`LinearPMap.withLpProdMap`.

## Main declarations

* `LinearPMap.piLpMap p f`: the direct sum of the family `f` on `PiLp p E`.
* `LinearPMap.mem_piLpMap_domain`: `x` lies in the domain exactly when each coordinate `x i` lies
  in the domain of `f i`.
* `LinearPMap.piLpMap_apply`, `LinearPMap.piLpMap_apply_toLp`: on the domain,
  `(⊕ i, f i) x i = f i (x i)`.
* `LinearPMap.mem_graph_piLpMap_iff`: the graph of the direct sum is the product of the graphs.
* `LinearPMap.dense_piLpMap_domain_iff`: the direct sum is densely defined if and only if every
  `f i` is.
* `LinearPMap.isClosed_piLpMap_iff`: the direct sum is closed if and only if every `f i` is.

## References

* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Graduate Texts in
  Mathematics 265, Springer (2012), Chapter 1.
-/

public section

open Set WithLp

variable {R ι : Type*} {E F : ι → Type*} (p : ENNReal)

namespace LinearPMap

section Algebra

variable [Ring R] [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)] [∀ i, AddCommGroup (F i)]
  [∀ i, Module R (F i)]

/-- The direct sum of a family of partial linear maps on the `L^p` product: the partial linear map
`x ↦ (i ↦ f i (x i))` on `PiLp p E`, whose domain is the product of the domains of the `f i`. -/
noncomputable def piLpMap (f : ∀ i, E i →ₗ.[R] F i) : PiLp p E →ₗ.[R] PiLp p F where
  domain := Submodule.piLp p fun i ↦ (f i).domain
  toFun := (WithLp.linearEquiv p R (∀ i, F i)).symm.toLinearMap.comp
    (LinearMap.pi fun i ↦ (f i).toFun.comp (Submodule.piLpProj p (fun i ↦ (f i).domain) i))

variable {p} {f : ∀ i, E i →ₗ.[R] F i}

/-- The domain of the direct sum is the product of the domains, transported to the `L^p`
product. -/
theorem piLpMap_domain (f : ∀ i, E i →ₗ.[R] F i) :
    (piLpMap p f).domain = Submodule.piLp p fun i ↦ (f i).domain :=
  (rfl)

/-- A vector lies in the domain of the direct sum exactly when each coordinate lies in the domain
of the corresponding map. -/
@[simp]
theorem mem_piLpMap_domain {x : PiLp p E} : x ∈ (piLpMap p f).domain ↔ ∀ i, x i ∈ (f i).domain :=
  Submodule.mem_piLp

/-- A family of vectors `x i` of the domains of the `f i` gives a vector of the domain of the
direct sum. -/
theorem toLp_mem_piLpMap_domain (x : ∀ i, (f i).domain) :
    toLp p (fun i ↦ (x i : E i)) ∈ (piLpMap p f).domain :=
  Submodule.toLp_mem_piLp x

/-- The `i`-th coordinate of the direct sum is `f i` applied to the `i`-th coordinate. -/
@[simp]
theorem piLpMap_apply (x : (piLpMap p f).domain) (i : ι) :
    piLpMap p f x i = f i ⟨(x : PiLp p E) i, mem_piLpMap_domain.mp x.property i⟩ :=
  congrArg (f i) (Subtype.ext (Submodule.coe_piLpProj i x))

/-- On the domain, the direct sum acts by `(⊕ i, f i) (i ↦ x i) = (i ↦ f i (x i))`. -/
theorem piLpMap_apply_toLp (x : ∀ i, (f i).domain) :
    piLpMap p f ⟨toLp p fun i ↦ (x i : E i), toLp_mem_piLpMap_domain x⟩ =
      toLp p fun i ↦ f i (x i) :=
  PiLp.ext fun i ↦ piLpMap_apply _ i

/-- The graph of the direct sum is the product of the graphs: `(u, v)` lies on the graph of
`⊕ i, f i` exactly when `(u i, v i)` lies on the graph of `f i` for every `i`. -/
theorem mem_graph_piLpMap_iff {z : PiLp p E × PiLp p F} :
    z ∈ (piLpMap p f).graph ↔ ∀ i, (z.1 i, z.2 i) ∈ (f i).graph := by
  obtain ⟨u, v⟩ := z
  simp only [mem_graph_iff]
  constructor
  · rintro ⟨x, rfl, rfl⟩ i
    exact ⟨_, rfl, (piLpMap_apply x i).symm⟩
  · intro h
    choose x hx hfx using h
    refine ⟨⟨u, mem_piLpMap_domain.mpr fun i ↦ hx i ▸ (x i).property⟩, rfl, ?_⟩
    ext i
    rw [piLpMap_apply, ← hfx i]
    exact congrArg (f i) (Subtype.ext (hx i).symm)

variable [∀ i, TopologicalSpace (E i)]

/-- The direct sum is densely defined if and only if every `f i` is densely defined. -/
theorem dense_piLpMap_domain_iff :
    Dense ((piLpMap p f).domain : Set (PiLp p E)) ↔ ∀ i, Dense ((f i).domain : Set (E i)) :=
  Submodule.dense_piLp_iff

/-- The direct sum of densely defined partial linear maps is densely defined. -/
theorem dense_piLpMap_domain (hf : ∀ i, Dense ((f i).domain : Set (E i))) :
    Dense ((piLpMap p f).domain : Set (PiLp p E)) :=
  dense_piLpMap_domain_iff.mpr hf

end Algebra

section Closed

variable {p} [CommRing R] [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]
  [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)] [∀ i, TopologicalSpace (E i)]
  [∀ i, TopologicalSpace (F i)] {f : ∀ i, E i →ₗ.[R] F i}

/-- The direct sum is closed if and only if every `f i` is closed. -/
theorem isClosed_piLpMap_iff : (LinearPMap.piLpMap p f).IsClosed ↔ ∀ i, (f i).IsClosed := by
  classical
  refine ⟨fun h i ↦ ?_, fun hf ↦ ?_⟩
  · -- The graph of `f i` is the preimage of the graph of the direct sum under the embedding of
    -- the `i`-th coordinate, since every other graph contains `0`.
    have hgraph : ((f i).graph : Set (E i × F i)) =
        (fun z : E i × F i ↦ (PiLp.single p i z.1, PiLp.single p i z.2)) ⁻¹'
          ((LinearPMap.piLpMap p f).graph : Set (PiLp p E × PiLp p F)) := by
      ext z
      simp only [SetLike.mem_coe, mem_preimage, mem_graph_piLpMap_iff]
      refine ⟨fun hz j ↦ ?_, fun hz ↦ by simpa using hz i⟩
      by_cases hj : j = i
      · subst hj
        simpa using hz
      · simp [Pi.single_eq_of_ne hj]
    rw [LinearPMap.IsClosed, hgraph]
    exact h.preimage (by simp only [← PiLp.toLp_single]; fun_prop)
  · have hgraph : ((LinearPMap.piLpMap p f).graph : Set (PiLp p E × PiLp p F)) =
        ⋂ i, (fun z : PiLp p E × PiLp p F ↦ (z.1 i, z.2 i)) ⁻¹'
          ((f i).graph : Set (E i × F i)) := by
      ext z
      simp only [SetLike.mem_coe, mem_graph_piLpMap_iff, mem_iInter, mem_preimage]
    rw [LinearPMap.IsClosed, hgraph]
    exact isClosed_iInter fun i ↦ (hf i).preimage (by fun_prop)

/-- The direct sum of a family of closed partial linear maps is closed. -/
theorem isClosed_piLpMap (hf : ∀ i, (f i).IsClosed) : (LinearPMap.piLpMap p f).IsClosed :=
  isClosed_piLpMap_iff.mpr hf

end Closed

end LinearPMap

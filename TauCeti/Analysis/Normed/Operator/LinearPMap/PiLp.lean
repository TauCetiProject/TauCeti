/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Direct sums of families of partial linear maps on `L^p` products

For a family of partial linear maps `f i : E i →ₗ.[R] F i`, the direct sum `⊕ i, f i` acts on the
`L^p` product `PiLp p E` coordinatewise, `x ↦ (i ↦ f i (x i))`. Its domain is the product of the
domains, transported through the identification `PiLp p E ≃ ∀ i, E i`. For `p = 2`, a finite
index type and Hilbert spaces `E i`, this is the orthogonal direct sum of finitely many unbounded
operators, acting on the Hilbert direct sum `PiLp 2 E`. It is the family version of
`LinearPMap.withLpProdMap`.

## Main declarations

* `Submodule.piLp p s`: the vectors of `PiLp p E` whose coordinates lie in the submodules `s i`,
  with its coordinate projections `Submodule.piLpProj`. It is the domain of the direct sum.
* `Submodule.piLpEquiv p s`: `Submodule.piLp p s` is the product of the `s i`.
* `Submodule.dense_piLp_iff`: `Submodule.piLp p s` is dense if and only if every `s i` is.
* `PiLp.completeSpace_iff`: for a finite index type, `PiLp p E` is complete if and only if every
  factor `E i` is.
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

namespace Submodule

variable [Semiring R] [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]

/-- The vectors of the `L^p` product whose coordinates lie in the submodules `s i`:
`Submodule.pi univ s` transported to `PiLp p E`. It is the domain of `LinearPMap.piLpMap`. -/
def piLp (s : ∀ i, Submodule R (E i)) : Submodule R (PiLp p E) :=
  (Submodule.pi univ s).comap (WithLp.linearEquiv p R (∀ i, E i)).toLinearMap

variable {p} {s : ∀ i, Submodule R (E i)}

/-- A vector lies in `Submodule.piLp p s` exactly when each coordinate `x i` lies in `s i`. -/
@[simp]
theorem mem_piLp {x : PiLp p E} : x ∈ piLp p s ↔ ∀ i, x i ∈ s i := by
  simp [piLp, Submodule.mem_pi]

/-- A family of vectors `x i ∈ s i` gives a vector of `Submodule.piLp p s`. -/
theorem toLp_mem_piLp (x : ∀ i, s i) : toLp p (fun i ↦ (x i : E i)) ∈ piLp p s :=
  mem_piLp.mpr fun i ↦ (x i).property

/-- A vector of `s i` placed in the `i`-th coordinate, with `0` elsewhere, lies in
`Submodule.piLp p s`. -/
theorem single_mem_piLp [DecidableEq ι] {i : ι} {x : E i} (hx : x ∈ s i) :
    PiLp.single p i x ∈ piLp p s :=
  mem_piLp.mpr fun j ↦ by
    rcases eq_or_ne j i with rfl | hj
    · simpa using hx
    · simp [Pi.single_eq_of_ne hj]

variable (p s) in
/-- The `i`-th coordinate of a vector of `Submodule.piLp p s`, as a vector of `s i`. -/
def piLpProj (i : ι) : piLp p s →ₗ[R] s i :=
  ((LinearMap.proj i).comp ((WithLp.linearEquiv p R (∀ i, E i)).toLinearMap.comp
    (piLp p s).subtype)).codRestrict (s i) fun x ↦ mem_piLp.mp x.property i

/-- `Submodule.piLpProj p s i` reads off the `i`-th coordinate. -/
@[simp]
theorem coe_piLpProj (i : ι) (x : piLp p s) :
    (piLpProj p s i x : E i) = (x : PiLp p E) i :=
  (rfl)

variable (p s) in
/-- `Submodule.piLp p s` is the product of the submodules `s i`. -/
def piLpEquiv : piLp p s ≃ₗ[R] ∀ i, s i where
  toFun x i := piLpProj p s i x
  invFun x := ⟨toLp p fun i ↦ (x i : E i), toLp_mem_piLp x⟩
  map_add' x y := by funext i; simp
  map_smul' c x := by funext i; simp
  left_inv x := Subtype.ext (PiLp.ext fun i ↦ by simp)
  right_inv x := funext fun i ↦ Subtype.ext (by simp)

/-- The `i`-th component of `Submodule.piLpEquiv p s x` is the `i`-th coordinate of `x`. -/
@[simp]
theorem piLpEquiv_apply (x : piLp p s) (i : ι) :
    piLpEquiv p s x i = piLpProj p s i x :=
  (rfl)

/-- `(Submodule.piLpEquiv p s).symm` assembles a family of vectors into a vector of
`PiLp p E`. -/
@[simp]
theorem coe_piLpEquiv_symm_apply (x : ∀ i, s i) :
    ((piLpEquiv p s).symm x : PiLp p E) = toLp p fun i ↦ (x i : E i) :=
  (rfl)

variable [∀ i, TopologicalSpace (E i)]

/-- `Submodule.piLp p s` is dense if and only if every `s i` is dense. -/
theorem dense_piLp_iff :
    Dense (piLp p s : Set (PiLp p E)) ↔ ∀ i, Dense (s i : Set (E i)) := by
  have hdom : (piLp p s : Set (PiLp p E)) =
      PiLp.homeomorph p E ⁻¹' univ.pi fun i ↦ (s i : Set (E i)) := by
    ext x
    simp [← Homeomorph.coe_toEquiv]
  rw [hdom, (PiLp.homeomorph p E).isOpenQuotientMap.dense_preimage_iff]
  refine ⟨fun h i ↦ ?_, fun h ↦ dense_pi univ fun i _ ↦ h i⟩
  -- Every `s i` contains `0`, so `s i` is the image of the product under the `i`-th evaluation.
  rw [← eval_image_univ_pi (t := fun i ↦ (s i : Set (E i))) ⟨0, fun i _ ↦ (s i).zero_mem⟩]
  exact (Function.surjective_eval i).denseRange.dense_image (continuous_apply i) h

end Submodule

namespace PiLp

variable [Fact (1 ≤ p)] [Finite ι] [∀ i, NormedAddCommGroup (E i)]

/-- Each factor of a complete finite `L^p` product is complete. -/
theorem completeSpace_of_completeSpace [CompleteSpace (PiLp p E)] (i : ι) :
    CompleteSpace (E i) := by
  classical
  have := Fintype.ofFinite ι
  have hs : Isometry (single p i : E i → PiLp p E) := .of_dist_eq (dist_single_same p E i)
  -- The `i`-th coordinate is a continuous left inverse of `single p i`, so its range is closed.
  exact hs.isUniformInducing.completeSpace
    (Function.LeftInverse.isClosed_range (f := fun x : PiLp p E ↦ x i)
      (fun _ ↦ single_eq_same p i _) (PiLp.continuous_apply p E i) hs.continuous).isComplete

/-- A finite `L^p` product is complete if and only if every factor is complete. -/
theorem completeSpace_iff : CompleteSpace (PiLp p E) ↔ ∀ i, CompleteSpace (E i) :=
  ⟨fun _ ↦ completeSpace_of_completeSpace p, fun _ ↦ inferInstance⟩

end PiLp

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
  (rfl)

/-- On the domain, the direct sum acts by `(⊕ i, f i) (i ↦ x i) = (i ↦ f i (x i))`. -/
theorem piLpMap_apply_toLp (x : ∀ i, (f i).domain) :
    piLpMap p f ⟨toLp p fun i ↦ (x i : E i), toLp_mem_piLpMap_domain x⟩ =
      toLp p fun i ↦ f i (x i) :=
  (rfl)

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

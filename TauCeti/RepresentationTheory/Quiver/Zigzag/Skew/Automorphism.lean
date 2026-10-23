/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.SemisimpleQuotient
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Skew.Cohomology
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Skew.Grading
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Skew.Multiplication

/-!
# Isomorphisms of skew-zigzag algebras up to graph automorphisms

Two skew-zigzag parameters `c` and `c'` of a finite simple graph `G` are gauge equivalent,
equivalently have the same class in `H¹(G, kˣ)`, exactly when their relation quotients are
isomorphic by an isomorphism fixing every vertex idempotent
(`TauCeti.SkewZigzagParameter.cohomologyClass_eq_iff_exists_vertexFixing_algEquiv`). This file
drops the requirement that the vertex idempotents be fixed: isomorphisms which only permute them are
classified by the gauge classes modulo the automorphisms of `G`, that is by the orbits of
`Aut(G)` on `H¹(G, kˣ)`.

An algebra isomorphism `φ : Z_k(G, c) ≃ Z_k(G, c')` with `φ(e_i) = e_{σ i}` for a permutation `σ` of
the vertices maps the corner `e_j Z e_i` onto the corner `e_{σ j} Z e_{σ i}`. For distinct vertices
this corner is nonzero exactly when `i` and `j` are adjacent: it contains the arrow of an edge, and
it vanishes otherwise. So `σ` is a graph automorphism, and composing `φ` with the inverse of the
relabelling isomorphism `Z_k(G, c) ≃ Z_k(G, c.relabel σ)` gives a vertex-fixing isomorphism
`Z_k(G, c.relabel σ) ≃ Z_k(G, c')`, which forces `c.relabel σ` and `c'` to be gauge equivalent.

When the coefficient ring has only trivial idempotents, an isomorphism which maps every vertex
idempotent into their span automatically permutes them. The images `φ(e_i)` are nonzero orthogonal
idempotents in that span. Their vertex coordinates lie in the product algebra `V → k`, where an
idempotent is the indicator function of a set of vertices. The sets attached to the `e_i` are then
nonempty, pairwise disjoint and as many as the vertices, hence singletons.
These results classify vertex-permuting and vertex-span-preserving algebra isomorphisms; they do
not assert a classification of arbitrary graded isomorphisms.

## Main results

* `AlgEquiv.adj_iff_of_vertexPermuting`: the permutation of the vertices induced by an isomorphism
  of skew-zigzag relation quotients is a graph automorphism.
* `AlgEquiv.exists_iso_isGaugeEquivalent_relabel_of_vertexPermuting`: an isomorphism permuting the
  vertex idempotents by `σ` makes `σ` a graph automorphism along which the relabelled parameter is
  gauge equivalent to the target parameter.
* `AlgEquiv.exists_equiv_apply_vertexIdempotent_of_mem_span`: over a ring with only trivial
  idempotents, an isomorphism mapping the vertex idempotents into their span permutes them.
* `TauCeti.SkewZigzagParameter.exists_isGaugeEquivalent_relabel_iff_exists_vertexPermuting_algEquiv`
  and `exists_isGaugeEquivalent_relabel_iff_exists_algEquiv_mem_span`: the relation quotients are
  isomorphic by an isomorphism permuting the vertex idempotents, or over a ring with only trivial
  idempotents by one preserving their span, exactly when the parameters are gauge equivalent up to a
  graph automorphism.
* `exists_isGaugeEquivalent_relabel_iff_exists_algEquiv_vertexImages_mem_grade_zero`, in the same
  namespace: the span criterion expressed using the quotient's degree-zero piece.
* `exists_firstCohomologyRelabel_eq_iff_exists_vertexPermuting_algEquiv` and
  `exists_firstCohomologyRelabel_eq_iff_exists_algEquiv_mem_span`, in the same namespace: the same
  classification by the orbits of the graph automorphisms on `H¹(G, kˣ)`.

## References

C. Couture, *Skew-Zigzag Algebras*, Section 4, Theorem 4.12, https://arxiv.org/abs/1509.08405,
which identifies the graded isomorphism classes of skew-zigzag algebras with the orbits of the
graph automorphisms on the graph cohomology `H¹(G, kˣ)`.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V} [Finite V]
  {c c' : SkewZigzagParameter k G}

/-! ### Vertex coefficients -/

/-- Every skew-zigzag relator has zero coefficient on each trivial path. -/
private theorem trivialCoeff_eq_zero_of_isSkewZigzagRelator
    {x : pathAlgebra k (DoubledQuiver G)} (hx : IsSkewZigzagRelator k G c x) :
    PathAlgebra.trivialCoeff k (DoubledQuiver G) x = 0 := by
  cases hx with
  | nonreturn p hp _ =>
    exact PathAlgebra.trivialCoeff_ofPath_of_length_pos (hp.symm ▸ by omega)
  | backtrack_ratio h h' =>
    rw [map_sub, map_smul, backtrackElem_eq_ofPath, backtrackElem_eq_ofPath,
      PathAlgebra.trivialCoeff_ofPath_of_length_pos (by simp [length_backtrackPath]),
      PathAlgebra.trivialCoeff_ofPath_of_length_pos (by simp [length_backtrackPath]),
      smul_zero, sub_zero]
  | long_path x hx =>
    exact PathAlgebra.trivialCoeff_ofPath_of_length_pos (by omega)

variable (c) in
/-- The vertex-coefficient homomorphism of a skew-zigzag relation quotient, reading off the
coefficients on the trivial paths. -/
private noncomputable def skewTrivialCoeff :
    skewZigzagQuotient k G c →ₐ[k] (DoubledQuiver G → k) :=
  skewZigzagLift k G c (PathAlgebra.trivialCoeff k (DoubledQuiver G)) fun _ hx =>
    trivialCoeff_eq_zero_of_isSkewZigzagRelator hx

variable (c) in
/-- The vertex idempotent at `i` has coefficient one at `i` and zero at every other vertex. -/
private theorem skewTrivialCoeff_vertexIdempotent [DecidableEq V] (i j : V) :
    skewTrivialCoeff c (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) (vertex G j) =
      if i = j then 1 else 0 := by
  classical
  rw [skewTrivialCoeff, skewZigzagLift_skewZigzagMk, PathAlgebra.trivialCoeff_vertexIdempotent,
    Pi.single_apply]
  simp only [(vertex_injective G).eq_iff, eq_comm]

/-! ### Isomorphisms permuting the vertex idempotents -/

/-- **An isomorphism permuting the vertex idempotents preserves adjacency.** If an algebra
isomorphism between skew-zigzag relation quotients sends each vertex idempotent `e_i` to `e_{σ i}`
for an injective `σ`, then `σ` maps edges to edges. -/
private theorem adj_of_vertexPermuting [Nontrivial k]
    (φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c') {σ : V → V}
    (hσ : Function.Injective σ)
    (hφ : ∀ i : V, φ (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) =
      skewZigzagMk k G c' (vertexIdempotent k (vertex G (σ i))))
    {i j : V} (h : G.Adj i j) : G.Adj (σ i) (σ j) := by
  by_contra hn
  have hcorner := skewZigzagMk_vertexIdempotent_mul_mul_vertexIdempotent_eq_zero k G c'
    (hσ.ne (G.ne_of_adj h)) hn (φ (skewZigzagMk k G c (ofArrow (arrow G h))))
  rw [← hφ i, ← hφ j, ← map_mul, ← map_mul, ← map_mul, ← map_mul, vertexIdempotent_mul_ofArrow,
    ofArrow_mul_vertexIdempotent, map_eq_zero_iff φ φ.injective] at hcorner
  exact skewZigzagMk_ofArrow_ne_zero k G c _ hcorner

/-- **The vertex permutation of an isomorphism is a graph automorphism.** If an algebra isomorphism
between skew-zigzag relation quotients sends each vertex idempotent `e_i` to `e_{σ i}`, then `σ`
preserves and reflects adjacency. -/
theorem _root_.AlgEquiv.adj_iff_of_vertexPermuting [Nontrivial k]
    (φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c') (σ : V ≃ V)
    (hφ : ∀ i : V, φ (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) =
      skewZigzagMk k G c' (vertexIdempotent k (vertex G (σ i))))
    (i j : V) : G.Adj (σ i) (σ j) ↔ G.Adj i j := by
  refine ⟨fun h => ?_, adj_of_vertexPermuting φ σ.injective hφ⟩
  have hφsymm : ∀ i : V, φ.symm (skewZigzagMk k G c' (vertexIdempotent k (vertex G i))) =
      skewZigzagMk k G c (vertexIdempotent k (vertex G (σ.symm i))) := fun i => by
    rw [AlgEquiv.symm_apply_eq, hφ, Equiv.apply_symm_apply]
  simpa using adj_of_vertexPermuting φ.symm σ.symm.injective hφsymm h

/-- **An isomorphism permuting the vertex idempotents is a relabelling up to gauge.** If an algebra
isomorphism between the skew-zigzag relation quotients of `c` and `c'` sends each vertex idempotent
`e_i` to `e_{σ i}`, then `σ` is a graph automorphism, and relabelling `c` along it gives a parameter
gauge equivalent to `c'`. -/
theorem _root_.AlgEquiv.exists_iso_isGaugeEquivalent_relabel_of_vertexPermuting [Nontrivial k]
    (φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c') (σ : V ≃ V)
    (hφ : ∀ i : V, φ (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) =
      skewZigzagMk k G c' (vertexIdempotent k (vertex G (σ i)))) :
    ∃ τ : G ≃g G, ⇑τ = ⇑σ ∧ (c.relabel τ).IsGaugeEquivalent c' := by
  let τ : G ≃g G := ⟨σ, fun {i j} => φ.adj_iff_of_vertexPermuting σ hφ i j⟩
  refine ⟨τ, RelIso.coe_fn_mk _ _, ?_⟩
  -- Undoing the relabelling turns `φ` into an isomorphism fixing every vertex idempotent.
  refine ((skewZigzagQuotientEquiv k τ c).symm.trans φ).isGaugeEquivalent_of_vertexFixing
    fun j => ?_
  obtain ⟨i, rfl⟩ := τ.surjective j
  have hsymm : (skewZigzagQuotientEquiv k τ c).symm
      (skewZigzagMk k G (c.relabel τ) (vertexIdempotent k (vertex G (τ i)))) =
      skewZigzagMk k G c (vertexIdempotent k (vertex G i)) := by
    rw [AlgEquiv.symm_apply_eq, skewZigzagQuotientEquiv_skewZigzagMk,
      pathAlgebraEquiv_vertexIdempotent]
  rw [AlgEquiv.trans_apply, hsymm, hφ, RelIso.coe_fn_mk]

/-- **An isomorphism preserving the span of the vertex idempotents permutes them.** If the
coefficient ring has only trivial idempotents and an algebra isomorphism between skew-zigzag
relation quotients maps each vertex idempotent into
the span of the vertex idempotents, then it sends each `e_i` to `e_{σ i}` for a permutation `σ` of
the vertices. -/
theorem _root_.AlgEquiv.exists_equiv_apply_vertexIdempotent_of_mem_span [Nontrivial k]
    (hidempotents : ∀ e : k, IsIdempotentElem e → e = 0 ∨ e = 1)
    (φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c')
    (hφ : ∀ i : V, φ (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) ∈
      Submodule.span k (Set.range fun j : V =>
        skewZigzagMk k G c' (vertexIdempotent k (vertex G j)))) :
    ∃ σ : V ≃ V, ∀ i : V, φ (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) =
      skewZigzagMk k G c' (vertexIdempotent k (vertex G (σ i))) := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  -- `g i j` is the coefficient of `e_j` in `φ (e_i)`.
  obtain ⟨g, hg⟩ : ∃ g : V → V → k, ∀ i j, g i j =
      skewTrivialCoeff c' (φ (skewZigzagMk k G c (vertexIdempotent k (vertex G i)))) (vertex G j) :=
    ⟨_, fun _ _ => rfl⟩
  have hcoeff : ∀ (a : V → k) (j : V), skewTrivialCoeff c'
      (∑ l, a l • skewZigzagMk k G c' (vertexIdempotent k (vertex G l))) (vertex G j) = a j :=
    fun a j => by simp [skewTrivialCoeff_vertexIdempotent]
  have hsum : ∀ i, φ (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) =
      ∑ j, g i j • skewZigzagMk k G c' (vertexIdempotent k (vertex G j)) := fun i => by
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp (hφ i)
    have hga : g i = a := funext fun j => by rw [hg, ← ha, hcoeff]
    rw [hga, ha]
  -- The coefficients of the idempotent `φ (e_i)` are idempotent, hence zero or one.
  have hidem : ∀ i j, g i j = 0 ∨ g i j = 1 := fun i j => by
    apply hidempotents
    have h := congrArg (fun x => skewTrivialCoeff c' (φ x) (vertex G j))
      (skewZigzagMk_vertexIdempotent_mul_self k G c i)
    simp only [map_mul, Pi.mul_apply] at h
    rw [IsIdempotentElem, hg, h]
  -- The images of distinct vertex idempotents are orthogonal.
  have horth : ∀ i i', i ≠ i' → ∀ j, g i j * g i' j = 0 := fun i i' hii j => by
    have h := congrArg (fun x => skewTrivialCoeff c' (φ x) (vertex G j))
      (skewZigzagMk_vertexIdempotent_mul_vertexIdempotent_of_ne k G c hii)
    simp only [map_mul, Pi.mul_apply, map_zero, Pi.zero_apply] at h
    rw [hg, hg, h]
  -- The image of a vertex idempotent is nonzero, so one of its coefficients is one.
  have hne : ∀ i, ∃ j, g i j ≠ 0 := fun i => by
    by_contra! h
    have hzero : skewZigzagMk k G c (vertexIdempotent k (vertex G i)) = 0 :=
      φ.injective <| by simp [hsum i, h]
    have h1 := congrArg (fun x => skewTrivialCoeff c x (vertex G i)) hzero
    simp [skewTrivialCoeff_vertexIdempotent] at h1
  choose s hs using hne
  have hs1 : ∀ i, g i (s i) = 1 := fun i => (hidem i (s i)).resolve_left (hs i)
  have hinj : Function.Injective s := fun i i' h => by
    by_contra hii
    have h0 := horth i i' hii (s i)
    rw [hs1, h, hs1, one_mul] at h0
    exact one_ne_zero h0
  have hbij : Function.Bijective s := ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  refine ⟨Equiv.ofBijective s hbij, fun i => ?_⟩
  -- The coefficients of `φ (e_i)` are those of `e_{s i}`.
  have hgi : ∀ j, g i j = if s i = j then 1 else 0 := fun j => by
    split_ifs with hj
    · rw [← hj, hs1]
    · obtain ⟨i', rfl⟩ := hbij.2 j
      have h0 := horth i i' (fun h => hj (h ▸ rfl)) (s i')
      rwa [hs1, mul_one] at h0
  simp [hsum i, hgi, ite_smul]

namespace SkewZigzagParameter

/-- **Gauge classes up to graph automorphisms are the isomorphism classes permuting the vertex
idempotents.** Over a nontrivial commutative ring, a relabelling of `c` along a graph automorphism
is gauge equivalent to `c'` exactly when the relation quotients of `c` and `c'` are isomorphic by an
algebra isomorphism sending each vertex idempotent `e_i` to `e_{σ i}` for a permutation `σ`. -/
theorem exists_isGaugeEquivalent_relabel_iff_exists_vertexPermuting_algEquiv [Nontrivial k] :
    (∃ τ : G ≃g G, (c.relabel τ).IsGaugeEquivalent c') ↔
      ∃ φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c', ∃ σ : V ≃ V,
        ∀ i : V, φ (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) =
          skewZigzagMk k G c' (vertexIdempotent k (vertex G (σ i))) := by
  refine ⟨fun ⟨τ, h⟩ => ?_, fun ⟨φ, σ, hφ⟩ => ?_⟩
  · obtain ⟨ψ, hψ⟩ := isGaugeEquivalent_iff_exists_vertexFixing_algEquiv.mp h
    refine ⟨(skewZigzagQuotientEquiv k τ c).trans ψ, τ.toEquiv, fun i => ?_⟩
    rw [AlgEquiv.trans_apply, skewZigzagQuotientEquiv_skewZigzagMk,
      pathAlgebraEquiv_vertexIdempotent, hψ, RelIso.coe_fn_toEquiv]
  · obtain ⟨τ, -, h⟩ := φ.exists_iso_isGaugeEquivalent_relabel_of_vertexPermuting σ hφ
    exact ⟨τ, h⟩

/-- **Gauge classes up to graph automorphisms are the isomorphism classes preserving vertex span.**
If the coefficient ring has only trivial idempotents, a relabelling of `c` along a graph
automorphism is gauge equivalent to `c'` exactly when the relation quotients of `c` and `c'` are
isomorphic by an algebra isomorphism mapping every
vertex idempotent into the span of the vertex idempotents. -/
theorem exists_isGaugeEquivalent_relabel_iff_exists_algEquiv_mem_span [Nontrivial k]
    (hidempotents : ∀ e : k, IsIdempotentElem e → e = 0 ∨ e = 1) :
    (∃ τ : G ≃g G, (c.relabel τ).IsGaugeEquivalent c') ↔
      ∃ φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c',
        ∀ i : V, φ (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) ∈
          Submodule.span k (Set.range fun j : V =>
            skewZigzagMk k G c' (vertexIdempotent k (vertex G j))) := by
  rw [exists_isGaugeEquivalent_relabel_iff_exists_vertexPermuting_algEquiv]
  refine ⟨fun ⟨φ, σ, hφ⟩ => ⟨φ, fun i => ?_⟩, fun ⟨φ, hφ⟩ => ⟨φ, ?_⟩⟩
  · rw [hφ i]
    exact Submodule.subset_span ⟨σ i, rfl⟩
  · exact φ.exists_equiv_apply_vertexIdempotent_of_mem_span hidempotents hφ

/-- Gauge equivalence up to graph automorphisms is equivalent to the existence of an algebra
isomorphism taking each vertex idempotent into the degree-zero piece of the target skew-zigzag
quotient. This reformulates the vertex-span criterion using the induced grading. -/
theorem exists_isGaugeEquivalent_relabel_iff_exists_algEquiv_vertexImages_mem_grade_zero
    [Nontrivial k] (hidempotents : ∀ e : k, IsIdempotentElem e → e = 0 ∨ e = 1) :
    (∃ τ : G ≃g G, (c.relabel τ).IsGaugeEquivalent c') ↔
      ∃ φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c',
        ∀ i : V, φ (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) ∈
          skewZigzagGrade k G c' 0 := by
  simpa only [skewZigzagGrade_zero_eq_span_range_vertexIdempotent] using
    exists_isGaugeEquivalent_relabel_iff_exists_algEquiv_mem_span hidempotents

/-- **Couture's classification up to graph automorphisms, permuting form.** Over a nontrivial
commutative ring, the cohomology classes of `c` and `c'` lie in one orbit of the graph automorphisms
on `H¹(G, kˣ)` exactly when the relation quotients of `c` and `c'` are isomorphic by an algebra
isomorphism permuting the vertex idempotents. -/
theorem exists_firstCohomologyRelabel_eq_iff_exists_vertexPermuting_algEquiv [Nontrivial k] :
    (∃ τ : G ≃g G,
        SimpleGraph.firstCohomologyRelabel kˣ τ (cohomologyClass k G c) = cohomologyClass k G c') ↔
      ∃ φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c', ∃ σ : V ≃ V,
        ∀ i : V, φ (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) =
          skewZigzagMk k G c' (vertexIdempotent k (vertex G (σ i))) := by
  simp_rw [← cohomologyClass_relabel, cohomologyClass_eq_iff]
  exact exists_isGaugeEquivalent_relabel_iff_exists_vertexPermuting_algEquiv

/-- **Couture's classification up to graph automorphisms.** If the coefficient ring has only
trivial idempotents, the cohomology classes of `c` and `c'` lie in one orbit of the graph
automorphisms on `H¹(G, kˣ)` exactly when the
relation quotients of `c` and `c'` are isomorphic by an algebra isomorphism mapping every vertex
idempotent into the span of the vertex idempotents. -/
theorem exists_firstCohomologyRelabel_eq_iff_exists_algEquiv_mem_span [Nontrivial k]
    (hidempotents : ∀ e : k, IsIdempotentElem e → e = 0 ∨ e = 1) :
    (∃ τ : G ≃g G,
        SimpleGraph.firstCohomologyRelabel kˣ τ (cohomologyClass k G c) = cohomologyClass k G c') ↔
      ∃ φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c',
        ∀ i : V, φ (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) ∈
          Submodule.span k (Set.range fun j : V =>
            skewZigzagMk k G c' (vertexIdempotent k (vertex G j))) := by
  simp_rw [← cohomologyClass_relabel, cohomologyClass_eq_iff]
  exact exists_isGaugeEquivalent_relabel_iff_exists_algEquiv_mem_span hidempotents

end SkewZigzagParameter

end TauCeti

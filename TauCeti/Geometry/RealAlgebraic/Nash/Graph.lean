/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Nash.OfSemialgebraic
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Topology
import TauCeti.Geometry.RealAlgebraic.CAD.Existence
import TauCeti.Geometry.RealAlgebraic.Stack.Selection
import TauCeti.Topology.Algebra.MvPolynomial.Nonvanishing
import TauCeti.Topology.ContinuousOn.ClosedGraph

/-!
# The local Nash graph criterion

A continuous real function satisfying one nonzero polynomial relation on an open semialgebraic
domain has a semialgebraic graph. Consequently a function is a Nash germ precisely when it is
analytic and has a semialgebraic graph on some open semialgebraic neighbourhood.

On the locus where the specialized polynomial is nonzero, a CAD adapted to its Collins
projection and to the domain gives finitely many connected base cells. A continuous root chooses
one fixed section over each cell. The native delineation handles repeated roots directly, so no
squarefree hypothesis is required. A nonzero coefficient has dense nonvanishing locus;
continuity recovers the entire graph, including the nullified fibres, from the closure of the
graph over this locus. In particular, no arbitrary values can be assigned on a nullified fibre.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998, Section 8.1.
* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Chapters 10 and 11 (Collins projection and delineability).
-/

public section

open Set MvPolynomial Topology
open scoped Polynomial

namespace TauCeti

/-- On a semialgebraic domain where a polynomial relation is nowhere nullified, a continuous
root has a semialgebraic graph. The domain need not be open and roots may be repeated. -/
private theorem isSemialgebraic_graph_of_polynomial_relation_of_not_nullified {n : ℕ}
    {s : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hs : IsSemialgebraic s) (hf : ContinuousOn f s) (P : (MvPolynomial (Fin n) ℝ)[X])
    (hne : ∀ x ∈ s, P.map (eval x) ≠ 0)
    (hrel : ∀ x ∈ s, (P.map (eval x)).IsRoot (f x)) :
    IsSemialgebraic {y : Fin (n + 1) → ℝ | Fin.tail y ∈ s ∧ f (Fin.tail y) = y 0} := by
  classical
  obtain ⟨m, p, Φ, hpres⟩ := hs.exists_eq_setOf_sign_eval
  let F : Finset (MvPolynomial (Fin n) ℝ)[X] := {P}
  obtain ⟨𝒞, h𝒞, hsign⟩ := exists_isCAD_signInvariant
    (F.collinsProjection ∪ Finset.univ.image p)
  have hcells (C) (hC : C ∈ 𝒞) : C ⊆ s ∨ Disjoint C s := by
    rw [hpres]
    exact subset_or_disjoint_setOf_sign (fun i ↦
      hsign _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))) C hC) Φ
  have hgraph (C) (hC : C ∈ 𝒞) (hCs : C ⊆ s) :
      IsSemialgebraic {y : Fin (n + 1) → ℝ | Fin.tail y ∈ C ∧ f (Fin.tail y) = y 0} := by
    have : ConnectedSpace C := isConnected_iff_connectedSpace.mp (h𝒞.isConnected hC)
    obtain ⟨D⟩ := nonempty_delineation_of_signInvariant_collinsProjection
      (F := F) (φ := RingHom.id ℝ) (h𝒞.isConnected hC).isPreconnected
      (fun q hq ↦ by
        simpa only [eval₂_id] using hsign q (Finset.mem_union_left _ hq) C hC)
    obtain ⟨i, hi⟩ := D.exists_eq_root_of_continuous (k := ⟨P, Finset.mem_singleton_self P⟩)
      (continuousOn_iff_continuous_domRestrict.mp (hf.mono hCs))
      (fun x ↦ hne x.1 (hCs x.2)) (fun x ↦ hrel x.1 (hCs x.2))
    convert (D.isSemialgebraicStack (h𝒞.isSemialgebraic hC)).isSemialgebraic_sectionSet i using 1
    ext y
    simp only [mem_ofPred_eq, mem_image_cylinder, mem_sectionSet]
    constructor
    · rintro ⟨hy, hfy⟩
      exact ⟨hy, (congr_fun hi ⟨Fin.tail y, hy⟩).symm.trans hfy⟩
    · rintro ⟨hy, hiy⟩
      exact ⟨hy, (congr_fun hi ⟨Fin.tail y, hy⟩).trans hiy⟩
  have heq : {y : Fin (n + 1) → ℝ | Fin.tail y ∈ s ∧ f (Fin.tail y) = y 0} =
      ⋃ C ∈ {C ∈ 𝒞 | C ⊆ s}, {y : Fin (n + 1) → ℝ | Fin.tail y ∈ C ∧ f (Fin.tail y) = y 0} := by
    ext y
    simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hy, hfy⟩
      obtain ⟨C, ⟨hC, hyC⟩, -⟩ := h𝒞.isPartition.2 (Fin.tail y)
      exact ⟨C, ⟨hC, (hcells C hC).resolve_right fun hd ↦ disjoint_left.mp hd hyC hy⟩,
        hyC, hfy⟩
    · rintro ⟨C, ⟨-, hCs⟩, hy, hfy⟩
      exact ⟨hCs hy, hfy⟩
  rw [heq]
  exact .biUnion (h𝒞.finite.subset (sep_subset _ _)) fun C hC ↦ hgraph C hC.1 hC.2

/-- On a semialgebraic domain, a continuous root of a nowhere-nullified polynomial relation
has semialgebraic graph. No openness or simplicity of the roots is required. -/
theorem isSemialgebraicOn_of_polynomial_relation_of_not_nullified {σ : Type*} [Finite σ]
    {s : Set (σ → ℝ)} {f : (σ → ℝ) → ℝ} (hs : IsSemialgebraic s)
    (hf : ContinuousOn f s) (P : (MvPolynomial σ ℝ)[X])
    (hne : ∀ x ∈ s, P.map (eval x) ≠ 0)
    (hrel : ∀ x ∈ s, (P.map (eval x)).IsRoot (f x)) :
    IsSemialgebraicOn (fun x (_ : Unit) ↦ f x) s := by
  let := Fintype.ofFinite σ
  let e := Fintype.equivFin σ
  let S := (fun y : Fin (Fintype.card σ) → ℝ ↦ y ∘ e) ⁻¹' s
  have hS : IsSemialgebraic S := hs.preimage_comp e
  have hmap (y : Fin (Fintype.card σ) → ℝ) :
      (P.map (rename e).toRingHom).map (eval y) = P.map (eval (y ∘ e)) := by
    ext j
    simp [Polynomial.coeff_map, eval_rename]
  have hG := isSemialgebraic_graph_of_polynomial_relation_of_not_nullified hS
    (hf.comp (by fun_prop) (fun _ hx ↦ hx)) (P.map (rename e).toRingHom)
    (fun y hy ↦ by rw [hmap]; exact hne _ hy)
    (fun y hy ↦ by rw [hmap]; exact hrel _ hy)
  apply (isSemialgebraicOn_preimage_comp_equiv_iff e).mp
  refine isSemialgebraicOn_def.mpr ⟨hS, ?_⟩
  -- Convert the distinguished-coordinate graph to the input-by-output graph encoding.
  convert hG.preimage_eval
    (Fin.cons (MvPolynomial.X (Sum.inr ())) (fun j ↦ MvPolynomial.X (Sum.inl j))) using 1
  ext z
  simp only [Equiv.sumArrowEquivProdArrow, Function.comp_def, Equiv.coe_fn_mk, mem_preimage,
    mem_graphOn, funext_iff, Fin.tail_def, Function.comp_apply, preimage_ofPred_eq,
    Fin.cons_succ, eval_X, Fin.cons_zero, mem_ofPred_eq, and_congr_right_iff, S]
  intro _
  exact ⟨fun h ↦ h (), fun h u ↦ by cases u; exact h⟩

/-- A continuous function satisfying a single nonzero polynomial relation on an open
semialgebraic domain has semialgebraic graph, including over nullified fibres. -/
theorem isSemialgebraicOn_of_polynomial_relation {σ : Type*} [Finite σ]
    {s : Set (σ → ℝ)} {f : (σ → ℝ) → ℝ} (hs : IsSemialgebraic s) (hso : IsOpen s)
    (hf : ContinuousOn f s) (P : (MvPolynomial σ ℝ)[X]) (hP : P ≠ 0)
    (hrel : ∀ x ∈ s, (P.map (eval x)).IsRoot (f x)) :
    IsSemialgebraicOn (fun x (_ : Unit) ↦ f x) s := by
  obtain ⟨j, hj⟩ : ∃ j, P.coeff j ≠ 0 := by
    by_contra h
    exact hP (Polynomial.ext fun j ↦ by simpa using not_exists.mp h j)
  let t := s ∩ {x | eval x (P.coeff j) ≠ 0}
  have ht : IsSemialgebraic t := hs.inter (isSemialgebraic_eval_ne_zero (P.coeff j))
  have hts : t ⊆ s := inter_subset_left
  have hst : s ⊆ closure t := by
    have h := hso.closure_inter (s := {x | eval x (P.coeff j) ≠ 0})
    simpa only [(P.coeff j).dense_setOf_eval_ne_zero hj |>.closure_eq, univ_inter,
      inter_comm, inter_univ] using h
  have hG := isSemialgebraicOn_of_polynomial_relation_of_not_nullified ht (hf.mono hts) P
    (fun x hx hzero ↦ hx.2 (by
      simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using
        congrArg (fun Q : ℝ[X] ↦ Q.coeff j) hzero))
    (fun x hx ↦ hrel x hx.1)
  let e := Homeomorph.sumArrowHomeomorphProdArrow (X := ℝ) (ι := σ) (ι' := Unit)
  have he : ⇑e = ⇑(Equiv.sumArrowEquivProdArrow σ Unit ℝ) := by
    -- This homeomorphism equips precisely the graph-encoding equivalence with its topology.
    rfl
  have hcl := (continuousOn_pi.mpr (fun _ : Unit ↦ hf)).closure_graphOn_inter hts hst
  refine isSemialgebraicOn_def.mpr ⟨hs, ?_⟩
  have hsemi := hG.graph.closure.inter (hs.preimage_comp Sum.inl)
  rw [← he, ← e.preimage_closure] at hsemi
  convert hsemi using 1
  ext z
  have hz := Set.ext_iff.mp hcl (e z)
  simpa [he, Equiv.sumArrowEquivProdArrow, Function.comp_def] using hz.symm

/-- **The local Nash graph criterion.** A scalar function is a Nash germ at `x` exactly when
it is analytic there and its graph is semialgebraic on some open semialgebraic neighbourhood. -/
theorem isNashAt_iff_exists_isSemialgebraicOn {σ : Type*} [Fintype σ]
    {f : (σ → ℝ) → ℝ} {x : σ → ℝ} :
    IsNashAt f x ↔ AnalyticAt ℝ f x ∧ ∃ U, IsOpen U ∧ x ∈ U ∧ IsSemialgebraic U ∧
      IsSemialgebraicOn (fun y (_ : Unit) ↦ f y) U := by
  constructor
  · intro hf
    obtain ⟨U, hU, hfa, P, hP, hrel⟩ := isNashAt_iff_exists_mem_nhds.mp hf
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
    have hB := isSemialgebraic_ball x r
    exact ⟨hf.analyticAt, Metric.ball x r, Metric.isOpen_ball, Metric.mem_ball_self hr, hB,
      isSemialgebraicOn_of_polynomial_relation hB Metric.isOpen_ball
        (hfa.continuousOn.mono hball) P hP (fun y hy ↦ hrel y (hball hy))⟩
  · rintro ⟨hf, U, hUo, hxU, -, hG⟩
    exact hG.isNashAt hf (hUo.mem_nhds hxU)

/-- Finitely many Nash germs have semialgebraic graphs on one common open semialgebraic
neighbourhood. This includes the empty family. -/
theorem exists_isSemialgebraicOn_of_forall_isNashAt {σ ι : Type*} [Fintype σ] [Finite ι]
    {f : ι → (σ → ℝ) → ℝ} {x : σ → ℝ} (hf : ∀ i, IsNashAt (f i) x) :
    ∃ U, IsOpen U ∧ x ∈ U ∧ IsSemialgebraic U ∧
      ∀ i, IsSemialgebraicOn (fun y (_ : Unit) ↦ f i y) U := by
  choose U hUo hxU hU hG using fun i ↦ (isNashAt_iff_exists_isSemialgebraicOn.mp (hf i)).2
  refine ⟨⋂ i, U i, isOpen_iInter_of_finite hUo, mem_iInter.mpr hxU,
    .iInter hU, fun i ↦ ?_⟩
  exact (hG i).mono (.iInter hU) (iInter_subset U i)

end TauCeti

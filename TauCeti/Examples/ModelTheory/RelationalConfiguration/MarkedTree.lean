/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.ModelTheory.RelationalConfiguration.OrderClass
public import TauCeti.ModelTheory.RelationalConfiguration.MarkedTree

/-!
# Checks for the cover graph of a coded order

The cover graph of the chain `(ℕ, ≤)` with its least element marked is a ray with its end marked:
`u` and `v` are adjacent exactly when they differ by one, and `0` is the only marked vertex. In
particular it is a marked tree, so `markedTreeClass` contains an infinite code.

The checks of the two presentations of trees:

* the same ray with the vertex `1` marked is not isomorphic to the ray with `0` marked, as distinct
  roots give distinct orders;
* the cover graph of the star, in which `0` lies below every element and other pairs are
  incomparable, is the star with its centre marked;
* the cover-graph map is not continuous on `treeClass`: inserting `n` between `0` and `1` in the
  star gives coded trees `T_n` converging to the star, but `0` and `1` are adjacent in the cover
  graph of the star and in that of no `T_n` with `n ≥ 2`.

The star and the trees `T_n` as coded trees, and the trees of finite sequences, are in the
examples for `OrderClass`.
-/

public section

open FirstOrder FirstOrder.Language TauCeti TauCeti.RelationalConfiguration
  TauCeti.Examples.ModelTheory.OrderClass

namespace TauCeti.Examples.MarkedTree

/-- The code of the chain `(ℕ, ≤)`. -/
noncomputable abbrev chain : RelationalConfiguration Language.order ℕ :=
  @ofStructure Language.order ℕ (orderStructure ℕ)

private theorem relCovBy_chain (u v : ℕ) : RelCovBy (codeRel leSymb chain) u v ↔ u + 1 = v := by
  rw [relCovBy_codeRel_leSymb_ofStructure_orderStructure, Nat.covBy_iff_add_one_eq]

/-- In the cover graph of `(ℕ, ≤)`, two vertices are adjacent exactly when they differ by one. -/
private theorem codeRel_coverGraphCode_chain (u v : ℕ) :
    codeRel adjSymb (coverGraphCode chain) u v ↔ u + 1 = v ∨ v + 1 = u := by
  rw [codeRel_coverGraphCode, relCovBy_chain, relCovBy_chain]

/-- In the cover graph of `(ℕ, ≤)`, the only marked vertex is `0`. -/
private theorem isMarked_coverGraphCode_chain (v : ℕ) :
    IsMarked (coverGraphCode chain) v ↔ v = 0 := by
  simp only [isMarked_coverGraphCode, chain, codeRel_leSymb_ofStructure_orderStructure]
  exact ⟨fun h => Nat.le_zero.1 (h 0), fun h w => h ▸ Nat.zero_le w⟩

/-- The graph of the cover graph of `(ℕ, ≤)` is the Hasse diagram of `ℕ`. -/
private theorem markedGraph_coverGraphCode_chain :
    markedGraph (coverGraphCode chain) = SimpleGraph.hasse ℕ := by
  ext u v
  simp only [markedGraph_adj, codeRel_coverGraphCode_chain, SimpleGraph.hasse_adj,
    Nat.covBy_iff_add_one_eq]
  omega

/-- The cover graph of `(ℕ, ≤)` is a marked tree: the ray with its end `0` marked. -/
example : coverGraphCode chain ∈ markedTreeClass := by
  refine mem_markedTreeClass.2 ⟨fun u v h => ?_, fun v h => ?_,
    markedGraph_coverGraphCode_chain ▸ ⟨⟨SimpleGraph.preconnected_hasse_of_succOrder ℕ⟩,
      SimpleGraph.isAcyclic_hasse_of_linearOrder ℕ⟩, 0, (isMarked_coverGraphCode_chain 0).2 rfl,
    fun v hv => (isMarked_coverGraphCode_chain v).1 hv⟩
  · rw [codeRel_coverGraphCode_chain] at h ⊢
    exact h.symm
  · rw [codeRel_coverGraphCode_chain] at h
    omega

/-! ### Rays with distinct marked vertices -/

/-- The ray on `ℕ`, `u` and `v` adjacent when they differ by one, with the vertex `m` marked. -/
@[instance_reducible]
def rayStructure (m : ℕ) : markedGraphLanguage.Structure ℕ where
  RelMap
    | .adj => fun x => x 0 + 1 = x 1 ∨ x 1 + 1 = x 0
    | .mark => fun x => x 0 = m

/-- The code of the ray with the vertex `m` marked. -/
noncomputable abbrev ray (m : ℕ) : RelationalConfiguration markedGraphLanguage ℕ :=
  @ofStructure markedGraphLanguage ℕ (rayStructure m)

private theorem codeRel_ray (m u v : ℕ) : codeRel adjSymb (ray m) u v ↔ u + 1 = v ∨ v + 1 = u := by
  rw [ray, @codeRel_ofStructure _ _ (rayStructure m)]
  exact Iff.rfl

private theorem isMarked_ray (m v : ℕ) : IsMarked (ray m) v ↔ v = m := by
  rw [ray, @isMarked_ofStructure _ (rayStructure m)]
  exact Iff.rfl

/-- The cover graph of `(ℕ, ≤)` is the ray with `0` marked. -/
theorem coverGraphCode_chain : coverGraphCode chain = ray 0 :=
  ext_markedGraph (fun u v => by rw [codeRel_coverGraphCode_chain, codeRel_ray])
    fun v => by rw [isMarked_coverGraphCode_chain, isMarked_ray]

/-- The ray with `1` marked is not isomorphic to the ray with `0` marked. -/
theorem not_isoSetoid_ray_zero_one : ¬ isoSetoid markedGraphLanguage ℕ (ray 0) (ray 1) := by
  -- a relabelling would send `1` to `0`, and the two neighbours `0`, `2` of `1` to neighbours
  -- of `0`, of which there is only `1`
  intro h
  obtain ⟨σ, hσ⟩ := isoSetoid_iff_exists_perm_smul_eq.1 h
  have hmark : σ.symm 1 = 0 := by
    have := isMarked_perm_smul σ (ray 0) 1
    rw [hσ, isMarked_ray, isMarked_ray] at this
    exact this.1 rfl
  have hadj (u v : ℕ) : codeRel adjSymb (ray 1) u v ↔ codeRel adjSymb (ray 0) (σ.symm u)
      (σ.symm v) := by
    rw [← hσ, codeRel_perm_smul]
  have h0 := (hadj 1 0).1 ((codeRel_ray 1 1 0).2 (.inr rfl))
  have h2 := (hadj 1 2).1 ((codeRel_ray 1 1 2).2 (.inl rfl))
  rw [hmark, codeRel_ray] at h0 h2
  have : σ.symm 0 = σ.symm 2 := by omega
  exact absurd (σ.symm.injective this) (by decide)

/-! ### The cover graph of the star -/

/-- In the cover graph of the star, `u` and `v` are adjacent exactly when one of them is `0` and
the other is not. Its marked vertices are described by `isMarked_coverGraphCode_star`. -/
theorem codeRel_coverGraphCode_star (u v : ℕ) :
    codeRel adjSymb (coverGraphCode star) u v ↔ u = 0 ∧ v ≠ 0 ∨ v = 0 ∧ u ≠ 0 := by
  have hcov (a b : ℕ) : RelCovBy (codeRel leSymb star) a b ↔ a = 0 ∧ b ≠ 0 := by
    rw [codeRel_ofRel, relCovBy_iff]
    refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨ha, hb⟩ => ⟨⟨.inl ha, ?_⟩, fun w hw => ?_⟩⟩
    · rcases h.1.1 with h' | h' <;> [exact h'; exact absurd (.inr h'.symm) h.1.2]
    · rintro rfl
      exact h.1.2 (.inl rfl)
    · rintro (h | h) <;> omega
    · obtain ⟨⟨_, hw0⟩, hwb, hbw⟩ := hw
      rcases hwb with h | h
      · exact hw0 (.inl h)
      · exact hbw (.inr h.symm)
  rw [codeRel_coverGraphCode, hcov, hcov]

/-- In the cover graph of the star, `0` is the only marked vertex. -/
theorem isMarked_coverGraphCode_star (v : ℕ) : IsMarked (coverGraphCode star) v ↔ v = 0 := by
  rw [isMarked_coverGraphCode, codeRel_ofRel]
  refine ⟨fun h => ?_, fun h w => .inl h⟩
  rcases h (v + 1) with h | h <;> omega

/-! ### The cover-graph map is not continuous on `treeClass` -/

/-- In the cover graph of the star with `n ≥ 2` inserted, `0` and `1` are not adjacent. -/
theorem not_codeRel_coverGraphCode_starInsert {n : ℕ} (hn : 2 ≤ n) :
    ¬ codeRel adjSymb (coverGraphCode (starInsert n)) 0 1 := by
  rw [codeRel_coverGraphCode, codeRel_ofRel, relCovBy_iff, relCovBy_iff]
  rintro (⟨-, h⟩ | ⟨⟨h, -⟩, -⟩)
  · exact h n ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  · omega

/-- The stars with `n` inserted between `0` and `1` converge to the star: each coordinate is
eventually that of the star. -/
theorem tendsto_starInsert : Filter.Tendsto starInsert Filter.atTop (nhds star) := by
  refine tendsto_nhds_iff.2 fun a => ?_
  induction a using Atom.induction_atom with | @h k R v => ?_
  obtain rfl : k = 2 := by cases R; rfl
  rw [order.relation_eq_leSymb R]
  refine tendsto_const_nhds.congr' ?_
  -- once `n` exceeds the first vertex, the clause `x = n ∧ y = 1` is false
  filter_upwards [Filter.eventually_gt_atTop (Finset.univ.sup v)] with n hn
  rw [eval_ofRel, eval_ofRel]
  have h0 := (Finset.le_sup (f := v) (Finset.mem_univ 0)).trans_lt hn
  refine decide_eq_decide.2 ?_
  omega

/-- **The cover-graph map is not continuous on `treeClass`.** -/
theorem not_continuousOn_coverGraphCode :
    ¬ ContinuousOn (coverGraphCode : RelationalConfiguration Language.order ℕ → _) treeClass := by
  intro hcont
  have hT := (hcont star star_mem_treeClass).tendsto.comp
    (tendsto_nhdsWithin_iff.2 ⟨tendsto_starInsert,
      Filter.Eventually.of_forall starInsert_mem_treeClass⟩)
  have hE := ((continuous_eval (atom adjSymb ![0, 1])).tendsto _).comp hT
  have hstar : (coverGraphCode star).eval (atom adjSymb ![0, 1]) = true := by
    rw [← codeRel_iff, codeRel_coverGraphCode_star]
    omega
  rw [hstar] at hE
  obtain ⟨n, hn⟩ := ((Filter.eventually_ge_atTop 2).and
    (hE.eventually ((isOpen_discrete {true}).mem_nhds (Set.mem_singleton _)))).exists
  exact not_codeRel_coverGraphCode_starInsert hn.1 (codeRel_iff.2 (Set.mem_singleton_iff.1 hn.2))

end TauCeti.Examples.MarkedTree

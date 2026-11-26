/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.MarkedTree

/-!
# Checks for the cover graph of a coded order

The cover graph of the chain `(ℕ, ≤)` with its least element marked is a ray with its end marked:
`u` and `v` are adjacent exactly when they differ by one, and `0` is the only marked vertex. In
particular it is a marked tree, so `markedTreeClass` contains an infinite code.

The checks of the two presentations of trees (CountableStructureSpacesPartII §3.5):

* the same ray with the vertex `1` marked is not isomorphic to the ray with `0` marked, as distinct
  roots give distinct orders;
* the cover graph of the star, in which `0` lies below every element and other pairs are
  incomparable, is the star with its centre marked;
* the cover-graph map is not continuous on `treeClass`: inserting `n` between `0` and `1` in the
  star gives coded trees `T_n` converging to the star, but `0` and `1` are adjacent in the cover
  graph of the star and in that of no `T_n`;
* a finite tree of finite sequences, such as `{[], [0], [1], [0, 0]}`, has no code on `ℕ`, while
  the full tree `List ℕ` has a code in `treeClass`.
-/

public section

open FirstOrder FirstOrder.Language TauCeti TauCeti.RelationalConfiguration

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

/-- **Distinct roots give distinct marked trees**: the ray with `1` marked is not isomorphic to
the ray with `0` marked. A relabelling would send `0` to `1`, and the two neighbours `0`, `2` of
`1` to neighbours of `0`, of which there is only `1`. -/
theorem not_isoSetoid_ray_zero_one : ¬ isoSetoid markedGraphLanguage ℕ (ray 0) (ray 1) := by
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

/-! ### The star -/

/-- The code of the star, in which `0` lies below every element and other pairs are
incomparable. -/
noncomputable abbrev star : RelationalConfiguration Language.order ℕ :=
  ofRel fun x y : ℕ => x = 0 ∨ x = y

/-- The star is a coded tree. -/
theorem star_mem_treeClass : star ∈ treeClass := by
  rw [mem_treeClass, codeRel_ofRel]
  have hpo : IsPartialOrder ℕ (fun x y : ℕ => x = 0 ∨ x = y) :=
    { refl := fun _ => .inr rfl
      trans := by rintro a b c (h | h) (h' | h') <;> omega
      antisymm := by rintro a b (h | h) (h' | h') <;> omega }
  refine ⟨hpo, ⟨0, fun _ => .inl rfl⟩, fun x => ?_, fun x => ?_⟩
  · exact ((Set.finite_singleton 0).union (Set.finite_singleton x)).subset fun y hy => by
      simpa only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq] using hy
  · rintro a (h | h) b (h' | h') - <;> omega

/-- **The cover graph of the star is the star with its centre marked**: `u` and `v` are adjacent
exactly when one of them is `0` and the other is not, and `0` is the only marked vertex. -/
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

/-- The star with `n` inserted between `0` and `1`: `0 < n < 1`, every other vertex a leaf above
`0`. -/
noncomputable abbrev starInsert (n : ℕ) : RelationalConfiguration Language.order ℕ :=
  ofRel fun x y : ℕ => x = y ∨ x = 0 ∨ x = n ∧ y = 1

/-- The star with `n` inserted between `0` and `1` is a coded tree (for `n ≤ 1` it is the
star). -/
theorem starInsert_mem_treeClass (n : ℕ) : starInsert n ∈ treeClass := by
  rw [mem_treeClass, codeRel_ofRel]
  have hpo : IsPartialOrder ℕ (fun x y : ℕ => x = y ∨ x = 0 ∨ x = n ∧ y = 1) :=
    { refl := fun _ => .inl rfl
      trans := by
        rintro a b c (h | h | ⟨h, h'⟩) (k | k | ⟨k, k'⟩) <;> omega
      antisymm := by
        rintro a b (h | h | ⟨h, h'⟩) (k | k | ⟨k, k'⟩) <;> omega }
  refine ⟨hpo, ⟨0, fun _ => .inr (.inl rfl)⟩, fun x => ?_, fun x => ?_⟩
  · exact (((Set.finite_singleton x).union (Set.finite_singleton 0)).union
      (Set.finite_singleton n)).subset fun y hy => by
        simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq] at hy ⊢
        omega
  · rintro a ha b hb -
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    omega

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
  refine tendsto_pi_nhds.2 fun a => ?_
  simp only [← eval_def]
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

/-! ### Trees of finite sequences -/

/-- A finite tree of finite sequences has no code on `ℕ`: its prefix order is isomorphic to the
order of no coded tree, since `ℕ` is infinite. -/
theorem isEmpty_relIso_of_finite {T : Descriptive.tree ℕ} (hT : (T : Set (List ℕ)).Finite)
    (c : RelationalConfiguration Language.order ℕ) :
    IsEmpty (codeRel leSymb c ≃r fun x y : T => (x : List ℕ) <+: y) :=
  ⟨fun e => have : Finite T := hT.to_subtype
    not_finite_iff_infinite.2 inferInstance (Finite.of_injective e e.injective)⟩

/-- The tree `{[], [0], [1], [0, 0]}`. -/
def smallTree : Descriptive.tree ℕ :=
  ⟨{[], [0], [1], [0, 0]}, by
    intro x a h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
    rcases h with h | h | h | h
    · simp at h
    · obtain ⟨rfl, -⟩ := List.append_eq_singleton_iff.1 h |>.resolve_right (by simp)
      simp
    · obtain ⟨rfl, -⟩ := List.append_eq_singleton_iff.1 h |>.resolve_right (by simp)
      simp
    · have := congrArg List.dropLast h
      simp at this
      simp [this]⟩

/-- The tree `{[], [0], [1], [0, 0]}` is finite and so has no code on `ℕ`. -/
example (c : RelationalConfiguration Language.order ℕ) :
    IsEmpty (codeRel leSymb c ≃r fun x y : smallTree => (x : List ℕ) <+: y) :=
  isEmpty_relIso_of_finite (Set.toFinite (s := ({[], [0], [1], [0, 0]} : Set (List ℕ)))) c

/-- The full tree `List ℕ`, infinitely branching, has a code in `treeClass`. -/
example : ∃ c : RelationalConfiguration Language.order ℕ, c ∈ treeClass ∧
    Nonempty (codeRel leSymb c ≃r fun x y : (⊤ : Descriptive.tree ℕ) => (x : List ℕ) <+: y) :=
  exists_mem_treeClass_relIso (by simpa using Set.infinite_univ)

end TauCeti.Examples.MarkedTree

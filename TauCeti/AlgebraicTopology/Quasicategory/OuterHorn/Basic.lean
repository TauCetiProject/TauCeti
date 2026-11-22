/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.Slice
public import TauCeti.AlgebraicTopology.SimplicialSet.Horn

/-!
# Joyal's theorem on special outer horns and the Kan complex property of the core

In a quasicategory `C`, the outer horns `Λ[n + 2, 0]` cannot be filled in general, but they can
when their initial edge, from `0` to `1`, is an equivalence. Conversely, an edge all of whose
outer horns `Λ[n + 2, 0]` can be filled is an equivalence (HTT Proposition 1.2.4.3). Passing to
the opposite quasicategory `Cᵒᵖ` gives the dual criterion for the final outer horns
`Λ[n + 2, Fin.last (n + 2)]` whose final edge, from `n + 1` to `n + 2`, is an equivalence.

Together with inner horn filling, the two special outer horn theorems imply Joyal's criterion: a
simplicial set is a Kan complex exactly when it is a quasicategory in which every edge is an
equivalence. In particular, the core `C.core` of a quasicategory is a Kan complex
(`SSet.core.kanComplex`, HTT Proposition 1.2.5.3), and hence the largest Kan subcomplex of `C`
(`SSet.isGreatest_core`).

The proof for `Λ[n + 2, 0]` follows Kerodon: under the isomorphism `Δ[1] ⋆ Δ[n] ≅ Δ[n + 2]`, the
horn `Λ[n + 2, 0]` is the pushout-join `(Λ[1, 0] ⋆ Δ[n]) ∪ (Δ[1] ⋆ ∂Δ[n])`, so filling it amounts
to lifting an edge, with prescribed source, along the restriction of cones `C_{/σ} ⟶ C_{/∂σ}` for
the face `σ : Δ[n] ⟶ C` opposite to the vertices `0` and `1`. This restriction is a right
fibration, and right fibrations lift equivalences with prescribed source. The edge to be lifted is
an equivalence because its image in `C` is, and the projection `C_{/∂σ} ⟶ C` is a right fibration,
which reflects equivalences. These facts about right fibrations are in
`TauCeti.AlgebraicTopology.Quasicategory.RightFibration`, and the lifting property of the
restriction of cones is `SSet.slice.hasLift_of_isEquivalence`.

Conversely, filling the horns `Λ[2, 0]` and `Λ[3, 0]` with initial edge `e` produces a right
inverse of `e` and shows that it is also a left inverse. Reversing simplices via
`SSet.horn.opIsoLast` transports both directions to `Λ[n + 2, Fin.last (n + 2)]`.

## Main results

* `SSet.Quasicategory.hornFilling_zero`, `SSet.Quasicategory.hornFilling_last`: **Joyal's theorem**
  on special outer horns `Λ[n + 2, 0]` and `Λ[n + 2, Fin.last (n + 2)]`.
* `SSet.Quasicategory.exists_fill_of_ne_last`: a horn `Λ[d + 1, i]` with `i` not the last vertex
  can be filled when it is inner, or when `i = 0` and its initial edge is an equivalence.
* `SSet.Edge.isEquivalence_iff_hornFilling_zero`, `SSet.Edge.isEquivalence_iff_hornFilling_last`:
  an edge of a quasicategory is an equivalence if and only if every outer horn `Λ[n + 2, 0]`
  (respectively `Λ[n + 2, Fin.last (n + 2)]`) with that initial (respectively final) edge can be
  filled.
* `SSet.Quasicategory.kanComplex_of_forall_isEquivalence`,
  `SSet.kanComplex_iff_quasicategory_and_forall_isEquivalence`: **Joyal's criterion**, a simplicial
  set is a Kan complex if and only if it is a quasicategory in which every edge is an equivalence.
* `SSet.core.kanComplex`, `SSet.isGreatest_core`: the core of a quasicategory is a Kan complex, and
  the greatest Kan subcomplex of `C`.

## References

* A. Joyal, *Quasi-categories and Kan complexes*, J. Pure Appl. Algebra 175 (2002), Theorem 1.3
  and Corollaries 1.4 and 1.5.
* J. Lurie, *Higher Topos Theory*, Propositions 1.2.4.3 and 1.2.5.3.
* J. Lurie, *Kerodon*, Theorem 4.4.2.6, Proposition 4.4.2.11, Proposition 4.4.2.13,
  Example 4.4.1.11 and Corollary 4.4.3.2.
-/

public section

open CategoryTheory Limits Simplicial Opposite

universe u

namespace SSet

open Edge

namespace Quasicategory

variable {C : SSet.{u}}

/-- Under `Δ[1] ⋆ Δ[n] ≅ Δ[n + 2]`, the horn `Λ[n + 2, 0]` is the pushout-join
`(Λ[1, 0] ⋆ Δ[n]) ∪ (Δ[1] ⋆ ∂Δ[n])`: a horn `Λ[N, 0]`, `2 ≤ N`, whose initial edge is an
equivalence extends along it by `SSet.slice.hasLift_of_isEquivalence` for `∂Δ[n] ⟶ Δ[n]`. -/
private lemma hornFilling_zero_aux [Quasicategory C] (N : ℕ) (hN : 2 ≤ N)
    (σ₀ : (Λ[N, 0] : SSet) ⟶ C) (H : Finset.card {(0 : Fin (N + 1)), 0, 1} ≤ N)
    (h : (Edge.mk' (σ₀.app _ (horn.edge N 0 0 1 (Fin.zero_le _) H))).IsEquivalence) :
    ∃ σ : Δ[N] ⟶ C, σ₀ = Λ[N, 0].ι ≫ σ := by
  obtain ⟨n, rfl⟩ : ∃ n, N = 1 + n + 1 := ⟨N - 2, by omega⟩
  let E := join.stdSimplexIso 1 n
  let U := Subcomplex.unionJoin Λ[1, 0] ∂Δ[n]
  have hU : U.preimage E.inv = Λ[1 + n + 1, 0] := by
    rw [join.preimage_unionJoin_horn_boundary n one_ne_zero 0, Fin.castLE_zero]
  -- The isomorphism `E` restricts to an isomorphism `I` between `U` and the horn.
  let I := Subcomplex.isoOfPreimageEq E hU
  -- The two pieces `a` and `b` of `I.hom ≫ σ₀` on `Λ[1, 0] ⋆ Δ[n]` and `Δ[1] ⋆ ∂Δ[n]`, a vertex
  -- `A` of `C_{/p}` for the face `p : Δ[n] ⟶ C` and an edge `B` of `C_{/∂p}` from its restriction.
  have hpush := Subcomplex.unionJoin.isPushout Λ[1, 0] ∂Δ[n]
  let a := Subcomplex.unionJoin.ι₁ Λ[1, 0] ∂Δ[n] ≫ I.hom ≫ σ₀
  let b := Subcomplex.unionJoin.ι₂ Λ[1, 0] ∂Δ[n] ≫ I.hom ≫ σ₀
  let p := join.inr _ _ ≫ a
  have hw : join.map (𝟙 _) ∂Δ[n].ι ≫ a = join.map Λ[1, 0].ι (𝟙 _) ≫ b := hpush.w_assoc _
  have hb : join.inr _ _ ≫ b = ∂Δ[n].ι ≫ p := by
    calc join.inr _ _ ≫ b = join.inr _ _ ≫ join.map Λ[1, 0].ι (𝟙 _) ≫ b := by
          rw [join.inr_map_assoc, Category.id_comp]
      _ = ∂Δ[n].ι ≫ p := by rw [← hw, join.inr_map_assoc]
  let A : (Λ[1, 0] : SSet) ⟶ slice p := slice.homEquiv.symm ⟨a, rfl⟩
  let B : Δ[1] ⟶ slice (∂Δ[n].ι ≫ p) := slice.homEquiv.symm ⟨b, hb⟩
  have sq : CommSq A Λ[1, 0].ι (slice.map ∂Δ[n].ι (𝟙 C) (by simp)) B :=
    ⟨slice.hom_ext (by
      rw [slice.homEquiv_comp_map_coe, slice.homEquiv_comp_coe, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply, Category.comp_id, hw])⟩
  -- The edge underlying `B` is the initial edge of `σ₀`.
  have hB : (Edge.mk' (yonedaEquiv (B ≫ slice.π (∂Δ[n].ι ≫ p)))).IsEquivalence := by
    have hedge : yonedaEquiv (join.inl _ _ ≫ Subcomplex.unionJoin.ι₂ Λ[1, 0] ∂Δ[n] ≫ I.hom) =
        horn.edge (1 + n + 1) 0 0 1 (Fin.zero_le _) H := by
      refine injective_of_mono (Subcomplex.ι.{u} Λ[1 + n + 1, 0] |>.app _) ?_
      rw [← yonedaEquiv_comp, Category.assoc, Category.assoc, Subcomplex.isoOfPreimageEq_hom_ι E hU,
        Subcomplex.unionJoin.ι₂_ι_assoc, join.inl_map_assoc, Category.id_comp]
      exact join.yonedaEquiv_inl_comp_stdSimplexIso_hom_eq_edge n
    refine (isEquivalence_iff_of_edge_eq ?_).1 h
    rw [mk'_edge, mk'_edge, slice.comp_π, Equiv.apply_symm_apply, ← hedge, ← yonedaEquiv_comp]
    simp only [b, Category.assoc]
  have := slice.hasLift_of_isEquivalence p ∂Δ[n].ι sq hB
  let τ := (slice.homEquiv sq.lift).val
  have hτ : U.ι ≫ τ = I.hom ≫ σ₀ := hpush.hom_ext
    (by
      rw [Subcomplex.unionJoin.ι₁_ι_assoc, ← slice.homEquiv_comp_coe, sq.fac_left,
        Equiv.apply_symm_apply])
    (by
      have h := congrArg (fun F ↦ (slice.homEquiv F).val) sq.fac_right
      rw [slice.homEquiv_comp_map_coe, Equiv.apply_symm_apply, Category.comp_id] at h
      rw [Subcomplex.unionJoin.ι₂_ι_assoc, h])
  exact ⟨E.inv ≫ τ, by
    rw [← Subcomplex.isoOfPreimageEq_inv_ι_assoc E hU, hτ, I.inv_hom_id_assoc]⟩

/-- **Joyal's theorem on special outer horns** (HTT Proposition 1.2.4.3): in a quasicategory, a
horn `Λ[n + 2, 0]` whose initial edge, from `0` to `1`, is an equivalence can be filled. -/
theorem hornFilling_zero [Quasicategory C] {n : ℕ} (σ₀ : (Λ[n + 2, 0] : SSet) ⟶ C)
    (h : (Edge.mk' (σ₀.app _ (horn.edge (n + 2) 0 0 1 (Fin.zero_le _) (by simp)))).IsEquivalence) :
    ∃ σ : Δ[n + 2] ⟶ C, σ₀ = Λ[n + 2, 0].ι ≫ σ :=
  hornFilling_zero_aux (n + 2) (by omega) σ₀ _ h

/-- In a quasicategory, a horn `Λ[d + 1, i]` with `i` not the last vertex can be filled when it is
inner, or when `i = 0` and its initial edge is an equivalence. This combines inner horn filling
with `SSet.Quasicategory.hornFilling_zero`; the horn `Λ[1, 0]`, which has no initial edge, is a
single vertex. -/
lemma exists_fill_of_ne_last [Quasicategory C] {d : ℕ} {i : Fin (d + 2)}
    (hi : i ≠ Fin.last _) (σ₀ : (Λ[d + 1, i] : SSet) ⟶ C)
    (h0 : i = 0 → ∀ H, (Edge.mk' (σ₀.app _
      (horn.edge (d + 1) i 0 1 (Fin.zero_le _) H))).IsEquivalence) :
    ∃ σ : Δ[d + 1] ⟶ C, σ₀ = Λ[d + 1, i].ι ≫ σ := by
  by_cases hi0 : i = 0
  · subst hi0
    obtain _ | d := d
    · exact horn.exists_extension_one 0 σ₀
    · exact hornFilling_zero σ₀ (h0 rfl _)
  · exact hornFilling (Fin.pos_iff_ne_zero.2 hi0) (Fin.lt_last_iff_ne_last.2 hi) σ₀

/-- **Joyal's dual theorem on special outer horns** (HTT Proposition 1.2.4.3): in a quasicategory,
a horn `Λ[n + 2, Fin.last (n + 2)]` whose final edge, from `n + 1` to `n + 2`, is an equivalence
can be filled. -/
theorem hornFilling_last [Quasicategory C] {n : ℕ}
    (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet) ⟶ C)
    (h : (Edge.mk' (σ₀.app _ (horn.edge (n + 2) (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc
      (Fin.last (n + 2)) (Fin.le_last _) (by simp)))).IsEquivalence) :
    ∃ σ : Δ[n + 2] ⟶ C, σ₀ = Λ[n + 2, Fin.last (n + 2)].ι ≫ σ := by
  rw [horn.exists_extension_last_iff_op]
  refine hornFilling_zero _ ?_
  have hedge : ((horn.opIsoLast (n + 2)).inv ≫ opFunctor.map σ₀).app _
      (horn.edge (n + 2) 0 0 1 (Fin.zero_le _) (by simp)) =
    C.opObjEquiv.symm (σ₀.app _ (horn.edge (n + 2) (Fin.last (n + 2))
      (Fin.last (n + 1)).castSucc (Fin.last (n + 2)) (Fin.le_last _) (by simp))) := by
    rw [NatTrans.comp_app_apply, horn.opIsoLast_inv_app_edge_zero_one]
    simp [opFunctor_map]
  rwa [hedge, Edge.isEquivalence_mk'_opObjEquiv_symm_iff]

/-- **Joyal's Kan-complex criterion** (Joyal Corollary 1.4, HTT Proposition 1.2.4.3): a
quasicategory in which every edge is an equivalence is a Kan complex. -/
theorem kanComplex_of_forall_isEquivalence [Quasicategory C]
    (h : ∀ s : C _⦋1⦌, (Edge.mk' s).IsEquivalence) : KanComplex C :=
  kanComplex_of_outerHornFilling C (fun _ σ₀ ↦ hornFilling_zero σ₀ (h _))
    (fun _ σ₀ ↦ hornFilling_last σ₀ (h _))

/-- A quasicategory is a Kan complex if and only if its core is everything. -/
theorem kanComplex_iff_core_eq_top [Quasicategory C] : KanComplex C ↔ C.core = ⊤ :=
  ⟨fun _ ↦ core_eq_top, fun h ↦ kanComplex_of_forall_isEquivalence (core_eq_top_iff.1 h)⟩

end Quasicategory

/-- A simplicial set is a Kan complex if and only if it is a quasicategory in which every edge is
an equivalence. -/
theorem kanComplex_iff_quasicategory_and_forall_isEquivalence {C : SSet.{u}} :
    KanComplex C ↔ Quasicategory C ∧ ∀ s : C _⦋1⦌, (Edge.mk' s).IsEquivalence :=
  ⟨fun _ ↦ ⟨inferInstance, fun _ ↦ isEquivalence_of_kanComplex _⟩,
    fun ⟨_, h⟩ ↦ Quasicategory.kanComplex_of_forall_isEquivalence h⟩

namespace Edge

variable {C : SSet.{u}} {x y : C _⦋0⦌}

/-- If every horn `Λ[2, 0]` with initial edge `e : x ⟶ y` can be filled, `e` has a right inverse
up to a `2`-simplex: filling the horn with faces `e` (from `0` to `1`) and `id x` (from `0`
to `2`) gives an edge `g` with `e ≫ g = id x`. -/
private lemma exists_compStruct_id_of_hornFilling_zero (e : Edge x y)
    (H : ∀ σ₀ : (Λ[2, 0] : SSet) ⟶ C,
      σ₀.app _ (horn.edge 2 0 0 1 (Fin.zero_le _) (by simp)) = e.edge →
        ∃ σ : Δ[2] ⟶ C, σ₀ = Λ[2, 0].ι ≫ σ) :
    ∃ g : Edge y x, Nonempty (CompStruct e g (id x)) := by
  let f : ∀ j : Fin 3, j ≠ 0 → (Δ[1] ⟶ C) := fun j _ ↦
    ![yonedaEquiv.symm e.edge, yonedaEquiv.symm (id x).edge, yonedaEquiv.symm e.edge] j
  have hf : horn.IsCompatible f := by
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k <;> simp at hj hk hjk ⊢
    simp [f, stdSimplex.δ_comp_yonedaEquiv_symm, -id_edge]
  -- The initial edge of `Λ[2, 0]` is the edge of its face `2`.
  have hedge : horn.edge.{u} 2 0 0 1 (Fin.zero_le _) (by simp) =
      (horn.ι 0 2 (by decide)).app _ (yonedaEquiv (𝟙 Δ[1])) := by
    refine (horn.ι_app_edge 0 2 (by decide) 0 1 (Fin.zero_le _)).symm.trans (congrArg _ ?_)
    ext i
    fin_cases i <;> rfl
  obtain ⟨σ, hσ⟩ := H hf.desc (by
    rw [hedge, hf.desc_app_ι_app, ← yonedaEquiv_comp, Category.id_comp]
    exact yonedaEquiv.apply_symm_apply _)
  have hw₁ : C.δ 1 (yonedaEquiv σ) = (id x).edge := by
    simpa [f, -id_edge] using hf.δ_yonedaEquiv_of_desc_eq hσ 1 (by decide)
  have hw₂ : C.δ 2 (yonedaEquiv σ) = e.edge := by
    simpa [f] using hf.δ_yonedaEquiv_of_desc_eq hσ 2 (by decide)
  have hsrc : C.δ 1 (C.δ 0 (yonedaEquiv σ)) = y := by
    rw [← e.tgt_eq, ← hw₂]
    exact (δ_comp_δ_apply (i := 0) (j := 1) (by decide) _).symm
  have htgt : C.δ 0 (C.δ 0 (yonedaEquiv σ)) = x := by
    rw [← (id x).tgt_eq, ← hw₁]
    exact δ_comp_δ_self_apply (i := 0) _
  exact ⟨.mk _ hsrc htgt, ⟨.mk _ hw₂ rfl hw₁⟩⟩

/-- If every horn `Λ[3, 0]` with initial edge `e : x ⟶ y` can be filled, a right inverse `g` of
`e` is also a left inverse: filling the horn with faces given by `id x ≫ e = e` (on `0, 2, 3`),
`e ≫ id y = e` (on `0, 1, 3`) and `e ≫ g = id x` (on `0, 1, 2`), the remaining face exhibits
`g ≫ e = id y`. -/
private lemma nonempty_compStruct_id_of_hornFilling_zero {e : Edge x y} {g : Edge y x}
    (c : CompStruct e g (id x))
    (H : ∀ σ₀ : (Λ[3, 0] : SSet) ⟶ C,
      σ₀.app _ (horn.edge 3 0 0 1 (Fin.zero_le _) (by simp)) = e.edge →
        ∃ σ : Δ[3] ⟶ C, σ₀ = Λ[3, 0].ι ≫ σ) :
    Nonempty (CompStruct g e (id y)) := by
  let f : ∀ j : Fin 4, j ≠ 0 → (Δ[2] ⟶ C) := fun j _ ↦
    ![yonedaEquiv.symm c.simplex, yonedaEquiv.symm (CompStruct.idComp e).simplex,
      yonedaEquiv.symm (CompStruct.compId e).simplex, yonedaEquiv.symm c.simplex] j
  have hf : horn.IsCompatible f := by
    have h₂ : Fin.castPred (2 : Fin 4) (by decide) = 2 := rfl
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k <;> simp at hj hk hjk ⊢ <;>
      simp [f, h₂, stdSimplex.δ_comp_yonedaEquiv_symm, -id_edge,
        -CompStruct.idComp_simplex, -CompStruct.compId_simplex]
  -- The initial edge of `Λ[3, 0]` is the edge `δ 2` of its face `3`.
  have hedge : horn.edge.{u} 3 0 0 1 (Fin.zero_le _) (by simp) =
      (horn.ι 0 3 (by decide)).app _ (yonedaEquiv (stdSimplex.δ 2)) := by
    refine (horn.ι_app_edge 0 3 (by decide) 0 1 (Fin.zero_le _)).symm.trans (congrArg _ ?_)
    ext i
    fin_cases i <;> rfl
  obtain ⟨σ, hσ⟩ := H hf.desc (by
    rw [hedge, hf.desc_app_ι_app, ← yonedaEquiv_comp]
    simp [f, stdSimplex.δ_comp_yonedaEquiv_symm, c.d₂])
  have hw₁ : C.δ 1 (yonedaEquiv σ) = (CompStruct.idComp e).simplex := by
    simpa [f, -CompStruct.idComp_simplex] using hf.δ_yonedaEquiv_of_desc_eq hσ 1 (by decide)
  have hw₂ : C.δ 2 (yonedaEquiv σ) = (CompStruct.compId e).simplex := by
    simpa [f, -CompStruct.compId_simplex] using hf.δ_yonedaEquiv_of_desc_eq hσ 2 (by decide)
  have hw₃ : C.δ 3 (yonedaEquiv σ) = c.simplex := by
    simpa [f] using hf.δ_yonedaEquiv_of_desc_eq hσ 3 (by decide)
  have h₂ : C.δ 2 (C.δ 0 (yonedaEquiv σ)) = g.edge := by
    rw [← c.d₀, ← hw₃]
    exact (δ_comp_δ_apply (i := 0) (j := 2) (by decide) _).symm
  have h₀ : C.δ 0 (C.δ 0 (yonedaEquiv σ)) = e.edge := by
    rw [← (CompStruct.idComp e).d₀, ← hw₁]
    exact δ_comp_δ_self_apply (i := 0) _
  have h₁ : C.δ 1 (C.δ 0 (yonedaEquiv σ)) = (id y).edge := by
    rw [← (CompStruct.compId e).d₀, ← hw₂]
    exact (δ_comp_δ_apply (i := 0) (j := 1) (by decide) _).symm
  exact ⟨.mk _ h₂ h₀ h₁⟩

/-- **Joyal's characterization of equivalences by special outer horns** (HTT Proposition
1.2.4.3): an edge `e` of a quasicategory is an equivalence exactly when every horn
`Λ[n + 2, 0]` whose initial edge is `e` can be filled. -/
theorem isEquivalence_iff_hornFilling_zero [Quasicategory C] (e : Edge x y) :
    e.IsEquivalence ↔ ∀ (n : ℕ) (σ₀ : (Λ[n + 2, 0] : SSet) ⟶ C),
      σ₀.app _ (horn.edge (n + 2) 0 0 1 (Fin.zero_le _) (by simp)) = e.edge →
        ∃ σ : Δ[n + 2] ⟶ C, σ₀ = Λ[n + 2, 0].ι ≫ σ := by
  refine ⟨fun he n σ₀ h ↦ Quasicategory.hornFilling_zero σ₀
    ((isEquivalence_iff_of_edge_eq (e := mk' _) (e' := e) h).2 he), fun H ↦ ?_⟩
  obtain ⟨g, ⟨c₁⟩⟩ := exists_compStruct_id_of_hornFilling_zero e (H 0)
  obtain ⟨c₂⟩ := nonempty_compStruct_id_of_hornFilling_zero c₁ (H 1)
  exact InvStruct.isEquivalence { inv := g, homInvId := c₁, invHomId := c₂ }

/-- **Joyal's dual characterization of equivalences by special outer horns** (HTT Proposition
1.2.4.3): an edge `e` of a quasicategory is an equivalence exactly when every horn
`Λ[n + 2, Fin.last (n + 2)]` whose final edge is `e` can be filled. -/
theorem isEquivalence_iff_hornFilling_last [Quasicategory C] (e : Edge x y) :
    e.IsEquivalence ↔ ∀ (n : ℕ) (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet) ⟶ C),
      σ₀.app _ (horn.edge (n + 2) (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc
        (Fin.last (n + 2)) (Fin.le_last _) (by simp)) = e.edge →
        ∃ σ : Δ[n + 2] ⟶ C, σ₀ = Λ[n + 2, Fin.last (n + 2)].ι ≫ σ := by
  refine ⟨fun he n σ₀ h ↦ Quasicategory.hornFilling_last σ₀
    ((isEquivalence_iff_of_edge_eq (e := mk' _) (e' := e) h).2 he), fun H ↦ ?_⟩
  rw [← isEquivalence_opEquiv_iff, isEquivalence_iff_hornFilling_zero]
  intro n τ₀ hτ₀
  let σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet) ⟶ C :=
    opFunctor.preimage ((horn.opIsoLast (n + 2)).hom ≫ τ₀)
  have hτ₀' : (horn.opIsoLast (n + 2)).inv ≫ opFunctor.map σ₀ = τ₀ := by
    simp [σ₀]
  rw [← hτ₀', ← horn.exists_extension_last_iff_op]
  refine H n σ₀ (C.opObjEquiv.symm.injective ?_)
  have := congrArg (fun f ↦ f.app _ (horn.edge (n + 2) 0 0 1 (Fin.zero_le _) (by simp))) hτ₀'
  rw [NatTrans.comp_app_apply, horn.opIsoLast_inv_app_edge_zero_one] at this
  simpa [opFunctor_map] using this.trans hτ₀

end Edge

/-! ### The core of a quasicategory is a Kan complex -/

section Core

variable {C : SSet.{u}}

/-- The missing face `δ 0` of a filler in `C` of an outer horn `Λ[2, 0]` in `C.core` is an
equivalence, by two-out-of-three from the faces `δ 2` and `δ 1`. -/
private lemma isEquivalence_of_horn₂₀ [Quasicategory C] {a : (Λ[2, 0] : SSet) ⟶ C.core}
    {b : Δ[2] ⟶ C} (hab : a ≫ C.core.ι = Λ[2, 0].ι ≫ b) (y : Δ[2] _⦋1⦌)
    (hy : y ∉ Λ[2, 0].obj (op ⦋1⦌)) : (mk' (b.app _ y)).IsEquivalence := by
  obtain ⟨s, rfl⟩ := yonedaEquiv.symm.surjective b
  have hface (j : Fin 3) (hj : j ≠ 0) : (mk' (C.δ j s)).IsEquivalence := by
    have h : yonedaEquiv.symm (C.δ j s) = horn.ι 0 j hj ≫ a ≫ C.core.ι := by
      rw [← stdSimplex.δ_comp_yonedaEquiv_symm, ← horn.ι_ι 0 j hj, Category.assoc, hab]
    rw [← edge_mem_core_iff, mk'_edge, ← yonedaEquiv.apply_symm_apply (C.δ j s), h,
      yonedaEquiv_comp]
    exact (a.app _ _).property
  obtain ⟨f, rfl⟩ : ∃ f : ⦋1⦌ ⟶ ⦋2⦌, stdSimplex.objEquiv.symm f = y :=
    stdSimplex.objEquiv.symm.surjective y
  rw [yonedaEquiv_symm_app_objEquiv_symm]
  obtain rfl | rfl | rfl | ⟨k, rfl⟩ := SimplexCategory.eq_of_one_to_two' f
  · exact isEquivalence_mk'_δ_zero s (hface 2 (by decide)) (hface 1 (by decide))
  · exact absurd ((objEquiv_symm_δ_notMem_horn_iff _ _).1 hy) (by decide)
  · exact absurd ((objEquiv_symm_δ_notMem_horn_iff _ _).1 hy) (by decide)
  · exact isEquivalence_mk'_map_of_eq _ _ rfl

/-- Every outer horn `Λ[n + 2, 0]` in the core of a quasicategory can be filled. -/
theorem core.hornFilling_zero [Quasicategory C] {n : ℕ}
    (σ₀ : (Λ[n + 2, 0] : SSet) ⟶ C.core) :
    ∃ σ : Δ[n + 2] ⟶ C.core, σ₀ = Λ[n + 2, 0].ι ≫ σ := by
  have he : (mk' ((σ₀ ≫ C.core.ι).app _
      (horn.edge (n + 2) 0 0 1 (Fin.zero_le _) (by simp)))).IsEquivalence :=
    (edge_mem_core_iff (mk' _)).1 (σ₀.app _ _).property
  obtain ⟨b, hb⟩ := Quasicategory.hornFilling_zero (σ₀ ≫ C.core.ι) he
  have hrange : Subcomplex.range b ≤ C.core := by
    rw [range_le_core_iff]
    intro y
    by_cases hy : y ∈ Λ[n + 2, 0].obj (op ⦋1⦌)
    · have : b.app _ y = (σ₀.app _ ⟨y, hy⟩).val := congr($(hb).app _ ⟨y, hy⟩).symm
      exact (edge_mem_core_iff (mk' _)).1 (this ▸ (σ₀.app _ ⟨y, hy⟩).property)
    obtain _ | n := n
    · exact isEquivalence_of_horn₂₀ hb y hy
    · exact (hy (horn_obj_eq_univ (0 : Fin (n + 4)) 1 (by lia) ▸ Set.mem_univ y)).elim
  exact ⟨Subcomplex.lift b hrange, by rw [← cancel_mono C.core.ι]; simp [hb]⟩

/-- Every outer horn `Λ[n + 2, Fin.last (n + 2)]` in the core of a quasicategory can be filled. -/
theorem core.hornFilling_last [Quasicategory C] {n : ℕ}
    (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet) ⟶ C.core) :
    ∃ σ : Δ[n + 2] ⟶ C.core, σ₀ = Λ[n + 2, Fin.last (n + 2)].ι ≫ σ := by
  rw [horn.exists_extension_last_iff_op]
  obtain ⟨τ, hτ⟩ := core.hornFilling_zero
    ((horn.opIsoLast (n + 2)).inv ≫ opFunctor.map σ₀ ≫ (core.opIso C).hom)
  exact ⟨τ ≫ (core.opIso C).inv, by
    rw [← Category.assoc Λ[n + 2, 0].ι τ, ← hτ, Category.assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]⟩

/-- **The core of a quasicategory is a Kan complex** (HTT Proposition 1.2.5.3). -/
instance core.kanComplex [Quasicategory C] : KanComplex (C.core : SSet) :=
  kanComplex_of_outerHornFilling _ (fun _ ↦ core.hornFilling_zero) (fun _ ↦ core.hornFilling_last)

/-- The core of a quasicategory `C` is the greatest subcomplex of `C` that is a Kan complex. -/
theorem isGreatest_core (C : SSet.{u}) [Quasicategory C] :
    IsGreatest {A : C.Subcomplex | KanComplex (A : SSet)} C.core :=
  ⟨core.kanComplex, fun A (_ : KanComplex (A : SSet)) ↦ le_core_of_kanComplex A⟩

end Core

end SSet

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.Slice
public import TauCeti.AlgebraicTopology.SimplicialSet.Horn

/-!
# Joyal's theorem on special outer horns and the Kan core of a quasicategory

In a quasicategory `C`, the outer horns `Λ[n + 2, 0]` and `Λ[n + 2, n + 2]` cannot be filled in
general, but `Λ[n + 2, 0]` can be filled when its initial edge, from `0` to `1`, is an
equivalence, and `Λ[n + 2, n + 2]` can be filled when its final edge, from `n + 1` to `n + 2`, is
an equivalence. Conversely, an edge all of whose outer horns `Λ[n + 2, 0]` (or all of whose outer
horns `Λ[n + 2, n + 2]`) can be filled is an equivalence (HTT Proposition 1.2.4.3). Consequently, a
quasicategory in which every edge is an equivalence is a Kan complex, and the core `C.core` of a
quasicategory is a Kan complex — the largest Kan subcomplex of `C` (HTT Proposition 1.2.5.3).

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
inverse of `e` and shows that it is also a left inverse. Passing to the opposite quasicategory
`Cᵒᵖ` via `SSet.horn.opHomEquiv` gives the dual statements for `Λ[n + 2, n + 2]`.

## Main results

* `SSet.Quasicategory.hornFilling_zero`, `SSet.Quasicategory.hornFilling_last`: **Joyal's
  theorem**, a horn `Λ[n + 2, 0]` (resp. `Λ[n + 2, n + 2]`) in a quasicategory whose initial
  (resp. final) edge is an equivalence can be filled.
* `SSet.Edge.isEquivalence_iff_hornFilling_zero`,
  `SSet.Edge.isEquivalence_iff_hornFilling_last`: an edge of a quasicategory is an equivalence
  exactly when every horn `Λ[n + 2, 0]` (resp. `Λ[n + 2, n + 2]`) with that initial (resp. final)
  edge can be filled.
* `SSet.Quasicategory.kanComplex_of_forall_isEquivalence`,
  `SSet.kanComplex_iff_quasicategory_and_forall_isEquivalence`: a simplicial set is a Kan complex
  if and only if it is a quasicategory in which every edge is an equivalence.
* `SSet.core.kanComplex`, `SSet.isGreatest_kanComplex_core`: the core of a quasicategory is a Kan
  complex, and it is the largest Kan subcomplex.

## References

* A. Joyal, *Quasi-categories and Kan complexes*, J. Pure Appl. Algebra 175 (2002), Theorem 1.3
  and Corollary 1.4.
* J. Lurie, *Higher Topos Theory*, Propositions 1.2.4.3 and 1.2.5.3.
* J. Lurie, *Kerodon*, Theorem 4.4.2.6, Corollary 4.4.2.7, Proposition 4.4.2.11,
  Proposition 4.4.2.13 and Example 4.4.1.11.
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
  let τ := (slice.homEquiv sq.lift).1
  have hτ : U.ι ≫ τ = I.hom ≫ σ₀ := hpush.hom_ext
    (by
      rw [Subcomplex.unionJoin.ι₁_ι_assoc, ← slice.homEquiv_comp_coe, sq.fac_left,
        Equiv.apply_symm_apply])
    (by
      have h := congrArg (fun F ↦ (slice.homEquiv F).1) sq.fac_right
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

/-- Under horn reversal `Λ[n + 2, n + 2] ⟶ C` corresponds to `Λ[n + 2, 0] ⟶ Cᵒᵖ`, sending the
initial edge of `Λ[n + 2, 0]` to the opposite of the final edge of `Λ[n + 2, n + 2]`. -/
private lemma opHomEquiv_zero_app_edge {n : ℕ}
    (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet) ⟶ C) :
    (horn.opHomEquiv (n + 2) (0 : Fin (n + 3)) σ₀).app _
      (horn.edge (n + 2) 0 0 1 (Fin.zero_le _) (by simp)) =
      C.opObjEquiv.symm (σ₀.app _ (horn.edge (n + 2) (Fin.last (n + 2))
        (Fin.last (n + 1)).castSucc (Fin.last (n + 2)) (Fin.le_last _) (by simp))) := by
  have hrev₁ : (1 : Fin (n + 3)).rev = (Fin.last (n + 1)).castSucc := by
    ext
    simp
  refine (horn.opHomEquiv_app_edge (i := (0 : Fin (n + 3))) σ₀ 0 1
    (Fin.zero_le _) (by simp) (by simp [hrev₁])).trans
      (congrArg (fun z ↦ C.opObjEquiv.symm (σ₀.app _ z)) ?_)
  apply Subtype.ext
  ext k
  fin_cases k <;> simp [hrev₁]

/-- **Joyal's theorem on special final horns** (HTT Proposition 1.2.4.3): in a quasicategory, a
horn `Λ[n + 2, n + 2]` whose final edge, from `n + 1` to `n + 2`, is an equivalence can be
filled. -/
theorem hornFilling_last [Quasicategory C] {n : ℕ}
    (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet) ⟶ C)
    (h : (Edge.mk' (σ₀.app _ (horn.edge (n + 2) (Fin.last (n + 2))
      (Fin.last (n + 1)).castSucc (Fin.last (n + 2)) (Fin.le_last _) (by simp)))).IsEquivalence) :
    ∃ σ : Δ[n + 2] ⟶ C, σ₀ = Λ[n + 2, Fin.last (n + 2)].ι ≫ σ :=
  (horn.exists_extension_opHomEquiv_iff (i := (0 : Fin (n + 3))) σ₀).1
    (hornFilling_zero _ (by rwa [opHomEquiv_zero_app_edge, isEquivalence_mk'_opObjEquiv_symm_iff]))

/-- **Joyal's Kan-complex criterion** (Joyal Corollary 1.4, HTT Proposition 1.2.4.3): a
quasicategory in which every edge is an equivalence is a Kan complex. -/
theorem kanComplex_of_forall_isEquivalence [Quasicategory C]
    (h : ∀ s : C _⦋1⦌, (Edge.mk' s).IsEquivalence) : KanComplex C := by
  rw [KanComplex.iff]
  intro n i f hf
  obtain _ | m := n
  · -- A horn `Λ[1, i]` is a single vertex, filled by precomposing with `stdSimplex.σ 0`.
    refine ⟨stdSimplex.σ 0 ≫ f i.rev (by fin_cases i <;> decide), fun j hj ↦ ?_⟩
    fin_cases i <;> fin_cases j
    · exact absurd rfl hj
    · exact CosimplicialObject.δ_comp_σ_succ_assoc (X := stdSimplex) (i := (0 : Fin 1)) _
    · exact CosimplicialObject.δ_comp_σ_self_assoc (X := stdSimplex) (i := (0 : Fin 1)) _
    · exact absurd rfl hj
  · have hex : ∃ σ : Δ[m + 2] ⟶ C, hf.desc = Λ[m + 2, i].ι ≫ σ := by
      by_cases hi0 : i = 0
      · subst hi0
        exact hornFilling_zero hf.desc (h _)
      · by_cases hil : i = Fin.last (m + 2)
        · subst hil
          exact hornFilling_last hf.desc (h _)
        · exact hornFilling (Fin.pos_iff_ne_zero.2 hi0) (lt_of_le_of_ne (Fin.le_last i) hil) hf.desc
    obtain ⟨σ, hσ⟩ := hex
    exact ⟨σ, fun j hj ↦ by rw [← horn.ι_ι_assoc i j hj, ← hσ, hf.ι_desc]⟩

/-- A quasicategory is a Kan complex if and only if its core is everything. -/
theorem kanComplex_iff_core_eq_top [Quasicategory C] : KanComplex C ↔ C.core = ⊤ :=
  ⟨fun _ ↦ core_eq_top, fun h ↦ kanComplex_of_forall_isEquivalence (core_eq_top_iff.1 h)⟩

end Quasicategory

/-- A simplicial set is a Kan complex if and only if it is a quasicategory in which every edge is
an equivalence. -/
theorem kanComplex_iff_quasicategory_and_forall_isEquivalence {C : SSet.{u}} :
    KanComplex C ↔ Quasicategory C ∧ ∀ s : C _⦋1⦌, (Edge.mk' s).IsEquivalence :=
  ⟨fun _ ↦ ⟨inferInstance, fun _ ↦ isEquivalence_of_kanComplex _⟩,
    fun ⟨_, h⟩ ↦ have := ‹Quasicategory C›; Quasicategory.kanComplex_of_forall_isEquivalence h⟩

/-- The core of a quasicategory is a Kan complex (HTT Proposition 1.2.5.3). -/
instance core.kanComplex {C : SSet.{u}} [Quasicategory C] : KanComplex (C.core : SSet) :=
  Quasicategory.kanComplex_of_forall_isEquivalence fun _ ↦ core.isEquivalence _

/-- The core of a quasicategory `C` is the largest Kan subcomplex of `C`
(HTT Proposition 1.2.5.3). -/
theorem isGreatest_kanComplex_core {C : SSet.{u}} [Quasicategory C] :
    IsGreatest {A : C.Subcomplex | KanComplex (A : SSet)} C.core :=
  ⟨core.kanComplex, fun A hA ↦ have : KanComplex (A : SSet) := hA; le_core_of_kanComplex A⟩

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

/-- **Joyal's characterization of equivalences by special final horns** (HTT Proposition
1.2.4.3): an edge `e` of a quasicategory is an equivalence exactly when every horn
`Λ[n + 2, n + 2]` whose final edge is `e` can be filled. -/
theorem isEquivalence_iff_hornFilling_last [Quasicategory C] (e : Edge x y) :
    e.IsEquivalence ↔ ∀ (n : ℕ) (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet) ⟶ C),
      σ₀.app _ (horn.edge (n + 2) (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc
        (Fin.last (n + 2)) (Fin.le_last _) (by simp)) = e.edge →
        ∃ σ : Δ[n + 2] ⟶ C, σ₀ = Λ[n + 2, Fin.last (n + 2)].ι ≫ σ := by
  refine ⟨fun he n σ₀ h ↦ Quasicategory.hornFilling_last σ₀
    ((isEquivalence_iff_of_edge_eq (e := mk' _) (e' := e) h).2 he), fun H ↦ ?_⟩
  rw [← isEquivalence_opEquiv_iff, isEquivalence_iff_hornFilling_zero]
  intro n τ₀ hτ₀
  obtain ⟨σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet) ⟶ C, rfl⟩ :=
    (horn.opHomEquiv (n + 2) (0 : Fin (n + 3))).surjective τ₀
  rw [Quasicategory.opHomEquiv_zero_app_edge, opEquiv_edge, Equiv.apply_eq_iff_eq] at hτ₀
  exact (horn.exists_extension_opHomEquiv_iff (i := (0 : Fin (n + 3))) σ₀).2 (H n σ₀ hτ₀)

end Edge

end SSet

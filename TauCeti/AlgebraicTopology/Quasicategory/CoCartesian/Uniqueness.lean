/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.CoCartesian.HornFilling
public import TauCeti.AlgebraicTopology.Quasicategory.PointwiseEquivalence
public import TauCeti.AlgebraicTopology.SimplicialSet.Vertex

/-!
# Uniqueness of coCartesian lifts and of coCartesian transports

Let `p : X ⟶ S` be a map of simplicial sets. An edge `f : x ⟶ y` of `X` is `p`-coCartesian when
the map of coslices `X_{f/} ⟶ X_{x/} ×_{S_{p x/}} S_{p f/}` is a trivial fibration. Through the
pushout-join description of outer horns, this says that horns `Λ[n + 2, 0] ⟶ X` whose initial
edge is `f` can be filled over every `(n + 2)`-simplex of `S` (HTT Remark 2.4.1.4,
`SSet.Edge.IsCoCartesian.exists_lift_horn_zero`). This file deduces that coCartesian lifts of an
edge, and the functors of fibers associated to an edge, are unique up to equivalence.

* Two coCartesian edges `f : x ⟶ y` and `f' : x ⟶ y'` over the same edge `e : s ⟶ t` of `S` are
  joined by an equivalence `y ⟶ y'` of the fiber `X_t`. Filling a horn `Λ[2, 0]` factors `f'`
  through `f`, and filling horns `Λ[3, 0]` shows that the factor is invertible.
* For an inner fibration `p`, two coCartesian transports along `e`
  (`SSet.CoCartesianTransport`) are joined by an equivalence of the functor quasicategory
  `Fun(X_s, X_t)`. Their homotopies form a family of horns `Λ[2, 0]` parametrized by `X_s`. Such a
  family is filled by the relative, parametrized form of horn filling along coCartesian edges
  (`SSet.exists_lift_ihomOver_pre_horn_zero`), whose case over a point is the parametrized form
  of Joyal's theorem (`SSet.Quasicategory.exists_lift_pre_horn_zero`). The components of the
  resulting natural transformation are equivalences by the first point.

In particular the functors of fibers associated to the inert projections, through which the Segal
condition `SSet.IsSegal` is stated, are unique up to equivalence.

## Main results

* `SSet.Edge.IsCoCartesian.isEquivalence_of_compStruct`: if two coCartesian edges `f` and `f'`
  with the same source are related by a `2`-simplex `f' = f ≫ g` lying over a degenerate
  `2`-simplex, then `g` is an equivalence of the fiber.
* `SSet.Edge.IsCoCartesian.exists_isEquivalence`: **uniqueness of coCartesian lifts**, two
  coCartesian edges with the same source over the same edge are joined by an equivalence of the
  fiber.
* `SSet.CoCartesianTransport.exists_isEquivalence`: **uniqueness of coCartesian transports**, two
  coCartesian transports along an edge are equivalent in the functor quasicategory of the fibers.

## References

* J. Lurie, *Higher Topos Theory*, §2.4.1, Remark 2.4.1.4 and Propositions 2.4.1.5 and 2.4.1.7
  (in the dual form of Remark 2.4.1.9), and §2.4.2 for the functors associated to an edge.
* J. Lurie, *Kerodon*, proof of Theorem 4.4.4.4 (the parametrized horn filling).
* S. Moss, *Another approach to the Kan-Quillen model structure*, J. Homotopy Relat. Struct. 15
  (2020).
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed Simplicial

universe u

namespace SSet

namespace Edge

variable {X S : SSet.{u}} {x y : X _⦋0⦌}

variable {p : X ⟶ S}

/-- A `p`-coCartesian edge `f : x ⟶ y` factors every edge `f' : x ⟶ y'` lying over the same edge
`e` of `S`: there are an edge `g : y ⟶ y'` and a `2`-simplex of `X` exhibiting `f'` as a composite
of `f` and `g`, lying over the degenerate `2`-simplex `s₁ e` of `S`. In particular `g` lies over
the identity of the target of `e`. -/
lemma IsCoCartesian.exists_compStruct {f : Edge x y} (hf : f.IsCoCartesian p) {y' : X _⦋0⦌}
    (f' : Edge x y') (h : p.app _ f'.edge = p.app _ f.edge) :
    ∃ (g : Edge y y') (c : CompStruct f g f'), p.app _ c.simplex = S.σ 1 (p.app _ f.edge) := by
  -- Fill the horn `Λ[2, 0]` with faces `f` (from `0` to `1`) and `f'` (from `0` to `2`).
  let F : ∀ j : Fin 3, j ≠ 0 → (Δ[1] ⟶ X) := fun j _ ↦
    ![yonedaEquiv.symm f.edge, yonedaEquiv.symm f'.edge, yonedaEquiv.symm f.edge] j
  have hF : horn.IsCompatible F := by
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k <;> simp at hj hk hjk ⊢
    simp [F, stdSimplex.δ_comp_yonedaEquiv_symm]
  -- The faces `1` and `2` of the degenerate `2`-simplex `s₁ e` are `e`.
  have h₁ : S.δ 1 (S.σ 1 (p.app _ f.edge)) = p.app _ f.edge := δ_comp_σ_self_apply (1 : Fin 2) _
  have h₂ : S.δ 2 (S.σ 1 (p.app _ f.edge)) = p.app _ f.edge := δ_comp_σ_succ_apply (1 : Fin 2) _
  obtain ⟨σ, hσ, hσp⟩ := hf.exists_lift_horn_zero hF.desc (by
      rw [horn.edge_two_zero_eq_ι_app, hF.desc_app_ι_app, ← yonedaEquiv_comp, Category.id_comp]
      exact yonedaEquiv.apply_symm_apply _)
    (yonedaEquiv.symm (S.σ 1 (p.app _ f.edge))) (horn.hom_ext' fun j hj ↦ by
      rw [hF.ι_desc_assoc, horn.ι_ι_assoc, stdSimplex.δ_comp_yonedaEquiv_symm]
      fin_cases j
      · exact absurd rfl hj
      · simp [F, yonedaEquiv_symm_comp, h, h₁]
      · simp [F, yonedaEquiv_symm_comp, h₂])
  have hw₁ : X.δ 1 (yonedaEquiv σ) = f'.edge := by
    simpa [F] using hF.δ_yonedaEquiv_of_desc_eq hσ.symm 1 (by decide)
  have hw₂ : X.δ 2 (yonedaEquiv σ) = f.edge := by
    simpa [F] using hF.δ_yonedaEquiv_of_desc_eq hσ.symm 2 (by decide)
  have hsrc : X.δ 1 (X.δ 0 (yonedaEquiv σ)) = y := by
    rw [← f.tgt_eq, ← hw₂]
    exact (δ_comp_δ_apply (i := 0) (j := 1) (by decide) _).symm
  have htgt : X.δ 0 (X.δ 0 (yonedaEquiv σ)) = y' := by
    rw [← f'.tgt_eq, ← hw₁]
    exact δ_comp_δ_self_apply (i := 0) _
  refine ⟨.mk _ hsrc htgt, .mk _ hw₂ rfl hw₁, ?_⟩
  -- The `2`-simplex of the structure just built is `yonedaEquiv σ`, by definition of
  -- `CompStruct.mk` (here `simp only [CompStruct.mk_simplex]` makes no progress).
  change p.app _ (yonedaEquiv σ) = _
  rw [← yonedaEquiv_comp, hσp, Equiv.apply_symm_apply]

/-- The face `0` of the degenerate `3`-simplex `s₁ s₁ e` on an edge `e` is the degenerate
`2`-simplex on the target of `e`. -/
private lemma δ_zero_σ_one_σ_one (e : S _⦋1⦌) :
    S.δ 0 (S.σ 1 (S.σ 1 e)) = S.σ 0 (S.σ 0 (S.δ 0 e)) :=
  (δ_comp_σ_of_le_apply (i := (0 : Fin 3)) (j := 0) (Fin.zero_le _) _).trans
    (congrArg _ (δ_comp_σ_of_le_apply (i := (0 : Fin 2)) (j := 0) (Fin.zero_le _) _))

/-- Let `f : x ⟶ y` be `p`-coCartesian, and let `c` and `c'` be `2`-simplices exhibiting
`f' = f ≫ g` and `f = f' ≫ g'`, both lying over the degenerate `2`-simplex `s₁ e` on the image
`e` of `f`. Then `g ≫ g' = id y`, through a `2`-simplex lying over the degenerate `2`-simplex on
the image of `y`. -/
lemma IsCoCartesian.exists_compStruct_id {f : Edge x y} (hf : f.IsCoCartesian p) {y' : X _⦋0⦌}
    {f' : Edge x y'} {g : Edge y y'} {g' : Edge y' y} (c : CompStruct f g f')
    (c' : CompStruct f' g' f) (hc : p.app _ c.simplex = S.σ 1 (p.app _ f.edge))
    (hc' : p.app _ c'.simplex = S.σ 1 (p.app _ f.edge)) :
    ∃ d : CompStruct g g' (id y), p.app _ d.simplex = S.σ 0 (S.σ 0 (p.app _ y)) := by
  -- Fill the horn `Λ[3, 0]` with faces `c'` (on `0, 2, 3`), `f ≫ id y = f` (on `0, 1, 3`) and
  -- `c` (on `0, 1, 2`); its remaining face exhibits `g ≫ g' = id y`.
  let F : ∀ j : Fin 4, j ≠ 0 → (Δ[2] ⟶ X) := fun j _ ↦
    ![yonedaEquiv.symm c.simplex, yonedaEquiv.symm c'.simplex,
      yonedaEquiv.symm (CompStruct.compId f).simplex, yonedaEquiv.symm c.simplex] j
  have hF : horn.IsCompatible F := by
    have h₂ : Fin.castPred (2 : Fin 4) (by decide) = 2 := rfl
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k <;> simp at hj hk hjk ⊢ <;>
      simp [F, h₂, stdSimplex.δ_comp_yonedaEquiv_symm, -CompStruct.compId_simplex]
  -- The faces `1`, `2` and `3` of the degenerate `3`-simplex `s₁ s₁ e` on `e = p f` are `s₁ e`.
  have h₁ : S.δ 1 (S.σ 1 (S.σ 1 (p.app _ f.edge))) = S.σ 1 (p.app _ f.edge) :=
    δ_comp_σ_self_apply (1 : Fin 3) _
  have h₂ : S.δ 2 (S.σ 1 (S.σ 1 (p.app _ f.edge))) = S.σ 1 (p.app _ f.edge) :=
    δ_comp_σ_succ_apply (1 : Fin 3) _
  have h₃ : S.δ 3 (S.σ 1 (S.σ 1 (p.app _ f.edge))) = S.σ 1 (p.app _ f.edge) :=
    (δ_comp_σ_of_gt'_apply (i := (3 : Fin 4)) (j := (1 : Fin 3)) (by decide) _).trans
      (congrArg (S.σ 1) (δ_comp_σ_succ_apply (1 : Fin 2) _))
  obtain ⟨σ, hσ, hσp⟩ := hf.exists_lift_horn_zero hF.desc (by
      rw [horn.edge_three_zero_eq_ι_app, hF.desc_app_ι_app, ← yonedaEquiv_comp]
      simp [F, stdSimplex.δ_comp_yonedaEquiv_symm, c.d₂])
    (yonedaEquiv.symm (S.σ 1 (S.σ 1 (p.app _ f.edge)))) (horn.hom_ext' fun j hj ↦ by
      rw [hF.ι_desc_assoc, horn.ι_ι_assoc, stdSimplex.δ_comp_yonedaEquiv_symm]
      fin_cases j
      · exact absurd rfl hj
      · simp [F, yonedaEquiv_symm_comp, hc', h₁]
      · simp [F, yonedaEquiv_symm_comp, σ_naturality_apply, h₂]
      · simp [F, yonedaEquiv_symm_comp, hc, h₃])
  have hw₁ : X.δ 1 (yonedaEquiv σ) = c'.simplex := by
    simpa [F] using hF.δ_yonedaEquiv_of_desc_eq hσ.symm 1 (by decide)
  have hw₂ : X.δ 2 (yonedaEquiv σ) = (CompStruct.compId f).simplex := by
    simpa [F, -CompStruct.compId_simplex] using hF.δ_yonedaEquiv_of_desc_eq hσ.symm 2 (by decide)
  have hw₃ : X.δ 3 (yonedaEquiv σ) = c.simplex := by
    simpa [F] using hF.δ_yonedaEquiv_of_desc_eq hσ.symm 3 (by decide)
  have h₂ : X.δ 2 (X.δ 0 (yonedaEquiv σ)) = g.edge := by
    rw [← c.d₀, ← hw₃]
    exact (δ_comp_δ_apply (i := 0) (j := 2) (by decide) _).symm
  have h₀ : X.δ 0 (X.δ 0 (yonedaEquiv σ)) = g'.edge := by
    rw [← c'.d₀, ← hw₁]
    exact δ_comp_δ_self_apply (i := 0) _
  have h₁ : X.δ 1 (X.δ 0 (yonedaEquiv σ)) = (id y).edge := by
    rw [← (CompStruct.compId f).d₀, ← hw₂]
    exact (δ_comp_δ_apply (i := 0) (j := 1) (by decide) _).symm
  refine ⟨.mk _ h₂ h₀ h₁, ?_⟩
  -- The `2`-simplex of the structure just built is `X.δ 0 (yonedaEquiv σ)`, by definition of
  -- `CompStruct.mk`.
  change p.app _ (X.δ 0 (yonedaEquiv σ)) = _
  rw [δ_naturality_apply, ← yonedaEquiv_comp, hσp, Equiv.apply_symm_apply]
  rw [δ_zero_σ_one_σ_one, ← δ_naturality_apply, f.tgt_eq]

/-- The edge `g` of a `2`-simplex `c` of `X` over the degenerate `2`-simplex `s₁ e`, from the
vertex `1` to the vertex `2`, lies in the fiber over the target `t` of `e`. -/
private lemma δ_zero_mem_fiber {t : S _⦋0⦌} {e : S _⦋1⦌} (he : S.δ 0 e = t) (z : X _⦋2⦌)
    (hz : p.app _ z = S.σ 1 e) : X.δ 0 z ∈ (fiber p t).obj _ :=
  mem_fiber_of_app_eq_map _ _ _ (SimplexCategory.σ 0) (by
    rw [δ_naturality_apply, hz, ← he]
    exact δ_comp_σ_of_le_apply (i := (0 : Fin 2)) (j := 0) (Fin.zero_le _) _)

/-- **CoCartesian lifts are unique up to equivalence: comparison.** Let `f : x ⟶ y` and
`f' : x ⟶ y'` be `p`-coCartesian edges with targets `y` and `y'` in the fiber of `p` over a vertex
`t` of `S`, and let `c` be a `2`-simplex of `X` exhibiting `f'` as a composite of `f` and an edge
`g : y ⟶ y'` of the fiber, lying over the degenerate `2`-simplex `s₁ e` on the image `e` of `f`.
Then `g` is an equivalence of the fiber (dual of HTT Propositions 2.4.1.5 and 2.4.1.7: `g` is
coCartesian, and a coCartesian edge over an identity is an equivalence). -/
theorem IsCoCartesian.isEquivalence_of_compStruct {t : S _⦋0⦌} {y y' : (fiber p t : SSet) _⦋0⦌}
    {f : Edge x y.val} {f' : Edge x y'.val} (hf : f.IsCoCartesian p) (hf' : f'.IsCoCartesian p)
    {g : Edge y y'} (c : CompStruct f (g.map (fiber p t).ι) f')
    (hc : p.app _ c.simplex = S.σ 1 (p.app _ f.edge)) : g.IsEquivalence := by
  -- An inverse `g' : y' ⟶ y` comes from factoring `f` through the coCartesian edge `f'`, and the
  -- two composites are identities by filling horns `Λ[3, 0]` along `f` and along `f'`.
  have h : p.app _ f'.edge = p.app _ f.edge :=
    ((congrArg (p.app _) c.d₁).symm.trans (δ_naturality_apply _ _ _)).trans
      ((congrArg (S.δ 1) hc).trans (δ_comp_σ_self_apply (1 : Fin 2) _))
  have he : S.δ 0 (p.app _ f.edge) = t := by
    rw [← δ_naturality_apply, f.tgt_eq, fiber.app_coe_obj₀]
  -- An inverse `g'`, and the `2`-simplices `d` and `d'` exhibiting `g ≫ g' = id y` and
  -- `g' ≫ g = id y'`, which lie over the degenerate `2`-simplex on `t`.
  obtain ⟨g', c', hc'⟩ := hf'.exists_compStruct f h.symm
  rw [h] at hc'
  obtain ⟨d, hd⟩ := hf.exists_compStruct_id c c' hc hc'
  obtain ⟨d', hd'⟩ := hf'.exists_compStruct_id c' c (hc'.trans (congrArg _ h.symm))
    (hc.trans (congrArg _ h.symm))
  have hσσ (z : X _⦋2⦌) (hz : p.app _ z = S.σ 0 (S.σ 0 t)) : z ∈ (fiber p t).obj _ :=
    mem_fiber_of_app_eq_map _ _ z (SimplexCategory.σ 0 ≫ SimplexCategory.σ 0) (by
      rw [hz, op_comp, Functor.map_comp_apply]
      -- `S.σ 0` is `S.map (SimplexCategory.σ 0).op` by definition.
      rfl)
  have hd₀ : d.simplex ∈ (fiber p t).obj _ := hσσ _ (by rw [hd, fiber.app_coe_obj₀])
  have hd₀' : d'.simplex ∈ (fiber p t).obj _ := hσσ _ (by rw [hd', fiber.app_coe_obj₀])
  have hg' : g'.edge ∈ (fiber p t).obj _ := by
    rw [← c'.d₀]
    exact δ_zero_mem_fiber he _ hc'
  exact InvStruct.isEquivalence
    { inv := g'.toSubcomplex (fiber p t) hg'
      homInvId := CompStruct.mk ⟨d.simplex, hd₀⟩ (Subtype.ext d.d₂) (Subtype.ext d.d₀)
        (Subtype.ext d.d₁)
      invHomId := CompStruct.mk ⟨d'.simplex, hd₀'⟩ (Subtype.ext d'.d₂) (Subtype.ext d'.d₀)
        (Subtype.ext d'.d₁) }

/-- **CoCartesian lifts are unique up to equivalence** (HTT §2.4.1). Two `p`-coCartesian edges
`f : x ⟶ y` and `f' : x ⟶ y'` with the same source, lying over the same edge `e` of `S`, are
joined by an equivalence `g : y ⟶ y'` of the fiber of `p` over the target `t` of `e`, together
with a `2`-simplex of `X` over the degenerate `2`-simplex `s₁ e` exhibiting `f'` as a composite of
`f` and `g`. -/
theorem IsCoCartesian.exists_isEquivalence {t : S _⦋0⦌} {y y' : (fiber p t : SSet) _⦋0⦌}
    {f : Edge x y.val} {f' : Edge x y'.val} (hf : f.IsCoCartesian p) (hf' : f'.IsCoCartesian p)
    (h : p.app _ f'.edge = p.app _ f.edge) :
    ∃ g : Edge y y', g.IsEquivalence ∧
      ∃ c : CompStruct f (g.map (fiber p t).ι) f', p.app _ c.simplex = S.σ 1 (p.app _ f.edge) := by
  obtain ⟨g, c, hc⟩ := hf.exists_compStruct f' h
  have he : S.δ 0 (p.app _ f.edge) = t := by
    rw [← δ_naturality_apply, f.tgt_eq, fiber.app_coe_obj₀]
  have hg : g.edge ∈ (fiber p t).obj _ := by
    rw [← c.d₀]
    exact δ_zero_mem_fiber he _ hc
  exact ⟨g.toSubcomplex (fiber p t) hg, hf.isEquivalence_of_compStruct hf' c hc, c, hc⟩

end Edge

namespace CoCartesianTransport

variable {X S : SSet.{u}} {p : X ⟶ S} {s t : S _⦋0⦌} {e : Edge s t}

/-- The homotopies of two transports along `e` are the faces `2` and `1` of a family
`X_s ⊗ Δ[2] ⟶ X` of `2`-simplices over the degenerate `2`-simplex `s₁ e`. -/
private lemma exists_lift_homotopies [InnerFibration p] (T T' : CoCartesianTransport p e) :
    ∃ l : (fiber p s : SSet) ⊗ Δ[2] ⟶ X, (fiber p s : SSet) ◁ stdSimplex.δ 2 ≫ l = T.homotopy ∧
      (fiber p s : SSet) ◁ stdSimplex.δ 1 ≫ l = T'.homotopy ∧
      l ≫ p = snd _ _ ≫ yonedaEquiv.symm (S.σ 1 e.edge) := by
  -- The family of horns `Λ[2, 0]` with faces the two homotopies, over `s₁ e`.
  let σ : (Λ[2, 0] : SSet) ⟶ (ihom (fiber p s : SSet)).obj X :=
    horn₂₀.isPushout.desc (curry T.homotopy) (curry T'.homotopy) (by
      rw [← curry_natural_left, ← curry_natural_left, whiskerLeft_δ_one_homotopy,
        whiskerLeft_δ_one_homotopy])
  have hσ₀₁ : horn₂₀.ι₀₁ ≫ σ = curry T.homotopy := horn₂₀.isPushout.inl_desc _ _ _
  have hσ₀₂ : horn₂₀.ι₀₂ ≫ σ = curry T'.homotopy := horn₂₀.isPushout.inr_desc _ _ _
  have hσp : σ ≫ (ihom (fiber p s : SSet)).map p =
      curry (snd _ _ ≫ Λ[2, 0].ι ≫ yonedaEquiv.symm (S.σ 1 e.edge)) := by
    refine horn₂₀.isPushout.hom_ext ?_ ?_
    · rw [reassoc_of% hσ₀₁, ← curry_natural_right, ← curry_natural_left, homotopy_comp,
        whiskerLeft_snd_assoc, horn.ι_ι_assoc, stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg (fun φ ↦ curry (snd _ _ ≫ yonedaEquiv.symm φ))
        (δ_comp_σ_succ_apply (1 : Fin 2) _).symm
    · rw [reassoc_of% hσ₀₂, ← curry_natural_right, ← curry_natural_left, homotopy_comp,
        whiskerLeft_snd_assoc, horn.ι_ι_assoc, stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg (fun φ ↦ curry (snd _ _ ≫ yonedaEquiv.symm φ))
        (δ_comp_σ_self_apply (1 : Fin 2) _).symm
  have hface₀₁ : (fiber p s : SSet) ◁ horn₂₀.ι₀₁ ≫ uncurry σ = T.homotopy := by
    rw [← uncurry_natural_left, hσ₀₁, uncurry_curry]
  have hface₀₂ : (fiber p s : SSet) ◁ horn₂₀.ι₀₂ ≫ uncurry σ = T'.homotopy := by
    rw [← uncurry_natural_left, hσ₀₂, uncurry_curry]
  -- Its initial edges are the coCartesian edges of `T`.
  obtain ⟨l, hl, hlp⟩ := exists_lift_tensor_horn_zero p _ (uncurry σ)
    (by rw [← uncurry_natural_right, hσp, uncurry_curry]) fun z ↦ by
      refine (T.isCoCartesian z).of_edge_eq ?_
      rw [Edge.mk'_edge, Edge.mk'_edge, horn.edge_two_zero_eq_ι_app,
        ← Category.id_comp (lift (const z) (𝟙 Δ[1])), Category.assoc, yonedaEquiv_comp]
      -- Both sides are `T.homotopy` applied to the `1`-simplex `(s₀ z, 𝟙)` of `X_s ⊗ Δ[1]`.
      change T.homotopy.app _ ((lift (const z) (𝟙 Δ[1])).app _ _) =
        ((fiber p s : SSet) ◁ horn₂₀.ι₀₁ ≫ uncurry σ).app _
          ((fiber p s : SSet).σ 0 z, yonedaEquiv (𝟙 Δ[1]))
      rw [hface₀₁]
      exact congrArg (T.homotopy.app _) (Prod.ext (const_app_one (W := Δ[1]) z _) rfl)
  refine ⟨l, ?_, ?_, hlp⟩
  · rw [← horn.ι_ι (0 : Fin 3) 2 (by decide), MonoidalCategory.whiskerLeft_comp_assoc, hl,
      hface₀₁]
  · rw [← horn.ι_ι (0 : Fin 3) 1 (by decide), MonoidalCategory.whiskerLeft_comp_assoc, hl,
      hface₀₂]

/-- The components of the face opposite to `0` of a family `l` as in `exists_lift_homotopies`
are equivalences of `X_t`, by uniqueness of coCartesian lifts. -/
private lemma isEquivalence_of_lift (T T' : CoCartesianTransport p e)
    {l : (fiber p s : SSet) ⊗ Δ[2] ⟶ X} (hl₂ : (fiber p s : SSet) ◁ stdSimplex.δ 2 ≫ l = T.homotopy)
    (hl₁ : (fiber p s : SSet) ◁ stdSimplex.δ 1 ≫ l = T'.homotopy)
    (hlp : l ≫ p = snd _ _ ≫ yonedaEquiv.symm (S.σ 1 e.edge)) (x : (fiber p s : SSet) _⦋0⦌)
    {g : Edge (T.functor.app _ x) (T'.functor.app _ x)}
    (hg : (g.map (fiber p t).ι).edge =
      yonedaEquiv (lift (const x) (𝟙 Δ[1]) ≫ (fiber p s : SSet) ◁ stdSimplex.δ 0 ≫ l)) :
    g.IsEquivalence := by
  have hlc {n m : ℕ} (v : Δ[m] ⟶ Δ[n]) :
      v ≫ lift (const x) (𝟙 Δ[n]) = lift (const x) (𝟙 Δ[m]) ≫ (fiber p s : SSet) ◁ v := by
    rw [comp_lift, comp_const, Category.comp_id, lift_whiskerLeft, Category.id_comp]
  -- The coCartesian edges of `T` and `T'` at `x`, with their endpoints in the fibers.
  have hsrc (U : CoCartesianTransport p e) :
      X.δ 1 (yonedaEquiv (lift (const x) (𝟙 Δ[1]) ≫ U.homotopy)) = x.val := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, hlc, Category.assoc,
      whiskerLeft_δ_one_homotopy, lift_fst_assoc, const_comp, yonedaEquiv_const]
    -- The inclusion `(fiber p s).ι` sends `x` to its underlying vertex, by definition.
    rfl
  have htgt (U : CoCartesianTransport p e) :
      X.δ 0 (yonedaEquiv (lift (const x) (𝟙 Δ[1]) ≫ U.homotopy)) = (U.functor.app _ x).val := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, hlc, Category.assoc,
      whiskerLeft_δ_zero_homotopy, lift_fst_assoc, ← Category.assoc, const_comp, const_comp,
      yonedaEquiv_const]
    -- The inclusion `(fiber p t).ι` sends a vertex to its underlying vertex, by definition.
    rfl
  let F : Edge x.val (T.functor.app _ x).val := Edge.mk _ (hsrc T) (htgt T)
  let F' : Edge x.val (T'.functor.app _ x).val := Edge.mk _ (hsrc T') (htgt T')
  -- The `2`-simplex of `l` at `x` exhibits `F'` as a composite of `F` and `g`.
  have hc₂ : X.δ 2 (yonedaEquiv (lift (const x) (𝟙 Δ[2]) ≫ l)) = F.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, hlc, Category.assoc, hl₂]
    -- `F.edge` is this simplex, by definition of `Edge.mk`.
    rfl
  have hc₁ : X.δ 1 (yonedaEquiv (lift (const x) (𝟙 Δ[2]) ≫ l)) = F'.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, hlc, Category.assoc, hl₁]
    -- `F'.edge` is this simplex, by definition of `Edge.mk`.
    rfl
  have hc₀ : X.δ 0 (yonedaEquiv (lift (const x) (𝟙 Δ[2]) ≫ l)) = (g.map (fiber p t).ι).edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, hlc, Category.assoc, hg]
  have hc : p.app _ (yonedaEquiv (lift (const x) (𝟙 Δ[2]) ≫ l)) = S.σ 1 (p.app _ F.edge) := by
    -- The edge `F` is by definition the image of `(x, 𝟙)` under the homotopy of `T`.
    change _ = S.σ 1 (p.app _ (yonedaEquiv (lift (const x) (𝟙 Δ[1]) ≫ T.homotopy)))
    rw [← yonedaEquiv_comp, ← yonedaEquiv_comp, Category.assoc, Category.assoc, hlp,
      homotopy_comp, lift_snd_assoc, lift_snd_assoc, Category.id_comp, Category.id_comp,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hF : F.IsCoCartesian p := (T.isCoCartesian x).of_edge_eq rfl
  have hF' : F'.IsCoCartesian p := (T'.isCoCartesian x).of_edge_eq rfl
  exact hF.isEquivalence_of_compStruct hF' (Edge.CompStruct.mk _ hc₂ hc₀ hc₁) hc

/-- **Two coCartesian transports along an edge are equivalent**: the functor of fibers associated
to an edge is unique up to equivalence (HTT §2.4.2). Let `p : X ⟶ S` be an inner
fibration and `e : s ⟶ t` an edge of `S`. For two coCartesian transports `T` and `T'` along `e`,
there is an equivalence `T.functor ⟶ T'.functor` of the functor quasicategory
`Fun(X_s, X_t)` of the fibers. -/
theorem exists_isEquivalence [InnerFibration p] (T T' : CoCartesianTransport p e) :
    ∃ α : Edge ((ihomObj₀Equiv _ _).symm T.functor) ((ihomObj₀Equiv _ _).symm T'.functor),
      α.IsEquivalence := by
  -- The two homotopies are faces of a family `l` of `2`-simplices over `s₁ e`, whose face
  -- opposite to `0` lies over the degenerate edge on `t`, hence in `X_t`: it is a natural
  -- transformation `g' : T.functor ⟶ T'.functor`.
  obtain ⟨l, hl₂, hl₁, hlp⟩ := exists_lift_homotopies T T'
  have hconst : (yonedaEquiv.symm (S.δ 0 (S.σ 1 e.edge)) : Δ[1] ⟶ S) = const t := by
    rw [Equiv.symm_apply_eq, yonedaEquiv_const_one, Edge.id_edge]
    exact (δ_comp_σ_of_le_apply (i := (0 : Fin 2)) (j := 0) (Fin.zero_le _) _).trans
      (congrArg (S.σ 0) e.tgt_eq)
  have hl₀ : ((fiber p s : SSet) ◁ stdSimplex.δ 0 ≫ l) ≫ p = const t := by
    rw [Category.assoc, hlp, whiskerLeft_snd_assoc, stdSimplex.δ_comp_yonedaEquiv_symm, hconst,
      comp_const]
  let g' := fiber.lift ((fiber p s : SSet) ◁ stdSimplex.δ 0 ≫ l) p t hl₀
  have hg' : g' ≫ (fiber p t).ι = (fiber p s : SSet) ◁ stdSimplex.δ 0 ≫ l :=
    fiber.lift_ι _ _ _ _
  -- The ends of `g'`, at the vertices `1` and `2` of `Δ[2]`, are the functors of `T` and `T'`.
  have hend (U : CoCartesianTransport p e) (j : Fin 3)
      (hj : (fiber p s : SSet) ◁ stdSimplex.δ j ≫ l = U.homotopy) (v : Fin 2)
      (hv : stdSimplex.δ v ≫ stdSimplex.δ 0 = stdSimplex.δ 0 ≫ stdSimplex.δ j) :
      (fiber p s : SSet) ◁ stdSimplex.δ v ≫ g' = fst _ _ ≫ U.functor := by
    rw [← cancel_mono (fiber p t).ι, Category.assoc, hg', ← MonoidalCategory.whiskerLeft_comp_assoc,
      hv, MonoidalCategory.whiskerLeft_comp_assoc, hj, whiskerLeft_δ_zero_homotopy,
      Category.assoc]
  let α : Edge ((ihomObj₀Equiv _ _).symm T.functor) ((ihomObj₀Equiv _ _).symm T'.functor) :=
    Edge.mk (yonedaEquiv (curry g'))
      (yonedaEquiv.symm.injective (by
        rw [yonedaEquiv_symm_δ_yonedaEquiv_curry, yonedaEquiv_symm_ihomObj₀Equiv_symm,
          hend T 2 hl₂ 1 (CosimplicialObject.δ_comp_δ _ (i := 0) (j := 1) (by decide)).symm]))
      (yonedaEquiv.symm.injective (by
        rw [yonedaEquiv_symm_δ_yonedaEquiv_curry, yonedaEquiv_symm_ihomObj₀Equiv_symm,
          hend T' 1 hl₁ 0 (CosimplicialObject.δ_comp_δ _ (i := 0) (j := 0) le_rfl).symm]))
  -- Its components are equivalences, by uniqueness of coCartesian lifts.
  refine ⟨α, (Edge.isEquivalence_iff_forall_isEquivalence_map_evalAt α).2 fun x ↦ ?_⟩
  have hev (φ : (fiber p s : SSet) ⟶ (fiber p t : SSet)) :
      (evalAt x _).app _ ((ihomObj₀Equiv _ _).symm φ) = φ.app _ x := by
    have h := yonedaEquiv_comp (yonedaEquiv.symm ((ihomObj₀Equiv _ _).symm φ)) (evalAt x _)
    rw [Equiv.apply_symm_apply] at h
    rw [← h, yonedaEquiv_symm_ihomObj₀Equiv_symm, curry_evalAt, lift_fst_assoc, const_comp,
      yonedaEquiv_const]
  rw [← Edge.isEquivalence_ofEq_iff (hev T.functor) (hev T'.functor)]
  refine isEquivalence_of_lift T T' hl₂ hl₁ hlp x ?_
  -- The component of `α` at `x` is the evaluation of `curry g'` at `x`.
  change (fiber p t).ι.app _ ((evalAt x _).app _ (yonedaEquiv (curry g'))) = _
  rw [← yonedaEquiv_comp, curry_evalAt, ← yonedaEquiv_comp, Category.assoc, hg']

end CoCartesianTransport

end SSet

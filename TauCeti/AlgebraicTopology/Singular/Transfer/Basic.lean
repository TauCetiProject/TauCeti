/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Lifting
public import TauCeti.Topology.Covering.Quotient
public import TauCeti.AlgebraicTopology.Singular.Basic
public import TauCeti.AlgebraicTopology.TopologicalSimplex

/-!
# The transfer of a finite covering on singular chains

Let `p : E ⟶ B` be a covering map whose fibres are finite.  Topological simplices are simply
connected and locally path connected, so a singular simplex `σ` of `B` lifts uniquely through `p`
once the lift of one point is prescribed: evaluating at any point `x` of the simplex is a
bijection from the lifts of `σ` onto the fibre of `p` over `σ x`.  In particular `σ` has finitely
many lifts, and restricting a lift to a face is a bijection onto the lifts of that face.

The transfer `hp.singularTransfer hfin R : C(B; R) ⟶ C(E; R)` sends a singular simplex to the
sum of its lifts.  Since faces of lifts are exactly the lifts of faces, this is a chain map.
Composing with `p_*` counts the lifts: on a simplex `σ` it is multiplication by the cardinality
of a fibre over a point of `σ`, so `p_* ∘ transfer = d • id` when every fibre has `d` points.
A bijective self-map `f` of `E` over `B`, such as a deck transformation, permutes the lifts of
each simplex, so `f_* ∘ transfer = transfer`. When `p` is the quotient covering of a free action of
a finite group `G`, the lifts of `p ∘ τ` are the translates `g • τ`, so
`transfer ∘ p_* = ∑_{g ∈ G} g_*`.

## Main declarations

* `IsCoveringMap.bijOn_simplexMap_apply`: evaluation at a point of the simplex identifies the
  lifts of a singular simplex with a fibre of `p`.
* `IsCoveringMap.bijOn_toSSet_obj_map`: restricting lifts along a simplicial operator is a
  bijection onto the lifts of the restricted simplex.
* `IsCoveringMap.bijOn_toSSet_map_app_of_comp_eq`: a bijective self-map of `E` over `B` permutes
  the lifts of each singular simplex.
* `IsCoveringMap.singularTransfer`: the transfer chain map `C(B; R) ⟶ C(E; R)`, with
  `IsCoveringMap.ιChainComplex_singularTransfer_f` its value on a singular simplex.
* `IsCoveringMap.singularTransfer_comp_chainComplexMap`: `p_* ∘ transfer = d • id` on singular
  chains for a covering whose fibres all have `d` points, and
  `IsCoveringMap.homologyMap_singularTransfer_comp_homologyMap` the same on singular homology.
* `IsCoveringMap.singularTransfer_comp_chainComplexMap_of_comp_eq`: `f_* ∘ transfer = transfer`
  on singular chains for a bijective self-map `f` of `E` over `B`, and
  `IsCoveringMap.homologyMap_singularTransfer_comp_homologyMap_of_comp_eq` the same on singular
  homology.
* `IsQuotientCoveringMap.chainComplexMap_comp_singularTransfer`: for the quotient covering of a
  finite group `G`, `transfer ∘ p_* = ∑_{g ∈ G} g_*` on singular chains.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.G, for the transfer of a finite covering.
-/

public section

noncomputable section

open CategoryTheory Limits Simplicial TauCeti.TopCat

universe w v u

namespace IsCoveringMap

variable {E B : TopCat.{w}} {p : E ⟶ B}

section Lifts

variable (hp : IsCoveringMap p)
include hp

/-- Evaluation at a point `x` of the topological simplex is a bijection from the lifts of a
singular simplex `σ` of `B` through the covering map `p` onto the fibre of `p` over `σ x`. -/
theorem bijOn_simplexMap_apply {n : SimplexCategoryᵒᵖ} (σ : (TopCat.toSSet.obj B).obj n)
    (x : SimplexCategory.toTop.{w}.obj n.unop) :
    Set.BijOn (fun τ ↦ simplexMap τ x) ((TopCat.toSSet.map p).app n ⁻¹' {σ})
      (p ⁻¹' {simplexMap σ x}) := by
  have lifts {τ : (TopCat.toSSet.obj E).obj n} :
      (TopCat.toSSet.map p).app n τ = σ ↔ ⇑p ∘ ⇑(simplexMap τ) = ⇑(simplexMap σ) := by
    rw [← simplexMap_injective.eq_iff, simplexMap_app, ← DFunLike.coe_fn_eq,
      ContinuousMap.coe_comp]
  refine ⟨fun τ hτ ↦ ?_, fun τ₁ hτ₁ τ₂ hτ₂ h ↦ ?_, fun e he ↦ ?_⟩
  · have := congr_fun (lifts.mp hτ) x
    simpa using this
  · obtain ⟨F, -, hF⟩ := hp.existsUnique_continuousMap_lifts (simplexMap σ) x (simplexMap τ₁ x)
      (congr_fun (lifts.mp hτ₁) x)
    exact simplexMap_injective <|
      (hF _ ⟨rfl, lifts.mp hτ₁⟩).trans (hF _ ⟨h.symm, lifts.mp hτ₂⟩).symm
  · obtain ⟨F, ⟨hFx, hF⟩, -⟩ := hp.existsUnique_continuousMap_lifts (simplexMap σ) x e he
    obtain ⟨τ, rfl⟩ := simplexMap_surjective F
    exact ⟨τ, lifts.mpr hF, hFx⟩

/-- A singular simplex has only finitely many lifts through a covering map with finite
fibres. -/
theorem finite_preimage_singleton_toSSet_map_app (hfin : ∀ b, Finite ↥(p ⁻¹' {b}))
    {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj B).obj n) :
    ((TopCat.toSSet.map p).app n ⁻¹' {σ}).Finite := by
  let x : SimplexCategory.toTop.{w}.obj n.unop := SimplexCategory.toTopInitialVertex _
  have h := hp.bijOn_simplexMap_apply σ x
  have := hfin (simplexMap σ x)
  exact Set.Finite.of_finite_image (by rw [h.image_eq]; exact Set.toFinite _) h.injOn

/-- A simplicial operator `α` restricts the lifts of a singular simplex `σ` bijectively onto
the lifts of the restricted simplex `α^* σ`. -/
theorem bijOn_toSSet_obj_map {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n)
    (σ : (TopCat.toSSet.obj B).obj m) :
    Set.BijOn ((TopCat.toSSet.obj E).map α) ((TopCat.toSSet.map p).app m ⁻¹' {σ})
      ((TopCat.toSSet.map p).app n ⁻¹' {(TopCat.toSSet.obj B).map α σ}) := by
  let x : SimplexCategory.toTop.{w}.obj n.unop := SimplexCategory.toTopInitialVertex _
  let y := (SimplexCategory.toTop.map α.unop) x
  have hx := hp.bijOn_simplexMap_apply ((TopCat.toSSet.obj B).map α σ) x
  have hy := hp.bijOn_simplexMap_apply σ y
  have eval (τ : (TopCat.toSSet.obj E).obj m) :
      simplexMap ((TopCat.toSSet.obj E).map α τ) x = simplexMap τ y := by
    simp [y]
  have maps : Set.MapsTo ((TopCat.toSSet.obj E).map α) ((TopCat.toSSet.map p).app m ⁻¹' {σ})
      ((TopCat.toSSet.map p).app n ⁻¹' {(TopCat.toSSet.obj B).map α σ}) := by
    intro τ hτ
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hτ ⊢
    rw [← hτ]
    exact NatTrans.naturality_apply (TopCat.toSSet.map p) α τ
  refine ⟨maps, fun τ₁ hτ₁ τ₂ hτ₂ h ↦ hy.injOn hτ₁ hτ₂ ?_, fun τ' hτ' ↦ ?_⟩
  · simpa only [eval] using congr_arg (fun τ ↦ simplexMap τ x) h
  · obtain ⟨τ, hτ, hτy⟩ := hy.surjOn (hx.mapsTo hτ')
    refine ⟨τ, hτ, hx.injOn (maps hτ) hτ' ?_⟩
    simpa only [eval] using hτy

/-- A bijective self-map `f` of `E` over `B`, such as a deck transformation of `p`, permutes the
lifts of every singular simplex of `B` through `p`. -/
theorem bijOn_toSSet_map_app_of_comp_eq {f : E ⟶ E} (hf : Function.Bijective f)
    (hfp : f ≫ p = p) {n : SimplexCategoryᵒᵖ} (σ : (TopCat.toSSet.obj B).obj n) :
    Set.BijOn ((TopCat.toSSet.map f).app n) ((TopCat.toSSet.map p).app n ⁻¹' {σ})
      ((TopCat.toSSet.map p).app n ⁻¹' {σ}) := by
  let x : SimplexCategory.toTop.{w}.obj n.unop := SimplexCategory.toTopInitialVertex _
  have hx := hp.bijOn_simplexMap_apply σ x
  have maps : Set.MapsTo ((TopCat.toSSet.map f).app n) ((TopCat.toSSet.map p).app n ⁻¹' {σ})
      ((TopCat.toSSet.map p).app n ⁻¹' {σ}) := by
    intro τ hτ
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hτ ⊢
    rw [← hτ, ← NatTrans.comp_app_apply, ← Functor.map_comp, hfp]
  refine ⟨maps, fun τ₁ hτ₁ τ₂ hτ₂ h ↦ hx.injOn hτ₁ hτ₂ (hf.1 ?_), fun τ' hτ' ↦ ?_⟩
  · simpa using congr_arg (fun τ ↦ simplexMap τ x) h
  · -- lift `σ` through a preimage under `f` of the value of `τ'` at `x`
    obtain ⟨e, he⟩ := hf.2 (simplexMap τ' x)
    have hpe : e ∈ p ⁻¹' {simplexMap σ x} := by
      have hτ'x := hx.mapsTo hτ'
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hτ'x ⊢
      rw [← hτ'x, ← he, ← ConcreteCategory.comp_apply, hfp]
    obtain ⟨τ, hτ, hτx⟩ := hx.surjOn hpe
    refine ⟨τ, hτ, hx.injOn (maps hτ) hτ' ?_⟩
    simpa [hτx] using he

end Lifts

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- The value on the summand of a singular simplex `σ` of the transfer, before checking that it
commutes with the differentials: the sum of the summands of the lifts of `σ`. -/
private def singularTransferX (hp : IsCoveringMap p) (hfin : ∀ b, Finite ↥(p ⁻¹' {b})) (R : C)
    (n : ℕ) :
    ((TopCat.toSSet.obj B).chainComplex R).X n ⟶ ((TopCat.toSSet.obj E).chainComplex R).X n :=
  Cofan.IsColimit.desc ((TopCat.toSSet.obj B).isColimitChainComplexXCofan R n) fun σ ↦
    ∑ τ ∈ (hp.finite_preimage_singleton_toSSet_map_app hfin σ).toFinset,
      (TopCat.toSSet.obj E).ιChainComplex τ

@[reassoc]
private lemma ιChainComplex_singularTransferX (hp : IsCoveringMap p)
    (hfin : ∀ b, Finite ↥(p ⁻¹' {b})) (R : C) {n : ℕ} (σ : (TopCat.toSSet.obj B) _⦋n⦌) :
    (TopCat.toSSet.obj B).ιChainComplex σ ≫ singularTransferX hp hfin R n =
      ∑ τ ∈ (hp.finite_preimage_singleton_toSSet_map_app hfin σ).toFinset,
        (TopCat.toSSet.obj E).ιChainComplex τ :=
  Cofan.IsColimit.fac _ _ σ

/-- **The transfer** `C(B; R) ⟶ C(E; R)` of a covering map `p : E ⟶ B` with finite fibres: the
chain map sending a singular simplex of `B` to the sum of its lifts to `E`. -/
def singularTransfer (hp : IsCoveringMap p) (hfin : ∀ b, Finite ↥(p ⁻¹' {b})) (R : C) :
    (TopCat.toSSet.obj B).chainComplex R ⟶ (TopCat.toSSet.obj E).chainComplex R where
  f := singularTransferX hp hfin R
  comm' := by
    rintro _ n rfl
    ext σ
    simp only [SSet.ιChainComplex_d_assoc, ιChainComplex_singularTransferX_assoc,
      Preadditive.sum_comp, Preadditive.zsmul_comp, ιChainComplex_singularTransferX,
      SSet.ιChainComplex_d]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.smul_sum]
    congr 1
    have hbij : Set.BijOn ((TopCat.toSSet.obj E).δ i) ((TopCat.toSSet.map p).app _ ⁻¹' {σ})
        ((TopCat.toSSet.map p).app _ ⁻¹' {(TopCat.toSSet.obj B).δ i σ}) :=
      hp.bijOn_toSSet_obj_map (SimplexCategory.δ i).op σ
    refine Finset.sum_nbij ((TopCat.toSSet.obj E).δ i) (fun τ hτ ↦ ?_) (fun τ₁ hτ₁ τ₂ hτ₂ h ↦ ?_)
      (fun τ' hτ' ↦ ?_) fun _ _ ↦ rfl
    · simpa using hbij.mapsTo (by simpa using hτ)
    · exact hbij.injOn (by simpa using hτ₁) (by simpa using hτ₂) h
    · obtain ⟨τ, hτ, rfl⟩ := hbij.surjOn (by simpa using hτ')
      exact ⟨τ, by simpa using hτ, rfl⟩

/-- The transfer sends the summand of a singular simplex `σ` to the sum of the summands of the
lifts of `σ`. -/
@[reassoc (attr := simp)]
lemma ιChainComplex_singularTransfer_f (hp : IsCoveringMap p) (hfin : ∀ b, Finite ↥(p ⁻¹' {b}))
    (R : C) {n : ℕ} (σ : (TopCat.toSSet.obj B) _⦋n⦌) :
    (TopCat.toSSet.obj B).ιChainComplex σ ≫ (hp.singularTransfer hfin R).f n =
      ∑ τ ∈ (hp.finite_preimage_singleton_toSSet_map_app hfin σ).toFinset,
        (TopCat.toSSet.obj E).ιChainComplex τ :=
  ιChainComplex_singularTransferX hp hfin R σ

/-- Projecting the transfer of a singular simplex `σ` back down to `B` multiplies `σ` by the
number of points of the fibre over any point `σ x` of `σ`. -/
lemma ιChainComplex_singularTransfer_f_comp_chainComplexMap_f (hp : IsCoveringMap p)
    (hfin : ∀ b, Finite ↥(p ⁻¹' {b})) (R : C) {n : ℕ} (σ : (TopCat.toSSet.obj B) _⦋n⦌)
    (x : SimplexCategory.toTop.{w}.obj ⦋n⦌) :
    (TopCat.toSSet.obj B).ιChainComplex σ ≫ (hp.singularTransfer hfin R).f n ≫
        (SSet.chainComplexMap (TopCat.toSSet.map p) R).f n =
      Nat.card (p ⁻¹' {simplexMap σ x}) • (TopCat.toSSet.obj B).ιChainComplex σ := by
  have h := hp.bijOn_simplexMap_apply σ x
  have hcard : (hp.finite_preimage_singleton_toSSet_map_app hfin σ).toFinset.card =
      Nat.card (p ⁻¹' {simplexMap σ x}) := by
    rw [← Set.ncard_eq_toFinset_card _ _, Nat.card_coe_set_eq, ← h.image_eq,
      h.injOn.ncard_image]
  rw [ιChainComplex_singularTransfer_f_assoc, Preadditive.sum_comp]
  simp only [SSet.ι_chainComplexMap_f]
  rw [Finset.sum_congr rfl fun τ hτ ↦ by rw [(Set.Finite.mem_toFinset _).mp hτ],
    Finset.sum_const, hcard]

/-- **The transfer formula** `p_* ∘ transfer = d • id` on singular chains, for a covering map
whose fibres all have `d` points. -/
theorem singularTransfer_comp_chainComplexMap (hp : IsCoveringMap p)
    (hfin : ∀ b, Finite ↥(p ⁻¹' {b})) (R : C) {d : ℕ} (hd : ∀ b, Nat.card (p ⁻¹' {b}) = d) :
    hp.singularTransfer hfin R ≫ SSet.chainComplexMap (TopCat.toSSet.map p) R = d • 𝟙 _ := by
  ext n σ
  rw [HomologicalComplex.comp_f,
    ιChainComplex_singularTransfer_f_comp_chainComplexMap_f hp hfin R σ
      (SimplexCategory.toTopInitialVertex _), hd, HomologicalComplex.nsmul_f_apply,
    HomologicalComplex.id_f, Preadditive.comp_nsmul, Category.comp_id]

/-- **The transfer formula** `p_* ∘ transfer = d • id` on singular homology, for a covering map
whose fibres all have `d` points. -/
theorem homologyMap_singularTransfer_comp_homologyMap [CategoryWithHomology C]
    (hp : IsCoveringMap p) (hfin : ∀ b, Finite ↥(p ⁻¹' {b})) (R : C) {d : ℕ}
    (hd : ∀ b, Nat.card (p ⁻¹' {b}) = d) (n : ℕ) :
    HomologicalComplex.homologyMap (hp.singularTransfer hfin R) n ≫
        SSet.homologyMap (TopCat.toSSet.map p) R n = d • 𝟙 _ := by
  rw [← HomologicalComplex.homologyMap_comp, singularTransfer_comp_chainComplexMap hp hfin R hd]
  exact (HomologicalComplex.homologyFunctor C _ n).map_nsmul.trans
    (congrArg (d • ·) ((HomologicalComplex.homologyFunctor C _ n).map_id _))

/-- **The transfer is invariant under deck transformations**: `f_* ∘ transfer = transfer` on
singular chains for every bijective self-map `f` of `E` over `B`, since `f` permutes the lifts of
each singular simplex. -/
theorem singularTransfer_comp_chainComplexMap_of_comp_eq (hp : IsCoveringMap p)
    (hfin : ∀ b, Finite ↥(p ⁻¹' {b})) (R : C) {f : E ⟶ E} (hf : Function.Bijective f)
    (hfp : f ≫ p = p) :
    hp.singularTransfer hfin R ≫ SSet.chainComplexMap (TopCat.toSSet.map f) R =
      hp.singularTransfer hfin R := by
  ext n σ
  rw [HomologicalComplex.comp_f, ιChainComplex_singularTransfer_f_assoc, Preadditive.sum_comp,
    ιChainComplex_singularTransfer_f]
  simp only [SSet.ι_chainComplexMap_f]
  have hbij := hp.bijOn_toSSet_map_app_of_comp_eq hf hfp σ
  refine Finset.sum_nbij ((TopCat.toSSet.map f).app _) (fun τ hτ ↦ ?_)
    (fun τ₁ hτ₁ τ₂ hτ₂ h ↦ ?_) (fun τ' hτ' ↦ ?_) fun _ _ ↦ rfl
  · simpa using hbij.mapsTo (by simpa using hτ)
  · exact hbij.injOn (by simpa using hτ₁) (by simpa using hτ₂) h
  · obtain ⟨τ, hτ, rfl⟩ := hbij.surjOn (by simpa using hτ')
    exact ⟨τ, by simpa using hτ, rfl⟩

/-- **The transfer is invariant under deck transformations**: `f_* ∘ transfer = transfer` on
singular homology for every bijective self-map `f` of `E` over `B`. -/
theorem homologyMap_singularTransfer_comp_homologyMap_of_comp_eq [CategoryWithHomology C]
    (hp : IsCoveringMap p) (hfin : ∀ b, Finite ↥(p ⁻¹' {b})) (R : C) {f : E ⟶ E}
    (hf : Function.Bijective f) (hfp : f ≫ p = p) (n : ℕ) :
    HomologicalComplex.homologyMap (hp.singularTransfer hfin R) n ≫
        SSet.homologyMap (TopCat.toSSet.map f) R n =
      HomologicalComplex.homologyMap (hp.singularTransfer hfin R) n := by
  rw [← HomologicalComplex.homologyMap_comp,
    singularTransfer_comp_chainComplexMap_of_comp_eq hp hfin R hf hfp]

end IsCoveringMap

namespace IsQuotientCoveringMap

open IsCoveringMap

variable {E B : TopCat.{w}} {p : E ⟶ B}
  {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {G : Type*} [Group G] [Fintype G] [MulAction G E]

/-- **The deck-transformation formula** `transfer ∘ p_* = ∑_{g ∈ G} g_*` on singular chains, for
the quotient covering map `p` of an action of a finite group `G`. -/
theorem chainComplexMap_comp_singularTransfer
    (hG : IsQuotientCoveringMap p G) (R : C) :
    SSet.chainComplexMap (TopCat.toSSet.map p) R ≫
        hG.isCoveringMap.singularTransfer hG.finite_fiber R =
      ∑ g : G, SSet.chainComplexMap
        (TopCat.toSSet.map (TopCat.ofHom ⟨(g • ·), hG.continuous_const_smul g⟩)) R := by
  classical
  have := hG.isCancelSMul
  have hp := hG.isCoveringMap
  ext n τ
  let act (g : G) : E ⟶ E := TopCat.ofHom ⟨(g • ·), hG.continuous_const_smul g⟩
  have hsum : (∑ g : G, SSet.chainComplexMap (TopCat.toSSet.map (act g)) R).f n =
      ∑ g : G, (SSet.chainComplexMap (TopCat.toSSet.map (act g)) R).f n :=
    map_sum (HomologicalComplex.Hom.fAddMonoidHom n) _ _
  rw [HomologicalComplex.comp_f, SSet.ι_chainComplexMap_f_assoc, ιChainComplex_singularTransfer_f,
    hsum, Preadditive.comp_sum]
  simp only [SSet.ι_chainComplexMap_f]
  let x : SimplexCategory.toTop.{w}.obj ⦋n⦌ := SimplexCategory.toTopInitialVertex _
  let σ := (TopCat.toSSet.map p).app _ τ
  have hbij := hp.bijOn_simplexMap_apply σ x
  have act_apply (g : G) :
      simplexMap ((TopCat.toSSet.map (act g)).app _ τ) x = g • simplexMap τ x := by
    simp [act, simplexMap_app]
  have act_mem (g : G) : (TopCat.toSSet.map (act g)).app _ τ ∈
      (TopCat.toSSet.map p).app _ ⁻¹' {σ} := by
    have hcomp : act g ≫ p = p := by
      ext e
      exact hG.map_smul g
    simp only [Set.mem_preimage, Set.mem_singleton_iff, σ, ← NatTrans.comp_app_apply,
      ← Functor.map_comp, hcomp]
  have hτ : τ ∈ (TopCat.toSSet.map p).app _ ⁻¹' {σ} := rfl
  -- every lift of `σ` is a translate of `τ`: compare their values at `x` in the fibre over `σ x`
  have hex (τ' : (TopCat.toSSet.obj E) _⦋n⦌) (hτ' : τ' ∈ (TopCat.toSSet.map p).app _ ⁻¹' {σ}) :
      ∃ g : G, simplexMap τ' x = g • simplexMap τ x := by
    obtain ⟨g, hg⟩ := hG.apply_eq_iff_mem_orbit.mp ((hbij.mapsTo hτ').trans (hbij.mapsTo hτ).symm)
    exact ⟨g, hg.symm⟩
  let j (τ' : (TopCat.toSSet.obj E) _⦋n⦌) : G :=
    if h : τ' ∈ (TopCat.toSSet.map p).app _ ⁻¹' {σ} then (hex τ' h).choose else 1
  have hj (τ' : (TopCat.toSSet.obj E) _⦋n⦌) (h : τ' ∈ (TopCat.toSSet.map p).app _ ⁻¹' {σ}) :
      simplexMap τ' x = j τ' • simplexMap τ x := by
    simp only [j, h, ↓reduceDIte]
    exact (hex τ' h).choose_spec
  -- `g ↦ g • τ` is a bijection from `G` onto the lifts of `σ`, with inverse `j`, since the action
  -- is free and evaluation at `x` is injective on lifts
  symm
  refine Finset.sum_nbij' (fun g ↦ (TopCat.toSSet.map (act g)).app _ τ) j
    (fun g _ ↦ (Set.Finite.mem_toFinset _).mpr (act_mem g)) (fun _ _ ↦ Finset.mem_univ _)
    (fun g _ ↦ ?_) (fun τ' hτ' ↦ ?_) fun _ _ ↦ rfl
  · exact IsCancelSMul.right_cancel _ _ (simplexMap τ x)
      ((hj _ (act_mem g)).symm.trans (act_apply g))
  · have hτ' := (Set.Finite.mem_toFinset _).mp hτ'
    exact hbij.injOn (act_mem _) hτ' ((act_apply _).trans (hj τ' hτ').symm)

end IsQuotientCoveringMap

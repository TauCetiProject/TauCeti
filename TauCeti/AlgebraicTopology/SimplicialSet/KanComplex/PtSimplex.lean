/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex.MulStruct
public import TauCeti.AlgebraicTopology.SimplicialSet.ProdStdSimplexOne

/-!
# Homotopies of pointed simplices in Kan complexes

For a simplicial set `X` with a vertex `x`, Mathlib's `X.PtSimplex n x` is the type of morphisms
`Δ[n] ⟶ X` sending the boundary `∂Δ[n]` to `x`, and `SSet.PtSimplex.RelStruct p q i` is the
combinatorial homotopy relation: an `(n + 1)`-simplex whose `i`th and `(i + 1)`st faces are `p`
and `q` and whose other faces are constant. This file compares these relations with each other and
with homotopies `Δ[n] ⊗ Δ[1] ⟶ X` relative to `∂Δ[n]` (`SSet.PtSimplex.Homotopy`), which is what
makes the homotopy groups of a Kan complex well defined.

* For a Kan complex and `n ≥ 1`, each relation `RelStruct · · i` is symmetric and transitive
  (`SSet.PtSimplex.RelStruct.symm`, `SSet.PtSimplex.RelStruct.trans`), and all of them are
  equivalent to `RelStruct₀ = RelStruct · · 0` (`SSet.PtSimplex.RelStruct.relStruct₀`,
  `SSet.PtSimplex.RelStruct₀.relStruct`). These follow from the associativity and unit laws of
  Mathlib's `SSet.PtSimplex.MulStruct`.
* In any simplicial set, `h : RelStruct₀ p q` gives a homotopy from `q` to `p`
  (`SSet.PtSimplex.RelStruct₀.homotopy`): precompose the simplex of `h` with the map
  `Δ[n] ⊗ Δ[1] ⟶ Δ[n + 1]` which collapses the edges `{k} × Δ[1]` for `k ≠ 0`.
* In a Kan complex and for `n ≥ 1`, a homotopy from `p` to `q` gives a `RelStruct₀ p q`
  (`SSet.PtSimplex.Homotopy.relStruct₀`): restricting the homotopy to the `n + 1` nondegenerate
  `(n + 1)`-simplices `SSet.prodStdSimplex₁.ι i` of the prism `Δ[n] ⊗ Δ[1]` gives a chain of
  `RelStruct`s from `q` to `p`.
* Products in the sense of `MulStruct` are well defined up to `RelStruct₀`
  (`SSet.PtSimplex.MulStruct.unique`, `SSet.PtSimplex.MulStruct.unique'`), and morphisms of
  simplicial sets carry `MulStruct`s to `MulStruct`s (`SSet.PtSimplex.MulStruct.postcomp`).

The case `n = 0`, where `RelStruct₀` is an edge between vertices, is not treated here.

## References

The statements and the proofs of the comparisons between `RelStruct`, `MulStruct` and homotopies
in Kan complexes follow Joël Riou's Mathlib pull request
[mathlib4#42435](https://github.com/leanprover-community/mathlib4/pull/42435) (file
`Mathlib/AlgebraicTopology/SimplicialSet/KanComplex/PtSimplexEquiv.lean`), restricted to
positive dimensions. The construction of a homotopy from a `RelStruct₀` through an explicit map
`Δ[n] ⊗ Δ[1] ⟶ Δ[n + 1]` is different from the one there.

* J. P. May, *Simplicial Objects in Algebraic Topology*, University of Chicago Press, 1967,
  Chapter I, §3–§4.
-/

public section

universe u

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory

namespace SSet

namespace prodStdSimplex₁

section collapse

variable (p : ℕ)

/-- The monotone map `Fin (p + 1) × Fin 2 → Fin (p + 2)` which sends `(0, e)` to `e` and
`(k, e)` to `k + 1` for `k ≠ 0`. -/
private def collapseOrderHom : Fin (p + 1) × Fin 2 →o Fin (p + 2) where
  toFun z := if z.1 = 0 then z.2.castLE (by lia) else z.1.succ
  monotone' := by
    rintro ⟨a, e⟩ ⟨a', e'⟩ ⟨ha, he⟩
    dsimp only
    split_ifs with h h' h' <;>
      simp only [Fin.le_def, Fin.ext_iff, Fin.val_zero, Fin.val_castLE, Fin.val_succ] at * <;>
      lia

/-- The morphism `Δ[p] ⊗ Δ[1] ⟶ Δ[p + 1]` induced by `collapseOrderHom p`. Its restrictions to
the bottom and the top of the prism are the faces `δ 1` and `δ 0` of `Δ[p + 1]`. -/
private noncomputable def collapse : (Δ[p] ⊗ Δ[1] : SSet.{u}) ⟶ Δ[p + 1] where
  app _ := TypeCat.ofHom fun z ↦ stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk
    ((collapseOrderHom p).comp
      ((stdSimplex.objEquiv z.1).toOrderHom.prod (stdSimplex.objEquiv z.2).toOrderHom)))

private lemma collapse_app_apply {d : ℕ} (z : (Δ[p] ⊗ Δ[1] : SSet.{u}) _⦋d⦌) (t : Fin (d + 1)) :
    (collapse p).app _ z t = collapseOrderHom p (z.1 t, z.2 t) := rfl

private lemma collapseOrderHom_apply (z : Fin (p + 1) × Fin 2) :
    collapseOrderHom p z = if z.1 = 0 then z.2.castLE (by lia) else z.1.succ := rfl

private lemma ι₀_collapse : ι₀ ≫ collapse.{u} p = stdSimplex.δ 1 := by
  apply yonedaEquiv.injective
  refine stdSimplex.ext _ _ fun k ↦ ?_
  -- Unfolding `yonedaEquiv`, the two sides evaluate `k` by `collapseOrderHom p (k, 0)` and by
  -- `δ 1`.
  refine (?_ : collapseOrderHom p (k, 0) = Fin.succAbove 1 k)
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_eq_succ <;> simp [collapseOrderHom_apply]

private lemma ι₁_collapse : ι₁ ≫ collapse.{u} p = stdSimplex.δ 0 := by
  apply yonedaEquiv.injective
  refine stdSimplex.ext _ _ fun k ↦ ?_
  -- Unfolding `yonedaEquiv`, the two sides evaluate `k` by `collapseOrderHom p (k, 1)` and by
  -- `δ 0`.
  refine (?_ : collapseOrderHom p (k, 1) = Fin.succAbove 0 k)
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_eq_succ <;> simp [collapseOrderHom_apply, Fin.ext_iff]

end collapse

end prodStdSimplex₁

namespace PtSimplex

variable {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}

namespace RelStruct

open MulStruct

variable [KanComplex X]

/-- Symmetry of `RelStruct` in a Kan complex. -/
noncomputable def symm {p q : X.PtSimplex (n + 1) x} {i : Fin (n + 2)} (h : RelStruct p q i) :
    RelStruct q p i := by
  cases i using Fin.lastCases with
  | last =>
    exact relStructSuccEquivMulStruct.symm
      (mulOneEqSymm (relStructSuccEquivMulStruct (i := Fin.last n) h))
  | cast i =>
    exact relStructCastSuccEquivMulStruct.symm (oneMulEqSymm (relStructCastSuccEquivMulStruct h))

/-- Transitivity of `RelStruct` in a Kan complex. -/
noncomputable def trans {p q r : X.PtSimplex (n + 1) x} {i : Fin (n + 2)} (h : RelStruct p q i)
    (h' : RelStruct q r i) : RelStruct p r i := by
  cases i using Fin.lastCases with
  | last =>
    exact relStructSuccEquivMulStruct.symm
      (mulOneEqTrans (relStructSuccEquivMulStruct (i := Fin.last n) h')
        (relStructSuccEquivMulStruct (i := Fin.last n) h))
  | cast i =>
    exact relStructCastSuccEquivMulStruct.symm
      (oneMulEqTrans (relStructCastSuccEquivMulStruct h) (relStructCastSuccEquivMulStruct h'))

/-- A `RelStruct p q i.succ` deduced from a `RelStruct p q i.castSucc` in a Kan complex. -/
noncomputable def succ {p q : X.PtSimplex (n + 1) x} {i : Fin (n + 1)}
    (h : RelStruct p q i.castSucc) : RelStruct p q i.succ :=
  relStructSuccEquivMulStruct.symm (mulOneEqOfOneMulEq (relStructCastSuccEquivMulStruct h.symm))

/-- A `RelStruct p q i.castSucc` deduced from a `RelStruct p q i.succ` in a Kan complex. -/
noncomputable def ofSucc {p q : X.PtSimplex (n + 1) x} {i : Fin (n + 1)}
    (h : RelStruct p q i.succ) : RelStruct p q i.castSucc :=
  relStructCastSuccEquivMulStruct.symm (oneMulEqOfMulOneEq (relStructSuccEquivMulStruct h.symm))

/-- A `RelStruct₀ p q` deduced from a `RelStruct p q i` in a Kan complex. -/
noncomputable def relStruct₀ {p q : X.PtSimplex (n + 1) x} {i : Fin (n + 2)}
    (h : RelStruct p q i) : RelStruct₀ p q := by
  induction i using Fin.induction with
  | zero => exact h
  | succ i hi => exact hi h.ofSucc

end RelStruct

namespace RelStruct₀

variable [KanComplex X]

/-- Symmetry of `RelStruct₀` in a Kan complex. -/
noncomputable abbrev symm {p q : X.PtSimplex (n + 1) x} (h : RelStruct₀ p q) : RelStruct₀ q p :=
  RelStruct.symm h

/-- Transitivity of `RelStruct₀` in a Kan complex. -/
noncomputable abbrev trans {p q r : X.PtSimplex (n + 1) x} (h₁ : RelStruct₀ p q)
    (h₂ : RelStruct₀ q r) : RelStruct₀ p r :=
  RelStruct.trans h₁ h₂

/-- A `RelStruct p q i` deduced from a `RelStruct₀ p q` in a Kan complex. -/
noncomputable def relStruct {p q : X.PtSimplex (n + 1) x} (h : RelStruct₀ p q) (i : Fin (n + 2)) :
    RelStruct p q i := by
  induction i using Fin.induction with
  | zero => exact h
  | succ i hi => exact hi.succ

end RelStruct₀

namespace MulStruct

variable [KanComplex X]

/-- In a Kan complex, a product of pointed simplices is well defined up to `RelStruct₀`: products
of `RelStruct₀`-related factors are `RelStruct₀`-related. -/
noncomputable def unique {p₀₁ p₁₂ p₀₂ p₀₁' p₁₂' p₀₂' : X.PtSimplex (n + 1) x} {i : Fin (n + 1)}
    (h : MulStruct p₀₁ p₁₂ p₀₂ i) (h' : MulStruct p₀₁' p₁₂' p₀₂' i)
    (h₀₁ : RelStruct₀ p₀₁ p₀₁') (h₁₂ : RelStruct₀ p₁₂ p₁₂') : RelStruct₀ p₀₂ p₀₂' :=
  RelStruct.relStruct₀ (relStructSuccEquivMulStruct.symm
    (assoc h' (relStructSuccEquivMulStruct (h₁₂.relStruct i.succ))
      (assoc (relStructSuccEquivMulStruct (h₀₁.symm.relStruct i.succ)) (oneMul p₁₂ i) h)))

/-- In a Kan complex, a `MulStruct p₀₁ p₁₂ p₀₂ i` gives a `MulStruct p₀₁ p₁₂ p₀₂' i` when
`p₀₂` and `p₀₂'` are related by `RelStruct₀`. -/
noncomputable def unique' {p₀₁ p₁₂ p₀₂ p₀₂' : X.PtSimplex (n + 1) x} {i : Fin (n + 1)}
    (h : MulStruct p₀₁ p₁₂ p₀₂ i) (h₀₂ : RelStruct₀ p₀₂ p₀₂') : MulStruct p₀₁ p₁₂ p₀₂' i :=
  assoc' h (mulOne p₁₂ i) (relStructSuccEquivMulStruct (h₀₂.symm.relStruct i.succ))

end MulStruct

namespace MulStruct

variable {Y : SSet.{u}} {y : Y _⦋0⦌}

/-- The image of a `MulStruct` under a morphism of simplicial sets sending `x` to `y`. -/
def postcomp {p q pq : X.PtSimplex n x} {i : Fin n} (h : MulStruct p q pq i) (f : X ⟶ Y)
    (hy : f.app _ x = y) :
    MulStruct (p.comp (.ofSimplex₀ f x y hy) (by simp)) (q.comp (.ofSimplex₀ f x y hy) (by simp))
      (pq.comp (.ofSimplex₀ f x y hy) (by simp)) i where
  map := h.map ≫ f
  δ_map_of_lt j hj := by simp [h.δ_map_of_lt_assoc j hj, hy]
  δ_map_of_gt j hj := by simp [h.δ_map_of_gt_assoc j hj, hy]

end MulStruct

/-- Given `p` and `q` in `X.PtSimplex n x`, this is the type of homotopies `Δ[n] ⊗ Δ[1] ⟶ X`
from `p` to `q` relative to the boundary `∂Δ[n]`. -/
abbrev Homotopy (p q : X.PtSimplex n x) : Type u := RelativeMorphism.Homotopy p q

namespace Homotopy

variable {p q : X.PtSimplex (n + 1) x} (h : Homotopy p q)

/-- A homotopy between pointed simplices is constant on the simplices of `Δ[n + 1] ⊗ Δ[1]` whose
first projection lies in a face of `Δ[n + 1]`. -/
lemma comp_h_eq_const {Y : SSet.{u}} (f : Y ⟶ Δ[n + 1] ⊗ Δ[1]) (g : Y ⟶ Δ[n]) (k : Fin (n + 2))
    (hf : f ≫ fst _ _ = g ≫ stdSimplex.δ k) : f ≫ h.h = const x := by
  have : f = lift (g ≫ boundary.ι k) (f ≫ snd _ _) ≫ ∂Δ[n + 1].ι ▷ Δ[1] := by
    ext1 <;> simp [hf]
  rw [this, Category.assoc, h.rel]
  simp

/-- The restriction of `h` to the `(n + 1)`-simplex of `Δ[n + 1] ⊗ Δ[1]` whose second
projection takes the value `0` exactly `j` times. -/
private noncomputable def face (j : Fin (n + 1 + 2)) : X.PtSimplex (n + 1) x where
  map := yonedaEquiv.symm (prodStdSimplex₁.codimOneSimplex j).val ≫ h.h
  comm := by
    ext k : 1
    simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, comp_const]
    rw [← Category.assoc]
    exact h.comp_h_eq_const _ (𝟙 _) k (by
      rw [Category.assoc, prodStdSimplex₁.yonedaEquiv_symm_codimOneSimplex_fst, Category.comp_id,
        Category.id_comp])

private lemma face_map (j : Fin (n + 1 + 2)) :
    (face h j).map = yonedaEquiv.symm (prodStdSimplex₁.codimOneSimplex j).val ≫ h.h := rfl

private lemma face_zero : face h 0 = q := by
  ext : 1
  rw [face_map, prodStdSimplex₁.yonedaEquiv_symm_codimOneSimplex_zero, h.h₁]

private lemma face_last : face h (Fin.last _) = p := by
  ext : 1
  rw [face_map, prodStdSimplex₁.yonedaEquiv_symm_codimOneSimplex_last, h.h₀]

/-- The restriction of `h` to the `i`th nondegenerate `(n + 2)`-simplex of `Δ[n + 1] ⊗ Δ[1]`. -/
private noncomputable def ρ (i : Fin (n + 2)) :
    RelStruct (face h i.castSucc) (face h i.succ) i where
  map := prodStdSimplex₁.ι i ≫ h.h
  δ_castSucc_map := by rw [face_map, prodStdSimplex₁.δ_castSucc_ι_assoc]
  δ_succ_map := by rw [face_map, prodStdSimplex₁.δ_succ_ι_assoc]
  δ_map_of_lt j hj := by
    obtain ⟨i, rfl⟩ := i.eq_succ_of_ne_zero (by rintro rfl; simp at hj)
    obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hj)
    rw [← Category.assoc]
    refine h.comp_h_eq_const _ (stdSimplex.σ i) j ?_
    rw [Category.assoc, prodStdSimplex₁.ι_fst,
      stdSimplex.δ_comp_σ_of_le (by simpa [Fin.castSucc_lt_succ_iff] using hj)]
  δ_map_of_gt j hj := by
    obtain ⟨i, rfl⟩ := i.eq_castSucc_of_ne_last (by
      rintro rfl
      simp only [Fin.lt_def, Fin.val_succ, Fin.val_last] at hj
      lia)
    obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hj)
    rw [← Category.assoc]
    refine h.comp_h_eq_const _ (stdSimplex.σ i) j ?_
    rw [Category.assoc, prodStdSimplex₁.ι_fst,
      stdSimplex.δ_comp_σ_of_gt (by simpa using hj)]

/-- A homotopy between pointed simplices of a Kan complex gives a `RelStruct₀`. -/
noncomputable def relStruct₀ [KanComplex X] : RelStruct₀ p q := by
  have (j : Fin (n + 1 + 2)) : RelStruct₀ q (face h j) := by
    induction j using Fin.induction with
    | zero => exact RelStruct.ofEq (face_zero h).symm 0
    | succ i hi => exact hi.trans (ρ h i).relStruct₀
  exact ((this (Fin.last _)).copy rfl (face_last h)).symm

end Homotopy

namespace RelStruct₀

variable {p q : X.PtSimplex n x} (h : RelStruct₀ p q)

/-- The `(n + 1)`-simplex of a `RelStruct₀` is constant on the simplices of `Δ[n + 1]` which miss
a vertex `v ≥ 2`, or both vertices `0` and `1`. -/
private lemma stdSimplex_map_comp_map_eq_const {d : ℕ} (θ : ⦋d⦌ ⟶ ⦋n + 1⦌)
    (hθ : (∃ v : Fin (n + 2), 1 < v ∧ ∀ t, θ.toOrderHom t ≠ v) ∨
      ∀ t, θ.toOrderHom t ≠ 0 ∧ θ.toOrderHom t ≠ 1) :
    stdSimplex.map θ ≫ h.map = const x := by
  -- `stdSimplex.δ` is the image of `SimplexCategory.δ` under the cosimplicial object `stdSimplex`.
  have hδ {m : ℕ} (i : Fin (m + 2)) :
      stdSimplex.map (SimplexCategory.δ i) = stdSimplex.{u}.δ i := rfl
  obtain ⟨v, hv, hθv⟩ | hθ := hθ
  · obtain ⟨θ', rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective' θ v hθv
    rw [Functor.map_comp, Category.assoc, hδ, h.δ_map_of_gt v (by simpa using hv), comp_const]
  · obtain ⟨θ', rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective' θ 0 fun t ↦ (hθ t).1
    obtain _ | n := n
    · exact absurd (hθ 0).2 (by simp [SimplexCategory.δ, Fin.ext_iff, Fin.val_eq_zero])
    obtain ⟨θ'', rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective' θ' 0 fun t ht ↦
      (hθ t).2 (by simp [SimplexCategory.δ, ht])
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hδ, hδ,
      (by simpa using h.δ_castSucc_map : stdSimplex.δ 0 ≫ h.map = p.map), p.δ_map, comp_const]

/-- Given `h : RelStruct₀ p q`, the homotopy from `q` to `p` obtained by precomposing the
`(n + 1)`-simplex of `h` with the map `Δ[n] ⊗ Δ[1] ⟶ Δ[n + 1]` which collapses the edges
`{k} × Δ[1]` for `k ≠ 0`. -/
noncomputable def homotopy : Homotopy q p where
  h := prodStdSimplex₁.collapse n ≫ h.map
  h₀ := by
    rw [← Category.assoc, prodStdSimplex₁.ι₀_collapse]
    exact h.δ_succ_map
  h₁ := by
    rw [← Category.assoc, prodStdSimplex₁.ι₁_collapse]
    simpa using h.δ_castSucc_map
  rel := by
    -- A simplex of `∂Δ[n] ⊗ Δ[1]` misses a vertex `j` of `Δ[n]` in its first projection, so its
    -- image under `collapse` misses `j + 1` if `j ≠ 0`, and both `0` and `1` if `j = 0`.
    rw [Subcomplex.ofSimplex_ι, comp_const, comp_const]
    refine hom_ext_uliftYoneda fun ⟨d⟩ φ ↦ ?_
    let a : Δ[n] _⦋d⦌ := (yonedaEquiv φ).1.1
    have ha : a ∈ (∂Δ[n]).obj _ := (yonedaEquiv φ).1.2
    have : φ ≫ ∂Δ[n].ι ▷ Δ[1] ≫ prodStdSimplex₁.collapse n =
        stdSimplex.map (SimplexCategory.Hom.mk ((prodStdSimplex₁.collapseOrderHom n).comp
          ((stdSimplex.objEquiv a).toOrderHom.prod
            (stdSimplex.objEquiv (yonedaEquiv φ).2).toOrderHom))) := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_map]
      -- both sides are the simplex `collapse` assigns to `yonedaEquiv φ`, by definition
      rfl
    rw [reassoc_of% this, comp_const]
    apply stdSimplex_map_comp_map_eq_const
    obtain ⟨j, hj⟩ := (mem_boundary_iff_notMem_range a).1 ha
    obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
    · refine Or.inr fun t ↦ ?_
      have hat : a t ≠ 0 := fun h' ↦ hj ⟨t, h'⟩
      simp only [Fin.ne_iff_vne, Fin.val_zero] at hat
      simp [prodStdSimplex₁.collapseOrderHom_apply, Fin.ext_iff, hat]
    · refine Or.inl ⟨j.succ.succ, by simp [Fin.lt_def], fun t ↦ ?_⟩
      have hat : a t ≠ j.succ := fun h' ↦ hj ⟨t, h'⟩
      simp only [SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe, Function.comp_apply,
        OrderHom.prod_coe, prodStdSimplex₁.collapseOrderHom_apply]
      split_ifs
      · simp only [ne_eq, Fin.ext_iff, Fin.val_castLE, Fin.val_succ]
        lia
      · exact fun h' ↦ hat (Fin.succ_injective _ h')

end RelStruct₀

end PtSimplex

end SSet

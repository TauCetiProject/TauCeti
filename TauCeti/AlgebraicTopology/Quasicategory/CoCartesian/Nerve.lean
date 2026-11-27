/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import TauCeti.AlgebraicTopology.Quasicategory.EquivalenceCartesian
public import TauCeti.AlgebraicTopology.SimplicialSet.Coskeletal
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.StrictSegal
import Mathlib.AlgebraicTopology.SimplicialSet.Coskeletal
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
import TauCeti.CategoryTheory.ComposableArrows.Basic
import TauCeti.CategoryTheory.FiberedCategory.HomLift

/-!
# CoCartesian edges of the nerve of a functor

Let `F : E ⥤ B` be a functor. A morphism `φ : a ⟶ b` of `E` is strongly coCartesian for `F`
(Mathlib's `CategoryTheory.Functor.IsStronglyCocartesian`) when every morphism `a ⟶ b'` lying over
a composite `F φ ≫ g` factors uniquely through `φ` by a morphism lying over `g`. Then the edge of
the nerve given by `φ` is coCartesian for the map of nerves `nerveMap F`
(`CategoryTheory.nerve.isCoCartesian_edgeMk_of_isStronglyCocartesian`). This is how ordinary
categories fibred over the category of finite pointed sets, such as categories of operators, give
coCartesian edges of simplicial sets over its nerve.

By the horn criterion `SSet.Edge.isCoCartesian_of_hornFilling_zero`, it suffices to fill the horns
`Λ[n + 2, 0]` of the nerve of `E` whose initial edge is `φ` over every `(n + 2)`-simplex of the
nerve of `B`. Nerves are `2`-coskeletal, so horns of dimension at least `4` have unique fillers
(`SSet.existsUnique_horn_extension_of_isCoskeletal`), and a simplex of the nerve of `B` is
determined by its restriction to a horn of dimension at least `3`
(`SSet.IsStrictSegal.hom_ext_of_horn`). For `Λ[2, 0]`, given `φ : a ⟶ b` and `h : a ⟶ c` over
`F φ ≫ g`, the filler is the composable pair `φ, χ` for the factorization `χ` of `h` through `φ`
over `g`. For `Λ[3, 0]`, the three given triangles determine every edge, and the missing face
commutes because two morphisms out of `b` lying over the same morphism agree once they agree after
precomposition with `φ`. This case analysis follows the proof that the nerve of a groupoid is a Kan
complex (`CategoryTheory.nerve.kanComplex`), with the inverse of an isomorphism replaced by the
universal property of `φ`.

## Main results

* `CategoryTheory.nerve.isCoCartesian_edgeMk_of_isStronglyCocartesian`: the edge of the nerve given
  by a strongly coCartesian morphism is coCartesian for the map of nerves.

## References

* J. Lurie, *Higher Topos Theory*, Remark 2.4.1.4 and Remark 2.4.1.9 (the horn description of
  coCartesian edges).
-/

public section

open CategoryTheory Functor Simplicial SSet

universe v u

namespace CategoryTheory.nerve

variable {E B : Type u} [Category.{v} E] [Category.{v} B] (F : E ⥤ B)

/-- The horn `Λ[2, 0]` in the nerve of `E`, given by its faces `δ 1` and `δ 2 = φ`, has a filler
over the `2`-simplex `z` of the nerve of `B`, when `φ` is strongly coCartesian for `F`. -/
private lemma exists_horn₂₀ {a b : E} (φ : a ⟶ b) [F.IsStronglyCocartesian (F.map φ) φ]
    (y : (nerve E) _⦋1⦌) (hy : (nerve E).δ 1 y = (nerve E).δ 1 (ComposableArrows.mk₁ φ))
    (z : (nerve B) _⦋2⦌) (hz₁ : (nerve B).δ 1 z = (nerveMap F).app _ y)
    (hz₂ : (nerve B).δ 2 z = (nerveMap F).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ φ)) :
    ∃ x : (nerve E) _⦋2⦌, (nerve E).δ 1 x = y ∧ (nerve E).δ 2 x = ComposableArrows.mk₁ φ ∧
      (nerveMap F).app _ x = z := by
  obtain ⟨a', c, h, rfl⟩ := ComposableArrows.mk₁_surjective y
  obtain ⟨_, _, _, g₁, g₂, rfl⟩ := ComposableArrows.mk₂_surjective z
  -- The edge `h` starts at the source `a` of `φ`.
  obtain rfl : a' = a := congrArg (fun w : ComposableArrows E 0 ↦ w.obj 0) hy
  rw [δ₁_mk₂_eq, nerveMap_app_mk₁] at hz₁
  rw [δ₂_mk₂_eq, nerveMap_app_mk₁] at hz₂
  obtain ⟨rfl, rfl, hg₁⟩ := (Arrow.mk_eq_mk_iff _ _).1 (ComposableArrows.mk₁_eq_mk₁_iff.1 hz₂)
  obtain ⟨_, rfl, hg⟩ := (Arrow.mk_eq_mk_iff _ _).1 (ComposableArrows.mk₁_eq_mk₁_iff.1 hz₁)
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hg₁ hg
  subst hg₁
  -- The factorization of `h` through `φ` over `g₂` gives the missing edge.
  have hχ : F.IsHomLift g₂ (IsStronglyCocartesian.map F (F.map φ) φ hg.symm h) := inferInstance
  refine ⟨ComposableArrows.mk₂ φ (IsStronglyCocartesian.map F (F.map φ) φ hg.symm h), ?_,
    δ₂_mk₂_eq _ _, ?_⟩
  · rw [δ₁_mk₂_eq, IsStronglyCocartesian.fac]
  · rw [nerveMap_app_mk₂, isHomLift_iff_map_eq.1 hχ]

/-- The horn `Λ[3, 0]` in the nerve of `E`, given by its faces `δ 1`, `δ 2` and `δ 3`, whose
initial edge is `φ`, has a filler, when `φ` is strongly coCartesian for `F` and the horn lies over
a `3`-simplex `z` of the nerve of `B`. -/
private lemma exists_horn₃₀ {a b : E} (φ : a ⟶ b) [F.IsStronglyCocartesian (F.map φ) φ]
    (y₁ y₂ y₃ : (nerve E) _⦋2⦌) (h₁₂ : (nerve E).δ 1 y₁ = (nerve E).δ 1 y₂)
    (h₁₃ : (nerve E).δ 2 y₁ = (nerve E).δ 1 y₃) (h₂₃ : (nerve E).δ 2 y₂ = (nerve E).δ 2 y₃)
    (hφ : (nerve E).δ 2 y₃ = ComposableArrows.mk₁ φ) (z : (nerve B) _⦋3⦌)
    (hz₁ : (nerve B).δ 1 z = (nerveMap F).app _ y₁) (hz₂ : (nerve B).δ 2 z = (nerveMap F).app _ y₂)
    (hz₃ : (nerve B).δ 3 z = (nerveMap F).app _ y₃) :
    ∃ x : (nerve E) _⦋3⦌,
      (nerve E).δ 1 x = y₁ ∧ (nerve E).δ 2 x = y₂ ∧ (nerve E).δ 3 x = y₃ := by
  obtain ⟨_, _, _, p, q, rfl⟩ := ComposableArrows.mk₂_surjective y₁
  obtain ⟨_, _, _, r, s, rfl⟩ := ComposableArrows.mk₂_surjective y₂
  obtain ⟨_, _, _, f, g, rfl⟩ := ComposableArrows.mk₂_surjective y₃
  obtain ⟨_, _, _, _, c₀₁, c₁₂, c₂₃, rfl⟩ := ComposableArrows.mk₃_surjective z
  rw [δ₁_mk₂_eq, δ₁_mk₂_eq] at h₁₂
  rw [δ₂_mk₂_eq, δ₁_mk₂_eq] at h₁₃
  rw [δ₂_mk₂_eq, δ₂_mk₂_eq] at h₂₃
  rw [δ₂_mk₂_eq] at hφ
  -- The faces `δ 2` and `δ 3` share the edge `f = φ` from `0` to `1`, the faces `δ 1` and `δ 3`
  -- the edge `f ≫ g` from `0` to `2`, and the faces `δ 1` and `δ 2` the edge from `0` to `3`.
  obtain ⟨rfl, rfl, hr⟩ := (Arrow.mk_eq_mk_iff _ _).1 (ComposableArrows.mk₁_eq_mk₁_iff.1 h₂₃)
  obtain ⟨rfl, rfl, hp⟩ := (Arrow.mk_eq_mk_iff _ _).1 (ComposableArrows.mk₁_eq_mk₁_iff.1 h₁₃)
  obtain ⟨rfl, rfl, hf⟩ := (Arrow.mk_eq_mk_iff _ _).1 (ComposableArrows.mk₁_eq_mk₁_iff.1 hφ)
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hr hp hf
  subst f r p
  obtain ⟨_, rfl, hs⟩ := (Arrow.mk_eq_mk_iff _ _).1 (ComposableArrows.mk₁_eq_mk₁_iff.1 h₁₂)
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Category.assoc] at hs
  -- The images in `B` of the edges `s` from `1` to `3` and `g ≫ q` are both the edge `c₁₂ ≫ c₂₃`
  -- of `z`, read on the faces `δ 0` of the faces of `z`.
  have hzs := congrArg ((nerve B).δ 0) hz₂
  have hzg := congrArg ((nerve B).δ 0) hz₃
  have hzq := congrArg ((nerve B).δ 0) hz₁
  rw [δ₂_mk₃_eq, nerveMap_app_mk₂, δ₀_mk₂_eq, δ₀_mk₂_eq] at hzs
  rw [δ₃_mk₃_eq, nerveMap_app_mk₂, δ₀_mk₂_eq, δ₀_mk₂_eq] at hzg
  rw [δ₁_mk₃_eq, nerveMap_app_mk₂, δ₀_mk₂_eq, δ₀_mk₂_eq] at hzq
  obtain ⟨rfl, rfl, hc₁₂⟩ := (Arrow.mk_eq_mk_iff _ _).1 (ComposableArrows.mk₁_eq_mk₁_iff.1 hzg)
  obtain ⟨_, rfl, hc₂₃⟩ := (Arrow.mk_eq_mk_iff _ _).1 (ComposableArrows.mk₁_eq_mk₁_iff.1 hzq)
  obtain ⟨_, _, hc⟩ := (Arrow.mk_eq_mk_iff _ _).1 (ComposableArrows.mk₁_eq_mk₁_iff.1 hzs)
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hc₁₂ hc₂₃ hc
  subst hc₁₂ hc₂₃
  -- Two morphisms out of `b` over `F s` that agree after `φ` agree, so `s = g ≫ q`.
  have : F.IsHomLift (F.map s) (g ≫ q) := isHomLift_iff_map_eq.2 (by rw [F.map_comp, ← hc])
  obtain rfl : s = g ≫ q := IsStronglyCocartesian.ext F (F.map φ) φ (F.map s) hs.symm
  exact ⟨ComposableArrows.mk₃ φ g q, δ₁_mk₃_eq _ _ _, δ₂_mk₃_eq _ _ _, δ₃_mk₃_eq _ _ _⟩

/-- **Strongly coCartesian morphisms give coCartesian edges of nerves.** If `φ : a ⟶ b` is
strongly coCartesian for `F : E ⥤ B` over `f`, then the edge of the nerve of `E` given by `φ` is
coCartesian for the map of nerves `nerveMap F`. -/
theorem isCoCartesian_edgeMk_of_isStronglyCocartesian {R S : B} {a b : E} (f : R ⟶ S)
    (φ : a ⟶ b) [F.IsStronglyCocartesian f φ] : (edgeMk φ).IsCoCartesian (nerveMap F) := by
  obtain rfl := IsHomLift.domain_eq F f φ
  obtain rfl := IsHomLift.codomain_eq F f φ
  obtain rfl : F.map φ = f := (IsHomLift.eq_of_isHomLift F f φ).symm
  refine Edge.isCoCartesian_of_hornFilling_zero _ _ fun n σ₀ τ hσ₀ hτ ↦ ?_
  -- A simplex whose faces are those of `σ₀` fills `σ₀`.
  have of_faces (x : (nerve E) _⦋n + 2⦌)
      (hx : ∀ j (hj : j ≠ 0), (nerve E).δ j x = SSet.yonedaEquiv (horn.ι 0 j hj ≫ σ₀)) :
      Λ[n + 2, 0].ι ≫ SSet.yonedaEquiv.symm x = σ₀ :=
    horn.hom_ext' fun j hj ↦ by
      rw [horn.ι_ι_assoc, stdSimplex.δ_comp_yonedaEquiv_symm, hx j hj, Equiv.symm_apply_apply]
  -- The faces of `τ` are the images of the faces of `σ₀`.
  have base (j : Fin (n + 3)) (hj : j ≠ 0) : (nerve B).δ j (SSet.yonedaEquiv τ) =
      (nerveMap F).app _ (SSet.yonedaEquiv (horn.ι 0 j hj ≫ σ₀)) := by
    rw [← SSet.yonedaEquiv_comp, Category.assoc, hτ, horn.ι_ι_assoc, stdSimplex.yonedaEquiv_δ_comp]
  -- Two faces of `σ₀` agree on their common face.
  have compat (j k : Fin (n + 3)) (hj : j ≠ 0) (hk : k ≠ 0) (hjk : j < k) :=
    congrArg SSet.yonedaEquiv ((horn.IsCompatible.of_hom σ₀).δ_pred_comp j k hj hk hjk)
  simp only [stdSimplex.yonedaEquiv_δ_comp] at compat
  obtain _ | _ | m := n
  · -- Horns `Λ[2, 0]`: the face `δ 2` is the initial edge `φ`.
    have h₂ : SSet.yonedaEquiv (horn.ι 0 2 (by decide) ≫ σ₀) = (edgeMk φ).edge := by
      rw [SSet.yonedaEquiv_comp, ← hσ₀]
      congr 1
      exact Subtype.ext (stdSimplex.ext _ _ fun j ↦ by fin_cases j <;> rfl)
    obtain ⟨x, hx₁, hx₂, hx⟩ := exists_horn₂₀ F φ _
      ((compat 1 2 (by decide) (by decide) (by decide)).trans (by rw [h₂]; rfl)) _
      (base 1 (by decide)) ((base 2 (by decide)).trans (by rw [h₂]; rfl))
    refine ⟨SSet.yonedaEquiv.symm x, of_faces x fun j hj ↦ ?_,
      SSet.yonedaEquiv.injective (by rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, hx])⟩
    fin_cases j
    exacts [absurd rfl hj, hx₁, hx₂.trans h₂.symm]
  · -- Horns `Λ[3, 0]`: the edge from `0` to `1` of the face `δ 3` is the initial edge `φ`.
    have h₃ : (nerve E).δ 2 (SSet.yonedaEquiv (horn.ι 0 3 (by decide) ≫ σ₀)) =
        (edgeMk φ).edge := by
      rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, SSet.yonedaEquiv_comp, ← hσ₀]
      congr 1
      exact Subtype.ext (stdSimplex.ext _ _ fun j ↦ by fin_cases j <;> rfl)
    obtain ⟨x, hx₁, hx₂, hx₃⟩ := exists_horn₃₀ F φ _ _ _
      (compat 1 2 (by decide) (by decide) (by decide))
      (compat 1 3 (by decide) (by decide) (by decide))
      (compat 2 3 (by decide) (by decide) (by decide)) h₃ _
      (base 1 (by decide)) (base 2 (by decide)) (base 3 (by decide))
    have hσ := of_faces x fun j hj ↦ by
      fin_cases j
      exacts [absurd rfl hj, hx₁, hx₂, hx₃]
    exact ⟨_, hσ, IsStrictSegal.hom_ext_of_horn 0 (by rw [reassoc_of% hσ, hτ])⟩
  · -- Horns of dimension at least `4` are filled since the nerve is `2`-coskeletal, and the
    -- filler lies over `τ` since simplices of the nerve of `B` are determined by horns.
    obtain ⟨σ, hσ, -⟩ := existsUnique_horn_extension_of_isCoskeletal (k := 2) (by omega) 0 σ₀
    exact ⟨σ, hσ, IsStrictSegal.hom_ext_of_horn 0 (by rw [reassoc_of% hσ, hτ])⟩

end CategoryTheory.nerve

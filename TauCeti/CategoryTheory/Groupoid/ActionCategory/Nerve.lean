/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Map
public import TauCeti.Order.Fin.Induction

import TauCeti.Data.Fin.Basic

/-!
# Strings of composable arrows of an action category

For a monoid `G` acting on `X`, a string of `n` composable arrows `x₀ ⟶ x₁ ⟶ ⋯ ⟶ xₙ` of the
action category `CategoryTheory.ActionCategory G X` is determined by its first point `x₀` and the
labels `gₖ` of its consecutive arrows, with `xₖ₊₁ = gₖ • xₖ`. This file proves the facts about
labels along a string behind this description, and the resulting bijection
`TauCeti.ActionGroupoid.nerveEquiv` between the `n`-simplices of the nerve and `X × Gⁿ`. Every
label is retained, including labels acting trivially.

For an invariant subset `U`, a string of `G ⋉ X` comes from the full subcategory `G ⋉ U`
exactly when its first point lies in `U`
(`TauCeti.ActionGroupoid.range_mapComposableArrows_obj_restrict`).

In these coordinates the label of the arrow from the first point to the `i`-th one is
`TauCeti.ActionGroupoid.vertexLabel g i = gᵢ₋₁ ⋯ g₀`. For a group action, every map
`θ : {0, …, m} → {0, …, n}`, monotone or not, acts on strings by restriction to the points
`x_{θ 0}, …, x_{θ m}` (`TauCeti.ActionGroupoid.nerveMap`, contravariantly functorial by
`TauCeti.ActionGroupoid.nerveMap_nerveMap`). For monotone `θ` this is the simplicial operator of the
nerve (`TauCeti.ActionGroupoid.nerveEquiv_whiskerLeft`). Corepresenting these operators gives the
cobar complex of a Hopf algebroid.

For a group action, all points of a string lie in one orbit
(`CategoryTheory.ComposableArrows.quotient_mk_back_obj`).

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112,
  Section 3.
-/

public noncomputable section

open CategoryTheory CategoryTheory.ActionCategory

section Monoid

variable {G X : Type*} [Monoid G] [MulAction G X] {n : ℕ}

namespace CategoryTheory.ComposableArrows

/-- In a string of composable arrows of an action category, the arrow from the `i`-th object to
itself has label `1`. -/
theorem hom_map_homOfLE_refl (F : ComposableArrows (ActionCategory G X) n)
    (i : Fin (n + 1)) : (F.map (homOfLE (le_refl i))).hom = (1 : G) := by
  simp

/-- In a string of composable arrows of an action category, the label of the arrow from the `i`-th
to the `(k + 1)`-th object is the `k`-th consecutive label times the label of the arrow from the
`i`-th to the `k`-th object. -/
theorem hom_map_homOfLE_succ (F : ComposableArrows (ActionCategory G X) n)
    {i : Fin (n + 1)} {k : Fin n} (hik : i ≤ k.castSucc) :
    (F.map (homOfLE (hik.trans k.castSucc_le_succ))).hom =
      ((F.map (homOfLE k.castSucc_le_succ)).hom : G) * (F.map (homOfLE hik)).hom := by
  rw [← homOfLE_comp, F.map_comp, ActionCategory.comp_hom]

/-- The point underlying the `i`-th object of a string of composable arrows of an action category
is the label of the arrow from the first object, applied to the first point. -/
theorem back_obj_eq_smul (F : ComposableArrows (ActionCategory G X) n) (i : Fin (n + 1)) :
    (F.obj i).back = ((F.map (homOfLE (Fin.zero_le i))).hom : G) • (F.obj 0).back :=
  (F.map (homOfLE (Fin.zero_le i))).map_val.symm

/-- Two strings of composable arrows of an action category with the same first point and the
same consecutive labels are equal. -/
theorem ext_of_back_obj_zero_of_hom_map {F F' : ComposableArrows (ActionCategory G X) n}
    (h₀ : (F.obj 0).back = (F'.obj 0).back)
    (h : ∀ k : Fin n, (F.map (homOfLE k.castSucc_le_succ)).hom =
      ((F'.map (homOfLE k.castSucc_le_succ)).hom : G)) : F = F' := by
  have hlabel : ∀ i j (hij : i ≤ j),
      (F.map (homOfLE hij)).hom = ((F'.map (homOfLE hij)).hom : G) :=
    Fin.le_induction_castSucc (fun i ↦ by rw [hom_map_homOfLE_refl F, hom_map_homOfLE_refl F'])
      fun i k hik ih ↦ by rw [hom_map_homOfLE_succ F hik, hom_map_homOfLE_succ F' hik, ih, h]
  have hobj (i : Fin (n + 1)) : F.obj i = F'.obj i := by
    rw [← back_coe (F.obj i), ← back_coe (F'.obj i), back_obj_eq_smul F i, back_obj_eq_smul F' i,
      h₀, hlabel]
  refine ComposableArrows.ext hobj fun i hi ↦ Functor.Elements.Hom.ext ?_
  simp only [ComposableArrows.map', ActionCategory.comp_hom, eqToHom_hom, one_mul, mul_one]
  exact hlabel _ _ _

/-- The consecutive labels of a string built by `ComposableArrows.mkOfObjOfMapSucc` are the labels
of the given arrows. -/
theorem hom_map_mkOfObjOfMapSucc (obj : Fin (n + 1) → ActionCategory G X)
    (mapSucc : ∀ k : Fin n, obj k.castSucc ⟶ obj k.succ) (k : Fin n) :
    ((ComposableArrows.mkOfObjOfMapSucc obj mapSucc).map (homOfLE k.castSucc_le_succ)).hom =
      ((mapSucc k).hom : G) :=
  congrArg (fun f ↦ Functor.Elements.Hom.hom f)
    (ComposableArrows.mkOfObjOfMapSucc_map_succ obj mapSucc k.1 k.2)

end CategoryTheory.ComposableArrows

namespace TauCeti.ActionGroupoid

/-- The label `gᵢ₋₁ ⋯ g₀` of the arrow from the first to the `i`-th point of the string with
consecutive labels `g`: the partial product of the labels in the opposite monoid, since later
labels act last. -/
def vertexLabel (g : Fin n → G) (i : Fin (n + 1)) : G :=
  (Fin.partialProd (fun k ↦ MulOpposite.op (g k)) i).unop

@[simp]
theorem vertexLabel_zero (g : Fin n → G) : vertexLabel g 0 = 1 := by
  simp [vertexLabel]

@[simp]
theorem vertexLabel_succ (g : Fin n → G) (k : Fin n) :
    vertexLabel g k.succ = g k * vertexLabel g k.castSucc := by
  simp [vertexLabel, Fin.partialProd_succ]

/-- The arrow to the second point of a string is its first arrow. -/
@[simp]
theorem vertexLabel_one (g : Fin (n + 1) → G) : vertexLabel g 1 = g 0 := by
  simpa using vertexLabel_succ g 0

/-- The arrow to the third point of a string is the composite of its first two arrows. -/
@[simp]
theorem vertexLabel_two (g : Fin (n + 2) → G) : vertexLabel g 2 = g 1 * g 0 := by
  simpa using vertexLabel_succ g 1

/-- Appending an arrow to a string does not change the labels of its earlier points. -/
@[simp]
theorem vertexLabel_snoc_castSucc (g : Fin n → G) (h : G) (i : Fin (n + 1)) :
    vertexLabel (Fin.snoc g h : Fin (n + 1) → G) i.castSucc = vertexLabel g i := by
  rw [vertexLabel, vertexLabel, ← Fin.partialProd_init]
  congr
  ext k
  simp [Fin.init]

/-- Applying a monoid homomorphism to the consecutive labels applies it to the labels of the
points. -/
@[simp]
theorem vertexLabel_comp {H : Type*} [Monoid H] (φ : G →* H) (g : Fin n → G) (i : Fin (n + 1)) :
    vertexLabel (φ ∘ g) i = φ (vertexLabel g i) :=
  congrArg MulOpposite.unop (Fin.map_partialProd φ.op (fun k ↦ MulOpposite.op (g k)) i).symm

variable (G X n) in
/-- The `n`-simplices of the nerve of an action category correspond to `X × Gⁿ`, by recording the
first point and the labels of the consecutive arrows of a string. The string with first point `x`
and labels `g` has `k`-th point `gₖ₋₁ ⋯ g₀ • x`. -/
def nerveEquiv : ComposableArrows (ActionCategory G X) n ≃ X × (Fin n → G) where
  toFun F := ((F.obj 0).back, fun k ↦ (F.map (homOfLE k.castSucc_le_succ)).hom)
  invFun p := ComposableArrows.mkOfObjOfMapSucc (fun i ↦ (vertexLabel p.2 i • p.1 : X))
    -- The side condition of `homMk` in an action category is `g • x = y` by definition, as in
    -- `ActionCategory.nonempty_hom_iff`.
    fun k ↦ Functor.Elements.homMk (p.2 k)
      (show p.2 k • (vertexLabel p.2 k.castSucc • p.1) = vertexLabel p.2 k.succ • p.1 by
        rw [vertexLabel_succ, mul_smul])
  left_inv F := ComposableArrows.ext_of_back_obj_zero_of_hom_map
    (by simp [ComposableArrows.mkOfObjOfMapSucc_obj]) fun k ↦ by
      rw [ComposableArrows.hom_map_mkOfObjOfMapSucc]
  right_inv p := Prod.ext (by simp [ComposableArrows.mkOfObjOfMapSucc_obj]) <| funext fun k ↦ by
    dsimp only
    rw [ComposableArrows.hom_map_mkOfObjOfMapSucc]

@[simp]
theorem nerveEquiv_apply (F : ComposableArrows (ActionCategory G X) n) :
    nerveEquiv G X n F = ((F.obj 0).back, fun k ↦ (F.map (homOfLE k.castSucc_le_succ)).hom) :=
  (rfl)

/-- The `i`-th point of the string with first point `x` and consecutive labels `g` is
`gᵢ₋₁ ⋯ g₀ • x`. -/
@[simp]
theorem back_obj_nerveEquiv_symm (p : X × (Fin n → G)) (i : Fin (n + 1)) :
    (((nerveEquiv G X n).symm p).obj i).back = vertexLabel p.2 i • p.1 := (rfl)

/-- The `k`-th consecutive label of the string with first point `x` and consecutive labels `g` is
`gₖ`. -/
@[simp]
theorem label_nerveEquiv_symm (p : X × (Fin n → G)) (k : Fin n) :
    ((((nerveEquiv G X n).symm p).map (homOfLE k.castSucc_le_succ)).hom : G) = p.2 k :=
  congrFun (congrArg Prod.snd ((nerveEquiv G X n).apply_symm_apply p)) k

/-- A string of composable arrows of `G ⋉ X` comes from `G ⋉ U` exactly when its first vertex lies
in the invariant subset `U`. -/
theorem range_mapComposableArrows_obj_restrict (U : SubMulAction G X) (n : ℕ) :
    Set.range ((restrict U).mapComposableArrows n).obj = {F | (F.obj 0).back ∈ U} := by
  ext F
  refine ⟨?_, fun hF => ?_⟩
  · rintro ⟨F', rfl⟩
    simp
  · -- Every vertex is a translate of the first one, so it lies in `U` as well.
    have hF' (i : Fin (n + 1)) : (F.obj i).back ∈ U :=
      F.back_obj_eq_smul i ▸ U.smul_mem _ hF
    exact ⟨restrictLift U F hF', restrictLift_comp_restrict U F hF'⟩

/-- In a string of composable arrows, the arrow from the first to the `i`-th point has label
`vertexLabel` of the consecutive labels. -/
theorem hom_map_homOfLE_zero_le (F : ComposableArrows (ActionCategory G X) n) (i : Fin (n + 1)) :
    (F.map (homOfLE (Fin.zero_le i))).hom = vertexLabel (nerveEquiv G X n F).2 i := by
  induction i using Fin.induction with
  | zero => exact F.hom_map_homOfLE_refl 0
  | succ i ih =>
    rw [vertexLabel_succ, ← ih]
    exact F.hom_map_homOfLE_succ (Fin.zero_le _)

end TauCeti.ActionGroupoid

end Monoid

section Group

variable {G X : Type*} [Group G] [MulAction G X] {n : ℕ}

namespace CategoryTheory.ComposableArrows

/-- All points of a string of composable arrows of an action groupoid lie in one orbit. -/
theorem quotient_mk_back_obj (F : ComposableArrows (ActionCategory G X) n) (i : Fin (n + 1)) :
    (⟦(F.obj i).back⟧ : MulAction.orbitRel.Quotient G X) = ⟦(F.obj 0).back⟧ := by
  rw [back_obj_eq_smul F i, MulAction.orbitRel.Quotient.quotient_smul_eq]

end CategoryTheory.ComposableArrows

namespace TauCeti.ActionGroupoid

/-- The action of `θ : {0, …, m} → {0, …, n}` on `n`-simplices of the nerve of an action
groupoid, in the coordinates of `nerveEquiv`: the string with first point `x` and consecutive
labels `g` is sent to the string of its points `x_{θ 0}, …, x_{θ m}`, whose `j`-th arrow is the
arrow from `x_{θ j}` to `x_{θ (j + 1)}`. Every arrow is invertible, so `θ` need not be monotone;
for monotone `θ` this is the simplicial operator of the nerve (`nerveEquiv_whiskerLeft`). -/
def nerveMap {m : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) (x : X × (Fin n → G)) : X × (Fin m → G) :=
  (vertexLabel x.2 (θ 0) • x.1,
    fun j ↦ vertexLabel x.2 (θ j.succ) * (vertexLabel x.2 (θ j.castSucc))⁻¹)

@[simp]
theorem nerveMap_fst {m : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) (x : X × (Fin n → G)) :
    (nerveMap θ x).1 = vertexLabel x.2 (θ 0) • x.1 :=
  (rfl)

@[simp]
theorem nerveMap_snd {m : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) (x : X × (Fin n → G)) (j : Fin m) :
    (nerveMap θ x).2 j = vertexLabel x.2 (θ j.succ) * (vertexLabel x.2 (θ j.castSucc))⁻¹ :=
  (rfl)

/-- The labels of the points of the restricted string, as arrows from its first point
`x_{θ 0}`. -/
@[simp]
theorem vertexLabel_nerveMap {m : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) (x : X × (Fin n → G))
    (j : Fin (m + 1)) :
    vertexLabel (nerveMap θ x).2 j = vertexLabel x.2 (θ j) * (vertexLabel x.2 (θ 0))⁻¹ := by
  induction j using Fin.induction with
  | zero => simp
  | succ j ih => simp [ih, mul_assoc]

/-- Restriction along the identity is the identity. -/
@[simp]
theorem nerveMap_id (x : X × (Fin n → G)) : nerveMap id x = x := by
  ext <;> simp

/-- Restriction is contravariantly functorial: restricting along `θ` and then along `ψ` is
restricting along `θ ∘ ψ`. -/
@[simp]
theorem nerveMap_nerveMap {l m : ℕ} (θ : Fin (m + 1) → Fin (n + 1))
    (ψ : Fin (l + 1) → Fin (m + 1)) (x : X × (Fin n → G)) :
    nerveMap ψ (nerveMap θ x) = nerveMap (θ ∘ ψ) x := by
  refine Prod.ext ?_ (funext fun j ↦ ?_)
  · simp [smul_smul]
  · simp [mul_assoc]

/-- Restriction commutes with equivariant maps of actions. -/
theorem nerveMap_map {m : ℕ} {H Y : Type*} [Group H] [MulAction H Y]
    (θ : Fin (m + 1) → Fin (n + 1)) (φ : G →* H) (f : X → Y)
    (hf : ∀ (g : G) (x : X), f (g • x) = φ g • f x) (x : X × (Fin n → G)) :
    nerveMap θ (f x.1, φ ∘ x.2) = (f (nerveMap θ x).1, φ ∘ (nerveMap θ x).2) := by
  refine Prod.ext ?_ (funext fun j ↦ ?_)
  · simp [hf]
  · simp

/-- For a monotone `θ`, `nerveMap θ` is the simplicial operator of the nerve: precomposing a
string of composable arrows with `θ`. -/
theorem nerveEquiv_whiskerLeft {m : ℕ} {θ : Fin (m + 1) → Fin (n + 1)} (hθ : Monotone θ)
    (F : ComposableArrows (ActionCategory G X) n) :
    nerveEquiv G X m (F.whiskerLeft hθ.functor) = nerveMap θ (nerveEquiv G X n F) := by
  -- Every label in `F` is the label to its target from the first point times the inverse of the
  -- label to its source.
  have hlabel {i j : Fin (n + 1)} (hij : i ≤ j) : (F.map (homOfLE hij)).hom =
      vertexLabel (nerveEquiv G X n F).2 j * (vertexLabel (nerveEquiv G X n F).2 i)⁻¹ := by
    rw [← hom_map_homOfLE_zero_le F i, ← hom_map_homOfLE_zero_le F j,
      ← homOfLE_comp (Fin.zero_le i) hij, F.map_comp, ActionCategory.comp_hom,
      mul_inv_cancel_right]
  -- The points and arrows of `F.whiskerLeft hθ.functor` are those of `F` at `θ 0, …, θ m`.
  refine Prod.ext ?_ (funext fun j ↦ ?_)
  · rw [nerveMap_fst, ← hom_map_homOfLE_zero_le F]
    simp only [nerveEquiv_apply, ComposableArrows.whiskerLeft_obj, Monotone.functor_obj]
    exact F.back_obj_eq_smul (θ 0)
  · rw [nerveMap_snd, ← hlabel (hθ j.castSucc_le_succ)]
    simp only [nerveEquiv_apply, ComposableArrows.whiskerLeft_map, Monotone.functor_map_homOfLE]

end TauCeti.ActionGroupoid

end Group

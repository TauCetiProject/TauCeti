/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import Mathlib.AlgebraicTopology.Quasicategory.StrictSegal
public import TauCeti.AlgebraicTopology.SimplicialSet.BoundaryColimits
public import TauCeti.AlgebraicTopology.SimplicialSet.Colimits
public import TauCeti.AlgebraicTopology.SimplicialSet.Truncated

/-!
# Strict Segal simplicial sets

In a strict Segal simplicial set, such as the nerve of a category, a simplex is determined by its
spine (Mathlib's `SSet.IsStrictSegal`), so it is determined by its simplices of dimension at most
two. This file records consequences of this.

A simplicial operator fixes a simplex as soon as it fixes every edge of its spine. Since every
inner horn contains the spine of the standard simplex, a map from a standard simplex to a strict
Segal simplicial set is determined by its restriction to an inner horn, so any map from a
quasicategory to a strict Segal simplicial set is an inner fibration. In particular the nerve of
every functor is an inner fibration. The inner horn containing the spine is Mathlib's
`SSet.horn.spineId`, as in Mathlib's proof `SSet.StrictSegal.quasicategory` that strict Segal
simplicial sets are quasicategories.

A simplex of dimension at least two is determined by its first and last faces, which together
contain its spine. Every map from the boundary `∂Δ[n]` with `n ≥ 3` extends to `Δ[n]`: fill the
inner horn `Λ[n, 1]` and observe that the missing face is forced by the others. In dimensions one
and two this fails in general: two vertices need not be joined by an edge, and the third edge of
the boundary of a triangle need not be the composite of the other two.

An `(n + 1)`-simplex of a strict Segal simplicial set is the same as its first edge together with
its face opposite to the vertex `0`, glued along a vertex: this is Mathlib's
`SSet.StrictSegalCore`, which conversely characterizes strict Segal simplicial sets
(`SSet.StrictSegal.ofCore`). This condition involves only one edge, one simplex and one equation,
which in a filtered colimit all come from a common stage. Hence a filtered colimit of strict Segal
simplicial sets is strict Segal; applied to nerves, this shows that the nerve commutes with
filtered colimits of categories.

For truncated simplicial sets, a morphism between strict Segal ones that is bijective on edges is
an isomorphism, since simplices correspond to their spines.

## Main results

* `SSet.map_eq_of_isStrictSegal`: an `(n + 1)`-simplex whose face opposite to the last vertex is
  constant at a vertex is fixed by any operator that fixes its last edge.
* `SSet.IsStrictSegal.of_iso`: the strict Segal condition is invariant under isomorphism; in
  particular the standard simplices, being isomorphic to nerves of finite linear orders, are
  strict Segal (`SSet.stdSimplex.isStrictSegal`).
* `SSet.IsStrictSegal.hom_ext_of_innerHorn`: maps from `Δ[n + 2]` to a strict Segal simplicial
  set agree as soon as they agree on an inner horn.
* `SSet.IsStrictSegal.hom_ext_of_horn`: maps from `Δ[n + 3]` to a strict Segal simplicial set agree
  as soon as they agree on any horn.
* `SSet.innerFibration_of_isStrictSegal`: a map from a quasicategory to a strict Segal simplicial
  set is an inner fibration.
* `SSet.IsStrictSegal.ext_of_δ_zero_of_δ_last`: a simplex of dimension at least two is determined
  by its first and last faces.
* `SSet.IsStrictSegal.exists_boundary_extension`: every map `∂Δ[n + 3] ⟶ X` extends to
  `Δ[n + 3]`.
* `SSet.Edge.CompStruct.eq_of_isStrictSegal`: in a strict Segal simplicial set, the edge `e₀₂` of
  a `CompStruct e₀₁ e₁₂ e₀₂` is determined by the spine edges `e₀₁` and `e₁₂`.
* `SSet.StrictSegal.core`: a strict Segal structure gives `SSet.StrictSegalCore` in every
  dimension.
* `SSet.IsStrictSegal.of_isColimit`: a filtered colimit of strict Segal simplicial sets is strict
  Segal, for diagrams of any size.
* `SSet.Truncated.isIso_of_bijective_app_one`: a morphism of strict Segal truncated simplicial sets
  that is bijective on edges is an isomorphism.
-/

public section

open CategoryTheory Limits Opposite Simplicial SimplexCategory

universe u

namespace SSet

variable {X : SSet.{u}} [X.IsStrictSegal]

/-- Two maps from `Δ[n + 2]` to a strict Segal simplicial set agree as soon as they agree on an
inner horn: the inner horn contains the spine of `Δ[n + 2]`. -/
theorem IsStrictSegal.hom_ext_of_innerHorn {n : ℕ} {i : Fin (n + 3)} (h₀ : 0 < i)
    (hₙ : i < Fin.last (n + 2)) {f g : Δ[n + 2] ⟶ X}
    (h : Λ[n + 2, i].ι ≫ f = Λ[n + 2, i].ι ≫ g) : f = g := by
  have key (f : Δ[n + 2] ⟶ X) :
      X.spine (n + 2) (yonedaEquiv f) = (horn.spineId i h₀ hₙ).map (Λ[n + 2, i].ι ≫ f) := by
    ext k
    rw [spine_arrow, yonedaEquiv_naturality, yonedaEquiv_comp]
    -- Both sides are the image under `f` of the edge `mkOfSucc k` of `Δ[n + 2]`.
    rfl
  exact yonedaEquiv.injective ((IsStrictSegal.segal (n + 2)).injective (by rw [key, key, h]))

/-- Two maps from `Δ[n + 3]` to a strict Segal simplicial set agree as soon as they agree on a
horn, inner or outer: in dimension at least `3`, every horn contains every edge of `Δ[n + 3]`, so
in particular the spine. -/
theorem IsStrictSegal.hom_ext_of_horn {n : ℕ} (i : Fin (n + 4)) {f g : Δ[n + 3] ⟶ X}
    (h : Λ[n + 3, i].ι ≫ f = Λ[n + 3, i].ι ≫ g) : f = g := by
  have key (f : Δ[n + 3] ⟶ X) (k : Fin (n + 3)) :
      (X.spine (n + 3) (yonedaEquiv f)).arrow k = (Λ[n + 3, i].ι ≫ f).app _
        (horn.edge (n + 3) i k.castSucc k.succ (Fin.castSucc_le_succ k)
          (Finset.card_le_three.trans (by omega))) := by
    rw [spine_arrow, yonedaEquiv_naturality, yonedaEquiv_comp, NatTrans.comp_app_apply]
    -- Both sides are the image under `f` of the edge `mkOfSucc k` of `Δ[n + 3]`.
    congr 1
    refine stdSimplex.ext _ _ fun j ↦ ?_
    fin_cases j <;> rfl
  exact yonedaEquiv.injective ((IsStrictSegal.segal (n + 3)).injective
    (Path.ext' fun k ↦ by rw [key, key, h]))

/-- A map from a quasicategory to a strict Segal simplicial set is an inner fibration: inner horns
fill in the source, and the filler lies over the given simplex because simplices of the target
are determined by their restrictions to inner horns. -/
instance innerFibration_of_isStrictSegal {W : SSet.{u}} [Quasicategory W] (p : W ⟶ X) :
    InnerFibration p where
  mem _ _ _ := fun ⟨_, h₀, hₙ⟩ ↦ ⟨fun {a _} sq ↦ by
    obtain ⟨σ, hσ⟩ := Quasicategory.hornFilling h₀ hₙ a
    refine ⟨⟨{ l := σ
               fac_left := hσ.symm
               fac_right := IsStrictSegal.hom_ext_of_innerHorn h₀ hₙ ?_ }⟩⟩
    rw [← Category.assoc, ← hσ, sq.w]⟩

/-- In a strict Segal simplicial set, an `(n + 1)`-simplex whose face opposite to the last vertex
is constant at `x` is fixed by any operator `r` that fixes the last edge. -/
theorem map_eq_of_isStrictSegal {n : ℕ} (r : ⦋n + 1⦌ ⟶ ⦋n + 1⦌)
    (hlast : mkOfSucc (Fin.last n) ≫ r = mkOfSucc (Fin.last n))
    {x : X _⦋0⦌} (σ : X _⦋n + 1⦌)
    (hσ : X.δ (Fin.last (n + 1)) σ = X.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op x) :
    X.map r.op σ = σ := by
  -- Every edge missing the last vertex lies in the face opposite to it, which is constant at `x`.
  have hedge (f : ⦋1⦌ ⟶ ⦋n + 1⦌) (hf : ∀ a, f a ≠ Fin.last (n + 1)) :
      X.map f.op σ = X.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op x := by
    rw [← SimplexCategory.factor_δ_spec f (Fin.last (n + 1)) hf, op_comp, Functor.map_comp_apply]
    -- `X.δ i σ` is by definition `X.map (δ i).op σ`, so the face of `σ` appears syntactically
    change X.map _ (X.δ _ σ) = _
    rw [hσ, ← Functor.map_comp_apply, ← op_comp,
      Subsingleton.elim (SimplexCategory.factor_δ f (Fin.last (n + 1)) ≫ _)]
  refine (IsStrictSegal.segal (X := X) (n + 1)).injective (Path.ext' fun i ↦ ?_)
  rw [spine_arrow, spine_arrow, ← Functor.map_comp_apply, ← op_comp]
  cases i using Fin.lastCases with
  | last => rw [hlast]
  | cast j =>
    have hr : r.toOrderHom (Fin.last n).castSucc = (Fin.last n).castSucc :=
      congrArg (fun φ : ⦋1⦌ ⟶ ⦋n + 1⦌ => φ.toOrderHom 0) hlast
    have hlt (a : Fin (n + 2)) (ha : a ≤ (Fin.last n).castSucc) :
        r.toOrderHom a ≠ Fin.last (n + 1) :=
      ((r.toOrderHom.monotone ha).trans_eq hr).trans_lt (Fin.castSucc_lt_last _) |>.ne
    have hle (a : Fin 2) : mkOfSucc j.castSucc a ≤ (Fin.last n).castSucc := by
      fin_cases a
      -- the two vertices of `mkOfSucc i` are `i.castSucc` and `i.succ`
      -- (`SimplexCategory.mkOfSucc_homToOrderHom_zero`, `_one`, both `rfl`)
      · change j.castSucc.castSucc ≤ _
        rw [Fin.le_def]; simp
      · change j.castSucc.succ ≤ _
        rw [Fin.le_def]; simp
    rw [hedge _ fun a => hlt _ (hle a),
      hedge _ fun a => ((hle a).trans_lt (Fin.castSucc_lt_last _)).ne]

/-- The strict Segal condition is invariant under isomorphism: an isomorphism `X ≅ Y` matches the
spines of the simplices of `X` and of `Y`. -/
theorem IsStrictSegal.of_iso {Y : SSet.{u}} (e : X ≅ Y) : Y.IsStrictSegal where
  segal n := by
    have h : Y.spine n = (fun p ↦ p.map e.hom) ∘ X.spine n ∘ e.inv.app _ := by
      funext y
      ext <;> simp [Path.map_vertex, Path.map_arrow]
    rw [h]
    refine Function.Bijective.comp ?_ ((IsStrictSegal.segal n).comp ?_)
    · refine Function.bijective_iff_has_inverse.2 ⟨fun p ↦ p.map e.inv, fun p ↦ ?_, fun p ↦ ?_⟩
      all_goals ext <;> simp [Path.map_vertex, Path.map_arrow]
    · exact (isIso_iff_bijective _).1 inferInstance

/-- Standard simplices are strict Segal, being isomorphic to nerves of finite linear orders. -/
instance stdSimplex.isStrictSegal (n : ℕ) : (Δ[n] : SSet.{u}).IsStrictSegal :=
  .of_iso (stdSimplex.isoNerve n).symm

namespace IsStrictSegal

/-- In a strict Segal simplicial set, a simplex of dimension at least two is determined by its
first and last faces, which together contain its spine. -/
lemma ext_of_δ_zero_of_δ_last {n : ℕ} {x y : X _⦋n + 2⦌}
    (h₀ : X.δ 0 x = X.δ 0 y) (hl : X.δ (Fin.last _) x = X.δ (Fin.last _) y) : x = y := by
  have sx := StrictSegal.ofIsStrictSegal X
  apply (IsStrictSegal.segal (X := X) _).injective
  refine Path.ext' fun i ↦ ?_
  obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
  · have hx := sx.spine_δ_arrow_lt (X.spine _ x) (i := i) (j := Fin.last _)
      (Fin.lt_def.2 (by simp; omega))
    have hy := sx.spine_δ_arrow_lt (X.spine _ y) (i := i) (j := Fin.last _)
      (Fin.lt_def.2 (by simp; omega))
    simp only [StrictSegal.spineToSimplex_spine_apply] at hx hy
    exact hx.symm.trans ((congrArg (fun z ↦ (X.spine _ z).arrow i) hl).trans hy)
  · have hx := sx.spine_δ_arrow_gt (X.spine _ x) (i := Fin.last n) (j := 0)
      (Fin.lt_def.2 (by simp))
    have hy := sx.spine_δ_arrow_gt (X.spine _ y) (i := Fin.last n) (j := 0)
      (Fin.lt_def.2 (by simp))
    simp only [StrictSegal.spineToSimplex_spine_apply] at hx hy
    rw [← Fin.succ_last]
    exact hx.symm.trans ((congrArg (fun z ↦ (X.spine _ z).arrow (Fin.last n)) h₀).trans hy)

/-- In a strict Segal simplicial set, every map from the boundary `∂Δ[n + 3]` extends to
`Δ[n + 3]`. -/
lemma exists_boundary_extension {n : ℕ} (σ₀ : (∂Δ[n + 3] : SSet) ⟶ X) :
    ∃ σ : Δ[n + 3] ⟶ X, σ₀ = ∂Δ[n + 3].ι ≫ σ := by
  have hΛ : Λ[n + 3, 1] ≤ ∂Δ[n + 3] := by
    rw [horn_eq_iSup, boundary_eq_iSup]
    exact iSup_le fun j ↦ le_iSup (fun k : Fin (n + 4) ↦ stdSimplex.face {k}ᶜ) j.val
  obtain ⟨σ, hσ⟩ := Quasicategory.hornFilling (n := n + 3) (i := 1) (Fin.lt_def.2 (by simp))
    (Fin.lt_def.2 (by simp)) (Subcomplex.homOfLE hΛ ≫ σ₀)
  refine ⟨σ, ?_⟩
  -- The faces of `σ₀` and of the restriction of `σ` agree away from the face `1`.
  have hface (j : Fin (n + 4)) (hj : j ≠ 1) : boundary.ι j ≫ σ₀ = stdSimplex.δ j ≫ σ := by
    have : boundary.ι j = horn.ι 1 j hj ≫ Subcomplex.homOfLE hΛ := by
      rw [← cancel_mono (∂Δ[n + 3]).ι]
      simp
    rw [this, Category.assoc, hσ, horn.ι_ι_assoc]
  have h01 : (0 : Fin (n + 4)) < 1 := Fin.lt_def.2 (by simp)
  have h1l : (1 : Fin (n + 4)) < Fin.last _ := Fin.lt_def.2 (by simp)
  have h₀ := (boundary.IsCompatible.of_hom σ₀).δ_pred_comp 0 1 h01
  have hl := (boundary.IsCompatible.of_hom σ₀).δ_pred_comp 1 (Fin.last _) h1l
  have h₀' := (boundary.IsCompatible.of_hom (∂Δ[n + 3].ι ≫ σ)).δ_pred_comp 0 1 h01
  have hl' := (boundary.IsCompatible.of_hom (∂Δ[n + 3].ι ≫ σ)).δ_pred_comp 1 (Fin.last _) h1l
  simp only [boundary.ι_ι_assoc] at h₀' hl'
  refine boundary.hom_ext fun j ↦ ?_
  by_cases hj : j = 1
  · subst hj
    rw [boundary.ι_ι_assoc]
    -- The remaining face is determined by its first and last faces.
    apply yonedaEquiv.injective
    apply ext_of_δ_zero_of_δ_last
    · rw [← stdSimplex.yonedaEquiv_δ_comp, ← stdSimplex.yonedaEquiv_δ_comp]
      congr 1
      simp only [Fin.castPred_zero] at h₀ h₀'
      rw [← h₀, ← h₀', hface 0 (by simp)]
    · rw [← stdSimplex.yonedaEquiv_δ_comp, ← stdSimplex.yonedaEquiv_δ_comp]
      congr 1
      rw [hface (Fin.last _) (by simp [Fin.ext_iff])] at hl
      simpa only [Fin.pred_last] using hl.trans hl'.symm
  · rw [hface j hj, boundary.ι_ι_assoc]

end IsStrictSegal

end SSet

namespace SSet

section Core

variable {X : SSet.{u}}

/-- The path obtained by prepending an edge `e` to a path `p` that starts at the target of `e`. -/
def Path.cons {n : ℕ} (e : X _⦋1⦌) (p : X.Path n) (h : X.δ 0 e = p.vertex 0) :
    X.Path (n + 1) where
  vertex := Fin.cons (X.δ 1 e) p.vertex
  arrow := Fin.cons e p.arrow
  arrow_src i := by
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact p.arrow_src i
  arrow_tgt i := by
    cases i using Fin.cases with
    | zero => exact h
    | succ i => exact p.arrow_tgt i

section

variable {n : ℕ} (e : X _⦋1⦌) (p : X.Path n) (h : X.δ 0 e = p.vertex 0)

@[simp]
lemma Path.cons_vertex_zero : (p.cons e h).vertex 0 = X.δ 1 e := (rfl)

@[simp]
lemma Path.cons_vertex_succ (i : Fin (n + 1)) : (p.cons e h).vertex i.succ = p.vertex i := (rfl)

@[simp]
lemma Path.cons_arrow_zero : (p.cons e h).arrow 0 = e := (rfl)

@[simp]
lemma Path.cons_arrow_succ (i : Fin n) : (p.cons e h).arrow i.succ = p.arrow i := (rfl)

/-- Removing the first edge of `p.cons e h` recovers `p`. -/
@[simp]
lemma Path.cons_interval : (p.cons e h).interval 1 n = p := by
  cases n with
  | zero => exact Path.ext₀ ((p.cons e h).arrow_tgt 0 |>.symm.trans h)
  | succ n =>
    ext k
    rw [Path.arrow_interval _ 1 (n + 1) k k.succ, Path.cons_arrow_succ]

end

/-- The edges of the spine of an `(n + 1)`-simplex after the first one are the edges of the spine
of its face opposite to the vertex `0`. -/
lemma spine_arrow_succ {n : ℕ} (x : X _⦋n + 1⦌) (i : Fin n) :
    (X.spine (n + 1) x).arrow i.succ = (X.spine n (X.δ 0 x)).arrow i := by
  rw [spine_δ₀, Path.arrow_interval _ 1 n i i.succ]

/-- A strict Segal structure gives, in each dimension, Mathlib's `SSet.StrictSegalCore`: an
`(n + 1)`-simplex is the same as its first edge together with its face opposite to the vertex `0`,
glued along a vertex. This is a converse to `SSet.StrictSegal.ofCore`. -/
noncomputable def StrictSegal.core (sx : X.StrictSegal) (n : ℕ) : X.StrictSegalCore n where
  concat e s h := sx.spineToSimplex ((X.spine n s).cons e (h.trans (X.spine_vertex n s 0).symm))
  map_mkOfSucc_zero_concat e s h := by
    rw [← spine_arrow, StrictSegal.spine_spineToSimplex_apply, Path.cons_arrow_zero]
  δ₀_concat e s h := by
    apply sx.spineInjective
    -- `spineEquiv` is `spine` by definition; `spine_δ₀` is stated for `spine`
    change X.spine n _ = X.spine n s
    rw [spine_δ₀, StrictSegal.spine_spineToSimplex_apply, Path.cons_interval]
  injective {x y} h h₀ := by
    apply sx.spineInjective
    -- `spineEquiv` is `spine` by definition; `spine_arrow_succ` is stated for `spine`
    change X.spine _ x = X.spine _ y
    ext i
    cases i using Fin.cases with
    | zero => exact h
    | succ i => rw [spine_arrow_succ, spine_arrow_succ, h₀]

/-- The simplex `(sx.core n).concat e s h` is the simplex whose spine is `e` followed by the spine
of `s`. -/
@[simp]
lemma StrictSegal.core_concat (sx : X.StrictSegal) (n : ℕ) (e : X _⦋1⦌) (s : X _⦋n⦌)
    (h : X.δ 0 e = X.map (SimplexCategory.const _ _ 0).op s) :
    (sx.core n).concat e s h =
      sx.spineToSimplex ((X.spine n s).cons e (h.trans (X.spine_vertex n s 0).symm)) :=
  (rfl)

/-- In a strict Segal simplicial set, the edge `e₀₂` of a `CompStruct e₀₁ e₁₂ e₀₂` is determined
by the spine edges `e₀₁` and `e₁₂`. -/
lemma Edge.CompStruct.eq_of_isStrictSegal [X.IsStrictSegal] {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ e₀₂' : Edge x₀ x₂}
    (h : CompStruct e₀₁ e₁₂ e₀₂) (h' : CompStruct e₀₁ e₁₂ e₀₂') : e₀₂ = e₀₂' := by
  have : h.simplex = h'.simplex :=
    IsStrictSegal.ext_of_δ_zero_of_δ_last (n := 0) (h.d₀.trans h'.d₀.symm)
      (h.d₂.trans h'.d₂.symm)
  exact Edge.ext (by rw [← h.d₁, ← h'.d₁, this])

end Core

namespace Truncated

open SimplexCategory.Truncated Truncated.Hom SimplicialObject.Truncated

variable {n : ℕ} {V W : SSet.Truncated.{u} (n + 1)}

/-- A morphism of truncated simplicial sets maps the spine of a simplex to the spine of its
image. -/
lemma spine_app {m : ℕ} (hm : m ≤ n + 1) (f : V ⟶ W) (x : V _⦋m⦌ₙ₊₁) :
    W.spine m hm (f.app _ x) = (V.spine m hm x).map f := by
  ext i <;> simp [← NatTrans.naturality_apply]

/-- A morphism of truncated simplicial sets that is bijective on edges is bijective on
vertices. -/
lemma bijective_app_zero_of_bijective_app_one (f : V ⟶ W)
    (h₁ : Function.Bijective (f.app (op ⦋1⦌ₙ₊₁))) : Function.Bijective (f.app (op ⦋0⦌ₙ₊₁)) := by
  refine ⟨fun x y hxy ↦ ?_, fun w ↦ ?_⟩
  · have := h₁.injective ((NatTrans.naturality_apply f (tr (SimplexCategory.σ 0)).op x).trans
      ((congrArg _ hxy).trans (NatTrans.naturality_apply f (tr (SimplexCategory.σ 0)).op y).symm))
    rw [← δ_zero_comp_σ_zero_apply V x, ← δ_zero_comp_σ_zero_apply V y, this]
  · obtain ⟨s, hs⟩ := h₁.surjective (W.map (tr (SimplexCategory.σ 0)).op w)
    exact ⟨V.map (tr (SimplexCategory.δ 0)).op s,
      (NatTrans.naturality_apply f _ s).trans
        ((congrArg _ hs).trans (δ_zero_comp_σ_zero_apply W w))⟩

/-- A morphism of strict Segal truncated simplicial sets that is bijective on edges is an
isomorphism. -/
theorem isIso_of_bijective_app_one [V.IsStrictSegal] [W.IsStrictSegal] (f : V ⟶ W)
    (h₁ : Function.Bijective (f.app (op ⦋1⦌ₙ₊₁))) : IsIso f := by
  have h₀ := bijective_app_zero_of_bijective_app_one f h₁
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨⟨m, hm⟩⟩
  induction m using SimplexCategory.rec with | _ m
  rw [isIso_iff_bijective]
  refine ⟨fun x y hxy ↦ V.spine_injective (h := hm) ?_, fun w ↦ ?_⟩
  · have := congr_arg (W.spine m hm) hxy
    rw [spine_app, spine_app] at this
    ext i
    · exact h₀.injective congr(Truncated.Path.vertex $this i)
    · exact h₁.injective congr(Truncated.Path.arrow $this i)
  · -- Lift the spine of `w` along `f` vertex by vertex and edge by edge.
    obtain ⟨x, hx⟩ := V.spine_surjective
      { vertex i := Function.surjInv h₀.surjective ((W.spine m hm w).vertex i)
        arrow i := Function.surjInv h₁.surjective ((W.spine m hm w).arrow i)
        arrow_src i := h₀.injective <| (NatTrans.naturality_apply f _ _).trans <|
          (congrArg (W.map _) (Function.surjInv_eq h₁.surjective _)).trans <|
            ((W.spine m hm w).arrow_src i).trans (Function.surjInv_eq h₀.surjective _).symm
        arrow_tgt i := h₀.injective <| (NatTrans.naturality_apply f _ _).trans <|
          (congrArg (W.map _) (Function.surjInv_eq h₁.surjective _)).trans <|
            ((W.spine m hm w).arrow_tgt i).trans (Function.surjInv_eq h₀.surjective _).symm } hm
    refine ⟨x, W.spine_injective (h := hm) ?_⟩
    rw [spine_app, hx]
    ext i
    · exact Function.surjInv_eq h₀.surjective _
    · exact Function.surjInv_eq h₁.surjective _

end Truncated

section Colimit

variable {J : Type*} [Category* J] {F : J ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c)

variable [IsFilteredOrEmpty J] [∀ j, (F.obj j).IsStrictSegal]

include hc in
/-- In a filtered colimit of strict Segal simplicial sets, an `(n + 1)`-simplex is determined by
its first edge and its face opposite to the vertex `0`. -/
private lemma ext_of_isColimit {n : ℕ} {x y : c.pt _⦋n + 1⦌}
    (h : c.pt.map (mkOfSucc 0).op x = c.pt.map (mkOfSucc 0).op y)
    (h₀ : c.pt.δ 0 x = c.pt.δ 0 y) : x = y := by
  obtain ⟨j, x, y, rfl, rfl⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂
    (isColimitOfPreserves ((evaluation _ _).obj (op ⦋n + 1⦌)) hc) x y
  dsimp at h h₀ x y ⊢
  rw [SimplicialObject.δ_def, ← NatTrans.naturality_apply, ← NatTrans.naturality_apply,
    ι_app_eq_ι_app_iff_of_isColimit hc] at h₀
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply,
    ι_app_eq_ι_app_iff_of_isColimit hc] at h
  obtain ⟨k₁, f₁, h₁⟩ := h
  obtain ⟨k₂, f₂, h₂⟩ := h₀
  -- Both equations hold at a common later stage, where the strict Segal condition applies.
  obtain ⟨k, g₁, g₂, hg⟩ := IsFiltered.span f₁ f₂
  rw [← ι_app_map_app (f₁ ≫ g₁), ← ι_app_map_app (f₁ ≫ g₁) y]
  congr 1
  apply ((StrictSegal.ofIsStrictSegal (F.obj k)).core n).injective
  · simp only [Functor.map_comp, NatTrans.comp_app, ConcreteCategory.comp_apply,
      ← NatTrans.naturality_apply, h₁]
  · simp only [hg, Functor.map_comp, NatTrans.comp_app, ConcreteCategory.comp_apply,
      SimplicialObject.δ_def, ← NatTrans.naturality_apply, h₂]

include hc in
/-- In a filtered colimit of strict Segal simplicial sets, an edge and an `n`-simplex glued along
a vertex are the first edge and the face opposite to the vertex `0` of an `(n + 1)`-simplex. -/
private lemma exists_concat_of_isColimit {n : ℕ} (e : c.pt _⦋1⦌) (s : c.pt _⦋n⦌)
    (h : c.pt.δ 0 e = c.pt.map (SimplexCategory.const _ _ 0).op s) :
    ∃ x : c.pt _⦋n + 1⦌, c.pt.map (mkOfSucc 0).op x = e ∧ c.pt.δ 0 x = s := by
  obtain ⟨j₁, e, rfl⟩ := exists_ι_app_eq_of_isColimit hc e
  obtain ⟨j₂, s, rfl⟩ := exists_ι_app_eq_of_isColimit hc s
  rw [← ι_app_map_app (IsFiltered.leftToMax j₁ j₂) e,
    ← ι_app_map_app (IsFiltered.rightToMax j₁ j₂) s] at h ⊢
  generalize (F.map (IsFiltered.leftToMax j₁ j₂)).app _ e = e at h ⊢
  generalize (F.map (IsFiltered.rightToMax j₁ j₂)).app _ s = s at h ⊢
  rw [SimplicialObject.δ_def, ← NatTrans.naturality_apply, ← NatTrans.naturality_apply,
    ι_app_eq_ι_app_iff_of_isColimit hc] at h
  -- The gluing condition holds at a later stage `k`, where the simplex can be formed.
  obtain ⟨k, f, hf⟩ := h
  rw [← ι_app_map_app f e, ← ι_app_map_app f s]
  have h' : (F.obj k).δ 0 ((F.map f).app _ e) =
      (F.obj k).map (SimplexCategory.const _ _ 0).op ((F.map f).app _ s) := by
    rw [SimplicialObject.δ_def, ← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
    exact hf
  let sk := (StrictSegal.ofIsStrictSegal (F.obj k)).core n
  refine ⟨(c.ι.app k).app _ (sk.concat _ _ h'), ?_, ?_⟩
  · rw [← NatTrans.naturality_apply, sk.map_mkOfSucc_zero_concat]
  · rw [SimplicialObject.δ_def, ← NatTrans.naturality_apply, ← SimplicialObject.δ_def,
      sk.δ₀_concat]

include hc in
/-- The colimit of a filtered (or empty) diagram of strict Segal simplicial sets, of any size, is
strict Segal. -/
theorem IsStrictSegal.of_isColimit : c.pt.IsStrictSegal :=
  (StrictSegal.ofCore fun _ ↦
    { concat e s h := (exists_concat_of_isColimit hc e s h).choose
      map_mkOfSucc_zero_concat e s h := (exists_concat_of_isColimit hc e s h).choose_spec.1
      δ₀_concat e s h := (exists_concat_of_isColimit hc e s h).choose_spec.2
      injective := ext_of_isColimit hc }).isStrictSegal

end Colimit

end SSet

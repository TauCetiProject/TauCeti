/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.DenseAtYoneda
public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
public import Mathlib.Topology.Category.TopCat.ULift
public import TauCeti.AlgebraicTopology.SimplicialSet.Discrete
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.AlgebraicTopology.SimplicialSet.ULift
public import TauCeti.AlgebraicTopology.TopologicalSimplex
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Open cells, faithfulness, discrete spaces, and universe lift of geometric realization

Every point of the geometric realization `|X|` of a simplicial set `X` has the form
`SSet.toTopObjMk x w` for some `n`-simplex `x` of `X` and barycentric coordinates
`w : StdSimplex ℝ (Fin (n + 1))` (`SSet.exists_toTopObjMk`). Stripping the vanishing coordinates of
`w` passes to a uniquely determined face of `⦋n⦌`, and Mathlib's Eilenberg–Zilber lemma
(`SSet.exists_nonDegenerate`) expresses the restricted simplex uniquely as an iterated degeneracy of
a nondegenerate simplex `s : X.N`. Pushing the remaining strictly positive coordinates forward along
that degeneracy exhibits every point of `|X|` uniquely as `SSet.toTopObjMk s.simplex w₀` with
nowhere-vanishing coordinates (`SSet.toTopCellEquiv`), the underlying bijection of Milnor's
open-cell decomposition of `|X|`.

Evaluating at any interior point of the standard simplex — in particular at `StdSimplex.barycenter`
— whose pushforwards along monotone maps determine the maps via cumulative weight sums, shows that
`x ↦ SSet.toTopObjMk x w` is injective in every dimension
(`SSet.toTopObjMk_injective_of_weights_ne_zero`, `SSet.toTopObjMk_barycenter_injective`).
Consequently the unit `X ⟶ Sing |X|` of `sSetTopAdj` is a monomorphism
(`SSet.mono_sSetTopAdj_unit_app`), the geometric realization functor `SSet.toTop` is faithful, and
the vertex map `SSet.toTopPoint : X _⦋0⦌ → |X|` is injective (`SSet.toTopPoint_injective`).

We also record the basic point-set identifications of `|X|`:
* `SSet.toTopPoint`, `SSet.toTop_map_toTopPoint`: the point of `|X|` attached to a vertex of `X`.
* `SSet.nonempty_toTop_iff`, `SSet.isEmpty_toTop_iff`: `|X|` is nonempty (resp. empty) precisely
  when `X` has a `0`-simplex (resp. no `0`-simplices).
* `SSet.toTop_map_const`: a constant simplicial map `SSet.const y` realizes to `TopCat.const`.
* `SSet.toTopConstIso`, `SSet.toTopConstHomeomorph`: the realization of a constant (discrete)
  simplicial set `(Functor.const SimplexCategoryᵒᵖ).obj S` is discrete on `S`.
* `SSet.toTopUliftNatIso`, `SSet.toTopUliftIso`, `SSet.toTopUliftHomeomorph`: geometric realization
  commutes with `SSet.uliftFunctor` and `TopCat.uliftFunctor`, so lifting a simplicial set to a
  higher universe produces a homeomorphic realization.

## References

* J. Milnor, *The geometric realization of a semi-simplicial complex*, Ann. of Math. (2) 65
  (1957), 357–362, Lemma 1.
* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Section I.2.
-/

public section

open CategoryTheory Limits Opposite Simplicial Convexity

universe v u

namespace SSet

instance : stdSimplex.{u}.IsDense :=
  inferInstanceAs uliftYoneda.{u}.IsDense

section Points

variable {X : SSet.{u}}

-- `@[expose]` is mandated by `module` so downstream realization modules (`PiZero`,
-- `FundamentalGroupoid`) can unfold `toTopPoint` to the unit's `0`-simplex component.
/-- The point of the geometric realization `|X|` given by a vertex `x` of `X`: the singular vertex
`(sSetTopAdj.unit.app X).app _ x` of `|X|`. -/
@[expose]
noncomputable def toTopPoint {X : SSet.{u}} (x : X _⦋0⦌) : |X| :=
  TopCat.toSSetObj₀Equiv ((sSetTopAdj.unit.app X).app _ x)

/-- The realization of a map sends the point of a vertex to the point of its image. -/
@[simp]
lemma toTop_map_toTopPoint {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    toTop.map f (toTopPoint x) = toTopPoint (f.app _ x) := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (sSetTopAdj.unit.naturality f) _) x
  dsimp at h
  rw [toTopPoint, toTopPoint, h, TauCeti.TopCat.toSSetObj₀Equiv_toSSet_map_app]

/-- On a `0`-simplex, `toTopPoint` agrees with `toTopObjMk` at any point of `StdSimplex ℝ (Fin 1)`.
-/
lemma toTopPoint_eq_toTopObjMk (x : X _⦋0⦌) (w : StdSimplex ℝ (Fin 1)) :
    toTopPoint x = toTopObjMk x w := by
  let v₀ : (Δ[0] : SSet.{u}) _⦋0⦌ := stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)
  have hmap := congrArg (toTop.map (yonedaEquiv.symm x))
    (Subsingleton.elim (toTopPoint v₀) (toTopObjMk v₀ w))
  rw [toTop_map_toTopPoint, toTop_map_toTopObjMk] at hmap
  simpa [v₀] using hmap

/-- On a `0`-simplex, `toTopObjMk` is independent of the coordinates and equals `toTopPoint`. -/
@[simp]
lemma toTopObjMk_zero (x : X _⦋0⦌) (w : StdSimplex ℝ (Fin 1)) :
    toTopObjMk x w = toTopPoint x :=
  (toTopPoint_eq_toTopObjMk x w).symm

/-- At the `i`-th standard basis vertex, `toTopObjMk x (StdSimplex.single i)` is the realized point
of the `i`-th vertex of `x`. -/
@[simp]
lemma toTopObjMk_single {n : ℕ} (x : X _⦋n⦌) (i : Fin (n + 1)) :
    toTopObjMk x (StdSimplex.single i) =
      toTopPoint (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op x) := by
  have hsingle : (StdSimplex.single i : StdSimplex ℝ (Fin (n + 1))) =
      StdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i) (StdSimplex.single 0) := by
    rw [StdSimplex.map_single]; rfl
  rw [hsingle, ← toTopObjMk_map, toTopObjMk_zero]

/-- In terms of the colimit presentation of `|X|`, `toTopObjMk x w` is the image of `w` under the
realized simplex `|Δ[n]| ⟶ |X|` classifying `x`. -/
lemma toTopObjMk_eq_toTop_map {n : ℕ} (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    toTopObjMk x w = toTop.map (yonedaEquiv.symm x) (⦋n⦌.toTopHomeo.symm w) := by
  rw [toTopObjMk_def]
  exact ConcreteCategory.congr_hom (sSetTopAdj_unit_app_app_down X (op ⦋n⦌) x) (ULift.up w)

/-- Every point of `|X|` lies in the image of `toTopObjMk` for some simplex of `X`. -/
lemma exists_toTopObjMk (p : |X|) :
    ∃ (n : ℕ) (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))), p = toTopObjMk x w := by
  obtain ⟨⟨m, _, f⟩, y, hy⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (toTop ⋙ forget TopCat) (stdSimplex.{u}.denseAt X)) p
  dsimp at y hy
  rw [Category.id_comp] at hy
  induction m using SimplexCategory.rec with | _ n => ?_
  refine ⟨n, yonedaEquiv f, ⦋n⦌.toTopHomeo y, ?_⟩
  rw [toTopObjMk_eq_toTop_map, Equiv.symm_apply_apply, Homeomorph.symm_apply_apply]
  exact hy.symm

/-- Every point of `|X|` can be joined by a path in `|X|` to the realization of a vertex of `X`. -/
lemma exists_joined_toTopPoint (p : |X|) : ∃ x : X _⦋0⦌, Joined (toTopPoint x) p := by
  obtain ⟨n, s, w, rfl⟩ := exists_toTopObjMk p
  refine ⟨X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op s, ?_⟩
  rw [← toTopObjMk_single]
  exact (PathConnectedSpace.joined (StdSimplex.single 0) w).map (continuous_toTopObjMk s)

/-- The geometric realization `|X|` is nonempty if and only if `X` has a `0`-simplex. -/
@[simp]
lemma nonempty_toTop_iff (X : SSet.{u}) : Nonempty |X| ↔ X.Nonempty :=
  ⟨fun ⟨p⟩ ↦ let ⟨_, x, _, _⟩ := exists_toTopObjMk p; .mk x, fun ⟨x⟩ ↦ ⟨toTopPoint x⟩⟩

/-- The geometric realization `|X|` is empty if and only if `X` has no `0`-simplices. -/
@[simp]
lemma isEmpty_toTop_iff (X : SSet.{u}) : IsEmpty |X| ↔ IsEmpty (X _⦋0⦌) := by
  rw [← not_nonempty_iff, nonempty_toTop_iff, SSet.Nonempty, not_nonempty_iff]

instance isEmpty_toTop (X : SSet.{u}) [IsEmpty (X _⦋0⦌)] : IsEmpty |X| :=
  (isEmpty_toTop_iff X).2 ‹_›

instance nonempty_toTop (X : SSet.{u}) [X.Nonempty] : Nonempty |X| :=
  (nonempty_toTop_iff X).2 ‹_›

/-- The geometric realization of a constant simplicial map `SSet.const y` is the constant
continuous map at `toTopPoint y` (dual to `TopCat.toSSet_map_const`). -/
@[simp]
lemma toTop_map_const (X : SSet.{u}) {Y : SSet.{u}} (y : Y _⦋0⦌) :
    toTop.map (SSet.const (X := X) y) = TopCat.const (X := |X|) (toTopPoint y) :=
  toTop_hom_ext fun _ _ _ ↦ by
    rw [toTop_map_toTopObjMk, SSet.const_app, TypeCat.ofHom_apply, toTopObjMk_map,
      toTopObjMk_zero, TopCat.const_apply]

end Points

section Discrete

/-- Auxiliary morphism `|(Functor.const SimplexCategoryᵒᵖ).obj S| ⟶ TopCat.discrete.obj S`. -/
private noncomputable def toTopConstHom (S : Type u) :
    |(Functor.const SimplexCategoryᵒᵖ).obj S| ⟶ TopCat.discrete.obj S :=
  (sSetTopAdj.homEquiv _ (TopCat.discrete.obj S)).symm
    ((constHomEquiv S).symm fun s ↦ TopCat.toSSetObj₀Equiv (X := TopCat.discrete.obj S).symm s)

private lemma toTopConstHom_toTopPoint (S : Type u) (s : S) :
    toTopConstHom S (toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s) = s := by
  rw [toTopConstHom, toTopPoint_eq_toTopObjMk (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s
    default, apply_toTopObjMk, Equiv.apply_symm_apply]
  have h0 := constHomEquiv_symm_app_zero S
    (fun t ↦ TopCat.toSSetObj₀Equiv (X := TopCat.discrete.obj S).symm t) s
  dsimp at h0 ⊢
  rw [h0]; rfl

/-- The geometric realization of the constant (discrete) simplicial set on `S` is isomorphic in
`TopCat` to the discrete topological space on `S`. -/
noncomputable def toTopConstIso (S : Type u) :
    |(Functor.const SimplexCategoryᵒᵖ).obj S| ≅ TopCat.discrete.obj S where
  hom := toTopConstHom S
  inv := TopCat.ofHom (X := TopCat.discrete.obj S)
    ⟨fun s ↦ toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s, continuous_bot⟩
  hom_inv_id := toTop_hom_ext fun n x w ↦ by
    have hw : toTopObjMk (X := (Functor.const SimplexCategoryᵒᵖ).obj S) x w =
        toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) x := by
      conv_lhs =>
        rw [show x = ((Functor.const SimplexCategoryᵒᵖ).obj S).map
          (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op x by simp]
      rw [toTopObjMk_map, toTopObjMk_zero]
    simp only [ConcreteCategory.comp_apply, TopCat.id_app, hw, toTopConstHom_toTopPoint]
    rfl
  inv_hom_id := by ext s; exact toTopConstHom_toTopPoint S s

@[simp]
lemma toTopConstIso_inv_apply (S : Type u) (s : S) :
    (toTopConstIso S).inv s = toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s :=
  (rfl)

@[simp]
lemma toTopConstIso_hom_toTopPoint (S : Type u) (s : S) :
    (toTopConstIso S).hom
      (toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s) = s :=
  toTopConstHom_toTopPoint S s

/-- The homeomorphism between the geometric realization of the constant simplicial set on `S` and
the discrete topological space on `S`. -/
noncomputable def toTopConstHomeomorph (S : Type u) :
    |(Functor.const SimplexCategoryᵒᵖ).obj S| ≃ₜ TopCat.discrete.obj S :=
  TopCat.homeoOfIso (toTopConstIso S)

@[simp]
lemma toTopConstHomeomorph_toTopPoint (S : Type u) (s : S) :
    toTopConstHomeomorph S
      (toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s) = s :=
  toTopConstIso_hom_toTopPoint S s

@[simp]
lemma toTopConstHomeomorph_symm_apply (S : Type u) (s : TopCat.discrete.obj S) :
    (toTopConstHomeomorph S).symm s =
      toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s :=
  (rfl)

end Discrete

section Cells

/-- An open-cell point in Milnor's decomposition of the geometric realization `|X|`: a
nondegenerate simplex `simplex : X.N` together with strictly positive barycentric coordinates on
`Fin (simplex.dim + 1)`. -/
structure ToTopCell (X : SSet.{u}) : Type u where
  /-- The unique nondegenerate simplex whose open cell contains the point. -/
  simplex : X.N
  /-- The interior barycentric coordinates of the point in `simplex`. -/
  coords : StdSimplex ℝ (Fin (simplex.dim + 1))
  /-- Every barycentric coordinate is nonzero (hence strictly positive). -/
  coords_ne_zero : ∀ j, coords.weights j ≠ 0

@[ext (iff := false)]
lemma ToTopCell.ext {X : SSet.{u}} {c₁ c₂ : X.ToTopCell} (hs : c₁.simplex = c₂.simplex)
    (hc : ∀ j : Fin (c₁.simplex.dim + 1),
      c₁.coords.weights j = c₂.coords.weights (Fin.cast (by rw [hs]) j)) :
    c₁ = c₂ := by
  rcases c₁ with ⟨s₁, w₁, hw₁⟩
  rcases c₂ with ⟨s₂, w₂, hw₂⟩
  dsimp only at hs hc
  subst hs
  congr
  ext j
  exact hc j

/-- The open cell attached to a pair `(x, w)` by stripping zero weights of `w` and taking the
Eilenberg–Zilber nondegenerate quotient of the corresponding face of `x`. -/
private noncomputable def toTopCellOfSimplex {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) : X.ToTopCell :=
  let hface := SimplexCategory.exists_mono_stdSimplex_map_eq w
  let k := hface.choose
  let ι : ⦋k⦌ ⟶ ⦋n⦌ := hface.choose_spec.choose
  have : Mono ι := hface.choose_spec.choose_spec.choose
  let w₀ := hface.choose_spec.choose_spec.choose_spec.choose
  let hw₀ := hface.choose_spec.choose_spec.choose_spec.choose_spec.1
  let hez := X.exists_nonDegenerate (X.map ι.op x)
  let r := hez.choose
  let π : ⦋k⦌ ⟶ ⦋r⦌ := hez.choose_spec.choose
  have : Epi π := hez.choose_spec.choose_spec.choose
  let z : X.nonDegenerate r := hez.choose_spec.choose_spec.choose_spec.choose
  { simplex := N.mk z.1 z.2
    coords := w₀.map π
    coords_ne_zero := SimplexCategory.weights_stdSimplex_map_ne_zero_of_epi π hw₀ }

/-- Characterization of `toTopCellOfSimplex x w` by any mono–epi decomposition of `(x, w)`. -/
private lemma toTopCellOfSimplex_eq_of_decomp {X : SSet.{u}} {n k r : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1)))
    (ι : ⦋k⦌ ⟶ ⦋n⦌) [Mono ι] (w₀ : StdSimplex ℝ (Fin (k + 1)))
    (hw₀ : ∀ j, w₀.weights j ≠ 0) (hw : w = w₀.map ι)
    (π : ⦋k⦌ ⟶ ⦋r⦌) [Epi π] (z : X.nonDegenerate r) (hz : X.map ι.op x = X.map π.op z.1) :
    toTopCellOfSimplex x w =
      ⟨N.mk z.1 z.2, w₀.map π, SimplexCategory.weights_stdSimplex_map_ne_zero_of_epi π hw₀⟩ := by
  rw [toTopCellOfSimplex]
  set hface := SimplexCategory.exists_mono_stdSimplex_map_eq w
  set k' := hface.choose
  set ι' : ⦋k'⦌ ⟶ ⦋n⦌ := hface.choose_spec.choose
  have : Mono ι' := hface.choose_spec.choose_spec.choose
  set w₀' := hface.choose_spec.choose_spec.choose_spec.choose
  have hw₀' : ∀ j, w₀'.weights j ≠ 0 := hface.choose_spec.choose_spec.choose_spec.choose_spec.1
  have hw' : w = w₀'.map ι' := hface.choose_spec.choose_spec.choose_spec.choose_spec.2
  have hk : k' = k := SimplexCategory.eq_dim_of_mono_stdSimplex_map_eq hw₀' hw₀ (hw'.symm.trans hw)
  set hez := X.exists_nonDegenerate (X.map ι'.op x)
  set r' := hez.choose
  set π' : ⦋k'⦌ ⟶ ⦋r'⦌ := hez.choose_spec.choose
  have : Epi π' := hez.choose_spec.choose_spec.choose
  set z' : X.nonDegenerate r' := hez.choose_spec.choose_spec.choose_spec.choose
  have hz' : X.map ι'.op x = X.map π'.op z'.1 := hez.choose_spec.choose_spec.choose_spec.choose_spec
  subst hk
  obtain ⟨rfl, rfl⟩ := SimplexCategory.eq_of_mono_stdSimplex_map_eq hw₀' hw₀ (hw'.symm.trans hw)
  have hr : r' = r := X.unique_nonDegenerate_dim (X.map ι'.op x) π' z' hz' π z hz
  subst hr
  have hz_eq : z' = z := X.unique_nonDegenerate_simplex (X.map ι'.op x) π' z' hz' π z hz
  have hπ_eq : π' = π := X.unique_nonDegenerate_map (X.map ι'.op x) π' z' hz' π z hz
  subst hz_eq hπ_eq
  rfl

/-- Naturality of `toTopCellOfSimplex` along simplicial operators, proved via epi–mono
factorization in `SimplexCategory`. -/
private lemma toTopCellOfSimplex_map {X : SSet.{u}} {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (m + 1))) :
    toTopCellOfSimplex (X.map θ.op x) w = toTopCellOfSimplex x (w.map θ) := by
  obtain ⟨k, ι, _, w₀, hw₀, rfl⟩ := SimplexCategory.exists_mono_stdSimplex_map_eq w
  -- Factor `ι ≫ θ` in `SimplexCategory` as an epimorphism followed by a monomorphism.
  obtain ⟨k', hk'⟩ : ∃ k' : ℕ, image (ι ≫ θ) = ⦋k'⦌ :=
    ⟨(image (ι ≫ θ)).len, SimplexCategory.rec (fun _ ↦ rfl) (image (ι ≫ θ))⟩
  let e : ⦋k⦌ ⟶ ⦋k'⦌ := factorThruImage (ι ≫ θ) ≫ eqToHom hk'
  let ι' : ⦋k'⦌ ⟶ ⦋n⦌ := eqToHom hk'.symm ≫ image.ι (ι ≫ θ)
  have : Epi e := epi_comp _ _
  have : Mono ι' := mono_comp _ _
  have hfac : e ≫ ι' = ι ≫ θ := by simp [e, ι', image.fac]
  obtain ⟨r, π', _, z, hz⟩ := X.exists_nonDegenerate (X.map ι'.op x)
  have hez_lhs : X.map ι.op (X.map θ.op x) = X.map (e ≫ π').op z.1 := by
    rw [← Functor.map_comp_apply, ← op_comp, ← hfac, op_comp, Functor.map_comp_apply, hz,
      ← Functor.map_comp_apply, ← op_comp]
  have hw_rhs : (w₀.map ι).map θ = (w₀.map e).map ι' := by
    rw [StdSimplex.map_map, StdSimplex.map_map]
    exact congrArg (fun f : ⦋k⦌ ⟶ ⦋n⦌ ↦ w₀.map f) hfac.symm
  have : Epi (e ≫ π') := epi_comp _ _
  rw [toTopCellOfSimplex_eq_of_decomp (X.map θ.op x) (w₀.map ι) ι w₀ hw₀ rfl (e ≫ π') z hez_lhs,
    toTopCellOfSimplex_eq_of_decomp x ((w₀.map ι).map θ) ι' (w₀.map e)
      (SimplexCategory.weights_stdSimplex_map_ne_zero_of_epi e hw₀) hw_rhs π' z hz]
  refine ToTopCell.ext rfl fun j ↦ ?_
  have hcomp : (w₀.map e).map π' = w₀.map (e ≫ π') := StdSimplex.map_map _ _ _
  exact congrArg (fun u ↦ u.weights j) hcomp.symm

/-- Reassembling an open cell via `toTopObjMk` recovers the original point of `|X|`. -/
private lemma toTopObjMk_toTopCellOfSimplex {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    toTopObjMk (toTopCellOfSimplex x w).simplex.simplex (toTopCellOfSimplex x w).coords =
      toTopObjMk x w := by
  obtain ⟨k, ι, _, w₀, hw₀, hw⟩ := SimplexCategory.exists_mono_stdSimplex_map_eq w
  obtain ⟨r, π, _, z, hz⟩ := X.exists_nonDegenerate (X.map ι.op x)
  refine (congrArg (fun c : X.ToTopCell ↦ toTopObjMk c.simplex.simplex c.coords)
    (toTopCellOfSimplex_eq_of_decomp x w ι w₀ hw₀ hw π z hz)).trans ?_
  dsimp only [N.mk, S.mk]
  rw [← toTopObjMk_map π z.1 w₀, ← hz, toTopObjMk_map ι x w₀, ← hw]

/-- An open cell `(s, w)` is recovered from its point `toTopObjMk s.simplex w`. -/
private lemma toTopCellOfSimplex_cell {X : SSet.{u}} (c : X.ToTopCell) :
    toTopCellOfSimplex c.simplex.simplex c.coords = c := by
  rcases c with ⟨s, w, hw⟩
  obtain ⟨d, ⟨y, hy⟩, rfl⟩ := s.mk_surjective
  have hid : (w : StdSimplex ℝ (Fin (d + 1))) = (w : StdSimplex ℝ (Fin (d + 1))).map (𝟙 ⦋d⦌) :=
    (StdSimplex.map_id _).symm
  refine (toTopCellOfSimplex_eq_of_decomp y w (𝟙 ⦋d⦌) w hw hid (𝟙 ⦋d⦌) ⟨y, hy⟩ rfl).trans ?_
  exact ToTopCell.ext rfl fun j ↦ congrArg (·.weights j) hid.symm

/-- Milnor's open-cell bijection: every point of the geometric realization `|X|` corresponds to a
unique pair `(s, w)` consisting of a nondegenerate simplex `s : X.N` and strictly positive
barycentric coordinates `w : StdSimplex ℝ (Fin (s.dim + 1))`. -/
noncomputable def toTopCellEquiv (X : SSet.{u}) : |X| ≃ X.ToTopCell := by
  -- Map `|X|` to the indiscrete space on `X.ToTopCell`, where every map from a simplex is
  -- automatically continuous.
  let φ : X ⟶ TopCat.toSSet.obj (TopCat.trivial.obj X.ToTopCell) :=
    { app m := ↾fun x ↦ ((TopCat.trivial.obj X.ToTopCell).toSSetObjEquiv m).symm
        ⟨fun w ↦ toTopCellOfSimplex (n := m.unop.len)
          (X.map (eqToHom (by cases m using Opposite.rec; cases ‹SimplexCategory›; rfl)) x) w,
          continuous_top⟩
      naturality := fun ⟨⟨d₁⟩⟩ ⟨⟨d₂⟩⟩ ⟨g⟩ ↦ by
        ext x
        apply ((TopCat.trivial.obj X.ToTopCell).toSSetObjEquiv (op ⦋d₂⦌)).injective
        ext w
        simp only [TypeCat.Fun.toFun_apply, ConcreteCategory.comp_apply, TypeCat.ofHom_apply,
          Equiv.apply_symm_apply, eqToHom_refl, CategoryTheory.Functor.map_id, types_id_apply]
        exact toTopCellOfSimplex_map g x w }
  let F : |X| ⟶ TopCat.trivial.obj X.ToTopCell := (sSetTopAdj.homEquiv X _).symm φ
  have hF {n : ℕ} (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
      F (toTopObjMk x w) = toTopCellOfSimplex x w := by
    rw [apply_toTopObjMk, Equiv.apply_symm_apply]
    simp only [φ, TypeCat.ofHom_apply, Equiv.apply_symm_apply,
      eqToHom_refl, CategoryTheory.Functor.map_id, types_id_apply]
    rfl
  exact
    { toFun := F
      invFun c := toTopObjMk c.simplex.simplex c.coords
      left_inv p := by
        obtain ⟨n, x, w, rfl⟩ := exists_toTopObjMk p
        rw [hF]; exact toTopObjMk_toTopCellOfSimplex x w
      right_inv c := by dsimp only; rw [hF]; exact toTopCellOfSimplex_cell c }

@[simp]
lemma toTopCellEquiv_symm_apply {X : SSet.{u}} (c : X.ToTopCell) :
    X.toTopCellEquiv.symm c = toTopObjMk c.simplex.simplex c.coords :=
  (rfl)

@[simp]
lemma toTopCellEquiv_toTopObjMk_of_ne_zero {X : SSet.{u}} (s : X.N)
    (w : StdSimplex ℝ (Fin (s.dim + 1))) (hw : ∀ j, w.weights j ≠ 0) :
    X.toTopCellEquiv (toTopObjMk s.simplex w) = ⟨s, w, hw⟩ := by
  simpa using X.toTopCellEquiv.apply_symm_apply ⟨s, w, hw⟩

/-- Characterization of `X.toTopCellEquiv (toTopObjMk x w)` by any decomposition of `(x, w)` along
a morphism `ι : ⦋k⦌ ⟶ ⦋n⦌` carrying interior coordinates `w₀` (for instance a face `[Mono ι]` in a
mono–epi factorization) and an iterated degeneracy `π : ⦋k⦌ ⟶ ⦋r⦌` (`[Epi π]`) onto a
nondegenerate simplex `z`. -/
lemma toTopCellEquiv_toTopObjMk_eq_of_decomp {X : SSet.{u}} {n k r : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1)))
    (ι : ⦋k⦌ ⟶ ⦋n⦌) (w₀ : StdSimplex ℝ (Fin (k + 1)))
    (hw₀ : ∀ j, w₀.weights j ≠ 0) (hw : w = w₀.map ι)
    (π : ⦋k⦌ ⟶ ⦋r⦌) [Epi π] (z : X.nonDegenerate r) (hz : X.map ι.op x = X.map π.op z.1) :
    X.toTopCellEquiv (toTopObjMk x w) =
      ⟨N.mk z.1 z.2, w₀.map π, SimplexCategory.weights_stdSimplex_map_ne_zero_of_epi π hw₀⟩ := by
  apply X.toTopCellEquiv.symm.injective
  rw [Equiv.symm_apply_apply, toTopCellEquiv_symm_apply]
  dsimp only [N.mk, S.mk]
  rw [← toTopObjMk_map π z.1 w₀, ← hz, toTopObjMk_map ι x w₀, ← hw]

/-- A realized vertex `toTopPoint x` lies in the `0`-dimensional open cell of `x`. -/
@[simp]
lemma toTopCellEquiv_toTopPoint {X : SSet.{u}} (x : X _⦋0⦌) :
    X.toTopCellEquiv (toTopPoint x) =
      ⟨N.mk x (by simp), StdSimplex.single 0, fun j ↦ by
        have hj : j = 0 := Fin.ext (by dsimp [N.mk, S.mk] at j ⊢; omega)
        rw [hj, StdSimplex.weights_single, Finsupp.single_eq_same]
        exact one_ne_zero⟩ := by
  rw [toTopPoint_eq_toTopObjMk x (StdSimplex.single 0)]
  exact toTopCellEquiv_toTopObjMk_of_ne_zero (N.mk x (by simp)) (StdSimplex.single 0) _

/-- The nondegenerate simplex carrying `toTopObjMk x w` lies in the subcomplex generated by `x`. -/
lemma toTopCellEquiv_toTopObjMk_subcomplex_le {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    (X.toTopCellEquiv (toTopObjMk x w)).simplex.subcomplex ≤ Subcomplex.ofSimplex x := by
  obtain ⟨k, ι, _, w₀, hw₀, hw⟩ := SimplexCategory.exists_mono_stdSimplex_map_eq w
  obtain ⟨r, π, _, z, hz⟩ := X.exists_nonDegenerate (X.map ι.op x)
  rw [toTopCellEquiv_toTopObjMk_eq_of_decomp x w ι w₀ hw₀ hw π z hz]
  exact (S.subcomplex_eq_of_epi (S.mk (X.map ι.op x)) (S.mk z.1) π hz.symm).symm.trans_le
    (S.subcomplex_map_le (S.mk (X.map ι.op x)) (S.mk x) ι rfl)

/-- The open cell of `toTopObjMk x w` has dimension at most `n`. -/
lemma toTopCellEquiv_toTopObjMk_dim_le {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    (X.toTopCellEquiv (toTopObjMk x w)).simplex.dim ≤ n := by
  obtain ⟨k, ι, _, w₀, hw₀, hw⟩ := SimplexCategory.exists_mono_stdSimplex_map_eq w
  obtain ⟨r, π, _, z, hz⟩ := X.exists_nonDegenerate (X.map ι.op x)
  rw [toTopCellEquiv_toTopObjMk_eq_of_decomp x w ι w₀ hw₀ hw π z hz]
  exact (SimplexCategory.len_le_of_epi π).trans (SimplexCategory.len_le_of_mono ι)

/-- A monomorphism `f : X ⟶ Y` of simplicial sets preserves open cells under `toTop.map f`. -/
@[simp]
lemma toTopCellEquiv_toTop_map {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (p : |X|) :
    Y.toTopCellEquiv (toTop.map f p) =
      ⟨N.mk (f.app (op ⦋(X.toTopCellEquiv p).simplex.dim⦌) (X.toTopCellEquiv p).simplex.simplex)
        ((nonDegenerate_iff_of_mono f _).mpr (X.toTopCellEquiv p).simplex.nonDegenerate),
        (X.toTopCellEquiv p).coords, (X.toTopCellEquiv p).coords_ne_zero⟩ := by
  conv_lhs =>
    rw [← X.toTopCellEquiv.symm_apply_apply p, toTopCellEquiv_symm_apply, toTop_map_toTopObjMk]
  exact toTopCellEquiv_toTopObjMk_of_ne_zero
    (N.mk (f.app _ (X.toTopCellEquiv p).simplex.simplex)
      ((nonDegenerate_iff_of_mono f _).mpr (X.toTopCellEquiv p).simplex.nonDegenerate))
    (X.toTopCellEquiv p).coords (X.toTopCellEquiv p).coords_ne_zero

/-- Evaluating `toTopObjMk · w` at any interior point `w` of `StdSimplex ℝ (Fin (n + 1))` is
injective on `n`-simplices. -/
theorem toTopObjMk_injective_of_weights_ne_zero (X : SSet.{u}) {n : ℕ}
    {w : StdSimplex ℝ (Fin (n + 1))} (hw : ∀ j, w.weights j ≠ 0) :
    Function.Injective fun x : X _⦋n⦌ ↦ toTopObjMk x w := by
  intro x₁ x₂ h
  dsimp only at h
  obtain ⟨r₁, π₁, _, z₁, rfl⟩ := X.exists_nonDegenerate x₁
  obtain ⟨r₂, π₂, _, z₂, rfl⟩ := X.exists_nonDegenerate x₂
  rw [toTopObjMk_map, toTopObjMk_map] at h
  have hc : X.toTopCellEquiv (toTopObjMk (N.mk z₁.1 z₁.2).simplex (w.map π₁)) =
      X.toTopCellEquiv (toTopObjMk (N.mk z₂.1 z₂.2).simplex (w.map π₂)) :=
    congrArg X.toTopCellEquiv h
  rw [toTopCellEquiv_toTopObjMk_of_ne_zero (N.mk z₁.1 z₁.2) (w.map π₁)
      (SimplexCategory.weights_stdSimplex_map_ne_zero_of_epi π₁ hw),
    toTopCellEquiv_toTopObjMk_of_ne_zero (N.mk z₂.1 z₂.2) (w.map π₂)
      (SimplexCategory.weights_stdSimplex_map_ne_zero_of_epi π₂ hw)] at hc
  have hsimp : N.mk z₁.1 z₁.2 = N.mk z₂.1 z₂.2 := congrArg ToTopCell.simplex hc
  have hdim : r₁ = r₂ := congrArg (·.dim) hsimp
  subst hdim
  have hz : z₁ = z₂ := Subtype.ext (by injection hsimp with hS; injection hS)
  subst hz
  have hcoords : w.map π₁ = w.map π₂ := by injection hc
  rw [SimplexCategory.eq_of_stdSimplex_map_eq_of_weights_ne_zero hw hcoords]

/-- Evaluating `toTopObjMk · StdSimplex.barycenter` on `n`-simplices is injective. -/
theorem toTopObjMk_barycenter_injective (X : SSet.{u}) (n : ℕ) :
    Function.Injective fun x : X _⦋n⦌ ↦
      toTopObjMk x (StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))) :=
  toTopObjMk_injective_of_weights_ne_zero X fun _ ↦ by
    rw [StdSimplex.weights_barycenter_apply, Fintype.card_fin]; positivity

/-- The unit `X ⟶ Sing |X|` of the realization–singular adjunction is componentwise injective. -/
theorem sSetTopAdj_unit_app_app_injective (X : SSet.{u}) (m : SimplexCategoryᵒᵖ) :
    Function.Injective ((sSetTopAdj.unit.app X).app m) := by
  rcases m with ⟨⟨n⟩⟩
  intro x₁ x₂ h
  apply toTopObjMk_barycenter_injective X n
  simp only [toTopObjMk_def, h]

/-- The unit `X ⟶ Sing |X|` of `sSetTopAdj` is a monomorphism. -/
instance mono_sSetTopAdj_unit_app (X : SSet.{u}) : Mono (sSetTopAdj.unit.app X) := by
  rw [NatTrans.mono_iff_mono_app]
  intro m
  rw [mono_iff_injective]
  exact sSetTopAdj_unit_app_app_injective X m

/-- The geometric realization functor `SSet.toTop` is faithful. -/
instance : toTop.{u}.Faithful :=
  sSetTopAdj.faithful_L_of_mono_unit_app

/-- Distinct `0`-simplices of `X` map to distinct points of the geometric realization `|X|`. -/
theorem toTopPoint_injective (X : SSet.{u}) : Function.Injective (toTopPoint (X := X)) := by
  intro x₁ x₂ h
  apply toTopObjMk_barycenter_injective X 0
  dsimp only
  rwa [toTopObjMk_zero, toTopObjMk_zero]

@[simp]
lemma toTopPoint_inj {X : SSet.{u}} {x₁ x₂ : X _⦋0⦌} :
    toTopPoint x₁ = toTopPoint x₂ ↔ x₁ = x₂ :=
  (toTopPoint_injective X).eq_iff

end Cells

section ULift

/-- Forward morphism `|uliftFunctor.obj X| ⟶ TopCat.uliftFunctor.obj |X|` adjoint to lifting the
adjunction unit of `X`. -/
private noncomputable def toTopUliftHom (X : SSet.{u}) :
    |uliftFunctor.{v, u}.obj X| ⟶ TopCat.uliftFunctor.{v, u}.obj |X| :=
  (sSetTopAdj.homEquiv _ _).symm
    { app m := ↾fun x ↦ ((TopCat.uliftFunctor.{v, u}.obj |X|).toSSetObjEquiv m).symm
        ((|X|.uliftFunctorObjHomeo : C(|X|, TopCat.uliftFunctor.{v, u}.obj |X|)).comp
          (|X|.toSSetObjEquiv m
            ((sSetTopAdj.unit.app X).app m ((X.uliftFunctorObjEquiv.{v} m).symm x))))
      naturality m₁ m₂ f := by
        obtain ⟨a₁, rfl⟩ : ∃ a, m₁ = op a := ⟨m₁.unop, rfl⟩
        obtain ⟨a₂, rfl⟩ : ∃ a, m₂ = op a := ⟨m₂.unop, rfl⟩
        obtain ⟨g, rfl⟩ : ∃ g : a₂ ⟶ a₁, f = g.op := ⟨f.unop, rfl⟩
        ext x
        apply ((TopCat.uliftFunctor.{v, u}.obj |X|).toSSetObjEquiv (op a₂)).injective
        ext w
        simp only [TypeCat.Fun.toFun_apply, ConcreteCategory.comp_apply, TypeCat.ofHom_apply,
          TopCat.toSSetObjEquiv_naturality_apply, Equiv.apply_symm_apply, ContinuousMap.comp_apply,
          ContinuousMap.coe_ofClass]
        have hnat := ConcreteCategory.congr_hom ((sSetTopAdj.unit.app X).naturality g.op)
          ((X.uliftFunctorObjEquiv.{v} (op a₁)).symm x)
        dsimp at hnat
        rw [← TopCat.toSSetObjEquiv_naturality_apply, ← hnat, uliftFunctorObjEquiv_symm_map] }

private lemma toTopUliftHom_toTopObjMk {X : SSet.{u}} {n : ℕ}
    (x : (uliftFunctor.{v, u}.obj X) _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    toTopUliftHom.{v, u} X (toTopObjMk x w) =
      |X|.uliftFunctorObjHomeo (toTopObjMk ((X.uliftFunctorObjEquiv.{v} (op ⦋n⦌)).symm x) w) := by
  rw [toTopUliftHom, apply_toTopObjMk, Equiv.apply_symm_apply]
  simp only [TypeCat.ofHom_apply, Equiv.apply_symm_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_ofClass, toTopObjMk_def]

/-- Homeomorphism identifying the lifted realization of a standard simplex in `Type u` with the
realization of the standard simplex in `Type (max u v)`. -/
private noncomputable def toTopUliftSimplexHomeo (m : SimplexCategory) :
    TopCat.uliftFunctor.{v, u}.obj |stdSimplex.{u}.obj m| ≃ₜ |stdSimplex.{max u v}.obj m| :=
  (|stdSimplex.{u}.obj m|.uliftFunctorObjHomeo.symm.trans m.toTopHomeo.{u}).trans
    m.toTopHomeo.{max u v}.symm

private lemma toTopUliftSimplexHomeo_apply (m : SimplexCategory)
    (y : TopCat.uliftFunctor.{v, u}.obj |stdSimplex.{u}.obj m|) :
    toTopUliftSimplexHomeo.{v, u} m y =
      m.toTopHomeo.{max u v}.symm (m.toTopHomeo.{u}
        (|stdSimplex.{u}.obj m|.uliftFunctorObjHomeo.symm y)) :=
  (rfl)

/-- Morphism in `TopCat` underlying `toTopUliftSimplexHomeo`. -/
private noncomputable def toTopUliftSimplexHom (m : SimplexCategory) :
    TopCat.uliftFunctor.{v, u}.obj |stdSimplex.{u}.obj m| ⟶ |stdSimplex.{max u v}.obj m| :=
  ConcreteCategory.ofHom (toTopUliftSimplexHomeo.{v, u} m : C(_, _))

@[simp]
private lemma toTopUliftSimplexHom_apply (m : SimplexCategory)
    (y : TopCat.uliftFunctor.{v, u}.obj |stdSimplex.{u}.obj m|) :
    toTopUliftSimplexHom.{v, u} m y = toTopUliftSimplexHomeo.{v, u} m y :=
  (rfl)

private def toTopUliftCoconeLegHom {X : SSet.{u}} (j : CostructuredArrow stdSimplex.{u} X) :
    stdSimplex.{max u v}.obj j.left ⟶ uliftFunctor.{v, u}.obj X :=
  (uliftFunctorHomEquiv.{u, v} X j.left).symm j.hom

/-- Cocone assembling the inverse `TopCat.uliftFunctor.obj |X| ⟶ |uliftFunctor.obj X|` via
preservation of colimits by `toTop` and `TopCat.uliftFunctor`. -/
private noncomputable def toTopUliftCocone (X : SSet.{u}) :
    Cocone (CostructuredArrow.proj stdSimplex.{u} X ⋙ stdSimplex.{u} ⋙
      toTop.{u} ⋙ TopCat.uliftFunctor.{v, u}) where
  pt := |uliftFunctor.{v, u}.obj X|
  ι :=
    { app j := toTopUliftSimplexHom.{v, u} j.left ≫
        toTop.{max u v}.map (toTopUliftCoconeLegHom.{v, u} j)
      naturality j₁ j₂ α := by
        ext y
        simp only [Functor.comp_obj, CostructuredArrow.proj_obj, Functor.comp_map,
          CostructuredArrow.proj_map, Functor.const_obj_obj, Functor.const_obj_map,
          Category.comp_id, ConcreteCategory.comp_apply, toTopUliftSimplexHom_apply]
        have hy : toTopUliftSimplexHomeo.{v, u} j₂.left
              ((TopCat.uliftFunctor.{v, u}.map (toTop.{u}.map (stdSimplex.{u}.map α.left))) y) =
            toTop.{max u v}.map (stdSimplex.{max u v}.map α.left)
              (toTopUliftSimplexHomeo.{v, u} j₁.left y) := by
          rw [toTopUliftSimplexHomeo_apply, toTopUliftSimplexHomeo_apply,
            TopCat.uliftFunctorObjHomeo_symm_naturality_apply,
            SimplexCategory.toTopHomeo_naturality_apply,
            SimplexCategory.toTopHomeo_symm_naturality_apply]
        have hα : toTopUliftCoconeLegHom.{v, u} j₁ =
            SSet.stdSimplex.map α.left ≫ toTopUliftCoconeLegHom.{v, u} j₂ :=
          (uliftFunctorHomEquiv.{u, v} X j₁.left).injective (by
            rw [toTopUliftCoconeLegHom, toTopUliftCoconeLegHom, Equiv.apply_symm_apply,
              uliftFunctorHomEquiv_map_comp, Equiv.apply_symm_apply]
            exact (CostructuredArrow.w α).symm)
        rw [hy, hα, toTop.map_comp, ConcreteCategory.comp_apply] }

/-- Inverse morphism `TopCat.uliftFunctor.obj |X| ⟶ |uliftFunctor.obj X|`. -/
private noncomputable def toTopUliftInv (X : SSet.{u}) :
    TopCat.uliftFunctor.{v, u}.obj |X| ⟶ |uliftFunctor.{v, u}.obj X| :=
  (isColimitOfPreserves (toTop.{u} ⋙ TopCat.uliftFunctor.{v, u}) (stdSimplex.{u}.denseAt X)).desc
    (toTopUliftCocone.{v, u} X)

private lemma toTopUliftInv_uliftFunctorObjHomeo_toTopObjMk {X : SSet.{u}} {n : ℕ}
    (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    toTopUliftInv.{v, u} X (|X|.uliftFunctorObjHomeo (toTopObjMk x w)) =
      toTopObjMk (X.uliftFunctorObjEquiv.{v} (op ⦋n⦌) x) w := by
  let hc := isColimitOfPreserves (toTop.{u} ⋙ TopCat.uliftFunctor.{v, u}) (stdSimplex.{u}.denseAt X)
  let j : CostructuredArrow stdSimplex.{u} X := CostructuredArrow.mk (yonedaEquiv.symm x)
  let z : TopCat.uliftFunctor.{v, u}.obj |stdSimplex.{u}.obj ⦋n⦌| :=
    |stdSimplex.{u}.obj ⦋n⦌|.uliftFunctorObjHomeo (⦋n⦌.toTopHomeo.symm w)
  have hj : toTopUliftInv.{v, u} X
        (TopCat.uliftFunctor.{v, u}.map (toTop.{u}.map (yonedaEquiv.symm x)) z) =
      (toTopUliftSimplexHom.{v, u} ⦋n⦌ ≫
        toTop.{max u v}.map (toTopUliftCoconeLegHom.{v, u} j)) z :=
    ConcreteCategory.congr_hom (hc.fac (toTopUliftCocone.{v, u} X) j) z
  have hz : TopCat.uliftFunctor.{v, u}.map (toTop.{u}.map (yonedaEquiv.symm x)) z =
      |X|.uliftFunctorObjHomeo (toTopObjMk x w) := by
    rw [toTopObjMk_eq_toTop_map]
    exact TopCat.uliftFunctorObjHomeo_naturality_apply (toTop.{u}.map (yonedaEquiv.symm x))
      (⦋n⦌.toTopHomeo.symm w)
  rw [← hz, hj, ConcreteCategory.comp_apply, toTopUliftSimplexHom_apply]
  have hsymm : toTopUliftCoconeLegHom.{v, u} j =
      yonedaEquiv.symm (X.uliftFunctorObjEquiv.{v} (op ⦋n⦌) x) := by
    dsimp only [j, toTopUliftCoconeLegHom, CostructuredArrow.mk_left]
    rw [CostructuredArrow.mk_hom_eq_self, uliftFunctorHomEquiv_symm_eq_yonedaEquiv_symm,
      Equiv.apply_symm_apply]
  have hw : toTopUliftSimplexHomeo.{v, u} ⦋n⦌ z = ⦋n⦌.toTopHomeo.{max u v}.symm w := by
    rw [toTopUliftSimplexHomeo_apply]
    simp [z]
  rw [hsymm, hw, ← toTopObjMk_eq_toTop_map]

/-- Geometric realization of a universe-lifted simplicial set is isomorphic in `TopCat` to the
universe lift of its geometric realization (see `SSet.toTopUliftNatIso` for naturality in `X`). -/
noncomputable def toTopUliftIso (X : SSet.{u}) :
    |uliftFunctor.{v, u}.obj X| ≅ TopCat.uliftFunctor.{v, u}.obj |X| where
  hom := toTopUliftHom.{v, u} X
  inv := toTopUliftInv.{v, u} X
  hom_inv_id := toTop_hom_ext fun _ _ _ ↦ by
    simp only [ConcreteCategory.comp_apply, TopCat.id_app, toTopUliftHom_toTopObjMk,
      toTopUliftInv_uliftFunctorObjHomeo_toTopObjMk, Equiv.apply_symm_apply]
  inv_hom_id := by
    ext p
    obtain ⟨q, rfl⟩ := |X|.uliftFunctorObjHomeo.surjective p
    obtain ⟨_, _, _, rfl⟩ := exists_toTopObjMk q
    simp only [ConcreteCategory.comp_apply, TopCat.id_app,
      toTopUliftInv_uliftFunctorObjHomeo_toTopObjMk, toTopUliftHom_toTopObjMk,
      Equiv.symm_apply_apply]

@[simp]
lemma toTopUliftIso_hom_toTopObjMk {X : SSet.{u}} {n : ℕ}
    (x : (uliftFunctor.{v, u}.obj X) _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    (toTopUliftIso.{v, u} X).hom (toTopObjMk x w) =
      |X|.uliftFunctorObjHomeo (toTopObjMk ((X.uliftFunctorObjEquiv.{v} (op ⦋n⦌)).symm x) w) :=
  toTopUliftHom_toTopObjMk x w

@[simp]
lemma toTopUliftIso_inv_uliftFunctorObjHomeo_toTopObjMk {X : SSet.{u}} {n : ℕ}
    (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    (toTopUliftIso.{v, u} X).inv (|X|.uliftFunctorObjHomeo (toTopObjMk x w)) =
      toTopObjMk (X.uliftFunctorObjEquiv.{v} (op ⦋n⦌) x) w :=
  toTopUliftInv_uliftFunctorObjHomeo_toTopObjMk x w

/-- Natural isomorphism `|uliftFunctor.obj ·| ≅ uliftFunctor.obj |·|`. -/
noncomputable def toTopUliftNatIso :
    uliftFunctor.{v, u} ⋙ toTop.{max u v} ≅ toTop.{u} ⋙ TopCat.uliftFunctor.{v, u} :=
  NatIso.ofComponents toTopUliftIso fun f ↦ toTop_hom_ext fun _ _ _ ↦ by
    simp only [Functor.comp_obj, Functor.comp_map, ConcreteCategory.comp_apply,
      toTop_map_toTopObjMk, toTopUliftIso_hom_toTopObjMk,
      uliftFunctorObjEquiv_symm_uliftFunctor_map, TopCat.uliftFunctorObjHomeo_naturality_apply]

@[simp]
lemma toTopUliftNatIso_hom_app (X : SSet.{u}) :
    toTopUliftNatIso.{v, u}.hom.app X = (toTopUliftIso.{v, u} X).hom :=
  (rfl)

@[simp]
lemma toTopUliftNatIso_inv_app (X : SSet.{u}) :
    toTopUliftNatIso.{v, u}.inv.app X = (toTopUliftIso.{v, u} X).inv :=
  (rfl)

@[simp]
lemma toTopUliftNatIso_app (X : SSet.{u}) :
    toTopUliftNatIso.{v, u}.app X = toTopUliftIso.{v, u} X :=
  Iso.ext rfl

/-- Homeomorphism `|X| ≃ₜ |uliftFunctor.obj X|` between the geometric realization of `X` and the
geometric realization of its universe lift, matching `TopCat.uliftFunctorObjHomeo`. -/
noncomputable def toTopUliftHomeomorph (X : SSet.{u}) :
    |X| ≃ₜ |uliftFunctor.{v, u}.obj X| :=
  |X|.uliftFunctorObjHomeo.trans (TopCat.homeoOfIso (toTopUliftIso.{v, u} X)).symm

@[simp]
lemma toTopUliftHomeomorph_toTopObjMk {X : SSet.{u}} {n : ℕ}
    (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    toTopUliftHomeomorph.{v, u} X (toTopObjMk x w) =
      toTopObjMk (X.uliftFunctorObjEquiv.{v} (op ⦋n⦌) x) w := by
  simp [toTopUliftHomeomorph]

@[simp]
lemma toTopUliftHomeomorph_symm_toTopObjMk {X : SSet.{u}} {n : ℕ}
    (x : (uliftFunctor.{v, u}.obj X) _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    (toTopUliftHomeomorph.{v, u} X).symm (toTopObjMk x w) =
      toTopObjMk ((X.uliftFunctorObjEquiv.{v} (op ⦋n⦌)).symm x) w := by
  simp [toTopUliftHomeomorph]

@[simp]
lemma toTopUliftHomeomorph_toTopPoint {X : SSet.{u}} (x : X _⦋0⦌) :
    toTopUliftHomeomorph.{v, u} X (toTopPoint x) =
      toTopPoint (X.uliftFunctorObjEquiv.{v} (op ⦋0⦌) x) := by
  rw [toTopPoint_eq_toTopObjMk x default, toTopUliftHomeomorph_toTopObjMk, toTopObjMk_zero]

@[simp]
lemma toTopUliftHomeomorph_symm_toTopPoint {X : SSet.{u}}
    (x : (uliftFunctor.{v, u}.obj X) _⦋0⦌) :
    (toTopUliftHomeomorph.{v, u} X).symm (toTopPoint x) =
      toTopPoint ((X.uliftFunctorObjEquiv.{v} (op ⦋0⦌)).symm x) := by
  rw [toTopPoint_eq_toTopObjMk x default, toTopUliftHomeomorph_symm_toTopObjMk, toTopObjMk_zero]

@[simp]
lemma toTopUliftHomeomorph_naturality_apply {X Y : SSet.{u}} (f : X ⟶ Y) (p : |X|) :
    toTop.map (uliftFunctor.{v, u}.map f) (toTopUliftHomeomorph.{v, u} X p) =
      toTopUliftHomeomorph.{v, u} Y (toTop.map f p) := by
  obtain ⟨_, _, _, rfl⟩ := exists_toTopObjMk p
  simp

@[simp]
lemma toTopUliftHomeomorph_symm_naturality_apply {X Y : SSet.{u}} (f : X ⟶ Y)
    (p : |uliftFunctor.{v, u}.obj X|) :
    (toTopUliftHomeomorph.{v, u} Y).symm (toTop.map (uliftFunctor.{v, u}.map f) p) =
      toTop.map f ((toTopUliftHomeomorph.{v, u} X).symm p) := by
  obtain ⟨_, _, _, rfl⟩ := exists_toTopObjMk p
  simp

end ULift

end SSet

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
public import Mathlib.Topology.Category.TopCat.ULift
public import TauCeti.AlgebraicTopology.SimplicialSet.Discrete
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.AlgebraicTopology.SimplicialSet.ULift
public import TauCeti.AlgebraicTopology.TopologicalSimplex
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import TauCeti.CategoryTheory.Functor.KanExtension.Dense

/-!
# Open cells, faithfulness, discrete spaces, and universe lift of geometric realization

Every point of the geometric realization `|X|` of `X : SSet` has the form `SSet.toTopObjMk x w`
(`SSet.exists_toTopObjMk`). Stripping zero weights of `w` and taking the Eilenberg–Zilber
nondegenerate quotient expresses every point of `|X|` uniquely as `SSet.toTopObjMk s.simplex w₀`
with `s : X.N` and nowhere-vanishing coordinates (`SSet.toTopCellPointEquiv`), giving Milnor's
open-cell bijection. Evaluating at any interior point
(`SSet.toTopObjMk_injective_of_weights_ne_zero`, `SSet.toTopObjMk_barycenter_injective`) shows that
`sSetTopAdj.unit.app X` is a monomorphism, `SSet.toTop` is faithful, and `SSet.toTopPoint` is
injective. We also identify realizations of constant maps (`SSet.toTop_map_const`), discrete
simplicial sets (`SSet.toTopConstIso`, `SSet.toTopConstHomeomorph`), and universe lifts
(`SSet.toTopUliftNatIso`, `SSet.toTopUliftIso`, `SSet.toTopUliftHomeomorph`).

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

section Points

variable {X : SSet.{u}}

/-- The point of `|X|` given by a vertex `x` of `X` via `(sSetTopAdj.unit.app X).app _ x`. -/
noncomputable def toTopPoint {X : SSet.{u}} (x : X _⦋0⦌) : |X| :=
  TopCat.toSSetObj₀Equiv ((sSetTopAdj.unit.app X).app _ x)

lemma toTopPoint_def {X : SSet.{u}} (x : X _⦋0⦌) :
    toTopPoint x = TopCat.toSSetObj₀Equiv ((sSetTopAdj.unit.app X).app _ x) :=
  (rfl)

/-- The realization of a map sends the point of a vertex to the point of its image. -/
@[simp] lemma toTop_map_toTopPoint {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    toTop.map f (toTopPoint x) = toTopPoint (f.app _ x) := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (sSetTopAdj.unit.naturality f) _) x
  dsimp at h
  rw [toTopPoint, toTopPoint, h, TauCeti.TopCat.toSSetObj₀Equiv_toSSet_map_app]

/-- `toTopPoint` agrees with `toTopObjMk` at any point of `StdSimplex ℝ (Fin 1)`. -/
lemma toTopPoint_eq_toTopObjMk (x : X _⦋0⦌) (w : StdSimplex ℝ (Fin 1)) :
    toTopPoint x = toTopObjMk x w := by
  rw [toTopPoint_def, toTopObjMk_def, TopCat.toSSetObj₀Equiv_apply, Subsingleton.elim default w]

/-- On a `0`-simplex, `toTopObjMk` is independent of the coordinates and equals `toTopPoint`. -/
@[simp] lemma toTopObjMk_zero (x : X _⦋0⦌) (w : StdSimplex ℝ (Fin 1)) :
    toTopObjMk x w = toTopPoint x := (toTopPoint_eq_toTopObjMk x w).symm

/-- At `StdSimplex.single i`, `toTopObjMk x` gives the realized `i`-th vertex of `x`. -/
@[simp] lemma toTopObjMk_single {n : ℕ} (x : X _⦋n⦌) (i : Fin (n + 1)) :
    toTopObjMk x (StdSimplex.single i) =
      toTopPoint (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op x) := by
  have hs : (StdSimplex.single i : StdSimplex ℝ (Fin (n + 1))) =
      StdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i) (StdSimplex.single 0) := by
    rw [StdSimplex.map_single]; rfl
  rw [hs, ← toTopObjMk_map, toTopObjMk_zero]

/-- `toTopObjMk x w` is the image of `w` under the realized simplex `|Δ[n]| ⟶ |X|` of `x`. -/
lemma toTopObjMk_eq_toTop_map {n : ℕ} (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    toTopObjMk x w = toTop.map (yonedaEquiv.symm x) (⦋n⦌.toTopHomeo.symm w) := by
  rw [toTopObjMk_def, TauCeti.TopCat.toSSetObjEquiv_apply, sSetTopAdj_unit_app_app_down,
    ← ConcreteCategory.comp_apply, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- Evaluating `⦋n⦌.toTopHomeo` on a realized simplex `x` of `Δ[n]` pushes forward barycentric
coordinates along `stdSimplex.objEquiv x`. -/
@[simp] lemma stdSimplex.toTopHomeo_toTopObjMk {m n : ℕ} (x : (Δ[n] : SSet.{u}) _⦋m⦌)
    (w : StdSimplex ℝ (Fin (m + 1))) :
    ⦋n⦌.toTopHomeo.{u} (toTopObjMk x w) = w.map (stdSimplex.objEquiv.{u} x) := by
  obtain ⟨θ, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  rw [Equiv.apply_symm_apply, toTopObjMk_eq_toTop_map, ← yonedaEquiv_map θ,
    Equiv.symm_apply_apply, SimplexCategory.toTopHomeo_naturality_apply,
    Homeomorph.apply_symm_apply]

/-- Every point of `|X|` lies in the image of `toTopObjMk` for some simplex of `X`. -/
lemma exists_toTopObjMk (p : |X|) :
    ∃ (n : ℕ) (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))), p = toTopObjMk x w := by
  obtain ⟨⟨m, _, f⟩, y, hy⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (toTop ⋙ forget TopCat) (stdSimplex.{u}.denseAt X)) p
  dsimp at y hy; rw [Category.id_comp] at hy
  induction m using SimplexCategory.rec with | _ n => ?_
  exact ⟨n, yonedaEquiv f, ⦋n⦌.toTopHomeo y,
    by rw [toTopObjMk_eq_toTop_map, Equiv.symm_apply_apply, Homeomorph.symm_apply_apply, hy]⟩

/-- Every point of `|X|` can be joined by a path in `|X|` to the realization of a vertex of `X`. -/
lemma exists_joined_toTopPoint (p : |X|) : ∃ x : X _⦋0⦌, Joined (toTopPoint x) p := by
  obtain ⟨n, s, w, rfl⟩ := exists_toTopObjMk p
  exact ⟨X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op s, by
    rw [← toTopObjMk_single]; exact (PathConnectedSpace.joined _ w).map (continuous_toTopObjMk s)⟩

/-- The geometric realization `|X|` is nonempty if and only if `X` has a `0`-simplex. -/
@[simp] lemma nonempty_toTop_iff (X : SSet.{u}) : Nonempty |X| ↔ X.Nonempty :=
  ⟨fun ⟨p⟩ ↦ let ⟨_, x, _, _⟩ := exists_toTopObjMk p; .mk x, fun ⟨x⟩ ↦ ⟨toTopPoint x⟩⟩

/-- The geometric realization `|X|` is empty if and only if `X` has no `0`-simplices. -/
@[simp] lemma isEmpty_toTop_iff (X : SSet.{u}) : IsEmpty |X| ↔ IsEmpty (X _⦋0⦌) := by
  rw [← not_nonempty_iff, nonempty_toTop_iff, SSet.Nonempty, not_nonempty_iff]

instance isEmpty_toTop (X : SSet.{u}) [IsEmpty (X _⦋0⦌)] : IsEmpty |X| :=
  (isEmpty_toTop_iff X).2 ‹_›

instance nonempty_toTop (X : SSet.{u}) [X.Nonempty] : Nonempty |X| := (nonempty_toTop_iff X).2 ‹_›

/-- `SSet.const y` realizes to `TopCat.const (toTopPoint y)` (dual to `TopCat.toSSet_map_const`). -/
@[simp] lemma toTop_map_const (X : SSet.{u}) {Y : SSet.{u}} (y : Y _⦋0⦌) :
    toTop.map (SSet.const (X := X) y) = TopCat.const (X := |X|) (toTopPoint y) :=
  toTop_hom_ext fun _ _ _ ↦ by
    rw [toTop_map_toTopObjMk, SSet.const_app, TypeCat.ofHom_apply, toTopObjMk_map, toTopObjMk_zero,
      TopCat.const_apply]

end Points

section Discrete

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
  rw [h0, ← TopCat.toSSetObj₀Equiv_apply]
  exact Equiv.apply_symm_apply (TopCat.toSSetObj₀Equiv (X := TopCat.discrete.obj S)) s

private noncomputable def toTopConstInv (S : Type u) :
    TopCat.discrete.obj S ⟶ |(Functor.const SimplexCategoryᵒᵖ).obj S| :=
  TopCat.ofHom (X := TopCat.discrete.obj S)
    ⟨fun s ↦ toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s, continuous_bot⟩

private lemma toTopConstInv_apply (S : Type u) (s : S) :
    toTopConstInv S s = toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s := (rfl)

/-- Every point `toTopObjMk s w` in the realization of the constant simplicial set on `S` collapses
to the vertex `toTopPoint s`. -/
@[simp] lemma toTopObjMk_const (S : Type u) {n : ℕ} (s : S) (w : StdSimplex ℝ (Fin (n + 1))) :
    toTopObjMk (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s w =
      toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s := by
  have hs : s = ((Functor.const SimplexCategoryᵒᵖ).obj S).map
      (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op s := by simp
  conv_lhs => rw [hs]
  rw [toTopObjMk_map, toTopObjMk_zero]

/-- The geometric realization of the constant simplicial set on `S` is isomorphic in `TopCat` to
the discrete topological space on `S`. -/
noncomputable def toTopConstIso (S : Type u) :
    |(Functor.const SimplexCategoryᵒᵖ).obj S| ≅ TopCat.discrete.obj S where
  hom := toTopConstHom S
  inv := toTopConstInv S
  hom_inv_id := toTop_hom_ext fun _ _ _ ↦ by
    simp only [ConcreteCategory.comp_apply, TopCat.id_app, toTopObjMk_const,
      toTopConstHom_toTopPoint, toTopConstInv_apply]
  inv_hom_id := by ext s; exact toTopConstHom_toTopPoint S s

@[simp] lemma toTopConstIso_inv_apply (S : Type u) (s : S) :
    (toTopConstIso S).inv s = toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s :=
  toTopConstInv_apply S s

@[simp] lemma toTopConstIso_hom_toTopPoint (S : Type u) (s : S) :
    (toTopConstIso S).hom (toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s) = s :=
  toTopConstHom_toTopPoint S s

/-- Homeomorphism between `|(Functor.const SimplexCategoryᵒᵖ).obj S|` and discrete `S`. -/
noncomputable def toTopConstHomeomorph (S : Type u) :
    |(Functor.const SimplexCategoryᵒᵖ).obj S| ≃ₜ TopCat.discrete.obj S :=
  TopCat.homeoOfIso (toTopConstIso S)

@[simp] lemma toTopConstHomeomorph_toTopPoint (S : Type u) (s : S) :
    toTopConstHomeomorph S (toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s) = s := by
  rw [toTopConstHomeomorph, TopCat.homeoOfIso_apply]
  exact toTopConstIso_hom_toTopPoint S s

@[simp] lemma toTopConstHomeomorph_symm_apply (S : Type u) (s : TopCat.discrete.obj S) :
    (toTopConstHomeomorph S).symm s =
      toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s := by
  rw [toTopConstHomeomorph, TopCat.homeoOfIso_symm_apply]
  exact toTopConstIso_inv_apply S s

end Discrete

section Cells

/-- An open-cell point in Milnor's decomposition of `|X|`: a nondegenerate simplex `simplex : X.N`
together with nowhere-vanishing barycentric coordinates on `Fin (simplex.dim + 1)`. -/
structure ToTopCellPoint (X : SSet.{u}) : Type u where
  /-- The unique nondegenerate simplex whose open cell contains the point. -/
  simplex : X.N
  /-- The interior barycentric coordinates of the point in `simplex`. -/
  coords : StdSimplex ℝ (Fin (simplex.dim + 1))
  /-- Every barycentric coordinate is nonzero (hence strictly positive). -/
  coords_ne_zero : ∀ j, coords.weights j ≠ 0

@[ext (iff := false)]
lemma ToTopCellPoint.ext {X : SSet.{u}} {c₁ c₂ : X.ToTopCellPoint} (hs : c₁.simplex = c₂.simplex)
    (hc : ∀ j : Fin (c₁.simplex.dim + 1),
      c₁.coords.weights j = c₂.coords.weights (Fin.cast (by rw [hs]) j)) : c₁ = c₂ := by
  rcases c₁ with ⟨s₁, w₁, _⟩; rcases c₂ with ⟨s₂, w₂, _⟩
  dsimp only at hs hc; subst hs; congr; ext j; exact hc j

private lemma exists_cellPoint_decomp {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    ∃ c : X.ToTopCellPoint, ∃ (k r : ℕ) (ι : ⦋k⦌ ⟶ ⦋n⦌) (_ : Mono ι)
      (w₀ : StdSimplex ℝ (Fin (k + 1))) (hw₀ : ∀ j, w₀.weights j ≠ 0)
      (π : ⦋k⦌ ⟶ ⦋r⦌) (_ : Epi π) (z : X.nonDegenerate r),
      w = w₀.map ι ∧ X.map ι.op x = X.map π.op z.val ∧
      c = ⟨N.mk z.val z.property, w₀.map π,
        SimplexCategory.weights_stdSimplex_map_ne_zero_of_epi π hw₀⟩ := by
  obtain ⟨k, ι, _, w₀, hw₀, hw⟩ := SimplexCategory.exists_mono_stdSimplex_map_eq w
  obtain ⟨r, π, _, z, hz⟩ := X.exists_nonDegenerate (X.map ι.op x)
  exact ⟨_, k, r, ι, ‹_›, w₀, hw₀, π, ‹_›, z, hw, hz, rfl⟩

private noncomputable def toTopCellPointOfSimplex {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) : X.ToTopCellPoint :=
  (exists_cellPoint_decomp x w).choose

private lemma toTopCellPointOfSimplex_eq_of_decomp {X : SSet.{u}} {n k r : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) (ι : ⦋k⦌ ⟶ ⦋n⦌) [Mono ι]
    (w₀ : StdSimplex ℝ (Fin (k + 1))) (hw₀ : ∀ j, w₀.weights j ≠ 0) (hw : w = w₀.map ι)
    (π : ⦋k⦌ ⟶ ⦋r⦌) [Epi π] (z : X.nonDegenerate r) (hz : X.map ι.op x = X.map π.op z.val) :
    toTopCellPointOfSimplex x w =
      ⟨N.mk z.val z.property, w₀.map π,
        SimplexCategory.weights_stdSimplex_map_ne_zero_of_epi π hw₀⟩ := by
  obtain ⟨k', r', ι', _, w₀', hw₀', π', _, z', hw', hz', hcell⟩ :=
    (exists_cellPoint_decomp x w).choose_spec
  obtain rfl : k' = k :=
    SimplexCategory.eq_dim_of_mono_stdSimplex_map_eq hw₀' hw₀ (hw'.symm.trans hw)
  obtain ⟨rfl, rfl⟩ := SimplexCategory.eq_of_mono_stdSimplex_map_eq hw₀' hw₀ (hw'.symm.trans hw)
  obtain rfl : r' = r := X.unique_nonDegenerate_dim (X.map ι'.op x) π' z' hz' π z hz
  have hz_eq : z' = z := X.unique_nonDegenerate_simplex (X.map ι'.op x) π' z' hz' π z hz
  have hπ_eq : π' = π := X.unique_nonDegenerate_map (X.map ι'.op x) π' z' hz' π z hz
  subst hz_eq hπ_eq; exact hcell

private lemma toTopCellPointOfSimplex_map {X : SSet.{u}} {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (m + 1))) :
    toTopCellPointOfSimplex (X.map θ.op x) w = toTopCellPointOfSimplex x (w.map θ) := by
  obtain ⟨k, ι, _, w₀, hw₀, rfl⟩ := SimplexCategory.exists_mono_stdSimplex_map_eq w
  obtain ⟨k', hk'⟩ : ∃ k' : ℕ, image (ι ≫ θ) = ⦋k'⦌ :=
    ⟨(image (ι ≫ θ)).len, SimplexCategory.rec (fun _ ↦ rfl) (image (ι ≫ θ))⟩
  let e : ⦋k⦌ ⟶ ⦋k'⦌ := factorThruImage (ι ≫ θ) ≫ eqToHom hk'
  let ι' : ⦋k'⦌ ⟶ ⦋n⦌ := eqToHom hk'.symm ≫ image.ι (ι ≫ θ)
  have : Epi e := epi_comp _ _; have : Mono ι' := mono_comp _ _
  have hfac : e ≫ ι' = ι ≫ θ := by simp [e, ι', image.fac]
  obtain ⟨r, π', _, z, hz⟩ := X.exists_nonDegenerate (X.map ι'.op x)
  have hez_lhs : X.map ι.op (X.map θ.op x) = X.map (e ≫ π').op z.val := by
    rw [← Functor.map_comp_apply, ← op_comp, ← hfac, op_comp, Functor.map_comp_apply, hz,
      ← Functor.map_comp_apply, ← op_comp]
  have hw_rhs : (w₀.map ι).map θ = (w₀.map e).map ι' := by
    rw [StdSimplex.map_map, StdSimplex.map_map]
    exact congrArg (fun f : ⦋k⦌ ⟶ ⦋n⦌ ↦ w₀.map f) hfac.symm
  have : Epi (e ≫ π') := epi_comp _ _
  rw [toTopCellPointOfSimplex_eq_of_decomp (X.map θ.op x) (w₀.map ι) ι w₀ hw₀ rfl (e ≫ π') z
      hez_lhs,
    toTopCellPointOfSimplex_eq_of_decomp x ((w₀.map ι).map θ) ι' (w₀.map e)
      (SimplexCategory.weights_stdSimplex_map_ne_zero_of_epi e hw₀) hw_rhs π' z hz]
  exact ToTopCellPoint.ext rfl fun j ↦
    congrArg (·.weights j) ((StdSimplex.map_map w₀ e π' : (w₀.map e).map π' = w₀.map (e ≫ π')).symm)

private lemma toTopObjMk_toTopCellPointOfSimplex {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    toTopObjMk (toTopCellPointOfSimplex x w).simplex.simplex
        (toTopCellPointOfSimplex x w).coords =
      toTopObjMk x w := by
  obtain ⟨k, ι, _, w₀, hw₀, hw⟩ := SimplexCategory.exists_mono_stdSimplex_map_eq w
  obtain ⟨r, π, _, z, hz⟩ := X.exists_nonDegenerate (X.map ι.op x)
  refine (congrArg (fun c : X.ToTopCellPoint ↦ toTopObjMk c.simplex.simplex c.coords)
    (toTopCellPointOfSimplex_eq_of_decomp x w ι w₀ hw₀ hw π z hz)).trans ?_
  dsimp only [N.mk, S.mk]
  rw [← toTopObjMk_map π z.val w₀, ← hz, toTopObjMk_map ι x w₀, ← hw]

private lemma toTopCellPointOfSimplex_cellPoint {X : SSet.{u}} (c : X.ToTopCellPoint) :
    toTopCellPointOfSimplex c.simplex.simplex c.coords = c := by
  rcases c with ⟨s, w, hw⟩
  obtain ⟨d, ⟨y, hy⟩, rfl⟩ := s.mk_surjective
  have hid : (w : StdSimplex ℝ (Fin (d + 1))) = (w : StdSimplex ℝ (Fin (d + 1))).map (𝟙 ⦋d⦌) :=
    (StdSimplex.map_id _).symm
  exact (toTopCellPointOfSimplex_eq_of_decomp y w (𝟙 ⦋d⦌) w hw hid (𝟙 ⦋d⦌) ⟨y, hy⟩ rfl).trans
    (ToTopCellPoint.ext rfl fun j ↦ congrArg (·.weights j) hid.symm)

/-- Milnor's open-cell bijection: every point of `|X|` corresponds to a unique pair `(s, w)` of a
nondegenerate simplex `s : X.N` and nowhere-vanishing coordinates on `Fin (s.dim + 1)`. -/
noncomputable def toTopCellPointEquiv (X : SSet.{u}) : |X| ≃ X.ToTopCellPoint := by
  letI : TopologicalSpace X.ToTopCellPoint := ⊤
  let T : TopCat.{u} := TopCat.of X.ToTopCellPoint
  let φ : X ⟶ TopCat.toSSet.obj T :=
    { app m := ↾fun x ↦ (T.toSSetObjEquiv m).symm
        ⟨fun w ↦ toTopCellPointOfSimplex (n := m.unop.len)
          (X.map (eqToHom (by cases m using Opposite.rec; cases ‹SimplexCategory›; rfl)) x) w,
          continuous_top⟩
      naturality m₁ m₂ f := by
        obtain ⟨⟨d₁⟩, rfl⟩ : ∃ a, m₁ = op a := ⟨m₁.unop, rfl⟩
        obtain ⟨⟨d₂⟩, rfl⟩ : ∃ a, m₂ = op a := ⟨m₂.unop, rfl⟩
        obtain ⟨g, rfl⟩ : ∃ g : ⦋d₂⦌ ⟶ ⦋d₁⦌, f = g.op := ⟨f.unop, rfl⟩
        ext x
        apply (T.toSSetObjEquiv (op ⦋d₂⦌)).injective
        apply ContinuousMap.ext
        intro w
        simp only [TypeCat.Fun.toFun_apply, ConcreteCategory.comp_apply, TypeCat.ofHom_apply,
          TopCat.toSSetObjEquiv_naturality_apply, Equiv.apply_symm_apply, ContinuousMap.coe_mk,
          eqToHom_refl, CategoryTheory.Functor.map_id, types_id_apply]
        exact toTopCellPointOfSimplex_map g x w }
  let F : |X| ⟶ T := (sSetTopAdj.homEquiv X T).symm φ
  have hF {n : ℕ} (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
      F (toTopObjMk x w) = toTopCellPointOfSimplex x w := by
    rw [apply_toTopObjMk, Equiv.apply_symm_apply]
    simp only [φ, TypeCat.ofHom_apply, Equiv.apply_symm_apply, ContinuousMap.coe_mk,
      eqToHom_refl, CategoryTheory.Functor.map_id, types_id_apply]
  exact
    { toFun := F
      invFun c := toTopObjMk c.simplex.simplex c.coords
      left_inv p := by
        obtain ⟨n, x, w, rfl⟩ := exists_toTopObjMk p
        rw [hF]; exact toTopObjMk_toTopCellPointOfSimplex x w
      right_inv c := by dsimp only; rw [hF]; exact toTopCellPointOfSimplex_cellPoint c }

@[simp] lemma toTopCellPointEquiv_symm_apply {X : SSet.{u}} (c : X.ToTopCellPoint) :
    X.toTopCellPointEquiv.symm c = toTopObjMk c.simplex.simplex c.coords := (rfl)

@[simp] lemma toTopCellPointEquiv_toTopObjMk_of_weights_ne_zero {X : SSet.{u}} (s : X.N)
    (w : StdSimplex ℝ (Fin (s.dim + 1))) (hw : ∀ j, w.weights j ≠ 0) :
    X.toTopCellPointEquiv (toTopObjMk s.simplex w) = ⟨s, w, hw⟩ := by
  simpa using X.toTopCellPointEquiv.apply_symm_apply ⟨s, w, hw⟩

/-- Characterization of `X.toTopCellPointEquiv (toTopObjMk x w)` by any decomposition of `(x, w)`
along `ι : ⦋k⦌ ⟶ ⦋n⦌` carrying interior coordinates `w₀` and `π : ⦋k⦌ ⟶ ⦋r⦌` (`[Epi π]`) onto a
nondegenerate simplex `z`. -/
lemma toTopCellPointEquiv_toTopObjMk_eq_of_decomp {X : SSet.{u}} {n k r : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) (ι : ⦋k⦌ ⟶ ⦋n⦌) (w₀ : StdSimplex ℝ (Fin (k + 1)))
    (hw₀ : ∀ j, w₀.weights j ≠ 0) (hw : w = w₀.map ι) (π : ⦋k⦌ ⟶ ⦋r⦌) [Epi π]
    (z : X.nonDegenerate r) (hz : X.map ι.op x = X.map π.op z.val) :
    X.toTopCellPointEquiv (toTopObjMk x w) =
      ⟨N.mk z.val z.property, w₀.map π,
        SimplexCategory.weights_stdSimplex_map_ne_zero_of_epi π hw₀⟩ := by
  apply X.toTopCellPointEquiv.symm.injective
  rw [Equiv.symm_apply_apply, toTopCellPointEquiv_symm_apply]; dsimp only [N.mk, S.mk]
  rw [← toTopObjMk_map π z.val w₀, ← hz, toTopObjMk_map ι x w₀, ← hw]

/-- A realized vertex `toTopPoint x` lies in the `0`-dimensional open cell of `x`. -/
@[simp] lemma toTopCellPointEquiv_toTopPoint {X : SSet.{u}} (x : X _⦋0⦌) :
    X.toTopCellPointEquiv (toTopPoint x) =
      ⟨N.mk x (by simp), StdSimplex.single 0, fun j ↦ by
        obtain rfl : j = 0 := Fin.ext (by dsimp [N.mk, S.mk] at j ⊢; omega); simp⟩ := by
  rw [toTopPoint_eq_toTopObjMk x (StdSimplex.single 0)]
  exact toTopCellPointEquiv_toTopObjMk_of_weights_ne_zero (N.mk x (by simp)) (StdSimplex.single 0) _

/-- The nondegenerate simplex carrying `toTopObjMk x w` lies in `Subcomplex.ofSimplex x`. -/
lemma toTopCellPointEquiv_toTopObjMk_subcomplex_le {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    (X.toTopCellPointEquiv (toTopObjMk x w)).simplex.subcomplex ≤ Subcomplex.ofSimplex x := by
  obtain ⟨k, ι, _, w₀, hw₀, hw⟩ := SimplexCategory.exists_mono_stdSimplex_map_eq w
  obtain ⟨r, π, _, z, hz⟩ := X.exists_nonDegenerate (X.map ι.op x)
  rw [toTopCellPointEquiv_toTopObjMk_eq_of_decomp x w ι w₀ hw₀ hw π z hz]
  exact (S.subcomplex_eq_of_epi (S.mk (X.map ι.op x)) (S.mk z.val) π hz.symm).symm.trans_le
    (S.subcomplex_map_le (S.mk (X.map ι.op x)) (S.mk x) ι rfl)

/-- The open cell of `toTopObjMk x w` has dimension at most `n`. -/
lemma toTopCellPointEquiv_toTopObjMk_dim_le {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    (X.toTopCellPointEquiv (toTopObjMk x w)).simplex.dim ≤ n := by
  obtain ⟨k, ι, _, w₀, hw₀, hw⟩ := SimplexCategory.exists_mono_stdSimplex_map_eq w
  obtain ⟨r, π, _, z, hz⟩ := X.exists_nonDegenerate (X.map ι.op x)
  rw [toTopCellPointEquiv_toTopObjMk_eq_of_decomp x w ι w₀ hw₀ hw π z hz]
  exact (SimplexCategory.len_le_of_epi π).trans (SimplexCategory.len_le_of_mono ι)

/-- A monomorphism `f : X ⟶ Y` of simplicial sets preserves open cells under `toTop.map f`. -/
@[simp] lemma toTopCellPointEquiv_toTop_map {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (p : |X|) :
    Y.toTopCellPointEquiv (toTop.map f p) =
      ⟨N.mk (f.app (op ⦋(X.toTopCellPointEquiv p).simplex.dim⦌)
          (X.toTopCellPointEquiv p).simplex.simplex)
        ((nonDegenerate_iff_of_mono f _).mpr (X.toTopCellPointEquiv p).simplex.nonDegenerate),
        (X.toTopCellPointEquiv p).coords, (X.toTopCellPointEquiv p).coords_ne_zero⟩ := by
  conv_lhs =>
    rw [← X.toTopCellPointEquiv.symm_apply_apply p, toTopCellPointEquiv_symm_apply,
      toTop_map_toTopObjMk]
  exact toTopCellPointEquiv_toTopObjMk_of_weights_ne_zero
    (N.mk (f.app _ (X.toTopCellPointEquiv p).simplex.simplex)
      ((nonDegenerate_iff_of_mono f _).mpr (X.toTopCellPointEquiv p).simplex.nonDegenerate))
    (X.toTopCellPointEquiv p).coords (X.toTopCellPointEquiv p).coords_ne_zero

/-- Evaluating `toTopObjMk · w` at any interior point `w` of `StdSimplex ℝ (Fin (n + 1))` is
injective on `n`-simplices. -/
theorem toTopObjMk_injective_of_weights_ne_zero (X : SSet.{u}) {n : ℕ}
    {w : StdSimplex ℝ (Fin (n + 1))} (hw : ∀ j, w.weights j ≠ 0) :
    Function.Injective fun x : X _⦋n⦌ ↦ toTopObjMk x w := fun x₁ x₂ h ↦ by
  dsimp only at h
  obtain ⟨r₁, π₁, _, z₁, rfl⟩ := X.exists_nonDegenerate x₁
  obtain ⟨r₂, π₂, _, z₂, rfl⟩ := X.exists_nonDegenerate x₂
  rw [toTopObjMk_map, toTopObjMk_map] at h
  have hc : X.toTopCellPointEquiv (toTopObjMk (N.mk z₁.val z₁.property).simplex (w.map π₁)) =
      X.toTopCellPointEquiv (toTopObjMk (N.mk z₂.val z₂.property).simplex (w.map π₂)) :=
    congrArg X.toTopCellPointEquiv h
  rw [toTopCellPointEquiv_toTopObjMk_of_weights_ne_zero (N.mk z₁.val z₁.property) (w.map π₁)
      (SimplexCategory.weights_stdSimplex_map_ne_zero_of_epi π₁ hw),
    toTopCellPointEquiv_toTopObjMk_of_weights_ne_zero (N.mk z₂.val z₂.property) (w.map π₂)
      (SimplexCategory.weights_stdSimplex_map_ne_zero_of_epi π₂ hw)] at hc
  have hsimp : N.mk z₁.val z₁.property = N.mk z₂.val z₂.property :=
    congrArg ToTopCellPoint.simplex hc
  obtain rfl : r₁ = r₂ := congrArg (·.dim) hsimp
  obtain rfl : z₁ = z₂ := Subtype.ext (by simpa [N.mk, S.mk] using hsimp)
  have hcoords : w.map π₁ = w.map π₂ := by injection hc
  rw [SimplexCategory.eq_of_stdSimplex_map_eq_of_weights_ne_zero hw hcoords]

/-- Evaluating `toTopObjMk · StdSimplex.barycenter` on `n`-simplices is injective. -/
theorem toTopObjMk_barycenter_injective (X : SSet.{u}) (n : ℕ) :
    Function.Injective fun x : X _⦋n⦌ ↦
      toTopObjMk x (StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))) :=
  toTopObjMk_injective_of_weights_ne_zero X fun _ ↦ by
    rw [StdSimplex.weights_barycenter_apply, Fintype.card_fin]; positivity

/-- The unit `X ⟶ Sing |X|` of `sSetTopAdj` is componentwise injective. -/
theorem sSetTopAdj_unit_app_app_injective (X : SSet.{u}) (m : SimplexCategoryᵒᵖ) :
    Function.Injective ((sSetTopAdj.unit.app X).app m) := by
  rcases m with ⟨⟨n⟩⟩
  exact fun _ _ h ↦ toTopObjMk_barycenter_injective X n (by simp only [toTopObjMk_def, h])

/-- The unit `X ⟶ Sing |X|` of `sSetTopAdj` is a monomorphism. -/
instance mono_sSetTopAdj_unit_app (X : SSet.{u}) : Mono (sSetTopAdj.unit.app X) := by
  rw [NatTrans.mono_iff_mono_app]
  exact fun m ↦ (mono_iff_injective _).2 (sSetTopAdj_unit_app_app_injective X m)

/-- The geometric realization functor `SSet.toTop` is faithful. -/
instance : toTop.{u}.Faithful := sSetTopAdj.faithful_L_of_mono_unit_app

/-- Distinct `0`-simplices of `X` map to distinct points of `|X|`. -/
theorem toTopPoint_injective (X : SSet.{u}) : Function.Injective (toTopPoint (X := X)) :=
  fun _ _ h ↦ toTopObjMk_barycenter_injective X 0 (by simpa using h)

@[simp] lemma toTopPoint_inj {X : SSet.{u}} {x₁ x₂ : X _⦋0⦌} :
    toTopPoint x₁ = toTopPoint x₂ ↔ x₁ = x₂ := (toTopPoint_injective X).eq_iff

end Cells

section ULift

private def stdSimplexUliftIso :
    stdSimplex.{u} ⋙ uliftFunctor.{v, u} ≅ stdSimplex.{max u v} :=
  NatIso.ofComponents
    (fun _ ↦ NatIso.ofComponents fun _ ↦
      Equiv.toIso (Equiv.ulift.trans (Equiv.ulift.trans Equiv.ulift.symm)))
    fun _ ↦ rfl

private noncomputable def simplexToTopUliftIso :
    SimplexCategory.toTop.{max u v} ≅
      SimplexCategory.toTop.{u} ⋙ TopCat.uliftFunctor.{v, u} :=
  NatIso.ofComponents
    (fun m ↦ TopCat.isoOfHomeo
      ((SimplexCategory.toTop₀.obj m).uliftFunctorObjHomeo.{max u v}.symm.trans
        ((SimplexCategory.toTop₀.obj m).uliftFunctorObjHomeo.{u}.trans
          (SimplexCategory.toTop.{u}.obj m).uliftFunctorObjHomeo.{v})))
    fun _ ↦ by ext ⟨w⟩; rfl

/-- Evaluating `simplexToTopUliftIso.hom.app m` on the realized standard simplex point of `w`
recovers the universe lift of the corresponding point in `SimplexCategory.toTop.{u}.obj m`. -/
private lemma simplexToTopUliftIso_hom_app_toTopSimplex (m : SimplexCategory)
    (w : StdSimplex ℝ (Fin (m.len + 1))) :
    simplexToTopUliftIso.{v, u}.hom.app m
        (toTopSimplex.{max u v}.hom.app m (m.toTopHomeo.{max u v}.symm w)) =
      (SimplexCategory.toTop.{u}.obj m).uliftFunctorObjHomeo.{v}
        (toTopSimplex.{u}.hom.app m (m.toTopHomeo.{u}.symm w)) := by
  apply ((SimplexCategory.toTop.{u}.obj m).uliftFunctorObjHomeo.{v}).symm.injective
  rw [Homeomorph.symm_apply_apply]
  apply ((SimplexCategory.toTop₀.obj m).uliftFunctorObjHomeo.{u}).symm.injective
  -- By definition, `SimplexCategory.toTop.obj m = TopCat.uliftFunctor.obj (toTop₀.obj m)`,
  -- `TopCat.uliftFunctorObjHomeo = Homeomorph.ulift.symm`, and
  -- `m.toTopHomeo = (TopCat.homeoOfIso (toTopSimplex.app m)).trans Homeomorph.ulift`.
  -- Stripping the two `uliftFunctorObjHomeo` layers cancels those in `simplexToTopUliftIso` and
  -- reduces both sides to `m.toTopHomeo (m.toTopHomeo.symm w)`.
  exact (m.toTopHomeo.{max u v}.apply_symm_apply w).trans
    (m.toTopHomeo.{u}.apply_symm_apply w).symm

private noncomputable def toTopUliftRestrictIso :
    stdSimplex.{u} ⋙ uliftFunctor.{v, u} ⋙ toTop.{max u v} ≅
      stdSimplex.{u} ⋙ toTop.{u} ⋙ TopCat.uliftFunctor.{v, u} :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight stdSimplexUliftIso.{v, u} toTop.{max u v} ≪≫
    toTopSimplex.{max u v} ≪≫
    simplexToTopUliftIso.{v, u} ≪≫
    Functor.isoWhiskerRight toTopSimplex.{u}.symm TopCat.uliftFunctor.{v, u} ≪≫
    Functor.associator _ _ _

/-- Natural isomorphism `|uliftFunctor.obj ·| ≅ uliftFunctor.obj |·|`. -/
noncomputable def toTopUliftNatIso :
    uliftFunctor.{v, u} ⋙ toTop.{max u v} ≅ toTop.{u} ⋙ TopCat.uliftFunctor.{v, u} :=
  haveI : PreservesColimitsOfSize.{0, u} uliftFunctor.{v, u} :=
    inferInstanceAs (PreservesColimitsOfSize.{0, u}
      ((Functor.whiskeringRight SimplexCategoryᵒᵖ (Type u) (Type max u v)).obj
        CategoryTheory.uliftFunctor.{v, u}))
  haveI := Functor.IsDense.isLeftKanExtension_id stdSimplex.{u}
    (uliftFunctor.{v, u} ⋙ toTop.{max u v})
  haveI := Functor.IsDense.isLeftKanExtension_id stdSimplex.{u}
    (toTop.{u} ⋙ TopCat.uliftFunctor.{v, u})
  Functor.leftKanExtensionUniqueOfIso
    (uliftFunctor.{v, u} ⋙ toTop.{max u v}) (𝟙 _)
    toTopUliftRestrictIso.{v, u}
    (toTop.{u} ⋙ TopCat.uliftFunctor.{v, u}) (𝟙 _)

/-- Geometric realization of a universe-lifted simplicial set is isomorphic in `TopCat` to the
universe lift of its geometric realization (see `SSet.toTopUliftNatIso` for naturality in `X`). -/
noncomputable def toTopUliftIso (X : SSet.{u}) :
    |uliftFunctor.{v, u}.obj X| ≅ TopCat.uliftFunctor.{v, u}.obj |X| :=
  toTopUliftNatIso.{v, u}.app X

@[simp] lemma toTopUliftNatIso_hom_app (X : SSet.{u}) :
    toTopUliftNatIso.{v, u}.hom.app X = (toTopUliftIso.{v, u} X).hom := (rfl)

@[simp] lemma toTopUliftNatIso_inv_app (X : SSet.{u}) :
    toTopUliftNatIso.{v, u}.inv.app X = (toTopUliftIso.{v, u} X).inv := (rfl)

@[simp] lemma toTopUliftNatIso_app (X : SSet.{u}) :
    toTopUliftNatIso.{v, u}.app X = toTopUliftIso.{v, u} X := (rfl)

private lemma toTopUliftNatIso_hom_app_stdSimplex (m : SimplexCategory) :
    toTopUliftNatIso.{v, u}.hom.app (stdSimplex.{u}.obj m) =
      toTopUliftRestrictIso.{v, u}.hom.app m := by
  have : PreservesColimitsOfSize.{0, u} uliftFunctor.{v, u} :=
    inferInstanceAs (PreservesColimitsOfSize.{0, u}
      ((Functor.whiskeringRight SimplexCategoryᵒᵖ (Type u) (Type max u v)).obj
        CategoryTheory.uliftFunctor.{v, u}))
  have := Functor.IsDense.isLeftKanExtension_id stdSimplex.{u}
    (uliftFunctor.{v, u} ⋙ toTop.{max u v})
  have := Functor.IsDense.isLeftKanExtension_id stdSimplex.{u}
    (toTop.{u} ⋙ TopCat.uliftFunctor.{v, u})
  have h := Functor.descOfIsLeftKanExtension_fac_app
    (uliftFunctor.{v, u} ⋙ toTop.{max u v}) (𝟙 _)
    (toTop.{u} ⋙ TopCat.uliftFunctor.{v, u}) (toTopUliftRestrictIso.{v, u}.hom ≫ 𝟙 _) m
  simpa [toTopUliftNatIso, Functor.leftKanExtensionUniqueOfIso] using h

@[simp]
lemma toTopUliftIso_hom_toTopObjMk {X : SSet.{u}} {n : ℕ}
    (x : (uliftFunctor.{v, u}.obj X) _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    (toTopUliftIso.{v, u} X).hom (toTopObjMk x w) =
      |X|.uliftFunctorObjHomeo (toTopObjMk ((X.uliftFunctorObjEquiv.{v} (op ⦋n⦌)).symm x) w) := by
  let x' : X _⦋n⦌ := (X.uliftFunctorObjEquiv.{v} (op ⦋n⦌)).symm x
  have hfac : yonedaEquiv.symm x =
      stdSimplexUliftIso.{v, u}.inv.app ⦋n⦌ ≫ uliftFunctor.{v, u}.map (yonedaEquiv.symm x') := by
    apply yonedaEquiv.injective
    rw [Equiv.apply_symm_apply, yonedaEquiv_comp]
    have h1 : yonedaEquiv (stdSimplexUliftIso.{v, u}.inv.app ⦋n⦌) =
        (stdSimplex.{u}.obj ⦋n⦌).uliftFunctorObjEquiv (op ⦋n⦌) (yonedaEquiv (𝟙 _)) := by
      apply ULift.ext
      rw [uliftFunctorObjEquiv_down]
      rfl
    rw [h1, uliftFunctor_map_uliftFunctorObjEquiv, yonedaEquiv_symm_app_id, Equiv.apply_symm_apply]
  have hnat := ConcreteCategory.congr_hom
    (toTopUliftNatIso.{v, u}.hom.naturality (yonedaEquiv.symm x'))
    (toTop.{max u v}.map (stdSimplexUliftIso.{v, u}.inv.app ⦋n⦌) (⦋n⦌.toTopHomeo.symm w))
  have hstd : toTopUliftNatIso.{v, u}.hom.app (stdSimplex.{u}.obj ⦋n⦌)
        (toTop.{max u v}.map (stdSimplexUliftIso.{v, u}.inv.app ⦋n⦌) (⦋n⦌.toTopHomeo.symm w)) =
      |stdSimplex.{u}.obj ⦋n⦌|.uliftFunctorObjHomeo (⦋n⦌.toTopHomeo.symm w) := by
    rw [toTopUliftNatIso_hom_app_stdSimplex, toTopUliftRestrictIso]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.associator_hom_app,
      Category.id_comp, Category.comp_id, ConcreteCategory.comp_apply,
      ← Functor.map_comp_apply, Iso.inv_hom_id_app]
    rw [CategoryTheory.Functor.map_id, TopCat.id_app,
      simplexToTopUliftIso_hom_app_toTopSimplex,
      TopCat.uliftFunctorObjHomeo_naturality_apply, ← ConcreteCategory.comp_apply,
      Iso.hom_inv_id_app, TopCat.id_app]
    rfl
  rw [toTopObjMk_eq_toTop_map, hfac, toTop.map_comp, ConcreteCategory.comp_apply,
    ← toTopUliftNatIso_hom_app]
  dsimp only [Functor.comp_obj, Functor.comp_map] at hnat
  rw [← ConcreteCategory.comp_apply, hnat, ConcreteCategory.comp_apply, hstd,
    TopCat.uliftFunctorObjHomeo_naturality_apply, ← toTopObjMk_eq_toTop_map]

@[simp]
lemma toTopUliftIso_inv_uliftFunctorObjHomeo_toTopObjMk {X : SSet.{u}} {n : ℕ}
    (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    (toTopUliftIso.{v, u} X).inv (|X|.uliftFunctorObjHomeo (toTopObjMk x w)) =
      toTopObjMk (X.uliftFunctorObjEquiv.{v} (op ⦋n⦌) x) w := by
  have h := toTopUliftIso_hom_toTopObjMk.{v, u} (X.uliftFunctorObjEquiv.{v} (op ⦋n⦌) x) w
  rw [Equiv.symm_apply_apply] at h
  rw [← h, ← ConcreteCategory.comp_apply, Iso.hom_inv_id, TopCat.id_app]

@[simp]
lemma toTopUliftIso_hom_toTopPoint {X : SSet.{u}} (x : (uliftFunctor.{v, u}.obj X) _⦋0⦌) :
    (toTopUliftIso.{v, u} X).hom (toTopPoint x) =
      |X|.uliftFunctorObjHomeo (toTopPoint ((X.uliftFunctorObjEquiv.{v} (op ⦋0⦌)).symm x)) := by
  rw [toTopPoint_eq_toTopObjMk x default, toTopUliftIso_hom_toTopObjMk, toTopObjMk_zero]

@[simp]
lemma toTopUliftIso_inv_uliftFunctorObjHomeo_toTopPoint {X : SSet.{u}} (x : X _⦋0⦌) :
    (toTopUliftIso.{v, u} X).inv (|X|.uliftFunctorObjHomeo (toTopPoint x)) =
      toTopPoint (X.uliftFunctorObjEquiv.{v} (op ⦋0⦌) x) := by
  rw [toTopPoint_eq_toTopObjMk x default, toTopUliftIso_inv_uliftFunctorObjHomeo_toTopObjMk,
    toTopObjMk_zero]

/-- Homeomorphism `|X| ≃ₜ |uliftFunctor.obj X|` between the geometric realization of `X` and the
geometric realization of its universe lift, matching `TopCat.uliftFunctorObjHomeo`. -/
noncomputable def toTopUliftHomeomorph (X : SSet.{u}) :
    |X| ≃ₜ |uliftFunctor.{v, u}.obj X| :=
  |X|.uliftFunctorObjHomeo.trans (TopCat.homeoOfIso (toTopUliftIso.{v, u} X)).symm

@[simp] lemma toTopUliftHomeomorph_toTopObjMk {X : SSet.{u}} {n : ℕ}
    (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    toTopUliftHomeomorph.{v, u} X (toTopObjMk x w) =
      toTopObjMk (X.uliftFunctorObjEquiv.{v} (op ⦋n⦌) x) w := by
  simp [toTopUliftHomeomorph]

@[simp] lemma toTopUliftHomeomorph_symm_toTopObjMk {X : SSet.{u}} {n : ℕ}
    (x : (uliftFunctor.{v, u}.obj X) _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    (toTopUliftHomeomorph.{v, u} X).symm (toTopObjMk x w) =
      toTopObjMk ((X.uliftFunctorObjEquiv.{v} (op ⦋n⦌)).symm x) w := by
  simp [toTopUliftHomeomorph]

@[simp] lemma toTopUliftHomeomorph_toTopPoint {X : SSet.{u}} (x : X _⦋0⦌) :
    toTopUliftHomeomorph.{v, u} X (toTopPoint x) =
      toTopPoint (X.uliftFunctorObjEquiv.{v} (op ⦋0⦌) x) := by
  simp [toTopUliftHomeomorph]

@[simp] lemma toTopUliftHomeomorph_symm_toTopPoint {X : SSet.{u}}
    (x : (uliftFunctor.{v, u}.obj X) _⦋0⦌) :
    (toTopUliftHomeomorph.{v, u} X).symm (toTopPoint x) =
      toTopPoint ((X.uliftFunctorObjEquiv.{v} (op ⦋0⦌)).symm x) := by
  simp [toTopUliftHomeomorph]

@[simp] lemma toTopUliftHomeomorph_naturality_apply {X Y : SSet.{u}} (f : X ⟶ Y) (p : |X|) :
    toTop.map (uliftFunctor.{v, u}.map f) (toTopUliftHomeomorph.{v, u} X p) =
      toTopUliftHomeomorph.{v, u} Y (toTop.map f p) := by
  obtain ⟨_, _, _, rfl⟩ := exists_toTopObjMk p; simp

@[simp] lemma toTopUliftHomeomorph_symm_naturality_apply {X Y : SSet.{u}} (f : X ⟶ Y)
    (p : |uliftFunctor.{v, u}.obj X|) :
    (toTopUliftHomeomorph.{v, u} Y).symm (toTop.map (uliftFunctor.{v, u}.map f) p) =
      toTop.map f ((toTopUliftHomeomorph.{v, u} X).symm p) := by
  obtain ⟨_, _, _, rfl⟩ := exists_toTopObjMk p; simp

end ULift

end SSet

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
public import Mathlib.Topology.Category.TopCat.ULift
public import TauCeti.AlgebraicTopology.SimplicialSet.Realization.PiZero
public import TauCeti.AlgebraicTopology.SimplicialSet.ULift
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import TauCeti.Geometry.Convex.ConvexSpace.Defs

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

Evaluating at the barycenter of the standard simplex, whose pushforwards along monotone maps
determine the maps via cumulative weight sums, shows that `x ↦ SSet.toTopObjMk x barycenter` is
injective in every dimension (`SSet.toTopObjMk_barycenter_injective`). Consequently the unit
`X ⟶ Sing |X|` of `sSetTopAdj` is a monomorphism (`SSet.mono_sSetTopAdj_unit_app`), the geometric
realization functor `SSet.toTop` is faithful, and the vertex map `SSet.toTopPoint : X _⦋0⦌ → |X|`
is injective (`SSet.toTopPoint_injective`).

We also record the basic point-set identifications of `|X|`:
* `SSet.nonempty_toTop_iff`, `SSet.isEmpty_toTop_iff`: `|X|` is nonempty (resp. empty) precisely
  when `X` has a `0`-simplex (resp. no `0`-simplices).
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

section Points

variable {X : SSet.{u}}

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
    (isColimitOfPreserves (toTop ⋙ forget TopCat) (denseAtUliftYoneda X)) p
  dsimp at y hy
  rw [Category.id_comp] at hy
  induction m using SimplexCategory.rec with | _ n => ?_
  let f' : (Δ[n] : SSet.{u}) ⟶ X := f
  let y' : |(Δ[n] : SSet.{u})| := y
  refine ⟨n, yonedaEquiv f', ⦋n⦌.toTopHomeo y', ?_⟩
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

end Points

section Discrete

/-- The geometric realization of the constant (discrete) simplicial set on `S` is isomorphic in
`TopCat` to the discrete topological space on `S`. -/
noncomputable def toTopConstIso (S : Type u) :
    |(Functor.const SimplexCategoryᵒᵖ).obj S| ≅ TopCat.discrete.obj S := by
  let homMap : |(Functor.const SimplexCategoryᵒᵖ).obj S| ⟶ TopCat.discrete.obj S :=
    (sSetTopAdj.homEquiv _ (TopCat.discrete.obj S)).symm
      ((constHomEquiv S).symm fun s ↦ TopCat.toSSetObj₀Equiv (X := TopCat.discrete.obj S).symm s)
  let invMap : TopCat.discrete.obj S ⟶ |(Functor.const SimplexCategoryᵒᵖ).obj S| :=
    TopCat.ofHom (X := TopCat.discrete.obj S)
      ⟨fun s ↦ toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s, continuous_bot⟩
  have hpt (s : S) :
      homMap (toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s) = s := by
    let s₀ : ((Functor.const SimplexCategoryᵒᵖ).obj S) _⦋0⦌ := s
    change homMap (toTopPoint s₀) = s
    rw [toTopPoint_eq_toTopObjMk s₀ default, apply_toTopObjMk, Equiv.apply_symm_apply]
    have h0 := constHomEquiv_symm_app_zero S
      (fun t ↦ TopCat.toSSetObj₀Equiv (X := TopCat.discrete.obj S).symm t) s
    dsimp [s₀] at h0 ⊢
    rw [h0]; rfl
  exact
    { hom := homMap
      inv := invMap
      hom_inv_id := toTop_hom_ext fun n x w ↦ by
        have hx : x = ((Functor.const SimplexCategoryᵒᵖ).obj S).map
            (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op x := rfl
        have hw : toTopObjMk (X := (Functor.const SimplexCategoryᵒᵖ).obj S) x w =
            toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) x := by
          conv_lhs => rw [hx]
          rw [toTopObjMk_map, toTopObjMk_zero]
        simp only [ConcreteCategory.comp_apply, TopCat.id_app, hw]
        exact congrArg invMap (hpt x)
      inv_hom_id := by ext s; exact hpt s }

@[simp]
lemma toTopConstIso_inv_apply (S : Type u) (s : S) :
    (toTopConstIso S).inv s = toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s :=
  (rfl)

@[simp]
lemma toTopConstIso_hom_toTopPoint (S : Type u) (s : S) :
    (toTopConstIso S).hom (toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s) = s := by
  change ((toTopConstIso S).inv ≫ (toTopConstIso S).hom) s = (𝟙 (TopCat.discrete.obj S)) s
  rw [(toTopConstIso S).inv_hom_id]

/-- The homeomorphism between the geometric realization of the constant simplicial set on `S` and
the discrete topological space on `S`. -/
noncomputable def toTopConstHomeomorph (S : Type u) :
    |(Functor.const SimplexCategoryᵒᵖ).obj S| ≃ₜ TopCat.discrete.obj S :=
  TopCat.homeoOfIso (toTopConstIso S)

@[simp]
lemma toTopConstHomeomorph_toTopPoint (S : Type u) (s : S) :
    toTopConstHomeomorph S (toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s) = s :=
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

/-- Every point `w` of a standard simplex comes from a face with nowhere-vanishing coordinates.
Adapted from the face-stripping step of `SSet.prodStdSimplex.exists_injective_toTopObjMk_eq` in
`TauCeti/AlgebraicTopology/SimplicialSet/PrismRealization.lean`. -/
private lemma exists_mono_map_eq_of_stdSimplex :
    ∀ {n : ℕ} (w : StdSimplex ℝ (Fin (n + 1))),
      ∃ (k : ℕ) (ι : ⦋k⦌ ⟶ ⦋n⦌) (_ : Mono ι) (w₀ : StdSimplex ℝ (Fin (k + 1))),
        (∀ j, w₀.weights j ≠ 0) ∧ w = w₀.map ι := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w
    by_cases h0 : ∃ j, w.weights j = 0
    · obtain ⟨j, hj⟩ := h0
      obtain _ | n := n
      · rw [Subsingleton.elim w (StdSimplex.single 0), Fin.eq_zero j,
          StdSimplex.weights_single, Finsupp.single_eq_same] at hj
        exact absurd hj one_ne_zero
      have hsupp : ↑w.weights.support ⊆ Set.range j.succAbove := fun i hi ↦
        Fin.exists_succAbove_eq fun h ↦ by simp [h, hj] at hi
      obtain ⟨k, ι', _, w₀, hw₀, hw'⟩ :=
        ih n (Nat.lt_succ_self n) (StdSimplex.comap Fin.succAbove_right_injective w hsupp)
      refine ⟨k, ι' ≫ SimplexCategory.δ j, mono_comp _ _, w₀, hw₀, ?_⟩
      change w = w₀.map (j.succAbove ∘ ι')
      rw [StdSimplex.map_comp, ← hw', StdSimplex.map_comap]
    · push Not at h0
      exact ⟨n, 𝟙 ⦋n⦌, inferInstance, w, h0, (StdSimplex.map_id w).symm⟩

/-- When `w` has nowhere-vanishing coordinates, the nonzero coordinates of `w.map θ` are precisely
the range of `θ`. -/
private lemma weights_map_ne_zero_iff {m r : ℕ} (θ : ⦋m⦌ ⟶ ⦋r⦌) {w : StdSimplex ℝ (Fin (m + 1))}
    (hw : ∀ i, w.weights i ≠ 0) (j : Fin (r + 1)) :
    (w.map θ).weights j ≠ 0 ↔ j ∈ Set.range (θ : Fin (m + 1) → Fin (r + 1)) := by
  rw [StdSimplex.weights_map_apply]
  refine ⟨fun hne ↦ ?_, ?_⟩
  · obtain ⟨i, hi, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    exact ⟨i, by simpa using hi⟩
  · rintro ⟨i, hi⟩
    refine ne_of_gt (lt_of_lt_of_le (lt_of_le_of_ne (w.nonneg i) (hw i).symm) ?_)
    exact Finset.single_le_sum (fun a _ ↦ w.nonneg a) (by simp [hi])

private lemma weights_map_ne_zero_of_epi {k r : ℕ} (π : ⦋k⦌ ⟶ ⦋r⦌) [Epi π]
    {w₀ : StdSimplex ℝ (Fin (k + 1))} (hw₀ : ∀ j, w₀.weights j ≠ 0) (j : Fin (r + 1)) :
    (w₀.map π).weights j ≠ 0 :=
  (weights_map_ne_zero_iff π hw₀ j).2 ((SimplexCategory.epi_iff_surjective.1 ‹Epi π›) j)

private lemma range_eq_of_stdSimplex_map_eq {n k₁ k₂ : ℕ}
    {ι₁ : ⦋k₁⦌ ⟶ ⦋n⦌} {w₁ : StdSimplex ℝ (Fin (k₁ + 1))} (hw₁ : ∀ j, w₁.weights j ≠ 0)
    {ι₂ : ⦋k₂⦌ ⟶ ⦋n⦌} {w₂ : StdSimplex ℝ (Fin (k₂ + 1))} (hw₂ : ∀ j, w₂.weights j ≠ 0)
    (h : w₁.map ι₁ = w₂.map ι₂) :
    Set.range (ι₁ : Fin (k₁ + 1) → Fin (n + 1)) = Set.range (ι₂ : Fin (k₂ + 1) → Fin (n + 1)) :=
  Set.ext fun j ↦ by rw [← weights_map_ne_zero_iff ι₁ hw₁, ← weights_map_ne_zero_iff ι₂ hw₂, h]

private lemma unique_mono_dim_of_stdSimplex {n k₁ k₂ : ℕ}
    {ι₁ : ⦋k₁⦌ ⟶ ⦋n⦌} [Mono ι₁] {w₁ : StdSimplex ℝ (Fin (k₁ + 1))} (hw₁ : ∀ j, w₁.weights j ≠ 0)
    {ι₂ : ⦋k₂⦌ ⟶ ⦋n⦌} [Mono ι₂] {w₂ : StdSimplex ℝ (Fin (k₂ + 1))} (hw₂ : ∀ j, w₂.weights j ≠ 0)
    (h : w₁.map ι₁ = w₂.map ι₂) : k₁ = k₂ := by
  have hinj₁ : Function.Injective (ι₁ : Fin (k₁ + 1) → Fin (n + 1)) :=
    SimplexCategory.mono_iff_injective.1 ‹_›
  have hinj₂ : Function.Injective (ι₂ : Fin (k₂ + 1) → Fin (n + 1)) :=
    SimplexCategory.mono_iff_injective.1 ‹_›
  have hc := congrArg (fun s : Set (Fin (n + 1)) ↦ Nat.card s)
    (range_eq_of_stdSimplex_map_eq hw₁ hw₂ h)
  rw [Nat.card_range_of_injective hinj₁, Nat.card_range_of_injective hinj₂,
    Nat.card_fin, Nat.card_fin] at hc
  exact Nat.succ.inj hc

private lemma unique_mono_of_stdSimplex {n k : ℕ}
    {ι₁ ι₂ : ⦋k⦌ ⟶ ⦋n⦌} [Mono ι₁] [Mono ι₂] {w₁ w₂ : StdSimplex ℝ (Fin (k + 1))}
    (hw₁ : ∀ j, w₁.weights j ≠ 0) (hw₂ : ∀ j, w₂.weights j ≠ 0)
    (h : w₁.map ι₁ = w₂.map ι₂) : ι₁ = ι₂ ∧ w₁ = w₂ := by
  have hinj₁ : Function.Injective ι₁ := SimplexCategory.mono_iff_injective.1 ‹_›
  have hinj₂ : Function.Injective ι₂ := SimplexCategory.mono_iff_injective.1 ‹_›
  have hfn : (ι₁ : Fin (k + 1) → Fin (n + 1)) = ι₂ :=
    (StrictMono.range_inj_of_wellFoundedLT
      (ι₁.toOrderHom.monotone.strictMono_of_injective hinj₁)
      (ι₂.toOrderHom.monotone.strictMono_of_injective hinj₂)).1
      (range_eq_of_stdSimplex_map_eq hw₁ hw₂ h)
  have hι : ι₁ = ι₂ := by ext i : 3; exact congrFun hfn i
  subst hι
  exact ⟨rfl, StdSimplex.map_injective hinj₁ h⟩

/-- The open cell attached to a pair `(x, w)` by stripping zero weights of `w` and taking the
Eilenberg–Zilber nondegenerate quotient of the corresponding face of `x`. -/
private noncomputable def toTopCellOfSimplex {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) : X.ToTopCell :=
  let hface := exists_mono_map_eq_of_stdSimplex w
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
    coords_ne_zero := weights_map_ne_zero_of_epi π hw₀ }

/-- Characterization of `toTopCellOfSimplex x w` by any mono–epi decomposition of `(x, w)`. -/
private lemma toTopCellOfSimplex_eq_of_decomp {X : SSet.{u}} {n k r : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1)))
    (ι : ⦋k⦌ ⟶ ⦋n⦌) [Mono ι] (w₀ : StdSimplex ℝ (Fin (k + 1)))
    (hw₀ : ∀ j, w₀.weights j ≠ 0) (hw : w = w₀.map ι)
    (π : ⦋k⦌ ⟶ ⦋r⦌) [Epi π] (z : X.nonDegenerate r) (hz : X.map ι.op x = X.map π.op z.1) :
    toTopCellOfSimplex x w = ⟨N.mk z.1 z.2, w₀.map π, weights_map_ne_zero_of_epi π hw₀⟩ := by
  let hface := exists_mono_map_eq_of_stdSimplex w
  set k' := hface.choose
  set ι' : ⦋k'⦌ ⟶ ⦋n⦌ := hface.choose_spec.choose
  have : Mono ι' := hface.choose_spec.choose_spec.choose
  set w₀' := hface.choose_spec.choose_spec.choose_spec.choose
  have hw₀' : ∀ j, w₀'.weights j ≠ 0 := hface.choose_spec.choose_spec.choose_spec.choose_spec.1
  have hw' : w = w₀'.map ι' := hface.choose_spec.choose_spec.choose_spec.choose_spec.2
  have hk : k' = k := unique_mono_dim_of_stdSimplex hw₀' hw₀ (hw'.symm.trans hw)
  let hez := X.exists_nonDegenerate (X.map ι'.op x)
  set r' := hez.choose
  set π' : ⦋k'⦌ ⟶ ⦋r'⦌ := hez.choose_spec.choose
  have : Epi π' := hez.choose_spec.choose_spec.choose
  set z' : X.nonDegenerate r' := hez.choose_spec.choose_spec.choose_spec.choose
  have hz' : X.map ι'.op x = X.map π'.op z'.1 := hez.choose_spec.choose_spec.choose_spec.choose_spec
  change (⟨N.mk z'.1 z'.2, w₀'.map π', weights_map_ne_zero_of_epi π' hw₀'⟩ : X.ToTopCell) = _
  subst hk
  obtain ⟨rfl, rfl⟩ := unique_mono_of_stdSimplex hw₀' hw₀ (hw'.symm.trans hw)
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
  obtain ⟨k, ι, _, w₀, hw₀, rfl⟩ := exists_mono_map_eq_of_stdSimplex w
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
      (weights_map_ne_zero_of_epi e hw₀) hw_rhs π' z hz]
  refine ToTopCell.ext rfl fun j ↦ ?_
  have hcomp : (w₀.map e).map π' = w₀.map (e ≫ π') := StdSimplex.map_map _ _ _
  exact congrArg (fun u ↦ u.weights j) hcomp.symm

/-- Reassembling an open cell via `toTopObjMk` recovers the original point of `|X|`. -/
private lemma toTopObjMk_toTopCellOfSimplex {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    toTopObjMk (toTopCellOfSimplex x w).simplex.simplex (toTopCellOfSimplex x w).coords =
      toTopObjMk x w := by
  obtain ⟨k, ι, _, w₀, hw₀, hw⟩ := exists_mono_map_eq_of_stdSimplex w
  obtain ⟨r, π, _, z, hz⟩ := X.exists_nonDegenerate (X.map ι.op x)
  rw [toTopCellOfSimplex_eq_of_decomp x w ι w₀ hw₀ hw π z hz]
  change toTopObjMk z.1 (w₀.map π) = toTopObjMk x w
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

/-- Monotone maps `Fin (n + 1) → Fin (r + 1)` are determined by the pushforward of the uniform
barycenter of `StdSimplex ℝ (Fin (n + 1))`. -/
private lemma eq_of_barycenter_map_eq {n r : ℕ} {π₁ π₂ : ⦋n⦌ ⟶ ⦋r⦌}
    (h : (StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))).map π₁ =
      (StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))).map π₂) :
    π₁ = π₂ := by
  -- For each `j`, cumulative weights up to `j` count the preimage `{a | πᵢ a ≤ j}`, which is a
  -- downward-closed subset of `Fin (n + 1)` and hence determined by its cardinality.
  have hset (j : Fin (r + 1)) :
      Finset.univ.filter (fun a : Fin (n + 1) ↦ π₁ a ≤ j) =
        Finset.univ.filter (fun a : Fin (n + 1) ↦ π₂ a ≤ j) := by
    have hsum := congrArg (fun u ↦ ∑ y ∈ Finset.univ.filter (· ≤ j), u.weights y) h
    dsimp only at hsum
    rw [StdSimplex.sum_filter_weights_map, StdSimplex.sum_filter_weights_map] at hsum
    simp only [StdSimplex.weights_barycenter_apply, Fintype.card_fin, Nat.cast_add, Nat.cast_one,
      Finset.sum_const, nsmul_eq_mul] at hsum
    have hcard : (Finset.univ.filter (fun a : Fin (n + 1) ↦ π₁ a ≤ j)).card =
        (Finset.univ.filter (fun a : Fin (n + 1) ↦ π₂ a ≤ j)).card := by
      exact_mod_cast mul_right_cancel₀ (inv_ne_zero (by positivity : (n : ℝ) + 1 ≠ 0)) hsum
    have hsub {f g : ⦋n⦌ ⟶ ⦋r⦌}
        (hc : (Finset.univ.filter (fun a : Fin (n + 1) ↦ f a ≤ j)).card ≤
          (Finset.univ.filter (fun a : Fin (n + 1) ↦ g a ≤ j)).card) :
        Finset.univ.filter (fun a : Fin (n + 1) ↦ f a ≤ j) ⊆
          Finset.univ.filter (fun a : Fin (n + 1) ↦ g a ≤ j) := fun a ha ↦ by
      by_contra ha'
      refine (Finset.card_lt_card (Finset.ssubset_iff_of_subset ?_ |>.2 ⟨a, ha, ha'⟩)).not_ge hc
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ha' hb ⊢
      exact (f.toOrderHom.monotone
        (le_of_not_ge fun hab ↦ ha' ((g.toOrderHom.monotone hab).trans hb))).trans ha
    exact Finset.Subset.antisymm (hsub hcard.le) (hsub hcard.ge)
  ext i : 3
  have hle (j : Fin (r + 1)) : π₁ i ≤ j ↔ π₂ i ≤ j := by simpa using Finset.ext_iff.1 (hset j) i
  exact le_antisymm ((hle (π₂ i)).2 le_rfl) ((hle (π₁ i)).1 le_rfl)

/-- Evaluating `toTopObjMk · StdSimplex.barycenter` on `n`-simplices is injective. -/
theorem toTopObjMk_barycenter_injective (X : SSet.{u}) (n : ℕ) :
    Function.Injective fun x : X _⦋n⦌ ↦
      toTopObjMk x (StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))) := by
  intro x₁ x₂ h
  dsimp only at h
  let b : StdSimplex ℝ (Fin (n + 1)) := StdSimplex.barycenter
  have hb : ∀ j, b.weights j ≠ 0 := fun j ↦ by
    rw [StdSimplex.weights_barycenter_apply, Fintype.card_fin]; positivity
  obtain ⟨r₁, π₁, _, z₁, rfl⟩ := X.exists_nonDegenerate x₁
  obtain ⟨r₂, π₂, _, z₂, rfl⟩ := X.exists_nonDegenerate x₂
  rw [toTopObjMk_map, toTopObjMk_map] at h
  have hc : X.toTopCellEquiv (toTopObjMk (N.mk z₁.1 z₁.2).simplex (b.map π₁)) =
      X.toTopCellEquiv (toTopObjMk (N.mk z₂.1 z₂.2).simplex (b.map π₂)) :=
    congrArg X.toTopCellEquiv h
  rw [toTopCellEquiv_toTopObjMk_of_ne_zero (N.mk z₁.1 z₁.2) (b.map π₁)
      (weights_map_ne_zero_of_epi π₁ hb),
    toTopCellEquiv_toTopObjMk_of_ne_zero (N.mk z₂.1 z₂.2) (b.map π₂)
      (weights_map_ne_zero_of_epi π₂ hb)] at hc
  have hsimp : N.mk z₁.1 z₁.2 = N.mk z₂.1 z₂.2 := congrArg ToTopCell.simplex hc
  have hdim : r₁ = r₂ := congrArg (·.dim) hsimp
  subst hdim
  have hz : z₁ = z₂ := Subtype.ext (by injection hsimp with hS; injection hS)
  subst hz
  have hcoords : b.map π₁ = b.map π₂ := by injection hc
  rw [eq_of_barycenter_map_eq hcoords]

/-- The unit `X ⟶ Sing |X|` of the realization–singular adjunction is componentwise injective. -/
theorem sSetTopAdj_unit_app_injective (X : SSet.{u}) (m : SimplexCategoryᵒᵖ) :
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
  exact sSetTopAdj_unit_app_injective X m

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

/-- The bijection between `m`-simplices of `X` and `m`-simplices of `uliftFunctor.obj X`, matching
the direction of `TopCat.uliftFunctorObjHomeo`. -/
@[expose]
def uliftFunctorObjEquiv (X : SSet.{u}) (m : SimplexCategoryᵒᵖ) :
    X.obj m ≃ (uliftFunctor.{v, u}.obj X).obj m :=
  Equiv.ulift.symm

@[simp]
lemma uliftFunctorObjEquiv_map {X : SSet.{u}} {m₁ m₂ : SimplexCategoryᵒᵖ} (f : m₁ ⟶ m₂)
    (x : X.obj m₁) :
    (uliftFunctor.{v, u}.obj X).map f (X.uliftFunctorObjEquiv.{v} m₁ x) =
      X.uliftFunctorObjEquiv.{v} m₂ (X.map f x) :=
  (rfl)

@[simp]
lemma uliftFunctorObjEquiv_symm_map {X : SSet.{u}} {m₁ m₂ : SimplexCategoryᵒᵖ} (f : m₁ ⟶ m₂)
    (x : (uliftFunctor.{v, u}.obj X).obj m₁) :
    (X.uliftFunctorObjEquiv.{v} m₂).symm ((uliftFunctor.{v, u}.obj X).map f x) =
      X.map f ((X.uliftFunctorObjEquiv.{v} m₁).symm x) :=
  (rfl)

@[simp]
lemma uliftFunctor_map_uliftFunctorObjEquiv {X Y : SSet.{u}} (f : X ⟶ Y)
    {m : SimplexCategoryᵒᵖ} (x : X.obj m) :
    (uliftFunctor.{v, u}.map f).app m (X.uliftFunctorObjEquiv.{v} m x) =
      Y.uliftFunctorObjEquiv.{v} m (f.app m x) :=
  (rfl)

@[simp]
lemma uliftFunctorObjEquiv_symm_uliftFunctor_map {X Y : SSet.{u}} (f : X ⟶ Y)
    {m : SimplexCategoryᵒᵖ} (x : (uliftFunctor.{v, u}.obj X).obj m) :
    (Y.uliftFunctorObjEquiv.{v} m).symm ((uliftFunctor.{v, u}.map f).app m x) =
      f.app m ((X.uliftFunctorObjEquiv.{v} m).symm x) :=
  (rfl)

/-- Geometric realization of a universe-lifted simplicial set is naturally isomorphic to the
universe lift of its geometric realization. -/
noncomputable def toTopUliftIso (X : SSet.{u}) :
    |uliftFunctor.{v, u}.obj X| ≅ TopCat.uliftFunctor.{v, u}.obj |X| := by
  let φ : uliftFunctor.{v, u}.obj X ⟶ TopCat.toSSet.obj (TopCat.uliftFunctor.{v, u}.obj |X|) :=
    { app m := ↾fun x ↦ ((TopCat.uliftFunctor.{v, u}.obj |X|).toSSetObjEquiv m).symm
        ((|X|.uliftFunctorObjHomeo : C(|X|, TopCat.uliftFunctor.{v, u}.obj |X|)).comp
          (|X|.toSSetObjEquiv m ((sSetTopAdj.unit.app X).app m
            ((X.uliftFunctorObjEquiv.{v} m).symm x))))
      naturality m₁ m₂ f := by
        obtain ⟨a₁, rfl⟩ : ∃ a, m₁ = op a := ⟨m₁.unop, rfl⟩
        obtain ⟨a₂, rfl⟩ : ∃ a, m₂ = op a := ⟨m₂.unop, rfl⟩
        obtain ⟨g, rfl⟩ : ∃ g : a₂ ⟶ a₁, f = g.op := ⟨f.unop, rfl⟩
        ext x
        apply ((TopCat.uliftFunctor.{v, u}.obj |X|).toSSetObjEquiv (op a₂)).injective
        ext w
        simp only [TypeCat.Fun.toFun_apply, ConcreteCategory.comp_apply, TypeCat.ofHom_apply,
          TopCat.toSSetObjEquiv_naturality_apply, Equiv.apply_symm_apply, ContinuousMap.comp_apply,
          ContinuousMap.coe_ofClass, uliftFunctorObjEquiv_symm_map]
        have hnat := ConcreteCategory.congr_hom ((sSetTopAdj.unit.app X).naturality g.op)
          ((X.uliftFunctorObjEquiv.{v} (op a₁)).symm x)
        dsimp at hnat
        rw [hnat, TopCat.toSSetObjEquiv_naturality_apply] }
  let homMap : |uliftFunctor.{v, u}.obj X| ⟶ TopCat.uliftFunctor.{v, u}.obj |X| :=
    (sSetTopAdj.homEquiv _ _).symm φ
  have hhom {n : ℕ} (x : (uliftFunctor.{v, u}.obj X) _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
      homMap (toTopObjMk x w) =
        |X|.uliftFunctorObjHomeo (toTopObjMk ((X.uliftFunctorObjEquiv.{v} (op ⦋n⦌)).symm x) w) := by
    rw [apply_toTopObjMk, Equiv.apply_symm_apply]
    simp only [φ, TypeCat.ofHom_apply, Equiv.apply_symm_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_ofClass, toTopObjMk_def]
  -- Inverse map via preservation of colimits by `toTop` and `TopCat.uliftFunctor`.
  let hc := isColimitOfPreserves (toTop.{u} ⋙ TopCat.uliftFunctor.{v, u}) (denseAtUliftYoneda X)
  let legHomeo (m : SimplexCategory) :
      TopCat.uliftFunctor.{v, u}.obj |stdSimplex.{u}.obj m| ≃ₜ |stdSimplex.{max u v}.obj m| :=
    (|stdSimplex.{u}.obj m|.uliftFunctorObjHomeo.symm.trans m.toTopHomeo.{u}).trans
      m.toTopHomeo.{max u v}.symm
  let c : Cocone (CostructuredArrow.proj uliftYoneda.{u} X ⋙ uliftYoneda.{u} ⋙
      toTop.{u} ⋙ TopCat.uliftFunctor.{v, u}) :=
    { pt := |uliftFunctor.{v, u}.obj X|
      ι :=
        { app j := (TopCat.isoOfHomeo (legHomeo j.left)).hom ≫
            toTop.{max u v}.map ((uliftFunctorHomEquiv.{u, v} X j.left).symm j.hom)
          naturality j₁ j₂ α := by
            ext y
            let y' : TopCat.uliftFunctor.{v, u}.obj |stdSimplex.{u}.obj j₁.left| := y
            let f₁ : stdSimplex.{u}.obj j₁.left ⟶ X := j₁.hom
            let f₂ : stdSimplex.{u}.obj j₂.left ⟶ X := j₂.hom
            change (toTop.{max u v}.map ((uliftFunctorHomEquiv.{u, v} X j₂.left).symm f₂))
                (legHomeo j₂.left ((TopCat.uliftFunctor.{v, u}.map
                  (toTop.{u}.map (stdSimplex.{u}.map α.left))) y')) =
              (toTop.{max u v}.map ((uliftFunctorHomEquiv.{u, v} X j₁.left).symm f₁))
                (legHomeo j₁.left y')
            simp only [legHomeo, Homeomorph.trans_apply]
            rw [TopCat.uliftFunctorObjHomeo_symm_naturality_apply,
              SimplexCategory.toTopHomeo_naturality_apply,
              SimplexCategory.toTopHomeo_symm_naturality_apply]
            have hα : (uliftFunctorHomEquiv.{u, v} X j₁.left).symm f₁ =
                SSet.stdSimplex.map α.left ≫ (uliftFunctorHomEquiv.{u, v} X j₂.left).symm f₂ :=
              (uliftFunctorHomEquiv.{u, v} X j₁.left).injective (by
                rw [Equiv.apply_symm_apply, uliftFunctorHomEquiv_map_comp, Equiv.apply_symm_apply]
                exact (CostructuredArrow.w α).symm)
            rw [hα, toTop.map_comp, ConcreteCategory.comp_apply] } }
  let invMap : TopCat.uliftFunctor.{v, u}.obj |X| ⟶ |uliftFunctor.{v, u}.obj X| := hc.desc c
  have hinv {n : ℕ} (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
      invMap (|X|.uliftFunctorObjHomeo (toTopObjMk x w)) =
        toTopObjMk (X.uliftFunctorObjEquiv.{v} (op ⦋n⦌) x) w := by
    let j : CostructuredArrow uliftYoneda.{u} X := CostructuredArrow.mk (yonedaEquiv.symm x)
    have hj := ConcreteCategory.congr_hom (hc.fac c j)
      (|stdSimplex.{u}.obj ⦋n⦌|.uliftFunctorObjHomeo (⦋n⦌.toTopHomeo.symm w))
    change invMap ((TopCat.uliftFunctor.{v, u}.map (toTop.{u}.map (yonedaEquiv.symm x)))
        (|stdSimplex.{u}.obj ⦋n⦌|.uliftFunctorObjHomeo (⦋n⦌.toTopHomeo.symm w))) =
      (toTop.{max u v}.map ((uliftFunctorHomEquiv.{u, v} X ⦋n⦌).symm (yonedaEquiv.symm x)))
        (legHomeo ⦋n⦌
          (|stdSimplex.{u}.obj ⦋n⦌|.uliftFunctorObjHomeo (⦋n⦌.toTopHomeo.symm w))) at hj
    rw [toTopObjMk_eq_toTop_map, ← TopCat.uliftFunctorObjHomeo_naturality_apply]
    refine hj.trans ?_
    have hsymm : (uliftFunctorHomEquiv.{u, v} X ⦋n⦌).symm (yonedaEquiv.symm x) =
        yonedaEquiv.symm (X.uliftFunctorObjEquiv.{v} (op ⦋n⦌) x) :=
      (uliftFunctorHomEquiv.{u, v} X ⦋n⦌).injective <| yonedaEquiv.injective <| by
        rw [Equiv.apply_symm_apply, yonedaEquiv_uliftFunctorHomEquiv,
          Equiv.apply_symm_apply, Equiv.apply_symm_apply]; rfl
    simp only [legHomeo, Homeomorph.trans_apply, Homeomorph.symm_apply_apply,
      Homeomorph.apply_symm_apply, hsymm, ← toTopObjMk_eq_toTop_map]
  exact
    { hom := homMap
      inv := invMap
      hom_inv_id := toTop_hom_ext fun n x w ↦ by
        simp only [ConcreteCategory.comp_apply, TopCat.id_app, hhom, hinv, Equiv.apply_symm_apply]
      inv_hom_id := by
        ext p
        obtain ⟨q, rfl⟩ := |X|.uliftFunctorObjHomeo.surjective p
        obtain ⟨n, x, w, rfl⟩ := exists_toTopObjMk q
        simp only [ConcreteCategory.comp_apply, TopCat.id_app, hinv, hhom, Equiv.symm_apply_apply] }

@[simp]
lemma toTopUliftIso_hom_toTopObjMk {X : SSet.{u}} {n : ℕ}
    (x : (uliftFunctor.{v, u}.obj X) _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    (toTopUliftIso.{v, u} X).hom (toTopObjMk x w) =
      |X|.uliftFunctorObjHomeo (toTopObjMk ((X.uliftFunctorObjEquiv.{v} (op ⦋n⦌)).symm x) w) := by
  rw [toTopUliftIso, apply_toTopObjMk, Equiv.apply_symm_apply]
  simp only [TypeCat.ofHom_apply, Equiv.apply_symm_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_ofClass, toTopObjMk_def]

@[simp]
lemma toTopUliftIso_inv_uliftFunctorObjHomeo_toTopObjMk {X : SSet.{u}} {n : ℕ}
    (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    (toTopUliftIso.{v, u} X).inv (|X|.uliftFunctorObjHomeo (toTopObjMk x w)) =
      toTopObjMk (X.uliftFunctorObjEquiv.{v} (op ⦋n⦌) x) w := by
  apply (TopCat.homeoOfIso (toTopUliftIso.{v, u} X)).injective
  simp only [TopCat.homeoOfIso_apply, Iso.inv_hom_id_apply, toTopUliftIso_hom_toTopObjMk,
    Equiv.symm_apply_apply]

/-- Natural isomorphism `|uliftFunctor.obj ·| ≅ uliftFunctor.obj |·|`. -/
noncomputable def toTopUliftNatIso :
    uliftFunctor.{v, u} ⋙ toTop.{max u v} ≅ toTop.{u} ⋙ TopCat.uliftFunctor.{v, u} :=
  NatIso.ofComponents toTopUliftIso fun f ↦ toTop_hom_ext fun n x w ↦ by
    simp only [Functor.comp_obj, Functor.comp_map, ConcreteCategory.comp_apply,
      toTop_map_toTopObjMk, toTopUliftIso_hom_toTopObjMk,
      TopCat.uliftFunctorObjHomeo_naturality_apply, uliftFunctorObjEquiv_symm_uliftFunctor_map]

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
lemma toTopUliftHomeomorph_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (p : |X|) :
    toTop.map (uliftFunctor.{v, u}.map f) (toTopUliftHomeomorph.{v, u} X p) =
      toTopUliftHomeomorph.{v, u} Y (toTop.map f p) := by
  obtain ⟨n, x, w, rfl⟩ := exists_toTopObjMk p
  simp

@[simp]
lemma toTopUliftHomeomorph_symm_naturality {X Y : SSet.{u}} (f : X ⟶ Y)
    (p : |uliftFunctor.{v, u}.obj X|) :
    (toTopUliftHomeomorph.{v, u} Y).symm (toTop.map (uliftFunctor.{v, u}.map f) p) =
      toTop.map f ((toTopUliftHomeomorph.{v, u} X).symm p) := by
  obtain ⟨n, x, w, rfl⟩ := exists_toTopObjMk p
  simp

end ULift

end SSet

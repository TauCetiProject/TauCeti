/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.NTQ.Basic
public import TauCeti.GroupTheory.FreeGroup.Coprod
import TauCeti.Algebra.Group.Subgroup.Closure
import TauCeti.GroupTheory.Coprod.Finiteness
import TauCeti.GroupTheory.FreeGroup.MaximalRoot.Basic

/-!
# Normalized towers

A *normalized tower* over a group `G` is built from the bottom up: its bottom carrier is `G`, and
over a carrier `H` the next carrier is one of

1. the coordinate group `H[X] ⧸ Rad_H(Q)` of a standard quadratic equation `Q` over `H` with a
   specified solution in `H`, the radical being taken over the fixed group `H`;
2. the extension `H ∗_{C_H(u)} (C_H(u) × ℤⁿ)` of the full centralizer of `u`, for admissible
   centralizer data `(u, U, n)`;
3. the free product `H ∗ ℤⁿ`;
4. the free product `H ∗ F(X)`.

Each level comes with the coefficient homomorphism `H →* T` and a retraction `T →* H`: evaluation
at the specified solution for a quadratic level, and the map killing the new generators for the
other levels. The radical of a quadratic level is taken over the carrier below it, not over `G`:
the coordinate group over `G` of the raw system of equations of a tower is a different group in
general.

## Main definitions

* `TauCeti.LimitGroup.NTQ.TowerLevel H`: the data of one level over the carrier `H`, with its
  carrier `TowerLevel.Carrier`, `TowerLevel.inclusion` and `TowerLevel.retraction`.
* `TauCeti.LimitGroup.NTQ.Tower G T ι`: a normalized tower over `G` with top carrier `T` and
  coefficient homomorphism `ι : G →* T`, with `Tower.height` and `Tower.retraction`;
  `Tower.single L` is the tower with the single level `L`.

## Main results

* `TauCeti.LimitGroup.NTQ.TowerLevel.retraction_comp_inclusion`,
  `TauCeti.LimitGroup.NTQ.TowerLevel.inclusion_injective`: the level maps are injective, with the
  specified retractions.
* `TauCeti.LimitGroup.NTQ.Tower.retraction_comp`,
  `TauCeti.LimitGroup.NTQ.Tower.retraction_apply_coeff`, `TauCeti.LimitGroup.NTQ.Tower.injective`:
  the coefficient homomorphism of a tower is injective, with a retraction.
* `TauCeti.LimitGroup.NTQ.Tower.exists_surjective_gHom`, `TauCeti.LimitGroup.NTQ.Tower.fg`: the
  top carrier is finitely generated over `G`, hence finitely generated when `G` is.
* `TauCeti.LimitGroup.NTQ.TowerLevel.inclusion_bijective_sq_iff`: the quadratic level `x² = 1`
  adds nothing exactly when the carrier below has no element of order two.
* `TauCeti.LimitGroup.NTQ.isAdmissibleCentralizerLevel_inr_of`: over a free group `G`, a variable
  of `G[X]` with its own singleton is admissible centralizer data in every positive rank.
* `TauCeti.LimitGroup.NTQ.map_gHom_t_eq_one_of_map_inr_of_eq_one`,
  `TauCeti.LimitGroup.NTQ.exists_gHom_centralizerExt_inr_of_eq_one_and_t_eq`: over a free group
  `G`, let `K` be the top carrier of the tower `H = G ∗ ⟨z⟩` followed by the extension of the
  centralizer of `z` by a new letter `x`. Every homomorphism `K → H` over `H` followed by a
  homomorphism killing `z` kills `x`, whereas for every `g ∈ G` there is a `G`-homomorphism
  `K → G` with `z ↦ 1` and `x ↦ g`.

## References

* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §1,
  Theorem 1 (the coordinate groups of quadratic equations over a fixed coefficient group), and
  §3, Form 2 (the full-centralizer relations in the radical of `z⁻¹ c z = d`) and Form 3 (the
  radical of `x² = d`).
* [VAR-II] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. II:
  Systems in triangular quasi-quadratic form and description of residually free groups*,
  J. Algebra 200 (1998), §0, Definition 8.
* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §7.6, Definition 43.
-/

public section

open Monoid.Coprod Subgroup TauCeti.GroupAlgGeom

universe u

namespace TauCeti.LimitGroup.NTQ

/-- The data of one level of a normalized tower over the carrier `H`. -/
inductive TowerLevel (H : Type u) [Group H] : Type (u + 1)
  /-- A quadratic level: a standard quadratic equation `Q` over `H` in the variables `X`, with a
  specified solution `v` in `H`. -/
  | quadratic (X : Type u) [Finite X] (Q : Quadratic.Standard H X) (v : X → H)
      (hv : v ∈ V (MonoidHom.id H) {Q.toWord})
  /-- A centralizer level: admissible data `(u, U, n)` for extending the full centralizer of `u`
  by `ℤⁿ`. -/
  | centralizer (u : H) (U : Finset H) (n : ℕ) (h : IsAdmissibleCentralizerLevel u U n)
  /-- An abelian level: a free factor `ℤⁿ`. -/
  | abelian (n : ℕ)
  /-- A free level: a free factor `F(X)`. -/
  | free (X : Type u) [Finite X]

namespace TowerLevel

variable {H : Type u} [Group H]

/-- The carrier of a level over `H`: the coordinate group over `H` of a quadratic level, the
extension of the centralizer for a centralizer level, `H ∗ ℤⁿ` and `H ∗ F(X)` for abelian and free
levels. -/
@[expose] def Carrier : TowerLevel H → Type u
  | quadratic _ Q _ _ => CoordGroup (MonoidHom.id H) {Q.toWord}
  | centralizer u _ n _ => CentralizerExt u n
  | abelian n => Monoid.Coprod H (Fin n → Multiplicative ℤ)
  | free X => GX H X

/-- The group structure of the carrier of a level. -/
instance : (L : TowerLevel H) → Group L.Carrier
  | quadratic _ Q _ _ => inferInstanceAs (Group (CoordGroup (MonoidHom.id H) {Q.toWord}))
  | centralizer u _ n _ => inferInstanceAs (Group (CentralizerExt u n))
  | abelian n => inferInstanceAs (Group (Monoid.Coprod H (Fin n → Multiplicative ℤ)))
  | free X => inferInstanceAs (Group (GX H X))

/-- The coefficient homomorphism `H →* T` of a level with carrier `T`. -/
@[expose] def inclusion : (L : TowerLevel H) → H →* L.Carrier
  | quadratic _ Q _ _ => CoordGroup.coeff (MonoidHom.id H) {Q.toWord}
  | centralizer _ _ _ _ => CentralizerExt.of
  | abelian _ => inl
  | free _ => inl

/-- The retraction `T →* H` of a level with carrier `T`: evaluation at the specified solution of a
quadratic level, and the homomorphism killing the new generators of the other levels. -/
def retraction : (L : TowerLevel H) → L.Carrier →* H
  | quadratic _ _ v hv => (CoordGroup.evalGHom v hv).toMonoidHom
  | centralizer _ _ _ _ => CentralizerExt.retraction 0
  | abelian _ => fst
  | free _ => fst

section Equations

/-! The defining equations of `inclusion` and `retraction` on the four kinds of level, for rewriting
after a case split, as homomorphisms and as functions. Rewrite an applied map with the function
forms `coe_…`: they replace the whole coercion, so that the result is an application of a
homomorphism between the underlying groups. They are not `simp` lemmas: their right-hand sides
live on the underlying groups, where the `simp` lemmas about elements of the carrier no longer
apply. -/

variable {X : Type u} [Finite X]

theorem inclusion_quadratic (Q : Quadratic.Standard H X) (v : X → H)
    (hv : v ∈ V (MonoidHom.id H) {Q.toWord}) :
    (quadratic X Q v hv).inclusion = CoordGroup.coeff (MonoidHom.id H) {Q.toWord} := (rfl)

theorem inclusion_centralizer (u : H) (U : Finset H) (n : ℕ)
    (h : IsAdmissibleCentralizerLevel u U n) :
    (centralizer u U n h).inclusion = CentralizerExt.of := (rfl)

theorem inclusion_abelian (n : ℕ) : (abelian n : TowerLevel H).inclusion = inl := (rfl)

theorem inclusion_free : (free X : TowerLevel H).inclusion = inl := (rfl)

theorem retraction_quadratic (Q : Quadratic.Standard H X) (v : X → H)
    (hv : v ∈ V (MonoidHom.id H) {Q.toWord}) : (quadratic X Q v hv).retraction =
      (CoordGroup.evalGHom v hv : CoordGroup (MonoidHom.id H) {Q.toWord} →* H) := (rfl)

theorem retraction_centralizer (u : H) (U : Finset H) (n : ℕ)
    (h : IsAdmissibleCentralizerLevel u U n) :
    (centralizer u U n h).retraction = CentralizerExt.retraction 0 := (rfl)

theorem retraction_abelian (n : ℕ) : (abelian n : TowerLevel H).retraction = fst := (rfl)

theorem retraction_free : (free X : TowerLevel H).retraction = fst := (rfl)

theorem coe_inclusion_quadratic (Q : Quadratic.Standard H X) (v : X → H)
    (hv : v ∈ V (MonoidHom.id H) {Q.toWord}) :
    ⇑(quadratic X Q v hv).inclusion = CoordGroup.coeff (MonoidHom.id H) {Q.toWord} := (rfl)

theorem coe_inclusion_centralizer (u : H) (U : Finset H) (n : ℕ)
    (h : IsAdmissibleCentralizerLevel u U n) :
    ⇑(centralizer u U n h).inclusion = (CentralizerExt.of : H →* CentralizerExt u n) := (rfl)

theorem coe_inclusion_abelian (n : ℕ) : ⇑(abelian n : TowerLevel H).inclusion =
    (inl : H →* Monoid.Coprod H (Fin n → Multiplicative ℤ)) := (rfl)

theorem coe_inclusion_free : ⇑(free X : TowerLevel H).inclusion = (inl : H →* GX H X) := (rfl)

theorem coe_retraction_quadratic (Q : Quadratic.Standard H X) (v : X → H)
    (hv : v ∈ V (MonoidHom.id H) {Q.toWord}) :
    ⇑(quadratic X Q v hv).retraction = CoordGroup.evalGHom v hv := (rfl)

theorem coe_retraction_centralizer (u : H) (U : Finset H) (n : ℕ)
    (h : IsAdmissibleCentralizerLevel u U n) :
    ⇑(centralizer u U n h).retraction = (CentralizerExt.retraction 0 : CentralizerExt u n →* H) :=
  (rfl)

theorem coe_retraction_abelian (n : ℕ) : ⇑(abelian n : TowerLevel H).retraction =
    (fst : Monoid.Coprod H (Fin n → Multiplicative ℤ) →* H) := (rfl)

theorem coe_retraction_free : ⇑(free X : TowerLevel H).retraction = (fst : GX H X →* H) := (rfl)

/-- The retraction of a quadratic level evaluates the class of a word at the specified solution. -/
@[simp]
theorem retraction_quadratic_mk (Q : Quadratic.Standard H X) (v : X → H)
    (hv : v ∈ V (MonoidHom.id H) {Q.toWord}) (w : GX H X) :
    (quadratic X Q v hv).retraction (w : CoordGroup (MonoidHom.id H) {Q.toWord}) =
      eval (MonoidHom.id H) v w :=
  CoordGroup.evalGHom_mk hv w

/-- The retraction of a quadratic level sends the generic point to the specified solution. -/
@[simp]
theorem retraction_quadratic_genericPoint (Q : Quadratic.Standard H X) (v : X → H)
    (hv : v ∈ V (MonoidHom.id H) {Q.toWord}) (x : X) :
    (quadratic X Q v hv).retraction (CoordGroup.genericPoint (.id H) {Q.toWord} x) = v x :=
  CoordGroup.evalGHom_genericPoint hv x

/-- Composing the generic point with the retraction of a quadratic level gives the specified
solution. -/
@[simp]
theorem retraction_quadratic_comp_genericPoint (Q : Quadratic.Standard H X) (v : X → H)
    (hv : v ∈ V (MonoidHom.id H) {Q.toWord}) :
    (quadratic X Q v hv).retraction ∘ CoordGroup.genericPoint (.id H) {Q.toWord} = v :=
  CoordGroup.evalGHom_comp_genericPoint hv

/-- The retraction of a centralizer level fixes the elements of the carrier below it. -/
@[simp]
theorem retraction_centralizer_of (u : H) (U : Finset H) (n : ℕ)
    (h : IsAdmissibleCentralizerLevel u U n) (x : H) :
    (centralizer u U n h).retraction (CentralizerExt.of x) = x :=
  CentralizerExt.retraction_of 0 x

/-- The retraction of a centralizer level kills the new letters. -/
@[simp]
theorem retraction_centralizer_t (u : H) (U : Finset H) (n : ℕ)
    (h : IsAdmissibleCentralizerLevel u U n) (i : Fin n) :
    (centralizer u U n h).retraction (CentralizerExt.t i) = 1 :=
  (CentralizerExt.retraction_t 0 i).trans (zpow_zero u)

/-- The retraction of an abelian level fixes the elements of the carrier below it. -/
@[simp]
theorem retraction_abelian_inl (n : ℕ) (x : H) :
    (abelian n : TowerLevel H).retraction (inl x) = x :=
  fst_apply_inl x

/-- The retraction of an abelian level kills the new free factor `ℤⁿ`. -/
@[simp]
theorem retraction_abelian_inr {n : ℕ} (w : Fin n → Multiplicative ℤ) :
    (abelian n : TowerLevel H).retraction (inr w) = 1 :=
  fst_apply_inr w

/-- The retraction of a free level fixes the elements of the carrier below it. -/
@[simp]
theorem retraction_free_inl (x : H) : (free X : TowerLevel H).retraction (inl x) = x :=
  fst_apply_inl x

/-- The retraction of a free level kills the new free factor `F(X)`. -/
@[simp]
theorem retraction_free_inr (w : FreeGroup X) : (free X : TowerLevel H).retraction (inr w) = 1 :=
  fst_apply_inr w

end Equations

/-- The retraction of a level is a left inverse of its coefficient homomorphism. -/
@[simp]
theorem retraction_comp_inclusion (L : TowerLevel H) :
    L.retraction.comp L.inclusion = MonoidHom.id H := by
  cases L with
  | quadratic X Q v hv => exact (CoordGroup.evalGHom v hv).comp_coeff
  | centralizer u U n h => exact CentralizerExt.retraction_comp_of 0
  | abelian n => exact fst_comp_inl
  | free X => exact fst_comp_inl

/-- The retraction of a level fixes the coefficients. -/
@[simp]
theorem retraction_inclusion (L : TowerLevel H) (h : H) : L.retraction (L.inclusion h) = h :=
  DFunLike.congr_fun L.retraction_comp_inclusion h

/-- The coefficient homomorphism of a level is injective. -/
theorem inclusion_injective (L : TowerLevel H) : Function.Injective L.inclusion :=
  Function.LeftInverse.injective L.retraction_inclusion

/-- The carrier of a level is finitely generated over the carrier below it. -/
theorem exists_finite_closure_range_inclusion_union (L : TowerLevel H) :
    ∃ s : Set L.Carrier, s.Finite ∧ closure (Set.range L.inclusion ∪ s) = ⊤ := by
  cases L with
  | quadratic X Q v hv =>
    -- The coordinate group is a quotient of `H[X] = H ∗ F(X)`.
    obtain ⟨s, hs, hcl⟩ := exists_finite_closure_range_inl_union (G := H) (H := FreeGroup X)
    have h : closure (Set.range (CoordGroup.coeff (MonoidHom.id H) {Q.toWord}) ∪
        QuotientGroup.mk' _ '' s) = ⊤ := by
      rw [CoordGroup.coeff_def, GX.quotientCoeff_def, MonoidHom.closure_range_comp_union_image,
        hcl, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact ⟨_, hs.image _, h⟩
  | centralizer u U n h =>
    exact ⟨_, Set.finite_range _, CentralizerExt.closure_range_of_union_range_t⟩
  | abelian n => exact exists_finite_closure_range_inl_union
  | free X => exact exists_finite_closure_range_inl_union

/-- The carrier of a level over a finitely generated group is finitely generated. -/
instance [Group.FG H] : (L : TowerLevel H) → Group.FG L.Carrier
  | quadratic _ Q _ _ => inferInstanceAs (Group.FG (CoordGroup (MonoidHom.id H) {Q.toWord}))
  | centralizer u _ n _ => inferInstanceAs (Group.FG (CentralizerExt u n))
  | abelian n => inferInstanceAs (Group.FG (Monoid.Coprod H (Fin n → Multiplicative ℤ)))
  | free X => inferInstanceAs (Group.FG (GX H X))

/-- The quadratic level `x² = 1`, with any of its solutions, adds nothing to the carrier `H` below
it, the coefficient map onto its carrier `H[x] ⧸ Rad_H(x²)` being bijective, exactly when `H` has
no element of order two; for instance, when `H` is torsion-free. -/
theorem inclusion_bijective_sq_iff :
    let Q : Quadratic.Standard H PUnit.{u + 1} :=
      .nonorientable 1 one_pos (fun _ ↦ .unit) (Function.injective_of_subsingleton _)
    ∀ (v : PUnit.{u + 1} → H) (hv : v ∈ V (MonoidHom.id H) {Q.toWord}),
      Function.Bijective (quadratic PUnit Q v hv).inclusion ↔ ∀ h : H, h ^ 2 = 1 → h = 1 := by
  intro Q v hv
  have hV (w : PUnit.{u + 1} → H) : w ∈ V (MonoidHom.id H) {Q.toWord} ↔ w .unit ^ 2 = 1 := by
    simp [Q, Quadratic.Standard.toWord_def, Quadratic.Standard.atoms_nonorientable,
      Quadratic.Standard.constant_nonorientable]
  refine ⟨fun h k hk ↦ ?_, fun h ↦ ⟨inclusion_injective _, fun y ↦ ?_⟩⟩
  · -- The class of `x` is a constant `c`; the solutions `x = k` and `x = 1` give `c = k = 1`.
    obtain ⟨c, hc⟩ := h.2 ((inr (FreeGroup.of .unit) : GX H PUnit) :
      CoordGroup (MonoidHom.id H) {Q.toWord})
    replace hc := (CoordGroup.coeff_apply _ c).symm.trans hc
    have h₁ : c = k := by simpa using congrArg (CoordGroup.evalGHom (fun _ ↦ k) ((hV _).2 hk)) hc
    have h₂ : c = 1 := by simpa using congrArg (CoordGroup.evalGHom 1 ((hV _).2 (one_pow 2))) hc
    rw [← h₁, h₂]
  · -- The only solution is `x = 1`, so every word is congruent to its value there.
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨eval (MonoidHom.id H) 1 w,
      (CoordGroup.coeff_apply _ _).trans (QuotientGroup.eq.2 (mem_Rad.2 fun w' hw' ↦ ?_))⟩
    obtain rfl : w' = 1 := funext fun _ ↦ h _ ((hV w').1 hw')
    simp

end TowerLevel

/-- A *normalized tower* over `G` with top carrier `T` and coefficient homomorphism `ι : G →* T`:
the bottom carrier is `G`, and each further carrier is the carrier of a level over the previous
one. -/
inductive Tower (G : Type u) [Group G] : (T : Type u) → [Group T] → (G →* T) → Type (u + 1)
  /-- The tower with no levels: `G` over itself. -/
  | base : Tower G G (MonoidHom.id G)
  /-- Put a level `L` over the top carrier `H` of a tower. -/
  | cons {H : Type u} [Group H] {ι : G →* H} (t : Tower G H ι) (L : TowerLevel H) :
      Tower G L.Carrier (L.inclusion.comp ι)

namespace Tower

variable {G T : Type u} [Group G] [Group T] {ι : G →* T}

/-- The number of levels of a tower. -/
def height {T : Type u} [Group T] {ι : G →* T} : Tower G T ι → ℕ
  | base => 0
  | cons t _ => t.height + 1

@[simp] theorem height_base : (base : Tower G G (.id G)).height = 0 := (rfl)

@[simp] theorem height_cons (t : Tower G T ι) (L : TowerLevel T) :
    (cons t L).height = t.height + 1 := (rfl)

/-- The retraction `T →* G` of a tower: the composite of the retractions of its levels. -/
def retraction {T : Type u} [Group T] {ι : G →* T} : Tower G T ι → T →* G
  | base => MonoidHom.id G
  | cons t L => t.retraction.comp L.retraction

@[simp] theorem retraction_base : (base : Tower G G (.id G)).retraction = .id G := (rfl)

@[simp] theorem retraction_cons (t : Tower G T ι) (L : TowerLevel T) :
    (cons t L).retraction = t.retraction.comp L.retraction := (rfl)

/-- The tower with the single level `L` over `G`. -/
def single (L : TowerLevel G) : Tower G L.Carrier L.inclusion :=
  cons base L

theorem single_eq_cons_base (L : TowerLevel G) : single L = cons base L := (rfl)

@[simp] theorem height_single (L : TowerLevel G) : (single L).height = 1 := (rfl)

@[simp] theorem retraction_single (L : TowerLevel G) : (single L).retraction = L.retraction :=
  (rfl)

/-- The retraction of a tower is a left inverse of its coefficient homomorphism. -/
@[simp]
theorem retraction_comp (t : Tower G T ι) : t.retraction.comp ι = MonoidHom.id G := by
  induction t with
  | base => rfl
  | cons t L ih =>
    ext x
    simpa using DFunLike.congr_fun ih x

/-- The retraction of a tower fixes the coefficients. -/
@[simp]
theorem retraction_apply_coeff (t : Tower G T ι) (g : G) : t.retraction (ι g) = g :=
  DFunLike.congr_fun t.retraction_comp g

/-- The retraction of a tower, as a homomorphism over `G`. -/
def retractionGHom (t : Tower G T ι) : GHom ι (MonoidHom.id G) where
  toMonoidHom := t.retraction
  map_coeff' := t.retraction_apply_coeff

@[simp]
theorem coe_retractionGHom (t : Tower G T ι) : ⇑t.retractionGHom = t.retraction := (rfl)

private theorem exists_finite_closure_range_union (t : Tower G T ι) :
    ∃ s : Set T, s.Finite ∧ closure (Set.range ι ∪ s) = ⊤ := by
  induction t with
  | base => exact ⟨∅, Set.finite_empty, by simp⟩
  | @cons H _ ι _ L ih =>
    obtain ⟨s₀, hs₀, h₀⟩ := ih
    obtain ⟨s₁, hs₁, h₁⟩ := L.exists_finite_closure_range_inclusion_union
    refine ⟨L.inclusion '' s₀ ∪ s₁, (hs₀.image _).union hs₁, eq_top_iff.2 ?_⟩
    rw [← h₁, closure_le]
    refine Set.union_subset ?_ (Set.subset_union_right.trans (Set.subset_union_right.trans
      subset_closure))
    rintro _ ⟨h, rfl⟩
    have hh : L.inclusion h ∈ closure (Set.range (L.inclusion.comp ι) ∪ L.inclusion '' s₀) := by
      rw [MonoidHom.closure_range_comp_union_image, h₀]
      exact mem_map_of_mem _ (mem_top h)
    exact closure_mono (Set.union_subset_union_right _ Set.subset_union_left) hh

/-- The coefficient homomorphism of a tower is injective. -/
theorem injective (t : Tower G T ι) : Function.Injective ι :=
  Function.LeftInverse.injective t.retraction_apply_coeff

/-- The top carrier of a tower over `G` is finitely generated over `G`: it is a quotient of
`G[Y]`, over `G`, for a finite set `Y` of variables. -/
theorem exists_surjective_gHom (t : Tower G T ι) :
    ∃ (n : ℕ) (π : GHom (inl : G →* GX G (Fin n)) ι), Function.Surjective π := by
  obtain ⟨s, hs, hcl⟩ := t.exists_finite_closure_range_union
  have := hs.to_subtype
  let e := Finite.equivFin s
  refine ⟨Nat.card s, evalGHom ι (Subtype.val ∘ e.symm), ?_⟩
  rwa [coe_evalGHom, eval_surjective_iff, e.symm.surjective.range_comp, Subtype.range_coe]

/-- The top carrier of a tower over a finitely generated group is finitely generated. -/
theorem fg [Group.FG G] (t : Tower G T ι) : Group.FG T := by
  induction t with
  | base => infer_instance
  | cons _ L ih => infer_instance

/-- The tower with one free level in the variables `X` over `G` is `G[X] = G ∗ F(X)`. -/
example (X : Type u) [Finite X] : Tower G (GX G X) inl :=
  single (.free X)

end Tower

/-! ### Admissible centralizer data over a free group -/

section Free

variable {G : Type u} [Group G]

/-- Over a free group `G`, a variable `x` of `G[X] = G ∗ F(X)`, with its own singleton, is
admissible centralizer data in every positive rank: `G[X]` is free and `x` is primitive. -/
theorem isAdmissibleCentralizerLevel_inr_of [IsFreeGroup G] {X : Type*} (x : X) {n : ℕ}
    (hn : 0 < n) :
    IsAdmissibleCentralizerLevel (inr (FreeGroup.of x) : GX G X) {inr (FreeGroup.of x)} n :=
  isAdmissibleCentralizerLevel_singleton_iff_of_isFreeGroup.2
    ⟨(isPrimitive_inr (by simp)).not_isProperPower, hn⟩

/-! ### A tower with several homomorphisms to its base -/

/-- Over a free group `G`, the tower with a free level `H = G ∗ ⟨z⟩` and above it the level
extending the centralizer `⟨z⟩` of `z` by `ℤ`, with top carrier `K = H ∗_{⟨z⟩} (⟨z⟩ × ⟨x⟩)`. -/
example [IsFreeGroup G] :
    Tower G (CentralizerExt (inr (FreeGroup.of .unit) : GX G PUnit) 1)
      ((CentralizerExt.of : GX G PUnit →* _).comp inl) :=
  (Tower.single (.free PUnit)).cons
    (.centralizer _ _ 1 (isAdmissibleCentralizerLevel_inr_of PUnit.unit one_pos))

/-- Over a free group `G`, let `H = G ∗ ⟨z⟩` be the carrier of a free level and
`K = H ∗_{⟨z⟩} (⟨z⟩ × ⟨x⟩)` the carrier of the level above it extending the centralizer of `z`: the
top carrier of the tower `(Tower.single (.free PUnit)).cons (.centralizer z {z} 1 _)`. Every
homomorphism `ρ : K → H` over `H`, in particular every retraction of the upper level, sends `x`
into the centralizer `⟨z⟩` of `z`; so every homomorphism of `H` killing `z` kills `ρ x`. -/
theorem map_gHom_t_eq_one_of_map_inr_of_eq_one [IsFreeGroup G] {M : Type*} [Group M]
    (ρ : GHom (CentralizerExt.of : GX G PUnit.{u + 1} →* CentralizerExt
      (inr (FreeGroup.of .unit) : GX G PUnit) 1) (MonoidHom.id (GX G PUnit)))
    (ψ : GX G PUnit.{u + 1} →* M) (hψ : ψ (inr (FreeGroup.of .unit)) = 1) :
    ψ (ρ (CentralizerExt.t 0)) = 1 := by
  have hz : ρ (CentralizerExt.t 0) ∈ centralizer {(inr (FreeGroup.of .unit) : GX G PUnit)} :=
    mem_centralizer_singleton_iff.2 <| by
      simpa using
        ((CentralizerExt.commute_of_t (mem_centralizer_singleton_iff.2 rfl) 0).map ρ).symm.eq
  obtain ⟨k, hk⟩ := (IsFreeGroup.centralizer_singleton_eq_zpowers_self
    (isPrimitive_inr (by simp)).not_isProperPower).le hz
  rw [← hk, map_zpow, hψ, one_zpow]

/-- Over a free group `G`, let `H = G ∗ ⟨z⟩` and `K = H ∗_{⟨z⟩} (⟨z⟩ × ⟨x⟩)` be the carriers of the
tower `(Tower.single (.free PUnit)).cons (.centralizer z {z} 1 _)`. For every `g ∈ G` there is a
`G`-homomorphism `K → G` with `z ↦ 1` and `x ↦ g`. For `g ≠ 1` it is not the retraction of the
tower, which sends `x` to `1` (`TowerLevel.retraction_centralizer_t`), nor any homomorphism
`K → H` over `H` followed by a homomorphism `H → G` killing `z`
(`map_gHom_t_eq_one_of_map_inr_of_eq_one`). -/
theorem exists_gHom_centralizerExt_inr_of_eq_one_and_t_eq [IsFreeGroup G] (g : G) :
    ∃ φ : GHom ((CentralizerExt.of : GX G PUnit.{u + 1} →* CentralizerExt
        (inr (FreeGroup.of .unit) : GX G PUnit) 1).comp inl) (MonoidHom.id G),
      φ (CentralizerExt.of (inr (FreeGroup.of .unit))) = 1 ∧ φ (CentralizerExt.t 0) = g := by
  -- Lift the projection `H → G` killing `z`, which kills `C_H(z) = ⟨z⟩`, and send `x` to `g`.
  refine ⟨⟨CentralizerExt.lift fst (fun _ ↦ g) (fun _ _ ↦ .refl _) fun c hc _ ↦ ?_,
    fun _ ↦ by simp⟩, by simp, by simp⟩
  rw [IsFreeGroup.centralizer_singleton_eq_zpowers_self
    (isPrimitive_inr (by simp)).not_isProperPower] at hc
  obtain ⟨k, rfl⟩ := hc
  simp

end Free

end TauCeti.LimitGroup.NTQ

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.NTQ.Basic
import TauCeti.GroupTheory.FreeGroup.Centralizer

/-!
# Fundamental points of triangular quasi-quadratic systems

Let `S = S₁ ∪ ⋯ ∪ Sₙ` be a raw triangular quasi-quadratic system over a group `G`, with raw lower
groups `Gᵢ₊₁ = G_{R(Sᵢ₊₁, …, Sₙ)}` and `Gₙ₊₁ = G`. A *fundamental point* of `S` is a solution in
`G` obtained level by level: a fundamental point `w` of the lower system, together with the values
at `w` of a solution of the top level in the raw lower group. Equivalently, it is the point of a
composite `G₁ → G₂ → ⋯ → Gₙ₊₁ = G` of `Gᵢ₊₁`-homomorphisms `Gᵢ → Gᵢ₊₁`; Kharlampovich and
Myasnikov's fundamental sequences `σ₁ π₁ ⋯ σₙ πₙ`, with `σᵢ` a `Gᵢ₊₁`-automorphism of `Gᵢ` and `πᵢ`
a `Gᵢ₊₁`-homomorphism, consist of such composites.

Fundamental points are solutions, but a solution need not be fundamental. Over a free group with
distinct basis elements `a` and `b`, the point `(x, u, v) = (b, 1, a)` of the system
`TauCeti.LimitGroup.NTQ.System.conjOverCommute`, with lower level `[u, v] = 1` and upper level
`x⁻¹ u x u⁻¹ = 1`, is a solution but not a fundamental point. Indeed the class of a solution `x`
of the upper level in the raw lower group commutes with the class of `u`, so its value at the
solution `(u, v) = (a, 1)` of the lower level commutes with `a` and is a power of `a`. The number
of occurrences of `b`, counted with signs, is the same in this value and in the value at
`(u, v) = (1, a)`, so it is zero, whereas it is one in `b`. A cover of all solutions by fundamental
points has to reach such a point through another system, for instance one in which `u = 1` and
`v`, `x` are free.

A *raw cover* of a set `P` of solutions of a system `S` over `G` is a finite family of raw TQ
systems `Uᵢ` with word maps `pᵢ` that send the solutions of `Uᵢ` to solutions of `S`, such that
every point of `P` is the image of a fundamental point of some `Uᵢ`.

## Main definitions

* `TauCeti.LimitGroup.NTQ.System.fundPoints`: the fundamental points of a raw TQ system.
* `TauCeti.LimitGroup.NTQ.RawCover`: a finite raw cover by fundamental points.

## Main results

* `TauCeti.LimitGroup.NTQ.System.fundPoints_subset_V`: fundamental points are solutions.
* `TauCeti.LimitGroup.NTQ.System.fundPoints_cons_nil`: for a system of one level, the fundamental
  points are all the solutions.
* `TauCeti.LimitGroup.NTQ.System.notMem_fundPoints_conjOverCommute`: for distinct basis elements
  `a`, `b` of a free group, the solution `(b, 1, a)` of `conjOverCommute` is not fundamental.
* `TauCeti.LimitGroup.NTQ.RawCover.nonempty_of_subset_iUnion`: raw covers compose with word maps.

## References

* [KM06] O. Kharlampovich, A. Myasnikov, *Elementary theory of free non-abelian groups*,
  J. Algebra 302 (2006), §2.3 (fundamental sequences of NTQ systems).
* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §5.6, Theorems 5–6.
* [VAR-II] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. II:
  Systems in triangular quasi-quadratic form and description of residually free groups*,
  J. Algebra 200 (1998), §7, Lemma 17.
-/

public section

open Monoid.Coprod TauCeti.GroupAlgGeom

universe u v w

namespace TauCeti.LimitGroup.NTQ

variable {G : Type u} [Group G]

namespace System

/-- The *fundamental points* of a raw TQ system: the unique point of `nil`, and for `cons S X L`
the points `v` such that `v ∘ Sum.inr` is a fundamental point of `S` and `v ∘ Sum.inl` is the value
at `v ∘ Sum.inr` of a solution `s` of the top level `L` in the raw lower group `S.CoordGroup`
(given by representatives in `G[Y]`). -/
def fundPoints : {Y : Type v} → System G Y → Set (Y → G)
  | _, nil => Set.univ
  | _, cons (Y := Y) S X L => {v | v ∘ Sum.inr ∈ fundPoints S ∧
      ∃ s : X → GX G Y, (fun x ↦ (s x : S.CoordGroup)) ∈
        V (QuotientGroup.mk' (Rad (MonoidHom.id G) S.equations)) L.equations ∧
        v ∘ Sum.inl = fun x ↦ eval (MonoidHom.id G) (v ∘ Sum.inr) (s x)}

@[simp]
theorem fundPoints_nil : (nil : System G PEmpty).fundPoints = Set.univ := (rfl)

theorem mem_fundPoints_cons {Y X : Type v} [Finite X] {S : System G Y} {L : Level (GX G Y) X}
    {v : X ⊕ Y → G} : v ∈ (cons S X L).fundPoints ↔ v ∘ Sum.inr ∈ S.fundPoints ∧
      ∃ s : X → GX G Y, (fun x ↦ (s x : S.CoordGroup)) ∈
        V (QuotientGroup.mk' (Rad (MonoidHom.id G) S.equations)) L.equations ∧
        v ∘ Sum.inl = fun x ↦ eval (MonoidHom.id G) (v ∘ Sum.inr) (s x) := Iff.rfl

private theorem eval_mem_V_of_mk_mem_V {Y X : Type v} {S : System G Y} {L : Level (GX G Y) X}
    {w : Y → G} (hw : w ∈ V (MonoidHom.id G) S.equations) {s : X → GX G Y}
    (hs : (fun x ↦ (s x : S.CoordGroup)) ∈
      V (QuotientGroup.mk' (Rad (MonoidHom.id G) S.equations)) L.equations) :
    (fun x ↦ eval (MonoidHom.id G) w (s x)) ∈ V (eval (MonoidHom.id G) w) L.equations := by
  -- Evaluation at `w`, as a homomorphism `S.CoordGroup → G` over `G[Y]`.
  let φ : GHom (QuotientGroup.mk' (Rad (MonoidHom.id G) S.equations)) (eval (MonoidHom.id G) w) :=
    ⟨CoordGroup.evalGHom w hw, CoordGroup.evalGHom_mk hw⟩
  have h := φ.comp_mem_V hs
  rwa [show (φ ∘ fun x ↦ (s x : S.CoordGroup)) = fun x ↦ eval (MonoidHom.id G) w (s x) from
    funext fun x ↦ CoordGroup.evalGHom_mk hw (s x)] at h

/-- Fundamental points are solutions. -/
theorem fundPoints_subset_V {Y : Type v} (S : System G Y) :
    S.fundPoints ⊆ V (MonoidHom.id G) S.equations := by
  induction S with
  | nil => simp
  | cons S X L ih =>
    rintro v ⟨hw, s, hs, hv⟩
    exact mem_V_cons.2 ⟨ih hw, hv ▸ eval_mem_V_of_mk_mem_V (ih hw) hs⟩

/-- For a system of one level, over `nil`, every solution is a fundamental point: the raw lower
group of the level is `G` itself. -/
theorem fundPoints_cons_nil {X : Type v} [Finite X] (L : Level (GX G PEmpty) X) :
    (cons nil X L).fundPoints = V (MonoidHom.id G) (cons nil X L).equations := by
  refine (fundPoints_subset_V _).antisymm fun v hv ↦ ⟨trivial, fun x ↦ inl (v (Sum.inl x)),
    mem_V.2 fun e he ↦ coordGroupNilEquiv.injective ?_, by ext; simp⟩
  -- Over `nil`, the raw lower group is `G`, through `coordGroupNilEquiv`.
  have h : (coordGroupNilEquiv (G := G) : (nil : System G PEmpty).CoordGroup →* G).comp
      (QuotientGroup.mk' _) = eval (MonoidHom.id G) (v ∘ Sum.inr) :=
    hom_ext (MonoidHom.ext fun g ↦ by simp) (FreeGroup.ext_hom _ _ isEmptyElim)
  rw [map_one, hom_eval, h]
  convert mem_V.1 (mem_V_cons.1 hv).2 e he using 3
  ext
  simp

/-- Over a free group, the solution `(x, u, v) = (b, 1, a)` of `conjOverCommute`, for distinct
basis letters `a`, `b`, is not a fundamental point. -/
theorem notMem_fundPoints_conjOverCommute {α : Type u} {a b : α} (hab : a ≠ b) :
    Sum.elim (fun _ ↦ FreeGroup.of b) (Sum.elim ![1, FreeGroup.of a] PEmpty.elim) ∉
      (conjOverCommute (FreeGroup α)).fundPoints := by
  classical
  rw [conjOverCommute_def, mem_fundPoints_cons]
  rintro ⟨-, s, hs, hv⟩
  -- The solution `(u, v) = (a, 1)` of the lower level `[u, v] = 1`.
  let p : Fin 2 ⊕ PEmpty → FreeGroup α := Sum.elim ![FreeGroup.of a, 1] PEmpty.elim
  have hp : p ∈ V (MonoidHom.id _) (cons nil (Fin 2) .abelian).equations := by
    rw [mem_V_cons, Level.mem_V_abelian]
    refine ⟨by simp, fun i j ↦ ?_⟩
    fin_cases i <;> fin_cases j <;> simp [p]
  -- The value `y` at `(a, 1)` of the solution of the upper level solves it at `(u, v) = (a, 1)`,
  -- so it commutes with `a` and is a power of `a`.
  have h : Sum.elim (fun x ↦ eval (MonoidHom.id _) p (s x)) p ∈
      V (MonoidHom.id _) (conjOverCommute (FreeGroup α)).equations := by
    rw [conjOverCommute_def, mem_V_cons]
    exact ⟨hp, eval_mem_V_of_mk_mem_V hp hs⟩
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1
    (FreeGroup.commute_of_iff.mp (mem_V_conjOverCommute.1 h).2.symm)
  rw [Sum.elim_inl] at hj
  -- The signed number `β` of occurrences of `b` takes the same value at `(a, 1)` and `(1, a)`.
  let β : FreeGroup α →* Multiplicative ℤ := FreeGroup.lift fun c ↦ if c = b then .ofAdd 1 else 1
  have hβ : β ∘ p = β ∘ Sum.elim ![1, FreeGroup.of a] PEmpty.elim := by
    funext i
    rcases i with i | i
    · fin_cases i <;> simp [β, p, hab]
    · exact i.elim
  have hb : β (FreeGroup.of b) = β (FreeGroup.of a ^ j) := by
    rw [hj, hom_eval, hβ, ← hom_eval]
    exact congrArg β (congrFun hv ())
  simp [β, hab] at hb

/-- Over `F(a, b)`, the point `(x, u, v) = (b, 1, a)` is a solution of `conjOverCommute` that is
not a fundamental point. -/
example {α : Type u} {a b : α} (hab : a ≠ b) :
    Sum.elim (fun _ ↦ FreeGroup.of b) (Sum.elim ![1, FreeGroup.of a] PEmpty.elim) ∈
      V (MonoidHom.id _) (conjOverCommute (FreeGroup α)).equations \
        (conjOverCommute (FreeGroup α)).fundPoints :=
  ⟨mem_V_conjOverCommute.2 ⟨.one_left _, .one_right _⟩, notMem_fundPoints_conjOverCommute hab⟩

end System

/-- A *raw cover* of a set `P` of solutions of a system `S` over `G`, in the variables `X`: finitely
many raw TQ systems over `G`, in variables of the universe of `G`, with word maps sending their
solutions to solutions of `S`, such that every point of `P` is the image of a fundamental point of
one of them. -/
structure RawCover {X : Type w} (S : Set (GX G X)) (P : Set (X → G)) where
  /-- The number of systems. -/
  n : ℕ
  /-- The variables of the `i`-th system. -/
  vars : Fin n → Type u
  /-- The `i`-th system. -/
  system : ∀ i, System G (vars i)
  /-- The word map of the `i`-th system: the value of each variable of `S`. -/
  wordMap : ∀ i, X → GX G (vars i)
  /-- The word maps send solutions of the systems to solutions of `S`. -/
  mapsTo : ∀ i, Set.MapsTo (GroupAlgGeom.wordMap (MonoidHom.id G) (wordMap i))
    (V (MonoidHom.id G) (system i).equations) (V (MonoidHom.id G) S)
  /-- Every point of `P` is the image of a fundamental point. -/
  subset_iUnion :
    P ⊆ ⋃ i, GroupAlgGeom.wordMap (MonoidHom.id G) (wordMap i) '' (system i).fundPoints

private theorem RawCover.nonempty_of_finite {X : Type w} {S : Set (GX G X)} {P : Set (X → G)}
    {ι : Type*} [Finite ι] {vars : ι → Type u} (system : ∀ i, System G (vars i))
    (wordMap : ∀ i, X → GX G (vars i))
    (mapsTo : ∀ i, Set.MapsTo (GroupAlgGeom.wordMap (MonoidHom.id G) (wordMap i))
      (V (MonoidHom.id G) (system i).equations) (V (MonoidHom.id G) S))
    (subset_iUnion :
      P ⊆ ⋃ i, GroupAlgGeom.wordMap (MonoidHom.id G) (wordMap i) '' (system i).fundPoints) :
    Nonempty (RawCover S P) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  exact ⟨⟨n, fun j ↦ vars (e.symm j), fun j ↦ system (e.symm j), fun j ↦ wordMap (e.symm j),
    fun j ↦ mapsTo (e.symm j), subset_iUnion.trans_eq e.symm.iSup_comp.symm⟩⟩

/-- Raw covers compose with word maps: if `P` is covered by the images under finitely many word
maps `w k`, sending solutions of systems `S' k` to solutions of `S`, of sets `P' k` with raw covers,
then `P` has a raw cover. -/
theorem RawCover.nonempty_of_subset_iUnion {X : Type w} {S : Set (GX G X)} {P : Set (X → G)}
    {κ : Type*} [Finite κ] {Z : κ → Type*} {S' : ∀ k, Set (GX G (Z k))} {P' : ∀ k, Set (Z k → G)}
    (w : ∀ k, X → GX G (Z k)) (hw : ∀ k, Set.MapsTo (GroupAlgGeom.wordMap (MonoidHom.id G) (w k))
      (V (MonoidHom.id G) (S' k)) (V (MonoidHom.id G) S))
    (hP : P ⊆ ⋃ k, GroupAlgGeom.wordMap (MonoidHom.id G) (w k) '' P' k)
    (r : ∀ k, RawCover (S' k) (P' k)) : Nonempty (RawCover S P) := by
  refine nonempty_of_finite (ι := Σ k, Fin (r k).n) (fun i ↦ (r i.1).system i.2)
    (fun i x ↦ eval inl ((r i.1).wordMap i.2) (w i.1 x))
    (fun i ↦ mapsTo_wordMap_comp (hw i.1) ((r i.1).mapsTo i.2)) fun p hp ↦ ?_
  obtain ⟨k, q, hq, rfl⟩ := Set.mem_iUnion.1 (hP hp)
  obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.1 ((r k).subset_iUnion hq)
  exact Set.mem_iUnion.2 ⟨⟨k, i⟩, z, hz, (wordMap_wordMap _ _ _).symm⟩

/-- The empty system in finitely many variables `X` has a raw cover of all its points: the system
with one empty level in the variables `X`, with the tuple of variables as word map. -/
example {X : Type u} [Finite X] : Nonempty (RawCover (∅ : Set (GX G X)) (V (MonoidHom.id G) ∅)) :=
  ⟨⟨1, fun _ ↦ X ⊕ PEmpty, fun _ ↦ .cons .nil X .empty, fun _ x ↦ inr (.of (.inl x)),
    fun _ _ _ ↦ by simp, fun v _ ↦ Set.mem_iUnion.2 ⟨0, Sum.elim v PEmpty.elim,
      by rw [System.fundPoints_cons_nil, System.mem_V_cons]; simp, by ext; simp⟩⟩⟩

end TauCeti.LimitGroup.NTQ

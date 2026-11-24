/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.NTQ.Basic
import TauCeti.GroupTheory.FreeGroup.Centralizer

/-!
# Blocks of triangular quasi-quadratic levels over a system

A *block* over a system `S₀` of equations over `G` in the variables `Z` is a finite stack of levels
put on top of `S₀`, each in new variables, with coefficients the words in `G`, the variables `Z` and
the variables of the levels below. A level is one of the levels of a raw triangular
quasi-quadratic system (a standard quadratic equation, the equations of an extension of a
centralizer or of a free abelian group, or no equation), or a finite *quadratic system*: a finite
set of equations in which every variable occurs at most twice. A raw TQ system is a block over the
empty system in no variables, with no quadratic systems among its levels.

In the Makanin–Razborov process a branch of the solution tree of a generalised equation `Ω`, from
`Ω` to a generalised equation `Ω'` lower in the tree, carries such a block over the system `Ω'*`:
the canonical automorphisms of the coordinate groups along the branch are recorded by solutions of
its levels, and the quadratic levels are quadratic systems, which become standard quadratic
equations only after a change of variables. Every change of coefficients keeps a system quadratic
(`BlockLevel.map`), while the image of a standard quadratic equation need not be standard, since
a coefficient may become trivial; so blocks with quadratic systems among their levels can be
stacked along word maps.

Given a set `P₀` of *base points*, solutions of `S₀`, the *fundamental points* of a block are
obtained level by level: a base point, and then at each level the values of a solution of the level
in the coordinate group `G[Y] ⧸ Rad_G(⋯)` of the system below, all equations of the block below and
of `S₀` included. For `S₀ = ∅` in no variables these are the fundamental points of raw TQ systems.

## Main definitions

* `TauCeti.LimitGroup.NTQ.BlockLevel`: a level of a raw TQ system or a finite quadratic system.
* `TauCeti.LimitGroup.NTQ.BlockLevel.map`: the image of a level under a change of coefficients.
* `TauCeti.LimitGroup.NTQ.Block`: a block of levels over a system `S₀`.
* `TauCeti.LimitGroup.NTQ.Block.equations`: its equations, those of `S₀` included.
* `TauCeti.LimitGroup.NTQ.Block.fundPoints`: its fundamental points over a set of base points.

## Main results

* `TauCeti.LimitGroup.NTQ.BlockLevel.equations_map`: the equations of the image of a level are the
  images of its equations.
* `TauCeti.LimitGroup.NTQ.Block.mem_V_cons`: a solution of `cons B X L` is a solution `w` of `B`
  together with a solution of the top level `L` whose coefficients are evaluated at `w`.
* `TauCeti.LimitGroup.NTQ.Block.fundPoints_subset_V`: over base points that are solutions of `S₀`,
  fundamental points are solutions of the block.
* `TauCeti.LimitGroup.NTQ.Block.exists_append`: for a block over `S₀` and a block over another
  system mapping to `S₀` by a word map, there is a block over the other system whose fundamental
  points reach those of the first block over the image of the second.

## References

* [VAR-II] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. II:
  Systems in triangular quasi-quadratic form and description of residually free groups*,
  J. Algebra 200 (1998), §5 (Case 14, Lemmas 8–9) and §7, Lemma 17.
* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §1.
-/

public section

open Monoid.Coprod TauCeti.GroupAlgGeom
open scoped commutatorElement

universe u v w

namespace TauCeti.LimitGroup.NTQ

/-- A level of a block, in the variables `X` with coefficients in `K`: a level of a raw TQ system,
or a finite quadratic system (every variable occurs, over all its equations, at most twice). -/
inductive BlockLevel (K : Type u) [Group K] (X : Type v) : Type (max u v)
  /-- A level of a raw triangular quasi-quadratic system. -/
  | level (L : Level K X)
  /-- A finite quadratic system. -/
  | quadraticSystem (Q : Finset (GX K X)) (hQ : Quadratic.IsQuadratic Q)

namespace BlockLevel

variable {K : Type u} [Group K] {X : Type v}

/-- The equations of a level of a block. -/
def equations : BlockLevel K X → Set (GX K X)
  | level L => L.equations
  | quadraticSystem Q _ => (Q : Set (GX K X))

@[simp]
theorem equations_level (L : Level K X) : (level L).equations = L.equations := (rfl)

@[simp]
theorem equations_quadraticSystem (Q : Finset (GX K X)) (hQ : Quadratic.IsQuadratic Q) :
    (quadraticSystem Q hQ).equations = (Q : Set (GX K X)) := (rfl)

variable {K' : Type w} [Group K'] (f : K →* K')

open scoped Classical in
/-- The image of a level of a block under a change of coefficients `f : K →* K'`: a centralizer
level goes to the centralizer level of the image of its set of coefficients, abelian and empty
levels are unchanged, and a quadratic system goes to the quadratic system of the images of its
equations. A standard quadratic level `S = 1` goes, as the quadratic system `{S}`, to the quadratic
system `{f(S)}`: `f` may send a coefficient of the standard form to `1`. -/
noncomputable def map : BlockLevel K X → BlockLevel K' X
  | level (.quadratic Q) => quadraticSystem (({Q.toWord} : Finset (GX K X)).image
      (Monoid.Coprod.map f (FreeGroup.map id))) (Q.isQuadratic.image_map f)
  | level (.centralizer U hU) => level (.centralizer (f '' U) (hU.image f))
  | level .abelian => level .abelian
  | level .empty => level .empty
  | quadraticSystem Q hQ =>
    quadraticSystem (Q.image (Monoid.Coprod.map f (FreeGroup.map id))) (hQ.image_map f)

@[simp]
theorem map_quadraticSystem [DecidableEq (GX K' X)] (Q : Finset (GX K X))
    (hQ : Quadratic.IsQuadratic Q) : (quadraticSystem Q hQ).map f =
      quadraticSystem (Q.image (Monoid.Coprod.map f (FreeGroup.map id))) (hQ.image_map f) := by
  rw [map]
  congr!

/-- A standard quadratic level is mapped as the quadratic system of its equation. -/
@[simp]
theorem map_level_quadratic (Q : Quadratic.Standard K X) : (level (.quadratic Q)).map f =
    (quadraticSystem {Q.toWord} Q.isQuadratic).map f := (rfl)

@[simp]
theorem map_level_centralizer (U : Set K) (hU : U.Finite) :
    (level (.centralizer U hU) : BlockLevel K X).map f =
      level (.centralizer (f '' U) (hU.image f)) := (rfl)

@[simp]
theorem map_level_abelian : (level .abelian : BlockLevel K X).map f = level .abelian := (rfl)

@[simp]
theorem map_level_empty : (level .empty : BlockLevel K X).map f = level .empty := (rfl)

/-- The equations of the image of a level under a change of coefficients are the images of its
equations. -/
@[simp]
theorem equations_map (L : BlockLevel K X) : (L.map f).equations =
    Monoid.Coprod.map f (FreeGroup.map id) '' L.equations := by
  classical
  rcases L with ((Q | ⟨U, hU⟩ | _ | _) | ⟨Q, hQ⟩) <;> ext w <;>
    simp [Level.equations_centralizer, Level.equations_abelian, or_and_right, exists_or,
      map_commutatorElement]

end BlockLevel

/-- A block of levels over the system `S₀` in the variables `Z`, in the total variables `Y`,
built from the bottom up: `base` has no level and the variables `Z`; `cons B X L` puts the level
`L`, in finitely many new variables `X` and with coefficients the words `G[Y]` in the variables of
`B`, on top of `B`. -/
inductive Block (G : Type u) [Group G] (Z : Type v) (S₀ : Set (GX G Z)) :
    Type v → Type (max u (v + 1))
  /-- The block with no level. -/
  | base : Block G Z S₀ Z
  /-- The block with top level `L` in the variables `X` over the block `B`. -/
  | cons {Y : Type v} (B : Block G Z S₀ Y) (X : Type v) [Finite X] (L : BlockLevel (GX G Y) X) :
      Block G Z S₀ (X ⊕ Y)

namespace Block

variable {G : Type u} [Group G] {Z : Type v} {S₀ : Set (GX G Z)}

/-- The equations of a block, as a subset of `G[Y]`: those of `S₀` for `base`; for `cons B X L`,
the equations of `B` in the lower variables `Sum.inr`, and the equations of the top level `L`, in
the variables `Sum.inl` and with their coefficients `G[Y]` read in `G[X ⊕ Y]`. -/
def equations : {Y : Type v} → Block G Z S₀ Y → Set (GX G Y)
  | _, base => S₀
  | _, cons B _ L =>
    Monoid.Coprod.map (.id G) (FreeGroup.map Sum.inr) '' B.equations ∪
      eval (Monoid.Coprod.map (.id G) (FreeGroup.map Sum.inr))
        (fun x ↦ inr (FreeGroup.of (Sum.inl x))) '' L.equations

@[simp]
theorem equations_base : (base : Block G Z S₀ Z).equations = S₀ := (rfl)

theorem equations_cons {Y X : Type v} [Finite X] (B : Block G Z S₀ Y) (L : BlockLevel (GX G Y) X) :
    (cons B X L).equations = Monoid.Coprod.map (.id G) (FreeGroup.map Sum.inr) '' B.equations ∪
      eval (Monoid.Coprod.map (.id G) (FreeGroup.map Sum.inr))
        (fun x ↦ inr (FreeGroup.of (Sum.inl x))) '' L.equations := (rfl)

/-- A point of `cons B X L` is a point `w = v ∘ Sum.inr` of the block `B` together with a solution
`v ∘ Sum.inl` of the top level `L` whose coefficients are evaluated at `w`. -/
theorem mem_V_cons {H : Type*} [Group H] {ι : G →* H} {Y X : Type v} [Finite X] {B : Block G Z S₀ Y}
    {L : BlockLevel (GX G Y) X} {v : X ⊕ Y → H} : v ∈ V ι (cons B X L).equations ↔
      v ∘ Sum.inr ∈ V ι B.equations ∧ v ∘ Sum.inl ∈ V (eval ι (v ∘ Sum.inr)) L.equations := by
  simp [equations_cons, V_union, mem_V, ← MonoidHom.comp_apply, MonoidHom.comp_eval,
    eval_comp_map, Function.comp_def]

/-- The *fundamental points* of a block over the set `P₀` of base points: the base points for
`base`; for `cons B X L`, the points `v` such that `v ∘ Sum.inr` is a fundamental point of `B` and
`v ∘ Sum.inl` is the value at `v ∘ Sum.inr` of a solution `s` of the top level `L` in the coordinate
group `G[Y] ⧸ Rad_G(B)` of the block below (given by representatives in `G[Y]`). The radical is
that of all equations of `B`, those of `S₀` included. -/
def fundPoints (P₀ : Set (Z → G)) : {Y : Type v} → Block G Z S₀ Y → Set (Y → G)
  | _, base => P₀
  | _, cons (Y := Y) B X L => {v | v ∘ Sum.inr ∈ fundPoints P₀ B ∧
      ∃ s : X → GX G Y,
        (fun x ↦ (s x : CoordGroup (MonoidHom.id G) B.equations)) ∈
          V (QuotientGroup.mk' (Rad (MonoidHom.id G) B.equations)) L.equations ∧
        v ∘ Sum.inl = fun x ↦ eval (MonoidHom.id G) (v ∘ Sum.inr) (s x)}

@[simp]
theorem fundPoints_base (P₀ : Set (Z → G)) : (base : Block G Z S₀ Z).fundPoints P₀ = P₀ := (rfl)

theorem mem_fundPoints_cons {P₀ : Set (Z → G)} {Y X : Type v} [Finite X] {B : Block G Z S₀ Y}
    {L : BlockLevel (GX G Y) X} {v : X ⊕ Y → G} : v ∈ (cons B X L).fundPoints P₀ ↔
      v ∘ Sum.inr ∈ B.fundPoints P₀ ∧
      ∃ s : X → GX G Y,
        (fun x ↦ (s x : CoordGroup (MonoidHom.id G) B.equations)) ∈
          V (QuotientGroup.mk' (Rad (MonoidHom.id G) B.equations)) L.equations ∧
        v ∘ Sum.inl = fun x ↦ eval (MonoidHom.id G) (v ∘ Sum.inr) (s x) := Iff.rfl

/-- Over base points that are solutions of `S₀`, the fundamental points of a block are solutions
of the block. -/
theorem fundPoints_subset_V {P₀ : Set (Z → G)} (hP₀ : P₀ ⊆ V (MonoidHom.id G) S₀) {Y : Type v}
    (B : Block G Z S₀ Y) : B.fundPoints P₀ ⊆ V (MonoidHom.id G) B.equations := by
  induction B with
  | base => exact hP₀
  | cons B X L ih =>
    rintro v ⟨hw, s, hs, hv⟩
    exact mem_V_cons.2 ⟨ih hw, hv ▸ CoordGroup.eval_mem_V_of_mk_mem_V (ih hw) hs⟩

/-- Fundamental points are monotone in the base points. -/
theorem fundPoints_mono {P₀ P₁ : Set (Z → G)} (h : P₀ ⊆ P₁) {Y : Type v} (B : Block G Z S₀ Y) :
    B.fundPoints P₀ ⊆ B.fundPoints P₁ := by
  induction B with
  | base => exact h
  | cons B X L ih => exact fun v hv ↦ ⟨ih hv.1, hv.2⟩

section Append

variable {Z' : Type v} {S₀' : Set (GX G Z')} {Y Y'' X : Type v} {B : Block G Z S₀ Y}
  {B'' : Block G Z' S₀' Y''} {q : Y → GX G Y''}

/-- The word map extending `q : Y → G[Y'']` by the identity on new variables `X`. -/
private def consWordMap (q : Y → GX G Y'') : X ⊕ Y → GX G (X ⊕ Y'') :=
  Sum.elim (fun x ↦ inr (FreeGroup.of (Sum.inl x)))
    fun y ↦ Monoid.Coprod.map (.id G) (FreeGroup.map Sum.inr) (q y)

private theorem wordMap_consWordMap_comp_inl (v : X ⊕ Y'' → G) :
    wordMap (.id G) (consWordMap q) v ∘ Sum.inl = v ∘ Sum.inl := by
  funext x
  simp [consWordMap]

private theorem wordMap_consWordMap_comp_inr (v : X ⊕ Y'' → G) :
    wordMap (.id G) (consWordMap q) v ∘ Sum.inr = wordMap (.id G) q (v ∘ Sum.inr) := by
  funext y
  simp [consWordMap]

/-- A word map `q` from the solutions of `B''` to those of `B` extends, by the identity on the
variables of a level `L` over `B`, to a word map from the solutions of `L` put on `B''` with its
coefficients substituted by `q` to the solutions of `L` put on `B`. -/
private theorem mapsTo_wordMap_consWordMap [Finite X]
    (hq : Set.MapsTo (wordMap (.id G) q) (V (.id G) B''.equations) (V (.id G) B.equations))
    (L : BlockLevel (GX G Y) X) : Set.MapsTo (wordMap (.id G) (consWordMap q))
      (V (.id G) (cons B'' X (L.map (eval inl q))).equations)
      (V (.id G) (cons B X L).equations) := by
  intro v hv
  rw [mem_V_cons] at hv ⊢
  refine ⟨wordMap_consWordMap_comp_inr v ▸ hq hv.1, ?_⟩
  simpa [mem_V, eval_comp_eval, wordMap_consWordMap_comp_inl, wordMap_consWordMap_comp_inr]
    using hv.2

/-- Under the hypothesis of `mapsTo_wordMap_consWordMap`, if the fundamental points of `B` over
`P` are images under `q` of fundamental points of `B''` over `P''`, the same holds for a level `L`
put on `B`, and on `B''` with its coefficients substituted by `q`. -/
private theorem fundPoints_cons_subset_image [Finite X] {P : Set (Z → G)} {P'' : Set (Z' → G)}
    (hq : Set.MapsTo (wordMap (.id G) q) (V (.id G) B''.equations) (V (.id G) B.equations))
    (hB : B.fundPoints P ⊆ wordMap (.id G) q '' B''.fundPoints P'') (L : BlockLevel (GX G Y) X) :
    (cons B X L).fundPoints P ⊆ wordMap (.id G) (consWordMap q) ''
      (cons B'' X (L.map (eval inl q))).fundPoints P'' := by
  rintro v ⟨hv, s, hs, hvs⟩
  obtain ⟨u, hu, hvu⟩ := hB hv
  refine ⟨Sum.elim (v ∘ Sum.inl) u, ⟨by rwa [Sum.elim_comp_inr], fun x ↦ eval inl q (s x), ?_, ?_⟩,
    ?_⟩
  · rw [BlockLevel.equations_map]
    exact CoordGroup.mk_eval_mem_V_image_map_of_mk_mem_V hq hs
  · funext x
    rw [Sum.elim_comp_inl, Sum.elim_comp_inr, hvs, ← hvu]
    exact (DFunLike.congr_fun (eval_comp_eval q u) (s x)).symm
  · funext i
    rcases i with x | y
    · simp [consWordMap]
    · simpa [consWordMap] using congrFun hvu y

/-- Let `B` be a block over `S₀` and `B'` a block over another system, with a word map `p` sending
the solutions of `B'` to solutions of `S₀`. Then there are a block `B''` over the system of `B'`
(in the construction: `B'` followed by the levels of `B`, their coefficients read through `p`) and a
word map `q` sending its solutions to solutions of `B`, such that every fundamental point of `B`
over the images under `p` of fundamental points of `B'` is the image under `q` of a fundamental
point of `B''`. -/
theorem exists_append {Y : Type v} (B : Block G Z S₀ Y) {Z' Y' : Type v} {S₀' : Set (GX G Z')}
    (B' : Block G Z' S₀' Y') (p : Z → GX G Y')
    (hp : Set.MapsTo (wordMap (MonoidHom.id G) p) (V (MonoidHom.id G) B'.equations)
      (V (MonoidHom.id G) S₀)) : ∃ (Y'' : Type v) (B'' : Block G Z' S₀' Y'') (q : Y → GX G Y''),
      Set.MapsTo (wordMap (MonoidHom.id G) q) (V (MonoidHom.id G) B''.equations)
        (V (MonoidHom.id G) B.equations) ∧
      ∀ P₀ : Set (Z' → G), B.fundPoints (wordMap (MonoidHom.id G) p '' B'.fundPoints P₀) ⊆
        wordMap (MonoidHom.id G) q '' B''.fundPoints P₀ := by
  induction B with
  | base => exact ⟨Y', B', p, equations_base (S₀ := S₀) ▸ hp, fun P₀ ↦ (fundPoints_base _).subset⟩
  | cons B X L ih =>
    obtain ⟨Y'', B'', q, hq, hB⟩ := ih
    exact ⟨X ⊕ Y'', cons B'' X (L.map (eval inl q)), consWordMap q,
      mapsTo_wordMap_consWordMap hq L, fun P₀ ↦ fundPoints_cons_subset_image hq (hB P₀) L⟩

end Append

/-- Over a free group, take the block with one centralizer level `{a}`, in one variable `x`, over
the system `h₀ h₁⁻¹ = 1` in two variables. Its fundamental points over the solutions of that system
are the points with `h₀ = h₁` and `x` a power of `a`. -/
example {α : Type u} (a : α) :
    (cons (base : Block (FreeGroup α) (Fin 2) {inr (.of 0) * (inr (.of 1))⁻¹} (Fin 2)) PUnit
      (.level (.centralizer {inl (FreeGroup.of a)} (Set.finite_singleton _)))).fundPoints
        (V (.id _) {inr (.of 0) * (inr (.of 1))⁻¹}) =
      {v | v (.inr 0) = v (.inr 1) ∧ v (.inl .unit) ∈ Subgroup.zpowers (FreeGroup.of a)} := by
  ext v
  constructor
  · intro hv
    obtain ⟨h₀, h₁⟩ := mem_V_cons.1 (fundPoints_subset_V subset_rfl _ hv)
    rw [BlockLevel.equations_level, Level.mem_V_centralizer] at h₁
    simp only [equations_base, mem_V, Set.mem_singleton_iff, forall_eq, map_mul, map_inv,
      eval_inr_of, Function.comp_apply, mul_inv_eq_one] at h₀
    exact ⟨h₀, FreeGroup.commute_of_iff.mp (Commute.symm (by simpa using h₁.2 .unit _ rfl))⟩
  · rintro ⟨h, n, hn⟩
    refine mem_fundPoints_cons.2
      ⟨by simpa [mul_inv_eq_one] using h, fun _ ↦ inl (FreeGroup.of a ^ n), ?_, ?_⟩
    · rw [BlockLevel.equations_level, Level.mem_V_centralizer]
      refine ⟨fun _ _ ↦ .refl _, fun _ c hc ↦ ?_⟩
      rw [Set.mem_singleton_iff.1 hc]
      simp
    · funext x
      simp [← hn]

end Block

end TauCeti.LimitGroup.NTQ

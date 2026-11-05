/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import TauCeti.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# The join of simplicial sets

The join `K ⋆ L` of simplicial sets `K` and `L` is the simplicial set whose `n`-simplices are the
decompositions of the vertices `{0, …, n}` into an initial segment `I` and a final segment `J`,
together with a simplex of `K` with vertices `I` and a simplex of `L` with vertices `J`, where a
simplex on the empty set of vertices is a single point. Thus `K` and `L` are the parts of `K ⋆ L`
over the two vertices of `Δ[1]`, and every simplex of `K` is joined to every simplex of `L`. The
join is the operation through which cone and slice quasicategories, and hence limits and colimits
in quasicategories, are defined: a cocone on a diagram `Y ⟶ C` is a map `Y ⋆ Δ[0] ⟶ C` extending
it.

The decomposition of the vertices of a simplex is a map to `Δ[1]`, and the simplices of `K` and
`L` are maps from the parts over the vertices `0` and `1` of `Δ[1]`. Accordingly, a map from any
simplicial set `X` to the join is described by *join data* (`SSet.JoinData X K L`): a map
`p : X ⟶ Δ[1]` together with maps to `K` and `L` from the subcomplexes `SSet.joinFiber p 0` and
`SSet.joinFiber p 1` of `X` lying over the two vertices. The join is the simplicial set of join data
on standard simplices, and `SSet.join.homEquiv` identifies its maps from `X` with the join data on
`X`.

## Main definitions

* `SSet.joinFiber p e`: the part of `X` over the vertex `e` of `Δ[1]` along `p : X ⟶ Δ[1]`.
* `SSet.JoinData X K L`: the data of a map `X ⟶ K ⋆ L`, with its restriction
  `SSet.JoinData.precomp` along maps `Y ⟶ X`.
* `SSet.join K L`: the join `K ⋆ L`, whose simplices are the join data on standard simplices
  (`SSet.join.objEquiv`).
* `SSet.join.π`: the projection `K ⋆ L ⟶ Δ[1]`.
* `SSet.join.inl`, `SSet.join.inr`: the inclusions of `K` and `L` as the parts over `0` and `1`.
* `SSet.join.joinFiberZeroIso`, `SSet.join.joinFiberOneIso`: the parts of `K ⋆ L` over the vertices
  `0` and `1` are `K` and `L`, through the inverses of the inclusions.
* `SSet.join.map`: the functoriality of the join in both variables.
* `SSet.join.edgeMk`: the edge of `K ⋆ L` from a vertex of `K` to a vertex of `L`.
* `SSet.joinFiberZeroRetraction`: the retraction of `Δ[m]` onto its part over the vertex `0` of
  `Δ[1]`, when that part contains the vertex `0`.
* `SSet.Subcomplex.unionJoin A B`: for subcomplexes `A` of `K` and `B` of `L`, the subcomplex
  `(A ⋆ L) ∪ (K ⋆ B)` of `K ⋆ L`, the domain of the pushout-join of their inclusions.

## Main results

* `SSet.join.homEquiv`: maps `X ⟶ K ⋆ L` correspond to join data on `X`, naturally in `X`
  (`SSet.join.homEquiv_comp`); this is the representability `SSet.join.representableBy`.
* `SSet.join.edge_mem_joinFiber_zero`: an edge of `K ⋆ L` ending over the vertex `0` lies over
  `0`.
* `SSet.join.exists_eq_comp_inr_or_exists_eq_comp_map`: every simplex of `K ⋆ L` comes from `L`
  or is the image of a simplex of `Δ[m] ⋆ L` under `g ⋆ L` for a simplex `g : Δ[m] ⟶ K`.
* `SSet.Subcomplex.mem_unionJoin_iff`: a simplex of `K ⋆ L` lies in `(A ⋆ L) ∪ (K ⋆ B)` exactly
  when its part in `K` lies in `A` or its part in `L` lies in `B`.
* `SSet.Subcomplex.unionJoin_le_iff`: `(A ⋆ L) ∪ (K ⋆ B)` lies in a subcomplex exactly when the
  images of `A ⋆ L` and `K ⋆ B` do.
* `SSet.Subcomplex.unionJoin.isPushout`: `(A ⋆ L) ∪ (K ⋆ B)` is the pushout of `A ⋆ L` and
  `K ⋆ B` along `A ⋆ B`.
* `SSet.join.isoOfIsTerminal`: the join of two terminal simplicial sets, such as
  `Δ[0] ⋆ Δ[0]`, is `Δ[1]`.
* `SSet.join.quasicategory`: the join of two quasicategories is a quasicategory (Joyal).

## Implementation notes

The universal property reduces Joyal's theorem to horn filling in `K`, `L` and `Δ[1]`
(`SSet.JoinData.exists_precomp_horn_ι_eq`): over `Δ[1]`, an inner horn lies either entirely over
one vertex, or so that its parts over both vertices are faces contained in the horn.

The pushout square `SSet.Subcomplex.unionJoin.isPushout` is obtained, as Mathlib's
`SSet.Subcomplex.unionProd.isPushout` (Joël Riou and Jack McKoen) is for products, from the
bicartesian square of subcomplexes formed by `A ⋆ B`, `A ⋆ L`, `K ⋆ B` and their union.

## References

* J. Lurie, *Higher Topos Theory*, Definition 1.2.8.1 and Proposition 1.2.8.3.
* A. Joyal, *Quasi-categories and Kan complexes*, J. Pure Appl. Algebra 175 (2002).
-/

public section

open CategoryTheory Opposite Simplicial

universe u

namespace SSet

variable {X Y Z K L K' L' K'' L'' : SSet.{u}}

/-- The part of a simplicial set `X` lying over the vertex `e` of `Δ[1]` along `p : X ⟶ Δ[1]`:
the subcomplex of the simplices all of whose vertices are sent to `e`. -/
@[expose]
def joinFiber (p : X ⟶ Δ[1]) (e : Fin 2) : X.Subcomplex :=
  (stdSimplex.face {e}).preimage p

@[simp]
lemma mem_joinFiber_iff (p : X ⟶ Δ[1]) (e : Fin 2) {d : ℕ} (x : X _⦋d⦌) :
    x ∈ (joinFiber p e).obj _ ↔ ∀ j, p.app _ x j = e := by
  simp [joinFiber]

/-- The whole of `X` lies over the vertex `e` along the constant map at `e`. -/
@[simp]
lemma joinFiber_const_self (e : Fin 2) :
    joinFiber (const (stdSimplex.const 1 e _) : X ⟶ Δ[1]) e = ⊤ := by
  ext n x
  induction n using Opposite.rec with | op n
  induction n using SimplexCategory.rec with | _ n
  simp only [mem_joinFiber_iff, stdSimplex.const_app_apply, implies_true, Subfunctor.top_obj,
    Set.mem_univ]

/-- Nothing lies over the vertex `e'` along the constant map at a different vertex `e`. -/
@[simp]
lemma joinFiber_const_of_ne {e e' : Fin 2} (h : e ≠ e') :
    joinFiber (const (stdSimplex.const 1 e _) : X ⟶ Δ[1]) e' = ⊥ := by
  ext n x
  induction n using Opposite.rec with | op n
  induction n using SimplexCategory.rec with | _ n
  simp only [mem_joinFiber_iff, stdSimplex.const_app_apply, Subfunctor.bot_obj,
    Set.mem_empty_iff_false, iff_false, not_forall]
  exact ⟨0, h⟩

/-- The part of `X` over the vertex `e` lies over `e`. -/
@[reassoc (attr := simp)]
lemma joinFiber_ι_comp (p : X ⟶ Δ[1]) (e : Fin 2) :
    (joinFiber p e).ι ≫ p = const (stdSimplex.const 1 e _) := by
  ext n ⟨x, hx⟩
  induction n using Opposite.rec with | op n
  induction n using SimplexCategory.rec with | _ n
  exact stdSimplex.ext _ _ ((mem_joinFiber_iff p e x).1 hx)

/-- The vertex `j` of `Δ[m]` lies over the vertex `e` of `Δ[1]` along `q` exactly when `q` sends
`j` to `e`. -/
lemma obj₀Equiv_symm_mem_joinFiber_iff {m : ℕ} (q : Δ[m] ⟶ Δ[1]) (e : Fin 2) (j : Fin (m + 1)) :
    stdSimplex.obj₀Equiv.symm j ∈ (joinFiber q e).obj (op ⦋0⦌) ↔ yonedaEquiv q j = e := by
  simp [stdSimplex.hom_app_apply]

/-- Every vertex of a simplex of `Δ[d]` over the vertex `c` of `Δ[1]` along `q` is sent to `c` by
`q`. -/
lemma yonedaEquiv_apply_of_mem_joinFiber {d : ℕ} {q : Δ[d] ⟶ Δ[1]} {c : Fin 2} {a : ℕ}
    {y : Δ[d] _⦋a⦌} (hy : y ∈ (joinFiber q c).obj _) (t : Fin (a + 1)) :
    yonedaEquiv q (y t) = c := by
  rw [← stdSimplex.hom_app_apply]
  exact (mem_joinFiber_iff _ _ _).1 hy t

/-- A map to `Δ[k]` from the part of `Δ[d]` over a vertex `c` of `Δ[1]` is monotone on the vertices
over `c`. -/
lemma joinFiber_hom_vertex_le {d k : ℕ} {q : Δ[d] ⟶ Δ[1]} {c : Fin 2}
    (g : (joinFiber q c : SSet) ⟶ Δ[k]) {j l : Fin (d + 1)} (hjl : j ≤ l)
    (hj : yonedaEquiv q j = c) (hl : yonedaEquiv q l = c) :
    g.app _ ⟨stdSimplex.obj₀Equiv.symm j, (obj₀Equiv_symm_mem_joinFiber_iff _ _ _).2 hj⟩ 0 ≤
      g.app _ ⟨stdSimplex.obj₀Equiv.symm l, (obj₀Equiv_symm_mem_joinFiber_iff _ _ _).2 hl⟩ 0 := by
  have hy : stdSimplex.edge d j l hjl ∈ (joinFiber q c).obj _ := by
    rw [mem_joinFiber_iff]
    intro t
    fin_cases t <;> simpa [stdSimplex.hom_app_apply]
  -- The edge from `j` to `l` goes to an edge of `Δ[k]` from the image of `j` to that of `l`.
  have h : g.app _ ⟨_, hy⟩ 0 ≤ g.app _ ⟨_, hy⟩ 1 := stdSimplex.monotone_apply _ (Fin.zero_le 1)
  rw [stdSimplex.subcomplex_hom_app_apply g _ hy 0
      ((obj₀Equiv_symm_mem_joinFiber_iff _ _ _).2 (by simpa using hj)),
    stdSimplex.subcomplex_hom_app_apply g _ hy 1
      ((obj₀Equiv_symm_mem_joinFiber_iff _ _ _).2 (by simpa using hl))] at h
  simpa only [stdSimplex.edge_apply_zero, stdSimplex.edge_apply_one] using h

section retraction

variable {m : ℕ} (q : Δ[m] ⟶ Δ[1]) (h : yonedaEquiv q 0 = 0)

/-- The last vertex of `Δ[m]` lying over the vertex `0` of `Δ[1]`. -/
private noncomputable def lastZero : Fin (m + 1) :=
  (Finset.univ.filter fun j ↦ yonedaEquiv q j = 0).max' ⟨0, by simp [h]⟩

private lemma apply_lastZero : yonedaEquiv q (lastZero q h) = 0 := by
  have := Finset.max'_mem (Finset.univ.filter fun j ↦ yonedaEquiv q j = 0) ⟨0, by simp [h]⟩
  simpa [lastZero] using this

private lemma le_lastZero {j : Fin (m + 1)} (hj : yonedaEquiv q j = 0) : j ≤ lastZero q h :=
  Finset.le_max' _ _ (by simp [hj])

private lemma apply_min_lastZero (j : Fin (m + 1)) :
    yonedaEquiv q (min j (lastZero q h)) = 0 :=
  le_antisymm ((stdSimplex.monotone_apply _ (min_le_right _ _)).trans
    (apply_lastZero q h).le) (Fin.zero_le _)

/-- When the vertex `0` of `Δ[m]` lies over the vertex `0` of `Δ[1]` along `q`, the retraction of
`Δ[m]` onto its part over `0`, which collapses the vertices over `1` onto the last vertex over
`0`. -/
noncomputable def joinFiberZeroRetraction : Δ[m] ⟶ (joinFiber q 0 : SSet) :=
  Subcomplex.lift (stdSimplex.map (SimplexCategory.mkHom
    ⟨fun j ↦ min j (lastZero q h), fun _ _ hab ↦ min_le_min_right _ hab⟩)) (by
    rintro ⟨k⟩ _ ⟨y, rfl⟩
    induction k using SimplexCategory.rec with | _ k
    rw [mem_joinFiber_iff]
    intro j
    rw [stdSimplex.hom_app_apply]
    exact apply_min_lastZero q h _)

/-- The retraction `joinFiberZeroRetraction` fixes the part of `Δ[m]` over `0`. -/
lemma joinFiberZeroRetraction_app_of_mem {k : ℕ} (y : Δ[m] _⦋k⦌)
    (hy : y ∈ (joinFiber q 0).obj _) : (joinFiberZeroRetraction q h).app _ y = ⟨y, hy⟩ := by
  apply Subtype.ext
  refine stdSimplex.ext _ _ fun j ↦ ?_
  have hyj := (mem_joinFiber_iff q 0 y).1 hy j
  rw [stdSimplex.hom_app_apply] at hyj
  exact min_eq_left (le_lastZero q h hyj)

/-- The retraction `joinFiberZeroRetraction` is a retraction of the inclusion of the part of `Δ[m]`
over `0`. -/
@[reassoc (attr := simp)]
lemma ι_joinFiberZeroRetraction : (joinFiber q 0).ι ≫ joinFiberZeroRetraction q h = 𝟙 _ := by
  ext ⟨k⟩ ⟨y, hy⟩
  induction k using SimplexCategory.rec with | _ k
  exact joinFiberZeroRetraction_app_of_mem q h y hy

end retraction

/-- If the vertex `0` of `Δ[m]` does not lie over `0` along `q`, every vertex lies over `1`. -/
private lemma yonedaEquiv_apply_eq_one_of_ne_zero {m : ℕ} {q : Δ[m] ⟶ Δ[1]}
    (h : yonedaEquiv q 0 ≠ 0) (j : Fin (m + 1)) : yonedaEquiv q j = 1 := by
  have h10 : ∀ a : Fin 2, a ≠ 0 → a = 1 := by decide
  exact le_antisymm (Fin.le_last _) (h10 _ h ▸ stdSimplex.monotone_apply _ (Fin.zero_le j))

/-- If the vertex `0` of `Δ[m]` does not lie over `0` along `q`, the whole of `Δ[m]` lies over
`1`. -/
lemma joinFiber_one_eq_top {m : ℕ} {q : Δ[m] ⟶ Δ[1]} (h : yonedaEquiv q 0 ≠ 0) :
    joinFiber q 1 = ⊤ := by
  ext k x
  induction k using Opposite.rec with | op k
  induction k using SimplexCategory.rec with | _ k
  simp only [mem_joinFiber_iff, stdSimplex.hom_app_apply, Subfunctor.top_obj, Set.mem_univ,
    iff_true]
  exact fun _ ↦ yonedaEquiv_apply_eq_one_of_ne_zero h _

/-- The data of a map from `X` to the join of `K` and `L`: a map `p : X ⟶ Δ[1]`, a map to `K` from
the part of `X` over the vertex `0`, and a map to `L` from the part of `X` over the vertex `1`. -/
structure JoinData (X K L : SSet.{u}) where
  /-- The map to `Δ[1]`. -/
  p : X ⟶ Δ[1]
  /-- The map to `K` from the part over the vertex `0`. -/
  left : (joinFiber p 0 : SSet) ⟶ K
  /-- The map to `L` from the part over the vertex `1`. -/
  right : (joinFiber p 1 : SSet) ⟶ L

namespace JoinData

/-- Join data are equal when their maps to `Δ[1]` agree and their maps to `K` and `L` agree on
every simplex. -/
@[ext]
lemma ext {d d' : JoinData X K L} (hp : d.p = d'.p)
    (hl : ∀ (n : SimplexCategoryᵒᵖ) (x : X.obj n) (hx : x ∈ (joinFiber d.p 0).obj n)
      (hx' : x ∈ (joinFiber d'.p 0).obj n), d.left.app n ⟨x, hx⟩ = d'.left.app n ⟨x, hx'⟩)
    (hr : ∀ (n : SimplexCategoryᵒᵖ) (x : X.obj n) (hx : x ∈ (joinFiber d.p 1).obj n)
      (hx' : x ∈ (joinFiber d'.p 1).obj n), d.right.app n ⟨x, hx⟩ = d'.right.app n ⟨x, hx'⟩) :
    d = d' := by
  obtain ⟨p, l, r⟩ := d
  obtain ⟨p', l', r'⟩ := d'
  obtain rfl : p = p' := hp
  congr 1
  · ext n ⟨x, hx⟩
    exact hl n x hx hx
  · ext n ⟨x, hx⟩
    exact hr n x hx hx

/-- Equal join data have equal maps to `K`. -/
lemma congr_left_app {d d' : JoinData X K L} (h : d = d') {n : SimplexCategoryᵒᵖ} (x : X.obj n)
    (hx : x ∈ (joinFiber d.p 0).obj n) (hx' : x ∈ (joinFiber d'.p 0).obj n) :
    d.left.app n ⟨x, hx⟩ = d'.left.app n ⟨x, hx'⟩ := by
  subst h
  rfl

/-- Equal join data have equal maps to `L`. -/
lemma congr_right_app {d d' : JoinData X K L} (h : d = d') {n : SimplexCategoryᵒᵖ} (x : X.obj n)
    (hx : x ∈ (joinFiber d.p 1).obj n) (hx' : x ∈ (joinFiber d'.p 1).obj n) :
    d.right.app n ⟨x, hx⟩ = d'.right.app n ⟨x, hx'⟩ := by
  subst h
  rfl

/-- The restriction of join data on `X` along a map `g : Y ⟶ X`. -/
@[expose, simps p]
def precomp (d : JoinData X K L) (g : Y ⟶ X) : JoinData Y K L where
  p := g ≫ d.p
  left := (joinFiber d.p 0).fromPreimage g ≫ d.left
  right := (joinFiber d.p 1).fromPreimage g ≫ d.right

@[simp]
lemma precomp_left_app (d : JoinData X K L) (g : Y ⟶ X) {n : SimplexCategoryᵒᵖ} (y : Y.obj n)
    (hy : y ∈ (joinFiber (d.precomp g).p 0).obj n) :
    dsimp% (d.precomp g).left.app n ⟨y, hy⟩ = d.left.app n ⟨g.app n y, hy⟩ :=
  (rfl)

@[simp]
lemma precomp_right_app (d : JoinData X K L) (g : Y ⟶ X) {n : SimplexCategoryᵒᵖ} (y : Y.obj n)
    (hy : y ∈ (joinFiber (d.precomp g).p 1).obj n) :
    dsimp% (d.precomp g).right.app n ⟨y, hy⟩ = d.right.app n ⟨g.app n y, hy⟩ :=
  (rfl)

/-- Along join data on `Δ[k]` restricted by `g : Δ[k'] ⟶ Δ[k]`, the vertex `j` of `Δ[k']` lies over
the vertex of `Δ[1]` over which `yonedaEquiv g j` lies. -/
lemma yonedaEquiv_precomp_p_apply {k k' : ℕ} (d : JoinData Δ[k] K L) (g : Δ[k'] ⟶ Δ[k])
    (j : Fin (k' + 1)) : yonedaEquiv (d.precomp g).p j = yonedaEquiv d.p (yonedaEquiv g j) := by
  rw [precomp_p, yonedaEquiv_comp, stdSimplex.hom_app_apply]

@[simp]
lemma precomp_id (d : JoinData X K L) : d.precomp (𝟙 X) = d :=
  ext (by simp) (fun _ _ _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl)

@[simp]
lemma precomp_precomp (d : JoinData X K L) (g : Y ⟶ X) (h : Z ⟶ Y) :
    (d.precomp g).precomp h = d.precomp (h ≫ g) :=
  ext (by simp) (fun _ _ _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl)

/-- Composition of join data with maps `f : K ⟶ K'` and `g : L ⟶ L'`. -/
def postcomp (d : JoinData X K L) (f : K ⟶ K') (g : L ⟶ L') : JoinData X K' L' where
  p := d.p
  left := d.left ≫ f
  right := d.right ≫ g

@[simp]
lemma postcomp_p (d : JoinData X K L) (f : K ⟶ K') (g : L ⟶ L') : (d.postcomp f g).p = d.p :=
  (rfl)

@[simp]
lemma postcomp_left_app (d : JoinData X K L) (f : K ⟶ K') (g : L ⟶ L') {n : SimplexCategoryᵒᵖ}
    (x : X.obj n) (hx : x ∈ (joinFiber (d.postcomp f g).p 0).obj n) :
    dsimp% (d.postcomp f g).left.app n ⟨x, hx⟩ =
      f.app n (d.left.app n ⟨x, by rwa [postcomp_p] at hx⟩) :=
  (rfl)

@[simp]
lemma postcomp_right_app (d : JoinData X K L) (f : K ⟶ K') (g : L ⟶ L') {n : SimplexCategoryᵒᵖ}
    (x : X.obj n) (hx : x ∈ (joinFiber (d.postcomp f g).p 1).obj n) :
    dsimp% (d.postcomp f g).right.app n ⟨x, hx⟩ =
      g.app n (d.right.app n ⟨x, by rwa [postcomp_p] at hx⟩) :=
  (rfl)

@[simp]
lemma postcomp_id (d : JoinData X K L) : d.postcomp (𝟙 K) (𝟙 L) = d :=
  ext rfl (fun _ _ _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl)

@[simp]
lemma postcomp_postcomp (d : JoinData X K L) (f : K ⟶ K') (g : L ⟶ L') (f' : K' ⟶ K'')
    (g' : L' ⟶ L'') : (d.postcomp f g).postcomp f' g' = d.postcomp (f ≫ f') (g ≫ g') :=
  ext rfl (fun _ _ _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl)

lemma precomp_postcomp (d : JoinData X K L) (h : Y ⟶ X) (f : K ⟶ K') (g : L ⟶ L') :
    (d.postcomp f g).precomp h = (d.precomp h).postcomp f g :=
  ext rfl (fun _ _ _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl)

/-- Composition of join data with monomorphisms is injective. -/
lemma postcomp_injective (f : K ⟶ K') (g : L ⟶ L') [Mono f] [Mono g] :
    Function.Injective fun d : JoinData X K L ↦ d.postcomp f g := by
  rintro ⟨p, l, r⟩ ⟨p', l', r'⟩ h
  obtain rfl : p = p' := congrArg JoinData.p h
  simp only [postcomp, mk.injEq, heq_eq_eq, true_and, cancel_mono] at h
  rw [h.1, h.2]

variable (K L) in
/-- Join data, as a presheaf on simplicial sets. -/
@[expose, simps]
def functor : SSet.{u}ᵒᵖ ⥤ Type u where
  obj X := JoinData X.unop K L
  map g := ↾fun d ↦ d.precomp g.unop

end JoinData

/-- The join `K ⋆ L` of simplicial sets `K` and `L`. Its `n`-simplices are the join data on
`Δ[n]`: a splitting of the vertices of `Δ[n]` into an initial segment and a final segment, with a
simplex of `K` on the first and a simplex of `L` on the second, either of which is omitted when its
segment is empty. -/
@[expose]
def join (K L : SSet.{u}) : SSet.{u} :=
  stdSimplex.op ⋙ JoinData.functor K L

namespace JoinData

/-- Restricting join data along the simplex `x` and evaluating its map to `K` on the top
simplex gives the value of the map to `K` at `x`. -/
lemma precomp_yonedaEquiv_symm_left_app (d : JoinData X K L) {n : SimplexCategory}
    (x : X.obj (op n)) (hx : x ∈ (joinFiber d.p 0).obj _)
    (h : yonedaEquiv (𝟙 _) ∈ (joinFiber (d.precomp (yonedaEquiv.symm x)).p 0).obj (op n)) :
    (d.precomp (yonedaEquiv.symm x)).left.app _ ⟨yonedaEquiv (𝟙 _), h⟩ = d.left.app _ ⟨x, hx⟩ := by
  refine (precomp_left_app d _ _ h).trans (congrArg (d.left.app (op n)) (Subtype.ext ?_))
  dsimp only
  rw [← yonedaEquiv_comp, Category.id_comp, Equiv.apply_symm_apply]

/-- Restricting join data along the simplex `x` and evaluating its map to `L` on the top
simplex gives the value of the map to `L` at `x`. -/
lemma precomp_yonedaEquiv_symm_right_app (d : JoinData X K L) {n : SimplexCategory}
    (x : X.obj (op n)) (hx : x ∈ (joinFiber d.p 1).obj _)
    (h : yonedaEquiv (𝟙 _) ∈ (joinFiber (d.precomp (yonedaEquiv.symm x)).p 1).obj (op n)) :
    (d.precomp (yonedaEquiv.symm x)).right.app _ ⟨yonedaEquiv (𝟙 _), h⟩ =
      d.right.app _ ⟨x, hx⟩ := by
  refine (precomp_right_app d _ _ h).trans (congrArg (d.right.app (op n)) (Subtype.ext ?_))
  dsimp only
  rw [← yonedaEquiv_comp, Category.id_comp, Equiv.apply_symm_apply]

end JoinData

namespace join

/-- The `n`-simplices of the join `K ⋆ L` are the join data on `Δ[n]`. -/
def objEquiv {n : SimplexCategoryᵒᵖ} : (join K L).obj n ≃ JoinData (stdSimplex.obj n.unop) K L :=
  Equiv.refl _

@[simp]
lemma objEquiv_map {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (x : (join K L).obj n) :
    objEquiv ((join K L).map f x) = (objEquiv x).precomp (stdSimplex.map f.unop) :=
  (rfl)

variable (K L) in
/-- The projection of the join `K ⋆ L` to `Δ[1]`. -/
def π : join K L ⟶ Δ[1] where
  app n := ↾fun x ↦ yonedaEquiv (objEquiv x).p
  naturality n m f := by
    ext x
    exact (yonedaEquiv_naturality f.unop (objEquiv x).p).symm

@[simp]
lemma π_app {n : SimplexCategoryᵒᵖ} (x : (join K L).obj n) :
    (π K L).app n x = yonedaEquiv (objEquiv x).p :=
  (rfl)

/-- A simplex `x` of the join lies over the vertex `e` exactly when the top simplex of `Δ[n]` lies
over `e` for the join data of `x`. -/
lemma mem_joinFiber_π_iff {n : SimplexCategory} (x : (join K L).obj (op n)) (e : Fin 2) :
    x ∈ (joinFiber (π K L) e).obj (op n) ↔
      yonedaEquiv (𝟙 _) ∈ (joinFiber (objEquiv x).p e).obj (op n) := by
  simp only [joinFiber, Subcomplex.preimage_obj, Set.mem_preimage, π_app, ← yonedaEquiv_comp,
    Category.id_comp]

variable (K L) in
/-- The map to `T` from the part of the join over the vertex `e` given by a component `c` of join
data on standard simplices compatible with restriction: the component `c` of the join data of a
simplex, evaluated on the top simplex. -/
private def ofFiber (e : Fin 2) {T : SSet.{u}}
    (c : ∀ {n : SimplexCategory} (d : JoinData (stdSimplex.obj n) K L),
      (joinFiber d.p e : SSet) ⟶ T)
    (hc : ∀ {n m : SimplexCategory} (d : JoinData (stdSimplex.obj n) K L)
      (g : stdSimplex.obj m ⟶ stdSimplex.obj n),
      c (d.precomp g) = (joinFiber d.p e).fromPreimage g ≫ c d) :
    (joinFiber (π K L) e : SSet) ⟶ T where
  app n := ↾fun x ↦ (c (objEquiv x.1)).app n
    ⟨yonedaEquiv (𝟙 _), (mem_joinFiber_π_iff x.1 e).1 x.2⟩
  naturality n m f := by
    ext ⟨x, hx⟩
    induction n using Opposite.rec with | op n
    induction m using Opposite.rec with | op m
    have hs : yonedaEquiv (stdSimplex.{u}.map f.unop) =
        (stdSimplex.obj n).map f (yonedaEquiv (𝟙 _)) := by
      conv_rhs => rw [← Quiver.Hom.op_unop f]
      rw [yonedaEquiv_naturality, Category.comp_id]
    dsimp
    rw [← NatTrans.naturality_apply]
    -- The join data of the face of `x` along `f` is the restriction of the join data of `x`.
    refine (ConcreteCategory.congr_hom
      (NatTrans.congr_app (hc (objEquiv x) (stdSimplex.map f.unop)) (op m)) _).trans ?_
    refine congrArg _ (Subtype.ext ((?_ : _ = yonedaEquiv (stdSimplex.{u}.map f.unop)).trans hs))
    exact (yonedaEquiv_comp (𝟙 (stdSimplex.obj m)) (stdSimplex.map f.unop)).symm.trans
      (congrArg _ (Category.id_comp _))

variable (K L) in
/-- The tautological join data on the join `K ⋆ L`, corresponding to its identity map. -/
def univ : JoinData (join K L) K L where
  p := π K L
  left := ofFiber K L 0 (fun d ↦ d.left) (fun _ _ ↦ rfl)
  right := ofFiber K L 1 (fun d ↦ d.right) (fun _ _ ↦ rfl)

@[simp]
lemma univ_p : (univ K L).p = π K L :=
  (rfl)

lemma univ_left_app {n : SimplexCategory} (x : (join K L).obj (op n))
    (hx : x ∈ (joinFiber (univ K L).p 0).obj (op n)) :
    (univ K L).left.app _ ⟨x, hx⟩ =
      (objEquiv x).left.app _
        ⟨yonedaEquiv (𝟙 _), (mem_joinFiber_π_iff x 0).1 (by simpa using hx)⟩ :=
  (rfl)

lemma univ_right_app {n : SimplexCategory} (x : (join K L).obj (op n))
    (hx : x ∈ (joinFiber (univ K L).p 1).obj (op n)) :
    (univ K L).right.app _ ⟨x, hx⟩ =
      (objEquiv x).right.app _
        ⟨yonedaEquiv (𝟙 _), (mem_joinFiber_π_iff x 1).1 (by simpa using hx)⟩ :=
  (rfl)

/-- Restricting the tautological join data along a simplex `x` of the join gives the join data
of `x`. -/
lemma univ_precomp_yonedaEquiv_symm {n : SimplexCategory} (x : (join K L).obj (op n)) :
    (univ K L).precomp (yonedaEquiv.symm x) = objEquiv x := by
  refine JoinData.ext (yonedaEquiv.injective ?_) ?_ ?_
  · simp [yonedaEquiv_comp]
  · intro k y hy hy'
    induction k using Opposite.rec with | op k
    rw [JoinData.precomp_left_app]
    -- By `univ_left_app` and `yonedaEquiv_symm_app`, the left side evaluates the join data of the
    -- face of `x` along `y`. That is the restriction of the join data of `x` along
    -- `stdSimplex.map (stdSimplex.objEquiv y)`, which is `yonedaEquiv.symm y`.
    exact (univ_left_app _ _).trans ((objEquiv x).precomp_yonedaEquiv_symm_left_app y hy' _)
  · intro k y hy hy'
    induction k using Opposite.rec with | op k
    rw [JoinData.precomp_right_app]
    -- As for the maps to `K`.
    exact (univ_right_app _ _).trans ((objEquiv x).precomp_yonedaEquiv_symm_right_app y hy' _)

/-- The map to the join `K ⋆ L` given by join data on `X`: a simplex `x` of `X` goes to the
restriction of the join data along `x`. -/
private def ofJoinData (d : JoinData X K L) : X ⟶ join K L where
  app n := ↾fun x ↦ objEquiv.symm (d.precomp (yonedaEquiv.symm x))
  naturality n m f := by
    ext x
    induction n using Opposite.rec with | op n
    induction m using Opposite.rec with | op m
    have h : d.precomp (yonedaEquiv.symm (X.map f x)) =
        (d.precomp (yonedaEquiv.symm x)).precomp (stdSimplex.map f.unop) := by
      rw [JoinData.precomp_precomp, yonedaEquiv_symm_naturality_left, Quiver.Hom.op_unop]
    -- Both sides are `objEquiv.symm` of the two sides of `h`, by definition of the action of
    -- the join on simplices.
    exact congrArg objEquiv.symm h

/-- **The universal property of the join**: maps of simplicial sets `X ⟶ K ⋆ L` correspond to join
data on `X`, that is, to a map `p : X ⟶ Δ[1]` together with maps to `K` and `L` from the parts of
`X` over the vertices `0` and `1`. The join data of a map `F` is the restriction of the
tautological join data along `F`. -/
def homEquiv : (X ⟶ join K L) ≃ JoinData X K L where
  toFun F := (univ K L).precomp F
  invFun d := ofJoinData d
  left_inv F := by
    ext n x
    induction n using Opposite.rec with | op n
    apply objEquiv.injective
    simp [ofJoinData, yonedaEquiv_symm_comp, univ_precomp_yonedaEquiv_symm]
  right_inv d := by
    refine JoinData.ext ?_ ?_ ?_
    · ext n x
      induction n using Opposite.rec with | op n
      exact (yonedaEquiv_comp (yonedaEquiv.symm x) d.p).trans
        (congrArg _ (yonedaEquiv.apply_symm_apply x))
    · intro k y hy hy'
      induction k using Opposite.rec with | op k
      rw [JoinData.precomp_left_app]
      -- The simplex of the join attached to `y` is the restriction of `d` along `y`.
      exact (univ_left_app _ _).trans (d.precomp_yonedaEquiv_symm_left_app y hy' _)
    · intro k y hy hy'
      induction k using Opposite.rec with | op k
      rw [JoinData.precomp_right_app]
      exact (univ_right_app _ _).trans (d.precomp_yonedaEquiv_symm_right_app y hy' _)

lemma homEquiv_apply (F : X ⟶ join K L) : homEquiv F = (univ K L).precomp F :=
  (rfl)

@[simp]
lemma homEquiv_comp (f : Y ⟶ X) (F : X ⟶ join K L) :
    homEquiv (f ≫ F) = (homEquiv F).precomp f :=
  ((univ K L).precomp_precomp F f).symm

@[simp]
lemma homEquiv_id : homEquiv (𝟙 (join K L)) = univ K L :=
  (univ K L).precomp_id

/-- The join data of a map `F` to the join has `F ≫ π K L` as its map to `Δ[1]`. -/
@[simp]
lemma homEquiv_p (F : X ⟶ join K L) : (homEquiv F).p = F ≫ π K L :=
  (rfl)

lemma homEquiv_symm_app {n : SimplexCategory} (d : JoinData X K L) (x : X.obj (op n)) :
    (homEquiv.symm d).app _ x = objEquiv.symm (d.precomp (yonedaEquiv.symm x)) :=
  (rfl)

variable (K L) in
/-- The join `K ⋆ L` represents join data. -/
def representableBy : (JoinData.functor K L).RepresentableBy (join K L) where
  homEquiv := homEquiv
  homEquiv_comp f g := homEquiv_comp f g

/-- The map of joins `K ⋆ L ⟶ K' ⋆ L'` induced by maps `f : K ⟶ K'` and `g : L ⟶ L'`. -/
def map (f : K ⟶ K') (g : L ⟶ L') : join K L ⟶ join K' L' :=
  homEquiv.symm ((univ K L).postcomp f g)

@[simp high]
lemma homEquiv_comp_map (F : X ⟶ join K L) (f : K ⟶ K') (g : L ⟶ L') :
    homEquiv (F ≫ map f g) = (homEquiv F).postcomp f g := by
  rw [homEquiv_comp, map, Equiv.apply_symm_apply, homEquiv_apply, JoinData.precomp_postcomp]

/-- The join of two monomorphisms is a monomorphism. -/
instance mono_map (f : K ⟶ K') (g : L ⟶ L') [Mono f] [Mono g] : Mono (map f g) :=
  ⟨fun a b h ↦ homEquiv.injective (JoinData.postcomp_injective f g (by
    simp only [← homEquiv_comp_map, h]))⟩

@[reassoc (attr := simp)]
lemma map_π (f : K ⟶ K') (g : L ⟶ L') : map f g ≫ π K' L' = π K L := by
  rw [← homEquiv_p, ← Category.id_comp (map f g), homEquiv_comp_map]
  simp

@[simp]
lemma map_id : map (𝟙 K) (𝟙 L) = 𝟙 (join K L) :=
  homEquiv.injective (by simp [map])

@[reassoc]
lemma map_comp (f : K ⟶ K') (g : L ⟶ L') (f' : K' ⟶ K'') (g' : L' ⟶ L'') :
    map (f ≫ f') (g ≫ g') = map f g ≫ map f' g' :=
  homEquiv.injective (by
    rw [homEquiv_comp_map, map, map, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      JoinData.postcomp_postcomp])

variable (K L) in
/-- The inclusion of `K` into the join `K ⋆ L`, as the part over the vertex `0`. -/
def inl : K ⟶ join K L :=
  homEquiv.symm
    { p := const (stdSimplex.const 1 0 _)
      left := (joinFiber _ 0).ι
      right := (Subcomplex.eqToIso (joinFiber_const_of_ne (by decide))).hom ≫
        Subcomplex.isInitialBot.to L }

variable (K L) in
/-- The inclusion of `L` into the join `K ⋆ L`, as the part over the vertex `1`. -/
def inr : L ⟶ join K L :=
  homEquiv.symm
    { p := const (stdSimplex.const 1 1 _)
      left := (Subcomplex.eqToIso (joinFiber_const_of_ne (by decide))).hom ≫
        Subcomplex.isInitialBot.to K
      right := (joinFiber _ 1).ι }

variable (K L) in
@[reassoc (attr := simp)]
lemma inl_π : inl K L ≫ π K L = const (stdSimplex.const 1 0 _) := by
  rw [← homEquiv_p, inl, Equiv.apply_symm_apply]

variable (K L) in
@[reassoc (attr := simp)]
lemma inr_π : inr K L ≫ π K L = const (stdSimplex.const 1 1 _) := by
  rw [← homEquiv_p, inr, Equiv.apply_symm_apply]

/-- On the part of `K` over the vertex `0`, the inclusion of `K` is inverse to the map to `K` of
the tautological join data. -/
lemma univ_left_app_inl_app {n : SimplexCategoryᵒᵖ} (x : K.obj n)
    (hx : (inl K L).app n x ∈ (joinFiber (univ K L).p 0).obj n) :
    (univ K L).left.app n ⟨(inl K L).app n x, hx⟩ = x :=
  JoinData.congr_left_app (homEquiv.apply_symm_apply _) x hx (by simp)

/-- On the part of `L` over the vertex `1`, the inclusion of `L` is inverse to the map to `L` of
the tautological join data. -/
lemma univ_right_app_inr_app {n : SimplexCategoryᵒᵖ} (x : L.obj n)
    (hx : (inr K L).app n x ∈ (joinFiber (univ K L).p 1).obj n) :
    (univ K L).right.app n ⟨(inr K L).app n x, hx⟩ = x :=
  JoinData.congr_right_app (homEquiv.apply_symm_apply _) x hx (by simp)

/-- The join data of the inclusion of `K` into `K ⋆ L` restrict to the identity of `K` over the
vertex `0`. -/
lemma homEquiv_inl_left_app {n : SimplexCategoryᵒᵖ} (x : K.obj n)
    (hx : x ∈ (joinFiber (homEquiv (inl K L)).p 0).obj n) :
    (homEquiv (inl K L)).left.app n ⟨x, hx⟩ = x :=
  (JoinData.congr_left_app (homEquiv_apply _) x hx
    (by rwa [homEquiv_apply] at hx)).trans (univ_left_app_inl_app x _)

/-- The join data of the inclusion of `L` into `K ⋆ L` restrict to the identity of `L` over the
vertex `1`. -/
lemma homEquiv_inr_right_app {n : SimplexCategoryᵒᵖ} (x : L.obj n)
    (hx : x ∈ (joinFiber (homEquiv (inr K L)).p 1).obj n) :
    (homEquiv (inr K L)).right.app n ⟨x, hx⟩ = x :=
  (JoinData.congr_right_app (homEquiv_apply _) x hx
    (by rwa [homEquiv_apply] at hx)).trans (univ_right_app_inr_app x _)

variable (K L) in
/-- Every simplex of the join over the vertex `0` is the inclusion of its image in `K` under the map
to `K` of the tautological join data. -/
@[simp]
lemma univ_left_comp_inl : (univ K L).left ≫ inl K L = (joinFiber (univ K L).p 0).ι := by
  apply homEquiv.injective
  rw [homEquiv_comp, inl, Equiv.apply_symm_apply, homEquiv_apply]
  refine JoinData.ext (by simpa using (joinFiber_ι_comp (univ K L).p 0).symm)
    (fun _ _ _ _ ↦ rfl) (fun _ _ hx _ ↦ ?_)
  simp at hx

variable (K L) in
/-- Every simplex of the join over the vertex `1` is the inclusion of its image in `L` under the map
to `L` of the tautological join data. -/
@[simp]
lemma univ_right_comp_inr : (univ K L).right ≫ inr K L = (joinFiber (univ K L).p 1).ι := by
  apply homEquiv.injective
  rw [homEquiv_comp, inr, Equiv.apply_symm_apply, homEquiv_apply]
  refine JoinData.ext (by simpa using (joinFiber_ι_comp (univ K L).p 1).symm)
    (fun _ _ hx _ ↦ ?_) (fun _ _ _ _ ↦ rfl)
  simp at hx

/-- On the part of the join over the vertex `0`, the map to `K` of the tautological join data is
inverse to the inclusion of `K`. -/
lemma inl_app_univ_left_app {n : SimplexCategoryᵒᵖ} (x : (join K L).obj n)
    (hx : x ∈ (joinFiber (univ K L).p 0).obj n) :
    (inl K L).app n ((univ K L).left.app n ⟨x, hx⟩) = x :=
  -- Elaborated without the expected type, which is only definitionally equal.
  (ConcreteCategory.congr_hom (NatTrans.congr_app (univ_left_comp_inl K L) n) ⟨x, hx⟩ :)

/-- On the part of the join over the vertex `1`, the map to `L` of the tautological join data is
inverse to the inclusion of `L`. -/
lemma inr_app_univ_right_app {n : SimplexCategoryᵒᵖ} (x : (join K L).obj n)
    (hx : x ∈ (joinFiber (univ K L).p 1).obj n) :
    (inr K L).app n ((univ K L).right.app n ⟨x, hx⟩) = x :=
  -- Elaborated without the expected type, which is only definitionally equal.
  (ConcreteCategory.congr_hom (NatTrans.congr_app (univ_right_comp_inr K L) n) ⟨x, hx⟩ :)

variable (K L) in
/-- The inclusion of `K` lands in the part of the join over the vertex `0`. -/
lemma range_inl_le_joinFiber : Subcomplex.range (inl K L) ≤ joinFiber (univ K L).p 0 := by
  rw [← Subcomplex.preimage_eq_top_iff, univ_p, joinFiber, ← Subcomplex.preimage_comp, inl_π,
    ← joinFiber, joinFiber_const_self]

variable (K L) in
/-- The inclusion of `L` lands in the part of the join over the vertex `1`. -/
lemma range_inr_le_joinFiber : Subcomplex.range (inr K L) ≤ joinFiber (univ K L).p 1 := by
  rw [← Subcomplex.preimage_eq_top_iff, univ_p, joinFiber, ← Subcomplex.preimage_comp, inr_π,
    ← joinFiber, joinFiber_const_self]

variable (K L) in
/-- The part of the join `K ⋆ L` over the vertex `0` is `K`, through the map to `K` of the
tautological join data and the inclusion of `K`. -/
def joinFiberZeroIso : (joinFiber (univ K L).p 0 : SSet) ≅ K where
  hom := (univ K L).left
  inv := Subcomplex.lift (inl K L) (range_inl_le_joinFiber K L)
  hom_inv_id := by
    rw [← cancel_mono (Subcomplex.ι _), Category.assoc, Subcomplex.lift_ι, Category.id_comp]
    exact univ_left_comp_inl K L
  inv_hom_id := by
    ext n x
    exact univ_left_app_inl_app x _

variable (K L) in
/-- The part of the join `K ⋆ L` over the vertex `1` is `L`, through the map to `L` of the
tautological join data and the inclusion of `L`. -/
def joinFiberOneIso : (joinFiber (univ K L).p 1 : SSet) ≅ L where
  hom := (univ K L).right
  inv := Subcomplex.lift (inr K L) (range_inr_le_joinFiber K L)
  hom_inv_id := by
    rw [← cancel_mono (Subcomplex.ι _), Category.assoc, Subcomplex.lift_ι, Category.id_comp]
    exact univ_right_comp_inr K L
  inv_hom_id := by
    ext n x
    exact univ_right_app_inr_app x _

variable (K L) in
/-- The isomorphism `joinFiberZeroIso` is the map to `K` of the tautological join data. -/
@[simp]
lemma joinFiberZeroIso_hom : (joinFiberZeroIso K L).hom = (univ K L).left := by
  rfl

variable (K L) in
/-- The isomorphism `joinFiberOneIso` is the map to `L` of the tautological join data. -/
@[simp]
lemma joinFiberOneIso_hom : (joinFiberOneIso K L).hom = (univ K L).right := by
  rfl

variable (K L) in
/-- The inverse of `joinFiberZeroIso` is the inclusion of `K`. -/
@[reassoc (attr := simp)]
lemma joinFiberZeroIso_inv_ι :
    (joinFiberZeroIso K L).inv ≫ (joinFiber (univ K L).p 0).ι = inl K L :=
  Subcomplex.lift_ι _ (range_inl_le_joinFiber K L)

variable (K L) in
/-- The inverse of `joinFiberOneIso` is the inclusion of `L`. -/
@[reassoc (attr := simp)]
lemma joinFiberOneIso_inv_ι :
    (joinFiberOneIso K L).inv ≫ (joinFiber (univ K L).p 1).ι = inr K L :=
  Subcomplex.lift_ι _ (range_inr_le_joinFiber K L)

@[reassoc (attr := simp)]
lemma inl_map (f : K ⟶ K') (g : L ⟶ L') : inl K L ≫ map f g = f ≫ inl K' L' := by
  apply homEquiv.injective
  rw [homEquiv_comp_map, homEquiv_comp, inl, inl, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  refine JoinData.ext (by simp) (fun _ _ _ _ ↦ rfl) (fun n x hx _ ↦ ?_)
  simp at hx

@[reassoc (attr := simp)]
lemma inr_map (f : K ⟶ K') (g : L ⟶ L') : inr K L ≫ map f g = g ≫ inr K' L' := by
  apply homEquiv.injective
  rw [homEquiv_comp_map, homEquiv_comp, inr, inr, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  refine JoinData.ext (by simp) (fun n x hx _ ↦ ?_) (fun _ _ _ _ ↦ rfl)
  simp at hx

/-- The join of two terminal simplicial sets, such as `Δ[0] ⋆ Δ[0]`, is `Δ[1]`, through the
projection `π K L`. -/
def isoOfIsTerminal (hK : Limits.IsTerminal K) (hL : Limits.IsTerminal L) : join K L ≅ Δ[1] where
  hom := π K L
  inv := homEquiv.symm ⟨𝟙 _, hK.from _, hL.from _⟩
  hom_inv_id := homEquiv.injective (by
    rw [homEquiv_comp, Equiv.apply_symm_apply, homEquiv_id]
    -- Simplices of a terminal simplicial set are unique, being maps from standard simplices.
    exact JoinData.ext (by simp) (fun _ _ _ _ ↦ yonedaEquiv.symm.injective (hK.hom_ext _ _))
      (fun _ _ _ _ ↦ yonedaEquiv.symm.injective (hL.hom_ext _ _)))
  inv_hom_id := by rw [← homEquiv_p, Equiv.apply_symm_apply]

@[simp]
lemma isoOfIsTerminal_hom (hK : Limits.IsTerminal K) (hL : Limits.IsTerminal L) :
    (isoOfIsTerminal hK hL).hom = π K L :=
  (rfl)

/-- The edge of the join `K ⋆ L` from a vertex `x` of `K` to a vertex `y` of `L`: the join data on
`Δ[1]` splitting its vertices as `{0}` and `{1}`, with the constant maps at `x` and `y`. -/
def edgeMk (x : K _⦋0⦌) (y : L _⦋0⦌) : (join K L).Edge ((inl K L).app _ x) ((inr K L).app _ y) :=
  Edge.mk (objEquiv.symm ⟨𝟙 Δ[1], const x, const y⟩)
    (objEquiv.injective (by
      rw [SimplicialObject.δ, objEquiv_map, inl, homEquiv_symm_app]
      refine JoinData.ext ?_ (fun _ _ _ _ ↦ ?_) (fun _ _ _ hz ↦ by simp at hz)
      · -- Both maps `Δ[0] ⟶ Δ[1]` pick the vertex `0`.
        apply yonedaEquiv.injective
        refine stdSimplex.ext _ _ fun j ↦ ?_
        fin_cases j
        rfl
      · -- Both sides are images of `x` under maps to `⦋0⦌`, which are unique.
        exact congrArg (fun f ↦ K.map f x) (Subsingleton.elim _ _)))
    (objEquiv.injective (by
      rw [SimplicialObject.δ, objEquiv_map, inr, homEquiv_symm_app]
      refine JoinData.ext ?_ (fun _ _ _ hz ↦ by simp at hz) (fun _ _ _ _ ↦ ?_)
      · -- Both maps `Δ[0] ⟶ Δ[1]` pick the vertex `1`.
        apply yonedaEquiv.injective
        refine stdSimplex.ext _ _ fun j ↦ ?_
        fin_cases j
        rfl
      · -- Both sides are images of `y` under maps to `⦋0⦌`, which are unique.
        exact congrArg (fun f ↦ L.map f y) (Subsingleton.elim _ _)))

/-- The join data of the edge `edgeMk x y` on `Δ[1]`. -/
@[simp]
lemma objEquiv_edgeMk_edge (x : K _⦋0⦌) (y : L _⦋0⦌) :
    objEquiv (edgeMk x y).edge = ⟨𝟙 Δ[1], const x, const y⟩ :=
  (rfl)

/-- An edge of the join `K ⋆ L` whose target lies over the vertex `0` lies over `0`, since the
projection to `Δ[1]` is monotone along the edge. -/
lemma edge_mem_joinFiber_zero {v w : (join K L) _⦋0⦌} (e : (join K L).Edge v w)
    (hw : w ∈ (joinFiber (univ K L).p 0).obj _) :
    e.edge ∈ (joinFiber (univ K L).p 0).obj _ := by
  rw [univ_p, mem_joinFiber_iff] at hw ⊢
  have h1 : (π K L).app (op ⦋1⦌) e.edge 1 = 0 := by
    -- The target of the edge is its face opposite to the vertex `0`.
    refine Eq.trans ?_ ((congrArg (fun t ↦ (π K L).app (op ⦋0⦌) t 0) e.tgt_eq).trans (hw 0))
    have hnat := ConcreteCategory.congr_hom
      (SimplicialObject.δ_naturality (π K L) (0 : Fin 2)) e.edge
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
    rw [hnat, stdSimplex.δ_apply]
    rfl
  exact fun j ↦ le_antisymm (h1 ▸ stdSimplex.monotone_apply _ (Fin.le_last j)) (Fin.zero_le _)

/-- The map from a standard simplex given by the join data of a simplex `s` of the join is the map
`yonedaEquiv.symm s` corresponding to `s`. -/
@[simp]
lemma homEquiv_symm_objEquiv {n : SimplexCategory} (s : (join K L).obj (op n)) :
    homEquiv.symm (objEquiv s) = yonedaEquiv.symm s :=
  (Equiv.symm_apply_eq _).2
    ((univ_precomp_yonedaEquiv_symm s).symm.trans (homEquiv_apply _).symm)

/-- A simplex `t` of `K ⋆ L` none of whose vertices lies over `0` comes from `L`. -/
lemma exists_eq_comp_inr {m : ℕ} (t : Δ[m] ⟶ join K L) (h : yonedaEquiv (homEquiv t).p 0 ≠ 0) :
    ∃ l : Δ[m] ⟶ L, t = l ≫ inr K L := by
  have hs : yonedaEquiv t ∈ (joinFiber (univ K L).p 1).obj _ := by
    rw [mem_joinFiber_iff]
    intro j
    rw [univ_p, ← yonedaEquiv_comp, ← homEquiv_p]
    exact yonedaEquiv_apply_eq_one_of_ne_zero h j
  refine ⟨yonedaEquiv.symm ((univ K L).right.app _ ⟨_, hs⟩), ?_⟩
  rw [yonedaEquiv_symm_comp, inr_app_univ_right_app, Equiv.symm_apply_apply]

/-- A simplex of `K ⋆ L` with join data `e` whose vertex `0` lies over `0` is the image, under
`g ⋆ L`, of the simplex of `Δ[m] ⋆ L` with the same splitting and the same part in `L`, where
`g : Δ[m] ⟶ K` extends the part of `e` in `K` along the retraction `joinFiberZeroRetraction`. -/
lemma homEquiv_symm_eq_comp_map {m : ℕ} (e : JoinData Δ[m] K L) (h : yonedaEquiv e.p 0 = 0) :
    homEquiv.symm e = homEquiv.symm ⟨e.p, (joinFiber e.p 0).ι, e.right⟩ ≫
      map (joinFiberZeroRetraction e.p h ≫ e.left) (𝟙 L) := by
  apply homEquiv.injective
  rw [homEquiv_comp_map, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  refine JoinData.ext (by simp) (fun n x hx hx' ↦ ?_) (fun n x hx hx' ↦ ?_)
  · induction n using Opposite.rec with | op n
    induction n using SimplexCategory.rec with | _ n
    rw [JoinData.postcomp_left_app]
    simp [joinFiberZeroRetraction_app_of_mem _ _ x hx]
  · simp

/-- Every simplex of `K ⋆ L` either comes from `L`, or is the image of a simplex of `Δ[m] ⋆ L`
under `g ⋆ L` for a simplex `g : Δ[m] ⟶ K`. -/
lemma exists_eq_comp_inr_or_exists_eq_comp_map {m : ℕ} (s : Δ[m] ⟶ join K L) :
    (∃ l : Δ[m] ⟶ L, s = l ≫ inr K L) ∨
      ∃ (t : Δ[m] ⟶ join Δ[m] L) (g : Δ[m] ⟶ K), s = t ≫ map g (𝟙 L) := by
  by_cases h : yonedaEquiv (homEquiv s).p 0 = 0
  · refine Or.inr ⟨homEquiv.symm ⟨_, (joinFiber _ 0).ι, (homEquiv s).right⟩,
      joinFiberZeroRetraction _ h ≫ (homEquiv s).left, ?_⟩
    rw [← homEquiv_symm_eq_comp_map _ h, Equiv.symm_apply_apply]
  · exact Or.inl (exists_eq_comp_inr s h)

/-- The join data of the image of a simplex `s` under `f ⋆ g` is the composition of the join data
of `s` with `f` and `g`. -/
@[simp]
lemma objEquiv_map_app (f : K ⟶ K') (g : L ⟶ L') {n : SimplexCategory}
    (s : (join K L).obj (op n)) :
    objEquiv ((map f g).app _ s) = (objEquiv s).postcomp f g := by
  rw [map, homEquiv_symm_app, Equiv.apply_symm_apply, JoinData.precomp_postcomp,
    univ_precomp_yonedaEquiv_symm]

/-- A simplex of `K ⋆ L` lies in the image of `A ⋆ L` for a subcomplex `A` of `K` exactly when its
part in `K` lies in `A`. -/
lemma mem_range_map_ι_id_iff (A : K.Subcomplex) {n : SimplexCategory} (s : (join K L).obj (op n)) :
    s ∈ (Subcomplex.range (map A.ι (𝟙 L))).obj _ ↔
      ∀ (k : SimplexCategoryᵒᵖ) (x : (stdSimplex.obj n).obj k)
        (hx : x ∈ (joinFiber (objEquiv s).p 0).obj k),
          (objEquiv s).left.app k ⟨x, hx⟩ ∈ A.obj k := by
  refine ⟨?_, fun h ↦ ⟨objEquiv.symm ⟨(objEquiv s).p, Subcomplex.lift (objEquiv s).left ?_,
    (objEquiv s).right⟩, objEquiv.injective ?_⟩⟩
  · rintro ⟨t, rfl⟩ k x hx
    have hx' : x ∈ (joinFiber ((objEquiv t).postcomp A.ι (𝟙 L)).p 0).obj k := by
      rwa [← objEquiv_map_app]
    rw [JoinData.congr_left_app (objEquiv_map_app A.ι (𝟙 L) t) x hx hx',
      JoinData.postcomp_left_app]
    exact Subtype.property _
  · rintro k _ ⟨y, rfl⟩
    exact h k y.1 y.2
  · rw [objEquiv_map_app, Equiv.apply_symm_apply]
    -- `Subcomplex.lift (objEquiv s).left _ ≫ A.ι` is `(objEquiv s).left` by definition, since
    -- `Subcomplex.lift` only restricts the codomain.
    exact JoinData.ext rfl (fun _ _ _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl)

/-- A simplex of `K ⋆ L` lies in the image of `K ⋆ B` for a subcomplex `B` of `L` exactly when its
part in `L` lies in `B`. -/
lemma mem_range_map_id_ι_iff (B : L.Subcomplex) {n : SimplexCategory} (s : (join K L).obj (op n)) :
    s ∈ (Subcomplex.range (map (𝟙 K) B.ι)).obj _ ↔
      ∀ (k : SimplexCategoryᵒᵖ) (x : (stdSimplex.obj n).obj k)
        (hx : x ∈ (joinFiber (objEquiv s).p 1).obj k),
          (objEquiv s).right.app k ⟨x, hx⟩ ∈ B.obj k := by
  refine ⟨?_, fun h ↦ ⟨objEquiv.symm ⟨(objEquiv s).p, (objEquiv s).left,
    Subcomplex.lift (objEquiv s).right ?_⟩, objEquiv.injective ?_⟩⟩
  · rintro ⟨t, rfl⟩ k x hx
    have hx' : x ∈ (joinFiber ((objEquiv t).postcomp (𝟙 K) B.ι).p 1).obj k := by
      rwa [← objEquiv_map_app]
    rw [JoinData.congr_right_app (objEquiv_map_app (𝟙 K) B.ι t) x hx hx',
      JoinData.postcomp_right_app]
    exact Subtype.property _
  · rintro k _ ⟨y, rfl⟩
    exact h k y.1 y.2
  · rw [objEquiv_map_app, Equiv.apply_symm_apply]
    -- `Subcomplex.lift (objEquiv s).right _ ≫ B.ι` is `(objEquiv s).right` by definition, since
    -- `Subcomplex.lift` only restricts the codomain.
    exact JoinData.ext rfl (fun _ _ _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl)

end join

namespace Subcomplex

variable (A : K.Subcomplex) (B : L.Subcomplex)

/-- For subcomplexes `A` of `K` and `B` of `L`, the subcomplex `(A ⋆ L) ∪ (K ⋆ B)` of `K ⋆ L`: the
domain of the pushout-join of the inclusions of `A` and `B`. -/
def unionJoin : (join K L).Subcomplex :=
  range (join.map A.ι (𝟙 L)) ⊔ range (join.map (𝟙 K) B.ι)

/-- `(A ⋆ L) ∪ (K ⋆ B)` is the union of the images of `A ⋆ L` and `K ⋆ B` in `K ⋆ L`. -/
lemma unionJoin_def :
    A.unionJoin B = range (join.map A.ι (𝟙 L)) ⊔ range (join.map (𝟙 K) B.ι) := (rfl)

/-- The image of `A ⋆ L` in `K ⋆ L` is contained in `(A ⋆ L) ∪ (K ⋆ B)`. -/
lemma range_join_map_ι_id_le_unionJoin : range (join.map A.ι (𝟙 L)) ≤ A.unionJoin B :=
  le_sup_left

/-- The image of `K ⋆ B` in `K ⋆ L` is contained in `(A ⋆ L) ∪ (K ⋆ B)`. -/
lemma range_join_map_id_ι_le_unionJoin : range (join.map (𝟙 K) B.ι) ≤ A.unionJoin B :=
  le_sup_right

/-- `(A ⋆ L) ∪ (K ⋆ B)` is contained in a subcomplex `Z` of `K ⋆ L` exactly when the images of
`A ⋆ L` and `K ⋆ B` are. -/
lemma unionJoin_le_iff {Z : (join K L).Subcomplex} :
    A.unionJoin B ≤ Z ↔ range (join.map A.ι (𝟙 L)) ≤ Z ∧ range (join.map (𝟙 K) B.ι) ≤ Z :=
  sup_le_iff

/-- A simplex of `K ⋆ L` lies in `(A ⋆ L) ∪ (K ⋆ B)` exactly when its part in `K` lies in `A` or its
part in `L` lies in `B`. -/
lemma mem_unionJoin_iff {n : SimplexCategory} (s : (join K L).obj (op n)) :
    s ∈ (A.unionJoin B).obj _ ↔
      (∀ (k : SimplexCategoryᵒᵖ) (x : (stdSimplex.obj n).obj k)
        (hx : x ∈ (joinFiber (join.objEquiv s).p 0).obj k),
          (join.objEquiv s).left.app k ⟨x, hx⟩ ∈ A.obj k) ∨
      ∀ (k : SimplexCategoryᵒᵖ) (x : (stdSimplex.obj n).obj k)
        (hx : x ∈ (joinFiber (join.objEquiv s).p 1).obj k),
          (join.objEquiv s).right.app k ⟨x, hx⟩ ∈ B.obj k := by
  rw [unionJoin, Subfunctor.max_obj, Set.mem_union, join.mem_range_map_ι_id_iff,
    join.mem_range_map_id_ι_iff]

/-- The images of `A ⋆ L` and `K ⋆ B` in `K ⋆ L` meet in the image of `A ⋆ B`. -/
lemma range_join_map_ι_ι :
    range (join.map A.ι B.ι) = range (join.map A.ι (𝟙 L)) ⊓ range (join.map (𝟙 K) B.ι) := by
  refine le_antisymm (le_inf ?_ ?_) ?_
  · have h : join.map A.ι B.ι = join.map (𝟙 _) B.ι ≫ join.map A.ι (𝟙 L) := by
      simp [← join.map_comp]
    rw [h]
    exact Subfunctor.range_comp_le _ _
  · have h : join.map A.ι B.ι = join.map A.ι (𝟙 _) ≫ join.map (𝟙 K) B.ι := by
      simp [← join.map_comp]
    rw [h]
    exact Subfunctor.range_comp_le _ _
  rintro ⟨n⟩ s ⟨hA, hB⟩
  induction n using SimplexCategory.rec with | _ n
  rw [join.mem_range_map_ι_id_iff] at hA
  rw [join.mem_range_map_id_ι_iff] at hB
  refine ⟨join.objEquiv.symm ⟨(join.objEquiv s).p, lift (join.objEquiv s).left ?_,
    lift (join.objEquiv s).right ?_⟩, join.objEquiv.injective ?_⟩
  · rintro k _ ⟨y, rfl⟩
    exact hA k y.1 y.2
  · rintro k _ ⟨y, rfl⟩
    exact hB k y.1 y.2
  · rw [join.objEquiv_map_app, Equiv.apply_symm_apply]
    -- `lift _ _ ≫ ι` is the original map by definition, since `lift` only restricts the codomain.
    exact JoinData.ext rfl (fun _ _ _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl)

namespace unionJoin

/-- The inclusion `A ⋆ L ⟶ (A ⋆ L) ∪ (K ⋆ B)`. -/
noncomputable def ι₁ : join A L ⟶ A.unionJoin B :=
  lift (join.map A.ι (𝟙 L)) (range_join_map_ι_id_le_unionJoin A B)

/-- The inclusion `K ⋆ B ⟶ (A ⋆ L) ∪ (K ⋆ B)`. -/
noncomputable def ι₂ : join K B ⟶ A.unionJoin B :=
  lift (join.map (𝟙 K) B.ι) (range_join_map_id_ι_le_unionJoin A B)

@[reassoc (attr := simp)]
lemma ι₁_ι : ι₁ A B ≫ (A.unionJoin B).ι = join.map A.ι (𝟙 L) := lift_ι _ _

@[reassoc (attr := simp)]
lemma ι₂_ι : ι₂ A B ≫ (A.unionJoin B).ι = join.map (𝟙 K) B.ι := lift_ι _ _

/-- In the lattice of subcomplexes of `K ⋆ L`, the square formed by the images of `A ⋆ B`,
`A ⋆ L`, `K ⋆ B` and their union `(A ⋆ L) ∪ (K ⋆ B)` is bicartesian. -/
lemma bicartSq : BicartSq (range (join.map A.ι B.ι)) (range (join.map A.ι (𝟙 L)))
    (range (join.map (𝟙 K) B.ι)) (A.unionJoin B) where
  sup_eq := rfl
  inf_eq := (range_join_map_ι_ι A B).symm

/-- **`(A ⋆ L) ∪ (K ⋆ B)` is the pushout of `A ⋆ L` and `K ⋆ B` along `A ⋆ B`.** Hence maps out
of the domain of the pushout-join of the inclusions of `A` and `B` are glued from compatible maps
out of `A ⋆ L` and `K ⋆ B`. -/
lemma isPushout : IsPushout (join.map (𝟙 (A : SSet)) B.ι) (join.map A.ι (𝟙 (B : SSet)))
    (ι₁ A B) (ι₂ A B) := by
  refine (bicartSq A B).isPushout.of_iso' (asIso (toRange _)) (asIso (toRange _))
    (asIso (toRange _)) (Iso.refl _) ?_ ?_ ?_ ?_
  all_goals
    rw [← cancel_mono (Subcomplex.ι _)]
    simp [← join.map_comp]

end unionJoin

end Subcomplex

namespace JoinData

variable {n : ℕ} {i : Fin (n + 3)} (h₀ : 0 < i) (hₙ : i < Fin.last (n + 2))
  {q : Δ[n + 2] ⟶ Δ[1]}

/-- If every vertex of `Δ[n + 2]` lies over the vertex `e` of `Δ[1]`, nothing lies over a
different vertex `e'`. -/
private lemma joinFiber_eq_bot_of_forall_eq {e e' : Fin 2} (h : e ≠ e')
    (hq : ∀ v, yonedaEquiv q v = e) : joinFiber q e' = ⊥ := by
  ext k x
  induction k using Opposite.rec with | op k
  induction k using SimplexCategory.rec with | _ k
  simp only [mem_joinFiber_iff, stdSimplex.hom_app_apply, hq, Subfunctor.bot_obj,
    Set.mem_empty_iff_false, iff_false, not_forall]
  exact ⟨0, h⟩

include h₀ hₙ in
/-- If every vertex of `Δ[n + 2]` lies over the vertex `e` of `Δ[1]`, a map to a quasicategory `T`
from the part of the inner horn over `e` extends to the part of `Δ[n + 2]` over `e`. -/
private lemma exists_fromPreimage_horn_ι_comp_eq {T : SSet.{u}} [Quasicategory T] {e : Fin 2}
    (hq : ∀ v, yonedaEquiv q v = e) (φ : (joinFiber (Λ[n + 2, i].ι ≫ q) e : SSet) ⟶ T) :
    ∃ τ : (joinFiber q e : SSet) ⟶ T, (joinFiber q e).fromPreimage Λ[n + 2, i].ι ≫ τ = φ := by
  have htop : joinFiber (Λ[n + 2, i].ι ≫ q) e = ⊤ := by
    ext k x
    induction k using Opposite.rec with | op k
    induction k using SimplexCategory.rec with | _ k
    simp only [Subfunctor.top_obj, Set.mem_univ, iff_true, mem_joinFiber_iff]
    exact fun j ↦ (stdSimplex.hom_app_apply q x.1 j).trans (hq _)
  obtain ⟨τ, hτ⟩ := Quasicategory.hornFilling'
    ((Subcomplex.topIso _).inv ≫ Subcomplex.homOfLE htop.ge ≫ φ) h₀ hₙ
  refine ⟨(joinFiber q e).ι ≫ τ, ?_⟩
  ext k x
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app hτ k) x.1).symm

include h₀ hₙ in
/-- Join data on an inner horn lying entirely over the vertex `0` of `Δ[1]` is the restriction of
join data on the simplex when `K` is a quasicategory. -/
private lemma exists_precomp_horn_ι_eq_of_forall_eq_zero [Quasicategory K]
    (hq : ∀ v, yonedaEquiv q v = 0) (l : (joinFiber (Λ[n + 2, i].ι ≫ q) 0 : SSet) ⟶ K)
    (r : (joinFiber (Λ[n + 2, i].ι ≫ q) 1 : SSet) ⟶ L) :
    ∃ D : JoinData Δ[n + 2] K L, D.precomp Λ[n + 2, i].ι = ⟨Λ[n + 2, i].ι ≫ q, l, r⟩ := by
  obtain ⟨τ, hτ⟩ := exists_fromPreimage_horn_ι_comp_eq h₀ hₙ hq l
  have hbot := joinFiber_eq_bot_of_forall_eq (e' := 1) (by decide) hq
  refine ⟨⟨q, τ, (Subcomplex.eqToIso hbot).hom ≫ Subcomplex.isInitialBot.to L⟩,
    ext rfl (fun k x _ _ ↦ ?_) (fun k x _ hx ↦ ?_)⟩
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app hτ k) ⟨x, _⟩
  · rw [joinFiber, Subcomplex.preimage_comp, ← joinFiber, hbot] at hx
    simp at hx

include h₀ hₙ in
/-- Join data on an inner horn lying entirely over the vertex `1` of `Δ[1]` is the restriction of
join data on the simplex when `L` is a quasicategory. -/
private lemma exists_precomp_horn_ι_eq_of_forall_eq_one [Quasicategory L]
    (hq : ∀ v, yonedaEquiv q v = 1) (l : (joinFiber (Λ[n + 2, i].ι ≫ q) 0 : SSet) ⟶ K)
    (r : (joinFiber (Λ[n + 2, i].ι ≫ q) 1 : SSet) ⟶ L) :
    ∃ D : JoinData Δ[n + 2] K L, D.precomp Λ[n + 2, i].ι = ⟨Λ[n + 2, i].ι ≫ q, l, r⟩ := by
  obtain ⟨τ, hτ⟩ := exists_fromPreimage_horn_ι_comp_eq h₀ hₙ hq r
  have hbot := joinFiber_eq_bot_of_forall_eq (e' := 0) (by decide) hq
  refine ⟨⟨q, (Subcomplex.eqToIso hbot).hom ≫ Subcomplex.isInitialBot.to K, τ⟩,
    ext rfl (fun k x _ hx ↦ ?_) (fun k x _ _ ↦ ?_)⟩
  · rw [joinFiber, Subcomplex.preimage_comp, ← joinFiber, hbot] at hx
    simp at hx
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app hτ k) ⟨x, _⟩

include h₀ hₙ in
/-- If the first vertex of `Δ[n + 2]` lies over `0` and the last over `1`, the parts of
`Δ[n + 2]` over both vertices of `Δ[1]` are contained in the inner horn, so join data on the horn
is the restriction of join data on the simplex. -/
private lemma exists_precomp_horn_ι_eq_of_eq_zero_of_eq_one (h0 : yonedaEquiv q 0 = 0)
    (hlast : yonedaEquiv q (Fin.last _) = 1) (l : (joinFiber (Λ[n + 2, i].ι ≫ q) 0 : SSet) ⟶ K)
    (r : (joinFiber (Λ[n + 2, i].ι ≫ q) 1 : SSet) ⟶ L) :
    ∃ D : JoinData Δ[n + 2] K L, D.precomp Λ[n + 2, i].ι = ⟨Λ[n + 2, i].ι ≫ q, l, r⟩ := by
  -- A simplex over `e` misses every vertex not over `e`, so lies in the horn if such a vertex
  -- is not `i`.
  have hle (e : Fin 2) (v : Fin (n + 3)) (hv : v ≠ i) (hqv : yonedaEquiv q v ≠ e) :
      joinFiber q e ≤ Λ[n + 2, i] := by
    intro k x hx
    induction k using Opposite.rec with | op k
    induction k using SimplexCategory.rec with | _ k
    rw [mem_horn_iff_notMem_range]
    refine ⟨v, hv, ?_⟩
    rintro ⟨j, rfl⟩
    exact hqv ((stdSimplex.hom_app_apply q x j).symm.trans ((mem_joinFiber_iff q e x).1 hx j))
  have hle₀ := hle 0 (Fin.last _) hₙ.ne' (by simp [hlast])
  have hle₁ := hle 1 0 h₀.ne (by simp [h0])
  refine ⟨⟨q, Subcomplex.lift (Subcomplex.homOfLE hle₀) ?_ ≫ l,
    Subcomplex.lift (Subcomplex.homOfLE hle₁) ?_ ≫ r⟩,
    ext rfl (fun _ _ _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl)⟩
  all_goals rintro k _ ⟨⟨x, hx⟩, rfl⟩; exact hx

include h₀ hₙ in
/-- **Inner horn extension for join data**: if `K` and `L` are quasicategories, join data on an
inner horn `Λ[n + 2, i]` is the restriction of join data on `Δ[n + 2]`. -/
lemma exists_precomp_horn_ι_eq [Quasicategory K] [Quasicategory L]
    (d : JoinData Λ[n + 2, i] K L) :
    ∃ D : JoinData Δ[n + 2] K L, D.precomp Λ[n + 2, i].ι = d := by
  obtain ⟨p, l, r⟩ := d
  -- Extend the map to `Δ[1]`, then distinguish according to the endpoints of its vertex map.
  obtain ⟨q, rfl⟩ := Quasicategory.hornFilling' p h₀ hₙ
  have hmono := stdSimplex.monotone_apply (yonedaEquiv q)
  by_cases hlast : yonedaEquiv q (Fin.last _) = 0
  · exact exists_precomp_horn_ι_eq_of_forall_eq_zero h₀ hₙ
      (fun v ↦ le_antisymm (hlast ▸ hmono (Fin.le_last v)) (Fin.zero_le _)) l r
  by_cases h0 : yonedaEquiv q 0 = 1
  · exact exists_precomp_horn_ι_eq_of_forall_eq_one h₀ hₙ
      (fun v ↦ le_antisymm (Fin.le_last _) (h0 ▸ hmono (Fin.zero_le v))) l r
  have h01 : ∀ a : Fin 2, a ≠ 1 → a = 0 := by decide
  have h10 : ∀ a : Fin 2, a ≠ 0 → a = 1 := by decide
  exact exists_precomp_horn_ι_eq_of_eq_zero_of_eq_one h₀ hₙ (h01 _ h0) (h10 _ hlast) l r

end JoinData

/-- **Joyal**: the join of two quasicategories is a quasicategory. -/
instance join.quasicategory [Quasicategory K] [Quasicategory L] : Quasicategory (join K L) where
  hornFilling' _ _ σ₀ h₀ hₙ := by
    obtain ⟨D, hD⟩ := JoinData.exists_precomp_horn_ι_eq h₀ hₙ (join.homEquiv σ₀)
    refine ⟨join.homEquiv.symm D, join.homEquiv.injective ?_⟩
    rw [join.homEquiv_comp, Equiv.apply_symm_apply, hD]

end SSet

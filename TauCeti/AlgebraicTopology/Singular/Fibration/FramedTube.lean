/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup
public import TauCeti.AlgebraicTopology.Singular.Fibration.FundamentalClass
public import TauCeti.AlgebraicTopology.Singular.Fibration.LocalHomology
public import TauCeti.Geometry.Manifold.PontryaginThom.NormalCoordinate
import TauCeti.AlgebraicTopology.Singular.Fibration.FiberInclusion
import TauCeti.Topology.Homeomorph.SetCongr

/-!
# Local homology of a Serre fibration along the preimage of a framed submanifold

A closed subset `Z ⊆ B` with a **normal coordinate** `ν : W → K` (a Serre fibration on an open
neighbourhood `W` of `Z`, onto a convex neighbourhood `K` of `0` in a real normed space `V` of
finite dimension `r`, whose zero set is `Z`) gives every Serre fibration `p : E → B` the shriek map
`Hₙ₊ᵣ(E) → Hₙ₊ᵣ(E, E ∖ p⁻¹(Z)) ≅ Hₙ(p⁻¹(Z))` of the inclusion of `Z`
(`TauCeti.TopCat.singularHomologyComplPreimageIso`). For a point and a chart it is the shriek map
of `TauCeti.TopCat.singularHomologyComplFiberIso`. This file applies it to framed submanifolds.

A framed tube `τ : S × V → B` around `f : S → B` (`TauCeti.IsFramedTube`) gives the core
`Z = f(S)` the normal coordinate `τ(x, v) ↦ v` on the part `τ(S × D)` of the tube over a ball `D`
about `0` (`TauCeti.IsFramedTube.tubeBall`, `TauCeti.IsFramedTube.normalCoordinate`), so
`Hₙ₊ᵣ(E, E ∖ p⁻¹(f(S))) ≅ Hₙ(p⁻¹(f(S)))` (`TauCeti.TopCat.singularHomologyComplPreimageCoreIso`).
It is natural for a map `s : B' → B` carrying a second framed tube `τ'` to `τ` fibrewise,
`s (τ' (x, v)) = τ (φ x, v)`, and pulling the core of `τ` back into the core of `τ'`
(`TauCeti.TopCat.singularHomologyComplPreimageCoreIso_hom_naturality_of_apply_eq`): for instance
the Thom collapse onto the Thom space of the trivial bundle.
For the identity of `B` this is the Thom isomorphism `Hₙ₊ᵣ(B, B ∖ f(S)) ≅ Hₙ(S)` of the framed
submanifold (`TauCeti.TopCat.singularHomologyComplRangeIso`), the trivial-bundle case of the
identification of a shriek map with the Thom isomorphism of a tube.

Let `s : B' → B` meet the core in a single point `b'`, `s⁻¹(f(S)) = {b'}`, and suppose that near
`b'` the normal coordinate of `s` is a chart `e` of `B'`: `s` maps the ball of radius `ε` about
`b'` in the chart into the tube, with `s x = τ(y, e x - e b')` for some `y`. For a smooth map `s`
transverse to the core this is the inverse function theorem in the normal coordinate. Then for a
map `g : E' → E` of Serre fibrations over `s`, the shriek maps commute:

`j_{f(S)!} ∘ g_* = (g|)_* ∘ j_{b'!}`,

where `j_{b'!} : Hₙ₊ᵣ(E') → Hₙ(p'⁻¹(b'))` is the shriek map of the point `b'` for the chart `e` and
`g| : p'⁻¹(b') → p⁻¹(f(S))` is the restriction of `g`
(`TauCeti.TopCat.singularHomologyComplPreimageCoreIso_hom_naturality`). This is the commutative
square in the proof of Lemma 7.7 of Barraud, Damian, Humilière and Oancea, which they deduce from
the fibration theorem and the relation `j_{Y!} s_* = j^{(Y)}_* j_!` for the transverse square of `s`
and the inclusion of `Y = f(S)`. In particular, when `g|` is injective on `Hₙ` a class of infinite
order of the fibre `p'⁻¹(b')` stays of infinite order along the core
(`TauCeti.TopCat.not_isOfFinAddOrder_singularHomologyComplPreimageCoreIso`). The injectivity holds
in degrees `n < N` when the core is `N`-connected at `s b'` and `g` is injective on the homology of
the fibres, since the fibre `p⁻¹(s b')` then carries the homology of `p⁻¹(f(S))` in low degrees
(`not_isOfFinAddOrder_singularHomologyComplPreimageCoreIso_of_subsingleton_homotopyGroup`).
In Barraud–Damian–Humilière–Oancea, `p` is the evaluation fibration `Map(S², Q) → Q` and `s` is an
embedded sphere meeting a highly connected framed submanifold of `Q` once.

If `p` is moreover trivial over the part of the tube over a ball, with `S` and the fibre `T₁`
spaces, the shriek map of the core sends fundamental classes of `E` to fundamental classes of
`p⁻¹(f(S))`
(`TauCeti.IsFundamentalClass.singularHomologyComplPreimageCoreIso_hom_singularHomologyπ`). For `p`
the identity of a closed manifold `B`, trivial with a one-point fibre, and a framed closed
submanifold `f(S)`, this says that the fundamental class of `B`, localized along `f(S)`, is a
fundamental class of `f(S)`; for a fibre bundle trivial over the tube it is the identity
`j_![E] = [E|_{f(S)}]` of Barraud, Damian, Humilière and Oancea (Remark 2.10), up to the
orientation conventions which `TauCeti.IsFundamentalClass` leaves free.
The trivialization over the tube is read as a product with the ball through
`TauCeti.IsFramedTube.tubeBallTrivialization`.

## Main definitions and results

* `TauCeti.IsFramedTube.coreHom`, `TauCeti.IsFramedTube.coreHomeomorph`: the core `S → f(S)` as a
  morphism of topological spaces and as a homeomorphism.
* `TauCeti.TopCat.singularHomologyComplPreimageCoreIso`: the local homology along the core of a
  framed tube.
* `TauCeti.TopCat.isZero_singularHomology_complRange`,
  `TauCeti.TopCat.singularHomologyComplRangeIso`: the Thom isomorphism of a framed submanifold,
  and the vanishing below the codimension.
* `TauCeti.TopCat.singularHomologyComplPreimageCoreIso_hom_naturality_of_apply_eq`: naturality
  of the shriek map of the core for maps of framed tubes.
* `TauCeti.TopCat.singularHomologyComplPreimageCoreIso_hom_naturality`,
  `TauCeti.TopCat.singularHomologyComplPreimageCoreIso_singularHomologyπ_homologyMap`: the shriek
  map of the core and the shriek map of a transverse point commute.
* `TauCeti.TopCat.not_isOfFinAddOrder_singularHomologyComplPreimageCoreIso`,
  `not_isOfFinAddOrder_singularHomologyComplPreimageCoreIso_of_subsingleton_homotopyGroup`:
  classes of infinite order along the core.
* `TauCeti.IsFramedTube.tubeBallTrivialization`: a trivialization of `p` over the tube, read as a
  product with the ball compatibly with the normal coordinate.
* `TauCeti.IsFundamentalClass.singularHomologyComplPreimageCoreIso_hom_singularHomologyπ`: the
  shriek map of the core sends fundamental classes to fundamental classes.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.4 (Remark 2.10) and §7, Lemma 7.7.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §11 (the Thom isomorphism of a tubular neighbourhood).
-/

public section

noncomputable section

open CategoryTheory Limits Module Metric Set Topology

universe u

namespace TauCeti

/-! ### The core of a framed tube as a morphism -/

namespace IsFramedTube

section Core

variable {S : Type u} {V : Type*} [TopologicalSpace S] [TopologicalSpace V] [Zero V]
  {B : _root_.TopCat.{u}} {f : S → B} {τ : S × V → B} (hτ : IsFramedTube f τ)

/-- The core `f : S → f(S)` of a framed tube, as a morphism to the preimage of `f(S)` under the
identity of `B`, the form in which the local homology along the core is stated. -/
def coreHom : _root_.TopCat.of S ⟶ _root_.TopCat.of ↥((𝟙 B) ⁻¹' range f) :=
  _root_.TopCat.ofHom ⟨fun x ↦ ⟨f x, mem_range_self x⟩, hτ.continuous.subtype_mk _⟩

-- Not `@[simp]`: `simp` rewrites the preimage under the identity in the type of the codomain, so
-- the left-hand side is not in simp normal form.
lemma coe_coreHom_apply (x : S) : (hτ.coreHom x : B) = f x :=
  (rfl)

end Core

section CoreHomeomorph

variable {S V : Type*} [TopologicalSpace S] [TopologicalSpace V] [Zero V] {B : _root_.TopCat.{u}}
  {f : S → B} {τ : S × V → B} (hτ : IsFramedTube f τ)

/-- The core of a framed tube is a homeomorphism of `S` onto the preimage of `f(S)` under the
identity of `B`. -/
def coreHomeomorph : S ≃ₜ ↥((𝟙 B) ⁻¹' range f) :=
  hτ.isEmbedding.toHomeomorph.trans
    (.setCongr (by ext; rw [mem_preimage, ConcreteCategory.id_apply]))

-- Not `@[simp]`, for the same reason as `TauCeti.IsFramedTube.coe_coreHom_apply`.
lemma coe_coreHomeomorph_apply (x : S) : (hτ.coreHomeomorph x : B) = f x := by
  rw [coreHomeomorph, Homeomorph.trans_apply, Homeomorph.setCongr_apply,
    IsEmbedding.toHomeomorph_apply_coe]

end CoreHomeomorph

/-- The homeomorphism of `S` with the core is the core `TauCeti.IsFramedTube.coreHom`. -/
lemma isoOfHomeo_coreHomeomorph_hom {S : Type u} {V : Type*} [TopologicalSpace S]
    [TopologicalSpace V] [Zero V] {B : _root_.TopCat.{u}} {f : S → B} {τ : S × V → B}
    (hτ : IsFramedTube f τ) :
    (_root_.TopCat.isoOfHomeo hτ.coreHomeomorph).hom = hτ.coreHom := by
  -- `ext` also applies `Subtype.ext`, so the goal is about the points of `B`.
  ext x
  rw [coe_coreHom_apply]
  -- The morphism `(TopCat.isoOfHomeo h).hom` applies `h` itself.
  exact hτ.coe_coreHomeomorph_apply x

/-- A map of the bases carrying the tube `τ'` to the tube `τ` fibrewise carries the core of `τ'`
into the core of `τ`. -/
lemma mapsTo_range_of_apply_eq {B B' S S' V : Type*} [TopologicalSpace B] [TopologicalSpace B']
    [TopologicalSpace S] [TopologicalSpace S'] [TopologicalSpace V] [Zero V] {f : S → B}
    {τ : S × V → B} {f' : S' → B'} {τ' : S' × V → B'} (hτ : IsFramedTube f τ)
    (hτ' : IsFramedTube f' τ') {s : B' → B} {φ : S' → S}
    (hs : ∀ x v, s (τ' (x, v)) = τ (φ x, v)) : MapsTo s (range f') (range f) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨φ x, by rw [← hτ.apply_zero, ← hs, hτ'.apply_zero]⟩

/-- If near `b'` the normal coordinate of `s` is a chart at `b'`, then `s b'` lies on the core. -/
lemma apply_mem_range_of_chartBall {V B B' S : Type*} [SeminormedAddCommGroup V]
    [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace S] {f : S → B} {τ : S × V → B}
    (hτ : IsFramedTube f τ) {s : B' → B} (e : OpenPartialHomeomorph B' V) {b' : B'}
    (hb : b' ∈ e.source) {ε : ℝ} (hs : ∀ x ∈ e.chartBall b' ε, ∃ y, τ (y, e x - e b') = s x)
    (hε₀ : 0 < ε) : s b' ∈ range f := by
  obtain ⟨y, hy⟩ := hs b' (e.mem_chartBall_self hb hε₀)
  exact ⟨y, by rw [← hτ.apply_zero, ← hy, sub_self]⟩

end IsFramedTube

namespace TopCat

/-! ### The local homology along the core of a framed tube -/

section Core

variable {V : Type u} [NormedAddCommGroup V] {B : _root_.TopCat.{u}} {S : Type*}
  [TopologicalSpace S] {f : S → B} {τ : S × V → B}

/-- The normal coordinate of a framed tube is a Serre fibration. -/
lemma mem_serreFibrations_normalCoordinate (hτ : IsFramedTube f τ) (ε : ℝ) :
    serreFibrations (_root_.TopCat.ofHom (hτ.normalCoordinate ε) :
      _root_.TopCat.of (IsFramedTube.tubeBall τ ε) ⟶ _root_.TopCat.of (ball (0 : V) ε)) :=
  mem_serreFibrations_of_hasHomotopyLiftingProperty fun A _ ↦
    hτ.hasHomotopyLiftingProperty_normalCoordinate ε A

variable [NormedSpace ℝ V] {E : _root_.TopCat.{u}} {p : E ⟶ B} {R : Type*} [Ring R]

/-- **The local homology of a Serre fibration along the core of a framed tube vanishes below the
codimension.** Let `τ : S × V → B` be a framed tube around `f : S → B` with closed core `f(S)`,
where `V` is a real normed space of dimension `r`, and let `p : E ⟶ B` be a Serre fibration.
Then `Hₘ(E, E ∖ p⁻¹(f(S)); M) = 0` for every `m < r`. -/
theorem isZero_singularHomology_complPreimage_range (hτ : IsFramedTube f τ) (M : ModuleCat.{u} R)
    (hfc : IsClosed (range f)) (hp : serreFibrations p) {m : ℕ} (hm : m < finrank ℝ V) :
    IsZero ((TopPair.ofSubset (p ⁻¹' range f)ᶜ).singularHomology M m) :=
  haveI : FiniteDimensional ℝ V := Module.finite_of_finrank_pos ((Nat.zero_le m).trans_lt hm)
  isZero_singularHomology_complPreimage (ν := _root_.TopCat.ofHom (hτ.normalCoordinate 1))
    hτ.normalCoordinate_eq_zero_iff M (hτ.isOpen_tubeBall 1) hfc (hτ.range_subset_tubeBall one_pos)
    hp (mem_serreFibrations_normalCoordinate hτ 1) (convex_ball 0 1) (ball_mem_nhds 0 one_pos) hm

/-- **The local homology of a Serre fibration along the core of a framed tube.** Let
`τ : S × V → B` be a framed tube around `f : S → B` with closed core `f(S)`, where `V` is a real
normed space of finite dimension `r`, and let `p : E ⟶ B` be a Serre fibration. Then
`Hₘ(E, E ∖ p⁻¹(f(S)); M) ≅ Hₙ(p⁻¹(f(S)); M)` for `m = n + r`.

This is `TauCeti.TopCat.singularHomologyComplPreimageIso` for the normal coordinate
`τ(x, v) ↦ v` on the part of the tube over the ball of radius `ε` about `0`
(`TauCeti.IsFramedTube.normalCoordinate`). Composed with the map
`Hₘ(E) → Hₘ(E, E ∖ p⁻¹(f(S)))`, it is the shriek map `Hₘ(E) → Hₙ(p⁻¹(f(S)))` of the inclusion of
the framed submanifold `f(S)`, with coefficients in the fibration. -/
def singularHomologyComplPreimageCoreIso [FiniteDimensional ℝ V] (hτ : IsFramedTube f τ)
    (M : ModuleCat.{u} R) (hfc : IsClosed (range f)) {ε : ℝ} (hε₀ : 0 < ε) (hp : serreFibrations p)
    (n m : ℕ) (h : n + finrank ℝ V = m) :
    (TopPair.ofSubset (p ⁻¹' range f)ᶜ).singularHomology M m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        M).obj (_root_.TopCat.of (p ⁻¹' range f)) :=
  singularHomologyComplPreimageIso (ν := _root_.TopCat.ofHom (hτ.normalCoordinate ε))
    hτ.normalCoordinate_eq_zero_iff M (hτ.isOpen_tubeBall ε) hfc (hτ.range_subset_tubeBall hε₀)
    hp (mem_serreFibrations_normalCoordinate hτ ε) (convex_ball 0 ε) (ball_mem_nhds 0 hε₀) n m h

end Core

/-! ### Maps of framed tubes -/

section TubeMap

variable {V : Type u} [NormedAddCommGroup V] {E B E' B' : _root_.TopCat.{u}} {p : E ⟶ B}
  {p' : E' ⟶ B'} {S S' : Type*} {τ : S × V → B} {τ' : S' × V → B'} {s : B' ⟶ B} {g : E' ⟶ E}
  {φ : S' → S}

private lemma mapsTo_tubeBall_tubeBall (hg : g ≫ p = p' ≫ s)
    (hs : ∀ x v, s (τ' (x, v)) = τ (φ x, v)) {ε : ℝ} :
    MapsTo g (p' ⁻¹' IsFramedTube.tubeBall τ' ε) (p ⁻¹' IsFramedTube.tubeBall τ ε) :=
  g.mapsTo_preimage_of_comp_eq_comp hg fun x hx ↦ by
    obtain ⟨y, v, hv, rfl⟩ := IsFramedTube.mem_tubeBall.1 hx
    rw [hs]
    exact IsFramedTube.apply_mem_tubeBall (φ y) hv

variable [TopologicalSpace S] [TopologicalSpace S'] {f : S → B} {f' : S' → B'}

private lemma normalCoordinate_apply_comp_of_apply_eq (hτ : IsFramedTube f τ)
    (hτ' : IsFramedTube f' τ') (hg : g ≫ p = p' ≫ s) (hs : ∀ x v, s (τ' (x, v)) = τ (φ x, v))
    {ε : ℝ} (x : E') (hx : p' x ∈ IsFramedTube.tubeBall τ' ε) :
    hτ.normalCoordinate ε ⟨p (g x), mapsTo_tubeBall_tubeBall hg hs hx⟩ =
      hτ'.normalCoordinate ε ⟨p' x, hx⟩ := by
  obtain ⟨y, hy⟩ := hτ'.exists_apply_normalCoordinate ⟨p' x, hx⟩
  apply Subtype.ext
  refine hτ.normalCoordinate_eq_of_eq (x := φ y) ((ConcreteCategory.congr_hom hg x).trans ?_)
  rw [← hs, hy]
  rfl

/-- **Naturality of the shriek map of the core for maps of framed tubes.** Let `τ : S × V → B` and
`τ' : S' × V → B'` be framed tubes around `f` and `f'`, with closed cores, and let `s : B' → B`
carry `τ'` to `τ` fibrewise, `s (τ' (x, v)) = τ (φ x, v)`, and pull the core of `τ` back into the
core of `τ'`. For a map `g : E' ⟶ E` of Serre fibrations over `s`, the shriek map
`Hₙ₊ᵣ(E, E ∖ p⁻¹(f(S))) ≅ Hₙ(p⁻¹(f(S)))` of the core
(`TauCeti.TopCat.singularHomologyComplPreimageCoreIso`) composed with the map induced by `g` is
the shriek map of the core of `τ'` composed with the map induced by the restriction
`p'⁻¹(f'(S')) → p⁻¹(f(S))` of `g`. -/
@[reassoc]
theorem singularHomologyComplPreimageCoreIso_hom_naturality_of_apply_eq [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (hτ : IsFramedTube f τ) (hτ' : IsFramedTube f' τ')
    (hg : g ≫ p = p' ≫ s) (hs : ∀ x v, s (τ' (x, v)) = τ (φ x, v))
    (hsf : ∀ x, s x ∈ range f → x ∈ range f') {R : Type*} [Ring R] (M : ModuleCat.{u} R)
    (hfc : IsClosed (range f)) (hfc' : IsClosed (range f')) {ε : ℝ} (hε₀ : 0 < ε)
    (hp : serreFibrations p) (hp' : serreFibrations p') (n m : ℕ) (h : n + finrank ℝ V = m) :
    TopPair.singularHomologyMap
        (TopPair.ofSubsetMap g
          (g.mapsTo_preimage_of_comp_eq_comp (T := (range f')ᶜ) (U := (range f)ᶜ) hg
            fun x hx hxf ↦ hx (hsf x hxf))) M m ≫
        (singularHomologyComplPreimageCoreIso hτ M hfc hε₀ hp n m h).hom =
      (singularHomologyComplPreimageCoreIso hτ' M hfc' hε₀ hp' n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (g.preimageMapOver hg (hτ.mapsTo_range_of_apply_eq hτ' hs)) := by
  refine (singularHomologyComplPreimageIso_hom_naturality hτ.normalCoordinate_eq_zero_iff
    hτ'.normalCoordinate_eq_zero_iff (hτ'.range_subset_tubeBall hε₀)
    (mapsTo_tubeBall_tubeBall hg hs) (normalCoordinate_apply_comp_of_apply_eq hτ hτ' hg hs)
    (g.mapsTo_preimage_of_comp_eq_comp (T := (range f')ᶜ) (U := (range f)ᶜ) hg
      fun x hx hxf ↦ hx (hsf x hxf)) M (hτ.isOpen_tubeBall ε) hfc (hτ.range_subset_tubeBall hε₀)
    (hτ'.isOpen_tubeBall ε) hfc' hp hp' (mem_serreFibrations_normalCoordinate hτ ε)
    (mem_serreFibrations_normalCoordinate hτ' ε) (convex_ball 0 ε) (ball_mem_nhds 0 hε₀)
    n m h).trans ?_
  -- Both restrictions of `g` send a point `x` of `p'⁻¹(f'(S'))` to `g x`.
  congr 2
  ext x
  exact (g.coe_preimageMapOver_apply hg _ x).symm

end TubeMap

/-! ### The Thom isomorphism of a framed submanifold -/

section Thom

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : _root_.TopCat.{u}}
  {R : Type*} [Ring R]

/-- **The local homology of a space along a framed submanifold vanishes below the codimension.**
Let `τ : S × V → B` be a framed tube around `f : S → B` with closed core `f(S)`, where `V` is a
real normed space of dimension `r`. Then `Hₘ(B, B ∖ f(S); M) = 0` for every `m < r`. -/
theorem isZero_singularHomology_complRange {S : Type*} [TopologicalSpace S] {f : S → B}
    {τ : S × V → B} (hτ : IsFramedTube f τ) (M : ModuleCat.{u} R) (hfc : IsClosed (range f))
    {m : ℕ} (hm : m < finrank ℝ V) :
    IsZero ((TopPair.ofSubset (range f)ᶜ).singularHomology M m) :=
  isZero_singularHomology_complPreimage_range hτ M hfc (serreFibrations.id_mem B) hm

variable [FiniteDimensional ℝ V] {S : Type u} [TopologicalSpace S] {f : S → B} {τ : S × V → B}

/-- **The Thom isomorphism of a framed submanifold.** Let `τ : S × V → B` be a framed tube around
`f : S → B` with closed core `f(S)`, where `V` is a real normed space of finite dimension `r`.
Then `Hₘ(B, B ∖ f(S); M) ≅ Hₙ(S; M)` for `m = n + r`. This is
`TauCeti.TopCat.singularHomologyComplPreimageCoreIso` for the identity of `B`, followed by the
inverse of the homeomorphism `S ≃ₜ f(S)` of the core
(`TauCeti.TopCat.singularHomologyComplRangeIso_hom_comp_map_coreHom`). -/
def singularHomologyComplRangeIso (hτ : IsFramedTube f τ) (M : ModuleCat.{u} R)
    (hfc : IsClosed (range f)) {ε : ℝ} (hε₀ : 0 < ε) (n m : ℕ) (h : n + finrank ℝ V = m) :
    (TopPair.ofSubset (range f)ᶜ).singularHomology M m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj
        (_root_.TopCat.of S) :=
  singularHomologyComplPreimageCoreIso hτ M hfc hε₀ (serreFibrations.id_mem B) n m h ≪≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).mapIso
      (_root_.TopCat.isoOfHomeo hτ.coreHomeomorph).symm

/-- The forward morphism of `TauCeti.TopCat.singularHomologyComplRangeIso` is the local homology
along the core for the identity of `B`, followed by the inverse of the homeomorphism `S ≃ₜ f(S)`. -/
@[reassoc]
lemma singularHomologyComplRangeIso_hom (hτ : IsFramedTube f τ) (M : ModuleCat.{u} R)
    (hfc : IsClosed (range f)) {ε : ℝ} (hε₀ : 0 < ε) (n m : ℕ) (h : n + finrank ℝ V = m) :
    (singularHomologyComplRangeIso hτ M hfc hε₀ n m h).hom =
      (singularHomologyComplPreimageCoreIso hτ M hfc hε₀ (serreFibrations.id_mem B) n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (_root_.TopCat.isoOfHomeo hτ.coreHomeomorph).inv :=
  (rfl)

/-- The Thom isomorphism of a framed submanifold, followed by the map induced by the core
`S → f(S)`, is the local homology along the core for the identity of `B`. -/
@[reassoc]
lemma singularHomologyComplRangeIso_hom_comp_map_coreHom (hτ : IsFramedTube f τ)
    (M : ModuleCat.{u} R) (hfc : IsClosed (range f)) {ε : ℝ} (hε₀ : 0 < ε) (n m : ℕ)
    (h : n + finrank ℝ V = m) :
    (singularHomologyComplRangeIso hτ M hfc hε₀ n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map hτ.coreHom =
      (singularHomologyComplPreimageCoreIso hτ M hfc hε₀ (serreFibrations.id_mem B) n m h).hom := by
  -- The source of the Thom isomorphism is that of the local homology along the core only up to
  -- unfolding the preimage under the identity, which `rw` does not see through, so the
  -- composite is reassociated as a term.
  refine (Category.assoc _ _ _).trans ?_
  rw [Functor.mapIso_hom, Iso.symm_hom, ← Functor.map_comp, ← hτ.isoOfHomeo_coreHomeomorph_hom,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

end Thom

/-! ### Maps meeting the core of a framed tube once -/

section Transverse

variable {V : Type u} [NormedAddCommGroup V] {E B E' B' : _root_.TopCat.{u}} {p : E ⟶ B}
  {p' : E' ⟶ B'} {S : Type*} {τ : S × V → B} {s : B' ⟶ B} {g : E' ⟶ E} {b' : B'} {ε : ℝ}

private lemma mapsTo_chartBall_tubeBall (hg : g ≫ p = p' ≫ s) (e : OpenPartialHomeomorph B' V)
    (hs : ∀ x ∈ e.chartBall b' ε, ∃ y, τ (y, e x - e b') = s x) :
    MapsTo g (p' ⁻¹' e.chartBall b' ε) (p ⁻¹' IsFramedTube.tubeBall τ ε) :=
  g.mapsTo_preimage_of_comp_eq_comp hg fun x hx ↦ by
    obtain ⟨y, hy⟩ := hs x hx
    rw [← hy]
    exact IsFramedTube.apply_mem_tubeBall y
      (by simpa [mem_ball, dist_eq_norm] using ((e.mem_chartBall).1 hx).2)

variable [TopologicalSpace S] {f : S → B}

private lemma normalCoordinate_apply_comp (hτ : IsFramedTube f τ) (hg : g ≫ p = p' ≫ s)
    (e : OpenPartialHomeomorph B' V) (hε : ball (e b') ε ⊆ e.target)
    (hs : ∀ x ∈ e.chartBall b' ε, ∃ y, τ (y, e x - e b') = s x) (x : E')
    (hx : p' x ∈ e.chartBall b' ε) :
    _root_.TopCat.ofHom (hτ.normalCoordinate ε) ⟨p (g x), mapsTo_chartBall_tubeBall hg e hs hx⟩ =
      (_root_.TopCat.isoOfHomeo (X := _root_.TopCat.of (e.chartBall b' ε))
        (Y := _root_.TopCat.of (ball (0 : V) ε)) (e.chartBallHomeomorph hε)).hom ⟨p' x, hx⟩ := by
  obtain ⟨y, hy⟩ := hs _ hx
  apply Subtype.ext
  exact (hτ.normalCoordinate_eq_of_eq (x := y)
    ((ConcreteCategory.congr_hom hg x).trans hy.symm)).trans
    (e.coe_chartBallHomeomorph_apply hε ⟨p' x, hx⟩).symm

variable [NormedSpace ℝ V] [FiniteDimensional ℝ V] [T1Space B']

/-- **The shriek maps of a framed submanifold and of a transverse point commute**
(Barraud–Damian–Humilière–Oancea, proof of Lemma 7.7). Let `τ : S × V → B` be a framed tube around
`f : S → B` with closed core, let `s : B' → B` meet the core only at `b'`, and let `e` be a chart
of `B'` at `b'` such that every point `x` of its ball `e.chartBall b' ε` is mapped to
`τ (y, e x - e b')` for some `y`: near `b'`, the normal coordinate of `s` is the chart. Let
`g : E' ⟶ E` be a map of Serre fibrations over `s`. Then the shriek map
`Hₙ₊ᵣ(E, E ∖ p⁻¹(f(S))) ≅ Hₙ(p⁻¹(f(S)))` of the core
(`TauCeti.TopCat.singularHomologyComplPreimageCoreIso`) composed with the map induced by `g` is the
shriek map `Hₙ₊ᵣ(E', E' ∖ p'⁻¹(b')) ≅ Hₙ(p'⁻¹(b'))` of the point
(`TauCeti.TopCat.singularHomologyComplFiberIso`) composed with the map induced by the restriction
`p'⁻¹(b') → p⁻¹(f(S))` of `g`. -/
@[reassoc]
theorem singularHomologyComplPreimageCoreIso_hom_naturality (hτ : IsFramedTube f τ)
    (hg : g ≫ p = p' ≫ s) (e : OpenPartialHomeomorph B' V) (hb : b' ∈ e.source)
    (hε : ball (e b') ε ⊆ e.target) (hs : ∀ x ∈ e.chartBall b' ε, ∃ y, τ (y, e x - e b') = s x)
    (hsf : ∀ x, s x ∈ range f → x = b') {R : Type*} [Ring R] (M : ModuleCat.{u} R)
    (hfc : IsClosed (range f)) (hε₀ : 0 < ε) (hp : serreFibrations p) (hp' : serreFibrations p')
    (n m : ℕ) (h : n + finrank ℝ V = m) :
    TopPair.singularHomologyMap
        (TopPair.ofSubsetMap g
          (g.mapsTo_preimage_of_comp_eq_comp (T := {b'}ᶜ) (U := (range f)ᶜ) hg
            fun x hx hxf ↦ hx (hsf x hxf))) M m ≫
        (singularHomologyComplPreimageCoreIso hτ M hfc hε₀ hp n m h).hom =
      (singularHomologyComplFiberIso M e hb hε hε₀ hp' n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (g.preimageMapOver hg
            (mapsTo_singleton.2 (hτ.apply_mem_range_of_chartBall e hb hs hε₀))) := by
  rw [singularHomologyComplFiberIso_def]
  refine (singularHomologyComplPreimageIso_hom_naturality hτ.normalCoordinate_eq_zero_iff
    (e.isoOfHomeo_chartBallHomeomorph_hom_eq_zero_iff hε hb)
    (singleton_subset_iff.2 (e.mem_chartBall_self hb hε₀)) (mapsTo_chartBall_tubeBall hg e hs)
    (normalCoordinate_apply_comp hτ hg e hε hs)
    (g.mapsTo_preimage_of_comp_eq_comp (T := {b'}ᶜ) (U := (range f)ᶜ) hg
      fun x hx hxf ↦ hx (hsf x hxf)) M (hτ.isOpen_tubeBall ε) hfc (hτ.range_subset_tubeBall hε₀)
    (e.isOpen_chartBall b' ε) isClosed_singleton hp hp'
    (mem_serreFibrations_normalCoordinate hτ ε) (serreFibrations.of_isIso _) (convex_ball 0 ε)
    (ball_mem_nhds 0 hε₀) n m h).trans ?_
  -- Both restrictions of `g` send a point `x` of `p'⁻¹(b')` to `g x`.
  congr 2
  ext x
  exact (g.coe_preimageMapOver_apply hg _ x).symm

/-- **The shriek maps of a framed submanifold and of a transverse point commute, on classes**
(Barraud–Damian–Humilière–Oancea, proof of Lemma 7.7). In the setting of
`TauCeti.TopCat.singularHomologyComplPreimageCoreIso_hom_naturality`, for `α ∈ Hₙ₊ᵣ(E')` the shriek
map of the core sends `g_* α` to the image under the restriction `p'⁻¹(b') → p⁻¹(f(S))` of `g`
of the shriek map `j_! α ∈ Hₙ(p'⁻¹(b'))` of the point: `j_{f(S)!} (g_* α) = (g|)_* (j_! α)`. -/
theorem singularHomologyComplPreimageCoreIso_singularHomologyπ_homologyMap (hτ : IsFramedTube f τ)
    (hg : g ≫ p = p' ≫ s) (e : OpenPartialHomeomorph B' V) (hb : b' ∈ e.source)
    (hε : ball (e b') ε ⊆ e.target) (hs : ∀ x ∈ e.chartBall b' ε, ∃ y, τ (y, e x - e b') = s x)
    (hsf : ∀ x, s x ∈ range f → x = b') {R : Type*} [Ring R] (M : ModuleCat.{u} R)
    (hfc : IsClosed (range f)) (hε₀ : 0 < ε) (hp : serreFibrations p) (hp' : serreFibrations p')
    (n m : ℕ) (h : n + finrank ℝ V = m)
    (α : ((_root_.TopCat.toSSet.obj E').homology M m : ModuleCat.{u} R)) :
    (singularHomologyComplPreimageCoreIso hτ M hfc hε₀ hp n m h).hom.hom
        (((TopPair.ofSubset (p ⁻¹' range f)ᶜ).singularHomologyπ M m).hom
          ((SSet.homologyMap (_root_.TopCat.toSSet.map g) M m).hom α)) =
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (g.preimageMapOver hg
            (mapsTo_singleton.2 (hτ.apply_mem_range_of_chartBall e hb hs hε₀)))).hom
        ((singularHomologyComplFiberIso M e hb hε hε₀ hp' n m h).hom.hom
          ((fiberLocalization M p' b' m).hom α)) := by
  have hπ : SSet.homologyMap (_root_.TopCat.toSSet.map g) M m ≫
        (TopPair.ofSubset (p ⁻¹' range f)ᶜ).singularHomologyπ M m =
      fiberLocalization M p' b' m ≫
        TopPair.singularHomologyMap
          (TopPair.ofSubsetMap g
            (g.mapsTo_preimage_of_comp_eq_comp (T := {b'}ᶜ) (U := (range f)ᶜ) hg
              fun x hx hxf ↦ hx (hsf x hxf))) M m := by
    have hnat := TopPair.singularHomologyπ_naturality
      (TopPair.ofSubsetMap g
        (g.mapsTo_preimage_of_comp_eq_comp (T := {b'}ᶜ) (U := (range f)ᶜ) hg
          fun x hx hxf ↦ hx (hsf x hxf))) M m
    rw [TopPair.ofSubsetMap_fst] at hnat
    exact hnat
  have hcomp : (SSet.homologyMap (_root_.TopCat.toSSet.map g) M m ≫
        (TopPair.ofSubset (p ⁻¹' range f)ᶜ).singularHomologyπ M m) ≫
        (singularHomologyComplPreimageCoreIso hτ M hfc hε₀ hp n m h).hom =
      fiberLocalization M p' b' m ≫
        (singularHomologyComplFiberIso M e hb hε hε₀ hp' n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (g.preimageMapOver hg
            (mapsTo_singleton.2 (hτ.apply_mem_range_of_chartBall e hb hs hε₀))) := by
    rw [hπ, Category.assoc,
      singularHomologyComplPreimageCoreIso_hom_naturality hτ hg e hb hε hs hsf]
  have hval := congrArg (fun φ ↦ φ.hom α) hcomp
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hval
  exact (congrArg _ (ModuleCat.comp_apply
    (SSet.homologyMap (_root_.TopCat.toSSet.map g) M m)
    ((TopPair.ofSubset (p ⁻¹' range f)ᶜ).singularHomologyπ M m) α)).symm.trans hval

/-- **Classes of infinite order along the core of a framed tube** (Barraud–Damian–Humilière–Oancea,
Lemma 7.7). In the setting of `TauCeti.TopCat.singularHomologyComplPreimageCoreIso_hom_naturality`,
suppose the restriction `p'⁻¹(b') → p⁻¹(f(S))` of `g` is injective on `Hₙ`, as it is for the
fibration of maps `S² → Q` over a highly connected core. If the shriek map
`j_! α ∈ Hₙ(p'⁻¹(b'))` of the point has infinite order, then so does the shriek map of the core of
`g_* α`. -/
theorem not_isOfFinAddOrder_singularHomologyComplPreimageCoreIso (hτ : IsFramedTube f τ)
    (hg : g ≫ p = p' ≫ s) (e : OpenPartialHomeomorph B' V) (hb : b' ∈ e.source)
    (hε : ball (e b') ε ⊆ e.target) (hs : ∀ x ∈ e.chartBall b' ε, ∃ y, τ (y, e x - e b') = s x)
    (hsf : ∀ x, s x ∈ range f → x = b') {R : Type*} [Ring R] (M : ModuleCat.{u} R)
    (hfc : IsClosed (range f)) (hε₀ : 0 < ε) (hp : serreFibrations p) (hp' : serreFibrations p')
    (n m : ℕ) (h : n + finrank ℝ V = m)
    (hinj : Function.Injective
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
        (g.preimageMapOver hg
          (mapsTo_singleton.2 (hτ.apply_mem_range_of_chartBall e hb hs hε₀)))).hom)
    {α : ((_root_.TopCat.toSSet.obj E').homology M m : ModuleCat.{u} R)}
    (hα : ¬ IsOfFinAddOrder ((singularHomologyComplFiberIso M e hb hε hε₀ hp' n m h).hom.hom
      ((fiberLocalization M p' b' m).hom α))) :
    ¬ IsOfFinAddOrder ((singularHomologyComplPreimageCoreIso hτ M hfc hε₀ hp n m h).hom.hom
      (((TopPair.ofSubset (p ⁻¹' range f)ᶜ).singularHomologyπ M m).hom
        ((SSet.homologyMap (_root_.TopCat.toSSet.map g) M m).hom α))) := by
  rw [singularHomologyComplPreimageCoreIso_singularHomologyπ_homologyMap hτ hg e hb hε hs hsf M
    hfc hε₀ hp hp' n m h]
  exact (Function.Injective.isOfFinAddOrder_iff (f := LinearMap.toAddMonoidHom _) hinj).not.2 hα

/-- **Classes of infinite order along a highly connected core** (Barraud–Damian–Humilière–Oancea,
Lemma 7.7). In the setting of `TauCeti.TopCat.singularHomologyComplPreimageCoreIso_hom_naturality`,
with coefficients in a ring `R`, suppose that the core `f(S)` has trivial homotopy groups `π_k` at
`s b'` for every `k ≤ N`, and that `g` restricted to the fibres `p'⁻¹(b') → p⁻¹(s b')` is injective
on `Hₙ` for some `n < N`, for instance because `g` is the projection of the pullback of `p` along
`s`. If the shriek map `j_! α ∈ Hₙ(p'⁻¹(b'))` of the point has infinite order, then so does the
shriek map of the core of `g_* α`: the inclusion `p⁻¹(s b') → p⁻¹(f(S))` is injective on `Hₙ`
(`TauCeti.TopCat.isIso_singularHomologyMap_preimageInclusion`). -/
theorem not_isOfFinAddOrder_singularHomologyComplPreimageCoreIso_of_subsingleton_homotopyGroup
    (hτ : IsFramedTube f τ) (hg : g ≫ p = p' ≫ s) (e : OpenPartialHomeomorph B' V)
    (hb : b' ∈ e.source) (hε : ball (e b') ε ⊆ e.target)
    (hs : ∀ x ∈ e.chartBall b' ε, ∃ y, τ (y, e x - e b') = s x)
    (hsf : ∀ x, s x ∈ range f → x = b') (hfc : IsClosed (range f)) {R : Type u} [Ring R]
    (hε₀ : 0 < ε) (hp : serreFibrations p) (hp' : serreFibrations p') {n m N : ℕ}
    (h : n + finrank ℝ V = m) (hn : n < N)
    (hY : ∀ k ≤ N,
      Subsingleton (π_ k (range f) ⟨s b', hτ.apply_mem_range_of_chartBall e hb hs hε₀⟩))
    (hinj : Function.Injective
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).map
          (g.preimageMapOver (T := {b'}) hg (mapsTo_singleton.2 (mem_singleton (s b'))))).hom)
    {α : ((_root_.TopCat.toSSet.obj E').homology (ModuleCat.of R R) m : ModuleCat.{u} R)}
    (hα : ¬ IsOfFinAddOrder
      ((singularHomologyComplFiberIso (ModuleCat.of R R) e hb hε hε₀ hp' n m h).hom.hom
        ((fiberLocalization (ModuleCat.of R R) p' b' m).hom α))) :
    ¬ IsOfFinAddOrder
      ((singularHomologyComplPreimageCoreIso hτ (ModuleCat.of R R) hfc hε₀ hp n m h).hom.hom
        (((TopPair.ofSubset (p ⁻¹' range f)ᶜ).singularHomologyπ (ModuleCat.of R R) m).hom
          ((SSet.homologyMap (_root_.TopCat.toSSet.map g) (ModuleCat.of R R) m).hom α))) := by
  refine not_isOfFinAddOrder_singularHomologyComplPreimageCoreIso hτ hg e hb hε hs hsf
    (ModuleCat.of R R) hfc hε₀ hp hp' n m h ?_ hα
  have := isIso_singularHomologyMap_preimageInclusion R
    (mem_serreFibrations_restrictPreimage hp (range f))
    (hτ.apply_mem_range_of_chartBall e hb hs hε₀) hY hn
  rw [← g.preimageMapOver_comp_preimageInclusion hg (T := {b'})
      (mapsTo_singleton.2 (mem_singleton (s b'))) (hτ.apply_mem_range_of_chartBall e hb hs hε₀),
    Functor.map_comp, ModuleCat.hom_comp, LinearMap.coe_comp]
  exact ((ModuleCat.mono_iff_injective _).1 inferInstance).comp hinj

end Transverse

end TopCat

/-! ### Fundamental classes along the core -/

namespace IsFramedTube

variable {V E B S Y : Type*} [NormedAddCommGroup V] [TopologicalSpace E] [TopologicalSpace B]
  [TopologicalSpace S] [TopologicalSpace Y] {p : E → B} {f : S → B} {τ : S × V → B}
  (hτ : IsFramedTube f τ) {ε : ℝ} (T : Bundle.Trivialization Y p) (hT : tubeBall τ ε ⊆ T.baseSet)

/-- Over the part `τ(S × D)` of a framed tube over the ball `D` of radius `ε` about `0`, a
trivialization of `p` over a base set containing `τ(S × D)` identifies the part of `E` over it with
`D × (S × Y)`: a point goes to the normal coordinate of its image, the coordinate of its image along
the core, and its fibre coordinate. -/
def tubeBallTrivialization : p ⁻¹' tubeBall τ ε ≃ₜ ball (0 : V) ε × (S × Y) :=
  (T.preimageHomeomorph hT).trans <|
    (((hτ.tubeBallHomeomorph ε).symm.trans (.prodComm _ _)).prodCongr (.refl Y)).trans
      (.prodAssoc _ _ _)

/-- The first coordinate of `TauCeti.IsFramedTube.tubeBallTrivialization` is the normal coordinate
of `p z` (`TauCeti.IsFramedTube.normalCoordinate`), which agrees with
`TauCeti.TopCat.normalCoordinateProj` when `p` is a morphism in `TopCat`. -/
@[simp]
lemma tubeBallTrivialization_apply_fst (z : p ⁻¹' tubeBall τ ε) :
    (hτ.tubeBallTrivialization T hT z).1 = hτ.normalCoordinate ε ⟨p z, z.property⟩ := by
  simp [tubeBallTrivialization, T.preimageHomeomorph_apply, Homeomorph.prodAssoc]

/-- The second coordinate of `TauCeti.IsFramedTube.tubeBallTrivialization` is the coordinate along
the core given by the tube, together with the fibre coordinate of `T`. -/
@[simp]
lemma tubeBallTrivialization_apply_snd (z : p ⁻¹' tubeBall τ ε) :
    (hτ.tubeBallTrivialization T hT z).2 =
      (((hτ.tubeBallHomeomorph ε).symm ⟨p z, z.property⟩).1, (T z.val).2) := by
  simp [tubeBallTrivialization, T.preimageHomeomorph_apply, Homeomorph.prodAssoc]

/-- The inverse of `TauCeti.IsFramedTube.tubeBallTrivialization` is the inverse of `T` after reading
the normal coordinate and the coordinate along the core back in `B` through the framed tube. -/
@[simp]
lemma coe_tubeBallTrivialization_symm_apply (x : ball (0 : V) ε × (S × Y)) :
    ((hτ.tubeBallTrivialization T hT).symm x : E) =
      T.toOpenPartialHomeomorph.symm (τ (x.2.1, x.1), x.2.2) := by
  simp [tubeBallTrivialization, Homeomorph.prodAssoc]

end IsFramedTube

/-- **The shriek map of a framed submanifold sends fundamental classes to fundamental classes.**
Let `τ : S × V → B` be a framed tube around `f : S → B` with closed core `f(S)`, where `V` is a
real normed space of finite dimension `r` and `S` is a `T₁` space, and let `p : E ⟶ B` be a Serre
fibration, trivial over the part `τ(S × D)` of the tube over a ball `D` about `0`, with fibre a `T₁`
space. If `μ ∈ Hₙ₊ᵣ(E; R)` is a fundamental class of `E`, then its image under the shriek map
`j_! : Hₙ₊ᵣ(E) → Hₙ₊ᵣ(E, E ∖ p⁻¹(f(S))) ≅ Hₙ(p⁻¹(f(S)))` of the inclusion of the core
(`TauCeti.TopCat.singularHomologyComplPreimageCoreIso`) is a fundamental class of `p⁻¹(f(S))`.
For `p` the identity of a closed manifold `B`, trivial with a one-point fibre, this is the identity
`j_![B] = [f(S)]` for a framed closed submanifold, and for a fibre bundle of closed manifolds
trivial over the tube the identity `j_![E] = [E|_{f(S)}]`, up to the orientation conventions which
`TauCeti.IsFundamentalClass` leaves free. -/
theorem IsFundamentalClass.singularHomologyComplPreimageCoreIso_hom_singularHomologyπ
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {E B : _root_.TopCat.{u}} {p : E ⟶ B} {S : Type u} [TopologicalSpace S] [T1Space S]
    {f : S → B} {τ : S × V → B} (hτ : IsFramedTube f τ) (hfc : IsClosed (range f))
    {R : Type u} [Ring R] {ε : ℝ} (hε₀ : 0 < ε) (hp : TopCat.serreFibrations p) {Y : Type u}
    [TopologicalSpace Y] [T1Space Y] (T : Bundle.Trivialization Y p)
    (hT : IsFramedTube.tubeBall τ ε ⊆ T.baseSet) {n m : ℕ} (h : n + finrank ℝ V = m)
    {μ : ((_root_.TopCat.toSSet.obj E).homology (ModuleCat.of R R) m : ModuleCat.{u} R)}
    (hμ : IsFundamentalClass μ) :
    IsFundamentalClass (M := p ⁻¹' range f)
      ((TopCat.singularHomologyComplPreimageCoreIso hτ (ModuleCat.of R R) hfc hε₀ hp n m h).hom.hom
        (((TopPair.ofSubset (p ⁻¹' range f)ᶜ).singularHomologyπ (ModuleCat.of R R) m).hom μ)) :=
  IsFundamentalClass.singularHomologyComplPreimageIso_hom_singularHomologyπ
    hτ.normalCoordinate_eq_zero_iff (hτ.isOpen_tubeBall ε) hfc (hτ.range_subset_tubeBall hε₀)
    (hτ.tubeBallTrivialization T hT)
    (fun z ↦ (hτ.tubeBallTrivialization_apply_fst T hT z).trans
      (TopCat.normalCoordinateProj_apply ..).symm)
    hp (TopCat.mem_serreFibrations_normalCoordinate hτ ε) (convex_ball 0 ε)
    (ball_mem_nhds 0 hε₀) h hμ

end TauCeti

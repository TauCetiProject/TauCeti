/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.FiberInclusion
public import TauCeti.AlgebraicTopology.Singular.Fibration.LocalHomology
public import TauCeti.Geometry.Manifold.PontryaginThom.NormalCoordinate

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

## Main definitions and results

* `TauCeti.TopCat.singularHomologyComplPreimageCoreIso`: the local homology along the core of a
  framed tube.
* `TauCeti.TopCat.singularHomologyComplPreimageCoreIso_hom_naturality_of_apply_eq`: naturality
  of the shriek map of the core for maps of framed tubes.
* `TauCeti.TopCat.singularHomologyComplPreimageCoreIso_hom_naturality`,
  `TauCeti.TopCat.singularHomologyComplPreimageCoreIso_singularHomologyπ_homologyMap`: the shriek
  map of the core and the shriek map of a transverse point commute.
* `TauCeti.TopCat.not_isOfFinAddOrder_singularHomologyComplPreimageCoreIso`,
  `not_isOfFinAddOrder_singularHomologyComplPreimageCoreIso_of_subsingleton_homotopyGroup`:
  classes of infinite order along the core.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §7, Lemma 7.7.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
-/

public section

noncomputable section

open CategoryTheory Limits Module Metric Set Topology

universe u

namespace TauCeti

namespace TopCat

/-! ### The local homology along the core of a framed tube -/

section Core

variable {V : Type u} [NormedAddCommGroup V] {E B : _root_.TopCat.{u}} {p : E ⟶ B}
  {S : Type*} [TopologicalSpace S] {f : S → B} {τ : S × V → B} (hτ : IsFramedTube f τ)

/-- The normal coordinate of a framed tube is a Serre fibration. -/
lemma mem_serreFibrations_normalCoordinate (ε : ℝ) :
    serreFibrations (_root_.TopCat.ofHom (hτ.normalCoordinate ε) :
      _root_.TopCat.of (IsFramedTube.tubeBall τ ε) ⟶ _root_.TopCat.of (ball (0 : V) ε)) :=
  mem_serreFibrations_of_hasHomotopyLiftingProperty fun A _ ↦
    hτ.hasHomotopyLiftingProperty_normalCoordinate ε A

variable {R : Type*} [Ring R] (M : ModuleCat.{u} R) (hfc : IsClosed (range f))
  [NormedSpace ℝ V] [FiniteDimensional ℝ V]

include hτ hfc in
/-- **The local homology of a Serre fibration along the core of a framed tube vanishes below the
codimension.** Let `τ : S × V → B` be a framed tube around `f : S → B` with closed core `f(S)`,
where `V` is a real normed space of finite dimension `r`, and let `p : E ⟶ B` be a Serre fibration.
Then `Hₘ(E, E ∖ p⁻¹(f(S)); M) = 0` for every `m < r`. -/
theorem isZero_singularHomology_complPreimage_range (hp : serreFibrations p) {m : ℕ}
    (hm : m < finrank ℝ V) :
    IsZero ((TopPair.ofSubset (p ⁻¹' range f)ᶜ).singularHomology M m) :=
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
def singularHomologyComplPreimageCoreIso {ε : ℝ} (hε₀ : 0 < ε) (hp : serreFibrations p)
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
  {p' : E' ⟶ B'} {S S' : Type*} [TopologicalSpace S] [TopologicalSpace S'] {f : S → B}
  {τ : S × V → B} {f' : S' → B'} {τ' : S' × V → B'} (hτ : IsFramedTube f τ)
  (hτ' : IsFramedTube f' τ') {s : B' ⟶ B} {g : E' ⟶ E} (hg : g ≫ p = p' ≫ s) {φ : S' → S}
  (hs : ∀ x v, s (τ' (x, v)) = τ (φ x, v)) (hsf : ∀ x, s x ∈ range f → x ∈ range f')

include hτ hτ' hs in
/-- A map of the bases carrying the tube `τ'` to the tube `τ` fibrewise carries the core of `τ'`
into the core of `τ`. -/
lemma mapsTo_range_of_apply_eq : MapsTo s (range f') (range f) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨φ x, by rw [← hτ.apply_zero, ← hs, hτ'.apply_zero]⟩

omit [TopologicalSpace S] [TopologicalSpace S'] in
include hg hsf in
/-- A map over `s`, where `s` pulls the core of `τ` back into the core of `τ'`, maps the complement
of the preimage of the core of `τ'` into the complement of the preimage of the core of `τ`. -/
lemma mapsTo_compl_preimage_range_compl_preimage_range :
    MapsTo g (p' ⁻¹' range f')ᶜ (p ⁻¹' range f)ᶜ :=
  g.mapsTo_preimage_of_comp_eq_comp (T := (range f')ᶜ) (U := (range f)ᶜ) hg fun x hx hxf ↦
    hx (hsf x hxf)

omit [TopologicalSpace S] [TopologicalSpace S'] in
include hg hs in
private lemma mapsTo_tubeBall_tubeBall {ε : ℝ} :
    MapsTo g (p' ⁻¹' IsFramedTube.tubeBall τ' ε) (p ⁻¹' IsFramedTube.tubeBall τ ε) :=
  g.mapsTo_preimage_of_comp_eq_comp hg fun x hx ↦ by
    obtain ⟨y, v, hv, rfl⟩ := IsFramedTube.mem_tubeBall.1 hx
    rw [hs]
    exact IsFramedTube.apply_mem_tubeBall (φ y) hv

include hg hs in
private lemma normalCoordinate_apply_comp_of_apply_eq {ε : ℝ} (x : E')
    (hx : p' x ∈ IsFramedTube.tubeBall τ' ε) :
    hτ.normalCoordinate ε ⟨p (g x), mapsTo_tubeBall_tubeBall hg hs hx⟩ =
      hτ'.normalCoordinate ε ⟨p' x, hx⟩ := by
  obtain ⟨y, hy⟩ := hτ'.exists_apply_normalCoordinate ⟨p' x, hx⟩
  apply Subtype.ext
  refine hτ.normalCoordinate_eq_of_eq (x := φ y) ((ConcreteCategory.congr_hom hg x).trans ?_)
  rw [← hs, hy]
  rfl

variable {R : Type*} [Ring R] (M : ModuleCat.{u} R) (hfc : IsClosed (range f))
  (hfc' : IsClosed (range f')) [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Naturality of the shriek map of the core for maps of framed tubes.** Let `τ : S × V → B` and
`τ' : S' × V → B'` be framed tubes around `f` and `f'`, with closed cores, and let `s : B' → B`
carry `τ'` to `τ` fibrewise, `s (τ' (x, v)) = τ (φ x, v)`, and pull the core of `τ` back into the
core of `τ'`. For a map `g : E' ⟶ E` of Serre fibrations over `s`, the shriek map
`Hₙ₊ᵣ(E, E ∖ p⁻¹(f(S))) ≅ Hₙ(p⁻¹(f(S)))` of the core
(`TauCeti.TopCat.singularHomologyComplPreimageCoreIso`) composed with the map induced by `g` is
the shriek map of the core of `τ'` composed with the map induced by the restriction
`p'⁻¹(f'(S')) → p⁻¹(f(S))` of `g`. -/
@[reassoc]
theorem singularHomologyComplPreimageCoreIso_hom_naturality_of_apply_eq {ε : ℝ} (hε₀ : 0 < ε)
    (hp : serreFibrations p) (hp' : serreFibrations p') (n m : ℕ) (h : n + finrank ℝ V = m) :
    TopPair.singularHomologyMap
        (TopPair.ofSubsetMap g (mapsTo_compl_preimage_range_compl_preimage_range hg hsf)) M m ≫
        (singularHomologyComplPreimageCoreIso hτ M hfc hε₀ hp n m h).hom =
      (singularHomologyComplPreimageCoreIso hτ' M hfc' hε₀ hp' n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (g.preimageMapOver hg (mapsTo_range_of_apply_eq hτ hτ' hs)) := by
  refine (singularHomologyComplPreimageIso_hom_naturality hτ.normalCoordinate_eq_zero_iff
    hτ'.normalCoordinate_eq_zero_iff (hτ'.range_subset_tubeBall hε₀)
    (mapsTo_tubeBall_tubeBall hg hs) (normalCoordinate_apply_comp_of_apply_eq hτ hτ' hg hs)
    (mapsTo_compl_preimage_range_compl_preimage_range hg hsf) M (hτ.isOpen_tubeBall ε) hfc
    (hτ.range_subset_tubeBall hε₀) (hτ'.isOpen_tubeBall ε) hfc' hp hp'
    (mem_serreFibrations_normalCoordinate hτ ε) (mem_serreFibrations_normalCoordinate hτ' ε)
    (convex_ball 0 ε) (ball_mem_nhds 0 hε₀) n m h).trans ?_
  -- Both restrictions of `g` send a point `x` of `p'⁻¹(f'(S'))` to `g x`.
  congr 2
  ext x
  exact (g.coe_preimageMapOver_apply hg _ x).symm

end TubeMap

/-! ### Maps meeting the core of a framed tube once -/

section Transverse

variable {V : Type u} [NormedAddCommGroup V] {E B E' B' : _root_.TopCat.{u}} {p : E ⟶ B}
  {p' : E' ⟶ B'} {S : Type*} [TopologicalSpace S] {f : S → B} {τ : S × V → B}
  (hτ : IsFramedTube f τ) {s : B' ⟶ B} {g : E' ⟶ E} (hg : g ≫ p = p' ≫ s)
  (e : OpenPartialHomeomorph B' V) {b' : B'} (hb : b' ∈ e.source) {ε : ℝ}
  (hε : ball (e b') ε ⊆ e.target)
  (hs : ∀ x ∈ e.chartBall b' ε, ∃ y, τ (y, e x - e b') = s x)
  (hsf : ∀ x, s x ∈ range f → x = b')

omit [TopologicalSpace S] in
include hg hs in
private lemma mapsTo_chartBall_tubeBall :
    MapsTo g (p' ⁻¹' e.chartBall b' ε) (p ⁻¹' IsFramedTube.tubeBall τ ε) :=
  g.mapsTo_preimage_of_comp_eq_comp hg fun x hx ↦ by
    obtain ⟨y, hy⟩ := hs x hx
    rw [← hy]
    exact IsFramedTube.apply_mem_tubeBall y
      (by simpa [mem_ball, dist_eq_norm] using ((e.mem_chartBall).1 hx).2)

include hg hs in
private lemma normalCoordinate_apply_comp (x : E') (hx : p' x ∈ e.chartBall b' ε) :
    _root_.TopCat.ofHom (hτ.normalCoordinate ε) ⟨p (g x), mapsTo_chartBall_tubeBall hg e hs hx⟩ =
      (_root_.TopCat.isoOfHomeo (X := _root_.TopCat.of (e.chartBall b' ε))
        (Y := _root_.TopCat.of (ball (0 : V) ε)) (e.chartBallHomeomorph hε)).hom ⟨p' x, hx⟩ := by
  obtain ⟨y, hy⟩ := hs _ hx
  apply Subtype.ext
  exact (hτ.normalCoordinate_eq_of_eq (x := y)
    ((ConcreteCategory.congr_hom hg x).trans hy.symm)).trans
    (e.coe_chartBallHomeomorph_apply hε ⟨p' x, hx⟩).symm

omit [TopologicalSpace S] in
include hg hsf in
/-- A map over `s`, where `s` meets the core of the tube only at `b'`, maps the complement of the
fibre over `b'` into the complement of the preimage of the core. -/
lemma mapsTo_compl_preimage_singleton_compl_preimage_range_of_forall_eq :
    MapsTo g (p' ⁻¹' {b'})ᶜ (p ⁻¹' range f)ᶜ :=
  g.mapsTo_preimage_of_comp_eq_comp (T := {b'}ᶜ) (U := (range f)ᶜ) hg fun x hx hxf ↦
    hx (hsf x hxf)

include hτ hb hs in
/-- If near `b'` the normal coordinate of `s` is a chart at `b'`, then `s b'` lies on the core. -/
lemma _root_.TauCeti.IsFramedTube.apply_mem_range_of_chartBall (hε₀ : 0 < ε) :
    s b' ∈ range f := by
  obtain ⟨y, hy⟩ := hs b' (e.mem_chartBall_self hb hε₀)
  exact ⟨y, by rw [← hτ.apply_zero, ← hy, sub_self]⟩

variable [T1Space B'] {R : Type*} [Ring R] (M : ModuleCat.{u} R) (hfc : IsClosed (range f))
  [NormedSpace ℝ V] [FiniteDimensional ℝ V]

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
theorem singularHomologyComplPreimageCoreIso_hom_naturality (hε₀ : 0 < ε) (hp : serreFibrations p)
    (hp' : serreFibrations p') (n m : ℕ) (h : n + finrank ℝ V = m) :
    TopPair.singularHomologyMap
        (TopPair.ofSubsetMap g
          (mapsTo_compl_preimage_singleton_compl_preimage_range_of_forall_eq hg hsf)) M m ≫
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
    (mapsTo_compl_preimage_singleton_compl_preimage_range_of_forall_eq hg hsf) M
    (hτ.isOpen_tubeBall ε) hfc (hτ.range_subset_tubeBall hε₀) (e.isOpen_chartBall b' ε)
    isClosed_singleton hp hp' (mem_serreFibrations_normalCoordinate hτ ε)
    (serreFibrations.of_isIso _) (convex_ball 0 ε) (ball_mem_nhds 0 hε₀) n m h).trans ?_
  -- Both restrictions of `g` send a point `x` of `p'⁻¹(b')` to `g x`.
  congr 2
  ext x
  exact (g.coe_preimageMapOver_apply hg _ x).symm

include hsf in
/-- **The shriek maps of a framed submanifold and of a transverse point commute, on classes**
(Barraud–Damian–Humilière–Oancea, proof of Lemma 7.7). In the setting of
`TauCeti.TopCat.singularHomologyComplPreimageCoreIso_hom_naturality`, for `α ∈ Hₙ₊ᵣ(E')` the shriek
map of the core sends `g_* α` to the image under the restriction `p'⁻¹(b') → p⁻¹(f(S))` of `g`
of the shriek map `j_! α ∈ Hₙ(p'⁻¹(b'))` of the point: `j_{f(S)!} (g_* α) = (g|)_* (j_! α)`. -/
theorem singularHomologyComplPreimageCoreIso_singularHomologyπ_homologyMap (hε₀ : 0 < ε)
    (hp : serreFibrations p) (hp' : serreFibrations p') (n m : ℕ) (h : n + finrank ℝ V = m)
    (α : ((_root_.TopCat.toSSet.obj E').homology M m : ModuleCat.{u} R)) :
    (singularHomologyComplPreimageCoreIso hτ M hfc hε₀ hp n m h).hom.hom
        (((TopPair.ofSubset (p ⁻¹' range f)ᶜ).singularHomologyπ M m).hom
          ((SSet.homologyMap (_root_.TopCat.toSSet.map g) M m).hom α)) =
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (g.preimageMapOver hg
            (mapsTo_singleton.2 (hτ.apply_mem_range_of_chartBall e hb hs hε₀)))).hom
        ((singularHomologyComplFiberIso M e hb hε hε₀ hp' n m h).hom.hom
          ((fiberLocalization M p' b' m).hom α)) := by
  have hπ := TopPair.singularHomologyπ_naturality
    (TopPair.ofSubsetMap g
      (mapsTo_compl_preimage_singleton_compl_preimage_range_of_forall_eq hg hsf)) M m
  rw [TopPair.ofSubsetMap_fst] at hπ
  have hsq := singularHomologyComplPreimageCoreIso_hom_naturality hτ hg e hb hε hs hsf M hfc hε₀ hp
    hp' n m h
  have h₁ := congrArg (fun φ ↦ φ.hom α) hπ
  have h₂ := congrArg (fun φ ↦ φ.hom ((fiberLocalization M p' b' m).hom α)) hsq
  dsimp only at h₁ h₂
  -- `TopPair.singularHomologyπ_naturality` composes in the category of the coefficients, whose
  -- instances `rw` does not match against `ModuleCat.hom_comp`.
  erw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply] at h₁
  erw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply] at h₂
  -- The ambient spaces in `h₁` are `TopCat.of` of the carriers, which `rw` does not unfold.
  erw [h₁]
  exact h₂

include hsf in
/-- **Classes of infinite order along the core of a framed tube** (Barraud–Damian–Humilière–Oancea,
Lemma 7.7). In the setting of `TauCeti.TopCat.singularHomologyComplPreimageCoreIso_hom_naturality`,
suppose the restriction `p'⁻¹(b') → p⁻¹(f(S))` of `g` is injective on `Hₙ`, as it is for the
fibration of maps `S² → Q` over a highly connected core. If the shriek map
`j_! α ∈ Hₙ(p'⁻¹(b'))` of the point has infinite order, then so does the shriek map of the core of
`g_* α`. -/
theorem not_isOfFinAddOrder_singularHomologyComplPreimageCoreIso (hε₀ : 0 < ε)
    (hp : serreFibrations p) (hp' : serreFibrations p') (n m : ℕ) (h : n + finrank ℝ V = m)
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

include hsf in
/-- **Classes of infinite order along a highly connected core** (Barraud–Damian–Humilière–Oancea,
Lemma 7.7). In the setting of `TauCeti.TopCat.singularHomologyComplPreimageCoreIso_hom_naturality`,
with coefficients in a ring `R`, suppose that the core `f(S)` has trivial homotopy groups `π_k` at
`s b'` for every `k ≤ N`, and that `g` restricted to the fibres `p'⁻¹(b') → p⁻¹(s b')` is injective
on `Hₙ` for some `n < N`, for instance because `g` is the projection of the pullback of `p` along
`s`. If the shriek map `j_! α ∈ Hₙ(p'⁻¹(b'))` of the point has infinite order, then so does the
shriek map of the core of `g_* α`: the inclusion `p⁻¹(s b') → p⁻¹(f(S))` is injective on `Hₙ`
(`TauCeti.TopCat.isIso_singularHomologyMap_preimageInclusion`). -/
theorem not_isOfFinAddOrder_singularHomologyComplPreimageCoreIso_of_subsingleton_homotopyGroup
    {R : Type u} [Ring R] (hε₀ : 0 < ε) (hp : serreFibrations p) (hp' : serreFibrations p')
    {n m N : ℕ} (h : n + finrank ℝ V = m) (hn : n < N)
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

end TauCeti

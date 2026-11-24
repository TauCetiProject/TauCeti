/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Basic

/-!
# The Leray–Hirsch map

Let `k` be a commutative ring, `p : E ⟶ B` a continuous map, and for every degree `d` let
`e d : ι d → Hᵈ(E; k)` be a family of global classes on `E`. The **Leray–Hirsch map** in degree `n`
is

`⨁_{d + q = n} ⨁_{i : ι d} H^q(B; k) ⟶ Hⁿ(E; k)`, `(a_{d,i}) ↦ ∑ p^* a_{d,i} ⌣ e_{d,i}`.

The Leray–Hirsch theorem asserts that it is bijective for a locally trivial bundle with fibre `F`
whose classes `e d` restrict to a basis of `Hᵈ` of every fibre, under finiteness hypotheses on the
fibre.

## Main definitions and results

* `TopCat.lerayHirsch`: the Leray–Hirsch map, characterized on summands by
  `TopCat.lerayHirsch_lof`.
* `TopCat.lerayHirsch_lof_naturality`, `TopCat.lerayHirsch_comp_lmap`, `TopCat.lerayHirsch_lmap`,
  `TopCat.singularCohomologyMap_lerayHirsch`: naturality for maps of total spaces covering a map
  of the bases.
* `TopCat.lerayHirsch_bijective_iff_of_bijective`, `TopCat.lerayHirsch_bijective_iff_of_isIso`:
  invariance of bijectivity under such maps inducing bijections on cohomology.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4D.1 (Leray–Hirsch).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory
open scoped DirectSum

universe w u

namespace TopCat

variable {k : Type w} [CommRing k]

section Defs

variable {E B : TopCat.{w}} (p : E ⟶ B) (n : ℕ) {ι : ℕ → Type u}
  [∀ d, DecidableEq (ι d)]
  (e : ∀ d, ι d → E.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) d)

/-- **The Leray–Hirsch map** of `p : E ⟶ B` and a family of classes `e d : ι d → Hᵈ(E; k)` in degree
`n`, `⨁_{d + q = n} ⨁_{i : ι d} H^q(B; k) ⟶ Hⁿ(E; k)`, sending `a` in the summand indexed by
`d + q = n` and `i : ι d` to `p^* a ⌣ e d i`. -/
def lerayHirsch :
    (⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.val.1,
        B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.val.2) →ₗ[k]
      E.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n :=
  DirectSum.toModule k _ _ fun j ↦
    (E.singularCup k (λ_ _).inv (λ_ _).hom j.1.val.2 j.1.val.1 n
        (by rw [add_comm]; exact j.1.property)).flip (e j.1.val.1 j.2) ∘ₗ
      (TopCat.singularCohomologyMap p j.1.val.2).hom

/-- The Leray–Hirsch map sends `a` in the summand indexed by `d + q = n` and `i : ι d` to
`p^* a ⌣ e d i`. -/
@[simp]
lemma lerayHirsch_lof (d q : ℕ) (h : d + q = n) (i : ι d)
    (a : B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    lerayHirsch p n e (DirectSum.lof k _ (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
        ι pq.val.1 ↦
        B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.val.2)
        ⟨⟨(d, q), h⟩, i⟩ a) =
      E.singularCup k (λ_ _).inv (λ_ _).hom q d n (by omega)
        (TopCat.singularCohomologyMap p q a) (e d i) := by
  simp [lerayHirsch]

end Defs

section Naturality

variable {E B E' B' : TopCat.{w}} {p : E ⟶ B} {p' : E' ⟶ B'} {n : ℕ} {ι : ℕ → Type u}
  [∀ d, DecidableEq (ι d)]
  {e : ∀ d, ι d → E.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) d}
  {e' : ∀ d, ι d → E'.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) d}

/-- **Naturality of the Leray–Hirsch map.** For maps `f : E' ⟶ E` and `g : B' ⟶ B` with
`f ≫ p = p' ≫ g`, carrying the classes `e` to the classes `e'`, the Leray–Hirsch map of `p'` sends
`g^* a` in a summand to the pullback along `f` of the image of `a` under the Leray–Hirsch map of
`p`. -/
lemma lerayHirsch_lof_naturality (f : E' ⟶ E) (g : B' ⟶ B) (hfg : f ≫ p = p' ≫ g)
    (d q : ℕ) (h : d + q = n) (i : ι d)
    (he : TopCat.singularCohomologyMap f d (e d i) = e' d i)
    (a : B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    lerayHirsch p' n e' (DirectSum.lof k _ (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
        ι pq.val.1 ↦
        B'.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.val.2)
        ⟨⟨(d, q), h⟩, i⟩ (TopCat.singularCohomologyMap g q a)) =
      TopCat.singularCohomologyMap f n (lerayHirsch p n e (DirectSum.lof k _
        (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.val.1 ↦
          B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.val.2)
        ⟨⟨(d, q), h⟩, i⟩ a)) := by
  rw [lerayHirsch_lof, lerayHirsch_lof, ← singularCup_naturality, ← he,
    ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← TopCat.singularCohomologyMap_comp, ← TopCat.singularCohomologyMap_comp, hfg]

/-- **Naturality of the Leray–Hirsch map**, as linear maps. For maps `f : E' ⟶ E` and `g : B' ⟶ B`
with `f ≫ p = p' ≫ g`, carrying the classes `e` to the classes `e'`, the Leray–Hirsch map of `p'`
precomposed with the pullback along `g` on every summand is the Leray–Hirsch map of `p` followed by
the pullback along `f`. -/
lemma lerayHirsch_comp_lmap (f : E' ⟶ E) (g : B' ⟶ B) (hfg : f ≫ p = p' ≫ g)
    (he : ∀ d ≤ n, ∀ i, TopCat.singularCohomologyMap f d (e d i) = e' d i) :
    lerayHirsch p' n e' ∘ₗ
        DirectSum.lmap (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.val.1 ↦
          (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
            (M := 𝟙_ (ModuleCat.{w} k)) g j.1.val.2).hom) =
      (TopCat.singularCohomologyMap f n).hom ∘ₗ lerayHirsch p n e := by
  refine DirectSum.linearMap_ext k fun ⟨⟨⟨d, q⟩, h⟩, i⟩ ↦ LinearMap.ext fun a ↦ ?_
  simp only [LinearMap.comp_apply, DirectSum.lmap_lof]
  exact lerayHirsch_lof_naturality f g hfg d q h i (he d (by omega) i) a

/-- **Naturality of the Leray–Hirsch map**, applied to an element: under the hypotheses of
`TopCat.lerayHirsch_comp_lmap`, the Leray–Hirsch map of `p'` sends the pullback along `g` of `x`
on every summand to the pullback along `f` of the image of `x` under the Leray–Hirsch map of
`p`. -/
lemma lerayHirsch_lmap (f : E' ⟶ E) (g : B' ⟶ B) (hfg : f ≫ p = p' ≫ g)
    (he : ∀ d ≤ n, ∀ i, TopCat.singularCohomologyMap f d (e d i) = e' d i)
    (x : ⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.val.1,
      B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.val.2) :
    lerayHirsch p' n e'
        (DirectSum.lmap (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.val.1 ↦
          (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
            (M := 𝟙_ (ModuleCat.{w} k)) g j.1.val.2).hom) x) =
      TopCat.singularCohomologyMap f n (lerayHirsch p n e x) :=
  DFunLike.congr_fun (lerayHirsch_comp_lmap f g hfg he) x

/-- Bijectivity of the Leray–Hirsch map is invariant under maps `f : E' ⟶ E` and `g : B' ⟶ B`
with `f ≫ p = p' ≫ g` carrying the classes `e` to the classes `e'`, provided `f` induces a
bijection on cohomology in degree `n` and `g` in all degrees `q ≤ n`. -/
lemma lerayHirsch_bijective_iff_of_bijective (f : E' ⟶ E) (g : B' ⟶ B) (hfg : f ≫ p = p' ≫ g)
    (he : ∀ d ≤ n, ∀ i, TopCat.singularCohomologyMap f d (e d i) = e' d i)
    (hf : Function.Bijective (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
      (M := 𝟙_ (ModuleCat.{w} k)) f n))
    (hg : ∀ q ≤ n, Function.Bijective (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k))
      (k := k) (M := 𝟙_ (ModuleCat.{w} k)) g q)) :
    Function.Bijective (lerayHirsch p' n e') ↔ Function.Bijective (lerayHirsch p n e) := by
  have hsrc : Function.Bijective
      (DirectSum.lmap (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.val.1 ↦
        (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
          (M := 𝟙_ (ModuleCat.{w} k)) g j.1.val.2).hom)) :=
    ⟨(DirectSum.lmap_injective _).2 fun j ↦ (hg _ (by have := j.1.property; omega)).1,
      (DirectSum.lmap_surjective _).2 fun j ↦ (hg _ (by have := j.1.property; omega)).2⟩
  rw [← Function.Bijective.of_comp_iff _ hsrc, ← LinearMap.coe_comp,
    lerayHirsch_comp_lmap f g hfg he, LinearMap.coe_comp]
  exact Function.Bijective.of_comp_iff' hf _

/-- Bijectivity of the Leray–Hirsch map is invariant under isomorphisms `f : E' ⟶ E` and
`g : B' ⟶ B` with `f ≫ p = p' ≫ g` carrying the classes `e` to the classes `e'`. -/
lemma lerayHirsch_bijective_iff_of_isIso (f : E' ⟶ E) (g : B' ⟶ B) [IsIso f] [IsIso g]
    (hfg : f ≫ p = p' ≫ g)
    (he : ∀ d ≤ n, ∀ i, TopCat.singularCohomologyMap f d (e d i) = e' d i) :
    Function.Bijective (lerayHirsch p' n e') ↔ Function.Bijective (lerayHirsch p n e) :=
  lerayHirsch_bijective_iff_of_bijective f g hfg he
    ((TauCeti.singularCohomologyFunctor _ k _ n).mapIso (asIso f).op).toLinearEquiv.bijective
    fun q _ ↦
      ((TauCeti.singularCohomologyFunctor _ k _ q).mapIso (asIso g).op).toLinearEquiv.bijective

/-- **Naturality of the Leray–Hirsch map** for the pulled-back classes: for a map `φ : E ⟶ E'`
covering `f : B ⟶ B'`, pulling back the image of `a` along `φ` gives the image of `f^* a` for the
classes `φ^* e'`. -/
lemma singularCohomologyMap_lerayHirsch (φ : E' ⟶ E) (g : B' ⟶ B) (hφg : φ ≫ p = p' ≫ g)
    (x : ⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.val.1,
      B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.val.2) :
    TopCat.singularCohomologyMap φ n (lerayHirsch p n e x) =
      lerayHirsch p' n (fun d i ↦ TopCat.singularCohomologyMap φ d (e d i))
        (DirectSum.lmap (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.val.1 ↦
          (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
            (M := 𝟙_ (ModuleCat.{w} k)) g j.1.val.2).hom) x) :=
  (lerayHirsch_lmap φ g hφg (fun _ _ _ ↦ rfl) x).symm

end Naturality


end TopCat

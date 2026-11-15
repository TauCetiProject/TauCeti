/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Basis
public import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
public import TauCeti.AlgebraicTopology.Cohomology.LerayHirsch.Product
public import TauCeti.AlgebraicTopology.Cohomology.Point
public import TauCeti.LinearAlgebra.End.LocallyNilpotent
public import TauCeti.Topology.Category.TopCat.Monoidal

/-!
# The Leray–Hirsch theorem for a product with fibrewise basis classes

Let `k` be a commutative ring and let `F` be a space whose homology `Hₚ(F; k)` is projective in
every degree and finitely generated in degrees `p ≤ n`. Let `X` be a space and, for every degree
`p`, let `c p : ι p → Hᵖ(X × F; k)` be a family of classes on the product, finite for `p ≤ n`,
whose restrictions `c p i |_{x} ∈ Hᵖ(F; k)` along the inclusion `f ↦ (x, f)` of the fibre over `x`
(`TopCat.prodFiberInclusion`) form a basis of `Hᵖ(F; k)` for every point `x : X`. Then the
**Leray–Hirsch map** of the classes `c` in degree `n`,

`⨁_{p + q = n} ⨁_{i : ι p} H^q(X; k) ⟶ Hⁿ(X × F; k)`, `(a_{p,i}) ↦ ∑ pr₁^* a_{p,i} ⌣ c_{p,i}`,

(`TopCat.lerayHirschProdOfClasses`) is bijective (`TopCat.lerayHirschProdOfClasses_bijective`).
This is the trivial-bundle case of the Leray–Hirsch theorem with the hypothesis of the general
theorem: the classes are global classes on the total space restricting to a basis of the
cohomology of every fibre, not pullbacks of a basis of the fibre. For the pullbacks
`pr₂^* b_{p,i}` of a basis `b` of the cohomology of `F` it is the Leray–Hirsch map
`TopCat.lerayHirschProd` (`TopCat.lerayHirschProdOfClasses_snd`). Restricted to the fibre over
`x`, the image of `a` is the combination of the restricted classes with coefficients the values at
`x` of the base-degree-zero components of `a`
(`TopCat.singularCohomologyMap_prodFiberInclusion_lerayHirschProdOfClasses`), and the map is
natural for maps of products covering a map of the bases
(`TopCat.singularCohomologyMap_lerayHirschProdOfClasses`).

The proof reduces to `TopCat.lerayHirschProd_bijective` for the basis `b` of `Hᵖ(F; k)` given by
the restrictions of the classes to the fibre over a chosen point. Expanding every class
`c_{p,i} = ∑ pr₁^* γ_{p,i;p',i'} ⌣ pr₂^* b_{p',i'}` by that theorem, associativity and naturality
of the cup product write the Leray–Hirsch map of `c` as that of `b` after the coefficient map
`a ↦ (∑ a_{p,i} ⌣ γ_{p,i;p',i'})`, whose coefficients lie in `H^{p - p'}(X; k)`. This coefficient
map is block triangular for the fibre degree. Its diagonal blocks are the matrices of degree-zero
classes `γ_{p,i;p,i'} ∈ H⁰(X; k)` whose values at a point `x` form the change of basis matrix from
`b` to the restrictions of `c` to the fibre over `x`
(`TopCat.singularCohomologyMap_prodFiberInclusion_lerayHirschProd`). Since these are invertible
at every point, the diagonal blocks are invertible (`TauCeti.exists_singularCup_matrix_eq_one`,
applied on each path component), and the coefficient map is an invertible block diagonal map times
a unipotent one.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4D.1 (Leray–Hirsch).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicTopology
open scoped DirectSum Matrix

universe w

namespace TopCat

variable {k : Type w} [CommRing k]

section Definition

variable (X F : TopCat.{w})

variable (n : ℕ) {ι : ℕ → Type w} [∀ p, DecidableEq (ι p)]
  (c : ∀ p, ι p → (X ⊗ F).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)

/-- **The Leray–Hirsch map of the product** `X × F` and a family of classes
`c p : ι p → Hᵖ(X × F; k)` in degree `n`,
`⨁_{p + q = n} ⨁_{i : ι p} H^q(X; k) ⟶ Hⁿ(X × F; k)`, sending `a` in the summand indexed by
`p + q = n` and `i : ι p` to `pr₁^* a ⌣ c p i`. -/
def lerayHirschProdOfClasses :
    (⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1,
        X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2) →ₗ[k]
      (X ⊗ F).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n :=
  DirectSum.toModule k _ _ fun j ↦
    ((X ⊗ F).singularCup k (λ_ _).inv (λ_ _).hom j.1.1.2 j.1.1.1 n
        (by rw [add_comm]; exact j.1.2)).flip (c j.1.1.1 j.2) ∘ₗ
      (TopCat.singularCohomologyMap (fst X F) j.1.1.2).hom

/-- The Leray–Hirsch map of the classes `c` sends `a` in the summand indexed by `p + q = n` and
`i : ι p` to `pr₁^* a ⌣ c p i`. -/
@[simp]
lemma lerayHirschProdOfClasses_lof (p q : ℕ) (h : p + q = n) (i : ι p)
    (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    lerayHirschProdOfClasses X F n c (DirectSum.lof k _
        (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1 ↦
          X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2)
        ⟨⟨(p, q), h⟩, i⟩ a) =
      (X ⊗ F).singularCup k (λ_ _).inv (λ_ _).hom q p n (by omega)
        (TopCat.singularCohomologyMap (fst X F) q a) (c p i) := by
  simp [lerayHirschProdOfClasses]

/-- **Naturality of the Leray–Hirsch map of the classes**: for a map `φ : X × F ⟶ X' × F'` covering
`f : X ⟶ X'`, pulling back the image of `a` along `φ` gives the image of `f^* a` for the
pulled-back classes `φ^* c`. -/
lemma singularCohomologyMap_lerayHirschProdOfClasses {X' F' : TopCat.{w}} (φ : X ⊗ F ⟶ X' ⊗ F')
    (f : X ⟶ X') (hφ : φ ≫ fst X' F' = fst X F ≫ f)
    (c : ∀ p, ι p → (X' ⊗ F').singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
    (a : ⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1,
        X'.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2) :
    TopCat.singularCohomologyMap φ n (lerayHirschProdOfClasses X' F' n c a) =
      lerayHirschProdOfClasses X F n (fun p i ↦ TopCat.singularCohomologyMap φ p (c p i))
        (DirectSum.lmap (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1 ↦
          (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
            (M := 𝟙_ (ModuleCat.{w} k)) f j.1.1.2).hom) a) := by
  suffices h : (TopCat.singularCohomologyMap φ n).hom ∘ₗ lerayHirschProdOfClasses X' F' n c =
      lerayHirschProdOfClasses X F n (fun p i ↦ TopCat.singularCohomologyMap φ p (c p i)) ∘ₗ
        DirectSum.lmap (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1 ↦
          (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
            (M := 𝟙_ (ModuleCat.{w} k)) f j.1.1.2).hom) from LinearMap.congr_fun h a
  refine DirectSum.linearMap_ext k fun ⟨⟨⟨p, q⟩, h⟩, i⟩ ↦ LinearMap.ext fun a ↦ ?_
  simp only [LinearMap.comp_apply, DirectSum.lmap_lof]
  rw [lerayHirschProdOfClasses_lof, lerayHirschProdOfClasses_lof, ← singularCup_naturality,
    ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← singularCohomologyMap_comp,
    ← singularCohomologyMap_comp, hφ]

/-- For the pullbacks `pr₂^* b` of classes `b` on `F`, the Leray–Hirsch map of the classes is the
Leray–Hirsch map `TopCat.lerayHirschProd` of the product. -/
lemma lerayHirschProdOfClasses_snd
    (b : ∀ p, Module.Basis (ι p) k
      (F.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)) :
    lerayHirschProdOfClasses X F n
        (fun p i ↦ TopCat.singularCohomologyMap (snd X F) p (b p i)) =
      lerayHirschProd X F n b :=
  DirectSum.linearMap_ext k fun ⟨⟨⟨p, q⟩, h⟩, i⟩ ↦ LinearMap.ext fun a ↦ by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, lerayHirschProdOfClasses_lof,
      lerayHirschProd_lof]

end Definition

section Bijective

variable {X F : TopCat.{w}} {ι : ℕ → Type w} [∀ p, DecidableEq (ι p)]

/-- The source `⨁_{p + q = n} ⨁_{i : ι p} H^q(X; k)` of the Leray–Hirsch maps in degree `n`. -/
private abbrev LHSource (k : Type w) [CommRing k] (X : TopCat.{w}) (ι : ℕ → Type w) (n : ℕ) :=
  ⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1,
    X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2

/-- The summand inclusion of the source of the Leray–Hirsch maps. -/
private abbrev lhLof (n p q : ℕ) (h : p + q = n) (i : ι p) :
    X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q →ₗ[k]
      LHSource k X ι n :=
  DirectSum.lof k _ (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1 ↦
    X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2) ⟨⟨(p, q), h⟩, i⟩

/-- Linear maps out of the source of the Leray–Hirsch maps agree if they agree on summands. -/
private lemma lhSource_ext {n : ℕ} {M : Type*} [AddCommGroup M] [Module k M]
    {f g : LHSource k X ι n →ₗ[k] M}
    (h : ∀ p q (hpq : p + q = n) (i : ι p) a, f (lhLof n p q hpq i a) = g (lhLof n p q hpq i a)) :
    f = g :=
  DirectSum.linearMap_ext k fun ⟨⟨⟨p, q⟩, hpq⟩, i⟩ ↦ LinearMap.ext fun a ↦ h p q hpq i a

/-- A property of elements of the source closed under zero and addition holds everywhere if it
holds on summands. -/
private lemma lhSource_induction {n : ℕ} {motive : LHSource k X ι n → Prop} (g : LHSource k X ι n)
    (zero : motive 0) (add : ∀ g g', motive g → motive g' → motive (g + g'))
    (lof : ∀ p q (hpq : p + q = n) (i : ι p) a, motive (lhLof n p q hpq i a)) : motive g := by
  induction g using DirectSum.induction_on with
  | zero => exact zero
  | of j a => obtain ⟨⟨⟨p, q⟩, hpq⟩, i⟩ := j; exact lof p q hpq i a
  | add g g' hg hg' => exact add g g' hg hg'

/-- The component of base degree `0` and index `l` of a summand of base degree `0` and index
`i = l`. -/
private lemma lhLof_apply_self (p : ℕ) (h : p + 0 = p) (i : ι p)
    (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0) :
    lhLof p p 0 h i a ⟨⟨(p, 0), add_zero p⟩, i⟩ = a :=
  DirectSum.of_eq_same _ _

/-- The component of base degree `0` and index `l` of a summand of base degree `0` and index
`i ≠ l` vanishes. -/
private lemma lhLof_apply_of_ne (p : ℕ) (h : p + 0 = p) {i l : ι p} (hl : l ≠ i)
    (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0) :
    lhLof p p 0 h i a ⟨⟨(p, 0), add_zero p⟩, l⟩ = 0 :=
  DirectSum.of_eq_of_ne _ _ _ fun he ↦ hl (eq_of_heq (Sigma.mk.inj_iff.1 he).2)

/-- The component of base degree `0` of a summand of positive base degree vanishes. -/
private lemma lhLof_apply_of_ne_zero (p p' q' : ℕ) (h : p' + q' = p) (hq : q' ≠ 0) (i : ι p')
    (l : ι p) (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q') :
    lhLof p p' q' h i a ⟨⟨(p, 0), add_zero p⟩, l⟩ = 0 :=
  DirectSum.of_eq_of_ne _ _ _ fun he ↦ hq (by
    have := congrArg (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = p}, ι pq.1.1 ↦ j.1.1.2) he
    exact this.symm)

/-- Cupping on the left with `a ∈ H^q(X; k)` and shifting the base degrees by `q`: the map from the
source in degree `p` to the source in degree `n = p + q` sending `β` in the summand indexed by
`(p', q')` and `i'` to `a ⌣ β` in the summand indexed by `(p', q + q')` and `i'`. -/
private def shiftCup (n p q : ℕ) (h : p + q = n) :
    X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q →ₗ[k]
      LHSource k X ι p →ₗ[k] LHSource k X ι n :=
  (DirectSum.toModule k _ _ fun j' : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = p}, ι pq.1.1 ↦
    ((X.singularCup k (λ_ _).inv (λ_ _).hom q j'.1.1.2 (q + j'.1.1.2) rfl).compr₂
      (DirectSum.lof k _ (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1 ↦
          X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2)
        ⟨⟨(j'.1.1.1, q + j'.1.1.2), by have := j'.1.2; omega⟩, j'.2⟩)).flip).flip

private lemma shiftCup_lof (n p q : ℕ) (h : p + q = n) (p' q' : ℕ) (h' : p' + q' = p) (i : ι p')
    (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q)
    (β : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q') :
    shiftCup n p q h a (lhLof p p' q' h' i β) =
      lhLof n p' (q + q') (by omega) i
        (X.singularCup k (λ_ _).inv (λ_ _).hom q q' (q + q') rfl a β) := by
  simp [shiftCup]

/-- The coefficient map of a family `γ p i` of elements of the source in degree `p`: it sends `a` in
the summand indexed by `p + q = n` and `i` to `shiftCup a (γ p i)`. -/
private def coeffMap (n : ℕ) (γ : ∀ p, ι p → LHSource k X ι p) :
    LHSource k X ι n →ₗ[k] LHSource k X ι n :=
  DirectSum.toModule k _ _ fun j ↦ (shiftCup n j.1.1.1 j.1.1.2 j.1.2).flip (γ j.1.1.1 j.2)

private lemma coeffMap_lof (n : ℕ) (γ : ∀ p, ι p → LHSource k X ι p) (p q : ℕ) (h : p + q = n)
    (i : ι p) (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    coeffMap n γ (lhLof n p q h i a) = shiftCup n p q h a (γ p i) := by
  simp [coeffMap]

section Diagonal

variable (s : ∀ p, Finset (ι p))

/-- The block diagonal map of a family of matrices `E p` of degree-zero classes with columns in
`s p`: it sends `a` in the summand indexed by `(p, q)` and `i` to `∑ i' ∈ s p, a ⌣ E p i i'` in the
summands indexed by `(p, q)` and `i'`. -/
private def diagMap (n : ℕ)
    (E : ∀ p, ι p → ι p → X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0) :
    LHSource k X ι n →ₗ[k] LHSource k X ι n :=
  DirectSum.toModule k _ _ fun j ↦ ∑ i' ∈ s j.1.1.1, DirectSum.lof k _
      (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1 ↦
        X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2) ⟨j.1, i'⟩ ∘ₗ
    (X.singularCup k (λ_ _).inv (λ_ _).hom j.1.1.2 0 j.1.1.2 (add_zero _)).flip
      (E j.1.1.1 j.2 i')

private lemma diagMap_lof (n : ℕ)
    (E : ∀ p, ι p → ι p → X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0)
    (p q : ℕ) (h : p + q = n) (i : ι p)
    (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    diagMap s n E (lhLof n p q h i a) =
      ∑ i' ∈ s p, lhLof n p q h i' (X.singularCup k (λ_ _).inv (λ_ _).hom q 0 q (add_zero _) a
        (E p i i')) := by
  simp [diagMap]

private lemma diagMap_comp (n : ℕ)
    (E E' : ∀ p, ι p → ι p →
      X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0) :
    diagMap s n E ∘ₗ diagMap s n E' = diagMap s n fun p i l ↦
      ∑ j ∈ s p, X.singularCup k (λ_ _).inv (λ_ _).hom 0 0 0 rfl (E' p i j) (E p j l) :=
  lhSource_ext fun p q h i a ↦ by
    simp only [LinearMap.comp_apply, diagMap_lof, map_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun j _ ↦ congrArg _ ?_
    exact X.singularCup_assoc_unit k (add_zero q) (add_zero q) rfl (add_zero q) a (E' p i j)
      (E p j l)

private lemma diagMap_eq_id (n : ℕ)
    (E : ∀ p, ι p → ι p → X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0)
    (hs : ∀ p ≤ n, ∀ i, i ∈ s p)
    (hE : ∀ p ≤ n, ∀ i l, E p i l = if i = l then X.singularCohomologyZeroOne else 0) :
    diagMap s n E = LinearMap.id :=
  lhSource_ext fun p q h i a ↦ by
    rw [diagMap_lof, LinearMap.id_apply, Finset.sum_eq_single_of_mem i (hs p (by omega) i)]
    · simp [hE p (by omega)]
    · intro l _ hl
      simp [hE p (by omega), Ne.symm hl]

/-- The filtration of the source by the fibre degree: the span of the summands of fibre degree
`p < m`. -/
private def filt (n m : ℕ) : Submodule k (LHSource k X ι n) :=
  ⨆ (j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1) (_ : j.1.1.1 < m),
    LinearMap.range (DirectSum.lof k _
      (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1 ↦
        X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2) j)

private lemma lhLof_mem_filt {n m p q : ℕ} (h : p + q = n) (hp : p < m) (i : ι p)
    (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    lhLof n p q h i a ∈ filt (k := k) (X := X) (ι := ι) n m :=
  Submodule.mem_iSup_of_mem ⟨⟨(p, q), h⟩, i⟩ (Submodule.mem_iSup_of_mem hp ⟨a, rfl⟩)

private lemma filt_le_iff {n m : ℕ} {N : Submodule k (LHSource k X ι n)} :
    filt n m ≤ N ↔ ∀ p q (h : p + q = n) (i : ι p) a, p < m → lhLof n p q h i a ∈ N := by
  refine ⟨fun hN p q h i a hp ↦ hN (lhLof_mem_filt h hp i a), fun hN ↦ ?_⟩
  refine iSup₂_le fun ⟨⟨⟨p, q⟩, h⟩, i⟩ hp ↦ ?_
  rintro _ ⟨a, rfl⟩
  exact hN p q h i a hp

private lemma filt_mono {n m m' : ℕ} (hm : m ≤ m') :
    filt (k := k) (X := X) (ι := ι) n m ≤ filt n m' :=
  filt_le_iff.2 fun _ _ h i a hp ↦ lhLof_mem_filt h (hp.trans_le hm) i a

private lemma filt_zero (n : ℕ) : filt (k := k) (X := X) (ι := ι) n 0 = ⊥ :=
  le_bot_iff.1 (filt_le_iff.2 fun _ _ _ _ _ hp ↦ absurd hp (Nat.not_lt_zero _))

private lemma filt_succ_self (n : ℕ) : filt (k := k) (X := X) (ι := ι) n (n + 1) = ⊤ := by
  refine eq_top_iff.2 fun g _ ↦ lhSource_induction g (zero_mem _) (fun _ _ ↦ add_mem) ?_
  intro p q h i a
  exact lhLof_mem_filt h (by omega) i a

private lemma diagMap_filt_le (n m : ℕ)
    (E : ∀ p, ι p → ι p →
      X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0) :
    filt n m ≤ (filt n m).comap (diagMap s n E) :=
  filt_le_iff.2 fun p q h i a hp ↦ by
    rw [Submodule.mem_comap, diagMap_lof]
    exact Submodule.sum_mem _ fun l _ ↦ lhLof_mem_filt h hp l _

/-- The diagonal part of an element `g` of the source in degree `p`: its components of base
degree `0` and index in `s p`. -/
private def diagPart (p : ℕ) (g : LHSource k X ι p) : LHSource k X ι p :=
  ∑ i' ∈ s p, lhLof p p 0 (add_zero p) i' (g ⟨⟨(p, 0), add_zero p⟩, i'⟩)

private lemma sub_diagPart_mem_filt (p : ℕ) (hs : ∀ i, i ∈ s p) (g : LHSource k X ι p) :
    g - diagPart s p g ∈ filt (k := k) (X := X) (ι := ι) p p := by
  induction g using lhSource_induction with
  | zero => simp [diagPart]
  | add g g' hg hg' =>
    have : g + g' - diagPart s p (g + g') = (g - diagPart s p g) + (g' - diagPart s p g') := by
      simp only [diagPart, DirectSum.add_apply, map_add, Finset.sum_add_distrib]
      abel
    rw [this]
    exact add_mem hg hg'
  | lof p' q' h' i a =>
    by_cases hq : q' = 0
    · subst hq
      obtain rfl : p' = p := by omega
      have : diagPart s p' (lhLof p' p' 0 h' i a) = lhLof p' p' 0 h' i a := by
        rw [diagPart, Finset.sum_eq_single_of_mem i (hs i)]
        · rw [lhLof_apply_self]
        · intro l _ hl
          rw [lhLof_apply_of_ne _ _ hl, map_zero]
      rw [this, sub_self]
      exact zero_mem _
    · have : diagPart s p (lhLof p p' q' h' i a) = 0 := by
        refine Finset.sum_eq_zero fun l _ ↦ ?_
        rw [lhLof_apply_of_ne_zero _ _ _ _ hq, map_zero]
      rw [this, sub_zero]
      exact lhLof_mem_filt h' (by omega) i a

private lemma shiftCup_filt_le (n p q : ℕ) (h : p + q = n)
    (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    filt p p ≤ (filt n p).comap (shiftCup (ι := ι) n p q h a) :=
  filt_le_iff.2 fun p' q' h' i β hp ↦ by
    rw [Submodule.mem_comap, shiftCup_lof]
    exact lhLof_mem_filt _ hp i _

/-- The coefficient map minus its block diagonal part lowers the fibre degree. -/
private lemma coeffMap_sub_diagMap_lof_mem (n : ℕ) (hs : ∀ p ≤ n, ∀ i, i ∈ s p)
    (γ : ∀ p, ι p → LHSource k X ι p) (p q : ℕ) (h : p + q = n) (i : ι p)
    (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    coeffMap n γ (lhLof n p q h i a) -
        diagMap s n (fun p i i' ↦ γ p i ⟨⟨(p, 0), add_zero p⟩, i'⟩) (lhLof n p q h i a) ∈
      filt n p := by
  have hdiag : diagMap s n (fun p i i' ↦ γ p i ⟨⟨(p, 0), add_zero p⟩, i'⟩) (lhLof n p q h i a) =
      shiftCup n p q h a (diagPart s p (γ p i)) := by
    rw [diagMap_lof, diagPart, map_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [shiftCup_lof]
    -- The summand index `q + 0` and the cup product degree `q + 0` reduce to `q` by `Nat.add`.
    rfl
  rw [coeffMap_lof, hdiag, ← map_sub]
  exact shiftCup_filt_le n p q h a (sub_diagPart_mem_filt s p (hs p (by omega)) (γ p i))

/-- Block diagonal maps whose blocks are, in degrees `p ≤ n`, inverse matrices for the cup product
compose to the identity. -/
private lemma diagMap_mul_eq_one (n : ℕ) (hs : ∀ p ≤ n, ∀ i, i ∈ s p)
    (E E' : ∀ p, ι p → ι p →
      X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0)
    (h : ∀ p ≤ n, ∀ i l, ∑ j ∈ s p, X.singularCup k (λ_ _).inv (λ_ _).hom 0 0 0 rfl (E' p i j)
      (E p j l) = if i = l then X.singularCohomologyZeroOne else 0) :
    diagMap s n E * diagMap s n E' = 1 := by
  rw [Module.End.mul_eq_comp, diagMap_comp, Module.End.one_eq_id]
  exact diagMap_eq_id s n _ hs h

/-- **The coefficient map is invertible** when its diagonal blocks, the matrices of base-degree-zero
components of `γ p i` for `p ≤ n`, have an inverse `B` for the cup product: it is the invertible
block diagonal map times `1 + T` with `T` nilpotent, since `T` lowers the fibre degree. -/
private lemma isUnit_coeffMap (n : ℕ) (hs : ∀ p ≤ n, ∀ i, i ∈ s p)
    (γ : ∀ p, ι p → LHSource k X ι p)
    (B : ∀ p, ι p → ι p → X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0)
    (hAB : ∀ p ≤ n, ∀ i l, ∑ j ∈ s p, X.singularCup k (λ_ _).inv (λ_ _).hom 0 0 0 rfl
      (γ p i ⟨⟨(p, 0), add_zero p⟩, j⟩) (B p j l) =
        if i = l then X.singularCohomologyZeroOne else 0)
    (hBA : ∀ p ≤ n, ∀ i l, ∑ j ∈ s p, X.singularCup k (λ_ _).inv (λ_ _).hom 0 0 0 rfl
      (B p i j) (γ p j ⟨⟨(p, 0), add_zero p⟩, l⟩) =
        if i = l then X.singularCohomologyZeroOne else 0) :
    IsUnit (coeffMap n γ) := by
  let A (p : ℕ) (i i' : ι p) := γ p i ⟨⟨(p, 0), add_zero p⟩, i'⟩
  have hD : diagMap s n A * diagMap s n B = 1 := diagMap_mul_eq_one s n hs _ _ hBA
  -- The coefficient map is `D (1 + T)` with `D` block diagonal and `T` lowering the fibre degree.
  let T : Module.End k (LHSource k X ι n) := diagMap s n B * (coeffMap n γ - diagMap s n A)
  have hT (m : ℕ) : filt n (m + 1) ≤ (filt n m).comap T :=
    filt_le_iff.2 fun p q h i a hp ↦ diagMap_filt_le s n m B
      (filt_mono (by omega) (coeffMap_sub_diagMap_lof_mem s n hs γ p q h i a))
  have hU : IsUnit (1 + T) := (Module.End.isUnit_iff _).2 <|
    Module.End.bijective_of_sub_mem_filtration (filt_zero n)
      (fun _ ↦ ⟨n + 1, by rw [filt_succ_self]; trivial⟩) fun m v hv ↦ by simpa using hT m hv
  have hM : coeffMap n γ = diagMap s n A * (1 + T) := by
    rw [mul_add, mul_one, ← mul_assoc, hD, one_mul, add_sub_cancel]
  rw [hM]
  exact (Units.mk _ _ hD (diagMap_mul_eq_one s n hs _ _ hAB)).isUnit.mul hU

end Diagonal

/-- **Expansion of the Leray–Hirsch map of the classes.** If each class `c p i` is the image of
`γ p i` under the Leray–Hirsch map of a basis `b`, then the Leray–Hirsch map of `c` is that of `b`
after the coefficient map of `γ`. -/
private lemma lerayHirschProdOfClasses_eq (n : ℕ)
    (c : ∀ p, ι p → (X ⊗ F).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
    (b : ∀ p, Module.Basis (ι p) k
      (F.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p))
    (γ : ∀ p, ι p → LHSource k X ι p)
    (hγ : ∀ p ≤ n, ∀ i, lerayHirschProd X F p b (γ p i) = c p i) :
    lerayHirschProdOfClasses X F n c = lerayHirschProd X F n b ∘ₗ coeffMap n γ := by
  refine lhSource_ext fun p q h i a ↦ ?_
  rw [LinearMap.comp_apply, coeffMap_lof, lerayHirschProdOfClasses_lof, ← hγ p (by omega)]
  induction γ p i using lhSource_induction with
  | zero => simp
  | add g g' hg hg' => simp only [map_add, hg, hg']
  | lof p' q' h' i' β =>
    rw [lerayHirschProd_lof, shiftCup_lof, lerayHirschProd_lof, ← singularCup_naturality,
      (X ⊗ F).singularCup_assoc_unit k (m' := p) rfl (by omega) (by omega) (by omega)]

variable (X) in
/-- **The restriction of the Leray–Hirsch map of the classes to a fibre**: restricting the image of
`g` to the fibre over `x` gives the combination of the restrictions of the classes with coefficients
the values at `x` of the base-degree-zero components of `g`. -/
theorem singularCohomologyMap_prodFiberInclusion_lerayHirschProdOfClasses (x : X) (p : ℕ)
    [Fintype (ι p)]
    (c : ∀ p, ι p → (X ⊗ F).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
    (g : ⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = p}, ι pq.1.1,
      X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2) :
    TopCat.singularCohomologyMap (prodFiberInclusion X F x) p (lerayHirschProdOfClasses X F p c g) =
      ∑ i', TauCeti.singularCohomologyZeroEval x (g ⟨⟨(p, 0), add_zero p⟩, i'⟩) •
        TopCat.singularCohomologyMap (prodFiberInclusion X F x) p (c p i') := by
  -- In positive degrees the constant map induces zero.
  have hpos {q : ℕ} (hq : q ≠ 0) :
      TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
        (M := 𝟙_ (ModuleCat.{w} k)) (TopCat.const (X := F) x) q = 0 :=
    singularCohomologyMap_eq_zero_of_nullhomotopic (by
      rw [show (TopCat.const (X := F) x).hom = ContinuousMap.const F x from
        ContinuousMap.ext fun _ ↦ TopCat.const_apply _ _]
      exact ContinuousMap.nullhomotopic_of_constant x) hq
  have hlof (q' p' : ℕ) (h' : p' + q' = p) (i : ι p')
      (β : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q') :
      TopCat.singularCohomologyMap (prodFiberInclusion X F x) p
          (lerayHirschProdOfClasses X F p c (lhLof p p' q' h' i β)) =
        F.singularCup k (λ_ _).inv (λ_ _).hom q' p' p (by omega)
          (TopCat.singularCohomologyMap (TopCat.const (X := F) x) q' β)
          (TopCat.singularCohomologyMap (prodFiberInclusion X F x) p' (c p' i)) := by
    rw [lerayHirschProdOfClasses_lof, ← singularCup_naturality, ← ConcreteCategory.comp_apply,
      ← singularCohomologyMap_comp, prodFiberInclusion_fst]
  induction g using lhSource_induction with
  | zero => simp
  | add g g' hg hg' =>
    simp only [map_add, hg, hg', DirectSum.add_apply, add_smul, Finset.sum_add_distrib]
  | lof p' q' h' i β =>
    rw [hlof]
    by_cases hq : q' = 0
    · subst hq
      obtain rfl : p' = p := by omega
      rw [TauCeti.singularCohomologyMap_const_eq_singularCohomologyZeroEval_smul,
        LinearMap.map_smul₂, singularCup_singularCohomologyZeroOne_left, Finset.sum_eq_single i]
      · rw [lhLof_apply_self]
      · intro l _ hl
        rw [lhLof_apply_of_ne _ _ hl, map_zero, zero_smul]
      · simp
    · simp only [hpos hq, ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]
      refine (Finset.sum_eq_zero fun l _ ↦ ?_).symm
      rw [lhLof_apply_of_ne_zero _ _ _ _ hq, map_zero, zero_smul]

variable (X) in
/-- **The restriction of the Leray–Hirsch map of a basis to a fibre**: restricting the image of `g`
to the fibre over `x` gives the combination of the basis with coefficients the values at `x` of
the base-degree-zero components of `g`. -/
theorem singularCohomologyMap_prodFiberInclusion_lerayHirschProd (x : X) (p : ℕ)
    [Fintype (ι p)]
    (b : ∀ p, Module.Basis (ι p) k
      (F.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p))
    (g : ⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = p}, ι pq.1.1,
      X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2) :
    TopCat.singularCohomologyMap (prodFiberInclusion X F x) p (lerayHirschProd X F p b g) =
      ∑ i', TauCeti.singularCohomologyZeroEval x (g ⟨⟨(p, 0), add_zero p⟩, i'⟩) • b p i' := by
  rw [← lerayHirschProdOfClasses_snd,
    singularCohomologyMap_prodFiberInclusion_lerayHirschProdOfClasses]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg _ ?_
  rw [← ConcreteCategory.comp_apply, ← singularCohomologyMap_comp, prodFiberInclusion_snd,
    singularCohomologyMap_id]
  rfl

variable (X) [∀ p, Projective (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
    (𝟙_ (ModuleCat.{w} k))).obj F)]

/-- **The Leray–Hirsch theorem for a product with fibrewise basis classes**: over a commutative ring
`k`, if the homology `Hₚ(F; k)` is projective in every degree and finitely generated in degrees
`p ≤ n`, and the classes `c p : ι p → Hᵖ(X × F; k)`, finite for `p ≤ n`, restrict to a basis of
`Hᵖ(F; k)` on the fibre over every point of `X`, then the Leray–Hirsch map
`⨁_{p + q = n} ⨁_{i : ι p} H^q(X; k) ⟶ Hⁿ(X × F; k)`, `(a_{p,i}) ↦ ∑ pr₁^* a_{p,i} ⌣ c_{p,i}`,
is bijective. -/
theorem lerayHirschProdOfClasses_bijective (n : ℕ)
    (c : ∀ p, ι p → (X ⊗ F).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
    (hι : ∀ p ≤ n, Finite (ι p))
    (hF : ∀ p ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj F))
    (hc : ∀ (x : X) (p : ℕ),
      LinearIndependent k (fun i ↦ TopCat.singularCohomologyMap (prodFiberInclusion X F x) p
        (c p i)) ∧
      ⊤ ≤ Submodule.span k (Set.range fun i ↦
        TopCat.singularCohomologyMap (prodFiberInclusion X F x) p (c p i))) :
    Function.Bijective (lerayHirschProdOfClasses X F n c) := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · -- Over an empty base both sides vanish.
    have h0 (g : LHSource k X ι n) : g = 0 :=
      lhSource_induction (motive := fun g ↦ g = 0) g rfl (fun _ _ h h' ↦ by rw [h, h', add_zero])
        fun p q h i a ↦ by
        rw [(ModuleCat.subsingleton_of_isZero (TauCeti.isZero_singularCohomology_of_isEmpty
          (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) X q)).elim a 0, map_zero]
    have : IsEmpty ↑(X ⊗ F) := inferInstanceAs (IsEmpty (X × F))
    have := ModuleCat.subsingleton_of_isZero (TauCeti.isZero_singularCohomology_of_isEmpty
      (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) (X ⊗ F) n)
    exact ⟨fun g g' _ ↦ (h0 g).trans (h0 g').symm, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  -- The index types in degrees `p ≤ n`, the only ones in the source, are finite.
  have hfin (p : ℕ) (hp : p ≤ n) : Fintype (ι p) := have := hι p hp; Fintype.ofFinite _
  let s (p : ℕ) : Finset (ι p) := if hp : p ≤ n then @Finset.univ _ (hfin p hp) else ∅
  have hs (p : ℕ) (hp : p ≤ n) (i : ι p) : i ∈ s p := by simp [s, hp]
  -- The bases of the cohomology of the fibres, and the basis `b` over the point `x₀`.
  let bx (x : X) (p : ℕ) : Module.Basis (ι p) k
      (F.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p) :=
    Module.Basis.mk (hc x p).1 (hc x p).2
  let b := bx x₀
  have hFp (p : ℕ) (hp : p ≤ n) : ∀ p' ≤ p, Module.Finite k
      (((singularHomologyFunctor (ModuleCat.{w} k) p').obj (𝟙_ (ModuleCat.{w} k))).obj F) :=
    fun p' hp' ↦ hF p' (hp'.trans hp)
  -- The coordinates `γ p i` of the classes `c p i` for the Leray–Hirsch isomorphism of `b`.
  let γ (p : ℕ) (i : ι p) : LHSource k X ι p :=
    if hp : p ≤ n then (lerayHirschProdEquiv X b (hFp p hp)).symm (c p i) else 0
  have hγ (p : ℕ) (hp : p ≤ n) (i : ι p) : lerayHirschProd X F p b (γ p i) = c p i := by
    simp only [γ, hp, ↓reduceDIte, ← lerayHirschProdEquiv_apply X b (hFp p hp),
      LinearEquiv.apply_symm_apply]
  -- The diagonal blocks of the coefficient map, invertible at every point.
  let A (p : ℕ) (i i' : ι p) := γ p i ⟨⟨(p, 0), add_zero p⟩, i'⟩
  have hA (p : ℕ) (hp : p ≤ n) (x : X) :
      letI := hfin p hp
      IsUnit (Matrix.of fun i i' ↦ TauCeti.singularCohomologyZeroEval x (A p i i')) := by
    let := hfin p hp
    have hmat : (Matrix.of fun i i' ↦ TauCeti.singularCohomologyZeroEval x (A p i i')) =
        ((b p).toMatrix (bx x p))ᵀ := by
      ext i i'
      rw [Matrix.transpose_apply, Module.Basis.toMatrix_apply, Module.Basis.mk_apply, ← hγ p hp i,
        singularCohomologyMap_prodFiberInclusion_lerayHirschProd,
        ← Module.Basis.equivFun_symm_apply, ← Module.Basis.equivFun_apply,
        LinearEquiv.apply_symm_apply]
      rfl
    rw [hmat, Matrix.isUnit_transpose]
    let := (b p).invertibleToMatrix (bx x p)
    exact isUnit_of_invertible _
  choose B hB using fun p (hp : p ≤ n) ↦
    letI := hfin p hp
    TauCeti.exists_singularCup_matrix_eq_one (A p) (hA p hp)
  let B' (p : ℕ) : ι p → ι p →
      X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0 :=
    if hp : p ≤ n then B p hp else 0
  have hunit : IsUnit (coeffMap n γ) := isUnit_coeffMap s n hs γ B'
    (fun p hp i l ↦ by simpa only [s, B', hp, ↓reduceDIte] using (hB p hp).1 i l)
    (fun p hp i l ↦ by simpa only [s, B', hp, ↓reduceDIte] using (hB p hp).2 i l)
  rw [lerayHirschProdOfClasses_eq n c b γ hγ]
  exact (lerayHirschProd_bijective X b hF).comp ((Module.End.isUnit_iff _).1 hunit)

/-- **The Leray–Hirsch isomorphism for a product with fibrewise basis classes**
`⨁_{p + q = n} ⨁_{i : ι p} H^q(X; k) ≃ Hⁿ(X × F; k)`, the linear equivalence given by the
Leray–Hirsch map `TopCat.lerayHirschProdOfClasses` under the hypotheses of
`TopCat.lerayHirschProdOfClasses_bijective`. -/
def lerayHirschProdOfClassesEquiv (n : ℕ)
    (c : ∀ p, ι p → (X ⊗ F).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
    (hι : ∀ p ≤ n, Finite (ι p))
    (hF : ∀ p ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj F))
    (hc : ∀ (x : X) (p : ℕ),
      LinearIndependent k (fun i ↦ TopCat.singularCohomologyMap (prodFiberInclusion X F x) p
        (c p i)) ∧
      ⊤ ≤ Submodule.span k (Set.range fun i ↦
        TopCat.singularCohomologyMap (prodFiberInclusion X F x) p (c p i))) :
    (⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1,
        X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2) ≃ₗ[k]
      (X ⊗ F).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n :=
  LinearEquiv.ofBijective (lerayHirschProdOfClasses X F n c)
    (lerayHirschProdOfClasses_bijective X n c hι hF hc)

@[simp]
lemma lerayHirschProdOfClassesEquiv_apply (n : ℕ)
    (c : ∀ p, ι p → (X ⊗ F).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
    (hι : ∀ p ≤ n, Finite (ι p))
    (hF : ∀ p ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj F))
    (hc : ∀ (x : X) (p : ℕ),
      LinearIndependent k (fun i ↦ TopCat.singularCohomologyMap (prodFiberInclusion X F x) p
        (c p i)) ∧
      ⊤ ≤ Submodule.span k (Set.range fun i ↦
        TopCat.singularCohomologyMap (prodFiberInclusion X F x) p (c p i)))
    (a : ⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1,
        X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2) :
    lerayHirschProdOfClassesEquiv X n c hι hF hc a = lerayHirschProdOfClasses X F n c a :=
  (rfl)

end Bijective

end TopCat

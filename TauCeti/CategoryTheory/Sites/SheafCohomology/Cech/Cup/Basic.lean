/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Functor

import TauCeti.Data.Fin.Basic

/-!
# The cup product on Čech complexes

Let `C` be a category with finite products, `U : ι → C` a family of objects, for instance an open
cover of a topological space, and `F` a presheaf of `R`-algebras on `C`, for instance the sheaf of
locally constant functions with values in a commutative ring `R`. The Čech complex of the
underlying presheaf of `R`-modules (`TauCeti.CategoryTheory.cechAlgebraComplex U F`) has in degree
`m` the product over all `a : Fin (m + 1) → ι` of the algebras `F(U (a 0) × ⋯ × U (a m))`, repeated
indices included. This file defines the **cup product** of Čech cochains
(`TauCeti.CategoryTheory.cechCup`): for `a` of degree `p` and `b` of degree `q`,

`(a ⌣ b)(k 0, …, k (p + q)) = a(k 0, …, k p) · b(k p, …, k (p + q))`,

the factor of `a` on the front `p`-face times the factor of `b` on the back `q`-face, both
restricted to `U (k 0) × ⋯ × U (k (p + q))` (`TauCeti.CategoryTheory.cechComponent_cechCup`). No
sign enters, since the coefficients form a single presheaf placed in degree `0`. The file proves
the laws of the product at the level of cochains:

* the **Leibniz rule** `d (a ⌣ b) = d a ⌣ b + (-1) ^ p a ⌣ d b`
  (`TauCeti.CategoryTheory.d_cechCup`). Consequently the product of two cocycles is a cocycle, and
  the product of a coboundary and a cocycle, in either order, is a coboundary
  (`TauCeti.CategoryTheory.d_cechCup_eq_zero`, `TauCeti.CategoryTheory.cechCup_d_left`,
  `TauCeti.CategoryTheory.cechCup_d_right`);
* **associativity** (`TauCeti.CategoryTheory.cechCup_assoc`);
* the **unit**: the `0`-cochain `1` (`TauCeti.CategoryTheory.cechOne`) is a cocycle and a two-sided
  unit (`TauCeti.CategoryTheory.d_cechOne`, `TauCeti.CategoryTheory.cechOne_cechCup`,
  `TauCeti.CategoryTheory.cechCup_cechOne`);
* **naturality** for the maps of Čech complexes induced by morphisms of families, such as
  refinements of open covers (`TauCeti.CategoryTheory.cechComplexMap_cechCup`,
  `TauCeti.CategoryTheory.cechComplexMap_cechOne`), and by morphisms of presheaves of algebras
  (`TauCeti.CategoryTheory.cechComplexFunctor_map_cechCup`,
  `TauCeti.CategoryTheory.cechComplexFunctor_map_cechOne`), and for the comparison
  `Č(G ∘ U, Q) ≅ Č(U, G.op ⋙ Q)` along a functor `G` preserving the products of members
  (`TauCeti.CategoryTheory.cechComplexCompIso_hom_cechCup`,
  `TauCeti.CategoryTheory.cechComplexCompIso_inv_cechCup`), such as the inverse image of opens
  along a continuous map.

The product is not graded commutative on cochains. For presheaves of commutative algebras graded
commutativity holds on cohomology, through a cochain homotopy that is not constructed here.

Cochains are handled through their factors: `TauCeti.CategoryTheory.cechComponent a c` is the
factor of `c` indexed by `a`, and `TauCeti.CategoryTheory.cechFace k σ c` restricts the factor of
`c` indexed by `k ∘ σ` along a map `σ` of vertices. The Čech differential is the alternating sum
of the restrictions along the coface maps (`TauCeti.CategoryTheory.cechComponent_d`), and the cup
product multiplies the restrictions along the front and back faces, so all identities above
reduce to identities between maps of vertices. The maps induced by morphisms of families and of
presheaves act on factors and restrictions by restriction maps and by components of the morphism
(`TauCeti.CategoryTheory.cechComponent_cechComplexMap`,
`TauCeti.CategoryTheory.cechFace_cechComplexMap`,
`TauCeti.CategoryTheory.cechComponent_cechComplexFunctor_map`,
`TauCeti.CategoryTheory.cechFace_cechComplexFunctor_map`); the comparison along a functor acts
by the restrictions along the product comparison maps
(`TauCeti.CategoryTheory.cechComponent_cechComplexCompIso_hom`,
`TauCeti.CategoryTheory.cechFace_cechComplexCompIso_hom`).

## References

* The Stacks Project, Cohomology of Sheaves, Section 20.25 (tag 01FP), for the cup product on
  Čech complexes and its Leibniz rule.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe w v u u'

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {ι : Type w} {U : ι → C}
  {R : Type u'} [CommRing R] {F : Cᵒᵖ ⥤ AlgCat.{w} R}

section Components

variable (U F) in
/-- The Čech complex, for the family `U`, of the presheaf of `R`-modules underlying a presheaf of
`R`-algebras `F`. Its degree `m` term is the product over `a : Fin (m + 1) → ι` of the algebras
`F(U (a 0) × ⋯ × U (a m))`. -/
abbrev cechAlgebraComplex : CochainComplex (ModuleCat.{w} R) ℕ :=
  (cechComplexFunctor U).obj (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))

/-- The factor indexed by `a` of a Čech `m`-cochain, an element of `F(U (a 0) × ⋯ × U (a m))`. -/
def cechComponent {m : ℕ} (a : Fin (m + 1) → ι) :
    (cechAlgebraComplex U F).X m →ₗ[R] F.obj (op (∏ᶜ fun j ↦ U (a j))) :=
  (Pi.π (fun a : Fin (m + 1) → ι ↦ (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)).obj
    (op (∏ᶜ fun j ↦ U (a j)))) a).hom

/-- A Čech cochain is determined by its factors. -/
theorem cechCochain_ext {m : ℕ} {c c' : (cechAlgebraComplex U F).X m}
    (h : ∀ a, cechComponent a c = cechComponent a c') : c = c' := by
  apply (ModuleCat.piIsoPi _).toLinearEquiv.injective
  funext a
  exact (ModuleCat.piIsoPi_hom_ker_subtype_apply _ a c).trans
    ((h a).trans (ModuleCat.piIsoPi_hom_ker_subtype_apply _ a c').symm)

/-- The Čech cochain with prescribed factors. -/
def cechOfComponents {m : ℕ}
    (f : ∀ a : Fin (m + 1) → ι, F.obj (op (∏ᶜ fun j ↦ U (a j)))) :
    (cechAlgebraComplex U F).X m :=
  (ModuleCat.piIsoPi (fun a : Fin (m + 1) → ι ↦
    (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)).obj (op (∏ᶜ fun j ↦ U (a j))))).inv.hom f

/-- The factors of the cochain with prescribed factors are the prescribed ones. -/
@[simp]
theorem cechComponent_cechOfComponents {m : ℕ}
    (f : ∀ a : Fin (m + 1) → ι, F.obj (op (∏ᶜ fun j ↦ U (a j)))) (a : Fin (m + 1) → ι) :
    cechComponent a (cechOfComponents f) = f a :=
  ModuleCat.piIsoPi_inv_kernel_ι_apply (fun a : Fin (m + 1) → ι ↦
    (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)).obj (op (∏ᶜ fun j ↦ U (a j)))) a f

/-- The restriction of a Čech `m`-cochain `c` along a map `σ : Fin (m + 1) → Fin (n + 1)` of
vertices, at `k : Fin (n + 1) → ι`: the factor of `c` indexed by `k ∘ σ`, restricted along the
projection `U (k 0) × ⋯ × U (k n) ⟶ U (k (σ 0)) × ⋯ × U (k (σ m))`. For the coface maps
`σ = j.succAbove` these are the terms of the Čech differential (`cechFace_d`), and the cup product
multiplies the restrictions along the front and back faces (`cechComponent_cechCup`). -/
def cechFace {m n : ℕ} (k : Fin (n + 1) → ι) (σ : Fin (m + 1) → Fin (n + 1)) :
    (cechAlgebraComplex U F).X m →ₗ[R] F.obj (op (∏ᶜ fun j ↦ U (k j))) :=
  (F.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (σ x)).op).hom.toLinearMap ∘ₗ
    cechComponent (k ∘ σ)

/-- The restriction along `σ` is the restriction of the factor indexed by `k ∘ σ`. -/
theorem cechFace_apply {m n : ℕ} (k : Fin (n + 1) → ι) (σ : Fin (m + 1) → Fin (n + 1))
    (c : (cechAlgebraComplex U F).X m) :
    cechFace k σ c =
      (F.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (σ x)).op).hom (cechComponent (k ∘ σ) c) :=
  (rfl)

/-- Restricting along the identity of the vertices is taking the factor. -/
@[simp]
theorem cechFace_id {m : ℕ} (k : Fin (m + 1) → ι) (c : (cechAlgebraComplex U F).X m) :
    cechFace k id c = cechComponent k c := by
  simp [cechFace_apply]

/-- Restrictions along composable maps of vertices compose. -/
theorem map_cechFace {l m n : ℕ} (k : Fin (n + 1) → ι) (τ : Fin (m + 1) → Fin (n + 1))
    (σ : Fin (l + 1) → Fin (m + 1)) (c : (cechAlgebraComplex U F).X l) :
    (F.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (τ x)).op).hom (cechFace (k ∘ τ) σ c) =
      cechFace k (τ ∘ σ) c := by
  have : (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (τ x)) ≫
      (Pi.lift fun x ↦ Pi.π (fun j ↦ U ((k ∘ τ) j)) (σ x)) =
      Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) ((τ ∘ σ) x) :=
    Pi.hom_ext _ _ fun _ ↦ by simp
  rw [cechFace_apply, cechFace_apply, ← AlgCat.comp_apply, ← F.map_comp, ← op_comp]
  exact congrArg (fun g ↦ (F.map g.op).hom (cechComponent (k ∘ τ ∘ σ) c)) this

/-- Reading a factor formula of a map of Čech complexes on cochains: if the factor indexed by `k` of
a map `f` is the combination `∑ i ∈ s, z i • (π_(k ∘ σ i) ≫ F(σ i))` of projections followed by
restrictions along maps `σ i` of vertices, then the factor indexed by `k` of `f c` is the same
combination `∑ i ∈ s, z i • cechFace k (σ i) c` of restrictions of `c`. This turns the factor
formulas of maps of Čech complexes, proved in a general preadditive category, into formulas for
algebra-valued cochains. -/
theorem cechComponent_eq_sum_of_comp_π_eq {κ : Type*} {m n : ℕ}
    {f : (cechAlgebraComplex U F).X m ⟶ (cechAlgebraComplex U F).X n} {k : Fin (n + 1) → ι}
    {s : Finset κ} {z : κ → ℤ} {σ : κ → Fin (m + 1) → Fin (n + 1)}
    (h : f ≫ Pi.π _ k = ∑ i ∈ s, z i • (Pi.π _ (k ∘ σ i) ≫
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)).map
        (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (σ i x)).op))
    (c : (cechAlgebraComplex U F).X m) :
    cechComponent k (f.hom c) = ∑ i ∈ s, z i • cechFace k (σ i) c := by
  have h := congrArg (fun g ↦ g.hom c) h
  -- `h` is stated for a general preadditive category; `erw` reads its composites, sums and integer
  -- multiples of morphisms as those of `ModuleCat`
  erw [ModuleCat.hom_comp, ModuleCat.hom_sum, LinearMap.sum_apply] at h
  refine h.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  erw [ModuleCat.hom_zsmul, LinearMap.smul_apply, ModuleCat.hom_comp]
  rw [Functor.comp_map, AlgCat.forget₂_module_map]
  -- `ModuleCat.ofHom` and `ModuleCat.Hom.hom` cancel, and the factors of the Čech complex are
  -- indexed by the products `∏ᶜ fun j ↦ U (a j)`
  rfl

/-- The factors of the Čech differential: the factor of `d c` indexed by `k : Fin (n + 2) → ι` is
the alternating sum of the restrictions of `c` along the coface maps `m.succAbove`. -/
theorem cechComponent_d {n : ℕ} (k : Fin (n + 2) → ι) (c : (cechAlgebraComplex U F).X n) :
    cechComponent k (((cechAlgebraComplex U F).d n (n + 1)).hom c) =
      ∑ m : Fin (n + 2), (-1 : ℤ) ^ (m : ℕ) • cechFace k m.succAbove c :=
  cechComponent_eq_sum_of_comp_π_eq
    (cechComplexFunctor_obj_d_comp_π U (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) n k) c

/-- The restrictions of the Čech differential of a cochain are alternating sums of restrictions of
the cochain. -/
theorem cechFace_d {m n : ℕ} (k : Fin (n + 1) → ι) (σ : Fin (m + 2) → Fin (n + 1))
    (c : (cechAlgebraComplex U F).X m) :
    cechFace k σ (((cechAlgebraComplex U F).d m (m + 1)).hom c) =
      ∑ j : Fin (m + 2), (-1 : ℤ) ^ (j : ℕ) • cechFace k (σ ∘ j.succAbove) c := by
  rw [cechFace_apply, cechComponent_d, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_zsmul, map_cechFace]

end Components

section Maps

/-- The factors of the map of Čech complexes `Č(V, F) ⟶ Č(U, F)` induced by a morphism of families
`φ : U ⟶ V`: the factor indexed by `k` is the factor indexed by `φ.f ∘ k`, restricted along the
product of the morphisms `φ.φ (k j)`. -/
@[simp]
theorem cechComponent_cechComplexMap {κ : Type w} {V : κ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) {m : ℕ} (k : Fin (m + 1) → ι)
    (c : (cechAlgebraComplex V F).X m) :
    cechComponent k
        (((cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ).f m).hom c) =
      (F.map (Limits.Pi.map fun j ↦ φ.φ (k j)).op).hom (cechComponent (φ.f ∘ k) c) :=
  congrArg (fun f ↦ f.hom c)
    (cechComplexMap_f_π (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ m k)

/-- The restrictions of the map of Čech complexes induced by a morphism of families `φ : U ⟶ V`
are the restrictions along the product of the morphisms `φ.φ (k j)`. -/
@[simp]
theorem cechFace_cechComplexMap {κ : Type w} {V : κ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) {m l : ℕ} (k : Fin (l + 1) → ι)
    (σ : Fin (m + 1) → Fin (l + 1)) (c : (cechAlgebraComplex V F).X m) :
    cechFace k σ
        (((cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ).f m).hom c) =
      (F.map (Limits.Pi.map fun j ↦ φ.φ (k j)).op).hom (cechFace (φ.f ∘ k) σ c) := by
  have : (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (σ x)) ≫
      Limits.Pi.map (fun j ↦ φ.φ ((k ∘ σ) j)) =
      Limits.Pi.map (fun j ↦ φ.φ (k j)) ≫
        Pi.lift fun x ↦ Pi.π (fun j ↦ V ((φ.f ∘ k) j)) (σ x) :=
    Pi.hom_ext _ _ fun _ ↦ by simp
  rw [cechFace_apply, cechComponent_cechComplexMap, cechFace_apply, ← AlgCat.comp_apply,
    ← AlgCat.comp_apply, ← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, this]
  -- the products `∏ᶜ fun j ↦ U ((k ∘ σ) j)` and `∏ᶜ fun x ↦ U (k (σ x))` are the same object
  rfl

/-- The factors of the map of Čech complexes induced by a morphism of presheaves of algebras
`α : F ⟶ G` are the images of the factors under the components of `α`. -/
@[simp]
theorem cechComponent_cechComplexFunctor_map {G : Cᵒᵖ ⥤ AlgCat.{w} R} (α : F ⟶ G) {m : ℕ}
    (k : Fin (m + 1) → ι) (c : (cechAlgebraComplex U F).X m) :
    cechComponent k ((((cechComplexFunctor U).map
      (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))).f m).hom c) =
      (α.app (op (∏ᶜ fun j ↦ U (k j)))).hom (cechComponent k c) :=
  congrArg (fun f ↦ f.hom c) (cechComplexFunctor_map_f_π U
    (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) m k)

/-- The restrictions of the map of Čech complexes induced by a morphism of presheaves of algebras
`α : F ⟶ G` are the images of the restrictions under the components of `α`. -/
@[simp]
theorem cechFace_cechComplexFunctor_map {G : Cᵒᵖ ⥤ AlgCat.{w} R} (α : F ⟶ G) {m l : ℕ}
    (k : Fin (l + 1) → ι) (σ : Fin (m + 1) → Fin (l + 1)) (c : (cechAlgebraComplex U F).X m) :
    cechFace k σ ((((cechComplexFunctor U).map
      (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))).f m).hom c) =
      (α.app (op (∏ᶜ fun j ↦ U (k j)))).hom (cechFace k σ c) := by
  rw [cechFace_apply, cechComponent_cechComplexFunctor_map, cechFace_apply, ← AlgCat.comp_apply,
    ← AlgCat.comp_apply, α.naturality]
  -- the products `∏ᶜ fun j ↦ U ((k ∘ σ) j)` and `∏ᶜ fun x ↦ U (k (σ x))` are the same object
  rfl

end Maps

/-- Restrictions along maps of vertices with the same values agree. -/
lemma cechFace_eq_of_val {m n : ℕ} {k : Fin (n + 1) → ι} {σ σ' : Fin (m + 1) → Fin (n + 1)}
    (c : (cechAlgebraComplex U F).X m) (h : ∀ i, (σ i : ℕ) = σ' i) :
    cechFace k σ c = cechFace k σ' c := by
  rw [show σ = σ' from funext fun i ↦ Fin.ext (h i)]

section Cup

variable (p q n : ℕ) (h : p + q = n)

/-- The **cup product** of Čech cochains of a presheaf of algebras: for `a` of degree `p` and `b` of
degree `q`, the factor of `a ⌣ b` indexed by `k : Fin (p + q + 1) → ι` is
`a(k 0, …, k p) · b(k p, …, k (p + q))`, the factor of `a` on the front `p`-face and the factor of
`b` on the back `q`-face, both restricted to `U (k 0) × ⋯ × U (k (p + q))`
(`cechComponent_cechCup`). -/
def cechCup : (cechAlgebraComplex U F).X p →ₗ[R] (cechAlgebraComplex U F).X q →ₗ[R]
    (cechAlgebraComplex U F).X n :=
  LinearMap.mk₂ R
    (fun a b ↦ cechOfComponents fun k ↦ cechFace k (Fin.castLE (by omega)) a *
      cechFace k (fun i ↦ Fin.cast (by omega) (Fin.natAdd p i)) b)
    (fun a a' b ↦ cechCochain_ext fun k ↦ by
      simp only [cechComponent_cechOfComponents, map_add, add_mul])
    (fun r a b ↦ cechCochain_ext fun k ↦ by
      simp only [cechComponent_cechOfComponents, map_smul, smul_mul_assoc])
    (fun a b b' ↦ cechCochain_ext fun k ↦ by
      simp only [cechComponent_cechOfComponents, map_add, mul_add])
    (fun r a b ↦ cechCochain_ext fun k ↦ by
      simp only [cechComponent_cechOfComponents, map_smul, mul_smul_comm])

variable {p q n}

/-- The factors of a cup product: the factor of `a` on the front face times the factor of `b` on the
back face. -/
@[simp]
theorem cechComponent_cechCup (k : Fin (n + 1) → ι) (a : (cechAlgebraComplex U F).X p)
    (b : (cechAlgebraComplex U F).X q) :
    cechComponent k (cechCup p q n h a b) =
      cechFace k (Fin.castLE (by omega)) a *
        cechFace k (fun i ↦ Fin.cast (by omega) (Fin.natAdd p i)) b := by
  simp only [cechCup, LinearMap.mk₂_apply, cechComponent_cechOfComponents]

/-- The restrictions of a cup product are the products of the restrictions along the front and back
faces. -/
@[simp]
theorem cechFace_cechCup {m : ℕ} (k : Fin (m + 1) → ι) (σ : Fin (n + 1) → Fin (m + 1))
    (a : (cechAlgebraComplex U F).X p) (b : (cechAlgebraComplex U F).X q) :
    cechFace k σ (cechCup p q n h a b) =
      cechFace k (σ ∘ Fin.castLE (by omega)) a *
        cechFace k (σ ∘ fun i ↦ Fin.cast (by omega) (Fin.natAdd p i)) b := by
  rw [cechFace_apply, cechComponent_cechCup, map_mul, map_cechFace, map_cechFace]

/-- The **Leibniz rule** for the Čech cup product:
`d (a ⌣ b) = d a ⌣ b + (-1) ^ p a ⌣ d b` for a cochain `a` of degree `p`. -/
theorem d_cechCup (a : (cechAlgebraComplex U F).X p) (b : (cechAlgebraComplex U F).X q) :
    ((cechAlgebraComplex U F).d n (n + 1)).hom (cechCup p q n h a b) =
      cechCup (p + 1) q (n + 1) (by omega) (((cechAlgebraComplex U F).d p (p + 1)).hom a) b +
        (-1 : ℤ) ^ p • cechCup p (q + 1) (n + 1) (by omega) a
          (((cechAlgebraComplex U F).d q (q + 1)).hom b) := by
  subst h
  refine cechCochain_ext fun k ↦ ?_
  rw [map_add, map_zsmul, cechComponent_d, cechComponent_cechCup, cechComponent_cechCup,
    cechFace_d, cechFace_d, ← Fin.sum_congr' _ (show p + 1 + (q + 1) = p + q + 2 by omega),
    Fin.sum_univ_add, Fin.sum_univ_castSucc (n := p + 1), Fin.sum_univ_succ (n := q + 1)]
  simp only [cechFace_cechCup]
  -- the faces `j ≤ p` of `a ⌣ b` are the faces of `d a`, the faces `j ≥ p + 1` those of `d b`,
  -- and the last face of `d a` cancels the first face of `d b`
  rw [add_mul, mul_add, smul_add, Finset.sum_mul, Finset.mul_sum, Finset.smul_sum]
  have key {M : Type w} [AddCommGroup M] {P₁ P₂ Q₁ Q₂ X Y : M} (h₁ : P₁ = Q₁) (h₂ : P₂ = Q₂)
      (h : X + Y = 0) : P₁ + P₂ = Q₁ + X + (Y + Q₂) := by
    rw [h₁, h₂, add_assoc Q₁, ← add_assoc X, h, zero_add]
  refine key (Finset.sum_congr rfl fun x _ ↦ ?_)
    (Finset.sum_congr rfl fun x _ ↦ ?_) ?_
  · rw [smul_mul_assoc]
    congr 2 <;> exact cechFace_eq_of_val _ fun i ↦ by grind [Fin.val_succAbove]
  · rw [mul_smul_comm, smul_smul, ← pow_add]
    congr 2
    · simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
      omega
    all_goals exact cechFace_eq_of_val _ fun i ↦ by grind [Fin.val_succAbove]
  · rw [Fin.val_last, Fin.val_zero, pow_zero, one_smul, pow_succ, mul_neg_one, neg_smul]
    simp only [neg_mul, smul_mul_assoc, neg_add_eq_zero]
    congr 2 <;> exact cechFace_eq_of_val _ fun i ↦ by grind [Fin.val_succAbove]

/-- The cup product of two cocycles is a cocycle. -/
theorem d_cechCup_eq_zero {a : (cechAlgebraComplex U F).X p} {b : (cechAlgebraComplex U F).X q}
    (ha : ((cechAlgebraComplex U F).d p (p + 1)).hom a = 0)
    (hb : ((cechAlgebraComplex U F).d q (q + 1)).hom b = 0) :
    ((cechAlgebraComplex U F).d n (n + 1)).hom (cechCup p q n h a b) = 0 := by
  rw [d_cechCup, ha, hb, map_zero, map_zero, LinearMap.zero_apply, smul_zero, add_zero]

/-- A coboundary times a cocycle is a coboundary: `d x ⌣ b = d (x ⌣ b)` when `d b = 0`. -/
theorem cechCup_d_left (x : (cechAlgebraComplex U F).X p) {b : (cechAlgebraComplex U F).X q}
    (hb : ((cechAlgebraComplex U F).d q (q + 1)).hom b = 0) :
    cechCup (p + 1) q (n + 1) (by omega) (((cechAlgebraComplex U F).d p (p + 1)).hom x) b =
      ((cechAlgebraComplex U F).d n (n + 1)).hom (cechCup p q n h x b) := by
  rw [d_cechCup, hb, map_zero, smul_zero, add_zero]

/-- A cocycle times a coboundary is a coboundary: `a ⌣ d y = (-1) ^ p d (a ⌣ y)` when `d a = 0`
and `a` has degree `p`. -/
theorem cechCup_d_right {a : (cechAlgebraComplex U F).X p} (y : (cechAlgebraComplex U F).X q)
    (ha : ((cechAlgebraComplex U F).d p (p + 1)).hom a = 0) :
    cechCup p (q + 1) (n + 1) (by omega) a (((cechAlgebraComplex U F).d q (q + 1)).hom y) =
      (-1 : ℤ) ^ p • ((cechAlgebraComplex U F).d n (n + 1)).hom (cechCup p q n h a y) := by
  rw [d_cechCup, ha, map_zero, LinearMap.zero_apply, zero_add, smul_smul, ← pow_add, ← two_mul,
    pow_mul, neg_one_sq, one_pow, one_smul]

/-- **Associativity** of the Čech cup product, at the level of cochains. -/
theorem cechCup_assoc {r m l : ℕ} (h₁ : p + q = m) (h₂ : m + r = n) (h₃ : q + r = l)
    (h₄ : p + l = n) (a : (cechAlgebraComplex U F).X p) (b : (cechAlgebraComplex U F).X q)
    (c : (cechAlgebraComplex U F).X r) :
    cechCup m r n h₂ (cechCup p q m h₁ a b) c = cechCup p l n h₄ a (cechCup q r l h₃ b c) := by
  refine cechCochain_ext fun k ↦ ?_
  rw [cechComponent_cechCup, cechComponent_cechCup, cechFace_cechCup, cechFace_cechCup, mul_assoc]
  exact congrArg₂ (· * ·) (cechFace_eq_of_val _ fun i ↦ by grind) <|
    congrArg₂ (· * ·) (cechFace_eq_of_val _ fun i ↦ by grind)
      (cechFace_eq_of_val _ fun i ↦ by grind)

variable (U F) in
/-- The **unit cochain**: the Čech `0`-cochain all of whose factors are `1`. -/
def cechOne : (cechAlgebraComplex U F).X 0 :=
  cechOfComponents fun _ ↦ 1

/-- Every factor of the unit cochain is `1`. -/
@[simp]
theorem cechComponent_cechOne (a : Fin 1 → ι) : cechComponent a (cechOne U F) = 1 :=
  cechComponent_cechOfComponents _ a

/-- Every restriction of the unit cochain is `1`. -/
@[simp]
theorem cechFace_cechOne {m : ℕ} (k : Fin (m + 1) → ι) (σ : Fin 1 → Fin (m + 1)) :
    cechFace k σ (cechOne U F) = 1 := by
  rw [cechFace_apply, cechComponent_cechOne, map_one]

/-- The unit cochain is a cocycle. -/
@[simp]
theorem d_cechOne : ((cechAlgebraComplex U F).d 0 1).hom (cechOne U F) = 0 :=
  cechCochain_ext fun k ↦ by simp [cechComponent_d, Fin.sum_univ_two]

/-- The unit cochain is a left unit for the cup product. -/
@[simp]
theorem cechOne_cechCup (b : (cechAlgebraComplex U F).X q) :
    cechCup 0 q q (zero_add q) (cechOne U F) b = b := by
  refine cechCochain_ext fun k ↦ ?_
  rw [cechComponent_cechCup, cechFace_cechOne, one_mul, ← cechFace_id]
  exact cechFace_eq_of_val _ fun i ↦ by simp

/-- The unit cochain is a right unit for the cup product. -/
@[simp]
theorem cechCup_cechOne (a : (cechAlgebraComplex U F).X p) :
    cechCup p 0 p (add_zero p) a (cechOne U F) = a := by
  refine cechCochain_ext fun k ↦ ?_
  rw [cechComponent_cechCup, cechFace_cechOne, mul_one, ← cechFace_id]
  exact cechFace_eq_of_val _ fun i ↦ by simp

section Naturality

/-- **Naturality under refinement.** The map of Čech complexes `Č(V, F) ⟶ Č(U, F)` induced by a
morphism of families `φ : U ⟶ V`, such as a refinement of open covers, preserves cup products. -/
theorem cechComplexMap_cechCup {κ : Type w} {V : κ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) (a : (cechAlgebraComplex V F).X p)
    (b : (cechAlgebraComplex V F).X q) :
    ((cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ).f n).hom
        (cechCup p q n h a b) =
      cechCup p q n h ((cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ).f p a)
        ((cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ).f q b) := by
  refine cechCochain_ext fun k ↦ ?_
  rw [cechComponent_cechComplexMap, cechComponent_cechCup, cechComponent_cechCup, map_mul,
    cechFace_cechComplexMap, cechFace_cechComplexMap]

/-- **Naturality in the coefficients.** A morphism of presheaves of algebras `α : F ⟶ G` induces a
map of Čech complexes preserving cup products. -/
theorem cechComplexFunctor_map_cechCup {G : Cᵒᵖ ⥤ AlgCat.{w} R} (α : F ⟶ G)
    (a : (cechAlgebraComplex U F).X p) (b : (cechAlgebraComplex U F).X q) :
    (((cechComplexFunctor U).map
      (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))).f n).hom
        (cechCup p q n h a b) =
      cechCup p q n h (((cechComplexFunctor U).map
          (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))).f p a)
        (((cechComplexFunctor U).map
          (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))).f q b) := by
  refine cechCochain_ext fun k ↦ ?_
  rw [cechComponent_cechComplexFunctor_map, cechComponent_cechCup, cechComponent_cechCup,
    map_mul, cechFace_cechComplexFunctor_map, cechFace_cechComplexFunctor_map]

/-- The map of Čech complexes induced by a morphism of families, such as a refinement of open
covers, preserves the unit cochain. -/
@[simp]
theorem cechComplexMap_cechOne {κ : Type w} {V : κ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    ((cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ).f 0).hom (cechOne V F) =
      cechOne U F :=
  cechCochain_ext fun k ↦ by simp

/-- The map of Čech complexes induced by a morphism of presheaves of algebras preserves the unit
cochain. -/
@[simp]
theorem cechComplexFunctor_map_cechOne {G : Cᵒᵖ ⥤ AlgCat.{w} R} (α : F ⟶ G) :
    (((cechComplexFunctor U).map
      (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))).f 0).hom (cechOne U F) =
      cechOne U G :=
  cechCochain_ext fun k ↦ by simp

end Naturality

section Comparison

variable {D : Type*} [Category D] [HasFiniteProducts D] (G : C ⥤ D) {Q : Dᵒᵖ ⥤ AlgCat.{w} R}
  (hG : ∀ (n : ℕ) (a : Fin (n + 1) → ι), IsIso (piComparison G fun j ↦ U (a j)))

/-- The factors of the comparison `Č(G ∘ U, Q) ≅ Č(U, G.op ⋙ Q)` of Čech complexes along a functor
`G` preserving the products of members: the factor indexed by `k` is the image of the factor of
the same index under `Q` applied to the comparison map
`G(U (k 0) × ⋯ × U (k m)) ⟶ G (U (k 0)) × ⋯ × G (U (k m))`. -/
@[simp]
theorem cechComponent_cechComplexCompIso_hom {m : ℕ} (k : Fin (m + 1) → ι)
    (c : (cechAlgebraComplex (fun i ↦ G.obj (U i)) Q).X m) :
    cechComponent (F := G.op ⋙ Q) k
        (((cechComplexCompIso G U (Q ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) hG).hom.f m).hom
          c) =
      (Q.map (piComparison G fun j ↦ U (k j)).op).hom (cechComponent k c) :=
  congrArg (fun f ↦ f.hom c)
    (cechComplexCompIso_hom_f_π G U (Q ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) hG m k)

/-- The restrictions of the comparison `Č(G ∘ U, Q) ≅ Č(U, G.op ⋙ Q)` are the images of the
restrictions under `Q` applied to the comparison maps of products. -/
@[simp]
theorem cechFace_cechComplexCompIso_hom {m l : ℕ} (k : Fin (l + 1) → ι)
    (σ : Fin (m + 1) → Fin (l + 1)) (c : (cechAlgebraComplex (fun i ↦ G.obj (U i)) Q).X m) :
    cechFace (F := G.op ⋙ Q) k σ
        (((cechComplexCompIso G U (Q ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) hG).hom.f m).hom
          c) =
      (Q.map (piComparison G fun j ↦ U (k j)).op).hom (cechFace k σ c) := by
  have : piComparison G (fun j ↦ U (k j)) ≫
      (Pi.lift fun x ↦ Pi.π (fun j ↦ G.obj (U (k j))) (σ x)) =
      G.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (σ x)) ≫
        piComparison G fun j ↦ U ((k ∘ σ) j) :=
    Pi.hom_ext _ _ fun _ ↦ by simp
  rw [cechFace_apply, cechComponent_cechComplexCompIso_hom, cechFace_apply, Functor.comp_map,
    Functor.op_map, Quiver.Hom.unop_op, ← AlgCat.comp_apply, ← AlgCat.comp_apply, ← Q.map_comp,
    ← Q.map_comp, ← op_comp, ← op_comp, this]

/-- The comparison `Č(G ∘ U, Q) ≅ Č(U, G.op ⋙ Q)` of Čech complexes along a functor `G` preserving
the products of members preserves cup products. -/
theorem cechComplexCompIso_hom_cechCup
    (a : (cechAlgebraComplex (fun i ↦ G.obj (U i)) Q).X p)
    (b : (cechAlgebraComplex (fun i ↦ G.obj (U i)) Q).X q) :
    ((cechComplexCompIso G U (Q ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) hG).hom.f n).hom
        (cechCup p q n h a b) =
      cechCup (U := U) (F := G.op ⋙ Q) p q n h
        (((cechComplexCompIso G U (Q ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) hG).hom.f p).hom
          a)
        (((cechComplexCompIso G U (Q ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) hG).hom.f q).hom
          b) := by
  refine cechCochain_ext (U := U) (F := G.op ⋙ Q) fun k ↦ ?_
  rw [cechComponent_cechComplexCompIso_hom, cechComponent_cechCup, cechComponent_cechCup, map_mul,
    cechFace_cechComplexCompIso_hom, cechFace_cechComplexCompIso_hom]

/-- The inverse comparison `Č(U, G.op ⋙ Q) ≅ Č(G ∘ U, Q)` preserves cup products. -/
theorem cechComplexCompIso_inv_cechCup (a : (cechAlgebraComplex U (G.op ⋙ Q)).X p)
    (b : (cechAlgebraComplex U (G.op ⋙ Q)).X q) :
    ((cechComplexCompIso G U (Q ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) hG).inv.f n).hom
        (cechCup p q n h a b) =
      cechCup p q n h
        (((cechComplexCompIso G U (Q ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) hG).inv.f p).hom
          a)
        (((cechComplexCompIso G U (Q ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) hG).inv.f q).hom
          b) := by
  let e := cechComplexCompIso G U (Q ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) hG
  have he (m : ℕ) (x) : (e.hom.f m).hom ((e.inv.f m).hom x) = x :=
    (HomologicalComplex.Hom.isoApp e m).inv_hom_id_apply x
  have he' (x) : (e.inv.f n).hom ((e.hom.f n).hom x) = x :=
    (HomologicalComplex.Hom.isoApp e n).hom_inv_id_apply x
  refine (Function.LeftInverse.injective he') ?_
  rw [he, cechComplexCompIso_hom_cechCup, he, he]

/-- The comparison `Č(G ∘ U, Q) ≅ Č(U, G.op ⋙ Q)` of Čech complexes preserves the unit cochain. -/
@[simp]
theorem cechComplexCompIso_hom_cechOne :
    ((cechComplexCompIso G U (Q ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) hG).hom.f 0).hom
        (cechOne (fun i ↦ G.obj (U i)) Q) =
      cechOne U (G.op ⋙ Q) :=
  cechCochain_ext (U := U) (F := G.op ⋙ Q) fun k ↦ by
    rw [cechComponent_cechComplexCompIso_hom, cechComponent_cechOne, cechComponent_cechOne,
      map_one]

/-- The inverse comparison `Č(U, G.op ⋙ Q) ≅ Č(G ∘ U, Q)` preserves the unit cochain. -/
@[simp]
theorem cechComplexCompIso_inv_cechOne :
    ((cechComplexCompIso G U (Q ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) hG).inv.f 0).hom
        (cechOne U (G.op ⋙ Q)) =
      cechOne (fun i ↦ G.obj (U i)) Q := by
  rw [← cechComplexCompIso_hom_cechOne G hG]
  exact (HomologicalComplex.Hom.isoApp _ 0).hom_inv_id_apply _

end Comparison

end Cup

end TauCeti.CategoryTheory

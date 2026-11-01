/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Monad.Coequalizer

/-!
# The canonical polynomial presentation of a commutative algebra

The free commutative `R`-algebra on a set is its multivariable polynomial ring.
The free-forgetful adjunction gives the polynomial comonad `P(B) = R[B]`,
with counit evaluating variables and comultiplication taking `X b` to `X (X b)`.

Every commutative `R`-algebra `B` is the coequalizer of the two canonical maps
`P(P(B)) ⇉ P(B)`: evaluation of the outer variables and renaming by evaluation
of the inner polynomials. After forgetting to sets this is a split coequalizer,
with sections `b ↦ X b` and `p ↦ X p`. This is the augmented first stage of the
standard simplicial polynomial resolution. The difference of the two faces has image
exactly the augmentation kernel, giving exactness at `R[B]` of its underlying module complex.

## References

* The Stacks Project, Definition 92.3.1 (Tag 08PM), the standard polynomial resolution.
* The free functor and adjunction follow the construction of `CommRingCat.free` and
  `CommRingCat.adj` by Kim Morrison, Johannes Hölzl and Andrew Yang, with coefficients in `R`.
  The comonad and the underlying split coequalizer use Mathlib's
  `Adjunction.toComonad` and `Monad.beckSplitCoequalizer`.
-/

public noncomputable section

open CategoryTheory Limits MvPolynomial

universe u v

namespace CommAlgCat

variable (R : Type u) [CommRing R]

/-- The free commutative `R`-algebra functor, with variables in `Type (max u v)`.
The body is exposed so its elements can be used as multivariable polynomials. -/
@[expose] def free : Type (max u v) ⥤ CommAlgCat.{max u v} R where
  obj X := of R (MvPolynomial X R)
  map f := ofHom (rename f)
  map_id X := by
    apply hom_ext
    exact MvPolynomial.rename_id
  map_comp f g := by
    apply hom_ext
    exact (MvPolynomial.rename_comp_rename f g).symm

/-- The free algebra has the multivariable polynomial ring as its carrier. -/
@[simp]
lemma free_obj (X : Type (max u v)) :
    (free R).obj X = of R (MvPolynomial X R) := (rfl)

/-- A map of variable sets acts by renaming polynomials. -/
@[simp]
lemma free_map_hom {X Y : Type (max u v)} (f : X ⟶ Y) :
    ((free R).map f).hom = rename f := (rfl)

/-- The free-polynomial / underlying-set adjunction. Its unit inserts variables and its
counit evaluates them in the algebra. -/
def freeForgetAdjunction : free R ⊣ forget (CommAlgCat.{max u v} R) where
  unit :=
    { app X := ↾(MvPolynomial.X : X → MvPolynomial X R)
      naturality X Y f := by ext x; simp [free] }
  counit :=
    { app B := ofHom (aeval (id : B → B))
      naturality B C f := by
        apply hom_ext
        apply MvPolynomial.algHom_ext
        intro b
        dsimp [free]
        simp }
  left_triangle_components S := by
    apply hom_ext
    -- Normalize the ring instances carried by `free.obj S` to those of `MvPolynomial S R`.
    change (aeval (id : MvPolynomial S R → MvPolynomial S R)).comp
      (rename (MvPolynomial.X : S → MvPolynomial S R)) = AlgHom.id R _
    apply MvPolynomial.algHom_ext
    intro x
    simp
  right_triangle_components B := by
    ext b
    exact MvPolynomial.aeval_X (id : B → B) b

/-- The adjunction unit sends an element to the variable indexed by it. -/
@[simp]
lemma freeForgetAdjunction_unit_app (X : Type (max u v)) :
    (freeForgetAdjunction R).unit.app X = ↾(MvPolynomial.X : X → MvPolynomial X R) := (rfl)

/-- The adjunction counit is evaluation at the elements indexing the variables. -/
@[simp]
lemma freeForgetAdjunction_counit_app_hom (B : CommAlgCat.{max u v} R) :
    ((freeForgetAdjunction R).counit.app B).hom = aeval (id : B → B) := (rfl)

/-- The polynomial comonad `P(B) = R[B]` of the free-forgetful adjunction.
The body is exposed so iterating it gives the corresponding iterated polynomial rings. -/
@[expose] def polynomialComonad : Comonad (CommAlgCat.{max u v} R) :=
  (freeForgetAdjunction R).toComonad

/-- On objects, the polynomial comonad forms the polynomial ring on all elements. -/
@[simp]
lemma polynomialComonad_obj (B : CommAlgCat.{max u v} R) :
    (polynomialComonad R).obj B = of R (MvPolynomial B R) := (rfl)

/-- On morphisms, the polynomial comonad renames variables by the algebra map. -/
@[simp]
lemma polynomialComonad_map_hom {B C : CommAlgCat.{max u v} R} (f : B ⟶ C) :
    ((polynomialComonad R).map f).hom = rename f := (rfl)

/-- The polynomial comonad counit evaluates variables. -/
@[simp]
lemma polynomialComonad_ε_app_hom (B : CommAlgCat.{max u v} R) :
    ((polynomialComonad R).ε.app B).hom = aeval (id : B → B) := (rfl)

/-- The polynomial comonad comultiplication replaces `X b` with `X (X b)`. -/
@[simp]
lemma polynomialComonad_δ_app_hom (B : CommAlgCat.{max u v} R) :
    ((polynomialComonad R).δ.app B).hom =
      rename (MvPolynomial.X : B → MvPolynomial B R) := (rfl)

variable {R} (B : CommAlgCat.{max u v} R)

/-- The canonical cofork `R[R[B]] ⇉ R[B] → B`: the first arrow renames each polynomial
variable by its value in `B`, and the second evaluates the polynomial variables in `R[B]`.
The body is exposed so the cofork point is definitionally `B`. -/
@[expose] def polynomialPresentation :
    Cofork (ofHom (rename (R := R) (aeval (id : B → B))))
      (ofHom (aeval (R := R) (id : MvPolynomial B R → MvPolynomial B R))) :=
  Cofork.ofπ (ofHom (aeval (id : B → B))) (by
    apply hom_ext
    apply MvPolynomial.algHom_ext
    intro p
    simp)

/-- The augmentation in the canonical polynomial presentation is evaluation. -/
@[simp]
lemma polynomialPresentation_π_hom :
    B.polynomialPresentation.π.hom = aeval (id : B → B) := (rfl)

/-- The canonical polynomial presentation is split after forgetting to sets. The two
sections insert a variable at their respective levels. -/
def polynomialPresentationSplit :
    IsSplitCoequalizer
      ((forget (CommAlgCat.{max u v} R)).map
        (ofHom (rename (R := R) (aeval (id : B → B)))))
      ((forget (CommAlgCat.{max u v} R)).map
        (ofHom (aeval (R := R) (id : MvPolynomial B R → MvPolynomial B R))))
      ((forget (CommAlgCat.{max u v} R)).map B.polynomialPresentation.π) := by
  -- Normalize the explicit polynomial maps to the maps in the Beck diagram.
  exact Monad.beckSplitCoequalizer ((Monad.comparison (freeForgetAdjunction R)).obj B)

/-- The first splitting inserts variables indexed by elements of `B`. -/
@[simp]
lemma polynomialPresentationSplit_rightSection (b : B) :
    B.polynomialPresentationSplit.rightSection b = MvPolynomial.X b := (rfl)

/-- The second splitting inserts variables indexed by polynomials. -/
@[simp]
lemma polynomialPresentationSplit_leftSection (p : MvPolynomial B R) :
    B.polynomialPresentationSplit.leftSection p = MvPolynomial.X p := (rfl)

/-- The canonical polynomial cofork is a coequalizer in commutative `R`-algebras. -/
def polynomialPresentationIsColimit : IsColimit B.polynomialPresentation := by
  refine Cofork.IsColimit.mk' _ fun s ↦ ?_
  let q : MvPolynomial B R →ₐ[R] s.pt := s.π.hom
  have hs : q.comp (rename (aeval (id : B → B))) =
      q.comp (aeval (id : MvPolynomial B R → MvPolynomial B R)) :=
    congrArg Hom.hom s.condition
  have h (p : MvPolynomial B R) :
      q (MvPolynomial.X (aeval (id : B → B) p)) = q p := by
    simpa using DFunLike.congr_fun hs (MvPolynomial.X p)
  have hf : Function.Surjective (aeval (R := R) (id : B → B)) :=
    fun b ↦ ⟨MvPolynomial.X b, by simp⟩
  have hk : RingHom.ker (aeval (R := R) (id : B → B)).toRingHom ≤
      RingHom.ker q.toRingHom := by
    intro p hp
    rw [RingHom.mem_ker] at hp ⊢
    have h0 : q (MvPolynomial.X (0 : B)) = 0 := by simpa using h 0
    have hp' : aeval (id : B → B) p = 0 := hp
    exact (h p).symm.trans (by simpa only [hp'] using h0)
  let f := AlgHom.liftOfSurjective (aeval (id : B → B)) hf q hk
  refine ⟨ofHom f, ?_, ?_⟩
  · exact hom_ext (AlgHom.liftOfSurjective_comp _ hf q hk)
  · intro g hg
    apply hom_ext
    apply AlgHom.ext
    intro b
    obtain ⟨p, rfl⟩ := hf b
    have hgb : g.hom (aeval (id : B → B) p) = q p := congr($(hg).hom p)
    exact hgb.trans (AlgHom.liftOfSurjective_apply _ hf q hk p).symm

/-- The difference of the two face maps has image exactly the kernel of the augmentation.
Thus the augmented polynomial complex is exact at `R[B]`, as an `R`-module complex. -/
theorem polynomialPresentation_exact :
    Function.Exact
      ((aeval (R := R) (id : MvPolynomial B R → MvPolynomial B R)).toLinearMap -
        (rename (R := R) (aeval (R := R) (id : B → B))).toLinearMap)
      (aeval (R := R) (id : B → B)).toLinearMap := by
  apply LinearMap.exact_of_comp_of_mem_range
  · apply LinearMap.ext
    intro p
    have h : aeval (id : B → B) (rename (aeval (id : B → B)) p) =
        aeval (id : B → B) (aeval (id : MvPolynomial B R → MvPolynomial B R) p) :=
      congr($(B.polynomialPresentation.condition).hom p)
    simpa using sub_eq_zero.mpr h.symm
  · intro p hp
    refine ⟨MvPolynomial.X p - MvPolynomial.X (0 : MvPolynomial B R), ?_⟩
    have hp' : aeval (R := R) (id : B → B) p = 0 := hp
    simp [hp']

end CommAlgCat

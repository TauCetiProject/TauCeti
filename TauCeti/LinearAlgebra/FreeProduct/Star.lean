/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FreeProduct.Basic
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Algebra.Opposite

/-!
# The involution on an algebraic free product

The algebraic free product of unital star algebras is itself a star algebra: its involution
extends those of the factors, conjugates scalars, and reverses the order of products.
`LinearAlgebra.FreeProduct.ιStar` and `LinearAlgebra.FreeProduct.liftStar` express its
universal property for unital star algebra homomorphisms,
`LinearAlgebra.FreeProduct.iSup_range_ιStar` records that the factor images generate the free
product as a star subalgebra, and `LinearAlgebra.FreeProduct.isEmptyStarAlgEquiv` identifies the
empty star free product with `R`. Functoriality in the factors
(`LinearAlgebra.FreeProduct.mapStar`, `LinearAlgebra.FreeProduct.mapStarEquiv`), index relabeling
(`LinearAlgebra.FreeProduct.reindexStarHom`, `LinearAlgebra.FreeProduct.reindexStarAlgEquiv`), and
grouping of factors over sigma types or map fibers (`LinearAlgebra.FreeProduct.sigmaStarAlgEquiv`,
`LinearAlgebra.FreeProduct.fiberStarAlgEquiv`) follow directly from `liftStar`. Forgetting star
recovers Mathlib's algebraic coproduct and its universal maps, not a different quotient.

This is an algebraic construction. No positivity, norm, completion or faithfulness of the
factor maps is asserted. The index type can be empty.

## References

* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, §1.4.

The construction uses Mathlib's `LinearAlgebra.FreeProduct.lift`, applied to the opposite
algebra with its scalar action twisted by conjugation.
-/

public section

noncomputable section

namespace LinearAlgebra.FreeProduct

open MulOpposite

variable {I : Type*} [DecidableEq I] (R : Type*) [CommSemiring R] [StarRing R]
  (A : I → Type*) [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]
  [∀ i, StarRing (A i)] [∀ i, StarModule R (A i)]

/-- The conjugate-linear antihomomorphism, before proving involutivity. -/
private def starAux : FreeProduct R A →+* (FreeProduct R A)ᵐᵒᵖ := by
  letI := Algebra.compHom (FreeProduct R A)ᵐᵒᵖ (starRingEnd R)
  exact (lift R A fun {i} =>
    { toRingHom := (RingHom.op (ι R A i).toRingHom).comp
        (starRingEquiv : A i ≃+* (A i)ᵐᵒᵖ).toRingHom
      commutes' r := by
        simp [Algebra.compHom_algebraMap_apply, starRingEnd_apply,
          ← algebraMap_star_comm] }).toRingHom

private theorem starAux_ι (i : I) (a : A i) :
    starAux R A (ι R A i a) = op (ι R A i (star a)) := by
  let := Algebra.compHom (FreeProduct R A)ᵐᵒᵖ (starRingEnd R)
  exact lift_ι_apply R A _ i a

private theorem starAux_algebraMap (r : R) :
    starAux R A (algebraMap R _ r) = op (algebraMap R _ (star r)) := by
  let := Algebra.compHom (FreeProduct R A)ᵐᵒᵖ (starRingEnd R)
  exact (lift R A _).commutes r

private theorem starAux_involutive (x : FreeProduct R A) :
    unop (starAux R A (unop (starAux R A x))) = x := by
  let f : FreeProduct R A →ₐ[R] FreeProduct R A :=
    { toFun x := unop (starAux R A (unop (starAux R A x)))
      map_one' := by simp
      map_mul' x y := by simp
      map_zero' := by simp
      map_add' x y := by simp
      commutes' r := by simp [starAux_algebraMap] }
  have hf : f = AlgHom.id R (FreeProduct R A) :=
    algHom_ext fun i a ↦ by simp [f, starAux_ι]
  exact AlgHom.congr_fun hf x

/-- The involution extending the factor involutions to the algebraic free product. -/
@[no_expose]
instance instStarRing : StarRing (FreeProduct R A) where
  star x := unop (starAux R A x)
  star_involutive := starAux_involutive R A
  star_mul x y := by simp
  star_add x y := by simp

private theorem star_algebraMap (r : R) :
    star (algebraMap R (FreeProduct R A) r) = algebraMap R _ (star r) :=
  congrArg unop (starAux_algebraMap R A r)

/-- The free-product involution conjugates scalars. -/
instance instStarModule : StarModule R (FreeProduct R A) where
  star_smul r x := by
    rw [Algebra.smul_def, Algebra.smul_def, star_mul, star_algebraMap]
    exact (Algebra.commutes (star r) (star x)).symm

/-- The involution on the free product restricts to the given involution on each factor. -/
@[simp]
theorem star_ι (i : I) (a : A i) : star (ι R A i a) = ι R A i (star a) :=
  congrArg unop (starAux_ι R A i a)

/-- The canonical map from a factor, as a unital star algebra homomorphism. -/
def ιStar (i : I) : A i →⋆ₐ[R] FreeProduct R A :=
  { ι R A i with map_star' a := (star_ι R A i a).symm }

@[simp]
theorem ιStar_toAlgHom (i : I) : (ιStar R A i).toAlgHom = ι R A i := (rfl)

@[simp]
theorem ιStar_apply (i : I) (a : A i) : ιStar R A i a = ι R A i a := (rfl)

variable {R A} {B : Type*} [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

/-- An algebra homomorphism out of the free product preserves star if it does so on every
factor. -/
theorem _root_.AlgHom.map_star_of_comp_freeProduct_ι (f : FreeProduct R A →ₐ[R] B)
    (hf : ∀ i a, f (ι R A i (star a)) = star (f (ι R A i a))) (x : FreeProduct R A) :
    f (star x) = star (f x) := by
  let g : FreeProduct R A →ₐ[R] B :=
    { toFun x := star (f (star x))
      map_one' := by simp
      map_mul' x y := by simp
      map_zero' := by simp
      map_add' x y := by simp
      commutes' r := by simp [← algebraMap_star_comm] }
  have hg : g = f :=
    algHom_ext fun i a ↦ by simp [g, hf]
  have := AlgHom.congr_fun hg x
  simpa [g] using congrArg star this

/-- The algebraic free product is also the coproduct of unital star algebras. -/
def liftStar : ({i : I} → A i →⋆ₐ[R] B) ≃ (FreeProduct R A →⋆ₐ[R] B) where
  toFun maps :=
    { lift R A (fun {i} => (maps (i := i)).toAlgHom) with
      map_star' x := AlgHom.map_star_of_comp_freeProduct_ι _
        (fun i a => by simp [map_star (maps (i := i))]) x }
  invFun f := fun {i} => f.comp (ιStar R A i)
  left_inv maps := by
    funext i
    apply StarAlgHom.ext
    intro a
    exact lift_ι_apply R A _ i a
  right_inv f := by
    apply StarAlgHom.ext
    intro x
    exact AlgHom.congr_fun ((lift R A).apply_symm_apply f.toAlgHom) x

@[simp]
theorem liftStar_toAlgHom (maps : {i : I} → A i →⋆ₐ[R] B) :
    (liftStar maps).toAlgHom = lift R A (fun {i} => (maps (i := i)).toAlgHom) := (rfl)

/-- The inverse of the universal equivalence restricts a map to a factor. -/
@[simp]
theorem liftStar_symm_apply (i : I) (f : FreeProduct R A →⋆ₐ[R] B) :
    liftStar.symm f = f.comp (ιStar R A i) := (rfl)

/-- The star-universal map extends the prescribed homomorphism on each factor. -/
@[simp]
theorem liftStar_ι (maps : {i : I} → A i →⋆ₐ[R] B) (i : I) (a : A i) :
    liftStar maps (ι R A i a) = maps a :=
  lift_ι_apply R A _ i a

/-- Star algebra homomorphisms out of a free product are determined on its factors. -/
@[ext]
theorem starAlgHom_ext {f g : FreeProduct R A →⋆ₐ[R] B}
    (h : ∀ i a, f (ι R A i a) = g (ι R A i a)) : f = g := by
  apply liftStar.symm.injective
  funext i
  exact StarAlgHom.ext (h i)

/-- Composing the star-universal map with a factor map recovers the given map. -/
@[simp]
theorem liftStar_comp_ιStar (maps : {i : I} → A i →⋆ₐ[R] B) (i : I) :
    (liftStar maps).comp (ιStar R A i) = maps := by
  ext a
  simp

/-- The universal map for the canonical factor maps is the identity. -/
@[simp]
theorem liftStar_ιStar :
    liftStar (fun {i} => ιStar R A i) = StarAlgHom.id R (FreeProduct R A) := by
  ext i a
  simp

/-- Postcomposition of universal maps agrees with postcomposition on each factor. -/
@[simp]
theorem liftStar_comp {C : Type*} [Semiring C] [Algebra R C] [StarRing C] [StarModule R C]
    (maps : {i : I} → A i →⋆ₐ[R] B) (g : B →⋆ₐ[R] C) :
    liftStar (fun {i} => g.comp (maps (i := i))) = g.comp (liftStar maps) := by
  ext i a
  simp

section GenerationAndEmpty

variable (R A)

/-- The star-subalgebra images of the factor embeddings generate `FreeProduct R A`. -/
theorem iSup_range_ιStar :
    (⨆ i, (ιStar R A i).range) = (⊤ : StarSubalgebra R (FreeProduct R A)) := by
  rw [← StarSubalgebra.toSubalgebra_eq_top, eq_top_iff, ← iSup_range_ι R A, iSup_le_iff]
  rintro i _ ⟨a, rfl⟩
  exact le_iSup (fun j ↦ (ιStar R A j).range) i ⟨a, rfl⟩

/-- The unital star-algebraic free product over an empty index type is canonically star-isomorphic
to the base star semiring `R`. -/
def isEmptyStarAlgEquiv [IsEmpty I] : FreeProduct R A ≃⋆ₐ[R] R :=
  StarAlgEquiv.ofStarAlgHom
    (liftStar fun {i} ↦ isEmptyElim i)
    (StarAlgHom.ofId R (FreeProduct R A))
    (starAlgHom_ext fun i ↦ isEmptyElim i)
    (StarAlgHom.ext fun r ↦ AlgHomClass.commutes (liftStar (R := R) (A := A) fun {i} ↦
      isEmptyElim i) r)

@[simp]
theorem isEmptyStarAlgEquiv_toAlgEquiv [IsEmpty I] :
    (isEmptyStarAlgEquiv R A).toAlgEquiv = isEmptyAlgEquiv R A :=
  AlgEquiv.ext fun x ↦ AlgHom.congr_fun
    (algHom_ext (f := (isEmptyStarAlgEquiv R A).toAlgEquiv.toAlgHom)
      (g := (isEmptyAlgEquiv R A).toAlgHom) fun i ↦ isEmptyElim i) x

@[simp]
theorem isEmptyStarAlgEquiv_symm_apply [IsEmpty I] (r : R) :
    (isEmptyStarAlgEquiv R A).symm r = algebraMap R (FreeProduct R A) r :=
  (rfl)

end GenerationAndEmpty

section Combinators

/-- Functoriality of the algebraic star free product in the factor algebras. -/
def mapStar {A' : I → Type*} [∀ i, Semiring (A' i)] [∀ i, Algebra R (A' i)]
    [∀ i, StarRing (A' i)] [∀ i, StarModule R (A' i)]
    (f : ∀ i, A i →⋆ₐ[R] A' i) : FreeProduct R A →⋆ₐ[R] FreeProduct R A' :=
  liftStar fun {i} ↦ (ιStar R A' i).comp (f i)

@[simp]
theorem mapStar_ι {A' : I → Type*} [∀ i, Semiring (A' i)] [∀ i, Algebra R (A' i)]
    [∀ i, StarRing (A' i)] [∀ i, StarModule R (A' i)]
    (f : ∀ i, A i →⋆ₐ[R] A' i) (i : I) (a : A i) :
    mapStar f (ι R A i a) = ι R A' i (f i a) :=
  liftStar_ι _ i a

@[simp]
theorem mapStar_comp_ιStar {A' : I → Type*} [∀ i, Semiring (A' i)] [∀ i, Algebra R (A' i)]
    [∀ i, StarRing (A' i)] [∀ i, StarModule R (A' i)]
    (f : ∀ i, A i →⋆ₐ[R] A' i) (i : I) :
    (mapStar f).comp (ιStar R A i) = (ιStar R A' i).comp (f i) :=
  liftStar_comp_ιStar _ i

@[simp]
theorem mapStar_id :
    mapStar (fun i ↦ StarAlgHom.id R (A i)) = StarAlgHom.id R (FreeProduct R A) := by
  ext i a
  simp

theorem mapStar_comp {A' A'' : I → Type*}
    [∀ i, Semiring (A' i)] [∀ i, Algebra R (A' i)] [∀ i, StarRing (A' i)] [∀ i, StarModule R (A' i)]
    [∀ i, Semiring (A'' i)] [∀ i, Algebra R (A'' i)] [∀ i, StarRing (A'' i)]
    [∀ i, StarModule R (A'' i)]
    (g : ∀ i, A' i →⋆ₐ[R] A'' i) (f : ∀ i, A i →⋆ₐ[R] A' i) :
    mapStar (fun i ↦ (g i).comp (f i)) = (mapStar g).comp (mapStar f) := by
  ext i a
  simp

/-- If each factor homomorphism is surjective, so is the induced homomorphism on star free
products. -/
theorem mapStar_surjective {A' : I → Type*} [∀ i, Semiring (A' i)] [∀ i, Algebra R (A' i)]
    [∀ i, StarRing (A' i)] [∀ i, StarModule R (A' i)]
    {f : ∀ i, A i →⋆ₐ[R] A' i} (hf : ∀ i, Function.Surjective (f i)) :
    Function.Surjective (mapStar f) := by
  have htop : (⊤ : StarSubalgebra R (FreeProduct R A')) ≤ (mapStar f).range := by
    rw [← iSup_range_ιStar R A', iSup_le_iff]
    rintro i _ ⟨a', rfl⟩
    obtain ⟨a, rfl⟩ := hf i a'
    exact ⟨ι R A i a, mapStar_ι f i a⟩
  exact fun y ↦ htop trivial

/-- Factorwise star-algebra equivalences induce a star-algebra equivalence of free products. -/
def mapStarEquiv {A' : I → Type*} [∀ i, Semiring (A' i)] [∀ i, Algebra R (A' i)]
    [∀ i, StarRing (A' i)] [∀ i, StarModule R (A' i)]
    (e : ∀ i, A i ≃⋆ₐ[R] A' i) : FreeProduct R A ≃⋆ₐ[R] FreeProduct R A' :=
  StarAlgEquiv.ofStarAlgHom
    (mapStar fun i ↦ (e i).toStarAlgHom)
    (mapStar fun i ↦ (e i).symm.toStarAlgHom)
    (starAlgHom_ext fun i a ↦ by simp)
    (starAlgHom_ext fun i a' ↦ by simp)

@[simp]
theorem mapStarEquiv_toStarAlgHom {A' : I → Type*} [∀ i, Semiring (A' i)] [∀ i, Algebra R (A' i)]
    [∀ i, StarRing (A' i)] [∀ i, StarModule R (A' i)] (e : ∀ i, A i ≃⋆ₐ[R] A' i) :
    (mapStarEquiv e).toStarAlgHom = mapStar fun i ↦ (e i).toStarAlgHom :=
  (rfl)

@[simp]
theorem mapStarEquiv_ι {A' : I → Type*} [∀ i, Semiring (A' i)] [∀ i, Algebra R (A' i)]
    [∀ i, StarRing (A' i)] [∀ i, StarModule R (A' i)]
    (e : ∀ i, A i ≃⋆ₐ[R] A' i) (i : I) (a : A i) :
    mapStarEquiv e (ι R A i a) = ι R A' i (e i a) := by
  simp [mapStarEquiv]

@[simp]
theorem mapStarEquiv_symm {A' : I → Type*} [∀ i, Semiring (A' i)] [∀ i, Algebra R (A' i)]
    [∀ i, StarRing (A' i)] [∀ i, StarModule R (A' i)] (e : ∀ i, A i ≃⋆ₐ[R] A' i) :
    (mapStarEquiv e).symm = mapStarEquiv fun i ↦ (e i).symm :=
  (rfl)

end Combinators

end LinearAlgebra.FreeProduct

-- Reopen `LinearAlgebra.FreeProduct` cleanly so the outer fixed-family `A` variables are not in
-- scope when reindexing and grouping across varying index types.
namespace LinearAlgebra.FreeProduct

section ReindexAndGroup

variable {I J : Type*} [DecidableEq I] [DecidableEq J]
  (R : Type*) [CommSemiring R] [StarRing R]

/-- Pull back the index set of a star free product along any map `f : I → J`. -/
def reindexStarHom (A : J → Type*) [∀ j, Semiring (A j)]
    [∀ j, Algebra R (A j)] [∀ j, StarRing (A j)] [∀ j, StarModule R (A j)]
    (f : I → J) : FreeProduct R (fun i ↦ A (f i)) →⋆ₐ[R] FreeProduct R A :=
  liftStar fun {i} ↦ ιStar R A (f i)

@[simp]
theorem reindexStarHom_ι (A : J → Type*) [∀ j, Semiring (A j)]
    [∀ j, Algebra R (A j)] [∀ j, StarRing (A j)] [∀ j, StarModule R (A j)]
    (f : I → J) (i : I) (a : A (f i)) :
    reindexStarHom R A f (ι R (fun k ↦ A (f k)) i a) = ι R A (f i) a := by
  simp [reindexStarHom]

@[simp]
theorem reindexStarHom_comp_ιStar (A : J → Type*)
    [∀ j, Semiring (A j)] [∀ j, Algebra R (A j)] [∀ j, StarRing (A j)] [∀ j, StarModule R (A j)]
    (f : I → J) (i : I) :
    (reindexStarHom R A f).comp (ιStar R (fun k ↦ A (f k)) i) = ιStar R A (f i) := by
  simp [reindexStarHom]

omit [StarRing R] in
private def castFactor (A : J → Type*) [∀ j, Semiring (A j)]
    [∀ j, Algebra R (A j)] [∀ j, StarRing (A j)]
    {j₁ j₂ : J} (h : j₁ = j₂) : A j₁ →⋆ₐ[R] A j₂ :=
  h ▸ StarAlgHom.id R (A j₁)

private def reindexStarInv (A : J → Type*) [∀ j, Semiring (A j)]
    [∀ j, Algebra R (A j)] [∀ j, StarRing (A j)] [∀ j, StarModule R (A j)]
    (σ : I ≃ J) : FreeProduct R A →⋆ₐ[R] FreeProduct R (fun i ↦ A (σ i)) :=
  liftStar fun {j} ↦
    (ιStar R (fun i ↦ A (σ i)) (σ.symm j)).comp (castFactor R A (σ.apply_symm_apply j).symm)

private theorem reindexStarInv_ι (A : J → Type*) [∀ j, Semiring (A j)]
    [∀ j, Algebra R (A j)] [∀ j, StarRing (A j)] [∀ j, StarModule R (A j)]
    (σ : I ≃ J) (j : J) (a : A j) :
    reindexStarInv R A σ (ι R A j a) =
      ι R (fun i ↦ A (σ i)) (σ.symm j) (castFactor R A (σ.apply_symm_apply j).symm a) := by
  simp [reindexStarInv]

/-- Relabeling the index type along an equivalence `σ : I ≃ J` induces a star-algebra equivalence
of free products. -/
def reindexStarAlgEquiv (A : J → Type*) [∀ j, Semiring (A j)]
    [∀ j, Algebra R (A j)] [∀ j, StarRing (A j)] [∀ j, StarModule R (A j)]
    (σ : I ≃ J) : FreeProduct R (fun i ↦ A (σ i)) ≃⋆ₐ[R] FreeProduct R A :=
  StarAlgEquiv.ofStarAlgHom
    (reindexStarHom R A σ)
    (reindexStarInv R A σ)
    (starAlgHom_ext fun i a ↦ by
      rw [StarAlgHom.comp_apply, reindexStarHom_ι, reindexStarInv_ι, StarAlgHom.coe_id, id_eq]
      have hkey : ∀ (k : I) (_ : k = i) (hk : σ k = σ i),
          ι R (fun m ↦ A (σ m)) k (castFactor R A hk.symm a) =
            ι R (fun m ↦ A (σ m)) i a := by
        rintro k rfl hk
        cases Subsingleton.elim hk rfl
        rfl
      exact hkey (σ.symm (σ i)) (σ.symm_apply_apply i) (σ.apply_symm_apply (σ i)))
    (starAlgHom_ext fun j a ↦ by
      rw [StarAlgHom.comp_apply, reindexStarInv_ι, reindexStarHom_ι, StarAlgHom.coe_id, id_eq]
      have hkey : ∀ (k : I) (hk : σ k = j),
          ι R A (σ k) (castFactor R A hk.symm a) = ι R A j a := by
        rintro k rfl
        rfl
      exact hkey (σ.symm j) (σ.apply_symm_apply j))

@[simp]
theorem reindexStarAlgEquiv_toStarAlgHom (A : J → Type*)
    [∀ j, Semiring (A j)] [∀ j, Algebra R (A j)] [∀ j, StarRing (A j)] [∀ j, StarModule R (A j)]
    (σ : I ≃ J) :
    (reindexStarAlgEquiv R A σ).toStarAlgHom = reindexStarHom R A σ :=
  (rfl)

@[simp]
theorem reindexStarAlgEquiv_ι (A : J → Type*) [∀ j, Semiring (A j)]
    [∀ j, Algebra R (A j)] [∀ j, StarRing (A j)] [∀ j, StarModule R (A j)]
    (σ : I ≃ J) (i : I) (a : A (σ i)) :
    reindexStarAlgEquiv R A σ (ι R (fun k ↦ A (σ k)) i a) = ι R A (σ i) a := by
  simp [reindexStarAlgEquiv]

@[simp]
theorem reindexStarAlgEquiv_symm_ι (A : J → Type*)
    [∀ j, Semiring (A j)] [∀ j, Algebra R (A j)] [∀ j, StarRing (A j)] [∀ j, StarModule R (A j)]
    (σ : I ≃ J) (i : I) (a : A (σ i)) :
    (reindexStarAlgEquiv R A σ).symm (ι R A (σ i) a) = ι R (fun k ↦ A (σ k)) i a :=
  (reindexStarAlgEquiv R A σ).symm_apply_eq.mpr (reindexStarAlgEquiv_ι R A σ i a).symm

/-- Associativity (sigma grouping) for algebraic star free products: a star free product indexed by
`Σ j, κ j` is canonically star-isomorphic to the iterated star free product over `j` and `κ j`. -/
def sigmaStarAlgEquiv {κ : J → Type*} [∀ j, DecidableEq (κ j)]
    (B : (j : J) → κ j → Type*) [∀ j k, Semiring (B j k)] [∀ j k, Algebra R (B j k)]
    [∀ j k, StarRing (B j k)] [∀ j k, StarModule R (B j k)] :
    FreeProduct R (fun p : Σ j, κ j ↦ B p.fst p.snd) ≃⋆ₐ[R]
      FreeProduct R (fun j ↦ FreeProduct R (B j)) :=
  StarAlgEquiv.ofStarAlgHom
    (liftStar fun {p} ↦
      (ιStar R (fun j ↦ FreeProduct R (B j)) p.fst).comp (ιStar R (B p.fst) p.snd))
    (liftStar fun {j} ↦ liftStar fun {k} ↦
      ιStar R (fun p : Σ j, κ j ↦ B p.fst p.snd) ⟨j, k⟩)
    (starAlgHom_ext fun p b ↦ by
      rcases p with ⟨j, k⟩
      simp)
    (starAlgHom_ext fun j x ↦ by
      have hj :
          ((liftStar fun {p : Σ j, κ j} ↦
              (ιStar R (fun j ↦ FreeProduct R (B j)) p.fst).comp (ιStar R (B p.fst) p.snd)).comp
            (liftStar fun {k} ↦ ιStar R (fun p : Σ j, κ j ↦ B p.fst p.snd) ⟨j, k⟩)) =
            ιStar R (fun j ↦ FreeProduct R (B j)) j :=
        starAlgHom_ext fun k b ↦ by simp
      simpa using DFunLike.congr_fun hj x)

@[simp]
theorem sigmaStarAlgEquiv_ι {κ : J → Type*} [∀ j, DecidableEq (κ j)]
    (B : (j : J) → κ j → Type*) [∀ j k, Semiring (B j k)] [∀ j k, Algebra R (B j k)]
    [∀ j k, StarRing (B j k)] [∀ j k, StarModule R (B j k)]
    (j : J) (k : κ j) (b : B j k) :
    sigmaStarAlgEquiv R B (ι R (fun p : Σ j, κ j ↦ B p.fst p.snd) ⟨j, k⟩ b) =
      ι R (fun j ↦ FreeProduct R (B j)) j (ι R (B j) k b) := by
  simp [sigmaStarAlgEquiv]

@[simp]
theorem sigmaStarAlgEquiv_symm_ι {κ : J → Type*}
    [∀ j, DecidableEq (κ j)] (B : (j : J) → κ j → Type*) [∀ j k, Semiring (B j k)]
    [∀ j k, Algebra R (B j k)] [∀ j k, StarRing (B j k)] [∀ j k, StarModule R (B j k)]
    (j : J) (k : κ j) (b : B j k) :
    (sigmaStarAlgEquiv R B).symm (ι R (fun j ↦ FreeProduct R (B j)) j (ι R (B j) k b)) =
      ι R (fun p : Σ j, κ j ↦ B p.fst p.snd) ⟨j, k⟩ b :=
  (sigmaStarAlgEquiv R B).symm_apply_eq.mpr (sigmaStarAlgEquiv_ι R B j k b).symm

/-- Grouping the factors of `FreeProduct R A` along any indexing map `p : I → J` identifies
`FreeProduct R A` with the star free product over `j : J` of the fiber star free products over
`{i : I // p i = j}`. -/
def fiberStarAlgEquiv (A : I → Type*) [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]
    [∀ i, StarRing (A i)] [∀ i, StarModule R (A i)] (p : I → J) :
    FreeProduct R A ≃⋆ₐ[R]
      FreeProduct R (fun j : J ↦ FreeProduct R (fun i : {i : I // p i = j} ↦ A i.val)) :=
  (reindexStarAlgEquiv R A (Equiv.sigmaFiberEquiv p)).symm.trans
    (sigmaStarAlgEquiv R fun j (i : {i : I // p i = j}) ↦ A i.val)

@[simp]
theorem fiberStarAlgEquiv_ι (A : I → Type*) [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]
    [∀ i, StarRing (A i)] [∀ i, StarModule R (A i)] (p : I → J)
    (i : I) (a : A i) :
    fiberStarAlgEquiv R A p (ι R A i a) =
      ι R (fun j : J ↦ FreeProduct R (fun k : {k : I // p k = j} ↦ A k.val)) (p i)
        (ι R (fun k : {k : I // p k = p i} ↦ A k.val) ⟨i, rfl⟩ a) := by
  have h1 : (reindexStarAlgEquiv R A (Equiv.sigmaFiberEquiv p)).symm (ι R A i a) =
      ι R (fun q : Σ j : J, {k : I // p k = j} ↦ A (Equiv.sigmaFiberEquiv p q))
        ⟨p i, ⟨i, rfl⟩⟩ a :=
    reindexStarAlgEquiv_symm_ι R A (Equiv.sigmaFiberEquiv p) ⟨p i, ⟨i, rfl⟩⟩ a
  exact (congrArg (sigmaStarAlgEquiv R fun j (k : {k : I // p k = j}) ↦ A k.val) h1).trans
    (sigmaStarAlgEquiv_ι R (fun j (k : {k : I // p k = j}) ↦ A k.val) (p i) ⟨i, rfl⟩ a)

@[simp]
theorem fiberStarAlgEquiv_symm_ι (A : I → Type*) [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]
    [∀ i, StarRing (A i)] [∀ i, StarModule R (A i)] (p : I → J)
    (j : J) (i : {i : I // p i = j}) (a : A i.val) :
    (fiberStarAlgEquiv R A p).symm
      (ι R (fun j' : J ↦ FreeProduct R (fun k : {k : I // p k = j'} ↦ A k.val)) j
        (ι R (fun k : {k : I // p k = j} ↦ A k.val) i a)) = ι R A i.val a := by
  obtain ⟨i, rfl⟩ := i
  exact (fiberStarAlgEquiv R A p).symm_apply_eq.mpr (fiberStarAlgEquiv_ι R A p i a).symm

end ReindexAndGroup

end LinearAlgebra.FreeProduct

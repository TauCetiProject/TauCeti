/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.EulerCharacteristic

/-!
# The intersection pairing of line bundles on a surface, and numerical equivalence

For invertible sheaves `L`, `M` on a scheme `S` over a field `k`, the intersection number is
`L · M := χ(𝒪_S) − χ(L⁻¹) − χ(M⁻¹) + χ(L⁻¹ ⊗ M⁻¹)`, with `χ = Σ_{i<3} (−1)ⁱ dim_k Hⁱ` the
truncated Euler characteristic `Scheme.Modules.eulerCharBelow k S _ 3`. For `S` proper over `k`
of dimension at most two the cohomology of a coherent sheaf is finite-dimensional and vanishes in
degrees `≥ 3`, so `χ` is the Euler characteristic, and `L · M` is the coefficient of `n₁n₂` in
the numerical polynomial `χ(S, L^{⊗n₁} ⊗ M^{⊗n₂})`: the intersection number `(L · M · S)` of
Stacks, Definition 33.45.3 (0BEP), see also Hartshorne, *Algebraic Geometry*, V.1, Exercise 1.1.

Two line-bundle classes are numerically equivalent when they have the same intersection number
with every class for this surface pairing, and `Num` is the quotient of the line-bundle classes by
numerical equivalence, with the descended pairing (Hartshorne, *Algebraic Geometry*, §V.1). On a
smooth proper surface of pure dimension two, where the classes of curves generate the Picard group,
this is numerical equivalence of divisors in the sense of Fulton, *Intersection Theory*, §19.1.

## Main declarations

* `Chow.intersectionNumber k S L M`: the intersection number of two invertible sheaves;
  `Chow.intersectionNumber_comm` (symmetry), `Chow.intersectionNumber_congr` (invariance under
  isomorphism) and `Chow.intersectionNumber_trivial_left` (the trivial line bundle pairs to
  zero).
* `Chow.classIntersectionNumber k S a b`: the descended pairing on `LineBundleClass S`, given by
  `LineBundleClass.eulerCharBelow` in `Chow.classIntersectionNumber_eq`.
* `Chow.NumericallyEquivalent k S a b`: `a · c = b · c` for every class `c`, an equivalence
  relation.
* `Chow.Num k S`: line-bundle classes modulo numerical equivalence, with the descents
  `Chow.Num.lift` and `Chow.Num.lift₂` of functions invariant under numerical equivalence and
  `Chow.Num.intersectionNumber`, the descended pairing, which separates points
  (`Chow.Num.ext_intersectionNumber`).

## Implementation notes

The definitions impose no hypothesis on `S`; outside the case of a scheme proper over `k` of
dimension at most two, `χ` has the junk values of `Scheme.Modules.eulerCharBelow`. The pairing is
the surface (degree two) pairing: on a proper scheme of dimension at most one, `χ(L)` is affine in
the degree of `L`, so the pairing vanishes identically and `Num` is a single point. So
`NumericallyEquivalent` and `Num` are only meaningful on surfaces. The
bilinearity of the pairing, and with it the group structure on `Num`, rest on the numerical
polynomial of Stacks, Lemma 33.45.1 (0BEM), and are not part of this file; so `Num` is the
quotient type of the setoid of numerical equivalence.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry.Chow

variable (k : Type u) [Field k] (S : Scheme.{u}) [S.Over (Spec (.of k))]

/-- The intersection number `L · M := χ(𝒪_S) − χ(L⁻¹) − χ(M⁻¹) + χ(L⁻¹ ⊗ M⁻¹)` of invertible
sheaves on a scheme over a field, with `χ = Σ_{i<3} (−1)ⁱ dim_k Hⁱ`. For `S` proper over `k` of
dimension at most two it is the coefficient of `n₁n₂` in the numerical polynomial
`χ(S, L^{⊗n₁} ⊗ M^{⊗n₂})`, the intersection number `(L · M · S)` of Stacks, Definition 33.45.3
(0BEP), with Lemma 33.45.1 (0BEM). -/
@[stacks 0BEP "for d = 2 and F = 𝒪_S, via the second difference of χ"]
def intersectionNumber (L M : InvertibleSheaf S) : ℤ :=
  Scheme.Modules.eulerCharBelow k S (InvertibleSheaf.trivial S).obj 3 -
    Scheme.Modules.eulerCharBelow k S L.dual.obj 3 -
    Scheme.Modules.eulerCharBelow k S M.dual.obj 3 +
    Scheme.Modules.eulerCharBelow k S (L.dual.tensorProduct M.dual).obj 3

variable {k S}

lemma intersectionNumber_def (L M : InvertibleSheaf S) :
    intersectionNumber k S L M =
      Scheme.Modules.eulerCharBelow k S (InvertibleSheaf.trivial S).obj 3 -
        Scheme.Modules.eulerCharBelow k S L.dual.obj 3 -
        Scheme.Modules.eulerCharBelow k S M.dual.obj 3 +
        Scheme.Modules.eulerCharBelow k S (L.dual.tensorProduct M.dual).obj 3 :=
  (rfl)

/-- The intersection number only depends on the classes of the line bundles in the Picard
group. -/
lemma intersectionNumber_congr {L L' M M' : InvertibleSheaf S}
    (hL : LineBundleClass.mk L = LineBundleClass.mk L')
    (hM : LineBundleClass.mk M = LineBundleClass.mk M') :
    intersectionNumber k S L M = intersectionNumber k S L' M' := by
  have hL' : LineBundleClass.mk L.dual = LineBundleClass.mk L'.dual := by
    rw [← LineBundleClass.inv_mk, ← LineBundleClass.inv_mk, hL]
  have hM' : LineBundleClass.mk M.dual = LineBundleClass.mk M'.dual := by
    rw [← LineBundleClass.inv_mk, ← LineBundleClass.inv_mk, hM]
  have hLM : LineBundleClass.mk (L.dual.tensorProduct M.dual) =
      LineBundleClass.mk (L'.dual.tensorProduct M'.dual) := by
    rw [LineBundleClass.mk_tensorProduct, LineBundleClass.mk_tensorProduct, hL', hM']
  rw [intersectionNumber_def, intersectionNumber_def,
    InvertibleSheaf.eulerCharBelow_eq_of_mk_eq k hL',
    InvertibleSheaf.eulerCharBelow_eq_of_mk_eq k hM',
    InvertibleSheaf.eulerCharBelow_eq_of_mk_eq k hLM]

/-- The intersection pairing is symmetric. -/
lemma intersectionNumber_comm (L M : InvertibleSheaf S) :
    intersectionNumber k S L M = intersectionNumber k S M L := by
  have h : LineBundleClass.mk (L.dual.tensorProduct M.dual) =
      LineBundleClass.mk (M.dual.tensorProduct L.dual) := by
    rw [LineBundleClass.mk_tensorProduct, LineBundleClass.mk_tensorProduct, mul_comm]
  rw [intersectionNumber_def, intersectionNumber_def,
    InvertibleSheaf.eulerCharBelow_eq_of_mk_eq k h]
  ring

/-- The trivial line bundle has intersection number zero with every line bundle. -/
@[simp]
lemma intersectionNumber_trivial_left (M : InvertibleSheaf S) :
    intersectionNumber k S (InvertibleSheaf.trivial S) M = 0 := by
  have h₁ : LineBundleClass.mk (InvertibleSheaf.trivial S).dual =
      LineBundleClass.mk (InvertibleSheaf.trivial S) := by
    rw [← LineBundleClass.inv_mk, LineBundleClass.mk_trivial, inv_one]
  have h₂ : LineBundleClass.mk ((InvertibleSheaf.trivial S).dual.tensorProduct M.dual) =
      LineBundleClass.mk M.dual := by
    rw [LineBundleClass.mk_tensorProduct, h₁, LineBundleClass.mk_trivial, one_mul]
  rw [intersectionNumber_def, InvertibleSheaf.eulerCharBelow_eq_of_mk_eq k h₁,
    InvertibleSheaf.eulerCharBelow_eq_of_mk_eq k h₂]
  ring

/-- The trivial line bundle has intersection number zero with every line bundle. -/
@[simp]
lemma intersectionNumber_trivial_right (L : InvertibleSheaf S) :
    intersectionNumber k S L (InvertibleSheaf.trivial S) = 0 := by
  rw [intersectionNumber_comm, intersectionNumber_trivial_left]

variable (k S)

/-- The surface intersection pairing on the Picard group `LineBundleClass S`, descended from
`Chow.intersectionNumber`. -/
def classIntersectionNumber (a b : LineBundleClass S) : ℤ :=
  LineBundleClass.lift
    (fun L ↦ LineBundleClass.lift (intersectionNumber k S L)
      (fun _ _ h ↦ intersectionNumber_congr rfl (LineBundleClass.mk_eq_mk_iff.2 h)))
    (fun L L' h ↦ by
      funext b
      obtain ⟨M, rfl⟩ := LineBundleClass.mk_surjective b
      simp only [LineBundleClass.lift_mk]
      exact intersectionNumber_congr (LineBundleClass.mk_eq_mk_iff.2 h) rfl) a b

variable {k S}

@[simp]
lemma classIntersectionNumber_mk_mk (L M : InvertibleSheaf S) :
    classIntersectionNumber k S (LineBundleClass.mk L) (LineBundleClass.mk M) =
      intersectionNumber k S L M := by
  simp only [classIntersectionNumber, LineBundleClass.lift_mk]

/-- The intersection pairing on the Picard group is symmetric. -/
lemma classIntersectionNumber_comm (a b : LineBundleClass S) :
    classIntersectionNumber k S a b = classIntersectionNumber k S b a := by
  obtain ⟨L, rfl⟩ := LineBundleClass.mk_surjective a
  obtain ⟨M, rfl⟩ := LineBundleClass.mk_surjective b
  rw [classIntersectionNumber_mk_mk, classIntersectionNumber_mk_mk, intersectionNumber_comm]

/-- The unit class has intersection number zero with every class. -/
@[simp]
lemma classIntersectionNumber_one_left (b : LineBundleClass S) :
    classIntersectionNumber k S 1 b = 0 := by
  obtain ⟨M, rfl⟩ := LineBundleClass.mk_surjective b
  rw [← LineBundleClass.mk_trivial, classIntersectionNumber_mk_mk,
    intersectionNumber_trivial_left]

/-- The unit class has intersection number zero with every class. -/
@[simp]
lemma classIntersectionNumber_one_right (a : LineBundleClass S) :
    classIntersectionNumber k S a 1 = 0 := by
  rw [classIntersectionNumber_comm, classIntersectionNumber_one_left]

/-- The intersection pairing on the Picard group in terms of the truncated Euler characteristic
of line-bundle classes: `a · b = χ(1) − χ(a⁻¹) − χ(b⁻¹) + χ(a⁻¹ b⁻¹)`. -/
lemma classIntersectionNumber_eq (a b : LineBundleClass S) :
    classIntersectionNumber k S a b =
      LineBundleClass.eulerCharBelow k (1 : LineBundleClass S) 3 -
        LineBundleClass.eulerCharBelow k a⁻¹ 3 - LineBundleClass.eulerCharBelow k b⁻¹ 3 +
        LineBundleClass.eulerCharBelow k (a⁻¹ * b⁻¹) 3 := by
  obtain ⟨L, rfl⟩ := LineBundleClass.mk_surjective a
  obtain ⟨M, rfl⟩ := LineBundleClass.mk_surjective b
  rw [classIntersectionNumber_mk_mk, intersectionNumber_def, LineBundleClass.inv_mk,
    LineBundleClass.inv_mk, ← LineBundleClass.mk_tensorProduct, LineBundleClass.eulerCharBelow_one,
    LineBundleClass.eulerCharBelow_mk, LineBundleClass.eulerCharBelow_mk,
    LineBundleClass.eulerCharBelow_mk]

variable (k S)

/-- Two line-bundle classes are numerically equivalent when they have the same surface
intersection number `Chow.classIntersectionNumber` with every line-bundle class (Hartshorne,
*Algebraic Geometry*, §V.1). On a smooth proper surface of pure dimension two this agrees with
numerical equivalence in the sense of Fulton, *Intersection Theory*, §19.1. -/
def NumericallyEquivalent (a b : LineBundleClass S) : Prop :=
  ∀ c, classIntersectionNumber k S a c = classIntersectionNumber k S b c

variable {k S}

lemma numericallyEquivalent_iff {a b : LineBundleClass S} :
    NumericallyEquivalent k S a b ↔
      ∀ c, classIntersectionNumber k S a c = classIntersectionNumber k S b c :=
  Iff.rfl

/-- Numerically equivalent classes have the same intersection number with every class. -/
lemma NumericallyEquivalent.classIntersectionNumber_right {a b : LineBundleClass S}
    (h : NumericallyEquivalent k S a b) (c : LineBundleClass S) :
    classIntersectionNumber k S a c = classIntersectionNumber k S b c :=
  h c

@[refl, simp]
lemma NumericallyEquivalent.refl (a : LineBundleClass S) : NumericallyEquivalent k S a a :=
  fun _ ↦ rfl

@[symm]
lemma NumericallyEquivalent.symm {a b : LineBundleClass S} (h : NumericallyEquivalent k S a b) :
    NumericallyEquivalent k S b a :=
  fun c ↦ (h c).symm

@[trans]
lemma NumericallyEquivalent.trans {a b c : LineBundleClass S} (h₁ : NumericallyEquivalent k S a b)
    (h₂ : NumericallyEquivalent k S b c) : NumericallyEquivalent k S a c :=
  fun d ↦ (h₁ d).trans (h₂ d)

/-- Numerical equivalence is an equivalence relation. -/
lemma numericallyEquivalent_equivalence : Equivalence (NumericallyEquivalent k S) :=
  ⟨NumericallyEquivalent.refl, NumericallyEquivalent.symm, NumericallyEquivalent.trans⟩

/-- A class is numerically trivial when it has intersection number zero with every class. -/
lemma numericallyEquivalent_one_right {a : LineBundleClass S} :
    NumericallyEquivalent k S a 1 ↔ ∀ c, classIntersectionNumber k S a c = 0 := by
  simp only [numericallyEquivalent_iff, classIntersectionNumber_one_left]

/-- A class is numerically trivial when it has intersection number zero with every class. -/
lemma numericallyEquivalent_one_left {a : LineBundleClass S} :
    NumericallyEquivalent k S 1 a ↔ ∀ c, classIntersectionNumber k S a c = 0 :=
  ⟨fun h ↦ numericallyEquivalent_one_right.1 h.symm,
    fun h ↦ (numericallyEquivalent_one_right.2 h).symm⟩

/-- Numerically equivalent classes have the same intersection number with every class, also
when the class is put on the left. -/
lemma NumericallyEquivalent.classIntersectionNumber_left {a b : LineBundleClass S}
    (h : NumericallyEquivalent k S a b) (c : LineBundleClass S) :
    classIntersectionNumber k S c a = classIntersectionNumber k S c b := by
  rw [classIntersectionNumber_comm, h c, classIntersectionNumber_comm]

/-- Numerically equivalent classes on both sides have the same intersection number. -/
lemma NumericallyEquivalent.classIntersectionNumber {a a' b b' : LineBundleClass S}
    (ha : NumericallyEquivalent k S a a') (hb : NumericallyEquivalent k S b b') :
    Chow.classIntersectionNumber k S a b = Chow.classIntersectionNumber k S a' b' :=
  (ha b).trans (hb.classIntersectionNumber_left a')

variable (k S)

/-- The setoid of numerical equivalence on line-bundle classes. -/
private def numericalSetoid : Setoid (LineBundleClass S) where
  r := NumericallyEquivalent k S
  iseqv := numericallyEquivalent_equivalence

/-- Line-bundle classes modulo numerical equivalence for the surface pairing
`Chow.classIntersectionNumber` (Hartshorne, *Algebraic Geometry*, §V.1); on a smooth proper
surface of pure dimension two this is the group of Fulton, *Intersection Theory*, §19.1. -/
def Num : Type _ :=
  Quotient (numericalSetoid k S)

namespace Num

variable {S}

/-- The numerical class of a line-bundle class. -/
def mk (a : LineBundleClass S) : Num k S :=
  Quotient.mk (numericalSetoid k S) a

variable {k}

lemma mk_surjective : Function.Surjective (mk k : LineBundleClass S → Num k S) :=
  Quotient.mk_surjective

@[simp]
lemma mk_eq_mk_iff {a b : LineBundleClass S} :
    mk k a = mk k b ↔ NumericallyEquivalent k S a b :=
  Quotient.eq (r := numericalSetoid k S)

/-- Descend a function on line-bundle classes that is invariant under numerical equivalence to
numerical classes. -/
def lift {α : Sort*} (f : LineBundleClass S → α)
    (hf : ∀ a b, NumericallyEquivalent k S a b → f a = f b) : Num k S → α :=
  Quotient.lift (s := numericalSetoid k S) f hf

@[simp]
lemma lift_mk {α : Sort*} {f : LineBundleClass S → α}
    {hf : ∀ a b, NumericallyEquivalent k S a b → f a = f b} (a : LineBundleClass S) :
    lift f hf (mk k a) = f a :=
  (rfl)

/-- A function on numerical classes is determined by its values on representatives. -/
lemma lift_unique {α : Sort*} {f : LineBundleClass S → α}
    {hf : ∀ a b, NumericallyEquivalent k S a b → f a = f b} (g : Num k S → α)
    (hg : ∀ a, g (mk k a) = f a) : g = lift f hf := by
  funext x
  obtain ⟨a, rfl⟩ := mk_surjective x
  rw [hg, lift_mk]

/-- Descend a binary function on line-bundle classes that is invariant under numerical
equivalence in each argument to numerical classes. -/
def lift₂ {α : Sort*} (f : LineBundleClass S → LineBundleClass S → α)
    (hf : ∀ a₁ b₁ a₂ b₂, NumericallyEquivalent k S a₁ a₂ → NumericallyEquivalent k S b₁ b₂ →
      f a₁ b₁ = f a₂ b₂) : Num k S → Num k S → α :=
  Quotient.lift₂ (s₁ := numericalSetoid k S) (s₂ := numericalSetoid k S) f hf

@[simp]
lemma lift₂_mk_mk {α : Sort*} {f : LineBundleClass S → LineBundleClass S → α}
    {hf : ∀ a₁ b₁ a₂ b₂, NumericallyEquivalent k S a₁ a₂ → NumericallyEquivalent k S b₁ b₂ →
      f a₁ b₁ = f a₂ b₂} (a b : LineBundleClass S) :
    lift₂ f hf (mk k a) (mk k b) = f a b :=
  (rfl)

variable (k S)

/-- The surface intersection pairing descended to numerical classes. -/
def intersectionNumber (x y : Num k S) : ℤ :=
  lift₂ (classIntersectionNumber k S) (fun _ _ _ _ ha hb ↦ ha.classIntersectionNumber hb) x y

variable {k S}

@[simp]
lemma intersectionNumber_mk_mk (a b : LineBundleClass S) :
    intersectionNumber k S (mk k a) (mk k b) = classIntersectionNumber k S a b :=
  (rfl)

/-- The descended intersection pairing is symmetric. -/
lemma intersectionNumber_comm (x y : Num k S) :
    intersectionNumber k S x y = intersectionNumber k S y x := by
  obtain ⟨a, rfl⟩ := mk_surjective x
  obtain ⟨b, rfl⟩ := mk_surjective y
  simp only [intersectionNumber_mk_mk, classIntersectionNumber_comm]

/-- The numerical class of the unit has intersection number zero with every numerical class. -/
@[simp]
lemma intersectionNumber_mk_one_left (y : Num k S) :
    intersectionNumber k S (mk k 1) y = 0 := by
  obtain ⟨b, rfl⟩ := mk_surjective y
  rw [intersectionNumber_mk_mk, classIntersectionNumber_one_left]

/-- The numerical class of the unit has intersection number zero with every numerical class. -/
@[simp]
lemma intersectionNumber_mk_one_right (x : Num k S) :
    intersectionNumber k S x (mk k 1) = 0 := by
  rw [intersectionNumber_comm, intersectionNumber_mk_one_left]

/-- The descended intersection pairing separates numerical classes. -/
lemma ext_intersectionNumber {x y : Num k S}
    (h : ∀ z, intersectionNumber k S x z = intersectionNumber k S y z) : x = y := by
  obtain ⟨a, rfl⟩ := mk_surjective x
  obtain ⟨b, rfl⟩ := mk_surjective y
  exact mk_eq_mk_iff.2 fun c ↦ h (mk k c)

end Num

end TauCeti.AlgebraicGeometry.Chow

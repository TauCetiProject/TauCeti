/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Extension.SquareZero
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The Baer sum of square-zero extensions

Let `E` and `F` be square-zero extensions of the `A`-algebra `B` by the `B`-module `M`. Their
Baer sum is the quotient of the fibre product `E ×_B F` by the antidiagonal kernel
`{(ι_E m, -ι_F m)}`, again a square-zero extension of `B` by `M`; the class of `(ι_E m, ι_F n)`
is the kernel element `m + n`. This operation makes `Exal_A(B, M)` an abelian group, with the
class of the trivial extension as zero and the extension with negated kernel inclusion as
negative.

## Main definitions

* `TauCeti.SquareZeroExtension.fiberProduct`: the fibre product `E ×_B F`, with its universal
  property `TauCeti.SquareZeroExtension.fiberProductLift`.
* `TauCeti.SquareZeroExtension.antidiagonal`: the ideal `{(ι_E m, -ι_F m)}` of `E ×_B F`.
* `TauCeti.SquareZeroExtension.baerSum`: the Baer sum `E + F` of two extensions, with the
  projection `TauCeti.SquareZeroExtension.baerSumMk : E ×_B F → E + F` and the morphisms out of it
  `TauCeti.SquareZeroExtension.baerSumLift`.
* `TauCeti.SquareZeroExtension.baerSumMap`, `baerSumComm`, `baerSumAssoc`: functoriality,
  commutativity and associativity of the Baer sum, as morphisms of extensions.
* `TauCeti.SquareZeroExtension.toBaerSumOfSplitting`: a split extension is a unit for the Baer sum.
* `TauCeti.SquareZeroExtension.neg`: the extension with negated kernel inclusion, and
  `TauCeti.SquareZeroExtension.baerSumNegSplitting`, the diagonal splitting of `E + neg E`.
* The `AddCommGroup` structure on `TauCeti.Exal A B M`.

## Main results

* `TauCeti.SquareZeroExtension.baerSumMk_ι_ι`: the class of `(ι_E m, ι_F n)` is `ι (m + n)`.
* `TauCeti.SquareZeroExtension.extensionClass_baerSum`: the class of the Baer sum is the sum of
  the classes.
* `TauCeti.SquareZeroExtension.extensionClass_neg`: the class of the negated extension is the
  negative of the class.

## References

* [Stacks Project, Deformation Theory, Remark 2.4, Tag 08S3](https://stacks.math.columbia.edu/tag/08S3).
* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §§2.5.4–2.5.7.
-/

public section

universe w u v t

namespace TauCeti

open CategoryTheory

variable {A : Type u} {B : Type v} {M : Type t} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module B M]

namespace SquareZeroExtension

section FiberProduct

variable (E F : SquareZeroExtension.{w} A B M)

/-- The fibre product `E ×_B F` of two square-zero extensions of `B`: the pairs `(x, y)` with
`π_E x = π_F y`. -/
def fiberProduct : Subalgebra A (E.Ring × F.Ring) :=
  AlgHom.equalizer (E.π.comp (AlgHom.fst A E.Ring F.Ring)) (F.π.comp (AlgHom.snd A E.Ring F.Ring))

variable {E F} in
@[simp]
theorem mem_fiberProduct {p : E.Ring × F.Ring} : p ∈ fiberProduct E F ↔ E.π p.1 = F.π p.2 :=
  Iff.rfl

variable {E F} in
/-- The universal property of the fibre product: two algebra maps to `E` and `F` that agree
after projecting to `B` define an algebra map to `E ×_B F`. -/
def fiberProductLift {P : Type*} [Semiring P] [Algebra A P] (f : P →ₐ[A] E.Ring)
    (g : P →ₐ[A] F.Ring) (h : ∀ p, E.π (f p) = F.π (g p)) : P →ₐ[A] fiberProduct E F :=
  (f.prod g).codRestrict _ h

variable {E F} in
@[simp]
theorem coe_fiberProductLift_apply {P : Type*} [Semiring P] [Algebra A P] (f : P →ₐ[A] E.Ring)
    (g : P →ₐ[A] F.Ring) (h : ∀ p, E.π (f p) = F.π (g p)) (p : P) :
    (fiberProductLift f g h p : E.Ring × F.Ring) = (f p, g p) :=
  (rfl)

/-- The antidiagonal kernel `{(ι_E m, -ι_F m)}` of the fibre product `E ×_B F`. -/
def antidiagonal : Ideal (fiberProduct E F) where
  carrier := {p | ∃ m, (p : E.Ring × F.Ring) = (E.ι m, -F.ι m)}
  add_mem' := by
    rintro _ _ ⟨m, hm⟩ ⟨n, hn⟩
    exact ⟨m + n, by simp [hm, hn, add_comm]⟩
  zero_mem' := ⟨0, by ext <;> simp⟩
  smul_mem' := by
    rintro ⟨⟨x, y⟩, hxy⟩ _ ⟨m, hm⟩
    exact ⟨E.π x • m, by simp [hm, mul_neg, (mem_fiberProduct.1 hxy : E.π x = F.π y)]⟩

variable {E F} in
theorem mem_antidiagonal {p : fiberProduct E F} :
    p ∈ antidiagonal E F ↔ ∃ m, (p : E.Ring × F.Ring) = (E.ι m, -F.ι m) :=
  Iff.rfl

/-- The projection from the fibre product onto its quotient by the antidiagonal. -/
private noncomputable def mk' : fiberProduct E F →ₐ[A] fiberProduct E F ⧸ antidiagonal E F :=
  Ideal.Quotient.mkₐ A (antidiagonal E F)

private theorem mk'_surjective : Function.Surjective (mk' E F) :=
  Ideal.Quotient.mkₐ_surjective A _

variable {E F} in
private theorem mk'_eq_mk'_iff {p q : fiberProduct E F} :
    mk' E F p = mk' E F q ↔ ∃ m, (p : E.Ring × F.Ring) - q = (E.ι m, -F.ι m) := by
  rw [mk', Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
  rfl

/-- The projection `(x, y) ↦ π_E x` on the quotient of the fibre product. -/
private noncomputable def π' : fiberProduct E F ⧸ antidiagonal E F →ₐ[A] B :=
  Ideal.Quotient.liftₐ _ ((E.π.comp (AlgHom.fst A E.Ring F.Ring)).comp (fiberProduct E F).val)
    (by rintro _ ⟨m, hm⟩; simp [hm])

variable {E F} in
private theorem π'_mk' (p : fiberProduct E F) : π' E F (mk' E F p) = E.π p.1.1 :=
  Ideal.Quotient.liftₐ_apply _ _ _ _

/-- The pair `(ι_E m, ι_F n)` of kernel elements, as an element of the fibre product. -/
private def ιι (m n : M) : fiberProduct E F :=
  ⟨(E.ι m, F.ι n), by simp⟩

/-- The kernel inclusion `m ↦ (ι_E m, 0)` on the quotient of the fibre product. -/
private noncomputable def ι' : M →+ fiberProduct E F ⧸ antidiagonal E F where
  toFun m := mk' E F (ιι E F m 0)
  map_zero' := by rw [← map_zero (mk' E F)]; congr 1; ext <;> simp [ιι]
  map_add' m n := by rw [← map_add]; congr 1; ext <;> simp [ιι]

variable {E F} in
private theorem ι'_apply (m : M) : ι' E F m = mk' E F (ιι E F m 0) :=
  rfl

variable {E F} in
private theorem mk'_ιι (m n : M) : mk' E F (ιι E F m n) = ι' E F (m + n) :=
  mk'_eq_mk'_iff.2 ⟨-n, by simp [ιι]⟩

/-- The Baer sum of two square-zero extensions of `B` by `M`: the fibre product `E ×_B F` modulo
the antidiagonal kernel `{(ι_E m, -ι_F m)}`, with projection `(x, y) ↦ π_E x` and kernel
inclusion `m ↦ (ι_E m, 0)`. -/
noncomputable def baerSum : SquareZeroExtension.{w} A B M where
  Ring := fiberProduct E F ⧸ antidiagonal E F
  π := π' E F
  π_surjective b := by
    obtain ⟨x, rfl⟩ := E.π_surjective b
    obtain ⟨y, hy⟩ := F.π_surjective (E.π x)
    exact ⟨mk' E F ⟨(x, y), hy.symm⟩, π'_mk' _⟩
  ι := ι' E F
  ι_injective := by
    rw [injective_iff_map_eq_zero]
    intro m hm
    rw [← add_zero m, ← mk'_ιι, ← map_zero (mk' E F), mk'_eq_mk'_iff] at hm
    obtain ⟨n, hn⟩ := hm
    simp only [ιι, ZeroMemClass.coe_zero, sub_zero, Prod.mk.injEq] at hn
    have hn' : F.ι n = 0 := by simpa using hn.2.symm
    rw [← E.ι_injective.eq_iff, hn.1, (F.ι_eq_zero_iff n).1 hn', map_zero]
  exact := by
    intro q
    obtain ⟨⟨⟨x, y⟩, hxy⟩, rfl⟩ := mk'_surjective E F q
    rw [π'_mk']
    constructor
    · intro hx
      obtain ⟨m, rfl⟩ := (E.exact x).1 hx
      obtain ⟨n, rfl⟩ := (F.exact y).1 (by simpa [hx] using (mem_fiberProduct.1 hxy).symm)
      exact ⟨m + n, (mk'_ιι m n).symm⟩
    · rintro ⟨m, hm⟩
      have h := congrArg (π' E F) hm
      rw [ι'_apply, π'_mk', π'_mk'] at h
      simpa [ιι] using h.symm
  mul_ι q m := by
    obtain ⟨⟨⟨x, y⟩, hxy⟩, rfl⟩ := mk'_surjective E F q
    rw [π'_mk', ι'_apply, ι'_apply, ← map_mul]
    congr 1
    ext <;> simp [ιι]

/-- The projection from the fibre product `E ×_B F` onto the Baer sum. -/
noncomputable def baerSumMk : fiberProduct E F →ₐ[A] (baerSum E F).Ring :=
  mk' E F

theorem baerSumMk_surjective : Function.Surjective (baerSumMk E F) :=
  mk'_surjective E F

/-- The kernel of the projection onto the Baer sum is the antidiagonal. -/
theorem ker_baerSumMk : RingHom.ker (baerSumMk E F) = antidiagonal E F :=
  Ideal.Quotient.mkₐ_ker A _

variable {E F} in
theorem baerSumMk_eq_baerSumMk_iff {p q : fiberProduct E F} :
    baerSumMk E F p = baerSumMk E F q ↔ ∃ m, (p : E.Ring × F.Ring) - q = (E.ι m, -F.ι m) :=
  mk'_eq_mk'_iff

variable {E F} in
@[simp]
theorem π_baerSumMk (p : fiberProduct E F) : (baerSum E F).π (baerSumMk E F p) = E.π p.1.1 :=
  π'_mk' p

/-- The class of a pair `(ι_E m, ι_F n)` of kernel elements is the kernel element `m + n`. -/
@[simp]
theorem baerSumMk_ι_ι (m n : M) :
    baerSumMk E F ⟨(E.ι m, F.ι n), by simp⟩ = (baerSum E F).ι (m + n) :=
  mk'_ιι m n

theorem ι_baerSum (m : M) : (baerSum E F).ι m = baerSumMk E F ⟨(E.ι m, 0), by simp⟩ := by
  simpa using (baerSumMk_ι_ι E F m 0).symm

variable {E F} in
/-- A version of `baerSumMk_ι_ι` for an element of the fibre product given by its coordinates. -/
private theorem baerSumMk_eq_ι {p : fiberProduct E F} {m n : M} (hm : p.1.1 = E.ι m)
    (hn : p.1.2 = F.ι n) : baerSumMk E F p = (baerSum E F).ι (m + n) := by
  rw [← baerSumMk_ι_ι]
  exact congrArg _ (Subtype.ext (Prod.ext hm hn))

variable {E F} {G : SquareZeroExtension.{w} A B M}

/-- The algebra map on the quotient of the fibre product induced by an algebra map on the fibre
product that sends `(ι_E m, ι_F n)` to `ι_G (m + n)`. -/
private noncomputable def liftAux (φ : fiberProduct E F →ₐ[A] G.Ring)
    (hι : ∀ m n, φ ⟨(E.ι m, F.ι n), by simp⟩ = G.ι (m + n)) :
    fiberProduct E F ⧸ antidiagonal E F →ₐ[A] G.Ring :=
  Ideal.Quotient.liftₐ _ φ <| by
    rintro p ⟨m, hm⟩
    have hp : p = ⟨(E.ι m, F.ι (-m)), by simp⟩ := Subtype.ext (by simp [hm])
    rw [hp, hι, add_neg_cancel, map_zero]

private theorem liftAux_mk' (φ : fiberProduct E F →ₐ[A] G.Ring)
    (hι : ∀ m n, φ ⟨(E.ι m, F.ι n), by simp⟩ = G.ι (m + n)) (p : fiberProduct E F) :
    liftAux φ hι (mk' E F p) = φ p :=
  Ideal.Quotient.liftₐ_apply _ _ _ _

/-- A morphism out of the Baer sum, from an algebra map on the fibre product `E ×_B F` that is
compatible with the projections to `B` and sends `(ι_E m, ι_F n)` to `ι_G (m + n)`. -/
noncomputable def baerSumLift (φ : fiberProduct E F →ₐ[A] G.Ring)
    (hπ : ∀ p, G.π (φ p) = E.π p.1.1)
    (hι : ∀ m n, φ ⟨(E.ι m, F.ι n), by simp⟩ = G.ι (m + n)) : baerSum E F ⟶ G where
  toAlgHom := liftAux φ hι
  π_toAlgHom q := by
    obtain ⟨p, rfl⟩ := mk'_surjective E F q
    exact (congrArg G.π (liftAux_mk' φ hι p)).trans (hπ p)
  toAlgHom_ι m := by
    rw [ι_baerSum]
    exact (liftAux_mk' φ hι _).trans (by simpa using hι m 0)

@[simp]
theorem baerSumLift_toAlgHom_baerSumMk (φ : fiberProduct E F →ₐ[A] G.Ring)
    (hπ : ∀ p, G.π (φ p) = E.π p.1.1)
    (hι : ∀ m n, φ ⟨(E.ι m, F.ι n), by simp⟩ = G.ι (m + n)) (p : fiberProduct E F) :
    (baerSumLift φ hπ hι).toAlgHom (baerSumMk E F p) = φ p :=
  liftAux_mk' φ hι p

end FiberProduct

section Laws

variable {E E' F F' G : SquareZeroExtension.{w} A B M}

/-- The Baer sum is functorial in morphisms of extensions. -/
noncomputable def baerSumMap (e : E ⟶ E') (f : F ⟶ F') : baerSum E F ⟶ baerSum E' F' :=
  baerSumLift ((baerSumMk E' F').comp (fiberProductLift (e.toAlgHom.comp (AlgHom.fst A _ _ |>.comp
    (fiberProduct E F).val)) (f.toAlgHom.comp (AlgHom.snd A _ _ |>.comp (fiberProduct E F).val))
    fun p ↦ by simpa using mem_fiberProduct.1 p.2))
    (fun p ↦ by simp) (fun m n ↦ by
      rw [AlgHom.comp_apply, ← baerSumMk_ι_ι]
      exact congrArg (baerSumMk E' F') (Subtype.ext (by simp)))

@[simp]
theorem baerSumMap_toAlgHom_baerSumMk (e : E ⟶ E') (f : F ⟶ F') (p : fiberProduct E F) :
    (baerSumMap e f).toAlgHom (baerSumMk E F p) =
      baerSumMk E' F' ⟨(e.toAlgHom p.1.1, f.toAlgHom p.1.2),
        mem_fiberProduct.2 (by simpa using mem_fiberProduct.1 p.2)⟩ := by
  rw [baerSumMap, baerSumLift_toAlgHom_baerSumMk]
  rfl

/-- The Baer sum is commutative: `(x, y) ↦ (y, x)` induces a morphism `E + F ⟶ F + E`. -/
noncomputable def baerSumComm (E F : SquareZeroExtension.{w} A B M) : baerSum E F ⟶ baerSum F E :=
  baerSumLift ((baerSumMk F E).comp (fiberProductLift (AlgHom.snd A _ _ |>.comp
    (fiberProduct E F).val) (AlgHom.fst A _ _ |>.comp (fiberProduct E F).val)
    fun p ↦ by simpa using (mem_fiberProduct.1 p.2).symm))
    (fun p ↦ by simpa using (mem_fiberProduct.1 p.2).symm)
    (fun m n ↦ by
      rw [AlgHom.comp_apply, add_comm, ← baerSumMk_ι_ι]
      exact congrArg (baerSumMk F E) (Subtype.ext (by simp)))

@[simp]
theorem baerSumComm_toAlgHom_baerSumMk (p : fiberProduct E F) :
    (baerSumComm E F).toAlgHom (baerSumMk E F p) =
      baerSumMk F E ⟨(p.1.2, p.1.1), by simpa using (mem_fiberProduct.1 p.2).symm⟩ := by
  rw [baerSumComm, baerSumLift_toAlgHom_baerSumMk]
  rfl

/-- The negative of a square-zero extension: the same ring and projection, with the kernel
inclusion `m ↦ -ι m`. -/
-- This is reducible so that the ring of `neg E`, with its instances, is that of `E`.
abbrev neg (E : SquareZeroExtension.{w} A B M) : SquareZeroExtension.{w} A B M where
  Ring := E.Ring
  π := E.π
  π_surjective := E.π_surjective
  ι := -E.ι
  ι_injective := neg_injective.comp E.ι_injective
  exact x := (E.exact x).trans
    ⟨fun ⟨m, h⟩ ↦ ⟨-m, by simp [h]⟩, fun ⟨m, h⟩ ↦ ⟨-m, by simp [← h]⟩⟩
  mul_ι x m := by simp

@[simp]
theorem neg_π (E : SquareZeroExtension.{w} A B M) (x : E.Ring) : (neg E).π x = E.π x :=
  rfl

@[simp]
theorem neg_ι (E : SquareZeroExtension.{w} A B M) (m : M) : (neg E).ι m = -E.ι m :=
  rfl

/-- A morphism of extensions is also a morphism between their negatives. -/
def negMap (e : E ⟶ F) : neg E ⟶ neg F where
  toAlgHom := e.toAlgHom
  π_toAlgHom := e.π_toAlgHom
  toAlgHom_ι m := by simp

@[simp]
theorem negMap_toAlgHom (e : E ⟶ F) : (negMap e).toAlgHom = e.toAlgHom :=
  (rfl)

/-- The Baer sum of an extension with its negative is split by the diagonal `x ↦ (x, x)`. -/
noncomputable def baerSumNegSplitting (E : SquareZeroExtension.{w} A B M) :
    (baerSum E (neg E)).Splitting where
  toAlgHom := E.π.liftOfSurjective E.π_surjective
    ((baerSumMk E (neg E)).comp (fiberProductLift (AlgHom.id A E.Ring) (AlgHom.id A E.Ring)
      fun _ ↦ rfl)) <| by
    intro x hx
    obtain ⟨m, rfl⟩ := (E.exact x).1 hx
    rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.comp_apply,
      baerSumMk_eq_ι (m := m) (n := -m) (by simp) (by simp), add_neg_cancel, map_zero]
  π_toAlgHom b := by
    obtain ⟨x, rfl⟩ := E.π_surjective b
    rw [AlgHom.liftOfSurjective_apply]
    simp

@[simp]
theorem baerSumNegSplitting_toAlgHom_π (E : SquareZeroExtension.{w} A B M) (x : E.Ring) :
    (baerSumNegSplitting E).toAlgHom (E.π x) =
      baerSumMk E (neg E) ⟨(x, x), mem_fiberProduct.2 rfl⟩ :=
  AlgHom.liftOfSurjective_apply _ _ _ _ _

/-- The morphism `x ↦ (x, s (π x))` from an extension to its Baer sum with an extension split
by `s`. -/
noncomputable def toBaerSumOfSplitting (E : SquareZeroExtension.{w} A B M) (s : F.Splitting) :
    E ⟶ baerSum E F where
  toAlgHom := (baerSumMk E F).comp
    (fiberProductLift (AlgHom.id A E.Ring) (s.toAlgHom.comp E.π) fun x ↦ by
      rw [AlgHom.id_apply, AlgHom.comp_apply, Splitting.π_toAlgHom])
  π_toAlgHom x := by simp
  toAlgHom_ι m := by
    rw [AlgHom.comp_apply, baerSumMk_eq_ι (m := m) (n := 0) (by simp) (by simp), add_zero]

@[simp]
theorem toBaerSumOfSplitting_toAlgHom (E : SquareZeroExtension.{w} A B M) (s : F.Splitting)
    (x : E.Ring) :
    (toBaerSumOfSplitting E s).toAlgHom x = baerSumMk E F ⟨(x, s.toAlgHom (E.π x)), by simp⟩ :=
  (rfl)

section Assoc

variable (E F G)

/-- The triples `(x, y, z)` in `E × F × G` over a common point of `B`. -/
private def triple : Subalgebra A (E.Ring × F.Ring × G.Ring) :=
  AlgHom.equalizer (E.π.comp (AlgHom.fst A _ _)) (F.π.comp ((AlgHom.fst A _ _).comp
    (AlgHom.snd A _ _))) ⊓
  AlgHom.equalizer (E.π.comp (AlgHom.fst A _ _)) (G.π.comp ((AlgHom.snd A _ _).comp
    (AlgHom.snd A _ _)))

/-- The projection `(x, y, z) ↦ x` on triples. -/
private def t₁ : triple E F G →ₐ[A] E.Ring :=
  (AlgHom.fst A _ _).comp (triple E F G).val

/-- The projection `(x, y, z) ↦ y` on triples. -/
private def t₂ : triple E F G →ₐ[A] F.Ring :=
  (AlgHom.fst A _ _).comp ((AlgHom.snd A _ _).comp (triple E F G).val)

/-- The projection `(x, y, z) ↦ z` on triples. -/
private def t₃ : triple E F G →ₐ[A] G.Ring :=
  (AlgHom.snd A _ _).comp ((AlgHom.snd A _ _).comp (triple E F G).val)

variable {E F G}

private theorem t₁_apply (q : triple E F G) : t₁ E F G q = q.1.1 :=
  rfl

private theorem t₂_apply (q : triple E F G) : t₂ E F G q = q.1.2.1 :=
  rfl

private theorem t₃_apply (q : triple E F G) : t₃ E F G q = q.1.2.2 :=
  rfl

private theorem mem_triple {q : E.Ring × F.Ring × G.Ring} :
    q ∈ triple E F G ↔ E.π q.1 = F.π q.2.1 ∧ E.π q.1 = G.π q.2.2 :=
  Iff.rfl

variable (E F G)

/-- The map `(x, y, z) ↦ (x, y)` from triples to `E ×_B F`. -/
private noncomputable def tripleXY : triple E F G →ₐ[A] fiberProduct E F :=
  fiberProductLift (t₁ E F G) (t₂ E F G) fun q ↦ by
    rw [t₁_apply, t₂_apply]
    exact (mem_triple.1 q.2).1

/-- The map `(x, y, z) ↦ (y, z)` from triples to `F ×_B G`. -/
private noncomputable def tripleYZ : triple E F G →ₐ[A] fiberProduct F G :=
  fiberProductLift (t₂ E F G) (t₃ E F G) fun q ↦ by
    rw [t₂_apply, t₃_apply, ← (mem_triple.1 q.2).1]
    exact (mem_triple.1 q.2).2

/-- The surjection `(x, y, z) ↦ ([x, y], z)` from triples onto `(E + F) ×_B G`. -/
private noncomputable def tripleToLeft : triple E F G →ₐ[A] fiberProduct (baerSum E F) G :=
  fiberProductLift ((baerSumMk E F).comp (tripleXY E F G)) (t₃ E F G) fun q ↦ by
    rw [AlgHom.comp_apply, π_baerSumMk, t₃_apply]
    exact (mem_triple.1 q.2).2

/-- The map `(x, y, z) ↦ [x, [y, z]]` from triples to `E + (F + G)`. -/
private noncomputable def tripleToRight : triple E F G →ₐ[A] (baerSum E (baerSum F G)).Ring :=
  (baerSumMk E (baerSum F G)).comp <| fiberProductLift (t₁ E F G)
    ((baerSumMk F G).comp (tripleYZ E F G)) fun q ↦ by
      rw [AlgHom.comp_apply, π_baerSumMk, t₁_apply]
      exact (mem_triple.1 q.2).1

variable {E F G}

private theorem coe_tripleToLeft_apply (q : triple E F G) :
    (tripleToLeft E F G q : (baerSum E F).Ring × G.Ring) =
      (baerSumMk E F ⟨(q.1.1, q.1.2.1), (mem_triple.1 q.2).1⟩, q.1.2.2) :=
  rfl

private theorem π_tripleToRight (q : triple E F G) :
    (baerSum E (baerSum F G)).π (tripleToRight E F G q) = E.π q.1.1 :=
  π_baerSumMk _

private theorem tripleToRight_eq_ι {q : triple E F G} {a b c : M} (ha : q.1.1 = E.ι a)
    (hb : q.1.2.1 = F.ι b) (hc : q.1.2.2 = G.ι c) :
    tripleToRight E F G q = (baerSum E (baerSum F G)).ι (a + (b + c)) := by
  rw [tripleToRight, AlgHom.comp_apply]
  refine baerSumMk_eq_ι ha ?_
  rw [coe_fiberProductLift_apply, AlgHom.comp_apply]
  exact baerSumMk_eq_ι hb hc

private theorem tripleToLeft_surjective : Function.Surjective (tripleToLeft E F G) := by
  rintro ⟨⟨r, z⟩, hrz⟩
  obtain ⟨⟨⟨x, y⟩, hxy⟩, rfl⟩ := baerSumMk_surjective E F r
  refine ⟨⟨(x, y, z), mem_triple.2 ⟨hxy, ?_⟩⟩, rfl⟩
  exact (π_baerSumMk (E := E) (F := F) ⟨(x, y), hxy⟩).symm.trans (mem_fiberProduct.1 hrz)

private theorem tripleToRight_eq_zero {q : triple E F G} (h : tripleToLeft E F G q = 0) :
    tripleToRight E F G q = 0 := by
  have h' := congrArg Subtype.val h
  rw [coe_tripleToLeft_apply, ZeroMemClass.coe_zero, Prod.mk_eq_zero] at h'
  obtain ⟨m, hm⟩ := (baerSumMk_eq_baerSumMk_iff (q := 0)).1 (h'.1.trans (map_zero _).symm)
  rw [ZeroMemClass.coe_zero, sub_zero] at hm
  have h₁ : q.1.1 = E.ι m := congrArg Prod.fst hm
  have h₂ : q.1.2.1 = F.ι (-m) := (congrArg Prod.snd hm).trans (map_neg F.ι m).symm
  rw [tripleToRight_eq_ι h₁ h₂ (h'.2.trans (map_zero G.ι).symm), add_zero, add_neg_cancel,
    map_zero]

variable (E F G) in
/-- The map `([x, y], z) ↦ [x, [y, z]]` from `(E + F) ×_B G` to `E + (F + G)`. -/
private noncomputable def assocAux :
    fiberProduct (baerSum E F) G →ₐ[A] (baerSum E (baerSum F G)).Ring :=
  (tripleToLeft E F G).liftOfSurjective tripleToLeft_surjective (tripleToRight E F G) <| by
    intro q h
    exact tripleToRight_eq_zero h

private theorem assocAux_tripleToLeft (q : triple E F G) :
    assocAux E F G (tripleToLeft E F G q) = tripleToRight E F G q :=
  AlgHom.liftOfSurjective_apply _ _ _ _ _

variable (E F G) in
/-- The Baer sum is associative: `([x, y], z) ↦ [x, [y, z]]` induces a morphism
`(E + F) + G ⟶ E + (F + G)`. -/
noncomputable def baerSumAssoc : baerSum (baerSum E F) G ⟶ baerSum E (baerSum F G) :=
  baerSumLift (assocAux E F G)
    (fun r ↦ by
      obtain ⟨q, rfl⟩ := tripleToLeft_surjective r
      rw [assocAux_tripleToLeft, π_tripleToRight]
      simp only [coe_tripleToLeft_apply, π_baerSumMk])
    (fun m n ↦ by
      have hr : (⟨((baerSum E F).ι m, G.ι n), by simp⟩ : fiberProduct (baerSum E F) G) =
          tripleToLeft E F G ⟨(E.ι m, 0, G.ι n), mem_triple.2 (by simp)⟩ := by
        refine Subtype.ext ?_
        rw [coe_tripleToLeft_apply]
        exact Prod.ext (ι_baerSum E F m) rfl
      rw [hr, assocAux_tripleToLeft, tripleToRight_eq_ι (a := m) (b := 0) (c := n) rfl
        (map_zero F.ι).symm rfl, zero_add])

@[simp]
theorem baerSumAssoc_toAlgHom_baerSumMk (x : E.Ring) (y : F.Ring) (z : G.Ring)
    (hxy : E.π x = F.π y) (hyz : F.π y = G.π z) :
    (baerSumAssoc E F G).toAlgHom
        (baerSumMk (baerSum E F) G ⟨(baerSumMk E F ⟨(x, y), mem_fiberProduct.2 hxy⟩, z),
          by simpa using hxy.trans hyz⟩) =
      baerSumMk E (baerSum F G)
        ⟨(x, baerSumMk F G ⟨(y, z), mem_fiberProduct.2 hyz⟩), by simpa using hxy⟩ := by
  rw [baerSumAssoc, baerSumLift_toAlgHom_baerSumMk]
  exact assocAux_tripleToLeft ⟨(x, y, z), mem_triple.2 ⟨hxy, hxy.trans hyz⟩⟩

end Assoc

end Laws

end SquareZeroExtension

namespace Exal

open SquareZeroExtension

/-- The sum of two classes in `Exal_A(B, M)` is the class of the Baer sum of representatives
(`TauCeti.SquareZeroExtension.extensionClass_baerSum`). -/
noncomputable instance : Add (Exal A B M) where
  add := lift (fun E ↦ lift (fun F ↦ (baerSum E F).extensionClass) fun _ _ ⟨f⟩ ↦
      extensionClass_eq_extensionClass_iff.2 ⟨baerSumMap (𝟙 E) f⟩)
    fun _ _ ⟨e⟩ ↦ funext <| ind fun F ↦ by
      simp only [lift_extensionClass]
      exact extensionClass_eq_extensionClass_iff.2 ⟨baerSumMap e (𝟙 F)⟩

/-- The negative of a class in `Exal_A(B, M)` is the class of a representative with negated
kernel inclusion (`TauCeti.SquareZeroExtension.extensionClass_neg`). -/
noncomputable instance : Neg (Exal A B M) where
  neg := lift (fun E ↦ (neg E).extensionClass) fun _ _ ⟨e⟩ ↦
    extensionClass_eq_extensionClass_iff.2 ⟨negMap e⟩

end Exal

namespace SquareZeroExtension

/-- The class of the Baer sum of two extensions is the sum of their classes. -/
@[simp]
theorem extensionClass_baerSum (E F : SquareZeroExtension.{max v t} A B M) :
    (baerSum E F).extensionClass = E.extensionClass + F.extensionClass := by
  -- The sum unfolds to the iterated `Exal.lift` defining the `Add` instance.
  change _ = Exal.lift (α := Exal A B M → Exal A B M) _ _ E.extensionClass F.extensionClass
  rw [Exal.lift_extensionClass, Exal.lift_extensionClass]

/-- The class of the negated extension is the negative of the class. -/
@[simp]
theorem extensionClass_neg (E : SquareZeroExtension.{max v t} A B M) :
    (neg E).extensionClass = -E.extensionClass := by
  -- The negative unfolds to the `Exal.lift` defining the `Neg` instance.
  change _ = Exal.lift _ _ E.extensionClass
  rw [Exal.lift_extensionClass]

end SquareZeroExtension

namespace Exal

open SquareZeroExtension

variable [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module A M] [IsScalarTower A B M]
  [IsScalarTower A Bᵐᵒᵖ M]

/-- Baer sum makes `Exal_A(B, M)` an abelian group, with the class of the trivial extension as
zero and negation of the kernel inclusion as negative. -/
noncomputable instance : AddCommGroup (Exal A B M) where
  add_assoc x y z := by
    obtain ⟨E, rfl⟩ := extensionClass_surjective x
    obtain ⟨F, rfl⟩ := extensionClass_surjective y
    obtain ⟨G, rfl⟩ := extensionClass_surjective z
    simp only [← extensionClass_baerSum]
    exact extensionClass_eq_extensionClass_iff.2 ⟨baerSumAssoc E F G⟩
  zero_add x := by
    obtain ⟨E, rfl⟩ := extensionClass_surjective x
    rw [← extensionClass_squareZero, ← extensionClass_baerSum]
    exact (extensionClass_eq_extensionClass_iff.2
      ⟨toBaerSumOfSplitting E (squareZeroSplitting A B M) ≫ baerSumComm _ _⟩).symm
  add_zero x := by
    obtain ⟨E, rfl⟩ := extensionClass_surjective x
    rw [← extensionClass_squareZero, ← extensionClass_baerSum]
    exact (extensionClass_eq_extensionClass_iff.2
      ⟨toBaerSumOfSplitting E (squareZeroSplitting A B M)⟩).symm
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel x := by
    obtain ⟨E, rfl⟩ := extensionClass_surjective x
    rw [← extensionClass_neg, ← extensionClass_baerSum, extensionClass_eq_zero_iff]
    exact ⟨(baerSumNegSplitting E).map (baerSumComm E (neg E))⟩
  add_comm x y := by
    obtain ⟨E, rfl⟩ := extensionClass_surjective x
    obtain ⟨F, rfl⟩ := extensionClass_surjective y
    rw [← extensionClass_baerSum, ← extensionClass_baerSum]
    exact extensionClass_eq_extensionClass_iff.2 ⟨baerSumComm E F⟩

end Exal

end TauCeti

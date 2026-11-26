/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.GroupWithZero.Idempotent
public import Mathlib.Basic.Finite.Sum

/-!
# Algebra maps into and out of products

An algebra map `φ : A × C →ₐ[F] B` does not restrict to the first factor on the nose, because
`a ↦ (a, 0)` is not unital and so is not an algebra map.  It does restrict once `φ (1, 0) = 1`:
that hypothesis supplies exactly the missing unitality, and `a ↦ φ (a, 0)` is then an algebra map
`A →ₐ[F] B`.

This is why there is no `AlgHom.inl` upstream to compose with, and what
`AlgHom.prodFirst` provides instead. The file also records the apply lemmas of Mathlib's
`AlgHom.prodMap`.

Since `(1, 0)` is idempotent, a ring homomorphism from a product `E₁ × E₂` to a semiring with
cancellation of nonzero factors (`IsLeftCancelMulZero`) sends it to `0` or `1`, so it factors
through one of the two projections, and through only one when the target is nontrivial. So
finitely many homomorphisms out of each factor give finitely many out of the product.

## Main declarations

* `AlgHom.map_eq_map_fst`: a `φ` with `φ (1, 0) = 1` ignores its second argument.
* `AlgHom.map_zero_one_eq_zero`: such a `φ` kills the second coordinate unit.
* `AlgHom.prodFirst`: the first-coordinate algebra map attached to such a `φ`.
* `AlgHom.prodFirst_comp_fst`: the coordinate map is a factorisation -- precomposing with the first
  projection returns `φ`.
* `AlgHom.prodFirst_surjective_iff`: it is surjective exactly when `φ` is.
* `AlgHom.coe_prodMap`, `AlgHom.prodMap_apply`: `f.prodMap g` acts as `Prod.map f g`.
* `RingHom.exists_eq_comp_fst_or_snd`: a ring homomorphism out of `E₁ × E₂` factors through a
  projection.
* `RingHom.comp_fst_ne_comp_snd`, `RingHom.disjoint_image_comp_fst_image_comp_snd`,
  `RingHom.comp_fst_mem_union_iff`, `RingHom.comp_snd_mem_union_iff`: over a nontrivial target it
  factors through only one.
* `RingHom.instFiniteProd`: finitely many homomorphisms out of each factor give finitely many out of
  the product.
-/

public section

namespace AlgHom

section Semiring

variable {F A C B : Type*} [CommSemiring F] [Semiring A] [Algebra F A] [Semiring C] [Algebra F C]
  [Semiring B] [Algebra F B]

/-- **`φ` ignores its second argument**, once `φ (1, 0) = 1`: right multiplication by `(1, 0)`
zeroes the second coordinate, and `φ` sends it to `1`. -/
theorem map_eq_map_fst (φ : (A × C) →ₐ[F] B) (hu : φ (1, 0) = 1) (p : A × C) :
    φ p = φ (p.1, 0) := by
  rw [← mul_one (φ p), ← hu, ← map_mul]
  simp [Prod.mul_def]

/-- **The second coordinate unit is killed**, once `φ (1, 0) = 1`. The two coordinate units
annihilate each other in the product, so this holds over an arbitrary semiring and needs no
additive cancellation. -/
@[simp]
theorem map_zero_one_eq_zero (φ : (A × C) →ₐ[F] B) (hu : φ (1, 0) = 1) : φ (0, 1) = 0 := by
  rw [map_eq_map_fst φ hu, Prod.mk_zero_zero, map_zero]

/-- The coordinate map `a ↦ φ (a, 0)` attached to an algebra map out of a product, packaged as an
algebra map once the image of `(1, 0)` is known to be the unit. It is multiplicative and linear for
every `φ`; unitality is exactly the hypothesis.

Note that `a ↦ (a, 0)` is not itself an algebra map -- it does not preserve `1` -- so this cannot
be obtained by composing `φ` with an inclusion. -/
def prodFirst (φ : (A × C) →ₐ[F] B) (hu : φ (1, 0) = 1) : A →ₐ[F] B where
  __ := φ.toNonUnitalAlgHom.comp (NonUnitalAlgHom.inl F A C)
  map_one' := hu
  commutes' r := by
    -- The inherited non-unital hom is `a ↦ φ (a, 0)` by definition; state it so that the
    -- rewrites below can act on `φ`.
    change φ (algebraMap F A r, 0) = algebraMap F B r
    rw [← φ.commutes, map_eq_map_fst φ hu (algebraMap F (A × C) r), Prod.algebraMap_apply]

/-- The first coordinate map is what its name says: `a ↦ φ (a, 0)`. -/
@[simp]
theorem prodFirst_apply (φ : (A × C) →ₐ[F] B) (hu : φ (1, 0) = 1) (a : A) :
    prodFirst φ hu a = φ (a, 0) := (rfl)

/-- **The first coordinate map really is a factorisation of `φ`**: precomposing it with the first
projection returns `φ`. -/
@[simp]
theorem prodFirst_comp_fst (φ : (A × C) →ₐ[F] B) (hu : φ (1, 0) = 1) :
    (prodFirst φ hu).comp (AlgHom.fst F A C) = φ :=
  AlgHom.ext fun p => (map_eq_map_fst φ hu p).symm

/-- **The first coordinate map is surjective exactly when `φ` is**, since `φ` factors through it
along the surjective first projection. -/
theorem prodFirst_surjective_iff (φ : (A × C) →ₐ[F] B) (hu : φ (1, 0) = 1) :
    Function.Surjective (prodFirst φ hu) ↔ Function.Surjective φ := by
  conv_rhs => rw [← prodFirst_comp_fst φ hu, AlgHom.coe_comp]
  exact (Function.Surjective.of_comp_iff _ Prod.fst_surjective).symm

/-- The product map `f.prodMap g` is `Prod.map f g` as a function. -/
@[simp]
theorem coe_prodMap {D : Type*} [Semiring D] [Algebra F D] (f : A →ₐ[F] B) (g : C →ₐ[F] D) :
    ⇑(f.prodMap g) = Prod.map f g :=
  (rfl)

/-- The product map `f.prodMap g` applies `f` and `g` coordinatewise. -/
theorem prodMap_apply {D : Type*} [Semiring D] [Algebra F D] (f : A →ₐ[F] B) (g : C →ₐ[F] D)
    (p : A × C) : f.prodMap g p = (f p.1, g p.2) :=
  (rfl)

end Semiring

end AlgHom

namespace RingHom

variable {E₁ E₂ K : Type*} [Semiring E₁] [Semiring E₂] [Semiring K]

/-- Precomposition with the first projection is injective on ring homomorphisms. -/
theorem comp_fst_injective :
    Function.Injective fun ψ : E₁ →+* K ↦ ψ.comp (RingHom.fst E₁ E₂) :=
  fun _ _ h ↦ (RingHom.cancel_right Prod.fst_surjective).mp h

/-- Precomposition with the second projection is injective on ring homomorphisms. -/
theorem comp_snd_injective :
    Function.Injective fun ψ : E₂ →+* K ↦ ψ.comp (RingHom.snd E₁ E₂) :=
  fun _ _ h ↦ (RingHom.cancel_right Prod.snd_surjective).mp h

/-- No ring homomorphism from `E₁ × E₂` to a nontrivial semiring factors through both
projections. -/
theorem comp_fst_ne_comp_snd [Nontrivial K] (ψ₁ : E₁ →+* K) (ψ₂ : E₂ →+* K) :
    ψ₁.comp (RingHom.fst E₁ E₂) ≠ ψ₂.comp (RingHom.snd E₁ E₂) := fun h ↦ by
  simpa using congr($h (1, 0))

/-- Homomorphisms factoring through `fst` and homomorphisms factoring through `snd` form disjoint
sets of ring homomorphisms from `E₁ × E₂` to a nontrivial semiring. -/
theorem disjoint_image_comp_fst_image_comp_snd [Nontrivial K] (s₁ : Set (E₁ →+* K))
    (s₂ : Set (E₂ →+* K)) :
    Disjoint ((fun ψ : E₁ →+* K ↦ ψ.comp (RingHom.fst E₁ E₂)) '' s₁)
      ((fun ψ : E₂ →+* K ↦ ψ.comp (RingHom.snd E₁ E₂)) '' s₂) :=
  Set.disjoint_left.mpr fun _ ⟨ψ₁, _, h₁⟩ ⟨ψ₂, _, h₂⟩ ↦
    comp_fst_ne_comp_snd ψ₁ ψ₂ (h₁.trans h₂.symm)

/-- `ψ ∘ fst` lies in the union of the images of `s₁` under `· ∘ fst` and of `s₂` under `· ∘ snd`
exactly when `ψ ∈ s₁`. -/
theorem comp_fst_mem_union_iff [Nontrivial K] {s₁ : Set (E₁ →+* K)} {s₂ : Set (E₂ →+* K)}
    {ψ : E₁ →+* K} :
    ψ.comp (RingHom.fst E₁ E₂) ∈ (fun ψ : E₁ →+* K ↦ ψ.comp (RingHom.fst E₁ E₂)) '' s₁ ∪
      (fun ψ : E₂ →+* K ↦ ψ.comp (RingHom.snd E₁ E₂)) '' s₂ ↔ ψ ∈ s₁ := by
  simp only [Set.mem_union, Set.mem_image, comp_fst_injective.eq_iff, exists_eq_right]
  exact or_iff_left fun ⟨ψ₂, _, h⟩ ↦ comp_fst_ne_comp_snd ψ ψ₂ h.symm

/-- `ψ ∘ snd` lies in the union of the images of `s₁` under `· ∘ fst` and of `s₂` under `· ∘ snd`
exactly when `ψ ∈ s₂`. -/
theorem comp_snd_mem_union_iff [Nontrivial K] {s₁ : Set (E₁ →+* K)} {s₂ : Set (E₂ →+* K)}
    {ψ : E₂ →+* K} :
    ψ.comp (RingHom.snd E₁ E₂) ∈ (fun ψ : E₁ →+* K ↦ ψ.comp (RingHom.fst E₁ E₂)) '' s₁ ∪
      (fun ψ : E₂ →+* K ↦ ψ.comp (RingHom.snd E₁ E₂)) '' s₂ ↔ ψ ∈ s₂ := by
  simp only [Set.mem_union, Set.mem_image, comp_snd_injective.eq_iff, exists_eq_right]
  exact or_iff_right fun ⟨ψ₁, _, h⟩ ↦ comp_fst_ne_comp_snd ψ₁ ψ h

/-- **A ring homomorphism from a product to a semiring with cancellation of nonzero factors
(`IsLeftCancelMulZero`) factors through a projection.** -/
theorem exists_eq_comp_fst_or_snd [IsLeftCancelMulZero K] (φ : E₁ × E₂ →+* K) :
    (∃ ψ : E₁ →+* K, φ = ψ.comp (RingHom.fst E₁ E₂)) ∨
      ∃ ψ : E₂ →+* K, φ = ψ.comp (RingHom.snd E₁ E₂) := by
  -- The image of the idempotent `(1, 0)` is `0` or `1`. When it is `1`, `AlgHom.prodFirst` gives
  -- the factorization through `fst`; when it is `0`, the image of `(0, 1)` is `1` and the same
  -- applies after swapping the factors.
  have hidem : IsIdempotentElem (φ (1, 0)) := by
    rw [IsIdempotentElem, ← map_mul, Prod.mk_mul_mk, one_mul, zero_mul]
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hidem with h | h
  · -- `φ (0, 1) = 1`, so `φ ∘ swap` factors through `fst` and `φ` through `snd`
    have h1 : φ (0, 1) = 1 := by
      rw [← map_one φ, show (1 : E₁ × E₂) = (1, 0) + (0, 1) by ext <;> simp, map_add, h, zero_add]
    let φ' := (φ.comp (RingEquiv.prodComm (R := E₂) (S := E₁)).toRingHom).toNatAlgHom
    have h1' : φ' (1, 0) = 1 := by simpa [φ'] using h1
    exact .inr ⟨(φ'.prodFirst h1').toRingHom,
      RingHom.ext fun x ↦ by
        -- `φ'` is `φ ∘ swap`, so `φ' x.swap = φ x.swap.swap = φ x`
        have hx : φ' x.swap = φ x := by simp [φ']
        rw [← hx]
        exact (DFunLike.congr_fun (φ'.prodFirst_comp_fst h1') x.swap).symm⟩
  · exact .inl ⟨(φ.toNatAlgHom.prodFirst h).toRingHom,
      RingHom.ext fun x ↦ (DFunLike.congr_fun (φ.toNatAlgHom.prodFirst_comp_fst h) x).symm⟩

/-- A product of semirings with finitely many homomorphisms to a semiring with cancellation of
nonzero factors (`IsLeftCancelMulZero`) has finitely many. -/
instance instFiniteProd [IsLeftCancelMulZero K] [_root_.Finite (E₁ →+* K)]
    [_root_.Finite (E₂ →+* K)] : _root_.Finite (E₁ × E₂ →+* K) :=
  _root_.Finite.of_surjective
    (Sum.elim (fun ψ : E₁ →+* K ↦ ψ.comp (RingHom.fst E₁ E₂))
      (fun ψ : E₂ →+* K ↦ ψ.comp (RingHom.snd E₁ E₂)))
    fun φ : E₁ × E₂ →+* K ↦ by
      rcases φ.exists_eq_comp_fst_or_snd with ⟨ψ, rfl⟩ | ⟨ψ, rfl⟩
      exacts [⟨.inl ψ, rfl⟩, ⟨.inr ψ, rfl⟩]

end RingHom

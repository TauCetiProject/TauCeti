/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: `AlgHom`, `RingHom.toAlgebra` and `algebraMap` all occur in the statement below.
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Bridging lemmas between `AlgHom` and `RingHom`

Two small families of identities relating the bundled homomorphism types, each of which several
files would otherwise restate inline, together with a few further facts about algebra
homomorphisms: their action on images of units of the base ring, the maximality of the kernel of
an augmentation to the ground field, the promotion of an algebra homomorphism between
finite-dimensional algebras of equal finrank to an algebra equivalence, and the ranges of
composition maps on algebra homomorphisms.

## The structure map of the algebra induced by an algebra homomorphism

An algebra homomorphism `f : A →ₐ[R] B` induces an `A`-algebra structure on `B`, namely
`f.toRingHom.toAlgebra`. Mathlib's `RingHom.algebraMap_toAlgebra` identifies the structure map of
that algebra with the homomorphism it was built from, but states it as an equality of *bundled ring
homomorphisms*. Every consumer that has to feed a hypothesis of the form `∀ z, algebraMap A B z =
f z` therefore applies it pointwise by hand, through `congrArg DFunLike.coe` and `congrFun`.

This file states the pointwise form once, for an `AlgHom`, which is the shape those consumers want:
the right-hand side is `f z` rather than `f.toRingHom z`.

## Functoriality of `RingHom.toIntAlgHom`

Every ring is a `ℤ`-algebra, so a ring homomorphism is a `ℤ`-algebra homomorphism; Mathlib bundles
that as `RingHom.toIntAlgHom` but carries no *named* identity, composition or round-trip lemma for
it; the round-trips are reachable only through `RingHom.equivIntAlgHom`, which is not the shape
`rw` wants. Any file transporting an equality of ring homomorphisms into `AlgHom` needs these, and
several do.

## Main results

* `AlgHom.algebraMap_toAlgebra_apply`: `algebraMap A B z = f z` for the algebra structure
  `f.toRingHom.toAlgebra` induced by `f : A →ₐ[R] B`.
* `RingHom.toIntAlgHom_id`, `RingHom.toIntAlgHom_comp`: `RingHom.toIntAlgHom` is functorial.
* `RingHom.toIntAlgHom_toRingHom`, `AlgHom.toRingHom_toIntAlgHom`: it is inverse to
  `AlgHom.toRingHom` in both directions.
* `AlgHom.units_map_units_map_algebraMap`: an algebra homomorphism sends the image of a unit of
  the base ring to the image of the same unit.
* `AlgHom.ker_isMaximal`: the kernel of an augmentation `H →ₐ[k] k` to a field is a maximal
  ideal, for any (not necessarily commutative) `k`-algebra `H`.
* `AlgHom.algEquivOfFinrankEq`: an algebra homomorphism from a finite-dimensional division algebra
  to an algebra of the same finrank is an algebra equivalence. It is the algebra analogue of
  Mathlib's `LinearMap.linearEquivOfInjective`, with injectivity supplied by the division-ring
  source.
* `AlgHom.range_comp_left_of_injective`, `AlgHom.range_comp_left_eq_of_adjoin_eq_top` and
  `AlgHom.range_comp_right_of_surjective`: ranges of composition maps on algebra homomorphisms,
  characterized by lifting values and by vanishing on a kernel.
* `AlgHom.descend`: an algebra homomorphism constant on the fibres of a surjective algebra
  homomorphism descends along it, over arbitrary semirings; `AlgHom.descend_unique` says the
  descent is the only homomorphism factoring it.

## Implementation notes

### The structure map

The codomain is a `CommSemiring`, not a `Semiring`. That is forced rather than chosen:
`RingHom.toAlgebra` is itself stated for `[CommSemiring R] [CommSemiring S]`
(`Mathlib/Algebra/Algebra/Defs.lean`), so the algebra instance this lemma is about does not exist
over a bare semiring codomain. The `Semiring` version of the construction is `RingHom.toAlgebra'`,
which takes a commutation hypothesis `∀ c x, i c * x = x * i c` and is a different instance; a
lemma about it would not apply to any of the call sites here, all of which build their algebra with
the unprimed `toAlgebra`.

This is original work, not ported: Mathlib carries the un-applied `RingHom.algebraMap_toAlgebra`
but no pointwise `AlgHom` form, though it does carry the analogous `_apply` lemmas for the other
`AlgHom` coercions (`AlgHom.toLinearMap_apply`, `AlgHom.toLieHom_apply`).

### Functoriality of `RingHom.toIntAlgHom`

The two round-trip lemmas are stated through the coercion rather than `.toRingHom`, because
Mathlib's `AlgHom.toRingHom_eq_coe` is a `simp` lemma making the coercion the simp-normal form:
a `.toRingHom` left-hand side is rewritten before the lemma can fire, so the `simp` attribute
would be dead.
-/

public section

/-- **The structure map of `f.toRingHom.toAlgebra` is `f`**, pointwise. Mathlib's
`RingHom.algebraMap_toAlgebra` is the same fact as an equality of bundled ring homomorphisms; this
is the applied form, stated for an `AlgHom` so that the right-hand side is `f z`.

Consumers wanting a hypothesis `∀ z, algebraMap A B z = f z` can pass this lemma directly, since
`z` is explicit. -/
-- Proved from `RingHom.algebraMap_toAlgebra` and `AlgHom.coe_toRingHom` rather than by `rfl`:
-- both sides are definitionally equal, but `rfl` closes the goal only by reducing through
-- `toRingHom`, `toAlgebra`, `algebraMap` and two coercions -- exactly the fragile defeq this
-- lemma exists to spare its call sites.
theorem AlgHom.algebraMap_toAlgebra_apply {R A B : Type*} [CommSemiring R] [CommSemiring A]
    [CommSemiring B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (z : A) :
    @algebraMap A B _ _ f.toRingHom.toAlgebra z = f z := by
  rw [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

/-! ### Functoriality of `RingHom.toIntAlgHom` -/

section ToIntAlgHom

variable {R : Type*} {S : Type*} {T : Type*} [Ring R] [Ring S] [Ring T]

/-- `RingHom.toIntAlgHom` sends the identity ring homomorphism to the identity `ℤ`-algebra
homomorphism. -/
@[simp]
theorem RingHom.toIntAlgHom_id : (RingHom.id R).toIntAlgHom = AlgHom.id ℤ R :=
  AlgHom.ext fun _ ↦ rfl

/-- `RingHom.toIntAlgHom` preserves composition. -/
@[simp]
theorem RingHom.toIntAlgHom_comp (f : S →+* T) (g : R →+* S) :
    (f.comp g).toIntAlgHom = f.toIntAlgHom.comp g.toIntAlgHom :=
  AlgHom.ext fun _ ↦ rfl

/-- Reading a ring homomorphism as a `ℤ`-algebra homomorphism and back recovers it: composing
`AlgHom.toRingHom` after `RingHom.toIntAlgHom` is the identity, so `RingHom.toIntAlgHom` is a
right inverse of `AlgHom.toRingHom`.

Stated through the coercion rather than `.toRingHom`, because Mathlib's `AlgHom.toRingHom_eq_coe`
is a `simp` lemma making the coercion the simp-normal form; a `.toRingHom` left-hand side would
be rewritten before this could fire. -/
@[simp]
theorem RingHom.toIntAlgHom_toRingHom (f : R →+* S) : (f.toIntAlgHom : R →+* S) = f :=
  RingHom.ext fun _ ↦ rfl

/-- Reading a `ℤ`-algebra homomorphism as a ring homomorphism and back recovers it: composing
`RingHom.toIntAlgHom` after `AlgHom.toRingHom` is the identity, so `RingHom.toIntAlgHom` is a
left inverse of `AlgHom.toRingHom`.

Stated through the coercion, for the reason given above. -/
@[simp]
theorem AlgHom.toRingHom_toIntAlgHom (φ : R →ₐ[ℤ] S) : (φ : R →+* S).toIntAlgHom = φ :=
  AlgHom.ext fun _ ↦ rfl

end ToIntAlgHom

/-! ### Images of units of the base ring -/

/-- An `R`-algebra homomorphism sends the image in `A` of a unit of `R` to its image in `B`. It
is stated through the ring homomorphism coercion, the form in which `Units.map` of an algebra
homomorphism arises from constructions over ring homomorphisms. -/
theorem AlgHom.units_map_units_map_algebraMap {R A B : Type*} [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (q : Rˣ) :
    Units.map ((f : A →+* B) : A →* B) (Units.map (algebraMap R A : R →* A) q) =
      Units.map (algebraMap R B : R →* B) q :=
  Units.ext (f.commutes q)

/-! ### The kernel of an augmentation -/

/-- The kernel of an augmentation to a field is a maximal ideal, even when the algebra is
not commutative. -/
instance AlgHom.ker_isMaximal {k H : Type*} [Field k] [Ring H] [Algebra k H]
    (f : H →ₐ[k] k) : (RingHom.ker (f : H →+* k)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (f : H →+* k)
    (fun r ↦ ⟨algebraMap k H r, f.commutes r⟩)

/-! ### Algebra equivalences from equal finrank -/

section FinrankEq

variable {K L M : Type*} [Field K] [DivisionRing L] [Semiring M] [Algebra K L] [Algebra K M]
  [FiniteDimensional K L]

/-- An algebra homomorphism from a finite-dimensional division algebra to an algebra of the same
finrank promotes to an algebra equivalence. The equality of finranks forces the target to be
finite-dimensional, so that is not assumed. This is the algebra analogue of
Mathlib's `LinearMap.linearEquivOfInjective`. -/
noncomputable def AlgHom.algEquivOfFinrankEq (f : L →ₐ[K] M)
    (hfin : Module.finrank K L = Module.finrank K M) : L ≃ₐ[K] M :=
  letI := Algebra.semiringToRing (A := M) K
  haveI : Nontrivial M := Module.nontrivial_of_finrank_pos (R := K) (hfin ▸ Module.finrank_pos)
  haveI : Module.Finite K M := Module.finite_of_finrank_pos (hfin ▸ Module.finrank_pos)
  AlgEquiv.ofBijective f
    ⟨f.injective, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
      (f := f.toLinearMap)).mp f.injective⟩

/-- The algebra equivalence `AlgHom.algEquivOfFinrankEq` acts as the homomorphism it promotes. -/
@[simp]
theorem AlgHom.algEquivOfFinrankEq_apply (f : L →ₐ[K] M)
    (hfin : Module.finrank K L = Module.finrank K M) (x : L) :
    f.algEquivOfFinrankEq hfin x = f x :=
  AlgEquiv.ofBijective_apply f _ x

end FinrankEq

/-! ### Ranges of composition maps -/

section Ranges

variable {k A R S : Type*} [CommSemiring k]
  [Semiring A] [Algebra k A] [Semiring R] [Algebra k R] [Semiring S] [Algebra k S]

/-- A homomorphism lifts through an injective coefficient map exactly when all its values lie
in the image. -/
theorem AlgHom.range_comp_left_of_injective (ψ : R →ₐ[k] S) (hψ : Function.Injective ψ) :
    Set.range (fun x : A →ₐ[k] R ↦ ψ.comp x) =
      {x | ∀ a, x a ∈ Set.range ψ} := by
  ext x
  refine ⟨fun ⟨y, hy⟩ a ↦ ⟨y a, by simp [← hy]⟩, fun hx ↦ ?_⟩
  refine ⟨(AlgEquiv.ofInjective ψ hψ).symm.toAlgHom.comp (x.codRestrict ψ.range hx),
    AlgHom.ext fun a ↦ ?_⟩
  exact congrArg Subtype.val ((AlgEquiv.ofInjective ψ hψ).apply_symm_apply ⟨x a, hx a⟩)

/-- Lifting through an injective coefficient map can be tested on any algebra generating family. -/
theorem AlgHom.range_comp_left_eq_of_adjoin_eq_top (ψ : R →ₐ[k] S)
    (hψ : Function.Injective ψ) {ι : Type*} {a : ι → A}
    (ha : Algebra.adjoin k (Set.range a) = ⊤) :
    Set.range (fun x : A →ₐ[k] R ↦ ψ.comp x) =
      {x | ∀ i, x (a i) ∈ Set.range ψ} := by
  rw [AlgHom.range_comp_left_of_injective ψ hψ]
  ext x
  refine ⟨fun hx i ↦ hx (a i), fun hx b ↦ ?_⟩
  have hle : Algebra.adjoin k (Set.range a) ≤ ψ.range.comap x :=
    Algebra.adjoin_le (Set.range_subset_iff.2 hx)
  exact hle (ha ▸ Algebra.mem_top)

end Ranges

/-- Precomposition by a surjection has image the homomorphisms vanishing on its kernel. -/
theorem AlgHom.range_comp_right_of_surjective {k A B R : Type*}
    [CommSemiring k] [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    [Ring R] [Algebra k R] (φ : B →ₐ[k] A) (hφ : Function.Surjective φ) :
    Set.range (fun x : A →ₐ[k] R ↦ x.comp φ) =
      {x | ∀ b ∈ RingHom.ker φ, x b = 0} := by
  ext x
  refine ⟨fun ⟨y, hy⟩ b hb ↦ ?_, fun hx ↦ ?_⟩
  · rw [← hy, AlgHom.comp_apply, RingHom.mem_ker.mp hb, map_zero]
  · let g : {g : B →+* R // RingHom.ker φ ≤ RingHom.ker g} := ⟨x.toRingHom, hx⟩
    let y := φ.toRingHom.liftOfSurjective hφ g
    have hy (b : B) : y (φ b) = x b :=
      RingHom.liftOfSurjective_comp_apply φ.toRingHom hφ g b
    refine ⟨{ y with commutes' := ?_ }, AlgHom.ext hy⟩
    intro c
    exact (congrArg y (φ.commutes c)).symm.trans ((hy _).trans (x.commutes c))

/-! ### Descending along a surjection -/

section Descend

variable {R A B C : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
  [Algebra R A] [Algebra R B] [Algebra R C]

/-- An algebra homomorphism `φ : A →ₐ[R] C` that is constant on the fibres of a surjective
algebra homomorphism `g : A →ₐ[R] B` descends to `B →ₐ[R] C`. Unlike Mathlib's
`AlgHom.liftOfSurjective`, which asks for a kernel inclusion, this needs no ring structure. -/
noncomputable def AlgHom.descend (g : A →ₐ[R] B) (hg : Function.Surjective g) (φ : A →ₐ[R] C)
    (h : ∀ a b, g a = g b → φ a = φ b) : B →ₐ[R] C where
  toFun x := φ (Function.surjInv hg x)
  map_one' := (h _ _ (by rw [Function.surjInv_eq hg, map_one])).trans (map_one φ)
  map_mul' x y := (h _ _ (by rw [map_mul, Function.surjInv_eq hg, Function.surjInv_eq hg,
    Function.surjInv_eq hg])).trans (map_mul φ _ _)
  map_zero' := (h _ _ (by rw [Function.surjInv_eq hg, map_zero])).trans (map_zero φ)
  map_add' x y := (h _ _ (by rw [map_add, Function.surjInv_eq hg, Function.surjInv_eq hg,
    Function.surjInv_eq hg])).trans (map_add φ _ _)
  commutes' c := (h _ _ (by rw [Function.surjInv_eq hg, AlgHom.commutes])).trans (φ.commutes c)

/-- The descent of `φ` along `g` sends `g a` to `φ a`. -/
@[simp]
theorem AlgHom.descend_apply (g : A →ₐ[R] B) (hg : Function.Surjective g) (φ : A →ₐ[R] C)
    (h : ∀ a b, g a = g b → φ a = φ b) (a : A) : g.descend hg φ h (g a) = φ a :=
  h _ _ (Function.surjInv_eq hg (g a))

/-- The descent of `φ` along `g`, composed with `g`, is `φ`. -/
@[simp]
theorem AlgHom.descend_comp (g : A →ₐ[R] B) (hg : Function.Surjective g) (φ : A →ₐ[R] C)
    (h : ∀ a b, g a = g b → φ a = φ b) : (g.descend hg φ h).comp g = φ :=
  AlgHom.ext (g.descend_apply hg φ h)

/-- The descent of `φ` along `g` is the only homomorphism whose composite with `g` is `φ`. -/
theorem AlgHom.descend_unique (g : A →ₐ[R] B) (hg : Function.Surjective g) (φ : A →ₐ[R] C)
    (h : ∀ a b, g a = g b → φ a = φ b) (ψ : B →ₐ[R] C) (hψ : ψ.comp g = φ) :
    ψ = g.descend hg φ h :=
  AlgHom.ext <| hg.forall.mpr fun a ↦
    (DFunLike.congr_fun hψ a).trans (g.descend_apply hg φ h a).symm

end Descend

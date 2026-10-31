/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Extension
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Extensions built from 2-cocycles

A 2-cocycle `c` of a Lie algebra `L` with values in an `L`-module `M` shears the bracket of `L × M`.
Mathlib's `LieAlgebra.ofTwoCocycle c` is this Lie algebra, and Mathlib packages it as an extension
(`LieAlgebra.Extension.ofTwoCocycle`) only when `M` is itself given the structure of an abelian Lie
algebra.

This file works with an arbitrary module `M` and supplies:

* `LieAlgebra.ofProdLinearEquiv`: the identification `LieAlgebra.ofProd` with `L × M` as a linear
  equivalence, so that finiteness transfers to `LieAlgebra.ofTwoCocycle c`;
* `LieAlgebra.ofTwoCocycle.proj`: the projection onto `L` as a surjective Lie algebra
  homomorphism, whose kernel `0 × M` is an abelian ideal;
* `LieAlgebra.ofTwoCocycle.map` and `LieAlgebra.ofTwoCocycle.mapEquiv`: for trivial coefficients,
  the morphisms and isomorphisms of central extensions `(x, m) ↦ (φ x, e m)` induced by a map `φ`
  of the quotients and a linear map `e` of the kernels carrying one cocycle to the other.

The construction of `map` and `mapEquiv` follows Mathlib's `LieAlgebra.LieEquiv.ofCoboundary`,
which identifies the extensions of cohomologous cocycles by acting on the coordinates of `ofProd`.
Here the coordinates are instead transformed by a map of quotients and a map of kernels.

These let structure theorems about abelian ideals, such as the existence of Levi complements, be
applied to the sheared Lie algebra, for instance to show that a 2-cocycle is a coboundary. The
morphisms of central extensions compare the extensions attached to proportional cocycles, and an
extension with its restriction to a subalgebra. The degree-one counterpart, the module sheared by
a Lie derivation, is `LieDerivation.ShearedModule` in `TauCeti.Algebra.Lie.Derivation.Cocycle`.
-/

public section

open LieModule.Cohomology

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M]

namespace LieAlgebra

variable (c : twoCocycle R L M)

/-- The identification `LieAlgebra.ofProd` of `L × M` with the Lie algebra sheared by a 2-cocycle,
as a linear equivalence. -/
def ofProdLinearEquiv : (L × M) ≃ₗ[R] ofTwoCocycle c where
  __ := ofProd c
  map_add' := of_add c
  map_smul' := of_smul c

@[simp]
lemma coe_ofProdLinearEquiv : ⇑(ofProdLinearEquiv c) = ofProd c := (rfl)

@[simp]
lemma coe_ofProdLinearEquiv_symm : ⇑(ofProdLinearEquiv c).symm = (ofProd c).symm := (rfl)

instance [Module.Finite R L] [Module.Finite R M] : Module.Finite R (ofTwoCocycle c) :=
  Module.Finite.equiv (ofProdLinearEquiv c)

namespace ofTwoCocycle

/-- The projection of the Lie algebra sheared by a 2-cocycle onto `L`, as a Lie algebra
homomorphism. -/
def proj : ofTwoCocycle c →ₗ⁅R⁆ L where
  toFun x := ((ofProd c).symm x).1
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  map_lie' {_ _} := by simp [bracket_ofTwoCocycle]

@[simp]
lemma proj_apply (x : ofTwoCocycle c) : proj c x = ((ofProd c).symm x).1 := (rfl)

lemma proj_surjective : Function.Surjective (proj c) :=
  fun x ↦ ⟨ofProd c (x, 0), by simp⟩

lemma mem_ker_proj {x : ofTwoCocycle c} : x ∈ (proj c).ker ↔ ((ofProd c).symm x).1 = 0 :=
  LieHom.mem_ker

/-- The kernel `0 × M` of the projection is an abelian ideal. -/
instance : IsLieAbelian (proj c).ker where
  trivial a b := by
    have ha := (mem_ker_proj c).1 a.2
    have hb := (mem_ker_proj c).1 b.2
    refine Subtype.ext ((ofProd c).symm.injective ?_)
    simp [bracket_ofTwoCocycle, ha, hb]

section Trivial

/-! ### Morphisms of central extensions -/

variable {L' M' : Type*} [LieRing L'] [LieAlgebra R L'] [AddCommGroup M'] [Module R M']
  [LieRingModule L' M'] [LieModule R L' M'] [LieModule.IsTrivial L M] [LieModule.IsTrivial L' M']

/-- The morphism of central extensions `(x, m) ↦ (φ x, e m)` from the Lie algebra sheared by a
2-cocycle `c` with trivial coefficients to the one sheared by `c'`, for a Lie algebra morphism `φ`
and a linear map `e` of coefficients such that `c' (φ x) (φ y) = e (c x y)`.

With `φ` the identity this pushes an extension forward along a map of its kernels; with `e` the
identity it compares an extension with the pullback of another along `φ`. -/
def map (φ : L →ₗ⁅R⁆ L') (e : M →ₗ[R] M') (c' : twoCocycle R L' M')
    (h : ∀ x y, (c' : twoCochain R L' M') (φ x) (φ y) = e ((c : twoCochain R L M) x y)) :
    ofTwoCocycle c →ₗ⁅R⁆ ofTwoCocycle c' where
  toFun v := ofProd c' (φ ((ofProd c).symm v).1, e ((ofProd c).symm v).2)
  map_add' _ _ := by simp [← of_add]
  map_smul' _ _ := by simp [← of_smul]
  map_lie' {_ _} := by simp [bracket_ofTwoCocycle, trivial_lie_zero, h]

section Map

variable (φ : L →ₗ⁅R⁆ L') (e : M →ₗ[R] M') (c' : twoCocycle R L' M')
  (h : ∀ x y, (c' : twoCochain R L' M') (φ x) (φ y) = e ((c : twoCochain R L M) x y))

/-- A morphism of central extensions acts by `φ` on the first coordinate and `e` on the
second. -/
@[simp]
lemma map_ofProd (x : L) (m : M) : map c φ e c' h (ofProd c (x, m)) = ofProd c' (φ x, e m) :=
  (rfl)

@[simp]
lemma ofProd_symm_map (v : ofTwoCocycle c) :
    (ofProd c').symm (map c φ e c' h v) = (φ ((ofProd c).symm v).1, e ((ofProd c).symm v).2) :=
  (rfl)

/-- A morphism of central extensions lies over the morphism `φ` of the quotients. -/
lemma proj_map (v : ofTwoCocycle c) : proj c' (map c φ e c' h v) = φ (proj c v) :=
  (rfl)

/-- The identity morphism of a central extension. -/
@[simp]
lemma map_id : map c (LieHom.id : L →ₗ⁅R⁆ L) LinearMap.id c (fun _ _ ↦ rfl) = LieHom.id :=
  LieHom.ext fun _ ↦ rfl

/-- Morphisms of central extensions compose by composing the maps of quotients and kernels. -/
lemma map_comp {L'' M'' : Type*} [LieRing L''] [LieAlgebra R L''] [AddCommGroup M'']
    [Module R M''] [LieRingModule L'' M''] [LieModule R L'' M''] [LieModule.IsTrivial L'' M'']
    (φ' : L' →ₗ⁅R⁆ L'') (e' : M' →ₗ[R] M'') (c'' : twoCocycle R L'' M'')
    (h' : ∀ x y, (c'' : twoCochain R L'' M'') (φ' x) (φ' y) = e' ((c' : twoCochain R L' M') x y)) :
    (map c' φ' e' c'' h').comp (map c φ e c' h) =
      map c (φ'.comp φ) (e' ∘ₗ e) c'' (fun x y ↦ by simp [h', h]) :=
  LieHom.ext fun _ ↦ rfl

/-- A morphism of central extensions is injective when the maps of quotients and kernels are. -/
lemma map_injective (hφ : Function.Injective φ) (he : Function.Injective e) :
    Function.Injective (map c φ e c' h) :=
  (ofProd c').injective.comp ((hφ.prodMap he).comp (ofProd c).symm.injective)

/-- A morphism of central extensions is surjective when the maps of quotients and kernels are. -/
lemma map_surjective (hφ : Function.Surjective φ) (he : Function.Surjective e) :
    Function.Surjective (map c φ e c' h) :=
  (ofProd c').surjective.comp ((hφ.prodMap he).comp (ofProd c).symm.surjective)

end Map

variable (φ : L ≃ₗ⁅R⁆ L') (e : M ≃ₗ[R] M') (c' : twoCocycle R L' M')
  (h : ∀ x y, (c' : twoCochain R L' M') (φ x) (φ y) = e ((c : twoCochain R L M) x y))

/-- The isomorphism of central extensions `(x, m) ↦ (φ x, e m)` induced by isomorphisms `φ` of
the quotients and `e` of the kernels such that `c' (φ x) (φ y) = e (c x y)`. -/
def mapEquiv : ofTwoCocycle c ≃ₗ⁅R⁆ ofTwoCocycle c' where
  __ := map c φ.toLieHom e.toLinearMap c' h
  invFun := map c' φ.symm.toLieHom e.symm.toLinearMap c fun x y ↦ by
    simpa using congrArg e.symm (h (φ.symm x) (φ.symm y)).symm
  left_inv v := (ofProd c).symm.injective (by simp)
  right_inv v := (ofProd c').symm.injective (by simp)

@[simp]
lemma mapEquiv_ofProd (x : L) (m : M) :
    mapEquiv c φ e c' h (ofProd c (x, m)) = ofProd c' (φ x, e m) :=
  (rfl)

@[simp]
lemma ofProd_symm_mapEquiv (v : ofTwoCocycle c) :
    (ofProd c').symm (mapEquiv c φ e c' h v) = (φ ((ofProd c).symm v).1, e ((ofProd c).symm v).2) :=
  (rfl)

@[simp]
lemma mapEquiv_symm_ofProd (x : L') (m : M') :
    (mapEquiv c φ e c' h).symm (ofProd c' (x, m)) = ofProd c (φ.symm x, e.symm m) :=
  (rfl)

@[simp]
lemma toLieHom_mapEquiv :
    (mapEquiv c φ e c' h).toLieHom = map c φ.toLieHom e.toLinearMap c' h :=
  (rfl)

end Trivial

end ofTwoCocycle

end LieAlgebra

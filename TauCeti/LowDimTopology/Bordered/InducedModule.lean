/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.TypeD

/-!
# The differential module induced by a type `D` structure

A type `D` structure `N` over a differential algebra `(A, d)` with ring of idempotents `I` induces
the differential left `A`-module `A ⊠ N = A ⊗_I N`, with differential
`∂ (a ⊗ x) = d a ⊗ x + ∑ y, a * coeff x y ⊗ y`. Lipshitz, Ozsváth and Thurston use this
construction to compare type `D` structures with ordinary differential modules: the morphism
complex of type `D` structures from `N` to `N'` is isomorphic to the complex of `A`-linear maps
from `A ⊠ N` to `A ⊠ N'`, compatibly with composition and identities. So `N ↦ A ⊠ N` is a fully
faithful functor from type `D` structures to differential left `A`-modules, and homomorphisms and
homotopies of type `D` structures are exactly the chain maps and chain homotopies of the induced
modules.

In the basis of generators `x : X` of `N`, `A ⊠ N` is the left `A`-submodule of row vectors
`φ : X → A` with `φ x * ι (idem x) = φ x` (`TauCeti.TypeDStructure.inducedModule`); as an
`R`-module it is the box tensor product `TauCeti.TypeDStructure.boxTensor` of the regular right
module `A` with `N`. When the `ι s` are idempotents, it is spanned over `A` by the generators
`1 ⊗ x`, the row vectors with `ι (idem x)` in position `x`
(`TauCeti.TypeDStructure.generator`), and every row vector of the submodule is
`φ = ∑ x, φ x • (1 ⊗ x)` (`TauCeti.TypeDStructure.sum_smul_generator`). The induced differential
`TauCeti.TypeDStructure.inducedDifferential` is the box tensor differential, which needs the
`ι s` to be cycles to preserve the submodule; it sends `1 ⊗ x` to the row `coeff x`
(`TauCeti.TypeDStructure.coe_inducedDifferential_generator`).

* **Morphisms.** A morphism `F` of type `D` structures, a matrix of coefficients, acts on row
  vectors by `φ ↦ φ ⬝ F`, an `A`-linear map `A ⊠ N → A ⊠ N'`
  (`TauCeti.TypeDStructure.inducedHom`). It sends `1 ⊗ x` to the row `F x`, and since an `A`-linear
  map is determined by the images of the generators, every `A`-linear map arises from exactly one
  morphism (`TauCeti.TypeDStructure.inducedHomEquiv`). Matrix products go to composites and the
  identity morphism to the identity (`TauCeti.TypeDStructure.inducedHom_mul`,
  `TauCeti.TypeDStructure.inducedHom_idMorphism`).
* **Differentials.** Over a ring of characteristic two, the `A`-linear maps carry the differential
  `∂ T = ∂' ∘ T + T ∘ ∂` (`TauCeti.TypeDStructure.inducedHomDifferential`), which squares to zero.
  It is `A`-linear because `∂ (b • φ) = d b • φ + b • ∂ φ` and the two terms `d b • T φ`
  cancel. Under `inducedHom` it is the morphism differential `∂F = d F + F * δ' + δ * F`
  (`TauCeti.TypeDStructure.inducedHom_morphismDifferential`), and so is its inverse
  (`TauCeti.TypeDStructure.inducedHomEquiv_symm_inducedHomDifferential`). Consequently `F` is a
  homomorphism exactly when `φ ↦ φ ⬝ F` is a chain map
  (`TauCeti.TypeDStructure.morphismDifferential_eq_zero_iff`), and `∂H = F + G` exactly when the
  map of `H` is a chain homotopy between those of `F` and `G`
  (`TauCeti.TypeDStructure.morphismDifferential_eq_add_iff`); every `A`-linear chain homotopy
  between them is the map of a unique such `H`. The differential of `A`-linear maps also
  satisfies the Leibniz rule for composition
  (`TauCeti.TypeDStructure.inducedHomDifferential_comp`), and the identity is a cycle
  (`TauCeti.TypeDStructure.inducedHomDifferential_id`).
* **Objects.** Conversely, let `D` be a differential of `A ⊠ N = A ⊗_I ⟨X⟩` satisfying the Leibniz
  rule `D (b • φ) = d b • φ + b • D φ`. The difference of `D` and the entrywise differential `d`
  is then `A`-linear, so it is `φ ↦ φ ⬝ δ` for a unique morphism `δ`, whose row at `x` is
  `D (1 ⊗ x)`. Evaluating `D² = 0` at the generators `1 ⊗ x` gives the structure equation
  `d δ + δ * δ = 0`. Hence `D` is the box tensor differential of the type `D` structure
  `TauCeti.TypeDStructure.ofInducedDifferential`, the only one with the idempotents of `N`
  (`TauCeti.TypeDStructure.existsUnique_idem_eq_and_boxDifferential_eq`). The induced
  differential of `N` gives back `N`
  (`TauCeti.TypeDStructure.ofInducedDifferential_inducedDifferential`).

## Main definitions

* `TauCeti.TypeDStructure.inducedModule`: the induced left `A`-module `A ⊠ N`.
* `TauCeti.TypeDStructure.generator`: the generator `1 ⊗ x` of `A ⊠ N`.
* `TauCeti.TypeDStructure.inducedDifferential`: the differential of `A ⊠ N`.
* `TauCeti.TypeDStructure.inducedHom`: the `A`-linear map `φ ↦ φ ⬝ F` of a morphism `F`.
* `TauCeti.TypeDStructure.inducedHomEquiv`: morphisms of type `D` structures are the `A`-linear
  maps of the induced modules.
* `TauCeti.TypeDStructure.inducedHomDifferential`: the differential of `A`-linear maps of induced
  modules.
* `TauCeti.TypeDStructure.ofInducedDifferential`: the type `D` structure of a Leibniz differential
  of square zero on an induced module.

## Main results

* `TauCeti.TypeDStructure.inducedHom_morphismDifferential`,
  `TauCeti.TypeDStructure.inducedHomEquiv_symm_inducedHomDifferential`: the morphism complex of
  type `D` structures is isomorphic to the complex of `A`-linear maps of the induced modules.
* `TauCeti.TypeDStructure.inducedHom_mul`, `TauCeti.TypeDStructure.inducedHom_idMorphism`: the
  isomorphism respects composition and identities.
* `TauCeti.TypeDStructure.morphismDifferential_eq_zero_iff`,
  `TauCeti.TypeDStructure.morphismDifferential_eq_add_iff`: homomorphisms and homotopies of type
  `D` structures are the chain maps and chain homotopies of the induced modules.
* `TauCeti.TypeDStructure.inducedHomDifferential_comp`: the Leibniz rule for composition of
  `A`-linear maps of induced modules.
* `TauCeti.TypeDStructure.existsUnique_idem_eq_and_boxDifferential_eq`: every Leibniz differential
  of square zero on an induced module is the box tensor differential of a unique type `D`
  structure with the idempotents of `N`.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  §2.2 (the differential module `A ⊠ N` induced by a type `D` structure, and the
  identification of morphisms of type `D` structures with `A`-linear maps of the induced modules).
-/

public section

open MulOpposite

namespace TauCeti

namespace TypeDStructure

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {d : A →ₗ[R] A} {S : Type*}
  {ι : S → A} {X X' X'' : Type*} [Fintype X] [Fintype X'] [Fintype X'']
  {N : TypeDStructure d ι X} {N' : TypeDStructure d ι X'} {N'' : TypeDStructure d ι X''}

/-! ### The induced module and its generators -/

variable (N) in
/-- The **induced module** `A ⊠ N = A ⊗_I N` of a type `D` structure `N`, as the left
`A`-submodule of row vectors `φ : X → A`, standing for `∑ x, φ x ⊗ x`, with
`φ x * ι (idem x) = φ x`. -/
def inducedModule : Submodule A (X → A) where
  carrier := {φ | ∀ x, φ x * ι (N.idem x) = φ x}
  add_mem' {φ ψ} hφ hψ x := by simp [add_mul, hφ x, hψ x]
  zero_mem' := by simp
  smul_mem' b φ hφ x := by simp [mul_assoc, hφ x]

@[simp]
theorem mem_inducedModule_iff {φ : X → A} :
    φ ∈ N.inducedModule ↔ ∀ x, φ x * ι (N.idem x) = φ x :=
  Iff.rfl

/-- As an `R`-module, the induced module is the box tensor product of the regular right module
`A` with `N`. -/
theorem mem_inducedModule_iff_mem_boxTensor {φ : X → A} :
    φ ∈ N.inducedModule ↔ φ ∈ N.boxTensor A := by
  simp

variable (N) in
/-- The induced module is the box tensor product of `A` with `N`, with its `R`-module
structure. -/
theorem restrictScalars_inducedModule : N.inducedModule.restrictScalars R = N.boxTensor A :=
  SetLike.ext fun _ => mem_inducedModule_iff_mem_boxTensor

variable (N) in
/-- The **generator** `1 ⊗ x` of the induced module: the row vector with `ι (idem x)` in position
`x` and zero elsewhere. It lies in `A ⊠ N` when the `ι s` are idempotents. -/
def generator [DecidableEq X] (hι : ∀ s, IsIdempotentElem (ι s)) (x : X) : N.inducedModule :=
  ⟨Pi.single x (ι (N.idem x)), fun y => by
    rcases eq_or_ne y x with rfl | h
    · simp [(hι _).eq]
    · simp [h]⟩

@[simp]
theorem coe_generator [DecidableEq X] (hι : ∀ s, IsIdempotentElem (ι s)) (x : X) :
    (N.generator hι x : X → A) = Pi.single x (ι (N.idem x)) :=
  (rfl)

/-- **The generators span the induced module**: every element of `A ⊠ N` is
`φ = ∑ x, φ x • (1 ⊗ x)`. -/
theorem sum_smul_generator [DecidableEq X] (hι : ∀ s, IsIdempotentElem (ι s))
    (φ : N.inducedModule) : ∑ x, (φ : X → A) x • N.generator hι x = φ := by
  ext y
  simp only [Submodule.coe_sum, Submodule.coe_smul, coe_generator, Finset.sum_apply,
    Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  exact φ.2 y

/-- An `A`-linear map out of the induced module is determined by its values on the
generators. -/
theorem inducedModule_hom_ext [DecidableEq X] (hι : ∀ s, IsIdempotentElem (ι s))
    {P : Type*} [AddCommGroup P] [Module A P] {T T' : N.inducedModule →ₗ[A] P}
    (h : ∀ x, T (N.generator hι x) = T' (N.generator hι x)) : T = T' := by
  ext φ
  rw [← sum_smul_generator hι φ]
  simp [h]

/-- The generator `1 ⊗ x` is fixed by its idempotent: `ι (idem x) • (1 ⊗ x) = 1 ⊗ x`. -/
theorem idem_smul_generator [DecidableEq X] (hι : ∀ s, IsIdempotentElem (ι s)) (x : X) :
    ι (N.idem x) • N.generator hι x = N.generator hι x := by
  ext y
  simp only [Submodule.coe_smul, coe_generator, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
    mul_ite, mul_zero, (hι _).eq]

/-! ### Morphisms as `A`-linear maps -/

variable (N N') in
/-- The **`A`-linear map induced by a morphism** `F` from `N` to `N'`: on row vectors,
`φ ↦ φ ⬝ F`, that is `a ⊗ x ↦ ∑ y, a * F x y ⊗ y`. -/
noncomputable def inducedHom : morphisms N N' →ₗ[R] N.inducedModule →ₗ[A] N'.inducedModule where
  toFun F :=
    { toFun φ := ⟨continuationMap R A (F : Matrix X X' A) φ, mem_inducedModule_iff_mem_boxTensor.mpr
        (continuationMap_mem_boxTensor (M := A) F.2 φ)⟩
      map_add' φ ψ := Subtype.ext (map_add _ _ _)
      map_smul' b φ := by
        ext z
        simp [continuationMap_apply (R := R) (M := A) (F : Matrix X X' A), Finset.mul_sum,
          mul_assoc] }
  map_add' F G := by
    ext φ z
    simp [continuationMap_add]
  map_smul' r F := by
    ext φ z
    simp [continuationMap_apply (R := R) (M := A) (F : Matrix X X' A),
      continuationMap_apply (R := R) (M := A) (r • F : Matrix X X' A), Finset.smul_sum]

@[simp]
theorem coe_inducedHom_apply (F : morphisms N N') (φ : N.inducedModule) :
    (inducedHom N N' F φ : X' → A) = continuationMap R A (F : Matrix X X' A) φ :=
  (rfl)

/-- A morphism sends the generator `1 ⊗ x` to `∑ y, F x y ⊗ y`, the row of `F` at `x`. -/
theorem coe_inducedHom_generator [DecidableEq X] (hι : ∀ s, IsIdempotentElem (ι s))
    (F : morphisms N N') (x : X) :
    (inducedHom N N' F (N.generator hι x) : X' → A) = (F : Matrix X X' A) x := by
  ext y
  rw [coe_inducedHom_apply, coe_generator,
    continuationMap_single_apply (R := R) (M := A) (F : Matrix X X' A), op_smul_eq_mul,
    (mem_morphisms_iff.mp F.2 x y).1]

/-- **Composition**: the matrix product of morphisms induces the composite of the maps. -/
theorem inducedHom_mul (F : morphisms N N') (G : morphisms N' N'') :
    inducedHom N N'' ⟨(F : Matrix X X' A) * (G : Matrix X' X'' A), mul_mem_morphisms F.2 G.2⟩ =
      (inducedHom N' N'' G).comp (inducedHom N N' F) := by
  ext φ : 2
  simp only [coe_inducedHom_apply, LinearMap.comp_apply, continuationMap_matMul]

/-- **Identities**: the identity morphism induces the identity of `A ⊠ N`. -/
@[simp]
theorem inducedHom_idMorphism [DecidableEq X] (hι : ∀ s, IsIdempotentElem (ι s)) :
    inducedHom N N ⟨N.idMorphism, N.idMorphism_mem_morphisms hι⟩ = LinearMap.id := by
  ext φ : 2
  exact continuationMap_idMorphism (mem_inducedModule_iff_mem_boxTensor.mp φ.2)

variable (N N') in
/-- **Morphisms of type `D` structures are the `A`-linear maps of the induced modules**: when
the `ι s` are idempotents, every `A`-linear map `A ⊠ N → A ⊠ N'` is `φ ↦ φ ⬝ F` for exactly one
morphism `F`, whose row at `x` is the image of the generator `1 ⊗ x`. -/
noncomputable def inducedHomEquiv [DecidableEq X] (hι : ∀ s, IsIdempotentElem (ι s)) :
    morphisms N N' ≃ₗ[R] N.inducedModule →ₗ[A] N'.inducedModule where
  __ := inducedHom N N'
  invFun T := ⟨fun x y => (T (N.generator hι x) : X' → A) y, mem_morphisms_iff.mpr fun x y => by
    refine ⟨?_, (T (N.generator hι x)).2 y⟩
    have h := congrArg (fun φ : N'.inducedModule => (φ : X' → A) y)
      (congrArg T (idem_smul_generator hι x))
    simpa only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] using h⟩
  left_inv F := by
    ext x y
    exact congrFun (coe_inducedHom_generator hι F x) y
  right_inv T := by
    refine inducedModule_hom_ext hι fun x => ?_
    ext y
    exact congrFun (coe_inducedHom_generator hι _ x) y

@[simp]
theorem inducedHomEquiv_apply [DecidableEq X] (hι : ∀ s, IsIdempotentElem (ι s))
    (F : morphisms N N') : inducedHomEquiv N N' hι F = inducedHom N N' F :=
  (rfl)

@[simp]
theorem coe_inducedHomEquiv_symm_apply [DecidableEq X] (hι : ∀ s, IsIdempotentElem (ι s))
    (T : N.inducedModule →ₗ[A] N'.inducedModule) (x : X) (y : X') :
    ((inducedHomEquiv N N' hι).symm T : Matrix X X' A) x y = (T (N.generator hι x) : X' → A) y :=
  (rfl)

/-- The map of morphisms to `A`-linear maps of the induced modules is injective. -/
theorem inducedHom_injective (hι : ∀ s, IsIdempotentElem (ι s)) :
    Function.Injective (inducedHom N N') := by
  classical
  exact (inducedHomEquiv N N' hι).injective

/-! ### Differentials -/

variable (N) in
/-- The **differential of the induced module** `A ⊠ N`, `∂ φ = d φ + φ ⬝ δ`, that is
`∂ (a ⊗ x) = d a ⊗ x + ∑ y, a * coeff x y ⊗ y`. It preserves `A ⊠ N` when the `ι s` are cycles. -/
noncomputable def inducedDifferential (hd : IsUngradedDGAlgebra d) (hι : ∀ s, d (ι s) = 0) :
    N.inducedModule →ₗ[R] N.inducedModule where
  toFun φ := ⟨N.boxDifferential d φ, mem_inducedModule_iff_mem_boxTensor.mpr
    (N.boxDifferential_mem_boxTensor hι hd.isUngradedDGRightModule
      (mem_inducedModule_iff_mem_boxTensor.mp φ.2))⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' r φ := Subtype.ext (map_smul (N.boxDifferential d) r (φ : X → A))

@[simp]
theorem coe_inducedDifferential_apply (hd : IsUngradedDGAlgebra d) (hι : ∀ s, d (ι s) = 0)
    (φ : N.inducedModule) :
    (N.inducedDifferential hd hι φ : X → A) = N.boxDifferential d φ :=
  (rfl)

/-- The differential of the induced module squares to zero. -/
@[simp]
theorem inducedDifferential_inducedDifferential [CharP R 2] (hd : IsUngradedDGAlgebra d)
    (hι : ∀ s, d (ι s) = 0) (φ : N.inducedModule) :
    N.inducedDifferential hd hι (N.inducedDifferential hd hι φ) = 0 :=
  Subtype.ext (N.boxDifferential_boxDifferential hd.isUngradedDGRightModule φ)

/-- **The Leibniz rule** of the induced module: `∂ (b • φ) = d b • φ + b • ∂ φ`. -/
theorem inducedDifferential_smul (hd : IsUngradedDGAlgebra d) (hι : ∀ s, d (ι s) = 0) (b : A)
    (φ : N.inducedModule) :
    N.inducedDifferential hd hι (b • φ) = d b • φ + b • N.inducedDifferential hd hι φ :=
  Subtype.ext (boxDifferential_smul hd N b φ)

/-- The induced differential sends the generator `1 ⊗ x` to `∑ y, coeff x y ⊗ y`, the row of the
coefficient matrix at `x`. -/
theorem coe_inducedDifferential_generator [DecidableEq X] (hd : IsUngradedDGAlgebra d)
    (hidem : ∀ s, IsIdempotentElem (ι s)) (hι : ∀ s, d (ι s) = 0) (x : X) :
    (N.inducedDifferential hd hι (N.generator hidem x) : X → A) = N.coeff x := by
  ext y
  simp only [coe_inducedDifferential_apply, coe_generator, boxDifferential_apply, Pi.add_apply,
    continuationMap_single_apply (R := R) (M := A) N.coeff, op_smul_eq_mul, N.idem_mul_coeff]
  simp [Pi.single_apply, apply_ite d, hι]

variable (N N') in
/-- The **differential of `A`-linear maps** of induced modules, `∂ T = ∂' ∘ T + T ∘ ∂`. Over a
ring of characteristic two this is again `A`-linear, since the two terms `d b • T φ` coming from
the Leibniz rule cancel. -/
noncomputable def inducedHomDifferential [CharP R 2] (hd : IsUngradedDGAlgebra d)
    (hι : ∀ s, d (ι s) = 0) :
    (N.inducedModule →ₗ[A] N'.inducedModule) →ₗ[R] N.inducedModule →ₗ[A] N'.inducedModule where
  toFun T :=
    { toFun φ := N'.inducedDifferential hd hι (T φ) + T (N.inducedDifferential hd hι φ)
      map_add' φ ψ := by
        simp only [map_add]
        abel
      map_smul' b φ := by
        simp only [map_smul, inducedDifferential_smul, map_add, RingHom.id_apply, smul_add]
        calc _ = (d b • T φ + d b • T φ) + b • N'.inducedDifferential hd hι (T φ) +
              b • T (N.inducedDifferential hd hι φ) := by abel
          _ = _ := by rw [add_self_eq_zero_of_charTwo R, zero_add] }
  map_add' T T' := by
    ext φ : 1
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add]
    abel
  map_smul' r T := by
    ext φ : 1
    simp

@[simp]
theorem inducedHomDifferential_apply [CharP R 2] (hd : IsUngradedDGAlgebra d)
    (hι : ∀ s, d (ι s) = 0) (T : N.inducedModule →ₗ[A] N'.inducedModule) (φ : N.inducedModule) :
    inducedHomDifferential N N' hd hι T φ =
      N'.inducedDifferential hd hι (T φ) + T (N.inducedDifferential hd hι φ) :=
  (rfl)

/-- The differential of `A`-linear maps of induced modules squares to zero. -/
@[simp]
theorem inducedHomDifferential_inducedHomDifferential [CharP R 2] (hd : IsUngradedDGAlgebra d)
    (hι : ∀ s, d (ι s) = 0) (T : N.inducedModule →ₗ[A] N'.inducedModule) :
    inducedHomDifferential N N' hd hι (inducedHomDifferential N N' hd hι T) = 0 := by
  ext φ : 1
  simp only [inducedHomDifferential_apply, map_add, inducedDifferential_inducedDifferential,
    map_zero, zero_add, add_zero, LinearMap.zero_apply]
  exact add_self_eq_zero_of_charTwo R _

/-- An `A`-linear map of induced modules is a cycle exactly when it commutes with the
differentials, that is, when it is a chain map. -/
theorem inducedHomDifferential_eq_zero_iff [CharP R 2] (hd : IsUngradedDGAlgebra d)
    (hι : ∀ s, d (ι s) = 0) {T : N.inducedModule →ₗ[A] N'.inducedModule} :
    inducedHomDifferential N N' hd hι T = 0 ↔
      ∀ φ, N'.inducedDifferential hd hι (T φ) = T (N.inducedDifferential hd hι φ) := by
  simp only [LinearMap.ext_iff, inducedHomDifferential_apply, LinearMap.zero_apply,
    add_eq_zero_iff_eq_of_charTwo R]

/-- The identity of an induced module is a cycle: `∂ id = ∂ + ∂ = 0`. -/
@[simp]
theorem inducedHomDifferential_id [CharP R 2] (hd : IsUngradedDGAlgebra d)
    (hι : ∀ s, d (ι s) = 0) : inducedHomDifferential N N hd hι LinearMap.id = 0 := by
  ext φ : 1
  simp only [inducedHomDifferential_apply, LinearMap.id_apply, LinearMap.zero_apply]
  exact add_self_eq_zero_of_charTwo R _

/-- **The Leibniz rule for composition**: `∂ (T' ∘ T) = ∂ T' ∘ T + T' ∘ ∂ T`, so the `A`-linear
maps of induced modules form a differential category. -/
theorem inducedHomDifferential_comp [CharP R 2] (hd : IsUngradedDGAlgebra d)
    (hι : ∀ s, d (ι s) = 0) (T : N.inducedModule →ₗ[A] N'.inducedModule)
    (T' : N'.inducedModule →ₗ[A] N''.inducedModule) :
    inducedHomDifferential N N'' hd hι (T'.comp T) =
      (inducedHomDifferential N' N'' hd hι T').comp T +
        T'.comp (inducedHomDifferential N N' hd hι T) := by
  ext φ : 1
  simp only [inducedHomDifferential_apply, LinearMap.comp_apply, LinearMap.add_apply, map_add]
  calc _ = N''.inducedDifferential hd hι (T' (T φ)) + T' (T (N.inducedDifferential hd hι φ)) +
        (T' (N'.inducedDifferential hd hι (T φ)) + T' (N'.inducedDifferential hd hι (T φ))) := by
        rw [add_self_eq_zero_of_charTwo R, add_zero]
    _ = _ := by abel

/-- **The morphism differential is the differential of `A`-linear maps**: the map induced by
`∂F = d F + F * δ' + δ * F` is `∂' ∘ T_F + T_F ∘ ∂`. -/
theorem inducedHom_morphismDifferential [CharP R 2] (hd : IsUngradedDGAlgebra d)
    (hι : ∀ s, d (ι s) = 0) (F : morphisms N N') :
    inducedHom N N' ⟨morphismDifferential N N' F, morphismDifferential_mem_morphisms hd hι F.2⟩ =
      inducedHomDifferential N N' hd hι (inducedHom N N' F) := by
  ext φ : 2
  exact (boxDifferential_continuationMap hd.isUngradedDGRightModule (F : Matrix X X' A)
    (φ : X → A)).symm

/-- The inverse of `inducedHomEquiv` also commutes with the differentials: the morphism
corresponding to `∂' ∘ T + T ∘ ∂` is the morphism differential of the one corresponding to `T`.
So the morphism complex of type `D` structures and the complex of `A`-linear maps of the induced
modules are isomorphic complexes. -/
theorem inducedHomEquiv_symm_inducedHomDifferential [CharP R 2] [DecidableEq X]
    (hd : IsUngradedDGAlgebra d) (hidem : ∀ s, IsIdempotentElem (ι s)) (hι : ∀ s, d (ι s) = 0)
    (T : N.inducedModule →ₗ[A] N'.inducedModule) :
    ((inducedHomEquiv N N' hidem).symm (inducedHomDifferential N N' hd hι T) :
        Matrix X X' A) =
      morphismDifferential N N' ((inducedHomEquiv N N' hidem).symm T) := by
  have h := inducedHom_morphismDifferential hd hι ((inducedHomEquiv N N' hidem).symm T)
  rw [← inducedHomEquiv_apply hidem, ← inducedHomEquiv_apply hidem,
    LinearEquiv.apply_symm_apply, ← LinearEquiv.eq_symm_apply] at h
  rw [← h]

/-- **Homomorphisms are chain maps**: a morphism `F` of type `D` structures is a cycle,
`∂F = 0`, exactly when `φ ↦ φ ⬝ F` commutes with the differentials of the induced modules. -/
theorem morphismDifferential_eq_zero_iff [CharP R 2]
    (hd : IsUngradedDGAlgebra d) (hidem : ∀ s, IsIdempotentElem (ι s)) (hι : ∀ s, d (ι s) = 0)
    (F : morphisms N N') :
    morphismDifferential N N' F = 0 ↔ ∀ φ, N'.inducedDifferential hd hι (inducedHom N N' F φ) =
      inducedHom N N' F (N.inducedDifferential hd hι φ) := by
  rw [← inducedHomDifferential_eq_zero_iff hd hι, ← inducedHom_morphismDifferential hd hι,
    ← map_zero (inducedHom N N'), (inducedHom_injective hidem).eq_iff, Subtype.ext_iff,
    Submodule.coe_zero]

/-- **Homotopies are chain homotopies**: for morphisms `F`, `G`, `H` of type `D` structures,
`∂H = F + G` exactly when the map of `H` is a chain homotopy between the maps of `F` and `G`,
`∂' ∘ T_H + T_H ∘ ∂ = T_F + T_G`. Since every `A`-linear map is the map of a morphism, every
`A`-linear chain homotopy between `T_F` and `T_G` arises from such an `H`. -/
theorem morphismDifferential_eq_add_iff [CharP R 2]
    (hd : IsUngradedDGAlgebra d) (hidem : ∀ s, IsIdempotentElem (ι s)) (hι : ∀ s, d (ι s) = 0)
    (F G H : morphisms N N') :
    morphismDifferential N N' H = (F : Matrix X X' A) + G ↔
      inducedHomDifferential N N' hd hι (inducedHom N N' H) =
        inducedHom N N' F + inducedHom N N' G := by
  rw [← inducedHom_morphismDifferential hd hι, ← map_add, (inducedHom_injective hidem).eq_iff,
    Subtype.ext_iff, Submodule.coe_add]

/-! ### Differentials of the induced module come from type `D` structures -/

variable (N) in
/-- The entrywise differential `φ ↦ d φ` of the induced module, when the `ι s` are cycles. -/
private noncomputable def entrywiseDifferential (hd : IsUngradedDGAlgebra d)
    (hι : ∀ s, d (ι s) = 0) : N.inducedModule →ₗ[R] N.inducedModule where
  toFun φ := ⟨fun x => d ((φ : X → A) x), mem_inducedModule_iff.mpr fun x => by
    conv_rhs => rw [← φ.2 x]
    rw [hd.map_mul, hι, mul_zero, add_zero]⟩
  map_add' φ ψ := by ext; simp
  map_smul' r φ := by ext; simp

/-- A Leibniz differential of the induced module differs from the entrywise differential by an
`A`-linear map. -/
private noncomputable def leibnizDefect (hd : IsUngradedDGAlgebra d) (hι : ∀ s, d (ι s) = 0)
    (D : N.inducedModule →ₗ[R] N.inducedModule)
    (hD : ∀ (b : A) φ, D (b • φ) = d b • φ + b • D φ) :
    N.inducedModule →ₗ[A] N.inducedModule where
  toFun φ := D φ - N.entrywiseDifferential hd hι φ
  map_add' φ ψ := by simp only [map_add]; abel
  map_smul' b φ := by
    ext x
    simp [entrywiseDifferential, hD, hd.map_mul, mul_sub]

/-- A Leibniz differential is the entrywise differential plus the map of the morphism
corresponding to its defect. -/
private theorem coe_apply_eq_add_continuationMap [DecidableEq X] (hd : IsUngradedDGAlgebra d)
    (hidem : ∀ s, IsIdempotentElem (ι s)) (hι : ∀ s, d (ι s) = 0)
    (D : N.inducedModule →ₗ[R] N.inducedModule)
    (hD : ∀ (b : A) φ, D (b • φ) = d b • φ + b • D φ) (φ : N.inducedModule) :
    (D φ : X → A) = (fun x => d ((φ : X → A) x)) + continuationMap R A
      ((inducedHomEquiv N N hidem).symm (leibnizDefect hd hι D hD) : Matrix X X A) φ := by
  have h := congrArg (fun T : N.inducedModule →ₗ[A] N.inducedModule => (T φ : X → A))
    ((inducedHomEquiv N N hidem).apply_symm_apply (leibnizDefect hd hι D hD))
  simp only [inducedHomEquiv_apply, coe_inducedHom_apply] at h
  rw [h]
  ext x
  simp [leibnizDefect, entrywiseDifferential]

/-- The entrywise differential vanishes on the generators, so the row at `x` of the morphism of
the defect is `D (1 ⊗ x)`. -/
private theorem coe_inducedHomEquiv_symm_leibnizDefect [DecidableEq X]
    (hd : IsUngradedDGAlgebra d) (hidem : ∀ s, IsIdempotentElem (ι s)) (hι : ∀ s, d (ι s) = 0)
    (D : N.inducedModule →ₗ[R] N.inducedModule)
    (hD : ∀ (b : A) φ, D (b • φ) = d b • φ + b • D φ) (x y : X) :
    ((inducedHomEquiv N N hidem).symm (leibnizDefect hd hι D hD) : Matrix X X A) x y =
      (D (N.generator hidem x) : X → A) y := by
  simp [leibnizDefect, entrywiseDifferential, Pi.single_apply, apply_ite d, hι]

variable (N) in
/-- The **type `D` structure of a Leibniz differential** `D` of square zero on the induced module
`A ⊠ N`, when the `ι s` are idempotent cycles. It has the idempotents of `N`, and its coefficient
`coeff x y` is the `y` entry of `D (1 ⊗ x)`. Its box tensor differential is `D`
(`TauCeti.TypeDStructure.boxDifferential_ofInducedDifferential`). -/
noncomputable def ofInducedDifferential [DecidableEq X] (hd : IsUngradedDGAlgebra d)
    (hidem : ∀ s, IsIdempotentElem (ι s)) (hι : ∀ s, d (ι s) = 0)
    (D : N.inducedModule →ₗ[R] N.inducedModule)
    (hD : ∀ (b : A) φ, D (b • φ) = d b • φ + b • D φ) (hDD : ∀ φ, D (D φ) = 0) :
    TypeDStructure d ι X where
  idem := N.idem
  coeff := (inducedHomEquiv N N hidem).symm (leibnizDefect hd hι D hD)
  idem_mul_coeff x y :=
    (mem_morphisms_iff.mp ((inducedHomEquiv N N hidem).symm (leibnizDefect hd hι D hD)).2 x y).1
  coeff_mul_idem x y :=
    (mem_morphisms_iff.mp ((inducedHomEquiv N N hidem).symm (leibnizDefect hd hι D hD)).2 x y).2
  map_coeff_add_coeff_mul_coeff := by
    -- `D (D (1 ⊗ x)) = 0` is the row at `x` of `d δ + δ * δ`, since `D (1 ⊗ x)` is the row `δ x`.
    ext x y
    have hrow (z : X) : (D (N.generator hidem x) : X → A) z =
        ((inducedHomEquiv N N hidem).symm (leibnizDefect hd hι D hD) : Matrix X X A) x z :=
      (coe_inducedHomEquiv_symm_leibnizDefect hd hidem hι D hD x z).symm
    have h := congrArg (fun φ : N.inducedModule => (φ : X → A) y) (hDD (N.generator hidem x))
    rw [coe_apply_eq_add_continuationMap hd hidem hι D hD, Pi.add_apply,
      continuationMap_apply (R := R) (M := A)
        ((inducedHomEquiv N N hidem).symm (leibnizDefect hd hι D hD) : Matrix X X A)] at h
    simp only [hrow, op_smul_eq_mul, ZeroMemClass.coe_zero, Pi.zero_apply] at h
    simpa only [Matrix.add_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.zero_apply] using h

section OfInducedDifferential

variable [DecidableEq X] (hd : IsUngradedDGAlgebra d) (hidem : ∀ s, IsIdempotentElem (ι s))
  (hι : ∀ s, d (ι s) = 0) (D : N.inducedModule →ₗ[R] N.inducedModule)
  (hD : ∀ (b : A) φ, D (b • φ) = d b • φ + b • D φ) (hDD : ∀ φ, D (D φ) = 0)

@[simp]
theorem ofInducedDifferential_idem :
    (N.ofInducedDifferential hd hidem hι D hD hDD).idem = N.idem :=
  (rfl)

@[simp]
theorem ofInducedDifferential_coeff (x y : X) :
    (N.ofInducedDifferential hd hidem hι D hD hDD).coeff x y =
      (D (N.generator hidem x) : X → A) y :=
  coe_inducedHomEquiv_symm_leibnizDefect hd hidem hι D hD x y

/-- The box tensor differential of the type `D` structure of `D` is `D`. -/
@[simp]
theorem boxDifferential_ofInducedDifferential (φ : N.inducedModule) :
    (N.ofInducedDifferential hd hidem hι D hD hDD).boxDifferential d φ = D φ := by
  -- The coefficient matrix is by definition the morphism of the defect `D - d`.
  rw [boxDifferential_apply, coe_apply_eq_add_continuationMap hd hidem hι D hD]
  rfl

end OfInducedDifferential

/-- The type `D` structure of the induced differential of `N` is `N`. -/
@[simp]
theorem ofInducedDifferential_inducedDifferential [CharP R 2] [DecidableEq X]
    (hd : IsUngradedDGAlgebra d) (hidem : ∀ s, IsIdempotentElem (ι s)) (hι : ∀ s, d (ι s) = 0) :
    N.ofInducedDifferential hd hidem hι (N.inducedDifferential hd hι)
      (inducedDifferential_smul hd hι) (inducedDifferential_inducedDifferential hd hι) = N :=
  TypeDStructure.ext rfl (Matrix.ext fun x y => by
    rw [ofInducedDifferential_coeff, coe_inducedDifferential_generator hd hidem hι])

/-- **Leibniz differentials of square zero on an induced module are type `D` structures.** Let the
`ι s` be idempotent cycles, and let `D` be a differential of the induced module
`A ⊠ N = A ⊗_I ⟨X⟩`, with `D (b • φ) = d b • φ + b • D φ` and `D ∘ D = 0`. Then there is a unique
type `D` structure `N'` with the same idempotents as `N` whose box tensor differential
`φ ↦ d φ + φ ⬝ δ'` is `D`, namely `TauCeti.TypeDStructure.ofInducedDifferential`. So the
differential module structures on `A ⊗_I ⟨X⟩` are exactly the type `D` structures on the
generators `X` with the idempotents of `N`. -/
theorem existsUnique_idem_eq_and_boxDifferential_eq
    (hd : IsUngradedDGAlgebra d) (hidem : ∀ s, IsIdempotentElem (ι s)) (hι : ∀ s, d (ι s) = 0)
    (D : N.inducedModule →ₗ[R] N.inducedModule)
    (hD : ∀ (b : A) φ, D (b • φ) = d b • φ + b • D φ) (hDD : ∀ φ, D (D φ) = 0) :
    ∃! N' : TypeDStructure d ι X,
      N'.idem = N.idem ∧ ∀ φ : N.inducedModule, N'.boxDifferential d φ = D φ := by
  classical
  refine ⟨N.ofInducedDifferential hd hidem hι D hD hDD,
    ⟨rfl, boxDifferential_ofInducedDifferential hd hidem hι D hD hDD⟩, ?_⟩
  -- Uniqueness: the coefficients of `N'` form the morphism whose map is the defect `D - d`.
  rintro ⟨idem', coeff', hl', hr', hs'⟩ ⟨rfl, hN⟩
  have hF : ⟨coeff', mem_morphisms_iff.mpr fun x y => ⟨hl' x y, hr' x y⟩⟩ =
      (inducedHomEquiv N N hidem).symm (leibnizDefect hd hι D hD) := by
    rw [LinearEquiv.eq_symm_apply, inducedHomEquiv_apply]
    ext φ y
    simp [leibnizDefect, entrywiseDifferential, ← hN, boxDifferential_apply]
  exact TypeDStructure.ext rfl (congrArg Subtype.val hF)

end TypeDStructure

end TauCeti

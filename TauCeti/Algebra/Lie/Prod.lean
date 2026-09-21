/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Prod
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod

/-!
# Products of Lie modules

Mathlib gives the product of two Lie *algebras* its Lie ring structure
(`Mathlib/Algebra/Lie/Prod.lean`) and the direct sum of a *family* of Lie modules its Lie module
structure (`Mathlib/Algebra/Lie/DirectSum.lean`), but not the binary product of two Lie modules over
a fixed Lie algebra. This file supplies it: for `L`-modules `M` and `N`, the componentwise bracket
makes `M × N` an `L`-module, and the four maps `fst`, `snd`, `inl`, `inr` are morphisms of
`L`-modules.

The binary product is what an argument comparing two Lie modules of *different* types needs: the
direct sum `⨁ i, M i` of a family forces all the summands into one universe, whereas `M × N` does
not. The first consumer is the uniqueness of the irreducible highest weight module of a given
weight, which compares two such modules by cutting out the graph of an isomorphism inside their
product.

## Main definitions

* `TauCeti.LieModuleHom.fst` and `TauCeti.LieModuleHom.snd`: the two projections.
* `TauCeti.LieModuleHom.inl` and `TauCeti.LieModuleHom.inr`: the two inclusions.
* `TauCeti.LieModuleHom.prod`: the pairing of two morphisms with the same domain.
* `TauCeti.LieModuleEquiv.prodComm`: swapping the factors is an equivalence.
* `TauCeti.lie_prod_apply`: the componentwise bracket on a product.
* `LieHom.prodRepresentation`: the product of two explicit Lie representations.
* `LieHom.piRepresentation`: the product of a family of explicit Lie representations.
-/

public section

namespace TauCeti

universe u v w w₁

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}
variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M] [LieRingModule L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N]

namespace Prod

/-- The componentwise bracket makes the product of two `L`-modules an `L`-module. -/
instance instLieRingModule : LieRingModule L (M × N) where
  bracket x p := (⁅x, p.1⁆, ⁅x, p.2⁆)
  add_lie x y p := Prod.ext (add_lie x y p.1) (add_lie x y p.2)
  lie_add x p q := Prod.ext (lie_add x p.1 q.1) (lie_add x p.2 q.2)
  leibniz_lie x y p := Prod.ext (leibniz_lie x y p.1) (leibniz_lie x y p.2)

instance instLieModule [LieAlgebra R L] [LieModule R L M] [LieModule R L N] :
    LieModule R L (M × N) where
  smul_lie t x p := Prod.ext (smul_lie t x p.1) (smul_lie t x p.2)
  lie_smul t x p := Prod.ext (lie_smul t x p.1) (lie_smul t x p.2)

end Prod

@[simp]
theorem lie_prod_apply (x : L) (p : M × N) : ⁅x, p⁆ = (⁅x, p.1⁆, ⁅x, p.2⁆) := rfl

namespace LieModuleHom

variable (R L M N)

/-- The projection of a product of Lie modules onto its first factor. -/
def fst : M × N →ₗ⁅R,L⁆ M :=
  { LinearMap.fst R M N with map_lie' := rfl }

/-- The projection of a product of Lie modules onto its second factor. -/
def snd : M × N →ₗ⁅R,L⁆ N :=
  { LinearMap.snd R M N with map_lie' := rfl }

/-- The inclusion of the first factor into a product of Lie modules. -/
def inl : M →ₗ⁅R,L⁆ M × N :=
  { LinearMap.inl R M N with map_lie' := by simp [lie_prod_apply] }

/-- The inclusion of the second factor into a product of Lie modules. -/
def inr : N →ₗ⁅R,L⁆ M × N :=
  { LinearMap.inr R M N with map_lie' := by simp [lie_prod_apply] }

variable {R L M N}
variable {P : Type*} [AddCommGroup P] [Module R P] [LieRingModule L P]

/-- Pair two morphisms of Lie modules with the same domain. -/
def prod (f : P →ₗ⁅R,L⁆ M) (g : P →ₗ⁅R,L⁆ N) : P →ₗ⁅R,L⁆ M × N :=
  { LinearMap.prod f g with map_lie' := by simp [lie_prod_apply] }

@[simp] theorem fst_apply (p : M × N) : fst R L M N p = p.1 := (rfl)

@[simp] theorem snd_apply (p : M × N) : snd R L M N p = p.2 := (rfl)

@[simp] theorem inl_apply (m : M) : inl R L M N m = (m, 0) := (rfl)

@[simp] theorem inr_apply (n : N) : inr R L M N n = (0, n) := (rfl)

@[simp] theorem prod_apply (f : P →ₗ⁅R,L⁆ M) (g : P →ₗ⁅R,L⁆ N) (p : P) :
    prod f g p = (f p, g p) := by
  exact LinearMap.prod_apply (f : P →ₗ[R] M) (g : P →ₗ[R] N) p

@[simp]
theorem fst_prod (f : P →ₗ⁅R,L⁆ M) (g : P →ₗ⁅R,L⁆ N) :
    (fst R L M N).comp (prod f g) = f := by
  ext p
  simp

@[simp]
theorem snd_prod (f : P →ₗ⁅R,L⁆ M) (g : P →ₗ⁅R,L⁆ N) :
    (snd R L M N).comp (prod f g) = g := by
  ext p
  simp

end LieModuleHom

variable [LieAlgebra R L] [LieModule R L M] [LieModule R L N]

namespace LieModuleEquiv

/-- Swapping the factors is an equivalence of product Lie modules. -/
def prodComm : (M × N) ≃ₗ⁅R,L⁆ (N × M) where
  __ := LinearEquiv.prodComm R M N
  map_lie' := by simp [lie_prod_apply]

omit [LieAlgebra R L] [LieModule R L M] [LieModule R L N] in
@[simp]
theorem prodComm_apply (p : M × N) : prodComm (R := R) (L := L) p = p.swap :=
  LinearEquiv.prodComm_apply R M N p

omit [LieAlgebra R L] [LieModule R L M] [LieModule R L N] in
@[simp]
theorem coe_prodComm_apply (p : M × N) :
    ((prodComm (R := R) (L := L) : (M × N) ≃ₗ⁅R,L⁆ (N × M)) :
      M × N →ₗ⁅R,L⁆ N × M) p = p.swap :=
  prodComm_apply p

end LieModuleEquiv

end TauCeti

namespace LieHom

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v w w₁

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The product of two Lie representations, acting componentwise on the product of their
carriers. -/
def prodRepresentation (rho : L →ₗ⁅R⁆ Module.End R M)
    (sigma : L →ₗ⁅R⁆ Module.End R N) : L →ₗ⁅R⁆ Module.End R (M × N) :=
  (LinearMap.prodMapAlgHom R M N).toLieHom.comp (LieHom.prod rho sigma)

/-- The product representation acts componentwise. -/
@[simp, grind =]
theorem prodRepresentation_apply (rho : L →ₗ⁅R⁆ Module.End R M)
    (sigma : L →ₗ⁅R⁆ Module.End R N) (x : L) (p : M × N) :
    rho.prodRepresentation sigma x p = (rho x p.1, sigma x p.2) :=
  (rfl)

/-- The kernel of a product representation is the intersection of the two kernels. -/
@[simp]
theorem ker_prodRepresentation (rho : L →ₗ⁅R⁆ Module.End R M)
    (sigma : L →ₗ⁅R⁆ Module.End R N) :
    (rho.prodRepresentation sigma).ker = rho.ker ⊓ sigma.ker := by
  ext x
  simp only [LieHom.mem_ker, LieSubmodule.mem_inf, LinearMap.ext_iff, prodRepresentation_apply,
    LinearMap.zero_apply, Prod.forall, Prod.mk_eq_zero]
  exact ⟨fun h ↦ ⟨fun m ↦ (h m 0).1, fun n ↦ (h 0 n).2⟩, fun h m n ↦ ⟨h.1 m, h.2 n⟩⟩

/-- A product representation is faithful exactly when the kernels of its factors are disjoint. -/
theorem prodRepresentation_injective_iff (rho : L →ₗ⁅R⁆ Module.End R M)
    (sigma : L →ₗ⁅R⁆ Module.End R N) :
    Function.Injective (rho.prodRepresentation sigma) ↔ Disjoint rho.ker sigma.ker := by
  rw [← LieHom.ker_eq_bot, ker_prodRepresentation, disjoint_iff]

section Pi

universe i w₂

variable {I : Type i} {V : I → Type w₂}
variable [(j : I) → AddCommGroup (V j)] [(j : I) → Module R (V j)]

/-- The product of a family of Lie representations, acting coordinatewise on the dependent
function space. For a finite index type, this product representation is canonically equivalent to
the corresponding finite direct-sum representation. -/
def piRepresentation (rho : (j : I) → L →ₗ⁅R⁆ Module.End R (V j)) :
    L →ₗ⁅R⁆ Module.End R ((j : I) → V j) where
  toFun x :=
    { toFun := fun m j ↦ rho j x (m j)
      map_add' := fun m n ↦ by ext j; exact (rho j x).map_add (m j) (n j)
      map_smul' := fun r m ↦ by ext j; exact (rho j x).map_smul r (m j) }
  map_add' x y := by ext m j; exact LinearMap.congr_fun (map_add (rho j) x y) (m j)
  map_smul' r x := by ext m j; exact LinearMap.congr_fun (map_smul (rho j) r x) (m j)
  map_lie' {x y} := by
    ext m j
    -- The action is a nested linear-map structure literal; expose its coordinatewise
    -- composition so that the corresponding coordinate representation law applies.
    change rho j ⁅x, y⁆ (m j) =
      rho j x (rho j y (m j)) - rho j y (rho j x (m j))
    simpa only [LieRing.of_associative_ring_bracket, Module.End.mul_apply,
      LinearMap.sub_apply] using LinearMap.congr_fun (map_lie (rho j) x y) (m j)

/-- A product representation acts coordinatewise. -/
@[simp, grind =]
theorem piRepresentation_apply (rho : (j : I) → L →ₗ⁅R⁆ Module.End R (V j))
    (x : L) (m : (j : I) → V j) (j : I) :
    piRepresentation rho x m j = rho j x (m j) :=
  (rfl)

/-- The kernel of a family product representation is the intersection of the kernels of its
coordinates. -/
@[simp]
theorem ker_piRepresentation (rho : (j : I) → L →ₗ⁅R⁆ Module.End R (V j)) :
    (piRepresentation rho).ker = ⨅ j, (rho j).ker := by
  classical
  apply le_antisymm
  · refine le_iInf fun j x hx ↦ ?_
    rw [LieHom.mem_ker] at hx ⊢
    apply LinearMap.ext
    intro v
    have h := congrArg (fun f : Module.End R ((j : I) → V j) ↦
      f (Function.update 0 j v) j) hx
    simpa [piRepresentation_apply] using h
  · intro x hx
    rw [LieHom.mem_ker]
    apply LinearMap.ext
    intro m
    funext j
    have hxj : x ∈ (rho j).ker := (iInf_le (fun k ↦ (rho k).ker) j) hx
    rw [LieHom.mem_ker] at hxj
    simpa only [piRepresentation_apply, LinearMap.zero_apply, Pi.zero_apply] using
      LinearMap.congr_fun hxj (m j)

/-- A family product representation is faithful exactly when its coordinate kernels have trivial
intersection. -/
theorem piRepresentation_injective_iff
    (rho : (j : I) → L →ₗ⁅R⁆ Module.End R (V j)) :
    Function.Injective (piRepresentation rho) ↔ (⨅ j, (rho j).ker) = ⊥ := by
  rw [← LieHom.ker_eq_bot, ker_piRepresentation]

end Pi

end LieHom

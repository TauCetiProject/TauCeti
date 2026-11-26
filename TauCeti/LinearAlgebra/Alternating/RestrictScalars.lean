/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Curry

/-!
# Restriction of scalars for alternating maps

Given an `A`-alternating map `f : M [⋀^ι]→ₗ[A] N` and a compatible action of `R` on `A`, `M`,
and `N`, `AlternatingMap.restrictScalars R f` reinterprets `f` as an `R`-alternating map
`M [⋀^ι]→ₗ[R] N` with the same underlying function. This is the alternating counterpart of
`MultilinearMap.restrictScalars`.

## Main definitions

* `AlternatingMap.instIsScalarTower`: pointwise `IsScalarTower` instance on `M [⋀^ι]→ₗ[R] N`.
* `AlternatingMap.restrictScalars`: scalar restriction `M [⋀^ι]→ₗ[A] N → M [⋀^ι]→ₗ[R] N`.
* `AlternatingMap.restrictScalarsₗ`: `AlternatingMap.restrictScalars` bundled as a linear map.
* `AlternatingMap.ofRestrictScalars`: upgrade an `R`-alternating map that is `A`-homogeneous in
  each coordinate to an `A`-alternating map `M [⋀^ι]→ₗ[A] N`.
-/

public section

namespace AlternatingMap

/-- Pointwise `IsScalarTower` instance on `M [⋀^ι]→ₗ[R] N`. -/
instance instIsScalarTower {R M N ι S T : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Monoid S] [Monoid T] [DistribMulAction S N] [DistribMulAction T N]
    [SMulCommClass R S N] [SMulCommClass R T N] [SMul S T] [IsScalarTower S T N] :
    IsScalarTower S T (M [⋀^ι]→ₗ[R] N) :=
  FunLike.isScalarTower

section Semiring

variable (R : Type*) {A M N ι : Type*} [Semiring R] [Semiring A] [SMul R A]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module A M] [IsScalarTower R A M]
  [Module R N] [Module A N] [IsScalarTower R A N]

/-- Reinterpret an `A`-alternating map as an `R`-alternating map when the actions of `R` and `A`
form scalar towers on the domain and codomain. -/
def restrictScalars (f : M [⋀^ι]→ₗ[A] N) : M [⋀^ι]→ₗ[R] N where
  toMultilinearMap := f.toMultilinearMap.restrictScalars R
  map_eq_zero_of_eq' := f.map_eq_zero_of_eq'

@[simp]
theorem coe_restrictScalars (f : M [⋀^ι]→ₗ[A] N) : ⇑(f.restrictScalars R) = f := (rfl)

@[simp]
theorem restrictScalars_apply (f : M [⋀^ι]→ₗ[A] N) (v : ι → M) : f.restrictScalars R v = f v :=
  (rfl)

@[simp]
theorem toMultilinearMap_restrictScalars (f : M [⋀^ι]→ₗ[A] N) :
    (f.restrictScalars R).toMultilinearMap = f.toMultilinearMap.restrictScalars R := (rfl)

theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (M [⋀^ι]→ₗ[A] N) → M [⋀^ι]→ₗ[R] N) :=
  fun _ _ h ↦ ext fun v ↦ congr($h v)

@[simp]
theorem restrictScalars_inj {f g : M [⋀^ι]→ₗ[A] N} :
    f.restrictScalars R = g.restrictScalars R ↔ f = g :=
  (restrictScalars_injective R).eq_iff

@[simp]
theorem restrictScalars_zero : (0 : M [⋀^ι]→ₗ[A] N).restrictScalars R = 0 := ext fun _ ↦ rfl

@[simp]
theorem restrictScalars_add (f g : M [⋀^ι]→ₗ[A] N) :
    (f + g).restrictScalars R = f.restrictScalars R + g.restrictScalars R := ext fun _ ↦ rfl

@[simp]
theorem restrictScalars_smul {S : Type*} [Monoid S] [DistribMulAction S N]
    [SMulCommClass A S N] [SMulCommClass R S N] (c : S) (f : M [⋀^ι]→ₗ[A] N) :
    (c • f).restrictScalars R = c • f.restrictScalars R := ext fun _ ↦ rfl

/-- `AlternatingMap.restrictScalars` as an `S`-linear map. -/
def restrictScalarsₗ (S : Type*) [Semiring S] [Module S N]
    [SMulCommClass A S N] [SMulCommClass R S N] :
    (M [⋀^ι]→ₗ[A] N) →ₗ[S] M [⋀^ι]→ₗ[R] N where
  toFun := restrictScalars R
  map_add' := restrictScalars_add R
  map_smul' := restrictScalars_smul R

@[simp]
theorem restrictScalarsₗ_apply (S : Type*) [Semiring S] [Module S N]
    [SMulCommClass A S N] [SMulCommClass R S N] (f : M [⋀^ι]→ₗ[A] N) :
    restrictScalarsₗ R S f = f.restrictScalars R := (rfl)

end Semiring

section OfRestrictScalars

variable (A : Type*) {R M N ι : Type*} [Semiring R] [Semiring A]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module A M]
  [Module R N] [Module A N]

/-- Upgrade an `R`-alternating map `g` to an `A`-alternating map given `A`-homogeneity in each
coordinate. -/
def ofRestrictScalars [hdec₀ : DecidableEq ι] (g : M [⋀^ι]→ₗ[R] N)
    (h : ∀ (v : ι → M) (i : ι) (a : A) (x : M),
      g (Function.update v i (a • x)) = a • g (Function.update v i x)) :
    M [⋀^ι]→ₗ[A] N where
  toFun := g
  map_update_add' := g.map_update_add'
  map_update_smul' := fun [hdec : DecidableEq ι] m i a x ↦ by
    obtain rfl := Subsingleton.elim hdec hdec₀
    exact h m i a x
  map_eq_zero_of_eq' := g.map_eq_zero_of_eq'

@[simp]
theorem coe_ofRestrictScalars [DecidableEq ι] (g : M [⋀^ι]→ₗ[R] N)
    (h : ∀ (v : ι → M) (i : ι) (a : A) (x : M),
      g (Function.update v i (a • x)) = a • g (Function.update v i x)) :
    ⇑(g.ofRestrictScalars A h) = g := (rfl)

@[simp]
theorem ofRestrictScalars_apply [DecidableEq ι] (g : M [⋀^ι]→ₗ[R] N)
    (h : ∀ (v : ι → M) (i : ι) (a : A) (x : M),
      g (Function.update v i (a • x)) = a • g (Function.update v i x)) (v : ι → M) :
    g.ofRestrictScalars A h v = g v := (rfl)

@[simp]
theorem restrictScalars_ofRestrictScalars [SMul R A] [IsScalarTower R A M] [IsScalarTower R A N]
    [DecidableEq ι] (g : M [⋀^ι]→ₗ[R] N)
    (h : ∀ (v : ι → M) (i : ι) (a : A) (x : M),
      g (Function.update v i (a • x)) = a • g (Function.update v i x)) :
    (g.ofRestrictScalars A h).restrictScalars R = g := ext fun _ ↦ rfl

@[simp]
theorem ofRestrictScalars_restrictScalars [SMul R A] [IsScalarTower R A M] [IsScalarTower R A N]
    [DecidableEq ι] (f : M [⋀^ι]→ₗ[A] N)
    (h : ∀ (v : ι → M) (i : ι) (a : A) (x : M),
      f.restrictScalars R (Function.update v i (a • x)) =
        a • f.restrictScalars R (Function.update v i x)) :
    (f.restrictScalars R).ofRestrictScalars A h = f := ext fun _ ↦ rfl

end OfRestrictScalars

section Group

variable (R : Type*) {A M N ι : Type*} [Semiring R] [Semiring A] [SMul R A]
  [AddCommMonoid M] [AddCommGroup N] [Module R M] [Module A M] [IsScalarTower R A M]
  [Module R N] [Module A N] [IsScalarTower R A N]

@[simp]
theorem restrictScalars_neg (f : M [⋀^ι]→ₗ[A] N) :
    (-f).restrictScalars R = -f.restrictScalars R := ext fun _ ↦ rfl

@[simp]
theorem restrictScalars_sub (f g : M [⋀^ι]→ₗ[A] N) :
    (f - g).restrictScalars R = f.restrictScalars R - g.restrictScalars R := ext fun _ ↦ rfl

end Group

section Curry

variable (R : Type*) {A M N : Type*} [CommSemiring R] [CommSemiring A] [SMul R A]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module A M] [IsScalarTower R A M]
  [Module R N] [Module A N] [IsScalarTower R A N]

@[simp]
theorem curryLeft_restrictScalars {n : ℕ} (f : M [⋀^Fin (n + 1)]→ₗ[A] N) (x : M) :
    (f.restrictScalars R).curryLeft x = (f.curryLeft x).restrictScalars R := ext fun _ ↦ rfl

end Curry

end AlternatingMap

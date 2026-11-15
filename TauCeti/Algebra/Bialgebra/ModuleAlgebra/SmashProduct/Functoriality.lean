/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.ModuleAlgebra.SmashProduct.Basic
public import Mathlib.RingTheory.Bialgebra.Equiv

/-!
# Functoriality and canonical isomorphisms of smash products

This file establishes covariant functoriality of `TauCeti.SmashProduct` in equivariant algebra
homomorphisms and bialgebra homomorphisms, together with the canonical `R`-algebra equivalences
identifying degenerate cases of the smash product:

* for the trivial `H`-action `h · a = ε(h) • a`, `SmashProduct trivial ≃ₐ[R] A ⊗[R] H` recovers
  the ordinary tensor-product algebra;
* when `A = R`, the unique left `H`-module algebra structure on `R` is `trivial`, and
  `SmashProduct μ ≃ₐ[R] H` with inverse `includeRight μ : h ↦ 1 # h`;
* when `H = R`, the unique left `R`-module algebra structure on `A` is `trivial`, and
  `SmashProduct μ ≃ₐ[R] A` with inverse `includeLeft μ : a ↦ a # 1`.

## Main definitions

* `TauCeti.SmashProduct.map`: the `R`-algebra map `SmashProduct μ →ₐ[R] SmashProduct ν` sending
  `a # h ↦ f a # g h` for `g : H →ₐc[R] L` and `f : μ.Hom (ν.restrict g)`.
* `TauCeti.SmashProduct.mapLeft`, `TauCeti.SmashProduct.mapRight`: functoriality in the algebra
  variable alone and in the bialgebra variable alone.
* `TauCeti.SmashProduct.congr`: transport of smash products across an equivariant pair of an
  algebra isomorphism and a bialgebra isomorphism.
* `TauCeti.SmashProduct.trivialAlgEquiv`: `SmashProduct trivial ≃ₐ[R] A ⊗[R] H`.
* `TauCeti.SmashProduct.baseLeftAlgEquiv`: `SmashProduct μ ≃ₐ[R] H` for any
  `μ : LeftModuleAlgebra R H R`.
* `TauCeti.SmashProduct.baseRightAlgEquiv`: `SmashProduct μ ≃ₐ[R] A` for any
  `μ : LeftModuleAlgebra R R A`.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, CBMS Regional Conference Series in
  Mathematics 82, AMS, 1993, §4.1.
* Y. Qi, *Hopfological algebra*, Compos. Math. 150 (2014), 1–45, Example 2.8.
-/

public section

open scoped TensorProduct Coalgebra
open Coalgebra

namespace TauCeti

universe u v v' v'' w w' w''

namespace SmashProduct

section Functoriality

variable {R : Type u} [CommSemiring R]
variable {H : Type v} {L : Type v'} {P : Type v''}
variable {A : Type w} {B : Type w'} {C : Type w''}
variable [Semiring H] [Bialgebra R H] [Semiring L] [Bialgebra R L] [Semiring P] [Bialgebra R P]
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

/-- For a bialgebra homomorphism `g : H →ₐc[R] L` and an equivariant algebra homomorphism
`f : μ.Hom (ν.restrict g)`, the composites `a ↦ f a # 1` and `h ↦ 1 # g h` satisfy
`LeftModuleAlgebra.SmashCompatible`. -/
theorem smashCompatible_map {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R L B}
    (g : H →ₐc[R] L) (f : μ.Hom (ν.restrict g)) :
    μ.SmashCompatible ((includeLeft ν).comp f.toAlgHom) ((includeRight ν).comp g.toAlgHom) := by
  rw [LeftModuleAlgebra.smashCompatible_iff]
  intro h a
  simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom, LeftModuleAlgebra.Hom.coe_toAlgHom]
  rw [smashCompatible_include.apply (g h) (f a), ← CoalgHomClass.map_comp_comul_apply g h]
  exact TensorProduct.inductionOn (comul (R := R) h)
    (fun h₁ h₂ => by simp)
    (fun x y hx hy => by simp [map_add, hx, hy])

/-- Functoriality of `SmashProduct`: a bialgebra homomorphism `g : H →ₐc[R] L` and an equivariant
algebra homomorphism `f : μ.Hom (ν.restrict g)` induce an `R`-algebra homomorphism
`SmashProduct μ →ₐ[R] SmashProduct ν` sending `a # h ↦ f a # g h`. -/
def map {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R L B}
    (g : H →ₐc[R] L) (f : μ.Hom (ν.restrict g)) :
    SmashProduct μ →ₐ[R] SmashProduct ν :=
  lift ((includeLeft ν).comp f.toAlgHom) ((includeRight ν).comp g.toAlgHom)
    (smashCompatible_map g f)

@[simp]
theorem map_tmul {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R L B}
    (g : H →ₐc[R] L) (f : μ.Hom (ν.restrict g)) (a : A) (h : H) :
    map g f (tmul μ a h) = tmul ν (f a) (g h) := by
  simp [map]

theorem map_includeLeft {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R L B}
    (g : H →ₐc[R] L) (f : μ.Hom (ν.restrict g)) (a : A) :
    map g f (includeLeft μ a) = includeLeft ν (f a) := by
  simp

theorem map_includeRight {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R L B}
    (g : H →ₐc[R] L) (f : μ.Hom (ν.restrict g)) (h : H) :
    map g f (includeRight μ h) = includeRight ν (g h) := by
  simp

@[simp]
theorem map_comp_includeLeft {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R L B}
    (g : H →ₐc[R] L) (f : μ.Hom (ν.restrict g)) :
    (map g f).comp (includeLeft μ) = (includeLeft ν).comp f.toAlgHom := by
  ext a
  simp

@[simp]
theorem map_comp_includeRight {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R L B}
    (g : H →ₐc[R] L) (f : μ.Hom (ν.restrict g)) :
    (map g f).comp (includeRight μ) = (includeRight ν).comp g.toAlgHom := by
  ext h
  simp

/-- Composition of smash-product maps induced by composable equivariant algebra and bialgebra
homomorphisms. -/
theorem map_comp {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R L B}
    {ξ : LeftModuleAlgebra R P C}
    (g₂ : L →ₐc[R] P) (f₂ : ν.Hom (ξ.restrict g₂))
    (g₁ : H →ₐc[R] L) (f₁ : μ.Hom (ν.restrict g₁)) :
    (map g₂ f₂).comp (map g₁ f₁) =
      map (g₂.comp g₁)
        ⟨f₂.toAlgHom.comp f₁.toAlgHom, fun h a => by simp⟩ := by
  ext x <;> simp

/-- Covariant functoriality of `SmashProduct` in an `H`-equivariant algebra homomorphism
`f : μ.Hom ν`, fixing `H`. -/
def mapLeft {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R H B}
    (f : μ.Hom ν) : SmashProduct μ →ₐ[R] SmashProduct ν :=
  map (BialgHom.id R H) ⟨f.toAlgHom, fun h a => by simp⟩

@[simp]
theorem mapLeft_tmul {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R H B}
    (f : μ.Hom ν) (a : A) (h : H) :
    mapLeft f (tmul μ a h) = tmul ν (f a) h := by
  simp [mapLeft]

theorem mapLeft_includeLeft {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R H B}
    (f : μ.Hom ν) (a : A) :
    mapLeft f (includeLeft μ a) = includeLeft ν (f a) := by
  simp [mapLeft]

theorem mapLeft_includeRight {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R H B}
    (f : μ.Hom ν) (h : H) :
    mapLeft f (includeRight μ h) = includeRight ν h := by
  simp [mapLeft]

@[simp]
theorem mapLeft_id (μ : LeftModuleAlgebra R H A) :
    mapLeft (LeftModuleAlgebra.Hom.id μ) = AlgHom.id R (SmashProduct μ) := by
  ext x <;> simp

@[simp]
theorem mapLeft_comp {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R H B}
    {ξ : LeftModuleAlgebra R H C} (g : ν.Hom ξ) (f : μ.Hom ν) :
    (mapLeft g).comp (mapLeft f) = mapLeft (g.comp f) := by
  ext x <;> simp

/-- Covariant functoriality of `SmashProduct` in a bialgebra homomorphism `g : H →ₐc[R] L`,
sending `a # h` in `SmashProduct (μ.restrict g)` to `a # g h` in `SmashProduct μ`. -/
def mapRight (μ : LeftModuleAlgebra R L A) (g : H →ₐc[R] L) :
    SmashProduct (μ.restrict g) →ₐ[R] SmashProduct μ :=
  map g (LeftModuleAlgebra.Hom.id (μ.restrict g))

@[simp]
theorem mapRight_tmul (μ : LeftModuleAlgebra R L A) (g : H →ₐc[R] L) (a : A) (h : H) :
    mapRight μ g (tmul (μ.restrict g) a h) = tmul μ a (g h) := by
  simp [mapRight]

theorem mapRight_includeLeft (μ : LeftModuleAlgebra R L A) (g : H →ₐc[R] L) (a : A) :
    mapRight μ g (includeLeft (μ.restrict g) a) = includeLeft μ a := by
  simp [mapRight]

theorem mapRight_includeRight (μ : LeftModuleAlgebra R L A) (g : H →ₐc[R] L) (h : H) :
    mapRight μ g (includeRight (μ.restrict g) h) = includeRight μ (g h) := by
  simp [mapRight]

/-- Transport `SmashProduct` across an `R`-algebra isomorphism `eA : A ≃ₐ[R] B` and an
`R`-bialgebra isomorphism `eH : H ≃ₐc[R] L` intertwining the module-algebra actions. -/
def congr {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R L B}
    (eA : A ≃ₐ[R] B) (eH : H ≃ₐc[R] L)
    (heq : ∀ h a, eA (μ.action h a) = ν.action (eH h) (eA a)) :
    SmashProduct μ ≃ₐ[R] SmashProduct ν :=
  AlgEquiv.ofAlgHom
    (map eH.toBialgHom ⟨eA.toAlgHom, fun h a => by simpa using heq h a⟩)
    (map eH.symm.toBialgHom
      ⟨eA.symm.toAlgHom, fun l b => eA.injective <| by simp [heq]⟩)
    (by
      ext x
      · simp [← LeftModuleAlgebra.Hom.coe_toAlgHom]
      · simp)
    (by
      ext x
      · simp [← LeftModuleAlgebra.Hom.coe_toAlgHom]
      · simp)

@[simp]
theorem congr_tmul {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R L B}
    (eA : A ≃ₐ[R] B) (eH : H ≃ₐc[R] L)
    (heq : ∀ h a, eA (μ.action h a) = ν.action (eH h) (eA a)) (a : A) (h : H) :
    congr eA eH heq (tmul μ a h) = tmul ν (eA a) (eH h) := by
  simp [congr, ← LeftModuleAlgebra.Hom.coe_toAlgHom]

@[simp]
theorem congr_symm_tmul {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R L B}
    (eA : A ≃ₐ[R] B) (eH : H ≃ₐc[R] L)
    (heq : ∀ h a, eA (μ.action h a) = ν.action (eH h) (eA a)) (b : B) (l : L) :
    (congr eA eH heq).symm (tmul ν b l) = tmul μ (eA.symm b) (eH.symm l) := by
  simp [congr, ← LeftModuleAlgebra.Hom.coe_toAlgHom]

end Functoriality

/-! ### Canonical algebra equivalences in special cases -/

section CanonicalEquivs

variable (R : Type u) (H : Type v) (A : Type w)
variable [CommSemiring R] [Semiring H] [Bialgebra R H] [Semiring A] [Algebra R A]

/-- For the trivial `H`-action `h · a = ε(h) • a`, the smash product `A # H` is canonically
isomorphic as an `R`-algebra to the ordinary tensor-product algebra `A ⊗[R] H`. -/
def trivialAlgEquiv :
    SmashProduct (LeftModuleAlgebra.trivial (R := R) (H := H) (A := A)) ≃ₐ[R] A ⊗[R] H :=
  let μ₀ := LeftModuleAlgebra.trivial (R := R) (H := H) (A := A)
  AlgEquiv.ofLinearEquiv (linearEquiv μ₀) (by simp [Algebra.TensorProduct.one_def]) fun x y =>
    SmashProduct.inductionOn x
      (fun a h =>
        SmashProduct.inductionOn y
          (fun b l => by
            classical
            rw [tmul_mul_tmul_eq_sum (μ := μ₀) a (ℛ R h) b l, map_sum]
            have hterm (i : H × H) :
                (a * μ₀.action ((ℛ R h).left i) b) ⊗ₜ[R] ((ℛ R h).right i * l) =
                  (a * b) ⊗ₜ[R] ((counit (R := R) ((ℛ R h).left i) • (ℛ R h).right i) * l) := by
              rw [LeftModuleAlgebra.trivial_action, Algebra.mul_smul_comm,
                TensorProduct.smul_tmul, smul_mul_assoc]
            simp_rw [linearEquiv_apply, toTensor_tmul, hterm]
            have hsum :
                ∑ i ∈ (ℛ R h).index,
                  (a * b) ⊗ₜ[R] ((counit (R := R) ((ℛ R h).left i) • (ℛ R h).right i) * l) =
                (a * b) ⊗ₜ[R]
                  (∑ i ∈ (ℛ R h).index,
                    (counit (R := R) ((ℛ R h).left i) • (ℛ R h).right i) * l) :=
              (map_sum (TensorProduct.mk R A H (a * b)) _ _).symm
            rw [hsum, ← Finset.sum_mul, Coalgebra.sum_counit_smul (ℛ R h),
              Algebra.TensorProduct.tmul_mul_tmul])
          (fun y₁ y₂ hy₁ hy₂ => by rw [mul_add, map_add, map_add, hy₁, hy₂, mul_add]))
      (fun x₁ x₂ hx₁ hx₂ => by rw [add_mul, map_add, map_add, hx₁, hx₂, add_mul])

variable {R H A}

@[simp]
theorem trivialAlgEquiv_tmul (a : A) (h : H) :
    trivialAlgEquiv R H A (tmul LeftModuleAlgebra.trivial a h) = a ⊗ₜ[R] h := by
  simp [trivialAlgEquiv]

@[simp]
theorem trivialAlgEquiv_symm_tmul (a : A) (h : H) :
    (trivialAlgEquiv R H A).symm (a ⊗ₜ[R] h) = tmul LeftModuleAlgebra.trivial a h :=
  (trivialAlgEquiv R H A).symm_apply_eq.mpr (trivialAlgEquiv_tmul a h).symm

theorem trivialAlgEquiv_includeLeft (a : A) :
    trivialAlgEquiv R H A (includeLeft LeftModuleAlgebra.trivial a) = a ⊗ₜ[R] 1 := by
  simp

theorem trivialAlgEquiv_includeRight (h : H) :
    trivialAlgEquiv R H A (includeRight LeftModuleAlgebra.trivial h) = 1 ⊗ₜ[R] h := by
  simp

/-- For any left `H`-module algebra structure `μ` on the base semiring `R`, `R # H` is canonically
isomorphic as an `R`-algebra to `H`, with `r # h ↦ r • h` and inverse `includeRight μ : h ↦ 1 # h`.
-/
def baseLeftAlgEquiv (μ : LeftModuleAlgebra R H R) : SmashProduct μ ≃ₐ[R] H :=
  have hcompat : μ.SmashCompatible (Algebra.ofId R H) (AlgHom.id R H) := by
    rw [LeftModuleAlgebra.eq_trivial_of_self_left μ, LeftModuleAlgebra.smashCompatible_iff]
    intro h r
    classical
    rw [← (ℛ R h).eq, map_sum, map_sum]
    simp only [AlgHom.id_apply, Algebra.ofId_apply,
      TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.flip_apply,
      AlgHom.toLinearMap_apply, LeftModuleAlgebra.trivial_action, LinearMap.mul'_apply]
    have hterm (i : H × H) :
        algebraMap R H (counit (R := R) ((ℛ R h).left i) • r) * (ℛ R h).right i =
          algebraMap R H r * (counit (R := R) ((ℛ R h).left i) • (ℛ R h).right i) := by
      rw [smul_eq_mul, mul_comm, map_mul, mul_assoc, Algebra.smul_def]
    simp_rw [hterm, ← Finset.mul_sum, Coalgebra.sum_counit_smul (ℛ R h)]
    exact (Algebra.commutes r h).symm
  AlgEquiv.ofAlgHom
    (lift (Algebra.ofId R H) (AlgHom.id R H) hcompat)
    (includeRight μ)
    (lift_comp_includeRight _ _ hcompat)
    (by
      ext x
      · simp [algebraMap_apply]
      · simp)

@[simp]
theorem baseLeftAlgEquiv_tmul (μ : LeftModuleAlgebra R H R) (r : R) (h : H) :
    baseLeftAlgEquiv μ (tmul μ r h) = r • h := by
  simp [baseLeftAlgEquiv, Algebra.smul_def]

@[simp]
theorem baseLeftAlgEquiv_symm_apply (μ : LeftModuleAlgebra R H R) (h : H) :
    (baseLeftAlgEquiv μ).symm h = includeRight μ h :=
  (rfl)

theorem baseLeftAlgEquiv_includeRight (μ : LeftModuleAlgebra R H R) (h : H) :
    baseLeftAlgEquiv μ (includeRight μ h) = h := by
  simp

/-- When `A = R`, `includeRight μ : H →ₐ[R] SmashProduct μ` (`h ↦ 1 # h`) is bijective. -/
theorem includeRight_bijective_of_self (μ : LeftModuleAlgebra R H R) :
    Function.Bijective (includeRight μ) :=
  (baseLeftAlgEquiv μ).symm.bijective

/-- For any left `R`-module algebra structure `μ` on an `R`-algebra `A`, `A # R` is canonically
isomorphic as an `R`-algebra to `A`, with `a # r ↦ r • a` and inverse `includeLeft μ : a ↦ a # 1`.
-/
def baseRightAlgEquiv (μ : LeftModuleAlgebra R R A) : SmashProduct μ ≃ₐ[R] A :=
  have hcompat : μ.SmashCompatible (AlgHom.id R A) (Algebra.ofId R A) := by
    rw [LeftModuleAlgebra.eq_trivial_of_self_right μ, LeftModuleAlgebra.smashCompatible_iff]
    intro r a
    simp [Algebra.commutes]
  AlgEquiv.ofAlgHom
    (lift (AlgHom.id R A) (Algebra.ofId R A) hcompat)
    (includeLeft μ)
    (lift_comp_includeLeft _ _ hcompat)
    (by
      ext x
      · simp
      · simp only [AlgHom.comp_apply, AlgHom.id_apply, includeRight_apply, lift_tmul, map_one,
          one_mul, Algebra.ofId_apply, includeLeft_apply]
        rw [Algebra.algebraMap_eq_smul_one, smul_tmul, ← tmul_smul, smul_eq_mul, mul_one])

@[simp]
theorem baseRightAlgEquiv_tmul (μ : LeftModuleAlgebra R R A) (a : A) (r : R) :
    baseRightAlgEquiv μ (tmul μ a r) = r • a := by
  simp [baseRightAlgEquiv, Algebra.commutes, Algebra.smul_def]

@[simp]
theorem baseRightAlgEquiv_symm_apply (μ : LeftModuleAlgebra R R A) (a : A) :
    (baseRightAlgEquiv μ).symm a = includeLeft μ a :=
  (rfl)

theorem baseRightAlgEquiv_includeLeft (μ : LeftModuleAlgebra R R A) (a : A) :
    baseRightAlgEquiv μ (includeLeft μ a) = a := by
  simp

/-- When `H = R`, `includeLeft μ : A →ₐ[R] SmashProduct μ` (`a ↦ a # 1`) is bijective. -/
theorem includeLeft_bijective_of_self (μ : LeftModuleAlgebra R R A) :
    Function.Bijective (includeLeft μ) :=
  (baseRightAlgEquiv μ).symm.bijective

end CanonicalEquivs

end SmashProduct

end TauCeti

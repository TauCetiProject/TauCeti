/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
public import TauCeti.Algebra.Coalgebra.Comodule.Fixed
public import TauCeti.Algebra.HopfAlgebra.TensorShear

/-!
# Comodule algebras and Hopf–Galois extensions

Let `H` be an `R`-bialgebra. A (right) `H`-comodule algebra is an `R`-algebra `A` with a right
`H`-comodule structure whose coaction `ρ : A → A ⊗[R] H` is a homomorphism of algebras. When `H`
and `A` are commutative this is a right action `X × G → X` of the affine monoid scheme
`G = Spec H` on the affine scheme `X = Spec A`, over `Spec R`; the regular comodule algebra `H`
is the action of `G` on itself by right translation.

The **coinvariants** `A^{co H}` are the elements `a` with `ρ a = a ⊗ 1`, the functions on `X`
which are invariant under `G`. They form a subalgebra of `A`. For the action of a closed subgroup
on the ambient group by right translation, the analogous constructions are the coinvariants
`TauCeti.HopfIdeal.coinvariants` of a Hopf ideal and its canonical map
`TauCeti.HopfIdeal.canonicalMap`.

Let `B` be an algebra over which `A` is an algebra, acting by coinvariants. Geometrically
`q : X ⟶ Y = Spec B` is a `G`-invariant morphism. The **Galois map**

  `β : A ⊗[B] A → A ⊗[R] H,  a ⊗ a' ↦ (a ⊗ 1) ρ(a')`

is the coordinate map of `X × G ⟶ X ×_Y X`, `(x, g) ↦ (x, x g)`. When `A` is faithfully flat
over `B` and `β` is bijective, `A` is an `H`-Galois extension of `B`: `X ⟶ Y` is a `G`-torsor
for the faithfully flat topology, trivialised by its own base change `X ×_Y X ≅ X × G`.

The main result says that the base of a torsor is recovered as the invariant algebra: if `A` is
faithfully flat over `B` and `β` is injective, then `B` maps isomorphically onto `A^{co H}`
(`TauCeti.ComoduleAlgebra.coinvariants_eq_range`). The proof is faithfully flat descent: for
`a ∈ A^{co H}`, both `a ⊗ 1` and `1 ⊗ a` are sent by `β` to `a ⊗ 1`, so they agree in
`A ⊗[B] A`, and the equalizer of `A ⇉ A ⊗[B] A` is `B`. Consequently `Spec A ⟶ Spec B` is a
categorical quotient in affine schemes: an invariant algebra map into `A` factors uniquely
through `B` (`TauCeti.ComoduleAlgebra.existsUnique_comp_eq`).

For a commutative Hopf algebra `H`, the Galois map of the regular comodule algebra `H` over `R`
is the tensor shear `HopfAlgebra.tensorShearMulRight`, which is bijective
(`TauCeti.ComoduleAlgebra.galoisMap_self_bijective`). When `H` is moreover faithfully flat over
`R` (for instance when `R` is a field), `H` is therefore an `H`-Galois extension of `R`: the
trivial torsor `G ⟶ Spec R`.

## Main definitions

* `TauCeti.ComoduleAlgebra`: a right comodule algebra over a bialgebra.
* `TauCeti.ComoduleAlgebra.coactAlgHom`: the coaction as an algebra homomorphism.
* `TauCeti.ComoduleAlgebra.coinvariants`: the subalgebra of coinvariants.
* `TauCeti.ComoduleAlgebra.galoisMap`: the Galois map `A ⊗[B] A → A ⊗[R] H`.
* `TauCeti.ComoduleAlgebra.coinvariantsEquiv`: for a faithfully flat extension with injective
  Galois map, the algebra isomorphism `B ≃ A^{co H}`.

## Main results

* `TauCeti.ComoduleAlgebra.coinvariants_eq_range`: if `A` is faithfully flat over `B` and the
  Galois map is injective, the coinvariants are exactly the image of `B`.
* `TauCeti.ComoduleAlgebra.existsUnique_comp_eq`: under the same hypotheses, every invariant
  algebra map into `A` factors uniquely through `B`.
* `TauCeti.ComoduleAlgebra.galoisMap_self_bijective`: the regular comodule algebra of a
  commutative Hopf algebra has bijective Galois map.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, CBMS Regional Conference Series in
  Mathematics 82, AMS, 1993, §4.1 (comodule algebras and coinvariants) and §8.1 (Hopf–Galois
  extensions).
* H. F. Kreimer and M. Takeuchi, *Hopf algebras and Galois extensions of an algebra*, Indiana Univ.
  Math. J. **30** (1981), 675–692.
* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé IV, §5 (torsors) and
  Exposé V, §4.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w x

/-- A right **comodule algebra** over an `R`-bialgebra `H`: an `R`-algebra `A` with a right
`H`-comodule structure whose coaction `A → A ⊗[R] H` is multiplicative and unital, so that it is
a homomorphism of `R`-algebras. For commutative `H` and `A` it is an action of the affine monoid
scheme `Spec H` on the affine scheme `Spec A`. -/
class ComoduleAlgebra (R : Type u) (H : Type v) (A : Type w) [CommSemiring R] [Semiring H]
    [Bialgebra R H] [Semiring A] [Algebra R A] extends Comodule R H A where
  /-- The coaction is unital. -/
  coact_one : coact 1 = 1
  /-- The coaction is multiplicative. -/
  coact_mul (a b : A) : coact (a * b) = coact a * coact b

namespace ComoduleAlgebra

attribute [simp] coact_one coact_mul

section Semiring

variable (R : Type u) (H : Type v) (A : Type w) [CommSemiring R] [Semiring H] [Bialgebra R H]
  [Semiring A] [Algebra R A] [ComoduleAlgebra R H A]

/-- The coaction of a comodule algebra, as a homomorphism of `R`-algebras `A →ₐ[R] A ⊗[R] H`. -/
noncomputable def coactAlgHom : A →ₐ[R] A ⊗[R] H :=
  AlgHom.ofLinearMap (Comodule.coact (R := R) (C := H) (M := A)) coact_one coact_mul

variable {R H A} in
@[simp]
theorem coactAlgHom_apply (a : A) :
    coactAlgHom R H A a = Comodule.coact (R := R) (C := H) a :=
  (rfl)

@[simp]
theorem toLinearMap_coactAlgHom :
    (coactAlgHom R H A).toLinearMap = Comodule.coact (R := R) (C := H) (M := A) :=
  (rfl)

/-- The coaction sends a scalar `r` to `r ⊗ 1`. -/
@[simp]
theorem coact_algebraMap (r : R) :
    Comodule.coact (R := R) (C := H) (algebraMap R A r) = algebraMap R A r ⊗ₜ[R] 1 := by
  rw [← coactAlgHom_apply, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]

/-- The **coinvariants** `A^{co H}` of a comodule algebra: the subalgebra of elements `a` with
`coact a = a ⊗ 1`, the equalizer of the coaction and `a ↦ a ⊗ 1`. These are the functions on
`Spec A` invariant under the action of `Spec H`. Its underlying set is the fixed subcomodule
`TauCeti.Comodule.fixedSubcomodule` (`TauCeti.ComoduleAlgebra.coe_coinvariants`). -/
noncomputable def coinvariants : Subalgebra R A :=
  AlgHom.equalizer (coactAlgHom R H A) Algebra.TensorProduct.includeLeft

variable {R H A}

@[simp]
theorem mem_coinvariants {a : A} :
    a ∈ coinvariants R H A ↔ Comodule.coact (R := R) (C := H) a = a ⊗ₜ[R] 1 := by
  simp [coinvariants, AlgHom.mem_equalizer]

theorem coe_coinvariants :
    (coinvariants R H A : Set A) = Comodule.fixedSubcomodule R H A := by
  ext a
  simp

/-- An algebra map `φ : C → A` lands in the coinvariants exactly when it is invariant:
composing it with the coaction or with `a ↦ a ⊗ 1` gives the same map. -/
theorem range_le_coinvariants_iff {C : Type x} [Semiring C] [Algebra R C] (φ : C →ₐ[R] A) :
    φ.range ≤ coinvariants R H A ↔
      (coactAlgHom R H A).comp φ = Algebra.TensorProduct.includeLeft.comp φ := by
  refine ⟨fun h ↦ AlgHom.ext fun c ↦ ?_, fun h ↦ ?_⟩
  · simpa using h ⟨c, rfl⟩
  · rintro _ ⟨c, rfl⟩
    simpa using AlgHom.congr_fun h c

variable (R H) in
/-- The **regular comodule algebra**: a bialgebra is a comodule algebra over itself, with
coaction the comultiplication. It is the action of a monoid scheme on itself by right
translation. -/
instance instSelf : ComoduleAlgebra R H H where
  toComodule := Comodule.instSelf R H
  coact_one := Bialgebra.comul_one
  coact_mul := Bialgebra.comul_mul

@[simp]
theorem coactAlgHom_self : coactAlgHom R H H = Bialgebra.comulAlgHom R H :=
  AlgHom.ext fun _ ↦ (rfl)

end Semiring

/-! ### The Galois map -/

section Galois

variable {R : Type u} {H : Type v} {A : Type w} [CommSemiring R] [Semiring H]
  [Bialgebra R H] [CommSemiring A] [Algebra R A] [ComoduleAlgebra R H A]
  (B : Type x) [CommSemiring B] [Algebra R B] [Algebra B A] [IsScalarTower R B A]

/-- The coaction, regarded as a `B`-algebra homomorphism when `B` acts on `A` by coinvariants. -/
private noncomputable def coactAlgHomOver (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A) :
    A →ₐ[B] A ⊗[R] H where
  toRingHom := (coactAlgHom R H A).toRingHom
  commutes' b := by
    simpa [Algebra.TensorProduct.algebraMap_apply] using mem_coinvariants.1 (hB b)

/-- The **Galois map** `A ⊗[B] A → A ⊗[R] H`, `a ⊗ a' ↦ (a ⊗ 1) coact(a')`, of a comodule
algebra `A` over an algebra `B` acting by coinvariants. It is the coordinate map of
`(x, g) ↦ (x, x g) : Spec A × Spec H ⟶ Spec A ×_{Spec B} Spec A`, and it is linear over the
first copy of `A`. -/
noncomputable def galoisMap (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A) :
    A ⊗[B] A →ₐ[A] A ⊗[R] H :=
  Algebra.TensorProduct.lift (Algebra.ofId A _) (coactAlgHomOver B hB) fun a _ ↦
    Algebra.commutes a _

variable {B}

@[simp]
theorem galoisMap_tmul (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A) (a a' : A) :
    galoisMap B hB (a ⊗ₜ[B] a') =
      (a ⊗ₜ[R] 1) * Comodule.coact (R := R) (C := H) a' := by
  simp [galoisMap, coactAlgHomOver, Algebra.TensorProduct.algebraMap_apply]

/-- The Galois map sends `a ⊗ 1` to `a ⊗ 1`: it restricts to `a ↦ a ⊗ 1` on the first factor. -/
theorem galoisMap_comp_includeLeft (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A) :
    ((galoisMap B hB).restrictScalars R).comp
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[B] A) =
      Algebra.TensorProduct.includeLeft :=
  AlgHom.ext fun a ↦ by simp

/-- The Galois map restricts to the coaction on the second factor. -/
theorem galoisMap_comp_includeRight (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A) :
    ((galoisMap B hB).restrictScalars R).comp
        ((Algebra.TensorProduct.includeRight : A →ₐ[B] A ⊗[B] A).restrictScalars R) =
      coactAlgHom R H A :=
  AlgHom.ext fun a ↦ by simp [← Algebra.TensorProduct.one_def]

end Galois

/-! ### The coinvariants of a faithfully flat Galois extension -/

section FaithfullyFlat

variable {R : Type u} {H : Type v} {A : Type w} [CommSemiring R] [Semiring H] [Bialgebra R H]
  [CommRing A] [Algebra R A] [ComoduleAlgebra R H A]
  {B : Type x} [CommRing B] [Algebra R B] [Algebra B A] [IsScalarTower R B A]
  [Module.FaithfullyFlat B A]

/-- **The base of a torsor is its invariant algebra.** Let `A` be a comodule algebra which is
faithfully flat over an algebra `B` acting by coinvariants. If the Galois map
`A ⊗[B] A → A ⊗[R] H` is injective, in particular if `A` is an `H`-Galois extension of `B`, then
the coinvariants of `A` are exactly the image of `B`. -/
theorem coinvariants_eq_range (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A)
    (hinj : Function.Injective (galoisMap B hB)) :
    coinvariants R H A = (IsScalarTower.toAlgHom R B A).range := by
  refine le_antisymm (fun a ha ↦ ?_) ?_
  · -- `a ⊗ 1` and `1 ⊗ a` have the same image `a ⊗ 1` under the Galois map.
    have h : a ⊗ₜ[B] (1 : A) = 1 ⊗ₜ[B] a :=
      hinj (by simpa [← Algebra.TensorProduct.one_def] using (mem_coinvariants.1 ha).symm)
    obtain ⟨b, rfl⟩ : a ∈ Set.range (algebraMap B A) := by
      rw [← (Algebra.IsEffective.of_faithfullyFlat B A).eqLocus_includeLeft_includeRight]
      exact RingHom.mem_eqLocus.2 h
    exact ⟨b, rfl⟩
  · rintro _ ⟨b, rfl⟩
    exact hB b

/-- For a faithfully flat comodule algebra over `B` with injective Galois map, the isomorphism
`B ≃ A^{co H}` induced by the algebra map `B → A`. -/
noncomputable def coinvariantsEquiv (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A)
    (hinj : Function.Injective (galoisMap B hB)) : B ≃ₐ[R] coinvariants R H A :=
  (AlgEquiv.ofInjective (IsScalarTower.toAlgHom R B A)
    (FaithfulSMul.algebraMap_injective B A)).trans
    (Subalgebra.equivOfEq _ _ (coinvariants_eq_range hB hinj).symm)

@[simp]
theorem coe_coinvariantsEquiv_apply (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A)
    (hinj : Function.Injective (galoisMap B hB)) (b : B) :
    (coinvariantsEquiv hB hinj b : A) = algebraMap B A b :=
  (rfl)

@[simp]
theorem algebraMap_coinvariantsEquiv_symm_apply
    (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A)
    (hinj : Function.Injective (galoisMap B hB)) (a : coinvariants R H A) :
    algebraMap B A ((coinvariantsEquiv hB hinj).symm a) = a := by
  rw [← coe_coinvariantsEquiv_apply hB hinj, AlgEquiv.apply_symm_apply]

/-- **The categorical quotient in affine schemes.** Let `A` be a comodule algebra which is
faithfully flat over `B`, acting by coinvariants, with injective Galois map. An algebra map
`φ : C → A` which is invariant, in the sense that `coact ∘ φ = (· ⊗ 1) ∘ φ`, factors uniquely
through `B`. -/
theorem existsUnique_comp_eq (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A)
    (hinj : Function.Injective (galoisMap B hB)) {C : Type*} [Semiring C] [Algebra R C]
    (φ : C →ₐ[R] A)
    (hφ : (coactAlgHom R H A).comp φ = Algebra.TensorProduct.includeLeft.comp φ) :
    ∃! ψ : C →ₐ[R] B, (IsScalarTower.toAlgHom R B A).comp ψ = φ := by
  have hle : φ.range ≤ coinvariants R H A := (range_le_coinvariants_iff φ).2 hφ
  refine ⟨((coinvariantsEquiv hB hinj).symm.toAlgHom).comp (φ.codRestrict _ fun c ↦ hle ⟨c, rfl⟩),
    AlgHom.ext fun c ↦ by simp, fun ψ hψ ↦ AlgHom.ext fun c ↦ ?_⟩
  apply FaithfulSMul.algebraMap_injective B A
  simpa using AlgHom.congr_fun hψ c

end FaithfullyFlat

/-! ### The regular comodule algebra of a Hopf algebra -/

section Hopf

variable {R : Type u} {H : Type v} [CommSemiring R] [CommSemiring H] [HopfAlgebra R H]

/-- **The trivial torsor.** For a commutative Hopf algebra `H`, the Galois map of the regular
comodule algebra `H` over `R` is the tensor shear `a ⊗ b ↦ (a ⊗ 1) Δ b`, which is bijective. When
`H` is faithfully flat over `R`, the action of `Spec H` on itself by right translation therefore
makes it a torsor over `Spec R`. -/
theorem galoisMap_self_bijective :
    Function.Bijective (galoisMap R fun r ↦ (coinvariants R H H).algebraMap_mem r) := by
  have h : (galoisMap R fun r ↦ (coinvariants R H H).algebraMap_mem r).restrictScalars R =
      (HopfAlgebra.tensorShearMulRight (R := R) (H := H)).toAlgHom :=
    Algebra.TensorProduct.ext' fun a b ↦ by simp [HopfAlgebra.tensorShearMulRight_tmul]
  rw [← AlgHom.coe_restrictScalars' R, h, AlgEquiv.coe_toAlgHom]
  exact (HopfAlgebra.tensorShearMulRight (R := R)).bijective

end Hopf

end ComoduleAlgebra

end TauCeti

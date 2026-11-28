/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra.Basic
public import TauCeti.Algebra.HopfAlgebra.TensorShear

import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

/-!
# Galois maps and faithfully flat descent for comodule algebras

Let `H` be an `R`-bialgebra, `A` a right `H`-comodule algebra, and `B` an algebra over which `A` is
an algebra, acting by coinvariants. Geometrically `q : X ⟶ Y = Spec B` is a `G`-invariant morphism
for `G = Spec H` acting on `X = Spec A`. The **Galois map**

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

* `TauCeti.ComoduleAlgebra.coactAlgHomOver`: the coaction as a `B`-algebra homomorphism, for an
  algebra `B` acting by coinvariants.
* `TauCeti.ComoduleAlgebra.galoisMap`: the Galois map `A ⊗[B] A → A ⊗[R] H`.
* `TauCeti.ComoduleAlgebra.coinvariantsEquiv`: for a faithfully flat extension with injective
  Galois map, the algebra isomorphism `B ≃ A^{co H}`.

## Main results

* `TauCeti.ComoduleAlgebra.coinvariants_eq_range`: if `A` is faithfully flat over `B` and the
  Galois map is injective, the coinvariants are exactly the image of `B`.
* `TauCeti.ComoduleAlgebra.existsUnique_comp_eq`: under the same hypotheses, every invariant
  algebra map into `A` factors uniquely through `B`.
* `TauCeti.ComoduleAlgebra.surjective_galoisMap_of_surjective_galoisMap`: if the Galois map over
  `B` is surjective, so is the Galois map over the base ring.
* `TauCeti.ComoduleAlgebra.galoisMap_self_bijective`: the regular comodule algebra of a
  commutative Hopf algebra has bijective Galois map.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, CBMS Regional Conference Series in
  Mathematics 82, AMS, 1993, §8.1 (Hopf–Galois extensions).
* H. F. Kreimer and M. Takeuchi, *Hopf algebras and Galois extensions of an algebra*, Indiana Univ.
  Math. J. **30** (1981), 675–692.
* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé IV, §5 (torsors) and
  Exposé V, §4.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w x

namespace ComoduleAlgebra

/-! ### The Galois map -/

section Galois

variable {R : Type u} {H : Type v} {A : Type w} [CommSemiring R] [Semiring H]
  [Bialgebra R H] [CommSemiring A] [Algebra R A] [ComoduleAlgebra R H A]
  (B : Type x) [CommSemiring B] [Algebra R B] [Algebra B A] [IsScalarTower R B A]

/-- The coinvariants act on `A` by coinvariants, so that they are a base for the Galois map
`TauCeti.ComoduleAlgebra.galoisMap`. -/
theorem algebraMap_coinvariants_mem (c : coinvariants R H A) :
    algebraMap (coinvariants R H A) A c ∈ coinvariants R H A :=
  c.property

/-- The coaction, regarded as a `B`-algebra homomorphism when `B` acts on `A` by coinvariants. -/
noncomputable def coactAlgHomOver (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A) :
    A →ₐ[B] A ⊗[R] H where
  toRingHom := (coactAlgHom R H A).toRingHom
  commutes' b := by
    simpa [Algebra.TensorProduct.algebraMap_apply] using mem_coinvariants.1 (hB b)

@[simp]
theorem coactAlgHomOver_apply (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A) (a : A) :
    coactAlgHomOver B hB a = Comodule.coact (R := R) (C := H) a :=
  coactAlgHom_apply a

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

/-- If the Galois map over an algebra `B` acting by coinvariants is surjective, so is the Galois map
`A ⊗[R] A → A ⊗[R] H` over the base ring, which factors through it via `A ⊗[R] A → A ⊗[B] A`:
the action of `Spec H` on the total space of a torsor is free. -/
theorem surjective_galoisMap_of_surjective_galoisMap
    (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A)
    (h : Function.Surjective (galoisMap B hB)) :
    Function.Surjective (galoisMap R fun r ↦ (coinvariants R H A).algebraMap_mem r) := by
  have : (galoisMap B hB).comp (Algebra.TensorProduct.mapOfCompatibleSMul B R A A A) =
      galoisMap R fun r ↦ (coinvariants R H A).algebraMap_mem r :=
    Algebra.TensorProduct.ext' fun a a' ↦ by simp
  rw [← this, AlgHom.coe_comp]
  exact h.comp (Algebra.TensorProduct.mapOfCompatibleSMul_surjective B R A A A)

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

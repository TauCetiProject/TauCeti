/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import TauCeti.Algebra.Algebra.Tower
public import TauCeti.RingTheory.Pure.Basic

/-!
# Pure ring homomorphisms

A ring homomorphism `f : R →+* S` of commutative rings is *pure* if it is pure as a map of
`R`-modules (`LinearMap.IsPure`): for every `R`-module `P`, the map `P → P ⊗[R] S` is injective.
Pure ring maps are injective, every faithfully flat ring map is pure, and a ring map is faithfully
flat exactly when it is flat and pure. Purity is what makes contracted ideals and, more generally,
injectivity survive base change; it is the condition in the direct summand theorem.

## Main definitions

* `RingHom.IsPure`: `f : R →+* S` is pure if `R → S` is a pure map of `R`-modules.

## Main results

* `RingHom.IsPure.injective_tensorProduct_mk`, `RingHom.isPure_algebraMap_iff_forall_injective`:
  `R → S` is pure iff `P → S ⊗[R] P` is injective for every `R`-module `P`.
* `RingHom.isPure_algebraMap_iff_forall_injective_algebraMap`: `R → S` is pure iff
  `R' → R' ⊗[R] S` is injective for every commutative `R`-algebra `R'`.
* `RingHom.IsPure.injective`, `RingHom.IsPure.id`, `RingHom.IsPure.comp`,
  `RingHom.IsPure.of_comp`: pure ring maps are injective, contain the identities, are closed
  under composition, and if `g ∘ f` is pure then so is `f`.
* `RingHom.IsPure.algebraMap_tensorProduct`: purity is stable under base change.
* `RingHom.IsPure.of_bijective`, `RingHom.IsPure.containsIdentities`,
  `RingHom.IsPure.stableUnderComposition`, `RingHom.IsPure.respectsIso`,
  `RingHom.IsPure.isStableUnderBaseChange`: the same laws as properties of ring homomorphisms.
* `RingHom.FaithfullyFlat.isPure`, `RingHom.faithfullyFlat_iff_flat_and_isPure`: a ring map is
  faithfully flat iff it is flat and pure.
* `Module.Flat.of_isPure_algebraMap_of_flat`, `RingHom.Flat.of_comp_of_isPure`: if `R → T` is
  flat and factors through `R → S` with `S → T` pure, then `R → S` is flat. This is the ring
  form of `LinearMap.IsPure.flat_of_flat`.

## References

* Y. André, *La conjecture du facteur direct*, Publ. Math. IHÉS 127 (2018), Annexe A,
  Lemme A.2.1.
* The Stacks Project, Section *Universally injective module maps*.
-/

public section

open TensorProduct

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} {T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- A ring homomorphism `f : R →+* S` is *pure* if it is pure as a map of `R`-modules: the map
`P ⊗[R] R → P ⊗[R] S` is injective for every `R`-module `P` (`LinearMap.IsPure`). -/
def IsPure (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  (Algebra.linearMap R S).IsPure

/-- The structure map of an algebra is pure iff it is pure as a map of `R`-modules. -/
theorem isPure_algebraMap_iff [Algebra R S] :
    (algebraMap R S).IsPure ↔ (Algebra.linearMap R S).IsPure := by
  rw [IsPure, toAlgebra_algebraMap]

section Algebra

variable [Algebra R S]

/-- If `R → S` is pure, then `P → S ⊗[R] P`, `p ↦ 1 ⊗ p`, is injective for every `R`-module `P`,
in any universe. -/
theorem IsPure.injective_tensorProduct_mk (h : (algebraMap R S).IsPure) (P : Type*)
    [AddCommGroup P] [Module R P] : Function.Injective (TensorProduct.mk R S P 1) := by
  rw [injective_mk_one_iff]
  exact (isPure_algebraMap_iff.mp h).rTensor_injective P

/-- `R → S` is pure if and only if `P → S ⊗[R] P`, `p ↦ 1 ⊗ p`, is injective for every
`R`-module `P`. -/
theorem isPure_algebraMap_iff_forall_injective :
    (algebraMap R S).IsPure ↔ ∀ (P : Type u) [AddCommGroup P] [Module R P],
      Function.Injective (TensorProduct.mk R S P 1) := by
  refine ⟨fun h P _ _ ↦ h.injective_tensorProduct_mk P, fun H ↦ ?_⟩
  rw [isPure_algebraMap_iff, LinearMap.isPure_iff]
  intro P _ _
  exact (LinearMap.lTensor_inj_iff_rTensor_inj P _).mpr ((injective_mk_one_iff P S).mp (H P))

/-- If `R → S` is pure, then `R' → R' ⊗[R] S` is injective for every commutative `R`-algebra `R'`,
in any universe. -/
theorem IsPure.injective_algebraMap_tensorProduct (h : (algebraMap R S).IsPure) (R' : Type*)
    [CommRing R'] [Algebra R R'] : Function.Injective (algebraMap R' (R' ⊗[R] S)) := by
  have := (isPure_algebraMap_iff.mp h).lTensor_injective R'
  rw [← Algebra.TensorProduct.linearMap_comp_rid, LinearMap.coe_comp] at this
  exact this.of_comp_right (Algebra.TensorProduct.rid R R R').surjective

/-- `R → S` is pure if and only if `R' → R' ⊗[R] S` is injective for every commutative
`R`-algebra `R'`. For the converse, an `R`-module `P` is a direct summand of the trivial
square-zero extension `R ⊕ P`. -/
theorem isPure_algebraMap_iff_forall_injective_algebraMap :
    (algebraMap R S).IsPure ↔ ∀ (R' : Type u) [CommRing R'] [Algebra R R'],
      Function.Injective (algebraMap R' (R' ⊗[R] S)) := by
  refine ⟨fun h R' _ _ ↦ h.injective_algebraMap_tensorProduct R', fun H ↦ ?_⟩
  rw [isPure_algebraMap_iff, LinearMap.isPure_iff]
  intro P _ _
  let _ : Module Rᵐᵒᵖ P := Module.compHom P ((RingHom.id R).fromOpposite fun _ _ ↦ .all _ _)
  have : IsCentralScalar R P := ⟨fun _ _ ↦ rfl⟩
  have h := (H (TrivSqZeroExt R P)).comp (TrivSqZeroExt.inr_injective (R := R) (M := P))
  -- `inr p ⊗ 1` is the image of `p ⊗ 1` under `inr ⊗ S`.
  rw [← EquivLike.injective_comp (TensorProduct.rid R P).symm]
  refine Function.Injective.of_comp (f := (TrivSqZeroExt.inrHom R P).rTensor S) ?_
  convert h using 1
  ext p
  simp [Algebra.TensorProduct.algebraMap_apply]

/-- If `R → S` is pure, then so is its base change `R' → R' ⊗[R] S`. -/
theorem IsPure.algebraMap_tensorProduct (h : (algebraMap R S).IsPure) (R' : Type*)
    [CommRing R'] [Algebra R R'] : (algebraMap R' (R' ⊗[R] S)).IsPure := by
  rw [isPure_algebraMap_iff]
  have : Algebra.linearMap R' (R' ⊗[R] S) =
      (Algebra.linearMap R S).baseChange R' ∘ₗ
        (AlgebraTensorModule.rid R R' R').symm.toLinearMap := by
    ext
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [this]
  exact ((isPure_algebraMap_iff.mp h).baseChange R').comp (LinearEquiv.isPure _)

end Algebra

namespace IsPure

/-- A pure ring homomorphism is injective. -/
theorem injective {f : R →+* S} (hf : f.IsPure) : Function.Injective f := by
  algebraize [f]
  rw [← algebraMap_toAlgebra f, isPure_algebraMap_iff] at hf
  exact hf.injective

variable (R) in
/-- The identity ring homomorphism is pure. -/
theorem id : (RingHom.id R).IsPure := by
  rw [← Algebra.algebraMap_self, isPure_algebraMap_iff]
  exact LinearMap.isPure_of_comp_eq_id (g := LinearMap.id) (by ext; simp)

/-- The composite of pure ring homomorphisms is pure. -/
theorem comp {f : R →+* S} {g : S →+* T} (hf : f.IsPure) (hg : g.IsPure) : (g.comp f).IsPure := by
  algebraize [f, g, g.comp f]
  rw [← algebraMap_toAlgebra (g.comp f), isPure_algebraMap_iff,
    IsScalarTower.linearMap_eq_restrictScalars_comp R S T]
  exact (LinearMap.IsPure.restrictScalars hg).comp hf

/-- If `g ∘ f` is pure, then `f` is pure. -/
theorem of_comp {f : R →+* S} {g : S →+* T} (h : (g.comp f).IsPure) : f.IsPure := by
  algebraize [f, g, g.comp f]
  rw [← algebraMap_toAlgebra (g.comp f), isPure_algebraMap_iff,
    IsScalarTower.linearMap_eq_restrictScalars_comp R S T] at h
  exact h.of_comp

/-- A bijective ring homomorphism is pure. -/
theorem of_bijective {f : R →+* S} (hf : Function.Bijective f) : f.IsPure := by
  algebraize [f]
  rw [← algebraMap_toAlgebra f, isPure_algebraMap_iff]
  exact (LinearEquiv.ofBijective (Algebra.linearMap R S) hf).isPure

/-- Identities are pure. -/
theorem containsIdentities : ContainsIdentities IsPure := RingHom.IsPure.id

/-- Pure ring homomorphisms are closed under composition. -/
theorem stableUnderComposition : StableUnderComposition IsPure := by
  introv R hf hg
  exact hf.comp hg

/-- Purity is invariant under composing with ring isomorphisms. -/
theorem respectsIso : RespectsIso IsPure :=
  stableUnderComposition.respectsIso fun e ↦ of_bijective e.bijective

/-- Purity is stable under base change. -/
theorem isStableUnderBaseChange : IsStableUnderBaseChange IsPure :=
  .mk respectsIso fun _ _ _ _ _ _ _ _ h ↦ h.algebraMap_tensorProduct _

end IsPure

/-- A faithfully flat ring homomorphism is pure. -/
theorem FaithfullyFlat.isPure {f : R →+* S} (hf : f.FaithfullyFlat) : f.IsPure := by
  algebraize [f]
  rw [← algebraMap_toAlgebra f, isPure_algebraMap_iff_forall_injective]
  rw [← algebraMap_toAlgebra f, faithfullyFlat_algebraMap_iff] at hf
  exact fun P _ _ ↦ Module.FaithfullyFlat.tensorProduct_mk_injective P

/-- A ring homomorphism is faithfully flat if and only if it is flat and pure. -/
theorem faithfullyFlat_iff_flat_and_isPure {f : R →+* S} :
    f.FaithfullyFlat ↔ f.Flat ∧ f.IsPure := by
  refine ⟨fun hf ↦ ⟨hf.flat, hf.isPure⟩, fun ⟨hflat, hpure⟩ ↦ ?_⟩
  algebraize [f]
  rw [← algebraMap_toAlgebra f, faithfullyFlat_algebraMap_iff,
    Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality]
  rw [← algebraMap_toAlgebra f] at hflat hpure
  refine ⟨flat_algebraMap_iff.mp hflat, fun N _ _ _ ↦ ?_⟩
  exact (hpure.injective_tensorProduct_mk N).subsingleton

end RingHom

namespace Module.Flat

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
  [Algebra R T] [IsScalarTower R S T]

/-- **Flatness descends along pure maps.** If `T` is flat over `R` and `S → T` is pure, then `S`
is flat over `R`. -/
theorem of_isPure_algebraMap_of_flat (h : (algebraMap S T).IsPure) [Flat R T] : Flat R S :=
  ((RingHom.isPure_algebraMap_iff.mp h).restrictScalars (R := R)).flat_of_flat

end Module.Flat

/-- **Flatness descends along pure maps.** If `g ∘ f` is flat and `g` is pure, then `f` is
flat. -/
theorem RingHom.Flat.of_comp_of_isPure {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    {f : R →+* S} {g : S →+* T} (hgf : (g.comp f).Flat) (hg : g.IsPure) : f.Flat := by
  algebraize [f, g, g.comp f]
  rw [← algebraMap_toAlgebra (g.comp f), flat_algebraMap_iff] at hgf
  rw [← algebraMap_toAlgebra f, flat_algebraMap_iff]
  exact Module.Flat.of_isPure_algebraMap_of_flat R S T hg

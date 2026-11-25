/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing

import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import TauCeti.RingTheory.KrullDimension.Basic

/-!
# Arc-covers of rings

A ring homomorphism `f : A →+* B` is an *arc-cover* when every homomorphism `A →+* V` to a
valuation domain of rank at most one lifts along `f`, after an injective local homomorphism
`V →+* W` to another valuation domain of rank at most one. On spectra this is the arc-cover
condition of Bhatt and Mathew for `Spec B → Spec A`; the test rings live in the universe of `A`
and `B`. Unlike the v-topology, only valuation rings of rank at most one are tested.

The main theorem is that a Milnor square gives an arc-cover: if `f : A →+* B` carries an ideal
`I` of `A` bijectively onto an ideal of `B`, then `A →+* A ⧸ I × B` is an arc-cover. A map
`A →+* V` either kills `I`, and factors through `A ⧸ I`, or it extends along `f`; the extension
stays inside `V` because a rank-one valuation is archimedean. Milnor squares are the source of
arc-covers that are not v-covers, and they are the squares on which the excision criterion for
arc-sheaves is tested.

## Main definitions

* `RingHom.IsArcCover`: the rank-at-most-one valuative lifting property of a ring homomorphism.

## Main results

* `RingHom.IsArcCover.id`, `RingHom.IsArcCover.comp`, `RingHom.IsArcCover.of_comp`: identities
  are arc-covers, arc-covers compose, and a map through which an arc-cover factors is one.
* `RingHom.IsArcCover.of_comp_eq_id`, `RingHom.IsArcCover.of_bijective`: a homomorphism with a
  retraction, in particular a bijective one, is an arc-cover.
* `RingHom.IsArcCover.respectsIso`, `RingHom.IsArcCover.isStableUnderBaseChange`: arc-covers
  respect isomorphisms and are stable under base change.
* `RingHom.IsArcCover.of_surjective_of_ker_le_nilradical`: a surjection with nil kernel is an
  arc-cover, although it need not be flat.
* `RingHom.IsArcCover.comap_surjective`: an arc-cover is surjective on prime spectra.
* `RingHom.exists_comp_eq_of_injOn`: a homomorphism to a valuation domain of rank at most one
  which does not kill `I` extends along a map carrying `I` bijectively onto an ideal.
* `RingHom.isArcCover_quotientMk_prod`: a Milnor square gives an arc-cover.

## References

* B. Bhatt and A. Mathew, *The arc-topology*, Forum Math. Pi 9 (2021), Definition 1.2,
  Lemma 2.3, Lemma 2.7 and Corollary 2.9.
-/

public section


universe u

namespace RingHom

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-- A ring homomorphism `f : A →+* B` is an *arc-cover* if every homomorphism `φ : A →+* V` to
a valuation domain `V` of rank at most one lifts along `f` after an injective local homomorphism
`e : V →+* W` to a valuation domain `W` of rank at most one: there is `ψ : B →+* W` with
`ψ ∘ f = e ∘ φ`. The test rings live in the universe of `A` and `B`. -/
def IsArcCover (f : A →+* B) : Prop :=
  ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V] [Ring.KrullDimLE 1 V]
    (φ : A →+* V),
    ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : ValuationRing W)
      (_ : Ring.KrullDimLE 1 W) (e : V →+* W) (ψ : B →+* W),
      Function.Injective e ∧ IsLocalHom e ∧ ψ.comp f = e.comp φ

/-- Unfolding `RingHom.IsArcCover`. -/
theorem isArcCover_iff (f : A →+* B) :
    f.IsArcCover ↔
      ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V] [Ring.KrullDimLE 1 V]
        (φ : A →+* V),
        ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : ValuationRing W)
          (_ : Ring.KrullDimLE 1 W) (e : V →+* W) (ψ : B →+* W),
          Function.Injective e ∧ IsLocalHom e ∧ ψ.comp f = e.comp φ :=
  Iff.rfl

namespace IsArcCover

/-- If every test homomorphism lifts along `f` without enlarging the valuation ring, then `f` is
an arc-cover. -/
theorem of_forall_exists_comp_eq {f : A →+* B}
    (h : ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V] [Ring.KrullDimLE 1 V]
      (φ : A →+* V), ∃ ψ : B →+* V, ψ.comp f = φ) :
    f.IsArcCover := by
  intro V _ _ _ _ φ
  obtain ⟨ψ, hψ⟩ := h V φ
  exact ⟨V, ‹_›, ‹_›, ‹_›, ‹_›, RingHom.id V, ψ, Function.injective_id, inferInstance,
    by simpa using hψ⟩

/-- The identity is an arc-cover. -/
protected theorem id : (RingHom.id A).IsArcCover :=
  of_forall_exists_comp_eq fun _ _ _ _ _ φ => ⟨φ, rfl⟩

/-- Arc-covers compose. -/
protected theorem comp {f : A →+* B} {g : B →+* C} (hf : f.IsArcCover) (hg : g.IsArcCover) :
    (g.comp f).IsArcCover := by
  intro V _ _ _ _ φ
  obtain ⟨W₁, _, _, _, _, e₁, ψ₁, he₁, _, hψ₁⟩ := hf V φ
  obtain ⟨W₂, i₁, i₂, i₃, i₄, e₂, ψ₂, he₂, _, hψ₂⟩ := hg W₁ ψ₁
  refine ⟨W₂, i₁, i₂, i₃, i₄, e₂.comp e₁, ψ₂, he₂.comp he₁, inferInstance, ?_⟩
  rw [← RingHom.comp_assoc, hψ₂, RingHom.comp_assoc, hψ₁, RingHom.comp_assoc]

/-- If a composite `g ∘ f` is an arc-cover, then so is `f`: restrict a lift along `g ∘ f`. -/
theorem of_comp {f : A →+* B} {g : B →+* C} (h : (g.comp f).IsArcCover) :
    f.IsArcCover := by
  intro V _ _ _ _ φ
  obtain ⟨W, i₁, i₂, i₃, i₄, e, ψ, he, he', hψ⟩ := h V φ
  exact ⟨W, i₁, i₂, i₃, i₄, e, ψ.comp g, he, he', by rw [RingHom.comp_assoc, hψ]⟩

/-- A ring homomorphism with a retraction is an arc-cover; on spectra, a morphism with a section
is an arc-cover. -/
theorem of_comp_eq_id {f : A →+* B} (g : B →+* A) (h : g.comp f = RingHom.id A) :
    f.IsArcCover :=
  of_comp (g := g) (h ▸ IsArcCover.id)

/-- Bijective ring homomorphisms are arc-covers. -/
theorem of_bijective {f : A →+* B} (hf : Function.Bijective f) : f.IsArcCover :=
  of_comp_eq_id (RingEquiv.ofBijective f hf).symm.toRingHom
    (by
      ext x
      simpa [RingEquiv.ofBijective_apply] using (RingEquiv.ofBijective f hf).symm_apply_apply x)

/-- Identities are arc-covers, in the form used by Mathlib's ring-homomorphism properties. -/
theorem containsIdentities : ContainsIdentities IsArcCover := fun _ _ => IsArcCover.id

/-- Arc-covers are stable under composition. -/
theorem stableUnderComposition : StableUnderComposition IsArcCover := by
  introv R hf hg
  exact hf.comp hg

/-- Arc-covers respect ring isomorphisms of the source and target. -/
theorem respectsIso : RespectsIso IsArcCover :=
  stableUnderComposition.respectsIso fun e => of_bijective e.bijective

/-- Arc-covers are stable under base change: if `R →+* T` is an arc-cover, then so is
`S →+* S ⊗[R] T` for every `R`-algebra `S`. -/
theorem isStableUnderBaseChange : IsStableUnderBaseChange IsArcCover := by
  refine IsStableUnderBaseChange.mk respectsIso ?_
  introv h
  intro V _ _ _ _ φ
  obtain ⟨W, i₁, i₂, i₃, i₄, e, ψ, he, he', hψ⟩ := h V (φ.comp (algebraMap R S))
  let : Algebra R W := ((e.comp φ).comp (algebraMap R S)).toAlgebra
  let φ' : S →ₐ[R] W := { e.comp φ with commutes' := fun _ => rfl }
  let ψ' : T →ₐ[R] W := { ψ with commutes' := fun r => congr($hψ r) }
  refine ⟨W, i₁, i₂, i₃, i₄, e, (Algebra.TensorProduct.productMap φ' ψ').toRingHom, he, he', ?_⟩
  ext s
  simp [Algebra.TensorProduct.algebraMap_apply, φ', ψ']

/-- A surjective ring homomorphism whose kernel consists of nilpotent elements is an arc-cover,
since every homomorphism to a domain kills nilpotent elements. For instance the reduction
`k[ε]/(ε²) →+* k` is an arc-cover, although it is not flat. -/
theorem of_surjective_of_ker_le_nilradical {f : A →+* B}
    (hf : Function.Surjective f) (hker : RingHom.ker f ≤ nilradical A) : f.IsArcCover := by
  refine of_forall_exists_comp_eq fun V _ _ _ _ φ => ?_
  have hle : RingHom.ker f ≤ RingHom.ker φ := fun a ha =>
    (RingHom.mem_ker).mpr ((mem_nilradical.mp (hker ha)).map φ).eq_zero
  exact ⟨f.liftOfSurjective hf ⟨φ, hle⟩, f.liftOfSurjective_comp hf ⟨φ, hle⟩⟩

/-- An arc-cover is surjective on prime spectra: test it against the residue field of a prime. -/
theorem comap_surjective {f : A →+* B} (h : f.IsArcCover) :
    Function.Surjective (PrimeSpectrum.comap f) := by
  intro p
  obtain ⟨W, _, _, _, _, e, ψ, he, _, hψ⟩ := h p.asIdeal.ResidueField (algebraMap A _)
  refine ⟨⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩, PrimeSpectrum.ext ?_⟩
  -- The preimage of `ker ψ` is `ker (ψ ∘ f) = ker (e ∘ φ) = ker φ = p`, as `e` is injective.
  rw [PrimeSpectrum.comap_asIdeal, RingHom.comap_ker, hψ, RingHom.ker_comp_of_injective _ he,
    Ideal.ker_algebraMap_residueField]

end IsArcCover

section Milnor

/-- Let `f : A →+* B` carry the ideal `I` bijectively onto an ideal of `B`. Then every
homomorphism `φ : A →+* V` to a valuation domain of rank at most one which does not kill `I`
extends along `f`. -/
theorem exists_comp_eq_of_injOn {A B V : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {I : Ideal A} [CommRing V] [IsDomain V] [ValuationRing V] [Ring.KrullDimLE 1 V]
    (hinj : Set.InjOn f I) (himage : (I.map f : Set B) ⊆ f '' I)
    (φ : A →+* V) {x : A} (hxI : x ∈ I) (hx : φ x ≠ 0) :
    ∃ ψ : B →+* V, ψ.comp f = φ := by
  -- Fix `x ∈ I` with `φ x ≠ 0`. For `b : B`, write `b * f x = f y` with `y ∈ I`; the extension
  -- sends `b` to `φ y / φ x`, which lies in `V` because a rank-one valuation is archimedean.
  have hg : ∀ b : B, ∃ y ∈ I, f y = b * f x := fun b =>
    himage (Ideal.mul_mem_left _ b (Ideal.mem_map_of_mem f hxI))
  choose g hgI hgf using hg
  -- `g b` is the unique `y ∈ I` with `f y = b * f x`.
  have hg_eq : ∀ b y, y ∈ I → f y = b * f x → g b = y := fun b y hy h =>
    hinj (hgI b) hy ((hgf b).trans h.symm)
  -- `φ x` divides `φ (g b)`; otherwise `φ x = φ (g b) * t` for a nonunit `t`, and then every
  -- power of `t` divides `φ x`.
  have hdvd : ∀ b, φ x ∣ φ (g b) := by
    intro b
    obtain h | ⟨t, ht⟩ := ValuationRing.dvd_total (φ x) (φ (g b))
    · exact h
    by_cases htu : IsUnit t
    · exact ⟨↑htu.unit⁻¹, by rw [ht, mul_assoc, IsUnit.mul_val_inv, mul_one]⟩
    refine absurd (FiniteMultiplicity.of_not_isUnit_of_krullDimLE_one htu hx)
      (FiniteMultiplicity.not_iff_forall.mpr fun n => ?_)
    have hpow : g b ^ n * x = g (b ^ n) * x ^ n :=
      hinj (I.mul_mem_left _ hxI) (I.mul_mem_right _ (hgI _))
        (by simp only [map_mul, map_pow, hgf]; ring)
    have hφ : φ x ^ n * φ x = φ x ^ n * (t ^ n * φ (g (b ^ n))) := by
      have := congr(φ $hpow)
      simp only [map_mul, map_pow] at this
      calc φ x ^ n * φ x = (φ (g b) * t) ^ n * φ x := by rw [← ht]
        _ = φ x ^ n * (t ^ n * φ (g (b ^ n))) := by linear_combination t ^ n * this
    exact ⟨φ (g (b ^ n)), mul_left_cancel₀ (pow_ne_zero n hx) hφ⟩
  choose q hq using hdvd
  have hq' : ∀ b c, φ (g b) = φ x * c → q b = c := fun b c h =>
    mul_left_cancel₀ hx ((hq b).symm.trans h)
  refine ⟨{ toFun := q, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · exact hq' 1 1 (by rw [hg_eq 1 x hxI (one_mul _).symm, mul_one])
  · intro b c
    have hbc : g (b * c) * x = g b * g c :=
      hinj (I.mul_mem_right _ (hgI _)) (I.mul_mem_right _ (hgI _))
        (by simp only [map_mul, hgf]; ring)
    refine hq' _ _ (mul_right_cancel₀ hx ?_)
    rw [← map_mul, hbc, map_mul, hq, hq]
    ring
  · exact hq' 0 0 (by rw [hg_eq 0 0 I.zero_mem (by simp), map_zero, mul_zero])
  · intro b c
    refine hq' _ _ ?_
    rw [hg_eq _ _ (I.add_mem (hgI b) (hgI c)) (by simp [hgf, add_mul]), map_add, hq, hq,
      mul_add]
  · ext a
    refine hq' _ _ ?_
    rw [hg_eq _ _ (I.mul_mem_left a hxI) (map_mul f a x), map_mul, mul_comm]

variable (f : A →+* B) {I : Ideal A}

/-- A Milnor square gives an arc-cover: if `f : A →+* B` carries the ideal `I` bijectively onto
an ideal of `B`, then `A →+* A ⧸ I × B` is an arc-cover. On spectra,
`Spec (A ⧸ I) ⊔ Spec B → Spec A` is an arc-cover, and no enlargement of the valuation ring is
needed. -/
theorem isArcCover_quotientMk_prod (hinj : Set.InjOn f I) (himage : (I.map f : Set B) ⊆ f '' I) :
    ((Ideal.Quotient.mk I).prod f).IsArcCover := by
  refine IsArcCover.of_forall_exists_comp_eq fun V _ _ _ _ φ => ?_
  -- A test map that kills `I` factors through `A ⧸ I`, and any other extends along `f`.
  by_cases h : ∀ x ∈ I, φ x = 0
  · exact ⟨(Ideal.Quotient.lift I φ h).comp (RingHom.fst _ _), by ext a; simp⟩
  · push Not at h
    obtain ⟨x, hxI, hx⟩ := h
    obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_injOn f hinj himage φ hxI hx
    exact ⟨ψ.comp (RingHom.snd _ _), by rw [RingHom.comp_assoc, RingHom.snd_comp_prod, hψ]⟩

end Milnor

end RingHom

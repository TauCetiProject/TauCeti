/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Length
public import TauCeti.Algebra.Category.FGModuleCat.Generator.Basic

import Mathlib.RingTheory.Finiteness.Small
import TauCeti.Algebra.Category.FGModuleCat.Injective
import TauCeti.Algebra.Category.FGModuleCat.MatlisDuality.Projectivization
import TauCeti.Algebra.Subalgebra.Center
import TauCeti.RingTheory.Artinian.FiniteLength
import TauCeti.RingTheory.Artinian.Subalgebra
import TauCeti.RingTheory.MatlisDuality.ArtinAlgebra
import TauCeti.RingTheory.MatlisDuality.Cogenerator

/-!
# Coseparators and injective modules over their endomorphism rings

Over an Artin algebra `A`, with `A` small in the module universe, a coseparator `M` of `mod A` is an
injective module over its endomorphism ring (`CategoryTheory.IsCoseparator.injective_end`),
dually to a generator being projective over it (`TauCeti.Module.IsGenerator.projective_end`). By
projectivization and the Hom-tensor adjunction the dual of `M` is projective as a right module over
the endomorphism ring (a left module over its opposite), and Matlis biduality returns to `M`. This
is the cogenerator half of the forward direction of the Morita-Tachikawa correspondence
(`TauCeti.two_le_dominantDimension_end`).

Conversely, a finitely generated injective module `Q` over an Artin algebra `Γ` is a cogenerator
over its endomorphism ring `B = Module.End Γ Q`: every nonzero element of every `B`-module is
detected by a `B`-linear map to `Q` (`TauCeti.exists_linearMap_end_apply_ne_zero_of_injective`),
so `Q` is a coseparator of `mod B` (`FGModuleCat.isCoseparator_end_of_injective`). This is dual to
a finitely generated projective module being a generator over its endomorphism ring
(`TauCeti.Module.isGenerator_end_of_projective`), and is the cogenerator half of the converse of
the Morita-Tachikawa correspondence (`TauCeti.exists_algEquiv_end_of_two_le_dominantDimension`).

## Implementation notes

Write `D = Hom_C(-, E)` for the Matlis duality over a commutative ring `C` with `Γ` a `C`-algebra.
As `Q` is Artinian, it embeds into a finite power `(D Γ)ⁿ`
(`TauCeti.exists_injective_linearMap_pi_matlisDual`), and as `Q` is injective the embedding `s`
splits, with retraction `r`; write `ψᵢ` and `ρᵢ` for their coordinates. By the Hom-tensor adjunction
(`TauCeti.MatlisDual.equivLinearMapDualRegular`) each map `D Q → B`, `χ ↦ ρᵢ ∘ adj χ`, is right
`B`-linear; dualizing it and applying biduality gives a `B`-linear map `D B → Q`. Together
these maps embed `D B` into `Qⁿ`, because `b = ∑ᵢ ρᵢ ∘ ψᵢ ∘ b` for every `b ∈ B`. As `D B` detects
the nonzero elements of every `B`-module, by the adjunction for `B`, so does `Q`. The argument works
with the elementwise description `FGModuleCat.isCoseparator_iff`, so the dual `D B` is never needed
as an object of `mod B`.

## Main results

* `CategoryTheory.IsCoseparator.injective_end`: over an Artin algebra, a coseparator `M` of `mod A`
  is an injective module over its endomorphism ring.
* `TauCeti.exists_linearMap_end_apply_ne_zero_of_injective`: an injective module of finite length
  over `C` is a cogenerator over its endomorphism ring.
* `FGModuleCat.isCoseparator_end_of_injective`: over an Artin algebra, a finitely generated
  injective module is a coseparator of `mod B` for its endomorphism ring `B`.

## References

* B. J. Müller, *The classification of algebras by dominant dimension*, Canad. J. Math. 20 (1968),
  398–409, Theorem 2.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  Studies in Advanced Mathematics 36, CUP (1995), §VI.5.
-/

public section

namespace TauCeti

open CategoryTheory MatlisDual

universe u v w

/-- **A coseparator is injective over its endomorphism ring.** Over an Artin algebra `A`, a
coseparator `M` of `mod A` is an injective module over `Module.End A M`. The modules may live in
any universe in which `A` is small. -/
theorem _root_.CategoryTheory.IsCoseparator.injective_end {A : Type v} [Ring A] [Small.{w} A]
    {M : FGModuleCat.{w} A} (hM : IsCoseparator M) (R : Type u) [CommRing R] [IsArtinianRing R]
    [Algebra R A] [Module.Finite R A] :
    Module.Injective (Module.End A M.obj) M.obj := by
  have := IsArtinianRing.of_finite R A
  -- Replace `R` by the centre `C` of `A`, which is small in the universe `w`, and take an injective
  -- hull `E` of `C ⧸ J(C)`.
  let C := Subalgebra.center R A
  have : Module.Finite C A := Subalgebra.finite_centerAlgebra_of_finite
  have : Small.{w} C := inferInstanceAs (Small.{w} {a : A // a ∈ C})
  obtain ⟨E, _, _, f, hf, -⟩ := exists_isInjectiveEnvelope_quotient_jacobson.{v, v} C
  have := hf.moduleInjective
  -- The dual `D_C A`, shrunk to the universe `w`, is a finitely generated injective module.
  have : Module.Finite Aᵐᵒᵖ A := .equiv (MulOpposite.opLinearEquiv Aᵐᵒᵖ).symm
  have : Module.Finite A (MatlisDual C E A) := hf.finite_matlisDual_of_finite_op
  have : Small.{w} (MatlisDual C E A) := Module.Finite.small A _
  let e := Shrink.linearEquiv.{w} A (MatlisDual C E A)
  have : Module.Finite A (Shrink.{w} (MatlisDual C E A)) := .equiv e.symm
  have : Module.Injective A (Shrink.{w} (MatlisDual C E A)) :=
    ((Module.Baer.of_injective inferInstance).of_equiv e.symm).injective
  let X := FGModuleCat.of A (Shrink.{w} (MatlisDual C E A))
  have : Injective X := FGModuleCat.injective_of_moduleInjective X
  -- As a finitely generated injective object, `X` lies in `add M`; so `D_C M` is projective as a
  -- right module over `End M` (a left module over its opposite).
  have := (FGModuleCat.finite_projective_end_op_matlisDual_of_additiveClosure (R := C) M
    (hM.additiveClosure_of_injective X) e).2
  exact moduleInjective_of_projective_op_matlisDual (MatlisDual.bijective_evalₗ
    hf.length_quotient_linearMap_eq_one (isFiniteLength_of_finite_trans C A M.obj))

section Converse

variable {C : Type u} [CommRing C] {E : Type v} [AddCommGroup E] [Module C E]
  [Module.Injective C E] [Small.{v} C] {Γ : Type*} [Ring Γ] [Algebra C Γ] [Small.{w} Γ]
  {Q : Type w} [AddCommGroup Q] [Module Γ Q] [Module C Q] [IsScalarTower C Γ Q]
  [Module.Injective Γ Q]

/-- An injective module of finite length over `C` is a retract of a finite power of `D Γ`: the maps
`Q → D Γ` given by the Hom-tensor adjunction separate the points of `Q`, so finitely many of them
embed the Artinian module `Q` into `(D Γ)ⁿ`, and the embedding splits. -/
private theorem exists_retract_pi_matlisDual
    (hE : ∀ 𝔪 : Ideal C, 𝔪.IsMaximal → Module.length C (C ⧸ 𝔪 →ₗ[C] E) = 1)
    (hQ : IsFiniteLength C Q) :
    ∃ (n : ℕ) (s : Q →ₗ[Γ] Fin n → MatlisDual C E Γ) (r : (Fin n → MatlisDual C E Γ) →ₗ[Γ] Q),
      r ∘ₗ s = LinearMap.id := by
  have hE' 𝔪 (h𝔪 : 𝔪.IsMaximal) : Nontrivial (C ⧸ 𝔪 →ₗ[C] E) :=
    (Module.length_eq_one_iff.1 (hE 𝔪 h𝔪)).nontrivial
  have : IsArtinian C Q := (isFiniteLength_iff_isNoetherian_isArtinian.1 hQ).2
  have : IsArtinian Γ Q := isArtinian_of_tower C inferInstance
  obtain ⟨n, s, hs⟩ := exists_injective_linearMap_pi_matlisDual (A := Γ)
    (MatlisDual.injective_evalₗ (N := Q) hE')
  obtain ⟨r, hr⟩ := Module.Injective.extension_property Γ Q _ _ s hs LinearMap.id
  exact ⟨n, s, r, hr⟩

/-- The dual `D B` of the endomorphism ring `B` of an injective module `Q` of finite length over
`C` embeds into a finite power `Qⁿ` as a left `B`-module. -/
private theorem exists_injective_matlisDual_end
    (hE : ∀ 𝔪 : Ideal C, 𝔪.IsMaximal → Module.length C (C ⧸ 𝔪 →ₗ[C] E) = 1)
    (hQ : IsFiniteLength C Q) :
    ∃ (n : ℕ) (σ : MatlisDual C E (Module.End Γ Q) →ₗ[Module.End Γ Q] Fin n → Q),
      Function.Injective σ := by
  obtain ⟨n, s, r, hrs⟩ := exists_retract_pi_matlisDual (Γ := Γ) hE hQ
  -- `τᵢ χ = ρᵢ ∘ adj χ` is right `B`-linear, by naturality of the adjunction.
  let τ (i : Fin n) : MatlisDual C E Q →ₗ[(Module.End Γ Q)ᵐᵒᵖ] Module.End Γ Q :=
    { toFun χ := r ∘ₗ LinearMap.single Γ _ i ∘ₗ equivLinearMapDualRegular χ
      map_add' _ _ := by simp [LinearMap.comp_add]
      map_smul' b χ := by
        rw [end_op_smul_eq_map, equivLinearMapDualRegular_map]
        rfl }
  refine ⟨n, LinearMap.pi fun i ↦
    (evalEquiv (A := Module.End Γ Q) hE hQ).symm.toLinearMap ∘ₗ mapOp (τ i),
    (injective_iff_map_eq_zero _).2 fun θ hθ ↦ ?_⟩
  have h0 (i : Fin n) (χ : MatlisDual C E Q) : equivLinearMap C E _ θ (τ i χ) = 0 := by
    have := congr_fun hθ i
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, Pi.zero_apply,
      LinearEquiv.map_eq_zero_iff] at this
    simpa using congr(equivLinearMap C E _ $this χ)
  -- Every `b ∈ B` is `∑ᵢ ρᵢ ∘ ψᵢ ∘ b`, a sum of values of the maps `τᵢ`.
  have hb (b : Module.End Γ Q) :
      b = ∑ i, τ i (map b (equivLinearMapDualRegular.symm (LinearMap.proj i ∘ₗ s))) := by
    ext x
    simp only [τ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply, LinearMap.comp_apply,
      equivLinearMapDualRegular_map, LinearEquiv.apply_symm_apply, LinearMap.coe_single,
      LinearMap.proj_apply]
    rw [← map_sum, Finset.univ_sum_single]
    exact (LinearMap.congr_fun hrs (b x)).symm
  ext b
  rw [hb b, map_sum]
  simp [h0]

/-- **An injective module is a cogenerator over its endomorphism ring.** Let `Q` be an injective
`Γ`-module of finite length over `C`, for a `C`-algebra `Γ` and the Matlis duality into an injective
`C`-module `E` such that each `Hom_C(C ⧸ 𝔪, E)` has length one. Then every nonzero element `y` of
every module `Y` over `B = Module.End Γ Q` is detected by a `B`-linear map `Y → Q`. -/
theorem exists_linearMap_end_apply_ne_zero_of_injective
    (hE : ∀ 𝔪 : Ideal C, 𝔪.IsMaximal → Module.length C (C ⧸ 𝔪 →ₗ[C] E) = 1)
    (hQ : IsFiniteLength C Q) {Y : Type*} [AddCommGroup Y] [Module (Module.End Γ Q) Y] {y : Y}
    (hy : y ≠ 0) : ∃ h : Y →ₗ[Module.End Γ Q] Q, h y ≠ 0 := by
  let : Module C Y := Module.compHom Y (algebraMap C (Module.End Γ Q))
  have : IsScalarTower C (Module.End Γ Q) Y := .of_algebraMap_smul fun _ _ ↦ rfl
  have hE' 𝔪 (h𝔪 : 𝔪.IsMaximal) : Nontrivial (C ⧸ 𝔪 →ₗ[C] E) :=
    (Module.length_eq_one_iff.1 (hE 𝔪 h𝔪)).nontrivial
  -- `D B` detects `y` by the adjunction for `B`, and `D B` embeds into `Qⁿ`.
  obtain ⟨n, σ, hσ⟩ := exists_injective_matlisDual_end (Γ := Γ) hE hQ
  obtain ⟨χ, hχ⟩ := exists_apply_ne_zero_of_forall_isMaximal hE' hy
  let g := equivLinearMapDualRegular (A := Module.End Γ Q) ((equivLinearMap C E Y).symm χ)
  have hg : g y ≠ 0 := fun h ↦ hχ (by simpa [g] using congr(equivLinearMap C E _ $h 1))
  obtain ⟨i, hi⟩ := Function.ne_iff.1 ((map_ne_zero_iff σ hσ).2 hg)
  exact ⟨LinearMap.proj i ∘ₗ σ ∘ₗ g, hi⟩

end Converse

/-- **A finitely generated injective module is a coseparator over its endomorphism ring.** Over an
Artin algebra `Γ`, a finitely generated injective module `Q` is a coseparator of `mod B` for
`B = Module.End Γ Q`. The finiteness of `Q` over `B`, which holds as `Q` is finite over `R`, is
needed to state this. The modules may live in any universe in which `Γ` is small. -/
theorem _root_.FGModuleCat.isCoseparator_end_of_injective (R : Type u) [CommRing R]
    [IsArtinianRing R] {Γ : Type v} [Ring Γ] [Algebra R Γ] [Module.Finite R Γ] [Small.{w} Γ]
    {Q : Type w} [AddCommGroup Q] [Module Γ Q] [Module.Finite Γ Q] [Module.Injective Γ Q]
    [Module.Finite (Module.End Γ Q) Q] :
    IsCoseparator (FGModuleCat.of (Module.End Γ Q) Q) := by
  let : Module R Q := Module.compHom Q (algebraMap R Γ)
  have : IsScalarTower R Γ Q := .of_algebraMap_smul fun _ _ ↦ rfl
  obtain ⟨E, _, _, f, hf, -⟩ := exists_isInjectiveEnvelope_quotient_jacobson.{u, u} R
  have := hf.moduleInjective
  exact (FGModuleCat.isCoseparator_iff _).2 fun X x hx ↦
    exists_linearMap_end_apply_ne_zero_of_injective hf.length_quotient_linearMap_eq_one
      (isFiniteLength_of_finite_trans R Γ Q) hx

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Injective.Bidual
public import TauCeti.Algebra.Module.Torsion.ResidueField
public import TauCeti.RingTheory.AdicCompletion.Noetherian
public import TauCeti.RingTheory.AdicCompletion.Torsion
public import TauCeti.RingTheory.Artinian.LocalRing
public import TauCeti.RingTheory.MatlisDuality.Endomorphism
public import TauCeti.RingTheory.MatlisDuality.FiniteLength

/-!
# Matlis duality for Artinian modules

Let `E` be an injective module containing the residue field of a commutative local ring `R`.
The annihilator of a submodule `N ≤ M` in `Hom_R(M, E)` is the kernel of restriction to `N`.
Annihilation reverses and reflects inclusion, since `E` separates points of `M/N`.
Consequently, if `Hom_R(M, E)` is Noetherian, then `M` is Artinian.

The same argument allows scalars on the dual to act through any semiring acting on `E` and
commuting with `R`. In particular, for an injective envelope `E` of the residue field of a
Noetherian local ring `R`, the `𝔪`-adic completion `R̂` acts canonically on `E`. Conversely, every
Artinian `R`-module embeds into a finite power `E^r`
(`TauCeti.exists_injective_linearMap_pi_of_isArtinian`), so injectivity of `E` presents
`Hom_R(M, E)` as a quotient of `Hom_R(E^r, E) ≅ R̂^r`. Thus `M` is Artinian over `R` if and only if
`Hom_R(M, E)` is finitely generated over `R̂`, with no torsion or completeness assumption on `M` or
`R`.

When `R` is complete for its maximal ideal, `Hom_R(M, E)` is finitely generated over `R` whenever
`M` is Artinian, and the canonical evaluation map `M → Hom_R(Hom_R(M, E), E)` is an isomorphism:
surjectivity on `E^r` follows from `End_R(E) ≅ R` (`TauCeti.IsInjectiveEnvelope.exists_eq_smul_id`)
and descends along `M ↪ E^r` via `LinearMap.surjective_applyₗ_of_injective`. No finiteness of the
residue field is required.

## Main declarations

* `TauCeti.matlisAnnihilatorOrderEmbedding`: annihilation embeds `Submodule R M` into the opposite
  lattice `(Submodule S (M →ₗ[R] E))ᵒᵈ`.
* `TauCeti.IsInjectiveEnvelope.finite_adicCompletion_linearMap_of_artinian` and
  `TauCeti.IsInjectiveEnvelope.isArtinian_iff_finite_adicCompletion_linearMap`: over a Noetherian
  local ring `R`, `M` is Artinian over `R` if and only if `Hom_R(M, E)` is finite over `R̂`.
* `TauCeti.IsInjectiveEnvelope.finite_linearMap_of_artinian` and
  `TauCeti.IsInjectiveEnvelope.bijective_applyₗ_of_artinian`: over a complete Noetherian local ring,
  the Matlis dual of an Artinian module is finite and evaluation into the double Matlis dual is
  bijective (`TauCeti.IsInjectiveEnvelope.evalEquivOfArtinian`).

## References

* [Stacks Project, Section 47.7](https://stacks.math.columbia.edu/tag/08Z1),
  [Proposition 47.7.8](https://stacks.math.columbia.edu/tag/08Z9), and
  [Remark 47.7.9](https://stacks.math.columbia.edu/tag/0EGL).
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Section 3.2.
-/

public section

noncomputable section

namespace TauCeti

open IsLocalRing LinearMap

universe u v w t

section General

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {E : Type v} [AddCommGroup E] [Module R E] [Small.{v} R]
  {ι : ResidueField R →ₗ[R] E}
  {M : Type w} [AddCommGroup M] [Module R M]
  (S : Type t) [Semiring S] [Module S E] [SMulCommClass R S E]

/-- Restriction kernels in the Matlis dual reverse and reflect inclusion of submodules.
It suffices that the injective target contain the residue field; essentiality is not needed. -/
theorem ker_lcomp_subtype_le_iff_of_injective [Module.Injective R E]
    (hι : Function.Injective ι) (N P : Submodule R M) :
    ker (N.subtype.lcomp S E) ≤ ker (P.subtype.lcomp S E) ↔ P ≤ N := by
  constructor
  · intro h x hx
    have hz : (LinearMap.applyₗ : (M ⧸ N) →ₗ[R] ((M ⧸ N) →ₗ[R] E) →ₗ[R] E)
        (N.mkQ x) = 0 := by
      ext f
      have hf : f.comp N.mkQ ∈ ker (N.subtype.lcomp S E) := by
        simp only [LinearMap.mem_ker, lcomp_apply']
        ext y
        simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.subtype_apply,
          (Submodule.Quotient.mk_eq_zero N).mpr y.property, map_zero, LinearMap.zero_apply]
      have hp := LinearMap.congr_fun (h hf) ⟨x, hx⟩
      simpa using hp
    have := injective_applyₗ_of_injective (M := M ⧸ N) hι
    exact (Submodule.Quotient.mk_eq_zero N).mp (this (hz.trans (map_zero _).symm))
  · intro h f hf
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun hf ⟨x, h x.property⟩

/-- Annihilation embeds the submodule lattice into the opposite lattice of submodules of the
Matlis dual. The dual scalars act on the target `E` and need only commute with `R`. -/
def matlisAnnihilatorOrderEmbedding [Module.Injective R E] (hι : Function.Injective ι) :
    Submodule R M ↪o (Submodule S (M →ₗ[R] E))ᵒᵈ :=
  OrderEmbedding.ofMapLEIff (fun N ↦ OrderDual.toDual (ker (N.subtype.lcomp S E)))
    (fun _ _ ↦ ker_lcomp_subtype_le_iff_of_injective S hι _ _)

/-- The annihilator embedding assigns to `N` the maps vanishing on `N`. -/
@[simp]
theorem matlisAnnihilatorOrderEmbedding_apply [Module.Injective R E]
    (hι : Function.Injective ι) (N : Submodule R M) :
    matlisAnnihilatorOrderEmbedding S hι N =
      OrderDual.toDual (ker (N.subtype.lcomp S E)) :=
  (rfl)

/-- A module is Artinian if its dual into an injective module containing the residue field
is Noetherian, even for a commuting scalar action on the dual. -/
theorem isArtinian_of_isNoetherian_linearMap [Module.Injective R E]
    (hι : Function.Injective ι) [IsNoetherian S (M →ₗ[R] E)] : IsArtinian R M :=
  (matlisAnnihilatorOrderEmbedding (M := M) S hι).wellFoundedLT

/-- A module is Noetherian if its dual into an injective module containing the residue field is
Artinian, even for a commuting scalar action on the dual. -/
theorem isNoetherian_of_isArtinian_linearMap [Module.Injective R E]
    (hι : Function.Injective ι) [IsArtinian S (M →ₗ[R] E)] : IsNoetherian R M := by
  rw [isNoetherian_iff]
  exact (matlisAnnihilatorOrderEmbedding (M := M) S hι).dual.wellFounded ‹_›

end General

namespace IsInjectiveEnvelope

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {E : Type v} [AddCommGroup E] [Module R E] [Small.{v} R]
  {ι : ResidueField R →ₗ[R] E} (hι : IsInjectiveEnvelope ι)

include hι

/-- A module whose Matlis dual is finite over the completion of a Noetherian local ring is
Artinian. The completion acts on the injective hull through its canonical torsion-module action.
Neither the original ring nor the original module is required to be complete. -/
theorem isArtinian_of_finite_adicCompletion_linearMap {M : Type w} [AddCommGroup M] [Module R M]
    (hfinite : letI := AdicCompletion.torsionModule (fun _ : E ↦
        hι.isEssential_range.primaryComponent_maximalIdeal_eq_top.ge Submodule.mem_top)
      Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) (M →ₗ[R] E)) :
    IsArtinian R M := by
  let := AdicCompletion.torsionModule (fun _ : E ↦
    hι.isEssential_range.primaryComponent_maximalIdeal_eq_top.ge Submodule.mem_top)
  have := hfinite
  have : IsScalarTower R (_root_.AdicCompletion (maximalIdeal R) R) E :=
    AdicCompletion.torsionModule_isScalarTower _
  have := hι.moduleInjective
  exact isArtinian_of_isNoetherian_linearMap
    (_root_.AdicCompletion (maximalIdeal R) R) hι.injective

/-- Over a Noetherian local ring, the Matlis dual of an Artinian module is finitely generated over
the `𝔪`-adic completion, acting via `TauCeti.AdicCompletion.torsionModule`. Neither completeness of
`R` nor finiteness of the residue field is required. -/
@[stacks 0EGL]
theorem finite_adicCompletion_linearMap_of_artinian (M : Type w) [AddCommGroup M] [Module R M]
    [IsArtinian R M] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) (M →ₗ[R] E) := by
  let A := _root_.AdicCompletion (maximalIdeal R) R
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  have := hι.moduleInjective
  obtain ⟨r, j, hj⟩ := exists_injective_linearMap_pi_of_isArtinian (M := M) hι.injective
  -- Every functional on `E^r` is an `A`-linear combination of coordinate projections.
  let Φ : (Fin r → A) →ₗ[A] ((Fin r → E) →ₗ[R] E) :=
    { toFun s := ∑ i, s i • proj i
      map_add' s₁ s₂ := by simp [add_smul, Finset.sum_add_distrib]
      map_smul' a s := by simp [mul_smul, Finset.smul_sum] }
  have hΦ_apply (s : Fin r → A) : Φ s = ∑ i, s i • proj i := rfl
  have hΦ : Function.Surjective Φ := by
    intro f
    refine ⟨fun i ↦ hι.adicCompletionEquivEnd.symm (f ∘ₗ single R (fun _ : Fin r ↦ E) i), ?_⟩
    apply LinearMap.ext
    intro x
    conv_rhs => rw [← Finset.univ_sum_single x, map_sum]
    rw [hΦ_apply, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [LinearMap.smul_apply, proj_apply, ← hι.adicCompletionEquivEnd_apply hι.mem_primaryComponent,
      AlgEquiv.apply_symm_apply, comp_apply]
    rfl
  have hj_surj : Function.Surjective (j.lcomp A E) := fun g ↦ by
    obtain ⟨g', hg'⟩ := Module.Injective.extension_property R E M (Fin r → E) j hj g
    exact ⟨g', hg'⟩
  exact Module.Finite.of_surjective ((j.lcomp A E) ∘ₗ Φ) (hj_surj.comp hΦ)

/-- Over a Noetherian local ring, an `R`-module is Artinian if and only if its Matlis dual is
finitely generated over the `𝔪`-adic completion. -/
theorem isArtinian_iff_finite_adicCompletion_linearMap (M : Type w) [AddCommGroup M] [Module R M] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    IsArtinian R M ↔ Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) (M →ₗ[R] E) :=
  ⟨fun _ ↦ hι.finite_adicCompletion_linearMap_of_artinian M,
    hι.isArtinian_of_finite_adicCompletion_linearMap⟩

section Complete

variable [IsAdicComplete (maximalIdeal R) R]

/-- Over a complete Noetherian local ring, the Matlis dual of an Artinian module is finitely
generated. -/
@[stacks 08Z9]
theorem finite_linearMap_of_artinian (M : Type w) [AddCommGroup M] [Module R M] [IsArtinian R M] :
    Module.Finite R (M →ₗ[R] E) := by
  let A := _root_.AdicCompletion (maximalIdeal R) R
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  have : Module.Finite R A := .of_surjective (Algebra.ofId R A).toLinearMap
    (_root_.AdicCompletion.of_bijective (maximalIdeal R) R).surjective
  have : Module.Finite A (M →ₗ[R] E) := hι.finite_adicCompletion_linearMap_of_artinian M
  exact Module.Finite.trans A (M →ₗ[R] E)

/-- Over a complete Noetherian local ring, a module is Artinian if and only if its Matlis dual is
finitely generated. -/
theorem isArtinian_iff_finite_linearMap (M : Type w) [AddCommGroup M] [Module R M] :
    IsArtinian R M ↔ Module.Finite R (M →ₗ[R] E) := by
  refine ⟨fun _ ↦ hι.finite_linearMap_of_artinian M, fun _ ↦ ?_⟩
  have := hι.moduleInjective
  exact isArtinian_of_isNoetherian_linearMap R hι.injective

variable (M : Type w) [AddCommGroup M] [Module R M] [IsArtinian R M]

/-- Matlis biduality for Artinian modules over a complete Noetherian local ring: the canonical
evaluation map into the double Matlis dual is bijective. -/
@[stacks 08Z9]
theorem bijective_applyₗ_of_artinian :
    Function.Bijective (applyₗ : M →ₗ[R] (M →ₗ[R] E) →ₗ[R] E) := by
  have := hι.moduleInjective
  obtain ⟨r, j, hj⟩ := exists_injective_linearMap_pi_of_isArtinian (M := M) hι.injective
  exact ⟨injective_applyₗ_of_injective hι.injective,
    j.surjective_applyₗ_of_injective hj (injective_applyₗ_of_injective hι.injective)
      (surjective_applyₗ_pi_self_of_end_eq_smul hι.exists_eq_smul_id (Fin r))⟩

/-- Evaluation identifies an Artinian module over a complete Noetherian local ring with its double
Matlis dual. -/
def evalEquivOfArtinian : M ≃ₗ[R] ((M →ₗ[R] E) →ₗ[R] E) :=
  LinearEquiv.ofBijective applyₗ (hι.bijective_applyₗ_of_artinian M)

@[simp]
theorem evalEquivOfArtinian_apply_apply (m : M) (f : M →ₗ[R] E) :
    hι.evalEquivOfArtinian M m f = f m :=
  (rfl)

@[simp]
theorem evalEquivOfArtinian_symm_apply_apply (φ : (M →ₗ[R] E) →ₗ[R] E) (f : M →ₗ[R] E) :
    f ((hι.evalEquivOfArtinian M).symm φ) = φ f := by
  simpa only [evalEquivOfArtinian_apply_apply] using
    congrArg (fun ψ : (M →ₗ[R] E) →ₗ[R] E ↦ ψ f)
      ((hι.evalEquivOfArtinian M).apply_symm_apply φ)

end Complete

end IsInjectiveEnvelope

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MatlisDuality.FiniteLength
public import TauCeti.Algebra.Module.Torsion.ResidueField
public import TauCeti.RingTheory.AdicCompletion.Torsion
public import TauCeti.RingTheory.AdicCompletion.Noetherian
import TauCeti.RingTheory.Artinian.LocalRing
public import TauCeti.RingTheory.MatlisDuality.Endomorphism

/-!
# Artinian modules and their Matlis duals

Let `E` be an injective module containing the residue field of a commutative local ring `R`.
The annihilator of a submodule `N ≤ M` in `Hom_R(M, E)` is the kernel of restriction to `N`.
Annihilation reverses and reflects inclusion, since `E` separates points of `M/N`.
Consequently, if `Hom_R(M, E)` is Noetherian, then `M` is Artinian.

The same argument allows scalars on the dual to act through any semiring acting on `E` and
commuting with `R`. In particular, for the injective hull of the residue field of a Noetherian
local ring, use its canonical action by the completion `R̂`. A Matlis dual finite over `R̂`
therefore detects Artinianness of the original module. Conversely, every Artinian module embeds into
a finite power `Fin n → E` (`TauCeti.exists_injective_linearMap_fin_of_isArtinian`), so dualizing
against `End_R(E) ≃ R̂` shows that `Hom_R(M, E)` is a finite `R̂`-module for every Artinian
`R`-module `M`. Neither completeness of `R` nor finiteness of its residue field is required. When
`R` is complete, `M` is Artinian iff `Hom_R(M, E)` is finitely generated over `R`.

## Main results

* `TauCeti.isArtinian_of_isNoetherian_linearMap`: if `Hom_R(M, E)` is Noetherian over a commuting
  scalar semiring `S`, then `M` is Artinian.
* `TauCeti.IsInjectiveEnvelope.isArtinian_of_finite_adicCompletion_linearMap`: a module whose Matlis
  dual is finite over `R̂` is Artinian.
* `TauCeti.IsInjectiveEnvelope.finite_adicCompletion_linearMap_of_isArtinian` and
  `TauCeti.IsInjectiveEnvelope.isArtinian_iff_finite_adicCompletion_linearMap`: an `R`-module is
  Artinian iff its Matlis dual is finite over `R̂`.
* `TauCeti.IsInjectiveEnvelope.finite_linearMap_of_isArtinian` and
  `TauCeti.IsInjectiveEnvelope.isArtinian_iff_finite_linearMap`: over a complete Noetherian local
  ring, an `R`-module is Artinian iff its Matlis dual is finitely generated over `R`.

## References

* The Stacks Project, Section 47.7, Matlis duality, Tag 08Z1, Proposition 47.7.8 (Tag 08Z9), and
  Remark 47.7.9 (Tag 0EGL).
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Section 3.2.
-/

public section

noncomputable section

namespace TauCeti

open IsLocalRing LinearMap

universe u v w t

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

variable [IsNoetherianRing R]

namespace IsInjectiveEnvelope

/-- A module whose Matlis dual is finite over the completion of a Noetherian local ring is
Artinian. The completion acts on the injective hull through its canonical torsion-module action.
Neither the original ring nor the original module is required to be complete. -/
theorem isArtinian_of_finite_adicCompletion_linearMap
    (hι : IsInjectiveEnvelope ι)
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

/-- The Matlis dual of an Artinian module over a Noetherian local ring is finitely generated over
the completion `R̂`. Completeness of `R` is not needed. -/
theorem finite_adicCompletion_linearMap_of_isArtinian (hι : IsInjectiveEnvelope ι)
    (M : Type w) [AddCommGroup M] [Module R M] [IsArtinian R M] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) (M →ₗ[R] E) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := hι.moduleInjective
  obtain ⟨n, f, hf⟩ := exists_injective_linearMap_fin_of_isArtinian hι.injective M
  -- Precomposition with `f : M ↪ Eⁿ` surjects `Hom_R(Eⁿ, E) ≃ End_R(E)ⁿ ≃ R̂ⁿ` onto `Hom_R(M, E)`.
  have hsurj : Function.Surjective (f.lcomp (_root_.AdicCompletion (maximalIdeal R) R) E) :=
    fun g ↦ Module.Injective.extension_property R E M (Fin n → E) f hf g
  let e : (Fin n → _root_.AdicCompletion (maximalIdeal R) R) ≃ₗ[_root_.AdicCompletion
      (maximalIdeal R) R] ((Fin n → E) →ₗ[R] E) :=
    (LinearEquiv.piCongrRight fun _ ↦ hι.adicCompletionLinearEquivEnd).trans
      (LinearMap.lsum R (fun _ : Fin n ↦ E) (_root_.AdicCompletion (maximalIdeal R) R))
  exact Module.Finite.of_surjective ((f.lcomp _ E).comp e.toLinearMap)
    (hsurj.comp e.surjective)

/-- Over a Noetherian local ring, a module is Artinian iff its Matlis dual is finitely generated
over the completion `R̂`. -/
theorem isArtinian_iff_finite_adicCompletion_linearMap (hι : IsInjectiveEnvelope ι)
    (M : Type w) [AddCommGroup M] [Module R M] :
    IsArtinian R M ↔
      letI := AdicCompletion.torsionModule hι.mem_primaryComponent
      Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) (M →ₗ[R] E) :=
  ⟨fun _ ↦ hι.finite_adicCompletion_linearMap_of_isArtinian M,
    hι.isArtinian_of_finite_adicCompletion_linearMap⟩

section Complete

variable [IsAdicComplete (maximalIdeal R) R]

/-- The Matlis dual of an Artinian module over a complete Noetherian local ring is finitely
generated over `R`. -/
theorem finite_linearMap_of_isArtinian (hι : IsInjectiveEnvelope ι)
    (M : Type w) [AddCommGroup M] [Module R M] [IsArtinian R M] :
    Module.Finite R (M →ₗ[R] E) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have : Module.Finite R (_root_.AdicCompletion (maximalIdeal R) R) :=
    Module.Finite.equiv (_root_.AdicCompletion.ofLinearEquiv (maximalIdeal R) R)
  have : Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) (M →ₗ[R] E) :=
    hι.finite_adicCompletion_linearMap_of_isArtinian M
  exact Module.Finite.trans (_root_.AdicCompletion (maximalIdeal R) R) (M →ₗ[R] E)

/-- Over a complete Noetherian local ring, a module is Artinian iff its Matlis dual is finitely
generated over `R`. -/
theorem isArtinian_iff_finite_linearMap (hι : IsInjectiveEnvelope ι)
    (M : Type w) [AddCommGroup M] [Module R M] :
    IsArtinian R M ↔ Module.Finite R (M →ₗ[R] E) := by
  refine ⟨fun _ ↦ hι.finite_linearMap_of_isArtinian M, fun _ ↦ ?_⟩
  have := hι.moduleInjective
  exact isArtinian_of_isNoetherian_linearMap R hι.injective

end Complete

end IsInjectiveEnvelope

end TauCeti

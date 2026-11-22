/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MatlisDuality.Endomorphism
public import TauCeti.RingTheory.AdicCompletion.Noetherian
public import TauCeti.RingTheory.Artinian.Module

/-!
# Artinian modules and their Matlis duals

Let `E` be an injective module containing the residue field of a commutative local ring `R`.
The annihilator embedding (`TauCeti.matlisAnnihilatorOrderEmbedding`, in
`TauCeti/Algebra/Module/Injective/Cogenerator/LocalRing.lean`) implies that if `Hom_R(M, E)` is
Noetherian over any semiring of scalars acting on `E` and commuting with `R`, then `M` is
Artinian. In particular, for the injective hull of the residue field of a Noetherian local ring, a
Matlis dual finite over the completion detects Artinianness of the original module, with no
torsion or completeness assumptions on `M` or `R`.

Conversely, an Artinian module embeds into a finite power of `E`
(`IsArtinian.exists_injective_linearMap_pi`), so its dual is a quotient of a finite power of
`End_R(E)`. Hence the dual is finite over every semiring of scalars over which `End_R(E)` is
finite; for the injective hull this is the completion, which acts on `End_R(E)` as a cyclic
module. So a module over a Noetherian local ring is Artinian exactly when its Matlis dual is
finite over the completion.

## Main results

* `TauCeti.finite_linearMap_of_isArtinian`: the dual of an Artinian module is finite over any
  scalars over which `End_R(E)` is finite.
* `TauCeti.IsInjectiveEnvelope.isArtinian_iff_finite_adicCompletion_linearMap`: for the injective
  hull of the residue field of a Noetherian local ring, a module is Artinian exactly when its dual
  is finite over the completion.

## References

* The Stacks Project, Section 47.7, Matlis duality, Tag 08Z1 and Remark 47.7.9.
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

/-- **The Matlis dual of an Artinian module is finite.** Let `E` be an injective module containing
the residue field and `S` a semiring acting on `E`, commuting with `R`, over which the
endomorphisms of `E` form a finite module. Then the dual of every Artinian module is finite over
`S`. -/
theorem finite_linearMap_of_isArtinian [Module.Injective R E] (hι : Function.Injective ι)
    [IsArtinian R M] [Module.Finite S (Module.End R E)] : Module.Finite S (M →ₗ[R] E) := by
  -- `E` separates the points of `M`, so `M` embeds into some `Eⁿ`.
  obtain ⟨n, g, hg⟩ := IsArtinian.exists_injective_linearMap_pi (R := R) (M := M) (E := E)
    fun _ hm ↦ exists_apply_ne_zero_of_injective hι hm
  -- Restriction along `g` maps `Hom_R(Eⁿ, E) ≅ End_R(E)ⁿ` onto the dual, by injectivity of `E`.
  refine Module.Finite.of_surjective
    (g.lcomp S E ∘ₗ (LinearMap.lsum R (fun _ : Fin n ↦ E) S).toLinearMap) fun f ↦ ?_
  obtain ⟨h, rfl⟩ := Module.Injective.extension_property R E M (Fin n → E) g hg f
  exact ⟨(LinearMap.lsum R (fun _ : Fin n ↦ E) S).symm h, by simp [lcomp_apply']⟩

variable [IsNoetherianRing R]

/-- A module whose Matlis dual is finite over the completion of a Noetherian local ring is
Artinian. The completion acts on the injective hull through its canonical torsion-module action.
Neither the original ring nor the original module is required to be complete. -/
theorem IsInjectiveEnvelope.isArtinian_of_finite_adicCompletion_linearMap
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

/-- **The Matlis dual of an Artinian module is finite over the completion.** For an injective hull
`E` of the residue field of a Noetherian local ring, the dual of every Artinian module is finite
over the completion, which acts on `E` through its canonical torsion-module action. The ring need
not be complete. -/
theorem IsInjectiveEnvelope.finite_adicCompletion_linearMap_of_isArtinian
    (hι : IsInjectiveEnvelope ι) [IsArtinian R M] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) (M →ₗ[R] E) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := hι.finite_adicCompletion_end
  have := hι.moduleInjective
  exact finite_linearMap_of_isArtinian _ hι.injective

/-- **Artinian modules are those with Matlis dual finite over the completion.** For an injective
hull `E` of the residue field of a Noetherian local ring, a module is Artinian exactly when its
dual is finite over the completion. -/
theorem IsInjectiveEnvelope.isArtinian_iff_finite_adicCompletion_linearMap
    (hι : IsInjectiveEnvelope ι) :
    IsArtinian R M ↔ letI := AdicCompletion.torsionModule hι.mem_primaryComponent
      Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) (M →ₗ[R] E) :=
  ⟨fun _ ↦ hι.finite_adicCompletion_linearMap_of_isArtinian,
    hι.isArtinian_of_finite_adicCompletion_linearMap⟩

end TauCeti

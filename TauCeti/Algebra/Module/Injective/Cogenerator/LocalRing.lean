/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Injective.Cogenerator
public import TauCeti.RingTheory.LocalRing.ResidueField.Quotient

/-!
# Injective cogenerators over a commutative local ring

Let `R` be a commutative local ring with residue field `κ`, and let `E` be an injective `R`-module
containing a copy of `κ` via an injective linear map `ι : κ →ₗ[R] E`. Because `R` has a unique
maximal ideal `𝔪` and `R ⧸ 𝔪 ≅ κ`, `E` receives a nonzero map from `R ⧸ 𝔪` for every maximal ideal
`𝔪` and therefore satisfies the cogenerator criteria of
`TauCeti/Algebra/Module/Injective/Cogenerator.lean`, without assuming finite length or an
injective envelope.

## Main results

* `TauCeti.injective_applyₗ_of_injective`: the evaluation map `M → Hom_R(Hom_R(M, E), E)` is
  injective for every module `M`, so `E` is a cogenerator.
* `TauCeti.ker_lcomp_subtype_le_iff_of_injective`, `TauCeti.matlisAnnihilatorOrderEmbedding`,
  `TauCeti.isArtinian_of_isNoetherian_linearMap`, and
  `TauCeti.isNoetherian_of_isArtinian_linearMap`: annihilation embeds the submodule lattice into
  the opposite submodule lattice of the `E`-dual over any commuting scalar semiring, transferring
  chain conditions contravariantly.
* `TauCeti.annihilator_torsionBySet_of_injective`: the annihilator of `E[J]` is `J` for every
  ideal `J`.

## References

* The Stacks Project, Section 47.7, Matlis duality, Tag 08Z1.
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Section 3.2.
-/

public section

noncomputable section

namespace TauCeti

open IsLocalRing LinearMap

universe u v w

variable {R : Type u} [CommRing R] [IsLocalRing R] {E : Type v} [AddCommGroup E] [Module R E]
  {ι : ResidueField R →ₗ[R] E}

private theorem nontrivial_quotient_linearMap_of_injective (hι : Function.Injective ι)
    (𝔪 : Ideal R) (h𝔪 : 𝔪.IsMaximal) : Nontrivial (R ⧸ 𝔪 →ₗ[R] E) :=
  ⟨ι ∘ₗ (quotientEquivResidueField h𝔪).toLinearMap, 0, fun h => one_ne_zero <| hι <| by
    simpa using LinearMap.congr_fun h ((quotientEquivResidueField h𝔪).symm 1)⟩

variable [Small.{v} R]

/-- If `E` is injective and contains a copy of the residue field, then `E` is a cogenerator: the
evaluation map `M → Hom_R(Hom_R(M, E), E)` is injective for every module `M`. -/
theorem injective_applyₗ_of_injective [Module.Injective R E] (hι : Function.Injective ι)
    {M : Type w} [AddCommGroup M] [Module R M] :
    Function.Injective (LinearMap.applyₗ : M →ₗ[R] (M →ₗ[R] E) →ₗ[R] E) :=
  injective_applyₗ_of_forall_isMaximal (nontrivial_quotient_linearMap_of_injective hι)

/-- Restriction kernels in the Matlis dual reverse and reflect inclusion of submodules.
It suffices that the injective target contain the residue field; essentiality is not needed. -/
theorem ker_lcomp_subtype_le_iff_of_injective
    (S : Type*) [Semiring S] [Module S E] [SMulCommClass R S E] [Module.Injective R E]
    (hι : Function.Injective ι) {M : Type w} [AddCommGroup M] [Module R M]
    (N P : Submodule R M) :
    LinearMap.ker (N.subtype.lcomp S E) ≤ LinearMap.ker (P.subtype.lcomp S E) ↔ P ≤ N :=
  ker_lcomp_subtype_le_iff_of_forall_isMaximal
    (nontrivial_quotient_linearMap_of_injective hι) S N P

/-- Annihilation embeds the submodule lattice into the opposite lattice of submodules of the
Matlis dual. The dual scalars act on the target `E` and need only commute with `R`. -/
def matlisAnnihilatorOrderEmbedding
    (S : Type*) [Semiring S] [Module S E] [SMulCommClass R S E] [Module.Injective R E]
    (hι : Function.Injective ι) {M : Type w} [AddCommGroup M] [Module R M] :
    Submodule R M ↪o (Submodule S (M →ₗ[R] E))ᵒᵈ :=
  annihilatorOrderEmbedding (nontrivial_quotient_linearMap_of_injective hι) S

/-- The annihilator embedding assigns to `N` the maps vanishing on `N`. -/
@[simp]
theorem matlisAnnihilatorOrderEmbedding_apply
    (S : Type*) [Semiring S] [Module S E] [SMulCommClass R S E] [Module.Injective R E]
    (hι : Function.Injective ι) {M : Type w} [AddCommGroup M] [Module R M]
    (N : Submodule R M) :
    matlisAnnihilatorOrderEmbedding S hι N =
      OrderDual.toDual (LinearMap.ker (N.subtype.lcomp S E)) :=
  annihilatorOrderEmbedding_apply _ S N

/-- A module is Artinian if its dual into an injective module containing the residue field
is Noetherian, even for a commuting scalar action on the dual. -/
theorem isArtinian_of_isNoetherian_linearMap
    (S : Type*) [Semiring S] [Module S E] [SMulCommClass R S E] [Module.Injective R E]
    (hι : Function.Injective ι) {M : Type w} [AddCommGroup M] [Module R M]
    [IsNoetherian S (M →ₗ[R] E)] : IsArtinian R M :=
  isArtinian_of_isNoetherian_linearMap_of_forall_isMaximal
    (nontrivial_quotient_linearMap_of_injective hι) S

/-- A module is Noetherian if its dual into an injective module containing the residue field is
Artinian, even for a commuting scalar action on the dual. -/
theorem isNoetherian_of_isArtinian_linearMap
    (S : Type*) [Semiring S] [Module S E] [SMulCommClass R S E] [Module.Injective R E]
    (hι : Function.Injective ι) {M : Type w} [AddCommGroup M] [Module R M]
    [IsArtinian S (M →ₗ[R] E)] : IsNoetherian R M :=
  isNoetherian_of_isArtinian_linearMap_of_forall_isMaximal
    (nontrivial_quotient_linearMap_of_injective hι) S

/-- If `E` is injective and contains a copy of the residue field, then the elements of `E`
killed by an ideal `J` have annihilator exactly `J`. -/
theorem annihilator_torsionBySet_of_injective [Module.Injective R E]
    (hι : Function.Injective ι) (J : Ideal R) : (Submodule.torsionBySet R E J).annihilator = J := by
  refine le_antisymm (fun r hr => ?_) fun r hr => Submodule.mem_annihilator.mpr fun x hx =>
    (Submodule.mem_torsionBySet_iff _ _).mp hx ⟨r, hr⟩
  -- `E` cogenerates `R ⧸ J`, so the class of `r` is detected by a map `R ⧸ J → E`; that map
  -- sends `1` into `E[J]`, which `r` kills.
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine (injective_iff_map_eq_zero _).mp
    (injective_applyₗ_of_injective (M := R ⧸ J) hι) _ (LinearMap.ext fun f => ?_)
  simpa [f.apply_quotient_mk_eq_smul_apply_one] using
    Submodule.mem_annihilator.mp hr _ (J.quotientLinearMapEquivTorsionBySet E f).prop

end TauCeti

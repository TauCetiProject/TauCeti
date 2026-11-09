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

/-!
# Artinian modules detected by their Matlis duals

Let `E` be an injective module containing the residue field of a commutative local ring `R`.
The annihilator of a submodule `N ≤ M` in `Hom_R(M, E)` is the kernel of restriction to `N`.
Annihilation reverses and reflects inclusion, since `E` separates points of `M/N`.
Consequently, if `Hom_R(M, E)` is Noetherian, then `M` is Artinian.

The same argument allows scalars on the dual to act through any semiring acting on `E` and
commuting with `R`. In particular, for the injective hull of the residue field of a Noetherian
local ring, use its canonical action by the completion. A Matlis dual finite over the completion
therefore detects Artinianness of the original module. The module need not be assumed to be
maximal-ideal-power torsion; the criterion implies Artinianness even without that assumption.
No completeness of `R` or finiteness of its residue field is required.

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

end TauCeti

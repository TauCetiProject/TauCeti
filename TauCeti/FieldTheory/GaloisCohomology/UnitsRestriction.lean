/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Cyclic
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.CyclicRestriction

/-!
# Restriction of cyclic relative Brauer classes

For a tower of fields `K ⊆ E ⊆ L`, the actions of `Gal(L/E)` and `Gal(L/K)` on `Lˣ`
agree along the inclusion of Galois groups. The identity on units is therefore an equivariant
coefficient map for restriction of relative Galois cohomology. In degree two this is the
restriction map on relative Brauer groups. If the generators are related by the degree of the
ground-field extension, `TauCeti.restrict_cyclicClass` proves that restriction preserves the
unit representing a cyclic class. The proof uses the carry-cocycle description of
`TauCeti.H2π_eq_cyclicClass` and `TauCeti.map_groupCohomologyπEven_two_of_pow`.

## References

* J.-P. Serre, *Local Fields*, Chapter X, §1 and Chapter XIII, §3.
-/

public noncomputable section

namespace TauCeti

universe u

section Coefficients

variable (K E L : Type u) [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]

/-- The identity on `Lˣ` as an equivariant coefficient map along
`Gal(L/E) → Gal(L/K)`. -/
def unitsRestrictionHom :
    Rep.res (AlgEquiv.restrictScalarsHom K : (L ≃ₐ[E] L) →* (L ≃ₐ[K] L))
        (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) ⟶
      Rep.ofMulDistribMulAction (L ≃ₐ[E] L) Lˣ :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    LinearMap.id fun _ _ ↦ rfl

/-- Restricting the units representation leaves the underlying unit unchanged. -/
@[simp]
theorem unitsRestrictionHom_apply (a : Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) :
    (unitsRestrictionHom K E L).hom a = a := by
  rfl

end Coefficients

open CategoryTheory Rep.FiniteCyclicGroup groupCohomology

attribute [local instance] IsCyclic.commGroup

variable {K E L : Type} [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
  [FiniteDimensional K L] [FiniteDimensional E L] [IsGalois K L] [IsGalois E L]
  {g : L ≃ₐ[K] L} {gE : L ≃ₐ[E] L}

/-- Restriction from `Gal(L/K)` to `Gal(L/E)` preserves the cyclic class of `a`, when the
chosen generator of `Gal(L/E)` is the `[E : K]`-th power of that of `Gal(L/K)`. -/
theorem restrict_cyclicClass (hg : ∀ σ, σ ∈ Subgroup.zpowers g)
    (hgE : ∀ σ, σ ∈ Subgroup.zpowers gE)
    (hgg : AlgEquiv.restrictScalarsHom K gE = g ^ Module.finrank K E) (a : Kˣ) :
    groupCohomology.map (AlgEquiv.restrictScalarsHom K) (unitsRestrictionHom K E L) 2
        (cyclicClass hg (Additive.ofMul a)) =
      cyclicClass hgE (Additive.ofMul (Units.map (algebraMap K E : K →* E) a)) := by
  have : IsCyclic (L ≃ₐ[K] L) := ⟨g, fun σ ↦ Subgroup.mem_zpowers_iff.1 (hg σ)⟩
  have : IsCyclic (L ≃ₐ[E] L) := ⟨gE, fun σ ↦ Subgroup.mem_zpowers_iff.1 (hgE σ)⟩
  -- Use the coefficient of the carry cocycle directly; its class is characterized by
  -- `H2π_eq_cyclicClass`, independently of the implementation of `cyclicClass`.
  let y : LinearMap.ker
      (Rep.applyAsHom (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) g - 𝟙 _).hom.toLinearMap :=
    ⟨Rep.toAdditive.symm (Additive.ofMul (Units.map (algebraMap K L : K →* L) a)), by
      rw [LinearMap.mem_ker]
      simp only [Rep.sub_hom, Representation.IntertwiningMap.sub_toLinearMap,
        LinearMap.sub_apply, sub_eq_zero]
      exact Additive.toMul.injective (Units.ext (AlgEquiv.commutes g (a : K)))⟩
  let z : LinearMap.ker
      (Rep.applyAsHom (Rep.ofMulDistribMulAction (L ≃ₐ[E] L) Lˣ) gE - 𝟙 _).hom.toLinearMap :=
    ⟨Rep.toAdditive.symm (Additive.ofMul (Units.map (algebraMap E L : E →* L)
        (Units.map (algebraMap K E : K →* E) a))), by
      rw [LinearMap.mem_ker]
      simp only [Rep.sub_hom, Representation.IntertwiningMap.sub_toLinearMap,
        LinearMap.sub_apply, sub_eq_zero]
      exact Additive.toMul.injective (Units.ext (AlgEquiv.commutes gE (algebraMap K E (a : K))))⟩
  have hy : groupCohomologyπEven _ g hg 2 even_two y =
      cyclicClass hg (Additive.ofMul a) := by
    rw [groupCohomologyπEven_two_apply]
    apply H2π_eq_cyclicClass hg
    intro i j hi hj
    rw [carryCocycle_apply_pow _ g hg y hi hj]
    split_ifs <;> rfl
  have hz : groupCohomologyπEven _ gE hgE 2 even_two z =
      cyclicClass hgE (Additive.ofMul (Units.map (algebraMap K E : K →* E) a)) := by
    rw [groupCohomologyπEven_two_apply]
    apply H2π_eq_cyclicClass hgE
    intro i j hi hj
    rw [carryCocycle_apply_pow _ gE hgE z hi hj]
    split_ifs <;> rfl
  rw [← hy, ← hz]
  exact map_groupCohomologyπEven_two_of_pow _ _ hgE _ hg _ hgg
    (by rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
      Module.finrank_mul_finrank K E L]) (unitsRestrictionHom K E L) y z (by
        rw [unitsRestrictionHom_apply]
        apply Rep.toAdditive.injective
        apply Additive.toMul.injective
        apply Units.ext
        exact (IsScalarTower.algebraMap_apply K E L _).symm)

end TauCeti

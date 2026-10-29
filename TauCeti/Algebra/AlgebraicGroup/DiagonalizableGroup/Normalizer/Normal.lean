/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Centralizer.Basic
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Normalizer.Scheme
import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints

/-!
# The centralizer and the diagonalizable subgroup are normal in the normalizer

Let `G = Spec H` be an affine group scheme over a commutative ring `R` and `D(X) → G` a closed
diagonalizable subgroup with surjective coordinate map `π : H →ₐc[R] R[X]`. The normalizer
`N_G(D(X))` is cut out by `BialgHom.normalizerHopfIdeal π hπ`, and the centralizer `Z_G(D(X))`
by `BialgHom.centralizerHopfIdeal π`. This file shows that `Z_G(D(X))` is a closed subgroup of
`N_G(D(X))`, that both `D(X)` and `Z_G(D(X))` are normal in `N_G(D(X))`, and that the normalizer
is the whole group exactly when `D(X)` is normal in `G`.

A closed subgroup of `N_G(D(X))` is cut out by the image, in the quotient Hopf algebra
`H ⧸ normalizerHopfIdeal π hπ`, of the Hopf ideal of `H` cutting it out in `G`. It is normal as
soon as the points of the normalizer, which are the points normalizing `D(X)` after every
extension of the value algebra, normalize its points in `G`. For `D(X)` this is the definition
of the normalizer. For `Z_G(D(X))`, conjugating a point commuting with every point of `D(X)` by
a point normalizing `D(X)` yields another such point.

## Main declarations

* `BialgHom.normalizerHopfIdeal_le_centralizerHopfIdeal`: the centralizer of the diagonalizable
  subgroup is contained in its normalizer.
* `BialgHom.isNormal_map_kerOfSurjective_mkBialgHom_normalizerHopfIdeal`: the diagonalizable
  subgroup is normal in its normalizer.
* `BialgHom.isNormal_map_centralizerHopfIdeal_mkBialgHom_normalizerHopfIdeal`: the centralizer
  of the diagonalizable subgroup is normal in the normalizer.
* `BialgHom.normalizerHopfIdeal_eq_bot_iff_isNormal`: the normalizer is the whole group exactly
  when the diagonalizable subgroup is normal.

## References

* SGA 3, Exposé XI, Proposition 5.9.
* J. S. Milne, *Algebraic Groups* (2017), §12 and §13.b.
-/

public section

open WithConv

namespace BialgHom

open TauCeti

universe u

variable {R H X : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H] [CommGroup X]
variable (π : H →ₐc[R] MonoidAlgebra R X) (hπ : Function.Surjective π)

/-- **The centralizer of a diagonalizable subgroup is contained in its normalizer.** The order on
defining ideals reverses the inclusion of closed subgroup schemes. -/
theorem normalizerHopfIdeal_le_centralizerHopfIdeal :
    normalizerHopfIdeal π hπ ≤ centralizerHopfIdeal π := by
  let A := CommAlgCat.of R (H ⧸ (centralizerHopfIdeal π).toIdeal)
  let q : WithConv (H →ₐ[R] A) := toConv (Ideal.Quotient.mkₐ R (centralizerHopfIdeal π).toIdeal)
  have hq : q ∈ centralizerPointsSubgroup π A := by
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    exact fun x hx ↦ Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have hle : (normalizerHopfIdeal π hπ).toIdeal ≤ RingHom.ker q.ofConv := by
    rw [normalizerHopfIdeal_le_ker_iff, mem_universalNormalizerPoints]
    refine fun B φ ↦ Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, rfl⟩
    exact ((mem_centralizerPointsSubgroup_iff π A q).mp hq φ t).symm
  exact fun x hx ↦ Ideal.Quotient.eq_zero_iff_mem.mp (hle (HopfIdeal.mem_toIdeal.mpr hx))

/-- The image in the normalizer of a closed subgroup of `G` is normal as soon as the points of
the normalizer normalize the points of the subgroup over every value algebra. -/
private theorem isNormal_map_mkBialgHom_normalizerHopfIdeal_of_le_normalizer (I : HopfIdeal R H)
    (h : ∀ A : CommAlgCat.{u} R, universalNormalizerPoints π A ≤
      Subgroup.normalizer
        (CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I A : Set _)) :
    (I.map (Bialgebra.Quotient.mkBialgHom (normalizerHopfIdeal π hπ).toIdeal)).IsNormal := by
  have key : (I.map (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R H)
      (normalizerHopfIdeal π hπ)).hom).IsNormal := by
    rw [CommHopfAlgCat.isNormal_iff_quotientPointsSubgroup_normal]
    refine fun A ↦ ⟨fun n hn g ↦ ?_⟩
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_map_iff (CommHopfAlgCat.mkQuotient
        (_root_.CommHopfAlgCat.of R H) (normalizerHopfIdeal π hπ)),
      CommHopfAlgCat.Hom.mapPointsFunctor_app_apply, ← BialgHom.mapDomain_apply] at hn ⊢
    have hg : BialgHom.mapDomain (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R H)
        (normalizerHopfIdeal π hπ)).hom g ∈ universalNormalizerPoints π A := by
      rw [← quotientPointsSubgroup_normalizerHopfIdeal π hπ,
        CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
      intro x hx
      rw [BialgHom.mapDomain_apply_apply, CommHopfAlgCat.mkQuotient_apply,
        Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem.mpr (HopfIdeal.mem_toIdeal.mpr hx), map_zero]
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (h A hg) _).mp hn
  exact key

/-- **The diagonalizable subgroup is normal in its normalizer.** -/
theorem isNormal_map_kerOfSurjective_mkBialgHom_normalizerHopfIdeal :
    ((HopfIdeal.kerOfSurjective π hπ).map
      (Bialgebra.Quotient.mkBialgHom (normalizerHopfIdeal π hπ).toIdeal)).IsNormal := by
  refine isNormal_map_mkBialgHom_normalizerHopfIdeal_of_le_normalizer π hπ _ fun A g hg ↦ ?_
  rw [HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range π hπ A]
  simpa only [AlgHom.mapValue_id, MonoidHom.id_apply] using
    (mem_universalNormalizerPoints π A g).mp hg A (AlgHom.id R A)

/-- **The centralizer of a diagonalizable subgroup is normal in the normalizer.** -/
theorem isNormal_map_centralizerHopfIdeal_mkBialgHom_normalizerHopfIdeal :
    ((centralizerHopfIdeal π).map
      (Bialgebra.Quotient.mkBialgHom (normalizerHopfIdeal π hπ).toIdeal)).IsNormal := by
  refine isNormal_map_mkBialgHom_normalizerHopfIdeal_of_le_normalizer π hπ _ fun A ↦
    Subgroup.le_normalizer_iff.mpr fun g hg n hn ↦ ?_
  rw [mem_centralizerPointsSubgroup_iff] at hn ⊢
  intro B _ _ φ t
  have hφ := (mem_universalNormalizerPoints π A g).mp hg (CommAlgCat.of R B) φ
  obtain ⟨t', ht'⟩ := (Subgroup.mem_normalizer_iff''.mp hφ _).mp ⟨t, rfl⟩
  have ht : BialgHom.mapDomain π t =
      AlgHom.mapValue φ g * BialgHom.mapDomain π t' * (AlgHom.mapValue φ g)⁻¹ := by
    rw [ht']
    group
  rw [map_mul, map_mul, map_inv, ht]
  exact (hn φ t').conj _

/-- **The normalizer is the whole group exactly when the diagonalizable subgroup is normal.** -/
theorem normalizerHopfIdeal_eq_bot_iff_isNormal :
    normalizerHopfIdeal π hπ = ⊥ ↔ (HopfIdeal.kerOfSurjective π hπ).IsNormal := by
  constructor
  · intro h
    rw [CommHopfAlgCat.isNormal_iff_quotientPointsSubgroup_normal (_root_.CommHopfAlgCat.of R H)]
    intro A
    rw [HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range π hπ A,
      ← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    intro g _
    have hg : g ∈ universalNormalizerPoints π A := by
      rw [← normalizerHopfIdeal_le_ker_iff π hπ, h, HopfIdeal.bot_toIdeal]
      exact bot_le
    simpa only [AlgHom.mapValue_id, MonoidHom.id_apply] using
      (mem_universalNormalizerPoints π A g).mp hg A (AlgHom.id R A)
  · intro hI
    have hid : (normalizerHopfIdeal π hπ).toIdeal ≤
        RingHom.ker (toConv (AlgHom.id R H) : WithConv (H →ₐ[R] CommAlgCat.of R H)).ofConv := by
      rw [normalizerHopfIdeal_le_ker_iff, mem_universalNormalizerPoints]
      intro B φ
      rw [← HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range π hπ B,
        Subgroup.normalizer_eq_top_iff.mpr
          (CommHopfAlgCat.quotientPointsSubgroup_normal _ _ hI B)]
      exact Subgroup.mem_top _
    rw [eq_bot_iff]
    exact fun x hx ↦ HopfIdeal.mem_bot.mpr (hid (HopfIdeal.mem_toIdeal.mpr hx))

end BialgHom

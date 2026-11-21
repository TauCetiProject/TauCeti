/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Splitting
public import TauCeti.AlgebraicGeometry.GroupScheme.Torsion.Basic
import TauCeti.GroupTheory.ExponentPrime

/-!
# Splitting finite étale `ℓ`-torsion over a field

Let `G` be a commutative group scheme over a field `K` which is finite étale of rank `ℓ ^ r`
over `Spec K` and killed by a prime `ℓ`. After a finite Galois extension `L / K` whose degree
divides `(ℓ ^ r)!`, the group of points of `G` with values in `L`, the morphisms
`Spec L ⟶ G` over `Spec K`, is isomorphic to `(ℤ/ℓℤ) ^ r`. No hypothesis on the characteristic
of `K` or on the perfectness of `K` is needed: étaleness of `G` is what makes its points rational
over a finite separable extension.

More generally, for any field extension `K₁ / K`, the same holds over a finite Galois extension
`L / K₁` of degree dividing `(ℓ ^ r)!`. This is the form used to combine the splitting of `G` with a
previously chosen extension `K₁`, for instance one over which a curve acquires a rational point:
the degrees multiply in the tower `K ⊆ K₁ ⊆ L`.

The extension is the one splitting the base change `G_{K₁}`, again finite étale of rank `ℓ ^ r`, as
a finite étale scheme over `K₁`
(`AlgebraicGeometry.Scheme.Hom.exists_natCard_hom_eq_finrank_of_isFinite_of_etale`), over which
`G_{K₁}` has exactly `ℓ ^ r` points; by the pullback adjunction these are the points of `G` with
values in `L`. A commutative group killed by `ℓ` with `ℓ ^ r` elements is `(ℤ/ℓℤ) ^ r`
(`TauCeti.nonempty_mulEquiv_of_exponent_dvd_of_natCard_eq_pow`).

The main application is to the `ℓ`-torsion `A[ℓ]` of a commutative group scheme `A`: when `A[ℓ]`
is finite étale of rank `ℓ ^ r`, the `ℓ`-torsion of the group of `L`-points of `A` is
`(ℤ/ℓℤ) ^ r`. For the Jacobian of a curve of genus `g`, with `ℓ` invertible in `K`, the rank is
`ℓ ^ (2g)`, which gives the factor `(ℓ ^ (2g))!` of the degree bound in the semistable reduction
theorem.

## Main results

* `TauCeti.GroupScheme.exists_nonempty_mulEquiv_points_of_zpow_eq_one`: a finite étale
  commutative group scheme of rank `ℓ ^ r` killed by `ℓ` has group of `L`-points `(ℤ/ℓℤ) ^ r`
  over a finite Galois extension `L / K` of degree dividing `(ℓ ^ r)!`.
* `TauCeti.GroupScheme.exists_nonempty_mulEquiv_ker_zpowGroupHom`: if the `ℓ`-torsion of a
  commutative group scheme is finite étale of rank `ℓ ^ r`, then over such an extension the
  `ℓ`-torsion of the group of `L`-points is `(ℤ/ℓℤ) ^ r`.
* `TauCeti.GroupScheme.exists_isScalarTower_and_nonempty_mulEquiv_points_of_zpow_eq_one` and
  `TauCeti.GroupScheme.exists_isScalarTower_and_nonempty_mulEquiv_ker_zpowGroupHom`: the same over
  a finite Galois extension `L / K₁` of degree dividing `(ℓ ^ r)!`, for any extension `K₁ / K`.

## References

* The Stacks Project, [Tag 0CDN](https://stacks.math.columbia.edu/tag/0CDN), for the degree bound
  in the semistable reduction theorem.
* D. Mumford, *Abelian Varieties*, §4, for the `ℓ`-torsion of an abelian variety.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonObj

namespace TauCeti.GroupScheme

universe u

variable {K : Type u} [Field K]

/-- **Finite étale `ℓ`-torsion becomes `(ℤ/ℓℤ) ^ r` over a Galois extension of a given extension.**
Let `G` be a commutative group scheme over a field `K`, finite étale of rank `ℓ ^ r` over `Spec K`
and killed by the prime `ℓ`, and let `K₁` be any field extension of `K`. There is a finite Galois
extension `L / K₁` of degree dividing `(ℓ ^ r)!` such that the group of points of `G` with values
in `L` is isomorphic to `(ZMod ℓ) ^ r`. -/
theorem exists_isScalarTower_and_nonempty_mulEquiv_points_of_zpow_eq_one
    (G : CommGrp (Over (Spec (.of K)))) [IsFinite G.X.hom] [Etale G.X.hom] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hG : 𝟙 G.X ^ (ℓ : ℤ) = 1) {r : ℕ} (s : Spec (.of K)) (hr : G.X.hom.finrank s = ℓ ^ r)
    (K₁ : Type u) [Field K₁] [Algebra K K₁] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K₁ L) (_ : Algebra K L) (_ : IsScalarTower K K₁ L)
      (_ : Module.Finite K₁ L) (_ : IsGalois K₁ L),
      Module.finrank K₁ L ∣ (ℓ ^ r).factorial ∧
        Nonempty ((Over.mk (Spec.algebraMap K L) ⟶ G.X) ≃* Multiplicative (Fin r → ZMod ℓ)) := by
  -- Split the base change `G_{K₁}`, which is finite étale over `Spec K₁` of the same rank.
  let g := Spec.algebraMap K K₁
  have hr₁ : (pullback.snd G.X.hom g).finrank default = ℓ ^ r := by
    rw [Scheme.Hom.finrank_pullback_snd, Subsingleton.elim (g default) s, hr]
  obtain ⟨L, _, _, _, _, hdeg, hcard⟩ :=
    (pullback.snd G.X.hom g).exists_natCard_hom_eq_finrank_of_isFinite_of_etale default
  let : Algebra K L := ((algebraMap K₁ L).comp (algebraMap K K₁)).toAlgebra
  have : IsScalarTower K K₁ L := .of_algebraMap_eq' rfl
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hr₁ ▸ hdeg, ?_⟩
  -- The points of `G_{K₁}` over `K₁` with values in `L` are the points of `G` with values in `L`,
  -- through the pullback adjunction.
  have hL : Spec.algebraMap K L = Spec.algebraMap K₁ L ≫ g := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have hcard' : Nat.card (Over.mk (Spec.algebraMap K L) ⟶ G.X) = ℓ ^ r := by
    rw [← hr₁, ← hcard, hL]
    exact Nat.card_congr ((Over.mapPullbackAdj g).homEquiv (Over.mk (Spec.algebraMap K₁ L)) G.X)
  -- A commutative group killed by `ℓ` with `ℓ ^ r` elements is `(ℤ/ℓℤ) ^ r`.
  refine nonempty_mulEquiv_of_exponent_dvd_of_natCard_eq_pow hℓ
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x ↦ ?_) hcard'
  rw [← zpow_natCast, ← Category.comp_id x, ← GrpObj.comp_zpow, hG, MonObj.comp_one]

/-- **Finite étale `ℓ`-torsion becomes `(ℤ/ℓℤ) ^ r` over a Galois extension of degree dividing
`(ℓ ^ r)!`.** Let `G` be a commutative group scheme over a field `K`, finite étale of rank
`ℓ ^ r` over `Spec K` and killed by the prime `ℓ`. There is a finite Galois extension `L / K`
of degree dividing `(ℓ ^ r)!` such that the group of points of `G` with values in `L` is
isomorphic to `(ZMod ℓ) ^ r`. -/
theorem exists_nonempty_mulEquiv_points_of_zpow_eq_one (G : CommGrp (Over (Spec (.of K))))
    [IsFinite G.X.hom] [Etale G.X.hom] {ℓ : ℕ} (hℓ : ℓ.Prime) (hG : 𝟙 G.X ^ (ℓ : ℤ) = 1) {r : ℕ}
    (s : Spec (.of K)) (hr : G.X.hom.finrank s = ℓ ^ r) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L) (_ : IsGalois K L),
      Module.finrank K L ∣ (ℓ ^ r).factorial ∧
        Nonempty ((Over.mk (Spec.algebraMap K L) ⟶ G.X) ≃* Multiplicative (Fin r → ZMod ℓ)) := by
  obtain ⟨L, _, i₁, i₂, h, _, _, hdeg, e⟩ :=
    exists_isScalarTower_and_nonempty_mulEquiv_points_of_zpow_eq_one G hℓ hG s hr K
  -- For `K₁ = K` the two algebra structures of `L` over `K` agree.
  obtain rfl : i₂ = i₁ :=
    Algebra.algebra_ext _ _ (@IsScalarTower.algebraMap_apply _ _ _ _ _ _ _ i₁ i₂ h)
  exact ⟨L, inferInstance, i₂, inferInstance, inferInstance, hdeg, e⟩

/-- **Finite étale `ℓ`-torsion points become `(ℤ/ℓℤ) ^ r` over a Galois extension of a given
extension.** Let `A` be a commutative group scheme over a field `K` whose `ℓ`-torsion `A[ℓ]`, for a
prime `ℓ`, is finite étale of rank `ℓ ^ r` over `Spec K`, and let `K₁` be any field extension of
`K`. There is a finite Galois extension `L / K₁` of degree dividing `(ℓ ^ r)!` such that the
`ℓ`-torsion of the group of points of `A` with values in `L` is isomorphic to `(ZMod ℓ) ^ r`. -/
theorem exists_isScalarTower_and_nonempty_mulEquiv_ker_zpowGroupHom
    (A : CommGrp (Over (Spec (.of K)))) {ℓ : ℕ} (hℓ : ℓ.Prime) [IsFinite (torsion A ℓ).X.hom]
    [Etale (torsion A ℓ).X.hom] {r : ℕ} (s : Spec (.of K))
    (hr : (torsion A ℓ).X.hom.finrank s = ℓ ^ r) (K₁ : Type u) [Field K₁] [Algebra K K₁] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K₁ L) (_ : Algebra K L) (_ : IsScalarTower K K₁ L)
      (_ : Module.Finite K₁ L) (_ : IsGalois K₁ L),
      Module.finrank K₁ L ∣ (ℓ ^ r).factorial ∧
        Nonempty ((zpowGroupHom (ℓ : ℤ) :
          (Over.mk (Spec.algebraMap K L) ⟶ A.X) →* (Over.mk (Spec.algebraMap K L) ⟶ A.X)).ker ≃*
            Multiplicative (Fin r → ZMod ℓ)) := by
  obtain ⟨L, _, _, _, _, _, _, hdeg, ⟨e⟩⟩ :=
    exists_isScalarTower_and_nonempty_mulEquiv_points_of_zpow_eq_one
      (torsionCommGrp A ℓ) hℓ (torsion_zpow_eq_one _) s hr K₁
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hdeg, ⟨(torsionPointsMulEquiv A ℓ _).symm.trans e⟩⟩

/-- **Finite étale `ℓ`-torsion points become `(ℤ/ℓℤ) ^ r` over a Galois extension of degree
dividing `(ℓ ^ r)!`.** Let `A` be a commutative group scheme over a field `K` whose `ℓ`-torsion
`A[ℓ]`, for a prime `ℓ`, is finite étale of rank `ℓ ^ r` over `Spec K`. There is a finite Galois
extension `L / K` of degree dividing `(ℓ ^ r)!` such that the `ℓ`-torsion of the group of points
of `A` with values in `L` is isomorphic to `(ZMod ℓ) ^ r`. -/
theorem exists_nonempty_mulEquiv_ker_zpowGroupHom (A : CommGrp (Over (Spec (.of K)))) {ℓ : ℕ}
    (hℓ : ℓ.Prime) [IsFinite (torsion A ℓ).X.hom] [Etale (torsion A ℓ).X.hom] {r : ℕ}
    (s : Spec (.of K)) (hr : (torsion A ℓ).X.hom.finrank s = ℓ ^ r) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L) (_ : IsGalois K L),
      Module.finrank K L ∣ (ℓ ^ r).factorial ∧
        Nonempty ((zpowGroupHom (ℓ : ℤ) :
          (Over.mk (Spec.algebraMap K L) ⟶ A.X) →* (Over.mk (Spec.algebraMap K L) ⟶ A.X)).ker ≃*
            Multiplicative (Fin r → ZMod ℓ)) := by
  obtain ⟨L, _, _, _, _, hdeg, ⟨e⟩⟩ := exists_nonempty_mulEquiv_points_of_zpow_eq_one
    (torsionCommGrp A ℓ) hℓ (torsion_zpow_eq_one _) s hr
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, hdeg,
    ⟨(torsionPointsMulEquiv A ℓ _).symm.trans e⟩⟩

end TauCeti.GroupScheme

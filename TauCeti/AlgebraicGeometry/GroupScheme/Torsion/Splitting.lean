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

The extension is the one splitting `G` as a finite étale scheme
(`AlgebraicGeometry.Scheme.Hom.exists_natCard_hom_eq_finrank_of_isFinite_of_etale`), over which
`G` has exactly `ℓ ^ r` points. A commutative group killed by `ℓ` with `ℓ ^ r` elements is
`(ℤ/ℓℤ) ^ r` (`TauCeti.nonempty_mulEquiv_of_exponent_dvd_of_natCard_eq_pow`).

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

## References

* The Stacks Project, [Tag 0CDN](https://stacks.math.columbia.edu/tag/0CDN), for the degree bound
  in the semistable reduction theorem.
* D. Mumford, *Abelian Varieties*, §4, for the `ℓ`-torsion of an abelian variety.
-/

public section

open CategoryTheory AlgebraicGeometry MonObj

namespace TauCeti.GroupScheme

universe u

variable {K : Type u} [Field K]

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
  obtain ⟨L, _, _, _, _, hdeg, hcard⟩ :=
    G.X.hom.exists_natCard_hom_eq_finrank_of_isFinite_of_etale s
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, hr ▸ hdeg, ?_⟩
  refine nonempty_mulEquiv_of_exponent_dvd_of_natCard_eq_pow hℓ
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x ↦ ?_) (hr ▸ hcard)
  rw [← zpow_natCast, ← Category.comp_id x, ← GrpObj.comp_zpow, hG, MonObj.comp_one]

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

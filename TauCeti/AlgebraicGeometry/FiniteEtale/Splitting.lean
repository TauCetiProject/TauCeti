/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import TauCeti.AlgebraicGeometry.FiniteEtale.Basic
public import TauCeti.AlgebraicGeometry.Pullback.SpecMap
public import TauCeti.RingTheory.Etale.Splitting
import TauCeti.AlgebraicGeometry.Scheme.SpecOver
import TauCeti.RingTheory.TotallySplit

/-!
# Splitting finite étale schemes over a field

Every finite étale scheme over a field becomes the spectrum of a finite product of `n` copies
of the base field after a finite Galois extension whose degree divides `n!`. The isomorphism
is over the extended base, so it labels all points as rational points, including their scheme
structures.
The empty scheme corresponds to the product indexed by `Fin 0`.

This is the scheme form of `TauCeti.Algebra.Etale.exists_isFiniteSplit_tensorProduct`, transported
through `TauCeti.FiniteEtaleScheme.spec` and Mathlib's affine pullback comparison.

Counted in the functor-of-points sense, there is a finite Galois extension `L / K` of degree
dividing `n!` over which a finite étale scheme `X` of rank `n` over `K` has exactly `n` points
with values in `L`, that is `n` morphisms `Spec L ⟶ X` over `Spec K`. The rank is Mathlib's
`AlgebraicGeometry.Scheme.Hom.finrank`, so this applies to any finite étale scheme over a field
whose rank is known.

## References

* The Stacks Project, Tag 03QR (schemes étale over a point).
-/

public section

open CategoryTheory Limits AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A finite étale scheme becomes a disjoint union of `n` rational points after a finite
Galois field extension of degree dividing `n!`. The splitting is an isomorphism over the
extended base. -/
theorem exists_split_of_isFinite_of_etale {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (_ : Module.Finite K L) (_ : IsGalois K L) (n : ℕ),
      Module.finrank K L ∣ n.factorial ∧
        Nonempty (Over.mk (pullback.snd f (Spec.algebraMap K L)) ≅
          Over.mk (Spec.algebraMap L (Fin n → L))) := by
  obtain ⟨A, ⟨e₀⟩⟩ := f.exists_finiteEtale_algebra
  obtain ⟨L, _, _, _, _, hdeg, hL⟩ :=
    TauCeti.Algebra.Etale.exists_isFiniteSplit_tensorProduct K A.obj
  obtain ⟨n, ⟨a⟩⟩ := hL.nonempty_algEquiv_fun
  have hn : Module.finrank K A.obj = n := by
    rw [← Module.finrank_baseChange (R := L), a.toLinearEquiv.finrank_eq]
    simp
  let e₁ :=
    TauCeti.AlgebraicGeometry.pullbackSpecIsoOfAlgEquiv K A.obj L (Fin n → L) a
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, n, hn ▸ hdeg,
    ⟨((Over.pullback (Spec.algebraMap K L)).mapIso e₀).symm ≪≫ e₁⟩⟩

/-- **A finite étale scheme of rank `n` has `n` points over a Galois extension of degree dividing
`n!`.** For a finite étale morphism `f : X ⟶ Spec K` of rank `n` there is a finite Galois
extension `L / K` of degree dividing `n!` such that exactly `n` morphisms `Spec L ⟶ X` lie over
`Spec K`. -/
theorem exists_natCard_hom_eq_finrank_of_isFinite_of_etale {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f] (s : Spec (.of K)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (_ : Module.Finite K L) (_ : IsGalois K L),
      Module.finrank K L ∣ (f.finrank s).factorial ∧
        Nat.card (Over.mk (Spec.algebraMap K L) ⟶ Over.mk f) = f.finrank s := by
  obtain ⟨A, ⟨e⟩⟩ := f.exists_finiteEtale_algebra
  have : Module.Finite K A.obj := Algebra.FormallyUnramified.finite_of_free K A.obj
  -- The rank of `f` is the dimension of its coordinate algebra `A`.
  have hrank : f.finrank s = Module.finrank K A.obj := by
    have hw : e.hom.left ≫ f = Spec.algebraMap K A.obj := Over.w e.hom
    rw [← Scheme.Hom.finrank_comp_left_of_isIso e.hom.left f, hw, Spec.algebraMap]
    exact (Scheme.Hom.finrank_SpecMap_algebraMap K A.obj s).trans
      (congrFun Module.rankAtStalk_eq_finrank_of_free s)
  obtain ⟨L, _, _, _, _, hdeg, hL⟩ :=
    TauCeti.Algebra.Etale.exists_isFiniteSplit_tensorProduct K A.obj
  -- `L ⊗[K] A` is split over `L`, so `A` has `finrank K A` characters with values in `L`.
  have hcard : Nat.card (A.obj →ₐ[K] L) = Module.finrank K A.obj := by
    rw [Nat.card_congr (AlgHom.liftEquiv K L A.obj L), hL.card_algHom_eq_finrank,
      Module.finrank_baseChange]
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    by rw [hrank]; exact hdeg, ?_⟩
  rw [hrank, ← hcard]
  -- The points of `X` with values in `L` are the characters of `A` with values in `L`.
  let eL : Over.mk (Spec.algebraMap K L) ≅ (algSpec (.of K)).obj (op (CommAlgCat.of K L)) :=
    (TauCeti.AlgebraicGeometry.algSpecObjIsoOverMk (R := .of K) (.of K L)).symm
  let eA : Over.mk (Spec.algebraMap K A.obj) ≅
      (algSpec (.of K)).obj (op (CommAlgCat.of K A.obj)) :=
    (TauCeti.AlgebraicGeometry.algSpecObjIsoOverMk (R := .of K) (.of K A.obj)).symm
  exact Nat.card_congr ((Iso.homCongr eL (e.symm ≪≫ eA)).trans
    (TauCeti.AlgebraicGeometry.algSpecHomEquivAlgHom _ _))

end AlgebraicGeometry.Scheme.Hom

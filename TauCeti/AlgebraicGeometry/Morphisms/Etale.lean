/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Rank
import TauCeti.AlgebraicGeometry.RationalPoint.Affine
import TauCeti.RingTheory.TotallySplit

/-!
# Rational points of finite schemes over a field and étaleness

Let `f : X ⟶ Spec R` be a morphism from an affine scheme to the spectrum of a commutative ring.
Then `f` is étale exactly when `Γ(X, ⊤)` is an étale `R`-algebra. Its points with values in
`Spec R` are the characters `Γ(X, ⊤) →ₐ[R] R` of its coordinate ring
(`AlgebraicGeometry.Scheme.Hom.pointsEquivAlgHom`, in
`TauCeti.AlgebraicGeometry.RationalPoint.Affine`).

Now let `f : X ⟶ Spec K` be a finite morphism to the spectrum of a field. A finite-dimensional
`K`-algebra has at most as many characters as its dimension, which is the rank of `f`
(`AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_of_field`).
When `X` has at least that many points over `Spec K`, its coordinate ring is a finite product of
copies of `K` (`Algebra.IsFiniteSplit.of_finrank_le_card_algHom`), so `f` is étale. Conversely,
over a separably closed field a finite étale `K`-algebra is a finite product of copies of `K`, so a
finite étale scheme over `Spec K` has exactly as many points over `Spec K` as its rank.

Points over `Spec K` are written as morphisms `𝟙_ (Over (Spec K)) ⟶ Over.mk f` of the cartesian
monoidal category `Over (Spec K)`, as for the points of group schemes over `Spec K`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.etale_iff_algebraEtale`: for affine `X`, `f : X ⟶ Spec R` is
  étale exactly when `Γ(X, ⊤)` is an étale `R`-algebra.
* `AlgebraicGeometry.Scheme.Hom.etale_of_finrank_le_natCard`: a finite morphism `f : X ⟶ Spec K`
  with at least `f.finrank s` points of `X` over `Spec K` is étale.
* `AlgebraicGeometry.Scheme.Hom.natCard_eq_finrank_of_etale`: over a separably closed field `K`,
  a finite étale morphism `f : X ⟶ Spec K` has exactly `f.finrank s` points of `X` over `Spec K`.
-/

public section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- A morphism `f : X ⟶ Spec R` from an affine scheme is étale exactly when its coordinate ring
`Γ(X, ⊤)` is an étale `R`-algebra, for the `R`-algebra structure given by the map of global
sections of `f`. -/
theorem Scheme.Hom.etale_iff_algebraEtale (f : X ⟶ Spec (.of R)) [IsAffine X] [Algebra R Γ(X, ⊤)]
    (hf : algebraMap R Γ(X, ⊤) = ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom) :
    Etale f ↔ Algebra.Etale R Γ(X, ⊤) := by
  -- the map of global sections of `f` is `algebraMap R Γ(X, ⊤)` up to `Γ(Spec R, ⊤) ≅ R`
  have hf' : f.appTop =
      (Scheme.ΓSpecIso (.of R)).hom ≫ CommRingCat.ofHom (algebraMap R Γ(X, ⊤)) := by
    simp [hf]
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), hf', CommRingCat.hom_comp,
    RingHom.Etale.respectsIso.cancel_left_isIso, CommRingCat.hom_ofHom, RingHom.etale_algebraMap]

variable {K : Type u} [Field K]

/-- **A finite scheme over a field with as many rational points as its degree is étale.** Let
`f : X ⟶ Spec K` be finite. If `X` has at least `f.finrank s` points over `Spec K`, then `f` is
étale: the coordinate ring of `X` is a finite product of copies of `K`. -/
theorem Scheme.Hom.etale_of_finrank_le_natCard (f : X ⟶ Spec (.of K)) [IsFinite f]
    (s : Spec (.of K)) (h : f.finrank s ≤ Nat.card (𝟙_ (Over (Spec (.of K))) ⟶ Over.mk f)) :
    Etale f := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom.toAlgebra
  have hf : algebraMap K Γ(X, ⊤) = ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom := rfl
  have : Module.Finite K Γ(X, ⊤) := f.moduleFinite_appTop hf
  have : Algebra.IsFiniteSplit K Γ(X, ⊤) := .of_finrank_le_card_algHom <| by
    rw [← f.finrank_eq_finrank_of_field hf s, ← Nat.card_congr (f.pointsEquivAlgHom hf)]
    exact h
  exact (f.etale_iff_algebraEtale hf).2 inferInstance

/-- **A finite étale scheme over a separably closed field has as many rational points as its
degree.** Let `K` be separably closed and `f : X ⟶ Spec K` finite étale. Then `X` has exactly
`f.finrank s` points over `Spec K`: its coordinate ring is a finite product of copies of `K`. -/
theorem Scheme.Hom.natCard_eq_finrank_of_etale [IsSepClosed K] (f : X ⟶ Spec (.of K))
    [IsFinite f] [Etale f] (s : Spec (.of K)) :
    Nat.card (𝟙_ (Over (Spec (.of K))) ⟶ Over.mk f) = f.finrank s := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom.toAlgebra
  have hf : algebraMap K Γ(X, ⊤) = ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom := rfl
  have : Module.Finite K Γ(X, ⊤) := f.moduleFinite_appTop hf
  have : Algebra.Etale K Γ(X, ⊤) := (f.etale_iff_algebraEtale hf).1 ‹_›
  -- so `Γ(X, ⊤) ≃ₐ[K] Fin m → K`, which has the `m` characters given by the coordinates
  obtain ⟨m, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun K Γ(X, ⊤)
  rw [Nat.card_congr (f.pointsEquivAlgHom hf), f.finrank_eq_finrank_of_field hf s]
  refine le_antisymm (card_algHom_le_finrank K Γ(X, ⊤) K) ?_
  have := Finite.algHom K Γ(X, ⊤) K
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
  refine (Nat.card_fin m).symm.le.trans
    (Nat.card_le_card_of_injective (fun i ↦ (Pi.evalAlgHom K (fun _ ↦ K) i).comp e.toAlgHom) ?_)
  intro i j hij
  have := congr($hij (e.symm (Pi.single i 1)))
  by_contra hne
  simp [hne] at this

end AlgebraicGeometry

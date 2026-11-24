/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.KrullDimension

import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Ideal.Height
import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Stalk.Basic
import TauCeti.Topology.KrullDimension.Basic

/-!
# The dimension of a formal scheme

The dimension of a formal scheme `X` at a point `x` is the Krull dimension of its local ring
`𝒪_{X,x}`, and the dimension `X.dim` of `X` is the supremum of these local dimensions, which is
`⊥` exactly when `X` is empty. Unlike for schemes, this is not the Krull dimension of the
underlying topological space: with the maximal-ideal-adic topology, the formal spectrum of
`ℤ_p⟦t⟧` has a single point, while its ring has dimension `2`.

For a noetherian adic ring `A`, the local ring of `Spf A` at the open prime `𝔭` has the dimension
of `A_𝔭` (`TauCeti.FormalScheme.Spf.ringKrullDim_stalk`), and every maximal ideal of `A` is open
(`TauCeti.FormalScheme.Spf.mem_carrier_of_isMaximal`), so `dim (Spf A) = dim A`. Applied to the
quotient adic rings `A ⧸ 𝔞` (`TauCeti.IsAdicRing.quotient`), it gives
`dim (Spf (A ⧸ 𝔞)) = dim (A ⧸ 𝔞)` for every ideal `𝔞`. For an ordinary scheme, regarded as a
formal scheme, the dimension is the Krull dimension of its underlying space.

## Main definitions

* `TauCeti.FormalScheme.dim`: the supremum of the Krull dimensions of the local rings.

## Main results

* `TauCeti.FormalScheme.dim_eq_bot_iff`: the dimension is `⊥` exactly for the empty formal scheme.
* `TauCeti.FormalScheme.dim_le_of_isOpenImmersion`: an open immersion does not raise dimension.
* `TauCeti.FormalScheme.dim_ofSpf`: `dim (Spf A) = dim A` for a noetherian adic ring `A`.
* `TauCeti.FormalScheme.dim_toFormalScheme`: an ordinary scheme has, as a formal scheme, the
  Krull dimension of its underlying space.

## References

* W. Zhang, *Weil representation and arithmetic fundamental lemma*, Ann. of Math. 193 (2021),
  Appendix B.1.
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, 7.6.15–7.6.18,
  and Ch. I, 10.1.5–10.1.6.
* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ), for schemes.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry

namespace TauCeti.FormalScheme

/-- The **dimension** of a formal scheme `X`: the supremum over the points `x` of `X` of the Krull
dimensions of the local rings `𝒪_{X,x}`. It is `⊥` for the empty formal scheme. It is not the
Krull dimension of the underlying space, which can be a single point when `X` has positive
dimension. -/
noncomputable def dim (X : FormalScheme.{u}) : WithBot ℕ∞ :=
  ⨆ x : X, ringKrullDim (X.presheaf.stalk x)

variable {X Y : FormalScheme.{u}}

theorem dim_def (X : FormalScheme.{u}) : X.dim = ⨆ x : X, ringKrullDim (X.presheaf.stalk x) :=
  (rfl)

theorem ringKrullDim_stalk_le_dim (x : X) : ringKrullDim (X.presheaf.stalk x) ≤ X.dim :=
  le_iSup (fun x : X ↦ ringKrullDim (X.presheaf.stalk x)) x

theorem dim_le_iff {n : WithBot ℕ∞} :
    X.dim ≤ n ↔ ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ n :=
  iSup_le_iff

/-- The dimension of a formal scheme is `⊥` exactly when it is empty: its local rings are local,
hence nonzero, so each has dimension at least `0`. -/
@[simp]
theorem dim_eq_bot_iff : X.dim = ⊥ ↔ IsEmpty X := by
  simp only [dim_def, iSup_eq_bot, ringKrullDim_eq_bot_iff_subsingleton, not_subsingleton,
    isEmpty_iff]

/-- The source of an open immersion has dimension at most that of its target, since an open
immersion identifies local rings. -/
theorem dim_le_of_isOpenImmersion (f : X ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion (forgetToLocallyRingedSpace.map f)] : X.dim ≤ Y.dim :=
  dim_le_iff.mpr fun x ↦ (ringKrullDim_eq_of_ringEquiv
    (stalkRingEquivOfIsOpenImmersion f x)).ge.trans (ringKrullDim_stalk_le_dim _)

/-- The dimension of the formal spectrum of a noetherian adic ring `A` is the Krull dimension
of `A`. The local ring at the open prime `𝔭` has the dimension of `A_𝔭`, which is at most
`dim A`, and the supremum is attained at maximal ideals, all of which are open. -/
@[simp]
theorem dim_ofSpf (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsAdicRing A] [IsNoetherianRing A] : (ofSpf A).dim = ringKrullDim A := by
  have hstalk (p : Spf.carrier A) :
      ringKrullDim ((ofSpf A).presheaf.stalk p) = (p : PrimeSpectrum A).asIdeal.height :=
    -- the local rings of `ofSpf A` are those of `Spf A`, by `ofSpf_toLocallyRingedSpace`
    (Spf.ringKrullDim_stalk p).trans (IsLocalization.AtPrime.ringKrullDim_eq_height _ _)
  refine le_antisymm (dim_le_iff.mpr fun p ↦ ?_) ((ringKrullDim_le_iff_isMaximal_height_le _).mpr
    fun m hm ↦ ?_)
  · exact (hstalk p).trans_le Ideal.height_le_ringKrullDim_of_isPrime
  · exact (hstalk (Spf.pointOfIsMaximal m)).ge.trans
      (ringKrullDim_stalk_le_dim (X := ofSpf A) (Spf.pointOfIsMaximal m))

/-- An ordinary scheme, regarded as a formal scheme, has the dimension of its underlying
topological space: the local ring at a point has the dimension of the codimension of the
point (Stacks 02IZ). -/
@[simp]
theorem dim_toFormalScheme (X : Scheme.{u}) : X.toFormalScheme.dim = topologicalKrullDim X := by
  rw [topologicalKrullDim_eq_iSup_coheight]
  exact iSup_congr ringKrullDim_stalk_eq_coheight

end TauCeti.FormalScheme

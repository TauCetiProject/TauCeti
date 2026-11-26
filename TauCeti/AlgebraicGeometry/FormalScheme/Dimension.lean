/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Noetherian
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.KrullDimension

import Mathlib.AlgebraicGeometry.Properties
import TauCeti.Topology.KrullDimension.Basic

/-!
# The dimension of a formal scheme

The dimension of a formal scheme `X` at a point `x` is the Krull dimension of its local ring
`𝒪_{X,x}`, and the dimension `X.dim` of `X` is the supremum of these local dimensions, which is
`⊥` exactly when `X` is empty. Unlike for schemes, this is not the Krull dimension of the
underlying topological space: with the maximal-ideal-adic topology, the formal spectrum of
`ℤ_p⟦t⟧` has a single point, while its ring has dimension `2`.

For a noetherian adic ring `A`, the local ring of `Spf A` at the open prime `𝔭` has the dimension
of `A_𝔭`, the height of `𝔭` (`TauCeti.FormalScheme.Spf.ringKrullDim_stalk_eq_height`), and every
maximal ideal of `A` is open (`TauCeti.FormalScheme.Spf.mem_carrier_of_isMaximal`), so
`dim (Spf A) = dim A`. Applied to the quotient adic rings `A ⧸ 𝔞` (`TauCeti.IsAdicRing.quotient`),
it gives `dim (Spf (A ⧸ 𝔞)) = dim (A ⧸ 𝔞)` for every ideal `𝔞`. For an ordinary scheme, regarded
as a formal scheme, the dimension is the Krull dimension of its underlying space.

On a locally noetherian formal scheme the local dimension does not decrease under specialisation:
in a noetherian chart `Spf A` it is the height of the corresponding open prime. A noetherian formal
scheme has quasi-compact T₀ underlying space, so every point specialises to a closed point, and
the dimension is already the supremum of the local dimensions at the closed points. A formal scheme
has *pure dimension* `d` (`TauCeti.FormalScheme.HasPureDim`) when its local ring at every closed
point has dimension `d`; a nonempty noetherian formal scheme of pure dimension `d` has dimension
`d`. For `Spf A` with `A` noetherian, purity says that every maximal ideal of `A` has height `d`.

## Main definitions

* `TauCeti.FormalScheme.dim`: the supremum of the Krull dimensions of the local rings.
* `TauCeti.FormalScheme.HasPureDim`: the local rings at all closed points have the same
  dimension.

## Main results

* `TauCeti.FormalScheme.dim_eq_bot_iff`: the dimension is `⊥` exactly for the empty formal scheme.
* `TauCeti.FormalScheme.dim_le_of_isOpenImmersion`: an open immersion does not raise dimension.
* `TauCeti.FormalScheme.dim_ofSpf`: `dim (Spf A) = dim A` for a noetherian adic ring `A`.
* `TauCeti.FormalScheme.dim_toFormalScheme`: an ordinary scheme has, as a formal scheme, the
  Krull dimension of its underlying space.
* `TauCeti.FormalScheme.ringKrullDim_stalk_le_of_specializes`: on a locally noetherian formal
  scheme, the local dimension does not decrease under specialisation.
* `TauCeti.FormalScheme.dim_eq_iSup_isClosed`: the dimension of a noetherian formal scheme is the
  supremum of its local dimensions at closed points.
* `TauCeti.FormalScheme.HasPureDim.dim_eq`: a nonempty noetherian formal scheme of pure dimension
  `d` has dimension `d`.
* `TauCeti.FormalScheme.hasPureDim_ofSpf_iff`: `Spf A` has pure dimension `d` exactly when every
  maximal ideal of `A` has height `d`.

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
    (LocallyRingedSpace.IsOpenImmersion.stalkRingEquiv
      (forgetToLocallyRingedSpace.map f) x)).ge.trans (ringKrullDim_stalk_le_dim _)

/-- The dimension of the formal spectrum of a noetherian adic ring `A` is the Krull dimension
of `A`. The local ring at the open prime `𝔭` has the dimension of `A_𝔭`, which is at most
`dim A`, and the supremum is attained at maximal ideals, all of which are open. -/
@[simp]
theorem dim_ofSpf (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsAdicRing A] [IsNoetherianRing A] : (ofSpf A).dim = ringKrullDim A := by
  -- the local rings of `ofSpf A` are those of `Spf A`, by `ofSpf_toLocallyRingedSpace`
  refine le_antisymm (dim_le_iff.mpr fun p ↦ ?_) ((ringKrullDim_le_iff_isMaximal_height_le _).mpr
    fun m hm ↦ ?_)
  · exact (Spf.ringKrullDim_stalk_eq_height p).trans_le Ideal.height_le_ringKrullDim_of_isPrime
  · exact (Spf.ringKrullDim_stalk_eq_height (Spf.pointOfIsMaximal m)).ge.trans
      (ringKrullDim_stalk_le_dim (X := ofSpf A) (Spf.pointOfIsMaximal m))

/-- An ordinary scheme, regarded as a formal scheme, has the dimension of its underlying
topological space: the local ring at a point has the dimension of the codimension of the
point (Stacks 02IZ). -/
@[simp]
theorem dim_toFormalScheme (X : Scheme.{u}) : X.toFormalScheme.dim = topologicalKrullDim X := by
  rw [topologicalKrullDim_eq_iSup_coheight]
  exact iSup_congr ringKrullDim_stalk_eq_coheight

/-! ### Specialisation and closed points -/

/-- On a locally noetherian formal scheme the local dimension does not decrease under
specialisation: if `y` lies in the closure of `x`, then `dim 𝒪_{X,x} ≤ dim 𝒪_{X,y}`. -/
theorem ringKrullDim_stalk_le_of_specializes [X.IsLocallyNoetherian] {x y : X} (h : x ⤳ y) :
    ringKrullDim (X.presheaf.stalk x) ≤ ringKrullDim (X.presheaf.stalk y) := by
  -- a noetherian chart `Spf A` around `y` also contains `x`, and identifies both local rings with
  -- local rings of `Spf A`, whose dimensions are the heights of nested open primes of `A`
  obtain ⟨A, _, _, _, _, _, f, hf, y', rfl⟩ := IsLocallyNoetherian.exists_isNoetherianRing y
  obtain ⟨x', rfl⟩ : x ∈ Set.range f.base := h.mem_open hf.base_open.isOpen_range ⟨y', rfl⟩
  rw [ringKrullDim_eq_of_ringEquiv (LocallyRingedSpace.IsOpenImmersion.stalkRingEquiv f x'),
    ringKrullDim_eq_of_ringEquiv (LocallyRingedSpace.IsOpenImmersion.stalkRingEquiv f y')]
  refine ((Spf.ringKrullDim_stalk_eq_height x').trans_le ?_).trans_eq
    (Spf.ringKrullDim_stalk_eq_height y').symm
  exact_mod_cast Ideal.height_mono <| (PrimeSpectrum.le_iff_specializes _ _).mpr <|
    (subtype_specializes_iff _ _).mp (hf.base_open.isInducing.specializes_iff.mp h)

/-- The dimension of a noetherian formal scheme is the supremum of the dimensions of its local
rings at closed points. -/
theorem dim_eq_iSup_isClosed [X.IsNoetherian] :
    X.dim = ⨆ (x : X) (_ : IsClosed ({x} : Set X)), ringKrullDim (X.presheaf.stalk x) := by
  -- the underlying space is quasi-compact and T₀, so every point specialises to a closed point
  refine le_antisymm (dim_le_iff.mpr fun x ↦ ?_) (iSup₂_le fun x _ ↦ ringKrullDim_stalk_le_dim x)
  obtain ⟨y, hy, hcl⟩ := isClosed_closure.exists_closed_singleton
    ⟨x, subset_closure (Set.mem_singleton x)⟩
  exact (ringKrullDim_stalk_le_of_specializes (specializes_iff_mem_closure.mpr hy)).trans
    (le_iSup₂_of_le y hcl le_rfl)

/-! ### Pure dimension -/

/-- A formal scheme `X` has **pure dimension** `d` if its local ring at every closed point has
Krull dimension `d`. This is the purity of Zhang's Appendix B.1. It concerns the local rings, not
the irreducible components of the underlying space, which for `Spf ℤ_p⟦t⟧` is a single point
although the formal scheme has pure dimension `2`. On a nonempty noetherian formal scheme it
determines `d`, as the dimension of `X` (`TauCeti.FormalScheme.HasPureDim.dim_eq`). -/
structure HasPureDim (X : FormalScheme.{u}) (d : ℕ) : Prop where
  /-- The local ring at every closed point has dimension `d`. -/
  ringKrullDim_stalk_eq (x : X) (hx : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = d

/-- A formal scheme has pure dimension `d` exactly when its local ring at every closed point has
dimension `d`. -/
theorem hasPureDim_iff {d : ℕ} : X.HasPureDim d ↔
    ∀ x : X, IsClosed ({x} : Set X) → ringKrullDim (X.presheaf.stalk x) = d :=
  ⟨fun h ↦ h.ringKrullDim_stalk_eq, fun h ↦ ⟨h⟩⟩

/-- A nonempty noetherian formal scheme of pure dimension `d` has dimension `d`. -/
theorem HasPureDim.dim_eq [X.IsNoetherian] [Nonempty X] {d : ℕ} (h : X.HasPureDim d) :
    X.dim = d := by
  -- the dimension is attained at closed points, and a nonempty quasi-compact T₀ space has one
  obtain ⟨y, -, hy⟩ := isClosed_univ.exists_closed_singleton (Set.univ_nonempty (α := X))
  rw [dim_eq_iSup_isClosed]
  exact le_antisymm (iSup₂_le fun x hx ↦ (h.ringKrullDim_stalk_eq x hx).le)
    ((h.ringKrullDim_stalk_eq y hy).ge.trans (le_iSup₂_of_le y hy le_rfl))

section Spf

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  [IsNoetherianRing A]

/-- The formal spectrum of a noetherian adic ring `A` has pure dimension `d` exactly when every
maximal ideal of `A` has height `d`. -/
@[simp]
theorem hasPureDim_ofSpf_iff {d : ℕ} :
    (ofSpf A).HasPureDim d ↔ ∀ m : Ideal A, m.IsMaximal → m.height = d := by
  -- the closed points of `Spf A` are the maximal ideals of `A`, all of which are open
  have hI := (IsAdicRing.ideal_spec A).2.1
  refine ⟨fun h m hm ↦ ?_, fun h ↦ ⟨fun x hx ↦ ?_⟩⟩
  · have := (Spf.ringKrullDim_stalk_eq_height (Spf.pointOfIsMaximal m)).symm.trans
      (h.ringKrullDim_stalk_eq _ ((Spf.isClosed_singleton_iff_isMaximal hI).mpr hm))
    exact_mod_cast this
  · refine (Spf.ringKrullDim_stalk_eq_height x).trans ?_
    exact_mod_cast h _ ((Spf.isClosed_singleton_iff_isMaximal hI).mp hx)

/-- The formal spectrum of a noetherian local adic ring `A`, such as a complete noetherian local
ring with its maximal-ideal-adic topology, has pure dimension `d` exactly when `A` has Krull
dimension `d`. -/
theorem hasPureDim_ofSpf_iff_of_isLocalRing [IsLocalRing A] {d : ℕ} :
    (ofSpf A).HasPureDim d ↔ ringKrullDim A = d := by
  rw [hasPureDim_ofSpf_iff, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  refine ⟨fun h ↦ by exact_mod_cast h _ (IsLocalRing.maximalIdeal.isMaximal A), fun h m hm ↦ ?_⟩
  rw [IsLocalRing.eq_maximalIdeal hm]
  exact_mod_cast h

end Spf

end TauCeti.FormalScheme

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Stalk
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme
public import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay
public import TauCeti.RingTheory.SerreCondition

/-!
# Cohen–Macaulay schemes and modules

Let `X` be a locally Noetherian scheme. A coherent `𝒪_X`-module `F` is *Cohen–Macaulay* if every
stalk `F_x` is a Cohen–Macaulay module over the local ring `𝒪_{X,x}`, that is, `F_x = 0` or
`depth F_x = dim Supp F_x`; and `X` is *Cohen–Macaulay* if `𝒪_X` is (Stacks, Definition 28.8.1
(02IO)). Equivalently, every local ring `𝒪_{X,x}` is a Cohen–Macaulay ring.

Since a stalk of an affine open `U` is the localization of `Γ(X, U)` at the corresponding prime,
Cohen–Macaulayness of `X` can be read off its affine opens: `X` is Cohen–Macaulay exactly when
every ring of sections `Γ(X, U)` over an affine open is Noetherian and Cohen–Macaulay at every
prime, equivalently satisfies Serre's conditions `(S_n)` for every `n`. In particular `Spec R` is
Cohen–Macaulay exactly when `R` is a Noetherian ring all of whose localizations at primes are
Cohen–Macaulay. Regular schemes are Cohen–Macaulay, since regular local rings are.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.IsCohenMacaulay F`: every stalk of the `𝒪_X`-module `F` is a
  Cohen–Macaulay module over the local ring.
* `AlgebraicGeometry.Scheme.IsCohenMacaulay X`: `X` is locally Noetherian and every local ring of
  `X` is Cohen–Macaulay.

## Main results

* `AlgebraicGeometry.Scheme.isCohenMacaulay_iff_forall_stalk`: the stalkwise characterization.
* `AlgebraicGeometry.Scheme.isCohenMacaulay_iff_isCohenMacaulay_unit`: `X` is Cohen–Macaulay
  exactly when it is locally Noetherian and the `𝒪_X`-module `𝒪_X` is Cohen–Macaulay.
* `AlgebraicGeometry.Scheme.IsCohenMacaulay.of_isOpenImmersion` and
  `AlgebraicGeometry.Scheme.isCohenMacaulay_iff_openCover`: Cohen–Macaulayness is local.
* `AlgebraicGeometry.Scheme.isCohenMacaulay_iff_forall_affineOpens`: the affine-open criterion.
* `AlgebraicGeometry.Scheme.isCohenMacaulay_iff_forall_satisfiesSerreS`: the same criterion with
  Serre's conditions `(S_n)` for all `n`.
* `AlgebraicGeometry.Scheme.isCohenMacaulay_Spec_iff`: the affine case.
* `AlgebraicGeometry.Scheme.IsCohenMacaulay.of_isRegular`: regular schemes are Cohen–Macaulay.

## References

* [Stacks Project, Definition 28.8.1](https://stacks.math.columbia.edu/tag/02IO)
* [Stacks Project, Definition 10.103.12](https://stacks.math.columbia.edu/tag/0AAH)
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

namespace Scheme

namespace Modules

variable {X : Scheme.{u}}

/-- An `𝒪_X`-module `F` is *Cohen–Macaulay* if for every point `x` the stalk `F_x` is a
Cohen–Macaulay module over the local ring `𝒪_{X,x}`: it vanishes, or its depth equals the
dimension of its support. This is meant for coherent modules on a locally Noetherian scheme.
Stacks, Definition 28.8.1 (02IO). -/
@[stacks 02IO]
def IsCohenMacaulay (F : X.Modules) : Prop :=
  ∀ x : X, Module.IsCohenMacaulay (X.presheaf.stalk x) (F.presheaf.stalk x)

/-- Unfolds `AlgebraicGeometry.Scheme.Modules.IsCohenMacaulay`. -/
theorem isCohenMacaulay_iff (F : X.Modules) :
    F.IsCohenMacaulay ↔ ∀ x : X, Module.IsCohenMacaulay (X.presheaf.stalk x) (F.presheaf.stalk x) :=
  Iff.rfl

end Modules

/-- A scheme `X` is *Cohen–Macaulay* if it is locally Noetherian and every local ring `𝒪_{X,x}`
is a Cohen–Macaulay ring. By `AlgebraicGeometry.Scheme.isCohenMacaulay_iff_isCohenMacaulay_unit`
this says that `𝒪_X` is a Cohen–Macaulay `𝒪_X`-module. Stacks, Definition 28.8.1 (02IO). -/
@[stacks 02IO]
class IsCohenMacaulay (X : Scheme.{u}) : Prop extends IsLocallyNoetherian X where
  isCohenMacaulay_stalk :
    ∀ x : X, Module.IsCohenMacaulay (X.presheaf.stalk x) (X.presheaf.stalk x)

variable {X : Scheme.{u}}

/-- A scheme is Cohen–Macaulay exactly when it is locally Noetherian and every local ring is
Cohen–Macaulay. -/
theorem isCohenMacaulay_iff_forall_stalk :
    X.IsCohenMacaulay ↔ IsLocallyNoetherian X ∧
      ∀ x : X, Module.IsCohenMacaulay (X.presheaf.stalk x) (X.presheaf.stalk x) :=
  ⟨fun h ↦ ⟨inferInstance, h.isCohenMacaulay_stalk⟩, fun ⟨_, h⟩ ↦ ⟨h⟩⟩

/-- A scheme is Cohen–Macaulay exactly when it is locally Noetherian and its structure sheaf is a
Cohen–Macaulay module over itself. -/
theorem isCohenMacaulay_iff_isCohenMacaulay_unit :
    X.IsCohenMacaulay ↔ IsLocallyNoetherian X ∧
      Modules.IsCohenMacaulay (X := X) (SheafOfModules.unit X.ringCatSheaf) := by
  rw [isCohenMacaulay_iff_forall_stalk]
  let F : X.Modules := SheafOfModules.unit X.ringCatSheaf
  refine and_congr_right fun _ ↦
    (forall_congr' fun x ↦ ?_).trans (Modules.isCohenMacaulay_iff F).symm
  -- The stalk of `𝒪_X` as an `𝒪_X`-module is free of rank one over `𝒪_{X,x}`.
  exact (Modules.nonempty_linearEquiv_stalk_of_isInvertible F x).some.isCohenMacaulay_iff

/-- An open immersion `f : X ⟶ Y` identifies the local ring of `X` at `x` with the local ring of
`Y` at `f x`, so one is Cohen–Macaulay exactly when the other is. -/
theorem isCohenMacaulay_stalk_iff_of_isOpenImmersion {Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] [IsLocallyNoetherian Y] (x : X) :
    Module.IsCohenMacaulay (Y.presheaf.stalk (f x)) (Y.presheaf.stalk (f x)) ↔
      Module.IsCohenMacaulay (X.presheaf.stalk x) (X.presheaf.stalk x) :=
  (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.isCohenMacaulay_self_iff

/-- The source of an open immersion into a Cohen–Macaulay scheme is Cohen–Macaulay. -/
theorem IsCohenMacaulay.of_isOpenImmersion {Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    [Y.IsCohenMacaulay] : X.IsCohenMacaulay := by
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isOpenImmersion f
  exact ⟨fun x ↦ (isCohenMacaulay_stalk_iff_of_isOpenImmersion f x).mp
    (IsCohenMacaulay.isCohenMacaulay_stalk (f x))⟩

/-- Every open subscheme of a Cohen–Macaulay scheme is Cohen–Macaulay. -/
instance IsCohenMacaulay.opens [X.IsCohenMacaulay] (U : X.Opens) : (U : Scheme).IsCohenMacaulay :=
  .of_isOpenImmersion U.ι

/-- A scheme is Cohen–Macaulay if and only if all members of an open cover are. -/
theorem isCohenMacaulay_iff_openCover (𝒰 : X.OpenCover) :
    X.IsCohenMacaulay ↔ ∀ i, (𝒰.X i).IsCohenMacaulay := by
  refine ⟨fun _ i ↦ .of_isOpenImmersion (𝒰.f i), fun h ↦ ?_⟩
  have : IsLocallyNoetherian X :=
    (isLocallyNoetherian_iff_openCover 𝒰).mpr fun i ↦ (h i).toIsLocallyNoetherian
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨y, hy⟩ := 𝒰.covers x
  rw [← hy, isCohenMacaulay_stalk_iff_of_isOpenImmersion]
  exact IsCohenMacaulay.isCohenMacaulay_stalk y

/-- Let `U` be an affine open with Noetherian ring of sections. The local ring of `X` at a point
of `U` is Cohen–Macaulay exactly when the localization of `Γ(X, U)` at the corresponding prime
is. -/
theorem isCohenMacaulay_stalk_iff_of_isAffineOpen {U : X.Opens} (hU : IsAffineOpen U)
    [IsNoetherianRing Γ(X, U)] (x : U) :
    Module.IsCohenMacaulay (X.presheaf.stalk x) (X.presheaf.stalk x) ↔
      Module.IsCohenMacaulay (Localization.AtPrime (hU.primeIdealOf x).asIdeal)
        (Localization.AtPrime (hU.primeIdealOf x).asIdeal) := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  have := hU.isLocalization_stalk x
  exact IsLocalization.AtPrime.isCohenMacaulay_self_iff _ (X.presheaf.stalk x)

/-- A scheme is Cohen–Macaulay exactly when the ring of sections over every affine open is
Noetherian and its localization at every prime is Cohen–Macaulay. -/
theorem isCohenMacaulay_iff_forall_affineOpens :
    X.IsCohenMacaulay ↔ ∀ U : X.affineOpens, IsNoetherianRing Γ(X, U) ∧
      ∀ (p : Ideal Γ(X, U)) [p.IsPrime],
        Module.IsCohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p) := by
  refine ⟨fun _ U ↦ ⟨IsLocallyNoetherian.component_noetherian U, fun p _ ↦ ?_⟩, fun h ↦ ?_⟩
  · -- The prime `p` is the prime of the point `U.2.fromSpec y` of `U`, whose stalk is `Γ(X, U)_p`.
    have := IsLocallyNoetherian.component_noetherian U
    let y : PrimeSpectrum Γ(X, U) := ⟨p, inferInstance⟩
    have hy : U.2.fromSpec y ∈ (U : X.Opens) := U.2.range_fromSpec.le ⟨y, rfl⟩
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨U.2.fromSpec y, hy⟩
    have : IsLocalization.AtPrime (X.presheaf.stalk (U.2.fromSpec y)) p :=
      U.2.isLocalization_stalk' y hy
    exact (IsLocalization.AtPrime.isCohenMacaulay_self_iff p _).mp
      (IsCohenMacaulay.isCohenMacaulay_stalk (U.2.fromSpec y))
  · have : IsLocallyNoetherian X := ⟨fun U ↦ (h U).1⟩
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
    have := (h ⟨U, hU⟩).1
    exact (isCohenMacaulay_stalk_iff_of_isAffineOpen hU ⟨x, hx⟩).mpr ((h ⟨U, hU⟩).2 _)

/-- The ring of sections over an affine open of a Cohen–Macaulay scheme is Cohen–Macaulay at every
prime. -/
theorem IsCohenMacaulay.isCohenMacaulay_localization [X.IsCohenMacaulay] (U : X.affineOpens)
    (p : Ideal Γ(X, U)) [p.IsPrime] :
    Module.IsCohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p) :=
  have := IsLocallyNoetherian.component_noetherian U
  (isCohenMacaulay_iff_forall_affineOpens.mp inferInstance U).2 p

/-- A scheme is Cohen–Macaulay exactly when the ring of sections over every affine open is
Noetherian and satisfies Serre's condition `(S_n)` for every `n`. -/
theorem isCohenMacaulay_iff_forall_satisfiesSerreS :
    X.IsCohenMacaulay ↔ ∀ U : X.affineOpens, IsNoetherianRing Γ(X, U) ∧
      ∀ n, Module.SatisfiesSerreS n Γ(X, U) Γ(X, U) := by
  rw [isCohenMacaulay_iff_forall_affineOpens]
  refine forall_congr' fun U ↦ and_congr_right fun _ ↦ ?_
  -- `LocalizedModule p.primeCompl Γ(X, U)` is by definition the localization
  -- `Localization.AtPrime p`, an abbreviation for the same Ore localization.
  exact Module.forall_satisfiesSerreS_iff_forall_isCohenMacaulay.symm

/-- The spectrum of a ring `R` is Cohen–Macaulay exactly when `R` is Noetherian and its
localization at every prime is Cohen–Macaulay. Stacks, Definition 10.103.12 (0AAH) on the ring
side. -/
@[simp 1100]
theorem isCohenMacaulay_Spec_iff (R : CommRingCat.{u}) :
    (Spec R).IsCohenMacaulay ↔ IsNoetherianRing R ∧ ∀ (p : Ideal R) [p.IsPrime],
      Module.IsCohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p) := by
  rw [isCohenMacaulay_iff_forall_stalk, isLocallyNoetherian_Spec]
  refine and_congr_right fun _ ↦ ⟨fun h p hp ↦ ?_, fun h x ↦ ?_⟩
  · let x : Spec R := ⟨p, hp⟩
    let : Algebra R ((Spec R).presheaf.stalk x) := StructureSheaf.stalkAlgebra R x
    have : IsLocalization.AtPrime ((Spec R).presheaf.stalk x) p :=
      StructureSheaf.IsLocalization.to_stalk R x
    exact (IsLocalization.AtPrime.isCohenMacaulay_self_iff p _).mp (h x)
  · have : x.asIdeal.IsPrime := x.isPrime
    let : Algebra R ((Spec R).presheaf.stalk x) := StructureSheaf.stalkAlgebra R x
    have : IsLocalization.AtPrime ((Spec R).presheaf.stalk x) x.asIdeal :=
      StructureSheaf.IsLocalization.to_stalk R x
    exact (IsLocalization.AtPrime.isCohenMacaulay_self_iff x.asIdeal _).mpr (h _)

/-- A regular scheme is Cohen–Macaulay, since regular local rings are Cohen–Macaulay. -/
instance IsCohenMacaulay.of_isRegular [TauCeti.AlgebraicGeometry.IsRegular X] :
    X.IsCohenMacaulay :=
  ⟨fun _ ↦ TauCeti.IsRegularLocalRing.isCohenMacaulay⟩

end Scheme

end AlgebraicGeometry

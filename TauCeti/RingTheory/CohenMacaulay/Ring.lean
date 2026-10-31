/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.SerreCondition.Basic
import TauCeti.RingTheory.Localization.LocalizationLocalization
import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay

/-!
# Cohen–Macaulay rings

A commutative ring is Cohen–Macaulay if it is Noetherian and its localization at every prime
is Cohen–Macaulay as a module over itself. It suffices to test maximal ideals; for a local
ring this agrees with the module-theoretic definition. These criteria use localization of
Cohen–Macaulay modules, rather than imposing a common dimension on the components.

The predicate is invariant under ring isomorphisms and passes to arbitrary localizations.
It is also equivalent, for Noetherian rings, to satisfying all of Serre's conditions `(S_n)`.
This gives the ring-theoretic interface for the affine-local definition on schemes.

## References

* Stacks Project, Definition 10.103.12 (Tag 0AAH).
* Stacks Project, Lemma 10.103.11 (Tag 0AAG).
-/

public section

universe u v

namespace TauCeti.Ring

/-- A commutative ring is *Cohen–Macaulay* if it is Noetherian and its localization at every
prime is Cohen–Macaulay over itself. Stacks, Definition 10.103.12 (0AAH). -/
@[stacks 0AAH]
class IsCohenMacaulay (R : Type u) [CommRing R] : Prop extends IsNoetherianRing R where
  isCohenMacaulay_localization (p : Ideal R) [p.IsPrime] :
    Module.IsCohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p)

variable {R : Type u} [CommRing R]

/-- Cohen–Macaulayness includes Noetherianity and the local condition at every prime. -/
theorem isCohenMacaulay_iff :
    IsCohenMacaulay R ↔ IsNoetherianRing R ∧ ∀ (p : Ideal R) [p.IsPrime],
      Module.IsCohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p) :=
  ⟨fun h ↦ ⟨inferInstance, h.isCohenMacaulay_localization⟩, fun ⟨_, h⟩ ↦ ⟨h⟩⟩

/-- A Noetherian ring is Cohen–Macaulay exactly when all its prime localizations are. -/
theorem isCohenMacaulay_iff_forall_localization [IsNoetherianRing R] :
    IsCohenMacaulay R ↔ ∀ (p : Ideal R) [p.IsPrime],
      Module.IsCohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p) := by
  rw [isCohenMacaulay_iff, and_iff_right (inferInstance : IsNoetherianRing R)]

/-- A Noetherian ring is Cohen–Macaulay exactly when it satisfies `(S_n)` for every `n`. -/
theorem isCohenMacaulay_iff_forall_satisfiesSerreS [IsNoetherianRing R] :
    IsCohenMacaulay R ↔ ∀ n, Module.SatisfiesSerreS n R R := by
  rw [isCohenMacaulay_iff_forall_localization]
  refine Iff.trans ?_
    (Module.forall_satisfiesSerreS_iff_forall_isCohenMacaulay (R := R) (M := R)).symm
  refine forall_congr' fun p ↦ forall_congr' fun _ ↦ ?_
  let e : LocalizedModule p.primeCompl R ≃ₗ[Localization.AtPrime p] Localization.AtPrime p :=
    (IsLocalizedModule.iso p.primeCompl (Algebra.linearMap R (Localization.AtPrime p))
      ).extendScalarsOfIsLocalization p.primeCompl _
  exact e.isCohenMacaulay_iff.symm

/-- Over a Noetherian local ring, the ring and module definitions of Cohen–Macaulayness agree. -/
theorem isCohenMacaulay_iff_of_isLocalRing [IsLocalRing R] [IsNoetherianRing R] :
    IsCohenMacaulay R ↔ Module.IsCohenMacaulay R R := by
  constructor
  · intro h
    let e : R ≃ₐ[R] Localization.AtPrime (IsLocalRing.maximalIdeal R) :=
      IsLocalization.atUnits R (IsLocalRing.maximalIdeal R).primeCompl
        (fun x ↦ by simpa using! fun a ↦ a)
    exact e.toRingEquiv.isCohenMacaulay_self_iff.mpr
      (h.isCohenMacaulay_localization _)
  · intro h
    exact isCohenMacaulay_iff_forall_satisfiesSerreS.mpr fun _ ↦ h.satisfiesSerreS

/-- For a Noetherian ring it suffices to test Cohen–Macaulayness at maximal ideals. -/
theorem isCohenMacaulay_iff_forall_isMaximal [IsNoetherianRing R] :
    IsCohenMacaulay R ↔ ∀ (m : Ideal R) [m.IsMaximal],
      Module.IsCohenMacaulay (Localization.AtPrime m) (Localization.AtPrime m) := by
  refine ⟨fun h m _ ↦ h.isCohenMacaulay_localization m,
    fun h ↦ isCohenMacaulay_iff_forall_localization.mpr ?_⟩
  intro p hp
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hp.ne_top
  have := hm
  obtain ⟨P, hP, -, ⟨e⟩⟩ := IsLocalization.exists_ringEquiv_localization_atPrime
    m.primeCompl (Localization.AtPrime m) p (Set.disjoint_left.mpr fun x hx hxp ↦ hx (hpm hxp))
  have := hP
  have hlocal := isCohenMacaulay_iff_of_isLocalRing.mpr (h m)
  exact e.isCohenMacaulay_self_iff.mpr (hlocal.isCohenMacaulay_localization P)

/-- Cohen–Macaulayness is preserved by a ring isomorphism. -/
theorem _root_.RingEquiv.isCohenMacaulay {S : Type v} [CommRing S]
    (e : R ≃+* S) [IsCohenMacaulay R] : IsCohenMacaulay S := by
  have := isNoetherianRing_of_ringEquiv R e
  refine isCohenMacaulay_iff_forall_localization.mpr fun p _ ↦ ?_
  let e' : Localization.AtPrime (p.comap e) ≃+* Localization.AtPrime p :=
    IsLocalization.ringEquivOfRingEquiv _ _ e (e.map_primeCompl_comap_eq p)
  exact e'.isCohenMacaulay_self_iff.mp (IsCohenMacaulay.isCohenMacaulay_localization _)

/-- Cohen–Macaulayness is invariant under ring isomorphisms. -/
theorem _root_.RingEquiv.isCohenMacaulay_iff {S : Type v} [CommRing S]
    (e : R ≃+* S) : IsCohenMacaulay R ↔ IsCohenMacaulay S :=
  ⟨fun _ ↦ e.isCohenMacaulay, fun _ ↦ e.symm.isCohenMacaulay⟩

/-- Every localization of a Cohen–Macaulay ring is Cohen–Macaulay. -/
theorem IsCohenMacaulay.of_isLocalization [IsCohenMacaulay R]
    (M : Submonoid R) (S : Type v) [CommRing S] [Algebra R S] [IsLocalization M S] :
    IsCohenMacaulay S := by
  have := IsLocalization.isNoetherianRing M S inferInstance
  refine isCohenMacaulay_iff_forall_localization.mpr fun Q _ ↦ ?_
  let P := Q.comap (algebraMap R S)
  have : IsLocalization.AtPrime (Localization.AtPrime Q) P :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M _ Q
  exact (IsLocalization.AtPrime.isCohenMacaulay_self_iff P (Localization.AtPrime Q)).mpr
    (IsCohenMacaulay.isCohenMacaulay_localization P)

/-- The canonical localization of a Cohen–Macaulay ring is Cohen–Macaulay. -/
instance IsCohenMacaulay.localization [IsCohenMacaulay R] (M : Submonoid R) :
    IsCohenMacaulay (Localization M) :=
  IsCohenMacaulay.of_isLocalization M _

/-- Regular rings are Cohen–Macaulay. -/
instance (priority := low) IsCohenMacaulay.of_isRegularRing [IsRegularRing R] :
    IsCohenMacaulay R where
  isCohenMacaulay_localization _ := TauCeti.IsRegularLocalRing.isCohenMacaulay

/-- A Noetherian ring of dimension zero is Cohen–Macaulay, even when it is nonreduced. -/
theorem IsCohenMacaulay.of_krullDimLE_zero [IsNoetherianRing R] [Ring.KrullDimLE 0 R] :
    IsCohenMacaulay R where
  isCohenMacaulay_localization p _ := by
    have := Ring.KrullDimLE.of_isLocalization p
      (Ideal.mem_minimalPrimes_iff_isPrime.mpr inferInstance) (Localization.AtPrime p)
    exact Module.isCohenMacaulay_of_krullDimLE_zero

end TauCeti.Ring

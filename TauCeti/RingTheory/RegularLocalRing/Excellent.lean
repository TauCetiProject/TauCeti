/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.RegularLocalRing.GRing
public import TauCeti.RingTheory.RegularLocalRing.J2
public import TauCeti.RingTheory.UniversallyCatenary
import TauCeti.RingTheory.RegularLocalRing.Catenary

/-!
# Quasi-excellent and excellent rings

A ring is *quasi-excellent* if it is a G-ring (`TauCeti.Excellence.IsGRing`: Noetherian with
geometrically regular formal fibres) and J-2 (`TauCeti.Excellence.IsJ2`: every algebra of finite
type has open regular locus). It is *excellent* if moreover it is universally catenary
(`TauCeti.Excellence.IsUniversallyCatenary`). Stacks, Definition 15.53.1. Quasi-excellence is the
hypothesis under which normalizations of reduced schemes of finite type are finite; excellence adds
the dimension theory of catenary rings.

Both conditions pass to localizations and are invariant under ring isomorphisms. Perfect fields are
excellent: they are Artinian, hence G-rings, J-2 by `TauCeti.Excellence.IsJ2.of_perfectField`, and
regular, hence universally catenary.

## Main definitions and results

* `TauCeti.Excellence.IsQuasiExcellentRing R`: `R` is a G-ring and J-2.
* `TauCeti.Excellence.IsExcellentRing R`: `R` is quasi-excellent and universally catenary.
* `TauCeti.Excellence.IsQuasiExcellentRing.of_isLocalization`,
  `TauCeti.Excellence.IsExcellentRing.of_isLocalization`: localizations of quasi-excellent,
  respectively excellent, rings are quasi-excellent, respectively excellent.
* `TauCeti.Excellence.IsExcellentRing.of_perfectField`: a perfect field is excellent.

## References

* The Stacks Project, Section 15.53 (*Excellent rings*), Definition 15.53.1.
-/

public section

universe u v

namespace TauCeti.Excellence

/-- A ring `R` is *quasi-excellent* if it is a G-ring and J-2: it is Noetherian, its formal fibres
are geometrically regular, and every `R`-algebra of finite type has open regular locus. No
catenarity is required. Stacks, Definition 15.53.1 (1). -/
class IsQuasiExcellentRing (R : Type u) [CommRing R] : Prop extends IsGRing R, IsJ2 R

/-- A ring `R` is *excellent* if it is quasi-excellent and universally catenary.
Stacks, Definition 15.53.1 (2). -/
class IsExcellentRing (R : Type u) [CommRing R] : Prop extends IsQuasiExcellentRing R,
    IsUniversallyCatenary R

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace IsQuasiExcellentRing

/-- Being quasi-excellent is invariant under ring isomorphisms. -/
theorem of_ringEquiv [IsQuasiExcellentRing R] (e : R ≃+* S) : IsQuasiExcellentRing S where
  __ := IsGRing.of_ringEquiv e
  __ := e.isJ2

/-- A localization of a quasi-excellent ring is quasi-excellent. -/
theorem of_isLocalization [Algebra R S] [IsQuasiExcellentRing R] (M : Submonoid R)
    [IsLocalization M S] : IsQuasiExcellentRing S where
  __ := IsGRing.of_isLocalization (S := S) M
  __ := M.isJ2_of_isLocalization (S := S)

/-- The localization `Localization M` of a quasi-excellent ring is quasi-excellent. -/
instance localization [IsQuasiExcellentRing R] (M : Submonoid R) :
    IsQuasiExcellentRing (Localization M) :=
  of_isLocalization M

end IsQuasiExcellentRing

namespace IsExcellentRing

/-- Being excellent is invariant under ring isomorphisms. -/
theorem of_ringEquiv [IsExcellentRing R] (e : R ≃+* S) : IsExcellentRing S where
  __ := IsQuasiExcellentRing.of_ringEquiv e
  __ := e.isUniversallyCatenary

/-- A localization of an excellent ring is excellent. -/
theorem of_isLocalization [Algebra R S] [IsExcellentRing R] (M : Submonoid R)
    [IsLocalization M S] : IsExcellentRing S where
  __ := IsQuasiExcellentRing.of_isLocalization (S := S) M
  __ := M.isUniversallyCatenary_of_isLocalization (S := S)

/-- The localization `Localization M` of an excellent ring is excellent. -/
instance localization [IsExcellentRing R] (M : Submonoid R) : IsExcellentRing (Localization M) :=
  of_isLocalization M

/-- A perfect field is excellent: it is Artinian, hence a G-ring; it is J-2; and it is regular,
hence universally catenary. -/
instance of_perfectField (k : Type u) [Field k] [PerfectField k] : IsExcellentRing k where
  __ : IsGRing k := inferInstance
  __ : IsJ2 k := inferInstance
  __ : IsUniversallyCatenary k := inferInstance

end IsExcellentRing

/-! ### Checks -/

/-- The rationals are excellent. -/
example : IsExcellentRing ℚ := inferInstance

/-- A finite field is quasi-excellent. -/
example (k : Type u) [Field k] [Finite k] : IsQuasiExcellentRing k := inferInstance

/-- A localization of an excellent ring is a G-ring, J-2 and universally catenary. -/
example [IsExcellentRing R] (M : Submonoid R) :
    IsGRing (Localization M) ∧ IsJ2 (Localization M) ∧ IsUniversallyCatenary (Localization M) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end TauCeti.Excellence

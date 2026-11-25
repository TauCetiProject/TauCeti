/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Basic
public import TauCeti.RingTheory.LocalRing.Pullback

/-!
# Witt vectors of pullbacks

Witt vectors are computed coordinatewise, so they commute with pullbacks: for ring homomorphisms
`f : R →+* T` and `g : S →+* T`, the Witt vectors of the two projections of the pullback
`R ×_T S` (`RingHom.pullback`) give a ring isomorphism
`W(R ×_T S) ≃+* W(R) ×_{W(T)} W(S)`, under which the `n`-th Witt coordinate of a Witt vector of
pairs is the pair of `n`-th Witt coordinates.

## Main definitions

* `WittVector.pullbackEquiv`:
  `WittVector p (f.pullback g) ≃+* (WittVector.map f).pullback (WittVector.map g)`.

## Main results

* `WittVector.coe_pullbackEquiv`, `WittVector.coe_coeff_pullbackEquiv_symm`: the isomorphism and
  its inverse in terms of the projections and of Witt coordinates.
-/

public section

namespace WittVector

variable (p : ℕ) [Fact p.Prime] {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  (f : R →+* T) (g : S →+* T)

/-- **Witt vectors commute with pullbacks**: `W(R ×_T S) ≃+* W(R) ×_{W(T)} W(S)`, by the Witt
vectors of the two projections; Witt coordinates are taken componentwise. -/
noncomputable def pullbackEquiv :
    WittVector p (f.pullback g) ≃+* (map (p := p) f).pullback (map g) :=
  RingEquiv.ofBijective
    (((map (f.pullbackFst g)).prod (map (f.pullbackSnd g))).codRestrict _ fun w ↦ by
      refine RingHom.mem_pullback.mpr (ext fun n ↦ ?_)
      simp only [RingHom.prod_apply, map_coeff]
      exact RingHom.mem_pullback.mp (w.coeff n).property) <| by
    refine ⟨fun x y hxy ↦ ext fun n ↦ Subtype.ext (Prod.ext ?_ ?_), fun y ↦ ?_⟩
    · simpa [map_coeff] using congr((($hxy : WittVector p R × WittVector p S).1).coeff n)
    · simpa [map_coeff] using congr((($hxy : WittVector p R × WittVector p S).2).coeff n)
    · have hy := RingHom.mem_pullback.mp y.property
      refine ⟨mk p fun n ↦ ⟨((y : WittVector p R × WittVector p S).1.coeff n,
        (y : WittVector p R × WittVector p S).2.coeff n), ?_⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
      · simpa [map_coeff] using congr(($hy).coeff n)
      all_goals exact ext fun n ↦ by simp [map_coeff]

variable {p f g}

/-- The image of `w` under `WittVector.pullbackEquiv` is the pair of its images under the Witt
vectors of the two projections. -/
@[simp]
theorem coe_pullbackEquiv (w : WittVector p (f.pullback g)) :
    (pullbackEquiv p f g w : WittVector p R × WittVector p S) =
      (map (f.pullbackFst g) w, map (f.pullbackSnd g) w) :=
  (rfl)

/-- The Witt coordinates of `(pullbackEquiv p f g).symm y` are the pairs of Witt coordinates of the
two components of `y`. -/
@[simp]
theorem coe_coeff_pullbackEquiv_symm (y : (map (p := p) f).pullback (map g)) (n : ℕ) :
    (((pullbackEquiv p f g).symm y).coeff n : R × S) =
      ((y : WittVector p R × WittVector p S).1.coeff n,
        (y : WittVector p R × WittVector p S).2.coeff n) := by
  obtain ⟨w, rfl⟩ := (pullbackEquiv p f g).surjective y
  simp [map_coeff]

end WittVector

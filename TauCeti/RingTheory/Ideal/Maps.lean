/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Maps

/-!
# Images of ideals under a surjective ring homomorphism

Let `π : R →+* S` be a surjective ring homomorphism of commutative rings, and let `I` and `J` be
ideals of `R` that both contain `RingHom.ker π`. Such ideals are determined by their image in `S`:
if `I.map π = J.map π`, then `I = J`.

The image decides an ideal only up to what is added to it inside the kernel, and an ideal that
already contains the kernel has nothing left to add, which is why the image suffices. This is
what makes a presentation of a ring by a quotient determine the ideals lying above it: two ideals
containing the kernel of the quotient map, the same maximal ideal written in two presentations
for instance, are equal as soon as they have the same image there.

Mathlib states the comparison in the form `Ideal.map_eq_iff_sup_ker_eq_of_surjective`, which
compares `I ⊔ RingHom.ker π` with `J ⊔ RingHom.ker π`. The result here is that comparison with the
kernel already contained in both ideals, so that each of the two suprema is the ideal itself.

## Main results

* `TauCeti.Ideal.eq_of_map_eq_of_le_ker`: two ideals containing the kernel of a surjective ring
  homomorphism, and with equal images, are equal.

## References

* `Mathlib.RingTheory.Ideal.Maps`: `Ideal.map_eq_iff_sup_ker_eq_of_surjective`, the comparison of
  the suprema with the kernel that the statement here specialises, and
  `Ideal.comap_injective_of_surjective`, which compares two ideals through their inverse images.
-/

public section

namespace TauCeti.Ideal

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

/-- **The image of a surjective ring homomorphism determines an ideal that contains the kernel.**
If `π : R →+* S` is surjective and two ideals `I` and `J` of `R` both contain `RingHom.ker π`,
then `I = J` as soon as their images agree: `Ideal.map_eq_iff_sup_ker_eq_of_surjective` compares
`I ⊔ RingHom.ker π` with `J ⊔ RingHom.ker π`, and each of those ideals is the ideal itself. -/
theorem eq_of_map_eq_of_le_ker (π : R →+* S) (hπ : Function.Surjective π) {I J : Ideal R}
    (hIJ : I.map π = J.map π) (hI : RingHom.ker π ≤ I) (hJ : RingHom.ker π ≤ J) : I = J := by
  have h1 : I = I ⊔ RingHom.ker π := (sup_eq_left.mpr hI).symm
  have h2 : J = J ⊔ RingHom.ker π := (sup_eq_left.mpr hJ).symm
  rw [h1, h2]
  exact (Ideal.map_eq_iff_sup_ker_eq_of_surjective π hπ).mp hIJ

end TauCeti.Ideal

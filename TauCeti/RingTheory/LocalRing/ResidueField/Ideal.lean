/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Functoriality of the residue field at a prime ideal

For ring maps `f : R → S` and `g : S → T` and primes `P`, `Q`, `Q'` of `R`, `S`, `T` lying over
one another, the maps `κ(P) → κ(Q) → κ(Q')` of Mathlib's `Ideal.ResidueField.map` compose to the
map `κ(P) → κ(Q')` induced by `g ∘ f`. Thus residue fields are preserved along a composite when
they are preserved along each step, as for a tower of étale neighbourhoods that do not extend the
residue field at a point.

## Main results

* `Ideal.ResidueField.map_comp_map`: the residue field maps of `f` and `g` compose to that of
  `g ∘ f`.
-/

public section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- The residue field maps `κ(P) → κ(Q)` along `f` and `κ(Q) → κ(Q')` along `g` compose to the
residue field map `κ(P) → κ(Q')` along `g ∘ f`. -/
theorem Ideal.ResidueField.map_comp_map (P : Ideal R) (Q : Ideal S) (Q' : Ideal T) [P.IsPrime]
    [Q.IsPrime] [Q'.IsPrime] (f : R →+* S) (g : S →+* T) (hf : P = Q.comap f)
    (hg : Q = Q'.comap g) :
    (Ideal.ResidueField.map Q Q' g hg).comp (Ideal.ResidueField.map P Q f hf) =
      Ideal.ResidueField.map P Q' (g.comp f) (by rw [hf, hg, Ideal.comap_comap]) :=
  Ideal.ResidueField.ringHom_ext <| RingHom.ext fun r ↦ by
    simp [Ideal.ResidueField.map_algebraMap]

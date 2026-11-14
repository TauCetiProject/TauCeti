/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Abelian
import TauCeti.Algebra.Algebra.Equiv

/-!
# Transporting abelian Galois extensions along ring equivalences

Mathlib's `IsGalois.of_equiv_equiv` transports the Galois property along a commuting square of
ring equivalences `(f : K ≃+* K', g : L ≃+* L')`. Conjugation by `(f, g)` also identifies the
automorphism groups `Gal(L/K)` and `Gal(L'/K')` as groups (`RingEquiv.algAutCongr`), so
commutativity of the Galois group transports across the same square.

## Main results

* `IsAbelianGalois.of_equiv_equiv`: if `L/K` is abelian Galois, then so is `L'/K'` along any
  compatible pair of ring equivalences.
* `IsAbelianGalois.iff_of_equiv_equiv`: equivalence of `IsAbelianGalois` across a commuting square
  of ring equivalences.
-/

public section

namespace IsAbelianGalois

variable {K L K' L' : Type*} [Field K] [Field L] [Algebra K L]
  [Field K'] [Field L'] [Algebra K' L']

/-- **Abelian Galois extensions transport along compatible ring equivalences.** Given ring
isomorphisms `f : K ≃+* K'` and `g : L ≃+* L'` commuting with `algebraMap`, if `L/K` is abelian
Galois then so is `L'/K'`. -/
theorem of_equiv_equiv [IsAbelianGalois K L] (f : K ≃+* K') (g : L ≃+* L')
    (hcomp : (algebraMap K' L').comp (f : K →+* K') = (g : L →+* L').comp (algebraMap K L)) :
    IsAbelianGalois K' L' :=
  have := IsGalois.of_equiv_equiv (f := f) (g := g) hcomp
  have := (RingEquiv.algAutCongr f g fun c ↦ (RingHom.congr_fun hcomp c).symm)
    |>.surjective.isMulCommutative
  {}

/-- **Abelian Galoisness is invariant under compatible ring equivalences.** -/
theorem iff_of_equiv_equiv (f : K ≃+* K') (g : L ≃+* L')
    (hcomp : (algebraMap K' L').comp (f : K →+* K') = (g : L →+* L').comp (algebraMap K L)) :
    IsAbelianGalois K L ↔ IsAbelianGalois K' L' :=
  ⟨fun _ ↦ of_equiv_equiv f g hcomp,
    fun _ ↦ of_equiv_equiv f.symm g.symm <| RingHom.ext fun x ↦
      g.eq_symm_apply.mpr <| by simpa using (RingHom.congr_fun hcomp (f.symm x)).symm⟩

end IsAbelianGalois

end

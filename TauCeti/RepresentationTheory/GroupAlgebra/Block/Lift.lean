/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.CenterMap
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Basic
import TauCeti.RingTheory.Henselian.Integral

/-!
# Lifting blocks from `k[G]` to `O[G]`

Let `O` be a commutative ring, Henselian along an ideal `I`, let `π : O → k` be a surjective ring
homomorphism with kernel `I`, and let `G` be a finite group. The typical case is a complete
discrete valuation ring `O`, such as `ℤ_p`, with its residue field `k`: a ring complete for the
`I`-adic topology is Henselian along `I`. Reduction of coefficients maps the centre `Z(O[G])` onto
the centre `Z(k[G])`, with kernel `I Z(O[G])` (`TauCeti.centerMapRingHom_surjective`,
`TauCeti.ker_centerMapRingHom`). The centre `Z(O[G])` is a finite `O`-algebra, spanned by the class
sums, so it is Henselian along `I Z(O[G])`. Since `Z(O[G])` is commutative, reduction is therefore a
bijection from the idempotents of `Z(O[G])` onto those of `Z(k[G])`: every central idempotent of
`k[G]` has exactly one central idempotent lift to `O[G]`.

A bijection on idempotents of commutative rings preserves and reflects primitivity, so reduction
is also a bijection from the block idempotents of `O[G]` onto those of `k[G]`: every block of
`k[G]` is the reduction of exactly one block of `O[G]`. Over `O = ℤ₂`, the blocks `1 + r + r²` and
`r + r²` of `𝔽₂[C₃]` lift to the blocks `(1 + r + r²)/3` and `(2 - r - r²)/3` of `ℤ₂[C₃]`, where
`3` is a unit. The ordinary idempotents `(1 ± t)/2` of `ℚ₂[C₂]` are not in `ℤ₂[C₂]`, whose only
block is `1`, matching the single block of `𝔽₂[C₂]`.

## Main results

* `TauCeti.bijOn_centerMapRingHom_isIdempotentElem`: reduction is a bijection from the central
  idempotents of `O[G]` onto those of `k[G]`.
* `TauCeti.isBlockIdempotent_centerMapRingHom_iff`: a central idempotent of `O[G]` is a block
  idempotent exactly when its reduction is.
* `TauCeti.bijOn_centerMapRingHom_isBlockIdempotent`: reduction is a bijection from the block
  idempotents of `O[G]` onto those of `k[G]`.
* `TauCeti.existsUnique_blockIdempotent_map_residue`: over a Henselian local ring `O`, every block
  idempotent of `k[G]`, for `k` the residue field, is the reduction of exactly one block idempotent
  of `O[G]`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Proposition 9.4.3, p. 149, and
  §12.1, p. 227.
-/

public section

namespace TauCeti

open MonoidAlgebra

variable {O k G : Type*} [CommRing O] [CommRing k] [Group G] [Finite G] (I : Ideal O)
  [HenselianRing O I] {π : O →+* k}

/-- **Central idempotents lift uniquely.** If `O` is Henselian along `I` and `π : O →+* k` is
surjective with kernel `I`, reduction of coefficients is a bijection from the idempotents of the
centre of `O[G]` onto those of the centre of `k[G]`. -/
theorem bijOn_centerMapRingHom_isIdempotentElem (hπ : Function.Surjective π)
    (hker : RingHom.ker π = I) :
    Set.BijOn (centerMapRingHom G π) {e | IsIdempotentElem e} {t | IsIdempotentElem t} := by
  -- The centre is a finite `O`-algebra, so it is Henselian along the extension of `I`, which is
  -- the kernel of reduction.
  have := Ideal.henselianRing_map_of_isIntegral I (S := Subalgebra.center O (MonoidAlgebra O G))
  exact HenselianRing.bijOn_isIdempotentElem_of_surjective _ (centerMapRingHom_surjective hπ) _
    (by rw [ker_centerMapRingHom, hker])

/-- **Blocks are detected after reduction.** A central idempotent of `O[G]` is a block idempotent
exactly when its reduction is a block idempotent of `k[G]`. -/
theorem isBlockIdempotent_centerMapRingHom_iff (hπ : Function.Surjective π)
    (hker : RingHom.ker π = I) {b : Subalgebra.center O (MonoidAlgebra O G)}
    (hb : IsIdempotentElem b) :
    IsBlockIdempotent (centerMapRingHom G π b) ↔ IsBlockIdempotent b :=
  isPrimitiveIdempotent_map_iff_of_bijOn (centerMapRingHom G π)
    (bijOn_centerMapRingHom_isIdempotentElem I hπ hker) hb

/-- **Blocks of `O[G]` and of `k[G]` correspond.** If `O` is Henselian along `I` and
`π : O →+* k` is surjective with kernel `I`, reduction of coefficients is a bijection from the
block idempotents of `O[G]` onto those of `k[G]`. -/
theorem bijOn_centerMapRingHom_isBlockIdempotent (hπ : Function.Surjective π)
    (hker : RingHom.ker π = I) :
    Set.BijOn (centerMapRingHom G π) {b | IsBlockIdempotent b} {c | IsBlockIdempotent c} := by
  have h := bijOn_centerMapRingHom_isIdempotentElem (G := G) I hπ hker
  refine ⟨fun b hb ↦ (isBlockIdempotent_centerMapRingHom_iff I hπ hker
      hb.isIdempotentElem).mpr hb, fun b hb b' hb' ↦
    h.injOn hb.isIdempotentElem hb'.isIdempotentElem, fun c hc ↦ ?_⟩
  obtain ⟨b, hb, rfl⟩ := h.surjOn hc.isIdempotentElem
  exact ⟨b, (isBlockIdempotent_centerMapRingHom_iff I hπ hker hb).mp hc, rfl⟩

/-- **Blocks of `O[G]` and of `k[G]` correspond.** For a Henselian local ring `O`, for instance a
complete discrete valuation ring, with residue field `k`, every block idempotent of `k[G]` is the
reduction of exactly one block idempotent of `O[G]`. -/
theorem existsUnique_blockIdempotent_map_residue [IsLocalRing O]
    [HenselianRing O (IsLocalRing.maximalIdeal O)]
    (c : Subalgebra.center (IsLocalRing.ResidueField O)
      (MonoidAlgebra (IsLocalRing.ResidueField O) G))
    (hc : IsBlockIdempotent c) :
    ∃! b : Subalgebra.center O (MonoidAlgebra O G), IsBlockIdempotent b ∧
      mapRingHom G (IsLocalRing.residue O) (b : MonoidAlgebra O G) =
        (c : MonoidAlgebra (IsLocalRing.ResidueField O) G) := by
  have h := bijOn_centerMapRingHom_isBlockIdempotent (G := G) _ IsLocalRing.residue_surjective
    (IsLocalRing.ker_residue (R := O))
  obtain ⟨b, hb, rfl⟩ := h.surjOn hc
  refine ⟨b, ⟨hb, (coe_centerMapRingHom G _ b).symm⟩, fun b' ⟨hb', hb'c⟩ ↦ h.injOn hb' hb ?_⟩
  rw [Subtype.ext_iff, coe_centerMapRingHom, hb'c]

end TauCeti

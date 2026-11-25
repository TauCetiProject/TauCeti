/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Cyclotomic.Completion
public import TauCeti.RepresentationTheory.Induction.Cyclotomic.SplittingField

/-!
# The completion of a cyclotomic field splits every group of exponent dividing `e`

Let `F = ℚ⟮complexRoot e⟯ ⊆ ℂ` and let `v` be a finite place of `F`. The completion `F_v` has
characteristic zero and contains the primitive `e`-th root of unity `complexRoot e`
(`TauCeti.Cyclotomic.isPrimitiveRoot_embedding_zeta`). So, for every finite group `H` whose
exponent divides `e`, and every algebraically closed extension `L` of `F_v`, every simple
representation of `H` over `L` is the scalar extension of an absolutely irreducible
representation of `H` over `F_v` (`FDRep.exists_simple_nonempty_iso_baseChange_of_isPrimitiveRoot`):
`F_v` is a splitting field for `H`. For a finite group `G` with `exponent G ∣ e` this applies to
every subgroup of `G`, at every place `v`, with the same root of unity, so the `p`-modular system
`(F_v, O_v, k_v)` at a place over `p` is a splitting system for every subgroup of `G`.

## Main results

* `TauCeti.Cyclotomic.exists_simple_nonempty_iso_baseChange_adicCompletion`: `F_v` splits every
  finite group of exponent dividing `e`.
* `TauCeti.Cyclotomic.exists_simple_nonempty_iso_baseChange_adicCompletion_subgroup`: `F_v` splits
  every subgroup of a finite group of exponent dividing `e`.

## References

* Peter Webb, *A Course in Finite Group Representation Theory*, Section 9.4, p. 148.
* J.-P. Serre, *Linear Representations of Finite Groups* (1977), Section 12.3.
-/

public section

open IsDedekindDomain NumberField

namespace TauCeti.Cyclotomic

variable {e : ℕ} [NeZero e] (v : HeightOneSpectrum (𝓞 (complexField e)))
  {L : Type} [Field L] [IsAlgClosed L] [Algebra (v.adicCompletion (complexField e)) L]

/-- **The completion of `ℚ(ζ_e)` at a finite place splits every group of exponent dividing `e`.**
Every simple representation `W` of a finite group `H` with `exponent H ∣ e` over an algebraically
closed extension `L` of `F_v` is the scalar extension of an absolutely irreducible representation
of `H` over `F_v`. -/
theorem exists_simple_nonempty_iso_baseChange_adicCompletion {H : Type*} [Group H] [Finite H]
    (hH : Monoid.exponent H ∣ e) (W : FDRep L H) [CategoryTheory.Simple W] :
    ∃ V : FDRep (v.adicCompletion (complexField e)) H, CategoryTheory.Simple V ∧
      Module.finrank (v.adicCompletion (complexField e)) (V ⟶ V) = 1 ∧
        Nonempty (FDRep.of (Representation.baseChange L V.ρ) ≅ W) :=
  W.exists_simple_nonempty_iso_baseChange_of_isPrimitiveRoot (isPrimitiveRoot_embedding_zeta v) hH

/-- **The completion of `ℚ(ζ_e)` at a finite place splits every subgroup.** For a finite group
`G` with `exponent G ∣ e` and a subgroup `H ≤ G`, every simple representation of `H` over an
algebraically closed extension `L` of `F_v` is the scalar extension of an absolutely irreducible
representation of `H` over `F_v`. -/
theorem exists_simple_nonempty_iso_baseChange_adicCompletion_subgroup {G : Type*} [Group G]
    [Finite G] (hG : Monoid.exponent G ∣ e) (H : Subgroup G) (W : FDRep L H)
    [CategoryTheory.Simple W] :
    ∃ V : FDRep (v.adicCompletion (complexField e)) H, CategoryTheory.Simple V ∧
      Module.finrank (v.adicCompletion (complexField e)) (V ⟶ V) = 1 ∧
        Nonempty (FDRep.of (Representation.baseChange L V.ρ) ≅ W) :=
  exists_simple_nonempty_iso_baseChange_adicCompletion v
    ((Monoid.exponent_dvd_of_monoidHom H.subtype H.subtype_injective).trans hG) W

end TauCeti.Cyclotomic

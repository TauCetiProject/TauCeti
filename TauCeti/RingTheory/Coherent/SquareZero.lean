/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Coherent.Basic
public import TauCeti.RingTheory.Ideal.Cotangent.Basic

/-!
# Coherence of ring extensions and of square-zero extensions

Let `S → R` be a surjective map of commutative rings with finitely generated kernel `I`. Then `S`
is coherent exactly when `R` is coherent and `I` is a coherent `S`-module: this is the
two-out-of-three property of coherent modules applied to the short exact sequence
`0 → I → S → R → 0` of `S`-modules.

The main case is a *square-zero extension*, `I ^ 2 = 0`. Then `I` is a module over `S ⧸ I`, by
the identification of `I` with the conormal module `I ⧸ I²`, and `S` is coherent as soon as
`S ⧸ I` is coherent and `I` is finitely presented over `S ⧸ I`. Applied one square-zero step at
a time, this lifts coherence along nilpotent thickenings.

## Main results

* `TauCeti.isCoherentRing_iff_of_surjective`: along a surjection `S → R` with finitely generated
  kernel `I`, `S` is coherent iff `R` is coherent and `I` is a coherent `S`-module.
* `TauCeti.IsCoherentRing.of_isCoherent_ker`: the reverse implication, which needs no finiteness
  hypothesis on the kernel.
* `TauCeti.IsCoherentRing.of_sq_eq_bot`: if `I ^ 2 = ⊥`, `S ⧸ I` is coherent and `I ⧸ I²` (that
  is, `I`) is finitely presented over `S ⧸ I`, then `S` is coherent.
* `TauCeti.isCoherentRing_iff_of_sq_eq_bot`: for a finitely generated square-zero ideal `I`, the
  converse holds as well.

## References

* B. Bhatt, M. Morrow and P. Scholze, *Integral `p`-adic Hodge theory*,
  Publ. Math. IHÉS 128 (2018), Lemma 3.26.
* [The Stacks Project, Lemma 10.90.3, Tag 05CU](https://stacks.math.columbia.edu/tag/05CU).
-/

public section

namespace TauCeti

section Surjective

variable {S R : Type*} [CommRing S] [CommRing R] [Algebra S R]

/-- Let `S → R` be surjective with kernel `I`. If `R` is a coherent ring and `I` is a coherent
`S`-module, then `S` is a coherent ring. -/
theorem IsCoherentRing.of_isCoherent_ker (hsurj : Function.Surjective (algebraMap S R))
    [IsCoherentRing R] [Module.IsCoherent S (RingHom.ker (algebraMap S R))] :
    IsCoherentRing S := by
  set I := RingHom.ker (algebraMap S R)
  have : Module.FinitePresentation S R :=
    Module.finitePresentation_of_surjective (Algebra.linearMap S R) hsurj
      (Module.Finite.iff_fg.mp (inferInstance : Module.Finite S I))
  have : Module.IsCoherent S R := (Module.isCoherent_iff_of_surjective hsurj).mp ‹_›
  -- Two-out-of-three in the short exact sequence `0 → I → S → R → 0` of `S`-modules.
  refine Module.IsCoherent.of_exact_middle I.subtype (Algebra.linearMap S R)
    I.injective_subtype hsurj (LinearMap.exact_iff.mpr ?_)
  ext x
  simp [I]

/-- Along a surjection `S → R` with finitely generated kernel `I`, the ring `S` is coherent if and
only if `R` is a coherent ring and `I` is a coherent `S`-module. -/
theorem isCoherentRing_iff_of_surjective (hsurj : Function.Surjective (algebraMap S R))
    (hI : (RingHom.ker (algebraMap S R)).FG) :
    IsCoherentRing S ↔
      IsCoherentRing R ∧ Module.IsCoherent S (RingHom.ker (algebraMap S R)) := by
  refine ⟨fun _ ↦ ⟨?_, Module.IsCoherent.of_fg_submodule hI⟩,
    fun ⟨_, _⟩ ↦ .of_isCoherent_ker hsurj⟩
  exact (RingHom.quotientKerEquivOfSurjective hsurj).isCoherentRing_iff.mp (.quotient hI)

end Surjective

section SqEqBot

variable {S : Type*} [CommRing S] {I : Ideal S}

/-- For a finitely generated square-zero ideal `I` of `S`, the ring `S` is coherent if and only if
`S ⧸ I` is coherent and `I`, as a module over `S ⧸ I` through its identification with the conormal
module `I ⧸ I²`, is finitely presented. -/
theorem isCoherentRing_iff_of_sq_eq_bot (hI : I ^ 2 = ⊥) (hfg : I.FG) :
    IsCoherentRing S ↔
      IsCoherentRing (S ⧸ I) ∧ Module.FinitePresentation (S ⧸ I) I.Cotangent := by
  have hker : RingHom.ker (algebraMap S (S ⧸ I)) = I := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  rw [isCoherentRing_iff_of_surjective Ideal.Quotient.mk_surjective (hker ▸ hfg),
    (LinearEquiv.ofEq _ _ hker).isCoherent_iff, (I.toCotangentEquivOfSqEqBot hI).isCoherent_iff,
    ← Ideal.Quotient.isCoherent_iff hfg]
  exact and_congr_right fun _ ↦ IsCoherentRing.isCoherent_iff_finitePresentation

/-- **Coherence of a square-zero extension.** Let `I` be an ideal of `S` with `I ^ 2 = ⊥`. If
`S ⧸ I` is a coherent ring and `I`, as a module over `S ⧸ I` through its identification with the
conormal module `I ⧸ I²`, is finitely presented, then `S` is a coherent ring
(Bhatt–Morrow–Scholze, *Integral `p`-adic Hodge theory*, Lemma 3.26). -/
theorem IsCoherentRing.of_sq_eq_bot (hI : I ^ 2 = ⊥) [IsCoherentRing (S ⧸ I)]
    [Module.FinitePresentation (S ⧸ I) I.Cotangent] : IsCoherentRing S := by
  -- A finite presentation of `I ⧸ I²` over `S ⧸ I` makes `I ≅ I ⧸ I²` finitely generated over `S`.
  have : Module.Finite S I.Cotangent := .trans (S ⧸ I) _
  have : Module.Finite S I := .equiv (I.toCotangentEquivOfSqEqBot hI).symm
  exact ((isCoherentRing_iff_of_sq_eq_bot hI (Module.Finite.iff_fg.mp ‹_›)).mpr ⟨‹_›, ‹_›⟩)

end SqEqBot

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth.Sequence
public import TauCeti.AlgebraicTopology.Singular.Kunneth.Basic

/-!
# The Künneth short exact sequence for singular homology

Let `X` and `Y` be topological spaces and `M` and `N` modules over a commutative ring `k`.
Suppose that the cycles `Z_q(Y; N)` of the singular chain complex `C(Y; N)` and the quotients
`C_q(Y; N) / Z_q(Y; N)` are projective.  Over a principal ideal domain this holds for every
projective `N`, for instance `N = k`, since the singular chain modules `C_q(Y; N) = ⨁ N` are then
projective (`SSet.projective_chainComplex_X`) and instance search finds both hypotheses
(`HomologicalComplex.free_cycles_of_isPrincipalIdealRing` and
`HomologicalComplex.free_cokernel_iCycles_of_isPrincipalIdealRing`).  Then the **Künneth
sequence**

`0 ⟶ ⨁_{p + q = m + 1} Hₚ(X; M) ⊗ H_q(Y; N) ⟶ Hₘ₊₁(X × Y; M ⊗ N)`
`    ⟶ ⨁_{p + q = m} Tor₁(Hₚ(X; M), H_q(Y; N)) ⟶ 0`

is exact (`TopCat.singularHomologyKunnethShortComplex_shortExact`).  The first map is the Künneth
map `TopCat.singularHomologyKunneth`, assembled from the homology cross products.  The second map
`TopCat.singularHomologyToTor` is the map induced by the Alexander–Whitney map
`C(X × Y; M ⊗ N) ⟶ C(X; M) ⊗ C(Y; N)` followed by the algebraic map
`HomologicalComplex.homologyToTor` of the Künneth sequence of chain complexes
(`HomologicalComplex.homologyKunnethShortComplex_shortExact`).  The two sequences are isomorphic
through the Eilenberg–Zilber homotopy equivalence `TopCat.eilenbergZilberHomotopyEquiv`, whose
inverse is the shuffle map through which the Künneth map is defined.

Over a principal ideal domain `k`, with `M = N = k` and the unitor `k ⊗ k ≅ k`, this gives the
classical sequence

`0 ⟶ ⨁_{p + q = m + 1} Hₚ(X; k) ⊗ H_q(Y; k) ⟶ Hₘ₊₁(X × Y; k)`
`    ⟶ ⨁_{p + q = m} Tor₁(Hₚ(X; k), H_q(Y; k)) ⟶ 0`

(`TopCat.singularHomologyKunnethUnitShortComplex_shortExact`).

The naturality of `TopCat.singularHomologyToTor` in `X` and `Y`, and the splitting of the
sequence, which cannot be chosen naturally, are not proved in this file.

## Main definitions and results

* `TopCat.singularHomologyToTor`: the map
  `Hₘ₊₁(X × Y; M ⊗ N) ⟶ ⨁_{p + q = m} Tor₁(Hₚ(X; M), H_q(Y; N))`.
* `TopCat.singularHomologyKunnethShortComplex` and
  `TopCat.singularHomologyKunnethShortComplex_shortExact`: **the Künneth short exact sequence**.
* `TopCat.mono_singularHomologyKunneth`: the Künneth map is a monomorphism in every degree.
* `TopCat.singularHomologyKunnethUnitShortComplex` and
  `TopCat.singularHomologyKunnethUnitShortComplex_shortExact`: its form with coefficients in a
  principal ideal domain.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.B, Theorem 3B.6.
* C. Weibel, *An Introduction to Homological Algebra*, Theorem 3.6.3, the Künneth formula.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex

universe w

namespace TopCat

variable {k : Type w} [CommRing k]

section Kunneth

variable (X Y : TopCat.{w}) (M N : ModuleCat.{w} k)
  [∀ q, Projective (cokernel (((toSSet.obj Y).chainComplex N).iCycles q))]
  [∀ q, Projective (((toSSet.obj Y).chainComplex N).cycles q)]

/-- The map `Hₘ₊₁(X × Y; M ⊗ N) ⟶ ⨁_{p + q = m} Tor₁(Hₚ(X; M), H_q(Y; N))` of the Künneth short
exact sequence (`TopCat.singularHomologyKunnethShortComplex_shortExact`): the map induced by the
Alexander–Whitney map, followed by the map `HomologicalComplex.homologyToTor` of the Künneth
sequence of the singular chain complexes `C(X; M)` and `C(Y; N)`. -/
def singularHomologyToTor (m : ℕ) :
    ((singularHomologyFunctor _ (m + 1)).obj (M ⊗ N)).obj (X ⊗ Y) ⟶
      GradedObject.mapBifunctorMapObj (Tor (ModuleCat.{w} k) 1) (fun x ↦ x.1 + x.2)
        (fun p ↦ ((singularHomologyFunctor _ p).obj M).obj X)
        (fun q ↦ ((singularHomologyFunctor _ q).obj N).obj Y) m :=
  homologyMap (alexanderWhitney X Y M N) (m + 1) ≫
    homologyToTor ((toSSet.obj X).chainComplex M) ((toSSet.obj Y).chainComplex N) m

/-- The map to `⨁ Tor₁(Hₚ(X; M), H_q(Y; N))` is the map induced by the Alexander–Whitney map
followed by the algebraic map of the Künneth sequence of the singular chain complexes. -/
lemma singularHomologyToTor_def (m : ℕ) :
    singularHomologyToTor X Y M N m =
      homologyMap (alexanderWhitney X Y M N) (m + 1) ≫
        homologyToTor ((toSSet.obj X).chainComplex M) ((toSSet.obj Y).chainComplex N) m :=
  (rfl)

/-- The Künneth map followed by the map to `⨁ Tor₁(Hₚ(X; M), H_q(Y; N))` vanishes. -/
@[reassoc (attr := simp)]
lemma singularHomologyKunneth_comp_singularHomologyToTor (m : ℕ) :
    singularHomologyKunneth X Y M N (m + 1) ≫ singularHomologyToTor X Y M N m = 0 :=
  (singularHomologyKunneth_comp_homologyMap_alexanderWhitney_assoc X Y M N (m + 1) _).trans
    (homologyKunneth_comp_homologyToTor _ _ m)

/-- The Künneth short complex
`⨁_{p + q = m + 1} Hₚ(X; M) ⊗ H_q(Y; N) ⟶ Hₘ₊₁(X × Y; M ⊗ N)`
`  ⟶ ⨁_{p + q = m} Tor₁(Hₚ(X; M), H_q(Y; N))`
formed by the Künneth map and `TopCat.singularHomologyToTor`. -/
abbrev singularHomologyKunnethShortComplex (m : ℕ) : ShortComplex (ModuleCat.{w} k) :=
  ShortComplex.mk _ _ (singularHomologyKunneth_comp_singularHomologyToTor X Y M N m)

/-- The Künneth short complex of the spaces is that of their singular chain complexes, through
the isomorphism induced on homology by the Eilenberg–Zilber homotopy equivalence. -/
private def homologyKunnethShortComplexIso (m : ℕ) :
    homologyKunnethShortComplex ((toSSet.obj X).chainComplex M)
        ((toSSet.obj Y).chainComplex N) m ≅
      singularHomologyKunnethShortComplex X Y M N m :=
  ShortComplex.isoMk (Iso.refl _)
    ((eilenbergZilberHomotopyEquiv X Y M N).toHomologyIso (m + 1)).symm (Iso.refl _)
    (by
      simp only [Iso.symm_hom, HomotopyEquiv.toHomologyIso, eilenbergZilberHomotopyEquiv_inv,
        Iso.refl_hom]
      exact (Category.id_comp _).trans (singularHomologyKunneth_def X Y M N (m + 1)))
    (by
      have h := ((eilenbergZilberHomotopyEquiv X Y M N).toHomologyIso (m + 1)).inv_hom_id
      simp only [Iso.symm_hom, HomotopyEquiv.toHomologyIso, eilenbergZilberHomotopyEquiv_hom,
        eilenbergZilberHomotopyEquiv_inv, Iso.refl_hom] at h ⊢
      exact ((reassoc_of% h) _).trans (Category.comp_id _).symm)

/-- **The Künneth short exact sequence for singular homology.**  Let `M` and `N` be modules over a
commutative ring such that the cycles `Z_q(Y; N)` and the quotients `C_q(Y; N) / Z_q(Y; N)` are
projective, for instance any projective `N` over a principal ideal domain.  Then

`0 ⟶ ⨁_{p + q = m + 1} Hₚ(X; M) ⊗ H_q(Y; N) ⟶ Hₘ₊₁(X × Y; M ⊗ N)`
`  ⟶ ⨁_{p + q = m} Tor₁(Hₚ(X; M), H_q(Y; N)) ⟶ 0`

is exact, the first map being the Künneth map and the second `TopCat.singularHomologyToTor`. -/
theorem singularHomologyKunnethShortComplex_shortExact (m : ℕ) :
    (singularHomologyKunnethShortComplex X Y M N m).ShortExact :=
  ShortComplex.shortExact_of_iso (homologyKunnethShortComplexIso X Y M N m)
    (homologyKunnethShortComplex_shortExact _ _ m)

/-- **The Künneth map is a monomorphism** when the cycles `Z_q(Y; N)` and the quotients
`C_q(Y; N) / Z_q(Y; N)` are projective, for instance for any projective `N` over a principal ideal
domain. -/
theorem mono_singularHomologyKunneth (n : ℕ) : Mono (singularHomologyKunneth X Y M N n) := by
  rw [singularHomologyKunneth_def, ← eilenbergZilberHomotopyEquiv_inv]
  -- The shuffle map is a homotopy inverse of the Alexander–Whitney map.  The instances are passed
  -- explicitly: instance search does not identify the homology instances of the general
  -- `TopCat.singularHomologyKunneth` with those found in `ModuleCat`, which are only defeq.
  exact @mono_comp _ _ _ _ _ _ (mono_homologyKunneth _ _ n) _ (@IsIso.mono_of_iso _ _ _ _ _
    ((eilenbergZilberHomotopyEquiv X Y M N).toHomologyIso n).isIso_inv)

end Kunneth

section Unit

variable (k) [NoZeroDivisors k] [IsPrincipalIdealRing k] (X Y : TopCat.{w})

/-- The Künneth short complex with coefficients in the ring:
`⨁_{p + q = m + 1} Hₚ(X; k) ⊗ H_q(Y; k) ⟶ Hₘ₊₁(X × Y; k) ⟶ ⨁_{p + q = m} Tor₁(Hₚ(X; k), H_q(Y; k))`,
formed by the Künneth map and `TopCat.singularHomologyToTor` through the unitor `k ⊗ k ≅ k`. -/
abbrev singularHomologyKunnethUnitShortComplex (m : ℕ) : ShortComplex (ModuleCat.{w} k) :=
  -- The unit `𝟙_ (ModuleCat k)` is `k` itself, so the singular chain modules `C_q(Y; k)` are
  -- projective and instance search finds the hypotheses of `TopCat.singularHomologyToTor`.
  have : Module.Projective k (𝟙_ (ModuleCat.{w} k)) := inferInstanceAs (Module.Projective k k)
  ShortComplex.mk
    (singularHomologyKunneth X Y (𝟙_ _) (𝟙_ _) (m + 1) ≫
      ((singularHomologyFunctor _ (m + 1)).map (λ_ (𝟙_ (ModuleCat.{w} k))).hom).app (X ⊗ Y))
    (((singularHomologyFunctor _ (m + 1)).map (λ_ (𝟙_ (ModuleCat.{w} k))).inv).app (X ⊗ Y) ≫
      singularHomologyToTor X Y (𝟙_ _) (𝟙_ _) m)
    (by simp)

/-- **The Künneth short exact sequence over a principal ideal domain.**  For a principal ideal
domain `k`, for instance `ℤ`,

`0 ⟶ ⨁_{p + q = m + 1} Hₚ(X; k) ⊗ H_q(Y; k) ⟶ Hₘ₊₁(X × Y; k)`
`  ⟶ ⨁_{p + q = m} Tor₁(Hₚ(X; k), H_q(Y; k)) ⟶ 0`

is exact, the first map being the Künneth map followed by the map induced by the unitor
`k ⊗ k ≅ k`. -/
theorem singularHomologyKunnethUnitShortComplex_shortExact (m : ℕ) :
    (singularHomologyKunnethUnitShortComplex k X Y m).ShortExact := by
  have : Module.Projective k (𝟙_ (ModuleCat.{w} k)) := inferInstanceAs (Module.Projective k k)
  refine ShortComplex.shortExact_of_iso ?_
    (singularHomologyKunnethShortComplex_shortExact X Y (𝟙_ (ModuleCat.{w} k)) (𝟙_ _) m)
  -- the middle terms are identified by the map induced by the unitor `k ⊗ k ≅ k`
  exact ShortComplex.isoMk (Iso.refl _)
    (((singularHomologyFunctor _ (m + 1)).mapIso (λ_ (𝟙_ (ModuleCat.{w} k)))).app (X ⊗ Y))
    (Iso.refl _) (Category.id_comp _).symm (by simp)

end Unit

end TopCat

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

If the cycles of `C(X; M)` split off its terms as well, for instance for projective `M` and `N`
over a principal ideal domain, the Künneth map is a split monomorphism
(`TopCat.isSplitMono_singularHomologyKunneth`) and the sequence splits
(`TopCat.singularHomologyKunnethSplitting`, and `TopCat.singularHomologyKunnethUnitSplitting` for
coefficients in a principal ideal domain).  The splitting is built from chosen splittings of the
cycles of the singular chain complexes and need not be natural in `X` and `Y`; that no natural
splitting exists is not proved here.

The sequence itself is natural.  Continuous maps `f : X ⟶ X'` and `g : Y ⟶ Y'` induce a morphism
of Künneth short complexes (`TopCat.singularHomologyKunnethShortComplexMap`): the Künneth map is
natural by `TopCat.singularHomologyKunneth_naturality`, and `TopCat.singularHomologyToTor`
intertwines `(f × g)_*` with the maps `Tor₁(f_*, g_*)`
(`TopCat.singularHomologyToTor_naturality`).  The sequence is natural in the coefficient modules
as well (`TopCat.singularHomologyKunneth_coefficient_naturality` and
`TopCat.singularHomologyToTor_coefficient_naturality`), giving the morphism of Künneth short
complexes `TopCat.singularHomologyKunnethShortComplexCoefficientMap`.  The naturality of
`TopCat.singularHomologyToTor` follows from that of the Alexander–Whitney map and of the algebraic
map (`HomologicalComplex.homologyToTor_naturality`).

## Main definitions and results

* `TopCat.singularHomologyToTor`: the map
  `Hₘ₊₁(X × Y; M ⊗ N) ⟶ ⨁_{p + q = m} Tor₁(Hₚ(X; M), H_q(Y; N))`.
* `TopCat.singularHomologyKunnethShortComplex` and
  `TopCat.singularHomologyKunnethShortComplex_shortExact`: **the Künneth short exact sequence**.
* `TopCat.mono_singularHomologyKunneth`: the Künneth map is a monomorphism in every degree.
* `TopCat.singularHomologyKunnethUnitShortComplex` and
  `TopCat.singularHomologyKunnethUnitShortComplex_shortExact`: its form with coefficients in a
  principal ideal domain.
* `TopCat.singularHomologyKunnethSplitting` and `TopCat.singularHomologyKunnethUnitSplitting`:
  **the splitting of the Künneth sequence**.
* `TopCat.singularHomologyToTor_naturality` and
  `TopCat.singularHomologyToTor_coefficient_naturality`: **naturality of the map to `Tor`** in
  the spaces and in the coefficients.
* `TopCat.singularHomologyKunnethShortComplexMap` and
  `TopCat.singularHomologyKunnethShortComplexCoefficientMap`: the morphisms of Künneth short
  complexes induced by a pair of continuous maps and by a pair of maps of coefficient modules.

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

/-- **The Künneth short exact sequence for singular homology splits** when, in addition, the
cycles of the singular chain complex `C(X; M)` split off its terms; for instance for projective
modules `M` and `N` over a principal ideal domain.  The splitting comes from a retraction of the
Künneth map (`TopCat.isSplitMono_singularHomologyKunneth`) built from chosen splittings of the
cycles, so it need not be natural in `X` and `Y`. -/
def singularHomologyKunnethSplitting
    [∀ p, IsSplitMono (((toSSet.obj X).chainComplex M).iCycles p)] (m : ℕ) :
    (singularHomologyKunnethShortComplex X Y M N m).Splitting :=
  have := isSplitMono_singularHomologyKunneth X Y M N (m + 1)
  .ofExactOfRetraction _ (singularHomologyKunnethShortComplex_shortExact X Y M N m).exact
    (retraction (singularHomologyKunneth X Y M N (m + 1))) (IsSplitMono.id _)
    (singularHomologyKunnethShortComplex_shortExact X Y M N m).epi_g

/-- The retraction of the Künneth splitting is the chosen retraction of the Künneth map. -/
@[simp] lemma singularHomologyKunnethSplitting_r
    [∀ p, IsSplitMono (((toSSet.obj X).chainComplex M).iCycles p)] (m : ℕ) :
    (singularHomologyKunnethSplitting X Y M N m).r =
      retraction (singularHomologyKunneth X Y M N (m + 1))
        (hf := isSplitMono_singularHomologyKunneth X Y M N (m + 1)) :=
  (rfl)

end Kunneth

section Naturality

variable {X Y X' Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (M N : ModuleCat.{w} k)
  [∀ q, Projective (cokernel (((toSSet.obj Y).chainComplex N).iCycles q))]
  [∀ q, Projective (((toSSet.obj Y).chainComplex N).cycles q)]
  [∀ q, Projective (cokernel (((toSSet.obj Y').chainComplex N).iCycles q))]
  [∀ q, Projective (((toSSet.obj Y').chainComplex N).cycles q)]

/-- **Naturality of the map to `⨁ Tor₁(Hₚ(X; M), H_q(Y; N))`** in both spaces: for continuous
maps `f : X ⟶ X'` and `g : Y ⟶ Y'`, `TopCat.singularHomologyToTor` intertwines `(f × g)_*` with
the maps `Tor₁(f_*, g_*)`. -/
@[reassoc]
theorem singularHomologyToTor_naturality (m : ℕ) :
    ((singularHomologyFunctor _ (m + 1)).obj (M ⊗ N)).map (f ⊗ₘ g) ≫
        singularHomologyToTor X' Y' M N m =
      singularHomologyToTor X Y M N m ≫
        GradedObject.mapBifunctorMapMap (Tor (ModuleCat.{w} k) 1) (fun x ↦ x.1 + x.2)
          (fun p ↦ ((singularHomologyFunctor _ p).obj M).map f)
          (fun q ↦ ((singularHomologyFunctor _ q).obj N).map g) m := by
  -- `Hₙ(f)` is by definition the homology of the induced chain map, so the statement is the
  -- naturality of the Alexander–Whitney map followed by that of the algebraic map to `Tor`.
  have hAW : SSet.chainComplexMap (toSSet.map (f ⊗ₘ g)) (M ⊗ N) ≫ alexanderWhitney X' Y' M N =
      alexanderWhitney X Y M N ≫ HomologicalComplex.tensorHom
        (SSet.chainComplexMap (toSSet.map f) M) (SSet.chainComplexMap (toSSet.map g) N) :=
    alexanderWhitney_naturality f g M N
  have := homologyToTor_naturality (SSet.chainComplexMap (toSSet.map f) M)
    (SSet.chainComplexMap (toSSet.map g) N) m
  calc _ = homologyMap (SSet.chainComplexMap (toSSet.map (f ⊗ₘ g)) (M ⊗ N) ≫
        alexanderWhitney X' Y' M N) (m + 1) ≫
          homologyToTor ((toSSet.obj X').chainComplex M) ((toSSet.obj Y').chainComplex N) m :=
        (homologyMap_comp_assoc _ _ _ _).symm
    _ = _ := by
      rw [hAW, homologyMap_comp_assoc, this, singularHomologyToTor_def]
      exact (Category.assoc _ _ _).symm

/-- The morphism of Künneth short complexes induced by continuous maps `f : X ⟶ X'` and
`g : Y ⟶ Y'`: the maps `f_* ⊗ g_*` on `⨁ Hₚ(X; M) ⊗ H_q(Y; N)`, `(f × g)_*` on
`Hₘ₊₁(X × Y; M ⊗ N)` and `Tor₁(f_*, g_*)` on `⨁ Tor₁(Hₚ(X; M), H_q(Y; N))`.  Together with
`TopCat.singularHomologyKunnethShortComplex_shortExact` this makes the Künneth short exact sequence
natural in both spaces. -/
def singularHomologyKunnethShortComplexMap (m : ℕ) :
    singularHomologyKunnethShortComplex X Y M N m ⟶
      singularHomologyKunnethShortComplex X' Y' M N m where
  τ₁ := GradedObject.Monoidal.tensorHom (fun p ↦ ((singularHomologyFunctor _ p).obj M).map f)
    (fun q ↦ ((singularHomologyFunctor _ q).obj N).map g) (m + 1)
  τ₂ := ((singularHomologyFunctor _ (m + 1)).obj (M ⊗ N)).map (f ⊗ₘ g)
  τ₃ := GradedObject.mapBifunctorMapMap (Tor (ModuleCat.{w} k) 1) (fun x ↦ x.1 + x.2)
    (fun p ↦ ((singularHomologyFunctor _ p).obj M).map f)
    (fun q ↦ ((singularHomologyFunctor _ q).obj N).map g) m
  comm₁₂ := singularHomologyKunneth_naturality f g M N (m + 1)
  comm₂₃ := singularHomologyToTor_naturality f g M N m

/-- On `⨁ Hₚ(X; M) ⊗ H_q(Y; N)`, the morphism of Künneth short complexes is `f_* ⊗ g_*`. -/
@[simp]
lemma singularHomologyKunnethShortComplexMap_τ₁ (m : ℕ) :
    (singularHomologyKunnethShortComplexMap f g M N m).τ₁ =
      GradedObject.Monoidal.tensorHom (fun p ↦ ((singularHomologyFunctor _ p).obj M).map f)
        (fun q ↦ ((singularHomologyFunctor _ q).obj N).map g) (m + 1) :=
  (rfl)

/-- On `Hₘ₊₁(X × Y; M ⊗ N)`, the morphism of Künneth short complexes is `(f × g)_*`. -/
@[simp]
lemma singularHomologyKunnethShortComplexMap_τ₂ (m : ℕ) :
    (singularHomologyKunnethShortComplexMap f g M N m).τ₂ =
      ((singularHomologyFunctor _ (m + 1)).obj (M ⊗ N)).map (f ⊗ₘ g) :=
  (rfl)

/-- On `⨁ Tor₁(Hₚ(X; M), H_q(Y; N))`, the morphism of Künneth short complexes is
`Tor₁(f_*, g_*)`. -/
@[simp]
lemma singularHomologyKunnethShortComplexMap_τ₃ (m : ℕ) :
    (singularHomologyKunnethShortComplexMap f g M N m).τ₃ =
      GradedObject.mapBifunctorMapMap (Tor (ModuleCat.{w} k) 1) (fun x ↦ x.1 + x.2)
        (fun p ↦ ((singularHomologyFunctor _ p).obj M).map f)
        (fun q ↦ ((singularHomologyFunctor _ q).obj N).map g) m :=
  (rfl)

end Naturality

section CoefficientNaturality

variable (X Y : TopCat.{w}) {M N M' N' : ModuleCat.{w} k} (φ : M ⟶ M') (ψ : N ⟶ N')
  [∀ q, Projective (cokernel (((toSSet.obj Y).chainComplex N).iCycles q))]
  [∀ q, Projective (((toSSet.obj Y).chainComplex N).cycles q)]
  [∀ q, Projective (cokernel (((toSSet.obj Y).chainComplex N').iCycles q))]
  [∀ q, Projective (((toSSet.obj Y).chainComplex N').cycles q)]

/-- **Naturality of the map to `⨁ Tor₁(Hₚ(X; M), H_q(Y; N))`** in both coefficient modules: for
linear maps `φ : M ⟶ M'` and `ψ : N ⟶ N'`, `TopCat.singularHomologyToTor` intertwines the map
induced by `φ ⊗ ψ` with the maps `Tor₁(φ_*, ψ_*)`. -/
@[reassoc]
theorem singularHomologyToTor_coefficient_naturality (m : ℕ) :
    ((singularHomologyFunctor _ (m + 1)).map (φ ⊗ₘ ψ)).app (X ⊗ Y) ≫
        singularHomologyToTor X Y M' N' m =
      singularHomologyToTor X Y M N m ≫
        GradedObject.mapBifunctorMapMap (Tor (ModuleCat.{w} k) 1) (fun x ↦ x.1 + x.2)
          (fun p ↦ ((singularHomologyFunctor _ p).map φ).app X)
          (fun q ↦ ((singularHomologyFunctor _ q).map ψ).app Y) m := by
  -- as for the naturality in the spaces, with the coefficient naturality of the Alexander–Whitney
  -- map
  have hAW : ((SSet.chainComplexFunctor _).map (φ ⊗ₘ ψ)).app (toSSet.obj (X ⊗ Y)) ≫
        alexanderWhitney X Y M' N' =
      alexanderWhitney X Y M N ≫ HomologicalComplex.tensorHom
        (((SSet.chainComplexFunctor _).map φ).app (toSSet.obj X))
        (((SSet.chainComplexFunctor _).map ψ).app (toSSet.obj Y)) :=
    alexanderWhitney_coefficient_naturality X Y φ ψ
  have := homologyToTor_naturality (((SSet.chainComplexFunctor _).map φ).app (toSSet.obj X))
    (((SSet.chainComplexFunctor _).map ψ).app (toSSet.obj Y)) m
  calc _ = homologyMap (((SSet.chainComplexFunctor _).map (φ ⊗ₘ ψ)).app (toSSet.obj (X ⊗ Y)) ≫
        alexanderWhitney X Y M' N') (m + 1) ≫
          homologyToTor ((toSSet.obj X).chainComplex M') ((toSSet.obj Y).chainComplex N') m :=
        (homologyMap_comp_assoc _ _ _ _).symm
    _ = _ := by
      rw [hAW, homologyMap_comp_assoc, this, singularHomologyToTor_def]
      exact (Category.assoc _ _ _).symm

/-- The morphism of Künneth short complexes induced by linear maps `φ : M ⟶ M'` and `ψ : N ⟶ N'`
of coefficient modules: the maps `φ_* ⊗ ψ_*` on `⨁ Hₚ(X; M) ⊗ H_q(Y; N)`, the map induced by
`φ ⊗ ψ` on `Hₘ₊₁(X × Y; M ⊗ N)` and `Tor₁(φ_*, ψ_*)` on `⨁ Tor₁(Hₚ(X; M), H_q(Y; N))`.  Together
with `TopCat.singularHomologyKunnethShortComplex_shortExact` this makes the Künneth short exact
sequence natural in both coefficient modules. -/
def singularHomologyKunnethShortComplexCoefficientMap (m : ℕ) :
    singularHomologyKunnethShortComplex X Y M N m ⟶
      singularHomologyKunnethShortComplex X Y M' N' m where
  τ₁ := GradedObject.Monoidal.tensorHom (fun p ↦ ((singularHomologyFunctor _ p).map φ).app X)
    (fun q ↦ ((singularHomologyFunctor _ q).map ψ).app Y) (m + 1)
  τ₂ := ((singularHomologyFunctor _ (m + 1)).map (φ ⊗ₘ ψ)).app (X ⊗ Y)
  τ₃ := GradedObject.mapBifunctorMapMap (Tor (ModuleCat.{w} k) 1) (fun x ↦ x.1 + x.2)
    (fun p ↦ ((singularHomologyFunctor _ p).map φ).app X)
    (fun q ↦ ((singularHomologyFunctor _ q).map ψ).app Y) m
  comm₁₂ := singularHomologyKunneth_coefficient_naturality X Y φ ψ (m + 1)
  comm₂₃ := singularHomologyToTor_coefficient_naturality X Y φ ψ m

/-- On `⨁ Hₚ(X; M) ⊗ H_q(Y; N)`, the morphism of Künneth short complexes is `φ_* ⊗ ψ_*`. -/
@[simp]
lemma singularHomologyKunnethShortComplexCoefficientMap_τ₁ (m : ℕ) :
    (singularHomologyKunnethShortComplexCoefficientMap X Y φ ψ m).τ₁ =
      GradedObject.Monoidal.tensorHom (fun p ↦ ((singularHomologyFunctor _ p).map φ).app X)
        (fun q ↦ ((singularHomologyFunctor _ q).map ψ).app Y) (m + 1) :=
  (rfl)

/-- On `Hₘ₊₁(X × Y; M ⊗ N)`, the morphism of Künneth short complexes is the map induced by
`φ ⊗ ψ`. -/
@[simp]
lemma singularHomologyKunnethShortComplexCoefficientMap_τ₂ (m : ℕ) :
    (singularHomologyKunnethShortComplexCoefficientMap X Y φ ψ m).τ₂ =
      ((singularHomologyFunctor _ (m + 1)).map (φ ⊗ₘ ψ)).app (X ⊗ Y) :=
  (rfl)

/-- On `⨁ Tor₁(Hₚ(X; M), H_q(Y; N))`, the morphism of Künneth short complexes is
`Tor₁(φ_*, ψ_*)`. -/
@[simp]
lemma singularHomologyKunnethShortComplexCoefficientMap_τ₃ (m : ℕ) :
    (singularHomologyKunnethShortComplexCoefficientMap X Y φ ψ m).τ₃ =
      GradedObject.mapBifunctorMapMap (Tor (ModuleCat.{w} k) 1) (fun x ↦ x.1 + x.2)
        (fun p ↦ ((singularHomologyFunctor _ p).map φ).app X)
        (fun q ↦ ((singularHomologyFunctor _ q).map ψ).app Y) m :=
  (rfl)

end CoefficientNaturality

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

/-- **The Künneth short exact sequence over a principal ideal domain splits**, so that
`Hₘ₊₁(X × Y; k)` is the direct sum of `⨁_{p + q = m + 1} Hₚ(X; k) ⊗ H_q(Y; k)` and
`⨁_{p + q = m} Tor₁(Hₚ(X; k), H_q(Y; k))`
(`CategoryTheory.ShortComplex.Splitting.isoBinaryBiproduct`).
The splitting depends on chosen splittings of the cycles of the singular chain complexes, and need
not be natural in `X` and `Y`. -/
def singularHomologyKunnethUnitSplitting (m : ℕ) :
    (singularHomologyKunnethUnitShortComplex k X Y m).Splitting :=
  have : Module.Projective k (𝟙_ (ModuleCat.{w} k)) := inferInstanceAs (Module.Projective k k)
  have := isSplitMono_singularHomologyKunneth X Y (𝟙_ (ModuleCat.{w} k)) (𝟙_ _) (m + 1)
  -- a retraction of the Künneth map, preceded by the map induced by the inverse unitor
  .ofExactOfRetraction _ (singularHomologyKunnethUnitShortComplex_shortExact k X Y m).exact
    (((singularHomologyFunctor _ (m + 1)).map (λ_ (𝟙_ (ModuleCat.{w} k))).inv).app (X ⊗ Y) ≫
      retraction (singularHomologyKunneth X Y (𝟙_ _) (𝟙_ _) (m + 1)))
    (by simp) (singularHomologyKunnethUnitShortComplex_shortExact k X Y m).epi_g

/-- The retraction of the Künneth splitting with coefficients in `k` is the chosen retraction of
the Künneth map, preceded by the map induced by the inverse unitor. -/
@[simp] lemma singularHomologyKunnethUnitSplitting_r (m : ℕ) :
    (singularHomologyKunnethUnitSplitting k X Y m).r =
      ((singularHomologyFunctor _ (m + 1)).map (λ_ (𝟙_ (ModuleCat.{w} k))).inv).app (X ⊗ Y) ≫
        retraction (singularHomologyKunneth X Y (𝟙_ _) (𝟙_ _) (m + 1))
          (hf := have : Module.Projective k (𝟙_ (ModuleCat.{w} k)) :=
            inferInstanceAs (Module.Projective k k)
          isSplitMono_singularHomologyKunneth X Y (𝟙_ _) (𝟙_ _) (m + 1)) :=
  (rfl)

end Unit

end TopCat

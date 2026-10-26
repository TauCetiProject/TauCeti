/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.Basic
public import TauCeti.Algebra.Homology.HomologicalComplex.ProjectiveDimension
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.Algebra.Homology.Monoidal.Homology.Braiding
public import TauCeti.CategoryTheory.Monoidal.Tor

/-!
# The Künneth short exact sequence

Let `K` and `L` be chain complexes of modules over a commutative ring `R`, indexed by `ℕ`, and
suppose that the cycles `Z_q(L)` and the quotients `L_q / Z_q(L)` are projective.  The quotient
`L_q / Z_q(L)` is the module of boundaries `B_{q-1}(L)`, so this holds for every complex of
projective modules over a principal ideal domain
(`HomologicalComplex.free_cycles_of_isPrincipalIdealRing` and
`HomologicalComplex.free_cokernel_iCycles_of_isPrincipalIdealRing`), for instance for singular
chains with integer coefficients. More generally, both projectivity hypotheses are found by
instance search for a complex of projective modules when every module has projective dimension
at most one (`HomologicalComplex.projective_cycles_of_hasProjectiveDimensionLE_one` and
`HomologicalComplex.projective_cokernel_iCycles_of_hasProjectiveDimensionLE_one`). Then the
**Künneth sequence**

`0 ⟶ ⨁_{p + q = m + 1} Hₚ(K) ⊗ H_q(L) ⟶ Hₘ₊₁(K ⊗ L) ⟶ ⨁_{p + q = m} Tor₁(Hₚ(K), H_q(L)) ⟶ 0`

is exact (`HomologicalComplex.homologyKunnethShortComplex_shortExact`), where the first map is
the Künneth map `HomologicalComplex.homologyKunneth` assembled from the cross products, and `Tor₁`
is Mathlib's `CategoryTheory.Tor`.  No hypothesis is imposed on `K`.

The second map `HomologicalComplex.homologyToTor` is induced by the projection of `L` onto
`L / Z(L)`, through the identification of `Tor₁(Hₚ(K), H_q(L))` given by the projective
presentation `0 ⟶ H_{q+1}(L / Z(L)) ⟶ H_q(Z(L)) ⟶ H_q(L) ⟶ 0`
(`HomologicalComplex.homologyPresentation`).  It is characterized by its composite with the
monomorphism `HomologicalComplex.homologyTorToHomologyQuotient` into `Hₘ₊₁(K ⊗ (L / Z(L)))`
(`HomologicalComplex.homologyToTor_comp_homologyTorToHomologyQuotient` and
`HomologicalComplex.homologyToTor_unique`).  It is natural in both complexes
(`HomologicalComplex.homologyToTor_naturality`), as is the Künneth map, so the Künneth sequence is
natural in `K` and `L`: chain maps induce morphisms of Künneth short complexes
(`HomologicalComplex.homologyKunnethShortComplexMap`).

If the cycles of `K` split off its terms as well, for instance when `K` is also a complex of
projective modules over a principal ideal domain, the Künneth map is a split monomorphism and the
sequence splits (`HomologicalComplex.homologyKunnethShortComplexSplitting`).  The splitting is
built from chosen splittings of the cycles and need not be natural in `K` and `L`.

## Main definitions and results

* `HomologicalComplex.homologyPresentation` and
  `HomologicalComplex.homologyPresentation_shortExact`: the presentation of `H_q(L)` by the
  homology of `Z(L)` and `L / Z(L)`.
* `HomologicalComplex.homologyTor`: the module `⨁_{p + q = m} Tor₁(Hₚ(K), H_q(L))`.
* `HomologicalComplex.homologyToTor`: the map `Hₘ₊₁(K ⊗ L) ⟶ ⨁_{p + q = m} Tor₁(Hₚ(K), H_q(L))`.
* `HomologicalComplex.homologyTorToHomologyQuotient`: the inclusion
  `⨁_{p + q = m} Tor₁(Hₚ(K), H_q(L)) ⟶ Hₘ₊₁(K ⊗ (L / Z(L)))` characterizing `homologyToTor`.
* `HomologicalComplex.homologyKunnethShortComplex`: the Künneth short complex.
* `HomologicalComplex.mono_homologyKunneth`: the Künneth map is a monomorphism in every degree.
* `HomologicalComplex.homologyKunnethShortComplex_shortExact`: **the Künneth short exact sequence**.
* `HomologicalComplex.homologyTorToHomologyQuotient_naturality` and
  `HomologicalComplex.homologyToTor_naturality`: naturality in both complexes.
* `HomologicalComplex.homologyKunnethShortComplexMap`: the morphism of Künneth short complexes
  induced by a pair of chain maps.
* `HomologicalComplex.homologyKunnethShortComplexSplitting`: its splitting when the cycles of `K`
  split off as well.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Theorem 3.6.3, the Künneth formula.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.B, Theorem 3B.5.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace HomologicalComplex

universe u

variable {R : Type u} [CommRing R]

section Presentation

variable (L : ChainComplex (ModuleCat.{u} R) ℕ)

/-- The short complex `H_{q+1}(L / Z(L)) ⟶ H_q(Z(L)) ⟶ H_q(L)` formed by the connecting
morphism of `0 ⟶ Z(L) ⟶ L ⟶ L / Z(L) ⟶ 0` and the map induced by the inclusion of the cycles.
It is short exact (`HomologicalComplex.homologyPresentation_shortExact`), and since `Z(L)` and
`L / Z(L)` have zero differentials its first two terms are isomorphic to `L_{q+1} / Z_{q+1}(L)` and
`Z_q(L)`, so it is a projective presentation of `H_q(L)` when these are projective. -/
abbrev homologyPresentation (q : ℕ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (L.cyclesComplexShortComplex_shortExact.δ (q + 1) q (by simp))
    (homologyMap L.cyclesComplexShortComplex.f q ≫
      eqToHom (congrArg (·.homology q) L.cyclesComplexShortComplex_X₂)) (by simp)

/-- `H_{q+1}(L / Z(L)) ⟶ H_q(Z(L)) ⟶ H_q(L)` is short exact: it is a piece of the long exact
homology sequence of `0 ⟶ Z(L) ⟶ L ⟶ L / Z(L) ⟶ 0`, whose connecting morphisms are
monomorphisms and whose map `H(Z(L)) ⟶ H(L)` is an epimorphism. -/
lemma homologyPresentation_shortExact (q : ℕ) : (L.homologyPresentation q).ShortExact where
  exact := (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk (S₂ := L.homologyPresentation q)
    (S₁ := ShortComplex.mk (L.cyclesComplexShortComplex_shortExact.δ (q + 1) q (by simp))
      (homologyMap L.cyclesComplexShortComplex.f q)
      (L.cyclesComplexShortComplex_shortExact.δ_comp (q + 1) q (by simp)))
    (Iso.refl _) (Iso.refl _) (eqToIso (congrArg (·.homology q) L.cyclesComplexShortComplex_X₂))
    (by simp) (by simp))).1
    (L.cyclesComplexShortComplex_shortExact.homology_exact₁ (q + 1) q (by simp))
  mono_f := L.mono_δ_cyclesComplexShortComplex (by simp)
  epi_g := by dsimp; infer_instance

end Presentation

section Kunneth

variable (K L : ChainComplex (ModuleCat.{u} R) ℕ)

/-
The proof is Weibel's.  The sequence `0 ⟶ Z(L) ⟶ L ⟶ L / Z(L) ⟶ 0` is split in each degree, so it
stays exact after tensoring with `K`.  Its outer terms have zero differentials and flat terms, so
the Künneth maps of `K ⊗ Z(L)` and `K ⊗ (L / Z(L))` are isomorphisms
(`HomologicalComplex.isIso_homologyKunneth_of_d_eq_zero_of_flat_right`).  Through them, the
connecting morphisms of the long exact homology sequence of `K ⊗ Z(L) ⟶ K ⊗ L ⟶ K ⊗ (L / Z(L))`
become, up to the sign `(-1)ᵖ`, the sums over `p + q = m` of the maps
`Hₚ(K) ⊗ H_{q+1}(L / Z(L)) ⟶ Hₚ(K) ⊗ H_q(Z(L))` obtained by tensoring `Hₚ(K)` with
the projective presentations

`0 ⟶ H_{q+1}(L / Z(L)) ⟶ H_q(Z(L)) ⟶ H_q(L) ⟶ 0`

(`HomologicalComplex.homologyPresentation`).  By right exactness the cokernel of such a map is
`Hₚ(K) ⊗ H_q(L)`, which makes the Künneth map of `K` and `L` a monomorphism
(`HomologicalComplex.mono_homologyKunneth`).  The kernel of each tensorized presentation map
`Hₚ(K) ⊗ H_{q+1}(L / Z(L)) ⟶ Hₚ(K) ⊗ H_q(Z(L))` is `Tor₁(Hₚ(K), H_q(L))`
(`CategoryTheory.ShortComplex.ShortExact.torOneIsoKernel`).  The map
`Hₘ₊₁(K ⊗ L) ⟶ ⨁ Hₚ(K) ⊗ H_{q+1}(L / Z(L))` induced by `L ⟶ L / Z(L)` factors through the direct
sum of these kernels, which defines `HomologicalComplex.homologyToTor`.  Sums over the finitely
many pairs `(p, q)` preserve these exact sequences (`CategoryTheory.GradedObject.exact_mapMap`).
-/

/-- The module `⨁_{p + q = m} Tor₁(Hₚ(K), H_q(L))`, the third term of the Künneth short exact
sequence (`HomologicalComplex.homologyKunnethShortComplex_shortExact`). -/
abbrev homologyTor (m : ℕ) : ModuleCat.{u} R :=
  GradedObject.mapBifunctorMapObj (Tor (ModuleCat.{u} R) 1) (fun x ↦ x.1 + x.2)
    (fun p ↦ K.homology p) (fun q ↦ L.homology q) m

/-- Sums over the finitely many pairs `(p, q)` with `p + q = m` are exact. -/
private instance (m : ℕ) : HasExactColimitsOfShape
    (Discrete ((fun x : ℕ × ℕ ↦ x.1 + x.2) ⁻¹' {m})) (ModuleCat.{u} R) :=
  have := ((Finset.antidiagonal m).finite_toSet.subset
    (t := (fun x : ℕ × ℕ ↦ x.1 + x.2) ⁻¹' {m}) fun x hx ↦ by simpa using hx).to_subtype
  @hasExactColimitsOfShape_discrete_finite _ _ _ Abelian.hasFiniteBiproducts _ _

/-- The map `⨁ Hₚ(K) ⊗ H_{q+1}(L / Z(L)) ⟶ ⨁ Hₚ(K) ⊗ H_q(Z(L))` of degree `m` induced by the
connecting morphisms of `0 ⟶ Z(L) ⟶ L ⟶ L / Z(L) ⟶ 0`. -/
private abbrev tensorδ (m : ℕ) :=
  GradedObject.Monoidal.tensorHom (𝟙 (fun p ↦ K.homology p))
    (fun q ↦ (L.homologyPresentation q).f) m

/-- The map `⨁ Hₚ(K) ⊗ H_q(Z(L)) ⟶ ⨁ Hₚ(K) ⊗ H_q(L)` of degree `m` induced by the inclusion of
the cycles. -/
private abbrev tensorπ (m : ℕ) :=
  GradedObject.Monoidal.tensorHom (𝟙 (fun p ↦ K.homology p))
    (fun q ↦ (L.homologyPresentation q).g) m

private lemma whiskerLeft_homologyPresentation_zero (x : ℕ × ℕ) :
    K.homology x.1 ◁ (L.homologyPresentation x.2).f ≫
      K.homology x.1 ◁ (L.homologyPresentation x.2).g = 0 := by
  rw [← whiskerLeft_comp, (L.homologyPresentation x.2).zero, MonoidalPreadditive.whiskerLeft_zero]

/-- The graded short complex `Hₚ(K) ⊗ H_{q+1}(L / Z(L)) ⟶ Hₚ(K) ⊗ H_q(Z(L)) ⟶ Hₚ(K) ⊗ H_q(L)`
indexed by `(p, q)`. -/
private def tensorShortComplex : ShortComplex (GradedObject (ℕ × ℕ) (ModuleCat.{u} R)) :=
  ShortComplex.mk
    (((GradedObject.mapBifunctor (curriedTensor _) ℕ ℕ).obj (fun p ↦ K.homology p)).map
      (fun q ↦ (L.homologyPresentation q).f))
    (((GradedObject.mapBifunctor (curriedTensor _) ℕ ℕ).obj (fun p ↦ K.homology p)).map
      (fun q ↦ (L.homologyPresentation q).g))
    (funext (whiskerLeft_homologyPresentation_zero K L))

private lemma tensorShortComplex_exact (x : ℕ × ℕ) :
    (ShortComplex.mk ((tensorShortComplex K L).f x) ((tensorShortComplex K L).g x)
      (congr_fun (tensorShortComplex K L).zero x)).Exact :=
  have := CategoryWithHomology.hasHomology
    ((L.homologyPresentation x.2).map (tensorLeft (K.homology x.1)))
  (L.homologyPresentation_shortExact x.2).exact.map_of_epi_of_preservesCokernel
    (tensorLeft (K.homology x.1)) (L.homologyPresentation_shortExact x.2).epi_g inferInstance

private lemma tensorδ_comp_tensorπ (m : ℕ) : tensorδ K L m ≫ tensorπ K L m = 0 := by
  refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ?_
  simp [← whiskerLeft_comp_assoc]

/-- Right exactness of the tensor product: `⨁ Hₚ(K) ⊗ H_q(L)` is the cokernel of `tensorδ`. -/
private lemma tensorπ_exact (m : ℕ) :
    (ShortComplex.mk _ _ (tensorδ_comp_tensorπ K L m)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (GradedObject.exact_mapMap (tensorShortComplex K L) (fun x ↦ x.1 + x.2) m
      (tensorShortComplex_exact K L))
  -- the coproducts over the fibre of `m` are the terms of the tensor products of degree `m`
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans ((GradedObject.Monoidal.id_tensorHom_eq_mapMap _ _ m).trans
      (Category.comp_id _).symm))
    ((Category.id_comp _).trans ((GradedObject.Monoidal.id_tensorHom_eq_mapMap _ _ m).trans
      (Category.comp_id _).symm))

private instance (m : ℕ) : Epi (tensorπ K L m) := by
  rw [tensorπ, GradedObject.Monoidal.id_tensorHom_eq_mapMap]
  have (x : ℕ × ℕ) : Epi ((((GradedObject.mapBifunctor (curriedTensor _) ℕ ℕ).obj
      (fun p ↦ K.homology p)).map (fun q ↦ (L.homologyPresentation q).g)) x) := by
    have : (tensorLeft (K.homology x.1)).PreservesEpimorphisms :=
      Functor.preservesEpimorphisms_of_isLeftAdjoint _
    have := (L.homologyPresentation_shortExact x.2).epi_g
    exact (tensorLeft (K.homology x.1)).map_epi (L.homologyPresentation x.2).g
  exact GradedObject.epi_mapMap _ _ m

/-- The reindexing `⨁ Hₚ(K) ⊗ H_{q+1}(L / Z(L)) ≅ ⨁ Hₚ(K) ⊗ H_q(L / Z(L))` from degree `m` to
degree `m + 1`, which holds since `H₀(L / Z(L)) = 0`. -/
private abbrev succIso (m : ℕ) :=
  GradedObject.Monoidal.tensorObjSuccIso (fun p ↦ K.homology p)
    (fun q ↦ L.cyclesComplexShortComplex.X₃.homology q)
    L.isZero_homology_cyclesComplexShortComplex_X₃_zero m

/-- Multiplication by the sign `ε(p) = (-1)ᵖ` on the summand `Hₚ(K) ⊗ H_{q+1}(L / Z(L))`. -/
private abbrev signHom (m : ℕ) :=
  GradedObject.Monoidal.tensorHom (homologySign K)
    (𝟙 (fun q ↦ L.cyclesComplexShortComplex.X₃.homology (q + 1))) m

private lemma signHom_comp_signHom (m : ℕ) : signHom K L m ≫ signHom K L m = 𝟙 _ := by
  refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ?_
  simp only [GradedObject.Monoidal.ι_tensorHom_assoc, GradedObject.Monoidal.ι_tensorHom,
    zsmul_tensorHom, Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul]
  simp [← mul_pow]

private instance (m : ℕ) : IsIso (signHom K L m) :=
  ⟨signHom K L m, signHom_comp_signHom K L m, signHom_comp_signHom K L m⟩

/-- The identification of the middle term `K ⊗ L` of `K ⊗ Z(L) ⟶ K ⊗ L ⟶ K ⊗ (L / Z(L))`. -/
private abbrev middleIso (n : ℕ) :
    (tensorObj K L.cyclesComplexShortComplex.X₂).homology n ≅ (tensorObj K L).homology n :=
  eqToIso (congrArg (fun M ↦ (tensorObj K M).homology n) L.cyclesComplexShortComplex_X₂)

/-- The inclusion of the cycles of `L`, read through the Künneth maps. -/
private lemma tensorπ_comp_homologyKunneth (n : ℕ) :
    tensorπ K L n ≫ homologyKunneth K L n =
      homologyKunneth K L.cyclesComplexShortComplex.X₁ n ≫
        homologyMap (tensorLeftShortComplex K L.cyclesComplexShortComplex).f n ≫
          (middleIso K L n).hom := by
  have h₁ : GradedObject.Monoidal.tensorHom (𝟙 (fun p ↦ K.homology p))
      (fun q ↦ homologyMap L.cyclesComplexShortComplex.f q) n ≫
        homologyKunneth K L.cyclesComplexShortComplex.X₂ n =
      homologyKunneth K L.cyclesComplexShortComplex.X₁ n ≫
        homologyMap (tensorHom (𝟙 K) L.cyclesComplexShortComplex.f) n := by
    have := homologyKunneth_naturality (𝟙 K) L.cyclesComplexShortComplex.f n
    simp only [homologyMap_id] at this
    exact this
  have h₂ : tensorπ K L n = GradedObject.Monoidal.tensorHom (𝟙 (fun p ↦ K.homology p))
      (fun q ↦ homologyMap L.cyclesComplexShortComplex.f q) n ≫
        GradedObject.Monoidal.tensorHom (𝟙 (fun p ↦ K.homology p))
          (fun q ↦ eqToHom (congrArg (fun M ↦ M.homology q) L.cyclesComplexShortComplex_X₂)) n := by
    refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ?_
    simp
  rw [h₂, Category.assoc, ← homologyKunneth_comp_eqToHom K L.cyclesComplexShortComplex_X₂,
    reassoc_of% h₁, eqToIso.hom]

variable [∀ q, Projective (cokernel (L.iCycles q))]

/-- `K ⊗ Z(L) ⟶ K ⊗ L ⟶ K ⊗ (L / Z(L))` is short exact: since `L / Z(L)` has projective terms,
the cycles split off `L`. -/
private lemma shortExact_tensorLeft_cycles :
    (tensorLeftShortComplex K L.cyclesComplexShortComplex).ShortExact :=
  shortExact_tensorLeftShortComplex K L.cyclesComplexShortComplex_shortExact

/-- The connecting morphism of `K ⊗ Z(L) ⟶ K ⊗ L ⟶ K ⊗ (L / Z(L))`, read through the Künneth
maps. -/
private lemma homologyKunneth_comp_δ_cycles (m : ℕ) :
    homologyKunneth K L.cyclesComplexShortComplex.X₃ (m + 1) ≫
        (shortExact_tensorLeft_cycles K L).δ (m + 1) m (by simp) =
      (succIso K L m).inv ≫ signHom K L m ≫ tensorδ K L m ≫
        homologyKunneth K L.cyclesComplexShortComplex.X₁ m := by
  rw [homologyKunneth_comp_δ (shortExact_tensorLeft_cycles K L) m, ← Category.assoc (signHom _ _ _)]
  congr 2
  refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ?_
  simp only [GradedObject.Monoidal.ι_tensorHom_assoc, GradedObject.Monoidal.ι_tensorHom,
    zsmul_tensorHom, Preadditive.zsmul_comp]
  simp

private instance (n : ℕ) : IsIso (homologyKunneth K L.cyclesComplexShortComplex.X₃ n) :=
  have (q : ℕ) : Module.Flat R (L.cyclesComplexShortComplex.X₃.X q) := by
    rw [cyclesComplexShortComplex_X₃]
    exact inferInstanceAs (Module.Flat R (cokernel (L.iCycles q) : ModuleCat.{u} R))
  isIso_homologyKunneth_of_d_eq_zero_of_flat_right _ _ (by simp) n

/-- The identification `Hₙ₊₁(K ⊗ (L / Z(L))) ≅ ⨁ Hₚ(K) ⊗ H_{q+1}(L / Z(L))` of degree `n`: the
inverse Künneth isomorphism, the reindexing `succIso` and the sign `ε(p)`. -/
private def quotientIso (n : ℕ) :
    (tensorObj K L.cyclesComplexShortComplex.X₃).homology (n + 1) ≅
      GradedObject.Monoidal.tensorObj (fun p ↦ K.homology p)
        (fun q ↦ L.cyclesComplexShortComplex.X₃.homology (q + 1)) n :=
  (asIso (homologyKunneth K L.cyclesComplexShortComplex.X₃ (n + 1))).symm ≪≫
    (succIso K L n).symm ≪≫ asIso (signHom K L n)

variable [∀ q, Projective (L.cycles q)]

private instance (n : ℕ) : IsIso (homologyKunneth K L.cyclesComplexShortComplex.X₁ n) :=
  have (q : ℕ) : Module.Flat R (L.cyclesComplexShortComplex.X₁.X q) := by
    rw [cyclesComplexShortComplex_X₁]
    exact inferInstanceAs (Module.Flat R (L.cycles q))
  isIso_homologyKunneth_of_d_eq_zero_of_flat_right _ _ (by simp) n

private instance (q : ℕ) : Projective (L.homologyPresentation q).X₁ :=
  Projective.of_iso ((L.cyclesComplexShortComplex.X₃.iCyclesIso (q + 1) _ rfl (by simp)).symm ≪≫
    L.cyclesComplexShortComplex.X₃.isoHomologyπ _ (q + 1) rfl (by simp))
    (by simpa using (inferInstance : Projective (cokernel (L.iCycles (q + 1)))))

private instance (q : ℕ) : Projective (L.homologyPresentation q).X₂ :=
  Projective.of_iso ((L.cyclesComplexShortComplex.X₁.iCyclesIso q _ rfl (by simp)).symm ≪≫
    L.cyclesComplexShortComplex.X₁.isoHomologyπ _ q rfl (by simp))
    (by simpa using (inferInstance : Projective (L.cycles q)))

/-- The connecting morphism of `K ⊗ Z(L) ⟶ K ⊗ L ⟶ K ⊗ (L / Z(L))` is `tensorδ`, read through
`quotientIso` and the Künneth isomorphism for `Z(L)`. -/
private lemma quotientIso_hom_comp_tensorδ (n : ℕ) :
    (quotientIso K L n).hom ≫ tensorδ K L n =
      (shortExact_tensorLeft_cycles K L).δ (n + 1) n (by simp) ≫
        inv (homologyKunneth K L.cyclesComplexShortComplex.X₁ n) := by
  rw [← cancel_mono (homologyKunneth K L.cyclesComplexShortComplex.X₁ n)]
  simp only [quotientIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Category.assoc,
    IsIso.inv_hom_id, Category.comp_id, ← homologyKunneth_comp_δ_cycles, IsIso.inv_hom_id_assoc]

omit [∀ q, Projective (cokernel (L.iCycles q))] in
/-- The inclusion of the cycles, read through the Künneth isomorphism for `Z(L)`. -/
@[reassoc]
private lemma inv_homologyKunneth_comp_tensorπ (n : ℕ) :
    inv (homologyKunneth K L.cyclesComplexShortComplex.X₁ n) ≫
      tensorπ K L n ≫ homologyKunneth K L n =
        homologyMap (tensorLeftShortComplex K L.cyclesComplexShortComplex).f n ≫
          (middleIso K L n).hom := by
  rw [tensorπ_comp_homologyKunneth, IsIso.inv_hom_id_assoc]

/-- In the long exact homology sequence of `K ⊗ Z(L) ⟶ K ⊗ L ⟶ K ⊗ (L / Z(L))`, the piece
`Hₙ₊₁(K ⊗ (L / Z(L))) ⟶ Hₙ(K ⊗ Z(L)) ⟶ Hₙ(K ⊗ L)`, read through the Künneth isomorphisms. -/
private lemma tensorδ_exact_homologyKunneth (n : ℕ) :
    (ShortComplex.mk (tensorδ K L n) (tensorπ K L n ≫ homologyKunneth K L n)
      (by rw [← Category.assoc, tensorδ_comp_tensorπ, zero_comp])).Exact :=
  (ShortComplex.exact_iff_of_epi_of_isIso_of_mono (ShortComplex.Hom.mk
    (S₁ := ShortComplex.mk _ _ ((shortExact_tensorLeft_cycles K L).δ_comp (n + 1) n (by simp)))
    (S₂ := ShortComplex.mk (tensorδ K L n) (tensorπ K L n ≫ homologyKunneth K L n)
      (by rw [← Category.assoc, tensorδ_comp_tensorπ, zero_comp]))
    (quotientIso K L n).hom (asIso (homologyKunneth K L.cyclesComplexShortComplex.X₁ n)).inv
    (middleIso K L n).hom (quotientIso_hom_comp_tensorδ K L n)
    (inv_homologyKunneth_comp_tensorπ K L n))).1
    ((shortExact_tensorLeft_cycles K L).homology_exact₁ (n + 1) n (by simp))

/-- **The Künneth map is a monomorphism** when the cycles and the quotients `L_q / Z_q(L)` of `L`
are projective, for instance for a complex `L` of projective modules over a principal ideal
domain.  No hypothesis is imposed on `K`; compare `HomologicalComplex.isSplitMono_homologyKunneth`,
which assumes that the cycles of both complexes split off and gives a split monomorphism. -/
theorem mono_homologyKunneth (n : ℕ) : Mono (homologyKunneth K L n) := by
  have hc := (tensorπ_exact K L n).gIsCokernel
  have hm := (tensorδ_exact_homologyKunneth K L n).mono_cokernelDesc
  -- the cokernel of `tensorδ` is `⨁ Hₚ(K) ⊗ H_q(L)`, and the induced map is the Künneth map
  have : cokernel.desc (tensorδ K L n) (tensorπ K L n ≫ homologyKunneth K L n)
      (by rw [← Category.assoc, tensorδ_comp_tensorπ, zero_comp]) =
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _) hc).hom ≫
        homologyKunneth K L n :=
    (IsColimit.coconePointUniqueUpToIso_hom_desc _ hc).symm.trans
      (_ ≫= Cofork.IsColimit.hom_ext hc ((Cofork.IsColimit.π_desc hc).trans (by simp)))
  simpa only [this, mono_comp_iff_of_isIso] using hm

/-- The summand inclusion `Tor₁(Hₚ(K), H_q(L)) ⟶ Hₚ(K) ⊗ H_{q+1}(L / Z(L))`, identifying `Tor₁`
with the kernel of `Hₚ(K) ⊗ H_{q+1}(L / Z(L)) ⟶ Hₚ(K) ⊗ H_q(Z(L))` through the projective
presentation `HomologicalComplex.homologyPresentation`. -/
private def torι (x : ℕ × ℕ) :
    ((Tor (ModuleCat.{u} R) 1).obj (K.homology x.1)).obj (L.homology x.2) ⟶
      K.homology x.1 ⊗ (L.homologyPresentation x.2).X₁ :=
  ((L.homologyPresentation_shortExact x.2).torOneIsoKernel (K.homology x.1)).hom ≫ kernel.ι _

private lemma torι_comp (x : ℕ × ℕ) :
    torι K L x ≫ (K.homology x.1 ◁ (L.homologyPresentation x.2).f) = 0 := by
  simp [torι]

/-- The inclusions `torι`, as a morphism of graded objects indexed by `(p, q)`. -/
private def torGradedι : ((GradedObject.mapBifunctor (Tor (ModuleCat.{u} R) 1) ℕ ℕ).obj
      (fun p ↦ K.homology p)).obj (fun q ↦ L.homology q) ⟶
    ((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} R)) ℕ ℕ).obj
      (fun p ↦ K.homology p)).obj (fun q ↦ (L.homologyPresentation q).X₁) :=
  fun x ↦ torι K L x

/-- The graded short complex `Tor₁(Hₚ(K), H_q(L)) ⟶ Hₚ(K) ⊗ H_{q+1}(L / Z(L)) ⟶ Hₚ(K) ⊗ H_q(Z(L))`
indexed by `(p, q)`. -/
private def torShortComplex : ShortComplex (GradedObject (ℕ × ℕ) (ModuleCat.{u} R)) :=
  ShortComplex.mk (torGradedι K L) (tensorShortComplex K L).f (funext (torι_comp K L))

private lemma torShortComplex_exact (x : ℕ × ℕ) :
    (ShortComplex.mk ((torShortComplex K L).f x) ((torShortComplex K L).g x)
      (congr_fun (torShortComplex K L).zero x)).Exact := by
  refine (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
    (S₁ := ShortComplex.mk _ _ (kernel.condition (K.homology x.1 ◁ (L.homologyPresentation x.2).f)))
    (S₂ := ShortComplex.mk ((torShortComplex K L).f x) ((torShortComplex K L).g x)
      (congr_fun (torShortComplex K L).zero x))
    ((L.homologyPresentation_shortExact x.2).torOneIsoKernel (K.homology x.1)).symm (Iso.refl _)
    (Iso.refl _) ?_ ?_)).1 (ShortComplex.exact_kernel _)
  · exact (Iso.inv_hom_id_assoc _ _).trans (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The inclusion `⨁ Tor₁(Hₚ(K), H_q(L)) ⟶ ⨁ Hₚ(K) ⊗ H_{q+1}(L / Z(L))` of degree `m`. -/
private def torToTensor (m : ℕ) :
    homologyTor K L m ⟶ GradedObject.Monoidal.tensorObj (fun p ↦ K.homology p)
      (fun q ↦ L.cyclesComplexShortComplex.X₃.homology (q + 1)) m :=
  GradedObject.mapMap (torGradedι K L) (fun x ↦ x.1 + x.2) m

private lemma torToTensor_comp_tensorδ (m : ℕ) : torToTensor K L m ≫ tensorδ K L m = 0 := by
  rw [tensorδ, GradedObject.Monoidal.id_tensorHom_eq_mapMap, torToTensor]
  refine GradedObject.mapObj_ext _ _ _ _ fun x _ ↦ ?_
  -- `erw`: the components of `mapMap` are morphisms of the graded category, whose hom types are
  -- those of `ModuleCat R` only up to unfolding
  erw [GradedObject.ι_mapMap_assoc, GradedObject.ι_mapMap, ← Category.assoc, ← Pi.comp_apply,
    (torShortComplex K L).zero]
  exact zero_comp.trans comp_zero.symm

/-- `⨁ Tor₁(Hₚ(K), H_q(L))` is the kernel of `tensorδ`. -/
private lemma torToTensor_exact (m : ℕ) :
    (ShortComplex.mk _ _ (torToTensor_comp_tensorδ K L m)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (GradedObject.exact_mapMap (torShortComplex K L) (fun x ↦ x.1 + x.2) m
      (torShortComplex_exact K L))
  -- the coproducts over the fibre of `m` are the terms of the tensor products of degree `m`
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans ((GradedObject.Monoidal.id_tensorHom_eq_mapMap _ _ m).trans
      (Category.comp_id _).symm))

private instance (m : ℕ) : Mono (torToTensor K L m) := by
  have (x : ℕ × ℕ) : Mono (torGradedι K L x) := mono_comp
    ((L.homologyPresentation_shortExact x.2).torOneIsoKernel (K.homology x.1)).hom (kernel.ι _)
  exact GradedObject.mono_mapMap _ _ m

/-- The inclusion `⨁_{p + q = m} Tor₁(Hₚ(K), H_q(L)) ⟶ Hₘ₊₁(K ⊗ (L / Z(L)))` which characterizes
`HomologicalComplex.homologyToTor`
(`HomologicalComplex.homologyToTor_comp_homologyTorToHomologyQuotient`): the inclusion of
`Tor₁(Hₚ(K), H_q(L))` into `Hₚ(K) ⊗ H_{q+1}(L / Z(L))` given by the projective presentation
`HomologicalComplex.homologyPresentation`, followed by the sign `ε(p)` and the Künneth isomorphism
of `K` and `L / Z(L)`. -/
def homologyTorToHomologyQuotient (m : ℕ) :
    homologyTor K L m ⟶ (tensorObj K L.cyclesComplexShortComplex.X₃).homology (m + 1) :=
  torToTensor K L m ≫ (quotientIso K L m).inv

instance (m : ℕ) : Mono (homologyTorToHomologyQuotient K L m) := by
  rw [homologyTorToHomologyQuotient]
  infer_instance

/-- `⨁ Tor₁(Hₚ(K), H_q(L))` is the kernel of `tensorδ`, as a limit. -/
private def torIsKernel (m : ℕ) :
    IsLimit (KernelFork.ofι (torToTensor K L m) (torToTensor_comp_tensorδ K L m)) :=
  (torToTensor_exact K L m).fIsKernel

/-- The map `Hₘ₊₁(K ⊗ L) ⟶ ⨁ Hₚ(K) ⊗ H_{q+1}(L / Z(L))` induced by the projection of `L` onto
`L / Z(L)`, read through `quotientIso`. -/
private def toTensorQuotient (m : ℕ) :
    (tensorObj K L).homology (m + 1) ⟶ GradedObject.Monoidal.tensorObj (fun p ↦ K.homology p)
      (fun q ↦ L.cyclesComplexShortComplex.X₃.homology (q + 1)) m :=
  (middleIso K L (m + 1)).inv ≫
    homologyMap (tensorLeftShortComplex K L.cyclesComplexShortComplex).g (m + 1) ≫
      (quotientIso K L m).hom

private lemma toTensorQuotient_comp_tensorδ (m : ℕ) :
    toTensorQuotient K L m ≫ tensorδ K L m = 0 := by
  rw [toTensorQuotient, Category.assoc, Category.assoc, quotientIso_hom_comp_tensorδ,
    (shortExact_tensorLeft_cycles K L).comp_δ_assoc, zero_comp, comp_zero]

private lemma homologyKunneth_comp_toTensorQuotient (m : ℕ) :
    homologyKunneth K L (m + 1) ≫ toTensorQuotient K L m = 0 := by
  rw [← cancel_epi (inv (homologyKunneth K L.cyclesComplexShortComplex.X₁ (m + 1)) ≫
    tensorπ K L (m + 1)), comp_zero, Category.assoc, inv_homologyKunneth_comp_tensorπ_assoc,
    toTensorQuotient, Iso.hom_inv_id_assoc, ← homologyMap_comp_assoc,
    (tensorLeftShortComplex K L.cyclesComplexShortComplex).zero, homologyMap_zero, zero_comp]

/-- The second map `Hₘ₊₁(K ⊗ L) ⟶ ⨁_{p + q = m} Tor₁(Hₚ(K), H_q(L))` of the Künneth short exact
sequence (`HomologicalComplex.homologyKunnethShortComplex_shortExact`).  It is induced by the
projection of `L` onto `L / Z(L)`: its image lies in the kernel of the map
`⨁ Hₚ(K) ⊗ H_{q+1}(L / Z(L)) ⟶ ⨁ Hₚ(K) ⊗ H_q(Z(L))` given by the connecting morphisms, and this
kernel is `⨁ Tor₁(Hₚ(K), H_q(L))` through the projective presentations
`HomologicalComplex.homologyPresentation`. -/
def homologyToTor (m : ℕ) : (tensorObj K L).homology (m + 1) ⟶ homologyTor K L m :=
  (torIsKernel K L m).lift (KernelFork.ofι _ (toTensorQuotient_comp_tensorδ K L m))

@[reassoc]
private lemma homologyToTor_comp_torToTensor (m : ℕ) :
    homologyToTor K L m ≫ torToTensor K L m = toTensorQuotient K L m :=
  Fork.IsLimit.lift_ι (torIsKernel K L m)

/-- `HomologicalComplex.homologyToTor` followed by the inclusion
`HomologicalComplex.homologyTorToHomologyQuotient` is the map `Hₘ₊₁(K ⊗ L) ⟶ Hₘ₊₁(K ⊗ (L / Z(L)))`
induced by the projection of `L` onto `L / Z(L)`. -/
@[reassoc (attr := simp)]
lemma homologyToTor_comp_homologyTorToHomologyQuotient (m : ℕ) :
    homologyToTor K L m ≫ homologyTorToHomologyQuotient K L m =
      eqToHom (congrArg (fun M ↦ (tensorObj K M).homology (m + 1))
          L.cyclesComplexShortComplex_X₂.symm) ≫
        homologyMap (tensorLeftShortComplex K L.cyclesComplexShortComplex).g (m + 1) := by
  simp [homologyTorToHomologyQuotient, homologyToTor_comp_torToTensor_assoc, toTensorQuotient]

/-- `HomologicalComplex.homologyToTor` is the unique morphism whose composite with
`HomologicalComplex.homologyTorToHomologyQuotient` is the map induced by the projection of `L`
onto `L / Z(L)`. -/
lemma homologyToTor_unique {m : ℕ} (f : (tensorObj K L).homology (m + 1) ⟶ homologyTor K L m)
    (hf : f ≫ homologyTorToHomologyQuotient K L m =
      eqToHom (congrArg (fun M ↦ (tensorObj K M).homology (m + 1))
          L.cyclesComplexShortComplex_X₂.symm) ≫
        homologyMap (tensorLeftShortComplex K L.cyclesComplexShortComplex).g (m + 1)) :
    f = homologyToTor K L m := by
  rw [← cancel_mono (homologyTorToHomologyQuotient K L m), hf,
    homologyToTor_comp_homologyTorToHomologyQuotient]

/-- The Künneth map followed by the map to `⨁ Tor₁(Hₚ(K), H_q(L))` vanishes. -/
@[reassoc (attr := simp)]
lemma homologyKunneth_comp_homologyToTor (m : ℕ) :
    homologyKunneth K L (m + 1) ≫ homologyToTor K L m = 0 := by
  rw [← cancel_mono (torToTensor K L m), Category.assoc, homologyToTor_comp_torToTensor,
    homologyKunneth_comp_toTensorQuotient, zero_comp]

section Naturality

/-
The map `HomologicalComplex.homologyToTor` is characterized by its composite with the
monomorphism `HomologicalComplex.homologyTorToHomologyQuotient`, so its naturality reduces to that
of `homologyTorToHomologyQuotient`.  A chain map `ψ : L ⟶ L'` induces a morphism of cycle
sequences (`HomologicalComplex.cyclesComplexShortComplexMap`), hence a morphism of the projective
presentations `HomologicalComplex.homologyPresentation`, and the identification of `Tor₁` with a
kernel is natural in such morphisms and in the first variable
(`CategoryTheory.ShortComplex.ShortExact.Tor_obj_map_comp_torOneIsoKernel_hom` and
`CategoryTheory.ShortComplex.ShortExact.Tor_map_app_comp_torOneIsoKernel_hom`).
-/

variable {K L} {K' L' : ChainComplex (ModuleCat.{u} R) ℕ}
  [∀ q, Projective (cokernel (L'.iCycles q))] [∀ q, Projective (L'.cycles q)]
  (φ : K ⟶ K') (ψ : L ⟶ L')

omit [∀ q, Projective (cokernel (L.iCycles q))] [∀ q, Projective (L.cycles q)]
  [∀ q, Projective (cokernel (L'.iCycles q))] [∀ q, Projective (L'.cycles q)] in
/-- The morphism of presentations `homologyPresentation L q ⟶ homologyPresentation L' q` induced
by `ψ`. -/
@[simps]
private def homologyPresentationMap (q : ℕ) :
    L.homologyPresentation q ⟶ L'.homologyPresentation q where
  τ₁ := homologyMap (cyclesComplexShortComplexMap ψ).τ₃ (q + 1)
  τ₂ := homologyMap (cyclesComplexShortComplexMap ψ).τ₁ q
  τ₃ := homologyMap ψ q
  comm₁₂ := (HomologySequence.δ_naturality (cyclesComplexShortComplexMap ψ)
    L.cyclesComplexShortComplex_shortExact L'.cyclesComplexShortComplex_shortExact (q + 1) q
    (by simp)).symm
  comm₂₃ := by
    dsimp
    rw [← homologyMap_comp_assoc, (cyclesComplexShortComplexMap ψ).comm₁₂, homologyMap_comp_assoc,
      homologyMap_comp_eqToHom ψ L.cyclesComplexShortComplex_X₂ L'.cyclesComplexShortComplex_X₂ _
        (cyclesComplexShortComplexMap_τ₂ ψ), Category.assoc]

/-- The inclusion `torι` is natural. -/
private lemma torι_naturality (x : ℕ × ℕ) :
    ((Tor (ModuleCat.{u} R) 1).map (homologyMap φ x.1)).app (L.homology x.2) ≫
        ((Tor (ModuleCat.{u} R) 1).obj (K'.homology x.1)).map (homologyMap ψ x.2) ≫
          torι K' L' x =
      torι K L x ≫
        (homologyMap φ x.1 ⊗ₘ homologyMap (cyclesComplexShortComplexMap ψ).τ₃ (x.2 + 1)) := by
  have h := (L'.homologyPresentation_shortExact x.2).Tor_obj_map_comp_torOneIsoKernel_hom
    (hS := L.homologyPresentation_shortExact x.2) (K'.homology x.1) (homologyPresentationMap ψ x.2)
  rw [← homologyPresentationMap_τ₃ ψ x.2]
  simp only [torι, Category.assoc]
  rw [reassoc_of% h]
  refine ((L.homologyPresentation_shortExact x.2).Tor_map_app_comp_torOneIsoKernel_hom_assoc
    (homologyMap φ x.1) _).trans ?_
  simp [tensorHom_def]

/-- On the summand `Tor₁(Hₚ(K), H_q(L))`, `torToTensor` is the inclusion `torι`. -/
@[reassoc]
private lemma ι_torToTensor (p q m : ℕ) (h : p + q = m) :
    GradedObject.ιMapBifunctorMapObj (Tor (ModuleCat.{u} R) 1) (fun x ↦ x.1 + x.2)
        (fun p ↦ K.homology p) (fun q ↦ L.homology q) p q m h ≫ torToTensor K L m =
      torι K L (p, q) ≫ GradedObject.Monoidal.ιTensorObj (fun p ↦ K.homology p)
        (fun q ↦ L.cyclesComplexShortComplex.X₃.homology (q + 1)) p q m h := by
  -- `erw`: the components of `mapMap` are morphisms of the graded category, whose hom types are
  -- those of `ModuleCat R` only up to unfolding
  erw [GradedObject.ι_mapMap]
  rfl

/-- The inclusion `torToTensor` is natural. -/
@[reassoc]
private lemma torToTensor_naturality (m : ℕ) :
    GradedObject.mapBifunctorMapMap (Tor (ModuleCat.{u} R) 1) (fun x ↦ x.1 + x.2)
        (fun p ↦ homologyMap φ p) (fun q ↦ homologyMap ψ q) m ≫ torToTensor K' L' m =
      torToTensor K L m ≫ GradedObject.Monoidal.tensorHom (fun p ↦ homologyMap φ p)
        (fun q ↦ homologyMap (cyclesComplexShortComplexMap ψ).τ₃ (q + 1)) m := by
  refine GradedObject.mapBifunctorMapObj_ext _ _ fun p q h ↦ ?_
  rw [GradedObject.ι_mapBifunctorMapMap_assoc, ι_torToTensor, ι_torToTensor_assoc,
    GradedObject.Monoidal.ι_tensorHom, reassoc_of% torι_naturality φ ψ (p, q)]

omit [∀ q, Projective (L.cycles q)] [∀ q, Projective (L'.cycles q)] in
/-- The identification `quotientIso` is natural. -/
@[reassoc]
private lemma quotientIso_hom_naturality (n : ℕ) :
    (quotientIso K L n).hom ≫ GradedObject.Monoidal.tensorHom (fun p ↦ homologyMap φ p)
        (fun q ↦ homologyMap (cyclesComplexShortComplexMap ψ).τ₃ (q + 1)) n =
      homologyMap (tensorHom φ (cyclesComplexShortComplexMap ψ).τ₃) (n + 1) ≫
        (quotientIso K' L' n).hom := by
  rw [← cancel_epi (homologyKunneth K L.cyclesComplexShortComplex.X₃ (n + 1)),
    ← homologyKunneth_naturality_assoc]
  simp only [quotientIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Category.assoc,
    IsIso.hom_inv_id_assoc]
  refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ?_
  match q, h with
  | 0, _ =>
    -- the summand `Hₚ(K) ⊗ H₀(L / Z(L))` vanishes
    exact ((tensorLeft (K.homology p)).map_isZero
      L.isZero_homology_cyclesComplexShortComplex_X₃_zero).eq_of_src _ _
  | q + 1, h =>
    simp only [GradedObject.Monoidal.ι_tensorObjSuccIso_inv_assoc,
      GradedObject.Monoidal.ι_tensorHom_assoc, GradedObject.Monoidal.ι_tensorHom]
    simp [homologySign, -tensorHom_id]

/-- **Naturality of the inclusion characterizing `HomologicalComplex.homologyToTor`**: for chain
maps `φ : K ⟶ K'` and `ψ : L ⟶ L'`, the inclusion
`⨁ Tor₁(Hₚ(K), H_q(L)) ⟶ Hₘ₊₁(K ⊗ (L / Z(L)))` commutes with the maps induced by `φ` and `ψ`. -/
@[reassoc]
lemma homologyTorToHomologyQuotient_naturality (m : ℕ) :
    GradedObject.mapBifunctorMapMap (Tor (ModuleCat.{u} R) 1) (fun x ↦ x.1 + x.2)
        (fun p ↦ homologyMap φ p) (fun q ↦ homologyMap ψ q) m ≫
      homologyTorToHomologyQuotient K' L' m =
    homologyTorToHomologyQuotient K L m ≫
      homologyMap (tensorHom φ (cyclesComplexShortComplexMap ψ).τ₃) (m + 1) := by
  rw [homologyTorToHomologyQuotient, homologyTorToHomologyQuotient, torToTensor_naturality_assoc,
    Category.assoc]
  congr 1
  rw [Iso.eq_inv_comp, quotientIso_hom_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

omit [∀ q, Projective (cokernel (L.iCycles q))] [∀ q, Projective (L.cycles q)]
  [∀ q, Projective (cokernel (L'.iCycles q))] [∀ q, Projective (L'.cycles q)] in
/-- Tensoring the projections `L ⟶ L / Z(L)` and `L' ⟶ L' / Z(L')` with `K` and `K'` commutes with
the maps induced by `φ` and `ψ`. -/
@[reassoc]
private lemma tensorHom_id_g_comp_tensorHom :
    tensorHom (𝟙 K) L.cyclesComplexShortComplex.g ≫
        tensorHom φ (cyclesComplexShortComplexMap ψ).τ₃ =
      tensorHom φ (cyclesComplexShortComplexMap ψ).τ₂ ≫
        tensorHom (𝟙 K') L'.cyclesComplexShortComplex.g := by
  rw [← mapBifunctorMap_comp, ← mapBifunctorMap_comp, Category.id_comp, Category.comp_id,
    (cyclesComplexShortComplexMap ψ).comm₂₃]

/-- **Naturality of the Künneth short exact sequence**: the map
`HomologicalComplex.homologyToTor` to `⨁_{p + q = m} Tor₁(Hₚ(K), H_q(L))` is natural in both
complexes.  Together with the naturality of the Künneth map
(`HomologicalComplex.homologyKunneth_naturality`), this makes the Künneth short exact sequence
natural in `K` and `L` (`HomologicalComplex.homologyKunnethShortComplexMap`). -/
@[reassoc]
theorem homologyToTor_naturality (m : ℕ) :
    homologyMap (tensorHom φ ψ) (m + 1) ≫ homologyToTor K' L' m =
      homologyToTor K L m ≫ GradedObject.mapBifunctorMapMap (Tor (ModuleCat.{u} R) 1)
        (fun x ↦ x.1 + x.2) (fun p ↦ homologyMap φ p) (fun q ↦ homologyMap ψ q) m := by
  apply (cancel_mono (homologyTorToHomologyQuotient K' L' m)).1
  -- both sides are now maps `Hₘ₊₁(K ⊗ L) ⟶ Hₘ₊₁(K' ⊗ (L' / Z(L')))`; by the characterization of
  -- `homologyToTor` and the naturality of `homologyTorToHomologyQuotient`, it remains to commute
  -- `φ ⊗ ψ` with the maps induced by the projections `L ⟶ L / Z(L)` and `L' ⟶ L' / Z(L')`
  simp only [Category.assoc, homologyToTor_comp_homologyTorToHomologyQuotient,
    homologyTorToHomologyQuotient_naturality,
    homologyToTor_comp_homologyTorToHomologyQuotient_assoc]
  -- move `φ ⊗ ψ` past the identification of the middle terms, then past the projections
  simp only [← eqToHom_comp_homologyMap_tensorHom_assoc φ ψ L.cyclesComplexShortComplex_X₂
      L'.cyclesComplexShortComplex_X₂ _ (cyclesComplexShortComplexMap_τ₂ ψ) (m + 1),
    ← homologyMap_comp, tensorHom_id_g_comp_tensorHom]

end Naturality

/-- In the long exact homology sequence of `K ⊗ Z(L) ⟶ K ⊗ L ⟶ K ⊗ (L / Z(L))`, the piece
`Hₘ₊₁(K ⊗ L) ⟶ Hₘ₊₁(K ⊗ (L / Z(L))) ⟶ Hₘ(K ⊗ Z(L))`, read through the Künneth isomorphisms. -/
private lemma toTensorQuotient_exact (m : ℕ) :
    (ShortComplex.mk _ _ (toTensorQuotient_comp_tensorδ K L m)).Exact :=
  (ShortComplex.exact_iff_of_epi_of_isIso_of_mono (ShortComplex.Hom.mk
    (S₁ := ShortComplex.mk _ _ ((shortExact_tensorLeft_cycles K L).comp_δ (m + 1) m (by simp)))
    (S₂ := ShortComplex.mk _ _ (toTensorQuotient_comp_tensorδ K L m))
    (middleIso K L (m + 1)).hom (quotientIso K L m).hom
    (asIso (homologyKunneth K L.cyclesComplexShortComplex.X₁ m)).inv
    (by simp [toTensorQuotient]) (quotientIso_hom_comp_tensorδ K L m))).1
    ((shortExact_tensorLeft_cycles K L).homology_exact₃ (m + 1) m (by simp))

/-- In the long exact homology sequence of `K ⊗ Z(L) ⟶ K ⊗ L ⟶ K ⊗ (L / Z(L))`, the piece
`Hₘ₊₁(K ⊗ Z(L)) ⟶ Hₘ₊₁(K ⊗ L) ⟶ Hₘ₊₁(K ⊗ (L / Z(L)))`, read through the Künneth maps: its first
term becomes its quotient `⨁_{p + q = m + 1} Hₚ(K) ⊗ H_q(L)` and its first map the Künneth map. -/
private lemma homologyKunneth_exact_toTensorQuotient (m : ℕ) :
    (ShortComplex.mk _ _ (homologyKunneth_comp_toTensorQuotient K L m)).Exact :=
  -- the comparison maps from the long exact sequence are an epimorphism and two isomorphisms;
  -- these instances are supplied explicitly because synthesizing them is slow
  (@ShortComplex.exact_iff_of_epi_of_isIso_of_mono _ _ _ _ _ (ShortComplex.Hom.mk
    (S₂ := ShortComplex.mk _ _ (homologyKunneth_comp_toTensorQuotient K L m))
    (inv (homologyKunneth K L.cyclesComplexShortComplex.X₁ (m + 1)) ≫ tensorπ K L (m + 1))
    (middleIso K L (m + 1)).hom (quotientIso K L m).hom
    ((Category.assoc _ _ _).trans (inv_homologyKunneth_comp_tensorπ K L (m + 1)))
    (by simp [toTensorQuotient])) (epi_comp _ _) (Iso.isIso_hom _) (IsIso.mono_of_iso _)).1
    ((shortExact_tensorLeft_cycles K L).homology_exact₂ (m + 1))

/-- The Künneth short complex
`⨁_{p + q = m + 1} Hₚ(K) ⊗ H_q(L) ⟶ Hₘ₊₁(K ⊗ L) ⟶ ⨁_{p + q = m} Tor₁(Hₚ(K), H_q(L))`, formed by
the Künneth map and `HomologicalComplex.homologyToTor`. -/
abbrev homologyKunnethShortComplex (m : ℕ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk _ _ (homologyKunneth_comp_homologyToTor K L m)

/-- The second map `HomologicalComplex.homologyToTor` of the Künneth short complex is an
epimorphism. -/
private lemma epi_homologyToTor (m : ℕ) : Epi (homologyToTor K L m) := by
  -- `homologyToTor` is the lift of `toTensorQuotient` to the kernel `torToTensor` of `tensorδ`,
  -- an epimorphism since `toTensorQuotient` and `tensorδ` are exact (`toTensorQuotient_exact`)
  have := (toTensorQuotient_exact K L m).epi_kernelLift
  rw [homologyToTor, ← IsLimit.lift_comp_conePointUniqueUpToIso_hom (kernelIsKernel _)]
  -- `kernel.lift` abbreviates this `(kernelIsKernel _).lift` of a `KernelFork`, so the
  -- epimorphism instance from `epi_kernelLift` applies by definitional equality.
  infer_instance

/-- **The Künneth short exact sequence.**  Let `K` and `L` be chain complexes of modules over a
commutative ring, indexed by `ℕ`, such that the cycles `Z_q(L)` and the quotients `L_q / Z_q(L)`
are projective, for instance a complex `L` of projective modules over a principal ideal domain.
Then

`0 ⟶ ⨁_{p + q = m + 1} Hₚ(K) ⊗ H_q(L) ⟶ Hₘ₊₁(K ⊗ L) ⟶ ⨁_{p + q = m} Tor₁(Hₚ(K), H_q(L)) ⟶ 0`

is exact, the first map being the Künneth map and the second `HomologicalComplex.homologyToTor`.
-/
theorem homologyKunnethShortComplex_shortExact (m : ℕ) :
    (homologyKunnethShortComplex K L m).ShortExact where
  -- the sequence with `⨁ Tor₁(Hₚ(K), H_q(L))` replaced by `⨁ Hₚ(K) ⊗ H_{q+1}(L / Z(L))` is exact
  -- by the long exact homology sequence of `K ⊗ Z(L) ⟶ K ⊗ L ⟶ K ⊗ (L / Z(L))`
  exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono (ShortComplex.Hom.mk
    (S₁ := homologyKunnethShortComplex K L m)
    (S₂ := ShortComplex.mk _ _ (homologyKunneth_comp_toTensorQuotient K L m))
    (𝟙 _) (𝟙 _) (torToTensor K L m) (by simp)
    (by simp [homologyToTor_comp_torToTensor]))).2 (homologyKunneth_exact_toTensorQuotient K L m)
  mono_f := mono_homologyKunneth K L (m + 1)
  epi_g := epi_homologyToTor K L m

section ShortComplexMap

variable {K L} {K' L' : ChainComplex (ModuleCat.{u} R) ℕ}
  [∀ q, Projective (cokernel (L'.iCycles q))] [∀ q, Projective (L'.cycles q)]
  (φ : K ⟶ K') (ψ : L ⟶ L')

/-- The morphism of Künneth short complexes induced by chain maps `φ : K ⟶ K'` and `ψ : L ⟶ L'`:
the maps `Hₚ(φ) ⊗ H_q(ψ)` on `⨁ Hₚ(K) ⊗ H_q(L)`, the map induced by `φ ⊗ ψ` on `Hₘ₊₁(K ⊗ L)` and
`Tor₁(Hₚ(φ), H_q(ψ))` on `⨁ Tor₁(Hₚ(K), H_q(L))`.  Together with
`HomologicalComplex.homologyKunnethShortComplex_shortExact` this makes the Künneth short exact
sequence natural in both complexes. -/
def homologyKunnethShortComplexMap (m : ℕ) :
    homologyKunnethShortComplex K L m ⟶ homologyKunnethShortComplex K' L' m where
  τ₁ := GradedObject.Monoidal.tensorHom (fun p ↦ homologyMap φ p) (fun q ↦ homologyMap ψ q) (m + 1)
  τ₂ := homologyMap (tensorHom φ ψ) (m + 1)
  τ₃ := GradedObject.mapBifunctorMapMap (Tor (ModuleCat.{u} R) 1) (fun x ↦ x.1 + x.2)
    (fun p ↦ homologyMap φ p) (fun q ↦ homologyMap ψ q) m
  comm₁₂ := homologyKunneth_naturality φ ψ (m + 1)
  comm₂₃ := homologyToTor_naturality φ ψ m

/-- On `⨁ Hₚ(K) ⊗ H_q(L)`, the morphism of Künneth short complexes is `Hₚ(φ) ⊗ H_q(ψ)`. -/
@[simp]
lemma homologyKunnethShortComplexMap_τ₁ (m : ℕ) :
    (homologyKunnethShortComplexMap φ ψ m).τ₁ =
      GradedObject.Monoidal.tensorHom (fun p ↦ homologyMap φ p) (fun q ↦ homologyMap ψ q)
        (m + 1) :=
  (rfl)

/-- On `Hₘ₊₁(K ⊗ L)`, the morphism of Künneth short complexes is the map induced by `φ ⊗ ψ`. -/
@[simp]
lemma homologyKunnethShortComplexMap_τ₂ (m : ℕ) :
    (homologyKunnethShortComplexMap φ ψ m).τ₂ = homologyMap (tensorHom φ ψ) (m + 1) :=
  (rfl)

/-- On `⨁ Tor₁(Hₚ(K), H_q(L))`, the morphism of Künneth short complexes is
`Tor₁(Hₚ(φ), H_q(ψ))`. -/
@[simp]
lemma homologyKunnethShortComplexMap_τ₃ (m : ℕ) :
    (homologyKunnethShortComplexMap φ ψ m).τ₃ =
      GradedObject.mapBifunctorMapMap (Tor (ModuleCat.{u} R) 1) (fun x ↦ x.1 + x.2)
        (fun p ↦ homologyMap φ p) (fun q ↦ homologyMap ψ q) m :=
  (rfl)

end ShortComplexMap

variable [∀ p, IsSplitMono (K.iCycles p)]

/-- **The Künneth short exact sequence splits** when, in addition, the cycles of `K` split off its
terms; for instance for complexes `K` and `L` of projective modules over a principal ideal domain.
The splitting comes from a retraction of the Künneth map
(`HomologicalComplex.isSplitMono_homologyKunneth`) built from chosen splittings of the cycles, so
it need not be natural in `K` and `L`. -/
def homologyKunnethShortComplexSplitting (m : ℕ) : (homologyKunnethShortComplex K L m).Splitting :=
  have := isSplitMono_homologyKunneth K L (m + 1)
  .ofExactOfRetraction _ (homologyKunnethShortComplex_shortExact K L m).exact
    (retraction (homologyKunneth K L (m + 1))) (IsSplitMono.id _)
    (homologyKunnethShortComplex_shortExact K L m).epi_g

/-- The retraction of the Künneth splitting is the chosen retraction of the Künneth map. -/
@[simp] lemma homologyKunnethShortComplexSplitting_r (m : ℕ) :
    (homologyKunnethShortComplexSplitting K L m).r =
      retraction (homologyKunneth K L (m + 1)) (hf := isSplitMono_homologyKunneth K L (m + 1)) :=
  (rfl)

end Kunneth

end HomologicalComplex

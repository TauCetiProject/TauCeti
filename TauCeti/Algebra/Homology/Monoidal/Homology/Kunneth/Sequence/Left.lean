/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth.Sequence.Basic

/-!
# The Künneth short exact sequence with a projective first factor

Let `K` and `L` be chain complexes of modules over a commutative ring `R`, with differentials
`d : C_{p+1} ⟶ C_p` indexed by an additive cancellative commutative monoid `I` with a `1` which
carries tensor signs on `ComplexShape.down I`, and suppose that the cycles `Z_p(K)` and the
quotients `K_p / Z_p(K)` of the *first* factor are projective; no hypothesis is imposed on `L`.
Then the **Künneth sequence**

`0 ⟶ ⨁_{p + q = m + 1} Hₚ(K) ⊗ H_q(L) ⟶ Hₘ₊₁(K ⊗ L) ⟶ ⨁_{p + q = m} Tor₁(Hₚ(K), H_q(L)) ⟶ 0`

is exact (`HomologicalComplex.homologyKunnethShortComplexLeft_shortExact`). Here `K ⊗ L` carries
the differential `d (x ⊗ y) = d x ⊗ y + ε(p) x ⊗ d y` on `Kₚ ⊗ L_q`, with the sign `ε(p)` taken in
the degree of the projective factor, the first map is the Künneth map
`HomologicalComplex.homologyKunneth`, and `Tor₁` is Mathlib's `CategoryTheory.Tor'`, which derives
the tensor product in its first variable, that of the projective factor.

This is the counterpart of `HomologicalComplex.homologyKunnethShortComplex_shortExact`, which
assumes the projectivity of the second factor. The two are not interchangeable without a
comparison of the homology of `K ⊗ L` with that of `L ⊗ K` through the symmetry of the tensor
product of complexes, and of the two derived functors `Tor` and `Tor'`. Both hypotheses hold for
every complex of projective modules over a principal ideal domain, and are then found by instance
search (`HomologicalComplex.projective_cycles_of_hasProjectiveDimensionLE_one` and
`HomologicalComplex.projective_cokernel_iCycles_of_hasProjectiveDimensionLE_one`).

The index may be `ℕ`, or `ZMod n` for even `n` with the tensor signs
`ComplexShape.tensorSignsDownZMod`. In the latter case the sums run over all pairs in `ZMod n`
with the given sum; the sequence is not a consequence of the `ℕ`-indexed one, since the tensor
product of cyclically graded complexes is not the tensor product of their periodic unrollings.

The proof is Weibel's, applied to the cycle sequence `0 ⟶ Z(K) ⟶ K ⟶ K / Z(K) ⟶ 0` of the first
factor, tensored on the right with `L`. The sequence splits in each degree, so it stays exact.
Its outer terms have zero differentials and flat terms, so the Künneth maps of `Z(K) ⊗ L` and
`(K / Z(K)) ⊗ L` are isomorphisms (`HomologicalComplex.isIso_homologyKunneth_of_d_eq_zero_of_flat`).
Through them, the connecting morphisms of the long exact homology sequence become the sums over
`p + q = m` of the projective presentations

`0 ⟶ H_{p+1}(K / Z(K)) ⟶ Hₚ(Z(K)) ⟶ Hₚ(K) ⟶ 0`

(`HomologicalComplex.homologyPresentation`) tensored on the right with `H_q(L)`, without a sign
(`HomologicalComplex.homologyKunneth_comp_δ_right`). By right exactness the cokernel of such a map
is `Hₚ(K) ⊗ H_q(L)`, which makes the Künneth map a monomorphism
(`HomologicalComplex.mono_homologyKunneth_left`), and its kernel is `Tor'₁(Hₚ(K), H_q(L))`
(`CategoryTheory.ShortComplex.ShortExact.tor'OneIsoKernel`).

## Main definitions and results

* `HomologicalComplex.homologyTorLeft`: the module `⨁_{p + q = m} Tor'₁(Hₚ(K), H_q(L))`.
* `HomologicalComplex.homologyToTorLeft`: the map
  `Hₘ₊₁(K ⊗ L) ⟶ ⨁_{p + q = m} Tor'₁(Hₚ(K), H_q(L))`, induced by the projection of `K` onto
  `K / Z(K)`.
* `HomologicalComplex.homologyTorLeftToHomologyQuotient`: the inclusion
  `⨁_{p + q = m} Tor'₁(Hₚ(K), H_q(L)) ⟶ Hₘ₊₁((K / Z(K)) ⊗ L)` characterizing `homologyToTorLeft`
  (`HomologicalComplex.homologyToTorLeft_comp_homologyTorLeftToHomologyQuotient` and
  `HomologicalComplex.homologyToTorLeft_unique`).
* `HomologicalComplex.mono_homologyKunneth_left`: the Künneth map is a monomorphism.
* `HomologicalComplex.homologyKunnethShortComplexLeft` and
  `HomologicalComplex.homologyKunnethShortComplexLeft_shortExact`: **the Künneth short exact
  sequence** with a projective first factor.
* `HomologicalComplex.homologyKunnethShortComplexLeftSplitting`: its splitting when the cycles of
  `L` split off as well.

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

variable {R : Type u} [CommRing R] {I : Type*} [AddCancelCommMonoid I] [One I] [Small.{u} I]
  [(ComplexShape.down I).TensorSigns] [DecidableEq I] (K L : ChainComplex (ModuleCat.{u} R) I)

/-- The module `⨁_{p + q = m} Tor'₁(Hₚ(K), H_q(L))`, the third term of the Künneth short exact
sequence with a projective first factor
(`HomologicalComplex.homologyKunnethShortComplexLeft_shortExact`). Mathlib's `CategoryTheory.Tor'`
derives the tensor product in its first variable. -/
abbrev homologyTorLeft (m : I) : ModuleCat.{u} R :=
  GradedObject.mapBifunctorMapObj (Tor' (ModuleCat.{u} R) 1) (fun x ↦ x.1 + x.2)
    (fun p ↦ K.homology p) (fun q ↦ L.homology q) m

/-- The map `⨁ H_{p+1}(K / Z(K)) ⊗ H_q(L) ⟶ ⨁ Hₚ(Z(K)) ⊗ H_q(L)` of degree `m` induced by the
connecting morphisms of `0 ⟶ Z(K) ⟶ K ⟶ K / Z(K) ⟶ 0`. -/
private abbrev tensorδLeft (m : I) :=
  GradedObject.Monoidal.tensorHom (fun p ↦ (K.homologyPresentation p).f)
    (𝟙 (fun q ↦ L.homology q)) m

/-- The map `⨁ Hₚ(Z(K)) ⊗ H_q(L) ⟶ ⨁ Hₚ(K) ⊗ H_q(L)` of degree `m` induced by the inclusion of
the cycles. -/
private abbrev tensorπLeft (m : I) :=
  GradedObject.Monoidal.tensorHom (fun p ↦ (K.homologyPresentation p).g)
    (𝟙 (fun q ↦ L.homology q)) m

/-- The graded short complex `H_{p+1}(K / Z(K)) ⊗ H_q(L) ⟶ Hₚ(Z(K)) ⊗ H_q(L) ⟶ Hₚ(K) ⊗ H_q(L)`
indexed by `(p, q)`. -/
private def tensorShortComplexLeft : ShortComplex (GradedObject (I × I) (ModuleCat.{u} R)) :=
  ShortComplex.mk
    (((GradedObject.mapBifunctor (curriedTensor _) I I).map
      (fun p ↦ (K.homologyPresentation p).f)).app (fun q ↦ L.homology q))
    (((GradedObject.mapBifunctor (curriedTensor _) I I).map
      (fun p ↦ (K.homologyPresentation p).g)).app (fun q ↦ L.homology q))
    (funext fun x ↦ by
      dsimp
      rw [← comp_whiskerRight, (K.homologyPresentation x.1).zero,
        MonoidalPreadditive.zero_whiskerRight])

omit [Small.{u} I] [(ComplexShape.down I).TensorSigns] [DecidableEq I] in
private lemma tensorShortComplexLeft_exact (x : I × I) :
    (ShortComplex.mk ((tensorShortComplexLeft K L).f x) ((tensorShortComplexLeft K L).g x)
      (congr_fun (tensorShortComplexLeft K L).zero x)).Exact :=
  have := CategoryWithHomology.hasHomology
    ((K.homologyPresentation x.1).map (tensorRight (L.homology x.2)))
  (K.homologyPresentation_shortExact x.1).exact.map_of_epi_of_preservesCokernel
    (tensorRight (L.homology x.2)) (K.homologyPresentation_shortExact x.1).epi_g inferInstance

omit [(ComplexShape.down I).TensorSigns] [DecidableEq I] in
private lemma tensorδLeft_comp_tensorπLeft (m : I) :
    tensorδLeft K L m ≫ tensorπLeft K L m = 0 := by
  refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ?_
  simp [← comp_whiskerRight_assoc]

omit [DecidableEq I] [(ComplexShape.down I).TensorSigns] in
/-- Right exactness of the tensor product: `⨁ Hₚ(K) ⊗ H_q(L)` is the cokernel of `tensorδLeft`. -/
private lemma tensorπLeft_exact (m : I) :
    (ShortComplex.mk _ _ (tensorδLeft_comp_tensorπLeft K L m)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (GradedObject.exact_mapMap (tensorShortComplexLeft K L) (fun x ↦ x.1 + x.2) m
      (tensorShortComplexLeft_exact K L))
  -- the coproducts over the fibre of `m` are the terms of the tensor products of degree `m`
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans ((GradedObject.Monoidal.tensorHom_id_eq_mapMap _ _ m).trans
      (Category.comp_id _).symm))
    ((Category.id_comp _).trans ((GradedObject.Monoidal.tensorHom_id_eq_mapMap _ _ m).trans
      (Category.comp_id _).symm))

private instance (m : I) : Epi (tensorπLeft K L m) := by
  rw [tensorπLeft, GradedObject.Monoidal.tensorHom_id_eq_mapMap]
  have (x : I × I) : Epi ((((GradedObject.mapBifunctor (curriedTensor _) I I).map
      (fun p ↦ (K.homologyPresentation p).g)).app (fun q ↦ L.homology q)) x) := by
    have : (tensorRight (L.homology x.2)).PreservesEpimorphisms :=
      Functor.preservesEpimorphisms_of_isLeftAdjoint _
    have := (K.homologyPresentation_shortExact x.1).epi_g
    exact (tensorRight (L.homology x.2)).map_epi (K.homologyPresentation x.1).g
  exact GradedObject.epi_mapMap _ _ m

/-- The reindexing `⨁ H_{p+1}(K / Z(K)) ⊗ H_q(L) ≅ ⨁ Hₚ(K / Z(K)) ⊗ H_q(L)` from degree `m` to
degree `m + 1`, which holds since `Hₚ(K / Z(K)) = 0` when `p` is not of the form `p' + 1`. -/
private abbrev succIsoLeft (m : I) :=
  GradedObject.Monoidal.succTensorObjIso
    (fun p ↦ K.cyclesComplexShortComplex.X₃.homology p) (fun q ↦ L.homology q)
    (fun _ ↦ K.isZero_homology_cyclesComplexShortComplex_X₃_of_forall_add_one_ne) m

/-- The identification of the middle term `K ⊗ L` of `Z(K) ⊗ L ⟶ K ⊗ L ⟶ (K / Z(K)) ⊗ L`. -/
private abbrev middleIsoLeft (n : I) :
    (tensorObj K.cyclesComplexShortComplex.X₂ L).homology n ≅ (tensorObj K L).homology n :=
  eqToIso (congrArg (fun M ↦ (tensorObj M L).homology n) K.cyclesComplexShortComplex_X₂)

/-- The inclusion of the cycles of `K`, read through the Künneth maps. -/
private lemma tensorπLeft_comp_homologyKunneth (n : I) :
    tensorπLeft K L n ≫ homologyKunneth K L n =
      homologyKunneth K.cyclesComplexShortComplex.X₁ L n ≫
        homologyMap (tensorRightShortComplex L K.cyclesComplexShortComplex).f n ≫
          (middleIsoLeft K L n).hom := by
  have h₁ : GradedObject.Monoidal.tensorHom
      (fun p ↦ homologyMap K.cyclesComplexShortComplex.f p) (𝟙 (fun q ↦ L.homology q)) n ≫
        homologyKunneth K.cyclesComplexShortComplex.X₂ L n =
      homologyKunneth K.cyclesComplexShortComplex.X₁ L n ≫
        homologyMap (tensorHom K.cyclesComplexShortComplex.f (𝟙 L)) n := by
    have := homologyKunneth_naturality K.cyclesComplexShortComplex.f (𝟙 L) n
    simp only [homologyMap_id] at this
    exact this
  have h₂ : tensorπLeft K L n = GradedObject.Monoidal.tensorHom
      (fun p ↦ homologyMap K.cyclesComplexShortComplex.f p) (𝟙 (fun q ↦ L.homology q)) n ≫
        GradedObject.Monoidal.tensorHom
          (fun p ↦ eqToHom (congrArg (fun M ↦ M.homology p) K.cyclesComplexShortComplex_X₂))
          (𝟙 (fun q ↦ L.homology q)) n := by
    refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ?_
    simp
  rw [h₂, Category.assoc,
    ← homologyKunneth_comp_eqToHom_left L K.cyclesComplexShortComplex_X₂, reassoc_of% h₁,
    eqToIso.hom]

variable [∀ p, Projective (cokernel (K.iCycles p))]

/-- `Z(K) ⊗ L ⟶ K ⊗ L ⟶ (K / Z(K)) ⊗ L` is short exact: since `K / Z(K)` has projective terms,
the cycles split off `K`. -/
private lemma shortExact_tensorRight_cycles :
    (tensorRightShortComplex L K.cyclesComplexShortComplex).ShortExact :=
  shortExact_tensorRightShortComplex L _ K.cyclesComplexShortComplex_shortExact

/-- The connecting morphism of `Z(K) ⊗ L ⟶ K ⊗ L ⟶ (K / Z(K)) ⊗ L`, read through the Künneth
maps. -/
private lemma homologyKunneth_comp_δ_cycles_left (m : I) :
    homologyKunneth K.cyclesComplexShortComplex.X₃ L (m + 1) ≫
        (shortExact_tensorRight_cycles K L).δ (m + 1) m (by simp) =
      (succIsoLeft K L m).inv ≫ tensorδLeft K L m ≫
        homologyKunneth K.cyclesComplexShortComplex.X₁ L m :=
  homologyKunneth_comp_δ_right (shortExact_tensorRight_cycles K L) m

private instance (n : I) : IsIso (homologyKunneth K.cyclesComplexShortComplex.X₃ L n) :=
  have (p : I) : Module.Flat R (K.cyclesComplexShortComplex.X₃.X p) := by
    rw [cyclesComplexShortComplex_X₃]
    exact inferInstanceAs (Module.Flat R (cokernel (K.iCycles p) : ModuleCat.{u} R))
  isIso_homologyKunneth_of_d_eq_zero_of_flat _ _ (by simp) n

/-- The identification `Hₙ₊₁((K / Z(K)) ⊗ L) ≅ ⨁ H_{p+1}(K / Z(K)) ⊗ H_q(L)` of degree `n`: the
inverse Künneth isomorphism and the reindexing `succIsoLeft`. -/
private def quotientIsoLeft (n : I) :
    (tensorObj K.cyclesComplexShortComplex.X₃ L).homology (n + 1) ≅
      GradedObject.Monoidal.tensorObj
        (fun p ↦ K.cyclesComplexShortComplex.X₃.homology (p + 1)) (fun q ↦ L.homology q) n :=
  (asIso (homologyKunneth K.cyclesComplexShortComplex.X₃ L (n + 1))).symm ≪≫
    (succIsoLeft K L n).symm

variable [∀ p, Projective (K.cycles p)]

private instance (n : I) : IsIso (homologyKunneth K.cyclesComplexShortComplex.X₁ L n) :=
  have (p : I) : Module.Flat R (K.cyclesComplexShortComplex.X₁.X p) := by
    rw [cyclesComplexShortComplex_X₁]
    exact inferInstanceAs (Module.Flat R (K.cycles p))
  isIso_homologyKunneth_of_d_eq_zero_of_flat _ _ (by simp) n

private instance (p : I) : Projective (K.homologyPresentation p).X₁ :=
  Projective.of_iso
    (K.cyclesComplexShortComplex.X₃.XIsoHomologyOfDEqZero (p + 1) (by simp) (by simp))
    (by simpa using (inferInstance : Projective (cokernel (K.iCycles (p + 1)))))

private instance (p : I) : Projective (K.homologyPresentation p).X₂ :=
  Projective.of_iso (K.cyclesComplexShortComplex.X₁.XIsoHomologyOfDEqZero p (by simp) (by simp))
    (by simpa using (inferInstance : Projective (K.cycles p)))

/-- The connecting morphism of `Z(K) ⊗ L ⟶ K ⊗ L ⟶ (K / Z(K)) ⊗ L` is `tensorδLeft`, read through
`quotientIsoLeft` and the Künneth isomorphism for `Z(K)`. -/
private lemma quotientIsoLeft_hom_comp_tensorδLeft (n : I) :
    (quotientIsoLeft K L n).hom ≫ tensorδLeft K L n =
      (shortExact_tensorRight_cycles K L).δ (n + 1) n (by simp) ≫
        inv (homologyKunneth K.cyclesComplexShortComplex.X₁ L n) := by
  rw [← cancel_mono (homologyKunneth K.cyclesComplexShortComplex.X₁ L n)]
  simp only [quotientIsoLeft, Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc,
    IsIso.inv_hom_id, Category.comp_id, ← homologyKunneth_comp_δ_cycles_left,
    IsIso.inv_hom_id_assoc]

omit [∀ p, Projective (cokernel (K.iCycles p))] in
/-- The inclusion of the cycles, read through the Künneth isomorphism for `Z(K)`. -/
@[reassoc]
private lemma inv_homologyKunneth_comp_tensorπLeft (n : I) :
    inv (homologyKunneth K.cyclesComplexShortComplex.X₁ L n) ≫
      tensorπLeft K L n ≫ homologyKunneth K L n =
        homologyMap (tensorRightShortComplex L K.cyclesComplexShortComplex).f n ≫
          (middleIsoLeft K L n).hom := by
  rw [tensorπLeft_comp_homologyKunneth, IsIso.inv_hom_id_assoc]

/-- In the long exact homology sequence of `Z(K) ⊗ L ⟶ K ⊗ L ⟶ (K / Z(K)) ⊗ L`, the piece
`Hₙ₊₁((K / Z(K)) ⊗ L) ⟶ Hₙ(Z(K) ⊗ L) ⟶ Hₙ(K ⊗ L)`, read through the Künneth isomorphisms. -/
private lemma tensorδLeft_exact_homologyKunneth (n : I) :
    (ShortComplex.mk (tensorδLeft K L n) (tensorπLeft K L n ≫ homologyKunneth K L n)
      (by rw [← Category.assoc, tensorδLeft_comp_tensorπLeft, zero_comp])).Exact :=
  (ShortComplex.exact_iff_of_epi_of_isIso_of_mono (ShortComplex.Hom.mk
    (S₁ := ShortComplex.mk _ _ ((shortExact_tensorRight_cycles K L).δ_comp (n + 1) n (by simp)))
    (S₂ := ShortComplex.mk (tensorδLeft K L n) (tensorπLeft K L n ≫ homologyKunneth K L n)
      (by rw [← Category.assoc, tensorδLeft_comp_tensorπLeft, zero_comp]))
    (quotientIsoLeft K L n).hom (asIso (homologyKunneth K.cyclesComplexShortComplex.X₁ L n)).inv
    (middleIsoLeft K L n).hom (quotientIsoLeft_hom_comp_tensorδLeft K L n)
    (inv_homologyKunneth_comp_tensorπLeft K L n))).1
    ((shortExact_tensorRight_cycles K L).homology_exact₁ (n + 1) n (by simp))

/-- **The Künneth map is a monomorphism** when the cycles and the quotients `Kₚ / Zₚ(K)` of the
first factor `K` are projective, for instance for a complex `K` of projective modules over a
principal ideal domain. No hypothesis is imposed on `L`; compare
`HomologicalComplex.mono_homologyKunneth`, which assumes this of the second factor. -/
theorem mono_homologyKunneth_left (n : I) : Mono (homologyKunneth K L n) := by
  have hc := (tensorπLeft_exact K L n).gIsCokernel
  have hm := (tensorδLeft_exact_homologyKunneth K L n).mono_cokernelDesc
  -- the cokernel of `tensorδLeft` is `⨁ Hₚ(K) ⊗ H_q(L)`, and the induced map is the Künneth map
  have : cokernel.desc (tensorδLeft K L n) (tensorπLeft K L n ≫ homologyKunneth K L n)
      (by rw [← Category.assoc, tensorδLeft_comp_tensorπLeft, zero_comp]) =
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _) hc).hom ≫
        homologyKunneth K L n :=
    (IsColimit.coconePointUniqueUpToIso_hom_desc _ hc).symm.trans
      (_ ≫= Cofork.IsColimit.hom_ext hc ((Cofork.IsColimit.π_desc hc).trans (by simp)))
  simpa only [this, mono_comp_iff_of_isIso] using hm

/-- The summand inclusion `Tor'₁(Hₚ(K), H_q(L)) ⟶ H_{p+1}(K / Z(K)) ⊗ H_q(L)`, identifying `Tor'₁`
with the kernel of `H_{p+1}(K / Z(K)) ⊗ H_q(L) ⟶ Hₚ(Z(K)) ⊗ H_q(L)` through the projective
presentation `HomologicalComplex.homologyPresentation`. -/
private def torιLeft (x : I × I) :
    ((Tor' (ModuleCat.{u} R) 1).obj (K.homology x.1)).obj (L.homology x.2) ⟶
      (K.homologyPresentation x.1).X₁ ⊗ L.homology x.2 :=
  ((K.homologyPresentation_shortExact x.1).tor'OneIsoKernel (L.homology x.2)).hom ≫ kernel.ι _

omit [Small.{u} I] [(ComplexShape.down I).TensorSigns] [DecidableEq I] in
private lemma torιLeft_comp (x : I × I) :
    torιLeft K L x ≫ ((K.homologyPresentation x.1).f ▷ L.homology x.2) = 0 := by
  simp [torιLeft]

/-- The inclusions `torιLeft`, as a morphism of graded objects indexed by `(p, q)`. -/
private def torGradedιLeft : ((GradedObject.mapBifunctor (Tor' (ModuleCat.{u} R) 1) I I).obj
      (fun p ↦ K.homology p)).obj (fun q ↦ L.homology q) ⟶
    ((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} R)) I I).obj
      (fun p ↦ (K.homologyPresentation p).X₁)).obj (fun q ↦ L.homology q) :=
  fun x ↦ torιLeft K L x

/-- The graded short complex
`Tor'₁(Hₚ(K), H_q(L)) ⟶ H_{p+1}(K / Z(K)) ⊗ H_q(L) ⟶ Hₚ(Z(K)) ⊗ H_q(L)` indexed by `(p, q)`. -/
private def torShortComplexLeft : ShortComplex (GradedObject (I × I) (ModuleCat.{u} R)) :=
  ShortComplex.mk (torGradedιLeft K L) (tensorShortComplexLeft K L).f
    (funext (torιLeft_comp K L))

omit [Small.{u} I] [(ComplexShape.down I).TensorSigns] [DecidableEq I] in
private lemma torShortComplexLeft_exact (x : I × I) :
    (ShortComplex.mk ((torShortComplexLeft K L).f x) ((torShortComplexLeft K L).g x)
      (congr_fun (torShortComplexLeft K L).zero x)).Exact := by
  refine (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
    (S₁ := ShortComplex.mk _ _ (kernel.condition ((K.homologyPresentation x.1).f ▷ L.homology x.2)))
    (S₂ := ShortComplex.mk ((torShortComplexLeft K L).f x) ((torShortComplexLeft K L).g x)
      (congr_fun (torShortComplexLeft K L).zero x))
    ((K.homologyPresentation_shortExact x.1).tor'OneIsoKernel (L.homology x.2)).symm (Iso.refl _)
    (Iso.refl _) ?_ ?_)).1 (ShortComplex.exact_kernel _)
  · exact (Iso.inv_hom_id_assoc _ _).trans (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The inclusion `⨁ Tor'₁(Hₚ(K), H_q(L)) ⟶ ⨁ H_{p+1}(K / Z(K)) ⊗ H_q(L)` of degree `m`. -/
private def torToTensorLeft (m : I) :
    homologyTorLeft K L m ⟶ GradedObject.Monoidal.tensorObj
      (fun p ↦ K.cyclesComplexShortComplex.X₃.homology (p + 1)) (fun q ↦ L.homology q) m :=
  GradedObject.mapMap (torGradedιLeft K L) (fun x ↦ x.1 + x.2) m

omit [DecidableEq I] [(ComplexShape.down I).TensorSigns] in
private lemma torToTensorLeft_comp_tensorδLeft (m : I) :
    torToTensorLeft K L m ≫ tensorδLeft K L m = 0 := by
  rw [tensorδLeft, GradedObject.Monoidal.tensorHom_id_eq_mapMap, torToTensorLeft]
  refine GradedObject.mapObj_ext _ _ _ _ fun x _ ↦ ?_
  -- `erw`: the components of `mapMap` are morphisms of the graded category, whose hom types are
  -- those of `ModuleCat R` only up to unfolding
  erw [GradedObject.ι_mapMap_assoc, GradedObject.ι_mapMap, ← Category.assoc, ← Pi.comp_apply,
    (torShortComplexLeft K L).zero]
  exact zero_comp.trans comp_zero.symm

omit [DecidableEq I] [(ComplexShape.down I).TensorSigns] in
/-- `⨁ Tor'₁(Hₚ(K), H_q(L))` is the kernel of `tensorδLeft`. -/
private lemma torToTensorLeft_exact (m : I) :
    (ShortComplex.mk _ _ (torToTensorLeft_comp_tensorδLeft K L m)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (GradedObject.exact_mapMap (torShortComplexLeft K L) (fun x ↦ x.1 + x.2) m
      (torShortComplexLeft_exact K L))
  -- the coproducts over the fibre of `m` are the terms of the tensor products of degree `m`
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans ((GradedObject.Monoidal.tensorHom_id_eq_mapMap _ _ m).trans
      (Category.comp_id _).symm))

private instance (m : I) : Mono (torToTensorLeft K L m) := by
  have (x : I × I) : Mono (torGradedιLeft K L x) := mono_comp
    ((K.homologyPresentation_shortExact x.1).tor'OneIsoKernel (L.homology x.2)).hom (kernel.ι _)
  exact GradedObject.mono_mapMap _ _ m

/-- The inclusion `⨁_{p + q = m} Tor'₁(Hₚ(K), H_q(L)) ⟶ Hₘ₊₁((K / Z(K)) ⊗ L)` which characterizes
`HomologicalComplex.homologyToTorLeft`
(`HomologicalComplex.homologyToTorLeft_comp_homologyTorLeftToHomologyQuotient`): the inclusion of
`Tor'₁(Hₚ(K), H_q(L))` into `H_{p+1}(K / Z(K)) ⊗ H_q(L)` given by the projective presentation
`HomologicalComplex.homologyPresentation`, followed by the Künneth isomorphism of `K / Z(K)`
and `L`. -/
def homologyTorLeftToHomologyQuotient (m : I) :
    homologyTorLeft K L m ⟶ (tensorObj K.cyclesComplexShortComplex.X₃ L).homology (m + 1) :=
  torToTensorLeft K L m ≫ (quotientIsoLeft K L m).inv

instance (m : I) : Mono (homologyTorLeftToHomologyQuotient K L m) := by
  rw [homologyTorLeftToHomologyQuotient]
  infer_instance

/-- `⨁ Tor'₁(Hₚ(K), H_q(L))` is the kernel of `tensorδLeft`, as a limit. -/
private def torIsKernelLeft (m : I) :
    IsLimit (KernelFork.ofι (torToTensorLeft K L m) (torToTensorLeft_comp_tensorδLeft K L m)) :=
  (torToTensorLeft_exact K L m).fIsKernel

/-- The map `Hₘ₊₁(K ⊗ L) ⟶ ⨁ H_{p+1}(K / Z(K)) ⊗ H_q(L)` induced by the projection of `K` onto
`K / Z(K)`, read through `quotientIsoLeft`. -/
private def toTensorQuotientLeft (m : I) :
    (tensorObj K L).homology (m + 1) ⟶ GradedObject.Monoidal.tensorObj
      (fun p ↦ K.cyclesComplexShortComplex.X₃.homology (p + 1)) (fun q ↦ L.homology q) m :=
  (middleIsoLeft K L (m + 1)).inv ≫
    homologyMap (tensorRightShortComplex L K.cyclesComplexShortComplex).g (m + 1) ≫
      (quotientIsoLeft K L m).hom

private lemma toTensorQuotientLeft_comp_tensorδLeft (m : I) :
    toTensorQuotientLeft K L m ≫ tensorδLeft K L m = 0 := by
  rw [toTensorQuotientLeft, Category.assoc, Category.assoc, quotientIsoLeft_hom_comp_tensorδLeft,
    (shortExact_tensorRight_cycles K L).comp_δ_assoc, zero_comp, comp_zero]

private lemma homologyKunneth_comp_toTensorQuotientLeft (m : I) :
    homologyKunneth K L (m + 1) ≫ toTensorQuotientLeft K L m = 0 := by
  rw [← cancel_epi (inv (homologyKunneth K.cyclesComplexShortComplex.X₁ L (m + 1)) ≫
    tensorπLeft K L (m + 1)), comp_zero, Category.assoc, inv_homologyKunneth_comp_tensorπLeft_assoc,
    toTensorQuotientLeft, Iso.hom_inv_id_assoc, ← homologyMap_comp_assoc,
    (tensorRightShortComplex L K.cyclesComplexShortComplex).zero, homologyMap_zero, zero_comp]

/-- The second map `Hₘ₊₁(K ⊗ L) ⟶ ⨁_{p + q = m} Tor'₁(Hₚ(K), H_q(L))` of the Künneth short exact
sequence with a projective first factor
(`HomologicalComplex.homologyKunnethShortComplexLeft_shortExact`). It is induced by the projection
of `K` onto `K / Z(K)`: its image lies in the kernel of the map
`⨁ H_{p+1}(K / Z(K)) ⊗ H_q(L) ⟶ ⨁ Hₚ(Z(K)) ⊗ H_q(L)` given by the connecting morphisms, and this
kernel is `⨁ Tor'₁(Hₚ(K), H_q(L))` through the projective presentations
`HomologicalComplex.homologyPresentation`. -/
def homologyToTorLeft (m : I) : (tensorObj K L).homology (m + 1) ⟶ homologyTorLeft K L m :=
  (torIsKernelLeft K L m).lift (KernelFork.ofι _ (toTensorQuotientLeft_comp_tensorδLeft K L m))

@[reassoc]
private lemma homologyToTorLeft_comp_torToTensorLeft (m : I) :
    homologyToTorLeft K L m ≫ torToTensorLeft K L m = toTensorQuotientLeft K L m :=
  Fork.IsLimit.lift_ι (torIsKernelLeft K L m)

/-- `HomologicalComplex.homologyToTorLeft` followed by the inclusion
`HomologicalComplex.homologyTorLeftToHomologyQuotient` is the map
`Hₘ₊₁(K ⊗ L) ⟶ Hₘ₊₁((K / Z(K)) ⊗ L)` induced by the projection of `K` onto `K / Z(K)`. -/
@[reassoc (attr := simp)]
lemma homologyToTorLeft_comp_homologyTorLeftToHomologyQuotient (m : I) :
    homologyToTorLeft K L m ≫ homologyTorLeftToHomologyQuotient K L m =
      eqToHom (congrArg (fun M ↦ (tensorObj M L).homology (m + 1))
          K.cyclesComplexShortComplex_X₂.symm) ≫
        homologyMap (tensorRightShortComplex L K.cyclesComplexShortComplex).g (m + 1) := by
  simp [homologyTorLeftToHomologyQuotient, homologyToTorLeft_comp_torToTensorLeft_assoc,
    toTensorQuotientLeft]

/-- `HomologicalComplex.homologyToTorLeft` is the unique morphism whose composite with
`HomologicalComplex.homologyTorLeftToHomologyQuotient` is the map induced by the projection of `K`
onto `K / Z(K)`. -/
lemma homologyToTorLeft_unique {m : I}
    (f : (tensorObj K L).homology (m + 1) ⟶ homologyTorLeft K L m)
    (hf : f ≫ homologyTorLeftToHomologyQuotient K L m =
      eqToHom (congrArg (fun M ↦ (tensorObj M L).homology (m + 1))
          K.cyclesComplexShortComplex_X₂.symm) ≫
        homologyMap (tensorRightShortComplex L K.cyclesComplexShortComplex).g (m + 1)) :
    f = homologyToTorLeft K L m := by
  rw [← cancel_mono (homologyTorLeftToHomologyQuotient K L m), hf,
    homologyToTorLeft_comp_homologyTorLeftToHomologyQuotient]

/-- The Künneth map followed by the map to `⨁ Tor'₁(Hₚ(K), H_q(L))` vanishes. -/
@[reassoc (attr := simp)]
lemma homologyKunneth_comp_homologyToTorLeft (m : I) :
    homologyKunneth K L (m + 1) ≫ homologyToTorLeft K L m = 0 := by
  rw [← cancel_mono (torToTensorLeft K L m), Category.assoc,
    homologyToTorLeft_comp_torToTensorLeft, homologyKunneth_comp_toTensorQuotientLeft, zero_comp]

/-- In the long exact homology sequence of `Z(K) ⊗ L ⟶ K ⊗ L ⟶ (K / Z(K)) ⊗ L`, the piece
`Hₘ₊₁(K ⊗ L) ⟶ Hₘ₊₁((K / Z(K)) ⊗ L) ⟶ Hₘ(Z(K) ⊗ L)`, read through the Künneth isomorphisms. -/
private lemma toTensorQuotientLeft_exact (m : I) :
    (ShortComplex.mk _ _ (toTensorQuotientLeft_comp_tensorδLeft K L m)).Exact :=
  (ShortComplex.exact_iff_of_epi_of_isIso_of_mono (ShortComplex.Hom.mk
    (S₁ := ShortComplex.mk _ _ ((shortExact_tensorRight_cycles K L).comp_δ (m + 1) m (by simp)))
    (S₂ := ShortComplex.mk _ _ (toTensorQuotientLeft_comp_tensorδLeft K L m))
    (middleIsoLeft K L (m + 1)).hom (quotientIsoLeft K L m).hom
    (asIso (homologyKunneth K.cyclesComplexShortComplex.X₁ L m)).inv
    (by simp [toTensorQuotientLeft]) (quotientIsoLeft_hom_comp_tensorδLeft K L m))).1
    ((shortExact_tensorRight_cycles K L).homology_exact₃ (m + 1) m (by simp))

/-- In the long exact homology sequence of `Z(K) ⊗ L ⟶ K ⊗ L ⟶ (K / Z(K)) ⊗ L`, the piece
`Hₘ₊₁(Z(K) ⊗ L) ⟶ Hₘ₊₁(K ⊗ L) ⟶ Hₘ₊₁((K / Z(K)) ⊗ L)`, read through the Künneth maps: its first
term becomes its quotient `⨁_{p + q = m + 1} Hₚ(K) ⊗ H_q(L)` and its first map the Künneth map. -/
private lemma homologyKunneth_exact_toTensorQuotientLeft (m : I) :
    (ShortComplex.mk _ _ (homologyKunneth_comp_toTensorQuotientLeft K L m)).Exact :=
  -- the comparison maps from the long exact sequence are an epimorphism and two isomorphisms;
  -- these instances are supplied explicitly because synthesizing them is slow
  (@ShortComplex.exact_iff_of_epi_of_isIso_of_mono _ _ _ _ _ (ShortComplex.Hom.mk
    (S₂ := ShortComplex.mk _ _ (homologyKunneth_comp_toTensorQuotientLeft K L m))
    (inv (homologyKunneth K.cyclesComplexShortComplex.X₁ L (m + 1)) ≫ tensorπLeft K L (m + 1))
    (middleIsoLeft K L (m + 1)).hom (quotientIsoLeft K L m).hom
    ((Category.assoc _ _ _).trans (inv_homologyKunneth_comp_tensorπLeft K L (m + 1)))
    (by simp [toTensorQuotientLeft])) (epi_comp _ _) (Iso.isIso_hom _) (IsIso.mono_of_iso _)).1
    ((shortExact_tensorRight_cycles K L).homology_exact₂ (m + 1))

/-- The Künneth short complex with a projective first factor
`⨁_{p + q = m + 1} Hₚ(K) ⊗ H_q(L) ⟶ Hₘ₊₁(K ⊗ L) ⟶ ⨁_{p + q = m} Tor'₁(Hₚ(K), H_q(L))`, formed by
the Künneth map and `HomologicalComplex.homologyToTorLeft`. -/
abbrev homologyKunnethShortComplexLeft (m : I) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk _ _ (homologyKunneth_comp_homologyToTorLeft K L m)

/-- The second map `HomologicalComplex.homologyToTorLeft` of the Künneth short complex is an
epimorphism. -/
private lemma epi_homologyToTorLeft (m : I) : Epi (homologyToTorLeft K L m) := by
  -- `homologyToTorLeft` is the lift of `toTensorQuotientLeft` to the kernel `torToTensorLeft` of
  -- `tensorδLeft`, an epimorphism since `toTensorQuotientLeft` and `tensorδLeft` are exact
  have := (toTensorQuotientLeft_exact K L m).epi_kernelLift
  rw [homologyToTorLeft, ← IsLimit.lift_comp_conePointUniqueUpToIso_hom (kernelIsKernel _)]
  -- `kernel.lift` abbreviates this `(kernelIsKernel _).lift` of a `KernelFork`, so the
  -- epimorphism instance from `epi_kernelLift` applies by definitional equality.
  infer_instance

/-- **The Künneth short exact sequence with a projective first factor.** Let `K` and `L` be chain
complexes of modules over a commutative ring, indexed by `ℕ`, by `ZMod n` for even `n`, or by any
additive cancellative commutative monoid with a `1` carrying tensor signs, such that the cycles
`Zₚ(K)` and the quotients `Kₚ / Zₚ(K)` are projective, for instance a complex `K` of projective
modules over a principal ideal domain. Then

`0 ⟶ ⨁_{p + q = m + 1} Hₚ(K) ⊗ H_q(L) ⟶ Hₘ₊₁(K ⊗ L) ⟶ ⨁_{p + q = m} Tor'₁(Hₚ(K), H_q(L)) ⟶ 0`

is exact, the first map being the Künneth map and the second
`HomologicalComplex.homologyToTorLeft`. -/
theorem homologyKunnethShortComplexLeft_shortExact (m : I) :
    (homologyKunnethShortComplexLeft K L m).ShortExact where
  -- the sequence with `⨁ Tor'₁(Hₚ(K), H_q(L))` replaced by `⨁ H_{p+1}(K / Z(K)) ⊗ H_q(L)` is
  -- exact by the long exact homology sequence of `Z(K) ⊗ L ⟶ K ⊗ L ⟶ (K / Z(K)) ⊗ L`
  exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono (ShortComplex.Hom.mk
    (S₁ := homologyKunnethShortComplexLeft K L m)
    (S₂ := ShortComplex.mk _ _ (homologyKunneth_comp_toTensorQuotientLeft K L m))
    (𝟙 _) (𝟙 _) (torToTensorLeft K L m) (by simp)
    (by simp [homologyToTorLeft_comp_torToTensorLeft]))).2
    (homologyKunneth_exact_toTensorQuotientLeft K L m)
  mono_f := mono_homologyKunneth_left K L (m + 1)
  epi_g := epi_homologyToTorLeft K L m

variable [∀ q, IsSplitMono (L.iCycles q)]

/-- **The Künneth short exact sequence with a projective first factor splits** when, in addition,
the cycles of `L` split off its terms; for instance for complexes `K` and `L` of projective modules
over a principal ideal domain. The splitting comes from a retraction of the Künneth map
(`HomologicalComplex.isSplitMono_homologyKunneth`) built from chosen splittings of the cycles, so
it need not be natural in `K` and `L`. -/
def homologyKunnethShortComplexLeftSplitting (m : I) :
    (homologyKunnethShortComplexLeft K L m).Splitting :=
  have := isSplitMono_homologyKunneth K L (m + 1)
  .ofExactOfRetraction _ (homologyKunnethShortComplexLeft_shortExact K L m).exact
    (retraction (homologyKunneth K L (m + 1))) (IsSplitMono.id _)
    (homologyKunnethShortComplexLeft_shortExact K L m).epi_g

/-- The retraction of the Künneth splitting is the chosen retraction of the Künneth map. -/
@[simp] lemma homologyKunnethShortComplexLeftSplitting_r (m : I) :
    (homologyKunnethShortComplexLeftSplitting K L m).r =
      retraction (homologyKunneth K L (m + 1)) (hf := isSplitMono_homologyKunneth K L (m + 1)) :=
  (rfl)

end HomologicalComplex

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.DrinfeldBasis.Locus
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.ExactOrder.Subgroup
public import TauCeti.AlgebraicGeometry.FullSetOfSections.Curve
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Rank

/-!
# Full sets of sections and divisor sums on an elliptic curve

Let `E` be an elliptic curve over a scheme `S`. Specializing Theorem 1.8.3 of Katz and Mazur from
smooth curves (`TauCeti.AlgebraicGeometry.isFullSetOfSections_subschemeι_comp_iff`) to the smooth
separated curve `E ⟶ S` yields Katz–Mazur's comparison between full sets of sections of finite
locally free closed subschemes of `E` and sums of point divisors (Katz–Mazur, 1.10.1):

* For any finite family `x : A → E(S)` of `S`-points of `E`, the canonical lifts of the `x a` to
  the divisor `∑_{a ∈ A} [x a]` (`EllipticCurveGeom.pointsDivisor`) form a full set of sections
  (`EllipticCurveGeom.isFullSetOfSections_pointsDivisor`), and sections of any finite locally free
  closed subscheme `G ⊆ E` lifting `x` form a full set of sections of `G` over `S` if and only if
  `G` is the divisor `∑_{a ∈ A} [x a]`
  (`EllipticCurveGeom.isFullSetOfSections_iff_eq_pointsDivisor`,
  `EllipticCurveGeom.isFullSetOfSections_iff_ker_eq_pointsDivisor`).
* For a positive integer `N` and a homomorphism `φ : (ℤ/Nℤ)² →* E(S)`, each `φ a` factors uniquely
  through the `N`-torsion `E[N]` (`EllipticCurveGeom.torsionSection`). The homomorphism `φ` is a
  Drinfeld basis of `E[N]` (`EllipticCurveGeom.IsDrinfeldBasis`) if and only if the induced
  sections `torsionSection` form a full set of sections of `E[N]` over `S`
  (`EllipticCurveGeom.isDrinfeldBasis_iff_isFullSetOfSections`), and the Drinfeld-basis locus on
  `S` agrees scheme-theoretically with the full-set locus on `E[N]`
  (`EllipticCurveGeom.drinfeldBasisLocus_eq_fullSetLocus`, Katz–Mazur 1.10.13(1) and §3.1).
* For an `S`-point `P` of `E` and `N : ℕ`, the lifts of `P, 2P, …, NP` form a full set of sections
  of the divisor `[P] + [2P] + ⋯ + [NP]` (`EllipticCurveGeom.isFullSetOfSections_multiplesDivisor`),
  and sections of a finite locally free closed subscheme `G ⊆ E` lifting `P, 2P, …, NP` form a full
  set of sections of `G` if and only if `G` is `[P] + [2P] + ⋯ + [NP]`
  (`EllipticCurveGeom.isFullSetOfSections_iff_eq_multiplesDivisor`, Katz–Mazur 1.10.1
  and 1.10.5).

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.pointsDivisorSection`: the canonical sections of
  `∑_a [x a]` over `S` lifting a finite family `x : A → E(S)`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.torsionSection`: the sections of `E[N]` over `S`
  induced by a homomorphism `φ : (ℤ/Nℤ)² →* E(S)`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.multiplesDivisorSection`: the canonical sections of
  `[P] + [2P] + ⋯ + [NP]` over `S` lifting `P, 2P, …, NP`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isFullSetOfSections_pointsDivisor`: the canonical
  lifts of `x : A → E(S)` form a full set of sections of `∑_a [x a]`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isFullSetOfSections_iff_eq_pointsDivisor` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isFullSetOfSections_iff_ker_eq_pointsDivisor`:
  Katz–Mazur 1.10.1, equating full sets of sections of a finite locally free closed subscheme of
  `E` with its `pointsDivisor`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isDrinfeldBasis_iff_isFullSetOfSections`: `φ` is a
  Drinfeld basis of `E[N]` if and only if its induced sections form a full set of sections of
  `E[N]`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.drinfeldBasisLocus_eq_fullSetLocus`: the
  Drinfeld-basis locus equals the full-set locus on `E[N]`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isFullSetOfSections_multiplesDivisor` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isFullSetOfSections_iff_eq_multiplesDivisor`:
  full-set-of-sections characterization of `[P] + [2P] + ⋯ + [NP]`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, Theorem 1.8.3, §§1.10 (1.10.1, 1.10.5, 1.10.13) and §3.1.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj
open Scheme.IdealSheafData

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-! ### Divisors of finite families of points (Katz–Mazur 1.10.1) -/

section PointsDivisor

variable {A : Type*} [Fintype A]

/-- The canonical lift of each `S`-point `x a` in a finite family `x : A → E(S)` to a section of
the closed subscheme cut out by `E.pointsDivisor x`. -/
noncomputable def pointsDivisorSection (x : A → (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) (a : A) :
    S ⟶ (E.pointsDivisor x).subscheme :=
  IsClosedImmersion.lift (E.pointsDivisor x).subschemeι (x a).left
    ((ker_subschemeι _).symm ▸ pointsDivisor_le_ker x a)

variable {E}

/-- Composing `pointsDivisorSection x a` with the closed immersion of `∑_b [x b]` into `E` recovers
the section `(x a).left`. -/
@[reassoc (attr := simp)]
theorem pointsDivisorSection_subschemeι (x : A → (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) (a : A) :
    E.pointsDivisorSection x a ≫ (E.pointsDivisor x).subschemeι = (x a).left :=
  IsClosedImmersion.lift_fac _ _ _

/-- Each `pointsDivisorSection x a` is a section of `∑_b [x b]` over `S`. -/
@[reassoc]
theorem pointsDivisorSection_comp (x : A → (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) (a : A) :
    E.pointsDivisorSection x a ≫ ((E.pointsDivisor x).subschemeι ≫ E.structureMap) = 𝟙 S := by
  rw [← Category.assoc, pointsDivisorSection_subschemeι, left_comp_structureMap]

/-- **Katz–Mazur, 1.10.1** (ideal-sheaf form). Let `I` be an ideal sheaf on `E` cutting out a
closed subscheme finite locally free over `S` (in particular, any finite locally free closed
subgroup scheme `G ⊆ E`), and let `s : A → (S ⟶ I.subscheme)` be sections lifting a finite family
`x : A → E(S)`. Then `s` is a full set of sections of `V(I) ⟶ S` if and only if
`I = E.pointsDivisor x`. -/
theorem isFullSetOfSections_iff_eq_pointsDivisor {I : E.carrier.IdealSheafData}
    [IsFinite (I.subschemeι ≫ E.structureMap)] [Flat (I.subschemeι ≫ E.structureMap)]
    [LocallyOfFinitePresentation (I.subschemeι ≫ E.structureMap)]
    {x : A → (𝟙_ (Over S) ⟶ Over.mk E.structureMap)} {s : A → (S ⟶ I.subscheme)}
    (hs : ∀ a, s a ≫ (I.subschemeι ≫ E.structureMap) = 𝟙 S)
    (hlift : ∀ a, s a ≫ I.subschemeι = (x a).left) :
    IsFullSetOfSections (I.subschemeι ≫ E.structureMap) s hs ↔ I = E.pointsDivisor x := by
  rw [isFullSetOfSections_subschemeι_comp_iff hs, pointsDivisor_def]
  simp_rw [hlift]

/-- **The canonical lifts of `x : A → E(S)` form a full set of sections of `∑_a [x a]`**
(Katz–Mazur, 1.8.3 and 1.10.1). -/
theorem isFullSetOfSections_pointsDivisor (x : A → (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) :
    IsFullSetOfSections ((E.pointsDivisor x).subschemeι ≫ E.structureMap)
      (E.pointsDivisorSection x) (E.pointsDivisorSection_comp x) :=
  (isFullSetOfSections_iff_eq_pointsDivisor (E.pointsDivisorSection_comp x)
    (E.pointsDivisorSection_subschemeι x)).2 rfl

/-- **Katz–Mazur, 1.10.1** (closed-immersion form). Let `i : G ⟶ E` be a closed immersion such that
`G` is finite locally free over `S`, and let `s : A → (S ⟶ G)` be sections lifting a finite family
`x : A → E(S)`. Then `s` is a full set of sections of `G ⟶ S` if and only if
`i.ker = E.pointsDivisor x`. -/
theorem isFullSetOfSections_iff_ker_eq_pointsDivisor {G : Scheme.{u}} (i : G ⟶ E.carrier)
    [IsClosedImmersion i] [IsFinite (i ≫ E.structureMap)] [Flat (i ≫ E.structureMap)]
    [LocallyOfFinitePresentation (i ≫ E.structureMap)]
    {x : A → (𝟙_ (Over S) ⟶ Over.mk E.structureMap)} {s : A → (S ⟶ G)}
    (hs : ∀ a, s a ≫ (i ≫ E.structureMap) = 𝟙 S) (hlift : ∀ a, s a ≫ i = (x a).left) :
    IsFullSetOfSections (i ≫ E.structureMap) s hs ↔ i.ker = E.pointsDivisor x := by
  rw [isFullSetOfSections_iff_ker_eq_prod_ker i hs, pointsDivisor_def]
  simp_rw [hlift]

/-- The full-set locus of sections `s` of `V(I) ⟶ S` lifting `x : A → E(S)` is the equality locus
of `I` and `E.pointsDivisor x`. -/
theorem fullSetLocus_subschemeι_eq_equalityLocus_pointsDivisor {I : E.carrier.IdealSheafData}
    [IsFinite (I.subschemeι ≫ E.structureMap)] [Flat (I.subschemeι ≫ E.structureMap)]
    [LocallyOfFinitePresentation (I.subschemeι ≫ E.structureMap)]
    {x : A → (𝟙_ (Over S) ⟶ Over.mk E.structureMap)} {s : A → (S ⟶ I.subscheme)}
    (hs : ∀ a, s a ≫ (I.subschemeι ≫ E.structureMap) = 𝟙 S)
    (hlift : ∀ a, s a ≫ I.subschemeι = (x a).left) :
    fullSetLocus (I.subschemeι ≫ E.structureMap) s hs =
      equalityLocus E.structureMap I (E.pointsDivisor x) := by
  rw [fullSetLocus_subschemeι_comp_eq_equalityLocus hs]
  congr 1
  rw [pointsDivisor_def]
  simp_rw [hlift]

/-- The full-set locus of sections `s` of `i ≫ E.structureMap : G ⟶ S` lifting `x : A → E(S)` is
the equality locus of `i.ker` and `E.pointsDivisor x`. -/
theorem fullSetLocus_eq_equalityLocus_pointsDivisor {G : Scheme.{u}} (i : G ⟶ E.carrier)
    [IsClosedImmersion i] [IsFinite (i ≫ E.structureMap)] [Flat (i ≫ E.structureMap)]
    [LocallyOfFinitePresentation (i ≫ E.structureMap)]
    {x : A → (𝟙_ (Over S) ⟶ Over.mk E.structureMap)} {s : A → (S ⟶ G)}
    (hs : ∀ a, s a ≫ (i ≫ E.structureMap) = 𝟙 S) (hlift : ∀ a, s a ≫ i = (x a).left) :
    letI : IsFinite (i.ker.subschemeι ≫ E.structureMap) :=
      ((Iso.inv_comp_eq (asIso i.toImage)).mpr (i.toImage_imageι_assoc E.structureMap).symm) ▸
        inferInstance
    letI : Flat (i.ker.subschemeι ≫ E.structureMap) :=
      ((Iso.inv_comp_eq (asIso i.toImage)).mpr (i.toImage_imageι_assoc E.structureMap).symm) ▸
        inferInstance
    letI : LocallyOfFinitePresentation (i.ker.subschemeι ≫ E.structureMap) :=
      ((Iso.inv_comp_eq (asIso i.toImage)).mpr (i.toImage_imageι_assoc E.structureMap).symm) ▸
        inferInstance
    fullSetLocus (i ≫ E.structureMap) s hs =
      equalityLocus E.structureMap i.ker (E.pointsDivisor x) := by
  rw [fullSetLocus_eq_equalityLocus i hs]
  congr 1
  rw [pointsDivisor_def]
  simp_rw [hlift]

end PointsDivisor

/-! ### Drinfeld bases of `E[N]` as full sets of sections (Katz–Mazur 1.10.1, 1.10.13(1), §3.1) -/

section DrinfeldBasis

/-- For `n ≠ 0`, the `n`-torsion `E[n]` is finite over `S`. -/
instance isFinite_torsion_hom_of_neZero {n : ℤ} [NeZero n] :
    IsFinite (E.torsion n).X.hom :=
  E.isFinite_torsion_hom (NeZero.ne n)

/-- For `n ≠ 0`, the `n`-torsion `E[n]` is flat over `S`. -/
instance flat_torsion_hom_of_neZero {n : ℤ} [NeZero n] :
    Flat (E.torsion n).X.hom :=
  E.flat_torsion_hom (NeZero.ne n)

variable (N : ℕ)

/-- The section of `E[N] ⟶ S` assigned to `a ∈ (ℤ/Nℤ)²` by a homomorphism
`φ : (ℤ/Nℤ)² →* E(S)`. -/
noncomputable def torsionSection
    (φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap))
    (a : Multiplicative (ZMod N × ZMod N)) : S ⟶ (E.torsion N).X.left :=
  (E.torsionLift (φ a) (range_le_ker_mulBy φ ⟨a, rfl⟩)).left

/-- Composing `torsionSection E N φ a` with the closed immersion `E[N] ⟶ E` recovers `(φ a).left`.
-/
@[reassoc (attr := simp)]
theorem torsionSection_torsionι_left
    (φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap))
    (a : Multiplicative (ZMod N × ZMod N)) :
    E.torsionSection N φ a ≫ (E.torsionι N).left = (φ a).left :=
  congrArg Over.Hom.left (E.torsionLift_torsionι (φ a) _)

/-- Each `torsionSection E N φ a` is a section of the structure morphism `E[N] ⟶ S`. -/
@[reassoc (attr := simp)]
theorem torsionSection_hom
    (φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap))
    (a : Multiplicative (ZMod N × ZMod N)) :
    E.torsionSection N φ a ≫ (E.torsion N).X.hom = 𝟙 S := by
  rw [← torsionι_left_structureMap, ← Category.assoc, torsionSection_torsionι_left,
    left_comp_structureMap]

variable [NeZero N]

/-- **Drinfeld bases are `(ℤ/Nℤ)²`-full sets of sections of `E[N]`** (Katz–Mazur, 1.10.1 and §3.1).
A homomorphism `φ : (ℤ/Nℤ)² →* E(S)` is a Drinfeld basis of `E[N]` if and only if its induced
sections `torsionSection E N φ` form a full set of sections of the finite locally free `S`-scheme
`E[N]`. -/
theorem isDrinfeldBasis_iff_isFullSetOfSections
    (φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) :
    E.IsDrinfeldBasis N φ ↔
      IsFullSetOfSections (E.torsion N).X.hom (E.torsionSection N φ)
        (E.torsionSection_hom N φ) := by
  have hhom : (E.torsionι N).left ≫ E.structureMap = (E.torsion N).X.hom :=
    E.torsionι_left_structureMap N
  have : IsFinite ((E.torsionι N).left ≫ E.structureMap) := hhom.symm ▸ inferInstance
  have : Flat ((E.torsionι N).left ≫ E.structureMap) := hhom.symm ▸ inferInstance
  have : LocallyOfFinitePresentation ((E.torsionι N).left ≫ E.structureMap) :=
    hhom.symm ▸ inferInstance
  have hs' (a : Multiplicative (ZMod N × ZMod N)) :
      E.torsionSection N φ a ≫ ((E.torsionι N).left ≫ E.structureMap) = 𝟙 S := by
    rw [hhom, torsionSection_hom]
  rw [isFullSetOfSections_of_iso ((E.torsionι N).left ≫ E.structureMap) (E.torsionSection N φ) hs'
    (Iso.refl _) ((Category.id_comp _).trans hhom) (E.torsionSection_hom N φ)
    (fun a ↦ Category.comp_id _),
    isFullSetOfSections_iff_ker_eq_pointsDivisor (E.torsionι N).left hs'
      (E.torsionSection_torsionι_left N φ),
    isDrinfeldBasis_iff, ← ker_torsionι_left, eq_comm]

/-- **The Drinfeld-basis locus is the full-set locus on `E[N]`** (Katz–Mazur, 1.10.13(1) and §3.1).
For any homomorphism `φ : (ℤ/Nℤ)² →* E(S)`, the closed subscheme of `S` cut out by
`E.drinfeldBasisLocus N φ` agrees scheme-theoretically with `fullSetLocus` of the induced sections
of `E[N] ⟶ S`. -/
theorem drinfeldBasisLocus_eq_fullSetLocus
    (φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) :
    E.drinfeldBasisLocus N φ =
      fullSetLocus (E.torsion N).X.hom (E.torsionSection N φ) (E.torsionSection_hom N φ) := by
  have hhom : (E.torsionι N).left ≫ E.structureMap = (E.torsion N).X.hom :=
    E.torsionι_left_structureMap N
  let _ : IsFinite ((E.torsionι N).left ≫ E.structureMap) := hhom.symm ▸ inferInstance
  let _ : Flat ((E.torsionι N).left ≫ E.structureMap) := hhom.symm ▸ inferInstance
  let _ : LocallyOfFinitePresentation ((E.torsionι N).left ≫ E.structureMap) :=
    hhom.symm ▸ inferInstance
  have hs' (a : Multiplicative (ZMod N × ZMod N)) :
      E.torsionSection N φ a ≫ ((E.torsionι N).left ≫ E.structureMap) = 𝟙 S := by
    rw [hhom, torsionSection_hom]
  have hdrin : E.drinfeldBasisLocus N φ =
      equalityLocus E.structureMap (E.pointsDivisor φ) (E.torsionι N).left.ker := by
    have key {T' : Scheme.{u}} (r : T' ⟶ S) : E.drinfeldBasisLocus N φ ≤ r.ker ↔
        equalityLocus E.structureMap (E.pointsDivisor φ) (E.torsionι N).left.ker ≤ r.ker := by
      have hg := E.isPullback_baseChange r
      rw [← isDrinfeldBasis_pointsPullback_iff hg (by simp) φ, isDrinfeldBasis_iff,
        ← ker_torsionι_left, MonoidHom.coe_comp, pointsDivisor_pointsPullback,
        ker_torsionι_left_of_isPullback _ hg (by simp),
        equalityLocus_le_ker_iff_of_isPullback _ _ hg]
    exact le_antisymm
      (((key _).2 (ker_subschemeι _).ge).trans (ker_subschemeι _).le)
      (((key _).1 (ker_subschemeι _).ge).trans (ker_subschemeι _).le)
  rw [fullSetLocus_of_iso ((E.torsionι N).left ≫ E.structureMap) (E.torsionSection N φ) hs'
    (Iso.refl _) ((Category.id_comp _).trans hhom) (E.torsionSection_hom N φ)
    (fun a ↦ Category.comp_id _),
    fullSetLocus_eq_equalityLocus_pointsDivisor (E.torsionι N).left hs'
      (E.torsionSection_torsionι_left N φ),
    hdrin, equalityLocus_comm]

end DrinfeldBasis

/-! ### Multiples divisors and cyclic subgroups (Katz–Mazur 1.10.1, 1.10.5) -/

section MultiplesDivisor

/-- The canonical lift of `P ^ (a + 1)` (`a : Fin N`) to a section of the closed subscheme cut out
by `E.multiplesDivisor P N = [P] + [2P] + ⋯ + [NP]`. -/
noncomputable def multiplesDivisorSection (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) (N : ℕ)
    (a : Fin N) : S ⟶ (E.multiplesDivisor P N).subscheme :=
  IsClosedImmersion.lift (E.multiplesDivisor P N).subschemeι (P ^ (a.val + 1)).left
    ((ker_subschemeι _).symm ▸ E.multiplesDivisor_le_ker a.isLt)

variable {E}

/-- Composing `multiplesDivisorSection E P N a` with the closed immersion of
`[P] + [2P] + ⋯ + [NP]` into `E` recovers `(P ^ (a.val + 1)).left`. -/
@[reassoc (attr := simp)]
theorem multiplesDivisorSection_subschemeι (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) (N : ℕ)
    (a : Fin N) :
    E.multiplesDivisorSection P N a ≫ (E.multiplesDivisor P N).subschemeι =
      (P ^ (a.val + 1)).left :=
  IsClosedImmersion.lift_fac _ _ _

/-- Each `multiplesDivisorSection E P N a` is a section of `[P] + [2P] + ⋯ + [NP]` over `S`. -/
@[reassoc]
theorem multiplesDivisorSection_comp (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) (N : ℕ)
    (a : Fin N) :
    E.multiplesDivisorSection P N a ≫
      ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap) = 𝟙 S := by
  rw [← Category.assoc, multiplesDivisorSection_subschemeι, left_comp_structureMap]

/-- **The multiples `P, 2P, …, NP` form a full set of sections of `[P] + [2P] + ⋯ + [NP]`**
(Katz–Mazur, 1.8.3 and 1.10.1). -/
theorem isFullSetOfSections_multiplesDivisor (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) (N : ℕ) :
    IsFullSetOfSections ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap)
      (E.multiplesDivisorSection P N) (E.multiplesDivisorSection_comp P N) := by
  rw [isFullSetOfSections_iff_eq_pointsDivisor (E.multiplesDivisorSection_comp P N)
    (E.multiplesDivisorSection_subschemeι P N)]
  exact E.multiplesDivisor_eq_pointsDivisor P N

/-- **Katz–Mazur, 1.10.1 and 1.10.5**: sections `s : Fin N → (S ⟶ I.subscheme)` of a finite locally
free closed subscheme `V(I) ⊆ E` (in particular, any cyclic subgroup of order `N`) lifting
`P, 2P, …, NP` form a full set of sections of `V(I) ⟶ S` if and only if
`I = E.multiplesDivisor P N`. -/
theorem isFullSetOfSections_iff_eq_multiplesDivisor {I : E.carrier.IdealSheafData}
    [IsFinite (I.subschemeι ≫ E.structureMap)] [Flat (I.subschemeι ≫ E.structureMap)]
    [LocallyOfFinitePresentation (I.subschemeι ≫ E.structureMap)]
    {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {N : ℕ} {s : Fin N → (S ⟶ I.subscheme)}
    (hs : ∀ a, s a ≫ (I.subschemeι ≫ E.structureMap) = 𝟙 S)
    (hlift : ∀ a : Fin N, s a ≫ I.subschemeι = (P ^ (a.val + 1)).left) :
    IsFullSetOfSections (I.subschemeι ≫ E.structureMap) s hs ↔ I = E.multiplesDivisor P N := by
  rw [isFullSetOfSections_iff_eq_pointsDivisor hs hlift,
    ← E.multiplesDivisor_eq_pointsDivisor P N]

/-- The full-set locus of sections `s : Fin N → (S ⟶ I.subscheme)` lifting `P, 2P, …, NP` is the
equality locus of `I` and `E.multiplesDivisor P N`. -/
theorem fullSetLocus_subschemeι_eq_equalityLocus_multiplesDivisor {I : E.carrier.IdealSheafData}
    [IsFinite (I.subschemeι ≫ E.structureMap)] [Flat (I.subschemeι ≫ E.structureMap)]
    [LocallyOfFinitePresentation (I.subschemeι ≫ E.structureMap)]
    {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {N : ℕ} {s : Fin N → (S ⟶ I.subscheme)}
    (hs : ∀ a, s a ≫ (I.subschemeι ≫ E.structureMap) = 𝟙 S)
    (hlift : ∀ a : Fin N, s a ≫ I.subschemeι = (P ^ (a.val + 1)).left) :
    fullSetLocus (I.subschemeι ≫ E.structureMap) s hs =
      equalityLocus E.structureMap I (E.multiplesDivisor P N) := by
  have hcongr (J₁ J₂ : E.carrier.IdealSheafData)
      [IsFinite (J₁.subschemeι ≫ E.structureMap)] [Flat (J₁.subschemeι ≫ E.structureMap)]
      [LocallyOfFinitePresentation (J₁.subschemeι ≫ E.structureMap)]
      [IsFinite (J₂.subschemeι ≫ E.structureMap)] [Flat (J₂.subschemeι ≫ E.structureMap)]
      [LocallyOfFinitePresentation (J₂.subschemeι ≫ E.structureMap)] (h : J₁ = J₂) :
      equalityLocus E.structureMap I J₁ = equalityLocus E.structureMap I J₂ := by
    subst h; rfl
  exact (fullSetLocus_subschemeι_eq_equalityLocus_pointsDivisor hs hlift).trans
    (hcongr _ _ (E.multiplesDivisor_eq_pointsDivisor P N).symm)

end MultiplesDivisor

end TauCeti.AlgebraicGeometry.EllipticCurveGeom

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.DrinfeldBasis.Locus
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.ExactOrder.Subgroup
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Rank
public import TauCeti.AlgebraicGeometry.FullSetOfSections.Curve

/-!
# Full sets of sections and divisor sums on an elliptic curve

Let `E` be an elliptic curve over a scheme `S`. Specializing Theorem 1.8.3 of Katz and Mazur from
smooth separated curves (`TauCeti.AlgebraicGeometry.isFullSetOfSections_subschemeι_comp_iff`) to
`E ⟶ S` connects the divisor-based definitions of level structures on `E` to Katz–Mazur's
norm-based `A`-generators of finite locally free closed subschemes (Katz–Mazur, 1.10.1, 1.10.13,
and §3.1):

* For any finite family of `S`-points `x : A → E(S)` lifting to sections `s` of a finite locally
  free closed subscheme `G ⊆ E`, `s` is a full set of sections of `G ⟶ S` if and only if `G`
  equals `E.pointsDivisor x = ∑_a [x a]`, and the full-set locus on `S` equals the divisor
  equality locus (`equalityLocus`).
* Under `[NeZero N]`, when the `N`-torsion subgroup scheme `E[N] ⟶ S` is finite locally free, a
  homomorphism `φ : (ℤ/Nℤ)² →* E(S)` is a Drinfeld basis (`IsDrinfeldBasis`) if and only if its
  induced sections `torsionSection` form a `(ℤ/Nℤ)²`-full set of sections of `E[N] ⟶ S`, and
  `drinfeldBasisLocus` coincides scheme-theoretically with `fullSetLocus`.
* For an `S`-point `P` and `N : ℕ`, sections lifting `P, 2P, …, NP` to a finite locally free closed
  subscheme `G ⊆ E` (such as a cyclic subgroup scheme of order `N`) form a full set of sections if
  and only if `G` equals `E.multiplesDivisor P N = [P] + [2P] + ⋯ + [NP]`, with matching schematic
  loci on `S`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isFullSetOfSections_pointsDivisor`: the canonical
  lifts `pointsDivisorSection` of `x : A → E(S)` form a full set of sections of `∑_a [x a]`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isFullSetOfSections_iff_eq_pointsDivisor`,
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isFullSetOfSections_iff_ker_eq_pointsDivisor`,
  `EllipticCurveGeom.fullSetLocus_subschemeι_eq_equalityLocus_pointsDivisor`, and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.fullSetLocus_eq_equalityLocus_pointsDivisor`:
  Katz–Mazur 1.10.1 and schematic locus identifications, equating full sets of sections of a finite
  locally free closed subscheme of `E` with `pointsDivisor`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.drinfeldBasisLocus_eq_fullSetLocus` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isDrinfeldBasis_iff_isFullSetOfSections`: for
  `[NeZero N]`, the Drinfeld-basis locus equals the full-set locus on `E[N]`, so
  `φ : (ℤ/Nℤ)² →* E(S)` is a Drinfeld basis of `E[N]` iff `torsionSection` is a full set of
  sections of `E[N]`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isFullSetOfSections_multiplesDivisor`,
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isFullSetOfSections_iff_eq_multiplesDivisor`,
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isFullSetOfSections_iff_ker_eq_multiplesDivisor`,
  `EllipticCurveGeom.fullSetLocus_subschemeι_eq_equalityLocus_multiplesDivisor`, and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.fullSetLocus_eq_equalityLocus_multiplesDivisor`:
  full-set-of-sections characterization and locus identifications for `[P] + [2P] + ⋯ + [NP]`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, Theorem 1.8.3, §§1.10 (1.10.1, 1.10.13) and §3.1.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj
open Scheme.IdealSheafData

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-! ### Divisors of finite families of points (Katz–Mazur 1.10.1) -/

section PointsDivisor

variable {A : Type*} [Fintype A] {E}

/-- **Katz–Mazur, 1.10.1** (ideal-sheaf form): sections `s : A → (S ⟶ I.subscheme)` of `V(I) ⊆ E`
lifting `x : A → E(S)` form a full set of sections iff `I = E.pointsDivisor x`. -/
theorem isFullSetOfSections_iff_eq_pointsDivisor {I : E.carrier.IdealSheafData}
    [IsFinite (I.subschemeι ≫ E.structureMap)] [Flat (I.subschemeι ≫ E.structureMap)]
    [LocallyOfFinitePresentation (I.subschemeι ≫ E.structureMap)]
    {x : A → (𝟙_ (Over S) ⟶ Over.mk E.structureMap)} {s : A → (S ⟶ I.subscheme)}
    (hs : ∀ a, s a ≫ (I.subschemeι ≫ E.structureMap) = 𝟙 S)
    (hlift : ∀ a, s a ≫ I.subschemeι = (x a).left) :
    IsFullSetOfSections (I.subschemeι ≫ E.structureMap) s hs ↔ I = E.pointsDivisor x := by
  rw [isFullSetOfSections_subschemeι_comp_iff hs, pointsDivisor_def]; simp_rw [hlift]

variable (E) in
/-- **The canonical lifts of `x : A → E(S)` form a full set of sections of `∑_a [x a]`**
(Katz–Mazur, 1.8.3 and 1.10.1). -/
theorem isFullSetOfSections_pointsDivisor (x : A → (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) :
    IsFullSetOfSections ((E.pointsDivisor x).subschemeι ≫ E.structureMap)
      (E.pointsDivisorSection x) (E.pointsDivisorSection_comp x) :=
  (isFullSetOfSections_iff_eq_pointsDivisor (E.pointsDivisorSection_comp x)
    (E.pointsDivisorSection_subschemeι x)).2 rfl

/-- **Katz–Mazur, 1.10.1** (closed-immersion form): for `i : G ⟶ E` finite locally free over `S`,
sections `s` lifting `x : A → E(S)` form a full set of sections iff `i.ker = E.pointsDivisor x`. -/
theorem isFullSetOfSections_iff_ker_eq_pointsDivisor {G : Scheme.{u}} (i : G ⟶ E.carrier)
    [IsClosedImmersion i] [IsFinite (i ≫ E.structureMap)] [Flat (i ≫ E.structureMap)]
    [LocallyOfFinitePresentation (i ≫ E.structureMap)]
    {x : A → (𝟙_ (Over S) ⟶ Over.mk E.structureMap)} {s : A → (S ⟶ G)}
    (hs : ∀ a, s a ≫ (i ≫ E.structureMap) = 𝟙 S) (hlift : ∀ a, s a ≫ i = (x a).left) :
    IsFullSetOfSections (i ≫ E.structureMap) s hs ↔ i.ker = E.pointsDivisor x := by
  rw [isFullSetOfSections_iff_ker_eq_prod_ker i hs, pointsDivisor_def]; simp_rw [hlift]

/-- The full-set locus of sections of `V(I) ⟶ S` lifting `x` is `equalityLocus` with `∑_a [x a]`. -/
theorem fullSetLocus_subschemeι_eq_equalityLocus_pointsDivisor {I : E.carrier.IdealSheafData}
    [IsFinite (I.subschemeι ≫ E.structureMap)] [Flat (I.subschemeι ≫ E.structureMap)]
    [LocallyOfFinitePresentation (I.subschemeι ≫ E.structureMap)]
    {x : A → (𝟙_ (Over S) ⟶ Over.mk E.structureMap)} {s : A → (S ⟶ I.subscheme)}
    (hs : ∀ a, s a ≫ (I.subschemeι ≫ E.structureMap) = 𝟙 S)
    (hlift : ∀ a, s a ≫ I.subschemeι = (x a).left) :
    fullSetLocus (I.subschemeι ≫ E.structureMap) s hs =
      equalityLocus E.structureMap I (E.pointsDivisor x) := by
  rw [fullSetLocus_subschemeι_comp_eq_equalityLocus hs]; congr 1
  rw [pointsDivisor_def]; simp_rw [hlift]

/-- The full-set locus of sections of `G ⟶ S` lifting `x` is `equalityLocus` with `∑_a [x a]`. -/
theorem fullSetLocus_eq_equalityLocus_pointsDivisor {G : Scheme.{u}} (i : G ⟶ E.carrier)
    [IsClosedImmersion i] [IsFinite (i ≫ E.structureMap)] [Flat (i ≫ E.structureMap)]
    [LocallyOfFinitePresentation (i ≫ E.structureMap)]
    {x : A → (𝟙_ (Over S) ⟶ Over.mk E.structureMap)} {s : A → (S ⟶ G)}
    (hs : ∀ a, s a ≫ (i ≫ E.structureMap) = 𝟙 S) (hlift : ∀ a, s a ≫ i = (x a).left) :
    fullSetLocus (i ≫ E.structureMap) s hs =
      equalityLocus E.structureMap i.ker (E.pointsDivisor x) := by
  rw [fullSetLocus_eq_equalityLocus i hs]; congr 1; rw [pointsDivisor_def]; simp_rw [hlift]

end PointsDivisor

/-! ### Drinfeld bases of `E[N]` as full sets of sections (Katz–Mazur 1.10.1, 1.10.13(1), §3.1) -/

section DrinfeldBasis

variable (N : ℕ) [NeZero N]

/-- **The Drinfeld-basis locus is the full-set locus on `E[N]`** (Katz–Mazur, 1.10.13(1), §3.1). -/
theorem drinfeldBasisLocus_eq_fullSetLocus
    (φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) :
    E.drinfeldBasisLocus N φ =
      fullSetLocus (E.torsion N).X.hom (E.torsionSection N φ) (E.torsionSection_hom N φ) := by
  have hhom := E.torsionι_left_structureMap N
  let _ : IsFinite ((E.torsionι N).left ≫ E.structureMap) := hhom.symm ▸ inferInstance
  let _ : Flat ((E.torsionι N).left ≫ E.structureMap) := hhom.symm ▸ inferInstance
  let _ : LocallyOfFinitePresentation ((E.torsionι N).left ≫ E.structureMap) :=
    hhom.symm ▸ inferInstance
  have hs' (a : Multiplicative (ZMod N × ZMod N)) :
      E.torsionSection N φ a ≫ ((E.torsionι N).left ≫ E.structureMap) = 𝟙 S := by
    rw [hhom, torsionSection_hom]
  rw [fullSetLocus_eq_of_iso ((E.torsionι N).left ≫ E.structureMap) (E.torsionSection N φ) hs'
    (Iso.refl _) ((Category.id_comp _).trans hhom) (E.torsionSection_hom N φ)
    (fun _ ↦ Category.comp_id _), fullSetLocus_eq_equalityLocus_pointsDivisor (E.torsionι N).left
    hs' (E.torsionSection_torsionι_left N φ), drinfeldBasisLocus_def, equalityLocus_comm]

/-- **Drinfeld bases are `(ℤ/Nℤ)²`-full sets of sections of `E[N]`** (Katz–Mazur, 1.10.1, §3.1). -/
theorem isDrinfeldBasis_iff_isFullSetOfSections
    (φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) :
    E.IsDrinfeldBasis N φ ↔ IsFullSetOfSections (E.torsion N).X.hom (E.torsionSection N φ)
      (E.torsionSection_hom N φ) := by
  rw [isDrinfeldBasis_iff_drinfeldBasisLocus_eq_bot, drinfeldBasisLocus_eq_fullSetLocus,
    isFullSetOfSections_iff_fullSetLocus_eq_bot]

end DrinfeldBasis

/-! ### Multiples divisors `[P] + [2P] + ⋯ + [NP]` (Katz–Mazur 1.10.1) -/

section MultiplesDivisor

variable {E}

/-- **The multiples `P, 2P, …, NP` form a full set of sections of `[P] + [2P] + ⋯ + [NP]`**
(Katz–Mazur, 1.8.3 and 1.10.1). -/
theorem isFullSetOfSections_multiplesDivisor (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) (N : ℕ) :
    IsFullSetOfSections ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap)
      (E.multiplesDivisorSection P N) (E.multiplesDivisorSection_comp P N) :=
  (isFullSetOfSections_iff_eq_pointsDivisor (E.multiplesDivisorSection_comp P N)
    (E.multiplesDivisorSection_subschemeι P N)).2 (E.multiplesDivisor_eq_pointsDivisor P N)

/-- **Katz–Mazur, 1.10.1** (ideal-sheaf form for multiples divisors): sections lifting
`P, 2P, …, NP` to `V(I) ⊆ E` form a full set of sections iff `I = E.multiplesDivisor P N`. -/
theorem isFullSetOfSections_iff_eq_multiplesDivisor {I : E.carrier.IdealSheafData}
    [IsFinite (I.subschemeι ≫ E.structureMap)] [Flat (I.subschemeι ≫ E.structureMap)]
    [LocallyOfFinitePresentation (I.subschemeι ≫ E.structureMap)]
    {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {N : ℕ} {s : Fin N → (S ⟶ I.subscheme)}
    (hs : ∀ a, s a ≫ (I.subschemeι ≫ E.structureMap) = 𝟙 S)
    (hlift : ∀ a : Fin N, s a ≫ I.subschemeι = (P ^ (a.val + 1)).left) :
    IsFullSetOfSections (I.subschemeι ≫ E.structureMap) s hs ↔ I = E.multiplesDivisor P N := by
  rw [isFullSetOfSections_iff_eq_pointsDivisor hs hlift, ← E.multiplesDivisor_eq_pointsDivisor P N]

/-- **Katz–Mazur, 1.10.1** (closed-immersion form for multiples divisors): sections lifting
`P, 2P, …, NP` to `G ⊆ E` form a full set of sections iff `i.ker = E.multiplesDivisor P N`. -/
theorem isFullSetOfSections_iff_ker_eq_multiplesDivisor {G : Scheme.{u}} (i : G ⟶ E.carrier)
    [IsClosedImmersion i] [IsFinite (i ≫ E.structureMap)] [Flat (i ≫ E.structureMap)]
    [LocallyOfFinitePresentation (i ≫ E.structureMap)]
    {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {N : ℕ} {s : Fin N → (S ⟶ G)}
    (hs : ∀ a, s a ≫ (i ≫ E.structureMap) = 𝟙 S)
    (hlift : ∀ a : Fin N, s a ≫ i = (P ^ (a.val + 1)).left) :
    IsFullSetOfSections (i ≫ E.structureMap) s hs ↔ i.ker = E.multiplesDivisor P N := by
  rw [isFullSetOfSections_iff_ker_eq_pointsDivisor i hs hlift,
    ← E.multiplesDivisor_eq_pointsDivisor P N]

/-- The full-set locus of sections lifting `P, 2P, …, NP` to `V(I)` is `equalityLocus` with
`E.multiplesDivisor P N`. -/
theorem fullSetLocus_subschemeι_eq_equalityLocus_multiplesDivisor {I : E.carrier.IdealSheafData}
    [IsFinite (I.subschemeι ≫ E.structureMap)] [Flat (I.subschemeι ≫ E.structureMap)]
    [LocallyOfFinitePresentation (I.subschemeι ≫ E.structureMap)]
    {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {N : ℕ} {s : Fin N → (S ⟶ I.subscheme)}
    (hs : ∀ a, s a ≫ (I.subschemeι ≫ E.structureMap) = 𝟙 S)
    (hlift : ∀ a : Fin N, s a ≫ I.subschemeι = (P ^ (a.val + 1)).left) :
    fullSetLocus (I.subschemeι ≫ E.structureMap) s hs =
      equalityLocus E.structureMap I (E.multiplesDivisor P N) := by
  rw [fullSetLocus_subschemeι_eq_equalityLocus_pointsDivisor hs hlift]
  congr 1; exact (E.multiplesDivisor_eq_pointsDivisor P N).symm

/-- The full-set locus of sections lifting `P, 2P, …, NP` to `G` is `equalityLocus` with
`E.multiplesDivisor P N`. -/
theorem fullSetLocus_eq_equalityLocus_multiplesDivisor {G : Scheme.{u}} (i : G ⟶ E.carrier)
    [IsClosedImmersion i] [IsFinite (i ≫ E.structureMap)] [Flat (i ≫ E.structureMap)]
    [LocallyOfFinitePresentation (i ≫ E.structureMap)]
    {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {N : ℕ} {s : Fin N → (S ⟶ G)}
    (hs : ∀ a, s a ≫ (i ≫ E.structureMap) = 𝟙 S)
    (hlift : ∀ a : Fin N, s a ≫ i = (P ^ (a.val + 1)).left) :
    fullSetLocus (i ≫ E.structureMap) s hs =
      equalityLocus E.structureMap i.ker (E.multiplesDivisor P N) := by
  rw [fullSetLocus_eq_equalityLocus_pointsDivisor i hs hlift]
  congr 1; exact (E.multiplesDivisor_eq_pointsDivisor P N).symm

end MultiplesDivisor

end TauCeti.AlgebraicGeometry.EllipticCurveGeom

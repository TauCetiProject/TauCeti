/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.LaurentChart.Field
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integral
public import TauCeti.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Algebra.Tower

/-!
# Generating Laurent charts and total quotient rings

Regular generation means that the ambient commutative algebra is the total quotient ring
of the faithful Laurent image. The chart also identifies the ambient algebra with the total
quotient ring of its polynomial algebra. The chosen chart supplies each algebra structure
explicitly; no second global algebra structure is imposed on the ambient algebra.

For an ambient field, generation agrees with generation by the image as a subfield. In this
case the coordinates form a transcendence basis, and a proper coordinate subfamily cannot
generate the field. The canonical Laurent and polynomial models are constructed in
`LaurentChart/Standard.lean`.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras I: Foundations*, §§2–3.
-/

public section

namespace TauCeti.LaurentChart

variable {R K F G : Type*}

section CommRing
variable [CommRing R] [CommRing F] [Algebra R F] [CommRing G] [Algebra R G]

/-- A regular chart generates when its ambient algebra is its total ring of fractions. -/
def Generates (c : LaurentChart R K F) : Prop :=
  let _ := c.toAlgHom.toRingHom.toAlgebra
  IsFractionRing (LaurentRing R K) F

/-- A generating chart supplies the total ring of fractions under chart evaluation. -/
theorem isFractionRing (c : LaurentChart R K F) (h : c.Generates) :
    let _ := c.toAlgHom.toRingHom.toAlgebra
    IsFractionRing (LaurentRing R K) F := h

/-- Public characterization of regular generation by the chart-induced localization structure. -/
theorem generates_iff_isFractionRing (c : LaurentChart R K F) :
    c.Generates ↔
      letI := c.toAlgHom.toRingHom.toAlgebra
      IsFractionRing (LaurentRing R K) F := Iff.rfl

/-- Every ambient element of a generating regular chart has a regular Laurent denominator. -/
theorem Generates.exists_mul {c : LaurentChart R K F} (h : c.Generates) (z : F) :
    ∃ p : LaurentRing R K, ∃ q : nonZeroDivisors (LaurentRing R K), z * c q = c p := by
  let _ := c.toAlgHom.toRingHom.toAlgebra
  have : IsFractionRing (LaurentRing R K) F := c.isFractionRing h
  obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors (LaurentRing R K)) z
  exact ⟨p, q, hpq⟩

/-- Relabelling the Laurent variables preserves regular generation. -/
theorem Generates.reindex {c : LaurentChart R K F} (h : c.Generates) {K' : Type*}
    (e : K ≃ K') : (c.reindex e).Generates := by
  let _ := c.toAlgHom.toRingHom.toAlgebra
  let _ := (c.reindex e).toAlgHom.toRingHom.toAlgebra
  have : IsFractionRing (LaurentRing R K) F := c.isFractionRing h
  apply IsFractionRing.of_ringEquiv_left (LaurentRing.renameEquiv R e.symm).toRingEquiv
  intro p
  change (c.reindex e) p = c (LaurentRing.renameEquiv R e.symm p)
  simpa only [LaurentRing.renameEquiv_apply] using c.reindex_apply e p

/-- Relabelling coordinates does not change regular generation. -/
@[simp]
theorem generates_reindex_iff (c : LaurentChart R K F) {K' : Type*} (e : K ≃ K') :
    (c.reindex e).Generates ↔ c.Generates := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.reindex e⟩
  simpa using h.reindex e.symm

/-- A generating faithful chart also supplies the total quotient ring of its polynomial ring. -/
theorem isFractionRing_mvPolynomial (c : LaurentChart R K F) (h : c.Generates) :
    let _ := (c.toAlgHom.comp MvPolynomial.toLaurent).toRingHom.toAlgebra
    IsFractionRing (MvPolynomial K R) F := by
  let _ := c.toAlgHom.toRingHom.toAlgebra
  let _ := (c.toAlgHom.comp MvPolynomial.toLaurent).toRingHom.toAlgebra
  have : IsScalarTower (MvPolynomial K R) (LaurentRing R K) F :=
    .of_algebraMap_eq fun _ ↦ rfl
  have : IsFractionRing (LaurentRing R K) F := c.isFractionRing h
  exact TauCeti.IsFractionRing.of_isLocalization_of_isFractionRing
    (Submonoid.closure (Set.range (MvPolynomial.X : K → MvPolynomial K R)))
    (LaurentRing R K) F
    (Submonoid.closure_le.mpr <| by
      rintro p ⟨i, rfl⟩
      exact isRegular_iff_mem_nonZeroDivisors.mp (MvPolynomial.isRegular_X (n := i)))

/-- Algebra maps out of a generating ambient algebra are determined by its coordinates. -/
theorem Generates.algHom_ext {c : LaurentChart R K F} (h : c.Generates)
    {A : Type*} [Semiring A] [Algebra R A] {f g : F →ₐ[R] A}
    (hfg : ∀ i, f (c.coordinate i) = g (c.coordinate i)) : f = g := by
  let _ := c.toAlgHom.toRingHom.toAlgebra
  have : IsFractionRing (LaurentRing R K) F := c.isFractionRing h
  have : IsScalarTower R (LaurentRing R K) F := IsScalarTower.of_algHom c.toAlgHom
  apply IsLocalization.algHom_ext (nonZeroDivisors (LaurentRing R K))
  -- The canonical map of this tower is the chart-induced algebra map.
  have hmap : Algebra.algHom R (LaurentRing R K) F = c.toAlgHom := by rfl
  rw [hmap]
  apply LaurentRing.algHom_ext
  intro i
  simpa only [AlgHom.comp_apply, toAlgHom_apply, apply_X] using hfg i

/-- The total quotient ring of the Laurent ring is canonically the ambient algebra of a generating
  chart. -/
noncomputable def fractionRingEquiv (c : LaurentChart R K F) (h : c.Generates) :
    FractionRing (LaurentRing R K) ≃ₐ[R] F := by
  let _ := c.toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower R (LaurentRing R K) F :=
    .of_algebraMap_eq fun r ↦ (c.toAlgHom.commutes r).symm
  have : IsFractionRing (LaurentRing R K) F := c.isFractionRing h
  exact (FractionRing.algEquiv (LaurentRing R K) F).restrictScalars R

@[simp]
theorem fractionRingEquiv_algebraMap (c : LaurentChart R K F) (h : c.Generates)
    (p : LaurentRing R K) :
    c.fractionRingEquiv h (algebraMap _ (FractionRing (LaurentRing R K)) p) = c p := by
  let _ := c.toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower R (LaurentRing R K) F :=
    .of_algebraMap_eq fun r ↦ (c.toAlgHom.commutes r).symm
  have : IsFractionRing (LaurentRing R K) F := c.isFractionRing h
  rw [fractionRingEquiv, AlgEquiv.restrictScalars_apply, AlgEquiv.commutes]
  simp only [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, toAlgHom_apply]

/-- The inverse total-quotient equivalence recovers the canonical class of a chart value. -/
@[simp↓]
theorem fractionRingEquiv_symm_apply (c : LaurentChart R K F) (h : c.Generates)
    (p : LaurentRing R K) :
    (c.fractionRingEquiv h).symm (c p) =
      algebraMap _ (FractionRing (LaurentRing R K)) p := by
  apply (c.fractionRingEquiv h).injective
  simp

/-- The inverse total-quotient equivalence sends a chart coordinate to its Laurent variable. -/
@[simp↓]
theorem fractionRingEquiv_symm_apply_coordinate (c : LaurentChart R K F) (h : c.Generates)
    (i : K) : (c.fractionRingEquiv h).symm (c.coordinate i) =
      algebraMap _ (FractionRing (LaurentRing R K)) (LaurentRing.X (R := R) i) := by
  simpa only [apply_X] using c.fractionRingEquiv_symm_apply h (LaurentRing.X i)

/-- Inverse total-quotient evaluation sends an inverse coordinate to its negative monomial. -/
@[simp↓]
theorem fractionRingEquiv_symm_apply_inv_coordinateUnit (c : LaurentChart R K F)
    (h : c.Generates) (i : K) :
    (c.fractionRingEquiv h).symm (((c.coordinateUnit i)⁻¹ : Fˣ) : F) =
      algebraMap _ (FractionRing (LaurentRing R K))
        (AddMonoidAlgebra.single (-Finsupp.single i 1) 1 : LaurentRing R K) := by
  apply (c.fractionRingEquiv h).injective
  simp only [fractionRingEquiv_algebraMap, AlgEquiv.apply_symm_apply,
    apply_single_neg_single_one]

/-- The polynomial rational-function model is canonically the ambient algebra of a generating
  chart. -/
noncomputable def fractionRingMvPolynomialEquiv (c : LaurentChart R K F) (h : c.Generates) :
    FractionRing (MvPolynomial K R) ≃ₐ[R] F := by
  let f := c.toAlgHom.comp MvPolynomial.toLaurent
  let _ := f.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial K R) F :=
    .of_algebraMap_eq fun r ↦ (f.commutes r).symm
  have : IsFractionRing (MvPolynomial K R) F := c.isFractionRing_mvPolynomial h
  exact (FractionRing.algEquiv (MvPolynomial K R) F).restrictScalars R

@[simp]
theorem fractionRingMvPolynomialEquiv_algebraMap (c : LaurentChart R K F) (h : c.Generates)
    (p : MvPolynomial K R) :
    c.fractionRingMvPolynomialEquiv h (algebraMap _ (FractionRing (MvPolynomial K R)) p) =
      MvPolynomial.aeval c.coordinate p := by
  let f := c.toAlgHom.comp MvPolynomial.toLaurent
  let _ := f.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial K R) F :=
    .of_algebraMap_eq fun r ↦ (f.commutes r).symm
  have : IsFractionRing (MvPolynomial K R) F := c.isFractionRing_mvPolynomial h
  rw [fractionRingMvPolynomialEquiv, AlgEquiv.restrictScalars_apply, AlgEquiv.commutes,
    RingHom.algebraMap_toAlgebra]
  simpa only [f, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
    DFunLike.congr_fun c.comp_toLaurent p

/-- The inverse polynomial total-quotient equivalence recovers a polynomial from its
coordinate evaluation. -/
@[simp↓]
theorem fractionRingMvPolynomialEquiv_symm_aeval (c : LaurentChart R K F) (h : c.Generates)
    (p : MvPolynomial K R) :
    (c.fractionRingMvPolynomialEquiv h).symm (MvPolynomial.aeval c.coordinate p) =
      algebraMap _ (FractionRing (MvPolynomial K R)) p := by
  apply (c.fractionRingMvPolynomialEquiv h).injective
  simp

/-- The inverse polynomial total-quotient equivalence sends coordinates to polynomial variables. -/
@[simp↓]
theorem fractionRingMvPolynomialEquiv_symm_apply_coordinate (c : LaurentChart R K F)
    (h : c.Generates) (i : K) :
    (c.fractionRingMvPolynomialEquiv h).symm (c.coordinate i) =
      algebraMap _ (FractionRing (MvPolynomial K R)) (MvPolynomial.X (R := R) i) := by
  simpa only [MvPolynomial.aeval_X] using
    c.fractionRingMvPolynomialEquiv_symm_aeval h (MvPolynomial.X i)

/-- Change of generating Laurent chart on the canonical total-quotient models. The coordinate
index types may differ; both charts have the same ambient algebra. -/
noncomputable def fractionRingTransition {K' : Type*} (c : LaurentChart R K F)
    (d : LaurentChart R K' F) (hc : c.Generates) (hd : d.Generates) :
    FractionRing (LaurentRing R K) ≃ₐ[R] FractionRing (LaurentRing R K') :=
  (c.fractionRingEquiv hc).trans (d.fractionRingEquiv hd).symm

/-- The total-quotient transition is the composite through the common ambient algebra. -/
theorem fractionRingTransition_def {K' : Type*} (c : LaurentChart R K F)
    (d : LaurentChart R K' F) (hc : c.Generates) (hd : d.Generates) :
    c.fractionRingTransition d hc hd = (c.fractionRingEquiv hc).trans
      (d.fractionRingEquiv hd).symm := (rfl)

/-- Evaluate change of total-quotient chart on any fraction, without an overlap hypothesis. -/
theorem fractionRingTransition_apply {K' : Type*} (c : LaurentChart R K F)
    (d : LaurentChart R K' F) (hc : c.Generates) (hd : d.Generates)
    (x : FractionRing (LaurentRing R K)) :
    c.fractionRingTransition d hc hd x =
      (d.fractionRingEquiv hd).symm (c.fractionRingEquiv hc x) := (rfl)

/-- On a Laurent polynomial class, transition is inverse evaluation in the target chart. -/
@[simp↓]
theorem fractionRingTransition_algebraMap {K' : Type*} (c : LaurentChart R K F)
    (d : LaurentChart R K' F) (hc : c.Generates) (hd : d.Generates) (p : LaurentRing R K) :
    c.fractionRingTransition d hc hd (algebraMap _ (FractionRing (LaurentRing R K)) p) =
      (d.fractionRingEquiv hd).symm (c p) := by
  rw [fractionRingTransition_apply, fractionRingEquiv_algebraMap]

@[simp]
theorem fractionRingTransition_self (c : LaurentChart R K F) (hc : c.Generates) :
    c.fractionRingTransition c hc hc = AlgEquiv.refl := by
  ext x
  simp [fractionRingTransition]

@[simp]
theorem fractionRingTransition_symm {K' : Type*} (c : LaurentChart R K F)
    (d : LaurentChart R K' F) (hc : c.Generates) (hd : d.Generates) :
    (c.fractionRingTransition d hc hd).symm = d.fractionRingTransition c hd hc := by
  ext x
  rfl

@[simp]
theorem fractionRingTransition_trans {K' K'' : Type*} (c : LaurentChart R K F)
    (d : LaurentChart R K' F) (e : LaurentChart R K'' F)
    (hc : c.Generates) (hd : d.Generates) (he : e.Generates) :
    (c.fractionRingTransition d hc hd).trans (d.fractionRingTransition e hd he) =
      c.fractionRingTransition e hc he := by
  ext x
  simp [fractionRingTransition]

/-- Consecutive changes of fraction coordinates compose pointwise. -/
@[simp]
theorem fractionRingTransition_fractionRingTransition {K' K'' : Type*} (c : LaurentChart R K F)
    (d : LaurentChart R K' F) (e : LaurentChart R K'' F)
    (hc : c.Generates) (hd : d.Generates) (he : e.Generates)
    (x : FractionRing (LaurentRing R K)) :
    d.fractionRingTransition e hd he (c.fractionRingTransition d hc hd x) =
      c.fractionRingTransition e hc he x := by
  simp only [fractionRingTransition_apply, AlgEquiv.apply_symm_apply]

/-- Evaluating a fraction transition agrees with its source chart's evaluation. -/
@[simp]
theorem fractionRingEquiv_fractionRingTransition {K' : Type*} (c : LaurentChart R K F)
    (d : LaurentChart R K' F) (hc : c.Generates) (hd : d.Generates)
    (x : FractionRing (LaurentRing R K)) :
    d.fractionRingEquiv hd (c.fractionRingTransition d hc hd x) =
      c.fractionRingEquiv hc x := by
  simp only [fractionRingTransition_apply, AlgEquiv.apply_symm_apply]

/-- Changing fraction coordinates commutes with inverse evaluation from the ambient algebra. -/
@[simp]
theorem fractionRingTransition_fractionRingEquiv_symm {K' : Type*}
    (c : LaurentChart R K F) (d : LaurentChart R K' F) (hc : c.Generates) (hd : d.Generates)
    (z : F) :
    c.fractionRingTransition d hc hd ((c.fractionRingEquiv hc).symm z) =
      (d.fractionRingEquiv hd).symm z := by
  simp only [fractionRingTransition_apply, AlgEquiv.apply_symm_apply]

/-- A bijective ambient algebra map preserves regular generation. -/
theorem Generates.map {c : LaurentChart R K F} (h : c.Generates)
    {f : F →ₐ[R] G} (hf : Function.Injective f) (hs : Function.Surjective f) :
    (c.map f hf).Generates := by
  let _ := c.toAlgHom.toRingHom.toAlgebra
  let _ := (c.map f hf).toAlgHom.toRingHom.toAlgebra
  have : IsFractionRing (LaurentRing R K) F := c.isFractionRing h
  change IsFractionRing (LaurentRing R K) G
  let e : F ≃ₐ[LaurentRing R K] G :=
    { (AlgEquiv.ofBijective f ⟨hf, hs⟩).toRingEquiv with
      commutes' := fun p ↦ by
        change f (c p) = (c.map f hf) p
        exact (c.map_apply f hf p).symm }
  exact IsFractionRing.of_algEquiv e

/-- Ambient algebra equivalences preserve and reflect regular generation. -/
@[simp]
theorem generates_map_algEquiv_iff (c : LaurentChart R K F) (e : F ≃ₐ[R] G) :
    (c.map e.toAlgHom e.injective).Generates ↔ c.Generates := by
  constructor
  · intro h
    have hh := h.map (f := e.symm.toAlgHom) e.symm.injective e.symm.surjective
    have he : (c.map e.toAlgHom e.injective).map e.symm.toAlgHom e.symm.injective = c := by
      ext i
      calc
        _ = e.symm ((c.map e.toAlgHom e.injective).coordinate i) :=
          (c.map e.toAlgHom e.injective).coordinate_map e.symm.toAlgHom e.symm.injective i
        _ = e.symm (e (c.coordinate i)) :=
          congrArg e.symm (c.coordinate_map e.toAlgHom e.injective i)
        _ = c.coordinate i := e.symm_apply_apply _
    rwa [he] at hh
  · intro h
    exact h.map (f := e.toAlgHom) e.injective e.surjective

/-- Fraction evaluation commutes with an injective ambient algebra map when both charts generate. -/
theorem toAlgHom_fractionRingEquiv_map (c : LaurentChart R K F) (f : F →ₐ[R] G)
    (hf : Function.Injective f) (hc : c.Generates) (h : (c.map f hf).Generates) :
    ((c.map f hf).fractionRingEquiv h).toAlgHom = f.comp (c.fractionRingEquiv hc).toAlgHom := by
  apply IsLocalization.algHom_ext (nonZeroDivisors (LaurentRing R K))
  apply LaurentRing.algHom_ext
  intro i
  simp [Algebra.algHom]

/-- Pointwise fraction evaluation commutes with the ambient map. -/
theorem fractionRingEquiv_map_apply (c : LaurentChart R K F) (f : F →ₐ[R] G)
    (hf : Function.Injective f) (hc : c.Generates) (h : (c.map f hf).Generates)
    (z : FractionRing (LaurentRing R K)) :
    (c.map f hf).fractionRingEquiv h z = f (c.fractionRingEquiv hc z) :=
  DFunLike.congr_fun (c.toAlgHom_fractionRingEquiv_map f hf hc h) z

/-- The polynomial fraction model has the same ambient-map compatibility. -/
theorem toAlgHom_fractionRingMvPolynomialEquiv_map (c : LaurentChart R K F)
    (f : F →ₐ[R] G) (hf : Function.Injective f) (hc : c.Generates)
    (h : (c.map f hf).Generates) :
    ((c.map f hf).fractionRingMvPolynomialEquiv h).toAlgHom =
      f.comp (c.fractionRingMvPolynomialEquiv hc).toAlgHom := by
  apply IsLocalization.algHom_ext (nonZeroDivisors (MvPolynomial K R))
  apply MvPolynomial.algHom_ext
  intro i
  simp [Algebra.algHom]

/-- A simultaneous ambient embedding leaves the fraction transition unchanged whenever both
source charts and both target charts generate. -/
theorem fractionRingTransition_map_of_generates {K' : Type*} (c : LaurentChart R K F)
    (d : LaurentChart R K' F) (f : F →ₐ[R] G) (hf : Function.Injective f)
    (hc : c.Generates) (hd : d.Generates)
    (hc' : (c.map f hf).Generates) (hd' : (d.map f hf).Generates) :
    (c.map f hf).fractionRingTransition (d.map f hf) hc' hd' =
      c.fractionRingTransition d hc hd := by
  ext z
  apply ((d.map f hf).fractionRingEquiv hd').injective
  rw [fractionRingEquiv_fractionRingTransition, fractionRingEquiv_map_apply c f hf hc hc',
    fractionRingEquiv_map_apply d f hf hd hd', fractionRingEquiv_fractionRingTransition]

/-- Inverse fraction evaluation recovers a constructor-normal Laurent evaluation. -/
@[simp↓]
theorem fractionRingEquiv_ofCoordinates_symm_aeval (x : K → Fˣ)
    (hx : AlgebraicIndependent R fun i ↦ (x i : F)) (h : (ofCoordinates x hx).Generates)
    (p : LaurentRing R K) :
    ((ofCoordinates x hx).fractionRingEquiv h).symm (LaurentRing.aeval x p) =
      algebraMap _ (FractionRing (LaurentRing R K)) p := by
  simpa only [ofCoordinates_apply] using (ofCoordinates x hx).fractionRingEquiv_symm_apply h p

/-- Inverse polynomial fraction evaluation recovers a constructor-normal polynomial value. -/
@[simp↓]
theorem fractionRingMvPolynomialEquiv_ofCoordinates_symm_aeval (x : K → Fˣ)
    (hx : AlgebraicIndependent R fun i ↦ (x i : F)) (h : (ofCoordinates x hx).Generates)
    (p : MvPolynomial K R) :
    ((ofCoordinates x hx).fractionRingMvPolynomialEquiv h).symm
      (MvPolynomial.aeval (fun i ↦ (x i : F)) p) =
        algebraMap _ (FractionRing (MvPolynomial K R)) p := by
  simpa only [show (ofCoordinates x hx).coordinate = (fun i ↦ (x i : F)) from
    funext (coordinate_ofCoordinates x hx)] using
      (ofCoordinates x hx).fractionRingMvPolynomialEquiv_symm_aeval h p

/-- Reindex the canonical Laurent fraction model using the existing localization equivalence. -/
@[simp]
theorem fractionRingEquiv_reindex {K' : Type*} (c : LaurentChart R K F) (σ : K ≃ K')
    (h : (c.reindex σ).Generates) :
    (c.reindex σ).fractionRingEquiv h =
      (IsFractionRing.algEquivOfAlgEquiv (K := FractionRing (LaurentRing R K'))
        (L := FractionRing (LaurentRing R K)) (LaurentRing.renameEquiv R σ.symm)).trans
          (c.fractionRingEquiv ((c.generates_reindex_iff σ).mp h)) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply IsLocalization.algHom_ext (nonZeroDivisors (LaurentRing R K'))
  apply LaurentRing.algHom_ext
  intro i
  simp [Algebra.algHom, LaurentRing.renameEquiv_apply]

/-- Reindex the polynomial fraction model by the existing total-quotient functor. -/
@[simp]
theorem fractionRingMvPolynomialEquiv_reindex {K' : Type*}
    (c : LaurentChart R K F) (σ : K ≃ K') (h : (c.reindex σ).Generates) :
    (c.reindex σ).fractionRingMvPolynomialEquiv h =
      (IsFractionRing.algEquivOfAlgEquiv (K := FractionRing (MvPolynomial K' R))
        (L := FractionRing (MvPolynomial K R)) (MvPolynomial.renameEquiv R σ.symm)).trans
          (c.fractionRingMvPolynomialEquiv ((c.generates_reindex_iff σ).mp h)) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply IsLocalization.algHom_ext (nonZeroDivisors (MvPolynomial K' R))
  apply MvPolynomial.algHom_ext
  intro i
  simp [Algebra.algHom, MvPolynomial.renameEquiv_apply]

/-- On the overlap of two chart ranges, change of total-quotient chart sends the first Laurent
expansion to the second Laurent expansion of the same ambient element. -/
theorem fractionRingTransition_algebraMap_laurentExpansion {K' : Type*}
    (c : LaurentChart R K F) (d : LaurentChart R K' F)
    (hc : c.Generates) (hd : d.Generates) (z : F)
    (hz : z ∈ c.range ⊓ d.range) :
    c.fractionRingTransition d hc hd
        (algebraMap _ (FractionRing (LaurentRing R K)) (c.laurentExpansion ⟨z, hz.1⟩)) =
      algebraMap _ (FractionRing (LaurentRing R K')) (d.laurentExpansion ⟨z, hz.2⟩) := by
  apply (d.fractionRingEquiv hd).injective
  simp

end CommRing

section Field
variable [CommRing R] [Field F] [Algebra R F] [Field G] [Algebra R G]

/-- In an ambient field the inverse coordinate has the same negative Laurent fraction class. -/
@[simp↓]
theorem fractionRingEquiv_symm_apply_inv_coordinate (c : LaurentChart R K F)
    (h : c.Generates) (i : K) :
    (c.fractionRingEquiv h).symm (c.coordinate i)⁻¹ =
      algebraMap _ (FractionRing (LaurentRing R K))
        (AddMonoidAlgebra.single (-Finsupp.single i 1) 1 : LaurentRing R K) := by
  simpa only [Units.val_inv_eq_inv_val, val_coordinateUnit] using
    c.fractionRingEquiv_symm_apply_inv_coordinateUnit h i

/-- For fields, regular generation agrees with generation by the chart image as a subfield. -/
theorem generates_iff (c : LaurentChart R K F) :
    c.Generates ↔ Subfield.closure (Set.range c) = ⊤ := by
  constructor
  · intro h
    let _ := c.toAlgHom.toRingHom.toAlgebra
    have : IsFractionRing (LaurentRing R K) F := c.isFractionRing h
    exact IsFractionRing.closure_range_algebraMap (LaurentRing R K) F
  · intro h
    let _ := c.toAlgHom.toRingHom.toAlgebra
    have : FaithfulSMul (LaurentRing R K) F :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr c.injective
    apply IsFractionRing.of_field
    intro z
    have hz : z ∈ Subfield.closure (Set.range c) := by rw [h]; trivial
    obtain ⟨x, hx, y, hy, hxy⟩ := Subfield.mem_closure_iff.mp hz
    have hr : Subring.closure (Set.range c) = c.toAlgHom.toRingHom.range :=
      Subring.closure_eq c.toAlgHom.toRingHom.range
    rw [hr] at hx hy
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    exact ⟨p, q, hxy.symm⟩

/-- Every ambient field value has a quotient expression with a nonzero Laurent denominator. -/
theorem Generates.exists_div {c : LaurentChart R K F} (h : c.Generates) (z : F) :
    ∃ p q : LaurentRing R K, q ≠ 0 ∧ c p / c q = z := by
  let _ := c.toAlgHom.toRingHom.toAlgebra
  have : IsFractionRing (LaurentRing R K) F := c.isFractionRing h
  have : IsDomain R := c.isDomain
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (LaurentRing R K) z
  exact ⟨p, q, mem_nonZeroDivisors_iff_ne_zero.mp hq, hpq⟩

/-- Generated subfields commute with every ambient field embedding. -/
theorem closure_range_map (c : LaurentChart R K F) (f : F →ₐ[R] G) :
    Subfield.closure (Set.range (c.map f f.toRingHom.injective)) =
      (Subfield.closure (Set.range c)).map f.toRingHom := by
  have hr : Set.range (c.map f f.toRingHom.injective) = f.toRingHom '' Set.range c := by
    calc
      Set.range (c.map f f.toRingHom.injective) = Set.range (f.toRingHom ∘ c) := by
        congr 1
        funext p
        exact c.map_apply f f.toRingHom.injective p
      _ = f.toRingHom '' Set.range c := Set.range_comp _ _
  rw [hr]
  exact (RingHom.map_field_closure f.toRingHom _).symm

/-- An embedded chart generates precisely when the original chart generates and the ambient
embedding is surjective. -/
theorem generates_map_iff (c : LaurentChart R K F) (f : F →ₐ[R] G) :
    (c.map f f.toRingHom.injective).Generates ↔ c.Generates ∧ Function.Surjective f := by
  rw [generates_iff, closure_range_map]
  constructor
  · intro h
    have hc : Subfield.closure (Set.range c) = ⊤ := by
      rw [← Subfield.comap_map f.toRingHom (Subfield.closure (Set.range c)),
        h, Subfield.comap_top]
    exact ⟨c.generates_iff.mpr hc, RingHom.fieldRange_eq_top_iff.mp
      ((RingHom.fieldRange_eq_map f.toRingHom).trans (hc ▸ h))⟩
  · rintro ⟨h, hf⟩
    rw [c.generates_iff.mp h]
    exact (RingHom.fieldRange_eq_map f.toRingHom).symm.trans
      (RingHom.fieldRange_eq_top_iff.mpr hf)

/-- Inverting the variables does not change the generated subfield. -/
theorem closure_range_comp_toLaurent (c : LaurentChart R K F) :
    Subfield.closure (Set.range (c.toAlgHom.comp MvPolynomial.toLaurent)) =
      Subfield.closure (Set.range c) := by
  apply le_antisymm
  · apply Subfield.closure_mono
    rintro _ ⟨p, rfl⟩
    exact ⟨MvPolynomial.toLaurent p, rfl⟩
  · apply Subfield.closure_le.mpr
    rintro _ ⟨f, rfl⟩
    let M := Submonoid.closure (Set.range (MvPolynomial.X : K → MvPolynomial K R))
    obtain ⟨⟨p, m⟩, hp⟩ := IsLocalization.surj M f
    have hm : c (MvPolynomial.toLaurent (m : MvPolynomial K R)) ≠ 0 := by
      exact ((IsLocalization.map_units (LaurentRing R K) m).map c.toAlgHom).ne_zero
    have heq : c f = c (MvPolynomial.toLaurent p) /
        c (MvPolynomial.toLaurent (m : MvPolynomial K R)) := by
      apply (eq_div_iff hm).mpr
      simpa using congrArg c hp
    rw [heq]
    apply Subfield.div_mem <;> exact Subfield.subset_closure ⟨_, rfl⟩

/-- The chart image and the coefficients together with coordinates generate the same subfield. -/
theorem closure_range_eq (c : LaurentChart R K F) :
    Subfield.closure (Set.range c) =
      Subfield.closure (Set.range (algebraMap R F) ∪ Set.range c.coordinate) := by
  rw [← c.closure_range_comp_toLaurent, c.comp_toLaurent]
  have hr : Subring.closure (Set.range (MvPolynomial.aeval (R := R) c.coordinate)) =
      Subring.closure (Set.range (algebraMap R F) ∪ Set.range c.coordinate) := by
    rw [← AlgHom.coe_range, ← Subalgebra.coe_toSubring, Subring.closure_eq,
      MvPolynomial.aeval_range, Algebra.adjoin_eq_ring_closure]
  ext z
  simp_rw [Subfield.mem_closure_iff, hr]

/-- Generation can be checked on coefficients and coordinates. -/
theorem generates_iff_closure_range_coordinate (c : LaurentChart R K F) :
    c.Generates ↔
      Subfield.closure (Set.range (algebraMap R F) ∪ Set.range c.coordinate) = ⊤ := by
  rw [generates_iff, closure_range_eq]

/-- A chart constructed from independent units generates exactly when those units together
with the coefficient image generate the ambient field. -/
@[simp]
theorem generates_ofCoordinates_iff (x : K → Fˣ)
    (hx : AlgebraicIndependent R fun i ↦ (x i : F)) :
    (ofCoordinates x hx).Generates ↔
      Subfield.closure (Set.range (algebraMap R F) ∪ Set.range fun i ↦ (x i : F)) = ⊤ := by
  rw [generates_iff_closure_range_coordinate]
  rw [show (ofCoordinates x hx).coordinate = (fun i ↦ (x i : F)) from
    funext (coordinate_ofCoordinates x hx)]

/-- Generation is equivalent to a quotient expression for every ambient value. -/
theorem generates_iff_exists_div (c : LaurentChart R K F) :
    c.Generates ↔ ∀ z : F, ∃ p q : LaurentRing R K, q ≠ 0 ∧ c p / c q = z := by
  refine ⟨fun h ↦ h.exists_div, fun h ↦ ?_⟩
  apply (c.generates_iff).mpr
  apply top_unique
  intro z _
  obtain ⟨p, q, -, rfl⟩ := h z
  exact Subfield.div_mem _ (Subfield.subset_closure ⟨p, rfl⟩)
    (Subfield.subset_closure ⟨q, rfl⟩)

/-- Coordinates of a generating chart are a transcendence basis of the ambient field. -/
theorem isTranscendenceBasis (c : LaurentChart R K F) (h : c.Generates) :
    IsTranscendenceBasis R c.coordinate := by
  have : IsDomain R := c.isDomain
  let _ := (c.toAlgHom.comp MvPolynomial.toLaurent).toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial K R) F :=
    IsScalarTower.of_algHom (c.toAlgHom.comp MvPolynomial.toLaurent)
  have : IsFractionRing (MvPolynomial K R) F := c.isFractionRing_mvPolynomial h
  have : Algebra.IsAlgebraic (MvPolynomial K R) F :=
    IsFractionRing.comap_isAlgebraic_iff.mpr (inferInstance : Algebra.IsAlgebraic F F)
  simpa only [Function.comp_def, RingHom.algebraMap_toAlgebra,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.comp_apply,
    toAlgHom_apply, apply_toLaurent, MvPolynomial.aeval_X] using
    (IsTranscendenceBasis.mvPolynomial K R).algebraMap_comp (A := F)

/-- A coordinate subfamily generates exactly when the original chart generates and every
coordinate was retained. -/
@[simp]
theorem generates_restrict_iff (c : LaurentChart R K F) {K' : Type*} (f : K' ↪ K) :
    (c.restrict f).Generates ↔ c.Generates ∧ Function.Surjective f := by
  have : IsDomain R := c.isDomain
  constructor
  · intro h
    have hc : c.Generates := by
      apply c.generates_iff.mpr
      apply top_unique
      rw [← (c.restrict f).generates_iff.mp h]
      apply Subfield.closure_mono
      rintro _ ⟨p, rfl⟩
      exact ⟨LaurentRing.rename f p, (c.restrict_apply f p).symm⟩
    refine ⟨hc, ?_⟩
    have hb := (c.restrict f).isTranscendenceBasis h
    have hs : Set.range (c.restrict f).coordinate ⊆ Set.range c.coordinate := by
      rintro _ ⟨i, rfl⟩
      exact ⟨f i, by simp⟩
    have heq := hb.2 (Set.range c.coordinate) c.algebraicIndependent.coe_range hs
    intro j
    have hj : c.coordinate j ∈ Set.range (c.restrict f).coordinate := by
      rw [heq]
      exact ⟨j, rfl⟩
    obtain ⟨i, hi⟩ := hj
    exact ⟨i, c.algebraicIndependent.injective (by simpa using hi)⟩
  · rintro ⟨h, hf⟩
    let e := Equiv.ofBijective f ⟨f.injective, hf⟩
    have he : c.restrict f = c.reindex e.symm := by
      ext i
      simp only [coordinate_restrict, coordinate_reindex, Equiv.symm_symm]
      exact congrArg c.coordinate
        (congrFun (Equiv.coe_ofBijective f ⟨f.injective, hf⟩) i).symm
    rw [he]
    exact (c.generates_reindex_iff e.symm).mpr h

/-- A proper coordinate subfamily cannot generate the ambient field. -/
theorem not_generates_restrict (c : LaurentChart R K F) {K' : Type*} (f : K' ↪ K)
    (hf : ¬ Function.Surjective f) : ¬ (c.restrict f).Generates :=
  fun h ↦ hf ((c.generates_restrict_iff f).mp h).2

/-- Ambient algebra equivalences transport the canonical Laurent fraction-field equivalence. -/
@[simp]
theorem fractionRingEquiv_map (c : LaurentChart R K F) (e : F ≃ₐ[R] G)
    (h : (c.map e.toAlgHom e.injective).Generates) :
    (c.map e.toAlgHom e.injective).fractionRingEquiv h =
      (c.fractionRingEquiv ((c.generates_map_algEquiv_iff e).mp h)).trans e := by
  apply AlgEquiv.coe_toAlgHom_injective
  exact c.toAlgHom_fractionRingEquiv_map e.toAlgHom e.injective
    ((c.generates_map_algEquiv_iff e).mp h) h

/-- For ambient fields, generation of both transported charts suffices for transition transport
along any algebra homomorphism, without assuming surjectivity in advance. -/
@[simp]
theorem fractionRingTransition_map {K' : Type*} (c : LaurentChart R K F)
    (d : LaurentChart R K' F) (f : F →ₐ[R] G)
    (hc : (c.map f f.toRingHom.injective).Generates)
    (hd : (d.map f f.toRingHom.injective).Generates) :
    (c.map f f.toRingHom.injective).fractionRingTransition
        (d.map f f.toRingHom.injective) hc hd =
      c.fractionRingTransition d ((c.generates_map_iff f).mp hc).1
        ((d.generates_map_iff f).mp hd).1 :=
  c.fractionRingTransition_map_of_generates d f f.toRingHom.injective
    ((c.generates_map_iff f).mp hc).1 ((d.generates_map_iff f).mp hd).1 hc hd

/-- Ambient algebra equivalences transport the canonical polynomial fraction-field model. -/
@[simp]
theorem fractionRingMvPolynomialEquiv_map (c : LaurentChart R K F) (e : F ≃ₐ[R] G)
    (h : (c.map e.toAlgHom e.injective).Generates) :
    (c.map e.toAlgHom e.injective).fractionRingMvPolynomialEquiv h =
      (c.fractionRingMvPolynomialEquiv ((c.generates_map_algEquiv_iff e).mp h)).trans e := by
  apply AlgEquiv.coe_toAlgHom_injective
  exact c.toAlgHom_fractionRingMvPolynomialEquiv_map e.toAlgHom e.injective
    ((c.generates_map_algEquiv_iff e).mp h) h

/-- Inverse Laurent fraction evaluation at a unit-family coordinate in constructor normal form. -/
@[simp↓]
theorem fractionRingEquiv_ofCoordinates_symm_coordinate (x : K → Fˣ)
    (hx : AlgebraicIndependent R fun i ↦ (x i : F)) (h : (ofCoordinates x hx).Generates) (i : K) :
    ((ofCoordinates x hx).fractionRingEquiv h).symm (x i : F) =
      algebraMap _ (FractionRing (LaurentRing R K)) (LaurentRing.X (R := R) i) := by
  simpa only [coordinate_ofCoordinates] using
    (ofCoordinates x hx).fractionRingEquiv_symm_apply_coordinate h i

/-- Inverse Laurent fraction evaluation at an inverse unit-family coordinate. -/
@[simp↓]
theorem fractionRingEquiv_ofCoordinates_symm_inv_coordinate (x : K → Fˣ)
    (hx : AlgebraicIndependent R fun i ↦ (x i : F)) (h : (ofCoordinates x hx).Generates) (i : K) :
    ((ofCoordinates x hx).fractionRingEquiv h).symm ((x i : F)⁻¹) =
      algebraMap _ (FractionRing (LaurentRing R K))
        (AddMonoidAlgebra.single (-Finsupp.single i 1) 1 : LaurentRing R K) := by
  simpa only [coordinate_ofCoordinates] using
    (ofCoordinates x hx).fractionRingEquiv_symm_apply_inv_coordinate h i

/-- Inverse polynomial fraction evaluation at a unit-family coordinate. -/
@[simp↓]
theorem fractionRingMvPolynomialEquiv_ofCoordinates_symm_coordinate (x : K → Fˣ)
    (hx : AlgebraicIndependent R fun i ↦ (x i : F)) (h : (ofCoordinates x hx).Generates) (i : K) :
    ((ofCoordinates x hx).fractionRingMvPolynomialEquiv h).symm (x i : F) =
      algebraMap _ (FractionRing (MvPolynomial K R)) (MvPolynomial.X (R := R) i) := by
  simpa only [coordinate_ofCoordinates] using
    (ofCoordinates x hx).fractionRingMvPolynomialEquiv_symm_apply_coordinate h i

/-- Generating charts correspond to field-generating transcendence bases. -/
noncomputable def generatingCoordinatesEquiv :
    {c : LaurentChart R K F // c.Generates} ≃
      {x : K → F // IsTranscendenceBasis R x ∧
        Subfield.closure (Set.range (algebraMap R F) ∪ Set.range x) = ⊤} where
  toFun c := ⟨c.1.coordinate, c.1.isTranscendenceBasis c.2,
    c.1.generates_iff_closure_range_coordinate.mp c.2⟩
  invFun x := by
    have : IsDomain R := Function.Injective.isDomain (algebraMap R F) x.2.1.1.algebraMap_injective
    let u : K → Fˣ := fun i ↦ Units.mk0 (x.1 i) (x.2.1.1.ne_zero i)
    let c := ofCoordinates u (by simpa [u] using x.2.1.1)
    refine ⟨c, c.generates_iff_closure_range_coordinate.mpr ?_⟩
    have hc : c.coordinate = x.1 := funext fun i ↦ by simp [c, u]
    rw [hc]
    exact x.2.2
  left_inv c := by
    apply Subtype.ext
    ext i
    simp
  right_inv x := by
    apply Subtype.ext
    funext i
    simp

@[simp]
theorem val_generatingCoordinatesEquiv_apply (c : {c : LaurentChart R K F // c.Generates}) :
    (generatingCoordinatesEquiv c).1 = c.1.coordinate := (rfl)

@[simp]
theorem coordinate_val_generatingCoordinatesEquiv_symm_apply
    (x : {x : K → F // IsTranscendenceBasis R x ∧
      Subfield.closure (Set.range (algebraMap R F) ∪ Set.range x) = ⊤}) :
    (generatingCoordinatesEquiv.symm x).1.coordinate = x.1 := by
  funext i
  simp [generatingCoordinatesEquiv]

end Field

end TauCeti.LaurentChart

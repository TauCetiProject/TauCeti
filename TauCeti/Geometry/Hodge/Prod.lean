/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import TauCeti.Geometry.Hodge.Zero
public import TauCeti.LinearAlgebra.Submodule.Compl
import Mathlib.Analysis.Complex.Basic
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# Direct sums of polarizable pure Hodge structures

The direct sum of two pure Hodge structures of the same weight `n` carries the product filtration
`F^p ⊕ F'^p` on the product space, and its Hodge components are the products of the Hodge
components. Opposedness is inherited factor by factor because a conjugation acting componentwise
turns a product of subspaces into the product of their conjugates.

A polarization of the direct sum is the block-diagonal form `Q ⊕ Q'`: the two summands are
orthogonal to each other, and the Hodge–Riemann positivity of a nonzero vector `(x, y)` is the sum
of the two contributions, of which one is positive and the other nonnegative.

Consequently the category of polarizable rational Hodge structures of weight `n` has binary
biproducts, and with the zero object it has all finite biproducts: a finite family of polarizable
Hodge structures has a direct sum which is again one. This is the ambient structure in which the
decomposition of a polarizable Hodge structure into simple ones is an isomorphism onto a direct
sum of objects.

## Main declarations

* `TauCeti.Hodge.HodgeStructureOn.prod`: the direct sum of two pure Hodge structures of the same
  weight, with `TauCeti.Hodge.HodgeStructureOn.prod_piece` describing its Hodge components.
* `TauCeti.Hodge.IsPolarization.prod`: the block-diagonal form polarizes the direct sum.
* `TauCeti.Hodge.Polarization.prod`: the direct sum of two polarizations.
* `TauCeti.Hodge.IsPolarizable.prod`: a direct sum of polarizable structures is polarizable.
* `TauCeti.Hodge.PolarizableHodgeStructureCat.hasFiniteBiproducts`: the resulting finite
  biproducts in the category of polarizable rational Hodge structures.

## References

Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1.2; Peters--Steenbrink, *Mixed Hodge
Structures*, §2.

The categorical bicone construction follows `TauCeti.Geometry.Hodge.Mixed.Prod`.
-/

public section

namespace TauCeti.Hodge

universe u v w

/-! ### The direct sum of two pure Hodge structures -/

section Structure

variable {W : Type u} {W' : Type v} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
variable {ω : Conjugation W} {ω' : Conjugation W'} {Ω : Conjugation (W × W')} {n : ℤ}

namespace HodgeStructureOn

variable (hs : HodgeStructureOn W ω n) (hs' : HodgeStructureOn W' ω' n)
variable (hΩ : ∀ x : W × W', Ω.toEquiv x = (ω.toEquiv x.1, ω'.toEquiv x.2))

/-- The direct sum of two Hodge structures of the same weight, filtered by the products of the
two filtrations.

The conjugation `Ω` of the product space is required to act componentwise; for the canonical
conjugation of a product of complexifications this is
`TauCeti.Hodge.latticeConjugation_prodMap_toEquiv_apply`. -/
def prod : HodgeStructureOn (W × W') Ω n where
  F p := (hs.F p).prod (hs'.F p)
  F_antitone _ _ hpq := Submodule.prod_mono (hs.F_antitone hpq) (hs'.F_antitone hpq)
  F_top := by
    obtain ⟨i, hi⟩ := hs.F_top
    obtain ⟨j, hj⟩ := hs'.F_top
    exact ⟨min i j, by
      rw [eq_top_mono (hs.F_antitone (min_le_left i j)) hi,
        eq_top_mono (hs'.F_antitone (min_le_right i j)) hj, Submodule.prod_top]⟩
  opposed p := by
    rw [Conjugation.map_prod hΩ]
    exact (hs.opposed p).prod (hs'.opposed p)

/-- The Hodge filtration of a direct sum is the product of the two Hodge filtrations. -/
@[simp]
theorem prod_F (p : ℤ) : (hs.prod hs' hΩ).F p = (hs.F p).prod (hs'.F p) :=
  (rfl)

/-- The conjugate filtration of a direct sum is the product of the two conjugate filtrations. -/
@[simp]
theorem prod_conjF (p : ℤ) : (hs.prod hs' hΩ).conjF p = (hs.conjF p).prod (hs'.conjF p) := by
  rw [conjF_def, conjF_def, conjF_def, prod_F, Conjugation.map_prod hΩ]

/-- The Hodge components of a direct sum are the products of the Hodge components. -/
@[simp]
theorem prod_piece (p : ℤ) : (hs.prod hs' hΩ).piece p = (hs.piece p).prod (hs'.piece p) := by
  rw [piece_def, piece_def, piece_def, prod_F, prod_conjF, Submodule.prod_inf_prod]

end HodgeStructureOn

end Structure

/-! ### The direct sum of two polarizations -/

section Polarization

variable {V : Type u} {V' : Type v} {Vℂ : Type w} {V'ℂ : Type*}
variable [AddCommGroup V] [AddCommGroup V'] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable [AddCommGroup V'ℂ] [Module ℂ V'ℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ} {ι'ℂ : V' →ₗ[ℤ] V'ℂ}
variable {hℂ : IsBaseChange ℂ ιℂ} {h'ℂ : IsBaseChange ℂ ι'ℂ} {n : ℤ}
variable {hs : HodgeStructure hℂ n} {hs' : HodgeStructure h'ℂ n}

open scoped ComplexOrder

/-- The block-diagonal form of two polarizing forms polarizes the direct sum: the summands are
orthogonal to each other, so both Hodge–Riemann relations are inherited componentwise. -/
theorem IsPolarization.prod {Q : LinearMap.BilinForm ℤ V} {Q' : LinearMap.BilinForm ℤ V'}
    (h : IsPolarization hℂ hs Q) (h' : IsPolarization h'ℂ hs' Q') :
    IsPolarization (IsBaseChange.prodMap ιℂ ι'ℂ hℂ h'ℂ)
      (hs.prod hs' (latticeConjugation_prodMap_toEquiv_apply hℂ h'ℂ)) (Q.prod Q') where
  symm_weight x y := by
    rw [LinearMap.BilinForm.prod_apply, LinearMap.BilinForm.prod_apply, h.symm_weight x.1 y.1,
      h'.symm_weight x.2 y.2, mul_add]
  nondegenerate :=
    LinearMap.BilinForm.nondegenerate_prod_iff.2 ⟨h.nondegenerate, h'.nondegenerate⟩
  orthogonal p x hx y hy := by
    obtain ⟨hx1, hx2⟩ := (Submodule.mem_prod (p := hs.F p) (q := hs'.F p)).mp hx
    obtain ⟨hy1, hy2⟩ :=
      (Submodule.mem_prod (p := hs.F (n + 1 - p)) (q := hs'.F (n + 1 - p))).mp hy
    rw [integralFormBaseChange_prod hℂ h'ℂ, LinearMap.BilinForm.prod_apply,
      h.orthogonal p x.1 hx1 y.1 hy1, h'.orthogonal p x.2 hx2 y.2 hy2, add_zero]
  positive p x hx hx0 := by
    rw [HodgeStructureOn.prod_piece] at hx
    obtain ⟨hx1, hx2⟩ := (Submodule.mem_prod (p := hs.piece p) (q := hs'.piece p)).mp hx
    rw [integralFormBaseChange_prod hℂ h'ℂ, latticeConj_prodMap hℂ h'ℂ,
      LinearMap.BilinForm.prod_apply, mul_add]
    have hfst : 0 ≤ Complex.I ^ (2 * p - n) * integralFormBaseChange hℂ Q x.1
        (latticeConj hℂ x.1) := by
      rcases eq_or_ne x.1 0 with hzero | hne
      · simp [hzero]
      · exact (h.positive p x.1 hx1 hne).le
    have hsnd : 0 ≤ Complex.I ^ (2 * p - n) * integralFormBaseChange h'ℂ Q' x.2
        (latticeConj h'ℂ x.2) := by
      rcases eq_or_ne x.2 0 with hzero | hne
      · simp [hzero]
      · exact (h'.positive p x.2 hx2 hne).le
    rcases eq_or_ne x.1 0 with hzero | hne
    · have hne' : x.2 ≠ 0 := fun hzero' ↦ hx0 (by simp [Prod.ext_iff, hzero, hzero'])
      exact add_pos_of_nonneg_of_pos hfst (h'.positive p x.2 hx2 hne')
    · exact add_pos_of_pos_of_nonneg (h.positive p x.1 hx1 hne) hsnd

/-- The direct sum of two polarizations of pure Hodge structures of the same weight. -/
noncomputable def Polarization.prod (P : Polarization hℂ hs) (P' : Polarization h'ℂ hs') :
    Polarization (IsBaseChange.prodMap ιℂ ι'ℂ hℂ h'ℂ)
      (hs.prod hs' (latticeConjugation_prodMap_toEquiv_apply hℂ h'ℂ)) where
  Qint := P.Qint.prod P'.Qint
  isPolarization := P.isPolarization.prod P'.isPolarization

/-- The integral form of a direct sum of polarizations is block diagonal. -/
@[simp]
theorem Polarization.prod_Qint (P : Polarization hℂ hs) (P' : Polarization h'ℂ hs') :
    (P.prod P').Qint = P.Qint.prod P'.Qint :=
  (rfl)

/-- The complex form of a direct sum of polarizations is block diagonal. -/
@[simp]
theorem Polarization.prod_Q (P : Polarization hℂ hs) (P' : Polarization h'ℂ hs') :
    (P.prod P').Q = P.Q.prod P'.Q := by
  rw [Polarization.Q_def, Polarization.Q_def, Polarization.Q_def, Polarization.prod_Qint,
    integralFormBaseChange_prod]

/-- A direct sum of polarizable pure Hodge structures is polarizable. -/
theorem IsPolarizable.prod (h : IsPolarizable hℂ hs) (h' : IsPolarizable h'ℂ hs') :
    IsPolarizable (IsBaseChange.prodMap ιℂ ι'ℂ hℂ h'ℂ)
      (hs.prod hs' (latticeConjugation_prodMap_toEquiv_apply hℂ h'ℂ)) := by
  obtain ⟨P⟩ := isPolarizable_iff_nonempty.1 h
  obtain ⟨P'⟩ := isPolarizable_iff_nonempty.1 h'
  exact (P.prod P').isPolarizable

end Polarization

/-! ### Finite biproducts in the category of polarizable Hodge structures -/

namespace PolarizableHodgeStructureCat

open CategoryTheory Limits

variable {n : ℤ}

/-- The binary direct-sum bicone: product carriers, product filtration, and the usual inclusions
and projections of vector spaces. -/
private noncomputable def binaryBicone (X Y : PolarizableHodgeStructureCat.{u} n) :
    BinaryBicone X Y where
  pt := of (IsBaseChange.prodMap X.toRat Y.toRat X.isBaseChangeRat Y.isBaseChangeRat)
    (IsBaseChange.prodMap X.toComplex Y.toComplex X.isBaseChangeComplex Y.isBaseChangeComplex)
    (X.hs.prod Y.hs (latticeConjugation_prodMap_toEquiv_apply _ _))
    (X.isPolarizable.prod Y.isPolarizable)
  fst := Hom.mk (LinearMap.fst ℚ X.ratCarrier Y.ratCarrier) fun p _ hx ↦ by
    rw [rationalMapToComplex_fst X.isBaseChangeRat X.isBaseChangeComplex Y.isBaseChangeRat
      Y.isBaseChangeComplex]
    exact ((Submodule.mem_prod (p := X.hs.F p) (q := Y.hs.F p)).mp hx).1
  snd := Hom.mk (LinearMap.snd ℚ X.ratCarrier Y.ratCarrier) fun p _ hx ↦ by
    rw [rationalMapToComplex_snd X.isBaseChangeRat X.isBaseChangeComplex Y.isBaseChangeRat
      Y.isBaseChangeComplex]
    exact ((Submodule.mem_prod (p := X.hs.F p) (q := Y.hs.F p)).mp hx).2
  inl := Hom.mk (LinearMap.inl ℚ X.ratCarrier Y.ratCarrier) fun p _ hx ↦ by
    rw [rationalMapToComplex_inl X.isBaseChangeRat X.isBaseChangeComplex Y.isBaseChangeRat
      Y.isBaseChangeComplex]
    exact (Submodule.mem_prod (p := X.hs.F p) (q := Y.hs.F p)).mpr ⟨hx, (Y.hs.F p).zero_mem⟩
  inr := Hom.mk (LinearMap.inr ℚ X.ratCarrier Y.ratCarrier) fun p _ hx ↦ by
    rw [rationalMapToComplex_inr X.isBaseChangeRat X.isBaseChangeComplex Y.isBaseChangeRat
      Y.isBaseChangeComplex]
    exact (Submodule.mem_prod (p := X.hs.F p) (q := Y.hs.F p)).mpr ⟨(X.hs.F p).zero_mem, hx⟩
  inl_fst := by apply Hom.ext; simp
  inl_snd := by apply Hom.ext; simp
  inr_fst := by apply Hom.ext; simp
  inr_snd := by apply Hom.ext; simp

/-- The binary direct sum is both a product and a coproduct. -/
private noncomputable def binaryBiconeIsBilimit (X Y : PolarizableHodgeStructureCat.{u} n) :
    (binaryBicone X Y).IsBilimit := by
  apply isBinaryBilimitOfTotal
  apply Hom.ext
  rw [add_toRatLinearMap]
  -- Unfold the private bicone to identify its four maps on the rational product carrier.
  simp only [binaryBicone, comp_toRatLinearMap, id_toRatLinearMap, Hom.mk_toRatLinearMap]
  exact LinearMap.coprod_inl_inr

noncomputable instance hasBinaryBiproducts :
    HasBinaryBiproducts (PolarizableHodgeStructureCat.{u} n) where
  has_binary_biproduct X Y :=
    HasBinaryBiproduct.mk ⟨binaryBicone X Y, binaryBiconeIsBilimit X Y⟩

/-- A finite family of polarizable rational Hodge structures of weight `n` has a direct sum,
which is again a polarizable rational Hodge structure of weight `n`. -/
noncomputable instance hasFiniteBiproducts :
    HasFiniteBiproducts (PolarizableHodgeStructureCat.{u} n) :=
  have : HasFiniteProducts (PolarizableHodgeStructureCat.{u} n) :=
    hasFiniteProducts_of_has_binary_and_terminal
  HasFiniteBiproducts.of_hasFiniteProducts

end PolarizableHodgeStructureCat

end TauCeti.Hodge

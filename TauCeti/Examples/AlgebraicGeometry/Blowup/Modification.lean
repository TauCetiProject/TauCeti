/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Basic
public import TauCeti.AlgebraicGeometry.Blowup.IsoLocus
public import TauCeti.AlgebraicGeometry.Blowup.Modification
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import Mathlib.RingTheory.MvPolynomial.Ideal
import TauCeti.RingTheory.KrullDimension.FiniteType
import TauCeti.RingTheory.MvPolynomial.Ideal.Basic

/-!
# Examples: the blowup of the affine plane at the origin is a modification

On `𝔸²_k = Spec k[x, y]` the ideal `(x, y)` of the origin has support a single closed point, which
is not the whole plane: the generic point `(0)` does not contain `x`. Since `𝔸²_k` is irreducible
and Noetherian, the blowup at the origin is a modification, and its centre lies in the origin.

The ideal `(x, y)` is not an effective Cartier divisor on any affine open neighbourhood `U` of the
origin: its stalk at the origin is the maximal ideal of the local ring `k[x, y]_(x, y)`, which has
dimension two since `(x, y)` is a maximal ideal of `k[x, y]`, while the stalks of an effective
Cartier divisor are principal. The same argument applies on every open neighbourhood, so the
blowup is an isomorphism over no neighbourhood of the origin, and its centre is exactly the origin
(`centre_blowupToBase_originIdealSheaf`).
-/

public section

open AlgebraicGeometry MvPolynomial TauCeti.AlgebraicGeometry

namespace TauCeti.BlowupModificationExample

variable (k : Type) [Field k]

/-- The ideal sheaf of the origin `(x, y)` of the affine plane `Spec k[x, y]`. -/
noncomputable def originIdealSheaf : (Spec (.of (MvPolynomial (Fin 2) k))).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    ((Ideal.span {X 0, X 1}).map (Scheme.ΓSpecIso (.of (MvPolynomial (Fin 2) k))).inv.hom)

/-- The ideal sheaf of the origin is associated to the ideal `(x, y)` of global sections. -/
theorem originIdealSheaf_def : originIdealSheaf k = Scheme.IdealSheafData.ofIdealTop
    ((Ideal.span {X 0, X 1}).map (Scheme.ΓSpecIso (.of (MvPolynomial (Fin 2) k))).inv.hom) :=
  (rfl)

/-- The support of the ideal sheaf of the origin is not the whole plane. -/
theorem support_originIdealSheaf_ne_top : (originIdealSheaf k).support ≠ ⊤ := by
  -- The generic point `(0)` would lie in the support, so `(0)` would contain `x`.
  intro h
  have hmem : (⊥ : PrimeSpectrum (MvPolynomial (Fin 2) k)) ∈ ((originIdealSheaf k).support :
      Set (Spec (.of (MvPolynomial (Fin 2) k)))) := h ▸ trivial
  simp only [originIdealSheaf, Scheme.IdealSheafData.coe_support_ofIdealTop,
    Spec_zeroLocus] at hmem
  simpa using (PrimeSpectrum.mem_zeroLocus _ _).1 hmem
    (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_insert (X 0) {X 1})))

-- The blowup of `𝔸²_k` at the origin is a modification.
example : IsModification (originIdealSheaf k).blowupToBase :=
  Scheme.IdealSheafData.isModification_blowupToBase_of_irreducibleSpace
    (support_originIdealSheaf_ne_top k)

-- Its centre lies in the origin.
example : (originIdealSheaf k).blowupToBase.centre ⊆ (originIdealSheaf k).support :=
  Scheme.IdealSheafData.centre_blowupToBase_subset

/-- The origin of the affine plane, the point of the prime `(x, y)`. -/
noncomputable def origin : Spec (.of (MvPolynomial (Fin 2) k)) :=
  ⟨Ideal.span {X 0, X 1}, idealOfVars_fin_two k ▸ isPrime_idealOfVars (Fin 2) k⟩

/-- The prime of the origin is `(x, y)`. -/
@[simp]
theorem origin_asIdeal : (origin k).asIdeal = Ideal.span {X 0, X 1} := (rfl)

/-- The prime `(x, y)` of the origin is maximal: it is the ideal of all variables. -/
theorem isMaximal_origin_asIdeal : (origin k).asIdeal.IsMaximal := by
  rw [origin_asIdeal, ← idealOfVars_fin_two]
  exact isMaximal_idealOfVars (Fin 2) k

/-- The support of the ideal sheaf of `(x, y)` is the origin. -/
theorem mem_support_originIdealSheaf_iff (x : Spec (.of (MvPolynomial (Fin 2) k))) :
    x ∈ (originIdealSheaf k).support ↔ x = origin k := by
  rw [← SetLike.mem_coe]
  simp only [originIdealSheaf, Scheme.IdealSheafData.coe_support_ofIdealTop, Spec_zeroLocus]
  refine (PrimeSpectrum.mem_zeroLocus x _).trans ?_
  rw [← Ideal.coe_comap, Ideal.comap_map_of_bijective (Scheme.ΓSpecIso _).inv.hom
    (CategoryTheory.ConcreteCategory.bijective_of_isIso _), SetLike.coe_subset_coe,
    ← origin_asIdeal]
  exact ⟨fun h ↦ PrimeSpectrum.ext
    ((isMaximal_origin_asIdeal k).eq_of_le x.isPrime.ne_top h).symm, fun h ↦ h ▸ le_rfl⟩

/-- The local ring of the plane at the origin has dimension two: the prime `(x, y)` is a maximal
ideal of `k[x, y]`, so its height is the number of variables. -/
theorem ringKrullDim_stalk_origin :
    ringKrullDim ((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.stalk (origin k)) = 2 := by
  have := isMaximal_origin_asIdeal k
  rw [ringKrullDim_eq_of_ringEquiv (Spec.stalkIso _ (origin k)).commRingCatIsoToRingEquiv,
    IsLocalization.AtPrime.ringKrullDim_eq_height (origin k).asIdeal,
    MvPolynomial.height_eq_natCard_of_isMaximal, Nat.card_fin]
  norm_cast

/-- The stalk of the ideal sheaf of the origin at the origin is the maximal ideal of the local
ring there. -/
theorem stalkIdeal_originIdealSheaf_origin :
    (originIdealSheaf k).stalkIdeal (origin k) = IsLocalRing.maximalIdeal _ := by
  have := (origin k).isPrime
  rw [originIdealSheaf,
    Scheme.IdealSheafData.stalkIdeal_ofIdealTop_map_ΓSpecIso_inv (R := .of _) _ (origin k),
    ← origin_asIdeal, Localization.AtPrime.map_eq_maximalIdeal]
  exact IsLocalRing.map_ringEquiv_maximalIdeal
    (Spec.stalkIso _ (origin k)).symm.commRingCatIsoToRingEquiv

/-- **The origin is not a Cartier divisor near the origin.** If a morphism `f` to `𝔸²_k` is flat
at a point `p` over the origin, then the ideal `(x, y)` does not pull back along `f` to an
effective Cartier divisor. -/
theorem not_isEffectiveCartier_comap {Y : Scheme} (f : Y ⟶ Spec (.of (MvPolynomial (Fin 2) k)))
    {p : Y} (hp : f p = origin k) (hf : (f.stalkMap p).hom.Flat) :
    ¬ ((originIdealSheaf k).comap f).IsEffectiveCartier := by
  intro h
  have hdim := Scheme.IdealSheafData.ringKrullDim_stalk_le_one_of_comap f h p hf
    (hp ▸ stalkIdeal_originIdealSheaf_origin k)
  rw [hp] at hdim
  exact absurd ((ringKrullDim_stalk_origin k).ge.trans hdim) (by decide)

/-- On no affine open neighbourhood `U` of the origin of `𝔸²_k` does the ideal `(x, y)` pull back
to an effective Cartier divisor on `Spec Γ(𝔸²_k, U)`. -/
theorem not_isEffectiveCartier_comap_fromSpec {U : (Spec (.of (MvPolynomial (Fin 2) k))).Opens}
    (hU : IsAffineOpen U) (hoU : origin k ∈ U) :
    ¬ ((originIdealSheaf k).comap hU.fromSpec).IsEffectiveCartier := by
  obtain ⟨y, hy⟩ : origin k ∈ Set.range hU.fromSpec := hU.range_fromSpec ▸ hoU
  exact not_isEffectiveCartier_comap k _ hy (Flat.stalkMap _ y)

/-- On no open neighbourhood `U` of the origin of `𝔸²_k` does the ideal `(x, y)` restrict to an
effective Cartier divisor. -/
theorem not_isEffectiveCartier_comap_ι {U : (Spec (.of (MvPolynomial (Fin 2) k))).Opens}
    (hoU : origin k ∈ U) : ¬ ((originIdealSheaf k).comap U.ι).IsEffectiveCartier :=
  not_isEffectiveCartier_comap k U.ι (p := ⟨origin k, hoU⟩) rfl (Flat.stalkMap _ _)

/-- **The centre of the blowup of the plane at the origin is the origin.** The blowup
`Bl_0 𝔸²_k ⟶ 𝔸²_k` is an isomorphism exactly over the complement of the origin. -/
theorem centre_blowupToBase_originIdealSheaf :
    (originIdealSheaf k).blowupToBase.centre = {origin k} := by
  ext x
  refine ⟨fun hx ↦ (mem_support_originIdealSheaf_iff k x).1
    (Scheme.IdealSheafData.centre_blowupToBase_subset hx), ?_⟩
  rintro rfl
  rw [Scheme.Hom.centre_def, Set.mem_compl_iff, SetLike.mem_coe,
    Scheme.IdealSheafData.mem_isoLocus_blowupToBase_iff]
  rintro ⟨U, hoU, hU⟩
  exact not_isEffectiveCartier_comap_ι k hoU hU

end TauCeti.BlowupModificationExample

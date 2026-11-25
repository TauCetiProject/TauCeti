/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Basic
public import TauCeti.AlgebraicGeometry.Blowup.Modification
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import TauCeti.RingTheory.Ideal.Height

/-!
# Examples: the blowup of the affine plane at the origin is a modification

On `𝔸²_k = Spec k[x, y]` the ideal `(x, y)` of the origin has support a single closed point, which
is not the whole plane: the generic point `(0)` does not contain `x`. Since `𝔸²_k` is irreducible
and Noetherian, the blowup at the origin is a modification, and its centre lies in the origin.

The ideal `(x, y)` is not an effective Cartier divisor on any affine open neighbourhood `U` of the
origin: its stalk at the origin is the maximal ideal of the local ring `k[x, y]_(x, y)`, which has
dimension two since `(x, y)` contains the two coprime elements `x` and `y`, while the stalks of an
effective Cartier divisor are principal.
-/

public section

open AlgebraicGeometry MvPolynomial TauCeti.AlgebraicGeometry

namespace TauCeti.BlowupModificationExample

variable (k : Type) [Field k]

/-- The ideal sheaf of the origin `(x, y)` of the affine plane `Spec k[x, y]`. -/
noncomputable def originIdealSheaf : (Spec (.of (MvPolynomial (Fin 2) k))).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    ((Ideal.span {X 0, X 1}).map (Scheme.ΓSpecIso (.of (MvPolynomial (Fin 2) k))).inv.hom)

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

private theorem X_image_univ : (X '' Set.univ : Set (MvPolynomial (Fin 2) k)) = {X 0, X 1} := by
  ext p
  simp [Fin.exists_fin_two, eq_comm]

/-- The origin of the affine plane, the point of the prime `(x, y)`. -/
noncomputable def origin : Spec (.of (MvPolynomial (Fin 2) k)) :=
  ⟨Ideal.span {X 0, X 1}, X_image_univ k ▸ span_X_image_isPrime Set.univ⟩

/-- The prime of the origin is `(x, y)`. -/
@[simp]
theorem origin_asIdeal : (origin k).asIdeal = Ideal.span {X 0, X 1} := (rfl)

/-- The prime `(x, y)` of the origin is maximal: it is the kernel of the constant coefficient map
`k[x, y] → k`. -/
theorem isMaximal_origin_asIdeal : (origin k).asIdeal.IsMaximal := by
  have h : (origin k).asIdeal = RingHom.ker (constantCoeff (σ := Fin 2) (R := k)) := by
    ext p
    rw [origin_asIdeal, ← X_image_univ k, mem_ideal_span_X_image, RingHom.mem_ker,
      constantCoeff_eq, ← notMem_support_iff]
    refine ⟨fun h h0 ↦ ?_, fun h m hm ↦ ?_⟩
    · obtain ⟨i, -, hi⟩ := h 0 h0
      exact hi rfl
    · simpa using DFunLike.ne_iff.mp (ne_of_mem_of_not_mem hm h)
  exact h ▸ RingHom.ker_isMaximal_of_surjective _ fun a ↦ ⟨C a, constantCoeff_C _ a⟩

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

/-- The local ring of the plane at the origin has dimension at least two: the prime `(x, y)`
contains the coprime elements `x` and `y` of the factorial ring `k[x, y]`. -/
theorem two_le_ringKrullDim_stalk_origin :
    2 ≤ ringKrullDim ((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.stalk (origin k)) := by
  have := (origin k).isPrime
  rw [ringKrullDim_eq_of_ringEquiv (Spec.stalkIso _ (origin k)).commRingCatIsoToRingEquiv,
    IsLocalization.AtPrime.ringKrullDim_eq_height (origin k).asIdeal]
  have hxy : IsRelPrime (X 0 : MvPolynomial (Fin 2) k) (X 1) :=
    (MvPolynomial.prime_X (i := (0 : Fin 2))).irreducible.isRelPrime_iff_not_dvd.mpr
      (by simp [MvPolynomial.X_dvd_X])
  have h := Ideal.two_le_height_of_isRelPrime hxy (p := (origin k).asIdeal)
    (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
  exact (WithBot.coe_le_coe.mpr h : ((2 : ℕ∞) : WithBot ℕ∞) ≤ _)

/-- The stalk of the ideal sheaf of the origin at the origin is the maximal ideal of the local
ring there. -/
theorem stalkIdeal_originIdealSheaf_origin :
    (originIdealSheaf k).stalkIdeal (origin k) = IsLocalRing.maximalIdeal _ := by
  have := (origin k).isPrime
  rw [Scheme.IdealSheafData.stalkIdeal_eq_map _
    (⟨⊤, isAffineOpen_top _⟩ : (Spec (.of (MvPolynomial (Fin 2) k))).affineOpens) _ trivial]
  simp only [originIdealSheaf, Scheme.IdealSheafData.ofIdealTop_ideal,
    CategoryTheory.homOfLE_refl, CategoryTheory.op_id, CategoryTheory.Functor.map_id,
    CommRingCat.hom_id, RingHom.id_comp, Ideal.map_map]
  -- The germ map of `Γ(𝔸²_k, ⊤)` factors through the localization `k[x, y]_(x, y)`.
  rw [← CommRingCat.hom_comp, ← Spec.algebraMap_stalkIso_inv (origin k), CommRingCat.hom_comp,
    ← Ideal.map_map, CommRingCat.hom_ofHom, ← origin_asIdeal,
    Localization.AtPrime.map_eq_maximalIdeal]
  exact IsLocalRing.map_ringEquiv_maximalIdeal
    (Spec.stalkIso _ (origin k)).symm.commRingCatIsoToRingEquiv

/-- **The origin is not a Cartier divisor near the origin.** On no affine open neighbourhood `U` of
the origin of `𝔸²_k` does the ideal `(x, y)` pull back to an effective Cartier divisor on
`Spec Γ(𝔸²_k, U)`. -/
theorem not_isEffectiveCartier_comap_fromSpec {U : (Spec (.of (MvPolynomial (Fin 2) k))).Opens}
    (hU : IsAffineOpen U) (hoU : origin k ∈ U) :
    ¬ ((originIdealSheaf k).comap hU.fromSpec).IsEffectiveCartier := by
  intro h
  obtain ⟨y, hy⟩ : origin k ∈ Set.range hU.fromSpec := hU.range_fromSpec ▸ hoU
  have hdim := Scheme.IdealSheafData.ringKrullDim_stalk_le_one_of_comap hU.fromSpec h y
    (hy ▸ stalkIdeal_originIdealSheaf_origin k)
  rw [hy] at hdim
  exact absurd ((two_le_ringKrullDim_stalk_origin k).trans hdim) (by decide)

end TauCeti.BlowupModificationExample

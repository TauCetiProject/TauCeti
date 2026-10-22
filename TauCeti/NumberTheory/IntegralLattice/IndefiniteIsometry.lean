/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Isometry.OrthogonalExtension
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Transvection
public import TauCeti.LinearAlgebra.IntegralLattice.Restriction
public import TauCeti.NumberTheory.IntegralLattice.Binary.NormOne
import TauCeti.Algebra.Module.Torsion.Int

/-!
# Isometry groups of indefinite lattices are infinite

A nondegenerate indefinite integral lattice `L` of rank at least three has infinitely many
isometries, in contrast with the finiteness of `O(L)` for definite lattices. The proof splits
according to whether the rational norm form of `L` is isotropic. The isotropic case, in which the
Eichler transvections already form an infinite group, is
`TauCeti.IntegralLattice.infinite_isometry_of_not_anisotropic`. This file treats the anisotropic
case and assembles the two.

Suppose the rational norm form is anisotropic and indefinite; no rank or nondegeneracy hypothesis
is needed. Choose lattice vectors `x` and `y` of positive and negative norm. They span a binary
sublattice `M` whose rational norm form is indefinite and anisotropic, so its primitive
discriminant is positive and not a square, and `O(M)` is infinite by Pell's equation. Its rational
form is nondegenerate, so every isometry of `M` extends to a rational isometry of `L` acting as the
identity on the orthogonal complement of `ℚ x + ℚ y`
(`LinearMap.BilinForm.Isometry.isometryGroupExtend`). Such an extension need not preserve `L`, but
a nonzero integer `d` carries the orthogonal projection of `L` into `M`, and then every isometry of
`M` acting trivially on `M / d M` extends to an isometry of `L`. These isometries form a subgroup
of finite index in the infinite group `O(M)`, and distinct ones have distinct extensions.

In rank two an indefinite lattice with isotropic norm form, such as the hyperbolic plane, can have
a finite isometry group, so the rank hypothesis of the combined statement cannot be dropped.

## Main results

* `TauCeti.IntegralLattice.infinite_isometry_of_isIndefinite_of_anisotropic`: an indefinite lattice
  with anisotropic rational norm form has infinite `O(L)`, and
  `TauCeti.IntegralLattice.infinite_specialOrthogonalGroup_of_isIndefinite_of_anisotropic`
  infinite `SO(L)`.
* `TauCeti.IntegralLattice.infinite_isometry_of_isIndefinite` and
  `TauCeti.IntegralLattice.infinite_specialOrthogonalGroup_of_isIndefinite`: a nondegenerate
  indefinite lattice of rank at least three has infinite `O(L)` and `SO(L)`.

## References

* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 13.
* M. Eichler, *Quadratische Formen und orthogonale Gruppen*, Springer (1952).
-/

public section

open Module LinearMap.BilinForm TauCeti.BilinForm
open scoped Pointwise TensorProduct

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-! ## Isometries acting trivially modulo `d` -/

/-- The action of a self-isometry of `M` on the finite quotient `M / d M` of its carrier. -/
private noncomputable def reductionHom (M : IntegralLattice W) (d : ℤ) :
    Isometry M M →* Module.End ℤ (QuotSMulTop d M) where
  toFun g := QuotSMulTop.map d (g.carrierEquiv : M →ₗ[ℤ] M)
  map_one' := by
    rw [Isometry.one_def, Isometry.carrierEquiv_refl]
    exact QuotSMulTop.map_id d M
  map_mul' g h := by
    rw [Isometry.mul_def, Isometry.carrierEquiv_trans, LinearEquiv.coe_trans,
      QuotSMulTop.map_comp, Module.End.mul_eq_comp]

/-- For `d ≠ 0`, the isometries acting trivially on `M / d M` have finite index in `O(M)`. -/
private theorem finiteIndex_ker_reductionHom (M : IntegralLattice W) (d : ℕ) [NeZero d] :
    (reductionHom M d).ker.FiniteIndex := by
  have : Finite (Module.End ℤ (QuotSMulTop (d : ℤ) M)) :=
    Finite.of_injective _ DFunLike.coe_injective
  rw [← MonoidHom.ker_toHomUnits]
  infer_instance

/-- An isometry acting trivially on `M / d M` moves every lattice vector by a `d`-multiple of a
lattice vector. -/
private theorem exists_eq_smul_of_mem_ker_reductionHom {M : IntegralLattice W} {d : ℤ}
    {g : Isometry M M} (hg : g ∈ (reductionHom M d).ker) (x : M) :
    ∃ y : M, g.carrierEquiv x - x = d • y := by
  have h := LinearMap.congr_fun (MonoidHom.mem_ker.mp hg) (Submodule.Quotient.mk x)
  rw [Module.End.one_apply, reductionHom, MonoidHom.coe_mk, OneHom.coe_mk,
    QuotSMulTop.map_apply_mk, Submodule.Quotient.eq, Submodule.mem_smul_pointwise_iff_exists] at h
  obtain ⟨y, -, hy⟩ := h
  exact ⟨y, hy.symm⟩

/-! ## A binary sublattice of an indefinite lattice -/

/-- An indefinite lattice has lattice vectors of positive and of negative norm. -/
private theorem exists_carrier_pos_and_neg {L : IntegralLattice V} (hL : L.IsIndefinite) :
    ∃ x y : L, 0 < L.form x x ∧ L.form y y < 0 := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := L.isIndefinite_iff_exists_pos_and_exists_neg.mp hL
  obtain ⟨s, hs, hsp⟩ := Submodule.IsLattice.exists_ne_zero_smul_mem ℚ L.carrier p
  obtain ⟨t, ht, htq⟩ := Submodule.IsLattice.exists_ne_zero_smul_mem ℚ L.carrier q
  have hscale (r : ℤ) (z : V) : L.form (r • z) (r • z) = (r : ℚ) ^ 2 * L.form z z := by
    simp only [← Int.cast_smul_eq_zsmul ℚ, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  refine ⟨⟨s • p, hsp⟩, ⟨t • q, htq⟩, ?_, ?_⟩
  · rw [hscale]
    exact mul_pos (by positivity) hp
  · rw [hscale]
    exact mul_neg_of_pos_of_neg (by positivity) hq

/-- The restriction of a lattice with anisotropic rational norm form is anisotropic. -/
private theorem anisotropic_restrict {L : IntegralLattice V} (h : L.norm.Anisotropic)
    (S : Submodule ℤ L) : (L.restrict S).norm.Anisotropic := fun z hz ↦
  L.restrictMap_injective S <| by
    rw [map_zero]
    exact h _ (by rw [norm_apply, form_restrictMap, ← norm_apply, hz])

/-- A lattice with anisotropic rational norm form has nondegenerate rational form. -/
private theorem form_nondegenerate_of_anisotropic {L : IntegralLattice V}
    (h : L.norm.Anisotropic) : L.form.Nondegenerate :=
  (LinearMap.IsRefl.nondegenerate_iff_separatingLeft L.isSymm.isRefl).mpr
    (separatingLeft_of_anisotropic (by rwa [← norm_def]))

/-- Two lattice vectors of opposite signs span an indefinite binary sublattice. -/
private theorem restrict_span_pair {L : IntegralLattice V} {x y : L} (hx : 0 < L.form x x)
    (hy : L.form y y < 0) :
    (L.restrict (Submodule.span ℤ (Set.range ![x, y]))).IsIndefinite ∧
      finrank ℚ (ℚ ⊗[ℤ] Submodule.span ℤ (Set.range ![x, y])) = 2 := by
  set S := Submodule.span ℤ (Set.range ![x, y])
  have hmem (z : L) (hz : z ∈ Set.range ![x, y]) :
      L.restrictMap S (1 ⊗ₜ ⟨z, Submodule.subset_span hz⟩) = z := by
    rw [restrictMap_tmul, one_smul]
  have hind : (L.restrict S).IsIndefinite := by
    refine (L.restrict S).isIndefinite_iff_exists_pos_and_exists_neg.mpr
      ⟨⟨1 ⊗ₜ ⟨x, Submodule.subset_span ⟨0, rfl⟩⟩, ?_⟩,
        ⟨1 ⊗ₜ ⟨y, Submodule.subset_span ⟨1, rfl⟩⟩, ?_⟩⟩
    · rwa [← form_restrictMap, hmem x ⟨0, rfl⟩]
    · rwa [← form_restrictMap, hmem y ⟨1, rfl⟩]
  refine ⟨hind, le_antisymm ?_ ?_⟩
  · rw [← (L.restrict S).finrank_carrier, ← (L.restrictCarrierEquiv S).finrank_eq]
    exact (finrank_range_le_card (R := ℤ) ![x, y]).trans (by simp)
  · have := (L.restrict S).signature_sum_eq_finrank
    obtain ⟨h₁, h₂⟩ := (L.restrict S).isIndefinite_iff_not_semidef.mp hind
    rw [isPosSemidef_iff_sigNeg_eq_zero] at h₁
    rw [isNegSemidef_iff_sigPos_eq_zero] at h₂
    omega

/-! ## Extending isometries of the binary sublattice -/

/-- A self-isometry of a lattice, as an isometry of its rational form. -/
private noncomputable def toIsometryGroup (M : IntegralLattice W) :
    Isometry M M →* isometryGroup M.form where
  toFun g := (isometryGroupEquivIsometryEquiv M.form).symm g.toIsometryEquiv
  map_one' := Subtype.ext (LinearEquiv.ext fun x ↦ by simp)
  map_mul' g h := Subtype.ext (LinearEquiv.ext fun x ↦ by simp)

private theorem toIsometryGroup_apply (M : IntegralLattice W) (g : Isometry M M) (x : W) :
    (toIsometryGroup M g : W ≃ₗ[ℚ] W) x = g x := by
  simp [toIsometryGroup]

/-- A rational isometry of `L` which, together with its inverse, maps the carrier into itself is an
isometry of `L`. -/
private noncomputable def ofIsometryGroup {L : IntegralLattice V} (G : isometryGroup L.form)
    (h : ∀ x ∈ L.carrier, (G : V ≃ₗ[ℚ] V) x ∈ L.carrier)
    (h' : ∀ x ∈ L.carrier, (G : V ≃ₗ[ℚ] V).symm x ∈ L.carrier) : Isometry L L where
  toIsometryEquiv := isometryGroupEquivIsometryEquiv L.form G
  map_carrier := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      simpa using h x hx
    · intro x hx
      exact ⟨_, h' x hx, by simp⟩

private theorem ofIsometryGroup_apply {L : IntegralLattice V} (G : isometryGroup L.form) (h h')
    (x : V) : ofIsometryGroup G h h' x = (G : V ≃ₗ[ℚ] V) x := by
  simp [ofIsometryGroup, ← Isometry.coe_toIsometryEquiv]

/-- The inclusion of the ambient space of a restricted lattice, as an isometric embedding. -/
private def restrictIsometry (L : IntegralLattice V) (S : Submodule ℤ L) :
    (L.restrict S).form →bᵢ L.form :=
  ⟨L.restrictMap S, fun a b ↦ L.form_restrictMap S a b⟩

private theorem restrictIsometry_apply (L : IntegralLattice V) (S : Submodule ℤ L)
    (z : ℚ ⊗[ℤ] S) : L.restrictIsometry S z = L.restrictMap S z := by
  simp [restrictIsometry, ← LinearMap.BilinForm.Isometry.coe_toLinearMap]

/-- **The extension preserves the lattice.** Let `M` be the restriction of `L` to a submodule `S`
with nondegenerate rational form, and let `d ≠ 0` carry the orthogonal projection of `L` into the
carrier of `M`. Then the extension of an isometry of `M` acting trivially on `M / d M` maps `L`
into itself. -/
private theorem isometryGroupExtend_mem_carrier {L : IntegralLattice V} {S : Submodule ℤ L}
    (hS : (L.restrict S).form.Nondegenerate) {d : ℤ} (hd : d ≠ 0)
    (hdπ : ∀ x ∈ L.carrier,
      d • (L.restrictIsometry S).orthogonalProjection hS x ∈ (L.restrict S).carrier)
    {g : Isometry (L.restrict S) (L.restrict S)} (hg : g ∈ (reductionHom (L.restrict S) d).ker)
    {x : V} (hx : x ∈ L.carrier) :
    ((L.restrictIsometry S).isometryGroupExtend L.isSymm hS (toIsometryGroup _ g) :
      V ≃ₗ[ℚ] V) x ∈ L.carrier := by
  set p := (L.restrictIsometry S).orthogonalProjection hS x
  rw [LinearMap.BilinForm.Isometry.isometryGroupExtend_apply, toIsometryGroup_apply]
  obtain ⟨y, hy⟩ := exists_eq_smul_of_mem_ker_reductionHom hg ⟨d • p, hdπ x hx⟩
  -- Dividing the congruence by `d`, the displacement `g p - p` is the lattice vector `y`.
  have hgp : g p - p = (y : ℚ ⊗[ℤ] S) := by
    have hy' := congrArg (fun z : (L.restrict S) ↦ (z : ℚ ⊗[ℤ] S)) hy
    simp only [Submodule.coe_sub, Isometry.coe_carrierEquiv_apply, Submodule.coe_smul_of_tower,
      ← Int.cast_smul_eq_zsmul ℚ, map_smul, ← smul_sub] at hy'
    exact smul_right_injective _ (Int.cast_ne_zero.mpr hd) hy'
  have hy'' := Submodule.mem_map_of_mem (f := (L.restrictMap S).restrictScalars ℤ) y.2
  rw [map_restrictMap_restrict_carrier] at hy''
  obtain ⟨z, -, hz⟩ := hy''
  rw [restrictIsometry_apply, hgp]
  exact L.carrier.add_mem hx (hz ▸ z.2)

/-! ## The anisotropic case -/

/-- **The anisotropic case of the infiniteness of `O(L)`.** An indefinite integral lattice whose
rational norm form is anisotropic has infinitely many isometries. No rank or nondegeneracy
hypothesis is needed: anisotropy forces nondegeneracy, and in rank two this is the Pell case. -/
theorem infinite_isometry_of_isIndefinite_of_anisotropic {L : IntegralLattice V}
    (hL : L.IsIndefinite) (haniso : L.norm.Anisotropic) : Infinite (Isometry L L) := by
  obtain ⟨x, y, hx, hy⟩ := exists_carrier_pos_and_neg hL
  set S := Submodule.span ℤ (Set.range ![x, y])
  set M := L.restrict S
  obtain ⟨hMind, hV⟩ := restrict_span_pair hx hy
  have hManiso := anisotropic_restrict haniso S
  have hS := form_nondegenerate_of_anisotropic hManiso
  have : Infinite (Isometry M M) := infinite_isometry_of_binaryDiscriminant_pos_of_not_isSquare hV
    (M.binaryDiscriminant_pos_of_isIndefinite hV hMind)
    (M.not_isSquare_binaryDiscriminant_of_anisotropic hV hManiso)
  set ι := L.restrictIsometry S
  -- A single positive integer `d` carries the orthogonal projection of `L` into `M`.
  obtain ⟨r, hr, hrπ⟩ := Submodule.IsLattice.exists_ne_zero_forall_smul_mem ℚ M.carrier
    ((Module.Finite.fg_top (M := L)).map ((ι.orthogonalProjection hS).restrictScalars ℤ ∘ₗ
      L.carrier.subtype))
  set d := r.natAbs
  have : NeZero d := ⟨Int.natAbs_ne_zero.mpr hr⟩
  have hd : (d : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne d)
  have hdπ' (z : V) (hz : z ∈ L.carrier) :
      (d : ℤ) • ι.orthogonalProjection hS z ∈ M.carrier := by
    have h := hrπ _ ⟨⟨z, hz⟩, Submodule.mem_top, rfl⟩
    rcases Int.natAbs_eq r with hr' | hr'
    · rwa [← hr']
    · rw [hr', neg_smul, neg_mem_iff] at h
      exact h
  -- The isometries of `M` acting trivially on `M / d M` form an infinite group.
  let Γ := (reductionHom M d).ker
  have := finiteIndex_ker_reductionHom M d
  have : Infinite Γ := by
    by_contra h
    have := (Subgroup.finite_iff_finite_and_finiteIndex Γ).mpr ⟨not_infinite_iff_finite.mp h, this⟩
    exact not_finite (Isometry M M)
  let F : Γ → Isometry L L := fun g ↦ ofIsometryGroup
    (ι.isometryGroupExtend L.isSymm hS (toIsometryGroup M g))
    (fun z hz ↦ isometryGroupExtend_mem_carrier hS hd hdπ' g.2 hz)
    (fun z hz ↦ by
      rw [← LinearEquiv.coe_inv, ← Subgroup.coe_inv, ← map_inv, ← map_inv]
      exact isometryGroupExtend_mem_carrier hS hd hdπ' (inv_mem g.2) hz)
  refine Infinite.of_injective F fun g h hgh ↦ Subtype.ext (Isometry.ext fun z ↦ ?_)
  have h₁ := ι.isometryGroupExtend_injective L.isSymm hS (Subtype.ext (LinearEquiv.ext fun w ↦ by
    simpa only [F, ofIsometryGroup_apply] using congrArg (fun e : Isometry L L ↦ e w) hgh))
  simpa only [toIsometryGroup_apply] using LinearEquiv.congr_fun (congrArg Subtype.val h₁) z

/-- **The anisotropic case of the infiniteness of `SO(L)`.** An indefinite integral lattice whose
rational norm form is anisotropic has infinitely many proper isometries. -/
theorem infinite_specialOrthogonalGroup_of_isIndefinite_of_anisotropic {L : IntegralLattice V}
    (hL : L.IsIndefinite) (haniso : L.norm.Anisotropic) : Infinite (specialOrthogonalGroup L) := by
  have := infinite_isometry_of_isIndefinite_of_anisotropic hL haniso
  by_contra h
  have := (Subgroup.finite_iff_finite_and_finiteIndex (specialOrthogonalGroup L)).mpr
    ⟨not_infinite_iff_finite.mp h, inferInstance⟩
  exact not_finite (Isometry L L)

/-! ## Indefinite lattices of rank at least three -/

/-- **Indefinite lattices have infinite isometry groups.** A nondegenerate indefinite integral
lattice of rank at least three has infinitely many isometries. -/
theorem infinite_isometry_of_isIndefinite {L : IntegralLattice V} [L.IsNondegenerate]
    (hrank : 3 ≤ finrank ℤ L) (hL : L.IsIndefinite) : Infinite (Isometry L L) := by
  by_cases haniso : L.norm.Anisotropic
  · exact infinite_isometry_of_isIndefinite_of_anisotropic hL haniso
  · exact infinite_isometry_of_not_anisotropic hrank haniso

/-- **Indefinite lattices have infinite special isometry groups.** A nondegenerate indefinite
integral lattice of rank at least three has infinitely many proper isometries. -/
theorem infinite_specialOrthogonalGroup_of_isIndefinite {L : IntegralLattice V}
    [L.IsNondegenerate] (hrank : 3 ≤ finrank ℤ L) (hL : L.IsIndefinite) :
    Infinite (specialOrthogonalGroup L) := by
  by_cases haniso : L.norm.Anisotropic
  · exact infinite_specialOrthogonalGroup_of_isIndefinite_of_anisotropic hL haniso
  · exact infinite_specialOrthogonalGroup_of_not_anisotropic hrank haniso

end TauCeti.IntegralLattice

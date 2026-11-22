/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import TauCeti.Algebra.Homology.DieudonneComplex.Verschiebung.Quotient
public import TauCeti.Algebra.Homology.HomologicalComplex.QuotSMulTop

/-!
# The finite Verschiebung quotients compute cohomology modulo `pʳ`

Let `M` be a saturated Dieudonné complex and `r : ℕ`. The finite Verschiebung quotient
`W_r(M)ⁿ = Mⁿ / (im Vʳ + im d Vʳ)` is related to the reduction `M / pʳ M` in two ways
(Bhatt–Lurie–Mathew, §2.7).

* Sending `x` to the class of the cocycle `Fʳ x` of `M / pʳ M` induces an isomorphism of abelian
  groups `θ_r : W_r(M)ⁿ ≅ Hⁿ(M / pʳ M)` in every degree, natural in morphisms of saturated
  Dieudonné complexes. Indeed `d (Fʳ x) = pʳ Fʳ (d x)`, every element whose differential is
  divisible by `pʳ` is in the image of `Fʳ`, and `Fʳ` carries `Vʳ a + d Vʳ b` to `pʳ a + d b`.
* The projection `M / pʳ M ⟶ W_r(M)`, which exists because `pʳ x = Vʳ (Fʳ x)`, is a
  quasi-isomorphism of cochain complexes.

So the cohomology of the reductions of `M` modulo powers of `p` lives in the terms of the finite
quotients `W_r(M)`. In particular a morphism `f` of saturated Dieudonné complexes induces an
isomorphism `W_r(f)` exactly when it induces a quasi-isomorphism `M / pʳ M ⟶ N / pʳ N`, and this
holds for every `r` as soon as it holds for `r = 1`.

## Main definitions

* `TauCeti.DieudonneComplex.frobeniusIterateCycles`: the map `x ↦ Fʳ x` from `Mⁿ` to the
  cocycles of `M / pʳ M`.
* `TauCeti.DieudonneComplex.IsSaturated.verschiebungQuotientIsoHomology`: the isomorphism
  `θ_r : W_r(M)ⁿ ≅ Hⁿ(M / pʳ M)`.
* `TauCeti.DieudonneComplex.IsSaturated.quotSMulTopToVerschiebungQuotient`: the projection
  `M / pʳ M ⟶ W_r(M)`.

## Main results

* `IsSaturated.toVerschiebungQuotient_f_comp_verschiebungQuotientIsoHomology_hom`: `θ_r` sends
  the class of `x` to the cohomology class of `Fʳ x`.
* `IsSaturated.verschiebungQuotientMap_f_comp_verschiebungQuotientIsoHomology_hom`: `θ_r` is
  natural.
* `IsSaturated.quasiIso_quotSMulTopToVerschiebungQuotient`: the projection `M / pʳ M ⟶ W_r(M)` is
  a quasi-isomorphism.
* `IsSaturated.isIso_verschiebungQuotientMap_iff_quasiIso`: `W_r(f)` is an isomorphism iff
  `M / pʳ M ⟶ N / pʳ N` is a quasi-isomorphism.
* `IsSaturated.forall_isIso_verschiebungQuotientMap_iff`: `W_r(f)` is an isomorphism for every `r`
  iff `W_1(f)` is.

## References

* B. Bhatt, J. Lurie, A. Mathew, *Revisiting the de Rham–Witt complex*, Astérisque 424 (2021),
  arXiv:1805.05501, Proposition 2.7.1, Corollaries 2.7.2 and 2.7.4 and Remark 2.7.3.
-/

public section

open CategoryTheory HomologicalComplex

universe u

namespace TauCeti

namespace DieudonneComplex

variable {p : ℕ} (M : DieudonneComplex.{u} p)

/-- `Fʳ` as an endomorphism of `Mⁿ`. -/
private noncomputable def frobeniusIterate (r : ℕ) (n : ℤ) : M.X n ⟶ M.X n :=
  AddCommGrpCat.ofHom (AddMonoidHom.mk' (⇑(M.F n).hom)^[r] (iterate_map_add _ r))

/-- The class of `Fʳ x` in `M / pʳ M` is a cocycle, since `d (Fʳ x) = pʳ Fʳ (d x)`. -/
private lemma frobeniusIterate_comp_toQuotSMulTop_comp_d (r : ℕ) (n : ℤ) :
    (M.frobeniusIterate r n ≫ (M.toQuotSMulTop (p ^ r)).f n) ≫
      (M.quotSMulTop (p ^ r)).d n (n + 1) = 0 := by
  ext x
  simp only [frobeniusIterate, AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom,
    AddMonoidHom.comp_apply, AddMonoidHom.mk'_apply, quotSMulTop_d_toQuotSMulTop_f_apply,
    M.d_F_iterate_apply, map_nsmul, smul_toQuotSMulTop_f_apply, AddCommGrpCat.hom_zero,
    AddMonoidHom.zero_apply]

/-- The map `x ↦ Fʳ x` from `Mⁿ` to the cocycles of `M / pʳ M`. -/
noncomputable def frobeniusIterateCycles (r : ℕ) (n : ℤ) :
    M.X n ⟶ (M.quotSMulTop (p ^ r)).cycles n :=
  (M.quotSMulTop (p ^ r)).liftCycles (M.frobeniusIterate r n ≫ (M.toQuotSMulTop _).f n)
    (n + 1) (by simp) (M.frobeniusIterate_comp_toQuotSMulTop_comp_d r n)

/-- The cocycle `frobeniusIterateCycles r n x` of `M / pʳ M` is the class of `Fʳ x`. -/
@[simp]
lemma iCycles_frobeniusIterateCycles_apply (r : ℕ) {n : ℤ} (x : M.X n) :
    ((M.quotSMulTop (p ^ r)).iCycles n).hom ((M.frobeniusIterateCycles r n).hom x) =
      ((M.toQuotSMulTop (p ^ r)).f n).hom ((⇑(M.F n).hom)^[r] x) := by
  rw [← AddCommGrpCat.comp_apply, frobeniusIterateCycles, liftCycles_i]
  rfl

variable {M}

/-- `frobeniusIterateCycles` is natural in morphisms of Dieudonné complexes. -/
@[reassoc]
lemma frobeniusIterateCycles_naturality {N : DieudonneComplex.{u} p} (f : M ⟶ N) (r : ℕ)
    (n : ℤ) :
    M.frobeniusIterateCycles r n ≫ cyclesMap (quotSMulTopMap _ f.hom) n =
      f.hom.f n ≫ N.frobeniusIterateCycles r n := by
  have hF : Function.Semiconj (f.hom.f n).hom (M.F n).hom (N.F n).hom :=
    fun x ↦ Hom.comm_F_apply f n x
  ext x
  refine (AddCommGrpCat.mono_iff_injective (iCycles _ n)).1 inferInstance ?_
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
  rw [← AddCommGrpCat.comp_apply _ (iCycles _ n), cyclesMap_i, AddCommGrpCat.comp_apply,
    iCycles_frobeniusIterateCycles_apply, quotSMulTopMap_f_apply,
    iCycles_frobeniusIterateCycles_apply, hF.iterate_right]

namespace IsSaturated

variable (hM : M.IsSaturated)
include hM

/-- The class of `Fʳ x` in `Hⁿ(M / pʳ M)` only depends on the class of `x` in `W_r(M)ⁿ`: `Fʳ`
carries `Vʳ a + d (Vʳ b)` to `pʳ a + d b`. -/
private lemma verschiebungFiltration_le_ker (r : ℕ) (n : ℤ) :
    hM.verschiebungFiltration r n ≤
      (M.frobeniusIterateCycles r n ≫ (M.quotSMulTop (p ^ r)).homologyπ n).hom.ker := by
  intro x hx
  obtain ⟨a, b, rfl⟩ := (hM.mem_verschiebungFiltration_iff (sub_add_cancel n 1)).1 hx
  have : M.frobeniusIterateCycles r n ((⇑(hM.V n).hom)^[r] a +
      (M.d (n - 1) n).hom ((⇑(hM.V (n - 1)).hom)^[r] b)) =
      ((M.quotSMulTop (p ^ r)).toCycles (n - 1) n).hom
        (((M.toQuotSMulTop (p ^ r)).f (n - 1)).hom b) := by
    refine (AddCommGrpCat.mono_iff_injective (iCycles _ n)).1 inferInstance ?_
    rw [iCycles_frobeniusIterateCycles_apply, ← AddCommGrpCat.comp_apply, toCycles_i,
      quotSMulTop_d_toQuotSMulTop_f_apply, iterate_map_add, hM.F_iterate_V_iterate_apply,
      hM.F_iterate_d_V_iterate_apply, map_add, map_nsmul, smul_toQuotSMulTop_f_apply,
      zero_add]
  rw [AddMonoidHom.mem_ker, AddCommGrpCat.comp_apply, this, ← AddCommGrpCat.comp_apply,
    toCycles_comp_homologyπ, AddCommGrpCat.zero_apply]

/-- The map `W_r(M)ⁿ → Hⁿ(M / pʳ M)` sending the class of `x` to the class of `Fʳ x`. -/
private noncomputable def verschiebungQuotientToHomology (r : ℕ) (n : ℤ) :
    (hM.verschiebungQuotient r).X n →+ (M.quotSMulTop (p ^ r)).homology n :=
  hM.verschiebungQuotientLift r n _ (hM.verschiebungFiltration_le_ker r n)

private lemma verschiebungQuotientToHomology_bijective (r : ℕ) (n : ℤ) :
    Function.Bijective (hM.verschiebungQuotientToHomology r n) := by
  set Q := M.quotSMulTop (p ^ r)
  have hi := (AddCommGrpCat.mono_iff_injective (Q.iCycles n)).1 inferInstance
  refine ⟨(injective_iff_map_eq_zero _).2 fun y hy ↦ ?_, fun z ↦ ?_⟩
  · -- If `[Fʳ x] = d [b]` in `M / pʳ M`, then `Fʳ x = d b + pʳ t`, so
    -- `pʳ x = Vʳ (Fʳ x) = pʳ (d (Vʳ b) + Vʳ t)`, and `x ∈ Nʳ Mⁿ`.
    obtain ⟨x, rfl⟩ := hM.toVerschiebungQuotient_f_surjective r n y
    rw [verschiebungQuotientToHomology, verschiebungQuotientLift_apply,
      AddCommGrpCat.comp_apply] at hy
    obtain ⟨b', hb'⟩ := addCommGrpCat_exists_toCycles_eq _ (CochainComplex.prev ℤ n) _ hy
    obtain ⟨b, rfl⟩ := M.toQuotSMulTop_f_surjective _ (n - 1) b'
    have h := congrArg (Q.iCycles n).hom hb'
    rw [← AddCommGrpCat.comp_apply, toCycles_i, quotSMulTop_d_toQuotSMulTop_f_apply,
      iCycles_frobeniusIterateCycles_apply, toQuotSMulTop_f_apply_eq_iff] at h
    obtain ⟨t, ht⟩ := h
    rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq'] at ht
    have hx : p ^ r • x = p ^ r • ((M.d (n - 1) n).hom ((⇑(hM.V (n - 1)).hom)^[r] b) -
        (⇑(hM.V n).hom)^[r] t) := by
      rw [← hM.V_iterate_F_iterate_apply, ht, iterate_map_sub, hM.V_iterate_d_apply,
        iterate_map_nsmul, smul_sub]
    rw [toVerschiebungQuotient_f_apply_eq_zero_iff, (hM.isSMulRegular n).pow r hx]
    exact sub_mem (hM.d_V_iterate_mem_verschiebungFiltration r b)
      (hM.V_iterate_mem_verschiebungFiltration r t)
  · -- A cocycle of `M / pʳ M` is the class of some `w` with `d w ∈ pʳ M`, and `w = Fʳ x`.
    obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (Q.homologyπ n)).1 inferInstance z
    obtain ⟨w, hw, t, ht⟩ := exists_toQuotSMulTop_eq_iCycles (n + 1) z
    obtain ⟨x, rfl⟩ := (hM.mem_range_F_iterate_iff r).2 ⟨t, ht⟩
    refine ⟨((hM.toVerschiebungQuotient r).f n).hom x, ?_⟩
    rw [verschiebungQuotientToHomology, verschiebungQuotientLift_apply, AddCommGrpCat.comp_apply]
    exact congrArg _ (hi (by rw [iCycles_frobeniusIterateCycles_apply, hw]))

/-- **The finite Verschiebung quotients compute cohomology modulo `pʳ`**
(Bhatt–Lurie–Mathew, Proposition 2.7.1). For a saturated Dieudonné complex `M`, the map
`θ_r : W_r(M)ⁿ ≅ Hⁿ(M / pʳ M)` sending the class of `x` to the class of the cocycle `Fʳ x` is an
isomorphism of abelian groups. -/
noncomputable def verschiebungQuotientIsoHomology (r : ℕ) (n : ℤ) :
    (hM.verschiebungQuotient r).X n ≅ (M.quotSMulTop (p ^ r)).homology n :=
  (AddEquiv.ofBijective _ (hM.verschiebungQuotientToHomology_bijective r n)).toAddCommGrpIso

/-- `θ_r` sends the class of `x` in `W_r(M)ⁿ` to the cohomology class of `Fʳ x`. -/
@[reassoc]
lemma toVerschiebungQuotient_f_comp_verschiebungQuotientIsoHomology_hom (r : ℕ) (n : ℤ) :
    (hM.toVerschiebungQuotient r).f n ≫ (hM.verschiebungQuotientIsoHomology r n).hom =
      M.frobeniusIterateCycles r n ≫ (M.quotSMulTop (p ^ r)).homologyπ n := by
  ext x
  exact hM.verschiebungQuotientLift_apply r _ _ x

/-- `θ_r` sends the class of `x` in `W_r(M)ⁿ` to the cohomology class of `Fʳ x`, on elements. -/
@[simp]
lemma verschiebungQuotientIsoHomology_hom_apply (r : ℕ) {n : ℤ} (x : M.X n) :
    (hM.verschiebungQuotientIsoHomology r n).hom.hom (((hM.toVerschiebungQuotient r).f n).hom x) =
      ((M.quotSMulTop (p ^ r)).homologyπ n).hom ((M.frobeniusIterateCycles r n).hom x) :=
  hM.verschiebungQuotientLift_apply r _ _ x

/-- `θ_r` is natural in morphisms of saturated Dieudonné complexes. -/
@[reassoc]
lemma verschiebungQuotientMap_f_comp_verschiebungQuotientIsoHomology_hom
    {N : DieudonneComplex.{u} p} (hN : N.IsSaturated) (f : M ⟶ N) (r : ℕ) (n : ℤ) :
    (hM.verschiebungQuotientMap hN f r).f n ≫ (hN.verschiebungQuotientIsoHomology r n).hom =
      (hM.verschiebungQuotientIsoHomology r n).hom ≫ homologyMap (quotSMulTopMap _ f.hom) n := by
  ext y
  obtain ⟨x, rfl⟩ := hM.toVerschiebungQuotient_f_surjective r n y
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply, verschiebungQuotientMap_f_apply,
    verschiebungQuotientIsoHomology_hom_apply, verschiebungQuotientIsoHomology_hom_apply,
    ← AddCommGrpCat.comp_apply _ (homologyMap _ n), homologyπ_naturality, AddCommGrpCat.comp_apply,
    ← AddCommGrpCat.comp_apply _ (cyclesMap _ n), frobeniusIterateCycles_naturality,
    AddCommGrpCat.comp_apply]

/-- The projection `M / pʳ M ⟶ W_r(M)`, which exists because `pʳ x = Vʳ (Fʳ x) ∈ Nʳ M`. -/
noncomputable def quotSMulTopToVerschiebungQuotient (r : ℕ) :
    M.quotSMulTop (p ^ r) ⟶ hM.verschiebungQuotient r :=
  quotSMulTopDesc (hM.toVerschiebungQuotient r) fun n x ↦ by
    rw [toVerschiebungQuotient_f_apply_eq_zero_iff]
    exact hM.pow_smul_mem_verschiebungFiltration r x

@[simp]
lemma quotSMulTopToVerschiebungQuotient_f_apply (r : ℕ) {n : ℤ} (x : M.X n) :
    ((hM.quotSMulTopToVerschiebungQuotient r).f n).hom
        (((M.toQuotSMulTop (p ^ r)).f n).hom x) =
      ((hM.toVerschiebungQuotient r).f n).hom x :=
  quotSMulTopDesc_f_apply _ _ x

@[reassoc (attr := simp)]
lemma toQuotSMulTop_comp_quotSMulTopToVerschiebungQuotient (r : ℕ) :
    M.toQuotSMulTop (p ^ r) ≫ hM.quotSMulTopToVerschiebungQuotient r =
      hM.toVerschiebungQuotient r :=
  toQuotSMulTop_comp_quotSMulTopDesc _ _

section QuasiIso

variable (r : ℕ) (n : ℤ)

/-- `M / pʳ M ⟶ W_r(M)` is injective on cohomology. Let `w` represent a cocycle of `M / pʳ M`
whose class in `W_r(M)` is `d [w']`. Then `w - d w' = Vʳ u + d (Vʳ v)` with
`d (Vʳ u) = d w ∈ pʳ M`, so `Vʳ u ∈ pʳ M` and `w = d (w' + Vʳ v) + Vʳ u` is a coboundary of
`M / pʳ M`. -/
private lemma injective_homologyMap_quotSMulTopToVerschiebungQuotient :
    Function.Injective (homologyMap (hM.quotSMulTopToVerschiebungQuotient r) n).hom := by
  set Q := M.quotSMulTop (p ^ r)
  refine (injective_iff_map_eq_zero _).2 fun y hy ↦ ?_
  obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (Q.homologyπ n)).1 inferInstance y
  rw [← AddCommGrpCat.comp_apply, homologyπ_naturality, AddCommGrpCat.comp_apply] at hy
  obtain ⟨y', hy'⟩ := addCommGrpCat_exists_toCycles_eq _ (CochainComplex.prev ℤ n) _ hy
  obtain ⟨w', rfl⟩ := hM.toVerschiebungQuotient_f_surjective r (n - 1) y'
  obtain ⟨w, hw, t, ht⟩ := exists_toQuotSMulTop_eq_iCycles (n + 1) z
  have h := congrArg ((hM.verschiebungQuotient r).iCycles n).hom hy'
  rw [← AddCommGrpCat.comp_apply, toCycles_i, verschiebungQuotient_d_toVerschiebungQuotient_f_apply,
    ← AddCommGrpCat.comp_apply (cyclesMap _ n), cyclesMap_i, AddCommGrpCat.comp_apply, ← hw,
    quotSMulTopToVerschiebungQuotient_f_apply, toVerschiebungQuotient_f_apply_eq_iff,
    ← neg_mem_iff, neg_sub, hM.mem_verschiebungFiltration_iff (sub_add_cancel n 1)] at h
  obtain ⟨u, v, huv⟩ := h
  obtain ⟨u', hu'⟩ := hM.exists_pow_smul_eq_V_iterate_iff.2
    ⟨t, by rw [ht, ← sub_eq_iff_eq_add.2 huv.symm]; simp⟩
  have hz : z = (Q.toCycles (n - 1) n).hom (((M.toQuotSMulTop (p ^ r)).f (n - 1)).hom
      (w' + (⇑(hM.V (n - 1)).hom)^[r] v)) := by
    refine (AddCommGrpCat.mono_iff_injective (Q.iCycles n)).1 inferInstance ?_
    rw [← AddCommGrpCat.comp_apply _ (Q.iCycles n), toCycles_i,
      quotSMulTop_d_toQuotSMulTop_f_apply, ← hw, toQuotSMulTop_f_apply_eq_iff, map_add]
    exact ⟨u', by rw [hu', ← sub_eq_iff_eq_add'.2 huv.symm]; abel⟩
  rw [hz, ← AddCommGrpCat.comp_apply, toCycles_comp_homologyπ, AddCommGrpCat.zero_apply]

/-- `M / pʳ M ⟶ W_r(M)` is surjective on cohomology. A cocycle of `W_r(M)` is the class of `x`
with `d x = Vʳ y + d (Vʳ w)`. Then `d (Vʳ y) = 0`, so `Vʳ y ∈ pʳ M`, and `x - Vʳ w` is a cocycle
of `M / pʳ M` with the same class in `W_r(M)`. -/
private lemma surjective_homologyMap_quotSMulTopToVerschiebungQuotient :
    Function.Surjective (homologyMap (hM.quotSMulTopToVerschiebungQuotient r) n).hom := by
  set W := hM.verschiebungQuotient r
  intro y
  obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (W.homologyπ n)).1 inferInstance y
  obtain ⟨x, hx⟩ := hM.toVerschiebungQuotient_f_surjective r n ((W.iCycles n).hom z)
  have hdx : (M.d n (n + 1)).hom x ∈ hM.verschiebungFiltration r (n + 1) := by
    rw [← toVerschiebungQuotient_f_apply_eq_zero_iff,
      ← verschiebungQuotient_d_toVerschiebungQuotient_f_apply, hx, ← AddCommGrpCat.comp_apply,
      iCycles_d, AddCommGrpCat.zero_apply]
  obtain ⟨y', w, hyw⟩ := (hM.mem_verschiebungFiltration_iff rfl).1 hdx
  obtain ⟨y'', hy''⟩ := hM.exists_pow_smul_eq_V_iterate_iff.2
    ⟨0, by simpa using (congrArg (M.d (n + 1) (n + 1 + 1)).hom hyw).symm⟩
  have hcyc : ((M.quotSMulTop (p ^ r)).d n (n + 1)).hom (((M.toQuotSMulTop (p ^ r)).f n).hom
      (x - (⇑(hM.V n).hom)^[r] w)) = 0 := by
    rw [quotSMulTop_d_toQuotSMulTop_f_apply, map_sub, ← hyw, add_sub_cancel_right, ← hy'',
      map_nsmul, smul_toQuotSMulTop_f_apply]
  obtain ⟨c, hc⟩ := addCommGrpCat_exists_iCycles_eq _ (CochainComplex.next ℤ n) _ hcyc
  refine ⟨((M.quotSMulTop (p ^ r)).homologyπ n).hom c, ?_⟩
  rw [← AddCommGrpCat.comp_apply, homologyπ_naturality, AddCommGrpCat.comp_apply]
  refine congrArg _ ((AddCommGrpCat.mono_iff_injective (W.iCycles n)).1 inferInstance ?_)
  rw [← AddCommGrpCat.comp_apply (cyclesMap _ n), cyclesMap_i, AddCommGrpCat.comp_apply, hc,
    quotSMulTopToVerschiebungQuotient_f_apply, ← hx, toVerschiebungQuotient_f_apply_eq_iff,
    sub_sub_cancel_left, neg_mem_iff]
  exact hM.V_iterate_mem_verschiebungFiltration r w

end QuasiIso

/-- **The projection `M / pʳ M ⟶ W_r(M)` is a quasi-isomorphism** (Bhatt–Lurie–Mathew,
Corollary 2.7.2 and Remark 2.7.3). -/
instance quasiIso_quotSMulTopToVerschiebungQuotient (r : ℕ) :
    QuasiIso (hM.quotSMulTopToVerschiebungQuotient r) where
  quasiIsoAt n := by
    rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
    exact ⟨hM.injective_homologyMap_quotSMulTopToVerschiebungQuotient r n,
      hM.surjective_homologyMap_quotSMulTopToVerschiebungQuotient r n⟩

/-- A morphism `f` of saturated Dieudonné complexes induces an isomorphism `W_r(f)` iff it induces
a quasi-isomorphism `M / pʳ M ⟶ N / pʳ N` (Bhatt–Lurie–Mathew, Corollary 2.7.4). -/
lemma isIso_verschiebungQuotientMap_iff_quasiIso {N : DieudonneComplex.{u} p}
    (hN : N.IsSaturated) (f : M ⟶ N) (r : ℕ) :
    IsIso (hM.verschiebungQuotientMap hN f r) ↔ QuasiIso (quotSMulTopMap (p ^ r) f.hom) := by
  have h (n : ℤ) : IsIso ((hM.verschiebungQuotientMap hN f r).f n) ↔
      IsIso (homologyMap (quotSMulTopMap (p ^ r) f.hom) n) := by
    rw [← isIso_comp_right_iff _ (hN.verschiebungQuotientIsoHomology r n).hom,
      hM.verschiebungQuotientMap_f_comp_verschiebungQuotientIsoHomology_hom hN,
      isIso_comp_left_iff]
  simp only [quasiIso_iff, quasiIsoAt_iff_isIso_homologyMap, ← h]
  exact ⟨fun _ n ↦ inferInstance, fun _ ↦ HomologicalComplex.Hom.isIso_of_components _⟩

/-- A morphism `f` of saturated Dieudonné complexes induces isomorphisms `W_r(f)` for every `r` as
soon as it induces an isomorphism `W_1(f)` (Bhatt–Lurie–Mathew, Corollary 2.7.4). Equivalently, by
`isIso_verschiebungQuotientMap_iff_quasiIso`, a quasi-isomorphism `M / p M ⟶ N / p N` gives
quasi-isomorphisms `M / pʳ M ⟶ N / pʳ N` for every `r`. -/
lemma forall_isIso_verschiebungQuotientMap_iff {N : DieudonneComplex.{u} p} (hN : N.IsSaturated)
    (f : M ⟶ N) :
    (∀ r, IsIso (hM.verschiebungQuotientMap hN f r)) ↔
      IsIso (hM.verschiebungQuotientMap hN f 1) := by
  refine ⟨fun h ↦ h 1, fun h r ↦ ?_⟩
  cases r with
  | zero =>
    -- `W_0(M)` and `W_0(N)` are zero.
    have (n : ℤ) : IsIso ((hM.verschiebungQuotientMap hN f 0).f n) :=
      (ConcreteCategory.isIso_iff_bijective _).2
        ⟨Function.injective_of_subsingleton _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
    exact HomologicalComplex.Hom.isIso_of_components _
  | succ r =>
    rw [isIso_verschiebungQuotientMap_iff_quasiIso, pow_one] at h
    rw [isIso_verschiebungQuotientMap_iff_quasiIso]
    exact quasiIso_quotSMulTopMap_pow_succ f.hom hM.isSMulRegular hN.isSMulRegular h r

end IsSaturated

end DieudonneComplex

end TauCeti

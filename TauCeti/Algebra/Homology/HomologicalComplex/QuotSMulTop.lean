/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.RingTheory.QuotSMulTop
public import TauCeti.Algebra.Homology.AddCommGrpCat.Basic
public import TauCeti.Algebra.Homology.HomologySequenceLemmas

/-!
# The reduction of a complex of abelian groups modulo a natural number

For a homological complex `K` of abelian groups and a natural number `a`, the complex `K / a K` has
terms `QuotSMulTop a (K.X i) = K.X i ⧸ a K.X i` and the differential induced by that of `K`.
Reductions modulo powers of a prime appear in the theory of Dieudonné complexes, whose finite
Verschiebung quotients compute the cohomology of the reductions modulo `pʳ`.

When the terms of `K` have no `n₂`-torsion, multiplication by `n₂` and the projection form a short
exact sequence `0 ⟶ K / n₁ K ⟶ K / n₁ n₂ K ⟶ K / n₂ K ⟶ 0`. By the five lemma on the associated
long exact sequences, a chain map between complexes with `a`-torsion-free terms that is a
quasi-isomorphism modulo `a` is a quasi-isomorphism modulo every positive power of `a`.

## Main definitions

* `HomologicalComplex.quotSMulTop K a`: the complex `K / a K`.
* `HomologicalComplex.toQuotSMulTop K a`: the projection `K ⟶ K / a K`.
* `HomologicalComplex.quotSMulTopDesc`: the chain map out of `K / a K` induced by a chain map
  out of `K` killing `a K`.
* `HomologicalComplex.quotSMulTopMap`: the chain map `K / a K ⟶ L / a L` induced by a chain map
  `K ⟶ L`.
* `HomologicalComplex.quotSMulTopShortComplex`: the sequence `K / n₁ K ⟶ K / n₁ n₂ K ⟶ K / n₂ K`.

## Main results

* `HomologicalComplex.quotSMulTopShortComplex_shortExact`: it is short exact when the terms of
  `K` have no `n₂`-torsion.
* `HomologicalComplex.quasiIso_quotSMulTopMap_pow_succ`: a quasi-isomorphism modulo `a` between
  complexes with `a`-torsion-free terms is a quasi-isomorphism modulo `aʳ⁺¹`.
-/

public section

open CategoryTheory

universe u

namespace HomologicalComplex

variable {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex AddCommGrpCat.{u} c) (a : ℕ)

/-- The reduction `K / a K` of a complex of abelian groups modulo a natural number `a`: its terms
are `QuotSMulTop a (K.X i) = K.X i ⧸ a K.X i`, with the differential induced by that of `K`. -/
noncomputable def quotSMulTop : HomologicalComplex AddCommGrpCat.{u} c where
  X i := AddCommGrpCat.of (QuotSMulTop (a : ℤ) (K.X i))
  d i j := AddCommGrpCat.ofHom
    (QuotSMulTop.map (a : ℤ) (K.d i j).hom.toIntLinearMap).toAddMonoidHom
  shape i j h := by
    ext x
    induction x using Submodule.Quotient.induction_on
    simp [K.shape i j h]
  d_comp_d' _ _ _ _ _ := by
    ext x
    induction x using Submodule.Quotient.induction_on
    simp

/-- The projection `K ⟶ K / a K`. -/
noncomputable def toQuotSMulTop : K ⟶ K.quotSMulTop a where
  f _ := AddCommGrpCat.ofHom (Submodule.mkQ _).toAddMonoidHom
  comm' _ _ _ := rfl

variable {K a}

/-- The differential of `K / a K` on the class of `x` is the class of `d x`. -/
@[simp]
lemma quotSMulTop_d_toQuotSMulTop_f_apply {i j : ι} (x : K.X i) :
    ((K.quotSMulTop a).d i j).hom (((K.toQuotSMulTop a).f i).hom x) =
      ((K.toQuotSMulTop a).f j).hom ((K.d i j).hom x) :=
  (rfl)

variable (K a) in
/-- The projection `K.X i → (K / a K).X i` is surjective. -/
lemma toQuotSMulTop_f_surjective (i : ι) : Function.Surjective ((K.toQuotSMulTop a).f i).hom :=
  Submodule.mkQ_surjective _

/-- The class of `x` in `K / a K` vanishes iff `x` is a multiple of `a`. -/
@[simp]
lemma toQuotSMulTop_f_apply_eq_zero_iff {i : ι} {x : K.X i} :
    ((K.toQuotSMulTop a).f i).hom x = 0 ↔ ∃ y, a • y = x :=
  (Submodule.Quotient.mk_eq_zero _).trans <|
    (Submodule.mem_smul_pointwise_iff_exists _ _ _).trans (by simp [natCast_zsmul])

/-- Two elements have the same class in `K / a K` iff their difference is a multiple of `a`. -/
lemma toQuotSMulTop_f_apply_eq_iff {i : ι} {x y : K.X i} :
    ((K.toQuotSMulTop a).f i).hom x = ((K.toQuotSMulTop a).f i).hom y ↔ ∃ z, a • z = x - y := by
  rw [← sub_eq_zero, ← map_sub, toQuotSMulTop_f_apply_eq_zero_iff]

/-- The terms of `K / a K` are killed by `a`. -/
@[simp]
lemma smul_toQuotSMulTop_f_apply {i : ι} (x : K.X i) :
    a • ((K.toQuotSMulTop a).f i).hom x = 0 := by
  rw [← map_nsmul, toQuotSMulTop_f_apply_eq_zero_iff]
  exact ⟨x, rfl⟩

/-- Chain maps out of `K / a K` are determined by their composites with the projection. -/
lemma quotSMulTop_hom_ext {L : HomologicalComplex AddCommGrpCat.{u} c}
    {φ ψ : K.quotSMulTop a ⟶ L} (h : K.toQuotSMulTop a ≫ φ = K.toQuotSMulTop a ≫ ψ) : φ = ψ := by
  ext i y
  obtain ⟨x, rfl⟩ := K.toQuotSMulTop_f_surjective a i y
  exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom h i) x

/-- A cycle of `K / a K` of degree `n` is the class of an element `w` whose differential to any
degree `m` is a multiple of `a`. -/
lemma exists_toQuotSMulTop_eq_iCycles {n : ι} (m : ι) (z : (K.quotSMulTop a).cycles n) :
    ∃ w, ((K.toQuotSMulTop a).f n).hom w = ((K.quotSMulTop a).iCycles n).hom z ∧
      ∃ t, a • t = (K.d n m).hom w := by
  obtain ⟨w, hw⟩ := K.toQuotSMulTop_f_surjective a n (((K.quotSMulTop a).iCycles n).hom z)
  refine ⟨w, hw, toQuotSMulTop_f_apply_eq_zero_iff.1 ?_⟩
  rw [← quotSMulTop_d_toQuotSMulTop_f_apply, hw, ← AddCommGrpCat.comp_apply, iCycles_d,
    AddCommGrpCat.zero_apply]

section Desc

variable {L : HomologicalComplex AddCommGrpCat.{u} c} (g : K ⟶ L)
  (hg : ∀ i (x : K.X i), (g.f i).hom (a • x) = 0)

/-- The chain map `K / a K ⟶ L` induced by a chain map `g : K ⟶ L` that kills `a K`. -/
noncomputable def quotSMulTopDesc : K.quotSMulTop a ⟶ L where
  f i := AddCommGrpCat.ofHom <| QuotientAddGroup.lift _ (g.f i).hom fun x hx ↦ by
    obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    rw [natCast_zsmul]
    exact hg i y
  comm' i j _ := by
    ext y
    obtain ⟨x, rfl⟩ := K.toQuotSMulTop_f_surjective a i y
    exact ConcreteCategory.congr_hom (g.comm i j) x

@[simp]
lemma quotSMulTopDesc_f_apply {i : ι} (x : K.X i) :
    ((quotSMulTopDesc g hg).f i).hom (((K.toQuotSMulTop a).f i).hom x) = (g.f i).hom x :=
  (rfl)

@[reassoc (attr := simp)]
lemma toQuotSMulTop_comp_quotSMulTopDesc : K.toQuotSMulTop a ≫ quotSMulTopDesc g hg = g :=
  (rfl)

end Desc

section Map

variable {L M : HomologicalComplex AddCommGrpCat.{u} c}

variable (a) in
/-- The chain map `K / a K ⟶ L / a L` induced by a chain map `φ : K ⟶ L`. -/
noncomputable def quotSMulTopMap (φ : K ⟶ L) : K.quotSMulTop a ⟶ L.quotSMulTop a :=
  quotSMulTopDesc (φ ≫ L.toQuotSMulTop a) fun i x ↦ by simp

@[simp]
lemma quotSMulTopMap_f_apply (φ : K ⟶ L) {i : ι} (x : K.X i) :
    ((quotSMulTopMap a φ).f i).hom (((K.toQuotSMulTop a).f i).hom x) =
      ((L.toQuotSMulTop a).f i).hom ((φ.f i).hom x) :=
  (rfl)

@[reassoc (attr := simp)]
lemma toQuotSMulTop_comp_quotSMulTopMap (φ : K ⟶ L) :
    K.toQuotSMulTop a ≫ quotSMulTopMap a φ = φ ≫ L.toQuotSMulTop a :=
  (rfl)

variable (K a) in
@[simp]
lemma quotSMulTopMap_id : quotSMulTopMap a (𝟙 K) = 𝟙 _ :=
  quotSMulTop_hom_ext rfl

@[simp, reassoc]
lemma quotSMulTopMap_comp (φ : K ⟶ L) (ψ : L ⟶ M) :
    quotSMulTopMap a (φ ≫ ψ) = quotSMulTopMap a φ ≫ quotSMulTopMap a ψ :=
  quotSMulTop_hom_ext rfl

end Map

section ShortExact

variable (K) {n₁ n₂ m : ℕ} (h : n₁ * n₂ = m)

/-- Multiplication by `n₂`, as a chain map `K / n₁ K ⟶ K / m K` for `m = n₁ n₂`. -/
noncomputable def quotSMulTopSMul : K.quotSMulTop n₁ ⟶ K.quotSMulTop m :=
  quotSMulTopDesc (n₂ • K.toQuotSMulTop m) fun i x ↦ by
    rw [nsmul_f_apply, AddCommGrpCat.hom_nsmul, AddMonoidHom.nsmul_apply, map_nsmul, smul_smul,
      mul_comm, h, smul_toQuotSMulTop_f_apply]

@[simp]
lemma quotSMulTopSMul_f_apply {i : ι} (x : K.X i) :
    ((K.quotSMulTopSMul h).f i).hom (((K.toQuotSMulTop n₁).f i).hom x) =
      ((K.toQuotSMulTop m).f i).hom (n₂ • x) := by
  rw [quotSMulTopSMul, quotSMulTopDesc_f_apply, nsmul_f_apply, AddCommGrpCat.hom_nsmul,
    AddMonoidHom.nsmul_apply, map_nsmul]

@[reassoc (attr := simp)]
lemma toQuotSMulTop_comp_quotSMulTopSMul :
    K.toQuotSMulTop n₁ ≫ K.quotSMulTopSMul h = n₂ • K.toQuotSMulTop m :=
  toQuotSMulTop_comp_quotSMulTopDesc _ _

/-- The projection `K / m K ⟶ K / n₂ K` for `m = n₁ n₂`. -/
noncomputable def quotSMulTopProj : K.quotSMulTop m ⟶ K.quotSMulTop n₂ :=
  quotSMulTopDesc (K.toQuotSMulTop n₂) fun i x ↦ by
    rw [← h, mul_comm, mul_smul, map_nsmul, smul_toQuotSMulTop_f_apply]

@[simp]
lemma quotSMulTopProj_f_apply {i : ι} (x : K.X i) :
    ((K.quotSMulTopProj h).f i).hom (((K.toQuotSMulTop m).f i).hom x) =
      ((K.toQuotSMulTop n₂).f i).hom x :=
  quotSMulTopDesc_f_apply _ _ x

@[reassoc (attr := simp)]
lemma toQuotSMulTop_comp_quotSMulTopProj :
    K.toQuotSMulTop m ≫ K.quotSMulTopProj h = K.toQuotSMulTop n₂ :=
  toQuotSMulTop_comp_quotSMulTopDesc _ _

/-- The sequence `K / n₁ K ⟶ K / m K ⟶ K / n₂ K`, for `m = n₁ n₂`, whose maps are multiplication
by `n₂` and the projection. -/
noncomputable def quotSMulTopShortComplex : ShortComplex (HomologicalComplex AddCommGrpCat.{u} c) :=
  ShortComplex.mk (K.quotSMulTopSMul h) (K.quotSMulTopProj h) <| quotSMulTop_hom_ext <| by
    ext i x
    simp

/-- If the terms of `K` have no `n₂`-torsion, the sequence
`0 ⟶ K / n₁ K ⟶ K / n₁ n₂ K ⟶ K / n₂ K ⟶ 0` is short exact. -/
lemma quotSMulTopShortComplex_shortExact (hK : ∀ i, IsSMulRegular (K.X i) n₂) :
    (K.quotSMulTopShortComplex h).ShortExact := by
  refine shortExact_of_degreewise_shortExact _ fun i ↦ ?_
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ab_exact_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := K.toQuotSMulTop_f_surjective m i y
    obtain ⟨z, hz⟩ := toQuotSMulTop_f_apply_eq_zero_iff.1 hy
    exact ⟨((K.toQuotSMulTop n₁).f i).hom z, (K.quotSMulTopSMul_f_apply h z).trans (by rw [hz])⟩
  · rw [AddCommGrpCat.mono_iff_injective, injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨x, rfl⟩ := K.toQuotSMulTop_f_surjective n₁ i y
    obtain ⟨z, hz⟩ := toQuotSMulTop_f_apply_eq_zero_iff.1 hy
    rw [← h, mul_comm, mul_smul] at hz
    exact toQuotSMulTop_f_apply_eq_zero_iff.2 ⟨z, hK i hz⟩
  · rw [AddCommGrpCat.epi_iff_surjective]
    intro y
    obtain ⟨x, rfl⟩ := K.toQuotSMulTop_f_surjective n₂ i y
    exact ⟨((K.toQuotSMulTop m).f i).hom x, K.quotSMulTopProj_f_apply h x⟩

variable {K} {L : HomologicalComplex AddCommGrpCat.{u} c}

/-- The morphism of short exact sequences induced by a chain map `φ : K ⟶ L`. -/
noncomputable def quotSMulTopShortComplexMap (φ : K ⟶ L) :
    K.quotSMulTopShortComplex h ⟶ L.quotSMulTopShortComplex h where
  τ₁ := quotSMulTopMap n₁ φ
  τ₂ := quotSMulTopMap m φ
  τ₃ := quotSMulTopMap n₂ φ
  comm₁₂ := quotSMulTop_hom_ext <| by simp [quotSMulTopShortComplex]
  comm₂₃ := quotSMulTop_hom_ext <| by simp [quotSMulTopShortComplex]

/-- A chain map between complexes whose terms have no `a`-torsion that induces a
quasi-isomorphism modulo `a` induces a quasi-isomorphism modulo every positive power of `a`, by
induction along the short exact sequences `0 ⟶ K / aʳ K ⟶ K / aʳ⁺¹ K ⟶ K / a K ⟶ 0`. -/
lemma quasiIso_quotSMulTopMap_pow_succ (φ : K ⟶ L) (hK : ∀ i, IsSMulRegular (K.X i) a)
    (hL : ∀ i, IsSMulRegular (L.X i) a) (hφ : QuasiIso (quotSMulTopMap a φ)) (r : ℕ) :
    QuasiIso (quotSMulTopMap (a ^ (r + 1)) φ) := by
  induction r with
  | zero => rwa [zero_add, pow_one]
  | succ r ih =>
    exact HomologySequence.quasiIso_τ₂ (quotSMulTopShortComplexMap (pow_succ a (r + 1)).symm φ)
      (K.quotSMulTopShortComplex_shortExact _ hK) (L.quotSMulTopShortComplex_shortExact _ hL) ih hφ

end ShortExact

end HomologicalComplex

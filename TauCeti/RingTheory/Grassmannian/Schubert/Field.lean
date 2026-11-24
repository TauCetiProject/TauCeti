/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Localization.FractionRing
public import TauCeti.RingTheory.Grassmannian.Schubert.Basic

import Mathlib.LinearAlgebra.Transvection.Basic
import TauCeti.Data.Fin.StrictMono
import TauCeti.LinearAlgebra.TensorProduct.Basis
import TauCeti.LinearAlgebra.TensorProduct.Submodule

/-!
# Field points of Schubert cells and single-step polynomial deformations

Let `M` be a free module over a commutative ring `R` with a basis `b` indexed by `Fin n`, and let
`p : Fin r → Fin n` be strictly increasing zero-based pivot positions with `r + k = n`.

This file characterizes field-valued points of the Schubert cell and of the determinantal Schubert
rank locus in terms of `Module.Basis.flagPivots`, and constructs explicit one-step `𝔸¹_K` families
over `K[X]` raising non-maximal pivot tuples toward `p`:

* Over a field `K`, a point `N ∈ G(k, K ⊗[R] M; K)` lies in the Schubert cell at `p` if and only if
  `(b.baseChange K).flagPivots N.toSubmodule = Finset.univ.image p`
  (`mem_chart_and_rankLocus_eq_bot_iff_flagPivots`), in which case `schubertCellEquiv` agrees with
  `(b.baseChange K).flagCellEquiv` (`schubertCellEquiv_eq_flagCellEquiv`). More generally, `N`
  satisfies all Schubert rank conditions for `p` if and only if its pivot tuple `p'` satisfies
  `p' ≤ p` coordinatewise (`forall_rankLocus_eq_bot_iff_exists_flagPivots`).
* Whenever `p' ≤ p` and `p' ≠ p`, an elementary basis transvection over `K[X]` produces an
  `𝔸¹_K`-family specializing at `0` to `N` whose generic fiber over `FractionRing K[X]` has a
  strictly increasing pivot tuple `p''` with `p' ≤ p'' ≤ p` and strictly smaller Bruhat gap
  `∑ i, (p i - p'' i)` (`exists_sum_sub_lt_and_map_aeval_zero_eq_of_flagPivots_eq`). This supplies
  the specialization step along `Spec K[X] → G(k, M)` used in
  `TauCeti.AlgebraicGeometry.Grassmannian.Schubert` to prove that `schemeSchubertLocus` is the
  Zariski closure of `schubertCellι`.

## Main results

* `Module.Grassmannian.mem_chart_and_rankLocus_eq_bot_iff_flagPivots`: field-point characterization
  of the Schubert cell via `Module.Basis.flagPivots`.
* `Module.Grassmannian.schubertCellEquiv_eq_flagCellEquiv`: agreement of `schubertCellEquiv` with
  `Module.Basis.flagCellEquiv` over a field.
* `Module.Grassmannian.forall_rankLocus_eq_bot_iff_exists_flagPivots`: field-point characterization
  of the Schubert rank locus in the Bruhat order.
* `Module.Grassmannian.exists_sum_sub_lt_and_map_aeval_zero_eq_of_flagPivots_eq`: one-step
  `𝔸¹_K`-family specializing at `0` to `N` and reducing the Bruhat gap `∑ i, (p i - p' i)`.

## References

* W. Fulton, *Young tableaux*, London Mathematical Society Student Texts 35, Cambridge University
  Press (1997), §9.4.
* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Mathematical Surveys and
  Monographs 107, American Mathematical Society (2003), Part II, Chapter 13.
-/

public section

universe u v w

open TensorProduct Module Finset

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {A B : Type w} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  {n r k : ℕ} {K : Type w} [Field K] [Algebra R K] (b : Basis (Fin n) R M)

/-- **Field points of the Schubert cell.** Over a field `K`, a point `N ∈ G(k, K ⊗[R] M; K)` lies
in the adapted chart at `b ∘ schubertComplEmb hp hnk` and satisfies all Schubert rank conditions
for `p` if and only if its pivot set `(b.baseChange K).flagPivots N.toSubmodule` equals
`Finset.univ.image p`. -/
theorem mem_chart_and_rankLocus_eq_bot_iff_flagPivots
    {p : Fin r → Fin n} (hp : StrictMono p) (hnk : r + k = n) (N : G(k, K ⊗[R] M; K)) :
    (N ∈ chart K (fun j ↦ (1 : K) ⊗ₜ[R] schubertChartBasis b hp hnk (.inr j)) ∧
      ∀ i : Fin r, N.rankLocus (b.flag (p i).succ) ((p i : ℕ) - i) = ⊥) ↔
      (b.baseChange K).flagPivots N.toSubmodule = univ.image p := by
  constructor
  · rintro ⟨hchart, hrank⟩
    let a := schubertCellEquiv b hp hnk K ⟨⟨N, hchart⟩, hrank⟩
    have hN : N = ((schubertCellEquiv b hp hnk K).symm a).val.val := by simp [a]
    rw [hN, toSubmodule_schubertCellEquiv_symm]
    exact Basis.flagPivots_span_echelonRow (univ.image p) a
  · intro hpiv
    let a := (b.baseChange K).flagCellEquiv (univ.image p) ⟨N.toSubmodule, hpiv⟩
    have hN : N = ((schubertCellEquiv b hp hnk K).symm a).val.val := Grassmannian.ext <| by
      rw [toSubmodule_schubertCellEquiv_symm, ← Basis.coe_flagCellEquiv_symm_apply,
        Equiv.symm_apply_apply]
    rw [hN]
    exact ⟨((schubertCellEquiv b hp hnk K).symm a).val.property,
        ((schubertCellEquiv b hp hnk K).symm a).property⟩

/-- Over a field `K`, the Schubert cell coordinates `schubertCellEquiv` agree with the linear
echelon coordinates `(b.baseChange K).flagCellEquiv (Finset.univ.image p)`. -/
theorem schubertCellEquiv_eq_flagCellEquiv {p : Fin r → Fin n}
    (hp : StrictMono p) (hnk : r + k = n)
    (N : {N : chart K (fun j ↦ (1 : K) ⊗ₜ[R] schubertChartBasis b hp hnk (.inr j)) //
      ∀ i : Fin r, N.val.rankLocus (b.flag (p i).succ) ((p i : ℕ) - i) = ⊥}) :
    schubertCellEquiv b hp hnk K N =
      (b.baseChange K).flagCellEquiv (univ.image p)
        ⟨N.val.val.toSubmodule,
          (mem_chart_and_rankLocus_eq_bot_iff_flagPivots b hp hnk N.val.val).mp ⟨N.val.property,
              N.property⟩⟩ := by
  refine ((b.baseChange K).flagCellEquiv (univ.image p)).symm.injective <| Subtype.ext ?_
  rw [Equiv.symm_apply_apply, Basis.coe_flagCellEquiv_symm_apply,
    ← toSubmodule_schubertCellEquiv_symm b hp hnk, Equiv.symm_apply_apply]

/-- **Field points of the Schubert rank locus in the Bruhat order.** Over a field `K`, a point
`N ∈ G(k, K ⊗[R] M; K)` (with `r + k = n`) satisfies all Schubert rank conditions for `p` if and
only if the strictly increasing pivot sequence `p' : Fin r → Fin n` of `N.toSubmodule` satisfies
`p' i ≤ p i` for every `i`. -/
theorem forall_rankLocus_eq_bot_iff_exists_flagPivots
    {p : Fin r → Fin n} (hp : StrictMono p) (hnk : r + k = n) (N : G(k, K ⊗[R] M; K)) :
    (∀ i : Fin r, N.rankLocus (b.flag (p i).succ) ((p i : ℕ) - i) = ⊥) ↔
      ∃ p' : Fin r → Fin n, StrictMono p' ∧
        (b.baseChange K).flagPivots N.toSubmodule = univ.image p' ∧ ∀ i : Fin r, p' i ≤ p i := by
  have := Module.Finite.of_basis (b.baseChange K)
  have hcard : #((b.baseChange K).flagPivots N.toSubmodule) = r := by
    rw [Basis.card_flagPivots, N.finrank_toSubmodule, finrank_eq_card_basis (b.baseChange K),
      Fintype.card_fin]
    omega
  let p' : Fin r ↪o Fin n := ((b.baseChange K).flagPivots N.toSubmodule).orderEmbOfFin hcard
  have hpiv : (b.baseChange K).flagPivots N.toSubmodule = univ.image p' :=
    (Finset.image_orderEmbOfFin_univ _ hcard).symm
  constructor
  · intro hrank
    refine ⟨p', p'.strictMono, hpiv, fun i ↦ ?_⟩
    by_contra! hlt
    have hdim := (N.rankLocus_eq_bot_iff_finrank_inf (b.flag (p i).succ) ((p i : ℕ) - i)).mp
      (hrank i)
    rw [← Basis.flag_baseChange, Basis.finrank_flag, Fin.val_succ, inf_comm,
      Basis.finrank_inf_flag, hpiv, filter_image, card_image_of_injective _ p'.injective] at hdim
    have hhi := (Fin.val_strictMono.comp hp).add_sub_le_nat
      (Fin.le_def.mpr (Nat.zero_le i) : (⟨0, i.pos⟩ : Fin r) ≤ i)
    simp only [Function.comp_apply] at hhi
    have hcard_lt : #{l : Fin r | (p' l).castSucc < (p i).succ} ≤ i :=
      (card_le_card fun l hl ↦ mem_Iio.mpr <| p'.strictMono.lt_iff_lt.mp <|
        (Fin.castSucc_lt_succ_iff.mp (mem_filter.mp hl).2).trans_lt hlt).trans_eq (Fin.card_Iio i)
    omega
  · rintro ⟨p₁, hp₁, hpiv₁, hle⟩
    have hcell := ((mem_chart_and_rankLocus_eq_bot_iff_flagPivots b hp₁ hnk N).mpr hpiv₁).2
    rw [← iSup_eq_bot] at hcell ⊢
    exact le_bot_iff.mp ((iSup_rankLocus_flag_succ_anti b hp hp₁ hle N).trans_eq hcell)

/-! ### Elementary basis transvections and single-step polynomial deformations -/

private noncomputable def shearLin (u v : Fin n) (t : A) : A ⊗[R] M →ₗ[A] A ⊗[R] M :=
  LinearMap.transvection (t • (b.baseChange A).coord u) ((b.baseChange A) v)

private theorem repr_shearLin (u v : Fin n) (t : A) (x : A ⊗[R] M) (w : Fin n) :
    (b.baseChange A).repr (shearLin b u v t x) w =
      (b.baseChange A).repr x w + if w = v then t * (b.baseChange A).repr x u else 0 := by
  simp [shearLin, LinearMap.transvection.apply, Finsupp.single_apply, eq_comm]

private noncomputable def shearEquiv {u v : Fin n} (huv : u ≠ v) (t : A) :
    (A ⊗[R] M) ≃ₗ[A] (A ⊗[R] M) :=
  LinearEquiv.transvection (f := t • (b.baseChange A).coord u) (v := (b.baseChange A) v)
    (by simp [Finsupp.single_eq_of_ne huv])

@[simp]
private theorem shearEquiv_toLinearMap {u v : Fin n} (huv : u ≠ v) (t : A) :
    (shearEquiv b huv t).toLinearMap = shearLin b u v t :=
  rfl

@[simp]
private theorem shearEquiv_apply {u v : Fin n} (huv : u ≠ v) (t : A) (x : A ⊗[R] M) :
    shearEquiv b huv t x = shearLin b u v t x :=
  rfl

@[simp]
private theorem shearEquiv_zero {u v : Fin n} (huv : u ≠ v) :
    shearEquiv b huv (0 : A) = LinearEquiv.refl A (A ⊗[R] M) := by
  simp [shearEquiv]

private theorem map_grassmannianCongr_shearEquiv {u v : Fin n} (huv : u ≠ v) (t : A)
    (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)) :
    map f ((shearEquiv b huv t).grassmannianCongr N) =
      (shearEquiv b huv (f t)).grassmannianCongr (map f N) := by
  ext : 1
  rw [map_toSubmodule_eq_span, LinearEquiv.toSubmodule_grassmannianCongr_apply,
    LinearEquiv.toSubmodule_grassmannianCongr_apply, map_toSubmodule_eq_span,
    Submodule.map_span, Submodule.map_coe, ← Set.image_comp, ← Set.image_comp]
  refine congrArg (Submodule.span B) <| Set.image_congr' rfl fun x ↦
    (b.baseChange B).repr.injective (Finsupp.ext fun w ↦ ?_)
  simp only [Function.comp_apply, shearEquiv_toLinearMap, LinearMap.rTensor_def,
    ← b.map_baseChange_repr, repr_shearLin, AlgHom.toLinearMap_apply, map_add, apply_ite f,
    map_mul, map_zero]

section Shear

variable {L : Type w} [Field L] [Algebra R L] (jKL : K →ₐ[R] L)

private noncomputable def baseChangeEchelon (p' : Fin r → Fin n) (N : G(k, K ⊗[R] M; K))
    (m : Fin r) : L ⊗[R] M :=
  jKL.toLinearMap.rTensor M ((b.baseChange K).flagEchelon N.toSubmodule (p' m))

private theorem repr_baseChangeEchelon_eq_zero_of_lt {p' : Fin r → Fin n} (N : G(k, K ⊗[R] M; K))
    (m : Fin r) {q : Fin n} (hmq : p' m < q) :
    (b.baseChange L).repr (baseChangeEchelon b jKL p' N m) q = 0 := by
  rw [baseChangeEchelon, LinearMap.rTensor_def, ← b.map_baseChange_repr,
    ((b.baseChange K).mem_flag_iff_repr_eq_zero.mp
      ((b.baseChange K).flagEchelon_mem_flag N.toSubmodule (p' m))) q
      (Fin.succ_le_castSucc_iff.mpr hmq), map_zero]

private theorem repr_baseChangeEchelon_pivot {p' : Fin r → Fin n} (hp' : StrictMono p')
    (N : G(k, K ⊗[R] M; K)) (hpiv : (b.baseChange K).flagPivots N.toSubmodule = univ.image p')
    (l m : Fin r) :
    (b.baseChange L).repr (baseChangeEchelon b jKL p' N l) (p' m) = if l = m then 1 else 0 := by
  rw [baseChangeEchelon, LinearMap.rTensor_def, ← b.map_baseChange_repr,
    (b.baseChange K).repr_flagEchelon (p' l) (hpiv ▸ mem_image_of_mem p' (mem_univ m))]
  simp [Finsupp.single_apply, hp'.injective.eq_iff]

private noncomputable def shearEchelonVec (p' : Fin r → Fin n) (i₀ : Fin r) (v : Fin n)
    (t : L) (N : G(k, K ⊗[R] M; K)) (l : Fin r) : L ⊗[R] M :=
  let y (m : Fin r) := shearLin b (p' i₀) v t (baseChangeEchelon b jKL p' N m)
  if l = i₀ then t⁻¹ • y i₀ else y l - ((b.baseChange L).repr (y l) v * t⁻¹) • y i₀

private theorem shearLin_baseChangeEchelon_of_ne {p' : Fin r → Fin n} (hp' : StrictMono p')
    {i₀ m : Fin r} (hm : m ≠ i₀) (v : Fin n) (t : L) (N : G(k, K ⊗[R] M; K))
    (hpiv : (b.baseChange K).flagPivots N.toSubmodule = univ.image p') :
    shearLin b (p' i₀) v t (baseChangeEchelon b jKL p' N m) = baseChangeEchelon b jKL p' N m :=
  (b.baseChange L).repr.injective <| Finsupp.ext fun w ↦ by
    simp [repr_shearLin, repr_baseChangeEchelon_pivot b jKL hp' N hpiv m i₀, hm]

private theorem toSubmodule_grassmannianCongr_shearEquiv_eq_span {p' : Fin r → Fin n}
    {i₀ : Fin r} {v : Fin n} (huv : p' i₀ < v) {t : L} (ht : t ≠ 0) (N : G(k, K ⊗[R] M; K))
    (hpiv : (b.baseChange K).flagPivots N.toSubmodule = univ.image p') :
    ((shearEquiv b huv.ne t).grassmannianCongr (map jKL N)).toSubmodule =
      Submodule.span L (Set.range (shearEchelonVec b jKL p' i₀ v t N)) := by
  set y : Fin r → L ⊗[R] M := fun l ↦ shearLin b (p' i₀) v t (baseChangeEchelon b jKL p' N l)
  set y' := shearEchelonVec b jKL p' i₀ v t N
  have hN_echelon : N.toSubmodule = Submodule.span K
      (Set.range fun l : Fin r ↦ (b.baseChange K).flagEchelon N.toSubmodule (p' l)) := by
    conv_lhs => rw [← (b.baseChange K).span_flagEchelon (W := N.toSubmodule)]
    exact congrArg (Submodule.span K) <| Set.ext fun x ↦ by simp [hpiv]
  have hrange :
      ((⇑(shearEquiv b huv.ne t).toLinearMap ∘ ⇑(jKL.toLinearMap.rTensor M)) ∘
        fun l : Fin r ↦ (b.baseChange K).flagEchelon N.toSubmodule (p' l)) = y :=
    funext fun l ↦ by simp [y, baseChangeEchelon]
  rw [LinearEquiv.toSubmodule_grassmannianCongr_apply, map_toSubmodule_eq_span, hN_echelon,
    Submodule.span_rTensor_image_span, Submodule.map_span, ← Set.image_comp, ← Set.range_comp,
    hrange]
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨l, rfl⟩
    by_cases hl : l = i₀
    · subst l
      have hy : y i₀ = t • y' i₀ := by
        simp [y', shearEchelonVec, y, smul_smul, mul_inv_cancel₀ ht]
      rw [hy]
      exact Submodule.smul_mem _ t (Submodule.subset_span ⟨i₀, rfl⟩)
    · have hy : y l = y' l + ((b.baseChange L).repr (y l) v) • y' i₀ := by
        simp [y', shearEchelonVec, y, ite_eq_right hl, smul_smul]
      rw [hy]
      exact add_mem (Submodule.subset_span ⟨l, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i₀, rfl⟩))
  · rintro _ ⟨l, rfl⟩
    by_cases hl : l = i₀
    · subst l; simp only [y', shearEchelonVec, ↓reduceIte]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i₀, rfl⟩)
    · simp only [y', shearEchelonVec, ite_eq_right hl]
      exact sub_mem (Submodule.subset_span ⟨l, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i₀, rfl⟩))

private theorem shearEchelonVec_mem_flag {p' : Fin r → Fin n} (hp' : StrictMono p')
    {i₀ : Fin r} {v : Fin n} (huv : p' i₀ < v) (hgt : ∀ l : Fin r, i₀ < l → v < p' l)
    (t : L) (N : G(k, K ⊗[R] M; K))
    (hpiv : (b.baseChange K).flagPivots N.toSubmodule = univ.image p') (l : Fin r) :
    shearEchelonVec b jKL p' i₀ v t N l ∈
      (b.baseChange L).flag (Function.update p' i₀ v l).succ := by
  rw [Basis.mem_flag_iff_repr_eq_zero]
  intro w hw
  have hpw : Function.update p' i₀ v l < w := Fin.succ_le_castSucc_iff.mp hw
  by_cases hl : l = i₀
  · subst l
    have hvw : v < w := by simpa using hpw
    simp [shearEchelonVec, repr_shearLin, ite_eq_right hvw.ne',
      repr_baseChangeEchelon_eq_zero_of_lt b jKL N i₀ (huv.trans hvw)]
  · have hplw : p' l < w := by simpa [Function.update_of_ne hl] using hpw
    rcases lt_or_gt_of_ne hl with hlt | hgt'
    · simp [shearEchelonVec, hl, shearLin_baseChangeEchelon_of_ne b jKL hp' hl v t N hpiv,
        repr_baseChangeEchelon_eq_zero_of_lt b jKL N l hplw,
        repr_baseChangeEchelon_eq_zero_of_lt b jKL N l ((hp' hlt).trans huv)]
    · have hvw : v < w := (hgt l hgt').trans hplw
      simp [shearEchelonVec, hl, shearLin_baseChangeEchelon_of_ne b jKL hp' hl v t N hpiv,
        repr_baseChangeEchelon_eq_zero_of_lt b jKL N l hplw, repr_shearLin, hvw.ne',
        repr_baseChangeEchelon_eq_zero_of_lt b jKL N i₀ (huv.trans hvw)]

private theorem repr_shearEchelonVec_update {p' : Fin r → Fin n} (hp' : StrictMono p')
    {i₀ : Fin r} {v : Fin n} (huv : p' i₀ < v) (hgt : ∀ l : Fin r, i₀ < l → v < p' l)
    {t : L} (ht : t ≠ 0) (N : G(k, K ⊗[R] M; K))
    (hpiv : (b.baseChange K).flagPivots N.toSubmodule = univ.image p') (l m : Fin r) :
    (b.baseChange L).repr (shearEchelonVec b jKL p' i₀ v t N l) (Function.update p' i₀ v m) =
      Finsupp.single (Function.update p' i₀ v l) 1 (Function.update p' i₀ v m) := by
  set y' := shearEchelonVec b jKL p' i₀ v t N
  have hp'_ne_v (c : Fin r) : p' c ≠ v := by
    rcases lt_trichotomy c i₀ with h | rfl | h
    exacts [((hp' h).trans huv).ne, huv.ne, (hgt c h).ne']
  have hyi₀ (w : Fin n) : (b.baseChange L).repr (y' i₀) w =
      if w = v then 1 else t⁻¹ * (b.baseChange L).repr (baseChangeEchelon b jKL p' N i₀) w := by
    simp only [y', shearEchelonVec, ↓reduceIte, LinearEquiv.map_smul, Finsupp.smul_apply,
      smul_eq_mul, repr_shearLin]
    split_ifs with hwv
    · subst w; simp [repr_baseChangeEchelon_eq_zero_of_lt b jKL N i₀ huv,
        repr_baseChangeEchelon_pivot b jKL hp' N hpiv i₀ i₀, inv_mul_cancel₀ ht]
    · simp
  by_cases hl : l = i₀
  · subst l; by_cases hm : m = i₀
    · subst m; simp [hyi₀]
    · simp [hm, hyi₀, hp'_ne_v m, repr_baseChangeEchelon_pivot b jKL hp' N hpiv i₀ m,
        Ne.symm hm, Finsupp.single_eq_of_ne (hp'_ne_v m)]
  · have hy'_sub : y' l = baseChangeEchelon b jKL p' N l -
        (b.baseChange L).repr (baseChangeEchelon b jKL p' N l) v • y' i₀ := by
      simp [y', shearEchelonVec, hl,
        shearLin_baseChangeEchelon_of_ne b jKL hp' hl v t N hpiv, smul_smul]
    by_cases hm : m = i₀
    · subst m; simp [hl, hy'_sub, hyi₀, Finsupp.single_eq_of_ne (hp'_ne_v l).symm]
    · simp [hl, hm, hy'_sub, hyi₀, hp'_ne_v m, repr_baseChangeEchelon_pivot b jKL hp' N hpiv i₀ m,
        Ne.symm hm, repr_baseChangeEchelon_pivot b jKL hp' N hpiv l m,
        Finsupp.single_apply, hp'.injective.eq_iff]

private theorem flagPivots_grassmannianCongr_shearEquiv {p' : Fin r → Fin n} (hp' : StrictMono p')
    {i₀ : Fin r} {v : Fin n} (huv : p' i₀ < v) (hp'' : StrictMono (Function.update p' i₀ v))
    (hgt : ∀ l : Fin r, i₀ < l → v < p' l) {t : L} (ht : t ≠ 0) (N : G(k, K ⊗[R] M; K))
    (hpiv : (b.baseChange K).flagPivots N.toSubmodule = univ.image p') :
    (b.baseChange L).flagPivots
      ((shearEquiv b huv.ne t).grassmannianCongr (map jKL N)).toSubmodule =
      univ.image (Function.update p' i₀ v) := by
  set p'' := Function.update p' i₀ v
  set y' := shearEchelonVec b jKL p' i₀ v t N
  let eS : Fin r ≃ univ.image p'' :=
    Equiv.ofBijective (fun l ↦ ⟨p'' l, mem_image_of_mem p'' (mem_univ l)⟩)
      ⟨fun _ _ h ↦ hp''.injective (Subtype.mk.inj h),
        fun ⟨_, hs⟩ ↦ by obtain ⟨l, -, rfl⟩ := mem_image.mp hs; exact ⟨l, rfl⟩⟩
  have heS (l : Fin r) : (eS l : Fin n) = p'' l := rfl
  rw [toSubmodule_grassmannianCongr_shearEquiv_eq_span b jKL huv ht N hpiv,
    ← eS.symm.surjective.range_comp y']
  refine Basis.flagPivots_span_eq (fun s ↦ ?_) (fun s q hq ↦ ?_)
  · obtain ⟨l, rfl⟩ := eS.surjective s
    rw [Function.comp_apply, Equiv.symm_apply_apply, heS l]
    exact shearEchelonVec_mem_flag b jKL hp' huv hgt t N hpiv l
  · obtain ⟨l, rfl⟩ := eS.surjective s; obtain ⟨m, -, rfl⟩ := mem_image.mp hq
    rw [Function.comp_apply, Equiv.symm_apply_apply, heS l]
    exact repr_shearEchelonVec_update b jKL hp' huv hgt ht N hpiv l m

end Shear

/-- **One-step polynomial family in a Schubert locus.** Let `N ∈ G(k, K ⊗[R] M; K)` over a field
`K` have pivot sequence `p' : Fin r → Fin n` with `p' ≤ p` and `p' ≠ p`. Then there exists an
`𝔸¹_K`-family `N_poly ∈ G(k, K[X] ⊗[R] M; K[X])` whose fiber at `X = 0` is `N` and whose generic
fiber over `FractionRing K[X]` has a strictly increasing pivot sequence `p''` with `p' ≤ p'' ≤ p`
and strictly smaller gap sum `∑ i, (p i - p'' i)`. -/
theorem exists_sum_sub_lt_and_map_aeval_zero_eq_of_flagPivots_eq
    {p p' : Fin r → Fin n} (hp : StrictMono p) (hp' : StrictMono p')
    (hle : ∀ i, p' i ≤ p i) (hne : p' ≠ p) (N : G(k, K ⊗[R] M; K))
    (hpiv : (b.baseChange K).flagPivots N.toSubmodule = univ.image p') :
    ∃ (N_poly : G(k, Polynomial K ⊗[R] M; Polynomial K)) (p'' : Fin r → Fin n),
      StrictMono p'' ∧ (∀ i, p' i ≤ p'' i) ∧ (∀ i, p'' i ≤ p i) ∧
      ∑ i, ((p i : ℕ) - p'' i) < ∑ i, ((p i : ℕ) - p' i) ∧
      map ((Polynomial.aeval (0 : K)).restrictScalars R) N_poly = N ∧
      (b.baseChange (FractionRing (Polynomial K))).flagPivots
        (map (IsScalarTower.toAlgHom R (Polynomial K) (FractionRing (Polynomial K)))
          N_poly).toSubmodule = univ.image p'' := by
  obtain ⟨i₀, v, huv, hp'', hp''_le, hgt, hsum⟩ := hp.exists_update_strictMono hp' hle hne
  let jKP : K →ₐ[R] Polynomial K := IsScalarTower.toAlgHom R K _
  let ι : Polynomial K →ₐ[R] FractionRing (Polynomial K) := IsScalarTower.toAlgHom R _ _
  refine ⟨(shearEquiv b huv.ne Polynomial.X).grassmannianCongr (map jKP N),
    Function.update p' i₀ v, hp'',
    fun i ↦ by by_cases hi : i = i₀ <;> simp [hi, huv.le], hp''_le, hsum, ?_, ?_⟩
  · let ev₀ : Polynomial K →ₐ[R] K := (Polynomial.aeval (0 : K)).restrictScalars R
    have hev₀_X : ev₀ Polynomial.X = 0 := by simp [ev₀]
    have hev₀_comp : ev₀.comp jKP = AlgHom.id R K := AlgHom.ext fun _ ↦ by simp [ev₀, jKP]
    rw [map_grassmannianCongr_shearEquiv, hev₀_X, shearEquiv_zero, ← map_comp, hev₀_comp,
      map_id k (.of R K)]
    ext : 1; simp
  · have ht : ι Polynomial.X ≠ 0 :=
      (map_ne_zero_iff ι (IsFractionRing.injective _ _)).mpr Polynomial.X_ne_zero
    rw [map_grassmannianCongr_shearEquiv, ← map_comp]
    exact flagPivots_grassmannianCongr_shearEquiv b (ι.comp jKP) hp' huv hp'' hgt ht N hpiv

end Module.Grassmannian

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Localization.FractionRing
public import TauCeti.RingTheory.Grassmannian.Schubert.Basic

import TauCeti.Data.Fin.StrictMono
import TauCeti.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Field points of Schubert cells and single-step polynomial deformations

Let `M` be a free module over a commutative ring `R` with a basis `b` indexed by `Fin n`, and let
`p : Fin r → Fin n` be strictly increasing zero-based pivot positions with `r + k = n`.

This file characterizes field-valued points of the Schubert cell and of the determinantal Schubert
rank locus in terms of `Module.Basis.flagPivots`, and constructs explicit one-step `𝔸¹_K`
deformations raising non-maximal pivot tuples toward `p`:

* Over a field `K`, a point `N ∈ G(k, K ⊗[R] M; K)` lies in the Schubert cell at `p` if and only if
  `(b.baseChange K).flagPivots N.toSubmodule = Finset.univ.image p`
  (`mem_chart_and_rankLocus_eq_bot_iff_flagPivots`), and satisfies all Schubert rank conditions for
  `p` if and only if its pivot tuple `p'` satisfies `p' ≤ p` coordinatewise
  (`forall_rankLocus_eq_bot_iff_exists_flagPivots`).
* Whenever `p' ≤ p` and `p' ≠ p`, an elementary basis transvection over `K[X]` produces an
  `𝔸¹_K`-family specializing at `0` to `N` whose generic fiber over `FractionRing K[X]` has a
  strictly larger pivot tuple `p'' ≤ p` (`exists_polynomial_deformation_of_flagPivots_lt`).

## Main results

* `Module.Grassmannian.finrank_toSubmodule_of_basis`: when `r + k = n`, a field point
  `N ∈ G(k, K ⊗[R] M; K)` has `dim_K N = r`.
* `Module.Grassmannian.mem_chart_and_rankLocus_eq_bot_iff_flagPivots`: field-point characterization
  of the Schubert cell via `Module.Basis.flagPivots`.
* `Module.Grassmannian.forall_rankLocus_eq_bot_iff_exists_flagPivots`: field-point characterization
  of the Schubert rank locus in the Bruhat order.
* `Module.Grassmannian.exists_polynomial_deformation_of_flagPivots_lt`: one-step `𝔸¹_K`-deformation
  reducing the Bruhat gap `∑ i, (p i - p' i)`.

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
  {n r k : ℕ} {K : Type w} [Field K] [Algebra R K]

/-- Over a field `K`, a point `N ∈ G(k, K ⊗[R] M; K)` with `r + k = n` has `dim_K N = r`. -/
theorem finrank_toSubmodule_of_basis (b : Basis (Fin n) R M) (hnk : r + k = n)
    (N : G(k, K ⊗[R] M; K)) :
    finrank K N.toSubmodule = r := by
  have := Module.Finite.of_basis (b.baseChange K)
  have hsum := N.toSubmodule.finrank_quotient_add_finrank
  rw [TauCeti.Module.finrank_eq_of_rankAtStalk_eq (funext N.rankAtStalk_eq),
    finrank_eq_card_basis (b.baseChange K), Fintype.card_fin] at hsum
  omega

/-- **Field points of the Schubert cell.** Over a field `K`, a point `N ∈ G(k, K ⊗[R] M; K)` lies
in the adapted chart at `b ∘ schubertComplEmb hp hnk` and satisfies all Schubert rank conditions
for `p` if and only if its pivot set `(b.baseChange K).flagPivots N.toSubmodule` equals
`Finset.univ.image p`. -/
theorem mem_chart_and_rankLocus_eq_bot_iff_flagPivots (b : Basis (Fin n) R M)
    {p : Fin r → Fin n} (hp : StrictMono p) (hnk : r + k = n) (N : G(k, K ⊗[R] M; K)) :
    (N ∈ chart K (fun j ↦ (1 : K) ⊗ₜ[R] schubertChartBasis b hp hnk (.inr j)) ∧
      ∀ i : Fin r, N.rankLocus (b.flag (p i).succ) ((p i : ℕ) - i) = ⊥) ↔
      (b.baseChange K).flagPivots N.toSubmodule = univ.image p := by
  constructor
  · rintro ⟨hchart, hrank⟩
    let a := schubertCellEquiv b hp hnk K ⟨⟨N, hchart⟩, hrank⟩
    rw [show N.toSubmodule = ((schubertCellEquiv b hp hnk K).symm a).1.1.toSubmodule by simp [a],
      toSubmodule_schubertCellEquiv_symm]
    exact Basis.flagPivots_span_echelonRow (univ.image p) a
  · intro hpiv
    let a := (b.baseChange K).flagCellEquiv (univ.image p) ⟨N.toSubmodule, hpiv⟩
    have hN : N = ((schubertCellEquiv b hp hnk K).symm a).1.1 := Grassmannian.ext <| by
      rw [toSubmodule_schubertCellEquiv_symm, ← Basis.coe_flagCellEquiv_symm_apply,
        Equiv.symm_apply_apply]
    rw [hN]
    exact ⟨((schubertCellEquiv b hp hnk K).symm a).1.2, ((schubertCellEquiv b hp hnk K).symm a).2⟩

/-- **Field points of the Schubert rank locus in the Bruhat order.** Over a field `K`, a point
`N ∈ G(k, K ⊗[R] M; K)` (with `r + k = n`) satisfies all Schubert rank conditions for `p` if and
only if the strictly increasing pivot sequence `p' : Fin r → Fin n` of `N.toSubmodule` satisfies
`p' i ≤ p i` for every `i`. -/
theorem forall_rankLocus_eq_bot_iff_exists_flagPivots (b : Basis (Fin n) R M)
    {p : Fin r → Fin n} (hp : StrictMono p) (hnk : r + k = n) (N : G(k, K ⊗[R] M; K)) :
    (∀ i : Fin r, N.rankLocus (b.flag (p i).succ) ((p i : ℕ) - i) = ⊥) ↔
      ∃ p' : Fin r → Fin n, StrictMono p' ∧
        (b.baseChange K).flagPivots N.toSubmodule = univ.image p' ∧ ∀ i : Fin r, p' i ≤ p i := by
  have := Module.Finite.of_basis (b.baseChange K)
  have hcard : #((b.baseChange K).flagPivots N.toSubmodule) = r := by
    rw [Basis.card_flagPivots, finrank_toSubmodule_of_basis b hnk N]
  let p' : Fin r ↪o Fin n := ((b.baseChange K).flagPivots N.toSubmodule).orderEmbOfFin hcard
  have hpiv : (b.baseChange K).flagPivots N.toSubmodule = univ.image p' := by
    rw [← coe_inj, coe_image, coe_univ, Set.image_univ, Finset.range_orderEmbOfFin]
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
    exact le_bot_iff.mp ((iSup_rankLocus_flag_succ_antitone b hp hp₁ hle N).trans_eq hcell)

/-! ### Elementary basis transvections and single-step polynomial deformations -/

private theorem repr_baseChange_rTensor (b : Basis (Fin n) R M) (f : A →ₐ[R] B) (x : A ⊗[R] M)
    (w : Fin n) :
    (b.baseChange B).repr (f.toLinearMap.rTensor M x) w = f ((b.baseChange A).repr x w) := by
  have hterm (q : Fin n) :
      ((b.baseChange B).repr (f.toLinearMap.rTensor M
        ((b.baseChange A).repr x q • (b.baseChange A) q))) w =
        if w = q then f ((b.baseChange A).repr x q) else 0 := by
    rw [Basis.baseChange_apply, smul_tmul', smul_eq_mul, mul_one, LinearMap.rTensor_tmul,
      AlgHom.toLinearMap_apply, ← mul_one (f _), ← smul_eq_mul, ← smul_tmul',
      ← Basis.baseChange_apply, LinearEquiv.map_smul, Finsupp.smul_apply, Basis.repr_self,
      smul_eq_mul, Finsupp.single_apply]
    rcases eq_or_ne w q with rfl | hwq
    · simp
    · simp [hwq, hwq.symm]
  conv_lhs => rw [← (b.baseChange A).sum_repr x]
  rw [map_sum, map_sum, Finset.sum_apply']
  simp only [hterm, Finset.sum_ite_eq, mem_univ, ↓reduceIte]

private noncomputable def shearLin (b : Basis (Fin n) R M) (u v : Fin n) (t : A) :
    A ⊗[R] M →ₗ[A] A ⊗[R] M :=
  LinearMap.id + t • ((b.baseChange A).coord u).smulRight ((b.baseChange A) v)

private theorem repr_shearLin (b : Basis (Fin n) R M) (u v : Fin n) (t : A) (x : A ⊗[R] M)
    (w : Fin n) :
    (b.baseChange A).repr (shearLin b u v t x) w =
      (b.baseChange A).repr x w + if w = v then t * (b.baseChange A).repr x u else 0 := by
  simp [shearLin, Finsupp.single_apply, eq_comm, mul_comm]

private noncomputable def shearEquiv (b : Basis (Fin n) R M) {u v : Fin n} (huv : u ≠ v)
    (t : A) : (A ⊗[R] M) ≃ₗ[A] (A ⊗[R] M) :=
  LinearEquiv.ofLinearMap (shearLin b u v t) (shearLin b u v (-t))
    (LinearMap.ext fun x ↦ (b.baseChange A).repr.injective <| Finsupp.ext fun w ↦ by
      simp [repr_shearLin, ite_eq_right huv]; split_ifs <;> ring)
    (LinearMap.ext fun x ↦ (b.baseChange A).repr.injective <| Finsupp.ext fun w ↦ by
      simp [repr_shearLin, ite_eq_right huv]; split_ifs <;> ring)

private theorem map_grassmannianCongr_shearEquiv (b : Basis (Fin n) R M) {u v : Fin n}
    (huv : u ≠ v) (t : A) (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)) :
    map f ((shearEquiv b huv t).grassmannianCongr N) =
      (shearEquiv b huv (f t)).grassmannianCongr (map f N) := by
  ext : 1
  rw [map_toSubmodule_eq_span, LinearEquiv.toSubmodule_grassmannianCongr_apply,
    LinearEquiv.toSubmodule_grassmannianCongr_apply, map_toSubmodule_eq_span,
    Submodule.map_span, Submodule.map_coe, ← Set.image_comp, ← Set.image_comp]
  refine congrArg (Submodule.span B) <| Set.image_congr' fun x ↦
    (b.baseChange B).repr.injective (Finsupp.ext fun w ↦ ?_)
  dsimp [shearEquiv]
  rw [repr_baseChange_rTensor, repr_shearLin, repr_shearLin, repr_baseChange_rTensor,
    repr_baseChange_rTensor, map_add, apply_ite f, map_mul, map_zero]

private theorem span_rTensor_image_span (f : A →ₐ[R] B) (s : Set (A ⊗[R] M)) :
    Submodule.span B (f.toLinearMap.rTensor M '' (Submodule.span A s : Set (A ⊗[R] M))) =
      Submodule.span B (f.toLinearMap.rTensor M '' s) := by
  have hsmul (a : A) (y : A ⊗[R] M) :
      f.toLinearMap.rTensor M (a • y) = f a • f.toLinearMap.rTensor M y := by
    induction y using TensorProduct.inductionOn with
    | tmul a' m => simp [smul_tmul', map_mul]
    | add y₁ y₂ h₁ h₂ => rw [smul_add, map_add, h₁, h₂, map_add, smul_add]
  refine le_antisymm (Submodule.span_le.mpr ?_)
    (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨x, hx, rfl⟩
  exact Submodule.span_induction (fun y hy ↦ Submodule.subset_span ⟨y, hy, rfl⟩) (by simp)
    (fun _ _ _ _ h₁ h₂ ↦ by rw [map_add]; exact add_mem h₁ h₂)
    (fun a _ _ hy ↦ by rw [hsmul]; exact Submodule.smul_mem _ (f a) hy) hx

private theorem exists_update_succ_strictMono {p p' : Fin r → Fin n} (hp : StrictMono p)
    (hp' : StrictMono p') (hle : ∀ i, p' i ≤ p i) (hne : p' ≠ p) :
    ∃ (i₀ : Fin r) (v : Fin n),
      p' i₀ < v ∧
      StrictMono (Function.update p' i₀ v) ∧
      (∀ i, Function.update p' i₀ v i ≤ p i) ∧
      (∀ l : Fin r, i₀ < l → v < p' l) ∧
      ∑ i, ((p i : ℕ) - Function.update p' i₀ v i) < ∑ i, ((p i : ℕ) - p' i) := by
  obtain ⟨i₁, hi₁⟩ := Function.ne_iff.mp hne
  have hD : ({i : Fin r | p' i < p i} : Finset (Fin r)).Nonempty :=
    ⟨i₁, mem_filter.mpr ⟨mem_univ i₁, lt_of_le_of_ne (hle i₁) hi₁⟩⟩
  let i₀ : Fin r := ({i : Fin r | p' i < p i} : Finset (Fin r)).max' hD
  have hi₀ : p' i₀ < p i₀ := (mem_filter.mp (max'_mem _ hD)).2
  let v : Fin n := ⟨(p' i₀ : ℕ) + 1, lt_of_le_of_lt (Nat.succ_le_of_lt hi₀) (p i₀).isLt⟩
  have huv : p' i₀ < v := Fin.lt_def.mpr (Nat.lt_succ_self _)
  have hvp : v ≤ p i₀ := Fin.le_def.mpr (Nat.succ_le_of_lt hi₀)
  have hgt (l : Fin r) (hl : i₀ < l) : v < p' l := by
    have hmax : p' l = p l := le_antisymm (hle l)
      (not_lt.mp fun hlt ↦ hl.not_ge (le_max' _ l (mem_filter.mpr ⟨mem_univ l, hlt⟩)))
    exact hmax ▸ hvp.trans_lt (hp hl)
  refine ⟨i₀, v, huv, fun a c hac ↦ ?_, fun i ↦ ?_, hgt,
    Finset.sum_lt_sum (fun i _ ↦ ?_) ⟨i₀, mem_univ i₀, ?_⟩⟩
  · by_cases ha : a = i₀
    · subst a; rw [Function.update_self, Function.update_of_ne hac.ne']; exact hgt c hac
    · rw [Function.update_of_ne ha]
      by_cases hc : c = i₀
      · subst c; rw [Function.update_self]; exact (hp' hac).trans huv
      · rw [Function.update_of_ne hc]; exact hp' hac
  · by_cases hi : i = i₀
    · subst i; rwa [Function.update_self]
    · rw [Function.update_of_ne hi]; exact hle i
  · by_cases hi : i = i₀
    · subst i; rw [Function.update_self]; omega
    · rw [Function.update_of_ne hi]
  · rw [Function.update_self]
    have : (p' i₀ : ℕ) < p i₀ := hi₀
    have : (v : ℕ) = (p' i₀ : ℕ) + 1 := rfl
    omega

private noncomputable def baseChangeEchelon {L : Type w} [Field L] [Algebra R L]
    (b : Basis (Fin n) R M) (jKL : K →ₐ[R] L) (p' : Fin r → Fin n)
    (N : G(k, K ⊗[R] M; K)) (m : Fin r) : L ⊗[R] M :=
  jKL.toLinearMap.rTensor M ((b.baseChange K).flagEchelon N.toSubmodule (p' m))

private theorem repr_baseChangeEchelon_eq_zero_of_lt {L : Type w} [Field L] [Algebra R L]
    (b : Basis (Fin n) R M) (jKL : K →ₐ[R] L) {p' : Fin r → Fin n} (N : G(k, K ⊗[R] M; K))
    (m : Fin r) {q : Fin n} (hmq : p' m < q) :
    (b.baseChange L).repr (baseChangeEchelon b jKL p' N m) q = 0 := by
  rw [baseChangeEchelon, repr_baseChange_rTensor, ((b.baseChange K).mem_flag_iff_repr_eq_zero.mp
    ((b.baseChange K).flagEchelon_mem_flag N.toSubmodule (p' m))) q
    (Fin.succ_le_castSucc_iff.mpr hmq), map_zero]

private theorem repr_baseChangeEchelon_pivot {L : Type w} [Field L] [Algebra R L]
    (b : Basis (Fin n) R M) (jKL : K →ₐ[R] L) {p' : Fin r → Fin n} (hp' : StrictMono p')
    (N : G(k, K ⊗[R] M; K)) (hpiv : (b.baseChange K).flagPivots N.toSubmodule = univ.image p')
    (l m : Fin r) :
    (b.baseChange L).repr (baseChangeEchelon b jKL p' N l) (p' m) = if l = m then 1 else 0 := by
  have hm : p' m ∈ (b.baseChange K).flagPivots N.toSubmodule :=
    hpiv ▸ mem_image_of_mem p' (mem_univ m)
  rw [baseChangeEchelon, repr_baseChange_rTensor, (b.baseChange K).repr_flagEchelon (p' l) hm]
  simp [Finsupp.single_apply, hp'.injective.eq_iff]

private noncomputable def shearEchelonVec {L : Type w} [Field L] [Algebra R L]
    (b : Basis (Fin n) R M) (jKL : K →ₐ[R] L) (p' : Fin r → Fin n) (i₀ : Fin r) (v : Fin n)
    (t : L) (N : G(k, K ⊗[R] M; K)) (l : Fin r) : L ⊗[R] M :=
  let y (m : Fin r) := shearLin b (p' i₀) v t (baseChangeEchelon b jKL p' N m)
  if l = i₀ then t⁻¹ • y i₀ else y l - ((b.baseChange L).repr (y l) v * t⁻¹) • y i₀

private theorem shearLin_baseChangeEchelon_of_ne {L : Type w} [Field L] [Algebra R L]
    (b : Basis (Fin n) R M) (jKL : K →ₐ[R] L) {p' : Fin r → Fin n} (hp' : StrictMono p')
    {i₀ m : Fin r} (hm : m ≠ i₀) (v : Fin n) (t : L) (N : G(k, K ⊗[R] M; K))
    (hpiv : (b.baseChange K).flagPivots N.toSubmodule = univ.image p') :
    shearLin b (p' i₀) v t (baseChangeEchelon b jKL p' N m) = baseChangeEchelon b jKL p' N m :=
  (b.baseChange L).repr.injective <| Finsupp.ext fun w ↦ by
    simp [repr_shearLin, repr_baseChangeEchelon_pivot b jKL hp' N hpiv m i₀, hm]

private theorem toSubmodule_grassmannianCongr_shearEquiv_eq_span {L : Type w} [Field L]
    [Algebra R L] (b : Basis (Fin n) R M) (jKL : K →ₐ[R] L) {p' : Fin r → Fin n}
    {i₀ : Fin r} {v : Fin n} (huv : p' i₀ < v) {t : L} (ht : t ≠ 0) (N : G(k, K ⊗[R] M; K))
    (hpiv : (b.baseChange K).flagPivots N.toSubmodule = univ.image p') :
    ((shearEquiv b huv.ne t).grassmannianCongr (map jKL N)).toSubmodule =
      Submodule.span L (Set.range (shearEchelonVec b jKL p' i₀ v t N)) := by
  let y (l : Fin r) : L ⊗[R] M := shearLin b (p' i₀) v t (baseChangeEchelon b jKL p' N l)
  set y' := shearEchelonVec b jKL p' i₀ v t N
  have hN_echelon : N.toSubmodule = Submodule.span K
      (Set.range fun l : Fin r ↦ (b.baseChange K).flagEchelon N.toSubmodule (p' l)) := by
    conv_lhs => rw [← (b.baseChange K).span_flagEchelon (W := N.toSubmodule)]
    refine congrArg (Submodule.span K) (Set.ext fun x ↦ ?_)
    simp only [Set.mem_range, Subtype.exists, hpiv, mem_image, mem_univ, true_and]
    exact ⟨by rintro ⟨_, ⟨l, rfl⟩, rfl⟩; exact ⟨l, rfl⟩, fun ⟨l, hx⟩ ↦ ⟨p' l, ⟨l, rfl⟩, hx⟩⟩
  rw [LinearEquiv.toSubmodule_grassmannianCongr_apply, map_toSubmodule_eq_span, hN_echelon,
    span_rTensor_image_span, Submodule.map_span, ← Set.image_comp, ← Set.range_comp]
  change Submodule.span L (Set.range y) = Submodule.span L (Set.range y')
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨l, rfl⟩
    by_cases hl : l = i₀
    · subst l
      rw [show y i₀ = t • y' i₀ by simp [y', shearEchelonVec, y, smul_smul, mul_inv_cancel₀ ht]]
      exact Submodule.smul_mem _ t (Submodule.subset_span ⟨i₀, rfl⟩)
    · rw [show y l = y' l + ((b.baseChange L).repr (y l) v) • y' i₀ by
        simp [y', shearEchelonVec, y, ite_eq_right hl, smul_smul]]
      exact add_mem (Submodule.subset_span ⟨l, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i₀, rfl⟩))
  · rintro _ ⟨l, rfl⟩
    by_cases hl : l = i₀
    · subst l
      simp only [y', shearEchelonVec, ↓reduceIte]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i₀, rfl⟩)
    · simp only [y', shearEchelonVec, ite_eq_right hl]
      exact sub_mem (Submodule.subset_span ⟨l, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i₀, rfl⟩))

private theorem shearEchelonVec_mem_flag {L : Type w} [Field L] [Algebra R L]
    (b : Basis (Fin n) R M) (jKL : K →ₐ[R] L) {p' : Fin r → Fin n} (hp' : StrictMono p')
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
    dsimp only [shearEchelonVec]
    rw [ite_eq_right hl, shearLin_baseChangeEchelon_of_ne b jKL hp' hl v t N hpiv, map_sub,
      LinearEquiv.map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
      repr_baseChangeEchelon_eq_zero_of_lt b jKL N l hplw, zero_sub, neg_eq_zero]
    rcases lt_or_gt_of_ne hl with hlt | hgt'
    · rw [repr_baseChangeEchelon_eq_zero_of_lt b jKL N l ((hp' hlt).trans huv),
        zero_mul, zero_mul]
    · have hvw : v < w := (hgt l hgt').trans hplw
      rw [repr_shearLin, ite_eq_right hvw.ne', add_zero,
        repr_baseChangeEchelon_eq_zero_of_lt b jKL N i₀ (huv.trans hvw), mul_zero]

private theorem repr_shearEchelonVec_update {L : Type w} [Field L] [Algebra R L]
    (b : Basis (Fin n) R M) (jKL : K →ₐ[R] L) {p' : Fin r → Fin n} (hp' : StrictMono p')
    {i₀ : Fin r} {v : Fin n} (huv : p' i₀ < v) (hgt : ∀ l : Fin r, i₀ < l → v < p' l)
    {t : L} (ht : t ≠ 0) (N : G(k, K ⊗[R] M; K))
    (hpiv : (b.baseChange K).flagPivots N.toSubmodule = univ.image p') (l m : Fin r) :
    (b.baseChange L).repr (shearEchelonVec b jKL p' i₀ v t N l)
      (Function.update p' i₀ v m) =
      Finsupp.single (Function.update p' i₀ v l) 1 (Function.update p' i₀ v m) := by
  set y' := shearEchelonVec b jKL p' i₀ v t N
  have hp'_ne_v (c : Fin r) : p' c ≠ v := by
    rcases lt_trichotomy c i₀ with hlt | rfl | hgt'
    · exact ((hp' hlt).trans huv).ne
    · exact huv.ne
    · exact (hgt c hgt').ne'
  have hyi₀ (w : Fin n) :
      (b.baseChange L).repr (y' i₀) w =
        if w = v then 1 else t⁻¹ * (b.baseChange L).repr (baseChangeEchelon b jKL p' N i₀) w := by
    simp only [y', shearEchelonVec, ↓reduceIte, LinearEquiv.map_smul, Finsupp.smul_apply,
      smul_eq_mul, repr_shearLin]
    split_ifs with hwv
    · subst w
      rw [repr_baseChangeEchelon_eq_zero_of_lt b jKL N i₀ huv,
        repr_baseChangeEchelon_pivot b jKL hp' N hpiv i₀ i₀, ite_eq_left rfl, zero_add, mul_one,
        inv_mul_cancel₀ ht]
    · rw [add_zero]
  by_cases hl : l = i₀
  · subst l
    by_cases hm : m = i₀
    · subst m; simp [hyi₀]
    · rw [Function.update_of_ne hm, Function.update_self, hyi₀, ite_eq_right (hp'_ne_v m),
        repr_baseChangeEchelon_pivot b jKL hp' N hpiv i₀ m, ite_eq_right (Ne.symm hm), mul_zero,
        Finsupp.single_eq_of_ne (hp'_ne_v m)]
  · have hy'_sub : y' l = baseChangeEchelon b jKL p' N l -
        (b.baseChange L).repr (baseChangeEchelon b jKL p' N l) v • y' i₀ := by
      simp [y', shearEchelonVec, ite_eq_right hl,
        shearLin_baseChangeEchelon_of_ne b jKL hp' hl v t N hpiv, smul_smul]
    by_cases hm : m = i₀
    · subst m
      rw [Function.update_self, Function.update_of_ne hl, hy'_sub, map_sub, LinearEquiv.map_smul,
        Finsupp.sub_apply, Finsupp.smul_apply, hyi₀, ite_eq_left rfl, smul_eq_mul, mul_one,
        sub_self, Finsupp.single_eq_of_ne (hp'_ne_v l).symm]
    · rw [Function.update_of_ne hm, Function.update_of_ne hl, hy'_sub, map_sub,
        LinearEquiv.map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, hyi₀,
        ite_eq_right (hp'_ne_v m), repr_baseChangeEchelon_pivot b jKL hp' N hpiv i₀ m,
        ite_eq_right (Ne.symm hm), mul_zero, mul_zero, sub_zero,
        repr_baseChangeEchelon_pivot b jKL hp' N hpiv l m]
      simp [Finsupp.single_apply, hp'.injective.eq_iff]

private theorem flagPivots_grassmannianCongr_shearEquiv {L : Type w} [Field L] [Algebra R L]
    (b : Basis (Fin n) R M) (jKL : K →ₐ[R] L) {p' : Fin r → Fin n} (hp' : StrictMono p')
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
  have heS (l : Fin r) : (eS l : Fin n) = p'' l :=
    congrArg Subtype.val (congrFun (Equiv.coe_ofBijective _ _) l)
  rw [toSubmodule_grassmannianCongr_shearEquiv_eq_span b jKL huv ht N hpiv,
    show Set.range y' = Set.range (fun s : univ.image p'' ↦ y' (eS.symm s)) from
      (eS.symm.surjective.range_comp y').symm]
  refine Basis.flagPivots_span_eq (fun s ↦ ?_) (fun s q hq ↦ ?_)
  · obtain ⟨l, rfl⟩ := eS.surjective s
    rw [Equiv.symm_apply_apply, heS l]
    exact shearEchelonVec_mem_flag b jKL hp' huv hgt t N hpiv l
  · obtain ⟨l, rfl⟩ := eS.surjective s
    obtain ⟨m, -, rfl⟩ := mem_image.mp hq
    rw [Equiv.symm_apply_apply, heS l]
    exact repr_shearEchelonVec_update b jKL hp' huv hgt ht N hpiv l m

/-- **One-step polynomial deformation in a Schubert locus.** Let `N ∈ G(k, K ⊗[R] M; K)` over a
field `K` have pivot sequence `p' : Fin r → Fin n` with `p' ≤ p` and `p' ≠ p`. Then there exists
an `𝔸¹_K`-family `N_poly ∈ G(k, K[X] ⊗[R] M; K[X])` whose fiber at `X = 0` is `N` and whose generic
fiber over `FractionRing K[X]` has a strictly increasing pivot sequence `p'' ≤ p` with strictly
smaller gap sum `∑ i, (p i - p'' i)`. -/
theorem exists_polynomial_deformation_of_flagPivots_lt (b : Basis (Fin n) R M)
    {p p' : Fin r → Fin n} (hp : StrictMono p) (hp' : StrictMono p')
    (hle : ∀ i, p' i ≤ p i) (hne : p' ≠ p) (N : G(k, K ⊗[R] M; K))
    (hpiv : (b.baseChange K).flagPivots N.toSubmodule = univ.image p') :
    ∃ (N_poly : G(k, Polynomial K ⊗[R] M; Polynomial K)) (p'' : Fin r → Fin n),
      StrictMono p'' ∧ (∀ i, p'' i ≤ p i) ∧
      ∑ i, ((p i : ℕ) - p'' i) < ∑ i, ((p i : ℕ) - p' i) ∧
      map ((Polynomial.aeval (0 : K)).restrictScalars R) N_poly = N ∧
      (b.baseChange (FractionRing (Polynomial K))).flagPivots
        (map (IsScalarTower.toAlgHom R (Polynomial K) (FractionRing (Polynomial K)))
          N_poly).toSubmodule = univ.image p'' := by
  obtain ⟨i₀, v, huv, hp'', hp''_le, hgt, hsum⟩ :=
    exists_update_succ_strictMono hp hp' hle hne
  let P := Polynomial K
  let L := FractionRing P
  let jKP : K →ₐ[R] P := IsScalarTower.toAlgHom R K P
  let ι : P →ₐ[R] L := IsScalarTower.toAlgHom R P L
  refine ⟨(shearEquiv b huv.ne Polynomial.X).grassmannianCongr (map jKP N),
    Function.update p' i₀ v, hp'', hp''_le, hsum, ?_, ?_⟩
  · let ev₀ : P →ₐ[R] K := (Polynomial.aeval (0 : K)).restrictScalars R
    rw [map_grassmannianCongr_shearEquiv, show ev₀ Polynomial.X = 0 from Polynomial.aeval_X 0,
      ← map_comp, show ev₀.comp jKP = AlgHom.id R K from AlgHom.ext fun _ ↦ by simp [ev₀, jKP],
      map_id k (.of R K)]
    ext : 1; simp [shearEquiv, shearLin]
  · have ht : ι Polynomial.X ≠ 0 :=
      (map_ne_zero_iff ι (IsFractionRing.injective P L)).mpr Polynomial.X_ne_zero
    rw [map_grassmannianCongr_shearEquiv, ← map_comp]
    exact flagPivots_grassmannianCongr_shearEquiv b (ι.comp jKP) hp' huv hp'' hgt ht N hpiv

end Module.Grassmannian

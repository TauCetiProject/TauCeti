/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.StdBasis
public import TauCeti.Algebra.Category.GradedModuleCat.Coproducts.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Free
import TauCeti.Algebra.Module.GradedModule.Nakayama
import TauCeti.RingTheory.GradedAlgebra.Basic

/-!
# Graded freeness of retracts of finite graded free modules

Let `A` be a `ℤ`-graded `k`-algebra concentrated in nonnegative degrees whose degree-zero piece
consists of `k`-scalars, where `k` is a principal ideal domain acting faithfully on `A`. Every
graded retract of a finite graded free `A`-module `free 𝒜 s` is again isomorphic to a finite
graded free `A`-module `free 𝒜 d`.

The algebra `A` need not be commutative or of low global dimension, and `k` need not be a field:
unlike `TauCeti.Algebra.Category.GradedModuleCat.Idempotent.MinimalResolution`, the degree-zero
subalgebra `𝒜 0 ≅ k` need not be semisimple (for instance, `A` may be a positively weighted
polynomial ring over `ℤ` in arbitrarily many variables), so arbitrary bounded-below graded modules
do not admit projective covers. For a graded retract of `free 𝒜 s`, however, the degree-`p` head
modulo the positive-degree action `A₊` embeds into the finite free `k`-module indexed by the
summands with `s j = p`. Because `k` is a principal ideal domain, that degree-`p` head has a
finite `k`-basis. Lifting those `k`-bases homogeneously gives a graded map from a finite graded
free module `E`:

* bounded-below graded Nakayama makes the map surjective because its image spans the retract modulo
  `A₊`;
* categorical projectivity of the retract splits the surjection homogeneously, making its kernel a
  bounded-below graded retract of `E`;
* linear independence of the chosen `k`-bases forces the kernel into `A₊ E` and hence `A₊ K`, so a
  second application of bounded-below graded Nakayama proves injectivity.

In coordinate form on `(J → A)`, any degree-zero idempotent endomorphism factors through
`(Fin n → A)` via homogeneous `A`-linear inclusion and projection maps, and its image
`LinearMap.range p` admits a finite `A`-basis of homogeneous vectors.

## Main results

* `TauCeti.GradedModuleCat.idempotentRetract`: the graded retraction of `P` onto
  `kernelObj (𝟙 P - e)` associated with an idempotent `e : P ⟶ P`.
* `TauCeti.GradedModuleCat.free_mem_positive_smul_top_iff`: a degree-`p` element of `free 𝒜 s`
  lies in `A₊ (free 𝒜 s)` if and only if its coordinates at summands of shift `p` vanish.
* `TauCeti.GradedModuleCat.exists_free_retract_of_idempotent`: any graded idempotent on a finite
  graded free module splits through a `Fin n`-indexed graded free module.
* `TauCeti.GradedModuleCat.exists_fin_free_retract_of_idempotent`: the `ULift`-free specialization
  when the source index type lives in `Type`.
* `TauCeti.GradedModuleCat.exists_iso_fin_free_of_retract`: any graded retract of a finite graded
  free module is graded-isomorphic to `free 𝒜 d` and to a finite biproduct of shifts of `regular`.
* `TauCeti.GradedModuleCat.exists_homogeneous_matrix_retract_of_idempotent`: coordinate splitting
  of a degree-zero idempotent on `(J → A)` into homogeneous `A`-linear maps through `(Fin n → A)`.
* `TauCeti.GradedModuleCat.exists_homogeneous_basis_range_idempotent`: the image of a degree-zero
  idempotent on `(J → A)` has a finite `A`-basis with homogeneous coordinates.
* `TauCeti.GradedModuleCat.rank_one_homogeneous_basis_eq`: over a nonnegatively graded commutative
  algebra, a submodule of `(J → A)` spanned by a nonzero homogeneous vector of degree `d₀` has
  every `Fin n`-indexed homogeneous basis of length `1` and degree `d₀`.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded
  projectives and bounded-below graded Nakayama arguments.
* L.-H. Robert and E. Wagner, *Symmetric Khovanov-Rozansky link homologies*, J. Éc. polytech.
  Math. 7 (2020), Theorem 3.30, for the integral graded retract splitting over symmetric
  polynomials.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

namespace TauCeti.GradedModuleCat

universe uk uA v uI uJ

section IdempotentRetract

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

/-- The graded retraction onto the fixed-point object `kernelObj (𝟙 P - e)` of a graded
idempotent `e : P ⟶ P`. -/
def idempotentRetract {P : GradedModuleCat.{v} 𝒜} {e : P ⟶ P} (he : e ≫ e = e) :
    P ⟶ kernelObj (𝟙 P - e) :=
  (kernelIsLimit (𝟙 P - e)).lift <|
    KernelFork.ofι e (by rw [Preadditive.comp_sub, Category.comp_id, he, sub_self])

/-- Composing the idempotent retraction with the kernel inclusion recovers `e`. -/
@[reassoc (attr := simp)]
theorem idempotentRetract_comp_kernelι {P : GradedModuleCat.{v} 𝒜} {e : P ⟶ P}
    (he : e ≫ e = e) :
    idempotentRetract he ≫ kernelι (𝟙 P - e) = e :=
  (kernelIsLimit (𝟙 P - e)).fac _ WalkingParallelPair.zero

/-- The kernel inclusion is a section of `idempotentRetract`. -/
@[reassoc (attr := simp)]
theorem kernelι_comp_idempotentRetract {P : GradedModuleCat.{v} 𝒜} {e : P ⟶ P}
    (he : e ≫ e = e) :
    kernelι (𝟙 P - e) ≫ idempotentRetract he = 𝟙 (kernelObj (𝟙 P - e)) := by
  have : Mono (kernelι (𝟙 P - e)) := (mono_iff_injective _).mpr Subtype.val_injective
  rw [← cancel_mono (kernelι (𝟙 P - e)), Category.assoc, idempotentRetract_comp_kernelι,
    Category.id_comp]
  calc
    kernelι (𝟙 P - e) ≫ e = kernelι (𝟙 P - e) - kernelι (𝟙 P - e) ≫ (𝟙 P - e) := by
      rw [Preadditive.comp_sub, Category.comp_id, sub_sub_cancel]
    _ = kernelι (𝟙 P - e) := by rw [kernelι_comp, sub_zero]

/-- Evaluating `idempotentRetract he` in the ambient module applies `e`. -/
@[simp]
theorem coe_hom_idempotentRetract_apply {P : GradedModuleCat.{v} 𝒜} {e : P ⟶ P}
    (he : e ≫ e = e) (x : P) :
    dsimp% only [hom_sub, hom_id] ((idempotentRetract he).hom x : P) = e.hom x :=
  LinearMap.congr_fun (congr_arg Hom.hom (idempotentRetract_comp_kernelι he)) x

/-- Vanishing of a homogeneous piece of the source implies vanishing of the same piece of any
graded kernel. -/
theorem kernelObj_piece_eq_bot_of_piece_eq_bot {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N)
    {p : ℤ} (hM : M.grading.piece p = ⊥) :
    (kernelObj f).grading.piece p = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun z hz ↦ Subtype.ext ?_
  exact (Submodule.eq_bot_iff _).mp hM z.1 ((InternalGrading.mem_ker_piece _ _).mp hz)

/-- Along a graded retraction `i ≫ r = 𝟙 M`, an element of `M` whose image in `P` lies in `A₊ P`
already lies in `A₊ M`. -/
theorem mem_positive_smul_top_of_retract {M P : GradedModuleCat.{v} 𝒜}
    (i : M ⟶ P) (r : P ⟶ M) (hir : i ≫ r = 𝟙 M) {z : M}
    (hz : i.hom z ∈ (⨆ (d : ℤ) (_ : 0 < d), 𝒜 d) • (⊤ : Submodule k P)) :
    z ∈ (⨆ (d : ℤ) (_ : 0 < d), 𝒜 d) • (⊤ : Submodule k M) := by
  have hmap : ∀ y ∈ (⨆ (d : ℤ) (_ : 0 < d), 𝒜 d) • (⊤ : Submodule k P),
      r.hom y ∈ (⨆ (d : ℤ) (_ : 0 < d), 𝒜 d) • (⊤ : Submodule k M) := fun _ hy ↦
    Submodule.smul_induction_on hy
      (fun a ha y _ ↦ by
        rw [r.hom.map_smul]
        exact Submodule.smul_mem_smul ha Submodule.mem_top)
      (fun _ _ hx hy ↦ by
        rw [map_add]
        exact add_mem hx hy)
  have hri : r.hom (i.hom z) = z := by
    simpa using LinearMap.congr_fun (congr_arg Hom.hom hir) z
  exact hri ▸ hmap _ hz

end IdempotentRetract

section FreeHead

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

/-- Over a nonnegatively graded algebra, a graded free module whose shifts are bounded below by `b`
vanishes in degrees strictly below `b`. -/
theorem free_piece_eq_bot_of_lt {J : Type uJ} (s : J → ℤ) (hneg : ∀ i < 0, 𝒜 i = ⊥)
    {b : ℤ} (hb : ∀ j, b ≤ s j) {p : ℤ} (hp : p < b) :
    (free 𝒜 s).grading.piece p = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun x hx ↦ DFinsupp.ext fun j ↦ ?_
  have hxj : x j ∈ 𝒜 (p - s j) := (mem_free_piece_iff 𝒜 s p x).mp hx j
  have hlt : p - s j < 0 := by have := hb j; omega
  rwa [hneg _ hlt, Submodule.mem_bot] at hxj

/-- Over a nonnegatively graded algebra, every finite graded free module is bounded below. -/
theorem exists_free_piece_eq_bot_of_lt {J : Type uJ} [Finite J] (s : J → ℤ)
    (hneg : ∀ i < 0, 𝒜 i = ⊥) :
    ∃ b : ℤ, ∀ p < b, (free 𝒜 s).grading.piece p = ⊥ := by
  cases nonempty_fintype J
  by_cases hJ : (Finset.univ : Finset J).Nonempty
  · refine ⟨Finset.univ.inf' hJ s, fun p hp ↦ free_piece_eq_bot_of_lt 𝒜 s hneg ?_ hp⟩
    exact fun j ↦ Finset.inf'_le s (Finset.mem_univ j)
  · rw [Finset.not_nonempty_iff_eq_empty] at hJ
    refine ⟨0, fun p hp ↦ free_piece_eq_bot_of_lt 𝒜 s hneg ?_ hp⟩
    exact fun j ↦ False.elim (Finset.notMem_empty j (hJ ▸ Finset.mem_univ j))

/-- Over a nonnegatively graded algebra, a degree-`p` element of `free 𝒜 s` lies in the
positive-degree submodule `A₊ (free 𝒜 s)` if and only if its coordinates vanish at every summand
of shift `p`. -/
theorem free_mem_positive_smul_top_iff {J : Type uJ} (s : J → ℤ) (hneg : ∀ i < 0, 𝒜 i = ⊥)
    {p : ℤ} {x : free 𝒜 s} (hx : x ∈ (free 𝒜 s).grading.piece p) :
    x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (free 𝒜 s)) ↔
      ∀ j, s j = p → x j = 0 := by
  let _ := (free 𝒜 s).gradedSMul
  constructor
  · intro hxI j hsj
    have hdec := InternalGrading.decompose_mem_span_of_mem_positive_smul_top
      (G := (free 𝒜 s).grading) 𝒜 hxI p
    rw [DirectSum.decompose_of_mem_same _ hx] at hdec
    refine (Submodule.span_le (p := LinearMap.ker (DirectSum.component k J (fun _ ↦ A) j))).mpr
      ?_ hdec
    rintro _ ⟨i, hi, a, -, y, hy, rfl⟩
    have hyj : y j ∈ 𝒜 (p - i - s j) := (mem_free_piece_iff 𝒜 s (p - i) y).mp hy j
    have hlt : p - i - s j < 0 := by omega
    rw [hneg _ hlt, Submodule.mem_bot] at hyj
    exact LinearMap.mem_ker.mpr ((DFinsupp.smul_apply a y j).trans (by rw [hyj, smul_zero]))
  · intro h
    classical
    rw [← DirectSum.sum_support_of x]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    have hlof : DirectSum.of (fun _ : J ↦ A) j (x j) =
        (x j) • freeGenerator (𝒜 := 𝒜) (d := s) j := by
      rw [freeGenerator_eq_lof, ← map_smul, smul_eq_mul, mul_one, DirectSum.lof_eq_of]
    rw [hlof]
    have hxj : x j ∈ 𝒜 (p - s j) := (mem_free_piece_iff 𝒜 s p x).mp hx j
    rcases lt_trichotomy (s j) p with hlt | heq | hgt
    · exact Submodule.smul_mem_smul
        (Submodule.mem_iSup_of_mem (p - s j) (Submodule.mem_iSup_of_mem (by omega) hxj))
        Submodule.mem_top
    · simp [h j heq]
    · have h0 : x j = 0 := by rwa [hneg _ (by omega), Submodule.mem_bot] at hxj
      simp [h0]

section ScalarGradeZero

variable [FaithfulSMul k A]

/-- When `𝒜 0 ≤ 1` and `k` acts faithfully on `A`, the algebra map identifies `k` `k`-linearly
with the degree-zero piece `𝒜 0`. -/
private def gradeZeroEquiv (h₀ : 𝒜 0 ≤ 1) : k ≃ₗ[k] 𝒜 0 :=
  (LinearEquiv.ofInjective (Algebra.linearMap k A) (FaithfulSMul.algebraMap_injective k A)).trans <|
    LinearEquiv.ofEq _ _ <|
      Submodule.one_eq_range.symm.trans
        (le_antisymm (Submodule.one_le.mpr (SetLike.one_mem_graded 𝒜)) h₀)

private theorem algebraMap_gradeZeroEquiv_symm (h₀ : 𝒜 0 ≤ 1) (a : 𝒜 0) :
    algebraMap k A ((gradeZeroEquiv 𝒜 h₀).symm a) = (a : A) :=
  congr_arg Subtype.val ((gradeZeroEquiv 𝒜 h₀).apply_symm_apply a)

variable {𝒜}

omit [GradedAlgebra 𝒜] [FaithfulSMul k A] in
private theorem map_u_mem {I : Type*} {d : I → ℤ} {M N : GradedModuleCat.{v} 𝒜}
    (u : ∀ i, M.grading.piece (d i)) (g : M ⟶ N) {p : ℤ} {i : I} (hi : d i = p) :
    g.hom (u i) ∈ N.grading.piece p := by
  rw [← hi]
  exact map_mem g (u i).2

/-- Projection from the degree-`p` piece of `free 𝒜 s` onto the `k`-coordinates of the summands
of shift `p`. -/
private def freeHeadProj (h₀ : 𝒜 0 ≤ 1) {J : Type uJ} (s : J → ℤ) (p : ℤ) :
    (free 𝒜 s).grading.piece p →ₗ[k] ({j : J // s j = p} → k) where
  toFun x j := (gradeZeroEquiv 𝒜 h₀).symm
    ⟨x.1 j.1, by
      have hxj := (mem_free_piece_iff 𝒜 s p x.1).mp x.2 j.1
      rwa [j.2, sub_self] at hxj⟩
  map_add' x y := funext fun j ↦ by
    rw [Pi.add_apply, ← (gradeZeroEquiv 𝒜 h₀).symm.map_add]
    rfl
  map_smul' c x := funext fun j ↦ by
    rw [RingHom.id_apply, Pi.smul_apply, ← (gradeZeroEquiv 𝒜 h₀).symm.map_smul]
    rfl

private theorem algebraMap_freeHeadProj_apply (h₀ : 𝒜 0 ≤ 1) {J : Type uJ} (s : J → ℤ) (p : ℤ)
    (x : (free 𝒜 s).grading.piece p) (j : {j : J // s j = p}) :
    algebraMap k A (freeHeadProj h₀ s p x j) = x.1 j.1 :=
  algebraMap_gradeZeroEquiv_symm 𝒜 h₀ _

/-- The kernel of `freeHeadProj` is precisely `A₊ (free 𝒜 s)` intersected with the degree-`p`
piece. -/
private theorem freeHeadProj_eq_zero_iff (hneg : ∀ i < 0, 𝒜 i = ⊥) (h₀ : 𝒜 0 ≤ 1)
    {J : Type uJ} (s : J → ℤ) (p : ℤ) (x : (free 𝒜 s).grading.piece p) :
    freeHeadProj h₀ s p x = 0 ↔
      (x : free 𝒜 s) ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (free 𝒜 s)) := by
  rw [free_mem_positive_smul_top_iff 𝒜 s hneg x.2, funext_iff]
  refine ⟨fun h j hsj ↦ ?_, fun h ⟨j, hsj⟩ ↦ ?_⟩
  · rw [← algebraMap_freeHeadProj_apply h₀ s p x ⟨j, hsj⟩, h ⟨j, hsj⟩, Pi.zero_apply, map_zero]
  · apply FaithfulSMul.algebraMap_injective k A
    rw [algebraMap_freeHeadProj_apply, h j hsj, Pi.zero_apply, map_zero]

omit [FaithfulSMul k A] in
private theorem freeLift_comp_hom_eq_sum {I : Type uJ} [Fintype I] {d : I → ℤ}
    {M N : GradedModuleCat.{max uA uJ} 𝒜} (u : ∀ i, M.grading.piece (d i)) (g : M ⟶ N)
    (z : free 𝒜 d) :
    (freeLift u ≫ g).hom z = ∑ i : I, z i • g.hom (u i) := by
  classical
  have hz_sum : z = ∑ i : I, DirectSum.lof A I (fun _ ↦ A) i (z i) := by
    conv_lhs => rw [← DirectSum.sum_support_of z]
    simp_rw [DirectSum.lof_eq_of]
    exact Finset.sum_subset (Finset.subset_univ _) fun i _ hi ↦ by
      rw [DFinsupp.notMem_support_iff.mp hi, map_zero]
  conv_lhs => rw [hz_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hom_comp, LinearMap.comp_apply, freeLift_lof, map_smul]

/-- On a finite graded free source `free 𝒜 d`, `freeHeadProj` converts `freeLift u ≫ g` in
degree `p` into a `k`-linear combination over the basis indices with `d i = p`. -/
private theorem freeHeadProj_freeLift_comp (hneg : ∀ i < 0, 𝒜 i = ⊥) (h₀ : 𝒜 0 ≤ 1)
    {I : Type uJ} [Finite I] {d : I → ℤ} {J : Type uJ} {s : J → ℤ}
    {M : GradedModuleCat.{max uA uJ} 𝒜} (u : ∀ i, M.grading.piece (d i))
    (g : M ⟶ free 𝒜 s) (p : ℤ) (z : (free 𝒜 d).grading.piece p) :
    freeHeadProj h₀ s p ⟨(freeLift u ≫ g).hom z.1, map_mem (freeLift u ≫ g) z.2⟩ =
      ∑ i ∈ (Fintype.ofFinite {i : I // d i = p}).elems,
        freeHeadProj h₀ d p z i • freeHeadProj h₀ s p ⟨g.hom (u i.1), map_u_mem u g i.2⟩ := by
  classical
  let _ := Fintype.ofFinite I
  let _ := Fintype.ofFinite {i : I // d i = p}
  let _ := (free 𝒜 s).gradedSMul
  have hterm_mem (i : I) : (z.1 i) • g.hom (u i) ∈ (free 𝒜 s).grading.piece p := by
    have hzi : z.1 i ∈ 𝒜 (p - d i) := (mem_free_piece_iff 𝒜 d p z.1).mp z.2 i
    simpa [sub_add_cancel] using
      SetLike.GradedSMul.smul_mem (B := (free 𝒜 s).grading.piece) hzi (map_mem g (u i).2)
  have hmap_sum : (⟨(freeLift u ≫ g).hom z.1, map_mem (freeLift u ≫ g) z.2⟩ :
      (free 𝒜 s).grading.piece p) = ∑ i : I, ⟨(z.1 i) • g.hom (u i), hterm_mem i⟩ :=
    Subtype.ext (by simpa only [Subtype.coe_mk, Submodule.coe_sum] using
      freeLift_comp_hom_eq_sum u g z.1)
  have helem : (Fintype.ofFinite {i : I // d i = p}).elems = Finset.univ := rfl
  rw [helem, hmap_sum, map_sum]
  have hfilter :
      ∑ i : I, freeHeadProj h₀ s p ⟨(z.1 i) • g.hom (u i), hterm_mem i⟩ =
        ∑ i ∈ Finset.univ.filter (fun i : I ↦ d i = p),
          freeHeadProj h₀ s p ⟨(z.1 i) • g.hom (u i), hterm_mem i⟩ := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun i _ hi ↦ ?_
    have hzi : z.1 i ∈ 𝒜 (p - d i) := (mem_free_piece_iff 𝒜 d p z.1).mp z.2 i
    rcases lt_or_gt_of_ne (by simpa using hi : d i ≠ p) with hlt | hgt
    · exact (freeHeadProj_eq_zero_iff hneg h₀ s p _).mpr <| Submodule.smul_mem_smul
        (Submodule.mem_iSup_of_mem (p - d i) (Submodule.mem_iSup_of_mem (by omega) hzi))
        Submodule.mem_top
    · have hz0 : z.1 i = 0 := by rwa [hneg _ (by omega), Submodule.mem_bot] at hzi
      have hsub : (⟨(z.1 i) • g.hom (u i), hterm_mem i⟩ : (free 𝒜 s).grading.piece p) = 0 :=
        Subtype.ext (by simp [hz0])
      rw [hsub, map_zero]
  rw [hfilter, Finset.sum_subtype (p := fun i ↦ d i = p) _ (fun _ ↦ by simp)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hsmul : (⟨(z.1 i.1) • g.hom (u i.1), hterm_mem i.1⟩ : (free 𝒜 s).grading.piece p) =
      freeHeadProj h₀ d p z i • ⟨g.hom (u i.1), map_u_mem u g i.2⟩ :=
    Subtype.ext (by rw [Subtype.coe_mk, ← algebraMap_freeHeadProj_apply h₀ d p z i,
      algebraMap_smul, SetLike.val_smul])
  rw [hsmul, map_smul]

/-- If the homogeneous lifts `u` span the degree-`p` head of a bounded-below retract `M` of
`free 𝒜 s` in every degree `p`, then `freeLift u : free 𝒜 d ⟶ M` is surjective. -/
private theorem freeLift_surjective_of_head_span (hneg : ∀ i < 0, 𝒜 i = ⊥) (h₀ : 𝒜 0 ≤ 1)
    {I : Type uJ} {d : I → ℤ} {J : Type uJ} [Finite J] {s : J → ℤ}
    {M : GradedModuleCat.{max uA uJ} 𝒜} (iM : M ⟶ free 𝒜 s) (rM : free 𝒜 s ⟶ M)
    (hir : iM ≫ rM = 𝟙 M) (u : ∀ i, M.grading.piece (d i))
    (hspan : ∀ (p : ℤ) (x : M.grading.piece p),
      ∃ y ∈ LinearMap.range (freeLift u).hom, ∃ hy : y ∈ M.grading.piece p,
        freeHeadProj h₀ s p ⟨iM.hom y, map_mem iM hy⟩ =
          freeHeadProj h₀ s p ⟨iM.hom x.1, map_mem iM x.2⟩) :
    Function.Surjective (freeLift u).hom := by
  rw [← LinearMap.range_eq_top]
  obtain ⟨b, hb⟩ := exists_free_piece_eq_bot_of_lt 𝒜 s hneg
  have hbelow : ∀ p < b, M.grading.piece p = ⊥ := fun p hp ↦ by
    refine (Submodule.eq_bot_iff _).mpr fun x hx ↦ ?_
    have hx0 : iM.hom x = 0 := (Submodule.eq_bot_iff _).mp (hb p hp) _ (map_mem iM hx)
    have hri : rM.hom (iM.hom x) = x := by
      simpa using LinearMap.congr_fun (congr_arg Hom.hom hir) x
    rw [← hri, hx0, map_zero]
  refine InternalGrading.eq_top_of_piece_le_sup_positive_smul_top 𝒜
    (LinearMap.range (freeLift u).hom) (freeLift u).isHomogeneous.isHomogeneous_range b hbelow
    fun p x hx ↦ ?_
  obtain ⟨y, hyR, hyP, hhead⟩ := hspan p ⟨x, hx⟩
  have hdecomp : x = y + (x - y) := by abel
  rw [hdecomp]
  refine Submodule.add_mem_sup hyR (mem_positive_smul_top_of_retract iM rM hir ?_)
  have hxy : iM.hom (x - y) ∈ (free 𝒜 s).grading.piece p :=
    map_mem iM ((M.grading.piece p).sub_mem hx hyP)
  refine (freeHeadProj_eq_zero_iff hneg h₀ s p ⟨iM.hom (x - y), hxy⟩).mp ?_
  have hsub : (⟨iM.hom (x - y), hxy⟩ : (free 𝒜 s).grading.piece p) =
      ⟨iM.hom x, map_mem iM hx⟩ - ⟨iM.hom y, map_mem iM hyP⟩ :=
    Subtype.ext (map_sub iM.hom x y)
  rw [hsub, map_sub, hhead, sub_self]

/-- If `freeLift u : free 𝒜 d ⟶ M` onto a projective graded module `M` is surjective and the
head images of `u` in each degree `p` are `k`-linearly independent, then `(freeLift u).hom` is
injective. -/
private theorem freeLift_injective_of_head_linearIndependent (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (h₀ : 𝒜 0 ≤ 1) {I : Type uJ} [Finite I] {d : I → ℤ} {J : Type uJ} {s : J → ℤ}
    {M : GradedModuleCat.{max uA uJ} 𝒜} [Projective M] (iM : M ⟶ free 𝒜 s)
    (u : ∀ i, M.grading.piece (d i)) (hsurj : Function.Surjective (freeLift u).hom)
    (hli : ∀ p : ℤ, LinearIndependent k fun i : {i : I // d i = p} ↦
      freeHeadProj h₀ s p ⟨iM.hom (u i.1), map_u_mem u iM i.2⟩) :
    Function.Injective (freeLift u).hom := by
  let φ : free 𝒜 d ⟶ M := freeLift u
  let _ := (kernelObj φ).gradedSMul
  have : Epi φ := (epi_iff_surjective φ).mpr hsurj
  let ψ : M ⟶ free 𝒜 d := Projective.factorThru (𝟙 M) φ
  have hψφ : ψ ≫ φ = 𝟙 M := Projective.factorThru_comp (𝟙 M) φ
  let rK : free 𝒜 d ⟶ kernelObj φ :=
    (kernelIsLimit φ).lift <| KernelFork.ofι (𝟙 (free 𝒜 d) - φ ≫ ψ) <| by
      rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hψφ, Category.comp_id, sub_self]
  have hfac : rK ≫ kernelι φ = 𝟙 (free 𝒜 d) - φ ≫ ψ :=
    (kernelIsLimit φ).fac _ WalkingParallelPair.zero
  have hirK : kernelι φ ≫ rK = 𝟙 (kernelObj φ) := by
    have : Mono (kernelι φ) := (mono_iff_injective _).mpr Subtype.val_injective
    rw [← cancel_mono (kernelι φ), Category.assoc, hfac, Category.id_comp,
      Preadditive.comp_sub, Category.comp_id, ← Category.assoc, kernelι_comp, zero_comp, sub_zero]
  obtain ⟨b, hb⟩ := exists_free_piece_eq_bot_of_lt 𝒜 d hneg
  have hK_below : ∀ p < b, (kernelObj φ).grading.piece p = ⊥ :=
    fun p hp ↦ kernelObj_piece_eq_bot_of_piece_eq_bot φ (hb p hp)
  have hK_pos : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (kernelObj φ)) = ⊤ := by
    refine top_unique fun z _ ↦ ?_
    classical
    rw [← DirectSum.sum_support_decompose (kernelObj φ).grading.piece z]
    refine Submodule.sum_mem _ fun p _ ↦ ?_
    set zp := DirectSum.decompose (kernelObj φ).grading.piece z p
    refine mem_positive_smul_top_of_retract (kernelι φ) rK hirK ?_
    have hzpE : zp.1.1 ∈ (free 𝒜 d).grading.piece p :=
      (InternalGrading.mem_ker_piece _ _).mp zp.2
    refine (freeHeadProj_eq_zero_iff hneg h₀ d p ⟨zp.1.1, hzpE⟩).mp ?_
    have hzero_img : (freeLift u ≫ iM).hom zp.1.1 = 0 := by
      rw [hom_comp, LinearMap.comp_apply, LinearMap.mem_ker.mp zp.1.2, map_zero]
    have hsub0 : (⟨(freeLift u ≫ iM).hom zp.1.1, map_mem (freeLift u ≫ iM) hzpE⟩ :
        (free 𝒜 s).grading.piece p) = 0 := Subtype.ext hzero_img
    have hsum0 := (freeHeadProj_freeLift_comp hneg h₀ u iM p ⟨zp.1.1, hzpE⟩).symm.trans
      (by rw [hsub0, map_zero])
    exact funext fun i ↦
      linearIndependent_iff'.mp (hli p) (Fintype.ofFinite _).elems _ hsum0 i
        ((Fintype.ofFinite _).complete i)
  have : Subsingleton (kernelObj φ) :=
    InternalGrading.subsingleton_of_positive_smul_top_eq_top
      (G := (kernelObj φ).grading) 𝒜 b hK_below hK_pos
  exact LinearMap.ker_eq_bot.mp <| (Submodule.eq_bot_iff _).mpr fun x hx ↦
    congr_arg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : kernelObj φ) 0)

end ScalarGradeZero

/-! ### Splitting graded idempotents on finite graded free modules -/

section RetractSplitting

variable [IsDomain k] [IsPrincipalIdealRing k] [FaithfulSMul k A]

omit [CommRing k] [Ring A] [Algebra k A] [GradedAlgebra 𝒜] [IsDomain k]
  [IsPrincipalIdealRing k] [FaithfulSMul k A] in
/-- For a reindexing `eIdx : Fin n ≃ Σ p : S, Fin (r p)` and `d' i = (eIdx i.down).1.1`, the fiber
`{i : ULift (Fin n) // d' i = p}` at `p ∈ S` is equivalent to `Fin (r p)`. -/
private def fiberEquivFin {S : Finset ℤ} {r : ℤ → ℕ} {n : ℕ}
    (eIdx : Fin n ≃ Σ p : S, Fin (r p.1)) {p : ℤ} (hp : p ∈ S) :
    {i : ULift.{uJ} (Fin n) // (eIdx i.down).1.1 = p} ≃ Fin (r p) where
  toFun i := Fin.cast (congr_arg r i.2) (eIdx i.1.down).2
  invFun t := ⟨ULift.up (eIdx.symm ⟨⟨p, hp⟩, t⟩), by simp⟩
  left_inv := fun ⟨⟨i⟩, hi⟩ ↦ Subtype.ext <| congr_arg ULift.up <| eIdx.injective <| by
    rw [Equiv.apply_symm_apply]
    rcases h : eIdx i with ⟨⟨q, hq⟩, t⟩
    have hqp : q = p := by simpa [h] using hi
    subst hqp
    have hhq : hq = hp := Subsingleton.elim _ _
    subst hhq
    ext
    · rfl
    · refine heq_of_eq (Fin.ext ?_)
      rw [Fin.val_cast]
      exact congr_arg (fun z : Σ p : S, Fin (r p.1) ↦ (z.2 : ℕ)) h
  right_inv t := by
    ext
    rw [Fin.val_cast, Equiv.apply_symm_apply]

omit [IsDomain k] [IsPrincipalIdealRing k] in
/-- The `k`-linear map sending a degree-`p` element of `M` to the shift-`p` head coordinates of its
image under `iM : M ⟶ free 𝒜 s`. -/
private def retractHeadProj (h₀ : 𝒜 0 ≤ 1) {J : Type uJ} (s : J → ℤ)
    {M : GradedModuleCat.{max uA uJ} 𝒜} (iM : M ⟶ free 𝒜 s) (p : ℤ) :
    M.grading.piece p →ₗ[k] ({j : J // s j = p} → k) :=
  (freeHeadProj h₀ s p).comp <|
    ((iM.hom.restrictScalars k).domRestrict (M.grading.piece p)).codRestrict
      ((free 𝒜 s).grading.piece p) fun x ↦ map_mem iM x.2

omit [IsDomain k] [IsPrincipalIdealRing k] in
@[simp]
private theorem retractHeadProj_apply (h₀ : 𝒜 0 ≤ 1) {J : Type uJ} (s : J → ℤ)
    {M : GradedModuleCat.{max uA uJ} 𝒜} (iM : M ⟶ free 𝒜 s) (p : ℤ)
    (x : M.grading.piece p) :
    retractHeadProj 𝒜 h₀ s iM p x = freeHeadProj h₀ s p ⟨iM.hom x.1, map_mem iM x.2⟩ :=
  rfl

omit [IsDomain k] [IsPrincipalIdealRing k] in
private theorem head_span_of_sigma_basis (h₀ : 𝒜 0 ≤ 1) {J : Type uJ} [Fintype J] (s : J → ℤ)
    {M : GradedModuleCat.{max uA uJ} 𝒜} (iM : M ⟶ free 𝒜 s)
    (bPid : ∀ p : ℤ,
      Σ r : ℕ, Module.Basis (Fin r) k (LinearMap.range (retractHeadProj 𝒜 h₀ s iM p)))
    {n : ℕ} (eIdx : Fin n ≃ Σ p : Finset.univ.image s, Fin (bPid p.1).1)
    (u₀ : ∀ idx : (Σ p : Finset.univ.image s, Fin (bPid p.1).1), M.grading.piece idx.1.1)
    (hu₀ : ∀ idx, retractHeadProj 𝒜 h₀ s iM idx.1.1 (u₀ idx) = ((bPid idx.1.1).2 idx.2).1)
    (p : ℤ) (x : M.grading.piece p) :
    let u : ∀ i : ULift.{uJ} (Fin n), M.grading.piece (((fun i ↦ (eIdx i).1.1) ∘ ULift.down) i) :=
      fun i ↦ u₀ (eIdx i.down)
    ∃ y ∈ LinearMap.range (freeLift u).hom, ∃ hy : y ∈ M.grading.piece p,
      freeHeadProj h₀ s p ⟨iM.hom y, map_mem iM hy⟩ =
        freeHeadProj h₀ s p ⟨iM.hom x.1, map_mem iM x.2⟩ := by
  classical
  intro u
  by_cases hp : p ∈ Finset.univ.image s
  · let c := (bPid p).2.repr ⟨retractHeadProj 𝒜 h₀ s iM p x, ⟨x, rfl⟩⟩
    let y : M := ∑ t : Fin (bPid p).1, c t • (u₀ ⟨⟨p, hp⟩, t⟩ : M)
    have hyP : y ∈ M.grading.piece p :=
      (M.grading.piece p).sum_mem fun t _ ↦ (M.grading.piece p).smul_mem (c t) (u₀ ⟨⟨p, hp⟩, t⟩).2
    have hyR : y ∈ LinearMap.range (freeLift u).hom := Submodule.sum_mem _ fun t _ ↦ by
      rw [← algebraMap_smul A]
      exact Submodule.smul_mem _ _ ⟨freeGenerator (ULift.up (eIdx.symm ⟨⟨p, hp⟩, t⟩)), by
        rw [freeLift_generator]
        exact congr_arg (fun z ↦ (u₀ z : M)) (eIdx.apply_symm_apply ⟨⟨p, hp⟩, t⟩)⟩
    have hy_sub : (⟨y, hyP⟩ : M.grading.piece p) =
        ∑ t : Fin (bPid p).1, c t • u₀ ⟨⟨p, hp⟩, t⟩ :=
      Subtype.ext (by simp [y])
    have hval :=
      congr_arg Subtype.val ((bPid p).2.sum_repr ⟨retractHeadProj 𝒜 h₀ s iM p x, ⟨x, rfl⟩⟩)
    refine ⟨y, hyR, hyP, ?_⟩
    rw [← retractHeadProj_apply 𝒜 h₀ s iM p ⟨y, hyP⟩, ← retractHeadProj_apply 𝒜 h₀ s iM p x,
      hy_sub, map_sum]
    refine (Finset.sum_congr rfl fun t _ ↦ ?_).trans
      (by simpa only [Submodule.coe_sum, SetLike.val_smul] using hval)
    rw [map_smul, hu₀ ⟨⟨p, hp⟩, t⟩]
  · refine ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, ?_⟩
    ext ⟨j, rfl⟩
    exact False.elim (hp (Finset.mem_image_of_mem s (Finset.mem_univ j)))

omit [IsDomain k] [IsPrincipalIdealRing k] in
private theorem head_linearIndependent_of_sigma_basis (h₀ : 𝒜 0 ≤ 1) {J : Type uJ} [Fintype J]
    (s : J → ℤ) {M : GradedModuleCat.{max uA uJ} 𝒜} (iM : M ⟶ free 𝒜 s)
    (bPid : ∀ p : ℤ,
      Σ r : ℕ, Module.Basis (Fin r) k (LinearMap.range (retractHeadProj 𝒜 h₀ s iM p)))
    {n : ℕ} (eIdx : Fin n ≃ Σ p : Finset.univ.image s, Fin (bPid p.1).1)
    (u₀ : ∀ idx : (Σ p : Finset.univ.image s, Fin (bPid p.1).1), M.grading.piece idx.1.1)
    (hu₀ : ∀ idx, retractHeadProj 𝒜 h₀ s iM idx.1.1 (u₀ idx) = ((bPid idx.1.1).2 idx.2).1)
    (p : ℤ) :
    let d : Fin n → ℤ := fun i ↦ (eIdx i).1.1
    let u : ∀ i : ULift.{uJ} (Fin n), M.grading.piece ((d ∘ ULift.down) i) :=
      fun i ↦ u₀ (eIdx i.down)
    LinearIndependent k fun i : {i : ULift.{uJ} (Fin n) // (d ∘ ULift.down) i = p} ↦
      freeHeadProj h₀ s p ⟨iM.hom (u i.1), map_u_mem u iM i.2⟩ := by
  classical
  intro d u
  by_cases hp : p ∈ Finset.univ.image s
  · let eqv := fiberEquivFin.{uJ} (r := fun q ↦ (bPid q).1) eIdx hp
    have hidx : ∀ (idx : Σ p : Finset.univ.image s, Fin (bPid p.1).1) (h : idx.1.1 = p),
        freeHeadProj h₀ s p ⟨iM.hom (u₀ idx).1,
            map_u_mem (d := fun z : Σ p : Finset.univ.image s, Fin (bPid p.1).1 ↦ z.1.1)
              u₀ iM h⟩ =
          ((bPid p).2 (Fin.cast (congr_arg (fun q ↦ (bPid q).1) h) idx.2)).1 := by
      rintro ⟨⟨q, hq⟩, t⟩ rfl
      exact hu₀ ⟨⟨q, hq⟩, t⟩
    have hcomp : (fun i : {i : ULift.{uJ} (Fin n) // (d ∘ ULift.down) i = p} ↦
        freeHeadProj h₀ s p ⟨iM.hom (u i.1), map_u_mem u iM i.2⟩) =
        (fun t : Fin (bPid p).1 ↦ ((bPid p).2 t : {j : J // s j = p} → k)) ∘ eqv := by
      ext ⟨⟨i⟩, hi⟩
      exact congr_fun (hidx (eIdx i) hi) _
    rw [hcomp]
    exact (((bPid p).2.linearIndependent).map' (Submodule.subtype _)
      (Submodule.ker_subtype _)).comp eqv eqv.injective
  · have : IsEmpty {i : ULift.{uJ} (Fin n) // (d ∘ ULift.down) i = p} :=
      ⟨fun ⟨i, hi⟩ ↦ hp (hi ▸ (eIdx i.down).1.2)⟩
    exact linearIndependent_empty_type

/-- Given a projective graded retract `M` of a finite graded free module `free 𝒜 s`, lifting
degreewise `k`-bases of its head images produces a bijective graded map `free 𝒜 d' ⟶ M`. -/
private theorem exists_bijective_freeLift_of_retract (hneg : ∀ i < 0, 𝒜 i = ⊥) (h₀ : 𝒜 0 ≤ 1)
    {J : Type uJ} [Finite J] (s : J → ℤ) {M : GradedModuleCat.{max uA uJ} 𝒜}
    [Projective M] (iM : M ⟶ free 𝒜 s) (rM : free 𝒜 s ⟶ M) (hirM : iM ≫ rM = 𝟙 M) :
    ∃ (n : ℕ) (d : Fin n → ℤ) (φ : free 𝒜 (d ∘ ULift.down) ⟶ M),
      Function.Bijective φ.hom := by
  classical
  cases nonempty_fintype J
  let bPid (p : ℤ) :
      Σ r : ℕ, Module.Basis (Fin r) k (LinearMap.range (retractHeadProj 𝒜 h₀ s iM p)) :=
    Submodule.basisOfPid (Pi.basisFun k {j : J // s j = p})
      (LinearMap.range (retractHeadProj 𝒜 h₀ s iM p))
  let Idx : Type := Σ p : Finset.univ.image s, Fin (bPid p.1).1
  let eIdx : Fin (Fintype.card Idx) ≃ Idx := (Fintype.equivFin Idx).symm
  choose u₀ hu₀ using fun idx : Idx ↦ ((bPid idx.1.1).2 idx.2).2
  let d : Fin (Fintype.card Idx) → ℤ := fun i ↦ (eIdx i).1.1
  let u : ∀ i : ULift.{uJ} (Fin (Fintype.card Idx)), M.grading.piece ((d ∘ ULift.down) i) :=
    fun i ↦ u₀ (eIdx i.down)
  have hsurj : Function.Surjective (freeLift u).hom :=
    freeLift_surjective_of_head_span hneg h₀ iM rM hirM u
      (head_span_of_sigma_basis 𝒜 h₀ s iM bPid eIdx u₀ hu₀)
  have hinj : Function.Injective (freeLift u).hom :=
    freeLift_injective_of_head_linearIndependent hneg h₀ iM u hsurj
      (head_linearIndependent_of_sigma_basis 𝒜 h₀ s iM bPid eIdx u₀ hu₀)
  exact ⟨Fintype.card Idx, d, freeLift u, hinj, hsurj⟩

/-- **Graded retract freeness.** Over a nonnegatively `ℤ`-graded `k`-algebra `A` whose degree-zero
piece consists of scalars from a principal ideal domain `k` acting faithfully on `A`, every graded
idempotent `e` on a finite graded free module `free 𝒜 s` splits through a `Fin n`-indexed graded
free module `free 𝒜 (d ∘ ULift.down)`. -/
theorem exists_free_retract_of_idempotent (hneg : ∀ i < 0, 𝒜 i = ⊥) (h₀ : 𝒜 0 ≤ 1)
    {J : Type uJ} [Finite J] (s : J → ℤ) (e : free 𝒜 s ⟶ free 𝒜 s) (he : e ≫ e = e) :
    ∃ (n : ℕ) (d : Fin n → ℤ)
      (ι : free 𝒜 (d ∘ ULift.down) ⟶ free 𝒜 s)
      (π : free 𝒜 s ⟶ free 𝒜 (d ∘ ULift.down)),
      π ≫ ι = e ∧ ι ≫ π = 𝟙 (free 𝒜 (d ∘ ULift.down)) := by
  let M : GradedModuleCat.{max uA uJ} 𝒜 := kernelObj (𝟙 (free 𝒜 s) - e)
  let iM : M ⟶ free 𝒜 s := kernelι (𝟙 (free 𝒜 s) - e)
  let rM : free 𝒜 s ⟶ M := idempotentRetract he
  have hirM : iM ≫ rM = 𝟙 M := kernelι_comp_idempotentRetract he
  have : Module.Projective A M :=
    Module.Projective.of_split iM.hom rM.hom (congr_arg Hom.hom hirM)
  obtain ⟨n, d, φ, hφ⟩ := exists_bijective_freeLift_of_retract 𝒜 hneg h₀ s iM rM hirM
  have : IsIso φ := (isIso_iff_bijective φ).mpr hφ
  refine ⟨n, d, (asIso φ).hom ≫ iM, rM ≫ (asIso φ).inv, ?_, ?_⟩
  · simp [Category.assoc, rM, iM]
  · simp [Category.assoc, reassoc_of% hirM]

omit [IsDomain k] [IsPrincipalIdealRing k] [FaithfulSMul k A] in
/-- Reindexing a `Fin n`-graded free module along `ULift.up` in `Type` is a graded isomorphism. -/
def freeULiftZeroIso {n : ℕ} (d : Fin n → ℤ) :
    free 𝒜 (d ∘ ULift.down.{0}) ≅ free 𝒜 d where
  hom := freeLift (d := d ∘ ULift.down.{0}) (M := free 𝒜 d)
    fun i ↦ ⟨freeGenerator i.down, freeGenerator_mem_free_piece i.down⟩
  inv := freeLift (d := d) (M := free 𝒜 (d ∘ ULift.down.{0}))
    fun i ↦ ⟨freeGenerator (ULift.up i), freeGenerator_mem_free_piece (ULift.up i)⟩
  hom_inv_id := free_hom_ext fun i ↦ by
    rw [hom_comp, LinearMap.comp_apply, freeLift_generator, freeLift_generator, hom_id,
      LinearMap.id_apply]
  inv_hom_id := free_hom_ext fun i ↦ by
    rw [hom_comp, LinearMap.comp_apply, freeLift_generator, freeLift_generator, hom_id,
      LinearMap.id_apply]

omit [IsDomain k] [IsPrincipalIdealRing k] [FaithfulSMul k A] in
/-- `freeULiftZeroIso` sends the `i`-th generator to `i.down`. -/
@[simp]
theorem freeULiftZeroIso_hom_generator {n : ℕ} (d : Fin n → ℤ) (i : ULift.{0} (Fin n)) :
    dsimp% only ((freeULiftZeroIso 𝒜 d).hom.hom (freeGenerator (𝒜 := 𝒜) i)) =
      freeGenerator (𝒜 := 𝒜) (d := d) i.down :=
  freeLift_generator _ i

omit [IsDomain k] [IsPrincipalIdealRing k] [FaithfulSMul k A] in
/-- The inverse of `freeULiftZeroIso` sends the `i`-th generator to `ULift.up i`. -/
@[simp]
theorem freeULiftZeroIso_inv_generator {n : ℕ} (d : Fin n → ℤ) (i : Fin n) :
    dsimp% only ((freeULiftZeroIso 𝒜 d).inv.hom (freeGenerator (𝒜 := 𝒜) i)) =
      freeGenerator (𝒜 := 𝒜) (d := d ∘ ULift.down.{0}) (ULift.up i) :=
  freeLift_generator _ i

omit [IsDomain k] [IsPrincipalIdealRing k] [FaithfulSMul k A] in
/-- A `Type`-indexed graded free module `free 𝒜 s` with a biproduct of its shifted regular summands
is canonically isomorphic to that categorical biproduct. -/
def freeIsoBiproduct {J : Type} (s : J → ℤ)
    [HasBiproduct fun j : J ↦ (regular (𝒜 := 𝒜)).shiftObj (s j)] :
    free 𝒜 s ≅ ⨁ fun j : J ↦ (regular (𝒜 := 𝒜)).shiftObj (s j) :=
  (coproductCofanIsColimit fun j : J ↦ (regular (𝒜 := 𝒜)).shiftObj (s j)).coconePointUniqueUpToIso
    (biproduct.isColimit _)

omit [IsDomain k] [IsPrincipalIdealRing k] [FaithfulSMul k A] in
/-- Composing the direct-sum injection with `(freeIsoBiproduct 𝒜 s).hom` gives `biproduct.ι`. -/
@[reassoc (attr := simp)]
theorem coproductCofan_inj_comp_freeIsoBiproduct_hom {J : Type} (s : J → ℤ)
    [HasBiproduct fun j : J ↦ (regular (𝒜 := 𝒜)).shiftObj (s j)] (j : J) :
    (coproductCofan fun j : J ↦ (regular (𝒜 := 𝒜)).shiftObj (s j)).inj j ≫
      (freeIsoBiproduct 𝒜 s).hom =
      biproduct.ι (fun j : J ↦ (regular (𝒜 := 𝒜)).shiftObj (s j)) j :=
  (coproductCofanIsColimit _).comp_coconePointUniqueUpToIso_hom (biproduct.isColimit _) ⟨j⟩

omit [IsDomain k] [IsPrincipalIdealRing k] [FaithfulSMul k A] in
/-- Composing `biproduct.ι` with `(freeIsoBiproduct 𝒜 s).inv` gives the direct-sum injection. -/
@[reassoc (attr := simp)]
theorem biproduct_ι_comp_freeIsoBiproduct_inv {J : Type} (s : J → ℤ)
    [HasBiproduct fun j : J ↦ (regular (𝒜 := 𝒜)).shiftObj (s j)] (j : J) :
    biproduct.ι (fun j : J ↦ (regular (𝒜 := 𝒜)).shiftObj (s j)) j ≫
      (freeIsoBiproduct 𝒜 s).inv =
      (coproductCofan fun j : J ↦ (regular (𝒜 := 𝒜)).shiftObj (s j)).inj j :=
  (coproductCofanIsColimit _).comp_coconePointUniqueUpToIso_inv (biproduct.isColimit _) ⟨j⟩

/-- The `ULift`-free form of `exists_free_retract_of_idempotent` when the source index type `J`
lives in `Type`. -/
theorem exists_fin_free_retract_of_idempotent (hneg : ∀ i < 0, 𝒜 i = ⊥) (h₀ : 𝒜 0 ≤ 1)
    {J : Type} [Finite J] (s : J → ℤ) (e : free 𝒜 s ⟶ free 𝒜 s) (he : e ≫ e = e) :
    ∃ (n : ℕ) (d : Fin n → ℤ) (ι : free 𝒜 d ⟶ free 𝒜 s) (π : free 𝒜 s ⟶ free 𝒜 d),
      π ≫ ι = e ∧ ι ≫ π = 𝟙 (free 𝒜 d) := by
  obtain ⟨n, d, ι, π, hπι, hιπ⟩ := exists_free_retract_of_idempotent 𝒜 hneg h₀ s e he
  refine ⟨n, d, (freeULiftZeroIso 𝒜 d).inv ≫ ι, π ≫ (freeULiftZeroIso 𝒜 d).hom, ?_, ?_⟩
  · simp [Category.assoc, Iso.hom_inv_id_assoc, hπι]
  · simp [Category.assoc, reassoc_of% hιπ]

/-- Any graded retract `W` of a `Type`-indexed finite graded free module `free 𝒜 s` is
isomorphic to `free 𝒜 d` for a `Fin n`-tuple of shifts `d`, and therefore splits into `n` shifted
copies of the regular module with explicit summand inclusions and projections satisfying both
biproduct identities. -/
theorem exists_iso_fin_free_of_retract (hneg : ∀ i < 0, 𝒜 i = ⊥) (h₀ : 𝒜 0 ≤ 1)
    {J : Type} [Finite J] (s : J → ℤ) {W : GradedModuleCat.{uA} 𝒜}
    (u : W ⟶ free 𝒜 s) (v : free 𝒜 s ⟶ W) (huv : u ≫ v = 𝟙 W) :
    ∃ (n : ℕ) (d : Fin n → ℤ)
      (ι : ∀ i : Fin n, (regular (𝒜 := 𝒜)).shiftObj (d i) ⟶ W)
      (π : ∀ i : Fin n, W ⟶ (regular (𝒜 := 𝒜)).shiftObj (d i)),
      Nonempty (W ≅ free 𝒜 d) ∧
      (∀ i, ι i ≫ π i = 𝟙 _) ∧
      (∀ i j, i ≠ j → ι i ≫ π j = 0) ∧
      ∑ i : Fin n, π i ≫ ι i = 𝟙 W := by
  have he : (v ≫ u) ≫ (v ≫ u) = v ≫ u := by simp [Category.assoc, reassoc_of% huv]
  obtain ⟨n, d, ιF, πF, hπι, hιπ⟩ :=
    exists_fin_free_retract_of_idempotent 𝒜 hneg h₀ s (v ≫ u) he
  let isoFree : W ≅ free 𝒜 d :=
    { hom := u ≫ πF
      inv := ιF ≫ v
      hom_inv_id := by
        rw [Category.assoc, ← Category.assoc πF, hπι, Category.assoc, huv, Category.comp_id, huv]
      inv_hom_id := by
        calc
          (ιF ≫ v) ≫ (u ≫ πF) = ιF ≫ (v ≫ u) ≫ πF := by simp [Category.assoc]
          _ = ιF ≫ (πF ≫ ιF) ≫ πF := by rw [← hπι]
          _ = (ιF ≫ πF) ≫ (ιF ≫ πF) := by simp [Category.assoc]
          _ = 𝟙 (free 𝒜 d) := by rw [hιπ, Category.id_comp] }
  let F : Fin n → GradedModuleCat.{uA} 𝒜 := fun i ↦ (regular (𝒜 := 𝒜)).shiftObj (d i)
  let _ := HasBiproduct.of_hasCoproduct F
  let isoBiprod : W ≅ ⨁ F := isoFree ≪≫ freeIsoBiproduct 𝒜 d
  refine ⟨n, d, fun i ↦ biproduct.ι F i ≫ isoBiprod.inv,
    fun i ↦ isoBiprod.hom ≫ biproduct.π F i, ⟨isoFree⟩, fun i ↦ ?_, fun i j hij ↦ ?_, ?_⟩
  · simp [F, Category.assoc, Iso.inv_hom_id_assoc]
  · simp [Category.assoc, Iso.inv_hom_id_assoc, biproduct.ι_π_ne _ hij]
  · simp_rw [Category.assoc, ← Category.assoc (biproduct.π F _), ← Preadditive.comp_sum,
      ← Preadditive.sum_comp, biproduct.total, Category.id_comp, Iso.hom_inv_id]

/-! ### Coordinate matrix splittings and homogeneous bases -/

/-- **Homogeneous matrix splitting of a degree-zero idempotent.** On a finite product `(J → A)`
equipped with summand shifts `s : J → ℤ`, every degree-zero `A`-linear idempotent `p` factors as
`ι ∘ₗ π = p` with `π ∘ₗ ι = id` through `(Fin n → A)` for homogeneous `A`-linear maps `ι` and `π`
respecting shifts `d : Fin n → ℤ`. -/
theorem exists_homogeneous_matrix_retract_of_idempotent (hneg : ∀ i < 0, 𝒜 i = ⊥) (h₀ : 𝒜 0 ≤ 1)
    {J : Type uJ} [Finite J] (s : J → ℤ) (p : (J → A) →ₗ[A] (J → A)) (hp : p.comp p = p)
    (hhom : ∀ (q : ℤ) (v : J → A), (∀ j, v j ∈ 𝒜 (q - s j)) → ∀ j, p v j ∈ 𝒜 (q - s j)) :
    ∃ (n : ℕ) (d : Fin n → ℤ)
      (ι : (Fin n → A) →ₗ[A] (J → A)) (π : (J → A) →ₗ[A] (Fin n → A)),
      ι.comp π = p ∧ π.comp ι = LinearMap.id ∧
      (∀ (q : ℤ) (w : Fin n → A), (∀ i, w i ∈ 𝒜 (q - d i)) → ∀ j, ι w j ∈ 𝒜 (q - s j)) ∧
      (∀ (q : ℤ) (v : J → A), (∀ j, v j ∈ 𝒜 (q - s j)) → ∀ i, π v i ∈ 𝒜 (q - d i)) := by
  classical
  cases nonempty_fintype J
  let eqJ : free 𝒜 s ≃ₗ[A] (J → A) := DirectSum.linearEquivFunOnFintype A J (fun _ ↦ A)
  let eHom : free 𝒜 s →ₗ[A] free 𝒜 s := eqJ.symm.toLinearMap ∘ₗ p ∘ₗ eqJ.toLinearMap
  have heHom :
      LinearMap.IsHomogeneous eHom (free 𝒜 s).grading.piece (free 𝒜 s).grading.piece 0 := by
    refine LinearMap.isHomogeneous_def.mpr fun q x hx ↦ ?_
    rw [add_zero]
    exact (mem_free_piece_iff 𝒜 s q _).mpr fun j ↦
      hhom q (eqJ x) (fun j' ↦ (mem_free_piece_iff 𝒜 s q x).mp hx j') j
  let e : free 𝒜 s ⟶ free 𝒜 s := ofHom eHom heHom
  have he : e ≫ e = e := by
    refine hom_ext (LinearMap.ext fun x ↦ ?_)
    have hpp := LinearMap.congr_fun hp (eqJ x)
    simpa [e, eHom] using congr_arg eqJ.symm hpp
  obtain ⟨n, d, ι₀, π₀, hπι₀, hιπ₀⟩ := exists_free_retract_of_idempotent 𝒜 hneg h₀ s e he
  let eqULift : (ULift.{uJ} (Fin n) → A) ≃ₗ[A] (Fin n → A) :=
    { toFun := fun f i ↦ f (ULift.up i)
      invFun := fun g i ↦ g i.down
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let eqFin : free 𝒜 (d ∘ ULift.down) ≃ₗ[A] (Fin n → A) :=
    (DirectSum.linearEquivFunOnFintype A (ULift.{uJ} (Fin n)) (fun _ ↦ A)).trans eqULift
  let ι : (Fin n → A) →ₗ[A] (J → A) := eqJ.toLinearMap ∘ₗ ι₀.hom ∘ₗ eqFin.symm.toLinearMap
  let π : (J → A) →ₗ[A] (Fin n → A) := eqFin.toLinearMap ∘ₗ π₀.hom ∘ₗ eqJ.symm.toLinearMap
  refine ⟨n, d, ι, π, LinearMap.ext fun v ↦ ?_, LinearMap.ext fun w ↦ ?_,
    fun q w hw j ↦ ?_, fun q v hv i ↦ ?_⟩
  · have h1 := LinearMap.congr_fun (congr_arg Hom.hom hπι₀) (eqJ.symm v)
    simpa [ι, π, e, eHom] using congr_arg eqJ h1
  · have h2 := LinearMap.congr_fun (congr_arg Hom.hom hιπ₀) (eqFin.symm w)
    simpa [ι, π] using congr_arg eqFin h2
  · have hmem : eqFin.symm w ∈ (free 𝒜 (d ∘ ULift.down)).grading.piece q :=
      (mem_free_piece_iff 𝒜 (d ∘ ULift.down) q _).mpr fun ⟨i⟩ ↦ hw i
    exact (mem_free_piece_iff 𝒜 s q _).mp (map_mem ι₀ hmem) j
  · have hmem : eqJ.symm v ∈ (free 𝒜 s).grading.piece q :=
      (mem_free_piece_iff 𝒜 s q _).mpr fun j ↦ hv j
    exact (mem_free_piece_iff 𝒜 (d ∘ ULift.down) q _).mp (map_mem π₀ hmem) ⟨i⟩

/-- **Homogeneous basis of a graded idempotent image.** Over a nonnegatively `ℤ`-graded `k`-algebra
`A` whose degree-zero piece consists of scalars from a principal ideal domain `k` acting faithfully
on `A`, the image `LinearMap.range p` of any degree-zero `A`-linear idempotent `p` on `(J → A)` has
a finite `A`-basis whose `i`-th vector has `j`-th coordinate in `𝒜 (d i - s j)`. -/
theorem exists_homogeneous_basis_range_idempotent (hneg : ∀ i < 0, 𝒜 i = ⊥) (h₀ : 𝒜 0 ≤ 1)
    {J : Type uJ} [Finite J] (s : J → ℤ) (p : (J → A) →ₗ[A] (J → A)) (hp : p.comp p = p)
    (hhom : ∀ (q : ℤ) (v : J → A), (∀ j, v j ∈ 𝒜 (q - s j)) → ∀ j, p v j ∈ 𝒜 (q - s j)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) A (LinearMap.range p)) (d : Fin n → ℤ),
      ∀ i j, (b i).val j ∈ 𝒜 (d i - s j) := by
  classical
  obtain ⟨n, d, ι, π, hιπ, hπι, hι_hom, -⟩ :=
    exists_homogeneous_matrix_retract_of_idempotent 𝒜 hneg h₀ s p hp hhom
  have hinj : Function.Injective ι := fun w₁ w₂ hw ↦ by
    have := congr_arg π hw
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, hπι, LinearMap.id_apply,
      LinearMap.id_apply] at this
  have hrange : LinearMap.range ι = LinearMap.range p := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨w, rfl⟩
      refine ⟨ι w, ?_⟩
      rw [← hιπ, LinearMap.comp_apply, ← LinearMap.comp_apply π ι, hπι, LinearMap.id_apply]
    · rintro _ ⟨v, rfl⟩
      exact ⟨π v, by rw [← hιπ, LinearMap.comp_apply]⟩
  let eqRange : (Fin n → A) ≃ₗ[A] LinearMap.range p :=
    (LinearEquiv.ofInjective ι hinj).trans (LinearEquiv.ofEq _ _ hrange)
  refine ⟨n, (Pi.basisFun A (Fin n)).map eqRange, d, fun i j ↦ ?_⟩
  have hcoe : (((Pi.basisFun A (Fin n)).map eqRange) i : J → A) = ι (Pi.single i 1) := by
    simp [eqRange]
  rw [hcoe]
  refine hι_hom (d i) (Pi.single i 1) (fun i' ↦ ?_) j
  by_cases hi : i' = i
  · subst hi
    simpa using SetLike.one_mem_graded 𝒜
  · simp [Pi.single_eq_of_ne hi]

end RetractSplitting

end FreeHead

section RankOneBasis

/-- Over a nonnegatively `ℤ`-graded commutative algebra, if a submodule `L` of `(J → A)` is spanned
by a nonzero vector `v₀` homogeneous of degree `d₀` with respect to shifts `s`, then any
`Fin n`-indexed homogeneous `A`-basis `(b, d)` of `L` has `n = 1` and `d i = d₀`. -/
theorem rank_one_homogeneous_basis_eq {k : Type uk} [CommSemiring k] {A : Type uA} [CommRing A]
    [Algebra k A] (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]
    (hneg : ∀ i < 0, 𝒜 i = ⊥) {J : Type uJ} {s : J → ℤ} {L : Submodule A (J → A)}
    {v₀ : L} (hv₀_ne : v₀ ≠ 0) (hv₀_span : Submodule.span A {v₀} = ⊤) {d₀ : ℤ}
    (hv₀_hom : ∀ j, v₀.val j ∈ 𝒜 (d₀ - s j)) {n : ℕ} (b : Module.Basis (Fin n) A L)
    {d : Fin n → ℤ} (hb_hom : ∀ i j, (b i).val j ∈ 𝒜 (d i - s j)) :
    n = 1 ∧ ∀ i, d i = d₀ := by
  have h10 : (1 : A) ≠ 0 := fun h10 ↦ hv₀_ne (by rw [← one_smul A v₀, h10, zero_smul])
  have hn : n = 1 := by
    rcases eq_or_ne n 0 with rfl | hn0
    · exact False.elim (hv₀_ne (b.repr.injective (Subsingleton.elim _ _)))
    · by_contra hn1
      have h2 : 2 ≤ n := by omega
      let i₀ : Fin n := ⟨0, by omega⟩
      let i₁ : Fin n := ⟨1, h2⟩
      obtain ⟨c₀, hc₀⟩ := Submodule.mem_span_singleton.mp (hv₀_span ▸ Submodule.mem_top : b i₀ ∈ _)
      obtain ⟨c₁, hc₁⟩ := Submodule.mem_span_singleton.mp (hv₀_span ▸ Submodule.mem_top : b i₁ ∈ _)
      have hrel : c₁ • b i₀ = c₀ • b i₁ := by
        rw [← hc₀, ← hc₁, smul_smul, smul_smul, mul_comm]
      have hc₁_zero : c₁ = 0 := by
        simpa [i₀, i₁, b.repr_self] using congr_arg (fun x ↦ b.repr x i₀) hrel
      have hb₁_zero : b i₁ = 0 := by rw [← hc₁, hc₁_zero, zero_smul]
      exact h10 (by simpa [b.repr_self] using congr_arg (fun x ↦ b.repr x i₁) hb₁_zero)
  refine ⟨hn, fun i ↦ ?_⟩
  subst hn
  rw [Fin.eq_zero i]
  have hv₀_eq : v₀ = b.repr v₀ 0 • b 0 := by simpa using (b.sum_repr v₀).symm
  obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.mp (hv₀_span ▸ Submodule.mem_top : b 0 ∈ _)
  have hunit : c' * b.repr v₀ 0 = 1 := by
    have hsmul : (c' * b.repr v₀ 0) • b 0 = b 0 := by rw [← smul_smul, ← hv₀_eq, hc']
    simpa [b.repr_self] using congr_arg (fun x ↦ b.repr x 0) hsmul
  have hunit₀ : (DirectSum.decompose 𝒜 c' 0 : A) *
      (DirectSum.decompose 𝒜 (b.repr v₀ 0) 0 : A) = 1 := by
    rw [← GradedAlgebra.coe_decompose_mul_zero_of_nonneg hneg, hunit,
      DirectSum.decompose_of_mem_same 𝒜 (SetLike.one_mem_graded 𝒜)]
  by_contra hne
  have hb0 : b 0 = 0 := Subtype.ext <| funext fun j ↦ by
    classical
    have hmul : b.repr v₀ 0 * (b 0).val j = v₀.val j :=
      (congr_fun (congr_arg Subtype.val hv₀_eq) j).symm
    have hdec :=
      DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (i := 0) (a := b.repr v₀ 0) (hb_hom 0 j)
    rw [zero_add, hmul, DirectSum.decompose_of_mem_ne 𝒜 (hv₀_hom j) (by omega)] at hdec
    rw [Submodule.coe_zero, Pi.zero_apply]
    calc
      (b 0).val j = 1 * (b 0).val j := (one_mul _).symm
      _ = (DirectSum.decompose 𝒜 c' 0 : A) *
          ((DirectSum.decompose 𝒜 (b.repr v₀ 0) 0 : A) * (b 0).val j) := by rw [← mul_assoc, hunit₀]
      _ = 0 := by rw [← hdec, mul_zero]
  exact hv₀_ne (by rw [hv₀_eq, hb0, smul_zero])

end RankOneBasis

end TauCeti.GradedModuleCat

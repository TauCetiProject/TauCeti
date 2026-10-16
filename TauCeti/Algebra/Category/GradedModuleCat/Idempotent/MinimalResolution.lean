/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Idempotent.Head
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.Converse
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.Simple
public import TauCeti.Algebra.Module.GradedModule.Nakayama

/-!
# Minimal graded projective surjections and resolutions

Let `A` be a nonnegatively graded algebra over a field `k` whose degree-zero piece is spanned by a
complete family of orthogonal idempotents `eᵢ` of degree zero, as for the path-length grading of
a path algebra of a finite acyclic quiver or of a zigzag algebra. Write `A₊` for the sum of the
pieces of `A` of positive degree.

A graded module `M` vanishing below some degree is the target of a **minimal projective
surjection**: a degree-zero surjection `P ⟶ M` from a direct sum `P` of shifted projectives `A eᵢ`
whose kernel lies in `A₊ P`, minimal in the sense of `TauCeti.GradedProjectiveResolution.IsMinimal`.
Its generators lift a homogeneous `k`-basis of `M / A₊ M` adapted to the idempotents: in each
degree `p` choose a complement of `A₊ M` in `eᵢ • Mₚ`. Graded Nakayama makes the generators
generate, and because the degree-zero part of `A eᵢ` is `k eᵢ`, the kernel lies in `A₊ P`.

Iterating along successive kernels gives a minimal graded projective resolution, with
finite-dimensional terms when `A` and `M` are finite-dimensional. With the diagonal Ext criterion
for minimal resolutions this gives the elementary characterisation of linearity: `M` has a linear
graded projective resolution exactly when `Extⁿ(M, N)` vanishes for every graded module `N`
concentrated in a single degree `p ≠ n`. In the finite-dimensional case it suffices to test
finite-dimensional simple modules `N`; for `M` a graded simple this is the diagonal vanishing of
the bigraded `Ext` between graded simples.

## Main results

* `TauCeti.GradedModuleCat.exists_minimal_projective_surjection`: minimal projective
  surjections onto bounded-below graded modules.
* `TauCeti.GradedModuleCat.exists_minimal_projective_surjection_of_finite`: finite-dimensional
  sources for finite-dimensional graded modules over a finite-dimensional algebra.
* `TauCeti.GradedProjectiveResolution.exists_isMinimal`: minimal graded projective resolutions
  of bounded-below graded modules.
* `TauCeti.GradedProjectiveResolution.exists_isMinimal_of_finite`: minimal resolutions with
  finite-dimensional terms.
* `TauCeti.GradedProjectiveResolution.exists_isLinear_iff_subsingleton_ext`: a bounded-below
  graded module has a linear resolution exactly when Ext against concentrated modules vanishes
  off the diagonal.
* `TauCeti.GradedProjectiveResolution.exists_isLinear_iff_subsingleton_ext_simple`: the same
  criterion for finite-dimensional modules, tested against simple modules.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded
  projective modules and graded Nakayama.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, Section I.5, for projective covers over a basic algebra.
* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Section 1.2, for minimal and linear resolutions and the diagonal Ext criterion.
-/

public section

noncomputable section

namespace TauCeti.GradedModuleCat

open CategoryTheory _root_.DirectSum
open scoped Pointwise

universe uk uA uI v w

section Cover

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] {I : Type uI} {e : I → A}
  (he₀ : ∀ i, e i ∈ 𝒜 0) {J : Type w} (ι : J → I) (d : J → ℤ)

include he₀ in
private theorem isHomogeneous_span_e (i : I) : (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜 :=
  Ideal.homogeneous_span 𝒜 _ fun _ hx => ⟨0, (Set.mem_singleton_iff.1 hx) ▸ he₀ i⟩

/-- The graded projective `⨁ⱼ (A e_{ι j}){d j}`. -/
private abbrev coverObj : GradedModuleCat.{max w uA} 𝒜 :=
  directSumObj fun j =>
    (ofIdeal 𝒜 (Ideal.span {e (ι j)}) (isHomogeneous_span_e he₀ (ι j))).shiftObj (d j)

private theorem mem_coverObj_piece_iff (p : ℤ) (x : coverObj he₀ ι d) :
    x ∈ (coverObj he₀ ι d).grading.piece p ↔
      ∀ j, ((x j : Ideal.span {e (ι j)}) : A) ∈ 𝒜 (p - d j) := by
  rw [InternalGrading.directSum_piece, InternalGrading.mem_directSumPiece_iff]
  exact forall_congr' fun j => (mem_shiftObj_piece_iff _ _ _ _).trans (mem_ofIdeal_piece_iff _)

/-- The generator `e_{ι j}` of the `j`-th summand. -/
private def coverGen (j : J) : coverObj he₀ ι d := by
  classical
  exact DirectSum.lof A J (fun j => (Ideal.span {e (ι j)} : Ideal A)) j
    (spanSingletonGenerator (e (ι j)))

/-- The map `⨁ⱼ (A e_{ι j}){d j} ⟶ M` sending `a` in the `j`-th summand to `a • m j`. -/
private def coverLift {M : GradedModuleCat.{max w uA} 𝒜} (m : J → M)
    (hm : ∀ j, m j ∈ M.grading.piece (d j)) : coverObj he₀ ι d ⟶ M := by
  classical
  refine ofHom (DirectSum.toModule A J M fun j =>
    (LinearMap.toSpanSingleton A M (m j)).comp (Ideal.span {e (ι j)}).subtype)
    (TauCeti.LinearMap.isHomogeneous_def.mpr fun p y hy => ?_)
  have hy' := (mem_coverObj_piece_iff he₀ ι d p y).mp hy
  rw [← DFinsupp.sum_single (f := y), DFinsupp.sum, map_sum]
  refine (M.grading.piece (p + 0)).sum_mem fun j _ => ?_
  rw [DirectSum.single_eq_lof A, DirectSum.toModule_lof]
  simpa using SetLike.GradedSMul.smul_mem (hy' j) (hm j)

private theorem coverLift_coverGen {M : GradedModuleCat.{max w uA} 𝒜} (m : J → M)
    (hm : ∀ j, m j ∈ M.grading.piece (d j)) (j : J) :
    (coverLift he₀ ι d m hm).hom (coverGen he₀ ι d j) = e (ι j) • m j := by
  classical
  simp [coverLift, coverGen]

private theorem lof_eq_smul_coverGen (hidem : ∀ i, IsIdempotentElem (e i)) [hJ : DecidableEq J]
    (j : J) (y : (Ideal.span {e (ι j)} : Ideal A)) :
    DirectSum.lof A J (fun j => (Ideal.span {e (ι j)} : Ideal A)) j y =
      (y : A) • coverGen he₀ ι d j := by
  cases Subsingleton.elim hJ (Classical.decEq J)
  rw [coverGen, ← map_smul, smul_spanSingletonGenerator (hidem (ι j))]

private theorem projective_coverObj (hidem : ∀ i, IsIdempotentElem (e i)) :
    Module.Projective A (coverObj he₀ ι d) :=
  Module.Projective.directSum_iff.mpr fun j => (hidem (ι j)).projective_span_singleton

end Cover

section Minimal

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] {I : Type uI} {e : I → A}
  (hneg : ∀ p < 0, 𝒜 p = ⊥) (he : OrthogonalIdempotents e) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hspan : 𝒜 0 ≤ Submodule.span k (Set.range e)) {J : Type w} (ι : J → I) (d : J → ℤ)

include hneg he hspan in
/-- Modulo the positive-degree action, every multiple of a generator of the cover is a scalar
multiple of that generator. -/
private theorem exists_smul_coverGen_sub_mem (j : J) (a : A) :
    ∃ c : k, a • coverGen he₀ ι d j - c • coverGen he₀ ι d j ∈
      (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (coverObj he₀ ι d)) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => exact ⟨0, by simp⟩
  | add a b ha hb =>
    obtain ⟨c, hc⟩ := ha
    obtain ⟨c', hc'⟩ := hb
    exact ⟨c + c', by simpa [add_smul, sub_add_sub_comm] using add_mem hc hc'⟩
  | @homogeneous r a =>
    obtain ⟨a, ha⟩ := a
    rcases lt_trichotomy r 0 with hr | rfl | hr
    · rw [hneg r hr, Submodule.mem_bot] at ha
      exact ⟨0, by simp [ha]⟩
    · obtain ⟨c, hc⟩ := exists_eq_smul_of_mem_zero he hspan (i := ι j)
        (by simpa using SetLike.GradedMul.mul_mem ha (he₀ (ι j)))
        (Ideal.mul_mem_left _ a (Ideal.mem_span_singleton_self (e (ι j))))
      refine ⟨c, ?_⟩
      have h : a • spanSingletonGenerator (e (ι j)) = c • spanSingletonGenerator (e (ι j)) :=
        Subtype.ext (by simpa using hc)
      classical
      simp only [coverGen, ← LinearMap.map_smul_of_tower, ← map_smul, h, sub_self]
      exact zero_mem _
    · have hmem : a ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i :=
        Submodule.mem_iSup_of_mem r (Submodule.mem_iSup_of_mem (i := hr) ha)
      have h := Submodule.smul_mem_smul hmem (Submodule.mem_top (R := k) (x := coverGen he₀ ι d j))
      exact ⟨0, by simpa using h⟩

include hneg he hspan in
/-- Modulo the positive-degree action, every element of the cover is a `k`-linear combination of
its generators. -/
private theorem exists_sub_linearCombination_mem (x : coverObj he₀ ι d) :
    ∃ c : J →₀ k, x - Finsupp.linearCombination k (coverGen he₀ ι d) c ∈
      (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (coverObj he₀ ι d)) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, by simp⟩
  | of j y =>
    obtain ⟨c, hc⟩ := exists_smul_coverGen_sub_mem hneg he he₀ hspan ι d j y
    refine ⟨Finsupp.single j c, ?_⟩
    rwa [Finsupp.linearCombination_single, ← DirectSum.lof_eq_of A,
      lof_eq_smul_coverGen he₀ ι d he.idem]
  | add x y hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨c', hc'⟩ := hy
    exact ⟨c + c', by simpa [map_add, sub_add_sub_comm] using add_mem hc hc'⟩

include hneg he hspan in
/-- If the images of the generators are linearly independent modulo `A₊ M`, then the kernel of
the cover lies in `A₊` times the cover. -/
private theorem mem_positive_smul_top_of_coverLift_eq_zero {M : GradedModuleCat.{max w uA} 𝒜}
    (m : J → M) (hm : ∀ j, m j ∈ M.grading.piece (d j)) (hme : ∀ j, e (ι j) • m j = m j)
    (hind : ∀ c : J →₀ k, Finsupp.linearCombination k m c ∈
      (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) → c = 0)
    {x : coverObj he₀ ι d} (hx : (coverLift he₀ ι d m hm).hom x = 0) :
    x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (coverObj he₀ ι d)) := by
  obtain ⟨c, hc⟩ := exists_sub_linearCombination_mem hneg he he₀ hspan ι d x
  set π := ((coverLift he₀ ι d m hm).hom.restrictScalars k)
  have hmap : π (x - Finsupp.linearCombination k (coverGen he₀ ι d) c) ∈
      (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
    refine Submodule.smul_induction_on hc (fun a ha y _ => ?_) (fun y z hy hz => ?_)
    · simpa [π] using Submodule.smul_mem_smul ha (Submodule.mem_top (R := k) (x := π y))
    · simpa only [map_add] using add_mem hy hz
  have hlc : π (Finsupp.linearCombination k (coverGen he₀ ι d) c) =
      Finsupp.linearCombination k m c := by
    rw [Finsupp.apply_linearCombination]
    congr 2
    funext j
    exact (coverLift_coverGen he₀ ι d m hm j).trans (hme j)
  rw [map_sub, LinearMap.restrictScalars_apply, hx, zero_sub, hlc, neg_mem_iff] at hmap
  rwa [hind c hmap, map_zero, sub_zero] at hc

include hneg in
/-- The cover vanishes below the lowest degree of its generators. -/
private theorem coverObj_piece_eq_bot {b : ℤ} (hd : ∀ j, b ≤ d j) {p : ℤ} (hp : p < b) :
    (coverObj he₀ ι d).grading.piece p = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  ext j : 1
  have h := (mem_coverObj_piece_iff he₀ ι d p x).mp hx j
  rw [hneg _ (by linarith [hd j]), Submodule.mem_bot] at h
  exact Subtype.ext (by simpa using h)

/-- **Graded Nakayama for the cover.** If `M` is bounded below and the generator images span
every homogeneous piece of `M` modulo `A₊ M`, then the cover is surjective. -/
private theorem coverLift_surjective {M : GradedModuleCat.{max w uA} 𝒜}
    (m : J → M) (hm : ∀ j, m j ∈ M.grading.piece (d j)) (hme : ∀ j, e (ι j) • m j = m j)
    (b : ℤ) (hb : ∀ p < b, M.grading.piece p = ⊥)
    (hgen : ∀ p, M.grading.piece p ≤ Submodule.span k (Set.range m) ⊔
      (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) :
    Function.Surjective (coverLift he₀ ι d m hm).hom := by
  rw [← LinearMap.range_eq_top]
  refine InternalGrading.eq_top_of_piece_le_sup_positive_smul_top 𝒜 _
    (TauCeti.LinearMap.IsHomogeneous.isHomogeneous_range (coverLift he₀ ι d m hm).isHomogeneous)
    b hb fun p => (hgen p).trans (sup_le_sup_right ?_ _)
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact ⟨coverGen he₀ ι d j, by rw [coverLift_coverGen, hme]⟩

end Minimal

section Generators

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] {I : Type uI} [Fintype I] {e : I → A}
  (he : CompleteOrthogonalIdempotents e) (he₀ : ∀ i, e i ∈ 𝒜 0)

/-- The `k`-linear map `x ↦ a • xₚ` onto `a • Mₚ`. -/
private def smulPieceProj (N : GradedModuleCat.{v} 𝒜) (a : A) (p : ℤ) :
    N →ₗ[k] (a • N.grading.piece p : Submodule k N) where
  toFun x := ⟨a • (decompose N.grading.piece x p : N),
    Submodule.smul_mem_pointwise_smul _ _ _ (decompose N.grading.piece x p).2⟩
  map_add' x y := Subtype.ext (by simp [smul_add])
  map_smul' c x := Subtype.ext <| by
    simp only [decompose_smul, DirectSum.smul_apply, SetLike.val_smul, RingHom.id_apply]
    exact smul_comm _ _ _

omit [GradedAlgebra 𝒜] in
private theorem coe_smulPieceProj (N : GradedModuleCat.{v} 𝒜) (a : A) (p : ℤ) (x : N) :
    (smulPieceProj N a p x : N) = a • (decompose N.grading.piece x p : N) :=
  (rfl)

variable {M : GradedModuleCat.{v} 𝒜}
  (C : ∀ (p : ℤ) (i : I), Submodule k (e i • M.grading.piece p : Submodule k M))

/-- The index type of the generators: a basis of each `C p i`. -/
private abbrev GenIndex := Σ p : ℤ, Σ i : I, Module.Basis.ofVectorSpaceIndex k (C p i)

/-- The generator indexed by `⟨p, i, t⟩`: the `t`-th basis vector of `C p i`. -/
private def gen (j : GenIndex C) : M :=
  ((Module.Basis.ofVectorSpace k (C j.1 j.2.1) j.2.2 : C j.1 j.2.1) :
    ↥(e j.2.1 • M.grading.piece j.1))

omit [GradedAlgebra 𝒜] [Fintype I] in
private theorem gen_mem (j : GenIndex C) : gen C j ∈ e j.2.1 • M.grading.piece j.1 :=
  ((Module.Basis.ofVectorSpace k (C j.1 j.2.1) j.2.2 : C j.1 j.2.1) :
    ↥(e j.2.1 • M.grading.piece j.1)).2

variable (hC : ∀ p i, IsCompl (((⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)).comap
  (e i • M.grading.piece p).subtype) (C p i))

include he he₀ hC in
/-- If each `C p i` is a complement of `A₊ M` in `eᵢ • Mₚ`, the generators are linearly
independent modulo `A₊ M`. -/
private theorem eq_zero_of_linearCombination_gen_mem (c : GenIndex C →₀ k)
    (hc : Finsupp.linearCombination k (gen C) c ∈
      (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) : c = 0 := by
  classical
  ext ⟨p, i, t⟩
  -- The coordinate of the generator at `⟨p, i, t⟩`: apply `x ↦ eᵢ • xₚ`, project onto `C p i`
  -- along `A₊ M`, and read off the `t`-th basis coordinate.
  let b := Module.Basis.ofVectorSpace k (C p i)
  let κ : M →ₗ[k] k := b.coord t ∘ₗ (C p i).projectionOnto _ (hC p i).symm ∘ₗ
    smulPieceProj M (e i) p
  have hκQ : ∀ x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M), κ x = 0 := by
    intro x hx
    have hx' : smulPieceProj M (e i) p x ∈ ((⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) •
        (⊤ : Submodule k M)).comap (e i • M.grading.piece p).subtype := by
      simp only [Submodule.mem_comap, Submodule.subtype_apply, coe_smulPieceProj]
      exact InternalGrading.smul_mem_positive_smul_top (he₀ i)
        (InternalGrading.isHomogeneous_positive_smul_top 𝒜 p hx)
    simp [κ, Submodule.projectionOnto_apply_of_mem_right _ hx']
  have hκgen : ∀ l : GenIndex C, κ (gen C l) = if l = ⟨p, i, t⟩ then 1 else 0 := by
    rintro ⟨p', i', t'⟩
    have hmem := (mem_smul_grading_piece_iff (he.idem i') (he₀ i')).mp (gen_mem C ⟨p', i', t'⟩)
    by_cases hp : p' = p
    · subst hp
      by_cases hi : i' = i
      · subst hi
        have h : smulPieceProj M (e i') p' (gen C ⟨p', i', t'⟩) =
            (Module.Basis.ofVectorSpace k (C p' i') t' : C p' i') := by
          ext
          rw [coe_smulPieceProj, decompose_of_mem_same _ hmem.1, hmem.2]
          rfl
        have hj : (⟨p', i', t'⟩ : GenIndex C) = ⟨p', i', t⟩ ↔ t' = t :=
          ⟨fun h => by
            obtain ⟨-, h⟩ := Sigma.mk.inj_iff.mp h
            obtain ⟨-, h⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h)
            exact eq_of_heq h, fun h => h ▸ rfl⟩
        simp only [κ, b, LinearMap.comp_apply, h, Submodule.projectionOnto_apply_left,
          Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, hj]
      · have h : smulPieceProj M (e i) p' (gen C ⟨p', i', t'⟩) = 0 := by
          ext
          rw [coe_smulPieceProj, decompose_of_mem_same _ hmem.1, ← hmem.2, smul_smul,
            he.ortho (fun h => hi h.symm), zero_smul]
          rfl
        simp only [κ, LinearMap.comp_apply, h, map_zero]
        rw [eq_comm, ite_eq_right_iff]
        exact fun h => absurd (congrArg (fun l : GenIndex C => l.2.1) h) hi
    · have h : smulPieceProj M (e i) p (gen C ⟨p', i', t'⟩) = 0 := by
        ext
        rw [coe_smulPieceProj, decompose_of_mem_ne _ hmem.1 hp, smul_zero]
        rfl
      simp only [κ, LinearMap.comp_apply, h, map_zero]
      rw [eq_comm, ite_eq_right_iff]
      exact fun h => absurd (congrArg Sigma.fst h) hp
  have hcomp : κ ∘ₗ Finsupp.linearCombination k (gen C) = Finsupp.lapply ⟨p, i, t⟩ := by
    ext l
    simp [hκgen, Finsupp.single_apply]
  have h := LinearMap.congr_fun hcomp c
  rw [LinearMap.comp_apply, Finsupp.lapply_apply, hκQ _ hc] at h
  rw [Finsupp.coe_zero, Pi.zero_apply, ← h]

omit [GradedAlgebra 𝒜] in
include he hC in
/-- If each `C p i` is a complement of `A₊ M` in `eᵢ • Mₚ`, the generators span every homogeneous
piece of `M` modulo `A₊ M`. -/
private theorem piece_le_span_gen_sup (p : ℤ) :
    M.grading.piece p ≤ Submodule.span k (Set.range (gen C)) ⊔
      (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
  intro x hx
  rw [← one_smul A x, ← he.complete, Finset.sum_smul]
  refine Submodule.sum_mem _ fun i _ => ?_
  -- Split `eᵢ • x` along `A₊ M` and its complement `C p i`.
  have hy : (⟨e i • x, Submodule.smul_mem_pointwise_smul _ _ _ hx⟩ :
      ↥(e i • M.grading.piece p)) ∈
      ((⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)).comap
        (e i • M.grading.piece p).subtype ⊔ C p i := by
    rw [(hC p i).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨q, hq, c, hc, hqc⟩ := Submodule.mem_sup.mp hy
  have hcoe : e i • x = (c : M) + (q : M) := by
    rw [add_comm]
    exact congrArg Subtype.val hqc.symm
  rw [hcoe]
  refine Submodule.add_mem_sup ?_ hq
  have hspanC : (⟨c, hc⟩ : C p i) ∈
      Submodule.span k (Set.range (Module.Basis.ofVectorSpace k (C p i))) := by
    rw [(Module.Basis.ofVectorSpace k (C p i)).span_eq]
    exact Submodule.mem_top
  refine Submodule.span_mono ?_ (Submodule.apply_mem_span_image_of_mem_span
    ((e i • M.grading.piece p).subtype ∘ₗ (C p i).subtype) hspanC)
  rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
  exact ⟨⟨p, i, t⟩, rfl⟩

include he he₀ in
/-- Homogeneous generators of `M`, each fixed by one of the idempotents, whose images form a
`k`-basis of `M / A₊ M`. -/
private theorem exists_generators (M : GradedModuleCat.{max uA uI v} 𝒜) :
    ∃ (J : Type (max uA uI v)) (ι : J → I) (d : J → ℤ) (m : J → M),
      (∀ j, m j ∈ M.grading.piece (d j)) ∧ (∀ j, e (ι j) • m j = m j) ∧ (∀ j, m j ≠ 0) ∧
      (∀ c : J →₀ k, Finsupp.linearCombination k m c ∈
        (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) → c = 0) ∧
      ∀ p, M.grading.piece p ≤ Submodule.span k (Set.range m) ⊔
        (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
  choose C hC using fun (p : ℤ) (i : I) => (((⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) •
    (⊤ : Submodule k M)).comap (e i • M.grading.piece p).subtype).exists_isCompl
  have hmem (j : GenIndex C) :=
    (mem_smul_grading_piece_iff (he.idem j.2.1) (he₀ j.2.1)).mp (gen_mem C j)
  exact ⟨GenIndex C, fun j => j.2.1, fun j => j.1, gen C, fun j => (hmem j).1,
    fun j => (hmem j).2,
    fun j => by simpa [gen] using (Module.Basis.ofVectorSpace k (C j.1 j.2.1)).ne_zero j.2.2,
    eq_zero_of_linearCombination_gen_mem he he₀ C hC, piece_le_span_gen_sup he C hC⟩

end Generators

section ProjectiveSurjection

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] {I : Type uI} [Fintype I] {e : I → A}
  (hneg : ∀ p < 0, 𝒜 p = ⊥) (he : CompleteOrthogonalIdempotents e) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hspan : 𝒜 0 ≤ Submodule.span k (Set.range e))

include hneg he he₀ hspan in
private theorem exists_minimal_projective_surjection_aux (M : GradedModuleCat.{max uA uI v} 𝒜)
    (b : ℤ) (hb : ∀ p < b, M.grading.piece p = ⊥) :
    ∃ (P : GradedModuleCat.{max uA uI v} 𝒜) (π : P ⟶ M), Module.Projective A P ∧
      Function.Surjective π.hom ∧
      (∀ x, π.hom x = 0 → x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k P)) ∧
      (∀ p < b, P.grading.piece p = ⊥) ∧
      (Module.Finite k A → Module.Finite k M → Module.Finite k P) := by
  obtain ⟨J, ι, d, m, hm, hme, hm0, hind, hgen⟩ := exists_generators he he₀ M
  have hd (j : J) : b ≤ d j := by
    by_contra h
    exact hm0 j (by simpa [hb _ (not_le.mp h)] using hm j)
  refine ⟨coverObj he₀ ι d, coverLift he₀ ι d m hm, projective_coverObj he₀ ι d he.idem,
    coverLift_surjective he₀ ι d m hm hme b hb hgen,
    fun x hx => mem_positive_smul_top_of_coverLift_eq_zero hneg he.toOrthogonalIdempotents he₀
      hspan ι d m hm hme hind hx,
    fun p hp => coverObj_piece_eq_bot hneg he₀ ι d hd hp, fun _ _ => ?_⟩
  -- The generators are linearly independent, hence finitely many.
  have : Finite J := LinearIndependent.finite_of_isNoetherian (v := m)
    (linearIndependent_iff.mpr fun c hc => hind c (by rw [hc]; exact zero_mem _))
  have (j : J) : Module.Finite k (Ideal.span {e (ι j)} : Ideal A) :=
    Module.Finite.of_injective ((Ideal.span {e (ι j)} : Ideal A).subtype.restrictScalars k)
      Subtype.val_injective
  exact Module.Finite.instDirectSum _

include hneg he he₀ hspan in
/-- **Minimal projective surjections.** Let `A` be a nonnegatively graded algebra over a field
whose degree-zero part is spanned by a complete family of orthogonal idempotents `eᵢ` of degree
zero. Every graded module `M` vanishing below degree `b` is the image of a projective graded
module `P` under a degree-zero surjection whose kernel lies in `A₊ P`. The source `P` also vanishes
below degree `b`. -/
theorem exists_minimal_projective_surjection (M : GradedModuleCat.{max uA uI v} 𝒜) (b : ℤ)
    (hb : ∀ p < b, M.grading.piece p = ⊥) :
    ∃ (P : GradedModuleCat.{max uA uI v} 𝒜) (π : P ⟶ M), Module.Projective A P ∧
      Function.Surjective π.hom ∧
      (∀ x, π.hom x = 0 → x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k P)) ∧
      ∀ p < b, P.grading.piece p = ⊥ :=
  let ⟨P, π, hP, hπ, hmin, hb, _⟩ :=
    exists_minimal_projective_surjection_aux hneg he he₀ hspan M b hb
  ⟨P, π, hP, hπ, hmin, hb⟩

include hneg he he₀ hspan in
/-- **Minimal projective surjections onto finite-dimensional modules.** Over a finite-dimensional
algebra as in `TauCeti.GradedModuleCat.exists_minimal_projective_surjection`, a finite-dimensional
graded module is the target of a minimal projective surjection from a finite-dimensional graded
module. -/
theorem exists_minimal_projective_surjection_of_finite [Module.Finite k A]
    (M : GradedModuleCat.{max uA uI v} 𝒜) [Module.Finite k M] :
    ∃ (P : GradedModuleCat.{max uA uI v} 𝒜) (π : P ⟶ M), Module.Projective A P ∧
      Function.Surjective π.hom ∧
      (∀ x, π.hom x = 0 → x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k P)) ∧
      Module.Finite k P := by
  obtain ⟨b, hb⟩ := M.grading.finite_piece_ne_bot.bddBelow
  obtain ⟨P, π, hP, hπ, hmin, -, hfin⟩ :=
    exists_minimal_projective_surjection_aux hneg he he₀ hspan M b fun p hp => by
      by_contra hne
      exact absurd (hb hne) (not_le.mpr hp)
  exact ⟨P, π, hP, hπ, hmin, hfin inferInstance inferInstance⟩

end ProjectiveSurjection

end TauCeti.GradedModuleCat

namespace TauCeti.GradedProjectiveResolution

open CategoryTheory CategoryTheory.Abelian GradedModuleCat

universe w uk uA uI v

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] {I : Type uI} [Fintype I] {e : I → A}
  (hneg : ∀ p < 0, 𝒜 p = ⊥) (he : CompleteOrthogonalIdempotents e) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hspan : 𝒜 0 ≤ Submodule.span k (Set.range e))

include hneg he he₀ hspan in
/-- **Minimal graded projective resolutions exist.** Let `A` be a nonnegatively graded algebra over
a field whose degree-zero part is spanned by a complete family of orthogonal idempotents of degree
zero. Every graded module vanishing below degree `b` has a minimal graded projective resolution
all of whose terms vanish below degree `b`. -/
theorem exists_isMinimal (M : GradedModuleCat.{max uA uI v} 𝒜) (b : ℤ)
    (hb : ∀ p < b, M.grading.piece p = ⊥) :
    ∃ r : GradedProjectiveResolution.{uk, uA, max uA uI v, max uA uI v} 𝒜 M.grading,
      r.IsMinimal ∧ ∀ n p, p < b → (r.grading n).piece p = ⊥ :=
  exists_isMinimal_of_forall_cover (fun N => ∀ p < b, N.grading.piece p = ⊥)
    (fun N => ∀ p < b, N.grading.piece p = ⊥) (fun N hN => by
      obtain ⟨P, π, hP, hπ, hmin, hPb⟩ :=
        exists_minimal_projective_surjection hneg he he₀ hspan N b hN
      refine ⟨P, π, hP, hπ, hmin, hPb, fun p hp => ?_⟩
      rw [Submodule.eq_bot_iff]
      intro z hz
      rw [InternalGrading.mem_ker_piece, hPb p hp, Submodule.mem_bot] at hz
      exact Subtype.ext hz) M hb

include hneg he he₀ hspan in
/-- **Finite-dimensional minimal graded projective resolutions exist** over a finite-dimensional
algebra as in `TauCeti.GradedProjectiveResolution.exists_isMinimal`: a finite-dimensional graded
module has a minimal graded projective resolution with finite-dimensional terms. -/
theorem exists_isMinimal_of_finite [Module.Finite k A] (M : GradedModuleCat.{max uA uI v} 𝒜)
    [Module.Finite k M] :
    ∃ r : GradedProjectiveResolution.{uk, uA, max uA uI v, max uA uI v} 𝒜 M.grading,
      r.IsMinimal ∧ ∀ n, Module.Finite k (r.X n) :=
  exists_isMinimal_of_forall_cover (fun N => Module.Finite k N) (fun N => Module.Finite k N)
    (fun N hN => by
      obtain ⟨P, π, hP, hπ, hmin, hPf⟩ :=
        exists_minimal_projective_surjection_of_finite hneg he he₀ hspan N
      exact ⟨P, π, hP, hπ, hmin, hPf, Module.Finite.of_injective
        ((LinearMap.ker π.hom).subtype.restrictScalars k) Subtype.val_injective⟩) M inferInstance

variable [HasExt.{w} (GradedModuleCat.{max uA uI v} 𝒜)]

include hneg he he₀ hspan in
/-- **Diagonal Ext detects the existence of a linear resolution.** Over an algebra as in
`TauCeti.GradedProjectiveResolution.exists_isMinimal`, a bounded-below graded module has a linear
graded projective resolution exactly when `Extⁿ(M, N)` vanishes for every graded module `N`
concentrated in a single degree `p ≠ n`. -/
theorem exists_isLinear_iff_subsingleton_ext (M : GradedModuleCat.{max uA uI v} 𝒜) (b : ℤ)
    (hb : ∀ p < b, M.grading.piece p = ⊥) :
    (∃ r : GradedProjectiveResolution.{uk, uA, max uA uI v, max uA uI v} 𝒜 M.grading,
        r.IsLinear) ↔
      ∀ (n : ℕ) (p : ℤ), (n : ℤ) ≠ p → ∀ N : GradedModuleCat.{max uA uI v} 𝒜,
        (∀ q, q ≠ p → N.grading.piece q = ⊥) → Subsingleton (Ext.{w} M N n) := by
  constructor
  · rintro ⟨r, hr⟩ n p hnp N hN
    exact hr.subsingleton_ext_of_ne p hN n hnp
  · intro hExt
    obtain ⟨r, hr, hbelow⟩ := exists_isMinimal hneg he he₀ hspan M b hb
    exact ⟨r, (hr.isLinear_iff_subsingleton_ext hneg (fun _ => b) hbelow).mpr hExt⟩

include hneg he he₀ hspan in
/-- **Diagonal Ext against simple modules detects the existence of a linear resolution.** Over a
finite-dimensional algebra as in `TauCeti.GradedProjectiveResolution.exists_isMinimal`, a
finite-dimensional graded module `M` has a linear graded projective resolution exactly when
`Extⁿ(M, S)` vanishes for every finite-dimensional simple graded module `S` concentrated in a
degree `p ≠ n`. -/
theorem exists_isLinear_iff_subsingleton_ext_simple [Module.Finite k A]
    (M : GradedModuleCat.{max uA uI v} 𝒜) [Module.Finite k M] :
    (∃ r : GradedProjectiveResolution.{uk, uA, max uA uI v, max uA uI v} 𝒜 M.grading,
        r.IsLinear) ↔
      ∀ (n : ℕ) (p : ℤ), (n : ℤ) ≠ p → ∀ N : GradedModuleCat.{max uA uI v} 𝒜,
        Module.Finite k N → Simple N → (∀ q, q ≠ p → N.grading.piece q = ⊥) →
          Subsingleton (Ext.{w} M N n) := by
  constructor
  · rintro ⟨r, hr⟩ n p hnp N - - hN
    exact hr.subsingleton_ext_of_ne p hN n hnp
  · intro hExt
    obtain ⟨r, hr, hfin⟩ := exists_isMinimal_of_finite hneg he he₀ hspan M
    have := hfin
    exact ⟨r, (hr.isLinear_iff_subsingleton_ext_simple hneg).mpr hExt⟩

end TauCeti.GradedProjectiveResolution

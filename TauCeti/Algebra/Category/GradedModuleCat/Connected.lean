/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.Algebra.Category.GradedModuleCat.Free
public import TauCeti.Algebra.Module.GradedModule.Nakayama

/-!
# Graded projective modules and idempotent splittings over connected graded algebras

Let `A` be an algebra over a principal ideal domain `k`, internally `ℤ`-graded by `k`-submodules
`𝒜 : ℤ → Submodule k A`. Assume that `A` is *nonnegatively graded* (`𝒜 i = ⊥` for `i < 0`) and
*connected* over `k`, meaning that scalars act faithfully (`FaithfulSMul k A`) and degree-zero
elements come from `k` (`𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A)`). The algebra `A` itself
need not be commutative.

Under these hypotheses, every graded retract of a finite graded free module — and hence every
finitely generated projective graded `𝒜`-module — is isomorphic in `TauCeti.GradedModuleCat 𝒜` to
a finite graded free module `free 𝒜 d`, and therefore admits a finite `A`-basis of homogeneous
elements.

For any graded module `M` over a commutative base ring `k`, `headPiece M p` is the degree-`p` head
quotient `Mₚ / (A₊ M ∩ Mₚ)`, functorial in graded morphisms `M ⟶ N`. By bounded-below graded
Nakayama, a graded morphism between bounded-below graded modules with projective target is an
isomorphism whenever it induces a bijection on `headPiece` in every degree
(`isIso_of_forall_bijective_headPieceMap`). Over a connected nonnegatively graded algebra,
`freeHeadEquiv` identifies `headPiece (free 𝒜 s) p` with `{j // s j = p} → k`; when `k` is
nontrivial, graded free isomorphisms and finite homogeneous bases of submodules therefore determine
the degree multiplicities and shift multisets uniquely (`natCard_fiber_eq_of_free_iso`,
`multiset_map_eq_of_free_iso`, `multiset_map_eq_of_homogeneous_basis_submodule`).

Over a principal ideal domain `k`, every degree-zero idempotent endomorphism of `free 𝒜 s` — or, in
coordinates, of a finite product `J → A` with summand shifts `s : J → ℤ` — splits homogeneously
through a finite shifted free module via explicit maps `ι` and `π` satisfying `π ∘ₗ ι = id` and
`ι ∘ₗ π = p`, and its image `LinearMap.range p` admits a finite homogeneous `A`-basis.

## Main definitions

* `TauCeti.GradedModuleCat.positiveSubmodule`, `TauCeti.GradedModuleCat.positivePiece`,
  `TauCeti.GradedModuleCat.headPiece`: the positive-degree action `A₊ M`, its intersection with
  `Mₚ`, and the degree-`p` head quotient `Mₚ / (A₊ M ∩ Mₚ)`.
* `TauCeti.GradedModuleCat.headPieceMap`, `TauCeti.GradedModuleCat.headPieceLinearEquiv`:
  functorial action of graded morphisms and isomorphisms on `headPiece`.
* `TauCeti.GradedModuleCat.freeHeadEquiv`: the `k`-linear equivalence
  `({j : J // s j = p} → k) ≃ₗ[k] headPiece (free 𝒜 s) p` over a connected nonnegatively graded
  algebra.

## Main results

* `TauCeti.GradedModuleCat.isIso_of_forall_bijective_headPieceMap`: graded Nakayama isomorphism
  criterion for morphisms between bounded-below graded modules with projective target.
* `TauCeti.GradedModuleCat.natCard_fiber_eq_of_free_iso`,
  `TauCeti.GradedModuleCat.multiset_map_eq_of_free_iso`,
  `TauCeti.GradedModuleCat.multiset_map_eq_of_homogeneous_basis_submodule`: uniqueness of degree
  multiplicities and shift multisets over any nontrivial commutative base ring `k`.
* `TauCeti.GradedModuleCat.exists_free_iso_of_retract`,
  `TauCeti.GradedModuleCat.exists_fin_free_iso_of_retract`,
  `TauCeti.GradedModuleCat.exists_biproduct_shift_regular_iso_of_retract`: every graded retract of a
  finite graded free module (or finite biproduct of shifted copies of `regular 𝒜`) is isomorphic to
  a finite graded free module.
* `TauCeti.GradedModuleCat.exists_free_iso_of_finite_projective`,
  `TauCeti.GradedModuleCat.exists_fin_free_iso_of_finite_projective`: every finitely generated
  projective graded module is isomorphic to a finite graded free module.
* `TauCeti.GradedModuleCat.exists_homogeneous_basis_of_retract`,
  `TauCeti.GradedModuleCat.exists_homogeneous_basis_of_finite_projective`: existence of a finite
  homogeneous `A`-basis on any graded retract or finitely generated projective graded module.
* `TauCeti.GradedModuleCat.exists_split_free_of_idempotent`,
  `TauCeti.GradedModuleCat.exists_split_pi_of_idempotent`: explicit homogeneous splitting of a
  degree-zero idempotent through a finite shifted free module.
* `TauCeti.GradedModuleCat.exists_homogeneous_basis_range_idempotent`: the image of a degree-zero
  idempotent on `J → A` with shifts `s : J → ℤ` has a finite homogeneous `A`-basis.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
* T. Y. Lam, *Serre's Problem on Projective Modules*, Springer Monographs in Mathematics,
  Chapter II, §2, for projective modules over positively graded rings via graded Nakayama.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

namespace TauCeti.GradedModuleCat

universe uk uA v

section HeadPiece

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

/-- The `k`-submodule `A₊ M` generated by the action of positive-degree scalars on `M`. -/
def positiveSubmodule (M : GradedModuleCat.{v} 𝒜) : Submodule k M :=
  (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)

/-- Unfolding lemma for `positiveSubmodule`. -/
theorem positiveSubmodule_def (M : GradedModuleCat.{v} 𝒜) :
    positiveSubmodule M = (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) :=
  (rfl)

/-- Any graded morphism carries the positive-degree scalar action of the source into that of the
target. -/
theorem map_mem_positiveSubmodule {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) {x : M}
    (hx : x ∈ positiveSubmodule M) : f.hom x ∈ positiveSubmodule N := by
  refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun y z hy hz => ?_)
  · rw [f.hom.map_smul]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · rw [map_add]
    exact (positiveSubmodule N).add_mem hy hz

/-- The degree-`p` slice `(A₊ M) ∩ Mₚ`, viewed as a `k`-submodule of `M.grading.piece p`. -/
def positivePiece (M : GradedModuleCat.{v} 𝒜) (p : ℤ) : Submodule k (M.grading.piece p) :=
  (positiveSubmodule M).comap (M.grading.piece p).subtype

/-- Membership in `positivePiece M p` is membership in `positiveSubmodule M`. -/
@[simp]
theorem mem_positivePiece_iff (M : GradedModuleCat.{v} 𝒜) (p : ℤ) (x : M.grading.piece p) :
    x ∈ positivePiece M p ↔ (x : M) ∈ positiveSubmodule M :=
  Iff.rfl

/-- The degree-`p` head piece `Mₚ / (A₊ M ∩ Mₚ)` of a graded module, as a `k`-module. -/
abbrev headPiece (M : GradedModuleCat.{v} 𝒜) (p : ℤ) : Type v :=
  M.grading.piece p ⧸ positivePiece M p

/-- The quotient projection from `Mₚ` to `headPiece M p`. -/
def headPieceMk (M : GradedModuleCat.{v} 𝒜) (p : ℤ) :
    M.grading.piece p →ₗ[k] M.headPiece p :=
  (positivePiece M p).mkQ

/-- The quotient projection `headPieceMk M p` is surjective. -/
theorem headPieceMk_surjective (M : GradedModuleCat.{v} 𝒜) (p : ℤ) :
    Function.Surjective (headPieceMk M p) :=
  Submodule.mkQ_surjective _

/-- The kernel of `headPieceMk M p` consists of degree-`p` elements lying in `positiveSubmodule M`.
-/
@[simp]
theorem headPieceMk_eq_zero_iff (M : GradedModuleCat.{v} 𝒜) (p : ℤ) (x : M.grading.piece p) :
    headPieceMk M p x = 0 ↔ (x : M) ∈ positiveSubmodule M :=
  Submodule.Quotient.mk_eq_zero _

/-- The `k`-linear map induced on degree-`p` pieces by a morphism of graded modules. -/
def pieceMap {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) (p : ℤ) :
    M.grading.piece p →ₗ[k] N.grading.piece p where
  toFun x := ⟨f.hom x.1, map_mem f x.2⟩
  map_add' x y := Subtype.ext (map_add f.hom x.1 y.1)
  map_smul' r x := Subtype.ext (by simp)

/-- Coercing `pieceMap f p x` to `N` evaluates `f.hom` on `x`. -/
@[simp]
theorem coe_pieceMap_apply {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) (p : ℤ)
    (x : M.grading.piece p) : (pieceMap f p x : N) = f.hom x.1 :=
  (rfl)

/-- The `k`-linear map induced on `headPiece` in degree `p` by a morphism of graded modules. -/
def headPieceMap {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) (p : ℤ) :
    M.headPiece p →ₗ[k] N.headPiece p :=
  Submodule.mapQ (positivePiece M p) (positivePiece N p) (pieceMap f p)
    fun _ hx => map_mem_positiveSubmodule f hx

/-- Evaluation of `headPieceMap` on a quotient class in `headPiece`. -/
@[simp]
theorem headPieceMap_mk {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) (p : ℤ)
    (x : M.grading.piece p) :
    headPieceMap f p (headPieceMk M p x) = headPieceMk N p (pieceMap f p x) :=
  (rfl)

/-- The identity morphism acts as the identity on `headPiece`. -/
@[simp]
theorem headPieceMap_id (M : GradedModuleCat.{v} 𝒜) (p : ℤ) :
    headPieceMap (𝟙 M) p = LinearMap.id := by
  ext ⟨x, hx⟩
  rfl

/-- Composition of graded morphisms maps to composition on `headPiece`. -/
@[simp]
theorem headPieceMap_comp {L M N : GradedModuleCat.{v} 𝒜} (f : L ⟶ M) (g : M ⟶ N) (p : ℤ) :
    headPieceMap (f ≫ g) p = (headPieceMap g p).comp (headPieceMap f p) := by
  ext ⟨x, hx⟩
  rfl

/-- The zero morphism induces the zero map on `headPiece`. -/
@[simp]
theorem headPieceMap_zero (M N : GradedModuleCat.{v} 𝒜) (p : ℤ) :
    headPieceMap (0 : M ⟶ N) p = 0 := by
  ext ⟨x, hx⟩
  rfl

/-- An isomorphism in `GradedModuleCat 𝒜` induces a `k`-linear equivalence on `headPiece` in every
degree `p`. -/
def headPieceLinearEquiv {M N : GradedModuleCat.{v} 𝒜} (iso : M ≅ N) (p : ℤ) :
    M.headPiece p ≃ₗ[k] N.headPiece p :=
  LinearEquiv.ofLinearMap (headPieceMap iso.hom p) (headPieceMap iso.inv p)
    (by rw [← headPieceMap_comp, iso.inv_hom_id, headPieceMap_id])
    (by rw [← headPieceMap_comp, iso.hom_inv_id, headPieceMap_id])

/-- Surjectivity on `headPiece` in degree `p` implies that `Nₚ` lies in the sum of the image of `f`
and `A₊ N`. -/
theorem piece_le_range_sup_positiveSubmodule_of_surjective_headPieceMap
    {M N : GradedModuleCat.{v} 𝒜} {f : M ⟶ N} {p : ℤ}
    (hf : Function.Surjective (headPieceMap f p)) :
    N.grading.piece p ≤ (LinearMap.range f.hom).restrictScalars k ⊔ positiveSubmodule N := by
  intro y hy
  obtain ⟨q, hq⟩ := hf (headPieceMk N p ⟨y, hy⟩)
  obtain ⟨x, rfl⟩ := headPieceMk_surjective M p q
  rw [headPieceMap_mk] at hq
  have hsub : headPieceMk N p (⟨y, hy⟩ - pieceMap f p x) = 0 := by
    rw [map_sub, hq, sub_self]
  have hpos : y - f.hom x.1 ∈ positiveSubmodule N := (headPieceMk_eq_zero_iff N p _).mp hsub
  have heq : y = f.hom x.1 + (y - f.hom x.1) := (add_sub_cancel (f.hom x.1) y).symm
  rw [heq]
  exact Submodule.add_mem_sup ⟨x.1, rfl⟩ hpos

/-- By bounded-below graded Nakayama, a graded morphism into a bounded-below module is surjective
whenever it is surjective on `headPiece` in every degree. -/
theorem surjective_of_forall_surjective_headPieceMap
    {M N : GradedModuleCat.{v} 𝒜} {f : M ⟶ N} (b : ℤ)
    (hbelow : ∀ p < b, N.grading.piece p = ⊥)
    (hf : ∀ p, Function.Surjective (headPieceMap f p)) :
    Function.Surjective f.hom := by
  rw [← LinearMap.range_eq_top]
  exact InternalGrading.eq_top_of_piece_le_sup_positive_smul_top 𝒜
    (LinearMap.range f.hom) f.isHomogeneous.isHomogeneous_range b hbelow
    fun p => piece_le_range_sup_positiveSubmodule_of_surjective_headPieceMap (hf p)

/-- By bounded-below graded Nakayama, a bounded-below graded module whose `headPiece` vanishes in
every degree is trivial. -/
theorem subsingleton_of_forall_subsingleton_headPiece
    {M : GradedModuleCat.{v} 𝒜} (b : ℤ)
    (hbelow : ∀ p < b, M.grading.piece p = ⊥)
    (h : ∀ p, Subsingleton (M.headPiece p)) :
    Subsingleton M := by
  refine InternalGrading.subsingleton_of_positive_smul_top_eq_top 𝒜 b hbelow ?_
  apply top_unique
  intro x _
  classical
  rw [← _root_.DirectSum.sum_support_decompose M.grading.piece x]
  refine (positiveSubmodule M).sum_mem fun p _ => ?_
  let y : M.grading.piece p := _root_.DirectSum.decompose M.grading.piece x p
  have hz : headPieceMk M p y = 0 := (h p).elim _ _
  exact (headPieceMk_eq_zero_iff M p y).mp hz

/-- **Graded Nakayama isomorphism criterion.** A graded morphism `φ : M ⟶ P` between bounded-below
graded modules with projective target `P` is an isomorphism whenever `headPieceMap φ p` is
bijective in every degree `p`. -/
theorem isIso_of_forall_bijective_headPieceMap
    {M P : GradedModuleCat.{v} 𝒜} [Projective P] (φ : M ⟶ P)
    (bM bP : ℤ) (hM : ∀ p < bM, M.grading.piece p = ⊥) (hP : ∀ p < bP, P.grading.piece p = ⊥)
    (hbij : ∀ p, Function.Bijective (headPieceMap φ p)) :
    IsIso φ := by
  have hsurj : Function.Surjective φ.hom :=
    surjective_of_forall_surjective_headPieceMap bP hP fun p => (hbij p).2
  have _ : Epi φ := (epi_iff_surjective φ).mpr hsurj
  let σ : P ⟶ M := Projective.factorThru (𝟙 P) φ
  have hσφ : σ ≫ φ = 𝟙 P := Projective.factorThru_comp (𝟙 P) φ
  let eKer : M ⟶ M := 𝟙 M - φ ≫ σ
  have heKer_mem (y : M) : eKer.hom y ∈ LinearMap.ker φ.hom := by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← hom_comp,
      Preadditive.sub_comp, Category.id_comp, Category.assoc, hσφ, Category.comp_id,
      sub_self, hom_zero, LinearMap.zero_apply]
  let πK : M ⟶ kernelObj φ :=
    ofHom (eKer.hom.codRestrict (LinearMap.ker φ.hom) heKer_mem) <|
      LinearMap.isHomogeneous_def.mpr fun p y hy => by
        rw [add_zero, InternalGrading.mem_ker_piece]
        exact map_mem eKer hy
  have hι_πK : kernelι φ ≫ πK = 𝟙 (kernelObj φ) := by
    apply hom_ext
    apply LinearMap.ext
    rintro ⟨y, hy⟩
    apply Subtype.ext
    have hy0 : φ.hom y = 0 := hy
    simp [πK, eKer, hy0]
  have hbelowK : ∀ p < bM, (kernelObj φ).grading.piece p = ⊥ :=
    fun p hp => piece_eq_bot_of_injective (kernelι φ) (Submodule.subtype_injective _) p (hM p hp)
  have hsubK : Subsingleton (kernelObj φ) := by
    refine subsingleton_of_forall_subsingleton_headPiece bM hbelowK fun p => ?_
    refine subsingleton_of_forall_eq 0 fun z => ?_
    have hinj_ι : Function.Injective (headPieceMap (kernelι φ) p) := by
      refine Function.LeftInverse.injective (g := headPieceMap πK p) fun w => ?_
      have hcomp := congrArg (fun f => headPieceMap f p) hι_πK
      rw [headPieceMap_comp, headPieceMap_id] at hcomp
      exact LinearMap.congr_fun hcomp w
    have hzero_φ : headPieceMap φ p (headPieceMap (kernelι φ) p z) = 0 := by
      have hcomp := congrArg (fun f => headPieceMap f p z) (kernelι_comp φ)
      simpa only [headPieceMap_comp, LinearMap.comp_apply, headPieceMap_zero,
        LinearMap.zero_apply] using hcomp
    have hzero_ι : headPieceMap (kernelι φ) p z = 0 :=
      (hbij p).1 (hzero_φ.trans (map_zero _).symm)
    exact hinj_ι (hzero_ι.trans (map_zero _).symm)
  have hinj : Function.Injective φ.hom := by
    rw [← LinearMap.ker_eq_bot]
    refine (Submodule.eq_bot_iff _).mpr fun y hy => ?_
    exact congrArg Subtype.val (hsubK.elim (⟨y, hy⟩ : kernelObj φ) 0)
  exact (isIso_iff_bijective φ).mpr ⟨hinj, hsurj⟩

end HeadPiece

section FreeHead

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

/-- Over a nonnegatively graded algebra, any finitely indexed graded free module is bounded
below. -/
theorem exists_piece_eq_bot_of_lt_free (hneg : ∀ i < 0, 𝒜 i = ⊥)
    {J : Type v} [Finite J] (s : J → ℤ) :
    ∃ b : ℤ, ∀ p < b, (free 𝒜 s).grading.piece p = ⊥ := by
  obtain ⟨b, hb⟩ := (Set.finite_range s).bddBelow
  refine ⟨b, fun p hp => (Submodule.eq_bot_iff _).mpr fun x hx => ?_⟩
  have hx' := (mem_free_piece_iff 𝒜 s p x).mp hx
  apply DFinsupp.ext
  intro j
  have hsj : b ≤ s j := hb ⟨j, rfl⟩
  have hneg_j : 𝒜 (p - s j) = ⊥ := hneg (p - s j) (by omega)
  simpa only [hneg_j, Submodule.mem_bot, DFinsupp.zero_apply] using hx' j

/-- Over a nonnegatively graded algebra, a degree-`p` element of `free 𝒜 s` belongs to the
positive-degree action `A₊ (free 𝒜 s)` if and only if its `j`-th coordinate vanishes whenever
`s j = p`. -/
theorem mem_positiveSubmodule_free_iff (hneg : ∀ i < 0, 𝒜 i = ⊥)
    {J : Type v} (s : J → ℤ) (p : ℤ) {x : free 𝒜 s}
    (hx : x ∈ (free 𝒜 s).grading.piece p) :
    x ∈ positiveSubmodule (free 𝒜 s) ↔ ∀ j : J, s j = p → x j = 0 := by
  classical
  constructor
  · intro hpos j hj
    let F : GradedModuleCat.{max uA v} 𝒜 := free 𝒜 s
    let _ : SetLike.GradedSMul 𝒜 F.grading.piece := F.gradedSMul
    have hspan := InternalGrading.decompose_mem_span_of_mem_positive_smul_top
      (G := F.grading) 𝒜 hpos p
    rw [_root_.DirectSum.decompose_of_mem_same F.grading.piece hx] at hspan
    let proj : F →ₗ[k] A :=
      (DirectSum.component A J (fun _ : J => A) j).restrictScalars k
    have hker : Submodule.span k
        {z : F | ∃ i, 0 < i ∧ ∃ a ∈ 𝒜 i,
          ∃ y ∈ F.grading.piece (p - i), a • y = z} ≤ LinearMap.ker proj := by
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, a, -, y, hy, rfl⟩
      have hy' := (mem_free_piece_iff 𝒜 s (p - i) y).mp hy j
      have hlt : p - i - s j < 0 := by omega
      have hy0 : y j = 0 := by simpa only [hneg _ hlt, Submodule.mem_bot] using hy'
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      have hproj : proj (a • y) = a * y j := by
        simp only [proj, LinearMap.restrictScalars_apply, map_smul, smul_eq_mul]
        rfl
      rw [hproj, hy0, mul_zero]
    exact hker hspan
  · intro hzero
    have hx_coord := (mem_free_piece_iff 𝒜 s p x).mp hx
    rw [← DirectSum.sum_support_of x]
    refine (positiveSubmodule (free 𝒜 s)).sum_mem fun j _ => ?_
    have hof : DirectSum.of (fun _ : J => A) j (x j) =
        x j • freeGenerator (𝒜 := 𝒜) (d := s) j := by
      apply DFinsupp.ext
      intro j'
      rw [DirectSum.of_apply, DFinsupp.smul_apply, freeGenerator_apply, smul_eq_mul]
      by_cases hjj : j = j' <;> simp [hjj]
    rw [hof]
    rcases lt_trichotomy (p - s j) 0 with hlt | heq | hgt
    · have hxj : x j = 0 := by simpa only [hneg _ hlt, Submodule.mem_bot] using hx_coord j
      simp [hxj]
    · have hxj : x j = 0 := hzero j (by omega)
      simp [hxj]
    · exact Submodule.smul_mem_smul
        (Submodule.mem_iSup_of_mem (p - s j) (Submodule.mem_iSup_of_mem hgt (hx_coord j)))
        Submodule.mem_top

/-- Lift a `k`-tuple indexed by `{j : J // s j = p}` to a homogeneous degree-`p` element of
`free 𝒜 s` supported on those generators. -/
def freePieceOfFiber {J : Type v} [Finite J] (s : J → ℤ) (p : ℤ) :
    ({j : J // s j = p} → k) →ₗ[k] (free 𝒜 s).grading.piece p := by
  letI : Fintype {j : J // s j = p} := Fintype.ofFinite _
  let genElem (u : {j : J // s j = p}) : (free 𝒜 s).grading.piece p :=
    ⟨freeGenerator (𝒜 := 𝒜) (d := s) u.1,
      by simpa only [u.2] using freeGenerator_mem_free_piece (𝒜 := 𝒜) (d := s) u.1⟩
  exact
    { toFun := fun c => ∑ u : {j : J // s j = p}, c u • genElem u
      map_add' := fun c₁ c₂ => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }

/-- Coordinate evaluation of `freePieceOfFiber` at a generator in degree `p`. -/
theorem freePieceOfFiber_coord {J : Type v} [Finite J] (s : J → ℤ) (p : ℤ)
    (c : {j : J // s j = p} → k) (u : {j : J // s j = p}) :
    (freePieceOfFiber 𝒜 s p c : free 𝒜 s) u.1 = algebraMap k A (c u) := by
  classical
  let _ : Fintype {j : J // s j = p} := Fintype.ofFinite _
  let proj : free 𝒜 s →ₗ[k] A :=
    (DirectSum.component A J (fun _ : J => A) u.1).restrictScalars k
  have hval : (freePieceOfFiber 𝒜 s p c : free 𝒜 s) u.1 =
      proj (freePieceOfFiber 𝒜 s p c : free 𝒜 s) := rfl
  rw [hval, freePieceOfFiber]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, AddSubmonoidClass.coe_finsetSum,
    SetLike.val_smul, map_sum, map_smul]
  have hterm : ∀ v : {j : J // s j = p},
      c v • proj (freeGenerator (𝒜 := 𝒜) (d := s) v.1) =
        if v = u then algebraMap k A (c u) else 0 := by
    intro v
    have hpv : proj (freeGenerator (𝒜 := 𝒜) (d := s) v.1) = if v.1 = u.1 then 1 else 0 := by
      simp [proj, ← DirectSum.apply_eq_component, freeGenerator_apply]
    rw [hpv]
    by_cases hvu : v = u
    · subst hvu
      simp [Algebra.algebraMap_eq_smul_one]
    · have hval_ne : v.1 ≠ u.1 := fun h => hvu (Subtype.ext h)
      simp [hvu, hval_ne]
  simp [hterm]

/-- Over a connected nonnegatively graded algebra, the degree-`p` head piece of a finite graded
free module `free 𝒜 s` is `k`-linearly equivalent to `{j : J // s j = p} → k`. -/
def freeHeadEquiv [FaithfulSMul k A]
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A))
    {J : Type v} [Finite J] (s : J → ℤ) (p : ℤ) :
    ({j : J // s j = p} → k) ≃ₗ[k] (free 𝒜 s).headPiece p := by
  refine LinearEquiv.ofBijective ((headPieceMk (free 𝒜 s) p).comp (freePieceOfFiber 𝒜 s p)) ⟨?_, ?_⟩
  · intro c₁ c₂ hc
    have h0 : headPieceMk (free 𝒜 s) p (freePieceOfFiber 𝒜 s p (c₁ - c₂)) = 0 := by
      rw [map_sub, map_sub, sub_eq_zero]
      exact hc
    have hpos : (freePieceOfFiber 𝒜 s p (c₁ - c₂) : free 𝒜 s) ∈ positiveSubmodule (free 𝒜 s) :=
      (headPieceMk_eq_zero_iff (free 𝒜 s) p _).mp h0
    have hcoord := (mem_positiveSubmodule_free_iff 𝒜 hneg s p
      (freePieceOfFiber 𝒜 s p (c₁ - c₂)).2).mp hpos
    funext u
    have hu := hcoord u.1 u.2
    rw [freePieceOfFiber_coord, Pi.sub_apply, map_sub, sub_eq_zero] at hu
    exact FaithfulSMul.algebraMap_injective k A hu
  · intro q
    obtain ⟨x, rfl⟩ := headPieceMk_surjective (free 𝒜 s) p q
    have hx := (mem_free_piece_iff 𝒜 s p x.1).mp x.2
    have hdeg0 : ∀ u : {j : J // s j = p}, ∃ r : k, algebraMap k A r = x.1 u.1 := by
      intro u
      have hmem : x.1 u.1 ∈ 𝒜 0 := by simpa [u.2] using hx u.1
      exact hzero hmem
    choose c hc using hdeg0
    refine ⟨c, ?_⟩
    rw [LinearMap.comp_apply, ← sub_eq_zero, ← map_sub, headPieceMk_eq_zero_iff]
    refine (mem_positiveSubmodule_free_iff 𝒜 hneg s p (freePieceOfFiber 𝒜 s p c - x).2).mpr ?_
    intro j hj
    let u : {j : J // s j = p} := ⟨j, hj⟩
    have hsub : ((freePieceOfFiber 𝒜 s p c - x : (free 𝒜 s).grading.piece p) : free 𝒜 s) j =
        (freePieceOfFiber 𝒜 s p c : free 𝒜 s) u.1 - x.1 u.1 := rfl
    rw [hsub, freePieceOfFiber_coord, hc u, sub_self]

/-- On a standard basis vector `Pi.single u r`, `freeHeadEquiv` produces `r` times the class of
`freeGenerator u.1`. -/
@[simp]
theorem freeHeadEquiv_single [FaithfulSMul k A]
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A))
    {J : Type v} [Finite J] (s : J → ℤ) (p : ℤ)
    [DecidableEq {j : J // s j = p}] (u : {j : J // s j = p}) (r : k) :
    freeHeadEquiv 𝒜 hneg hzero s p (Pi.single u r) =
      r • headPieceMk (free 𝒜 s) p ⟨freeGenerator (𝒜 := 𝒜) (d := s) u.1,
        by simpa only [u.2] using freeGenerator_mem_free_piece (𝒜 := 𝒜) (d := s) u.1⟩ := by
  let _ : Fintype {j : J // s j = p} := Fintype.ofFinite _
  have hsingle : freePieceOfFiber 𝒜 s p (Pi.single u r) =
      r • ⟨freeGenerator (𝒜 := 𝒜) (d := s) u.1,
        by simpa only [u.2] using freeGenerator_mem_free_piece (𝒜 := 𝒜) (d := s) u.1⟩ := by
    simp only [freePieceOfFiber, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single u]
    · simp
    · intro v _ hvu
      simp [Pi.single_eq_of_ne hvu]
    · intro hu
      exact absurd (Finset.mem_univ u) hu
  have happly : freeHeadEquiv 𝒜 hneg hzero s p (Pi.single u r) =
      headPieceMk (free 𝒜 s) p (freePieceOfFiber 𝒜 s p (Pi.single u r)) := rfl
  rw [happly, hsingle, map_smul]

/-- Over a connected nonnegatively graded algebra over a nontrivial commutative ring `k`, any
graded isomorphism `free 𝒜 d ≅ free 𝒜 d'` between finite graded free modules preserves the number
of generators in every homogeneous degree `p`. -/
theorem natCard_fiber_eq_of_free_iso [Nontrivial k] [FaithfulSMul k A]
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A))
    {I J : Type v} [Finite I] [Finite J]
    (d : I → ℤ) (d' : J → ℤ)
    (iso : free 𝒜 d ≅ free 𝒜 d') (p : ℤ) :
    Nat.card {i : I // d i = p} = Nat.card {j : J // d' j = p} := by
  let _ : Fintype {i : I // d i = p} := Fintype.ofFinite _
  let _ : Fintype {j : J // d' j = p} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact card_eq_of_linearEquiv k
    ((freeHeadEquiv 𝒜 hneg hzero d p).trans
      ((headPieceLinearEquiv iso p).trans (freeHeadEquiv 𝒜 hneg hzero d' p).symm))

/-- Over a connected nonnegatively graded algebra over a nontrivial commutative ring `k`, any
graded isomorphism `free 𝒜 d ≅ free 𝒜 d'` between `Fin`-indexed graded free modules preserves the
multiset of generator shifts. -/
theorem multiset_map_eq_of_free_iso [Nontrivial k] [FaithfulSMul k A]
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A))
    {m n : ℕ} (d : Fin m → ℤ) (d' : Fin n → ℤ)
    (iso : free 𝒜 d ≅ free 𝒜 d') :
    Multiset.map d Finset.univ.val = Multiset.map d' Finset.univ.val := by
  refine Multiset.ext.mpr fun p => ?_
  have hcount : ∀ {r : ℕ} (e : Fin r → ℤ),
      Multiset.count p (Multiset.map e Finset.univ.val) = Nat.card {i : Fin r // e i = p} := by
    intro r e
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_def, Finset.filter_val,
      Multiset.count_map]
    simp_rw [eq_comm]
  rw [hcount d, hcount d']
  exact natCard_fiber_eq_of_free_iso 𝒜 hneg hzero d d' iso p

/-- Over a connected nonnegatively graded algebra over a nontrivial commutative ring `k`, any two
finite homogeneous `A`-bases of a submodule `S : Submodule A (J → A)` (with ambient summand shifts
`s : J → ℤ`) have the same multiset of shifts, and hence the same rank. -/
theorem multiset_map_eq_of_homogeneous_basis_submodule [Nontrivial k] [FaithfulSMul k A]
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A))
    {J : Type v} [Finite J] (s : J → ℤ) (S : Submodule A (J → A))
    {m n : ℕ}
    (b₁ : Module.Basis (Fin m) A S) (d₁ : Fin m → ℤ)
    (hb₁ : ∀ i j, (b₁ i).val j ∈ 𝒜 (d₁ i - s j))
    (b₂ : Module.Basis (Fin n) A S) (d₂ : Fin n → ℤ)
    (hb₂ : ∀ i j, (b₂ i).val j ∈ 𝒜 (d₂ i - s j)) :
    Multiset.map d₁ Finset.univ.val = Multiset.map d₂ Finset.univ.val := by
  classical
  let _ : Fintype J := Fintype.ofFinite J
  let eJ : free 𝒜 s ≃ₗ[A] (J → A) := DirectSum.linearEquivFunOnFintype A J (fun _ : J => A)
  let d₁' : ULift.{v} (Fin m) → ℤ := fun i => d₁ i.down
  let d₂' : ULift.{v} (Fin n) → ℤ := fun i => d₂ i.down
  have hlift : ∀ {r : ℕ} (b : Module.Basis (Fin r) A S) (d : Fin r → ℤ),
      (∀ i j, (b i).val j ∈ 𝒜 (d i - s j)) →
      ∀ i : ULift.{v} (Fin r),
        eJ.symm (b i.down).val ∈ (free 𝒜 s).grading.piece (d i.down) :=
    fun _ d hb i =>
      (linearEquivFunOnFintype_symm_mem_free_piece_iff 𝒜 s (d i.down) _).mpr (hb i.down)
  let φ₁ : free 𝒜 d₁' ⟶ free 𝒜 s :=
    freeLift fun i => ⟨eJ.symm (b₁ i.down).val, hlift b₁ d₁ hb₁ i⟩
  let φ₂ : free 𝒜 d₂' ⟶ free 𝒜 s :=
    freeLift fun i => ⟨eJ.symm (b₂ i.down).val, hlift b₂ d₂ hb₂ i⟩
  let e₁ : free 𝒜 d₁' ≃ₗ[A] S := (freeBasis 𝒜 d₁').equiv b₁ Equiv.ulift
  let e₂ : free 𝒜 d₂' ≃ₗ[A] S := (freeBasis 𝒜 d₂').equiv b₂ Equiv.ulift
  have hφ₁_eq : φ₁.hom = eJ.symm.toLinearMap.comp (S.subtype.comp e₁.toLinearMap) := by
    apply (freeBasis 𝒜 d₁').ext
    intro i
    simp only [e₁, φ₁, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
      Equiv.ulift_apply, Submodule.subtype_apply]
    rw [freeBasis_apply, freeLift_generator]
  have hφ₂_eq : φ₂.hom = eJ.symm.toLinearMap.comp (S.subtype.comp e₂.toLinearMap) := by
    apply (freeBasis 𝒜 d₂').ext
    intro i
    simp only [e₂, φ₂, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
      Equiv.ulift_apply, Submodule.subtype_apply]
    rw [freeBasis_apply, freeLift_generator]
  have hφ₁_inj : Function.Injective φ₁.hom := by
    rw [hφ₁_eq]
    exact eJ.symm.injective.comp ((Submodule.subtype_injective S).comp e₁.injective)
  have hφ₂_inj : Function.Injective φ₂.hom := by
    rw [hφ₂_eq]
    exact eJ.symm.injective.comp ((Submodule.subtype_injective S).comp e₂.injective)
  let e₁₂ : free 𝒜 d₁' ≃ₗ[A] free 𝒜 d₂' := e₁.trans e₂.symm
  have hcomm (x : free 𝒜 d₁') : φ₂.hom (e₁₂ x) = φ₁.hom x := by
    rw [hφ₁_eq, hφ₂_eq]
    simp [e₁₂]
  let iso : free 𝒜 d₁' ≅ free 𝒜 d₂' := isoMk e₁₂ fun q x => by
    rw [← mem_piece_iff_of_injective φ₁ hφ₁_inj, ← hcomm x,
      mem_piece_iff_of_injective φ₂ hφ₂_inj]
  refine Multiset.ext.mpr fun p => ?_
  have hcount : ∀ {r : ℕ} (e : Fin r → ℤ),
      Multiset.count p (Multiset.map e Finset.univ.val) =
        Nat.card {i : ULift.{v} (Fin r) // e i.down = p} := by
    intro r e
    have hequiv : {i : ULift.{v} (Fin r) // e i.down = p} ≃ {i : Fin r // e i = p} :=
      Equiv.subtypeEquiv Equiv.ulift (fun _ => Iff.rfl)
    rw [Nat.card_congr hequiv, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_def,
      Finset.filter_val, Multiset.count_map]
    simp_rw [eq_comm]
  rw [hcount d₁, hcount d₂]
  exact natCard_fiber_eq_of_free_iso 𝒜 hneg hzero d₁' d₂' iso p

end FreeHead

section ConnectedPID

variable {k : Type uk} [CommRing k] [IsDomain k] [IsPrincipalIdealRing k]
  {A : Type uA} [Ring A] [Algebra k A] [FaithfulSMul k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

/-- **Graded freeness of retracts over a connected graded algebra.** Let `A` be a connected
nonnegatively `ℤ`-graded algebra over a principal ideal domain `k`. Any graded module `P` that is
a retract of a finite graded free module `free 𝒜 s` is isomorphic in `GradedModuleCat 𝒜` to a
finite graded free module `free 𝒜 d`. -/
theorem exists_free_iso_of_retract
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A))
    {J : Type v} [Finite J] (s : J → ℤ)
    {P : GradedModuleCat.{max uA v} 𝒜}
    (i : P ⟶ free 𝒜 s) (r : free 𝒜 s ⟶ P) (hir : i ≫ r = 𝟙 P) :
    ∃ (n : ℕ) (d : ULift.{v} (Fin n) → ℤ), Nonempty (free 𝒜 d ≅ P) := by
  classical
  have _ : Projective P := ({ i := i, r := r, retract := hir } : Retract P (free 𝒜 s)).projective
  have hi_inj : Function.Injective i.hom :=
    Function.LeftInverse.injective fun z => LinearMap.congr_fun (congrArg Hom.hom hir) z
  obtain ⟨bP, hbP⟩ := exists_piece_eq_bot_of_lt_free 𝒜 hneg s
  have hbelowP : ∀ p < bP, P.grading.piece p = ⊥ :=
    fun p hp => piece_eq_bot_of_injective i hi_inj p (hbP p hp)
  -- For each degree `p`, embed `P.headPiece p` into `{j : J // s j = p} → k` and pick a PID basis.
  let emb (p : ℤ) : P.headPiece p →ₗ[k] ({j : J // s j = p} → k) :=
    (freeHeadEquiv 𝒜 hneg hzero s p).symm.toLinearMap.comp (headPieceMap i p)
  have hemb_inj (p : ℤ) : Function.Injective (emb p) := by
    refine (freeHeadEquiv 𝒜 hneg hzero s p).symm.injective.comp ?_
    refine Function.LeftInverse.injective (g := headPieceMap r p) fun z => ?_
    have hcomp := congrArg (fun f => headPieceMap f p) hir
    rw [headPieceMap_comp, headPieceMap_id] at hcomp
    exact LinearMap.congr_fun hcomp z
  let pidBasis (p : ℤ) : Σ m : ℕ, Module.Basis (Fin m) k (LinearMap.range (emb p)) := by
    letI : Fintype {j : J // s j = p} := Fintype.ofFinite _
    exact Submodule.basisOfPid (Pi.basisFun k {j : J // s j = p}) (LinearMap.range (emb p))
  let m : ℤ → ℕ := fun p => (pidBasis p).1
  let bHead (p : ℤ) : Module.Basis (Fin (m p)) k (P.headPiece p) :=
    (pidBasis p).2.map (LinearEquiv.ofInjective (emb p) (hemb_inj p)).symm
  -- Outside `Set.range s`, the target Pi module is subsingleton, so `m p = 0`.
  have hm_mem_range {p : ℤ} (u : Fin (m p)) : p ∈ Set.range s := by
    by_contra hp
    have _ : IsEmpty {j : J // s j = p} := ⟨fun ⟨j, hj⟩ => hp ⟨j, hj⟩⟩
    exact (bHead p).ne_zero u ((hemb_inj p).subsingleton.elim _ _)
  -- Reindex the total head basis `Σ p : ℤ, Fin (m p)` by `ULift.{v} (Fin n)`.
  have _ : Finite (Σ p : ℤ, Fin (m p)) := by
    let _ : Finite (Set.range s) := Set.finite_range s
    let toRange : (Σ p : ℤ, Fin (m p)) → (Σ p : Set.range s, Fin (m p.1)) :=
      fun u => ⟨⟨u.1, hm_mem_range u.2⟩, u.2⟩
    refine Finite.of_injective toRange fun ⟨p₁, r₁⟩ ⟨p₂, r₂⟩ h => ?_
    have hp : p₁ = p₂ := congrArg (fun z => z.1.1) h
    subst hp
    have hr : r₁ = r₂ := by simpa [toRange] using h
    rw [hr]
  let _ : Fintype (Σ p : ℤ, Fin (m p)) := Fintype.ofFinite _
  let n : ℕ := Fintype.card (Σ p : ℤ, Fin (m p))
  let eULift : ULift.{v} (Fin n) ≃ (Σ p : ℤ, Fin (m p)) :=
    Equiv.ulift.trans (Fintype.equivFin _).symm
  -- Lift each head basis element to a homogeneous representative in `P`.
  choose rep hrep_mk using fun u : (Σ p : ℤ, Fin (m p)) =>
    headPieceMk_surjective P u.1 (bHead u.1 u.2)
  let d : ULift.{v} (Fin n) → ℤ := fun idx => (eULift idx).1
  let x : ∀ idx : ULift.{v} (Fin n), P.grading.piece (d idx) := fun idx => rep (eULift idx)
  let φ : free 𝒜 d ⟶ P := freeLift x
  -- Show `headPieceMap φ p` is bijective in every degree `p` by matching `k`-bases.
  have hbij_head (p : ℤ) : Function.Bijective (headPieceMap φ p) := by
    let _ : Fintype {idx : ULift.{v} (Fin n) // d idx = p} := Fintype.ofFinite _
    let eSigmaFiber : {u : Σ q : ℤ, Fin (m q) // u.1 = p} ≃ Fin (m p) :=
      { toFun := fun ⟨⟨_, r⟩, h⟩ => h ▸ r
        invFun := fun r => ⟨⟨p, r⟩, rfl⟩
        left_inv := fun ⟨⟨_, _⟩, h⟩ => by cases h; rfl
        right_inv := fun _ => rfl }
    let eFiber : {idx : ULift.{v} (Fin n) // d idx = p} ≃ Fin (m p) :=
      (Equiv.subtypeEquiv eULift (fun _ => Iff.rfl)).trans eSigmaFiber
    let B₁ := Pi.basisFun k {idx : ULift.{v} (Fin n) // d idx = p}
    let L : ({idx : ULift.{v} (Fin n) // d idx = p} → k) →ₗ[k] P.headPiece p :=
      (headPieceMap φ p).comp (freeHeadEquiv 𝒜 hneg hzero d p).toLinearMap
    have hL_eq : L = (B₁.equiv (bHead p) eFiber).toLinearMap := by
      apply B₁.ext
      intro ⟨idx, hidx⟩
      rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
      simp only [L, B₁, Pi.basisFun_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        freeHeadEquiv_single, one_smul]
      rcases h : eULift idx with ⟨q, r⟩
      have hqp : q = p := by simpa [d, h] using hidx
      subst hqp
      rw [headPieceMap_mk]
      have hpiece : pieceMap φ q ⟨freeGenerator (𝒜 := 𝒜) (d := d) idx,
          by simpa only [hidx] using freeGenerator_mem_free_piece (𝒜 := 𝒜) (d := d) idx⟩ =
            rep ⟨q, r⟩ := by
        apply Subtype.ext
        rw [coe_pieceMap_apply, freeLift_generator x idx]
        exact congrArg (fun u => (rep u : P)) h
      rw [hpiece, hrep_mk ⟨q, r⟩]
      congr 1
      simp [eFiber, eSigmaFiber, h]
    have hL_bij : Function.Bijective L := by
      rw [hL_eq]
      exact (B₁.equiv (bHead p) eFiber).bijective
    exact (Function.Bijective.of_comp_iff (headPieceMap φ p)
      (freeHeadEquiv 𝒜 hneg hzero d p).bijective).mp hL_bij
  obtain ⟨bD, hbD⟩ := exists_piece_eq_bot_of_lt_free 𝒜 hneg d
  have _ : IsIso φ := isIso_of_forall_bijective_headPieceMap φ bD bP hbD hbelowP hbij_head
  exact ⟨n, d, ⟨asIso φ⟩⟩

/-- Specialization of `exists_free_iso_of_retract` to `GradedModuleCat.{uA} 𝒜`, where the basis
index type can be taken directly to be `Fin n`. -/
theorem exists_fin_free_iso_of_retract
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A))
    {J : Type} [Finite J] (s : J → ℤ)
    {P : GradedModuleCat.{uA} 𝒜}
    (i : P ⟶ free 𝒜 s) (r : free 𝒜 s ⟶ P) (hir : i ≫ r = 𝟙 P) :
    ∃ (n : ℕ) (d : Fin n → ℤ), Nonempty (free 𝒜 d ≅ P) := by
  obtain ⟨n, d', ⟨iso⟩⟩ := exists_free_iso_of_retract 𝒜 hneg hzero s i r hir
  exact ⟨n, fun idx => d' (ULift.up idx), ⟨(freeCongrIso 𝒜 Equiv.ulift.symm d').trans iso⟩⟩

/-- Every graded retract of a finite categorical biproduct of shifted copies of `regular 𝒜` is
isomorphic in `GradedModuleCat 𝒜` to a finite categorical biproduct of shifted copies of
`regular 𝒜`. -/
theorem exists_biproduct_shift_regular_iso_of_retract
    [HasFiniteBiproducts (GradedModuleCat.{uA} 𝒜)]
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A))
    {J : Type} [Finite J] (s : J → ℤ)
    {P : GradedModuleCat.{uA} 𝒜}
    (i : P ⟶ biproduct fun j : J => (shiftFunctor (𝒜 := 𝒜) (s j)).obj (regular (𝒜 := 𝒜)))
    (r : (biproduct fun j : J => (shiftFunctor (𝒜 := 𝒜) (s j)).obj (regular (𝒜 := 𝒜))) ⟶ P)
    (hir : i ≫ r = 𝟙 P) :
    ∃ (n : ℕ) (d : Fin n → ℤ),
      Nonempty ((biproduct fun idx : Fin n =>
        (shiftFunctor (𝒜 := 𝒜) (d idx)).obj (regular (𝒜 := 𝒜))) ≅ P) := by
  let isoJ := biproductShiftRegularIsoFree 𝒜 s
  have hir' : (i ≫ isoJ.hom) ≫ (isoJ.inv ≫ r) = 𝟙 P := by
    rw [Category.assoc, ← Category.assoc isoJ.hom, isoJ.hom_inv_id, Category.id_comp, hir]
  obtain ⟨n, d, ⟨iso⟩⟩ := exists_fin_free_iso_of_retract 𝒜 hneg hzero s (i ≫ isoJ.hom)
    (isoJ.inv ≫ r) hir'
  exact ⟨n, d, ⟨biproductShiftRegularIsoFree 𝒜 d ≪≫ iso⟩⟩

/-- **Graded freeness of finitely generated projectives.** Over a connected nonnegatively graded
algebra over a principal ideal domain, every finitely generated projective graded module is
isomorphic to a finite graded free module. -/
theorem exists_free_iso_of_finite_projective
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A))
    (P : GradedModuleCat.{max uA v} 𝒜) [Module.Finite A P] [Module.Projective A P] :
    ∃ (n : ℕ) (d : ULift.{max uA v} (Fin n) → ℤ), Nonempty (free 𝒜 d ≅ P) := by
  obtain ⟨I, hI, s, f, hf⟩ := exists_finite_free_surjection P
  let _ : Finite I := hI
  have _ : Epi f := (epi_iff_surjective f).mpr hf
  let σ : P ⟶ free 𝒜 s := Projective.factorThru (𝟙 P) f
  exact exists_free_iso_of_retract.{uk, uA, max uA v} 𝒜 hneg hzero s σ f
    (Projective.factorThru_comp (𝟙 P) f)

/-- Specialization of `exists_free_iso_of_finite_projective` to `GradedModuleCat.{uA} 𝒜`, with
basis indexed by `Fin n`. -/
theorem exists_fin_free_iso_of_finite_projective
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A))
    (P : GradedModuleCat.{uA} 𝒜) [Module.Finite A P] [Module.Projective A P] :
    ∃ (n : ℕ) (d : Fin n → ℤ), Nonempty (free 𝒜 d ≅ P) := by
  obtain ⟨I, hI, s, f, hf⟩ := exists_finite_free_surjection.{uk, uA, 0} P
  let _ : Finite I := hI
  let _ : Fintype I := Fintype.ofFinite I
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let s₀ : Fin (Fintype.card I) → ℤ := s ∘ e
  let g : free 𝒜 s₀ ⟶ free 𝒜 s :=
    freeLift fun idx => ⟨freeGenerator (e idx), freeGenerator_mem_free_piece (e idx)⟩
  have hg_surj : Function.Surjective g.hom := by
    rw [freeLift_surjective_iff]
    have hrange : (Set.range fun idx : Fin (Fintype.card I) =>
        (freeGenerator (𝒜 := 𝒜) (d := s) (e idx) : free 𝒜 s)) =
        Set.range (freeBasis 𝒜 s) := by
      ext y
      rw [Set.mem_range, Set.mem_range]
      exact ⟨fun ⟨idx, h⟩ => ⟨e idx, (freeBasis_apply 𝒜 s (e idx)).trans h⟩,
        fun ⟨j, h⟩ => ⟨e.symm j, by
          rw [Equiv.apply_symm_apply, ← freeBasis_apply 𝒜 s j]
          exact h⟩⟩
    rw [hrange, (freeBasis 𝒜 s).span_eq]
  have _ : Epi (g ≫ f) := (epi_iff_surjective (g ≫ f)).mpr (hf.comp hg_surj)
  let σ : P ⟶ free 𝒜 s₀ := Projective.factorThru (𝟙 P) (g ≫ f)
  exact exists_fin_free_iso_of_retract 𝒜 hneg hzero s₀ σ (g ≫ f)
    (Projective.factorThru_comp (𝟙 P) (g ≫ f))

/-- Every graded retract of a finite graded free module over a connected nonnegatively graded
algebra over a principal ideal domain admits a finite homogeneous `A`-basis. -/
theorem exists_homogeneous_basis_of_retract
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A))
    {J : Type v} [Finite J] (s : J → ℤ)
    {P : GradedModuleCat.{max uA v} 𝒜}
    (i : P ⟶ free 𝒜 s) (r : free 𝒜 s ⟶ P) (hir : i ≫ r = 𝟙 P) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) A P) (d : Fin n → ℤ),
      ∀ idx, b idx ∈ P.grading.piece (d idx) := by
  obtain ⟨n, d, ⟨iso⟩⟩ := exists_free_iso_of_retract 𝒜 hneg hzero s i r hir
  exact ⟨n, homogeneousBasisOfFreeIso 𝒜 iso, fun idx => d (ULift.up idx),
    homogeneousBasisOfFreeIso_mem_piece 𝒜 iso⟩

/-- Every finitely generated projective graded module over a connected nonnegatively graded algebra
over a principal ideal domain admits a finite homogeneous `A`-basis. -/
theorem exists_homogeneous_basis_of_finite_projective
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A))
    (P : GradedModuleCat.{max uA v} 𝒜) [Module.Finite A P] [Module.Projective A P] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) A P) (d : Fin n → ℤ),
      ∀ idx, b idx ∈ P.grading.piece (d idx) := by
  obtain ⟨n, d, ⟨iso⟩⟩ := exists_free_iso_of_finite_projective 𝒜 hneg hzero P
  exact ⟨n, homogeneousBasisOfFreeIso.{uk, uA, max uA v} 𝒜 iso,
    fun idx => d (ULift.up idx), homogeneousBasisOfFreeIso_mem_piece.{uk, uA, max uA v} 𝒜 iso⟩

/-- **Splitting of graded idempotents on finite shifted free modules.** Any degree-zero idempotent
endomorphism `e` of `free 𝒜 s` (`[Finite J]`) factors homogeneously through a finite shifted free
module `free 𝒜 d` via `ι : free 𝒜 d ⟶ free 𝒜 s` and `π : free 𝒜 s ⟶ free 𝒜 d` with
`ι ≫ π = 𝟙 (free 𝒜 d)` and `π ≫ ι = e`. -/
theorem exists_split_free_of_idempotent
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A))
    {J : Type v} [Finite J] (s : J → ℤ)
    (e : free 𝒜 s ⟶ free 𝒜 s) (he : e ≫ e = e) :
    ∃ (n : ℕ) (d : ULift.{v} (Fin n) → ℤ) (ι : free 𝒜 d ⟶ free 𝒜 s) (π : free 𝒜 s ⟶ free 𝒜 d),
      ι ≫ π = 𝟙 (free 𝒜 d) ∧ π ≫ ι = e := by
  obtain ⟨Y, iIm, rIm, hir, hri⟩ := IsIdempotentComplete.idempotents_split (free 𝒜 s) e he
  obtain ⟨n, d, ⟨iso⟩⟩ := exists_free_iso_of_retract 𝒜 hneg hzero s iIm rIm hir
  refine ⟨n, d, iso.hom ≫ iIm, rIm ≫ iso.inv, ?_, ?_⟩
  · rw [Category.assoc, ← Category.assoc iIm, hir, Category.id_comp, iso.hom_inv_id]
  · rw [Category.assoc, ← Category.assoc iso.inv, iso.inv_hom_id, Category.id_comp, hri]

/-- **Coordinate homogeneous splitting of degree-zero idempotents.** On a finite product `J → A`
with summand shifts `s : J → ℤ`, any `A`-linear idempotent `p` preserving shifted homogeneous
pieces splits through `Fin n → A` via homogeneous `A`-linear maps `ι` and `π` satisfying
`π ∘ₗ ι = id` and `ι ∘ₗ π = p`. -/
theorem exists_split_pi_of_idempotent
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A))
    {J : Type v} [Finite J] (s : J → ℤ)
    (p : (J → A) →ₗ[A] (J → A))
    (hp : p.comp p = p)
    (hhom : ∀ (q : ℤ) (v : J → A),
      (∀ j, v j ∈ 𝒜 (q - s j)) → ∀ j, p v j ∈ 𝒜 (q - s j)) :
    ∃ (n : ℕ) (d : Fin n → ℤ)
      (ι : (Fin n → A) →ₗ[A] (J → A))
      (π : (J → A) →ₗ[A] (Fin n → A)),
      π.comp ι = LinearMap.id ∧
      ι.comp π = p ∧
      (∀ (q : ℤ) (w : Fin n → A),
        (∀ i, w i ∈ 𝒜 (q - d i)) → ∀ j, ι w j ∈ 𝒜 (q - s j)) ∧
      (∀ (q : ℤ) (v : J → A),
        (∀ j, v j ∈ 𝒜 (q - s j)) → ∀ i, π v i ∈ 𝒜 (q - d i)) := by
  classical
  let _ : Fintype J := Fintype.ofFinite J
  let eJ : free 𝒜 s ≃ₗ[A] (J → A) := DirectSum.linearEquivFunOnFintype A J (fun _ : J => A)
  let eHom : free 𝒜 s ⟶ free 𝒜 s :=
    ofHom (eJ.symm.toLinearMap.comp (p.comp eJ.toLinearMap)) <|
      LinearMap.isHomogeneous_def.mpr fun q x hx => by
        rw [add_zero, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.coe_coe]
        refine (linearEquivFunOnFintype_symm_mem_free_piece_iff 𝒜 s q _).mpr ?_
        refine hhom q (eJ x) fun j => ?_
        simp only [eJ, DirectSum.linearEquivFunOnFintype_apply]
        exact (mem_free_piece_iff 𝒜 s q x).mp hx j
  have heHom : eHom ≫ eHom = eHom := by
    apply hom_ext
    apply LinearMap.ext
    intro x
    simp only [hom_comp, LinearMap.comp_apply, eHom, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    rw [← LinearMap.comp_apply p p, hp]
  obtain ⟨n, d', ιF, πF, hιπ, hπι⟩ := exists_split_free_of_idempotent 𝒜 hneg hzero s eHom heHom
  let d : Fin n → ℤ := fun i => d' (ULift.up i)
  let eN₀ : free 𝒜 d' ≃ₗ[A] (ULift.{v} (Fin n) → A) :=
    DirectSum.linearEquivFunOnFintype A (ULift.{v} (Fin n)) (fun _ => A)
  let eULift : (ULift.{v} (Fin n) → A) ≃ₗ[A] (Fin n → A) :=
    LinearEquiv.piCongrLeft' A (fun _ => A) Equiv.ulift
  let eN : free 𝒜 d' ≃ₗ[A] (Fin n → A) := eN₀.trans eULift
  let ι : (Fin n → A) →ₗ[A] (J → A) := eJ.toLinearMap.comp (ιF.hom.comp eN.symm.toLinearMap)
  let π : (J → A) →ₗ[A] (Fin n → A) := eN.toLinearMap.comp (πF.hom.comp eJ.symm.toLinearMap)
  refine ⟨n, d, ι, π, ?_, ?_, ?_, ?_⟩
  · apply LinearMap.ext
    intro w
    simp only [ι, π, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [← LinearMap.comp_apply πF.hom ιF.hom, ← hom_comp, hιπ, hom_id, LinearMap.id_apply,
      eN.apply_symm_apply, LinearMap.id_apply]
  · apply LinearMap.ext
    intro v
    simp only [ι, π, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [← LinearMap.comp_apply ιF.hom πF.hom, ← hom_comp, hπι]
    simp [eHom]
  · intro q w hw j
    have hmem : eN.symm w ∈ (free 𝒜 d').grading.piece q := by
      simp only [eN, eN₀, LinearEquiv.trans_symm, LinearEquiv.trans_apply]
      refine (linearEquivFunOnFintype_symm_mem_free_piece_iff 𝒜 d' q _).mpr fun ⟨i⟩ => ?_
      simpa only [eULift, LinearEquiv.piCongrLeft'_symm_apply, Equiv.piCongrLeft'_symm_apply,
        Equiv.ulift_apply] using hw i
    simp only [ι, eJ, LinearMap.comp_apply, LinearEquiv.coe_coe,
      DirectSum.linearEquivFunOnFintype_apply]
    exact (mem_free_piece_iff 𝒜 s q _).mp (map_mem ιF hmem) j
  · intro q v hv i
    have hmem : eJ.symm v ∈ (free 𝒜 s).grading.piece q :=
      (linearEquivFunOnFintype_symm_mem_free_piece_iff 𝒜 s q v).mpr hv
    simp only [π, eN, eN₀, eULift, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.trans_apply, LinearEquiv.piCongrLeft'_apply, Equiv.ulift_symm_apply,
      DirectSum.linearEquivFunOnFintype_apply]
    exact (mem_free_piece_iff 𝒜 d' q _).mp (map_mem πF hmem) (ULift.up i)

/-- **Homogeneous basis of the image of a degree-zero idempotent.** Over a connected nonnegatively
graded algebra over a principal ideal domain, the image `LinearMap.range p` of a degree-zero
idempotent `p` on `J → A` (with summand shifts `s : J → ℤ`) admits a finite `A`-basis of
homogeneous vectors. -/
theorem exists_homogeneous_basis_range_idempotent
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A))
    {J : Type v} [Finite J] (s : J → ℤ)
    (p : (J → A) →ₗ[A] (J → A))
    (hp : p.comp p = p)
    (hhom : ∀ (q : ℤ) (v : J → A),
      (∀ j, v j ∈ 𝒜 (q - s j)) → ∀ j, p v j ∈ 𝒜 (q - s j)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) A (LinearMap.range p)) (d : Fin n → ℤ),
      ∀ i j, (b i).val j ∈ 𝒜 (d i - s j) := by
  obtain ⟨n, d, ι, π, hπι, hιπ, hι_hom, -⟩ :=
    exists_split_pi_of_idempotent 𝒜 hneg hzero s p hp hhom
  have hmem_range (w : Fin n → A) : ι w ∈ LinearMap.range p := by
    refine ⟨ι w, ?_⟩
    have hw : π (ι w) = w := LinearMap.congr_fun hπι w
    rw [← hιπ, LinearMap.comp_apply, hw]
  let eRange : (Fin n → A) ≃ₗ[A] LinearMap.range p :=
    LinearEquiv.ofLinearMap (ι.codRestrict (LinearMap.range p) hmem_range)
      (π.comp (LinearMap.range p).subtype)
      (by
        apply LinearMap.ext
        rintro ⟨_, v, rfl⟩
        apply Subtype.ext
        simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, Submodule.subtype_apply,
          LinearMap.id_apply]
        rw [← LinearMap.comp_apply ι π, hιπ, ← LinearMap.comp_apply p p, hp])
      (by
        apply LinearMap.ext
        intro w
        simpa only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.codRestrict_apply,
          LinearMap.id_apply] using LinearMap.congr_fun hπι w)
  let b : Module.Basis (Fin n) A (LinearMap.range p) := (Pi.basisFun A (Fin n)).map eRange
  refine ⟨n, b, d, fun i j => ?_⟩
  have hbi : (b i).val = ι (Pi.single i 1) := by simp [b, eRange]
  rw [hbi]
  refine hι_hom (d i) (Pi.single i 1) (fun i' => ?_) j
  by_cases hi : i' = i
  · subst hi
    simpa only [Pi.single_eq_same, sub_self] using SetLike.one_mem_graded 𝒜
  · simp [Pi.single_eq_of_ne hi]

end ConnectedPID

end TauCeti.GradedModuleCat

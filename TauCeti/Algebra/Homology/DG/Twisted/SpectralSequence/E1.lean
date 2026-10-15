/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Filtration
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The graded pieces of the index filtration

Let `m` be a twisting cocycle on `(P, ind)` and `(ℳ, dM)` a differential graded right module.  The
`p`-th graded piece `F_p / F_{p-1}` of the index filtration of the twisted complex `ℳ ⊗ ⟨P⟩` is
`⊕_{ind x = p} ℳ ⊗ ⟨x⟩` with the differential `dM` alone: on a family supported on the generators
of index at most `p`, the twisting part of the differential only reaches generators of index
smaller than `p`, because the cocycle is one-sided.

## Main definitions

* `TauCeti.indexGradedPieceSubmodule ind p`: the families `P → M` supported on the generators of
  index `p`.
* `TauCeti.indexRestrict ind p`: the restriction of a family to the generators of index `p`.

## Main results

* `TauCeti.indexRestrict_twistedDifferential`: on the `p`-th piece of the index filtration, the
  restriction to the generators of index `p` intertwines the twisted differential with `dM`.
* `TauCeti.indexRestrict_eq_zero_iff`: on the `p`-th piece, the restriction vanishes exactly on
  the `(p - 1)`-st piece.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 3.38.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 3 and Section 4.2.
-/

public section

open CategoryTheory Limits MulOpposite

namespace TauCeti

universe uR uA uM uP

section Submodule

variable {R : Type uR} {M : Type uM} [Semiring R] [AddCommMonoid M] [Module R M]
  {P : Type uP} (ind : P → ℤ)

/-- The families `P → M` supported on the generators of index `p`. -/
def indexGradedPieceSubmodule (p : ℤ) : Submodule R (P → M) :=
  Submodule.pi {x | ind x ≠ p} fun _ ↦ ⊥

variable {ind}

@[simp]
theorem mem_indexGradedPieceSubmodule_iff {p : ℤ} {f : P → M} :
    f ∈ indexGradedPieceSubmodule (R := R) ind p ↔ ∀ x, ind x ≠ p → f x = 0 := by
  simp [indexGradedPieceSubmodule, Submodule.mem_pi]

/-- A family supported on the generators of index `p` lies in the `p`-th piece of the index
filtration. -/
theorem indexGradedPieceSubmodule_le_indexFiltrationSubmodule (p : ℤ) :
    indexGradedPieceSubmodule (R := R) (M := M) ind p ≤ indexFiltrationSubmodule ind p :=
  fun _ hf ↦ mem_indexFiltrationSubmodule_iff.2 fun x hx ↦
    mem_indexGradedPieceSubmodule_iff.1 hf x hx.ne'

variable (R M ind) in
/-- The restriction of a family `P → M` to the generators of index `p`. -/
def indexRestrict (p : ℤ) : (P → M) →ₗ[R] (P → M) :=
  LinearMap.pi fun x ↦ if ind x = p then LinearMap.proj x else 0

@[simp]
theorem indexRestrict_apply (p : ℤ) (f : P → M) (x : P) :
    indexRestrict R M ind p f x = if ind x = p then f x else 0 := by
  by_cases hx : ind x = p <;> simp [indexRestrict, hx]

theorem indexRestrict_mem_indexGradedPieceSubmodule (p : ℤ) (f : P → M) :
    indexRestrict R M ind p f ∈ indexGradedPieceSubmodule (R := R) ind p :=
  mem_indexGradedPieceSubmodule_iff.2 fun x hx ↦ by simp [hx]

/-- The restriction to the generators of index `p` is the identity on the families supported on
them. -/
theorem indexRestrict_of_mem {p : ℤ} {f : P → M}
    (hf : f ∈ indexGradedPieceSubmodule (R := R) ind p) : indexRestrict R M ind p f = f := by
  funext x
  rw [indexRestrict_apply]
  split_ifs with hx
  · rfl
  · exact (mem_indexGradedPieceSubmodule_iff.1 hf x hx).symm

/-- The restriction to the generators of index `p` preserves the total degree. -/
theorem indexRestrict_mem_twistedTotalGrading {ℳ : ℤ → Submodule R M} {n p : ℤ} {f : P → M}
    (hf : f ∈ twistedTotalGrading ℳ ind n) :
    indexRestrict R M ind p f ∈ twistedTotalGrading ℳ ind n := by
  rw [mem_twistedTotalGrading_iff] at hf ⊢
  intro x
  rw [indexRestrict_apply]
  split_ifs
  · exact hf x
  · exact zero_mem _

/-- On the `p`-th piece of the index filtration, the restriction to the generators of index `p`
vanishes exactly on the `(p - 1)`-st piece. -/
theorem indexRestrict_eq_zero_iff {p : ℤ} {f : P → M}
    (hf : f ∈ indexFiltrationSubmodule (R := R) ind p) :
    indexRestrict R M ind p f = 0 ↔ f ∈ indexFiltrationSubmodule (R := R) ind (p - 1) := by
  rw [mem_indexFiltrationSubmodule_iff] at hf ⊢
  refine ⟨fun h x hx ↦ ?_, fun h ↦ funext fun x ↦ ?_⟩
  · rcases eq_or_lt_of_le (Int.sub_one_lt_iff.1 hx) with hxp | hxp
    · simpa [hxp] using congrFun h x
    · exact hf x hxp
  · rw [indexRestrict_apply, Pi.zero_apply]
    split_ifs with hxp
    · exact h x (by omega)
    · rfl

/-- The grading of the `p`-th graded piece of the index filtration: in total degree `n`, the
families of total degree `n` supported on the generators of index `p`. -/
def indexGradedPieceGrading (ℳ : ℤ → Submodule R M) (ind : P → ℤ) (p n : ℤ) :
    Submodule R (P → M) :=
  twistedTotalGrading ℳ ind n ⊓ indexGradedPieceSubmodule ind p

theorem mem_indexGradedPieceGrading_iff {ℳ : ℤ → Submodule R M} {p n : ℤ} {f : P → M} :
    f ∈ indexGradedPieceGrading ℳ ind p n ↔
      f ∈ twistedTotalGrading ℳ ind n ∧ f ∈ indexGradedPieceSubmodule (R := R) ind p :=
  Submodule.mem_inf

end Submodule

section Differential

variable {R : Type uR} {A : Type uA} {M : Type uM} [CommRing R] [Semiring A]
  [AddCommMonoid M] [Module R M] [Module Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {P : Type uP} [Fintype P] {ind : P → ℤ}
  (m : P → P → A) {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] (dM : M →ₗ[R] M)

/-- **The differential on a graded piece of the index filtration.** On the `p`-th piece, the
restriction to the generators of index `p` intertwines the twisted differential of a matrix
vanishing on pairs `ind x ≤ ind y` with the differential `dM` applied to every component, that is,
with the twisted differential of the zero matrix. -/
theorem indexRestrict_twistedDifferential (hm : ∀ x y, ind x ≤ ind y → m x y = 0)
    {p : ℤ} {f : P → M} (hf : f ∈ indexFiltrationSubmodule (R := R) ind p) :
    indexRestrict R M ind p (twistedDifferential m ℳ dM f) =
      twistedDifferential (fun _ _ ↦ (0 : A)) ℳ dM (indexRestrict R M ind p f) := by
  rw [mem_indexFiltrationSubmodule_iff] at hf
  funext y
  rw [indexRestrict_apply, twistedDifferential_apply, twistedDifferential_apply,
    indexRestrict_apply]
  simp only [MulOpposite.op_zero, zero_smul, Finset.sum_const_zero, add_zero]
  split_ifs with hy
  · rw [Finset.sum_eq_zero fun x _ ↦ ?_, add_zero]
    rcases le_or_gt (ind x) p with hx | hx
    · rw [hm x y (hy ▸ hx), MulOpposite.op_zero, zero_smul]
    · rw [hf x hx, map_zero, smul_zero]
  · exact (map_zero dM).symm

/-- The differential `dM`, applied to every component, preserves the graded pieces. -/
theorem twistedDifferential_zero_mem_indexGradedPieceGrading
    (hdM : LinearMap.IsHomogeneous dM ℳ ℳ 1) {p n : ℤ} {f : P → M}
    (hf : f ∈ indexGradedPieceGrading ℳ ind p n) :
    twistedDifferential (fun _ _ ↦ (0 : A)) ℳ dM f ∈ indexGradedPieceGrading ℳ ind p (n + 1) := by
  rw [mem_indexGradedPieceGrading_iff] at hf ⊢
  refine ⟨mem_twistedTotalGrading_iff.2 fun y ↦ ?_,
    mem_indexGradedPieceSubmodule_iff.2 fun y hy ↦ ?_⟩
  · have hy := hdM.map_mem (mem_twistedTotalGrading_iff.1 hf.1 y)
    rw [show n + ind y + 1 = n + 1 + ind y by ring] at hy
    simpa using hy
  · rw [twistedDifferential_apply, mem_indexGradedPieceSubmodule_iff.1 hf.2 y hy, map_zero]
    simp

end Differential

section Complex

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {P : Type uP} [Fintype P] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] {dM : M →ₗ[R] M}
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]

variable (ind : P → ℤ) (hM : IsDGRightModule h ℳ dM)

/-- **The `p`-th graded piece of the index filtration**, as a cochain complex: in total degree `n`
the families of total degree `n` supported on the generators of index `p`, with the differential
`dM` applied to every component. -/
noncomputable def indexGradedPieceComplex (p : ℤ) : CochainComplex (ModuleCat.{max uP uM} R) ℤ :=
  gradedCochainComplex (indexGradedPieceGrading ℳ ind p)
    (twistedDifferential (fun _ _ ↦ (0 : A)) ℳ dM)
    (LinearMap.isHomogeneous_def.mpr fun _ _ hf ↦
      twistedDifferential_zero_mem_indexGradedPieceGrading dM hM.isHomogeneous hf)
    fun _ f ↦ (0 : TwistingCocycle 𝒜 d P ind).twistedDifferential_sq_zero dM hM f

/-- The degree-`n` term of the `p`-th graded piece is the module of families of total degree `n`
supported on the generators of index `p`. -/
noncomputable def indexGradedPieceComplexXEquiv (p n : ℤ) :
    (indexGradedPieceComplex ind hM p).X n ≃ₗ[R] indexGradedPieceGrading ℳ ind p n :=
  gradedCochainComplexXEquiv n

/-- The differential of the `p`-th graded piece is `dM`, applied to every component. -/
theorem indexGradedPieceComplexXEquiv_d (p n : ℤ) (f : (indexGradedPieceComplex ind hM p).X n) :
    (indexGradedPieceComplexXEquiv ind hM p (n + 1)
        (((indexGradedPieceComplex ind hM p).d n (n + 1)).hom f) : P → M) =
      twistedDifferential (fun _ _ ↦ (0 : A)) ℳ dM (indexGradedPieceComplexXEquiv ind hM p n f) :=
  gradedCochainComplexXEquiv_d n f

end Complex

namespace TwistingCocycle

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {P : Type uP} {ind : P → ℤ}
  [Fintype P] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] {dM : M →ₗ[R] M}
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  (m : TwistingCocycle 𝒜 d P ind) (hM : IsDGRightModule h ℳ dM)

/-- The restriction to the generators of index `p`, from the degree-`n` term of the twisted
complex to that of the `p`-th graded piece. -/
noncomputable def indexRestrictX (p n : ℤ) :
    (m.twistedCochainComplex dM hM).X n →ₗ[R] (indexGradedPieceComplex ind hM p).X n :=
  (indexGradedPieceComplexXEquiv ind hM p n).symm.toLinearMap ∘ₗ
    ((indexRestrict R M ind p ∘ₗ (twistedTotalGrading ℳ ind n).subtype ∘ₗ
      (twistedCochainComplexXEquiv m.mem_graded m.twisting hM n).toLinearMap).codRestrict _
        fun f ↦ mem_indexGradedPieceGrading_iff.2
          ⟨indexRestrict_mem_twistedTotalGrading (twistedCochainComplexXEquiv _ _ hM n f).2,
            indexRestrict_mem_indexGradedPieceSubmodule p _⟩)

@[simp]
theorem indexGradedPieceComplexXEquiv_indexRestrictX (p n : ℤ)
    (f : (m.twistedCochainComplex dM hM).X n) :
    (indexGradedPieceComplexXEquiv ind hM p n (m.indexRestrictX hM p n f) : P → M) =
      indexRestrict R M ind p (twistedCochainComplexXEquiv m.mem_graded m.twisting hM n f) := by
  simp [indexRestrictX]

/-- **The projection of a piece of the index filtration onto its graded piece**: the restriction
of the families of the `p`-th piece to the generators of index `p`, a morphism of cochain
complexes since the twisting part of the differential only reaches generators of smaller index.
-/
noncomputable def indexGradedPieceProj (p : ℤ) :
    (m.indexFiltration dM hM p : CochainComplex (ModuleCat.{max uP uM} R) ℤ) ⟶
      indexGradedPieceComplex ind hM p where
  f n := ModuleCat.ofHom (m.indexRestrictX hM p n ∘ₗ ((m.indexFiltration dM hM p).arrow.f n).hom)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦
      (indexGradedPieceComplexXEquiv ind hM p (i + 1)).injective (Subtype.ext ?_))
    have hc := congrArg (fun φ ↦ ModuleCat.Hom.hom φ x)
      ((m.indexFiltration dM hM p).arrow.comm i (i + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
    rw [indexGradedPieceComplexXEquiv_d, indexGradedPieceComplexXEquiv_indexRestrictX,
      indexGradedPieceComplexXEquiv_indexRestrictX, ← hc, twistedCochainComplexXEquiv_d]
    exact (indexRestrict_twistedDifferential (ℳ := ℳ) m.m dM (fun x y hxy ↦ m.one_sided x y hxy)
      (mem_indexFiltrationSubmodule_iff.2
        ((m.mem_range_indexFiltration_arrow_f_iff dM hM p i _).1 ⟨x, rfl⟩))).symm

/-- The projection onto the `p`-th graded piece restricts a family to the generators of index
`p`. -/
@[simp]
theorem indexGradedPieceComplexXEquiv_indexGradedPieceProj (p n : ℤ)
    (x : (m.indexFiltration dM hM p : CochainComplex (ModuleCat.{max uP uM} R) ℤ).X n) :
    (indexGradedPieceComplexXEquiv ind hM p n (((m.indexGradedPieceProj hM p).f n).hom x) :
        P → M) =
      indexRestrict R M ind p (twistedCochainComplexXEquiv m.mem_graded m.twisting hM n
        (((m.indexFiltration dM hM p).arrow.f n).hom x)) := by
  simp [indexGradedPieceProj]

section ShortExact

variable {q p : ℤ} (hqp : q + 1 = p)

/-- The inclusion of the `q`-th piece of the index filtration into the `p`-th, for `q + 1 = p`. -/
noncomputable abbrev indexFiltrationOfLE :
    (m.indexFiltration dM hM q : CochainComplex (ModuleCat.{max uP uM} R) ℤ) ⟶
      (m.indexFiltration dM hM p : CochainComplex (ModuleCat.{max uP uM} R) ℤ) :=
  Subobject.ofLE _ _ (m.monotone_indexFiltration dM hM (by omega))

private theorem arrow_f_indexFiltrationOfLE_apply (n : ℤ)
    (x : (m.indexFiltration dM hM q : CochainComplex (ModuleCat.{max uP uM} R) ℤ).X n) :
    ((m.indexFiltration dM hM p).arrow.f n).hom (((m.indexFiltrationOfLE hM hqp).f n).hom x) =
      ((m.indexFiltration dM hM q).arrow.f n).hom x := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.comp_f,
    Subobject.ofLE_arrow]

/-- The short complex `F_q ⟶ F_p ⟶ F_p / F_q` of the index filtration, for `q + 1 = p`, with the
graded piece described by `indexGradedPieceComplex`. -/
noncomputable def indexGradedPieceShortComplex :
    ShortComplex (CochainComplex (ModuleCat.{max uP uM} R) ℤ) :=
  ShortComplex.mk (m.indexFiltrationOfLE hM hqp) (m.indexGradedPieceProj hM p) (by
    refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦
      (indexGradedPieceComplexXEquiv ind hM p n).injective (Subtype.ext ?_))
    rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      indexGradedPieceComplexXEquiv_indexGradedPieceProj, arrow_f_indexFiltrationOfLE_apply,
      HomologicalComplex.zero_f, ModuleCat.hom_zero, LinearMap.zero_apply, map_zero,
      ZeroMemClass.coe_zero]
    have hq := (m.mem_range_indexFiltration_arrow_f_iff dM hM q n _).1 ⟨x, rfl⟩
    refine (indexRestrict_eq_zero_iff (R := R) (mem_indexFiltrationSubmodule_iff.2
      fun y hy ↦ hq y (by omega))).2 ?_
    rw [show p - 1 = q by omega, mem_indexFiltrationSubmodule_iff]
    exact hq)

/-- **The graded pieces of the index filtration**: the short complex
`F_q ⟶ F_p ⟶ indexGradedPieceComplex ind hM p` is short exact for `q + 1 = p`. -/
theorem indexGradedPieceShortComplex_shortExact :
    (m.indexGradedPieceShortComplex hM hqp).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ ?_
  have hinj (k : ℤ) : Function.Injective ((m.indexFiltration dM hM k).arrow.f n).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  refine ShortComplex.ShortExact.mk' ?_ ((ModuleCat.mono_iff_injective _).2 fun x y hxy ↦ ?_)
    ((ModuleCat.epi_iff_surjective _).2 fun y ↦ ?_)
  · refine (ShortComplex.moduleCat_exact_iff_ker_sub_range _).2 fun x hx ↦ ?_
    have hx₀ : ((m.indexGradedPieceProj hM p).f n).hom x = 0 := LinearMap.mem_ker.1 hx
    have hx' := (m.indexGradedPieceComplexXEquiv_indexGradedPieceProj hM p n x).symm.trans
      (by rw [hx₀, map_zero, ZeroMemClass.coe_zero])
    have hq := (indexRestrict_eq_zero_iff (R := R) (mem_indexFiltrationSubmodule_iff.2
      ((m.mem_range_indexFiltration_arrow_f_iff dM hM p n _).1 ⟨x, rfl⟩))).1 hx'
    rw [show p - 1 = q by omega, mem_indexFiltrationSubmodule_iff] at hq
    obtain ⟨w, hw⟩ := (m.mem_range_indexFiltration_arrow_f_iff dM hM q n _).2 hq
    exact ⟨w, hinj p ((arrow_f_indexFiltrationOfLE_apply m hM hqp n w).trans hw)⟩
  · exact hinj q ((arrow_f_indexFiltrationOfLE_apply m hM hqp n x).symm.trans
      ((congrArg ((m.indexFiltration dM hM p).arrow.f n).hom hxy).trans
        (arrow_f_indexFiltrationOfLE_apply m hM hqp n y)))
  · set g := indexGradedPieceComplexXEquiv ind hM p n y with hg_def
    have hg := mem_indexGradedPieceGrading_iff.1 g.2
    obtain ⟨t, ht⟩ : ∃ t, twistedCochainComplexXEquiv m.mem_graded m.twisting hM n t =
        ⟨g, hg.1⟩ := ⟨_, LinearEquiv.apply_symm_apply _ _⟩
    obtain ⟨s, hs⟩ := (m.mem_range_indexFiltration_arrow_f_iff dM hM p n t).2 (by
      rw [ht]
      exact mem_indexFiltrationSubmodule_iff.1
        (indexGradedPieceSubmodule_le_indexFiltrationSubmodule p hg.2))
    refine ⟨s, (indexGradedPieceComplexXEquiv ind hM p n).injective (Subtype.ext ?_)⟩
    change (indexGradedPieceComplexXEquiv ind hM p n
      (((m.indexGradedPieceProj hM p).f n).hom s) : P → M) = g
    rw [indexGradedPieceComplexXEquiv_indexGradedPieceProj, hs, ht]
    exact indexRestrict_of_mem hg.2

end ShortExact

section FirstPage

/-- The object at `n : ℤ` of the functor of the index filtration is the `n`-th piece. -/
noncomputable def indexFiltrationFunctorObjIso (n : ℤ) :
    (CochainComplex.filtrationFunctor (m.indexFiltration dM hM)
        (m.monotone_indexFiltration dM hM)).obj n ≅
      (m.indexFiltration dM hM n : CochainComplex (ModuleCat.{max uP uM} R) ℤ) :=
  CochainComplex.filtrationFunctorObjIso _ _ n ≪≫
    eqToIso congr(($(CochainComplex.filtrationEInt_coe (m.indexFiltration dM hM) n) :
      CochainComplex (ModuleCat.{max uP uM} R) ℤ))

/-- Under `indexFiltrationFunctorObjIso`, the inclusion of the `n`-th piece into the twisted
complex is that of the functor of the index filtration. -/
@[reassoc (attr := simp)]
theorem indexFiltrationFunctorObjIso_hom_arrow (n : ℤ) :
    (m.indexFiltrationFunctorObjIso hM n).hom ≫ (m.indexFiltration dM hM n).arrow =
      (CochainComplex.filtrationFunctorObjIso _ _ n).hom ≫
        (CochainComplex.filtrationEInt (m.indexFiltration dM hM) n).arrow := by
  rw [indexFiltrationFunctorObjIso, Iso.trans_hom, eqToIso.hom, Category.assoc,
    Subobject.arrow_congr _ _ (CochainComplex.filtrationEInt_coe _ n)]

variable (q : ℤ)

private theorem indexFiltrationFunctor_map_comp_objIso_hom :
    (CochainComplex.filtrationFunctor (m.indexFiltration dM hM)
        (m.monotone_indexFiltration dM hM)).map
          (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : q = q) rfl)) ≫
        (m.indexFiltrationFunctorObjIso hM (q + 1)).hom =
      (m.indexFiltrationFunctorObjIso hM q).hom ≫
        m.indexFiltrationOfLE hM (q := q) (p := q + 1) rfl := by
  rw [← cancel_mono (m.indexFiltration dM hM (q + 1)).arrow, Category.assoc,
    indexFiltrationFunctorObjIso_hom_arrow, Category.assoc, Subobject.ofLE_arrow,
    indexFiltrationFunctorObjIso_hom_arrow, ← Category.assoc,
    CochainComplex.filtrationFunctor_map_comp_objIso_hom, Category.assoc, Subobject.ofLE_arrow]

/-- The short complex `F_q ⟶ F_{q+1} ⟶ indexGradedPieceComplex ind hM (q + 1)` written with the
transition map of the functor of the index filtration. -/
private noncomputable def indexGradedPieceShortComplex' :
    ShortComplex (CochainComplex (ModuleCat.{max uP uM} R) ℤ) :=
  ShortComplex.mk ((CochainComplex.filtrationFunctor (m.indexFiltration dM hM)
      (m.monotone_indexFiltration dM hM)).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : q = q) rfl)))
    ((m.indexFiltrationFunctorObjIso hM (q + 1)).hom ≫ m.indexGradedPieceProj hM (q + 1)) (by
      rw [← Category.assoc, indexFiltrationFunctor_map_comp_objIso_hom, Category.assoc]
      exact (congrArg _
        (m.indexGradedPieceShortComplex hM (q := q) (p := q + 1) rfl).zero).trans comp_zero)

private noncomputable def indexGradedPieceShortComplexIso :
    m.indexGradedPieceShortComplex' hM q ≅
      m.indexGradedPieceShortComplex hM (q := q) (p := q + 1) rfl :=
  ShortComplex.isoMk (m.indexFiltrationFunctorObjIso hM q)
    (m.indexFiltrationFunctorObjIso hM (q + 1)) (Iso.refl _)
    (m.indexFiltrationFunctor_map_comp_objIso_hom hM q).symm
    (Category.comp_id _).symm

private theorem indexGradedPieceShortComplex'_shortExact :
    (m.indexGradedPieceShortComplex' hM q).ShortExact :=
  ShortComplex.shortExact_of_iso (m.indexGradedPieceShortComplexIso hM q).symm
    (m.indexGradedPieceShortComplex_shortExact hM (q := q) (p := q + 1) rfl)

/-- **The graded pieces of the index filtration**: the cokernel of the inclusion
`F_q ⟶ F_{q+1}` of the functor of the index filtration is `indexGradedPieceComplex ind hM (q + 1)`,
the families supported on the generators of index `q + 1` with the differential `dM`. -/
noncomputable def indexFiltrationCokernelIso :
    cokernel ((CochainComplex.filtrationFunctor (m.indexFiltration dM hM)
      (m.monotone_indexFiltration dM hM)).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : q = q) rfl))) ≅
      indexGradedPieceComplex ind hM (q + 1) :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _)
    (m.indexGradedPieceShortComplex'_shortExact hM q).gIsCokernel

/-- Under `indexFiltrationCokernelIso`, the projection onto the cokernel is the restriction to the
generators of index `q + 1`. -/
@[reassoc (attr := simp)]
theorem cokernel_π_indexFiltrationCokernelIso_hom :
    cokernel.π _ ≫ (m.indexFiltrationCokernelIso hM q).hom =
      (m.indexFiltrationFunctorObjIso hM (q + 1)).hom ≫ m.indexGradedPieceProj hM (q + 1) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
    (m.indexGradedPieceShortComplex'_shortExact hM q).gIsCokernel WalkingParallelPair.one

/-- **The first page of the index spectral sequence** (page `2` in Mathlib's numbering): the
object at `(p, q)` is the cohomology in degree `n = p + q` of the graded piece of the generators
of index `q + 1`, that is of `⊕_{ind x = q + 1} ℳ ⊗ ⟨x⟩` with the differential `dM`. -/
noncomputable def indexSpectralSequenceFirstPageXIso (pq : ℤ × ℤ) (n : ℤ)
    (hn : n = pq.1 + pq.2) :
    ((m.indexSpectralSequence dM hM).page 2).X pq ≅
      (indexGradedPieceComplex ind hM (pq.2 + 1)).homology n :=
  CochainComplex.spectralSequenceFirstPageXIsoCokernel _ pq pq.2 (pq.2 + 1) rfl rfl n hn ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso (m.indexFiltrationCokernelIso hM pq.2)

end FirstPage

end TwistingCocycle

end TauCeti

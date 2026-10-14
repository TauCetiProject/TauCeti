/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import TauCeti.Algebra.Homology.DG.Twisted.Complex
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.SpectralObject
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# The index filtration of a twisted complex

Let `m` be a twisting cocycle on the finite set `P` graded by `ind`, with values in a
differential graded algebra `(𝒜, d)`, and let `(ℳ, dM)` be a differential graded right module.
The **index filtration** of the twisted complex `ℳ ⊗ ⟨P⟩` is the increasing filtration by the
subcomplexes

`F_p = ⊕_{ind x ≤ p} ℳ ⊗ ⟨x⟩`.

It is a filtration by subcomplexes because `m` is one-sided: the coefficient `m x y` vanishes
unless `ind y < ind x`, so the twisted differential never raises the index of a generator.  (The
equation `D² = 0` does not need one-sidedness; the filtration does.)  Since `P` is finite, the
filtration is finite: `F_p = 0` below the smallest index, and `F_p` is the whole twisted complex
from the largest index on.

The graded piece `F_{p+1} / F_p` is the twisted complex `ℳ ⊗ ⟨P_{p+1}⟩` of the **zero** cocycle
on the generators `P_{p+1} = {x | ind x = p + 1}` of index `p + 1`: between these generators the
twisted differential has no component, again by one-sidedness, and only `dM` survives.  We prove
this through the short exact sequence of complexes `F_p ⟶ F_{p+1} ⟶ ℳ ⊗ ⟨P_{p+1}⟩`, whose second
map restricts a function on `P` to `P_{p+1}`.  Consequently the first page of the spectral
sequence of the index filtration is the cohomology of the untwisted complexes `ℳ ⊗ ⟨P_p⟩`.

## Main definitions

* `TauCeti.twistedIndexFiltration ℳ ind p n`: the degree-`n` part of `F_p`, as a submodule of
  `P → M`.
* `TauCeti.TwistingCocycle.indexFiltrationComplex m dM hM p`: the subcomplex `F_p`.
* `TauCeti.TwistingCocycle.indexFiltrationι`: its inclusion into the twisted complex, and
  `TauCeti.TwistingCocycle.indexFiltrationComplexMap` the inclusion `F_p ⟶ F_q` for `p ≤ q`.
* `TauCeti.TwistingCocycle.indexFiltration m dM hM`: the index filtration, as an increasing
  family of subobjects of the twisted cochain complex.
* `TauCeti.TwistingCocycle.indexFiltrationFunctor m dM hM`: the same filtration as a functor
  `EInt ⥤ CochainComplex`, with `indexFiltrationFunctorObjIso` identifying its value at `p` with
  `F_p`.
* `TauCeti.TwistingCocycle.indexSpectralSequence m dM hM`: its spectral sequence.
* `TauCeti.TwistingCocycle.indexFiltrationProj`: the restriction `F_p ⟶ ℳ ⊗ ⟨P_p⟩`.
* `TauCeti.TwistingCocycle.indexFiltrationShortComplex`: the short complex
  `F_p ⟶ F_{p+1} ⟶ ℳ ⊗ ⟨P_{p+1}⟩`.
* `TauCeti.TwistingCocycle.indexFiltrationCokernelIso`: the graded piece `F_{p+1} / F_p` is
  `ℳ ⊗ ⟨P_{p+1}⟩`.

## Main results

* `TauCeti.twistedDifferential_mem_twistedIndexFiltration`: the twisted differential of a
  one-sided matrix preserves the index filtration.
* `TauCeti.TwistingCocycle.monotone_indexFiltration`, `indexFiltration_eq_bot`,
  `indexFiltration_eq_top`: the index filtration is increasing and finite.
* `TauCeti.TwistingCocycle.indexFiltrationShortComplex_shortExact`: the sequence
  `F_p ⟶ F_{p+1} ⟶ ℳ ⊗ ⟨P_{p+1}⟩` is short exact.
* `TauCeti.TwistingCocycle.indexSpectralSequenceFirstPageXIso`: the object at `(p, q)` of the
  first page of the index spectral sequence is `H^{p+q}(ℳ ⊗ ⟨P_{q+1}⟩)`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 3.38.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 4.
-/

public section

open CategoryTheory Limits MulOpposite

namespace TauCeti

universe uR uA uM uP

section Submodule

variable {R : Type uR} {M : Type uM} [Semiring R] [AddCommMonoid M] [Module R M]
  {P : Type uP}

/-- The degree-`n` part of the `p`th step of the index filtration of `ℳ ⊗ ⟨P⟩`, identified with
`P → M`: the functions of total degree `n` supported on the generators of index at most `p`. -/
def twistedIndexFiltration (ℳ : ℤ → Submodule R M) (ind : P → ℤ) (p n : ℤ) :
    Submodule R (P → M) :=
  twistedTotalGrading ℳ ind n ⊓ Submodule.pi {x | p < ind x} fun _ ↦ ⊥

variable {ℳ : ℤ → Submodule R M} {ind : P → ℤ}

@[simp]
theorem mem_twistedIndexFiltration_iff {p n : ℤ} {f : P → M} :
    f ∈ twistedIndexFiltration ℳ ind p n ↔
      f ∈ twistedTotalGrading ℳ ind n ∧ ∀ x, p < ind x → f x = 0 := by
  simp [twistedIndexFiltration, Submodule.mem_pi]

/-- The index filtration is a filtration of each graded piece of the twisted complex. -/
theorem twistedIndexFiltration_le_twistedTotalGrading (p n : ℤ) :
    twistedIndexFiltration ℳ ind p n ≤ twistedTotalGrading ℳ ind n :=
  inf_le_left

/-- The index filtration is increasing. -/
theorem twistedIndexFiltration_mono {p q : ℤ} (hpq : p ≤ q) (n : ℤ) :
    twistedIndexFiltration ℳ ind p n ≤ twistedIndexFiltration ℳ ind q n := fun f hf ↦ by
  rw [mem_twistedIndexFiltration_iff] at hf ⊢
  exact ⟨hf.1, fun x hx ↦ hf.2 x (hpq.trans_lt hx)⟩

/-- Below the smallest index, the index filtration vanishes. -/
theorem twistedIndexFiltration_eq_bot {p : ℤ} (hp : ∀ x, p < ind x) (n : ℤ) :
    twistedIndexFiltration ℳ ind p n = ⊥ := by
  refine eq_bot_iff.mpr fun f hf ↦ ?_
  rw [mem_twistedIndexFiltration_iff] at hf
  exact (Submodule.mem_bot R).mpr (funext fun x ↦ hf.2 x (hp x))

/-- From the largest index on, the index filtration is everything. -/
theorem twistedIndexFiltration_eq_twistedTotalGrading {p : ℤ} (hp : ∀ x, ind x ≤ p) (n : ℤ) :
    twistedIndexFiltration ℳ ind p n = twistedTotalGrading ℳ ind n := by
  refine le_antisymm (twistedIndexFiltration_le_twistedTotalGrading p n) fun f hf ↦ ?_
  rw [mem_twistedIndexFiltration_iff]
  exact ⟨hf, fun x hx ↦ absurd (hp x) (not_le.mpr hx)⟩

end Submodule

section Differential

variable {R : Type uR} {A : Type uA} {M : Type uM} [CommRing R] [Semiring A]
  [AddCommMonoid M] [Module R M] [Module Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {P : Type uP} [Fintype P] {ind : P → ℤ} (m : P → P → A) {ℳ : ℤ → Submodule R M}
  [DirectSum.Decomposition ℳ] (dM : M →ₗ[R] M)

/-- The twisted differential of a one-sided matrix vanishes, at a generator `y`, on the
functions supported on the generators of index at most `ind y`, apart from the term `dM (f y)`. -/
theorem twistedDifferential_apply_of_one_sided (hm : ∀ x y, ind x ≤ ind y → m x y = 0)
    {f : P → M} {y : P} (hf : ∀ x, ind y < ind x → f x = 0) :
    twistedDifferential m ℳ dM f y = dM (f y) := by
  rw [twistedDifferential_apply, Finset.sum_eq_zero fun x _ ↦ ?_, add_zero]
  rcases le_or_gt (ind x) (ind y) with hx | hx
  · rw [hm x y hx, MulOpposite.op_zero, zero_smul]
  · rw [hf x hx, map_zero, smul_zero]

/-- The restriction to the generators of index `p` of a function supported on the generators of
index at most `p` intertwines the twisted differential of a one-sided matrix with that of the zero
matrix, which is `dM` on each generator. -/
theorem twistedDifferential_funLeft_val (hm : ∀ x y, ind x ≤ ind y → m x y = 0) {p : ℤ}
    {f : P → M} (hf : ∀ x, p < ind x → f x = 0) :
    twistedDifferential (0 : {x // ind x = p} → {x // ind x = p} → A) ℳ dM
        (LinearMap.funLeft R M Subtype.val f) =
      LinearMap.funLeft R M Subtype.val (twistedDifferential m ℳ dM f) := by
  funext y
  rw [LinearMap.funLeft_apply, twistedDifferential_apply_of_one_sided m dM hm
    fun x hx ↦ hf x (y.2.symm.trans_lt hx)]
  simp

end Differential

section Complex

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {P : Type uP} [Fintype P] {ind : P → ℤ}
  [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]

omit [IsScalarTower R Aᵐᵒᵖ M] in
/-- The twisted differential of a one-sided matrix with homogeneous entries of degree
`ind y - ind x + 1` preserves the index filtration, for any homogeneous `dM` of degree one. -/
theorem twistedDifferential_mem_twistedIndexFiltration (m : P → P → A) (dM : M →ₗ[R] M)
    (hm : ∀ x y, m x y ∈ 𝒜 (ind y - ind x + 1)) (hos : ∀ x y, ind x ≤ ind y → m x y = 0)
    (hdM : LinearMap.IsHomogeneous dM ℳ ℳ 1) {p n : ℤ} {f : P → M}
    (hf : f ∈ twistedIndexFiltration ℳ ind p n) :
    twistedDifferential m ℳ dM f ∈ twistedIndexFiltration ℳ ind p (n + 1) := by
  rw [mem_twistedIndexFiltration_iff] at hf ⊢
  refine ⟨twistedDifferential_mem_twistedTotalGrading m dM hm hdM hf.1, fun y hy ↦ ?_⟩
  rw [twistedDifferential_apply_of_one_sided m dM hos fun x hx ↦ hf.2 x (hy.trans hx),
    hf.2 y hy, map_zero]

namespace TwistingCocycle

variable (m : TwistingCocycle 𝒜 d P ind) (dM : M →ₗ[R] M) (hM : IsDGRightModule h ℳ dM)

/-! ### The subcomplexes of the index filtration -/

/-- The `p`th step `F_p = ⊕_{ind x ≤ p} ℳ ⊗ ⟨x⟩` of the index filtration of the twisted complex of
a twisting cocycle, as a cochain complex of `R`-modules: the degree-`n` term is
`twistedIndexFiltration ℳ ind p n` and the differential is the restriction of the twisted
differential. -/
noncomputable def indexFiltrationComplex (p : ℤ) : CochainComplex (ModuleCat.{max uP uM} R) ℤ :=
  gradedCochainComplex (twistedIndexFiltration ℳ ind p) (twistedDifferential m.m ℳ dM)
    (LinearMap.isHomogeneous_def.mpr fun _ _ hf ↦
      twistedDifferential_mem_twistedIndexFiltration m.m dM m.mem_graded m.one_sided
        hM.isHomogeneous hf)
    fun _ f ↦ m.twistedDifferential_sq_zero dM hM f

/-- The degree-`n` term of `F_p` is the submodule `twistedIndexFiltration ℳ ind p n` of `P → M`,
as a linear equivalence. -/
noncomputable def indexFiltrationComplexXEquiv (p n : ℤ) :
    (m.indexFiltrationComplex dM hM p).X n ≃ₗ[R] twistedIndexFiltration ℳ ind p n :=
  gradedCochainComplexXEquiv n

/-- Under `indexFiltrationComplexXEquiv`, the differential of `F_p` is the twisted
differential. -/
theorem indexFiltrationComplexXEquiv_d (p n : ℤ) (f : (m.indexFiltrationComplex dM hM p).X n) :
    (m.indexFiltrationComplexXEquiv dM hM p (n + 1)
        (((m.indexFiltrationComplex dM hM p).d n (n + 1)).hom f) : P → M) =
      twistedDifferential m.m ℳ dM (m.indexFiltrationComplexXEquiv dM hM p n f) :=
  gradedCochainComplexXEquiv_d n f

/-- The inclusion of the subcomplex `F_p` into the twisted complex. -/
noncomputable def indexFiltrationι (p : ℤ) :
    m.indexFiltrationComplex dM hM p ⟶ m.twistedCochainComplex dM hM where
  f n := ModuleCat.ofHom
    ((twistedCochainComplexXEquiv m.mem_graded m.twisting hM n).symm.toLinearMap ∘ₗ
      Submodule.inclusion (twistedIndexFiltration_le_twistedTotalGrading p n) ∘ₗ
        (m.indexFiltrationComplexXEquiv dM hM p n).toLinearMap)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    refine ModuleCat.hom_ext (LinearMap.ext fun f ↦
      (twistedCochainComplexXEquiv m.mem_graded m.twisting hM (i + 1)).injective
        (Subtype.ext ?_))
    simp [twistedCochainComplexXEquiv_d, indexFiltrationComplexXEquiv_d]

@[simp]
theorem indexFiltrationι_f_apply (p n : ℤ) (f : (m.indexFiltrationComplex dM hM p).X n) :
    (twistedCochainComplexXEquiv m.mem_graded m.twisting hM n
        (((m.indexFiltrationι dM hM p).f n).hom f) : P → M) =
      m.indexFiltrationComplexXEquiv dM hM p n f := by
  simp [indexFiltrationι]

/-- The inclusion of `F_p` into the twisted complex is injective in each degree. -/
theorem injective_indexFiltrationι_f (p n : ℤ) :
    Function.Injective ((m.indexFiltrationι dM hM p).f n) := by
  intro f g hfg
  have := congrArg (fun x ↦ (twistedCochainComplexXEquiv m.mem_graded m.twisting hM n x : P → M))
    hfg
  simp only [indexFiltrationι_f_apply] at this
  exact (m.indexFiltrationComplexXEquiv dM hM p n).injective (Subtype.ext this)

instance (p : ℤ) : Mono (m.indexFiltrationι dM hM p) :=
  HomologicalComplex.mono_of_mono_f _ fun n ↦
    (ModuleCat.mono_iff_injective _).mpr (m.injective_indexFiltrationι_f dM hM p n)

/-- The inclusion `F_p ⟶ F_q` of subcomplexes of the index filtration, for `p ≤ q`. -/
noncomputable def indexFiltrationComplexMap {p q : ℤ} (hpq : p ≤ q) :
    m.indexFiltrationComplex dM hM p ⟶ m.indexFiltrationComplex dM hM q where
  f n := ModuleCat.ofHom
    ((m.indexFiltrationComplexXEquiv dM hM q n).symm.toLinearMap ∘ₗ
      Submodule.inclusion (twistedIndexFiltration_mono hpq n) ∘ₗ
        (m.indexFiltrationComplexXEquiv dM hM p n).toLinearMap)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    refine ModuleCat.hom_ext (LinearMap.ext fun f ↦
      (m.indexFiltrationComplexXEquiv dM hM q (i + 1)).injective (Subtype.ext ?_))
    simp [indexFiltrationComplexXEquiv_d]

@[simp]
theorem indexFiltrationComplexMap_f_apply {p q : ℤ} (hpq : p ≤ q) (n : ℤ)
    (f : (m.indexFiltrationComplex dM hM p).X n) :
    (m.indexFiltrationComplexXEquiv dM hM q n
        (((m.indexFiltrationComplexMap dM hM hpq).f n).hom f) : P → M) =
      m.indexFiltrationComplexXEquiv dM hM p n f := by
  simp [indexFiltrationComplexMap]

@[reassoc (attr := simp)]
theorem indexFiltrationComplexMap_comp_indexFiltrationι {p q : ℤ} (hpq : p ≤ q) :
    m.indexFiltrationComplexMap dM hM hpq ≫ m.indexFiltrationι dM hM q =
      m.indexFiltrationι dM hM p := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext (LinearMap.ext fun f ↦
    (twistedCochainComplexXEquiv m.mem_graded m.twisting hM n).injective (Subtype.ext ?_))
  simp

/-! ### The index filtration -/

/-- The **index filtration** of the twisted complex of a twisting cocycle: its `p`th step is the
subcomplex `F_p = ⊕_{ind x ≤ p} ℳ ⊗ ⟨x⟩`. -/
noncomputable def indexFiltration (p : ℤ) : Subobject (m.twistedCochainComplex dM hM) :=
  Subobject.mk (m.indexFiltrationι dM hM p)

theorem indexFiltration_def (p : ℤ) :
    m.indexFiltration dM hM p = Subobject.mk (m.indexFiltrationι dM hM p) :=
  (rfl)

/-- The index filtration is increasing. -/
theorem monotone_indexFiltration : Monotone (m.indexFiltration dM hM) := fun _ _ hpq ↦
  Subobject.mk_le_mk_of_comm _ (m.indexFiltrationComplexMap_comp_indexFiltrationι dM hM hpq)

/-- Below the smallest index, the index filtration is zero. -/
theorem indexFiltration_eq_bot {p : ℤ} (hp : ∀ x, p < ind x) :
    m.indexFiltration dM hM p = ⊥ := by
  rw [indexFiltration, Subobject.mk_eq_bot_iff_zero]
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext (LinearMap.ext fun f ↦
    (twistedCochainComplexXEquiv m.mem_graded m.twisting hM n).injective (Subtype.ext ?_))
  have hf := (mem_twistedIndexFiltration_iff.mp (m.indexFiltrationComplexXEquiv dM hM p n f).2).2
  funext x
  simp [hf x (hp x)]

/-- From the largest index on, the index filtration is the whole twisted complex. -/
theorem indexFiltration_eq_top {p : ℤ} (hp : ∀ x, ind x ≤ p) :
    m.indexFiltration dM hM p = ⊤ := by
  have (n : ℤ) : IsIso ((m.indexFiltrationι dM hM p).f n) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨m.injective_indexFiltrationι_f dM hM p n, fun g ↦ ?_⟩
    have hg : (twistedCochainComplexXEquiv m.mem_graded m.twisting hM n g : P → M) ∈
        twistedIndexFiltration ℳ ind p n := by
      rw [twistedIndexFiltration_eq_twistedTotalGrading hp]
      exact (twistedCochainComplexXEquiv m.mem_graded m.twisting hM n g).2
    refine ⟨(m.indexFiltrationComplexXEquiv dM hM p n).symm ⟨_, hg⟩,
      (twistedCochainComplexXEquiv m.mem_graded m.twisting hM n).injective (Subtype.ext ?_)⟩
    simp
  have := HomologicalComplex.Hom.isIso_of_components (m.indexFiltrationι dM hM p)
  exact Subobject.mk_eq_top_of_isIso _

/-- The index filtration as a functor `EInt ⥤ CochainComplex`, extended by `0` at `⊥` and by the
whole twisted complex at `⊤`. -/
noncomputable abbrev indexFiltrationFunctor : EInt ⥤ CochainComplex (ModuleCat.{max uP uM} R) ℤ :=
  CochainComplex.filtrationFunctor (m.indexFiltration dM hM) (m.monotone_indexFiltration dM hM)

/-- The **spectral sequence of the index filtration** of the twisted complex of a twisting
cocycle; its first page is numbered `2`. -/
noncomputable abbrev indexSpectralSequence :
    SpectralSequence (ModuleCat.{max uP uM} R)
      (fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) 2 :=
  CochainComplex.spectralSequence (m.indexFiltrationFunctor dM hM)

/-! ### The graded pieces of the index filtration -/

/-- The restriction `F_p ⟶ ℳ ⊗ ⟨P_p⟩` from the `p`th step of the index filtration to the twisted
complex of the zero cocycle on the generators `P_p` of index `p`. -/
noncomputable def indexFiltrationProj (p : ℤ) :
    m.indexFiltrationComplex dM hM p ⟶
      (0 : TwistingCocycle 𝒜 d {x // ind x = p} fun x ↦ ind x).twistedCochainComplex dM hM where
  f n := ModuleCat.ofHom
    ((twistedCochainComplexXEquiv (TwistingCocycle.mem_graded 0) (TwistingCocycle.twisting 0) hM
        n).symm.toLinearMap ∘ₗ
      ((LinearMap.funLeft R M Subtype.val).restrict fun f hf ↦ by
        rw [mem_twistedTotalGrading_iff]
        exact fun x ↦ (mem_twistedTotalGrading_iff.mp
          (twistedIndexFiltration_le_twistedTotalGrading p n hf)) x) ∘ₗ
        (m.indexFiltrationComplexXEquiv dM hM p n).toLinearMap)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    refine ModuleCat.hom_ext (LinearMap.ext fun f ↦
      (twistedCochainComplexXEquiv (TwistingCocycle.mem_graded 0) (TwistingCocycle.twisting 0) hM
        (i + 1)).injective (Subtype.ext ?_))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      twistedCochainComplexXEquiv_d, indexFiltrationComplexXEquiv_d, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearMap.restrict_apply]
    exact twistedDifferential_funLeft_val m.m dM m.one_sided
      (mem_twistedIndexFiltration_iff.mp (m.indexFiltrationComplexXEquiv dM hM p i f).2).2

@[simp]
theorem indexFiltrationProj_f_apply (p n : ℤ) (f : (m.indexFiltrationComplex dM hM p).X n) :
    (twistedCochainComplexXEquiv (TwistingCocycle.mem_graded 0) (TwistingCocycle.twisting 0) hM n
        (((m.indexFiltrationProj dM hM p).f n).hom f) : {x // ind x = p} → M) =
      LinearMap.funLeft R M Subtype.val (m.indexFiltrationComplexXEquiv dM hM p n f) := by
  simp [indexFiltrationProj]

/-- The short complex `F_p ⟶ F_{p+1} ⟶ ℳ ⊗ ⟨P_{p+1}⟩` of the index filtration, whose second map
restricts to the generators of index `p + 1`. -/
@[expose, simps]
noncomputable def indexFiltrationShortComplex (p : ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{max uP uM} R) ℤ) :=
  ShortComplex.mk (m.indexFiltrationComplexMap dM hM (Int.le_add_one le_rfl))
    (m.indexFiltrationProj dM hM (p + 1)) <| by
      refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext (LinearMap.ext fun f ↦
        (twistedCochainComplexXEquiv (TwistingCocycle.mem_graded 0) (TwistingCocycle.twisting 0)
          hM n).injective (Subtype.ext ?_))
      funext x
      simpa using (mem_twistedIndexFiltration_iff.mp
        (m.indexFiltrationComplexXEquiv dM hM p n f).2).2 x (x.2.symm ▸ lt_add_one p)

/-- The inclusion `F_p ⟶ F_q` is injective in each degree. -/
theorem injective_indexFiltrationComplexMap_f {p q : ℤ} (hpq : p ≤ q) (n : ℤ) :
    Function.Injective ((m.indexFiltrationComplexMap dM hM hpq).f n) := by
  intro f g hfg
  have := congrArg (fun x ↦ (m.indexFiltrationComplexXEquiv dM hM q n x : P → M)) hfg
  simp only [indexFiltrationComplexMap_f_apply] at this
  exact (m.indexFiltrationComplexXEquiv dM hM p n).injective (Subtype.ext this)

/-- The restriction `F_p ⟶ ℳ ⊗ ⟨P_p⟩` is surjective in each degree: a function on the generators
of index `p` extends by zero to a function supported on the generators of index at most `p`. -/
theorem surjective_indexFiltrationProj_f (p n : ℤ) :
    Function.Surjective ((m.indexFiltrationProj dM hM p).f n) := by
  intro g
  have hg := mem_twistedTotalGrading_iff.mp (twistedCochainComplexXEquiv
    (TwistingCocycle.mem_graded 0) (TwistingCocycle.twisting 0) hM n g).2
  have hf : (fun x ↦ if hx : ind x = p then
      (twistedCochainComplexXEquiv (TwistingCocycle.mem_graded 0) (TwistingCocycle.twisting 0) hM
        n g : {x // ind x = p} → M) ⟨x, hx⟩ else 0) ∈ twistedIndexFiltration ℳ ind p n := by
    refine mem_twistedIndexFiltration_iff.mpr
      ⟨mem_twistedTotalGrading_iff.mpr fun x ↦ ?_,
        fun x hx ↦ dite_eq_right_iff.mpr fun hx' ↦ absurd hx' hx.ne'⟩
    split_ifs with hx
    · exact hg ⟨x, hx⟩
    · exact zero_mem _
  refine ⟨(m.indexFiltrationComplexXEquiv dM hM p n).symm ⟨_, hf⟩,
    (twistedCochainComplexXEquiv (TwistingCocycle.mem_graded 0) (TwistingCocycle.twisting 0) hM
      n).injective (Subtype.ext ?_)⟩
  funext y
  simp [y.2]

/-- An element of `F_{p+1}` whose restriction to the generators of index `p + 1` vanishes comes
from `F_p`. -/
theorem exists_indexFiltrationComplexMap_f_eq (p n : ℤ)
    (g : (m.indexFiltrationComplex dM hM (p + 1)).X n)
    (hg : ((m.indexFiltrationProj dM hM (p + 1)).f n) g = 0) :
    ∃ f, ((m.indexFiltrationComplexMap dM hM (Int.le_add_one le_rfl)).f n) f = g := by
  have hg' := congrArg (fun x ↦ (twistedCochainComplexXEquiv (TwistingCocycle.mem_graded 0)
    (TwistingCocycle.twisting 0) hM n x : {x // ind x = p + 1} → M)) hg
  simp only [indexFiltrationProj_f_apply, map_zero, ZeroMemClass.coe_zero] at hg'
  have hmem :=
    mem_twistedIndexFiltration_iff.mp (m.indexFiltrationComplexXEquiv dM hM (p + 1) n g).2
  have hp : (m.indexFiltrationComplexXEquiv dM hM (p + 1) n g : P → M) ∈
      twistedIndexFiltration ℳ ind p n := by
    refine mem_twistedIndexFiltration_iff.mpr ⟨hmem.1, fun x hx ↦ ?_⟩
    rcases (Int.add_one_le_iff.mpr hx).eq_or_lt with hx' | hx'
    · simpa using congrFun hg' ⟨x, hx'.symm⟩
    · exact hmem.2 x hx'
  refine ⟨(m.indexFiltrationComplexXEquiv dM hM p n).symm ⟨_, hp⟩,
    (m.indexFiltrationComplexXEquiv dM hM (p + 1) n).injective (Subtype.ext ?_)⟩
  simp

/-- **The graded pieces of the index filtration.** The sequence
`F_p ⟶ F_{p+1} ⟶ ℳ ⊗ ⟨P_{p+1}⟩` is short exact: the quotient `F_{p+1} / F_p` is the twisted complex
of the zero cocycle on the generators of index `p + 1`. -/
theorem indexFiltrationShortComplex_shortExact (p : ℤ) :
    (m.indexFiltrationShortComplex dM hM p).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    ShortComplex.ShortExact.mk'
      ((ShortComplex.moduleCat_exact_iff _).mpr (m.exists_indexFiltrationComplexMap_f_eq dM hM p n))
      ((ModuleCat.mono_iff_injective _).mpr
        (m.injective_indexFiltrationComplexMap_f dM hM (Int.le_add_one le_rfl) n))
      ((ModuleCat.epi_iff_surjective _).mpr (m.surjective_indexFiltrationProj_f dM hM (p + 1) n))

/-! ### The first page of the index spectral sequence -/

/-- The step `p` of `indexFiltrationFunctor` is the subcomplex `F_p`. -/
noncomputable def indexFiltrationFunctorObjIso (p : ℤ) :
    (m.indexFiltrationFunctor dM hM).obj p ≅ m.indexFiltrationComplex dM hM p :=
  CochainComplex.filtrationFunctorObjIso _ _ p ≪≫
    eqToIso (congrArg (fun S : Subobject (m.twistedCochainComplex dM hM) ↦
      (S : CochainComplex (ModuleCat.{max uP uM} R) ℤ))
      ((CochainComplex.filtrationEInt_coe _ p).trans (m.indexFiltration_def dM hM p))) ≪≫
    Subobject.underlyingIso (m.indexFiltrationι dM hM p)

/-- The identification of the step `p` of `indexFiltrationFunctor` with `F_p` is compatible with the
inclusions into the twisted complex. -/
@[reassoc (attr := simp)]
theorem indexFiltrationFunctorObjIso_hom_comp_indexFiltrationι (p : ℤ) :
    (m.indexFiltrationFunctorObjIso dM hM p).hom ≫ m.indexFiltrationι dM hM p =
      (CochainComplex.filtrationFunctorObjIso _ _ p).hom ≫
        (CochainComplex.filtrationEInt (m.indexFiltration dM hM) p).arrow := by
  simp only [indexFiltrationFunctorObjIso, Iso.trans_hom, eqToIso.hom, Category.assoc,
    Subobject.underlyingIso_hom_comp_eq_mk]
  exact congrArg _ (Subobject.arrow_congr _ _
    ((CochainComplex.filtrationEInt_coe _ p).trans (m.indexFiltration_def dM hM p)))

/-- The transition map `F_p ⟶ F_{p+1}` of `indexFiltrationFunctor` is the inclusion of
subcomplexes `indexFiltrationComplexMap`. -/
@[reassoc]
theorem indexFiltrationFunctor_map_comp_indexFiltrationFunctorObjIso_hom (p : ℤ) :
    (m.indexFiltrationFunctor dM hM).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : p = p) rfl)) ≫
      (m.indexFiltrationFunctorObjIso dM hM (p + 1)).hom =
    (m.indexFiltrationFunctorObjIso dM hM p).hom ≫
      m.indexFiltrationComplexMap dM hM (Int.le_add_one le_rfl) := by
  rw [← cancel_mono (m.indexFiltrationι dM hM (p + 1)), Category.assoc, Category.assoc,
    indexFiltrationFunctorObjIso_hom_comp_indexFiltrationι,
    indexFiltrationComplexMap_comp_indexFiltrationι,
    indexFiltrationFunctorObjIso_hom_comp_indexFiltrationι, ← Category.assoc,
    CochainComplex.filtrationFunctor_map_comp_objIso_hom, Category.assoc, Subobject.ofLE_arrow]

/-- The graded piece `F_{p+1} / F_p` of the index filtration, the cokernel of the transition map of
`indexFiltrationFunctor`, is the twisted complex of the zero cocycle on the generators of index
`p + 1`. -/
noncomputable def indexFiltrationCokernelIso (p : ℤ) :
    cokernel ((m.indexFiltrationFunctor dM hM).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : p = p) rfl))) ≅
      (0 : TwistingCocycle 𝒜 d {x // ind x = p + 1} fun x ↦ ind x).twistedCochainComplex dM hM :=
  cokernel.mapIso _ (m.indexFiltrationShortComplex dM hM p).f
      (m.indexFiltrationFunctorObjIso dM hM p) (m.indexFiltrationFunctorObjIso dM hM (p + 1))
      (m.indexFiltrationFunctor_map_comp_indexFiltrationFunctorObjIso_hom dM hM p) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso
      (m.indexFiltrationShortComplex_shortExact dM hM p).gIsCokernel

/-- **The first page of the index spectral sequence.** Its object at `(p, q)`, on page `2` in
Mathlib's numbering, is the cohomology `H^{p+q}` of the twisted complex `ℳ ⊗ ⟨P_{q+1}⟩` of the zero
cocycle on the generators of index `q + 1`. -/
noncomputable def indexSpectralSequenceFirstPageXIso (pq : ℤ × ℤ) :
    ((m.indexSpectralSequence dM hM).page 2).X pq ≅
      ((0 : TwistingCocycle 𝒜 d {x // ind x = pq.2 + 1} fun x ↦ ind x).twistedCochainComplex dM
        hM).homology (pq.1 + pq.2) :=
  CochainComplex.spectralSequenceFirstPageXIsoCokernel _ pq pq.2 (pq.2 + 1) rfl rfl _ rfl ≪≫
    (HomologicalComplex.homologyFunctor _ _ _).mapIso (m.indexFiltrationCokernelIso dM hM pq.2)

end TwistingCocycle

end Complex

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Complex
-- Reuse its graded-complex construction privately; callers use the characteristic equations.
import all TauCeti.Algebra.Homology.DG.Twisted.Complex
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Data.Fintype.Order

/-!
# The index filtration of a twisted complex

The index filtration `F_p` consists of functions supported on generators of index at most `p`.
For a finite generator set it is bounded below, exhaustive, and increasing. One-sidedness of the
cocycle ensures that the twisted differential preserves it: the coefficient differential keeps
the generator index, and every twisting term strictly lowers it.

Intersecting `F_p` with the total grading gives an actual cochain complex, with inclusion maps
between its stages. The quotient `F_p / F_{p-1}` is identified with the copies of the coefficient
module indexed by generators of index exactly `p`. Under this identification its induced
differential acts coordinatewise by the coefficient differential. These are the filtered-complex
and associated-graded inputs to the spectral sequence of a twisted complex; no spectral sequence
pages are constructed here.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 3.38.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti

universe uR uA uM uP

section IndexFiltration

variable {R : Type uR} {M : Type uM} {P : Type uP}
  [Semiring R] [AddCommMonoid M] [Module R M] (ind : P → ℤ)

/-- The stage of the index filtration supported on generators of index at most `p`. -/
def twistedIndexFiltration (p : ℤ) : Submodule R (P → M) :=
  Submodule.pi {x | p < ind x} fun _ ↦ ⊥

@[simp]
theorem mem_twistedIndexFiltration_iff {p : ℤ} {f : P → M} :
    f ∈ twistedIndexFiltration (R := R) ind p ↔ ∀ x, p < ind x → f x = 0 := by
  simp [twistedIndexFiltration, Submodule.mem_pi]

/-- The index filtration is increasing. -/
theorem twistedIndexFiltration_mono : Monotone (twistedIndexFiltration (R := R) (M := M) ind) :=
  fun _ _ hp _ hf ↦ (mem_twistedIndexFiltration_iff (R := R) ind).mpr fun x hx ↦
    (mem_twistedIndexFiltration_iff (R := R) ind).mp hf x (lt_of_le_of_lt hp hx)

/-- Above every generator index the filtration stage is all of `P → M`. -/
theorem twistedIndexFiltration_eq_top {p : ℤ} (hp : ∀ x, ind x ≤ p) :
    twistedIndexFiltration (R := R) (M := M) ind p = ⊤ := by
  ext f
  simp only [mem_twistedIndexFiltration_iff, Submodule.mem_top, iff_true]
  exact fun x hx ↦ False.elim (not_lt_of_ge (hp x) hx)

/-- Below every generator index the filtration vanishes. -/
theorem twistedIndexFiltration_eq_bot {p : ℤ} (hp : ∀ x, p < ind x) :
    twistedIndexFiltration (R := R) (M := M) ind p = ⊥ := by
  ext f
  simp only [mem_twistedIndexFiltration_iff, Submodule.mem_bot]
  exact ⟨fun hf ↦ funext fun x ↦ hf x (hp x), fun hf ↦ by simp [hf]⟩

section FiniteIndexFiltration

variable [Finite P]

/-- A finite index filtration is bounded, including when there are no generators. -/
theorem twistedIndexFiltration_bounded :
    ∃ a b : ℤ, twistedIndexFiltration (R := R) (M := M) ind a = ⊥ ∧
      twistedIndexFiltration (R := R) (M := M) ind b = ⊤ := by
  obtain ⟨a, ha⟩ := Finite.exists_ge ind
  obtain ⟨b, hb⟩ := Finite.exists_le ind
  exact ⟨a - 1, b, twistedIndexFiltration_eq_bot ind
    (fun x ↦ lt_of_lt_of_le (by omega) (ha x)), twistedIndexFiltration_eq_top ind hb⟩

/-- Every element lies in some stage of a finite index filtration. -/
theorem iSup_twistedIndexFiltration_eq_top :
    (⨆ p, twistedIndexFiltration (R := R) (M := M) ind p) = ⊤ := by
  obtain ⟨_, b, _, hb⟩ := twistedIndexFiltration_bounded (R := R) (M := M) ind
  exact top_unique (hb ▸ le_iSup (twistedIndexFiltration (R := R) (M := M) ind) b)

end FiniteIndexFiltration

section IndexGrading

variable {R : Type uR} {M : Type uM} {P : Type uP}
  [Semiring R] [AddCommMonoid M] [Module R M]
  {ℳ : ℤ → Submodule R M} {ind : P → ℤ}

/-- The degree-`n` part of `F_p`, in the total grading of the twisted complex. -/
def twistedIndexGrading (ℳ : ℤ → Submodule R M) (ind : P → ℤ) (p n : ℤ) :
    Submodule R (P → M) :=
  twistedIndexFiltration ind p ⊓ twistedTotalGrading ℳ ind n

@[simp]
theorem mem_twistedIndexGrading_iff {p n : ℤ} {f : P → M} :
    f ∈ twistedIndexGrading ℳ ind p n ↔
      (∀ x, p < ind x → f x = 0) ∧ ∀ x, f x ∈ ℳ (n + ind x) := by
  simp [twistedIndexGrading]

/-- The index filtration on each total degree is increasing. -/
theorem twistedIndexGrading_mono {p q n : ℤ} (hpq : p ≤ q) :
    twistedIndexGrading ℳ ind p n ≤ twistedIndexGrading ℳ ind q n :=
  inf_le_inf_right _ (twistedIndexFiltration_mono ind hpq)

/-- A homogeneous filtration stage is contained in the corresponding total-degree piece. -/
theorem twistedIndexGrading_le_twistedTotalGrading (p n : ℤ) :
    twistedIndexGrading ℳ ind p n ≤ twistedTotalGrading ℳ ind n :=
  inf_le_right

end IndexGrading

end IndexFiltration

section Differential

variable {R : Type uR} {A : Type uA} {M : Type uM} {P : Type uP}
  [CommRing R] [Semiring A] [AddCommMonoid M] [Module R M]
  [Module Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M] [Fintype P]
  {ind : P → ℤ} {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  (m : P → P → A) (hm : ∀ x y, ind x ≤ ind y → m x y = 0)

include hm

omit [SMulCommClass R Aᵐᵒᵖ M] in
/-- Every twisting contribution from `F_p` vanishes at a generator of index at least `p`. -/
theorem twistingSum_eq_zero_of_mem_twistedIndexFiltration {p : ℤ} {f : P → M}
    (hf : f ∈ twistedIndexFiltration (R := R) (M := M) ind p)
    {y : P} (hy : p ≤ ind y) :
    (∑ x, op (m x y) • (InternalGrading.ofDecomposition ℳ).koszulTwist 1 (f x)) = 0 := by
  rw [mem_twistedIndexFiltration_iff] at hf
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : p < ind x
  · simp [hf x hx]
  · rw [hm x y (by omega)]
    simp

variable (dM : M →ₗ[R] M)

/-- One-sidedness makes the twisted differential preserve every index-filtration stage. -/
theorem twistedDifferential_mem_twistedIndexFiltration {p : ℤ} {f : P → M}
    (hf : f ∈ twistedIndexFiltration (R := R) (M := M) ind p) :
    twistedDifferential m ℳ dM f ∈ twistedIndexFiltration (R := R) (M := M) ind p := by
  rw [mem_twistedIndexFiltration_iff]
  intro y hy
  rw [twistedDifferential_apply,
    twistingSum_eq_zero_of_mem_twistedIndexFiltration m hm hf hy.le,
    (mem_twistedIndexFiltration_iff (R := R) ind).mp hf y hy, map_zero, zero_add]

/-- At index `p`, the differential of an element of `F_p` is its coefficient differential.
Every twisting contribution has strictly smaller generator index. -/
theorem twistedDifferential_apply_of_mem_twistedIndexFiltration
    {p : ℤ} {f : P → M} (hf : f ∈ twistedIndexFiltration (R := R) (M := M) ind p)
    {y : P} (hy : ind y = p) : twistedDifferential m ℳ dM f y = dM (f y) := by
  rw [twistedDifferential_apply,
    twistingSum_eq_zero_of_mem_twistedIndexFiltration m hm hf hy.ge, add_zero]

/-- Restriction to generators of index `p` intertwines the differential on `F_p` with the
coefficient differential, which is the twisted differential of the zero cocycle. -/
theorem twistedDifferential_funLeft_val {p : ℤ} {f : P → M}
    (hf : ∀ x, p < ind x → f x = 0) :
    twistedDifferential (0 : {x // ind x = p} → {x // ind x = p} → A) ℳ dM
        (LinearMap.funLeft R M Subtype.val f) =
      LinearMap.funLeft R M Subtype.val (twistedDifferential m ℳ dM f) := by
  funext y
  rw [LinearMap.funLeft_apply, twistedDifferential_apply_of_mem_twistedIndexFiltration m hm dM
    ((mem_twistedIndexFiltration_iff ind).mpr hf) y.2]
  simp

end Differential

section AssociatedGraded

variable {R : Type uR} {M : Type uM} {P : Type uP}
  [Ring R] [AddCommGroup M] [Module R M] (ind : P → ℤ) (p : ℤ)

/-- The preceding filtration stage as a submodule of `F_p`. -/
def twistedIndexLower :
    Submodule R (twistedIndexFiltration (R := R) (M := M) ind p) :=
  (twistedIndexFiltration (R := R) (M := M) ind (p - 1)).comap
    (twistedIndexFiltration (R := R) (M := M) ind p).subtype

@[simp]
theorem mem_twistedIndexLower_iff
    {f : twistedIndexFiltration (R := R) (M := M) ind p} :
    f ∈ twistedIndexLower (R := R) (M := M) ind p ↔ ∀ x, p - 1 < ind x → f.val x = 0 := by
  simp [twistedIndexLower]

/-- Projection from `F_p` to the generators of index exactly `p`. -/
def twistedIndexProjection :
    twistedIndexFiltration (R := R) (M := M) ind p →ₗ[R] ({x : P // ind x = p} → M) :=
  (LinearMap.funLeft R M Subtype.val).comp (twistedIndexFiltration (R := R) (M := M) ind p).subtype

@[simp]
theorem twistedIndexProjection_apply
    (f : twistedIndexFiltration (R := R) (M := M) ind p) (x : {x : P // ind x = p}) :
    twistedIndexProjection (R := R) (M := M) ind p f x = f.val x.val :=
  (rfl)

/-- The kernel of projection to index `p` is exactly `F_{p-1}` inside `F_p`. -/
theorem ker_twistedIndexProjection :
    LinearMap.ker (twistedIndexProjection (R := R) (M := M) ind p) =
      twistedIndexLower (R := R) (M := M) ind p := by
  ext f
  rw [LinearMap.mem_ker, mem_twistedIndexLower_iff]
  constructor
  · intro hf x hx
    by_cases hxp : ind x = p
    · exact congrFun hf ⟨x, hxp⟩
    · exact (mem_twistedIndexFiltration_iff (R := R) ind).mp f.property x (by omega)
  · intro hf
    funext x
    exact hf x.val (by have := x.property; omega)

/-- Every family on the generators of index `p` is the projection of an element of `F_p`. -/
theorem twistedIndexProjection_surjective :
    Function.Surjective (twistedIndexProjection (R := R) (M := M) ind p) := by
  classical
  intro f
  refine ⟨⟨fun x ↦ if hx : ind x = p then f ⟨x, hx⟩ else 0, ?_⟩, ?_⟩
  · rw [mem_twistedIndexFiltration_iff]
    intro x hx
    simp only [dite_eq_right (ne_of_gt hx)]
  · funext x
    simp [x.property]

/-- The associated graded module `F_p / F_{p-1}` is the family of coefficient modules on
exactly the generators of index `p`. -/
noncomputable def twistedIndexGradedEquiv :
    (twistedIndexFiltration (R := R) (M := M) ind p ⧸
      twistedIndexLower (R := R) (M := M) ind p) ≃ₗ[R]
      ({x : P // ind x = p} → M) :=
  (Submodule.quotEquivOfEq _ _ (ker_twistedIndexProjection (R := R) (M := M) ind p).symm).trans
    ((twistedIndexProjection (R := R) (M := M) ind p).quotKerEquivOfSurjective
      (twistedIndexProjection_surjective (R := R) (M := M) ind p))

@[simp]
theorem twistedIndexGradedEquiv_mk
    (f : twistedIndexFiltration (R := R) (M := M) ind p) (x : {x : P // ind x = p}) :
    twistedIndexGradedEquiv (R := R) (M := M) ind p (Submodule.Quotient.mk f) x =
      f.val x.val := by
  simp [twistedIndexGradedEquiv]

end AssociatedGraded

section FilteredDifferential

variable {R : Type uR} {A : Type uA} {M : Type uM} {P : Type uP}
  [CommRing R] [Semiring A] [AddCommMonoid M] [Module R M]
  [Module Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M] [Fintype P]
  {ind : P → ℤ}
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  (m : P → P → A) (hm : ∀ x y, ind x ≤ ind y → m x y = 0)
  (dM : M →ₗ[R] M) (p : ℤ)

/-- The restriction of the twisted differential to `F_p`. -/
noncomputable def twistedIndexDifferential :
    twistedIndexFiltration (R := R) (M := M) ind p →ₗ[R]
      twistedIndexFiltration (R := R) (M := M) ind p :=
  (twistedDifferential m ℳ dM).restrict fun _ hf ↦
    twistedDifferential_mem_twistedIndexFiltration m hm dM hf

@[simp]
theorem twistedIndexDifferential_apply
    (f : twistedIndexFiltration (R := R) (M := M) ind p) :
    (twistedIndexDifferential (ℳ := ℳ) m hm dM p f : P → M) = twistedDifferential m ℳ dM f :=
  (rfl)

end FilteredDifferential

section AssociatedGradedDifferential

variable {R : Type uR} {A : Type uA} {M : Type uM} {P : Type uP}
  [CommRing R] [Semiring A] [AddCommGroup M] [Module R M]
  [Module Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M] [Fintype P]
  {ind : P → ℤ}
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  (m : P → P → A) (hm : ∀ x y, ind x ≤ ind y → m x y = 0)
  (dM : M →ₗ[R] M) (p : ℤ)

/-- The differential induced on `F_p / F_{p-1}` by the twisted differential. -/
noncomputable def twistedIndexGradedDifferential :
    (twistedIndexFiltration (R := R) (M := M) ind p ⧸
      twistedIndexLower (R := R) (M := M) ind p) →ₗ[R]
      (twistedIndexFiltration (R := R) (M := M) ind p ⧸
      twistedIndexLower (R := R) (M := M) ind p) :=
  (twistedIndexLower (R := R) (M := M) ind p).mapQ (twistedIndexLower (R := R) (M := M) ind p)
    (twistedIndexDifferential (ℳ := ℳ) m hm dM p) fun f hf ↦ by
      rw [Submodule.mem_comap, mem_twistedIndexLower_iff]
      rw [mem_twistedIndexLower_iff] at hf
      exact (mem_twistedIndexFiltration_iff (R := R) ind).mp
        (twistedDifferential_mem_twistedIndexFiltration m hm dM
          ((mem_twistedIndexFiltration_iff (R := R) ind).mpr hf))

/-- The quotient differential sends the class of `f` to the class of its twisted differential. -/
@[simp]
theorem twistedIndexGradedDifferential_mk
    (f : twistedIndexFiltration (R := R) (M := M) ind p) :
    twistedIndexGradedDifferential (ℳ := ℳ) m hm dM p (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (twistedIndexDifferential (ℳ := ℳ) m hm dM p f) := by
  rw [twistedIndexGradedDifferential, Submodule.mapQ_apply]

/-- Under the associated graded equivalence, the induced differential is the coefficient
differential on each generator of index exactly `p`. -/
@[simp]
theorem twistedIndexGradedEquiv_d
    (f : twistedIndexFiltration (R := R) (M := M) ind p ⧸
      twistedIndexLower (R := R) (M := M) ind p)
    (x : {x : P // ind x = p}) :
    twistedIndexGradedEquiv (R := R) (M := M) ind p
      (twistedIndexGradedDifferential (ℳ := ℳ) m hm dM p f) x =
      dM (twistedIndexGradedEquiv (R := R) (M := M) ind p f x) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    rw [twistedIndexGradedDifferential_mk, twistedIndexGradedEquiv_mk,
      twistedIndexGradedEquiv_mk]
    exact twistedDifferential_apply_of_mem_twistedIndexFiltration m hm dM f.property x.property

/-- The induced associated graded differential squares to zero whenever the coefficient
differential does. -/
theorem twistedIndexGradedDifferential_sq_zero
    (hdM : ∀ x, dM (dM x) = 0)
    (f : twistedIndexFiltration (R := R) (M := M) ind p ⧸
      twistedIndexLower (R := R) (M := M) ind p) :
    twistedIndexGradedDifferential (ℳ := ℳ) m hm dM p
      (twistedIndexGradedDifferential (ℳ := ℳ) m hm dM p f) = 0 := by
  apply (twistedIndexGradedEquiv (R := R) (M := M) ind p).injective
  funext x
  rw [twistedIndexGradedEquiv_d, twistedIndexGradedEquiv_d, hdM]
  simp

end AssociatedGradedDifferential

section FilteredComplex

variable {R : Type uR} {A : Type uA} {M : Type uM} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M] [Fintype P]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}
  {h : IsDGAlgebra 𝒜 d} {ind : P → ℤ}
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  (m : TwistingCocycle 𝒜 d P ind) {dM : M →ₗ[R] M} (hM : IsDGRightModule h ℳ dM)

omit [IsScalarTower R Aᵐᵒᵖ M] in
/-- The twisted differential carries the degree-`n` part of `F_p` into degree `n+1` in `F_p`. -/
theorem TwistingCocycle.twistedDifferential_mem_twistedIndexGrading
    (hdM : LinearMap.IsHomogeneous dM ℳ ℳ 1) {p n : ℤ} {f : P → M}
    (hf : f ∈ twistedIndexGrading ℳ ind p n) :
    twistedDifferential m.m ℳ dM f ∈ twistedIndexGrading ℳ ind p (n + 1) :=
  ⟨twistedDifferential_mem_twistedIndexFiltration m.m m.one_sided dM hf.1,
    m.twistedDifferential_mem_twistedTotalGrading dM hdM hf.2⟩

/-- The `p`th stage of the index filtration as a cochain complex of modules. -/
noncomputable def TwistingCocycle.twistedIndexCochainComplex (p : ℤ) :
    CochainComplex (ModuleCat.{max uP uM} R) ℤ :=
  gradedCochainComplex (twistedIndexGrading ℳ ind p) (twistedDifferential m.m ℳ dM)
    (LinearMap.isHomogeneous_def.mpr fun _ _ hf ↦
      m.twistedDifferential_mem_twistedIndexGrading hM.isHomogeneous hf)
    fun _ f ↦ m.twistedDifferential_sq_zero dM hM f

/-- The degree terms of the filtered complex are the intersections of filtration and grading. -/
@[simp]
theorem TwistingCocycle.twistedIndexCochainComplex_X (p n : ℤ) :
    (m.twistedIndexCochainComplex hM p).X n = ModuleCat.of R (twistedIndexGrading ℳ ind p n) := by
  rw [TwistingCocycle.twistedIndexCochainComplex]
  exact gradedCochainComplex_X n

/-- Identify a term of the filtered complex with the intersection of index and total degree. -/
noncomputable def TwistingCocycle.twistedIndexCochainComplexXEquiv (p n : ℤ) :
    (m.twistedIndexCochainComplex hM p).X n ≃ₗ[R] twistedIndexGrading ℳ ind p n :=
  gradedCochainComplexXEquiv n

/-- The filtered cochain differential acts by the ambient twisted differential. -/
theorem TwistingCocycle.twistedIndexCochainComplexXEquiv_d (p n : ℤ)
    (f : (m.twistedIndexCochainComplex hM p).X n) :
    (m.twistedIndexCochainComplexXEquiv hM p (n + 1)
      (((m.twistedIndexCochainComplex hM p).d n (n + 1)).hom f) : P → M) =
      twistedDifferential m.m ℳ dM (m.twistedIndexCochainComplexXEquiv hM p n f) := by
  unfold TwistingCocycle.twistedIndexCochainComplexXEquiv
  exact gradedCochainComplexXEquiv_d n f

/-- The canonical cochain inclusion of a filtration stage into a later stage. -/
noncomputable def TwistingCocycle.twistedIndexCochainComplexMap {p q : ℤ} (hpq : p ≤ q) :
    m.twistedIndexCochainComplex hM p ⟶ m.twistedIndexCochainComplex hM q :=
  gradedCochainComplexInclusion (fun _ ↦ twistedIndexGrading_mono hpq)

/-- The transition map is inclusion on the underlying homogeneous functions. -/
@[simp]
theorem TwistingCocycle.twistedIndexCochainComplexMap_apply {p q : ℤ} (hpq : p ≤ q)
    (n : ℤ) (f : (m.twistedIndexCochainComplex hM p).X n) :
    (m.twistedIndexCochainComplexXEquiv hM q n
      (((m.twistedIndexCochainComplexMap hM hpq).f n).hom f) : P → M) =
      m.twistedIndexCochainComplexXEquiv hM p n f := by
  exact gradedCochainComplexInclusion_apply (fun _ ↦ twistedIndexGrading_mono hpq) n f

/-- The inclusion `F_p ⟶ F_q` is injective in each degree. -/
theorem TwistingCocycle.injective_twistedIndexCochainComplexMap_f {p q : ℤ} (hpq : p ≤ q) (n : ℤ) :
    Function.Injective ((m.twistedIndexCochainComplexMap hM hpq).f n) := by
  intro x y hxy
  apply (m.twistedIndexCochainComplexXEquiv hM p n).injective
  apply Subtype.ext
  have he := congrArg (fun z ↦ (m.twistedIndexCochainComplexXEquiv hM q n z : P → M)) hxy
  simpa only [m.twistedIndexCochainComplexMap_apply] using he

/-- The canonical inclusion of an index-filtration stage into the twisted complex. -/
noncomputable def TwistingCocycle.twistedIndexCochainComplexι (p : ℤ) :
    m.twistedIndexCochainComplex hM p ⟶ m.twistedCochainComplex dM hM :=
  gradedCochainComplexInclusion (twistedIndexGrading_le_twistedTotalGrading p)

/-- The stage inclusion preserves the underlying homogeneous function. -/
@[simp]
theorem TwistingCocycle.twistedIndexCochainComplexι_apply (p n : ℤ)
    (f : (m.twistedIndexCochainComplex hM p).X n) :
    (twistedCochainComplexXEquiv m.mem_graded m.twisting hM n
      (((m.twistedIndexCochainComplexι hM p).f n).hom f) : P → M) =
      m.twistedIndexCochainComplexXEquiv hM p n f := by
  exact gradedCochainComplexInclusion_apply (twistedIndexGrading_le_twistedTotalGrading p) n f

/-- Each filtration stage embeds as a subcomplex of the twisted complex. -/
instance TwistingCocycle.mono_twistedIndexCochainComplexι (p : ℤ) :
    Mono (m.twistedIndexCochainComplexι hM p) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  rw [ModuleCat.mono_iff_injective]
  intro f g hfg
  apply (m.twistedIndexCochainComplexXEquiv hM p n).injective
  apply Subtype.ext
  have h := congrArg (fun t ↦
    (twistedCochainComplexXEquiv m.mem_graded m.twisting hM n t : P → M)) hfg
  simpa only [m.twistedIndexCochainComplexι_apply] using h

/-- Transition maps commute with the inclusions into the twisted complex. -/
@[reassoc (attr := simp)]
theorem TwistingCocycle.twistedIndexCochainComplexMap_ι {p q : ℤ} (hpq : p ≤ q) :
    m.twistedIndexCochainComplexMap hM hpq ≫ m.twistedIndexCochainComplexι hM q =
      m.twistedIndexCochainComplexι hM p := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply (twistedCochainComplexXEquiv m.mem_graded m.twisting hM n).injective
  apply Subtype.ext
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    m.twistedIndexCochainComplexι_apply, m.twistedIndexCochainComplexMap_apply]

/-- The transition map from a filtration stage to itself is the identity. -/
@[simp]
theorem TwistingCocycle.twistedIndexCochainComplexMap_id (p : ℤ) :
    m.twistedIndexCochainComplexMap hM (p := p) le_rfl =
      𝟙 (m.twistedIndexCochainComplex hM p) := by
  apply (cancel_mono (m.twistedIndexCochainComplexι hM p)).mp
  simp only [m.twistedIndexCochainComplexMap_ι, Category.id_comp]

/-- The transition maps of the index filtration compose. -/
@[reassoc (attr := simp)]
theorem TwistingCocycle.twistedIndexCochainComplexMap_comp {p q r : ℤ}
    (hpq : p ≤ q) (hqr : q ≤ r) :
    m.twistedIndexCochainComplexMap hM hpq ≫ m.twistedIndexCochainComplexMap hM hqr =
      m.twistedIndexCochainComplexMap hM (hpq.trans hqr) := by
  apply (cancel_mono (m.twistedIndexCochainComplexι hM r)).mp
  simp only [Category.assoc, m.twistedIndexCochainComplexMap_ι]

/-- The index filtration as actual subobjects of the twisted cochain complex. -/
noncomputable def TwistingCocycle.twistedIndexSubobject (p : ℤ) :
    Subobject (m.twistedCochainComplex dM hM) :=
  Subobject.mk (m.twistedIndexCochainComplexι hM p)

/-- The filtration subobject is represented by the canonical stage inclusion. -/
@[simp]
theorem TwistingCocycle.twistedIndexSubobject_eq_mk (p : ℤ) :
    m.twistedIndexSubobject hM p = Subobject.mk (m.twistedIndexCochainComplexι hM p) := by
  rfl

/-- The subobjects of the twisted complex form an increasing filtration. -/
theorem TwistingCocycle.twistedIndexSubobject_mono :
    Monotone (m.twistedIndexSubobject hM) := fun _ _ hpq ↦
  Subobject.mk_le_mk_of_comm (m.twistedIndexCochainComplexMap hM hpq)
    (m.twistedIndexCochainComplexMap_ι hM hpq)

/-- Above all generator indices the subobject filtration is the whole twisted complex. -/
theorem TwistingCocycle.twistedIndexSubobject_eq_top {p : ℤ} (hp : ∀ x, ind x ≤ p) :
    m.twistedIndexSubobject hM p = ⊤ := by
  have hs : ∀ n, Function.Surjective ((m.twistedIndexCochainComplexι hM p).f n) := by
    intro n f
    let g := twistedCochainComplexXEquiv m.mem_graded m.twisting hM n f
    have hg : (g : P → M) ∈ twistedIndexGrading ℳ ind p n := by
      refine ⟨?_, g.property⟩
      exact twistedIndexFiltration_eq_top (R := R) (M := M) ind hp ▸ Submodule.mem_top
    refine ⟨(m.twistedIndexCochainComplexXEquiv hM p n).symm ⟨g, hg⟩, ?_⟩
    apply (twistedCochainComplexXEquiv m.mem_graded m.twisting hM n).injective
    apply Subtype.ext
    rw [m.twistedIndexCochainComplexι_apply]
    simp only [LinearEquiv.apply_symm_apply]
    rfl
  let : ∀ n, IsIso ((m.twistedIndexCochainComplexι hM p).f n) := fun n ↦
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨(ModuleCat.mono_iff_injective _).mp inferInstance, hs n⟩
  have := HomologicalComplex.Hom.isIso_of_components (m.twistedIndexCochainComplexι hM p)
  exact Subobject.mk_eq_top_of_isIso _

/-- Below all generator indices the subobject filtration vanishes. -/
theorem TwistingCocycle.twistedIndexSubobject_eq_bot {p : ℤ} (hp : ∀ x, p < ind x) :
    m.twistedIndexSubobject hM p = ⊥ := by
  apply Subobject.mk_eq_bot_iff_zero.mpr
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply (twistedCochainComplexXEquiv m.mem_graded m.twisting hM n).injective
  apply Subtype.ext
  simp only [HomologicalComplex.zero_f, ModuleCat.hom_zero, LinearMap.zero_apply, map_zero,
    Submodule.coe_zero, m.twistedIndexCochainComplexι_apply]
  funext x
  exact (mem_twistedIndexFiltration_iff (R := R) ind).mp
    (m.twistedIndexCochainComplexXEquiv hM p n f).property.1 x (hp x)

/-- The actual subcomplex filtration is bounded below and exhaustive for finite generators. -/
theorem TwistingCocycle.twistedIndexSubobject_bounded :
    ∃ a b : ℤ, m.twistedIndexSubobject hM a = ⊥ ∧ m.twistedIndexSubobject hM b = ⊤ := by
  obtain ⟨a, ha⟩ := Finite.exists_ge ind
  obtain ⟨b, hb⟩ := Finite.exists_le ind
  exact ⟨a - 1, b, m.twistedIndexSubobject_eq_bot hM
    (fun x ↦ lt_of_lt_of_le (by omega) (ha x)), m.twistedIndexSubobject_eq_top hM hb⟩

end FilteredComplex

end TauCeti

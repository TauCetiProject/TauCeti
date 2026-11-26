/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.ActionSequence
public import TauCeti.Algebra.Homology.DG.Twisted.Equivalence
public import TauCeti.Algebra.Homology.HomologicalComplex.HomologyFunctorOfHomotopy
public import TauCeti.Algebra.Homology.ShortComplex.FunctorCategory
public import Mathlib.CategoryTheory.Limits.HasExactLimitsOfShape

/-!
# Direct limits of twisted complexes along continuation maps

Symplectic homology is the direct limit, over the slopes of the Hamiltonians, of Floer homology
groups connected by continuation maps. The continuation maps compose only up to homotopy, so the
direct limit is taken of homology groups. This file sets up that limit for the twisted complexes
of a differential graded algebra `(𝒜, d)` with coefficients in a differential graded right module
`(ℳ, dM)`, and shows that the long exact sequence of a subcomplex, such as the part of action
below a level, survives in the limit.

A **continuation system** over a preorder `ι` (`TauCeti.ContinuationSystem`) is a twisting
cocycle `m i` on a finite set `P i` of generators for each `i : ι`, with a continuation cocycle
`ν hij : m i → m j` for each `i ≤ j`, such that `ν (le_refl i)` is joined to the Kronecker cocycle
by a parametrized cocycle, and `ν (hij.trans hjk)` to the composite of `ν hij` and `ν hjk`. On
cohomology the continuation maps therefore form a functor `ι ⥤ ModuleCat R` in each degree
(`TauCeti.ContinuationSystem.homologyFunctor`), whose colimit is the direct limit.

A **subsystem** (`TauCeti.ContinuationSystem.Subsystem`) is a choice of sets `S i ⊆ P i` of
generators which the twisted differentials, the continuation cocycles and some choice of the
parametrized cocycles never leave. The subcomplexes of the `S i` and the quotient complexes of
their complements then also form continuation systems
(`TauCeti.ContinuationSystem.Subsystem.toSub`, `TauCeti.ContinuationSystem.Subsystem.toQuotient`),
so their cohomology groups form functors on `ι` too, and the maps of the long exact
sequences of the short exact sequences `0 → S i → P i → P i ∖ S i → 0` are natural transformations
between them, the connecting morphism included (`TauCeti.ContinuationSystem.Subsystem.homologyδ`).
When colimits of shape `ι` are exact, as filtered colimits of modules are, the colimit of these
long exact sequences is exact at each of its three kinds of terms
(`TauCeti.ContinuationSystem.Subsystem.exact_map_colim_homologyι_homologyπ`,
`TauCeti.ContinuationSystem.Subsystem.exact_map_colim_homologyπ_homologyδ`,
`TauCeti.ContinuationSystem.Subsystem.exact_map_colim_homologyδ_homologyι`).

In Floer theory the generators carry actions, the differentials and the continuation cocycles of
monotone homotopies do not raise them, and the generators of action below a level `a` form a
subsystem (`TauCeti.ContinuationSystem.IsActionNonincreasing.sublevel`). The colimit of the long
exact sequences is then the long exact sequence relating the direct limit of the parts of action
below `a`, the direct limit of the whole complexes and the direct limit of the parts of action at
least `a`, the algebraic content of the tautological long exact sequence of symplectic homology.

## Main definitions

* `TauCeti.ContinuationSystem`: twisting cocycles indexed by a preorder, with continuation
  cocycles which are functorial up to parametrized cocycles.
* `TauCeti.ContinuationSystem.homologyFunctor`: their cohomology in degree `n`, a functor on `ι`.
* `TauCeti.ContinuationSystem.const`: the constant system of a single twisting cocycle.
* `TauCeti.ContinuationSystem.Subsystem`: sets of generators spanning subcomplexes throughout.
* `TauCeti.ContinuationSystem.Subsystem.toSub`, `TauCeti.ContinuationSystem.Subsystem.toQuotient`:
  the continuation systems of their subcomplexes and of the quotient complexes.
* `TauCeti.ContinuationSystem.IsActionNonincreasing`: actions which the differentials,
  continuation cocycles and some parametrized cocycles do not raise, and their sublevel
  subsystems.

## Main results

* `TauCeti.ContinuationSystem.Subsystem.exact_homologyι_homologyπ`,
  `TauCeti.ContinuationSystem.Subsystem.exact_homologyπ_homologyδ`,
  `TauCeti.ContinuationSystem.Subsystem.exact_homologyδ_homologyι`: the long exact sequence of a
  subsystem, as sequences of functors on `ι`.
* `TauCeti.ContinuationSystem.Subsystem.exact_map_colim_homologyι_homologyπ`,
  `TauCeti.ContinuationSystem.Subsystem.exact_map_colim_homologyπ_homologyδ`,
  `TauCeti.ContinuationSystem.Subsystem.exact_map_colim_homologyδ_homologyι`: its colimit is exact
  when colimits of shape `ι` are.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3, symplectic homology with DG
  coefficients as a direct limit over slopes, and Proposition 3.45.
* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  §3, the direct limit over slopes.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

universe w uR uA uM uP

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ] {dM : M →ₗ[R] M}

variable (𝒜 d) in
/-- A **continuation system** over a preorder `ι`: a twisting cocycle `m i` on a finite set `P i`
of generators for each `i : ι`, and a continuation cocycle `ν hij : m i → m j` for each `i ≤ j`,
such that `ν (le_refl i)` is joined to the Kronecker cocycle, and `ν (hij.trans hjk)` to the
composite of `ν hij` and `ν hjk`, by parametrized cocycles. This is the algebraic shape of the
Floer complexes of Hamiltonians of increasing slopes and their continuation maps. -/
structure ContinuationSystem (h : IsDGAlgebra 𝒜 d) (ι : Type w) [Preorder ι] where
  /-- The generators at `i`. -/
  P : ι → Type uP
  [fintype : ∀ i, Fintype (P i)]
  [decidableEq : ∀ i, DecidableEq (P i)]
  /-- The index of the generators at `i`. -/
  ind : ∀ i, P i → ℤ
  /-- The twisting cocycle at `i`. -/
  m : ∀ i, TwistingCocycle 𝒜 d (P i) (ind i)
  /-- The continuation cocycle from `i` to `j ≥ i`. -/
  ν : ∀ ⦃i j : ι⦄, i ≤ j → ContinuationCocycle (m i) (m j)
  /-- The continuation cocycle from `i` to itself is homotopic to the Kronecker cocycle. -/
  nonempty_refl : ∀ i,
    Nonempty (ParametrizedCocycle (ContinuationCocycle.refl h.map_one_eq_zero (m i))
      (ν (le_refl i)))
  /-- The continuation cocycles compose up to homotopy. -/
  nonempty_comp : ∀ ⦃i j k : ι⦄ (hij : i ≤ j) (hjk : j ≤ k),
    Nonempty (ParametrizedCocycle ((ν hij).comp h (ν hjk)) (ν (hij.trans hjk)))

namespace ContinuationSystem

attribute [instance] fintype decidableEq

variable {h : IsDGAlgebra 𝒜 d} {ι : Type w} [Preorder ι]
  (S : ContinuationSystem.{w, uR, uA, uP} 𝒜 d h ι) (hM : IsDGRightModule h ℳ dM)

/-! ### The cohomology functor -/

/-- The **cohomology of a continuation system** in degree `n`: the functor on `ι` sending `i` to
the cohomology of the twisted complex of `m i`, and `i ≤ j` to the map induced by the
continuation cocycle `ν`. Its colimit is the direct limit of the system. -/
@[expose]
noncomputable def homologyFunctor (n : ℤ) : ι ⥤ ModuleCat.{max uP uM} R :=
  HomologicalComplex.homologyFunctorOfHomotopy (fun i ↦ (S.m i).twistedCochainComplex dM hM)
    (fun _ _ hij ↦ (S.ν hij).continuationHom hM)
    (fun i ↦ (S.nonempty_refl i).map fun η ↦
      (η.homotopy hM).trans (.ofEq (ContinuationCocycle.continuationHom_refl hM)))
    (fun _ _ _ hij hjk ↦ (S.nonempty_comp hij hjk).map fun η ↦
      (η.homotopy hM).trans (.ofEq (ContinuationCocycle.continuationHom_comp _ _ hM)))
    n

@[simp]
theorem homologyFunctor_obj (n : ℤ) (i : ι) :
    (S.homologyFunctor hM n).obj i = ((S.m i).twistedCochainComplex dM hM).homology n :=
  (rfl)

@[simp]
theorem homologyFunctor_map (n : ℤ) {i j : ι} (g : i ⟶ j) :
    (S.homologyFunctor hM n).map g =
      HomologicalComplex.homologyMap ((S.ν (leOfHom g)).continuationHom hM) n :=
  (rfl)

/-! ### Constant systems -/

variable (h ι) in
/-- The **constant continuation system** of a twisting cocycle `m`: `m` at every index, with the
Kronecker continuation cocycles. The body is exposed: its generators at each index are those
of `m`. -/
@[expose]
def const {P : Type uP} [Fintype P] [DecidableEq P] {ind : P → ℤ}
    (m : TwistingCocycle 𝒜 d P ind) : ContinuationSystem.{w, uR, uA, uP} 𝒜 d h ι where
  P _ := P
  ind _ := ind
  m _ := m
  ν _ _ _ := ContinuationCocycle.refl h.map_one_eq_zero m
  nonempty_refl _ := ⟨ParametrizedCocycle.ofEq rfl⟩
  nonempty_comp _ _ _ _ _ := ⟨ParametrizedCocycle.ofEq (ContinuationCocycle.refl_comp h _)⟩

section Const

variable {P : Type uP} [Fintype P] [DecidableEq P] {ind : P → ℤ} (m : TwistingCocycle 𝒜 d P ind)

@[simp]
theorem const_P (i : ι) : (const h ι m).P i = P :=
  (rfl)

@[simp]
theorem const_ind (i : ι) : (const h ι m).ind i = ind :=
  (rfl)

@[simp]
theorem const_m (i : ι) : (const h ι m).m i = m :=
  (rfl)

@[simp]
theorem const_ν {i j : ι} (hij : i ≤ j) :
    (const h ι m).ν hij = ContinuationCocycle.refl h.map_one_eq_zero m :=
  (rfl)

/-- The cohomology functor of a constant continuation system has identity maps. -/
theorem homologyFunctor_const_map (n : ℤ) {i j : ι} (g : i ⟶ j) :
    ((const h ι m).homologyFunctor hM n).map g = 𝟙 _ := by
  have hn := congrArg (HomologicalComplex.homologyMap · n)
    (ContinuationCocycle.continuationHom_refl (mP := m) hM)
  rw [HomologicalComplex.homologyMap_id] at hn
  rw [homologyFunctor_map, const_ν]
  exact hn

end Const

/-! ### Subsystems -/

/-- A **subsystem** of a continuation system: a set `carrier i` of generators at each `i` which
the twisted differential of `m i` never leaves, such that the continuation cocycles never leave
these sets, and some choice of the parametrized cocycles of the system never leaves them either.
The generators of action below a fixed level form a subsystem when the actions are not raised
(`TauCeti.ContinuationSystem.IsActionNonincreasing.sublevel`). -/
structure Subsystem where
  /-- The generators at `i` spanning the subcomplex. -/
  carrier : ∀ i, Set (S.P i)
  [decidableMem : ∀ i, DecidablePred (· ∈ carrier i)]
  /-- The twisted differential never leaves the subcomplex. -/
  m_eq_zero : ∀ i x y, x ∈ carrier i → y ∉ carrier i → (S.m i).m x y = 0
  /-- The continuation cocycles never leave the subcomplexes. -/
  ν_eq_zero : ∀ ⦃i j : ι⦄ (hij : i ≤ j) x y, x ∈ carrier i → y ∉ carrier j → (S.ν hij).ν x y = 0
  /-- Some parametrized cocycle joining the Kronecker cocycle to `ν (le_refl i)` never leaves the
  subcomplex. -/
  exists_refl : ∀ i, ∃ η : ParametrizedCocycle
      (ContinuationCocycle.refl h.map_one_eq_zero (S.m i)) (S.ν (le_refl i)),
    ∀ x y, x ∈ carrier i → y ∉ carrier i → η.h x y = 0
  /-- Some parametrized cocycle joining the composite of `ν hij` and `ν hjk` to
  `ν (hij.trans hjk)` never leaves the subcomplexes. -/
  exists_comp : ∀ ⦃i j k : ι⦄ (hij : i ≤ j) (hjk : j ≤ k),
    ∃ η : ParametrizedCocycle ((S.ν hij).comp h (S.ν hjk)) (S.ν (hij.trans hjk)),
      ∀ x y, x ∈ carrier i → y ∉ carrier k → η.h x y = 0

namespace Subsystem

attribute [instance] decidableMem

variable {S} (T : S.Subsystem)

/-- The Kronecker cocycle never leaves the subcomplex. -/
theorem refl_ν_eq_zero (i : ι) :
    ∀ x y, x ∈ T.carrier i → y ∉ T.carrier i →
      (ContinuationCocycle.refl h.map_one_eq_zero (S.m i)).ν x y = 0 := fun x y hx hy ↦ by
  rw [ContinuationCocycle.refl_ν, Matrix.one_apply_ne fun hxy : x = y ↦ hy (hxy ▸ hx)]

/-- The composite of two continuation cocycles of the system never leaves the subcomplexes. -/
theorem comp_ν_eq_zero {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) :
    ∀ x y, x ∈ T.carrier i → y ∉ T.carrier k → ((S.ν hij).comp h (S.ν hjk)).ν x y = 0 :=
  ContinuationCocycle.comp_ν_eq_zero_of_forall_eq_zero h _ _ (T.ν_eq_zero hij) (T.ν_eq_zero hjk)

/-- The twisted differential never enters the complement of the subcomplex from outside. -/
theorem compl_m_eq_zero (i : ι) :
    ∀ x y, x ∉ (T.carrier i)ᶜ → y ∈ (T.carrier i)ᶜ → (S.m i).m x y = 0 :=
  (S.m i).forall_eq_zero_of_compl (T.m_eq_zero i) fun _ ↦ Iff.rfl

/-- The continuation cocycles never enter the complements of the subcomplexes from outside. -/
theorem compl_ν_eq_zero {i j : ι} (hij : i ≤ j) :
    ∀ x y, x ∉ (T.carrier i)ᶜ → y ∈ (T.carrier j)ᶜ → (S.ν hij).ν x y = 0 :=
  (S.ν hij).forall_eq_zero_of_compl (T.ν_eq_zero hij) (fun _ ↦ Iff.rfl) fun _ ↦ Iff.rfl

/-- The Kronecker cocycle never enters the complement of the subcomplex from outside. -/
theorem compl_refl_ν_eq_zero (i : ι) :
    ∀ x y, x ∉ (T.carrier i)ᶜ → y ∈ (T.carrier i)ᶜ →
      (ContinuationCocycle.refl h.map_one_eq_zero (S.m i)).ν x y = 0 :=
  apply_eq_zero_of_compl (T.refl_ν_eq_zero i) (fun _ ↦ Iff.rfl) fun _ ↦ Iff.rfl

/-- The composite of two continuation cocycles of the system never enters the complements of the
subcomplexes from outside. -/
theorem compl_comp_ν_eq_zero {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) :
    ∀ x y, x ∉ (T.carrier i)ᶜ → y ∈ (T.carrier k)ᶜ → ((S.ν hij).comp h (S.ν hjk)).ν x y = 0 :=
  apply_eq_zero_of_compl (T.comp_ν_eq_zero hij hjk) (fun _ ↦ Iff.rfl) fun _ ↦ Iff.rfl

/-! ### The continuation systems of the subcomplexes and of the quotient complexes -/

/-- The **continuation system of the subcomplexes** of a subsystem: the restrictions of the
twisting cocycles and of the continuation cocycles to the generators of the subsystem. -/
@[expose]
def toSub : ContinuationSystem.{w, uR, uA, uP} 𝒜 d h ι where
  P i := T.carrier i
  ind i x := S.ind i x
  m i := (S.m i).restrict (T.carrier i) ((S.m i).mul_eq_zero_of_forall_eq_zero (T.m_eq_zero i))
  ν _ _ hij := (S.ν hij).restrictSubcomplex _ (T.m_eq_zero _) _ (T.m_eq_zero _) (T.ν_eq_zero hij)
  nonempty_refl i := by
    obtain ⟨η, hη⟩ := T.exists_refl i
    rw [← ContinuationCocycle.restrictSubcomplex_refl h.map_one_eq_zero _ (T.m_eq_zero i)
      (T.refl_ν_eq_zero i)]
    exact ⟨η.restrictSubcomplex _ _ _ _ _ _ hη⟩
  nonempty_comp _ _ _ hij hjk := by
    obtain ⟨η, hη⟩ := T.exists_comp hij hjk
    rw [← ContinuationCocycle.restrictSubcomplex_comp h _ _ _ _ _ (T.m_eq_zero _) _ _
      (T.ν_eq_zero hij) (T.ν_eq_zero hjk) (T.comp_ν_eq_zero hij hjk)]
    exact ⟨η.restrictSubcomplex _ _ _ _ _ _ hη⟩

/-- The **continuation system of the quotient complexes** of a subsystem: the restrictions of the
twisting cocycles and of the continuation cocycles to the generators outside the subsystem. -/
@[expose]
def toQuotient : ContinuationSystem.{w, uR, uA, uP} 𝒜 d h ι where
  P i := ↥(T.carrier i)ᶜ
  ind i x := S.ind i x
  m i := (S.m i).restrict (T.carrier i)ᶜ ((S.m i).mul_eq_zero_of_forall_eq_zero'
    (T.compl_m_eq_zero i))
  ν _ _ hij := (S.ν hij).restrictQuotient _ (T.compl_m_eq_zero _) _ (T.compl_m_eq_zero _)
    (T.compl_ν_eq_zero hij)
  nonempty_refl i := by
    obtain ⟨η, hη⟩ := T.exists_refl i
    rw [← ContinuationCocycle.restrictQuotient_refl h.map_one_eq_zero _ (T.compl_m_eq_zero i)
      (T.compl_refl_ν_eq_zero i)]
    exact ⟨η.restrictQuotient _ _ _ _ (T.compl_refl_ν_eq_zero i) _
      (apply_eq_zero_of_compl hη (fun _ ↦ Iff.rfl) fun _ ↦ Iff.rfl)⟩
  nonempty_comp _ _ _ hij hjk := by
    obtain ⟨η, hη⟩ := T.exists_comp hij hjk
    rw [← ContinuationCocycle.restrictQuotient_comp h _ _ _ _ _ (T.compl_m_eq_zero _) _ _
      (T.compl_ν_eq_zero hij) (T.compl_ν_eq_zero hjk) (T.compl_comp_ν_eq_zero hij hjk)]
    exact ⟨η.restrictQuotient _ _ _ _ (T.compl_comp_ν_eq_zero hij hjk) _
      (apply_eq_zero_of_compl hη (fun _ ↦ Iff.rfl) fun _ ↦ Iff.rfl)⟩

@[simp]
theorem toSub_P (i : ι) : T.toSub.P i = T.carrier i :=
  (rfl)

@[simp]
theorem toSub_ind (i : ι) (x : T.carrier i) : T.toSub.ind i x = S.ind i x :=
  (rfl)

@[simp]
theorem toSub_m (i : ι) :
    T.toSub.m i =
      (S.m i).restrict (T.carrier i) ((S.m i).mul_eq_zero_of_forall_eq_zero (T.m_eq_zero i)) :=
  (rfl)

@[simp]
theorem toSub_ν {i j : ι} (hij : i ≤ j) :
    T.toSub.ν hij = (S.ν hij).restrictSubcomplex (T.carrier i) (T.m_eq_zero i) (T.carrier j)
      (T.m_eq_zero j) (T.ν_eq_zero hij) :=
  (rfl)

@[simp]
theorem toQuotient_P (i : ι) : T.toQuotient.P i = ↥(T.carrier i)ᶜ :=
  (rfl)

@[simp]
theorem toQuotient_ind (i : ι) (x : ↥(T.carrier i)ᶜ) : T.toQuotient.ind i x = S.ind i x :=
  (rfl)

@[simp]
theorem toQuotient_m (i : ι) :
    T.toQuotient.m i = (S.m i).restrict (T.carrier i)ᶜ
      ((S.m i).mul_eq_zero_of_forall_eq_zero' (T.compl_m_eq_zero i)) :=
  (rfl)

@[simp]
theorem toQuotient_ν {i j : ι} (hij : i ≤ j) :
    T.toQuotient.ν hij = (S.ν hij).restrictQuotient (T.carrier i)ᶜ (T.compl_m_eq_zero i)
      (T.carrier j)ᶜ (T.compl_m_eq_zero j) (T.compl_ν_eq_zero hij) :=
  (rfl)

/-! ### The long exact sequence of a subsystem -/

/-- The short exact sequence `0 → S i → P i → P i ∖ S i → 0` of twisted complexes at `i`. -/
theorem shortExact (i : ι) :
    ((S.m i).restrictShortComplex hM (T.carrier i) (T.carrier i)ᶜ (T.m_eq_zero i)
      fun _ ↦ Iff.rfl).ShortExact :=
  (S.m i).restrictShortComplex_shortExact hM _ _ _ _

/-- The maps induced on cohomology by the inclusions of the subcomplexes, natural in `i`. -/
noncomputable def homologyι (n : ℤ) :
    T.toSub.homologyFunctor hM n ⟶ S.homologyFunctor hM n where
  app i := HomologicalComplex.homologyMap
    ((ContinuationCocycle.ofRestrict (S.m i) h.map_one_eq_zero (T.carrier i)
      (T.m_eq_zero i)).continuationHom hM) n
  naturality _ _ g := by
    have hn := congrArg (HomologicalComplex.homologyMap · n)
      (ContinuationCocycle.ofRestrict_continuationHom_comp h (S.ν (leOfHom g)) _ (T.m_eq_zero _) _
        (T.m_eq_zero _) (T.ν_eq_zero (leOfHom g)) hM)
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hn
    rw [homologyFunctor_map, homologyFunctor_map, toSub_ν]
    exact hn.symm

@[simp]
theorem homologyι_app (n : ℤ) (i : ι) :
    (T.homologyι hM n).app i = HomologicalComplex.homologyMap
      ((ContinuationCocycle.ofRestrict (S.m i) h.map_one_eq_zero (T.carrier i)
        (T.m_eq_zero i)).continuationHom hM) n :=
  (rfl)

/-- The maps induced on cohomology by the projections onto the quotient complexes, natural in
`i`. -/
noncomputable def homologyπ (n : ℤ) :
    S.homologyFunctor hM n ⟶ T.toQuotient.homologyFunctor hM n where
  app i := HomologicalComplex.homologyMap
    ((ContinuationCocycle.toRestrict (S.m i) h.map_one_eq_zero (T.carrier i)ᶜ
      (T.compl_m_eq_zero i)).continuationHom hM) n
  naturality _ _ g := by
    have hn := congrArg (HomologicalComplex.homologyMap · n)
      (ContinuationCocycle.toRestrict_continuationHom_comp h (S.ν (leOfHom g)) hM _
        (T.compl_m_eq_zero _) _ (T.compl_m_eq_zero _) (T.compl_ν_eq_zero (leOfHom g)))
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hn
    rw [homologyFunctor_map, homologyFunctor_map, toQuotient_ν]
    exact hn.symm

@[simp]
theorem homologyπ_app (n : ℤ) (i : ι) :
    (T.homologyπ hM n).app i = HomologicalComplex.homologyMap
      ((ContinuationCocycle.toRestrict (S.m i) h.map_one_eq_zero (T.carrier i)ᶜ
        (T.compl_m_eq_zero i)).continuationHom hM) n :=
  (rfl)

/-- The connecting morphisms `H^n(P i ∖ S i) ⟶ H^m(S i)`, for `n + 1 = m`, of the long exact
sequences of the subcomplexes, natural in `i`. -/
noncomputable def homologyδ (n m : ℤ) (hnm : n + 1 = m) :
    T.toQuotient.homologyFunctor hM n ⟶ T.toSub.homologyFunctor hM m where
  app i := (T.shortExact hM i).δ n m hnm
  naturality _ _ g := by
    rw [homologyFunctor_map, homologyFunctor_map, toQuotient_ν, toSub_ν]
    exact ((S.ν (leOfHom g)).restrictShortComplexMap_δ h hM _ _ _ _ _ _ _ _
      (T.ν_eq_zero (leOfHom g)) n m hnm).symm

@[simp]
theorem homologyδ_app (n m : ℤ) (hnm : n + 1 = m) (i : ι) :
    (T.homologyδ hM n m hnm).app i = (T.shortExact hM i).δ n m hnm :=
  (rfl)

@[reassoc (attr := simp)]
theorem homologyι_comp_homologyπ (n : ℤ) : T.homologyι hM n ≫ T.homologyπ hM n = 0 := by
  ext i : 2
  have hn := congrArg (HomologicalComplex.homologyMap · n)
    ((S.m i).ofRestrict_continuationHom_comp_toRestrict_continuationHom hM (T.carrier i)
      (T.carrier i)ᶜ (T.m_eq_zero i) fun _ ↦ Iff.rfl)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_zero] at hn
  rw [NatTrans.comp_app, homologyι_app, homologyπ_app, NatTrans.app_zero]
  exact hn

@[reassoc (attr := simp)]
theorem homologyπ_comp_homologyδ (n m : ℤ) (hnm : n + 1 = m) :
    T.homologyπ hM n ≫ T.homologyδ hM n m hnm = 0 := by
  ext i : 2
  exact (T.shortExact hM i).comp_δ n m hnm

@[reassoc (attr := simp)]
theorem homologyδ_comp_homologyι (n m : ℤ) (hnm : n + 1 = m) :
    T.homologyδ hM n m hnm ≫ T.homologyι hM m = 0 := by
  ext i : 2
  exact (T.shortExact hM i).δ_comp n m hnm

/-- **Exactness at the whole complexes**: `H^n(S) ⟶ H^n(P) ⟶ H^n(P ∖ S)` is exact, as a
sequence of functors on `ι`. -/
theorem exact_homologyι_homologyπ (n : ℤ) :
    (ShortComplex.mk _ _ (T.homologyι_comp_homologyπ hM n)).Exact :=
  (ShortComplex.exact_iff_evaluation _).2 fun i ↦ (T.shortExact hM i).homology_exact₂ n

/-- **Exactness at the quotient complexes**: `H^n(P) ⟶ H^n(P ∖ S) ⟶ H^m(S)`, for `n + 1 = m`, is
exact, as a sequence of functors on `ι`. -/
theorem exact_homologyπ_homologyδ (n m : ℤ) (hnm : n + 1 = m) :
    (ShortComplex.mk _ _ (T.homologyπ_comp_homologyδ hM n m hnm)).Exact :=
  (ShortComplex.exact_iff_evaluation _).2 fun i ↦ (T.shortExact hM i).homology_exact₃ n m hnm

/-- **Exactness at the subcomplexes**: `H^n(P ∖ S) ⟶ H^m(S) ⟶ H^m(P)`, for `n + 1 = m`, is exact,
as a sequence of functors on `ι`. -/
theorem exact_homologyδ_homologyι (n m : ℤ) (hnm : n + 1 = m) :
    (ShortComplex.mk _ _ (T.homologyδ_comp_homologyι hM n m hnm)).Exact :=
  (ShortComplex.exact_iff_evaluation _).2 fun i ↦ (T.shortExact hM i).homology_exact₁ n m hnm

/-! ### The long exact sequence in the direct limit -/

variable [HasColimitsOfShape ι (ModuleCat.{max uP uM} R)]
  [HasExactColimitsOfShape ι (ModuleCat.{max uP uM} R)]

/-- **The direct limit is exact at the whole complexes**: when colimits of shape `ι` are exact,
`lim H^n(S i) ⟶ lim H^n(P i) ⟶ lim H^n(P i ∖ S i)` is exact. -/
theorem exact_map_colim_homologyι_homologyπ (n : ℤ) :
    ((ShortComplex.mk _ _ (T.homologyι_comp_homologyπ hM n)).map colim).Exact :=
  (T.exact_homologyι_homologyπ hM n).map colim

/-- **The direct limit is exact at the quotient complexes**: when colimits of shape `ι` are exact,
`lim H^n(P i) ⟶ lim H^n(P i ∖ S i) ⟶ lim H^m(S i)`, for `n + 1 = m`, is exact. -/
theorem exact_map_colim_homologyπ_homologyδ (n m : ℤ) (hnm : n + 1 = m) :
    ((ShortComplex.mk _ _ (T.homologyπ_comp_homologyδ hM n m hnm)).map colim).Exact :=
  (T.exact_homologyπ_homologyδ hM n m hnm).map colim

/-- **The direct limit is exact at the subcomplexes**: when colimits of shape `ι` are exact,
`lim H^n(P i ∖ S i) ⟶ lim H^m(S i) ⟶ lim H^m(P i)`, for `n + 1 = m`, is exact. -/
theorem exact_map_colim_homologyδ_homologyι (n m : ℤ) (hnm : n + 1 = m) :
    ((ShortComplex.mk _ _ (T.homologyδ_comp_homologyι hM n m hnm)).map colim).Exact :=
  (T.exact_homologyδ_homologyι hM n m hnm).map colim

end Subsystem

/-! ### Action windows -/

variable {Γ : Type*} [LinearOrder Γ]

/-- Actions `act i : P i → Γ` on the generators of a continuation system which are **not raised**
by the twisted differentials, by the continuation cocycles, and by some choice of the parametrized
cocycles of the system: each of their entries from `x` to `y` vanishes when `act x < act y`. In
Floer theory these are the actions of the Hamiltonian orbits, for monotone homotopies of
Hamiltonians. -/
structure IsActionNonincreasing (act : ∀ i, S.P i → Γ) : Prop where
  /-- The twisted differentials do not raise the action. -/
  m_eq_zero : ∀ i x y, act i x < act i y → (S.m i).m x y = 0
  /-- The continuation cocycles do not raise the action. -/
  ν_eq_zero : ∀ ⦃i j : ι⦄ (hij : i ≤ j) x y, act i x < act j y → (S.ν hij).ν x y = 0
  /-- Some parametrized cocycle joining the Kronecker cocycle to `ν (le_refl i)` does not raise
  the action. -/
  exists_refl : ∀ i, ∃ η : ParametrizedCocycle
      (ContinuationCocycle.refl h.map_one_eq_zero (S.m i)) (S.ν (le_refl i)),
    ∀ x y, act i x < act i y → η.h x y = 0
  /-- Some parametrized cocycle joining the composite of `ν hij` and `ν hjk` to
  `ν (hij.trans hjk)` does not raise the action. -/
  exists_comp : ∀ ⦃i j k : ι⦄ (hij : i ≤ j) (hjk : j ≤ k),
    ∃ η : ParametrizedCocycle ((S.ν hij).comp h (S.ν hjk)) (S.ν (hij.trans hjk)),
      ∀ x y, act i x < act k y → η.h x y = 0

namespace IsActionNonincreasing

variable {S} {act : ∀ i, S.P i → Γ} (hS : S.IsActionNonincreasing act)

/-- The **action sublevel subsystem**: the generators of action `< a`, which span subcomplexes
throughout the system when the actions are not raised. -/
def sublevel (a : Γ) : S.Subsystem where
  carrier i := {x | act i x < a}
  m_eq_zero i x y hx hy := hS.m_eq_zero i x y (hx.trans_le (not_lt.1 hy))
  ν_eq_zero _ _ hij x y hx hy := hS.ν_eq_zero hij x y (hx.trans_le (not_lt.1 hy))
  exists_refl i := (hS.exists_refl i).imp fun _ hη x y hx hy ↦ hη x y (hx.trans_le (not_lt.1 hy))
  exists_comp _ _ _ hij hjk := (hS.exists_comp hij hjk).imp fun _ hη x y hx hy ↦
    hη x y (hx.trans_le (not_lt.1 hy))

@[simp]
theorem sublevel_carrier (a : Γ) (i : ι) : (hS.sublevel a).carrier i = {x | act i x < a} :=
  (rfl)

end IsActionNonincreasing

end ContinuationSystem

end TauCeti

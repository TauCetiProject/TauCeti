/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Equivalence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Twisted complexes on subsets of generators, and action windows

Let `m` be a twisting cocycle on a finite set `P` of generators. For a set `S ⊆ P` of generators
through which no product `m x y * m y z` with `x, z ∈ S` passes outside `S`, the entries of `m`
between generators of `S` form a twisting cocycle on `S` (`TauCeti.TwistingCocycle.restrict`).
This holds in particular when the twisted differential never leaves `S`, `m x y = 0` for `x ∈ S`
and `y ∉ S`; then `S` spans a subcomplex, and its complement a quotient complex.

* The inclusion of the subcomplex, extension by zero, is the continuation map of the Kronecker
  entries `S × P → A` (`TauCeti.ContinuationCocycle.ofRestrict`).
* The projection onto the quotient, restriction of functions, is the continuation map of the
  Kronecker entries `P × T → A` for the complement `T` (`TauCeti.ContinuationCocycle.toRestrict`).
* Together they form a short exact sequence of twisted cochain complexes
  (`TauCeti.TwistingCocycle.restrictShortComplex_shortExact`).
* A continuation cocycle `ν : mP → mQ` restricts to sets of generators under the analogous
  condition (`TauCeti.ContinuationCocycle.restrict`). If `ν` does not leave the subcomplexes,
  `ν x y = 0` for `x ∈ S` and `y ∉ S'`, it restricts to a continuation cocycle between them
  (`TauCeti.ContinuationCocycle.restrictSubcomplex`), and its continuation morphism carries the
  subcomplex of `S` into the subcomplex of `S'`
  (`TauCeti.ContinuationCocycle.ofRestrict_continuationHom_comp`).
* Dually, if `ν` never enters `T'` from outside `T`, it restricts to a continuation cocycle between
  the quotient complexes (`TauCeti.ContinuationCocycle.restrictQuotient`), and the projections
  commute with the continuation morphisms
  (`TauCeti.ContinuationCocycle.toRestrict_continuationHom_comp`).
* Restriction is functorial: it sends the Kronecker cocycle to the Kronecker cocycle
  (`TauCeti.ContinuationCocycle.restrict_refl`) and composites to composites
  (`TauCeti.ContinuationCocycle.restrict_comp`), in particular for subcomplexes and quotients.
* A parametrized cocycle between continuation cocycles restricts in the same way
  (`TauCeti.ParametrizedCocycle.restrict`, `TauCeti.ParametrizedCocycle.restrictSubcomplex`,
  `TauCeti.ParametrizedCocycle.restrictQuotient`).

In Floer theory the generators carry an action `act : P → ℝ`, and the twisted differential does
not raise it: `m x y = 0` whenever `act x < act y`. The statements below allow actions in any
linearly ordered additive group. Every action window `{x | act x ∈ I}`, for an order-connected
`I`, carries the restricted cocycle (`TauCeti.TwistingCocycle.mul_eq_zero_of_ordConnected`). The
generators of action `< a` span a subcomplex, and the twisted complex is an extension of the
twisted complex of the generators of action `≥ a` by it
(`TauCeti.TwistingCocycle.actionShortComplex_shortExact`): this is the action filtration and its
short exact sequences, the algebraic input of the long exact sequence of Proposition 3.45 of the
reference. A continuation cocycle which raises the action by at most `δ`, `ν x y = 0` whenever
`act x + δ < act' y`, restricts from the generators of action `< a` to those of action `< a + δ`
(`TauCeti.ContinuationCocycle.actionSublevel`), the algebraic part of the filtration estimate of
Proposition 3.22 of the reference; for `δ = 0` it preserves the action filtration. It also
restricts from the generators of action `≥ a` to those of action `≥ a + δ`
(`TauCeti.ContinuationCocycle.actionSuperlevel`), and a parametrized cocycle which raises the
action by at most `δ` restricts to both (`TauCeti.ParametrizedCocycle.actionSublevel`,
`TauCeti.ParametrizedCocycle.actionSuperlevel`). Such bounds add under composition
(`TauCeti.ContinuationCocycle.comp_ν_eq_zero_of_add_lt`), and the action sublevels and
superlevels of a composite at levels `a` and `a + δ₁ + δ₂` are the composites of those at levels
`a` and `a + δ₁` (`TauCeti.ContinuationCocycle.actionSublevel_comp`,
`TauCeti.ContinuationCocycle.actionSuperlevel_comp`).

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3, Proposition 3.22, Corollary 3.24 and
  Proposition 3.45.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti

universe uR uA uM uP

/-- If `f` vanishes from `S` to outside `S'`, it vanishes from outside the complement `T` of `S`
to the complement `T'` of `S'`. -/
theorem apply_eq_zero_of_compl {P Q X : Type*} [Zero X] {f : P → Q → X} {S T : Set P}
    {S' T' : Set Q} (hf : ∀ x y, x ∈ S → y ∉ S' → f x y = 0) (hST : ∀ x, x ∈ T ↔ x ∉ S)
    (hST' : ∀ x, x ∈ T' ↔ x ∉ S') : ∀ x y, x ∉ T → y ∈ T' → f x y = 0 :=
  fun x y hx hy ↦ hf x y (not_not.1 ((hST x).not.1 hx)) ((hST' y).1 hy)

/-! ### Restriction of twisting and continuation cocycles -/

section Cocycle

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {P Q : Type uP} {ind : P → ℤ} {indQ : Q → ℤ} [Fintype P] [Fintype Q]
  {𝒜 : ℤ → Submodule R A} {d : A →ₗ[R] A}

namespace TwistingCocycle

variable (m : TwistingCocycle 𝒜 d P ind)

/-- The **restriction of a twisting cocycle** to a set `S` of generators through which no
product `m x y * m y z`, with `x, z ∈ S`, passes outside `S`: its entries are those of `m` between
generators of `S`. -/
def restrict (S : Set P) [DecidablePred (· ∈ S)]
    (hS : ∀ x y z, x ∈ S → z ∈ S → y ∉ S → m.m x y * m.m y z = 0) :
    TwistingCocycle 𝒜 d S fun x ↦ ind x where
  m x y := m.m x y
  mem_graded x y := m.mem_graded x y
  twisting x y := by
    rw [m.twisting]
    refine Finset.sum_congr_set S _ _ (fun _ _ ↦ rfl) fun z hz ↦ ?_
    rw [hS x z y x.property y.property hz, smul_zero]
  one_sided x y := m.one_sided x y

@[simp]
theorem restrict_m (S : Set P) [DecidablePred (· ∈ S)]
    (hS : ∀ x y z, x ∈ S → z ∈ S → y ∉ S → m.m x y * m.m y z = 0) (x y : S) :
    (m.restrict S hS).m x y = m.m x y :=
  (rfl)

/-- A set of generators which the twisted differential never leaves can be restricted to. -/
theorem mul_eq_zero_of_forall_eq_zero {S : Set P} (hS : ∀ x y, x ∈ S → y ∉ S → m.m x y = 0) :
    ∀ x y z, x ∈ S → z ∈ S → y ∉ S → m.m x y * m.m y z = 0 :=
  fun x y _ hx _ hy ↦ by rw [hS x y hx hy, zero_mul]

/-- A set of generators which the twisted differential never enters from outside can be
restricted to. -/
theorem mul_eq_zero_of_forall_eq_zero' {T : Set P} (hT : ∀ x y, x ∉ T → y ∈ T → m.m x y = 0) :
    ∀ x y z, x ∈ T → z ∈ T → y ∉ T → m.m x y * m.m y z = 0 :=
  fun _ y z _ hz hy ↦ by rw [hT y z hy hz, mul_zero]

/-- If the twisted differential never leaves `S`, it never enters the complement `T` of `S` from
outside. -/
theorem forall_eq_zero_of_compl {S T : Set P} (hS : ∀ x y, x ∈ S → y ∉ S → m.m x y = 0)
    (hST : ∀ x, x ∈ T ↔ x ∉ S) : ∀ x y, x ∉ T → y ∈ T → m.m x y = 0 :=
  apply_eq_zero_of_compl hS hST hST

end TwistingCocycle

namespace ContinuationCocycle

variable [GradedAlgebra 𝒜] [DecidableEq P] (m : TwistingCocycle 𝒜 d P ind) (hd : d 1 = 0)

/-- The **inclusion of the subcomplex** spanned by a set `S` of generators which the twisted
differential never leaves: the Kronecker entries from `S` to `P`, a continuation cocycle from the
restriction of `m` to `S` to `m`. Its continuation map is extension by zero
(`TauCeti.ContinuationCocycle.continuationMap_ofRestrict_apply`). -/
def ofRestrict (S : Set P) [DecidablePred (· ∈ S)] (hS : ∀ x y, x ∈ S → y ∉ S → m.m x y = 0) :
    ContinuationCocycle (m.restrict S (m.mul_eq_zero_of_forall_eq_zero hS)) m where
  ν x y := (1 : Matrix P P A) x y
  mem_graded x y := kronecker_mem_graded (ind := ind) x y
  continuation x y := by
    rw [continuation_kronecker (ind := ind) m.m hd x y]
    congr 1
    -- The entries of the restriction are those of `m` (`TauCeti.TwistingCocycle.restrict_m`).
    exact Finset.sum_congr_set S _ _ (fun _ _ ↦ rfl) fun z hz ↦ by rw [hS x z x.property hz,
        zero_mul]

@[simp]
theorem ofRestrict_ν (S : Set P) [DecidablePred (· ∈ S)]
    (hS : ∀ x y, x ∈ S → y ∉ S → m.m x y = 0) (x : S) (y : P) :
    (ofRestrict m hd S hS).ν x y = (1 : Matrix P P A) x y :=
  (rfl)

/-- The **projection onto the quotient complex** spanned by a set `T` of generators which the
twisted differential never enters from outside: the Kronecker entries from `P` to `T`, a
continuation cocycle from `m` to its restriction to `T`. Its continuation map is restriction of
functions (`TauCeti.ContinuationCocycle.continuationMap_toRestrict_apply`). -/
def toRestrict (T : Set P) [DecidablePred (· ∈ T)] (hT : ∀ x y, x ∉ T → y ∈ T → m.m x y = 0) :
    ContinuationCocycle m (m.restrict T (m.mul_eq_zero_of_forall_eq_zero' hT)) where
  ν x y := (1 : Matrix P P A) x y
  mem_graded x y := kronecker_mem_graded (ind := ind) x y
  continuation x y := by
    rw [continuation_kronecker (ind := ind) m.m hd x y]
    congr 1
    -- The entries of the restriction are those of `m` (`TauCeti.TwistingCocycle.restrict_m`).
    exact Finset.sum_congr_set T _ _ (fun _ _ ↦ rfl) fun z hz ↦ by
      rw [hT z y hz y.property, mul_zero, smul_zero]

@[simp]
theorem toRestrict_ν (T : Set P) [DecidablePred (· ∈ T)]
    (hT : ∀ x y, x ∉ T → y ∈ T → m.m x y = 0) (x : P) (y : T) :
    (toRestrict m hd T hT).ν x y = (1 : Matrix P P A) x y :=
  (rfl)

variable {mP : TwistingCocycle 𝒜 d P ind} {mQ : TwistingCocycle 𝒜 d Q indQ}

omit [GradedAlgebra 𝒜] [DecidableEq P] in
/-- The **restriction of a continuation cocycle** `ν : mP → mQ` to sets `S ⊆ P` and `S' ⊆ Q`
of generators, provided that no product in the continuation equation between generators of `S`
and `S'` passes outside them: its entries are those of `ν` from `S` to `S'`, a continuation
cocycle between the restrictions of `mP` and `mQ`. -/
def restrict (ν : ContinuationCocycle mP mQ) (S : Set P) [DecidablePred (· ∈ S)]
    (hS : ∀ x y z, x ∈ S → z ∈ S → y ∉ S → mP.m x y * mP.m y z = 0)
    (S' : Set Q) [DecidablePred (· ∈ S')]
    (hS' : ∀ x y z, x ∈ S' → z ∈ S' → y ∉ S' → mQ.m x y * mQ.m y z = 0)
    (h₁ : ∀ x z y, x ∈ S → z ∉ S → y ∈ S' → mP.m x z * ν.ν z y = 0)
    (h₂ : ∀ x z y, x ∈ S → z ∉ S' → y ∈ S' → ν.ν x z * mQ.m z y = 0) :
    ContinuationCocycle (mP.restrict S hS) (mQ.restrict S' hS') where
  ν x y := ν.ν x y
  mem_graded x y := ν.mem_graded x y
  continuation x y := by
    rw [ν.continuation]
    -- The entries of the restrictions are those of `mP`, `mQ` and `ν`.
    congr 1
    · exact Finset.sum_congr_set S _ _ (fun _ _ ↦ rfl) fun z hz ↦ h₁ x z y x.property hz y.property
    · exact Finset.sum_congr_set S' _ _ (fun _ _ ↦ rfl) fun z hz ↦ by
        rw [h₂ x z y x.property hz y.property, smul_zero]

omit [GradedAlgebra 𝒜] [DecidableEq P] in
@[simp]
theorem restrict_ν (ν : ContinuationCocycle mP mQ) (S : Set P) [DecidablePred (· ∈ S)]
    (hS : ∀ x y z, x ∈ S → z ∈ S → y ∉ S → mP.m x y * mP.m y z = 0)
    (S' : Set Q) [DecidablePred (· ∈ S')]
    (hS' : ∀ x y z, x ∈ S' → z ∈ S' → y ∉ S' → mQ.m x y * mQ.m y z = 0)
    (h₁ : ∀ x z y, x ∈ S → z ∉ S → y ∈ S' → mP.m x z * ν.ν z y = 0)
    (h₂ : ∀ x z y, x ∈ S → z ∉ S' → y ∈ S' → ν.ν x z * mQ.m z y = 0) (x : S) (y : S') :
    (ν.restrict S hS S' hS' h₁ h₂).ν x y = ν.ν x y :=
  (rfl)

omit [GradedAlgebra 𝒜] [DecidableEq P] in
/-- The **restriction of a continuation cocycle to quotient complexes.** For sets `T ⊆ P` and
`T' ⊆ Q` of generators which the twisted differentials never enter from outside, and a
continuation cocycle `ν : mP → mQ` which never enters `T'` from outside `T`, `ν x y = 0` for
`x ∉ T` and `y ∈ T'`, the entries of `ν` from `T` to `T'` form a continuation cocycle between the
restrictions of `mP` and `mQ` to `T` and `T'`. -/
def restrictQuotient (ν : ContinuationCocycle mP mQ) (T : Set P) [DecidablePred (· ∈ T)]
    (hT : ∀ x y, x ∉ T → y ∈ T → mP.m x y = 0) (T' : Set Q) [DecidablePred (· ∈ T')]
    (hT' : ∀ x y, x ∉ T' → y ∈ T' → mQ.m x y = 0)
    (hν : ∀ x y, x ∉ T → y ∈ T' → ν.ν x y = 0) :
    ContinuationCocycle (mP.restrict T (mP.mul_eq_zero_of_forall_eq_zero' hT))
      (mQ.restrict T' (mQ.mul_eq_zero_of_forall_eq_zero' hT')) :=
  ν.restrict T _ T' _ (fun _ z y _ hz hy ↦ by rw [hν z y hz hy, mul_zero])
    (fun _ z y _ hz hy ↦ by rw [hT' z y hz hy, mul_zero])

omit [GradedAlgebra 𝒜] [DecidableEq P] in
@[simp]
theorem restrictQuotient_ν (ν : ContinuationCocycle mP mQ) (T : Set P) [DecidablePred (· ∈ T)]
    (hT : ∀ x y, x ∉ T → y ∈ T → mP.m x y = 0) (T' : Set Q) [DecidablePred (· ∈ T')]
    (hT' : ∀ x y, x ∉ T' → y ∈ T' → mQ.m x y = 0)
    (hν : ∀ x y, x ∉ T → y ∈ T' → ν.ν x y = 0) (x : T) (y : T') :
    (ν.restrictQuotient T hT T' hT' hν).ν x y = ν.ν x y :=
  (rfl)

omit [GradedAlgebra 𝒜] [DecidableEq P] in
/-- If `ν` never leaves the subcomplexes of `S` and `S'`, it never enters their complements `T` and
`T'` from outside. -/
theorem forall_eq_zero_of_compl (ν : ContinuationCocycle mP mQ) {S T : Set P} {S' T' : Set Q}
    (hν : ∀ x y, x ∈ S → y ∉ S' → ν.ν x y = 0) (hST : ∀ x, x ∈ T ↔ x ∉ S)
    (hST' : ∀ x, x ∈ T' ↔ x ∉ S') : ∀ x y, x ∉ T → y ∈ T' → ν.ν x y = 0 :=
  apply_eq_zero_of_compl hν hST hST'

end ContinuationCocycle

end Cocycle

/-! ### The continuation maps of the inclusion and the projection -/

section Maps

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommMonoid M] [Module R M] [Module Aᵐᵒᵖ M]
  [SMulCommClass R Aᵐᵒᵖ M] {P : Type uP} {ind : P → ℤ} [Fintype P] [DecidableEq P]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}
  (m : TwistingCocycle 𝒜 d P ind) (hd : d 1 = 0)

namespace ContinuationCocycle

/-- The continuation map of `TauCeti.ContinuationCocycle.ofRestrict` is extension by zero. -/
@[simp]
theorem continuationMap_ofRestrict_apply (S : Set P) [DecidablePred (· ∈ S)]
    (hS : ∀ x y, x ∈ S → y ∉ S → m.m x y = 0) (f : S → M) (y : P) :
    continuationMap R M (ofRestrict m hd S hS).ν f y = if hy : y ∈ S then f ⟨y, hy⟩ else 0 := by
  rw [continuationMap_apply]
  split_ifs with hy
  · rw [Finset.sum_eq_single_of_mem ⟨y, hy⟩ (Finset.mem_univ _) fun x _ hx ↦ by
      rw [ofRestrict_ν, Matrix.one_apply_ne fun h ↦ hx (Subtype.ext h), op_zero, zero_smul]]
    simp
  · refine Finset.sum_eq_zero fun x _ ↦ ?_
    rw [ofRestrict_ν, Matrix.one_apply_ne fun h ↦ hy (by rw [← h]; exact x.property), op_zero,
        zero_smul]

/-- The continuation map of `TauCeti.ContinuationCocycle.toRestrict` is restriction of
functions. -/
@[simp]
theorem continuationMap_toRestrict_apply (T : Set P) [DecidablePred (· ∈ T)]
    (hT : ∀ x y, x ∉ T → y ∈ T → m.m x y = 0) (f : P → M) (y : T) :
    continuationMap R M (toRestrict m hd T hT).ν f y = f y := by
  rw [continuationMap_apply, Finset.sum_eq_single_of_mem (y : P) (Finset.mem_univ _) fun x _ hx ↦ by
    rw [toRestrict_ν, Matrix.one_apply_ne hx, op_zero, zero_smul]]
  simp

end ContinuationCocycle

end Maps

/-! ### The short exact sequence of a subcomplex and its quotient -/

section ShortExact

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {P : Type uP} {ind : P → ℤ} [Fintype P] [DecidableEq P]
  [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ] {dM : M →ₗ[R] M}
  (m : TwistingCocycle 𝒜 d P ind) (hM : IsDGRightModule h ℳ dM)

namespace TwistingCocycle

/-- In each degree, the projection onto the quotient complex of a set `T` of generators which the
twisted differential never enters from outside is surjective: a function on `T` extends by zero to
`P`, in the same total degree. -/
theorem surjective_toRestrict_continuationHom_f (T : Set P) [DecidablePred (· ∈ T)]
    (hT : ∀ x y, x ∉ T → y ∈ T → m.m x y = 0) (n : ℤ) :
    Function.Surjective
      (((ContinuationCocycle.toRestrict m h.map_one_eq_zero T hT).continuationHom hM).f n) := by
  intro g
  refine ⟨(twistedCochainComplexXEquiv m.mem_graded m.twisting hM n).symm
    ⟨_, extendByZero_mem_twistedTotalGrading (twistedCochainComplexXEquiv
      (TwistingCocycle.mem_graded _) (TwistingCocycle.twisting _) hM n g).property⟩,
    (twistedCochainComplexXEquiv (TwistingCocycle.mem_graded _) (TwistingCocycle.twisting _) hM
      n).injective (Subtype.ext (funext fun y ↦ ?_))⟩
  simp

variable (S T : Set P) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
  (hS : ∀ x y, x ∈ S → y ∉ S → m.m x y = 0) (hST : ∀ x, x ∈ T ↔ x ∉ S)

include hS hST

/-- The composite of the inclusion of the subcomplex of `S` and the projection onto the
quotient complex of its complement `T` vanishes. -/
theorem ofRestrict_continuationHom_comp_toRestrict_continuationHom :
    (ContinuationCocycle.ofRestrict m h.map_one_eq_zero S hS).continuationHom hM ≫
      (ContinuationCocycle.toRestrict m h.map_one_eq_zero T
        (m.forall_eq_zero_of_compl hS hST)).continuationHom hM = 0 := by
  rw [← ContinuationCocycle.continuationHom_comp]
  refine HomologicalComplex.hom_ext _ _ fun n ↦ termHom_ext fun f ↦ ?_
  rw [ContinuationCocycle.continuationHom_f_apply, ContinuationCocycle.continuationMap_comp]
  funext y
  simp [(hST y).1 y.property]

/-- **The short complex of a subcomplex and its quotient.** For a set `S` of generators which
the twisted differential never leaves, with complement `T`, the inclusion of the twisted complex
on `S` (extension by zero) followed by the projection onto the twisted complex on `T`
(restriction of functions). -/
@[expose]
noncomputable def restrictShortComplex :
    ShortComplex (CochainComplex (ModuleCat.{max uP uM} R) ℤ) :=
  ShortComplex.mk _ _ (m.ofRestrict_continuationHom_comp_toRestrict_continuationHom hM S T hS hST)

@[simp]
theorem restrictShortComplex_X₁ :
    (m.restrictShortComplex hM S T hS hST).X₁ =
      (m.restrict S (m.mul_eq_zero_of_forall_eq_zero hS)).twistedCochainComplex dM hM :=
  (rfl)

@[simp]
theorem restrictShortComplex_X₂ :
    (m.restrictShortComplex hM S T hS hST).X₂ = m.twistedCochainComplex dM hM :=
  (rfl)

@[simp]
theorem restrictShortComplex_X₃ :
    (m.restrictShortComplex hM S T hS hST).X₃ =
      (m.restrict T (m.mul_eq_zero_of_forall_eq_zero'
        (m.forall_eq_zero_of_compl hS hST))).twistedCochainComplex dM hM :=
  (rfl)

/-- The first map of `TauCeti.TwistingCocycle.restrictShortComplex` is the inclusion of the
subcomplex of `S`. -/
@[simp]
theorem restrictShortComplex_f :
    (m.restrictShortComplex hM S T hS hST).f =
      (ContinuationCocycle.ofRestrict m h.map_one_eq_zero S hS).continuationHom hM :=
  (rfl)

/-- The second map of `TauCeti.TwistingCocycle.restrictShortComplex` is the projection onto the
quotient complex of `T`. -/
@[simp]
theorem restrictShortComplex_g :
    (m.restrictShortComplex hM S T hS hST).g =
      (ContinuationCocycle.toRestrict m h.map_one_eq_zero T
        (m.forall_eq_zero_of_compl hS hST)).continuationHom hM :=
  (rfl)

omit hST in
/-- In each degree, the inclusion of the subcomplex is injective: extension by zero forgets
nothing. -/
theorem injective_ofRestrict_continuationHom_f (n : ℤ) :
    Function.Injective (((ContinuationCocycle.ofRestrict m h.map_one_eq_zero S hS).continuationHom
      hM).f n) := by
  intro f g hfg
  have hfg' := congrArg (fun x ↦ (twistedCochainComplexXEquiv m.mem_graded m.twisting hM n x :
    P → M)) hfg
  simp only [ContinuationCocycle.continuationHom_f_apply] at hfg'
  refine (twistedCochainComplexXEquiv (TwistingCocycle.mem_graded _) (TwistingCocycle.twisting _)
    hM n).injective (Subtype.ext (funext fun x ↦ ?_))
  simpa [x.property] using congrFun hfg' x

/-- In each degree, an element whose restriction to `T` vanishes is the extension by zero of its
restriction to `S`. -/
theorem exists_ofRestrict_continuationHom_f_eq (n : ℤ)
    (g : (m.twistedCochainComplex dM hM).X n)
    (hg : ((ContinuationCocycle.toRestrict m h.map_one_eq_zero T
      (m.forall_eq_zero_of_compl hS hST)).continuationHom hM).f n g = 0) :
    ∃ f, ((ContinuationCocycle.ofRestrict m h.map_one_eq_zero S hS).continuationHom hM).f n f =
      g := by
  have hg' := congrArg (fun x ↦ (twistedCochainComplexXEquiv (TwistingCocycle.mem_graded _)
    (TwistingCocycle.twisting _) hM n x : T → M)) hg
  simp only [ContinuationCocycle.continuationHom_f_apply, map_zero, ZeroMemClass.coe_zero] at hg'
  refine ⟨(twistedCochainComplexXEquiv (TwistingCocycle.mem_graded _) (TwistingCocycle.twisting _)
    hM n).symm ⟨_, domRestrict_mem_twistedTotalGrading S
      (twistedCochainComplexXEquiv m.mem_graded m.twisting hM n g).property⟩,
    (twistedCochainComplexXEquiv m.mem_graded m.twisting hM n).injective
      (Subtype.ext (funext fun y ↦ ?_))⟩
  rw [ContinuationCocycle.continuationHom_f_apply,
    ContinuationCocycle.continuationMap_ofRestrict_apply]
  split_ifs with hy
  · simp
  · simpa using (congrFun hg' ⟨y, (hST y).2 hy⟩).symm

/-- **A subcomplex and its quotient form a short exact sequence.** For a set `S` of generators
which the twisted differential never leaves, with complement `T`, the twisted complex on `S`, the
twisted complex on `P` and the twisted complex on `T` form a short exact sequence of cochain
complexes. -/
theorem restrictShortComplex_shortExact :
    (m.restrictShortComplex hM S T hS hST).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    ShortComplex.ShortExact.mk'
      ((ShortComplex.moduleCat_exact_iff _).mpr
        (m.exists_ofRestrict_continuationHom_f_eq hM S T hS hST n))
      ((ModuleCat.mono_iff_injective _).mpr (m.injective_ofRestrict_continuationHom_f hM S hS n))
      ((ModuleCat.epi_iff_surjective _).mpr
        (m.surjective_toRestrict_continuationHom_f hM T (m.forall_eq_zero_of_compl hS hST) n))

end TwistingCocycle

end ShortExact

/-! ### Continuation maps between subcomplexes -/

section ContinuationSubcomplex

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {P Q : Type uP} {ind : P → ℤ} {indQ : Q → ℤ} [Fintype P] [Fintype Q]
  [DecidableEq P] [DecidableEq Q]
  [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} (h : IsDGAlgebra 𝒜 d)
  {mP : TwistingCocycle 𝒜 d P ind} {mQ : TwistingCocycle 𝒜 d Q indQ}
  (ν : ContinuationCocycle mP mQ)
  (S : Set P) [DecidablePred (· ∈ S)] (hS : ∀ x y, x ∈ S → y ∉ S → mP.m x y = 0)
  (S' : Set Q) [DecidablePred (· ∈ S')] (hS' : ∀ x y, x ∈ S' → y ∉ S' → mQ.m x y = 0)
  (hν : ∀ x y, x ∈ S → y ∉ S' → ν.ν x y = 0)

namespace ContinuationCocycle

omit [DecidableEq P] [DecidableEq Q] [GradedAlgebra 𝒜] in
/-- The restriction of a continuation cocycle `ν : mP → mQ` to the subcomplexes of sets `S ⊆ P`
and `S' ⊆ Q` of generators which the twisted differentials never leave, when `ν` never leaves
them either: `ν x y = 0` for `x ∈ S` and `y ∉ S'`. -/
def restrictSubcomplex : ContinuationCocycle (mP.restrict S (mP.mul_eq_zero_of_forall_eq_zero hS))
    (mQ.restrict S' (mQ.mul_eq_zero_of_forall_eq_zero hS')) :=
  ν.restrict S _ S' _ (fun x z _ hx hz _ ↦ by rw [hS x z hx hz, zero_mul])
    (fun x z _ hx hz _ ↦ by rw [hν x z hx hz, zero_mul])

omit [DecidableEq P] [DecidableEq Q] [GradedAlgebra 𝒜] in
@[simp]
theorem restrictSubcomplex_ν (x : S) (y : S') :
    (ν.restrictSubcomplex S hS S' hS' hν).ν x y = ν.ν x y :=
  (rfl)

/-- **Continuation maps preserve subcomplexes they never leave.** If `ν x y = 0` for `x ∈ S` and
`y ∉ S'`, the inclusion of the subcomplex of `S` followed by `ν` is the restriction of `ν`
followed by the inclusion of the subcomplex of `S'`. -/
theorem ofRestrict_comp :
    (ofRestrict mP h.map_one_eq_zero S hS).comp h ν =
      (ν.restrictSubcomplex S hS S' hS' hν).comp h (ofRestrict mQ h.map_one_eq_zero S' hS') := by
  ext x y
  rw [comp_ν, comp_ν, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.of_apply, ofRestrict_ν, restrictSubcomplex_ν]
  -- Both sides are `ν x y`: on the right, the generators outside `S'` contribute nothing.
  rw [← Finset.sum_congr_set S' (fun z ↦ ν.ν x z * (1 : Matrix Q Q A) z y)
    (fun z ↦ ν.ν x z * (1 : Matrix Q Q A) z y) (fun _ _ ↦ rfl) fun z hz ↦ by
      rw [hν x z x.property hz, zero_mul]]
  simp [Matrix.one_apply]

/-- **Continuation maps commute with the projections onto quotient complexes.** If `ν` never
enters `T'` from outside `T`, the projection onto the quotient complex of `T` followed by the
restriction of `ν` is `ν` followed by the projection onto the quotient complex of `T'`. -/
theorem toRestrict_comp (T : Set P) [DecidablePred (· ∈ T)]
    (hT : ∀ x y, x ∉ T → y ∈ T → mP.m x y = 0) (T' : Set Q) [DecidablePred (· ∈ T')]
    (hT' : ∀ x y, x ∉ T' → y ∈ T' → mQ.m x y = 0)
    (hν : ∀ x y, x ∉ T → y ∈ T' → ν.ν x y = 0) :
    (toRestrict mP h.map_one_eq_zero T hT).comp h (ν.restrictQuotient T hT T' hT' hν) =
      ν.comp h (toRestrict mQ h.map_one_eq_zero T' hT') := by
  ext x y
  simp only [comp_ν, Matrix.mul_apply, Matrix.of_apply, toRestrict_ν, restrictQuotient_ν]
  rw [Finset.sum_eq_single_of_mem (y : Q) (Finset.mem_univ _) fun z _ hz ↦ by
    rw [Matrix.one_apply_ne hz, mul_zero], Matrix.one_apply_eq, mul_one]
  -- Both sides are `ν x y` when `x ∈ T`, and both vanish otherwise.
  by_cases hx : x ∈ T
  · rw [Finset.sum_eq_single_of_mem (⟨x, hx⟩ : T) (Finset.mem_univ _) fun z _ hz ↦ by
      rw [Matrix.one_apply_ne fun h ↦ hz (Subtype.ext h.symm), zero_mul]]
    simp
  · rw [hν x y hx y.property]
    exact Finset.sum_eq_zero fun z _ ↦ by
      rw [Matrix.one_apply_ne fun h ↦ hx (by rw [h]; exact z.property), zero_mul]

variable {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ] {dM : M →ₗ[R] M}
  (hM : IsDGRightModule h ℳ dM)

/-- **The continuation morphism carries the subcomplex of `S` into the subcomplex of `S'`**, when
`ν x y = 0` for `x ∈ S` and `y ∉ S'`: the square of twisted cochain complexes formed by the two
inclusions, the continuation morphism of `ν` and that of its restriction commutes. -/
@[reassoc]
theorem ofRestrict_continuationHom_comp :
    (ofRestrict mP h.map_one_eq_zero S hS).continuationHom hM ≫ ν.continuationHom hM =
      (ν.restrictSubcomplex S hS S' hS' hν).continuationHom hM ≫
        (ofRestrict mQ h.map_one_eq_zero S' hS').continuationHom hM := by
  rw [← continuationHom_comp, ← continuationHom_comp, ofRestrict_comp h ν S hS S' hS' hν]

/-- **The continuation morphism commutes with the projections onto quotient complexes**, when `ν`
never enters `T'` from outside `T`: the square of twisted cochain complexes formed by the two
projections, the continuation morphism of `ν` and that of its restriction commutes. -/
@[reassoc]
theorem toRestrict_continuationHom_comp (T : Set P) [DecidablePred (· ∈ T)]
    (hT : ∀ x y, x ∉ T → y ∈ T → mP.m x y = 0) (T' : Set Q) [DecidablePred (· ∈ T')]
    (hT' : ∀ x y, x ∉ T' → y ∈ T' → mQ.m x y = 0)
    (hν : ∀ x y, x ∉ T → y ∈ T' → ν.ν x y = 0) :
    (toRestrict mP h.map_one_eq_zero T hT).continuationHom hM ≫
        (ν.restrictQuotient T hT T' hT' hν).continuationHom hM =
      ν.continuationHom hM ≫ (toRestrict mQ h.map_one_eq_zero T' hT').continuationHom hM := by
  rw [← continuationHom_comp, ← continuationHom_comp, toRestrict_comp h ν T hT T' hT' hν]

end ContinuationCocycle

end ContinuationSubcomplex

/-! ### Functoriality of restriction -/

section Functoriality

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {P Q W : Type uP} {ind : P → ℤ} {indQ : Q → ℤ} {indW : W → ℤ} [Fintype P] [Fintype Q]
  [Fintype W] {𝒜 : ℤ → Submodule R A} {d : A →ₗ[R] A}
  {mP : TwistingCocycle 𝒜 d P ind} {mQ : TwistingCocycle 𝒜 d Q indQ}
  {mW : TwistingCocycle 𝒜 d W indW}

namespace ContinuationCocycle

variable [GradedAlgebra 𝒜]

/-- The restriction of the Kronecker cocycle is the Kronecker cocycle. -/
@[simp]
theorem restrict_refl [DecidableEq P] (hd : d 1 = 0) (S : Set P) [DecidablePred (· ∈ S)]
    (hS : ∀ x y z, x ∈ S → z ∈ S → y ∉ S → mP.m x y * mP.m y z = 0)
    (h₁ : ∀ x z y, x ∈ S → z ∉ S → y ∈ S → mP.m x z * (refl hd mP).ν z y = 0)
    (h₂ : ∀ x z y, x ∈ S → z ∉ S → y ∈ S → (refl hd mP).ν x z * mP.m z y = 0) :
    (refl hd mP).restrict S hS S hS h₁ h₂ = refl hd _ := by
  ext x y
  simp [Matrix.one_apply, Subtype.ext_iff]

/-- The restriction of the Kronecker cocycle to a subcomplex is the Kronecker cocycle. -/
@[simp]
theorem restrictSubcomplex_refl [DecidableEq P] (hd : d 1 = 0) (S : Set P)
    [DecidablePred (· ∈ S)] (hS : ∀ x y, x ∈ S → y ∉ S → mP.m x y = 0)
    (hν : ∀ x y, x ∈ S → y ∉ S → (refl hd mP).ν x y = 0) :
    (refl hd mP).restrictSubcomplex S hS S hS hν = refl hd _ :=
  restrict_refl hd S _ _ _

/-- The restriction of the Kronecker cocycle to a quotient complex is the Kronecker cocycle. -/
@[simp]
theorem restrictQuotient_refl [DecidableEq P] (hd : d 1 = 0) (T : Set P) [DecidablePred (· ∈ T)]
    (hT : ∀ x y, x ∉ T → y ∈ T → mP.m x y = 0)
    (hν : ∀ x y, x ∉ T → y ∈ T → (refl hd mP).ν x y = 0) :
    (refl hd mP).restrictQuotient T hT T hT hν = refl hd _ :=
  restrict_refl hd T _ _ _

variable (h : IsDGAlgebra 𝒜 d)

/-- **Restriction is functorial**: if no product `ν₁ x z * ν₂ z y` with `x ∈ S₁` and `y ∈ S₃`
passes outside `S₂`, the restriction of the composite is the composite of the restrictions. -/
theorem restrict_comp (ν₁ : ContinuationCocycle mP mQ) (ν₂ : ContinuationCocycle mQ mW)
    (S₁ : Set P) [DecidablePred (· ∈ S₁)]
    (hS₁ : ∀ x y z, x ∈ S₁ → z ∈ S₁ → y ∉ S₁ → mP.m x y * mP.m y z = 0)
    (S₂ : Set Q) [DecidablePred (· ∈ S₂)]
    (hS₂ : ∀ x y z, x ∈ S₂ → z ∈ S₂ → y ∉ S₂ → mQ.m x y * mQ.m y z = 0)
    (S₃ : Set W) [DecidablePred (· ∈ S₃)]
    (hS₃ : ∀ x y z, x ∈ S₃ → z ∈ S₃ → y ∉ S₃ → mW.m x y * mW.m y z = 0)
    (h₁₁ : ∀ x z y, x ∈ S₁ → z ∉ S₁ → y ∈ S₂ → mP.m x z * ν₁.ν z y = 0)
    (h₁₂ : ∀ x z y, x ∈ S₁ → z ∉ S₂ → y ∈ S₂ → ν₁.ν x z * mQ.m z y = 0)
    (h₂₁ : ∀ x z y, x ∈ S₂ → z ∉ S₂ → y ∈ S₃ → mQ.m x z * ν₂.ν z y = 0)
    (h₂₂ : ∀ x z y, x ∈ S₂ → z ∉ S₃ → y ∈ S₃ → ν₂.ν x z * mW.m z y = 0)
    (h₁ : ∀ x z y, x ∈ S₁ → z ∉ S₁ → y ∈ S₃ → mP.m x z * (ν₁.comp h ν₂).ν z y = 0)
    (h₂ : ∀ x z y, x ∈ S₁ → z ∉ S₃ → y ∈ S₃ → (ν₁.comp h ν₂).ν x z * mW.m z y = 0)
    (hν : ∀ x z y, x ∈ S₁ → z ∉ S₂ → y ∈ S₃ → ν₁.ν x z * ν₂.ν z y = 0) :
    (ν₁.comp h ν₂).restrict S₁ hS₁ S₃ hS₃ h₁ h₂ =
      (ν₁.restrict S₁ hS₁ S₂ hS₂ h₁₁ h₁₂).comp h (ν₂.restrict S₂ hS₂ S₃ hS₃ h₂₁ h₂₂) := by
  ext x y
  simp only [restrict_ν, comp_ν, Matrix.mul_apply, Matrix.of_apply]
  -- The intermediate generators outside `S₂` contribute nothing.
  exact Finset.sum_congr_set S₂ _ _ (fun _ _ ↦ rfl) fun z hz ↦ hν x z y x.property hz y.property

/-- If `ν₁` never leaves the subcomplexes of `S₁` and `S₂` and `ν₂` those of `S₂` and `S₃`, then
their composite never leaves the subcomplexes of `S₁` and `S₃`. -/
theorem comp_ν_eq_zero_of_forall_eq_zero (ν₁ : ContinuationCocycle mP mQ)
    (ν₂ : ContinuationCocycle mQ mW) {S₁ : Set P} {S₂ : Set Q} {S₃ : Set W}
    (hν₁ : ∀ x y, x ∈ S₁ → y ∉ S₂ → ν₁.ν x y = 0) (hν₂ : ∀ x y, x ∈ S₂ → y ∉ S₃ → ν₂.ν x y = 0) :
    ∀ x y, x ∈ S₁ → y ∉ S₃ → (ν₁.comp h ν₂).ν x y = 0 := by
  intro x y hx hy
  rw [comp_ν, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun z _ ↦ ?_
  by_cases hz : z ∈ S₂
  · simp [hν₂ z y hz hy]
  · simp [hν₁ x z hx hz]

/-- **Restriction to subcomplexes is functorial**: the restriction of a composite is the composite
of the restrictions. -/
theorem restrictSubcomplex_comp (ν₁ : ContinuationCocycle mP mQ) (ν₂ : ContinuationCocycle mQ mW)
    (S₁ : Set P) [DecidablePred (· ∈ S₁)] (hS₁ : ∀ x y, x ∈ S₁ → y ∉ S₁ → mP.m x y = 0)
    (S₂ : Set Q) [DecidablePred (· ∈ S₂)] (hS₂ : ∀ x y, x ∈ S₂ → y ∉ S₂ → mQ.m x y = 0)
    (S₃ : Set W) [DecidablePred (· ∈ S₃)] (hS₃ : ∀ x y, x ∈ S₃ → y ∉ S₃ → mW.m x y = 0)
    (hν₁ : ∀ x y, x ∈ S₁ → y ∉ S₂ → ν₁.ν x y = 0) (hν₂ : ∀ x y, x ∈ S₂ → y ∉ S₃ → ν₂.ν x y = 0)
    (hν : ∀ x y, x ∈ S₁ → y ∉ S₃ → (ν₁.comp h ν₂).ν x y = 0) :
    (ν₁.comp h ν₂).restrictSubcomplex S₁ hS₁ S₃ hS₃ hν =
      (ν₁.restrictSubcomplex S₁ hS₁ S₂ hS₂ hν₁).comp h
        (ν₂.restrictSubcomplex S₂ hS₂ S₃ hS₃ hν₂) :=
  -- The intermediate generators outside `S₂` contribute nothing, since `ν₁` never leaves `S₂`.
  restrict_comp h ν₁ ν₂ S₁ _ S₂ _ S₃ _ _ _ _ _ _ _ fun x z _ hx hz _ ↦ by
    rw [hν₁ x z hx hz, zero_mul]

/-- **Restriction to quotient complexes is functorial**: the restriction of a composite is the
composite of the restrictions. -/
theorem restrictQuotient_comp (ν₁ : ContinuationCocycle mP mQ) (ν₂ : ContinuationCocycle mQ mW)
    (T₁ : Set P) [DecidablePred (· ∈ T₁)] (hT₁ : ∀ x y, x ∉ T₁ → y ∈ T₁ → mP.m x y = 0)
    (T₂ : Set Q) [DecidablePred (· ∈ T₂)] (hT₂ : ∀ x y, x ∉ T₂ → y ∈ T₂ → mQ.m x y = 0)
    (T₃ : Set W) [DecidablePred (· ∈ T₃)] (hT₃ : ∀ x y, x ∉ T₃ → y ∈ T₃ → mW.m x y = 0)
    (hν₁ : ∀ x y, x ∉ T₁ → y ∈ T₂ → ν₁.ν x y = 0) (hν₂ : ∀ x y, x ∉ T₂ → y ∈ T₃ → ν₂.ν x y = 0)
    (hν : ∀ x y, x ∉ T₁ → y ∈ T₃ → (ν₁.comp h ν₂).ν x y = 0) :
    (ν₁.comp h ν₂).restrictQuotient T₁ hT₁ T₃ hT₃ hν =
      (ν₁.restrictQuotient T₁ hT₁ T₂ hT₂ hν₁).comp h
        (ν₂.restrictQuotient T₂ hT₂ T₃ hT₃ hν₂) :=
  -- The intermediate generators outside `T₂` contribute nothing, since `ν₂` never enters `T₃`
  -- from outside `T₂`.
  restrict_comp h ν₁ ν₂ T₁ _ T₂ _ T₃ _ _ _ _ _ _ _ fun _ z y _ hz hy ↦ by
    rw [hν₂ z y hz hy, mul_zero]

end ContinuationCocycle

end Functoriality

/-! ### Restriction of parametrized cocycles -/

section Parametrized

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {P Q : Type uP} {ind : P → ℤ} {indQ : Q → ℤ} [Fintype P] [Fintype Q]
  {𝒜 : ℤ → Submodule R A} {d : A →ₗ[R] A}
  {mP : TwistingCocycle 𝒜 d P ind} {mQ : TwistingCocycle 𝒜 d Q indQ}

namespace ParametrizedCocycle

variable {ν₀ ν₁ : ContinuationCocycle mP mQ}

/-- The **restriction of a parametrized cocycle** `η` between `ν₀` and `ν₁` to sets `S ⊆ P` and
`S' ⊆ Q` of generators, provided that no product in the parametrized equation between generators
of `S` and `S'` passes outside them: its entries are those of `η` from `S` to `S'`, a parametrized
cocycle between the restrictions of `ν₀` and `ν₁`. -/
def restrict (η : ParametrizedCocycle ν₀ ν₁) (S : Set P) [DecidablePred (· ∈ S)]
    (hS : ∀ x y z, x ∈ S → z ∈ S → y ∉ S → mP.m x y * mP.m y z = 0)
    (S' : Set Q) [DecidablePred (· ∈ S')]
    (hS' : ∀ x y z, x ∈ S' → z ∈ S' → y ∉ S' → mQ.m x y * mQ.m y z = 0)
    (h₀₁ : ∀ x z y, x ∈ S → z ∉ S → y ∈ S' → mP.m x z * ν₀.ν z y = 0)
    (h₀₂ : ∀ x z y, x ∈ S → z ∉ S' → y ∈ S' → ν₀.ν x z * mQ.m z y = 0)
    (h₁₁ : ∀ x z y, x ∈ S → z ∉ S → y ∈ S' → mP.m x z * ν₁.ν z y = 0)
    (h₁₂ : ∀ x z y, x ∈ S → z ∉ S' → y ∈ S' → ν₁.ν x z * mQ.m z y = 0)
    (hη₁ : ∀ x z y, x ∈ S → z ∉ S → y ∈ S' → mP.m x z * η.h z y = 0)
    (hη₂ : ∀ x z y, x ∈ S → z ∉ S' → y ∈ S' → η.h x z * mQ.m z y = 0) :
    ParametrizedCocycle (ν₀.restrict S hS S' hS' h₀₁ h₀₂) (ν₁.restrict S hS S' hS' h₁₁ h₁₂) where
  h x y := η.h x y
  mem_graded x y := η.mem_graded x y
  parametrized x y := by
    rw [η.parametrized]
    simp only [ContinuationCocycle.restrict_ν, TwistingCocycle.restrict_m]
    -- The generators outside `S` and `S'` contribute nothing to either sum.
    congr 1
    · congr 1
      exact Finset.sum_congr_set S _ _ (fun _ _ ↦ rfl) fun z hz ↦ by
        rw [hη₁ x z y x.property hz y.property, smul_zero]
    · exact Finset.sum_congr_set S' _ _ (fun _ _ ↦ rfl) fun z hz ↦ by
        rw [hη₂ x z y x.property hz y.property, smul_zero]

@[simp]
theorem restrict_h (η : ParametrizedCocycle ν₀ ν₁) (S : Set P) [DecidablePred (· ∈ S)]
    (hS : ∀ x y z, x ∈ S → z ∈ S → y ∉ S → mP.m x y * mP.m y z = 0)
    (S' : Set Q) [DecidablePred (· ∈ S')]
    (hS' : ∀ x y z, x ∈ S' → z ∈ S' → y ∉ S' → mQ.m x y * mQ.m y z = 0)
    (h₀₁ : ∀ x z y, x ∈ S → z ∉ S → y ∈ S' → mP.m x z * ν₀.ν z y = 0)
    (h₀₂ : ∀ x z y, x ∈ S → z ∉ S' → y ∈ S' → ν₀.ν x z * mQ.m z y = 0)
    (h₁₁ : ∀ x z y, x ∈ S → z ∉ S → y ∈ S' → mP.m x z * ν₁.ν z y = 0)
    (h₁₂ : ∀ x z y, x ∈ S → z ∉ S' → y ∈ S' → ν₁.ν x z * mQ.m z y = 0)
    (hη₁ : ∀ x z y, x ∈ S → z ∉ S → y ∈ S' → mP.m x z * η.h z y = 0)
    (hη₂ : ∀ x z y, x ∈ S → z ∉ S' → y ∈ S' → η.h x z * mQ.m z y = 0) (x : S) (y : S') :
    (η.restrict S hS S' hS' h₀₁ h₀₂ h₁₁ h₁₂ hη₁ hη₂).h x y = η.h x y :=
  (rfl)

/-- The **restriction of a parametrized cocycle to subcomplexes.** If the parametrized cocycle `η`
between `ν₀` and `ν₁` never leaves the subcomplexes of `S` and `S'`, `η.h x y = 0` for `x ∈ S` and
`y ∉ S'`, its entries between them form a parametrized cocycle between the restrictions of `ν₀`
and `ν₁`. -/
def restrictSubcomplex (η : ParametrizedCocycle ν₀ ν₁) (S : Set P) [DecidablePred (· ∈ S)]
    (hS : ∀ x y, x ∈ S → y ∉ S → mP.m x y = 0) (S' : Set Q) [DecidablePred (· ∈ S')]
    (hS' : ∀ x y, x ∈ S' → y ∉ S' → mQ.m x y = 0) (hν₀ : ∀ x y, x ∈ S → y ∉ S' → ν₀.ν x y = 0)
    (hν₁ : ∀ x y, x ∈ S → y ∉ S' → ν₁.ν x y = 0) (hη : ∀ x y, x ∈ S → y ∉ S' → η.h x y = 0) :
    ParametrizedCocycle (ν₀.restrictSubcomplex S hS S' hS' hν₀)
      (ν₁.restrictSubcomplex S hS S' hS' hν₁) :=
  η.restrict S _ S' _ _ _ _ _ (fun x z _ hx hz _ ↦ by rw [hS x z hx hz, zero_mul])
    (fun x z _ hx hz _ ↦ by rw [hη x z hx hz, zero_mul])

@[simp]
theorem restrictSubcomplex_h (η : ParametrizedCocycle ν₀ ν₁) (S : Set P) [DecidablePred (· ∈ S)]
    (hS : ∀ x y, x ∈ S → y ∉ S → mP.m x y = 0) (S' : Set Q) [DecidablePred (· ∈ S')]
    (hS' : ∀ x y, x ∈ S' → y ∉ S' → mQ.m x y = 0) (hν₀ : ∀ x y, x ∈ S → y ∉ S' → ν₀.ν x y = 0)
    (hν₁ : ∀ x y, x ∈ S → y ∉ S' → ν₁.ν x y = 0) (hη : ∀ x y, x ∈ S → y ∉ S' → η.h x y = 0)
    (x : S) (y : S') : (η.restrictSubcomplex S hS S' hS' hν₀ hν₁ hη).h x y = η.h x y :=
  (rfl)

/-- The **restriction of a parametrized cocycle to quotient complexes.** If the parametrized
cocycle `η` between `ν₀` and `ν₁` never enters `T'` from outside `T`, `η.h x y = 0` for `x ∉ T`
and `y ∈ T'`, its entries between them form a parametrized cocycle between the restrictions of
`ν₀` and `ν₁`. -/
def restrictQuotient (η : ParametrizedCocycle ν₀ ν₁) (T : Set P) [DecidablePred (· ∈ T)]
    (hT : ∀ x y, x ∉ T → y ∈ T → mP.m x y = 0) (T' : Set Q) [DecidablePred (· ∈ T')]
    (hT' : ∀ x y, x ∉ T' → y ∈ T' → mQ.m x y = 0) (hν₀ : ∀ x y, x ∉ T → y ∈ T' → ν₀.ν x y = 0)
    (hν₁ : ∀ x y, x ∉ T → y ∈ T' → ν₁.ν x y = 0) (hη : ∀ x y, x ∉ T → y ∈ T' → η.h x y = 0) :
    ParametrizedCocycle (ν₀.restrictQuotient T hT T' hT' hν₀)
      (ν₁.restrictQuotient T hT T' hT' hν₁) :=
  η.restrict T _ T' _ _ _ _ _ (fun _ z y _ hz hy ↦ by rw [hη z y hz hy, mul_zero])
    (fun _ z y _ hz hy ↦ by rw [hT' z y hz hy, mul_zero])

@[simp]
theorem restrictQuotient_h (η : ParametrizedCocycle ν₀ ν₁) (T : Set P) [DecidablePred (· ∈ T)]
    (hT : ∀ x y, x ∉ T → y ∈ T → mP.m x y = 0) (T' : Set Q) [DecidablePred (· ∈ T')]
    (hT' : ∀ x y, x ∉ T' → y ∈ T' → mQ.m x y = 0) (hν₀ : ∀ x y, x ∉ T → y ∈ T' → ν₀.ν x y = 0)
    (hν₁ : ∀ x y, x ∉ T → y ∈ T' → ν₁.ν x y = 0) (hη : ∀ x y, x ∉ T → y ∈ T' → η.h x y = 0)
    (x : T) (y : T') : (η.restrictQuotient T hT T' hT' hν₀ hν₁ hη).h x y = η.h x y :=
  (rfl)

end ParametrizedCocycle

end Parametrized

/-! ### Action windows -/

section Action

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {P Q S : Type uP} {ind : P → ℤ} {indQ : Q → ℤ} {indS : S → ℤ} [Fintype P] [Fintype Q]
  [Fintype S] {𝒜 : ℤ → Submodule R A} {d : A →ₗ[R] A} {Γ : Type*}

namespace TwistingCocycle

variable [LinearOrder Γ] (m : TwistingCocycle 𝒜 d P ind) {act : P → Γ}
  (hm : ∀ x y, act x < act y → m.m x y = 0)
include hm

/-- **Action windows.** If the twisted differential does not raise the action, `m x y = 0`
whenever `act x < act y`, then the generators whose action lies in an order-connected set `I`
can be restricted to: a product `m x y * m y z` with `x` and `z` in the window and `y` outside it
vanishes. -/
theorem mul_eq_zero_of_ordConnected {I : Set Γ} (hI : I.OrdConnected) :
    ∀ x y z, x ∈ {x | act x ∈ I} → z ∈ {x | act x ∈ I} → y ∉ {x | act x ∈ I} →
      m.m x y * m.m y z = 0 := by
  intro x y z hx hz hy
  by_cases hxy : act x < act y
  · rw [hm x y hxy, zero_mul]
  by_cases hyz : act y < act z
  · rw [hm y z hyz, mul_zero]
  exact absurd (hI.out hz hx ⟨not_lt.1 hyz, not_lt.1 hxy⟩) hy

/-- If the twisted differential does not raise the action, it never leaves the generators of
action `< a`. -/
theorem m_eq_zero_of_mem_setOf_lt {a : Γ} :
    ∀ x y, x ∈ {x | act x < a} → y ∉ {x | act x < a} → m.m x y = 0 :=
  fun x y hx hy ↦ hm x y (lt_of_lt_of_le hx (not_lt.1 hy))

/-- If the twisted differential does not raise the action, it never enters the generators of
action `≥ a` from outside. -/
theorem m_eq_zero_of_notMem_setOf_le {a : Γ} :
    ∀ x y, x ∉ {x | a ≤ act x} → y ∈ {x | a ≤ act x} → m.m x y = 0 :=
  fun x y hx hy ↦ m.m_eq_zero_of_mem_setOf_lt hm x y (not_le.1 hx) (not_lt.2 hy)

end TwistingCocycle

section Shift

variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] {actP : P → Γ} {actQ : Q → Γ}
  {X : Type*} [Zero X] {f : P → Q → X} {δ : Γ}

omit [Fintype P] [Fintype Q] in
/-- If `f x y = 0` whenever `actP x + δ < actQ y`, then `f` vanishes from the generators of
action `< a` to those of action `≥ a + δ`. -/
theorem apply_eq_zero_of_mem_setOf_lt (hf : ∀ x y, actP x + δ < actQ y → f x y = 0) {a : Γ} :
    ∀ x y, x ∈ {x | actP x < a} → y ∉ {x | actQ x < a + δ} → f x y = 0 :=
  fun x y hx hy ↦ hf x y <| by
    calc actP x + δ < a + δ := add_lt_add_left hx δ
      _ ≤ actQ y := not_lt.1 hy

omit [Fintype P] [Fintype Q] in
/-- If `f x y = 0` whenever `actP x + δ < actQ y`, then `f` vanishes from outside the generators
of action `≥ a` to those of action `≥ a + δ`. -/
theorem apply_eq_zero_of_notMem_setOf_le (hf : ∀ x y, actP x + δ < actQ y → f x y = 0)
    {a : Γ} : ∀ x y, x ∉ {x | a ≤ actP x} → y ∈ {x | a + δ ≤ actQ x} → f x y = 0 :=
  fun x y hx hy ↦ apply_eq_zero_of_mem_setOf_lt hf x y (not_le.1 hx) (not_lt.2 hy)

end Shift

namespace ContinuationCocycle

variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  {mP : TwistingCocycle 𝒜 d P ind} {mQ : TwistingCocycle 𝒜 d Q indQ}
  {mS : TwistingCocycle 𝒜 d S indS} {actP : P → Γ} {actQ : Q → Γ} {actS : S → Γ}

/-- If the continuation cocycle `ν` raises the action by at most `δ`, it never leaves the
generators of action `< a + δ` from those of action `< a`. -/
theorem ν_eq_zero_of_mem_setOf_lt (ν : ContinuationCocycle mP mQ) {δ : Γ}
    (hν : ∀ x y, actP x + δ < actQ y → ν.ν x y = 0) {a : Γ} :
    ∀ x y, x ∈ {x | actP x < a} → y ∉ {x | actQ x < a + δ} → ν.ν x y = 0 :=
  apply_eq_zero_of_mem_setOf_lt hν

/-- If the continuation cocycle `ν` raises the action by at most `δ`, it never enters the
generators of action `≥ a + δ` from outside those of action `≥ a`. -/
theorem ν_eq_zero_of_notMem_setOf_le (ν : ContinuationCocycle mP mQ) {δ : Γ}
    (hν : ∀ x y, actP x + δ < actQ y → ν.ν x y = 0) {a : Γ} :
    ∀ x y, x ∉ {x | a ≤ actP x} → y ∈ {x | a + δ ≤ actQ x} → ν.ν x y = 0 :=
  apply_eq_zero_of_notMem_setOf_le hν

variable (ν : ContinuationCocycle mP mQ) (hmP : ∀ x y, actP x < actP y → mP.m x y = 0)
  (hmQ : ∀ x y, actQ x < actQ y → mQ.m x y = 0) {δ : Γ}
  (hν : ∀ x y, actP x + δ < actQ y → ν.ν x y = 0) (a : Γ)

/-- **The action filtration estimate of a continuation map.** If the twisted differentials of
`mP` and `mQ` do not raise the actions `actP` and `actQ`, and the continuation cocycle `ν`
raises the action by at most `δ`, `ν x y = 0` whenever `actP x + δ < actQ y`, then `ν` restricts
to a continuation cocycle from the generators of action `< a` to those of action `< a + δ`. It is
a `TauCeti.ContinuationCocycle.restrictSubcomplex`
(`TauCeti.ContinuationCocycle.actionSublevel_eq_restrictSubcomplex`), so by
`TauCeti.ContinuationCocycle.ofRestrict_continuationHom_comp` the continuation morphism of `ν`
carries the first subcomplex into the second. -/
def actionSublevel :
    ContinuationCocycle
      (mP.restrict {x | actP x < a}
        (mP.mul_eq_zero_of_forall_eq_zero (mP.m_eq_zero_of_mem_setOf_lt hmP)))
      (mQ.restrict {x | actQ x < a + δ}
        (mQ.mul_eq_zero_of_forall_eq_zero (mQ.m_eq_zero_of_mem_setOf_lt hmQ))) :=
  ν.restrictSubcomplex _ (mP.m_eq_zero_of_mem_setOf_lt hmP) _
    (mQ.m_eq_zero_of_mem_setOf_lt hmQ) (ν.ν_eq_zero_of_mem_setOf_lt hν)

@[simp]
theorem actionSublevel_ν (x : {x | actP x < a}) (y : {x | actQ x < a + δ}) :
    (ν.actionSublevel hmP hmQ hν a).ν x y = ν.ν x y :=
  (rfl)

/-- The action sublevel of `ν` is its restriction to the subcomplexes of generators of action
`< a` and `< a + δ`. -/
theorem actionSublevel_eq_restrictSubcomplex :
    ν.actionSublevel hmP hmQ hν a =
      ν.restrictSubcomplex {x | actP x < a} (mP.m_eq_zero_of_mem_setOf_lt hmP)
        {x | actQ x < a + δ} (mQ.m_eq_zero_of_mem_setOf_lt hmQ)
        (ν.ν_eq_zero_of_mem_setOf_lt hν) :=
  (rfl)

/-- **The action superlevel of a continuation map.** If the twisted differentials of `mP` and `mQ`
do not raise the actions and the continuation cocycle `ν` raises the action by at most `δ`, then
`ν` restricts to a continuation cocycle from the quotient complex of the generators of action
`≥ a` to that of the generators of action `≥ a + δ`. It is a
`TauCeti.ContinuationCocycle.restrictQuotient`
(`TauCeti.ContinuationCocycle.actionSuperlevel_eq_restrictQuotient`). -/
def actionSuperlevel :
    ContinuationCocycle
      (mP.restrict {x | a ≤ actP x}
        (mP.mul_eq_zero_of_forall_eq_zero' (mP.m_eq_zero_of_notMem_setOf_le hmP)))
      (mQ.restrict {x | a + δ ≤ actQ x}
        (mQ.mul_eq_zero_of_forall_eq_zero' (mQ.m_eq_zero_of_notMem_setOf_le hmQ))) :=
  ν.restrictQuotient _ (mP.m_eq_zero_of_notMem_setOf_le hmP) _
    (mQ.m_eq_zero_of_notMem_setOf_le hmQ) (ν.ν_eq_zero_of_notMem_setOf_le hν)

@[simp]
theorem actionSuperlevel_ν (x : {x | a ≤ actP x}) (y : {x | a + δ ≤ actQ x}) :
    (ν.actionSuperlevel hmP hmQ hν a).ν x y = ν.ν x y :=
  (rfl)

/-- The action superlevel of `ν` is its restriction to the quotient complexes of generators of
action `≥ a` and `≥ a + δ`. -/
theorem actionSuperlevel_eq_restrictQuotient :
    ν.actionSuperlevel hmP hmQ hν a =
      ν.restrictQuotient {x | a ≤ actP x} (mP.m_eq_zero_of_notMem_setOf_le hmP)
        {x | a + δ ≤ actQ x} (mQ.m_eq_zero_of_notMem_setOf_le hmQ)
        (ν.ν_eq_zero_of_notMem_setOf_le hν) :=
  (rfl)

/-- **Action sublevels compose.** If `ν` raises the action by at most `δ` and `ν₂` by at most
`δ₂`, the action sublevel of `ν` at level `a` followed by that of `ν₂` at level `a + δ` is the
restriction of their composite to the generators of action `< a` and `< a + δ + δ₂`. -/
theorem actionSublevel_comp [GradedAlgebra 𝒜] (h : IsDGAlgebra 𝒜 d)
    (ν₂ : ContinuationCocycle mQ mS) (hmS : ∀ x y, actS x < actS y → mS.m x y = 0) {δ₂ : Γ}
    (hν₂ : ∀ x y, actQ x + δ₂ < actS y → ν₂.ν x y = 0)
    (hνν₂ : ∀ x y, x ∈ {x | actP x < a} → y ∉ {x | actS x < a + δ + δ₂} →
      (ν.comp h ν₂).ν x y = 0) :
    (ν.actionSublevel hmP hmQ hν a).comp h (ν₂.actionSublevel hmQ hmS hν₂ (a + δ)) =
      (ν.comp h ν₂).restrictSubcomplex {x | actP x < a} (mP.m_eq_zero_of_mem_setOf_lt hmP)
        {x | actS x < a + δ + δ₂} (mS.m_eq_zero_of_mem_setOf_lt hmS) hνν₂ :=
  (restrictSubcomplex_comp h ν ν₂ _ _ _ _ _ _ (ν.ν_eq_zero_of_mem_setOf_lt hν)
    (ν₂.ν_eq_zero_of_mem_setOf_lt hν₂) hνν₂).symm

/-- **Action superlevels compose.** If `ν` raises the action by at most `δ` and `ν₂` by at most
`δ₂`, the action superlevel of `ν` at level `a` followed by that of `ν₂` at level `a + δ` is the
restriction of their composite to the generators of action `≥ a` and `≥ a + δ + δ₂`. -/
theorem actionSuperlevel_comp [GradedAlgebra 𝒜] (h : IsDGAlgebra 𝒜 d)
    (ν₂ : ContinuationCocycle mQ mS) (hmS : ∀ x y, actS x < actS y → mS.m x y = 0) {δ₂ : Γ}
    (hν₂ : ∀ x y, actQ x + δ₂ < actS y → ν₂.ν x y = 0)
    (hνν₂ : ∀ x y, x ∉ {x | a ≤ actP x} → y ∈ {x | a + δ + δ₂ ≤ actS x} →
      (ν.comp h ν₂).ν x y = 0) :
    (ν.actionSuperlevel hmP hmQ hν a).comp h (ν₂.actionSuperlevel hmQ hmS hν₂ (a + δ)) =
      (ν.comp h ν₂).restrictQuotient {x | a ≤ actP x} (mP.m_eq_zero_of_notMem_setOf_le hmP)
        {x | a + δ + δ₂ ≤ actS x} (mS.m_eq_zero_of_notMem_setOf_le hmS) hνν₂ :=
  (restrictQuotient_comp h ν ν₂ _ _ _ _ _ _ (ν.ν_eq_zero_of_notMem_setOf_le hν)
    (ν₂.ν_eq_zero_of_notMem_setOf_le hν₂) hνν₂).symm

end ContinuationCocycle

namespace ParametrizedCocycle

variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  {mP : TwistingCocycle 𝒜 d P ind} {mQ : TwistingCocycle 𝒜 d Q indQ} {actP : P → Γ}
  {actQ : Q → Γ} (hmP : ∀ x y, actP x < actP y → mP.m x y = 0)
  (hmQ : ∀ x y, actQ x < actQ y → mQ.m x y = 0) {δ : Γ} {ν₀ ν₁ : ContinuationCocycle mP mQ}
  (hν₀ : ∀ x y, actP x + δ < actQ y → ν₀.ν x y = 0)
  (hν₁ : ∀ x y, actP x + δ < actQ y → ν₁.ν x y = 0) (η : ParametrizedCocycle ν₀ ν₁)
  (hη : ∀ x y, actP x + δ < actQ y → η.h x y = 0) (a : Γ)

/-- The restriction of a parametrized cocycle which raises the action by at most `δ` to the
generators of action `< a` and `< a + δ`, a parametrized cocycle between the action sublevels. -/
def actionSublevel :
    ParametrizedCocycle (ν₀.actionSublevel hmP hmQ hν₀ a) (ν₁.actionSublevel hmP hmQ hν₁ a) :=
  η.restrictSubcomplex _ _ _ _ _ _ (apply_eq_zero_of_mem_setOf_lt hη)

@[simp]
theorem actionSublevel_h (x : {x | actP x < a}) (y : {x | actQ x < a + δ}) :
    (η.actionSublevel hmP hmQ hν₀ hν₁ hη a).h x y = η.h x y :=
  (rfl)

/-- The restriction of a parametrized cocycle which raises the action by at most `δ` to the
generators of action `≥ a` and `≥ a + δ`, a parametrized cocycle between the action
superlevels. -/
def actionSuperlevel :
    ParametrizedCocycle (ν₀.actionSuperlevel hmP hmQ hν₀ a)
      (ν₁.actionSuperlevel hmP hmQ hν₁ a) :=
  η.restrictQuotient _ _ _ _ _ _ (apply_eq_zero_of_notMem_setOf_le hη)

@[simp]
theorem actionSuperlevel_h (x : {x | a ≤ actP x}) (y : {x | a + δ ≤ actQ x}) :
    (η.actionSuperlevel hmP hmQ hν₀ hν₁ hη a).h x y = η.h x y :=
  (rfl)

end ParametrizedCocycle

end Action

section ActionShortExact

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {P : Type uP} {ind : P → ℤ} [Fintype P] [DecidableEq P]
  [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ] {dM : M →ₗ[R] M}
  {Γ : Type*} [LinearOrder Γ]
  (m : TwistingCocycle 𝒜 d P ind) {act : P → Γ} (hm : ∀ x y, act x < act y → m.m x y = 0)
  (hM : IsDGRightModule h ℳ dM) (a : Γ)

namespace TwistingCocycle

/-- **The action short complex.** If the twisted differential does not raise the action, the
inclusion of the twisted complex on the generators of action `< a` followed by the projection
onto the twisted complex on the generators of action `≥ a`. -/
@[expose]
noncomputable def actionShortComplex :
    ShortComplex (CochainComplex (ModuleCat.{max uP uM} R) ℤ) :=
  m.restrictShortComplex hM {x | act x < a} {x | a ≤ act x} (m.m_eq_zero_of_mem_setOf_lt hm)
    fun _ ↦ not_lt.symm

@[simp]
theorem actionShortComplex_def :
    m.actionShortComplex hm hM a =
      m.restrictShortComplex hM {x | act x < a} {x | a ≤ act x} (m.m_eq_zero_of_mem_setOf_lt hm)
        fun _ ↦ not_lt.symm :=
  (rfl)

/-- **The action filtration gives a short exact sequence.** If the twisted differential does not
raise the action, the twisted complexes on the generators of action `< a`, on all generators and
on the generators of action `≥ a` form a short exact sequence. -/
theorem actionShortComplex_shortExact : (m.actionShortComplex hm hM a).ShortExact :=
  m.restrictShortComplex_shortExact hM _ _ _ _

end TwistingCocycle

end ActionShortExact

end TauCeti

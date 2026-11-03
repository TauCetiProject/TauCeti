/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.MvPolynomial
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Topology
public import TauCeti.Geometry.RealAnalytic.Semianalytic.Basic

/-!
# Locally semialgebraic sets

A subset `s` of the real coordinate space `σ → ℝ` is *semialgebraic at* a point `x`
(`TauCeti.SemialgebraicAt`) if `x` has an open semialgebraic neighbourhood `U` such that `s ∩ U` is
semialgebraic. The set `s` is *locally semialgebraic* (`TauCeti.IsLocallySemialgebraic`) if it is
semialgebraic at every point of the ambient space, including the points of its frontier that lie
outside `s`. The results that use the metric or the closure assume that `σ` is finite. For
instance, the set of integer points of the real line is locally semialgebraic but, having infinitely
many connected components, it is not semialgebraic.

Locally semialgebraic sets are the sets which, near every point, are cut out by finitely many
polynomial sign conditions; they sit between semialgebraic and semianalytic sets. In Łojasiewicz's
triangulation of semianalytic sets they describe the semianalytic sets of the analytic-algebraic
(Nash) category, and the key point is that boundedness turns the local notion into the global one.

## Main declarations

* `TauCeti.SemialgebraicAt s x`: `s` is semialgebraic near `x`.
* `TauCeti.IsLocallySemialgebraic s`: `s` is semialgebraic near every point.

## Main results

* `TauCeti.semialgebraicAt_iff_exists_ball`: it suffices to test sup-norm balls around `x`, and
  `TauCeti.SemialgebraicAt.exists_subset`: the neighbourhood can be chosen inside any prescribed
  neighbourhood of `x`. Being semialgebraic at `x` depends only on the germ of the set at `x`
  (`TauCeti.SemialgebraicAt.congr`).
* Finite Boolean operations, locally and globally: `TauCeti.isSetAlgebra_setOf_semialgebraicAt`,
  `TauCeti.isSetAlgebra_setOf_isLocallySemialgebraic` and their named consequences, and locally
  finite unions (`LocallyFinite.isLocallySemialgebraic_iUnion`).
* Closures, interiors and frontiers (`TauCeti.SemialgebraicAt.closure`, …) and preimages under
  polynomial maps (`TauCeti.SemialgebraicAt.preimage_eval`).
* `TauCeti.IsCompact.exists_isSemialgebraic_inter`: a set semialgebraic at every point of a compact
  set `K` meets some open semialgebraic neighbourhood of `K` in a semialgebraic set. Consequently a
  bounded set which is semialgebraic at every point of its closure is semialgebraic
  (`TauCeti.isSemialgebraic_of_isBounded`), so a bounded set is semialgebraic exactly when it is
  locally semialgebraic (`Bornology.IsBounded.isSemialgebraic_iff`).
* `TauCeti.IsLocallySemialgebraic.isSemianalytic`: locally semialgebraic sets are semianalytic.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §1.
* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 36, Springer, 1998, Section 8.1.
-/

public section

open Filter MeasureTheory Metric MvPolynomial Set Topology

namespace TauCeti

variable {σ τ : Type*}

/-! ### Semialgebraicity at a point -/

/-- A set `s ⊆ σ → ℝ` is *semialgebraic at* `x` if `x` has an open semialgebraic neighbourhood `U`
such that `s ∩ U` is semialgebraic. -/
def SemialgebraicAt (s : Set (σ → ℝ)) (x : σ → ℝ) : Prop :=
  ∃ U, IsOpen U ∧ x ∈ U ∧ IsSemialgebraic U ∧ IsSemialgebraic (s ∩ U)

/-- A set is semialgebraic at `x` if and only if `x` has an open semialgebraic neighbourhood `U`
such that `s ∩ U` is semialgebraic. -/
theorem semialgebraicAt_def {s : Set (σ → ℝ)} {x : σ → ℝ} :
    SemialgebraicAt s x ↔ ∃ U, IsOpen U ∧ x ∈ U ∧ IsSemialgebraic U ∧ IsSemialgebraic (s ∩ U) :=
  Iff.rfl

section SemialgebraicAt

variable {s s' V : Set (σ → ℝ)} {x : σ → ℝ}

/-- **Shrinking.** If `s` is semialgebraic at `x`, then the open semialgebraic neighbourhood of
`x` meeting `s` in a semialgebraic set can be chosen inside any prescribed neighbourhood `V`
of `x`. -/
theorem SemialgebraicAt.exists_subset [Finite σ] (hs : SemialgebraicAt s x) (hV : V ∈ 𝓝 x) :
    ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ V ∧ IsSemialgebraic U ∧ IsSemialgebraic (s ∩ U) := by
  cases nonempty_fintype σ
  obtain ⟨U, hUo, hxU, hU, hsU⟩ := hs
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV
  refine ⟨U ∩ ball x ε, hUo.inter isOpen_ball, ⟨hxU, mem_ball_self hε⟩,
    inter_subset_right.trans hεV, hU.inter (isSemialgebraic_ball x ε), ?_⟩
  rw [← inter_assoc]
  exact hsU.inter (isSemialgebraic_ball x ε)

/-- A set is semialgebraic at `x` if and only if it meets some sup-norm ball around `x` in a
semialgebraic set. -/
theorem semialgebraicAt_iff_exists_ball [Fintype σ] :
    SemialgebraicAt s x ↔ ∃ ε > 0, IsSemialgebraic (s ∩ ball x ε) := by
  refine ⟨fun hs => ?_, fun ⟨ε, hε, hs⟩ =>
    ⟨ball x ε, isOpen_ball, mem_ball_self hε, isSemialgebraic_ball x ε, hs⟩⟩
  obtain ⟨U, hUo, hxU, hU, hsU⟩ := hs
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hUo x hxU
  refine ⟨ε, hε, ?_⟩
  rw [← inter_eq_right.2 hεU, ← inter_assoc]
  exact hsU.inter (isSemialgebraic_ball x ε)

/-- Being semialgebraic at `x` only depends on the germ of the set at `x`. -/
theorem SemialgebraicAt.congr [Finite σ] (hs : SemialgebraicAt s x) (h : s =ᶠ[𝓝 x] s') :
    SemialgebraicAt s' x := by
  obtain ⟨U, hUo, hxU, hUs, hU, hsU⟩ := hs.exists_subset (eventuallyEqSet_iff.1 h)
  refine ⟨U, hUo, hxU, hU, ?_⟩
  convert hsU using 1
  ext y
  simp only [mem_inter_iff, and_congr_left_iff]
  exact fun hy => (hUs hy).symm

/-- Being semialgebraic at `x` only depends on the germ of the set at `x`. -/
theorem semialgebraicAt_congr [Finite σ] (h : s =ᶠ[𝓝 x] s') :
    SemialgebraicAt s x ↔ SemialgebraicAt s' x :=
  ⟨fun hs => hs.congr h, fun hs => hs.congr h.symm⟩

/-- A semialgebraic set is semialgebraic at every point. -/
theorem IsSemialgebraic.semialgebraicAt (hs : IsSemialgebraic s) (x : σ → ℝ) :
    SemialgebraicAt s x :=
  ⟨univ, isOpen_univ, mem_univ x, isSemialgebraic_univ, by rwa [inter_univ]⟩

variable (x) in
/-- The sets semialgebraic at a point form an algebra of sets. -/
theorem isSetAlgebra_setOf_semialgebraicAt :
    IsSetAlgebra {s : Set (σ → ℝ) | SemialgebraicAt s x} where
  empty_mem := isSemialgebraic_empty.semialgebraicAt x
  compl_mem := by
    rintro s ⟨U, hUo, hxU, hU, hsU⟩
    refine ⟨U, hUo, hxU, hU, ?_⟩
    convert hU.sdiff hsU using 1
    ext y
    simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff]
    tauto
  union_mem := by
    rintro s s' ⟨U, hUo, hxU, hU, hsU⟩ ⟨U', hUo', hxU', hU', hsU'⟩
    refine ⟨U ∩ U', hUo.inter hUo', ⟨hxU, hxU'⟩, hU.inter hU', ?_⟩
    convert (hsU.inter hU').union (hsU'.inter hU) using 1
    ext y
    simp only [mem_inter_iff, mem_union]
    tauto

/-- The empty set is semialgebraic at every point. -/
@[simp]
theorem semialgebraicAt_empty : SemialgebraicAt (∅ : Set (σ → ℝ)) x :=
  (isSetAlgebra_setOf_semialgebraicAt x).empty_mem

/-- The whole space is semialgebraic at every point. -/
@[simp]
theorem semialgebraicAt_univ : SemialgebraicAt (univ : Set (σ → ℝ)) x :=
  (isSetAlgebra_setOf_semialgebraicAt x).univ_mem

/-- The complement of a set semialgebraic at `x` is semialgebraic at `x`. -/
theorem SemialgebraicAt.compl (hs : SemialgebraicAt s x) : SemialgebraicAt sᶜ x :=
  (isSetAlgebra_setOf_semialgebraicAt x).compl_mem hs

/-- A set is semialgebraic at `x` if and only if its complement is. -/
@[simp]
theorem semialgebraicAt_compl_iff : SemialgebraicAt sᶜ x ↔ SemialgebraicAt s x :=
  ⟨fun hs => compl_compl s ▸ hs.compl, SemialgebraicAt.compl⟩

/-- The union of two sets semialgebraic at `x` is semialgebraic at `x`. -/
theorem SemialgebraicAt.union (hs : SemialgebraicAt s x) (hs' : SemialgebraicAt s' x) :
    SemialgebraicAt (s ∪ s') x :=
  (isSetAlgebra_setOf_semialgebraicAt x).union_mem hs hs'

/-- The intersection of two sets semialgebraic at `x` is semialgebraic at `x`. -/
theorem SemialgebraicAt.inter (hs : SemialgebraicAt s x) (hs' : SemialgebraicAt s' x) :
    SemialgebraicAt (s ∩ s') x :=
  (isSetAlgebra_setOf_semialgebraicAt x).inter_mem hs hs'

/-- The difference of two sets semialgebraic at `x` is semialgebraic at `x`. -/
theorem SemialgebraicAt.sdiff (hs : SemialgebraicAt s x) (hs' : SemialgebraicAt s' x) :
    SemialgebraicAt (s \ s') x :=
  (isSetAlgebra_setOf_semialgebraicAt x).sdiff_mem hs hs'

/-- A finite union of sets semialgebraic at `x` is semialgebraic at `x`. -/
theorem SemialgebraicAt.biUnion {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι → Set (σ → ℝ)}
    (hs : ∀ i ∈ I, SemialgebraicAt (s i) x) : SemialgebraicAt (⋃ i ∈ I, s i) x := by
  simpa using (isSetAlgebra_setOf_semialgebraicAt x).biUnion_mem hI.toFinset
    fun i hi => hs i (hI.mem_toFinset.1 hi)

/-- A finite intersection of sets semialgebraic at `x` is semialgebraic at `x`. -/
theorem SemialgebraicAt.biInter {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι → Set (σ → ℝ)}
    (hs : ∀ i ∈ I, SemialgebraicAt (s i) x) : SemialgebraicAt (⋂ i ∈ I, s i) x := by
  simpa using (isSetAlgebra_setOf_semialgebraicAt x).biInter_mem hI.toFinset
    fun i hi => hs i (hI.mem_toFinset.1 hi)

/-- The union of a finite family of sets semialgebraic at `x` is semialgebraic at `x`. -/
theorem SemialgebraicAt.iUnion {ι : Type*} [Finite ι] {s : ι → Set (σ → ℝ)}
    (hs : ∀ i, SemialgebraicAt (s i) x) : SemialgebraicAt (⋃ i, s i) x := by
  simpa using SemialgebraicAt.biUnion finite_univ fun i (_ : i ∈ univ) => hs i

/-- The intersection of a finite family of sets semialgebraic at `x` is semialgebraic at `x`. -/
theorem SemialgebraicAt.iInter {ι : Type*} [Finite ι] {s : ι → Set (σ → ℝ)}
    (hs : ∀ i, SemialgebraicAt (s i) x) : SemialgebraicAt (⋂ i, s i) x := by
  simpa using SemialgebraicAt.biInter finite_univ fun i (_ : i ∈ univ) => hs i

/-- The closure of a set semialgebraic at `x` is semialgebraic at `x`. -/
theorem SemialgebraicAt.closure [Finite σ] (hs : SemialgebraicAt s x) :
    SemialgebraicAt (_root_.closure s) x := by
  obtain ⟨U, hUo, hxU, hU, hsU⟩ := hs
  refine ⟨U, hUo, hxU, hU, ?_⟩
  -- Inside the open set `U`, the closure of `s` agrees with the closure of `s ∩ U`.
  have : _root_.closure s ∩ U = _root_.closure (s ∩ U) ∩ U :=
    subset_antisymm (subset_inter (hUo.closure_inter) inter_subset_right)
      (inter_subset_inter_left U (closure_mono inter_subset_left))
  rw [this]
  exact hsU.closure.inter hU

/-- The interior of a set semialgebraic at `x` is semialgebraic at `x`. -/
theorem SemialgebraicAt.interior [Finite σ] (hs : SemialgebraicAt s x) :
    SemialgebraicAt (_root_.interior s) x := by
  simpa [closure_compl] using hs.compl.closure.compl

/-- The frontier of a set semialgebraic at `x` is semialgebraic at `x`. -/
theorem SemialgebraicAt.frontier [Finite σ] (hs : SemialgebraicAt s x) :
    SemialgebraicAt (_root_.frontier s) x := by
  rw [frontier_eq_closure_inter_closure]
  exact hs.closure.inter hs.compl.closure

/-- **Polynomial preimages.** The preimage of a set semialgebraic at `f x` under a polynomial
map `f` is semialgebraic at `x`. -/
theorem SemialgebraicAt.preimage_eval {s : Set (τ → ℝ)} (f : τ → MvPolynomial σ ℝ)
    (hs : SemialgebraicAt s fun i => eval x (f i)) :
    SemialgebraicAt ((fun y i => eval y (f i)) ⁻¹' s) x := by
  obtain ⟨U, hUo, hxU, hU, hsU⟩ := hs
  exact ⟨_, hUo.preimage (continuous_pi fun i => (f i).continuous_eval), hxU,
    hU.preimage_eval f, hsU.preimage_eval f⟩

/-- A set semialgebraic at `x` is semianalytic at `x`. -/
theorem SemialgebraicAt.semianalyticAt [Fintype σ] (hs : SemialgebraicAt s x) :
    SemianalyticAt s x := by
  obtain ⟨U, hUo, hxU, -, hsU⟩ := hs
  refine (hsU.isSemianalytic.semianalyticAt x).congr ?_
  filter_upwards [hUo.mem_nhds hxU] with y hy
  simp [hy]

end SemialgebraicAt

/-! ### Locally semialgebraic sets -/

/-- A set `s ⊆ σ → ℝ` is *locally semialgebraic* if it is semialgebraic at every point of
`σ → ℝ`: every point, whether or not it lies in `s`, has an open semialgebraic neighbourhood `U`
such that `s ∩ U` is semialgebraic. -/
def IsLocallySemialgebraic (s : Set (σ → ℝ)) : Prop :=
  ∀ x, SemialgebraicAt s x

/-- A set is locally semialgebraic if and only if it is semialgebraic at every point. -/
theorem isLocallySemialgebraic_iff {s : Set (σ → ℝ)} :
    IsLocallySemialgebraic s ↔ ∀ x, SemialgebraicAt s x :=
  Iff.rfl

/-- A locally semialgebraic set is semialgebraic at every point. -/
theorem IsLocallySemialgebraic.semialgebraicAt {s : Set (σ → ℝ)} (hs : IsLocallySemialgebraic s)
    (x : σ → ℝ) : SemialgebraicAt s x :=
  hs x

/-- A semialgebraic set is locally semialgebraic. -/
theorem IsSemialgebraic.isLocallySemialgebraic {s : Set (σ → ℝ)} (hs : IsSemialgebraic s) :
    IsLocallySemialgebraic s :=
  hs.semialgebraicAt

variable (σ) in
/-- The locally semialgebraic sets form an algebra of sets. -/
theorem isSetAlgebra_setOf_isLocallySemialgebraic :
    IsSetAlgebra {s : Set (σ → ℝ) | IsLocallySemialgebraic s} where
  empty_mem _ := semialgebraicAt_empty
  compl_mem _ hs x := (hs x).compl
  union_mem _ _ hs hs' x := (hs x).union (hs' x)

/-- The empty set is locally semialgebraic. -/
@[simp]
theorem isLocallySemialgebraic_empty : IsLocallySemialgebraic (∅ : Set (σ → ℝ)) :=
  (isSetAlgebra_setOf_isLocallySemialgebraic σ).empty_mem

/-- The whole space is locally semialgebraic. -/
@[simp]
theorem isLocallySemialgebraic_univ : IsLocallySemialgebraic (univ : Set (σ → ℝ)) :=
  (isSetAlgebra_setOf_isLocallySemialgebraic σ).univ_mem

/-- A set is locally semialgebraic if and only if its complement is. -/
@[simp]
theorem isLocallySemialgebraic_compl_iff {s : Set (σ → ℝ)} :
    IsLocallySemialgebraic sᶜ ↔ IsLocallySemialgebraic s :=
  forall_congr' fun _ => semialgebraicAt_compl_iff

namespace IsLocallySemialgebraic

variable {s s' : Set (σ → ℝ)}

/-- The complement of a locally semialgebraic set is locally semialgebraic. -/
protected theorem compl (hs : IsLocallySemialgebraic s) : IsLocallySemialgebraic sᶜ :=
  fun x => (hs x).compl

/-- The union of two locally semialgebraic sets is locally semialgebraic. -/
protected theorem union (hs : IsLocallySemialgebraic s) (hs' : IsLocallySemialgebraic s') :
    IsLocallySemialgebraic (s ∪ s') :=
  fun x => (hs x).union (hs' x)

/-- The intersection of two locally semialgebraic sets is locally semialgebraic. -/
protected theorem inter (hs : IsLocallySemialgebraic s) (hs' : IsLocallySemialgebraic s') :
    IsLocallySemialgebraic (s ∩ s') :=
  fun x => (hs x).inter (hs' x)

/-- The difference of two locally semialgebraic sets is locally semialgebraic. -/
protected theorem sdiff (hs : IsLocallySemialgebraic s) (hs' : IsLocallySemialgebraic s') :
    IsLocallySemialgebraic (s \ s') :=
  fun x => (hs x).sdiff (hs' x)

/-- A finite union of locally semialgebraic sets is locally semialgebraic. -/
protected theorem biUnion {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι → Set (σ → ℝ)}
    (hs : ∀ i ∈ I, IsLocallySemialgebraic (s i)) : IsLocallySemialgebraic (⋃ i ∈ I, s i) :=
  fun x => .biUnion hI fun i hi => hs i hi x

/-- A finite intersection of locally semialgebraic sets is locally semialgebraic. -/
protected theorem biInter {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι → Set (σ → ℝ)}
    (hs : ∀ i ∈ I, IsLocallySemialgebraic (s i)) : IsLocallySemialgebraic (⋂ i ∈ I, s i) :=
  fun x => .biInter hI fun i hi => hs i hi x

/-- The union of a finite family of locally semialgebraic sets is locally semialgebraic. -/
protected theorem iUnion {ι : Type*} [Finite ι] {s : ι → Set (σ → ℝ)}
    (hs : ∀ i, IsLocallySemialgebraic (s i)) : IsLocallySemialgebraic (⋃ i, s i) :=
  fun x => .iUnion fun i => hs i x

/-- The intersection of a finite family of locally semialgebraic sets is locally
semialgebraic. -/
protected theorem iInter {ι : Type*} [Finite ι] {s : ι → Set (σ → ℝ)}
    (hs : ∀ i, IsLocallySemialgebraic (s i)) : IsLocallySemialgebraic (⋂ i, s i) :=
  fun x => .iInter fun i => hs i x

/-- The closure of a locally semialgebraic set is locally semialgebraic. -/
protected theorem closure [Finite σ] (hs : IsLocallySemialgebraic s) :
    IsLocallySemialgebraic (_root_.closure s) :=
  fun x => (hs x).closure

/-- The interior of a locally semialgebraic set is locally semialgebraic. -/
protected theorem interior [Finite σ] (hs : IsLocallySemialgebraic s) :
    IsLocallySemialgebraic (_root_.interior s) :=
  fun x => (hs x).interior

/-- The frontier of a locally semialgebraic set is locally semialgebraic. -/
protected theorem frontier [Finite σ] (hs : IsLocallySemialgebraic s) :
    IsLocallySemialgebraic (_root_.frontier s) :=
  fun x => (hs x).frontier

/-- **Polynomial preimages.** The preimage of a locally semialgebraic set under a polynomial map
is locally semialgebraic. -/
protected theorem preimage_eval {s : Set (τ → ℝ)} (hs : IsLocallySemialgebraic s)
    (f : τ → MvPolynomial σ ℝ) : IsLocallySemialgebraic ((fun y i => eval y (f i)) ⁻¹' s) :=
  fun _ => (hs _).preimage_eval f

/-- A locally semialgebraic set is semianalytic. -/
protected theorem isSemianalytic [Fintype σ] (hs : IsLocallySemialgebraic s) : IsSemianalytic s :=
  isSemianalytic_iff.2 fun x => (hs x).semianalyticAt

end IsLocallySemialgebraic

/-- **Locally finite unions.** The union of a locally finite family of locally semialgebraic sets
is locally semialgebraic. -/
theorem _root_.LocallyFinite.isLocallySemialgebraic_iUnion [Finite σ] {ι : Type*}
    {s : ι → Set (σ → ℝ)} (hfin : LocallyFinite s) (hs : ∀ i, IsLocallySemialgebraic (s i)) :
    IsLocallySemialgebraic (⋃ i, s i) := by
  intro x
  obtain ⟨V, hV, hI⟩ := hfin x
  refine (SemialgebraicAt.biUnion hI fun i _ => hs i x).congr ?_
  filter_upwards [hV] with y hy
  simp only [eq_iff_iff, mem_iUnion, exists_prop]
  exact ⟨fun ⟨i, _, hyi⟩ => ⟨i, hyi⟩, fun ⟨i, hyi⟩ => ⟨i, ⟨y, hyi, hy⟩, hyi⟩⟩

/-! ### Bounded locally semialgebraic sets -/

/-- If `s` is semialgebraic at every point of a compact set `K`, then some open semialgebraic
neighbourhood `U` of `K` meets `s` in a semialgebraic set. -/
theorem _root_.IsCompact.exists_isSemialgebraic_inter {s K : Set (σ → ℝ)} (hK : IsCompact K)
    (hs : ∀ x ∈ K, SemialgebraicAt s x) :
    ∃ U, IsOpen U ∧ K ⊆ U ∧ IsSemialgebraic U ∧ IsSemialgebraic (s ∩ U) := by
  choose U hUo hxU hU hsU using hs
  obtain ⟨t, hKt⟩ := hK.elim_nhds_subcover' U fun x hx => (hUo x hx).mem_nhds (hxU x hx)
  refine ⟨⋃ x ∈ t, U x x.2, isOpen_biUnion fun x _ => hUo x x.2, hKt,
    .biUnion t.finite_toSet fun x _ => hU x x.2, ?_⟩
  rw [inter_iUnion₂]
  exact .biUnion t.finite_toSet fun x _ => hsU x x.2

/-- A bounded set which is semialgebraic at every point of its closure is semialgebraic. -/
theorem isSemialgebraic_of_isBounded [Finite σ] {s : Set (σ → ℝ)} (hb : Bornology.IsBounded s)
    (hs : ∀ x ∈ closure s, SemialgebraicAt s x) : IsSemialgebraic s := by
  cases nonempty_fintype σ
  obtain ⟨U, -, hsU, -, h⟩ := hb.isCompact_closure.exists_isSemialgebraic_inter hs
  rwa [inter_eq_left.2 (subset_closure.trans hsU)] at h

/-- A bounded locally semialgebraic set is semialgebraic. -/
theorem IsLocallySemialgebraic.isSemialgebraic_of_isBounded [Finite σ] {s : Set (σ → ℝ)}
    (hs : IsLocallySemialgebraic s) (hb : Bornology.IsBounded s) : IsSemialgebraic s :=
  TauCeti.isSemialgebraic_of_isBounded hb fun x _ => hs x

/-- A bounded set is semialgebraic if and only if it is locally semialgebraic. -/
theorem _root_.Bornology.IsBounded.isSemialgebraic_iff [Finite σ] {s : Set (σ → ℝ)}
    (hb : Bornology.IsBounded s) : IsSemialgebraic s ↔ IsLocallySemialgebraic s :=
  ⟨IsSemialgebraic.isLocallySemialgebraic, fun hs => hs.isSemialgebraic_of_isBounded hb⟩

end TauCeti
